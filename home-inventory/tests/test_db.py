from datetime import date, timedelta

import pytest

from home_inventory import Inventory, InventoryError


@pytest.fixture
def inv(tmp_path):
    inventory = Inventory(tmp_path / "home.db")
    inventory.create_container("Kitchen fridge", "refrigerator", location="Kitchen")
    inventory.create_container("Freezer drawer", "freezer", parent="Kitchen fridge")
    inventory.create_container("Wardrobe", "wardrobe", location="Bedroom")
    inventory.create_container("Hall closet", "closet", location="Hallway")
    yield inventory
    inventory.close()


def in_days(n):
    return (date.today() + timedelta(days=n)).isoformat()


def test_containers_by_name_or_id_case_insensitive(inv):
    fridge = inv.get_container("kitchen FRIDGE", include_items=False)
    assert fridge["kind"] == "refrigerator"
    assert inv.get_container(str(fridge["id"]), include_items=False)["name"] == "Kitchen fridge"
    assert fridge["children"] == ["Freezer drawer"]
    assert inv.get_container("Freezer drawer", include_items=False)["path"] == "Kitchen fridge > Freezer drawer"


def test_unknown_container_lists_known_names(inv):
    with pytest.raises(InventoryError, match="Known containers: .*Wardrobe"):
        inv.add_item("Socks", "Dresser")


def test_duplicate_container_names_rejected(inv):
    with pytest.raises(InventoryError, match="already exists"):
        inv.create_container("wardrobe")


def test_bad_kind_rejected(inv):
    with pytest.raises(InventoryError, match="kind must be one of"):
        inv.create_container("Garage", "spaceship")


def test_add_merges_same_stock(inv):
    first = inv.add_item("Eggs", "Kitchen fridge", 4, unit="eggs")
    second = inv.add_item("eggs", "Kitchen fridge", 6, unit="eggs")
    assert second["id"] == first["id"] and second["merged_into_existing"]
    assert second["quantity"] == 10


def test_add_keeps_different_expiry_separate(inv):
    a = inv.add_item("Yogurt", "Kitchen fridge", 2, expires_on=in_days(3))
    b = inv.add_item("Yogurt", "Kitchen fridge", 2, expires_on=in_days(10))
    assert a["id"] != b["id"]


def test_relative_dates(inv):
    item = inv.add_item("Milk", "Kitchen fridge", expires_on="+5")
    assert item["expires_on"] == in_days(5) and item["days_until_expiry"] == 5
    with pytest.raises(InventoryError, match="must be a date"):
        inv.add_item("Bread", "Kitchen fridge", expires_on="next-ish week")


def test_adjust_quantity_and_floor(inv):
    item = inv.add_item("Toilet paper", "Hall closet", 12, unit="rolls", low_stock_threshold=4)
    item = inv.adjust_quantity(item["id"], -9, reason="used", actor="gemini")
    assert item["quantity"] == 3 and item["low_stock"]
    with pytest.raises(InventoryError, match="cannot remove 5"):
        inv.adjust_quantity(item["id"], -5)
    assert inv.get_item(item["id"])["quantity"] == 3


def test_find_items_filters(inv):
    inv.add_item("Wool sweater", "Wardrobe", tags=["winter", "Wool"], category="tops")
    inv.add_item("Linen shirt", "Wardrobe", tags="summer", category="tops")
    inv.add_item("Peas", "Freezer drawer", 2, unit="bags", expires_on=in_days(60))
    inv.add_item("Milk", "Kitchen fridge", expires_on=in_days(2))
    inv.add_item("Old cheese", "Kitchen fridge", expires_on=in_days(-3))

    assert [i["name"] for i in inv.find_items(tag="winter")] == ["Wool sweater"]
    assert [i["name"] for i in inv.find_items(category="TOPS")] == ["Linen shirt", "Wool sweater"]
    assert [i["name"] for i in inv.find_items(query="wool sweater")] == ["Wool sweater"]
    # Searching a container includes the containers nested inside it.
    assert {i["name"] for i in inv.find_items(container="Kitchen fridge")} == {"Peas", "Milk", "Old cheese"}
    soon = inv.find_items(expiring_within_days=7)
    assert [i["name"] for i in soon] == ["Old cheese", "Milk"]
    assert soon[0]["expired"]


def test_move_whole_and_partial(inv):
    chicken = inv.add_item("Chicken thighs", "Kitchen fridge", 4, unit="lb")
    moved = inv.move_item(chicken["id"], "Freezer drawer", quantity=3)
    assert moved["id"] != chicken["id"] and moved["quantity"] == 3
    assert inv.get_item(chicken["id"])["quantity"] == 1
    whole = inv.move_item(chicken["id"], "Freezer drawer")
    assert whole["container"] == "Kitchen fridge > Freezer drawer"
    with pytest.raises(InventoryError, match="already in"):
        inv.move_item(chicken["id"], "freezer drawer")


def test_shopping_list(inv):
    inv.add_item("Shampoo", "Hall closet", 1, low_stock_threshold=1)
    inv.add_item("Soap", "Hall closet", 5, low_stock_threshold=1)
    inv.add_item("Sour milk", "Kitchen fridge", expires_on=in_days(-1))
    listed = {i["name"]: i["why"] for i in inv.shopping_list()}
    assert listed == {"Shampoo": "low stock", "Sour milk": "expired"}


def test_delete_container_protects_items(inv):
    inv.add_item("Scarf", "Wardrobe")
    with pytest.raises(InventoryError, match="still holds 1 item"):
        inv.delete_container("Wardrobe")
    result = inv.delete_container("Wardrobe", move_items_to="Hall closet")
    assert result["moved_items"] == 1
    assert [i["name"] for i in inv.find_items(container="Hall closet")] == ["Scarf"]
    with pytest.raises(InventoryError, match="still holds containers"):
        inv.delete_container("Kitchen fridge")


def test_container_cannot_nest_in_itself(inv):
    with pytest.raises(InventoryError, match="inside itself"):
        inv.update_container("Kitchen fridge", parent="Freezer drawer")


def test_update_item(inv):
    item = inv.add_item("Jeans", "Wardrobe", low_stock_threshold=1)
    item = inv.update_item(item["id"], notes="32x30", tags=["denim"], low_stock_threshold="")
    assert item["notes"] == "32x30" and item["tags"] == ["denim"] and item["low_stock_threshold"] is None
    with pytest.raises(InventoryError, match="Cannot update"):
        inv.update_item(item["id"], container="Hall closet")


def test_history_records_actor(inv):
    milk = inv.add_item("Milk", "Kitchen fridge", 1, actor="muse")
    inv.adjust_quantity(milk["id"], -1, actor="openclaw")
    events = inv.history(item_id=milk["id"])
    assert [(e["actor"], e["action"]) for e in events] == [("openclaw", "use"), ("muse", "add_item")]


def test_summary(inv):
    inv.add_item("Milk", "Kitchen fridge", 0, category="dairy")
    summary = inv.summary()
    assert summary["total_items"] == 1 and summary["out_of_stock"] == 1
    assert {"name": "Kitchen fridge > Freezer drawer", "kind": "freezer", "location": None, "item_count": 0} in summary["containers"]


def test_data_persists_across_connections(tmp_path):
    path = tmp_path / "home.db"
    first = Inventory(path)
    first.create_container("Pantry", "pantry")
    first.add_item("Rice", "Pantry", 2, unit="kg")
    first.close()
    second = Inventory(path)
    assert second.find_items(query="rice")[0]["quantity"] == 2
    second.close()
