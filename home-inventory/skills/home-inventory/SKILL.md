---
name: home-inventory
description: Track what is in the home - fridge, freezer, pantry, closets, wardrobe, toiletries - with quantities, expiration dates, and a shopping list. Use when the user asks what they have, where something is, what is expiring, what to buy, or says they used, bought, moved, or threw something out.
---

# Home inventory

The inventory lives in a SQLite file and is reached through the `home-inventory`
command, which prints JSON. (If the `home-inventory` MCP server is connected,
use its tools instead; they have the same names and arguments.)

Arguments are `key=value`. Quote values with spaces. Lists are JSON: `tags='["winter","kids"]'`.

## Look before you write

```bash
home-inventory get_inventory_summary              # every container, counts of low/expired items
home-inventory find_items query=milk              # words must all match name, category, notes or tags
home-inventory get_container container="Kitchen fridge"
```

## Record changes

```bash
home-inventory create_container name="Bathroom closet" kind=closet location="Upstairs bathroom"
home-inventory add_item name="Toothpaste" container="Bathroom closet" quantity=2 category=toiletries low_stock_threshold=1
home-inventory add_item name="Whole milk" container="Kitchen fridge" unit=gallon expires_on=+7
home-inventory adjust_quantity item_id=12 delta=-1 agent_name=openclaw   # used one
home-inventory move_item item_id=12 to_container="Freezer drawer" quantity=2
home-inventory remove_item item_id=12 reason="expired"
```

## Answer questions

```bash
home-inventory find_items expiring_within_days=3   # soonest first, includes already expired
home-inventory get_shopping_list                   # low stock or expired, each with a reason
home-inventory get_history item_id=12              # who changed it, and when
```

## Rules

- Search with `find_items` before `add_item`. Adding the same name, unit and expiry to the same container tops up the existing entry.
- Use `adjust_quantity` for use and restocking, not `update_item`. Items at 0 stay so they appear on the shopping list.
- Ask before `remove_item` or `delete_container` unless the user clearly asked for it.
- Dates: `YYYY-MM-DD`, `today`, `tomorrow`, or `+N` days.
- Container kinds: refrigerator, freezer, pantry, closet, wardrobe, cabinet, drawer, shelf, bin, room, other.
- Errors print `{"error": "..."}` to stderr with exit code 1. The message says how to fix the call (for example, it lists the containers that do exist).
