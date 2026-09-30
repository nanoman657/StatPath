"""SQLite storage for a single home's inventory.

The model is deliberately small:

* **containers** are the places things live: a refrigerator, a wardrobe, a
  toiletries closet. A container may sit inside another one (the freezer
  drawer of the fridge, the top shelf of the closet), so they form a tree.
* **items** are the things themselves, with a quantity and unit, an optional
  category, tags, expiration date, and a low-stock threshold.
* **events** is an append-only log of every change, recording which agent
  made it, so "who used the last of the milk?" has an answer.

Every public method takes and returns plain dicts and lists, so the MCP
server and the CLI can hand results straight to an agent as JSON.

Anywhere a container is expected, callers may pass either its numeric id or
its name (case-insensitive). Agents rarely remember ids; names are how
people talk about their fridge.
"""

from __future__ import annotations

import json
import os
import sqlite3
from contextlib import contextmanager
from datetime import date, datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Iterator

SCHEMA_VERSION = 1

SCHEMA = """
CREATE TABLE IF NOT EXISTS containers (
    id          INTEGER PRIMARY KEY,
    name        TEXT NOT NULL,
    kind        TEXT NOT NULL DEFAULT 'other',
    location    TEXT,
    description TEXT,
    parent_id   INTEGER REFERENCES containers(id) ON DELETE RESTRICT,
    created_at  TEXT NOT NULL,
    updated_at  TEXT NOT NULL
);
CREATE UNIQUE INDEX IF NOT EXISTS containers_name ON containers(name COLLATE NOCASE);

CREATE TABLE IF NOT EXISTS items (
    id                  INTEGER PRIMARY KEY,
    container_id        INTEGER NOT NULL REFERENCES containers(id) ON DELETE RESTRICT,
    name                TEXT NOT NULL,
    category            TEXT,
    quantity            REAL NOT NULL DEFAULT 1 CHECK (quantity >= 0),
    unit                TEXT,
    low_stock_threshold REAL,
    expires_on          TEXT,
    purchased_on        TEXT,
    tags                TEXT NOT NULL DEFAULT '[]',
    notes               TEXT,
    created_at          TEXT NOT NULL,
    updated_at          TEXT NOT NULL
);
CREATE INDEX IF NOT EXISTS items_container ON items(container_id);
CREATE INDEX IF NOT EXISTS items_name ON items(name COLLATE NOCASE);
CREATE INDEX IF NOT EXISTS items_expires ON items(expires_on);

CREATE TABLE IF NOT EXISTS events (
    id           INTEGER PRIMARY KEY,
    at           TEXT NOT NULL,
    actor        TEXT NOT NULL,
    action       TEXT NOT NULL,
    item_id      INTEGER,
    container_id INTEGER,
    detail       TEXT NOT NULL DEFAULT '{}'
);
CREATE INDEX IF NOT EXISTS events_at ON events(at);
CREATE INDEX IF NOT EXISTS events_item ON events(item_id);
"""

CONTAINER_KINDS = (
    "refrigerator",
    "freezer",
    "pantry",
    "closet",
    "wardrobe",
    "cabinet",
    "drawer",
    "shelf",
    "bin",
    "room",
    "other",
)

ITEM_FIELDS = (
    "name",
    "category",
    "quantity",
    "unit",
    "low_stock_threshold",
    "expires_on",
    "purchased_on",
    "tags",
    "notes",
)
CONTAINER_FIELDS = ("name", "kind", "location", "description", "parent")


class InventoryError(ValueError):
    """A request the inventory cannot satisfy. The message is written for the agent."""


def default_db_path() -> Path:
    env = os.environ.get("HOME_INVENTORY_DB")
    if env:
        return Path(env).expanduser()
    return Path.home() / ".home-inventory" / "inventory.db"


def _now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def _date(value: str | None, field: str) -> str | None:
    """Normalise a date to ISO YYYY-MM-DD, accepting a few forms agents produce."""
    if value is None or value == "":
        return None
    text = str(value).strip()
    lowered = text.lower()
    today = date.today()
    if lowered == "today":
        return today.isoformat()
    if lowered == "tomorrow":
        return (today + timedelta(days=1)).isoformat()
    if lowered.startswith("+") and lowered[1:].rstrip("d").isdigit():
        return (today + timedelta(days=int(lowered[1:].rstrip("d")))).isoformat()
    try:
        return date.fromisoformat(text[:10]).isoformat()
    except ValueError:
        raise InventoryError(
            f"{field} must be a date like 2026-10-14, 'today', 'tomorrow', or '+7' (days from now); got {value!r}"
        ) from None


def _tags(value: Any) -> list[str]:
    if value is None:
        return []
    if isinstance(value, str):
        value = value.split(",")
    tags = []
    for tag in value:
        tag = str(tag).strip().lower()
        if tag and tag not in tags:
            tags.append(tag)
    return tags


def _number(value: Any, field: str, *, allow_none: bool = False) -> float | None:
    if value is None:
        if allow_none:
            return None
        raise InventoryError(f"{field} is required")
    try:
        number = float(value)
    except (TypeError, ValueError):
        raise InventoryError(f"{field} must be a number; got {value!r}") from None
    if number < 0:
        raise InventoryError(f"{field} cannot be negative; got {number:g}")
    return number


def _clean_number(number: float | None) -> float | int | None:
    """Show 3 rather than 3.0, since most household counts are whole."""
    if number is None:
        return None
    return int(number) if float(number).is_integer() else number


class Inventory:
    """All reads and writes go through here. One instance per database file."""

    def __init__(self, path: str | os.PathLike[str] | None = None):
        self.path = Path(path) if path is not None else default_db_path()
        if str(self.path) != ":memory:":
            self.path.parent.mkdir(parents=True, exist_ok=True)
        self.conn = sqlite3.connect(str(self.path), check_same_thread=False, timeout=10)
        self.conn.row_factory = sqlite3.Row
        self.conn.execute("PRAGMA foreign_keys = ON")
        if str(self.path) != ":memory:":
            # WAL lets a CLI and a running MCP server share the file safely.
            self.conn.execute("PRAGMA journal_mode = WAL")
        self.conn.executescript(SCHEMA)
        self.conn.execute(f"PRAGMA user_version = {SCHEMA_VERSION}")
        self.conn.commit()

    def close(self) -> None:
        self.conn.close()

    @contextmanager
    def _tx(self) -> Iterator[sqlite3.Connection]:
        try:
            yield self.conn
        except BaseException:
            self.conn.rollback()
            raise
        else:
            self.conn.commit()

    def _log(self, actor: str, action: str, *, item_id=None, container_id=None, **detail) -> None:
        self.conn.execute(
            "INSERT INTO events (at, actor, action, item_id, container_id, detail) VALUES (?, ?, ?, ?, ?, ?)",
            (_now(), actor or "unknown", action, item_id, container_id, json.dumps(detail, default=str)),
        )

    # ------------------------------------------------------------------ lookup

    def _container_row(self, ref: int | str) -> sqlite3.Row:
        if ref is None or ref == "":
            raise InventoryError("A container is required (its name or id).")
        row = None
        if isinstance(ref, int) or (isinstance(ref, str) and ref.strip().isdigit()):
            row = self.conn.execute("SELECT * FROM containers WHERE id = ?", (int(ref),)).fetchone()
        if row is None and isinstance(ref, str):
            row = self.conn.execute(
                "SELECT * FROM containers WHERE name = ? COLLATE NOCASE", (ref.strip(),)
            ).fetchone()
        if row is None:
            names = [r["name"] for r in self.conn.execute("SELECT name FROM containers ORDER BY name")]
            hint = f" Known containers: {', '.join(names)}." if names else " No containers exist yet; create one first."
            raise InventoryError(f"No container named or numbered {ref!r}.{hint}")
        return row

    def _item_row(self, item_id: int) -> sqlite3.Row:
        row = self.conn.execute("SELECT * FROM items WHERE id = ?", (int(item_id),)).fetchone()
        if row is None:
            raise InventoryError(f"No item with id {item_id}. Use find_items to look it up by name.")
        return row

    def _container_path(self, container_id: int) -> str:
        parts, seen = [], set()
        current = container_id
        while current is not None and current not in seen:
            seen.add(current)
            row = self.conn.execute("SELECT name, parent_id FROM containers WHERE id = ?", (current,)).fetchone()
            if row is None:
                break
            parts.append(row["name"])
            current = row["parent_id"]
        return " > ".join(reversed(parts))

    def _descendant_ids(self, container_id: int) -> list[int]:
        rows = self.conn.execute(
            """
            WITH RECURSIVE tree(id) AS (
                SELECT ? UNION ALL
                SELECT c.id FROM containers c JOIN tree ON c.parent_id = tree.id
            )
            SELECT id FROM tree
            """,
            (container_id,),
        ).fetchall()
        return [r["id"] for r in rows]

    def _container_dict(self, row: sqlite3.Row) -> dict[str, Any]:
        counts = self.conn.execute(
            "SELECT COUNT(*) AS n FROM items WHERE container_id = ?", (row["id"],)
        ).fetchone()
        parent = None
        if row["parent_id"] is not None:
            p = self.conn.execute("SELECT name FROM containers WHERE id = ?", (row["parent_id"],)).fetchone()
            parent = p["name"] if p else None
        return {
            "id": row["id"],
            "name": row["name"],
            "kind": row["kind"],
            "location": row["location"],
            "description": row["description"],
            "parent": parent,
            "path": self._container_path(row["id"]),
            "item_count": counts["n"],
        }

    def _item_dict(self, row: sqlite3.Row) -> dict[str, Any]:
        today = date.today()
        expires = row["expires_on"]
        days_left = (date.fromisoformat(expires) - today).days if expires else None
        threshold = row["low_stock_threshold"]
        return {
            "id": row["id"],
            "name": row["name"],
            "container": self._container_path(row["container_id"]),
            "container_id": row["container_id"],
            "category": row["category"],
            "quantity": _clean_number(row["quantity"]),
            "unit": row["unit"],
            "low_stock_threshold": _clean_number(threshold),
            "low_stock": threshold is not None and row["quantity"] <= threshold,
            "expires_on": expires,
            "days_until_expiry": days_left,
            "expired": days_left is not None and days_left < 0,
            "purchased_on": row["purchased_on"],
            "tags": json.loads(row["tags"] or "[]"),
            "notes": row["notes"],
            "updated_at": row["updated_at"],
        }

    # -------------------------------------------------------------- containers

    def create_container(
        self,
        name: str,
        kind: str = "other",
        location: str | None = None,
        description: str | None = None,
        parent: int | str | None = None,
        actor: str = "unknown",
    ) -> dict[str, Any]:
        name = (name or "").strip()
        if not name:
            raise InventoryError("A container needs a name, e.g. 'Kitchen fridge'.")
        kind = (kind or "other").strip().lower()
        if kind not in CONTAINER_KINDS:
            raise InventoryError(f"kind must be one of {', '.join(CONTAINER_KINDS)}; got {kind!r}")
        if self.conn.execute("SELECT 1 FROM containers WHERE name = ? COLLATE NOCASE", (name,)).fetchone():
            raise InventoryError(f"A container named {name!r} already exists. Container names are unique.")
        parent_id = self._container_row(parent)["id"] if parent not in (None, "") else None
        now = _now()
        with self._tx():
            cur = self.conn.execute(
                "INSERT INTO containers (name, kind, location, description, parent_id, created_at, updated_at)"
                " VALUES (?, ?, ?, ?, ?, ?, ?)",
                (name, kind, location, description, parent_id, now, now),
            )
            self._log(actor, "create_container", container_id=cur.lastrowid, name=name, kind=kind)
        return self.get_container(cur.lastrowid, include_items=False)

    def list_containers(self) -> list[dict[str, Any]]:
        rows = self.conn.execute("SELECT * FROM containers").fetchall()
        result = [self._container_dict(r) for r in rows]
        result.sort(key=lambda c: c["path"].lower())
        return result

    def get_container(self, container: int | str, include_items: bool = True) -> dict[str, Any]:
        row = self._container_row(container)
        result = self._container_dict(row)
        children = self.conn.execute(
            "SELECT name FROM containers WHERE parent_id = ? ORDER BY name", (row["id"],)
        ).fetchall()
        result["children"] = [c["name"] for c in children]
        if include_items:
            ids = self._descendant_ids(row["id"])
            items = self.conn.execute(
                f"SELECT * FROM items WHERE container_id IN ({','.join('?' * len(ids))}) ORDER BY name COLLATE NOCASE",
                ids,
            ).fetchall()
            result["items"] = [self._item_dict(i) for i in items]
        return result

    def update_container(self, container: int | str, actor: str = "unknown", **changes: Any) -> dict[str, Any]:
        row = self._container_row(container)
        unknown = set(changes) - set(CONTAINER_FIELDS)
        if unknown:
            raise InventoryError(f"Cannot update {', '.join(sorted(unknown))}; allowed: {', '.join(CONTAINER_FIELDS)}")
        updates: dict[str, Any] = {}
        for key, value in changes.items():
            if value is None:
                continue
            if key == "name":
                value = str(value).strip()
                clash = self.conn.execute(
                    "SELECT id FROM containers WHERE name = ? COLLATE NOCASE AND id != ?", (value, row["id"])
                ).fetchone()
                if not value or clash:
                    raise InventoryError(f"Cannot rename to {value!r}: empty or already used.")
                updates["name"] = value
            elif key == "kind":
                value = str(value).strip().lower()
                if value not in CONTAINER_KINDS:
                    raise InventoryError(f"kind must be one of {', '.join(CONTAINER_KINDS)}")
                updates["kind"] = value
            elif key == "parent":
                if value == "":
                    updates["parent_id"] = None
                else:
                    parent_id = self._container_row(value)["id"]
                    if parent_id in self._descendant_ids(row["id"]):
                        raise InventoryError("A container cannot be placed inside itself or one of its children.")
                    updates["parent_id"] = parent_id
            else:
                updates[key] = value or None
        if not updates:
            return self.get_container(row["id"], include_items=False)
        updates["updated_at"] = _now()
        with self._tx():
            self.conn.execute(
                f"UPDATE containers SET {', '.join(f'{k} = ?' for k in updates)} WHERE id = ?",
                (*updates.values(), row["id"]),
            )
            self._log(actor, "update_container", container_id=row["id"], changes=changes)
        return self.get_container(row["id"], include_items=False)

    def delete_container(self, container: int | str, move_items_to: int | str | None = None, actor: str = "unknown") -> dict[str, Any]:
        row = self._container_row(container)
        children = self.conn.execute("SELECT name FROM containers WHERE parent_id = ?", (row["id"],)).fetchall()
        if children:
            raise InventoryError(
                f"{row['name']!r} still holds containers ({', '.join(c['name'] for c in children)}). Move or delete them first."
            )
        count = self.conn.execute("SELECT COUNT(*) FROM items WHERE container_id = ?", (row["id"],)).fetchone()[0]
        target = None
        if count:
            if move_items_to in (None, ""):
                raise InventoryError(
                    f"{row['name']!r} still holds {count} item(s). Pass move_items_to, or remove the items first."
                )
            target = self._container_row(move_items_to)
            if target["id"] == row["id"]:
                raise InventoryError("move_items_to must be a different container.")
        with self._tx():
            if target is not None:
                self.conn.execute(
                    "UPDATE items SET container_id = ?, updated_at = ? WHERE container_id = ?",
                    (target["id"], _now(), row["id"]),
                )
            self.conn.execute("DELETE FROM containers WHERE id = ?", (row["id"],))
            self._log(actor, "delete_container", container_id=row["id"], name=row["name"],
                      moved_items=count, moved_to=target["name"] if target is not None else None)
        return {"deleted": row["name"], "moved_items": count, "moved_to": target["name"] if target is not None else None}

    # ------------------------------------------------------------------- items

    def add_item(
        self,
        name: str,
        container: int | str,
        quantity: float = 1,
        unit: str | None = None,
        category: str | None = None,
        expires_on: str | None = None,
        purchased_on: str | None = None,
        low_stock_threshold: float | None = None,
        tags: list[str] | str | None = None,
        notes: str | None = None,
        merge: bool = True,
        actor: str = "unknown",
    ) -> dict[str, Any]:
        name = (name or "").strip()
        if not name:
            raise InventoryError("An item needs a name, e.g. 'Whole milk'.")
        box = self._container_row(container)
        qty = _number(quantity, "quantity")
        expires = _date(expires_on, "expires_on")
        purchased = _date(purchased_on, "purchased_on")
        threshold = _number(low_stock_threshold, "low_stock_threshold", allow_none=True)
        tag_list = _tags(tags)

        if merge:
            # Same name, same container, same unit, same expiry is the same stock: top it up.
            existing = self.conn.execute(
                "SELECT * FROM items WHERE container_id = ? AND name = ? COLLATE NOCASE"
                " AND COALESCE(unit, '') = COALESCE(?, '') AND COALESCE(expires_on, '') = COALESCE(?, '')",
                (box["id"], name, unit, expires),
            ).fetchone()
            if existing is not None:
                merged_tags = _tags(json.loads(existing["tags"]) + tag_list)
                with self._tx():
                    self.conn.execute(
                        "UPDATE items SET quantity = quantity + ?, tags = ?,"
                        " category = COALESCE(?, category), low_stock_threshold = COALESCE(?, low_stock_threshold),"
                        " purchased_on = COALESCE(?, purchased_on), notes = COALESCE(?, notes), updated_at = ?"
                        " WHERE id = ?",
                        (qty, json.dumps(merged_tags), category, threshold, purchased, notes, _now(), existing["id"]),
                    )
                    self._log(actor, "restock", item_id=existing["id"], container_id=box["id"], name=name, added=qty)
                item = self.get_item(existing["id"])
                item["merged_into_existing"] = True
                return item

        now = _now()
        with self._tx():
            cur = self.conn.execute(
                "INSERT INTO items (container_id, name, category, quantity, unit, low_stock_threshold,"
                " expires_on, purchased_on, tags, notes, created_at, updated_at)"
                " VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
                (box["id"], name, category, qty, unit, threshold, expires, purchased,
                 json.dumps(tag_list), notes, now, now),
            )
            self._log(actor, "add_item", item_id=cur.lastrowid, container_id=box["id"], name=name, quantity=qty)
        item = self.get_item(cur.lastrowid)
        item["merged_into_existing"] = False
        return item

    def get_item(self, item_id: int) -> dict[str, Any]:
        return self._item_dict(self._item_row(item_id))

    def find_items(
        self,
        query: str | None = None,
        container: int | str | None = None,
        category: str | None = None,
        tag: str | None = None,
        expiring_within_days: int | None = None,
        low_stock_only: bool = False,
        include_empty: bool = True,
        limit: int = 100,
    ) -> list[dict[str, Any]]:
        where, params = [], []
        if query:
            # Every word must appear somewhere in name, category, notes, or tags.
            for word in str(query).split():
                like = f"%{word}%"
                where.append("(name LIKE ? OR category LIKE ? OR notes LIKE ? OR tags LIKE ?)")
                params += [like, like, like, like]
        if container not in (None, ""):
            ids = self._descendant_ids(self._container_row(container)["id"])
            where.append(f"container_id IN ({','.join('?' * len(ids))})")
            params += ids
        if category:
            where.append("category LIKE ?")
            params.append(category)
        if tag:
            where.append("tags LIKE ?")
            params.append(f'%"{str(tag).strip().lower()}"%')
        if expiring_within_days is not None:
            cutoff = (date.today() + timedelta(days=int(expiring_within_days))).isoformat()
            where.append("expires_on IS NOT NULL AND expires_on <= ?")
            params.append(cutoff)
        if low_stock_only:
            where.append("low_stock_threshold IS NOT NULL AND quantity <= low_stock_threshold")
        if not include_empty:
            where.append("quantity > 0")
        sql = "SELECT * FROM items"
        if where:
            sql += " WHERE " + " AND ".join(where)
        order = "expires_on, name COLLATE NOCASE" if expiring_within_days is not None else "name COLLATE NOCASE"
        sql += f" ORDER BY {order} LIMIT ?"
        params.append(max(1, min(int(limit), 1000)))
        return [self._item_dict(r) for r in self.conn.execute(sql, params)]

    def update_item(self, item_id: int, actor: str = "unknown", **changes: Any) -> dict[str, Any]:
        row = self._item_row(item_id)
        unknown = set(changes) - set(ITEM_FIELDS)
        if unknown:
            raise InventoryError(f"Cannot update {', '.join(sorted(unknown))}; allowed: {', '.join(ITEM_FIELDS)}")
        updates: dict[str, Any] = {}
        for key, value in changes.items():
            if value is None:
                continue
            if key == "name":
                value = str(value).strip()
                if not value:
                    raise InventoryError("name cannot be empty")
                updates[key] = value
            elif key == "quantity":
                updates[key] = _number(value, key)
            elif key == "low_stock_threshold":
                # An empty string clears the threshold.
                updates[key] = None if value == "" else _number(value, key)
            elif key in ("expires_on", "purchased_on"):
                updates[key] = _date(value, key)
            elif key == "tags":
                updates[key] = json.dumps(_tags(value))
            else:
                updates[key] = value or None
        if updates:
            updates["updated_at"] = _now()
            with self._tx():
                self.conn.execute(
                    f"UPDATE items SET {', '.join(f'{k} = ?' for k in updates)} WHERE id = ?",
                    (*updates.values(), row["id"]),
                )
                self._log(actor, "update_item", item_id=row["id"], container_id=row["container_id"],
                          name=row["name"], changes={k: v for k, v in changes.items() if v is not None})
        return self.get_item(row["id"])

    def adjust_quantity(
        self, item_id: int, delta: float, reason: str | None = None, actor: str = "unknown"
    ) -> dict[str, Any]:
        row = self._item_row(item_id)
        try:
            delta = float(delta)
        except (TypeError, ValueError):
            raise InventoryError(f"delta must be a number, e.g. -1 to use one or 6 to add six; got {delta!r}") from None
        new_qty = row["quantity"] + delta
        if new_qty < -1e-9:
            raise InventoryError(
                f"Only {_clean_number(row['quantity'])} {row['unit'] or ''} of {row['name']!r} on hand; cannot remove {_clean_number(-delta)}."
                .replace("  ", " ")
            )
        new_qty = max(new_qty, 0.0)
        with self._tx():
            self.conn.execute("UPDATE items SET quantity = ?, updated_at = ? WHERE id = ?", (new_qty, _now(), row["id"]))
            self._log(actor, "use" if delta < 0 else "restock", item_id=row["id"], container_id=row["container_id"],
                      name=row["name"], delta=delta, quantity=new_qty, reason=reason)
        return self.get_item(row["id"])

    def move_item(
        self, item_id: int, to_container: int | str, quantity: float | None = None, actor: str = "unknown"
    ) -> dict[str, Any]:
        """Move a whole item, or split off `quantity` of it into another container."""
        row = self._item_row(item_id)
        target = self._container_row(to_container)
        if target["id"] == row["container_id"]:
            raise InventoryError(f"{row['name']!r} is already in {target['name']!r}.")
        from_name = self._container_path(row["container_id"])
        qty = _number(quantity, "quantity", allow_none=True)
        if qty is None or abs(qty - row["quantity"]) < 1e-9:
            with self._tx():
                self.conn.execute(
                    "UPDATE items SET container_id = ?, updated_at = ? WHERE id = ?", (target["id"], _now(), row["id"])
                )
                self._log(actor, "move_item", item_id=row["id"], container_id=target["id"],
                          name=row["name"], moved_from=from_name, moved_to=target["name"])
            return self.get_item(row["id"])
        if qty > row["quantity"]:
            raise InventoryError(f"Only {_clean_number(row['quantity'])} of {row['name']!r} to move.")
        with self._tx():
            self.conn.execute(
                "UPDATE items SET quantity = quantity - ?, updated_at = ? WHERE id = ?", (qty, _now(), row["id"])
            )
        moved = self.add_item(
            row["name"], target["id"], qty, unit=row["unit"], category=row["category"],
            expires_on=row["expires_on"], purchased_on=row["purchased_on"],
            low_stock_threshold=row["low_stock_threshold"], tags=json.loads(row["tags"]),
            notes=row["notes"], actor=actor,
        )
        with self._tx():
            self._log(actor, "move_item", item_id=moved["id"], container_id=target["id"], name=row["name"],
                      quantity=qty, moved_from=from_name, moved_to=target["name"], split_from_item=row["id"])
        return moved

    def remove_item(self, item_id: int, reason: str | None = None, actor: str = "unknown") -> dict[str, Any]:
        row = self._item_row(item_id)
        snapshot = self._item_dict(row)
        with self._tx():
            self.conn.execute("DELETE FROM items WHERE id = ?", (row["id"],))
            self._log(actor, "remove_item", item_id=row["id"], container_id=row["container_id"],
                      name=row["name"], quantity=row["quantity"], reason=reason)
        return {"removed": snapshot, "reason": reason}

    # ----------------------------------------------------------------- reports

    def shopping_list(self) -> list[dict[str, Any]]:
        """Items at or below their low-stock threshold, plus anything that has expired."""
        rows = self.conn.execute(
            "SELECT * FROM items WHERE (low_stock_threshold IS NOT NULL AND quantity <= low_stock_threshold)"
            " OR (expires_on IS NOT NULL AND expires_on < ?) ORDER BY name COLLATE NOCASE",
            (date.today().isoformat(),),
        ).fetchall()
        out = []
        for r in rows:
            item = self._item_dict(r)
            item["why"] = "expired" if item["expired"] and not item["low_stock"] else "low stock"
            out.append(item)
        return out

    def summary(self) -> dict[str, Any]:
        today = date.today()
        soon = (today + timedelta(days=7)).isoformat()
        q = lambda sql, *p: self.conn.execute(sql, p).fetchone()[0]  # noqa: E731
        return {
            "database": str(self.path),
            "containers": [
                {"name": c["path"], "kind": c["kind"], "location": c["location"], "item_count": c["item_count"]}
                for c in self.list_containers()
            ],
            "total_items": q("SELECT COUNT(*) FROM items"),
            "out_of_stock": q("SELECT COUNT(*) FROM items WHERE quantity = 0"),
            "low_stock": q("SELECT COUNT(*) FROM items WHERE low_stock_threshold IS NOT NULL AND quantity <= low_stock_threshold"),
            "expired": q("SELECT COUNT(*) FROM items WHERE expires_on < ?", today.isoformat()),
            "expiring_within_7_days": q(
                "SELECT COUNT(*) FROM items WHERE expires_on >= ? AND expires_on <= ?", today.isoformat(), soon
            ),
            "categories": [
                {"category": r[0], "count": r[1]}
                for r in self.conn.execute(
                    "SELECT COALESCE(category, '(none)'), COUNT(*) FROM items GROUP BY 1 ORDER BY 2 DESC, 1"
                )
            ],
        }

    def history(self, item_id: int | None = None, container: int | str | None = None, limit: int = 50) -> list[dict[str, Any]]:
        where, params = [], []
        if item_id is not None:
            where.append("item_id = ?")
            params.append(int(item_id))
        if container not in (None, ""):
            where.append("container_id = ?")
            params.append(self._container_row(container)["id"])
        sql = "SELECT * FROM events"
        if where:
            sql += " WHERE " + " AND ".join(where)
        sql += " ORDER BY id DESC LIMIT ?"
        params.append(max(1, min(int(limit), 500)))
        return [
            {"at": r["at"], "actor": r["actor"], "action": r["action"], "item_id": r["item_id"],
             "container_id": r["container_id"], **json.loads(r["detail"])}
            for r in self.conn.execute(sql, params)
        ]
