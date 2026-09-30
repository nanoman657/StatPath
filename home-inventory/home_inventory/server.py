"""MCP server exposing the home inventory to AI agents.

Run it over stdio for desktop and CLI agents (the default), or over
Streamable HTTP for agents that connect by URL:

    home-inventory-mcp                          # stdio
    home-inventory-mcp --http --port 8765       # http://127.0.0.1:8765/mcp
"""

from __future__ import annotations

import argparse
import functools
import json
import os
from typing import Any

from mcp.types import ToolAnnotations

try:  # MCP Python SDK 2.x
    from mcp.server.mcpserver import MCPServer as _Server
    from mcp.server.mcpserver.exceptions import ToolError
except ImportError:  # MCP Python SDK 1.x
    from mcp.server.fastmcp import FastMCP as _Server
    from mcp.server.fastmcp.exceptions import ToolError

from .db import CONTAINER_KINDS, Inventory, InventoryError

INSTRUCTIONS = f"""\
This server is the inventory of one home. Things live in containers (a
refrigerator, a wardrobe, a toiletries closet, a shelf inside a pantry), and
each item has a quantity, a unit, and optionally a category, tags, an
expiration date, and a low-stock threshold.

How to work with it:
- Start with get_inventory_summary or list_containers to learn what exists.
- Refer to containers by name ("Kitchen fridge") or id; names are case-insensitive.
- Before adding, call find_items to check whether the item is already there.
  add_item merges into an existing row with the same name, container, unit and
  expiry, so adding 6 eggs to 4 eggs gives 10 eggs.
- When something is used up or bought, call adjust_quantity with a negative or
  positive delta rather than rewriting the quantity. Keep items at quantity 0
  if the household wants to remember to rebuy them; remove_item deletes them.
- Dates are YYYY-MM-DD; 'today', 'tomorrow' and '+N' (days from now) also work.
- Pass agent_name on writes so the history shows who changed what.
- Container kinds: {", ".join(CONTAINER_KINDS)}.
"""

# Built from wire-format (camelCase) keys, which both SDK 1.x and 2.x accept.
READ = ToolAnnotations.model_validate({"readOnlyHint": True, "idempotentHint": True, "openWorldHint": False})
WRITE = ToolAnnotations.model_validate({"readOnlyHint": False, "destructiveHint": False, "openWorldHint": False})
DESTRUCTIVE = ToolAnnotations.model_validate({"readOnlyHint": False, "destructiveHint": True, "openWorldHint": False})


def build_server(inventory: Inventory | None = None) -> Any:
    inv = inventory or Inventory()
    default_actor = os.environ.get("HOME_INVENTORY_AGENT", "agent")
    mcp = _Server("home-inventory", instructions=INSTRUCTIONS)

    def who(agent_name: str | None) -> str:
        return (agent_name or "").strip() or default_actor

    def tool(annotations: ToolAnnotations):
        """Register a tool whose InventoryError messages reach the agent as a tool error it can act on."""

        def register(fn):
            @functools.wraps(fn)
            def wrapper(*args, **kwargs):
                try:
                    return fn(*args, **kwargs)
                except InventoryError as exc:
                    raise ToolError(str(exc)) from exc

            return mcp.tool(annotations=annotations)(wrapper)

        return register

    # ------------------------------------------------------------ containers

    @tool(READ)
    def list_containers() -> list[dict[str, Any]]:
        """List every container in the home (fridge, closets, wardrobe, shelves...) with its kind, location, parent, and item count."""
        return inv.list_containers()

    @tool(READ)
    def get_container(container: str, include_items: bool = True) -> dict[str, Any]:
        """Show one container and, by default, every item in it and in the containers nested inside it.

        Args:
            container: Container name (case-insensitive) or numeric id.
            include_items: Set false to get only the container's details.
        """
        return inv.get_container(container, include_items)

    @tool(WRITE)
    def create_container(
        name: str,
        kind: str = "other",
        location: str | None = None,
        description: str | None = None,
        parent: str | None = None,
        agent_name: str | None = None,
    ) -> dict[str, Any]:
        """Create a place where items are kept, such as a refrigerator, a wardrobe, or a toiletries closet.

        Args:
            name: Unique, human name, e.g. "Kitchen fridge" or "Hall closet".
            kind: One of refrigerator, freezer, pantry, closet, wardrobe, cabinet, drawer, shelf, bin, room, other.
            location: Where it is in the home, e.g. "Kitchen" or "Upstairs bathroom".
            description: Free-text notes.
            parent: Name or id of the container this one sits inside (e.g. a shelf inside a closet).
            agent_name: Who is making the change, for the history log.
        """
        return inv.create_container(name, kind, location, description, parent, actor=who(agent_name))

    @tool(WRITE)
    def update_container(
        container: str,
        name: str | None = None,
        kind: str | None = None,
        location: str | None = None,
        description: str | None = None,
        parent: str | None = None,
        agent_name: str | None = None,
    ) -> dict[str, Any]:
        """Rename a container or change its kind, location, description, or parent. Omitted fields stay as they are; pass parent="" to make it top-level."""
        return inv.update_container(
            container, actor=who(agent_name),
            name=name, kind=kind, location=location, description=description, parent=parent,
        )

    @tool(DESTRUCTIVE)
    def delete_container(container: str, move_items_to: str | None = None, agent_name: str | None = None) -> dict[str, Any]:
        """Delete a container. If it still holds items, pass move_items_to so they are moved rather than lost; it refuses otherwise."""
        return inv.delete_container(container, move_items_to, actor=who(agent_name))

    # ----------------------------------------------------------------- items

    @tool(WRITE)
    def add_item(
        name: str,
        container: str,
        quantity: float = 1,
        unit: str | None = None,
        category: str | None = None,
        expires_on: str | None = None,
        purchased_on: str | None = None,
        low_stock_threshold: float | None = None,
        tags: list[str] | None = None,
        notes: str | None = None,
        merge: bool = True,
        agent_name: str | None = None,
    ) -> dict[str, Any]:
        """Put an item into a container. If the same item (same name, unit, and expiry) is already there, its quantity is increased instead of creating a duplicate, unless merge is false.

        Args:
            name: What it is, e.g. "Whole milk", "Blue wool sweater", "Toothpaste".
            container: Container name or id.
            quantity: How many or how much (default 1).
            unit: e.g. "gallon", "eggs", "rolls", "pairs". Leave empty for simple counts.
            category: e.g. "dairy", "produce", "outerwear", "toiletries", "cleaning".
            expires_on: Expiration date: YYYY-MM-DD, "today", "tomorrow", or "+N" days.
            purchased_on: Purchase date, same formats.
            low_stock_threshold: At or below this quantity the item shows up on the shopping list.
            tags: Free-form labels, e.g. ["winter", "kids"].
            notes: Anything else worth remembering (size, color, brand).
            merge: Set false to always create a separate entry.
            agent_name: Who is making the change, for the history log.
        """
        return inv.add_item(
            name, container, quantity, unit, category, expires_on, purchased_on,
            low_stock_threshold, tags, notes, merge, actor=who(agent_name),
        )

    @tool(READ)
    def find_items(
        query: str | None = None,
        container: str | None = None,
        category: str | None = None,
        tag: str | None = None,
        expiring_within_days: int | None = None,
        low_stock_only: bool = False,
        include_empty: bool = True,
        limit: int = 100,
    ) -> list[dict[str, Any]]:
        """Search the inventory. All filters are optional and combine with AND; with none, lists everything.

        Args:
            query: Words that must all appear in the name, category, notes, or tags (e.g. "milk", "black shoes").
            container: Only look in this container and the containers nested inside it.
            category: Exact category, case-insensitive.
            tag: Items carrying this tag.
            expiring_within_days: Items expiring within this many days, including already expired (0 = today or earlier). Sorted soonest first.
            low_stock_only: Only items at or below their low-stock threshold.
            include_empty: Set false to hide items with quantity 0.
            limit: Maximum results (default 100).
        """
        return inv.find_items(query, container, category, tag, expiring_within_days, low_stock_only, include_empty, limit)

    @tool(READ)
    def get_item(item_id: int) -> dict[str, Any]:
        """Get one item by id, including where it is, how much is left, and days until it expires."""
        return inv.get_item(item_id)

    @tool(WRITE)
    def update_item(
        item_id: int,
        name: str | None = None,
        category: str | None = None,
        quantity: float | None = None,
        unit: str | None = None,
        low_stock_threshold: float | str | None = None,
        expires_on: str | None = None,
        purchased_on: str | None = None,
        tags: list[str] | None = None,
        notes: str | None = None,
        agent_name: str | None = None,
    ) -> dict[str, Any]:
        """Correct or change an item's details. Omitted fields stay as they are. To record use or restocking, prefer adjust_quantity; to relocate, use move_item. Pass low_stock_threshold="" to clear it."""
        return inv.update_item(
            item_id, actor=who(agent_name), name=name, category=category, quantity=quantity, unit=unit,
            low_stock_threshold=low_stock_threshold, expires_on=expires_on, purchased_on=purchased_on,
            tags=tags, notes=notes,
        )

    @tool(WRITE)
    def adjust_quantity(item_id: int, delta: float, reason: str | None = None, agent_name: str | None = None) -> dict[str, Any]:
        """Record using up or restocking an item: delta=-1 uses one, delta=6 adds six. Quantity cannot go below zero. The item is kept at zero so it can appear on the shopping list."""
        return inv.adjust_quantity(item_id, delta, reason, actor=who(agent_name))

    @tool(WRITE)
    def move_item(item_id: int, to_container: str, quantity: float | None = None, agent_name: str | None = None) -> dict[str, Any]:
        """Move an item to another container (e.g. from the fridge to the freezer). Pass quantity to move only part of it; the rest stays behind."""
        return inv.move_item(item_id, to_container, quantity, actor=who(agent_name))

    @tool(DESTRUCTIVE)
    def remove_item(item_id: int, reason: str | None = None, agent_name: str | None = None) -> dict[str, Any]:
        """Delete an item entirely (thrown out, donated, given away). Its history is kept. To record partial use, use adjust_quantity instead."""
        return inv.remove_item(item_id, reason, actor=who(agent_name))

    # --------------------------------------------------------------- reports

    @tool(READ)
    def get_inventory_summary() -> dict[str, Any]:
        """Overview of the whole home: every container with its item count, plus counts of low-stock, out-of-stock, expired, and soon-to-expire items and a breakdown by category. A good first call."""
        return inv.summary()

    @tool(READ)
    def get_shopping_list() -> list[dict[str, Any]]:
        """Items that need buying: at or below their low-stock threshold, or expired. Each entry says why."""
        return inv.shopping_list()

    @tool(READ)
    def get_history(item_id: int | None = None, container: str | None = None, limit: int = 50) -> list[dict[str, Any]]:
        """Recent changes, newest first, with who made them. Filter by item id or container to answer questions like "who used the last of the milk?"."""
        return inv.history(item_id, container, limit)

    # ------------------------------------------------------------- resources

    @mcp.resource("inventory://summary", mime_type="application/json")
    def summary_resource() -> str:
        """Overview of the home inventory."""
        return json.dumps(inv.summary(), indent=2)

    @mcp.resource("inventory://containers/{container}", mime_type="application/json")
    def container_resource(container: str) -> str:
        """One container and everything in it."""
        return json.dumps(inv.get_container(container), indent=2)

    @mcp.resource("inventory://shopping-list", mime_type="application/json")
    def shopping_list_resource() -> str:
        """Items that need buying."""
        return json.dumps(inv.shopping_list(), indent=2)

    # --------------------------------------------------------------- prompts

    @mcp.prompt()
    def stock_a_container(container: str) -> str:
        """Walk through a container and record what is in it."""
        return (
            f"Help me record what is in my {container}. If it does not exist yet, create it with a sensible kind. "
            "Ask me to list what I see, a shelf or section at a time, then add each item with add_item, "
            "including quantities, units, categories, and expiration dates where they apply. "
            "Finish by showing the container with get_container."
        )

    @mcp.prompt()
    def weekly_check() -> str:
        """Review what is expiring, running low, or already gone."""
        return (
            "Check my home inventory. Use find_items with expiring_within_days=7 and get_shopping_list. "
            "Tell me what to use first, what has expired and should be thrown out, and what to buy, "
            "grouped by store section. Do not change anything until I confirm."
        )

    return mcp


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(prog="home-inventory-mcp", description=__doc__.splitlines()[0])
    parser.add_argument("--db", help="SQLite file (default: $HOME_INVENTORY_DB or ~/.home-inventory/inventory.db)")
    parser.add_argument("--http", action="store_true", help="Serve Streamable HTTP instead of stdio")
    parser.add_argument("--host", default="127.0.0.1", help="HTTP bind address (default 127.0.0.1)")
    parser.add_argument("--port", type=int, default=8765, help="HTTP port (default 8765)")
    args = parser.parse_args(argv)

    server = build_server(Inventory(args.db) if args.db else None)
    if not args.http:
        server.run()
        return
    try:
        server.run("streamable-http", host=args.host, port=args.port)
    except TypeError:
        # MCP SDK 1.x reads host and port from settings rather than run() arguments.
        server.settings.host, server.settings.port = args.host, args.port
        server.run("streamable-http")


if __name__ == "__main__":
    main()
