"""Command-line access to the inventory, printing JSON.

For agents that run shell commands rather than speak MCP. Every MCP tool is
available under the same name, with arguments given as key=value:

    home-inventory list_containers
    home-inventory create_container name="Kitchen fridge" kind=refrigerator location=Kitchen
    home-inventory add_item name="Whole milk" container="Kitchen fridge" quantity=1 unit=gallon expires_on=+7
    home-inventory find_items query=milk
    home-inventory adjust_quantity item_id=3 delta=-1 agent_name=openclaw

Values are read as JSON when they parse (numbers, true/false, ["lists"]),
and as plain text otherwise. Errors go to stderr as {"error": ...} with exit code 1.
"""

from __future__ import annotations

import argparse
import inspect
import json
import sys
from typing import Any

from .db import Inventory, InventoryError

# Tool name -> (Inventory method, argument renames). Mirrors server.py.
COMMANDS: dict[str, tuple[str, dict[str, str]]] = {
    "list_containers": ("list_containers", {}),
    "get_container": ("get_container", {}),
    "create_container": ("create_container", {"agent_name": "actor"}),
    "update_container": ("update_container", {"agent_name": "actor"}),
    "delete_container": ("delete_container", {"agent_name": "actor"}),
    "add_item": ("add_item", {"agent_name": "actor"}),
    "find_items": ("find_items", {}),
    "get_item": ("get_item", {}),
    "update_item": ("update_item", {"agent_name": "actor"}),
    "adjust_quantity": ("adjust_quantity", {"agent_name": "actor"}),
    "move_item": ("move_item", {"agent_name": "actor"}),
    "remove_item": ("remove_item", {"agent_name": "actor"}),
    "get_inventory_summary": ("summary", {}),
    "get_shopping_list": ("shopping_list", {}),
    "get_history": ("history", {}),
}


# Text fields stay text even when they look like JSON ("7 Up", "2024", "true").
TEXT_KEYS = {
    "name", "container", "to_container", "move_items_to", "parent", "kind", "location", "description",
    "category", "unit", "notes", "query", "tag", "reason", "expires_on", "purchased_on", "agent_name",
}


def _value(key: str, text: str) -> Any:
    if key in TEXT_KEYS:
        return text
    try:
        return json.loads(text)
    except json.JSONDecodeError:
        return text


def _usage(name: str, method: Any, renames: dict[str, str]) -> str:
    back = {v: k for k, v in renames.items()}
    params = []
    for p in inspect.signature(method).parameters.values():
        if p.kind is p.VAR_KEYWORD:
            fields = "name kind location description parent" if name == "update_container" else (
                "name category quantity unit low_stock_threshold expires_on purchased_on tags notes")
            params += [f"[{f}]" for f in fields.split()]
            continue
        key = back.get(p.name, p.name)
        params.append(key if p.default is p.empty else f"[{key}]")
    doc = (inspect.getdoc(method) or "").splitlines()
    return f"{name} {' '.join(params)}".rstrip() + (f"\n    {doc[0]}" if doc else "")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="home-inventory",
        description="Home inventory in SQLite. Prints JSON.",
        epilog="Run 'home-inventory tools' to list commands and their arguments.",
    )
    parser.add_argument("--db", help="SQLite file (default: $HOME_INVENTORY_DB or ~/.home-inventory/inventory.db)")
    parser.add_argument("command", help="a tool name, or 'tools'")
    parser.add_argument("args", nargs="*", metavar="key=value")
    ns = parser.parse_args(argv)

    inv = Inventory(ns.db) if ns.db else Inventory()
    try:
        if ns.command == "tools":
            for name, (method, renames) in COMMANDS.items():
                print(_usage(name, getattr(inv, method), renames))
            return 0
        if ns.command not in COMMANDS:
            raise InventoryError(f"Unknown command {ns.command!r}. Run 'home-inventory tools'.")
        method, renames = COMMANDS[ns.command]
        kwargs: dict[str, Any] = {}
        if "agent_name" in renames:
            kwargs["actor"] = "cli"
        for pair in ns.args:
            key, sep, text = pair.partition("=")
            if not sep:
                raise InventoryError(f"Arguments are key=value; got {pair!r}")
            kwargs[renames.get(key, key)] = _value(key, text)
        result = getattr(inv, method)(**kwargs)
    except (InventoryError, TypeError) as exc:
        print(json.dumps({"error": str(exc)}), file=sys.stderr)
        return 1
    finally:
        inv.close()
    print(json.dumps(result, indent=2, default=str))
    return 0


if __name__ == "__main__":
    sys.exit(main())
