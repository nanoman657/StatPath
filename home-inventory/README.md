# Home Inventory

A home inventory for one household, stored in SQLite, with an [MCP](https://modelcontextprotocol.io) server so AI agents can read and update it.

Things live in **containers**: the refrigerator, the freezer drawer inside it, the wardrobe, the toiletries closet, a shelf in the pantry. Containers can nest. Each **item** has a quantity and unit, and can also have a category, tags, notes, an expiration date, a purchase date, and a low-stock threshold. Every change goes into a history log with the name of the agent that made it.

## Install

Requires Python 3.10+.

```bash
cd home-inventory
pip install -e .            # or: pipx install ./home-inventory
```

This installs two commands:

| Command | What it is |
|---|---|
| `home-inventory-mcp` | The MCP server. Uses stdio by default; pass `--http` to serve Streamable HTTP at `http://127.0.0.1:8765/mcp`. |
| `home-inventory` | The same operations as a CLI that prints JSON, for agents that run shell commands instead of speaking MCP. |

Both commands use the same database file. By default that is `~/.home-inventory/inventory.db`. You can change it with `--db PATH` or the `HOME_INVENTORY_DB` environment variable. Because the file runs in WAL mode, the CLI and a running server can use it at the same time.

## Connecting agents

Most agent hosts accept the same MCP server entry. File locations differ from host to host, so check your agent's MCP settings.

**Local (stdio).** Use this when the agent runs on the same machine as the database:

```json
{
  "mcpServers": {
    "home-inventory": {
      "command": "home-inventory-mcp",
      "env": {
        "HOME_INVENTORY_DB": "/home/you/.home-inventory/inventory.db",
        "HOME_INVENTORY_AGENT": "gemini"
      }
    }
  }
}
```

`HOME_INVENTORY_AGENT` is the name written to the history log when a tool call does not pass `agent_name`. Give each agent its own name, so the history can tell you whether Gemini or OpenClaw used the last of the milk.

**By URL (Streamable HTTP).** Use this for agents on another device, or several agents sharing one running server:

```bash
home-inventory-mcp --http --host 127.0.0.1 --port 8765
```

Point the agent at `http://127.0.0.1:8765/mcp` (for example `"httpUrl"` in Gemini CLI, or `"url"` in most other clients). **The server has no authentication.** Keep it on `127.0.0.1` or a private network. If a cloud-hosted agent needs to reach it, put an authenticating tunnel or reverse proxy in front of it.

**Claude Code:** `claude mcp add home-inventory -- home-inventory-mcp`

**Skill-based agents (OpenClaw and others that load `SKILL.md` folders):** copy `skills/home-inventory/` into the agent's skills directory. The skill teaches the agent to use the `home-inventory` CLI, so this also works without MCP support.

**Anything else:** if the agent can run a shell command, it can use `home-inventory tools` to discover every operation.

## Tools

| Tool | Does |
|---|---|
| `get_inventory_summary` | All containers with item counts; low-stock, out-of-stock, expired, and expiring-this-week counts; items by category. A good first call. |
| `list_containers`, `get_container` | Containers, and everything inside one (including nested containers). |
| `create_container`, `update_container`, `delete_container` | Manage containers. Delete refuses to drop items unless you pass `move_items_to`. |
| `add_item` | Add stock. Merges into an existing entry with the same name, unit, and expiry in that container. |
| `find_items` | Search by words, container, category, tag, expiring-within-N-days, or low stock. |
| `get_item`, `update_item` | Read or correct one item. |
| `adjust_quantity` | Record use (`delta=-1`) or restocking (`delta=6`). Never goes below zero. |
| `move_item` | Move an item, or split part of it off into another container. |
| `remove_item` | Delete an item (thrown out, given away). Its history is kept. |
| `get_shopping_list` | Items at or below their low-stock threshold, or expired. |
| `get_history` | Who changed what, and when. |

There are also resources (`inventory://summary`, `inventory://shopping-list`, `inventory://containers/{name}`) and two prompts: `stock_a_container` walks through recording a container's contents, and `weekly_check` reviews what is expiring and what to buy.

Choices that make the server easier for agents to use:

- Tools take a container's **name** (case-insensitive) or its id, so agents do not have to look up ids first.
- Dates can be `2026-10-14`, `today`, `tomorrow`, or `+7`.
- Errors explain how to fix the call. For example, naming a container that does not exist returns the list of containers that do.
- Tools are annotated as read-only or destructive, so hosts can auto-approve reads and ask before deletes.

## Example

```bash
home-inventory create_container name="Kitchen fridge" kind=refrigerator location=Kitchen
home-inventory create_container name="Freezer drawer" kind=freezer parent="Kitchen fridge"
home-inventory create_container name="Wardrobe" kind=wardrobe location=Bedroom
home-inventory create_container name="Bathroom closet" kind=closet location="Upstairs bathroom"

home-inventory add_item name="Whole milk" container="kitchen fridge" unit=gallon expires_on=+7 low_stock_threshold=0
home-inventory add_item name="Wool sweater" container=Wardrobe category=tops tags='["winter"]' notes="navy, size M"
home-inventory add_item name="Toilet paper" container="Bathroom closet" quantity=12 unit=rolls low_stock_threshold=4

home-inventory find_items expiring_within_days=3
home-inventory get_shopping_list
```

## Develop

```bash
pip install -e ".[test]"
pytest
```

The tests cover the database layer and drive the real server over stdio with an MCP client. They pass with MCP Python SDK 1.x (1.10 and later) and 2.x.

Code layout: `home_inventory/db.py` holds all SQLite logic and has no MCP dependency. `server.py` and `cli.py` are thin layers over it.
