"""Drive the real MCP server over stdio, as an agent would."""

import json
import sys

import anyio
import pytest
from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client


def wire(model):
    """The JSON an agent sees on the wire. SDK 1.x and 2.x name Python attributes differently."""
    return model.model_dump(by_alias=True, exclude_none=True)


def is_error(result):
    return bool(wire(result).get("isError"))


def payload(result):
    assert not is_error(result), result.content
    data = wire(result).get("structuredContent")
    if data is not None:
        return data["result"] if isinstance(data, dict) and set(data) == {"result"} else data
    return json.loads(result.content[0].text)


async def session_run(db_path, body):
    params = StdioServerParameters(
        command=sys.executable, args=["-m", "home_inventory", "--db", str(db_path)]
    )
    async with stdio_client(params) as (read, write):
        async with ClientSession(read, write) as session:
            await session.initialize()
            await body(session)


def test_agent_workflow_over_stdio(tmp_path):
    async def body(session):
        tools = {t.name: t for t in (await session.list_tools()).tools}
        assert {"create_container", "add_item", "find_items", "adjust_quantity", "move_item",
                "get_shopping_list", "get_inventory_summary", "get_history"} <= set(tools)
        assert wire(tools["find_items"].annotations)["readOnlyHint"] is True
        assert wire(tools["remove_item"].annotations)["destructiveHint"] is True

        await session.call_tool("create_container", {"name": "Kitchen fridge", "kind": "refrigerator"})
        await session.call_tool("create_container", {"name": "Bathroom closet", "kind": "closet"})
        item = payload(await session.call_tool("add_item", {
            "name": "Toothpaste", "container": "bathroom closet", "quantity": 2,
            "low_stock_threshold": 1, "category": "toiletries", "agent_name": "gemini",
        }))
        used = payload(await session.call_tool("adjust_quantity", {"item_id": item["id"], "delta": -1}))
        assert used["quantity"] == 1 and used["low_stock"]

        shopping = payload(await session.call_tool("get_shopping_list", {}))
        assert [i["name"] for i in shopping] == ["Toothpaste"]

        found = payload(await session.call_tool("find_items", {"query": "tooth"}))
        assert found[0]["container"] == "Bathroom closet"

        error = await session.call_tool("add_item", {"name": "Milk", "container": "Garage"})
        assert is_error(error) and "Known containers" in error.content[0].text

        summary = json.loads((await session.read_resource("inventory://summary")).contents[0].text)
        assert summary["total_items"] == 1

        prompts = {p.name for p in (await session.list_prompts()).prompts}
        assert {"stock_a_container", "weekly_check"} <= prompts

    anyio.run(session_run, tmp_path / "home.db", body)
