"""A SQLite home inventory with an MCP server for AI agents."""

from .db import CONTAINER_KINDS, Inventory, InventoryError

__all__ = ["CONTAINER_KINDS", "Inventory", "InventoryError"]
__version__ = "0.1.0"
