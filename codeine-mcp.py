from typing import Any
import httpx
from mcp.server.fastmcp import FastMCP

mcp = FastMCP("codeine")

BOOK_DIRECTORY = "data/principia"

@mcp.tool()
async def get_page(page: int) -> str: 
    """
    Get a page from the book.
    """
    with open(f"{BOOK_DIRECTORY}/{page:04d}.png", "rb") as f:
        return f.read()