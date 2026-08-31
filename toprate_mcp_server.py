"""
toprate_mcp_server.py
----------------------
Local MCP server exposing TopRate's own upstream API (api.toprate.au) as
Claude Code tools - lets a session query live race/runner data directly,
separately from this repo's own fetch pipeline and its CSV/JSON output.

api.toprate.au is a Supabase backend: email/password login gets a JWT via
the standard GoTrue endpoint, then data comes back through PostgREST RPC
calls. Auth here mirrors toprate_daily.py's login()/rpc() exactly (same
credential sources, same endpoint shapes) - duplicated rather than
imported, since toprate_daily.py is a standalone pipeline script, not a
library module.

Setup:
    pip install mcp requests
    Add to .mcp.json (see the repo's own .mcp.json for the exact entry) -
    credentials come from TOPRATE_EMAIL/TOPRATE_PASSWORD env vars or the
    gitignored toprate_credentials.txt, same as toprate_daily.py.

This is a read-only wrapper around TopRate's existing RPC functions - it
doesn't add capability toprate_daily.py doesn't already use, just exposes
it interactively.
"""

import os
import time
from pathlib import Path

import requests
from mcp.server.mcpserver import MCPServer

API_BASE = "https://api.toprate.au"
ANON_KEY = "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.ewogICJyb2xlIjogImFub24iLAogICJpc3MiOiAic3VwYWJhc2UiLAogICJpYXQiOiAxNjkxNjc2MDAwLAogICJleHAiOiAxODQ5NTI4ODAwCn0.MsNV6VIGz0f4K-wgKSwv1b2cnb76x7OcvrHm8HosHT4"
_CREDENTIALS_FILE = Path(__file__).parent / "toprate_credentials.txt"


def _load_toprate_credentials():
    email = os.environ.get("TOPRATE_EMAIL", "").strip()
    password = os.environ.get("TOPRATE_PASSWORD", "").strip()
    if email and password:
        return email, password
    if _CREDENTIALS_FILE.exists():
        lines = _CREDENTIALS_FILE.read_text().splitlines()
        if len(lines) >= 2 and lines[0].strip() and lines[1].strip():
            return lines[0].strip(), lines[1].strip()
    return None, None


EMAIL, PASSWORD = _load_toprate_credentials()

# Cached session state - login() runs lazily on first tool call (not at
# import time), so the server still starts even if credentials are wrong;
# the error surfaces as a normal tool-call failure instead of a crash Claude
# Code can't see the reason for.
_jwt = None
_expires_at = 0.0


def _login():
    if not EMAIL or not PASSWORD:
        raise RuntimeError(
            "TopRate credentials not found. Set TOPRATE_EMAIL and "
            "TOPRATE_PASSWORD env vars, or create toprate_credentials.txt "
            "(gitignored, repo root) with the email on line 1 and the "
            "password on line 2 - same as toprate_daily.py.")
    resp = requests.post(
        f"{API_BASE}/auth/v1/token?grant_type=password",
        headers={"apikey": ANON_KEY, "Content-Type": "application/json"},
        json={"email": EMAIL, "password": PASSWORD})
    resp.raise_for_status()
    data = resp.json()
    token = data.get("access_token")
    if not token:
        raise ValueError(f"Login failed: {data}")
    global _jwt, _expires_at
    _jwt = token
    _expires_at = float(data.get("expires_at", 0))
    return token


def _ensure_jwt():
    # 60s safety margin - a call that starts just before expiry shouldn't
    # race the token dying mid-request.
    if _jwt is None or time.time() > _expires_at - 60:
        _login()
    return _jwt


def _rpc(name, params=None, timeout=30):
    jwt = _ensure_jwt()
    resp = requests.post(
        f"{API_BASE}/rest/v1/rpc/{name}",
        headers={"apikey": ANON_KEY, "Authorization": f"Bearer {jwt}",
                 "Content-Type": "application/json"},
        json=params or {}, timeout=timeout)
    if resp.status_code == 401:
        # Server invalidated the token early (or clock drift beat our
        # expiry margin) - one fresh-login retry before giving up.
        _login()
        resp = requests.post(
            f"{API_BASE}/rest/v1/rpc/{name}",
            headers={"apikey": ANON_KEY, "Authorization": f"Bearer {_jwt}",
                     "Content-Type": "application/json"},
            json=params or {}, timeout=timeout)
    resp.raise_for_status()
    return resp.json()


mcp = MCPServer(
    name="toprate-api",
    instructions=(
        "Read-only access to TopRate's own upstream racing data API "
        "(api.toprate.au) - the same source this project's daily fetch "
        "pipeline (toprate_daily.py) pulls from, queried live instead of "
        "through the repo's CSV/JSON snapshots. rc_id is TopRate's race "
        "ID (the same id used as race_id/rc_id throughout this repo)."
    ),
)


@mcp.tool()
def list_upcoming_races() -> dict:
    """List upcoming race meetings/races from TopRate's calendar."""
    return _rpc("get_calendar_upcoming")


@mcp.tool()
def get_race_detail(rc_id: str) -> dict:
    """Full race + runner details (fields, prices, ratings) for one race."""
    return _rpc("get_race_detail", {"rc_id": rc_id})


@mcp.tool()
def get_race_wpr_chart(rc_id: str) -> dict:
    """Per-runner WPR rating history/chart data for one race."""
    return _rpc("get_race_wpr_chart", {"rc_id": rc_id})


@mcp.tool()
def get_race_stats(rc_id: str) -> dict:
    """Race-level statistics for one race."""
    return _rpc("get_race_stats", {"rc_id": rc_id})


@mcp.tool()
def get_race_results(rc_id: str) -> dict:
    """Results (finishing order, margins, starting prices) for one race."""
    return _rpc("get_race_results", {"rc_id": rc_id})


@mcp.tool()
def get_race_cache(rc_id: str) -> dict:
    """TopRate's own per-account cached view of one race (their user_cache_race RPC)."""
    return _rpc("get_user_cache_race", {"rc_id": rc_id})


if __name__ == "__main__":
    mcp.run()
