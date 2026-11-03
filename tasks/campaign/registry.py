#!/usr/bin/env python3
"""Campaign task registry for the 12-hour CRNT formalization campaign.

Machine-readable state for every worker task.  The orchestrator is the only
writer; workers read their own entry and never edit this file.

    python3 tasks/campaign/registry.py list
    python3 tasks/campaign/registry.py add --id W01 --leaf E3 --theorem "..." ...
    python3 tasks/campaign/registry.py set W01 --status VERIFIED --commit abc123
    python3 tasks/campaign/registry.py stats
"""
from __future__ import annotations

import argparse
import json
import time
from pathlib import Path

REG = Path(__file__).resolve().parent / "registry.json"

STATUSES = {
    "QUEUED", "RUNNING", "VERIFYING", "VERIFIED", "PARTIAL", "BLOCKED",
    "REJECTED", "INTEGRATED",
}


def load() -> dict:
    if REG.exists():
        return json.loads(REG.read_text())
    return {"campaign": {}, "tasks": {}}


def save(d: dict) -> None:
    REG.write_text(json.dumps(d, indent=1, sort_keys=False) + "\n")


def main() -> None:
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)

    sub.add_parser("list")
    sub.add_parser("stats")
    p = sub.add_parser("add")
    p.add_argument("--id", required=True)
    p.add_argument("--leaf", default="")
    p.add_argument("--theorem", default="")
    p.add_argument("--files", default="")
    p.add_argument("--deps", default="")
    p.add_argument("--priority", default="B")
    p.add_argument("--difficulty", default="medium")
    p.add_argument("--note", default="")
    p = sub.add_parser("set")
    p.add_argument("id")
    p.add_argument("--status", choices=sorted(STATUSES))
    p.add_argument("--commit", default=None)
    p.add_argument("--note", default=None)
    p.add_argument("--verify", default=None)

    a = ap.parse_args()
    d = load()

    if a.cmd == "add":
        if a.id in d["tasks"]:
            raise SystemExit(f"task {a.id} already exists")
        d["tasks"][a.id] = {
            "id": a.id,
            "leaf": a.leaf,
            "theorem": a.theorem,
            "files": [f for f in a.files.split(",") if f],
            "deps": [f for f in a.deps.split(",") if f],
            "priority": a.priority,
            "difficulty": a.difficulty,
            "status": "QUEUED",
            "worker": "",
            "last_progress": time.strftime("%Y-%m-%dT%H:%M:%S"),
            "commit": "",
            "verification": "",
            "note": a.note,
        }
        save(d)
        print(f"added {a.id}")
        return

    if a.cmd == "set":
        t = d["tasks"].get(a.id)
        if t is None:
            raise SystemExit(f"unknown task {a.id}")
        if a.status:
            t["status"] = a.status
        if a.commit is not None:
            t["commit"] = a.commit
        if a.note is not None:
            t["note"] = a.note
        if a.verify is not None:
            t["verification"] = a.verify
        t["last_progress"] = time.strftime("%Y-%m-%dT%H:%M:%S")
        save(d)
        print(f"{a.id}: {t['status']}")
        return

    if a.cmd == "list":
        for t in d["tasks"].values():
            print(f"{t['id']:>6} {t['status']:<10} {t['priority']} {t['leaf']:<4} "
                  f"{t['theorem'][:90]}")
        return

    if a.cmd == "stats":
        from collections import Counter
        c = Counter(t["status"] for t in d["tasks"].values())
        print("tasks:", len(d["tasks"]))
        for k, v in sorted(c.items()):
            print(f"  {k}: {v}")
        c2 = Counter(t["leaf"] for t in d["tasks"].values())
        print("by leaf:", dict(sorted(c2.items())))
        return


if __name__ == "__main__":
    main()
