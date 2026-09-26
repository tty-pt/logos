#!/usr/bin/env python3
"""audit_stipulations.py — verify the definitional-stipulation registry.

`formal/Logos/Stipulations.lean` registers each definitional stipulation in
scope as a `def <name> : Stipulation where` block with one field per line
(`name`, `location`, `anchor`, `tag`, `cost`, `dependents`). This script:

  1. parses the registry from the Lean source (rigid shape; see the module doc);
  2. verifies every `location` (`File.lean:line`) exists and the `anchor`
     substring appears on that line (drift check against silent stipulation edits);
  3. verifies every dependent theorem name resolves to exactly one kernel node
     in `formal/depgraph.json`;
  4. writes `formal/stipulation_audit.json` (consumed by
     `scripts/build_deduction.py` for the ◈ stipulation badge).

A clean run regenerates the file and is silent; any failure exits 1.
Requires `formal/depgraph.json` (run `make depviz` first).
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FORMAL = ROOT / "formal"
LEAN_PATH = FORMAL / "Logos" / "Stipulations.lean"
DEPGRAPH_PATH = FORMAL / "depgraph.json"
OUT_PATH = FORMAL / "stipulation_audit.json"

ENTRY_RE = re.compile(r"^def\s+(\w+)\s*:\s*Stipulation\s+where\s*$")
FIELD_RE = re.compile(r"^\s*(name|location|anchor|tag|cost|dependents)\s*:=\s*(.+?)\s*$")
STR_RE = re.compile(r'^"(.*)"$')
LIST_RE = re.compile(r"^\[(.*)\]$")
KNOWN_TAGS = {"StipulationTag.VOCAB", "StipulationTag.SEM", "StipulationTag.META"}


def parse_registry(text: str) -> list[dict]:
    entries, cur = [], None
    in_doc = False
    for raw in text.splitlines():
        s = raw.strip()
        if "/--" in raw:
            in_doc = True
        if in_doc:
            if "-/" in raw:
                in_doc = False
            continue
        if not s or s.startswith("--"):
            continue
        m = ENTRY_RE.match(raw)
        if m:
            if cur is not None:
                entries.append(cur)
            cur = {"def": m.group(1)}
            continue
        if cur is None:
            continue  # non-registry code (inductives, structures, list defs)
        fm = FIELD_RE.match(raw)
        if not fm:
            if cur is not None and {"name", "location", "anchor", "tag",
                                    "cost", "dependents"} <= set(cur):
                entries.append(cur)  # entry complete; trailing non-registry code
                cur = None
                continue
            # continuation lines are not part of the machine contract
            raise SystemExit(
                f"ERROR: unparsable registry line in Stipulations.lean: {raw!r}")
            continue
        key, val = fm.group(1), fm.group(2)
        if key == "dependents":
            lm = LIST_RE.match(val)
            if not lm:
                raise SystemExit(f"ERROR: dependents field is not a list: {raw!r}")
            cur[key] = [s.strip().strip('"') for s in lm.group(1).split(",") if s.strip()]
        elif key == "tag":
            if val not in KNOWN_TAGS:
                raise SystemExit(f"ERROR: unknown stipulation tag: {val!r}")
            cur[key] = val.split(".")[-1]
        else:
            sm = STR_RE.match(val)
            if not sm:
                raise SystemExit(f"ERROR: field {key} is not a string: {raw!r}")
            cur[key] = sm.group(1)
    if cur is not None:
        entries.append(cur)
    required = {"name", "location", "anchor", "tag", "cost", "dependents"}
    for e in entries:
        missing = required - set(e)
        if missing:
            raise SystemExit(f"ERROR: entry {e.get('def')} missing fields: {sorted(missing)}")
        if e["name"] != e["def"]:
            raise SystemExit(
                f"ERROR: entry name {e['name']!r} != def name {e['def']!r}")
    return entries


def check_locations(entries: list[dict]) -> None:
    for e in entries:
        loc = e["location"]
        m = re.fullmatch(r"(\w+\.lean):(\d+)", loc)
        if not m:
            raise SystemExit(f"ERROR: bad location shape: {loc!r}")
        path = FORMAL / "Logos" / m.group(1)
        lineno = int(m.group(2))
        if not path.exists():
            raise SystemExit(f"ERROR: stipulation location missing: {loc}")
        lines = path.read_text(encoding="utf-8").splitlines()
        if not (1 <= lineno <= len(lines)):
            raise SystemExit(f"ERROR: stipulation location out of range: {loc}")
        if e["anchor"] not in lines[lineno - 1]:
            raise SystemExit(
                f"ERROR: stipulation anchor drift at {loc}: "
                f"expected {e['anchor']!r} on line: {lines[lineno - 1]!r}")


def check_dependents(entries: list[dict], graph: dict) -> None:
    names = [n["fullName"] for n in graph["nodes"]]
    for e in entries:
        for dep in e["dependents"]:
            hits = [n for n in names if n.rsplit(".", 1)[-1] == dep]
            if len(hits) != 1:
                raise SystemExit(
                    f"ERROR: dependent {dep!r} of stipulation {e['name']!r} "
                    f"resolves to {len(hits)} kernel nodes: {hits}")


def main() -> int:
    if not DEPGRAPH_PATH.exists():
        print(f"ERROR: {DEPGRAPH_PATH} missing. Run `make depviz` first.",
              file=sys.stderr)
        return 1
    entries = parse_registry(LEAN_PATH.read_text(encoding="utf-8"))
    if not entries:
        print("ERROR: no stipulation entries parsed from Stipulations.lean",
              file=sys.stderr)
        return 1
    graph = json.loads(DEPGRAPH_PATH.read_text(encoding="utf-8"))
    check_locations(entries)
    check_dependents(entries, graph)
    OUT_PATH.write_text(json.dumps({"stipulations": entries}, indent=1,
                                   ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"wrote {OUT_PATH} ({len(entries)} stipulations, "
          f"{sum(len(e['dependents']) for e in entries)} dependents verified)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
