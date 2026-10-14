#!/usr/bin/env python3
"""audit_footprints.py — per-declaration axiom footprints from the Lean kernel for logos4.

Extracts all top-level declarations from formal/Logos/*.lean, generates a temporary
`.audit_footprints.lean` with `#print axioms` lines, runs `lake env lean`, parses
the exact kernel axiom footprints, and writes `formal/axiom_audit.json`.
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FORMAL = ROOT / "formal"
LEAN_DIR = FORMAL / "Logos"
OUT_PATH = FORMAL / "axiom_audit.json"
AUDIT_TMP = FORMAL / ".audit_footprints.lean"

DECL_RE = re.compile(r"^[ \t]*(?:theorem|def|noncomputable def|inductive|structure|axiom)\s+([A-Za-z0-9_]+)", re.MULTILINE)
DOC_LINE_RE = re.compile(r"^'([^']+)' (does not depend on any axioms|depends on axioms:)")
TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")

def parse_print_axioms(text: str) -> dict[str, list[str]]:
    footprints: dict[str, list[str]] = {}
    cur: str | None = None
    buf: list[str] = []

    def ingest(frag: str) -> bool:
        buf.extend([t for t in TOKEN_RE.findall(frag) if t != "Logos"])
        return "]" in frag

    for raw in text.splitlines():
        line = raw.strip()
        m = DOC_LINE_RE.match(line)
        if m:
            if cur is not None:
                footprints[cur] = list(dict.fromkeys(buf))
            cur = m.group(1)
            buf = []
            if m.group(2).startswith("does not"):
                footprints[cur] = []
                cur = None
            else:
                tail = line[m.end():]
                if ingest(tail):
                    footprints[cur] = list(dict.fromkeys(buf))
                    cur = None
            continue
        if cur is not None:
            if ingest(line):
                footprints[cur] = list(dict.fromkeys(buf))
                cur = None

    if cur is not None:
        footprints[cur] = list(dict.fromkeys(buf))

    return footprints

def main():
    modules = ["System", "Elimination", "Agency", "Source"]
    decls = []
    for mod in modules:
        path = LEAN_DIR / f"{mod}.lean"
        if not path.exists():
            continue
        code = path.read_text(encoding="utf-8")
        for m in DECL_RE.finditer(code):
            name = m.group(1)
            if not name.startswith("_"):
                decls.append(f"Logos.OntologicalIncompleteness.{name}")

    decls = sorted(set(decls))
    print(f"Auditing {len(decls)} declarations across {len(modules)} modules...")

    lines = ["import Logos\n", "open Classical\n", "open Logos\n", "open Logos.OntologicalIncompleteness\n\n"]
    for d in decls:
        lines.append(f"#print axioms {d}\n")

    AUDIT_TMP.write_text("".join(lines), encoding="utf-8")

    try:
        res = subprocess.run(
            ["lake", "env", "lean", str(AUDIT_TMP)],
            cwd=str(FORMAL),
            capture_output=True,
            text=True,
            check=False
        )
        output = res.stdout + "\n" + res.stderr
        footprints = parse_print_axioms(output)
        print(f"Successfully extracted {len(footprints)} footprints.")
        OUT_PATH.write_text(json.dumps(footprints, indent=2), encoding="utf-8")
        print(f"Wrote {OUT_PATH}")
    finally:
        if AUDIT_TMP.exists():
            AUDIT_TMP.unlink()

if __name__ == "__main__":
    main()
