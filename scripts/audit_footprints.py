#!/usr/bin/env python3
"""audit_footprints.py — per-declaration axiom footprints from the Lean kernel.

The authoritative axiom set of every kernel declaration is the one the
kernel itself reports: `#print axioms`. This script generates a temporary
`import Logos` module with a `#print axioms` line per user-authored
declaration (from `formal/depgraph.json`), runs `lake env lean`, parses the
output, and writes `formal/axiom_audit.json`:

    {
      "Logos.Core.someTrue": ["propext", "Classical.choice", "Quot.sound"],
      "Logos.Agency.Cogito": [],
      "Logos.Love.T14_eternalRelation": ["Logos.Love.AxPersonStability", ...],
      ...
    }

Why not the graph's own `axioms`/`customAxioms` fields? LeanDepViz
undercounts transitively (a node lists only the axioms of its direct
dependencies), while `#print axioms` gives the exact transitive footprint —
the mechanism AGENTS.md already mandates for footprint inspection. The graph
is still used for the dependency *edges* (the deduction chain).

Guards (a clean run is silent and writes the file):
  * `sorryAx` never appears;
  * every Logos axiom in any footprint is a declared axiom node of the graph;
  * everything else is a known meta-logic constant ({propext, Classical.choice,
    Quot.sound}).

Run before `build_deduction.py` whenever the Lean sources change (see
AGENTS.md). Requires the Lean toolchain (`$HOME/.elan/bin` on PATH).

Stdlib only. UTF-8 required.
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FORMAL = ROOT / "formal"
DEPGRAPH_PATH = FORMAL / "depgraph.json"
OUT_PATH = FORMAL / "axiom_audit.json"
AUDIT_TMP = FORMAL / ".audit_footprints.lean"

META_LOGIC = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = {"sorryAx"}

DOC_LINE_RE = re.compile(
    r"^'([^']+)' (does not depend on any axioms|depends on axioms:)")
TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")


def _short(name: str) -> str:
    """Bare identifier for meta-logic classification (`Init.Core.propext` → propext)."""
    return name.rsplit(".", 1)[-1]


def _tokens(frag: str) -> list[str]:
    """Axiom-name tokens in a fragment (single `Logos.X` names, `Logos` skipped)."""
    return [t for t in TOKEN_RE.findall(frag) if t != "Logos"]


def parse_print_axioms(text: str) -> dict:
    """Parse `#print axioms` output → {declName: [axiom names]}."""
    footprints: dict = {}
    cur: str | None = None
    buf: list[str] = []

    def ingest(frag: str) -> bool:
        """Add `frag`'s tokens to buf; True once the list is closed with `]`."""
        buf.extend(_tokens(frag))
        return "]" in frag

    for raw in text.splitlines():
        s = raw.strip()
        m = DOC_LINE_RE.match(s)
        if m:
            if cur is not None:  # kernel output never does this; safety only
                footprints[cur] = buf
            cur, verb = m.group(1), m.group(2)
            if verb == "does not depend on any axioms":
                footprints[cur] = []
                cur = None
                continue
            buf = []
            # the opening line may already hold the whole multi-axiom list
            if ingest(s.split("axioms: ", 1)[1]):
                footprints[cur] = buf
                cur = None
            continue
        if cur is not None and ingest(s):
            footprints[cur] = buf
            cur = None
    return footprints


def main() -> int:
    if not DEPGRAPH_PATH.exists():
        print(f"ERROR: {DEPGRAPH_PATH} missing. Run:\n"
              "  cd formal && lake exe depviz --roots Logos --json-out depgraph.json --dot-out depgraph.dot",
              file=sys.stderr)
        return 1

    graph = json.loads(DEPGRAPH_PATH.read_text(encoding="utf-8"))
    nodes = [n for n in graph["nodes"] if n["kind"] in ("thm", "def", "axiom")]
    names = sorted(n["fullName"] for n in nodes)
    declared_axioms = {n["fullName"] for n in graph["nodes"] if n["kind"] == "axiom"}
    print(f"auditing {len(names)} declarations via #print axioms …")

    audit_body = ["import Logos"] + [f"#print axioms {n}" for n in names]
    AUDIT_TMP.write_text("\n".join(audit_body) + "\n", encoding="utf-8")
    lake = "lake"
    fallback = Path.home() / ".elan" / "bin" / "lake"
    if subprocess.run(["which", "lake"], capture_output=True).returncode != 0 and fallback.exists():
        lake = str(fallback)
    try:
        proc = subprocess.run(
            [lake, "env", "lean", str(AUDIT_TMP)],
            cwd=str(FORMAL), capture_output=True, text=True, timeout=600,
        )
    finally:
        AUDIT_TMP.unlink(missing_ok=True)
    if proc.returncode != 0:
        print(f"ERROR: `lake env lean` failed ({proc.returncode}):\n{proc.stdout}\n{proc.stderr}",
              file=sys.stderr)
        return 1

    footprints = parse_print_axioms(proc.stdout)
    missing = [n for n in names if n not in footprints]
    if missing:
        print(f"ERROR: audit incomplete — no output for: {missing}", file=sys.stderr)
        return 1

    bad_forbidden = sorted({a for ax in footprints.values() for a in ax
                            if _short(a) in FORBIDDEN})
    if bad_forbidden:
        print(f"ERROR: unexpected kernel unavailability: {bad_forbidden}", file=sys.stderr)
        return 1

    bad_unknown = sorted({a for ax in footprints.values() for a in ax
                          if not a.startswith("Logos.") and a not in META_LOGIC
                          and _short(a) not in {x.rsplit(".", 1)[-1] for x in META_LOGIC}})
    if bad_unknown:
        print(f"ERROR: axioms outside declared set + meta-logic: {bad_unknown}", file=sys.stderr)
        return 1
    underdeclared = sorted({a for ax in footprints.values() for a in ax
                            if a.startswith("Logos.") and a not in declared_axioms})
    if underdeclared:
        print(f"ERROR: Logos axioms in footprints not declared as axiom nodes: {underdeclared}",
              file=sys.stderr)
        return 1

    unused = sorted(declared_axioms - {a for ax in footprints.values() for a in ax})
    OUT_PATH.write_text(json.dumps(footprints, indent=1, ensure_ascii=False) + "\n",
                        encoding="utf-8")
    print(f"wrote {OUT_PATH} ({len(footprints)} declarations)")
    if unused:
        print(f"note: declared axioms not used by any audited declaration: {unused}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())