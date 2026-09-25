#!/usr/bin/env python3
"""Derive the GAPMAP claim-taxonomy tallies and axiom inventory from the kernel.

`formal/GAPMAP.md` carries four hand-maintained tallies in its "Summary counts"
block — truly axiom-free (`{}`), `CL`-only, vocabulary-only, and the PROVEN↑
claim list — plus a "Net inventory" line. Those are the only status-like values
in the corpus that are *not* machine-derived (every status/footprint cell is
checked by `scripts/audit_footprints.py`). This script recomputes them from
`formal/axiom_audit.json` (the authoritative `#print axioms` ledger) through
`build_deduction`'s own GAPMAP parser, claim resolver and footprint splitter, so
the numbers can be derived instead of transcribed.

Usage:
  python3 scripts/gapmap_taxonomy.py           # print the derived report
  python3 scripts/gapmap_taxonomy.py --check   # exit 1 if the counts or the
                                               # enumerated ID lists written
                                               # in GAPMAP.md have drifted
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import build_deduction as bd  # noqa: E402

BUCKETS = ("af", "cl", "vocab", "up")

BUCKET_LABELS = {
    "af": "truly axiom-free ({})",
    "cl": "`CL`-only",
    "vocab": "vocabulary-only",
    "up": "PROVEN↑ claims",
}

STATED_RE = {
    "af": re.compile(r"\*\*(\d+) truly axiom-free\*\*"),
    "cl": re.compile(r"\*\*(\d+) `CL`-only\*\*"),
    "vocab": re.compile(r"\*\*(\d+) vocabulary-only\*\*"),
    "up": re.compile(r"\*\*(\d+) claims\*\*"),
}


def load_context() -> tuple[dict, dict]:
    graph = bd.load_depgraph()
    decls = bd.parse_lean_sources()
    node_map = graph["node_map"]
    bd._CTX.update({"decls": decls, "node_map": node_map, "graph": graph})
    bd._REGISTRY = bd.load_axiom_registry(decls, node_map)
    bd._AUDIT = bd.load_audit()
    return decls, node_map


def resolve_claims(decls: dict, node_map: dict) -> list[dict]:
    claims = [c for s in bd.parse_gapmap() for c in s.get("claims", [])]
    for c in claims:
        ref = c.get("lean_ref") or ""
        if not ref:
            continue
        r = bd.resolve(ref, decls, node_map, c.get("level_key", ""))
        if r is None and "." not in ref:
            matches = [f for f in decls if f.rsplit(".", 1)[-1] == ref]
            if len(matches) == 1:
                r = matches[0]
        c["_full"] = r
    return claims


def bucket_of(full: str) -> str:
    subst, vocab, cl = bd.footprint_parts(full)
    if subst:
        return "up"
    if vocab:
        return "vocab"
    return "cl" if cl else "af"


def derive(claims: list[dict]) -> tuple[dict, dict, list]:
    derived: dict[str, list[str]] = {b: [] for b in BUCKETS}
    substantive: dict[str, list[str]] = {}
    unresolved: list[str] = []
    for c in claims:
        if bd._clean_status((c.get("status") or "").strip()) not in ("PROVEN", "PROVEN↑"):
            continue
        full = c.get("_full")
        if not full:
            unresolved.append(c["id"])
            continue
        b = bucket_of(full)
        derived[b].append(c["id"])
        if b == "up":
            subst, _, _ = bd.footprint_parts(full)
            for a in subst:
                substantive.setdefault(a, []).append(c["id"])
    return derived, substantive, unresolved


def zero_axiom_nonproven(claims: list[dict]) -> list[str]:
    """Rows that are axiom-free but whose ledger status is not a PROVEN step
    (e.g. C175, the `{}` COUNTERMODEL separation) — listed so the prose may
    name them without silently counting them as PROVEN claims."""
    out = []
    for c in claims:
        if bd._clean_status((c.get("status") or "").strip()) in ("PROVEN", "PROVEN↑"):
            continue
        full = c.get("_full")
        if not full:
            continue
        if not bd.audit_footprint(full):
            out.append(f"{c['id']} ({c.get('status')})")
    return out


def stated_counts(text: str) -> dict:
    out = {}
    for b, rx in STATED_RE.items():
        m = rx.search(text)
        out[b] = int(m.group(1)) if m else None
    return out


def stated_axiom_counts(text: str) -> dict:
    """The per-axiom PROVEN↑ tallies written in the GAPMAP PROVEN↑ bullet
    (`AxTwoSubjects` (14): …)."""
    m = STATED_RE["up"].search(text)
    if not m:
        return {}
    tail = text[m.end():]
    end = re.search(r"\n  - \*\*|\n- \*\*", tail)
    region = tail[:end.start()] if end else tail
    return {ax: int(n) for ax, n in re.findall(r"`(\w+)`\s*\((\d+)\)", region)}


def format_list(ids: list[str], width: int = 78) -> str:
    lines, cur = [], ""
    for cid in ids:
        piece = f"{cid},"
        if cur and len(cur) + 1 + len(piece) > width:
            lines.append(cur)
            cur = "  " + piece
        else:
            cur = f"{cur} {piece}".strip()
    if cur:
        lines.append(cur)
    return "\n".join(lines)


def main() -> int:
    check = "--check" in sys.argv[1:]
    decls, node_map = load_context()
    claims = resolve_claims(decls, node_map)
    derived, substantive, unresolved = derive(claims)
    gapmap = bd.GAPMAP_PATH.read_text(encoding="utf-8")

    print("GAPMAP claim taxonomy — derived from formal/axiom_audit.json")
    print("=" * 72)
    drift = False
    counts = stated_counts(gapmap)
    for b in BUCKETS:
        ids = derived[b]
        print(f"\n{BUCKET_LABELS[b]}: {len(ids)}")
        print(format_list(ids))
        if check and counts.get(b) != len(ids):
            print(f"  !! DRIFT count: GAPMAP states {counts.get(b)}, derived {len(ids)}")
            drift = True

    if substantive:
        print("\nSubstantive axioms behind the PROVEN↑ claims")
        print("-" * 72)
        written = stated_axiom_counts(gapmap) if check else {}
        for ax in sorted(substantive):
            ids = sorted(set(substantive[ax]))
            print(f"  {ax} ({len(ids)}): " + ", ".join(ids))
            if check and ax in written and written[ax] != len(ids):
                print(f"  !! DRIFT: GAPMAP states {ax} ({written[ax]}), derived {len(ids)}")
                drift = True

    print("\nLive axiom inventory (kernel axioms actually declared)")
    print("-" * 72)
    lean_ax = {}
    for full, info in decls.items():
        if info.get("kind") == "axiom":
            tag = (info.get("tag") or "UNTAGGED")
            lean_ax.setdefault(tag, []).append(full)
    tagged_total = 0
    for tag in sorted(lean_ax):
        names = sorted(lean_ax[tag])
        print(f"  Tag: {tag} ({len(names)}): " + ", ".join(n.rsplit(".", 1)[-1] for n in names))
        if tag != "UNTAGGED":
            tagged_total += len(names)
    declared_total = sum(len(v) for v in lean_ax.values())
    audit_lean = {a for v in bd._AUDIT.values() for a in v if a.startswith("Logos.")}
    builtins = sorted({a for v in bd._AUDIT.values() for a in v if not a.startswith("Logos.")})
    print(f"  declared axioms: {declared_total} total / {tagged_total} tagged")
    print(f"  distinct Logos axiom names appearing in footprints: {len(audit_lean)}")
    print(f"  Lean built-ins in footprints: {', '.join(builtins)}")

    if unresolved:
        print(f"\nUNRESOLVED PROVEN rows (no kernel declaration): {len(unresolved)}")
        print("  " + ", ".join(unresolved))
        if check:
            drift = True

    nonproven = zero_axiom_nonproven(claims)
    if nonproven:
        print(f"\nAxiom-free rows that are NOT PROVEN steps: {len(nonproven)}")
        print("  " + ", ".join(nonproven))

    if check:
        print("\nRESULT: DRIFT DETECTED" if drift else "\nRESULT: GAPMAP taxonomy matches the kernel")
        return 1 if drift else 0
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
