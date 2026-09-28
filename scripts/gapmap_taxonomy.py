#!/usr/bin/env python3
"""Derive the GAPMAP claim-taxonomy tallies and axiom inventory from the kernel.

`formal/GAPMAP.md` carries four hand-maintained tallies in its "Summary counts"
block — truly axiom-free (`{}`), `CL`-only, vocabulary-only, and the PROVEN↑
claim list — plus a "Net inventory" line, and one hand-maintained set per
claim row (the `Pegada` cell). This script recomputes all of them from
`formal/axiom_audit.json` (the authoritative `#print axioms` ledger) through
`build_deduction`'s own GAPMAP parser, claim resolver and footprint splitter, so
the numbers and the per-row cells can be derived instead of transcribed.

Usage:
  python3 scripts/gapmap_taxonomy.py           # print the derived report
  python3 scripts/gapmap_taxonomy.py --check   # exit 1 if the counts, the
                                                # per-row `Pegada` footprint
                                                # cell, or the per-row *status*
                                                # cell written in GAPMAP.md has
                                                # drifted from the kernel
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


# Closed-logic spellings: the Pegada cells write `CL` or `propext` for the
# kernel's classical meta-logic axioms; all normalise to one class token.
CL_CELL_TOKENS = {"CL", "propext", "Classical.choice", "Quot.sound"}


def parse_claimed_footprint(cell: str) -> set | None:
    """The `{a, b, CL}` set a GAPMAP `Pegada` cell states, or None when the
    cell carries no stated set (empty, a bare `CL` class label, a retired /
    demoted / killed note). Leading `**` bold markers and trailing prose are
    ignored; `propext` is normalised to `CL`."""
    m = re.match(r"\**\{([^{}]*)\}", (cell or "").strip())
    if not m:
        return None
    out = set()
    for tok in m.group(1).split(","):
        tok = tok.strip().rsplit(".", 1)[-1]
        if tok:
            out.add("CL" if tok in CL_CELL_TOKENS else tok)
    return out


def derived_footprint_set(full: str) -> set:
    subst, vocab, cl = bd.footprint_parts(full)
    return set(subst) | set(vocab) | ({"CL"} if cl else set())


def check_status_cells(claims: list[dict]) -> list[str]:
    """Every GAPMAP row's *status* cell against the derived footprint bucket.

    This is the check the 2026-09-28 C455/C456 correction showed was missing.
    Both rows read `PROVEN` in the status cell while the kernel footprint
    carried the `Tag: TRANS` axiom `performative_act_datum`, so their derived
    bucket was `up`; the badge the reader sees is derived from the *bucket*
    (`compute_epistemic_badge`), not from the transcribed cell, so the ledger
    understated two axiomatic rows as proved. `check_footprint_cells` could not
    catch it: the `Pegada` cells were already correct, it was the status word
    that had drifted.

    The invariant is symmetric, and both directions are checked:

    - bucket `up` (a substantive `SEM`/`META`/`TRANS` axiom in the audited
      footprint) requires the status cell to read `PROVEN↑`, never plain
      `PROVEN`; and
    - a cell may not read `PROVEN↑` when the kernel says otherwise, which would
      overstate a vocabulary-only or axiom-free row as axiomatic.
    """
    bad = []
    for c in claims:
        status = bd._clean_status((c.get("status") or "").strip())
        if status not in ("PROVEN", "PROVEN↑"):
            continue
        full = c.get("_full")
        if not full:
            continue
        b = bucket_of(full)
        if b == "up" and status == "PROVEN":
            subst, _, _ = bd.footprint_parts(full)
            bad.append(
                f"{c['id']}: cell=PROVEN but kernel bucket=up "
                f"(substantive {{', '.join(subst)}}) - understated as proved"
            )
        elif b != "up" and status == "PROVEN↑":
            bad.append(
                f"{c['id']}: cell=PROVEN↑ but kernel bucket={b} "
                f"- overstated as axiomatic"
            )
    return bad


def check_footprint_cells(claims: list[dict], decls: dict, node_map: dict) -> list[str]:
    """Every GAPMAP row that states a `Pegada` set, compared against the
    audited kernel footprint. Axiom rows document the cone with or without
    the axiom itself (both spellings occur in the ledger); bare `CL` cells
    are checked as the CL-only class claim they are. Rows whose cell states
    one set per declaration (`A` / `B`, e.g. C232) are checked pairwise."""
    bad = []

    def one(ref_full: str | None, part: str, decl_kind: str | None) -> str | None:
        claimed = parse_claimed_footprint(part)
        if claimed is None or ref_full is None:
            return None
        real = derived_footprint_set(ref_full)
        base = ref_full.rsplit(".", 1)[-1]
        if claimed == real or (decl_kind == "axiom" and claimed == real - {base}):
            return None
        missing = sorted(real - claimed - {base})
        extra = sorted(claimed - real)
        return (
            f"cell={{{', '.join(sorted(claimed))}}} "
            f"kernel={{{', '.join(sorted(real))}}}"
            + (f" MISSING={missing}" if missing else "")
            + (f" EXTRA={extra}" if extra else "")
        )

    for c in claims:
        cell = c.get("footprint") or ""
        parts = [p.strip() for p in cell.split("/")]
        set_parts = [p for p in parts if re.match(r"\**\{", p)]
        if len(set_parts) > 1:
            refs = [
                m.group(0)
                for span in re.findall(r"`([^`]*)`", c.get("lean_cell") or "")
                for m in [re.search(r"[A-Za-z_][A-Za-z0-9_.]*", span)]
                if m and not m.group(0).startswith("Logos")
            ]
            if len(refs) == len(set_parts):
                for ref, part in zip(refs, set_parts):
                    full = bd.resolve(ref, decls, node_map, c.get("level_key", ""))
                    kind = (decls.get(full) or {}).get("kind") if full else None
                    msg = one(full, part, kind)
                    if msg:
                        bad.append(f"{c['id']} ({ref}): " + msg)
                continue
        full = c.get("_full")
        if not set_parts:
            if (cell.strip() == "CL") and full and bucket_of(full) != "cl":
                bad.append(f"{c['id']}: cell=CL kernel={bucket_of(full)}")
            continue
        kind = (decls.get(full) or {}).get("kind") if full else None
        msg = one(full, set_parts[0], kind)
        if msg:
            bad.append(f"{c['id']} ({(full or '?').rsplit('.', 1)[-1]}): " + msg)
    return bad


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

    status_drift = check_status_cells(claims)
    if status_drift:
        print(f"\nStatus cells disagreeing with the kernel bucket: {len(status_drift)}")
        for line in status_drift:
            print("  !! " + line)
        if check:
            drift = True
    elif check:
        print("\nStatus cells: every PROVEN/PROVEN↑ cell matches its kernel bucket")

    cell_drift = check_footprint_cells(claims, decls, node_map)
    if cell_drift:
        print(f"\nPegada cells disagreeing with the kernel: {len(cell_drift)}")
        for line in cell_drift:
            print("  !! " + line)
        if check:
            drift = True
    elif check:
        print("\nPegada cells: all stated sets match the kernel")

    if check:
        print("\nRESULT: DRIFT DETECTED" if drift else "\nRESULT: GAPMAP taxonomy matches the kernel")
        return 1 if drift else 0
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
