#!/usr/bin/env python3
"""Census of the pre-declaration occurrences of the F15 bound.

`SemanticFinitude` is `∀ s : Subject, ∃ p : Prop, ¬ Means s p` — "no subject means
every proposition". Before it was declared (2026-09-28) the corpus paid it as an
anonymous explicit premise in five attribute modules. This script counts those
occurrences so the number quoted in the prose corpus, in `GAPMAP.md` and in the
axiom's own justification docstring is *checkable* rather than asserted.

Two measures, because "how many times" has no single answer here:

  any      every top-level declaration whose STATEMENT mentions the bound in any
           form — the ∀-form (F15 itself, as a hypothesis) or the per-subject
           ∃-form (`hDisc : ∃ p, ¬ Means s p`).
  forall   only the declarations carrying the exact F15 ∀-form, i.e. the ones
           that pay the price Γ actually declares.

A statement is the declaration head up to the first `:=`, `by` or `where`, so
occurrences in proof bodies are excluded (they are usages of an already-paid
price, not new prices). Bodies are still counted separately in `--bodies` mode.

Both measures are printed with their per-file breakdown. Nothing here is
transcribed: re-run after any edit to the five modules.

Usage:
    python3 scripts/census_semantic_finitude.py            # table + totals
    python3 scripts/census_semantic_finitude.py --bodies   # include proof bodies
    python3 scripts/census_semantic_finitude.py --check     # exit 1 on drift
                                                              # from EXPECTED
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN = ROOT / "formal" / "Logos"

# The five modules that pay the F15 price. `SemanticFinitude` itself is excluded:
# it is the declaration, not a payment of it.
FILES = [
    "DivinePureActuality",
    "FoundationalUnicity",
    "CanonicalAseity",
    "DivineSimplicity",
    "AsieticChoice",
]

DECL_HEAD = re.compile(
    r"^(theorem|lemma|def|structure|inductive|axiom|abbrev|instance)\b"
)
# `Means` is reached both bare and as `Logos.Agency.Means`.
MEANS = r"(?:Logos\.\s*Agency\.\s*)?Means"
# The per-subject content: `∃ p, ¬ Means s p` (the `: Prop` is optional — it is
# present in some files and elided in others).
EXISTS_FORM = r"∃\s*p\s*(?::\s*Prop\s*)?,\s*¬\s*" + MEANS + r"\s+\w+\s+\w+"
RE_ANY = re.compile(EXISTS_FORM)
RE_FORALL = re.compile(r"∀\s*s\s*:\s*Subject.{0,40}?" + EXISTS_FORM)

# The number the prose corpus and the axiom docstring quote. `--check` fails if
# the kernel stops agreeing, so a refactor that moves the bound cannot silently
# leave a stale "paid N times" in the justification.
EXPECTED = {"any": 19, "forall": 14,
            "any_by_file": {"DivinePureActuality": 5, "FoundationalUnicity": 6,
                            "CanonicalAseity": 4, "DivineSimplicity": 3,
                            "AsieticChoice": 1},
            "forall_by_file": {"DivinePureActuality": 3, "FoundationalUnicity": 5,
                               "CanonicalAseity": 2, "DivineSimplicity": 3,
                               "AsieticChoice": 1}}


def declarations(path: Path, bodies: bool):
    """Yield (name, text) for each top-level declaration in `path`.

    With `bodies=False` the text is the declaration head only — the statement
    before the first `:=` / `by` / `where`. With `bodies=True` the whole
    declaration is returned, so occurrences in proofs are counted too.
    """
    lines = path.read_text().splitlines()
    starts = [(i, l) for i, l in enumerate(lines) if DECL_HEAD.match(l)]
    for k, (i, line) in enumerate(starts):
        end = starts[k + 1][0] if k + 1 < len(starts) else len(lines)
        block = "\n".join(lines[i:end])
        if not bodies:
            m = re.search(r":=|\bby\b|\bwhere\b", block)
            block = block[: m.start()] if m else block
        parts = line.split()
        if len(parts) < 2:
            continue
        yield parts[1], re.sub(r"\s+", " ", block)


def census(bodies: bool = False) -> dict:
    out = {"any_by_file": {}, "forall_by_file": {}, "hits": {}}
    for f in FILES:
        path = LEAN / f"{f}.lean"
        if not path.exists():
            sys.exit(f"missing module: {path}")
        any_n = fa_n = 0
        for name, text in declarations(path, bodies):
            if not RE_ANY.search(text):
                continue
            any_n += 1
            if RE_FORALL.search(text):
                fa_n += 1
                out["hits"].setdefault(f, []).append(name)
        out["any_by_file"][f] = any_n
        out["forall_by_file"][f] = fa_n
    out["any"] = sum(out["any_by_file"].values())
    out["forall"] = sum(out["forall_by_file"].values())
    return out


def main() -> int:
    bodies = "--bodies" in sys.argv
    check = "--check" in sys.argv
    data = census(bodies=bodies)

    scope = "declaration heads + proof bodies" if bodies else "declaration heads (statements only)"
    print(f"F15 bound census over {len(FILES)} modules — {scope}")
    print("=" * 78)
    print(f"{'file':24s} {'any':>6s} {'forall':>8s}")
    for f in FILES:
        print(f"{f:24s} {data['any_by_file'][f]:6d} {data['forall_by_file'][f]:8d}")
    print("-" * 78)
    print(f"{'TOTAL':24s} {data['any']:6d} {data['forall']:8d}")
    print()
    print("`any`   = every declaration whose statement mentions the bound, in the")
    print("         ∀-form (F15 itself) or the per-subject ∃-form (`hDisc`).")
    print("`forall`= only the declarations carrying the exact F15 ∀-form, i.e. the")
    print("         ones that pay the price Γ declares.")
    print()
    print("Declarations carrying the ∀-form:")
    for f, names in data["hits"].items():
        for n in names:
            print(f"  {f}.{n}")
    print()
    print(f"Both measures cover all {len(FILES)} attribute modules, so the robust")
    print(f"statement is: Γ pays this price by {len(FILES)} distinct attribute")
    print("arguments, under either measure.")

    if not check:
        return 0
    drift = []
    for k in ("any", "forall", "any_by_file", "forall_by_file"):
        if data[k] != EXPECTED[k]:
            drift.append(f"  {k}: kernel {data[k]!r}, quoted {EXPECTED[k]!r}")
    if drift:
        print()
        print("✗ DRIFT — the quoted census no longer matches the kernel:")
        print("\n".join(drift))
        print("  Either update the prose/docstring with the new figures, or record")
        print("  why the move does not change the price Γ pays.")
        return 1
    print()
    print("✓ census matches the figures quoted in the prose corpus")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
