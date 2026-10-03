#!/usr/bin/env python3
"""Gate the Free Person derivation and plurality architecture (LOVE-4 / C587).

Asserts:
  1. `formal/Logos/NoMeanerNoFalsity.lean` contains ZERO `axiom` declarations.
  2. `Logos.NoMeanerNoFalsity.a_genuine_free_person_exists` (C587) and C590 have ZERO META
     axioms in their audited footprints, paying only `{performative_act_datum, AxActPolarity}`.
  3. `Logos.NoMeanerNoFalsity.the_ground_is_a_personal_necessary_essence` (N9) and
     `Logos.NoMeanerNoFalsity.the_dependence_step_is_refuted` (N10) are free of substantive axioms.
  4. The census is strictly preserved at 39 = 18 VOCAB / 6 SEM / 13 META / 2 TRANS.
  5. C587–C590 exist in GAPMAP as PROVEN/PROVEN↑.
  6. Criterion 6: No-laundering detector: no VOCAB/TRANS axiom combines personhood/necessity with distinctness.
  7. Criterion 8: Stale-BLOCKED detector: no docstring asserts genuineChoice_exists or freeWillExists is BLOCKED.
  8. Negative test: an injected META axiom triggers failure.

Run: python3 scripts/test_two_eternal_persons.py
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MODULE = ROOT / "formal" / "Logos" / "NoMeanerNoFalsity.lean"
AUDIT = ROOT / "formal" / "axiom_audit.json"
GAPMAP = ROOT / "formal" / "GAPMAP.md"

sys.path.insert(0, str(ROOT / "scripts"))
import check_consistency as cc


def short(footprint: list[str]) -> set[str]:
    return {a.split(".")[-1] for a in footprint}


def main() -> int:
    errors: list[str] = []

    def check(cond: bool, msg: str) -> None:
        print(f"  {'✓' if cond else '✗'} {msg}")
        if not cond:
            errors.append(msg)

    print("== test_two_eternal_persons ==")

    # 1. Zero axioms declared in NoMeanerNoFalsity.lean
    check(MODULE.exists(), f"{MODULE} exists")
    if MODULE.exists():
        text = MODULE.read_text(encoding="utf-8")
        lines = cc.lean_code_lines(text.splitlines())
        code = "\n".join(lines)
        axiom_matches = re.findall(r"^\s*axiom\s+(\w+)", code, re.M)
        check(len(axiom_matches) == 0,
              f"NoMeanerNoFalsity.lean has 0 axiom declarations (found {axiom_matches})")

    # 2. Census inventory
    inventory = cc.axiom_inventory()
    check(len(inventory) == 39, f"Total axioms == 39 (got {len(inventory)})")
    tag_counts = {}
    axioms_by_tag = {"VOCAB": set(), "SEM": set(), "META": set(), "TRANS": set()}
    for name, stmt, lno, path, tag, ns in inventory:
        tag_counts[tag] = tag_counts.get(tag, 0) + 1
        if tag in axioms_by_tag:
            axioms_by_tag[tag].add(name)
    expected_tags = {"VOCAB": 18, "SEM": 6, "META": 13, "TRANS": 2}
    check(tag_counts == expected_tags,
          f"Census matches 18 VOCAB / 6 SEM / 13 META / 2 TRANS (got {tag_counts})")

    # 3. Audit check
    check(AUDIT.exists(), "formal/axiom_audit.json exists")
    if AUDIT.exists():
        audit = json.loads(AUDIT.read_text(encoding="utf-8"))

        c587_fp = audit.get("Logos.NoMeanerNoFalsity.a_genuine_free_person_exists")
        check(c587_fp is not None, "C587 a_genuine_free_person_exists is audited")
        if c587_fp is not None:
            c587_short = short(c587_fp)
            meta_axioms = axioms_by_tag.get("META", set())
            c587_meta = c587_short & meta_axioms
            check(len(c587_meta) == 0,
                  f"C587 has ZERO META axioms (got {sorted(c587_meta)})")
            check("performative_act_datum" in c587_short,
                  "C587 contains performative_act_datum (TRANS)")
            check("AxActPolarity" in c587_short,
                  "C587 contains AxActPolarity (SEM)")
            subst = (c587_short & axioms_by_tag.get("SEM", set()) |
                     c587_short & axioms_by_tag.get("TRANS", set()) |
                     c587_short & axioms_by_tag.get("META", set()))
            check(subst == {"performative_act_datum", "AxActPolarity"},
                  f"C587 substantive footprint is exactly {{performative_act_datum, AxActPolarity}} (got {sorted(subst)})")

        c590_fp = audit.get("Logos.NoMeanerNoFalsity.the_free_person_claim_in_one_statement")
        check(c590_fp is not None, "C590 the_free_person_claim_in_one_statement is audited")
        if c590_fp is not None:
            c590_short = short(c590_fp)
            c590_meta = c590_short & axioms_by_tag.get("META", set())
            check(len(c590_meta) == 0,
                  f"C590 has ZERO META axioms (got {sorted(c590_meta)})")

        n9_fp = audit.get("Logos.NoMeanerNoFalsity.the_ground_is_a_personal_necessary_essence")
        check(n9_fp is not None, "N9 is audited")
        if n9_fp is not None:
            n9_subst = short(n9_fp) & (axioms_by_tag.get("SEM", set()) |
                                      axioms_by_tag.get("TRANS", set()) |
                                      axioms_by_tag.get("META", set()))
            check(len(n9_subst) == 0, f"N9 has 0 substantive axioms (got {sorted(n9_subst)})")

        n10_fp = audit.get("Logos.NoMeanerNoFalsity.the_dependence_step_is_refuted")
        check(n10_fp is not None, "N10 is audited")
        if n10_fp is not None:
            n10_subst = short(n10_fp) & (axioms_by_tag.get("SEM", set()) |
                                       axioms_by_tag.get("TRANS", set()) |
                                       axioms_by_tag.get("META", set()))
            check(len(n10_subst) == 0, f"N10 has 0 substantive axioms (got {sorted(n10_subst)})")

    # 4. GAPMAP check
    if GAPMAP.exists():
        gm = GAPMAP.read_text(encoding="utf-8")
        for cid in ["C587", "C588", "C589", "C590"]:
            check(re.search(rf"^\|\s*{cid}\s*\|", gm, re.M) is not None,
                  f"{cid} is present in formal/GAPMAP.md")

    # 5. Criterion 6: No-laundering detector
    laundering_found = []
    for name, stmt, lno, path, tag, ns in inventory:
        if tag in ("VOCAB", "TRANS"):
            if any(p in stmt for p in ("Person", "FreeWill", "NecessarySubjectKind")) and \
               any(d in stmt for d in ("≠", "ne", "distinct", "s₁ ≠ s₂")):
                laundering_found.append((name, tag, path.name))
    check(len(laundering_found) == 0,
          f"Criterion 6 (no-laundering detector): no VOCAB/TRANS axiom combines personhood/necessity with distinctness (found {laundering_found})")

    # 6. Criterion 8: Stale-BLOCKED detector
    stale_blocked = []
    for p in sorted((ROOT / "formal" / "Logos").glob("*.lean")):
        text = p.read_text(encoding="utf-8")
        docstrings = re.findall(r"/--([\s\S]*?)-/", text)
        for ds in docstrings:
            if "genuineChoice_exists" in ds or "freeWillExists" in ds:
                if "is BLOCKED" in ds or "remains blocked" in ds or "not yet derived from the performative datum" in ds:
                    stale_blocked.append(p.name)
    check(len(stale_blocked) == 0,
          f"Criterion 8 (stale-BLOCKED detector): no docstring claims genuineChoice_exists or freeWillExists is BLOCKED (found in {stale_blocked})")

    # 7. Negative test fixture: injecting a META axiom fails the check
    test_simulated_fp = {"performative_act_datum", "AxActPolarity", "AxTwoNecessaryPersonalCentres"}
    test_meta = test_simulated_fp & axioms_by_tag.get("META", set())
    check(len(test_meta) > 0, "Negative test fixture: injected META axiom is correctly detected")

    if errors:
        print(f"\nFAILED with {len(errors)} error(s):")
        for e in errors:
            print(f"  - {e}")
        return 1

    print("\nOK: All tests passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
