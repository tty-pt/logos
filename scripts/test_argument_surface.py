#!/usr/bin/env python3
"""test_argument_surface.py — the READINGPATH.md two-tier contract, machine-checked.

README.md is the argument (fully visible, no collapsed blocks, FACT early);
investigations/ledger.md is the audit (chains, tables, derivations, full prose);
their union loses nothing from the pre-split README (see ledger_superset.py).

Fails the build on any regression of the split.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
README = ROOT / "README.md"
LEDGER = ROOT / "investigations" / "ledger.md"


def main() -> int:
    errors: list[str] = []
    readme = README.read_text(encoding="utf-8")
    ledger = LEDGER.read_text(encoding="utf-8")

    def check(cond: bool, msg: str) -> None:
        print(f"  {'✓' if cond else '✗'} {msg}")
        if not cond:
            errors.append(msg)

    # --- the argument surface ---
    check("<details>" not in readme and "</details>" not in readme,
          "README has zero collapsed <details> blocks")
    check("step by step" not in readme,
          "no chain blocks on the reading path")
    check("│" not in readme and "┌" not in readme,
          "no ASCII box-drawing on the reading path")
    visible = [l for l in readme.splitlines()
               if not l.strip().startswith("<")]
    check(len(visible) <= 700, f"README visible lines {len(visible)} <= 700")
    check(readme.startswith("# Γ — The Deduction\n"),
          "README opens with the title")
    fact_at = readme.find("for which meaning can mean")
    check(fact_at != -1 and readme[:fact_at].count("\n") + 1 <= 60,
          "thesis sentence (C553 FACT) lands by line 60")
    # The reading path is the epistemic route (2026-09-30): the ten steps, the
    # price table, the One-God-in-three-Persons rows, the cremation, the
    # instrument limits, what is not established, the attribute profile, and the
    # ledger's index. The deontic route moved to investigations/ledger.md.
    for sec in ["## 1. Satisfaction Is Free",
                "## 9. The Fact",
                "## 11. Necessity, and Exactly What It Costs",
                "## 12. One God, in Three Persons",
                "## 13. The Cremation",
                "## 14. What the Instrument Cannot See",
                "## 15. What Is Not Established",
                "## What Is Established of the Ground, and of the Person",
                "## Where the Rest of the Ledger Lives"]:
        check(sec in readme, f"README carries {sec[:44]}")
    check("## 1. Objective Right and Wrong" not in readme, (
        "the deontic route must not be re-emitted on the reading path"))
    for led_sec in ["## The Deontic Route, in Full (the previous reading spine)",
                    "### 1. Objective Right and Wrong",
                    "### 10. Constructive Personal Ground",
                    "### The Deontic Route in One Map (the previous reading spine)",
                    "## Why Common Skeptical Attacks Fail (The Seven Pillars of Formal Defense)"]:
        check(led_sec in ledger, f"ledger carries {led_sec[:44]}")
    # The pillar count is derived from the rows, so the heading and the table can
    # never disagree again (they did: seven rows under a "Six" title).
    _pil = ledger.partition("Pillars of Formal Defense")[2].split("## ")[0]
    _n = len(re.findall(r"^\| \*\*\d+\. ", _pil, re.M))
    check(f"(The {['One','Two','Three','Four','Five','Six','Seven','Eight','Nine','Ten'][_n-1]} Pillars"
          in ledger, f"the pillar heading counts its own {_n} rows")
    # The thesis and the anti-tritheism line are the two sentences a reader must
    # not be able to miss.
    check("not three gods" in readme.lower(), "README must foreclose tritheism explicitly")
    check("one God in three Persons" in readme or "One God, in Three Persons" in readme,
          "README must state one God in three Persons")
    ten = re.findall(r"^\| \*\*(\d+)\*\*", readme.split("## The Argument in Ten Steps")[1].split("## 1.")[0], re.M)
    check(sorted(int(t) for t in ten) == list(range(1, 11)),
          "ten-step table covers steps 1-10")

    # --- the ledger surface ---
    check(LEDGER.exists() and len(ledger.splitlines()) > 2000,
          f"ledger exists ({len(ledger.splitlines())} lines)")
    check(len(re.findall(r"^### .*?(?:chain, step by step|Chain \d+)", ledger, re.M)) == 14,
          "ledger carries all 14 chain blocks")
    # 40 -> >= 40 on 2026-09-30: the deontic route moved to the ledger rendered in
    # full (branches, supporting infrastructure, obstructions and per-step glosses),
    # so the ledger now carries strictly more derivations than the pre-split README.
    n_deriv = len(re.findall(r"^<summary>Formal Derivation", ledger, re.M))
    check(n_deriv >= 40, f"ledger carries all 40 natural-deduction blocks (got {n_deriv})")
    check("## Formal Frontiers" in ledger, "ledger carries the frontier list")
    check("## Which Classical Attributes Are Already Established?" in ledger,
          "ledger carries the full attributes table")
    check("## The Whole Argument in One Map" in ledger,
          "ledger carries the ASCII flowchart")

    # --- the union loses nothing (fast structural form; the full item-level
    #     form is scripts/ledger_superset.py against the snapshot) ---
    for name in ["the_person_supports_the_reality_of_right",
                 "indubitable_normative_free_will",
                 "epistemic_right_wrong_requires_a_free_being_for_which_meaning_can_mean",
                 "necessaryPersonalSubjectExists",
                 "ofGround_necessary_ground_of_reality"]:
        check(name in readme or name in ledger, f"union keeps {name[:50]}")

    # --- 13. The Cremation: every dead branch is a DERIVATION, not a badge
    # (2026-09-30, CREMATION.md). A row that only says "PROVEN" asserts what the
    # reader cannot check; a row that prints the premises, the steps and the
    # terminator lets the reader check it. Both are required.
    cre = readme.partition("## 13. The Cremation")[2].partition("## 14.")[0]
    check(cre, "README carries the cremation section")
    _rows = [ln for ln in cre.splitlines() if ln.startswith("| **")]
    check(len(_rows) == 3,
          f"only the three boundary rows stay tabular ({len(_rows)} rows in §13)")
    for _dead in ("No right or wrong at all", "Voluntarism (Euthyphro)",
                  "Descriptivism (D3)", "Ungraspable command (D6)"):
        check(not any(_dead in ln for ln in _rows),
              f"the dead branch '{_dead}' is a derivation, not a table row")
    blocks = re.findall(r"^\*\*(?:\d+\. )?(.+?)\*\* — ", cre, re.M)
    check(len(blocks) >= 12, f"the cremation shows every branch ({len(blocks)} found)")
    for term in ("⊥ CONTRADICTION", "⊘ DENIAL REFUTED", "COLLAPSE — INCOHERENT"):
        check(term in cre, f"the cremation derives a '{term}'")
    for d in ("Descriptivism (D3)", "Impersonal normativity (D4)",
              "Monolithic command (D5)", "Ungraspable command (D6)"):
        check(d in cre, f"the cremation covers {d}")
    # Each block: a Lean anchor, a price line, and a terminator. The price line
    # must never pair a ✅ with a substantive axiom (the V2 invariant, in prose).
    for blk in re.split(r"^\*\*(?:\d+\. )?.+?\*\* — ", cre, flags=re.M)[1:]:
        head = blk.split("\n", 1)[0]
        check("lean#L" in blk.split("\n## ")[0],
              f"block '{head[:40]}' links its Lean declaration")
        check("substantive axio" in blk, f"block '{head[:40]}' states its price")
    for line in cre.splitlines():
        if line.startswith("> ✅"):
            check("— 0 substantive axioms ·" in line,
                  "a ✅ price line must claim zero substantive axioms: " + line[:70])
    # A priced route is shown priced: the stipulative branch's second derivation
    # rests on AxJudicativeBipolarity and must say so, not borrow a ✅.
    check("⚠️ **AXIOMATIC (AxJudicativeBipolarity)**" in cre,
          "the priced second route to the stipulative death is disclosed as priced")
    check("A second, independently sufficient refutation" in cre,
          "the priced route explains why the free route is the one read")

    if errors:
        print(f"\nFAIL: {len(errors)} argument-surface regression(s)")
        return 1
    print("\nOK: two-tier contract holds (argument ~490 lines, ledger complete).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
