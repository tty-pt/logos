#!/usr/bin/env python3
"""Gate the bare-rejected-horn DIALECTIC, so no surface can call it open again.

`scripts/test_finitude_bound_scope.py` pins one instance of a recurring failure mode: prose
describing an intended re-scope as though the kernel had adopted it. This is a second instance,
and worse, because it ran the other way -- the ledger called a step `BLOCKED` for three days while
the kernel had been deriving it all along.

`ISSUE_K_PLAN.md` Step 2(ii) records the step: withdraw the BLOCKED/refuted reading of the bare
rejected horn and ledger the positive result. The underlying facts, all machine-derived:

  - Γ DOES derive the bare horn. `Agency.performative_act_datum` is unconditional
    (`exists s p, Act s p`) and `Choice.AxActPolarity` turns an act into its own polarity
    (`Act s p -> Means s (~ p)`), so `bareRejectedHornCoMeant_is_derivable` (C565) closes F11 at
    `{performative_act_datum, AxActPolarity}` -- one TRANS, one SEM.
  - The bare horn is ALSO unsatisfiable in every single-content model (C273/C274), because
    one-content-per-subject turns `means t p & means t (~ p)` into `p = ~ p`.
  - And Γ's own `Means` is provably NOT single-valued (`gammaMeans_is_not_single_valued`, C566).

The three are one result, not three: **there is no reading of "meaning" on which Γ both keeps
meaning single-valued and has genuine co-meaning.** Single-valuedness buys the refutation and costs
the choice; many-valuedness buys the choice and costs the refutation. A surface that reports only
one horn of this is wrong, which is what every surface did until 2026-10-03.

So the load-bearing assertion here is not about any single theorem -- it is that the *pair*
(derivation in Γ, refutation under single-valuedness) is present AND that no reader-facing ledger
still calls the step open. That last part is what would have caught the original defect.

Run: python3 scripts/test_horn_dialectic.py
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
AUDIT = ROOT / "formal" / "axiom_audit.json"
GAPMAP = ROOT / "formal" / "GAPMAP.md"

# The Γ-side derivation, and the two axioms it must pay for. Asserted by name so a rename cannot
# quietly strand the prose that explains the price.
DERIVED = "Logos.AsieticChoice.bareRejectedHornCoMeant_is_derivable"
DERIVED_PAID_BY = ("performative_act_datum", "AxActPolarity")

# Γ's meaning relation is provably not single-valued -- the half that reconciles the other two.
NOT_SINGLE_VALUED = "Logos.AsieticChoice.gammaMeans_is_not_single_valued"

# The countermodel side. These must stay free of the polarity axioms: they quantify over an
# ABSTRACT signature (`SingleContentSignature`), not over Γ. If they ever acquire `AxActPolarity`
# they have stopped being a statement about single-valued meaning and the dialectic collapses.
REFUTED = (
    "Logos.AsieticChoice.singleContentModelRefutesBareRejectedHorn",
    "Logos.AsieticChoice.bareRejectedHornCoMeant_is_not_derivable",
)
POLARITY_AXIOMS = ("AxActPolarity", "performative_act_datum")

# The frontier row F11 and the two C-rows the step registered.
F11_ROW = re.compile(r"^\| F11 \|.*$", re.M)
C565_ROW = re.compile(r"^\| C565 \|.*$", re.M)
C566_ROW = re.compile(r"^\| C566 \|.*$", re.M)

# Statuses that would re-assert the old, false verdict. `BLOCKED` is the one that shipped.
OPEN_STATUSES = ("BLOCKED", "DEFERRED")


def short(footprint):
    return {a.split(".")[-1] for a in footprint}


def main() -> int:
    if not AUDIT.exists():
        print(f"FAIL: {AUDIT} missing -- run scripts/audit_footprints.py")
        return 1
    audit = json.loads(AUDIT.read_text())

    for decl in (DERIVED, NOT_SINGLE_VALUED, *REFUTED):
        if decl not in audit:
            print(f"FAIL: dialectic declaration absent from the audit: {decl}")
            print("       Either the step was reverted, or `lake exe depviz` was not re-run --")
            print("       `scripts/audit_footprints.py` reads its declaration list from depgraph.json.")
            return 1

    # 1. The derivation must actually pay for what the prose says it pays for.
    paid = short(audit[DERIVED])
    missing = [a for a in DERIVED_PAID_BY if a not in paid]
    if missing:
        print(f"FAIL: {DERIVED} does not rest on {missing}.")
        print("       §18 and GAPMAP C565 state the price as `{performative_act_datum, AxActPolarity}`.")
        print("       Either the price changed (re-price the prose) or the derivation was replaced.")
        return 1

    # 2. Both halves must agree on the datum, or they are not one dialectic.
    for decl in (NOT_SINGLE_VALUED,):
        missing = [a for a in DERIVED_PAID_BY if a not in short(audit[decl])]
        if missing:
            print(f"FAIL: {decl} does not rest on {missing}; it cannot be the other horn of the")
            print("       same dialectic. Re-examine how the two sides are related before editing prose.")
            return 1

    # 3. The countermodel must stay a statement about ABSTRACT single-valued meaning.
    for decl in REFUTED:
        leaked = sorted(set(POLARITY_AXIOMS) & short(audit[decl]))
        if leaked:
            print(f"FAIL: {decl} now rests on {leaked}.")
            print("       C273/C274 quantify over `SingleContentSignature`, an abstract structure, so they")
            print("       cannot depend on Γ's polarity axioms. If they do, they are no longer the")
            print("       single-valued refutation and the dialectic's two horns have merged.")
            return 1

    if not GAPMAP.exists():
        print(f"FAIL: {GAPMAP} missing")
        return 1
    gapmap = GAPMAP.read_text()

    for name, rx in (("C565", C565_ROW), ("C566", C566_ROW), ("F11", F11_ROW)):
        if not rx.search(gapmap):
            print(f"FAIL: GAPMAP has no `{name}` row.")
            print("       The step registered a derivation and a reconciliation; both need a citable row,")
            print("       and a status the generator can derive a badge from.")
            return 1

    # 4. The assertion that would have caught the original defect: no ledger may still call the
    #    step open while the kernel derives it.
    f11 = F11_ROW.search(gapmap).group(0)
    cells = f11.split(" | ")
    status = cells[2].strip() if len(cells) > 2 else ""
    if status in OPEN_STATUSES:
        print(f"FAIL: GAPMAP F11 is `{status}` while {DERIVED} derives it.")
        print("       This is the exact defect of 2026-10-03, which sat for three days: a frontier row")
        print("       advertising a step as open that the kernel had closed. Either the derivation is")
        print("       wrong, or the row is stale. Do not resolve it by editing the status alone --")
        print("       `--print axioms` on the derivation first, and re-read the price you are publishing.")
        return 1

    print("OK: the bare rejected horn is DERIVED in Γ and REFUTED under single-valued meaning.")
    print(f"    {DERIVED}: pays {sorted(DERIVED_PAID_BY)} -- F11 is discharged, not open.")
    print(f"    {NOT_SINGLE_VALUED}: Γ's `Means` is provably not single-valued.")
    print("    C273/C274: stay free of the polarity axioms, so they remain a statement about")
    print("              ABSTRACT single-valued meaning rather than about Γ.")
    print(f"    GAPMAP F11 status: {status!r} -- consistent with the kernel.")
    print("    => No reading of \"meaning\" keeps single-valuedness and genuine co-meaning together.")
    return 0


if __name__ == "__main__":
    sys.exit(main())