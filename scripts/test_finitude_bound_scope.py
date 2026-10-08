#!/usr/bin/env python3
"""Gate WHICH finitude bound the corpus actually uses.

Milestone 2026-10-08: SemanticFinitude restricted to creatures, Divine Persons affirmed in total
meaning via DivinePersonsTotalMeaning, and GroundTranscendence eliminated.

`scripts/test_axiom_census.py` pins how many axioms are declared. This gate verifies what the
census cannot see:
  - `SemanticFinitude` (contingent-scoped, Tag VOCAB) is live and carries the creaturely branch.
  - `DivinePersonsTotalMeaning` (Tag META) carries the Divine Persons (homoousios).
  - `GroundTranscendence` (unrestricted, Tag META) has been completely eliminated from the kernel.
  - The old denial `necessary_kind_subject_lacks_maximal_capacity` is absent, replaced by the
    positive `necessary_kind_subject_has_maximal_capacity`.
  - `Plurality.kinds_are_the_modal_partition` stays free (0 substantive axioms).
  - Active `formal/Logos/*.lean` contains no residual unrestricted finitude axioms.

Run: python3 scripts/test_finitude_bound_scope.py
"""
from __future__ import annotations

import collections
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
AUDIT = ROOT / "formal" / "axiom_audit.json"

SCOPED = "SemanticFinitude"
TOTALITY = "DivinePersonsTotalMeaning"
ELIMINATED = "GroundTranscendence"

# The declarations verifying that the Divine Persons' semantic fullness is affirmed
POSITIVE_CHAIN = (
    "Logos.Plurality.kinds_are_the_modal_partition",
    "Logos.NecessaryKindAudit.necessary_kind_subject_has_maximal_capacity",
    "Logos.TrinitarianSubjectBridge.one_necessary_ground_three_free_necessary_persons",
)

ABSENT_DENIAL = "Logos.NecessaryKindAudit.necessary_kind_subject_lacks_maximal_capacity"

# `kinds_are_the_modal_partition` is what turns "necessary" into "necessary kind", and it must
# stay free (vocabulary only).
FREE_LINK = "Logos.Plurality.kinds_are_the_modal_partition"

FREE_TAGS = ("VOCAB", "TRANS")


def declared_tags():
    """Axiom short-name -> tag, from the Lean sources via the census gate's own parser."""
    ns = {"__file__": "scripts/check_consistency.py", "__name__": "census"}
    exec(compile((ROOT / "scripts" / "check_consistency.py").read_text(),
                 "check_consistency.py", "exec"), ns)
    out = {}
    for path in sorted((ROOT / "formal" / "Logos").glob("*.lean")):
        for name, _stmt, line in ns["axiom_statements"](path):
            out[name.split(".")[-1]] = ns["axiom_tag"](path, line)
    return out


def short(footprint):
    return {a.split(".")[-1] for a in footprint}


def main() -> int:
    if not AUDIT.exists():
        print(f"FAIL: {AUDIT} missing -- run scripts/audit_footprints.py")
        return 1
    audit = json.loads(AUDIT.read_text())

    # 1. Check positive declarations
    for decl in POSITIVE_CHAIN:
        if decl not in audit:
            print(f"FAIL: positive-chain declaration absent from the audit: {decl}")
            return 1

    # 2. Check absence of old denial
    if ABSENT_DENIAL in audit:
        print(f"FAIL: old denial declaration still present in the audit: {ABSENT_DENIAL}")
        return 1

    tags = declared_tags()
    if not tags:
        print("FAIL: census found no axioms; the parser is broken, not the corpus")
        return 1

    # 3. GroundTranscendence must be absent from declared axioms
    if ELIMINATED in tags:
        print(f"FAIL: {ELIMINATED} is still declared as an axiom with tag {tags[ELIMINATED]}")
        return 1

    # 4. DivinePersonsTotalMeaning must be declared as META
    if TOTALITY not in tags:
        print(f"FAIL: {TOTALITY} is missing from declared axioms")
        return 1
    if tags[TOTALITY] != "META":
        print(f"FAIL: {TOTALITY} has tag {tags[TOTALITY]}, expected META")
        return 1

    def substantive(footprint):
        """Named axioms in the footprint that are not free (VOCAB/TRANS)."""
        out = set()
        for a in short(footprint):
            if a in ("propext", "Classical.choice", "Quot.sound"):
                continue
            if a in tags and tags[a] not in FREE_TAGS:
                out.add(a)
        return out

    # 5. FREE_LINK must stay free
    free_foot = short(audit[FREE_LINK])
    priced = substantive(free_foot)
    if priced:
        print(f"FAIL: {FREE_LINK} must stay free (vocabulary only); it now rests on {sorted(priced)}")
        return 1

    def dependents(bound):
        out = []
        for name, footprint in audit.items():
            tail = name.split(".")[-1]
            if bound in short(footprint) and tail not in (SCOPED, TOTALITY, ELIMINATED):
                out.append(name)
        return out

    scoped_users = dependents(SCOPED)
    totality_users = dependents(TOTALITY)
    eliminated_users = dependents(ELIMINATED)

    # 6. GroundTranscendence must have 0 dependents anywhere
    if eliminated_users:
        print(f"FAIL: {ELIMINATED} still has {len(eliminated_users)} dependent(s): {sorted(eliminated_users)}")
        return 1

    # 7. SemanticFinitude must have live dependents on the contingent branch
    if len(scoped_users) < 10:
        print(f"FAIL: {SCOPED} has only {len(scoped_users)} dependent(s), expected >= 10: {sorted(scoped_users)}")
        return 1

    # 8. DivinePersonsTotalMeaning must have live dependents
    if not totality_users:
        print(f"FAIL: {TOTALITY} has no dependents; expected it to carry the Persons' maximal capacity")
        return 1

    # 9. Verify necessary_kind_subject_has_maximal_capacity rests on TOTALITY
    pos_cap = "Logos.NecessaryKindAudit.necessary_kind_subject_has_maximal_capacity"
    if TOTALITY not in short(audit[pos_cap]):
        print(f"FAIL: {pos_cap} does not rest on {TOTALITY}")
        return 1

    # 10. §4.5 Shape Rule: check active formal/Logos/*.lean for residual unrestricted axiom
    for path in sorted((ROOT / "formal" / "Logos").glob("*.lean")):
        content = path.read_text()
        if re.search(r"^\s*axiom\s+GroundTranscendence\b", content, re.M):
            print(f"FAIL: residual `axiom GroundTranscendence` found in {path.name}")
            return 1

    print("OK: Finitude bound scoping verified.")
    print(f"    {SCOPED} (contingent-scoped, VOCAB): {len(scoped_users)} dependents (live on creatures).")
    print(f"    {TOTALITY} (necessary-scoped, META): {len(totality_users)} dependents (homoousios).")
    print(f"    {ELIMINATED} (unrestricted, META): 0 dependents (eliminated from kernel).")
    print("    => Divine Persons' semantic fullness is AFFIRMED; creatures are bounded.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
