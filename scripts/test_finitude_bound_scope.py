#!/usr/bin/env python3
"""Gate WHICH finitude bound the corpus actually uses.

`scripts/test_axiom_census.py` pins how many axioms are declared. This pins something the census
cannot see: of the two halves `SemanticFinitude` (S5's split created), which one the 27 consumer
theorems actually rest on.

The claim asserted here is load-bearing for prose. `AGENTS.md`,
§10 row 6 and §11 all said the divine Persons' omniscience is *unasserted*, on the premise that
scoping `SemanticFinitude` to contingent subjects (`ContingentSubjectKind s -> ...`) exempts the
Persons, who are necessary. On 2026-10-03 that premise was measured and found false (§17):

  - `SemanticFinitude`  -- the contingent-scoped, `Tag: VOCAB` half -- has **0 dependents**.
  - `GroundTranscendence` -- the unrestricted, `Tag: META` half -- carries every consumer.

Nothing was ever narrowed, because nothing uses the narrowed half. The corpus therefore still
denies the Persons' omniscience, at a META price: `Plurality.kinds_are_the_modal_partition` (free)
reads `NecessarySubject p` as `NecessarySubjectKind p`, and
`NecessaryKindAudit.necessary_kind_subject_lacks_maximal_capacity` then gives
`not MaximalCapacity (EntityOf p)` for each Person.

The failure mode this gate closes is the one §17 and §14 both hit: **prose describing an intended
re-scope as though the kernel had adopted it.** A count cannot detect that, and neither can
`#print axioms` on any single declaration -- the unrestricted bound is a legitimate axiom with a
legitimate footprint. Only the *distribution of dependents across the two halves* shows it, and
until now nothing computed that distribution.

If a future milestone genuinely narrows the bound, this gate fails and the prose obligation
transfers with it: §1.7/§10/§11 may then say "unasserted", and only then.
Run: python3 scripts/test_finitude_bound_scope.py
"""
from __future__ import annotations

import collections
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
AUDIT = ROOT / "formal" / "axiom_audit.json"

SCOPED = "SemanticFinitude"
UNRESTRICTED = "GroundTranscendence"

# The theorems that make the Persons' denial of maximal capacity reachable at all. Each is
# checked here by name so that a rename cannot quietly strand the prose.
DENIAL_CHAIN = (
    "Logos.Plurality.kinds_are_the_modal_partition",
    "Logos.NecessaryKindAudit.necessary_kind_subject_lacks_maximal_capacity",
    "Logos.TrinitarianSubjectBridge.one_necessary_ground_three_free_necessary_persons",
)

# `kinds_are_the_modal_partition` is what turns "necessary" into "necessary kind", and it must
# stay free -- if it ever picks up an axiom, the Persons' denial is no longer reachable from
# vocabulary alone and the §17 chain needs re-pricing.
FREE_LINK = "Logos.Plurality.kinds_are_the_modal_partition"

# "Free" here means *vocabulary-only*: 0 substantive axioms. The corpus's vocabulary axioms
# (`Means`, `Subject`, `NecessarySubjectKind`, ...) are declared axioms and DO appear in
# footprints, so subtracting only `propext`/`Classical.choice` would misreport every VOCAB-only
# theorem as priced. The tag set comes from the same parser the census gate uses.
FREE_TAGS = ("VOCAB", "TRANS")


def declared_tags():
    """Axiom short-name -> tag, from the Lean sources via the census gate's own parser.

    Same derivation as `scripts/test_generator_price_prose.py`, so there is one parser, not two.
    """
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

    for decl in DENIAL_CHAIN:
        if decl not in audit:
            print(f"FAIL: denial-chain declaration absent from the audit: {decl}")
            return 1

    tags = declared_tags()
    if not tags:
        print("FAIL: census found no axioms; the parser is broken, not the corpus")
        return 1

    def substantive(footprint):
        """Named axioms in the footprint that are not free (VOCAB/TRANS)."""
        out = set()
        for a in short(footprint):
            if a in ("propext", "Classical.choice"):
                continue
            if a in tags and tags[a] not in FREE_TAGS:
                out.add(a)
        return out

    free_foot = short(audit[FREE_LINK])
    priced = substantive(free_foot)
    if priced:
        print(f"FAIL: {FREE_LINK} must stay free (vocabulary only); it now rests on {sorted(priced)}")
        print("       §17's chain is priced off this link being free. Re-price it before proceeding.")
        return 1

    def dependents(bound):
        out = []
        for name, footprint in audit.items():
            tail = name.split(".")[-1]
            if bound in short(footprint) and tail not in (SCOPED, UNRESTRICTED):
                out.append(name)
        return out

    scoped_users = dependents(SCOPED)
    unrestricted_users = dependents(UNRESTRICTED)

    # The load-bearing assertion. A nonzero count here would mean some consumer had actually
    # adopted the narrowed bound, and the §17 prose correction would no longer hold.
    if scoped_users:
        print(f"FAIL: {SCOPED} now has {len(scoped_users)} dependent(s): {sorted(scoped_users)}")
        print("       The contingent-scoped bound is now load-bearing. §1.7/§10/§11 said the Persons'")
        print("       omniscience is 'unasserted' on the strength of that narrowing; with live consumers")
        print("       that claim becomes checkable, and §17's correction must be revisited on the merits.")
        return 1

    if not unrestricted_users:
        print(f"FAIL: {UNRESTRICTED} has no dependents -- expected the unrestricted bound to carry the corpus")
        return 1

    # The denial must actually be reachable through the unrestricted bound.
    denial = "Logos.NecessaryKindAudit.necessary_kind_subject_lacks_maximal_capacity"
    if UNRESTRICTED not in short(audit[denial]):
        print(f"FAIL: {denial} does not rest on {UNRESTRICTED}; §17's denial chain no longer holds")
        return 1

    print("OK: the finitude bound the corpus uses is the UNRESTRICTED one.")
    print(f"    {SCOPED} (contingent-scoped, VOCAB): 0 dependents -- inert, as §17 states.")
    print(f"    {UNRESTRICTED} (unrestricted, META): {len(unrestricted_users)} dependents.")
    print("    => The three divine Persons' omniscience is DENIED at a META price, not unasserted.")
    print("       Plan §1.7 / §10 row 6 / §11 are corrected against this; see §17.")
    return 0


if __name__ == "__main__":
    sys.exit(main())