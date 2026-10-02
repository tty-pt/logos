#!/usr/bin/env python3
"""test_goal_audit.py — the `formal/goal_audit.json` contract, machine-checked.

This file exists because `STUPID_SIMON_SAYS.md` was written: a previous
`audit_goals.py` was declared "step 1 is DONE" on the strength of six
eye-checked spot-checks, and every measurement taken from the artifact by eye was
wrong. One of those spot-checks had a truncated goal string with its tail filled
in by hand. **No claim about this artifact may be made without an assertion here.**

Each check below corresponds to a measured defect recorded in
`RULE_R_CORRECTION_PLAN.md` §12.3. If one of them starts failing, the
artifact is drifting — do not relax the assertion to make the suite green; find
the cause in `scripts/audit_goals.py`.

Run `python3 scripts/audit_goals.py` first if `formal/goal_audit.json` is stale
(it takes minutes and needs `lake` on `$PATH`).
"""
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ARTIFACT = ROOT / "formal" / "goal_audit.json"

# Declaration names asserted verbatim in §13.3 / §4.0. Spelling them out is
# deliberate: these are the records the badge machinery reads, so a silent change
# to any of them must break the build rather than quietly alter a badge.
ASIETY = "Logos.AsieticChoice.Asiety"
ASIETIC_SUMMARY = "Logos.AsieticChoice.asietic_summary"
TRUE_CHOICE_EXISTS = "Logos.AsieticChoice.trueChoice_exists"
WEAK_CHOICE_ROUTE = "Logos.AsietyFreedom.weakChoice_implies_asiety"
C294_REFUTATION = "Logos.AsietyFreedom.rightWrongFactYieldsNoChooser"

# Lean's uniquifier suffix is `_uniq.<n>` appended to an identifier. It must be
# matched as a *marker*, not as a bare substring: the substring `_uniq` also
# occurs inside perfectly ordinary user-written names (`means_unique`), and the
# 22:57 artifact carries zero real uniquifiers, so a substring test only ever
# produced false positives. The assertion is unchanged in strength -- it is
# narrowed to the string the compiler actually produces.
HYGIENIC = ("_@", "_hyg", ".fvarId")
HYGIENIC_RE = re.compile(r"_uniq\.\d")


def main() -> int:
    if not ARTIFACT.exists():
        print(f"FAIL: {ARTIFACT} does not exist; run `python3 scripts/audit_goals.py`.")
        return 1
    # The artifact is a mapping of declaration name -> record, not a list.
    by_name = json.loads(ARTIFACT.read_text(encoding="utf-8"))
    records = list(by_name.items())          # (name, record) pairs
    errors: list[str] = []

    def check(cond: bool, msg: str) -> None:
        if not cond:
            errors.append(msg)

    thm_ax = [(nm, r) for nm, r in records if r.get("kind") in ("thm", "axiom")]

    # §13.3 #2 — truncated goals. A `thm`/`axiom` goal must be bracket-balanced;
    # a fragment cut at a pretty-printer line break leaves the conjuncts open.
    for nm, r in thm_ax:
        goal = r.get("goal", "")
        check(goal.count("(") == goal.count(")"),
              f"{nm}: goal is unbalanced ({goal.count('(')} '(' vs "
              f"{goal.count(')')} ')') — a truncated goal (§13.3 #2)")
        check("\\n" not in goal or "\n" not in goal,
              f"{nm}: goal contains a raw newline — unescaped (defect #2)")

    # §13.3 #7 — every thm/axiom has at least one structural conjunct.
    for nm, r in thm_ax:
        check(len(r.get("conjuncts", [])) >= 1,
              f"{nm}: no conjuncts recorded — the goal shape is unreadable")
        for c in r.get("conjuncts", []):
            check(c.get("head") != "(non-constant)",
                  f"{nm}: opaque conjunct head `(non-constant)` — the "
                  f"headSym resolution failed (§13.3 #7)")

    # §13.3 #3 — hygienic names must never reach the artifact.
    def hygienic(s: str) -> bool:
        return any(h in s for h in HYGIENIC) or bool(HYGIENIC_RE.search(s))

    for nm, r in records:
        for b in r.get("binderFree", []):
            check(not hygienic(b),
                  f"{nm}: hygienic binderFree name leaked: {b!r}")
        for h in r.get("hypothesis", []):
            check(not hygienic(str(h)),
                  f"{nm}: hygienic hypothesis name leaked: {h!r}")

    # §13.3 #4 — `valueHeads` is a channel for definitions only.
    for nm, r in records:
        # `opaque` has a value as well as a signature; a `thm`/`axiom` does not.
        # The defect was `valueHeads == ["Prop"]` on 2 836 theorems and axioms,
        # read off the `Expr.sort 0` fallback of `declType`.
        if r.get("kind") in ("def", "opaque"):
            continue
        check(r.get("valueHeads") in ([], None),
              f"{nm} ({r.get('kind')}): valueHeads={r.get('valueHeads')!r} — "
              f"only a def/opaque has a value (§13.3 #4)")

    # §13.3 #1 — no value whose entire content is a *splittable* connective.
    # Γ has no claim that is only an `And`, and `And` is exactly the connective
    # the reader splits, so `["And"]` means it split too late and threw the
    # claim away. `Iff` is **not** split here and a biconditional *is* a claim:
    # `def Choice.SelfAssertedChoice (s : Subject) (p : Prop) : Prop :=
    # p ↔ ∃ q : Prop, Chooses s p q` is faithfully `["Iff"]`. Asserting otherwise
    # was asserting that Γ cannot state a biconditional.
    for nm, r in records:
        check(not (r.get("valueHeads") in (["And"],)),
              f"{nm}: valueHeads={r.get('valueHeads')!r} is a bare connective "
              f"— quantifiers were not peeled before splitting (§13.3 #1)")

    # §13.3 #5 — a quantified conjunct must say what it ranges over, or gate G1
    # is unsatisfiable.
    for nm, r in records:
        for c in r.get("conjuncts", []):
            if c.get("quant") in ("forall", "exists"):
                check(len(c.get("sorts", [])) >= 1,
                      f"{nm}: {c['quant']} conjunct with no bound sorts — "
                      f"G1 cannot test it (§13.3 #5)")

    # §13.3 #6 — `conjuncts[].sorts` holds sorts, not premise heads.
    # The invariant is that a **premise head** never appears in `sorts`; those are
    # recorded in `hypothesis[].head` instead, and gate G2 compares sorts.
    premise_heads = {"ClaimsCorrect", "ChoiceField", "GenuineNormativity"}
    for nm, r in records:
        for c in r.get("conjuncts", []):
            for s in c.get("sorts", []):
                check(s.rsplit(".", 1)[-1] not in premise_heads,
                      f"{nm}: {s!r} is a premise, not a sort (§13.3 #6)")

    # A bare `Exists` in `sorts` is a binder *named by* an `∃` proposition, not a
    # sort: `Logos.BipolarityRetorsion.A18_is_independent_optional_semantic_premise`
    # concludes `A ∧ (∀ h : ∃ s : Subject, ∃ p : Prop, ClaimsNormativeCorrectness
    # s p, ¬ NoGN)`, and `h`'s domain is that `∃`. It is recorded honestly, and the
    # two facts a consumer must know are asserted here rather than assumed:
    #   (a) the record's `hypothesis` is EMPTY for it -- `Meta.forallTelescope`
    #       peels only *leading* binders, so a premise under a conjunction is not
    #       collected. This is a real reader scope limit; §7.2 step 2's G1/G2
    #       cannot use `hypothesis` to enumerate premises.
    #   (b) `sorts` therefore carries `Exists`, and no gate may read it as a sort.
    # Both are pinned by name so the population cannot grow unnoticed.
    a18 = "Logos.BipolarityRetorsion.A18_is_independent_optional_semantic_premise"
    if a18 in by_name:
        r = by_name[a18]
        check(r.get("hypothesis") == [],
              f"{a18}: hypothesis is {r.get('hypothesis')!r}, but premises under a "
              f"conjunction are not collected — if this changed, the scope limit "
              f"this asserts is gone and G1/G2 must be revisited")
        check(any(s.rsplit(".", 1)[-1] == "Exists"
                  for c in r.get("conjuncts", []) for s in c.get("sorts", [])),
              f"{a18}: expected a bare `Exists` binder type in conjuncts[].sorts")

    # §13.3 #8 — a refutation must be distinguishable from any other negation.
    # This is the record §4.1 item 2 and §8.2 make load-bearing.
    if C294_REFUTATION in by_name:
        spines = [c.get("spine", "") for c in by_name[C294_REFUTATION]["conjuncts"]]
        check(len(set(spines)) == len(spines),
              f"{C294_REFUTATION}: the conjuncts are not distinct: {spines}")
        joined = " ".join(spines)
        check("N_T" in joined and "N_F" in joined,
              f"{C294_REFUTATION}: the T/F distinction is absent from the spines "
              f"— two different refutations would compare IDENTICAL (§13.3 #8)")

        # C294's witness was repaired 2026-10-03 (plan §21.5 / Finding 2c). The old second
        # conjunct was `¬ ∃ s p q, M s p ∧ M s q` with no `p ≠ q`, which is *equivalent* to
        # meaninglessness — `AsietyFreedom.pairwise_denied_forces_meaninglessness` proves the
        # old form admitted only worlds where nothing is meant. So `M := fun _ _ => False` was
        # forced on the statement, not chosen, and the row was an uninterpreted-signature
        # artifact reported at `{}`.
        #
        # The exact conjunct COUNT is not asserted (it was pinned at 3 for the old arity and
        # pins nothing); distinctness and the T/F pair above are the §13.3 #8 claim and are
        # kept. What is asserted instead is the *repair*, by the three spines that only the
        # repaired statement produces. Reverting C294 to the degenerate form deletes all three
        # and fails here — a stronger gate than the one it replaces, not a loosened one.
        # These are the strings the compiler emits: the model conjunct `M/2(s, p)`, the order
        # conjunct `Alternatives.Incompatible/2(p, q)`, and the distinctness guard
        # `Ne/3(Prop, p, q)` that makes the denial non-degenerate.
        for label, marker, why in (
            ("signification instantiated", "M/2(s, p)",
             "the repaired model must MEAN something — the old form could not"),
            ("order granted", "Incompatible/2(p, q)",
             "the repaired model must grant order while denying pairwise signification"),
            ("distinctness guard", "Ne/3(Prop, p, q)",
             "the `p ≠ q` guard is what stops the statement collapsing to meaninglessness"),
        ):
            check(any(marker in s for s in spines),
                  f"{C294_REFUTATION}: {label} is absent from the conjunct spines — "
                  f"{why}; spines were {spines}")

        # The evidence lemma for the repair must exist, or the "was forced" claim is prose.
        check("Logos.AsietyFreedom.pairwise_denied_forces_meaninglessness" in by_name,
              "AsietyFreedom.pairwise_denied_forces_meaninglessness is missing — it is the "
              "kernel proof that C294's pre-repair form admitted only degenerate models, so "
              "without it the repair's necessity is asserted rather than checked")

    # --- the records the badge machinery actually reads (§4.0) ---
    if ASIETY in by_name:
        heads = by_name[ASIETY].get("valueHeads", [])
        check(heads == ["Eq", "Logos.AsieticChoice.TrueChoice"],
              f"{ASIETY}: valueHeads={heads!r}, expected the existential "
              f"identification [Eq, TrueChoice] (§4.0 item 2)")
    if TRUE_CHOICE_EXISTS in by_name:
        sorts = by_name[TRUE_CHOICE_EXISTS]["conjuncts"][0].get("sorts", [])
        check([s.rsplit(".", 1)[-1] for s in sorts] == ["Subject", "Prop", "Prop"],
              f"{TRUE_CHOICE_EXISTS}: binder sorts {sorts!r}, expected "
              f"['Subject', 'Prop', 'Prop'] (§4.0 item 3)")
    if ASIETIC_SUMMARY in by_name:
        cs = by_name[ASIETIC_SUMMARY]["conjuncts"]
        check(len(cs) == 3,
              f"{ASIETIC_SUMMARY}: {len(cs)} conjuncts, expected the three-way "
              f"conjunction C286 names (§4.0 item 3)")
        if len(cs) == 3:
            first = [s.rsplit(".", 1)[-1] for s in cs[0].get("sorts", [])]
            check(first == ["Subject", "Prop"],
                  f"{ASIETIC_SUMMARY} conjunct 1: sorts {first!r}, expected "
                  f"['Subject', 'Prop'] — an implication antecedent must not be "
                  f"recorded as a sort (isArrowBinder)")
            check([c.get("quant") for c in cs] == ["forall", "forall", "exists"],
                  f"{ASIETIC_SUMMARY}: quantifiers {[c.get('quant') for c in cs]!r}, "
                  f"expected ['forall','forall','exists'] — the existential is the "
                  f"unconditional-existence conjunct")
    if WEAK_CHOICE_ROUTE in by_name:
        r = by_name[WEAK_CHOICE_ROUTE]
        check(any("GenuineNormativity" in h.get("spine", "") for h in r["hypothesis"]),
              f"{WEAK_CHOICE_ROUTE}: no premise spine identifies GenuineNormativity "
              f"— the route's named premise is unreadable (§13.3 #8)")
        check(any("Asiety" in c.get("spine", "") for c in r["conjuncts"]),
              f"{WEAK_CHOICE_ROUTE}: no conjunct concludes Asiety — this is the "
              f"Level-1 IDENTICAL route of §4")

    for name in (ASIETY, ASIETIC_SUMMARY, TRUE_CHOICE_EXISTS, WEAK_CHOICE_ROUTE,
                 C294_REFUTATION):
        check(name in by_name, f"{name} is missing from the artifact — the corpus "
              f"was renamed and §4 of the plan is now stale")

    # §13.5 / Item 1 — sort-headed goals contract (1 657 records, 20 axiom/opaque).
    #
    # 1 645 → 1 647 at S2 (the personal-ground work): the whole delta was
    # two `def`s, `GroundByBeing` and `Perichoretic`.
    #
    # 1 647 → 1 657 at S3, and again the whole delta is accounted for: seven
    # `Prop`-valued `def`s (`means`, `potency`, `boundedMeaning`, `entityMeansIn`,
    # `freeWillIn`, `guardAntecedentHolds`, `meansInstantiated`), plus three generated
    # structure artefacts from `BoundedMeaningSignature` — its two sort projections
    # `Subject`/`Entity` (`Type`) and `ctorIdx` (`Nat`). That is +7 `Prop`, +2 `Type`,
    # +1 `Nat`, and +10 `def`, all from one module. Every binder survives in
    # `boundSorts`, so the rule that a `def`'s value goes to `conjunctShapes`
    # un-pre-peeled is holding; `Bool`, `axiom` and `opaque` are unmoved throughout.
    # S4 added exactly ONE sort-headed record from `TrinitarianSubjectBridge`:
    # `DivineRole.ctorIdx` (`Nat`-headed `def`), the generated recursor artefact
    # of the three-constructor `DivineRole` inductive. Hence +1 sort-headed, +1 `Nat`
    # and +1 `def` are the *same* record, not three. The module's two axioms do
    # NOT appear here — `DivineSubjectRole : Subject → DivineRole` has
    # `conjuncts[0].head == DivineRole`, not a sort head, and `axiom` records are
    # counted separately below. Verified record-by-record before bumping.
    sorts_set = {"Prop", "Nat", "Type", "Bool", "Sort"}
    sort_headed = {}
    for nm, r in records:
        cs = r.get("conjuncts", [])
        if cs and all(c.get("head") in sorts_set for c in cs):
            sort_headed[nm] = r

    # 1659 -> 1658 on 2026-10-03: -4 declarations with the `Consubstantial` family deleted in
    # plan §24, of which -1 was sort-headed (each of the four was a Prop-headed or def-headed
    # record; `consubstantial_comm` was the sort-bearing one and `the_three_persons_are_consubstantial`
    # the def-valued one). Recorded here rather than left implicit: every count in this file moved
    # down for the same single reason, and a count that drifts for no stated cause is the failure
    # mode AGENTS.md warns about for the axiom census.
    # (C294's repair evidence). Every count below moves together with any added declaration.
    check(len(sort_headed) == 1658,
          f"expected 1658 sort-headed records in goal_audit, got {len(sort_headed)}")

    sh_heads = {}
    sh_kinds = {}
    for r in sort_headed.values():
        h = r["conjuncts"][0].get("head")
        sh_heads[h] = sh_heads.get(h, 0) + 1
        k = r.get("kind")
        sh_kinds[k] = sh_kinds.get(k, 0) + 1

    check(sh_heads.get("Prop") == 1278, f"expected 1278 Prop-headed records, got {sh_heads.get('Prop')}")
    check(sh_heads.get("Nat") == 202, f"expected 202 Nat-headed records, got {sh_heads.get('Nat')}")
    check(sh_heads.get("Type") == 175, f"expected 175 Type-headed records, got {sh_heads.get('Type')}")
    check(sh_heads.get("Bool") == 3, f"expected 3 Bool-headed records, got {sh_heads.get('Bool')}")

    check(sh_kinds.get("def") == 1638, f"expected 1638 def sort-headed records, got {sh_kinds.get('def')}")
    check(sh_kinds.get("axiom") == 15, f"expected 15 axiom sort-headed records, got {sh_kinds.get('axiom')}")
    check(sh_kinds.get("opaque") == 5, f"expected 5 opaque sort-headed records, got {sh_kinds.get('opaque')}")

    expected_relational_axioms = {
        "Logos.Agency.HasNature",
        "Logos.Agency.Initiates",
        "Logos.Agency.Means",
        "Logos.Agency.Nature",
        "Logos.Agency.NecessarySubjectKind",
        "Logos.Agency.State",
        "Logos.Agency.Subject",
        "Logos.Agency.Will",
        "Logos.Agency.Wills",
        "Logos.Agency.act",
        "Logos.DivineAgape.DivineLove",
        "Logos.DivineAgape.IsSpirit",
        "Logos.DivineAgape.IsWord",
        "Logos.LovesAsGround.GroundBearsGood",
        "Logos.MoralFrontierAudit.Evil",
        "Logos.OughtRetorsion.Ought",
        "Logos.PersonhoodOntologyAudit.HistoricalSubstantivePerson",
        "Logos.Retorsion.DependsOn",
        "Logos.Retorsion.WingedPig",
        "Logos.ThomisticAct.Produces",
    }
    actual_sh_axioms = {nm for nm, r in sort_headed.items() if r.get("kind") in ("axiom", "opaque")}
    check(actual_sh_axioms == expected_relational_axioms,
          f"sort-headed axiom/opaque mismatch: missing={expected_relational_axioms - actual_sh_axioms}, "
          f"extra={actual_sh_axioms - expected_relational_axioms}")

    # Item 2 — entails REFUTES branch matches head with arguments.
    import sys
    sys.path.insert(0, str(ROOT))
    import scripts.build_deduction as bd
    from scripts.build_deduction import ConjunctShape, ClaimShape, entails, REFUTES, INCOMPARABLE

    claim_act = ClaimShape(
        conjuncts=(ConjunctShape(quant="plain", sorts=(), head="Logos.Agency.Act", spine="Logos.Agency.Act/2(s, p)"),),
        polarity="positive",
    )
    # Positive case: Not spine names head with arguments
    cand_refutes = ClaimShape(
        conjuncts=(ConjunctShape(quant="plain", sorts=(), head="Not", spine="!(Logos.Agency.Act/2(s, p))"),),
        polarity="contradiction",
    )
    check(entails(cand_refutes, claim_act) == REFUTES,
          f"expected entails(cand_refutes, claim_act) == REFUTES, got {entails(cand_refutes, claim_act)}")

    # Near-miss 1: Act is an argument inside Other/1, not the head with arguments
    cand_near_miss1 = ClaimShape(
        conjuncts=(ConjunctShape(quant="plain", sorts=(), head="Not", spine="!(Logos.Agency.Other/1(Logos.Agency.Act))"),),
        polarity="contradiction",
    )
    check(entails(cand_near_miss1, claim_act) == INCOMPARABLE,
          f"near-miss 1 (Act as argument to Other) must be INCOMPARABLE, got {entails(cand_near_miss1, claim_act)}")

    # Near-miss 2: bare head without arguments
    cand_near_miss2 = ClaimShape(
        conjuncts=(ConjunctShape(quant="plain", sorts=(), head="Not", spine="!(Logos.Agency.Act)"),),
        polarity="contradiction",
    )
    check(entails(cand_near_miss2, claim_act) == INCOMPARABLE,
          f"near-miss 2 (bare Act with no arguments) must be INCOMPARABLE, got {entails(cand_near_miss2, claim_act)}")


    if errors:
        print(f"\nFAIL: {len(errors)} goal-audit regression(s)")
        for e in errors[:40]:
            print(f"  - {e}")
        if len(errors) > 40:
            print(f"  … and {len(errors) - 40} more")
        return 1
    print(f"\nOK: goal-audit contract holds ({len(records)} records, "
          f"{len(thm_ax)} thm/axiom shapeless-free, hygienic names absent).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())