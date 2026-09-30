#!/usr/bin/env python3
"""test_deduction_compiler.py — Genericity, Provenance, and Sensitivity Verification Suite.

Validates:
1. Genericity: Proves that the proof compiler operates domain-independently by compiling
   synthetic non-theological theorems (e.g. transitivity A → B → C and reductio P → Q, ¬Q → False)
   into rigorous natural deduction ProofIR structures.
2. Provenance: Verifies that every displayed inferential step in README.md maps to
   an identified source rule, premise inputs, and kernel declaration reference, and that
   NoRight retorsion (0 substantive axioms) is strictly distinguished from the AxJudicativeBipolarity
   bridge to free will.
3. Sensitivity: Proves that mutating an underlying proof in memory immediately cascades to
   the generated deduction manuscript.
"""

import sys
import copy
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

import scripts.build_deduction as bd
from scripts.build_deduction import (
    parse_lean_sources,
    parse_gapmap,
    load_depgraph,
    load_audit,
    compile_lean_proof,
    discover_deduction_sections,
    render_deduction_sections,
    Rule,
    ProofIR,
    ProofStepIR,
    _CTX,
    axiom_full_map,
    AX_ID,
    OUT_PATH,
    build_boundary_by_decl,
    INCOMPARABLE,
)


def test_genericity():
    print("Testing compiler genericity with synthetic non-theological theorems…")
    
    with tempfile.TemporaryDirectory() as tmpdir:
        tmppath = Path(tmpdir)
        lean_file = tmppath / "GenericTest.lean"
        lean_file.write_text("""namespace TestModule

theorem test_trans (hA : PremiseA) (hAB : PremiseA → PremiseB) (hBC : PremiseB → PremiseC) : PremiseC := by
  have hB : PremiseB := hAB hA
  exact hBC hB

theorem test_reductio (hP : HypothesisP) (hPQ : HypothesisP → HypothesisQ) (hNQ : ¬ HypothesisQ) : False := by
  have hQ : HypothesisQ := hPQ hP
  exact hNQ hQ

end TestModule
""", encoding="utf-8")

        # Mock decls for synthetic theorems
        mock_decls = {
            "TestModule.test_trans": {
                "kind": "theorem",
                "name": "test_trans",
                "file": "GenericTest.lean",
                "line": 3,
                "statement": "theorem test_trans (hA : PremiseA) (hAB : PremiseA → PremiseB) (hBC : PremiseB → PremiseC) : PremiseC",
                "doc": "Hypothetical syllogism transitivity theorem."
            },
            "TestModule.test_reductio": {
                "kind": "theorem",
                "name": "test_reductio",
                "file": "GenericTest.lean",
                "line": 7,
                "statement": "theorem test_reductio (hP : HypothesisP) (hPQ : HypothesisP → HypothesisQ) (hNQ : ¬ HypothesisQ) : False",
                "doc": "Reductio ad absurdum contradiction theorem."
            }
        }
        
        orig_lean_dir = bd.LEAN_DIR
        bd.LEAN_DIR = tmppath
        try:
            # 1. Compile transitivity
            p_trans = compile_lean_proof("TestModule.test_trans", mock_decls, {}, {}, {})
            assert len(p_trans.assumptions) == 3, f"Expected 3 assumptions, got {len(p_trans.assumptions)}"
            assert len(p_trans.steps) == 1, f"Expected 1 intermediate step, got {len(p_trans.steps)}"
            assert p_trans.steps[0].rule == Rule.LEMMA_APP
            assert p_trans.steps[0].proposition == "PremiseB"
            assert p_trans.conclusion.rule == Rule.CONCLUSION
            assert p_trans.conclusion.proposition == "PremiseC"
            print("  ✓ Generic transitivity theorem compiled into ProofIR: (A, A → B, B → C) ⊢ B ⊢ C")

            # 2. Compile reductio
            p_reductio = compile_lean_proof("TestModule.test_reductio", mock_decls, {}, {}, {})
            assert len(p_reductio.assumptions) == 3, f"Expected 3 assumptions, got {len(p_reductio.assumptions)}"
            assert len(p_reductio.steps) == 1
            assert p_reductio.steps[0].rule == Rule.LEMMA_APP
            assert p_reductio.steps[0].proposition == "HypothesisQ"
            assert p_reductio.conclusion.rule == Rule.CONTRADICTION
            assert p_reductio.conclusion.proposition == "⊥"
            print("  ✓ Generic reductio theorem compiled into ProofIR: (P, P → Q, ¬Q) ⊢ Q ⊢ ⊥")
            
            # 3. Test rendering synthetic proofs
            mock_section = [{
                "title": "Synthetic Logic",
                "summary": "Pure logical proofs without domain semantics.",
                "proofs": [p_trans, p_reductio],
                "conclusion": "PremiseC ∧ ⊥",
                "investigations": []
            }]
            _doc = render_deduction_sections(mock_section, mock_decls, {})
            rendered = "\n".join(_doc.get("readme")) + "\n" + "\n".join(_doc.get("ledger"))
            assert "Assume PremiseA, and PremiseA → PremiseB, and PremiseB → PremiseC:" in rendered
            assert "1. PremiseB  (modus ponens via hAB)" in rendered
            assert "∴ PremiseC" in rendered
            assert "Contradiction:" in rendered
            print("  ✓ Synthetic proofs rendered into natural deduction manuscript without domain bias.")
        finally:
            bd.LEAN_DIR = orig_lean_dir


def test_provenance(decls: dict, node_map: dict, graph: dict):
    print("Testing proof provenance and formal distinction in README.md…")
    text = OUT_PATH.read_text(encoding="utf-8")
    assert text.startswith("# Γ — The Deduction\n"), "README.md must start on line 1"
    
    # 1. Distinction: NoRight retorsion is axiom-free, AxJudicativeBipolarity is priced at the bridge
    ledger = (ROOT / "investigations" / "ledger.md").read_text(encoding="utf-8")
    assert "NoRight ≡ ¬NormativeRightExists" in ledger, "NoRight definition gloss lives in the ledger"
    assert "claims_correct_no_right_self_refuting" in text
    assert "DirectNormativeRetorsion" in text
    
    # Check that claims_correct_no_right_self_refuting does not require AxJudicativeBipolarity
    p_no_right = compile_lean_proof("Logos.DirectNormativeRetorsion.claims_correct_no_right_self_refuting", decls, node_map, graph, {})
    assert "AxJudicativeBipolarity" not in p_no_right.subst_axioms, "NoRight retorsion must have 0 substantive axioms"
    assert len(p_no_right.subst_axioms) == 0, f"NoRight retorsion must be axiom-free, got: {p_no_right.subst_axioms}"
    print("  ✓ NoRight retorsion verified: strictly axiom-free (0 substantive axioms).")
    
    # Check that the bridge to GenuineNormativity requires AxJudicativeBipolarity
    p_bridge = compile_lean_proof("Logos.RetorsiveNormativity.claims_correct_presupposes_normativity", decls, node_map, graph, {})
    assert "AxJudicativeBipolarity" in p_bridge.subst_axioms, "Semantic bridge must price AxJudicativeBipolarity"
    print("  ✓ Bridge to GenuineNormativity verified: explicitly prices AxJudicativeBipolarity (SEM).")
    
    # Check that indubitable_normative_free_will derives free will with 0 substantive axioms
    p_fw = compile_lean_proof("Logos.IndubitableNormativeFreeWill.indubitable_normative_free_will", decls, node_map, graph, {})
    assert len(p_fw.subst_axioms) == 0, "indubitable_normative_free_will must have 0 substantive axioms"
    assert any("Chooses" in s.description for s in p_fw.steps)
    assert any("FreeWill" in s.description for s in p_fw.steps)

    # Check local edge classifications
    cat_no_right, _ = bd.classify_proof_edge(p_no_right, graph, decls)
    cat_bridge, badge_bridge = bd.classify_proof_edge(p_bridge, graph, decls)
    cat_fw, badge_fw = bd.classify_proof_edge(p_fw, graph, decls)
    assert cat_no_right == "PROVEN", f"Expected NoRight retorsion to be PROVEN, got {cat_no_right}"
    assert "SEMANTIC" in cat_bridge, f"Expected bridge to be SEMANTIC, got {cat_bridge}"
    assert "AxJudicativeBipolarity" in badge_bridge
    assert cat_fw == "PROVEN", f"Expected Free Will derivation to be PROVEN, got {cat_fw}"
    assert badge_fw.startswith("PROVEN"), f"Expected Free Will badge to start with PROVEN, got {badge_fw}"

    print("  ✓ Indubitable Free Will derivation verified: definitions expanded as justification rules, 0 substantive axioms.")


def test_minimal_assumption_dominance():
    print("Testing minimal-assumption route dominance & proof length decoupling…")
    # Synthetic candidate route 1: Short (1 step) but requires substantive axiom AxBridge (SEM)
    p_short = ProofIR(
        full_name="Synthetic.short_bridge_proof",
        name="short_bridge_proof",
        kind="theorem",
        file="Synthetic.lean",
        line=10,
        goal="TargetConclusion",
        doc="",
        subst_axioms=["Synthetic.AxBridge"],
    )
    r_short = bd.CandidateRoute(
        target_concepts={"TargetConclusion"},
        source_decl="Synthetic.short_bridge_proof",
        conclusion_prop="TargetConclusion",
        proof=p_short,
        premises=["PremiseA"],
        subst_axioms={"AxBridge"},
        status="PROVEN↑",
        countermodel_blocked=False,
    )

    # Synthetic candidate route 2: Longer (3 steps) but 0 substantive axioms (pure logic)
    p_long = ProofIR(
        full_name="Synthetic.long_axiom_free_proof",
        name="long_axiom_free_proof",
        kind="theorem",
        file="Synthetic.lean",
        line=20,
        goal="TargetConclusion",
        doc="",
        subst_axioms=[],
    )
    r_long = bd.CandidateRoute(
        target_concepts={"TargetConclusion"},
        source_decl="Synthetic.long_axiom_free_proof",
        conclusion_prop="TargetConclusion",
        proof=p_long,
        premises=["PremiseB"],
        subst_axioms=set(),
        status="PROVEN",
        countermodel_blocked=False,
    )

    # Dominance check: Longer axiom-free route MUST strictly dominate shorter bridge-dependent route
    verdict = bd.compare_routes(r_long, r_short)
    assert verdict == "DOMINATES", f"Expected r_long to DOMINATE r_short, got {verdict}"
    assert bd.compare_routes(r_short, r_long) == "DOMINATED_BY"

    undom, dom = bd.select_strongest_routes([r_short, r_long])
    assert len(undom) == 1 and undom[0].source_decl == "Synthetic.long_axiom_free_proof"
    assert len(dom) == 1 and dom[0].source_decl == "Synthetic.short_bridge_proof"

    # Test operational countermodel blockage engine on real extracted separation pairs
    mock_sep_pairs = [("act", "freewill", "not_entails_decoupled_freewill")]
    assert bd.is_route_countermodel_blocked(["Act s p"], {"FreeWill"}, set(), mock_sep_pairs) is True
    assert bd.is_route_countermodel_blocked(["Act s p"], {"FreeWill"}, {"AxIntentionalChoice"}, mock_sep_pairs) is False
    assert bd.is_route_countermodel_blocked(["GenuineNormativity s p q"], {"FreeWill"}, set(), mock_sep_pairs) is False

    # Test implication unwrapping and target concept normalization
    assert bd.extract_target_concepts("(Act s p) → ∃ s, FreeWill s") == {"FreeWill"}
    assert bd.extract_target_concepts("DeliberateChoice s p q → Chooses s p q") == {"Chooses"}
    assert bd.extract_target_concepts("ClaimsCorrect s NoRight → NoRight → False") == {"NoRight"}
    assert bd.extract_target_concepts("Chooses s p q ∧ FreeWill s") == {"Chooses", "FreeWill"}

    # Countermodel blockage dominance check: Unblocked route dominates countermodel-blocked route
    r_blocked = copy.deepcopy(r_long)
    r_blocked.source_decl = "Synthetic.blocked_proof"
    r_blocked.countermodel_blocked = True
    assert bd.compare_routes(r_long, r_blocked) == "DOMINATES"

    print("  ✓ Minimal-assumption principle verified: longer axiom-free route strictly dominates shorter bridge route.")


def test_sensitivity(decls: dict, node_map: dict, graph: dict, sections: list):
    print("Testing dynamic sensitivity to proof mutations…")
    def_reg = {}
    baseline_secs = discover_deduction_sections(sections, decls, node_map, graph, def_reg)
    _base = render_deduction_sections(baseline_secs, decls, node_map)
    baseline_text = "\n".join(_base.get("readme")) + "\n" + "\n".join(_base.get("ledger"))
    
    # 1. Mutate theorem statement in memory
    mutated_decls = copy.deepcopy(decls)
    target = "Logos.PersonalGroundOfReality.the_person_supports_the_reality_of_right"
    orig_stmt = mutated_decls[target]["statement"]
    mutated_decls[target]["statement"] = orig_stmt + " ∧ True"
    _CTX["decls"] = mutated_decls
    mutated_secs = discover_deduction_sections(sections, mutated_decls, node_map, graph, {})
    _mut = render_deduction_sections(mutated_secs, mutated_decls, node_map)
    mutated_text = "\n".join(_mut.get("readme")) + "\n" + "\n".join(_mut.get("ledger"))
    _CTX["decls"] = decls
    assert mutated_text != baseline_text
    print("  ✓ Sensitivity verified: hypothesis mutation dynamically updated deduction output.")
    
    # 2. Mutate axiom footprint in memory
    orig_audit = list(bd._AUDIT.get(target, []))
    bd._AUDIT[target] = orig_audit + ["Logos.Value.AxTwoSubjects"]
    mutated_secs2 = discover_deduction_sections(sections, decls, node_map, graph, {})
    _mut2 = render_deduction_sections(mutated_secs2, decls, node_map)
    mutated_text2 = "\n".join(_mut2.get("readme")) + "\n" + "\n".join(_mut2.get("ledger"))
    bd._AUDIT[target] = orig_audit
    assert mutated_text2 != baseline_text
    assert "AxTwoSubjects" in mutated_text2
    print("  ✓ Sensitivity verified: axiom footprint mutation dynamically updated local bridge pricing.")


def test_classifier_agreement(decls, node_map, graph, sections):
    """`strength_of` and `refutation_kind` must agree on every routed declaration,
    and the gate must fire when they are forced apart.

    Both classify one fact — machine-refutation vs bound — and while they could
    disagree silently a row could print a `🧱` beside a `✅`. They did: the
    `refutation_kind` separation test was `goal.startswith("∃")`, so any
    existential-headed theorem read as a countermodel. That returned
    `COUNTERMODEL · ⇏` for `exactly_one_universal_modal_ground`
    (`∃! g, UniversalModalGround g` — the one-ground claim Γ actually proves) and
    for `the_creation_countermodel_is_a_populated_contingent_world`, while
    `strength_of` said `PROVEN` for both.
    """
    build_boundary_by_decl(sections, decls)
    bd._COMPILED_BY_FULL.clear()
    bd._CTX["compiled"] = {}

    routed, disagreements = 0, []
    for row in bd.CLASSICAL_ATTRIBUTES:
        claim = bd._classical_claim_of(row)
        if not claim:
            continue
        cp = bd.compiled_proof(claim)
        if not cp:
            continue
        shape = bd.claim_shape_of(claim, premises=bd.route_premises(cp))
        try:
            tier = bd.select_route(shape, bd.route_candidates(shape))
        except SystemExit:
            continue
        sep = bd.claim_is_separation(shape)
        for p in tier:
            routed += 1
            cls = bd.strength_of(p, shape)
            kind = bd.refutation_kind(p)
            if (cls == "CONTRADICTION") != (kind in bd._REFUTATION_KINDS):
                disagreements.append(f"{p.full_name}: {cls} vs {kind}")
            elif sep and kind in bd._NOT_A_BOUND_KINDS:
                disagreements.append(f"{p.full_name}: separation badged {cls} but kind {kind}")
            elif not sep and kind == "COUNTERMODEL · ⇏":
                disagreements.append(f"{p.full_name}: kind {kind} but claim not a separation")
    assert not disagreements, (
        "strength ladder and refutation kind disagree on routed declarations: "
        + "; ".join(disagreements))
    assert routed > 0, "no routed declarations found — the census proved nothing"

    # The two positive-existence theorems that the `∃` proxy used to misread. Named
    # explicitly: a count going to zero would also mean the check stopped running.
    for full, expected_kind in (
        ("Logos.FoundationalUnicity.exactly_one_universal_modal_ground",
         "🪞 INSTANTIATION — not a death"),
        ("Logos.ConditionalTheology."
         "the_creation_countermodel_is_a_populated_contingent_world",
         "🪞 INSTANTIATION — not a death"),
        ("Logos.FoundationalUnicity.unicity_does_not_force_unitarian_monad",
         "COUNTERMODEL · ⇏"),
    ):
        p = bd.compiled_proof(full)
        assert p is not None, f"{full} is not compiled — the census is not exercising it"
        assert bd.refutation_kind(p) == expected_kind, (
            f"{full}: refutation_kind is {bd.refutation_kind(p)!r}, "
            f"expected {expected_kind!r}")
        assert bd._shape_polarity(p) == "positive", (
            f"{full}: expected audited polarity 'positive', got "
            f"{bd._shape_polarity(p)!r} — the ∃ proxy is back if this is 'separation'")
    print(f"  ✓ Classifier agreement: {routed} routed declarations, 0 disagreements; "
          f"∃-proxy regression asserted by name.")

    # The gate itself. Three ways it must fail, one per clause it asserts, so a
    # future edit that weakens one clause is caught by its own scenario.
    COUNTER = "Logos.FoundationalUnicity.unicity_does_not_force_unitarian_monad"
    cp = bd.compiled_proof(COUNTER)
    claim = bd.claim_shape_of(COUNTER, premises=bd.route_premises(cp))
    entries = [(cp, bd.claim_shape_of(COUNTER, premises=bd.route_premises(cp)),
                bd._relation_of(cp, claim))]
    saved = (bd.strength_of, bd.refutation_kind, bd.claim_is_separation)
    try:
        # (a) the 🧱-beside-✅ defect: a separation claim whose terminator label
        #     reads as a proof.
        bd.refutation_kind = lambda pr, denial_hypothesis=None: "🪞 INSTANTIATION — not a death"
        _expect_gate_failure(entries, claim, "a 🧱 row labelled an instantiation")
        bd.refutation_kind = saved[1]

        # (b) a claim that is not a separation reading as a countermodel.
        bd.claim_is_separation = lambda cl: False
        _expect_gate_failure(entries, claim, "a non-separation claim read as a countermodel")
        bd.claim_is_separation = saved[2]

        # (c) a refutation terminator with no CONTRADICTION class.
        bd.strength_of = lambda pr, cl, **kw: "PROVEN"
        bd.refutation_kind = lambda pr, denial_hypothesis=None: "⊥ CONTRADICTION"
        _expect_gate_failure(entries, claim, "a ⊥ terminator not badged CONTRADICTION")
    finally:
        bd.strength_of, bd.refutation_kind, bd.claim_is_separation = saved
    print("  ✓ Agreement gate fails loudly on all three forced disagreements.")


def _expect_gate_failure(entries, claim, why):
    try:
        bd._check_classifier_agreement(entries, claim, "selftest")
    except SystemExit as e:
        assert "disagree" in str(e), f"gate failed for the wrong reason ({why}): {e}"
    else:
        raise AssertionError(
            f"_check_classifier_agreement did not fail on: {why}")


def test_claim_relative_ladder(decls, node_map, graph, sections):
    """`strength_of` must be a function of (route, **claim**), and the claim must
    actually reach it.

    Threading the claim through the ladder is a **no-op on the current artifact**,
    and that is the trap: on all 32 routed `CLASSICAL_ATTRIBUTES` rows the winning
    route *is* the claim declaration, so every assertion about the resulting
    badges passes identically whether the claim is threaded or ignored. A census
    cannot tell the two implementations apart. These assertions can.
    """
    import dataclasses

    build_boundary_by_decl(sections, decls)
    bd._COMPILED_BY_FULL.clear()
    bd._CTX["compiled"] = {}

    ONE_GROUND = "Logos.FoundationalUnicity.exactly_one_universal_modal_ground"
    COUNTER = "Logos.FoundationalUnicity.unicity_does_not_force_unitarian_monad"

    # (1) The same route, two claims: flipping ONLY the claim's polarity flips the
    #     class. If `claim` were ignored, both calls would agree and this fails.
    pr = bd.compiled_proof(ONE_GROUND)
    assert pr is not None, f"{ONE_GROUND} is not compiled"
    own = bd.claim_shape_of(ONE_GROUND, premises=bd.route_premises(pr))
    as_sep = dataclasses.replace(own, polarity="separation")
    assert own.polarity == "positive", (
        f"expected the one-ground claim to audit as positive, got {own.polarity!r}")
    assert bd.strength_of(pr, own) == "PROVEN"
    assert bd.strength_of(pr, as_sep) == "COUNTERMODEL", (
        "strength_of ignored the claim: a free route to a separation-claim read as "
        "the same class it takes for a positive claim")
    print("  ✓ strength_of is claim-relative: one route, two claims, two classes.")

    # (2) Both separation channels are load-bearing, and each is asserted on a
    #     declaration where the OTHER channel alone would answer wrongly. C212
    #     concludes a *positive* ∃ and is a countermodel only by GAPMAP's register;
    #     pantheism's claim is a separation by audited polarity and is not in the
    #     boundary register.
    cp = bd.compiled_proof(COUNTER)
    assert cp is not None, f"{COUNTER} is not compiled"
    counter_claim = bd.claim_shape_of(COUNTER, premises=bd.route_premises(cp))
    assert bd._shape_polarity(cp) == "positive"
    assert bd.claim_is_separation(counter_claim) is True, (
        "C212 must be a separation via GAPMAP's register even though its goal audits "
        "as positive — the polarity channel alone would make Strict monotheism read "
        "as PROVEN")
    assert bd.strength_of(cp, counter_claim) == "COUNTERMODEL"

    PANTHEISM = "Logos.CosmicExistence.the_ground_is_not_the_universe"
    pp = bd.compiled_proof(PANTHEISM)
    assert pp is not None, f"{PANTHEISM} is not compiled"
    pant = bd.claim_shape_of(PANTHEISM, premises=bd.route_premises(pp))
    assert pant.polarity == "separation"
    assert PANTHEISM not in bd.boundary_by_decl(), (
        "the pantheism claim is expected NOT to be in the boundary register; if it "
        "now is, this test no longer isolates the polarity channel")
    assert bd.claim_is_separation(pant) is True
    print("  ✓ Both separation channels asserted on the declaration that needs them.")

    # (3) A terminator with no claim to refute must fail the build, not be badged.
    #     A route that merely *proves* something has no terminator, so the guard
    #     cannot be exercised with it — it takes a `⊥`-concluding theorem.
    refuter = None
    for full, rec in bd.load_goal_audit().items():
        if full.startswith("Logos.") and (rec.get("goal") or "").strip() == "False":
            cand = bd.compiled_proof(full)
            if cand is not None and bd.refutation_kind(cand) in bd._REFUTATION_KINDS:
                refuter, refuter_full = cand, full
                break
    assert refuter is not None, (
        "no Logos declaration with a `False` goal was compiled — the refutation "
        "guard cannot be exercised on this artifact")
    print(f"  ✓ refutation guard exercised on {refuter_full.rsplit('.', 1)[-1]}")
    stale_claim = dataclasses.replace(
        own, conjuncts=tuple(
            dataclasses.replace(c, head="SomeOtherHead")
            for c in own.conjuncts))
    assert bd._relation_of(refuter, stale_claim) == INCOMPARABLE, (
        "the guard's precondition does not hold: the refuter is not INCOMPARABLE "
        "to the substituted claim, so this scenario tests nothing")
    try:
        bd.strength_of(refuter, stale_claim)
    except SystemExit as e:
        assert INCOMPARABLE in str(e), f"failed for the wrong reason: {e}"
    else:
        raise AssertionError(
            "strength_of accepted a `⊥` route that is INCOMPARABLE to the named "
            "claim; the refutation guard does not fire")
    print("  ✓ A terminator that bears on no named claim fails the build.")


def test_select_slot_route(decls, node_map):
    # Assertion: no multi-claim slot in CLASSICAL_ATTRIBUTES
    multi = [r.get("attribute") for r in bd.CLASSICAL_ATTRIBUTES if r.get("claims") or r.get("subclaims")]
    assert len(multi) == 0, f"unexpected multi-claim rows: {multi}"

    # Test select_slot_route logic
    p_free = bd.compiled_proof("Logos.IndubitableNormativeFreeWill.indubitable_normative_free_will")
    claim = bd.claim_shape_of("Logos.IndubitableNormativeFreeWill.indubitable_normative_free_will", premises=bd.route_premises(p_free))

    # All conjunct routes PROVEN -> PROVEN
    weak_cls, tier = bd.select_slot_route(claim, [[p_free], [p_free]], node_map=node_map)
    assert weak_cls == "PROVEN", f"expected PROVEN, got {weak_cls}"

    # One conjunct route missing -> OPEN
    weak_cls2, tier2 = bd.select_slot_route(claim, [[p_free], []], node_map=node_map)
    assert weak_cls2 == "OPEN", f"expected OPEN, got {weak_cls2}"
    assert len(tier2) == 0
    print("  ✓ select_slot_route (Level 2) verified; no multi-claim slot in CLASSICAL_ATTRIBUTES asserted.")


def main():
    decls = parse_lean_sources()
    sections = parse_gapmap()
    all_claims = [c for s in sections for c in s["claims"]]
    graph = load_depgraph()
    node_map = graph["node_map"]
    
    bd._AUDIT = load_audit()
    bd._REGISTRY = bd.load_axiom_registry(decls, node_map)
    
    _CTX.update({
        "decls": decls, "node_map": node_map, "graph": graph,
        "ax_id": dict(AX_ID), "ax_shown": set(), "axiom_full": axiom_full_map(node_map),
        "claims_by_id": {}, "by_full": {}, "by_id": {c["id"]: c for c in all_claims},
        "glosses": {}, "countermodels": {}, "seen": {}, "reading_rank": {}, "cm_seen": set()
    })
    
    from scripts.build_deduction import resolve
    for s in sections:
        for c in s["claims"]:
            ref = c.get("lean_ref") or ""
            r = resolve(ref, decls, node_map, c.get("level_key", ""))
            if r is None and "." not in ref:
                matches = [f for f in decls if f.rsplit(".", 1)[-1] == ref]
                if len(matches) == 1:
                    r = matches[0]
            c["_full"] = r
            
    test_genericity()
    test_minimal_assumption_dominance()
    test_provenance(decls, node_map, graph)
    test_sensitivity(decls, node_map, graph, sections)
    test_select_slot_route(decls, node_map)
    test_classifier_agreement(decls, node_map, graph, sections)
    test_claim_relative_ladder(decls, node_map, graph, sections)
    print("\nALL GENERITY, PROVENANCE, AND SENSITIVITY TESTS PASSED SUCCESSFULLY! (0 errors)")


if __name__ == "__main__":
    main()
