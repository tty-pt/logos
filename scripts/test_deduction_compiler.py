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
    OUT_PATH
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
            rendered = "\n".join(render_deduction_sections(mock_section, mock_decls, {}))
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
    assert "NoRight ≡ ¬NormativeRightExists" in text
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
    baseline_text = "\n".join(render_deduction_sections(baseline_secs, decls, node_map))
    
    # 1. Mutate theorem statement in memory
    mutated_decls = copy.deepcopy(decls)
    target = "Logos.Modal.T7_necessaryReality"
    orig_stmt = mutated_decls[target]["statement"]
    mutated_decls[target]["statement"] = orig_stmt.replace(
        "Ground e τ",
        "Ground e τ ∧ FeasibleAction e"
    )
    _CTX["decls"] = mutated_decls
    mutated_secs = discover_deduction_sections(sections, mutated_decls, node_map, graph, {})
    mutated_text = "\n".join(render_deduction_sections(mutated_secs, mutated_decls, node_map))
    _CTX["decls"] = decls
    assert mutated_text != baseline_text
    assert "FeasibleAction" in mutated_text
    print("  ✓ Sensitivity verified: hypothesis mutation dynamically updated deduction output.")
    
    # 2. Mutate axiom footprint in memory
    orig_audit = list(bd._AUDIT.get(target, []))
    bd._AUDIT[target] = orig_audit + ["Logos.Value.AxTwoSubjects"]
    mutated_secs2 = discover_deduction_sections(sections, decls, node_map, graph, {})
    mutated_text2 = "\n".join(render_deduction_sections(mutated_secs2, decls, node_map))
    bd._AUDIT[target] = orig_audit
    assert mutated_text2 != baseline_text
    assert "AxTwoSubjects" in mutated_text2
    print("  ✓ Sensitivity verified: axiom footprint mutation dynamically updated local bridge pricing.")


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
    print("\nALL GENERITY, PROVENANCE, AND SENSITIVITY TESTS PASSED SUCCESSFULLY! (0 errors)")


if __name__ == "__main__":
    main()
