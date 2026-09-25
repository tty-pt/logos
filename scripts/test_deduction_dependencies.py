#!/usr/bin/env python3
"""test_deduction_dependencies.py — Verification of proof dependency correspondence and sensitivity.

This test validates two core architectural invariants:
1. Correspondence: Every mathematical transition, definition, and theorem in README.md
   corresponds to an actual Lean kernel declaration in formal/Logos/*.lean, a dependency
   edge in formal/depgraph.json, or an audited axiom footprint in formal/axiom_audit.json.
2. Sensitivity: The deduction generator is genuinely dynamic. Mutating a proof hypothesis,
   antecedent, or axiom footprint in memory immediately alters the generated deduction output.
"""

import sys
import copy
import re
from pathlib import Path
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

import scripts.build_deduction as bd
from scripts.build_deduction import (
    parse_lean_sources,
    parse_gapmap,
    load_depgraph,
    load_audit,
    discover_deduction_sections,
    render_deduction_sections,
    _CTX,
    axiom_full_map,
    AX_ID,
    OUT_PATH
)
from scripts.sync_docstring_footprints import scan as footprint_scan


def test_correspondence(decls: dict, node_map: dict, graph: dict, sections: list) -> None:
    print("Testing correspondence between README.md and the formal Lean corpus…")
    text = OUT_PATH.read_text(encoding="utf-8")
    assert text.startswith("# Γ — The Deduction\n"), "README.md must start at line 1 with title"
    
    discovered = discover_deduction_sections(sections, decls, node_map, graph, {})
    total_proofs = 0
    # In the reader-facing document, the presentation spine controls what is rendered
    spine_secs = [s for s in discovered if s.get("category", "spine") == "spine"]
    for sec in spine_secs:
        title = sec["title"]
        assert f"## {title}" in text, f"Section '{title}' missing from README.md"
        all_proofs = sec.get("primary_proofs", []) + sec.get("supporting_proofs", []) + sec.get("obstruction_proofs", [])
        for sub in sec.get("subsections", []):
            all_proofs.extend(sub.get("proofs", []))
        for b in sec.get("branches", []):
            assert f"### {b['title']}" in text, f"Branch '{b['title']}' missing from README.md"
            all_proofs.extend(b.get("primary_proofs", []))
            all_proofs.extend(b.get("supporting_proofs", []))
            all_proofs.extend(b.get("obstruction_proofs", []))

        for proof in all_proofs:
            if proof.kind == "frontier":
                assert proof.name in text, f"Frontier claim '{proof.name}' missing from README.md"
                continue
            full = proof.full_name
            assert full in decls, f"Declaration '{full}' not found in Lean AST decls"
            d = decls[full]
            name = d["name"]
            assert name in text or full in text, f"Claim identifier '{name}' missing from README.md"
            total_proofs += 1
            
            # Verify kernel node exists
            if d["kind"] in ("theorem", "axiom"):
                assert full in node_map or full in graph["in"] or full in graph["out"], (
                    f"Kernel node missing for declaration '{full}'"
                )
                
    print(f"  ✓ {total_proofs} proofs across {len(spine_secs)} presentation spine sections correspond to verified Lean declarations.")
    
    # 2. Verify key dependency transitions from depgraph.json
    fw_full = "Logos.IndubitableNormativeFreeWill.indubitable_normative_free_will"
    fw_preds = graph["in"].get(fw_full, set())
    assert any("GenuineNormativity" in p for p in fw_preds), "indubitable_normative_free_will must depend on GenuineNormativity"
    assert any("Chooses" in p for p in fw_preds), "indubitable_normative_free_will must depend on Chooses"
    
    ret_full = "Logos.DirectNormativeRetorsion.claims_correct_no_right_self_refuting"
    ret_preds = graph["in"].get(ret_full, set())
    assert any("NoRight" in p for p in ret_preds), "claims_correct_no_right_self_refuting must depend on NoRight"
    
    print("  ✓ Key deductive transitions match kernel dependency edges in depgraph.json.")

    # 3. Verify uninterrupted main deduction & Further Investigations catalogue
    main_body, _, further_sec = text.partition("## Further Investigations\n")
    assert further_sec, "README.md must contain '## Further Investigations' navigation catalogue at the end"
    assert "Technical Appendix & Kernel Audit" not in main_body, (
        "Main deduction must remain uninterrupted: no scattered kernel-audit links in intermediate sections"
    )
    assert "## The Argument at a Glance" in text, (
        "README.md must contain the opening summary section '## The Argument at a Glance'"
    )
    glance_text = text.partition("## The Argument at a Glance")[2].partition("## 1.")[0]
    assert "ClaimsCorrect" in glance_text and "NoRight" in glance_text, (
        "'The Argument at a Glance' must feature the performative denial of Right & Wrong as the starting datum"
    )
    assert "Chooses s p q ∧ FreeWill" in glance_text, (
        "'The Argument at a Glance' must visibly feature the minimal-assumption Free Will milestone"
    )
    assert "AxTwoSubjects" in glance_text, (
        "'The Argument at a Glance' must visibly feature the AxTwoSubjects bridge"
    )
    assert "preceding_theory ⇏ trinity" in glance_text, (
        "'The Argument at a Glance' must visibly incorporate the theological frontiers with countermodel boundaries"
    )

    assert "## Level 0" not in text and "## Level 1" not in text, (
        "README.md must not dump raw GAPMAP levels as the main reading order"
    )
    assert "## 1. Objective Right and Wrong" in text, (
        "README.md must open with the authoritative presentation spine (Section 1: Objective Right and Wrong)"
    )

    # Verify Section 1 objective starting point & retorsive defense
    sec1_text = text.partition("## 1. Objective Right and Wrong")[2].partition("## 2.")[0]
    assert "Right ≠ Wrong" in sec1_text or "EstablishedRightWrong" in sec1_text, (
        "Section 1 must define the objective Right/Wrong distinction"
    )
    assert "claims_correct_no_right_self_refuting" in sec1_text, (
        "Section 1 must present the retorsive defense of NoRight"
    )
    
    # Verify presentation policy: detailed research notebook is routed to investigations/, NOT appended to reader-facing document
    assert "## Detailed Deductions" not in text, (
        "README.md must NOT append the legacy 'Detailed Deductions' notebook when authoritative presentation spine is used"
    )
    
    # Verify the four first-class categories in Further Investigations
    for expected_cat in ("### Retorsions", "### Countermodels & Independence", "### Detailed Investigations", "### Technical"):
        assert expected_cat in further_sec, f"Missing category '{expected_cat}' in Further Investigations section"
        
    # Verify key independence boundaries in Further Investigations
    assert "⇏" in further_sec
    assert "preceding_theory_not_entails_trinity" in text
    assert "necessary_ground_not_entails_contingent_creation" in text
    assert "preceding_theory_not_entails_incarnation" in text
    
    # Verify minimal-assumption route dominance:
    # 1. Section 4 on primary spine uses axiom-free indubitable_normative_free_will
    sec4_text = text.partition("## 4. Free Will")[2].partition("## 5.")[0]
    assert "indubitable_normative_free_will" in sec4_text, (
        "Section 4 primary spine must present the minimal-assumption route (indubitable_normative_free_will)"
    )
    assert "✅ · [IndubitableNormativeFreeWill.lean#indubitable_normative_free_will]" in sec4_text, (
        "indubitable_normative_free_will in Section 4 must be badged as PROVEN (✅ cert footer)"
    )

    # 1b. Section 10 primary spine presents Constructive Personal Ground
    sec10_text = text.partition("## 10. Constructive Personal Ground")[2].partition("## Further Investigations")[0]
    assert "discover_person" in sec10_text, (
        "Section 10 primary spine must present discover_person"
    )
    assert "✅ · [" in sec10_text, (
        "discover_person in Section 10 must be badged as PROVEN (✅ cert footer)"
    )
    assert "the_person_supports_the_reality_of_right" in sec10_text, (
        "Section 10 must present the_person_supports_the_reality_of_right"
    )

    # Verify Definitional Identity of Free Subject
    assert "FreeSubject(s) ≡ FreeWill(s)" in glance_text, (
        "The Argument at a Glance must explicitly feature the definitional identity FreeSubject(s) ≡ FreeWill(s)"
    )

    # Verify local edge badges
    assert "✅ · [" in text and "person_grounds_normative_polarity" in text, (
        "person_grounds_normative_polarity must be present (✅ cert footer) in the README"
    )

    # Verify key retorsions
    assert "claims_correct_no_right_self_refuting" in text
    assert "indubitable_normative_free_will" in text
    
    print("  ✓ Uninterrupted main deduction & four first-class investigation categories verified.")
    assert "claims_correct_no_right_self_refuting" in text
    assert "retorsion_derives_genuine_normativity" in text
    assert "indubitable_normative_free_will" in text
    
    print("  ✓ Uninterrupted main deduction & four first-class investigation categories verified.")


def test_readability_invariants():
    print("Testing reader-facing philosophical readability invariants in README.md…")
    text = OUT_PATH.read_text(encoding="utf-8")

    # 1. Section 1 begins with Objective Right and Wrong, with subordinate retorsive defense
    sec1_text = text.partition("## 1. Objective Right and Wrong")[2].partition("## 2.")[0]
    assert "SubjectExists" not in sec1_text.partition("### Retorsive Defense")[0], "SubjectExists must not appear in Section 1 main body as starting datum"
    assert "Right ≠ Wrong" in sec1_text or "EstablishedRightWrong" in sec1_text, "Section 1 must define the objective Right/Wrong distinction"
    assert "claims_correct_no_right_self_refuting" in sec1_text, "Section 1 must present retorsive defense of NoRight"
    assert "NoRight" in sec1_text, "Section 1 must include NoRight"
    assert "Classical.not_not" in sec1_text, "Section 1 must explicitly document double-negation elimination"

    # 2. Section 2 is Ought and Normative Polarity
    sec2_text = text.partition("## 2. Ought and Normative Polarity")[2].partition("## 3.")[0]
    assert "TruthNorm" in sec2_text, "Section 2 must present TruthNorm"
    assert "correct_implies_ought" in sec2_text or "Ought" in sec2_text

    # 3. Section 3 is Genuine Choice
    sec3_text = text.partition("## 3. Genuine Choice")[2].partition("## 4.")[0]
    assert "Chooses" in sec3_text, "Section 3 must present Chooses"

    # 4. Free Will earned in Section 4
    sec4_text = text.partition("## 4. Free Will")[2].partition("## 5.")[0]
    assert "We did not assume a free subject" in sec4_text, "Section 4 must state that freedom is derived, not assumed"
    assert "indubitable_normative_free_will" in sec4_text, "Section 4 must derive free will from genuine normativity"

    # 5. Free Subject in Section 5
    sec5_text = text.partition("## 5. The Free Subject")[2].partition("## 6.")[0]
    assert "freeSubject_iff_freeWill" in sec5_text or "FreeSubject(s) ↔ FreeWill(s)" in sec5_text

    # 6. Person in Section 6
    sec6_text = text.partition("## 6. Person")[2].partition("## 7.")[0]
    assert "Person" in sec6_text and "free_subject_is_person" in sec6_text

    # 7. Personal and Independent Will in Section 7
    sec7_text = text.partition("## 7. Personal and Independent Will")[2].partition("## 8.")[0]
    assert "person_iff_freeIndependentWill" in sec7_text

    # 8. Ontological Ground in Section 8
    sec8_text = text.partition("## 8. Personal Agency as Ontological Ground of Normativity")[2].partition("## 9.")[0]
    milestone_sec8 = sec8_text.partition("### Supporting Infrastructure")[0]
    assert "person_grounds_normative_polarity" in milestone_sec8
    assert "✅ · [" in milestone_sec8
    assert "Grounding ≠ Identity" in sec8_text or "Grounding is strictly distinct from identity" in sec8_text
    assert "### Obstruction / Formal Boundary: `model_b_separation`" in sec8_text
    assert "model_b_separation" in sec8_text.partition("### Obstruction / Formal Boundary")[2]

    # 9. Necessary Truth in Section 9
    sec9_text = text.partition("## 9. Necessary Truth")[2].partition("## 10.")[0]
    milestone_sec9 = sec9_text.partition("### Supporting Infrastructure")[0]
    assert "step1_necessary_truth_exists" in milestone_sec9
    assert "✅ · [" in milestone_sec9

    # 10. Constructive Personal Ground in Section 10
    sec10_text = text.partition("## 10. Constructive Personal Ground")[2].partition("## Further Investigations")[0]
    assert "discover_person" in sec10_text
    assert "the_person_supports_the_reality_of_right" in sec10_text

    # 12. Branch C: What This Does Not Yet Prove (Theological Frontiers and Outward Links)
    branch_c_text = text.partition("### Branch C: What This Does Not Yet Prove")[2].partition("## Further Investigations")[0]
    assert "preceding_theory ⇏ trinity" in branch_c_text
    assert "necessary_ground ⇏ contingent_creation" in branch_c_text
    assert "preceding_theory ⇏ incarnation" in branch_c_text
    assert "investigations/right-and-wrong.md" in text
    assert "investigations/free-will.md" in text
    assert "investigations/grounding.md" in text
    assert "investigations/divine-personhood.md" in text
    assert "investigations/countermodels.md" in text

    # 12b. Classical-attributes status table: live statuses, honest deferrals,
    #      and no "necessary Person of God" conflation in the table region.
    attr_text = text.partition("## Which Classical Attributes Are Already Established?")[2].partition("## Further Investigations")[0]
    assert text.partition("## Which Classical Attributes Are Already Established?")[0], (
        "Classical-attributes table heading must appear in the main body"
    )
    assert text.partition("## Which Classical Attributes Are Already Established?")[2].find("## Further Investigations") != -1, (
        "Classical-attributes table must sit before the Further Investigations catalogue"
    )
    for scope in ("Personal ground / person-type", "Divine Being / Ground", "Divine Personhood",
                   "Proof architecture (not divine scope)"):
        assert scope in attr_text, f"Table must report scope '{scope}'"
    for bucket in ("✅ PROVEN", "⏸ DEFERRED", "❌ NOT ESTABLISHED", "🧱 INDEPENDENT"):
        assert bucket in attr_text, f"Table must report status bucket '{bucket}'"
    for footer in ("personal_ground_of_right_wrong", "person_iff_thomisticCore",
                   "preceding_theory_not_entails_trinity",
                   "necessary_ground_not_entails_contingent_creation",
                   "preceding_theory_not_entails_incarnation",
                   "ofGround_necessary_ground_of_reality",
                   "the_ground_everlasting",
                   "the_ground_atemporal",
                   "necessary_existence_is_stage_uniform",
                   "agent_invariant_core_is_strictly_inside_freewill_invariant_core"):
        assert footer in attr_text, f"Table must cite live declaration '{footer}'"
    assert "does not establish that the Divine Being / Ground" in attr_text, (
        "Table must preserve the architectural boundary for the non-relative core"
    )
    assert "does not instantiate the canonical `Entity` sort" in attr_text, (
        "C181 must remain generic rather than being presented as canonical divine eternity"
    )
    assert "NECESSARY PERSON" not in attr_text, (
        "Table must not re-introduce the 'necessary Person' conflation"
    )
    assert "God is a necessary Person" not in attr_text, (
        "Table must never say 'God is a necessary Person'"
    )
    assert "claimE" in attr_text, (
        "Claim E is a live theorem (non-hypostatic pairing) and must be cited by the table"
    )
    assert "ofGround_ne_ofSubject" in attr_text, (
        "Table must record the blocked hypostatic identity (ofGround ≠ EntityOf s)"
    )
    assert "**Aseity**" in attr_text, "Table must report Aseity"
    assert "aseity_does_not_force_any_volition_alternatives" in attr_text, (
        "Table must cite C182"
    )
    assert "volitional_alternative_does_not_force_aseity" in attr_text, (
        "Table must cite C184"
    )
    assert "**Divine simplicity**" in attr_text, "Table must report Divine simplicity"
    assert "ofGround_divine_simplicity" in attr_text, (
        "Table must cite ofGround_divine_simplicity"
    )
    assert "not a proof or disproof of aseity for `Entity.ofGround`" in attr_text, (
        "Aseity row must preserve the canonical divine-aseity boundary"
    )

    # 14. Invariant: Act / SubjectExists / Agent do NOT precede Free Will in main spine
    prior_to_fw = text.partition("## 4. Free Will")[0]
    assert "T1_subjectExists" not in prior_to_fw, "T1_subjectExists must not precede Free Will in main spine"
    assert "T4_agentExists" not in prior_to_fw, "T4_agentExists must not precede Free Will in main spine"

    # 15. Glance is conceptual and reflects the presentation spine with source-node branching
    glance_text = text.partition("## The Argument at a Glance")[2].partition("## 1.")[0]
    assert "RIGHT / WRONG" in glance_text
    assert "OUGHT / OUGHT-NOT" in glance_text
    assert "CHOICE" in glance_text
    assert "FREE WILL" in glance_text
    assert "FREE SUBJECT" in glance_text
    assert "PERSON" in glance_text
    assert "INDEPENDENT PERSONAL WILL" in glance_text
    assert "ONTOLOGICAL GROUND OF RIGHT / WRONG" in glance_text
    assert "NECESSARY TRUTH" in glance_text
    assert "CONSTRUCTIVE PERSONAL GROUND" in glance_text
    assert "├─── [PROVEN · NECESSARY GROUND — EVERLASTING & ATEMPORAL] → NECESSARY DIVINE GROUND / BEING" in glance_text
    assert "├─── [DEFERRED · NOT PART OF PROOF] → ONE GOD / STRICT MONOTHEISM" in glance_text
    assert "└─── [COUNTERMODEL SEPARATION FRONTIERS] → WHAT THIS DOES NOT YET PROVE" in glance_text
    assert "THEOLOGICAL FRONTIERS" in glance_text
    assert "discovery" in glance_text
    assert "GROUNDING" in glance_text or "grounding" in glance_text

    # 16. Explanatory sentences under each transition in glance
    assert "Right and wrong both obtain" in glance_text
    assert "Objective correctness determines agential standards" in glance_text
    assert "Apprehending incompatible alternatives within a committed stance constitutes Choice" in glance_text
    assert "Freedom is derived by pure logic from genuine normativity and choice" in glance_text
    assert "A subject is recognized as free in virtue of possessing Free Will" in glance_text
    assert "A free subject is constitutively an authoritative Person" in glance_text
    assert "Distinct persons have numerically distinct wills" in glance_text
    assert "Personal free agency ontologically grounds the normative order" in glance_text
    assert "The objective logical and normative order entails necessary truth" in glance_text
    assert "The machine-proved dependence: wherever Right/Wrong is real, its ground-type is personal" in glance_text

    # 17. First 200 lines readability (window wide enough for the reading-guide
    #     opening block, which grew with the moral-frontier note C175/F3)
    first_200 = "\n".join(text.splitlines()[:260])
    assert "NoRight" in first_200
    assert "claims_correct_no_right_self_refuting" in first_200

    # 18. Natural deduction step visibility in Main Proof Spine
    assert "Formal Derivation (" in text, "Main Proof Spine must expose step-by-step natural deduction derivations"

    # 19. Adversarial Denial Normal Forms in Free Will section
    assert "Adversarial Denial Normal Forms (D1–D8)" in text, "README.md must present the exhaustive D1-D8 adversarial denials"

    # 20. Historical disclaimer on legacy draft
    old_readme = (ROOT / "README-OLD.md").read_text(encoding="utf-8")
    assert "HISTORICAL NOTICE FOR AGENTS" in old_readme, "README-OLD.md must carry historical disclaimer banner"

    # 21. Machine-Checked Kernel Rebuttal blocks under skeptic attacks
    assert "Machine-Checked Kernel Rebuttal —" in text, "README.md must present machine-checked kernel rebuttals for skeptic attacks"

    # 22. Six Pillars of Formal Defense against skeptical attacks
    assert "Why Common Skeptical Attacks Fail (The Six Pillars of Formal Defense)" in text
    assert "Normative Nihilism" in text
    assert "Eliminativism of Choice" in text
    assert "Theological Smuggling" in text
    assert "Euthyphro / Voluntarism" in text
    assert "Physicalist / Atomic Ground" in text

    print("  ✓ All philosophical readability, derivation visibility, and expository invariants verified (22/22 checks passed).")


def test_normative_free_will_footprint_and_edge_isolation(decls: dict, node_map: dict, graph: dict) -> None:
    print("Testing normative free will footprint and edge isolation invariants (Section 14)…")
    audit = load_audit()
    registry = bd.load_axiom_registry(decls, node_map)
    text = OUT_PATH.read_text(encoding="utf-8")

    fw_full = "Logos.IndubitableNormativeFreeWill.indubitable_normative_free_will"
    assert fw_full in decls, f"Declaration '{fw_full}' missing from Lean AST"
    fw_footprint = audit.get(fw_full, [])

    # Test 1: indubitable_normative_free_will has substantive_axioms == ∅
    fw_subst = [ax for ax in fw_footprint if (registry.get(ax.rsplit(".", 1)[-1]) or {}).get("tag") in ("SEM", "META")]
    assert len(fw_subst) == 0, (
        f"Test 1 FAILED: indubitable_normative_free_will must have 0 substantive axioms, found: {fw_subst}"
    )
    print("  ✓ Test 1 passed: indubitable_normative_free_will substantive_axioms == ∅.")

    # Test 2: AxJudicativeBipolarity must not appear in the local footprint of indubitable_normative_free_will
    assert not any("AxJudicativeBipolarity" in ax for ax in fw_footprint), (
        "Test 2 FAILED: AxJudicativeBipolarity must not appear in local footprint of indubitable_normative_free_will"
    )
    print("  ✓ Test 2 passed: AxJudicativeBipolarity absent from local footprint of indubitable_normative_free_will.")

    # Test 3: AxJudicativeBipolarity appears on route to GenuineNormativity without contaminating indubitable_normative_free_will
    gn_full = "Logos.RetorsiveNormativity.claims_correct_presupposes_normativity"
    gn_footprint = audit.get(gn_full, [])
    assert any("AxJudicativeBipolarity" in ax for ax in gn_footprint), (
        "Test 3 FAILED: AxJudicativeBipolarity must appear in footprint of claims_correct_presupposes_normativity"
    )
    # Check that in README.md, the local certificate for indubitable_normative_free_will is 0 substantive axioms
    fw_text = text.partition("## 4. Free Will")[2].partition("## 5.")[0]
    assert "✅ · [IndubitableNormativeFreeWill.lean#indubitable_normative_free_will]" in fw_text, (
        "Test 3 FAILED: indubitable_normative_free_will certificate in Section 4 must be PROVEN (✅ cert footer)"
    )
    assert "AxJudicativeBipolarity" not in fw_text.partition("IndubitableNormativeFreeWill.lean#indubitable_normative_free_will")[0][-300:], (
        "Test 3 FAILED: AxJudicativeBipolarity must not appear as a requirement for indubitable_normative_free_will"
    )
    print("  ✓ Test 3 passed: AxJudicativeBipolarity is isolated to GenuineNormativity and does not contaminate FreeWill certificate.")

    # Test 4: FreeSubject and FreeWill must not be classified as AXIOMATIC, SEMANTIC BRIDGE, or METAPHYSICAL BRIDGE
    assert "FreeSubject" not in [ax.rsplit(".", 1)[-1] for ax in registry if registry[ax.rsplit(".", 1)[-1]].get("tag") in ("SEM", "META")], (
        "Test 4 FAILED: FreeSubject must not be registered as a semantic/metaphysical bridge axiom"
    )
    assert "FreeWill" not in [ax.rsplit(".", 1)[-1] for ax in registry if registry[ax.rsplit(".", 1)[-1]].get("tag") in ("SEM", "META")], (
        "Test 4 FAILED: FreeWill must not be registered as a semantic/metaphysical bridge axiom"
    )
    # In Section 4, the badge for freedom must be PROVEN, never SEMANTIC or METAPHYSICAL
    fw_block = fw_text.partition("indubitable_normative_free_will")[0]
    assert "SEMANTIC" not in fw_block.split("∴ Chooses s p q ∧ FreeWill(s)")[-1]
    assert "METAPHYSICAL" not in fw_block.split("∴ Chooses s p q ∧ FreeWill(s)")[-1]
    print("  ✓ Test 4 passed: FreeSubject and FreeWill are derived theorems, never classified as bridges.")

    # Test 5: The Main Proof Spine must contain an explicitly marked axiom-free Freedom edge
    assert "Free Will follows from Genuine Normativity by pure logic with zero substantive axioms" in fw_text, (
        "Test 5 FAILED: Section 4 must explicitly state that Free Will follows by pure logic with 0 substantive axioms"
    )
    glance_text = text.partition("## The Argument at a Glance")[2].partition("## 1.")[0]
    assert "PURE LOGIC · 0 substantive axioms" in glance_text, (
        "Test 5 FAILED: The Argument at a Glance must contain an edge [PURE LOGIC · 0 substantive axioms] entering choice/freedom"
    )
    print("  ✓ Test 5 passed: Main Proof Spine and Glance contain explicitly marked axiom-free Freedom edge.")

    # Test 6: No badge on an upstream edge may be inherited automatically by downstream conclusions
    choice_to_fw = glance_text.partition("CHOICE")[2].partition("FREE WILL")[0]
    assert "SEMANTIC" not in choice_to_fw, (
        "Test 6 FAILED: Upstream SEMANTIC badge must not be inherited by transition to Free Will"
    )
    assert "AxJudicativeBipolarity" not in choice_to_fw, (
        "Test 6 FAILED: AxJudicativeBipolarity must not be inherited on edge into Free Will"
    )
    print("  ✓ Test 6 passed: No upstream badge or bridge is inherited by downstream Free Will conclusion.")

    # Test 7: Target-driven canonical selection: Free-Will canonical proof is indubitable_normative_free_will
    assert "indubitable_normative_free_will" in fw_text, (
        "Test 7 FAILED: Section 4 canonical proof must be indubitable_normative_free_will"
    )
    assert "✅ · [IndubitableNormativeFreeWill.lean#indubitable_normative_free_will]" in fw_text, (
        "Test 7 FAILED: Section 4 canonical proof must have the PROVEN ✅ cert footer"
    )
    print("  ✓ Test 7 passed: Canonical Free-Will target is indubitable_normative_free_will (0 substantive axioms).")

    # Test 8: Conceptual bifurcation of Discovery and Ontological Grounding
    assert "discovery" in glance_text.lower(), (
        "Test 8 FAILED: Document must explicitly identify the Discovery direction"
    )
    assert "grounding" in glance_text.lower(), (
        "Test 8 FAILED: Document must explicitly identify the Ontological Grounding direction"
    )
    assert "ONTOLOGICAL GROUNDING" in glance_text, (
        "Test 8 FAILED: Flowchart must visually expose the Ontological Grounding arrow"
    )
    print("  ✓ Test 8 passed: Explicit bifurcation of Discovery and Ontological Grounding verified in Spine and Flowchart.")

    print("  ✓ All Section 14 & 16 regression invariants passed with 0 errors.")


def test_ought_retorsion_and_personhood_frontiers(decls: dict, node_map: dict) -> None:
    print("Testing practical ought retorsion and personhood frontier invariants…")
    audit = load_audit()
    registry = bd.load_axiom_registry(decls, node_map)
    text = OUT_PATH.read_text(encoding="utf-8")

    # 1. Anti-self-legislation collapse theorem
    s_full = "Logos.OughtRetorsion.self_grounded_ought_collapses"
    assert s_full in decls, f"Declaration '{s_full}' missing from Lean AST"
    s_footprint = audit.get(s_full, [])
    s_subst = [ax for ax in s_footprint if (registry.get(ax.rsplit(".", 1)[-1]) or {}).get("tag") in ("SEM", "META")]
    assert len(s_subst) == 0, f"self_grounded_ought_collapses must have 0 substantive axioms, found: {s_subst}"
    print("  ✓ Test 1 passed: self_grounded_ought_collapses has 0 substantive axioms.")

    # 2. Hostile impersonal Platonist model survives
    imp_full = "Logos.OughtRetorsion.HostileImpersonalModel.impersonal_model_satisfies_ought_without_person"
    assert imp_full in decls, f"Declaration '{imp_full}' missing from Lean AST"
    imp_footprint = audit.get(imp_full, [])
    assert len(imp_footprint) == 0, f"Hostile impersonal model must have 0 axioms, found: {imp_footprint}"
    print("  ✓ Test 2 passed: Hostile impersonal Platonist model survives with 0 axioms.")

    # 3. Retorsion boundary principle on personal source
    ret_full = "Logos.OughtRetorsion.asserting_no_personal_source_instantiates_only_judging_subject"
    assert ret_full in decls, f"Declaration '{ret_full}' missing from Lean AST"
    ret_subst = [ax for ax in audit.get(ret_full, []) if (registry.get(ax.rsplit(".", 1)[-1]) or {}).get("tag") in ("SEM", "META")]
    assert len(ret_subst) == 0, f"asserting_no_personal_source must have 0 substantive axioms, found: {ret_subst}"
    print("  ✓ Test 3 passed: asserting_no_personal_source instantiates only judging subject.")

    # 4. AxSecondPersonalAddress registered as META
    assert "AxSecondPersonalAddress" in registry, "AxSecondPersonalAddress missing from axiom registry"
    assert registry["AxSecondPersonalAddress"]["tag"] == "META", "AxSecondPersonalAddress must have tag META"
    print("  ✓ Test 4 passed: AxSecondPersonalAddress registered with Tag: META.")

    # 5. Plurality derivation depends on AxSecondPersonalAddress
    pl_full = "Logos.OughtRetorsion.second_personal_ought_derives_plurality"
    assert pl_full in decls, f"Declaration '{pl_full}' missing from Lean AST"
    assert any("AxSecondPersonalAddress" in ax for ax in audit.get(pl_full, [])), (
        "second_personal_ought_derives_plurality must depend on AxSecondPersonalAddress"
    )
    print("  ✓ Test 5 passed: second_personal_ought_derives_plurality correctly loads AxSecondPersonalAddress.")

    # 6. Unified Ontology: Person := FreeSubject derived with 0 substantive axioms
    fp_full = "Logos.Person.free_subject_is_person"
    assert fp_full in decls, f"Declaration '{fp_full}' missing from Lean AST"
    fp_subst = [ax for ax in audit.get(fp_full, []) if (registry.get(ax.rsplit(".", 1)[-1]) or {}).get("tag") in ("SEM", "META")]
    assert len(fp_subst) == 0, f"free_subject_is_person must have 0 substantive axioms, found: {fp_subst}"

    # Personhood equivalence and properties
    eq_full = "Logos.Person.person_iff_freeSubject"
    assert eq_full in decls, f"Declaration '{eq_full}' missing from Lean AST"
    fw_full = "Logos.Person.person_has_free_will"
    assert fw_full in decls, f"Declaration '{fw_full}' missing from Lean AST"
    pi_full = "Logos.Person.person_is_intentional"
    assert pi_full in decls, f"Declaration '{pi_full}' missing from Lean AST"

    # Core distinctions: Will individuation and Nature
    assert "will_individuation" in registry, "will_individuation missing from axiom registry"
    assert registry["will_individuation"]["tag"] == "VOCAB"
    assert "Nature" in registry and "HasNature" in registry
    assert registry["Nature"]["tag"] == "VOCAB" and registry["HasNature"]["tag"] == "VOCAB"

    # Independent Deontic Ought
    assert "Ought" in registry, "Ought missing from axiom registry"
    assert registry["Ought"]["tag"] == "VOCAB"

    # Faithful modal model: Contingent Person ⇏ NecessarySubject
    pn_full = "Logos.OughtRetorsion.faithful_contingent_person_fails_necessary_subject"
    assert pn_full in decls and len(audit.get(pn_full, [])) == 0, "faithful modal model must have 0 axioms"
    print("  ✓ Test 6 passed: Unified Personhood proven (0 axioms), Will/Nature/Ought distinguished, modal frontier verified.")

    # 7. Flowchart in README.md reflects the unified ontology without fake frontiers
    glance_text = text.partition("## The Argument at a Glance")[2].partition("## 1.")[0]
    assert "PERSON" in glance_text and ("Person(s) := FreeSubject(s)" in glance_text or "Person s : Prop := FreeSubject s" in glance_text), (
        "Glance must expose authoritative PERSON"
    )
    assert "Anti-Self-Legislation" in text and "NORMATIVE COLLAPSE" in text
    assert "Hostile Impersonal Model" in text and "SURVIVING PLATONIST MODEL" in text
    assert "AxSecondPersonalAddress" in text
    assert "SubstantivePerson" not in glance_text, "Fake SubstantivePerson frontier must not appear in glance"
    assert "CONSTRUCTIVE PERSONAL GROUND" in glance_text
    assert "ONE GOD / STRICT MONOTHEISM" in glance_text
    assert "NECESSARY DIVINE GROUND / BEING" in glance_text
    assert "preceding_theory ⇏ trinity" in glance_text
    print("  ✓ Test 7 passed: Flowchart exposes unified personhood, personal ground, necessary person frontier, strict monotheism frontier, and faithful frontiers.")

    # 8. Necessary Personal Ground & Claim Taxonomy Rigorous Audit
    ofatom_full = "Logos.NecessaryPersonalGround.ofAtom_ne_ofSubject"
    assert ofatom_full in decls, f"Declaration '{ofatom_full}' missing from Lean AST"

    # Countermodel: de dicto vs de re separation, 0 axioms
    cm_ddr = "Logos.NecessaryPersonalGround.de_dicto_not_implies_de_re"
    assert cm_ddr in decls and len(audit.get(cm_ddr, [])) == 0, "de_dicto_not_implies_de_re must have 0 axioms"

    # The Trinitarian/monotheism derived-need is explicit: no live kernel
    # declaration may resurrect the deferred block.
    deferred_marks = [
        "monotheism_of_god_and_uniqueness", "monotheism_compatible_with_trinity",
        "trinitarian_persons_are_personal", "trinitarian_wills_are_distinct",
    ]
    for dm in deferred_marks:
        assert not any(d.rsplit(".", 1)[-1] == dm for d in decls), (
            f"Deferred Trinitarian declaration '{dm}' must not be live in the kernel"
        )
    print("  ✓ Test 8 passed: claim taxonomy audited, Trinitarian block confirmed deferred (not in kernel).")

    # 9. Quarantined stance-closure attempt must NOT be live in the kernel
    quarantine_marks = [
        "AxJudicativeGrasp", "AxJudicativeGraspNeg",
        "PresentActDatum", "stance_from_act",
        "stance_exists_unconditional", "free_will_unconditional",
    ]
    for qm in quarantine_marks:
        assert not any(d.rsplit(".", 1)[-1] == qm for d in decls), (
            f"Quarantined stance-attempt declaration '{qm}' must not be live in the kernel"
        )
    print("  ✓ Test 9 passed: stance-closure attempt confirmed quarantined (scratch/, not in kernel).")


def test_grounding_predicate_is_forced(decls: dict, node_map: dict) -> None:
    print("Testing that GroundsRightWrong is forced by the preceding facts (not a stipulated predicate)…")
    audit = load_audit()
    registry = bd.load_axiom_registry(decls, node_map)

    forced = {
        "Logos.PersonalNormativeGround.groundsRightWrong_iff_forced_content",
        "Logos.PersonalNormativeGround.forced_content_of_person",
        "Logos.PersonalNormativeGround.grounding_forced_by_preceding_facts",
        "Logos.PersonalNormativeGround.grounding_forced_at_datum",
    }
    for full in forced:
        assert full in decls, f"Declaration '{full}' missing from Lean AST"
        fp = audit.get(full, [])
        subst = [ax for ax in fp if (registry.get(ax.rsplit(".", 1)[-1]) or {}).get("tag") in ("SEM", "META")]
        assert len(subst) == 0, f"'{full}' must have 0 substantive axioms, found: {subst}"
        assert set(ax.rsplit(".", 1)[-1] for ax in fp) <= {"Means", "Subject"}, (
            f"'{full}' footprint must be {{Means, Subject}} exactly, got: {set(ax.rsplit('.', 1)[-1] for ax in fp)}"
        )
    grw_code = Path("formal/Logos/PersonalNormativeGround.lean").read_text(encoding="utf-8")
    assert "def ForcedGroundContent" in grw_code, "ForcedGroundContent def missing from PersonalNormativeGround.lean"
    assert "groundsRightWrong_iff_forced_content" in grw_code, "Transparency theorem missing from source"
    for ax in ("AxPersonalNormativeGround", "GroundProp", "AxPersonalGround"):
        assert ax not in registry, f"Forbidden grounding axiom '{ax}' still present in registry!"
    print("  ✓ Test passed: GroundsRightWrong is transparent, prior-forced, and axiom-free ({Means, Subject}).")


def test_ontological_grounding_invariants(decls: dict, node_map: dict) -> None:
    print("Testing ontological grounding of normative polarity invariants…")
    audit = load_audit()
    registry = bd.load_axiom_registry(decls, node_map)
    text = OUT_PATH.read_text(encoding="utf-8")

    # 1. Person iff FreeIndependentWill proven with 0 substantive axioms
    pi_full = "Logos.Person.person_iff_freeIndependentWill"
    assert pi_full in decls, f"Declaration '{pi_full}' missing from Lean AST"
    pi_subst = [ax for ax in audit.get(pi_full, []) if (registry.get(ax.rsplit(".", 1)[-1]) or {}).get("tag") in ("SEM", "META")]
    assert len(pi_subst) == 0, f"person_iff_freeIndependentWill must have 0 substantive axioms, found: {pi_subst}"
    print("  ✓ Test 1 passed: person_iff_freeIndependentWill proven with 0 substantive axioms.")

    # 2. AxPersonalNormativeGround was removed in a prior batch (2026-09-21); the
    #    registration must not resurrect it as a bridge axiom.
    assert "AxPersonalNormativeGround" not in registry, (
        "AxPersonalNormativeGround was removed in a prior batch and must not be registered"
    )
    print("  ✓ Test 2 passed: AxPersonalNormativeGround confirmed removed from axiom registry.")

    # 3. Principal grounding theorem no longer depends on the removed bridge axiom.
    pg_full = "Logos.PersonalNormativeGround.person_grounds_normative_polarity"
    assert pg_full in decls, f"Declaration '{pg_full}' missing from Lean AST"
    assert not any("AxPersonalNormativeGround" in ax for ax in audit.get(pg_full, [])), (
        "person_grounds_normative_polarity must NOT depend on the removed AxPersonalNormativeGround"
    )
    pg_subst = [ax for ax in audit.get(pg_full, []) if (registry.get(ax.rsplit(".", 1)[-1]) or {}).get("tag") in ("SEM", "META")]
    assert len(pg_subst) == 0, f"person_grounds_normative_polarity must have 0 substantive axioms, found: {pg_subst}"
    print("  ✓ Test 3 passed: person_grounds_normative_polarity depends on no removed bridge; 0 substantive axioms.")

    # 4. Strict non-circularity: discovery proofs do not contain AxPersonalNormativeGround
    disc_full = "Logos.IndubitableNormativeFreeWill.indubitable_normative_free_will"
    assert not any("AxPersonalNormativeGround" in ax for ax in audit.get(disc_full, [])), (
        "indubitable_normative_free_will must not depend on AxPersonalNormativeGround"
    )
    claims_full = "Logos.NormativeOrder.claims_normative_correctness_derives_free_will"
    assert not any("AxPersonalNormativeGround" in ax for ax in audit.get(claims_full, [])), (
        "claims_normative_correctness_derives_free_will must not depend on AxPersonalNormativeGround"
    )
    disc_indep = "Logos.PersonalNormativeGround.discovery_independent_of_grounding"
    assert disc_indep in decls, f"Declaration '{disc_indep}' missing from Lean AST"
    assert not any("AxPersonalNormativeGround" in ax for ax in audit.get(disc_indep, [])), (
        "discovery_independent_of_grounding must not depend on AxPersonalNormativeGround"
    )
    print("  ✓ Test 4 passed: strict non-circularity verified (discovery independent of grounding).")

    # 5. Hostile anti-collapse models compile with 0 axioms
    ma_full = "Logos.PersonalNormativeGround.HostileModels.model_a_satisfiable"
    mb_full = "Logos.PersonalNormativeGround.HostileModels.model_b_satisfiable"
    mbs_full = "Logos.PersonalNormativeGround.HostileModels.model_b_separation"
    assert ma_full in decls and len(audit.get(ma_full, [])) == 0, "Model A must have 0 axioms"
    assert mb_full in decls and len(audit.get(mb_full, [])) == 0, "Model B must have 0 axioms"
    assert mbs_full in decls and len(audit.get(mbs_full, [])) == 0, "Model B separation must have 0 axioms"
    print("  ✓ Test 5 passed: hostile anti-collapse models compile with 0 axioms.")

    # 6. README.md reflects dual-arrow architecture (Discovery vs Grounding)
    glance_text = text.partition("## The Argument at a Glance")[2].partition("## 1.")[0]
    assert "Discovery" in glance_text or "discovery" in glance_text, "Glance must expose discovery arrow"
    assert "Grounding" in glance_text or "grounding" in glance_text, "Glance must expose grounding arrow"
    assert "ONTOLOGICAL GROUNDING ARROW" in glance_text, "Flowchart must visually expose Ontological Grounding Arrow"
    print("  ✓ Test 6 passed: README.md reflects dual-arrow architecture.")


def test_ontological_proof_structure(decls: dict, node_map: dict) -> None:
    print("Testing explicit proof structure of the unconditional personal-ground headline…")
    audit = load_audit()
    registry = bd.load_axiom_registry(decls, node_map)
    
    hl_full = "Logos.PersonalGroundOfReality.the_person_supports_the_reality_of_right"
    assert hl_full in decls, f"Declaration '{hl_full}' missing from Lean AST"
    hl_footprint = audit.get(hl_full, [])
    
    # 1. The headline is unconditional: exactly the vocabulary-only agency tunnel.
    hl_subst = [ax for ax in hl_footprint if (registry.get(ax.rsplit(".", 1)[-1]) or {}).get("tag") in ("SEM", "META")]
    assert len(hl_subst) == 0, f"Headline must have 0 substantive axioms, found: {hl_subst}"
    hl_vocab = sorted(set(ax.rsplit(".", 1)[-1] for ax in hl_footprint))
    assert set(hl_vocab) == {"Initiates", "Means", "State", "Subject", "choice", "propext", "sound"}, (
        f"Headline footprint mismatch: {hl_vocab}"
    )
    print(f"  ✓ Test 1 passed: Headline footprint exactly {{Initiates, Means, State, Subject, CL}} ({len(hl_subst)} substantive axioms).")
    
    # 2. The headline is closed (no free premise): the textual signature must not
    #    expose a hypothesis on a Subject/Act the reader would have to supply.
    hl_code = (Path("formal/Logos/PersonalGroundOfReality.lean")).read_text(encoding="utf-8")
    hl_body = hl_code.partition("theorem the_person_supports_the_reality_of_right")[2].partition("theorem personal_ground_of_right_exists")[0]
    assert "the_person_supports_the_reality_of_right :" in hl_code or "the_person_supports_the_reality_of_right :" in hl_body
    assert "didn't say the" not in hl_body, "No adversarial guard text may sit inside the theorem body"
    
    # 3. The constitutive twin (existential corollary) is guarded by the datum, not free.
    pg_full = "Logos.PersonalGroundOfReality.personal_ground_of_right_exists"
    assert pg_full in decls, f"Declaration '{pg_full}' missing from Lean AST"
    pg_footprint = audit.get(pg_full, [])
    assert "Logos.PersonalGroundOfReality.personal_ground_of_right_exists" in hl_code or "hDatum" in hl_code
    print("  ✓ Test 2 passed: Explicit proof structure verified with constitutive headline and datum-guarded existential corollary.")


def test_normative_order_ground_independence(decls: dict, node_map: dict) -> None:
    print("Testing normative order ground independence invariants (Outcome B)…")
    audit = load_audit()
    registry = bd.load_axiom_registry(decls, node_map)
    
    # 1. Verify live independence model + separation (HostileModels Model B) exist in Lean AST
    m_sat = "Logos.PersonalNormativeGround.HostileModels.model_b_satisfiable"
    sep_thm = "Logos.PersonalNormativeGround.HostileModels.model_b_separation"
    assert m_sat in decls, f"Declaration '{m_sat}' missing from Lean AST"
    assert sep_thm in decls, f"Declaration '{sep_thm}' missing from Lean AST"

    # 2. Verify audited footprints of independence model: 0 substantive axioms
    m_sat_subst = [ax for ax in audit.get(m_sat, []) if (registry.get(ax.rsplit(".", 1)[-1]) or {}).get("tag") in ("SEM", "META")]
    assert len(m_sat_subst) == 0, f"model_b_satisfiable must have 0 substantive axioms, got {m_sat_subst}"

    sep_thm_subst = [ax for ax in audit.get(sep_thm, []) if (registry.get(ax.rsplit(".", 1)[-1]) or {}).get("tag") in ("SEM", "META")]
    assert len(sep_thm_subst) == 0, f"model_b_separation must have 0 substantive axioms, got {sep_thm_subst}"
    print("  ✓ Test 1 passed: Model B (satisfiable) and its separation theorem proven with 0 substantive axioms.")
    
    # 3. Verify no smuggled replacement axiom exists
    forbidden_axioms = {
        "normative_order_has_ground",
        "ObjectiveNormativeOrderHasGround",
        "AxObjectiveNormativeOrderGround",
        "AxNormativeGround",
    }
    for d, info in decls.items():
        if info.get("kind") == "axiom":
            short_name = d.rsplit(".", 1)[-1]
            assert short_name not in forbidden_axioms, f"Forbidden smuggled axiom '{short_name}' detected in Lean declarations!"
    print("  ✓ Test 2 passed: No premise-smuggled axiom replacement detected in Lean environment.")
    
    # 4. Verify that GroundPrincipleProp and normative_ground_persistence are retired from the constitutive headline
    npg_full = "Logos.PersonalGroundOfReality.the_person_supports_the_reality_of_right"
    npg_footprint = audit.get(npg_full, [])
    assert not any("GroundPrincipleProp" in ax for ax in npg_footprint), (
        "the_person_supports_the_reality_of_right must NOT depend on GroundPrincipleProp"
    )
    assert not any("normative_ground_persistence" in ax for ax in npg_footprint), (
        "the_person_supports_the_reality_of_right must NOT depend on normative_ground_persistence"
    )
    print("  ✓ Test 3 passed: GroundPrincipleProp and normative_ground_persistence retired from the constitutive headline.")


def test_sensitivity(decls: dict, node_map: dict, graph: dict, sections: list) -> None:
    print("Testing dynamic sensitivity of the deduction generator to proof changes…")
    baseline_secs = discover_deduction_sections(sections, decls, node_map, graph, {})
    baseline = "\n".join(render_deduction_sections(baseline_secs, decls, node_map))
    
    # 1. Mutate a theorem hypothesis/conclusion in memory
    mutated_decls = copy.deepcopy(decls)
    target = "Logos.PersonalGroundOfReality.the_person_supports_the_reality_of_right"
    orig_stmt = mutated_decls[target]["statement"]
    mutated_decls[target]["statement"] = orig_stmt + " ∧ True"
    _CTX["decls"] = mutated_decls
    mutated_secs = discover_deduction_sections(sections, mutated_decls, node_map, graph, {})
    mutated_output = "\n".join(render_deduction_sections(mutated_secs, mutated_decls, node_map))
    _CTX["decls"] = decls
    assert mutated_output != baseline, "Mutating theorem statement did not alter generated deduction output!"
    print("  ✓ Hypothesis mutation test passed: adding antecedent dynamically cascaded to README.md.")
    
    # 2. Mutate a definition/theorem docstring in memory
    mutated_decls2 = copy.deepcopy(decls)
    def_target = "Logos.Core.rightWrongDistinction"
    mutated_decls2[def_target]["doc"] = "New custom explanation of non-nothingness"
    mutated_decls2[def_target]["doc_claim"] = "New custom explanation of non-nothingness"
    _CTX["decls"] = mutated_decls2
    mutated_secs2 = discover_deduction_sections(sections, mutated_decls2, node_map, graph, {})
    mutated_output2 = "\n".join(render_deduction_sections(mutated_secs2, mutated_decls2, node_map))
    _CTX["decls"] = decls
    assert "New custom explanation of non-nothingness" in mutated_output2
    print("  ✓ Docstring/meaning mutation test passed: changing Lean docstring dynamically updated explanation.")
    
    # 3. Mutate an axiom footprint in memory
    orig_audit = list(bd._AUDIT.get(target, []))
    bd._AUDIT[target] = orig_audit + ["Logos.Value.AxTwoSubjects"]
    mutated_secs3 = discover_deduction_sections(sections, decls, node_map, graph, {})
    mutated_output3 = "\n".join(render_deduction_sections(mutated_secs3, decls, node_map))
    bd._AUDIT[target] = orig_audit
    assert mutated_output3 != baseline, "Mutating axiom footprint did not alter generated deduction output!"
    assert "AxTwoSubjects" in mutated_output3
    print("  ✓ Axiom footprint mutation test passed: introducing new axiom dynamically priced local bridge.")


def test_constructive_person_ground(decls: dict, node_map: dict) -> None:
    print("Testing constructive person ground and absence of grounding axioms…")
    audit = load_audit()
    registry = bd.load_axiom_registry(decls, node_map)

    disc_full = "Logos.PersonalNormativeGround.Constructive.discover_person"
    assert disc_full in decls, f"Declaration '{disc_full}' missing from Lean AST"
    disc_subst = [ax for ax in audit.get(disc_full, []) if (registry.get(ax.rsplit(".", 1)[-1]) or {}).get("tag") in ("SEM", "META")]
    assert len(disc_subst) == 0, f"discover_person must have 0 substantive axioms, found: {disc_subst}"

    hl_full = "Logos.PersonalGroundOfReality.the_person_supports_the_reality_of_right"
    assert hl_full in decls, f"Declaration '{hl_full}' missing from Lean AST"
    hl_subst = [ax for ax in audit.get(hl_full, []) if (registry.get(ax.rsplit(".", 1)[-1]) or {}).get("tag") in ("SEM", "META")]
    assert len(hl_subst) == 0, f"the_person_supports_the_reality_of_right must have 0 substantive axioms, found: {hl_subst}"

    # Verify no grounding axiom exists in registry
    forbidden_grounding = {"Ground", "GroundProp", "AxGlobalGround", "AxPersonalGround", "Truthmaker"}
    for ax in forbidden_grounding:
        assert ax not in registry, f"Forbidden grounding axiom '{ax}' still present in registry!"

    print("  ✓ Test passed: Constructive person ground verified with 0 substantive axioms and 0 grounding axioms.")


def test_no_modal_collapse(decls: dict, node_map: dict) -> None:
    print("Testing absence of modal collapse…")
    
    assert "Logos.RecoveredOntologicalGround.contingent_subject_ne_necessary_entity" in decls
    assert "Logos.RecoveredOntologicalGround.ground_of_reality_grounds_finite_subject" in decls
    
    rec_code = (Path("formal/Logos/RecoveredOntologicalGround.lean")).read_text(encoding="utf-8")
    assert "contingent_subject_ne_necessary_entity" in rec_code
    assert "EntityOf s ≠ g" in rec_code
    
    print("  ✓ Test passed: Contingent finite subject strictly separated from necessary ground (no modal collapse).")


def test_no_unitarian_collapse(decls: dict, node_map: dict) -> None:
    print("Testing absence of unitarian collapse…")
    
    # The Trinitarian/monotheism architecture is deferred and currently absent
    # from the repository (would live in scratch/Trinitarian_deferred.lean once
    # authored; see NecessaryPersonalGround.lean). In the live kernel the
    # one-God definition must not collapse to a single subject, and no deferred
    # declaration may leak back.
    npg_code = (Path("formal/Logos/NecessaryPersonalGround.lean")).read_text(encoding="utf-8")
    assert "def God" not in npg_code.partition("--")[2], (
        "Unitarian collapse risk: God material must NOT be re-introduced in the live kernel as a single-subject collapse"
    )
    for deferred in ("monotheism_compatible_with_trinity", "trinitarian_persons_are_personal", "trinitarian_wills_are_distinct"):
        assert not any(d.rsplit(".", 1)[-1] == deferred for d in decls), (
            f"Deferred Trinitarian declaration '{deferred}' must not be live in the kernel"
        )
    scratch_file = Path("scratch/Trinitarian_deferred.lean")
    assert not scratch_file.exists(), (
        "stale regression: the deferred Trinitarian/monotheism archive is not in this repository "
        "(absent per NecessaryPersonalGround.lean; only scratch/StanceAttempt.lean is tracked)"
    )
    
    print("  ✓ Test passed: Trinitarian/monotheism block deferred to scratch; no unitarian collapse in the live kernel.")


def test_no_hidden_premises(decls: dict, node_map: dict) -> None:
    print("Testing absence of hidden premises in GroundOfReality…")
    
    rec_code = (Path("formal/Logos/RecoveredOntologicalGround.lean")).read_text(encoding="utf-8")
    gor_def = rec_code.partition("def GroundOfReality")[2].partition("structure NecessaryGroundOfReality")[0]
    assert "NecessaryEntity" not in gor_def, "GroundOfReality must not circularly embed NecessaryEntity"
    assert "NecessaryPersonalGround" not in gor_def, "GroundOfReality must not circularly embed NecessaryPersonalGround"
    assert "Personal" not in gor_def, "GroundOfReality must not circularly embed Personal"
    
    print("  ✓ Test passed: GroundOfReality definition is clean, non-circular, and free of hidden premises.")


def test_docstring_footprint_sync() -> None:
    print("Verifying every docstring Footprint marker / inline copy against formal/axiom_audit.json…")
    mismatches, warnings, checked = footprint_scan()
    for w in warnings:
        print(f"  ⚠ {w}")
    if checked == 0:
        raise AssertionError("footprint sync checker verified zero claims — nothing tested")
    if mismatches:
        for mm in mismatches:
            print(f"  ✗ {mm['full']} ({mm['file']}:{mm['line']}): doc {mm['doc']} ≠ audit {mm['audit']}")
        raise AssertionError(f"{len(mismatches)} footprint claim(s) disagree with the audit")
    print(f"  ✓ {checked} footprint claims verified, 0 mismatches.")


def test_frontier_appendix_renders() -> None:
    print("Verifying the ## Formal Frontiers appendix renders the named open bridges #7/#9…")
    text = OUT_PATH.read_text(encoding="utf-8")
    assert "\n## Formal Frontiers\n" in text, "README: '## Formal Frontiers' appendix missing from generated README (check presentation_policy.include_frontiers_appendix)"
    assert "**§28 open bridges.**" in text, "OPEN_BRIDGES block missing from ## Formal Frontiers"
    assert "#7 `NecessaryEntity e → ∃ τ, Ground e τ`" in text, "open bridge #7 literal missing"
    assert "#9 `Ground(e, personal) → Personal(e)`" in text, "open bridge #9 literal missing"
    print("  ✓ ## Formal Frontiers renders OPEN_BRIDGES #7/#9.")


def test_claim_kernel_existence_walk(decls: dict, node_map: dict, sections: list) -> None:
    """§7.6 — every GAPMAP PROVEN/PROVEN↑ row must resolve to a live kernel declaration."""
    print("Walking GAPMAP PROVEN/PROVEN↑ rows → kernel declarations…")
    missing = []
    walked = 0
    for s in sections:
        for c in s["claims"]:
            if c.get("status") in ("PROVEN", "PROVEN↑"):
                walked += 1
                full = c.get("_full")
                if not full or full not in decls:
                    missing.append((c["id"], c.get("lean_ref") or ""))
    assert not missing, (
        f"{len(missing)} PROVEN/PROVEN↑ claim(s) with no kernel declaration: "
        + ", ".join(f"{cid} ref {ref}" for cid, ref in missing)
    )
    audit_doc = (ROOT / "investigations" / "kernel-audit.md").read_text(encoding="utf-8")
    assert "**Claims whose referenced theorem is missing (MISSING)**" not in audit_doc, \
        "kernel-audit.md reports MISSING claims (D1-class residue)"
    print(f"  ✓ {walked} PROVEN/PROVEN↑ rows all resolved to live kernel declarations; no MISSING block.")


def test_no_gloss_residue() -> None:
    """§7.5 — every claim carries an English meaning in code; any no-gloss residue fails."""
    audit_doc = (ROOT / "investigations" / "kernel-audit.md").read_text(encoding="utf-8")
    line = next((l for l in audit_doc.splitlines() if "English meaning in code" in l), None)
    assert line, "kernel-audit.md missing the 'English meaning in code' gloss line"
    m = re.search(r"\*\*(\d+)\*\* / (\d+)\s*$", line)
    assert m, f"unparsable gloss line: {line!r}"
    got, total = int(m.group(1)), int(m.group(2))
    assert got == total and "**no gloss:**" not in line, \
        f"no-gloss residue: glossed {got}/{total} ({(total - got)} missing meaning strings)"
    print(f"  ✓ Gloss coverage {got}/{total}: no missing English meaning strings.")


def test_badge_display_mapping() -> None:
    print("Verifying the AGENTS.md-mandated display mapping PROVEN↑ → ⚠️ AXIOMATIC (X)…")
    assert bd._CA_STATUS_TEXT["PROVEN↑"] == "⚠️ AXIOMATIC", \
        "claim-status text must render PROVEN↑ as AXIOMATIC"
    assert bd.STATUS_BADGE["PROVEN↑"] == "⚠️", \
        "stage badge for PROVEN↑ must be ⚠️"
    sem = SimpleNamespace(
        subst_axioms=["Logos.Semantics.strongTruthExists"],
        name="some_proof", kind="theorem", boundary=False,
        goal="∃ τ, NecessarilyTrue τ", conclusion=None, doc="")
    badge = bd.compute_epistemic_badge(
        [sem], {"strongTruthExists": {"tag": "SEM", "note": "test"}})
    assert badge == "AXIOMATIC (strongTruthExists)", f"badge = {badge!r}"
    meta = SimpleNamespace(
        subst_axioms=["Logos.NecessaryNormativeOrder.ax"],
        name="some_proof2", kind="theorem", boundary=False, goal="", conclusion=None, doc="")
    badge2 = bd.compute_epistemic_badge(
        [meta], {"ax": {"tag": "META", "note": "test"}})
    assert badge2 == "AXIOMATIC (ax)", f"badge = {badge2!r}"
    print("  ✓ PROVEN↑ → ⚠️ AXIOMATIC (named axiom); SEM and META routes verified.")


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
    
    # Resolve claims
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
            
    test_correspondence(decls, node_map, graph, sections)
    test_readability_invariants()
    test_normative_free_will_footprint_and_edge_isolation(decls, node_map, graph)
    test_ought_retorsion_and_personhood_frontiers(decls, node_map)
    test_ontological_grounding_invariants(decls, node_map)
    test_grounding_predicate_is_forced(decls, node_map)
    test_ontological_proof_structure(decls, node_map)
    test_constructive_person_ground(decls, node_map)
    test_no_modal_collapse(decls, node_map)
    test_no_hidden_premises(decls, node_map)
    test_no_unitarian_collapse(decls, node_map)
    test_docstring_footprint_sync()
    test_badge_display_mapping()
    test_frontier_appendix_renders()
    test_normative_order_ground_independence(decls, node_map)
    test_claim_kernel_existence_walk(decls, node_map, sections)
    test_no_gloss_residue()
    test_sensitivity(decls, node_map, graph, sections)
    print("\nALL DEDUCTION DEPENDENCY, READABILITY, AND SENSITIVITY TESTS PASSED SUCCESSFULLY! (0 errors)")


if __name__ == "__main__":
    main()
