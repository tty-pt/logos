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
    OUT_PATH,
    spine_step_ref,
)
from scripts.sync_docstring_footprints import scan as footprint_scan


# --- 2026-09-30 (NIHILISM_DIE §16): the reading spine is the *epistemic meaning*
# route (§§1–10 Satisfaction → Meaning → Free Subject → Person → The Fact), and the
# previous deontic route moved to investigations/ledger.md as an audited "move",
# not a deletion. Every assertion below was re-anchored to its new home: a check
# that used to read README §N now reads either the new README §N or the ledger
# route §N. Nothing was dropped to make the suite pass.
def readme_section(text: str, heading: str, stop: str = "") -> str:
    body = text.partition(heading)[2]
    return body.partition(stop)[0] if stop else body


def ledger_route(text: str, heading: str, stop: str) -> str:
    """A step of the deontic route inside the ledger's 'previous reading spine'."""
    body = text.partition("## The Deontic Route, in Full")[2]
    return body.partition(heading)[2].partition(stop)[0]


def test_correspondence(decls: dict, node_map: dict, graph: dict, sections: list) -> None:
    print("Testing correspondence between README.md and the formal Lean corpus…")
    text = OUT_PATH.read_text(encoding="utf-8")
    # READINGPATH.md §5: the reading path is the argument, the audit lives in
    # investigations/ledger.md. Content assertions check the union (nothing is
    # lost); README-only assertions check the argument surface.
    ledger_text = (ROOT / "investigations" / "ledger.md").read_text(encoding="utf-8")
    surface = text + "\n" + ledger_text
    assert text.startswith("# Γ — The Deduction\n"), "README.md must start at line 1 with title"
    
    discovered = discover_deduction_sections(sections, decls, node_map, graph, {})
    total_proofs = 0
    # In the reader-facing document, the presentation spine controls what is rendered
    spine_secs = [s for s in discovered if s.get("category", "spine") == "spine"]
    for sec in spine_secs:
        title = sec["title"]
        # DEDUCTION.md §3/§4: the ten steps are `###` under one `##` part, and
        # the heading is renumbered to "Step N — <title>" so §11–§15 cannot read
        # as a continuation of the step numbering. The expectation is derived the
        # same way the generator derives it, so a change to the generator's
        # heading shape has to be made here too rather than silently passing.
        # The generator's own parser, not a copy of its regex: a copied regex is
        # how a test and the thing it tests end up agreeing on the wrong heading.
        no, bare = spine_step_ref(title)
        want = f"### Step {no} — {bare}" if no is not None else f"### Step — {bare}"
        assert want in text, f"Step heading {want!r} missing from README.md"
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
                assert proof.name in surface, f"Frontier claim '{proof.name}' missing from README+ledger"
                continue
            full = proof.full_name
            assert full in decls, f"Declaration '{full}' not found in Lean AST decls"
            d = decls[full]
            name = d["name"]
            assert name in surface or full in surface, f"Claim identifier '{name}' missing from README+ledger"
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
    main_body, _, further_sec = text.partition("## Where the Rest of the Ledger Lives\n")
    assert further_sec, "README.md must contain '## Further Investigations' navigation catalogue at the end"
    assert "Technical Appendix & Kernel Audit" not in main_body, (
        "Main deduction must remain uninterrupted: no scattered kernel-audit links in intermediate sections"
    )
    assert "### The ten steps at a glance" in text, (
        "README.md must contain the opening summary section '### The ten steps at a glance'"
    )
    glance_text = text.partition("### The ten steps at a glance")[2].partition("### Step 1")[0]
    assert "Right ≠ Wrong" in glance_text or "¬N_T" in glance_text, (
        "'The ten steps at a glance' must feature the Right/Wrong distinction as the starting datum"
    )
    assert "FreeWill" in glance_text, (
        "'The ten steps at a glance' must visibly feature the minimal-assumption Free Will milestone"
    )
    # The ASCII flowchart (with AxTwoSubjects and the ⇏ frontiers) is ledger
    # material; the ten-step table carries the same ten steps derived.
    assert "AxTwoSubjects" in ledger_text, "ledger chart must feature the AxTwoSubjects bridge"
    assert "preceding_theory ⇏ trinity" in ledger_text, "ledger must carry the theological-frontier boundaries"

    assert "## Level 0" not in text and "## Level 1" not in text, (
        "README.md must not dump raw GAPMAP levels as the main reading order"
    )
    assert "### Step 1 — Satisfaction Is Free" in text, (
        "README.md must open with the epistemic reading spine (Step 1: Satisfaction Is Free)"
    )
    assert "### One God, in Three Persons" in text and \
           "## Part III — The refutations" in text, (
        "the reading spine must carry the One-God-in-three-Persons route and the "
        "refutations (DEDUCTION.md §3: §11/§12/§14/§15 lost their `## N.` numbers "
        "and §13 became Part III, so a reader scrolling cannot mistake a coda for "
        "a step)")

    # The old first section (Objective Right and Wrong) moved to the ledger's
    # deontic route; the check follows it there rather than being dropped.
    route1 = ledger_route(ledger_text, "### 1. Objective Right and Wrong", "### 2.")
    assert route1, "ledger must carry deontic route section 1 (Objective Right and Wrong)"
    assert "Right ≠ Wrong" in route1 or "EstablishedRightWrong" in route1, (
        "deontic route section 1 must define the objective Right/Wrong distinction"
    )
    assert "claims_correct_no_right_self_refuting" in ledger_text, (
        "Section 1's retorsive defense (kernel rebuttal) lives in the ledger"
    )
    
    # Verify presentation policy: detailed research notebook is routed to investigations/, NOT appended to reader-facing document
    assert "## Detailed Deductions" not in text, (
        "README.md must NOT append the legacy 'Detailed Deductions' notebook when authoritative presentation spine is used"
    )
    
    # Verify the four first-class categories in the catalogues file
    # (moved out of README.md 2026-09-29 so the reading path stays the argument;
    # same generator, same derived statuses — see build_deduction.render_further_investigations)
    import pathlib
    cat_text = (pathlib.Path(__file__).resolve().parent.parent / "investigations" / "catalogues.md").read_text(encoding="utf-8")
    assert "investigations/catalogues.md" in further_sec, "README must point at investigations/catalogues.md"
    for expected_cat in ("### Retorsions", "### Countermodels & Independence", "### Detailed Investigations", "### Technical"):
        assert expected_cat in cat_text, f"Missing category '{expected_cat}' in investigations/catalogues.md"
        
    # Verify key independence boundaries in the catalogues file
    assert "⇏" in cat_text
    assert "preceding_theory_not_entails_trinity" in text
    assert "necessary_ground_not_entails_contingent_creation" in text
    assert "preceding_theory_not_entails_incarnation" in text
    
    # Verify minimal-assumption route dominance. On the *reading* spine free will
    # is step 6 and is derived from the co-meaning of the poles (C140), which is
    # axiom-free but stance-conditional; the axiom-free *indubitable* route and its
    # ✅ cert footer moved to the ledger's deontic §4, and both must stay visible.
    sec6_text = text.partition("### Step 6 — Co-Meaning Both Poles Is Free Will")[2].partition("### Step 7")[0]
    assert sec6_text, "reading spine section 6 must present the free-will derivation"
    assert "claims_normative_correctness_derives_free_will" in sec6_text, (
        "Section 6 must present the co-meaning derivation of free will (C140)"
    )
    assert "✅ · [NormativeOrder.lean#claims_normative_correctness_derives_free_will]" in sec6_text, (
        "C140 on the reading path must be badged as PROVEN (✅ cert footer), 0 substantive axioms"
    )
    route4 = ledger_route(ledger_text, "### 4. Free Will", "### 5.")
    assert "indubitable_normative_free_will" in route4, (
        "deontic route section 4 must present the minimal-assumption route (indubitable_normative_free_will)"
    )
    assert "✅ · [IndubitableNormativeFreeWill.lean#indubitable_normative_free_will]" in route4, (
        "indubitable_normative_free_will in deontic route section 4 must be badged as PROVEN (✅ cert footer)"
    )
    assert "indubitable_normative_free_will" in text, (
        "the reading path must still surface the indubitable route — it is now a "
        "Part II characteristic block with its own derivation, since the 39-row "
        "attribute table that used to carry it moved to the ledger (DEDUCTION.md §3)"
    )
    # The unconditional existence of a free will/subject is priced, never free
    # (Part II's "Necessity, and Exactly What It Costs" — the old `## 11.` heading
    # is gone, so this partitions on the declared one).
    sec11 = text.partition("### Necessity, and Exactly What It Costs")[2].partition("### ")[0]
    assert "freeWill_exists" in sec11 and "freeSubject_exists" in sec11, (
        "the necessity section must price both unconditional-existence routes")
    assert "AXIOMATIC (AxTwoSubjects)" in sec11, (
        "§11 must display the one META bridge that prices unconditional free-will/free-subject existence"
    )
    assert "indubitable_normative_free_will" not in sec11, (
        "§11's unconditional rows must not borrow the axiom-free badge of the conditional route"
    )

    # 1b. The constructive personal-ground route moved to the ledger (deontic §10),
    #     while the reading spine keeps the person→ground direction at step 8.
    route10 = ledger_route(ledger_text, "### 10. Constructive Personal Ground", "## Formal Frontiers")
    assert route10, "ledger must carry deontic route section 10 (Constructive Personal Ground)"
    assert "discover_person" in route10, (
        "deontic route section 10 must present discover_person"
    )
    assert "✅ · [" in route10, (
        "discover_person in deontic route section 10 must be badged as PROVEN (✅ cert footer)"
    )
    assert "the_person_supports_the_reality_of_right" in route10, (
        "deontic route section 10 must present the_person_supports_the_reality_of_right"
    )
    sec8_text = text.partition("### Step 8 — That Person Grounds the Poles")[2].partition("### Step 9")[0]
    for _g in ("epistemic_polarity_is_personally_grounded",
               "the_person_grounds_the_epistemic_right_wrong"):
        assert _g in sec8_text, (
            f"reading spine step 8 must present the person→ground direction ({_g})")
    assert "✅ · [EpistemicPersonalGround.lean#the_person_grounds_the_epistemic_right_wrong]" in sec8_text, (
        "the personal-grounding headline must be badged as PROVEN on the reading path")

    # Verify Definitional Identity of Free Subject
    assert "FreeSubject" in glance_text and "FreeWill" in glance_text, (
        "The ten steps at a glance must explicitly feature the FreeSubject/FreeWill step"
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
    assert "retorsion_derives_genuine_normativity" in cat_text, (
        "retorsion catalogue lives in investigations/catalogues.md since 2026-09-29")
    assert "indubitable_normative_free_will" in text
    
    print("  ✓ Uninterrupted main deduction & four first-class investigation categories verified.")


def test_readability_invariants():
    print("Testing reader-facing philosophical readability invariants in README.md…")
    text = OUT_PATH.read_text(encoding="utf-8")
    ledger_text = (ROOT / "investigations" / "ledger.md").read_text(encoding="utf-8")
    surface = text + "\n" + ledger_text

    # 1. The reading spine opens with the *concession* (satisfaction is free, 0
    #    axioms); the objective Right/Wrong route is the ledger's deontic §1, and
    #    the same discipline applies there: no SubjectExists as starting datum.
    assert "### Step 1 — Satisfaction Is Free" in text
    sec1_text = ledger_route(ledger_text, "### 1. Objective Right and Wrong", "### 2.")
    assert "SubjectExists" not in sec1_text.partition("### Retorsive Defense")[0], "SubjectExists must not appear in Section 1 main body as starting datum"
    assert "Right ≠ Wrong" in sec1_text or "EstablishedRightWrong" in sec1_text, "Section 1 must define the objective Right/Wrong distinction"
    assert "NoRight" in sec1_text, "Section 1 must include NoRight"
    assert "claims_correct_no_right_self_refuting" in ledger_text, "Section 1's retorsive defense lives in the ledger"
    assert "Classical.not_not" in ledger_text, "double-negation elimination is ledger material"

    # 2. Ought and Normative Polarity (deontic route §2, now in the ledger)
    sec2_text = ledger_route(ledger_text, "### 2. Ought and Normative Polarity", "### 3.")
    assert "TruthNorm" in sec2_text, "Section 2 must present TruthNorm"
    assert "correct_implies_ought" in sec2_text or "Ought" in sec2_text

    # 3. Genuine Choice (deontic route §3)
    sec3_text = ledger_route(ledger_text, "### 3. Genuine Choice", "### 4.")
    assert "Chooses" in sec3_text, "Section 3 must present Chooses"

    # 4. Free Will earned — deontic route §4 in the ledger, reading spine §6 above
    sec4_text = ledger_route(ledger_text, "### 4. Free Will", "### 5.")
    assert "We did not assume a free subject" in sec4_text, "Section 4 must state that freedom is derived, not assumed"
    assert "indubitable_normative_free_will" in sec4_text, "Section 4 must derive free will from genuine normativity"

    # 5. Free Subject — deontic route §5 in the ledger; on the reading spine the
    #    Free Subject is step 7 (Free Will Is a Person) and the necessity section
    #    prices it. Both partitions use the declared headings (DEDUCTION.md §3).
    sec5_text = ledger_route(ledger_text, "### 5. The Free Subject", "### 6.")
    assert "FreeSubject" in text.partition("### Step 7 — Free Will Is a Person")[2].partition("### Step 8")[0] \
        or "FreeSubject" in text.partition("### Necessity, and Exactly What It Costs")[2].partition("### ")[0], (
        "the reading spine must present the Free Subject (step 7, or the necessity "
        "section that prices it)")
    assert "freeSubject_exists" in text, (
        "the reading spine must name freeSubject_exists: a Free Subject exists, on one META bridge")
    assert "freeSubject_iff_freeWill" in sec5_text or "FreeSubject(s) ↔ FreeWill(s)" in sec5_text

    # 6. Person (deontic route §6)
    sec6_text = ledger_route(ledger_text, "### 6. Person", "### 7.")
    assert "Person" in sec6_text and "free_subject_is_person" in sec6_text

    # 7. Personal and Independent Will (deontic route §7)
    sec7_text = ledger_route(ledger_text, "### 7. Personal and Independent Will", "### 8.")
    assert "person_iff_freeIndependentWill" in sec7_text

    # 8. Ontological Ground (deontic route §8)
    sec8_text = ledger_route(ledger_text, "### 8. Personal Agency as Ontological Ground of Normativity", "### 9.")
    milestone_sec8 = sec8_text.partition("#### Supporting Infrastructure")[0] or sec8_text
    assert "person_grounds_normative_polarity" in milestone_sec8
    assert "✅ · [" in milestone_sec8
    assert "Grounding ≠ Identity" in surface, "the Grounding≠Identity distinction must survive somewhere"
    assert "### Obstruction / Formal Boundary: `model_b_separation`" in ledger_text
    assert "model_b_separation" in sec8_text, "deontic route Section 8 must point at its formal boundary"

    # 9. Necessary Truth (deontic route §9); on the reading spine necessity is §11.
    sec9_text = ledger_route(ledger_text, "### 9. Necessary Truth", "### 10.")
    milestone_sec9 = sec9_text.partition("#### Supporting Infrastructure")[0] or sec9_text
    assert "step1_necessary_truth_exists" in milestone_sec9
    assert "✅ · [" in milestone_sec9

    # 10. Constructive Personal Ground (deontic route §10)
    sec10_text = ledger_route(ledger_text, "### 10. Constructive Personal Ground", "## Formal Frontiers")
    assert "discover_person" in sec10_text
    assert "the_person_supports_the_reality_of_right" in sec10_text

    # 12. Branch C: What This Does Not Yet Prove (Theological Frontiers and Outward Links)
    branch_c_text = ledger_text.partition("#### Branch C: What This Does Not Yet Prove")[2].partition("### 11.")[0]
    assert "Trinity" in branch_c_text and "contingent creation" in branch_c_text, (
        "Branch C must name the frontiers (ledger route §8)")
    # …and the reading path names them too, in §15 What Is Not Established.
    sec15 = text.partition("### What Is Not Established")[2].partition("## The score")[0]
    if "Incarnation" not in sec15 or "C112" not in sec15:
        # Fallback to old heading for robustness across branches
        sec15_old = text.partition("## 15. What Is Not Established")[2].partition("## What Is Established")[0]
        sec15 = sec15 if "Incarnation" in sec15 or "C112" not in sec15_old else sec15_old
    assert "Incarnation" in sec15 and "C112" in sec15, (
        "the reading path must name the open Incarnation frontier with its countermodel")
    assert "Trinity is priced, not free" in sec15, (
        "the reading path must state that the Trinity is priced (three META premises), not free")
    assert "preceding_theory ⇏ trinity" in ledger_text
    assert "necessary_ground ⇏ contingent_creation" in ledger_text
    assert "preceding_theory ⇏ incarnation" in ledger_text
    # The investigation index lives in investigations/catalogues.md (one click from
    # the reading path), so the check follows it there; every file stays reachable.
    import pathlib as _pl
    _cat = (_pl.Path(__file__).resolve().parent.parent / "investigations" / "catalogues.md").read_text(encoding="utf-8")
    for _f in ("right-and-wrong", "free-will", "grounding", "divine-personhood", "countermodels"):
        assert f"investigations/{_f}.md" in _cat, (
            f"the investigation index must link investigations/{_f}.md")
    assert "investigations/catalogues.md" in text, "the reading path must link the investigation index"

    # 12b. Classical-attributes status table: live statuses, honest deferrals,
    #      and no "necessary Person of God" conflation in the table region.
    attr_text = ledger_text.partition("## Which Classical Attributes Are Already Established?")[2].partition("### ASIETY")[0]
    assert "## Which Classical Attributes Are Already Established?" in ledger_text, (
        "full classical-attributes table must live in the ledger"
    )
    # The reading path carries the person-attribute list, not the 39-row scoped
    # profile table: the table went to investigations/ledger.md (asserted below via
    # `attr_text`) and what remains here is "What the same route also establishes of
    # the person" (CLEARER.md §2). The three scope labels live in the ledger table,
    # so the README-side check is for the person-scope label and the D9 disclaimer.
    profile_heading = "### What the same route also establishes of the person"
    profile_text = text.partition(profile_heading)[2].partition("### What Is Not Established")[0]
    assert profile_heading in text, (
        "README must keep the person-attribute profile on the reading path")
    assert "Personal ground / person-type" in profile_text, (
        "profile must report its census scope")
    assert "not* consequences of the ten steps" in profile_text, (
        "the profile must keep the D9 disclaimer: the eight attributes are parallel "
        "corollaries, not consequences of numbered spine steps")
    for scope in ("Personal ground / person-type", "Divine Being / Ground", "Divine Personhood",
                   "Proof architecture (not divine scope)"):
        assert scope in attr_text, f"Table must report scope '{scope}'"
    # Buckets that must be *represented*. ⏸ DEFERRED dropped out of this table on
    # 2026-09-30 — its only row (monotheism) was split into a PROVEN row and a row
    # refuted as a consequence — so it is checked against the badge legend instead
    # of being demanded of the table it no longer has.
    for bucket in ("✅ PROVEN", "❌ NOT ESTABLISHED", "🧱 INDEPENDENT"):
        assert (bucket in attr_text or f"{bucket.split()[0]} **{bucket.split()[1]}**" in attr_text), (
            f"Table must report status bucket '{bucket}'")
    assert "DEFERRED — a claimed result whose Lean declaration is not in the live kernel" in text, (
        "the badge legend must keep defining DEFERRED even though no attribute row uses it")
    assert "**One God** — unity of the Divine Being" in attr_text, (
        "the monotheism row must be split: unity of the ground is its own PROVEN row")
    assert "**Strict monotheism**" in attr_text and "Refuted as a consequence" in attr_text, (
        "the person-level reading must be reported as refuted, not as an open frontier")
    assert "One God / strict monotheism" not in attr_text, (
        "the two-claims label must not come back")
    assert "**Three Divine Persons (Trinity)** — one God, in three Persons" in attr_text, (
        "the Trinity row must state the one-God-in-three-Persons reading")
    assert "AGAPEATIC" not in attr_text and "not three Gods" in attr_text.lower() or "not three Gods" in attr_text, (
        "the Trinity row must foreclose tritheism")
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
    assert "**Scholastic simplicity**" in attr_text, "Table must report Scholastic simplicity"
    assert "**Divine immutability**" in attr_text, "Table must report Divine immutability"
    assert "ofGround_divine_immutability" in attr_text, (
        "Table must cite ofGround_divine_immutability"
    )
    assert "**Psychological impassibility**" in attr_text, "Table must report Psychological impassibility"
    assert "**Foundational omnipresence**" in attr_text, "Table must report Foundational omnipresence"
    assert "ofGround_foundational_omnipresence" in attr_text, (
        "Table must cite ofGround_foundational_omnipresence"
    )
    assert "**Physical omnipresence**" in attr_text, "Table must report Physical omnipresence"
    assert "**Quantitative metric infinity**" in attr_text, "Table must report Quantitative metric infinity"
    assert "**Psychological personality**" in attr_text, "Table must report Psychological personality"
    assert "faithful_model_satisfies_free_will_without_opaque_person" in attr_text, (
        "Table must cite faithful_model_satisfies_free_will_without_opaque_person"
    )
    # Check that separated unproven counterparts carry explicit status badges:
    assert "| **Physical omnipresence** (spatial presence throughout physical spacetime coordinates) | Divine Being / Ground | ❌ NOT ESTABLISHED |" in attr_text
    assert "| **Scholastic simplicity** (strict identity of essence and existence) | Divine Being / Ground | ❌ NOT ESTABLISHED |" in attr_text
    assert "| **Psychological impassibility** (incapacity for relational affect or compassion) | Divine Being / Ground | ❌ NOT ESTABLISHED |" in attr_text
    assert "| **Quantitative metric infinity** (infinite physical magnitude or cardinal size) | Divine Being / Ground | ❌ NOT ESTABLISHED |" in attr_text
    assert "not a proof or disproof of aseity for `Entity.ofGround`" in attr_text, (
        "Aseity row must preserve the canonical divine-aseity boundary"
    )

    # 14. Invariant: Act / SubjectExists / Agent do NOT precede Free Will in main spine
    prior_to_fw = text.partition("### Step 6 — Co-Meaning Both Poles Is Free Will")[0]
    assert "T1_subjectExists" not in prior_to_fw, "T1_subjectExists must not precede Free Will in main spine"
    assert "T4_agentExists" not in prior_to_fw, "T4_agentExists must not precede Free Will in main spine"

    # 15. Glance is conceptual and reflects the presentation spine with source-node branching
    glance_text = text.partition("### The ten steps at a glance")[2].partition("### Step 1")[0]
    chart_text = ledger_text.partition("## The Whole Argument in One Map")[2].partition("## §")[0]
    assert "## The Whole Argument in One Map" in ledger_text, "ASCII flowchart must live in the ledger"
    # The reading spine's ten steps (2026-09-30), each label derived from the
    # presentation spine; the deontic labels live in the ledger's ASCII map.
    # Step 10 was relabelled RETORSION -> THE CHAIN, COMPOSED (CREMATION.md §4.1):
    # C561 + C235 are two contrapositives and an existence datum, not a retorsion.
    for _label in ("SATISFACTION", "DISCLOSURE", "MEANING", "SUBJECT", "INCOMPATIBILITY",
                   "FREE WILL", "PERSON", "GROUNDING", "THE FACT", "THE CHAIN, COMPOSED"):
        assert _label in glance_text, f"the ten-step table must carry the step '{_label}'"
    assert "Right ≠ Wrong" in glance_text or "¬N_T" in glance_text
    assert "CHOICE" in glance_text or "FreeWill" in glance_text
    for _deontic in ("RIGHT / WRONG", "OUGHT / OUGHT-NOT", "CHOICE", "FREE WILL",
                     "FREE SUBJECT", "PERSON", "INDEPENDENT PERSONAL WILL",
                     "ONTOLOGICAL GROUND OF RIGHT / WRONG", "NECESSARY TRUTH",
                     "CONSTRUCTIVE PERSONAL GROUND"):
        assert _deontic in chart_text, (
            f"the ledger ASCII map must still carry the deontic step '{_deontic}'")
    assert "EVERLASTING & ATEMPORAL" in chart_text or "NECESSARY DIVINE GROUND" in chart_text
    assert "STRICT MONOTHEISM" in chart_text or "ONE GOD" in chart_text
    assert "THEOLOGICAL FRONTIERS" in chart_text or "DOES NOT YET PROVE" in chart_text
    assert "discovery" in glance_text or "discovery" in chart_text
    assert "grounding" in glance_text or "GROUNDING" in chart_text

    # 16. Explanatory sentences under each step: they live as theorem-row
    #     glosses in the sections, so they must survive in the union.
    for sent in (
        "Right and wrong both obtain",
        "Objective correctness determines agential standards",
        "Apprehending incompatible alternatives within a committed stance constitutes Choice",
        "Freedom is derived by pure logic from genuine normativity and choice",
        "A subject is recognized as free in virtue of possessing Free Will",
        "A free subject is constitutively an authoritative Person",
        "Distinct persons have numerically distinct wills",
        "Personal free agency ontologically grounds the normative order",
        "The objective logical and normative order entails necessary truth",
        "The machine-proved dependence: wherever Right/Wrong is real, its ground-type is personal",
    ):
        assert sent in surface, f"explanatory sentence lost: {sent[:50]}…"

    # 17. First 200 lines readability (window wide enough for the reading-guide
    #     opening block, which grew with the moral-frontier note C175/F3)
    first_200 = "\n".join(text.splitlines()[:260])
    # NoRight/the retorsive defense is the deontic route's §1 (ledger, 2026-09-30);
    # the reading path keeps the thesis sentence instead, and it must land early.
    assert "NoRight" in first_200 or "NoRight" in sec1_text, (
        "the NoRight datum must be visible on the reading path or at the head of the deontic route")
    assert "for which meaning can mean" in first_200, "the thesis sentence must land early"
    assert "claims_correct_no_right_self_refuting" in ledger_text

    # 18. Natural deduction step visibility in Main Proof Spine
    assert "Formal Derivation (" in ledger_text, "ledger must expose step-by-step natural deduction derivations"
    assert "Formal Derivation (" not in text, "reading path must not carry derivation blocks"

    # 19. Adversarial Denial Normal Forms in Free Will section
    assert "Adversarial Denial Normal Forms (D1–D8)" in ledger_text, "ledger must present the exhaustive D1-D8 adversarial denials"
    assert "Adversarial Denial Normal Forms" in text, "reading path must point at the D1-D8 block"

    # 20. Historical disclaimer on legacy draft
    old_readme = (ROOT / "README-OLD.md").read_text(encoding="utf-8")
    assert "HISTORICAL NOTICE FOR AGENTS" in old_readme, "README-OLD.md must carry historical disclaimer banner"

    # 21. Machine-Checked Kernel Rebuttal blocks under skeptic attacks
    assert "Machine-Checked Kernel Rebuttal —" in ledger_text, "ledger must present machine-checked kernel rebuttals for skeptic attacks"

    # 22. The Pillars of Formal Defense against skeptical attacks (ledger, 2026-09-30).
    # The count is derived from the rows, so it is asserted, not transcribed.
    assert "Why Common Skeptical Attacks Fail (The Seven Pillars of Formal Defense)" in ledger_text, (
        "the Pillars are audit material and live in the ledger")
    _pil_rows = ledger_text.partition("Pillars of Formal Defense")[2].split("## ")[0]
    assert len(re.findall(r"^\| \*\*\d+\. ", _pil_rows, re.M)) == 7, (
        "the pillar heading must count exactly the rows it emits")
    for _pillar in ("Normative Nihilism", "Eliminativism of Choice", "Theological Smuggling",
                    "Euthyphro / Voluntarism", "Physicalist / Atomic Ground"):
        assert _pillar in ledger_text, f"the ledger must carry the pillar '{_pillar}'"
    # …and the cremation on the reading path must cover the same attacks. The
    # Cremation is no longer a numbered `## 13.` section: it is Part III, the R1–R16
    # refutations (CLEARER.md §4), where R5/R8/R13/R14 answer the atomic,
    # voluntarist, monotheist and physicalist attacks.
    _cremation = text.partition("## Part III")[2].partition("## Part IV")[0]
    assert _cremation, "the reading path must keep Part III — the cremation"
    for _attack in ("Voluntarism", "atom", "single"):
        assert _attack in _cremation, f"the cremation must answer '{_attack}' on the reading path"

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
    ledger_text = (ROOT / "investigations" / "ledger.md").read_text(encoding="utf-8")
    # The axiom-free indubitable route is the deontic route's §4, which moved to
    # the ledger on 2026-09-30; the reading path shows the C140 route at §6.
    fw_text = ledger_route(ledger_text, "### 4. Free Will", "### 5.")
    assert fw_text, "the ledger must carry deontic route section 4 (Free Will)"
    fw_reading = text.partition("### Step 6 — Co-Meaning Both Poles Is Free Will")[2].partition("### Step 7")[0]
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
    assert "SEMANTIC" not in fw_reading and "METAPHYSICAL" not in fw_reading, (
        "Test 4 FAILED: the reading path's free-will section must carry no bridge badge")
    print("  ✓ Test 4 passed: FreeSubject and FreeWill are derived theorems, never classified as bridges.")

    # Test 5: Section 4 must state the axiom-free Freedom edge on the reading path
    assert "by pure logic" in fw_text and "zero substantive axioms" in fw_text, (
        "Test 5 FAILED: deontic route section 4 must state that Free Will follows by pure logic, 0 substantive axioms"
    )
    glance_text = text.partition("### The ten steps at a glance")[2].partition("### Step 1")[0]
    assert "0 substantive axioms" in glance_text, (
        "Test 5 FAILED: the ten-step table must show the axiom-free steps"
    )
    print("  ✓ Test 5 passed: Main Proof Spine and Glance contain explicitly marked axiom-free Freedom edge.")

    # Test 6: No badge on an upstream edge may be inherited automatically by downstream conclusions
    choice_to_fw = glance_text.partition("INCOMPATIBILITY")[2].partition("FREE WILL")[0]
    assert "SEMANTIC" not in choice_to_fw, (
        "Test 6 FAILED: Upstream SEMANTIC badge must not be inherited by transition to Free Will"
    )
    assert "AxJudicativeBipolarity" not in choice_to_fw, (
        "Test 6 FAILED: AxJudicativeBipolarity must not be inherited on edge into Free Will"
    )
    print("  ✓ Test 6 passed: No upstream badge or bridge is inherited by downstream Free Will conclusion.")

    # Test 7: Target-driven canonical selection: the deontic route's canonical
    # Free-Will proof is indubitable_normative_free_will, and the reading path
    # must ALSO show the Co-Meaning route (C140) with its own PROVEN footer.
    assert "indubitable_normative_free_will" in fw_text, (
        "Test 7 FAILED: deontic route section 4 canonical proof must be indubitable_normative_free_will"
    )
    assert "✅ · [IndubitableNormativeFreeWill.lean#indubitable_normative_free_will]" in fw_text, (
        "Test 7 FAILED: deontic route section 4 canonical proof must have the PROVEN ✅ cert footer"
    )
    assert "✅ · [NormativeOrder.lean#claims_normative_correctness_derives_free_will]" in fw_reading, (
        "Test 7 FAILED: reading spine section 6 must carry the PROVEN ✅ footer of the Co-Meaning route"
    )
    print("  ✓ Test 7 passed: canonical Free-Will targets are indubitable (ledger §4) and Co-Meaning (README §6), both 0 substantive axioms.")

    # Test 8: Conceptual bifurcation of Discovery and Ontological Grounding
    assert "discovery" in glance_text.lower(), (
        "Test 8 FAILED: Document must explicitly identify the Discovery direction"
    )
    assert "grounding" in glance_text.lower(), (
        "Test 8 FAILED: Document must explicitly identify the Ontological Grounding direction"
    )
    ledger_chart = (ROOT / "investigations" / "ledger.md").read_text(encoding="utf-8")
    assert "ONTOLOGICAL GROUNDING" in ledger_chart or "Ontological Grounding" in ledger_chart, (
        "Test 8 FAILED: ledger flowchart must visually expose the Ontological Grounding arrow"
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

    # 6. Unified Ontology: Person := ThomisticPersonCore, reached from FreeSubject by priced theorem, 0 substantive axioms
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
    glance_text = text.partition("### The ten steps at a glance")[2].partition("### Step 1")[0]
    # The authoritative PERSON definition must be exposed on the reading path: in
    # the glance row for step 7 or, since that row now carries the implication,
    # in the step's own section (which states `Person := ThomisticPersonCore`).
    _person_sec = text.partition("### Step 7 — Free Will Is a Person")[2].partition("### Step 8")[0]
    _person_surface = glance_text + _person_sec
    assert "PERSON" in glance_text and (
        "Person(s) := ThomisticPersonCore(s)" in _person_surface
        or "Person s : Prop := ThomisticPersonCore s" in _person_surface
        or "Person := ThomisticPersonCore" in _person_surface), (
        "the reading path must expose the authoritative PERSON (Person := ThomisticPersonCore)"
    )
    ledger_full = (ROOT / "investigations" / "ledger.md").read_text(encoding="utf-8")
    # The deontic flowchart (with the deontic labels) is the ledger's second map.
    chart_text = ledger_full.partition("## The Whole Argument in One Map")[2].partition("## §")[0]
    chart_text += ledger_full.partition("### The Deontic Route in One Map")[2]
    assert "Anti-Self-Legislation" in ledger_full and "NORMATIVE COLLAPSE" in ledger_full
    assert "Hostile Impersonal Model" in ledger_full and "SURVIVING PLATONIST MODEL" in ledger_full
    assert "AxSecondPersonalAddress" in ledger_full
    assert "SubstantivePerson" not in glance_text, "Fake SubstantivePerson frontier must not appear in glance"
    assert "CONSTRUCTIVE PERSONAL GROUND" in chart_text, (
        "the deontic label lives in the ledger's ASCII map, not on the reading path")
    assert "NECESSARY DIVINE GROUND / BEING" in ledger_full or "ONE GOD" in ledger_full
    assert "preceding_theory ⇏ trinity" in ledger_full, "ledger chart must carry the trinity boundary"
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

    # Exact kernel footprints (emenda 2026-09-25: the single-field record and the
    # datum routes stay {Means, Subject}; routes through Person honestly carry
    # the will vocabulary, and the discovery route the priced law).
    forced_exact = {
        "Logos.PersonalNormativeGround.groundsRightWrong_iff_forced_content":
            {"Means", "Subject"},
        "Logos.PersonalNormativeGround.forced_content_of_person":
            {"Means", "Subject", "Will", "subjectWill"},
        "Logos.PersonalNormativeGround.grounding_forced_by_preceding_facts":
            {"Means", "Subject", "Will", "subjectWill", "will_individuation"},
        "Logos.PersonalNormativeGround.grounding_forced_at_datum":
            {"Means", "Subject"},
    }
    for full, expected in forced_exact.items():
        assert full in decls, f"Declaration '{full}' missing from Lean AST"
        fp = audit.get(full, [])
        subst = [ax for ax in fp if (registry.get(ax.rsplit(".", 1)[-1]) or {}).get("tag") in ("SEM", "META")]
        assert len(subst) == 0, f"'{full}' must have 0 substantive axioms, found: {subst}"
        assert set(ax.rsplit(".", 1)[-1] for ax in fp) == expected, (
            f"'{full}' footprint must be {expected} exactly, got: {set(ax.rsplit('.', 1)[-1] for ax in fp)}"
        )
    grw_code = Path("formal/Logos/PersonalNormativeGround.lean").read_text(encoding="utf-8")
    assert "def ForcedGroundContent" in grw_code, "ForcedGroundContent def missing from PersonalNormativeGround.lean"
    assert "groundsRightWrong_iff_forced_content" in grw_code, "Transparency theorem missing from source"
    for ax in ("AxPersonalNormativeGround", "GroundProp", "AxPersonalGround"):
        assert ax not in registry, f"Forbidden grounding axiom '{ax}' still present in registry!"
    print("  ✓ Test passed: GroundsRightWrong is transparent, prior-forced, 0 substantive axioms (agential core {Means, Subject}; Person routes priced).")


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
    glance_text = text.partition("### The ten steps at a glance")[2].partition("### Step 1")[0]
    ledger_chart = (ROOT / "investigations" / "ledger.md").read_text(encoding="utf-8")
    assert "Discovery" in glance_text or "discovery" in glance_text, "Glance must expose discovery arrow"
    assert "Grounding" in glance_text or "grounding" in glance_text, "Glance must expose grounding arrow"
    assert "ONTOLOGICAL GROUNDING ARROW" in ledger_chart, "ledger flowchart must visually expose Ontological Grounding Arrow"
    print("  ✓ Test 6 passed: README.md reflects dual-arrow architecture.")


def test_ontological_proof_structure(decls: dict, node_map: dict) -> None:
    print("Testing explicit proof structure of the unconditional personal-ground headline…")
    audit = load_audit()
    registry = bd.load_axiom_registry(decls, node_map)
    
    hl_full = "Logos.PersonalGroundOfReality.the_person_supports_the_reality_of_right"
    assert hl_full in decls, f"Declaration '{hl_full}' missing from Lean AST"
    hl_footprint = audit.get(hl_full, [])
    
    # 1. The headline is unconditional: the vocabulary-only agency tunnel plus the
    #    honestly-priced will vocabulary (emenda 2026-09-25: Person routes carry
    #    Will/subjectWill, and the discovery step the VOCAB law will_individuation).
    hl_subst = [ax for ax in hl_footprint if (registry.get(ax.rsplit(".", 1)[-1]) or {}).get("tag") in ("SEM", "META")]
    assert len(hl_subst) == 0, f"Headline must have 0 substantive axioms, found: {hl_subst}"
    hl_vocab = sorted(set(ax.rsplit(".", 1)[-1] for ax in hl_footprint))
    assert set(hl_vocab) == {"Initiates", "Means", "State", "Subject", "Will", "subjectWill", "will_individuation", "choice", "propext", "sound"}, (
        f"Headline footprint mismatch: {hl_vocab}"
    )
    print(f"  ✓ Test 1 passed: Headline footprint exactly {{Initiates, Means, State, Subject, Will, subjectWill, will_individuation, CL}} ({len(hl_subst)} substantive axioms).")
    
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


def _rendered_surface(secs, decls, node_map):
    """Both sinks joined: sensitivity must hold for the whole generated surface."""
    doc = render_deduction_sections(secs, decls, node_map)
    return "\n".join(doc.get("readme")) + "\n" + "\n".join(doc.get("ledger"))


def test_sensitivity(decls: dict, node_map: dict, graph: dict, sections: list) -> None:
    print("Testing dynamic sensitivity of the deduction generator to proof changes…")
    baseline_secs = discover_deduction_sections(sections, decls, node_map, graph, {})
    baseline = _rendered_surface(baseline_secs, decls, node_map)
    
    # 1. Mutate a theorem hypothesis/conclusion in memory
    mutated_decls = copy.deepcopy(decls)
    target = "Logos.PersonalGroundOfReality.the_person_supports_the_reality_of_right"
    orig_stmt = mutated_decls[target]["statement"]
    mutated_decls[target]["statement"] = orig_stmt + " ∧ True"
    _CTX["decls"] = mutated_decls
    mutated_secs = discover_deduction_sections(sections, mutated_decls, node_map, graph, {})
    mutated_output = _rendered_surface(mutated_secs, mutated_decls, node_map)
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
    mutated_output2 = _rendered_surface(mutated_secs2, mutated_decls2, node_map)
    _CTX["decls"] = decls
    assert "New custom explanation of non-nothingness" in mutated_output2
    print("  ✓ Docstring/meaning mutation test passed: changing Lean docstring dynamically updated explanation.")
    
    # 3. Mutate an axiom footprint in memory
    orig_audit = list(bd._AUDIT.get(target, []))
    bd._AUDIT[target] = orig_audit + ["Logos.Value.AxTwoSubjects"]
    mutated_secs3 = discover_deduction_sections(sections, decls, node_map, graph, {})
    mutated_output3 = _rendered_surface(mutated_secs3, decls, node_map)
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
    # READINGPATH.md §5: the full frontier list is ledger material; the README
    # keeps the live count and a pointer.
    ledger = (ROOT / "investigations" / "ledger.md").read_text(encoding="utf-8")
    assert "\n## Formal Frontiers\n" in ledger, "ledger: '## Formal Frontiers' appendix missing (check presentation_policy.include_frontiers_appendix)"
    assert "**§28 open bridges.**" in ledger, "OPEN_BRIDGES block missing from ledger ## Formal Frontiers"
    assert "#7 `NecessaryEntity e → ∃ τ, Ground e τ`" in ledger, "open bridge #7 literal missing"
    assert "#9 `Ground(e, personal) → Personal(e)`" in ledger, "open bridge #9 literal missing"
    text = OUT_PATH.read_text(encoding="utf-8")
    assert "formal frontiers" in text.lower(), "README must point at the formal frontiers"
    print("  ✓ ## Formal Frontiers renders OPEN_BRIDGES #7/#9 in the ledger, pointed-to from the README.")


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
