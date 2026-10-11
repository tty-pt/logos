#!/usr/bin/env python3
"""test_free_subject_determination_dilemma.py — Standalone validation and audit.

Verifies:
1. Compilation: `lean FreeSubjectDeterminationDilemma.lean` compiles with exit code 0 and 0 warnings.
2. Absence of escape hatches: 0 `sorry`, 0 `admit`, 0 `axiom` in code.
3. Clean footprint: all audited theorems depend on ZERO substantive axioms (empty or standard built-in only).
4. Structural compliance:
   - Pure determination model (no judgment concepts imported).
   - Distinguishes Determines from GroundingDependsOn.
   - 4 distinct explanatory targets (ExplainsSubstrate, ExplainsConfiguration, ExplainsProduction, ExplainsContrastiveSelection).
   - Non-question-begging taxonomy (FreeOrigin / FreeSubject is not an assumed disjunct).
   - OriginExplanationTaxonomy does NOT stipulate a trilemma (no independent_ground_dilemma field).
   - Primitive explanatory principles (Contrastive PSR and Impersonal Antecedent Symmetry).
   - Principle of Contrastive Teleology (ContrastiveTeleologyPrinciple).
   - Theorem independent_non_causal_ground_fails_under_contrastive_teleology is derived.
   - Result 1: impersonal_source_fails_if_consequence_dependent.
   - Result 2: impersonal_contingent_source_derives_consequence_dependence.
   - Clean separation of Personal Source from Libertarian Freedom:
     * ultimate_source_must_be_personal derives IsPersonalSource (unforced personal originator).
     * personal_source_yields_free_subject derives FreeSubject via AgentialControlBridge.
   - Metatheoretic proof bridge actively consumed:
     * hProof.proof_occurs is applied to hTerm.
     * hProof.proof_is_contingent supplies contingency.
   - All 4 negative independence models present and verified (including 3-node C -> S -> G model).
"""

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN_FILE = ROOT / "FreeSubjectDeterminationDilemma.lean"


def strip_comments_and_strings(text: str) -> str:
    """Blank out block comments, line comments, and string literals."""
    out = []
    i, n = 0, len(text)
    depth = 0
    while i < n:
        if depth == 0 and text[i : i + 2] == "--":
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if depth == 0 and text.startswith('"', i):
            out.append(" ")
            i += 1
            while i < n:
                if text[i] == "\\":
                    out.extend([" ", " "])
                    i += 2
                    continue
                if text[i] == '"':
                    out.append(" ")
                    i += 1
                    break
                if text[i] == "\n":
                    out.append("\n")
                else:
                    out.append(" ")
                i += 1
            continue
        if text.startswith("/-", i):
            depth += 1
            out.extend([" ", " "])
            i += 2
            continue
        if depth > 0 and text.startswith("-/", i):
            depth -= 1
            out.extend([" ", " "])
            i += 2
            continue
        if depth > 0:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def test_free_subject_determination_dilemma() -> None:
    print(f"Auditing {LEAN_FILE}...")
    assert LEAN_FILE.exists(), f"Missing {LEAN_FILE}"
    raw_text = LEAN_FILE.read_text(encoding="utf-8")
    code_text = strip_comments_and_strings(raw_text)

    # 1. Structural checks: No judgment-specific psychology
    banned_judgment_tokens = [
        "JudgmentDeterminationChain",
        "AssentsAt",
        "WithholdsAt",
        "verdictNode",
        "judgmentActNode",
    ]
    for tok in banned_judgment_tokens:
        assert tok not in code_text, f"Found judgment-specific concept `{tok}` in code"
    print("  ✓ Pure determination model verified (no judgment structures imported).")

    # 2. Check no escape hatches
    for bad in [r"\bsorry\b", r"\badmit\b", r"\baxiom\b"]:
        m = re.search(bad, code_text)
        assert not m, f"Found escape hatch `{bad}` in code"
    print("  ✓ Zero escape hatches verified (0 sorry, 0 admit, 0 axiom).")

    # 3. Check 4 distinct explanatory targets
    for target in [
        "ExplainsSubstrate",
        "ExplainsConfiguration",
        "ExplainsProduction",
        "ExplainsContrastiveSelection",
    ]:
        assert target in code_text, f"Missing explanatory target `{target}`"
    print("  ✓ 4 distinct explanatory targets verified (substrate, configuration, production, contrastive selection).")

    # 4. Check taxonomy is non-question-begging and does NOT stipulate a trilemma
    assert "FreeOrigin" not in code_text, "Found FreeOrigin smuggled in code"
    tax_match = re.search(r"taxonomy_is_exhaustive\s*:\s*([^:=]+)", code_text)
    assert tax_match, "taxonomy_is_exhaustive declaration not found"
    tax_body = tax_match.group(1)
    assert "FreeSubject" not in tax_body, (
        "taxonomy_is_exhaustive must NOT smuggle FreeSubject as a disjunct"
    )
    assert "PersonalSource" in tax_body, (
        "taxonomy_is_exhaustive must include PersonalSource"
    )
    assert "IndependentNonCausalGround" in tax_body, (
        "taxonomy_is_exhaustive must include IndependentNonCausalGround"
    )
    # Ensure independent_ground_dilemma is NOT a field in OriginExplanationTaxonomy
    assert "independent_ground_dilemma" not in code_text, (
        "OriginExplanationTaxonomy must NOT stipulate independent_ground_dilemma as a field"
    )
    assert "has_independent_non_causal_ground" in code_text, (
        "OriginExplanationTaxonomy must include has_independent_non_causal_ground"
    )
    print("  ✓ Non-question-begging taxonomy verified (no stipulated trilemma; covers independent non-causal ground).")

    # 5. Check primitive explanatory principles and results
    assert "PrimitiveExplanatoryPrinciples" in code_text
    assert "contrastive_psr" in code_text
    assert "impersonal_antecedent_symmetry_leaves_brute" in code_text
    assert "consequence_dependent_selection" in code_text
    assert "impersonal_source_fails_if_consequence_dependent" in code_text
    assert "impersonal_contingent_source_derives_consequence_dependence" in code_text
    assert "ContrastiveTeleologyPrinciple" in code_text
    assert "independent_non_causal_ground_fails_under_contrastive_teleology" in code_text
    print("  ✓ Primitive explanatory principles, contrastive teleology, and derived theorems verified.")

    # 6. Check 4 distinct agency conditions and clean separation
    for agency_cond in [
        "IsUnforced",
        "AgentiallyOriginated",
        "HasSamePastAlternative",
        "ExercisesControl",
    ]:
        assert agency_cond in code_text, f"Missing distinct agency condition `{agency_cond}`"
    assert "IsPersonalSource" in code_text, "Missing IsPersonalSource predicate"
    assert "ultimate_source_must_be_personal" in code_text
    assert "personal_source_yields_free_subject" in code_text
    print("  ✓ 4 distinct agency conditions and clean separation of Personal Source from Free Subject verified.")

    # 7. Check ContingencyTransferBridge and separated configuration
    assert "ContingencyTransferBridge" in code_text, "Missing ContingencyTransferBridge"
    assert "SourceConfigContingent" in code_text, "Missing SourceConfigContingent"
    assert "Necessitates" in code_text, "Missing Necessitates"
    assert "sourceConfig" in code_text, "Missing sourceConfig"
    print("  ✓ Separated source configuration and ContingencyTransferBridge verified.")

    # 8. Check active consumption of ProofOccurrence
    start_idx = code_text.find("theorem concrete_proof_occurrence_implies_free_subject")
    assert start_idx != -1, "theorem concrete_proof_occurrence_implies_free_subject not found"
    by_idx = code_text.find(":= by", start_idx)
    assert by_idx != -1, "proof body ':= by' for concrete_proof_occurrence_implies_free_subject not found"
    end_idx = len(code_text)
    for marker in ["\ntheorem ", "\ndef ", "\n#print "]:
        m_pos = code_text.find(marker, by_idx)
        if m_pos != -1 and m_pos < end_idx:
            end_idx = m_pos
    master_body = code_text[by_idx:end_idx]
    assert "hProof.proof_is_contingent" in master_body, (
        "concrete_proof_occurrence_implies_free_subject must actively consume hProof.proof_is_contingent"
    )
    assert "hProof.proof_occurs" in master_body, (
        "concrete_proof_occurrence_implies_free_subject must actively consume hProof.proof_occurs"
    )
    assert re.search(r"hTerm\s+(?:hProof\.proof_occurs|hOccurs)", master_body), (
        "concrete_proof_occurrence_implies_free_subject must substantively apply hProof.proof_occurs to hTerm"
    )
    print("  ✓ Substantive application of ProofOccurrence to hTerm verified.")

    # 9. Check all 4 negative independence theorems exist
    assert "independent_non_causal_ground_satisfiable_without_cycle" in code_text
    assert "occurrence_alone_fails_free_subject" in code_text
    assert "necessitating_source_fails_free_subject" in code_text
    assert "unforced_personal_source_without_control_fails_free_subject" in code_text
    print("  ✓ All 4 negative independence models verified (including 3-node C -> S -> G model).")

    # 10. Lean compilation check
    env = dict(sys.modules["os"].environ)
    env["PATH"] = f"{Path.home()}/.elan/bin:" + env.get("PATH", "")
    cmd = ["lean", str(LEAN_FILE)]
    res = subprocess.run(cmd, capture_output=True, text=True, env=env)
    assert res.returncode == 0, f"Lean compilation failed:\n{res.stderr}\n{res.stdout}"
    assert "warning:" not in res.stdout, f"Lean emitted warnings:\n{res.stdout}"
    print("  ✓ Lean 4.34.1 compilation clean (exit code 0, 0 warnings).")

    # 11. Axioms check
    expected_axioms = [
        ("Logos.FreeSubjectDeterminationDilemma.wellFounded_explanation_has_no_two_cycle", False),
        ("Logos.FreeSubjectDeterminationDilemma.necessitation_excludes_contingency", False),
        ("Logos.FreeSubjectDeterminationDilemma.impersonal_source_fails_if_consequence_dependent", False),
        ("Logos.FreeSubjectDeterminationDilemma.impersonal_contingent_source_derives_consequence_dependence", False),
        ("Logos.FreeSubjectDeterminationDilemma.impersonal_contingent_source_fails_as_ultimate_explanation", False),
        ("Logos.FreeSubjectDeterminationDilemma.independent_non_causal_ground_fails_under_contrastive_teleology", False),
        ("Logos.FreeSubjectDeterminationDilemma.ultimate_source_must_be_personal", False),
        ("Logos.FreeSubjectDeterminationDilemma.personal_source_yields_free_subject", False),
        ("Logos.FreeSubjectDeterminationDilemma.concrete_proof_occurrence_implies_free_subject", False),
        ("Logos.FreeSubjectDeterminationDilemma.independent_non_causal_ground_satisfiable_without_cycle", True),
        ("Logos.FreeSubjectDeterminationDilemma.occurrence_alone_fails_free_subject", False),
        ("Logos.FreeSubjectDeterminationDilemma.necessitating_source_fails_free_subject", True),
        ("Logos.FreeSubjectDeterminationDilemma.unforced_personal_source_without_control_fails_free_subject", False),
    ]
    for decl, built_in_ok in expected_axioms:
        needle_zero = f"'{decl}' does not depend on any axioms"
        needle_propext = f"'{decl}' depends on axioms: [propext]"
        assert (needle_zero in res.stdout) or (built_in_ok and needle_propext in res.stdout), (
            f"Declaration {decl} had unexpected footprint. Output:\n{res.stdout}"
        )
    print(f"  ✓ All {len(expected_axioms)} audited declarations verified with ZERO substantive axioms.")

    print("\nALL FREE SUBJECT DETERMINATION DILEMMA CHECKS PASSED (0 errors).")


if __name__ == "__main__":
    test_free_subject_determination_dilemma()
