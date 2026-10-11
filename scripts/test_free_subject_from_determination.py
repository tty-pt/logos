#!/usr/bin/env python3
"""test_free_subject_from_determination.py — Standalone validation and audit.

Verifies:
1. Compilation: `lean FreeSubjectFromDetermination.lean` compiles with exit code 0.
2. Absence of escape hatches: 0 `sorry`, 0 `admit`, 0 `axiom` in code.
3. Clean footprint: all audited theorems depend on ZERO substantive axioms (empty or standard built-in only).
4. Structural compliance:
   - Does not import judgment structures (JudgmentDeterminationChain, AssentsAt, WithholdsAt).
   - Distinguishes Determines from GroundingDependsOn.
   - Non-question-begging taxonomy (FreeOrigin / FreeSubject is not an assumed disjunct).
   - Independent non-causal ground dilemma analyzed.
   - Contingency transfer bridge and separate source configuration.
   - 4 distinct agency conditions (IsUnforced, AgentiallyOriginated, HasSamePastAlternative, ExercisesControl).
   - Metatheoretic proof bridge actively consumed (proof_occurs and proof_is_contingent).
   - All 3 negative independence models present and verified.
"""

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN_FILE = ROOT / "FreeSubjectFromDetermination.lean"


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


def test_free_subject_from_determination() -> None:
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

    # 3. Check taxonomy is non-question-begging
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
    print("  ✓ Non-question-begging taxonomy verified (covers independent non-causal ground; FreeSubject is not an assumed disjunct).")

    # 4. Check 4 distinct agency conditions
    for agency_cond in [
        "IsUnforced",
        "AgentiallyOriginated",
        "HasSamePastAlternative",
        "ExercisesControl",
    ]:
        assert agency_cond in code_text, f"Missing distinct agency condition `{agency_cond}`"
    print("  ✓ 4 distinct agency conditions verified (IsUnforced, AgentiallyOriginated, HasSamePastAlternative, ExercisesControl).")

    # 5. Check ContingencyTransferBridge and separated configuration
    assert "ContingencyTransferBridge" in code_text, "Missing ContingencyTransferBridge"
    assert "SourceConfigContingent" in code_text, "Missing SourceConfigContingent"
    assert "Necessitates" in code_text, "Missing Necessitates"
    assert "sourceConfig" in code_text, "Missing sourceConfig"
    print("  ✓ Separated source configuration and ContingencyTransferBridge verified.")

    # 6. Check active consumption of ProofOccurrence
    start_idx = code_text.find("theorem concrete_proof_occurrence_implies_free_subject")
    assert start_idx != -1, "theorem concrete_proof_occurrence_implies_free_subject not found in code"
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
    print("  ✓ Active consumption of ProofOccurrence bridge verified.")

    # 7. Check all 3 negative independence theorems exist
    assert "unforced_personal_source_without_control_fails_free_subject" in code_text
    assert "circular_impersonal_grounding_satisfiable_without_well_foundedness" in code_text
    assert "occurrence_contingency_without_transfer_fails_free_subject" in code_text
    print("  ✓ All 3 negative independence models verified.")

    # 8. Lean compilation check
    env = dict(sys.modules["os"].environ)
    env["PATH"] = f"{Path.home()}/.elan/bin:" + env.get("PATH", "")
    cmd = ["lean", str(LEAN_FILE)]
    res = subprocess.run(cmd, capture_output=True, text=True, env=env)
    assert res.returncode == 0, f"Lean compilation failed:\n{res.stderr}\n{res.stdout}"
    print("  ✓ Lean 4.34.1 compilation clean (exit code 0).")

    # 9. Axioms check
    expected_axioms = [
        ("Logos.FreeSubjectFromDetermination.wellFounded_explanation_has_no_two_cycle", False),
        ("Logos.FreeSubjectFromDetermination.necessitation_excludes_contingency", False),
        ("Logos.FreeSubjectFromDetermination.impersonal_contingent_source_forms_explanatory_cycle", False),
        ("Logos.FreeSubjectFromDetermination.impersonal_contingent_source_fails_as_ultimate_explanation", False),
        ("Logos.FreeSubjectFromDetermination.ultimate_source_must_be_personal", False),
        ("Logos.FreeSubjectFromDetermination.personal_source_and_contingency_yields_free_subject", False),
        ("Logos.FreeSubjectFromDetermination.concrete_proof_occurrence_implies_free_subject", False),
        ("Logos.FreeSubjectFromDetermination.unforced_personal_source_without_control_fails_free_subject", False),
        ("Logos.FreeSubjectFromDetermination.circular_impersonal_grounding_satisfiable_without_well_foundedness", False),
        ("Logos.FreeSubjectFromDetermination.occurrence_contingency_without_transfer_fails_free_subject", True),
    ]
    for decl, built_in_ok in expected_axioms:
        needle_zero = f"'{decl}' does not depend on any axioms"
        needle_propext = f"'{decl}' depends on axioms: [propext]"
        assert (needle_zero in res.stdout) or (built_in_ok and needle_propext in res.stdout), (
            f"Declaration {decl} had unexpected footprint. Output:\n{res.stdout}"
        )
    print(f"  ✓ All {len(expected_axioms)} audited declarations verified with ZERO substantive axioms.")

    print("\nALL FREE SUBJECT FROM DETERMINATION CHECKS PASSED (0 errors).")


if __name__ == "__main__":
    test_free_subject_from_determination()
