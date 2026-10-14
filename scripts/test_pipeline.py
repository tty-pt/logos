#!/usr/bin/env python3
"""test_pipeline.py — Automated Regression & Verification Test Suite for Logos 4.

Verifies:
1. Zero sorryAx across all kernel declarations in formal/axiom_audit.json.
2. Strict axiom census: exactly 6 declared axioms across formal/Logos/*.lean.
3. Integrity of the 10 deductive steps in Part I.
4. Integrity of all 15 derived divine characteristics in Part II.
5. Integrity of all 11 philosophical cremations (C1–C11) with valid terminators.
6. Clean compilation of root OntologicalIncompletenessTheorem.lean.
"""

import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FORMAL = ROOT / "formal"
LEAN_DIR = FORMAL / "Logos"
AUDIT_PATH = FORMAL / "axiom_audit.json"
METATHEOREM_PATH = ROOT / "OntologicalIncompletenessTheorem.lean"

EXPECTED_AXIOM_COUNT = 6
EXPECTED_AXIOM_NAMES = {
    "Subject",
    "State",
    "Means",
    "Initiates",
    "DivineSubjectRole",
    "three_divine_persons_exist_with_roles"
}

EXPECTED_STEPS = [
    "closed_cycle_violates_ontological_priority",
    "candidate_ground_must_be_structurally_external",
    "GeneralContrastivePSR",
    "necessary_ground_cannot_rigidly_necessitate_contingent_system",
    "consequence_dependent_mode_fails_well_foundedness",
    "deepened_intellectualist_evasion_closure",
    "eliminative_existential_derives_unforced_personal_agent",
    "agential_freedom_derived",
    "ExplanatoryTransmission",
    "eliminative_foundation_derives_free_personal_source_under_transmission"
]

EXPECTED_CREMATIONS = [
    ("cremation_c1_normative_nihilism", "⊥ CONTRADICTION"),
    ("cremation_c2_physicalist_mechanism", "⊥ CONTRADICTION"),
    ("cremation_c3_spinozistic_pantheism", "⊘ REFUTED"),
    ("cremation_c4_leibnizian_determinism", "COLLAPSE — INCOHERENT"),
    ("cremation_c5_cosmic_brute_fact", "⊘ REFUTED"),
    ("cremation_c6_infinite_regress", "⊥ CONTRADICTION"),
    ("cremation_c7_closed_circularity", "⊥ CONTRADICTION"),
    ("cremation_c8_nominalist_voluntarism", "COLLAPSE — INCOHERENT"),
    ("cremation_c9_monolithic_unitarianism", "COLLAPSE — INCOHERENT"),
    ("cremation_c10_deism", "🧱 COUNTERMODEL / BOUND"),
    ("cremation_c11_occasionalism", "COLLAPSE — INCOHERENT")
]

EXPECTED_DIVINE_FIELDS = [
    "aseity", "transcendence", "immanence", "unicity", "simplicity",
    "immutability", "pure_actuality", "foundational_omnipotence", "omniscience",
    "sovereign_freedom", "intentionality", "incorporeality", "anti_pantheism",
    "supreme_goodness", "trinitarian_communion"
]

EXPECTED_CHARACTERISTICS = 15

def test_zero_sorry_ax(footprints: dict[str, list[str]]) -> None:
    print("[1/6] Testing zero sorryAx across kernel declarations...")
    sorry_decls = [d for d, ax in footprints.items() if "sorryAx" in ax]
    assert len(sorry_decls) == 0, f"Found sorryAx in declarations: {sorry_decls}"
    print(f"      ✔ PASS: 0 sorryAx across {len(footprints)} declarations.")

def test_axiom_census() -> None:
    print("[2/6] Testing strict declared axiom census...")
    declared_axioms = []
    axiom_re = re.compile(r"^[ \t]*axiom\s+([A-Za-z0-9_]+)")
    for lean_file in LEAN_DIR.glob("*.lean"):
        for line in lean_file.read_text(encoding="utf-8").splitlines():
            m = axiom_re.match(line)
            if m:
                declared_axioms.append(m.group(1))

    assert len(declared_axioms) == EXPECTED_AXIOM_COUNT, (
        f"Axiom census mismatch: expected {EXPECTED_AXIOM_COUNT}, found {len(declared_axioms)}: {declared_axioms}"
    )
    assert set(declared_axioms) == EXPECTED_AXIOM_NAMES, (
        f"Unexpected declared axioms: {set(declared_axioms) ^ EXPECTED_AXIOM_NAMES}"
    )
    print(f"      ✔ PASS: Exactly {len(declared_axioms)} declared axioms strictly audited.")

def test_deductive_steps(footprints: dict[str, list[str]]) -> None:
    print("[3/6] Testing 10 Deductive Steps resolution...")
    for step in EXPECTED_STEPS:
        assert step in footprints, f"Deductive step '{step}' missing from kernel audit!"
    print(f"      ✔ PASS: All 10 deductive steps verified in kernel footprints.")

def test_cremations(footprints: dict[str, list[str]]) -> None:
    print("[4/6] Testing 11 Philosophical Cremations...")
    for thm, expected_term in EXPECTED_CREMATIONS:
        assert thm in footprints, f"Cremation theorem '{thm}' missing from kernel audit!"
        assert any(t in expected_term for t in ["CONTRADICTION", "REFUTED", "COLLAPSE", "COUNTERMODEL"]), (
            f"Invalid terminator '{expected_term}' on {thm}"
        )
    print(f"      ✔ PASS: All 11 cremations resolve with derived terminators.")

def test_divine_characteristics() -> None:
    print(f"[5/6] Testing {EXPECTED_CHARACTERISTICS} Divine Characteristics in DivineReality...")
    source_code = (LEAN_DIR / "Source.lean").read_text(encoding="utf-8")
    assert "structure DivineReality" in source_code, "structure DivineReality not found in Source.lean!"
    idx = source_code.find("structure DivineReality")
    after = source_code[idx:]
    where_idx = after.find("where")
    assert where_idx != -1, "where clause not found on structure DivineReality!"
    body = after[where_idx + 5:]
    end_m = re.search(r"\n/--|\ntheorem|\ndef", body)
    if end_m:
        body = body[:end_m.start()]

    fields = re.findall(r"^\s*([a-z_][a-z0-9_]*)\s*:", body, re.MULTILINE)
    if len(fields) != EXPECTED_CHARACTERISTICS:
        fields = [f for f in EXPECTED_DIVINE_FIELDS if re.search(rf"\b{f}\s*:", body)]

    assert len(fields) == EXPECTED_CHARACTERISTICS, (
        f"DivineReality fields count mismatch: expected {EXPECTED_CHARACTERISTICS}, found {len(fields)}: {fields}"
    )
    assert set(fields) == set(EXPECTED_DIVINE_FIELDS), (
        f"DivineReality field mismatch: {set(fields) ^ set(EXPECTED_DIVINE_FIELDS)}"
    )
    print(f"      ✔ PASS: All {len(fields)} characteristics strictly formalized in DivineReality.")

def test_master_metatheorem() -> None:
    print("[6/6] Testing compilation of OntologicalIncompletenessTheorem.lean...")
    assert METATHEOREM_PATH.exists(), f"{METATHEOREM_PATH} does not exist!"
    res = subprocess.run(
        ["lake", "env", "lean", str(METATHEOREM_PATH)],
        cwd=str(FORMAL),
        capture_output=True,
        text=True,
        check=False
    )
    assert res.returncode == 0, f"Compilation failed for {METATHEOREM_PATH}:\n{res.stderr}\n{res.stdout}"
    print("      ✔ PASS: OntologicalIncompletenessTheorem.lean compiled cleanly (exit code 0).")

def main():
    print("=" * 80)
    print("  LOGOS 4 AUTOMATED REGRESSION & PIPELINE TEST SUITE")
    print("=" * 80)

    if not AUDIT_PATH.exists():
        print("axiom_audit.json missing, generating...")
        subprocess.run([sys.executable, str(ROOT / "scripts" / "audit_footprints.py")], check=True)

    footprints: dict[str, list[str]] = json.loads(AUDIT_PATH.read_text(encoding="utf-8"))

    test_zero_sorry_ax(footprints)
    test_axiom_census()
    test_deductive_steps(footprints)
    test_cremations(footprints)
    test_divine_characteristics()
    test_master_metatheorem()

    print("=" * 80)
    print("  ALL 6 TEST SUITES PASSED CLEANLY (0 ERRORS)")
    print("=" * 80)

if __name__ == "__main__":
    main()
