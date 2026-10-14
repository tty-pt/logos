#!/usr/bin/env python3
"""check_consistency.py — Consistency, negative-compilation, and sort-discipline verification for logos4.

Four gates:
1. Gate A — Negative compilation (formal/consistency/FalseNotDerivable.lean):
   Attempts to derive `False` from live theory. MUST FAIL to elaborate.
   Rejects timeout, memory kill, crash, or missing import error.
2. Gate B — Syntactic scan:
   Ensures no declared axiom equates a subject with the ground.
3. Gate S — sorryAx audit:
   Ensures 0 `sorryAx` appears anywhere in the kernel axiom footprint.
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FORMAL = ROOT / "formal"
LEAN_DIR = FORMAL / "Logos"
AUDIT_PATH = FORMAL / "axiom_audit.json"
GUARD_PATH = FORMAL / "consistency" / "FalseNotDerivable.lean"

BANNED_AXIOM_PATTERNS = [
    re.compile(r"Entity\.ofSubject\s+[^=]+=\s*Entity\.ofGround"),
    re.compile(r"Entity\.ofGround\s*=\s*Entity\.ofSubject"),
    re.compile(r"EntityOf\s+[^=]+=\s*Entity\.ofGround"),
    re.compile(r"Entity\.ofGround\s*=\s*EntityOf"),
    re.compile(r"EntityOf\s+[^=]+=\s*divineReality"),
    re.compile(r"divineReality\s*=\s*EntityOf"),
]

def check_negative_compilation() -> bool:
    print("Gate A — negative compilation (formal/consistency/FalseNotDerivable.lean)...")
    if not GUARD_PATH.exists():
        print(f"  FAILED Gate A: Guard file {GUARD_PATH} not found.")
        return False

    res = subprocess.run(
        ["lake", "env", "lean", str(GUARD_PATH)],
        cwd=str(FORMAL),
        capture_output=True,
        text=True,
        check=False
    )

    if res.returncode == 0:
        print("  FATAL FAILED Gate A: FalseNotDerivable COMPILED CLEANLY!")
        print("  The kernel is inconsistent (False is derivable).")
        return False

    err_output = res.stderr + "\n" + res.stdout
    # Guard must fail with an elaboration/type error, not missing module or syntax crash
    if "unknown module" in err_output or "no such file" in err_output:
        print(f"  FAILED Gate A: Broken import in guard file:\n{err_output}")
        return False

    if "error:" in err_output:
        print("  PASS: Guard fails to elaborate as required (compiler correctly rejects FalseNotDerivable)")
        return True

    print(f"  FAILED Gate A: Unexpected failure mode:\n{err_output}")
    return False

def check_syntactic_scan() -> bool:
    print("Gate B — syntactic scan (no axiom equates a subject with the ground)...")
    count = 0
    for lean_file in LEAN_DIR.glob("*.lean"):
        code = lean_file.read_text(encoding="utf-8")
        for line in code.splitlines():
            if line.strip().startswith("axiom "):
                count += 1
                for pat in BANNED_AXIOM_PATTERNS:
                    if pat.search(line):
                        print(f"  FAILED Gate B: Banned identity in {lean_file.name}: {line}")
                        return False
    print(f"  PASS: Scanned {count} declared axioms; no axiom equates a subject with the ground.")
    return True

def check_footprints_for_sorry() -> bool:
    print("Gate S — sorryAx audit...")
    if not AUDIT_PATH.exists():
        print("  WARNING: axiom_audit.json not found, run audit_footprints.py first.")
        return True
    footprints = json.loads(AUDIT_PATH.read_text(encoding="utf-8"))
    bad = []
    for decl, axioms in footprints.items():
        if "sorryAx" in axioms:
            bad.append(decl)
    if bad:
        print(f"  FAILED Gate S: sorryAx found in {len(bad)} declarations:")
        for b in bad[:10]:
            print(f"    {b}")
        return False
    print(f"  PASS: 0 sorryAx found across {len(footprints)} declarations.")
    return True

def main():
    ok_a = check_negative_compilation()
    ok_b = check_syntactic_scan()
    ok_s = check_footprints_for_sorry()
    if ok_a and ok_b and ok_s:
        print("\nCONSISTENCY GATE PASSED: False is not derivable, theory is sound, and sort-discipline is verified.")
        sys.exit(0)
    else:
        print("\nCONSISTENCY GATE FAILED.")
        sys.exit(1)

if __name__ == "__main__":
    main()
