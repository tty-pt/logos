#!/usr/bin/env python3
"""Standalone consistency hygiene for best.lean.

best.lean lives outside `lean_lib Logos`, so none of the kernel gates
(`make build`, `check_consistency.py`, `audit_footprints.py`) ever see
it. This script is the substitute discipline, and it asserts three
things:

1. COMPILE-CLEAN: `lean best.lean` exits 0. Every proof in the file was
   therefore checked end to end by the kernel. (A file that does not
   compile proves nothing.)
2. NO ESCAPE HATCHES: no `sorry`, no `admit`, no `axiom` declarations
   in code. A `sorry` is an unproved claim; an `axiom` would silently
   widen every downstream `#print axioms` footprint. Both are checked
   on the comment-and-string-stripped text, so prose discussion of
   `sorryAx` (e.g. in audit notes) does not trip the gate.
3. AUDIT COVERAGE: every `#print axioms A.B.name` line names a
   declaration that exists in the file. (Lean itself would already fail
   on an unknown constant; this check reports the drift first, with a
   readable message.)

What this script does NOT do: it does not check consistency in the
`check_consistency.py` sense (that the theory does not derive False).
For a standalone file, the kernel's own elaboration plus (2) is the
available proxy: with no axioms and no sorries, every closed proof was
verified, and every remaining hypothesis travels explicitly in the
theorem signatures where the reader can see it.

Run:  python3 scripts/test_best_standalone.py [path/to/best.lean]
Exit: 0 = clean; 1 = failure (message on stdout).
"""

from __future__ import annotations

import io
import os
import re
import subprocess
import sys

BEST_LEAN = sys.argv[1] if len(sys.argv) > 1 and not sys.argv[1].startswith("-") else "best.lean"


def strip_comments_and_strings(text: str) -> str:
    """Blank out block comments and string literals, keep line numbers."""
    out = []
    i, n = 0, len(text)
    depth = 0  # Lean block comments nest
    while i < n:
        if depth == 0 and text.startswith('"', i):
            i += 1
            while i < n:
                if text[i] == "\\":
                    i += 2
                    continue
                if text[i] == '"':
                    i += 1
                    break
                if text[i] == "\n":
                    out.append("\n")
                i += 1
            continue
        if text.startswith("/-", i):
            depth += 1
            out.append("  ")
            i += 2
            continue
        if depth > 0 and text.startswith("-/", i):
            depth -= 1
            out.append("  ")
            i += 2
            continue
        if depth > 0:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


DECL_RE = re.compile(
    r"^(theorem|def|structure|inductive|instance|abbrev|lemma|example|axiom)\s+"
    r"([A-Za-z_][A-Za-z0-9_'!?]*)"
)
PRINT_AXIOMS_RE = re.compile(r"^#print\s+axioms\s+(\S+)\s*$")


def lean_env() -> dict:
    env = dict(os.environ)
    elan = os.path.expanduser("~/.elan/bin")
    if os.path.isdir(elan) and elan not in env.get("PATH", ""):
        env["PATH"] = elan + os.pathsep + env.get("PATH", "")
    return env


def main() -> int:
    failures: list[str] = []

    try:
        raw = io.open(BEST_LEAN, encoding="utf-8").read()
    except OSError as exc:
        print("FAIL: cannot read %s: %s" % (BEST_LEAN, exc))
        return 1

    code = strip_comments_and_strings(raw)
    lines = code.split("\n")

    # --- (2) no escape hatches -------------------------------------------
    forbidden = {"sorry": 0, "admit": 0}
    axiom_decls: list[tuple[int, str]] = []
    for no, line in enumerate(lines, 1):
        for tok in ("sorry", "admit"):
            if re.search(r"\b%s\b" % tok, line):
                forbidden[tok] += 1
                if forbidden[tok] == 1:
                    failures.append(
                        "escape hatch `%s` in code (first at line %d)"
                        % (tok, no))
        m = re.match(r"^axiom\s+([A-Za-z_][A-Za-z0-9_'!?]*)", line)
        if m:
            axiom_decls.append((no, m.group(1)))
    for no, name in axiom_decls:
        failures.append("axiom declaration `%s` at line %d" % (name, no))

    # --- (3) audit coverage ----------------------------------------------
    declared = set()
    for line in lines:
        d = DECL_RE.match(line)
        if d:
            declared.add(d.group(2))
    unaudited = []
    for no, line in enumerate(lines, 1):
        m = PRINT_AXIOMS_RE.match(line.strip())
        if m:
            short = m.group(1).split(".")[-1]
            if short not in declared:
                unaudited.append((no, m.group(1)))
    for no, full in unaudited:
        failures.append(
            "#print axioms names undeclared `%s` (line %d)" % (full, no))

    # --- (1) compile-clean ------------------------------------------------
    try:
        r = subprocess.run(["lean", BEST_LEAN], capture_output=True,
                           text=True, timeout=900, env=lean_env())
    except FileNotFoundError:
        failures.append("`lean` not found (expected ~/.elan/bin/lean)")
        r = None
    except subprocess.TimeoutExpired:
        failures.append("`lean best.lean` timed out after 900s")
        r = None
    if r is not None and r.returncode != 0:
        failures.append("`lean %s` exits %d" % (BEST_LEAN, r.returncode))
        for line in (r.stderr + r.stdout).splitlines():
            if "error" in line.lower():
                failures.append("  lean: %s" % line.strip())
                if len(failures) > 12:
                    break

    print()
    print("escape hatches (sorry/admit/axiom): %s"
          % ("none" if not any(forbidden.values()) and not axiom_decls
             else "FOUND"))
    print("audit lines checked, undeclared: %d" % len(unaudited))
    if failures:
        print("\nFAIL (%d):" % len([f for f in failures
                                    if not f.startswith("  lean:")]))
        for f in failures:
            print("  - %s" % f)
        return 1
    print("\nPASS: best.lean compiles clean with no escape hatches.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
