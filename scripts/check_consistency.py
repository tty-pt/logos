#!/usr/bin/env python3
"""Fail the build if the kernel derives `False`, or if an axiom equates a subject with the ground.

Two complementary gates over plan S4's consistency defect, neither of which the existing
audit suite could see (`AGENTS.md` (sync rule and gates)):

**Gate A — negative compilation.** `formal/consistency/FalseNotDerivable.lean` closes `False`
from `TrinitarianPersonalBridge` + `ofGround_ne_ofSubject`. It must FAIL to compile. A clean
compile means the axiom again equates a divine person with the ground and the theory is
inconsistent. The gate rejects the three ways a negative compile passes for the wrong reason: a
timeout, a memory kill, and a depth-limit crash — each of which is a non-answer rather than a
refutation. It also rejects an error raised inside `Logos/` itself, because a broken import makes
the guard file fail for a reason that has nothing to do with the guard.

**Gate B — syntactic scan.** Rejects the *shape* anywhere in an `axiom` statement, which is
position-exact and covers the orientations and placements the negative-compile probe is pinned
away from. Scanning axiom statements only is sufficient, not lazy: a `theorem` asserting
`EntityOf s = Entity.ofGround` can only be proved if some axiom supplies the equality, and Gate A
catches that.

Why this is not already covered: `audit_footprints.py` forbids `sorryAx`, and `#print axioms`
reports a declaration's axiom set without ever asking whether the theory is consistent. An
inconsistent theory prints the same "0 substantive axioms" rows as a sound one, which is exactly
how a derived `False` hid behind every badge and every reader-facing price.

Usage:
  python3 scripts/check_consistency.py
Exit 0 iff both gates pass. Stdlib only; runs one Lean process at a time.
"""

from __future__ import annotations

import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FORMAL = ROOT / "formal"
GUARD = FORMAL / "consistency" / "FalseNotDerivable.lean"
SOURCES = sorted((FORMAL / "Logos").glob("*.lean"))

TIMEOUT_S = 900

# The declared-axiom count, as measured after plan step S5 (40 statements: 18 VOCAB, 7 SEM,
# 13 META, 2 TRANS). This is a *pin*, and it is the only hard number in the gate.
#
# S5 took this from 39 to 40: `SemanticFinitude` was split, and the unrestricted half became
# the separate `Tag: META` axiom `GroundTranscendence`. The count moved because a *price* was
# named, not because a claim was added -- see the plan's §8.2.
#
# Why pin an axiom count at all: deleting an axiom is the one edit that silently lowers every
# price in the corpus. No badge moves, no audit fails -- `axiom_audit.json` simply reports one
# fewer, and a reader-facing "0 substantive axioms" row stays just as green. So the count is
# compared against a recorded baseline and a mismatch FAILS, which turns a silent edit into a
# loud one. Bumping this constant is a deliberate act in a reviewable diff, which is the point.
#
# The audit *sizes* (declarations in `axiom_audit.json`, records in `goal_audit.json`) are NOT
# pinned here: they move with every theorem and def authored, so a pin there would fire on
# ordinary progress. They are checked by `scripts/test_goal_audit.py` instead.
#
# This was 40 until 2026-10-03, and the extra 1 was not an axiom: `Logos/AsieticChoice.lean:19`
# is the prose line `axiom of Γ**:` inside a `/- -/` comment, and the parser counted it as an
# axiom named `of` (tagged SEM, inherited from the surrounding docstring). So the previous
# baseline of 40 was really 39 axioms plus a phantom, and AGENTS.md's documented census
# "18 VOCAB / 7 SEM / 13 META / 2 TRANS" was really 18 / 6 / 13 / 2. Corrected census:
# 39 = 18 VOCAB + 6 SEM + 13 META + 2 TRANS, agreed by `depgraph.json` and by the registry
# `build_deduction.py` prints. S5 therefore moved the count 38 -> 39, not 39 -> 40.
EXPECTED_AXIOM_STATEMENTS = 39

# Tag vocabulary, per AGENTS.md. `build_deduction.py` already refuses to regenerate when an
# axiom's tag is missing or outside this set; it is repeated here so this gate's census is
# self-contained and so the printed breakdown is derived rather than hard-coded.
VALID_TAGS = ("VOCAB", "SEM", "META", "TRANS")

# --------------------------------------------------------------------------
# Gate A: the negative-compilation probe
# --------------------------------------------------------------------------

# A failed elaboration, which is the intended outcome.
ELABORATION_ERROR_RE = re.compile(r"error:", re.M)
# An error raised inside the library rather than inside the guard.
LOGOS_ERROR_RE = re.compile(r"Logos/[\w.]*\.lean:\d+:\d+: error:")
# Non-answers: the process died or gave up rather than refuting the term.
BAD_FAILURES = (
    "resource exhausted",
    "maximum recursion depth",
    "maximum call depth",
    "deterministic timeout",
    "out of memory",
    "heap overflow",
    "no space left",
)
GUARD_ERROR_RE = re.compile(r"FalseNotDerivable\.lean:(\d+):(\d+): error:")


def lean_prefix() -> list[str]:
    """`taskset -c 0-3` when available (one Lean process at a time, per AGENTS.md)."""
    if shutil.which("taskset"):
        return ["taskset", "-c", "0-3"]
    return []


def gate_a_negative_compile() -> list[str]:
    """Return a list of problems; empty means the guard bit as required."""
    if not GUARD.exists():
        return [f"guard file missing: {GUARD.relative_to(ROOT)}"]

    cmd = lean_prefix() + ["lake", "env", "lean", str(GUARD.relative_to(FORMAL))]
    try:
        proc = subprocess.run(
            cmd, cwd=FORMAL, capture_output=True, text=True, timeout=TIMEOUT_S
        )
    except subprocess.TimeoutExpired:
        return [f"guard TIMED OUT after {TIMEOUT_S}s — a timeout is not a refutation"]

    out = proc.stdout + proc.stderr
    problems: list[str] = []

    if proc.returncode == 0:
        problems.append(
            "guard COMPILED CLEANLY: `False` is derivable — the kernel is inconsistent. "
            "This is the failure this gate exists to report."
        )
        return problems

    if proc.returncode < 0:
        problems.append(f"guard killed by signal {-proc.returncode} — a crash is not a refutation")

    low = out.lower()
    for marker in BAD_FAILURES:
        if marker in low:
            problems.append(f"guard failed with {marker!r} — a resource failure is not a refutation")

    if not ELABORATION_ERROR_RE.search(out):
        problems.append("guard exited non-zero without an `error:` — not an elaboration failure")

    library_errors = LOGOS_ERROR_RE.findall(out)
    if library_errors:
        problems.append(
            f"{len(library_errors)} error(s) inside Logos/ itself — the guard's imports are "
            "broken, so this is not a refutation"
        )
        for line in library_errors:
            problems.append(f"    {line}")

    guard_errors = GUARD_ERROR_RE.findall(out)
    if not guard_errors:
        problems.append("no error located inside the guard file — see the raw output above")

    if not problems:
        rows = sorted({f"{line}:{col}" for line, col in guard_errors})
        print(f"  guard fails to elaborate as required, at {', '.join(rows)}")
        detail = re.findall(r"FalseNotDerivable\.lean:\d+:\d+: error:.*", out)
        for line in detail[:4]:
            print(f"    {line.strip()}")
    return problems


# --------------------------------------------------------------------------
# Gate B: the syntactic scan over axiom statements
# --------------------------------------------------------------------------

AXIOM_RE = re.compile(r"^axiom\s+([A-Za-z_][A-Za-z0-9_'.]*)", re.M)


def lean_comment_lines(lines: list[str]) -> list[bool]:
    """True for each line lying inside a Lean comment: `--` to end of line, or `/- -/`, nestable.

    This exists because the corpus quotes axiom statements in prose. `Logos/AsieticChoice.lean:19`
    reads `axiom of Γ**:` -- a markdown emphasis inside the module's `/- -/` comment -- and the
    anchored regex counted it as an axiom named `of`. That put the census at 40 when the kernel
    holds 39, and it did so *silently*, because a phantom is exactly what a count cannot see.
    Three sources now agree the kernel holds 39 declared axioms: `depgraph.json` (39 `axiom`
    nodes, from a real Lean parser), the dynamic registry `build_deduction.py` prints (39), and
    this function once comments are skipped (39).

    It was also a laundering vector in the one edit the pin exists to catch: delete a real axiom
    and add any comment line beginning `axiom `, and the count holds steady, so the gate stays
    green while every price in the corpus silently drops.

    String literals are tracked so a `--` or `/-` inside one is not read as a comment opener.
    """
    mask: list[bool] = []
    depth = 0  # block-comment nesting depth
    in_str = False
    in_chr = False
    for raw in lines:
        began_in_comment = depth > 0
        i = 0
        n = len(raw)
        while i < n:
            if depth > 0:
                if raw.startswith("/-", i):
                    depth += 1
                    i += 2
                elif raw.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
                continue
            if in_str:
                if raw[i] == "\\":
                    i += 2
                elif raw[i] == '"':
                    in_str = False
                    i += 1
                else:
                    i += 1
                continue
            if in_chr:
                if raw[i] == "\\":
                    i += 2
                elif raw[i] == "'":
                    in_chr = False
                    i += 1
                else:
                    i += 1
                continue
            if raw.startswith("--", i):
                break  # rest of the line is a comment
            if raw.startswith("/-", i):
                depth += 1
                i += 2
            elif raw[i] == '"':
                in_str = True
                i += 1
            elif raw[i] == "'" and i + 2 < n and raw[i + 2] == "'":
                in_chr = True
                i += 3
            else:
                i += 1
        # Only the opening depth matters for an at-line-start regex: a line that begins in code
        # cannot match `^axiom` anyway, and one that begins in a comment always must be skipped.
        mask.append(began_in_comment or depth > 0)
    return mask

# Whitespace-normalised statement patterns. Whitespace-normalised because the corpus wraps
# statements across lines.
#
# Written as a product rather than as one regex per spelling, because one-regex-per-spelling is
# how three of the eight shapes went missing: `EntityOf` is a *definition* for `Entity.ofSubject`
# (`Entity.lean:29`), so `EntityOf a = divineReality` and `Entity.ofSubject a = divineReality`
# are the same defect under two spellings, and either side may be written first. An earlier
# version of this gate listed 5 patterns and silently failed to reject
# `Entity.ofSubject divineReality = Entity.ofGround` in a negative test.
#
# A subject side and a ground/reality side must never be equated. The gap between the two sides is
# bounded and may not cross `=`, `&`, `|`, `<`, `>` or parentheses, so a match cannot span a
# conjunction into an unrelated clause.
SUBJECT_SIDE = r"(?:EntityOf\b|Entity\.ofSubject\b)"
GROUND_SIDE = r"(?:divineReality\b|Entity\.ofGround\b|EntityOf\b)"
SPAN = r"[^=<>&|()]{1,80}?"

FORBIDDEN = (
    (re.compile(rf"{SUBJECT_SIDE}{SPAN}=\s*{GROUND_SIDE}"),
     "a subject IS the ground or divine reality"),
    (re.compile(rf"{GROUND_SIDE}{SPAN}=\s*{SUBJECT_SIDE}"),
     "the ground or divine reality IS a subject"),
)


def axiom_statements(path: Path) -> list[tuple[str, str, int]]:
    """(name, normalised statement, first line) for each `axiom` in the file.

    An axiom statement is every line from the `axiom` line until the next line
    that is neither blank nor indented -- which is how the corpus formats them.

    Lines inside comments are skipped (`lean_comment_lines`); the corpus quotes axiom
    statements in prose and one such quote was counted as a declaration.
    """
    lines = path.read_text().splitlines()
    masked = lean_comment_lines(lines)
    out: list[tuple[str, str, int]] = []
    i = 0
    while i < len(lines):
        if masked[i] or not AXIOM_RE.match(lines[i]):
            i += 1
            continue
        name = AXIOM_RE.match(lines[i]).group(1)
        start = i
        body = [lines[i]]
        i += 1
        while i < len(lines):
            nxt = lines[i]
            if nxt.strip() and not nxt[0].isspace():
                break
            body.append(nxt)
            i += 1
        out.append((name, " ".join(body), start + 1))
    return out


def axiom_tag(path: Path, line: int) -> str | None:
    """The tag on an axiom's own docstring, or None.

    The docstring is taken as the nearest preceding `/--` opener, and the tag is read from the
    first `Tag:` anywhere inside it. Two traps, both of which produced a wrong census when this
    was written by ad-hoc regex instead:

      * the tag usually sits ON the `/--` line (`/--Tag: VOCAB`), so an anchored-at-line-start
        pattern anchored at the *following* line misses every axiom in `Agency.lean`;
      * scanning upward for the previous `theorem`/`def` keyword matches prose -- the line
        "axiom, so the two halves of the slogan are separately priced." starts with `axiom` and
        truncates the window before the tag.
    """
    lines = path.read_text().splitlines()
    i = line - 1
    openers = [j for j in range(i) if lines[j].lstrip().startswith("/--")]
    start = openers[-1] if openers else 0
    m = re.search(r"Tag:\s*([A-Za-z]+)", "\n".join(lines[start:i]))
    return m.group(1) if m else None


def gate_b_syntactic_scan() -> list[str]:
    problems: list[str] = []
    checked = 0
    census: dict[str, int] = {}
    for path in SOURCES:
        for name, statement, line in axiom_statements(path):
            checked += 1
            tag = axiom_tag(path, line)
            census[tag or "UNTAGGED"] = census.get(tag or "UNTAGGED", 0) + 1
            if tag is None:
                problems.append(
                    f"{path.relative_to(ROOT)}:{line}: axiom `{name}` has no `Tag:` line — "
                    "an untagged axiom is a regeneration error, not a note (AGENTS.md)"
                )
            elif tag not in VALID_TAGS:
                problems.append(
                    f"{path.relative_to(ROOT)}:{line}: axiom `{name}` has tag `{tag}`, outside "
                    f"the closed vocabulary {VALID_TAGS}"
                )
            flat = re.sub(r"\s+", " ", statement)
            for pattern, label in FORBIDDEN:
                if pattern.search(flat):
                    problems.append(
                        f"{path.relative_to(ROOT)}:{line}: axiom `{name}` equates {label} — "
                        "indwelling is not identity"
                    )
    breakdown = ", ".join(f"{census.get(t, 0)} {t}" for t in VALID_TAGS if census.get(t))
    print(f"  scanned {checked} axiom statement(s) across {len(SOURCES)} module(s): {breakdown}")
    if checked != EXPECTED_AXIOM_STATEMENTS:
        problems.append(
            f"axiom count is {checked}, pinned at {EXPECTED_AXIOM_STATEMENTS}. If axioms were "
            "added or removed on purpose, update EXPECTED_AXIOM_STATEMENTS in "
            "scripts/check_consistency.py in the same change — do not leave the drift silent."
        )
    return problems


def main() -> int:
    if shutil.which("lake") is None:
        print("lake not on PATH; export $HOME/.elan/bin first", file=sys.stderr)
        return 2

    print("Gate A — negative compilation (formal/consistency/FalseNotDerivable.lean)")
    a = gate_a_negative_compile()
    print("\nGate B — syntactic scan (no axiom equates a subject with the ground)")
    b = gate_b_syntactic_scan()

    if a or b:
        print("\nCONSISTENCY GATE FAILED")
        for line in a + b:
            print(f"  !! {line}")
        return 1
    print("\nCONSISTENCY GATE PASSED: the kernel does not derive False, and no axiom "
          "identifies a subject with the ground.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())