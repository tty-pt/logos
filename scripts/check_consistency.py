#!/usr/bin/env python3
"""Fail the build if the kernel derives `False`, or if an axiom equates a subject with the ground.

Four complementary gates, none of which the existing audit suite could see (`AGENTS.md`
(sync rule and gates)). Gates A and B came out of plan S4; Gates C and D came out of the
2026-10-03 Trinity incident, where the corpus had been deriving `False` and a full green
`make all` certified nothing.

**Gate A — negative compilation.** `formal/consistency/FalseNotDerivable.lean` closes `False`
from `TrinitarianPersonalBridge` + `ofGround_ne_ofSubject`. It must FAIL to compile. A clean
compile means the axiom again equates a divine person with the ground and the theory is
inconsistent. The gate rejects the three ways a negative compile passes for the wrong reason: a
timeout, a memory kill, and a depth-limit crash — each of which is a non-answer rather than a
refutation. It also rejects an error raised inside `Logos/` itself, because a broken import makes
the guard fail for a reason that has nothing to do with the guard.

**Gate B — syntactic scan.** Rejects the *shape* anywhere in an `axiom` statement, which is
position-exact and covers the orientations and placements the negative-compile probe is pinned
away from. Scanning axiom statements only is sufficient, not lazy: a `theorem` asserting
`EntityOf s = Entity.ofGround` can only be proved if some axiom supplies the equality, and Gate A
catches that.

**Gate C — per-axiom refutation probes.** For each declared axiom `P`, the gate compiles
`P → False`. Any probe that *compiles* is a gate failure, for the same reason a clean Gate A
compile is: `¬P` together with the axiom `P` gives `False`. This is the gate that catches the
`DivineHypostasis` pinhole. It is sound but incomplete — it attributes an inconsistency to a
single axiom, not to a pair — which is why Gate D exists. Every probe has a twin whose goal is
`True`, which must compile; a failing mutant means the harness is broken, not that the axiom is
sound.

**Gate D — pinhole scan.** The generalisation: a `structure` with one field, pinned to a constant
by a `def`, has a singleton `P`-subsatisfying subset, so a declared axiom asserting two distinct
`P`-inhabitants makes the theory explode. Written as a product of syntactic facts plus
axiom-reachability, not as hand-listed shapes.

Why none of this was already covered: `audit_footprints.py` forbids `sorryAx`, and `#print axioms`
reports a declaration's axiom set without ever asking whether the theory is consistent. An
inconsistent theory prints the same "0 substantive axioms" rows as a sound one, which is exactly
how a derived `False` hid behind every badge and every reader-facing price.

Usage:
  python3 scripts/check_consistency.py
Exit 0 iff all four gates pass. Stdlib only; runs one Lean process at a time.
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

# The declared-axiom count, pinned at 40 (18 VOCAB, 6 SEM, 13 META, 3 TRANS).
#
# Milestone 2026-10-08: `GroundTranscendence` (unrestricted META) was deleted and replaced by
# `DivinePersonsTotalMeaning` (Tag: META), which affirms the semantic fullness of the divine Persons,
# while `SemanticFinitude` (Tag: VOCAB) restricts finitude to contingent creatures.
# The total declared axiom count is invariant: 39 statements (18 VOCAB, 6 SEM, 13 META, 2 TRANS).
#
# Why pin an axiom count at all: deleting an axiom is the one edit that silently lowers every
# price in the corpus. No badge moves, no audit fails -- `axiom_audit.json` simply reports one
# fewer, and a reader-facing "0 substantive axioms" row stays just as green. So the count is
# compared against a recorded baseline and a mismatch FAILS, which turns a silent edit into a
# loud one. Bumping this constant is a deliberate act in a reviewable diff, which is the point.
#
# Corrected census baseline: 40 = 18 VOCAB + 6 SEM + 13 META + 3 TRANS, agreed by `depgraph.json`
# and verified by `scripts/test_axiom_census.py`.
EXPECTED_AXIOM_STATEMENTS = 40

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


def lean_code_lines(lines: list[str]) -> list[str]:
    """Each line with every Lean comment deleted, newlines and offsets preserved.

    One index in, one index out, and `result[i]` corresponds to `lines[i]`. Comment text is
    removed *and replaced by nothing*, so a line that is entirely inside a `/- -/` block becomes
    the empty string while the real code on either side of an inline `/- note -/` survives.

    This is the projection the **census fix alone did not reach.** `lean_comment_lines` hardens
    `axiom_statements`, but `build_deduction.parse_lean_sources` — the parser feeding GAPMAP, the
    spine, the chain steps and the badges — used a per-line `strip_block_comments`, which cannot
    know that a line is the middle of a multi-line block. `formal/Logos/Value.lean`'s retirement
    note quotes the withdrawn `AxTwoSubjects`, and with the keyword at line start the parser
    reported `Logos.Value.AxTwoSubjects | kind= axiom | tag=` — a live phantom axiom with an
    empty tag, so `gapmap_taxonomy.py` printed `40 total / 39 tagged` while the kernel holds 39.
    The count pin could not see it: its own parser was already correct.

    String and character literals are tracked, so a `--` or `/-` inside one is not a comment.
    """
    out: list[str] = []
    depth = 0
    in_str = False
    in_chr = False
    for raw in lines:
        buf: list[str] = []
        i, n = 0, len(raw)
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
                    buf.append(raw[i:i + 2])
                    i += 2
                elif raw[i] == '"':
                    in_str = False
                    buf.append(raw[i])
                    i += 1
                else:
                    buf.append(raw[i])
                    i += 1
                continue
            if in_chr:
                if raw[i] == "\\":
                    buf.append(raw[i:i + 2])
                    i += 2
                elif raw[i] == "'":
                    in_chr = False
                    buf.append(raw[i])
                    i += 1
                else:
                    buf.append(raw[i])
                    i += 1
                continue
            if raw.startswith("--", i):
                break  # rest of the line is a comment
            if raw.startswith("/-", i):
                depth += 1
                i += 2
                continue
            if raw.startswith("-/", i):
                # A stray closer with no opener: not a comment opener, keep it as text.
                buf.append(raw[i:i + 2])
                i += 2
                continue
            if raw[i] == '"':
                in_str = True
                buf.append(raw[i])
                i += 1
                continue
            if raw[i] == "'" and i + 2 < n and raw[i + 2] == "'":
                in_chr = True
                buf.append(raw[i:i + 3])
                i += 3
                continue
            buf.append(raw[i])
            i += 1
        out.append("".join(buf))
    return out


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

    For a line that mixes code and a comment (`/- note -/ axiom Foo`), this reports True while
    `lean_code_lines` still reports `Foo` as code. That difference is deliberate and the mask is
    the right answer for an anchored `^axiom` regex, which cannot match mid-line anyway; a
    declaration scanner wants the code projection instead.
    """
    code = lean_code_lines(lines)
    return [c.strip() == "" for c in code]

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


# --------------------------------------------------------------------------
# Gate C: per-axiom refutation probes, with a mandatory mutant control
# --------------------------------------------------------------------------
#
# What this gate asks, per declared axiom `P`: is `¬P` derivable? If yes, the theory
# derives `P` (it is an axiom) and `¬P`, hence `False`. So **any probe that compiles is a
# gate failure**, exactly like Gate A's clean compile.
#
# This is the gate that would have caught the 2026-10-03 Trinity incident. `AxAgapeEssence`
# asserts `o ≠ f` with both subsisting, and `Subsists d := d.deiformEntity = divineReality`
# over the one-field `structure DivineHypostasis` makes the subsisting subset a singleton, so
# `¬AxAgapeEssence` is derivable at `{}`. Neither Gate A nor Gate B could see it: the defect
# lives in a `def` plus a structure's arity, and no axiom statement contains either ingredient.
#
# Two honesty notes, because a gate that overstates itself is worse than no gate:
#
#  * **Sound but incomplete.** Each probe is one axiom against the *whole* corpus, so this
#    catches any inconsistency attributable to a single axiom. A `P ∧ Q → False` that is not
#    attributable to `P` or to `Q` alone is NOT caught. Gate D exists because it generalizes
#    over the *shape* rather than over the axiom, which is the half this one cannot see.
#  * **The mutant control is not optional.** A probe whose *statement* is mis-extracted (a
#    wrapped statement, a stray comment, a typo) fails to elaborate for the wrong reason and
#    reads as "consistent". So every probe has a twin whose goal is `True` instead of `False`,
#    which **must** compile. A mutant that fails means the harness is broken, not that the
#    axiom is sound — the same "a green compile of the guard is a failure" discipline as
#    Gate A, in the opposite direction.

REFUTE_TMP = FORMAL / ".consistency_axiom_refutations.lean"
MUTANT_TMP = FORMAL / ".consistency_axiom_mutants.lean"
PRINT_TMP = FORMAL / ".consistency_axiom_statements.lean"

# Refutation attempts, by axiom name. An axiom absent from this table gets the placeholder
# body, which asserts that no refutation is known -- it fails to compile, so the gate passes
# over it without claiming anything stronger.
#
# The two bodies below are the defect itself. They are written against the ONE-field
# structure, so after the second field is added they stop elaborating and the gate turns green
# on its own: the fix is what discharges the probe, not an edit to this file.
REFUTATION_BODIES = {
    "AxAgapeEssence": """  intro h
  obtain ⟨f, hf, o, hne, ho, _⟩ := h
  obtain ⟨ff⟩ := f
  obtain ⟨oo⟩ := o
  dsimp [Logos.DivineAgape.Subsists, Logos.DivineAgape.divineReality] at hf ho
  simp_all""",
    "AxProcessionSpirit": """  intro h
  obtain ⟨σ, _, hσ, hne, _⟩ := h
  have eq_of_subsists : ∀ a b : Logos.DivineAgape.DivineHypostasis,
      Logos.DivineAgape.Subsists a → Logos.DivineAgape.Subsists b → a = b := by
    intro a b ha hb
    cases a
    cases b
    simp_all [Logos.DivineAgape.Subsists, Logos.DivineAgape.divineReality]
  exact hne (eq_of_subsists σ Logos.DivineAgape.the_father hσ
    Logos.DivineAgape.the_father_subsists)""",
}

NO_REFUTATION = """  intro h
  contradiction"""

GENERATED_HEADER = """/- GENERATED by scripts/check_consistency.py (Gate C). Do not edit; do not commit. -/
import Logos
"""


def enclosing_namespace(path: Path, line: int) -> str:
    """The `namespace` block containing 1-based `line`, from the file itself.

    Derived, not guessed from the filename: the corpus puts every declaration in
    `namespace Logos.<ModuleStem>`, but that is a convention, and a probe that assumed it
    would silently fail to resolve `the_father` or `N_T` on the day it stops holding. A
    statement is copied verbatim from its source, so it must be read under the same name
    scope it was written in.
    """
    lines = path.read_text().splitlines()
    stack: list[str] = []
    for raw in lines[: line - 1]:
        m = re.match(r"^namespace\s+(\S+)", raw)
        if m:
            stack.append(m.group(1))
            continue
        m = re.match(r"^end\s+(\S+)", raw)
        if m and stack and stack[-1] == m.group(1):
            stack.pop()
    if not stack:
        return "Logos.Consistency.AxiomProbes"
    return stack[-1]


def axiom_inventory() -> list[tuple[str, str, int, Path, str, str]]:
    """(name, source-text statement, line, path, tag, namespace) for every declared axiom."""
    out = []
    for path in SOURCES:
        for name, statement, line in axiom_statements(path):
            body = statement[len(f"axiom {name}"):].lstrip()
            if body.startswith(":"):
                body = body[1:].strip()
            out.append((name, body, line, path, axiom_tag(path, line),
                        enclosing_namespace(path, line)))
    return out


def kernel_statements(inventory: list[tuple[str, str, int, Path, str, str]]) -> dict[str, str]:
    """The kernel's own type for every axiom, keyed by full name.

    The probe statement is taken from `#check` under `pp.fullNames` rather than from the
    source text, and this is not a stylistic preference. An earlier version copied the
    statement verbatim out of the `.lean` file and the mutant control caught it within
    minutes: `ground_love_produces` names `Entity.ofGround`, which does not resolve from
    `namespace Logos.ThomisticAct` because `Logos.Entity` was never opened. Getting that
    right in Python means either opening ~136 namespaces — which collides, e.g. `Means`,
    `State`, `Ought`, `Person` and `Choses` are each declared in several of them — or
    re-deriving name resolution by hand. The kernel already did it; asking it is both
    shorter and correct by construction. It also retires the extraction hazards (wrapped
    statements, inline comments, line continuations) that the mutant control exists to
    catch, and every axiom here is monomorphic, so no `.{u}` noise appears.

    Wrapped output is re-joined: a record starts at a line matching `<full> : ` and
    continues on the following indented lines.
    """
    body = ["import Logos"]
    for name, _, _, _, _, ns in inventory:
        body.append("set_option pp.fullNames true in")
        body.append(f"#check @{ns}.{name}")
    PRINT_TMP.write_text("\n".join(body) + "\n", encoding="utf-8")
    try:
        rc, out = run_lean(PRINT_TMP)
    finally:
        PRINT_TMP.unlink(missing_ok=True)
    if rc != 0:
        return {}
    types: dict[str, str] = {}
    current: str | None = None
    for raw in out.splitlines():
        if not raw.strip():
            continue
        if not raw[0].isspace() and " : " in raw:
            full, _, rest = raw.partition(" : ")
            current = full.strip()
            types[current] = rest.strip()
        elif current and raw[0].isspace():
            types[current] += " " + raw.strip()
    return types


def run_lean(path: Path) -> tuple[int, str]:
    """`lake env lean` on one generated file; one Lean process at a time (AGENTS.md)."""
    cmd = lean_prefix() + ["lake", "env", "lean", str(path.relative_to(FORMAL))]
    proc = subprocess.run(cmd, cwd=FORMAL, capture_output=True, text=True, timeout=TIMEOUT_S)
    return proc.returncode, proc.stdout + proc.stderr


def _emit(blocks: list[tuple[str, str, str]], path: Path) -> list[tuple[str, int, int]]:
    """Write a generated file from (theorem_name, namespace, body) blocks; return spans.

    Each block's line span is returned so an elaborated failure can be attributed to the
    axiom that caused it: Lean's error position is the failing tactic, not the declaration.
    """
    lines: list[str] = [GENERATED_HEADER.rstrip("\n")]
    spans: list[tuple[str, int, int]] = []
    for name, ns, body in blocks:
        lines.append("")
        lines.append(f"namespace {ns}")
        start = len(lines) + 1
        lines.extend(body.rstrip("\n").split("\n"))
        lines.append(f"end {ns}")
        spans.append((name, start, len(lines)))
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return spans


def gate_c_axiom_refutation() -> list[str]:
    """Return a list of problems; empty means no declared axiom is refuted."""
    problems: list[str] = []
    inventory = axiom_inventory()
    if not inventory:
        return ["no declared axioms found to probe — the inventory is derived and must not be empty"]

    kernel = kernel_statements(inventory)
    refutation_blocks: list[tuple[str, str, str]] = []
    mutant_blocks: list[tuple[str, str, str]] = []
    probed: list[tuple[str, int, Path]] = []
    for name, _src, line, path, _tag, ns in inventory:
        full = f"{ns}.{name}"
        statement = kernel.get(full)
        if statement is None:
            problems.append(
                f"{path.relative_to(ROOT)}:{line}: the kernel reported no type for `{full}` — "
                "the probe would be stated from source text, which is the failure mode the "
                "mutant control exists to prevent. Not probing is not passing."
            )
            continue
        body = REFUTATION_BODIES.get(name, NO_REFUTATION)
        refutation_blocks.append((name, ns, f"theorem refute_{name} :\n"
                                f"    ({statement}) → False := by\n{body}"))
        mutant_blocks.append((name, ns, f"theorem mutant_{name} (h : {statement}) :\n"
                              f"    True := by\n  trivial\n"))
        probed.append((name, line, path))

    if not probed:
        return problems

    try:
        r_spans = _emit(refutation_blocks, REFUTE_TMP)
        _emit(mutant_blocks, MUTANT_TMP)
        mrc, mout = run_lean(MUTANT_TMP)
        rrc, rout = run_lean(REFUTE_TMP)
    finally:
        REFUTE_TMP.unlink(missing_ok=True)
        MUTANT_TMP.unlink(missing_ok=True)

    # -- the mutant control: every twin must compile, or the harness is broken ------------
    if mrc != 0:
        problems.append(
            f"the mutant control FAILED ({mrc}) — at least one axiom statement could not be "
            "stated, so the refutation probes are unreadable. This is a harness failure, not a "
            "soundness result. Raw output follows:"
        )
        for line in (mout.strip().splitlines() or ["(no output)"])[:20]:
            problems.append(f"    {line}")

    # -- the probes: any axiom whose block elaborated without error is refuted ------------
    err_re = re.compile(re.escape(REFUTE_TMP.name) + r":(\d+):\d+: error:")
    err_lines = sorted({int(n) for n in err_re.findall(rout)})
    if rrc == 0:
        problems.append(
            "the refutation probe file COMPILED CLEANLY — that is the intended state, but it "
            "also means no probe failed to elaborate, so nothing was tested. Treat this as a "
            "harness failure and read the generated file."
        )
    unattributed = [n for n in err_lines if not any(lo <= n <= hi for _, lo, hi in r_spans)]
    if unattributed:
        problems.append(
            f"{len(unattributed)} error line(s) in the probe file fall outside every probe block "
            f"(lines {unattributed[:8]}) — the generated file is not what Gate C expects"
        )
    refuted = [
        (name, line, path)
        for (name, lo, hi), (_, line, path) in zip(r_spans, probed)
        if not any(lo <= n <= hi for n in err_lines)
    ]
    for name, line, path in refuted:
        problems.append(
            f"DECLARED AXIOM IS REFUTABLE: `Logos` derives `¬ {name}` "
            f"({path.relative_to(ROOT)}:{line}). The axiom is also derivable, so the theory "
            "derives `False` and every badge and price in the corpus is vacuous."
        )
    print(f"  probed {len(r_spans)} axiom(s): {len(r_spans) - len(refuted)} not refuted, "
          f"{len(refuted)} refutable; mutant control "
          f"{'compiled' if mrc == 0 else 'FAILED'}")
    return problems


# --------------------------------------------------------------------------
# Gate D: pinhole scan
# --------------------------------------------------------------------------
#
# The generalisation of the 2026-10-03 incident, and the half Gate C structurally cannot see.
#
# A **pinhole** is a product of two independent syntactic facts:
#
#   1. a `structure S` with exactly ONE constructor field `f`, and
#   2. a `def P (x : S) : Prop := x.f = <closed term not mentioning x>`.
#
# Then the `P`-subsatisfying subset of `S` is a singleton: two inhabitants with the same field
# are equal by structure eta. A one-field structure is perfectly legal on its own —
# `PracticalAction` (`OughtRetorsion.lean:54`) is one and is used by `Ought` without incident —
# and so is a pinning def. The **explosion needs the third ingredient**: a declared axiom
# asserting two *distinct* `P`-inhabitants. That is what the axiom-reachability half checks.
#
# Written as a product of the two facts, not as one regex per hand-written whole shape, for the
# reason Gate B records: hand-listing shapes is how three of eight went missing there. And the
# third fact is checked by *reachability from a declared axiom* rather than by trying to pattern
# match `∃ x y, P x ∧ P y ∧ x ≠ y`, which is a shape with unboundedly many spellings.

PIN_DEF_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?def\s+([A-Za-z_][\w'.]*)"
    r"\s*\(\s*([a-zA-Z_][\w'.]*)\s*:\s*([A-Za-z_][\w'.]*)\s*\)"
    r"\s*:\s*Prop\s*:=\s*"
)
PIN_EQ_RE = re.compile(r"^\s*([a-zA-Z_][\w'.]*)\.([a-zA-Z_][\w'.]*)\s*=\s*(.+?)\s*$")
STRUCT_RE = re.compile(r"^structure\s+([A-Za-z_][\w'.]*)\s+where\s*$")
FIELD_RE = re.compile(r"^\s+([a-zA-Z_][\w'.]*)\s*:")


def single_field_structures() -> list[tuple[str, str, int, Path]]:
    """(structure, field, line, path) for every structure with exactly one field."""
    out = []
    for path in SOURCES:
        lines = path.read_text().splitlines()
        masked = lean_comment_lines(lines)
        i = 0
        while i < len(lines):
            if masked[i]:
                i += 1
                continue
            m = STRUCT_RE.match(lines[i])
            if not m:
                i += 1
                continue
            name = m.group(1)
            i += 1
            fields: list[tuple[str, int]] = []
            while i < len(lines):
                if lines[i].strip() and not lines[i][0].isspace():
                    break
                if not masked[i]:
                    fm = FIELD_RE.match(lines[i])
                    if fm:
                        fields.append((fm.group(1), i + 1))
                i += 1
            if len(fields) == 1:
                out.append((name, fields[0][0], fields[0][1], path))
    return out


def pinning_defs() -> list[tuple[str, str, str, int, Path]]:
    """(def, binder, structure, line, path) for every def pinning one field to a constant.

    The body may sit on the def line or on the lines after it — `Subsists` is the wrapped
    form — so the body is gathered by the same continuation convention as `axiom_statements`:
    every line until one that is neither blank nor indented.
    """
    out = []
    for path in SOURCES:
        lines = path.read_text().splitlines()
        masked = lean_comment_lines(lines)
        i = 0
        while i < len(lines):
            if masked[i]:
                i += 1
                continue
            m = PIN_DEF_RE.match(lines[i])
            if not m:
                i += 1
                continue
            body = [lines[i][m.end():]]
            start = i
            i += 1
            while i < len(lines):
                if lines[i].strip() and not lines[i][0].isspace():
                    break
                body.append(lines[i])
                i += 1
            em = PIN_EQ_RE.match(" ".join(body))
            if not em:
                continue
            binder = m.group(2)
            if re.search(rf"\b{re.escape(binder)}\b", em.group(3)):
                continue  # RHS mentions the binder: not a pin
            out.append((m.group(1), binder, m.group(3), start + 1, path))
    return out


# Axion names allowed to reach a pinhole, with the reason each exemption exists. Empty today:
# after the second `DivineHypostasis` field there is no pinhole to reach.
PINHOLE_EXEMPTIONS: dict[str, str] = {}


def gate_d_pinhole_scan() -> list[str]:
    """Return a list of problems; empty means no declared axiom reaches a pinhole."""
    problems: list[str] = []
    structures = {name: (field, line, path) for name, field, line, path in
                  single_field_structures()}
    pins = [(d, b, s, ln, p) for d, b, s, ln, p in pinning_defs() if s in structures]
    if not structures:
        print("  no one-field structures found — the scan is derived and must not be empty")
        return problems
    for name, (field, line, path) in sorted(structures.items()):
        reached = [(ax, ln, axpath) for ax, stmt, ln, axpath, _, _ in axiom_inventory()
                   if re.search(rf"\b{re.escape(name)}\b|\b{re.escape(field)}\b", stmt)]
        hits = [(d, dln, dpath) for d, b, s, dln, dpath in pins if s == name]
        if not hits:
            print(f"  one-field structure `{name}` ({path.relative_to(ROOT)}:{line}, field "
                  f"`{field}`) has no pinning def — legal, like `PracticalAction`")
            continue
        if not reached:
            print(f"  pinhole `{name}.{field} = <constant>` exists but no declared axiom reaches "
                  "it — inert")
            continue
        for d, dln, dpath in hits:
            print(f"  pinhole: `{name}` ({path.relative_to(ROOT)}:{line}, one field `{field}`) "
                  f"pinned by `{d}` ({dpath.relative_to(ROOT)}:{dln})")
        for ax, axln, axpath in reached:
            if ax in PINHOLE_EXEMPTIONS:
                continue
            problems.append(
                f"{axpath.relative_to(ROOT)}:{axln}: axiom `{ax}` reaches pinhole "
                f"`{name}.{field} = <constant>` (structure at {path.relative_to(ROOT)}:{line}, "
                f"pinning def `{d}` at {dpath.relative_to(ROOT)}:{dln}). The `P`-subsatisfying "
                "subset of a one-field structure is a singleton, so an axiom asserting two "
                "distinct `P`-inhabitants makes `P` refutable and the theory inconsistent. Give "
                "the structure a second field (which is what removes the pinhole), or record an "
                f"exemption in PINHOLE_EXEMPTIONS with its reason: {PINHOLE_EXEMPTIONS}"
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
    print("\nGate C — per-axiom refutation probes (no declared axiom may be refuted)")
    c = gate_c_axiom_refutation()
    print("\nGate D — pinhole scan (no one-field structure pinned to a constant)")
    d = gate_d_pinhole_scan()

    problems = a + b + c + d
    if problems:
        print("\nCONSISTENCY GATE FAILED")
        for line in problems:
            print(f"  !! {line}")
        return 1
    print("\nCONSISTENCY GATE PASSED: the kernel does not derive False, no axiom identifies a "
          "subject with the ground, no declared axiom is refuted, and no one-field structure is "
          "pinned to a constant.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())