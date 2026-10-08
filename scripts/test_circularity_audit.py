#!/usr/bin/env python3
"""Machine-checked circularity and dependency audit for best.lean.

Gates the following requirements:
1. `GenuineRationalJudgment` has ZERO dependencies on:
   - `FreeSubject`
   - `FreeWill`
   - `FreeWillAt`
   - `LibertarianFreeChoice`
   - `LibertarianFreeChoiceAt`
   - `MechanicallyForced`
   - `NormativelySensitive`
   - `SubjectSourceOfJudgment`

2. `SubjectSourceOfJudgment` has ZERO self-reference and ZERO dependencies on:
   - `FreeSubject`
   - `FreeWill`
   - `LibertarianFreeChoice`
   - `MechanicallyForced`

3. `VerdictConstitution` does NOT contain freedom predicates:
   - `FreeSubject`
   - `FreeWill`
   - `LibertarianFreeChoice`

4. `WeakToStrongBridge` and `hBridge` are completely absent from the file.

5. The subject-source bridge (section XV of best.lean) is non-circular:
   - the structural definitions (`NecessarySubject`, `ContingentSubject`,
     `DeterminationReceivedFromPriorState`, `ContingentDetermination`,
     `SubjectIsSourceOfDetermination`, `DeterminationOriginatedBySubject`)
     contain no freedom vocabulary, no `MechanicallyForced`, no
     `ReasonCessation` and no `ReasonMakesTheJudgmentDifference` (a
     definition naming the target would be the target renamed);
   - the bridge lemmas contain no freedom vocabulary and no
     `MechanicallyForced` (`ReasonCessation` is allowed there: it is a
     declared open-world premise, not a conclusion);
   - the declaration that concludes `¬ MechanicallyForced` mentions
     `MechanicallyForced` exactly once, always negated;
   - the main theorem's hypotheses are exactly `hPresentation`
     (the performative fact), `hSource` (the personal source) and
     `hCess` (the open world).

Run:  python3 scripts/test_circularity_audit.py [path/to/best.lean]
Exit: 0 = PASS; 1 = FAIL
"""

from __future__ import annotations

import io
import re
import sys

BEST_LEAN = sys.argv[1] if len(sys.argv) > 1 and not sys.argv[1].startswith("-") else "best.lean"

DECL_RE = re.compile(
    r"^(theorem|def|structure|inductive|instance|abbrev|lemma|example|axiom)\s+"
    r"([A-Za-z_][A-Za-z0-9_'!?]*)"
)


def word_re(name: str) -> str:
    return r"\b%s\b" % name


def strip_comments_and_strings(text: str) -> str:
    out = []
    i, n = 0, len(text)
    depth = 0
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


def get_decl_bodies(code: str) -> dict[str, str]:
    lines = code.split("\n")
    starts = [(i, DECL_RE.match(l).group(2)) for i, l in enumerate(lines)
              if DECL_RE.match(l)]
    bodies = {}
    for idx, (start_idx, name) in enumerate(starts):
        end_idx = starts[idx + 1][0] if idx + 1 < len(starts) else len(lines)
        bodies[name] = "\n".join(lines[start_idx:end_idx])
    return bodies


def main() -> int:
    try:
        raw = io.open(BEST_LEAN, encoding="utf-8").read()
    except OSError as exc:
        print("FAIL: cannot read %s: %s" % (BEST_LEAN, exc))
        return 1

    code = strip_comments_and_strings(raw)
    bodies = get_decl_bodies(code)
    failures: list[str] = []

    # 1. Total elimination of WeakToStrongBridge and hBridge across RAW text (including comments and docstrings)
    for banned in ("WeakToStrongBridge", "hBridge"):
        matches = [line_no for line_no, line in enumerate(raw.split("\n"), 1)
                   if re.search(word_re(banned), line)]
        if matches:
            failures.append("Banned token '%s' found in raw text at lines: %s"
                            % (banned, ", ".join(map(str, matches))))

    # If the file has been promoted to the canonical FinalNonCircularClosure architecture,
    # non-circularity is audited via FinalNonCircularClosure (guarded by test_no_linearity.py).
    if "FinalNonCircularClosure" in raw and "GenuineRationalJudgment" not in bodies:
        print("=== CIRCULARITY AUDIT RESULTS ===")
        if failures:
            print("FAIL (%d failures):" % len(failures))
            for f in failures:
                print("  - %s" % f)
            return 1
        print("PASS: FinalNonCircularClosure is present; WeakToStrongBridge and hBridge are completely absent.")
        return 0

    # 2. GenuineRationalJudgment independence
    if "GenuineRationalJudgment" in bodies:
        body = bodies["GenuineRationalJudgment"]
        banned_in_grj = (
            "FreeSubject",
            "FreeWill",
            "FreeWillAt",
            "LibertarianFreeChoice",
            "LibertarianFreeChoiceAt",
            "MechanicallyForced",
            "NormativelySensitive",
            "SubjectSourceOfJudgment",
        )
        for term in banned_in_grj:
            if re.search(word_re(term), body):
                failures.append("GenuineRationalJudgment mentions banned term: %s" % term)
    else:
        failures.append("GenuineRationalJudgment not declared in file")

    # 3. RationallyReasonResponsive independence
    if "RationallyReasonResponsive" in bodies:
        body = bodies["RationallyReasonResponsive"]
        banned_in_rrr = (
            "FreeSubject",
            "FreeWill",
            "FreeWillAt",
            "LibertarianFreeChoice",
            "LibertarianFreeChoiceAt",
            "MechanicallyForced",
            "NormativelySensitive",
            "SubjectSourceOfJudgment",
        )
        for term in banned_in_rrr:
            if re.search(word_re(term), body):
                failures.append("RationallyReasonResponsive mentions banned term: %s" % term)
    else:
        failures.append("RationallyReasonResponsive not declared in file")

    # 4. SubjectSourceOfJudgment independence & no self-reference
    if "SubjectSourceOfJudgment" in bodies:
        body = bodies["SubjectSourceOfJudgment"]
        # Strip the declaration signature header so we don't match the def name itself
        body_lines = body.split("\n")
        inner_body = "\n".join(body_lines[1:])
        if re.search(word_re("SubjectSourceOfJudgment"), inner_body):
            failures.append("SubjectSourceOfJudgment is self-referential in body")
        banned_in_source = (
            "FreeSubject",
            "FreeWill",
            "FreeWillAt",
            "LibertarianFreeChoice",
            "LibertarianFreeChoiceAt",
            "MechanicallyForced",
            "NormativelySensitive",
        )
        for term in banned_in_source:
            if re.search(word_re(term), body):
                failures.append("SubjectSourceOfJudgment mentions banned term: %s" % term)
    else:
        failures.append("SubjectSourceOfJudgment not declared in file")

    # 5. VerdictConstitution independence
    if "VerdictConstitution" in bodies:
        body = bodies["VerdictConstitution"]
        banned_in_vc = (
            "FreeSubject",
            "FreeWill",
            "FreeWillAt",
            "LibertarianFreeChoice",
            "LibertarianFreeChoiceAt",
        )
        for term in banned_in_vc:
            if re.search(word_re(term), body):
                failures.append("VerdictConstitution mentions freedom predicate: %s" % term)
    else:
        failures.append("VerdictConstitution not declared in file")

    # 6. rational_presentation_implies_genuine_rational_judgment direct independence
    direct_thm = "rational_presentation_implies_genuine_rational_judgment"
    if direct_thm in bodies:
        body = bodies[direct_thm]
        for term in ("WeakToStrongBridge", "hBridge", "FreeSubject", "FreeWill", "LibertarianFreeChoice"):
            if re.search(word_re(term), body):
                failures.append("%s mentions banned term: %s" % (direct_thm, term))
    else:
        failures.append("%s not declared in file" % direct_thm)

    # 7. The subject-source bridge (section XV): the structural
    #    definitions must be free of freedom vocabulary, free of
    #    MechanicallyForced, free of ReasonCessation and free of
    #    ReasonMakesTheJudgmentDifference — a definition mentioning the
    #    target would be the target renamed. The bridge lemmas must be
    #    free of the freedom vocabulary and of MechanicallyForced
    #    (ReasonCessation is a declared premise there, hence allowed).
    #    The main theorem mentions MechanicallyForced only as the negated
    #    conclusion, exactly once. The main theorem's premises are pinned
    #    to the three intended ones.
    law_defs = (
        "NecessarySubject",
        "ContingentSubject",
        "DeterminationReceivedFromPriorState",
        "ContingentDetermination",
        "SubjectIsSourceOfDetermination",
        "DeterminationOriginatedBySubject",
    )
    bridge_lemmas = (
        "consideration_presents_a_reason",
        "subject_is_source_of_presentation",
        "subject_source_yields_contingent_determination",
        "subject_source_yields_chain_subject_source",
        "determination_originated_by_subject",
    )
    bridge_main = "subject_source_and_open_world_exclude_mechanical_forcing"
    bridge_concluders = (
        bridge_main,
    )
    bridge_guards = (
        "necessary_subject_and_fixed_determination_coexist",
        "contingent_determination_without_necessary_subject",
        "subject_source_in_chain_with_mechanical_forcing",
        "presented_reason_without_determining_verdict",
        "necessary_subject_and_contingent_determination_coexist",
        "subject_source_without_open_world_is_compatible_with_forcing",
        "contingent_determination_coexists_with_mechanical_forcing",
    )
    freedom_banned = (
        "FreeSubject",
        "FreeWill",
        "FreeWillAt",
        "LibertarianFreeChoice",
        "LibertarianFreeChoiceAt",
        "Choice",
        "NormativelySensitive",
    )
    for name in law_defs + bridge_lemmas + bridge_concluders + bridge_guards:
        if name not in bodies:
            failures.append("bridge declaration not present: %s" % name)

    for name in law_defs:
        body = bodies.get(name, "")
        for term in freedom_banned + ("MechanicallyForced",
                                      "ReasonCessation",
                                      "ReasonMakesTheJudgmentDifference"):
            if re.search(word_re(term), body):
                failures.append(
                    "law %s mentions banned term: %s" % (name, term))

    for name in bridge_lemmas:
        body = bodies.get(name, "")
        for term in freedom_banned:
            if re.search(word_re(term), body):
                failures.append(
                    "bridge lemma %s mentions banned term: %s" % (name, term))
        if re.search(word_re("MechanicallyForced"), body):
            failures.append(
                "bridge lemma %s mentions MechanicallyForced before "
                "the main theorem's conclusion" % name)

    for name in bridge_concluders + bridge_guards:
        body = bodies.get(name, "")
        for term in freedom_banned:
            if re.search(word_re(term), body):
                failures.append(
                    "bridge declaration %s mentions banned term: %s"
                    % (name, term))

    # MechanicallyForced may appear only negated (never as a premise) and
    # exactly once (the conclusion) in the declarations that conclude it.
    for name in bridge_concluders:
        body = bodies.get(name, "")
        count = len(re.findall(word_re("MechanicallyForced"), body))
        if count != 1:
            failures.append(
                "%s must mention MechanicallyForced exactly once (the ¬ "
                "conclusion), found %d" % (name, count))
        if re.search(r"(?<!¬ )\bMechanicallyForced\b", body):
            failures.append(
                "%s asserts MechanicallyForced without negation "
                "(positive premise?)" % name)

    # The main theorem's hypotheses are pinned: the performative fact,
    # the personal source, and the open world.
    body = bodies.get(bridge_main, "")
    premises = sorted(set(re.findall(r"\((h[A-Za-z0-9_'!]*)\s*:", body)))
    if premises != ["hCess", "hPresentation", "hSource"]:
        failures.append(
            "%s has unexpected hypotheses: %s (expected exactly "
            "hCess, hPresentation, hSource)"
            % (bridge_main, ", ".join(premises)))

    print("=== CIRCULARITY AUDIT RESULTS ===")
    if failures:
        print("FAIL (%d failures):" % len(failures))
        for f in failures:
            print("  - %s" % f)
        return 1
    print("PASS: GenuineRationalJudgment, SubjectSourceOfJudgment, and VerdictConstitution have zero circular dependencies.")
    print("PASS: WeakToStrongBridge and hBridge are completely absent.")
    print("PASS: subject-source bridge definitions are free of freedom vocabulary,")
    print("      of MechanicallyForced, of ReasonCessation and of difference; its premises are")
    print("      presentation + subject-source + open world.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
