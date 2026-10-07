#!/usr/bin/env python3
"""No-linearity guard for best.lean.

The defect this gates: `Deliberates` was defined by

    Apprehends s p ∧ CanAssent C s p ∧ CanWithholdAssent C s p

where `CanAssent`/`CanWithholdAssent` ARE the open libertarian
alternatives. Any theorem deriving `FreeSubject` through
`RationallyAssents → Deliberates → CanAssent/CanWithholdAssent` is
therefore circular for the purpose of discovering freedom: the concept
of deliberating already contained the answer.

The canonical argument (`FinalNonCircularClosure`) reaches `FreeSubject`
without ever mentioning those predicates. This script asserts that, and
asserts it against the parsed declaration structure rather than by grep
alone: a theorem is only allowed to reach freedom if it is a declared
public theorem of the canonical chain, and every occurrence of a
circularity-bearing predicate must be accounted for.

Run:  python3 scripts/test_no_linearity.py [path/to/best.lean]
Exit: 0 = no circular route to freedom; 1 = a circular route exists.

Self-test: this file also runs as its own negative test when given
--self-test, which reintroduces each way the circularity could come back
and asserts the gate rejects every one of them. A gate never observed to
fail is not a gate.

Why a script and not a Lean theorem: the property is about which
declarations exist and what they mention, i.e. about the file's shape.
A Lean theorem could only see the declarations that survived, so it
could not notice the *reintroduction* of a deleted circular derivation --
which is exactly the regression that matters.
"""

from __future__ import annotations

import io
import re
import sys
from collections import defaultdict

# Overridable so the negative tests (which reintroduce a circular route
# on purpose) can run against a scratch copy.
BEST_LEAN = sys.argv[1] if len(sys.argv) > 1 and not sys.argv[1].startswith("-") else "best.lean"

# Predicates that carry libertarian content by definition. Deriving
# freedom through any of them is circular.
CIRCULAR_PREDICATES = (
    "Deliberates",
    "CanAssent",
    "CanWithholdAssent",
    "OpenAssentAlternative",
    "OpenWithholdingAlternative",
    "LibertarianFreeChoice",  # legacy, non-At version
    "RationallyAssents",
)

# Freedom conclusions that constitute "reaching freedom".
FREEDOM_CONCLUSIONS = (
    "FreeSubject",
    "FreeWill",
    "FreeWillAt",
    "LibertarianFreeChoice",
    "LibertarianFreeChoiceAt",
    "Person",
)


def word_re(name: str) -> str:
    return r"\b%s\b" % name

# The only declarations permitted to conclude freedom. Each must live
# inside FinalNonCircularClosure (except the public wrappers, which
# must merely delegate to it).
CANONICAL_FREEDOM_THEOREMS = {
    # direct ontological route: well-founded determination
    # chain + ultimate source is act of s + contingent determination -> freedom.
    "normative_sensitivity_implies_libertarian_choice_direct",
    "originated_contingent_determination_yields_libertarian_choice",
    "originated_contingent_determination_yields_free_will",
    "ontological_determination_yields_libertarian_freedom",
    "non_mechanical_yields_libertarian_freedom",
    "complete_libertarian_freedom_argument",
    "performative_proof_instantiates_libertarian_freedom",
    "proof_instance_implies_existence_of_free_subject",
    "proof_instance_implies_free_subject",
    "proof_instance_nonempty_implies_existence_of_free_subject",
    "demonstration_occurrence_implies_existence_of_free_subject",
    "proof_exists_implies_existence_of_free_subject",
    "freedom_is_not_merely_unforced",
    "epistemic_or_unforced_indeterminacy_fails_libertarian_choice",
    "indeterminacy_without_polar_alternative_fails_libertarian_choice",
    "unforced_alone_does_not_provide_libertarian_alternative",
    "mere_indeterminism_insufficient_for_libertarian_freedom",
    "contingent_determination_constructs_positive_libertarian_choice",
    "constitutive_chain_entails_free_subject",
    "libertarian_free_choice",
    "free_will",
    "free_subject",
    "toy_model_consistency_witness",
}

# Every allowlisted name must live in FinalNonCircularClosure or be one of
# the public wrappers declared at the top level of
# CompleteLibertarianFreedomArgument. This stops the allowlist from
# quietly becoming a dumping ground: adding a name here is not enough to
# smuggle a legacy-namespace derivation past the gate.
PUBLIC_WRAPPERS = {
    "ontological_determination_yields_libertarian_freedom",
    "non_mechanical_yields_libertarian_freedom",
    "complete_libertarian_freedom_argument",
    "performative_proof_instantiates_libertarian_freedom",
    "proof_instance_implies_existence_of_free_subject",
    "proof_instance_implies_free_subject",
    "proof_instance_nonempty_implies_existence_of_free_subject",
    "demonstration_occurrence_implies_existence_of_free_subject",
    "proof_exists_implies_existence_of_free_subject",
    "epistemic_or_unforced_indeterminacy_fails_libertarian_choice",
    "indeterminacy_without_polar_alternative_fails_libertarian_choice",
    "unforced_alone_does_not_provide_libertarian_alternative",
    "mere_indeterminism_insufficient_for_libertarian_freedom",
    "contingent_determination_constructs_positive_libertarian_choice",
    "constitutive_chain_entails_free_subject",
    "libertarian_free_choice",
    "free_will",
    "free_subject",
    "toy_model_consistency_witness",
}
FNC_PREFIX = "Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure"

# The legacy circular theorems that were deleted. Asserting their
# absence is the point: a reintroduction is the regression.
DELETED_CIRCULAR_THEOREMS = (
    "rational_assent_yields_libertarian_free_choice",
    "rational_assent_yields_libertarian_free_will",
    "rational_assent_yields_free_subject",
    "rational_assent_yields_person",
    "exists_free_subject_of_rational_activity",
    "presented_as_rational_implies_libertarian_free_subject",
    "presented_as_rational_implies_libertarian_free_will",
    "presented_as_rational_implies_person",
    "rational_assent_to_no_free_subject_is_self_refuting",
    "rational_presentation_of_no_free_subject_is_self_refuting",
    "no_free_subject_cannot_be_presented_as_rational",
    "denial_of_libertarian_freedom_is_performatively_inconsistent",
)

DECL_RE = re.compile(
    r"^(theorem|def|structure|inductive|instance|abbrev|lemma|example)\s+"
    r"([A-Za-z_][A-Za-z0-9_'!?]*)"
)
NAMESPACE_RE = re.compile(r"^(namespace|end)\s+([A-Za-z_][A-Za-z0-9_'!?]*)")


def strip_comments_and_strings(text: str) -> str:
    """Blank out comments and string literals, preserving line numbering.

    Prose in this file names deleted theorems and the circular
    predicates on purpose (tombstones, status ledger). Scanning the raw
    text would therefore report every honest mention as a violation.
    """
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
            # inside a block comment: blank the body, keep the newlines
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def parse(text: str):
    """Return [(line_no, kind, name, namespace_path)] for top-level decls."""
    decls = []
    ns_stack: list[str] = []
    for line_no, line in enumerate(text.split("\n"), 1):
        m = NAMESPACE_RE.match(line)
        if m:
            if m.group(1) == "namespace":
                ns_stack.append(m.group(2))
            elif ns_stack:
                ns_stack.pop()
            continue
        d = DECL_RE.match(line)
        if d:
            decls.append((line_no, d.group(1), d.group(2), ".".join(ns_stack)))
    return decls


def declaration_spans(text: str):
    """Map every line number to the name of the declaration containing it."""
    lines = text.split("\n")
    starts = [(i, DECL_RE.match(l).group(2)) for i, l in enumerate(lines, 1)
              if DECL_RE.match(l)]
    owner = ["<top>"] * (len(lines) + 2)
    for idx, (line_no, name) in enumerate(starts):
        end = starts[idx + 1][0] if idx + 1 < len(starts) else len(lines) + 1
        for j in range(line_no, end):
            owner[j] = name
    return owner, lines


def main() -> int:
    try:
        raw = io.open(BEST_LEAN, encoding="utf-8").read()
    except OSError as exc:
        print("FAIL: cannot read %s: %s" % (BEST_LEAN, exc))
        return 1

    code = strip_comments_and_strings(raw)
    decls = parse(code)
    owner, lines = declaration_spans(code)
    failures: list[str] = []

    # --- G1: the deleted circular theorems must be absent -----------------
    # One name is deliberately reused: the old circular
    # `rational_presentation_of_no_free_subject_is_self_refuting` was
    # deleted and the name was given to the recovered canonical-route
    # refutation (section XXII). Reuse is legitimate only because that
    # declaration is allowlisted and therefore vetted by G2/G3/G5/G6.
    declared = {name for _, _, name, _ in decls}
    for t in DELETED_CIRCULAR_THEOREMS:
        if t in declared and t not in CANONICAL_FREEDOM_THEOREMS:
            failures.append(
                "G1 circular theorem reintroduced: %s" % t)

    # --- G2: no declaration may reach freedom through a circular predicate
    # Only proofs can *reach* freedom. `def FreeSubject`,
    # `def LibertarianFreeChoice` and friends are the vocabulary itself;
    # they are declarations of the target notions, not derivations of
    # them, so they are reported as notes rather than as routes.
    kind_of = {name: kind for _, kind, name, _ in decls}
    PROOF_KINDS = {"theorem", "lemma", "example"}

    offenders: dict[str, set[str]] = defaultdict(set)
    freedom_reachers: dict[str, set[str]] = defaultdict(set)
    for line_no, raw_line in enumerate(lines, 1):
        if not raw_line.strip():
            continue
        name = owner[line_no]
        if name == "<top>":
            continue
        circular_here = {p for p in CIRCULAR_PREDICATES
                         if re.search(word_re(p), raw_line)}
        freedom_here = {f for f in FREEDOM_CONCLUSIONS
                        if re.search(word_re(f), raw_line)}
        if circular_here:
            offenders[name] |= circular_here
        if freedom_here and kind_of.get(name) in PROOF_KINDS:
            freedom_reachers[name] |= freedom_here

    for name, preds in sorted(offenders.items()):
        if name in CANONICAL_FREEDOM_THEOREMS:
            failures.append(
                "G2 canonical theorem %s mentions circular predicate(s) %s"
                % (name, ", ".join(sorted(preds))))
            continue
        if freedom_reachers.get(name):
            failures.append(
                "G2 %s reaches %s while mentioning circular predicate(s) %s"
                % (name, ", ".join(sorted(freedom_reachers[name])),
                   ", ".join(sorted(preds))))
        else:
            # Vocabulary and meaning theorems may mention them as long as
            # they conclude nothing about freedom. That is legitimate.
            print("  note: %s mentions %s but concludes no freedom"
                  % (name, ", ".join(sorted(preds))))

    # --- G3: every freedom-reaching theorem must be canonical -------------
    # `LibertarianFreeChoice`/`FreeWill`/`FreeSubject` also appear as the
    # *definitions* of the legacy vocabulary, which is allowed; only
    # theorems count here.
    for name, goals in sorted(freedom_reachers.items()):
        if name not in CANONICAL_FREEDOM_THEOREMS:
            failures.append(
                "G3 non-canonical theorem concludes freedom: %s -> %s"
                % (name, ", ".join(sorted(goals))))

    # --- G4: the canonical set must actually be present -------------------
    missing = sorted(CANONICAL_FREEDOM_THEOREMS - declared)
    if missing:
        failures.append("G4 missing canonical theorems: %s" % ", ".join(missing))

    # --- G5b: the allowlist must be honest ----------------------------------
    # G6: every allowlisted declaration must either live inside
    # FinalNonCircularClosure or be a declared public wrapper. A name that
    # is neither is a smuggled exemption.
    ns_of = {}
    cur: list[str] = []
    for line in code.split("\n"):
        m = NAMESPACE_RE.match(line)
        if m:
            if m.group(1) == "namespace":
                cur.append(m.group(2))
            elif cur:
                cur.pop()
            continue
        d = DECL_RE.match(line)
        if d:
            ns_of[d.group(2)] = ".".join(cur)
    for name in sorted(CANONICAL_FREEDOM_THEOREMS):
        loc = ns_of.get(name)
        if loc is None:
            failures.append("G6 allowlisted but undeclared: %s" % name)
        elif not (loc.startswith(FNC_PREFIX) or name in PUBLIC_WRAPPERS):
            failures.append(
                "G6 allowlisted %s lives outside the canonical namespace "
                "and is not a public wrapper (at %s)" % (name, loc))

    # --- G5: the public wrapper must delegate to the canonical theorem ----
    wrapper = "this_argument_implies_libertarian_freedom"
    if wrapper in declared:
        span = []
        for i, l in enumerate(lines, 1):
            if owner[i] == wrapper:
                span.append(l)
        body = "\n".join(span)
        if "rational_presentation_implies_free_subject" not in body:
            failures.append(
                "G5 %s does not delegate to rational_presentation_implies_free_subject"
                % wrapper)
        for banned in ("Deliberates", "CanAssent", "CanWithholdAssent",
                       "RationallyAssents", "LibertarianFreeChoice"):
            if re.search(word_re(banned), body):
                failures.append(
                    "G5 %s mentions banned %s" % (wrapper, banned))

    # --- report -----------------------------------------------------------
    print()
    print("declarations parsed      : %d" % len(decls))
    print("canonical freedom theorems: %d" % len(CANONICAL_FREEDOM_THEOREMS))
    print("deleted circular theorems: %d (asserted absent)"
          % len(DELETED_CIRCULAR_THEOREMS))
    if failures:
        print("\nFAIL (%d):" % len(failures))
        for f in failures:
            print("  - %s" % f)
        return 1
    print("\nPASS: FinalNonCircularClosure is the only route to freedom.")
    return 0



# =========================================================================
# SELF-TEST: the gate must reject every reintroduction of the circularity.
# =========================================================================

INJECTIONS = {
    "reintroduced deleted derivation": """
theorem rational_assent_yields_free_subject_reintroduced
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    {s : Subject} {p : Prop}
    (h : RationallyAssents C Apprehends Means s p) :
    FreeSubject C s := by
  sorry
""",
    "new theorem deriving freedom via Deliberates": """
theorem sneaky_freedom
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    {s : Subject} {p : Prop}
    (h : Deliberates C Apprehends s p) :
    FreeSubject C s := by
  sorry
""",
    "freedom reached via CanAssent only": """
theorem sneaker_via_can_assent
    (C : LibertarianChoiceSemantics Subject)
    {s : Subject} {p : Prop}
    (h : CanAssent C s p) :
    FreeWill C s := by
  sorry
""",
    "circular premise smuggled into an allowlisted wrapper": "@BODY-SWAP@",
    "bridge reimplemented through Deliberates": """
theorem sneaky_bridge
    {C : FinalNonCircularClosure.Semantics Subject}
    {s : Subject}
    (h : Deliberates C s True) :
    FinalNonCircularClosure.FreeSubject C s ↔
    True := by
  sorry
""",
    "unpriced freedom derivation (price dropped from the signature)": """
theorem unpriced_freedom
    {C : FinalNonCircularClosure.Semantics Subject}
    {s : Subject} {p : Prop}
    (J : FinalNonCircularClosure.JudgmentDeterminationChain C s C.actualWorld p) :
    FinalNonCircularClosure.FreeSubject C s := by
  sorry
""",
    "freedom smuggled through OpenWithholdingAlternative": """
theorem sneaker_via_open_alternative
    (C : LibertarianChoiceSemantics Subject)
    {s : Subject} {p : Prop}
    (h : OpenWithholdingAlternative C s p) :
    FreeSubject C s := by
  sorry
""",
}


def run_self_test() -> int:
    import os
    import subprocess
    import tempfile

    base = io.open(BEST_LEAN, encoding="utf-8").read()
    here = os.path.dirname(os.path.abspath(__file__))
    script = os.path.join(here, "test_no_linearity.py")

    if main() != 0:
        print("SELF-TEST: baseline already FAILS; aborting")
        return 1
    print("\nSELF-TEST: %d reintroduction attempts, each must be rejected"
          % len(INJECTIONS))

    bad = []
    for label, injection in INJECTIONS.items():
        if injection == "@BODY-SWAP@":
            # keep the file intact; smuggle a circular premise into the
            # allowlisted wrapper's proof. G2 (not G5) must fire.
            old_body = ("    FinalNonCircularClosure.FreeSubject C s :=\n"
                        "  FinalNonCircularClosure."
                        "performative_proof_instantiates_libertarian_freedom J hSrc")
            new_body = ("    FinalNonCircularClosure.FreeSubject C s := by\n"
                        "  have hCirc : Deliberates "
                        "C "
                        "(fun _ _ => True) s True := by\n"
                        "    sorry\n"
                        "  exact FinalNonCircularClosure."
                        "performative_proof_instantiates_libertarian_freedom J hSrc")
            assert base.count(old_body) == 1, "wrapper body anchor moved"
            mutated = base.replace(old_body, new_body, 1)
        else:
            mutated = base.replace(
                "\nend CompleteLibertarianFreedomArgument",
                injection + "\nend CompleteLibertarianFreedomArgument", 1)
        with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False,
                                         encoding="utf-8") as fh:
            fh.write(mutated)
            tmp = fh.name
        try:
            r = subprocess.run([sys.executable, script, tmp],
                               capture_output=True, text=True)
            rejected = r.returncode != 0
            why = ""
            for line in r.stdout.splitlines():
                if line.strip().startswith("- "):
                    why = line.strip()[2:]
                    break
            print("  %-46s %s%s"
                  % (label, "REJECTED" if rejected else "*** ACCEPTED ***",
                     ("  <- " + why) if why else ""))
            if not rejected:
                bad.append(label)
        finally:
            os.unlink(tmp)

    if bad:
        print("\nSELF-TEST FAIL: gate accepted %d circular reintroduction(s): %s"
              % (len(bad), ", ".join(bad)))
        return 1
    print("\nSELF-TEST PASS: gate rejects all %d reintroductions."
          % len(INJECTIONS))
    return 0


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        sys.argv = [a for a in sys.argv if a != "--self-test"]
        sys.exit(run_self_test())
    sys.exit(main())
