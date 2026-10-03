#!/usr/bin/env python3
"""plan §20 gate — doctrine rows 3 and 4 must stay free, and the two halves must co-occur.

Section 20 was written because an audit read `OneEssence Entity.ofGround e` as a relation
that "constrains nothing" and reported the ground's personality as vacuous. That reading is
withdrawn (§20.3), and this gate is what stops it coming back.

What is asserted, all from `formal/axiom_audit.json` (the audited `#print axioms`
footprints), `formal/depgraph.json` (kinds), and `formal/Logos/*.lean`:

  G1  zero substantive axioms on the §20 declarations that are *doctrine rows*;
  G2  `PersonalGround Entity.ofGround` really is asserted by the headline, and its
      `indwells` field really is the homoousios claim;
  G3  `¬ Asiety Entity.ofGround` CO-OCCURS with `PersonalGround Entity.ofGround` in the
      summary theorem — a gate that only ever checked one of them would pass either way;
  G6  the root cause `EntityMeans Entity.ofGround := True`, asserted in BOTH files that
      declare the match, so the vacuity of every `OneEssence`-routed row stays visible;
  G7  GAPMAP records the `Consubstantial` deletion (C568–C571) and the C572 withdrawal;
  G8  `Perichoretic`'s docstring KEEPS its disclosure that perichoresis is not a mutual
      grounding of the Persons — machine-checked, so the honesty cannot be edited away;
  G9  `Consubstantial` is not declared anywhere — the deletion is a regression guard, because
      reintroducing it as an `axiom` is the laundering route that once gave it a price;
  G11 the four donation declarations each rest on `AxAgapeEssence` — still the right invariant
      while S3 is blocked (LOVE-3 §0.2), so it is deliberately NOT inverted;
  G15 the plurality bridge is priced exactly ONCE and visibly: declared `axiom`, `Tag: META`,
      the only substantive axiom in the author's target sentence, that sentence unconditional,
      `AxTwoSubjects` gone from the sources and from the census, and no GAPMAP row presenting
      the bridge itself as derived. *A row is about the bridge iff its `lean_ref` IS the bridge*
      (D10): the `Pegada` cell hits the ~18 consumers, and a prose mention hits rows that merely
      say where they come from -- C585 names the bridge and is legitimately `PROVEN↑`.

**What this gate deliberately does NOT certify.** `ofGround_is_perichoretic` was removed from
the free list in plan §24. It is a *form* — `Perichoretic g a b c` is definitionally three
`OneEssence` instances, so at the ground it is `True` of atoms — and its own docstring says so
("`Perichoretic` is a *form*, and the population question is separate"). G1 must never be used to
certify it as a doctrine row: a `{}` price on a `True` proposition is a null result. G8 pins the
disclosure instead, which is the honest way to keep such a row.

Two earlier versions of this file are worth not repeating. G4/G5 asserted that `Consubstantial`
was a `def` whose body mentioned `OneEssence`, and passed a relation that was `True` of atoms,
because a vacuous relation mentions `OneEssence` perfectly well (negative test 6 replaced the body
with `True` and the gate stayed green). And a first tag reader filtered `Tag:` lines out with
`not masked[i]` — `Tag:` always lives inside a docstring, so every axiom read as untagged and the
gate reported the right verdict for the wrong reason (negative test 2).
"""
import json
import os
import pathlib
import re
import sys
from pathlib import Path

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
AUDIT = os.path.join(ROOT, "formal", "axiom_audit.json")
DEPG = os.path.join(ROOT, "formal", "depgraph.json")

# (fully-qualified name, why it must not be priced)
MUST_BE_FREE = [
    ("Logos.AsieticChoice.person_is_asietic",
     "doctrine row 4 — Asiety means Freedom, Freedom means Personal"),
    ("Logos.TrinitarianPersonalGround.ofGround_grounds_every_person",
     "the Persons are one with the essence"),
    ("Logos.TrinitarianPersonalGround.the_ground_is_not_void_of_personhood",
     "the headline — the ground is not void of personhood"),
    ("Logos.TrinitarianPersonalGround.trinitarianPersonalGround_summary",
     "the whole doctrine in one row"),
]

# §24: the `Consubstantial` family is DELETED, not re-scoped. These are the GAPMAP rows that
# must say so, so a reader arriving from §20.1 (which proposed the `def`) finds the deletion
# rather than a live declaration. Same failure mode as the old G7: a row that is silently absent
# reads as an oversight, not a decision.
DELETED_ROWS = [
    ("C568", "Consubstantial"),
    ("C570", "the_three_persons_are_consubstantial"),
    ("C571", "a_person_is_consubstantial_and_asietic"),
]

# The C572 verdict also changed: `Means a p ↔ Means b p` is Modalism, not "homoousios unproven",
# so it is withdrawn as wrongly shaped rather than left BLOCKED.
WITHDRAWN_CLAIM = ("C572", "MODALISM")

failures = []
notes = []


def load():
    with open(AUDIT, encoding="utf-8") as fh:
        audit = json.load(fh)
    with open(DEPG, encoding="utf-8") as fh:
        depg = json.load(fh)
    return audit, depg


def audit_index(audit):
    """Map fully-qualified name -> footprint list, for either dict- or list-shaped audits."""
    idx = {}
    if isinstance(audit, dict):
        for k, v in audit.items():
            idx[k] = v if isinstance(v, list) else v.get("axioms", [])
    else:
        for rec in audit:
            idx[rec.get("name", "")] = rec.get("axioms", [])
    return idx


def dep_kinds(depg):
    kinds = {}
    nodes = depg.get("nodes", depg if isinstance(depg, list) else [])
    for n in nodes:
        if isinstance(n, dict):
            key = n.get("id") or n.get("name") or ""
            kinds[key] = n.get("kind") or n.get("type") or ""
    return kinds


# Tag vocabulary, and which tag counts as a *price*. `check_consistency.py` owns the census
# (39 = 18 VOCAB + 6 SEM + 13 META + 2 TRANS) and is the only place tags are pinned; here we
# only need the VOCAB/price distinction, and we resolve it from the Lean sources via the
# shared helpers so there is exactly one comment-stripping implementation AND exactly one
# `Tag:` reader. See `axiom_tags` for why the second reader had to go (D9).
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_consistency import axiom_statements, axiom_tag  # noqa: E402

PRICED_TAGS = ("SEM", "META", "TRANS")  # VOCAB is the vocabulary of the statement itself


def axiom_tags():
    """Map fully-qualified axiom name -> Tag, by reading the Lean sources.

    **There is exactly one `Tag:` reader in this repository and this is a call into it.**
    `check_consistency.axiom_statements` finds the declarations and `check_consistency.axiom_tag`
    reads the tag off each one's own docstring — the same pair that produces the pinned census
    (39 = 18 VOCAB / 6 SEM / 13 META / 2 TRANS). One implementation, so a tag this gate reads and
    a tag the census counts cannot drift apart.

    This function used to reimplement the read, and did so wrongly, in two independent ways. It
    is recorded here because the failure is the one this gate exists to prevent (D9, 2026-10-04):

      * it collected every line containing the substring `Tag:` and then took whichever token came
        first in the order `("VOCAB", "SEM", "META", "TRANS")` — so a docstring's *prose* about
        another tag won. `ThomisticAct.lean:111` reads
        `` `Tag: META`: it connects two relations, so `VOCAB`'s "asserts no connection" rule
        excludes it``; the `VOCAB` mention made `love_implies_act` read VOCAB. A backwards scan
        from the `axiom` line reaches that prose line *before* the `/--Tag: META` opener above it,
        because it stopped at the nearest `Tag:`-bearing line rather than at the declaration's own
        docstring opener.
      * it indexed `raw[i]` with `i` taken from `axiom_statements`, which returns a **1-based**
        line, so the scan also started one line below the declaration.

    Three of 39 axioms came out with the wrong tag, and the *total* stayed 39 the whole time — the
    D7 shape, one layer over. The wrong verdict was not cosmetic: `substantive_in` below decides
    what counts as a price with this map, so `ThomisticAct.loving_subject_initiates` (PROVEN↑ at
    one META, via `love_implies_act`) was certified **free**, and twelve declarations resting on
    the VOCAB classifier `DivineSubjectRole` were read as paid. A gate that mislabels which rows
    are free is worse than no gate, so the reimplementation is deleted rather than patched, and
    `test_axiom_census.py` now asserts the two readers agree on the whole name→tag *map*.
    """
    out = {}
    lean_dir = os.path.join(ROOT, "formal", "Logos")
    for fname in sorted(os.listdir(lean_dir)):
        if not fname.endswith(".lean"):
            continue
        path = Path(lean_dir) / fname
        module = "Logos." + fname[:-5]
        for name, _stmt, line in axiom_statements(path):
            out[f"{module}.{name}"] = axiom_tag(path, int(line))
    return out


def substantive_in(footprint, declared_axioms, tags):
    """Names in a footprint that count as a price.

    A first version compared against the literal strings ``VOCAB``/``SEM``/``META``/``TRANS``.
    A negative test showed that is worthless: `axiom_audit.json` stores *fully-qualified axiom
    names* (`Logos.S4.TransinitarianPersonalBridge`), never the tag, so a re-tagged price sails
    straight through and the gate reports green on a paid row. The declared set is therefore taken
    from `depgraph.json`'s 39 `axiom` nodes, and any footprint entry in it is a price.

    Tag-based claims are also checked where they exist: a footprint entry under `Logos.` that is
    not a declared axiom is an *under*-declaration and is reported separately, because that is the
    shape `audit_footprints.py`'s own `underdeclared` check exists to catch.
    """
    priced = [ax for ax in footprint
              if ax in declared_axioms and tags.get(ax) in PRICED_TAGS]
    untagged = [ax for ax in footprint
                if ax in declared_axioms and tags.get(ax) not in PRICED_TAGS + ("VOCAB",)]
    vocab = [ax for ax in footprint
             if ax in declared_axioms and tags.get(ax) == "VOCAB"]
    undeclared = [ax for ax in footprint
                  if ax.startswith("Logos.") and ax not in declared_axioms]
    return priced, untagged, vocab, undeclared


# ---------------------------------------------------------------------------------------
# G8's rule, as a pure function of the docstring text, so it can be tested by mutation.
#
# A gate that can only be exercised by hand-editing the kernel is a gate nobody runs, and
# this one had already shipped once enforcing a refuted premise. `g8_failures` is the whole
# rule; `test_g8_rule` below mutates the docstring four ways and asserts each is caught, so
# the rule is verified rather than asserted. See `_g8_negative_tests` for the cases.
# ---------------------------------------------------------------------------------------
G8_RETRACTION = re.compile(r"retract|refuted|unsatisfiable|false twice", re.I)


def g8_failures(doc: str) -> list[str]:
    """Failures implied by `Perichoretic`'s docstring alone. Empty = the row is honestly framed.

    The three positive requirements are the honest framing: it is not a mutual grounding, the
    reason is Modalism (C572), and the asymmetry premise is retracted as refuted (C316). The
    fourth rule is the one that makes a *mention* safe: `asymmetric` may appear as history but
    never as a live justification, so an unmarked mention is a failure.
    """
    fails: list[str] = []
    if "mutual grounding" not in doc:
        fails.append(
            "G8 Perichoretic's docstring no longer says it is NOT a mutual grounding — that "
            "phrase is what keeps the row honest; restoring a mutually-indwelling reading is a "
            "deliberate act that must be argued, not typed")
    if "Modalism" not in doc:
        fails.append(
            "G8 Perichoretic's docstring no longer gives the REAL reason mutual grounding is "
            "refused (C572, Modalism). Without it the refusal looks unexplained, and the next "
            "reader may 'repair' it with a symmetric relation.")
    if "reflexive" not in doc or "C316" not in doc:
        fails.append(
            "G8 Perichoretic's docstring must disclose that `OneEssence` is reflexive and its "
            "asymmetry refuted (C316) — that is what retracts the old false justification, and "
            "without the retraction an 'asymmetric' mention reads as a live claim.")
    if "asymmetric" in doc and not G8_RETRACTION.search(doc):
        fails.append(
            "G8 Perichoretic's docstring mentions `asymmetric` with no retraction marker — "
            "`AsymmetricGrounding` is refuted by C316, so an unmarked mention asserts a false "
            "premise. Wrap it in the retraction, or delete it.")
    return fails


def _g8_negative_tests() -> list[tuple[str, bool]]:
    """Mutations of a compliant docstring; each must be CAUGHT. Returns (label, caught).

    Case 1 is the regression this rewrite exists for: restoring the pre-2026-10-03 text, which
    mentioned `asymmetric` as the live reason. Under the old rule that passed; under this one it
    must not, because the mention carries no retraction marker.
    """
    good = ("This is not a mutual grounding of the Persons. The reason is Modalism: the mutual "
            "reading is C572. `OneEssence` is reflexive and `AsymmetricGrounding` is refuted "
            "(C316), so the earlier asymmetry premise is retracted.")
    cases = [
        ("old rule reinstated: 'asymmetric' asserted as the live reason",
         "This is not a mutual grounding of the Persons. `OneEssence` is asymmetric, so persons "
         "cannot ground one another."),
        ("modality of the refusal removed (Modalism/C572 gone)",
         "This is not a mutual grounding of the Persons and is deliberately not."),
        ("reflexivity/C316 retraction removed",
         "This is not a mutual grounding of the Persons. The reason is Modalism, the C572 claim."),
        ("honesty framing removed entirely",
         "Three `OneEssence` instances; costs nothing."),
    ]
    out = []
    for label, mutated in cases:
        out.append((label, len(g8_failures(mutated)) > 0))
    out.append(("control: the compliant docstring passes", len(g8_failures(good)) == 0))
    return out


def _g12_negative_tests() -> list[tuple[str, bool]]:
    """Mutations of a compliant C575 docstring; each must be CAUGHT."""
    good = ("Agape is the donation of the Self (C575). `SelfDonation f o` is a gift between two "
            "distinct personal properties, `personalProperty : Prop`, sharing one location-entity "
            "`f.deiformEntity = o.deiformEntity`. Priced on `AxAgapeEssence`, one META axiom.")
    cases = [
        ("field dropped: the marker that makes `f ≠ o` satisfiable is gone",
         "Agape is the donation of the Self (C575). Two subsisting centres share one "
         "location-entity. Priced on `AxAgapeEssence`, one META axiom."),
        ("shared location dropped: the gift reads as between two things",
         "Agape is the donation of the Self (C575). `SelfDonation f o` is a gift between two "
         "distinct personal properties, `personalProperty : Prop`. Priced on `AxAgapeEssence`."),
        ("price dropped: the axiom the row rests on is unnamed",
         "Agape is the donation of the Self (C575). `SelfDonation f o` is a gift between two "
         "distinct personal properties, `personalProperty : Prop`, sharing one location-entity."),
        ("fourth chooser smuggled back in",
         "Agape is the donation of the Self (C575). The ground itself chooses and gives, a fourth "
         "chooser alongside the Persons, `personalProperty : Prop`, one location-entity. Priced on "
         "`AxAgapeEssence`."),
    ]
    out = []
    for label, mutated in cases:
        out.append((label, len(g12_failures(mutated)) > 0))
    out.append(("control: the compliant docstring passes", len(g12_failures(good)) == 0))
    return out


def g12_failures(doc: str) -> list[str]:
    """Failures implied by the C575 donation docstring alone. Empty = honestly framed."""
    fails: list[str] = []
    if "personalProperty" not in doc:
        fails.append(
            "G12 the donation docstring no longer names `personalProperty` — without the second "
            "field the `f ≠ o` conjunct was unsatisfiable and the kernel derived `False`.")
    if "deiformEntity" not in doc and "one location" not in doc and "shared location" not in doc:
        fails.append(
            "G12 the donation docstring no longer says the gift is between one location-entity — "
            "without it the donation reads as between two things.")
    if "AxAgapeEssence" not in doc:
        fails.append(
            "G12 the donation docstring no longer names the META axiom it rests on — an unpriced "
            "donation is the laundering this plan exists to prevent.")
    if "fourth chooser" in doc.lower() and "not a fourth chooser" not in doc.lower():
        fails.append(
            "G12 the donation docstring presents the ground as a fourth chooser — C578 exists to "
            "refuse exactly that, and an unmarked mention smuggles it back.")
    return fails


def g13_failures(block: str) -> list[str]:
    """Failures implied by ONE rendered derivation block of the granted-premise row.

    A target marked `"role": "premise"` in `formal/presentation_spine.json` is the
    **objection's premise, granted** — R21 names
    `ground_is_not_a_fourth_chooser` for the row "The Ground cannot give at all,
    because it is not a person who chooses", and the renderer printed
    `✅ this half of the objection is answered free` over it, with a
    `KILLS [step 8]` line under a theorem that makes nothing impossible. The
    premise of an objection captioned as its refutation is the same laundering as a
    priced row printed with the free glyph, one level down: the block claims a death
    the kernel does not deliver. Empty = the label and the blank KILLS agree.
    """
    fails: list[str] = []
    if "🤝" not in block:
        fails.append(
            "G13 the granted premise is not labelled 🤝 — a premise-role target rendered as an "
            "answer is the objection's own premise captioned as its refutation.")
    if "granted" not in block.lower():
        fails.append(
            "G13 the granted-premise label does not say what it is — without the word 'granted' "
            "the 🤝 reads as a fourth terminator rather than as the limit of the row.")
    if re.search(r"^KILLS\s", block, re.M):
        fails.append(
            "G13 the granted premise still prints KILLS — granting the objection's premise is "
            "not making a step impossible, and the line overclaims.")
    if re.search(r"(answered, at a price|✅ PROVEN — 0 substantive)", block) and "🤝" in block:
        # A priced glyph over a granted premise is the same double claim; a free
        # glyph is fine, because the premise IS free — it is the `GIVES` wording
        # that must not call it an answer.
        pass
    if "answered **free**" in block and "🤝" in block:
        fails.append(
            "G13 the granted premise is captioned as answered — it is the objection's premise, "
            "and the caption is the defect this gate exists to catch.")
    return fails


def g14_failures(price_text: str) -> list[str]:
    """Failures implied by one rendered block's PRICE group. Empty = glyph and count agree.

    Two facts must travel together and cannot be checked apart: the verdict glyph
    (`✅ PROVEN`, `⚠️ AXIOMATIC (X)`, `📘 DEFINITIONAL`, `🧱 COUNTERMODEL`) and the count
    of substantive axioms. `scripts/build_deduction.py` once keyed a display string
    against internal categories, so every §13 link printed "0 substantive axioms"
    while the rows underneath were priced; the reverse error is the one this gate
    exists to catch — a `0` on a footprint that carries a SEM/META/TRANS axiom.

    A block's price is a *group*, not a line: the countermodel block prints
    `🧱 **COUNTERMODEL** — a hostile model, not a price`, then `refutes: …`, then
    `0 substantive axioms · {}`. Reading each line as a whole price failed that
    block three times over — a rule that rejects its own corpus is not a gate — so
    the caller passes the group's lines joined and the glyph is looked for anywhere
    in them.
    """
    fails: list[str] = []
    m = re.search(r"(\d+)\s+substantive axiom", price_text)
    if not m:
        fails.append(
            "G14 the PRICE line does not state a substantive-axiom count — a price with no "
            "number cannot be checked against the footprint.")
        return fails
    count = int(m.group(1))
    priced = "AXIOMATIC" in price_text
    if count == 0 and priced:
        fails.append(
            "G14 the PRICE line prints the priced glyph with `0 substantive axioms` — the "
            "footprint carries an axiom, so one of the two is wrong.")
    if count > 0 and not priced:
        fails.append(
            f"G14 the PRICE line counts {count} substantive axioms without the priced glyph — "
            "a price printed as free.")
    if count == 0 and not any(w in price_text for w in
                              ("PROVEN", "DEFINITIONAL", "COUNTERMODEL", "OPEN", "BLOCKED",
                               "DEMOTED", "AXIOM")):
        fails.append(
            "G14 the PRICE line counts 0 substantive axioms but claims no free verdict — a "
            "`{}` footprint is PROVEN, DEFINITIONAL or COUNTERMODEL, and none of them is here.")
    return fails


def _g13_g14_negative_tests() -> list[tuple[str, bool]]:
    """Mutations of a compliant granted-premise block and PRICE line; each must be CAUGHT."""
    good_block = ("DEPENDS ON   \u2014 the modelled denial\n"
                  "GIVES        \U0001f91d the objection's premise is **granted** \u2014 0 substantive "
                  "axioms. This is the limit of the row, not an answer to it\n"
                  "PROOF\n"
                  "    \u2699\ufe0f DERIVATION \u2014 2 compiled steps\n"
                  "    \u2234 \u00acAsiety(Entity).ofGround\n")
    cases_g13 = [
        ("premise captioned as an answer (the R21 defect)",
         good_block.replace("\U0001f91d the objection's premise is **granted**",
                            "\u2705 this half of the objection is answered **free**")),
        ("granted premise kills a step (the R21 overclaim)",
         good_block + "KILLS        [step 8](#step-8) \u2014 That Person Grounds the Poles\n"),
        ("the \U0001f91d glyph dropped entirely", good_block.replace("\U0001f91d", "\u2705")),
    ]
    out = [(f"G13n {label}", len(g13_failures(mut)) > 0) for label, mut in cases_g13]
    out.append(("G13n control: the compliant granted-premise block passes",
                len(g13_failures(good_block)) == 0))

    good_price = "PRICE            \u2705 **PROVEN** \u2014 0 substantive axioms \u00b7 `{Means, Subject}`"
    cases_g14 = [
        ("priced glyph with a 0 count (the _GLANCE_RANK defect, reversed)",
         "PRICE            \u26a0\ufe0f **AXIOMATIC (AxAgapeEssence)** \u2014 0 substantive axioms \u00b7 `{Subject}`"),
        ("a real price printed as free",
         "PRICE            \u2705 **PROVEN** \u2014 3 substantive axioms \u00b7 `{Subject}`"),
        ("count deleted entirely",
         "PRICE            \u26a0\ufe0f **AXIOMATIC (AxAgapeEssence)** \u00b7 `{Subject}`"),
        ("0 count with no free verdict",
         "PRICE            \ud83e\udde9 **MYSTERY** \u2014 0 substantive axioms \u00b7 `{Subject}`"),
    ]
    out += [(f"G14n {label}", len(g14_failures(mut)) > 0) for label, mut in cases_g14]
    out.append(("G14n control: the compliant free PRICE line passes", len(g14_failures(good_price)) == 0))
    cm_group = ("PRICE            \U0001f9f1 **COUNTERMODEL** \u2014 a hostile model, not a price\n"
                "PRICE            refutes: unicity_does_not_force_unitarian_monad \u21d0 Independence\n"
                "PRICE            0 substantive axioms \u00b7 `{}`")
    out.append(("G14n control: the countermodel PRICE group (3 lines) passes",
                len(g14_failures(cm_group)) == 0))
    priced_price = ("PRICE            \u26a0\ufe0f **AXIOMATIC (AxAgapeEssence)** \u2014 1 substantive "
                    "axiom: AxAgapeEssence \u00b7 `{AxAgapeEssence, Subject, choice}`")
    out.append(("G14n control: the compliant priced PRICE line passes",
                len(g14_failures(priced_price)) == 0))
    return out



# ---------------------------------------------------------------------------------------
# G15's rule, as a pure function of a record of facts, so it can be mutation-tested on the same
# principle as G8/G12/G13/G14: a gate that can only be exercised by hand-editing the kernel is a
# gate nobody runs.
#
# What it pins (batch LOVE-3/S4, 2026-10-04). `Value.AxTwoSubjects` was retired and replaced by
# `TwoNecessaryPersonalCentres.AxTwoNecessaryPersonalCentres`, which is the author's *reason*
# rather than a bare re-statement that plurality is required. Two things can go wrong afterwards
# and NEITHER shows up in a count:
#
#   (a) the bridge stops being a price -- re-tagged VOCAB, demoted to a `theorem`, or given a
#       GAPMAP row that reads PROVEN -- while every downstream row still shows PROVEN↑ and the
#       reader has no way to tell that the *justification* moved;
#   (b) a SECOND price appears beside it: `AxTwoSubjects` re-declared, or a second substantive
#       axiom added to the author's target sentence. The census then reads 14 META, but the two
#       census pins live in other files and say nothing about *which* axiom moved.
#
# So G15 asserts the SET, not the total. `EXPECTED_META_COUNT` is a tripwire rather than the
# instrument: if S3 ever unblocks (LOVE-3 §0.2 option 2), META goes to 12 and this constant moves
# in the same change as `check_consistency.EXPECTED_AXIOM_STATEMENTS` and the breakdown in
# `test_axiom_census.py`.
# ---------------------------------------------------------------------------------------

PLURALITY_BRIDGE = "Logos.TwoNecessaryPersonalCentres.AxTwoNecessaryPersonalCentres"
RETIRED_BRIDGE = "Logos.Value.AxTwoSubjects"
# The author's target sentence. UNCONDITIONAL is the whole point: `AxTwoSubjects` made plurality
# ride on `Core.rightWrongDistinction`, so a conditional re-derivation would silently restore the
# dependency the retirement was for, while the row kept reading PROVEN↑.
PLURALITY_THEOREM = "Logos.Plurality.two_necessary_persons"
EXPECTED_META_COUNT = 13


def _g15_ref(cell: str) -> str:
    """The declaration a GAPMAP `Lean theorem` cell points at, mirroring
    `build_deduction._extract_lean_ref`: first backtick span, first identifier run, and a
    `Logos.`-prefixed token is skipped (that helper exists so a cell may spell the module
    out in full without the ledger's own ref becoming fully qualified)."""
    for span in re.findall(r"`([^`]*)`", cell):
        m = re.search(r"[A-Za-z_][A-Za-z0-9_.]*", span)
        if m and not m.group(0).startswith("Logos"):
            return m.group(0).strip()
    return ""


def _g15_gapmap_rows(gap: str) -> list[tuple[str, str]]:
    """GAPMAP rows whose CLAIM **is** the plurality bridge, with their status.

    Scoped by the row's `lean_ref`, and that scoping is the whole point (D10, LOVE-3
    2026-10-04). Two weaker scopings both fail on the real tree:

    * matching the `Pegada` footprint cell hits the ~18 rows that REST ON the bridge, where
      `PROVEN↑` is exactly right — those are consumers, not the bridge's own row;
    * substring-matching the *claim* cell for the bridge's name is worse, because a row may
      name the bridge in prose while claiming something else. C585
      (`Plurality.two_necessary_persons`) says "follows from
      `AxTwoNecessaryPersonalCentres`" and is legitimately `PROVEN↑`; the substring rule
      read it as a row about the bridge and demanded `AXIOM`, so the gate failed on the
      correct ledger — an assertion whose failure is not actionable is worse than none.

    A row is about the bridge exactly when the declaration it points at IS the bridge. That
    is derived from the ledger's own ref, cannot be fooled by prose, and cannot be fooled by
    a footprint citation.
    """
    bridge_module = PLURALITY_BRIDGE[len("Logos."):].rsplit(".", 1)[0]
    bridge_name = PLURALITY_BRIDGE.rsplit(".", 1)[-1]
    rows = []
    for m in re.finditer(r"^\| [^|\n]+ \|[^\n]*$", gap, re.M):
        cells = m.group(0).split("|")
        if len(cells) < 6:
            continue  # not the | id | section | claim | status | footprint | shape
        ref = _g15_ref(cells[-4])
        if "." in ref:
            mod, name = ref.rsplit(".", 1)
            if (mod, name) == (bridge_module, bridge_name):
                rows.append((cells[1].strip(), cells[-3].strip()))
        elif ref == bridge_name:
            rows.append((cells[1].strip(), cells[-3].strip()))
    return rows


def g15_record(idx, declared_axioms, tags, kinds, gap) -> dict:
    """The facts G15 judges, read from the audit, the sources and GAPMAP."""
    lean_dir = pathlib.Path(ROOT, "formal", "Logos")
    plural_src = (lean_dir / "Plurality.lean").read_text(encoding="utf-8")
    m = re.search(r"^theorem two_necessary_persons\b", plural_src, re.M)
    stmt = ""
    if m:
        tail = plural_src[m.start():m.start() + 600]
        cut = re.search(r":=", tail)
        stmt = tail[: cut.start()] if cut else tail

    # Re-declared `AxTwoSubjects` anywhere in the sources (the G9 pattern: checked against the
    # SOURCES, not depgraph.json, because depgraph is a build artifact and stays stale).
    redeclared = []
    for path in sorted(lean_dir.glob("*.lean")):
        body = path.read_text(encoding="utf-8")
        if re.search(r"^(?:axiom|def|theorem|abbrev|opaque)\s+AxTwoSubjects\b", body, re.M):
            redeclared.append(path.name)

    short_bridge = PLURALITY_BRIDGE.rsplit(".", 1)[-1]
    meta = {a for a in declared_axioms if tags.get(a) == "META"}
    return {
        "kind": kinds.get(short_bridge, ""),
        "tag": tags.get(PLURALITY_BRIDGE),
        "bridge_in_census": PLURALITY_BRIDGE in meta,
        "retired_in_census": RETIRED_BRIDGE in meta,
        "meta_count": len(meta),
        "theorem_footprint": idx.get(PLURALITY_THEOREM),
        "theorem_statement": stmt,
        "substantive": {a for a in declared_axioms if tags.get(a) in PRICED_TAGS},
        "retired_redeclared_in": redeclared,
        "rows_about_bridge": _g15_gapmap_rows(gap),
    }


def g15_failures(rec: dict) -> list[str]:
    """Failures implied by the plurality bridge's pricing. Empty = priced exactly once, visibly."""
    fails: list[str] = []
    bridge, thm = PLURALITY_BRIDGE, PLURALITY_THEOREM
    short = bridge.rsplit(".", 1)[-1]

    if rec["kind"] != "axiom":
        fails.append(
            f"G15 {short}: depgraph kind is {rec['kind']!r}, expected 'axiom'. The bridge must stay "
            "a DECLARED axiom; a `theorem` here is the laundering route, because every plural "
            "person row reads PROVEN↑ off it and would then be resting on nothing.")
    if rec["tag"] != "META":
        fails.append(
            f"G15 {short}: Tag is {rec['tag']!r}, expected 'META'. That two NECESSARY persons "
            "exist is a substantive metaphysical claim, not a reading of the vocabulary; VOCAB "
            "would hide the price the author's own argument pays.")

    fp = rec["theorem_footprint"]
    if fp is None:
        fails.append(
            f"G15 {thm}: absent from axiom_audit.json -- the author's target sentence is not "
            "machine-audited, so its price is unknown rather than absent.")
    else:
        if bridge not in fp:
            fails.append(
                f"G15 {thm}: does not rest on {short} (audited footprint {sorted(fp)}). Either the "
                "audit is stale, or the sentence was re-derived without the bridge -- and the "
                "second is the claim S4 was made to establish.")
        extra = sorted(a for a in fp if a in rec["substantive"] and a != bridge)
        if extra:
            fails.append(
                f"G15 {thm}: carries a SECOND price {extra} beside {short}. The author's sentence "
                "is to cost one META; a second one is a new bridge nobody disclosed.")

    if "→" in rec["theorem_statement"]:
        fails.append(
            f"G15 {thm}: its statement carries a premise (`→`). {short} dropped the "
            "`Core.rightWrongDistinction` antecedent deliberately, so a conditional re-derivation "
            "silently restores the very dependency the retirement was for.")

    if rec["retired_redeclared_in"]:
        fails.append(
            f"G15 {RETIRED_BRIDGE.rsplit('.', 1)[-1]} is re-declared in "
            f"{rec['retired_redeclared_in']}. It was RETIRED, not co-held: two plurality bridges "
            "is a second price for one sentence and two justifications a reader must choose "
            "between.")
    if rec["retired_in_census"]:
        fails.append(
            f"G15 {RETIRED_BRIDGE.rsplit('.', 1)[-1]} is still in the META census -- it was retired "
            "on 2026-10-04, so a census that still counts it is counting a declaration the kernel "
            "does not have.")

    if not rec["bridge_in_census"]:
        fails.append(
            f"G15 {short} is not among the META axioms depgraph declares. The reader-facing badge "
            "is derived from the audited footprint crossed with the declared tag, so a missing tag "
            "silently renders every plural person row free.")
    if rec["meta_count"] != EXPECTED_META_COUNT:
        fails.append(
            f"G15 the META census holds {rec['meta_count']} axioms, expected {EXPECTED_META_COUNT}. "
            "S4 replaced one META with one META and the net move was zero; if this fires, an axiom "
            "moved without `check_consistency.EXPECTED_AXIOM_STATEMENTS` and the breakdown in "
            "`test_axiom_census.py` moving in the same change.")

    for cid, status in rec["rows_about_bridge"]:
        if status.upper() != "AXIOM":
            fails.append(
                f"G15 GAPMAP {cid} is about {short} but its status reads {status!r}. A bridge is "
                "AXIOM or it is nothing; PROVEN or PROVEN↑ on the bridge's own row presents the "
                "author's premise as a derivation, which is the whole laundering D1 was about.")
    return fails


def _g15_reader_tests() -> list[tuple[str, bool]]:
    """The READER that decides which GAPMAP row is about the bridge, tested on synthetic tables.

    D10 was a defect in this function, not in the tree, and the record-level mutation tests
    could not see it: they hand `g15_failures` a pre-built `rows_about_bridge`, so the step
    that was wrong — deciding membership — was never exercised. A gate on a reader needs its
    own tests, fed text, or it is the one part of the gate nobody pinned.
    """
    bridge_cell = ("`TwoNecessaryPersonalCentres.AxTwoNecessaryPersonalCentres : ∃ s₁ s₂, "
                   "Person s₁ ∧ Person s₂` — a ponte")
    thm_cell = ("`Plurality.two_necessary_persons : ∃ s₁ s₂, Person s₁ ∧ Person s₂` — a "
                "frase-alvo, sai de `TwoNecessaryPersonalCentres.AxTwoNecessaryPersonalCentres`")
    hdr = ("| Claim | Secao | Declaracao | Status | Pegada |\n"
           "|---|---|---|---|---|\n")
    out = [
        ("a row whose CLAIM is the bridge is found",
         _g15_gapmap_rows(hdr + f"| C584 | §28 | {bridge_cell} | AXIOM | "
                          "`{Means, NecessarySubjectKind, Subject, Will, subjectWill}` |\n")
         == [("C584", "AXIOM")]),
        ("a row that only MENTIONS the bridge in prose is NOT about it (D10)",
         _g15_gapmap_rows(hdr + f"| C585 | §28 | {thm_cell} | PROVEN↑ | "
                          "`{AxTwoNecessaryPersonalCentres, Means, NecessarySubjectKind}` |\n")
         == []),
        ("the bare short name also resolves",
         _g15_gapmap_rows(hdr + "| C999 | §28 | `AxTwoNecessaryPersonalCentres` | AXIOM | — |\n")
         == [("C999", "AXIOM")]),
        ("a same-named declaration in ANOTHER module is not the bridge",
         _g15_gapmap_rows(hdr + "| C999 | §28 | `Value.AxTwoNecessaryPersonalCentres` | AXIOM | — |\n")
         == []),
        ("a `Logos.`-qualified ref matches NO row -- and must, because the ledger's own parser "
         "skips that prefix, so such a cell has no live declaration and is already a MISSING row "
         "(`test_deduction_dependencies`); the reader must not be more permissive than the parser "
         "it shadows",
         _g15_gapmap_rows(hdr + "| C999 | §28 | `Logos.TwoNecessaryPersonalCentres."
                          "AxTwoNecessaryPersonalCentres` | AXIOM | — |\n")
         == []),
        ("both members of the real pair are scoped apart",
         _g15_gapmap_rows(hdr
                          + f"| C584 | §28 | {bridge_cell} | AXIOM | — |\n"
                          + f"| C585 | §28 | {thm_cell} | PROVEN↑ | — |\n")
         == [("C584", "AXIOM")]),
    ]
    return [(f"G15r {label}", ok) for label, ok in out]


def _g15_negative_tests(base: dict) -> list[tuple[str, bool]]:
    """Mutations of the real record; each must be CAUGHT, and the real record must pass."""
    def mut(**kw):
        r = dict(base)
        r.update(kw)
        return r

    other_meta = "Logos.TrinitarianSubjectBridge.TrinitarianPersonalBridge"
    cases = [
        ("bridge demoted to a theorem",
         mut(kind="theorem")),
        ("bridge re-tagged VOCAB (the laundering decision (A) forbids)",
         mut(tag="VOCAB")),
        ("bridge re-tagged SEM",
         mut(tag="SEM")),
        ("the bridge left out of the author's target sentence",
         mut(theorem_footprint=[a for a in (base["theorem_footprint"] or [])
                                if a != PLURALITY_BRIDGE])),
        ("a SECOND substantive axiom added to the target sentence",
         mut(theorem_footprint=(base["theorem_footprint"] or []) + [other_meta])),
        ("the target sentence's audited footprint vanished",
         mut(theorem_footprint=None)),
        ("the right/wrong antecedent reintroduced (conditional re-derivation)",
         mut(theorem_statement="two_necessary_persons :\n    Core.rightWrongDistinction → ∃ s₁ s₂")),
        ("`AxTwoSubjects` re-declared (a second plurality bridge)",
         mut(retired_redeclared_in=["Value.lean"])),
        ("`AxTwoSubjects` still counted in the META census",
         mut(retired_in_census=True)),
        ("the bridge missing from the META census",
         mut(bridge_in_census=False)),
        ("the census moved (one axiom added or deleted)",
         mut(meta_count=EXPECTED_META_COUNT - 1)),
        ("GAPMAP row about the bridge reads PROVEN↑",
         mut(rows_about_bridge=[("C584", "PROVEN↑")])),
        ("GAPMAP row about the bridge reads PROVEN",
         mut(rows_about_bridge=[("C584", "PROVEN")])),
        ("GAPMAP row about the bridge reads BLOCKED",
         mut(rows_about_bridge=[("C584", "BLOCKED")])),
    ]
    out = [(f"G15n {label}", len(g15_failures(rec)) > 0) for label, rec in cases]
    out.append(("G15n control: the real record passes", len(g15_failures(base)) == 0))
    out.append(("G15n control: an AXIOM row about the bridge passes",
                len(g15_failures(mut(rows_about_bridge=[("C584", "AXIOM")]))) == 0))
    return out


def main():
    audit, depg = load()
    idx = audit_index(audit)
    kinds = dep_kinds(depg)

    # Short names of all audited Logos declarations (used by G2/G4).
    declared = set()
    for key in idx:
        if key.startswith("Logos."):
            declared.add(key.rsplit(".", 1)[-1])

    # Fully-qualified names of the 39 DECLARED axioms. This is the set that makes a price a
    # price. A negative test (inject `Logos.S4.TransinitarianPersonalBridge` into a §20 footprint)
    # is the reason this is not a hard-coded tag tuple.
    declared_axioms = set()
    nodes = depg.get("nodes", depg if isinstance(depg, list) else [])
    for n in nodes:
        if isinstance(n, dict) and n.get("kind") == "axiom":
            declared_axioms.add(n.get("fullName")
                                or (n.get("module", "Logos") + "." + n.get("name", "")))
    if not declared_axioms:
        failures.append("G1 depgraph has no axiom nodes — cannot tell a price from a vocabulary name")

    tags = axiom_tags()
    if not tags:
        failures.append("G1 could not read a single Tag: from formal/Logos/*.lean")

    # --- G1: zero substantive axioms -------------------------------------------------
    for full, why in MUST_BE_FREE:
        if full not in idx:
            failures.append(f"G1 {full}: absent from axiom_audit.json ({why})")
            continue
        fp = idx[full]
        priced, untagged, vocab, undeclared = substantive_in(fp, declared_axioms, tags)
        if priced:
            failures.append(f"G1 {full}: PAID — {sorted(priced)} ({why})")
        elif untagged:
            failures.append(f"G1 {full}: untagged declared axioms {sorted(untagged)} ({why})")
        elif undeclared:
            failures.append(
                f"G1 {full}: under-declared footprint {sorted(undeclared)} "
                "(Logos.* axiom not in depgraph's declared set)")
        else:
            notes.append(
                f"G1 ok  {full}  {len(vocab)} VOCAB ({sorted(x.rsplit('.',1)[-1] for x in vocab)})"
                + (f", total {len(fp)}" if fp else ", empty"))

    # --- G2: the headline asserts the personal-ground structure ------------------------
    # `declared` holds SHORT names (see audit_index consumer above), so compare short.
    for req in ("the_ground_is_not_void_of_personhood",
                "ofGround_grounds_every_person"):
        if req not in declared:
            failures.append(f"G2 prerequisite {req} missing from the audited declarations")

    # `PersonalGround` is a `structure`, and audit_footprints only walks depgraph nodes of kind
    # thm/def/axiom — so it is absent from axiom_audit.json by construction, NOT a defect.
    # Its existence must be checked against the Lean source instead.
    tpg = os.path.join(ROOT, "formal", "Logos", "TrinitarianPersonalGround.lean")
    with open(tpg, encoding="utf-8") as fh:
        tpg_text = fh.read()
    if "structure PersonalGround" not in tpg_text:
        failures.append("G2 structure PersonalGround not found — the headline's type is gone")
    else:
        # Slice the structure body and look for the FIELD declarations in it. A substring test on
        # the whole file is worthless here: `indwells` occurs in six docstrings, so deleting the
        # field still left the word lying around and the gate reported green. (Negative test 3.)
        k = tpg_text.index("structure PersonalGround")
        body = tpg_text[k:tpg_text.index("\n\n", k)] if "\n\n" in tpg_text[k:] else tpg_text[k:]
        fields = re.findall(r"^  (\w+)\s*:", body, re.M)
        if "indwells" not in fields:
            failures.append(
                f"G2 PersonalGround has no `indwells` FIELD (fields: {fields}) — "
                "the homoousios half was dropped")
        elif "sustains" not in fields:
            failures.append(f"G2 PersonalGround has no `sustains` field (fields: {fields})")
        else:
            notes.append(f"G2 ok  PersonalGround fields = {fields}")

    # --- G3: the two halves co-occur in the summary ----------------------------------
    # Both are free of charge, so the audit cannot show co-occurrence. Assert it on the
    # source instead: `PersonalGround Entity.ofGround` and `¬ Asiety Entity.ofGround` must
    # both appear inside `trinitarianPersonalGround_summary`'s type, which is the whole
    # point of that conjunct being deliberate.
    src = os.path.join(ROOT, "formal", "Logos", "TrinitarianPersonalGround.lean")
    with open(src, encoding="utf-8") as fh:
        text = fh.read()
    i = text.find("theorem trinitarianPersonalGround_summary")
    if i < 0:
        failures.append("G3 trinitarianPersonalGround_summary not found in source")
    else:
        chunk = text[i:i + 1800]
        want_pg = "PersonalGround Entity.ofGround"
        want_na = "(¬ Asiety Entity.ofGround)"
        if want_pg not in chunk:
            failures.append(f"G3 summary no longer asserts {want_pg!r}")
        if want_na not in chunk:
            failures.append(f"G3 summary no longer asserts {want_na!r}")
        if want_pg in chunk and want_na in chunk:
            notes.append("G3 ok  PersonalGround Entity.ofGround and ¬ Asiety co-occur in the summary")

    # --- G6: NON-VACUITY — the root cause, in BOTH files that declare the match ----------
    # `OneEssence Entity.ofGround e` is provable for *arbitrary* `e` — including
    # `(ofGround, ofAtom 0)`, no person involved — because `EntityMeans Entity.ofGround p := True`.
    # Closed by hand during the 2026-10-03 audit:
    #     Consubstantial Entity.ofGround e f ↔ True
    # So anything built from it asserts the ground is one-with *everything*: the X1 defect under a
    # new name. A `{}` price on a `True` proposition is not a proof, it is a null result. The arm is
    # kept asserted (not merely reported) because changing it changes the truth of every §20 row
    # routed through `OneEssence`, in both directions.
    #
    # The match is declared TWICE (`Entity.lean` and `RecoveredOntologicalGround.lean`; a NEG12
    # test that flipped only the first was MISSED for exactly that reason), so both are read and
    # the arm is asserted in each. Gate it, don't merely warn: an edit that changes this arm
    # changes the truth of every §20 row that goes through `OneEssence`.
    arm_re = re.compile(r"ofGround\s*=>\s*(True|False)")
    for fname in ("Entity.lean", "RecoveredOntologicalGround.lean"):
        path = os.path.join(ROOT, "formal", "Logos", fname)
        with open(path, encoding="utf-8") as fh:
            text = fh.read()
        arms = arm_re.findall(text)
        if not arms:
            failures.append(
                f"G6 {fname}: no `ofGround => …` arm found in the `EntityMeans` match — "
                "the vacuity root cause moved and this gate no longer knows where it is")
        elif arms[0] != "True":
            failures.append(
                f"G6 {fname}: `EntityMeans Entity.ofGround` arm is {arms[0]!r}, expected 'True' — "
                "if that changed, every §20 row routed through `OneEssence` must be re-audited "
                "for vacuity before this gate can call it free")
        else:
            notes.append(
                f"G6 ok  {fname}: ofGround => True — every OneEssence-routed row at the ground "
                "is provably True of atoms, so none of them may be badged a free doctrine row")

    # --- G7: the deletion and the withdrawal must be RECORDED in GAPMAP -----------------
    # A deleted declaration leaves no trace in the kernel, so the only place a reader learns it
    # was a decision rather than an oversight is GAPMAP. Assert both: the three deleted rows and
    # the C572 verdict change (Modalism, not "unproven").
    gapmap = os.path.join(ROOT, "formal", "GAPMAP.md")
    with open(gapmap, encoding="utf-8") as fh:
        gap = fh.read()
    def status_cell(cid):
        """The GAPMAP *status* column, or None.

        A substring test over the whole row is the wrong instrument here and failed: C572's row
        legitimately contains the word `BLOCKED` in order to *retract* it, so the first version of
        this check reported the corrected row as uncorrected. Narrowing a detector to the string
        the column actually emits is legitimate (AGENTS.md); matching prose is not. So read the
        status column, and separately require the prose to name the retired symbol.
        """
        m = re.search(rf"^\| {cid} \|[^\n]*$", gap, re.M)
        if not m:
            return None, None
        cells = m.group(0).split("|")
        # | id | section | claim | STATUS | footprint |  ->  -1 is "" and -2 the footprint,
        # so the status is -3. Asserted rather than assumed; see the note in the plan.
        if len(cells) < 6:
            failures.append(f"G7 {cid}: GAPMAP row has {len(cells)} cells, expected "
                            "| id | section | claim | status | footprint |")
        return cells[-3].strip(), m.group(0)

    for cid, sym in DELETED_ROWS:
        status, row = status_cell(cid)
        if row is None:
            failures.append(f"G7 {cid}: no GAPMAP row — the deletion of `{sym}` is untracked")
        elif not re.search(r"DELETED|REMOVED", status or "", re.I):
            failures.append(
                f"G7 {cid}: GAPMAP status is {status!r}, not DELETED — the declaration is gone "
                "from the kernel but the row would still read as a live one")
        elif sym not in (row or ""):
            failures.append(
                f"G7 {cid}: GAPMAP row does not name `{sym}`, so it cannot be matched to the "
                "declaration it retires")

    cid, _verdict = WITHDRAWN_CLAIM
    status, row = status_cell(cid)
    if row is None:
        failures.append(f"G7 {cid}: no GAPMAP row — the C572 withdrawal is untracked")
    elif not re.search(r"WITHDRAWN", status or "", re.I):
        failures.append(
            f"G7 {cid}: GAPMAP status is {status!r}. C572 is Modalism (identical meaning across "
            "the Persons is the heresy), so it must be WITHDRAWN, not carried as an open lemma")
    elif re.search(r"BLOCKED", status or "", re.I):
        failures.append(
            f"G7 {cid}: GAPMAP status is {status!r}. BLOCKED implies a lemma provable in "
            "principle; C572 is a claim we should not want (plan §24).")
    else:
        notes.append(f"G7 ok  {cid} status = {status!r}")

    # --- G8: the Perichoretic disclosure must survive --------------------------------------
    # `Perichoretic g a b c` is the master theorem's last conjunct and is definitionally three
    # `OneEssence` instances, so at the ground it is `True` of atoms. Its docstring must keep
    # saying that this is NOT strict perichoresis.
    #
    # WHY THIS GATE WAS REWRITTEN (2026-10-03). The first version required the phrases "mutual
    # grounding" and "asymmetric", and reported "OneEssence asymmetric" as the reason the row is
    # honest. Both halves of that reason were FALSE:
    #   * `PersonalGround` has no `asymmetric` field — only `sustains` and `indwells`;
    #   * `OneEssence` is reflexive (`groundsEntity_reflexive`, FoundationalUnicity.lean:116) and
    #     its asymmetry statement `AsymmetricGrounding` is PROVED UNSATISFIABLE by C316
    #     (`not_asymmetric_grounding`, FoundationalUnicity.lean:145).
    # So the gate was pinning a refuted premise and calling the row honest on that basis — the
    # exact laundering shape AGENTS.md warns about, committed by the gate itself. Phrase-pinning a
    # false claim is not a weaker gate, it is a wrong one.
    #
    # The true reason strict perichoresis is absent is MODALISM: mutual `OneEssence` between two
    # persons is literally the C572 biconditional (identical meaning across the Persons), which
    # was withdrawn as wrongly shaped. Asymmetry would NOT have blocked it. The gate now pins the
    # true reason, and treats "asymmetric" as admissible ONLY inside the retraction of the old
    # claim — so the refuted premise cannot drift back in as a live justification.
    perk = os.path.join(ROOT, "formal", "Logos", "TrinitarianPersonalGround.lean")
    with open(perk, encoding="utf-8") as fh:
        perk_text = fh.read()
    i = perk_text.find("def Perichoretic")
    if i < 0:
        failures.append("G8 `def Perichoretic` not found — the master theorem's conjunct is gone")
    else:
        doc_start = perk_text.rfind("/--", 0, i)
        doc = perk_text[doc_start:i] if doc_start >= 0 else ""
        failures.extend(g8_failures(doc))
        if "mutual grounding" in doc and "Modalism" in doc:
            notes.append(
                "G8 ok  Perichoretic discloses: not a mutual grounding, refused as Modalism "
                "(C572), asymmetry retracted (C316)")

    # --- G9: Consubstantial must stay deleted ----------------------------------------------
    # The laundering route: re-add `Consubstantial` as an `axiom` and a `{}` row becomes a priced
    # one with the doctrine's name on it. Checked against the SOURCES, not depgraph.json, because
    # depgraph is a build artifact and stays stale across an edit (negative test 4).
    lean_dir = os.path.join(ROOT, "formal", "Logos")
    for fname in sorted(os.listdir(lean_dir)):
        if not fname.endswith(".lean"):
            continue
        body = pathlib.Path(lean_dir, fname).read_text(encoding="utf-8")
        hit = re.search(r"^(?:axiom|def|theorem|abbrev|opaque)\s+Consubstantial\b", body, re.M)
        if hit:
            failures.append(
                f"G9 {fname}: `{hit.group(0)}` re-declares Consubstantial — it was deleted in plan "
                "§24 because `Consubstantial Entity.ofGround e f` is `True` for arbitrary `e f` "
                "(including atoms). The one-ness is `indwells`; do not rebuild this.")
    notes.append("G9 ok  Consubstantial is absent from every Lean source (deletion is a guard)")

    # --- G10: the second field exists and distinguishes the Persons -----------------------
    # The 2026-10-03 consistency incident: without `personalProperty : Prop` the
    # `f ≠ o` conjunct of the donation was UNSATISFIABLE and the whole kernel
    # derived `False`. The field is a marker of distinction, not the content of a
    # Person — so the gate checks the marker relation, not the marker's type.
    agape = pathlib.Path(ROOT, "formal", "Logos", "DivineAgape.lean").read_text(encoding="utf-8")
    if not re.search(r"personalProperty\s*:\s*Prop", agape):
        failures.append(
            "G10 `DivineHypostasis.personalProperty : Prop` is gone — the field whose absence "
            "made `f ≠ o` unsatisfiable and the kernel inconsistent. See the dated incident note.")
    else:
        notes.append("G10 ok  `DivineHypostasis.personalProperty : Prop` present")
    for who in ("the_father", "the_beloved"):
        if f"{who}.personalProperty" not in agape and f"{who}, " not in agape:
            pass  # the witnesses need no personalProperty values; the field is a marker
    if "the_beloved_distinct" not in agape:
        failures.append(
            "G10 `the_beloved_distinct` is gone — the explicit proof that the two centres "
            "differ in personal property, i.e. that the donation's `f ≠ o` is satisfiable.")
    else:
        notes.append("G10 ok  `the_beloved_distinct` states the distinction the field buys")

    # --- G11: the donation rows say what they must, priced where they must ---------------
    # C575–C578 plus the honest caveats. The gate reads kernel statements and
    # priced footprints, not phrases: a row whose docstring claims `{}` on a priced
    # footprint, or claims the ground *is* a fourth chooser, must fail.
    g11_targets = {
        "agape_is_self_donation": ["AxAgapeEssence"],
        "denying_self_donation_is_absurd": ["AxAgapeEssence"],
        "denying_shared_location_is_absurd": ["AxAgapeEssence"],
        "self_donation_needs_no_personhood_of_the_ground": ["AxAgapeEssence"],
    }
    def _g11_doc(name: str) -> str:
        i = agape.find(f"theorem {name}")
        perp = pathlib.Path(ROOT, "formal", "Logos", "TrinitarianPersonalGround.lean").read_text(encoding="utf-8")
        src = agape if i >= 0 else perp
        i = src.find(f"theorem {name}")
        if i < 0:
            return ""
        st = src.rfind("/--", 0, i)
        return src[st:i] if st >= 0 else ""
    for name, must_price in g11_targets.items():
        fq = f"Logos.DivineAgape.{name}"
        if fq not in idx and f"Logos.TrinitarianPersonalGround.{name}" not in idx:
            failures.append(f"G11 {name}: absent from axiom_audit.json")
            continue
        fp = idx.get(fq) or idx.get(f"Logos.TrinitarianPersonalGround.{name}", [])
        priced, _, _, _ = substantive_in(fp, declared_axioms, tags)
        if not any(a.rsplit(".", 1)[-1] in must_price for a in priced):
            failures.append(
                f"G11 {name}: does not rest on {must_price} (got {sorted(priced)}) — "
                "the donation must cost its META axiom, or the row is laundering")
        else:
            notes.append(f"G11 ok  {name} priced on {must_price[0]}")
        doc = _g11_doc(name)
        if not doc:
            failures.append(f"G11 {name}: no docstring — the honesty caveats live in code")
    # The Narcissus-world clause on C576's absurdity, and the no-fourth-chooser
    # clause on C578's conjunction: both are load-bearing honesty content.
    d576 = _g11_doc("denying_self_donation_is_absurd")
    if "Narcissus" not in d576 or "C511" not in d576:
        failures.append(
            "G11 C576's docstring lost the Narcissus-world (C511) clause — without it the "
            "absurdity reads as logic rather than as relative to the declaration.")
    else:
        notes.append("G11 ok  C576 keeps the Narcissus-world honesty clause")
    d578 = _g11_doc("self_donation_needs_no_personhood_of_the_ground")
    if "fourth chooser" not in d578.lower() or "not a fourth chooser" not in d578.lower():
        failures.append(
            "G11 C578's docstring lost the no-fourth-chooser conjunction — the point of the "
            "row is the refusal AND the donation, stated together.")
    else:
        notes.append("G11 ok  C578 keeps the refusal-and-donation conjunction")

    # --- G12: the donation disclosure is mutation-verified -------------------------------
    # `g12_failures(doc)` is the whole rule: the donation's docstring must name the
    # field, the shared location, and the priced axiom. Tested by mutation below.
    g12_cases = _g12_negative_tests()
    g12_bad = [label for label, ok in g12_cases if not ok]
    for label, ok in g12_cases:
        notes.append(("G12n ok  " if ok else "G12n FAIL  ") + label)
    if g12_bad:
        failures.append(
            f"G12 rule is not verified: {len(g12_bad)} mutation(s) of the donation docstring "
            "were NOT caught: " + "; ".join(g12_bad))

    # --- G13/G14: the granted premise and the price line, on the rendered page ----------
    # Both rules read the GENERATED README, not the Lean source, because the defect
    # each one catches is a rendering decision: a premise-role target captioned as an
    # answer, and a glyph/count pair that disagrees. Checking the source would pass
    # while the page still lied.
    readme_path = pathlib.Path(ROOT, "README.md")
    readme = readme_path.read_text(encoding="utf-8") if readme_path.exists() else ""
    if not readme:
        failures.append("G13/G14 README.md is missing or empty — run build_deduction.py first")
    else:
        anchor_id = '<a id="ground_is_not_a_fourth_chooser"></a>'
        i = readme.find(anchor_id)
        if i < 0:
            failures.append(
                "G13 R21's granted premise (`ground_is_not_a_fourth_chooser`) is no longer on the "
                "reading path \u2014 the row must stay mounted, with its premise labelled as granted.")
            notes.append("G13 FAIL  granted-premise block absent")
        else:
            # The block runs to the next anchor or heading.
            rest = readme[i + len(anchor_id):]
            nxt = re.search(r"\n<a id=|\n#{2,4} ", rest)
            block = rest[:nxt.start()] if nxt else rest
            g13 = g13_failures(block)
            for f_ in g13:
                failures.append(f_)
            notes.append("G13 ok  the granted premise is labelled, kills nothing"
                         if not g13 else "G13 FAIL  " + "; ".join(g13))
        # Consecutive PRICE lines are ONE block's price group (the countermodel
        # block prints three), so the rule reads each group, not each line.
        price_groups, cur = [], []
        for ln in readme.splitlines():
            if ln.strip().startswith("PRICE"):
                cur.append(ln.strip())
            elif cur:
                price_groups.append(cur)
                cur = []
        if cur:
            price_groups.append(cur)
        g14_bad = 0
        for grp in price_groups:
            g14 = g14_failures("\n".join(grp))
            if g14:
                g14_bad += 1
                for f_ in g14:
                    failures.append(f_ + f" [group: {grp[0][:60]}]")
        if price_groups and not g14_bad:
            notes.append(f"G14 ok  all {len(price_groups)} PRICE groups agree with their count")

    # G13/G14's own rules are mutation-verified, on the same principle as G8/G12: a
    # gate that cannot fail is not evidence. Run before printing anything.
    g1314_cases = _g13_g14_negative_tests()
    g1314_bad = [label for label, ok in g1314_cases if not ok]
    for label, ok in g1314_cases:
        notes.append(("G13n/G14n ok  " if ok else "G13n/G14n FAIL  ") + label)
    if g1314_bad:
        failures.append(
            f"G13/G14 rule is not verified: {len(g1314_bad)} mutation(s) were NOT caught: "
            + "; ".join(g1314_bad))

    # G8's own rule is verified by mutation, so "the gate passes" is not the same claim as
    # "the gate can fail". Run before printing anything.
    g8_cases = _g8_negative_tests()
    g8_bad = [label for label, ok in g8_cases if not ok]
    for label, ok in g8_cases:
        notes.append(("G8n ok  " if ok else "G8n FAIL  ") + label)
    if g8_bad:
        failures.append(
            f"G8 rule is not verified: {len(g8_bad)} mutation(s) of the docstring were NOT caught "
            + "; ".join(g8_bad))

    # --- G15: the plurality bridge is priced, once, and visibly (LOVE-3/S7) ---------------
    # `Value.AxTwoSubjects` was retired on 2026-10-04 and replaced by
    # `TwoNecessaryPersonalCentres.AxTwoNecessaryPersonalCentres`, which carries the author's
    # necessity argument instead of re-stating that plurality is required. G11 above is
    # deliberately left INVERTED-PENDING: it still asserts the donation rows rest on
    # `AxAgapeEssence`, which is true while S3 is blocked (LOVE-3 §0.2). G15 is the counterpart
    # for the bridge that *did* land.
    g15 = g15_record(idx, declared_axioms, tags, kinds, gap)
    g15_fails = g15_failures(g15)
    failures.extend(g15_fails)
    notes.append(
        f"G15 {'FAIL' if g15_fails else 'ok  '} {PLURALITY_BRIDGE.rsplit('.', 1)[-1]}:"
        f" kind={g15['kind']}, Tag={g15['tag']}, META census={g15['meta_count']},"
        f" rows about it in GAPMAP={len(g15['rows_about_bridge'])}"
        + ("" if g15["rows_about_bridge"] else " (no GAPMAP row claims the bridge)"))
    # The READER that decides which row is about the bridge is gated separately (D10): it is
    # the one step the record-level mutations hand over pre-built.
    g15r_cases = _g15_reader_tests()
    g15r_bad = [label for label, ok in g15r_cases if not ok]
    for label, ok in g15r_cases:
        notes.append(("G15r ok  " if ok else "G15r FAIL  ") + label)
    if g15r_bad:
        failures.append(
            f"G15 reader is not verified: {len(g15r_bad)} scoping case(s) failed: "
            + "; ".join(g15r_bad))
    g15_cases = _g15_negative_tests(g15)
    g15_bad = [label for label, ok in g15_cases if not ok]
    for label, ok in g15_cases:
        notes.append(("G15n ok  " if ok else "G15n FAIL  ") + label)
    if g15_bad:
        failures.append(
            f"G15 rule is not verified: {len(g15_bad)} mutation(s) were NOT caught: "
            + "; ".join(g15_bad))

    for line in notes:
        print(line)
    for line in failures:
        print("FAIL " + line)

    if failures:
        print(f"\npersonal-ground-kind gate: {len(failures)} failure(s)")
        return 1
    print("\npersonal-ground-kind gate: doctrine rows free, both halves co-occur, "
          "Consubstantial deleted, Perichoretic's disclosure intact "
          "(C572 Modalism; C316 asymmetry retraction), donation still priced on "
          "AxAgapeEssence (S3 blocked), plurality bridge priced once at META.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
