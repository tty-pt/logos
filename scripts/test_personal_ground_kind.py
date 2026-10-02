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
      reintroducing it as an `axiom` is the laundering route that once gave it a price.

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
# shared helpers so there is exactly one comment-stripping implementation.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_consistency import lean_comment_lines, axiom_statements  # noqa: E402

PRICED_TAGS = ("SEM", "META", "TRANS")  # VOCAB is the vocabulary of the statement itself


def axiom_tags():
    """Map fully-qualified axiom name -> Tag, by reading the Lean sources.

    Reuses `check_consistency.axiom_statements`, the *same* parser the 39-axiom census uses
    (comment-stripping included). One implementation, so a tag this gate reads and a tag the
    census counts cannot drift apart — the drift `lean_comment_lines` exists to prevent.

    A `Tag:` line is **always inside a comment** (it lives in the `/-- … -/` docstring), so it is
    masked by construction and must be found on the *masked* lines. The first version filtered
    them out with `not masked[i]`, which silently produced `None` for every axiom — and a `None`
    tag falls into the "untagged" bucket, so the gate reported *the right verdict for the wrong
    reason*. Negative test 2 caught it: injecting the real `TrinitarianPersonalBridge` (a genuine
    `Tag: META`) came back "untagged", not "PAID".

    So: collect Tag lines from the masked stream, then scan **backwards from the `axiom` line**
    (which is unmasked) to the nearest one. Backwards, not forwards — a forward scan reaches the
    *next* axiom's docstring and attributes its tag to this one.
    """
    out = {}
    lean_dir = os.path.join(ROOT, "formal", "Logos")
    for fname in sorted(os.listdir(lean_dir)):
        if not fname.endswith(".lean"):
            continue
        path = Path(lean_dir) / fname
        raw = path.read_text(encoding="utf-8").splitlines()
        masked = lean_comment_lines(raw)
        tags_by_line = {}
        for i, raw_line in enumerate(raw):
            if "Tag:" not in raw_line:
                continue
            for t in ("VOCAB", "SEM", "META", "TRANS"):
                if t in raw_line:
                    tags_by_line[i] = t
                    break
        module = "Logos." + fname[:-5]
        for name, _stmt, line in axiom_statements(path):
            tag = None
            i = int(line)
            while i >= 0:
                if i in tags_by_line:
                    tag = tags_by_line[i]
                    break
                # Stop at the previous axiom's line: that docstring's tag is not ours.
                if i != int(line) and masked[i] and raw[i].strip().startswith("/--"):
                    break
                i -= 1
            out[f"{module}.{name}"] = tag
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

    for line in notes:
        print(line)
    for line in failures:
        print("FAIL " + line)

    if failures:
        print(f"\npersonal-ground-kind gate: {len(failures)} failure(s)")
        return 1
    print("\npersonal-ground-kind gate: doctrine rows free, both halves co-occur, "
          "Consubstantial deleted, Perichoretic's disclosure intact "
          "(C572 Modalism; C316 asymmetry retraction).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
