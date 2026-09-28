/-
# Logos.MeaningRetorsion — the meaninglessness thesis, refuted (batch of 2026-09-27)

The author's sentence:

> to affirm that there is no meaning **is to prove the invalidity of my own
> affirmation**

and its companion demand:

> the countermodel is wrong, and you shall prove it.

This module proves the first without a new axiom, and answers the second in the
only form in which it is true.

## The distinction the whole batch turns on

`NegativeRetorsionAudit.lean:292-295` already records it:

> `NoI is false` is **not** equivalent to `NoI is unassertable`.

So there are two objects and they come apart:

* the **content** `NoMeaning` — a populated world in which nothing is meant is a
  model of it, and Section 3c (`the_meaningless_world_remains_a_model`) is the
  machine-checked proof. The content is *not* refuted, and this module does not
  claim it is.
* the **affirmation** of the content — `Asserts s NoMeaning` — which is
  self-refuting, unconditionally, with no hypothesis and no axiom beyond the
  declared meaning vocabulary (`noMeaning_is_unassertable`).

What the retorsion yields is the second. What it does not yield is the first.
The corpus says so in F13 and in C294, and this module does not overturn it.

## How this answers "the countermodel is wrong"

As an **answer**, and signature-universally. A countermodel is not a
counterexample; it is a *description of a world*. An answer is a move made
inside discourse. M1 and C294 describe worlds in which no move is ever made:
`Means := fun _ _ => False` and `act := fun _ _ => False`. To hold the thesis
*as an answer* one must affirm the denial of the act-datum, and that
conjunction is refutable at `{}` (`the_two_denials_cannot_both_be_affirmed`).

So the honest reading, which goes verbatim into the GAPMAP batch note:

> The countermodel is not refuted as a model; it is refuted as an **answer**.

## Cost

**Zero new axioms.** Every declaration below is a `theorem` over `def`s and
existing rows. This is the batch's one substantive claim about its own price,
and gate B2 checks it rather than assuming it.

## What is new here, and what is not

`no_countermodel_can_affirm_the_thesis` is a
**corollary** of the existing `level2_signature_asserts_noi_selfRefutes`
(`NegativeRetorsionAudit.lean:286`) and its docstring says so. The batch's
novelty rests on four items that are not instantiations of existing rows:

1. `NoMeaning` — the thesis in the corpus's own `Meaning_I` vocabulary
   (`base.txt` §26 item 3, `poem.txt` P3), and its identity with the audited
   `NoI_canonical`;
2. the `Correct`/judgeability rung, which exists for the act-thesis
   (`Order.no_correct_judgment_of_no_act`) and for nothing else in the corpus;
3. the signature-general **weak** retorsion — `Agency.noWeakAct_selfRefutes`
   (`Agency.lean:263`) is canonical-only;
4. the **populated** complement — `unassertability_does_not_imply_falsity`
   (`:296`) is M0, the empty subject sort, so the populated form was missing.
-/

import Logos.Core
import Logos.Agency
import Logos.Choice
import Logos.Order
import Logos.NegativeRetorsionAudit
import Logos.Plurality

namespace Logos.MeaningRetorsion

open Logos.Agency (Subject Means Act Asserts State Initiates act)
open Logos.Choice (Meaning_I)
open Logos.Order (Correct Incorrect)
open Logos.NegativeRetorsionAudit (NegativeRetorsionSignature NoI_canonical
  level2_signature_asserts_noi_selfRefutes)

-- ============================================================================
-- Section 0: the thesis in the corpus's own vocabulary
-- ============================================================================

/-- **"There is no meaning."** The negative of `poem.txt` P3 ("há significado",
    line 18) and of `base.txt` §26 item 3 ("Não existe conteúdo"), stated in
    the meaning vocabulary the corpus already uses rather than in the internal
    `IntentionalSubject` form. `base.txt` §11 defines `Meaning_I p := ∃ s,
    Means s p`, so the subject is a constituent of the notion and the thesis is
    `¬ ∃ p, ∃ s, Means s p`.

    This `def` is the sentence §26 item 3 asserts. Before this module no named
    `NoMeaning` existed anywhere in Γ.
    Footprint: `{Means, Subject}`. -/
def NoMeaning : Prop := ¬ ∃ p : Prop, Meaning_I p

/-- **The thesis and the audited negation of the retorsive conclusion are the
    same sentence, re-indexed.** `NoI_canonical := ¬ P_canonical` and
    `P_canonical := ∃ s, IntentionalSubject s` with `IntentionalSubject s := ∃ p,
    Means s p`; `NoMeaning` is `¬ ∃ p, ∃ s, Means s p`. The two differ only in
    the order of two existential quantifiers, so the equivalence is pure logic.

    Stated as an `Iff` rather than an `=` deliberately: the formulas are *not*
    definitionally equal (the quantifiers are bound in the opposite order), and an
    `=` form would need a cast, which would make the reader wonder whether the
    identity is definitional. It is not; it is a re-index. The audited footprint is
    `{Means, Subject}` with **no `propext`**, and that absence is the machine-checked
    confirmation that the re-index needs no extensionality axiom. -/
theorem noMeaning_iff_noIntentionalSubject : NoMeaning ↔ NoI_canonical := by
  constructor
  · intro hNoM hP
    obtain ⟨s, hInt⟩ := hP
    obtain ⟨p, hMeans⟩ := hInt
    exact hNoM ⟨p, s, hMeans⟩
  · intro hNoI hEx
    obtain ⟨p, hMI⟩ := hEx
    obtain ⟨s, hMeans⟩ := hMI
    exact hNoI ⟨s, p, hMeans⟩

/-- The pointwise reading of the thesis: no subject means anything at all. The
    corpus already draws this equivalence for `NoI_canonical`
    (`noi_canonical_iff_pointwise`); this is the `Meaning_I` re-index of it.
    Footprint: `{Means, Subject}`. -/
theorem noMeaning_iff_pointwise :
    NoMeaning ↔ ∀ s : Subject, ¬ ∃ p : Prop, Means s p := by
  constructor
  · intro hNoM s
    rintro ⟨p, hMeans⟩
    exact hNoM ⟨p, s, hMeans⟩
  · intro hAll ⟨p, s, hMeans⟩
    exact hAll s ⟨p, hMeans⟩

-- ============================================================================
-- Section 0b: the performance without the success condition
-- ============================================================================

/-- **To voice a proposition is to perform it, with no condition on its truth.**
    The author's "it can be uttered, it can be asserted" — the performance the
    performative contradiction leaves standing, since it refutes only the act
    *succeeding* (C375). Every `asserts` in the corpus carries `∧ p`
    (`asserts s p := act s p ∧ p`, `Asserts s p := Act s p ∧ p`,
    `Correct s p := A s p ∧ T p`), so the truth-agnostic one had no name.

    Built on the weak `act`, not `Act`: `Act` requires `Means`, and C372 already
    excludes `Act s NoMeaning` wherever `NoMeaning` holds, so an `Act`-based
    assertion-predicate could never witness the thesis being said.
    Footprint: `{Subject, act}`. -/
def Voices (s : Subject) (p : Prop) : Prop := act s p

-- ============================================================================
-- Section 1: the ladder — four rungs, each a way of taking the thesis
-- ============================================================================

/-!
The thesis cannot be *meant*, cannot be *acted*, cannot be *judged correct*, and
cannot be *affirmed*. The first two are already on record for `NoI_canonical`
(`canonical_noi_implies_not_means` `:204`, `canonical_noi_implies_not_act`
`:330`); they are restated here in the `Meaning_I` vocabulary so that the ladder
is one object. The third is new to the corpus for any meaninglessness thesis.
The fourth is unconditional.
-/

/-- **1/4 — the thesis cannot be meant.** If nothing is meant, no subject means
    the thesis; the thesis is among the things that would have to be meant for it
    to be true, so it is unmeaned. This is the self-application closed at the
    `Means` rung, and it is consistent — a universal negative is not a liar.
    Footprint: `{Means, Subject}`. -/
theorem noMeaning_is_unmeaned (s : Subject) : NoMeaning → ¬ Means s NoMeaning := by
  intro hNoM hMeans
  exact hNoM ⟨NoMeaning, s, hMeans⟩

/-- **2/4 — the thesis cannot be entertained as an act.** The act-rung: `Act` is
    the meaning-act, so performing the thesis as an act already means it.
    Footprint: `{Initiates, Means, State, Subject}`. -/
theorem noMeaning_is_unperformed (s : Subject) : NoMeaning → ¬ Act s NoMeaning := by
  intro hNoM hAct
  exact noMeaning_is_unmeaned s hNoM hAct.1

/-- **3/4 — the thesis cannot be judged correct.** NEW: the corpus has a
    `Correct`-rung for the *act*-thesis (`Order.no_correct_judgment_of_no_act`,
    `Order.lean:203`) and for nothing else. Judging `NoMeaning` correct is
    `Correct s NoMeaning`, whose second conjunct is `T NoMeaning`, i.e. the
    thesis itself; and whose first conjunct is an act of meaning it. The act
    supplies the meaning the thesis denies, and the truth-claim supplies the
    thesis. Pure logic, no axiom, and it places the thesis outside Γ's own
    epistemic criterion (F12 `JudicativeGood`).
    Footprint: `{Initiates, Means, State, Subject}`. -/
theorem no_correct_judgment_of_noMeaning (s : Subject) : ¬ Correct s NoMeaning := by
  intro hc
  exact hc.2 ⟨NoMeaning, s, hc.1.1⟩

/-- **3'/4 — the exhaustive form.** Mirroring `Order.judgment_of_no_act_is_incorrect`:
    whoever judges the thesis at all judges it incorrectly. Error is the only
    status the thesis can have as a judgment.

    This adds nothing over 3/4 logically — it is the same content packaged as
    exhaustiveness over the bivalent partition — and it is landed for the
    ledger's sake, so that the meaninglessness thesis appears in the corpus
    beside the act-thesis in the same two-row shape.
    Footprint: `{Initiates, Means, State, Subject}`. -/
theorem judgment_of_noMeaning_is_incorrect (s : Subject)
    (h : Correct s NoMeaning ∨ Incorrect s NoMeaning) : Incorrect s NoMeaning := by
  cases h with
  | inl hc => exact False.elim (no_correct_judgment_of_noMeaning s hc)
  | inr hi => exact hi

/-- **4/4 — THE RETORSION, unconditional.** Nobody can hold the thesis as
    correct. No hypothesis, no subject supplied, no bridge, no axiom beyond the
    declared meaning vocabulary: `Asserts s p` is `Act s p ∧ p`, so an assertion
    of the thesis is at once an act meaning it (forbidden by 1/4, given the
    thesis) and a truth-claim of the thesis (which is the thesis). Either
    conjunct alone is fatal.

    This is the author's sentence in the corpus's form, and it is the honest
    limit of it: the affirmation is the *input* that makes the contradiction,
    so the retorsion is free in axioms and **not free in performance**.
    Footprint: `{Initiates, Means, State, Subject}`. -/
theorem noMeaning_is_unassertable : ¬ ∃ s : Subject, Asserts s NoMeaning := by
  rintro ⟨s, hAssert⟩
  exact noMeaning_is_unmeaned s hAssert.2 hAssert.1.1

/-- The ladder in one conjunction, for the ledger: the four rungs at once, with
    the last one unconditional.
    Footprint: `{Initiates, Means, State, Subject}`. -/
theorem noMeaning_ladder :
    (∀ s : Subject, NoMeaning → ¬ Means s NoMeaning) ∧
    (∀ s : Subject, NoMeaning → ¬ Act s NoMeaning) ∧
    (∀ s : Subject, ¬ Correct s NoMeaning) ∧
    (¬ ∃ s : Subject, Asserts s NoMeaning) :=
  ⟨fun s h => noMeaning_is_unmeaned s h,
   fun s h => noMeaning_is_unperformed s h,
   fun s => no_correct_judgment_of_noMeaning s,
   noMeaning_is_unassertable⟩

-- ============================================================================
-- Section 2: the author's sentence as a positive existence theorem
-- ============================================================================

/-- **The retorsion, positively.** To affirm that there is no meaning is itself
    a meaning: affirming the thesis produces an instance of exactly what the
    thesis denies. The conclusion is the `Meaning_I` form with the content
    *named* — `NoMeaning` itself is the proposition that comes out meaning.

    This is the shape the author asked for ("it is not unutterable, I have just
    uttered it") and it is the contraposition-dual of `noMeaning_is_unassertable`.
    It is **not** a renamed premise: the conclusion is `Meaning_I` over a named
    content rather than an existential-existential.

    **Generalized 2026-09-27: hypothesis `Act`, not `Asserts`.** `Asserts s p` is
    `Act s p ∧ p`, so the old statement is the special case and this one
    subsumes it; the C-id is unchanged because the proposition grew. The
    hypothesis is still not to be had on demand — C372 excludes
    `Act s NoMeaning` wherever `NoMeaning` holds — so the reading is the brief's:
    whoever performs the thesis meaningfully thereby refutes it.
    Footprint: `{Initiates, Means, State, Subject}`. -/
theorem affirms_noMeaning_yields_meaning :
    (∃ s : Subject, Act s NoMeaning) → ∃ p : Prop, Meaning_I p := by
  rintro ⟨s, hs⟩
  exact ⟨NoMeaning, s, hs.1⟩

/-- The same at the judging level, which is the form `poem.txt` P3 actually
    uses: "há certo e há errado → há significado". Judging the thesis correct
    already exhibits a meaning.
    Footprint: `{Initiates, Means, State, Subject}`. -/
theorem judges_noMeaning_yields_meaning :
    (∃ s : Subject, Correct s NoMeaning) → ∃ p : Prop, Meaning_I p := by
  rintro ⟨s, hs⟩
  exact ⟨NoMeaning, s, hs.1.1⟩

/-!
### Why these do not yield `¬ NoMeaning`

Both theorems are *implications from* an affirmation. The unconditional claim
`¬ NoMeaning` does not follow, because the affirmation is not available in
advance — it is the thing being paid for. A world in which nobody ever affirms
anything satisfies `NoMeaning` and has nothing to refute it with; that world is
exhibited in Section 3c. This is the asymmetry the corpus already records at
`NegativeRetorsionAudit.lean:292-295`, and it is why the batch states the
unconditional form as a *refutation* (C375) rather than as a theorem that the
thesis is false.
-/

-- ============================================================================
-- Section 3: the joint refutation of M1 and C294 — as answers
-- ============================================================================

/-!
M1 (`NegativeRetorsionAudit.lean:157`) and C294 (`AsietyFreedom.lean:265`) are
not two unrelated artefacts. They are instances of one family: *a
meaning-vocabulary in which nothing is meant*. Both come with the same
withholding — M1 sets `act := fun _ _ => False` as well as `Means := False`, so
the denial extends past meaning to the performed event itself.

That withholding is what makes them refutable as **answers**. An answer is a
move made inside discourse. A world with no moves has no answers, and so cannot
contain the affirmation of its own silence. The refutation is stated once, over
the signature, and comes in two halves: the half that kills them, and the
complement that keeps it honest.
-/

/-- **No model of the meaning vocabulary, of any shape, can host an affirmation
    of the thesis.** In any signature whatsoever, if nothing is meant then
    nothing affirms the claim that nothing is meant.

    **This is a corollary, not a discovery.** It is
    `level2_signature_asserts_noi_selfRefutes` (`NegativeRetorsionAudit.lean:286`)
    generalised from one signature to all of them, and the corpus already had it
    for `NoI_canonical`. It is landed and badged here because (a) it is the
    sentence the author actually asked for, stated once over the signature, and
    (b) `NoI_canonical` is the internal form, while `base.txt` §26 item 3 is
    `NoMeaning`. The batch's novelty rests on the other four items, not on this one.
    Footprint: `{}`. -/
theorem no_countermodel_can_affirm_the_thesis :
    ∀ (S : NegativeRetorsionSignature), S.NoI → ¬ ∃ s : S.Subject, S.Asserts s S.NoI := by
  intro S _hNoI ⟨s, hAss⟩
  exact level2_signature_asserts_noi_selfRefutes S s hAss

/-- The weak act-datum denial, in the audit signature: no performed event
    occurs at all. `Agency.NoWeakAct` states this for Γ's canonical vocabulary;
    this states it for an arbitrary signature, which is what the joint refutation
    needs in order to quantify over the countermodels.

    M1 satisfies this (`act := fun _ _ => False`, `NegativeRetorsionAudit.lean:163`).
    Footprint: `{}`. -/
def NoWeakActIn (S : NegativeRetorsionSignature) : Prop :=
  ¬ ∃ (_s : S.Subject) (_p : Prop), S.act _s _p

/-- **The weak retorsion, signature-general.** Affirming that no performed event
    occurs is self-refuting: the affirmation is itself a performed event. This
    is `Agency.noWeakAct_selfRefutes` (`Agency.lean:263`) lifted from Γ's
    canonical vocabulary to an arbitrary signature — the canonical version is
    the only one on record. Footprint: `{}`. -/
theorem signature_weak_retorsion (S : NegativeRetorsionSignature) (s : S.Subject) :
    S.asserts s (NoWeakActIn S) → False := by
  intro h
  exact h.2 ⟨s, NoWeakActIn S, h.1⟩

/-- **THE JOINT REFUTATION, in one sentence.** A meaning-vocabulary in which
    nothing is meant cannot also be one in which the act-datum is denied *and
    that denial is then affirmed*. M1 and C294 are refuted as answers here, and
    the refutation costs no axiom: the denial of the act, once affirmed, is an
    act.

    The first conjunct is not needed for the proof and is kept because the
    reading depends on it — it says *the countermodel's own world is the kind of
    world in which the thesis is unstateable*, which is the whole answer to
    "the countermodel is wrong". Footprint: `{}`. -/
theorem the_two_denials_cannot_both_be_affirmed :
    ∀ (S : NegativeRetorsionSignature),
      S.NoI → NoWeakActIn S → ¬ ∃ s : S.Subject, S.asserts s (NoWeakActIn S) := by
  intro S _hNoI _hNoWeakAct ⟨s, hAss⟩
  exact signature_weak_retorsion S s hAss

/-- **THE COMPLEMENT — and this is what makes the two halves honest rather than
    a trick.** A world with subjects, no meaning anywhere, the thesis true, and
    the thesis unassertable. This is the exact shape of M1 with the
    `Asserts`-total-unassertability conjunct made explicit, and it is
    **consistent**.

    The corpus has `unassertability_does_not_imply_falsity`
    (`NegativeRetorsionAudit.lean:296`), but it is built on **M0, the empty
    subject sort**, where `∀ s, ¬ S.Asserts s S.NoI` holds *vacuously* — a weak
    counterpoint, trivially satisfiable by an empty domain. This is the
    populated version, and it was not on record.

    Consequences, and they are the price of the refutation above:

    * the countermodel is refuted as an **answer**, not as a **model**;
    * the *content* `NoMeaning` stays consistent **as a free signature** — which is
      what this theorem shows, and all it shows. It is *not* consistent *in Γ*:
      C401/C402 (Section 4) refute it there, on the plurality bridge and on the
      act-datum respectively. The earlier form of this bullet ("stays alive and
      stays consistent" without qualification) is withdrawn as overstated;
    * the positive claim still costs `AxTwoSubjects` (C367) for a subject that is
      not supplied as input.

    Gate B4 enforces this: if the three theorems above ever land without this
    one, the batch stops. Footprint: `{}`. -/
theorem the_meaningless_world_remains_a_model :
    ∃ (S : NegativeRetorsionSignature), (∃ _s : S.Subject, True) ∧
      S.NoI ∧ (∀ s : S.Subject, ¬ S.Asserts s S.NoI) := by
  let S1 : NegativeRetorsionSignature := {
    Subject    := Unit
    Means      := fun _ _ => False
    State      := Unit
    Initiates  := fun _ _ _ _ => False
    act        := fun _ _ => False
    DomainItem := Unit
    ofProp     := fun _ => ()
    DependsOn  := fun _ _ => False
    EO         := True
  }
  refine ⟨S1, ⟨(), trivial⟩, ?_, ?_⟩
  · rintro ⟨_, _p, hMeans⟩
    exact hMeans
  · intro _s hAss
    exact hAss.1.1

/-- The two halves read together, as a single machine-checked statement: the
    countermodel's world is a world in which the thesis is true, and the thesis
    cannot be affirmed anywhere — including there. The conjunction is the
    honest form of "the countermodel is wrong".
    Footprint: `{}`. -/
theorem countermodel_is_a_world_where_the_thesis_is_unutterable :
    (∃ (S : NegativeRetorsionSignature), (∃ _s : S.Subject, True) ∧
        S.NoI ∧ (∀ s : S.Subject, ¬ S.Asserts s S.NoI)) ∧
      (∀ (S : NegativeRetorsionSignature), S.NoI → ¬ ∃ s : S.Subject, S.Asserts s S.NoI) :=
  ⟨the_meaningless_world_remains_a_model, no_countermodel_can_affirm_the_thesis⟩

/-!
### Section 3d: and the world in which the thesis *is* uttered

C382's world with one field changed — the walk-back of C383's name.
-/

/-- **The thesis can be uttered: a world with a subject, no meaning anywhere, the
    thesis true, the thesis performed — and no assertion of it that succeeds.**
    C382's world with `act := True` in place of `False`; the third conjunct is
    C379 applied to it. C385 is what makes C383's "unutterable" a misnomer
    rather than a reading.

    `S.act` and not `Act` because C372 excludes `Act s NoMeaning` wherever
    `NoMeaning` holds: in a world where the thesis is true the only available
    act of it is the weak one. That is "saying it is not thinking it", and it is
    why `Voices` (C384) is built on `act`. The same instance disposes of C294's
    countermodel as an answer, since that lifts into this signature by setting
    `Means := M`, `act := True`.

    The retorsion does not need to know *who* is speaking, and that is the
    whole point of the doctrine. `Voices` and `Act` quantify over all
    subjects, so whoever performs the thesis is refuted by performing it — the
    contradiction is speaker-independent, and no axiom has to identify a
    natural-language speaker with a `Subject` in order to run it. An earlier
    note here framed the missing speaker-identification as a standing limit
    awaiting a 27th axiom; that framing was wrong, and it is withdrawn.
    `Subject` is a nullary uninterpreted sort, so Γ also cannot name *which*
    subject the model inhabits, but nothing in the retorsion needs it to.
    Footprint: `{}`. -/
theorem the_thesis_is_utterable_though_not_assertable :
    ∃ (S : NegativeRetorsionSignature), (∃ _s : S.Subject, True) ∧
      S.NoI ∧ (∃ s : S.Subject, S.act s S.NoI) ∧
      (∀ s : S.Subject, ¬ S.Asserts s S.NoI) := by
  let S1 : NegativeRetorsionSignature := {
    Subject    := Unit
    Means      := fun _ _ => False
    State      := Unit
    Initiates  := fun _ _ _ _ => False
    act        := fun _ _ => True
    DomainItem := Unit
    ofProp     := fun _ => ()
    DependsOn  := fun _ _ => False
    EO         := True
  }
  refine ⟨S1, ⟨(), trivial⟩, ?_, ⟨(), trivial⟩, ?_⟩
  · rintro ⟨_, _p, hMeans⟩
    exact hMeans
  · intro _s hAss
    exact hAss.1.1

-- ============================================================================
-- Section 4: the refutation — the no-meaning world is not possible in Γ
-- ============================================================================

/-- **The thesis is false in Γ: no-meaning worlds are not possible here.**
    `Meaning_I p` is definitionally `∃ s, Means s p` (`Choice.lean:131`), so a
    subject who means something is already a counterexample to `NoMeaning`, and
    `Logos.Plurality.cogito_from_T12` exhibits one with no hypothesis. Three
    lines, never written down until now.

    This is the "MUST be possible", priced honestly. It is **not** axiom-free —
    nothing in the bare meaning vocabulary refutes the thesis, and C382 above
    *is* the machine-checked proof of that impossibility. What C382 exhibits is
    a free `NegativeRetorsionSignature` satisfying its own `NoI`, a different
    proposition about a different sort; it is consistent *as a signature* and it
    stays that way, COUNTERMODEL status and B4 gate untouched. What this row
    shows is that the thesis does not survive *the theory*: given the plurality
    bridge, Γ refutes it outright.

    Companion, not replacement, to everything in Sections 1–3d. The ladder, the
    retorsion, the complement and the utterance model all stand exactly as
    stated; this row is what they were missing — the content's falsity, on the
    record, at the price the record already pays elsewhere.
    Footprint: `{AxTwoSubjects, Means, Subject, Will, subjectWill}`. -/
theorem noMeaning_is_refuted_from_plurality : ¬ NoMeaning := by
  obtain ⟨s, p, hmp⟩ := Logos.Plurality.cogito_from_T12
  exact fun h => h ⟨p, ⟨s, hmp⟩⟩

/-- **The same refutation on the act-datum: no META bridge required.**
    `Logos.Agency.act_datum_implies_means` turns `∃ s, ∃ p, Act s p` straight
    into a meaning witness, because `Act` already contains `Means` — so whoever
    grants that an act occurred grants the thesis's falsity with it. The
    God-lane twin of C401: C401 is unconditional on the plurality bridge, this
    row is conditional on the performative datum and free of every bridge,
    price relocated to ◈ `performativeActDatum` (`Tag: TRANS`) — free in axioms,
    not free in performance.

    The hypothesis is anonymous (`∃ s, ∃ p, Act s p`, not a named `def`), so the
    ◈ registry listing is the *only* signal of the dependence — the same
    arrangement as C386/C387, and the same limitation: invisible to
    `#print axioms` by construction.
    Footprint: `{Initiates, Means, State, Subject}`. -/
theorem noMeaning_is_refuted_from_the_act_datum
    (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Act s p) : ¬ NoMeaning := by
  obtain ⟨s, p, hm⟩ := Logos.Agency.act_datum_implies_means h
  exact fun hN => hN ⟨p, ⟨s, hm⟩⟩

end Logos.MeaningRetorsion
