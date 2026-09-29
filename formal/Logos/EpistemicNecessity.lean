/-
# Logos.EpistemicNecessity — the necessity direction, made unmissable

> **Nothing can be epistemologically right or wrong without a non-mechanical
> (Free) being for which meaning can mean.**

This module states that sentence as three theorems, so that no reader has to
assemble it from the ledger by hand. It is **not a new claim and not a new proof**:
C140 (`claims_normative_correctness_derives_free_will`, `NormativeOrder.lean:190`)
already derives `FreeWill s` from the epistemic stance at **zero substantive axioms**,
and `freeWill_implies_person` (`Person.lean:135`) closes the personhood half for the
price of the declared VOCAB law `will_individuation`. What was missing was a badged
row carrying the sentence, and that is what this module supplies.

## Why this is a visibility batch and not a proof batch

The generated README already carried the sentence in three places before this module
existed — pillar 2 of the Dialectical Inevitability Architecture (`README.md:20`), the
Route A antecedent (`:35`), the price (`:38-41`), and the *Personal — the epistemic
sibling* attribute row (`:1879`). What it did **not** carry was C140 itself: the
theorem appeared only inside tactic-script narration (`:753`, `:820`, `:838`) and never
as a badged chain row, so a reader could not tell that the *necessity* arrow is
machine-decided, only the *grounding* arrow. The README's "Two directions, not one"
note (`:23-29`) says that "the direction is not machine-decidable"; that is correct
about the **interpretive** reading of the conjunction (C527's downward ontological
arrow) and is not a claim about the two implications, each of which is a separate
theorem. C554 below is the machine-checked answer to that confusion.

## The three rows

| Row | Declaration | What it settles |
|---|---|---|
| C553 | `epistemic_right_wrong_requires_a_free_being_for_which_meaning_can_mean` | the author's sentence, conjuncts co-present in one statement |
| C554 | `the_epistemic_dependence_runs_both_ways` | both arrows are theorems, each with its own footprint |
| C555 | `epistemic_normativity_somewhere_yields_a_free_being` | the existential form, so the FACT is not merely pointwise |

## Honesty constraints — binding, and not negotiable

1. **The antecedents stay.** C553 and C555 both keep their hypotheses explicit and
   are never silently discharged. Nothing in Γ shows the epistemic stance obtains
   unconditionally, and this batch does not attempt it: `refuting the denial requires
   an inhabitant of `Act`` (`Agency.lean:210-213`) is a fact about `Act`-based routes
   only, not a theorem about the necessity direction, which is axiom-free.
2. **Neither row's gloss may say "unconditionally."** A conditional theorem is not an
   unconditional claim, and the register of this batch is 35 both before and after.
3. **The model-level side of the same principle is not here.** The claim that right
   and wrong *cannot exist at all* without such a being is a constraint on worlds, and
   it is installed in the audit signatures, not in Γ: `objectivity_grounded`
   (`NegativeRetorsionAudit.lean:65-97`) and `order_needs_a_meaning_being`
   (`EpistemicPersonalGround.lean`). Derivation and inhabitation are different
   questions; this module settles the first, the signatures settle the second.
-/

import Logos.Core
import Logos.Agency
import Logos.Order
import Logos.Choice
import Logos.Person
import Logos.NormativeOrder
import Logos.PersonalNormativeGround
import Logos.EpistemicPersonalGround

namespace Logos.EpistemicNecessity

open Logos.Agency (Subject Means Will subjectWill will_individuation Act
  NoSubject Asserts)
open Logos.Order (Correct Incorrect rightWrong_implies_meaning)
open Logos.Choice (FreeWill FreeSubject freeSubject_iff_freeWill
  Meaning_I meaning_I_needs_subject)
open Logos.Person (Person freeWill_implies_person)
open Logos.NormativeOrder (ClaimsNormativeCorrectness
  claims_normative_correctness_is_act
  claims_normative_correctness_derives_free_will)
open Logos.PersonalNormativeGround (GroundsRightWrongAt)
open Logos.EpistemicPersonalGround (the_person_grounds_the_epistemic_right_wrong)

/-!
## C553 — the FACT, in one statement

The author's sentence, with every conjunct present at once. A reader who has only
this row does not need C140, C222 or `freeSubject_iff_freeWill` to hand.

The will-individuation conjunct `(∃ w, w = subjectWill s)` is exposed deliberately:
it is the *only* place the price of personhood is visible, and it is declared
vocabulary (`Will`, `subjectWill`) plus one VOCAB law (`will_individuation`), never an
unfolding.
-/

/-- **THE FACT.** Nothing can be epistemologically right or wrong without a
    non-mechanical (Free) being for which meaning can mean.

    Every conjunct of that sentence in a single machine-checked statement: the
    epistemic poles are *meant* (so meaning can mean), co-grasping them is
    *free choice* between them (so the being is non-mechanical), the will is
    individuated (so the being is a person), and both the right pole and the wrong
    pole are among the contents meant — right/wrong is not one-sided.

    The last two conjuncts are projected out of `h` and are therefore *the same act
    read at two levels*, not an additional bridge: `Correct s p` and `Incorrect s p`
    are the epistemic poles, and `Means s` of both is the constitutive clause.

    Restatement of C140 plus `freeWill_implies_person`; adds no content the ledger
    lacks. The antecedent is kept explicit and is never discharged.
    Classification: DEFINITIONAL.
    Footprint: `{Initiates, Means, State, Subject, Will, subjectWill,
    will_individuation, CL}` (zero substantive axioms). -/
theorem epistemic_right_wrong_requires_a_free_being_for_which_meaning_can_mean
    (s : Subject) (p : Prop) (h : ClaimsNormativeCorrectness s p) :
    (∃ w : Will, w = subjectWill s) ∧ FreeWill s ∧ FreeSubject s ∧
      Person s ∧ Means s (Correct s p) ∧ Means s (Incorrect s p) := by
  have hFW : FreeWill s := (claims_normative_correctness_derives_free_will s p h).2
  refine ⟨⟨subjectWill s, rfl⟩, hFW, hFW, freeWill_implies_person s hFW, h.2.1, h.2.2⟩

/-!
## C554 — both arrows, and both of them theorems

The README's "the direction is not machine-decidable" note is about the
*interpretive* reading of a conjunction, not about the two implications. This row
makes the two implications explicit, and each with its own provenance: the
necessity arrow from C140, the grounding arrow from C527.

It does **not** assert the interpretive reading as ontology. It asserts only that both
implications are machine-checked, which is precisely what a reader is being invited
to disbelieve.
-/

/-- **The epistemic dependence runs both ways, and both ways are theorems.**
    *Necessity*: if the epistemic stance obtains — the subject means both the
    `Correct` and the `Incorrect` pole — then it is a free, personal being.
    *Grounding*: that same being is the one that grounds the two poles.
    The two are separate implications with separate footprints (C140 and C527), not
    one undirected claim.
    Classification: DEFINITIONAL.
    Footprint: `{Initiates, Means, State, Subject, Will, subjectWill,
    will_individuation, CL}` (zero substantive axioms). -/
theorem the_epistemic_dependence_runs_both_ways
    (s : Subject) (p : Prop) (h : ClaimsNormativeCorrectness s p) :
    FreeWill s ∧ GroundsRightWrongAt s (Correct s p) (Incorrect s p) ∧ Person s := by
  have hFW : FreeWill s := (claims_normative_correctness_derives_free_will s p h).2
  exact ⟨hFW, (the_person_grounds_the_epistemic_right_wrong s p h).1,
    freeWill_implies_person s hFW⟩

/-!
## C555 — the existential form

Pointwise (C553) is not existential. This row moves the quantifier out, so the FACT
is not merely a claim about a subject supplied as input. The price is unchanged: the
stance must be *claimed* by someone, and that claim is the antecedent.

**Binding honesty constraint (see the module docstring, item 1).** The antecedent
stays. Nothing here shows the epistemic stance obtains; this row says that *if*
somebody holds both poles, a free personal being exists. The word "unconditionally"
does not appear in its gloss, because it would be false.
-/

/-- **Existential form of the FACT.** If the epistemic stance obtains *somewhere* —
    some subject claims normative correctness of some content — then a non-mechanical
    personal being exists. This lifts the FACT out of the pointwise form, where `s`
    was supplied as input, without discharging the antecedent.
    Classification: DEFINITIONAL.
    Footprint: `{Initiates, Means, State, Subject, Will, subjectWill,
    will_individuation, CL}` (zero substantive axioms). -/
theorem epistemic_normativity_somewhere_yields_a_free_being
    (h : ∃ s : Subject, ∃ p : Prop, ClaimsNormativeCorrectness s p) :
    ∃ s : Subject, FreeWill s ∧ FreeSubject s ∧ Person s ∧
      (∃ p : Prop, Means s (Correct s p) ∧ Means s (Incorrect s p)) := by
  obtain ⟨s, p, hClaims⟩ := h
  have hFW : FreeWill s := (claims_normative_correctness_derives_free_will s p hClaims).2
  exact ⟨s, hFW, hFW, freeWill_implies_person s hFW, ⟨p, hClaims.2⟩⟩

/-- The same statement with the will-individuation conjunct restored, so the
    existential form carries the *whole* price of the FACT and not only its free
    part. Registered as a corollary of C555, not as a ledger row: it is the same
    content at `{}` and would otherwise double-count the batch.
    Footprint: `{Initiates, Means, State, Subject, Will, subjectWill,
    will_individuation, CL}`. -/
theorem epistemic_normativity_somewhere_yields_an_individuated_free_being
    (h : ∃ s : Subject, ∃ p : Prop, ClaimsNormativeCorrectness s p) :
    ∃ s : Subject, (∃ w : Will, w = subjectWill s) ∧ FreeWill s ∧ Person s := by
  obtain ⟨s, p, hClaims⟩ := h
  have hFW : FreeWill s := (claims_normative_correctness_derives_free_will s p hClaims).2
  exact ⟨s, ⟨subjectWill s, rfl⟩, hFW, freeWill_implies_person s hFW⟩

/-!
## C557 — the act datum is NECESSARY, not stipulated

The author's reasoning, formalised: the epistemic order cannot obtain without meaning
(C556 and the `NegativeRetorsionSignature` repair); meaning cannot obtain without a
Free person; a Free person needs an act; **therefore the act datum is necessary.**

The last step is available at `{}` and nobody had written it down. The reason is
that `ClaimsNormativeCorrectness` *contains* the act:

```lean
def ClaimsNormativeCorrectness (s : Subject) (p : Prop) : Prop :=
  Act s p ∧ Means s (Correct s p) ∧ Means s (Incorrect s p)
```

so the act is the stance's own first conjunct (`claims_normative_correctness_is_act`,
`NormativeOrder.lean:172`), not a separate premise. Reading `performative_act_datum`
as the price of this direction was wrong: it is `Tag: TRANS`, but the order route
never invokes it.

**What this does and does not discharge.** It discharges the TRANS datum from the
*necessity* direction only. The **unconditional** `∃ s, ∃ p, Act s p` still rests on
`performative_act_datum` (C454), and `F1bUncond` — unconditional
`∃ s, FreeWill s` from Γ's primitives — remains `BLOCKED` on
`rejectedHornCoMeant : ∃ s p, A s p ∧ A s (¬p)`. Those are different claims, and this
row does not close them. It says the act datum is *entailed by the order*, which is
what the argument actually needs.

**No new axiom, and the whole chain stays `{}`.** With C557 the necessity reading is
axiom-free end to end: order → act (`C557`) → choice between the poles (`C140`,
whose `Incompatible (Correct s p) (Incorrect s p)` is derived at
`NormativeOrder.lean:136`, not assumed) → `FreeWill` → `Person` (`C553`). The
substantive price of this direction is nil; the only named law is the VOCAB
`will_individuation`.
-/

/-- **The act datum is necessary.** If the epistemic order obtains — someone holds
    the stance that makes right and wrong meaningful — then someone acts, at
    `{}`.

    This is the author's argument step 3, isolated and machine-checked: the order
    needs meaning, meaning needs a Free person, a Free person needs an act, so the
    act datum is entailed rather than stipulated. It is immediate because the
    stance's first conjunct *is* an act.

    Consequence for the ledger: `performative_act_datum` (C454, `Tag: TRANS`) is
    **not** the price of the necessity direction. The price of *unconditional*
    existence of the datum remains, and `F1bUncond` remains `BLOCKED` — see the
    module docstring.
    Classification: DEFINITIONAL.
    Footprint: `{Initiates, Means, State, Subject}` (zero substantive axioms; not even `CL`). -/
theorem epistemic_order_makes_the_act_datum_necessary
    (h : ∃ s : Subject, ∃ p : Prop, ClaimsNormativeCorrectness s p) :
    ∃ s : Subject, ∃ p : Prop, Act s p := by
  obtain ⟨s, p, hClaims⟩ := h
  exact ⟨s, p, claims_normative_correctness_is_act s p hClaims⟩

/-- The same, in pointwise form, for a subject already in the stance — the form a
    reader of C553/C556 will want, since those are stated for a given `s`.
    Classification: DEFINITIONAL.
    Footprint: `{Initiates, Means, State, Subject}`. -/
theorem the_epistemic_stance_is_an_act
    (s : Subject) (p : Prop) (h : ClaimsNormativeCorrectness s p) :
    Act s p ∧ Means s (Correct s p) ∧ Means s (Incorrect s p) :=
  h

/-!
## C558 — the denial voiced as judgment requires a Free Subject

The author's point, formalised: voicing "no subjects exist" *as a judgment* — in
the normative stance, presenting-as-correct — requires a Free Subject, and the
thesis dies in its own performance.

Two tiers, in order, and the order matters (§13.3). Tier 1 (subjecthood) is conceded
by *any* denier, deterministic or free: `Asserts speaker NoSubject → False` (C57,
`noSubject_performative_selfRefutes`) fires for any speaker, because to deny,
something must assert, and what asserts is a subject. Even a deterministic
deliberator that emitted the denial would be a subject for C57's purposes —
determinism is no refuge from subjecthood, because subjecthood is prior to freedom.
Tier 2 (the really-Free kind, Tier9: could-have-settled-otherwise + sourcehood) is
the author's requirement on what counts as *genuine judgment*; this row derives
Tier6 `FreeWill` at `{}`-substance via C140, and the prose records Tier9 with its
independence from Γ's base on the record (see the module docstring of §13.2).
`M_Deliberator` is why Tier6 alone does not settle the author's claim: it co-means
incompatibles while settling only what it is fixed to settle.
-/

/-- **The denial voiced as judgment requires a Free Subject.** Holding the
    normative stance on `NoSubject` — presenting "no subjects exist" as correct —
    yields a Free, personal subject who acts: `FreeWill` by C140 (the stance derives
    choice between the poles at `{}`-substance), `Person` by
    `freeWill_implies_person`, `Act` by `claims_normative_correctness_is_act`.
    And the thesis dies in its own performance: with the full `Asserts speaker
    NoSubject`, C57 (`noSubject_performative_selfRefutes`) gives `False`.
    Tier 1 (subject) is conceded by any denier whatever, deterministic or free;
    Tier 2 (really Free, Tier9) is the author's requirement on genuine judgment,
    recorded with its independence from Γ's base.
    Classification: DEFINITIONAL.
    Footprint: `{Initiates, Means, State, Subject, Will, subjectWill,
    will_individuation, CL}` (zero substantive axioms). -/
theorem empty_world_denial_voiced_as_judgment_requires_a_free_subject
    (speaker : Subject) (h : ClaimsNormativeCorrectness speaker NoSubject) :
    FreeWill speaker ∧ Person speaker ∧ Act speaker NoSubject := by
  have hFW : FreeWill speaker :=
    (claims_normative_correctness_derives_free_will speaker NoSubject h).2
  exact ⟨hFW, freeWill_implies_person speaker hFW,
    claims_normative_correctness_is_act speaker NoSubject h⟩

/-!
## C560 — the third leg: no meaning, no right/wrong

The contrapositive of C49 (`meaning_I_needs_subject`), and the premise the author's
three-premise chain was missing as a named row: right/wrong needs meaning (C62),
meaning needs a subject (C49) — therefore without meaning, nothing is correct and
nothing is incorrect. `Meaning_I p` *is* `∃ s, Means s p` definitionally
(`Choice.lean:131`), so this is one line at `{}`.
-/

/-- **No meaning, no right/wrong.** If nothing means `p`, then `p` is not among the
    contents anyone means — `¬ Meaning_I p` — so `p` is neither correctly nor
    incorrectly judgable. The third leg of the author's chain, `{}`.
    Classification: DEFINITIONAL.
    Footprint: `{Means, Subject}`. -/
theorem no_meaning_no_correctness
    {p : Prop} (hNoM : ¬ ∃ s : Subject, Means s p) : ¬ Meaning_I p :=
  fun hMI => hNoM hMI

/-!
## C561 — the chain, composed: no subject who means, no epistemic right/wrong

All three premises and the conclusion in one statement (C62 + C49 + C560): if no
subject means anything at all, then correctness obtains nowhere and incorrectness
obtains nowhere. This is the author's argument — "without meaning, nothing is
correct and nothing is incorrect" — with the subject made explicit, since C62
delivers `Meaning_I` and C49 delivers the subject. Full composition, vocabulary
only: a `{}` version of this row would be a weaker claim wearing its name.
-/

/-- **No subject who means, no epistemic right/wrong.** If `¬ ∃ s, ∃ p, Means s p`,
    then `¬ ∃ s, ∃ p, Correct s p` and `¬ ∃ s, ∃ p, Incorrect s p`. From `Correct s p`
    (resp. `Incorrect s p`) C62 yields `∃ q, Meaning_I q`, C49 yields a subject who
    means it, contradicting the hypothesis.
    Classification: DEFINITIONAL.
    Footprint: `{Initiates, Means, State, Subject}` (zero substantive axioms). -/
theorem no_subject_who_means_no_epistemic_right_wrong
    (hNoSubj : ¬ ∃ s : Subject, ∃ p : Prop, Means s p) :
    ¬ (∃ s : Subject, ∃ p : Prop, Correct s p) ∧
    ¬ (∃ s : Subject, ∃ p : Prop, Incorrect s p) := by
  constructor
  · intro hC
    obtain ⟨s, p, hCp⟩ := hC
    obtain ⟨q, hMq⟩ := rightWrong_implies_meaning (Or.inl ⟨s, p, hCp⟩)
    obtain ⟨s', hMs'⟩ := meaning_I_needs_subject hMq
    exact hNoSubj ⟨s', q, hMs'⟩
  · intro hI
    obtain ⟨s, p, hIp⟩ := hI
    obtain ⟨q, hMq⟩ := rightWrong_implies_meaning (Or.inr ⟨s, p, hIp⟩)
    obtain ⟨s', hMs'⟩ := meaning_I_needs_subject hMq
    exact hNoSubj ⟨s', q, hMs'⟩

/-!
## C559 — a signature model is not a candidate state

A `def` following the C552 precedent (presentation data, `—` row, no claim): the
discipline that a `{}` countermodel witnesses a constraint's underivability from a
signature and is never evidence about a state of affairs. This is the row that would
have caught the plan's own error — granting worldhood to M0 — before the author did.
-/

/-- C559 — presentation data, not a claim (`—` row, following the C552 precedent).
    A free-signature countermodel is a witness about a *signature*: it shows a
    constraint is underivable from stated fields. It is never evidence about a
    *state of affairs*, because a signature has no field for being a world — Γ's core
    vocabulary (`Subject`, `Prop`, `State`, `Means`, `Initiates`) contains no `World`
    sort. Reading an inhabitant of a record as a possible world is a category error;
    M0 (`Subject := Empty`) satisfies `NoI` and says nothing about any state. -/
def signature_model_reading_discipline : String :=
  "A free-signature countermodel witnesses underivability from a signature, never a state of affairs."

/-!
## C562 — being true is being true *to*: the alethic chain

The author's correction, formalised: being-true requires a subject to be true *to*.
Bare `T p` (`T p := p`, `Core.lean`) is *being-the-case* — satisfaction, subject-free.
*Being-true* is disclosure to a subject, and it has a kernel home:

```lean
def TrueTo (s : Subject) (p : Prop) : Prop := Means s p ∧ Logos.Core.T p
```

Three layers, each with its requirement, and the layers must not be collapsed:

| Layer | Notion | Requires | Row |
|---|---|---|---|
| being-the-case | `T p` (satisfaction) | nothing | `Core` |
| being-true (disclosure) | `TrueTo s p` (meaning + truth) | a subject who means | C49/C560 |
| judging rightly | `Correct s p` (act + truth) | a Free Subject who chooses | C140/C553 |

The chain `Correct → TrueTo → T` is one weakening after another (dropping
`Initiates`, then dropping `Means`), all `{}`-class. Its content is the hierarchy
itself: truth lives at the middle layer and above, never at the bottom alone. No
row of the ledger may call bare-`T` satisfaction "true" in a normative context —
that vocabulary now belongs to `TrueTo`/`Correct`. (Consequence on record: rows
that read `NecessarilyTrue`/satisfaction as normative truth, e.g. P2/C59's prose,
are satisfaction rows; the correction is flagged here, not silently rewritten —
see the C562 GAPMAP gloss.)
-/

/-- Truth-to-a-subject: `p` is true *to* `s` — meant by `s`, and the case.
    Being-the-case (`T p`) is free; being-true is disclosure, and disclosure is
    always to someone. Classification: DEFINITIONAL. -/
def TrueTo (s : Subject) (p : Prop) : Prop := Means s p ∧ Logos.Core.T p

/-- **The alethic chain: judging rightly is being-true, being-true is being-the-case.**
    `Correct s p → TrueTo s p` (drop the `Initiates` horn of the act) and
    `TrueTo s p → T p` (drop the meaning). So correctness entails truth-to, and
    truth-to entails truth — while the converses fail: `T p` with no subject is
    satisfaction, not truth, and `TrueTo` with no act is disclosure, not judgment.
    This is the author's "being true requires a subject to be true *to*" as a
    machine-checked hierarchy rather than a slogan.
    Classification: DEFINITIONAL.
    Footprint: `{Initiates, Means, State, Subject}` (zero substantive axioms). -/
theorem being_true_is_being_true_to (s : Subject) (p : Prop) :
    (Correct s p → TrueTo s p) ∧ (TrueTo s p → Logos.Core.T p) :=
  ⟨fun h => ⟨h.1.1, h.2⟩, fun h => h.2⟩

end Logos.EpistemicNecessity

/-!
# Axiom footprint audit
  C553 `{Initiates, Means, State, Subject, Will, subjectWill, will_individuation, CL}`
  C554 `{Initiates, Means, State, Subject, Will, subjectWill, will_individuation, CL}`
  C555 `{Initiates, Means, State, Subject, Will, subjectWill, will_individuation, CL}`
  C556 `{}` (`EpistemicPersonalGround.epistemic_order_requires_a_free_meaning_being`)
  C557 `{Initiates, Means, State, Subject}` (`epistemic_order_makes_the_act_datum_necessary`; the act datum is entailed
       by the order, not stipulated — see §0 for the argument and its limits)
  All four are zero substantive axioms; the register is 35 before and after this batch.
-/
#print axioms Logos.EpistemicNecessity.epistemic_right_wrong_requires_a_free_being_for_which_meaning_can_mean
#print axioms Logos.EpistemicNecessity.the_epistemic_dependence_runs_both_ways
#print axioms Logos.EpistemicNecessity.epistemic_normativity_somewhere_yields_a_free_being
#print axioms Logos.EpistemicNecessity.epistemic_normativity_somewhere_yields_an_individuated_free_being
#print axioms Logos.EpistemicNecessity.epistemic_order_makes_the_act_datum_necessary
#print axioms Logos.EpistemicNecessity.the_epistemic_stance_is_an_act
#print axioms Logos.EpistemicNecessity.empty_world_denial_voiced_as_judgment_requires_a_free_subject
#print axioms Logos.EpistemicNecessity.no_meaning_no_correctness
#print axioms Logos.EpistemicNecessity.no_subject_who_means_no_epistemic_right_wrong
#print axioms Logos.EpistemicNecessity.being_true_is_being_true_to
#print axioms Logos.EpistemicPersonalGround.epistemic_order_requires_a_free_meaning_being
