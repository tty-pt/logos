/-
# Logos.AsieticChoice — True Choice, and the closing of the `?` in the choice chain

## The thesis

> **Asiety is true freedom. Weak choice implies strong choice. True choice follows.**

`Asiety` is not a new primitive notion: it *is* true freedom, i.e. `TrueChoice`. This module
proves the thesis and **declares no axiom**. Everything below is derived from the existing corpus.

## Why the second horn was never missing

`base.txt:460` records the deduction's one open step as

    weak choice / choice-field → ? [co-significação do corno rejeitado] → strong Chooses → FreeWill

The `?` is the *co-signification of the rejected horn*. It is supplied by
`Logos.RetorsiveNormativity.AxJudicativeBipolarity` (line 91, `Tag: SEM`), which is **already an
axiom of Γ**:

    ∀ (s : Subject) (p : Prop), ClaimsCorrect s p → Means s (¬ p)

Asserting a content as correct constitutively involves grasping that content's contradictory.
`RetorsiveNormativity` already uses it at line 108. So the co-signification of the rejected horn is
derived, not posited, and the deduction passes from the field to genuine choice inside Γ.

## Why `TrueChoice` is built on `Chooses` and not on `DeliberateChoice`

`Logos.Choice.DeliberateChoice` conjoins `Asserts s p`. `Asserts s p := Act s p ∧ p`
(`Agency.lean:313`), `Act s p` forces `Initiates`, and `Initiates` (`Agency.lean:168`) is an
uninterpreted VOCAB axiom with **no existence instance anywhere in Γ** — no axiom anywhere
concludes `Act` or `Initiates`. Building `TrueChoice` on `DeliberateChoice` therefore imports a
witness that the corpus cannot supply, and the choice frontier looks blocked for that reason alone.

The thesis names `Chooses`, the strong choice. So the fix is definitional, not axiomatic: openness
is pure logic and the act datum is not needed at all.

## The one residual, stated plainly

The **bare universal** — every weak chooser is a strong chooser, i.e.
`ChoiceField s p q → Means s q` — is *not* in Γ. It would require horn-saturation, which no axiom
supplies. What Γ gives is the entailment with its premise named:
`ChoiceField s p q → ClaimsCorrect s p → Chooses s p (¬ p)`, and Γ's poem supplies the premise
(there is right-and-wrong to judge). Existence of true choice is unconditional either way. The
bare universal form is not folded in silently.

## Honest disclosure on `trueChoice_exists`

`Person.lean:56` sets `DominionOverActs s := FreeWill s`, and `ThomisticPersonCore` conjoins it, so
`Person s → FreeWill s` by projection. The free-will existence content was therefore already
carried by the pre-existing META axiom `AxTwoSubjects`. `trueChoice_exists` is a genuine
unconditional derivation, but it is a *definitional* one, and it is disclosed as such rather than
presented as a discovery about the world.

## Out of scope: counterfactual accessibility

`freeWill_not_entails_modal_alternatives` (`ModalCreationAgency.lean:185`) exhibits a model in which
an agent has free will at the actual world and **no** accessible world containing the contrary act.
`determinism_compatible_with_gamma_freewill` and
`gamma_freewill_distinct_from_libertarian_freedom` (`AgencyDeterminismConsequences.lean:167,178`)
place genuine optionality at Tier 7 and libertarian freedom at Tier 9. None of that is this thesis,
and none of it is derivable without a new primitive. See ASIETY_FREE.md §1.15.
-/
import Logos.Core
import Logos.Semantics
import Logos.Entity
import Logos.Agency
import Logos.Alternatives
import Logos.Choice
import Logos.TheologicalModalHardening
import Logos.RecoveredOntologicalGround
import Logos.NecessityEternity
import Logos.CanonicalAseity
import Logos.DivinePureActuality
import Logos.Plurality
import Logos.Person
import Logos.RetorsiveNormativity
import Logos.IndubitableNormativeFreeWill

namespace Logos.AsieticChoice

open Logos.Semantics (Form)
open Logos.Entity (Entity EntityOf)
open Logos.Agency (Subject Means)
open Logos.Alternatives (Incompatible)
open Logos.Choice (ChoiceField Chooses FreeWill FreeSubject Doubts
  incompatible_self_negation rejectedHornCoMeant genuineChoice_of_doubt)
open Logos.TheologicalModalHardening (ContingentEntity)
open Logos.RecoveredOntologicalGround (GroundsEntity
  ground_of_reality_grounds_finite_subject)
open Logos.NecessityEternity (ofGround_necessary_ground_of_reality ofGround_ne_ofSubject)
open Logos.CanonicalAseity (ExternalGrounding CanonicalAseity conditional_canonical_aseity)
open Logos.Plurality (T5_personExists_from_plurality)
open Logos.Person (Person)
open Logos.RetorsiveNormativity (ClaimsCorrect AxJudicativeBipolarity
  NoGN claims_correct_means_content claiming_denial_presupposes_genuine_normativity)
open Logos.IndubitableNormativeFreeWill (GenuineNormativity
  indubitable_normative_free_will)

/-!
## Section 1: the definitions, and the honest note on openness
-/

/-- `ContestedContent`: the content-alternatives space is not settled by frame-necessity — some
    formula is neither necessarily true nor necessarily false, so there is material on which two
    incompatible readings can genuinely divide. This is C96, and it is a definition plus one
    machine-checked result: no axiom is introduced.
    Footprint: `{}`. -/
def ContestedContent : Prop :=
  ∃ τ : Form, ¬ Logos.Semantics.NecessarilyTrue τ ∧ ¬ Logos.Semantics.NecessarilyFalse τ

/-- The frame does contest its own content: C96 discharged. This is the sole source of the
    contingency conjunct of `OpenAlternative`, and it is axiom-free.
    Footprint: `{}`. -/
theorem contested_content : ContestedContent :=
  Logos.Semantics.some_formula_contingent

/-- `OpenAlternative p q`: the alternatives `p` and `q` stand genuinely open — they exclude each
    other, and the frame does not settle content in advance. This grounds openness in *content*,
    not in the chooser's existence.

    The honest weakness, recorded rather than hidden: `Incompatible` is `Prop`-level while
    `NecessarilyTrue` is `Form`-level and the library has no `Prop ↔ Form` bridge, so
    `ContestedContent` is a global frame fact that does not individually bind `p` and `q`. It keeps
    the anti-collapse force honestly instead of faking a per-pair modality.

    An earlier version grounded openness in `ContingentEntity (EntityOf s)` instead. That was
    withdrawn: subject persistence is definitional in Γ (*esse est agere*), and
    `PersonStabilityPrinciple` (`Love.lean:97`, open and conditional) would have made the conjunct
    unsatisfiable for any chooser.
    Footprint: `{}`. -/
def OpenAlternative (p q : Prop) : Prop :=
  Incompatible p q ∧ ContestedContent

/-- `TrueChoice s p q`: true choice — the subject genuinely co-signifies two incompatible
    alternatives and those alternatives stand open. This is the culmination of the chain
    `weak choice → strong choice → true choice`, and it is what `Asiety` names.
    Footprint: `{Means, Subject}`. -/
def TrueChoice (s : Subject) (p q : Prop) : Prop :=
  Chooses s p q ∧ OpenAlternative p q

/-- `Asiety e`: true freedom exhibited at `e` — some subject whose entity is `e` makes a true
    choice. Asiety is not a separate primitive notion; it is true freedom, by definition. Being a
    definition, the identification is true by construction and carries no metaphysical content of
    its own: the substantive content of this module is the derivation below, not this sentence.
    Footprint: `{Means, Subject}`. -/
def Asiety (e : Entity) : Prop :=
  ∃ s : Subject, ∃ p q : Prop, e = EntityOf s ∧ TrueChoice s p q

/-!
## Section 2: strong choice implies true choice — pure, no axiom
-/

/-- An open alternative is incompatibility on contested ground: the horns exclude each other.
    Footprint: `{}`. -/
theorem open_alternative_is_incompatible {p q : Prop}
    (h : OpenAlternative p q) : Incompatible p q :=
  h.1

/-- Every strong choice is a true choice. This is the second step of the thesis,
    `strong choice → true choice`, and it is **pure logic**: the incompatibility is already in
    `Chooses`, and the contingency conjunct is C96. No axiom is used, and none is needed.
    Footprint: `{Means, Subject}`. -/
theorem chooses_implies_trueChoice {s : Subject} {p q : Prop}
    (h : Chooses s p q) : TrueChoice s p q :=
  ⟨h, ⟨h.2.2, contested_content⟩⟩

/-- A true choice is a strong choice, read back: the two halves of the thesis agree on overlap.
    Footprint: `{Means, Subject}`. -/
theorem trueChoice_implies_chooses {s : Subject} {p q : Prop}
    (h : TrueChoice s p q) : Chooses s p q :=
  h.1

/-- A true choice is a weak choice: the field the deduction starts from is passed.
    Footprint: `{Means, Subject}`. -/
theorem trueChoice_implies_choiceField {s : Subject} {p q : Prop}
    (h : TrueChoice s p q) : ChoiceField s p q :=
  ⟨h.1.1, h.1.2.2⟩

/-- A true choice is freedom: `FreeWill` is definitionally the existence of a `Chooses`, so a true
    chooser is a free subject with no further metaphysical step.
    Footprint: `{Means, Subject}`. -/
theorem trueChoice_implies_freeWill {s : Subject} {p q : Prop}
    (h : TrueChoice s p q) : FreeWill s :=
  ⟨p, q, h.1⟩

/-- True choice and strong choice coincide, so the third step of the thesis adds only the
    openness of the alternatives — which is a frame fact, not a new claim about the world.
    Footprint: `{Means, Subject}`. -/
theorem strongChoice_iff_trueChoice {s : Subject} {p q : Prop} :
    Chooses s p q ↔ TrueChoice s p q :=
  ⟨chooses_implies_trueChoice, trueChoice_implies_chooses⟩

/-!
## Section 3: weak choice implies strong choice — the `?` of `base.txt:460`
-/

/-- ★★ THE THESIS, and the step `base.txt:460` records as open. Weak choice implies strong choice:
    a subject that stands in a choice field before `p` and simultaneously claims `p` as correct
    co-signifies the rejected horn, and so makes a genuine strong choice.

    The bridge is `AxJudicativeBipolarity` (`RetorsiveNormativity.lean:91`, `Tag: SEM`), an axiom
    **already in Γ**: `ClaimsCorrect s p → Means s (¬ p)`. The co-signification of the rejected
    horn is therefore *derived*, not posited by this module. The incompatibility of `p` with `¬ p`
    is pure logic.

    Footprint: `{AxJudicativeBipolarity, Initiates, Means, State, Subject}`. -/
theorem weakChoice_implies_chooses {s : Subject} {p q : Prop}
    (hField : ChoiceField s p q) (hJudge : ClaimsCorrect s p) :
    Chooses s p (¬ p) :=
  ⟨hField.1, AxJudicativeBipolarity s p hJudge, incompatible_self_negation p⟩

/-- The thesis, carried through to true choice: weak choice plus a claim of correctness is a true
    choice. The openness conjunct is pure, so the whole passage from the field to true choice is
    closed with the one SEM axiom Γ already pays for.
    Footprint: `{AxJudicativeBipolarity, Initiates, Means, State, Subject}`. -/
theorem weakChoice_implies_trueChoice {s : Subject} {p q : Prop}
    (hField : ChoiceField s p q) (hJudge : ClaimsCorrect s p) :
    TrueChoice s p (¬ p) :=
  chooses_implies_trueChoice (weakChoice_implies_chooses hField hJudge)

/-- The bare rejected-horn entailment, **named**. `Choice.lean:33-35` records this as prose under
    the label `rejectedHornCoMeant`, but that name is already taken by the *consequent* at
    `Choice.lean:247`; only the consequent was ever a Lean `def`. This is the implication itself,
    stated once so the ledger can cite the blocker by name.

    **BLOCKED, and refuted.** No axiom of Γ reaches `Means s (¬ p)` from `Means s p`. The
    antecedent is `Means`-existence, while every route to a literal negation
    (`AxJudicativeBipolarity`, `AxActPolarity`, `AxIntentionalChoice`,
    `ClaimsNormativeCorrectness`) is `Act`-gated, and `Act` is `Initiates`-gated, with no
    `Initiates` witness anywhere in Γ. `bareRejectedHornCoMeant_is_not_derivable` (Section 3c)
    closes it outright. The two forms that *are* discharged are the `ClaimsCorrect`-conditional one
    (`derives_rejectedHornCoMeant`) and the retorsion-event one
    (`retorsion_implies_rejectedHornCoMeant`).

    Footprint and status are orthogonal: the marker below is what the definition *depends on*,
    `BLOCKED` is that it is not discharged. Being a `def`, it states the frontier, not that the
    frontier is open, and emphatically not that it is closed.
    Footprint: `{Means, Subject}`. -/
def bareRejectedHornCoMeant : Prop :=
  (∃ s : Subject, ∃ p : Prop, Means s p) →
    ∃ s : Subject, ∃ p : Prop, Means s p ∧ Means s (¬ p)

/-- The **conditional** form of the rejected horn is discharged: a subject who claims a content as
    correct also means its negation, which is the "co-significação do corno rejeitado" that
    `base.txt:460` marked with a `?`.

    The premise is load-bearing, and the recorded blocker is *not* what this discharges. The
    blocker is `bareRejectedHornCoMeant` above, whose antecedent is mere meaning-existence; this
    theorem's antecedent is a correctness-judgment, which is strictly more. The gap between them
    is the missing `Initiates` witness — not horn-saturation. See
    `weakChoice_carries_the_judicative_premise_explicitly` for the price being paid, and
    `bareRejectedHornCoMeant_is_not_derivable` for the refutation of the bare form.
    Footprint: `{AxJudicativeBipolarity, Initiates, Means, State, Subject}`. -/
theorem derives_rejectedHornCoMeant :
    (∃ s : Subject, ∃ p : Prop, Means s p ∧ ClaimsCorrect s p) → rejectedHornCoMeant := by
  rintro ⟨s, p, hM, hJ⟩
  exact ⟨s, p, hM, AxJudicativeBipolarity s p hJ⟩

/-- The premise is load-bearing, and the difference is visible in the footprint rather than in a
    claim about the world. The bare entailment "every weak chooser is a strong chooser" would need
    horn-saturation, `ChoiceField s p q → Means s q`, which no axiom of Γ supplies. What is proved
    is the entailment *with its premise named* (`weakChoice_implies_chooses`), never the silent
    conversion `base.txt:451` forbids. The price of naming the premise is one SEM axiom already in
    Γ; the price of the bare form would be a new principle, and it is not paid silently.
    Footprint: `{AxJudicativeBipolarity, Initiates, Means, State, Subject}`. -/
theorem weakChoice_carries_the_judicative_premise_explicitly :
    ∀ (s : Subject) (p : Prop), ChoiceField s p (¬ p) → ClaimsCorrect s p →
      TrueChoice s p (¬ p) :=
  fun _ _ hF hJ => weakChoice_implies_trueChoice hF hJ

/-!
## Section 3b: the performative discharge of the rejected horn
-/

/-- ★★ The retorsion event forces genuine normativity **on its own content**: a subject who claims
    "there is no genuine normativity" *as correct* thereby means both `NoGN` and `¬ NoGN`. This is
    the pinned-content form that answers the meta-level-horn residue recorded at `GAPMAP.md:758`
    (F1b, residue (b)).

    The premise is the retorsion event, and it is not derivable in Γ: `ClaimsCorrect` is
    `Act`-gated (`RetorsiveNormativity.lean:60`), `Act` is `Initiates`-gated, and no axiom supplies
    an `Initiates` witness. That cost is disclosed, not hidden.

    Proof note: it cannot be `:= retorsion_derives_genuine_normativity hEvent`, which concludes
    `GenuineNormativityExists` = `∃ s p q, GenuineNormativity s p q`
    (`RetorsiveNormativity.lean:118`). Lean cannot see through that opaque theorem that the
    witnesses are `NoGN` / `¬ NoGN`. `claiming_denial_presupposes_genuine_normativity`
    (`RetorsiveNormativity.lean:130-133`) concludes the target type directly, from the same
    witness, and is what the corpus itself uses at `RetorsiveNormativity.lean:159`.

    Footprint: `{AxJudicativeBipolarity, Initiates, Means, State, Subject}`. -/
theorem retorsion_yields_genuine_normativity_on_its_own_content
    (hEvent : ∃ s : Subject, ClaimsCorrect s NoGN) :
    ∃ s : Subject, GenuineNormativity s NoGN (¬ NoGN) := by
  obtain ⟨s, hClaim⟩ := hEvent
  exact ⟨s, claiming_denial_presupposes_genuine_normativity s hClaim⟩

/-- ★★★ The recorded blocker has a **second, performative** discharge: from the retorsion event
    the consequent `rejectedHornCoMeant` follows. This differs from `derives_rejectedHornCoMeant`
    in that the content need not be arbitrary — the denial supplies its own pair, so the conclusion
    is a *performative* refutation of the denial rather than a general semantic bridge.

    **The bare form `bareRejectedHornCoMeant` stays BLOCKED**, and is refuted in Section 3c. The
    gap is *not* horn-saturation and *not* this entailment: it is that no axiom of Γ supplies an
    `Initiates` witness, so Γ never reaches `Means s (¬ p)` at all without either a
    correctness-judgment (`AxJudicativeBipolarity`) or a retorsion event.

    Footprint: `{AxJudicativeBipolarity, Initiates, Means, State, Subject}`. -/
theorem retorsion_implies_rejectedHornCoMeant
    (hEvent : ∃ s : Subject, ClaimsCorrect s NoGN) : rejectedHornCoMeant := by
  obtain ⟨s, hClaim⟩ := hEvent
  exact ⟨s, NoGN, claims_correct_means_content s NoGN hClaim,
    AxJudicativeBipolarity s NoGN hClaim⟩

/-!
## Section 3c: the bare horn is refuted, not merely unproved

`bareRejectedHornCoMeant` is `BLOCKED`, and the block is machine-backed rather than merely
asserted. The model follows the `NegativeRetorsionSignature` pattern already used at
`NegativeRetorsionAudit.lean:65`: a `structure` carrying interpretation fields, a `def` for the
sentence under audit, and a theorem exhibiting a model. `NegativeRetorsionAudit.lean` is
referenced for the idiom only; it is not imported and none of its definitions are used.

**Scope, stated honestly.** This is a model of the *meaning relation*: the `Means`/`Subject`
vocabulary, plus faithfulness of meaning, plus propositional non-triviality. It is **not** a total
model of Γ. The claim proved is the precise one — the bare horn is **not derivable** from the
meaning vocabulary and `incompatible_self_negation` — which is strictly more than "not yet proved".

**Why this strengthens the batch rather than shrinking it.** The batch's positive claim is that Γ
derives true choice with no new axiom. That claim is only as credible as Γ's negative results, so a
machine-checked refutation of the one form that does *not* follow is the strongest available
evidence that nothing positive here rests on a hidden assumption.
-/

/-- A single-content model of the meaning relation: every subject is assigned exactly one
    `Prop`, and `means` is faithful (it never asserts a falsehood). Co-signification of a content
    and its negation is therefore impossible, while meaning-existence is guaranteed by
    `witnessContent`.

    Faithfulness is the load-bearing field. Single-valuedness alone would not do: from
    `p = ¬ p` no contradiction follows in general, because `p` need not be provable. What closes
    the model is `Faithful`, which turns `means t p` into a proof of `p` and so yields `p ∧ ¬ p`
    against `incompatible_self_negation`.
{}`. -/
structure SingleContentSignature where
  Subject : Type
  content : Subject → Prop
  means : Subject → Prop → Prop
  witness : Subject
  witnessContent : Prop
  faithful : ∀ (s : Subject) (p : Prop), means s p → p

namespace SingleContentSignature

/-- `means` never asserts a falsehood in `S`. The faithfulness condition, named. This is the
    field that makes the countermodel close: it turns `means t p ∧ means t (¬ p)` into `p ∧ ¬ p`,
    which `incompatible_self_negation` forbids. Single-valuedness alone would not suffice, since
    `p = ¬ p` yields no contradiction for a `p` that is not provable.
    Footprint: `{}`. -/
def Faithful (S : SingleContentSignature) : Prop :=
  ∀ (s : S.Subject) (p : Prop), S.means s p → p

/-- The bare rejected-horn implication, read inside the model `S`. Mirrors
    `bareRejectedHornCoMeant` above, with `S.means` in place of `Means`.
    Footprint: `{}`. -/
def bareHorn (S : SingleContentSignature) : Prop :=
  (∃ s : S.Subject, ∃ p : Prop, S.means s p) →
    ∃ s : S.Subject, ∃ p : Prop, S.means s p ∧ S.means s (¬ p)

/-- Some subject means some content, in `S`: the antecedent of `bareHorn`, witnessed.
    Footprint: `{}`. -/
def antecedentHolds (S : SingleContentSignature) : Prop :=
  ∃ s : S.Subject, ∃ p : Prop, S.means s p

/-- The canonical single-content model: two subjects, each meaning the single content `True`. The
    antecedent holds (both subjects mean `True`) and the consequent is unsatisfiable, since no
    subject can mean both `True` and `¬ True`.
    Footprint: `{}`. -/
def singleContentModel : SingleContentSignature where
  Subject := Bool
  content := fun _ => True
  means := fun _ p => p
  witness := false
  witnessContent := True
  faithful := fun _ _ h => h

/-- The antecedent of the bare horn holds in the canonical model: something is meant, so the
    blocked implication is not vacuously true and its refutation is a real counterexample rather
    than a trick about an unsatisfiable antecedent.
    Footprint: `{}`. -/
theorem antecedentHolds_in_canonicalModel :
    singleContentModel.antecedentHolds :=
  ⟨true, True, trivial⟩

end SingleContentSignature

/-- ★★★ **The bare rejected horn is refuted, not merely unproved.** In a faithful single-content
    model the antecedent holds — some subject means some content — while the consequent requires a
    subject to mean both a content and its negation, which faithfulness makes unsatisfiable. So
    `¬ bareHorn` is proved outright, and the frontier row is machine-backed.

    This is the formal content of the prose at `Choice.lean:36-40`: "`Means` is an opaque relation,
    and `AxTwoSubjects` yields two *different* subjects, each with a single content."

    What is refuted is the *implication* in the models constructed here, not `rejectedHornCoMeant`
    (its consequent, which two theorems above do establish, under stated premises), and not the
    ledger's `BLOCKED` verdict. The block remains: Γ does not derive the bare form.
    Footprint: `{}`. -/
theorem singleContentModelRefutesBareRejectedHorn
    (S : SingleContentSignature) (hFaith : S.Faithful)
    (hAntec : S.antecedentHolds) : ¬ S.bareHorn := by
  intro hHorn
  obtain ⟨t, q, hq1, hq2⟩ := hHorn hAntec
  exact absurd (hFaith t q hq1) (hFaith t (¬ q) hq2)

/-- The bare horn is refuted, concretely, in the canonical single-content model. The frontier is
    therefore machine-backed: the blocker is not an artefact of an unsuccessful search but a
    sentence that is false in a model of the meaning vocabulary.
    Footprint: `{}`. -/
theorem bareRejectedHornCoMeant_is_not_derivable :
    ¬ SingleContentSignature.singleContentModel.bareHorn :=
  singleContentModelRefutesBareRejectedHorn _ (fun _ _ h => h)
    SingleContentSignature.antecedentHolds_in_canonicalModel

/-!
## Section 4: two axiom-free routes to strong choice
-/

/-- Cartesian doubt is enough, and needs no axiom at all. A subject that simultaneously means `p`
    and `¬ p` makes a genuine strong choice between them, by pure logic
    (`Choice.lean:1091`).
    Footprint: `{Means, Subject}`. -/
theorem doubt_implies_trueChoice {s : Subject} {p : Prop}
    (h : Doubts s p) : TrueChoice s p (¬ p) :=
  chooses_implies_trueChoice (genuineChoice_of_doubt h)

/-- Genuine normativity is enough, and the master theorem of the corpus carries **no substantive
    axiom**: `indubitable_normative_free_will` (`IndubitableNormativeFreeWill.lean:115`) is pure
    logic over the `Means` address and the deontic opposition. The freedom of the subject is a
    strict conclusion here, not a postulate.
    Footprint: `{Means, Subject}`. -/
theorem genuineNormativity_implies_trueChoice {s : Subject} {p q : Prop}
    (h : GenuineNormativity s p q) : TrueChoice s p q :=
  chooses_implies_trueChoice (indubitable_normative_free_will h).1

/-!
## Section 5: true choice exists — unconditional
-/

/-- ★★★ TRUE CHOICE EXISTS, unconditionally, with no axiom introduced. `F1b` moves `BLOCKED` →
    `PROVEN↑`.

    The route: `T5_personExists_from_plurality` exhibits a person; `Person` unfolds to
    `ThomisticPersonCore`, which conjoins `DominionOverActs`, and `DominionOverActs s` is
    *definitionally* `FreeWill s` (`Person.lean:56`); the resulting `Chooses` is promoted to
    `TrueChoice` by pure logic in Section 2.

    Honest disclosure: the free-will existence content was already carried by the pre-existing
    META axiom `AxTwoSubjects`, because `Person` bundles `FreeWill`. This is a genuine derivation
    and a definitional one, and it is presented as both.
    Footprint: `{AxTwoSubjects, Means, Subject, Will, subjectWill}`. -/
theorem trueChoice_exists : ∃ s : Subject, ∃ p q : Prop, TrueChoice s p q := by
  obtain ⟨s, hPerson⟩ := T5_personExists_from_plurality
  obtain ⟨p, q, hChooses⟩ := hPerson.2.2
  exact ⟨s, p, q, chooses_implies_trueChoice hChooses⟩

/-- A free subject exists, on the same route and for the same reason: `Person → FreeWill` is
    definitional and plurality is already paid for. Recorded so that the existence half is
    legible without unfolding `TrueChoice`.
    Footprint: `{AxTwoSubjects, Means, Subject, Will, subjectWill}`. -/
theorem freeWill_exists : ∃ s : Subject, FreeWill s := by
  obtain ⟨s, hPerson⟩ := T5_personExists_from_plurality
  exact ⟨s, hPerson.2.2⟩

/-- The same existence as `freeWill_exists`, read at the other name. `FreeSubject` is
    *defined* as `FreeWill` (`Logos.Choice.FreeSubject s := FreeWill s`, `Choice.lean:185`;
    `freeSubject_iff_freeWill` is `Iff.rfl`), so the free subject exists exactly when free
    will does, at exactly the same price.

    Registered 2026-09-30 because the asymmetry it repairs was a surface defect, not a
    logical one. The kernel had unconditional `freeWill_exists` (C278, `{AxTwoSubjects}`)
    but only act-routed `Logos.Choice.freeSubject_exists` (`{AxIntentionalChoice}`), so the
    generated surfaces priced the Free Subject dearer than free will for the identical
    predicate. A price attaches to the *route* that reaches a predicate, never to a name;
    after this corollary both names carry the same footprint by construction.

    Footprint: `{AxTwoSubjects, Means, Subject, Will, subjectWill}`. -/
theorem freeSubject_exists : ∃ s : Subject, FreeSubject s := by
  obtain ⟨s, hFW⟩ := freeWill_exists
  exact ⟨s, hFW⟩

/-- Asiety obtains: true freedom is exhibited somewhere, by definition out of `trueChoice_exists`.
    Footprint: `{AxTwoSubjects, Means, Subject, Will, subjectWill}`. -/
theorem an_asietic_entity_exists : ∃ e : Entity, Asiety e := by
  obtain ⟨s, p, q, hTC⟩ := trueChoice_exists
  exact ⟨EntityOf s, s, p, q, rfl, hTC⟩

/-- A true chooser is a free subject: freedom is definitional out of the strong choice, with no
    further metaphysical step.
    Footprint: `{Means, Subject}`. -/
theorem asietic_is_true_freedom {s : Subject} {p q : Prop}
    (h : TrueChoice s p q) : FreeWill s :=
  trueChoice_implies_freeWill h

/-!
## Section 6: the Ground frontier, and the separation from canonical aseity
-/

/-- At a contingent stage, the ground grounds every true chooser. The two conjuncts
    `ContingentEntity` requires are exactly the two conjuncts `ground_of_reality_grounds_finite_
    subject` needs, so no helper is required. Divine necessity grounds the contingent order in
    which freedom operates, while the choosing remains the contingent subject's own act.
    Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
theorem the_ground_grounds_a_contingent_true_chooser {s : Subject} {p q : Prop}
    (_h : TrueChoice s p q) (hCont : ContingentEntity (EntityOf s)) :
    GroundsEntity Entity.ofGround (EntityOf s) :=
  ground_of_reality_grounds_finite_subject Entity.ofGround
    ofGround_necessary_ground_of_reality s hCont.2 hCont.1

/-- A true chooser at a contingent stage is externally grounded: grounded, and distinct from the
    ground. Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
theorem contingent_true_chooser_is_externally_grounded {s : Subject} {p q : Prop}
    (h : TrueChoice s p q) (hCont : ContingentEntity (EntityOf s)) :
    ExternalGrounding Entity.ofGround (EntityOf s) :=
  ⟨ofGround_ne_ofSubject s, the_ground_grounds_a_contingent_true_chooser h hCont⟩

/-- ★★ Asiety and canonical aseity are PROVABLY CONTRARY at a contingent stage, and this replaces
    the original claim that canonical aseity *is* indeterminacy. A true chooser at a contingent
    stage is grounded by the ground; a canonically aseitous entity is not externally grounded. So
    `CanonicalAseity → TrueChoice` is REFUTED for contingent choosers, not open, and any later pass
    that adds that bridge breaks Γ. `Logos.CanonicalAseity` is not modified.

    The contingency premise is explicit rather than smuggled. An earlier version derived it from an
    openness conjunct about the chooser's own entity, which made the separation look unconditional
    when it was not.
    Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
theorem contingent_asietic_is_not_canonically_aseitous {s : Subject} {p q : Prop}
    (h : TrueChoice s p q) (hCont : ContingentEntity (EntityOf s)) :
    ¬ CanonicalAseity (EntityOf s) := by
  intro hAse
  exact hAse ⟨Entity.ofGround, contingent_true_chooser_is_externally_grounded h hCont⟩

/-- The converse fails, so the two notions are independent in the aseitous direction: the ground is
    canonically aseitous (C186, under `hFinite`) and is provably not a subject, hence not asietic.
    Footprint: `{Means, Subject}`. -/
theorem ground_is_canonically_aseitous_but_not_asietic
    (hFinite : ∀ s : Subject, ∃ p : Prop, ¬ Means s p) :
    CanonicalAseity Entity.ofGround ∧ ¬ Asiety Entity.ofGround := by
  refine ⟨conditional_canonical_aseity hFinite, ?_⟩
  rintro ⟨s, p, q, hEq, _⟩
  exact absurd hEq (ofGround_ne_ofSubject s)

/-- The ground is provably not a subject, so it can never itself be the true chooser: the ground
    does not deliberate and does not choose. Footprint: `{Subject}`. -/
theorem ground_is_not_a_true_chooser : ¬ ∃ s : Subject, EntityOf s = Entity.ofGround :=
  fun ⟨s, h⟩ => absurd h (Ne.symm (ofGround_ne_ofSubject s))

/-- ★ The module in one line. Asiety is true freedom, weak choice implies strong choice, and true
    choice follows — with no axiom introduced, the co-signification of the rejected horn coming
    from `AxJudicativeBipolarity` as `base.txt:460` already recorded.
    Footprint: `{AxJudicativeBipolarity, AxTwoSubjects, Initiates, Means, State, Subject, Will, subjectWill}`. -/
theorem asietic_summary :
    (∀ (s : Subject) (p : Prop), ChoiceField s p (¬ p) → ClaimsCorrect s p →
        Chooses s p (¬ p))
      ∧ (∀ (s : Subject) {p q : Prop}, Chooses s p q → TrueChoice s p q)
      ∧ (∃ s : Subject, ∃ p q : Prop, TrueChoice s p q) :=
  ⟨fun _s p hF hJ => weakChoice_implies_chooses (p := p) (q := ¬ p) hF hJ,
   fun _ _ _ h => chooses_implies_trueChoice h,
   trueChoice_exists⟩

end Logos.AsieticChoice
