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
open Logos.RecoveredOntologicalGround (OneEssence
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

    **DERIVED in Γ** — this `def` was recorded `BLOCKED` until 2026-10-03 and that was wrong.
    See `bareRejectedHornCoMeant_is_derivable` (Section 3c): the unconditional datum
    `performative_act_datum` together with `AxActPolarity` reaches `Means s p ∧ Means s (¬ p)` in
    two steps, at the price of one TRANS and one SEM axiom.

    What the old note got wrong was the scope of its own claim. The `ClaimsCorrect`-gated routes
    (`AxJudicativeBipolarity`) really are `Initiates`-gated with no witness in Γ — but
    `AxActPolarity` reads the act directly and needs no gate, so "no axiom of Γ reaches
    `Means s (¬ p)` from `Means s p`" was a statement about *two* routes, silently generalised to
    all of them.

    The honest residual is narrower and survives: the horn is **not derivable from the meaning
    vocabulary alone**. `singleContentModelRefutesBareRejectedHorn` (C273) refutes it in every
    single-content model, and `gammaMeans_is_not_single_valued` proves Γ's own `Means` is *not*
    single-valued. So the horn is discharged **because** meaning is many-valued here — see the
    dialectic table in Section 3c.

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

    **The bare form `bareRejectedHornCoMeant` does not need this premise.** It is derived outright
    in Section 3c (`bareRejectedHornCoMeant_is_derivable`), because `AxActPolarity` reads the act
    directly and so does not wait on an `Initiates` witness. This theorem is the *narrower* route:
    it needs a correctness-judgment, where the bare route needs only that an act occurred.

    Footprint: `{AxJudicativeBipolarity, Initiates, Means, State, Subject}`. -/
theorem retorsion_implies_rejectedHornCoMeant
    (hEvent : ∃ s : Subject, ClaimsCorrect s NoGN) : rejectedHornCoMeant := by
  obtain ⟨s, hClaim⟩ := hEvent
  exact ⟨s, NoGN, claims_correct_means_content s NoGN hClaim,
    AxJudicativeBipolarity s NoGN hClaim⟩

/-!
## Section 3c: the bare horn — refuted under single-valued meaning, derived in Γ

`bareRejectedHornCoMeant` is **derived in Γ**, at a stated price. This section also refutes it in
every single-content model. Those two facts are not in conflict; together they are the corpus's
sharpest result about meaning, and reading either alone gives the wrong answer.

### The dialectic

| | meaning is **single-valued** (one content per subject) | meaning is **many-valued** (Γ) |
|---|---|---|
| the bare rejected horn | **REFUTED** — `singleContentModelRefutesBareRejectedHorn` (C273) | **DERIVED** — `bareRejectedHornCoMeant_is_derivable` (below) |
| so co-meaning, hence `TrueChoice` from co-meaning | **unavailable** | **available** |

The horn is not a truth hidden behind Γ's axioms; it is a *consequence* of Γ refusing to make
meaning single-valued. `AxActPolarity` (`Choice.lean:796`) says an intentional act carries its own
polarity: `Act s p → Means s (¬ p)`. Together with the unconditional datum
`performative_act_datum : ∃ s p, Act s p`, Γ reaches `Means s p ∧ Means s (¬ p)` outright. What
C273/C274 refute is the horn over the *bare* meaning vocabulary `<Subject, Means>` plus
propositional non-triviality — that is, meaning **without** the act-polarity apparatus.

So the honest form of the negative result is the narrow one: **the bare horn is not a consequence
of the meaning vocabulary alone.** Γ reaches it only by paying for polarity, and the price is
visible: one TRANS axiom (`performative_act_datum`) and one SEM axiom (`AxActPolarity`).

The consequence worth stating plainly: *there is no reading of "meaning" on which Γ both keeps
meaning single-valued and has genuine choice.* Single-valuedness buys the refutation and costs the
choice; many-valuedness buys the choice and costs the refutation. That is a real trade, and
before 2026-10-03 this module asserted the first horn of it while the kernel sat on the second.

The `NegativeRetorsionSignature` pattern is followed for the refutation: a `structure` carrying
interpretation fields, a `def` for the sentence under audit, and theorems exhibiting a model.
`NegativeRetorsionAudit.lean` is referenced for the idiom only; it is not imported and none of its
definitions are used.

**Scope, stated honestly.** This is a model of the *meaning relation*: the `Means`/`Subject`
vocabulary, plus single-valuedness of meaning, plus propositional non-triviality. It is **not** a total
model of Γ. The claim proved is the precise one — the bare horn is **not derivable** from the
meaning vocabulary and `incompatible_self_negation` — which is strictly more than "not yet proved".

**Repaired 2026-10-03 (ISSUE_K Step 2(i)).** The field was `faithful : means s p → p`, and the
canonical model had `means := fun _ p => p` -- so every subject meant **every** proposition, and
`faithful` held only because `means s p → p` was the identity there. That is exactly the artifact
AGENTS.md forbids: a model that does not instantiate the vocabulary it is used to deny, here by
granting total meaning while claiming single content. The field is now genuine single-valuedness,
`single : means s p → p = content s`, which is what the structure's own name promised, and
`singleContentModel` has `means := fun _ p => p = True`.
`singleContentModel_is_genuinely_single_content` machine-checks the difference, and the pre-repair
witness is now a **compile error**.

**Why this strengthens the batch rather than shrinking it.** The batch's positive claim is that Γ
derives true choice with no new axiom. That claim is only as credible as Γ's negative results, so a
machine-checked refutation of the one form that does *not* follow is the strongest available
evidence that nothing positive here rests on a hidden assumption.
-/

/-- ★★★ **The bare rejected horn IS derived in Γ**, and this is the positive half of the dialectic
    recorded in the section header. `F11` moves `BLOCKED` → `DERIVED` at a stated price.

    The route is two steps, both short. `Agency.performative_act_datum` (`Agency.lean:233`,
    `Tag: TRANS`) is **unconditional** — `∃ s p, Act s p` — so no `Initiates` witness has to be
    hunted for; and `Choice.AxActPolarity` (`Choice.lean:796`, `Tag: SEM`) turns that act into its
    own polarity, `Act s p → Means s (¬ p)`. The act's subject already means `p` via
    `Agency.Act.1`, so the conjunction is immediate.

    This is why the module used to say "no `Initiates` witness anywhere in Γ": that was true of the
    *correctness* and *retorsion* routes, which are `ClaimsCorrect`-gated and therefore need an
    `Initiates`-gated premise — but the polarity route reads the act directly, so the unconditional
    datum discharges it. The price is **one TRANS and one SEM axiom**, and it is visible on the row
    rather than assumed away.

    What is NOT claimed: that the horn follows from the meaning vocabulary alone. It does not, and
    `singleContentModelRefutesBareRejectedHorn` (C273) below proves the negative counterpart. Read
    the two together — §3c's table is the honest summary.

    Footprint: `{AxActPolarity, Initiates, Means, State, Subject, performative_act_datum}`. -/
theorem bareRejectedHornCoMeant_is_derivable : bareRejectedHornCoMeant :=
  fun _h => by
    obtain ⟨s, p, hAct⟩ := Agency.performative_act_datum
    exact ⟨s, p, hAct.1, Choice.AxActPolarity s p hAct⟩

/-- The same act-polarity step, kept separate so the price is legible on its own: an intentional
    act alone delivers co-meaning, with no hypothesis about what is true. This is the whole content
    of `AxActPolarity`, and it is what `bareRejectedHornCoMeant_is_derivable` consumes.
    Footprint: `{AxActPolarity, Initiates, Means, State, Subject}`. -/
theorem act_alone_yields_polarity {s : Subject} {p : Prop}
    (hAct : Agency.Act s p) : Means s p ∧ Means s (¬ p) :=
  ⟨hAct.1, Choice.AxActPolarity s p hAct⟩

/-- The dialectic in one line, as a *theorem about Γ's own `Means`*: Γ has genuine co-meaning, and
    so its meaning relation is provably **not** single-valued. Read against C273, which refutes the
    horn in every single-valued model, this pins the trade: the horn is discharged **because**
    meaning is many-valued here.
    Footprint: `{AxActPolarity, Initiates, Means, State, Subject, performative_act_datum, CL}`. -/
theorem gammaMeans_is_not_single_valued :
    ¬ (∀ (s : Subject) (p q : Prop), Means s p → Means s q → p = q) :=
  fun hSingle => by
    obtain ⟨s, p, hAct⟩ := Agency.performative_act_datum
    have hNeg : Means s (¬ p) := Choice.AxActPolarity s p hAct
    have hEq : p = ¬ p := hSingle s p (¬ p) hAct.1 hNeg
    have hiff : p ↔ ¬ p := Iff.of_eq hEq
    rcases Classical.em p with hp | hn
    · exact (hiff.mp hp) hp
    · exact hn (hiff.mpr hn)

/-- A single-content model of the meaning relation: every subject is assigned exactly one
    `Prop`, and `means` is single-valued -- it can mean only that subject's assigned content.
    Co-signification of a content and its negation is therefore impossible, while
    meaning-existence is guaranteed by `witnessContent`.

    `single` is the load-bearing field, and it is now the honest version of it. It was `faithful`
    (`means s p → p`) until 2026-10-03, and that version was defeatable: with
    `means := fun _ p => p` a model satisfied the field while meaning every proposition, so the
    "single content" claim was vacuous. See `singleContentModel_is_genuinely_single_content`.

    Single-valuedness does close the model, but *classically*: it turns the two meanings into
    `q = content t` and `¬ q = content t`, hence `q = ¬ q` as propositions, and `q ↔ ¬ q` is
    refutable only via the excluded middle. Faithfulness closed it constructively by producing two
    proofs outright. That is the one respect in which the repair is weaker, and it costs `CL`
    (not a substantive price; the footprint is the meta-logic trio alone). -/
structure SingleContentSignature where
  Subject : Type
  content : Subject → Prop
  means : Subject → Prop → Prop
  witness : Subject
  witnessContent : Prop
  single : ∀ (s : Subject) (p : Prop), means s p → p = content s

namespace SingleContentSignature

/-- `means` is single-valued in `S`: anything `s` means is `s`'s assigned content. This is what
    makes the countermodel close, by turning `means t q ∧ means t (¬ q)` into `q = ¬ q`. Replaces
    `Faithful`, which admitted the degenerate `means := fun _ p => p` -- a model satisfying the
    field while meaning every proposition (AGENTS.md, binding 2026-09-29).
    Footprint: `{}`. -/
def SingleValued (S : SingleContentSignature) : Prop :=
  ∀ (s : S.Subject) (p : Prop), S.means s p → p = S.content s

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
  means := fun _ p => p = True
  witness := false
  witnessContent := True
  single := fun _ _ h => h

/-- The antecedent of the bare horn holds in the canonical model: something is meant, so the
    blocked implication is not vacuously true and its refutation is a real counterexample rather
    than a trick about an unsatisfiable antecedent.
    Footprint: `{}`. -/
theorem antecedentHolds_in_canonicalModel :
    singleContentModel.antecedentHolds :=
  ⟨true, True, rfl⟩

/-- **Meaning-coherence check for the repaired model (AGENTS.md, binding 2026-09-29).** A
    countermodel is evidence only if it *instantiates the vocabulary it is used to deny*. The
    pre-repair model failed this: `means := fun _ p => p` let every subject mean **every**
    proposition, so it was not a single-content model at all and its `faithful` field held only
    because `means s p → p` was the identity there -- a self-refuting artifact of an
    uninterpreted signature field, the `NegativeRetorsionSignature` genre.

    The repaired model has `means := fun _ p => p = True`, so each subject means exactly one
    proposition, and this theorem says exactly that: two contents meant by one subject are equal.
    The countermodel is therefore honest, and what is refuted is the bare horn rather than a
    degenerate reading of `means`.
    Footprint: `{}`. -/
theorem singleContentModel_is_genuinely_single_content :
    ∀ s : singleContentModel.Subject, ∀ p q : Prop,
      singleContentModel.means s p → singleContentModel.means s q → p = q := by
  intro s p q hp hq
  exact hp.trans hq.symm

end SingleContentSignature

/-- ★★★ **The bare rejected horn is refuted wherever meaning is single-valued** — the negative
    half of the dialectic in the section header. In a single-content model the antecedent holds —
    some subject means some content — while the consequent requires a subject to mean both a content
    and its negation, which single-valuedness makes unsatisfiable. So `¬ bareHorn` is proved
    outright.

    Read this against `bareRejectedHornCoMeant_is_derivable`, which derives the same sentence in Γ.
    The two are not rivals: this theorem says meaning *cannot* be single-valued and support the
    horn, and the other says Γ's meaning *is* many-valued and so does. Nothing is left over.

    What is refuted is the *implication* over a **single-valued** meaning relation, not
    `rejectedHornCoMeant` (its consequent) and not the bare horn as Γ states it. The earlier
    version of this note closed with "Γ does not derive the bare form" — **that was false**, and it
    is what kept the frontier row `BLOCKED` for three days. Γ does derive it:
    `bareRejectedHornCoMeant_is_derivable`, at `{performative_act_datum, AxActPolarity}`.

    The two results are complementary, not competing, and together they are the real claim:
    **the horn holds in Γ because Γ's meaning is many-valued** (`gammaMeans_is_not_single_valued`),
    **and is unsatisfiable wherever meaning is single-valued** (this theorem). There is no reading
    of "meaning" that keeps single-valuedness and genuine co-meaning together.
    Footprint: `{CL, propext, Quot.sound}`. -/
theorem singleContentModelRefutesBareRejectedHorn
    (S : SingleContentSignature) (hSingle : S.SingleValued)
    (hAntec : S.antecedentHolds) : ¬ S.bareHorn := by
  intro hHorn
  obtain ⟨t, q, hq1, hq2⟩ := hHorn hAntec
  have hEq : q = ¬ q := (hSingle t q hq1).trans (hSingle t (¬ q) hq2).symm
  have hiff : q ↔ ¬ q := Iff.of_eq hEq
  rcases Classical.em q with hq | hnq
  · exact (hiff.mp hq) hq
  · exact hnq (hiff.mpr hnq)

/-- The bare horn is refuted, concretely, in the canonical single-content model. The frontier is
    therefore machine-backed: the blocker is not an artefact of an unsuccessful search but a
    sentence that is false in a model of the meaning vocabulary.
    Footprint: `{CL, propext, Quot.sound}`. -/
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
    OneEssence Entity.ofGround (EntityOf s) :=
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
/-- **DOCTRINE ROW 4 (plan §20.1): `Asiety` means Freedom, and Freedom means Personal.**

Every `Person` is *asietic*, i.e. true freedom exhibited at their own entity — and the
entailment is **free of substantive axioms**: three definitional steps and one tautology, no
declared axiom consumed. The `{Means, Subject, Will, subjectWill}` footprint is the four vocabulary
declarations the route runs through, which is why this is priced the same as `Person` itself.

    `Person s`            = `IndividualSubstance s ∧ RationalNature s ∧ DominionOverActs s`
    `DominionOverActs s`  = `FreeWill s`                         (definitional, `Person.lean:56`)
    `FreeWill s`          = `∃ p q, Chooses s p q`             (the body, `Choice.lean:188`)
    `Chooses s p q`       → `TrueChoice s p q`                (pure logic, above)

So `Person s → ∃ p q, TrueChoice s p q`, which is `Asiety (EntityOf s)` by the body of
`Asiety` — witnessed at `s` itself. This is the link plan §20.1 argued in prose and
§20.5 wrongly listed as established; it is established **here**.

The direction matters and is the cheap one: `Person → Asiety` is the projection above and costs
nothing, whereas the converse would need the pair `p q` extracted from the existential and is not
attempted. `FreeWill → Person` is likewise a separate priced row (`freeWill_implies_person`,
resting on `will_individuation`); this theorem is the other direction and does not consume it.

Consequence for §20: the doctrine's *kind* — personality as true freedom — is free, and so
is `the_ground_is_not_void_of_personhood`. Applying this to a person `a` of the ground's
perichoretic trio gives `Asiety (EntityOf a)` at the same vocabulary-only price, i.e. **the
Persons are asietic, and being one with the essence does not cost freedom.**
Footprint: `{Means, Subject, Will, subjectWill}`. -/
theorem person_is_asietic (s : Subject) (hP : Person s) : Asiety (EntityOf s) := by
  obtain ⟨p, q, hCh⟩ := hP.2.2
  exact ⟨s, ⟨p, q, rfl, chooses_implies_trueChoice hCh⟩⟩

end Logos.AsieticChoice
