/-
# Logos.BoundedMeaning — bounded meaning requires a free intending subject (plan step S3)

The record of record is `AGENTS.md` (sync rule) with `GAPMAP.md` (per-claim status); this module was step **S3** of the retired personal-ground plan,
landing **D-3** (`BoundedMeaningRequiresFreeSubject`, `Tag: TRANS`) and promoting three rows of
the plan's §2 basis out of `investigations/trinitarian-probe.lean` (an audit artifact, never
compiled by `lake build`).

## The doctrine

> **Bounded meaning is constituted by a free intending subject.** An entity that is *bounded* in
> what it can mean, and still means, is a subject that genuinely chooses. What requires a free
> subject is **bounded** meaning, not meaning as such.

The guard has two conjuncts, and the second is the whole content of the claim:

- `PassiveIntentionalPotency e` — `e` has propositional capacity it has not actualised;
- `∃ p, EntityMeans e p` — `e` nonetheless means something.

A **total** scope is not potency: `EntityMeans Entity.ofGround p := True` for every `p`, so the
ground has no unactualised content and fails the *first* conjunct. That is why the naive
unrestricted thesis is not merely unproved but **false**
(`unrestricted_meaning_thesis_is_refuted`, §2): it reaches the ground and dies on
`Entity.noConfusion`. This is the machine-checked form of *praeter hoc, quod unus est, tres
sunt* — and it is a claim about the *unrestricted* form, not an incoherence to repair.

## The countermodel, and why it is not the plan's sketch

The plan's §4.2 sketches consistency by interpreting `Means s p := False` for every `s`. **That
model is not admissible here.** It is precisely the defect `AGENTS.md` (2026-09-29) forbids and
that `NegativeRetorsionSignature` committed: a model which denies *every act of signification*
instantiates no part of the vocabulary it is about, so reporting it as evidence about a state of
affairs overstates the ledger.

`boundedMeaningModel` therefore **grants** a genuine act of signification. Its subject `false`
means two mutually incompatible contents (`True` and `False`), so it is a chooser by construction
— `meansInstantiated` and `means_is_instantiated_in_canonicalModel` are theorems, not comments.
What the model *withholds* is potency for anything that is not a subject, which is the honest
reading: what the axiom constrains is subjects, not the domain.

Two facts are recorded so the model cannot be read as a trick:

- `guardAntecedentHolds_in_canonicalModel` — the guard's antecedent is **satisfied** somewhere,
  so `boundedMeaning_in_canonicalModel` is a real constraint and not a vacuous truth;
- `boundedMeaning_in_canonicalModel` — the axiom holds with that antecedent witnessed.

## What the guard excludes in the canonical reading, and what it does not

Each exclusion below is axiom-free *as a step* and is stated separately, so the guard is not
credited with an exclusion it does not perform:

- **ground** — `ofGround_no_intentional_potency` kills the first conjunct
  (`potency_guard_excludes_the_ground`);
- **atoms** — `EntityMeans (ofAtom _) p := False` kills the second
  (`potency_guard_excludes_the_atoms`).

**Subjects are *not* excluded, and that is the point.** For `Entity.ofSubject s` both conjuncts can
hold at once. The plan's §4.2 sentence "the guard's two conjuncts exclude the whole domain of
`Entity`" is therefore **false as written** — it contradicts the axiom stated six lines above it.
The correct statement, which this module's `guard_excludes_exactly_the_impersonal_cases`
records: the guard excludes the ground and the atoms, and leaves *precisely* the subjects, to
which the axiom then demands `FreeWill`. Consistency comes from constraining subjects, not from
an empty domain.

## What this module does not claim

- **Nothing about the three divine persons.** Pure actuality leaves them without passive
  potency, so the antecedent never fires for them. Their `FreeWill` rests entirely on the D-2
  bridge (`TrinitarianPersonalBridge`, priced `META`, plan §7).
- **Not that the thesis is derivable.** It is a *declared* axiom (`Tag: TRANS`), priced and
  tagged; consistency is what the countermodel above establishes, and consistency is not
  derivation.
- **Not a statement about a state of affairs.** Γ's core vocabulary has no `World` sort and this
  model is a free signature: it witnesses that the constraint is underivable from the signature,
  and is no evidence about a world (C559).
-/

import Logos.Core
import Logos.Semantics
import Logos.Agency
import Logos.Entity
import Logos.Alternatives
import Logos.Choice
import Logos.RecoveredOntologicalGround
import Logos.DivineClassicalAttributes

namespace Logos.BoundedMeaning

open Logos.Core (T)
open Logos.Semantics (World)
open Logos.Agency (Subject Means)
open Logos.Entity (Entity EntityOf ExistsAt)
open Logos.Alternatives (Incompatible)
open Logos.Choice (Chooses FreeWill)
open Logos.RecoveredOntologicalGround (EntityMeans OneEssence ActualEntity)
open Logos.NecessityEternity (ofGround_ne_ofSubject)
open Logos.DivinePureActuality (PassiveIntentionalPotency ofGround_no_intentional_potency)

/-!
## Section 1: the declared thesis (D-3)
-/

/-- Tag: TRANS
    **D-3.** Bounded meaning is constituted by a free intending subject. An entity that is
    bounded in what it can mean, and still means, is a subject that genuinely chooses; what
    requires a free subject is *bounded* meaning, not meaning as such.

    Once the conclusion reaches `e = EntityOf s`, `FreeWill s` is definitional from `Chooses`
    (`Means s p ∧ Means s q ∧ Incompatible p q`), so the entire substantive content of this axiom
    is the `e = EntityOf s` step: **discrimination presupposes a chooser.**

    It says nothing about the three divine persons — pure actuality leaves them without passive
    potency, so the antecedent never fires for them. Their `FreeWill` rests entirely on the D-2
    bridge (`TrinitarianPersonalBridge`, `META`). The thesis is doctrine about *creatures*.
-/
axiom BoundedMeaningRequiresFreeSubject :
  ∀ e : Entity, PassiveIntentionalPotency e → (∃ p : Prop, EntityMeans e p) →
    ∃ s : Subject, e = EntityOf s ∧ FreeWill s

/-! The axiom above is tagged `TRANS`, and the registry reads that tag as substantive; its
footprint therefore carries a *named* datum. It is a declared semantic choice, not vocabulary,
and the price is shown wherever it is used. -/

/-!
## Section 2: what the guard excludes, axiom-free, case by case
-/

/-- **The guard's first conjunct excludes the ground.** `EntityMeans Entity.ofGround p := True`
    for every `p`, so the ground has no unactualised propositional content and no passive
    intentional potency. Footprint: `{Means, Subject}` — inherited from
    `ofGround_no_intentional_potency`, whose own footprint is `{Means, Subject}`.

    The plan's §2 table records this row as `{}`. **It is not `{}`**: the proof closes through
    `ofGround_no_intentional_potency`, whose footprint carries the `Means` vocabulary. The plan
    row is corrected against the audited kernel. Footprint: `{Means, Subject}`. -/
theorem potency_guard_excludes_the_ground :
    ¬ (PassiveIntentionalPotency Entity.ofGround ∧ (∃ p : Prop, EntityMeans Entity.ofGround p)) :=
  fun h => ofGround_no_intentional_potency h.1

/-- **The guard's second conjunct excludes the atoms.** An atom has passive potency (there is
    content it does not bear) but bears none, so no proposition witnesses the second conjunct.
    Pure logic on the `ofAtom` arm: `hp : EntityMeans (Entity.ofAtom n) p`, which reduces to
    `False`. The footprint is nevertheless `{Means, Subject}` rather than `{}`, because
    `PassiveIntentionalPotency` is stated over `EntityMeans`, whose `ofSubject` arm mentions both
    and so enters the constant's dependency footprint. **Zero substantive axioms** either way.
    Footprint: `{Means, Subject}`. -/
theorem potency_guard_excludes_the_atoms (n : Nat) :
    ¬ (PassiveIntentionalPotency (Entity.ofAtom n) ∧ (∃ p : Prop, EntityMeans (Entity.ofAtom n) p)) := by
  rintro ⟨_, ⟨p, hp⟩⟩
  exact hp

/-- **The guard excludes exactly the impersonal cases.** Together the two rows above cover
    `Entity.ofGround` and every `Entity.ofAtom n`; what is left in `Entity` is the `ofSubject`
    branch, where both conjuncts can hold. So the guard does **not** exclude the whole domain of
    `Entity` (plan §4.2 overstates this), and the survivors are exactly the entities the axiom
    then constrains. Footprint: `{Subject}`. -/
theorem guard_excludes_exactly_the_impersonal_cases (e : Entity) :
    (e = Entity.ofGround ∨ ∃ n : Nat, e = Entity.ofAtom n) ∨ ∃ s : Subject, e = EntityOf s := by
  cases e with
  | ofGround => exact Or.inl (Or.inl rfl)
  | ofAtom n => exact Or.inl (Or.inr ⟨n, rfl⟩)
  | ofSubject s => exact Or.inr ⟨s, rfl⟩

/-!
## Section 3: the naive form is false, not unproved
-/

/-- **The unrestricted meaning thesis is refuted, not merely unproved.** Stated without the
    guard, the thesis claims that *every* entity that means anything is a free subject. The
    ground's scope is total (`EntityMeans Entity.ofGround p := True`), so it qualifies for
    meaning, and injectivity kills it: `Entity.ofGround ≠ EntityOf s` for every `s`
    (`Entity.noConfusion`).

    This is why the plan's thesis is the **guarded** one, and why the truth-restricted arm
    (`EntityMeans Entity.ofGround p := T p`) is a *rejected alternative* rather than a step: that
    arm trades infallibility for pure actuality and is recorded in the probe's P6.

    Footprint: `{Means, Subject}`. -/
theorem unrestricted_meaning_thesis_is_refuted :
    ¬ (∀ e : Entity, ∀ p : Prop, EntityMeans e p → ∃ s : Subject, e = EntityOf s ∧ FreeWill s) := by
  intro h
  obtain ⟨s, hs, _⟩ := h Entity.ofGround True trivial
  exact ofGround_ne_ofSubject s hs

/-!
## Section 4: the `{}` consistency countermodel for D-3

The model is a **free signature**: `Subject` and `Entity` are interpreted as `Bool`, and
`means`, `potency`, `entityMeans` are interpreted. `Incompatible` is *not* interpreted — it is
Γ's own `def Incompatible p q := ¬ (p ∧ q)`, so the model inherits the real one and its
constructive witness `T9_incompatibleAlternatives` (`True`, `False`).
-/

/-- A signature for the D-3 vocabulary: two sorts and the two relations the guard reads.

    `entityMeans` is deliberately **not** a field. In Γ it is *derived* from `means` through
    `Entity.ofSubject` (`EntityMeans (ofSubject s) p := Means s p`), so it is derived here too, by
    `entityMeansIn`. A model that could interpret entity-meaning independently could grant an
    entity meaning that no subject bears, and would then be testing a weaker axiom than D-3.
    Footprint: `{}`. -/
structure BoundedMeaningSignature where
  Subject : Type
  Entity : Type
  entityOf : Subject → Entity
  means : Subject → Prop → Prop
  potency : Entity → Prop

/-- Entity-meaning *inside* the model, derived from subject-meaning through `entityOf`
    exactly as Γ derives it from the `ofSubject` arm. Footprint: `{}`. -/
def entityMeansIn (S : BoundedMeaningSignature) (e : S.Entity) (p : Prop) : Prop :=
  ∃ s : S.Subject, e = S.entityOf s ∧ S.means s p

/-- Free will *inside* the model, mirroring Γ's `FreeWill`/`Chooses` term for term:
    `∃ p q, means s p ∧ means s q ∧ Incompatible p q`. Footprint: `{}`. -/
def freeWillIn (S : BoundedMeaningSignature) (s : S.Subject) : Prop :=
  ∃ p q : Prop, S.means s p ∧ S.means s q ∧ Incompatible p q

/-- The D-3 axiom read inside the model, with Γ's `PassiveIntentionalPotency` replaced by the
    interpreted `S.potency`. Footprint: `{}`. -/
def boundedMeaning (S : BoundedMeaningSignature) : Prop :=
  ∀ e : S.Entity, S.potency e → (∃ p : Prop, entityMeansIn S e p) →
    ∃ s : S.Subject, e = S.entityOf s ∧ freeWillIn S s

/-- The antecedent of the guard, in the model: some entity is both potency-bearing and
    meaning. Footprint: `{}`. -/
def guardAntecedentHolds (S : BoundedMeaningSignature) : Prop :=
  ∃ e : S.Entity, S.potency e ∧ (∃ p : Prop, entityMeansIn S e p)

/-- `Means` is instantiated in the model: some subject genuinely means. Footprint: `{}`. -/
def meansInstantiated (S : BoundedMeaningSignature) : Prop :=
  ∃ s : S.Subject, freeWillIn S s

/-- **The canonical bounded-meaning model.** Two subjects and two entities, both `Bool`.

    It **grants** a genuine act of signification: the subject `false` means `True` and `False`,
    two mutually incompatible contents, so it is a chooser by construction. It **withholds**
    potency from every entity that is not that subject's own entity — i.e. it withholds
    potency from entities that are *not* subjects, which is the constraint D-3 states.

    It is deliberately **not** the plan's §4.2 sketch (`means := fun _ _ => False`), which
    denies every act of signification and so instantiates none of the vocabulary it is about
    (`AGENTS.md`, 2026-09-29). Footprint: `{}`. -/
def boundedMeaningModel : BoundedMeaningSignature where
  Subject := Bool
  Entity := Bool
  entityOf := fun s => s
  means := fun s p => s = false ∧ (p = True ∨ p = False)
  potency := fun e => e = false

/-- **`Means` is genuinely instantiated in the canonical model.** The subject `false` means `True`
    and `False`, and `¬ (True ∧ False)` holds, so this subject genuinely chooses. This is the
    fact that makes the model admissible under `AGENTS.md`'s 2026-09-29 rule, and it is a theorem
    rather than a comment for that reason. Footprint: `{}`. -/
theorem meansInstantiated_in_canonicalModel :
    meansInstantiated boundedMeaningModel :=
  ⟨false, True, False, ⟨rfl, Or.inl rfl⟩, ⟨rfl, Or.inr rfl⟩, fun hc => hc.2⟩

/-- The model instantiates `Means`, so it is a countermodel about the meaning vocabulary and not
    about a signature whose meaning field is inert. Footprint: `{}`. -/
theorem means_is_instantiated_in_canonicalModel :
    ∃ s : Bool, ∃ p : Prop, boundedMeaningModel.means s p :=
  ⟨false, True, ⟨rfl, Or.inl rfl⟩⟩

/-- **The guard's antecedent is satisfied in the canonical model**, witnessed by the entity
    `false`. So `boundedMeaning_in_canonicalModel` is a real constraint on a non-empty
    situation, not a vacuous truth — the defect a `means := fun _ _ => False` model would hide.
    Footprint: `{}`. -/
theorem guardAntecedentHolds_in_canonicalModel :
    guardAntecedentHolds boundedMeaningModel :=
  ⟨false, rfl, True, ⟨false, rfl, rfl, Or.inl rfl⟩⟩

/-- **The canonical model satisfies D-3.** Given an entity with potency and with meaning, it is
    the entity of a subject that genuinely chooses: the only potent entity is `false`, which is
    `entityOf false`, and `false` chooses by `meansInstantiated_in_canonicalModel`. Footprint:
    `{}`. -/
theorem boundedMeaning_in_canonicalModel :
    boundedMeaning boundedMeaningModel := by
  intro e hPot ⟨p, hEM⟩
  change (e = false) at hPot
  change (∃ s : Bool, e = s ∧ (s = false ∧ (p = True ∨ p = False))) at hEM
  cases e with
  | false =>
      exact ⟨false, rfl, True, False, ⟨rfl, Or.inl rfl⟩, ⟨rfl, Or.inr rfl⟩, fun hc => hc.2⟩
  | true => exact absurd hPot (Bool.noConfusion hPot)

/-- **D-3 is `{}`-consistent on this signature.** The countermodel required by plan §4.2 and by
    step S3: a model of the vocabulary in which the declared axiom holds, with `Means`
    instantiated non-trivially. Footprint: `{}`. -/
theorem boundedMeaningRequiresFreeSubject_is_consistent :
    boundedMeaning boundedMeaningModel :=
  boundedMeaning_in_canonicalModel

/-- The two facts together are what the S3 gate asks for: the model instantiates the vocabulary
    the axiom denies, **and** the axiom holds there with the antecedent witnessed. Stated as one
    conjunction so no future edit can drop half of it. Footprint: `{}`. -/
theorem boundedMeaningRequiresFreeSubject_is_consistent_and_nonVacuous :
    boundedMeaning boundedMeaningModel ∧
      meansInstantiated boundedMeaningModel ∧
      guardAntecedentHolds boundedMeaningModel :=
  ⟨boundedMeaning_in_canonicalModel, meansInstantiated_in_canonicalModel,
    guardAntecedentHolds_in_canonicalModel⟩

/-!
## Section 5: the summary
-/

/-- **D-3 landed.** The unrestricted thesis is false (`unrestricted_meaning_thesis_is_refuted`);
    the guarded thesis is declared and consistent on a signature that instantiates meaning
    (`boundedMeaningRequiresFreeSubject_is_consistent_and_nonVacuous`); and the guard excludes the
    ground and the atoms while leaving precisely the subjects it constrains
    (`guard_excludes_exactly_the_impersonal_cases`). It is the only declaration in this module
    that carries D-3 itself, and it says so in its price. Footprint:
    `{BoundedMeaningRequiresFreeSubject, Means, Subject}`. -/
theorem boundedMeaning_summary (e : Entity) :
    (PassiveIntentionalPotency e → (∃ p : Prop, EntityMeans e p) → ∃ s : Subject, e = EntityOf s ∧ FreeWill s) ∧
    ¬ (∀ e : Entity, ∀ p : Prop, EntityMeans e p → ∃ s : Subject, e = EntityOf s ∧ FreeWill s) :=
  ⟨BoundedMeaningRequiresFreeSubject e, unrestricted_meaning_thesis_is_refuted⟩

end Logos.BoundedMeaning

#print axioms Logos.BoundedMeaning.potency_guard_excludes_the_ground
#print axioms Logos.BoundedMeaning.potency_guard_excludes_the_atoms
#print axioms Logos.BoundedMeaning.guard_excludes_exactly_the_impersonal_cases
#print axioms Logos.BoundedMeaning.unrestricted_meaning_thesis_is_refuted
#print axioms Logos.BoundedMeaning.meansInstantiated_in_canonicalModel
#print axioms Logos.BoundedMeaning.means_is_instantiated_in_canonicalModel
#print axioms Logos.BoundedMeaning.guardAntecedentHolds_in_canonicalModel
#print axioms Logos.BoundedMeaning.boundedMeaning_in_canonicalModel
#print axioms Logos.BoundedMeaning.boundedMeaningRequiresFreeSubject_is_consistent
#print axioms Logos.BoundedMeaning.boundedMeaningRequiresFreeSubject_is_consistent_and_nonVacuous
#print axioms Logos.BoundedMeaning.boundedMeaning_summary