/-
# Logos.CharacteristicSoleBearer — the ground is the *sole bearer* of the footprint characteristics

This module is the answer to the question the rest of the corpus leaves open. A characteristic can
be recorded in Γ in two very different ways:

* **instantiated** — `Entity.ofGround` happens to have the property. This is what
  `ofGround_divine_immutability`, `ofGround_divine_simplicity`, `ofGround_foundational_omniscience`
  and their siblings establish, and on its own it is weak: it does not distinguish *"the ground is
  the unique bearer"* from *"the ground is the only example anyone wrote down."*
* **discriminating** — the property *characterises* the ground: `∀ e, P e → e = Entity.ofGround`.
  This is the form that makes a concept do work, and until this batch it held for exactly one
  characteristic, §9 precedence (C433, `Precedence.ofGround_sole_precedes_right_wrong`).

This module proves the discriminating form for six of the seven footprint characteristics, and in
five cases the proof is *the same proof*: a subject cannot ground the ground, so a subject cannot
be a universal modal ground, so no subject bears a characteristic whose structure carries a
`universal_ground` field. The sixth — Divine Simplicity — needs no reference to F15 at all.

## What the price is, and where it sits

`SemanticFinitude` (`SemanticFinitude.lean:151`, the 27th and last declared axiom, `Tag: VOCAB`) is
`∀ s : Subject, ∃ p : Prop, ¬ Means s p`. It is used here in exactly one place: to turn the
*hypothesis* `∃ p, ¬ Means s p` of `discriminating_subject_cannot_ground_the_ground`
(`CanonicalAseity.lean:113`) into a statement about *every* subject. Everything else in this module
is a case analysis on the three constructors of `Entity`.

So the batch's honest summary is: **unicity of the ground is free, and it is free because a subject
cannot be a universal ground.** The one axiom that has to be paid (`SemanticFinitude`) is what makes
"no subject" mean *all* subjects rather than "no discriminating subject" — which is exactly the
distinction C433's docstring drew for §9 precedence, and exactly the distinction that
`discriminating_subject_cannot_ground_the_ground` records for the *other* characteristics. One
bound, two places it was needed; the corpus now says so in one file.

**This does not make the ground unique among grounds.** The theorems below say the ground is the
*only bearer of these properties*. Where two universal grounds could coexist, Γ's answer is
`FoundationalUnicity.unicity` (C199), which needs `AsymmetricGrounding` as an extra premise and
which is a different, weaker claim; see the module note in `FoundationalUnicity.lean`.

## The seventh characteristic, and the one honest negative

* **Divine Transcendence** already had its discriminating form before this batch —
  `DivineTranscendence.ofGround_sole_transcendent_ground` (`:315`, `∀ e, TranscendentGround e → e =
  Entity.ofGround`, footprint `{Subject}`, unconditional). It was **already ledgered, as C307** — the
  batch added no theorem for it. What was missing was the reader-facing attributes row, which the
  generator now emits; the correction is recorded in `GAPMAP.md`. It is re-exported
  here in the master theorem (C446) so that all six stand side by side.
* **Divine Immutability** had **no** discriminating form in this batch, and the reason was recorded
  in `DivineImmutability.lean` and in `ImmutabilitySoleBounded` below: `capacity_invariance` is
  vacuous by reflexivity and `Initiates` is an unconstrained signature field, so the necessary-kind
  subject arm was not closable here. It was reported as a boundary, not quietly dropped. That
  boundary is now closed in the other direction by `Logos.ImmutabilitySoleBearer`: C453 is
  `COUNTERMODEL`, not `DEFERRED`.
-/

import Logos.Core
import Logos.Semantics
import Logos.Entity
import Logos.Agency
import Logos.RecoveredOntologicalGround
import Logos.CanonicalAseity
import Logos.NecessityEternity
import Logos.DivineImmutability
import Logos.DivineSimplicity
import Logos.FoundationalOmnipresence
import Logos.FoundationalUnicity
import Logos.DivinePureActuality
import Logos.DivineOmniscience
import Logos.DivineOmnipotence
import Logos.DivineTranscendence
import Logos.SemanticFinitude

namespace Logos.CharacteristicSoleBearer

open Logos.Semantics (World)
open Logos.Entity (Entity EntityOf ExistsAt actualWorld)
open Logos.Agency (Subject Means)
open Logos.RecoveredOntologicalGround (EntityMeans OneEssence)
open Logos.NecessityEternity (ofGround_ground_of_reality)
open Logos.CanonicalAseity (discriminating_subject_cannot_ground_the_ground)
open Logos.DivineSimplicity (DivineSimplicity TranscendentGround
  divine_simplicity_is_unique_to_the_ground)
open Logos.FoundationalOmnipresence (FoundationalOmnipresence MaximalCapacity
  UniversalModalGround)
open Logos.FoundationalUnicity (AsymmetricGrounding)
open Logos.DivinePureActuality (DivinePureActuality atom_fails_pure_actuality
  discriminating_subject_fails_pure_actuality)
open Logos.DivineOmniscience (FoundationalOmniscience atom_not_truth_exhaustive)
open Logos.DivineOmnipotence (FoundationalOmnipotence atom_not_gapless_operate)
open Logos.DivineTranscendence (ofGround_sole_transcendent_ground)
open Logos.SemanticFinitude (GroundTranscendence)

/-- C441 — the shared subject arm, in the exact form the three `universal_ground` routes need: a
    subject-correlate that grounds `Entity.ofGround` would have to mean every proposition, and
    `SemanticFinitude` denies that. This is the one place the batch pays the 27th axiom; the
    `hG` it is handed is the `OneEssence` disjunct of a `UniversalModalGround` witness
    instantiated at `(actualWorld, Entity.ofGround)`.

    Every `ExistsAt` premise discharged here is the ◈ stipulation `ofGround_existsAt`; the
    `OneEssence` disjunct is the *other* branch of `UniversalModalGround`, so no assumption
    about the subject's world-relative existence is made or needed.
    Footprint: `{GroundTranscendence, Means, Subject}`. -/
theorem no_subject_grounds_the_ground (s : Subject) :
    ¬ OneEssence (EntityOf s) Entity.ofGround := by
  obtain ⟨p, hp⟩ := GroundTranscendence s
  exact discriminating_subject_cannot_ground_the_ground s ⟨p, hp⟩

/-- C442 — **the ground alone is omniscient**: no entity other than `Entity.ofGround` is
    foundationally omniscient, so the concept discriminates the ground rather than merely
    describing it.

    *The atom arm* is free: `atom_not_truth_exhaustive` (`DivineOmniscience.lean:155`) excludes
    atoms from `TruthExhaustive` because `EntityMeans (ofAtom _) = False`. *The subject arm* runs
    through the structure's `universal_ground` field: a subject universal modal ground would have
    to ground `Entity.ofGround` itself, which is `no_subject_grounds_the_ground`.

    **Disclosure.** The `universal_ground` field is doing all the work, not the scope. Note also
    what this does *not* say: the ground is *not* infallible. `ofGround_not_truth_tracking`
    (`DivineOmniscience.lean:144`) refutes `TruthTracking Entity.ofGround`, because the ground's
    scope bears every proposition including `False` by the constructor's match arm. Unicity of
    the *permissive* sense therefore coexists with refutation of the *strong* one.
    Footprint: `{GroundTranscendence, Means, NecessarySubjectKind, Subject}`. -/
theorem ofGround_sole_foundational_omniscience :
    ∀ e, FoundationalOmniscience e → e = Entity.ofGround := by
  intro e h
  cases e with
  | ofGround => rfl
  | ofAtom n => exact False.elim (atom_not_truth_exhaustive n h.truth_exhaustive)
  | ofSubject s =>
      obtain hEq | hGr :=
        h.universal_ground actualWorld Entity.ofGround trivial
      · cases hEq
      · exact False.elim (no_subject_grounds_the_ground s hGr)

/-- C443 — **the ground alone is omnipotent**: no entity other than `Entity.ofGround` operates
    gaplessly across the satisfiable domain, so gapless operative scope characterises the ground.

    *The atom arm* is free: `atom_not_gapless_operate` (`DivineOmnipotence.lean:220`) — an atom
    exists exactly where its content obtains, so it misses the content `¬atom n`. *The subject arm*
    runs through `universal_ground` as in C442.

    **Disclosure — this is the operative sense, not the causal one.** `OperatesAt v e P` is
    *presence plus obtaining*, a priced identification of Γ's only operation relation
    (`DivineOmnipotence.lean:120`); in this batch Γ had no production relation, so causal/creative
    omnipotence stayed BLOCKED at F10 and this theorem must not be read as touching it. The
    production relation (C463) and the universal production bridge (C493) came later and leave
    this row's footprint untouched. The
    `existence_everywhere_does_not_entail_operation` countermodel (`:150`) is the machine-checked
    statement of that gap.

    **Disclosure — the necessary-kind subject arm is closed by `universal_ground`, not by
    world-rigidity.** `gapless_operators_are_ground_or_necessary_kind` (`:250`) proves that a
    gapless operator is the ground *or* a necessary-kind subject: whoever is present everywhere
    operates everything satisfiable, and `NecessarySubjectKind` makes a subject present
    everywhere. So `gapless_operate` alone does **not** characterise the ground. It is the
    `universal_ground` field, paid for by `SemanticFinitude`, that removes the second possibility.
    This is the sharpest statement in the batch of why a structure's fields are not
    interchangeable with its doctrine.
    Footprint: `{GroundTranscendence, Means, NecessarySubjectKind, Subject}`. -/
theorem ofGround_sole_foundational_omnipotence :
    ∀ e, FoundationalOmnipotence e → e = Entity.ofGround := by
  intro e h
  cases e with
  | ofGround => rfl
  | ofAtom n => exact False.elim (atom_not_gapless_operate n h.gapless_operate)
  | ofSubject s =>
      obtain hEq | hGr :=
        h.universal_ground actualWorld Entity.ofGround trivial
      · cases hEq
      · exact False.elim (no_subject_grounds_the_ground s hGr)

/-- C444 — **the ground alone is foundationally omnipresent**: no entity other than
    `Entity.ofGround` spans all worlds, grounds all beings, and spans all propositions.

    This is the cheapest of the three `SemanticFinitude`-priced rows, because its
    `maximal_capacity` field settles *both* non-ground constructors on its own:
    `EntityMeans (Entity.ofAtom _) = False` kills the atom arm with no theorem, and for a subject
    `MaximalCapacity (EntityOf s) := ∀ p, Means s p` is exactly what `SemanticFinitude` denies.

    **Disclosure — this is foundational, not physical.** Γ's omnipresence is *world-indexed
    presence plus universal grounding*, and the module says so at length
    (`FoundationalOmnipresence.lean:1-31`). Physical omnipresence (spatial extension) and
    quantitative metric infinity remain ❌: `Space`, `Spatial`, `Metric`, `Cardinal` and `Infinity`
    have no declarations in `formal/Logos/` at all, so no proof could close them.
    Footprint: `{GroundTranscendence, Means, NecessarySubjectKind, Subject}`. -/
theorem ofGround_sole_foundational_omnipresence :
    ∀ e, FoundationalOmnipresence e → e = Entity.ofGround := by
  intro e h
  cases e with
  | ofGround => rfl
  | ofAtom _ => exact False.elim (h.maximal_capacity True)
  | ofSubject s =>
      obtain ⟨p, hp⟩ := GroundTranscendence s
      exact False.elim (hp (h.maximal_capacity p))

/-- C445 — **the ground alone is Actus Purus**: no entity other than `Entity.ofGround` has zero
    passive potentiality, so Divine Pure Actuality discriminates the ground in the same
    unconditional shape as §9 precedence (C433) — which makes the two directly comparable.

    *The atom arm* is `atom_fails_pure_actuality` (`DivinePureActuality.lean:228`): an atom has
    passive existential potency, witnessed in a world where its content is false. *The subject
    arm* is `discriminating_subject_fails_pure_actuality` (`:241`) instantiated at
    `SemanticFinitude s`, which says every subject has unactualized propositional capacity.

    **Disclosure — the whole subject arm is the 27th axiom.** `DiscriminatingSubjectFails` needs
    `∃ p, ¬ Means s p`, and for *all* subjects that is `SemanticFinitude` and nothing else. The
    price is not incidental: it is the price of the ground's `EntityMeans _ p := True` stipulation,
    which is what makes "no passive intentional potency" and "means everything" the same sentence.
    Footprint: `{GroundTranscendence, Initiates, Means, NecessarySubjectKind, State, Subject}`. -/
theorem ofGround_sole_divine_pure_actuality :
    ∀ e, DivinePureActuality e → e = Entity.ofGround := by
  intro e h
  cases e with
  | ofGround => rfl
  | ofAtom n => exact False.elim (atom_fails_pure_actuality n h)
  | ofSubject s =>
      obtain ⟨p, hp⟩ := GroundTranscendence s
      exact False.elim (discriminating_subject_fails_pure_actuality s ⟨p, hp⟩ h)

/-- C446 — the batch's master theorem: **the ground is the sole bearer of all six footprint
    characteristics simultaneously**, so the six concepts jointly pick out `Entity.ofGround` and
    not merely describe it. Divine Simplicity and Divine Transcendence enter at their audited cost
    — `{Means, Subject}` and `{Subject}`, the latter unconditionally — and the other four all carry
    `SemanticFinitude`.

    The conjunction is a record, not a new inference: each conjunct is one of the theorems above
    (with `divine_simplicity_is_unique_to_the_ground` from `DivineSimplicity.lean` and
    `ofGround_sole_transcendent_ground` from `DivineTranscendence.lean`). What is new is that they
    are now available as one statement, which is the form the reader-facing list needs.

    **What it does not say.** Not that the ground is the unique *ground* — that is
    `FoundationalUnicity.unicity` (C199), which needs `AsymmetricGrounding` and is a weaker claim.
    Not that any of this is causal: the six are structural and modal, and F10 remains BLOCKED.
    Footprint: `{GroundTranscendence, Initiates, Means, NecessarySubjectKind, State, Subject}`. -/
theorem the_ground_is_sole_bearer_of_the_footprint_characteristics :
    (∀ e, FoundationalOmnipresence e → e = Entity.ofGround) ∧
    (∀ e, FoundationalOmniscience e → e = Entity.ofGround) ∧
    (∀ e, FoundationalOmnipotence e → e = Entity.ofGround) ∧
    (∀ e, DivinePureActuality e → e = Entity.ofGround) ∧
    (∀ e, DivineSimplicity e → e = Entity.ofGround) ∧
    (∀ e, TranscendentGround e → e = Entity.ofGround) :=
  ⟨ofGround_sole_foundational_omnipresence,
   ofGround_sole_foundational_omniscience,
   ofGround_sole_foundational_omnipotence,
   ofGround_sole_divine_pure_actuality,
   divine_simplicity_is_unique_to_the_ground,
   ofGround_sole_transcendent_ground⟩

/- **The boundary this batch did not cross: Divine Immutability.** Immutability is *not* in the
    master theorem, and the reason is recorded here rather than hidden. (It is a prose disclosure,
    not a theorem: Γ can neither prove nor refute the claim, and a `sorry`-bearing declaration
    would be worse than silence — the obstruction below is a *missing lemma*, and it is recorded
    in `PLAN2.md` Task 5 and in `ImmutabilitySoleBounded` in the ledger as a priced boundary.)

    * The atom arm is closable: `EntityExistsAt w (Entity.ofAtom n) = w n = TV.t` and
      `World := Nat → TV`, so a world denying `n` breaks `ModalInvariance`.
    * The subject arm is not closable here. `DivineImmutability.capacity_invariance` is
      `∀ p, ∀ _w₁ _w₂, EntityMeans e p ↔ EntityMeans e p` (`DivineImmutability.lean:131-132`) —
      **vacuously true of every entity by reflexivity**, the F16 wall. The only remaining field is
      `NotInSuccession e := ¬ ∃ s σ σ' p, e = EntityOf s ∧ Initiates s σ σ' p`
      (`NecessityEternity.lean:102-104`), which cannot be refuted generically. **Corrected
      2026-09-28 (C458–C462):** the old justification was that `Initiates` is an unconstrained
      signature field, and that justification expired when C454 (`performative_act_datum`,
      `Tag: TRANS`) inhabited `Initiates` — a countermodel in which no subject initiates anything
      is no longer admissible as a model of Γ. The field is still not refutable, and the arm is
      still open, but for a sharper reason: the predicate is *non-discriminating*, holding of every
      atom as well (C459), so `the_ground_not_in_succession` is a non-correlateness fact rather
      than a non-agency one. And `NecessarySubjectKind` has **no**
      exclusion theorem anywhere in the corpus, so a necessary-kind subject is world-rigid by
      construction and is a legitimate candidate for a world-rigidity-based characteristic.

    So immutability is reported as a **priced boundary**, and the honest reading is: *the ground
    is the sole bearer of every footprint characteristic whose structure carries a grounding or
    capacity field; immutability, whose only non-vacuous field is negative and quantified over an
    open signature, is the one whose exclusivity Γ cannot yet certify.* -/

#print axioms no_subject_grounds_the_ground
#print axioms ofGround_sole_foundational_omniscience
#print axioms ofGround_sole_foundational_omnipotence
#print axioms ofGround_sole_foundational_omnipresence
#print axioms ofGround_sole_divine_pure_actuality
#print axioms the_ground_is_sole_bearer_of_the_footprint_characteristics

end Logos.CharacteristicSoleBearer
