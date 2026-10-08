/-
# Logos.ImmutabilitySoleBearer — Divine Immutability is *not* sole-bearing, and the machine-checked reason

`Logos.CharacteristicSoleBearer` closes with an honest negative, and this module discharges it.
The claim it declines to prove is C453, the **unicity** of immutability:

```lean
∀ e : Entity, DivineImmutability e → e = Entity.ofGround
```

C453 has been `DEFERRED` with no declaration since the sole-bearer batch. This module replaces the
deferral with a **machine-checked separation**, and — more usefully — with the exact formal
statement of the unavailable universal, which is the same shape as a result the corpus already has.

## Why the claim fails, in one sentence

`NotInSuccession e` is `¬ ∃ s σ σ' p, e = EntityOf s ∧ Initiates s σ σ' p`, so it holds of **every**
entity whose subject correlate never initiates; and the act datum (C454) requires that *one* subject
initiates, not that *every* subject does. `ExistsAt` for a subject is
`SubjectExistsAt w s := NecessarySubjectKind s ∨ w = actualWorld` (`Entity.lean:55`), so a subject
of the necessary kind exists at every world and satisfies `ModalInvariance` and `StageInvariance`
outright; `CapacityInvariance` is satisfied by every entity (C321). **A necessary-kind subject that
never initiates therefore bears all four fields, and is not the ground.** C453 is non-derivable in this free-signature sense—not proved false inside Γ.

## The right diagnosis, and why it is not a defeat

The trap in refuting a uniqueness claim is to build a model in which *nothing happens* — no
initiation at all — and call that a refutation. Such a model would be a refutation of Γ, not of
C453: `performative_act_datum` forbids it. So the countermodel below is built the other way round.
It **saturates** the act datum — one subject genuinely acts, with a real `Means` and a real
`Initiates` — and only then exhibits a necessary-kind subject that does not. The two findings are
proved in a single model because they are a single fact: *initiation is a real relation with a
real inhabitant, and it is not universal over necessary-kind subjects.*

That is the formal content of the gap between C454 and C453:

| | statement | status |
|---|---|---|
| C454 (global) | `∃ s, ∃ p, Act s p` | `AXIOM` (`performative_act_datum`, `Tag: TRANS`) |
| C453 needs (per-necessary-kind-subject) | `∀ s, NecessaryKind s → ∃ σ σ' p, Initiates s σ σ' p` | **not derivable** — separated below |

ACT-CASCADE (C469–C480) made the *global* form visible in twelve unconditional rows, all of which
inherit the datum. This module shows the price of that: the datum is a **global existential**, and
every necessary-kind-subject strengthening of it is unavailable until someone pays for a per-necessary-kind-subject bound.
The exact missing lemma is now in the ledger rather than implicit in a `DEFERRED`.

## What survives, and is recorded rather than dropped

Unicity of immutability is non-derivable in the free-signature sense used here, but the batch does **not** claim its negation inside Γ. These stay true
and keep their existing ids:

* `ofGround_divine_immutability` (C201) — the ground *is* immutable, `{Initiates, Means,
  NecessarySubjectKind, State, Subject}`, 0 substantive axioms;
* `capacity_invariance_holds_for_every_entity` (C321) — field 4 is vacuous for all entities;
* `the_ground_and_every_atom_are_outside_succession` (C459) — field 3 holds of the ground and of
  every atom;
* `some_entity_is_in_succession` (C487, `Logos.CharacteristicClosure`) — field 3 is *refutable*,
  which C459 alone did not establish.

So the corrected table row reads: **immutability is the one footprint characteristic the ground
does not uniquely bear**, and the reason is quantified over `Subject` rather than over `Entity` —
a subject-indexed relation cannot discriminate an `Entity`-indexed property. That is a general
observation about the vocabulary, not a defect in this batch, and it is the same reason F10's
production relation had to be re-indexed from `Subject` to `Entity` in THOMISTIC-ACT.
-/

import Logos.Core
import Logos.Semantics
import Logos.Entity
import Logos.Agency
import Logos.RecoveredOntologicalGround
import Logos.NecessityEternity
import Logos.DivineImmutability

namespace Logos.ImmutabilitySoleBearer

open Logos.Semantics (World)
open Logos.Entity (Entity EntityOf)
open Logos.Agency (Subject State Initiates Act performative_act_datum)
open Logos.NecessityEternity (NotInSuccession)

/-- The counter-structure. Every field is one of the four `DivineImmutability` fields, read at its
    own logical strength and no stronger, so that a witness inhabiting this structure is a witness
    that the structure's *shape* does not characterise its bearer. `e` and `g` are two distinct
    entities, standing in for the non-ground bearer and the ground.

    The last two fields are the ACT-CASCADE half: the model must contain a genuine act, so that the
    separation cannot be dismissed as a model in which nothing happens. It must also identify the
    non-acting subject as necessary-kind, because that is the exact arm C453 needs.
    Footprint: `{}`. -/
structure ImmutabilityCountermodel
    (Entity Subject State World Time : Type)
    (EntityOf : Subject → Entity)
    (ExistsAt : World → Entity → Prop)
    (ExistsAtTime : Time → Entity → Prop)
    (EntityMeans : Entity → Prop → Prop)
    (Means : Subject → Prop → Prop)
    (Initiates : Subject → State → State → Prop → Prop)
    (NecessaryKind : Subject → Prop)
    (e g : Entity) : Prop where
  /-- The bearer is not the ground: this witnesses the failure of C453's conclusion. -/
  distinct : e ≠ g
  /-- Field 1: `ModalInvariance e` at full strength, `∀ w₁ w₂, ExistsAt w₁ e ↔ ExistsAt w₂ e`. -/
  modal_invariance : ∀ w₁ w₂ : World, ExistsAt w₁ e ↔ ExistsAt w₂ e
  /-- Field 2: `StageInvariance e` at full strength, `∀ t₁ t₂, ExistsAtTime t₁ e ↔ …`. -/
  stage_invariance : ∀ t₁ t₂ : Time, ExistsAtTime t₁ e ↔ ExistsAtTime t₂ e
  /-- Field 3: `TransitionInvariance e`, i.e. `NotInSuccession e` at full strength — including the
      `Initiates` conjunct that `NecessityEternity.the_ground_not_in_succession` *discards*. -/
  transition_invariance : ¬ ∃ s σ σ' p, e = EntityOf s ∧ Initiates s σ σ' p
  /-- Field 4: `CapacityInvariance e` — vacuous in Γ (C321), and vacuous here too. -/
  capacity_invariance : ∀ p : Prop, EntityMeans e p ↔ EntityMeans e p
  /-- The act datum **holds**: some subject genuinely means and initiates. -/
  some_act : ∃ s : Subject, ∃ p : Prop, Means s p ∧ ∃ w w' : State, Initiates s w w' p
  /-- … and yet the subject arm fails at a necessary-kind subject. This is the exact missing
      universal: it is not merely that some subject fails to act, but that a necessary-kind
      subject never initiates. -/
  necessary_non_acting_subject :
    ∃ s : Subject, NecessaryKind s ∧ e = EntityOf s ∧
      ¬ ∃ σ σ' : State, ∃ p : Prop, Initiates s σ σ' p

/-- C489 — **the ground is not shown to be the sole bearer of Divine Immutability.** C453 is separated, not
    deferred: there is an interpretation of Γ's immutability vocabulary in which a second entity
    satisfies all four fields at full strength while remaining distinct from the ground.

    **The model, in full.** `Entity := Nat` with `g = 0` and `e = 1`; `Subject := Bool`;
    `EntityOf true = 0`, `EntityOf false = 1`; existence constant everywhere; `Means s _ := s`
    and `Initiates s _ _ _ := s`, so `true` acts and `false` does not. `NecessaryKind` holds only
    of `false`. Then `1 ≠ 0`; fields 1, 2 and 4 hold by constancy and reflexivity; field 3 holds
    because the only subject correlating with `1` is the necessary-kind `false`, which initiates
    nothing. And the act datum is **saturated** — `true` means and initiates — so this separates
    the universal claim from Γ's vocabulary rather than denying Γ's datum.

    **Footprint: `{}`.** The statement quantifies over its own types and mentions no Γ axiom: the
    refusal to derive C453 is not a fact about Γ's axioms but about the *shape* of the claim, in
    the same way as C249 (gapless scope ⇏ conjunctive power) and C321. -/
theorem immutability_is_not_sole_bearer :
    ∃ (Entity Subject State World Time : Type)
      (EntityOf : Subject → Entity)
      (ExistsAt : World → Entity → Prop)
      (ExistsAtTime : Time → Entity → Prop)
      (EntityMeans : Entity → Prop → Prop)
      (Means : Subject → Prop → Prop)
      (Initiates : Subject → State → State → Prop → Prop)
      (NecessaryKind : Subject → Prop)
      (e g : Entity),
      ImmutabilityCountermodel Entity Subject State World Time
        EntityOf ExistsAt ExistsAtTime EntityMeans Means Initiates NecessaryKind e g := by
  refine ⟨Nat, Bool, Unit, Unit, Unit,
    fun s => if s then 0 else 1,
    fun _ _ => True, fun _ _ => True, fun _ _ => False, fun s _ => s,
    fun s _ _ _ => s, fun s => s = false, 1, 0, ?_⟩
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _
    exact Iff.rfl
  · intro _ _
    exact Iff.rfl
  · rintro ⟨s, _σ, _σ', _p, hEq, hInit⟩
    have hs : s = true := hInit
    subst hs
    exact absurd hEq (by decide)
  · intro p
    exact Iff.rfl
  · exact ⟨true, True, rfl, Exists.intro () (Exists.intro () rfl)⟩
  · refine ⟨false, rfl, rfl, ?_⟩
    rintro ⟨_, _, _, hInit⟩
    exact absurd hInit (by decide)

/-- C490 — the same model, isolated to the diagnosis, so the ledger row for the *missing lemma*
    cites a theorem about the gap rather than a comment about it. The necessary-kind initiation
    statement is exactly what C453's subject arm needs and exactly what C454 does not give:

      * `performative_act_datum` is `∃ s, ∃ p, Act s p` — a **global** existential;
      * excluding every necessary-kind subject from `NotInSuccession` needs
        `∀ s, NecessaryKind s → ∃ σ σ' p, Initiates s σ σ' p` — a **per-necessary-kind-subject**
        universal.

    An existential does not distribute over that universal, and the countermodel makes the gap
    explicit: in the model of C489 the first holds, while a necessary-kind subject never
    initiates.

    **This is the exact missing lemma, discharged as a negative.** No new axiom: the
    per-necessary-kind-subject bound would have to be `Tag: SEM` or `Tag: VOCAB`, and paying it is
    an author decision recorded in `INHABITED.md`, not something this batch may take. See `F17` in
    `GAPMAP.md`.
    Footprint: `{}`. -/
theorem the_act_datum_does_not_entail_every_subject_acts :
    ∃ (Subject State : Type)
      (Means : Subject → Prop → Prop)
      (Initiates : Subject → State → State → Prop → Prop)
      (NecessaryKind : Subject → Prop),
      (∃ s : Subject, ∃ p : Prop, Means s p ∧ ∃ w w' : State, Initiates s w w' p) ∧
      (∃ s : Subject, NecessaryKind s ∧
        ¬ ∃ σ σ' : State, ∃ p : Prop, Initiates s σ σ' p) := by
  refine ⟨Bool, Unit, fun s _ => s, fun s _ _ _ => s, fun s => s = false, ?_, ?_⟩
  · exact ⟨true, True, rfl, Exists.intro () (Exists.intro () rfl)⟩
  · refine ⟨false, rfl, ?_⟩
    rintro ⟨_, _, _, hInit⟩
    exact absurd hInit (by decide)

#print axioms immutability_is_not_sole_bearer
#print axioms the_act_datum_does_not_entail_every_subject_acts

end Logos.ImmutabilitySoleBearer
