/-
# Logos.DivineImmutability — Classical Divine Immutability and Ontological Invariance

This module formalizes the classical characteristic of **Divine Immutability**
(*De immutabilitate Dei*, Thomas Aquinas *Summa Theologiae* I, q. 9) for the necessary
Ground of Reality (`Entity.ofGround`), completing the classical quartet of incommunicable
attributes alongside **Aseity** (`Logos.CanonicalAseity`), **Simplicity** (`Logos.DivineSimplicity`),
and **Eternity/Atemporality** (`Logos.NecessityEternity`).

### Classical Foundations:
1. **Modal Invariance (Immutability across Possible Worlds):**
   The existence of `Entity.ofGround` is invariant across every possible world
   (`ModalInvariance Entity.ofGround`, footprint `{Subject}`). Unlike contingent entities
   whose actuality varies across modal space, the ground's existence is world-rigid.
2. **Temporal / Stage Invariance (Immutability across Time):**
   The ground does not begin, end, or fluctuate across temporal stages
   (`StageInvariance Entity.ofGround`, footprint `{Subject}`).
3. **Transition Invariance (Inalterability under Becoming):**
   The ground is strictly outside all succession and state transitions
   (`TransitionInvariance Entity.ofGround`, footprint `{Initiates, State, Subject}`).
   No finite agent or initiation event can bring it about, modify it, or terminate it.
4. **Capacity Invariance (Unchanging Meaning Capacity):**
   The ground's intentional capacity across reality is immutable and uniform
   (`CapacityInvariance Entity.ofGround`, footprint `{Means, Subject}`).
   **Vacuity disclosure (C321):** this fourth field is a tautology, satisfied by *every*
   entity, because `EntityMeans` takes no world argument — see
   `capacity_invariance_holds_for_every_entity`. The other three fields genuinely discriminate
   and each has a `{}` countermodel. Disclosure only: item 5 below remains `PROVEN`.
5. **The Master Synthesis:**
   `DivineImmutability Entity.ofGround` conjoins modal, temporal, process, and capacity
   invariance with 0 substantive axioms (footprint: `{Initiates, Means, State, Subject}`).
6. **The Thomistic Connection:**
   Following Aquinas (*ST* I, q. 9, a. 1–2), an entity that is simple, necessary, atemporal,
   and outside succession is altogether immutable.

### Honest Boundary:
Establishing modal, stage, process, and intentional invariance of `Entity.ofGround` within
the $\Gamma$ formal framework does not purport to prove psychological impassibility or
constrain personal intentional address beyond what the formal model specifies.
-/

import Logos.Core
import Logos.Semantics
import Logos.Entity
import Logos.Agency
import Logos.RecoveredOntologicalGround
import Logos.NecessityEternity
import Logos.DivineSimplicity

namespace Logos.DivineImmutability

open Logos.Core
open Logos.Semantics (World)
open Logos.Entity (Entity EntityOf ExistsAt)
open Logos.Agency (Subject State Initiates)
open Logos.RecoveredOntologicalGround (EntityMeans ActualEntity)
open Logos.NecessityEternity (Time stageOf ExistsAtTime Everlasting Atemporal NotInSuccession the_ground_atemporal the_ground_not_in_succession ofGround_necessary)
open Logos.DivineSimplicity (DivineSimplicity ofGround_divine_simplicity ofGround_undivided_meaning)

-- ============================================================================
-- Section 1: Modal Invariance (Immutability across Possible Worlds)
-- ============================================================================

/-- Modal Invariance: an entity's existence is invariant across all possible worlds.
    It does not exist contingently in some worlds while failing to exist in others.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
def ModalInvariance (e : Entity) : Prop :=
  ∀ w₁ w₂ : World, ExistsAt w₁ e ↔ ExistsAt w₂ e

/-- The Ground of Reality possesses Modal Invariance:
    `Entity.ofGround` exists invariably across every world (by definition).
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem ofGround_modal_invariance :
    ModalInvariance Entity.ofGround := by
  intro w₁ w₂
  dsimp [ExistsAt, Logos.Entity.EntityExistsAt]
  exact Iff.rfl

-- ============================================================================
-- Section 2: Temporal / Stage Invariance (Immutability across Time)
-- ============================================================================

/-- Temporal / Stage Invariance: an entity's existence does not fluctuate across temporal stages.
    It exists uniformly at all times without beginning, ending, or temporal alteration.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
def StageInvariance (e : Entity) : Prop :=
  ∀ t₁ t₂ : Time, ExistsAtTime t₁ e ↔ ExistsAtTime t₂ e

/-- The Ground of Reality possesses Stage Invariance:
    its existence across temporal stages is completely invariant.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem ofGround_stage_invariance :
    StageInvariance Entity.ofGround :=
  the_ground_atemporal

-- ============================================================================
-- Section 3: Transition Invariance (Inalterability under Becoming)
-- ============================================================================

/-- Process & Transition Invariance: the entity is outside all succession and becoming.
    No subjective agency can bring it into existence, modify it, or transition it.
    Footprint: `{Initiates, State, Subject}`. -/
def TransitionInvariance (e : Entity) : Prop :=
  NotInSuccession e

/-- The Ground of Reality possesses Transition Invariance:
    `Entity.ofGround` is outside every initiation-becoming.
    Footprint: `{Initiates, State, Subject}`. -/
theorem ofGround_transition_invariance :
    TransitionInvariance Entity.ofGround :=
  the_ground_not_in_succession

-- ============================================================================
-- Section 4: Meaning & Capacity Invariance (Unchanging Intentional Presence)
-- ============================================================================

/-- Intentional Capacity Invariance: the entity's meaning capacity across reality
    is constant and does not vary across worlds, times, or contexts.

    **Vacuity disclosure (C321).** As stated this predicate is a tautology, not a
    discrimination. `EntityMeans` is `EntityMeans (e : Entity) (p : Prop) : Prop`
    (`RecoveredOntologicalGround.lean:46`) and takes **no world argument at all**, so the two
    worlds quantified below are bound and never mentioned in the body, and `P ↔ P` holds for
    any `p`. Consequently `CapacityInvariance` holds for *every* entity — see
    `capacity_invariance_holds_for_every_entity`. The substantive reading ("meaning capacity is
    constant *across worlds*") is not expressible in the present vocabulary, which has no
    world-indexed meaning relation; that is recorded as blocked frontier F16. This is
    disclosure, not demotion: `ofGround_divine_immutability` remains `PROVEN`.

    Footprint: `{Means, Subject}`. -/
def CapacityInvariance (e : Entity) : Prop :=
  ∀ p : Prop, ∀ _w₁ _w₂ : World, EntityMeans e p ↔ EntityMeans e p

/-- The Ground of Reality possesses Capacity Invariance:
    its intentional grounding capacity is immutable across reality.
    Footprint: `{Means, Subject}`. -/
theorem ofGround_capacity_invariance :
    CapacityInvariance Entity.ofGround := by
  intro p _w₁ _w₂
  exact Iff.rfl

/-- COUNTERMODEL (C321) — Intentional Capacity Invariance discriminates nothing: it is
    satisfied by every entity whatsoever, not merely by the ground, so it cannot distinguish
    the ground from a subject or an atom.

    The reason is in the vocabulary, not the proof. `EntityMeans` takes no world argument
    (`RecoveredOntologicalGround.lean:46`), so the two worlds in `CapacityInvariance` are bound
    and unused, and the body reduces to `EntityMeans e p ↔ EntityMeans e p` — discharged by
    `Iff.rfl`, the same two lines as `ofGround_capacity_invariance` (`:132-135`).

    The asymmetry that makes this worth recording: all three sibling fields of
    `DivineImmutability` genuinely quantify and do discriminate — `ModalInvariance` over
    `w₁ w₂ : World` via `ExistsAt`, `StageInvariance` over `t₁ t₂ : Time` via `ExistsAtTime`,
    `TransitionInvariance` as the real predicate `NotInSuccession e` — and each has a `{}`
    non-triviality countermodel on record (C197 for modal/stage invariance, alongside C192
    simplicity, C202 omnipresence, C214 pure actuality). This field has none, because there is
    nothing in it to refute. Generalising the existing ground-specific theorem to all entities
    is the honest form of the disclosure: the ledger previously stated the property only where
    it could not fail, which read as if it carried weight.

    Footprint: `{Means, Subject}` — the *statement* mentions `EntityMeans`, whose body mentions
    `Means` and `Subject`, though the proof uses no axiom. Same reason
    `FoundationalUnicity.groundsEntity_reflexive` is not `{}`; see the `Entity`-layer floor. -/
theorem capacity_invariance_holds_for_every_entity (e : Entity) : CapacityInvariance e := by
  intro p _w₁ _w₂
  exact Iff.rfl

-- ============================================================================
-- Section 5: The Master Synthesis: Classical Divine Immutability
-- ============================================================================

/-- Classical Divine Immutability:
    The conjunction of:
    1. Modal Invariance (unchanging existence across all possible worlds);
    2. Temporal Stage Invariance (unchanging existence across all temporal stages);
    3. Transition Invariance (outside all initiation and state-becoming);
    4. Capacity Invariance (uniform, unchanging intentional presence). -/
structure DivineImmutability (e : Entity) : Prop where
  /-- Modal unchangeability: existence is invariant across all worlds -/
  modal_invariance : ModalInvariance e
  /-- Temporal unchangeability: existence is invariant across all temporal stages -/
  stage_invariance : StageInvariance e
  /-- Transition unchangeability: not subject to initiation or state transition -/
  transition_invariance : TransitionInvariance e
  /-- Intentional capacity unchangeability: unchanging meaning capacity -/
  capacity_invariance : CapacityInvariance e

/-- HEADLINE — Divine Immutability of the Ground of Reality:
    `Entity.ofGround` satisfies Classical Divine Immutability across worlds, time,
    processes, and intentional capacities.
    Footprint: `{Initiates, Means, NecessarySubjectKind, State, Subject}` (0 substantive axioms). -/
theorem ofGround_divine_immutability :
    DivineImmutability Entity.ofGround := {
  modal_invariance := ofGround_modal_invariance
  stage_invariance := ofGround_stage_invariance
  transition_invariance := ofGround_transition_invariance
  capacity_invariance := ofGround_capacity_invariance
}

-- ============================================================================
-- Section 6: Thomistic Connection (Necessity & Simplicity Entail Immutability)
-- ============================================================================

/-- The Thomistic Principle of Immutability:
    Any entity that is necessary, atemporal, outside succession, and possesses
    capacity invariance satisfies Divine Immutability.
    Footprint: `{Initiates, Means, NecessarySubjectKind, State, Subject}`. -/
theorem necessity_and_atemporality_yield_immutability (e : Entity)
    (hNec : ∀ w₁ w₂ : World, ExistsAt w₁ e ↔ ExistsAt w₂ e)
    (hAtemp : Atemporal e)
    (hSucc : NotInSuccession e)
    (hCap : CapacityInvariance e) :
    DivineImmutability e := {
  modal_invariance := hNec
  stage_invariance := hAtemp
  transition_invariance := hSucc
  capacity_invariance := hCap
}

-- ============================================================================
-- Section 7: F16 priced — the wall is vocabulary, not a missing proof
--
-- The F16 frontier row (GAPMAP.md) says the substantive reading of Immutability
-- ("the ground's meaning capacity cannot vary from world to world") cannot even be
-- *stated*, because `EntityMeans : Entity → Prop → Prop` has no `World` argument.
-- That diagnosis is right, and this section makes the diagnosis itself a theorem:
-- no relation that agrees with `EntityMeans` at every world can exhibit
-- world-varying capacity. So F16's variation, if it is to exist, must come from
-- NEW VOCABULARY — and new vocabulary is the author's decision at `Tag: SEM` at
-- minimum, not a lemma this batch may supply.
--
-- F16 therefore STAYS BLOCKED. What changes is that its price is now a `{}`-class
-- result rather than a sentence in a ledger cell. The plan of record is `PLAN2.md`
-- (and, for the audit trail, `investigations/kernel-audit.md`); there is no
-- root `AUDIT.md` in this repository and never has been.
-- ============================================================================

/-- **No world-indexed extension of Γ's meaning relation can vary.**
    Suppose `R : Entity → World → Prop → Prop` agrees with `EntityMeans` at every
    entity, world and proposition. Then capacity is a function of the entity alone,
    and `R e w₁ p ↔ R e w₂ p` for any two worlds — world-variation is impossible.
    Hence a world-relative meaning relation, were one added, could not be an
    extension of `EntityMeans`, and the substantive F16 reading has to be priced on
    new vocabulary rather than proved from the present one.

    This is the machine-checked form of F16's stated reason. It is *not* a proof of
    F16 and must not be read as one: F16 stays BLOCKED, and what is proved here is
    the stronger, sharper statement that the blocking is forced.
    Footprint: `{Means, Subject}`. -/
theorem no_world_indexed_extension_of_meaning_can_vary :
    ¬ ∃ (R : Entity → World → Prop → Prop),
        (∀ e : Entity, ∀ w : World, ∀ p : Prop, R e w p ↔ EntityMeans e p) ∧
        (∃ e : Entity, ∃ w₁ w₂ : World, ∃ p : Prop,
            R e w₁ p ∧ ¬ R e w₂ p) := by
  rintro ⟨R, hExt, ⟨e, w₁, w₂, p, h₁p, h₂neg⟩⟩
  exact h₂neg (hExt e w₂ p |>.mpr (hExt e w₁ p |>.mp h₁p))

/-- **The constructive half: any extension of `EntityMeans` IS world-constant.**
    The positive content of the previous row, stated so that the ledger can point
    at the invariance rather than only at its impossibility: if `R` agrees with
    `EntityMeans` at every world, then `R e w₁ p ↔ R e w₂ p` for any two worlds.

    Note what this is *not*: it is not a claim that the ground's meaning cannot
    change, because there is no world-indexed meaning in Γ to change. It is the
    statement that any future world-indexed relation which *extends* the present one
    would be world-constant, which is precisely why F16's variation would need a
    relation that does not extend it. C321
    (`capacity_invariance_holds_for_every_entity`) is the same fact about
    `CapacityInvariance`; this row is its conditional form.
    Footprint: `{Means, Subject}`. -/
theorem world_indexed_extension_of_meaning_is_world_constant
    (R : Entity → World → Prop → Prop)
    (hExt : ∀ e : Entity, ∀ w : World, ∀ p : Prop, R e w p ↔ EntityMeans e p)
    (e : Entity) (w₁ w₂ : World) (p : Prop) : R e w₁ p ↔ R e w₂ p :=
  (hExt e w₁ p).trans (hExt e w₂ p).symm

-- ============================================================================
-- Section 8: Metatheoretic Independence / Countermodel (Contingent Entities Are Mutable)
-- ============================================================================

/-- Metatheoretic Independence / Countermodel:
    Contingent entities are mutable (their existence varies across worlds),
    confirming that Divine Immutability is a non-trivial, discriminating property.
    Footprint: `{}`. -/
theorem contingent_entity_fails_immutability :
    ∃ (Ent World : Type) (ExistsAtRel : World → Ent → Prop) (e : Ent),
      ¬ (∀ w₁ w₂ : World, ExistsAtRel w₁ e ↔ ExistsAtRel w₂ e) := by
  refine ⟨Bool, Bool, fun w e => w = e, true, ?_⟩
  intro hInv
  have h := (hInv true false).mp rfl
  contradiction

#print axioms ModalInvariance
#print axioms ofGround_modal_invariance
#print axioms StageInvariance
#print axioms ofGround_stage_invariance
#print axioms TransitionInvariance
#print axioms ofGround_transition_invariance
#print axioms CapacityInvariance
#print axioms ofGround_capacity_invariance
#print axioms DivineImmutability
#print axioms ofGround_divine_immutability
#print axioms necessity_and_atemporality_yield_immutability
#print axioms contingent_entity_fails_immutability
#print axioms no_world_indexed_extension_of_meaning_can_vary
#print axioms world_indexed_extension_of_meaning_is_world_constant

end Logos.DivineImmutability
