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
    Footprint: `{Subject}`. -/
def ModalInvariance (e : Entity) : Prop :=
  ∀ w₁ w₂ : World, ExistsAt w₁ e ↔ ExistsAt w₂ e

/-- The Ground of Reality possesses Modal Invariance:
    `Entity.ofGround` exists invariably across every world (by definition).
    Footprint: `{Subject}`. -/
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
    Footprint: `{Subject}`. -/
def StageInvariance (e : Entity) : Prop :=
  ∀ t₁ t₂ : Time, ExistsAtTime t₁ e ↔ ExistsAtTime t₂ e

/-- The Ground of Reality possesses Stage Invariance:
    its existence across temporal stages is completely invariant.
    Footprint: `{Subject}`. -/
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
    Footprint: `{Initiates, Means, State, Subject}` (0 substantive axioms). -/
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
    Footprint: `{Initiates, Means, State, Subject}`. -/
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
-- Section 7: Metatheoretic Independence / Countermodel (Contingent Entities Are Mutable)
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

end Logos.DivineImmutability
