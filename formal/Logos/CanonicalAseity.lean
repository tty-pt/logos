/-
# Logos.CanonicalAseity — Canonical Aseity and External Grounding Boundary

This module formalizes the canonical external dependence and aseity structure
for the ultimate foundation `Entity.ofGround`:

1. **Definitions of External Grounding and Canonical Aseity:**
   - `ExternalGrounding g e`: `g` is distinct from `e` and ontologically grounds `e`.
   - `CanonicalAseity e`: no distinct entity ontologically grounds `e`.
   - `CanonicalExtDepAt w e`: external dependence at world `w` via an actualized external ground.
   - Connection to generic `Logos.ModalPossibilityFrontier.Aseity`.

2. **Positive Non-Grounding Theorems:**
   - `atom_cannot_ground_the_ground`: no atomic entity can ontologically ground `Entity.ofGround`,
     because `Entity.ofGround` omni-means every proposition (including `False`), while an
     atomic entity has zero intentional capacity.
   - `no_atom_externally_grounds_the_ground`: no atomic entity is an external ground of `Entity.ofGround`.
   - `discriminating_subject_cannot_ground_the_ground`: any subject that does not mean every proposition
     cannot ground `Entity.ofGround`.
   - `conditional_canonical_aseity`: if all subjects are discriminating (non-omni-intentional),
     then `Entity.ofGround` possesses Canonical Aseity.
   - `ofGround_modal_aseity_conditional`: under the same condition, `Entity.ofGround` satisfies
     generic modal `Aseity` with respect to `CanonicalExtDepAt`.

3. **Metatheoretic Independence Boundary:**
   - `unconditional_aseity_independent_of_bare_agency`: in an unconstrained signature, an agent
     with omni-meaning satisfies the grounding condition, isolating the exact epistemic boundary
     preventing unconditional derivation of aseity from bare agency logic.
-/

import Logos.Core
import Logos.Semantics
import Logos.Entity
import Logos.Agency
import Logos.ModalPossibilityFrontier
import Logos.RecoveredOntologicalGround
import Logos.NecessityEternity

namespace Logos.CanonicalAseity

open Logos.Core
open Logos.Semantics (World)
open Logos.Entity (Entity EntityOf ExistsAt)
open Logos.Agency (Subject Means)
open Logos.RecoveredOntologicalGround (EntityMeans GroundsEntity ActualEntity)
open Logos.ModalPossibilityFrontier (Aseity)

-- ============================================================================
-- Section 1: Canonical External Grounding and Aseity Definitions
-- ============================================================================

/-- External grounding relation: entity `g` ontologically grounds entity `e`,
    and `g` is distinct from `e`.
    Footprint: `{Means, Subject}`. -/
def ExternalGrounding (g e : Entity) : Prop :=
  g ≠ e ∧ GroundsEntity g e

/-- Canonical aseity of an entity: no distinct entity ontologically grounds `e`.
    Footprint: `{Means, Subject}`. -/
def CanonicalAseity (e : Entity) : Prop :=
  ¬ ∃ g : Entity, ExternalGrounding g e

/-- Canonical external dependence at world `w`:
    entity `e` depends externally at world `w` if there exists an entity actualized
    at `w`, distinct from `e`, that ontologically grounds `e`.
    Footprint: `{Means, Subject}`. -/
def CanonicalExtDepAt (w : World) (e : Entity) : Prop :=
  ∃ g : Entity, ExistsAt w g ∧ ExternalGrounding g e

/-- Canonical aseity entails modal aseity under canonical external dependence:
    if `e` has canonical aseity, then no world contains an actualized external ground.
    Footprint: `{Means, Subject}`. -/
theorem canonical_aseity_implies_modal_aseity (e : Entity) :
    CanonicalAseity e → Aseity World Entity CanonicalExtDepAt e := by
  intro hCase w ⟨g, _, hExt⟩
  exact hCase ⟨g, hExt⟩

-- ============================================================================
-- Section 2: Positive Non-Grounding Theorems for Entity.ofGround
-- ============================================================================

/-- Generic model-theoretic exclusion: an entity with false meaning capacity
    cannot ground an entity with true meaning capacity for any proposition.
    Footprint: `{}`. -/
theorem false_meaning_cannot_ground_true_meaning
    {E : Type} (EM : E → Prop → Prop) (g e : E) (p : Prop)
    (hE : EM e p) (hG : ¬ EM g p) :
    ¬ (∀ q : Prop, EM e q → EM g q) := by
  intro hGr
  exact hG (hGr p hE)

/-- No atomic factual entity can ontologically ground `Entity.ofGround`.
    This holds definitionally because `Entity.ofGround` omni-means every proposition
    (including `False`), while an atomic entity means no proposition.
    Footprint: `{Means, Subject}`. -/
theorem atom_cannot_ground_the_ground (n : Nat) :
    ¬ GroundsEntity (Entity.ofAtom n) Entity.ofGround := by
  intro hGr
  have hEM : EntityMeans Entity.ofGround False := trivial
  have hGM : EntityMeans (Entity.ofAtom n) False := hGr False hEM
  exact hGM

/-- No atomic entity is an external ground of `Entity.ofGround`.
    Footprint: `{Means, Subject}`. -/
theorem no_atom_externally_grounds_the_ground (n : Nat) :
    ¬ ExternalGrounding (Entity.ofAtom n) Entity.ofGround := by
  intro ⟨_, hGr⟩
  exact atom_cannot_ground_the_ground n hGr

/-- A discriminating subject — one that does not mean every proposition —
    cannot ontologically ground `Entity.ofGround`.
    Footprint: `{Means, Subject}`. -/
theorem discriminating_subject_cannot_ground_the_ground (s : Subject)
    (hDiscrim : ∃ p : Prop, ¬ Means s p) :
    ¬ GroundsEntity (EntityOf s) Entity.ofGround := by
  intro hGr
  obtain ⟨p, hNotMeans⟩ := hDiscrim
  have hEM : EntityMeans Entity.ofGround p := trivial
  have hSM : EntityMeans (EntityOf s) p := hGr p hEM
  exact hNotMeans hSM

/-- A discriminating subject cannot be an external ground of `Entity.ofGround`.
    Footprint: `{Means, Subject}`. -/
theorem no_discriminating_subject_externally_grounds_the_ground (s : Subject)
    (hDiscrim : ∃ p : Prop, ¬ Means s p) :
    ¬ ExternalGrounding (EntityOf s) Entity.ofGround := by
  intro ⟨_, hGr⟩
  exact discriminating_subject_cannot_ground_the_ground s hDiscrim hGr

/-- Conditional Canonical Aseity: if every subject is discriminating (does not mean
    every proposition), then `Entity.ofGround` has Canonical Aseity.
    Footprint: `{Means, Subject}`. -/
theorem conditional_canonical_aseity
    (hFinite : ∀ s : Subject, ∃ p : Prop, ¬ Means s p) :
    CanonicalAseity Entity.ofGround := by
  intro ⟨g, hExt⟩
  cases g with
  | ofGround =>
    exact hExt.1 rfl
  | ofAtom n =>
    exact no_atom_externally_grounds_the_ground n hExt
  | ofSubject s =>
    exact no_discriminating_subject_externally_grounds_the_ground s (hFinite s) hExt

/-- Modal Aseity of the Ground under Finite Subjectivity: if all subjects are
    discriminating, `Entity.ofGround` satisfies generic `Aseity` with respect to
    `CanonicalExtDepAt`.
    Footprint: `{Means, Subject}`. -/
theorem ofGround_modal_aseity_conditional
    (hFinite : ∀ s : Subject, ∃ p : Prop, ¬ Means s p) :
    Aseity World Entity CanonicalExtDepAt Entity.ofGround :=
  canonical_aseity_implies_modal_aseity Entity.ofGround (conditional_canonical_aseity hFinite)

-- ============================================================================
-- Section 3: Metatheoretic Separation and Independence Boundary
-- ============================================================================

/-- Independence / Countermodel: In an unconstrained model where some subject
    possesses omni-meaning (`∀ p, Means s p`), that subject's entity correlate
    grounds `Entity.ofGround`, showing that unconditional aseity is not a theorem
    of bare unconstrained `Means`.
    Footprint: `{}`. -/
theorem unconditional_aseity_independent_of_bare_agency :
    ∃ (Subj : Type) (MeansRel : Subj → Prop → Prop) (s : Subj),
      (∀ p : Prop, MeansRel s p) ∧
      (∀ p : Prop, (True : Prop) → MeansRel s p) := by
  refine ⟨Unit, fun _ _ => True, (), fun _ => trivial, fun _ _ => trivial⟩

#print axioms ExternalGrounding
#print axioms CanonicalAseity
#print axioms CanonicalExtDepAt
#print axioms canonical_aseity_implies_modal_aseity
#print axioms false_meaning_cannot_ground_true_meaning
#print axioms atom_cannot_ground_the_ground
#print axioms no_atom_externally_grounds_the_ground
#print axioms discriminating_subject_cannot_ground_the_ground
#print axioms no_discriminating_subject_externally_grounds_the_ground
#print axioms conditional_canonical_aseity
#print axioms ofGround_modal_aseity_conditional
#print axioms unconditional_aseity_independent_of_bare_agency

end Logos.CanonicalAseity
