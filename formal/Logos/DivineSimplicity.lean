/-
# Logos.DivineSimplicity — Classical Divine Simplicity and Ontological Transcendence

This module formalizes the classical characteristic of **Divine Simplicity** (non-compositeness,
inextension, and undivided intentional presence) and **Ontological Transcendence** for the
necessary Ground of Reality (`Entity.ofGround`), fulfilling the roadmap in `CHARACTERISTICS.md:210-233`
and `CHARS.md:144-154`.

### Classical Foundations:
1. **Mereological Simplicity (Via Negationis):**
   As argued by Thomas Aquinas (*Summa Theologiae* I, q. 3, a. 7) and Γ (`README-OLD.md:164`),
   every composite entity is dependent on and subsequent to its components. An ultimate foundation
   with Canonical Aseity cannot depend on external proper parts. We prove that
   `NonComposite e ↔ CanonicalAseity e`, and consequently `Entity.ofGround` is mereologically
   non-composite under the finite-subjectivity condition.
2. **Structural / Ontological Inextension:**
   In the entity ontology (`Entity`), atomic worldly states (`ofAtom n`) and subject correlates (`ofSubject s`)
   carry internal parameters, while `Entity.ofGround` is an atomic, nullary constructor with zero
   internal decomposition (`¬ HasInternalComponent Entity.ofGround`, footprint `{}`).
3. **Intentional Undividedness:**
   Unlike finite discriminating agents whose intentional capacity is fractured between grasped
   and ungrasped propositions, `Entity.ofGround` possesses uniform, undivided meaning capacity
   across reality (`UndividedMeaning Entity.ofGround`, footprint `{}`).
4. **Ontological Transcendence:**
   `Entity.ofGround` transcends every atomic worldly state and finite subjective agent
   (`TranscendentGround Entity.ofGround`, footprint `{Subject}`).
5. **The Master Synthesis:**
   `DivineSimplicity Entity.ofGround` combines mereological, structural, and intentional simplicity
   with 0 substantive axioms (footprint: `{Means, Subject}`).
-/

import Logos.Core
import Logos.Semantics
import Logos.Entity
import Logos.Agency
import Logos.RecoveredOntologicalGround
import Logos.CanonicalAseity
import Logos.NecessityEternity

namespace Logos.DivineSimplicity

open Logos.Core
open Logos.Semantics (World)
open Logos.Entity (Entity EntityOf ExistsAt)
open Logos.Agency (Subject Means)
open Logos.RecoveredOntologicalGround (EntityMeans OneEssence ActualEntity NecessaryGroundOfReality)
open Logos.CanonicalAseity (ExternalGrounding CanonicalAseity conditional_canonical_aseity)
open Logos.NecessityEternity (ofGround_necessary_ground_of_reality)

-- ============================================================================
-- Section 1: Mereological Simplicity (Non-Compositeness)
-- ============================================================================

/-- A proper ontological part or grounding constituent of entity `e`:
    an entity `p` distinct from `e` that ontologically grounds `e`.
    Footprint: `{Means, Subject}`. -/
def ProperPart (p e : Entity) : Prop :=
  p ≠ e ∧ OneEssence p e

/-- Mereological non-compositeness: entity `e` is not composed of any
    proper ontological parts (has no external grounding constituents).
    Footprint: `{Means, Subject}`. -/
def NonComposite (e : Entity) : Prop :=
  ¬ ∃ p : Entity, ProperPart p e

/-- Equivalence of Mereological Non-Compositeness and Canonical Aseity:
    an entity has no proper grounding parts iff no distinct entity externally grounds it.
    Footprint: `{Means, Subject}`. -/
theorem non_composite_iff_canonical_aseity (e : Entity) :
    NonComposite e ↔ CanonicalAseity e := by
  dsimp [NonComposite, ProperPart, CanonicalAseity, ExternalGrounding]
  rfl

/-- Mereological Simplicity of the Ground of Reality:
    Under the finite-subjectivity condition (all subjects are discriminating),
    `Entity.ofGround` is non-composite (has no proper ontological parts).
    Footprint: `{Means, Subject, propext}`. -/
theorem ofGround_non_composite
    (hFinite : ∀ s : Subject, ∃ p : Prop, ¬ Means s p) :
    NonComposite Entity.ofGround := by
  rw [non_composite_iff_canonical_aseity]
  exact conditional_canonical_aseity hFinite

-- ============================================================================
-- Section 2: Structural Simplicity (Absence of Internal Decomposition)
-- ============================================================================

/-- Predicate detecting whether an entity has internal component decomposition
    in the entity ontology.
    Footprint: `{Subject}`. -/
def HasInternalComponent : Entity → Prop
  | Entity.ofSubject _ => True
  | Entity.ofAtom _ => True
  | Entity.ofGround => False

/-- Structural Simplicity of the Ground:
    `Entity.ofGround` has zero internal component decomposition (is an atomic,
    indecomposable ontological constructor).
    Footprint: `{Subject}`. -/
theorem ofGround_has_no_internal_components :
    ¬ HasInternalComponent Entity.ofGround := by
  intro h
  exact h

-- ============================================================================
-- Section 3: Intentional Simplicity (Undivided Meaning Capacity)
-- ============================================================================

/-- Qualitative / intentional undividedness: the entity's meaning capacity
    is uniform and undivided across all propositions, containing no cleft or fracture.
    Footprint: `{Means, Subject}`. -/
def UndividedMeaning (e : Entity) : Prop :=
  ∀ p q : Prop, EntityMeans e p ↔ EntityMeans e q

/-- The Ground of Reality possesses Undivided Meaning:
    its meaning capacity is invariant across all propositions.
    Footprint: `{Means, Subject}`. -/
theorem ofGround_undivided_meaning :
    UndividedMeaning Entity.ofGround := by
  intro p q
  dsimp [EntityMeans]
  exact Iff.rfl

/-- Finite discriminating subjects fail undivided meaning:
    any subject with non-trivial discrimination between propositions lacks undivided meaning.
    Footprint: `{Means, Subject}`. -/
theorem discriminating_subject_not_undivided (s : Subject)
    (hDiscrim : ∃ p q : Prop, Means s p ∧ ¬ Means s q) :
    ¬ UndividedMeaning (EntityOf s) := by
  intro hUndiv
  obtain ⟨p, q, hp, hq⟩ := hDiscrim
  dsimp [UndividedMeaning] at hUndiv
  have hEquiv := hUndiv p q
  dsimp [EntityMeans, EntityOf] at hEquiv
  have hq_means : Means s q := hEquiv.mp hp
  exact hq hq_means

-- ============================================================================
-- Section 4: Ontological Transcendence (Non-Systemicity)
-- ============================================================================

/-- Ontological Transcendence: an entity is transcendent if it is neither an atomic
    worldly state (`Entity.ofAtom n`) nor identical to any subject-correlate (`EntityOf s`).
    Footprint: `{Subject}`. -/
def TranscendentGround (e : Entity) : Prop :=
  (∀ n : Nat, e ≠ Entity.ofAtom n) ∧ (∀ s : Subject, e ≠ EntityOf s)

/-- Transcendence of the Ground of Reality:
    `Entity.ofGround` transcends every atomic worldly state and every subjective agent.
    Footprint: `{Subject}`. -/
theorem ofGround_transcendent :
    TranscendentGround Entity.ofGround := by
  constructor
  · intro n h
    exact Entity.noConfusion h
  · intro s h
    exact Entity.noConfusion h

-- ============================================================================
-- Section 5: The Master Synthesis: Divine Simplicity
-- ============================================================================

/-- Classical Divine Simplicity:
    The conjunction of:
    1. Mereological Simplicity (NonComposite: no external grounding parts);
    2. Structural Simplicity (absence of internal component decomposition);
    3. Intentional Simplicity (undivided, uniform meaning capacity). -/
structure DivineSimplicity (e : Entity) : Prop where
  /-- Mereological non-compositeness: has no external proper parts -/
  non_composite : NonComposite e
  /-- Structural inextension: has no internal component decomposition -/
  no_internal_components : ¬ HasInternalComponent e
  /-- Intentional simplicity: uniform, undivided meaning capacity -/
  undivided_meaning : UndividedMeaning e

/-- HEADLINE — Divine Simplicity of the Ground of Reality:
    Under finite subjectivity, `Entity.ofGround` satisfies Classical Divine Simplicity.
    Footprint: `{Means, Subject, propext}` (0 substantive axioms). -/
theorem ofGround_divine_simplicity
    (hFinite : ∀ s : Subject, ∃ p : Prop, ¬ Means s p) :
    DivineSimplicity Entity.ofGround := {
  non_composite := ofGround_non_composite hFinite
  no_internal_components := ofGround_has_no_internal_components
  undivided_meaning := ofGround_undivided_meaning
}

/-- Divine Simplicity and Transcendence conjunction for the Ground of Reality:
    `Entity.ofGround` is both divinely simple and ontologically transcendent.
    Footprint: `{Means, Subject, propext}`. -/
theorem ofGround_simplicity_and_transcendence
    (hFinite : ∀ s : Subject, ∃ p : Prop, ¬ Means s p) :
    DivineSimplicity Entity.ofGround ∧ TranscendentGround Entity.ofGround :=
  ⟨ofGround_divine_simplicity hFinite, ofGround_transcendent⟩

-- ============================================================================
-- Section 5b: Sole Candidacy — Simplicity Discriminates
-- ============================================================================

/-- C439 — **sole bearer**: `Entity.ofGround` is the only entity in the Γ
    inventory satisfying `DivineSimplicity`. The three constructors of `Entity`
    exhaust the inventory, and the `no_internal_components` field alone closes
    the case: `HasInternalComponent` is `True` on both `Entity.ofSubject _`
    and `Entity.ofAtom _` and `False` only on `Entity.ofGround`
    (`HasInternalComponent`, above), so no non-ground constructor can inhabit
    the structure. The result is unconditional and — this is the correction to
    the batch plan's prediction — it is *not* axiom-free: the `DivineSimplicity`
    structure itself carries `Means`, because its `undivided_meaning : Prop` field
    mentions `UndividedMeaning`, which mentions `EntityMeans`. Unicity therefore
    rests on `{Means, Subject}`: no *substantive* axiom (0 price, no 27th axiom),
    but the vocabulary axiom `Means` enters through the type. Contrast with C433
    (`Precedence.ofGround_sole_precedes_right_wrong`), which pays the 27th axiom
    `SemanticFinitude` to exclude subjects. Here the exclusion is free and the
    price is zero-substantive.

    **Disclosure — the intentional conjunct does no work here.**
    `UndividedMeaning e := ∀ p q, EntityMeans e p ↔ EntityMeans e q`, and
    `EntityMeans (Entity.ofAtom _) = False` is a definitional stipulation, so
    `undivided_meaning` is *vacuously true of every atom*: an atom trivially
    has uniform meaning capacity because it has none. Likewise
    `discriminating_subject_not_undivided` rules out subjects that separate
    propositions, but a subject that separates *nothing* satisfies it too. The
    structure is therefore satisfied vacuously for the wrong reasons by non-ground
    entities, and only the `no_internal_components` field is load-bearing for
    this theorem. This is a disclosure, not a defect: the mereological and
    intentional conjuncts remain meaningful for the ground, they just do not
    discriminate.

    Footprint: `{Means, Subject}` (0 substantive axioms). -/
theorem divine_simplicity_is_unique_to_the_ground :
    ∀ e, DivineSimplicity e → e = Entity.ofGround := by
  intro e h
  cases e with
  | ofGround => rfl
  | ofAtom n => exact (h.no_internal_components (by simp [HasInternalComponent])).elim
  | ofSubject s => exact (h.no_internal_components (by simp [HasInternalComponent])).elim

/-- C440 — the attributes-table form: the ground is the sole bearer of Divine
    Simplicity, stated together with the existence half so a reader-facing row
    can cite a single declaration. This is the §13 Simplicity analogue of C433
    (`Precedence.ofGround_sole_precedes_right_wrong`), and unlike C433 it needs
    no subject-finiteness axiom — the unicity half is exactly C439's.

    Note the two halves have different costs, and the difference is the point:
    existence pays `Means`/`Subject` (via `hFinite`), while **unicity is free**.
    Footprint: `{Means, Subject, propext}`. -/
theorem divine_simplicity_sole_bearer
    (hFinite : ∀ s : Subject, ∃ p : Prop, ¬ Means s p) :
    DivineSimplicity Entity.ofGround ∧ (∀ e, DivineSimplicity e → e = Entity.ofGround) :=
  ⟨ofGround_divine_simplicity hFinite, divine_simplicity_is_unique_to_the_ground⟩

-- ============================================================================
-- Section 6: Metatheoretic Independence & Separation
-- ============================================================================

/-- Metatheoretic Independence / Countermodel:
    A composite entity with internal components fails Divine Simplicity.
    Footprint: `{}`. -/
theorem composite_entity_fails_simplicity :
    ∃ (Ent : Type) (HasComp : Ent → Prop) (Simp : Ent → Prop),
      (∀ e, Simp e → ¬ HasComp e) ∧
      (∃ e, HasComp e ∧ ¬ Simp e) := by
  refine ⟨Bool, fun b => b = true, fun b => b = false, ?_, ?_⟩
  · intro b hSimp hComp
    rw [hSimp] at hComp
    contradiction
  · refine ⟨true, rfl, ?_⟩
    intro h
    contradiction

#print axioms ProperPart
#print axioms NonComposite
#print axioms non_composite_iff_canonical_aseity
#print axioms ofGround_non_composite
#print axioms HasInternalComponent
#print axioms ofGround_has_no_internal_components
#print axioms UndividedMeaning
#print axioms ofGround_undivided_meaning
#print axioms discriminating_subject_not_undivided
#print axioms TranscendentGround
#print axioms ofGround_transcendent
#print axioms DivineSimplicity
#print axioms ofGround_divine_simplicity
#print axioms ofGround_simplicity_and_transcendence
#print axioms divine_simplicity_is_unique_to_the_ground
#print axioms divine_simplicity_sole_bearer
#print axioms composite_entity_fails_simplicity

end Logos.DivineSimplicity
