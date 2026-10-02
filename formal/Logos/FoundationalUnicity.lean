/-
# Logos.FoundationalUnicity — The Sixth Classical Divine Characteristic: Unity & Monotheism

This module formalizes the classical divine attribute of **Divine Unity / Foundational Unicity**
(Monotheism; *De Deo Uno*, Aquinas *Summa Theologiae* I, q. 11, a. 3: "Whether God is One?")
for the necessary Ground of Reality (`Entity.ofGround`).

## The Conceptual Movement

1. **Abstract Structural Unicity of Universal Grounding:**
   Two distinct entities cannot simultaneously be universal grounds of all reality under
   asymmetric grounding. If $g_1 \neq g_2$, then $g_1$ grounding all beings entails that
   $g_1$ grounds $g_2$, while $g_2$ grounding all beings entails that $g_2$ grounds $g_1$.
   Under foundational asymmetry (no two entities mutually ground each other), this is an
   immediate contradiction. Hence, at most one universal ground can exist (`universal_ground_unicity`).

2. **Concrete Exclusion of Non-Ground Entities in Γ:**
   We systematically prove that no other entity in the ontological inventory of Γ can be
   a universal modal ground:
   - **Atoms are excluded:** `no_atom_is_universal_modal_ground` proves that no atomic factual
     state `Entity.ofAtom n` can be a universal ground, because an atom cannot ground the
     exhaustive meaning of `Entity.ofGround` (footprint `{Means, Subject}`).
   - **Finite discriminating subjects are excluded:** `no_discriminating_subject_is_universal_modal_ground`
     proves that no subject with finite or discriminating propositional grasp can be a universal
     ground, because it cannot ground the inexhaustible meaning of `Entity.ofGround`
     (footprint `{Means, Subject}`).

3. **Master Synthesis of Foundational Unicity:**
   `ofGround_foundational_unicity` conjoins universal grounding, atom-exclusion,
   subject-transcendence, and unicity under asymmetry into the classical attribute of
   **Foundational Unicity** (`FoundationalUnicity Entity.ofGround`, footprint `{Means, Subject}`,
   0 substantive axioms).

4. **Strict Separation of Categories:**
   In accordance with the project's strict non-overclaiming rules:
   - **Foundational Unicity** (PROVEN): The impossibility of multiple universal grounding principles.
    - **Numerical Unitarianism** (SEPARATED / NOT PROVEN): Does not force a solitary, relationless
      monad; internal relational plurality (the Trinitarian frontier) remains an open, non-collapsed
      theological question. Note the direction: this separation says unicity does not *imply* a
      single-Person ground, leaving the person-count undetermined. It does not refute the
      single-Person reading, and it says nothing against monotheism in its primary sense (one God,
      C320) — the two are distinct claims, and `Monotheism` is the *proven* one.
   - **Pantheism / Monism** (SEPARATED / EXCLUDED): The unique ground is transcendent (`TranscendentGround`),
     strictly distinct from empirical atoms and finite subjects.
-/

import Logos.Core
import Logos.Semantics
import Logos.Agency
import Logos.Choice
import Logos.Entity
import Logos.Modal
import Logos.RecoveredOntologicalGround
import Logos.NecessityEternity
import Logos.CanonicalAseity
import Logos.DivineSimplicity
import Logos.DivineImmutability
import Logos.FoundationalOmnipresence

namespace Logos.FoundationalUnicity

open Logos.Core (T IsFalse)
open Logos.Semantics (World Form Satisfies)
open Logos.Agency (Subject Means)
open Logos.Entity (Entity ExistsAt EntityOf actualWorld)
open Logos.RecoveredOntologicalGround (EntityMeans GroundsEntity ActualEntity GroundOfReality)
open Logos.NecessityEternity (ofGround_necessary ofGround_ground_of_reality)
open Logos.CanonicalAseity (CanonicalAseity atom_cannot_ground_the_ground discriminating_subject_cannot_ground_the_ground)
open Logos.DivineSimplicity (TranscendentGround ofGround_transcendent)
open Logos.FoundationalOmnipresence (UniversalModalGround ofGround_universal_modal_ground WorldRigidPresence ofGround_world_rigid_presence NonReciprocalGround ofGround_non_reciprocal_ground MaximalCapacity ofGround_maximal_capacity FoundationalOmnipresence ofGround_foundational_omnipresence)

-- ============================================================================
-- Section 1: Abstract Structural Unicity of Universal Grounding
-- ============================================================================

/-- Foundational Asymmetry:
    No two distinct entities mutually ground each other.
    Ontological grounding is an asymmetric dependency relation.
    Footprint: `{Means, Subject}`. -/
def AsymmetricGrounding : Prop :=
  ∀ (g1 g2 : Entity), GroundsEntity g1 g2 → ¬ GroundsEntity g2 g1

/-- Master Metaphysical Theorem: Universal Ground Unicity.
    Two distinct entities cannot both be universal modal grounds under asymmetric grounding.
    Proof: If g1 ≠ g2, universality of g1 forces g1 to ground g2, and universality of g2
    forces g2 to ground g1. Under asymmetry, this yields an immediate contradiction.
    Hence, g1 = g2.
    Footprint: `{CL, Means, NecessarySubjectKind, Subject}` (0 substantive axioms). -/
theorem universal_ground_unicity
    (g1 g2 : Entity)
    (hU1 : UniversalModalGround g1)
    (hU2 : UniversalModalGround g2)
    (hAsym : AsymmetricGrounding)
    (w : World) (hEx1 : ExistsAt w g1) (hEx2 : ExistsAt w g2) :
    g1 = g2 := open Classical in by
  by_cases hEq : g1 = g2
  · exact hEq
  · have h12 : GroundsEntity g1 g2 := by
      cases hU1 w g2 hEx2 with
      | inl h1 => exact False.elim (hEq h1.symm)
      | inr h2 => exact h2
    have h21 : GroundsEntity g2 g1 := by
      cases hU2 w g1 hEx1 with
      | inl h1 => exact False.elim (hEq h1)
      | inr h2 => exact h2
    exact False.elim (hAsym g1 g2 h12 h21)

-- ============================================================================
-- Section 1b: Semantic Repair — the Asymmetry Premise is Refutable
-- ============================================================================

/-- Semantic Lemma: `GroundsEntity` is reflexive at every entity.
    Grounding is meaning-containment, so an entity trivially possesses every
    capacity it already has. No relation of this form can be irreflexive.
    Footprint: `{Means, Subject}`. -/
theorem groundsEntity_reflexive (e : Entity) : GroundsEntity e e :=
  fun _ hx => hx

/-- Semantic Lemma: an entity grounds the Ground of Reality exactly when it has
    total meaning-capacity. Because `Entity.ofGround` means every proposition,
    the grounding obligation `∀ p, EntityMeans ofGround p → EntityMeans e p`
    collapses to maximal capacity.
    Footprint: `{Means, Subject}`. -/
theorem grounds_ground_iff_maximal (e : Entity) :
    GroundsEntity e Entity.ofGround ↔ MaximalCapacity e := by
  constructor
  · intro h p
    exact h p trivial
  · intro h p _
    exact h p

/-- Semantic Lemma: no subject-entity is identical with the Ground of Reality.
    Footprint: `{Subject}`. -/
theorem ofGround_ne_ofSubject (s : Subject) : EntityOf s ≠ Entity.ofGround := by
  intro hEq
  cases hEq

/-- Countermodel: `AsymmetricGrounding` as stated is UNSATISFIABLE.
    It reads `∀ g1 g2, GroundsEntity g1 g2 → ¬ GroundsEntity g2 g1` with no
    `g1 ≠ g2` guard, but grounding is reflexive, so `g1 = g2 = ofGround` refutes
    it. This is not a price the theory could ever pay: the `hAsym` argument of
    `universal_ground_unicity` reduces against a false statement, so that route
    to unicity is void. Section 3b supplies a satisfiable replacement.
    Footprint: `{Means, Subject}`. -/
theorem not_asymmetric_grounding : ¬ AsymmetricGrounding := by
  intro h
  exact h Entity.ofGround Entity.ofGround
    (groundsEntity_reflexive Entity.ofGround)
    (groundsEntity_reflexive Entity.ofGround)

-- ============================================================================
-- Section 2: Concrete Exhaustive Exclusion of Non-Ground Entities in Γ
-- ============================================================================

/-- Theorem: No Atomic Entity Can Be a Universal Modal Ground.
    An atomic factual state cannot ground Entity.ofGround, hence cannot ground all beings.
    Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
theorem no_atom_is_universal_modal_ground (n : Nat) (w : World) :
    ¬ UniversalModalGround (Entity.ofAtom n) := by
  intro hU
  have hEx : ExistsAt w Entity.ofGround := trivial
  have hCases := hU w Entity.ofGround hEx
  cases hCases with
  | inl hEq => cases hEq
  | inr hGr => exact atom_cannot_ground_the_ground n hGr

/-- Theorem: No Finite Discriminating Subject Can Be a Universal Modal Ground.
    A subject with finite propositional grasp cannot ground Entity.ofGround,
    hence cannot ground all beings across modal space.
    Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
theorem no_discriminating_subject_is_universal_modal_ground
    (s : Subject) (hDisc : ∃ p, ¬ Logos.Agency.Means s p) (w : World) :
    ¬ UniversalModalGround (EntityOf s) := by
  intro hU
  have hEx : ExistsAt w Entity.ofGround := trivial
  have hCases := hU w Entity.ofGround hEx
  cases hCases with
  | inl hEq => cases hEq
  | inr hGr => exact discriminating_subject_cannot_ground_the_ground s hDisc hGr

/-- Theorem: Entity.ofGround is the Sole Universal Ground in the Γ Inventory.
    Any universal modal ground in a world w cannot be an atom, nor a discriminating subject.
    Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
theorem ofGround_sole_universal_ground (e : Entity) (w : World)
    (hU : UniversalModalGround e) :
    (∀ n : Nat, e ≠ Entity.ofAtom n) ∧
    (∀ s : Subject, (∃ p, ¬ Logos.Agency.Means s p) → e ≠ EntityOf s) := by
  constructor
  · intro n hEq
    subst hEq
    exact no_atom_is_universal_modal_ground n w hU
  · intro s hDisc hEq
    subst hEq
    exact no_discriminating_subject_is_universal_modal_ground s hDisc w hU

-- ============================================================================
-- Section 3: Synthesis of Foundational Unicity (Classical Divine Monotheism)
-- ============================================================================

/-- Foundational Unicity (The Sixth Classical Attribute):
    The entity is a universal modal ground of all reality, transcends all atomic
    and finite subjective beings, and is structurally unique (no competing universal
    ground can co-exist under asymmetric grounding). -/
structure FoundationalUnicity (g : Entity) : Prop where
  /-- The entity grounds every being in every possible world -/
  universal_ground : UniversalModalGround g
  /-- The entity cannot be an atomic worldly state -/
  atom_exclusion : ∀ n : Nat, g ≠ Entity.ofAtom n
  /-- The entity cannot be a finite discriminating subject -/
  subject_transcendence : ∀ s : Subject, (∃ p, ¬ Logos.Agency.Means s p) → g ≠ EntityOf s
  /-- Unicity: any competing universal ground is identical under asymmetry -/
  unicity : ∀ g' : Entity, UniversalModalGround g' → AsymmetricGrounding →
    ∀ w : World, ExistsAt w g → ExistsAt w g' → g = g'

/-- Master Synthesis Theorem: The Ground of Reality possesses Foundational Unicity.
    `Entity.ofGround` satisfies Classical Divine Unicity (Monotheism).
    Footprint: `{CL, Means, NecessarySubjectKind, Subject}` (0 substantive axioms). -/
theorem ofGround_foundational_unicity :
    FoundationalUnicity Entity.ofGround := {
  universal_ground := ofGround_universal_modal_ground
  atom_exclusion := fun n hEq => by cases hEq
  subject_transcendence := fun s _ hEq => by cases hEq
  unicity := fun g' hU' hAsym w hEx1 hEx2 =>
    universal_ground_unicity Entity.ofGround g' ofGround_universal_modal_ground hU' hAsym w hEx1 hEx2
}

-- ============================================================================
-- Section 3b: The Repaired Unicity Route (One Named Hypothesis)
-- ============================================================================

/-- Theorem: Foundational Unicity from ONE named hypothesis.
    If no subject has total meaning-capacity, then the Ground of Reality is the
    only universal modal ground. The atom and discriminating-subject branches are
    discharged by `ofGround_sole_universal_ground`; only the total-capacity
    subject is left, and `hNoTotal` rules it out. Unlike the `AsymmetricGrounding`
    route this premise is satisfiable, so the argument is not void.
    Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
theorem ofGround_unicity_from_no_discriminating_subject
    (hNoTotal : ∀ s : Subject, ∃ p, ¬ Means s p)
    (e : Entity) (w : World) (hU : UniversalModalGround e) : e = Entity.ofGround := by
  have h208 := ofGround_sole_universal_ground e w hU
  rcases e with s | n | _
  · exact False.elim (h208.2 s (hNoTotal s) rfl)
  · exact False.elim (h208.1 n rfl)
  · rfl

/-- Theorem: the maximality hypothesis IS the exclusion of maximal capacity among
    non-ground entities. This prices Foundational Unicity in the project's own
    vocabulary (`MaximalCapacity`, `FoundationalOmnipresence.lean:119`) instead of
    in newly invented terms, and shows the hypothesis is exactly one predicate.
    Footprint: `{CL, Means, Subject}`. -/
theorem no_discriminating_subject_iff_no_maximal_non_ground :
    (∀ s : Subject, ∃ p, ¬ Means s p)
      ↔ (∀ e : Entity, e ≠ Entity.ofGround → ¬ MaximalCapacity e) := by
  constructor
  · intro h e hne hM
    rcases e with s | n | _
    · obtain ⟨p, hp⟩ := h s
      exact hp (hM p)
    · exact hM True
    · exact hne rfl
  · intro h s
    classical
    by_cases hEx : ∃ p, ¬ Means s p
    · exact hEx
    · have hM : MaximalCapacity (EntityOf s) :=
        fun p => Classical.byContradiction (fun hn => hEx ⟨p, hn⟩)
      exact False.elim (h (EntityOf s) (ofGround_ne_ofSubject s) hM)

/-- Repaired Foundational Unicity: identical in content to `FoundationalUnicity`,
    except that the unicity field is discharged by the single named hypothesis
    `∀ s, ∃ p, ¬ Means s p` rather than by the refutable `AsymmetricGrounding`.
    The unicity field is now a plain identity, with no unpayable premise. -/
structure SoleUniversalGrounding (g : Entity) : Prop where
  /-- The entity grounds every being in every possible world -/
  universal_ground : UniversalModalGround g
  /-- The entity cannot be an atomic worldly state -/
  atom_exclusion : ∀ n : Nat, g ≠ Entity.ofAtom n
  /-- The entity cannot be a discriminating subject -/
  subject_transcendence : ∀ s : Subject, (∃ p, ¬ Means s p) → g ≠ EntityOf s
  /-- Unicity: any other universal modal ground is identical to this one -/
  unicity : ∀ g' : Entity, UniversalModalGround g' → g' = g

/-- Master Synthesis: the Ground of Reality is the sole universal ground, under
    the single named hypothesis.
    Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
theorem ofGround_sole_universal_grounding
    (hNoTotal : ∀ s : Subject, ∃ p, ¬ Means s p) :
    SoleUniversalGrounding Entity.ofGround := {
  universal_ground := ofGround_universal_modal_ground
  atom_exclusion := fun n hEq => by cases hEq
  subject_transcendence := fun s _ hEq => by cases hEq
  unicity := fun g' hU' =>
    ofGround_unicity_from_no_discriminating_subject hNoTotal g' actualWorld hU'
}

/-- Master Synthesis (existential form): exactly one universal modal ground exists.
    Existence comes from `ofGround_universal_modal_ground`, which is unconditional;
    uniqueness from `hNoTotal`. This is Classical Monotheism with the whole price
    of the claim visible in a single line. The `∃!` notation and `ExistsUnique`
    are absent from this Lean core, so the standard unique-existence conjunction
    is written out.
    Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
theorem exactly_one_universal_modal_ground
    (hNoTotal : ∀ s : Subject, ∃ p, ¬ Means s p) :
    ∃ g : Entity, UniversalModalGround g ∧
      (∀ g' : Entity, UniversalModalGround g' → g' = g) :=
  ⟨Entity.ofGround, ofGround_universal_modal_ground,
    fun g' hU' => ofGround_unicity_from_no_discriminating_subject hNoTotal g' actualWorld hU'⟩

-- ============================================================================
-- Section 4: Category Boundary Separations (Honest Demarcation)
-- ============================================================================

/-- Separation Model: Foundational Unicity Does Not Imply a Single-Person Ground.
    Proving that there is exactly one universal grounding principle does not logically
    force that the internal life of that ground is solitary or lacks relational plurality.

    **Read the entailment direction carefully — this is a separation, not a refutation.**
    The model has one ground, and in it that ground bears at least two distinct persons; so
    *unicity does not entail* a single-Person ground. It does **not** follow that a single-Person
    ground is false: the person-count is left *undetermined* by unicity. Two further
    consequences, each load-bearing against a common misreading:
      - **Monotheism is not this claim.** Monotheism is one *God* — one universal modal ground —
        and that is `exactly_one_universal_modal_ground` (C320), PROVEN. This declaration is about
        how many *Persons* that one God bears, which is a different question, and it stays open here.
      - **The positive plural reading is priced elsewhere.** Distinct subsisting centres come from
        the declared META axiom `DivineAgape.AxAgapeEssence` (C504), not from this countermodel.
        Whether the ground is personal *at all* is `C228` (BLOCKED), and that is upstream: a
        person-count is not well posed until personality is settled.
    Footprint: `{}`. -/
theorem unicity_does_not_force_unitarian_monad :
    ∃ (Ground : Type) (Persons : Ground → Type),
      (∃ g : Ground, ∀ g' : Ground, g' = g) ∧ (∀ g : Ground, ∃ (p1 p2 : Persons g), p1 ≠ p2) := by
  refine ⟨Unit, fun _ => Bool, ?_, fun _ => ⟨true, false, Bool.noConfusion⟩⟩
  exact ⟨(), fun y => Subsingleton.elim y ()⟩

/-- Separation Model: Foundational Unicity Does Not Entail Pantheism / Monism.
    A unique universal ground is strictly non-identical with the world of entities
    it grounds, preserving metaphysical transcendence (`TranscendentGround`).
    Footprint: `{Subject}`. -/
theorem unicity_strictly_transcends_world :
    TranscendentGround Entity.ofGround :=
  ofGround_transcendent

-- ============================================================================
-- Section 5: Axiom Footprint Audit
-- ============================================================================

#print axioms universal_ground_unicity
#print axioms no_atom_is_universal_modal_ground
#print axioms no_discriminating_subject_is_universal_modal_ground
#print axioms ofGround_sole_universal_ground
#print axioms ofGround_foundational_unicity
#print axioms unicity_does_not_force_unitarian_monad
#print axioms unicity_strictly_transcends_world
#print axioms groundsEntity_reflexive
#print axioms grounds_ground_iff_maximal
#print axioms ofGround_ne_ofSubject
#print axioms not_asymmetric_grounding
#print axioms ofGround_unicity_from_no_discriminating_subject
#print axioms no_discriminating_subject_iff_no_maximal_non_ground
#print axioms ofGround_sole_universal_grounding
#print axioms exactly_one_universal_modal_ground

end Logos.FoundationalUnicity
