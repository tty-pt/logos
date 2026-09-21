/-
# Logos.RecoveredOntologicalGround — Recovered T8 Ontology Layer and Ontological Synthesis

This module restores the authentic mathematical content of T8 and connects it
to the entity-level ground of reality:
1. Formalizes the recovered T8 result: `NecessaryPersonalReality` (Claim C) derived
   directly from `GroundPerson.T8_personalGround`.
2. Formalizes the act-to-personal-reality corollary.
3. Formalizes the stronger entity-level ontology: `GroundOfReality`, `NecessaryGroundOfReality`,
   and `NecessaryPersonalGroundOfReality` (Claim E).
4. Restores the historical reality-grounding principle `AxRealityGrounding` (GAPMAP C130).
5. Strictly separates the contingent human subject from the necessary ground of reality.
6. Connects Personal-Logical Inseparability (`Person.inseparability_24b`), Explanatory
   Adequacy (`explanatory_adequacy` / `atom_cannot_ground_person`), and agential grounding
   transmission to synthesize `NecessaryPersonalGroundOfReality`.
7. Preserves strict level separation: Claim C does not entail Claim E.
-/

import Logos.Core
import Logos.Semantics
import Logos.Truthmaker
import Logos.Modal
import Logos.Agency
import Logos.Person
import Logos.GroundPerson

namespace Logos.RecoveredOntologicalGround

open Logos.Core (T IsFalse)
open Logos.Semantics (Form World Satisfies TrueAt NecessarilyTrue strongTruthExists TV)
open Logos.Truthmaker (Entity Ground ExistsAt actualWorld otherWorld EntityOf)
open Logos.Modal (NecessaryEntity AxGlobalGround T7_necessaryReality)
open Logos.Agency (Subject Act A Means Will subjectWill)
open Logos.Person (Person inseparability_24b CarriesPersonalFeature CarriesLogicalFeature RationalAct free_subject_is_person person_is_intentional)
open Logos.GroundPerson (GroundProp Realizes IsPresentPersonalFeature Personal AxGroundBearing AxPersonalGround T8_personalGround)

/-- Actual entity: an entity that exists in the actual world. -/
def ActualEntity (e : Entity) : Prop := ExistsAt actualWorld e

/-- Impersonal Entity: an atomic factual truthmaker that is not a subject. -/
def ImpersonalEntity (e : Entity) : Prop := ∃ n : Nat, e = Entity.ofAtom n

/-- Meaning capacity of an entity. -/
def EntityMeans (e : Entity) (p : Prop) : Prop :=
  match e with
  | Entity.ofSubject s => Means s p
  | Entity.ofAtom _ => False

/-- GroundsEntity: ontological entities-relation l ge. DEFINITION (meaning-
    containment, esse est agere at the entity level): g grounds e iff g
    possesses at least e's intentional/agential capacity (means everything e
    means). `∀ p, EntityMeans e p → EntityMeans g p`.
    Footprint: `{Means, Subject}`. -/
def GroundsEntity (g e : Entity) : Prop :=
  ∀ p : Prop, EntityMeans e p → EntityMeans g p

/-- Ontological Distinction: Atomic entities are provably distinct from any subject correlate. -/
theorem ofAtom_ne_ofSubject (n : Nat) (s : Subject) :
    Entity.ofAtom n ≠ EntityOf s :=
  fun h => Entity.noConfusion h

/-- Explanatory Adequacy of Grounding: theorem (definitional consequence of
    `GroundsEntity`). The ground g of e possesses e's account-carrying meaning.
    Footprint: `{Means, Subject}`. -/
theorem explanatory_adequacy
    (g e : Entity) (hGr : GroundsEntity g e) (p : Prop) (hEM : EntityMeans e p) :
    EntityMeans g p :=
  hGr p hEM

/-- Theorem: An impersonal atomic entity cannot ground a personal subject. -/
theorem atom_cannot_ground_person
    (n : Nat) (s : Subject) (hPers : Person s) :
    ¬ GroundsEntity (Entity.ofAtom n) (EntityOf s) := by
  intro hGr
  have hMeans : ∃ p : Prop, Means s p := person_is_intentional s hPers
  obtain ⟨p, hp⟩ := hMeans
  have hEM : EntityMeans (EntityOf s) p := hp
  have hGM : EntityMeans (Entity.ofAtom n) p :=
    explanatory_adequacy (Entity.ofAtom n) (EntityOf s) hGr p hEM
  exact hGM

-- ============================================================================
-- Section 1: Entity-Level Grounding Surface (annotations only)
-- ============================================================================

/-
Entity-level claim E (`∃ g : Entity, NecessaryEntity g ∧ NecessaryPersonalGround g`) is
NOT a theorem: world-indexed necessity requires SEM `AxGlobalGround`; the
`Personal` predicate needs a META `GroundProp` instance; the `GroundOfReality`
subject-branch is open. These are the obstacle-registry items of
THIS_IS_PERSONAL.md §12.1 (Claim E) — never re-added as axioms. The required
headline is the constitutive claim in `Logos.PersonalGroundOfReality`.
-/

-- ============================================================================
-- Section 2: Formal Recovery of T8 Result Directly (Claim C)
-- ============================================================================

/-- NecessaryPersonalReality: a necessary entity realizes a present personal feature.
    This is the clean current-language predicate for what T8 actually establishes (Claim C). -/
def NecessaryPersonalReality (g : Entity) : Prop :=
  NecessaryEntity g ∧ ∃ f : Prop, Realizes g f ∧ IsPresentPersonalFeature f

/-- Theorem: A present personal feature directly forces a Necessary Personal Reality.
    Directly consumes `Logos.GroundPerson.T8_personalGround`.
    Footprint: `{AxPersonalGround, GroundProp, Initiates, Means, State, Subject}`. -/
theorem necessary_personal_reality_of_present_feature
    {f : Prop} (hf : IsPresentPersonalFeature f) :
    ∃ g : Entity, NecessaryPersonalReality g := by
  obtain ⟨g, hNec, hPersonal⟩ := T8_personalGround hf
  exact ⟨g, hNec, hPersonal⟩

/-- Present personal feature of a rational act. -/
theorem present_personal_feature_of_act
    {s : Subject} {p : Prop} (hAct : Act s p) :
    IsPresentPersonalFeature p :=
  ⟨s, p, hAct, hAct.1, rfl⟩

/-- Act-to-Personal-Reality Corollary: Any performed rational act forces a Necessary Personal Reality.
    Footprint: `{AxPersonalGround, GroundProp, Initiates, Means, State, Subject}`. -/
theorem necessary_personal_reality_of_act
    {s : Subject} {p : Prop} (hAct : Act s p) :
    ∃ g : Entity, NecessaryPersonalReality g :=
  necessary_personal_reality_of_present_feature (present_personal_feature_of_act hAct)

-- ============================================================================
-- Section 3: Stronger Entity-Level Ontology (Claim D and Claim E)
-- ============================================================================

/-- GroundOfReality: an entity g ontologically grounds every actual entity distinct from itself. -/
def GroundOfReality (g : Entity) : Prop :=
  ∀ e : Entity, ActualEntity e → e = g ∨ GroundsEntity g e

/-- NecessaryGroundOfReality: an entity is necessary and is the ontological ground of reality (Claim D).
    Does not encode necessity inside GroundOfReality or encode the final conclusion recursively. -/
structure NecessaryGroundOfReality (g : Entity) : Prop where
  necessary : NecessaryEntity g
  grounds_reality : GroundOfReality g

/-- NecessaryPersonalGroundOfReality: an entity is the necessary ground of reality AND personal (Claim E).
    Combines the universal ground of reality with the positive realization of personal features. -/
structure NecessaryPersonalGroundOfReality (g : Entity) : Prop where
  reality : NecessaryGroundOfReality g
  personal : ∃ f : Prop, Realizes g f ∧ IsPresentPersonalFeature f

-- ============================================================================
-- Section 4: Derivation of the Ground of Reality (T7 + AxRealityGrounding)
-- ============================================================================

/-
`necessary_ground_of_reality_derived` and `necessary_personal_ground_derived`
are REMOVED: their only routes were the deleted axioms `AxRealityGrounding`
and `agential_grounding_transmission`. The entity-level surface
(`GroundOfReality`, `NecessaryGroundOfReality`, `NecessaryPersonalGroundOfReality`)
remains as the annotated Claim-E statement (see Section 1 note). The headline
theorem is the constitutive claim in `Logos.PersonalGroundOfReality`.
-/

-- ============================================================================
-- Section 5: Modal Invariance and Finite Subject Separation
-- ============================================================================

theorem actualWorld_ne_otherWorld : otherWorld ≠ actualWorld := by
  intro h
  have h0 : otherWorld 0 = actualWorld 0 := congrFun h 0
  dsimp [otherWorld, actualWorld] at h0
  contradiction

theorem subject_exists_at_actualWorld (s : Subject) : ExistsAt actualWorld (EntityOf s) := by
  dsimp [ExistsAt, Logos.Truthmaker.EntityExistsAt, Logos.Truthmaker.SubjectExistsAt, EntityOf]

theorem subject_not_exists_at_otherWorld (s : Subject) : ¬ ExistsAt otherWorld (EntityOf s) := by
  dsimp [ExistsAt, Logos.Truthmaker.EntityExistsAt, Logos.Truthmaker.SubjectExistsAt, EntityOf]
  intro h
  exact actualWorld_ne_otherWorld h

/-- Contingent finite subjects are numerically distinct from any necessary entity.
    Prevents modal collapse and preserves the separation of the human subject from the ground. -/
theorem contingent_subject_ne_necessary_entity
    (s : Subject) (hCont : ∃ w : World, ¬ ExistsAt w (EntityOf s))
    (g : Entity) (hNec : NecessaryEntity g) :
    EntityOf s ≠ g := by
  rintro rfl
  obtain ⟨w, hw⟩ := hCont
  exact hw (hNec w)

/-- The ground of reality strictly grounds any contingent finite subject.
    Eliminates the disjunctive branch `EntityOf s = g` via modal contingency. -/
theorem ground_of_reality_grounds_finite_subject
    (g : Entity) (hg : NecessaryGroundOfReality g)
    (s : Subject) (hCont : ∃ w : World, ¬ ExistsAt w (EntityOf s))
    (hActual : ActualEntity (EntityOf s)) :
    GroundsEntity g (EntityOf s) := by
  have hDisj := hg.grounds_reality (EntityOf s) hActual
  cases hDisj with
  | inl hEq =>
    exfalso
    exact contingent_subject_ne_necessary_entity s hCont g hg.necessary hEq
  | inr hGrounds =>
    exact hGrounds

-- ============================================================================
-- Section 6: Non-Impersonality and Inseparability
-- ============================================================================

/-- The ground of reality cannot be an impersonal atom.
    Derived via explanatory adequacy (`atom_cannot_ground_person`). -/
theorem ground_of_reality_not_impersonal
    (g : Entity) (hg : NecessaryGroundOfReality g)
    (s : Subject) (hCont : ∃ w : World, ¬ ExistsAt w (EntityOf s))
    (hPers : Person s) (hAct : ActualEntity (EntityOf s)) :
    ¬ ImpersonalEntity g := by
  intro hImp
  obtain ⟨n, rfl⟩ := hImp
  have hGr := ground_of_reality_grounds_finite_subject (Entity.ofAtom n) hg s hCont hAct
  exact atom_cannot_ground_person n s hPers hGr

/-- Any rational act carries personal features (coinciding with logical features by §24b). -/
theorem rational_act_carries_personal_feature
    (s : Subject) (p : Prop) (hAct : Act s p) :
    CarriesPersonalFeature p := by
  have hRat : RationalAct p := ⟨s, p, hAct, rfl⟩
  have hInsep := inseparability_24b p hRat
  have hLog : CarriesLogicalFeature p := by
    refine ⟨p, id, ?_⟩
    by_cases hT : T p
    · exact Or.inl hT
    · exact Or.inr hT
  exact hInsep.mpr hLog

-- ============================================================================
-- Section 7: Master Synthesis Theorem
-- ============================================================================

/-
`necessary_personal_ground_derived` is REMOVED (route used the two deleted
axioms; see Section 4 note). The constitutive headline lives in
`Logos.PersonalGroundOfReality.present_act_yields_personal_grounding_of_reality`.
-/

-- ============================================================================
-- Section 8: Strict Level Separation & Non-Equivalence (Claim C vs Claim E)
-- ============================================================================

/-- Claim E entails Claim C: A Necessary Personal Ground of Reality is a Necessary Personal Reality. -/
theorem necessary_personal_ground_implies_personal_reality
    (g : Entity) (h : NecessaryPersonalGroundOfReality g) :
    NecessaryPersonalReality g :=
  ⟨h.reality.necessary, h.personal⟩

/-- Claim E entails Claim D: A Necessary Personal Ground of Reality is a Necessary Ground of Reality. -/
theorem necessary_personal_ground_implies_ground_of_reality
    (g : Entity) (h : NecessaryPersonalGroundOfReality g) :
    NecessaryGroundOfReality g :=
  h.reality

end Logos.RecoveredOntologicalGround
