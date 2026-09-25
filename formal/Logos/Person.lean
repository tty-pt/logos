/-
# Logos.Person — Level 2b: from agency to person; §24b inseparability

In the unified Γ ontology, **Personhood** is defined constitutively:
> A person is a subject possessing a numerically distinct free will.

Personhood is not an additional opaque metaphysical property placed on top of an
already established free subject. The project derives:
  Subject → Intentional Subject → Normativity → Choice → Free Will → Person
without any added metaphysical bridge or uninterpreted dummy predicate.
-/

import Logos.Core
import Logos.Agency
import Logos.Alternatives
import Logos.Choice

namespace Logos.Person

open Logos.Core (T IsFalse)
open Logos.Agency
open Logos.Alternatives (Incompatible)
open Logos.Choice (Chooses FreeWill FreeSubject ChoiceField)

/-- Person: a subject possessing a numerically distinct free will.
    In the unified Γ ontology, Personhood is constitutively defined as the possession
    of genuine free will (`Person s := FreeSubject s`).
    Footprint: `{Means, Subject}`. -/
def Person (s : Subject) : Prop := FreeSubject s

/-- Master Theorem: Every Free Subject is a Person.
    Footprint: `{Means, Subject}`. -/
theorem free_subject_is_person (s : Subject) (h : FreeSubject s) : Person s :=
  h

/-- Master Equivalence: Personhood is constitutively equivalent to Free Subjecthood.
    Footprint: `{Means, Subject}`. -/
theorem person_iff_freeSubject (s : Subject) : Person s ↔ FreeSubject s :=
  Iff.rfl

/-- Master Equivalence: Personhood is constitutively equivalent to Free Will.
    Footprint: `{Means, Subject}`. -/
theorem person_iff_freeWill (s : Subject) : Person s ↔ FreeWill s :=
  Iff.rfl

/-- Every Person possesses Free Will.
    Footprint: `{Means, Subject}`. -/
theorem person_has_free_will (s : Subject) (h : Person s) : FreeWill s :=
  h

/-- Independent Will: the faculty of will possessed by subject s is uniquely its own,
    numerically distinct from the will of any distinct subject.
    Directly unpacks the principle of numerical individuation of wills (`will_individuation`). -/
def IndependentWill (s : Subject) : Prop :=
  ∀ s' : Subject, s' ≠ s → Logos.Agency.subjectWill s' ≠ Logos.Agency.subjectWill s

/-- Individual substance (Boethius, "individual"): the subject is numerically
    individuated — no distinct subject owns its volitional identity (`IndependentWill`). -/
def IndividualSubstance (s : Subject) : Prop := IndependentWill s

/-- Discursive capacity: the intellectual capacity of a subject to co-entertain
    distinct or incompatible propositional contents. Independent of choice or volition. -/
def DiscursiveCapacity (s : Subject) : Prop :=
  ∃ p q : Prop, Means s p ∧ Means s q ∧ (p ≠ q ∨ Incompatible p q)

/-- Rational nature (Boethius, "of a rational nature"; deliberative rationality):
    an intentional subject endowed with discursive capacity (entertaining distinct
    or alternative propositional contents). Independent of FreeWill or Chooses. -/
def RationalNature (s : Subject) : Prop :=
  IntentionalSubject s ∧ DiscursiveCapacity s

/-- Dominion over one's own acts (Aquinas, ST I q.29 a.3; q.83): the subject
    genuinely chooses, acting from itself rather than being merely acted upon. -/
def DominionOverActs (s : Subject) : Prop := FreeWill s

/-- Free, Independent Will: a subject endowed with both the capacity of free choice
    (`FreeWill s`) and an independently individuated volitional faculty (`IndependentWill s`). -/
def FreeIndependentWill (s : Subject) : Prop :=
  FreeWill s ∧ IndependentWill s

/-- Numerical individuation guarantees that every subject possesses an independent will.
    Footprint: `{Subject, Will, subjectWill, will_individuation}`. -/
theorem independent_will_of_subject (s : Subject) : IndependentWill s :=
  fun s' hne => Logos.Agency.will_individuation s' s hne

/-- Every subject is an individual substance.
    Footprint: `{Subject, Will, subjectWill, will_individuation}`. -/
theorem individual_substance_of_subject (s : Subject) : IndividualSubstance s :=
  independent_will_of_subject s

/-- Free will implies discursive capacity. -/
theorem freeWill_implies_discursiveCapacity (s : Subject)
    (h : FreeWill s) : DiscursiveCapacity s := by
  obtain ⟨p, q, hCh⟩ := h
  exact ⟨p, q, hCh.1, hCh.2.1, Or.inr hCh.2.2⟩

/-- Free will implies rational nature. -/
theorem freeWill_implies_rationalNature (s : Subject)
    (h : FreeWill s) : RationalNature s := by
  have hDisc := freeWill_implies_discursiveCapacity s h
  obtain ⟨p, _q, hCh⟩ := h
  exact ⟨⟨p, hCh.1⟩, hDisc⟩

/-- Thomistic person core: the Boethius–Aquinas conditions of personhood —
    "individual substance of a rational nature" possessed of dominion over its
    own acts — formalized through their operative distinguishing features.
    Personhood is thus NOT an arbitrary redefinition: it is the formal criterion
    through which the Thomistic personal reality is identified.
    Map: individual → IndependentWill; rational nature → IntentionalSubject ∧ DiscursiveCapacity;
    dominion → FreeWill. -/
def ThomisticPersonCore (s : Subject) : Prop :=
  IndividualSubstance s ∧ RationalNature s ∧ DominionOverActs s

/-- Free, independent will entails the Thomistic person core.
    Footprint: `{Means, Subject, Will, subjectWill}`. -/
theorem freeIndependentWill_implies_thomisticCore (s : Subject)
    (h : FreeIndependentWill s) : ThomisticPersonCore s :=
  ⟨h.2, freeWill_implies_rationalNature s h.1, h.1⟩

/-- Thomistic person core entails free, independent will.
    Footprint: `{Means, Subject, Will, subjectWill}`. -/
theorem thomisticCore_implies_freeIndependentWill (s : Subject)
    (h : ThomisticPersonCore s) : FreeIndependentWill s :=
  ⟨h.2.2, h.1⟩

/-- Master Equivalence: free, independent will is equivalent to the
    Thomistic person core.
    Footprint: `{Means, Subject, Will, subjectWill}`. -/
theorem freeIndependentWill_iff_thomisticCore (s : Subject) :
    FreeIndependentWill s ↔ ThomisticPersonCore s :=
  ⟨freeIndependentWill_implies_thomisticCore s, thomisticCore_implies_freeIndependentWill s⟩

/-- Master Equivalence: Personhood is constitutively equivalent to Free, Independent Will.
    A person is a subject possessing a free will that is genuinely its own,
    not numerically identical with another subject's will.
    Footprint: `{Means, Subject, Will, subjectWill, will_individuation}`. -/
theorem person_iff_freeIndependentWill (s : Subject) : Person s ↔ FreeIndependentWill s := by
  constructor
  · intro hp
    exact ⟨hp, independent_will_of_subject s⟩
  · intro ⟨hFW, _⟩
    exact hFW

/-- Master Theorem: Every Person possesses a Free, Independent Will.
    Footprint: `{Means, Subject, Will, subjectWill, will_individuation}`. -/
theorem person_has_free_independent_will (s : Subject) (h : Person s) : FreeIndependentWill s :=
  (person_iff_freeIndependentWill s).mp h

/-- Master Theorem: Every Subject with a Free, Independent Will is a Person.
    Footprint: `{Means, Subject, Will, subjectWill, will_individuation}`. -/
theorem free_independent_will_is_person (s : Subject) (h : FreeIndependentWill s) : Person s :=
  (person_iff_freeIndependentWill s).mpr h

/-- Master Correspondence: Personhood is constitutively equivalent to the
    Thomistic person core.
    Footprint: `{Means, Subject, Will, subjectWill, will_individuation}`. -/
theorem person_iff_thomisticCore (s : Subject) : Person s ↔ ThomisticPersonCore s := by
  constructor
  · intro hp
    exact freeIndependentWill_implies_thomisticCore s ((person_iff_freeIndependentWill s).mp hp)
  · intro hc
    exact (person_iff_freeIndependentWill s).mpr (thomisticCore_implies_freeIndependentWill s hc)

/-- Every Person is an Intentional Subject.
    A free choosing agent necessarily means the alternatives between which it chooses.
    Footprint: `{Means, Subject}`. -/
theorem person_is_intentional (s : Subject) (h : Person s) : IntentionalSubject s := by
  obtain ⟨p, _q, hCh⟩ := h
  exact ⟨p, hCh.1⟩

/-- Every Person possesses Discursive Capacity.
    Footprint: `{Means, Subject}`. -/
theorem person_has_discursive_capacity (s : Subject) (h : Person s) : DiscursiveCapacity s :=
  freeWill_implies_discursiveCapacity s h

/-- Every Person has an Independent Will.
    Footprint: `{Means, Subject, Will, subjectWill, will_individuation}`. -/
theorem person_has_independent_will (s : Subject) (h : Person s) : IndependentWill s :=
  independent_will_of_subject s

/-- Any person has a choice field: a person is always before two incompatible alternatives.
    Footprint: `{Means, Subject}`. -/
theorem person_hasChoiceField {s : Subject} (hs : Person s) : ∃ p q : Prop, ChoiceField s p q := by
  obtain ⟨p, q, hCh⟩ := hs
  exact ⟨p, q, hCh.1, hCh.2.2⟩

/-- Act implies an intentional subject.
    Footprint: `{Initiates, Means, State, Subject}` (VOCAB). -/
theorem act_implies_intentionalSubject {s : Subject} {p : Prop} (h : Logos.Agency.Act s p) :
    IntentionalSubject s :=
  ⟨p, h.1⟩

theorem act_implies_intentional {s : Subject} {p : Prop} (h : Logos.Agency.Act s p) :
    Intentional s :=
  act_implies_intentionalSubject h

/-- An actualized subject of an act is an intentional subject.
    Footprint: `{Initiates, Means, State, Subject}` (VOCAB). -/
theorem subjectExists_implies_intentionalSubject (h : Logos.Agency.SubjectExists s) :
    IntentionalSubject s := by
  obtain ⟨p, ha⟩ := h
  exact ⟨p, ha.1⟩

theorem subjectExists_implies_intentional (h : Logos.Agency.SubjectExists s) :
    Intentional s :=
  subjectExists_implies_intentionalSubject h

/-- Under a bridge from meaning to initiation, intentionality implies SubjectExists. -/
theorem intentional_implies_subjectExists_of_bridge
    (hBridge : ∀ (s : Subject) (p : Prop), Logos.Agency.Means s p → ∃ w w' : Logos.Agency.State, Logos.Agency.Initiates s w w' p)
    (h : IntentionalSubject s) : Logos.Agency.SubjectExists s := by
  obtain ⟨p, hm⟩ := h
  exact ⟨p, hm, hBridge s p hm⟩

/-- The existence of an act entails that an intentional subject exists (formerly nominal T5).
    Footprint: `{Initiates, Means, State, Subject}` (VOCAB). -/
theorem intentionalSubject_exists_of_act (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Act s p) :
    ∃ s : Subject, IntentionalSubject s := by
  obtain ⟨s, p, ha⟩ := h
  exact ⟨s, act_implies_intentionalSubject ha⟩

/-- Backward-compatibility alias for intentional subject existence. -/
theorem intentional_exists_of_act (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Act s p) :
    ∃ s : Subject, Intentional s :=
  intentionalSubject_exists_of_act h

/-- An assertion entails that an intentional subject exists.
    Footprint: `{Initiates, Means, State, Subject}`. -/
theorem intentionalSubject_exists_of_assert {s : Subject} {p : Prop} (h : Logos.Agency.Asserts s p) :
    ∃ s' : Subject, IntentionalSubject s' :=
  ⟨s, act_implies_intentionalSubject (Logos.Agency.assertion_is_act h)⟩

/-- Backward-compatibility alias for intentionality from assert. -/
theorem intentional_exists_of_assert {s : Subject} {p : Prop} (h : Logos.Agency.Asserts s p) :
    ∃ s' : Subject, Intentional s' :=
  intentionalSubject_exists_of_assert h

-- ---------------------------------------------------------------------------
-- §24b — personal/logical inseparability of the rational act
-- ---------------------------------------------------------------------------

/-- An act whose content is `a`. -/
def RationalAct (a : Prop) : Prop := ∃ s : Subject, ∃ p : Prop, A s p ∧ a = p

/-- `f` is a feature of content `a` iff `a` logically entails `f`. -/
def HasFeature (a f : Prop) : Prop := a → f

/-- A personal feature of an act: someone means a feature of its content (Q3.1). -/
def CarriesPersonalFeature (a : Prop) : Prop :=
  ∃ p : Prop, HasFeature a p ∧ ∃ s : Subject, Means s p

/-- A logical feature of an act: a feature that is true-or-false (Q3.2). -/
def CarriesLogicalFeature (a : Prop) : Prop :=
  ∃ p : Prop, HasFeature a p ∧ (T p ∨ IsFalse p)

/-- Every rational act carries a personal feature exactly when it carries a logical feature:
    personhood and logic travel together.
    §24b — in every rational act, personal and logical features coincide. -/
theorem inseparability_24b : ∀ a : Prop,
    RationalAct a → (CarriesPersonalFeature a ↔ CarriesLogicalFeature a) := by
  intro a hra
  constructor
  · intro h
    obtain ⟨p, hf, s, hm⟩ := h
    by_cases hT : T p
    · exact ⟨p, hf, Or.inl hT⟩
    · exact ⟨p, hf, Or.inr hT⟩
  · intro h
    obtain ⟨s, q, hq⟩ := hra
    obtain ⟨ha, heq⟩ := hq
    rw [heq]
    exact ⟨q, id, s, act_implies_means ha⟩

-- ===========================================================================
-- Axiom Footprint Audit
-- ===========================================================================

#print axioms free_subject_is_person
#print axioms person_iff_freeSubject
#print axioms person_iff_freeWill
#print axioms person_has_free_will
#print axioms person_is_intentional
#print axioms person_hasChoiceField
#print axioms inseparability_24b
#print axioms independent_will_of_subject
#print axioms person_iff_freeIndependentWill
#print axioms person_has_free_independent_will
#print axioms free_independent_will_is_person
#print axioms freeIndependentWill_implies_thomisticCore
#print axioms thomisticCore_implies_freeIndependentWill
#print axioms freeIndependentWill_iff_thomisticCore
#print axioms person_iff_thomisticCore

end Logos.Person
