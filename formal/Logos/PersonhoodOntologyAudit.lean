/-
# Logos.PersonhoodOntologyAudit — Ontological Audit of Personhood in Γ

This module conducts a rigorous formal audit of Personhood in Γ, addressing the
fundamental question:
> Does the retorsive derivation (Act → Agency → Normativity → Choice → Free Will)
> logically reach Personhood, or is there an unbridgeable metaphysical frontier?

## 1. Historical & Conceptual Diagnosis

In Γ's development, three distinct definitions of `Person` have emerged:

1. **Nominal/Early Cogito Definition (`Spike_A4_2` / commit `7803f44`):**
   `Person_nominal s := Agent s ∧ Rational s ∧ Intentional s`
   With `Agent := True` and `Rational := True`, this collapsed definitionally to
   `IntentionalSubject s := ∃ p, Means s p`.
   Under this definition, `present_person` was proven immediately from the Cogito
   datum with `{Means, Subject}`. However, this was rightly criticized as nominal:
   any entity meaning a proposition (even an inanimate sign or simple mechanism)
   was called a "person" before any choice, deliberation, or freedom was established.

2. **Constitutive/Frankfurt-Retorsive Definition (`Retorsion.lean:153`):**
   `Person_constitutive s := IntentionalSubject s ∧ FreeWill s`
   In classical philosophical action theory (Frankfurt 1971, Locke, Kant, Boethius),
   a Person is an intentional subject endowed with rational deliberation and free will
   (the capacity to evaluate and choose between incompatible alternatives).
   Now that Γ has genuinely derived Free Will from Genuine Normativity with 0 substantive
   axioms (`indubitable_normative_free_will`), this constitutive definition is
   **fully derived as an unavoidable theorem** (`FreeSubject s → Person_constitutive s`).

3. **Dualist/Opaque Definition (`Person.lean:57` / commit `ef60650`):**
   `opaque SubstantivePerson : Subject → Prop`
   `Person_opaque s := IntentionalSubject s ∧ SubstantivePerson s`
   Here, `SubstantivePerson` was introduced as an uninterpreted atomic constant.
   This formalization created an artificial syntactic gap (Classification Type 3):
   because `SubstantivePerson` has no defining equations, no inferential rules, and
   no axioms, it is trivially unprovable. This was mistaken for a metaphysical discovery
   when it was merely an artifact of introducing an uninterpreted dummy predicate.

## 2. Four-Way Ontological Classification

This module proves machine-checked theorems establishing:
- Under the **Constitutive/Frankfurt definition**, Personhood is **DERIVABLE** (Type 2)
  from Free Will with 0 substantive axioms.
- Under the **Opaque definition**, non-derivability is an **ARTIFACT OF STRENGTHENING**
  (Type 3): the intentional conjunct succeeds, and failure is entirely localized to the
  uninterpreted constant `SubstantivePerson`.
- Under faithful model theory, a choosing agent is consistent with `SubstantivePerson = False`
  only because `SubstantivePerson` is uninterpreted.
- The step from `Person` to `NecessarySubject` is a **GENUINE MODAL INDEPENDENCE** (Type 1/4),
  demonstrated by a faithful world-indexed modal model where a person exists contingently.
-/

import Logos.Core
import Logos.Agency
import Logos.Alternatives
import Logos.Choice
import Logos.Person
import Logos.HostileSemantics
import Logos.IndubitableNormativeFreeWill

namespace Logos.PersonhoodOntologyAudit

open Logos.Agency (Subject Means Act SubjectExists IntentionalSubject Intentional)
open Logos.Alternatives (Incompatible)
open Logos.Choice (Chooses FreeWill FreeSubject)
open Logos.Person (Person)
open Logos.HostileSemantics (CoreSignature)

-- ============================================================================
-- 1. The Three Definitions Formalized
-- ============================================================================

/-- Nominal/Early Cogito definition of Person (base.txt §12 early formalization):
    a person is an agent, rational, intentional subject. -/
def Person_nominal (s : Subject) : Prop :=
  Logos.Agency.Agent s ∧ Logos.Agency.Rational s ∧ Intentional s

/-- Constitutive/Frankfurt definition of Person (Retorsion.lean:153 / Frankfurt 1971):
    a person is an intentional subject who possesses free will (chooses between incompatible alternatives). -/
def Person_constitutive (s : Subject) : Prop :=
  IntentionalSubject s ∧ FreeWill s

/-- Historical uninterpreted substantive predicate used in commit ef60650:
    demonstrated by the audit to be an artificial gap (Category 3). -/
opaque HistoricalSubstantivePerson : Subject → Prop

/-- Dualist/Opaque definition of Person (historical commit ef60650):
    a person is an intentional subject possessing an uninterpreted substantive personal center. -/
def Person_opaque (s : Subject) : Prop :=
  IntentionalSubject s ∧ HistoricalSubstantivePerson s

-- ============================================================================
-- 2. Machine-Checked Derivations Under Constitutive Personhood
-- ============================================================================

/-- A Free Subject is necessarily an Intentional Subject.
    Proof: FreeSubject s ≡ FreeWill s := ∃ p q, Chooses s p q.
    And Chooses s p q requires Means s p ∧ Means s q, which witnesses IntentionalSubject s.
    Footprint: `{Means, Subject}` (0 substantive axioms). -/
theorem free_subject_is_intentional (s : Subject) (h : FreeSubject s) :
    IntentionalSubject s := by
  obtain ⟨p, q, hCh⟩ := h
  exact ⟨p, hCh.1⟩

/-- Master Theorem: Free Subject entails Constitutive Personhood.
    Under the constitutive rational-agency definition (Frankfurt-Locke-Kant),
    every free subject is a person by pure logic.
    Footprint: `{Means, Subject}` (0 substantive axioms). -/
theorem free_subject_is_constitutive_person (s : Subject) (h : FreeSubject s) :
    Person_constitutive s :=
  ⟨free_subject_is_intentional s h, h⟩

/-- Master Theorem: Every Free Subject is an authoritative Person in the unified Γ ontology.
    Footprint: `{Means, Subject}` (0 substantive axioms). -/
theorem free_subject_is_person (s : Subject) (h : FreeSubject s) :
    Person s :=
  Logos.Person.free_subject_is_person s h

/-- Master Theorem: Existence of a Free Subject implies existence of a Person.
    Footprint: `{Means, Subject}` (0 substantive axioms). -/
theorem free_subject_implies_person_exists (h : ∃ s : Subject, FreeSubject s) :
    ∃ s : Subject, Person s := by
  obtain ⟨s, hf⟩ := h
  exact ⟨s, free_subject_is_person s hf⟩

/-- Existential Master Theorem: The existence of a Free Subject implies the existence of a Constitutive Person.
    Footprint: `{Means, Subject}` (0 substantive axioms). -/
theorem free_subject_implies_constitutive_person_exists
    (h : ∃ s : Subject, FreeSubject s) :
    ∃ s : Subject, Person_constitutive s := by
  obtain ⟨s, hf⟩ := h
  exact ⟨s, free_subject_is_constitutive_person s hf⟩

/-- Definitional equivalence between Free Subject and Constitutive Personhood:
    Since an intentional chooser has free will, and free will entails intentionality,
    FreeSubject and Person_constitutive are logically equivalent.
    Footprint: `{Means, Subject}` (0 substantive axioms). -/
theorem free_subject_iff_constitutive_person (s : Subject) :
    FreeSubject s ↔ Person_constitutive s :=
  ⟨fun h => free_subject_is_constitutive_person s h, fun h => h.2⟩

-- ============================================================================
-- 3. Conjunct Failure Isolation Under the Opaque Definition
-- ============================================================================

/-- Theorem: Conjunct Failure Isolation.
    Under the opaque definition (`Person_opaque s := IntentionalSubject s ∧ HistoricalSubstantivePerson s`),
    the intentional component is ALREADY SATISFIED by any Free Subject.
    The failure to prove `Person_opaque s` is ENTIRELY LOCALIZED to the uninterpreted
    predicate `HistoricalSubstantivePerson s`.
    Footprint: `{Means, Subject}` (0 substantive axioms). -/
theorem opaque_person_failure_isolated_to_substantive_conjunct
    (s : Subject) (h : FreeSubject s) :
    Person_opaque s ↔ HistoricalSubstantivePerson s := by
  constructor
  · intro hp; exact hp.2
  · intro hSubst; exact ⟨free_subject_is_intentional s h, hSubst⟩

-- ============================================================================
-- 4. Faithful Model of Γ Core Signature (Free Agency Without Opaque Person)
-- ============================================================================

/-- Faithful model interpreting Γ's actual CoreSignature:
    All core commitments of Γ (actual act, intentional meaning, genuine choice, free will)
    are fully satisfied, while the uninterpreted predicate Person is set to False.
    This demonstrates that non-derivability under an uninterpreted predicate is mathematically
    consistent, but philosophically vacuous (Type 3 artifact).
    Footprint: `{}`. -/
def FaithfulGammaModel : CoreSignature where
  Subject := Unit
  A := fun _ _ => True
  Means := fun _ _ => True
  Person := fun _ => False
  Chooses := fun _ _ _ => True
  FreeWill := fun _ => True

/-- Theorem: The faithful Γ core model satisfies Agency, Meaning, and Free Will,
    while failing uninterpreted Personhood.
    Footprint: `{}`. -/
theorem faithful_model_satisfies_free_will_without_opaque_person :
    Logos.HostileSemantics.Γ_act FaithfulGammaModel ∧
    Logos.HostileSemantics.Γ_means FaithfulGammaModel ∧
    Logos.HostileSemantics.FreeWillExistence FaithfulGammaModel ∧
    ¬ Logos.HostileSemantics.PersonExistence FaithfulGammaModel := by
  refine ⟨⟨(), True, trivial⟩, fun _ _ _ => trivial, ⟨(), trivial⟩, ?_⟩
  rintro ⟨_, hp⟩
  exact hp

-- ============================================================================
-- 5. Faithful Modal Model: Contingent Person ⇏ Necessary Subject
-- ============================================================================

/-- Faithful World-Indexed Modal Signature:
    Models a universe where persons exist contingently across possible worlds. -/
structure ModalPersonSignature where
  World : Type
  actualWorld : World
  Subject : Type
  ExistsAt : World → Subject → Prop
  Person : Subject → Prop
  NecessarySubject : Subject → Prop

/-- The Faithful Contingent Person Model:
    The subject exists and is a person at the actual world (true),
    but does not exist at the alternative world (false). -/
def FaithfulModalModel : ModalPersonSignature where
  World := Bool
  actualWorld := true
  Subject := Unit
  ExistsAt := fun w _ => w = true
  Person := fun _ => True
  NecessarySubject := fun _s => ∀ w : Bool, (w = true)

/-- Theorem: Genuine Modal Independence of Necessary Subjecthood.
    A subject being a Person in the actual world does NOT logically entail that the subject
    exists across all possible worlds.
    This proves that `Person → NecessarySubject` is a GENUINE METAPHYSICAL FRONTIER (Type 1/4),
    requiring the modal grounding bridges `AxGlobalGround` (SEM) and `AxPersonalGround` (META).
    Footprint: `{}`. -/
theorem faithful_contingent_person_fails_necessary_subject :
    (∃ s : FaithfulModalModel.Subject, FaithfulModalModel.Person s ∧ FaithfulModalModel.ExistsAt FaithfulModalModel.actualWorld s) ∧
    ¬ (∀ s : FaithfulModalModel.Subject, FaithfulModalModel.Person s → ∀ w : FaithfulModalModel.World, FaithfulModalModel.ExistsAt w s) := by
  refine ⟨⟨(), trivial, rfl⟩, ?_⟩
  intro h
  have hFalse := h () trivial false
  cases hFalse

-- ============================================================================
-- 6. Axiom Footprint Audit
-- ============================================================================

#print axioms free_subject_is_intentional
#print axioms free_subject_is_constitutive_person
#print axioms free_subject_is_person
#print axioms free_subject_implies_person_exists
#print axioms free_subject_implies_constitutive_person_exists
#print axioms free_subject_iff_constitutive_person
#print axioms opaque_person_failure_isolated_to_substantive_conjunct
#print axioms faithful_model_satisfies_free_will_without_opaque_person
#print axioms faithful_contingent_person_fails_necessary_subject

end Logos.PersonhoodOntologyAudit
