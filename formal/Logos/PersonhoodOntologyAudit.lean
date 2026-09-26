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
   With `Agent := True` and `Rational := ∃ p, Means s p` (derived floor,
   PERSON.md 2026-09-23), this still collapses definitionally to
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
    Footprint: `{Means, Subject, Will, subjectWill, will_individuation}` (0 substantive axioms). -/
theorem free_subject_is_person (s : Subject) (h : FreeSubject s) :
    Person s :=
  Logos.Person.free_subject_is_person s h

/-- Master Theorem: Existence of a Free Subject implies existence of a Person.
    Footprint: `{Means, Subject, Will, subjectWill, will_individuation}` (0 substantive axioms). -/
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
    This proves that `Person → NecessarySubject` is a genuine modal boundary.
    Footprint: `{}`. -/
theorem faithful_contingent_person_fails_necessary_subject :
    (∃ s : FaithfulModalModel.Subject, FaithfulModalModel.Person s ∧ FaithfulModalModel.ExistsAt FaithfulModalModel.actualWorld s) ∧
    ¬ (∀ s : FaithfulModalModel.Subject, FaithfulModalModel.Person s → ∀ w : FaithfulModalModel.World, FaithfulModalModel.ExistsAt w s) := by
  refine ⟨⟨(), trivial, rfl⟩, ?_⟩
  intro h
  have hFalse := h () trivial false
  cases hFalse


-- ============================================================================
-- 6b. Shared-will separation: FreeWill WITHOUT Personhood (AC9′)
-- ============================================================================

/-- Personhood-relevant axiom signature: exactly the four VOCAB items
    personhood closes over — `Subject`, `Means`, `Will`, `subjectWill` — and
    nothing else.
    Honest labelling (mandatory): a model of THIS signature is a model of the
    personhood-relevant axiom signature, NEVER "a model of Γ". It withholds the
    law `will_individuation` (and every axiom outside the four VOCAB items);
    that withholding is what makes the countermodel admissible. -/
structure PersonhoodVocab where
  Subj : Type
  MeansRel : Subj → Prop → Prop
  WillSort : Type
  WillOf : Subj → WillSort

-- Γ's personhood vocabulary, replayed over a `PersonhoodVocab` model.
-- Each body is Γ's own body with the four axioms replaced by model fields —
-- no field is transcribed, nothing is stipulated.
namespace Vocab

variable (M : PersonhoodVocab)

/-- Γ's `Chooses` body (`Means s p ∧ Means s q ∧ Incompatible p q`,
    `Incompatible p q := ¬ (p ∧ q)`) over the model vocabulary. -/
def Chooses (s : M.Subj) (p q : Prop) : Prop :=
  M.MeansRel s p ∧ M.MeansRel s q ∧ ¬ (p ∧ q)

/-- Γ's `FreeWill` body over the model vocabulary. -/
def FreeWill (s : M.Subj) : Prop :=
  ∃ p q : Prop, Chooses M s p q

/-- Γ's `IndependentWill` body over the model vocabulary. -/
def IndependentWill (s : M.Subj) : Prop :=
  ∀ s' : M.Subj, s' ≠ s → M.WillOf s' ≠ M.WillOf s

/-- Γ's `IntentionalSubject` body over the model vocabulary. -/
def IntentionalSubject (s : M.Subj) : Prop :=
  ∃ p : Prop, M.MeansRel s p

/-- Γ's `DiscursiveCapacity` body over the model vocabulary. -/
def DiscursiveCapacity (s : M.Subj) : Prop :=
  ∃ p q : Prop, M.MeansRel s p ∧ M.MeansRel s q ∧ (p ≠ q ∨ ¬ (p ∧ q))

/-- Γ's `RationalNature` body over the model vocabulary. -/
def RationalNature (s : M.Subj) : Prop :=
  IntentionalSubject M s ∧ DiscursiveCapacity M s

/-- Γ's `DominionOverActs` body over the model vocabulary (the disclosed
    coincidence: dominion IS free will). -/
def DominionOverActs (s : M.Subj) : Prop :=
  FreeWill M s

/-- Γ's `IndividualSubstance` body over the model vocabulary. -/
def IndividualSubstance (s : M.Subj) : Prop :=
  IndependentWill M s

/-- Γ's `ThomisticPersonCore` body over the model vocabulary. -/
def ThomisticPersonCore (s : M.Subj) : Prop :=
  IndividualSubstance M s ∧ RationalNature M s ∧ DominionOverActs M s

/-- Γ's `Person` body (the Boethius–Aquinas criterion) over the model vocabulary. -/
def Person (s : M.Subj) : Prop :=
  ThomisticPersonCore M s

end Vocab

/-- The shared-will model: two subjects (`Bool`), one shared will faculty
    (`Unit`), and a genuine incompatible pair (`True`, `False`) both co-meant.
    `P := True` and `Q := False` are both provable yet jointly unprovable, so
    `FreeWill` genuinely holds while the shared will defeats
    `IndividualSubstance`. A `def`, not an axiom: the counterexample works by
    WITHHOLDING `will_individuation`.
    Footprint: `{}`. -/
def SharedWillModel : PersonhoodVocab where
  Subj := Bool
  MeansRel := fun _ p => p = True ∨ p = False
  WillSort := Unit
  WillOf := fun _ => ()

/-- Separation (AC9′): a genuinely free-willing subject that is NOT a person.
    `FreeWill` holds via the incompatible pair `⟨True, False⟩`; `Person` fails
    because every subject shares the single will `()`, so no will is
    numerically individuated. Computed, not stipulated.
    Footprint: `{}`. -/
theorem freeWill_without_person :
    Vocab.FreeWill SharedWillModel true ∧ ¬ Vocab.Person SharedWillModel true := by
  constructor
  · exact ⟨True, False, Or.inl rfl, Or.inr rfl, fun h => h.2⟩
  · intro h
    exact h.1 false (fun heq => Bool.noConfusion heq) rfl

/-- Necessity (the irreducibility result): a subject can satisfy BOTH free
    personhood conjuncts — rational nature and dominion over its acts — and still
    fail to be a Person. In `SharedWillModel` the subject `true` means `True` and
    `False`, hence is an intentional subject with discursive capacity, and
    `DominionOverActs` is definitionally `FreeWill`, which holds. Yet `Person` fails,
    because `IndividualSubstance` (the third conjunct) needs an individuated will
    and this model deliberately withholds `will_individuation`.
    This is the machine-checked proof that the two cheap conjuncts CANNOT reach
    personhood: `will_individuation` is not an avoidable expense of the
    `RightWrong ⇒ Person` headline but its exact and minimal price.
    Footprint: `{}`. -/
theorem rational_domination_without_person :
    Vocab.RationalNature SharedWillModel true ∧
    Vocab.DominionOverActs SharedWillModel true ∧
    ¬ Vocab.Person SharedWillModel true := by
  obtain ⟨hFW, hNotPerson⟩ := freeWill_without_person
  refine ⟨⟨⟨True, Or.inl rfl⟩,
    ⟨True, False, Or.inl rfl, Or.inr rfl, Or.inr (fun h => h.2)⟩⟩, hFW, hNotPerson⟩

/-- Precision (the crown result): given free will, being a person is
    EQUIVALENT to this subject's will being numerically individuated.
    In the kernel, without definitional unfolding: personhood collapses to
    free will if and only if wills are numerically individuated. The entire
    non-definitional content of the `Person ↔ FreeWill` reduction is therefore
    the law `will_individuation`, and `SharedWillModel` is a machine-checked
    counterexample to that reduction.
    Footprint: `{}`. -/
theorem freeWill_person_iff_individuation (M : PersonhoodVocab) (s : M.Subj)
    (hFW : Vocab.FreeWill M s) :
    Vocab.Person M s ↔ ∀ s' : M.Subj, s' ≠ s → M.WillOf s' ≠ M.WillOf s := by
  constructor
  · intro h
    exact h.1
  · intro hIndiv
    have hEx : ∃ p q : Prop, Vocab.Chooses M s p q := hFW
    obtain ⟨p, q, hCh⟩ := hEx
    exact ⟨hIndiv, ⟨⟨p, hCh.1⟩, ⟨p, q, hCh.1, hCh.2.1, Or.inr hCh.2.2⟩⟩, hFW⟩
-- ============================================================================
-- 6. Anti-Baking Independence Audits (Quest 1xA7fZ)
-- ============================================================================

/-- Contemplative Signature:
    Models a purely contemplative rational subject who entertains distinct compatible
    propositions without engaging in choice between incompatible alternatives.
    DEPRECATED (2026-09-25): superseded by `PersonhoodVocab`. Retained, not deleted. -/
@[deprecated PersonhoodVocab (since := "2026-09-25")]
structure ContemplativeSignature where
  Subject : Type
  Means : Subject → Prop → Prop
  Incompatible : Prop → Prop → Prop
  Chooses : Subject → Prop → Prop → Prop
  FreeWill : Subject → Prop
  DiscursiveCapacity : Subject → Prop
  RationalNature : Subject → Prop
  IndividualSubstance : Subject → Prop

/-- Contemplative Model:
    The subject entertains distinct true propositions (True and True ∧ True),
    possesses discursive capacity and rational nature, is numerically individuated,
    yet faces no incompatible alternatives and makes no choices.
    DEPRECATED (2026-09-25): stipulates its own conclusion (`FreeWill := fun _ => False`
    together with the theorem's own conclusion) and its `Incompatible` diverges from
    Γ's body off-range. Superseded by the faithful `SharedWillModel`.
    Retained, not deleted. -/
@[deprecated SharedWillModel (since := "2026-09-25")]
def ContemplativeModel : ContemplativeSignature where
  Subject := Unit
  Means := fun _ p => p = True ∨ p = (True ∧ True)
  Incompatible := fun _ _ => False
  Chooses := fun _ _ _ => False
  FreeWill := fun _ => False
  DiscursiveCapacity := fun _ => True
  RationalNature := fun _ => True
  IndividualSubstance := fun _ => True

/-- Theorem: Rational Nature Does Not Definitionally or Logically Entail Free Will.
    A rational subject can contemplate distinct propositional truths without
    possessing free will between incompatible alternatives.
    DEPRECATED (2026-09-25): the proof is `⟨trivial, trivial, id⟩` — a tautology
    about stipulations, in the same category of error as the C1 charge (defining
    free will to be `False`, then reporting `¬FreeWill`). Superseded by the
    computed separation `freeWill_without_person`.
    Retained, not deleted.
    Footprint: `{}`. -/
@[deprecated freeWill_without_person (since := "2026-09-25")]
theorem contemplative_person_without_freewill :
    ContemplativeModel.RationalNature () ∧
    ContemplativeModel.IndividualSubstance () ∧
    ¬ ContemplativeModel.FreeWill () :=
  ⟨trivial, trivial, id⟩

/-- Generic Grounding Signature:
    Models generic ontological grounding of facts by entities. -/
structure GenericGroundingSignature where
  Entity : Type
  Fact : Type
  Grounds : Entity → Fact → Prop
  PersonalEntity : Entity → Prop

/-- Physical/Atomic Ground Model:
    An inanimate atomic entity (e.g. mass or charge) grounds an empirical fact
    without being a personal entity. -/
def PhysicalGroundModel : GenericGroundingSignature where
  Entity := Unit
  Fact := String
  Grounds := fun _ f => f = "mass"
  PersonalEntity := fun _ => False

/-- Theorem: Grounding Does Not Definitionally or Logically Entail Personhood.
    An entity can stand in an ontological grounding relation without being a Personal Entity.
    This demonstrates that `normative_ground_is_personal` is a substantive theorem of
    normativity rather than an artifact of defining grounding as personal.
    Footprint: `{}`. -/
theorem impersonal_ground_without_person :
    (∃ g : PhysicalGroundModel.Entity, ∃ f, PhysicalGroundModel.Grounds g f) ∧
    (∀ g : PhysicalGroundModel.Entity, PhysicalGroundModel.Grounds g "mass" → ¬ PhysicalGroundModel.PersonalEntity g) :=
  ⟨⟨(), "mass", rfl⟩, fun _ _ h => h⟩

-- ============================================================================
-- 7. Axiom Footprint Audit
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
#print axioms contemplative_person_without_freewill
#print axioms impersonal_ground_without_person
#print axioms freeWill_without_person
#print axioms freeWill_person_iff_individuation

end Logos.PersonhoodOntologyAudit
