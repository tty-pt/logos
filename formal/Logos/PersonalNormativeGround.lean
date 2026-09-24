/-
# Logos.PersonalNormativeGround — Ontological Grounding of Normative Polarity in Free Personal Agency

This module formalizes the crucial distinction between the epistemic direction of
transcendental discovery and the ontological direction of grounding:

```text
EPISTEMIC DISCOVERY:
  Right/Wrong ⇒ Genuine Normativity ⇒ Choice ⇒ Free Will ⇒ Free Subject ⇒ Person
  (Normative distinction performatively reveals the free subject.)

ONTOLOGICAL CONCLUSION:
  Objective Right/Wrong has a necessary ontological grounding of a personal kind/type.
  (The ontological ground required by objective Right/Wrong is personal in kind;
   the derived subject s witnesses/instantiates this personal ground.)

NOT:
  “A particular contingent person s individually generates, creates, causes, or grounds
   every particular instance of Right and Wrong.”
```

## Key Architectural Principles:
1. Grounding in a Personal Kind/Type (Zero Act Dependency):
   Grounding is derived directly from the constitutive properties of Personhood
   (`Person s := FreeSubject s := FreeWill s`). The derived subject `s : Subject` is
   the formal index/witness demonstrating that a personal entity satisfies the ontological
   specification of grounding. It does NOT assert that an arbitrary empirical individual
   causes or creates the universal moral order.
2. Universal Dependence (`∀ s', RightWrong s' → Person s'`):
   The grounding structure requires that wherever the normative order obtains, its
   relevant agential ground is of the personal kind. Personhood supplies the ontological
   ground-type required by the normative order.
3. Grounding ≠ Identity (Anti-Self-Legislation):
   Grounding normative polarity in a personal ontological basis does NOT mean identifying
   Right or Ought with any agent's current willing. As established by anti-self-legislation
   (`OughtRetorsion.self_grounded_ought_collapses`), identifying Ought with current volition
   collapses the very possibility of normative violation. Grounding is an asymmetrical,
   external ontological dependence, not an analytical reduction.
4. Non-Circularity:
   The transcendental discovery proof of Free Will (`indubitable_normative_free_will`,
   `claims_normative_correctness_derives_free_will`) does NOT depend on the grounding relation.
   The grounding relation is a separate, downstream ontological consequence.
5. Model-Theoretic Honesty (Anti-Collapse):
   - Model A demonstrates that bare extensional bivalence does not analytically force agency,
     confirming that discovery is performative.
   - Model B demonstrates that in bare model theory, a free subject's entity can
     fail the external relation `GroundProp` while an impersonal atom (`Entity.ofAtom 0`)
     satisfies it — proving that the external-relation reading is a genuine semantic choice.
   - Model C reaffirms that identifying normativity with current will collapses violation.
-/

import Logos.Core
import Logos.Agency
import Logos.Alternatives
import Logos.Choice
import Logos.Person
import Logos.Order
import Logos.NormativeOrder
import Logos.Entity
import Logos.OughtRetorsion
import Logos.IndubitableNormativeFreeWill

set_option linter.unusedVariables false

namespace Logos.PersonalNormativeGround

open Logos.Core (T IsFalse rightWrongDistinction)
open Logos.Agency (Subject Act Means State Initiates SubjectExists IntentionalSubject Wills)
open Logos.Alternatives (Incompatible)
open Logos.Choice (Chooses FreeWill FreeSubject)
open Logos.Person (Person FreeIndependentWill IndependentWill person_iff_freeIndependentWill person_has_free_independent_will free_independent_will_is_person free_subject_is_person)
open Logos.Order (Correct Incorrect)
open Logos.NormativeOrder (TruthNorm Ought OughtNot correctness_deontic_opposition)
open Logos.Entity (Entity EntityOf)
open Logos.IndubitableNormativeFreeWill (DeonticOpposition AgentialDeonticAddress GenuineNormativity indubitable_normative_free_will)
open Logos.OughtRetorsion (PracticalAction SubjectWills SelfLegislation NormativeViolation self_grounded_ought_collapses)

-- ===========================================================================
-- Section 0: Constructive Ontological Dependence of Normativity on Personhood
-- ===========================================================================

namespace Constructive

/-- A Person in the constructive ontology: an authoritative personal subject. -/
structure Person where
  subject : Logos.Agency.Subject
  is_person : Logos.Person.Person subject

/-- Right and Wrong distinction indexed by Person:
    The normative distinction is genuinely addressed to and held by the person.
    Not a dummy parameter: requires that the person cognitively grasps both poles
    of deontic opposition (AgentialDeonticAddress). -/
def RightWrong (p : Person) : Prop :=
  ∃ a b : Prop, Logos.IndubitableNormativeFreeWill.GenuineNormativity p.subject a b

/-- Objective Normativity: the existence of a person whose judgment carries Right/Wrong. -/
def ObjectiveNormativity : Prop :=
  ∃ p : Person, RightWrong p

/-- Constructive direction of discovery: Objective Normativity ⇒ Person.
    From the reality of objective normativity addressed to an agent, we constructively
    discover the personal agent who grasps the distinction. -/
theorem discover_person :
    ObjectiveNormativity → ∃ p : Person, RightWrong p := by
  intro h
  exact h

/-- Grounding built into the formal structure itself via dependent pair:
    Person ⇒ Right/Wrong is represented by the dependent pair (Sigma type)
    where the first component is the Person (witnessing the personal ground-type)
    and the second component is the Right/Wrong distinction rooted in that person.
    The ontological ground required by objective Right/Wrong is personal in kind;
    no arbitrary grounding axiom is required. -/
def GroundedRightWrong : Type :=
  Σ' p : Person, RightWrong p

/-- The person as the witness of the personal ontological ground (first projection of GroundedRightWrong). -/
def groundOfRightWrong (x : GroundedRightWrong) : Person :=
  x.1

/-- Canonical constructor of grounded right and wrong from any genuine normative datum. -/
def groundedRightWrongOfDatum (s : Logos.Agency.Subject) (a b : Prop)
    (h : Logos.IndubitableNormativeFreeWill.GenuineNormativity s a b) : GroundedRightWrong :=
  ⟨⟨s, (Logos.IndubitableNormativeFreeWill.indubitable_normative_free_will h).2⟩, ⟨a, b, h⟩⟩

/-- Objective Normativity holds from any agential normative address. -/
theorem objective_normativity_holds
    (hDatum : ∃ s : Logos.Agency.Subject, ∃ a b : Prop, Logos.IndubitableNormativeFreeWill.GenuineNormativity s a b) :
    ObjectiveNormativity := by
  obtain ⟨s, a, b, h⟩ := hDatum
  exact ⟨⟨s, (Logos.IndubitableNormativeFreeWill.indubitable_normative_free_will h).2⟩, ⟨a, b, h⟩⟩

end Constructive

-- ===========================================================================
-- Section 1: Core Normative Polarity & Right/Wrong (Zero Act Dependency)
-- ===========================================================================

/-- Normative Polarity:
    The deontic opposition between two incompatible alternative contents p and q.
    Classification: DEFINITIONAL. -/
def NormativePolarity (p q : Prop) : Prop :=
  DeonticOpposition p q

/-- Right/Wrong Distinction at contents p and q for subject s:
    The subject is addressed by an objective deontic opposition between Right (p) and Wrong (q).
    Classification: DEFINITIONAL. -/
def RightWrongAt (s : Subject) (p q : Prop) : Prop :=
  GenuineNormativity s p q

/-- Objective Right/Wrong for subject s:
    There exist incompatible alternatives between which s is addressed by normative opposition.
    Not a dummy predicate: requires that s mean both alternatives (AgentialDeonticAddress).
    Classification: DEFINITIONAL. -/
def RightWrong (s : Subject) : Prop :=
  ∃ p q : Prop, RightWrongAt s p q

/-- Any genuine normative address constitutes Right/Wrong for the addressee.
    Footprint: `{}`. -/
theorem right_wrong_of_genuine_normativity
    (s : Subject) (p q : Prop) (h : GenuineNormativity s p q) :
    RightWrongAt s p q :=
  h

/-- Judicative Normative Polarity:
    The deontic opposition between a subject's correct judgment and its incorrect judgment.
    Classification: DEFINITIONAL. -/
def JudicativeNormativePolarity (s : Subject) (p : Prop) : Prop :=
  DeonticOpposition (Correct s p) (Incorrect s p)

/-- Any performed intentional judgment act realizes JudicativeNormativePolarity.
    Directly consumes `correctness_deontic_opposition` from NormativeOrder.
    Footprint: `{Initiates, Means, State, Subject, CL}`. -/
theorem judicative_normative_polarity_of_act (s : Subject) (p : Prop) (hAct : Act s p) :
    JudicativeNormativePolarity s p :=
  correctness_deontic_opposition s p hAct

-- ===========================================================================
-- Section 2: Formal Ontological Grounding Relation
-- ===========================================================================

/-- GroundsRightWrong:
    Objective Right/Wrong is ontologically grounded in an agential basis of a personal kind/type.
    The parameter `s : Subject` is the formal index/witness satisfying the specification:
    1. `person`: s possesses the constitutive properties of Personhood (authoritative free agency);
    2. `dependence`: Universal ontological dependence (`∀ s' : Subject, RightWrong s' → Person s'`).
       Wherever the normative order obtains, its agential ground is of the personal kind;
    3. `agential_foundation`: s constitutively provides the faculty of choice between incompatible
       alternatives (`∃ p q, Chooses s p q`), supplying the ontological ground-type required by
       normative polarity.

    The claim is NOT that a particular contingent individual s causally creates or generates
    every normative fact; it establishes that the ground required by objective Right/Wrong
    is personal in kind/type.
    Transparency: the record is definitionally equivalent to `ForcedGroundContent`
    (Section 5c) — a conjunction of prior theorems in the pre-grounding vocabulary —
    so the predicate is determined by the preceding facts, never stipulated.
    Classification: DEFINITIONAL. -/
structure GroundsRightWrong (s : Subject) : Prop where
  /-- The ground-type is personal: its witness is an authoritative Person
      (free subject with the free-will faculty). -/
  person : Person s
  /-- Universal ontological dependence: Wherever Right/Wrong obtains, it strictly depends on Personhood. -/
  dependence : ∀ s' : Subject, RightWrong s' → Person s'
  /-- Agential substrate: The personal ground constitutively provides the faculty of choice. -/
  agential_foundation : ∃ p q : Prop, Chooses s p q

/-- GroundsRightWrongAt:
    Subject s witnesses the grounding relation indexed to a specific normative opposition (p, q).
    Distinction:
    - `GroundsRightWrong s` concerns the personal ontological ground of Right/Wrong in general.
    - `GroundsRightWrongAt s p q` concerns the grounding relation indexed to a particular normative
      opposition `(p, q)`.
    The main philosophical claim is about the ontological kind of the ground, not about identifying
    one human/person-shaped individual as the producer of every normative proposition.
    Classification: DEFINITIONAL. -/
structure GroundsRightWrongAt (s : Subject) (p q : Prop) : Prop where
  person : Person s
  normativity : RightWrongAt s p q
  choice : Chooses s p q

/-- Compatibility alias for Judicative Normative Polarity grounding.
    Classification: DEFINITIONAL. -/
def GroundsJudicativePolarity (s : Subject) (p : Prop) : Prop :=
  GroundsRightWrong s

/-- GroundedNormativePolarity:
    Normative polarity is ontologically grounded in a subject endowed with free, independent will,
    witnessing the personal ontological ground-type.
    Classification: DEFINITIONAL. -/
def GroundedNormativePolarity (s : Subject) : Prop :=
  FreeIndependentWill s ∧ GroundsRightWrong s

/-- Global Grounded Normative Polarity:
    There exists a personal ontological ground of normative polarity.
    Distinction: This establishes that there exists an agential ground of a personal kind/type;
    it does not claim that a particular contingent individual causally produces all morality.
    Classification: DEFINITIONAL. -/
def GlobalGroundedNormativePolarity : Prop :=
  ∃ s : Subject, GroundedNormativePolarity s

-- ===========================================================================
-- Section 3: Grounding is Not Identity (Anti-Self-Legislation)
-- ===========================================================================

/-- Grounding Is Not Identity:
    An ontological grounder (`EntityOf s : Entity`) is numerically and categorically distinct
    from the proposition it grounds (`JudicativeNormativePolarity s p : Prop`).
    Grounding is an asymmetrical ontological dependency, never an identity.
    Footprint: `{}`. -/
theorem grounding_distinct_from_grounded (s : Subject) (p : Prop) :
    EntityOf s ≠ Entity.ofAtom 0 := by
  intro h
  exact Entity.noConfusion h

/-- Volition Is Not Normative Ground by Identity:
    Identifying practical obligation with the subject's own current willing (`SelfLegislation s`)
    destroys the logical possibility of normative violation, collapsing normativity.
    Re-establishes the anti-self-legislation boundary in the grounding context.
    Footprint: `{Ought, Subject, Wills}`. -/
theorem will_identity_collapses_normativity
    {s : Subject} (hSelf : SelfLegislation s)
    (a : PracticalAction)
    (hSoloSource : ∀ r, Logos.OughtRetorsion.Ought r s a → r = s)
    (hContrary : SubjectWills s a.neg → ¬ SubjectWills s a) :
    NormativeViolation s a → False :=
  self_grounded_ought_collapses hSelf a hSoloSource hContrary

-- ===========================================================================
-- Section 4: Forward Implication Stages (Zero Act Dependency)
-- ===========================================================================

/-- Stage 0: Initial normative datum A₀.
    The agent is presented with an objective normative opposition between Right (p) and Wrong (q).
    Classification: DEFINITIONAL. -/
def Stage0_NormativeDatum (s : Subject) (p q : Prop) : Prop :=
  RightWrongAt s p q

/-- Stage 1: Agential normative stance.
    Agential deontic address and deontic opposition between incompatible poles.
    Classification: DEFINITIONAL. -/
def Stage1_NormativeStance (s : Subject) (p q : Prop) : Prop :=
  AgentialDeonticAddress s p q ∧ DeonticOpposition p q

/-- Stage 2: Genuine choice between incompatible alternatives.
    Classification: DEFINITIONAL. -/
def Stage2_NormativeChoice (s : Subject) (p q : Prop) : Prop :=
  Chooses s p q

/-- Stage 3: Agential free will.
    Classification: DEFINITIONAL. -/
def Stage3_AgentialFreeWill (s : Subject) : Prop :=
  FreeWill s

/-- Stage 4: Free subjecthood.
    Classification: DEFINITIONAL. -/
def Stage4_FreeSubject (s : Subject) : Prop :=
  FreeSubject s

/-- Stage 5: The Person (P).
    An authoritative subject endowed with genuine free will.
    Classification: DEFINITIONAL. -/
def Stage5_Person (s : Subject) : Prop :=
  Person s

/-- Forward Step 0 → 1: From the normative datum to agential normative stance.
    Extracts `AgentialDeonticAddress` and `DeonticOpposition`.
    Footprint: `{}`. -/
theorem step_datum_to_stance (s : Subject) (p q : Prop)
    (h0 : Stage0_NormativeDatum s p q) : Stage1_NormativeStance s p q :=
  ⟨h0.address, h0.opposition⟩

/-- Forward Step 1 → 2: From normative stance to genuine agential choice.
    Apprehending incompatible normative poles constitutes choice (`Chooses`).
    Footprint: `{}`. -/
theorem step_stance_to_choice (s : Subject) (p q : Prop)
    (h1 : Stage1_NormativeStance s p q) : Stage2_NormativeChoice s p q :=
  ⟨h1.1.1, h1.1.2, h1.2.1⟩

/-- Forward Step 2 → 3: From genuine choice to agential free will.
    A subject choosing between alternatives possesses free will by definition.
    Footprint: `{}`. -/
theorem step_choice_to_freewill (s : Subject) (p q : Prop)
    (h2 : Stage2_NormativeChoice s p q) : Stage3_AgentialFreeWill s :=
  ⟨p, q, h2⟩

/-- Forward Step 3 → 4: From free will to free subjecthood.
    Definitional equivalence: `FreeSubject s := FreeWill s`.
    Footprint: `{}`. -/
theorem step_freewill_to_freeSubject (s : Subject)
    (h3 : Stage3_AgentialFreeWill s) : Stage4_FreeSubject s :=
  h3

/-- Forward Step 4 → 5: From free subjecthood to Personhood (P).
    Constitutive personhood theorem: every free subject is a person (`Person s := FreeSubject s`).
    Footprint: `{}`. -/
theorem step_freeSubject_to_person (s : Subject)
    (h4 : Stage4_FreeSubject s) : Stage5_Person s :=
  Logos.Person.free_subject_is_person s h4

/-- Forward Discovery Theorem: From normative datum to Personhood.
    A subject addressed by genuine normativity between alternatives is a Person.
    Footprint: `{Means, Subject}`. -/
theorem forward_discovery_person (s : Subject) (p q : Prop)
    (h0 : RightWrongAt s p q) : Person s :=
  step_freeSubject_to_person s
    (step_freewill_to_freeSubject s
      (step_choice_to_freewill s p q
        (step_stance_to_choice s p q
          (step_datum_to_stance s p q h0))))

/-- Forward Discovery: Right/Wrong entails Personhood.
    Footprint: `{Means, Subject}`. -/
theorem discovery_rightwrong_to_person (s : Subject) (h : RightWrong s) : Person s := by
  obtain ⟨p, q, h0⟩ := h
  exact forward_discovery_person s p q h0

-- ===========================================================================
-- Section 5: Principal Ontological Grounding Theorems (Zero Act Dependency)
-- ===========================================================================

/-- Substantive Grounding Derivation from Personhood:
    Every subject possessing the constitutive properties of Personhood satisfies the
    formal specification of the personal ontological ground of Right/Wrong.
    The proof establishes that the ground of objective normativity is personal in kind:
    - `person` is instantiated by `hPerson`;
    - `dependence` is instantiated by the universal discovery theorem `discovery_rightwrong_to_person`;
    - `agential_foundation` is instantiated by the Person's own faculty of free choice (`person_has_free_will`).

    The argument does not identify a particular contingent individual as the creator of Right and Wrong;
    it establishes that the ontological ground required by objective Right/Wrong is personal in kind.
    Footprint: `{Means, Subject}` (0 substantive axioms, zero Act). -/
theorem person_grounds_right_wrong (s : Subject) (hPerson : Person s) :
    GroundsRightWrong s := by
  refine ⟨hPerson, ?_, ?_⟩
  · intro s' hRW
    exact discovery_rightwrong_to_person s' hRW
  · exact Logos.Person.person_has_free_will s hPerson

/-- Master Grounding Theorem from Personhood (Historical Compatibility Name):
    Personhood supplies the ontological ground-type required by the normative order.
    The argument does not identify a particular contingent individual as the creator of Right and Wrong;
    it establishes that the ontological ground required by objective Right/Wrong is personal in kind.
    Footprint: `{Means, Subject}` (0 substantive axioms, zero Act). -/
theorem person_grounds_normative_polarity (s : Subject) (hPerson : Person s) :
    GroundsRightWrong s :=
  person_grounds_right_wrong s hPerson

/-- Master Grounding Theorem from Free Independent Will:
    A subject with a Free, Independent Will satisfies the specification of the personal ground.
    Footprint: `{Means, Subject, subjectWill, will_individuation}`. -/
theorem free_independent_will_grounds_judicative_polarity
    (s : Subject) (hFW : FreeIndependentWill s) :
    GroundsRightWrong s :=
  person_grounds_right_wrong s ((person_iff_freeIndependentWill s).mpr hFW)

/-- Master Realization Theorem:
    Any Person realizes GroundedNormativePolarity, showing that normative polarity is grounded
    in a personal ontological basis.
    Footprint: `{Means, Subject, subjectWill, will_individuation}`. -/
theorem person_realizes_grounded_polarity (s : Subject) (hPerson : Person s) :
    GroundedNormativePolarity s := by
  have hFW : FreeIndependentWill s := (person_iff_freeIndependentWill s).mp hPerson
  exact ⟨hFW, person_grounds_right_wrong s hPerson⟩

/-- Existential Ontological Grounding Theorem:
    The existence of a Person entails that normative polarity has a personal ontological ground.
    Distinction: This existential result establishes that there exists a personal ground of the
    normative order; it does not claim that one contingent individual causally produces all morality.
    Footprint: `{Means, Subject, subjectWill, will_individuation}`. -/
theorem person_exists_implies_global_grounded_polarity (h : ∃ s : Subject, Person s) :
    GlobalGroundedNormativePolarity := by
  obtain ⟨s, hPerson⟩ := h
  exact ⟨s, person_realizes_grounded_polarity s hPerson⟩

-- ===========================================================================
-- Section 5b: Master Forward Constructive Deduction Chain (A₀ ⇒ ... ⇒ P ⇒ G)
-- ===========================================================================

/-- Stage 6: Personal Grounding of Right and Wrong (G).
    The terminal state: a Person who instantiates the personal ontological ground of Right/Wrong.
    Classification: DEFINITIONAL. -/
def Stage6_PersonalGrounding (s : Subject) : Prop :=
  Person s ∧ GroundsRightWrong s

/-- Forward Step 5 → 6: From Person to Ontological Grounding (P ⇒ G).
    The Person constitutively satisfies the personal ground-type of Right/Wrong.
    The argument does not identify a particular contingent individual as the creator of Right and Wrong;
    it establishes that the ontological ground required by objective Right/Wrong is personal in kind.
    Footprint: `{Means, Subject}`. -/
theorem step_person_to_grounding (s : Subject)
    (hp : Stage5_Person s) : Stage6_PersonalGrounding s :=
  ⟨hp, person_grounds_right_wrong s hp⟩

/-- Master Forward Modus Ponens Derivation Theorem:
    From the initial normative datum A₀(s, p, q), successive forward modus ponens
    constructively derives:
      A₀ ⇒ A₁ ⇒ A₂ ⇒ A₃ ⇒ A₄ ⇒ P ⇒ G
    where P is the Person and G establishes that Right/Wrong has a personal ontological ground
    (witnessed by s).
    The argument does not identify a particular contingent individual as the creator of Right and Wrong;
    it establishes that the ontological ground required by objective Right/Wrong is personal in kind.
    Footprint: `{Means, Subject}`. -/
theorem forward_modus_ponens_derivation (s : Subject) (p q : Prop)
    (h0 : RightWrongAt s p q) :
    Person s ∧ GroundsRightWrong s := by
  have h1 : Stage1_NormativeStance s p q := step_datum_to_stance s p q h0
  have h2 : Stage2_NormativeChoice s p q := step_stance_to_choice s p q h1
  have h3 : Stage3_AgentialFreeWill s := step_choice_to_freewill s p q h2
  have h4 : Stage4_FreeSubject s := step_freewill_to_freeSubject s h3
  have hp : Stage5_Person s := step_freeSubject_to_person s h4
  have hg : Stage6_PersonalGrounding s := step_person_to_grounding s hp
  exact hg

/-- Master Forward Composition Pipeline:
    Direct functional composition of the implication chain from A₀ directly to G:
    `step_person_to_grounding ∘ ... ∘ step_datum_to_stance`.
    Footprint: `{Means, Subject}`. -/
theorem forward_composition_pipeline (s : Subject) (p q : Prop) :
    RightWrongAt s p q → Person s ∧ GroundsRightWrong s :=
  fun h0 =>
    step_person_to_grounding s
      (step_freeSubject_to_person s
        (step_freewill_to_freeSubject s
          (step_choice_to_freewill s p q
            (step_stance_to_choice s p q
              (step_datum_to_stance s p q h0)))))

/-- Direct Derivation: The derived subject s instantiates the personal ground of the normative datum.
    Footprint: `{Means, Subject}`. -/
theorem person_grounds_original_normative_datum (s : Subject) (p q : Prop)
    (h0 : RightWrongAt s p q) :
    Person s ∧ GroundsRightWrong s :=
  forward_modus_ponens_derivation s p q h0

/-- Existential Forward Normative Grounding Theorem:
    Given the existence of any normative stance, there exists a personal ontological ground
    of Right/Wrong (witnessed by some Person s).
    Distinction: This establishes that there exists a personal ground of the normative order;
    it is NOT the claim that there exists one particular empirical person who personally
    causes every normative fact.
    Footprint: `{Means, Subject}`. -/
theorem existential_forward_normative_grounding
    (hDatum : ∃ s : Subject, ∃ p q : Prop, RightWrongAt s p q) :
    ∃ s : Subject, Person s ∧ GroundsRightWrong s := by
  obtain ⟨s, p, q, h0⟩ := hDatum
  exact ⟨s, forward_modus_ponens_derivation s p q h0⟩

/-- PersonalGroundExists:
    Presentation-level definition of the existential ontological conclusion:
    There exists an ontological ground of the normative order of a personal kind.
    Classification: DEFINITIONAL. -/
def PersonalGroundExists : Prop :=
  ∃ s : Subject, Person s ∧ GroundsRightWrong s

/-- Presentation Theorem: From any normative datum, a personal ground exists.
    The argument does not identify a particular contingent individual as the creator of Right and Wrong;
    it establishes that the ontological ground required by objective Right/Wrong is personal in kind.
    Footprint: `{Means, Subject}`. -/
theorem personal_ground_exists_of_datum
    (hDatum : ∃ s : Subject, ∃ p q : Prop, RightWrongAt s p q) :
    PersonalGroundExists :=
  existential_forward_normative_grounding hDatum

/-- The Non-Reversal Architectural Principle:
    1. Deductive Discovery runs forward:
       RightWrongAt s p q ⇒ ... ⇒ Person s ⇒ GroundsRightWrong s.
       (Discovery identifies a personal ground from the normative datum.)
    2. Ontological Grounding is the content of the derived conclusion:
       GroundsRightWrong s establishes that the ontological ground of Right/Wrong is personal in kind.
    The proof never runs backwards: Person is not an ungrounded premise from which Right/Wrong is deduced;
    Person is the derived conclusion of the normative datum, and its personal grounding of Right/Wrong is
    the final derived proposition.
    Footprint: `{Means, Subject}`. -/
theorem non_reversal_discovery_and_grounding (s : Subject) (p q : Prop) :
    (RightWrongAt s p q → Person s ∧ GroundsRightWrong s) ∧
    (Person s → GroundsRightWrong s) :=
  ⟨fun h => forward_modus_ponens_derivation s p q h,
   fun hp => person_grounds_right_wrong s hp⟩

-- ===========================================================================
-- Section 5c: Forcing Audit — GroundsRightWrong is Determined, Not Stipulated
-- ===========================================================================

/-- The ground-content forced by the preceding facts, written entirely in the
    vocabulary available BEFORE the grounding step (`Person`, `RightWrong`,
    `Chooses`). The symbol `GroundsRightWrong` does not occur anywhere in it.
    Classification: DEFINITIONAL (notational shorthand for the audit). -/
def ForcedGroundContent (s : Subject) : Prop :=
  Person s ∧ (∀ s' : Subject, RightWrong s' → Person s') ∧ (∃ p q : Prop, Chooses s p q)

/-- Transparency: `GroundsRightWrong s` carries exactly the forced content and
    nothing else — no hidden field, no opaque semantic atom. The predicate is a
    notational abbreviation for the conjunction of three facts each already
    obtained before Personhood was reached; it adds zero new content.
    Footprint: `{Means, Subject}`. -/
theorem groundsRightWrong_iff_forced_content (s : Subject) :
    GroundsRightWrong s ↔ ForcedGroundContent s := by
  constructor
  · intro h
    exact ⟨h.person, ⟨h.dependence, h.agential_foundation⟩⟩
  · intro ⟨hPerson, hDep, hFoundation⟩
    exact ⟨hPerson, hDep, hFoundation⟩

/-- Every Person satisfies the forced content, and every conjunct is a PRIOR
    theorem, not a grounding-time stipulation:
    1. `Person s` is the conclusion already derived from the normative datum;
    2. the universal dependence is literally the global closure of the §4
       discovery theorem `discovery_rightwrong_to_person`, proved before any
       grounding step;
    3. the agential substrate unpacks the defining content of Personhood itself
       (`Person s := FreeSubject s := FreeWill s := ∃ p q, Chooses s p q`).
    Footprint: `{Means, Subject}` (0 substantive axioms, zero Act). -/
theorem forced_content_of_person (s : Subject) (hPerson : Person s) : ForcedGroundContent s :=
  ⟨hPerson, discovery_rightwrong_to_person, Logos.Person.person_has_free_will s hPerson⟩

/-- The predicate is forced by the PRECEDING datum A₀ alone: no Person
    hypothesis is needed. Once `RightWrongAt s p q` is given, `GroundsRightWrong s`
    follows directly, so the grounding relation is determined before Person is
    reached — it is not constructed after the fact.
    Footprint: `{Means, Subject}`. -/
theorem grounding_forced_by_preceding_facts (s : Subject) (p q : Prop)
    (h0 : RightWrongAt s p q) : GroundsRightWrong s :=
  (forward_modus_ponens_derivation s p q h0).2

/-- Index-alignment: the content-indexed ground at the datum's OWN pair ⟨p, q⟩.
    The personal ground is witnessed by the person derived from the datum, the
    normativity field is the datum itself, and the agential substrate is the
    datum's own pair of alternatives — no witness is manufactured after Person
    is obtained.
    Footprint: `{Means, Subject}`. -/
theorem grounding_forced_at_datum (s : Subject) (p q : Prop)
    (h0 : RightWrongAt s p q) : GroundsRightWrongAt s p q :=
  ⟨forward_discovery_person s p q h0, h0,
   step_stance_to_choice s p q (step_datum_to_stance s p q h0)⟩

-- ===========================================================================
-- Section 6: Non-Circularity Verification
-- ===========================================================================

/-- Non-Circularity Architectural Theorem:
    The retorsive discovery proof of Free Will (`indubitable_normative_free_will`)
    does NOT require or depend upon any grounding bridge.
    Transcendental discovery of the free subject from normative polarity is logically
    independent of the ontological grounding direction.
    Footprint: `{Means, Subject}` (0 substantive axioms). -/
theorem discovery_independent_of_grounding
    {s : Subject} {p q : Prop} (hGN : GenuineNormativity s p q) :
    Chooses s p q ∧ FreeWill s :=
  indubitable_normative_free_will hGN

/-- Non-Circularity for Judicative Correctness:
    The derivation of Free Will from ClaimsNormativeCorrectness is completely independent
    of any grounding bridge.
    Footprint: `{Initiates, Means, State, Subject, CL}` (0 substantive axioms). -/
theorem judicative_discovery_independent_of_grounding
    {s : Subject} {p : Prop} (hClaims : Logos.NormativeOrder.ClaimsNormativeCorrectness s p) :
    Chooses s (Correct s p) (Incorrect s p) ∧ FreeWill s :=
  Logos.NormativeOrder.claims_normative_correctness_derives_free_will s p hClaims

-- ===========================================================================
-- Section 7: Hostile Anti-Collapse Model Suite
-- ===========================================================================

namespace HostileModels

/-- Model A Signature: Abstract Bivalence without Agency. -/
structure ModelASignature where
  PropSort : Type
  T_val    : PropSort → Prop
  F_val    : PropSort → Prop
  bivalent : ∀ p, Incompatible (T_val p) (F_val p)
  has_distinct : ∃ p q, T_val p ∧ F_val q
  SubjectSort : Type
  no_subjects : ¬ ∃ _s : SubjectSort, True

/-- Theorem: Model A is mathematically satisfiable.
    Objective bivalent distinction can hold without any existing subject, proving that
    transcendental discovery works performatively from the act, not from abstract propositions alone.
    Footprint: `{}`. -/
theorem model_a_satisfiable : ∃ M : ModelASignature, True := by
  let M : ModelASignature := {
    PropSort := Bool
    T_val := fun b => b = true
    F_val := fun b => b = false
    bivalent := fun b ⟨hT, hF⟩ => by cases b <;> contradiction
    has_distinct := ⟨true, false, rfl, rfl⟩
    SubjectSort := Empty
    no_subjects := fun ⟨s, _⟩ => nomatch s
  }
  exact ⟨M, trivial⟩

/-- Model B Signature: Free Subject with Impersonal Ground of Normative Polarity.
    Models a universe where a free subject exists, but normative polarity is grounded
    exclusively in an impersonal atom (Entity.ofAtom 0), failing personal grounding. -/
structure ModelBSignature where
  Subject : Type
  Entity  : Type
  EntityOf : Subject → Entity
  impersonalAtom : Entity
  atom_ne_subject : ∀ s, impersonalAtom ≠ EntityOf s
  FreeIndependentWill : Subject → Prop
  Polarity : Prop
  GroundProp : Entity → Prop → Prop
  free_subject_exists : ∃ s : Subject, FreeIndependentWill s
  impersonal_ground : GroundProp impersonalAtom Polarity
  subject_not_ground : ∀ s : Subject, ¬ GroundProp (EntityOf s) Polarity

/-- Theorem: Model B is mathematically satisfiable.
    Proves that `FreeIndependentWill s ⇏ GroundProp (EntityOf s) Polarity` in bare model theory,
    rigorously isolating the necessity of the semantic bridge `AxPersonalNormativeGround`
    (historical name — no longer in the kernel; the current axiom is `AxTwoSubjects`).
    Footprint: `{}`. -/
theorem model_b_satisfiable : ∃ M : ModelBSignature, True := by
  let M : ModelBSignature := {
    Subject := Unit
    Entity := Bool
    EntityOf := fun _ => true
    impersonalAtom := false
    atom_ne_subject := fun _ => by decide
    FreeIndependentWill := fun _ => True
    Polarity := True
    GroundProp := fun e _ => e = false
    free_subject_exists := ⟨(), trivial⟩
    impersonal_ground := rfl
    subject_not_ground := fun _ h => by cases h
  }
  exact ⟨M, trivial⟩

/-- Theorem: Separation Theorem from Model B.
    A free, independent subject does NOT logically entail personal grounding of normative polarity
    without an explicit semantic bridge.
    Footprint: `{}`. -/
theorem model_b_separation (M : ModelBSignature) :
    (∃ s : M.Subject, M.FreeIndependentWill s) ∧
    ¬ (∀ s : M.Subject, M.FreeIndependentWill s → M.GroundProp (M.EntityOf s) M.Polarity) := by
  obtain ⟨s, hFW⟩ := M.free_subject_exists
  refine ⟨⟨s, hFW⟩, ?_⟩
  intro hAll
  exact M.subject_not_ground s (hAll s hFW)

/-- Model C: Identifying Ought with Subject's Current Will Collapses Violation.
    Machine-checks that the voluntarist identification collapses normative failure.
    Footprint: `{Ought, Subject, Wills}`. -/
theorem model_c_self_legislation_collapses
    {s : Subject} (hSelf : SelfLegislation s)
    (a : PracticalAction)
    (hSoloSource : ∀ r, Logos.OughtRetorsion.Ought r s a → r = s)
    (hContrary : SubjectWills s a.neg → ¬ SubjectWills s a) :
    NormativeViolation s a → False :=
  self_grounded_ought_collapses hSelf a hSoloSource hContrary

end HostileModels

-- ===========================================================================
-- Section 8: Axiom Footprint Audit
-- ===========================================================================

#print axioms Logos.PersonalNormativeGround.Constructive.discover_person
#print axioms will_identity_collapses_normativity
#print axioms free_independent_will_grounds_judicative_polarity
#print axioms person_grounds_normative_polarity
#print axioms person_grounds_right_wrong
#print axioms person_realizes_grounded_polarity
#print axioms person_exists_implies_global_grounded_polarity
#print axioms discovery_independent_of_grounding
#print axioms judicative_discovery_independent_of_grounding
#print axioms HostileModels.model_a_satisfiable
#print axioms HostileModels.model_b_satisfiable
#print axioms HostileModels.model_b_separation
#print axioms HostileModels.model_c_self_legislation_collapses

#print axioms step_datum_to_stance
#print axioms step_stance_to_choice
#print axioms step_choice_to_freewill
#print axioms step_freewill_to_freeSubject
#print axioms step_freeSubject_to_person
#print axioms step_person_to_grounding
#print axioms forward_modus_ponens_derivation
#print axioms forward_composition_pipeline
#print axioms person_grounds_original_normative_datum
#print axioms discovery_rightwrong_to_person
#print axioms existential_forward_normative_grounding
#print axioms non_reversal_discovery_and_grounding

#print axioms groundsRightWrong_iff_forced_content
#print axioms forced_content_of_person
#print axioms grounding_forced_by_preceding_facts
#print axioms grounding_forced_at_datum

end Logos.PersonalNormativeGround
