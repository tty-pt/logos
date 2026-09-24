/-
# Logos.PersonalGroundOfReality — Personal Grounding of the Judicative/Normative Order
  (not a creator-of-existence claim)

Objective Right/Wrong has a necessary ontological grounding of a personal kind/type.
The Γ judicative/normative order (Right/Wrong, truth/falsity, Ought/OughtNot under the
epistemic TruthNorm) has its necessary ontological basis in Personhood.
Direction of discovery (Right/Wrong ⇒ Person) and direction of ontology
(Person ⇒ grounds ⇒ Right/Wrong) are stated, derived, and kept distinct without
invoking Act in the grounding relation.

The claim concerns the objective normative/truth order governing the correctness of
judgments *about* reality. It is NOT a claim that Personhood causally produces every
existent, nor that it makes evil exist or morally legitimizes anything that exists.

The argument does not identify a particular contingent individual as the creator of
Right and Wrong; it establishes that the ontological ground required by objective
Right/Wrong is personal in kind.
-/
import Logos.Core
import Logos.Agency
import Logos.Person
import Logos.Choice
import Logos.Order
import Logos.NormativeOrder
import Logos.PersonalNormativeGround
import Logos.NecessaryPersonalGround
import Logos.IndubitableNormativeFreeWill
import Logos.RetorsiveNormativity
import Logos.DirectNormativeRetorsion

namespace Logos.PersonalGroundOfReality

open Logos.Agency (Subject Act)
open Logos.Person (Person)
open Logos.Order (Correct Incorrect)
open Logos.NormativeOrder (ClaimsNormativeCorrectness claims_normative_correctness_derives_free_will claims_normative_correctness_derives_genuine_normativity)
open Logos.PersonalNormativeGround (
  RightWrong
  RightWrongAt
  GroundsRightWrong
  GroundsRightWrongAt
  GroundsJudicativePolarity
  GroundedNormativePolarity
  GlobalGroundedNormativePolarity
  judicative_normative_polarity_of_act
  JudicativeNormativePolarity
  person_grounds_right_wrong
  person_grounds_normative_polarity
  discovery_rightwrong_to_person
  forward_discovery_person
  forward_modus_ponens_derivation
  forward_composition_pipeline
  person_grounds_original_normative_datum
  existential_forward_normative_grounding
  non_reversal_discovery_and_grounding
)
open Logos.NecessaryPersonalGround (NecessaryNormativeOrder necessary_normative_order)
open Logos.IndubitableNormativeFreeWill (EstablishedRightWrong)
open Logos.RetorsiveNormativity (ClaimsCorrect)
open Logos.DirectNormativeRetorsion (NoRight cannot_claim_correct_no_right_and_true)

/-- The free subject addressed by an objective normative opposition constitutively
    instantiates the personal ground of Right/Wrong.
    The argument does not identify a particular contingent individual as the creator of Right and Wrong;
    it establishes that the ontological ground required by objective Right/Wrong is personal in kind.
    Footprint: `{Means, Subject}`. -/
theorem free_subject_grounds_normative_order
    {s : Subject} {p q : Prop} (hRW : RightWrongAt s p q) :
    GroundsRightWrong s :=
  (forward_modus_ponens_derivation s p q hRW).2

/-- Denying Right is performatively self-contradictory: no agent can present
    NoRight as correct while NoRight is true. Footprint: `{Initiates, Means,
    State, Subject}` (zero substantive axioms). Re-export of the retorsion
    boundary. -/
theorem deny_right_self_contradicts :
    ¬ ∃ s : Subject, ClaimsCorrect s NoRight ∧ NoRight :=
  cannot_claim_correct_no_right_and_true

/-- Right and Wrong are real, bivalence holds, and the normative order is necessary — all
    unconditional, zero substantive axioms. Footprint: `{Initiates, Means, State, Subject, CL}`. -/
theorem reality_of_right :
    EstablishedRightWrong ∧ (∀ p : Prop, Logos.Core.T p ∨ Logos.Core.IsFalse p) ∧ NecessaryNormativeOrder :=
  ⟨Logos.Core.rightWrongDistinction, Logos.Core.bivalence, necessary_normative_order⟩

/-- The normative datum forces the Person: any agent addressed by genuine
    normativity is a free subject (FreeWill), hence a Person.
    Footprint: `{Means, Subject}` (zero substantive axioms). -/
theorem normative_datum_forces_person :
    ∀ (s : Subject), RightWrong s → Person s :=
  discovery_rightwrong_to_person

/-- The ontology in one universal: wherever Right/Wrong is real, its
    ground-type is personal (the 'simple thing'). The elaborated
    `GroundsRightWrong` record is its record-form (DEFINITIONAL).
    Footprint: `{Means, Subject}`. -/
theorem personal_ground_of_right_wrong
    (s : Subject) : RightWrong s → Person s :=
  normative_datum_forces_person s

/-- The judicative stance forces the Person: any agent grasping a proposition
    as correct and as incorrect is a free subject (FreeWill), hence a Person.
    Footprint: `{Initiates, Means, State, Subject, CL}` (zero substantive
    axioms). -/
theorem judicative_stance_forces_person :
    ∀ (s : Subject) (p : Prop), ClaimsNormativeCorrectness s p → Person s := by
  intro s p hClaims
  have hFW := claims_normative_correctness_derives_free_will s p hClaims
  exact Logos.Person.free_subject_is_person s hFW.2

/-- Every Person constitutes the ontological ground of Right/Wrong.
    Derived directly from Personhood itself without Act.
    The argument does not identify a particular contingent individual as the creator of Right and Wrong;
    it establishes that the ontological ground required by objective Right/Wrong is personal in kind.
    Footprint: `{Means, Subject}` (zero substantive axioms). -/
theorem person_grounds_normative_order :
    ∀ (s : Subject), Person s → GroundsRightWrong s :=
  person_grounds_right_wrong

/-- Historical lemma: every performed act under correctness realizes judicative polarity.
    Grounding itself is established through Personhood (`Person s → GroundsRightWrong s`). -/
theorem every_judicative_act_grounds_its_own_polarity :
    ∀ (s : Subject) (q : Prop), Act s q → JudicativeNormativePolarity s q := by
  intro s q hq
  exact judicative_normative_polarity_of_act s q hq

/-- HEADLINE — THE PERSON SUPPORTS THE REALITY OF RIGHT.
    Unconditional, zero substantive axioms, no free premise:
    1. Denying Right is self-contradictory (`deny_right_self_contradicts`);
    2. Right/Wrong is real, bivalence holds, and the normative order is necessary (`reality_of_right`);
    3. The normative datum forces the Person (`normative_datum_forces_person`);
    4. Personhood supplies the ontological ground-type required by Right and Wrong (`person_grounds_normative_order`).

    "Supports the reality of Right" means: the asserted reality is the objective
    correctness/normativity structure governing judgments (RightWrong-reality:
    truth/falsity of propositions, Ought/OughtNot under TruthNorm). It is NOT a claim
    that the Person causally produces everything that exists, and NOT a moral evaluation
    of any content — e.g., if evil exists, "evil exists" is objectively correct to affirm
    without thereby making evil morally right.

    The argument does not identify a particular contingent individual as the creator of Right and Wrong;
    it establishes that the ontological ground required by objective Right/Wrong is personal in kind.

    The performative datum is internalized as an implication, so this is a closed Prop.
    "Necessary" = the order is necessary and its basis is the personal ontological nature
    (retorsive-transcendental necessity), NOT an entity-level modal claim that the same contingent
    individual s exists in every possible world.
    Footprint: `{Initiates, Means, State, Subject, CL}`. -/
theorem the_person_supports_the_reality_of_right :
    (¬ ∃ s : Subject, ClaimsCorrect s NoRight ∧ NoRight) ∧
    EstablishedRightWrong ∧ (∀ p : Prop, Logos.Core.T p ∨ Logos.Core.IsFalse p) ∧
    NecessaryNormativeOrder ∧
    (∀ (s : Subject), RightWrong s → Person s) ∧
    (∀ (s : Subject), Person s → GroundsRightWrong s) := by
  exact ⟨deny_right_self_contradicts,
         ⟨Logos.Core.rightWrongDistinction, ⟨Logos.Core.bivalence, ⟨necessary_normative_order,
            ⟨normative_datum_forces_person,
             person_grounds_normative_order⟩⟩⟩⟩⟩

/-- Existential corollary: given the performative datum (some agent actually
    faces Right/Wrong), there exists a personal ontological ground of Right/Wrong,
    and the normative order is necessary.
    Distinction: This establishes that there exists a personal ground of the normative order;
    it does NOT claim that there exists one particular empirical person who personally
    causes every normative fact.
    Footprint: `{Initiates, Means, State, Subject}` (zero substantive axioms). -/
theorem personal_ground_of_right_exists
    (hDatum : ∃ s : Subject, RightWrong s) :
    ∃ s : Subject, Person s ∧ NecessaryNormativeOrder ∧ GroundsRightWrong s := by
  obtain ⟨s, hRW⟩ := hDatum
  have hPerson : Person s := normative_datum_forces_person s hRW
  exact ⟨s, hPerson, necessary_normative_order, person_grounds_normative_order s hPerson⟩

/-- Datum-guarded existential corollary from judicative stance. -/
theorem personal_ground_of_right_exists_of_claims
    (hDatum : ∃ s : Subject, ∃ p : Prop, ClaimsNormativeCorrectness s p) :
    ∃ s : Subject, Person s ∧ NecessaryNormativeOrder ∧ GroundsRightWrong s := by
  obtain ⟨s, p, hClaims⟩ := hDatum
  have hGN := claims_normative_correctness_derives_genuine_normativity s p hClaims
  have hRW : RightWrong s := ⟨Correct s p, Incorrect s p, hGN⟩
  exact personal_ground_of_right_exists ⟨s, hRW⟩

/-- HEADLINE (instance form, datum-guarded). The personal ontological ground is the necessary
    ground of the objective normative/truth order governing judgments about Γ-reality
    (Right/Wrong, truth/falsity, Ought/OughtNot under TruthNorm): it grounds the correctness
    of propositions *about* what is the case, not the fact of what exists.
    This is not a claim that the ground causally generates every existent, and not a claim
    that it makes evil exist or morally legitimizes evil. "Γ-reality" is the domain of what
    is real / what exists; the normative order determines only whether propositions about
    that domain are objectively correct or incorrect, and does not generate their contents.
    The derived Person s instantiates the personal ground-type.
    The argument does not identify a particular contingent individual as the creator of Right and Wrong;
    it establishes that the ontological ground required by objective Right/Wrong is personal in kind.
    Footprint: `{Initiates, Means, State, Subject}`. -/
theorem person_yields_personal_grounding_of_reality
    (s : Subject) (hPerson : Person s) :
    Person s ∧ GroundsRightWrong s ∧ NecessaryNormativeOrder :=
  ⟨hPerson, person_grounds_right_wrong s hPerson, necessary_normative_order⟩

/-- Historical compatibility alias for `person_yields_personal_grounding_of_reality`.
    Marked explicitly as historical compatibility terminology: the theorem requires no `Act` premise
    and expresses `Person → personal ontological ground`.
    Footprint: `{Initiates, Means, State, Subject}`. -/
@[deprecated person_yields_personal_grounding_of_reality (since := "2026-04")]
theorem present_act_yields_personal_grounding_of_reality
    (s : Subject) (hPerson : Person s) :
    Person s ∧ GroundsRightWrong s ∧ NecessaryNormativeOrder :=
  person_yields_personal_grounding_of_reality s hPerson

/-- HEADLINE FORWARD CHAIN: The forward constructive derivation from the normative
    datum to the Person who instantiates its personal ontological ground.
    Unconditional implication chain: A₀(s, p, q) ⇒ ... ⇒ P(s) ⇒ G(s).
    The argument does not identify a particular contingent individual as the creator of Right and Wrong;
    it establishes that the ontological ground required by objective Right/Wrong is personal in kind.
    Footprint: `{Means, Subject}`. -/
theorem forward_normative_derivation_to_personal_ground (s : Subject) (p q : Prop)
    (h0 : RightWrongAt s p q) :
    Person s ∧ GroundsRightWrong s :=
  forward_modus_ponens_derivation s p q h0

/-- Re-export of the master forward composition pipeline. -/
theorem forward_pipeline (s : Subject) (p q : Prop) :
    RightWrongAt s p q → Person s ∧ GroundsRightWrong s :=
  forward_composition_pipeline s p q

/-- The derived subject s instantiates the personal ontological ground of the initial normative datum:
    `RightWrongAt s p q → Person s ∧ GroundsRightWrong s`.
    The proof runs strictly forward; the personal ontological grounding relation is the terminal derived theorem.
    The argument does not identify a particular contingent individual as the creator of Right and Wrong;
    it establishes that the ontological ground required by objective Right/Wrong is personal in kind.
    Footprint: `{Means, Subject}`. -/
theorem person_grounds_initial_normative_datum (s : Subject) (p q : Prop)
    (h0 : RightWrongAt s p q) :
    Person s ∧ GroundsRightWrong s :=
  person_grounds_original_normative_datum s p q h0

/-- Direction table: discovery vs ontology, both directions formalized. -/
def direction_stack : List (String × String) :=
  [("discovery", "deny-Right is contradictory -> EstablishedRightWrong /\n    NecessaryNormativeOrder -> normative datum forces Person"),
   ("ontology",  "Person s -> GroundsRightWrong s (the ground required by Right/Wrong is of a personal
    kind/type; the Person grounds the objective correctness/normative order (RightWrong-reality),
    not the creation of existents)")]

-- Axiom footprint audit (must print exactly {Initiates, Means, State, Subject, CL})
#print axioms the_person_supports_the_reality_of_right
#print axioms person_yields_personal_grounding_of_reality
#print axioms present_act_yields_personal_grounding_of_reality
#print axioms free_subject_grounds_normative_order
#print axioms forward_normative_derivation_to_personal_ground
#print axioms forward_pipeline
#print axioms person_grounds_initial_normative_datum

end Logos.PersonalGroundOfReality
