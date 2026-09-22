/-
# Logos.PersonalGroundOfReality — Personal Grounding grounds all reality

The free personal judicative act is the necessary ontological basis of
Right/Wrong, truth/falsity and all Γ-reality. Reality in Γ = acts +
truth-bearing content + their constitutive base. Direction of discovery
(Right ⇒ free subject) and direction of ontology (free personal act ⇒
Right/Wrong) are stated and kept distinct.
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
open Logos.NormativeOrder (ClaimsNormativeCorrectness claims_normative_correctness_derives_free_will)
open Logos.PersonalNormativeGround (GroundsJudicativePolarity judicative_normative_polarity_of_act)
open Logos.NecessaryPersonalGround (NecessaryNormativeOrder necessary_normative_order)
open Logos.IndubitableNormativeFreeWill (EstablishedRightWrong)
open Logos.RetorsiveNormativity (ClaimsCorrect)
open Logos.DirectNormativeRetorsion (NoRight cannot_claim_correct_no_right_and_true)

/-- The free subject of a present judicative act constitutes the normative
    polarity of its judgment (Right/Wrong). -/
theorem free_subject_grounds_normative_order
    {s : Subject} {p : Prop} (hClaims : ClaimsNormativeCorrectness s p) :
    GroundsJudicativePolarity s p :=
  judicative_normative_polarity_of_act s p hClaims.1

/-- Denying Right is performatively self-contradictory: no agent can present
    NoRight as correct while NoRight is true. Footprint: `{Initiates, Means,
    State, Subject}` (zero substantive axioms). Re-export of the retorsion
    boundary. -/
theorem deny_right_self_contradicts :
    ¬ ∃ s : Subject, ClaimsCorrect s NoRight ∧ NoRight :=
  cannot_claim_correct_no_right_and_true

/-- Right and Wrong are real, and the normative order is necessary — both
    unconditional, zero substantive axioms. -/
theorem reality_of_right :
    EstablishedRightWrong ∧ NecessaryNormativeOrder :=
  ⟨Logos.Core.rightWrongDistinction, necessary_normative_order⟩

/-- The judicative stance forces the Person: any agent grasping a proposition
    as correct and as incorrect is a free subject (FreeWill), hence a Person.
    Footprint: `{Initiates, Means, State, Subject, CL}` (zero substantive
    axioms). -/
theorem judicative_stance_forces_person :
    ∀ (s : Subject) (p : Prop), ClaimsNormativeCorrectness s p → Person s := by
  intro s p hClaims
  have hFW := claims_normative_correctness_derives_free_will s p hClaims
  exact Logos.Person.free_subject_is_person s hFW.2

/-- Every judicative act of every subject constitutes its own Right/Wrong
    polarity — the Person, as free subject, grounds ALL judicative reality.
    Footprint: `{Initiates, Means, State, Subject, CL}` (zero substantive
    axioms). -/
theorem every_judicative_act_grounds_its_own_polarity :
    ∀ (s : Subject) (q : Prop), Act s q → GroundsJudicativePolarity s q := by
  intro s q hq
  exact judicative_normative_polarity_of_act s q hq

/-- HEADLINE — THE PERSON SUPPORTS THE REALITY OF RIGHT.
    Unconditional, zero substantive axioms, no free premise:
    1. Denying Right is self-contradictory (`deny_right_self_contradicts`);
    2. Right/Wrong is real and necessary (`reality_of_right`);
    3. the judicative stance forces the Person (`judicative_stance_forces_person`);
    4. the Person grounds ALL judicative reality (`every_judicative_act_grounds_its_own_polarity`).
    The performative datum is internalized as an implication, so this is a
    closed Prop. "Necessary" = the order is necessary and its basis is the free
    personal judging nature (retorsive-transcendental necessity), NOT
    entity-level world-indexed necessity (Claim E stays annotated, see
    THIS_IS_PERSONAL.md §12.1).
    Footprint: `{Initiates, Means, State, Subject, CL}`. -/
theorem the_person_supports_the_reality_of_right :
    (¬ ∃ s : Subject, ClaimsCorrect s NoRight ∧ NoRight) ∧
    EstablishedRightWrong ∧ NecessaryNormativeOrder ∧
    (∀ (s : Subject) (p : Prop), ClaimsNormativeCorrectness s p → Person s) ∧
    (∀ (s : Subject) (q : Prop), Act s q → GroundsJudicativePolarity s q) := by
  exact ⟨deny_right_self_contradicts,
         ⟨Logos.Core.rightWrongDistinction, ⟨necessary_normative_order,
            ⟨judicative_stance_forces_person,
             every_judicative_act_grounds_its_own_polarity⟩⟩⟩⟩

/-- Existential corollary: given the performative datum (some agent actually
    judges), A Person exists whose free judicative nature grounds Right/Wrong
    for all its acts and the normative order is necessary.
    Footprint: `{Initiates, Means, State, Subject, CL}` (zero substantive
    axioms). -/
theorem personal_ground_of_right_exists
    (hDatum : ∃ s : Subject, ∃ p : Prop, ClaimsNormativeCorrectness s p) :
    ∃ s : Subject, Person s ∧ NecessaryNormativeOrder ∧
            (∀ q : Prop, Act s q → GroundsJudicativePolarity s q) := by
  obtain ⟨s, p, hClaims⟩ := hDatum
  refine ⟨s, ?_, ?_⟩
  · exact judicative_stance_forces_person s p hClaims
  · exact ⟨necessary_normative_order, every_judicative_act_grounds_its_own_polarity s⟩

/-- HEADLINE (instance form, datum-guarded). The present personal free act is
    the necessary ontological basis of Right/Wrong and of all Γ-reality.
    Footprint: `{Initiates, Means, State, Subject, CL}`. -/
theorem present_act_yields_personal_grounding_of_reality
    {s : Subject} {p : Prop} (hClaims : ClaimsNormativeCorrectness s p) :
    Person s ∧ (∀ q : Prop, Act s q → GroundsJudicativePolarity s q)
           ∧ NecessaryNormativeOrder := by
  refine ⟨judicative_stance_forces_person s p hClaims, ?_, necessary_normative_order⟩
  intro q hq
  exact judicative_normative_polarity_of_act s q hq

/-- Direction table: discovery vs ontology, both directions formalized. -/
def direction_stack : List (String × String) :=
  [("discovery", "deny-Right is contradictory -> EstablishedRightWrong /\n    NecessaryNormativeOrder -> judicative stance forces Person"),
   ("ontology",  "every judicative act (every subject) -> GroundsJudicativePolarity;\n    the Person supports the reality of Right")]

-- Axiom footprint audit (must print exactly {Initiates, Means, State, Subject, CL})
#print axioms the_person_supports_the_reality_of_right
#print axioms present_act_yields_personal_grounding_of_reality
#print axioms free_subject_grounds_normative_order

end Logos.PersonalGroundOfReality