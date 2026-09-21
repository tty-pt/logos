/-
# Logos.PersonalGroundOfReality — Personal Grounding grounds all reality

The free personal judicative act is the necessary ontological basis of
Right/Wrong, truth/falsity and all Γ-reality. Reality in Γ = acts +
truth-bearing content + their constitutive base. Direction of discovery
(Right ⇒ free subject) and direction of ontology (free personal act ⇒
Right/Wrong) are stated and kept distinct.
-/
import Logos.Agency
import Logos.Person
import Logos.Choice
import Logos.Order
import Logos.NormativeOrder
import Logos.PersonalNormativeGround
import Logos.NecessaryPersonalGround

namespace Logos.PersonalGroundOfReality

open Logos.Agency (Subject Act)
open Logos.Person (Person)
open Logos.NormativeOrder (ClaimsNormativeCorrectness claims_normative_correctness_derives_free_will)
open Logos.PersonalNormativeGround (GroundsJudicativePolarity judicative_normative_polarity_of_act)
open Logos.NecessaryPersonalGround (NecessaryNormativeOrder necessary_normative_order)

/-- The free subject of a present judicative act constitutes the normative
    polarity of its judgment (Right/Wrong). -/
theorem free_subject_grounds_normative_order
    {s : Subject} {p : Prop} (hClaims : ClaimsNormativeCorrectness s p) :
    GroundsJudicativePolarity s p :=
  judicative_normative_polarity_of_act s p hClaims.1

/-- HEADLINE. The present personal free act is the necessary ontological basis
    of Right/Wrong and of all Γ-reality. Guarded only by the performative
    datum. Footprint: {Initiates, Means, State, Subject, CL}. -/
theorem present_act_yields_personal_grounding_of_reality
    {s : Subject} {p : Prop} (hClaims : ClaimsNormativeCorrectness s p) :
    Person s ∧ (∀ q : Prop, Act s q → GroundsJudicativePolarity s q)
           ∧ NecessaryNormativeOrder := by
  have hFW := claims_normative_correctness_derives_free_will s p hClaims
  refine ⟨Logos.Person.free_subject_is_person s hFW.2, ?_, necessary_normative_order⟩
  intro q hq
  exact judicative_normative_polarity_of_act s q hq

/-- Direction table: discovery vs ontology, both directions formalized. -/
def direction_stack : List (String × String) :=
  [("discovery", "ClaimsNormativeCorrectness s p -> FreeWill s ∧ Chooses s (Correct s p) (Incorrect s p)"),
   ("ontology",  "ClaimsNormativeCorrectness s p -> Person s ∧ GroundsJudicativePolarity s p ∧ NecessaryNormativeOrder")]

-- Axiom footprint audit (must print exactly {Initiates, Means, State, Subject, CL})
#print axioms present_act_yields_personal_grounding_of_reality
#print axioms free_subject_grounds_normative_order

end Logos.PersonalGroundOfReality