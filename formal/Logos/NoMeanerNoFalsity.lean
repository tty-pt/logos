/-
# Logos.NoMeanerNoFalsity — the act datum's own polarity discharges the choice frontier

The target sentence is reached without substantive META axioms: the performative act datum
(`Agency.performative_act_datum`, 1 TRANS) carries its own polarity (`Choice.AxActPolarity`, 1 SEM)
to derive co-meaning (`AsieticChoice.bareRejectedHornCoMeant_is_derivable`, C565). Genuine choice
(`Choice.rejectedHornCoMeant_implies_genuineChoice`) and free will
(`Choice.freeWillExists_of_genuineChoice`) follow at zero substantive price, yielding a genuine
Free Person (`Person.freeWill_implies_person`, C221) at `{performative_act_datum, AxActPolarity}`.

Zero new axioms are declared in this module. Every theorem is an existing declaration reached by an
existing free or ledgered step.
-/

import Logos.Core
import Logos.Agency
import Logos.Alternatives
import Logos.Choice
import Logos.Person
import Logos.Plurality
import Logos.Entity
import Logos.Semantics
import Logos.MeaningRetorsion
import Logos.ActCascade
import Logos.AsieticChoice
import Logos.Order
import Logos.SinglePersonDenial
import Logos.TrinitarianSubjectBridge
import Logos.Necessity
import Logos.NecessityEternity
import Logos.EpistemicNecessity
import Logos.Modal
import Logos.DivineAgape
import Logos.TrinitarianPersonalGround

namespace Logos.NoMeanerNoFalsity

open Logos.Core
open Logos.Agency (Subject Means Act performative_act_datum NecessarySubjectKind)
open Logos.Alternatives (Incompatible)
open Logos.Choice (Chooses FreeWill FreeSubject AxActPolarity genuineChoice_exists
  rejectedHornCoMeant_implies_genuineChoice freeWillExists_of_genuineChoice)
open Logos.Person (Person freeWill_implies_person)
open Logos.Plurality (NecessarySubject)
open Logos.Entity (Entity EntityOf)
open Logos.Semantics (World)
open Logos.MeaningRetorsion (NoMeaning noMeaning_is_refuted_from_the_act_datum)
open Logos.ActCascade (someone_means_something)
open Logos.AsieticChoice (bareRejectedHornCoMeant_is_derivable singleContentModelRefutesBareRejectedHorn
  gammaMeans_is_not_single_valued bareRejectedHornCoMeant_is_not_derivable SingleContentSignature)
open Logos.RecoveredOntologicalGround (NecessaryGroundOfReality OneEssence)
open Logos.NecessityEternity (ofGround_necessary_ground_of_reality)
open Logos.SinglePersonDenial (single_necessary_personal_essence_three_persons
  self_gift_cannot_depend_on_a_contingent_person donation_makes_contingency_is_refuted
  donation_terminus_is_as_necessary_as_the_donor not_a_single_person)
open Logos.DivineAgape (DivineHypostasis SelfDonation)
open Logos.TrinitarianPersonalGround (PersonalGround)
open Logos.Modal (NecessaryEntity)

/-- N1: The performative act datum guarantees that someone means something.
    Footprint: `{Initiates, Means, State, Subject, performative_act_datum}`. -/
theorem act_datum_gives_a_meaning : ∃ s : Subject, ∃ p : Prop, Means s p :=
  someone_means_something

/-- N2: A world without meaning is impossible given the act datum.
    Footprint: `{Initiates, Means, State, Subject, performative_act_datum}`. -/
theorem no_meaning_world_is_impossible : ¬ NoMeaning :=
  noMeaning_is_refuted_from_the_act_datum performative_act_datum

/-- N3: Both right and wrong obtain: the alethic distinction is non-empty and non-conflating.
    Footprint: `{}`. -/
theorem right_and_wrong_both_obtain : ¬ N_T ∧ ¬ N_F :=
  rightWrongDistinction

/-- N4: Falsity is instantiated alongside truth.
    Footprint: `{}`. -/
theorem falsity_is_instantiated : ∃ p q : Prop, T p ∧ IsFalse q :=
  greatResult

/-- N5: The act carries its own polarity: both horns are co-meant by one subject (C565).
    Footprint: `{AxActPolarity, Initiates, Means, State, Subject, performative_act_datum}`. -/
theorem the_act_carries_its_own_polarity : ∃ s : Subject, ∃ p : Prop, Means s p ∧ Means s (¬ p) :=
  bareRejectedHornCoMeant_is_derivable someone_means_something

/-- N6: Co-meaning entails genuine choice between incompatible alternatives.
    Footprint: `{AxActPolarity, Initiates, Means, State, Subject, performative_act_datum}`. -/
theorem genuine_choice_exists_derived : genuineChoice_exists :=
  rejectedHornCoMeant_implies_genuineChoice the_act_carries_its_own_polarity

/-- N7: Genuine choice entails the existence of free will.
    Footprint: `{AxActPolarity, Initiates, Means, State, Subject, performative_act_datum}`. -/
theorem a_free_will_exists_derived : ∃ s : Subject, FreeWill s :=
  freeWillExists_of_genuineChoice genuine_choice_exists_derived

/-- N8: A genuine Free Person exists, derived without any META axiom.
    Footprint: `{AxActPolarity, Initiates, Means, State, Subject, Will, performative_act_datum, subjectWill, will_individuation}`. -/
theorem a_genuine_free_person_exists : ∃ s : Subject, Person s := by
  obtain ⟨s, hfw⟩ := a_free_will_exists_derived
  exact ⟨s, freeWill_implies_person s hfw⟩

/-- N9: The Ground of Reality is a personal, necessary essence, indwelt by every person,
    and no person is the ground.
    Footprint: `{Means, NecessarySubjectKind, Subject, Will, subjectWill}`. -/
theorem the_ground_is_a_personal_necessary_essence :
    NecessaryGroundOfReality Entity.ofGround ∧
    PersonalGround Entity.ofGround ∧
    (∀ s : Subject, Person s → OneEssence Entity.ofGround (EntityOf s)) ∧
    (∀ s : Subject, ¬ (Entity.ofGround = EntityOf s)) :=
  single_necessary_personal_essence_three_persons

/-- N10: The dependence step of the single-person objection is refuted:
    self-giving love cannot depend on contingent persons, and donation terminus is necessary.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem the_dependence_step_is_refuted :
    (∀ _dependence : ∃ f o : DivineHypostasis, ∃ s : Subject,
      SelfDonation f o ∧ o.deiformEntity = EntityOf s, False) ∧
    (∀ _donation_makes_contingency : ∃ f o : DivineHypostasis,
      SelfDonation f o ∧ ¬ NecessaryEntity o.deiformEntity, False) ∧
    (∀ f o : DivineHypostasis, SelfDonation f o →
      NecessaryEntity f.deiformEntity ∧ NecessaryEntity o.deiformEntity) :=
  ⟨fun d => self_gift_cannot_depend_on_a_contingent_person d,
   fun c => donation_makes_contingency_is_refuted c,
   donation_terminus_is_as_necessary_as_the_donor⟩

/-- N11: The choice frontier is discharged in Γ because meaning is many-valued.
    Footprint: `{AxActPolarity, CL, Initiates, Means, State, Subject, performative_act_datum}`. -/
theorem the_choice_frontier_is_discharged :
    (∃ s p, Means s p ∧ Means s (¬ p)) ∧
    (¬ (∀ s p q, Means s p → Means s q → p = q)) :=
  ⟨the_act_carries_its_own_polarity, gammaMeans_is_not_single_valued⟩

/-- N12: The free person claim in one composed statement: a genuine free person exists,
    the ground is a personal necessary essence, and contingent donation-dependence is refuted. -/
theorem the_free_person_claim_in_one_statement :
    (∃ s : Subject, Person s) ∧
    NecessaryGroundOfReality Entity.ofGround ∧
    PersonalGround Entity.ofGround ∧
    (∀ _dependence : ∃ f o : DivineHypostasis, ∃ s : Subject,
      SelfDonation f o ∧ o.deiformEntity = EntityOf s, False) :=
  ⟨a_genuine_free_person_exists,
   the_ground_is_a_personal_necessary_essence.1,
   the_ground_is_a_personal_necessary_essence.2.1,
   the_dependence_step_is_refuted.1⟩

/-- N13: Countermodel: co-meaning is not free of semantic commitment; in every single-content
    model of meaning, the rejected horn fails.
    Footprint: `{CL}`. -/
theorem countermodel_co_meaning_is_not_free :
    ¬ SingleContentSignature.singleContentModel.bareHorn :=
  bareRejectedHornCoMeant_is_not_derivable

/-- N14: Countermodel: the choice frontier is not vocabulary; Γ's own Means is many-valued.
    Footprint: `{AxActPolarity, CL, Initiates, Means, State, Subject, performative_act_datum}`. -/
theorem countermodel_the_choice_frontier_is_not_vocabulary :
    ¬ (∀ s p q, Means s p → Means s q → p = q) :=
  gammaMeans_is_not_single_valued

/-! ## Axiom Footprint Audit -/
#print axioms act_datum_gives_a_meaning
#print axioms no_meaning_world_is_impossible
#print axioms right_and_wrong_both_obtain
#print axioms falsity_is_instantiated
#print axioms the_act_carries_its_own_polarity
#print axioms genuine_choice_exists_derived
#print axioms a_free_will_exists_derived
#print axioms a_genuine_free_person_exists
#print axioms the_ground_is_a_personal_necessary_essence
#print axioms the_dependence_step_is_refuted
#print axioms the_choice_frontier_is_discharged
#print axioms the_free_person_claim_in_one_statement
#print axioms countermodel_co_meaning_is_not_free
#print axioms countermodel_the_choice_frontier_is_not_vocabulary

end Logos.NoMeanerNoFalsity
