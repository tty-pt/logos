import Logos.Core
import Logos.Agency
import Logos.Alternatives
import Logos.Choice
import Logos.Person
import Logos.PersonalNormativeGround
import Logos.CompleteLibertarianFreedomArgument

namespace Logos.LibertarianPersonhood

open Logos.Core
open Logos.Agency
open Logos.Alternatives
open Logos.Choice
open Logos.Person
open Logos.PersonalNormativeGround
open Logos.CompleteLibertarianFreedomArgument
open Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure

/-- Canonical two-world modal model for the demonstration. -/
inductive GammaWorld | actual | alternative
  deriving DecidableEq

/-- Canonical semantics for the Γ deduction.
    Disclosed as a semantic reading:
    - Assent at the actual world models asserting/meaning the proposition p.
    - Withholding at an alternative world models meaning the contrary/negated horn ¬p.
    - Exclusive is immediate because the actual world is distinct from any alternative world. -/
def gammaSem : CompleteLibertarianFreedomArgument.FinalNonCircularClosure.Semantics Subject where
  World := GammaWorld
  actualWorld := GammaWorld.actual
  Accessible := fun _ _ => True
  SameCompletePriorState := fun _ _ => True
  AssentsAt := fun s w x => w = GammaWorld.actual ∧ Means s x
  WithholdsAt := fun s w x => w ≠ GammaWorld.actual ∧ Means s (¬ x)
  exclusive := by
    intro s w x ⟨hA, hW⟩
    exact hW.1 hA.1

/-- Bridge theorem: Libertarian freedom in the canonical semantics gammaSem
    strictly derives the genuine choice and Free Subject of Choice.lean.
    Price: 0 substantive axioms (pure logic). -/
theorem gamma_freeSubject_is_choice {s : Subject}
    (h : CompleteLibertarianFreedomArgument.FinalNonCircularClosure.FreeSubject gammaSem s) :
    Logos.Choice.FreeSubject s := by
  have ⟨p, hChoice⟩ := h
  rcases hChoice with (⟨hAssent, ⟨w', _, _, _, hWithhold⟩⟩ | ⟨hWithhold, _⟩)
  · have hMeansP : Means s p := hAssent.2
    have hMeansNotP : Means s (¬ p) := hWithhold.2
    have hIncomp : Incompatible p (¬ p) := incompatible_self_negation p
    have hChooses : Chooses s p (¬ p) := ⟨hMeansP, hMeansNotP, hIncomp⟩
    exact ⟨p, ¬ p, hChooses⟩
  · exact False.elim (hWithhold.1 rfl)

/-- Tag: TRANS
This very demonstration occurs as an instance of the formalized judgment-determination structure.

The demonstration of libertarian freedom is instantiated in the canonical two-world semantics
`gammaSem`. By performative retorsion, the act of formulating and verifying this deduction
constitutes a concrete instance of judgment determination.
Price: 0 substantive axioms (`Tag: TRANS`). -/
axiom demonstration_occurs :
  CompleteLibertarianFreedomArgument.FinalNonCircularClosure.DemonstrativeProofOccurrence.{0, 0, 0} gammaSem

/-- Master existence theorem: If this demonstration occurs, an anonymous Free Subject exists.
    Combines the existential wrapper of CLFA with the bridge theorem to Logos.Choice.FreeSubject.
    Price: `[Classical.choice]`, 1 TRANS (`demonstration_occurs`). -/
theorem free_subject_exists_via_judgment_chain :
    ∃ s : Subject, Logos.Choice.FreeSubject s := by
  have hDemo := CompleteLibertarianFreedomArgument.demonstration_occurrence_implies_existence_of_free_subject
    demonstration_occurs
  rcases hDemo with ⟨s, hFS⟩
  exact ⟨s, gamma_freeSubject_is_choice hFS⟩

/-- Unconditional existence of free will: If this demonstration occurs, free will exists.
    Definitionally identical to `free_subject_exists_via_judgment_chain`.
    Price: `[Classical.choice]`, 1 TRANS (`demonstration_occurs`). -/
theorem free_will_exists_via_judgment_chain :
    ∃ s : Subject, Logos.Choice.FreeWill s :=
  free_subject_exists_via_judgment_chain

/-- Master personhood theorem: The Free Subject delivered by the judgment-determination chain
    is constitutively an authoritative Person in the Boethian-Thomistic sense.
    Price: `[Classical.choice]`, 1 TRANS (`demonstration_occurs`). -/
theorem person_exists_via_judgment_chain :
    ∃ s : Subject, Person s := by
  have ⟨s, hFS⟩ := free_subject_exists_via_judgment_chain
  exact ⟨s, free_subject_is_person s hFS⟩

/-- Master personal-ground theorem: The Person established by the judgment-determination chain
    grounds objective Right and Wrong. One single witness `s` satisfies all three conditions.
    Price: `[Classical.choice]`, 1 TRANS (`demonstration_occurs`). -/
theorem person_grounds_right_wrong_via_judgment_chain :
    ∃ s : Subject, Person s ∧ GroundsRightWrong s := by
  have ⟨s, hFS⟩ := free_subject_exists_via_judgment_chain
  have hP : Person s := free_subject_is_person s hFS
  have hG : GroundsRightWrong s := person_grounds_normative_polarity s hP
  exact ⟨s, hP, hG⟩

/-- Anti-determinism theorem: The ultimate internal source of the judgment act
    in the demonstration chain is an act of the subject and does not receive its
    determination from the complete prior state.
    Price: `[Classical.choice]`, 1 TRANS (`demonstration_occurs`). -/
theorem judgment_source_not_fixed_by_prior_state :
    ∃ (s : Subject) (p : Prop)
      (J : CompleteLibertarianFreedomArgument.FinalNonCircularClosure.JudgmentDeterminationChain.{0, 0, 0} gammaSem s gammaSem.actualWorld p)
      (a : J.Node),
      CompleteLibertarianFreedomArgument.FinalNonCircularClosure.UltimateInternalSource J.toDeterminationSystem a ∧
      J.IsActOf s a ∧
      ¬ CompleteLibertarianFreedomArgument.FinalNonCircularClosure.DeterminationReceivedFromPriorState J a := by
  let inst := demonstration_occurs.instanceOfJudgment
  let s := inst.subject
  let p := inst.proposition
  let J := inst.chain
  have ⟨a, haSource, haReachAct⟩ := CompleteLibertarianFreedomArgument.FinalNonCircularClosure.exists_ultimate_source_of_judgment_act J
  have haAct : J.IsActOf s a := CompleteLibertarianFreedomArgument.FinalNonCircularClosure.ultimate_source_is_agential J haReachAct
  have haNotRec : ¬ CompleteLibertarianFreedomArgument.FinalNonCircularClosure.DeterminationReceivedFromPriorState J a :=
    CompleteLibertarianFreedomArgument.FinalNonCircularClosure.ultimate_internal_act_source_is_not_received_from_prior_state J haSource haAct
  exact ⟨s, p, J, a, haSource, haAct, haNotRec⟩

#print axioms gamma_freeSubject_is_choice
#print axioms demonstration_occurs
#print axioms free_subject_exists_via_judgment_chain
#print axioms free_will_exists_via_judgment_chain
#print axioms person_exists_via_judgment_chain
#print axioms person_grounds_right_wrong_via_judgment_chain
#print axioms judgment_source_not_fixed_by_prior_state

end Logos.LibertarianPersonhood
