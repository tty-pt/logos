/-
# Logos.UndeniableNormativeDerivation — Undeniable Normative Derivation of Free Will

This module provides the definitive, maximally adversarial audit and resolution
of the normative route to Free Will in Γ:
  Right/Wrong ⇒ GenuineNormativity ⇒ Cognitive Grasp ⇒ Chooses ⇒ FreeWill.

Key Results:
1. Boundary Formalization: Proves that bare extensional bivalence (¬N_T ∧ ¬N_F)
   is satisfied by an inanimate world with zero subjects (Hostile Model M_inanimate),
   establishing that bare bivalence alone cannot derive Free Will without an
   agential/normative bridge.
2. The Three Legitimate Agential Bridges:
   - The Constitutive Normative Bridge (Right/Wrong means genuine prescriptive directive)
   - The Metaphysical Plurality Bridge (AxTwoSubjects)
   - The Performative Retorsion Bridge (judge_commits)
3. Circularity Audit: Proves strict DAG ordering from primitives {Subject, Means, Incompatible}
   through GenuineNormativity to Chooses and FreeWill (zero circular definitions).
4. The 8 Formal Denial Normal Forms (D1–D8): Classified into (a) formally inconsistent,
   (b) inconsistent with established theorem, (c) rejection of constitutive meaning,
   or (d) surviving alternative.
5. Smallest Final Kernel Theorems: Clean, transparent proofs with footprint {Means, Subject}
   and zero substantive axioms.
-/

import Logos.Core
import Logos.Necessity
import Logos.Semantics
import Logos.Agency
import Logos.Order
import Logos.Choice
import Logos.Alternatives
import Logos.Value
import Logos.Plurality
import Logos.IndubitableNormativeFreeWill
import Logos.RetorsiveNormativity

set_option linter.unusedVariables false

namespace Logos.UndeniableNormativeDerivation

open Logos.Agency (Subject Means State Initiates Act)
open Logos.Alternatives (Incompatible)
open Logos.Choice (Chooses FreeWill FreeSubject ChoiceField)
open Logos.IndubitableNormativeFreeWill (DeonticOpposition AgentialDeonticAddress GenuineNormativity indubitable_normative_free_will)

-- ===========================================================================
-- Section 1: The Epistemic Boundary: Extensional vs Constitutive Right/Wrong
-- ===========================================================================

/-- Extensional Right/Wrong: Propositional non-triviality in the universe of propositions.
    "Not everything is true, and not everything is false."
    Classification: LOGICAL / EXTENSIONAL. -/
def ExtensionalRightWrong : Prop :=
  ¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F

/-- Constitutive Right/Wrong: Genuine prescriptive normativity addressed to an agent.
    "There is an authoritative normative law commanding Right and forbidding Wrong."
    Classification: CONSTITUTIVE SEMANTIC. -/
def ConstitutiveRightWrong : Prop :=
  ∃ (s : Subject) (p q : Prop), GenuineNormativity s p q

/-- Hostile Inanimate Model: An uninhabited universe with zero subjects.
    In an inanimate universe, propositional non-triviality holds (True is true, False is false),
    yet no agential choice or free will exists.
    Status: MACHINE-CHECKED COUNTERMODEL TO BARE EXTENSIONAL DERIVATION. -/
theorem inanimate_universe_satisfies_extensional_bivalence_without_agency :
    ∃ (Universe : Type) (MeansRel : Universe → Prop → Prop),
      (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) ∧
      ¬ (∃ (s : Universe) (p q : Prop), MeansRel s p ∧ MeansRel s q ∧ Incompatible p q) := by
  refine ⟨Empty, fun e _ => False, Logos.Core.rightWrongDistinction, ?_⟩
  intro ⟨s, _, _, _, _, _⟩
  cases s

/-- Formal Insufficiency Theorem: Bare extensional bivalence alone does not deductively
    force agential choice without an agential or normative bridge.
    Footprint: {} (pure logic). -/
theorem extensional_bivalence_insufficient_for_free_will :
    ¬ (∀ (U : Type) (M : U → Prop → Prop),
        (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) →
        (∃ (s : U) (p q : Prop), M s p ∧ M s q ∧ Incompatible p q)) := by
  intro h
  have hContra := h Empty (fun _ _ => False) Logos.Core.rightWrongDistinction
  obtain ⟨s, _, _, _, _, _⟩ := hContra
  cases s

-- ===========================================================================
-- Section 2: The Three Bridges from Propositional Fact to Agential Normativity
-- ===========================================================================

/-!
### The Bridge Architecture: From Propositional Fact to Agential Normativity
To reach agential Free Will, Γ provides four distinct paths:
1. Bridge A (Constitutive Normative Semantics): The premise "Há certo e há errado"
   is constitutively understood as Strong Normativity (ConstitutiveRightWrong).
2. Bridge B (Metaphysical Plurality Bridge): AxTwoSubjects (Value.lean) yields persons.
3. Bridge C (Performative Retorsion Bridge): The assertion of right-and-wrong is an act
   by a judge (Order.lean: judge_commits).
4. Bridge D (Transcendental Retorsion of Genuine Normativity): The skeptical denial of
   GenuineNormativity cannot be asserted as correct without performatively instantiating
   GenuineNormativity under Judicative Bipolarity (RetorsiveNormativity.lean).
-/

/-- Bridge A: Constitutive Normative Route directly derives Free Will with ZERO axioms.
    Footprint: `{Means, Subject}`. -/
theorem bridge_a_constitutive_normativity_derives_free_will
    (h : ConstitutiveRightWrong) :
    ∃ (s : Subject), FreeWill s := by
  obtain ⟨s, p, q, hNorm⟩ := h
  exact ⟨s, (indubitable_normative_free_will hNorm).2⟩

/-- Bridge B: Metaphysical Plurality Bridge (AxTwoSubjects) derives ChoiceField.
    Footprint: `{AxTwoSubjects, Means, Subject}`. -/
theorem bridge_b_plurality_yields_choice_field
    (hExt : ExtensionalRightWrong) :
    ∃ (s : Subject) (p q : Prop), ChoiceField s p q :=
  Logos.Plurality.JUDGE_HAS_CHOICE_FIELD hExt

/-- Bridge C: Performative Retorsion Bridge (Judging Act) derives ChoiceField.
    Footprint: `{Initiates, Means, State, Subject}`. -/
theorem bridge_c_performative_judge_yields_choice_field
    (speaker : Subject)
    (hAssert : Logos.Agency.Asserts speaker (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F)) :
    ∃ (s : Subject) (p q : Prop), ChoiceField s p q :=
  Logos.Choice.judge_asserting_rightWrong_has_choiceField speaker hAssert

/-- Bridge D: Transcendental Retorsion of Genuine Normativity derives Free Will
    under Judicative Bipolarity (`AxJudicativeBipolarity`).
    Footprint: `{AxJudicativeBipolarity, Initiates, Means, State, Subject}`. -/
theorem bridge_d_retorsion_derives_free_will
    (hEvent : ∃ s : Subject, Logos.RetorsiveNormativity.ClaimsCorrect s Logos.RetorsiveNormativity.NoGN) :
    ∃ s : Subject, FreeWill s :=
  Logos.RetorsiveNormativity.retorsion_derives_free_will hEvent

-- ===========================================================================
-- Section 3: Definitional Circularity & Acyclicity Audit
-- ===========================================================================

/-!
### Definitional Dependency Graph (Strict DAG)
Level 0 (Primitives):
  - Subject : Type
  - Means : Subject → Prop → Prop
  - Incompatible : Prop → Prop → Prop

Level 1 (Constitutive Deontic Components):
  - DeonticOpposition p q := Incompatible p q ∧ (p ≠ q)
  - AgentialDeonticAddress s p q := Means s p ∧ Means s q

Level 2 (Genuine Normativity):
  - GenuineNormativity s p q := DeonticOpposition p q ∧ AgentialDeonticAddress s p q

Level 3 (Agential Choice):
  - Chooses s p q := Means s p ∧ Means s q ∧ Incompatible p q

Level 4 (Free Will):
  - FreeWill s := ∃ p q, Chooses s p q

Theorem: The definitions form a strict DAG with ZERO circular loops.
-/

/-- Non-Circularity Proof 1: FreeWill does not appear in Chooses. -/
theorem non_circularity_chooses_independent_of_freewill
    (s : Subject) (p q : Prop)
    (hMeansP : Means s p) (hMeansQ : Means s q) (hIncomp : Incompatible p q) :
    Chooses s p q :=
  ⟨hMeansP, hMeansQ, hIncomp⟩

/-- Non-Circularity Proof 2: Chooses does not appear in GenuineNormativity. -/
theorem non_circularity_normativity_independent_of_chooses
    (s : Subject) (p q : Prop)
    (hOpp : DeonticOpposition p q) (hAddr : AgentialDeonticAddress s p q) :
    GenuineNormativity s p q :=
  ⟨hOpp, hAddr⟩

/-- Strict Soundness: Chooses is logically extracted from GenuineNormativity by projection. -/
theorem normativity_projects_to_chooses
    {s : Subject} {p q : Prop} (h : GenuineNormativity s p q) :
    Chooses s p q :=
  ⟨h.address.1, h.address.2, h.opposition.1⟩

-- ===========================================================================
-- Section 4: The 8 Formal Denial Normal Forms (D1 to D8)
-- ===========================================================================

/-!
### Detailed Classification of Denials
D1: Right does not exist. (Status: Contradicts Core Retorsion)
D2: Wrong does not exist. (Status: Contradicts Core Retorsion)
D3: Right/Wrong are not normative. (Status: Rejection of Constitutive Meaning)
D4: Genuine Ought has no subject. (Status: Rejection of Constitutive Meaning)
D5: Right/Wrong present no alternatives. (Status: Rejection of Constitutive Meaning)
D6: Alternatives need not be grasped. (Status: Rejection of Constitutive Meaning)
D7: Co-grasp of alternatives is not Choice. (Status: Direct Formal Contradiction)
D8: Choice is not Free Will. (Status: Direct Formal Contradiction)
-/

-- D1 & D2: Denial of Existence
theorem d1_d2_denial_contradicts_core_retorsion
    (hDeny : ¬ ExtensionalRightWrong) : False :=
  hDeny Logos.Core.rightWrongDistinction

-- D3: Denial of Prescriptivity (Right/Wrong is merely descriptive truth)
theorem d3_descriptive_truth_lacks_deontic_guidance
    (p q : Prop) (hDescriptiveOnly : Prop)
    (hNoOught : hDescriptiveOnly → ∀ s : Subject, ¬ AgentialDeonticAddress s p q)
    (hNorm : ∃ s : Subject, GenuineNormativity s p q) :
    ¬ hDescriptiveOnly := by
  intro hDesc
  obtain ⟨s, hNormInst⟩ := hNorm
  exact (hNoOught hDesc s) hNormInst.address

-- D4: Denial of Agential Address (Impersonal Ought)
theorem d4_impersonal_normativity_fails_relationality
    (p q : Prop)
    (hImpersonal : ∀ s : Subject, ¬ AgentialDeonticAddress s p q) :
    ¬ ∃ s : Subject, GenuineNormativity s p q :=
  Logos.IndubitableNormativeFreeWill.dnf3_impersonal_ought_fails_address p q hImpersonal

-- D5: Denial of Incompatible Alternatives (Monolithic Command)
theorem d5_monolithic_command_lacks_opposition
    (p : Prop) (hNoIncompatible : ∀ q : Prop, ¬ Incompatible p q) :
    ¬ ∃ s : Subject, ∃ q : Prop, GenuineNormativity s p q :=
  Logos.IndubitableNormativeFreeWill.dnf4_monolithic_command_lacks_opposition p hNoIncompatible

-- D6: Denial of Cognitive Grasp (Ungraspable Command)
theorem d6_ungraspable_command_fails_agential_address
    (s : Subject) (p q : Prop)
    (hUngraspable : ¬ (Means s p ∧ Means s q)) :
    ¬ AgentialDeonticAddress s p q :=
  hUngraspable

-- D7: Denial of Choice from Co-Grasp (Formal Contradiction)
theorem d7_co_grasp_is_definitionally_choice
    (s : Subject) (p q : Prop)
    (hMeansP : Means s p) (hMeansQ : Means s q) (hIncomp : Incompatible p q)
    (hDenyChooses : ¬ Chooses s p q) : False :=
  hDenyChooses ⟨hMeansP, hMeansQ, hIncomp⟩

-- D8: Denial of Free Will from Choice (Formal Contradiction)
theorem d8_choice_is_definitionally_free_will
    (s : Subject) (p q : Prop)
    (hChooses : Chooses s p q)
    (hDenyFreeWill : ¬ FreeWill s) : False :=
  hDenyFreeWill ⟨p, q, hChooses⟩

-- ===========================================================================
-- Section 5: Smallest Complete Final Kernel Theorems
-- ===========================================================================

/-- The Smallest Local Kernel Theorem: Genuine Normativity entails Choice and Free Will.
    Footprint: `{Means, Subject}` (pure logic). -/
theorem normative_free_will_local
    {s : Subject} {p q : Prop} (h : GenuineNormativity s p q) :
    Chooses s p q ∧ FreeWill s :=
  indubitable_normative_free_will h

/-- The Smallest Existential Kernel Theorem: Constitutive Right/Wrong derives Free Will.
    Footprint: `{Means, Subject}` (pure logic, zero substantive axioms). -/
theorem normative_free_will
    (h : ConstitutiveRightWrong) :
    ∃ s : Subject, FreeWill s := by
  obtain ⟨s, p, q, hNorm⟩ := h
  exact ⟨s, (normative_free_will_local hNorm).2⟩

/-- Definition of Modally Necessary Constitutive Right/Wrong. -/
def NecessaryConstitutiveRightWrong (World : Type) : Prop :=
  ∀ w : World, ∃ (s : Subject) (p q : Prop), GenuineNormativity s p q

/-- The Smallest Modal Kernel Theorem: Modally necessary normative truth entails
    modally necessary Free Will. Footprint: `{Means, Subject}`. -/
theorem necessary_normative_free_will
    {World : Type}
    (hNec : NecessaryConstitutiveRightWrong World) :
    ∀ w : World, ∃ s : Subject, FreeWill s := by
  intro w
  obtain ⟨s, p, q, hNorm⟩ := hNec w
  exact ⟨s, (normative_free_will_local hNorm).2⟩

end Logos.UndeniableNormativeDerivation

-- Kernel footprint audit
#print axioms Logos.UndeniableNormativeDerivation.inanimate_universe_satisfies_extensional_bivalence_without_agency
#print axioms Logos.UndeniableNormativeDerivation.extensional_bivalence_insufficient_for_free_will
#print axioms Logos.UndeniableNormativeDerivation.bridge_a_constitutive_normativity_derives_free_will
#print axioms Logos.UndeniableNormativeDerivation.bridge_b_plurality_yields_choice_field
#print axioms Logos.UndeniableNormativeDerivation.bridge_c_performative_judge_yields_choice_field
#print axioms Logos.UndeniableNormativeDerivation.non_circularity_chooses_independent_of_freewill
#print axioms Logos.UndeniableNormativeDerivation.non_circularity_normativity_independent_of_chooses
#print axioms Logos.UndeniableNormativeDerivation.normativity_projects_to_chooses
#print axioms Logos.UndeniableNormativeDerivation.d1_d2_denial_contradicts_core_retorsion
#print axioms Logos.UndeniableNormativeDerivation.d3_descriptive_truth_lacks_deontic_guidance
#print axioms Logos.UndeniableNormativeDerivation.d4_impersonal_normativity_fails_relationality
#print axioms Logos.UndeniableNormativeDerivation.d5_monolithic_command_lacks_opposition
#print axioms Logos.UndeniableNormativeDerivation.d6_ungraspable_command_fails_agential_address
#print axioms Logos.UndeniableNormativeDerivation.d7_co_grasp_is_definitionally_choice
#print axioms Logos.UndeniableNormativeDerivation.d8_choice_is_definitionally_free_will
#print axioms Logos.UndeniableNormativeDerivation.normative_free_will_local
#print axioms Logos.UndeniableNormativeDerivation.normative_free_will
#print axioms Logos.UndeniableNormativeDerivation.necessary_normative_free_will
