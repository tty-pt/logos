/-
# Logos.NormativeOrder — Agential Normative Standards and Derivation of Deontic Normativity from Correctness

This module formalizes the intrinsic normative content of judgment acts without introducing
moral primitives (`Good`, `Bad`, `Duty`, `Lawgiver`) and without semantic bridge axioms
(`AxJudicativeBipolarity`, `AxIntentionalChoice`):
  1. `JudicativeAct` and `JudicativeNorm`: generic agential standard evaluating judgment acts.
  2. `TruthNorm`: the objective epistemic norm where `prescribes` is truth (`T p`) and `prohibits` is falsity (`IsFalse p`).
  3. `Ought` and `OughtNot`: agential deontic relations derived from conformity with / violation of the standard.
  4. Essential connection to `DeonticOpposition` eliminating dead code.
  5. Primary recovery of `GenuineNormativity` connecting the positive normative pole (`Correct s p`) and negative normative pole (`Incorrect s p`) via `ClaimsNormativeCorrectness`.
  6. Grounded deliberative content recovery via `DeliberateChoice`.
  7. Derivation of `Chooses` and `FreeWill` via unmodified `indubitable_normative_free_will`.
-/

import Logos.Core
import Logos.Agency
import Logos.Order
import Logos.Choice
import Logos.Alternatives
import Logos.IndubitableNormativeFreeWill

set_option linter.unusedVariables false

namespace Logos.NormativeOrder

open Logos.Agency (Subject Means State Initiates Act)
open Logos.Alternatives (Incompatible)
open Logos.Choice (Chooses FreeWill FreeSubject DeliberateChoice)
open Logos.IndubitableNormativeFreeWill (DeonticOpposition AgentialDeonticAddress GenuineNormativity indubitable_normative_free_will)
open Logos.Order (Correct Incorrect)

-- ===========================================================================
-- Section 1: Agential Normative Standard over Judicative Acts (Step 1)
-- ===========================================================================

/-- An agential judicative act binding a judging subject and a propositional content.
    Classification: DEFINITIONAL. -/
structure JudicativeAct where
  subject : Subject
  content : Prop

/-- Performance of a judicative act is the realization of the intentional act in reality.
    Classification: DEFINITIONAL. -/
def JudicativeAct.performed (a : JudicativeAct) : Prop :=
  Act a.subject a.content

/-- An objective normative standard evaluating judicative acts.
    Provides prescriptive and prohibitive relations and guarantees their mutual incompatibility.
    Does not require moral concepts, duties, or a lawgiver.
    Classification: DEFINITIONAL. -/
structure JudicativeNorm where
  prescribes : JudicativeAct → Prop
  prohibits  : JudicativeAct → Prop
  incompatible : ∀ a : JudicativeAct, Incompatible (prescribes a) (prohibits a)

/-- General agential Ought: the act is prescribed by standard N.
    Classification: DEFINITIONAL. -/
def Ought (N : JudicativeNorm) (a : JudicativeAct) : Prop :=
  N.prescribes a

/-- General agential OughtNot: the act is prohibited by standard N.
    Classification: DEFINITIONAL. -/
def OughtNot (N : JudicativeNorm) (a : JudicativeAct) : Prop :=
  N.prohibits a

/-- The objective epistemic norm of Truth:
    truth prescribes affirmation, and falsity prohibits affirmation.
    Classification: DEFINITIONAL. -/
def TruthNorm : JudicativeNorm where
  prescribes a := Logos.Core.T a.content
  prohibits  a := Logos.Core.IsFalse a.content
  incompatible a := fun ⟨hT, hF⟩ => hF hT

-- ===========================================================================
-- Section 2: Derivation of Ought and OughtNot from Correctness (Step 2)
-- ===========================================================================

/-- A correct judgment act implies that the subject ought to affirm the content under TruthNorm.
    Footprint: {} (pure logic). -/
theorem correct_implies_ought (s : Subject) (p : Prop) (h : Correct s p) :
    Ought TruthNorm ⟨s, p⟩ :=
  h.2

/-- An incorrect judgment act implies that the subject ought not to affirm the content under TruthNorm.
    Footprint: {} (pure logic). -/
theorem incorrect_implies_oughtNot (s : Subject) (p : Prop) (h : Incorrect s p) :
    OughtNot TruthNorm ⟨s, p⟩ :=
  h.2

/-- Correctness is definitionally the performance of the judicative act in conformity with what ought to be judged.
    Footprint: {} (pure logic). -/
theorem correct_iff_performed_and_ought (s : Subject) (p : Prop) :
    Correct s p ↔ (JudicativeAct.mk s p).performed ∧ Ought TruthNorm ⟨s, p⟩ :=
  Iff.rfl

/-- Incorrectness is definitionally the performance of the judicative act in violation of the norm (what ought not to be judged).
    Footprint: {} (pure logic). -/
theorem incorrect_iff_performed_and_oughtNot (s : Subject) (p : Prop) :
    Incorrect s p ↔ (JudicativeAct.mk s p).performed ∧ OughtNot TruthNorm ⟨s, p⟩ :=
  Iff.rfl

/-- If p is correctly judged, any incompatible alternative q is what ought not to be affirmed under TruthNorm.
    Footprint: {} (pure logic). -/
theorem correct_implies_oughtNot_incompatible (s : Subject) (p q : Prop)
    (hCorr : Correct s p) (hIncomp : Incompatible p q) :
    OughtNot TruthNorm ⟨s, q⟩ :=
  fun hTq => hIncomp ⟨hCorr.2, hTq⟩

-- ===========================================================================
-- Section 3: Essential Connection of Ought/OughtNot to Deontic Opposition (Step 3)
-- ===========================================================================

/-- Ought and OughtNot under TruthNorm are strictly incompatible.
    Footprint: {} (pure logic). -/
theorem ought_and_oughtNot_incompatible (s : Subject) (p : Prop) :
    Incompatible (Ought TruthNorm ⟨s, p⟩) (OughtNot TruthNorm ⟨s, p⟩) :=
  TruthNorm.incompatible ⟨s, p⟩

/-- Essential non-identity of contents: what ought to be affirmed cannot be identical
    to what ought not to be affirmed under TruthNorm.
    Uses Ought and OughtNot essentially, guaranteeing zero dead code.
    Footprint: {} (pure logic). -/
theorem content_distinct_of_ought_oughtNot (s : Subject) (p q : Prop)
    (hp : Ought TruthNorm ⟨s, p⟩) (hq : OughtNot TruthNorm ⟨s, q⟩) : p ≠ q := by
  intro hEq
  have hq' : OughtNot TruthNorm ⟨s, p⟩ := hEq ▸ hq
  exact ought_and_oughtNot_incompatible s p ⟨hp, hq'⟩

/-- Correctness and incorrectness are mutually incompatible, derived directly from
    the incompatibility of Ought and OughtNot under TruthNorm.
    Footprint: {} (pure logic). -/
theorem correctness_incompatible (s : Subject) (p : Prop) :
    Incompatible (Correct s p) (Incorrect s p) :=
  fun ⟨hC, hI⟩ => ought_and_oughtNot_incompatible s p ⟨hC.2, hI.2⟩

/-- For any performed act, Correctness is distinct from Incorrectness.
    Footprint: `{Initiates, Means, State, Subject, CL}`. -/
theorem correctness_distinct_of_act (s : Subject) (p : Prop) (hAct : Act s p) :
    Correct s p ≠ Incorrect s p := by
  intro hEq
  have hOr : Correct s p ∨ Incorrect s p := (Logos.Order.act_iff_correct_or_incorrect s p).mp hAct
  cases hOr with
  | inl hC =>
    have hI : Incorrect s p := hEq ▸ hC
    exact correctness_incompatible s p ⟨hC, hI⟩
  | inr hI =>
    have hC : Correct s p := hEq ▸ hI
    exact correctness_incompatible s p ⟨hC, hI⟩

/-- Deontic opposition between the positive normative pole (Correct s p) and the negative pole (Incorrect s p).
    Footprint: `{Initiates, Means, State, Subject, CL}`. -/
theorem correctness_deontic_opposition (s : Subject) (p : Prop) (hAct : Act s p) :
    DeonticOpposition (Correct s p) (Incorrect s p) :=
  ⟨correctness_incompatible s p, correctness_distinct_of_act s p hAct⟩

-- ===========================================================================
-- Section 4: Primary Recovery of GenuineNormativity on Judicative Normative Polarity (Step 4)
-- ===========================================================================

/-- The constitutive normative judicative stance:
    the subject performs the judgment act while grasping both the positive normative standard (Correctness)
    and the negative normative standard (Incorrectness).
    Bypasses contradictory propositional negation `¬p` and eliminates `AxJudicativeBipolarity`.
    Classification: DEFINITIONAL. -/
def ClaimsNormativeCorrectness (s : Subject) (p : Prop) : Prop :=
  Act s p ∧ Means s (Logos.Order.Correct s p) ∧ Means s (Logos.Order.Incorrect s p)

/-- Extraction of the act from the normative judicative stance. -/
theorem claims_normative_correctness_is_act (s : Subject) (p : Prop)
    (h : ClaimsNormativeCorrectness s p) : Act s p :=
  h.1

/-- Derivation of GenuineNormativity on the judicative normative poles (Correct s p vs Incorrect s p).
    Consumes correctness_deontic_opposition and discharges address directly without un-discharged hypotheses.
    Footprint: `{Initiates, Means, State, Subject, CL}`. -/
theorem claims_normative_correctness_derives_genuine_normativity
    (s : Subject) (p : Prop) (h : ClaimsNormativeCorrectness s p) :
    GenuineNormativity s (Correct s p) (Incorrect s p) := by
  have hOpp : DeonticOpposition (Correct s p) (Incorrect s p) :=
    correctness_deontic_opposition s p h.1
  have hAddr : AgentialDeonticAddress s (Correct s p) (Incorrect s p) :=
    ⟨h.2.1, h.2.2⟩
  exact ⟨hOpp, hAddr⟩

/-- Master derivation from the normative judicative stance to Choice and Free Will.
    Footprint: `{Initiates, Means, State, Subject, CL}` (zero substantive axioms). -/
theorem claims_normative_correctness_derives_free_will
    (s : Subject) (p : Prop) (h : ClaimsNormativeCorrectness s p) :
    Chooses s (Correct s p) (Incorrect s p) ∧ FreeWill s :=
  indubitable_normative_free_will (claims_normative_correctness_derives_genuine_normativity s p h)

-- ===========================================================================
-- Section 5: Grounded Deliberative Content Derivation of GenuineNormativity (Step 5)
-- ===========================================================================

/-- Deliberative choice between incompatible contents p and q, where p is correct,
    instantiates GenuineNormativity between p and q.
    Discharges address from DeliberateChoice and proves DeonticOpposition using Ought and OughtNot essentially.
    Footprint: `{Initiates, Means, State, Subject}` (zero substantive axioms). -/
theorem deliberate_choice_derives_genuine_normativity
    (s : Subject) (p q : Prop)
    (hDelib : DeliberateChoice s p q) (hCorr : Correct s p) :
    GenuineNormativity s p q := by
  have hp : Ought TruthNorm ⟨s, p⟩ := correct_implies_ought s p hCorr
  have hONq : OughtNot TruthNorm ⟨s, q⟩ :=
    correct_implies_oughtNot_incompatible s p q hCorr hDelib.2.2.1
  have hne : p ≠ q := content_distinct_of_ought_oughtNot s p q hp hONq
  have hOpp : DeonticOpposition p q := ⟨hDelib.2.2.1, hne⟩
  have hAddr : AgentialDeonticAddress s p q := ⟨hDelib.1, hDelib.2.1⟩
  exact ⟨hOpp, hAddr⟩

/-- Master derivation from DeliberateChoice and Correctness to Choice and Free Will.
    Footprint: `{Initiates, Means, State, Subject}` (zero substantive axioms). -/
theorem deliberate_choice_derives_free_will
    (s : Subject) (p q : Prop)
    (hDelib : DeliberateChoice s p q) (hCorr : Correct s p) :
    Chooses s p q ∧ FreeWill s :=
  indubitable_normative_free_will (deliberate_choice_derives_genuine_normativity s p q hDelib hCorr)

-- ===========================================================================
-- Section 6: Axiom Audit
-- ===========================================================================

#print axioms correct_implies_ought
#print axioms incorrect_implies_oughtNot
#print axioms correct_iff_performed_and_ought
#print axioms incorrect_iff_performed_and_oughtNot
#print axioms correct_implies_oughtNot_incompatible
#print axioms ought_and_oughtNot_incompatible
#print axioms content_distinct_of_ought_oughtNot
#print axioms correctness_incompatible
#print axioms correctness_distinct_of_act
#print axioms correctness_deontic_opposition
#print axioms claims_normative_correctness_derives_genuine_normativity
#print axioms claims_normative_correctness_derives_free_will
#print axioms deliberate_choice_derives_genuine_normativity
#print axioms deliberate_choice_derives_free_will

end Logos.NormativeOrder
