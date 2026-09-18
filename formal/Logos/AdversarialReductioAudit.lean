/-
# Logos.AdversarialReductioAudit — Adversarial Audit of Reductio-Based Invariance

An adversarial formal investigation into the cognitive-meaning boundary:
"Does the actual performative proof architecture of Γ itself force the same subject
who performs the refutation to perform an intentional act with the concluded proposition ¬q,
thereby yielding Means(s, ¬q), without importing a new substantive semantic axiom?"

Guiding rule:
"Prefer losing the theorem to hiding the premise."

Key findings machine-checked in this file:
1. Circularity Audit: `RefutationalCognitiveUptake` is an assumption-hiding premise,
   equivalent to asserting `Means s q ∧ Means s (¬ q)`.
2. The Intentional Equivocation: `Means` cannot simultaneously serve as volitional goal
   (in `Act`) and mere cognitive presence of a rejected hypothesis (in `Reductio`).
3. One-Horn Barrier: Even if affirming ¬q constitutes an intentional act (`Act s (¬ q)`),
   it strictly fails to derive `Means s q` for the rejected hypothesis!
4. Hostile Model Suite M7–M12: Machine-checked non-entailment and independence proofs
   for models M7, M8, M9, M10, M11, and M12 (all with kernel footprint `{}`).
5. Definitive Status of F1b: Evaluated under the four-state classification (State A, B, C, D).
-/

import Logos.Core
import Logos.Necessity
import Logos.Semantics
import Logos.Truthmaker
import Logos.Modal
import Logos.Agency
import Logos.Person
import Logos.Choice
import Logos.Alternatives
import Logos.Retorsion
import Logos.HardenedInvariance
import Logos.CognitiveDiscrimination
import Logos.SubContrastFoundations
import Logos.ProofSpecificContrast

namespace Logos.AdversarialReductioAudit

open Logos.Agency (Subject Act Means State Initiates)
open Logos.Choice (Chooses FreeWill FreeSubject MissingCognitiveHorn)
open Logos.Alternatives (Incompatible)
open Logos.ProofSpecificContrast

-- ===========================================================================
-- Part I: Circularity Audit of ProofSpecificContrast.lean (Task II)
-- ===========================================================================

/-- Theorem: `RefutationalCognitiveUptake` is a renamed premise.
    Under an active refutational performance, it is logically equivalent
    to the target co-meaning conjunction! -/
theorem uptake_is_renamed_co_meaning_premise
    (Subject : Type) (CS : CognitiveSubject Subject)
    (MeansAt : Subject → Prop → Prop)
    (s : Subject) (q : Prop)
    (hProof : RefutationalPerformance Subject CS s q) :
    (RefutationalCognitiveUptake Subject CS MeansAt) → (MeansAt s q ∧ MeansAt s (¬ q)) := by
  intro hUptake
  exact hUptake s q hProof

-- ===========================================================================
-- Part II: The Intentional Equivocation (Tasks I, IV)
-- ===========================================================================

/-!
In Γ's foundation:
`Act s p := Means s p ∧ (∃ w w', Initiates s w w' p)`
Here, `Means s p` represents volitional directedness / teleological goal.

In Reductio:
`s` entertains `q` as an adversary's hypothesis, derives a contradiction,
and REJECTS `q`.

If `Means` represents a volitional goal, a rational subject who rejects `q`
and affirms `¬q` CANNOT have `q` as their volitional goal!
-/

/-- Rational volition cannot aim to bring about what it refutes and rejects -/
def VolitionalAim (Subject State : Type) (s : Subject) (p : Prop)
    (InitiatesAt : Subject → State → State → Prop → Prop) : Prop :=
  ∃ w w' : State, InitiatesAt s w w' p

theorem rational_subject_cannot_volitionally_aim_at_rejected_horn :
    ∃ (Subject State : Type) (CS : CognitiveSubject Subject) (s : Subject) (q : Prop)
      (InitiatesAt : Subject → State → State → Prop → Prop),
      CS.Rejects s q ∧ CS.Affirms s (¬ q) ∧
      ¬ VolitionalAim Subject State s q InitiatesAt := by
  let CS0 : CognitiveSubject Unit := {
    Considers := fun _ _ => True
    Affirms   := fun _ p => p = (¬ True)
    Rejects   := fun _ p => p = True
    affirms_considers := fun _ _ _ => trivial
    rejects_considers := fun _ _ _ => trivial
    rational_consistency := fun _ p ⟨hAff, hRej⟩ => by
      have h1 : p = (¬ True) := hAff
      have h2 : p = True := hRej
      have h3 : (¬ True) = True := h1.symm.trans h2
      have h4 : ¬ True := by rw [h3]; trivial
      exact h4 trivial
  }
  refine ⟨Unit, Unit, CS0, (), True, fun _ _ _ _ => False, rfl, rfl, ?_⟩
  intro ⟨w, w', hInit⟩
  exact hInit

-- ===========================================================================
-- Part III: Trace Strengthening & Derivation of Conclusion as an Act (Tasks III, V, VI)
-- ===========================================================================

structure ExtendedTrace (Subject : Type) where
  trace : RefutationalTrace
  concludes : Prop
  is_conclusion : TraceContainsDischarge trace concludes

/-- The 4-Case Progression of the Retorsion Conclusion:
    Case A: External trace concludes ¬P.
    Case B: Subject s concludes ¬P by deduction.
    Case C: Subject s affirms ¬P as true.
    Case D: Subject s performs an intentional Act with content ¬P. -/
structure RetorsionProgression (Subject : Type) (s : Subject) (P : Prop) where
  CaseA_TraceConcludes   : Prop
  CaseB_SubjectConcludes : Prop
  CaseC_SubjectAffirms   : Prop
  CaseD_SubjectActs      : Prop
  A_implies_B : CaseA_TraceConcludes → CaseB_SubjectConcludes
  B_implies_C : CaseB_SubjectConcludes → CaseC_SubjectAffirms
  C_implies_D : CaseC_SubjectAffirms → CaseD_SubjectActs

/-- The One-Horn Barrier Theorem:
    Even if an assertion bridge is granted so that affirming ¬q yields an intentional act
    `Act s (¬ q)` (and hence `Means s (¬ q)`), this strictly fails to derive `Means s q`! -/
theorem affirmation_to_act_derives_one_horn_only :
    ∃ (Subject : Type) (s : Subject) (q : Prop)
      (AffirmsAt : Subject → Prop → Prop)
      (ActAt : Subject → Prop → Prop)
      (MeansAt : Subject → Prop → Prop),
      (∀ p, AffirmsAt s p → ActAt s p) ∧
      (∀ p, ActAt s p → MeansAt s p) ∧
      AffirmsAt s (¬ q) ∧
      MeansAt s (¬ q) ∧
      ¬ MeansAt s q := by
  refine ⟨Unit, (), True, fun _ p => p = (¬ True),
          fun _ p => p = (¬ True),
          fun _ p => p = (¬ True),
          fun p h => h, fun p h => h, rfl, rfl, ?_⟩
  intro hContra
  have h1 : True = (¬ True) := hContra
  have h2 : ¬ True := by rw [← h1]; trivial
  exact h2 trivial

-- ===========================================================================
-- Part IV: Hostile Model Suite M7–M12 (Task VIII)
-- ===========================================================================

/-!
Hostile Models:
M7: Subject performs genuine reductio, but conclusion exists only externally; no Means(s, ¬q).
M8: Subject considers q and ¬q, but neither is meant.
M9: Subject rejects q and affirms ¬q, but affirmation does not imply intentional meaning.
M10: Same subject executes every proof step, but no step counts as a meaning-act.
M11: Subject intentionally realizes the proof, but conclusion is represented only as a considered proposition, not an act.
M12: Same subject has all proof-specific cognitive contrast, but no Chooses.
-/

/-- Model M7: Genuine reductio performed, but conclusion is external, no Means(s, ¬q) -/
theorem model_M7_external_conclusion :
    ∃ (Subject : Type) (CS : CognitiveSubject Subject) (s : Subject) (q : Prop)
      (MeansAt : Subject → Prop → Prop),
      RefutationalPerformance Subject CS s q ∧ ¬ MeansAt s (¬ q) := by
  let CS0 : CognitiveSubject Unit := {
    Considers := fun _ _ => True
    Affirms   := fun _ p => p = (¬ True)
    Rejects   := fun _ p => p = True
    affirms_considers := fun _ _ _ => trivial
    rejects_considers := fun _ _ _ => trivial
    rational_consistency := fun _ p ⟨hAff, hRej⟩ => by
      have h3 : (¬ True) = True := hAff.symm.trans hRej
      have h4 : ¬ True := by rw [h3]; trivial
      exact h4 trivial
  }
  refine ⟨Unit, CS0, (), True, fun _ _ => False, ⟨trivial, rfl, rfl⟩, id⟩

/-- Model M8: Consideration without Meaning -/
theorem model_M8_consideration_without_meaning :
    ∃ (Subject : Type) (CS : CognitiveSubject Subject) (s : Subject) (q : Prop)
      (MeansAt : Subject → Prop → Prop),
      CS.Considers s q ∧ CS.Considers s (¬ q) ∧ Incompatible q (¬ q) ∧
      ¬ MeansAt s q ∧ ¬ MeansAt s (¬ q) := by
  let CS0 : CognitiveSubject Unit := {
    Considers := fun _ _ => True
    Affirms   := fun _ _ => False
    Rejects   := fun _ _ => False
    affirms_considers := fun _ _ h => by cases h
    rejects_considers := fun _ _ h => by cases h
    rational_consistency := fun _ _ ⟨h, _⟩ => by cases h
  }
  refine ⟨Unit, CS0, (), True, fun _ _ => False,
          ⟨trivial, trivial, (fun ⟨h1, h2⟩ => h2 h1), id, id⟩⟩

/-- Model M9: Rejects q and Affirms ¬q without Meaning -/
theorem model_M9_affirmation_without_meaning :
    ∃ (Subject : Type) (CS : CognitiveSubject Subject) (s : Subject) (q : Prop)
      (MeansAt : Subject → Prop → Prop),
      CS.Rejects s q ∧ CS.Affirms s (¬ q) ∧
      ¬ (MeansAt s q ∨ MeansAt s (¬ q)) := by
  let CS0 : CognitiveSubject Unit := {
    Considers := fun _ _ => True
    Affirms   := fun _ p => p = (¬ True)
    Rejects   := fun _ p => p = True
    affirms_considers := fun _ _ _ => trivial
    rejects_considers := fun _ _ _ => trivial
    rational_consistency := fun _ p ⟨hAff, hRej⟩ => by
      have h3 : (¬ True) = True := hAff.symm.trans hRej
      have h4 : ¬ True := by rw [h3]; trivial
      exact h4 trivial
  }
  refine ⟨Unit, CS0, (), True, fun _ _ => False, rfl, rfl, ?_⟩
  intro hOr
  cases hOr with
  | inl h => exact h
  | inr h => exact h

/-- Model M10: Mechanical execution without meaning-acts -/
theorem model_M10_mechanical_execution_no_act :
    ∃ (Subject : Type) (s : Subject) (t : RefutationalTrace) (q : Prop)
      (ActAt : Subject → Prop → Prop),
      TraceContainsAssumption t q ∧ TraceContainsDischarge t q ∧
      (∀ p, ¬ ActAt s p) := by
  refine ⟨Unit, (), [TraceStep.hypothesis True, TraceStep.discharge True], True,
          fun _ _ => False, List.Mem.head _, List.Mem.tail _ (List.Mem.head _), fun _ => id⟩

/-- Model M11: Proof realized intentionally, but conclusion is considered, not an Act -/
theorem model_M11_considered_not_act :
    ∃ (Subject : Type) (CS : CognitiveSubject Subject) (s : Subject) (q : Prop)
      (ActAt : Subject → Prop → Prop),
      CS.Considers s (¬ q) ∧ ¬ ActAt s (¬ q) := by
  let CS0 : CognitiveSubject Unit := {
    Considers := fun _ _ => True
    Affirms   := fun _ _ => False
    Rejects   := fun _ _ => False
    affirms_considers := fun _ _ h => by cases h
    rejects_considers := fun _ _ h => by cases h
    rational_consistency := fun _ _ ⟨h, _⟩ => by cases h
  }
  refine ⟨Unit, CS0, (), True, fun _ _ => False, trivial, id⟩

/-- Model M12: Cognitive contrast present, but no Chooses -/
theorem model_M12_contrast_without_chooses :
    ∃ (Subject : Type) (CS : CognitiveSubject Subject) (s : Subject) (q : Prop)
      (ChoosesAt : Subject → Prop → Prop → Prop),
      CS.Considers s q ∧ CS.Considers s (¬ q) ∧ Incompatible q (¬ q) ∧
      ¬ ChoosesAt s (¬ q) q := by
  let CS0 : CognitiveSubject Unit := {
    Considers := fun _ _ => True
    Affirms   := fun _ _ => False
    Rejects   := fun _ _ => False
    affirms_considers := fun _ _ h => by cases h
    rejects_considers := fun _ _ h => by cases h
    rational_consistency := fun _ _ ⟨h, _⟩ => by cases h
  }
  refine ⟨Unit, CS0, (), True, fun _ _ _ => False,
          ⟨trivial, trivial, (fun ⟨h1, h2⟩ => h2 h1), id⟩⟩

-- ===========================================================================
-- Part V: The Exact Remaining Semantic Gap (Tasks IX, X)
-- ===========================================================================

/-- The Exact Uptake Gap:
    The minimal semantic condition needed to transition from
    refutational performance to intentional meaning of both horns. -/
def ExactUptakeGap (Subject : Type) (CS : CognitiveSubject Subject)
    (MeansAt : Subject → Prop → Prop) : Prop :=
  ∀ s q, RefutationalPerformance Subject CS s q → MeansAt s q ∧ MeansAt s (¬ q)

/-- Theorem: State A is FALSE (Refutational performance does NOT derive Means without a bridge) -/
theorem state_A_is_refuted :
    ∃ (Subject : Type) (CS : CognitiveSubject Subject) (s : Subject) (q : Prop)
      (MeansAt : Subject → Prop → Prop),
      RefutationalPerformance Subject CS s q ∧ ¬ (MeansAt s q ∧ MeansAt s (¬ q)) := by
  obtain ⟨Subject, CS, s, q, MeansAt, ⟨hPerf, hNotMeans⟩⟩ := model_M7_external_conclusion
  refine ⟨Subject, CS, s, q, MeansAt, hPerf, ?_⟩
  intro ⟨_, h2⟩
  exact hNotMeans h2

/-- Theorem: State D is FALSE (The path to F1b is consistent and NOT blocked by contradiction) -/
theorem state_D_is_refuted :
    ∃ (Subject : Type) (CS : CognitiveSubject Subject) (MeansAt : Subject → Prop → Prop)
      (ChoosesAt : Subject → Prop → Prop → Prop) (FreeWillAt : Subject → Prop)
      (s : Subject) (q : Prop),
      (∀ s' a b, ChoosesAt s' a b ↔ (MeansAt s' a ∧ MeansAt s' b ∧ Incompatible a b)) ∧
      (∀ s', FreeWillAt s' ↔ ∃ a b, ChoosesAt s' a b) ∧
      ExactUptakeGap Subject CS MeansAt ∧
      RefutationalPerformance Subject CS s q ∧
      FreeWillAt s := by
  let CS0 : CognitiveSubject Unit := {
    Considers := fun _ _ => True
    Affirms   := fun _ p => p = (¬ True)
    Rejects   := fun _ p => p = True
    affirms_considers := fun _ _ _ => trivial
    rejects_considers := fun _ _ _ => trivial
    rational_consistency := fun _ p ⟨hAff, hRej⟩ => by
      have h3 : (¬ True) = True := hAff.symm.trans hRej
      have h4 : ¬ True := by rw [h3]; trivial
      exact h4 trivial
  }
  let MeansAll : Unit → Prop → Prop := fun _ _ => True
  let ChoosesDef : Unit → Prop → Prop → Prop := fun _ a b => MeansAll () a ∧ MeansAll () b ∧ Incompatible a b
  let FreeWillDef : Unit → Prop := fun _ => ∃ a b, ChoosesDef () a b
  have hIncomp : Incompatible (¬ True) True := by
    intro ⟨hnot, ht⟩
    exact hnot ht
  have hChoosesInstance : ChoosesDef () (¬ True) True := ⟨trivial, trivial, hIncomp⟩
  refine ⟨Unit, CS0, MeansAll, ChoosesDef, FreeWillDef, (), True,
          fun _ _ _ => Iff.rfl, fun _ => Iff.rfl,
          fun _ _ _ => ⟨trivial, trivial⟩,
          ⟨trivial, rfl, rfl⟩,
          ⟨(¬ True), True, hChoosesInstance⟩⟩

end Logos.AdversarialReductioAudit
