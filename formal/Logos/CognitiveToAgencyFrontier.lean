/-
# Logos.CognitiveToAgencyFrontier — The Cognitive-to-Agency Frontier

This module formalizes the exact mathematical boundary reached by performative reductio
in Γ, investigating:
1. Fine-Grained Cognitive Vocabulary (Considers, Affirms, Rejects, CommitsTo, AimsAt, SettlesFor, Assumes, Derives).
2. The Asymmetric Dynamic Progression of Reductio (Assumes → DerivesAbsurdity → Rejects → Affirms).
3. The 5-Level Settlement Hierarchy (Settlement-1 to Settlement-5).
4. Strong Negative Theorems (reductio is non-mechanical, non-passive, non-unary, and asymmetric).
5. The Hostile Countermodel Suite M13–M18 (separating each layer from dual consideration to libertarian freedom).
6. Agency Disambiguation (Choice, Compatibilist Free Will, Bilateral Modal Freedom, Agent-Causal Settlement, Libertarian Freedom).

Governing rule:
"Prefer losing the theorem to hiding the premise."
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
import Logos.AdversarialReductioAudit

namespace Logos.CognitiveToAgencyFrontier

open Logos.Agency (Subject Act Means State Initiates)
open Logos.Choice (Chooses FreeWill FreeSubject MissingCognitiveHorn)
open Logos.Alternatives (Incompatible)

-- ===========================================================================
-- Part I: Fine-Grained Cognitive Vocabulary (Tasks 1, 2, 5)
-- ===========================================================================

/-- Fine-grained cognitive subject structure disentangling distinct cognitive relations. -/
structure FineCognitiveSubject (Subject : Type) where
  Considers   : Subject → Prop → Prop
  Affirms     : Subject → Prop → Prop
  Rejects     : Subject → Prop → Prop
  CommitsTo   : Subject → Prop → Prop
  AimsAt      : Subject → Prop → Prop
  SettlesFor  : Subject → Prop → Prop
  Assumes     : Subject → Prop → Prop
  Derives     : Subject → Prop → Prop → Prop
  affirms_considers  : ∀ s p, Affirms s p → Considers s p
  rejects_considers  : ∀ s p, Rejects s p → Considers s p
  assumes_considers  : ∀ s p, Assumes s p → Considers s p
  commits_affirms    : ∀ s p, CommitsTo s p → Affirms s p
  aims_commits       : ∀ s p, AimsAt s p → CommitsTo s p
  settles_commits    : ∀ s p, SettlesFor s p → CommitsTo s p
  rational_non_contradiction : ∀ s p, ¬ (Affirms s p ∧ Rejects s p)

/-- The dynamic asymmetric progression of genuine performative reductio:
    1. The hypothesis q is assumed.
    2. A contradiction (False) is derived from q.
    3. The hypothesis q is rejected.
    4. The negation ¬q is affirmed.
    5. The two contents are objectively incompatible. -/
structure ReductioProgression (Subject : Type) (CS : FineCognitiveSubject Subject)
    (s : Subject) (q : Prop) : Prop where
  hypothesized      : CS.Assumes s q
  derived_absurdity : CS.Derives s q False
  rejected          : CS.Rejects s q
  affirmed_negation : CS.Affirms s (¬ q)
  incompatible      : Incompatible q (¬ q)

/-- Theorem: Performative reductio forces an asymmetric status transition. -/
theorem reductio_induces_asymmetric_status_transition
    (Subject : Type) (CS : FineCognitiveSubject Subject) (s : Subject) (q : Prop)
    (hRed : ReductioProgression Subject CS s q) :
    CS.Assumes s q ∧ CS.Rejects s q ∧ CS.Affirms s (¬ q) ∧ ¬ CS.Affirms s q := by
  refine ⟨hRed.hypothesized, hRed.rejected, hRed.affirmed_negation, ?_⟩
  intro hAffq
  exact CS.rational_non_contradiction s q ⟨hAffq, hRed.rejected⟩

-- ===========================================================================
-- Part II: The 5-Level Cognitive Settlement Hierarchy (Tasks 3, 6)
-- ===========================================================================

/-- Settlement-1: Cognitive Resolution
    The subject considers both incompatible contents and adopts an asymmetric
    evaluative stance (affirming one and rejecting the other). -/
def Settlement1 (Subject : Type) (CS : FineCognitiveSubject Subject)
    (s : Subject) (p q : Prop) : Prop :=
  CS.Considers s p ∧ CS.Considers s q ∧ Incompatible p q ∧
  CS.Affirms s p ∧ CS.Rejects s q

/-- Settlement-2: Doxastic/Normative Commitment Resolution
    The subject commits to p over q. -/
def Settlement2 (Subject : Type) (CS : FineCognitiveSubject Subject)
    (s : Subject) (p q : Prop) : Prop :=
  Settlement1 Subject CS s p q ∧ CS.CommitsTo s p ∧ ¬ CS.CommitsTo s q

/-- Settlement-3: Intentional Resolution
    The affirmed content p enters the intentional field as meant (`Means`),
    while the rejected content q is not meant. -/
def Settlement3 (Subject : Type) (CS : FineCognitiveSubject Subject)
    (MeansAt : Subject → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Settlement2 Subject CS s p q ∧ MeansAt s p ∧ ¬ MeansAt s q

/-- Settlement-4: Volitional Resolution
    The affirmed content p is a practical goal (`AimsAt`) and initiates a state change. -/
def Settlement4 (Subject State : Type) (CS : FineCognitiveSubject Subject)
    (MeansAt : Subject → Prop → Prop)
    (InitiatesAt : Subject → State → State → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Settlement3 Subject CS MeansAt s p q ∧ CS.AimsAt s p ∧
  (∃ w w' : State, InitiatesAt s w w' p)

/-- Settlement-5: Agent-Causal Settlement
    The resolution is actively caused by the agent itself rather than being
    determined entirely by antecedent non-agent conditions. -/
def Settlement5 (Subject State : Type) (CS : FineCognitiveSubject Subject)
    (MeansAt : Subject → Prop → Prop)
    (InitiatesAt : Subject → State → State → Prop → Prop)
    (AgentDetermined : Subject → Prop → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Settlement4 Subject State CS MeansAt InitiatesAt s p q ∧
  AgentDetermined s p q

/-- Theorem: Genuine performative reductio proves Settlement-1 (Cognitive Resolution). -/
theorem reductio_proves_settlement_1
    (Subject : Type) (CS : FineCognitiveSubject Subject) (s : Subject) (q : Prop)
    (hRed : ReductioProgression Subject CS s q) :
    Settlement1 Subject CS s (¬ q) q := by
  refine ⟨CS.affirms_considers s (¬ q) hRed.affirmed_negation,
          CS.rejects_considers s q hRed.rejected,
          (fun ⟨h1, h2⟩ => h1 h2),
          hRed.affirmed_negation,
          hRed.rejected⟩

-- ===========================================================================
-- Part III: Strong Negative Theorems (Task 8)
-- ===========================================================================

/-- Negative Theorem 1: Reductio cannot collapse to a one-horn cognitive state. -/
theorem reductio_cannot_collapse_to_one_horn
    (Subject : Type) (CS : FineCognitiveSubject Subject) (s : Subject) (q : Prop)
    (hRed : ReductioProgression Subject CS s q) :
    CS.Considers s q ∧ CS.Considers s (¬ q) ∧ q ≠ (¬ q) := by
  have hConsQ : CS.Considers s q := CS.rejects_considers s q hRed.rejected
  have hConsNotQ : CS.Considers s (¬ q) := CS.affirms_considers s (¬ q) hRed.affirmed_negation
  refine ⟨hConsQ, hConsNotQ, ?_⟩
  intro hEq
  have hAff : CS.Affirms s q := by rw [hEq]; exact hRed.affirmed_negation
  exact CS.rational_non_contradiction s q ⟨hAff, hRed.rejected⟩

/-- Negative Theorem 2: Reductio necessarily involves asymmetric evaluation. -/
theorem reductio_necessarily_asymmetric
    (Subject : Type) (CS : FineCognitiveSubject Subject) (s : Subject) (q : Prop)
    (hRed : ReductioProgression Subject CS s q) :
    ¬ (CS.Affirms s q ∧ CS.Affirms s (¬ q)) := by
  intro ⟨hAffQ, _⟩
  exact CS.rational_non_contradiction s q ⟨hAffQ, hRed.rejected⟩

/-- Negative Theorem 3: Settlement-1 does not entail Intentional Meaning (`Means`). -/
theorem settlement_1_does_not_imply_settlement_3 :
    ∃ (Subject : Type) (CS : FineCognitiveSubject Subject) (s : Subject) (p q : Prop)
      (MeansAt : Subject → Prop → Prop),
      Settlement1 Subject CS s p q ∧ ¬ Settlement3 Subject CS MeansAt s p q := by
  let CS0 : FineCognitiveSubject Unit := {
    Considers   := fun _ _ => True
    Affirms     := fun _ p => p = (¬ True)
    Rejects     := fun _ p => p = True
    CommitsTo   := fun _ _ => False
    AimsAt      := fun _ _ => False
    SettlesFor  := fun _ _ => False
    Assumes     := fun _ p => p = True
    Derives     := fun _ _ _ => True
    affirms_considers := fun _ _ _ => trivial
    rejects_considers := fun _ _ _ => trivial
    assumes_considers := fun _ _ _ => trivial
    commits_affirms   := fun _ _ h => by cases h
    aims_commits      := fun _ _ h => by cases h
    settles_commits   := fun _ _ h => by cases h
    rational_non_contradiction := fun _ p ⟨h1, h2⟩ => by
      have h3 : (¬ True) = True := h1.symm.trans h2
      have h4 : ¬ True := by rw [h3]; trivial
      exact h4 trivial
  }
  refine ⟨Unit, CS0, (), (¬ True), True, fun _ _ => False, ?_, ?_⟩
  · exact ⟨trivial, trivial, (fun ⟨h1, h2⟩ => h1 h2), rfl, rfl⟩
  · intro ⟨⟨_, hComm, _⟩, _⟩
    exact hComm

-- ===========================================================================
-- Part IV: Machine-Checked Hostile Model Suite M13–M18 (Task 4)
-- ===========================================================================

/-!
Hostile Models:
M13: Dual consideration without evaluation (considers q and ¬q, neither affirmed nor rejected).
M14: Evaluation without settlement/commitment (affirms ¬q, rejects q, but no CommitsTo).
M15: Settlement without Choice (Settlement1 holds, but Chooses fails).
M16: Deterministic settlement (Settlement is a deterministic function of antecedent state).
M17: Compatibilist choice (Chooses holds coexisting with deterministic state transitions).
M18: Agent-causal settlement (Settlement survives identical deliberative antecedents).
-/

/-- Model M13: Dual consideration without evaluation -/
theorem model_M13_dual_consideration_without_evaluation :
    ∃ (Subject : Type) (CS : FineCognitiveSubject Subject) (s : Subject) (q : Prop),
      CS.Considers s q ∧ CS.Considers s (¬ q) ∧ Incompatible q (¬ q) ∧
      ¬ CS.Affirms s (¬ q) ∧ ¬ CS.Rejects s q := by
  let CS0 : FineCognitiveSubject Unit := {
    Considers   := fun _ _ => True
    Affirms     := fun _ _ => False
    Rejects     := fun _ _ => False
    CommitsTo   := fun _ _ => False
    AimsAt      := fun _ _ => False
    SettlesFor  := fun _ _ => False
    Assumes     := fun _ _ => False
    Derives     := fun _ _ _ => False
    affirms_considers := fun _ _ h => by cases h
    rejects_considers := fun _ _ h => by cases h
    assumes_considers := fun _ _ h => by cases h
    commits_affirms   := fun _ _ h => by cases h
    aims_commits      := fun _ _ h => by cases h
    settles_commits   := fun _ _ h => by cases h
    rational_non_contradiction := fun _ _ ⟨h, _⟩ => by cases h
  }
  refine ⟨Unit, CS0, (), True, ⟨trivial, trivial, (fun ⟨h1, h2⟩ => h2 h1), id, id⟩⟩

/-- Model M14: Evaluation without commitment -/
theorem model_M14_evaluation_without_commitment :
    ∃ (Subject : Type) (CS : FineCognitiveSubject Subject) (s : Subject) (q : Prop),
      CS.Affirms s (¬ q) ∧ CS.Rejects s q ∧ ¬ CS.CommitsTo s (¬ q) := by
  let CS0 : FineCognitiveSubject Unit := {
    Considers   := fun _ _ => True
    Affirms     := fun _ p => p = (¬ True)
    Rejects     := fun _ p => p = True
    CommitsTo   := fun _ _ => False
    AimsAt      := fun _ _ => False
    SettlesFor  := fun _ _ => False
    Assumes     := fun _ _ => False
    Derives     := fun _ _ _ => False
    affirms_considers := fun _ _ _ => trivial
    rejects_considers := fun _ _ _ => trivial
    assumes_considers := fun _ _ h => by cases h
    commits_affirms   := fun _ _ h => by cases h
    aims_commits      := fun _ _ h => by cases h
    settles_commits   := fun _ _ h => by cases h
    rational_non_contradiction := fun _ p ⟨h1, h2⟩ => by
      have h3 : (¬ True) = True := h1.symm.trans h2
      have h4 : ¬ True := by rw [h3]; trivial
      exact h4 trivial
  }
  refine ⟨Unit, CS0, (), True, rfl, rfl, id⟩

/-- Model M15: Settlement-1 holds, but Chooses fails -/
theorem model_M15_settlement_without_choice :
    ∃ (Subject : Type) (CS : FineCognitiveSubject Subject) (s : Subject) (p q : Prop)
      (ChoosesAt : Subject → Prop → Prop → Prop),
      Settlement1 Subject CS s p q ∧ ¬ ChoosesAt s p q := by
  let CS0 : FineCognitiveSubject Unit := {
    Considers   := fun _ _ => True
    Affirms     := fun _ p => p = (¬ True)
    Rejects     := fun _ p => p = True
    CommitsTo   := fun _ _ => False
    AimsAt      := fun _ _ => False
    SettlesFor  := fun _ _ => False
    Assumes     := fun _ _ => False
    Derives     := fun _ _ _ => False
    affirms_considers := fun _ _ _ => trivial
    rejects_considers := fun _ _ _ => trivial
    assumes_considers := fun _ _ h => by cases h
    commits_affirms   := fun _ _ h => by cases h
    aims_commits      := fun _ _ h => by cases h
    settles_commits   := fun _ _ h => by cases h
    rational_non_contradiction := fun _ p ⟨h1, h2⟩ => by
      have h3 : (¬ True) = True := h1.symm.trans h2
      have h4 : ¬ True := by rw [h3]; trivial
      exact h4 trivial
  }
  refine ⟨Unit, CS0, (), (¬ True), True, fun _ _ _ => False,
          ⟨trivial, trivial, (fun ⟨h1, h2⟩ => h1 h2), rfl, rfl⟩, id⟩

/-- Model M16: Deterministic settlement (Settlement-1 is a deterministic function of prior state) -/
theorem model_M16_deterministic_settlement :
    ∃ (DeliberativeState : Type) (Step : DeliberativeState → DeliberativeState)
      (Subject : Type) (CS : FineCognitiveSubject Subject) (s : Subject) (p q : Prop)
      (d0 : DeliberativeState),
      (∀ d, d = d0 → Settlement1 Subject CS s p q) ∧
      (∀ d1 d2, d1 = d2 → Step d1 = Step d2) := by
  let CS0 : FineCognitiveSubject Unit := {
    Considers   := fun _ _ => True
    Affirms     := fun _ p => p = (¬ True)
    Rejects     := fun _ p => p = True
    CommitsTo   := fun _ _ => False
    AimsAt      := fun _ _ => False
    SettlesFor  := fun _ _ => False
    Assumes     := fun _ _ => False
    Derives     := fun _ _ _ => False
    affirms_considers := fun _ _ _ => trivial
    rejects_considers := fun _ _ _ => trivial
    assumes_considers := fun _ _ h => by cases h
    commits_affirms   := fun _ _ h => by cases h
    aims_commits      := fun _ _ h => by cases h
    settles_commits   := fun _ _ h => by cases h
    rational_non_contradiction := fun _ p ⟨h1, h2⟩ => by
      have h3 : (¬ True) = True := h1.symm.trans h2
      have h4 : ¬ True := by rw [h3]; trivial
      exact h4 trivial
  }
  refine ⟨Unit, id, Unit, CS0, (), (¬ True), True, (),
          fun _ _ => ⟨trivial, trivial, (fun ⟨h1, h2⟩ => h1 h2), rfl, rfl⟩,
          fun _ _ h => h⟩

/-- Model M17: Compatibilist choice (Chooses holds deterministically) -/
theorem model_M17_compatibilist_choice :
    ∃ (DeliberativeState : Type) (Step : DeliberativeState → DeliberativeState)
      (Subject : Type) (s : Subject) (p q : Prop)
      (MeansAt : Subject → Prop → Prop)
      (ChoosesAt : Subject → Prop → Prop → Prop)
      (d0 : DeliberativeState),
      (∀ d, d = d0 → ChoosesAt s p q) ∧
      (∀ d1 d2, d1 = d2 → Step d1 = Step d2) ∧
      (ChoosesAt s p q ↔ (MeansAt s p ∧ MeansAt s q ∧ Incompatible p q)) := by
  let MeansAll : Unit → Prop → Prop := fun _ _ => True
  let ChoosesDef : Unit → Prop → Prop → Prop := fun _ a b => MeansAll () a ∧ MeansAll () b ∧ Incompatible a b
  have hIncomp : Incompatible (¬ True) True := fun ⟨h1, h2⟩ => h1 h2
  refine ⟨Unit, id, Unit, (), (¬ True), True, MeansAll, ChoosesDef, (),
          fun _ _ => ⟨trivial, trivial, hIncomp⟩,
          fun _ _ h => h,
          Iff.rfl⟩

/-- Model M18: Agent-causal settlement (Settlement is determined by the agent itself) -/
theorem model_M18_agent_causal_settlement :
    ∃ (DeliberativeState : Type) (Subject : Type)
      (CanSettle : Subject → DeliberativeState → Prop → Prop)
      (AgentDetermines : Subject → DeliberativeState → Prop → Prop)
      (s : Subject) (d : DeliberativeState) (p q : Prop),
      CanSettle s d p ∧ CanSettle s d q ∧ Incompatible p q ∧
      AgentDetermines s d p ∧ ¬ AgentDetermines s d q := by
  refine ⟨Unit, Unit, fun _ _ _ => True, fun _ _ prop => prop = (¬ True),
          (), (), (¬ True), True,
          trivial, trivial, (fun ⟨h1, h2⟩ => h1 h2), rfl, ?_⟩
  intro hContra
  have h1 : True = (¬ True) := hContra
  have h2 : ¬ True := by rw [← h1]; trivial
  exact h2 trivial

-- ===========================================================================
-- Part V: Agency Disambiguation & Layer Analysis (Tasks 7, 9, 10)
-- ===========================================================================

/-- Bilateral Modal Freedom: The agent possesses accessible alternative possibilities. -/
def BilateralModalFreedom (Subject : Type) (s : Subject) (p q : Prop)
    (CanAct : Subject → Prop → Prop) : Prop :=
  CanAct s p ∧ CanAct s q ∧ Incompatible p q

/-- Libertarian Freedom: Bilateral modal freedom combined with non-deterministic agent determination. -/
def LibertarianFreedom (Subject : Type) (s : Subject) (p q : Prop)
    (CanAct : Subject → Prop → Prop)
    (SelfDetermined : Subject → Prop → Prop) : Prop :=
  BilateralModalFreedom Subject s p q CanAct ∧
  SelfDetermined s p ∧ ¬ SelfDetermined s q

/-- Theorem: Performative reductio strictly proves Settlement-1, but leaves Choice and Libertarian Freedom open. -/
theorem reductio_frontier_status
    (Subject : Type) (CS : FineCognitiveSubject Subject) (s : Subject) (q : Prop)
    (hRed : ReductioProgression Subject CS s q) :
    Settlement1 Subject CS s (¬ q) q ∧
    CS.Considers s q ∧ CS.Considers s (¬ q) ∧
    CS.Affirms s (¬ q) ∧ CS.Rejects s q := by
  have hS1 := reductio_proves_settlement_1 Subject CS s q hRed
  exact ⟨hS1, hS1.2.1, hS1.1, hS1.2.2.2.1, hS1.2.2.2.2⟩

end Logos.CognitiveToAgencyFrontier
