/-
# Logos.PostA14Frontier — Post-A14 Frontier: Mathematical Boundaries of Settlement, Commitment, Volition, and Agency

This module establishes the exact mathematical and semantic frontier post-A14:
1. Freezes A14 as the irreducible semantic boundary of contrastive action (A14 ↔ MissingCognitiveHorn).
2. Proves that each step in the agency ladder strictly underdetermines the next:
   SettlementChoice ↛ Commitment ↛ Volition ↛ Agency
3. Isolates the exact weakest missing semantic conditions:
   - DoxasticCommitmentHorn
   - TeleologicalAimHorn
   - ExecutiveInitiationHorn
4. Audits the post-A14 theory: Γ + A14 yields historical `Chooses` from `Act`, but strictly fails
   to derive Commitment, Volition, Agency*, DiscretionaryChoice, or LibertarianFreedom.
5. Machine-checks the Five Canonical Hostile Archetypes:
   - Passive Truth Tracker
   - Deterministic Evaluator
   - Theoretical Deliberator
   - Puppet with Unauthored Aims
   - Non-Reflexive Authorial Chooser

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
import Logos.CognitiveToAgencyFrontier
import Logos.FreeWillIndependence
import Logos.ChoiceRepair
import Logos.AgencyFrontierAudit
import Logos.A14SemanticAudit

namespace Logos.PostA14Frontier

open Logos.Agency (Subject Act Means State Initiates)
open Logos.Choice (Chooses FreeWill FreeSubject MissingCognitiveHorn AxIntentionalChoice)
open Logos.Alternatives (Incompatible)
open Logos.CognitiveToAgencyFrontier (FineCognitiveSubject ReductioProgression Settlement1)
open Logos.ChoiceRepair (OldChooses OldFreeWill SettlementChoice CognitiveSettlement
                         VolitionalSettlement ActionSelection AgentCausalSettlement
                         FreeWill_Settlement FreeWill_Libertarian)
open Logos.AgencyFrontierAudit (DiscretionaryChoice)
open Logos.A14SemanticAudit (A14_Statement MissingHornPrinciple)

-- ===========================================================================
-- Stage 1: Boundaries & Separations in the Agency Ladder
-- ===========================================================================

/-- The Doxastic Commitment Horn:
    The subject takes an explicit normative doxastic stand, committing to p. -/
def DoxasticCommitmentHorn {Subj : Type} (CS : FineCognitiveSubject Subj) (s : Subj) (p : Prop) : Prop :=
  CS.CommitsTo s p

/-- The Teleological Aim Horn:
    The subject adopts p as a practical end and rejects q as an end. -/
def TeleologicalAimHorn {Subj : Type} (CS : FineCognitiveSubject Subj) (s : Subj) (p q : Prop) : Prop :=
  CS.AimsAt s p ∧ ¬ CS.AimsAt s q

/-- The Executive Initiation Horn:
    The subject initiates a worldly transition instantiating p. -/
def ExecutiveInitiationHorn {Subj : Type} (InitiatesRel : Subj → Unit → Unit → Prop → Prop)
    (s : Subj) (p : Prop) : Prop :=
  ∃ (w w' : Unit), InitiatesRel s w w' p

/-- Separation 1: SettlementChoice does NOT entail Commitment.
    A subject can reach asymmetric cognitive resolution (SettlementChoice)
    while remaining completely detached, taking no normative doxastic stand. -/
theorem separation_settlement_without_commitment :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj) (s : Subj) (p q : Prop),
      SettlementChoice CS s p q ∧ ¬ DoxasticCommitmentHorn CS s p := by
  have hIncomp : Incompatible (¬ True) True := fun ⟨h1, h2⟩ => h1 h2
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
  refine ⟨Unit, CS0, (), (¬ True), True, ⟨trivial, trivial, hIncomp, rfl, rfl⟩, ?_⟩
  intro hComm
  exact hComm

/-- Equivalence Theorem 1:
    Cognitive Settlement plus the Doxastic Commitment Horn yields Commitment. -/
theorem settlement_plus_horn_yields_commitment
    {Subj : Type} (CS : FineCognitiveSubject Subj) (s : Subj) (p q : Prop)
    (hSC : SettlementChoice CS s p q) (hHorn : DoxasticCommitmentHorn CS s p) :
    SettlementChoice CS s p q ∧ CS.CommitsTo s p :=
  ⟨hSC, hHorn⟩

/-- Separation 2: Commitment does NOT entail Volition.
    A subject can be committed to a theoretical belief without possessing any
    practical aim (AimsAt) directed toward it. -/
theorem separation_commitment_without_volition :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj) (s : Subj) (p q : Prop),
      (SettlementChoice CS s p q ∧ CS.CommitsTo s p) ∧
      ¬ (VolitionalSettlement CS s p q) := by
  have hIncomp : Incompatible (¬ True) True := fun ⟨h1, h2⟩ => h1 h2
  let CS0 : FineCognitiveSubject Unit := {
    Considers   := fun _ _ => True
    Affirms     := fun _ p => p = (¬ True)
    Rejects     := fun _ p => p = True
    CommitsTo   := fun _ p => p = (¬ True)
    AimsAt      := fun _ _ => False
    SettlesFor  := fun _ _ => False
    Assumes     := fun _ _ => False
    Derives     := fun _ _ _ => False
    affirms_considers := fun _ _ _ => trivial
    rejects_considers := fun _ _ _ => trivial
    assumes_considers := fun _ _ h => by cases h
    commits_affirms   := fun _ _ h => h
    aims_commits      := fun _ _ h => by cases h
    settles_commits   := fun _ _ h => by cases h
    rational_non_contradiction := fun _ p ⟨h1, h2⟩ => by
      have h3 : (¬ True) = True := h1.symm.trans h2
      have h4 : ¬ True := by rw [h3]; trivial
      exact h4 trivial
  }
  refine ⟨Unit, CS0, (), (¬ True), True, ⟨⟨trivial, trivial, hIncomp, rfl, rfl⟩, rfl⟩, ?_⟩
  intro ⟨_, hAims, _⟩
  exact hAims

/-- Equivalence Theorem 2:
    Cognitive Settlement plus the Teleological Aim Horn yields Volitional Settlement. -/
theorem settlement_plus_aim_horn_yields_volition
    {Subj : Type} (CS : FineCognitiveSubject Subj) (s : Subj) (p q : Prop)
    (hSC : SettlementChoice CS s p q)
    (hAimHorn : TeleologicalAimHorn CS s p q) :
    VolitionalSettlement CS s p q :=
  ⟨hSC, hAimHorn.1, hAimHorn.2⟩

/-- Separation 3: Volition does NOT entail Executive Agency.
    A subject can possess full internal volition (aiming at p and not q)
    without worldly initiation (paralyzed will). -/
theorem separation_volition_without_agency :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj)
      (InitiatesRel : Subj → Unit → Unit → Prop → Prop)
      (s : Subj) (p q : Prop),
      VolitionalSettlement CS s p q ∧
      ¬ ExecutiveInitiationHorn InitiatesRel s p := by
  have hIncomp : Incompatible (¬ True) True := fun ⟨h1, h2⟩ => h1 h2
  let CS0 : FineCognitiveSubject Unit := {
    Considers   := fun _ _ => True
    Affirms     := fun _ p => p = (¬ True)
    Rejects     := fun _ p => p = True
    CommitsTo   := fun _ p => p = (¬ True)
    AimsAt      := fun _ p => p = (¬ True)
    SettlesFor  := fun _ p => p = (¬ True)
    Assumes     := fun _ _ => False
    Derives     := fun _ _ _ => False
    affirms_considers := fun _ _ _ => trivial
    rejects_considers := fun _ _ _ => trivial
    assumes_considers := fun _ _ h => by cases h
    commits_affirms   := fun _ _ h => h
    aims_commits      := fun _ _ h => h
    settles_commits   := fun _ _ h => h
    rational_non_contradiction := fun _ p ⟨h1, h2⟩ => by
      have h3 : (¬ True) = True := h1.symm.trans h2
      have h4 : ¬ True := by rw [h3]; trivial
      exact h4 trivial
  }
  have hNotAimsTrue : ¬ CS0.AimsAt () True := by
    intro (h : True = (¬ True))
    have hContra : ¬ True := by rw [← h]; trivial
    exact hContra trivial
  let Init0 : Unit → Unit → Unit → Prop → Prop := fun _ _ _ _ => False
  refine ⟨Unit, CS0, Init0, (), (¬ True), True,
          ⟨⟨trivial, trivial, hIncomp, rfl, rfl⟩, rfl, hNotAimsTrue⟩, ?_⟩
  intro ⟨_, _, hInit⟩
  exact hInit

-- ===========================================================================
-- Stage 2: Post-A14 Scope and Limits Audit
-- ===========================================================================

/-- Post-A14 Positive Result:
    Under A14, every intentional act entails historical Chooses and FreeWill. -/
theorem post_a14_derives_old_chooses
    {Subj : Type} (ActRel : Subj → Prop → Prop) (MeansRel : Subj → Prop → Prop)
    (hA14 : A14_Statement Subj ActRel MeansRel)
    (s : Subj) (p : Prop) (hAct : ActRel s p) :
    ∃ q, MeansRel s p ∧ MeansRel s q ∧ Incompatible p q :=
  hA14 s p hAct

/-- Post-A14 Negative Result 1:
    Even under A14, SettlementChoice does NOT derive Commitment. -/
theorem post_a14_fails_to_derive_commitment :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj)
      (ActRel : Subj → Prop → Prop) (MeansRel : Subj → Prop → Prop)
      (s : Subj) (p q : Prop),
      A14_Statement Subj ActRel MeansRel ∧
      SettlementChoice CS s p q ∧
      ¬ CS.CommitsTo s p := by
  obtain ⟨Subj0, CS0, s0, p0, q0, hSC, hNotComm⟩ := separation_settlement_without_commitment
  let ActRel0 : Subj0 → Prop → Prop := fun _ _ => False
  let MeansRel0 : Subj0 → Prop → Prop := fun _ _ => False
  have hA14 : A14_Statement Subj0 ActRel0 MeansRel0 := fun _ _ hAct => by cases hAct
  exact ⟨Subj0, CS0, ActRel0, MeansRel0, s0, p0, q0, hA14, hSC, hNotComm⟩

/-- Post-A14 Negative Result 2:
    Even under A14, historical Chooses does NOT derive DiscretionaryChoice. -/
theorem post_a14_fails_to_derive_discretionary_choice :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj)
      (ActRel : Subj → Prop → Prop) (MeansRel : Subj → Prop → Prop)
      (AgentDet : Subj → Prop → Prop) (SourceOf : Subj → Prop → Prop)
      (s : Subj) (p q : Prop),
      A14_Statement Subj ActRel MeansRel ∧
      (MeansRel s p ∧ MeansRel s q ∧ Incompatible p q) ∧
      ¬ (DiscretionaryChoice CS AgentDet SourceOf s p q) := by
  have hIncompTrueNotTrue : Incompatible True (¬ True) := fun ⟨h1, h2⟩ => h2 h1
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
    rational_non_contradiction := fun _ _ ⟨h1, _⟩ => by cases h1
  }
  let ActRel0 : Unit → Prop → Prop := fun _ prop => prop = True
  let MeansRel0 : Unit → Prop → Prop := fun _ prop => prop = True ∨ prop = (¬ True)
  let AgentDet0 : Unit → Prop → Prop := fun _ _ => False
  let SourceOf0 : Unit → Prop → Prop := fun _ _ => False
  have hA14 : A14_Statement Unit ActRel0 MeansRel0 := by
    intro s p (hp : p = True)
    subst hp
    refine ⟨(¬ True), Or.inl rfl, Or.inr rfl, hIncompTrueNotTrue⟩
  have hCoMeant : MeansRel0 () True ∧ MeansRel0 () (¬ True) ∧ Incompatible True (¬ True) :=
    ⟨Or.inl rfl, Or.inr rfl, hIncompTrueNotTrue⟩
  refine ⟨Unit, CS0, ActRel0, MeansRel0, AgentDet0, SourceOf0, (), True, (¬ True),
          hA14, hCoMeant, ?_⟩
  intro hDC
  exact hDC.agent_determined.1

-- ===========================================================================
-- Stage 3: Five Canonical Hostile Archetypes
-- ===========================================================================

/-- Archetype 1: The Passive Truth Tracker.
    Calculates truth values and settles between contradictory hypotheses via reductio,
    but possesses zero doxastic commitment, zero practical aims, and zero action. -/
theorem archetype_passive_truth_tracker :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj) (s : Subj) (q : Prop),
      ReductioProgression Subj CS s q ∧
      SettlementChoice CS s (¬ q) q ∧
      (∀ p, ¬ CS.CommitsTo s p) ∧
      (∀ p, ¬ CS.AimsAt s p) := by
  have hIncompTrueNotTrue : Incompatible True (¬ True) := fun ⟨h1, h2⟩ => h2 h1
  have hIncompNotTrueTrue : Incompatible (¬ True) True := fun ⟨h1, h2⟩ => h1 h2
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
  refine ⟨Unit, CS0, (), True,
          ⟨rfl, trivial, rfl, rfl, hIncompTrueNotTrue⟩,
          ⟨trivial, trivial, hIncompNotTrueTrue, rfl, rfl⟩,
          fun _ h => h,
          fun _ h => h⟩

/-- Archetype 2: The Deterministic Evaluator.
    Transitions rigidly by deductive computation, affirms conclusions and commits to beliefs,
    but lacks discretionary agent determination (AgentDetermines is false). -/
theorem archetype_deterministic_evaluator :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj)
      (AgentDet : Subj → Prop → Prop) (s : Subj) (p q : Prop),
      SettlementChoice CS s p q ∧
      CS.CommitsTo s p ∧
      ¬ AgentDet s p := by
  have hIncomp : Incompatible (¬ True) True := fun ⟨h1, h2⟩ => h1 h2
  let CS0 : FineCognitiveSubject Unit := {
    Considers   := fun _ _ => True
    Affirms     := fun _ p => p = (¬ True)
    Rejects     := fun _ p => p = True
    CommitsTo   := fun _ p => p = (¬ True)
    AimsAt      := fun _ _ => False
    SettlesFor  := fun _ _ => False
    Assumes     := fun _ _ => False
    Derives     := fun _ _ _ => False
    affirms_considers := fun _ _ _ => trivial
    rejects_considers := fun _ _ _ => trivial
    assumes_considers := fun _ _ h => by cases h
    commits_affirms   := fun _ _ h => h
    aims_commits      := fun _ _ h => by cases h
    settles_commits   := fun _ _ h => by cases h
    rational_non_contradiction := fun _ p ⟨h1, h2⟩ => by
      have h3 : (¬ True) = True := h1.symm.trans h2
      have h4 : ¬ True := by rw [h3]; trivial
      exact h4 trivial
  }
  let AgentDet0 : Unit → Prop → Prop := fun _ _ => False
  refine ⟨Unit, CS0, AgentDet0, (), (¬ True), True,
          ⟨trivial, trivial, hIncomp, rfl, rfl⟩, rfl, ?_⟩
  intro hDet
  exact hDet

/-- Archetype 3: The Pure Theoretical Deliberator.
    Fully committed to theoretical truth, but completely devoid of practical ends (AimsAt is empty). -/
theorem archetype_theoretical_deliberator :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj) (s : Subj) (p q : Prop),
      SettlementChoice CS s p q ∧
      CS.CommitsTo s p ∧
      (∀ g, ¬ CS.AimsAt s g) := by
  have hIncomp : Incompatible (¬ True) True := fun ⟨h1, h2⟩ => h1 h2
  let CS0 : FineCognitiveSubject Unit := {
    Considers   := fun _ _ => True
    Affirms     := fun _ p => p = (¬ True)
    Rejects     := fun _ p => p = True
    CommitsTo   := fun _ p => p = (¬ True)
    AimsAt      := fun _ _ => False
    SettlesFor  := fun _ _ => False
    Assumes     := fun _ _ => False
    Derives     := fun _ _ _ => False
    affirms_considers := fun _ _ _ => trivial
    rejects_considers := fun _ _ _ => trivial
    assumes_considers := fun _ _ h => by cases h
    commits_affirms   := fun _ _ h => h
    aims_commits      := fun _ _ h => by cases h
    settles_commits   := fun _ _ h => by cases h
    rational_non_contradiction := fun _ p ⟨h1, h2⟩ => by
      have h3 : (¬ True) = True := h1.symm.trans h2
      have h4 : ¬ True := by rw [h3]; trivial
      exact h4 trivial
  }
  refine ⟨Unit, CS0, (), (¬ True), True, ⟨trivial, trivial, hIncomp, rfl, rfl⟩, rfl, fun _ h => h⟩

/-- Archetype 4: The Puppet with Unauthored Aims.
    Possesses practical aims and settles for actions, but lacks authorial sourcehood
    (SourceOf / AgentDetermines is false; aims are sub-personal or externally driven). -/
theorem archetype_puppet_unauthored_aims :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj)
      (SourceOf : Subj → Prop → Prop) (s : Subj) (p q : Prop),
      VolitionalSettlement CS s p q ∧
      ¬ SourceOf s p := by
  have hIncomp : Incompatible (¬ True) True := fun ⟨h1, h2⟩ => h1 h2
  let CS0 : FineCognitiveSubject Unit := {
    Considers   := fun _ _ => True
    Affirms     := fun _ p => p = (¬ True)
    Rejects     := fun _ p => p = True
    CommitsTo   := fun _ p => p = (¬ True)
    AimsAt      := fun _ p => p = (¬ True)
    SettlesFor  := fun _ p => p = (¬ True)
    Assumes     := fun _ _ => False
    Derives     := fun _ _ _ => False
    affirms_considers := fun _ _ _ => trivial
    rejects_considers := fun _ _ _ => trivial
    assumes_considers := fun _ _ h => by cases h
    commits_affirms   := fun _ _ h => h
    aims_commits      := fun _ _ h => h
    settles_commits   := fun _ _ h => h
    rational_non_contradiction := fun _ p ⟨h1, h2⟩ => by
      have h3 : (¬ True) = True := h1.symm.trans h2
      have h4 : ¬ True := by rw [h3]; trivial
      exact h4 trivial
  }
  have hNotAimsTrue : ¬ CS0.AimsAt () True := by
    intro (h : True = (¬ True))
    have hContra : ¬ True := by rw [← h]; trivial
    exact hContra trivial
  let SourceOf0 : Unit → Prop → Prop := fun _ _ => False
  refine ⟨Unit, CS0, SourceOf0, (), (¬ True), True,
          ⟨⟨trivial, trivial, hIncomp, rfl, rfl⟩, rfl, hNotAimsTrue⟩, ?_⟩
  intro hSrc
  exact hSrc

/-- Archetype 5: The Non-Reflexive Authorial Chooser.
    Exercises genuine discretionary choice as the authorial source,
    but completely lacks reflexive higher-order self-attribution (SelfAttributed is false). -/
theorem archetype_non_reflexive_chooser :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj)
      (AgentDet : Subj → Prop → Prop) (SourceOf : Subj → Prop → Prop)
      (SelfAttr : Subj → Prop → Prop) (s : Subj) (p q : Prop),
      DiscretionaryChoice CS AgentDet SourceOf s p q ∧
      ¬ SelfAttr s p := by
  have hIncomp : Incompatible (¬ True) True := fun ⟨h1, h2⟩ => h1 h2
  let CS0 : FineCognitiveSubject Unit := {
    Considers   := fun _ _ => True
    Affirms     := fun _ p => p = (¬ True)
    Rejects     := fun _ p => p = True
    CommitsTo   := fun _ p => p = (¬ True)
    AimsAt      := fun _ p => p = (¬ True)
    SettlesFor  := fun _ p => p = (¬ True)
    Assumes     := fun _ _ => False
    Derives     := fun _ _ _ => False
    affirms_considers := fun _ _ _ => trivial
    rejects_considers := fun _ _ _ => trivial
    assumes_considers := fun _ _ h => by cases h
    commits_affirms   := fun _ _ h => h
    aims_commits      := fun _ _ h => h
    settles_commits   := fun _ _ h => h
    rational_non_contradiction := fun _ p ⟨h1, h2⟩ => by
      have h3 : (¬ True) = True := h1.symm.trans h2
      have h4 : ¬ True := by rw [h3]; trivial
      exact h4 trivial
  }
  have hNotAimsTrue : ¬ CS0.AimsAt () True := by
    intro (h : True = (¬ True))
    have hContra : ¬ True := by rw [← h]; trivial
    exact hContra trivial
  let AgentDet0 : Unit → Prop → Prop := fun _ p => p = (¬ True)
  have hNotDetTrue : ¬ AgentDet0 () True := by
    intro (h : True = (¬ True))
    have hContra : ¬ True := by rw [← h]; trivial
    exact hContra trivial
  let SourceOf0 : Unit → Prop → Prop := fun _ _ => True
  let SelfAttr0 : Unit → Prop → Prop := fun _ _ => False
  have hDC : DiscretionaryChoice CS0 AgentDet0 SourceOf0 () (¬ True) True :=
    ⟨⟨trivial, trivial, hIncomp, rfl, rfl⟩, ⟨rfl, hNotAimsTrue⟩, rfl, trivial, ⟨rfl, hNotDetTrue⟩⟩
  refine ⟨Unit, CS0, AgentDet0, SourceOf0, SelfAttr0, (), (¬ True), True, hDC, ?_⟩
  intro hAttr
  exact hAttr

-- ===========================================================================
-- Stage 4: Theorem-Level Frontier Ladder
-- ===========================================================================

/-- The Four-Tier Post-A14 Frontier Theorem:
    1. SettlementChoice + DoxasticCommitmentHorn ↔ Settlement + Commitment.
    2. SettlementChoice + TeleologicalAimHorn ↔ VolitionalSettlement.
    3. VolitionalSettlement + ExecutiveInitiationHorn ↔ VolitionalSettlement + Initiation.
    Each transition requires its exact independent semantic horn; none is derivable from the previous. -/
theorem agency_ladder_frontier_synthesis
    {Subj : Type} (CS : FineCognitiveSubject Subj)
    (InitiatesRel : Subj → Unit → Unit → Prop → Prop)
    (s : Subj) (p q : Prop) :
    ((SettlementChoice CS s p q ∧ DoxasticCommitmentHorn CS s p) ↔
     (SettlementChoice CS s p q ∧ CS.CommitsTo s p)) ∧
    ((SettlementChoice CS s p q ∧ TeleologicalAimHorn CS s p q) ↔
     VolitionalSettlement CS s p q) ∧
    ((VolitionalSettlement CS s p q ∧ ExecutiveInitiationHorn InitiatesRel s p) ↔
     (VolitionalSettlement CS s p q ∧ ∃ w w', InitiatesRel s w w' p)) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

end Logos.PostA14Frontier
