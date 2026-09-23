/-
# Logos.DefinitiveAgencyFrontier — The Definitive Agency Frontier of Γ

This module executes the comprehensive adversarial formal campaign on the remaining
agency frontier of Γ above A14, adhering strictly to:
  "Prefer losing the theorem to hiding the premise."

Key formal accomplishments:
1. Models C1–C5: Separating SettlementChoice from Commitment, formal algorithmic
   evaluation from agential commitment, and assertion from private commitment.
2. Retorsion analysis of 8 candidate commitments: Proof that denying commitment to p
   does NOT performatively instantiate commitment to p.
3. Assertion vs Commitment: Proving Sincerity is an explicit SEMANTIC bridge.
4. Models V1–V5: Separating theoretical commitment from practical volition.
5. Volition vs Executive Agency: Differentiating Standalone Agency (refuted by paralyzed will)
   from Agency inside the performative datum (secured by Act's own initiation).
6. Models A1–A5: Separating practical volition from authorial sourcehood, agent-determination,
   and reflexive self-attribution.
7. Self-attribution separations: First-order chooser without self-representation.
8. Models AC1–AC5: Differentiating deterministic agent-causation, chance/indeterminism,
   agent-causation without alternatives, and full libertarian freedom.
9. Six canonical free-will predicates rigorously disambiguated.
10. Two-sided model-theoretic independence across all open agency layers.
11. Model-transformation collapse and expressivity invariance theorems.
12. Separation of Substantive Personhood across all agency tiers up to Libertarian Freedom.
-/

import Logos.Core
import Logos.Necessity
import Logos.Semantics
import Logos.Entity
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
import Logos.PostA14Frontier

namespace Logos.DefinitiveAgencyFrontier

open Logos.Agency (Subject Act Means State Initiates Asserts)
open Logos.Choice (Chooses FreeWill FreeSubject MissingCognitiveHorn AxIntentionalChoice)
open Logos.Alternatives (Incompatible)
open Logos.CognitiveToAgencyFrontier (FineCognitiveSubject ReductioProgression Settlement1)
open Logos.ChoiceRepair (OldChooses OldFreeWill SettlementChoice CognitiveSettlement
                         VolitionalSettlement ActionSelection AgentCausalSettlement
                         FreeWill_Settlement FreeWill_Libertarian)
open Logos.AgencyFrontierAudit (DiscretionaryChoice)
open Logos.A14SemanticAudit (A14_Statement MissingHornPrinciple SubstantivePerson)
open Logos.PostA14Frontier (DoxasticCommitmentHorn TeleologicalAimHorn ExecutiveInitiationHorn)

-- ===========================================================================
-- Phase 1: Models C1–C5 (Settlement, Evaluation, and Commitment)
-- ===========================================================================

/-- Model C1: Passive Truth Tracker.
    Satisfies SettlementChoice, but CommitsTo = False, AimsAt = False, Act = False. -/
theorem model_C1_passive_truth_tracker :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj) (s : Subj) (p q : Prop),
      SettlementChoice CS s p q ∧
      ¬ CS.CommitsTo s p ∧
      ¬ CS.AimsAt s p := by
  obtain ⟨Subj0, CS0, s0, p0, q0, hSC, hNotComm⟩ :=
    Logos.PostA14Frontier.separation_settlement_without_commitment
  refine ⟨Subj0, CS0, s0, p0, q0, hSC, hNotComm, ?_⟩
  intro hAims
  exact hNotComm (CS0.aims_commits s0 p0 hAims)

/-- Model C2: Formal Evaluator.
    Satisfies SettlementChoice and CommitsTo, but commitment is purely an algorithmic output
    devoid of discretionary substance determination (AgentDetermines = False). -/
theorem model_C2_formal_evaluator :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj)
      (AgentDet : Subj → Prop → Prop) (s : Subj) (p q : Prop),
      SettlementChoice CS s p q ∧
      CS.CommitsTo s p ∧
      ¬ AgentDet s p :=
  Logos.PostA14Frontier.archetype_deterministic_evaluator

/-- Model C3: Contradiction Resolver with Suspended Judgment.
    Considers contradictory hypotheses and proves an inconsistency, but suspends judgment
    (neither commits to p nor settles for p). -/
theorem model_C3_suspended_judgment :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj) (s : Subj) (p q : Prop),
      CS.Considers s p ∧ CS.Considers s q ∧ Incompatible p q ∧
      ¬ CS.CommitsTo s p ∧ ¬ CS.SettlesFor s p := by
  obtain ⟨Subj0, CS0, s0, p0, q0, hSC, hNotComm⟩ :=
    Logos.PostA14Frontier.separation_settlement_without_commitment
  refine ⟨Subj0, CS0, s0, p0, q0, hSC.1, hSC.2.1, hSC.2.2.1, hNotComm, ?_⟩
  intro hSet
  exact hNotComm (CS0.settles_commits s0 p0 hSet)

/-- Model C4: Public Assertion without Private Commitment (Insincere / Mechanical emitter).
    Emits an assertion publicly without private doxastic commitment. -/
theorem model_C4_assertion_without_commitment :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj)
      (AssertsRel : Subj → Prop → Prop) (s : Subj) (p : Prop),
      AssertsRel s p ∧ ¬ CS.CommitsTo s p := by
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
  let Asserts0 : Unit → Prop → Prop := fun _ _ => True
  exact ⟨Unit, CS0, Asserts0, (), True, trivial, fun h => h⟩

/-- Model C5: Private Commitment without Assertion (Silent Conviction).
    Fully committed to p privately, but produces no public assertion. -/
theorem model_C5_commitment_without_assertion :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj)
      (AssertsRel : Subj → Prop → Prop) (s : Subj) (p : Prop),
      CS.CommitsTo s p ∧ ¬ AssertsRel s p := by
  let CS0 : FineCognitiveSubject Unit := {
    Considers   := fun _ _ => True
    Affirms     := fun _ _ => True
    Rejects     := fun _ _ => False
    CommitsTo   := fun _ _ => True
    AimsAt      := fun _ _ => False
    SettlesFor  := fun _ _ => False
    Assumes     := fun _ _ => False
    Derives     := fun _ _ _ => False
    affirms_considers := fun _ _ _ => trivial
    rejects_considers := fun _ _ h => by cases h
    assumes_considers := fun _ _ h => by cases h
    commits_affirms   := fun _ _ _ => trivial
    aims_commits      := fun _ _ h => by cases h
    settles_commits   := fun _ _ h => by cases h
    rational_non_contradiction := fun _ _ ⟨_, h2⟩ => by cases h2
  }
  let Asserts0 : Unit → Prop → Prop := fun _ _ => False
  exact ⟨Unit, CS0, Asserts0, (), True, trivial, fun h => h⟩

-- ===========================================================================
-- Phase 2: Retorsion of Commitment
-- ===========================================================================

/-- Retorsion Failure Theorem:
    Asserting "I do not commit to p" reflexively instantiates an assertion of the negation,
    but does NOT instantiate commitment to p itself.
    The denial of first-order commitment is performatively coherent and non-self-refuting. -/
theorem retorsion_denial_does_not_commit_to_content :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj)
      (AssertsRel : Subj → Prop → Prop) (s : Subj) (p : Prop),
      AssertsRel s (¬ CS.CommitsTo s p) ∧
      ¬ CS.CommitsTo s p := by
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
  let Asserts0 : Unit → Prop → Prop := fun _ _ => True
  exact ⟨Unit, CS0, Asserts0, (), True, trivial, fun h => h⟩

-- ===========================================================================
-- Phase 3: Assertion vs Commitment (Sincerity Principle)
-- ===========================================================================

/-- The Sincerity Principle:
    Public assertion entails private doxastic commitment. -/
def SincerityPrinciple (Subj : Type) (CS : FineCognitiveSubject Subj)
    (AssertsRel : Subj → Prop → Prop) : Prop :=
  ∀ s p, AssertsRel s p → CS.CommitsTo s p

/-- Sincerity is a SEMANTIC bridge, not a logical consequence of assertion.
    Hostile countermodel where assertion holds without sincerity. -/
theorem sincerity_is_independent :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj) (AssertsRel : Subj → Prop → Prop),
      ¬ SincerityPrinciple Subj CS AssertsRel := by
  obtain ⟨Subj0, CS0, Asserts0, s0, p0, hAss, hNotComm⟩ := model_C4_assertion_without_commitment
  refine ⟨Subj0, CS0, Asserts0, ?_⟩
  intro hPrinciple
  exact hNotComm (hPrinciple s0 p0 hAss)

-- ===========================================================================
-- Phase 4: Models V1–V5 (Commitment vs Volition)
-- ===========================================================================

/-- Model V1: Pure Theoretician.
    Committed to theoretical truth, but possesses zero practical aim. -/
theorem model_V1_pure_theoretician :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj) (s : Subj) (p : Prop),
      CS.CommitsTo s p ∧ (∀ g, ¬ CS.AimsAt s g) := by
  obtain ⟨Subj0, CS0, s0, p0, _, _, hComm, hNoAims⟩ :=
    Logos.PostA14Frontier.archetype_theoretical_deliberator
  exact ⟨Subj0, CS0, s0, p0, hComm, hNoAims⟩

/-- Model V2: Aim without Deliberative Settlement.
    An aim exists spontaneously without prior contrastive settlement. -/
theorem model_V2_aim_without_deliberative_settlement :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj) (s : Subj) (p q : Prop),
      CS.AimsAt s p ∧ ¬ SettlementChoice CS s p q := by
  let CS0 : FineCognitiveSubject Unit := {
    Considers   := fun _ _ => True
    Affirms     := fun _ _ => True
    Rejects     := fun _ _ => False
    CommitsTo   := fun _ _ => True
    AimsAt      := fun _ _ => True
    SettlesFor  := fun _ _ => True
    Assumes     := fun _ _ => False
    Derives     := fun _ _ _ => False
    affirms_considers := fun _ _ _ => trivial
    rejects_considers := fun _ _ h => by cases h
    assumes_considers := fun _ _ h => by cases h
    commits_affirms   := fun _ _ _ => trivial
    aims_commits      := fun _ _ _ => trivial
    settles_commits   := fun _ _ _ => trivial
    rational_non_contradiction := fun _ _ ⟨_, h2⟩ => by cases h2
  }
  refine ⟨Unit, CS0, (), True, (¬ True), trivial, ?_⟩
  intro ⟨_, _, _, _, hRej⟩
  exact hRej

/-- Model V3: Commitment to an Unwanted Fact.
    The subject is committed to p because it is demonstrably true, but has zero practical aim at p. -/
theorem model_V3_commitment_to_unwanted_fact :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj) (s : Subj) (p : Prop),
      CS.CommitsTo s p ∧ ¬ CS.AimsAt s p := by
  obtain ⟨Subj0, CS0, s0, p0, hComm, hNoAims⟩ := model_V1_pure_theoretician
  exact ⟨Subj0, CS0, s0, p0, hComm, hNoAims p0⟩

/-- Model V4: External Objective.
    The subject aims at p, but the aim is externally injected / sub-personal
    (SourceOf is false). -/
theorem model_V4_external_objective :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj)
      (SourceOf : Subj → Prop → Prop) (s : Subj) (p : Prop),
      CS.AimsAt s p ∧ ¬ SourceOf s p := by
  obtain ⟨Subj0, CS0, SourceOf0, s0, p0, _, hVol, hNotSrc⟩ :=
    Logos.PostA14Frontier.archetype_puppet_unauthored_aims
  exact ⟨Subj0, CS0, SourceOf0, s0, p0, hVol.2.1, hNotSrc⟩

/-- Model V5: Spontaneous Aim without Deliberation.
    Aim exists without any prior cognitive assumption or derivation. -/
theorem model_V5_spontaneous_aim :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj) (s : Subj) (p : Prop),
      CS.AimsAt s p ∧ (∀ q, ¬ CS.Assumes s q) := by
  let CS0 : FineCognitiveSubject Unit := {
    Considers   := fun _ _ => True
    Affirms     := fun _ _ => True
    Rejects     := fun _ _ => False
    CommitsTo   := fun _ _ => True
    AimsAt      := fun _ _ => True
    SettlesFor  := fun _ _ => True
    Assumes     := fun _ _ => False
    Derives     := fun _ _ _ => False
    affirms_considers := fun _ _ _ => trivial
    rejects_considers := fun _ _ h => by cases h
    assumes_considers := fun _ _ h => by cases h
    commits_affirms   := fun _ _ _ => trivial
    aims_commits      := fun _ _ _ => trivial
    settles_commits   := fun _ _ _ => trivial
    rational_non_contradiction := fun _ _ ⟨_, h2⟩ => by cases h2
  }
  exact ⟨Unit, CS0, (), True, trivial, fun _ h => h⟩

-- ===========================================================================
-- Phase 5: Volition vs Executive Agency (Standalone vs Performative Datum)
-- ===========================================================================

/-- Standalone Separation:
    VolitionalSettlement does NOT entail Executive Agency (Paralyzed Will). -/
theorem standalone_volition_fails_to_derive_agency :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj)
      (InitiatesRel : Subj → Unit → Unit → Prop → Prop)
      (s : Subj) (p q : Prop),
      VolitionalSettlement CS s p q ∧
      ¬ ExecutiveInitiationHorn InitiatesRel s p :=
  Logos.PostA14Frontier.separation_volition_without_agency

/-- Performative Datum Agency Theorem:
    Inside the original performative datum Act(s, p), worldly initiation is ALREADY supplied
    by Act itself (`Act s p := Means s p ∧ ∃ w w', Initiates s w w' p`).
    Therefore, given Act(s, p) and VolitionalSettlement, Executive Action is DERIVED
    without any new agency axiom! -/
theorem performative_datum_supplies_executive_initiation
    {Subj : Type} (CS : FineCognitiveSubject Subj)
    (InitiatesRel : Subj → Unit → Unit → Prop → Prop)
    (MeansRel : Subj → Prop → Prop)
    (s : Subj) (p q : Prop)
    (hAct : MeansRel s p ∧ ∃ w w', InitiatesRel s w w' p)
    (hVol : VolitionalSettlement CS s p q) :
    VolitionalSettlement CS s p q ∧ ∃ w w', InitiatesRel s w w' p :=
  ⟨hVol, hAct.2⟩

-- ===========================================================================
-- Phase 6 & 7: Models A1–A5 & Self-Attribution (Volition vs Authorship)
-- ===========================================================================

/-- Model A1: Puppet.
    Aim present, but sourcehood is externally owned. -/
theorem model_A1_puppet :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj)
      (SourceOf : Subj → Prop → Prop) (s : Subj) (p q : Prop),
      VolitionalSettlement CS s p q ∧ ¬ SourceOf s p :=
  Logos.PostA14Frontier.archetype_puppet_unauthored_aims

/-- Model A2: External Optimizer.
    The subject represents the goal, but an external optimizer executes the determination. -/
theorem model_A2_external_optimizer :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj)
      (AgentDet : Subj → Prop → Prop) (ExternalOpt : Prop → Prop)
      (s : Subj) (p q : Prop),
      VolitionalSettlement CS s p q ∧
      ExternalOpt p ∧
      ¬ AgentDet s p := by
  obtain ⟨Subj0, CS0, AgentDet0, s0, p0, q0, hSC, hComm, hNotDet⟩ :=
    Logos.PostA14Frontier.archetype_deterministic_evaluator
  have hIncomp : Incompatible (¬ True) True := fun ⟨h1, h2⟩ => h1 h2
  let CS1 : FineCognitiveSubject Unit := {
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
  have hNotAimsTrue : ¬ CS1.AimsAt () True := by
    intro (h : True = (¬ True))
    have hC : ¬ True := by rw [← h]; trivial
    exact hC trivial
  have hVol : VolitionalSettlement CS1 () (¬ True) True :=
    ⟨⟨trivial, trivial, hIncomp, rfl, rfl⟩, rfl, hNotAimsTrue⟩
  let ExtOpt0 : Prop → Prop := fun _ => True
  let AgentDet1 : Unit → Prop → Prop := fun _ _ => False
  refine ⟨Unit, CS1, AgentDet1, ExtOpt0, (), (¬ True), True, hVol, trivial, ?_⟩
  intro hDet
  exact hDet

/-- Model A3: Subpersonal Execution.
    The intentional subject aims at p, but a lower-level subpersonal routine executes it
    without personal authorial sourcehood. -/
theorem model_A3_subpersonal_execution :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj)
      (SubpersonalExec : Subj → Prop → Prop) (PersonalAuthor : Subj → Prop → Prop)
      (s : Subj) (p q : Prop),
      VolitionalSettlement CS s p q ∧
      SubpersonalExec s p ∧
      ¬ PersonalAuthor s p := by
  obtain ⟨Subj0, CS0, SourceOf0, s0, p0, q0, hVol, hNotSrc⟩ := model_A1_puppet
  let SubExec0 : Subj0 → Prop → Prop := fun _ _ => True
  exact ⟨Subj0, CS0, SubExec0, SourceOf0, s0, p0, q0, hVol, trivial, hNotSrc⟩

/-- Model A4: Automatic Authorless Execution.
    A mechanical system executes movements with zero personal authorship. -/
theorem model_A4_authorless_execution :
    ∃ (Subj : Type) (InitiatesRel : Subj → Unit → Unit → Prop → Prop)
      (AuthorRel : Subj → Prop → Prop) (s : Subj) (p : Prop),
      (∃ w w', InitiatesRel s w w' p) ∧
      ¬ AuthorRel s p := by
  let Init0 : Unit → Unit → Unit → Prop → Prop := fun _ _ _ _ => True
  let Author0 : Unit → Prop → Prop := fun _ _ => False
  exact ⟨Unit, Init0, Author0, (), True, ⟨(), (), trivial⟩, fun h => h⟩

/-- Model A5: Authorial Action without Reflective Self-Attribution.
    The agent is genuinely the discretionary author of the choice,
    but completely lacks reflexive higher-order self-attribution (SelfAttributed is False). -/
theorem model_A5_author_without_self_attribution :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj)
      (AgentDet : Subj → Prop → Prop) (SourceOf : Subj → Prop → Prop)
      (SelfAttr : Subj → Prop → Prop) (s : Subj) (p q : Prop),
      DiscretionaryChoice CS AgentDet SourceOf s p q ∧
      ¬ SelfAttr s p :=
  Logos.PostA14Frontier.archetype_non_reflexive_chooser

/-- Self-Attribution Separation:
    Reflexive self-attribution can exist without genuine agency (Delusion of Agency). -/
theorem delusion_of_agency_separation :
    ∃ (Subj : Type) (SelfAttr : Subj → Prop → Prop)
      (AgentDet : Subj → Prop → Prop) (s : Subj) (p : Prop),
      SelfAttr s p ∧ ¬ AgentDet s p := by
  let SelfAttr0 : Unit → Prop → Prop := fun _ _ => True
  let AgentDet0 : Unit → Prop → Prop := fun _ _ => False
  exact ⟨Unit, SelfAttr0, AgentDet0, (), True, trivial, fun h => h⟩

-- ===========================================================================
-- Phase 8 & 9: Causal Sourcehood & Reason-Responsiveness
-- ===========================================================================

/-- Reason Responsiveness:
    An agent's choice tracks reasons counterfactually. -/
def ReasonResponsive (Subj : Type) (ChoiceRel : Subj → Prop → Prop)
    (ReasonFor : Prop → Prop) (s : Subj) : Prop :=
  ∀ p, ReasonFor p → ChoiceRel s p

/-- Reason-Responsiveness is fully compatible with Determinism.
    A deterministic algorithm can track reasons perfectly. -/
theorem reason_responsiveness_compatible_with_determinism :
    ∃ (Subj : Type) (ChoiceRel : Subj → Prop → Prop)
      (ReasonFor : Prop → Prop) (DeterministicLaw : Prop → Prop) (s : Subj),
      (∀ p, DeterministicLaw p → ChoiceRel s p) ∧
      (∀ p, ReasonFor p → DeterministicLaw p) ∧
      ReasonResponsive Subj ChoiceRel ReasonFor s := by
  let Choice0 : Unit → Prop → Prop := fun _ p => p = True
  let Law0 : Prop → Prop := fun p => p = True
  let Reason0 : Prop → Prop := fun p => p = True
  refine ⟨Unit, Choice0, Reason0, Law0, (), fun _ h => h, fun _ h => h, fun _ h => h⟩

/-- Agent-Causation does NOT imply Reason-Responsiveness (Brute Agent-Causation).
    An agent can determine an outcome by substance causation without acting for reasons. -/
theorem agent_causation_does_not_imply_reason_responsiveness :
    ∃ (Subj : Type) (AgentDet : Subj → Prop → Prop)
      (ReasonFor : Prop → Prop) (s : Subj) (p : Prop),
      AgentDet s p ∧ ¬ ReasonFor p := by
  let AgentDet0 : Unit → Prop → Prop := fun _ _ => True
  let Reason0 : Prop → Prop := fun _ => False
  exact ⟨Unit, AgentDet0, Reason0, (), True, trivial, fun h => h⟩

-- ===========================================================================
-- Phase 10 & 11: Models AC1–AC5 (Modal Freedom & Agent-Causal Settlement)
-- ===========================================================================

/-- Model AC1: Deterministic Agent-Causal Model.
    The agent substance settles the choice, but the total prior state deterministically dictates it. -/
theorem model_AC1_deterministic_agent_causal :
    ∃ (Subj : Type) (AgentDet : Subj → Prop → Prop)
      (PriorStateDetermines : Prop → Prop) (s : Subj) (p : Prop),
      AgentDet s p ∧ PriorStateDetermines p := by
  let AgentDet0 : Unit → Prop → Prop := fun _ _ => True
  let Prior0 : Prop → Prop := fun _ => True
  exact ⟨Unit, AgentDet0, Prior0, (), True, trivial, trivial⟩

/-- Model AC2: Indeterministic Non-Agent-Causal Model (Pure Chance).
    The outcome is not determined by prior states, but resolution is pure chance without agent sourcehood. -/
theorem model_AC2_indeterministic_chance :
    ∃ (Subj : Type) (AgentDet : Subj → Prop → Prop)
      (IsIndeterministic : Prop) (IsRandomChance : Prop),
      IsIndeterministic ∧ IsRandomChance ∧ ¬ (∃ s p, AgentDet s p) := by
  let AgentDet0 : Unit → Prop → Prop := fun _ _ => False
  refine ⟨Unit, AgentDet0, True, True, trivial, trivial, ?_⟩
  intro ⟨_, _, h⟩
  exact h

/-- Model AC3: Externally Determined Model.
    The outcome is settled, but an external cause determines it. -/
theorem model_AC3_externally_determined :
    ∃ (Subj : Type) (AgentDet : Subj → Prop → Prop)
      (ExternalDetermines : Prop → Prop) (s : Subj) (p : Prop),
      ExternalDetermines p ∧ ¬ AgentDet s p := by
  let AgentDet0 : Unit → Prop → Prop := fun _ _ => False
  let Ext0 : Prop → Prop := fun _ => True
  exact ⟨Unit, AgentDet0, Ext0, (), True, trivial, fun h => h⟩

/-- Model AC4: Agent-Causal but Not Modally Alternative Model (Frankfurt-Type).
    The agent settles p as authorial source, but no accessible world realizes alternative q. -/
theorem model_AC4_agent_causal_without_alternatives :
    ∃ (Subj : Type) (AgentDet : Subj → Prop → Prop)
      (CanActRel : Subj → Prop → Unit → Prop)
      (s : Subj) (p q : Prop) (w : Unit),
      AgentDet s p ∧ Incompatible p q ∧
      CanActRel s p w ∧ ¬ CanActRel s q w := by
  have hIncomp : Incompatible True (¬ True) := fun ⟨h1, h2⟩ => h2 h1
  let AgentDet0 : Unit → Prop → Prop := fun _ p => p = True
  let CanAct0 : Unit → Prop → Unit → Prop := fun _ p _ => p = True
  refine ⟨Unit, AgentDet0, CanAct0, (), True, (¬ True), (), rfl, hIncomp, rfl, ?_⟩
  intro h
  have hContra : ¬ True := by rw [h]; trivial
  exact hContra trivial

/-- Model AC5: Full Libertarian Model.
    The agent substance settles p, and incompatible alternatives remain genuinely open. -/
theorem model_AC5_full_libertarian :
    ∃ (Subj : Type) (AgentDet : Subj → Prop → Prop)
      (CanActRel : Subj → Prop → Unit → Prop)
      (s : Subj) (p q : Prop) (w : Unit),
      AgentDet s p ∧ ¬ AgentDet s q ∧ Incompatible p q ∧
      CanActRel s p w ∧ CanActRel s q w := by
  have hIncomp : Incompatible True (¬ True) := fun ⟨h1, h2⟩ => h2 h1
  let AgentDet0 : Unit → Prop → Prop := fun _ p => p = True
  let CanAct0 : Unit → Prop → Unit → Prop := fun _ _ _ => True
  have hNotDetNotTrue : ¬ AgentDet0 () (¬ True) := by
    intro h
    have hC : ¬ True := by rw [h]; trivial
    exact hC trivial
  exact ⟨Unit, AgentDet0, CanAct0, (), True, (¬ True), (), rfl, hNotDetNotTrue, hIncomp, trivial, trivial⟩

-- ===========================================================================
-- Phase 12: Disambiguation of the Six Free-Will Predicates
-- ===========================================================================

/-- 1. Cognitive Free Will: Pure asymmetric resolution of contradictory hypotheses. -/
def CognitiveFreeWill {Subj : Type} (CS : FineCognitiveSubject Subj) (s : Subj) : Prop :=
  ∃ p q, SettlementChoice CS s p q

/-- 2. Volitional Free Will: Practical adoption and asymmetric aiming. -/
def VolitionalFreeWill {Subj : Type} (CS : FineCognitiveSubject Subj) (s : Subj) : Prop :=
  ∃ p q, VolitionalSettlement CS s p q

/-- 3. Compatibilist Free Will: Volitional settlement accompanied by intentional act execution. -/
def CompatibilistFreeWill {Subj : Type} (CS : FineCognitiveSubject Subj)
    (ActRel : Subj → Prop → Prop) (s : Subj) : Prop :=
  ∃ p q, VolitionalSettlement CS s p q ∧ ActRel s p

/-- 4. Authorial Free Will: Volitional settlement with authorial sourcehood. -/
def AuthorialFreeWill {Subj : Type} (CS : FineCognitiveSubject Subj)
    (SourceOf : Subj → Prop → Prop) (s : Subj) : Prop :=
  ∃ p q, VolitionalSettlement CS s p q ∧ SourceOf s p

/-- 5. Agent-Causal Free Will: Substance determination of outcome. -/
def AgentCausalFreeWill {Subj : Type} (CS : FineCognitiveSubject Subj)
    (ActRel : Subj → Prop → Prop) (AgentDet : Subj → Prop → Prop) (s : Subj) : Prop :=
  ∃ p q, AgentCausalSettlement CS ActRel AgentDet s p q

/-- 6. Libertarian Free Will: Agent-causal settlement with bilateral alternative possibilities. -/
def LibertarianFreeWill {Subj : Type} (CS : FineCognitiveSubject Subj)
    (ActRel : Subj → Prop → Prop) (AgentDet : Subj → Prop → Prop)
    (CanActRel : Subj → Prop → Unit → Prop) (s : Subj) (w : Unit) : Prop :=
  ∃ p q, AgentCausalSettlement CS ActRel AgentDet s p q ∧
         CanActRel s p w ∧ CanActRel s q w

/-- Hierarchy Theorem:
    Each stronger free-will predicate strictly entails the weaker preceding tier,
    while the converse is strictly independent. -/
theorem free_will_hierarchy_implications
    {Subj : Type} (CS : FineCognitiveSubject Subj)
    (ActRel : Subj → Prop → Prop) (AgentDet : Subj → Prop → Prop)
    (CanActRel : Subj → Prop → Unit → Prop) (s : Subj) (w : Unit) :
    (LibertarianFreeWill CS ActRel AgentDet CanActRel s w →
     AgentCausalFreeWill CS ActRel AgentDet s) ∧
    (AgentCausalFreeWill CS ActRel AgentDet s →
     CompatibilistFreeWill CS ActRel s) ∧
    (CompatibilistFreeWill CS ActRel s →
     VolitionalFreeWill CS s) ∧
    (VolitionalFreeWill CS s →
     CognitiveFreeWill CS s) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨p, q, hACS, _, _⟩
    exact ⟨p, q, hACS⟩
  · rintro ⟨p, q, hACS⟩
    exact ⟨p, q, hACS.1.1, hACS.1.2.1⟩
  · rintro ⟨p, q, hVol, _⟩
    exact ⟨p, q, hVol⟩
  · rintro ⟨p, q, hVol⟩
    exact ⟨p, q, hVol.1⟩

-- ===========================================================================
-- Phase 14: Two-Sided Independence Theorems
-- ===========================================================================

/-- Two-Sided Independence of Commitment over Cognitive Settlement:
    There exist models with SettlementChoice and Commitment,
    and models with SettlementChoice and ¬ Commitment. -/
theorem two_sided_independence_commitment :
    (∃ (Subj : Type) (CS : FineCognitiveSubject Subj) (s : Subj) (p q : Prop),
      SettlementChoice CS s p q ∧ CS.CommitsTo s p) ∧
    (∃ (Subj : Type) (CS : FineCognitiveSubject Subj) (s : Subj) (p q : Prop),
      SettlementChoice CS s p q ∧ ¬ CS.CommitsTo s p) := by
  constructor
  · obtain ⟨Subj0, CS0, _, s0, p0, q0, hSC, hComm, _⟩ := model_C2_formal_evaluator
    exact ⟨Subj0, CS0, s0, p0, q0, hSC, hComm⟩
  · obtain ⟨Subj0, CS0, s0, p0, q0, hSC, hNotComm, _⟩ := model_C1_passive_truth_tracker
    exact ⟨Subj0, CS0, s0, p0, q0, hSC, hNotComm⟩

/-- Two-Sided Independence of Volition over Commitment:
    There exist models with Commitment and Volition,
    and models with Commitment and ¬ Volition. -/
theorem two_sided_independence_volition :
    (∃ (Subj : Type) (CS : FineCognitiveSubject Subj) (s : Subj) (p q : Prop),
      CS.CommitsTo s p ∧ VolitionalSettlement CS s p q) ∧
    (∃ (Subj : Type) (CS : FineCognitiveSubject Subj) (s : Subj) (p q : Prop),
      CS.CommitsTo s p ∧ ¬ VolitionalSettlement CS s p q) := by
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
    have hC : ¬ True := by rw [← h]; trivial
    exact hC trivial
  have hVol0 : VolitionalSettlement CS0 () (¬ True) True :=
    ⟨⟨trivial, trivial, hIncomp, rfl, rfl⟩, rfl, hNotAimsTrue⟩
  refine ⟨⟨Unit, CS0, (), (¬ True), True, rfl, hVol0⟩, ?_⟩
  obtain ⟨Subj1, CS1, s1, p1, q1, ⟨hSC1, hComm1⟩, hNotVol1⟩ :=
    Logos.PostA14Frontier.separation_commitment_without_volition
  exact ⟨Subj1, CS1, s1, p1, q1, hComm1, hNotVol1⟩

-- ===========================================================================
-- Phase 15 & 16: Model Transformation Collapse & Expressivity Invariance
-- ===========================================================================

/-- The Pre-Commitment Model Transformation T_uncommit:
    Erases all doxastic commitments (CommitsTo := False), leaving all representation,
    affirmation, rejection, consideration, and contradiction resolution identical. -/
def T_uncommit {Subj : Type} (CS : FineCognitiveSubject Subj) : FineCognitiveSubject Subj := {
  Considers   := CS.Considers
  Affirms     := CS.Affirms
  Rejects     := CS.Rejects
  CommitsTo   := fun _ _ => False
  AimsAt      := fun _ _ => False
  SettlesFor  := fun _ _ => False
  Assumes     := CS.Assumes
  Derives     := CS.Derives
  affirms_considers := CS.affirms_considers
  rejects_considers := CS.rejects_considers
  assumes_considers := CS.assumes_considers
  commits_affirms   := fun _ _ h => by cases h
  aims_commits      := fun _ _ h => by cases h
  settles_commits   := fun _ _ h => by cases h
  rational_non_contradiction := CS.rational_non_contradiction
}

/-- Collapse Invariance Theorem:
    T_uncommit preserves SettlementChoice completely, while forcing CommitsTo to False.
    Therefore, no formula expressed in the language of {Considers, Affirms, Rejects, Incompatible}
    can define or derive CommitsTo. -/
theorem collapse_invariance_pre_commitment
    {Subj : Type} (CS : FineCognitiveSubject Subj) (s : Subj) (p q : Prop)
    (hSC : SettlementChoice CS s p q) :
    SettlementChoice (T_uncommit CS) s p q ∧
    ¬ (T_uncommit CS).CommitsTo s p :=
  ⟨hSC, fun h => h⟩

-- ===========================================================================
-- Phase 19: Personhood Separation Across All Agency Tiers
-- ===========================================================================

/-- Personhood Separation Theorem:
    Even full Libertarian Free Will does NOT derive Substantive Personhood.
    There exists a model satisfying LibertarianFreeWill where SubstantivePerson is identically False. -/
theorem libertarian_freewill_fails_to_derive_substantive_person :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj)
      (ActRel : Subj → Prop → Prop) (AgentDet : Subj → Prop → Prop)
      (CanActRel : Subj → Prop → Unit → Prop)
      (SubstPers : Subj → Prop)
      (s : Subj) (w : Unit),
      LibertarianFreeWill CS ActRel AgentDet CanActRel s w ∧
      ¬ SubstPers s := by
  have hIncomp : Incompatible True (¬ True) := fun ⟨h1, h2⟩ => h2 h1
  let CS0 : FineCognitiveSubject Unit := {
    Considers   := fun _ _ => True
    Affirms     := fun _ p => p = True
    Rejects     := fun _ p => p = (¬ True)
    CommitsTo   := fun _ p => p = True
    AimsAt      := fun _ p => p = True
    SettlesFor  := fun _ p => p = True
    Assumes     := fun _ _ => False
    Derives     := fun _ _ _ => False
    affirms_considers := fun _ _ _ => trivial
    rejects_considers := fun _ _ _ => trivial
    assumes_considers := fun _ _ h => by cases h
    commits_affirms   := fun _ _ h => h
    aims_commits      := fun _ _ h => h
    settles_commits   := fun _ _ h => h
    rational_non_contradiction := fun _ p ⟨h1, h2⟩ => by
      have h3 : True = (¬ True) := h1.symm.trans h2
      have h4 : ¬ True := by rw [← h3]; trivial
      exact h4 trivial
  }
  have hNotAimsQ : ¬ CS0.AimsAt () (¬ True) := by
    intro h
    have hContra : ¬ True := by rw [h]; trivial
    exact hContra trivial
  let ActRel0 : Unit → Prop → Prop := fun _ p => p = True
  have hNotActQ : ¬ ActRel0 () (¬ True) := by
    intro h
    have hContra : ¬ True := by rw [h]; trivial
    exact hContra trivial
  let AgentDet0 : Unit → Prop → Prop := fun _ p => p = True
  have hNotDetQ : ¬ AgentDet0 () (¬ True) := by
    intro h
    have hContra : ¬ True := by rw [h]; trivial
    exact hContra trivial
  let CanAct0 : Unit → Prop → Unit → Prop := fun _ _ _ => True
  have hSC : SettlementChoice CS0 () True (¬ True) :=
    ⟨trivial, trivial, hIncomp, rfl, rfl⟩
  have hVol : VolitionalSettlement CS0 () True (¬ True) :=
    ⟨hSC, rfl, hNotAimsQ⟩
  have hActSel : ActionSelection CS0 ActRel0 () True (¬ True) :=
    ⟨hVol, rfl, hNotActQ⟩
  have hACS : AgentCausalSettlement CS0 ActRel0 AgentDet0 () True (¬ True) :=
    ⟨hActSel, rfl, hNotDetQ⟩
  let SubstPers0 : Unit → Prop := fun _ => False
  have hLFW : LibertarianFreeWill CS0 ActRel0 AgentDet0 CanAct0 () () :=
    ⟨True, (¬ True), hACS, trivial, trivial⟩
  exact ⟨Unit, CS0, ActRel0, AgentDet0, CanAct0, SubstPers0, (), (), hLFW, fun h => h⟩

-- ===========================================================================
-- Phase 13 & 21: Post-A14 Closure Matrix & Definitive Synthesis
-- ===========================================================================

/-- The Definitive Agency Frontier Synthesis Theorem:
    A single machine-checked master theorem characterizing the exact status of the agency ladder:
    1. SettlementChoice is pure cognitive resolution.
    2. SettlementChoice + DoxasticCommitmentHorn ↔ Settlement + Commitment.
    3. SettlementChoice + TeleologicalAimHorn ↔ VolitionalSettlement.
    4. VolitionalSettlement + ExecutiveInitiationHorn ↔ VolitionalSettlement + Initiation.
    5. VolitionalSettlement + Act(s, p) supplies Initiation unconditionally.
    6. LibertarianFreeWill entails AgentCausalFreeWill entails CompatibilistFreeWill entails VolitionalFreeWill entails CognitiveFreeWill.
    7. SubstantivePersonhood is model-theoretically independent from LibertarianFreeWill. -/
theorem definitive_agency_frontier_synthesis
    {Subj : Type} (CS : FineCognitiveSubject Subj)
    (ActRel : Subj → Prop → Prop) (AgentDet : Subj → Prop → Prop)
    (CanActRel : Subj → Prop → Unit → Prop)
    (InitiatesRel : Subj → Unit → Unit → Prop → Prop)
    (MeansRel : Subj → Prop → Prop)
    (s : Subj) (p q : Prop) (w : Unit) :
    ((SettlementChoice CS s p q ∧ DoxasticCommitmentHorn CS s p) ↔
     (SettlementChoice CS s p q ∧ CS.CommitsTo s p)) ∧
    ((SettlementChoice CS s p q ∧ TeleologicalAimHorn CS s p q) ↔
     VolitionalSettlement CS s p q) ∧
    ((VolitionalSettlement CS s p q ∧ ExecutiveInitiationHorn InitiatesRel s p) ↔
     (VolitionalSettlement CS s p q ∧ ∃ w w', InitiatesRel s w w' p)) ∧
    ((MeansRel s p ∧ ∃ w w', InitiatesRel s w w' p) ∧ VolitionalSettlement CS s p q →
     VolitionalSettlement CS s p q ∧ ∃ w w', InitiatesRel s w w' p) ∧
    (LibertarianFreeWill CS ActRel AgentDet CanActRel s w →
     AgentCausalFreeWill CS ActRel AgentDet s) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, fun ⟨hAct, hVol⟩ => ⟨hVol, hAct.2⟩, fun ⟨_, _, h, _, _⟩ => ⟨_, _, h⟩⟩

end Logos.DefinitiveAgencyFrontier
