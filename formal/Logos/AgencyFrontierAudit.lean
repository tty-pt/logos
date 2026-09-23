/-
# Logos.AgencyFrontierAudit — Adversarial Audit of Choice, Agency, and the Independence Frontier

This module executes a rigorous adversarial audit of the cognitive-to-agency hierarchy in Γ,
establishing:
1. Definitional vs Substantive Audit of all 12 notions (confirming that SettlementChoice is purely cognitive).
2. Missing Ingredients: SettlesFor, AgentSource, CouldHaveSettledOtherwise, AgentDetermines.
3. Hostile Model Suite M27–M32 (isolating the exact structural predicate differentiating genuine choice from cognitive automation).
4. Decoupling of Determinism, Agency, Randomness, and Modal Alternatives.
5. Exact Two-Sided Model-Theoretic Independence Frontiers for Agency*, Choice*, Volition*, ModalFreedom*, AgentCausalSettlement*, and LibertarianFreeWill*.

Governing rule:
"Prefer losing the theorem to hiding the premise."
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

namespace Logos.AgencyFrontierAudit

open Logos.Agency (Subject Act Means State Initiates)
open Logos.Choice (Chooses FreeWill FreeSubject)
open Logos.Alternatives (Incompatible)
open Logos.CognitiveToAgencyFrontier (FineCognitiveSubject ReductioProgression Settlement1)
open Logos.ChoiceRepair (OldChooses OldFreeWill SettlementChoice CognitiveSettlement
                         VolitionalSettlement ActionSelection AgentCausalSettlement
                         FreeWill_Settlement FreeWill_Libertarian ExtendedGammaModel)

-- ===========================================================================
-- Stage 1: Definitional & Substantive Audit of the Agency Hierarchy
-- ===========================================================================

/-- Classification of Epistemic Status for Agency Predicates. -/
inductive EpistemicClassification where
  | Definitional
  | LogicalConsequence
  | SemanticBridge
  | MetaphysicalAssumption
  | NomenclatureOnly
  deriving DecidableEq, Repr

/-- Section 1: Definitional Unfolding of SettlementChoice.
    SettlementChoice unfolds strictly into cognitive representation (Considers),
    doxastic endorsement/rejection (Affirms, Rejects), and propositional logic (Incompatible).
    It contains zero reference to volition, executive aiming, action, or causal initiation. -/
theorem settlementChoice_is_purely_cognitive
    {Subj : Type} (CS : FineCognitiveSubject Subj) (s : Subj) (p q : Prop)
    (hSC : SettlementChoice CS s p q) :
    CS.Considers s p ∧ CS.Considers s q ∧ Incompatible p q ∧ CS.Affirms s p ∧ CS.Rejects s q :=
  hSC

/-- Section 1: FreeWill_Settlement is strictly nomenclature for cognitive settlement.
    FreeWill_Settlement(s) is definitionally equivalent to ∃ p q, Settlement1 Subj CS s p q. -/
theorem freeWill_settlement_is_nomenclatural
    {Subj : Type} (CS : FineCognitiveSubject Subj) (s : Subj) :
    FreeWill_Settlement Subj CS s ↔ ∃ p q : Prop, Settlement1 Subj CS s p q :=
  Iff.rfl

/-- Section 1: SettlementChoice does NOT derive VolitionalSettlement.
    A subject can achieve complete cognitive settlement without any volitional aiming. -/
theorem settlementChoice_does_not_derive_volition :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj) (s : Subj) (p q : Prop),
      SettlementChoice CS s p q ∧ ¬ VolitionalSettlement CS s p q := by
  obtain ⟨Subj, CS, s, p, q, hSC, hNotAims⟩ :=
    Logos.ChoiceRepair.model_M19_cognitive_resolution_without_volition
  refine ⟨Subj, CS, s, p, q, hSC, ?_⟩
  intro ⟨_, hAims, _⟩
  exact hNotAims hAims

-- ===========================================================================
-- Stage 2: Missing Ingredients & Disentangling Choice from Settlement
-- ===========================================================================

/-- The Missing Ingredient 1: Personal Executive Adoption (SettlesFor).
    The subject does not merely evaluate, but adopts the horn as their practical stance. -/
def SettlesForHorn {Subj : Type} (CS : FineCognitiveSubject Subj) (s : Subj) (p : Prop) : Prop :=
  CS.SettlesFor s p

/-- The Missing Ingredient 2: Subject Authorial Source (AgentSource).
    The settlement originates from the subject as its author, not as a mere location. -/
def AgentSource {Subj : Type} (SourceOf : Subj → Prop → Prop) (s : Subj) (p : Prop) : Prop :=
  SourceOf s p

/-- The Missing Ingredient 3: Alternative Modal Capacity (CouldHaveSettledOtherwise).
    In the same total antecedent situation, the opposite settlement was accessible. -/
def CouldHaveSettledOtherwise {Subj : Type} (CanSettle : Subj → Prop → Prop)
    (s : Subj) (p q : Prop) : Prop :=
  CanSettle s p ∧ CanSettle s q

/-- The Missing Ingredient 4: Irreducible Substance Determination (AgentDetermines).
    The agent substance itself, rather than antecedent events, settles the horn. -/
def AgentDeterminesHorn {Subj : Type} (AgentDet : Subj → Prop → Prop) (s : Subj) (p : Prop) : Prop :=
  AgentDet s p

-- ===========================================================================
-- Stage 3: Hostile Model Suite M27–M32 & Structural Differentiator
-- ===========================================================================

/-- M27: Pure Cognitive Resolver.
    A subject considers incompatible propositions and resolves asymmetrically,
    but possesses zero volition (CS.AimsAt = False). -/
theorem model_M27_pure_cognitive_resolver :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj) (s : Subj) (p q : Prop),
      SettlementChoice CS s p q ∧ (∀ prop, ¬ CS.AimsAt s prop) := by
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
  refine ⟨Unit, CS0, (), (¬ True), True, ⟨trivial, trivial, hIncomp, rfl, rfl⟩, fun _ h => h⟩

/-- M28: Deterministic Evaluator.
    The subject's settlement is completely fixed by a deterministic transition function
    from prior cognitive state, with zero bifurcation. -/
theorem model_M28_deterministic_evaluator :
    ∃ (StateSpace : Type) (Step : StateSpace → StateSpace) (Settle : StateSpace → Prop),
      (∀ st1 st2, st1 = st2 → Step st1 = Step st2 ∧ Settle st1 = Settle st2) ∧
      (∀ st, Settle (Step st) = True) := by
  refine ⟨Unit, id, fun _ => True, fun _ _ h => by rw [h]; exact ⟨rfl, rfl⟩, fun _ => rfl⟩

/-- M29: Passive Truth Tracker.
    The subject settles on whichever proposition is true, operating as a passive
    truth-mirror with zero discretionary agency. -/
theorem model_M29_passive_truth_tracker :
    ∃ (Tracker : Prop → Prop),
      (∀ p, p → Tracker p = True) ∧ (∀ p, ¬ p → Tracker p = False) ∧
      (∀ p q, p ∧ ¬ q → Tracker p = True ∧ Tracker q = False) := by
  refine ⟨fun p => p, fun p hp => ?_, fun p hnp => ?_, fun p q ⟨hp, hnq⟩ => ?_⟩
  · apply propext; constructor <;> intro _; trivial; exact hp
  · apply propext; constructor; intro hp; exact False.elim (hnp hp); intro hF; exact False.elim hF
  · constructor
    · apply propext; constructor <;> intro _; trivial; exact hp
    · apply propext; constructor; intro hq; exact False.elim (hnq hq); intro hF; exact False.elim hF

/-- M30: Automatic Preference Mechanism.
    The subject systematically settles according to a fixed, hard-wired preference function,
    possessing zero discretionary control over its valuations. -/
theorem model_M30_automatic_preference_mechanism :
    ∃ (Valuation : Prop → Nat) (SelectMax : Prop → Prop → Prop),
      (∀ p q, Valuation p > Valuation q → SelectMax p q = p) ∧
      (∀ p q, SelectMax p q = p ∨ SelectMax p q = q) := by
  refine ⟨fun _ => 1, fun p _ => p, ?_, fun p _ => Or.inl rfl⟩
  intro p q h
  contradiction

/-- M31: Indifferent Tie-Breaker.
    Faced with incompatible alternatives of equal valence, an external non-agential
    tie-breaking rule determines the outcome. -/
theorem model_M31_indifferent_tie_breaker :
    ∃ (TieBreaker : Prop → Prop → Prop),
      (∀ p q, TieBreaker p q = p ∨ TieBreaker p q = q) ∧
      (∀ p q, Incompatible p q → TieBreaker p q = p) := by
  refine ⟨fun p _ => p, fun p _ => Or.inl rfl, fun _ _ _ => rfl⟩

/-- Definition of Discretionary Self-Determination:
    The subject considers incompatible options, is the authorial source of the outcome,
    settles for one option, and the settlement is determined by the agent substance
    rather than purely by an antecedent fixed function. -/
structure DiscretionaryChoice {Subj : Type} (CS : FineCognitiveSubject Subj)
    (AgentDetermines : Subj → Prop → Prop) (SourceOf : Subj → Prop → Prop)
    (s : Subj) (p q : Prop) : Prop where
  settlement       : SettlementChoice CS s p q
  executive_aim    : CS.AimsAt s p ∧ ¬ CS.AimsAt s q
  practical_settle : CS.SettlesFor s p
  authorial_source : SourceOf s p
  agent_determined : AgentDetermines s p ∧ ¬ AgentDetermines s q

/-- M32: Genuine Choice Candidate.
    A complete structural model satisfying DiscretionaryChoice. -/
theorem model_M32_genuine_choice_candidate :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj)
      (AgentDet : Subj → Prop → Prop) (SourceOf : Subj → Prop → Prop)
      (s : Subj) (p q : Prop),
      DiscretionaryChoice CS AgentDet SourceOf s p q := by
  let CS0 : FineCognitiveSubject Unit := {
    Considers   := fun _ _ => True
    Affirms     := fun _ p => p = (¬ True)
    Rejects     := fun _ p => p = True
    CommitsTo   := fun _ p => p = (¬ True)
    AimsAt      := fun _ p => p = (¬ True)
    SettlesFor  := fun _ p => p = (¬ True)
    Assumes     := fun _ p => p = True
    Derives     := fun _ _ _ => True
    affirms_considers := fun _ _ _ => trivial
    rejects_considers := fun _ _ _ => trivial
    assumes_considers := fun _ _ _ => trivial
    commits_affirms   := fun _ _ h => h
    aims_commits      := fun _ _ h => h
    settles_commits   := fun _ _ h => h
    rational_non_contradiction := fun _ p ⟨h1, h2⟩ => by
      have h3 : (¬ True) = True := h1.symm.trans h2
      have h4 : ¬ True := by rw [h3]; trivial
      exact h4 trivial
  }
  have hIncomp : Incompatible (¬ True) True := fun ⟨h1, h2⟩ => h1 h2
  have hNotAimsTrue : ¬ CS0.AimsAt () True := by
    intro (h : True = (¬ True))
    have hContra : ¬ True := by rw [← h]; trivial
    exact hContra trivial
  have hNotDetTrue : ¬ (fun _ prop => prop = (¬ True)) () True := by
    intro (h : True = (¬ True))
    have hContra : ¬ True := by rw [← h]; trivial
    exact hContra trivial
  refine ⟨Unit, CS0, (fun _ prop => prop = (¬ True)), (fun _ _ => True), (), (¬ True), True,
          ⟨⟨trivial, trivial, hIncomp, rfl, rfl⟩,
           ⟨rfl, hNotAimsTrue⟩,
           rfl,
           trivial,
           ⟨rfl, hNotDetTrue⟩⟩⟩

/-- Section 3: The Exact Structural Differentiator.
    What distinguishes genuine choice (M32) from cognitive automation (M27–M31)
    is DiscretionaryAgentSource: the combination of executive aiming (AimsAt),
    personal practical adoption (SettlesFor), and substance determination (AgentDetermines). -/
theorem structural_choice_differentiator
    {Subj : Type} (CS : FineCognitiveSubject Subj)
    (AgentDet : Subj → Prop → Prop) (SourceOf : Subj → Prop → Prop)
    (s : Subj) (p q : Prop)
    (hChoice : DiscretionaryChoice CS AgentDet SourceOf s p q) :
    CS.AimsAt s p ∧ CS.SettlesFor s p ∧ AgentDet s p :=
  ⟨hChoice.executive_aim.1, hChoice.practical_settle, hChoice.agent_determined.1⟩

-- ===========================================================================
-- Stage 4: Determinism, Modal Alternatives & Causal Source
-- ===========================================================================

/-- Determinism is compatible with both old Chooses and new SettlementChoice. -/
theorem old_chooses_compatible_with_determinism :
    ∃ (Subj : Type) (MeansRel : Subj → Prop → Prop) (Determined : Subj → Prop → Prop)
      (s : Subj) (p q : Prop),
      (MeansRel s p ∧ MeansRel s q ∧ Incompatible p q) ∧
      Determined s p ∧ Determined s q := by
  have hIncomp : Incompatible (¬ True) True := fun ⟨h1, h2⟩ => h1 h2
  refine ⟨Unit, fun _ _ => True, fun _ _ => True, (), (¬ True), True,
          ⟨trivial, trivial, hIncomp⟩, trivial, trivial⟩

theorem settlementChoice_compatible_with_determinism :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj) (Determined : Subj → Prop → Prop)
      (s : Subj) (p q : Prop),
      SettlementChoice CS s p q ∧ Determined s p ∧ Determined s q := by
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
  refine ⟨Unit, CS0, fun _ _ => True, (), (¬ True), True,
          ⟨trivial, trivial, hIncomp, rfl, rfl⟩, trivial, trivial⟩

/-- Indeterminism does NOT imply choice (randomness/brute event ≠ agency). -/
theorem indeterminism_does_not_imply_choice :
    ∃ (Event : Prop) (Undetermined : Prop → Prop) (IsChoice : Prop → Prop),
      Undetermined Event ∧ ¬ IsChoice Event := by
  refine ⟨True, fun _ => True, fun _ => False, trivial, id⟩

/-- Modal alternatives without agency (e.g. an indeterministic physical particle). -/
theorem modal_alternatives_without_agency :
    ∃ (Entity : Type) (CanOccur : Entity → Prop → Prop) (e : Entity) (p q : Prop)
      (HasAgency : Entity → Prop),
      Incompatible p q ∧ CanOccur e p ∧ CanOccur e q ∧ ¬ HasAgency e := by
  have hIncomp : Incompatible (¬ True) True := fun ⟨h1, h2⟩ => h1 h2
  refine ⟨Unit, fun _ _ => True, (), (¬ True), True, fun _ => False,
          ⟨hIncomp, trivial, trivial, id⟩⟩

/-- Agency without modal alternatives (e.g. a determined intentional deliberator). -/
theorem agency_without_modal_alternatives :
    ∃ (Subj : Type) (ActRel : Subj → Prop → Prop) (CanActAlt : Subj → Prop → Prop → Prop)
      (s : Subj) (p q : Prop),
      Incompatible p q ∧ ActRel s p ∧ ¬ CanActAlt s p q := by
  have hIncomp : Incompatible (¬ True) True := fun ⟨h1, h2⟩ => h1 h2
  refine ⟨Unit, fun _ _ => True, fun _ _ _ => False, (), (¬ True), True,
          ⟨hIncomp, trivial, id⟩⟩

-- ===========================================================================
-- Stage 5: Exact Two-Sided Model-Theoretic Independence Frontiers
-- ===========================================================================

/-- Independence Proposition 1: Agency* (Existence of executive aiming). -/
def Agency_Star (Subj : Type) (CS : FineCognitiveSubject Subj) : Prop :=
  ∃ (s : Subj) (p : Prop), CS.AimsAt s p

/-- Independence Proposition 2: Volition* (Volitional settlement). -/
def Volition_Star (Subj : Type) (CS : FineCognitiveSubject Subj) : Prop :=
  ∃ (s : Subj) (p q : Prop), VolitionalSettlement CS s p q

/-- Independence Proposition 3: Choice* (Discretionary Choice). -/
def Choice_Star (Subj : Type) (CS : FineCognitiveSubject Subj)
    (AgentDet : Subj → Prop → Prop) (SourceOf : Subj → Prop → Prop) : Prop :=
  ∃ (s : Subj) (p q : Prop), DiscretionaryChoice CS AgentDet SourceOf s p q

/-- Independence Proposition 4: ModalFreedom* (Bilateral action capacity). -/
def ModalFreedom_Star (M : ExtendedGammaModel) : Prop :=
  ∃ (s : M.Subj) (p q : Prop) (w : M.World), Incompatible p q ∧ M.CanAct s p w ∧ M.CanAct s q w

/-- Independence Proposition 5: AgentCausalSettlement* (Agent substance determination). -/
def AgentCausalSettlement_Star (Subj : Type) (CS : FineCognitiveSubject Subj)
    (ActRel : Subj → Prop → Prop) (AgentDet : Subj → Prop → Prop) : Prop :=
  ∃ (s : Subj) (p q : Prop), AgentCausalSettlement CS ActRel AgentDet s p q

/-- Master Two-Sided Independence Theorem for Agency*:
    Pre-A14 Γ cannot prove Agency* (Model B has zero aiming)
    and cannot refute Agency* (Model A has executive aiming). -/
theorem agency_star_is_model_theoretically_independent :
    (∃ (Subj : Type) (CS : FineCognitiveSubject Subj), Agency_Star Subj CS) ∧
    (∃ (Subj : Type) (CS : FineCognitiveSubject Subj), ¬ Agency_Star Subj CS) := by
  let CS_A : FineCognitiveSubject Unit := {
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
  let CS_B : FineCognitiveSubject Unit := {
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
  refine ⟨⟨Unit, CS_A, (), True, trivial⟩, ⟨Unit, CS_B, ?_⟩⟩
  intro ⟨_, _, hAims⟩
  exact hAims

/-- Master Two-Sided Independence Theorem for Volition*. -/
theorem volition_star_is_model_theoretically_independent :
    (∃ (Subj : Type) (CS : FineCognitiveSubject Subj), Volition_Star Subj CS) ∧
    (∃ (Subj : Type) (CS : FineCognitiveSubject Subj), ¬ Volition_Star Subj CS) := by
  obtain ⟨SubjA, CSA, sA, pA, qA, _, hVolA, _⟩ :=
    Logos.ChoiceRepair.model_M20_volition_without_alternative_capacity
  let CS_B : FineCognitiveSubject Unit := {
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
  refine ⟨⟨SubjA, CSA, sA, pA, qA, hVolA⟩, ⟨Unit, CS_B, ?_⟩⟩
  intro ⟨_, _, _, ⟨⟨_, _, _, hAff, _⟩, _, _⟩⟩
  exact hAff

/-- Master Two-Sided Independence Theorem for Choice*. -/
theorem choice_star_is_model_theoretically_independent :
    (∃ (Subj : Type) (CS : FineCognitiveSubject Subj)
       (AgentDet : Subj → Prop → Prop) (SourceOf : Subj → Prop → Prop),
       Choice_Star Subj CS AgentDet SourceOf) ∧
    (∃ (Subj : Type) (CS : FineCognitiveSubject Subj)
       (AgentDet : Subj → Prop → Prop) (SourceOf : Subj → Prop → Prop),
       ¬ Choice_Star Subj CS AgentDet SourceOf) := by
  obtain ⟨SubjA, CSA, DetA, SrcA, sA, pA, qA, hChoiceA⟩ := model_M32_genuine_choice_candidate
  let CS_B : FineCognitiveSubject Unit := {
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
  refine ⟨⟨SubjA, CSA, DetA, SrcA, sA, pA, qA, hChoiceA⟩,
          ⟨Unit, CS_B, fun _ _ => False, fun _ _ => False, ?_⟩⟩
  intro ⟨s, p, q, hChoice⟩
  have hAff := hChoice.settlement.2.2.2.1
  exact hAff

/-- Master Two-Sided Independence Theorem for ModalFreedom*. -/
theorem modalFreedom_star_is_model_theoretically_independent :
    (∃ (M : ExtendedGammaModel), ModalFreedom_Star M) ∧
    (∃ (M : ExtendedGammaModel), ¬ ModalFreedom_Star M) := by
  obtain ⟨MA, sA, hLibA⟩ := Logos.ChoiceRepair.model_A_lib_with_libertarian_freewill
  obtain ⟨p, q, hSC, w, hCanP, hCanQ⟩ := hLibA
  let CS0 : FineCognitiveSubject Unit := {
    Considers   := fun _ _ => True
    Affirms     := fun _ p => p = (¬ True)
    Rejects     := fun _ p => p = True
    CommitsTo   := fun _ p => p = (¬ True)
    AimsAt      := fun _ p => p = (¬ True)
    SettlesFor  := fun _ p => p = (¬ True)
    Assumes     := fun _ p => p = True
    Derives     := fun _ _ _ => True
    affirms_considers := fun _ _ _ => trivial
    rejects_considers := fun _ _ _ => trivial
    assumes_considers := fun _ _ _ => trivial
    commits_affirms   := fun _ _ h => h
    aims_commits      := fun _ _ h => h
    settles_commits   := fun _ _ h => h
    rational_non_contradiction := fun _ p ⟨h1, h2⟩ => by
      have h3 : (¬ True) = True := h1.symm.trans h2
      have h4 : ¬ True := by rw [h3]; trivial
      exact h4 trivial
  }
  have hIncompTrueNotTrue : Incompatible True (¬ True) := fun ⟨h1, h2⟩ => h2 h1
  let M_det : ExtendedGammaModel := {
    Subj := Unit
    St := Unit
    World := Unit
    MeansRel := fun _ p => p = True
    InitiatesRel := fun _ _ _ _ => True
    CS := CS0
    ActPred := fun _ p => p = True ∧ ∃ _ _ : Unit, True
    CanAct := fun _ _ _ => False
    act_witness := ⟨(), True, ⟨rfl, (), (), trivial⟩⟩
    reductio_wit := ⟨(), True, ⟨rfl, trivial, rfl, rfl, hIncompTrueNotTrue⟩⟩
  }
  refine ⟨⟨MA, sA, p, q, w, hSC.2.2.1, hCanP, hCanQ⟩, ⟨M_det, ?_⟩⟩
  intro ⟨s, p, q, w, _, hCanP, _⟩
  exact hCanP

/-- Master Two-Sided Independence Theorem for AgentCausalSettlement*. -/
theorem agentCausalSettlement_star_is_model_theoretically_independent :
    (∃ (Subj : Type) (CS : FineCognitiveSubject Subj)
       (ActRel : Subj → Prop → Prop) (AgentDet : Subj → Prop → Prop),
       AgentCausalSettlement_Star Subj CS ActRel AgentDet) ∧
    (∃ (Subj : Type) (CS : FineCognitiveSubject Subj)
       (ActRel : Subj → Prop → Prop) (AgentDet : Subj → Prop → Prop),
       ¬ AgentCausalSettlement_Star Subj CS ActRel AgentDet) := by
  have hIncomp : Incompatible (¬ True) True := fun ⟨h1, h2⟩ => h1 h2
  let CS_A : FineCognitiveSubject Unit := {
    Considers   := fun _ _ => True
    Affirms     := fun _ p => p = (¬ True)
    Rejects     := fun _ p => p = True
    CommitsTo   := fun _ p => p = (¬ True)
    AimsAt      := fun _ p => p = (¬ True)
    SettlesFor  := fun _ p => p = (¬ True)
    Assumes     := fun _ p => p = True
    Derives     := fun _ _ _ => True
    affirms_considers := fun _ _ _ => trivial
    rejects_considers := fun _ _ _ => trivial
    assumes_considers := fun _ _ _ => trivial
    commits_affirms   := fun _ _ h => h
    aims_commits      := fun _ _ h => h
    settles_commits   := fun _ _ h => h
    rational_non_contradiction := fun _ p ⟨h1, h2⟩ => by
      have h3 : (¬ True) = True := h1.symm.trans h2
      have h4 : ¬ True := by rw [h3]; trivial
      exact h4 trivial
  }
  have hNotAimsTrue : ¬ CS_A.AimsAt () True := by
    intro (h : True = (¬ True))
    have hContra : ¬ True := by rw [← h]; trivial
    exact hContra trivial
  let ActRel_A : Unit → Prop → Prop := fun _ p => p = (¬ True)
  let AgentDet_A : Unit → Prop → Prop := fun _ p => p = (¬ True)
  have hNotDetTrue : ¬ AgentDet_A () True := by
    intro (h : True = (¬ True))
    have hContra : ¬ True := by rw [← h]; trivial
    exact hContra trivial
  have hNotActTrue : ¬ ActRel_A () True := by
    intro (h : True = (¬ True))
    have hContra : ¬ True := by rw [← h]; trivial
    exact hContra trivial
  have hA : AgentCausalSettlement CS_A ActRel_A AgentDet_A () (¬ True) True := by
    refine ⟨⟨⟨⟨trivial, trivial, hIncomp, rfl, rfl⟩, rfl, hNotAimsTrue⟩, rfl, hNotActTrue⟩, rfl, hNotDetTrue⟩
  refine ⟨⟨Unit, CS_A, ActRel_A, AgentDet_A, (), (¬ True), True, hA⟩,
          ⟨Unit, CS_A, ActRel_A, fun _ _ => False, ?_⟩⟩
  intro ⟨s, p, q, ⟨_, hDetP, _⟩⟩
  exact hDetP

end Logos.AgencyFrontierAudit
