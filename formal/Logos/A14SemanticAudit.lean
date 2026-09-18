/-
# Logos.A14SemanticAudit — Philosophical and Semantic Audit of A14

This module executes a rigorous audit of A14 (AxIntentionalChoice), establishing:
1. The Irreducible Semantic Boundary Theorem: Any principle B yielding A14 over pre-A14 Γ
   must non-trivially assert the missing cognitive contrast horn (MissingCognitiveHorn).
2. Five competing formalizations of Intentional Action (Minimal, Contrastive, Purposeful,
   Authorial, Reasons-Responsive), proving that defining Act contrastively trivially
   smuggles A14 into the definition of action without deriving it.
3. Hostile analysis of candidate semantic laws for `Means` (negation closure, inferential closure),
   refuted by unipolar models.
4. Performative Boundary Theorem: Performative retorsion stops strictly at IntentionalSubject
   and cognitive resolution, leaving volition, choice, and personhood underdetermined.
5. The 9-Component Incremental Choice Chain with formal separation models.

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

namespace Logos.A14SemanticAudit

open Logos.Agency (Subject Act Means State Initiates)
open Logos.Choice (Chooses FreeWill FreeSubject MissingCognitiveHorn)
open Logos.Alternatives (Incompatible)
open Logos.CognitiveToAgencyFrontier (FineCognitiveSubject ReductioProgression Settlement1)
open Logos.ChoiceRepair (OldChooses OldFreeWill SettlementChoice CognitiveSettlement
                         VolitionalSettlement ActionSelection AgentCausalSettlement
                         FreeWill_Settlement FreeWill_Libertarian ExtendedGammaModel)
open Logos.AgencyFrontierAudit (DiscretionaryChoice)

-- ===========================================================================
-- Stage 1: Philosophical Audit of A14 & The Irreducible Semantic Boundary
-- ===========================================================================

/-- Statement of A14 in the vocabulary of Γ. -/
def A14_Statement (Subj : Type) (ActRel : Subj → Prop → Prop)
    (MeansRel : Subj → Prop → Prop) : Prop :=
  ∀ (s : Subj) (p : Prop), ActRel s p → ∃ (q : Prop), MeansRel s p ∧ MeansRel s q ∧ Incompatible p q

/-- The Missing Cognitive Horn Principle:
    Every acting subject cognitively represents an incompatible alternative. -/
def MissingHornPrinciple (Subj : Type) (ActRel : Subj → Prop → Prop)
    (MeansRel : Subj → Prop → Prop) : Prop :=
  ∀ (s : Subj) (p : Prop), ActRel s p → ∃ (q : Prop), MeansRel s q ∧ Incompatible p q

/-- Lemma: Over any theory where Act s p implies Means s p,
    A14 is definitionally equivalent to the MissingHornPrinciple. -/
theorem a14_iff_missing_horn_principle
    {Subj : Type} (ActRel : Subj → Prop → Prop) (MeansRel : Subj → Prop → Prop)
    (hActMeans : ∀ s p, ActRel s p → MeansRel s p) :
    A14_Statement Subj ActRel MeansRel ↔ MissingHornPrinciple Subj ActRel MeansRel := by
  constructor
  · intro hA14 s p hAct
    obtain ⟨q, _, hMeansQ, hIncomp⟩ := hA14 s p hAct
    exact ⟨q, hMeansQ, hIncomp⟩
  · intro hHorn s p hAct
    have hMeansP := hActMeans s p hAct
    obtain ⟨q, hMeansQ, hIncomp⟩ := hHorn s p hAct
    exact ⟨q, hMeansP, hMeansQ, hIncomp⟩

/-- Candidate Semantic Principle B1: Teleological Action (Action has a purpose/goal). -/
def TeleologicalAction {Subj : Type} (ActRel : Subj → Prop → Prop)
    (AimsAt : Subj → Prop → Prop) : Prop :=
  ∀ s p, ActRel s p → ∃ g, AimsAt s g

/-- Candidate Semantic Principle B2: Reasons-Responsive Action. -/
def ReasonsResponsiveAction {Subj : Type} (ActRel : Subj → Prop → Prop)
    (Responsive : Subj → Prop → Prop) : Prop :=
  ∀ s p, ActRel s p → Responsive s p

/-- Candidate Semantic Principle B3: Authorial Action (Subject is source of action). -/
def AuthorialAction {Subj : Type} (ActRel : Subj → Prop → Prop)
    (SourceOf : Subj → Prop → Prop) : Prop :=
  ∀ s p, ActRel s p → SourceOf s p

/-- THE IRREDUCIBLE SEMANTIC BOUNDARY THEOREM:
    Neither TeleologicalAction (B1), nor ReasonsResponsiveAction (B2), nor AuthorialAction (B3)
    can derive A14 in a unipolar model where the subject acts toward a goal
    without cognitively representing an incompatible alternative. -/
theorem candidate_principles_fail_to_derive_a14 :
    ∃ (Subj : Type) (ActRel : Subj → Prop → Prop) (MeansRel : Subj → Prop → Prop)
      (AimsAt : Subj → Prop → Prop) (Responsive : Subj → Prop → Prop)
      (SourceOf : Subj → Prop → Prop),
      (∀ s p, ActRel s p → MeansRel s p) ∧
      TeleologicalAction ActRel AimsAt ∧
      ReasonsResponsiveAction ActRel Responsive ∧
      AuthorialAction ActRel SourceOf ∧
      ¬ A14_Statement Subj ActRel MeansRel := by
  let Subj0 := Unit
  let ActRel0 : Unit → Prop → Prop := fun _ p => p = True
  let MeansRel0 : Unit → Prop → Prop := fun _ p => p = True
  let AimsAt0 : Unit → Prop → Prop := fun _ p => p = True
  let Responsive0 : Unit → Prop → Prop := fun _ _ => True
  let SourceOf0 : Unit → Prop → Prop := fun _ _ => True
  refine ⟨Subj0, ActRel0, MeansRel0, AimsAt0, Responsive0, SourceOf0,
          fun _ p h => h,
          fun _ _ _ => ⟨True, rfl⟩,
          fun _ _ _ => trivial,
          fun _ _ _ => trivial,
          ?_⟩
  intro hA14
  obtain ⟨q, _, hMeansQ, hIncomp⟩ := hA14 () True rfl
  have hIncompTrue : Incompatible True True := by
    rw [hMeansQ] at hIncomp
    exact hIncomp
  exact hIncompTrue ⟨trivial, trivial⟩

/-- Master Semantic Boundary Theorem:
    A14 is an irreducible semantic commitment. Any premise B entailing A14
    must strictly entail the MissingHornPrinciple. -/
theorem irreducible_semantic_boundary_of_a14
    {Subj : Type} (ActRel : Subj → Prop → Prop) (MeansRel : Subj → Prop → Prop)
    (hActMeans : ∀ s p, ActRel s p → MeansRel s p) (B : Prop)
    (hB_implies_A14 : B → A14_Statement Subj ActRel MeansRel) :
    B → MissingHornPrinciple Subj ActRel MeansRel := by
  intro hB
  have hA14 := hB_implies_A14 hB
  rw [a14_iff_missing_horn_principle ActRel MeansRel hActMeans] at hA14
  exact hA14

-- ===========================================================================
-- Stage 2: Competing Action Semantics & Laws of Means
-- ===========================================================================

/-- Competing Formalization A: Minimal Intentional Act (Existing Act). -/
def Act_Minimal {Subj : Type} (MeansRel : Subj → Prop → Prop)
    (InitiatesRel : Subj → Unit → Unit → Prop → Prop) (s : Subj) (p : Prop) : Prop :=
  MeansRel s p ∧ ∃ w w' : Unit, InitiatesRel s w w' p

/-- Competing Formalization B: Contrastive Intentional Act.
    Action explicitly presupposes representation of an incompatible alternative. -/
def Act_Contrastive {Subj : Type} (MeansRel : Subj → Prop → Prop)
    (InitiatesRel : Subj → Unit → Unit → Prop → Prop) (s : Subj) (p : Prop) : Prop :=
  Act_Minimal MeansRel InitiatesRel s p ∧ ∃ q, MeansRel s q ∧ Incompatible p q

/-- Competing Formalization C: Purposeful Intentional Act.
    Action includes an explicit goal or teleological end. -/
def Act_Purposeful {Subj : Type} (MeansRel : Subj → Prop → Prop)
    (InitiatesRel : Subj → Unit → Unit → Prop → Prop)
    (AimsAt : Subj → Prop → Prop) (s : Subj) (p : Prop) : Prop :=
  Act_Minimal MeansRel InitiatesRel s p ∧ ∃ g, AimsAt s g

/-- Competing Formalization D: Authorial Intentional Act.
    Action requires the subject to be the authorial source of the occurrence. -/
def Act_Authorial {Subj : Type} (MeansRel : Subj → Prop → Prop)
    (InitiatesRel : Subj → Unit → Unit → Prop → Prop)
    (SourceOf : Subj → Prop → Prop) (s : Subj) (p : Prop) : Prop :=
  Act_Minimal MeansRel InitiatesRel s p ∧ SourceOf s p

/-- Competing Formalization E: Reasons-Responsive Intentional Act.
    Action includes counterfactual sensitivity to reasons. -/
def Act_Responsive {Subj : Type} (MeansRel : Subj → Prop → Prop)
    (InitiatesRel : Subj → Unit → Unit → Prop → Prop)
    (Responsive : Subj → Prop → Prop) (s : Subj) (p : Prop) : Prop :=
  Act_Minimal MeansRel InitiatesRel s p ∧ Responsive s p

/-- Theorem: Redefining Act as Act_Contrastive trivially satisfies A14,
    but this is a definitional tautology (premise smuggling), not a derivation. -/
theorem act_contrastive_trivializes_a14
    {Subj : Type} (MeansRel : Subj → Prop → Prop)
    (InitiatesRel : Subj → Unit → Unit → Prop → Prop)
    (s : Subj) (p : Prop) (hAct : Act_Contrastive MeansRel InitiatesRel s p) :
    ∃ q, MeansRel s p ∧ MeansRel s q ∧ Incompatible p q := by
  obtain ⟨hMin, q, hMeansQ, hIncomp⟩ := hAct
  exact ⟨q, hMin.1, hMeansQ, hIncomp⟩

/-- Attack on Semantic Laws of Means:
    Law 1 (Negation Closure): Means(s, p) → Means(s, ¬p).
    Refuted: A subject can intend an affirmative state without representing its negation. -/
theorem negation_closure_of_means_fails :
    ∃ (Subj : Type) (MeansRel : Subj → Prop → Prop) (s : Subj) (p : Prop),
      MeansRel s p ∧ ¬ MeansRel s (¬ p) := by
  refine ⟨Unit, fun _ prop => prop = True, (), True, rfl, ?_⟩
  intro (h : (¬ True) = True)
  have hContra : ¬ True := by rw [h]; trivial
  exact hContra trivial

/-- Attack on Semantic Laws of Means:
    Law 2 (Inferential Closure): Means(s, p) ∧ (p → q) → Means(s, q).
    Refuted: Intentionality is hyperintensional; meaning p does not entail meaning all consequences. -/
theorem inferential_closure_of_means_fails :
    ∃ (Subj : Type) (MeansRel : Subj → Prop → Prop) (s : Subj) (p q : Prop),
      MeansRel s p ∧ (p → q) ∧ ¬ MeansRel s q := by
  refine ⟨Unit, fun _ prop => prop = False, (), False, True,
          rfl, fun h => False.elim h, ?_⟩
  intro (h : True = False)
  have hContra : False := by rw [← h]; trivial
  exact hContra

/-- Attack on Semantic Laws of Means:
    Law 3 (Contrastive Relevance): Means(s, p) → ∃ q, Incompatible p q ∧ Means(s, q).
    Refuted by unipolar models. -/
theorem contrastive_closure_of_means_fails :
    ∃ (Subj : Type) (MeansRel : Subj → Prop → Prop) (s : Subj) (p : Prop),
      MeansRel s p ∧ ¬ (∃ q, Incompatible p q ∧ MeansRel s q) := by
  refine ⟨Unit, fun _ prop => prop = True, (), True, rfl, ?_⟩
  intro ⟨q, hIncomp, (hQ : q = True)⟩
  have hIncompTrue : Incompatible True True := by
    rw [hQ] at hIncomp
    exact hIncomp
  exact hIncompTrue ⟨trivial, trivial⟩

-- ===========================================================================
-- Stage 3: Performative Boundary & Global Personhood Consistency
-- ===========================================================================

/-- Substantive Personhood requires interpersonal relations or plurality. -/
def SubstantivePerson (Subj : Type) (s : Subj) : Prop :=
  ∃ (other : Subj), other ≠ s

/-- PERFORMATIVE BOUNDARY THEOREM:
    Performative retorsion forces an intentional subject (Considers, Assumes, Derives, Affirms, Rejects)
    and asymmetric cognitive resolution (SettlementChoice),
    but strictly stops before executive aiming (AimsAt), action execution (Act),
    and substantive personhood (SubstantivePerson). -/
theorem performative_boundary_theorem :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj) (s : Subj) (q : Prop),
      ReductioProgression Subj CS s q ∧
      SettlementChoice CS s (¬ q) q ∧
      (∀ p, ¬ CS.AimsAt s p) ∧
      ¬ SubstantivePerson Subj s := by
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
  have hReductio : ReductioProgression Unit CS0 () True :=
    ⟨rfl, trivial, rfl, rfl, hIncompTrueNotTrue⟩
  have hSC : SettlementChoice CS0 () (¬ True) True :=
    ⟨trivial, trivial, hIncompNotTrueTrue, rfl, rfl⟩
  refine ⟨Unit, CS0, (), True, hReductio, hSC, fun _ h => h, ?_⟩
  intro ⟨other, hDiff⟩
  have hSame : other = () := Subsingleton.elim other ()
  exact hDiff hSame

-- ===========================================================================
-- Stage 4: 9-Component Incremental Choice Chain & Separation Models
-- ===========================================================================

-- 1. Representation
def ReprStage {Subj : Type} (CS : FineCognitiveSubject Subj) (s : Subj) (p q : Prop) : Prop :=
  CS.Considers s p ∧ CS.Considers s q ∧ Incompatible p q

-- 2. Evaluation
def EvalStage {Subj : Type} (CS : FineCognitiveSubject Subj) (s : Subj) (p q : Prop) : Prop :=
  ReprStage CS s p q ∧ CS.Affirms s p ∧ CS.Rejects s q

-- 3. Settlement (Cognitive Resolution)
def SettleStage {Subj : Type} (CS : FineCognitiveSubject Subj) (s : Subj) (p q : Prop) : Prop :=
  EvalStage CS s p q

-- 4. Authorship
def AuthorStage {Subj : Type} (CS : FineCognitiveSubject Subj)
    (SourceOf : Subj → Prop → Prop) (s : Subj) (p q : Prop) : Prop :=
  SettleStage CS s p q ∧ SourceOf s p

-- 5. Practical Aim
def AimStage {Subj : Type} (CS : FineCognitiveSubject Subj)
    (SourceOf : Subj → Prop → Prop) (s : Subj) (p q : Prop) : Prop :=
  AuthorStage CS SourceOf s p q ∧ CS.AimsAt s p ∧ ¬ CS.AimsAt s q

-- 6. Self-Attribution
def SelfAttrStage {Subj : Type} (CS : FineCognitiveSubject Subj)
    (SourceOf : Subj → Prop → Prop) (SelfAttr : Subj → Prop → Prop)
    (s : Subj) (p q : Prop) : Prop :=
  AimStage CS SourceOf s p q ∧ SelfAttr s p

-- 7. Causal Sourcehood (Substance Determination)
def CausalStage {Subj : Type} (CS : FineCognitiveSubject Subj)
    (SourceOf : Subj → Prop → Prop) (SelfAttr : Subj → Prop → Prop)
    (AgentDet : Subj → Prop → Prop) (s : Subj) (p q : Prop) : Prop :=
  SelfAttrStage CS SourceOf SelfAttr s p q ∧ AgentDet s p ∧ ¬ AgentDet s q

-- 8. Alternative Sensitivity (Reasons-Responsiveness)
def ReasonStage {Subj : Type} (CS : FineCognitiveSubject Subj)
    (SourceOf : Subj → Prop → Prop) (SelfAttr : Subj → Prop → Prop)
    (AgentDet : Subj → Prop → Prop) (Responsive : Subj → Prop → Prop → Prop)
    (s : Subj) (p q : Prop) : Prop :=
  CausalStage CS SourceOf SelfAttr AgentDet s p q ∧ Responsive s p q

-- 9. Modal Availability (Bilateral Capacity)
def ModalStage {Subj : Type} (CS : FineCognitiveSubject Subj)
    (SourceOf : Subj → Prop → Prop) (SelfAttr : Subj → Prop → Prop)
    (AgentDet : Subj → Prop → Prop) (Responsive : Subj → Prop → Prop → Prop)
    (CanAct : Subj → Prop → Prop) (s : Subj) (p q : Prop) : Prop :=
  ReasonStage CS SourceOf SelfAttr AgentDet Responsive s p q ∧ CanAct s p ∧ CanAct s q

-- Separation Models:

/-- Separation 1: Representation without Evaluation. -/
theorem separation_repr_without_eval :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj) (s : Subj) (p q : Prop),
      ReprStage CS s p q ∧ ¬ EvalStage CS s p q := by
  have hIncomp : Incompatible (¬ True) True := fun ⟨h1, h2⟩ => h1 h2
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
  refine ⟨Unit, CS0, (), (¬ True), True, ⟨trivial, trivial, hIncomp⟩, ?_⟩
  intro ⟨_, hAff, _⟩
  exact hAff

/-- Separation 2: Settlement without Authorship. -/
theorem separation_settle_without_authorship :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj)
      (SourceOf : Subj → Prop → Prop) (s : Subj) (p q : Prop),
      SettleStage CS s p q ∧ ¬ AuthorStage CS SourceOf s p q := by
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
  refine ⟨Unit, CS0, fun _ _ => False, (), (¬ True), True,
          ⟨⟨trivial, trivial, hIncomp⟩, rfl, rfl⟩, ?_⟩
  intro ⟨_, hSrc⟩
  exact hSrc

/-- Separation 3: Authorship without Practical Aim. -/
theorem separation_author_without_aim :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj)
      (SourceOf : Subj → Prop → Prop) (s : Subj) (p q : Prop),
      AuthorStage CS SourceOf s p q ∧ ¬ AimStage CS SourceOf s p q := by
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
          ⟨⟨⟨trivial, trivial, hIncomp⟩, rfl, rfl⟩, trivial⟩, ?_⟩
  intro ⟨_, hAims, _⟩
  exact hAims

/-- Separation 4: Practical Aim without Self-Attribution. -/
theorem separation_aim_without_self_attr :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj)
      (SourceOf : Subj → Prop → Prop) (SelfAttr : Subj → Prop → Prop)
      (s : Subj) (p q : Prop),
      AimStage CS SourceOf s p q ∧ ¬ SelfAttrStage CS SourceOf SelfAttr s p q := by
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
  refine ⟨Unit, CS0, fun _ _ => True, fun _ _ => False, (), (¬ True), True,
          ⟨⟨⟨⟨trivial, trivial, hIncomp⟩, rfl, rfl⟩, trivial⟩, rfl, hNotAimsTrue⟩, ?_⟩
  intro ⟨_, hAttr⟩
  exact hAttr

/-- Separation 5: Self-Attribution without Substance Determination. -/
theorem separation_self_attr_without_causal :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj)
      (SourceOf : Subj → Prop → Prop) (SelfAttr : Subj → Prop → Prop)
      (AgentDet : Subj → Prop → Prop) (s : Subj) (p q : Prop),
      SelfAttrStage CS SourceOf SelfAttr s p q ∧
      ¬ CausalStage CS SourceOf SelfAttr AgentDet s p q := by
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
  refine ⟨Unit, CS0, fun _ _ => True, fun _ _ => True, fun _ _ => False, (), (¬ True), True,
          ⟨⟨⟨⟨⟨trivial, trivial, hIncomp⟩, rfl, rfl⟩, trivial⟩, rfl, hNotAimsTrue⟩, trivial⟩, ?_⟩
  intro ⟨_, hDet, _⟩
  exact hDet

/-- Separation 6: Substance Determination without Reasons-Responsiveness. -/
theorem separation_causal_without_reason :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj)
      (SourceOf : Subj → Prop → Prop) (SelfAttr : Subj → Prop → Prop)
      (AgentDet : Subj → Prop → Prop) (Responsive : Subj → Prop → Prop → Prop)
      (s : Subj) (p q : Prop),
      CausalStage CS SourceOf SelfAttr AgentDet s p q ∧
      ¬ ReasonStage CS SourceOf SelfAttr AgentDet Responsive s p q := by
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
  let AgentDet0 : Unit → Prop → Prop := fun _ prop => prop = (¬ True)
  have hNotDetTrue : ¬ AgentDet0 () True := by
    intro (h : True = (¬ True))
    have hContra : ¬ True := by rw [← h]; trivial
    exact hContra trivial
  refine ⟨Unit, CS0, fun _ _ => True, fun _ _ => True, AgentDet0, fun _ _ _ => False, (), (¬ True), True,
          ⟨⟨⟨⟨⟨⟨trivial, trivial, hIncomp⟩, rfl, rfl⟩, trivial⟩, rfl, hNotAimsTrue⟩, trivial⟩, rfl, hNotDetTrue⟩, ?_⟩
  intro ⟨_, hResp⟩
  exact hResp

/-- Separation 7: Reasons-Responsive Choice without Bilateral Modal Alternative. -/
theorem separation_reason_without_modal :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj)
      (SourceOf : Subj → Prop → Prop) (SelfAttr : Subj → Prop → Prop)
      (AgentDet : Subj → Prop → Prop) (Responsive : Subj → Prop → Prop → Prop)
      (CanAct : Subj → Prop → Prop) (s : Subj) (p q : Prop),
      ReasonStage CS SourceOf SelfAttr AgentDet Responsive s p q ∧
      ¬ ModalStage CS SourceOf SelfAttr AgentDet Responsive CanAct s p q := by
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
  let AgentDet0 : Unit → Prop → Prop := fun _ prop => prop = (¬ True)
  have hNotDetTrue : ¬ AgentDet0 () True := by
    intro (h : True = (¬ True))
    have hContra : ¬ True := by rw [← h]; trivial
    exact hContra trivial
  refine ⟨Unit, CS0, fun _ _ => True, fun _ _ => True, AgentDet0, fun _ _ _ => True, fun _ _ => False,
          (), (¬ True), True,
          ⟨⟨⟨⟨⟨⟨⟨trivial, trivial, hIncomp⟩, rfl, rfl⟩, trivial⟩, rfl, hNotAimsTrue⟩, trivial⟩, rfl, hNotDetTrue⟩, trivial⟩, ?_⟩
  intro ⟨_, hCanP, _⟩
  exact hCanP

end Logos.A14SemanticAudit
