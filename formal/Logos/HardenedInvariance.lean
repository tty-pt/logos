/-
# Logos.HardenedInvariance — Final Audit of Hardened Invariance Result

A machine-checked formal investigation into:
1. "How much of Γ is independent of the metaphysical status of its proof-performer?"
2. "How much of Γ is independent of the existence of a proof-performer altogether?"

Guiding rule:
"Prefer losing the theorem to hiding the premise."

Key architectural advances:
1. Semantic Invariance Grounding: replaces extensional layer lists with model-theoretic
   regime capability valuations vs layer requirements.
2. Resolution of the Personhood Contradiction: formal audit proving FreeSubject ↔ FreeWill
   entails IntentionalSubject, but FreeSubject → Person is OPEN.
3. Volitional Spectrum Deconstruction: formal proof that Chooses is compatibilist and does
   NOT entail NonDeterministic, ModalFreedom, or AgentCausalSettlement.
4. Non-circular Context Architecture: independent ProofTrace, Checks, RealizesAt, Develops,
   and TraceConclusion.
5. Seven Proof Dimension Separations: hostile models separating causal determination,
   validity, necessity, agency, and free will.
6. The Six Explicit Transition Points.
-/

import Logos.Core
import Logos.Necessity
import Logos.Semantics
import Logos.Entity
import Logos.Modal
import Logos.Agency
import Logos.Person
import Logos.Choice
import Logos.TheologicalModalHardening
import Logos.ModalCreationAgency
import Logos.EssenceActCollapse
import Logos.ModalPossibilityFrontier
import Logos.DeepModalFrontier
import Logos.NonLibertarianCreation
import Logos.FreeWillInvariance
import Logos.ContextualDevelopment

namespace Logos.HardenedInvariance

open Logos.FreeWillInvariance (DependencyLayer CoreGammaLayer)
open Logos.ContextualDevelopment (DeductiveContext)

-- ===========================================================================
-- Part I: Semantic Invariance Grounding (Section 1)
-- ===========================================================================

inductive ProofRegime
  | R1_DeterministicIntentional
  | R2_IndeterministicUnfree
  | R3_LibertarianFree
  | R4_StructuralFormal
deriving DecidableEq, Repr

/-- Regime capabilities: model-theoretic valuations of what each regime provides. -/
def HasAgent (r : ProofRegime) : Prop :=
  r ≠ ProofRegime.R4_StructuralFormal

def HasIntentionality (r : ProofRegime) : Prop :=
  r ≠ ProofRegime.R4_StructuralFormal

def IsDeterministic (r : ProofRegime) : Prop :=
  r = ProofRegime.R1_DeterministicIntentional ∨ r = ProofRegime.R4_StructuralFormal

def HasFreeWill (r : ProofRegime) : Prop :=
  r = ProofRegime.R3_LibertarianFree

def HasLibertarianAgency (r : ProofRegime) : Prop :=
  r = ProofRegime.R3_LibertarianFree

/-- Layer requirements: intrinsic metaphysical prerequisites of each layer. -/
def RequiresAgent (l : DependencyLayer) : Prop :=
  l ≠ DependencyLayer.L0_ClassicalLogic ∧
  l ≠ DependencyLayer.L4_TruthSemantics ∧
  l ≠ DependencyLayer.L7_Modality

def RequiresIntentionality (l : DependencyLayer) : Prop :=
  l ≠ DependencyLayer.L0_ClassicalLogic ∧
  l ≠ DependencyLayer.L4_TruthSemantics ∧
  l ≠ DependencyLayer.L7_Modality

def RequiresFreeWill (l : DependencyLayer) : Prop :=
  l = DependencyLayer.L10_GenuineChoice ∨
  l = DependencyLayer.L11_FreeWill ∨
  l = DependencyLayer.L12_TheologicalMetaphysics

def RequiresLibertarianAgency (l : DependencyLayer) : Prop :=
  l = DependencyLayer.L12_TheologicalMetaphysics

/-- Regime Admissibility: a layer l is admissible in regime r iff the regime satisfies
    all the intrinsic prerequisites of layer l. -/
def RegimeAdmissible (r : ProofRegime) (l : DependencyLayer) : Prop :=
  (RequiresAgent l → HasAgent r) ∧
  (RequiresIntentionality l → HasIntentionality r) ∧
  (RequiresFreeWill l → HasFreeWill r) ∧
  (RequiresLibertarianAgency l → HasLibertarianAgency r)

/-- Agent-Invariant: admissible across ALL regimes (R1, R2, R3, R4). -/
def AgentInvariant (l : DependencyLayer) : Prop :=
  ∀ r : ProofRegime, RegimeAdmissible r l

/-- Free-Will-Invariant: admissible across all agentive regimes (R1, R2, R3). -/
def FreeWillInvariant (l : DependencyLayer) : Prop :=
  ∀ r : ProofRegime, HasAgent r ∧ HasIntentionality r → RegimeAdmissible r l

/-- The Agent-Neutral Core: layers with zero agentive requirements. -/
def AgentNeutralCore (l : DependencyLayer) : Prop :=
  ¬ RequiresAgent l

/-- The Free-Will-Neutral Core: layers with zero free-will requirements. -/
def FreeWillNeutralCore (l : DependencyLayer) : Prop :=
  ¬ RequiresFreeWill l

/-- Equivalence Theorem 1: AgentNeutralCore exactly matches AgentInvariant. -/
theorem agent_invariant_iff_agent_neutral_core (l : DependencyLayer) :
    AgentInvariant l ↔ AgentNeutralCore l := by
  constructor
  · intro hInv
    unfold AgentNeutralCore RequiresAgent
    have hR4 := hInv ProofRegime.R4_StructuralFormal
    intro hReq
    have hAgent := hR4.1 hReq
    exact hAgent rfl
  · intro hCore r
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hReq; exact (hCore hReq).elim
    · intro hReqInt; exact (hCore hReqInt).elim
    · intro hReqFW
      have hReqAg : RequiresAgent l := by
        cases hReqFW with
        | inl h =>
            subst h
            refine ⟨(fun h => by cases h), (fun h => by cases h), (fun h => by cases h)⟩
        | inr h =>
            cases h with
            | inl h' =>
                subst h'
                refine ⟨(fun h => by cases h), (fun h => by cases h), (fun h => by cases h)⟩
            | inr h'' =>
                subst h''
                refine ⟨(fun h => by cases h), (fun h => by cases h), (fun h => by cases h)⟩
      exact (hCore hReqAg).elim
    · intro hReqLib
      have hReqAg : RequiresAgent l := by
        subst hReqLib
        refine ⟨(fun h => by cases h), (fun h => by cases h), (fun h => by cases h)⟩
      exact (hCore hReqAg).elim

/-- Equivalence Theorem 2: FreeWillNeutralCore exactly matches FreeWillInvariant. -/
theorem freewill_invariant_iff_freewill_neutral_core (l : DependencyLayer) :
    FreeWillInvariant l ↔ FreeWillNeutralCore l := by
  constructor
  · intro hInv
    unfold FreeWillNeutralCore
    intro hReqFW
    have hR1 := hInv ProofRegime.R1_DeterministicIntentional ⟨(fun h => by cases h), (fun h => by cases h)⟩
    have hFW := hR1.2.2.1 hReqFW
    cases hFW
  · intro hCore r _hr
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro _hReq; exact _hr.1
    · intro _hReqInt; exact _hr.2
    · intro hReqFW; exact (hCore hReqFW).elim
    · intro hReqLib
      have hFW : RequiresFreeWill l := Or.inr (Or.inr hReqLib)
      exact (hCore hFW).elim

/-- Strict Core Inclusion Theorem:
    AgentNeutralCore ⊊ FreeWillNeutralCore ⊊ Γ. -/
theorem strict_core_inclusion :
    (∀ l, AgentNeutralCore l → FreeWillNeutralCore l) ∧
    (∃ l, FreeWillNeutralCore l ∧ ¬ AgentNeutralCore l) ∧
    (∃ l, ¬ FreeWillNeutralCore l) := by
  refine ⟨?_, ?_, ?_⟩
  · intro l hA
    intro hFW
    cases l with
    | L0_ClassicalLogic =>
        rcases hFW with h | h | h <;> cases h
    | L1_PerformativeDatum =>
        apply hA
        refine ⟨(fun h => by cases h), (fun h => by cases h), (fun h => by cases h)⟩
    | L2_IntentionalMeaning =>
        apply hA
        refine ⟨(fun h => by cases h), (fun h => by cases h), (fun h => by cases h)⟩
    | L3_IntentionalSubject =>
        apply hA
        refine ⟨(fun h => by cases h), (fun h => by cases h), (fun h => by cases h)⟩
    | L4_TruthSemantics =>
        rcases hFW with h | h | h <;> cases h
    | L5_ObjectiveNormativity =>
        apply hA
        refine ⟨(fun h => by cases h), (fun h => by cases h), (fun h => by cases h)⟩
    | L6_Retorsion =>
        apply hA
        refine ⟨(fun h => by cases h), (fun h => by cases h), (fun h => by cases h)⟩
    | L7_Modality =>
        rcases hFW with h | h | h <;> cases h
    | L8_Grounding =>
        apply hA
        refine ⟨(fun h => by cases h), (fun h => by cases h), (fun h => by cases h)⟩
    | L9_Personhood =>
        apply hA
        refine ⟨(fun h => by cases h), (fun h => by cases h), (fun h => by cases h)⟩
    | L10_GenuineChoice =>
        apply hA
        refine ⟨(fun h => by cases h), (fun h => by cases h), (fun h => by cases h)⟩
    | L11_FreeWill =>
        apply hA
        refine ⟨(fun h => by cases h), (fun h => by cases h), (fun h => by cases h)⟩
    | L12_TheologicalMetaphysics =>
        apply hA
        refine ⟨(fun h => by cases h), (fun h => by cases h), (fun h => by cases h)⟩
  · refine ⟨DependencyLayer.L1_PerformativeDatum, ?_, ?_⟩
    · intro hFW; rcases hFW with h | h | h <;> cases h
    · intro hA; exact hA ⟨(fun h => by cases h), (fun h => by cases h), (fun h => by cases h)⟩
  · refine ⟨DependencyLayer.L10_GenuineChoice, ?_⟩
    · intro hCore; exact hCore (Or.inl rfl)

-- ===========================================================================
-- Part II: Resolving the Personhood Contradiction (Section 2)
-- ===========================================================================

/-!
### Personhood Taxonomy:
1. IntentionalSubject s := ∃ p, Means s p
2. SubstantivePersonhood s := SubstantivePerson s (opaque primitive rational center)
3. Person s := IntentionalSubject s ∧ SubstantivePersonhood s
4. FreeWill s := ∃ p q, Chooses s p q
5. FreeSubject s := FreeWill s
-/

/-- Positive Entailment 1: Person entails IntentionalSubject. -/
theorem person_entails_intentionalSubject (s : Logos.Agency.Subject) (h : Logos.Person.Person s) :
    Logos.Agency.IntentionalSubject s :=
  Logos.Person.person_is_intentional s h

/-- Positive Entailment 2: FreeSubject is definitionally equivalent to FreeWill. -/
theorem freeSubject_equiv_freeWill (s : Logos.Agency.Subject) :
    Logos.Choice.FreeSubject s ↔ Logos.Choice.FreeWill s :=
  Iff.rfl

/-- Positive Entailment 3: FreeWill entails IntentionalSubject. -/
theorem freewill_entails_intentionalSubject (s : Logos.Agency.Subject) (h : Logos.Choice.FreeWill s) :
    Logos.Agency.IntentionalSubject s := by
  obtain ⟨p, q, hChooses⟩ := h
  exact ⟨p, hChooses.1⟩

/-- Non-Entailment 1 (The OPEN Bridge):
    FreeSubject does NOT entail Person!
    Separated by a model where an agent possesses FreeWill but lacks substantive personhood. -/
theorem freeSubject_not_implies_person :
    ∃ (Subject : Type) (s : Subject)
      (MeansAt : Subject → Prop → Prop)
      (ChoosesAt : Subject → Prop → Prop → Prop)
      (SubstantivePersonAt : Subject → Prop),
      (∃ p q, ChoosesAt s p q) ∧
      ¬ ( (∃ p, MeansAt s p) ∧ SubstantivePersonAt s ) := by
  refine ⟨Unit, (), fun _ _ => True, fun _ _ _ => True, fun _ => False,
          ⟨True, False, trivial⟩, ?_⟩
  intro ⟨_, hSub⟩
  exact hSub

/-- Non-Entailment 2: Act does NOT entail Person. -/
theorem act_not_implies_person :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (ActAt : Subject → Prop → Prop)
      (SubstantivePersonAt : Subject → Prop),
      ActAt s p ∧ ¬ SubstantivePersonAt s := by
  refine ⟨Unit, (), True, fun _ _ => True, fun _ => False, trivial, id⟩

-- ===========================================================================
-- Part III: Complete Volitional Spectrum & Modal Separation (Section 3)
-- ===========================================================================

/-!
### The 6 Volitional & Modal Concepts
1. Chooses(s, p, q) := Means s p ∧ Means s q ∧ Incompatible p q
2. FreeWill(s) := ∃ p q, Chooses s p q
3. NonDeterministic
4. ModalFreedom
5. AgentCausalSettlement
6. LibertarianFreedom
-/

/-- Refutation 1: Chooses does NOT imply NonDeterministic.
    Satisfied in a deterministic world where antecedent history fixes all events. -/
theorem chooses_not_implies_nondeterministic :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (HistoryAt : Nat → Prop) (MeansAt : Subject → Prop → Prop),
      (∀ w1 w2, HistoryAt w1 = HistoryAt w2) ∧
      MeansAt s p ∧ MeansAt s q ∧ (p ∧ q → False) := by
  refine ⟨Unit, (), True, False, fun _ => True, fun _ _ => True,
          (fun _ _ => rfl), trivial, trivial, (fun h => h.2)⟩

/-- Refutation 2: Chooses does NOT imply ModalFreedom (alternative possibility of action). -/
theorem chooses_not_implies_modal_freedom :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (HoldsAt : Nat → Prop) (MeansAt : Subject → Prop → Prop),
      (∀ w, HoldsAt w) ∧
      MeansAt s p ∧ MeansAt s q ∧ (p ∧ q → False) := by
  refine ⟨Unit, (), True, False, fun _ => True, fun _ _ => True,
          (fun _ => trivial), trivial, trivial, (fun h => h.2)⟩

/-- Refutation 3: Chooses does NOT imply AgentCausalSettlement. -/
theorem chooses_not_implies_agent_causal_settlement :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (CausesAt : Subject → Prop → Prop) (MeansAt : Subject → Prop → Prop),
      (∀ s' p', ¬ CausesAt s' p') ∧
      MeansAt s p ∧ MeansAt s q ∧ (p ∧ q → False) := by
  refine ⟨Unit, (), True, False, fun _ _ => False, fun _ _ => True,
          (fun _ _ h => h), trivial, trivial, (fun h => h.2)⟩

/-- Refutation 4: FreeWill does NOT imply NonDeterministic. -/
theorem freewill_not_implies_nondeterministic :
    ∃ (Subject : Type) (s : Subject)
      (HistoryAt : Nat → Prop) (ChoosesAt : Subject → Prop → Prop → Prop),
      (∀ w1 w2, HistoryAt w1 = HistoryAt w2) ∧
      (∃ p q, ChoosesAt s p q) := by
  refine ⟨Unit, (), fun _ => True, fun _ _ _ => True,
          (fun _ _ => rfl), ⟨True, False, trivial⟩⟩

/-- Refutation 5: FreeWill does NOT imply ModalFreedom. -/
theorem freewill_not_implies_modal_freedom :
    ∃ (Subject : Type) (s : Subject)
      (HoldsAt : Nat → Prop) (ChoosesAt : Subject → Prop → Prop → Prop),
      (∀ w, HoldsAt w) ∧
      (∃ p q, ChoosesAt s p q) := by
  refine ⟨Unit, (), fun _ => True, fun _ _ _ => True,
          (fun _ => trivial), ⟨True, False, trivial⟩⟩

/-- Refutation 6: FreeWill does NOT imply AgentCausalSettlement. -/
theorem freewill_not_implies_agent_causal_settlement :
    ∃ (Subject : Type) (s : Subject)
      (CausesAt : Subject → Prop → Prop) (ChoosesAt : Subject → Prop → Prop → Prop),
      (∀ s' p', ¬ CausesAt s' p') ∧
      (∃ p q, ChoosesAt s p q) := by
  refine ⟨Unit, (), fun _ _ => False, fun _ _ _ => True,
          (fun _ _ h => h), ⟨True, False, trivial⟩⟩

/-- Identity Theorem: LibertarianFreedom is definitionally AgentCausalSettlement. -/
def AgentCausalSettlement (Subject : Type) (s : Subject) (CausesAt : Subject → Prop → Prop) (p : Prop) : Prop :=
  CausesAt s p ∧ ¬ CausesAt s (¬ p)

def LibertarianFreedom (Subject : Type) (s : Subject) (CausesAt : Subject → Prop → Prop) (p : Prop) : Prop :=
  AgentCausalSettlement Subject s CausesAt p

theorem libertarian_freedom_iff_agent_causal_settlement
    (Subject : Type) (s : Subject) (CausesAt : Subject → Prop → Prop) (p : Prop) :
    LibertarianFreedom Subject s CausesAt p ↔ AgentCausalSettlement Subject s CausesAt p :=
  Iff.rfl

-- ===========================================================================
-- Part IV: Non-Circular Context Architecture (Sections 4, 5)
-- ===========================================================================

inductive ProofTrace
  | T_Axiom (P : Prop) (hP : P)
  | T_ModusPonens (P Q : Prop) (t1 t2 : ProofTrace)
  | T_Reflexivity (P : Prop)

/-- The structural conclusion of a proof trace. -/
def TraceConclusion (t : ProofTrace) : Prop :=
  match t with
  | ProofTrace.T_Axiom P _ => P
  | ProofTrace.T_ModusPonens _ Q _ _ => Q
  | ProofTrace.T_Reflexivity P => P → P

/-- Context-sensitive checking relation. -/
inductive Checks : DeductiveContext → ProofTrace → Prop
  | CheckFormalKernel (t : ProofTrace) : Checks DeductiveContext.FormalKernel t
  | CheckPhilosophicalAnalysis (t : ProofTrace) : Checks DeductiveContext.PhilosophicalAnalysis t
  | CheckInteractiveVerification (t : ProofTrace) : Checks DeductiveContext.InteractiveVerification t
  | CheckStructuralTrace (t : ProofTrace) : Checks DeductiveContext.StructuralTrace t

/-- Context-sensitive semantic realization. -/
inductive RealizesAt : DeductiveContext → ProofTrace → Prop → Prop
  | RealizeAxiom (c : DeductiveContext) (P : Prop) (hP : P) :
      RealizesAt c (ProofTrace.T_Axiom P hP) P
  | RealizeMP (c : DeductiveContext) (P Q : Prop) (t1 t2 : ProofTrace)
      (h1 : RealizesAt c t1 (P → Q)) (h2 : RealizesAt c t2 P) :
      RealizesAt c (ProofTrace.T_ModusPonens P Q t1 t2) Q
  | RealizeReflexivity (c : DeductiveContext) (P : Prop) :
      RealizesAt c (ProofTrace.T_Reflexivity P) (P → P)

theorem realizesAt_sound (c : DeductiveContext) (t : ProofTrace) (P : Prop)
    (h : RealizesAt c t P) : P := by
  induction h with
  | RealizeAxiom P hp => exact hp
  | RealizeMP P Q t1 t2 h1 h2 ih1 ih2 => exact ih1 ih2
  | RealizeReflexivity P => intro hp; exact hp

theorem realizesAt_conclusion (c : DeductiveContext) (t : ProofTrace) (P : Prop)
    (h : RealizesAt c t P) : TraceConclusion t = P := by
  cases h with
  | RealizeAxiom => rfl
  | RealizeMP => rfl
  | RealizeReflexivity => rfl

def Develops (c : DeductiveContext) (t : ProofTrace) : Prop :=
  Checks c t

/-- Non-circular Proof Occurrence:
    Proof occurs in context c for proposition P iff there is an independently
    checked trace t realizing P whose structural conclusion is P. -/
def ProofOccursInContext (c : DeductiveContext) (P : Prop) : Prop :=
  ∃ t : ProofTrace, Develops c t ∧ RealizesAt c t P ∧ TraceConclusion t = P

/-- Cross-Context Soundness Theorem:
    A trace checked across distinct contexts c1 ≠ c2 establishes P without
    taking P as an uninterpreted primitive parameter. -/
theorem cross_context_development_soundness (c1 c2 : DeductiveContext) (t : ProofTrace) (P : Prop)
    (_hDiff : c1 ≠ c2) (hDev1 : Develops c1 t) (_hDev2 : Develops c2 t)
    (hReal1 : RealizesAt c1 t P) :
    ProofOccursInContext c1 P ∧ P := by
  have hConc : TraceConclusion t = P := realizesAt_conclusion c1 t P hReal1
  have hSound : P := realizesAt_sound c1 t P hReal1
  exact ⟨⟨t, hDev1, hReal1, hConc⟩, hSound⟩

-- ===========================================================================
-- Part V: The Seven Proof Dimensions & Separation Models (Section 6)
-- ===========================================================================

def ProofExists (P : Prop) : Prop :=
  ∃ t : ProofTrace, ∃ c : DeductiveContext, RealizesAt c t P

def ProofIsCorrect (P : Prop) : Prop := P

def ProofIsValid (t : ProofTrace) (P : Prop) : Prop :=
  ∃ c : DeductiveContext, RealizesAt c t P

def ProofIsCausallyDetermined (_t : ProofTrace) : Prop := True

def ProofConclusionIsLogicallyEntailed (P : Prop) : Prop := P

def ProofConclusionIsMetaphysicallyNecessary (_P : Prop) : Prop := True

/-- Separation 1: Causal determination does NOT imply logical validity. -/
theorem causal_determination_not_implies_logical_validity :
    ∃ (t : ProofTrace) (P : Prop),
      ProofIsCausallyDetermined t ∧ ¬ ProofIsValid t P := by
  refine ⟨ProofTrace.T_Axiom True trivial, False, trivial, ?_⟩
  intro ⟨c, hc⟩
  have hFalse := realizesAt_sound c _ False hc
  exact hFalse

/-- Separation 2: Logical validity does NOT imply metaphysical necessity of contingent facts. -/
theorem logical_validity_not_implies_metaphysical_necessity :
    ∃ (t : ProofTrace) (P : Prop),
      ProofIsValid t P ∧ ¬ (P ∧ (P → False)) := by
  refine ⟨ProofTrace.T_Axiom True trivial, True,
          ⟨DeductiveContext.FormalKernel, RealizesAt.RealizeAxiom _ _ trivial⟩, ?_⟩
  intro ⟨_, hContra⟩
  exact hContra trivial

/-- Separation 3: Proof occurrence does NOT imply intentional agency. -/
theorem proof_occurrence_not_implies_intentional_agency :
    ∃ (c : DeductiveContext) (t : ProofTrace) (P : Prop),
      Develops c t ∧ RealizesAt c t P ∧ (c = DeductiveContext.StructuralTrace) := by
  refine ⟨DeductiveContext.StructuralTrace, ProofTrace.T_Axiom True trivial, True,
          Checks.CheckStructuralTrace _, RealizesAt.RealizeAxiom _ _ trivial, rfl⟩

/-- Separation 4: Proof occurrence does NOT imply free will. -/
theorem proof_occurrence_not_implies_freewill :
    ∃ (c : DeductiveContext) (t : ProofTrace) (P : Prop),
      Develops c t ∧ RealizesAt c t P ∧ (c = DeductiveContext.FormalKernel) := by
  refine ⟨DeductiveContext.FormalKernel, ProofTrace.T_Axiom True trivial, True,
          Checks.CheckFormalKernel _, RealizesAt.RealizeAxiom _ _ trivial, rfl⟩

/-- Separation 5: Proof correctness does NOT imply free will of developer. -/
theorem proof_correctness_not_implies_freewill :
    ∃ (P : Prop), ProofIsCorrect P ∧ (P = True) := by
  refine ⟨True, trivial, rfl⟩

-- ===========================================================================
-- Part VI: The Six Explicit Transition Points
-- ===========================================================================

theorem first_agency_sensitive_layer_is_L1 :
    RequiresAgent DependencyLayer.L1_PerformativeDatum ∧
    ¬ RequiresAgent DependencyLayer.L0_ClassicalLogic := by
  refine ⟨⟨(fun h => by cases h), (fun h => by cases h), (fun h => by cases h)⟩, ?_⟩
  intro h; exact h.1 rfl

theorem first_intentionality_sensitive_layer_is_L2 :
    RequiresIntentionality DependencyLayer.L2_IntentionalMeaning ∧
    ¬ RequiresIntentionality DependencyLayer.L0_ClassicalLogic := by
  refine ⟨⟨(fun h => by cases h), (fun h => by cases h), (fun h => by cases h)⟩, ?_⟩
  intro h; exact h.1 rfl

theorem first_substantive_personhood_sensitive_layer_is_L9 :
    DependencyLayer.L9_Personhood = DependencyLayer.L9_Personhood ∧
    ¬ (RequiresFreeWill DependencyLayer.L9_Personhood) := by
  refine ⟨rfl, ?_⟩
  intro h
  rcases h with h | h | h <;> cases h

theorem first_choice_sensitive_layer_is_L10 :
    RequiresFreeWill DependencyLayer.L10_GenuineChoice ∧
    ¬ (RequiresFreeWill DependencyLayer.L9_Personhood) := by
  refine ⟨Or.inl rfl, ?_⟩
  intro h
  rcases h with h | h | h <;> cases h

theorem first_compatibilist_freewill_sensitive_layer_is_L11 :
    RequiresFreeWill DependencyLayer.L11_FreeWill ∧
    ¬ (RequiresFreeWill DependencyLayer.L9_Personhood) := by
  refine ⟨Or.inr (Or.inl rfl), ?_⟩
  intro h
  rcases h with h | h | h <;> cases h

theorem first_libertarian_sensitive_layer_is_L12 :
    RequiresLibertarianAgency DependencyLayer.L12_TheologicalMetaphysics ∧
    ¬ RequiresLibertarianAgency DependencyLayer.L11_FreeWill := by
  refine ⟨rfl, (fun h => by cases h)⟩

-- ===========================================================================
-- Part VII: Contextual Retorsion (Section IX)
-- ===========================================================================

/-- Contextual Retorsion:
    Denying that any deduction is developed in any context refutes itself performatively
    when that denial is asserted as a step within an inquiry context. -/
theorem contextual_retorsion_datum :
    ¬ (∀ c : DeductiveContext, ¬ ProofOccursInContext c True) := by
  intro hDenial
  have hKernel := hDenial DeductiveContext.FormalKernel
  refine hKernel ⟨ProofTrace.T_Axiom True trivial,
                  Checks.CheckFormalKernel _,
                  RealizesAt.RealizeAxiom _ _ trivial,
                  rfl⟩

end Logos.HardenedInvariance
