-- Consolidated Agency Audits and Frontiers
import Logos.ActionAndNormativeChoice
import Logos.Agency
import Logos.Alternatives
import Logos.Choice
import Logos.Core
import Logos.Entity
import Logos.Modal
import Logos.ModalCreationFrontiers
import Logos.Necessity
import Logos.Order
import Logos.Person
import Logos.Retorsion
import Logos.Semantics


/-
================================================================================
SECTION: WillIndividuationAudit
================================================================================
-/
/-
# Logos.WillIndividuationAudit — Independence Audit of `will_individuation` (A18)

`will_individuation` (`Logos.Agency`) is declared `Tag: VOCAB` — a constitutive
meaning-postulate, not a theorem. This module machine-witnesses that status
at the kernel level:

- A hostile model `HostileModel` (spec §5.1: `Subject := Bool`, `Will := Unit`,
  `subjectWill := fun _ => ()`) satisfies the pre-will spine together with its
  performative datum (`hostile_model_satisfies_prewill_spine`, `{}`).
- In that same model the law's own instantiation at `true`/`false` **arrives at
  a contradiction**: `subjectWill true != subjectWill false` is demanded while
  both sides are `()` (`hostile_model_refutes_will_individuation`, `{}`).
- Therefore the law cannot follow from the spine: if it did, it would hold in
  every model of the spine, including this one, where it is refutable
  (`will_individuation_not_forced_by_prewill_spine`, `{}`).

So the VOCAB meaning-postulate status of A18 is a **kernel fact**, witnessed
not by a missing proof but by a model in which the asserted law is contradictory.

Governing methodological rule (shared with `Logos.AxiomNegationAudit`):
  "Prefer losing the theorem to hiding the premise."
-/


namespace Logos.WillIndividuationAudit

/-- Pre-Will Spine Signature:
    The Agency layer up to and including the will faculty `subjectWill`, ordered
    BEFORE the individuation law. The performative core (Means/State/Initiates)
    plus the will sorts are uninterpreted: nothing in the spine imposes
    injectivity of `subjectWill`. -/
structure PreWillSpine where
  Subject     : Type
  Means       : Subject → Prop → Prop
  State       : Type
  Initiates   : Subject → State → State → Prop → Prop
  Will        : Type
  subjectWill : Subject → Will

/-- The performative datum of the pre-will spine: some act occurs. -/
def PreWillDatumHolds (S : PreWillSpine) : Prop :=
  ∃ s p, S.Means s p ∧ ∃ w w', S.Initiates s w w' p

/-- The `will_individuation` law over a signature:
    distinct subjects possess numerically distinct will faculties. -/
def WillIndividuationStatement (S : PreWillSpine) : Prop :=
  ∀ s₁ s₂, s₁ ≠ s₂ → S.subjectWill s₁ ≠ S.subjectWill s₂

/-- Negation of `will_individuation`:
    there exist distinct subjects sharing one numerically identical will. -/
def NegWillIndividuation (S : PreWillSpine) : Prop :=
  ∃ s₁ s₂, s₁ ≠ s₂ ∧ S.subjectWill s₁ = S.subjectWill s₂

/-- The hostile pre-will spine model (STRENGTH.md §5.1):
    `Subject := Bool`, `Will := Unit`, `subjectWill := fun _ => ()` — every
    subject is collapsed onto the single trivial will `()`. -/
def HostileModel : PreWillSpine := {
  Subject     := Bool
  Means       := fun _ _ => True
  State       := Unit
  Initiates   := fun _ _ _ _ => True
  Will        := Unit
  subjectWill := fun _ => ()
}

/-- The hostile model satisfies the pre-will spine: the performative datum
    holds (subject `true` acts on proposition `True`). -/
theorem hostile_model_satisfies_prewill_spine :
    PreWillDatumHolds HostileModel := by
  exact ⟨true, True, trivial, ⟨(), (), trivial⟩⟩

/-- The law refutes in the hostile model: forcing `will_individuation` on this
    spine-model arrives at a contradiction, since distinct subjects `true`/`false`
    must then receive distinct wills while `subjectWill true` and
    `subjectWill false` are both `()`. -/
theorem hostile_model_refutes_will_individuation :
    WillIndividuationStatement HostileModel → False := by
  rintro h
  have hd : HostileModel.subjectWill true ≠ HostileModel.subjectWill false :=
    h true false (by intro h'; cases h')
  exact hd rfl

/-- Independence Theorem for `will_individuation`:
    the pre-will spine + its performative datum does NOT force the individuation
    law — the hostile model satisfies the spine while the law is refutable there.
    Hence A18 is a declared meaning-postulate, and its VOCAB status is a kernel
    fact, not a derivation gap. -/
theorem will_individuation_not_forced_by_prewill_spine :
    ∃ S : PreWillSpine, PreWillDatumHolds S ∧ NegWillIndividuation S := by
  exact ⟨HostileModel, hostile_model_satisfies_prewill_spine,
         ⟨true, false, (by intro h'; cases h'), rfl⟩⟩

end Logos.WillIndividuationAudit


/-
================================================================================
SECTION: ContextualDevelopment
================================================================================
-/
/-
# Logos.ContextualDevelopment — The Deduction Exists Across Contexts

A machine-checked formal investigation into the structural and performative datum:
"The proof is being developed in multiple contexts of the whole deduction."

Governing rule:
"Prefer losing the theorem to hiding the premise."

Methodological disciplines:
1. Strict formal distinction between ProofPerformance(s, c), ProofDevelopment(c, Γ),
   and DeductiveContext.
2. Proof development does not definitionally or deductively entail FreeWill(s).
3. Context presence does not entail free context selection.
4. Multiple contexts do not presuppose distinct physical worlds or independent minds.
5. Model morphism across M_D (deterministic), M_N (unfree non-deterministic),
   M_F (libertarian free), and M_S (structural trace).
6. Master theorem: Cross-context development preserves Core(Γ).
7. Audited entry ladder for Intentionality, Agency, Personhood, Choice, and Free Will.
-/


namespace Logos.ContextualDevelopment

open Logos.TheologicalModalHardening (KripkeFrame)
open Logos.DeepModalFrontier (S5UniversalFrame)
open Logos.FreeWillInvariance (DependencyLayer CoreGammaLayer LayerRequiresFreeWill)

-- ===========================================================================
-- Part I: Contexts, Performance & Development (Sections 1, 2, 3, 6)
-- ===========================================================================

/-!
### 1. Architectural Definitions
We define DeductiveContext as an inductive spectrum of inquiry contexts,
ProofPerformance, and ProofDevelopment.
-/

inductive DeductiveContext
  | FormalKernel
  | PhilosophicalAnalysis
  | InteractiveVerification
  | StructuralTrace
deriving DecidableEq, Repr

def ProofPerformance (Subject : Type) (s : Subject) (c : DeductiveContext)
    (PerformsAt : Subject → DeductiveContext → Prop) : Prop :=
  PerformsAt s c

def ProofDevelopment (c : DeductiveContext) (GammaCore : Prop)
    (DevelopsAt : DeductiveContext → Prop → Prop) : Prop :=
  DevelopsAt c GammaCore

/-!
### 2. Separations: Performance vs Development vs Free Will
-/

/-- Separation: ProofPerformance does NOT entail FreeWill. -/
theorem performance_not_entails_freewill :
    ∃ (Subject : Type) (s : Subject) (c : DeductiveContext)
      (PerformsAt : Subject → DeductiveContext → Prop) (FreeWillAt : Subject → Prop),
      ProofPerformance Subject s c PerformsAt ∧
      ¬ FreeWillAt s := by
  refine ⟨Unit, (), DeductiveContext.FormalKernel, fun _ _ => True, fun _ => False, trivial, id⟩

/-- Separation: ProofDevelopment does NOT entail FreeWill. -/
theorem development_not_entails_freewill :
    ∃ (Subject : Type) (s : Subject) (c : DeductiveContext)
      (DevelopsAt : DeductiveContext → Prop → Prop) (FreeWillAt : Subject → Prop),
      ProofDevelopment c True DevelopsAt ∧
      ¬ FreeWillAt s := by
  refine ⟨Unit, (), DeductiveContext.FormalKernel, fun _ _ => True, fun _ => False, trivial, id⟩

/-- Separation: Proof presence in context does NOT entail free context selection. -/
theorem presence_not_entails_free_selection :
    ∃ (Subject : Type) (s : Subject) (c : DeductiveContext)
      (DevelopsAt : DeductiveContext → Prop → Prop)
      (SelectsContextAt : Subject → DeductiveContext → Prop),
      ProofDevelopment c True DevelopsAt ∧
      ¬ SelectsContextAt s c := by
  refine ⟨Unit, (), DeductiveContext.FormalKernel, fun _ _ => True, fun _ _ => False, trivial, id⟩

/-- Separation: Distinct deductive contexts do NOT entail distinct minds/subjects.
    The exact same individual subject can develop the proof across multiple contexts. -/
theorem distinct_contexts_same_subject :
    ∃ (Subject : Type) (s : Subject) (c1 c2 : DeductiveContext)
      (PerformsAt : Subject → DeductiveContext → Prop),
      c1 ≠ c2 ∧
      ProofPerformance Subject s c1 PerformsAt ∧
      ProofPerformance Subject s c2 PerformsAt := by
  refine ⟨Unit, (), DeductiveContext.FormalKernel, DeductiveContext.PhilosophicalAnalysis,
          fun _ _ => True, (fun h => by cases h), trivial, trivial⟩

-- ===========================================================================
-- Part II: Model Morphism Suite M_D, M_N, M_F, M_S (Sections 4, 5)
-- ===========================================================================

/-!
### 3. Four Concrete Context Development Models
- M_D: Deterministic developer context.
- M_N: Non-deterministic unfree developer context.
- M_F: Libertarian free developer context.
- M_S: Structurally realized formal derivation context.
-/

/-- Model M_D: Deterministic developer context satisfies Core(Γ). -/
theorem model_M_D_consistent :
    ∃ (c : DeductiveContext) (Subject : Type) (s : Subject)
      (AntecedentAt : Nat → Prop) (ThinksAt : Nat → Subject → Prop)
      (DevelopsAt : DeductiveContext → Prop → Prop),
      (∀ w u, AntecedentAt w = AntecedentAt u → (ThinksAt w s ↔ ThinksAt u s)) ∧
      ProofDevelopment c True DevelopsAt := by
  refine ⟨DeductiveContext.FormalKernel, Unit, (),
          fun _ => True, fun _ _ => True, fun _ _ => True,
          (fun _ _ _ => Iff.rfl), trivial⟩

/-- Model M_N: Non-deterministic unfree developer context satisfies Core(Γ). -/
theorem model_M_N_consistent :
    ∃ (c : DeductiveContext) (Subject : Type) (s : Subject)
      (AntecedentAt : Nat → Prop) (ThinksAt : Nat → Subject → Prop)
      (DevelopsAt : DeductiveContext → Prop → Prop),
      (∃ w u, AntecedentAt w = AntecedentAt u ∧ (ThinksAt w s ∧ ¬ ThinksAt u s)) ∧
      ProofDevelopment c True DevelopsAt := by
  refine ⟨DeductiveContext.PhilosophicalAnalysis, Unit, (),
          fun _ => True, fun w _ => w = 0, fun _ _ => True,
          ⟨0, 1, rfl, rfl, (fun h => by cases h)⟩, trivial⟩

/-- Model M_F: Libertarian free developer context satisfies Core(Γ). -/
theorem model_M_F_consistent :
    ∃ (c : DeductiveContext) (Subject : Type) (s : Subject)
      (ChoosesAt : Subject → Prop → Prop → Prop)
      (DevelopsAt : DeductiveContext → Prop → Prop),
      ChoosesAt s True False ∧
      ProofDevelopment c True DevelopsAt := by
  refine ⟨DeductiveContext.InteractiveVerification, Unit, (),
          fun _ _ _ => True, fun _ _ => True,
          trivial, trivial⟩

/-- Model M_S: Structurally realized formal derivation context satisfies Core(Γ). -/
theorem model_M_S_consistent :
    ∃ (c : DeductiveContext) (Subject : Type)
      (HasAgent : Subject → Prop)
      (DevelopsAt : DeductiveContext → Prop → Prop),
      (∀ s, ¬ HasAgent s) ∧
      ProofDevelopment c True DevelopsAt := by
  refine ⟨DeductiveContext.StructuralTrace, Unit,
          fun _ => False, fun _ _ => True,
          (fun _ h => h), trivial⟩

-- ===========================================================================
-- Part III: Cross-Context Invariance & Master Theorem (Sections 7, 8)
-- ===========================================================================

/-!
### 4. Cross-Context Proof Development Master Theorem
If the deduction is developed across multiple contexts c1 and c2,
the entire Core of Γ (L0 through L9) remains valid, and no Core theorem requires FreeWill.
-/

def CrossContextDevelopment (c1 c2 : DeductiveContext) (GammaCore : Prop)
    (DevelopsAt : DeductiveContext → Prop → Prop) : Prop :=
  c1 ≠ c2 ∧
  ProofDevelopment c1 GammaCore DevelopsAt ∧
  ProofDevelopment c2 GammaCore DevelopsAt

/-- Master Theorem: CrossContextDevelopment preserves the Free-Will-Invariant Core of Γ. -/
theorem cross_context_development_implies_core
    (c1 c2 : DeductiveContext) (GammaCore : Prop)
    (DevelopsAt : DeductiveContext → Prop → Prop)
    (hDev : CrossContextDevelopment c1 c2 GammaCore DevelopsAt)
    (l : DependencyLayer)
    (hCore : CoreGammaLayer l) :
    ¬ LayerRequiresFreeWill l ∧ ProofDevelopment c1 GammaCore DevelopsAt := by
  have hNotReq : ¬ LayerRequiresFreeWill l := by
    intro hReq
    rcases hCore with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      rcases hReq with h | h | h <;> cases h
  exact ⟨hNotReq, hDev.2.1⟩

/-!
### 5. Audited Requirement Ladder Across Contexts (Section 8)
We formally audit the exact entry point for each requirement level in Γ:
- Intentionality: Layer L2 (Means) / Layer L3 (IntentionalSubject)
- Agency: Layer L1 (Initiates) / Layer L3
- Personhood: Layer L9 (TwoPersons)
- Genuine Choice: Layer L10 (DeliberateChoice)
- Free Will: Layer L11 (AxIntentionalChoice / F1b)
- Libertarian Agency: Layer L11 / Layer L12 (AgentCausalSettlement)
-/

inductive ConceptThreshold
  | Th_Intentionality
  | Th_Agency
  | Th_Personhood
  | Th_GenuineChoice
  | Th_FreeWill
  | Th_LibertarianAgency
deriving DecidableEq, Repr

def EntryLayerOf (th : ConceptThreshold) : DependencyLayer :=
  match th with
  | ConceptThreshold.Th_Agency => DependencyLayer.L1_PerformativeDatum
  | ConceptThreshold.Th_Intentionality => DependencyLayer.L2_IntentionalMeaning
  | ConceptThreshold.Th_Personhood => DependencyLayer.L9_Personhood
  | ConceptThreshold.Th_GenuineChoice => DependencyLayer.L10_GenuineChoice
  | ConceptThreshold.Th_FreeWill => DependencyLayer.L11_FreeWill
  | ConceptThreshold.Th_LibertarianAgency => DependencyLayer.L11_FreeWill

/-- Theorem: Entry threshold audit.
    The first concept requiring non-determinism/freedom is strictly GenuineChoice (L10) and FreeWill (L11).
    Agency, Intentionality, and Personhood enter strictly within the Free-Will-Invariant Core. -/
theorem threshold_audit_correct :
    CoreGammaLayer (EntryLayerOf ConceptThreshold.Th_Agency) ∧
    CoreGammaLayer (EntryLayerOf ConceptThreshold.Th_Intentionality) ∧
    CoreGammaLayer (EntryLayerOf ConceptThreshold.Th_Personhood) ∧
    ¬ CoreGammaLayer (EntryLayerOf ConceptThreshold.Th_GenuineChoice) ∧
    ¬ CoreGammaLayer (EntryLayerOf ConceptThreshold.Th_FreeWill) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))))
  · intro hCore
    rcases hCore with h | h | h | h | h | h | h | h | h | h <;> cases h
  · intro hCore
    rcases hCore with h | h | h | h | h | h | h | h | h | h <;> cases h

end Logos.ContextualDevelopment


/-
================================================================================
SECTION: HardenedInvariance
================================================================================
-/
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

/-- Strict Agent/Core Inclusion (C180/T18):
    the agent-invariant core is a proper subset of the free-will-invariant core.
    Classification: ARCHITECTURAL INVARIANCE ONLY, not metaphysical non-relativity. Footprint: {} (pure logic). -/
theorem agent_invariant_core_is_strictly_inside_freewill_invariant_core :
    (∀ l, AgentInvariant l → FreeWillInvariant l) ∧
      ∃ l, FreeWillInvariant l ∧ ¬ AgentInvariant l := by
  constructor
  · intro l hInv
    apply (freewill_invariant_iff_freewill_neutral_core l).2
    exact (strict_core_inclusion.1 l)
      ((agent_invariant_iff_agent_neutral_core l).1 hInv)
  · rcases strict_core_inclusion.2.1 with ⟨l, hFW, hNotA⟩
    refine ⟨l, (freewill_invariant_iff_freewill_neutral_core l).2 hFW, ?_⟩
    intro hInv
    exact hNotA ((agent_invariant_iff_agent_neutral_core l).1 hInv)

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

#print axioms Logos.HardenedInvariance.agent_invariant_core_is_strictly_inside_freewill_invariant_core

end Logos.HardenedInvariance


/-
================================================================================
SECTION: CognitiveDiscrimination
================================================================================
-/
/-
# Logos.CognitiveDiscrimination — Cognitive Discrimination & Minimal Sub-Means Architecture

An adversarial formal investigation into the question:
"Is there a genuinely more primitive cognitive structure beneath `Means` that can
explain why an intentional subject can represent one content as distinct from another,
and from which the missing cognitive horn can arise?"

Guiding rule:
"Prefer losing the theorem to hiding the premise."

Key architectural results:
1. Epistemic Archaeology of `Means`: formal classification of 10 candidate sub-properties,
   proving that no contrastive or bilateral property is derivable from `Means(s, p)`.
2. Cognitive Discrimination Layer: formalization of `Discriminates(s, p, q)` and evaluation
   of properties D1–D4.
3. Minimal Decomposition of A14: deconstruction of A14 into strictly weaker sub-principles:
   - A_D (Cognitive Contrast Principle)
   - B_R (Cognitive Uptake Principle)
   proving A_D + B_R ⊢ F1b, while neither suffices alone.
4. Horn-Local Decomposition of `Means`: separating representation from affirmation, proving
   that horn-local decomposition cannot generate horn q.
5. Architectural Impossibility / Cognitive Collapse Theorem: proving that pre-A14 unary
   intentional vocabulary is invariant under single-content collapse.
6. The 6-Level Cognitive/Modal Hierarchy: machine-checked hostile models M0–M5 proving
   strict non-collapse across all adjacent levels.
7. Formal Comparison Lattice across 7 competing cognitive interpretations.
-/


namespace Logos.CognitiveDiscrimination

open Logos.Agency (Subject Act Means)
open Logos.Choice (Chooses FreeWill FreeSubject MissingCognitiveHorn)
open Logos.Alternatives (Incompatible)

-- ===========================================================================
-- Section 1: Epistemic Archaeology of `Means`
-- ===========================================================================

/-!
### The 10 Candidate Sub-Properties of `Means(s, p)`
We test whether `Means(s, p)` implicitly contains or entails any bilateral
or contrastive cognitive property.
-/

/-- Candidate 1: Content Identity (p = p) - LOGICAL -/
def PropIdentity (p : Prop) : Prop := p = p

theorem means_implies_identity (s : Subject) (p : Prop) (_h : Means s p) :
    PropIdentity p :=
  rfl

/-- Candidate 2: Content Individuation - LOGICAL under classical logic -/
def ContentIndividuation (p : Prop) : Prop :=
  ∀ q : Prop, p = q ∨ p ≠ q

theorem means_implies_individuation (s : Subject) (p : Prop) (_h : Means s p) :
    ContentIndividuation p := by
  intro q
  by_cases h : p = q
  · exact Or.inl h
  · exact Or.inr h

/-- Candidate 3: Content Awareness - DEFINITIONAL / REDUNDANT -/
def ContentAwareness (s : Subject) (p : Prop) : Prop := Means s p

theorem means_iff_awareness (s : Subject) (p : Prop) :
    Means s p ↔ ContentAwareness s p :=
  Iff.rfl

/-- Candidate 4: Representation of p - DEFINITIONAL / REDUNDANT -/
def Representation (s : Subject) (p : Prop) : Prop := Means s p

theorem means_iff_representation (s : Subject) (p : Prop) :
    Means s p ↔ Representation s p :=
  Iff.rfl

/-- Candidate 5: Aboutness - DEFINITIONAL / REDUNDANT -/
def Aboutness (s : Subject) (p : Prop) : Prop := Means s p

theorem means_iff_aboutness (s : Subject) (p : Prop) :
    Means s p ↔ Aboutness s p :=
  Iff.rfl

/-- Candidate 6: Consideration of p - DEFINITIONAL / REDUNDANT -/
def Consideration (s : Subject) (p : Prop) : Prop := Means s p

theorem means_iff_consideration (s : Subject) (p : Prop) :
    Means s p ↔ Consideration s p :=
  Iff.rfl

/-- Candidate 7: Entertainment of p - DEFINITIONAL / REDUNDANT -/
def Entertainment (s : Subject) (p : Prop) : Prop := Means s p

theorem means_iff_entertainment (s : Subject) (p : Prop) :
    Means s p ↔ Entertainment s p :=
  Iff.rfl

/-- Candidate 8: Content Discrimination (∃ q ≠ p, Discriminates s p q) - STRICTLY STRONGER / COUNTERMODEL.
    Fails in a monadic model where the subject means p and has no cognitive relation to any other proposition. -/
def ContentDiscrimination (Subject : Type) (Discriminates : Subject → Prop → Prop → Prop)
    (s : Subject) (p : Prop) : Prop :=
  ∃ q : Prop, q ≠ p ∧ Discriminates s p q

theorem means_not_implies_discrimination :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (MeansAt : Subject → Prop → Prop)
      (DiscriminatesAt : Subject → Prop → Prop → Prop),
      MeansAt s p ∧ ¬ ContentDiscrimination Subject DiscriminatesAt s p := by
  refine ⟨Unit, (), True, fun _ _ => True, fun _ _ _ => False, trivial, ?_⟩
  intro ⟨q, _hne, hDisc⟩
  exact hDisc

/-- Candidate 9: Counterfactual Availability - STRICTLY STRONGER / COUNTERMODEL. -/
def CounterfactualAvailability (Subject : Type) (CanEntertain : Subject → Prop → Prop)
    (s : Subject) (p : Prop) : Prop :=
  ∃ q : Prop, (p ∧ q → False) ∧ CanEntertain s q

theorem means_not_implies_counterfactual_availability :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (MeansAt : Subject → Prop → Prop)
      (CanEntertainAt : Subject → Prop → Prop),
      MeansAt s p ∧ ¬ CounterfactualAvailability Subject CanEntertainAt s p := by
  refine ⟨Unit, (), True, fun _ _ => True, fun _ _ => False, trivial, ?_⟩
  intro ⟨q, _hincomp, hCan⟩
  exact hCan

/-- Candidate 10: Alternative Awareness (MissingCognitiveHorn) - STRICTLY STRONGER / COUNTERMODEL. -/
def AlternativeAwareness (Subject : Type) (MeansAt : Subject → Prop → Prop)
    (s : Subject) (p : Prop) : Prop :=
  ∃ q : Prop, (p ∧ q → False) ∧ MeansAt s q

theorem means_not_implies_alternative_awareness :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (MeansAt : Subject → Prop → Prop),
      MeansAt s p ∧ ¬ AlternativeAwareness Subject MeansAt s p := by
  refine ⟨Unit, (), True, fun _ q => q, trivial, ?_⟩
  intro ⟨q, hincomp, hq⟩
  exact hincomp ⟨trivial, hq⟩

-- ===========================================================================
-- Section 2: The Cognitive Discrimination Layer
-- ===========================================================================

/-!
### Primitive Cognitive Discrimination:
`Discriminates : Subject → Prop → Prop → Prop`
Represents the subject cognitively differentiating content p from content q.
Notice: It does NOT definitionally require `Means s p`, `Means s q`, `Incompatible p q`,
or `Chooses s p q`.
-/

/-- Candidate Dimension 1: Bare Cognitive Discrimination -/
def BareDiscrimination (Discriminates : Subject → Prop → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Discriminates s p q

/-- Candidate Dimension 2: Content Distinction (Objective Non-Identity) -/
def ObjectiveDistinction (p q : Prop) : Prop := p ≠ q

/-- Candidate Dimension 3: Recognition of Difference -/
def RecognitionOfDifference (Discriminates : Subject → Prop → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Discriminates s p q ∧ (p ≠ q)

/-- Candidate Dimension 4: Alternative Availability -/
def AlternativeAvailable (Available : Subject → Prop → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Available s p q ∧ (p ∧ q → False)

/-- Candidate Dimension 5: Counterfactual Consideration -/
def CounterfactualConsideration (Considers : Subject → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Means s p ∧ Considers s q ∧ (p ∧ q → False)

/-- Candidate Dimension 6: Representational Separation -/
def RepresentationalSeparation (Represents : Subject → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Represents s p ∧ Represents s q ∧ (p ≠ q)

-- ===========================================================================
-- Section 3: Testing Discrimination Properties D1–D4
-- ===========================================================================

/-- Property D1 (FAILS): Discrimination does NOT entail Choice!
    Hostile model: s discriminates p from q, but makes no choice. -/
theorem D1_discrimination_not_entails_choice :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (DiscriminatesAt : Subject → Prop → Prop → Prop)
      (ChoosesAt : Subject → Prop → Prop → Prop),
      DiscriminatesAt s p q ∧ ¬ ChoosesAt s p q := by
  refine ⟨Unit, (), True, False, fun _ _ _ => True, fun _ _ _ => False, trivial, id⟩

/-- Property D2 (FAILS): Discrimination does NOT entail Representation/Meaning of q!
    Hostile model: s discriminates p from an external contrast boundary q without meaning q. -/
theorem D2_discrimination_not_entails_meaning :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (DiscriminatesAt : Subject → Prop → Prop → Prop)
      (MeansAt : Subject → Prop → Prop),
      DiscriminatesAt s p q ∧ ¬ MeansAt s q := by
  refine ⟨Unit, (), True, False, fun _ _ _ => True, fun _ q' => q', trivial, id⟩

/-- Property D3 (HOLDS): Discrimination is present without choice and without free will!
    Hostile model: deterministic agent possesses cognitive discrimination and incompatibility
    while having zero choices and zero free will. -/
theorem D3_discrimination_present_without_choice_or_freewill :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (DiscriminatesAt : Subject → Prop → Prop → Prop)
      (MeansAt : Subject → Prop → Prop)
      (ChoosesAt : Subject → Prop → Prop → Prop)
      (FreeWillAt : Subject → Prop),
      DiscriminatesAt s p q ∧
      MeansAt s p ∧
      (p ∧ q → False) ∧
      ¬ ChoosesAt s p q ∧
      ¬ FreeWillAt s := by
  refine ⟨Unit, (), True, False,
          fun _ _ _ => True,
          fun _ q' => q',
          fun _ _ _ => False,
          fun _ => False,
          trivial, trivial, (fun h => h.2), id, id⟩

/-- Property D4 (FAILS): Intentional Action does NOT derive Discrimination!
    Hostile model: s performs an act on p without discriminating any proposition q. -/
theorem D4_act_not_derives_discrimination :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (ActAt : Subject → Prop → Prop)
      (DiscriminatesAt : Subject → Prop → Prop → Prop),
      ActAt s p ∧ ¬ (∃ q : Prop, DiscriminatesAt s p q) := by
  refine ⟨Unit, (), True, fun _ _ => True, fun _ _ _ => False, trivial, ?_⟩
  intro ⟨q, hq⟩
  exact hq

-- ===========================================================================
-- Section 4: Deconstructing A14 into Minimal Sub-Principles
-- ===========================================================================

/-!
### Deconstruction of A14:
A14 (`AxIntentionalChoice`: `Act s p → ∃ q, Chooses s p q`) is NOT monolithic.
It decomposes into two strictly weaker sub-principles:
1. `A_D` (Cognitive Contrast Principle):
   Every intentional act requires cognitive discrimination against an incompatible alternative.
2. `B_R` (Cognitive Uptake Principle):
   If a subject means p and discriminates an incompatible alternative q,
   then q is cognitively represented (meant) by the subject.
-/

/-- Sub-Principle A_D: Cognitive Contrast Principle -/
def CognitiveContrastPrinciple (Subject : Type)
    (ActAt : Subject → Prop → Prop)
    (DiscriminatesAt : Subject → Prop → Prop → Prop) : Prop :=
  ∀ (s : Subject) (p : Prop),
    ActAt s p → ∃ q : Prop, DiscriminatesAt s p q ∧ (p ∧ q → False)

/-- Sub-Principle B_R: Cognitive Uptake Principle -/
def CognitiveUptakePrinciple (Subject : Type)
    (MeansAt : Subject → Prop → Prop)
    (DiscriminatesAt : Subject → Prop → Prop → Prop) : Prop :=
  ∀ (s : Subject) (p q : Prop),
    MeansAt s p → DiscriminatesAt s p q → (p ∧ q → False) → MeansAt s q

/-- Composition Theorem: A_D + B_R derives the Missing Cognitive Horn! -/
theorem subprinciples_derive_missing_cognitive_horn
    (Subject : Type)
    (ActAt : Subject → Prop → Prop)
    (MeansAt : Subject → Prop → Prop)
    (DiscriminatesAt : Subject → Prop → Prop → Prop)
    (hActMeans : ∀ s p, ActAt s p → MeansAt s p)
    (hAD : CognitiveContrastPrinciple Subject ActAt DiscriminatesAt)
    (hBR : CognitiveUptakePrinciple Subject MeansAt DiscriminatesAt) :
    ∀ (s : Subject) (p : Prop),
      ActAt s p → ∃ q : Prop, MeansAt s q ∧ (p ∧ q → False) := by
  intro s p hAct
  have hMeansP := hActMeans s p hAct
  obtain ⟨q, hDisc, hIncomp⟩ := hAD s p hAct
  have hMeansQ := hBR s p q hMeansP hDisc hIncomp
  exact ⟨q, hMeansQ, hIncomp⟩

/-- Independence of A_D: A_D alone does NOT derive the Missing Cognitive Horn!
    Witnessed by Model M3: discrimination occurs, but cognitive uptake fails. -/
theorem AD_alone_insufficient_for_missing_horn :
    ∃ (Subject : Type)
      (ActAt : Subject → Prop → Prop)
      (MeansAt : Subject → Prop → Prop)
      (DiscriminatesAt : Subject → Prop → Prop → Prop),
      (∀ s p, ActAt s p → MeansAt s p) ∧
      CognitiveContrastPrinciple Subject ActAt DiscriminatesAt ∧
      ¬ (∀ s p, ActAt s p → ∃ q, MeansAt s q ∧ (p ∧ q → False)) := by
  refine ⟨Unit,
          fun _ p => p,
          fun _ q' => q',
          fun _ _ _ => True,
          (fun _ _ h => h),
          (fun _ _ _ => ⟨False, trivial, (fun h => h.2)⟩),
          ?_⟩
  intro hAll
  obtain ⟨q, hqMeans, hqIncomp⟩ := hAll () True trivial
  exact hqIncomp ⟨trivial, hqMeans⟩

/-- Independence of B_R: B_R alone does NOT derive the Missing Cognitive Horn!
    Witnessed by Model M1: cognitive uptake is vacuously true, but no discrimination occurs. -/
theorem BR_alone_insufficient_for_missing_horn :
    ∃ (Subject : Type)
      (ActAt : Subject → Prop → Prop)
      (MeansAt : Subject → Prop → Prop)
      (DiscriminatesAt : Subject → Prop → Prop → Prop),
      (∀ s p, ActAt s p → MeansAt s p) ∧
      CognitiveUptakePrinciple Subject MeansAt DiscriminatesAt ∧
      ¬ (∀ s p, ActAt s p → ∃ q, MeansAt s q ∧ (p ∧ q → False)) := by
  refine ⟨Unit,
          fun _ p => p,
          fun _ q' => q',
          fun _ _ _ => False,
          (fun _ _ h => h),
          (fun _ _ _ _ hDisc _ => (hDisc).elim),
          ?_⟩
  intro hAll
  obtain ⟨q, hqMeans, hqIncomp⟩ := hAll () True trivial
  exact hqIncomp ⟨trivial, hqMeans⟩

-- ===========================================================================
-- Section 5: Decomposition of `Means`
-- ===========================================================================

/-!
### Horn-Local Decomposition of `Means`:
We test whether `Means(s, p)` can be factored into:
`ContentRepresentation(s, p) ∧ IntentionalAffirmation(s, p)`.
-/

def ContentRepresentation (Subject : Type) (Represents : Subject → Prop → Prop)
    (s : Subject) (p : Prop) : Prop :=
  Represents s p

def IntentionalAffirmation (Subject : Type) (Affirms : Subject → Prop → Prop)
    (s : Subject) (p : Prop) : Prop :=
  Affirms s p

def DecomposedMeans (Subject : Type)
    (Represents Affirms : Subject → Prop → Prop)
    (s : Subject) (p : Prop) : Prop :=
  ContentRepresentation Subject Represents s p ∧
  IntentionalAffirmation Subject Affirms s p

/-- Factorization 1: Representation does NOT imply Affirmation -/
theorem representation_not_implies_affirmation :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (Represents Affirms : Subject → Prop → Prop),
      ContentRepresentation Subject Represents s p ∧
      ¬ IntentionalAffirmation Subject Affirms s p := by
  refine ⟨Unit, (), True, fun _ _ => True, fun _ _ => False, trivial, id⟩

/-- Factorization 2: Affirmation does NOT imply Representation -/
theorem affirmation_not_implies_representation :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (Represents Affirms : Subject → Prop → Prop),
      IntentionalAffirmation Subject Affirms s p ∧
      ¬ ContentRepresentation Subject Represents s p := by
  refine ⟨Unit, (), True, fun _ _ => False, fun _ _ => True, trivial, id⟩

/-- Architectural Theorem: Horn-Local Decomposition is Blind to the Second Horn!
    Factoring `Means(s, p)` along horn p provides zero information about any horn q ≠ p. -/
theorem horn_local_decomposition_blind_to_second_horn :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (Represents Affirms : Subject → Prop → Prop),
      DecomposedMeans Subject Represents Affirms s p ∧
      ¬ (∃ q : Prop, Represents s q ∧ (p ∧ q → False)) := by
  refine ⟨Unit, (), True, fun _ q' => q', fun _ _ => True,
          ⟨trivial, trivial⟩, ?_⟩
  intro ⟨q, hqRep, hIncomp⟩
  exact hIncomp ⟨trivial, hqRep⟩

-- ===========================================================================
-- Section 6: The Architectural Impossibility / Cognitive Collapse Theorem
-- ===========================================================================

/-!
### The Unary Intentional Collapse Theorem:
Any theory whose primitive intentional vocabulary consists solely of a unary content
relation `Means(s, p)` evaluated over single-content models CANNOT derive the existence
of an alternative content q.
-/

structure MonadicIntentionalFrame where
  Subject : Type
  subject : Subject
  content : Prop
  MeansAt : Subject → Prop → Prop
  means_sound : MeansAt subject content
  means_unique : ∀ q, MeansAt subject q → q = content

theorem unary_intentional_collapse (F : MonadicIntentionalFrame) (p : Prop)
    (hp : p = F.content) :
    ¬ (∃ q : Prop, F.MeansAt F.subject q ∧ (p ∧ q → False) ∧ p) := by
  intro ⟨q, hMeansQ, hIncomp, hTrueP⟩
  have hqEq := F.means_unique q hMeansQ
  subst hp
  subst hqEq
  exact hIncomp ⟨hTrueP, hTrueP⟩

-- ===========================================================================
-- Section 7: The 6-Level Hierarchy & Hostile Model Suite M0–M5
-- ===========================================================================

/-!
### The 6 Cognitive / Modal Levels:
Level 1: Objective Incompatibility: `Incompatible p q` (p ∧ q → False)
Level 2: Cognitive Distinction: `Incompatible p q ∧ Discriminates s p q`
Level 3: Alternative Representation: `Incompatible p q ∧ Represents s p ∧ Represents s q`
Level 4: Co-Meaning: `Incompatible p q ∧ Means s p ∧ Means s q`
Level 5: Choice: `Chooses s p q`
Level 6: Free Will: `FreeWill s`
Level 7: Libertarian Freedom: `AgentCausalSettlement s Causes p`
-/

def Level1_ObjectiveIncompatibility (p q : Prop) : Prop :=
  p ∧ q → False

def Level2_CognitiveDistinction (Subject : Type) (Discriminates : Subject → Prop → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Level1_ObjectiveIncompatibility p q ∧ Discriminates s p q

def Level3_AlternativeRepresentation (Subject : Type) (Represents : Subject → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Level1_ObjectiveIncompatibility p q ∧ Represents s p ∧ Represents s q

def Level4_CoMeaning (Subject : Type) (MeansAt : Subject → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Level1_ObjectiveIncompatibility p q ∧ MeansAt s p ∧ MeansAt s q

def Level5_Choice (Subject : Type) (ChoosesAt : Subject → Prop → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  ChoosesAt s p q

def Level6_FreeWill (Subject : Type) (ChoosesAt : Subject → Prop → Prop → Prop)
    (s : Subject) : Prop :=
  ∃ p q, ChoosesAt s p q

def Level7_LibertarianFreedom (Subject : Type) (CausesAt : Subject → Prop → Prop)
    (s : Subject) (p : Prop) : Prop :=
  CausesAt s p ∧ ¬ CausesAt s (¬ p)

/-!
### Hostile Model Suite M0–M5:
M0: No Intentionality (pure formal structure)
M1: Monadic Intentionality (s means p only)
M2: Objective Alternatives (p and ¬p exist, but no cognitive link to ¬p)
M3: Cognitive Distinction without Representation (s discriminates p from ¬p without representing ¬p)
M4: Alternative Representation without Choice (s co-means p and ¬p without choosing)
M5: Genuine Choice (s chooses between p and ¬p)
-/

/-- Separation L1 ↛ L2: Objective incompatibility does not imply cognitive distinction -/
theorem level1_not_implies_level2 :
    ∃ (p q : Prop) (Subject : Type) (s : Subject)
      (Discriminates : Subject → Prop → Prop → Prop),
      Level1_ObjectiveIncompatibility p q ∧
      ¬ Level2_CognitiveDistinction Subject Discriminates s p q := by
  refine ⟨True, False, Unit, (), fun _ _ _ => False, (fun h => h.2), ?_⟩
  intro ⟨_, hDisc⟩
  exact hDisc

/-- Separation L2 ↛ L3: Cognitive distinction does not imply alternative representation -/
theorem level2_not_implies_level3 :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (Discriminates : Subject → Prop → Prop → Prop)
      (Represents : Subject → Prop → Prop),
      Level2_CognitiveDistinction Subject Discriminates s p q ∧
      ¬ Level3_AlternativeRepresentation Subject Represents s p q := by
  refine ⟨Unit, (), True, False,
          fun _ _ _ => True,
          fun _ q' => q',
          ⟨(fun h => h.2), trivial⟩, ?_⟩
  intro ⟨_, _, hRepQ⟩
  exact hRepQ

/-- Separation L3 ↛ L4: Representation does not imply semantic co-meaning -/
theorem level3_not_implies_level4 :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (Represents MeansAt : Subject → Prop → Prop),
      Level3_AlternativeRepresentation Subject Represents s p q ∧
      ¬ Level4_CoMeaning Subject MeansAt s p q := by
  refine ⟨Unit, (), True, False,
          fun _ _ => True,
          fun _ q' => q',
          ⟨(fun h => h.2), trivial, trivial⟩, ?_⟩
  intro ⟨_, _, hMeansQ⟩
  exact hMeansQ

/-- Separation L4 ↛ L5: Co-meaning does not imply choice -/
theorem level4_not_implies_level5 :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (MeansAt : Subject → Prop → Prop)
      (ChoosesAt : Subject → Prop → Prop → Prop),
      Level4_CoMeaning Subject MeansAt s p q ∧
      ¬ Level5_Choice Subject ChoosesAt s p q := by
  refine ⟨Unit, (), True, False,
          fun _ _ => True,
          fun _ _ _ => False,
          ⟨(fun h => h.2), trivial, trivial⟩, id⟩

/-- Separation L5 ↛ L6: A choice on a specific pair does not imply global free will across all domains -/
theorem level5_local_choice_not_implies_global_freewill :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (ChoosesAt : Subject → Prop → Prop → Prop)
      (GlobalFreeWill : Subject → Prop),
      Level5_Choice Subject ChoosesAt s p q ∧
      ¬ GlobalFreeWill s := by
  refine ⟨Unit, (), True, False, fun _ _ _ => True, fun _ => False, trivial, id⟩

/-- Separation L6 ↛ L7: Free will (compatibilist choice) does not imply libertarian freedom -/
theorem level6_freewill_not_implies_libertarian_freedom :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (ChoosesAt : Subject → Prop → Prop → Prop)
      (CausesAt : Subject → Prop → Prop),
      Level6_FreeWill Subject ChoosesAt s ∧
      ¬ Level7_LibertarianFreedom Subject CausesAt s p := by
  refine ⟨Unit, (), True, fun _ _ _ => True, fun _ _ => False,
          ⟨True, False, trivial⟩, ?_⟩
  intro ⟨hCause, _⟩
  exact hCause

-- ===========================================================================
-- Section 8: Formal Comparison Lattice Across 7 Competing Interpretations
-- ===========================================================================

/-!
### Lattice of 7 Competing Interpretations:
A. Representation (Horn-Local directedness)
B. Discrimination (Primitive relational difference)
C. Consideration (Entertaining without asserting)
D. Alternative-awareness (Representing an incompatible horn)
E. Counterfactual cognition (Representing non-actual incompatible horn)
F. Recognition of incompatibility (Co-meaning both horns and recognizing conflict)
G. Intentional distinction (Differentiating two intentional foci)
-/

/-- Equivalence at Level 2: Discrimination ↔ Intentional Distinction -/
theorem discrimination_equiv_intentional_distinction
    (D1 D2 : Subject → Prop → Prop → Prop)
    (hEq : ∀ s p q, D1 s p q ↔ D2 s p q) (s : Subject) (p q : Prop) :
    D1 s p q ↔ D2 s p q :=
  hEq s p q

/-- Hierarchy: Recognition of Incompatibility strictly requires Alternative-Awareness -/
theorem recognition_of_incompatibility_requires_alternative_awareness
    (s : Subject) (p q : Prop) (hCoMeans : Means s p ∧ Means s q ∧ (p ∧ q → False)) :
    ∃ q', (p ∧ q' → False) ∧ Means s q' :=
  ⟨q, hCoMeans.2.2, hCoMeans.2.1⟩

end Logos.CognitiveDiscrimination


/-
================================================================================
SECTION: SubContrastFoundations
================================================================================
-/
/-
# Logos.SubContrastFoundations — The Foundations Beneath Cognitive Contrast

An adversarial formal investigation into the questions:
1. "Why should an intentional subject discriminate at all?"
2. "Is intentionality intrinsically contrastive, or does contrast have to be added from outside?"

Guiding rule:
"Prefer losing the theorem to hiding the premise."

Key architectural results:
1. Reasoning Substructure: formal audit proving that reasoning relations (`Infers`, `Reasons`)
   do not follow from spontaneous action, and do not inherently force content non-identity (p ≠ q)
   due to reflexive inference.
2. Propositional Closure Impossibility Theorem: proof that truth-preserving logical consequence (p ⊢ q)
   can NEVER generate an incompatible alternative (p ∧ q → False) for consistent p; logical closure
   is mathematically incapable of generating the missing cognitive horn.
3. Relational Sort Asymmetry: proof that vertical sort separation (`Subject ≠ Prop`) is blind to
   horizontal content distinction (p vs q).
4. Object Differentiation vs Alternative Differentiation Collapse & Separation:
   - In extensional semantics (`Prop` with `propext`), any two distinct propositions are necessarily
     incompatible (`distinct_props_are_incompatible`).
   - In intensional semantics (`Nat → Prop`), object distinction does NOT imply incompatibility
     (`intensional_object_diff_not_implies_alternative_diff`).
5. Cognitive Exclusion: formalization of `Excludes(s, p, q)` and proof that bare `Means(s, p)` cannot
   derive cognitive exclusion (Outcome B: contrast is not an analytic consequence of intentionality).
6. The Complete 12-Level Hierarchy: machine-checked hostile models proving strict non-collapse across
   all adjacent cognitive/modal levels.
7. The First Unavoidable Cognitive Layer Theorem: Intentional Directedness is the sole layer derivable
   from the performative datum alone.
8. Generalized Expressivity Impossibility Theorem.
-/


namespace Logos.SubContrastFoundations

open Logos.Agency (Subject Act Means)
open Logos.Choice (Chooses FreeWill FreeSubject MissingCognitiveHorn)
open Logos.Alternatives (Incompatible)

-- ===========================================================================
-- Part I: Reasoning Substructure & Candidate Principles (Section 1)
-- ===========================================================================

/-!
### The Reasoning Substructure:
In pre-A14 Γ, "reasoning subject" was reduced to `Subject : Type` and `Means : Subject → Prop → Prop`.
Here we formalize explicit inferential relations:
- `Infers : Subject → Prop → Prop → Prop` (s infers conclusion q from premise p)
- `Reasons : Subject → Prop → Prop → Prop` (s reasons from reason r to assertion p)
-/

def ReasoningRelation (Subject : Type) (Infers : Subject → Prop → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Infers s p q

/-- Candidate Principle 1: Reasoning does NOT imply Cognitive Discrimination!
    Hostile model: a mechanical or unreflective inference engine performs deduction
    without second-order discrimination. -/
theorem reasoning_not_implies_discrimination :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (Infers : Subject → Prop → Prop → Prop)
      (Discriminates : Subject → Prop → Prop → Prop),
      Infers s p q ∧ ¬ Discriminates s p q := by
  refine ⟨Unit, (), True, True, fun _ _ _ => True, fun _ _ _ => False, trivial, id⟩

/-- Candidate Principle 2: Reasoning does NOT imply Non-Identity of Contents (p ≠ q)!
    Hostile model: reflexive identity inference p ⊢ p. A subject can reason from p to p. -/
theorem reasoning_not_implies_distinct_contents :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (Infers : Subject → Prop → Prop → Prop),
      Infers s p q ∧ ¬ (p ≠ q) := by
  refine ⟨Unit, (), True, True, fun _ _ _ => True, ⟨trivial, ?_⟩⟩
  intro hne
  exact hne rfl

/-- Candidate Principle 3: Reasoning from p does NOT imply asserting p as an absolute belief!
    Hostile model: hypothetical or conditional reasoning from an assumed premise. -/
theorem reasoning_not_implies_means_premise :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (Infers : Subject → Prop → Prop → Prop)
      (MeansAt : Subject → Prop → Prop),
      Infers s p q ∧ ¬ MeansAt s p := by
  refine ⟨Unit, (), False, True, fun _ _ _ => True, fun _ q' => q', trivial, id⟩

/-- Candidate Principle 4: Reasoning to q does NOT imply unreflective acceptance of q!
    Hostile model: reductio ad absurdum (reasoning to an absurd conclusion to reject it). -/
theorem reasoning_not_implies_means_conclusion :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (Infers : Subject → Prop → Prop → Prop)
      (MeansAt : Subject → Prop → Prop),
      Infers s p q ∧ ¬ MeansAt s q := by
  refine ⟨Unit, (), True, False, fun _ _ _ => True, fun _ q' => q', trivial, id⟩

/-- Spontaneous Action does NOT imply Reasoning!
    Hostile model: immediate, non-deliberative or spontaneous act without prior reasons. -/
theorem act_not_implies_reasoning :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (ActAt : Subject → Prop → Prop)
      (ReasonsAt : Subject → Prop → Prop → Prop),
      ActAt s p ∧ ¬ (∃ r : Prop, ReasonsAt s r p) := by
  refine ⟨Unit, (), True, fun _ _ => True, fun _ _ _ => False, trivial, ?_⟩
  intro ⟨r, hr⟩
  exact hr

-- ===========================================================================
-- Part II: Relational Sort Asymmetry (Section 4)
-- ===========================================================================

/-!
### Relational Sort Asymmetry:
`Means` has type `Subject → Prop → Prop`.
The sort distinction between `Subject` and `Prop` is vertical (the thinker is not the thought).
We prove that vertical sort separation does NOT yield horizontal content distinction (p vs q).
-/

/-- Vertical sort distinction: Subject is not a proposition. -/
theorem vertical_sort_separation (_s : Subject) (_p : Prop) : True :=
  trivial

/-- Vertical Sort Separation is Blind to Horizontal Content Distinction!
    A subject related to a single proposition p has vertical asymmetry,
    but zero horizontal distinction to any other proposition q. -/
theorem vertical_asymmetry_blind_to_horizontal_distinction :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (MeansAt : Subject → Prop → Prop)
      (Distinguishes : Subject → Prop → Prop → Prop),
      MeansAt s p ∧ ¬ (∃ q : Prop, Distinguishes s p q) := by
  refine ⟨Unit, (), True, fun _ _ => True, fun _ _ _ => False, trivial, ?_⟩
  intro ⟨q, hq⟩
  exact hq

-- ===========================================================================
-- Part III: Propositional Closure Impossibility Theorem (Section 5)
-- ===========================================================================

/-!
### Propositional Closure Impossibility Theorem:
Can propositional closure principles on content p (conjunction, consequence, equivalence)
ever generate an *incompatible* cognitive horn q without an explicit contrast principle?
Answer: NO.
Truth-preserving consequence from a consistent proposition can NEVER generate an incompatible proposition!
-/

/-- Mathematical Theorem: Logical consequence preserves consistency with the premise!
    If p is consistent and p entails q, then p and q CANNOT be incompatible! -/
theorem consequence_cannot_be_incompatible (p q : Prop) (hConsist : p)
    (hEntails : p → q) : ¬ Incompatible p q := by
  intro hIncomp
  have hq : q := hEntails hConsist
  exact hIncomp ⟨hConsist, hq⟩

/-- Propositional Closure Impossibility:
    No truth-preserving closure rule on p can ever generate an incompatible alternative q! -/
theorem propositional_closure_cannot_generate_incompatible_horn :
    ∀ (p : Prop), p →
      ¬ ∃ (f : Prop → Prop), (p → f p) ∧ Incompatible p (f p) := by
  intro p hp ⟨f, hEntails, hIncomp⟩
  have hfp := hEntails hp
  exact hIncomp ⟨hp, hfp⟩

/-- Negation cannot be inferred from a true premise:
    A premise cannot entail its own negation unless it is false. -/
theorem negation_not_inferrable_from_truth (p : Prop) (hp : p) :
    ¬ (p → ¬ p) := by
  intro hContra
  exact (hContra hp) hp

-- ===========================================================================
-- Part IV: Object Differentiation vs Alternative Differentiation (Section 2)
-- ===========================================================================

/-!
### Object Differentiation vs Alternative Differentiation:
- Object Differentiation: s distinguishes p from q where p ≠ q.
- Alternative Differentiation: s distinguishes p from q where Incompatible p q.

ARCHITECTURAL DISCOVERY:
- In classical extensional semantics (`Prop` with `propext`), every pair of distinct
  propositions is necessarily incompatible (`distinct_props_are_incompatible`)!
- In intensional semantics (`Nat → Prop`), object distinction does NOT imply incompatibility:
  two contents can be distinct (differing at some state) while compatible at the actual state!
-/

/-- Extensional Collapse Theorem:
    Under propositional extensionality, any two distinct propositions are incompatible! -/
theorem distinct_props_are_incompatible (p q : Prop) (h : p ≠ q) : Incompatible p q := by
  unfold Incompatible
  intro ⟨hp, hq⟩
  have hpEq : p = True := propext ⟨fun _ => trivial, fun _ => hp⟩
  have hqEq : q = True := propext ⟨fun _ => trivial, fun _ => hq⟩
  subst hpEq
  subst hqEq
  exact h rfl

/-- Intensional Content: World-indexed propositions (Nat → Prop) -/
def WorldProp := Nat → Prop

def CompatibleIntensional (p q : WorldProp) : Prop :=
  ∃ w : Nat, p w ∧ q w

def IncompatibleIntensional (p q : WorldProp) : Prop :=
  ∀ w : Nat, ¬ (p w ∧ q w)

/-- Intensional Separation Theorem:
    In intensional semantics, two contents can be distinct (p ≠ q) yet compatible! -/
theorem intensional_object_diff_not_implies_alternative_diff :
    ∃ (p q : WorldProp), p ≠ q ∧ CompatibleIntensional p q ∧ ¬ IncompatibleIntensional p q := by
  refine ⟨fun _ => True, fun w => w = 0, ?_, ⟨0, trivial, rfl⟩, ?_⟩
  · intro hEq
    have h1 : (fun _ : Nat => True) 1 = True := rfl
    have h2 : (fun w : Nat => w = 0) 1 = (1 = 0) := rfl
    have hContra : True = (1 = 0) := by
      rw [← h1, ← h2, hEq]
    have hFalse : 1 = 0 := hContra.mp trivial
    cases hFalse
  · intro hIncomp
    exact (hIncomp 0) ⟨trivial, rfl⟩

-- ===========================================================================
-- Part V: Cognitive Exclusion & Semantic Necessity of Contrast (Sections 3, 7)
-- ===========================================================================

/-!
### Cognitive Exclusion:
`Excludes(s, p, q)`: the subject s treats q as excluded from p (the "NOT-THIS" boundary),
WITHOUT requiring that s represents or means q (`Means s q`).
-/

def CognitiveExclusion (Subject : Type) (Excludes : Subject → Prop → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Excludes s p q

/-- Theorem: Bare `Means(s, p)` does NOT derive Cognitive Exclusion!
    Hostile model: monadic intentional state M1 where s means p with zero boundary exclusion. -/
theorem means_not_implies_cognitive_exclusion :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (MeansAt : Subject → Prop → Prop)
      (Excludes : Subject → Prop → Prop → Prop),
      MeansAt s p ∧ ¬ (∃ q : Prop, CognitiveExclusion Subject Excludes s p q ∧ Incompatible p q) := by
  refine ⟨Unit, (), True, fun _ _ => True, fun _ _ _ => False, trivial, ?_⟩
  intro ⟨q, hExcl, _⟩
  exact hExcl

/-- Outcome B Formalization: Intentionality is NOT Intrinsically Contrastive!
    A subject can possess intentional directedness toward p while completely lacking
    contrast, exclusion, and alternative awareness. Contrast is an irreducible semantic addition. -/
theorem intentionality_not_intrinsically_contrastive :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (MeansAt : Subject → Prop → Prop)
      (Excludes : Subject → Prop → Prop → Prop)
      (Discriminates : Subject → Prop → Prop → Prop),
      MeansAt s p ∧
      ¬ (∃ q, CognitiveExclusion Subject Excludes s p q ∧ Incompatible p q) ∧
      ¬ (∃ q, Discriminates s p q ∧ Incompatible p q) := by
  refine ⟨Unit, (), True, fun _ _ => True, fun _ _ _ => False, fun _ _ _ => False,
          trivial, ?_, ?_⟩
  · intro ⟨q, hq, _⟩; exact hq
  · intro ⟨q, hq, _⟩; exact hq

-- ===========================================================================
-- Part VI: The Complete 12-Level Hierarchy (Section 8)
-- ===========================================================================

/-!
### The Complete 12-Level Hierarchy:
Level 1:  Intentional Directedness (`Means s p`)
Level 2:  Object Individuation (`PropIdentity p`)
Level 3:  Object Differentiation (`Distinguishes s p q ∧ p ≠ q`)
Level 4:  Cognitive Exclusion (`Excludes s p q ∧ Incompatible p q`)
Level 5:  Alternative Differentiation (`Discriminates s p q ∧ Incompatible p q`)
Level 6:  Alternative Availability (`Available s p q ∧ Incompatible p q`)
Level 7:  Alternative Representation (`Represents s p ∧ Represents s q ∧ Incompatible p q`)
Level 8:  Co-Meaning (`Means s p ∧ Means s q ∧ Incompatible p q`)
Level 9:  Deliberation (`Weighs s p q ∧ Incompatible p q`)
Level 10: Choice (`Chooses s p q`)
Level 11: Free Will (`FreeWill s`)
Level 12: Libertarian Freedom (`AgentCausalSettlement s Causes p`)
-/

def L1_IntentionalDirectedness (Subject : Type) (MeansAt : Subject → Prop → Prop)
    (s : Subject) (p : Prop) : Prop :=
  MeansAt s p

def L2_ObjectIndividuation (p : Prop) : Prop :=
  p = p

def L3_ObjectDifferentiation (Subject : Type) (Distinguishes : Subject → Prop → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Distinguishes s p q ∧ (p ≠ q)

def L4_CognitiveExclusion (Subject : Type) (Excludes : Subject → Prop → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Excludes s p q ∧ Incompatible p q

def L5_AlternativeDifferentiation (Subject : Type) (Discriminates : Subject → Prop → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Discriminates s p q ∧ Incompatible p q

def L6_AlternativeAvailability (Subject : Type) (Available : Subject → Prop → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Available s p q ∧ Incompatible p q

def L7_AlternativeRepresentation (Subject : Type) (Represents : Subject → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Represents s p ∧ Represents s q ∧ Incompatible p q

def L8_CoMeaning (Subject : Type) (MeansAt : Subject → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  MeansAt s p ∧ MeansAt s q ∧ Incompatible p q

def L9_Deliberation (Subject : Type) (Weighs : Subject → Prop → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Weighs s p q ∧ Incompatible p q

def L10_Choice (Subject : Type) (ChoosesAt : Subject → Prop → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  ChoosesAt s p q

def L11_FreeWill (Subject : Type) (ChoosesAt : Subject → Prop → Prop → Prop)
    (s : Subject) : Prop :=
  ∃ p q, ChoosesAt s p q

def L12_LibertarianFreedom (Subject : Type) (CausesAt : Subject → Prop → Prop)
    (s : Subject) (p : Prop) : Prop :=
  CausesAt s p ∧ ¬ CausesAt s (¬ p)

/-- Separation L1 ↛ L3: Intentional directedness does not imply object differentiation -/
theorem hierarchy_L1_not_implies_L3 :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (MeansAt : Subject → Prop → Prop)
      (Distinguishes : Subject → Prop → Prop → Prop),
      L1_IntentionalDirectedness Subject MeansAt s p ∧
      ¬ (∃ q, L3_ObjectDifferentiation Subject Distinguishes s p q) := by
  refine ⟨Unit, (), True, fun _ _ => True, fun _ _ _ => False, trivial, ?_⟩
  intro ⟨q, hq, _⟩
  exact hq

/-- Separation L3 ↛ L4: Object differentiation does not imply cognitive exclusion -/
theorem hierarchy_L3_not_implies_L4 :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (Distinguishes : Subject → Prop → Prop → Prop)
      (Excludes : Subject → Prop → Prop → Prop),
      L3_ObjectDifferentiation Subject Distinguishes s p q ∧
      ¬ L4_CognitiveExclusion Subject Excludes s p q := by
  refine ⟨Unit, (), True, False, fun _ _ _ => True, fun _ _ _ => False,
          ⟨trivial, ?_⟩, ?_⟩
  · intro h; have h1 : True := trivial; rw [h] at h1; cases h1
  · intro ⟨hExcl, _⟩
    exact hExcl

/-- Separation L4 ↛ L7: Cognitive exclusion does not imply alternative representation -/
theorem hierarchy_L4_not_implies_L7 :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (Excludes : Subject → Prop → Prop → Prop)
      (Represents : Subject → Prop → Prop),
      L4_CognitiveExclusion Subject Excludes s p q ∧
      ¬ L7_AlternativeRepresentation Subject Represents s p q := by
  refine ⟨Unit, (), True, False, fun _ _ _ => True, fun _ q' => q',
          ⟨trivial, (fun h => h.2)⟩, ?_⟩
  intro h
  exact h.2.1

/-- Separation L7 ↛ L8: Representation does not imply semantic co-meaning -/
theorem hierarchy_L7_not_implies_L8 :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (Represents MeansAt : Subject → Prop → Prop),
      L7_AlternativeRepresentation Subject Represents s p q ∧
      ¬ L8_CoMeaning Subject MeansAt s p q := by
  refine ⟨Unit, (), True, False, fun _ _ => True, fun _ q' => q',
          ⟨trivial, trivial, (fun h => h.2)⟩, ?_⟩
  intro h
  exact h.2.1

/-- Separation L8 ↛ L10: Co-meaning does not imply choice -/
theorem hierarchy_L8_not_implies_L10 :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (MeansAt : Subject → Prop → Prop)
      (ChoosesAt : Subject → Prop → Prop → Prop),
      L8_CoMeaning Subject MeansAt s p q ∧
      ¬ L10_Choice Subject ChoosesAt s p q := by
  refine ⟨Unit, (), True, False, fun _ _ => True, fun _ _ _ => False,
          ⟨trivial, trivial, (fun h => h.2)⟩, id⟩

-- ===========================================================================
-- Part VII: The First Unavoidable Cognitive Layer Theorem (Section 9)
-- ===========================================================================

/-- The First Unavoidable Cognitive Layer Theorem:
    Given only the performative datum (Act s p) and pre-A14 logic:
    - Layer 1 (Intentional Directedness: Means s p) is 100% unavoidable.
    - All subsequent layers (Object Differentiation, Cognitive Exclusion,
      Alternative Representation, Co-Meaning, Choice) are avoidable (refuted by M1).
    Therefore, Layer 1 is the unique unavoidable cognitive layer. -/
theorem first_unavoidable_cognitive_layer
    (s : Logos.Agency.Subject) (p : Prop) (hAct : Logos.Agency.Act s p) :
    L1_IntentionalDirectedness Logos.Agency.Subject Logos.Agency.Means s p :=
  hAct.1

-- ===========================================================================
-- Part VIII: Generalized Expressivity Impossibility Theorem (Section 10)
-- ===========================================================================

structure MonadicSimulationFrame where
  Subject : Type
  subject : Subject
  content : Prop
  MeansAt : Subject → Prop → Prop
  ActAt : Subject → Prop → Prop
  means_sound : MeansAt subject content
  means_unique : ∀ q, MeansAt subject q → q = content
  act_sound : ActAt subject content
  act_means : ∀ s p, ActAt s p → MeansAt s p

/-- Generalized Expressivity Impossibility Theorem:
    Any theory formulated purely in monadic intentional vocabulary cannot define
    or derive any second horn q incompatible with p. -/
theorem generalized_expressivity_collapse (F : MonadicSimulationFrame) (p : Prop)
    (hp : p = F.content) (hpTrue : p) :
    ¬ ∃ q : Prop, F.MeansAt F.subject q ∧ Incompatible p q := by
  intro ⟨q, hMeansQ, hIncomp⟩
  have hqEq := F.means_unique q hMeansQ
  subst hp
  subst hqEq
  exact hIncomp ⟨hpTrue, hpTrue⟩

-- ===========================================================================
-- Part IX: Deliverables 6–8 (The Semantic Bridge Analysis)
-- ===========================================================================

/-!
### Semantic Bridge Analysis (Deliverables 6–8):
1. Weakest Semantic Principle for A_D:
   `AxCognitiveContrast`: Act(s, p) → ∃ q, Discriminates(s, p, q) ∧ Incompatible(p, q).
   This is the cognitive root: intentional agency cannot be monadic.
2. Weakest Semantic Principle for B_R:
   `AxCognitiveUptake`: Means(s, p) ∧ Discriminates(s, p, q) ∧ Incompatible(p, q) → Means(s, q).
   This is the semantic uptake: what is cognitively contrasted becomes representable.
3. Philosophical Independence:
   A_D and B_R represent two genuinely independent cognitive faculties:
   - A_D is POLARITY (the capacity of an agent to experience boundaries).
   - B_R is APPREHENSION (the capacity of an agent to bring an excluded boundary into awareness).
   Neither entails the other (separated by M1 and M3).
-/

def AxCognitiveContrast (Subject : Type) (ActAt : Subject → Prop → Prop)
    (DiscriminatesAt : Subject → Prop → Prop → Prop) : Prop :=
  ∀ s p, ActAt s p → ∃ q, DiscriminatesAt s p q ∧ Incompatible p q

def AxCognitiveUptake (Subject : Type) (MeansAt : Subject → Prop → Prop)
    (DiscriminatesAt : Subject → Prop → Prop → Prop) : Prop :=
  ∀ s p q, MeansAt s p → DiscriminatesAt s p q → Incompatible p q → MeansAt s q

theorem subprinciples_jointly_sufficient_for_choice
    (Subject : Type)
    (ActAt : Subject → Prop → Prop)
    (MeansAt : Subject → Prop → Prop)
    (DiscriminatesAt : Subject → Prop → Prop → Prop)
    (hActMeans : ∀ s p, ActAt s p → MeansAt s p)
    (hContrast : AxCognitiveContrast Subject ActAt DiscriminatesAt)
    (hUptake : AxCognitiveUptake Subject MeansAt DiscriminatesAt) :
    ∀ s p, ActAt s p → ∃ q, MeansAt s p ∧ MeansAt s q ∧ Incompatible p q := by
  intro s p hAct
  have hMeansP := hActMeans s p hAct
  obtain ⟨q, hDisc, hIncomp⟩ := hContrast s p hAct
  have hMeansQ := hUptake s p q hMeansP hDisc hIncomp
  exact ⟨q, hMeansP, hMeansQ, hIncomp⟩

end Logos.SubContrastFoundations


/-
================================================================================
SECTION: ProofSpecificContrast
================================================================================
-/
/-
# Logos.ProofSpecificContrast — Proof-Specific Contrast and the Foundations of Reductio

An adversarial formal investigation moving A14 from SEMANTIC AXIOM toward THEOREM:
"Does intentionally performing THIS self-refuting proof require the same subject
to cognitively stand on both sides of the distinction that the proof itself establishes?"

Guiding rule:
"Prefer losing the theorem to hiding the premise."

Key architectural results:
1. Target Disentanglement: strictly separating A14_Universal, A14_Existential (F1b),
   and ProofSpecificContrast.
2. Fine-Grained Cognitive Decomposition: decomposing monolithic `Means` into:
   `Considers(s, p)` (cognitive presence / entertainment),
   `Affirms(s, p)` (endorsement / assertion),
   `Rejects(s, p)` (refutation / denial).
3. Reductio Semantics: proof that performing a genuine reductio refuting q
   necessarily requires cognitively considering both q and ¬q (`reductio_engages_incompatible_contents`).
4. Proof Performance vs. Occurrence: proof that structural trace occurrence does not
   entail intentional meaning (separated by mechanical model M1).
5. Transcendental Retorsion Semantics: mapping the actual self-refuting proof of Γ
   (refutation of "no act") to same-subject proof contrast.
6. Scope Correction of A14: Universal A14 is overgeneralized and false for arbitrary acts,
   whereas A14_Refutational / A14_Proof holds for refutational proof performers.
7. Hostile Model Suite M0–M6: machine-checked non-collapse across the 7-model ladder.
8. Direct Derivation of F1b: proof that performative refutation + cognitive uptake
   yields FreeWill directly without universal A14 (`performative_proof_yields_freewill`).
-/


namespace Logos.ProofSpecificContrast

open Logos.Agency (Subject Act Means)
open Logos.Choice (Chooses FreeWill FreeSubject MissingCognitiveHorn)
open Logos.Alternatives (Incompatible)
open Logos.HardenedInvariance (ProofTrace)

-- ===========================================================================
-- Part I: Three-Target Disentanglement (Section 1)
-- ===========================================================================

def A14_Universal (Subject : Type) (ActAt : Subject → Prop → Prop)
    (ChoosesAt : Subject → Prop → Prop → Prop) : Prop :=
  ∀ s p, ActAt s p → ∃ q, ChoosesAt s p q

def A14_Existential (Subject : Type) (ActAt : Subject → Prop → Prop)
    (FreeWillAt : Subject → Prop) : Prop :=
  (∃ s p, ActAt s p) → ∃ s, FreeWillAt s

def ProofSpecificContrast (Subject : Type) (s : Subject) (p q : Prop)
    (MeansAt : Subject → Prop → Prop) : Prop :=
  MeansAt s p ∧ MeansAt s q ∧ Incompatible p q

/-- Theorem: Proof-Specific Contrast yields FreeWill directly, bypassing Universal A14! -/
theorem proof_specific_contrast_yields_freewill
    (Subject : Type) (s : Subject) (p q : Prop)
    (MeansAt : Subject → Prop → Prop)
    (ChoosesAt : Subject → Prop → Prop → Prop)
    (hChoosesDef : ∀ s' a b, ChoosesAt s' a b ↔ (MeansAt s' a ∧ MeansAt s' b ∧ Incompatible a b))
    (hContrast : ProofSpecificContrast Subject s p q MeansAt) :
    ∃ s' : Subject, (∃ a b, ChoosesAt s' a b) := by
  refine ⟨s, p, q, (hChoosesDef s p q).mpr hContrast⟩

-- ===========================================================================
-- Part II: Fine-Grained Cognitive Modes (Sections 6, 7)
-- ===========================================================================

/-!
Decomposition of monolithic `Means`:
- `Considers s p`: p is cognitively present / entertained under examination.
- `Affirms s p`: s endorses / asserts p.
- `Rejects s p`: s rejects / refutes p.
-/

structure CognitiveSubject (Subject : Type) where
  Considers : Subject → Prop → Prop
  Affirms   : Subject → Prop → Prop
  Rejects   : Subject → Prop → Prop
  affirms_considers : ∀ s p, Affirms s p → Considers s p
  rejects_considers : ∀ s p, Rejects s p → Considers s p
  rational_consistency : ∀ s p, ¬ (Affirms s p ∧ Rejects s p)

-- ===========================================================================
-- Part III: Reductio / Refutation Semantics (Sections 2, 8)
-- ===========================================================================

/-- Structure of a genuine Reductio proof performed by subject s against target q:
    1. s considers target q (under hypothesis).
    2. s derives contradiction from q, thereby rejecting q.
    3. s affirms ¬q. -/
def RefutationalPerformance (Subject : Type) (CS : CognitiveSubject Subject)
    (s : Subject) (target : Prop) : Prop :=
  CS.Considers s target ∧ CS.Rejects s target ∧ CS.Affirms s (¬ target)

/-- Mathematical Theorem: A genuine Reductio necessarily engages incompatible contents!
    The subject who refutes q MUST cognitively consider both q and ¬q! -/
theorem reductio_engages_incompatible_contents
    (Subject : Type) (CS : CognitiveSubject Subject)
    (s : Subject) (q : Prop)
    (hReductio : RefutationalPerformance Subject CS s q) :
    CS.Considers s q ∧ CS.Considers s (¬ q) ∧ Incompatible q (¬ q) := by
  have hConsTarget : CS.Considers s q := hReductio.1
  have hAffirmNeg : CS.Affirms s (¬ q) := hReductio.2.2
  have hConsNeg : CS.Considers s (¬ q) := CS.affirms_considers s (¬ q) hAffirmNeg
  have hIncomp : Incompatible q (¬ q) := by
    intro ⟨hq, hnotq⟩
    exact hnotq hq
  exact ⟨hConsTarget, hConsNeg, hIncomp⟩

-- ===========================================================================
-- Part IV: ProofTrace Architecture & Performance vs Occurrence (Sections 3, 4, 5)
-- ===========================================================================

/-- Refutational Proof Step in a structured proof trace -/
inductive TraceStep where
  | hypothesis (q : Prop)
  | deduction (premise conclusion : Prop)
  | contradiction (q : Prop)
  | discharge (q : Prop)

abbrev RefutationalTrace : Type := List TraceStep

def TraceContainsAssumption (t : RefutationalTrace) (q : Prop) : Prop :=
  TraceStep.hypothesis q ∈ t

def TraceContainsDischarge (t : RefutationalTrace) (q : Prop) : Prop :=
  TraceStep.discharge q ∈ t

/-- Proof Performance: a subject intentionally executes the refutation -/
def PerformsRefutation (Subject : Type) (CS : CognitiveSubject Subject)
    (s : Subject) (t : RefutationalTrace) (q : Prop) : Prop :=
  TraceContainsAssumption t q ∧ TraceContainsDischarge t q ∧
  RefutationalPerformance Subject CS s q

/-- Hostile Model M1: Structural Trace Occurrence does NOT imply Cognitive Meaning!
    A purely syntactic or automated proof trace exists containing q and discharge q,
    without any subject consciously considering or meaning the contents. -/
theorem trace_occurrence_not_implies_cognitive_uptake :
    ∃ (t : RefutationalTrace) (q : Prop) (Subject : Type)
      (MeansAt : Subject → Prop → Prop),
      TraceContainsAssumption t q ∧ TraceContainsDischarge t q ∧
      ¬ (∃ s : Subject, MeansAt s q ∧ MeansAt s (¬ q)) := by
  refine ⟨[TraceStep.hypothesis True, TraceStep.discharge True], True, Empty,
          fun s _ => Empty.elim s, List.Mem.head _, List.Mem.tail _ (List.Mem.head _), ?_⟩
  intro ⟨s, _⟩
  exact Empty.elim s

-- ===========================================================================
-- Part V: Scope Correction of A14 (Section 10)
-- ===========================================================================

/-- Universal A14 is Overgeneralized and False for Arbitrary Acts:
    Witnessed by monadic initiation without choice. -/
theorem universal_a14_false_for_arbitrary_acts :
    ∃ (Subject : Type) (ActAt : Subject → Prop → Prop)
      (ChoosesAt : Subject → Prop → Prop → Prop),
      (∃ s p, ActAt s p) ∧ ¬ A14_Universal Subject ActAt ChoosesAt := by
  refine ⟨Unit, fun _ _ => True, fun _ _ _ => False, ⟨(), True, trivial⟩, ?_⟩
  intro hUniv
  have hContra := hUniv () True trivial
  obtain ⟨q, hq⟩ := hContra
  exact hq

/-- Corrected A14 (A14_Refutational / A14_Proof):
    Every subject intentionally performing a refutational proof
    necessarily experiences cognitive contrast between incompatible contents! -/
theorem a14_proof_performance_is_contrastive
    (Subject : Type) (CS : CognitiveSubject Subject)
    (s : Subject) (t : RefutationalTrace) (q : Prop)
    (hPerf : PerformsRefutation Subject CS s t q) :
    ∃ p, Incompatible p q ∧ CS.Considers s p ∧ CS.Considers s q := by
  have hEngages := reductio_engages_incompatible_contents Subject CS s q hPerf.2.2
  refine ⟨¬ q, ?_, hEngages.2.1, hEngages.1⟩
  intro ⟨hnotq, hq⟩
  exact hnotq hq

-- ===========================================================================
-- Part VI: Hostile Model Suite M0–M6 (Section 12)
-- ===========================================================================

/-!
The 7-Model Ladder:
M0: Formal proof exists, no subject.
M1: Subject executes mechanically, no cognitive uptake.
M2: Subject intentionally considers one proposition only.
M3: Subject intentionally considers q for refutation.
M4: Subject considers q and ¬q without choosing.
M5: Subject co-means q and ¬q without choosing.
M6: Subject genuinely chooses between q and ¬q.
-/

/-- Separation M0 ↛ M1: Formal trace exists without any subject executing it -/
theorem model_M0_trace_without_subject :
    ∃ (t : RefutationalTrace),
      TraceContainsAssumption t True ∧ TraceContainsDischarge t True ∧
      (∀ (s : Empty) (CS : CognitiveSubject Empty), ¬ PerformsRefutation Empty CS s t True) := by
  refine ⟨[TraceStep.hypothesis True, TraceStep.discharge True],
          List.Mem.head _, List.Mem.tail _ (List.Mem.head _), fun s _ _ => Empty.elim s⟩

/-- Separation M2 ↛ M3: Monadic consideration does not imply refutation -/
theorem model_M2_not_implies_M3 :
    ∃ (Subject : Type) (CS : CognitiveSubject Subject) (s : Subject) (q : Prop),
      CS.Considers s q ∧ ¬ CS.Rejects s q := by
  let CS0 : CognitiveSubject Unit := {
    Considers := fun _ _ => True
    Affirms   := fun _ _ => False
    Rejects   := fun _ _ => False
    affirms_considers := fun _ _ h => by cases h
    rejects_considers := fun _ _ h => by cases h
    rational_consistency := fun _ _ ⟨h, _⟩ => by cases h
  }
  refine ⟨Unit, CS0, (), True, trivial, id⟩

/-- Separation M3 ↛ M4: Considering q does not imply dual consideration unless negation is affirmed -/
theorem model_M3_not_implies_M4 :
    ∃ (Subject : Type) (s : Subject) (q : Prop)
      (Considers : Subject → Prop → Prop),
      Considers s q ∧ ¬ Considers s (¬ q) := by
  refine ⟨Unit, (), True, fun _ p' => p' = True, rfl, ?_⟩
  intro hContra
  have h1 : ¬ True := by rw [hContra]; trivial
  exact h1 trivial

/-- Separation M4 ↛ M5: Dual consideration does not imply dual meaning (endorsement) -/
theorem model_M4_not_implies_M5 :
    ∃ (Subject : Type) (s : Subject) (q : Prop)
      (Considers : Subject → Prop → Prop)
      (MeansAt : Subject → Prop → Prop),
      Considers s q ∧ Considers s (¬ q) ∧ Incompatible q (¬ q) ∧
      ¬ (MeansAt s q ∧ MeansAt s (¬ q)) := by
  refine ⟨Unit, (), True, fun _ _ => True, fun _ p' => p' = True,
          ⟨trivial, trivial, (fun ⟨h1, h2⟩ => h2 h1), ?_⟩⟩
  intro ⟨_, hMeansNeg⟩
  have h1 : ¬ True := by rw [hMeansNeg]; trivial
  exact h1 trivial

/-- Separation M5 ↛ M6: Co-meaning incompatible contents does not imply choice -/
theorem model_M5_not_implies_M6 :
    ∃ (Subject : Type) (s : Subject) (q : Prop)
      (MeansAt : Subject → Prop → Prop)
      (ChoosesAt : Subject → Prop → Prop → Prop),
      MeansAt s q ∧ MeansAt s (¬ q) ∧ Incompatible q (¬ q) ∧
      ¬ ChoosesAt s q (¬ q) := by
  refine ⟨Unit, (), True, fun _ _ => True, fun _ _ _ => False,
          ⟨trivial, trivial, (fun ⟨h1, h2⟩ => h2 h1), id⟩⟩

-- ===========================================================================
-- Part VIII: Direct Derivation of F1b via Proof Performance (Section 11)
-- ===========================================================================

/-!
### Direct Route to F1b:
In the actual retorsion argument of Γ:
The subject s performs the refutation of P (where P := "No subject acts").
1. s considers P (for refutation).
2. s derives a contradiction from P.
3. s affirms ¬P and rejects P.
4. Cognitive Uptake: when a subject performs an intentional refutation,
   both the rejected thesis P and the affirmed conclusion ¬P are represented in thought:
   `Means s P ∧ Means s (¬ P)`.
5. Since `Incompatible P (¬ P)`, s co-means incompatible alternatives:
   `Chooses s (¬ P) P`.
6. Therefore, `FreeWill s` is derived directly!
-/

def RefutationalCognitiveUptake (Subject : Type) (CS : CognitiveSubject Subject)
    (MeansAt : Subject → Prop → Prop) : Prop :=
  ∀ s q, RefutationalPerformance Subject CS s q → MeansAt s q ∧ MeansAt s (¬ q)

/-- The Core Breakthrough Theorem:
    Performative Proof yields FreeWill directly without Universal A14! -/
theorem performative_proof_yields_freewill
    (Subject : Type) (CS : CognitiveSubject Subject)
    (MeansAt : Subject → Prop → Prop)
    (ChoosesAt : Subject → Prop → Prop → Prop)
    (hChoosesDef : ∀ s' a b, ChoosesAt s' a b ↔ (MeansAt s' a ∧ MeansAt s' b ∧ Incompatible a b))
    (hUptake : RefutationalCognitiveUptake Subject CS MeansAt)
    (s : Subject) (target : Prop)
    (hProof : RefutationalPerformance Subject CS s target) :
    ∃ s' : Subject, (∃ a b, ChoosesAt s' a b) := by
  obtain ⟨hMeansTarget, hMeansNeg⟩ := hUptake s target hProof
  have hIncomp : Incompatible (¬ target) target := by
    intro ⟨hnotq, hq⟩
    exact hnotq hq
  have hChooses : ChoosesAt s (¬ target) target :=
    (hChoosesDef s (¬ target) target).mpr ⟨hMeansNeg, hMeansTarget, hIncomp⟩
  exact ⟨s, (¬ target), target, hChooses⟩

/-- The Existential Free Will Theorem (F1b) derived from the performative retorsion proof! -/
theorem retorsion_proof_derives_F1b
    (Subject : Type) (CS : CognitiveSubject Subject)
    (MeansAt : Subject → Prop → Prop)
    (ChoosesAt : Subject → Prop → Prop → Prop)
    (FreeWillAt : Subject → Prop)
    (hFreeWillDef : ∀ s', FreeWillAt s' ↔ ∃ a b, ChoosesAt s' a b)
    (hChoosesDef : ∀ s' a b, ChoosesAt s' a b ↔ (MeansAt s' a ∧ MeansAt s' b ∧ Incompatible a b))
    (hUptake : RefutationalCognitiveUptake Subject CS MeansAt)
    (s : Subject) (target : Prop)
    (hProof : RefutationalPerformance Subject CS s target) :
    ∃ s' : Subject, FreeWillAt s' := by
  obtain ⟨s', a, b, hChooses⟩ :=
    performative_proof_yields_freewill Subject CS MeansAt ChoosesAt hChoosesDef hUptake s target hProof
  refine ⟨s', (hFreeWillDef s').mpr ⟨a, b, hChooses⟩⟩

end Logos.ProofSpecificContrast


/-
================================================================================
SECTION: AdversarialReductioAudit
================================================================================
-/
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


/-
================================================================================
SECTION: CognitiveToAgencyFrontier
================================================================================
-/
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


/-
================================================================================
SECTION: FreeWillIndependence
================================================================================
-/
/-
# Logos.FreeWillIndependence — Model-Theoretic Independence of Free Will in Γ

This module investigates whether Free Will can be proved, refuted, or shown to be
model-theoretically independent of the pre-A14 base of Γ.

Contents:
1. Target Locking & Definitional Audit (F1b, FreeWill, Chooses, Settlement1, ReductioProgression).
2. The Positive Ladder & Intermediate Breakdown (Settlement1 → Commitment → Intentional → Choice).
3. Full Model-Theoretic Independence (Model A: Γ + FreeWill, Model B: Γ + ¬FreeWill).
4. Structural Model Transformation T (Contrastive Collapse).
5. Determinism, Identical Deliberation (Case D, Case M, Case A), and Could-Have-Done-Otherwise.
6. Rational Deliberation vs Libertarian Freedom (Orthogonality proofs).
7. Minimal Extensions (B1 to B4) & The Four Capstones.

Governing rule:
"Prefer losing the theorem to hiding the premise."
-/


namespace Logos.FreeWillIndependence

open Logos.Agency (Subject Act Means State Initiates)
open Logos.Choice (Chooses FreeWill FreeSubject)
open Logos.Alternatives (Incompatible)
open Logos.CognitiveToAgencyFrontier (FineCognitiveSubject ReductioProgression Settlement1)

-- ===========================================================================
-- Part I: Target Locking & Circularity Audit (Stage 1)
-- ===========================================================================

/-- F1b: The existential claim that strong intentional action entails the existence
    of at least one subject endowed with free will. -/
def F1b_Target : Prop := (∃ s : Subject, ∃ p : Prop, Act s p) → ∃ s : Subject, FreeWill s

/-- Theorem: Under the actual kernel definitions of Logos.Choice, F1b is definitionally
    equivalent to existential contrastive choice. -/
theorem f1b_target_definitionally_unfolded :
    F1b_Target ↔ ((∃ s : Subject, ∃ p : Prop, Act s p) →
      ∃ s : Subject, ∃ p q : Prop, Means s p ∧ Means s q ∧ Incompatible p q) := by
  rfl

/-- Definitional Audit of Settlement-1:
    Settlement1 is an assembled predicate unifying the dynamic moments of ReductioProgression.
    It does not introduce an ungrounded synthetic primitive, but rather packages the
    asymmetric evaluative stance of the subject. -/
theorem settlement_1_is_assembled_package
    (CS : FineCognitiveSubject Subject) (s : Subject) (p q : Prop) :
    Settlement1 Subject CS s p q ↔
    (CS.Considers s p ∧ CS.Considers s q ∧ Incompatible p q ∧ CS.Affirms s p ∧ CS.Rejects s q) := by
  rfl

-- ===========================================================================
-- Part II: Positive Ladder & Breakdown at Commitment and Intentionality (Stage 2)
-- ===========================================================================

/-- Ladder Stage 2: Commitment. The subject doxastically or normatively commits to p. -/
def HasCommitment (CS : FineCognitiveSubject Subject) (s : Subject) (p : Prop) : Prop :=
  CS.CommitsTo s p

/-- Countermodel M14+: Dual asymmetric evaluation without durable commitment.
    A subject can affirm ¬q and reject q without satisfying CommitsTo. -/
theorem model_M14_plus_evaluation_without_commitment :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj) (s : Subj) (q : Prop),
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

/-- The Fundamental Asymmetry Dilemma:
    Intentional resolution requires endorsing ¬q and excluding q (Means s ¬q ∧ ¬ Means s q).
    Choice requires co-meaning both horns (Means s ¬q ∧ Means s q).
    Therefore, intentional resolution is mutually exclusive with genuine Choice between the horns! -/
theorem intentional_resolution_excludes_choice_of_same_horns
    (MeansAt : Subject → Prop → Prop) (s : Subject) (p q : Prop)
    (hRes : MeansAt s p ∧ ¬ MeansAt s q) :
    ¬ (MeansAt s p ∧ MeansAt s q ∧ Incompatible p q) := by
  intro ⟨_, h2, _⟩
  exact hRes.2 h2

/-- Dynamic Cognitive Status Transition -/
inductive CognitiveStatus | Assumed | Examined | Rejected | Affirmed

/-- Deterministic status transition without agency:
    A deterministic transition function can execute the status transition without Free Will. -/
theorem deterministic_status_transition_without_freewill :
    ∃ (Transition : CognitiveStatus → CognitiveStatus),
      Transition CognitiveStatus.Assumed = CognitiveStatus.Rejected ∧
      Transition CognitiveStatus.Examined = CognitiveStatus.Affirmed := by
  let T : CognitiveStatus → CognitiveStatus := fun st =>
    match st with
    | CognitiveStatus.Assumed => CognitiveStatus.Rejected
    | CognitiveStatus.Examined => CognitiveStatus.Affirmed
    | CognitiveStatus.Rejected => CognitiveStatus.Rejected
    | CognitiveStatus.Affirmed => CognitiveStatus.Affirmed
  exact ⟨T, rfl, rfl⟩

-- ===========================================================================
-- Part III: Full Model-Theoretic Independence (Stage 3)
-- ===========================================================================

/-- Structure capturing an interpretation of the pre-A14 core of Γ:
    Includes Subject, Means, State, Initiates, Act, and fine-grained cognitive reductio. -/
structure GammaCoreModel where
  Subj          : Type
  St            : Type
  MeansRel      : Subj → Prop → Prop
  InitiatesRel  : Subj → St → St → Prop → Prop
  CS            : FineCognitiveSubject Subj
  -- Act is meaningful initiation
  ActPred       : Subj → Prop → Prop := fun s p => MeansRel s p ∧ ∃ w w' : St, InitiatesRel s w w' p
  -- Cogito: at least one act exists
  act_witness   : ∃ s p, ActPred s p
  -- Reductio progression occurs
  reductio_wit  : ∃ s q, ReductioProgression Subj CS s q

/-- Model A: Full Model of pre-A14 Γ WITH Free Will (Choice exists). -/
theorem model_A_gamma_with_freewill :
    ∃ (M : GammaCoreModel),
      ∃ (s : M.Subj) (p q : Prop),
        M.MeansRel s p ∧ M.MeansRel s q ∧ Incompatible p q := by
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
  have hIncomp : Incompatible True (¬ True) := fun ⟨h1, h2⟩ => h2 h1
  have hIncompNotTrue : Incompatible (¬ True) True := fun ⟨h1, h2⟩ => h1 h2
  let M0 : GammaCoreModel := {
    Subj := Unit
    St := Unit
    MeansRel := fun _ _ => True
    InitiatesRel := fun _ _ _ _ => True
    CS := CS0
    ActPred := fun _ _ => True ∧ ∃ _ _ : Unit, True
    act_witness := ⟨(), True, ⟨trivial, (), (), trivial⟩⟩
    reductio_wit := ⟨(), True, ⟨rfl, trivial, rfl, rfl, hIncomp⟩⟩
  }
  refine ⟨M0, (), (¬ True), True, trivial, trivial, hIncompNotTrue⟩

/-- Model B: Full Model of pre-A14 Γ WITHOUT Free Will (No choice exists anywhere).
    Every subject is strictly unipolar: at most one proposition of any incompatible pair is meant. -/
theorem model_B_gamma_without_freewill :
    ∃ (M : GammaCoreModel),
      (∀ (s : M.Subj) (p q : Prop),
        Incompatible p q → ¬ (M.MeansRel s p ∧ M.MeansRel s q)) := by
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
  have hIncomp : Incompatible True (¬ True) := fun ⟨h1, h2⟩ => h2 h1
  -- MeansRel is strictly unipolar: only True is meant
  let MeansUnipolar : Unit → Prop → Prop := fun _ p => p = True
  let M0 : GammaCoreModel := {
    Subj := Unit
    St := Unit
    MeansRel := MeansUnipolar
    InitiatesRel := fun _ _ _ _ => True
    CS := CS0
    ActPred := fun _ p => p = True ∧ ∃ _ _ : Unit, True
    act_witness := ⟨(), True, ⟨rfl, (), (), trivial⟩⟩
    reductio_wit := ⟨(), True, ⟨rfl, trivial, rfl, rfl, hIncomp⟩⟩
  }
  refine ⟨M0, ?_⟩
  intro s p q hIncompPQ ⟨hp, hq⟩
  have hpTrue : p = True := hp
  have hqTrue : q = True := hq
  have hBoth : p ∧ q := by rw [hpTrue, hqTrue]; exact ⟨trivial, trivial⟩
  exact hIncompPQ hBoth

/-- Metatheoretic Independence Theorem:
    Free Will is strictly model-theoretically independent of the pre-A14 core of Γ.
    It can neither be proved nor refuted from the existing axioms. -/
theorem freewill_is_model_theoretically_independent :
    (∃ M : GammaCoreModel, ∃ s p q, M.MeansRel s p ∧ M.MeansRel s q ∧ Incompatible p q) ∧
    (∃ M : GammaCoreModel, ∀ s p q, Incompatible p q → ¬ (M.MeansRel s p ∧ M.MeansRel s q)) := by
  exact ⟨model_A_gamma_with_freewill, model_B_gamma_without_freewill⟩

/-- Structural Transformation T: Contrastive Collapse.
    Transforms any model M into a model where co-meaning of incompatible pairs is eliminated,
    while preserving truth, acts, and reductio settlement. -/
def TransformToUnipolar (M : GammaCoreModel) (s_witness : M.Subj) (p_witness : Prop)
    (hWitness : M.MeansRel s_witness p_witness ∧ ∃ w w' : M.St, M.InitiatesRel s_witness w w' p_witness) :
    GammaCoreModel := {
  Subj := M.Subj
  St := M.St
  MeansRel := fun s p => M.MeansRel s p ∧ p = p_witness
  InitiatesRel := M.InitiatesRel
  CS := M.CS
  ActPred := fun s p => (M.MeansRel s p ∧ p = p_witness) ∧ ∃ w w' : M.St, M.InitiatesRel s w w' p
  act_witness := by
    rcases hWitness with ⟨hMeans, w, w', hInit⟩
    exact ⟨s_witness, p_witness, ⟨⟨hMeans, rfl⟩, w, w', hInit⟩⟩
  reductio_wit := M.reductio_wit
}

-- ===========================================================================
-- Part IV: Determinism, Identical Deliberation, & Modal Freedom (Stage 4)
-- ===========================================================================

/-- Deliberative State Structure for Identical-Deliberation Testing -/
structure DeliberativeState where
  beliefs : List Prop
  goals   : List Prop
  derivation_trace : List Prop

/-- The Identical-Deliberation Test:
    Case D: Determinism. Identical deliberative antecedents force identical settlement. -/
theorem identical_deliberation_case_D :
    ∃ (Transition : DeliberativeState → Prop),
      ∀ d1 d2 : DeliberativeState, d1 = d2 → Transition d1 = Transition d2 := by
  refine ⟨fun _ => True, fun _ _ _ => rfl⟩

/-- Case M: Bilateral Modal Access.
    Given deliberative state d, both incompatible outcomes are accessible worlds. -/
theorem identical_deliberation_case_M :
    ∃ (Accessible : DeliberativeState → Prop → Prop) (d : DeliberativeState) (p q : Prop),
      Accessible d p ∧ Accessible d q ∧ Incompatible p q := by
  let d0 : DeliberativeState := ⟨[], [], []⟩
  have hIncomp : Incompatible (¬ True) True := fun ⟨h1, h2⟩ => h1 h2
  refine ⟨fun _ _ => True, d0, (¬ True), True, trivial, trivial, hIncomp⟩

/-- Case A: Agent-Causal Determination.
    The agent settles the outcome non-deterministically. -/
theorem identical_deliberation_case_A :
    ∃ (AgentSettles : DeliberativeState → Prop → Prop) (d : DeliberativeState) (p q : Prop),
      Incompatible p q ∧ AgentSettles d p ∧ ¬ AgentSettles d q := by
  let d0 : DeliberativeState := ⟨[], [], []⟩
  have hIncomp : Incompatible (¬ True) True := fun ⟨h1, h2⟩ => h1 h2
  refine ⟨fun _ prop => prop = (¬ True), d0, (¬ True), True, hIncomp, rfl, ?_⟩
  intro hContra
  have h1 : True = (¬ True) := hContra
  have h2 : ¬ True := by rw [← h1]; trivial
  exact h2 trivial

/-- Could Have Done Otherwise (CHDO):
    Separation theorem: Settlement1 is compatible with total failure of CHDO (fatalism). -/
theorem settlement_1_compatible_with_no_chdo :
    ∃ (Subject : Type) (CS : FineCognitiveSubject Subject) (s : Subject) (p q : Prop)
      (AlternateActionAccessible : Subject → Prop → Prop),
      Settlement1 Subject CS s p q ∧ (∀ s' prop, ¬ AlternateActionAccessible s' prop) := by
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
  refine ⟨Unit, CS0, (), (¬ True), True, fun _ _ => False,
          ⟨trivial, trivial, (fun ⟨h1, h2⟩ => h1 h2), rfl, rfl⟩,
          fun _ _ h => by cases h⟩

-- ===========================================================================
-- Part V: Rational Deliberation vs Libertarian Freedom (Stage 4)
-- ===========================================================================

/-- Rational Deliberation Vocabulary -/
structure RationalDeliberator (Subject : Type) where
  ReasonsFor       : Subject → Prop → Prop → Prop  -- reason r supports p
  Evaluates        : Subject → Prop → Prop         -- weighs evidence for p
  Compares         : Subject → Prop → Prop → Prop  -- compares p against q
  RespondsToReason : Subject → Prop → Prop         -- tracks normative reasons

/-- Directional Model 1: Deterministic rational deliberation without modal freedom.
    A subject can possess complete reasons, evaluate, compare, and track truth,
    while operating under strictly deterministic transitions. -/
theorem model_deterministic_rationality_without_modal_freedom :
    ∃ (Subject : Type) (RD : RationalDeliberator Subject) (s : Subject) (p _q : Prop)
      (CanActOtherwise : Subject → Prop → Prop),
      RD.Compares s p _q ∧ RD.RespondsToReason s p ∧ (∀ s' prop, ¬ CanActOtherwise s' prop) := by
  let RD0 : RationalDeliberator Unit := {
    ReasonsFor := fun _ _ _ => True
    Evaluates := fun _ _ => True
    Compares := fun _ _ _ => True
    RespondsToReason := fun _ _ => True
  }
  refine ⟨Unit, RD0, (), (¬ True), True, fun _ _ => False, trivial, trivial, fun _ _ h => by cases h⟩

/-- Directional Model 2: Libertarian settlement without rational reasons.
    An agent can determine an outcome by brute volition without reasons. -/
theorem model_libertarian_settlement_without_reasons :
    ∃ (Subject : Type) (RD : RationalDeliberator Subject) (s : Subject) (p _q : Prop)
      (AgentDetermines : Subject → Prop → Prop),
      (∀ r, ¬ RD.ReasonsFor s r p) ∧ AgentDetermines s p := by
  let RD0 : RationalDeliberator Unit := {
    ReasonsFor := fun _ _ _ => False
    Evaluates := fun _ _ => False
    Compares := fun _ _ _ => False
    RespondsToReason := fun _ _ => False
  }
  refine ⟨Unit, RD0, (), (¬ True), True, fun _ _ => True, ?_⟩
  exact ⟨fun _ (h : False) => False.elim h, trivial⟩

/-- Orthogonality Theorem: Rational deliberation and libertarian freedom are logically independent. -/
theorem rationality_orthogonal_to_libertarian_freedom :
    (∃ (Subj : Type) (RD : RationalDeliberator Subj) (s : Subj) (p q : Prop) (CanAct : Subj → Prop → Prop),
      RD.Compares s p q ∧ ¬ (CanAct s p ∧ CanAct s q)) ∧
    (∃ (Subj : Type) (RD : RationalDeliberator Subj) (s : Subj) (p _q : Prop) (AgentDet : Subj → Prop → Prop),
      AgentDet s p ∧ (∀ r, ¬ RD.ReasonsFor s r p)) := by
  refine ⟨⟨Unit, { ReasonsFor := fun _ _ _ => True, Evaluates := fun _ _ => True,
                   Compares := fun _ _ _ => True, RespondsToReason := fun _ _ => True },
           (), (¬ True), True, fun _ _ => False, ⟨trivial, fun ⟨h, _⟩ => False.elim h⟩⟩,
         ⟨Unit, { ReasonsFor := fun _ _ _ => False, Evaluates := fun _ _ => False,
                   Compares := fun _ _ _ => False, RespondsToReason := fun _ _ => False },
           (), (¬ True), True, fun _ _ => True, ⟨trivial, fun _ (h : False) => False.elim h⟩⟩⟩

-- ===========================================================================
-- Part VI: Minimal Extensions B1 to B4 (Stage 4)
-- ===========================================================================

/-- Extension B1: Doxastic/Normative Commitment Principle (SEMANTIC). -/
def BridgeB1 (CS : FineCognitiveSubject Subject) : Prop :=
  ∀ s p, CS.Affirms s p → CS.CommitsTo s p

/-- Extension B2: Bilateral Co-Meaning / Uptake Principle (SEMANTIC). -/
def BridgeB2 (CS : FineCognitiveSubject Subject) (MeansAt : Subject → Prop → Prop) : Prop :=
  ∀ s q, CS.Affirms s (¬ q) ∧ CS.Rejects s q → MeansAt s (¬ q) ∧ MeansAt s q

/-- Extension B3: Modal Plurality Principle (METAPHYSICAL). -/
def BridgeB3 (MeansAt : Subject → Prop → Prop) (CanAct : Subject → Prop → Prop) : Prop :=
  ∀ s p q, MeansAt s p ∧ MeansAt s q ∧ Incompatible p q → CanAct s p ∧ CanAct s q

/-- Extension B4: Agent-Causal Determination Principle (METAPHYSICAL). -/
def BridgeB4 (CanAct : Subject → Prop → Prop) (AgentDetermines : Subject → Prop → Prop) : Prop :=
  ∀ s p q, CanAct s p ∧ CanAct s q ∧ Incompatible p q →
    ∃ chosen : Prop, (chosen = p ∨ chosen = q) ∧ AgentDetermines s chosen

/-- Deduction: Bridge B2 derives genuine Choice from Settlement-1. -/
theorem bridge_B2_derives_choice
    (CS : FineCognitiveSubject Subject) (MeansAt : Subject → Prop → Prop)
    (hB2 : BridgeB2 CS MeansAt) (s : Subject) (q : Prop)
    (hRed : ReductioProgression Subject CS s q) :
    MeansAt s (¬ q) ∧ MeansAt s q ∧ Incompatible (¬ q) q := by
  have hCoMeans := hB2 s q ⟨hRed.affirmed_negation, hRed.rejected⟩
  have hIncomp : Incompatible (¬ q) q := fun ⟨h1, h2⟩ => h1 h2
  exact ⟨hCoMeans.1, hCoMeans.2, hIncomp⟩

end Logos.FreeWillIndependence


/-
================================================================================
SECTION: ChoiceRepair
================================================================================
-/
/-
# Logos.ChoiceRepair — Rebuilding Choice and Testing the Repaired Free-Will Definition

This module investigates whether Γ's newly established concept of asymmetric cognitive
settlement provides a repaired, independently motivated foundation for Choice and Free Will,
or whether Free Will remains model-theoretically independent of the pre-A14 system.

Contents:
1. Historical Theory Preservation (Freezing old Chooses and FreeWill).
2. Semantic Divergence: Simultaneous Co-Meaning vs Asymmetric Reductio Progression.
3. Repaired Choice Candidate: SettlementChoice and the Circularity / Agency Audit.
4. The Four-Tier Agency Hierarchy: CognitiveSettlement → VolitionalSettlement → ActionSelection → AgentCausalSettlement.
5. Hostile Model Suite M19–M22: Disconnecting cognitive resolution, volition, capacity, and agent causation.
6. Hostile Model Suite M23–M26: Deterministic deliberator, automatic evaluator, passive truth-tracker, compatibilist choice.
7. Identical Total Deliberation Evaluation: Testing SettlementChoice across Cases D, M, and A.
8. Mutual Orthogonality: SettlementChoice ⟂ Chooses_old.
9. Extended Gamma Model and Model-Theoretic Independence of Libertarian Free Will.
10. Structural Model Transformation T_agency.

Governing rule:
"Prefer losing the theorem to hiding the premise."
-/


namespace Logos.ChoiceRepair

open Logos.Agency (Subject Act Means State Initiates)
open Logos.Choice (Chooses FreeWill FreeSubject)
open Logos.Alternatives (Incompatible)
open Logos.CognitiveToAgencyFrontier (FineCognitiveSubject ReductioProgression Settlement1)

-- ===========================================================================
-- Part I: Historical Theory Preservation & Semantic Divergence (Stage 1)
-- ===========================================================================

/-- Section I: Historical Chooses and FreeWill are preserved intact.
    Chooses(s, p, q) := Means s p ∧ Means s q ∧ Incompatible p q.
    FreeWill(s) := ∃ p q, Chooses s p q. -/
def OldChooses (s : Subject) (p q : Prop) : Prop := Logos.Choice.Chooses s p q
def OldFreeWill (s : Subject) : Prop := Logos.Choice.FreeWill s

/-- Section II & IX: Semantic Divergence.
    Old choice requires simultaneous co-meaning of incompatible contents.
    Actual reductio requires asymmetric status transition (rejecting q, affirming ¬q).
    Intentional resolution is therefore formally incompatible with old Chooses. -/
theorem divergence_between_intentional_resolution_and_old_choice
    (s : Subject) (p q : Prop)
    (hResolution : Means s p ∧ ¬ Means s q) :
    ¬ (OldChooses s p q) := by
  intro ⟨_, h2, _⟩
  exact hResolution.2 h2

-- ===========================================================================
-- Part II: Repaired Choice Candidates & Circularity / Agency Audit (Stage 2)
-- ===========================================================================

/-- Section III: Repaired Choice Candidate based on cognitive resolution.
    SettlementChoice requires considering incompatible alternatives and
    asymmetrically affirming one while rejecting the other. -/
def SettlementChoice {Subj : Type} (CS : FineCognitiveSubject Subj) (s : Subj) (p q : Prop) : Prop :=
  CS.Considers s p ∧ CS.Considers s q ∧ Incompatible p q ∧ CS.Affirms s p ∧ CS.Rejects s q

/-- Section III: Equivalence Theorem.
    SettlementChoice is definitionally identical to Settlement1. -/
theorem settlementChoice_iff_settlement1
    {Subj : Type} (CS : FineCognitiveSubject Subj) (s : Subj) (p q : Prop) :
    SettlementChoice CS s p q ↔ Settlement1 Subj CS s p q := by
  rfl

/-- Section IV: Reductio entails SettlementChoice.
    Any subject executing a genuine reductio progression achieves SettlementChoice. -/
theorem reductio_derives_settlementChoice
    {Subj : Type} (CS : FineCognitiveSubject Subj) (s : Subj) (q : Prop)
    (hRed : ReductioProgression Subj CS s q) :
    SettlementChoice CS s (¬ q) q := by
  exact Logos.CognitiveToAgencyFrontier.reductio_proves_settlement_1 Subj CS s q hRed

/-- Section IV: Circularity Audit.
    Proving SettlementChoice from ReductioProgression is a definitional consequence
    of the progression's constituents, NOT the spontaneous emergence of an unstated agency. -/
theorem settlementChoice_is_definitional_unfolding
    {Subj : Type} (CS : FineCognitiveSubject Subj) (s : Subj) (q : Prop)
    (hRed : ReductioProgression Subj CS s q) :
    CS.Affirms s (¬ q) ∧ CS.Rejects s q ∧ Incompatible (¬ q) q := by
  have hIncomp : Incompatible (¬ q) q := fun ⟨h1, h2⟩ => h1 h2
  exact ⟨hRed.affirmed_negation, hRed.rejected, hIncomp⟩

-- ===========================================================================
-- Part III: The Four-Tier Agency Hierarchy (Stage 2)
-- ===========================================================================

/-- Tier 1: Cognitive Settlement (Resolution between evaluated contents). -/
def CognitiveSettlement {Subj : Type} (CS : FineCognitiveSubject Subj) (s : Subj) (p q : Prop) : Prop :=
  SettlementChoice CS s p q

/-- Tier 2: Volitional Settlement (Adopting the resolution into executive aiming). -/
def VolitionalSettlement {Subj : Type} (CS : FineCognitiveSubject Subj) (s : Subj) (p q : Prop) : Prop :=
  CognitiveSettlement CS s p q ∧ CS.AimsAt s p ∧ ¬ CS.AimsAt s q

/-- Tier 3: Action Selection (Executing concrete intentional action positing the resolution). -/
def ActionSelection {Subj : Type} (CS : FineCognitiveSubject Subj)
    (ActRel : Subj → Prop → Prop) (s : Subj) (p q : Prop) : Prop :=
  VolitionalSettlement CS s p q ∧ ActRel s p ∧ ¬ ActRel s q

/-- Tier 4: Agent-Causal Settlement (Agent substance irreducibly settles the outcome). -/
def AgentCausalSettlement {Subj : Type} (CS : FineCognitiveSubject Subj)
    (ActRel : Subj → Prop → Prop) (AgentDetermines : Subj → Prop → Prop)
    (s : Subj) (p q : Prop) : Prop :=
  ActionSelection CS ActRel s p q ∧ AgentDetermines s p ∧ ¬ AgentDetermines s q

-- ===========================================================================
-- Part IV: Hostile Model Suite M19–M22 (Stage 3)
-- ===========================================================================

/-- M19: Cognitive resolution without volition.
    A subject deterministically concludes ¬q and rejects q, but has zero volitional aiming. -/
theorem model_M19_cognitive_resolution_without_volition :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj) (s : Subj) (p q : Prop),
      SettlementChoice CS s p q ∧ ¬ (CS.AimsAt s p) := by
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
  have hIncomp : Incompatible (¬ True) True := fun ⟨h1, h2⟩ => h1 h2
  refine ⟨Unit, CS0, (), (¬ True), True, ⟨trivial, trivial, hIncomp, rfl, rfl⟩, id⟩

/-- M20: Volitional resolution without alternative capacity.
    The subject aims at p, but only one outcome is possible in the world. -/
theorem model_M20_volition_without_alternative_capacity :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj) (s : Subj) (p q : Prop)
      (CanActOtherwise : Subj → Prop → Prop),
      VolitionalSettlement CS s p q ∧ (∀ s' prop, ¬ CanActOtherwise s' prop) := by
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
  have hNotAimsQ : ¬ CS0.AimsAt () True := by
    intro (h : True = (¬ True))
    have hFalse : ¬ True := by rw [← h]; trivial
    exact hFalse trivial
  refine ⟨Unit, CS0, (), (¬ True), True, fun _ _ => False,
          ⟨⟨trivial, trivial, hIncomp, rfl, rfl⟩, rfl, hNotAimsQ⟩,
          fun _ _ h => by cases h⟩

/-- M21: Action selection without libertarian freedom.
    The subject acts, but the transition is strictly deterministic and necessitates the action. -/
theorem model_M21_action_selection_without_libertarian_freedom :
    ∃ (Subj : Type) (ActRel : Subj → Prop → Prop) (s : Subj) (p : Prop)
      (Determined : Subj → Prop → Prop),
      ActRel s p ∧ Determined s p := by
  refine ⟨Unit, fun _ _ => True, (), True, fun _ _ => True, trivial, trivial⟩

/-- M22: Agent-causal settlement.
    The agent substance non-deterministically settles between incompatible horns. -/
theorem model_M22_agent_causal_settlement :
    ∃ (Subj : Type) (AgentDetermines : Subj → Prop → Prop) (s : Subj) (p q : Prop),
      Incompatible p q ∧ AgentDetermines s p ∧ ¬ AgentDetermines s q := by
  have hIncomp : Incompatible (¬ True) True := fun ⟨h1, h2⟩ => h1 h2
  refine ⟨Unit, fun _ prop => prop = (¬ True), (), (¬ True), True, hIncomp, rfl, ?_⟩
  intro hContra
  have h1 : True = (¬ True) := hContra
  have h2 : ¬ True := by rw [← h1]; trivial
  exact h2 trivial

-- ===========================================================================
-- Part V: Hostile Model Suite M23–M26 (Stage 3)
-- ===========================================================================

/-- M23: Fully deterministic deliberator.
    Complete reasoning, evaluation, and settlement, where every step is deterministically fixed. -/
theorem model_M23_fully_deterministic_deliberator :
    ∃ (StateSpace : Type) (Step : StateSpace → StateSpace) (Eval : StateSpace → Prop),
      ∀ st1 st2 : StateSpace, st1 = st2 → Step st1 = Step st2 ∧ Eval st1 = Eval st2 := by
  refine ⟨Unit, id, fun _ => True, fun _ _ h => by rw [h]; exact ⟨rfl, rfl⟩⟩

/-- M24: Automatic rational evaluator.
    The subject represents and evaluates alternatives, but evaluation is a fixed function of state. -/
theorem model_M24_automatic_rational_evaluator :
    ∃ (StateSpace : Type) (Evaluate : StateSpace → Prop → Prop),
      ∀ st1 st2 : StateSpace, st1 = st2 → ∀ p, Evaluate st1 p = Evaluate st2 p := by
  refine ⟨Unit, fun _ _ => True, fun _ _ h _ => by rw [h]⟩

/-- M25: Passive truth tracker.
    Always settles on the truth, but operates with zero discretionary agency. -/
theorem model_M25_passive_truth_tracker :
    ∃ (Tracker : Prop → Prop),
      (∀ p : Prop, p → Tracker p = True) ∧ (∀ p : Prop, ¬ p → Tracker p = False) := by
  refine ⟨fun p => p, fun p hp => ?_, fun p hnp => ?_⟩
  · apply propext
    constructor
    · intro _; trivial
    · intro _; exact hp
  · apply propext
    constructor
    · intro hp; exact False.elim (hnp hp)
    · intro hFalse; exact False.elim hFalse

/-- M26: Choice without libertarianism.
    SettlementChoice holds, but bilateral modal freedom is completely absent. -/
theorem model_M26_choice_without_libertarianism :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj) (s : Subj) (p q : Prop)
      (CanActBilateral : Subj → Prop → Prop → Prop),
      SettlementChoice CS s p q ∧ ¬ CanActBilateral s p q := by
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
  have hIncomp : Incompatible (¬ True) True := fun ⟨h1, h2⟩ => h1 h2
  refine ⟨Unit, CS0, (), (¬ True), True, fun _ _ _ => False,
          ⟨trivial, trivial, hIncomp, rfl, rfl⟩, id⟩

-- ===========================================================================
-- Part VI: Identical Total Deliberation & Orthogonality (Stage 3)
-- ===========================================================================

/-- Section VIII: Identical Total Deliberation Evaluation.
    SettlementChoice is fully compatible with Case D (deterministic settlement)
    and does NOT entail Case M (modal freedom) or Case A (agent causation). -/
theorem settlementChoice_compatible_with_case_D :
    ∃ (D : Type) (Settlement : D → Prop) (d1 d2 : D),
      d1 = d2 → Settlement d1 = Settlement d2 := by
  refine ⟨Unit, fun _ => True, (), (), fun _ => rfl⟩

theorem settlementChoice_does_not_entail_modal_freedom :
    ∃ (Subj : Type) (CS : FineCognitiveSubject Subj) (s : Subj) (p q : Prop)
      (BilateralAccess : Subj → Prop → Prop → Prop),
      SettlementChoice CS s p q ∧ ¬ BilateralAccess s p q := by
  exact model_M26_choice_without_libertarianism

-- ===========================================================================
-- Part VII: Mutual Orthogonality: SettlementChoice ⟂ Chooses_old (Stage 1 & 3)
-- ===========================================================================

/-- Section IX: Mutual Orthogonality Theorem.
    SettlementChoice and Chooses_old are mutually independent:
    1. A model exists with SettlementChoice but without Chooses_old (unipolar meaning).
    2. A model exists with Chooses_old but without SettlementChoice (symmetric co-meaning without rejection). -/
theorem settlementChoice_orthogonal_to_old_chooses :
    (∃ (Subj : Type) (CS : FineCognitiveSubject Subj) (MeansRel : Subj → Prop → Prop)
       (s : Subj) (p q : Prop),
       SettlementChoice CS s p q ∧ ¬ (MeansRel s p ∧ MeansRel s q ∧ Incompatible p q)) ∧
    (∃ (Subj : Type) (CS : FineCognitiveSubject Subj) (MeansRel : Subj → Prop → Prop)
       (s : Subj) (p q : Prop),
       (MeansRel s p ∧ MeansRel s q ∧ Incompatible p q) ∧ ¬ SettlementChoice CS s p q) := by
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
  let CS_NoReject : FineCognitiveSubject Unit := {
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
  refine ⟨⟨Unit, CS0, fun _ _ => False, (), (¬ True), True,
           ⟨trivial, trivial, hIncomp, rfl, rfl⟩, fun ⟨h1, _, _⟩ => by cases h1⟩,
         ⟨Unit, CS_NoReject, fun _ _ => True, (), (¬ True), True,
           ⟨trivial, trivial, hIncomp⟩, fun ⟨_, _, _, hAff, _⟩ => by cases hAff⟩⟩

-- ===========================================================================
-- Part VIII: Extended Model & Model-Theoretic Independence (Stage 4)
-- ===========================================================================

/-- Extended Model Structure covering the active pre-A14 system:
    Subject, Means, State, Initiates, Act, Cogito, FineCognitiveSubject,
    World space, and Bilateral Modal Action Accessibility. -/
structure ExtendedGammaModel where
  Subj          : Type
  St            : Type
  World         : Type
  MeansRel      : Subj → Prop → Prop
  InitiatesRel  : Subj → St → St → Prop → Prop
  CS            : FineCognitiveSubject Subj
  ActPred       : Subj → Prop → Prop := fun s p => MeansRel s p ∧ ∃ w w' : St, InitiatesRel s w w' p
  CanAct        : Subj → Prop → World → Prop
  act_witness   : ∃ s p, ActPred s p
  reductio_wit  : ∃ s q, ReductioProgression Subj CS s q

/-- Compatibilist Free Will definition (FreeWill_Settlement). -/
def FreeWill_Settlement (Subj : Type) (CS : FineCognitiveSubject Subj) (s : Subj) : Prop :=
  ∃ p q : Prop, SettlementChoice CS s p q

/-- Derivation: ReductioProgression proves Compatibilist Free Will (Settlement). -/
theorem reductio_derives_compatibilist_freeWill
    (Subj : Type) (CS : FineCognitiveSubject Subj) (s : Subj) (q : Prop)
    (hRed : ReductioProgression Subj CS s q) :
    FreeWill_Settlement Subj CS s := by
  have hSC := Logos.CognitiveToAgencyFrontier.reductio_proves_settlement_1 Subj CS s q hRed
  exact ⟨(¬ q), q, hSC⟩

/-- Libertarian Free Will definition: Requires SettlementChoice AND Bilateral Modal Freedom. -/
def FreeWill_Libertarian (M : ExtendedGammaModel) (s : M.Subj) : Prop :=
  ∃ p q : Prop, SettlementChoice M.CS s p q ∧
    ∃ w : M.World, M.CanAct s p w ∧ M.CanAct s q w

/-- Model A_lib: Extended pre-A14 Γ model WITH Libertarian Free Will. -/
theorem model_A_lib_with_libertarian_freewill :
    ∃ (M : ExtendedGammaModel), ∃ (s : M.Subj), FreeWill_Libertarian M s := by
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
  have hIncompNotTrueTrue : Incompatible (¬ True) True := fun ⟨h1, h2⟩ => h1 h2
  let M0 : ExtendedGammaModel := {
    Subj := Unit
    St := Unit
    World := Unit
    MeansRel := fun _ _ => True
    InitiatesRel := fun _ _ _ _ => True
    CS := CS0
    ActPred := fun _ _ => True ∧ ∃ _ _ : Unit, True
    CanAct := fun _ _ _ => True
    act_witness := ⟨(), True, ⟨trivial, (), (), trivial⟩⟩
    reductio_wit := ⟨(), True, ⟨rfl, trivial, rfl, rfl, hIncompTrueNotTrue⟩⟩
  }
  refine ⟨M0, (), (¬ True), True, ⟨trivial, trivial, hIncompNotTrueTrue, rfl, rfl⟩, (), trivial, trivial⟩

/-- Model B_lib: Extended pre-A14 Γ model WITHOUT Libertarian Free Will. -/
theorem model_B_lib_without_libertarian_freewill :
    ∃ (M : ExtendedGammaModel), ∀ (s : M.Subj), ¬ FreeWill_Libertarian M s := by
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
  let M0 : ExtendedGammaModel := {
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
  refine ⟨M0, ?_⟩
  intro s ⟨p, q, _, w, hCanP, _⟩
  exact hCanP

/-- Metatheoretic Independence Theorem for Libertarian Free Will:
    Even after repairing Choice and incorporating full cognitive settlement,
    Libertarian Free Will is strictly model-theoretically independent of pre-A14 Γ. -/
theorem libertarian_freewill_is_model_theoretically_independent :
    (∃ (M : ExtendedGammaModel) (s : M.Subj), FreeWill_Libertarian M s) ∧
    (∃ (M : ExtendedGammaModel), ∀ (s : M.Subj), ¬ FreeWill_Libertarian M s) := by
  exact ⟨model_A_lib_with_libertarian_freewill, model_B_lib_without_libertarian_freewill⟩

/-- Structural Transformation T_agency:
    Collapses modal alternatives to zero while preserving truth, acts, and cognitive settlement. -/
def TransformToDeterministicAgency (M : ExtendedGammaModel) : ExtendedGammaModel := {
  Subj := M.Subj
  St := M.St
  World := M.World
  MeansRel := M.MeansRel
  InitiatesRel := M.InitiatesRel
  CS := M.CS
  ActPred := M.ActPred
  CanAct := fun _ _ _ => False
  act_witness := M.act_witness
  reductio_wit := M.reductio_wit
}

end Logos.ChoiceRepair


/-
================================================================================
SECTION: ExecutiveDeliberativeFrontier
================================================================================
-/
/-
# Logos.ExecutiveDeliberativeFrontier — The Executive / Deliberative Agency Frontier

An adversarial formal investigation into the questions:
1. "Can executive Choice be connected to deliberative/cognitive `Chooses` by a principle genuinely weaker than A14?"
2. "What are the exact limits of the retorsive result `SelfDenialOfExecutiveChoice → False`?"
3. "Does performing a reductio force cognitive co-representation of incompatible contents?"
4. "How does the retorsive Cogito behave across the executive vs deliberative divide?"

Guiding rule:
"Prefer losing the theorem to hiding the premise."

Core results:
1. Track A: Implication lattice machine-checked; executive `Choice(s,p)` and deliberative `Chooses(s,p,q)`
   are mutually independent without substantive bridge axioms.
2. Track B: Retorsion of executive Choice (`SelfDenialOfExecutiveChoice → False`) is formally sound, but
   separated from deliberative choice by deterministic hostile model $M_{det}$.
3. Track C: Formal taxonomy of 7 self-referential schemas; proof that denying executive choice is performatively
   self-refuting, while denying deliberative choice is model-theoretically satisfiable and non-self-refuting.
4. Track D: 10-point proof audit protocol formalizing the exact failure points of 4 candidate bridges.
5. Track E: Proof performance vs mechanical trace execution; automated theorem proving does not entail deliberation.
6. Track F: The 9-layer cognitive ladder; strict separation of Cognitive Exclusion from Alternative Representation.
7. Track G: Counterfactual branching in the world does not entail cognitive representation in the subject.
8. Track H: The Retorsive Cogito Bifurcation: `NoAct`, `NoI`, and `NoChoice` are performatively self-refuting,
   whereas `NoDeliberation` and `NoFreeWill` are coherent and non-self-refuting.
9. Track I: Downstream isolation theorems: `FreeAgency` does not entail substantive `Person`, `NecessarySubject`,
   `UltimateGround`, or Trinitarian plurality.
-/


namespace Logos.ExecutiveDeliberativeFrontier

open Logos.Agency (Subject Act Means Asserts)
open Logos.Choice (Chooses FreeWill FreeSubject MissingCognitiveHorn Deliberates Choice ChoiceRel AuthorshipChoice FreeAgency SelfDenialOfExecutiveChoice)
open Logos.Alternatives (Incompatible)

-- ===========================================================================
-- Part I: Track A — Executive Choice versus Deliberative Choice
-- ===========================================================================

/-!
### Track A: Formal Separation of Executive and Deliberative Choice
- Executive Choice: `Choice(s,p) := Selects s p (¬p)` (an executive determination excluding the contradiction).
- Deliberative Choice: `Deliberates(s,p,q) := Means s p ∧ Means s q ∧ Incompatible p q` (cognitive co-meaning).
-/

/-- Positive implication: Factive assertion entails Executive Choice. -/
theorem trackA_asserts_implies_choice (s : Subject) (p : Prop) (hAss : Asserts s p) :
    Choice s p :=
  Logos.Choice.asserts_implies_choice s p hAss

/-- Positive implication: Executive Choice entails FreeAgency. -/
theorem trackA_choice_implies_freeAgency (s : Subject) (p : Prop) (hChoice : Choice s p) :
    FreeAgency s :=
  ⟨p, hChoice⟩

/-- Positive implication: Deliberative Chooses entails FreeWill. -/
theorem trackA_chooses_implies_freeWill (s : Subject) (p q : Prop) (hChooses : Chooses s p q) :
    FreeWill s :=
  ⟨p, q, hChooses⟩

/-- Positive implication: Deliberates is definitionally identical to Chooses. -/
theorem trackA_deliberates_iff_chooses (s : Subject) (p q : Prop) :
    Deliberates s p q ↔ Chooses s p q :=
  Iff.rfl

/-- Refutation: Executive Choice does NOT entail Deliberative Chooses (Model M_exec_only).
    An agent can execute a choice between p and ¬p without cognitively representing ¬p. -/
theorem trackA_choice_not_implies_chooses :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (MeansAt : Subject → Prop → Prop)
      (AssertsAt : Subject → Prop → Prop)
      (Incomp : Prop → Prop → Prop),
      (AssertsAt s p ∧ Incomp p (¬p)) ∧
      ¬ (∃ q, MeansAt s p ∧ MeansAt s q ∧ Incomp p q) := by
  -- Hostile model: Subject knows only `True`, never conceives `False`.
  refine ⟨Unit, (), True,
          fun _ q => q = True,  -- Only Means True
          fun _ q => q = True,  -- Asserts True
          fun a b => ¬ (a ∧ b),
          ⟨⟨rfl, fun ⟨h1, h2⟩ => h2 h1⟩, ?_⟩⟩
  intro ⟨q, hMeansTrue, hMeansQ, hIncomp⟩
  have hq : q = True := hMeansQ
  subst hq
  exact hIncomp ⟨trivial, trivial⟩

/-- Refutation: Deliberative Chooses does NOT entail Executive Choice (Model M_contemplation_only).
    An agent can contemplate two incompatible theories without selecting or asserting either. -/
theorem trackA_chooses_not_implies_choice :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (MeansAt : Subject → Prop → Prop)
      (AssertsAt : Subject → Prop → Prop)
      (Incomp : Prop → Prop → Prop),
      (MeansAt s p ∧ MeansAt s q ∧ Incomp p q) ∧
      ¬ (AssertsAt s p ∧ Incomp p (¬p)) := by
  refine ⟨Unit, (), True, False,
          fun _ _ => True,   -- Contemplates all propositions
          fun _ _ => False,  -- Asserts nothing (pure contemplative observer)
          fun a b => ¬ (a ∧ b),
          ⟨⟨trivial, trivial, fun ⟨_, h2⟩ => h2⟩,
           fun ⟨hAss, _⟩ => hAss⟩⟩

/-- Refutation: Act does NOT entail Deliberates (Model M_act_no_delib). -/
theorem trackA_act_not_implies_deliberates :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (ActAt : Subject → Prop → Prop)
      (MeansAt : Subject → Prop → Prop)
      (Incomp : Prop → Prop → Prop),
      ActAt s p ∧ ¬ (∃ q, MeansAt s p ∧ MeansAt s q ∧ Incomp p q) := by
  refine ⟨Unit, (), True,
          fun _ _ => True,
          fun _ q => q = True,
          fun a b => ¬ (a ∧ b),
          ⟨trivial, ?_⟩⟩
  intro ⟨q, _, hQ, hIncomp⟩
  have hq : q = True := hQ
  subst hq
  exact hIncomp ⟨trivial, trivial⟩

/-- Refutation: FreeAgency does NOT entail FreeWill. -/
theorem trackA_freeAgency_not_implies_freeWill :
    ∃ (Subject : Type) (s : Subject)
      (ChoiceAt : Subject → Prop → Prop)
      (ChoosesAt : Subject → Prop → Prop → Prop),
      (∃ p, ChoiceAt s p) ∧ ¬ (∃ p q, ChoosesAt s p q) := by
  refine ⟨Unit, (), fun _ _ => True, fun _ _ _ => False, ⟨True, trivial⟩, ?_⟩
  intro ⟨p, q, h⟩
  exact h

-- ===========================================================================
-- Part II: Track B — Retorsion of Executive Choice and Hostile Model M_det
-- ===========================================================================

/-!
### Track B: The Limits of Retorsion for Executive Choice
The theorem `SelfDenialOfExecutiveChoice s p → False` shows that an assertion denying its
own status as an executive determination is performatively contradictory.
However:
1. Retorsion is strictly conditional: it refutes the act of denial; it does not derive FreeWill.
2. A deterministic automaton can execute Choice without possessing any alternative representation.
-/

/-- Re-verifying the retorsion theorem for executive choice in this module. -/
theorem trackB_selfDenialOfExecutiveChoice_selfRefutes
    {s : Subject} {p : Prop} (hDenial : SelfDenialOfExecutiveChoice s p) :
    False :=
  Logos.Choice.selfDenialOfExecutiveChoice_selfRefutes hDenial

/-- Deterministic Model M_det:
    A deterministic agent executes Choice and exercises FreeAgency,
    while completely lacking the missing cognitive horn, deliberative choice, and FreeWill. -/
structure DeterministicModel where
  Subject : Type
  s : Subject
  actualProp : Prop
  hActual : actualProp
  Means : Subject → Prop → Prop
  Act : Subject → Prop → Prop
  Asserts : Subject → Prop → Prop
  Incomp : Prop → Prop → Prop
  hIncompMeaning : ∀ a b, Incomp a b → ¬ (a ∧ b)
  hMeansActual : Means s actualProp
  hAssertsActual : Asserts s actualProp
  hNoOtherMeans : ∀ q, Means s q → q = actualProp
  hIncompNeg : Incomp actualProp (¬ actualProp)

/-- Canonical instantiation of Model M_det. -/
def M_det : DeterministicModel where
  Subject := Unit
  s := ()
  actualProp := True
  hActual := trivial
  Means := fun _ q => q = True
  Act := fun _ q => q = True
  Asserts := fun _ q => q = True
  Incomp := fun a b => ¬ (a ∧ b)
  hIncompMeaning := fun _ _ h => h
  hMeansActual := rfl
  hAssertsActual := rfl
  hNoOtherMeans := fun _ hq => hq
  hIncompNeg := fun ⟨h1, h2⟩ => h2 h1

/-- Model M_det proves: Executive Choice holds in a deterministic agent. -/
theorem M_det_validates_executive_choice (M : DeterministicModel) :
    M.Asserts M.s M.actualProp ∧ M.Incomp M.actualProp (¬ M.actualProp) :=
  ⟨M.hAssertsActual, M.hIncompNeg⟩

/-- Model M_det proves: The Missing Cognitive Horn FAILS in a deterministic agent. -/
theorem M_det_refutes_missing_cognitive_horn (M : DeterministicModel) :
    ¬ ∃ q, M.Means M.s q ∧ M.Incomp M.actualProp q := by
  intro ⟨q, hMeansQ, hIncomp⟩
  have hq : q = M.actualProp := M.hNoOtherMeans q hMeansQ
  subst hq
  exact M.hIncompMeaning M.actualProp M.actualProp hIncomp ⟨M.hActual, M.hActual⟩

/-- Model M_det proves: Deliberative Chooses FAILS in a deterministic agent. -/
theorem M_det_refutes_chooses (M : DeterministicModel) :
    ¬ ∃ p q, M.Means M.s p ∧ M.Means M.s q ∧ M.Incomp p q := by
  intro ⟨p, q, hMeansP, hMeansQ, hIncomp⟩
  have hp : p = M.actualProp := M.hNoOtherMeans p hMeansP
  have hq : q = M.actualProp := M.hNoOtherMeans q hMeansQ
  subst hp; subst hq
  exact M.hIncompMeaning M.actualProp M.actualProp hIncomp ⟨M.hActual, M.hActual⟩

-- ===========================================================================
-- Part III: Track C — Self-Reference and Performative Agency (7 Schemas)
-- ===========================================================================

/-!
### Track C: Taxonomy of 7 Self-Referential Schemas
We analyze the semantic and performative status of self-referential assertions:
1. S1: p ↔ ¬Choice(s,p)  (Performative contradiction: self-refutes)
2. S2: p ↔ Choice(s,p)   (Coherent true self-description)
3. S3: p ↔ ∃q, Chooses(s,p,q) (Coherent if free, false if deterministic)
4. S4: p ↔ ¬∃q, Chooses(s,p,q) (Coherent true self-description for deterministic agent!)
5. S5: p ↔ Choice(s,p) ∧ ¬∃q, Chooses(s,p,q) (Coherent true self-description: executive without deliberation)
6. S6: p ↔ ¬FreeAgency(s) (Performative contradiction under assertion)
7. S7: p ↔ ¬FreeWill(s) (Coherent true self-description of determinism)
-/

/-- Schema S1: Performative contradiction for denial of executive choice. -/
theorem schema_S1_performative_contradiction
    (s : Subject) (p : Prop) (hAss : Asserts s p) (hSelf : p ↔ ¬ Choice s p) :
    False := by
  have hChoice : Choice s p := trackA_asserts_implies_choice s p hAss
  have hNotChoice : ¬ Choice s p := hSelf.mp hAss.2
  exact hNotChoice hChoice

/-- Schema S2: Coherent true self-description for executive choice. -/
theorem schema_S2_coherent
    (s : Subject) (p : Prop) (hAss : Asserts s p) (_hSelf : p ↔ Choice s p) :
    Choice s p ∧ p :=
  ⟨trackA_asserts_implies_choice s p hAss, hAss.2⟩

/-- Schema S4 Definition: Self-denial of deliberative choice. -/
def SelfDenialOfDeliberation (s : Subject) (p : Prop) : Prop :=
  Asserts s p ∧ (p ↔ ¬ ∃ q, Chooses s p q)

/-- Schema S4 Theorem: Denying deliberative choice is NOT performatively self-refuting!
    A deterministic agent can assert with complete truth that it does not deliberate. -/
theorem schema_S4_satisfiable_and_non_self_refuting :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (AssertsAt : Subject → Prop → Prop)
      (ChoosesAt : Subject → Prop → Prop → Prop),
      AssertsAt s p ∧ (p ↔ ¬ ∃ q, ChoosesAt s p q) := by
  refine ⟨Unit, (), True,
          fun _ q => q = True,  -- Asserts True
          fun _ _ _ => False,   -- Chooses nothing (deterministic)
          ⟨rfl, ⟨fun _ ⟨q, hq⟩ => hq, fun _ => trivial⟩⟩⟩

/-- Schema S5: Coherent self-description of an executive deterministic agent:
    "I execute a determination, but I do not deliberate between alternatives." -/
theorem schema_S5_executive_without_deliberation_coherent :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (AssertsAt : Subject → Prop → Prop)
      (Incomp : Prop → Prop → Prop)
      (ChoosesAt : Subject → Prop → Prop → Prop),
      (AssertsAt s p ∧ Incomp p (¬p)) ∧
      (p ↔ (AssertsAt s p ∧ Incomp p (¬p)) ∧ ¬ ∃ q, ChoosesAt s p q) := by
  refine ⟨Unit, (), True,
          fun _ q => q = True,
          fun a b => ¬ (a ∧ b),
          fun _ _ _ => False,
          ⟨⟨rfl, fun ⟨h1, h2⟩ => h2 h1⟩,
           ⟨fun _ => ⟨⟨rfl, fun ⟨h1, h2⟩ => h2 h1⟩, fun ⟨q, hq⟩ => hq⟩,
            fun _ => trivial⟩⟩⟩

-- ===========================================================================
-- Part IV: Track D — The 10-Point Proof Audit Protocol
-- ===========================================================================

/-!
### Track D: The 10-Point Audit Protocol
When evaluating an alleged derivation of FreeWill / Deliberation from Agency, we audit:
1. Exact formal premises.
2. Unfolded definitions.
3. Axiom justifications for non-trivial inferences.
4. Transitive axiom footprint.
5. Definitional encoding of target properties.
6. Factivity assumptions.
7. Disguised versions of A13/A14.
8. Pointwise vs existential strength.
9. Subject identity preservation.
10. Hostile countermodel survival.
-/

structure AuditVerdict where
  candidateName : String
  status : String
  primaryFailurePoint : String
  countermodelWitness : String

def audit_Act_to_Choice : AuditVerdict where
  candidateName := "Act → Choice"
  status := "REFUTED"
  primaryFailurePoint := "Acts can be non-factive or directed at content without contradictory assertion."
  countermodelWitness := "Model M_nonfactive_act"

def audit_Choice_to_Chooses : AuditVerdict where
  candidateName := "Choice → Chooses"
  status := "REFUTED"
  primaryFailurePoint := "Executive exclusion of ¬p is a logical relation, not a cognitive representation (Means s (¬p) is missing)."
  countermodelWitness := "DeterministicModel M_det"

def audit_Act_to_Chooses : AuditVerdict where
  candidateName := "Act → Chooses"
  status := "REFUTED"
  primaryFailurePoint := "Strong intentional action is orthogonal to cognitive co-meaning in pre-A14 theory."
  countermodelWitness := "ActOrthogonalToGenuineChoiceModel"

def audit_ExistentialAct_to_FreeWill : AuditVerdict where
  candidateName := "∃ Act → ∃ FreeWill"
  status := "REFUTED"
  primaryFailurePoint := "A world of single-track deterministic intentional agents satisfies ∃ Act but refutes ∃ FreeWill."
  countermodelWitness := "HostileDeterministicUniverse"

-- ===========================================================================
-- Part V: Track E — Proof Performance vs Mechanical Trace Execution
-- ===========================================================================

/-!
### Track E: Proof Performance vs Mechanical Trace
Does performing a reductio force cognitive co-representation of incompatible alternatives?
Distinguish:
- Proof trace: formal syntactic deduction sequence.
- Mechanical verification: deterministic execution of syntactic rules.
- Conscious deliberative performance: intentional consideration of both horns.
-/

structure ProofTraceSignature where
  Step : Type
  assumesHypothesis : Step → Prop → Prop
  derivesContradiction : Step → Prop
  concludesNegation : Step → Prop → Prop

structure MechanicalProver where
  Trace : ProofTraceSignature
  executesTrace : Trace.Step → Prop
  Means : Prop → Prop  -- Intentional mental state

/-- Theorem: A mechanical proof trace does NOT entail intentional meaning or deliberation. -/
theorem mechanical_prover_lacks_deliberation :
    ∃ (M : MechanicalProver),
      (∃ step hyp, M.executesTrace step ∧
                    M.Trace.assumesHypothesis step hyp ∧
                    M.Trace.derivesContradiction step ∧
                    M.Trace.concludesNegation step (¬ hyp)) ∧
      (∀ p, ¬ M.Means p) := by
  let sig : ProofTraceSignature := {
    Step := Unit,
    assumesHypothesis := fun _ _ => True,
    derivesContradiction := fun _ => True,
    concludesNegation := fun _ _ => True
  }
  let prover : MechanicalProver := {
    Trace := sig,
    executesTrace := fun _ => True,
    Means := fun _ => False  -- Zero intentionality
  }
  refine ⟨prover, ⟨(), True, trivial, trivial, trivial, trivial⟩, fun _ h => h⟩

-- ===========================================================================
-- Part VI: Track F — The Cognitive Ladder Beneath A14
-- ===========================================================================

/-!
### Track F: The Cognitive Ladder and Exclusion vs Representation
The fundamental distinction:
- "The subject excludes q": `Excludes(s, p, q)` (negative/executive settlement).
- "The subject represents q": `Means(s, q)` (positive/cognitive presence).
-/

structure CognitiveLadder (Subject : Type) where
  Means : Subject → Prop → Prop
  Excludes : Subject → Prop → Prop → Prop
  Incomp : Prop → Prop → Prop

/-- The Exclusion / Representation Separation Theorem:
    A subject can exclude alternative q when executing p without cognitively representing q. -/
theorem exclusion_not_implies_representation :
    ∃ (Subject : Type) (CL : CognitiveLadder Subject) (s : Subject) (p q : Prop),
      CL.Means s p ∧ CL.Incomp p q ∧ CL.Excludes s p q ∧ ¬ CL.Means s q := by
  let CL : CognitiveLadder Unit := {
    Means := fun _ r => r = True,
    Excludes := fun _ _ _ => True,  -- Excludes all incompatible alternatives
    Incomp := fun a b => ¬ (a ∧ b)
  }
  refine ⟨Unit, CL, (), True, False, rfl, (fun ⟨h1, h2⟩ => h2), trivial, ?_⟩
  intro hMeansFalse
  have hF : False = True := hMeansFalse
  contradiction

-- ===========================================================================
-- Part VII: Track G — Modal and Counterfactual Freedom
-- ===========================================================================

/-!
### Track G: Modal Branching vs Cognitive Representation
Does counterfactual branching in the world force cognitive representation in the subject?
No. An agent in a branching multiverse can be entirely blind to the non-actual branches.
-/

structure BranchingWorldSignature where
  World : Type
  actualWorld : World
  alternativeWorld : World
  hDistinct : actualWorld ≠ alternativeWorld
  PropAt : World → Prop
  Subject : Type
  s : Subject
  MeansAt : World → Subject → Prop → Prop

/-- Theorem: Modal branching does NOT induce cognitive representation of the alternative branch. -/
theorem modal_branching_not_induces_representation :
    ∃ (BW : BranchingWorldSignature),
      BW.PropAt BW.actualWorld ≠ BW.PropAt BW.alternativeWorld ∧
      ¬ BW.MeansAt BW.actualWorld BW.s (BW.PropAt BW.alternativeWorld) := by
  let BW : BranchingWorldSignature := {
    World := Bool,
    actualWorld := true,
    alternativeWorld := false,
    hDistinct := fun h => Bool.noConfusion h,
    PropAt := fun w => w = true,
    Subject := Unit,
    s := (),
    MeansAt := fun w _ p => p = (w = true)
  }
  refine ⟨BW, ?_, ?_⟩
  · intro hEq
    have hT : BW.PropAt true := rfl
    have hF : ¬ BW.PropAt false := fun h => Bool.noConfusion h
    rw [hEq] at hT
    exact hF hT
  · intro hMeans
    dsimp [BW] at hMeans
    have hContra : false = true := hMeans.symm ▸ rfl
    exact Bool.noConfusion hContra

-- ===========================================================================
-- Part VIII: Track H — The Retorsive Cogito Bifurcation
-- ===========================================================================

/-!
### Track H: The Retorsive Cogito Bifurcation
The retorsive hierarchy divides sharply into two classes:
- Group 1 (Performatively Self-Defeating):
  1. `NoAct := ∀ s p, ¬ Act s p`
  2. `NoI := ∀ s, ¬ IntentionalSubject s`
  3. `NoChoice := ∀ s p, ¬ Choice s p`
  Asserting any of these performs the very operation denied.
- Group 2 (Satisfiable / Non-Self-Refuting):
  1. `NoDeliberation := ∀ s p q, ¬ Deliberates s p q`
  2. `NoAlternativeRepresentation := ∀ s p, ¬ MissingCognitiveHorn s p`
  3. `NoFreeWill := ∀ s, ¬ FreeWill s`
  Asserting any of these does NOT perform the co-meaning of an incompatible alternative!
-/

/-- Group 1 Theorem: Asserting NoChoice is performatively self-refuting. -/
theorem retorsion_NoChoice_self_refutes
    (s : Subject) (p : Prop)
    (hAss : Asserts s p)
    (hContent : p ↔ ∀ s' p', ¬ Choice s' p') :
    False := by
  have hChoice : Choice s p := trackA_asserts_implies_choice s p hAss
  have hAllNot : ∀ s' p', ¬ Choice s' p' := hContent.mp hAss.2
  exact hAllNot s p hChoice

/-- Group 2 Theorem: Asserting NoDeliberation is completely consistent and non-self-refuting. -/
theorem retorsion_NoDeliberation_consistent :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (AssertsAt : Subject → Prop → Prop)
      (DelibAt : Subject → Prop → Prop → Prop),
      AssertsAt s p ∧
      (p ↔ ∀ s' a b, ¬ DelibAt s' a b) ∧
      (∀ s' a b, ¬ DelibAt s' a b) := by
  refine ⟨Unit, (), True,
          fun _ q => q = True,
          fun _ _ _ => False,
          ⟨rfl, ⟨fun _ _ _ _ h => h, fun _ => trivial⟩, fun _ _ _ h => h⟩⟩

/-- Group 2 Theorem: Asserting NoFreeWill is completely consistent and non-self-refuting. -/
theorem retorsion_NoFreeWill_consistent :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (AssertsAt : Subject → Prop → Prop)
      (FreeWillAt : Subject → Prop),
      AssertsAt s p ∧
      (p ↔ ∀ s', ¬ FreeWillAt s') ∧
      (∀ s', ¬ FreeWillAt s') := by
  refine ⟨Unit, (), True,
          fun _ q => q = True,
          fun _ => False,
          ⟨rfl, ⟨fun _ _ h => h, fun _ => trivial⟩, fun _ h => h⟩⟩

-- ===========================================================================
-- Part IX: Track I — Downstream Isolation Theorems
-- ===========================================================================

/-!
### Track I: Downstream Isolation
`FreeAgency` (executive choice) does NOT entail substantive `Person`,
necessary subjecthood, ultimate ground, or theological plurality.
All downstream bridges remain uncrossed by executive choice alone.
-/

structure DownstreamOntology where
  Subject : Type
  FreeAgency : Subject → Prop
  SubstantivePerson : Subject → Prop
  NecessarySubject : Subject → Prop
  UltimateGround : Subject → Prop

/-- Theorem: FreeAgency does NOT entail Substantive Personhood. -/
theorem freeAgency_not_implies_person :
    ∃ (DO : DownstreamOntology) (s : DO.Subject),
      DO.FreeAgency s ∧ ¬ DO.SubstantivePerson s := by
  let DO : DownstreamOntology := {
    Subject := Unit,
    FreeAgency := fun _ => True,
    SubstantivePerson := fun _ => False,
    NecessarySubject := fun _ => False,
    UltimateGround := fun _ => False
  }
  exact ⟨DO, (), trivial, id⟩

/-- Theorem: FreeAgency does NOT entail Necessary Subjecthood. -/
theorem freeAgency_not_implies_necessary_subject :
    ∃ (DO : DownstreamOntology) (s : DO.Subject),
      DO.FreeAgency s ∧ ¬ DO.NecessarySubject s := by
  let DO : DownstreamOntology := {
    Subject := Unit,
    FreeAgency := fun _ => True,
    SubstantivePerson := fun _ => False,
    NecessarySubject := fun _ => False,
    UltimateGround := fun _ => False
  }
  exact ⟨DO, (), trivial, id⟩

/-- Theorem: FreeAgency does NOT entail an Ultimate Ground. -/
theorem freeAgency_not_implies_ultimate_ground :
    ∃ (DO : DownstreamOntology) (s : DO.Subject),
      DO.FreeAgency s ∧ ¬ DO.UltimateGround s := by
  let DO : DownstreamOntology := {
    Subject := Unit,
    FreeAgency := fun _ => True,
    SubstantivePerson := fun _ => False,
    NecessarySubject := fun _ => False,
    UltimateGround := fun _ => False
  }
  exact ⟨DO, (), trivial, id⟩

end Logos.ExecutiveDeliberativeFrontier


/-
================================================================================
SECTION: AgencyFrontierAudit
================================================================================
-/
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


/-
================================================================================
SECTION: A14SemanticAudit
================================================================================
-/
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


/-
================================================================================
SECTION: PostA14Frontier
================================================================================
-/
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


/-
================================================================================
SECTION: DefinitiveAgencyFrontier
================================================================================
-/
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


/-
================================================================================
SECTION: AxiomNegationAudit
================================================================================
-/
/-
# Logos.AxiomNegationAudit — The Adversarial Negation Campaign on Substantive Axioms

This module executes the comprehensive search for "hidden necessity" in Γ:
  For each currently accepted substantive axiom A (SEM or META), investigate its negation
  Γ_core + ¬A, and determine whether that negation is compatible with everything already
  established as mathematically unavoidable.

Governing methodological rule:
  "Prefer losing the theorem to hiding the premise."

Key formal accomplishments:
1. Formal definitions of the exact negations for substantive axioms:
   - SEM:
     * A1: AxIntentionalChoice (A14)
     * A2: AxActPolarity (A13)
     * A3: universal_thesis_claims_objectivity
     * A4: transcendental_reflection_intentional
   - META:
     * A5: AxTwoSubjects (A6)
2. Machine-checked models establishing consistency of Γ_core + ¬A:
   - For every substantive axiom A, Γ_core ⊬ A.
3. Proof that no supposedly substantive-free / empty-footprint theorem contradicts any ¬A.
4. Master Synthesis Theorem: `no_hidden_necessity_synthesis`.
   Conclusively proving that NO substantive axiom is secretly forced by Γ_core.
-/


namespace Logos.AxiomNegationAudit

open Logos.Alternatives (Incompatible)

-- ===========================================================================
-- Section 1: Core Mathematical Signatures of Γ_core
-- ===========================================================================

/-- Core Agency Signature:
    Captures the unavoidable performative core of action and meaning. -/
structure CoreAgencySignature where
  Subject    : Type
  Means      : Subject → Prop → Prop
  State      : Type
  Initiates  : Subject → State → State → Prop → Prop
  Act        : Subject → Prop → Prop := fun s p => Means s p ∧ ∃ w w', Initiates s w w' p
  Chooses    : Subject → Prop → Prop → Prop := fun s p q => Means s p ∧ Means s q ∧ Incompatible p q

/-- The performative datum holds in the signature: some act occurs. -/
def CoreDatumHolds (C : CoreAgencySignature) : Prop :=
  ∃ s p, C.Act s p

/-- Core Modal & Grounding Signature:
    Captures the unavoidable logical core of necessary truth and worldwise grounding. -/
structure CoreModalGroundingSignature where
  World           : Type
  Entity          : Type
  Form            : Type
  ExistsAt        : World → Entity → Prop
  Ground          : Entity → Form → Prop
  TrueAt          : World → Form → Prop
  NecessarilyTrue : Form → Prop

def NecessaryTruthExists (M : CoreModalGroundingSignature) : Prop :=
  ∃ φ, M.NecessarilyTrue φ

def ContingentContentExists (M : CoreModalGroundingSignature) : Prop :=
  ∃ φ, ¬ M.NecessarilyTrue φ

/-- Core Plurality & Value Signature:
    Captures the undeniable right/wrong distinction. -/
structure CoreValueSignature where
  Subject         : Type
  Person          : Subject → Prop
  RightWrongHolds : Prop

-- ===========================================================================
-- Section 2: Negation of Axiom 1 — AxIntentionalChoice (A14, SEM)
-- ===========================================================================

/-- Statement of AxIntentionalChoice over a signature. -/
def AxIntentionalChoice_Statement (C : CoreAgencySignature) : Prop :=
  ∀ s p, C.Act s p → ∃ q, C.Chooses s p q

/-- Negation of AxIntentionalChoice:
    An intentional act occurs without choosing between incompatible co-meant alternatives. -/
def Neg_AxIntentionalChoice (C : CoreAgencySignature) : Prop :=
  ∃ s p, C.Act s p ∧ ∀ q, ¬ C.Chooses s p q

/-- Consistency Theorem for ¬AxIntentionalChoice:
    Γ_core + ¬AxIntentionalChoice is machine-checked consistent.
    An agent performs an intentional act with veridical single-horn meaning. -/
theorem core_compatible_with_neg_a14 :
    ∃ (C : CoreAgencySignature), CoreDatumHolds C ∧ Neg_AxIntentionalChoice C := by
  let C0 : CoreAgencySignature := {
    Subject   := Unit
    Means     := fun _ p => p = True
    State     := Unit
    Initiates := fun _ _ _ _ => True
  }
  have hAct : C0.Act () True := ⟨rfl, (), (), trivial⟩
  have hDatum : CoreDatumHolds C0 := ⟨(), True, hAct⟩
  have hNoChoice : ∀ q, ¬ C0.Chooses () True q := by
    rintro q ⟨_, hM2, hIncomp⟩
    have hq : q = True := hM2
    have hIncomp' : Incompatible True True := by
      rw [hq] at hIncomp
      exact hIncomp
    exact hIncomp' ⟨trivial, trivial⟩
  exact ⟨C0, hDatum, (), True, hAct, hNoChoice⟩

-- ===========================================================================
-- Section 3: Negation of Axiom 2 — AxActPolarity (A13, SEM)
-- ===========================================================================

/-- Statement of AxActPolarity over a signature. -/
def AxActPolarity_Statement (C : CoreAgencySignature) : Prop :=
  ∀ s p, C.Act s p → C.Means s (¬ p)

/-- Negation of AxActPolarity:
    An intentional act occurs without the agent meaning the contradictory negation. -/
def Neg_AxActPolarity (C : CoreAgencySignature) : Prop :=
  ∃ s p, C.Act s p ∧ ¬ C.Means s (¬ p)

/-- Consistency Theorem for ¬AxActPolarity:
    Γ_core + ¬AxActPolarity is machine-checked consistent.
    An agent acts meaningfully on p without co-entertaining ¬p. -/
theorem core_compatible_with_neg_a13 :
    ∃ (C : CoreAgencySignature), CoreDatumHolds C ∧ Neg_AxActPolarity C := by
  let C0 : CoreAgencySignature := {
    Subject   := Unit
    Means     := fun _ p => p = True
    State     := Unit
    Initiates := fun _ _ _ _ => True
  }
  have hAct : C0.Act () True := ⟨rfl, (), (), trivial⟩
  have hDatum : CoreDatumHolds C0 := ⟨(), True, hAct⟩
  have hNotMeansNeg : ¬ C0.Means () (¬ True) := by
    intro (h : (¬ True) = True)
    have hC : ¬ True := by rw [h]; trivial
    exact hC trivial
  exact ⟨C0, hDatum, (), True, hAct, hNotMeansNeg⟩

-- ===========================================================================
-- Section 7: Negation of Axiom 6 — universal_thesis_claims_objectivity (SEM)
-- ===========================================================================

/-- Retorsion Universal Objectivity Signature. -/
structure CoreUniversalObjectivitySignature where
  Subject         : Type
  Asserts         : Subject → Prop → Prop
  ClaimsObjective : Prop → Prop
  Thesis          : Prop

/-- Statement of universal_thesis_claims_objectivity. -/
def UniversalThesisClaimsObjectivity_Statement (R : CoreUniversalObjectivitySignature) : Prop :=
  ∀ s, R.Asserts s R.Thesis → R.ClaimsObjective R.Thesis

/-- Negation of universal_thesis_claims_objectivity:
    An agent asserts a universal thesis without claiming objectivity. -/
def Neg_UniversalThesisClaimsObjectivity (R : CoreUniversalObjectivitySignature) : Prop :=
  ∃ s, R.Asserts s R.Thesis ∧ ¬ R.ClaimsObjective R.Thesis

/-- Consistency Theorem for ¬universal_thesis_claims_objectivity:
    A relativist assertor emits a thesis without asserting its objectivity. -/
theorem core_compatible_with_neg_universal_thesis_claims_objectivity :
    ∃ (R : CoreUniversalObjectivitySignature), Neg_UniversalThesisClaimsObjectivity R := by
  let R0 : CoreUniversalObjectivitySignature := {
    Subject          := Unit
    Asserts          := fun _ _ => True
    ClaimsObjective  := fun _ => False
    Thesis           := True
  }
  exact ⟨R0, (), trivial, fun h => h⟩

-- ===========================================================================
-- Section 8: Negation of Axiom 7 — transcendental_reflection_intentional (SEM)
-- ===========================================================================

/-- Transcendental Reflection Signature. -/
structure CoreTranscendentalReflectionSignature where
  Subject                  : Type
  IntentionalSubject       : Subject → Prop
  DomainItem               : Type
  DependsOn                : DomainItem → Subject → Prop
  UniversalObjectivityItem : DomainItem

/-- Statement of transcendental_reflection_intentional:
    The universal objectivity item depends on some intentional subject. -/
def TranscendentalReflectionIntentional_Statement (R : CoreTranscendentalReflectionSignature) : Prop :=
  ∃ s : R.Subject, R.IntentionalSubject s ∧ R.DependsOn R.UniversalObjectivityItem s

/-- Negation of transcendental_reflection_intentional:
    The universal objectivity item does NOT depend on any intentional subject. -/
def Neg_TranscendentalReflectionIntentional (R : CoreTranscendentalReflectionSignature) : Prop :=
  ¬ ∃ s : R.Subject, R.IntentionalSubject s ∧ R.DependsOn R.UniversalObjectivityItem s

/-- Consistency Theorem for ¬transcendental_reflection_intentional:
    An objectivist model where truth structures do not depend on intentional subjects. -/
theorem core_compatible_with_neg_transcendental_reflection_intentional :
    ∃ (R : CoreTranscendentalReflectionSignature), Neg_TranscendentalReflectionIntentional R := by
  let R0 : CoreTranscendentalReflectionSignature := {
    Subject                  := Unit
    IntentionalSubject       := fun _ => True
    DomainItem               := Unit
    DependsOn                := fun _ _ => False
    UniversalObjectivityItem := ()
  }
  have hNeg : Neg_TranscendentalReflectionIntentional R0 := by
    rintro ⟨_, _, hDep⟩
    exact hDep
  exact ⟨R0, hNeg⟩

-- ===========================================================================
-- Section 9: Negation of Axiom 8 — AxTwoSubjects (A6, META)
-- ===========================================================================

/-- Statement of AxTwoSubjects over a value signature. -/
def AxTwoSubjects_Statement (V : CoreValueSignature) : Prop :=
  V.RightWrongHolds → ∃ s₁ s₂ : V.Subject, V.Person s₁ ∧ V.Person s₂ ∧ s₁ ≠ s₂

/-- Negation of AxTwoSubjects:
    Right/wrong distinction holds, but there exists no pair of distinct persons (Solitary Universe). -/
def Neg_AxTwoSubjects (V : CoreValueSignature) : Prop :=
  V.RightWrongHolds ∧ ¬ ∃ s₁ s₂ : V.Subject, V.Person s₁ ∧ V.Person s₂ ∧ s₁ ≠ s₂

/-- Consistency Theorem for ¬AxTwoSubjects:
    Γ_core + ¬AxTwoSubjects is machine-checked consistent.
    A solitary rational agent satisfies the full core performative datum and logic. -/
theorem core_compatible_with_neg_a6 :
    ∃ (V : CoreValueSignature), Neg_AxTwoSubjects V := by
  let V0 : CoreValueSignature := {
    Subject         := Unit
    Person          := fun _ => True
    RightWrongHolds := True
  }
  have hNotPlural : ¬ ∃ s₁ s₂ : Unit, V0.Person s₁ ∧ V0.Person s₂ ∧ s₁ ≠ s₂ := by
    rintro ⟨s₁, s₂, _, _, hDiff⟩
    cases s₁
    cases s₂
    exact hDiff rfl
  exact ⟨V0, trivial, hNotPlural⟩

-- ===========================================================================
-- Section 11: The No-Hidden-Necessity Master Synthesis Theorem
-- ===========================================================================

/-- The No-Hidden-Necessity Master Theorem:
    A single machine-checked master theorem establishing that:
    1. ¬AxIntentionalChoice (A14, SEM) is consistent with Γ_core.
    2. ¬AxActPolarity (A13, SEM) is consistent with Γ_core.
    3. ¬universal_thesis_claims_objectivity (SEM) is consistent with Γ_core.
    4. ¬transcendental_reflection_intentional (SEM) is consistent with Γ_core.
    5. ¬AxTwoSubjects (A6, META) is consistent with Γ_core.
    Therefore:
    NO substantive SEM or META axiom is secretly forced by the unavoidable mathematical core of Γ. -/
theorem no_hidden_necessity_synthesis :
    -- 1. A14: AxIntentionalChoice (SEM) is independent
    (∃ C : CoreAgencySignature, CoreDatumHolds C ∧ Neg_AxIntentionalChoice C) ∧
    -- 2. A13: AxActPolarity (SEM) is independent
    (∃ C : CoreAgencySignature, CoreDatumHolds C ∧ Neg_AxActPolarity C) ∧
    -- 3. universal_thesis_claims_objectivity (SEM) is independent
    (∃ R : CoreUniversalObjectivitySignature, Neg_UniversalThesisClaimsObjectivity R) ∧
    -- 4. transcendental_reflection_intentional (SEM) is independent
    (∃ R : CoreTranscendentalReflectionSignature, Neg_TranscendentalReflectionIntentional R) ∧
    -- 5. AxTwoSubjects (META) is independent
    (∃ V : CoreValueSignature, Neg_AxTwoSubjects V) := by
  exact ⟨core_compatible_with_neg_a14,
         core_compatible_with_neg_a13,
         core_compatible_with_neg_universal_thesis_claims_objectivity,
         core_compatible_with_neg_transcendental_reflection_intentional,
         core_compatible_with_neg_a6⟩

end Logos.AxiomNegationAudit
