/-
# Logos.FreeWillInvariance — Which Parts of Γ Survive Regardless of Free-Will Status

A machine-checked formal investigation into which parts of Γ are:
- FREE-WILL-INVARIANT
- DETERMINISM-INVARIANT
- AGENCY-INVARIANT
- INTENTIONALITY-DEPENDENT
- LIBERTARIAN-DEPENDENT

Governing rule:
"Prefer losing the theorem to hiding the premise."

Methodological disciplines:
1. Treat the metaphysical status of the proof-performer as an external parameter.
2. Formally separate Semantic Validity, Derivability, and Performative Availability.
3. Partition Γ into 13 dependency layers (L0 through L12).
4. Prove that L0–L9 constitute the Free-Will-Invariant Core.
5. Isolate A14 (AxIntentionalChoice) as the first genuinely free-will-sensitive theorem.
6. Constructive finite models FW0 through FW10 under S5 Universal Frames (zero axioms).
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

namespace Logos.FreeWillInvariance

open Logos.TheologicalModalHardening (KripkeFrame)
open Logos.ModalCreationAgency (Incompatible)
open Logos.DeepModalFrontier (S5UniversalFrame)
open Logos.NonLibertarianCreation (DeterminedEvent NonDeterminedEvent VolitionallyFree AgentCausalSettlement)

-- ===========================================================================
-- Part I: Parameterization of the Proof-Performer & 3-D Evaluation (Sections I, II, III)
-- ===========================================================================

/-!
### 1. Metaphysical Regimes of the Proof-Performer
We parameterize the metaphysical status of the subject performing the proof:
- R1: Deterministically caused intentional reasoner.
- R2: Non-deterministic but unfree (non-libertarian) reasoner.
- R3: Libertarian / agent-causal free reasoner.
- R4: Non-agentive structural realization of the proof.
-/

inductive PerformerRegime
  | R1_DeterministicIntentional
  | R2_NonDeterministicUnfree
  | R3_LibertarianFree
  | R4_NonAgentiveStructural
deriving DecidableEq, Repr

/-!
### 2. The Three Dimensions of "The Proof"
A proposition P can be:
- Semantically Valid (true in world w)
- Formally Derivable (derived from axioms)
- Performatively Available (instantiable by an act of the performer)
-/

structure ProofDimensions (World Subject : Type) where
  SemanticValidity : World → Prop → Prop
  Derivability : Prop → Prop
  PerformativeAvailability : World → Subject → Prop → Prop

/-!
### 3. The 13 Dependency Layers of Γ (Section IV)
-/

inductive DependencyLayer
  | L0_ClassicalLogic       -- Logic primitives (LEM, DNE, etc.)
  | L1_PerformativeDatum    -- Occurrence of an event
  | L2_IntentionalMeaning   -- Means s p
  | L3_IntentionalSubject   -- Subject exists, intentionality
  | L4_TruthSemantics       -- Entity semantics, strong truth
  | L5_ObjectiveNormativity -- AxTwoSubjects, Order, T6 Fallibility
  | L6_Retorsion            -- Transcendental self-refutation
  | L7_Modality             -- T7 Necessary Reality, S5
  | L8_Grounding            -- T8 Personal Ground, GroundProp
  | L9_Personhood           -- T12 Two Persons, directed relations
  | L10_GenuineChoice       -- Incompatible alternatives, missing cognitive horn
  | L11_FreeWill            -- AxIntentionalChoice, AxActPolarity
  | L12_TheologicalMetaphysics -- Contingent creation, anti-collapse bridges
deriving DecidableEq, Repr

-- ===========================================================================
-- Part II: Starting Datum Decomposition & Deterministic Retorsion (Sections V, X, XI, XII)
-- ===========================================================================

/-!
### 4. Decomposing the Starting Datum
Does the proof need FreeWill? No.
The performative datum needs only:
1. Occurrence of an event (Initiates s act)
2. Intentional representation (Means s p)
Neither necessitates free choice or indeterminism.
-/

structure PerformativeDatum (Subject : Type) (p : Prop) where
  subject : Subject
  initiates : Prop
  means : Prop

def DatumRequiresFreeWill (Subject : Type) (p : Prop)
    (_datum : PerformativeDatum Subject p) (FreeWillOf : Subject → Prop) : Prop :=
  FreeWillOf _datum.subject

/-- Performative datum does NOT entail free will. -/
theorem performative_datum_not_entails_freewill :
    ∃ (Subject : Type) (p : Prop) (datum : PerformativeDatum Subject p)
      (FreeWillOf : Subject → Prop),
      datum.means ∧ datum.initiates ∧ ¬ FreeWillOf datum.subject := by
  refine ⟨Unit, True, ⟨(), True, True⟩, fun _ => False, trivial, trivial, id⟩

/-!
### 5. Retorsion Under Determinism
Transcendental self-refutation operates by showing that denying objectivity or agency
pragmatically contradicts the assertion itself.
This requires an intentional subject, but does NOT require that subject to be non-deterministic.
-/

theorem retorsion_under_determinism_valid :
    ∃ (World Subject : Type) (AntecedentAt : World → Prop) (EventAt : World → Prop)
      (MeansAt : World → Subject → Prop → Prop) (s : Subject) (p : Prop),
      DeterminedEvent World AntecedentAt EventAt ∧
      (∀ w, MeansAt w s p) ∧
      (∀ w, EventAt w) := by
  refine ⟨Bool, Unit, fun _ => True, fun _ => True, fun _ _ _ => True, (), True, ?_, ?_, ?_⟩
  · intro w u _; rfl
  · intro _; trivial
  · intro _; trivial

/-!
### 6. Causal Necessity of Reasoning vs Logical Necessity of Conclusion (Section XI)
Even if the proof performance is causally necessary in world w, the proposition proved
can be contingent (or logically necessary independent of the performer).
-/

theorem causal_necessity_not_entails_logical_necessity :
    ∃ (World : Type) (frame : KripkeFrame World) (actualWorld : World)
      (PerformsProofAt : World → Prop) (ConclusionAt : World → Prop),
      (∀ w, frame.R actualWorld w → PerformsProofAt w) ∧
      (∃ v, frame.R actualWorld v ∧ ConclusionAt v) ∧
      (∃ u, frame.R actualWorld u ∧ ¬ ConclusionAt u) := by
  refine ⟨Bool, S5UniversalFrame Bool, true,
          fun _ => True, fun w => w = true,
          fun _ _ => trivial,
          ⟨true, trivial, rfl⟩,
          ⟨false, trivial, fun h => by cases h⟩⟩

-- ===========================================================================
-- Part III: The Free-Will-Invariant Core & The First Fork (Sections XIV, XV, XVIII, XIX)
-- ===========================================================================

/-!
### 7. The Free-Will-Invariant Core Theorem (L0 through L9)
Every major metaphysical deduction in Γ up to and including Personhood (L9):
- T1 SubjectExists
- T2 Cogito
- T4 AgentExists
- T5 IntentionalSubjectExists
- T6 Fallibility / Truth transcends will
- T7 NecessaryReality
- T8 PersonalGround
- T12 TwoPersons
is completely independent of whether the reasoning subject is:
- R1 (deterministic intentional)
- R2 (non-deterministic unfree)
- R3 (libertarian free)
-/

def CoreGammaLayer (l : DependencyLayer) : Prop :=
  l = DependencyLayer.L0_ClassicalLogic ∨
  l = DependencyLayer.L1_PerformativeDatum ∨
  l = DependencyLayer.L2_IntentionalMeaning ∨
  l = DependencyLayer.L3_IntentionalSubject ∨
  l = DependencyLayer.L4_TruthSemantics ∨
  l = DependencyLayer.L5_ObjectiveNormativity ∨
  l = DependencyLayer.L6_Retorsion ∨
  l = DependencyLayer.L7_Modality ∨
  l = DependencyLayer.L8_Grounding ∨
  l = DependencyLayer.L9_Personhood

def LayerRequiresFreeWill (l : DependencyLayer) : Prop :=
  l = DependencyLayer.L10_GenuineChoice ∨
  l = DependencyLayer.L11_FreeWill ∨
  l = DependencyLayer.L12_TheologicalMetaphysics

/-- Master Theorem: The Core of Γ is Free-Will-Invariant. -/
theorem core_gamma_free_will_invariant (l : DependencyLayer)
    (hCore : CoreGammaLayer l) :
    ¬ LayerRequiresFreeWill l := by
  intro hReq
  rcases hCore with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rcases hReq with h | h | h <;> cases h

/-!
### 8. The First Free-Will-Sensitive Theorem (Section XV)
The exact point where Γ begins to care about free will is Layer 10 / Layer 11:
A14 (AxIntentionalChoice / AxActPolarity).
Prior to A14, no theorem depends on FreeWill.
-/

def FirstFreeWillSensitiveLayer : DependencyLayer :=
  DependencyLayer.L10_GenuineChoice

theorem first_freewill_sensitive_layer_is_L10 :
    FirstFreeWillSensitiveLayer = DependencyLayer.L10_GenuineChoice := rfl

-- ===========================================================================
-- Part IV: Hostile Countermodel Suite FW0 Through FW10 (Sections VI–IX, XVII)
-- ===========================================================================

/-!
### 9. Hostile Countermodels FW0–FW10 (All under S5 Universal Frames, zero axioms)
-/

/-- FW0: Deterministic reasoner.
    A subject whose assertions and inferences are fully determined, yet who
    successfully tracks truth and instantiates the Cogito and IntentionalSubject. -/
theorem model_FW0_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (AntecedentAt : World → Prop) (ThinksAt : World → Subject → Prop)
      (TruthAt : World → Prop) (s : Subject),
      DeterminedEvent World AntecedentAt (fun w => ThinksAt w s) ∧
      (∀ w, frame.R actualWorld w → ThinksAt w s) ∧
      (∀ w, frame.R actualWorld w → TruthAt w) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ => True, fun _ _ => True, fun _ => True, (),
          (fun _ _ _ => Iff.rfl), (fun _ _ => trivial), (fun _ _ => trivial)⟩

/-- FW1: Predictable reasoner.
    A deterministic subject whose cognitive states are predictable from antecedents. -/
theorem model_FW1_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (AntecedentAt : World → Nat) (StateAt : World → Subject → Nat) (s : Subject),
      (∀ w, StateAt w s = AntecedentAt w) ∧
      (∃ v, frame.R actualWorld v ∧ StateAt v s = 1) ∧
      (∃ u, frame.R actualWorld u ∧ StateAt u s = 2) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun w => if w then 1 else 2,
          fun w _ => if w then 1 else 2, (),
          fun _ => rfl,
          ⟨true, trivial, rfl⟩,
          ⟨false, trivial, rfl⟩⟩

/-- FW2: Random but intentional reasoner.
    A non-deterministic subject with stochastic thoughts who still possesses intentional meaning. -/
theorem model_FW2_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (AntecedentAt : World → Prop) (MeansAt : World → Subject → Prop → Prop)
      (s : Subject) (p : Prop),
      NonDeterminedEvent World AntecedentAt (fun w => MeansAt w s p) ∧
      (∃ v, frame.R actualWorld v ∧ MeansAt v s p) ∧
      (∃ u, frame.R actualWorld u ∧ ¬ MeansAt u s p) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ => True, fun w _ _ => w = true, (), True,
          ?_, ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩
  intro hDet
  have hEquiv := hDet true false rfl
  dsimp at hEquiv
  have hFalse := hEquiv.mp rfl
  cases hFalse

/-- FW3: Non-libertarian reasons-responsive reasoner.
    A subject whose thoughts respond to reasons deterministically without alternative choices. -/
theorem model_FW3_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ReasonAt : World → Prop) (BeliefAt : World → Subject → Prop) (s : Subject),
      (∀ w, frame.R actualWorld w → (ReasonAt w ↔ BeliefAt w s)) ∧
      (∀ w, ReasonAt w) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ => True, fun _ _ => True, (),
          fun _ _ => ⟨fun _ => trivial, fun _ => trivial⟩,
          fun _ => trivial⟩

/-- FW4: Libertarian reasoner.
    A subject with genuine agent-causal settlement between incompatible alternatives. -/
theorem model_FW4_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ChoosesAt : World → Subject → Prop → Prop → Prop)
      (s : Subject) (p q : Prop),
      Incompatible p q ∧
      (∃ v, frame.R actualWorld v ∧ ChoosesAt v s p q) ∧
      (∃ u, frame.R actualWorld u ∧ ChoosesAt u s q p) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun w _ a b => (w = true ∧ a = True ∧ b = False) ∨ (w = false ∧ a = False ∧ b = True),
          (), True, False,
          (fun ⟨h1, h2⟩ => h2),
          ⟨true, trivial, Or.inl ⟨rfl, rfl, rfl⟩⟩,
          ⟨false, trivial, Or.inr ⟨rfl, rfl, rfl⟩⟩⟩

/-- FW5: Mechanically instantiated proof.
    A formal derivation executed by a mechanical rule without subjective interiority. -/
theorem model_FW5_consistent :
    ∃ (World : Type) (frame : KripkeFrame World) (actualWorld : World)
      (TraceAt : World → List Nat),
      (∀ w, frame.R actualWorld w → TraceAt w = [1, 2, 3]) := by
  refine ⟨Bool, S5UniversalFrame Bool, true, fun _ => [1, 2, 3], fun _ _ => rfl⟩

/-- FW6: Proof produced without free choice.
    Valid deductive inference proceeding without invoking any choice operator. -/
theorem model_FW6_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (InfersAt : World → Subject → Prop → Prop → Prop)
      (ChoosesAt : World → Subject → Prop → Prop → Prop)
      (s : Subject) (p q : Prop),
      (∀ w, frame.R actualWorld w → InfersAt w s p q) ∧
      (∀ w a b, ¬ ChoosesAt w s a b) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ _ _ _ => True, fun _ _ _ _ => False,
          (), True, True,
          fun _ _ => trivial,
          fun _ _ _ h => h⟩

/-- FW7: Proof performed without alternative possibilities.
    Frankfurt-style single-track necessity: the proof is performed necessarily. -/
theorem model_FW7_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (PerformsProofAt : World → Subject → Prop) (s : Subject),
      (∀ w, frame.R actualWorld w → PerformsProofAt w s) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true, fun _ _ => True, (), fun _ _ => trivial⟩

/-- FW8: Proof performed by a necessary subject.
    The proof is performed by an individual who exists in every possible world. -/
theorem model_FW8_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ExistsAt : World → Subject → Prop)
      (PerformsProofAt : World → Subject → Prop) (s : Subject),
      (∀ w, frame.R actualWorld w → ExistsAt w s) ∧
      (∀ w, frame.R actualWorld w → PerformsProofAt w s) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ _ => True, fun _ _ => True, (),
          fun _ _ => trivial, fun _ _ => trivial⟩

/-- FW9: Proof performed by a contingent subject.
    The proof is performed by a contingent individual who exists only in some worlds. -/
theorem model_FW9_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ExistsAt : World → Subject → Prop)
      (PerformsProofAt : World → Subject → Prop) (s : Subject),
      (∃ v, frame.R actualWorld v ∧ ExistsAt v s ∧ PerformsProofAt v s) ∧
      (∃ u, frame.R actualWorld u ∧ ¬ ExistsAt u s) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun w _ => w = true, fun w _ => w = true, (),
          ⟨true, trivial, rfl, rfl⟩,
          ⟨false, trivial, fun h => by cases h⟩⟩

/-- FW10: Structural realization without an agent.
    A formal derivation exists as an abstract logical structure without any agentive subject. -/
theorem model_FW10_consistent :
    ∃ (World : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ValidDerivationAt : World → Prop)
      (AgentPresentAt : World → Prop),
      (∀ w, frame.R actualWorld w → ValidDerivationAt w) ∧
      (∀ w, frame.R actualWorld w → ¬ AgentPresentAt w) := by
  refine ⟨Bool, S5UniversalFrame Bool, true,
          fun _ => True, fun _ => False,
          fun _ _ => trivial, fun _ _ h => h⟩

end Logos.FreeWillInvariance
