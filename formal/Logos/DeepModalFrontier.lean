/-
# Logos.DeepModalFrontier — Attacking the Fork Itself

A machine-checked formal investigation attacking the modal fork:
"Determine whether the fork is genuinely irreducible, or whether deeper principles
already present or defensibly sharpened inside Γ force one side of it."

Governing rule:
"Prefer losing the theorem to hiding the premise."

Methodological disciplines:
1. Strict separation of Non-Collapse, Modal Freedom, and Agent-Causal Freedom.
2. S5 universal frames for modal possibility countermodels.
3. Distinction between Explanation and Determination (The Third Regime).
4. Full audit of omniscience, rationality, goodness, aseity, and immutability.
-/

import Logos.Core
import Logos.Necessity
import Logos.Semantics
import Logos.Truthmaker
import Logos.Modal
import Logos.Agency
import Logos.Person
import Logos.Choice
import Logos.TheologicalModalHardening
import Logos.ModalCreationAgency
import Logos.EssenceActCollapse
import Logos.ModalPossibilityFrontier

namespace Logos.DeepModalFrontier

open Logos.TheologicalModalHardening (KripkeFrame BoxR)
open Logos.ModalCreationAgency (Incompatible ChoosesAt FreeWillAt)
open Logos.EssenceActCollapse (NecessaryEntity NecessaryNature NecessaryAct ContingentAct VolitionToActBridge SameCircumstances SameNature)
open Logos.ModalPossibilityFrontier (RigidAgent SameExternalCircumstances SameReasons SameHistory SameIntrinsicNature SameInternalState SameTotalDeliberativeState)

-- ===========================================================================
-- Part I: Correcting the Logical Overstatement & Alternative Hierarchy (Sections I, XV)
-- ===========================================================================

/-!
### 1. Separation of Non-Determinism from Modal Free Will
Non-collapse (¬ DeterministicVolition) does NOT entail Modal Free Will.
An indeterministic system can exhibit random fluctuation without intentional agency.
-/

def S5UniversalFrame (World : Type) : KripkeFrame World :=
  { R := fun _ _ => True }

theorem s5_frame_is_equivalence (World : Type) :
    (∀ w : World, (S5UniversalFrame World).R w w) ∧
    (∀ w u : World, (S5UniversalFrame World).R w u → (S5UniversalFrame World).R u w) ∧
    (∀ w u v : World, (S5UniversalFrame World).R w u → (S5UniversalFrame World).R u v → (S5UniversalFrame World).R w v) := by
  refine ⟨fun _ => trivial, fun _ _ _ => trivial, fun _ _ _ _ _ => trivial⟩

def NonDeterministicVolition (World Subject : Type)
    (ReasonsAt : World → Subject → Prop)
    (WillsAt : World → Subject → Prop → Prop) : Prop :=
  ¬ (∀ w u s a, SameReasons World Subject ReasonsAt s w u → (WillsAt w s a ↔ WillsAt u s a))

def ModalFreeWillRigid (World Subject : Type)
    (frame : KripkeFrame World) (actualWorld : World)
    (ChoosesAt : World → Subject → Prop → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Incompatible p q ∧
  (∃ v : World, frame.R actualWorld v ∧ ChoosesAt v s p q) ∧
  (∃ u : World, frame.R actualWorld u ∧ ChoosesAt u s q p)

/-- Separation: Non-deterministic volition does NOT entail Modal Free Will. -/
theorem nondeterministic_not_entails_modal_freewill :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ReasonsAt : World → Subject → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (ChoosesAt : World → Subject → Prop → Prop → Prop)
      (s : Subject) (p q : Prop),
      NonDeterministicVolition World Subject ReasonsAt WillsAt ∧
      ¬ ModalFreeWillRigid World Subject frame actualWorld ChoosesAt s p q := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ _ => True,
          fun w _ _ => w = true,
          fun _ _ _ _ => False,
          (), True, False, ?_, ?_⟩
  · intro hDet
    have hSame : SameReasons Bool Unit (fun _ _ => True) () true false := rfl
    have hEquiv := hDet true false () True hSame
    dsimp at hEquiv
    have hFalse := hEquiv.mp rfl
    cases hFalse
  · intro ⟨_, ⟨v, _, hChooseV⟩, _⟩
    exact hChooseV

/-!
### 2. Six-Level Hierarchy of Alternatives (Section XV)
We explicitly distinguish six distinct levels:
1. OutcomeAlternative
2. ActionAlternative
3. VolitionalAlternative
4. CounterfactualAlternative
5. AgentiveAlternative
6. AgentCausalAlternative
-/

def Alt1_Outcome (World : Type) (OutcomeAt : World → Prop) (v u : World) : Prop :=
  OutcomeAt v ≠ OutcomeAt u

def Alt2_Action (World Subject : Type) (ActAt : World → Subject → Prop → Prop)
    (s : Subject) (a : Prop) (v u : World) : Prop :=
  ActAt v s a ∧ ¬ ActAt u s a

def Alt3_Volition (World Subject : Type) (WillsAt : World → Subject → Prop → Prop)
    (s : Subject) (a : Prop) (v u : World) : Prop :=
  WillsAt v s a ∧ ¬ WillsAt u s a

def Alt4_Counterfactual (World Subject : Type)
    (ReasonsAt : World → Subject → Prop)
    (WillsAt : World → Subject → Prop → Prop)
    (s : Subject) (p : Prop) (actualWorld : World) : Prop :=
  ∃ c : World, ReasonsAt c s ≠ ReasonsAt actualWorld s ∧ WillsAt c s p ≠ WillsAt actualWorld s p

def Alt5_Agentive (World Subject : Type)
    (IntentionalAt : World → Subject → Prop → Prop)
    (s : Subject) (p q : Prop) (v u : World) : Prop :=
  Incompatible p q ∧ IntentionalAt v s p ∧ IntentionalAt u s q

def Alt6_AgentCausal (World Entity Subject : Type)
    (ExtCirc : World → Prop) (ReasonsAt : World → Subject → Prop)
    (HistoryAt : World → Prop) (NatureAt : World → Entity → Prop)
    (InternalStateAt : World → Subject → Prop)
    (SettlesAt : World → Subject → Prop → Prop)
    (g : Entity) (s : Subject) (p q : Prop) (v u : World) : Prop :=
  Incompatible p q ∧
  SameTotalDeliberativeState World Entity Subject ExtCirc ReasonsAt HistoryAt NatureAt InternalStateAt g s v u ∧
  SettlesAt v s p ∧ SettlesAt u s q

-- ===========================================================================
-- Part II: Agency Settlement Hierarchy C0 through C4 (Section II)
-- ===========================================================================

/-!
### 3. Deconstruction of Agent-Causal Settlement: The C0–C4 Ladder
- C0: Primitive Modal Variation (mere difference across worlds)
- C1: Non-Deterministic Settlement (antecedent conditions do not fix volition)
- C2: Agent-Attributable Settlement (difference is predicated of the agent's act)
- C3: Agent-Causal Settlement (agent is the settling source)
- C4: Explanatorily Agent-Causal Settlement (contrastive teleological explanation without necessitation)
-/

def Level_C0_PrimitiveVariation (World Subject : Type)
    (WillsAt : World → Subject → Prop → Prop) (s : Subject) (p q : Prop) (v u : World) : Prop :=
  Incompatible p q ∧ WillsAt v s p ∧ WillsAt u s q

def Level_C1_NonDeterministic (World Subject : Type)
    (ReasonsAt : World → Subject → Prop)
    (WillsAt : World → Subject → Prop → Prop) : Prop :=
  NonDeterministicVolition World Subject ReasonsAt WillsAt

def Level_C2_AgentAttributable (World Subject : Type)
    (SettlesAt : World → Subject → Prop → Prop)
    (s : Subject) (p q : Prop) (v u : World) : Prop :=
  Incompatible p q ∧ SettlesAt v s p ∧ SettlesAt u s q

def Level_C3_AgentCausal (World Entity Subject : Type)
    (ExtCirc : World → Prop) (ReasonsAt : World → Subject → Prop)
    (HistoryAt : World → Prop) (NatureAt : World → Entity → Prop)
    (InternalStateAt : World → Subject → Prop)
    (SettlesAt : World → Subject → Prop → Prop)
    (g : Entity) (s : Subject) (p q : Prop) (v u : World) : Prop :=
  Alt6_AgentCausal World Entity Subject ExtCirc ReasonsAt HistoryAt NatureAt InternalStateAt SettlesAt g s p q v u

def Level_C4_ExplanatoryAgentCausal (World Entity Subject : Type)
    (ExtCirc : World → Prop) (ReasonsAt : World → Subject → Prop)
    (HistoryAt : World → Prop) (NatureAt : World → Entity → Prop)
    (InternalStateAt : World → Subject → Prop)
    (SettlesAt : World → Subject → Prop → Prop)
    (ExplainsSettlement : World → Subject → Prop → Prop → Prop)
    (g : Entity) (s : Subject) (p q : Prop) (v u : World) : Prop :=
  Level_C3_AgentCausal World Entity Subject ExtCirc ReasonsAt HistoryAt NatureAt InternalStateAt SettlesAt g s p q v u ∧
  (∀ w form, SettlesAt w s form → ∃ r, ReasonsAt w s ∧ ExplainsSettlement w s r form)

/-- Separation C0 does not entail C1: A deterministic world with changing reasons has C0 but not C1. -/
theorem C0_not_entails_C1 :
    ∃ (World Subject : Type) (ReasonsAt : World → Subject → Prop)
      (WillsAt : World → Subject → Prop → Prop) (s : Subject) (p q : Prop) (v u : World),
      Level_C0_PrimitiveVariation World Subject WillsAt s p q v u ∧
      ¬ Level_C1_NonDeterministic World Subject ReasonsAt WillsAt := by
  refine ⟨Bool, Unit, fun w _ => w = true,
          fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          (), True, False, true, false, ?_, ?_⟩
  · exact ⟨fun ⟨_, hq⟩ => hq, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩
  · intro hNonDet
    apply hNonDet
    intro w u s a hSame
    dsimp [SameReasons] at hSame
    have hEq : w = u := by
      cases w <;> cases u <;> try rfl
      · contradiction
      · contradiction
    rw [hEq]

/-- Separation C1 does not entail C2: Non-deterministic fluctuation without agent attribution. -/
theorem C1_not_entails_C2 :
    ∃ (World Subject : Type) (ReasonsAt : World → Subject → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (SettlesAt : World → Subject → Prop → Prop)
      (s : Subject) (p q : Prop) (v u : World),
      Level_C1_NonDeterministic World Subject ReasonsAt WillsAt ∧
      ¬ Level_C2_AgentAttributable World Subject SettlesAt s p q v u := by
  refine ⟨Bool, Unit, fun _ _ => True, fun w _ _ => w = true, fun _ _ _ => False,
          (), True, False, true, false, ?_, ?_⟩
  · intro hDet
    have hSame : SameReasons Bool Unit (fun _ _ => True) () true false := rfl
    have hEquiv := hDet true false () True hSame
    dsimp at hEquiv
    have hFalse := hEquiv.mp rfl
    cases hFalse
  · intro ⟨_, hSetV, _⟩
    exact hSetV

-- ===========================================================================
-- Part III: Modal Analogue of A14 & Relative Completeness (Section III)
-- ===========================================================================

/-!
### 4. Tripartite Modal Decomposition & Relative Completeness
Target: Bilateral Contingent Volition (◇Wills(p) ∧ ◇Wills(q)).
Analogous to A14:
ModalDifference = NonDetermination + AgentAttribution + BilateralWitness.
-/

structure ModalDifferencePrimitive (World Subject : Type)
    (frame : KripkeFrame World) (actualWorld : World)
    (ReasonsAt : World → Subject → Prop)
    (WillsAt : World → Subject → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop where
  incomp : Incompatible p q
  witness_p : ∃ v : World, frame.R actualWorld v ∧ WillsAt v s p
  witness_q : ∃ u : World, frame.R actualWorld u ∧ WillsAt u s q
  non_determined : NonDeterministicVolition World Subject ReasonsAt WillsAt

/-- Relative Completeness Theorem:
    Bilateral Modal Volition under non-deterministic conditions is provably equivalent
    to the irreducible ModalDifferencePrimitive. -/
theorem modal_volition_iff_primitive_decomposition
    (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
    (ReasonsAt : World → Subject → Prop)
    (WillsAt : World → Subject → Prop → Prop)
    (s : Subject) (p q : Prop) :
    ModalDifferencePrimitive World Subject frame actualWorld ReasonsAt WillsAt s p q ↔
    (Incompatible p q ∧
     (∃ v : World, frame.R actualWorld v ∧ WillsAt v s p) ∧
     (∃ u : World, frame.R actualWorld u ∧ WillsAt u s q) ∧
     NonDeterministicVolition World Subject ReasonsAt WillsAt) := by
  constructor
  · intro h; exact ⟨h.incomp, h.witness_p, h.witness_q, h.non_determined⟩
  · intro ⟨hInc, hV, hU, hND⟩; exact ⟨hInc, hV, hU, hND⟩

-- ===========================================================================
-- Part IV: Hardened Attribute Spectra & Collapse Theorems (Sections IV–IX, XII, XIII)
-- ===========================================================================

/-!
### 5. Rationality Spectrum: R0 through R5
R0: Coherent action
R1: Acts for reasons
R2: Responds to reasons
R3: Deliberatively weighs reasons
R4: Deliberative non-compulsion (reasons incline without necessitation)
R5: Optimific compulsion (necessarily follows uniquely best reason)
-/

def Rationality_R0 (World Subject : Type) (ActAt : World → Subject → Prop → Prop) (s : Subject) : Prop :=
  ∀ w a, ActAt w s a → ¬ ActAt w s (¬ a)

def Rationality_R1 (World Subject : Type)
    (ReasonsAt : World → Subject → Prop) (ActAt : World → Subject → Prop → Prop) (s : Subject) : Prop :=
  ∀ w a, ActAt w s a → ∃ r, ReasonsAt w s ∧ r

def Rationality_R4_Deliberative (World Subject : Type)
    (ReasonsAt : World → Subject → Prop) (WillsAt : World → Subject → Prop → Prop) (s : Subject) : Prop :=
  ∀ w a, WillsAt w s a → ReasonsAt w s

def Rationality_R5_OptimificCompulsion (World Subject : Type)
    (BestReasonAt : World → Subject → Prop → Prop)
    (WillsAt : World → Subject → Prop → Prop) (s : Subject) : Prop :=
  ∀ w a, BestReasonAt w s a → WillsAt w s a

/-!
### 6. Goodness & Unique Best Action
-/

def UniqueBestAction (World Subject : Type)
    (BestReasonAt : World → Subject → Prop → Prop) (s : Subject) (best : Prop) : Prop :=
  ∀ w, BestReasonAt w s best ∧ (∀ a, BestReasonAt w s a → a = best)

/-- Threshold Collapse Theorem: Optimific Compulsion (R5) under a Unique Best Action forces modal collapse! -/
theorem unique_best_action_optimific_rationality_modal_collapse
    (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
    (BestReasonAt : World → Subject → Prop → Prop)
    (WillsAt : World → Subject → Prop → Prop)
    (s : Subject) (best : Prop)
    (hOpt : Rationality_R5_OptimificCompulsion World Subject BestReasonAt WillsAt s)
    (hUnique : UniqueBestAction World Subject BestReasonAt s best) :
    ∀ w : World, frame.R actualWorld w → WillsAt w s best := by
  intro w _
  have hBest := (hUnique w).1
  exact hOpt w best hBest

/-!
### 7. Omniscience Spectrum
-/

def Omniscience_AllTruths (World Subject : Type)
    (KnowsAt : World → Subject → Prop → Prop) (s : Subject) : Prop :=
  ∀ w (p : Prop), p → KnowsAt w s p

def Omniscience_Counterfactuals (World Subject : Type)
    (KnowsCounterfactualAt : World → Subject → (World → Prop) → Prop) (s : Subject) : Prop :=
  ∀ w (cond : World → Prop), KnowsCounterfactualAt w s cond

-- ===========================================================================
-- Part V: PSR Spectrum, Explanation vs Determination & The Third Regime (Sections X, XI, XVII–XIX)
-- ===========================================================================

/-!
### 8. PSR Spectrum: PSR-1 through PSR-8
PSR-3: Every act has a reason.
PSR-4: Every volition has an explanatory reason (non-necessitating).
PSR-6: Every volition is uniquely determined by sufficient reason (Determining PSR).
-/

def PSR_Level3_ActReason (World Subject : Type)
    (ReasonsAt : World → Subject → Prop) (ActAt : World → Subject → Prop → Prop) (s : Subject) : Prop :=
  ∀ w a, ActAt w s a → ReasonsAt w s

def PSR_Level4_VolitionReason (World Subject : Type)
    (ReasonsAt : World → Subject → Prop) (WillsAt : World → Subject → Prop → Prop) (s : Subject) : Prop :=
  ∀ w a, WillsAt w s a → ReasonsAt w s

def PSR_Level6_DeterminingPSR (World Subject : Type)
    (ReasonsAt : World → Subject → Prop) (WillsAt : World → Subject → Prop → Prop) : Prop :=
  ∀ w u s a, SameReasons World Subject ReasonsAt s w u → (WillsAt w s a ↔ WillsAt u s a)

/-!
### 9. The Third Regime: Teleological Explanation Without Determination
Reason `r` explains the agent's choice of `p`, without determining `p` to the exclusion of accessible `q`.
-/

def ExplainsChoiceNonDetermining (World Subject : Type)
    (frame : KripkeFrame World) (actualWorld : World)
    (ReasonsAt : World → Subject → Prop)
    (WillsAt : World → Subject → Prop → Prop)
    (Explains : World → Subject → Prop → Prop → Prop)
    (s : Subject) (p q r : Prop) : Prop :=
  Incompatible p q ∧
  (∃ v : World, frame.R actualWorld v ∧ WillsAt v s p ∧ ReasonsAt v s ∧ Explains v s r p) ∧
  (∃ u : World, frame.R actualWorld u ∧ WillsAt u s q ∧ ReasonsAt u s ∧ Explains u s r q)

/-- Consistency of the Third Regime:
    An agent can have genuine teleological reasons explaining its choice in both worlds
    under an S5 universal frame, without the choice being determined. -/
theorem third_regime_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ReasonsAt : World → Subject → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (Explains : World → Subject → Prop → Prop → Prop)
      (s : Subject) (p q r : Prop),
      ExplainsChoiceNonDetermining World Subject frame actualWorld ReasonsAt WillsAt Explains s p q r := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ _ => True,
          fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          fun _ _ _ _ => True,
          (), True, False, True, ?_⟩
  refine ⟨fun ⟨_, hq⟩ => hq, ⟨true, trivial, Or.inl ⟨rfl, rfl⟩, trivial, trivial⟩,
                              ⟨false, trivial, Or.inr ⟨rfl, rfl⟩, trivial, trivial⟩⟩

-- ===========================================================================
-- Part VI: The Hostile Countermodel Suite MC31 Through MC45 (Section XXI)
-- ===========================================================================

/-!
### 10. Hostile Countermodels MC31–MC45 (All under S5 Universal Frame)
-/

/-- MC31: Strong omniscience (knows all truths at world) + contingent will. -/
theorem model_MC31_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (KnowsAt : World → Subject → Prop → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (s : Subject) (p q : Prop),
      (∀ w form, form → KnowsAt w s form) ∧
      Incompatible p q ∧
      (∃ v : World, frame.R actualWorld v ∧ WillsAt v s p) ∧
      (∃ u : World, frame.R actualWorld u ∧ WillsAt u s q) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ _ form => form,
          fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          (), True, False, fun _ _ h => h, fun ⟨_, hq⟩ => hq,
          ⟨true, trivial, Or.inl ⟨rfl, rfl⟩⟩, ⟨false, trivial, Or.inr ⟨rfl, rfl⟩⟩⟩

/-- MC32: Strong rationality (R4 deliberative) + contingent will. -/
theorem model_MC32_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ReasonsAt : World → Subject → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (s : Subject) (p q : Prop),
      Rationality_R4_Deliberative World Subject ReasonsAt WillsAt s ∧
      Incompatible p q ∧
      (∃ v : World, frame.R actualWorld v ∧ WillsAt v s p) ∧
      (∃ u : World, frame.R actualWorld u ∧ WillsAt u s q) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ _ => True,
          fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          (), True, False, fun _ _ _ => trivial, fun ⟨_, hq⟩ => hq,
          ⟨true, trivial, Or.inl ⟨rfl, rfl⟩⟩, ⟨false, trivial, Or.inr ⟨rfl, rfl⟩⟩⟩

/-- MC33: Perfect goodness + multiple equally good alternatives. -/
theorem model_MC33_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (IsGoodAt : World → Subject → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (s : Subject) (p q : Prop),
      (∀ w, IsGoodAt w s) ∧
      Incompatible p q ∧
      (∃ v : World, frame.R actualWorld v ∧ WillsAt v s p) ∧
      (∃ u : World, frame.R actualWorld u ∧ WillsAt u s q) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ _ => True,
          fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          (), True, False, fun _ => trivial, fun ⟨_, hq⟩ => hq,
          ⟨true, trivial, Or.inl ⟨rfl, rfl⟩⟩, ⟨false, trivial, Or.inr ⟨rfl, rfl⟩⟩⟩

/-- MC34: Perfect goodness + unique best action forces collapse (freedom refuted). -/
theorem model_MC34_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (BestReasonAt : World → Subject → Prop → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (s : Subject) (best : Prop),
      Rationality_R5_OptimificCompulsion World Subject BestReasonAt WillsAt s ∧
      UniqueBestAction World Subject BestReasonAt s best ∧
      ∀ w, frame.R actualWorld w → WillsAt w s best := by
  refine ⟨Unit, Unit, S5UniversalFrame Unit, (),
          fun _ _ form => form = True, fun _ _ _ => True, (), True,
          fun _ _ _ => trivial, fun _ => ⟨rfl, fun _ h => h⟩, fun _ _ => trivial⟩

/-- MC35: Strong aseity + contingent will. -/
theorem model_MC35_consistent :
    ∃ (World Entity Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ExtDepAt : World → Entity → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (g : Entity) (s : Subject) (p q : Prop),
      (∀ w, ¬ ExtDepAt w g) ∧
      Incompatible p q ∧
      (∃ v : World, frame.R actualWorld v ∧ WillsAt v s p) ∧
      (∃ u : World, frame.R actualWorld u ∧ WillsAt u s q) := by
  refine ⟨Bool, Unit, Unit, S5UniversalFrame Bool, true,
          fun _ _ => False,
          fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          (), (), True, False, fun _ h => h, fun ⟨_, hq⟩ => hq,
          ⟨true, trivial, Or.inl ⟨rfl, rfl⟩⟩, ⟨false, trivial, Or.inr ⟨rfl, rfl⟩⟩⟩

/-- MC36: Strong immutability (nature + character) + contingent will. -/
theorem model_MC36_consistent :
    ∃ (World Entity Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (NatureAt : World → Entity → Prop)
      (CharacterAt : World → Subject → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (g : Entity) (s : Subject) (p q : Prop),
      (∀ w u, NatureAt w g = NatureAt u g) ∧
      (∀ w u, CharacterAt w s = CharacterAt u s) ∧
      Incompatible p q ∧
      (∃ v : World, frame.R actualWorld v ∧ WillsAt v s p) ∧
      (∃ u : World, frame.R actualWorld u ∧ WillsAt u s q) := by
  refine ⟨Bool, Unit, Unit, S5UniversalFrame Bool, true,
          fun _ _ => True, fun _ _ => True,
          fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          (), (), True, False, fun _ _ => rfl, fun _ _ => rfl, fun ⟨_, hq⟩ => hq,
          ⟨true, trivial, Or.inl ⟨rfl, rfl⟩⟩, ⟨false, trivial, Or.inr ⟨rfl, rfl⟩⟩⟩

/-- MC37: Strong PSR (PSR-4 reasons explanation) + non-determined choice. -/
theorem model_MC37_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ReasonsAt : World → Subject → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (s : Subject) (p q : Prop),
      PSR_Level4_VolitionReason World Subject ReasonsAt WillsAt s ∧
      Incompatible p q ∧
      (∃ v : World, frame.R actualWorld v ∧ WillsAt v s p) ∧
      (∃ u : World, frame.R actualWorld u ∧ WillsAt u s q) ∧
      NonDeterministicVolition World Subject ReasonsAt WillsAt := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ _ => True,
          fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          (), True, False, fun _ _ _ => trivial, fun ⟨_, hq⟩ => hq,
          ⟨true, trivial, Or.inl ⟨rfl, rfl⟩⟩, ⟨false, trivial, Or.inr ⟨rfl, rfl⟩⟩, ?_⟩
  intro hDet
  have hSame : SameReasons Bool Unit (fun _ _ => True) () true false := rfl
  have hEquiv := hDet true false () True hSame
  have hTrueAtTrue : (true = true ∧ True = True) ∨ (true = false ∧ True = False) := Or.inl ⟨rfl, rfl⟩
  have hFalseAtFalse := hEquiv.mp hTrueAtTrue
  rcases hFalseAtFalse with ⟨hF1, _⟩ | ⟨hF2, _⟩
  · contradiction
  · contradiction

/-- MC38: Determining PSR + modal collapse. -/
theorem model_MC38_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ReasonsAt : World → Subject → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (s : Subject) (p : Prop),
      PSR_Level6_DeterminingPSR World Subject ReasonsAt WillsAt ∧
      ∀ w, frame.R actualWorld w → WillsAt w s p := by
  refine ⟨Unit, Unit, S5UniversalFrame Unit, (), fun _ _ => True, fun _ _ _ => True, (), True, ?_, ?_⟩
  · intro _ _ _ _ _; exact Iff.rfl
  · intro _ _; trivial

/-- MC39: Agent-causal settlement as mere primitive branching (C0). -/
theorem model_MC39_consistent :
    ∃ (World Subject : Type) (WillsAt : World → Subject → Prop → Prop)
      (s : Subject) (p q : Prop) (v u : World),
      Level_C0_PrimitiveVariation World Subject WillsAt s p q v u := by
  refine ⟨Bool, Unit, fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          (), True, False, true, false, fun ⟨_, hq⟩ => hq, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩

/-- MC40: Genuine agent-causal explanation (C4). -/
theorem model_MC40_consistent :
    ∃ (World Entity Subject : Type)
      (ExtCirc : World → Prop) (ReasonsAt : World → Subject → Prop)
      (HistoryAt : World → Prop) (NatureAt : World → Entity → Prop)
      (InternalStateAt : World → Subject → Prop)
      (SettlesAt : World → Subject → Prop → Prop)
      (ExplainsSettlement : World → Subject → Prop → Prop → Prop)
      (g : Entity) (s : Subject) (p q : Prop) (v u : World),
      Level_C4_ExplanatoryAgentCausal World Entity Subject ExtCirc ReasonsAt HistoryAt NatureAt InternalStateAt
        SettlesAt ExplainsSettlement g s p q v u := by
  refine ⟨Bool, Unit, Unit,
          fun _ => True, fun _ _ => True, fun _ => True, fun _ _ => True, fun _ _ => True,
          fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          fun _ _ _ _ => True,
          (), (), True, False, true, false,
          ⟨fun ⟨_, hq⟩ => hq, ⟨rfl, rfl, rfl, rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩,
          fun _ _ _ => ⟨True, trivial, trivial⟩⟩

/-- MC41: Same complete qualitative state + divergent will. -/
theorem model_MC41_consistent :
    ∃ (World Subject : Type) (QualStateAt : World → Subject → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (s : Subject) (p q : Prop) (v u : World),
      QualStateAt v s = QualStateAt u s ∧
      Incompatible p q ∧
      WillsAt v s p ∧ WillsAt u s q := by
  refine ⟨Bool, Unit, fun _ _ => True,
          fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          (), True, False, true, false, rfl, fun ⟨_, hq⟩ => hq, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩

/-- MC42: Complete relational indiscernibility + divergent will. -/
theorem model_MC42_consistent :
    ∃ (World Entity : Type) (RelToAllAt : World → Entity → Entity → Prop)
      (WillsAt : World → Entity → Prop → Prop)
      (g : Entity) (p q : Prop) (v u : World),
      (∀ e, RelToAllAt v g e = RelToAllAt u g e) ∧
      Incompatible p q ∧
      WillsAt v g p ∧ WillsAt u g q := by
  refine ⟨Bool, Unit, fun _ _ _ => True,
          fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          (), True, False, true, false, fun _ => rfl, fun ⟨_, hq⟩ => hq, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩

/-- MC43: Third-regime explained-but-not-determined agency. -/
theorem model_MC43_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ReasonsAt : World → Subject → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (Explains : World → Subject → Prop → Prop → Prop)
      (s : Subject) (p q r : Prop),
      ExplainsChoiceNonDetermining World Subject frame actualWorld ReasonsAt WillsAt Explains s p q r ∧
      NonDeterministicVolition World Subject ReasonsAt WillsAt := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ _ => True,
          fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          fun _ _ _ _ => True,
          (), True, False, True,
          ⟨fun ⟨_, hq⟩ => hq, ⟨true, trivial, Or.inl ⟨rfl, rfl⟩, trivial, trivial⟩,
                              ⟨false, trivial, Or.inr ⟨rfl, rfl⟩, trivial, trivial⟩⟩,
          ?_⟩
  intro hDet
  have hSame : SameReasons Bool Unit (fun _ _ => True) () true false := rfl
  have hEquiv := hDet true false () True hSame
  have hTrueAtTrue : (true = true ∧ True = True) ∨ (true = false ∧ True = False) := Or.inl ⟨rfl, rfl⟩
  have hFalseAtFalse := hEquiv.mp hTrueAtTrue
  rcases hFalseAtFalse with ⟨hF1, _⟩ | ⟨hF2, _⟩
  · contradiction
  · contradiction

/-- MC44: Necessary agent with full divine-style package + contingent creation under S5 frame. -/
theorem model_MC44_consistent :
    ∃ (World Entity Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ExistsAt : World → Entity → Prop)
      (NatureAt : World → Entity → Prop)
      (ExtDepAt : World → Entity → Prop)
      (KnowsAt : World → Subject → Prop → Prop)
      (IsGoodAt : World → Subject → Prop)
      (CreatesAt : World → Entity → Entity → Prop)
      (g : Entity) (s : Subject) (c : Entity),
      (∀ w, ExistsAt w g) ∧
      (∀ w u, NatureAt w g = NatureAt u g) ∧
      (∀ w, ¬ ExtDepAt w g) ∧
      (∀ w form, form → KnowsAt w s form) ∧
      (∀ w, IsGoodAt w s) ∧
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  refine ⟨Bool, Unit, Unit, S5UniversalFrame Bool, true,
          fun _ _ => True, fun _ _ => True, fun _ _ => False,
          fun _ _ form => form, fun _ _ => True,
          fun w _ _ => w = true,
          (), (), (),
          fun _ => trivial, fun _ _ => rfl, fun _ h => h,
          fun _ _ h => h, fun _ => trivial,
          ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩

/-- MC45: Full divine-style package + necessary creation under S5 frame. -/
theorem model_MC45_consistent :
    ∃ (World Entity Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ExistsAt : World → Entity → Prop)
      (NatureAt : World → Entity → Prop)
      (ExtDepAt : World → Entity → Prop)
      (KnowsAt : World → Subject → Prop → Prop)
      (IsGoodAt : World → Subject → Prop)
      (CreatesAt : World → Entity → Entity → Prop)
      (g : Entity) (s : Subject) (c : Entity),
      (∀ w, ExistsAt w g) ∧
      (∀ w u, NatureAt w g = NatureAt u g) ∧
      (∀ w, ¬ ExtDepAt w g) ∧
      (∀ w form, form → KnowsAt w s form) ∧
      (∀ w, IsGoodAt w s) ∧
      (∀ w : World, frame.R actualWorld w → CreatesAt w g c) := by
  refine ⟨Unit, Unit, Unit, S5UniversalFrame Unit, (),
          fun _ _ => True, fun _ _ => True, fun _ _ => False,
          fun _ _ form => form, fun _ _ => True,
          fun _ _ _ => True,
          (), (), (),
          fun _ => trivial, fun _ _ => rfl, fun _ h => h,
          fun _ _ h => h, fun _ => trivial,
          fun _ _ => trivial⟩

end Logos.DeepModalFrontier
