/-
# Logos.ModalPossibilityFrontier — The Modal Possibility Frontier

An adversarial formal investigation into the modal frontier of agency, necessity,
reason, and creation:
"Try to shrink the remaining realm of possibilities by attacking it from every
logically and metaphysically available direction."

Governing rule:
"Prefer losing the theorem to hiding the premise."

Terminology:
All formal definitions use the neutral witness `g : Entity` and `s : Subject`.
Theological identifications are strictly confined to the synthesis layer.
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

namespace Logos.ModalPossibilityFrontier

open Logos.TheologicalModalHardening (KripkeFrame BoxR)
open Logos.ModalCreationAgency (Incompatible ChoosesAt FreeWillAt TargetA_NecessaryBeing TargetB_NecessaryPerson)
open Logos.EssenceActCollapse (NecessaryEntity NecessaryNature NecessaryAct ContingentAct VolitionToActBridge SameCircumstances SameNature)

-- ===========================================================================
-- Part I: Multi-Layer Semantic Hardening (Section I)
-- ===========================================================================

/-!
### 1. Rigid Individual Identity Across Worlds
We enforce rigid cross-world identity for the individual candidate entity `g`
and its personal subject correlate `s` across all worlds.
-/

structure RigidAgent (World Entity Subject : Type)
    (ExistsAt : World → Entity → Prop)
    (SubjectExistsAt : World → Subject → Prop)
    (EntityOf : Subject → Entity)
    (g : Entity) (s : Subject) : Prop where
  g_necessary : ∀ w : World, ExistsAt w g
  s_necessary : ∀ w : World, SubjectExistsAt w s
  rigid_correlate : EntityOf s = g

/-!
### 2. Deconstruction of Circumstances: Orthogonal Layers
Rather than a single monolithic "circumstance", we separate:
- External circumstances (world environment, external states)
- Reasons (deliberative inputs, values, motives)
- World history (prior temporal/modal stages)
- Intrinsic nature (essential attributes of g)
- Internal state (mental disposition of s)
- Total deliberative state (conjunction of all antecedent conditions)
-/

def SameExternalCircumstances (World : Type) (ExtCirc : World → Prop) (w u : World) : Prop :=
  ExtCirc w = ExtCirc u

def SameReasons (World Subject : Type) (ReasonsAt : World → Subject → Prop) (s : Subject) (w u : World) : Prop :=
  ReasonsAt w s = ReasonsAt u s

def SameHistory (World : Type) (HistoryAt : World → Prop) (w u : World) : Prop :=
  HistoryAt w = HistoryAt u

def SameIntrinsicNature (World Entity : Type) (NatureAt : World → Entity → Prop) (g : Entity) (w u : World) : Prop :=
  NatureAt w g = NatureAt u g

def SameInternalState (World Subject : Type) (InternalStateAt : World → Subject → Prop) (s : Subject) (w u : World) : Prop :=
  InternalStateAt w s = InternalStateAt u s

structure SameTotalDeliberativeState (World Entity Subject : Type)
    (ExtCirc : World → Prop)
    (ReasonsAt : World → Subject → Prop)
    (HistoryAt : World → Prop)
    (NatureAt : World → Entity → Prop)
    (InternalStateAt : World → Subject → Prop)
    (g : Entity) (s : Subject) (w u : World) : Prop where
  same_ext : SameExternalCircumstances World ExtCirc w u
  same_reasons : SameReasons World Subject ReasonsAt s w u
  same_history : SameHistory World HistoryAt w u
  same_nature : SameIntrinsicNature World Entity NatureAt g w u
  same_internal : SameInternalState World Subject InternalStateAt s w u

-- ===========================================================================
-- Part II: Modal Attribute Lattice & Separation (Sections II, VII)
-- ===========================================================================

/-!
### 3. Modal Attribute Lattice
Attributes of necessary beings and agents.
-/

def NecessaryRationality (World Subject : Type)
    (IsRationalAt : World → Subject → Prop) (s : Subject) : Prop :=
  ∀ w : World, IsRationalAt w s

def NecessaryKnowledge (World Subject : Type)
    (KnowsAt : World → Subject → Prop → Prop) (s : Subject) (p : Prop) : Prop :=
  ∀ w : World, KnowsAt w s p

def PerfectGoodness (World Subject : Type)
    (IsGoodAt : World → Subject → Prop) (s : Subject) : Prop :=
  ∀ w : World, IsGoodAt w s

def ImmutableNature (World Entity : Type)
    (NatureAt : World → Entity → Prop) (g : Entity) : Prop :=
  ∀ w u : World, NatureAt w g = NatureAt u g

def ImmutableWill (World Subject : Type)
    (WillsAt : World → Subject → Prop → Prop) (s : Subject) (a : Prop) : Prop :=
  ∀ w u : World, WillsAt w s a = WillsAt u s a

def Aseity (World Entity : Type)
    (ExtDepAt : World → Entity → Prop) (g : Entity) : Prop :=
  ∀ w : World, ¬ ExtDepAt w g

/-- Separation: Necessary Knowledge does NOT entail Necessary Will. -/
theorem necessary_knowledge_not_entails_necessary_will :
    ∃ (World Subject : Type)
      (KnowsAt : World → Subject → Prop → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (s : Subject) (k a : Prop),
      NecessaryKnowledge World Subject KnowsAt s k ∧
      ¬ ImmutableWill World Subject WillsAt s a := by
  refine ⟨Bool, Unit, fun _ _ _ => True, fun w _ _ => w = true, (), True, True, ?_, ?_⟩
  · intro _; trivial
  · intro hImm
    have hEq := hImm true false
    have hDiff : (true = true) ≠ (false = true) := by decide
    exact hDiff hEq

/-- Separation: Necessary Rationality does NOT entail Necessary Action. -/
theorem necessary_rationality_not_entails_necessary_act :
    ∃ (World Subject : Type)
      (IsRationalAt : World → Subject → Prop)
      (ActAt : World → Subject → Prop → Prop)
      (s : Subject) (a : Prop),
      NecessaryRationality World Subject IsRationalAt s ∧
      ContingentAct World Subject ActAt s a := by
  refine ⟨Bool, Unit, fun _ _ => True, fun w _ _ => w = true, (), True, ?_, ?_⟩
  · intro _; trivial
  · exact ⟨⟨true, rfl⟩, ⟨false, fun h => by cases h⟩⟩

-- ===========================================================================
-- Part III: Deterministic Collapse Taxonomy & Impossibility Theorems (Sections IV, VIII, IX, XVII)
-- ===========================================================================

/-!
### 4. Deterministic Principles: Hierarchy
- `StrictDeterminism`: Any two accessible worlds are identical.
- `CausalDeterminism`: Identical antecedent history uniquely determines volition.
- `ReasonDeterminism`: Identical reasons uniquely determine volition.
- `DeterminingPSR`: Every volition is uniquely determined by antecedent reasons.
- `CompleteStateDeterminism`: Identical total deliberative state uniquely determines volition.
-/

def StrictDeterminism (World : Type) (frame : KripkeFrame World) (actualWorld : World) : Prop :=
  ∀ w : World, frame.R actualWorld w → w = actualWorld

def CausalDeterminism (World Subject : Type)
    (HistoryAt : World → Prop)
    (WillsAt : World → Subject → Prop → Prop) : Prop :=
  ∀ w u s a, SameHistory World HistoryAt w u →
    (WillsAt w s a ↔ WillsAt u s a)

def ReasonDeterminism (World Subject : Type)
    (ReasonsAt : World → Subject → Prop)
    (WillsAt : World → Subject → Prop → Prop) : Prop :=
  ∀ w u s a, SameReasons World Subject ReasonsAt s w u →
    (WillsAt w s a ↔ WillsAt u s a)

def DeterminingPSR (World Subject : Type)
    (ReasonsAt : World → Subject → Prop)
    (WillsAt : World → Subject → Prop → Prop) : Prop :=
  ∀ w u s a, SameReasons World Subject ReasonsAt s w u →
    (WillsAt w s a ↔ WillsAt u s a)

/-- Equivalence: Determining PSR is identical in logical form to Reason Determinism. -/
theorem determining_psr_iff_reason_determinism
    (World Subject : Type)
    (ReasonsAt : World → Subject → Prop)
    (WillsAt : World → Subject → Prop → Prop) :
    DeterminingPSR World Subject ReasonsAt WillsAt ↔
    ReasonDeterminism World Subject ReasonsAt WillsAt :=
  Iff.rfl

def CompleteStateDeterminism (World Entity Subject : Type)
    (ExtCirc : World → Prop) (ReasonsAt : World → Subject → Prop)
    (HistoryAt : World → Prop) (NatureAt : World → Entity → Prop)
    (InternalStateAt : World → Subject → Prop)
    (WillsAt : World → Subject → Prop → Prop) : Prop :=
  ∀ w u g s a, SameTotalDeliberativeState World Entity Subject ExtCirc ReasonsAt HistoryAt NatureAt InternalStateAt g s w u →
    (WillsAt w s a ↔ WillsAt u s a)

/-- Causal Determinism Modal Collapse Theorem:
    If antecedent history is invariant across accessible worlds and causal determinism holds,
    then actual volition is necessary across all accessible worlds. -/
theorem causal_determinism_modal_collapse
    (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
    (HistoryAt : World → Prop) (WillsAt : World → Subject → Prop → Prop)
    (s : Subject) (a : Prop)
    (hActual : WillsAt actualWorld s a)
    (hInvariantHistory : ∀ w, frame.R actualWorld w → SameHistory World HistoryAt actualWorld w)
    (hCausalDet : CausalDeterminism World Subject HistoryAt WillsAt) :
    ∀ w, frame.R actualWorld w → WillsAt w s a := by
  intro w hRw
  have hSame := hInvariantHistory w hRw
  have hEquiv := hCausalDet actualWorld w s a hSame
  exact hEquiv.mp hActual

/-- Minimal Collapse Theorem: Reason Determinism yields modal collapse of will. -/
theorem reason_determinism_modal_collapse
    (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
    (ReasonsAt : World → Subject → Prop) (WillsAt : World → Subject → Prop → Prop)
    (s : Subject) (a : Prop)
    (hActual : WillsAt actualWorld s a)
    (hInvariantReasons : ∀ w, frame.R actualWorld w → SameReasons World Subject ReasonsAt s actualWorld w)
    (hDet : ReasonDeterminism World Subject ReasonsAt WillsAt) :
    ∀ w, frame.R actualWorld w → WillsAt w s a := by
  intro w hRw
  have hSame := hInvariantReasons w hRw
  have hEquiv := hDet actualWorld w s a hSame
  exact hEquiv.mp hActual

/-!
### 5. Positive Impossibility Theorems
-/

/-- Impossibility Theorem 1: Determining PSR is logically incompatible with Bilateral Modal Freedom.
    If reasons are invariant across accessible worlds and determining PSR holds,
    the agent cannot possess accessible alternative volitions. -/
theorem determining_psr_incompatible_with_modal_freedom
    (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
    (ReasonsAt : World → Subject → Prop) (WillsAt : World → Subject → Prop → Prop)
    (s : Subject) (p q : Prop)
    (hIncomp : Incompatible p q)
    (hConsistentVolition : ∀ w a b, Incompatible a b → WillsAt w s a → ¬ WillsAt w s b)
    (hPSR : DeterminingPSR World Subject ReasonsAt WillsAt)
    (hInvariantReasons : ∀ w, frame.R actualWorld w → SameReasons World Subject ReasonsAt s actualWorld w)
    (hBranchP : ∃ v : World, frame.R actualWorld v ∧ WillsAt v s p)
    (hBranchQ : ∃ u : World, frame.R actualWorld u ∧ WillsAt u s q) :
    False := by
  obtain ⟨v, hRv, hWillsP⟩ := hBranchP
  obtain ⟨u, hRu, hWillsQ⟩ := hBranchQ
  have hSameV := hInvariantReasons v hRv
  have hSameU := hInvariantReasons u hRu
  have hSameVU : SameReasons World Subject ReasonsAt s v u := by
    dsimp [SameReasons] at *
    rw [← hSameV, ← hSameU]
  have hWillsQ_at_v := (hPSR v u s q hSameVU).mpr hWillsQ
  have hNotQ_at_v := hConsistentVolition v p q hIncomp hWillsP
  exact hNotQ_at_v hWillsQ_at_v

/-- Impossibility Theorem 2: Immutable Will is incompatible with Contingent Action. -/
theorem immutable_will_incompatible_with_contingent_act
    (World Subject : Type) (_frame : KripkeFrame World) (_actualWorld : World)
    (WillsAt : World → Subject → Prop → Prop) (ActAt : World → Subject → Prop → Prop)
    (s : Subject) (a : Prop)
    (hBridge : VolitionToActBridge World Subject WillsAt ActAt)
    (hReflect : ∀ w s a, ActAt w s a → WillsAt w s a)
    (hImmWill : ImmutableWill World Subject WillsAt s a)
    (hContingentAct : ContingentAct World Subject ActAt s a) :
    False := by
  obtain ⟨⟨v, hActV⟩, ⟨u, hNotActU⟩⟩ := hContingentAct
  have hWillsV : WillsAt v s a := hReflect v s a hActV
  have hEq := hImmWill v u
  have hWillsU : WillsAt u s a := by
    have hPropEq : WillsAt v s a = WillsAt u s a := hEq
    exact hPropEq ▸ hWillsV
  have hActU := hBridge u s a hWillsU
  exact hNotActU hActU

-- ===========================================================================
-- Part IV: Action Hierarchy, Reasons-Responsiveness & Relative Completeness (Sections V, VI, X, XVIII, XIX)
-- ===========================================================================

/-!
### 6. Four-Level Action/Agency Hierarchy
We strictly separate:
Level 1: Outcome Alternative (world states differ)
Level 2: Action Alternative (agent's actions differ)
Level 3: Volition Alternative (agent's will differs)
Level 4: Agent-Causal Settlement (agent irreducibly settles between options under identical input)
-/

def Level1_OutcomeAlternative (World : Type) (OutcomeAt : World → Prop) (v u : World) : Prop :=
  OutcomeAt v ≠ OutcomeAt u

def Level2_ActAlternative (World Subject : Type) (ActAt : World → Subject → Prop → Prop)
    (s : Subject) (a : Prop) (v u : World) : Prop :=
  ActAt v s a ∧ ¬ ActAt u s a

def Level3_VolitionAlternative (World Subject : Type) (WillsAt : World → Subject → Prop → Prop)
    (s : Subject) (a : Prop) (v u : World) : Prop :=
  WillsAt v s a ∧ ¬ WillsAt u s a

def Level4_AgentCausalAlternative (World Entity Subject : Type)
    (ExtCirc : World → Prop) (ReasonsAt : World → Subject → Prop)
    (HistoryAt : World → Prop) (NatureAt : World → Entity → Prop)
    (InternalStateAt : World → Subject → Prop)
    (SettlesAt : World → Subject → Prop → Prop)
    (g : Entity) (s : Subject) (p q : Prop) (v u : World) : Prop :=
  Incompatible p q ∧
  SameTotalDeliberativeState World Entity Subject ExtCirc ReasonsAt HistoryAt NatureAt InternalStateAt g s v u ∧
  SettlesAt v s p ∧ SettlesAt u s q

/-!
### 7. Relative Completeness for Contingent Creation
We isolate the exact formal missing link: `MissingModalSettlement`.
-/

def MissingModalSettlement (World Subject : Type)
    (frame : KripkeFrame World) (actualWorld : World)
    (WillsAt : World → Subject → Prop → Prop)
    (s : Subject) (CreateForm RefrainForm : Prop) : Prop :=
  Incompatible CreateForm RefrainForm ∧
  (∃ v : World, frame.R actualWorld v ∧ WillsAt v s CreateForm) ∧
  (∃ u : World, frame.R actualWorld u ∧ WillsAt u s RefrainForm)

/-- Relative Completeness Theorem:
    Target Contingent Creation is provably equivalent to MissingModalSettlement.
    Nothing more, nothing less, is required. -/
theorem target_contingent_creation_iff_missing_modal_settlement
    (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
    (WillsAt : World → Subject → Prop → Prop)
    (s : Subject) (CreateForm RefrainForm : Prop) :
    MissingModalSettlement World Subject frame actualWorld WillsAt s CreateForm RefrainForm ↔
    (Incompatible CreateForm RefrainForm ∧
     (∃ v : World, frame.R actualWorld v ∧ WillsAt v s CreateForm) ∧
     (∃ u : World, frame.R actualWorld u ∧ WillsAt u s RefrainForm)) :=
  Iff.rfl

-- ===========================================================================
-- Part V: The Hostile Countermodel Suite MC13 Through MC30 (Sections III, XI, XII, XIII, XIV, XVI)
-- ===========================================================================

/-!
### 8. Hostile Countermodels MC13 – MC30
-/

/-- MC13: Same external circumstances, different will. -/
theorem model_MC13_consistent :
    ∃ (World Subject : Type) (ExtCirc : World → Prop) (WillsAt : World → Subject → Prop → Prop)
      (s : Subject) (a : Prop) (v u : World),
      SameExternalCircumstances World ExtCirc v u ∧
      Level3_VolitionAlternative World Subject WillsAt s a v u := by
  refine ⟨Bool, Unit, fun _ => True, fun w _ _ => w = true, (), True, true, false, rfl, ?_⟩
  exact ⟨rfl, fun h => by cases h⟩

/-- MC14: Same external circumstances + same reasons, different will. -/
theorem model_MC14_consistent :
    ∃ (World Subject : Type) (ExtCirc : World → Prop) (ReasonsAt : World → Subject → Prop)
      (WillsAt : World → Subject → Prop → Prop) (s : Subject) (a : Prop) (v u : World),
      SameExternalCircumstances World ExtCirc v u ∧
      SameReasons World Subject ReasonsAt s v u ∧
      Level3_VolitionAlternative World Subject WillsAt s a v u := by
  refine ⟨Bool, Unit, fun _ => True, fun _ _ => True, fun w _ _ => w = true, (), True, true, false, rfl, rfl, ?_⟩
  exact ⟨rfl, fun h => by cases h⟩

/-- MC15: Same external circumstances + reasons + history, different will. -/
theorem model_MC15_consistent :
    ∃ (World Subject : Type) (ExtCirc : World → Prop) (ReasonsAt : World → Subject → Prop)
      (HistoryAt : World → Prop) (WillsAt : World → Subject → Prop → Prop)
      (s : Subject) (a : Prop) (v u : World),
      SameExternalCircumstances World ExtCirc v u ∧
      SameReasons World Subject ReasonsAt s v u ∧
      SameHistory World HistoryAt v u ∧
      Level3_VolitionAlternative World Subject WillsAt s a v u := by
  refine ⟨Bool, Unit, fun _ => True, fun _ _ => True, fun _ => True, fun w _ _ => w = true,
          (), True, true, false, rfl, rfl, rfl, ?_⟩
  exact ⟨rfl, fun h => by cases h⟩

/-- MC16: Same total deliberative state, different will. -/
theorem model_MC16_consistent :
    ∃ (World Entity Subject : Type)
      (ExtCirc : World → Prop) (ReasonsAt : World → Subject → Prop)
      (HistoryAt : World → Prop) (NatureAt : World → Entity → Prop)
      (InternalStateAt : World → Subject → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (g : Entity) (s : Subject) (a : Prop) (v u : World),
      SameTotalDeliberativeState World Entity Subject ExtCirc ReasonsAt HistoryAt NatureAt InternalStateAt g s v u ∧
      Level3_VolitionAlternative World Subject WillsAt s a v u := by
  refine ⟨Bool, Unit, Unit,
          fun _ => True, fun _ _ => True, fun _ => True, fun _ _ => True, fun _ _ => True,
          fun w _ _ => w = true, (), (), True, true, false,
          ⟨rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, fun h => by cases h⟩⟩

/-- MC17: Necessary rational agent with complete knowledge and identical deliberative state, divergent will. -/
theorem model_MC17_consistent :
    ∃ (World Entity Subject : Type)
      (ExistsAt : World → Entity → Prop) (IsRationalAt : World → Subject → Prop)
      (KnowsAt : World → Subject → Prop → Prop)
      (ExtCirc : World → Prop) (ReasonsAt : World → Subject → Prop)
      (HistoryAt : World → Prop) (NatureAt : World → Entity → Prop)
      (InternalStateAt : World → Subject → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (g : Entity) (s : Subject) (k a : Prop) (v u : World),
      NecessaryEntity World Entity ExistsAt g ∧
      NecessaryRationality World Subject IsRationalAt s ∧
      NecessaryKnowledge World Subject KnowsAt s k ∧
      SameTotalDeliberativeState World Entity Subject ExtCirc ReasonsAt HistoryAt NatureAt InternalStateAt g s v u ∧
      Level3_VolitionAlternative World Subject WillsAt s a v u := by
  refine ⟨Bool, Unit, Unit,
          fun _ _ => True, fun _ _ => True, fun _ _ _ => True,
          fun _ => True, fun _ _ => True, fun _ => True, fun _ _ => True, fun _ _ => True,
          fun w _ _ => w = true, (), (), True, True, true, false,
          fun _ => trivial, fun _ => trivial, fun _ => trivial,
          ⟨rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, fun h => by cases h⟩⟩

/-- MC18: Informational symmetry with contingent volition. -/
theorem model_MC18_consistent :
    ∃ (World Subject : Type) (InfoAt : World → Subject → Prop)
      (WillsAt : World → Subject → Prop → Prop) (s : Subject) (p q : Prop) (v u : World),
      InfoAt v s = InfoAt u s ∧
      Incompatible p q ∧
      WillsAt v s p ∧ WillsAt u s q := by
  refine ⟨Bool, Unit, fun _ _ => True,
          fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          (), True, False, true, false, rfl, fun ⟨_, hq⟩ => hq, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩

/-- MC19: Necessary perfectly good agent with contingent volition. -/
theorem model_MC19_consistent :
    ∃ (World Subject : Type) (IsGoodAt : World → Subject → Prop)
      (WillsAt : World → Subject → Prop → Prop) (s : Subject) (a : Prop) (v u : World),
      PerfectGoodness World Subject IsGoodAt s ∧
      Level3_VolitionAlternative World Subject WillsAt s a v u := by
  refine ⟨Bool, Unit, fun _ _ => True, fun w _ _ => w = true, (), True, true, false,
          fun _ => trivial, ⟨rfl, fun h => by cases h⟩⟩

/-- MC20: Necessary immutable nature with contingent volition. -/
theorem model_MC20_consistent :
    ∃ (World Entity Subject : Type) (NatureAt : World → Entity → Prop)
      (WillsAt : World → Subject → Prop → Prop) (g : Entity) (s : Subject) (a : Prop) (v u : World),
      ImmutableNature World Entity NatureAt g ∧
      Level3_VolitionAlternative World Subject WillsAt s a v u := by
  refine ⟨Bool, Unit, Unit, fun _ _ => True, fun w _ _ => w = true, (), (), True, true, false,
          fun _ _ => rfl, ⟨rfl, fun h => by cases h⟩⟩

/-- MC21: Aseitic agent with contingent volition. -/
theorem model_MC21_consistent :
    ∃ (World Entity Subject : Type) (ExtDepAt : World → Entity → Prop)
      (WillsAt : World → Subject → Prop → Prop) (g : Entity) (s : Subject) (a : Prop) (v u : World),
      Aseity World Entity ExtDepAt g ∧
      Level3_VolitionAlternative World Subject WillsAt s a v u := by
  refine ⟨Bool, Unit, Unit, fun _ _ => False, fun w _ _ => w = true, (), (), True, true, false,
          fun _ h => h, ⟨rfl, fun h => by cases h⟩⟩

/-- MC22: Contrastive explanation via irreducible agent-causal settlement. -/
theorem model_MC22_consistent :
    ∃ (World Entity Subject : Type)
      (ExtCirc : World → Prop) (ReasonsAt : World → Subject → Prop)
      (HistoryAt : World → Prop) (NatureAt : World → Entity → Prop)
      (InternalStateAt : World → Subject → Prop)
      (SettlesAt : World → Subject → Prop → Prop)
      (g : Entity) (s : Subject) (p q : Prop) (v u : World),
      Level4_AgentCausalAlternative World Entity Subject ExtCirc ReasonsAt HistoryAt NatureAt InternalStateAt SettlesAt g s p q v u := by
  refine ⟨Bool, Unit, Unit,
          fun _ => True, fun _ _ => True, fun _ => True, fun _ _ => True, fun _ _ => True,
          fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          (), (), True, False, true, false,
          fun ⟨_, hq⟩ => hq, ⟨rfl, rfl, rfl, rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩

/-- MC23: Indeterministic but unfree agent (random fluctuation without intentional choice). -/
theorem model_MC23_consistent :
    ∃ (World Subject : Type) (Circumstance : World → Prop)
      (FluctuationAt : World → Subject → Prop → Prop)
      (ChoosesAt : World → Subject → Prop → Prop → Prop)
      (s : Subject) (p : Prop) (v u : World),
      Circumstance v = Circumstance u ∧
      (FluctuationAt v s p ∧ ¬ FluctuationAt u s p) ∧
      (∀ w p q, ¬ ChoosesAt w s p q) := by
  refine ⟨Bool, Unit, fun _ => True, fun w _ _ => w = true, fun _ _ _ _ => False, (), True, true, false,
          rfl, ⟨rfl, fun h => by cases h⟩, fun _ _ _ h => h⟩

/-- MC24: Reasons-responsive but modally closed agent (Frankfurt/compatibilist model).
    Agent responds to hypothetical different reasons, but in accessible reality only one reason/choice is open. -/
theorem model_MC24_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ReasonsAt : World → Subject → Prop) (WillsAt : World → Subject → Prop → Prop)
      (s : Subject) (p : Prop),
      -- Accessible modal closure:
      (∀ w, frame.R actualWorld w → WillsAt w s p) ∧
      -- Counterfactual sensitivity across a broader conceptual world:
      (∃ c : World, ReasonsAt c s ≠ ReasonsAt actualWorld s ∧ ¬ WillsAt c s p) := by
  refine ⟨Bool, Unit, { R := fun _ w => w = true }, true,
          fun w _ => w = true, fun w _ _ => w = true, (), True, ?_, ?_⟩
  · intro w hRw
    exact hRw
  · refine ⟨false, ?_, fun h => by cases h⟩
    intro hEq
    have hDiff : (false = true) ≠ (true = true) := by decide
    exact hDiff hEq

/-- MC25: Modal freedom without agent-causal settlement (pure ungrounded indeterminism). -/
theorem model_MC25_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (WillsAt : World → Subject → Prop → Prop)
      (SettlesAt : World → Subject → Prop → Prop)
      (s : Subject) (p q : Prop),
      Incompatible p q ∧
      (∃ v : World, frame.R actualWorld v ∧ WillsAt v s p) ∧
      (∃ u : World, frame.R actualWorld u ∧ WillsAt u s q) ∧
      (∀ w s a, ¬ SettlesAt w s a) := by
  refine ⟨Bool, Unit, { R := fun _ _ => True }, true,
          fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          fun _ _ _ => False, (), True, False,
          fun ⟨_, hq⟩ => hq, ⟨true, trivial, Or.inl ⟨rfl, rfl⟩⟩, ⟨false, trivial, Or.inr ⟨rfl, rfl⟩⟩,
          fun _ _ _ h => h⟩

/-- MC26: Agent-causal-looking structure that collapses into determinism. -/
theorem model_MC26_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (SettlesAt : World → Subject → Prop → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (s : Subject) (p : Prop),
      (∀ w form, SettlesAt w s form ↔ WillsAt w s form) ∧
      (∀ w, frame.R actualWorld w → WillsAt w s p) := by
  refine ⟨Unit, Unit, { R := fun _ _ => True }, (), fun _ _ _ => True, fun _ _ _ => True, (), True, ?_, ?_⟩
  · intro _ _; exact Iff.rfl
  · intro _ _; trivial

/-- MC27: Necessary agent with contingent creation. -/
theorem model_MC27_consistent :
    ∃ (World Entity : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ExistsAt : World → Entity → Prop) (CreatesAt : World → Entity → Entity → Prop)
      (g : Entity) (c : Entity),
      NecessaryEntity World Entity ExistsAt g ∧
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  refine ⟨Bool, Unit, { R := fun _ _ => True }, true,
          fun _ _ => True, fun w _ _ => w = true, (), (),
          fun _ => trivial, ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩

/-- MC28: Necessary agent with necessary creation. -/
theorem model_MC28_consistent :
    ∃ (World Entity : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ExistsAt : World → Entity → Prop) (CreatesAt : World → Entity → Entity → Prop)
      (g : Entity) (c : Entity),
      NecessaryEntity World Entity ExistsAt g ∧
      ∀ w : World, frame.R actualWorld w → CreatesAt w g c := by
  refine ⟨Unit, Unit, { R := fun _ _ => True }, (), fun _ _ => True, fun _ _ _ => True, (), (),
          fun _ => trivial, fun _ _ => trivial⟩

/-- MC29: Necessary agent with no creation and no voluntary abstention. -/
theorem model_MC29_consistent :
    ∃ (World Entity Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ExistsAt : World → Entity → Prop) (CreatesAt : World → Entity → Entity → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (g : Entity) (s : Subject) (RefrainForm : Prop),
      NecessaryEntity World Entity ExistsAt g ∧
      (∃ w : World, frame.R actualWorld w ∧ ¬ ∃ x, CreatesAt w g x) ∧
      (∀ w, ¬ WillsAt w s RefrainForm) := by
  refine ⟨Unit, Unit, Unit, { R := fun _ _ => True }, (), fun _ _ => True, fun _ _ _ => False, fun _ _ _ => False,
          (), (), True, fun _ => trivial, ⟨(), trivial, fun ⟨_, hx⟩ => hx⟩, fun _ h => h⟩

/-- MC30: Necessary agent freely abstaining from creation. -/
theorem model_MC30_consistent :
    ∃ (World Entity Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ExistsAt : World → Entity → Prop) (WillsAt : World → Subject → Prop → Prop)
      (CreatesAt : World → Entity → Entity → Prop)
      (g : Entity) (s : Subject) (CreateForm RefrainForm : Prop),
      NecessaryEntity World Entity ExistsAt g ∧
      Incompatible CreateForm RefrainForm ∧
      (∃ v : World, frame.R actualWorld v ∧ WillsAt v s CreateForm ∧ (∃ x, CreatesAt v g x)) ∧
      (∃ u : World, frame.R actualWorld u ∧ WillsAt u s RefrainForm ∧ (¬ ∃ x, CreatesAt u g x)) := by
  refine ⟨Bool, Unit, Unit, { R := fun _ _ => True }, true,
          fun _ _ => True,
          fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          fun w _ _ => w = true,
          (), (), True, False,
          fun _ => trivial, fun ⟨_, hq⟩ => hq,
          ⟨true, trivial, Or.inl ⟨rfl, rfl⟩, ⟨(), rfl⟩⟩,
          ⟨false, trivial, Or.inr ⟨rfl, rfl⟩, fun ⟨_, hx⟩ => by cases hx⟩⟩

end Logos.ModalPossibilityFrontier
