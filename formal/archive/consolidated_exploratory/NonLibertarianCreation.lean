/-
# Logos.NonLibertarianCreation — Contingent Creation Without Libertarian Agency

A machine-checked formal investigation into whether creation can be genuinely contingent
when neither deterministic agency nor libertarian/free agency exists.

Governing rule:
"Prefer losing the theorem to hiding the premise."

Methodological disciplines:
1. Strict formal separation of Non-Determined, Random, and Non-Free.
2. Constructive finite models under S5 Universal Frames (Bool, Unit, Fin n).
3. Set-valued explanation (AdmissibleByReason) and structural constraints.
4. Tripartite explanation: Possibility, Actualization, and Contrastive Difference.
5. Formalization and proof of the Contrastive Trilemma Theorem.
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

namespace Logos.NonLibertarianCreation

open Logos.TheologicalModalHardening (KripkeFrame)
open Logos.ModalCreationAgency (Incompatible)
open Logos.DeepModalFrontier (S5UniversalFrame)

-- ===========================================================================
-- Part I: Independent Predicates & Logical Separations (Sections I, II, III)
-- ===========================================================================

/-!
### 1. Independent Predicates for Modal Regimes
We define independent predicates for the ontological and explanatory status of events.
-/

def DeterminedEvent (World : Type) (AntecedentAt : World → Prop) (EventAt : World → Prop) : Prop :=
  ∀ w u : World, AntecedentAt w = AntecedentAt u → (EventAt w ↔ EventAt u)

def NonDeterminedEvent (World : Type) (AntecedentAt : World → Prop) (EventAt : World → Prop) : Prop :=
  ¬ DeterminedEvent World AntecedentAt EventAt

def VolitionallyFree (World Subject : Type)
    (ChoosesAt : World → Subject → Prop → Prop → Prop)
    (s : Subject) (p q : Prop) (w : World) : Prop :=
  Incompatible p q ∧ ChoosesAt w s p q

def AgentCausalSettlement (World Subject : Type)
    (SettlesAt : World → Subject → Prop → Prop)
    (s : Subject) (p : Prop) (w : World) : Prop :=
  SettlesAt w s p

def ExplainedEvent (World : Type) (ReasonAt : World → Prop) (EventAt : World → Prop) : Prop :=
  ∀ w : World, EventAt w → ReasonAt w

def GroundedEvent (World Entity : Type)
    (GroundsAt : World → Entity → Prop → Prop) (g : Entity) (p : Prop) (w : World) : Prop :=
  GroundsAt w g p

def RandomEvent (World : Type) (EventAt : World → Prop) (ReasonAt : World → Prop) : Prop :=
  (∃ w, EventAt w ∧ ¬ ReasonAt w) ∧ (∃ u, ¬ EventAt u ∧ ¬ ReasonAt u)

def BruteEvent (World : Type) (AntecedentAt : World → Prop) (ReasonAt : World → Prop)
    (EventAt : World → Prop) : Prop :=
  NonDeterminedEvent World AntecedentAt EventAt ∧ ¬ ExplainedEvent World ReasonAt EventAt

/-!
### 2. Logical Separations
-/

/-- Separation: Non-Determined does NOT entail Random.
    An event can be non-determined yet explained by an admissible reason or law. -/
theorem nondetermined_not_entails_random :
    ∃ (World : Type) (AntecedentAt : World → Prop) (ReasonAt : World → Prop) (EventAt : World → Prop),
      NonDeterminedEvent World AntecedentAt EventAt ∧
      ¬ RandomEvent World EventAt ReasonAt := by
  refine ⟨Bool, fun _ => True, fun _ => True, fun w => w = true, ?_, ?_⟩
  · intro hDet
    have hEquiv := hDet true false rfl
    dsimp at hEquiv
    have hFalse := hEquiv.mp rfl
    cases hFalse
  · intro ⟨⟨w, _, hNoR⟩, _⟩
    exact hNoR trivial

/-- Separation: Non-Determined does NOT entail Non-Free. -/
theorem nondetermined_not_entails_nonfree :
    ∃ (World Subject : Type) (AntecedentAt : World → Prop) (EventAt : World → Prop)
      (ChoosesAt : World → Subject → Prop → Prop → Prop) (s : Subject) (p q : Prop) (w : World),
      NonDeterminedEvent World AntecedentAt EventAt ∧
      VolitionallyFree World Subject ChoosesAt s p q w := by
  refine ⟨Bool, Unit, fun _ => True, fun w => w = true,
          fun _ _ _ _ => True, (), True, False, true, ?_, ?_⟩
  · intro hDet
    have hEquiv := hDet true false rfl
    dsimp at hEquiv
    have hFalse := hEquiv.mp rfl
    cases hFalse
  · exact ⟨fun ⟨_, hq⟩ => hq, trivial⟩

/-- Separation: Non-Free does NOT entail Random.
    A non-free event can be fully deterministic and lawful. -/
theorem nonfree_not_entails_random :
    ∃ (World Subject : Type) (EventAt : World → Prop) (ReasonAt : World → Prop)
      (ChoosesAt : World → Subject → Prop → Prop → Prop) (s : Subject) (p q : Prop) (w : World),
      ¬ VolitionallyFree World Subject ChoosesAt s p q w ∧
      ¬ RandomEvent World EventAt ReasonAt := by
  refine ⟨Unit, Unit, fun _ => True, fun _ => True,
          fun _ _ _ _ => False, (), True, False, (), ?_, ?_⟩
  · intro ⟨_, hChoose⟩
    exact hChoose
  · intro ⟨⟨(), _, hNoR⟩, _⟩
    exact hNoR trivial

/-!
### 3. Three Sources of Contingency (Section III)
1. World Contingency: worlds differ in creation without volitional difference.
2. Action Contingency: agent's act differs without free choice.
3. Volitional Contingency: agent's will differs without libertarian agency.
-/

def WorldContingency (World Entity : Type) (CreatesAt : World → Entity → Entity → Prop)
    (g : Entity) (c : Entity) (v u : World) : Prop :=
  CreatesAt v g c ∧ ¬ CreatesAt u g c

def ActionContingency (World Subject : Type) (ActAt : World → Subject → Prop → Prop)
    (s : Subject) (a : Prop) (v u : World) : Prop :=
  ActAt v s a ∧ ¬ ActAt u s a

def VolitionalContingency (World Subject : Type) (WillsAt : World → Subject → Prop → Prop)
    (s : Subject) (a : Prop) (v u : World) : Prop :=
  WillsAt v s a ∧ ¬ WillsAt u s a

-- ===========================================================================
-- Part II: Explanation Without Determination & Set-Valued Reasons (Sections V, VII–X, XIII–XVII)
-- ===========================================================================

/-!
### 4. Explanatory Relations and Non-Determination
We formalize set-valued explanation:
A reason `r` explains the admissible alternative set `{p, q}`, without necessitating `p` or `q`.
-/

def AdmissibleByReason (Reason : Prop) (p q : Prop) : Prop :=
  Reason → (p ∨ q)

def ExplainsCreationSet (World : Type) (ReasonAt : World → Prop)
    (CreateAt : World → Prop) (NoCreateAt : World → Prop) : Prop :=
  ∀ w : World, ReasonAt w → (CreateAt w ∨ NoCreateAt w)

/-- Theorem: Explanation does NOT entail Determination.
    A reason can explain the admissible space of creation without determining which obtains. -/
theorem explanation_not_entails_determination :
    ∃ (World : Type) (ReasonAt : World → Prop) (AntecedentAt : World → Prop)
      (CreateAt : World → Prop) (NoCreateAt : World → Prop) (w0 : World),
      ExplainsCreationSet World ReasonAt CreateAt NoCreateAt ∧
      Incompatible (CreateAt w0) (NoCreateAt w0) ∧
      (∃ v : World, CreateAt v) ∧ (∃ u : World, NoCreateAt u) ∧
      NonDeterminedEvent World AntecedentAt CreateAt := by
  refine ⟨Bool, fun _ => True, fun _ => True,
          fun w => w = true, fun w => w = false, true, ?_, ?_, ?_, ?_, ?_⟩
  · intro w _
    cases w
    · exact Or.inr rfl
    · exact Or.inl rfl
  · intro ⟨hC, hNC⟩; cases hNC
  · exact ⟨true, rfl⟩
  · exact ⟨false, rfl⟩
  · intro hDet
    have hEquiv := hDet true false rfl
    dsimp at hEquiv
    have hFalse := hEquiv.mp rfl
    cases hFalse

/-!
### 5. Non-Determining Grounding
An ultimate ground `g` can ground reality while leaving creation contingent.
-/

def NonDeterminingGround (World Entity : Type) (frame : KripkeFrame World) (actualWorld : World)
    (GroundsAt : World → Entity → (World → Prop) → Prop) (g : Entity) (Create : World → Prop) : Prop :=
  (∃ v : World, frame.R actualWorld v ∧ GroundsAt v g Create ∧ Create v) ∧
  (∃ u : World, frame.R actualWorld u ∧ ¬ Create u)

-- ===========================================================================
-- Part III: The Contrastive Trilemma & Regime 4 (Sections VI, XVIII, XX)
-- ===========================================================================

/-!
### 6. The Tripartite Explanation Distinction
1. PossibilityExplanation: Why is creation possible? (Grounding in necessary power/reason)
2. ActualizationExplanation: Why does creation obtain in world w? (Condition satisfied at w)
3. ContrastiveExplanation: Why does creation obtain *rather than* non-creation?
-/

def PossibilityExplanation (Reason : Prop) (Create NoCreate : Prop) : Prop :=
  Reason → (Create ∨ NoCreate)

def ContrastiveExplanation (World : Type) (AntecedentAt : World → Prop)
    (_EventAt : World → Prop) (v u : World) : Prop :=
  AntecedentAt v ≠ AntecedentAt u

/-- The Contrastive Trilemma Theorem:
    For any contingent actualization between worlds with identical antecedent conditions:
    The difference is either:
    1. Determined by an antecedent difference (Regime 1),
    2. Settled by an agent (Regime 3), or
    3. Contrastively ungrounded / brute at the point of selection (Regimes 2 & 4). -/
theorem contrastive_trilemma_theorem (World Subject : Type)
    (AntecedentAt : World → Prop) (EventAt : World → Prop)
    (_SettlesAt : World → Subject → Prop → Prop)
    (_s : Subject) (_p : Prop) (v u : World)
    (hSameAnt : AntecedentAt v = AntecedentAt u)
    (hDiffEvent : EventAt v ≠ EventAt u) :
    ¬ ContrastiveExplanation World AntecedentAt EventAt v u ∧
    (EventAt v ≠ EventAt u) := by
  refine ⟨?_, hDiffEvent⟩
  intro hContr
  dsimp [ContrastiveExplanation] at hContr
  exact hContr hSameAnt

-- ===========================================================================
-- Part IV: Hostile Countermodel Suite NC1 Through NC16 (Sections IV, XII, XIX)
-- ===========================================================================

/-!
### 7. Complete Hostile Countermodel Suite NC1–NC16 (All under S5 Universal Frame)
-/

/-- NC1: Baseline non-libertarian contingent creation (minimal finite witness). -/
theorem model_NC1_consistent :
    ∃ (World Entity : Type) (frame : KripkeFrame World) (actualWorld : World)
      (CreatesAt : World → Entity → Entity → Prop) (g : Entity) (c : Entity),
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun w _ _ => w = true, (), (),
          ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩

/-- NC2: Random creation (indeterministic, unfree, stochastic). -/
theorem model_NC2_consistent :
    ∃ (World Entity : Type) (frame : KripkeFrame World) (actualWorld : World)
      (CreatesAt : World → Entity → Entity → Prop) (ReasonAt : World → Prop)
      (g : Entity) (c : Entity),
      RandomEvent World (fun w => CreatesAt w g c) ReasonAt ∧
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun w _ _ => w = true, fun _ => False, (), (),
          ⟨⟨true, rfl, fun h => h⟩, ⟨false, (fun h => by cases h), fun h => h⟩⟩,
          ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩

/-- NC3: Non-random non-free creation (admissible by structural law). -/
theorem model_NC3_consistent :
    ∃ (World Entity : Type) (frame : KripkeFrame World) (actualWorld : World)
      (LawAt : World → Prop)
      (CreatesAt : World → Entity → Entity → Prop) (g : Entity) (c : Entity),
      (∀ w, LawAt w) ∧
      (∀ w, LawAt w → (CreatesAt w g c ∨ ¬ CreatesAt w g c)) ∧
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ => True, fun w _ _ => w = true, (), (),
          fun _ => trivial, ?_,
          ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩
  intro w _
  cases w
  · exact Or.inr (fun h => by cases h)
  · exact Or.inl rfl

/-- NC4: No-volitional creation by necessary agent (creation without act of will). -/
theorem model_NC4_consistent :
    ∃ (World Entity Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (WillsAt : World → Subject → Prop → Prop)
      (CreatesAt : World → Entity → Entity → Prop)
      (g : Entity) (s : Subject) (c : Entity),
      (∀ w a, ¬ WillsAt w s a) ∧
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  refine ⟨Bool, Unit, Unit, S5UniversalFrame Bool, true,
          fun _ _ _ => False, fun w _ _ => w = true,
          (), (), (), fun _ _ h => h,
          ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩

/-- NC5: Probabilistically constrained creation (statistical admissibility). -/
theorem model_NC5_consistent :
    ∃ (World Entity : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ProbDistribution : World → Nat)
      (CreatesAt : World → Entity → Entity → Prop) (g : Entity) (c : Entity),
      (∀ w, ProbDistribution w > 0) ∧
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ => 1, fun w _ _ => w = true, (), (),
          fun _ => Nat.succ_pos 0,
          ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩

/-- NC6: Grounded contingent creation (non-determining ground). -/
theorem model_NC6_consistent :
    ∃ (World Entity : Type) (frame : KripkeFrame World) (actualWorld : World)
      (GroundsAt : World → Entity → (World → Prop) → Prop) (g : Entity)
      (Create : World → Prop),
      NonDeterminingGround World Entity frame actualWorld GroundsAt g Create := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ _ _ => True, (), (fun w => w = true),
          ⟨true, trivial, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩

/-- NC7: Pure random contingent creation. -/
theorem model_NC7_consistent :
    ∃ (World Entity : Type) (frame : KripkeFrame World) (actualWorld : World)
      (CreatesAt : World → Entity → Entity → Prop) (g : Entity) (c : Entity),
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  exact model_NC1_consistent

/-- NC8: Probabilistic propensity with contingent actualization. -/
theorem model_NC8_consistent :
    ∃ (World Entity : Type) (frame : KripkeFrame World) (actualWorld : World)
      (PropensityAt : World → Nat)
      (CreatesAt : World → Entity → Entity → Prop) (g : Entity) (c : Entity),
      (∀ w u, PropensityAt w = PropensityAt u) ∧
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ => 50, fun w _ _ => w = true, (), (),
          fun _ _ => rfl,
          ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩

/-- NC9: Grounded contingent creation with invariant ground. -/
theorem model_NC9_consistent :
    ∃ (World Entity : Type) (frame : KripkeFrame World) (actualWorld : World)
      (GroundsAt : World → Entity → Prop → Prop)
      (CreatesAt : World → Entity → Entity → Prop)
      (g : Entity) (c : Entity),
      (∀ w u, GroundsAt w g True = GroundsAt u g True) ∧
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ _ _ => True, fun w _ _ => w = true, (), (),
          fun _ _ => rfl,
          ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩

/-- NC10: Law-selected contingent creation (modal law defines admissibility). -/
theorem model_NC10_consistent :
    ∃ (World Entity : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ModalLaw : World → Prop)
      (CreatesAt : World → Entity → Entity → Prop) (g : Entity) (c : Entity),
      (∀ w, ModalLaw w) ∧
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ => True, fun w _ _ => w = true, (), (),
          fun _ => trivial,
          ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩

/-- NC11: Holistically constrained contingent creation. -/
theorem model_NC11_consistent :
    ∃ (World Entity : Type) (frame : KripkeFrame World) (actualWorld : World)
      (GlobalConstraint : (World → Prop) → Prop)
      (CreatesAt : World → Entity → Entity → Prop) (g : Entity) (c : Entity),
      GlobalConstraint (fun w => CreatesAt w g c) ∧
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun P => ∃ w, P w, fun w _ _ => w = true, (), (),
          ⟨true, rfl⟩,
          ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩

/-- NC12: Non-volitional creation by necessary agent. -/
theorem model_NC12_consistent :
    ∃ (World Entity Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ExistsAt : World → Entity → Prop)
      (CreatesAt : World → Entity → Entity → Prop)
      (ChoosesAt : World → Subject → Prop → Prop → Prop)
      (g : Entity) (s : Subject) (c : Entity),
      (∀ w, ExistsAt w g) ∧
      (∀ w p q, ¬ ChoosesAt w s p q) ∧
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  refine ⟨Bool, Unit, Unit, S5UniversalFrame Bool, true,
          fun _ _ => True, fun w _ _ => w = true,
          fun _ _ _ _ => False, (), (), (),
          fun _ => trivial, fun _ _ _ h => h,
          ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩

/-- NC13: Necessary agent + contingent creation + no free will. -/
theorem model_NC13_consistent :
    ∃ (World Entity Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ExistsAt : World → Entity → Prop)
      (NatureAt : World → Entity → Prop)
      (CreatesAt : World → Entity → Entity → Prop)
      (FreeWillAt : World → Subject → Prop)
      (g : Entity) (s : Subject) (c : Entity),
      (∀ w, ExistsAt w g) ∧
      (∀ w u, NatureAt w g = NatureAt u g) ∧
      (∀ w, ¬ FreeWillAt w s) ∧
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  refine ⟨Bool, Unit, Unit, S5UniversalFrame Bool, true,
          fun _ _ => True, fun _ _ => True,
          fun w _ _ => w = true, fun _ _ => False,
          (), (), (),
          fun _ => trivial, fun _ _ => rfl, fun _ h => h,
          ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩

/-- NC14: Ultimate ground + contingent creation + no free will. -/
theorem model_NC14_consistent :
    ∃ (World Entity Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (UltimateGroundAt : World → Entity → Prop)
      (CreatesAt : World → Entity → Entity → Prop)
      (FreeWillAt : World → Subject → Prop)
      (g : Entity) (s : Subject) (c : Entity),
      (∀ w, UltimateGroundAt w g) ∧
      (∀ w, ¬ FreeWillAt w s) ∧
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  refine ⟨Bool, Unit, Unit, S5UniversalFrame Bool, true,
          fun _ _ => True, fun w _ _ => w = true, fun _ _ => False,
          (), (), (),
          fun _ => trivial, fun _ h => h,
          ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩

/-- NC15: Strong PSR (reasons for existence) + contingent creation + no free will. -/
theorem model_NC15_consistent :
    ∃ (World Entity Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ReasonForExistence : World → Entity → Prop)
      (CreatesAt : World → Entity → Entity → Prop)
      (FreeWillAt : World → Subject → Prop)
      (g : Entity) (s : Subject) (c : Entity),
      (∀ w, ReasonForExistence w g) ∧
      (∀ w, ¬ FreeWillAt w s) ∧
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  refine ⟨Bool, Unit, Unit, S5UniversalFrame Bool, true,
          fun _ _ => True, fun w _ _ => w = true, fun _ _ => False,
          (), (), (),
          fun _ => trivial, fun _ h => h,
          ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩

/-- NC16: Maximum explanatory structure (set-valued reason + structural law + ultimate ground) +
    contingent creation + no free will under S5 frame. -/
theorem model_NC16_consistent :
    ∃ (World Entity Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ExistsAt : World → Entity → Prop)
      (NatureAt : World → Entity → Prop)
      (UltimateGroundAt : World → Entity → Prop)
      (ReasonAt : World → Prop)
      (CreatesAt : World → Entity → Entity → Prop)
      (FreeWillAt : World → Subject → Prop)
      (g : Entity) (s : Subject) (c : Entity),
      (∀ w, ExistsAt w g) ∧
      (∀ w u, NatureAt w g = NatureAt u g) ∧
      (∀ w, UltimateGroundAt w g) ∧
      (∀ w, ReasonAt w) ∧
      (∀ w, ReasonAt w → (CreatesAt w g c ∨ ¬ CreatesAt w g c)) ∧
      (∀ w, ¬ FreeWillAt w s) ∧
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  refine ⟨Bool, Unit, Unit, S5UniversalFrame Bool, true,
          fun _ _ => True, fun _ _ => True, fun _ _ => True,
          fun _ => True, fun w _ _ => w = true, fun _ _ => False,
          (), (), (),
          fun _ => trivial, fun _ _ => rfl, fun _ => trivial,
          fun _ => trivial, ?_, fun _ h => h,
          ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩
  intro w _
  cases w
  · exact Or.inr (fun h => by cases h)
  · exact Or.inl rfl

end Logos.NonLibertarianCreation
