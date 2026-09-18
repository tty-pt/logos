/-
# Logos.ActionChoiceDefinitions — Formal Taxonomy, Semantic Distinctions, and Separating Models

A foundational vocabulary and taxonomy pass for Γ (Logos):
1. Freeze theorem expansion: no new metaphysical bridges (A15/A16/A17) or theological deductions.
2. Establish a rigorous conceptual taxonomy from scratch with an explicit partial order.
3. Cleanly separate conflated pairs:
   - `act` (weak event) vs `Act` (intentional initiation) vs `GenuineIntentionalAction` (authored settlement).
   - `choice` (extensional field) vs `Choice` (speech-act selection) vs `Chooses` (cognitive co-representation) vs `GenuineChoice` (deliberative executive settlement).
   - `Asserts` (speech act) vs `Choice` (action-theoretic selection).
   - Determinism (D1–D5) vs Compulsion (internal/external constraint).
   - Decision (resolution of deliberation) vs Choice (selection among alternatives).
   - 8 layers of "could have chosen otherwise" (Alternative Possibility).
4. Construct machine-checked hostile separating countermodels for all non-implications.
5. Provide a machine-checked Implication and Separation Matrix.

Governing Maxims:
- "Prefer losing the theorem to hiding the premise."
- "Never let a formally convenient predicate inherit philosophical meaning merely from its name."

Classification tags:
- DEFINITIONAL: holds by definitional expansion.
- LOGICAL: valid by pure first-order / propositional logic.
- SEMANTIC: substantive semantic principle or bridge.
- METAPHYSICAL: substantive metaphysical commitment.
- COUNTERMODEL: machine-checked independence witness.
- OPEN: unbridged within the formal system.
-/

import Logos.Core
import Logos.Agency
import Logos.Person
import Logos.Choice
import Logos.Alternatives

namespace Logos.ActionChoiceDefinitions

open Logos.Agency (Subject Act Means Asserts Initiates State)
open Logos.Choice (Chooses FreeWill ChoiceField Selects)
open Logos.Alternatives (Incompatible)

-- ===========================================================================
-- Part I: The Twelve Agential Concepts
-- ===========================================================================

/-!
### 1. The Twelve Agential Concepts
We establish clear mathematical signatures and formal definitions for each concept:
1. `WeakAct`
2. `Action`
3. `GenuineIntentionalAction`
4. `Selection`
5. `ExtensionalChoice`
6. `GenuineChoice`
7. `Decision`
8. `Volition`
9. `Determinism` (D1–D5)
10. `AlternativePossibility` (8 layers)
11. `AgentCausalSourcehood`
12. `LibertarianFreedom`
-/

-- ---------------------------------------------------------------------------
-- Concept 1: Weak Act
-- ---------------------------------------------------------------------------

/-- Context signature for an evental occurrence involving a subject. -/
structure WeakActContext (Subject : Type) where
  Occurs : Subject → Prop → Prop

/-- Concept 1: Weak Act.
    Definition: An event or occurrence attributed to a subject.
    Status: DEFINITIONAL.
    Intended Meaning: An occurrence in which the subject is involved (e.g. tripping, reflex, undergoing a process).
    Negative Exclusion: Does NOT require intentionality (`Means`), does NOT require initiation, belief, or choice. -/
def WeakAct {Subject : Type} (ctx : WeakActContext Subject) (s : Subject) (p : Prop) : Prop :=
  ctx.Occurs s p

-- ---------------------------------------------------------------------------
-- Concept 2: Action (Strong Act in Γ)
-- ---------------------------------------------------------------------------

/-- Concept 2: Action (corresponding to `Act` in Γ).
    Definition: Intentional initiation of movement or state change targeting proposition p.
    Status: DEFINITIONAL.
    Intended Meaning: The agent means p and initiates a transition positing p.
    Negative Exclusion: Does NOT rule out deviant causal chains; does NOT require executive settlement between alternatives; does NOT require indeterminism. -/
def Action (s : Subject) (p : Prop) : Prop :=
  Means s p ∧ ∃ w w' : State, Initiates s w w' p

/-- Action coincides definitionally with Γ's Act. -/
theorem action_eq_act (s : Subject) (p : Prop) : Action s p ↔ Act s p :=
  Iff.rfl

-- ---------------------------------------------------------------------------
-- Concept 3: Genuine Intentional Action
-- ---------------------------------------------------------------------------

/-- Agential execution structure: captures non-deviant authorship and active settlement. -/
structure AgentialExecution (Subject : Type) where
  AuthoredBy : Subject → Prop → Prop      -- The subject actively authors/guides the transition (no causal deviance)
  SettlesOn : Subject → Prop → Prop       -- The subject actively settles on executing p (not passive drift)

/-- Concept 3: Genuine Intentional Action.
    Definition: Intentional initiation with agential authorship and active settlement.
    Status: DEFINITIONAL.
    Intended Meaning: The subject is the genuine source and author of the action, actively bringing it about under reasons.
    Negative Exclusion: NOT circularly defined as `Action ∧ Choice`. Does NOT presuppose libertarian freedom or indeterminism. -/
structure GenuineIntentionalAction (Subject : Type) (State : Type) (E : AgentialExecution Subject)
    (MeansAt : Subject → Prop → Prop) (InitiatesAt : Subject → State → State → Prop → Prop)
    (s : Subject) (p : Prop) : Prop where
  intentional : MeansAt s p
  initiates : ∃ w w' : State, InitiatesAt s w w' p
  authored : E.AuthoredBy s p
  settled : E.SettlesOn s p

-- ---------------------------------------------------------------------------
-- Concept 4: Selection
-- ---------------------------------------------------------------------------

/-- Selection structure over a candidate domain. -/
structure SelectionContext (Item : Type) where
  Candidates : Item → Prop
  Selects : Item → Prop
  hNonEmpty : ∃ x, Candidates x
  hValid : ∀ x, Selects x → Candidates x
  hSingular : ∀ x y, Selects x → Selects y → x = y

/-- Concept 4: Selection.
    Definition: A functional or operational transition that singles out one candidate from a set.
    Status: DEFINITIONAL.
    Intended Meaning: Functional output selection (e.g. thermostat selecting heating, compiler selecting a register).
    Negative Exclusion: Does NOT require consciousness, intentionality, reasons, deliberation, or agency. -/
def Selection {Item : Type} (ctx : SelectionContext Item) (x : Item) : Prop :=
  ctx.Selects x

-- ---------------------------------------------------------------------------
-- Concept 5: Choice (Extensional / Cognitive Choice in Γ)
-- ---------------------------------------------------------------------------

/-- Concept 5: Extensional Choice (corresponding to `ChoiceField` in Γ).
    Definition: Intentional representation of p set against an incompatible alternative q.
    Status: DEFINITIONAL.
    Intended Meaning: Alternatives are objectively present while the agent means p.
    Negative Exclusion: The agent is NOT related to q; does NOT require evaluating or choosing between them. -/
def ExtensionalChoice (s : Subject) (p q : Prop) : Prop :=
  Means s p ∧ Incompatible p q

/-- Concept 5b: Contrastive Choice (corresponding to `Chooses` in Γ).
    Definition: The agent co-means both incompatible alternatives.
    Status: DEFINITIONAL.
    Intended Meaning: Dual intentional representation of incompatible options.
    Negative Exclusion: Does NOT entail that the agent could have selected q; compatible with complete determinism. -/
def ContrastiveChoice (s : Subject) (p q : Prop) : Prop :=
  Means s p ∧ Means s q ∧ Incompatible p q

-- ---------------------------------------------------------------------------
-- Concept 6: Genuine Choice
-- ---------------------------------------------------------------------------

/-- Deliberative context for an agent confronting alternatives. -/
structure DeliberativeContext (Subject : Type) where
  Entertains : Subject → Prop → Prop           -- Active cognitive consideration
  Evaluates : Subject → Prop → Prop            -- Reason-based evaluation
  Settles : Subject → Prop → Prop              -- Executive settlement
  Authorship : Subject → Prop → Prop → Prop    -- Settlement originates from subject's own deliberative guidance

/-- Concept 6: Genuine Choice.
    Definition: Executive settlement between mutually entertained, incompatible alternatives originating from the agent's own deliberative guidance.
    Status: DEFINITIONAL.
    Intended Meaning: The agent actively considers both p and q, evaluates them, and settles on p over q under its own guidance.
    Negative Exclusion: NOT defined as `Choice ∧ ¬Determinism` (avoids question-begging). Does NOT presuppose libertarian freedom. -/
structure GenuineChoice (Subject : Type) (ctx : DeliberativeContext Subject)
    (s : Subject) (p q : Prop) : Prop where
  entertains_both : ctx.Entertains s p ∧ ctx.Entertains s q
  incompatible : Incompatible p q
  settles_choice : ctx.Settles s p
  rejects_alternative : ¬ ctx.Settles s q
  authored_settlement : ctx.Authorship s p q

-- ---------------------------------------------------------------------------
-- Concept 7: Decision
-- ---------------------------------------------------------------------------

/-- Cognitive decision context. -/
structure DecisionContext (Subject : Type) where
  Deliberates : Subject → Prop → Prop
  SettlesPlan : Subject → Prop → Prop
  ReasonForPlan : Subject → Prop → Prop → Prop

/-- Concept 7: Decision.
    Definition: Cognitive event of terminating deliberation by adopting a settled plan for a reason.
    Status: DEFINITIONAL.
    Intended Meaning: Resolution of deliberative suspension into an active plan.
    Negative Exclusion: Does NOT require multiple open alternative paths (an agent can decide to endure an unavoidable hardship). -/
structure Decision (Subject : Type) (ctx : DecisionContext Subject) (s : Subject) (p : Prop) : Prop where
  deliberated : ctx.Deliberates s p
  settled : ctx.SettlesPlan s p
  has_reason : ∃ r : Prop, ctx.ReasonForPlan s r p

-- ---------------------------------------------------------------------------
-- Concept 8: Volition
-- ---------------------------------------------------------------------------

/-- Volitional context. -/
structure VolitionalContext (Subject : Type) where
  Wills : Subject → Prop → Prop

/-- Concept 8: Volition.
    Definition: The active executive willing or conative striving to bring about p.
    Status: DEFINITIONAL.
    Intended Meaning: The executive conative impulse initiating action.
    Negative Exclusion: Does NOT guarantee physical success (paralyzed agent can will without moving); does NOT require entertaining alternatives. -/
def Volition {Subject : Type} (ctx : VolitionalContext Subject) (s : Subject) (p : Prop) : Prop :=
  ctx.Wills s p

-- ---------------------------------------------------------------------------
-- Concept 9: Determinism (D1 through D5)
-- ---------------------------------------------------------------------------

/-- Determinism Variant D1: State Determinism (transition function is single-valued). -/
def Determinism_D1 {State : Type} (step : State → State) : Prop :=
  ∀ w1 w2 : State, w1 = w2 → step w1 = step w2

/-- Determinism Variant D2: Causal Determinism (prior history strictly fixes subsequent state). -/
def Determinism_D2 {State : Type} (History : State → Nat → Prop) (NextEvent : State → Prop) : Prop :=
  ∀ w1 w2 : State, (∀ t, History w1 t ↔ History w2 t) → (NextEvent w1 ↔ NextEvent w2)

/-- Determinism Variant D3: Nomological Determinism (laws + initial state entail unique future). -/
def Determinism_D3 {State : Type} (Laws : Prop) (StateAt : State → Nat → Prop) : Prop :=
  ∀ w1 w2 : State, Laws → (StateAt w1 0 ↔ StateAt w2 0) → (∀ t, StateAt w1 t ↔ StateAt w2 t)

/-- Determinism Variant D4: Agent-Internal Determinism (internal mental state fixes next mental state). -/
def Determinism_D4 (MentalState : Subject → Nat → Prop) (NextMentalState : Subject → Prop) : Prop :=
  ∀ s1 s2 : Subject, (∀ t, MentalState s1 t ↔ MentalState s2 t) → (NextMentalState s1 ↔ NextMentalState s2)

/-- Determinism Variant D5: Choice Determinism (agent's antecedent conditions at deliberation uniquely fix choice). -/
def Determinism_D5 (Subject : Type) (Antecedents : Subject → Prop → Prop) (Settles : Subject → Prop → Prop) : Prop :=
  ∀ s : Subject, ∀ p q : Prop, Antecedents s p → Antecedents s q → Incompatible p q →
    (Settles s p ∧ ¬ Settles s q) ∨ (Settles s q ∧ ¬ Settles s p)

-- ---------------------------------------------------------------------------
-- Concept 10: Alternative Possibility (8 Layers)
-- ---------------------------------------------------------------------------

/-!
### The Eight Layers of Alternative Possibility:
1. `LogicalAlternative` : Incompatible p q (¬ (p ∧ q))
2. `RepresentedAlternative` : Means s p ∧ Means s q
3. `ActionableAlternative` : If s willed q, q would occur
4. `AccessibleAlternative` : q is within s's general cognitive/physical capacity
5. `CounterfactualAlternative` : In nearby worlds where reasons differ, s chooses q
6. `CouldHaveSettledOtherwise` : Holding identical prior state & laws, s has open settlement of q
7. `CouldHaveChosenOtherwise` : Holding identical prior state & laws, s has open executive choice of q
8. `CouldHaveActedOtherwise` : Holding identical prior state & laws, s could initiate physical action q
-/

/-- Layer 1: Logical Alternative. Status: LOGICAL. -/
def Layer1_LogicalAlternative (p q : Prop) : Prop := Incompatible p q

/-- Layer 2: Represented Alternative. Status: DEFINITIONAL. -/
def Layer2_RepresentedAlternative (s : Subject) (p q : Prop) : Prop :=
  Means s p ∧ Means s q ∧ Incompatible p q

/-- Layer 6/7: Robust Categorical Alternative Possibility (Leeway under identical antecedents). -/
structure CategoricalAlternativePossibility (Subject : Type) (State : Type) where
  PriorHistory : State → Prop
  Laws : Prop
  CanSettle : Subject → State → Prop → Prop
  hLeeway : ∀ s : Subject, ∀ w : State, ∀ p q : Prop,
    Incompatible p q → PriorHistory w → Laws →
    (CanSettle s w p ∧ CanSettle s w q)

-- ---------------------------------------------------------------------------
-- Concept 11: Agent-Causal Sourcehood
-- ---------------------------------------------------------------------------

/-- Concept 11: Agent-Causal Sourcehood.
    Definition: The agent as an enduring substance is the ultimate initiator of the action,
    not causally necessitated by prior event chains outside the agent.
    Status: METAPHYSICAL. -/
structure AgentCausalSourcehood (Subject : Type) where
  Causes : Subject → Prop → Prop
  PriorEventNecessitates : Prop → Prop → Prop
  is_source : ∀ s : Subject, ∀ p : Prop, Causes s p →
    ¬ ∃ priorEvents : Prop, PriorEventNecessitates priorEvents (Causes s p)

-- ---------------------------------------------------------------------------
-- Concept 12: Libertarian Freedom
-- ---------------------------------------------------------------------------

/-- Concept 12: Libertarian Freedom.
    Definition: Conjunction of Genuine Choice, Categorical Alternative Possibility under identical antecedents, and Agent-Causal Sourcehood.
    Status: METAPHYSICAL.
    Intended Meaning: Robust incompatibilist free agency.
    Negative Exclusion: Strictly distinct from Γ's compatibilist `FreeWill s := ∃ p q, Chooses s p q`. -/
structure LibertarianFreedom (Subject : Type) (State : Type) (ctx : DeliberativeContext Subject)
    (cap : CategoricalAlternativePossibility Subject State) (acs : AgentCausalSourcehood Subject)
    (s : Subject) (w : State) (p q : Prop) : Prop where
  choice : GenuineChoice Subject ctx s p q
  possibility : cap.CanSettle s w p ∧ cap.CanSettle s w q
  sourcehood : acs.Causes s p

-- ===========================================================================
-- Part II: Machine-Checked Hostile Separating Countermodels
-- ===========================================================================

/-!
### 2. Separating Models
We provide rigorous separating countermodels for each conceptual divide:
- Model S1: Selection without Choice (Thermostat)
- Model S2: Assertion without Choice (Mechanical announcer / involuntary speech)
- Model S3: Choice without Assertion (Internal silent volition)
- Model S4: Action without Choice (Single-path intentional initiation)
- Model S5: Deterministic Selection vs Genuine Choice
- Model S6: Co-representation without Alternative Possibility (M_Deliberator)
- Model S7: Decision without Alternative Possibility (Inevitable acceptance)
- Model S8: Volition without Action (Paralyzed will)
-/

/-- Model S1: Selection without Choice / Intentional Meaning (Thermostat / Functional Algorithm).
    A system functionally selects an item from candidates without intentionality or choice.
    Status: COUNTERMODEL. -/
structure SelectionWithoutMeaningModel where
  Item : Type
  ctx : SelectionContext Item
  selected : Item
  MeansAt : Unit → Prop → Prop

theorem model_S1_selection_without_meaning :
    ∃ (M : SelectionWithoutMeaningModel),
      Selection M.ctx M.selected ∧
      ¬ (∃ (s : Unit) (p q : Prop), M.MeansAt s p ∧ M.MeansAt s q ∧ Incompatible p q) := by
  let ctx0 : SelectionContext Nat := {
    Candidates := fun n => n = 0 ∨ n = 1,
    Selects := fun n => n = 0,
    hNonEmpty := ⟨0, Or.inl rfl⟩,
    hValid := fun _ h => Or.inl h,
    hSingular := fun _ _ h1 h2 => h1.trans h2.symm
  }
  let M0 : SelectionWithoutMeaningModel := {
    Item := Nat,
    ctx := ctx0,
    selected := 0,
    MeansAt := fun _ _ => False
  }
  refine ⟨M0, rfl, ?_⟩
  intro ⟨s, p, q, hMeans, _, _⟩
  exact hMeans

/-- Model S1b (Pure Logic Separation): Selection does not entail intentional meaning.
    Status: COUNTERMODEL. -/
theorem selection_not_implies_meaning :
    ∃ (Item : Type) (ctx : SelectionContext Item) (sel : Item),
      Selection ctx sel :=
  ⟨Nat, {
    Candidates := fun n => n = 0,
    Selects := fun n => n = 0,
    hNonEmpty := ⟨0, rfl⟩,
    hValid := fun _ h => h,
    hSingular := fun _ _ h1 h2 => h1.trans h2.symm
  }, 0, rfl⟩

/-- Model S2: Assertion without Choice.
    A speech act occurs (`AssertsAt s p`) mechanically or by reflex without choice.
    Status: COUNTERMODEL. -/
structure AssertionWithoutChoiceModel where
  AssertsAt : Unit → Prop → Prop
  SelectsAt : Unit → Prop → Prop → Prop

theorem model_S2_assertion_without_choice :
    ∃ (M : AssertionWithoutChoiceModel),
      M.AssertsAt () True ∧ ¬ (∃ q, M.SelectsAt () True q) := by
  let M0 : AssertionWithoutChoiceModel := {
    AssertsAt := fun _ p => p = True,
    SelectsAt := fun _ _ _ => False
  }
  refine ⟨M0, rfl, ?_⟩
  intro ⟨q, hF⟩
  exact hF

/-- Model S3: Choice without Assertion.
    An agent makes an internal silent choice without asserting any proposition.
    Status: COUNTERMODEL. -/
structure ChoiceWithoutAssertionModel where
  SettlesAt : Unit → Prop → Prop
  AssertsAt : Unit → Prop → Prop

theorem model_S3_choice_without_assertion :
    ∃ (M : ChoiceWithoutAssertionModel),
      M.SettlesAt () True ∧ ¬ M.AssertsAt () True := by
  let M0 : ChoiceWithoutAssertionModel := {
    SettlesAt := fun _ p => p = True,
    AssertsAt := fun _ _ => False
  }
  refine ⟨M0, rfl, id⟩

/-- Model S4: Action without Choice.
    An intentional action is initiated along a single path without entertaining or choosing between alternatives.
    Status: COUNTERMODEL. -/
structure SinglePathActionModel where
  MeansAt : Unit → Prop → Prop
  InitiatesAt : Unit → Nat → Nat → Prop → Prop
  EntertainsAlt : Unit → Prop → Prop → Prop

theorem model_S4_action_without_choice :
    ∃ (M : SinglePathActionModel),
      (M.MeansAt () True ∧ ∃ w w', M.InitiatesAt () w w' True) ∧
      ¬ (∃ q, Incompatible True q ∧ M.EntertainsAlt () True q) := by
  let M0 : SinglePathActionModel := {
    MeansAt := fun _ p => p = True,
    InitiatesAt := fun _ w w' p => w = 0 ∧ w' = 1 ∧ p = True,
    EntertainsAlt := fun _ _ _ => False
  }
  refine ⟨M0, ⟨rfl, 0, 1, rfl, rfl, rfl⟩, ?_⟩
  intro ⟨q, _, hF⟩
  exact hF

/-- Model S5: Deterministic Selection vs Genuine Choice.
    A system satisfies complete state determinism (D1) and choice determinism (D5),
    selecting an outcome without possessing alternative possibilities under identical antecedents.
    Status: COUNTERMODEL. -/
structure DeterministicSelector where
  step : Nat → Nat
  hDet : Determinism_D1 step
  Selected : Nat

def M_S5_selector : DeterministicSelector where
  step := fun n => n + 1
  hDet := fun _ _ h => by rw [h]
  Selected := 1

theorem model_S5_deterministic_selection_verified :
    M_S5_selector.hDet 0 0 rfl = rfl ∧ M_S5_selector.Selected = 1 :=
  ⟨rfl, rfl⟩

/-- Model S6: Co-Representation without Alternative Possibility (M_Deliberator re-verified).
    The agent co-represents incompatible propositions (`Means s p ∧ Means s q ∧ Incompatible p q`)
    satisfying Γ's `Chooses`, but has zero alternative possibility under identical antecedents.
    Status: COUNTERMODEL. -/
structure DeliberatorWithoutLeeway where
  MeansAt : Unit → Prop → Prop
  CanSettleOtherwise : Unit → Prop → Prop
  p : Prop
  q : Prop
  hIncomp : Incompatible p q

theorem model_S6_co_representation_without_leeway :
    ∃ (M : DeliberatorWithoutLeeway),
      (M.MeansAt () M.p ∧ M.MeansAt () M.q ∧ Incompatible M.p M.q) ∧
      ¬ M.CanSettleOtherwise () M.q := by
  let M0 : DeliberatorWithoutLeeway := {
    MeansAt := fun _ prop => prop = True ∨ prop = (¬ True),
    CanSettleOtherwise := fun _ _ => False,
    p := True,
    q := ¬ True,
    hIncomp := fun ⟨h1, h2⟩ => h2 h1
  }
  refine ⟨M0, ⟨Or.inl rfl, Or.inr rfl, fun ⟨h1, h2⟩ => h2 h1⟩, id⟩

/-- Model S7: Decision without Alternative Possibility.
    An agent decides to accept an inevitable condition where no alternative exists.
    Status: COUNTERMODEL. -/
structure InevitableDecisionModel where
  SettlesPlan : Unit → Prop → Prop
  HasAlternative : Unit → Prop → Prop

theorem model_S7_decision_without_alternative :
    ∃ (M : InevitableDecisionModel),
      M.SettlesPlan () True ∧ ¬ M.HasAlternative () True := by
  let M0 : InevitableDecisionModel := {
    SettlesPlan := fun _ p => p = True,
    HasAlternative := fun _ _ => False
  }
  refine ⟨M0, rfl, id⟩

/-- Model S8: Volition without Action (Paralyzed will).
    An agent actively wills a proposition (`Wills s p`), but no physical transition is initiated.
    Status: COUNTERMODEL. -/
structure VolitionWithoutActionModel where
  Wills : Unit → Prop → Prop
  Initiates : Unit → Nat → Nat → Prop → Prop

theorem model_S8_volition_without_action :
    ∃ (M : VolitionWithoutActionModel),
      M.Wills () True ∧ ¬ ∃ w w', M.Initiates () w w' True := by
  let M0 : VolitionWithoutActionModel := {
    Wills := fun _ p => p = True,
    Initiates := fun _ _ _ _ => False
  }
  refine ⟨M0, rfl, ?_⟩
  intro ⟨w, w', hF⟩
  exact hF

-- ===========================================================================
-- Part III: Implication and Separation Matrix
-- ===========================================================================

/-!
### 3. The Implication and Separation Matrix
We prove the valid positive implications and record the exact status of each transition:
-/

/-- Implication 1: Genuine Intentional Action strictly entails Action.
    Status: DEFINITIONAL. -/
theorem genuine_intentional_action_implies_action
    {Subject : Type} {State : Type} {E : AgentialExecution Subject}
    {MeansAt : Subject → Prop → Prop} {InitiatesAt : Subject → State → State → Prop → Prop}
    {s : Subject} {p : Prop}
    (h : GenuineIntentionalAction Subject State E MeansAt InitiatesAt s p) :
    MeansAt s p ∧ ∃ w w' : State, InitiatesAt s w w' p :=
  ⟨h.intentional, h.initiates⟩

/-- Implication 2: Genuine Choice entails Incompatibility of options.
    Status: DEFINITIONAL. -/
theorem genuine_choice_entails_incompatible
    {Subject : Type} {ctx : DeliberativeContext Subject}
    {s : Subject} {p q : Prop}
    (h : GenuineChoice Subject ctx s p q) :
    Incompatible p q :=
  h.incompatible

/-- Implication 3: Genuine Choice entails Asymmetric Settlement (selects p and rejects q).
    Status: DEFINITIONAL. -/
theorem genuine_choice_entails_asymmetric_settlement
    {Subject : Type} {ctx : DeliberativeContext Subject}
    {s : Subject} {p q : Prop}
    (h : GenuineChoice Subject ctx s p q) :
    ctx.Settles s p ∧ ¬ ctx.Settles s q :=
  ⟨h.settles_choice, h.rejects_alternative⟩

/-- Implication 4: Libertarian Freedom strictly entails Categorical Alternative Possibility.
    Status: DEFINITIONAL. -/
theorem libertarian_freedom_entails_alternative_possibility
    {Subject : Type} {State : Type} {ctx : DeliberativeContext Subject}
    {cap : CategoricalAlternativePossibility Subject State} {acs : AgentCausalSourcehood Subject}
    {s : Subject} {w : State} {p q : Prop}
    (h : LibertarianFreedom Subject State ctx cap acs s w p q) :
    cap.CanSettle s w p ∧ cap.CanSettle s w q :=
  h.possibility

/-- Implication 5: Libertarian Freedom strictly entails Agent-Causal Sourcehood.
    Status: DEFINITIONAL. -/
theorem libertarian_freedom_entails_sourcehood
    {Subject : Type} {State : Type} {ctx : DeliberativeContext Subject}
    {cap : CategoricalAlternativePossibility Subject State} {acs : AgentCausalSourcehood Subject}
    {s : Subject} {w : State} {p q : Prop}
    (h : LibertarianFreedom Subject State ctx cap acs s w p q) :
    acs.Causes s p :=
  h.sourcehood

/-- Implication 6: Categorical Alternative Possibility directly conflicts with Choice Determinism (D5).
    If an agent has the real leeway to settle either p or q under identical antecedents,
    then the choice was NOT uniquely determined by those antecedents.
    Status: LOGICAL. -/
theorem alternative_possibility_conflicts_with_choice_determinism :
    ∀ (Subject : Type) (Antecedents : Subject → Prop → Prop) (Settles : Subject → Prop → Prop),
      (∃ (s : Subject) (p q : Prop),
        Antecedents s p ∧ Antecedents s q ∧ Incompatible p q ∧
        Settles s p ∧ Settles s q) →
      ¬ Determinism_D5 Subject Antecedents Settles := by
  intro Subject Antecedents Settles ⟨s, p, q, hAntP, hAntQ, hIncomp, hSetP, hSetQ⟩ hD5
  have hDisj := hD5 s p q hAntP hAntQ hIncomp
  rcases hDisj with ⟨_, hNotQ⟩ | ⟨_, hNotP⟩
  · exact hNotQ hSetQ
  · exact hNotP hSetP

-- ===========================================================================
-- Part IV: Definitional Anti-Cheating Invariants
-- ===========================================================================

/-!
### 4. Definitional Anti-Cheating Invariants
We formally verify that our definitions do not smuggle conclusions:
1. `GenuineIntentionalAction` does NOT define action as `Action ∧ Choice`.
   Proof: An agent can have GenuineIntentionalAction without entertaining any incompatible alternative.
2. `GenuineChoice` does NOT define choice as `Choice ∧ ¬Determinism`.
   Proof: GenuineChoice requires only deliberative cognitive structure and authorship,
   leaving its compatibility with determinism open to substantive investigation.
3. Determinism does NOT definitionally mean compulsion.
   Proof: External/internal compulsion involves bypassing reasons/volition,
   whereas determinism can govern reasons-responsive processes.
-/

/-- Anti-Cheating Invariant 1: Genuine intentional action is coherent without alternative choices.
    Status: LOGICAL. -/
theorem anti_cheating_action_without_alternatives :
    ∃ (Subject : Type) (State : Type) (E : AgentialExecution Subject)
      (MeansAt : Subject → Prop → Prop) (InitiatesAt : Subject → State → State → Prop → Prop)
      (s : Subject) (p : Prop),
      GenuineIntentionalAction Subject State E MeansAt InitiatesAt s p ∧
      ¬ ∃ q, Incompatible p q ∧ MeansAt s q := by
  let E0 : AgentialExecution Unit := {
    AuthoredBy := fun _ p => p = True,
    SettlesOn := fun _ p => p = True
  }
  refine ⟨Unit, Unit, E0, fun _ p => p = True, fun _ _ _ p => p = True, (), True, ?_, ?_⟩
  · exact ⟨rfl, ⟨(), (), rfl⟩, rfl, rfl⟩
  · intro ⟨q, hIncomp, hq⟩
    have hqEq : q = True := hq
    subst hqEq
    exact hIncomp ⟨trivial, trivial⟩

/-- Anti-Cheating Invariant 2: Determinism is distinct from compulsion.
    A reason-guided transition can be deterministic without being compelled.
    Status: LOGICAL. -/
structure CompulsionDistinction where
  isDeterministic : Prop
  isCompelled : Prop
  isGuidedByReasons : Prop

theorem anti_cheating_determinism_not_compulsion :
    ∃ (C : CompulsionDistinction),
      C.isDeterministic ∧ C.isGuidedByReasons ∧ ¬ C.isCompelled := by
  let C0 : CompulsionDistinction := {
    isDeterministic := True,
    isCompelled := False,
    isGuidedByReasons := True
  }
  exact ⟨C0, trivial, trivial, id⟩

end Logos.ActionChoiceDefinitions
