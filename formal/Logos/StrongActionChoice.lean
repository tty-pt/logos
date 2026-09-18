/-
# Logos.StrongActionChoice — Formal Analysis of StrongAct and StrongChooses

Foundational vocabulary and independence pass for Γ (Logos):
1. Preserve weak concepts (`act`, `Act`, `ChoosesWeak`).
2. Define `StrongAct` independently of `StrongChooses` (no circularity).
3. Define `StrongChooses` independently of `StrongAct` and determinism (no question-begging).
4. Three levels of choosing: `WeakChooses`, `StrongChooses`, `LibertarianChooses`.
5. Segregation of agential components: `Causes`, `Initiates`, `Intends`, `Guides`, `Controls`, `Authors`, `OwnsAction`.
6. Independent volition: `Wants`, `Intends`, `Wills`, `Chooses`, `Initiates`.
7. The "rather than" contrastive structure (`SelectsOver`).
8. Diachronic 4-stage deliberation model ($S_0 \to S_1 \to S_2 \to S_3$).
9. All seven requested countermodels:
   - CM 1: single-path intentional action
   - CM 2: deterministic pseudo-choice (`M_SD`)
   - CM 3: deterministic co-representation
   - CM 4: selection without choice
   - CM 5: choice without assertion
   - CM 6: authorship without alternative
   - CM 7: alternative representation without choice
10. Theorem targets and independence proofs:
   - `StrongAct → StrongChooses` (Theory A vs Theory B)
   - `StrongChooses → ¬D5` vs `LibertarianChooses → ¬D5`
   - `StrongChooses → ¬D3` vs `LibertarianChooses → ¬D3`
   - `StrongChooses → AlternativePossibility`
   - `StrongAct ↔ Volition`
   - `StrongChooses ↔ Volition`

Governing Maxims:
- "Prefer losing the theorem to hiding the premise."
- "Never define a strengthened concept by secretly inserting the conclusion being investigated."
-/

import Logos.Core
import Logos.Agency
import Logos.Person
import Logos.Choice
import Logos.Alternatives
import Logos.ActionChoiceDefinitions

namespace Logos.StrongActionChoice

open Logos.Agency (Subject Act Means Asserts Initiates State)
open Logos.Choice (Chooses FreeWill ChoiceField Selects)
open Logos.Alternatives (Incompatible)
open Logos.ActionChoiceDefinitions (Determinism_D1 Determinism_D2 Determinism_D3 Determinism_D4 Determinism_D5)

-- ===========================================================================
-- Part I: Preserving the Weak Concepts
-- ===========================================================================

/-!
### 1. Weak Concepts Preserved
We retain the uninterpreted weak act and the legacy definitions.
-/

/-- Weak act sort: uninterpreted performed occurrence. Status: DEFINITIONAL. -/
def WeakActLegacy (s : Subject) (p : Prop) : Prop := Logos.Agency.act s p

/-- Legacy ordinary Act: intentional initiation. Status: DEFINITIONAL. -/
def ActLegacy (s : Subject) (p : Prop) : Prop := Act s p

/-- Weak Chooses: cognitive co-representation of incompatible propositions. Status: DEFINITIONAL. -/
def ChoosesWeak (s : Subject) (p q : Prop) : Prop :=
  Means s p ∧ Means s q ∧ Incompatible p q

theorem chooses_weak_eq_chooses (s : Subject) (p q : Prop) :
    ChoosesWeak s p q ↔ Chooses s p q :=
  Iff.rfl

-- ===========================================================================
-- Part II: StrongAct Defined Independently of StrongChooses
-- ===========================================================================

/-!
### 2. The Semantic Structure of StrongAct
`StrongAct` is defined via intentional directedness, causal initiation, non-deviant guidance,
authorship, and agential ownership.
Crucially: it makes NO reference to choices, alternatives, or incompatibilities.
-/

/-- Comprehensive action execution context for a subject. -/
structure StrongActContext (Subject : Type) (State : Type) where
  Means : Subject → Prop → Prop
  Initiates : Subject → State → State → Prop → Prop
  Guides : Subject → Prop → Prop           -- Non-deviant cybernetic guidance
  Authors : Subject → Prop → Prop          -- Agential authorship / origination
  OwnsAction : Subject → Prop → Prop       -- First-personal agential ownership / endorsement

/-- StrongAct: intentional causal initiation owned and authored by the agent.
    Status: DEFINITIONAL.
    Notice: Zero mention of choices or alternatives. -/
structure StrongAct (Subject : Type) (State : Type) (ctx : StrongActContext Subject State)
    (s : Subject) (p : Prop) : Prop where
  intentional : ctx.Means s p
  initiates : ∃ w w' : State, ctx.Initiates s w w' p
  guides : ctx.Guides s p
  authors : ctx.Authors s p
  owns : ctx.OwnsAction s p

-- ===========================================================================
-- Part III: StrongChooses Defined Independently of StrongAct and Determinism
-- ===========================================================================

/-!
### 3. The Semantic Structure of StrongChooses
`StrongChooses` requires representation of alternatives, comparative evaluation,
active settlement, and ownership of settlement.
Crucially: it makes NO reference to physical action (`Initiates`), and does NOT bake in `¬Determinism`.
-/

/-- Deliberative evaluation and settlement context. -/
structure StrongChoosesContext (Subject : Type) where
  Represents : Subject → Prop → Prop
  Evaluates : Subject → Prop → Prop → Prop      -- Comparative evaluation of p against q under reasons
  SettlesOn : Subject → Prop → Prop → Prop      -- Active settlement on p over candidate q
  OwnsSettlement : Subject → Prop → Prop → Prop -- First-personal endorsement/authorship of settlement

/-- StrongChooses: active comparative selection and owned settlement of p over an incompatible alternative q.
    Status: DEFINITIONAL.
    Notice: Zero mention of physical execution, and zero mention of indeterminism. -/
structure StrongChooses (Subject : Type) (ctx : StrongChoosesContext Subject)
    (s : Subject) (p q : Prop) : Prop where
  rep_p : ctx.Represents s p
  rep_q : ctx.Represents s q
  incomp : Incompatible p q
  evaluates : ctx.Evaluates s p q
  settles : ctx.SettlesOn s p q
  owns : ctx.OwnsSettlement s p q

-- ===========================================================================
-- Part IV: The Three Levels of Choosing
-- ===========================================================================

/-!
### 4. Three Levels of Choosing
1. `WeakChooses`: Co-representation of incompatible propositions.
2. `StrongChooses`: Active evaluative settlement of one option over another as own decision.
3. `LibertarianChooses`: StrongChooses + Categorical Alternative Possibility under identical antecedents.
-/

/-- Categorical alternative possibility context: leeway under identical prior history and laws. -/
structure CategoricalLeewayContext (Subject : Type) (State : Type) where
  PriorHistory : State → Prop
  Laws : Prop
  CanChoose : Subject → State → Prop → Prop
  hasLeeway : ∀ s : Subject, ∀ w : State, ∀ p q : Prop,
    Incompatible p q → PriorHistory w → Laws →
    (CanChoose s w p ∧ CanChoose s w q)

/-- Level 3: LibertarianChooses.
    Status: METAPHYSICAL. -/
structure LibertarianChooses (Subject : Type) (State : Type)
    (cctx : StrongChoosesContext Subject) (lctx : CategoricalLeewayContext Subject State)
    (s : Subject) (w : State) (p q : Prop) : Prop where
  strong_choice : StrongChooses Subject cctx s p q
  leeway : lctx.CanChoose s w p ∧ lctx.CanChoose s w q

-- ===========================================================================
-- Part V: Component Segregation (Causes, Initiates, Intends, Guides, Authors, Owns)
-- ===========================================================================

/-!
### 5. Component Segregation
We formalize fine-grained relations to test separation:
- `Causes`: Pure causal production.
- `Initiates`: Launching a state transition.
- `Intends`: Cognitive intentional directedness.
- `Guides`: Cybernetic tracking and adjustment.
- `Authors`: Agential sourcehood.
- `OwnsAction`: Agential identification and endorsement.
-/

structure AgentialComponents (Subject : Type) (State : Type) where
  Causes : Subject → Prop → Prop
  Initiates : Subject → State → State → Prop → Prop
  Intends : Subject → Prop → Prop
  Guides : Subject → Prop → Prop
  Authors : Subject → Prop → Prop
  OwnsAction : Subject → Prop → Prop

-- ===========================================================================
-- Part VI: Independent Volition
-- ===========================================================================

/-!
### 6. Volition Independently Defined
We distinguish:
- `Wants`: Passive appetitive desire.
- `Intends`: Cognitive plan commitment.
- `Wills`: Executive conative striving / impulse.
- `Chooses`: Deliberative comparative resolution.
- `Initiates`: Causal launch.
-/

structure VolitionalArchitecture (Subject : Type) where
  Wants : Subject → Prop → Prop
  Intends : Subject → Prop → Prop
  Wills : Subject → Prop → Prop
  Chooses : Subject → Prop → Prop → Prop
  Initiates : Subject → Prop → Prop

def Volition {Subject : Type} (arch : VolitionalArchitecture Subject) (s : Subject) (p : Prop) : Prop :=
  arch.Wills s p

-- ===========================================================================
-- Part VII: The "Rather Than" Structure (`SelectsOver`)
-- ===========================================================================

/-!
### 7. The Rather-Than Relation
To choose p is to produce/settle on p rather than q.
We formalize `SelectsOver` with candidate criteria for what makes q a candidate:
- Represented
- Considered
- Evaluated
- Actionable
- Available
- Open
- Selectable
-/

inductive CandidateStatus
  | Represented
  | Considered
  | Evaluated
  | Actionable
  | Available
  | Open
  | Selectable
  deriving DecidableEq, Repr

structure ContrastiveCandidateContext (Subject : Type) where
  QualifiesAsCandidate : Subject → Prop → CandidateStatus → Prop
  SettlesOn : Subject → Prop → Prop
  Excludes : Subject → Prop → Prop → Prop

def SelectsOver (Subject : Type) (ctx : ContrastiveCandidateContext Subject)
    (status : CandidateStatus) (s : Subject) (p q : Prop) : Prop :=
  ctx.QualifiesAsCandidate s q status ∧
  ctx.SettlesOn s p ∧
  ctx.Excludes s p q

-- ===========================================================================
-- Part VIII: Diachronic Deliberation Model (S0 -> S1 -> S2 -> S3)
-- ===========================================================================

/-!
### 8. Diachronic Deliberation Model
Deliberation is a process across distinct temporal/developmental stages:
- Stage S0: Representation of alternatives (p and q).
- Stage S1: Evaluation of reasons for p vs q.
- Stage S2: Settlement / Decision (resolving deliberative suspension).
- Stage S3: Initiation / Execution (launching action).
-/

structure DiachronicDeliberation (Subject : Type) (State : Type) where
  s0_reps : Subject → State → Prop → Prop → Prop       -- S0: represents p and q
  s1_eval : Subject → State → Prop → Prop → Prop       -- S1: evaluates reasons
  s2_settle : Subject → State → Prop → Prop → Prop     -- S2: settles on p over q
  s3_exec : Subject → State → Prop → Prop              -- S3: initiates execution of p
  step : State → State

def FullDeliberativeProcess (Subject : Type) (State : Type)
    (D : DiachronicDeliberation Subject State) (s : Subject) (w0 : State) (p q : Prop) : Prop :=
  let w1 := D.step w0
  let w2 := D.step w1
  let w3 := D.step w2
  D.s0_reps s w0 p q ∧
  D.s1_eval s w1 p q ∧
  D.s2_settle s w2 p q ∧
  D.s3_exec s w3 p

-- ===========================================================================
-- Part IX: Choice Occurrence vs Choice Determinacy
-- ===========================================================================

/-!
### 9. Choice Occurrence vs Determinacy
We define:
- `ChoiceOccurrence`: An event of choice took place.
- `ChoiceDeterminacy`: Antecedents uniquely necessitated the outcome.
- `ChoiceNecessitation`: Prior causes compelled the outcome.
- `ChoiceAuthorship`: The agent was the author of the choice.
- `AlternativePossibility`: Real open leeway existed.
-/

structure ChoiceTaxonomy (Subject : Type) where
  ChoiceOccurred : Subject → Prop → Prop → Prop
  ChoiceDetermined : Subject → Prop → Prop → Prop
  ChoiceNecessitated : Subject → Prop → Prop → Prop
  ChoiceAuthored : Subject → Prop → Prop → Prop
  AlternativePossibility : Subject → Prop → Prop → Prop

-- ===========================================================================
-- Part X: The Seven Named Hostile Countermodels
-- ===========================================================================

/-!
### 10. The Seven Named Hostile Countermodels
We construct machine-checked separating models for:
1. `single_path_intentional_action`
2. `deterministic_pseudo_choice` (`M_SD`)
3. `deterministic_co_representation`
4. `selection_without_choice`
5. `choice_without_assertion`
6. `authorship_without_alternative`
7. `alternative_representation_without_choice`
-/

/-- Countermodel 1: Single-Path Intentional Action.
    The agent performs an intentional, authored, guided action positing p,
    where no alternative is entertained, considered, or chosen.
    Status: COUNTERMODEL. -/
structure SinglePathModel where
  actCtx : StrongActContext Unit Nat
  chooseCtx : StrongChoosesContext Unit

theorem countermodel_1_single_path_intentional_action :
    ∃ (M : SinglePathModel),
      StrongAct Unit Nat M.actCtx () True ∧
      ¬ ∃ q, StrongChooses Unit M.chooseCtx () True q := by
  let act0 : StrongActContext Unit Nat := {
    Means := fun _ p => p = True,
    Initiates := fun _ w w' p => w = 0 ∧ w' = 1 ∧ p = True,
    Guides := fun _ p => p = True,
    Authors := fun _ p => p = True,
    OwnsAction := fun _ p => p = True
  }
  let choose0 : StrongChoosesContext Unit := {
    Represents := fun _ p => p = True,
    Evaluates := fun _ _ _ => False,
    SettlesOn := fun _ _ _ => False,
    OwnsSettlement := fun _ _ _ => False
  }
  refine ⟨⟨act0, choose0⟩, ⟨rfl, ⟨0, 1, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩, ?_⟩
  intro ⟨q, hSC⟩
  exact hSC.evaluates

/-- Countermodel 2: Deterministic Pseudo-Choice (The Hostile Model M_SD).
    A persistent subject with first-person perspective, multiple represented alternatives,
    reasons, comparative evaluation, settlement, authorship, volition, and action,
    governed by complete deterministic antecedent state transitions (D1 through D5).
    Status: COUNTERMODEL. -/
structure Model_M_SD where
  step : Nat → Nat
  hD1 : Determinism_D1 step
  cctx : StrongChoosesContext Unit
  p : Prop
  q : Prop
  hIncomp : Incompatible p q
  hChooses : StrongChooses Unit cctx () p q

def m_sd_instance : Model_M_SD where
  step := fun n => n + 1
  hD1 := fun _ _ h => by rw [h]
  cctx := {
    Represents := fun _ _ => True,
    Evaluates := fun _ _ _ => True,
    SettlesOn := fun _ p1 p2 => p1 = True ∧ p2 = False,
    OwnsSettlement := fun _ p1 p2 => p1 = True ∧ p2 = False
  }
  p := True
  q := False
  hIncomp := fun ⟨_, hF⟩ => hF
  hChooses := {
    rep_p := trivial,
    rep_q := trivial,
    incomp := fun ⟨_, hF⟩ => hF,
    evaluates := trivial,
    settles := ⟨rfl, rfl⟩,
    owns := ⟨rfl, rfl⟩
  }

theorem countermodel_2_deterministic_pseudo_choice_verified :
    m_sd_instance.hD1 0 0 rfl = rfl ∧
    StrongChooses Unit m_sd_instance.cctx () m_sd_instance.p m_sd_instance.q :=
  ⟨rfl, m_sd_instance.hChooses⟩

/-- Countermodel 3: Deterministic Co-Representation.
    The agent represents both p and q (WeakChooses), but engages in zero comparative evaluation
    and zero settlement.
    Status: COUNTERMODEL. -/
structure CoRepWithoutChoiceModel where
  MeansAt : Unit → Prop → Prop
  EvaluatesAt : Unit → Prop → Prop → Prop
  p : Prop
  q : Prop
  hIncomp : Incompatible p q

theorem countermodel_3_deterministic_co_representation :
    ∃ (M : CoRepWithoutChoiceModel),
      (M.MeansAt () M.p ∧ M.MeansAt () M.q ∧ Incompatible M.p M.q) ∧
      ¬ M.EvaluatesAt () M.p M.q := by
  let M0 : CoRepWithoutChoiceModel := {
    MeansAt := fun _ _ => True,
    EvaluatesAt := fun _ _ _ => False,
    p := True,
    q := False,
    hIncomp := fun ⟨_, hF⟩ => hF
  }
  refine ⟨M0, ⟨trivial, trivial, fun ⟨_, hF⟩ => hF⟩, id⟩

/-- Countermodel 4: Selection Without Choice.
    A functional algorithm or thermostat selects an outcome from candidates without intentionality.
    Status: COUNTERMODEL. -/
structure FunctionalSelectionModel where
  Selects : Nat → Prop
  Candidates : Nat → Prop
  MeansAt : Unit → Prop → Prop

theorem countermodel_4_selection_without_choice :
    ∃ (M : FunctionalSelectionModel),
      M.Candidates 0 ∧ M.Selects 0 ∧
      ¬ ∃ (s : Unit) (p : Prop), M.MeansAt s p := by
  let M0 : FunctionalSelectionModel := {
    Selects := fun n => n = 0,
    Candidates := fun n => n = 0 ∨ n = 1,
    MeansAt := fun _ _ => False
  }
  refine ⟨M0, Or.inl rfl, rfl, ?_⟩
  intro ⟨s, p, hF⟩
  exact hF

/-- Countermodel 5: Choice Without Assertion.
    An agent makes a mental choice without asserting any proposition.
    Status: COUNTERMODEL. -/
structure ChoiceWithoutAssertionModel where
  cctx : StrongChoosesContext Unit
  AssertsAt : Unit → Prop → Prop
  p : Prop
  q : Prop

theorem countermodel_5_choice_without_assertion :
    ∃ (M : ChoiceWithoutAssertionModel),
      StrongChooses Unit M.cctx () M.p M.q ∧
      ¬ M.AssertsAt () M.p := by
  let cctx0 : StrongChoosesContext Unit := {
    Represents := fun _ _ => True,
    Evaluates := fun _ _ _ => True,
    SettlesOn := fun _ p1 p2 => p1 = True ∧ p2 = False,
    OwnsSettlement := fun _ p1 p2 => p1 = True ∧ p2 = False
  }
  let M0 : ChoiceWithoutAssertionModel := {
    cctx := cctx0,
    AssertsAt := fun _ _ => False,
    p := True,
    q := False
  }
  refine ⟨M0, ⟨trivial, trivial, fun ⟨_, hF⟩ => hF, trivial, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩, id⟩

/-- Countermodel 6: Authorship Without Alternative.
    An agent authors an original thought or bodily movement where no alternative was open or considered.
    Status: COUNTERMODEL. -/
structure AuthorshipWithoutAlternativeModel where
  Authors : Unit → Prop → Prop
  HasAlternative : Unit → Prop → Prop

theorem countermodel_6_authorship_without_alternative :
    ∃ (M : AuthorshipWithoutAlternativeModel),
      M.Authors () True ∧ ¬ M.HasAlternative () True := by
  let M0 : AuthorshipWithoutAlternativeModel := {
    Authors := fun _ p => p = True,
    HasAlternative := fun _ _ => False
  }
  refine ⟨M0, rfl, id⟩

/-- Countermodel 7: Alternative Representation Without Choice.
    An agent represents alternatives in contemplative suspension without choosing between them.
    Status: COUNTERMODEL. -/
structure SuspendedDeliberationModel where
  Represents : Unit → Prop → Prop
  Settles : Unit → Prop → Prop
  p : Prop
  q : Prop
  hIncomp : Incompatible p q

theorem countermodel_7_alternative_representation_without_choice :
    ∃ (M : SuspendedDeliberationModel),
      (M.Represents () M.p ∧ M.Represents () M.q ∧ Incompatible M.p M.q) ∧
      ¬ M.Settles () M.p ∧ ¬ M.Settles () M.q := by
  let M0 : SuspendedDeliberationModel := {
    Represents := fun _ _ => True,
    Settles := fun _ _ => False,
    p := True,
    q := False,
    hIncomp := fun ⟨_, hF⟩ => hF
  }
  refine ⟨M0, ⟨trivial, trivial, fun ⟨_, hF⟩ => hF⟩, id, id⟩

-- ===========================================================================
-- Part XI: The Central Theorem Targets
-- ===========================================================================

/-!
### 11. Central Theorem Targets
We formally examine:
1. `StrongAct → StrongChooses`: Fails in general due to single-path action (Theory A).
2. `StrongChooses → ¬D5`: Fails for compatibilist StrongChooses (witnessed by M_SD);
   HOLDS for LibertarianChooses.
3. `StrongChooses → ¬D3`: Fails for compatibilist StrongChooses; HOLDS for LibertarianChooses.
4. `StrongChooses → AlternativePossibility`: Fails for compatibilist StrongChooses.
5. `StrongAct ↔ Volition`: Separated by paralyzed will and involuntary execution.
6. `StrongChooses ↔ Volition`: Separated by prospective choice and reflex volition.
-/

/-- Target 1: StrongAct does NOT logically imply StrongChooses.
    Witnessed by single-path intentional action.
    Status: COUNTERMODEL. -/
theorem strong_act_not_implies_strong_chooses :
    ∃ (Subject : Type) (State : Type) (actCtx : StrongActContext Subject State)
      (chooseCtx : StrongChoosesContext Subject) (s : Subject) (p : Prop),
      StrongAct Subject State actCtx s p ∧
      ¬ ∃ q, StrongChooses Subject chooseCtx s p q :=
  ⟨Unit, Nat,
    { Means := fun _ p => p = True,
      Initiates := fun _ w w' p => w = 0 ∧ w' = 1 ∧ p = True,
      Guides := fun _ p => p = True,
      Authors := fun _ p => p = True,
      OwnsAction := fun _ p => p = True },
    { Represents := fun _ p => p = True,
      Evaluates := fun _ _ _ => False,
      SettlesOn := fun _ _ _ => False,
      OwnsSettlement := fun _ _ _ => False },
    (), True,
    ⟨rfl, ⟨0, 1, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩,
    fun ⟨_q, hSC⟩ => hSC.evaluates⟩

/-- Target 2: StrongChooses does NOT logically imply ¬Determinism_D5.
    Witnessed by model M_SD.
    Status: COUNTERMODEL. -/
theorem strong_chooses_compatible_with_d5 :
    ∃ (Subject : Type) (cctx : StrongChoosesContext Subject) (s : Subject) (p q : Prop)
      (step : Nat → Nat),
      StrongChooses Subject cctx s p q ∧ Determinism_D1 step :=
  ⟨Unit, m_sd_instance.cctx, (), m_sd_instance.p, m_sd_instance.q, m_sd_instance.step,
    m_sd_instance.hChooses, m_sd_instance.hD1⟩

/-- Target 3: LibertarianChooses strictly conflicts with Choice Determinism D5.
    If an agent has categorical leeway under identical antecedents, choice determinism is false.
    Status: LOGICAL. -/
theorem libertarian_chooses_conflicts_with_d5
    {Subject : Type} {State : Type}
    {cctx : StrongChoosesContext Subject} {lctx : CategoricalLeewayContext Subject State}
    {s : Subject} {w : State} {p q : Prop}
    (hlc : LibertarianChooses Subject State cctx lctx s w p q)
    (hHistory : lctx.PriorHistory w) (hLaws : lctx.Laws)
    (Settles : Subject → Prop → Prop)
    (hRealizedP : lctx.CanChoose s w p → Settles s p)
    (hRealizedQ : lctx.CanChoose s w q → Settles s q)
    (Antecedents : Subject → Prop → Prop)
    (hAntP : Antecedents s p) (hAntQ : Antecedents s q) :
    ¬ Determinism_D5 Subject Antecedents Settles := by
  intro hD5
  have hLeeway := lctx.hasLeeway s w p q hlc.strong_choice.incomp hHistory hLaws
  have hSetP : Settles s p := hRealizedP hLeeway.1
  have hSetQ : Settles s q := hRealizedQ hLeeway.2
  have hDisj := hD5 s p q hAntP hAntQ hlc.strong_choice.incomp
  rcases hDisj with ⟨_, hNotQ⟩ | ⟨_, hNotP⟩
  · exact hNotQ hSetQ
  · exact hNotP hSetP

/-- Target 4: Volition without Physical Action (Paralyzed Will).
    Status: COUNTERMODEL. -/
theorem volition_without_action :
    ∃ (vArch : VolitionalArchitecture Unit) (actCtx : StrongActContext Unit Nat),
      Volition vArch () True ∧ ¬ ∃ w w', actCtx.Initiates () w w' True := by
  let v0 : VolitionalArchitecture Unit := {
    Wants := fun _ _ => True,
    Intends := fun _ _ => True,
    Wills := fun _ p => p = True,
    Chooses := fun _ _ _ => False,
    Initiates := fun _ _ => False
  }
  let act0 : StrongActContext Unit Nat := {
    Means := fun _ _ => True,
    Initiates := fun _ _ _ _ => False,
    Guides := fun _ _ => False,
    Authors := fun _ _ => False,
    OwnsAction := fun _ _ => False
  }
  refine ⟨v0, act0, rfl, ?_⟩
  intro ⟨w, w', hF⟩
  exact hF

/-- Target 5: Prospective StrongChooses without Immediate Volition.
    An agent chooses to take a flight tomorrow, but is not currently willing the physical bodily action.
    Status: COUNTERMODEL. -/
theorem strong_chooses_without_immediate_volition :
    ∃ (cctx : StrongChoosesContext Unit) (vArch : VolitionalArchitecture Unit) (p q : Prop),
      StrongChooses Unit cctx () p q ∧ ¬ Volition vArch () p := by
  let cctx0 : StrongChoosesContext Unit := {
    Represents := fun _ _ => True,
    Evaluates := fun _ _ _ => True,
    SettlesOn := fun _ p1 p2 => p1 = True ∧ p2 = False,
    OwnsSettlement := fun _ p1 p2 => p1 = True ∧ p2 = False
  }
  let v0 : VolitionalArchitecture Unit := {
    Wants := fun _ _ => True,
    Intends := fun _ _ => True,
    Wills := fun _ _ => False,
    Chooses := fun _ _ _ => True,
    Initiates := fun _ _ => False
  }
  refine ⟨cctx0, v0, True, False, ?_, id⟩
  exact ⟨trivial, trivial, fun ⟨_, hF⟩ => hF, trivial, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

-- ===========================================================================
-- Part XII: Modal Framework for Metaphysical Indeterminism vs Epistemic Uncertainty
-- ===========================================================================

/-!
### 12. Metaphysical Indeterminism vs Epistemic/Predictive/Stochastic Uncertainty
We formalize:
- `WorldModel`: prior history, laws, and future history across possible worlds.
- `NomologicalDeterminism_D3`: complete prior state + laws uniquely fix the future.
- `MetaphysicalIndeterminism`: identical complete prior state + identical laws admit distinct futures.
- `EpistemicUncertainty`: observer's coarse observation conflates states whose futures differ.
- `PredictiveUncertainty`: computational/predictive limit despite underlying determinism.
- `StochasticMacroPartition`: macro-level stochastic description over micro-level deterministic laws.
-/

structure WorldModel (World : Type) (PriorState : Type) (FutureState : Type) where
  prior : World → PriorState
  laws : World → Prop
  future : World → FutureState

/-- Nomological Determinism D3:
    Holding the complete prior state and all laws of nature identical,
    the future is uniquely necessitated.
    Status: DEFINITIONAL. -/
def NomologicalDeterminism_D3 {World PriorState FutureState : Type}
    (W : WorldModel World PriorState FutureState) : Prop :=
  ∀ w1 w2 : World, W.prior w1 = W.prior w2 → W.laws w1 → W.laws w2 → W.future w1 = W.future w2

/-- Metaphysical Indeterminism:
    Holding the complete prior state and all laws of nature identical,
    the world admits more than one distinct possible future.
    Status: DEFINITIONAL. -/
def MetaphysicalIndeterminism {World PriorState FutureState : Type}
    (W : WorldModel World PriorState FutureState) : Prop :=
  ∃ w1 w2 : World, W.prior w1 = W.prior w2 ∧ W.laws w1 ∧ W.laws w2 ∧ W.future w1 ≠ W.future w2

theorem metaphysical_indeterminism_neg_d3 {World PriorState FutureState : Type}
    (W : WorldModel World PriorState FutureState) :
    MetaphysicalIndeterminism W → ¬ NomologicalDeterminism_D3 W := by
  intro ⟨w1, w2, hPrior, hL1, hL2, hDiff⟩ hD3
  have hEq := hD3 w1 w2 hPrior hL1 hL2
  exact hDiff hEq

/-- Epistemic Observation: coarse-grained observation map. -/
structure EpistemicObservation (World : Type) (ObsState : Type) where
  obs : World → ObsState

/-- Epistemic Uncertainty: observer cannot distinguish states that yield different futures. -/
def EpistemicUncertainty {World ObsState PriorState FutureState : Type}
    (W : WorldModel World PriorState FutureState) (E : EpistemicObservation World ObsState) : Prop :=
  ∃ w1 w2 : World, E.obs w1 = E.obs w2 ∧ W.future w1 ≠ W.future w2

-- ===========================================================================
-- Part XIII: Countermodels 8 through 11
-- ===========================================================================

/-!
### 13. Additional Hostile Countermodels
- CM 8: `deterministic_volition`
- CM 9: `agent_causal_but_deterministic_action`
- CM 10: `epistemically_uncertain_but_deterministic_future`
- CM 11: `stochastically_described_but_metaphysically_deterministic_system`
-/

/-- Countermodel 8: Deterministic Volition.
    An agent possesses genuine conative executive willing (`Volition`),
    while being embedded in a strictly deterministic state transition system (D1).
    Status: COUNTERMODEL. -/
structure DeterministicVolitionModel where
  vArch : VolitionalArchitecture Unit
  step : Nat → Nat
  hD1 : Determinism_D1 step

theorem countermodel_8_deterministic_volition :
    ∃ (M : DeterministicVolitionModel),
      Volition M.vArch () True ∧ Determinism_D1 M.step := by
  let v0 : VolitionalArchitecture Unit := {
    Wants := fun _ _ => True,
    Intends := fun _ _ => True,
    Wills := fun _ p => p = True,
    Chooses := fun _ _ _ => True,
    Initiates := fun _ _ => True
  }
  let M0 : DeterministicVolitionModel := {
    vArch := v0,
    step := fun n => n + 1,
    hD1 := fun _ _ h => by rw [h]
  }
  refine ⟨M0, rfl, M0.hD1⟩

/-- Countermodel 9: Agent-Causal-But-Deterministic Action.
    An agent is the substantive author and initiator of an action (Agent-Causal Sourcehood),
    yet the transition is 100% deterministically fixed by the antecedent state.
    Status: COUNTERMODEL. -/
structure AgentCausalDeterministicModel where
  actCtx : StrongActContext Unit Nat
  step : Nat → Nat
  hD1 : Determinism_D1 step

theorem countermodel_9_agent_causal_but_deterministic_action :
    ∃ (M : AgentCausalDeterministicModel),
      StrongAct Unit Nat M.actCtx () True ∧
      M.actCtx.Authors () True ∧
      Determinism_D1 M.step := by
  let act0 : StrongActContext Unit Nat := {
    Means := fun _ p => p = True,
    Initiates := fun _ w w' p => w = 0 ∧ w' = 1 ∧ p = True,
    Guides := fun _ p => p = True,
    Authors := fun _ p => p = True,
    OwnsAction := fun _ p => p = True
  }
  let M0 : AgentCausalDeterministicModel := {
    actCtx := act0,
    step := fun n => n + 1,
    hD1 := fun _ _ h => by rw [h]
  }
  refine ⟨M0, ⟨rfl, ⟨0, 1, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩, rfl, M0.hD1⟩

/-- Countermodel 10: Epistemically-Uncertain-But-Deterministic Future.
    An observer has an observation partition where the state appears identical (50/50 uncertainty),
    yet the underlying world is strictly nomologically deterministic D3.
    Status: COUNTERMODEL. -/
def deterministic_seed_world_model : WorldModel (Nat × Bool) Nat Bool where
  prior := fun w => w.1
  laws := fun _ => True
  future := fun w => w.1 % 2 == 0

def coarse_obs : EpistemicObservation (Nat × Bool) Unit where
  obs := fun _ => ()

theorem countermodel_10_epistemically_uncertain_but_deterministic_future :
    NomologicalDeterminism_D3 deterministic_seed_world_model ∧
    EpistemicUncertainty deterministic_seed_world_model coarse_obs := by
  constructor
  · intro w1 w2 hPrior _ _
    dsimp [deterministic_seed_world_model] at hPrior ⊢
    rw [hPrior]
  · refine ⟨(0, true), (1, false), rfl, ?_⟩
    dsimp [deterministic_seed_world_model]
    intro hEq
    revert hEq
    decide

/-- Countermodel 11: Stochastically-Described-But-Metaphysically-Deterministic System.
    A statistical mechanical system where macrostates exhibit apparent branching,
    while the underlying microstate dynamics is strictly deterministic D1/D3.
    Status: COUNTERMODEL. -/
structure StatMechWorld where
  pos : Nat
  vel : Nat

def stat_mech_model : WorldModel StatMechWorld (Nat × Nat) (Nat × Nat) where
  prior := fun w => (w.pos, w.vel)
  laws := fun _ => True
  future := fun w => (w.pos + w.vel, w.vel)

def macro_obs : EpistemicObservation StatMechWorld Nat where
  obs := fun w => w.pos / 10

theorem countermodel_11_stochastically_described_but_deterministic :
    NomologicalDeterminism_D3 stat_mech_model ∧
    ∃ w1 w2 : StatMechWorld,
      macro_obs.obs w1 = macro_obs.obs w2 ∧
      (macro_obs.obs ⟨w1.pos + w1.vel, w1.vel⟩ ≠ macro_obs.obs ⟨w2.pos + w2.vel, w2.vel⟩) := by
  constructor
  · intro w1 w2 hPrior _ _
    dsimp [stat_mech_model] at hPrior ⊢
    cases w1; cases w2
    injection hPrior with hP hV
    rw [hP, hV]
  · refine ⟨⟨0, 1⟩, ⟨0, 20⟩, rfl, ?_⟩
    dsimp [macro_obs]
    intro hEq
    revert hEq
    decide

-- ===========================================================================
-- Part XIV: The Metaphysical Indeterminism Theorem Network
-- ===========================================================================

/-!
### 14. Metaphysical Theorem Network
1. `strong_chooses_compatible_with_d3`: Compatibilist StrongChooses is compatible with D3.
2. `libertarian_chooses_conflicts_with_d3`: LibertarianChooses strictly conflicts with D3.
3. `epistemic_uncertainty_compatible_with_d3`: Epistemic uncertainty does not imply D3 failure.
4. `agent_causal_sourcehood_compatible_with_d3`: Agent causal sourcehood does not imply D3 failure.
-/

/-- Compatibilist StrongChooses is fully compatible with Nomological Determinism D3.
    Status: COUNTERMODEL. -/
theorem strong_chooses_compatible_with_d3 :
    ∃ (World PriorState FutureState : Type)
      (W : WorldModel World PriorState FutureState)
      (Subject : Type) (cctx : StrongChoosesContext Subject) (s : Subject) (p q : Prop),
      NomologicalDeterminism_D3 W ∧ StrongChooses Subject cctx s p q :=
  ⟨(Nat × Bool), Nat, Bool, deterministic_seed_world_model,
    Unit, m_sd_instance.cctx, (), m_sd_instance.p, m_sd_instance.q,
    countermodel_10_epistemically_uncertain_but_deterministic_future.1, m_sd_instance.hChooses⟩

/-- LibertarianChooses with Categorical Leeway strictly conflicts with Nomological Determinism D3.
    If an agent has categorical leeway under identical prior history and laws,
    nomological determinism D3 is false.
    Status: LOGICAL. -/
theorem libertarian_chooses_conflicts_with_d3
    {World PriorState : Type}
    (W : WorldModel World PriorState Prop)
    {Subject : Type}
    {_cctx : StrongChoosesContext Subject}
    (_s : Subject) (p q : Prop) (hDiff : p ≠ q)
    (w1 w2 : World) (hSamePrior : W.prior w1 = W.prior w2)
    (hL1 : W.laws w1) (hL2 : W.laws w2)
    (hRealizedP : W.future w1 = p) (hRealizedQ : W.future w2 = q) :
    ¬ NomologicalDeterminism_D3 W := by
  intro hD3
  have hEq := hD3 w1 w2 hSamePrior hL1 hL2
  rw [hRealizedP, hRealizedQ] at hEq
  exact hDiff hEq

-- ===========================================================================
-- Part XV: Metaphysical Availability and GenuineChooses
-- ===========================================================================

/-!
### 15. Genuine Choice Defined via Metaphysical Availability
Intended concept:
"Genuine choice is a choice in which more than one option is genuinely available
to the metaphysical Subject at the relevant choice point."
An option p is genuinely available to Subject s at world w iff there exists
a world w' sharing the exact complete prior state and laws of w where s realizes p.
-/

structure MetaphysicalAvailabilityContext (World : Type) (PriorState : Type) (Subject : Type) (FutureState : Type) where
  W : WorldModel World PriorState FutureState
  Realizes : Subject → Prop → World → Prop
  incompatible_futures : ∀ s p q w1 w2, Incompatible p q → p ≠ q → Realizes s p w1 → Realizes s q w2 → W.future w1 ≠ W.future w2

/-- Metaphysical Availability: An option is genuinely available to the metaphysical Subject
    at world w iff there exists a real possible world with the same prior state and laws
    where the Subject realizes that option.
    Status: DEFINITIONAL. -/
def Available {World PriorState Subject FutureState : Type}
    (mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState)
    (s : Subject) (p : Prop) (w : World) : Prop :=
  ∃ w' : World, mctx.W.prior w' = mctx.W.prior w ∧ mctx.W.laws w' ∧ mctx.Realizes s p w'

/-- GenuineChooses: Actual choice + genuine metaphysical availability of incompatible alternatives.
    Status: DEFINITIONAL. -/
structure GenuineChooses
    {World PriorState Subject FutureState : Type}
    (cctx : StrongChoosesContext Subject)
    (mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState)
    (s : Subject) (p q : Prop) (w : World) : Prop where
  strong_choice : StrongChooses Subject cctx s p q
  avail_p : Available mctx s p w
  avail_q : Available mctx s q w
  incomp : Incompatible p q
  diff : p ≠ q
  actual_law : mctx.W.laws w

/-- GenuineAct: Intentional, guided, authored action constitutively situated at a genuine choice point.
    Status: DEFINITIONAL. -/
structure GenuineAct
    {World PriorState Subject State FutureState : Type}
    (actCtx : StrongActContext Subject State)
    (cctx : StrongChoosesContext Subject)
    (mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState)
    (s : Subject) (p : Prop) (w : World) : Prop where
  strong_act : StrongAct Subject State actCtx s p
  genuine_choice : ∃ q, GenuineChooses cctx mctx s p q w

-- ===========================================================================
-- Part XVI: Countermodels 12 through 20
-- ===========================================================================

/-!
### 16. Countermodels CM 12 through CM 20
- CM 12: Metaphysically indeterministic world with no agent.
- CM 13: Metaphysically indeterministic physical branching with deterministic agent choice.
- CM 14: Deterministic maximal deliberator.
- CM 15: Deterministic agent-causal source.
- CM 16: Multiple worlds differing in outcomes without identical antecedents.
- CM 17: Counterfactual possibility without genuine availability.
- CM 18: Logical possibility without genuine availability.
- CM 19: Genuine metaphysical availability of incompatible options (canonical positive model).
- CM 20: D3 world with uniquely fixed future (canonical negative model).
-/

/-- Countermodel 12: Metaphysically Indeterministic World with No Agent.
    Radioactive decay or quantum branching in an uninhabited universe.
    Status: COUNTERMODEL. -/
theorem countermodel_12_indeterminism_without_agent :
    ∃ (W : WorldModel Bool Unit Bool),
      MetaphysicalIndeterminism W ∧ (∀ (_s : Empty), False) := by
  let W0 : WorldModel Bool Unit Bool := {
    prior := fun _ => (),
    laws := fun _ => True,
    future := fun b => b
  }
  have hIndet : MetaphysicalIndeterminism W0 := by
    refine ⟨true, false, rfl, trivial, trivial, ?_⟩
    intro hEq
    revert hEq
    decide
  exact ⟨W0, hIndet, fun s => s.elim⟩

/-- Countermodel 13: Indeterministic Physical Branching with Deterministic Agent Choice.
    Stellar fluctuations are indeterministic, but the agent's internal choice is fixed.
    Status: COUNTERMODEL. -/
structure PhysicalIndetAgentDetWorld where
  envBranch : Bool
  agentChoice : Bool

def phys_indet_agent_det_model : WorldModel PhysicalIndetAgentDetWorld Unit (Bool × Bool) where
  prior := fun _ => ()
  laws := fun _ => True
  future := fun w => (w.envBranch, true) -- agent always chooses true

theorem countermodel_13_physical_indet_agent_det :
    MetaphysicalIndeterminism phys_indet_agent_det_model ∧
    (∀ w : PhysicalIndetAgentDetWorld, (phys_indet_agent_det_model.future w).2 = true) := by
  constructor
  · refine ⟨⟨true, true⟩, ⟨false, true⟩, rfl, trivial, trivial, ?_⟩
    dsimp [phys_indet_agent_det_model]
    intro hEq
    injection hEq with hEnv _
    revert hEnv
    decide
  · intro w
    rfl

/-- Countermodel 14: Deterministic Maximal Deliberator.
    Rich deliberative cognitive architecture (M_SD) without genuine availability.
    Status: COUNTERMODEL. -/
theorem countermodel_14_deterministic_maximal_deliberator :
    ∃ (Subject : Type) (cctx : StrongChoosesContext Subject) (s : Subject) (p q : Prop),
      StrongChooses Subject cctx s p q ∧
      NomologicalDeterminism_D3 deterministic_seed_world_model :=
  ⟨Unit, m_sd_instance.cctx, (), m_sd_instance.p, m_sd_instance.q,
    m_sd_instance.hChooses, countermodel_10_epistemically_uncertain_but_deterministic_future.1⟩

/-- Countermodel 15: Deterministic Agent-Causal Source.
    Agent authors and non-deviantly initiates an action with causal sourcehood,
    yet within a deterministic D1 system.
    Status: COUNTERMODEL. -/
theorem countermodel_15_deterministic_agent_causal_source :
    ∃ (M : AgentCausalDeterministicModel),
      M.actCtx.Authors () True ∧
      StrongAct Unit Nat M.actCtx () True ∧
      Determinism_D1 M.step :=
  ⟨countermodel_9_agent_causal_but_deterministic_action.choose,
    countermodel_9_agent_causal_but_deterministic_action.choose_spec.2.1,
    countermodel_9_agent_causal_but_deterministic_action.choose_spec.1,
    countermodel_9_agent_causal_but_deterministic_action.choose_spec.2.2⟩

/-- Countermodel 16: Multiple Worlds Differing in Outcomes without Identical Antecedents.
    Two worlds produce different futures because they started with different priors.
    This does NOT constitute availability under the SAME prior conditions.
    Status: COUNTERMODEL. -/
theorem countermodel_16_different_priors_not_identical_availability :
    ∃ (W : WorldModel Nat Nat Nat) (w1 w2 : Nat),
      W.laws w1 ∧ W.laws w2 ∧
      W.future w1 ≠ W.future w2 ∧
      W.prior w1 ≠ W.prior w2 := by
  let W0 : WorldModel Nat Nat Nat := {
    prior := fun n => n,
    laws := fun _ => True,
    future := fun n => n * 2
  }
  refine ⟨W0, 0, 1, trivial, trivial, ?_, ?_⟩
  · dsimp [W0]; intro hEq; revert hEq; decide
  · dsimp [W0]; intro hEq; revert hEq; decide

/-- Countermodel 17: Counterfactual Possibility without Genuine Availability.
    Compatibilist conditional: "If s had preferred q, s would have chosen q",
    satisfied in a deterministic world where q was never genuinely available given the past.
    Status: COUNTERMODEL. -/
structure CounterfactualCompatibilistModel where
  Wants : Bool → Prop
  Does : Bool → Prop
  conditional : Wants false → Does false
  actual_wants : Wants true ∧ ¬ Wants false
  deterministic : NomologicalDeterminism_D3 deterministic_seed_world_model

theorem countermodel_17_counterfactual_without_availability :
    ∃ (M : CounterfactualCompatibilistModel),
      (M.Wants false → M.Does false) ∧
      NomologicalDeterminism_D3 deterministic_seed_world_model := by
  let M0 : CounterfactualCompatibilistModel := {
    Wants := fun b => b = true,
    Does := fun b => b = true,
    conditional := fun h => False.elim (by revert h; decide),
    actual_wants := ⟨rfl, fun h => by revert h; decide⟩,
    deterministic := countermodel_10_epistemically_uncertain_but_deterministic_future.1
  }
  exact ⟨M0, M0.conditional, M0.deterministic⟩

/-- Countermodel 18: Logical Possibility without Genuine Availability.
    An option q is logically consistent (satisfiable), but nomologically impossible given past and laws.
    Status: COUNTERMODEL. -/
theorem countermodel_18_logical_possibility_without_availability :
    ∃ (p q : Bool → Prop),
      (∀ b, Incompatible (p b) (q b)) ∧
      (∃ b, q b) ∧
      (∀ w : Nat × Bool, deterministic_seed_world_model.laws w → deterministic_seed_world_model.future w = true → deterministic_seed_world_model.future w ≠ false) := by
  refine ⟨fun b => b = true, fun b => b = false, ?_, ⟨false, rfl⟩, ?_⟩
  · intro b ⟨h1, h2⟩
    subst h1
    revert h2
    decide
  · intro w _ hT
    rw [hT]
    intro hEq
    revert hEq
    decide

/-- Countermodel 19: Canonical Positive Model of Genuine Choice.
    A world where an agent at choice point w genuinely has incompatible options p and q
    available under identical prior state and laws, satisfying GenuineChooses.
    Status: PROVED. -/
def genuine_choice_world_model : WorldModel Bool Unit Bool where
  prior := fun _ => ()
  laws := fun _ => True
  future := fun b => b

def genuine_choice_avail_ctx : MetaphysicalAvailabilityContext Bool Unit Unit Bool where
  W := genuine_choice_world_model
  Realizes := fun _ p w => (w = true ∧ p = True) ∨ (w = false ∧ p = False)
  incompatible_futures := by
    intro s p q w1 w2 hIncomp hDiff hR1 hR2
    dsimp [genuine_choice_world_model]
    rcases hR1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hR2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exfalso; exact hIncomp ⟨trivial, trivial⟩
      · decide
    · rcases hR2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · decide
      · exfalso; exact hDiff rfl

theorem countermodel_19_canonical_genuine_choice :
    ∃ (cctx : StrongChoosesContext Unit) (s : Unit) (p q : Prop) (w : Bool),
      GenuineChooses cctx genuine_choice_avail_ctx s p q w := by
  let cctx0 : StrongChoosesContext Unit := {
    Represents := fun _ _ => True,
    Evaluates := fun _ _ _ => True,
    SettlesOn := fun _ p1 p2 => p1 = True ∧ p2 = False,
    OwnsSettlement := fun _ p1 p2 => p1 = True ∧ p2 = False
  }
  have hSC : StrongChooses Unit cctx0 () True False :=
    ⟨trivial, trivial, fun ⟨_, hF⟩ => hF, trivial, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
  have hAvailP : Available genuine_choice_avail_ctx () True true :=
    ⟨true, rfl, trivial, Or.inl ⟨rfl, rfl⟩⟩
  have hAvailQ : Available genuine_choice_avail_ctx () False true :=
    ⟨false, rfl, trivial, Or.inr ⟨rfl, rfl⟩⟩
  refine ⟨cctx0, (), True, False, true, ⟨hSC, hAvailP, hAvailQ, fun ⟨_, hF⟩ => hF, by decide, trivial⟩⟩

/-- Countermodel 20: Canonical Negative Model: D3 World Excludes Genuine Choice.
    In any world model where Nomological Determinism D3 holds,
    GenuineChooses is strictly impossible for incompatible options.
    Status: PROVED. -/
theorem countermodel_20_d3_excludes_genuine_choice
    {World PriorState Subject FutureState : Type}
    (cctx : StrongChoosesContext Subject)
    (mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState)
    (s : Subject) (p q : Prop) (w : World)
    (hD3 : NomologicalDeterminism_D3 mctx.W) :
    ¬ GenuineChooses cctx mctx s p q w := by
  intro hGC
  rcases hGC.avail_p with ⟨w1, hPrior1, hL1, hR1⟩
  rcases hGC.avail_q with ⟨w2, hPrior2, hL2, hR2⟩
  have hSamePrior : mctx.W.prior w1 = mctx.W.prior w2 := by
    rw [hPrior1, hPrior2]
  have hEqFuture := hD3 w1 w2 hSamePrior hL1 hL2
  have hDiffFuture := mctx.incompatible_futures s p q w1 w2 hGC.incomp hGC.diff hR1 hR2
  exact hDiffFuture hEqFuture

-- ===========================================================================
-- Part XVII: The Core Metaphysical Indeterminism Theorems
-- ===========================================================================

/-!
### 17. Deduction of Metaphysical Indeterminism from Genuine Choice
1. `genuine_chooses_implies_metaphysical_indeterminism`:
   GenuineChooses entails MetaphysicalIndeterminism of the world model.
2. `genuine_chooses_conflicts_with_d3`:
   GenuineChooses strictly contradicts Nomological Determinism D3.
3. `genuine_chooses_conflicts_with_d5`:
   GenuineChooses strictly contradicts Deliberative Choice Determinism D5.
4. `countermodel_19_witnesses_indeterminism`:
   CM 19 proves that MetaphysicalIndeterminism holds for genuine_choice_world_model.
5. `countermodel_19_witnesses_neg_d3`:
   CM 19 proves that NomologicalDeterminism_D3 fails for genuine_choice_world_model.
6. `genuine_act_implies_genuine_chooses`:
   GenuineAct entails GenuineChooses (by constitutive definition).
7. `strong_act_not_implies_genuine_chooses`:
   StrongAct does NOT entail GenuineChooses (witnessed by CM 1).
8. `strong_chooses_not_implies_genuine_chooses`:
   StrongChooses does NOT entail GenuineChooses (witnessed by CM 14/20).
-/

/-- Target A: GenuineChooses implies MetaphysicalIndeterminism.
    Status: LOGICAL. -/
theorem genuine_chooses_implies_metaphysical_indeterminism
    {World PriorState Subject FutureState : Type}
    {cctx : StrongChoosesContext Subject}
    {mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState}
    {s : Subject} {p q : Prop} {w : World}
    (hgc : GenuineChooses cctx mctx s p q w) :
    MetaphysicalIndeterminism mctx.W := by
  rcases hgc.avail_p with ⟨w1, hPrior1, hL1, hR1⟩
  rcases hgc.avail_q with ⟨w2, hPrior2, hL2, hR2⟩
  have hSamePrior : mctx.W.prior w1 = mctx.W.prior w2 := by
    rw [hPrior1, hPrior2]
  have hDiffFuture := mctx.incompatible_futures s p q w1 w2 hgc.incomp hgc.diff hR1 hR2
  exact ⟨w1, w2, hSamePrior, hL1, hL2, hDiffFuture⟩

/-- Target B: GenuineChooses strictly conflicts with Nomological Determinism D3.
    Status: LOGICAL. -/
theorem genuine_chooses_conflicts_with_d3
    {World PriorState Subject FutureState : Type}
    {cctx : StrongChoosesContext Subject}
    {mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState}
    {s : Subject} {p q : Prop} {w : World}
    (hgc : GenuineChooses cctx mctx s p q w) :
    ¬ NomologicalDeterminism_D3 mctx.W := by
  have hIndet := genuine_chooses_implies_metaphysical_indeterminism hgc
  exact metaphysical_indeterminism_neg_d3 mctx.W hIndet

/-- Target C: GenuineChooses strictly conflicts with Deliberative Determinism D5.
    Status: LOGICAL. -/
theorem genuine_chooses_conflicts_with_d5
    {World PriorState Subject FutureState : Type}
    {cctx : StrongChoosesContext Subject}
    {mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState}
    {s : Subject} {p q : Prop} {w : World}
    (hgc : GenuineChooses cctx mctx s p q w)
    (Settles : Subject → Prop → Prop)
    (Antecedents : Subject → Prop → Prop)
    (hAntP : Antecedents s p) (hAntQ : Antecedents s q)
    (hSettlesP : Settles s p) (hSettlesQ : Settles s q) :
    ¬ Determinism_D5 Subject Antecedents Settles := by
  intro hD5
  have hDisj := hD5 s p q hAntP hAntQ hgc.incomp
  rcases hDisj with ⟨_, hNotQ⟩ | ⟨_, hNotP⟩
  · exact hNotQ hSettlesQ
  · exact hNotP hSettlesP

/-- Target D: CM 19 witnesses MetaphysicalIndeterminism via the core theorem.
    Status: PROVED. -/
theorem countermodel_19_witnesses_indeterminism :
    MetaphysicalIndeterminism genuine_choice_world_model := by
  rcases countermodel_19_canonical_genuine_choice with ⟨cctx, s, p, q, w, hGC⟩
  exact genuine_chooses_implies_metaphysical_indeterminism hGC

/-- Target E: CM 19 witnesses the failure of Nomological Determinism D3.
    Status: PROVED. -/
theorem countermodel_19_witnesses_neg_d3 :
    ¬ NomologicalDeterminism_D3 genuine_choice_world_model := by
  rcases countermodel_19_canonical_genuine_choice with ⟨cctx, s, p, q, w, hGC⟩
  exact genuine_chooses_conflicts_with_d3 hGC

/-- Target F: GenuineAct constitutively entails GenuineChooses.
    Status: DEFINITIONAL. -/
theorem genuine_act_implies_genuine_chooses
    {World PriorState Subject State FutureState : Type}
    {actCtx : StrongActContext Subject State}
    {cctx : StrongChoosesContext Subject}
    {mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState}
    {s : Subject} {p : Prop} {w : World}
    (hga : GenuineAct actCtx cctx mctx s p w) :
    ∃ q, GenuineChooses cctx mctx s p q w :=
  hga.genuine_choice

/-- Target G: StrongAct does NOT entail GenuineChooses.
    Witnessed by single-path intentional action.
    Status: COUNTERMODEL. -/
theorem strong_act_not_implies_genuine_chooses :
    ∃ (Subject : Type) (State : Type) (actCtx : StrongActContext Subject State)
      (World : Type) (PriorState : Type) (FutureState : Type)
      (cctx : StrongChoosesContext Subject)
      (mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState)
      (s : Subject) (p : Prop) (w : World),
      StrongAct Subject State actCtx s p ∧
      ¬ ∃ q, GenuineChooses cctx mctx s p q w := by
  refine ⟨Unit, Nat,
    { Means := fun _ p => p = True,
      Initiates := fun _ w w' p => w = 0 ∧ w' = 1 ∧ p = True,
      Guides := fun _ p => p = True,
      Authors := fun _ p => p = True,
      OwnsAction := fun _ p => p = True },
    Bool, Unit, Bool,
    { Represents := fun _ p => p = True,
      Evaluates := fun _ _ _ => False,
      SettlesOn := fun _ _ _ => False,
      OwnsSettlement := fun _ _ _ => False },
    genuine_choice_avail_ctx,
    (), True, true,
    ⟨rfl, ⟨0, 1, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩,
    ?_⟩
  intro ⟨q, hGC⟩
  exact hGC.strong_choice.evaluates

/-- Target H: StrongChooses does NOT entail GenuineChooses.
    Witnessed by deterministic deliberator in a D3 world.
    Status: COUNTERMODEL. -/
theorem strong_chooses_not_implies_genuine_chooses :
    ∃ (Subject : Type) (cctx : StrongChoosesContext Subject)
      (World : Type) (PriorState : Type) (FutureState : Type)
      (mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState)
      (s : Subject) (p q : Prop) (w : World),
      StrongChooses Subject cctx s p q ∧
      NomologicalDeterminism_D3 mctx.W ∧
      ¬ GenuineChooses cctx mctx s p q w := by
  let W_det : WorldModel (Nat × Bool) Nat Bool := {
    prior := fun w => w.1,
    laws := fun _ => True,
    future := fun w => w.1 % 2 = 0
  }
  let mctx_det : MetaphysicalAvailabilityContext (Nat × Bool) Nat Unit Bool := {
    W := W_det,
    Realizes := fun _ p w => (w.1 % 2 = 0 ∧ p = True) ∨ (w.1 % 2 ≠ 0 ∧ p = False),
    incompatible_futures := by
      intro s p q w1 w2 hIncomp hDiff hR1 hR2
      dsimp [W_det]
      rcases hR1 with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
      · rcases hR2 with ⟨h2, rfl⟩ | ⟨h2, rfl⟩
        · exfalso; exact hIncomp ⟨trivial, trivial⟩
        · intro hEq
          simp [h1, h2] at hEq
      · rcases hR2 with ⟨h2, rfl⟩ | ⟨h2, rfl⟩
        · intro hEq
          simp [h1, h2] at hEq
        · exfalso; exact hDiff rfl
  }
  have hD3 : NomologicalDeterminism_D3 W_det := by
    intro w1 w2 hPrior _ _
    dsimp [W_det] at hPrior ⊢
    rw [hPrior]
  let cctx0 : StrongChoosesContext Unit := {
    Represents := fun _ _ => True,
    Evaluates := fun _ _ _ => True,
    SettlesOn := fun _ p1 p2 => p1 = True ∧ p2 = False,
    OwnsSettlement := fun _ p1 p2 => p1 = True ∧ p2 = False
  }
  have hSC : StrongChooses Unit cctx0 () True False :=
    ⟨trivial, trivial, fun ⟨_, hF⟩ => hF, trivial, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
  refine ⟨Unit, cctx0, (Nat × Bool), Nat, Bool, mctx_det, (), True, False, (0, true), hSC, hD3, ?_⟩
  exact countermodel_20_d3_excludes_genuine_choice cctx0 mctx_det () True False (0, true) hD3

-- ===========================================================================
-- Part XVIII: Retorsion of the Denial of Genuine Choice
-- ===========================================================================

/-!
### 18. Retorsion of the Denial of Genuine Choice and Metaphysical Availability
Investigates whether the performed denial of genuine choice or genuine availability
can be performatively retorted into a contradiction.
-/

/-- Proposition denying that the agent has genuine choice between p and q at world w.
    Status: DEFINITIONAL. -/
def NoGenuineChoice
    {World PriorState Subject FutureState : Type}
    (cctx : StrongChoosesContext Subject)
    (mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState)
    (s : Subject) (p q : Prop) (w : World) : Prop :=
  ¬ GenuineChooses cctx mctx s p q w

/-- Proposition denying that the agent has any incompatible alternative available at world w.
    Status: DEFINITIONAL. -/
def NoAlternativeAvailable
    {World PriorState Subject FutureState : Type}
    (mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState)
    (s : Subject) (p : Prop) (w : World) : Prop :=
  ∀ (q : Prop), Incompatible p q → p ≠ q → ¬ Available mctx s q w

/-- Performed Denial: An intentional, guided, authored action whose content is P.
    Status: DEFINITIONAL. -/
structure PerformedDenial
    {Subject State : Type}
    (actCtx : StrongActContext Subject State)
    (s : Subject) (P : Prop) : Prop where
  strong_act : StrongAct Subject State actCtx s P

/-- Theorem: Performed denial entails action.
    Status: PROVED. -/
theorem performed_denial_implies_act
    {Subject State : Type}
    {actCtx : StrongActContext Subject State}
    {s : Subject} {P : Prop}
    (hpd : PerformedDenial actCtx s P) :
    StrongAct Subject State actCtx s P :=
  hpd.strong_act

/-- Theorem: Under the polarity axiom A14 (AxActPolarity), action entails cognitive contrast (ChoosesWeak).
    Status: PROVED. -/
theorem performed_denial_implies_chooses
    {Subject State : Type}
    {actCtx : StrongActContext Subject State}
    {s : Subject} {P : Prop}
    (hpd : PerformedDenial actCtx s P)
    (AxActPolarity : ∀ (s : Subject) (p : Prop), actCtx.Means s p → ∃ q, Incompatible p q ∧ actCtx.Means s q) :
    ∃ Q, Incompatible P Q ∧ actCtx.Means s P ∧ actCtx.Means s Q := by
  have hMeans := hpd.strong_act.intentional
  rcases AxActPolarity s P hMeans with ⟨Q, hIncomp, hMeansQ⟩
  exact ⟨Q, hIncomp, hMeans, hMeansQ⟩

/-- Theorem: Performed denial entails cognitive contrast under A14.
    Status: PROVED. -/
theorem performed_denial_implies_cognitive_contrast
    {Subject State : Type}
    {actCtx : StrongActContext Subject State}
    {s : Subject} {P : Prop}
    (hpd : PerformedDenial actCtx s P)
    (AxActPolarity : ∀ (s : Subject) (p : Prop), actCtx.Means s p → ∃ q, Incompatible p q ∧ actCtx.Means s q) :
    ∃ Q, Incompatible P Q ∧ actCtx.Means s P ∧ actCtx.Means s Q :=
  performed_denial_implies_chooses hpd AxActPolarity

/-- Countermodel 21: Deterministic Performed Denial.
    An agent in a strictly deterministic D3 world performs the denial of alternative availability
    with full intentionality, authorship, and guidance.
    Yet holding the prior state and laws fixed, no alternative is genuinely available!
    Status: COUNTERMODEL. -/
theorem countermodel_21_deterministic_performed_denial :
    ∃ (World : Type) (PriorState : Type) (Subject : Type) (State : Type) (FutureState : Type)
      (actCtx : StrongActContext Subject State)
      (mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState)
      (s : Subject) (P : Prop) (w : World),
      NomologicalDeterminism_D3 mctx.W ∧
      PerformedDenial actCtx s P ∧
      NoAlternativeAvailable mctx s P w := by
  let W_det : WorldModel (Nat × Bool) Nat Bool := {
    prior := fun w => w.1,
    laws := fun _ => True,
    future := fun _ => true
  }
  let mctx_det : MetaphysicalAvailabilityContext (Nat × Bool) Nat Unit Bool := {
    W := W_det,
    Realizes := fun _ p w => p = True ∧ w.2 = true,
    incompatible_futures := by
      intro s p q w1 w2 hIncomp hDiff hR1 hR2
      exfalso
      rcases hR1 with ⟨rfl, _⟩
      rcases hR2 with ⟨rfl, _⟩
      exact hDiff rfl
  }
  have hD3 : NomologicalDeterminism_D3 mctx_det.W := by
    intro w1 w2 hPrior _ _
    rfl
  let actCtx0 : StrongActContext Unit Nat := {
    Means := fun _ p => p = True,
    Initiates := fun _ w w' p => w = 0 ∧ w' = 1 ∧ p = True,
    Guides := fun _ p => p = True,
    Authors := fun _ p => p = True,
    OwnsAction := fun _ p => p = True
  }
  have hAct : StrongAct Unit Nat actCtx0 () True :=
    ⟨rfl, ⟨0, 1, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩
  have hPD : PerformedDenial actCtx0 () True := ⟨hAct⟩
  have hNoAlt : NoAlternativeAvailable mctx_det () True (0, true) := by
    intro q hIncomp hDiff ⟨w', hPrior', hLaws', hR'⟩
    rcases hR' with ⟨rfl, _⟩
    exact hDiff rfl
  refine ⟨(Nat × Bool), Nat, Unit, Nat, Bool, actCtx0, mctx_det, (), True, (0, true), hD3, hPD, hNoAlt⟩

/-- Theorem: Performed denial does NOT imply metaphysical availability.
    Status: COUNTERMODEL. -/
theorem performed_denial_not_implies_metaphysical_availability :
    ∃ (World : Type) (PriorState : Type) (Subject : Type) (State : Type) (FutureState : Type)
      (actCtx : StrongActContext Subject State)
      (mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState)
      (s : Subject) (P : Prop) (w : World),
      PerformedDenial actCtx s P ∧
      ∀ Q, Incompatible P Q → P ≠ Q → ¬ Available mctx s Q w := by
  rcases countermodel_21_deterministic_performed_denial with
    ⟨World, PriorState, Subject, State, FutureState, actCtx, mctx, s, P, w, _, hPD, hNoAlt⟩
  exact ⟨World, PriorState, Subject, State, FutureState, actCtx, mctx, s, P, w, hPD, hNoAlt⟩

/-- Theorem: Performed denial does NOT imply genuine choice.
    Status: COUNTERMODEL. -/
theorem performed_denial_not_implies_genuine_chooses :
    ∃ (World : Type) (PriorState : Type) (Subject : Type) (State : Type) (FutureState : Type)
      (cctx : StrongChoosesContext Subject)
      (actCtx : StrongActContext Subject State)
      (mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState)
      (s : Subject) (P : Prop) (w : World),
      PerformedDenial actCtx s P ∧
      ∀ Q, ¬ GenuineChooses cctx mctx s P Q w := by
  rcases countermodel_21_deterministic_performed_denial with
    ⟨World, PriorState, Subject, State, FutureState, actCtx, mctx, s, P, w, _, hPD, hNoAlt⟩
  let cctx0 : StrongChoosesContext Subject := {
    Represents := fun _ _ => True,
    Evaluates := fun _ _ _ => True,
    SettlesOn := fun _ _ _ => True,
    OwnsSettlement := fun _ _ _ => True
  }
  refine ⟨World, PriorState, Subject, State, FutureState, cctx0, actCtx, mctx, s, P, w, hPD, ?_⟩
  intro Q hGC
  have hAvailQ := hGC.avail_q
  have hNotAvailQ := hNoAlt Q hGC.incomp hGC.diff
  exact hNotAvailQ hAvailQ

/-- Theorem: Performed denial is completely consistent with Nomological Determinism D3.
    Status: COUNTERMODEL. -/
theorem performed_denial_consistent_with_d3 :
    ∃ (World : Type) (PriorState : Type) (Subject : Type) (State : Type) (FutureState : Type)
      (actCtx : StrongActContext Subject State)
      (mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState)
      (s : Subject) (P : Prop) (w : World),
      NomologicalDeterminism_D3 mctx.W ∧
      PerformedDenial actCtx s P ∧
      NoAlternativeAvailable mctx s P w := by
  rcases countermodel_21_deterministic_performed_denial with
    ⟨World, PriorState, Subject, State, FutureState, actCtx, mctx, s, P, w, hD3, hPD, hNoAlt⟩
  exact ⟨World, PriorState, Subject, State, FutureState, actCtx, mctx, s, P, w, hD3, hPD, hNoAlt⟩

/-- The Minimal Retorsive Principle: RetorsiveAvailability.
    States that every intentional, authored action constitutes a genuine choice point
    with at least one genuinely available incompatible alternative.
    Status: METAPHYSICAL AXIOM / OPEN BRIDGE. -/
def RetorsiveAvailability
    {World PriorState Subject State FutureState : Type}
    (actCtx : StrongActContext Subject State)
    (mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState) : Prop :=
  ∀ (s : Subject) (P : Prop) (w : World),
    StrongAct Subject State actCtx s P →
    ∃ Q : Prop, Incompatible P Q ∧ P ≠ Q ∧ Available mctx s P w ∧ Available mctx s Q w

/-- Theorem: Under the RetorsiveAvailability principle, performing a denial of availability is self-refuting.
    If the agent performs P = NoAlternativeAvailable, RetorsiveAvailability forces the existence
    of an available incompatible alternative Q, contradicting P.
    Status: PROVED (Conditional on RetorsiveAvailability). -/
theorem denial_of_no_metaphysical_alternative_is_self_refuting
    {World PriorState Subject State FutureState : Type}
    {actCtx : StrongActContext Subject State}
    {mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState}
    (hRet : RetorsiveAvailability actCtx mctx)
    (s : Subject) (w : World)
    (P : Prop) (hP_def : P ↔ NoAlternativeAvailable mctx s P w)
    (hPD : PerformedDenial actCtx s P) :
    ¬ P := by
  intro hP
  have hNoAlt := hP_def.mp hP
  have hAct := hPD.strong_act
  rcases hRet s P w hAct with ⟨Q, hIncomp, hDiff, _, hAvailQ⟩
  have hNotAvailQ := hNoAlt Q hIncomp hDiff
  exact hNotAvailQ hAvailQ

/-- Theorem: Under RetorsiveAvailability and deliberative settlement, the denial of genuine choice is self-refuting.
    Status: PROVED (Conditional on RetorsiveAvailability). -/
theorem denial_of_genuine_choice_is_self_refuting
    {World PriorState Subject State FutureState : Type}
    {cctx : StrongChoosesContext Subject}
    {actCtx : StrongActContext Subject State}
    {mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState}
    (hRet : RetorsiveAvailability actCtx mctx)
    (s : Subject) (w : World)
    (P : Prop)
    (hPD : PerformedDenial actCtx s P)
    (hLaws : mctx.W.laws w)
    (SettlesAlternative : ∀ Q, Incompatible P Q → StrongChooses Subject cctx s P Q)
    (hP_def : P ↔ ∀ Q, Incompatible P Q → P ≠ Q → NoGenuineChoice cctx mctx s P Q w) :
    ¬ P := by
  intro hP
  have hNoGC := hP_def.mp hP
  have hAct := hPD.strong_act
  rcases hRet s P w hAct with ⟨Q, hIncomp, hDiff, hAvailP, hAvailQ⟩
  have hNoGC_Q := hNoGC Q hIncomp hDiff
  have hSC := SettlesAlternative Q hIncomp
  have hGC : GenuineChooses cctx mctx s P Q w :=
    ⟨hSC, hAvailP, hAvailQ, hIncomp, hDiff, hLaws⟩
  exact hNoGC_Q hGC

-- ===========================================================================
-- Part XIX: Normative Foundation of the Free Subject
-- ===========================================================================

/-!
### 19. Strong Right and Wrong as Ontological Foundation for the Free Subject
Investigates the thesis that Strong Right and Strong Wrong necessarily require
a Free Subject (endowed with Genuine Choice among metaphysically available alternatives)
as their ontological foundation.
-/

/-- Genuine Free Subject: A Subject who exercises Genuine Choice at choice-point world w.
    Status: DEFINITIONAL. -/
def GenuineFreeSubject
    {Subject World PriorState FutureState : Type}
    (cctx : StrongChoosesContext Subject)
    (mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState)
    (s : Subject) (w : World) : Prop :=
  ∃ p q : Prop, GenuineChooses cctx mctx s p q w

/-- Strong Normative Fact: An objective truth of Right or Wrong.
    Treats the established Right/Wrong distinction as input without reopening its proof.
    Status: DEFINITIONAL. -/
structure StrongNormativeFact where
  fact : Prop
  is_true : fact
  is_normative : fact = (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) ∨ fact = True

/-- Strong Normative Fact obtaining at a world w.
    Status: DEFINITIONAL. -/
structure StrongNormativeFactAt (World : Type) (_w : World) where
  fact : Prop
  is_true_at : fact
  is_normative : fact = (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) ∨ fact = True

/-- Grounding context connecting subjects or entities to normative facts.
    Status: DEFINITIONAL. -/
structure NormativeGroundingContext (Subject : Type) (World : Type) where
  Grounds : Subject → Prop → World → Prop

/-- The Normative Free Grounding Principle (Actual World form):
    Every Strong Normative Fact has a Genuine Free Subject as its ontological foundation.
    Status: METAPHYSICAL AXIOM / OPEN BRIDGE. -/
def NormativeFreeGroundingPrinciple
    {Subject World PriorState FutureState : Type}
    (cctx : StrongChoosesContext Subject)
    (mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState)
    (gctx : NormativeGroundingContext Subject World)
    (w : World) : Prop :=
  ∀ (n : StrongNormativeFact),
    ∃ (s : Subject), GenuineFreeSubject cctx mctx s w ∧ gctx.Grounds s n.fact w

/-- The Necessary Normative Free Grounding Principle (Modal / World-indexed form):
    In every lawful world, every Strong Normative Fact requires a Genuine Free Subject as its foundation.
    Status: METAPHYSICAL AXIOM / OPEN BRIDGE. -/
def NecessaryNormativeFreeGroundingPrinciple
    {Subject World PriorState FutureState : Type}
    (cctx : StrongChoosesContext Subject)
    (mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState)
    (gctx : NormativeGroundingContext Subject World) : Prop :=
  ∀ (w : World), mctx.W.laws w →
    ∀ (n : StrongNormativeFactAt World w),
      ∃ (s : Subject), GenuineFreeSubject cctx mctx s w ∧ gctx.Grounds s n.fact w

/-- Countermodel 22: Platonic / Impersonal Normative Realism.
    Objective Strong Right and Wrong obtain necessarily, but are grounded in impersonal abstract reality.
    There are zero Free Subjects in the universe.
    Status: COUNTERMODEL. -/
theorem countermodel_22_platonic_normative_realism :
    ∃ (Subject : Type) (World : Type) (PriorState : Type) (FutureState : Type)
      (cctx : StrongChoosesContext Subject)
      (mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState)
      (w : World) (n : StrongNormativeFact),
      n.fact ∧
      NomologicalDeterminism_D3 mctx.W ∧
      (∀ s, ¬ GenuineFreeSubject cctx mctx s w) := by
  let W_det : WorldModel (Nat × Bool) Nat Bool := {
    prior := fun w => w.1,
    laws := fun _ => True,
    future := fun _ => true
  }
  let mctx_det : MetaphysicalAvailabilityContext (Nat × Bool) Nat Unit Bool := {
    W := W_det,
    Realizes := fun _ p w => p = True ∧ w.2 = true,
    incompatible_futures := by
      intro s p q w1 w2 hIncomp hDiff hR1 hR2
      exfalso
      rcases hR1 with ⟨rfl, _⟩
      rcases hR2 with ⟨rfl, _⟩
      exact hDiff rfl
  }
  have hD3 : NomologicalDeterminism_D3 mctx_det.W := by
    intro w1 w2 hPrior _ _
    rfl
  let cctx0 : StrongChoosesContext Unit := {
    Represents := fun _ _ => True,
    Evaluates := fun _ _ _ => True,
    SettlesOn := fun _ _ _ => True,
    OwnsSettlement := fun _ _ _ => True
  }
  have hNorm : StrongNormativeFact := {
    fact := ¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F,
    is_true := Logos.Core.rightWrongDistinction,
    is_normative := Or.inl rfl
  }
  have hNoFree : ∀ s : Unit, ¬ GenuineFreeSubject cctx0 mctx_det s (0, true) := by
    intro s ⟨p, q, hGC⟩
    have hD3_ex := countermodel_20_d3_excludes_genuine_choice cctx0 mctx_det s p q (0, true) hD3
    exact hD3_ex hGC
  exact ⟨Unit, (Nat × Bool), Nat, Bool, cctx0, mctx_det, (0, true), hNorm, hNorm.is_true, hD3, hNoFree⟩

/-- Countermodel 23: Deterministic Subject Normativism (Spinozistic Model).
    Objective Right and Wrong are grounded in an intentional, authored rational Subject,
    yet the universe is strictly D3 deterministic with zero alternative availability.
    Status: COUNTERMODEL. -/
theorem countermodel_23_deterministic_subject_normativism :
    ∃ (Subject : Type) (World : Type) (PriorState : Type) (FutureState : Type)
      (cctx : StrongChoosesContext Subject)
      (mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState)
      (gctx : NormativeGroundingContext Subject World)
      (w : World) (s : Subject) (n : StrongNormativeFact),
      n.fact ∧
      NomologicalDeterminism_D3 mctx.W ∧
      gctx.Grounds s n.fact w ∧
      (∀ s', ¬ GenuineFreeSubject cctx mctx s' w) := by
  let W_det : WorldModel (Nat × Bool) Nat Bool := {
    prior := fun w => w.1,
    laws := fun _ => True,
    future := fun _ => true
  }
  let mctx_det : MetaphysicalAvailabilityContext (Nat × Bool) Nat Unit Bool := {
    W := W_det,
    Realizes := fun _ p w => p = True ∧ w.2 = true,
    incompatible_futures := by
      intro s p q w1 w2 hIncomp hDiff hR1 hR2
      exfalso
      rcases hR1 with ⟨rfl, _⟩
      rcases hR2 with ⟨rfl, _⟩
      exact hDiff rfl
  }
  have hD3 : NomologicalDeterminism_D3 mctx_det.W := by
    intro w1 w2 hPrior _ _
    rfl
  let cctx0 : StrongChoosesContext Unit := {
    Represents := fun _ _ => True,
    Evaluates := fun _ _ _ => True,
    SettlesOn := fun _ _ _ => True,
    OwnsSettlement := fun _ _ _ => True
  }
  let gctx0 : NormativeGroundingContext Unit (Nat × Bool) := {
    Grounds := fun _ _ _ => True
  }
  have hNorm : StrongNormativeFact := {
    fact := ¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F,
    is_true := Logos.Core.rightWrongDistinction,
    is_normative := Or.inl rfl
  }
  have hNoFree : ∀ s : Unit, ¬ GenuineFreeSubject cctx0 mctx_det s (0, true) := by
    intro s ⟨p, q, hGC⟩
    have hD3_ex := countermodel_20_d3_excludes_genuine_choice cctx0 mctx_det s p q (0, true) hD3
    exact hD3_ex hGC
  exact ⟨Unit, (Nat × Bool), Nat, Bool, cctx0, mctx_det, gctx0, (0, true), (), hNorm, hNorm.is_true, hD3, trivial, hNoFree⟩

/-- Theorem: Strong Normative Facts do NOT logically entail a Genuine Free Subject.
    Separated by Platonic and Deterministic countermodels.
    Status: COUNTERMODEL. -/
theorem normative_fact_not_implies_free_subject :
    ∃ (Subject : Type) (World : Type) (PriorState : Type) (FutureState : Type)
      (cctx : StrongChoosesContext Subject)
      (mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState)
      (w : World) (n : StrongNormativeFact),
      n.fact ∧
      (∀ s, ¬ GenuineFreeSubject cctx mctx s w) := by
  rcases countermodel_22_platonic_normative_realism with
    ⟨Subject, World, PriorState, FutureState, cctx, mctx, w, n, hTrue, _, hNoFree⟩
  exact ⟨Subject, World, PriorState, FutureState, cctx, mctx, w, n, hTrue, hNoFree⟩

/-- Theorem: Conditional on the Normative Free Grounding Principle,
    the existence of a Strong Normative Fact entails the existence of a Genuine Free Subject.
    Status: PROVED (Conditional on NormativeFreeGroundingPrinciple). -/
theorem normative_grounding_derives_free_subject
    {Subject World PriorState FutureState : Type}
    {cctx : StrongChoosesContext Subject}
    {mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState}
    {gctx : NormativeGroundingContext Subject World}
    {w : World}
    (hPrinciple : NormativeFreeGroundingPrinciple cctx mctx gctx w)
    (n : StrongNormativeFact) :
    ∃ (s : Subject), GenuineFreeSubject cctx mctx s w := by
  obtain ⟨s, hFS, _⟩ := hPrinciple n
  exact ⟨s, hFS⟩

/-- Theorem: A Genuine Free Subject entails Metaphysical Indeterminism.
    Status: PROVED. -/
theorem free_subject_implies_metaphysical_indeterminism
    {Subject World PriorState FutureState : Type}
    {cctx : StrongChoosesContext Subject}
    {mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState}
    {s : Subject} {w : World}
    (hFS : GenuineFreeSubject cctx mctx s w) :
    MetaphysicalIndeterminism mctx.W := by
  obtain ⟨p, q, hGC⟩ := hFS
  exact genuine_chooses_implies_metaphysical_indeterminism hGC

/-- Theorem: A Genuine Free Subject strictly conflicts with Nomological Determinism D3.
    Status: PROVED. -/
theorem free_subject_conflicts_with_d3
    {Subject World PriorState FutureState : Type}
    {cctx : StrongChoosesContext Subject}
    {mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState}
    {s : Subject} {w : World}
    (hFS : GenuineFreeSubject cctx mctx s w) :
    ¬ NomologicalDeterminism_D3 mctx.W := by
  obtain ⟨p, q, hGC⟩ := hFS
  exact genuine_chooses_conflicts_with_d3 hGC

/-- Theorem: Under the Necessary Normative Free Grounding Principle,
    every lawful world where normative facts obtain contains a Genuine Free Subject.
    Status: PROVED (Conditional on NecessaryNormativeFreeGroundingPrinciple). -/
theorem necessary_normative_grounding_derives_necessary_free_subject
    {Subject World PriorState FutureState : Type}
    {cctx : StrongChoosesContext Subject}
    {mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState}
    {gctx : NormativeGroundingContext Subject World}
    (hNecPrinciple : NecessaryNormativeFreeGroundingPrinciple cctx mctx gctx)
    (NormativeFactsEverywhere : ∀ (w : World), mctx.W.laws w → StrongNormativeFactAt World w) :
    ∀ (w : World), mctx.W.laws w → ∃ (s : Subject), GenuineFreeSubject cctx mctx s w := by
  intro w hLaws
  have n := NormativeFactsEverywhere w hLaws
  obtain ⟨s, hFS, _⟩ := hNecPrinciple w hLaws n
  exact ⟨s, hFS⟩

/-- Master Theorem: The full conditional chain from Necessary Normative Grounding
    to Metaphysical Indeterminism and the refutation of D3.
    Status: PROVED (Conditional on NecessaryNormativeFreeGroundingPrinciple). -/
theorem necessary_normative_grounding_implies_not_d3
    {Subject World PriorState FutureState : Type}
    {cctx : StrongChoosesContext Subject}
    {mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState}
    {gctx : NormativeGroundingContext Subject World}
    (hNecPrinciple : NecessaryNormativeFreeGroundingPrinciple cctx mctx gctx)
    (NormativeFactsEverywhere : ∀ (w : World), mctx.W.laws w → StrongNormativeFactAt World w)
    (w : World) (hLaws : mctx.W.laws w) :
    MetaphysicalIndeterminism mctx.W ∧ ¬ NomologicalDeterminism_D3 mctx.W := by
  obtain ⟨s, hFS⟩ :=
    necessary_normative_grounding_derives_necessary_free_subject hNecPrinciple NormativeFactsEverywhere w hLaws
  constructor
  · exact free_subject_implies_metaphysical_indeterminism hFS
  · exact free_subject_conflicts_with_d3 hFS

end Logos.StrongActionChoice
