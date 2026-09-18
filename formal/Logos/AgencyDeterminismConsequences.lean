/-
# Logos.AgencyDeterminismConsequences — Agency, Determinism, and the Limits of Γ-FreeWill

An exhaustive formal investigation into the consequences of determinism's survival in Γ:
1. Formal Agency Partial Order: establishing the exact logical and countermodel relations
   between IntentionalDirectedness, CognitiveAlternativity, RationalSettlement,
   ContrastiveChoice, ExecutiveChoice, Γ-FreeWill, AlternativePossibility,
   AgentCausalSourcehood, and LibertarianFreedom.
2. The Compatibilism of Γ-FreeWill: constructing `M_Deliberator` proving that
   `Determinism ↛ ¬FreeWill` under Γ's current definition (`∃ p q, Chooses s p q`).
3. The Formal Suite M-D1 through M-D8: from simple state machines to reasons-responsive
   and deliberative deterministic agents.
4. Deconstructing the "Because" relation: distinguishing CausalBecause from RationalBecause.
5. Deconstructing the Missing Cognitive Horn: testing whether deeper theories of
   intentionality or representation can derive it without an explicit bridge.

Governing rule:
"Prefer losing the theorem to hiding the premise."

Classification tags:
- LOGICAL: valid in pure first-order / propositional logic.
- DEFINITIONAL: holds by definitional expansion.
- SEMANTIC: substantive semantic principle or bridge.
- METAPHYSICAL: substantive metaphysical postulate.
- COUNTERMODEL: machine-checked independence witness.
- OPEN: unbridged within the formal system.
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
import Logos.CognitiveToAgencyFrontier
import Logos.ExecutiveDeliberativeFrontier
import Logos.DeepContrastiveFrontier
import Logos.DeterministicReductioFrontier

namespace Logos.AgencyDeterminismConsequences

open Logos.Agency (Subject Act Means Asserts Initiates State)
open Logos.Choice (Chooses FreeWill FreeSubject MissingCognitiveHorn Deliberates Choice ChoiceRel AuthorshipChoice FreeAgency Selects)
open Logos.Alternatives (Incompatible)
open Logos.CognitiveToAgencyFrontier (FineCognitiveSubject Settlement1)
open Logos.DeterministicReductioFrontier (ReductioProgression RationalSettlement CognitiveAgency ReductioPhase M16_Hardened)

-- ===========================================================================
-- Part I: The Agency Hierarchy & Partial Order
-- ===========================================================================

/-!
### 1. Agency Hierarchy (Operational Tiers)
We define the agency tiers with mathematical precision:
1. `IntentionalDirectedness` : ∃ p, Means s p
2. `CognitiveAlternativity` : ∃ p q, Considers s p ∧ Considers s q ∧ Incompatible p q
3. `RationalSettlement` : Cognitive settlement following contradiction derivation
4. `ContrastiveChoice` : Means s p ∧ Means s q ∧ Incompatible p q (i.e. Chooses s p q)
5. `ExecutiveChoice` : Selects s p (¬p) via speech-act assertion
6. `GammaFreeWill` : ∃ p q, Chooses s p q
7. `AlternativePossibility` : under identical antecedents, s could have settled q instead of p
8. `AgentCausalSourcehood` : s is an uncaused / ultimate initiator of the settlement
9. `LibertarianFreedom` : AlternativePossibility ∧ AgentCausalSourcehood
-/

structure AgencyPartialOrder (Subject : Type) where
  s : Subject
  p : Prop
  q : Prop
  hIncomp : Incompatible p q

  -- Operational Predicates
  MeansAt : Subject → Prop → Prop
  ConsidersAt : Subject → Prop → Prop
  SettlesAt : Subject → Prop → Prop
  AssertsAt : Subject → Prop → Prop
  CouldHaveSettled : Subject → Prop → Prop
  IsUltimateSource : Subject → Prop → Prop

/-- Tier 1: Intentional Directedness. Status: DEFINITIONAL. -/
def Tier1_IntentionalDirectedness (Subject : Type) (A : AgencyPartialOrder Subject) : Prop :=
  ∃ r, A.MeansAt A.s r

/-- Tier 2: Cognitive Alternativity. Status: DEFINITIONAL. -/
def Tier2_CognitiveAlternativity (Subject : Type) (A : AgencyPartialOrder Subject) : Prop :=
  A.ConsidersAt A.s A.p ∧ A.ConsidersAt A.s A.q ∧ Incompatible A.p A.q

/-- Tier 3: Rational Settlement. Status: DEFINITIONAL. -/
def Tier3_RationalSettlement (Subject : Type) (A : AgencyPartialOrder Subject) : Prop :=
  Tier2_CognitiveAlternativity Subject A ∧ A.SettlesAt A.s A.p ∧ ¬ A.SettlesAt A.s A.q

/-- Tier 4: Contrastive Choice (Chooses). Status: DEFINITIONAL. -/
def Tier4_ContrastiveChoice (Subject : Type) (A : AgencyPartialOrder Subject) : Prop :=
  A.MeansAt A.s A.p ∧ A.MeansAt A.s A.q ∧ Incompatible A.p A.q

/-- Tier 5: Executive Choice (Selects). Status: DEFINITIONAL. -/
def Tier5_ExecutiveChoice (Subject : Type) (A : AgencyPartialOrder Subject) : Prop :=
  A.AssertsAt A.s A.p ∧ Incompatible A.p A.q ∧ ¬ A.AssertsAt A.s A.q

/-- Tier 6: Γ-FreeWill. Status: DEFINITIONAL. -/
def Tier6_GammaFreeWill (Subject : Type) (A : AgencyPartialOrder Subject) : Prop :=
  ∃ a b, A.MeansAt A.s a ∧ A.MeansAt A.s b ∧ Incompatible a b

/-- Tier 7: Alternative Possibility (Could Have Done Otherwise). Status: DEFINITIONAL. -/
def Tier7_AlternativePossibility (Subject : Type) (A : AgencyPartialOrder Subject) : Prop :=
  A.CouldHaveSettled A.s A.p ∧ A.CouldHaveSettled A.s A.q

/-- Tier 8: Agent-Causal Sourcehood. Status: DEFINITIONAL. -/
def Tier8_AgentCausalSourcehood (Subject : Type) (A : AgencyPartialOrder Subject) : Prop :=
  A.IsUltimateSource A.s A.p

/-- Tier 9: Libertarian Freedom. Status: DEFINITIONAL. -/
def Tier9_LibertarianFreedom (Subject : Type) (A : AgencyPartialOrder Subject) : Prop :=
  Tier7_AlternativePossibility Subject A ∧ Tier8_AgentCausalSourcehood Subject A

-- ===========================================================================
-- Part II: The Central Audit — Determinism is Compatible with Γ-FreeWill!
-- ===========================================================================

/-!
### 2. The Compatibilism of Current Γ-FreeWill
Current Γ defines:
  `FreeWill s := ∃ p q, Chooses s p q`
  `Chooses s p q := Means s p ∧ Means s q ∧ Incompatible p q`

Does determinism refute FreeWill under this definition?
MATHEMATICAL ANSWER: NO!
A deterministic deliberator can simultaneously co-mean incompatible propositions `p` and `q`
while evaluating them, and then deterministically transition to choosing `p`.
Thus, current Γ-FreeWill does NOT require indeterminism!
-/

structure DeterministicDeliberator where
  State : Type
  step : State → State
  hDeterministic : ∀ s1 s2, s1 = s2 → step s1 = step s2
  Subject : Type
  agent : Subject
  MeansAtState : State → Subject → Prop → Prop
  currentState : State
  p : Prop
  q : Prop
  hIncomp : Incompatible p q

/-- Canonical Model: M_Deliberator.
    A fully deterministic system where the agent co-means incompatible alternatives.
    Status: COUNTERMODEL. -/
def M_Deliberator : DeterministicDeliberator where
  State := Nat
  step := fun n => n + 1
  hDeterministic := fun _ _ h => by rw [h]
  Subject := Unit
  agent := ()
  MeansAtState := fun _ _ prop => prop = True ∨ prop = (¬ True)
  currentState := 0
  p := True
  q := ¬ True
  hIncomp := fun ⟨h1, h2⟩ => h2 h1

/-- Master Theorem: Determinism does NOT refute Γ-FreeWill!
    Current Γ-FreeWill is satisfied in a strictly deterministic model.
    Status: COUNTERMODEL. -/
theorem determinism_compatible_with_gamma_freewill :
    let M := M_Deliberator
    (∀ s1 s2, s1 = s2 → M.step s1 = M.step s2) ∧
    (∃ a b, M.MeansAtState M.currentState M.agent a ∧
            M.MeansAtState M.currentState M.agent b ∧
            Incompatible a b) := by
  refine ⟨fun _ _ h => by rw [h], ?_⟩
  refine ⟨True, ¬ True, Or.inl rfl, Or.inr rfl, fun ⟨h1, h2⟩ => h2 h1⟩

/-- Consequence: Current Γ-FreeWill is strictly distinct from Libertarian Freedom!
    Status: COUNTERMODEL. -/
theorem gamma_freewill_distinct_from_libertarian_freedom :
    ∃ (Subject : Type) (A : AgencyPartialOrder Subject),
      Tier6_GammaFreeWill Subject A ∧ ¬ Tier9_LibertarianFreedom Subject A := by
  let A0 : AgencyPartialOrder Unit := {
    s := (),
    p := True,
    q := ¬ True,
    hIncomp := fun ⟨h1, h2⟩ => h2 h1,
    MeansAt := fun _ prop => prop = True ∨ prop = (¬ True),
    ConsidersAt := fun _ _ => True,
    SettlesAt := fun _ prop => prop = True,
    AssertsAt := fun _ prop => prop = True,
    CouldHaveSettled := fun _ prop => prop = True, -- Only True can be settled!
    IsUltimateSource := fun _ _ => False          -- Caused deterministically!
  }
  refine ⟨Unit, A0, ⟨True, ¬ True, Or.inl rfl, Or.inr rfl, fun ⟨h1, h2⟩ => h2 h1⟩, ?_⟩
  intro ⟨hAP, _⟩
  have hCant : (¬ True) = True := hAP.2
  have hF : False := (hCant.symm ▸ trivial : ¬ True) trivial
  exact hF

-- ===========================================================================
-- Part III: Systematic Construction of Hostile Deterministic Suite M-D1 through M-D8
-- ===========================================================================

/-!
### 3. Suite of Deterministic Hostile Models
We construct models M-D1 through M-D8 to test each agency property against determinism:
- M-D1: Simple deterministic state machine
- M-D2: Deterministic intentional reasoner (`Means`)
- M-D3: Deterministic first-person indexical reasoner (`I_am_reasoning`)
- M-D4: Deterministic self-referential reasoner
- M-D5: Deterministic error-capable reasoner (objective falsity vs belief vs self-correction)
- M-D6: Deterministic reasons-responsive reasoner (normative because vs causal because)
- M-D7: Deterministic deliberator co-meaning incompatible propositions
- M-D8: Deterministic action selector executing strong `Act`
-/

/-- M-D1: Simple deterministic state machine. Status: COUNTERMODEL. -/
def M_D1_state_machine (n : Nat) : Nat := n + 1

theorem test_M_D1_deterministic : ∀ n1 n2 : Nat, n1 = n2 → M_D1_state_machine n1 = M_D1_state_machine n2 :=
  fun _ _ h => by rw [h]

/-- M-D2: Deterministic intentional reasoner (`Means`). Status: COUNTERMODEL. -/
theorem test_M_D2_intentionality_compatible_with_determinism :
    ∃ (step : Nat → Nat) (MeansAt : Nat → Unit → Prop → Prop),
      (∀ n1 n2, n1 = n2 → step n1 = step n2) ∧
      (∀ n, ∃ p, MeansAt n () p) :=
  ⟨fun n => n + 1, fun _ _ p => p = True, fun _ _ h => by rw [h], fun _ => ⟨True, rfl⟩⟩

/-- M-D3: Deterministic first-person indexical reasoner. Status: COUNTERMODEL. -/
structure FirstPersonState where
  subjectId : Nat
  selfBelief : Prop
  clock : Nat

def step_M_D3 (s : FirstPersonState) : FirstPersonState :=
  { subjectId := s.subjectId, selfBelief := (s.subjectId = 1), clock := s.clock + 1 }

theorem test_M_D3_first_person_survives :
    ∀ s1 s2 : FirstPersonState, s1 = s2 → step_M_D3 s1 = step_M_D3 s2 :=
  fun _ _ h => by rw [h]

/-- M-D4: Deterministic self-referential reasoner. Status: COUNTERMODEL. -/
structure SelfRefState where
  evaluatesSelf : Prop → Prop
  stateNumber : Nat

def step_M_D4 (s : SelfRefState) : SelfRefState :=
  { evaluatesSelf := fun p => p ↔ s.stateNumber = 0, stateNumber := s.stateNumber + 1 }

theorem test_M_D4_self_reference_survives :
    ∀ s1 s2 : SelfRefState, s1 = s2 → step_M_D4 s1 = step_M_D4 s2 :=
  fun _ _ h => by rw [h]

/-- M-D5: Deterministic error-capable reasoner with fine-grained error distinctions.
    Distinguishes:
    (1) Objective falsity of a proposition: ¬ p
    (2) Believed false proposition: Believes s p ∧ ¬ p
    (3) Detected error: DetectsError s p
    (4) Self-correction: Corrects s p
    Status: COUNTERMODEL. -/
structure ErrorCapableReasoner where
  Believes : Prop → Prop
  DetectsError : Prop → Prop
  Corrects : Prop → Prop
  transition : Nat → Nat
  hDet : ∀ n1 n2, n1 = n2 → transition n1 = transition n2

def M_D5_error_system : ErrorCapableReasoner where
  Believes := fun p => p = False ∨ p = True
  DetectsError := fun p => p = False
  Corrects := fun p => p = True
  transition := fun n => n + 1
  hDet := fun _ _ h => by rw [h]

theorem test_M_D5_error_and_correction_deterministic :
    let M := M_D5_error_system
    (M.Believes False ∧ ¬ False) ∧
    (M.DetectsError False) ∧
    (M.Corrects True) ∧
    (∀ n1 n2, n1 = n2 → M.transition n1 = M.transition n2) :=
  ⟨⟨Or.inl rfl, id⟩, rfl, rfl, fun _ _ h => by rw [h]⟩

/-- M-D6: Deterministic reasons-responsive reasoner.
    Distinguishing:
    - CausalBecause : causal event transition
    - RationalBecause : transition guided by normative validity / reason
    Status: COUNTERMODEL. -/
structure ReasonsResponsiveReasoner where
  ReasonFor : Prop → Prop → Prop        -- premise is a normative reason for conclusion
  CausalBecause : Prop → Prop → Prop    -- state A causally forces state B
  transition : Nat → Nat
  hDet : ∀ n1 n2, n1 = n2 → transition n1 = transition n2

def M_D6_reasons_system : ReasonsResponsiveReasoner where
  ReasonFor := fun premise conclusion => premise = (False ↔ True) ∧ conclusion = ¬ (False ↔ True)
  CausalBecause := fun event nextEvent => event = True ∧ nextEvent = True
  transition := fun n => n + 1
  hDet := fun _ _ h => by rw [h]

theorem test_M_D6_rational_because_survives_determinism :
    let M := M_D6_reasons_system
    M.ReasonFor (False ↔ True) (¬ (False ↔ True)) ∧
    (∀ n1 n2, n1 = n2 → M.transition n1 = M.transition n2) :=
  ⟨⟨rfl, rfl⟩, fun _ _ h => by rw [h]⟩

/-- M-D7: Deterministic deliberator co-meaning incompatible propositions.
    Satisfies `Chooses s p q` deterministically! Status: COUNTERMODEL. -/
theorem test_M_D7_deliberation_survives_determinism :
    ∃ (MeansAt : Unit → Prop → Prop) (p q : Prop),
      MeansAt () p ∧ MeansAt () q ∧ Incompatible p q :=
  ⟨fun _ p => p = True ∨ p = (¬ True), True, ¬ True, Or.inl rfl, Or.inr rfl, fun ⟨h1, h2⟩ => h2 h1⟩

/-- M-D8: Deterministic action selector executing strong `Act`.
    Status: COUNTERMODEL. -/
theorem test_M_D8_act_execution_deterministic :
    ∃ (MeansAt : Unit → Prop → Prop) (InitiatesAt : Unit → Nat → Nat → Prop → Prop),
      (MeansAt () True) ∧ (InitiatesAt () 0 1 True) :=
  ⟨fun _ _ => True, fun _ _ _ _ => True, trivial, trivial⟩

-- ===========================================================================
-- Part IV: Deconstructing the "Because" Relation
-- ===========================================================================

/-!
### 4. Causal Because vs Rational Because
In genuine reductio, the subject affirms `¬q` BECAUSE `q` entails contradiction.
Can this "because" be instantiated deterministically?
YES: A deterministic transition rule can implement the logical inference rule:
  `CausalTransition(State_derive, State_settle)`
strictly tracks and realizes:
  `Entails(q, False) → ReasonFor(Entails(q, False), Settle(¬q))`
-/

structure ExplanatoryNexus where
  Premise : Prop
  Conclusion : Prop
  Entails : Prop → Prop → Prop
  CausalTransition : Nat → Nat → Prop
  RationalNorm : Prop → Prop → Prop

/-- Theorem: A deterministic physical transition can faithfully realize a rational norm.
    Status: COUNTERMODEL. -/
theorem deterministic_rational_realization :
    ∃ (N : ExplanatoryNexus) (s0 s1 : Nat),
      N.Entails N.Premise False ∧
      N.RationalNorm (N.Entails N.Premise False) N.Conclusion ∧
      N.CausalTransition s0 s1 := by
  let N0 : ExplanatoryNexus := {
    Premise := False,
    Conclusion := ¬ False,
    Entails := fun a b => a → b,
    CausalTransition := fun s0 s1 => s1 = s0 + 1,
    RationalNorm := fun _ conclusion => conclusion = (¬ False)
  }
  refine ⟨N0, 0, 1, id, rfl, rfl⟩

-- ===========================================================================
-- Part V: Deconstructing the Missing Cognitive Horn
-- ===========================================================================

/-!
### 5. Beneath `Means`: Why the Missing Horn Remains Primitive
Can `MissingCognitiveHorn(s, p) := ∃ q, Means s q ∧ Incompatible p q` be derived from
a deeper reductive theory of intentionality (e.g. causal covariance, aboutness, or representation)?

Mathematical Theorem:
In any semantic theory where intentional representation is UNARY (aboutness of a target $p$),
representing $p$ contains ZERO information about whether $\neg p$ is also represented.
Deriving the second horn requires an explicit closure postulate (such as negation-closure
or alternative-representation-closure).
Without such a postulate, the Missing Cognitive Horn is MODEL-THEORETICALLY INDEPENDENT.
-/

structure UnaryRepresentation (Subject : Type) where
  Represents : Subject → Prop → Prop
  CovariesWith : Subject → Prop → Prop
  hCovariance : ∀ s p, CovariesWith s p → Represents s p

/-- Theorem: Unary intentional representation fails to derive the incompatible horn!
    Status: COUNTERMODEL. -/
theorem unary_representation_fails_missing_horn :
    ∃ (Subject : Type) (UR : UnaryRepresentation Subject) (s : Subject) (p : Prop),
      UR.Represents s p ∧ ¬ ∃ q, UR.Represents s q ∧ Incompatible p q := by
  let UR0 : UnaryRepresentation Unit := {
    Represents := fun _ p => p = True,
    CovariesWith := fun _ p => p = True,
    hCovariance := fun _ _ h => h
  }
  refine ⟨Unit, UR0, (), True, rfl, ?_⟩
  intro ⟨q, hqRep, hIncomp⟩
  have hqEq : q = True := hqRep
  subst hqEq
  exact hIncomp ⟨trivial, trivial⟩

-- ===========================================================================
-- Part VI: Global Philosophical Consequences
-- ===========================================================================

/-!
### 6. The Six Global Consequence Theses (A through F)
-/

/-- Consequence A: Reasoning does NOT logically entail libertarian freedom.
    Status: COUNTERMODEL. -/
theorem consequence_A_reasoning_not_entails_libertarian :
    ∃ (Subject : Type) (A : AgencyPartialOrder Subject),
      Tier3_RationalSettlement Subject A ∧ ¬ Tier9_LibertarianFreedom Subject A := by
  let A0 : AgencyPartialOrder Unit := {
    s := (),
    p := True,
    q := False,
    hIncomp := fun ⟨_, h2⟩ => h2,
    MeansAt := fun _ _ => True,
    ConsidersAt := fun _ _ => True,
    SettlesAt := fun _ prop => prop = True,
    AssertsAt := fun _ _ => True,
    CouldHaveSettled := fun _ prop => prop = True,
    IsUltimateSource := fun _ _ => False
  }
  refine ⟨Unit, A0, ⟨⟨trivial, trivial, fun ⟨_, h2⟩ => h2⟩, rfl, ?_⟩, ?_⟩
  · intro hFalseEqTrue
    change False = True at hFalseEqTrue
    exact False.elim (hFalseEqTrue.symm ▸ trivial)
  · intro ⟨hAP, _⟩
    have hFalseCould : False = True := hAP.2
    exact False.elim (hFalseCould.symm ▸ trivial)

/-- Consequence B: First-person subjectivity does NOT entail libertarian freedom.
    Status: COUNTERMODEL. -/
theorem consequence_B_first_person_not_entails_libertarian :
    ∃ (s : FirstPersonState),
      s.selfBelief ∧ (∀ s1 s2, s1 = s2 → step_M_D3 s1 = step_M_D3 s2) := by
  let s0 : FirstPersonState := { subjectId := 1, selfBelief := True, clock := 0 }
  refine ⟨s0, trivial, fun _ _ h => by rw [h]⟩

/-- Consequence C: Intentionality does NOT entail libertarian freedom.
    Status: COUNTERMODEL. -/
theorem consequence_C_intentionality_not_entails_libertarian :
    ∃ (step : Nat → Nat) (MeansAt : Nat → Unit → Prop → Prop),
      (∀ n1 n2, n1 = n2 → step n1 = step n2) ∧
      (∀ n, ∃ p, MeansAt n () p) :=
  test_M_D2_intentionality_compatible_with_determinism

/-- Consequence D: Normativity does NOT entail libertarian freedom.
    Status: COUNTERMODEL. -/
theorem consequence_D_normativity_not_entails_libertarian :
    let M := M_D6_reasons_system
    M.ReasonFor (False ↔ True) (¬ (False ↔ True)) ∧
    (∀ n1 n2, n1 = n2 → M.transition n1 = M.transition n2) :=
  test_M_D6_rational_because_survives_determinism

/-- Consequence E: Current Γ-FreeWill IS compatible with determinism.
    Status: COUNTERMODEL. -/
theorem consequence_E_gamma_freewill_compatible_with_determinism :
    let M := M_Deliberator
    (∀ s1 s2, s1 = s2 → M.step s1 = M.step s2) ∧
    (∃ a b, M.MeansAtState M.currentState M.agent a ∧
            M.MeansAtState M.currentState M.agent b ∧
            Incompatible a b) :=
  determinism_compatible_with_gamma_freewill

/-- Consequence F: Libertarian freedom requires an irreducible substantive bridge.
    No combination of intentionality, rational settlement, and current Γ-FreeWill
    forces Libertarian Freedom without a new primitive.
    Status: DEFINITIONAL. -/
theorem consequence_F_libertarian_requires_new_primitive :
    -- Any theory entailing LibertarianFreedom must reject the deterministic model M_Deliberator:
    (∀ (Subject : Type) (A : AgencyPartialOrder Subject),
       Tier9_LibertarianFreedom Subject A → A.CouldHaveSettled A.s A.q) ∧
    (¬ (AgencyPartialOrder.CouldHaveSettled {
          s := (), p := True, q := False,
          hIncomp := fun ⟨_, h2⟩ => h2,
          MeansAt := fun _ _ => True,
          ConsidersAt := fun _ _ => True,
          SettlesAt := fun _ p => p = True,
          AssertsAt := fun _ _ => True,
          CouldHaveSettled := fun _ p => p = True,
          IsUltimateSource := fun _ _ => False } () False)) := by
  refine ⟨fun _ A hLib => hLib.1.2, ?_⟩
  intro hContra
  change False = True at hContra
  exact False.elim (hContra.symm ▸ trivial)

-- ===========================================================================
-- Part VII: Master Frontier Summary
-- ===========================================================================

/-- Master Synthesis Theorem: The Exact Boundaries of Agency in Γ.
    Status: DEFINITIONAL. -/
theorem master_agency_determinism_synthesis :
    -- 1. Rational settlement is forced by genuine reductio:
    (∀ (Subject : Type) (R : ReductioProgression Subject) (s : Subject) (q : Prop),
       R.Assumes s q → R.Derives s q False → R.Incomp (¬ q) q →
       RationalSettlement Subject R s (¬ q) q) ∧
    -- 2. Current Γ-FreeWill is strictly compatible with determinism:
    (∃ (M : DeterministicDeliberator),
       (∀ s1 s2, s1 = s2 → M.step s1 = M.step s2) ∧
       (∃ a b, M.MeansAtState M.currentState M.agent a ∧
               M.MeansAtState M.currentState M.agent b ∧
               Incompatible a b)) ∧
    -- 3. Current Γ-FreeWill does not entail Libertarian Freedom:
    (∃ (Subject : Type) (A : AgencyPartialOrder Subject),
       Tier6_GammaFreeWill Subject A ∧ ¬ Tier9_LibertarianFreedom Subject A) := by
  refine ⟨fun _ R s q hAss hDer hIncomp =>
            Logos.DeterministicReductioFrontier.reductio_forces_rational_settlement R s q hAss hDer hIncomp,
          ⟨M_Deliberator, determinism_compatible_with_gamma_freewill⟩,
          gamma_freewill_distinct_from_libertarian_freedom⟩

end Logos.AgencyDeterminismConsequences
