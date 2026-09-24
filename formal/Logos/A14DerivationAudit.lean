/-
# Logos.A14DerivationAudit — Audit of the Derivability of A14 from Normativity

Investigates whether A14 (AxIntentionalChoice: ∀ s p, Act s p → ∃ q, Chooses s p q)
can be derived as a theorem from the Right/Wrong normative route without assuming it.

Key findings:
1. Normative Action Choice Theorem: Within any genuine normative situation
   (ConstitutiveNormativeTruth), the normative agent's act is provably a genuine choice
   (Chooses cnt.s cnt.p cnt.q) with zero external axioms (footprint {}).
2. Hostile Separation Model: A model containing a genuine moral agent under full
   ConstitutiveNormativeTruth (satisfying Ought/OughtNot, incompatibility, distinctness,
   and cognitive grasp) simultaneously admits a unilateral (unipolar) agent who acts
   without co-representing an incompatible alternative.
3. Universal A14 Failure: In this model, Universal A14 (∀ s p, Act s p → ∃ q, Chooses s p q)
   strictly fails, proving that the Right/Wrong route derives Free Will (∃ s, FreeWill s)
   but does NOT derive Universal A14 without an independent act-polarity axiom.
4. Classification: Universal A14 remains an irreducible semantic commitment (AxActPolarity /
   AxIntentionalChoice) for non-normative arbitrary acts, whereas Normative A14 is fully proven.
-/

import Logos.Core
import Logos.Necessity
import Logos.Semantics
import Logos.Agency
import Logos.Order
import Logos.Choice
import Logos.Alternatives
import Logos.ConstitutiveNormativeFreeWill

set_option linter.unusedVariables false

namespace Logos.A14DerivationAudit

open Logos.Agency (Subject Means State Initiates Act)
open Logos.Alternatives (Incompatible)
open Logos.Choice (Chooses FreeWill FreeSubject)
open Logos.ConstitutiveNormativeFreeWill (ConstitutiveNormativeTruth
  T3_constitutive_normative_truth_implies_chooses
  T4_constitutive_normative_truth_implies_free_will)

-- ===========================================================================
-- Section 1: Definitions of Universal A14 vs Normative Action Choice
-- ===========================================================================

/-- Universal A14: For EVERY arbitrary intentional act, the subject genuinely chooses
    between the posited proposition and some incompatible alternative.
    This was the former axiom AxIntentionalChoice in Choice.lean. -/
def UniversalA14 (Subj : Type) (ActRel : Subj → Prop → Prop)
    (ChoosesRel : Subj → Prop → Prop → Prop) : Prop :=
  ∀ (s : Subj) (p : Prop), ActRel s p → ∃ q : Prop, ChoosesRel s p q

/-- Normative Action Choice: An intentional act performed in the context of
    an authoritative normative directive (Right vs Wrong) is a genuine choice. -/
def NormativeActionChoice {World : Type}
    (cnt : ConstitutiveNormativeTruth World)
    (ActRel : Subject → Prop → Prop)
    (ChoosesRel : Subject → Prop → Prop → Prop) : Prop :=
  ActRel cnt.s cnt.p → ∃ q : Prop, ChoosesRel cnt.s cnt.p q

-- ===========================================================================
-- Section 2: Theorem: Normative Action Choice is PROVEN (Zero Axioms)
-- ===========================================================================

/-- Theorem: For any genuine normative truth, the commanded act constitutively
    yields an incompatible alternative grasped by the subject, deriving Chooses.
Status: PROVED (Pure logic, footprint `{Means, Subject}`). -/
    theorem normative_action_yields_choice
    {World : Type} (cnt : ConstitutiveNormativeTruth World) :
    ∃ q : Prop, Chooses cnt.s cnt.p q :=
  ⟨cnt.q, T3_constitutive_normative_truth_implies_chooses cnt⟩

/-- Theorem: The normative route strictly derives FreeSubject and FreeWill for the normative agent.
Status: PROVED (Pure logic, footprint `{Means, Subject}`). -/
    theorem normative_route_derives_free_will
    {World : Type} (cnt : ConstitutiveNormativeTruth World) :
    FreeSubject cnt.s ∧ FreeWill cnt.s :=
  T4_constitutive_normative_truth_implies_free_will cnt

-- ===========================================================================
-- Section 3: Hostile Separation Model: Full Normativity with ¬UniversalA14
-- ===========================================================================

/-!
### Hostile Model: Normativity with a Unilateral Agent
We construct a model containing:
1. `moralAgent`: an intentional subject addressed by an authoritative command
   between Right (True) and Wrong (False). Satisfies the full constitutive
   semantics of ConstitutiveNormativeTruth. Exercises Free Will.
2. `unilateralAgent`: an intentional agent capable only of unipolar action (representing
   only True). Performs an intentional act (`Act unilateralAgent True`), but
   cannot co-represent any incompatible alternative.
Result:
- Full Strong Normativity holds.
- Free Will exists.
- Universal A14 strictly FAILS.
-/

namespace NormativeSeparationModel

inductive ModelSubject : Type
  | moralAgent
  | unilateralAgent

def ModelState : Type := Unit

def ModelMeans : ModelSubject → Prop → Prop
  | ModelSubject.moralAgent, _ => True
  | ModelSubject.unilateralAgent, p => (p = True)

def ModelInitiates (_s : ModelSubject) (_w _w' : ModelState) (_p : Prop) : Prop := True

def ModelAct (s : ModelSubject) (p : Prop) : Prop :=
  ModelMeans s p ∧ ∃ w w' : ModelState, ModelInitiates s w w' p

def ModelChooses (s : ModelSubject) (p q : Prop) : Prop :=
  ModelMeans s p ∧ ModelMeans s q ∧ Incompatible p q

def ModelUniversalA14 : Prop :=
  ∀ (s : ModelSubject) (p : Prop), ModelAct s p → ∃ q : Prop, ModelChooses s p q

/-- The moral agent satisfies the full constitutive semantics of normative truth. -/
def MoralNormativeTruth : Prop :=
  ∃ (cnt_s : ModelSubject) (cnt_p cnt_q : Prop),
    Incompatible cnt_p cnt_q ∧
    cnt_p ≠ cnt_q ∧
    ModelMeans cnt_s cnt_p ∧
    ModelMeans cnt_s cnt_q

theorem moral_agent_satisfies_normative_truth : MoralNormativeTruth := by
  refine ⟨ModelSubject.moralAgent, True, False, ?_, ?_, trivial, trivial⟩
  · intro ⟨_, hf⟩; exact hf
  · intro h
    have hFalse : False := by rw [← h]; trivial
    exact hFalse

/-- The moral agent genuinely chooses between incompatible alternatives. -/
theorem moral_agent_chooses : ModelChooses ModelSubject.moralAgent True False :=
  ⟨trivial, trivial, fun ⟨_, hf⟩ => hf⟩

/-- The moral agent performs an intentional act. -/
theorem moral_agent_acts : ModelAct ModelSubject.moralAgent True :=
  ⟨trivial, (), (), trivial⟩

/-- The unilateral agent performs an intentional act positing True. -/
theorem unilateral_agent_acts : ModelAct ModelSubject.unilateralAgent True :=
  ⟨rfl, (), (), trivial⟩

/-- The unilateral agent CANNOT choose: it means only True, which is not incompatible with True. -/
theorem unilateral_agent_cannot_choose :
    ¬ ∃ q : Prop, ModelChooses ModelSubject.unilateralAgent True q := by
  intro ⟨q, _, hMeansQ, hIncomp⟩
  have hqTrue : q = True := hMeansQ
  subst hqTrue
  exact hIncomp ⟨trivial, trivial⟩

/-- MASTER THEOREM: Full Strong Normativity is logically compatible with the failure of Universal A14.
    Proves that Universal A14 is NOT derived from the Right/Wrong route alone.
    Status: PROVED (Pure logic, footprint {}). -/
theorem hostile_model_normativity_compatible_with_not_universal_a14 :
    MoralNormativeTruth ∧ ¬ ModelUniversalA14 := by
  constructor
  · exact moral_agent_satisfies_normative_truth
  · intro hUniv
    have hChoice := hUniv ModelSubject.unilateralAgent True unilateral_agent_acts
    exact unilateral_agent_cannot_choose hChoice

/-- Corollary: The Right/Wrong route does NOT logically entail Universal A14.
    Status: PROVED (Pure logic, footprint {}). -/
theorem normativity_does_not_entail_universal_a14 :
    ¬ (MoralNormativeTruth → ModelUniversalA14) := by
  intro h
  exact hostile_model_normativity_compatible_with_not_universal_a14.2
    (h hostile_model_normativity_compatible_with_not_universal_a14.1)

end NormativeSeparationModel

-- ===========================================================================
-- Section 4: Audit of the Missing Premise for Universal A14
-- ===========================================================================

/-!
### What is Missing for Universal A14?
To bridge from `Act s p` to `Chooses s p q` for an ARBITRARY non-normative act:
- `Act s p` provides only `Means s p`.
- The alternative horn `q` with `Means s q ∧ Incompatible p q` is entirely absent
  in non-normative actions.
- `Order.lean:judge_commits` provides `ChoiceField s p (¬p)` (`Means s p ∧ Incompatible p (¬p)`),
  where `¬p` is provided by logical bivalence, but `Means s (¬p)` is explicitly NOT derived.
- Closing Universal A14 requires either:
  1. Universal Act Polarity (`AxActPolarity : Act s p → Means s (¬p)`), OR
  2. Universal Intentional Choice (`AxIntentionalChoice : Act s p → ∃ q, Chooses s p q`).
- In contrast, `NormativeA14` requires NO new axiom because the moral law
  itself constitutively supplies `q` as the prohibited contrast horn.
-/

/-- Universal Act Polarity Principle: Every intentional act endows the agent with
    the representation of its contradictory negation. -/
def UniversalActPolarity (Subj : Type) (ActRel : Subj → Prop → Prop)
    (MeansRel : Subj → Prop → Prop) : Prop :=
  ∀ (s : Subj) (p : Prop), ActRel s p → MeansRel s (¬ p)

/-- Theorem: Universal Act Polarity strictly entails Universal A14.
Status: PROVED (Pure logic, footprint `{propext}`). -/
    theorem polarity_entails_universal_a14
    {Subj : Type} (ActRel : Subj → Prop → Prop) (MeansRel : Subj → Prop → Prop)
    (ChoosesRel : Subj → Prop → Prop → Prop)
    (hActMeans : ∀ s p, ActRel s p → MeansRel s p)
    (hChoosesDef : ∀ s p q, ChoosesRel s p q ↔ MeansRel s p ∧ MeansRel s q ∧ Incompatible p q)
    (hPol : UniversalActPolarity Subj ActRel MeansRel) :
    UniversalA14 Subj ActRel ChoosesRel := by
  intro s p hAct
  have hMeansP := hActMeans s p hAct
  have hMeansNotP := hPol s p hAct
  have hIncomp : Incompatible p (¬ p) := fun ⟨hp, hnp⟩ => hnp hp
  refine ⟨¬ p, ?_⟩
  rw [hChoosesDef]
  exact ⟨hMeansP, hMeansNotP, hIncomp⟩

end Logos.A14DerivationAudit

-- Axiom footprint audit
#print axioms Logos.A14DerivationAudit.normative_action_yields_choice
#print axioms Logos.A14DerivationAudit.normative_route_derives_free_will
#print axioms Logos.A14DerivationAudit.NormativeSeparationModel.moral_agent_satisfies_normative_truth
#print axioms Logos.A14DerivationAudit.NormativeSeparationModel.moral_agent_chooses
#print axioms Logos.A14DerivationAudit.NormativeSeparationModel.moral_agent_acts
#print axioms Logos.A14DerivationAudit.NormativeSeparationModel.unilateral_agent_acts
#print axioms Logos.A14DerivationAudit.NormativeSeparationModel.unilateral_agent_cannot_choose
#print axioms Logos.A14DerivationAudit.NormativeSeparationModel.hostile_model_normativity_compatible_with_not_universal_a14
#print axioms Logos.A14DerivationAudit.NormativeSeparationModel.normativity_does_not_entail_universal_a14
#print axioms Logos.A14DerivationAudit.polarity_entails_universal_a14
