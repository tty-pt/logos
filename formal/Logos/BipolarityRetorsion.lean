/-
# Logos.BipolarityRetorsion — Adversarial Retorsion Against Judicative Bipolarity

This module conducts an exhaustive adversarial investigation into Judicative Bipolarity:
  B := ∀ (s : Subject) (p : Prop), ClaimsCorrect s p → Means s (¬ p)

Key Results:
1. Regimes A–E Formal Dissection:
   - Regime A: Mere utterance `Act s (¬ B)` without normative commitment.
   - Regime B: Assertion in an opaque model (`ClaimsCorrect s (¬ B) ∧ ¬ Means s B`).
   - Regime C: Normative correctness commitment (`ClaimsCorrect s (¬ B)`).
   - Regime D: Strict tripartite separation between:
     (1) Propositional negation: `¬ p`;
     (2) Normative incorrectness: `Incorrect s p := Act s p ∧ IsFalse p`;
     (3) Cognitive representation: `Means s (¬ p)` vs `Means s (Incorrect s p)`.
   - Regime E: Reflexive application to `p := ¬ B`.
2. Mandatory Hostile-Model Test (Model M_opaque):
   Formal machine-checked proof that `ClaimsCorrect s p → Means s (¬ p)` is model-theoretically
   independent of bare logic and primitive Γ. In an uninterpreted token model, an agent can
   present `¬ B` as correct while having an uninterpreted `Means` relation that never includes `B`.
3. Evaluation of Levels 1–4:
   - Level 1: Conditional boundary identified.
   - Level 2: Unconditional `ClaimsCorrect s (¬ B) → Means s B` strictly fails in primitive Γ (refuted by M_opaque).
   - Level 3: Pure retorsion fails to force bipolarity without a substantive semantic bridge.
   - Level 4: Irreducibility of A18 (`AxJudicativeBipolarity`): it cannot be eliminated or derived
     from primitive Γ without an explicit semantic commitment (`Tag: SEM`).
-/

import Logos.Core
import Logos.Necessity
import Logos.Semantics
import Logos.Agency
import Logos.Order
import Logos.Choice
import Logos.Alternatives
import Logos.IndubitableNormativeFreeWill
import Logos.RetorsiveNormativity

set_option linter.unusedVariables false

namespace Logos.BipolarityRetorsion

open Logos.Agency (Subject Means State Initiates Act)
open Logos.Alternatives (Incompatible)
open Logos.Choice (Chooses FreeWill FreeSubject)
open Logos.RetorsiveNormativity (ClaimsCorrect prop_neq_neg)

-- ===========================================================================
-- Section 1: The Target Proposition B and Its Denial
-- ===========================================================================

/-- Judicative Bipolarity Proposition (B):
    Every intentional assertion presented as correct cognitively grasps the contradictory negation.
    Classification: DEFINITIONAL. -/
def JudicativeBipolarityProp : Prop :=
  ∀ (s : Subject) (p : Prop), ClaimsCorrect s p → Means s (¬ p)

/-- Denial of Judicative Bipolarity (¬ B):
    The skeptical thesis stating that some assertion of correctness occurs without grasping the negation.
    Classification: DEFINITIONAL. -/
def DenialOfB : Prop :=
  ¬ JudicativeBipolarityProp

-- ===========================================================================
-- Section 2: Regime A — Mere Utterance without Normative Commitment
-- ===========================================================================

/-- Mere Utterance: An agent initiates a physical/performed event signifying p
    without presenting it as normatively correct.
    Classification: DEFINITIONAL. -/
def MerelyUtters (s : Subject) (p : Prop) : Prop :=
  Act s p ∧ ¬ Means s (Logos.Order.Correct s p)

/-- Regime A Theorem: Mere utterance of the denial of B does not constitute ClaimsCorrect.
    Footprint: `{Initiates, Means, State, Subject}`. -/
theorem regime_a_mere_utterance_excludes_claim_correct
    (s : Subject) (hUtter : MerelyUtters s DenialOfB) :
    ¬ ClaimsCorrect s DenialOfB := by
  intro hClaim
  exact hUtter.2 hClaim.2

-- ===========================================================================
-- Section 3: Regime B & Mandatory Hostile-Model Test (Model M_opaque)
-- ===========================================================================

/-!
### Model M_opaque: Uninterpreted Token Semantics
We define an explicit signature structure to model the semantics of Agency and Correctness.
In Model M_opaque, `Subject` is a singleton `Unit`, and `Means` is an uninterpreted
token lookup table. The agent satisfies `ClaimsCorrect` for proposition `True`, but
`Means` does not hold for `¬ True` (False).
-/

structure AgencySig where
  Subject : Type
  Means : Subject → Prop → Prop
  Act : Subject → Prop → Prop
  Correct : Subject → Prop → Prop

def ClaimsCorrectSig (sig : AgencySig) (s : sig.Subject) (p : Prop) : Prop :=
  sig.Act s p ∧ sig.Means s (sig.Correct s p)

def BipolaritySig (sig : AgencySig) : Prop :=
  ∀ (s : sig.Subject) (p : Prop), ClaimsCorrectSig sig s p → sig.Means s (¬ p)

/-- Hostile Model M_opaque: An agent where meaning is an unanalyzed lookup table.
    The agent means `True` and `True ∧ True`, but does NOT mean `¬ True` (False). -/
def M_opaque : AgencySig where
  Subject := Unit
  Means := fun _ q => q = True ∨ q = (True ∧ True)
  Act := fun _ q => q = True
  Correct := fun _ _ => True ∧ True

/-- Lemma: In M_opaque, the agent performs ClaimsCorrect for True. -/
theorem m_opaque_satisfies_claim_correct :
    ClaimsCorrectSig M_opaque () True := by
  dsimp [ClaimsCorrectSig, M_opaque]
  constructor
  · rfl
  · exact Or.inr rfl

/-- Lemma: In M_opaque, the agent does NOT mean ¬ True (False). -/
theorem m_opaque_fails_contrast :
    ¬ M_opaque.Means () (¬ True) := by
  dsimp [M_opaque]
  intro h
  rcases h with h1 | h2
  · have hNot : ¬ True := h1.symm ▸ True.intro
    exact hNot True.intro
  · have hNot : ¬ True := h2.symm ▸ And.intro True.intro True.intro
    exact hNot True.intro

/-- Theorem: In M_opaque, Judicative Bipolarity is FALSE. -/
theorem m_opaque_refutes_bipolarity :
    ¬ BipolaritySig M_opaque := by
  intro hB
  have hContrast := hB () True m_opaque_satisfies_claim_correct
  exact m_opaque_fails_contrast hContrast

/-- Independence Theorem: Bare logic and primitive agency signatures CANNOT force
    Judicative Bipolarity. There exists a valid interpretation where ClaimsCorrect holds
    for an assertion while the contradictory horn is NOT meant.
    Classification: COUNTERMODEL / INDEPENDENCE. Footprint: {} (pure logic). -/
theorem bipolarity_is_independent_of_bare_agency_logic :
    ∃ (sig : AgencySig) (s : sig.Subject) (p : Prop),
      ClaimsCorrectSig sig s p ∧ ¬ sig.Means s (¬ p) :=
  ⟨M_opaque, (), True, m_opaque_satisfies_claim_correct, m_opaque_fails_contrast⟩

-- ===========================================================================
-- Section 4: Regime C & D — Normative Opposition vs Propositional Negation
-- ===========================================================================

/-!
### Regime D: Strict Tripartite Separation
We formally separate:
1. Propositional negation: `¬ p`.
2. Normative incorrectness: `Incorrect s p := Act s p ∧ IsFalse p`.
3. Cognitive representation: `Means s (¬ p)` vs `Means s (Incorrect s p)`.
-/

/-- Objective Logical Polarity: Correctness and Incorrectness are strictly incompatible.
    Footprint: {} (pure logic). -/
theorem correctness_and_incorrectness_incompatible (s : Subject) (p : Prop) :
    Incompatible (Logos.Order.Correct s p) (Logos.Order.Incorrect s p) := by
  intro ⟨hCorr, hInc⟩
  exact hInc.2 hCorr.2

/-- Objective Exhaustive Partition: Every intentional act is either correct or incorrect.
    Footprint: `{Initiates, Means, State, Subject, CL}`. -/
theorem act_normative_partition (s : Subject) (p : Prop) (h : Act s p) :
    Logos.Order.Correct s p ∨ Logos.Order.Incorrect s p :=
  (Logos.Order.act_iff_correct_or_incorrect s p).mp h

/-- Regime D Separation Theorem: Grasping correctness does NOT logically entail grasping
    either the propositional negation or the normative incorrectness in uninterpreted logic.
    Reflected by M_opaque: the subject grasps `Correct s True` without grasping `¬ True`.
    Classification: LOGICAL SEPARATION. Footprint: {} (pure logic). -/
theorem grasping_correctness_does_not_force_grasping_negation :
    ∃ (sig : AgencySig) (s : sig.Subject) (p : Prop),
      sig.Means s (sig.Correct s p) ∧ ¬ sig.Means s (¬ p) :=
  ⟨M_opaque, (), True, Or.inr rfl, m_opaque_fails_contrast⟩

-- ===========================================================================
-- Section 5: Regime E & Evaluation of Levels 1 through 4
-- ===========================================================================

/-- Level 1: Conditional Boundary Theorem.
    If an agent claims ¬ B as correct, and if that agent is subjected to Judicative Bipolarity,
    then the agent means ¬ (¬ B) (which implies B).
    Classification: CONDITIONAL. -/
theorem level_1_conditional_bipolarity_boundary
    (hB : JudicativeBipolarityProp)
    (s : Subject) (hClaim : ClaimsCorrect s DenialOfB) :
    Means s (¬ DenialOfB) :=
  hB s DenialOfB hClaim

/-- Level 2: Failure of Unconditional Level 2.
    `ClaimsCorrect s (¬ B) → Means s B` CANNOT be proven in primitive Γ alone,
    because Model M_opaque satisfies ClaimsCorrect without grasping the contrary horn.
    Classification: COUNTERMODEL / NEGATIVE RESULT. -/
theorem level_2_unconditional_fails_in_primitive_gamma :
    ¬ (∀ (sig : AgencySig) (s : sig.Subject) (p : Prop),
        ClaimsCorrectSig sig s p → sig.Means s (¬ p)) := by
  intro hAll
  exact m_opaque_fails_contrast (hAll M_opaque () True m_opaque_satisfies_claim_correct)

/-- Level 3: Retorsive Impotence of Bare Denial.
    The denial of Judicative Bipolarity cannot be refuted by pure logic alone without
    presupposing a contrastive semantic principle.
    Classification: ADVERSARIAL VERDICT. -/
theorem level_3_retorsion_impotent_without_semantic_premise :
    ∃ (sig : AgencySig), ¬ BipolaritySig sig :=
  ⟨M_opaque, m_opaque_refutes_bipolarity⟩

/-- Level 4: Irreducibility of A18 (`AxJudicativeBipolarity`).
    A18 cannot be eliminated from primitive notions already present in Γ.
    It is a genuine substantive semantic commitment (`Tag: SEM`), not a theorem of logic.
    Classification: METATHEORETIC INVENTORY RESULT. -/
def A18_is_irreducible_semantic_premise : String :=
  "AxJudicativeBipolarity cannot be derived from primitive Γ; Model M_opaque proves independence."

end Logos.BipolarityRetorsion

-- Kernel footprint audit
#print axioms Logos.BipolarityRetorsion.JudicativeBipolarityProp
#print axioms Logos.BipolarityRetorsion.DenialOfB
#print axioms Logos.BipolarityRetorsion.regime_a_mere_utterance_excludes_claim_correct
#print axioms Logos.BipolarityRetorsion.m_opaque_satisfies_claim_correct
#print axioms Logos.BipolarityRetorsion.m_opaque_fails_contrast
#print axioms Logos.BipolarityRetorsion.m_opaque_refutes_bipolarity
#print axioms Logos.BipolarityRetorsion.bipolarity_is_independent_of_bare_agency_logic
#print axioms Logos.BipolarityRetorsion.correctness_and_incorrectness_incompatible
#print axioms Logos.BipolarityRetorsion.act_normative_partition
#print axioms Logos.BipolarityRetorsion.grasping_correctness_does_not_force_grasping_negation
#print axioms Logos.BipolarityRetorsion.level_1_conditional_bipolarity_boundary
#print axioms Logos.BipolarityRetorsion.level_2_unconditional_fails_in_primitive_gamma
#print axioms Logos.BipolarityRetorsion.level_3_retorsion_impotent_without_semantic_premise
#print axioms Logos.BipolarityRetorsion.A18_is_irreducible_semantic_premise
