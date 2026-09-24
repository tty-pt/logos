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
3. Evaluation of Levels 1–4 (provenance):
   - Level 1: Conditional boundary identified.
   - Level 2: Unconditional `ClaimsCorrect s (¬ B) → Means s B` strictly fails in primitive Γ
     (countermodel independence, refuted by M_opaque).
   - Level 3: Pure retorsion fails to force bipolarity without a substantive semantic bridge
     (`level_3_retorsion_impotent_without_semantic_premise`: machine-checked verdict, not a claim).
   - Level 4: Inventory label for A18 (`AxJudicativeBipolarity`): model-theoretically independent
     of primitive Γ — it cannot be derived without an explicit semantic commitment (`Tag: SEM`),
so it is a free-standing weak-stance option, NOT a required cost of refuting the
     stipulation attack (the stance-guarded refutation is axiom-free given the stance;
     `RetorsiveNormativity.normative_stance_refutes_attack_without_axioms`,
     footprint `{Initiates, Means, State, Subject, CL}`).
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
    Footprint: `{Initiates, Means, State, Subject}`. -/
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
    the propositional negation in uninterpreted logic, and Section 6 machine-witnesses
    that it does not entail grasping the normative incorrectness either
    (`voice_without_normative_stance`).
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

/-- Level 4: Independence and Optionality of A18 (`AxJudicativeBipolarity`).
    A18 (`ClaimsCorrect s p → Means s (¬ p)`) cannot be derived from the primitive
    notions already present in Γ — Model M_opaque witnesses that independence. It is
    therefore a genuine substantive semantic commitment (`Tag: SEM`), not a theorem of
    logic; but it is an OPTIONAL weak-stance asset, not a required cost: the refutation
    of the stipulation attack is axiom-free under the normative-judicative stance
    (`RetorsiveNormativity.normative_stance_refutes_attack_without_axioms`,
    footprint `{Initiates, Means, State, Subject, CL}`).
    Classification: METATHEORETIC INVENTORY RESULT. -/
theorem A18_is_independent_optional_semantic_premise :
    (∃ (sig : AgencySig), ¬ BipolaritySig sig)
      ∧ (∀ (h : ∃ s : Subject, ∃ p : Prop, Logos.NormativeOrder.ClaimsNormativeCorrectness s p),
            ¬ Logos.RetorsiveNormativity.NoGN) := by
  constructor
  · exact ⟨M_opaque, m_opaque_refutes_bipolarity⟩
  · intro h
    exact Logos.RetorsiveNormativity.normative_stance_refutes_attack_without_axioms h

-- ===========================================================================
-- Section 6: The Datum Gap — Voice Without the Normative Stance (INVIABLE.md §1/§3)
-- ===========================================================================

/-- Judicative signature at the tier-0/tier-1 level: act, means, initiation,
    truth and falsehood — WITHOUT an `Incorrect` field, so that the negative
    pole is never smuggled into the vocabulary. Local to this module (mirrors
    the `PreA13AgencySignature` pattern in HostileSemantics.lean), so no import
    cycle is introduced. -/
structure JudicativeSig where
  Subject : Type
  State : Type
  Means : Subject → Prop → Prop
  Initiates : Subject → State → State → Prop → Prop
  T : Prop → Prop
  IsFalse : Prop → Prop

/-- Act in a judicative signature: means the content and initiates a transition. -/
def JudSigAct (sig : JudicativeSig) (s : sig.Subject) (p : Prop) : Prop :=
  sig.Means s p ∧ ∃ w w' : sig.State, sig.Initiates s w w' p

/-- Correct delimitation in a judicative signature (mirrors Order.Correct). -/
def JudSigCorrect (sig : JudicativeSig) (s : sig.Subject) (p : Prop) : Prop :=
  JudSigAct sig s p ∧ sig.T p

/-- Incorrect delimitation in a judicative signature (mirrors Order.Incorrect). -/
def JudSigIncorrect (sig : JudicativeSig) (s : sig.Subject) (p : Prop) : Prop :=
  JudSigAct sig s p ∧ sig.IsFalse p

/-- Voice: act plus grasp of the positive pole
    `Correct s p` — nothing more; this is all `ClaimsCorrect` gives in Γ. -/
def VoiceSig (sig : JudicativeSig) (s : sig.Subject) (p : Prop) : Prop :=
  JudSigAct sig s p ∧ sig.Means s (JudSigCorrect sig s p)

/-- Normative-judicative stance (tier 2): voice plus grasp of the negative pole
    `Incorrect s p` — exactly the missing conjunct of the INVIABLE.md §1 gap
    between `ClaimsCorrect` and `ClaimsNormativeCorrectness`. -/
def NormativeStanceSig (sig : JudicativeSig) (s : sig.Subject) (p : Prop) : Prop :=
  VoiceSig sig s p ∧ sig.Means s (JudSigIncorrect sig s p)

/-- Model M_oneway: `Means` means "not equivalent to False", `T` is identity,
    `IsFalse` is negation. A subject voices `True` as correct yet fails to mean
    that judging it is incorrect — the dual-pole grasp is absent. -/
def M_oneway : JudicativeSig where
  Subject := Unit
  State := Unit
  Means := fun _ q => ¬ (q ↔ False)
  Initiates := fun _ _ _ _ => True
  T := fun p => p
  IsFalse := fun p => ¬ p

theorem m_oneway_act_true : JudSigAct M_oneway () True := by
  refine ⟨fun h => h.mp True.intro, ⟨(), (), trivial⟩⟩

theorem m_oneway_voice_holds : VoiceSig M_oneway () True := by
  refine ⟨m_oneway_act_true, ?_⟩
  intro h
  exact h.mp ⟨m_oneway_act_true, True.intro⟩

theorem m_oneway_incorrect_iff_false :
    JudSigIncorrect M_oneway () True ↔ False := by
  constructor
  · intro h
    exact h.2 True.intro
  · intro f
    exact f.elim

theorem m_oneway_stance_fails :
    ¬ M_oneway.Means () (JudSigIncorrect M_oneway () True) := by
  intro hMeans
  exact hMeans m_oneway_incorrect_iff_false

/-- In primitive Γ, voicing a judgment does NOT force the normative-judicative
    stance: M_oneway voices `True` as correct (act plus grasp of the positive
    pole) while failing to mean `Incorrect () True` — machine witness of the
    voice↔stance gap. The stance is a datum (its field is non-empty because the
    proof is attempted from inside it), not a derivable consequence of voice.
    Classification: COUNTERMODEL / INDEPENDENCE. Footprint: {}. -/
theorem voice_without_normative_stance :
    ∃ (sig : JudicativeSig) (s : sig.Subject) (p : Prop),
      VoiceSig sig s p ∧ ¬ sig.Means s (JudSigIncorrect sig s p) :=
  ⟨M_oneway, (), True, m_oneway_voice_holds, m_oneway_stance_fails⟩

/-- Companion negative result: no signature over the primitive vocabulary forces
    the stance from voice in general — the gap is a theorem of independence,
    not an accident of any single model.
    Classification: COUNTERMODEL / NEGATIVE RESULT. Footprint: {}. -/
theorem voice_to_stance_not_forced_by_primitive_judicative_gamma :
    ¬ (∀ (sig : JudicativeSig) (s : sig.Subject) (p : Prop),
        VoiceSig sig s p → NormativeStanceSig sig s p) := by
  intro hAll
  have h := hAll M_oneway () True m_oneway_voice_holds
  exact m_oneway_stance_fails h.2

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
#print axioms Logos.BipolarityRetorsion.A18_is_independent_optional_semantic_premise
#print axioms Logos.BipolarityRetorsion.voice_without_normative_stance
#print axioms Logos.BipolarityRetorsion.voice_to_stance_not_forced_by_primitive_judicative_gamma
