/-
# Logos.DirectNormativeRetorsion — Direct Diagonal Retorsion of Normative Right

This module establishes the direct transcendental retorsion of normative Right:
  A proposition cannot be presented as normatively correct while denying the existence
  of normative correctness itself.

Key Architecture:
1. Pure Diagonal Retorsion:
   - `NormativeRightExists := ∃ s p, ClaimsCorrect s p ∧ Logos.Order.Correct s p`
   - `NoRight := ¬ NormativeRightExists`
   - Theorem: `ClaimsCorrect s NoRight ∧ NoRight → False`.
     Any agent claiming NoRight as correct while NoRight is true produces an immediate,
     constructive logical contradiction. Zero substantive axioms!
2. Hostile Models A, B, and C:
   - Model A (Mere noise): `Act s NoRight` without claiming correctness remains consistent.
   - Model B (Non-normative representation): `Means s NoRight` without acting remains consistent.
   - Model C (Normative denial): Formally refuted in the kernel.
3. Free Will (composition):
   - The normative route `NormativeRightExists → GenuineNormativity → Chooses → FreeWill`
     is carried by the C140/C141 chain in
     `Logos.NormativeOrder.claims_normative_correctness_derives_free_will` and
     `Logos.RetorsiveNormativity.normative_retorsion_derives_free_will`
     (footprints `{Initiates, Means, State, Subject, CL}`, zero substantive axioms).
   - The former `ConstitutiveNormativeBridge` structure was retired (2026-09-23): never
     instantiated, never on any ledger route.
-/

import Logos.Agency
import Logos.Order
import Logos.RetorsiveNormativity

set_option linter.unusedVariables false

namespace Logos.DirectNormativeRetorsion

open Logos.Agency (Subject Means Act)
open Logos.RetorsiveNormativity (ClaimsCorrect)

-- ===========================================================================
-- Section 1: The Diagonal Retorsion of Normative Right
-- ===========================================================================

/-- NormativeRightExists: The existential realization of a normative judgment that is
    both presented as correct by an agent and is factively correct (`Act s p ∧ p`).
    Classification: DEFINITIONAL. -/
def NormativeRightExists : Prop :=
  ∃ (s : Subject) (p : Prop), ClaimsCorrect s p ∧ Logos.Order.Correct s p

/-- NoRight: The universal skeptical thesis asserting that no genuine normative
    correctness judgment exists.
    Classification: DEFINITIONAL. -/
def NoRight : Prop :=
  ¬ NormativeRightExists

/-- The Fundamental Diagonal Retorsion Theorem:
    Claiming NoRight as correct while NoRight is true produces a strict, constructive contradiction.
    Footprint: `{Initiates, Means, State, Subject}` (zero substantive axioms).
    Classification: LOGICAL derivation from foundational definitions. -/
theorem claims_correct_no_right_self_refuting
    (s : Subject) (hClaim : ClaimsCorrect s NoRight) (hTrue : NoRight) : False := by
  have hAct : Act s NoRight := hClaim.1
  have hCorrect : Logos.Order.Correct s NoRight := ⟨hAct, hTrue⟩
  have hEx : NormativeRightExists := ⟨s, NoRight, hClaim, hCorrect⟩
  exact hTrue hEx

/-- Unassertability Theorem: No agent can claim NoRight as correct if NoRight is true.
    Footprint: `{Initiates, Means, State, Subject}` (zero substantive axioms).
    Classification: LOGICAL. -/
theorem cannot_claim_correct_no_right_and_true :
    ¬ ∃ s : Subject, ClaimsCorrect s NoRight ∧ NoRight := by
  intro ⟨s, hClaim, hTrue⟩
  exact claims_correct_no_right_self_refuting s hClaim hTrue

/-- Performative Derivation Theorem: If any agent actually performs a normative correctness
    claim on NoRight, the thesis NoRight is strictly false.
    Footprint: `{Initiates, Means, State, Subject}` (zero substantive axioms).
    Classification: LOGICAL. -/
theorem performative_normative_denial_establishes_normative_right
    (hDenial : ∃ s : Subject, ClaimsCorrect s NoRight) :
    ¬ NoRight := by
  intro hTrue
  obtain ⟨s, hClaim⟩ := hDenial
  exact claims_correct_no_right_self_refuting s hClaim hTrue

-- ===========================================================================
-- Section 2: Hostile Models A, B, and C
-- ===========================================================================

/-!
### Model-Theoretic Analysis:
We define an interpreted agency signature `RetorsionSig` to prove the satisfiability
and independence of Models A and B, and the kernel impossibility of Model C.
-/

structure RetorsionSig where
  Subject : Type
  Means : Subject → Prop → Prop
  Act : Subject → Prop → Prop

def SigCorrect (sig : RetorsionSig) (s : sig.Subject) (p : Prop) : Prop :=
  sig.Act s p ∧ p

def SigClaimsCorrect (sig : RetorsionSig) (s : sig.Subject) (p : Prop) : Prop :=
  sig.Act s p ∧ sig.Means s (SigCorrect sig s p)

def SigNormativeRightExists (sig : RetorsionSig) : Prop :=
  ∃ (s : sig.Subject) (p : Prop), SigClaimsCorrect sig s p ∧ SigCorrect sig s p

def SigNoRight (sig : RetorsionSig) : Prop :=
  ¬ SigNormativeRightExists sig

/-- Model A (Mere Noise): An agent acts on every proposition (including `SigNoRight`),
    but has an empty `Means` relation (`fun _ _ => False`).
    Therefore, no correctness claim is ever made, and `SigNoRight` is true. -/
def ModelA_MereNoise : RetorsionSig where
  Subject := Unit
  Means := fun _ _ => False
  Act := fun _ _ => True

/-- Theorem: In Model A, `SigNoRight` is factively true.
    Footprint: {} (pure logic). -/
theorem model_a_no_right_is_true :
    SigNoRight ModelA_MereNoise := by
  dsimp [SigNoRight, SigNormativeRightExists, SigClaimsCorrect]
  intro ⟨s, p, ⟨_, hMeans⟩, _⟩
  exact hMeans

/-- Theorem (Model A Satisfiability): The subject emits `SigNoRight` as mere noise
    without claiming correctness, and `SigNoRight` is factively true.
    Classification: COUNTERMODEL / SATISFIABILITY. Footprint: {} (pure logic). -/
theorem model_a_satisfiability :
    ∃ (sig : RetorsionSig) (s : sig.Subject),
      sig.Act s (SigNoRight sig) ∧ SigNoRight sig ∧ ¬ sig.Means s (SigCorrect sig s (SigNoRight sig)) :=
  ⟨ModelA_MereNoise, (), trivial, model_a_no_right_is_true, fun h => h⟩

/-- Model B (Non-Normative Representation): An agent entertains all propositions,
    but performs no acts (`fun _ _ => False`).
    Therefore, no act is ever performed, and `SigNoRight` is true. -/
def ModelB_NonNormativeRepresentation : RetorsionSig where
  Subject := Unit
  Means := fun _ _ => True
  Act := fun _ _ => False

/-- Theorem: In Model B, `SigNoRight` is factively true.
    Footprint: {} (pure logic). -/
theorem model_b_no_right_is_true :
    SigNoRight ModelB_NonNormativeRepresentation := by
  dsimp [SigNoRight, SigNormativeRightExists, SigCorrect]
  intro ⟨s, p, _, ⟨hAct, _⟩⟩
  exact hAct

/-- Theorem (Model B Satisfiability): The subject meaningfully entertains `SigNoRight`
    without performing an act, and `SigNoRight` is factively true.
    Classification: COUNTERMODEL / SATISFIABILITY. Footprint: {} (pure logic). -/
theorem model_b_satisfiability :
    ∃ (sig : RetorsionSig) (s : sig.Subject),
      sig.Means s (SigNoRight sig) ∧ SigNoRight sig ∧ ¬ sig.Act s (SigNoRight sig) :=
  ⟨ModelB_NonNormativeRepresentation, (), trivial, model_b_no_right_is_true, fun h => h⟩

/-- Model C Refutation (Model-Theoretic Impossibility):
    No interpreted signature can satisfy `SigClaimsCorrect s (SigNoRight sig)` and `SigNoRight sig`.
    Classification: LOGICAL IMPOSSIBILITY. Footprint: {} (pure logic). -/
theorem sig_model_c_normative_denial_is_impossible
    (sig : RetorsionSig) (s : sig.Subject) :
    ¬ (SigClaimsCorrect sig s (SigNoRight sig) ∧ SigNoRight sig) := by
  intro ⟨hClaim, hTrue⟩
  have hCorr : SigCorrect sig s (SigNoRight sig) := ⟨hClaim.1, hTrue⟩
  have hEx : SigNormativeRightExists sig := ⟨s, SigNoRight sig, hClaim, hCorr⟩
  exact hTrue hEx

/-- A normative denial cannot be both claimed correct and true.
    Classification: LOGICAL COROLLARY. Footprint: {} (pure logic). -/
theorem no_correct_claim_of_no_right_can_be_true
    (sig : RetorsionSig) (s : sig.Subject) :
    SigClaimsCorrect sig s (SigNoRight sig) → ¬ SigNoRight sig := by
  intro hClaim hTrue
  exact sig_model_c_normative_denial_is_impossible sig s ⟨hClaim, hTrue⟩

/-- Mere Utterance in Ambient Signature: An agent acts on p without claiming correctness. -/
def MereUtterance (s : Subject) (p : Prop) : Prop :=
  Act s p ∧ ¬ Means s (Logos.Order.Correct s p)

/-- Model A Avoidance Lemma: Mere utterance does not satisfy ClaimsCorrect.
    Footprint: `{Initiates, Means, State, Subject}`. -/
theorem model_a_mere_utterance_avoids_claims_correct
    (s : Subject) (hUtter : MereUtterance s NoRight) :
    ¬ ClaimsCorrect s NoRight := by
  intro hClaim
  exact hUtter.2 hClaim.2

/-- Model B Avoidance Lemma: Meaning NoRight without acting on it does not instantiate ClaimsCorrect.
    Footprint: `{Initiates, Means, State, Subject}`. -/
theorem model_b_mere_meaning_avoids_claims_correct
    (s : Subject) (hMeans : Means s NoRight) (hNotAct : ¬ Act s NoRight) :
    ¬ ClaimsCorrect s NoRight := by
  intro hClaim
  exact hNotAct hClaim.1

/-- Model C Ambient Refutation: Model C is impossible in the ambient signature.
    Footprint: `{Initiates, Means, State, Subject}`. -/
theorem model_c_normative_denial_is_impossible :
    ¬ ∃ s : Subject, ClaimsCorrect s NoRight ∧ NoRight :=
  cannot_claim_correct_no_right_and_true

-- ===========================================================================
-- Section 3: (retired 2026-09-23 — the former `ConstitutiveNormativeBridge`
--            structure and its two theorems were dead code: never instantiated,
--            never on a ledger route. The free-will composition is carried by
--            C140/C141, see module docstring, item 3.)
-- ===========================================================================

end Logos.DirectNormativeRetorsion

-- Kernel footprint audit
#print axioms Logos.DirectNormativeRetorsion.NormativeRightExists
#print axioms Logos.DirectNormativeRetorsion.NoRight
#print axioms Logos.DirectNormativeRetorsion.claims_correct_no_right_self_refuting
#print axioms Logos.DirectNormativeRetorsion.cannot_claim_correct_no_right_and_true
#print axioms Logos.DirectNormativeRetorsion.performative_normative_denial_establishes_normative_right
#print axioms Logos.DirectNormativeRetorsion.model_a_no_right_is_true
#print axioms Logos.DirectNormativeRetorsion.model_a_satisfiability
#print axioms Logos.DirectNormativeRetorsion.model_b_no_right_is_true
#print axioms Logos.DirectNormativeRetorsion.model_b_satisfiability
#print axioms Logos.DirectNormativeRetorsion.sig_model_c_normative_denial_is_impossible
#print axioms Logos.DirectNormativeRetorsion.no_correct_claim_of_no_right_can_be_true
#print axioms Logos.DirectNormativeRetorsion.model_a_mere_utterance_avoids_claims_correct
#print axioms Logos.DirectNormativeRetorsion.model_b_mere_meaning_avoids_claims_correct
#print axioms Logos.DirectNormativeRetorsion.model_c_normative_denial_is_impossible
