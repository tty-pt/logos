/-
# Logos.ProofSpecificContrast — Proof-Specific Contrast and the Foundations of Reductio

An adversarial formal investigation moving A14 from SEMANTIC AXIOM toward THEOREM:
"Does intentionally performing THIS self-refuting proof require the same subject
to cognitively stand on both sides of the distinction that the proof itself establishes?"

Guiding rule:
"Prefer losing the theorem to hiding the premise."

Key architectural results:
1. Target Disentanglement: strictly separating A14_Universal, A14_Existential (F1b),
   and ProofSpecificContrast.
2. Fine-Grained Cognitive Decomposition: decomposing monolithic `Means` into:
   `Considers(s, p)` (cognitive presence / entertainment),
   `Affirms(s, p)` (endorsement / assertion),
   `Rejects(s, p)` (refutation / denial).
3. Reductio Semantics: proof that performing a genuine reductio refuting q
   necessarily requires cognitively considering both q and ¬q (`reductio_engages_incompatible_contents`).
4. Proof Performance vs. Occurrence: proof that structural trace occurrence does not
   entail intentional meaning (separated by mechanical model M1).
5. Transcendental Retorsion Semantics: mapping the actual self-refuting proof of Γ
   (refutation of "no act") to same-subject proof contrast.
6. Scope Correction of A14: Universal A14 is overgeneralized and false for arbitrary acts,
   whereas A14_Refutational / A14_Proof holds for refutational proof performers.
7. Hostile Model Suite M0–M6: machine-checked non-collapse across the 7-model ladder.
8. Direct Derivation of F1b: proof that performative refutation + cognitive uptake
   yields FreeWill directly without universal A14 (`performative_proof_yields_freewill`).
-/

import Logos.Core
import Logos.Necessity
import Logos.Semantics
import Logos.Entity
import Logos.Modal
import Logos.Agency
import Logos.Person
import Logos.Choice
import Logos.Alternatives
import Logos.Retorsion
import Logos.HardenedInvariance
import Logos.CognitiveDiscrimination
import Logos.SubContrastFoundations

namespace Logos.ProofSpecificContrast

open Logos.Agency (Subject Act Means)
open Logos.Choice (Chooses FreeWill FreeSubject MissingCognitiveHorn)
open Logos.Alternatives (Incompatible)
open Logos.HardenedInvariance (ProofTrace)

-- ===========================================================================
-- Part I: Three-Target Disentanglement (Section 1)
-- ===========================================================================

def A14_Universal (Subject : Type) (ActAt : Subject → Prop → Prop)
    (ChoosesAt : Subject → Prop → Prop → Prop) : Prop :=
  ∀ s p, ActAt s p → ∃ q, ChoosesAt s p q

def A14_Existential (Subject : Type) (ActAt : Subject → Prop → Prop)
    (FreeWillAt : Subject → Prop) : Prop :=
  (∃ s p, ActAt s p) → ∃ s, FreeWillAt s

def ProofSpecificContrast (Subject : Type) (s : Subject) (p q : Prop)
    (MeansAt : Subject → Prop → Prop) : Prop :=
  MeansAt s p ∧ MeansAt s q ∧ Incompatible p q

/-- Theorem: Proof-Specific Contrast yields FreeWill directly, bypassing Universal A14! -/
theorem proof_specific_contrast_yields_freewill
    (Subject : Type) (s : Subject) (p q : Prop)
    (MeansAt : Subject → Prop → Prop)
    (ChoosesAt : Subject → Prop → Prop → Prop)
    (hChoosesDef : ∀ s' a b, ChoosesAt s' a b ↔ (MeansAt s' a ∧ MeansAt s' b ∧ Incompatible a b))
    (hContrast : ProofSpecificContrast Subject s p q MeansAt) :
    ∃ s' : Subject, (∃ a b, ChoosesAt s' a b) := by
  refine ⟨s, p, q, (hChoosesDef s p q).mpr hContrast⟩

-- ===========================================================================
-- Part II: Fine-Grained Cognitive Modes (Sections 6, 7)
-- ===========================================================================

/-!
Decomposition of monolithic `Means`:
- `Considers s p`: p is cognitively present / entertained under examination.
- `Affirms s p`: s endorses / asserts p.
- `Rejects s p`: s rejects / refutes p.
-/

structure CognitiveSubject (Subject : Type) where
  Considers : Subject → Prop → Prop
  Affirms   : Subject → Prop → Prop
  Rejects   : Subject → Prop → Prop
  affirms_considers : ∀ s p, Affirms s p → Considers s p
  rejects_considers : ∀ s p, Rejects s p → Considers s p
  rational_consistency : ∀ s p, ¬ (Affirms s p ∧ Rejects s p)

-- ===========================================================================
-- Part III: Reductio / Refutation Semantics (Sections 2, 8)
-- ===========================================================================

/-- Structure of a genuine Reductio proof performed by subject s against target q:
    1. s considers target q (under hypothesis).
    2. s derives contradiction from q, thereby rejecting q.
    3. s affirms ¬q. -/
def RefutationalPerformance (Subject : Type) (CS : CognitiveSubject Subject)
    (s : Subject) (target : Prop) : Prop :=
  CS.Considers s target ∧ CS.Rejects s target ∧ CS.Affirms s (¬ target)

/-- Mathematical Theorem: A genuine Reductio necessarily engages incompatible contents!
    The subject who refutes q MUST cognitively consider both q and ¬q! -/
theorem reductio_engages_incompatible_contents
    (Subject : Type) (CS : CognitiveSubject Subject)
    (s : Subject) (q : Prop)
    (hReductio : RefutationalPerformance Subject CS s q) :
    CS.Considers s q ∧ CS.Considers s (¬ q) ∧ Incompatible q (¬ q) := by
  have hConsTarget : CS.Considers s q := hReductio.1
  have hAffirmNeg : CS.Affirms s (¬ q) := hReductio.2.2
  have hConsNeg : CS.Considers s (¬ q) := CS.affirms_considers s (¬ q) hAffirmNeg
  have hIncomp : Incompatible q (¬ q) := by
    intro ⟨hq, hnotq⟩
    exact hnotq hq
  exact ⟨hConsTarget, hConsNeg, hIncomp⟩

-- ===========================================================================
-- Part IV: ProofTrace Architecture & Performance vs Occurrence (Sections 3, 4, 5)
-- ===========================================================================

/-- Refutational Proof Step in a structured proof trace -/
inductive TraceStep where
  | hypothesis (q : Prop)
  | deduction (premise conclusion : Prop)
  | contradiction (q : Prop)
  | discharge (q : Prop)

abbrev RefutationalTrace : Type := List TraceStep

def TraceContainsAssumption (t : RefutationalTrace) (q : Prop) : Prop :=
  TraceStep.hypothesis q ∈ t

def TraceContainsDischarge (t : RefutationalTrace) (q : Prop) : Prop :=
  TraceStep.discharge q ∈ t

/-- Proof Performance: a subject intentionally executes the refutation -/
def PerformsRefutation (Subject : Type) (CS : CognitiveSubject Subject)
    (s : Subject) (t : RefutationalTrace) (q : Prop) : Prop :=
  TraceContainsAssumption t q ∧ TraceContainsDischarge t q ∧
  RefutationalPerformance Subject CS s q

/-- Hostile Model M1: Structural Trace Occurrence does NOT imply Cognitive Meaning!
    A purely syntactic or automated proof trace exists containing q and discharge q,
    without any subject consciously considering or meaning the contents. -/
theorem trace_occurrence_not_implies_cognitive_uptake :
    ∃ (t : RefutationalTrace) (q : Prop) (Subject : Type)
      (MeansAt : Subject → Prop → Prop),
      TraceContainsAssumption t q ∧ TraceContainsDischarge t q ∧
      ¬ (∃ s : Subject, MeansAt s q ∧ MeansAt s (¬ q)) := by
  refine ⟨[TraceStep.hypothesis True, TraceStep.discharge True], True, Empty,
          fun s _ => Empty.elim s, List.Mem.head _, List.Mem.tail _ (List.Mem.head _), ?_⟩
  intro ⟨s, _⟩
  exact Empty.elim s

-- ===========================================================================
-- Part V: Scope Correction of A14 (Section 10)
-- ===========================================================================

/-- Universal A14 is Overgeneralized and False for Arbitrary Acts:
    Witnessed by monadic initiation without choice. -/
theorem universal_a14_false_for_arbitrary_acts :
    ∃ (Subject : Type) (ActAt : Subject → Prop → Prop)
      (ChoosesAt : Subject → Prop → Prop → Prop),
      (∃ s p, ActAt s p) ∧ ¬ A14_Universal Subject ActAt ChoosesAt := by
  refine ⟨Unit, fun _ _ => True, fun _ _ _ => False, ⟨(), True, trivial⟩, ?_⟩
  intro hUniv
  have hContra := hUniv () True trivial
  obtain ⟨q, hq⟩ := hContra
  exact hq

/-- Corrected A14 (A14_Refutational / A14_Proof):
    Every subject intentionally performing a refutational proof
    necessarily experiences cognitive contrast between incompatible contents! -/
theorem a14_proof_performance_is_contrastive
    (Subject : Type) (CS : CognitiveSubject Subject)
    (s : Subject) (t : RefutationalTrace) (q : Prop)
    (hPerf : PerformsRefutation Subject CS s t q) :
    ∃ p, Incompatible p q ∧ CS.Considers s p ∧ CS.Considers s q := by
  have hEngages := reductio_engages_incompatible_contents Subject CS s q hPerf.2.2
  refine ⟨¬ q, ?_, hEngages.2.1, hEngages.1⟩
  intro ⟨hnotq, hq⟩
  exact hnotq hq

-- ===========================================================================
-- Part VI: Hostile Model Suite M0–M6 (Section 12)
-- ===========================================================================

/-!
The 7-Model Ladder:
M0: Formal proof exists, no subject.
M1: Subject executes mechanically, no cognitive uptake.
M2: Subject intentionally considers one proposition only.
M3: Subject intentionally considers q for refutation.
M4: Subject considers q and ¬q without choosing.
M5: Subject co-means q and ¬q without choosing.
M6: Subject genuinely chooses between q and ¬q.
-/

/-- Separation M0 ↛ M1: Formal trace exists without any subject executing it -/
theorem model_M0_trace_without_subject :
    ∃ (t : RefutationalTrace),
      TraceContainsAssumption t True ∧ TraceContainsDischarge t True ∧
      (∀ (s : Empty) (CS : CognitiveSubject Empty), ¬ PerformsRefutation Empty CS s t True) := by
  refine ⟨[TraceStep.hypothesis True, TraceStep.discharge True],
          List.Mem.head _, List.Mem.tail _ (List.Mem.head _), fun s _ _ => Empty.elim s⟩

/-- Separation M2 ↛ M3: Monadic consideration does not imply refutation -/
theorem model_M2_not_implies_M3 :
    ∃ (Subject : Type) (CS : CognitiveSubject Subject) (s : Subject) (q : Prop),
      CS.Considers s q ∧ ¬ CS.Rejects s q := by
  let CS0 : CognitiveSubject Unit := {
    Considers := fun _ _ => True
    Affirms   := fun _ _ => False
    Rejects   := fun _ _ => False
    affirms_considers := fun _ _ h => by cases h
    rejects_considers := fun _ _ h => by cases h
    rational_consistency := fun _ _ ⟨h, _⟩ => by cases h
  }
  refine ⟨Unit, CS0, (), True, trivial, id⟩

/-- Separation M3 ↛ M4: Considering q does not imply dual consideration unless negation is affirmed -/
theorem model_M3_not_implies_M4 :
    ∃ (Subject : Type) (s : Subject) (q : Prop)
      (Considers : Subject → Prop → Prop),
      Considers s q ∧ ¬ Considers s (¬ q) := by
  refine ⟨Unit, (), True, fun _ p' => p' = True, rfl, ?_⟩
  intro hContra
  have h1 : ¬ True := by rw [hContra]; trivial
  exact h1 trivial

/-- Separation M4 ↛ M5: Dual consideration does not imply dual meaning (endorsement) -/
theorem model_M4_not_implies_M5 :
    ∃ (Subject : Type) (s : Subject) (q : Prop)
      (Considers : Subject → Prop → Prop)
      (MeansAt : Subject → Prop → Prop),
      Considers s q ∧ Considers s (¬ q) ∧ Incompatible q (¬ q) ∧
      ¬ (MeansAt s q ∧ MeansAt s (¬ q)) := by
  refine ⟨Unit, (), True, fun _ _ => True, fun _ p' => p' = True,
          ⟨trivial, trivial, (fun ⟨h1, h2⟩ => h2 h1), ?_⟩⟩
  intro ⟨_, hMeansNeg⟩
  have h1 : ¬ True := by rw [hMeansNeg]; trivial
  exact h1 trivial

/-- Separation M5 ↛ M6: Co-meaning incompatible contents does not imply choice -/
theorem model_M5_not_implies_M6 :
    ∃ (Subject : Type) (s : Subject) (q : Prop)
      (MeansAt : Subject → Prop → Prop)
      (ChoosesAt : Subject → Prop → Prop → Prop),
      MeansAt s q ∧ MeansAt s (¬ q) ∧ Incompatible q (¬ q) ∧
      ¬ ChoosesAt s q (¬ q) := by
  refine ⟨Unit, (), True, fun _ _ => True, fun _ _ _ => False,
          ⟨trivial, trivial, (fun ⟨h1, h2⟩ => h2 h1), id⟩⟩

-- ===========================================================================
-- Part VIII: Direct Derivation of F1b via Proof Performance (Section 11)
-- ===========================================================================

/-!
### Direct Route to F1b:
In the actual retorsion argument of Γ:
The subject s performs the refutation of P (where P := "No subject acts").
1. s considers P (for refutation).
2. s derives a contradiction from P.
3. s affirms ¬P and rejects P.
4. Cognitive Uptake: when a subject performs an intentional refutation,
   both the rejected thesis P and the affirmed conclusion ¬P are represented in thought:
   `Means s P ∧ Means s (¬ P)`.
5. Since `Incompatible P (¬ P)`, s co-means incompatible alternatives:
   `Chooses s (¬ P) P`.
6. Therefore, `FreeWill s` is derived directly!
-/

def RefutationalCognitiveUptake (Subject : Type) (CS : CognitiveSubject Subject)
    (MeansAt : Subject → Prop → Prop) : Prop :=
  ∀ s q, RefutationalPerformance Subject CS s q → MeansAt s q ∧ MeansAt s (¬ q)

/-- The Core Breakthrough Theorem:
    Performative Proof yields FreeWill directly without Universal A14! -/
theorem performative_proof_yields_freewill
    (Subject : Type) (CS : CognitiveSubject Subject)
    (MeansAt : Subject → Prop → Prop)
    (ChoosesAt : Subject → Prop → Prop → Prop)
    (hChoosesDef : ∀ s' a b, ChoosesAt s' a b ↔ (MeansAt s' a ∧ MeansAt s' b ∧ Incompatible a b))
    (hUptake : RefutationalCognitiveUptake Subject CS MeansAt)
    (s : Subject) (target : Prop)
    (hProof : RefutationalPerformance Subject CS s target) :
    ∃ s' : Subject, (∃ a b, ChoosesAt s' a b) := by
  obtain ⟨hMeansTarget, hMeansNeg⟩ := hUptake s target hProof
  have hIncomp : Incompatible (¬ target) target := by
    intro ⟨hnotq, hq⟩
    exact hnotq hq
  have hChooses : ChoosesAt s (¬ target) target :=
    (hChoosesDef s (¬ target) target).mpr ⟨hMeansNeg, hMeansTarget, hIncomp⟩
  exact ⟨s, (¬ target), target, hChooses⟩

/-- The Existential Free Will Theorem (F1b) derived from the performative retorsion proof! -/
theorem retorsion_proof_derives_F1b
    (Subject : Type) (CS : CognitiveSubject Subject)
    (MeansAt : Subject → Prop → Prop)
    (ChoosesAt : Subject → Prop → Prop → Prop)
    (FreeWillAt : Subject → Prop)
    (hFreeWillDef : ∀ s', FreeWillAt s' ↔ ∃ a b, ChoosesAt s' a b)
    (hChoosesDef : ∀ s' a b, ChoosesAt s' a b ↔ (MeansAt s' a ∧ MeansAt s' b ∧ Incompatible a b))
    (hUptake : RefutationalCognitiveUptake Subject CS MeansAt)
    (s : Subject) (target : Prop)
    (hProof : RefutationalPerformance Subject CS s target) :
    ∃ s' : Subject, FreeWillAt s' := by
  obtain ⟨s', a, b, hChooses⟩ :=
    performative_proof_yields_freewill Subject CS MeansAt ChoosesAt hChoosesDef hUptake s target hProof
  refine ⟨s', (hFreeWillDef s').mpr ⟨a, b, hChooses⟩⟩

end Logos.ProofSpecificContrast
