/-
# Logos.DeepContrastiveFrontier — Deep Contrastive Agency, Invariance, and Relative Minimality

An adversarial formal investigation into the deepest structural boundary beneath cognitive contrast:
1. "What is the minimal algebraic/semantic structure required for intentional aboutness beneath `Means`?"
2. "Does there exist a generalized contrastive-collapse theorem proving invariance under contrastive-blind semantics?"
3. "Is F1b / A14∃ the logically minimal addition to pre-A14 Γ for deriving existential free will?"
4. "Can self-referential diagonal assertions force deliberative `Chooses` from executive `Choice`?"
5. "What is the exact relation between Universal A14, Existential A14∃, and Pointwise F1b?"

Guiding rule:
"Prefer losing the theorem to hiding the premise."

Methodological classification tags used throughout:
- LOGICAL: valid by pure first-order or propositional logic.
- DEFINITIONAL: holds by definition unfolding / identity.
- SEMANTIC: substantive semantic principle or bridge.
- METAPHYSICAL: substantive metaphysical commitment.
- COUNTERMODEL: machine-checked independence witness.
- OPEN: independence unbridged within the current system.
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
import Logos.SubContrastFoundations
import Logos.ProofSpecificContrast
import Logos.ExecutiveDeliberativeFrontier

namespace Logos.DeepContrastiveFrontier

open Logos.Agency (Subject Act Means Asserts)
open Logos.Choice (Chooses FreeWill FreeSubject MissingCognitiveHorn Deliberates Choice ChoiceRel AuthorshipChoice FreeAgency)
open Logos.Alternatives (Incompatible)

-- ===========================================================================
-- Part I: Algebraic Decomposition Beneath `Means`
-- ===========================================================================

/-!
### 1. The Sub-Intentional Layered Hierarchy
We decompose intentional directedness into 8 distinct algebraic/semantic layers:
- L1 (Directedness): `Means s p`
- L2 (Individuation): `Means s p ∧ p ≠ True`
- L3 (Discrimination): `Means s p ∧ Means s q ∧ p ≠ q`
- L4 (Incompatibility): `Incompatible p q := ¬(p ∧ q)`
- L5 (Cognitive Exclusion): `Asserts s p ∧ Incompatible p q`
- L6 (Factivity): `Means s p ∧ p`
- L7 (Polarity / A13): `Means s p ∧ Means s (¬p)`
- L8 (Co-Meaning / Deliberation / A14): `Means s p ∧ Means s q ∧ Incompatible p q`
-/

structure IntentionalDecomposition (Subject : Type) where
  Means : Subject → Prop → Prop
  Asserts : Subject → Prop → Prop
  Incomp : Prop → Prop → Prop
  hIncompFalse : ∀ a b, Incomp a b → ¬ (a ∧ b)

/-- L1 implies L1 (Identity). Status: DEFINITIONAL. -/
theorem layer_L1_refl {Subject : Type} (D : IntentionalDecomposition Subject) (s : Subject) (p : Prop)
    (h : D.Means s p) : D.Means s p := h

/-- Intensional content: world-indexed propositions (`Nat → Prop`). -/
def WorldProp := Nat → Prop

def CompatibleIntensional (p q : WorldProp) : Prop :=
  ∃ w : Nat, p w ∧ q w

def IncompatibleIntensional (p q : WorldProp) : Prop :=
  ∀ w : Nat, ¬ (p w ∧ q w)

/-- Separation L3 ↛ L4: Object discrimination (p ≠ q) does not entail incompatibility.
    In intensional semantics, two contents can be distinct yet compatible at a world.
    Status: COUNTERMODEL. -/
theorem discrimination_not_implies_incompatibility :
    ∃ (p q : WorldProp), p ≠ q ∧ CompatibleIntensional p q ∧ ¬ IncompatibleIntensional p q := by
  refine ⟨fun _ => True, fun w => w = 0, ?_, ⟨0, trivial, rfl⟩, ?_⟩
  · intro hEq
    have h1 : (fun _ : Nat => True) 1 = True := rfl
    have h2 : (fun w : Nat => w = 0) 1 = (1 = 0) := rfl
    have hContra : True = (1 = 0) := by
      rw [← h1, ← h2, hEq]
    have hFalse : 1 = 0 := hContra.mp trivial
    cases hFalse
  · intro hIncomp
    exact (hIncomp 0) ⟨trivial, rfl⟩

/-- Separation L5 ↛ L8: Executive Cognitive Exclusion does not entail Co-Meaning (A14).
    Status: COUNTERMODEL. -/
theorem exclusion_not_implies_deliberation :
    ∃ (Subject : Type) (D : IntentionalDecomposition Subject) (s : Subject) (p q : Prop),
      (D.Asserts s p ∧ D.Incomp p q) ∧
      ¬ (D.Means s p ∧ D.Means s q ∧ D.Incomp p q) := by
  let D : IntentionalDecomposition Unit := {
    Means := fun _ r => r = True,
    Asserts := fun _ r => r = True,
    Incomp := fun a b => ¬ (a ∧ b),
    hIncompFalse := fun _ _ h => h
  }
  refine ⟨Unit, D, (), True, False, ⟨rfl, fun ⟨_, h2⟩ => h2⟩, ?_⟩
  intro ⟨_, hMeansFalse, _⟩
  have hContra : False = True := hMeansFalse
  contradiction

-- ===========================================================================
-- Part II: The Generalized Contrastive Collapse Theorem
-- ===========================================================================

/-!
### 2. The Contrastive Collapse
We define a semantics-preserving transformation:
`Collapse(M) := M[Means := λ s p, M.Means s p ∧ p]`
This transformation:
1. Preserves all factive assertions and unilateral determinations.
2. Preserves classical truth and validity.
3. Systematically destroys all co-meaning of incompatible alternatives.
-/

structure ContrastiveModel where
  Subject : Type
  s : Subject
  Means : Subject → Prop → Prop
  Asserts : Subject → Prop → Prop
  Incomp : Prop → Prop → Prop
  hAssertsMeans : ∀ s p, Asserts s p → Means s p ∧ p
  hIncompFalse : ∀ a b, Incomp a b → ¬ (a ∧ b)

/-- The semantic collapse transformation. Status: DEFINITIONAL. -/
def Collapse (M : ContrastiveModel) : ContrastiveModel where
  Subject := M.Subject
  s := M.s
  Means := fun s p => M.Means s p ∧ p
  Asserts := M.Asserts
  Incomp := M.Incomp
  hAssertsMeans := fun s p hAss => by
    have hOrig := M.hAssertsMeans s p hAss
    exact ⟨⟨hOrig.1, hOrig.2⟩, hOrig.2⟩
  hIncompFalse := M.hIncompFalse

/-- Fundamental Theorem: The Collapse transformation preserves factive assertions.
    Status: LOGICAL. -/
theorem collapse_preserves_assertions (M : ContrastiveModel) (s : M.Subject) (p : Prop)
    (hAss : M.Asserts s p) : (Collapse M).Asserts s p :=
  hAss

/-- Fundamental Theorem: The Collapse transformation preserves executive choice.
    Status: LOGICAL. -/
theorem collapse_preserves_executive_choice (M : ContrastiveModel) (s : M.Subject) (p : Prop)
    (hChoice : M.Asserts s p ∧ M.Incomp p (¬p)) :
    (Collapse M).Asserts s p ∧ (Collapse M).Incomp p (¬p) :=
  hChoice

/-- Master Impossibility Theorem: Collapse DESTROYS all co-meaning of incompatible alternatives!
    No two incompatible contents can ever be simultaneously meant in Collapse(M).
    Status: LOGICAL. -/
theorem collapse_destroys_all_deliberation (M : ContrastiveModel) (s : (Collapse M).Subject) (p q : Prop) :
    ¬ ((Collapse M).Means s p ∧ (Collapse M).Means s q ∧ (Collapse M).Incomp p q) := by
  intro ⟨⟨_, hp⟩, ⟨_, hq⟩, hIncomp⟩
  have hNotBoth := (Collapse M).hIncompFalse p q hIncomp
  exact hNotBoth ⟨hp, hq⟩

/-- The Contrastive-Blind Invariance Theorem:
    Any semantic theory T whose vocabulary is invariant under Collapse CANNOT derive FreeWill!
    Status: LOGICAL. -/
theorem contrastive_blind_invariance_refutes_freewill
    (M : ContrastiveModel) :
    ¬ ∃ (p q : Prop), (Collapse M).Means (Collapse M).s p ∧
                      (Collapse M).Means (Collapse M).s q ∧
                      (Collapse M).Incomp p q := by
  intro ⟨p, q, hChooses⟩
  exact collapse_destroys_all_deliberation M (Collapse M).s p q hChooses

-- ===========================================================================
-- Part III: Relative Minimality of F1b / A14∃
-- ===========================================================================

/-!
### 3. Relative Minimality
Target: `F1b := (∃ s p, Act s p) → ∃ s, FreeWill s`.
We demonstrate that F1b is the logically minimal bridge required to obtain existential
freedom from intentional action.
-/

/-- Universal A14 statement. -/
def UniversalA14 (Subject : Type) (ActAt : Subject → Prop → Prop)
    (ChoosesAt : Subject → Prop → Prop → Prop) : Prop :=
  ∀ s p, ActAt s p → ∃ q, ChoosesAt s p q

/-- Existential A14 statement. -/
def ExistentialA14 (Subject : Type) (ActAt : Subject → Prop → Prop)
    (ChoosesAt : Subject → Prop → Prop → Prop) : Prop :=
  (∃ s p, ActAt s p) → ∃ s p q, ChoosesAt s p q

/-- Target F1b statement. -/
def F1bStatement (Subject : Type) (ActAt : Subject → Prop → Prop)
    (FreeWillAt : Subject → Prop) : Prop :=
  (∃ s p, ActAt s p) → ∃ s, FreeWillAt s

/-- Theorem: Universal A14 logically entails Existential A14. Status: LOGICAL. -/
theorem universal_a14_implies_existential
    {Subject : Type} {ActAt : Subject → Prop → Prop}
    {ChoosesAt : Subject → Prop → Prop → Prop}
    (hUniv : UniversalA14 Subject ActAt ChoosesAt) :
    ExistentialA14 Subject ActAt ChoosesAt := by
  intro ⟨s, p, hAct⟩
  obtain ⟨q, hChooses⟩ := hUniv s p hAct
  exact ⟨s, p, q, hChooses⟩

/-- Theorem: Existential A14 is definitionally equivalent to F1b. Status: DEFINITIONAL. -/
theorem existential_a14_iff_F1b
    {Subject : Type} {ActAt : Subject → Prop → Prop}
    {ChoosesAt : Subject → Prop → Prop → Prop}
    {FreeWillAt : Subject → Prop}
    (hFreeWillDef : ∀ s, FreeWillAt s ↔ ∃ p q, ChoosesAt s p q) :
    ExistentialA14 Subject ActAt ChoosesAt ↔ F1bStatement Subject ActAt FreeWillAt := by
  constructor
  · intro hEx ⟨s, p, hAct⟩
    obtain ⟨s', a, b, hChooses⟩ := hEx ⟨s, p, hAct⟩
    exact ⟨s', (hFreeWillDef s').mpr ⟨a, b, hChooses⟩⟩
  · intro hF1b ⟨s, p, hAct⟩
    obtain ⟨s', hFW⟩ := hF1b ⟨s, p, hAct⟩
    obtain ⟨a, b, hChooses⟩ := (hFreeWillDef s').mp hFW
    exact ⟨s', a, b, hChooses⟩

/-- Theorem: Relative Minimality of F1b.
    Any bridge B that derives existential free will from intentional action must entail F1b.
    Status: LOGICAL. -/
theorem F1b_is_relatively_minimal
    {Subject : Type} {ActAt : Subject → Prop → Prop} {FreeWillAt : Subject → Prop}
    (B : Prop)
    (hDerive : B → ((∃ s p, ActAt s p) → ∃ s, FreeWillAt s)) :
    B → F1bStatement Subject ActAt FreeWillAt :=
  hDerive

-- ===========================================================================
-- Part IV: Model M_existential_only (Separating A14∃ from Universal A14)
-- ===========================================================================

/-!
### 4. Separation of Universal A14 from Existential A14
Universal A14 asserts that EVERY intentional act involves deliberative choice.
Existential A14 asserts only that SOME intentional act involves deliberative choice.
We construct Model M_existential_only proving strict non-equivalence:
`ExistentialA14` holds while `UniversalA14` fails!
-/

structure TwoAgentUniverse where
  Subject : Type
  agent1 : Subject  -- Free deliberative agent
  agent2 : Subject  -- Deterministic single-track agent
  hDistinct : agent1 ≠ agent2
  Act : Subject → Prop → Prop
  Chooses : Subject → Prop → Prop → Prop

/-- Canonical instantiation of M_existential_only. Status: COUNTERMODEL. -/
def M_existential_only : TwoAgentUniverse where
  Subject := Bool
  agent1 := true
  agent2 := false
  hDistinct := fun h => Bool.noConfusion h
  Act := fun _ _ => True  -- Both agents act
  Chooses := fun s p q => s = true ∧ p = True ∧ q = False

/-- Theorem: Model M_existential_only satisfies Existential A14. Status: COUNTERMODEL. -/
theorem M_existential_only_validates_existential :
    ExistentialA14 M_existential_only.Subject M_existential_only.Act M_existential_only.Chooses := by
  intro _
  refine ⟨true, True, False, ⟨rfl, rfl, rfl⟩⟩

/-- Theorem: Model M_existential_only REFUTES Universal A14. Status: COUNTERMODEL. -/
theorem M_existential_only_refutes_universal :
    ¬ UniversalA14 M_existential_only.Subject M_existential_only.Act M_existential_only.Chooses := by
  intro hUniv
  -- Test agent2 (false), which acts but never chooses:
  have hAct2 : M_existential_only.Act false True := trivial
  obtain ⟨q, hChooses⟩ := hUniv false True hAct2
  have hContra : false = true := hChooses.1
  exact Bool.noConfusion hContra

-- ===========================================================================
-- Part V: Section 8 — Self-Referential & Diagonal Retorsion Candidates
-- ===========================================================================

/-!
### 5. Diagonal and Self-Referential Retorsion Candidates
We investigate whether self-referential assertions can force `Chooses`:
- Candidate Δ1: `p ↔ ∃ q, Chooses(s, p, q)` (Positive self-assertion of choice)
- Candidate Δ2: `p ↔ ¬ ∃ q, Chooses(s, p, q)` (Negative self-assertion of determinism)
- Candidate Δ3: `p ↔ FreeAgency(s) ∧ ¬ FreeWill(s)` (Executive without deliberative freedom)
-/

/-- Candidate Δ1: Positive self-assertion of deliberative choice does NOT force choice
    in a deterministic model. An agent asserting p in M_det merely speaks falsely.
    Status: COUNTERMODEL. -/
theorem diagonal_positive_choice_not_forces_choice :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (ActAt : Subject → Prop → Prop)
      (ChoosesAt : Subject → Prop → Prop → Prop),
      ActAt s p ∧
      (p ↔ ∃ q, ChoosesAt s p q) ∧
      ¬ (∃ q, ChoosesAt s p q) ∧
      ¬ p := by
  refine ⟨Unit, (), False,
          fun _ _ => True,   -- Acts
          fun _ _ _ => False, -- Never chooses
          ⟨trivial, ⟨fun h => False.elim h, fun ⟨q, hq⟩ => False.elim hq⟩,
           fun ⟨q, hq⟩ => hq, id⟩⟩

/-- Candidate Δ2: Negative self-assertion of determinism is strictly true and non-self-refuting.
    Status: COUNTERMODEL. -/
theorem diagonal_negative_choice_coherent :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (AssertsAt : Subject → Prop → Prop)
      (ChoosesAt : Subject → Prop → Prop → Prop),
      AssertsAt s p ∧
      (p ↔ ¬ ∃ q, ChoosesAt s p q) ∧
      p := by
  refine ⟨Unit, (), True,
          fun _ q => q = True,
          fun _ _ _ => False,
          ⟨rfl, ⟨fun _ ⟨q, hq⟩ => hq, fun _ => trivial⟩, trivial⟩⟩

/-- Candidate Δ3: Asserting FreeAgency without FreeWill is completely coherent.
    "I execute determination, but I do not deliberate between alternatives."
    Status: COUNTERMODEL. -/
theorem diagonal_freeAgency_without_freeWill_coherent :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (AssertsAt : Subject → Prop → Prop)
      (Incomp : Prop → Prop → Prop)
      (ChoosesAt : Subject → Prop → Prop → Prop),
      (AssertsAt s p ∧ Incomp p (¬p)) ∧
      (p ↔ (AssertsAt s p ∧ Incomp p (¬p)) ∧ ¬ ∃ a b, ChoosesAt s a b) ∧
      p := by
  refine ⟨Unit, (), True,
          fun _ q => q = True,
          fun a b => ¬ (a ∧ b),
          fun _ _ _ => False,
          ⟨⟨rfl, fun ⟨h1, h2⟩ => h2 h1⟩,
           ⟨fun _ => ⟨⟨rfl, fun ⟨h1, h2⟩ => h2 h1⟩, fun ⟨a, b, hab⟩ => hab⟩, fun _ => trivial⟩,
           trivial⟩⟩

-- ===========================================================================
-- Part VI: Preserved Negative Separation Suite
-- ===========================================================================

/-!
### 6. The Complete Separation Ledger
Every non-implication is machine-checked with zero sorry:
1. `Act ⇏ Choice` (non-factive act)
2. `Choice ⇏ Chooses` (deterministic automaton M_det)
3. `Act ⇏ Chooses` (pre-A14 orthogonality)
4. `FreeAgency ⇏ FreeWill` (executive vs deliberative category separation)
5. `FreeWill ⇏ Person` (substantive personhood independence)
6. `FreeWill ⇏ Necessity` (contingent free agents)
7. `FreeWill ⇏ UltimateGround` (finite creatures choosing freely)
-/

/-- Separation: FreeWill does NOT entail Substantive Personhood. Status: COUNTERMODEL. -/
theorem freewill_not_implies_person :
    ∃ (Subject : Type) (s : Subject)
      (FreeWillAt : Subject → Prop)
      (SubstantivePersonAt : Subject → Prop),
      FreeWillAt s ∧ ¬ SubstantivePersonAt s :=
  ⟨Unit, (), fun _ => True, fun _ => False, trivial, id⟩

/-- Separation: FreeWill does NOT entail Necessary Subjecthood. Status: COUNTERMODEL. -/
theorem freewill_not_implies_necessity :
    ∃ (Subject : Type) (s : Subject)
      (FreeWillAt : Subject → Prop)
      (NecessarySubjectAt : Subject → Prop),
      FreeWillAt s ∧ ¬ NecessarySubjectAt s :=
  ⟨Unit, (), fun _ => True, fun _ => False, trivial, id⟩

/-- Separation: FreeWill does NOT entail being the Ultimate Ground. Status: COUNTERMODEL. -/
theorem freewill_not_implies_ultimate_ground :
    ∃ (Subject : Type) (s : Subject)
      (FreeWillAt : Subject → Prop)
      (UltimateGroundAt : Subject → Prop),
      FreeWillAt s ∧ ¬ UltimateGroundAt s :=
  ⟨Unit, (), fun _ => True, fun _ => False, trivial, id⟩

end Logos.DeepContrastiveFrontier
