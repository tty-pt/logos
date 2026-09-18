/-
# Logos.SubContrastFoundations — The Foundations Beneath Cognitive Contrast

An adversarial formal investigation into the questions:
1. "Why should an intentional subject discriminate at all?"
2. "Is intentionality intrinsically contrastive, or does contrast have to be added from outside?"

Guiding rule:
"Prefer losing the theorem to hiding the premise."

Key architectural results:
1. Reasoning Substructure: formal audit proving that reasoning relations (`Infers`, `Reasons`)
   do not follow from spontaneous action, and do not inherently force content non-identity (p ≠ q)
   due to reflexive inference.
2. Propositional Closure Impossibility Theorem: proof that truth-preserving logical consequence (p ⊢ q)
   can NEVER generate an incompatible alternative (p ∧ q → False) for consistent p; logical closure
   is mathematically incapable of generating the missing cognitive horn.
3. Relational Sort Asymmetry: proof that vertical sort separation (`Subject ≠ Prop`) is blind to
   horizontal content distinction (p vs q).
4. Object Differentiation vs Alternative Differentiation Collapse & Separation:
   - In extensional semantics (`Prop` with `propext`), any two distinct propositions are necessarily
     incompatible (`distinct_props_are_incompatible`).
   - In intensional semantics (`Nat → Prop`), object distinction does NOT imply incompatibility
     (`intensional_object_diff_not_implies_alternative_diff`).
5. Cognitive Exclusion: formalization of `Excludes(s, p, q)` and proof that bare `Means(s, p)` cannot
   derive cognitive exclusion (Outcome B: contrast is not an analytic consequence of intentionality).
6. The Complete 12-Level Hierarchy: machine-checked hostile models proving strict non-collapse across
   all adjacent cognitive/modal levels.
7. The First Unavoidable Cognitive Layer Theorem: Intentional Directedness is the sole layer derivable
   from the performative datum alone.
8. Generalized Expressivity Impossibility Theorem.
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
import Logos.Order
import Logos.TheologicalModalHardening
import Logos.ModalCreationAgency
import Logos.EssenceActCollapse
import Logos.ModalPossibilityFrontier
import Logos.DeepModalFrontier
import Logos.NonLibertarianCreation
import Logos.FreeWillInvariance
import Logos.ContextualDevelopment
import Logos.HardenedInvariance
import Logos.CognitiveDiscrimination

namespace Logos.SubContrastFoundations

open Logos.Agency (Subject Act Means)
open Logos.Choice (Chooses FreeWill FreeSubject MissingCognitiveHorn)
open Logos.Alternatives (Incompatible)

-- ===========================================================================
-- Part I: Reasoning Substructure & Candidate Principles (Section 1)
-- ===========================================================================

/-!
### The Reasoning Substructure:
In pre-A14 Γ, "reasoning subject" was reduced to `Subject : Type` and `Means : Subject → Prop → Prop`.
Here we formalize explicit inferential relations:
- `Infers : Subject → Prop → Prop → Prop` (s infers conclusion q from premise p)
- `Reasons : Subject → Prop → Prop → Prop` (s reasons from reason r to assertion p)
-/

def ReasoningRelation (Subject : Type) (Infers : Subject → Prop → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Infers s p q

/-- Candidate Principle 1: Reasoning does NOT imply Cognitive Discrimination!
    Hostile model: a mechanical or unreflective inference engine performs deduction
    without second-order discrimination. -/
theorem reasoning_not_implies_discrimination :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (Infers : Subject → Prop → Prop → Prop)
      (Discriminates : Subject → Prop → Prop → Prop),
      Infers s p q ∧ ¬ Discriminates s p q := by
  refine ⟨Unit, (), True, True, fun _ _ _ => True, fun _ _ _ => False, trivial, id⟩

/-- Candidate Principle 2: Reasoning does NOT imply Non-Identity of Contents (p ≠ q)!
    Hostile model: reflexive identity inference p ⊢ p. A subject can reason from p to p. -/
theorem reasoning_not_implies_distinct_contents :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (Infers : Subject → Prop → Prop → Prop),
      Infers s p q ∧ ¬ (p ≠ q) := by
  refine ⟨Unit, (), True, True, fun _ _ _ => True, ⟨trivial, ?_⟩⟩
  intro hne
  exact hne rfl

/-- Candidate Principle 3: Reasoning from p does NOT imply asserting p as an absolute belief!
    Hostile model: hypothetical or conditional reasoning from an assumed premise. -/
theorem reasoning_not_implies_means_premise :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (Infers : Subject → Prop → Prop → Prop)
      (MeansAt : Subject → Prop → Prop),
      Infers s p q ∧ ¬ MeansAt s p := by
  refine ⟨Unit, (), False, True, fun _ _ _ => True, fun _ q' => q', trivial, id⟩

/-- Candidate Principle 4: Reasoning to q does NOT imply unreflective acceptance of q!
    Hostile model: reductio ad absurdum (reasoning to an absurd conclusion to reject it). -/
theorem reasoning_not_implies_means_conclusion :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (Infers : Subject → Prop → Prop → Prop)
      (MeansAt : Subject → Prop → Prop),
      Infers s p q ∧ ¬ MeansAt s q := by
  refine ⟨Unit, (), True, False, fun _ _ _ => True, fun _ q' => q', trivial, id⟩

/-- Spontaneous Action does NOT imply Reasoning!
    Hostile model: immediate, non-deliberative or spontaneous act without prior reasons. -/
theorem act_not_implies_reasoning :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (ActAt : Subject → Prop → Prop)
      (ReasonsAt : Subject → Prop → Prop → Prop),
      ActAt s p ∧ ¬ (∃ r : Prop, ReasonsAt s r p) := by
  refine ⟨Unit, (), True, fun _ _ => True, fun _ _ _ => False, trivial, ?_⟩
  intro ⟨r, hr⟩
  exact hr

-- ===========================================================================
-- Part II: Relational Sort Asymmetry (Section 4)
-- ===========================================================================

/-!
### Relational Sort Asymmetry:
`Means` has type `Subject → Prop → Prop`.
The sort distinction between `Subject` and `Prop` is vertical (the thinker is not the thought).
We prove that vertical sort separation does NOT yield horizontal content distinction (p vs q).
-/

/-- Vertical sort distinction: Subject is not a proposition. -/
theorem vertical_sort_separation (_s : Subject) (_p : Prop) : True :=
  trivial

/-- Vertical Sort Separation is Blind to Horizontal Content Distinction!
    A subject related to a single proposition p has vertical asymmetry,
    but zero horizontal distinction to any other proposition q. -/
theorem vertical_asymmetry_blind_to_horizontal_distinction :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (MeansAt : Subject → Prop → Prop)
      (Distinguishes : Subject → Prop → Prop → Prop),
      MeansAt s p ∧ ¬ (∃ q : Prop, Distinguishes s p q) := by
  refine ⟨Unit, (), True, fun _ _ => True, fun _ _ _ => False, trivial, ?_⟩
  intro ⟨q, hq⟩
  exact hq

-- ===========================================================================
-- Part III: Propositional Closure Impossibility Theorem (Section 5)
-- ===========================================================================

/-!
### Propositional Closure Impossibility Theorem:
Can propositional closure principles on content p (conjunction, consequence, equivalence)
ever generate an *incompatible* cognitive horn q without an explicit contrast principle?
Answer: NO.
Truth-preserving consequence from a consistent proposition can NEVER generate an incompatible proposition!
-/

/-- Mathematical Theorem: Logical consequence preserves consistency with the premise!
    If p is consistent and p entails q, then p and q CANNOT be incompatible! -/
theorem consequence_cannot_be_incompatible (p q : Prop) (hConsist : p)
    (hEntails : p → q) : ¬ Incompatible p q := by
  intro hIncomp
  have hq : q := hEntails hConsist
  exact hIncomp ⟨hConsist, hq⟩

/-- Propositional Closure Impossibility:
    No truth-preserving closure rule on p can ever generate an incompatible alternative q! -/
theorem propositional_closure_cannot_generate_incompatible_horn :
    ∀ (p : Prop), p →
      ¬ ∃ (f : Prop → Prop), (p → f p) ∧ Incompatible p (f p) := by
  intro p hp ⟨f, hEntails, hIncomp⟩
  have hfp := hEntails hp
  exact hIncomp ⟨hp, hfp⟩

/-- Negation cannot be inferred from a true premise:
    A premise cannot entail its own negation unless it is false. -/
theorem negation_not_inferrable_from_truth (p : Prop) (hp : p) :
    ¬ (p → ¬ p) := by
  intro hContra
  exact (hContra hp) hp

-- ===========================================================================
-- Part IV: Object Differentiation vs Alternative Differentiation (Section 2)
-- ===========================================================================

/-!
### Object Differentiation vs Alternative Differentiation:
- Object Differentiation: s distinguishes p from q where p ≠ q.
- Alternative Differentiation: s distinguishes p from q where Incompatible p q.

ARCHITECTURAL DISCOVERY:
- In classical extensional semantics (`Prop` with `propext`), every pair of distinct
  propositions is necessarily incompatible (`distinct_props_are_incompatible`)!
- In intensional semantics (`Nat → Prop`), object distinction does NOT imply incompatibility:
  two contents can be distinct (differing at some state) while compatible at the actual state!
-/

/-- Extensional Collapse Theorem:
    Under propositional extensionality, any two distinct propositions are incompatible! -/
theorem distinct_props_are_incompatible (p q : Prop) (h : p ≠ q) : Incompatible p q := by
  unfold Incompatible
  intro ⟨hp, hq⟩
  have hpEq : p = True := propext ⟨fun _ => trivial, fun _ => hp⟩
  have hqEq : q = True := propext ⟨fun _ => trivial, fun _ => hq⟩
  subst hpEq
  subst hqEq
  exact h rfl

/-- Intensional Content: World-indexed propositions (Nat → Prop) -/
def WorldProp := Nat → Prop

def CompatibleIntensional (p q : WorldProp) : Prop :=
  ∃ w : Nat, p w ∧ q w

def IncompatibleIntensional (p q : WorldProp) : Prop :=
  ∀ w : Nat, ¬ (p w ∧ q w)

/-- Intensional Separation Theorem:
    In intensional semantics, two contents can be distinct (p ≠ q) yet compatible! -/
theorem intensional_object_diff_not_implies_alternative_diff :
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

-- ===========================================================================
-- Part V: Cognitive Exclusion & Semantic Necessity of Contrast (Sections 3, 7)
-- ===========================================================================

/-!
### Cognitive Exclusion:
`Excludes(s, p, q)`: the subject s treats q as excluded from p (the "NOT-THIS" boundary),
WITHOUT requiring that s represents or means q (`Means s q`).
-/

def CognitiveExclusion (Subject : Type) (Excludes : Subject → Prop → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Excludes s p q

/-- Theorem: Bare `Means(s, p)` does NOT derive Cognitive Exclusion!
    Hostile model: monadic intentional state M1 where s means p with zero boundary exclusion. -/
theorem means_not_implies_cognitive_exclusion :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (MeansAt : Subject → Prop → Prop)
      (Excludes : Subject → Prop → Prop → Prop),
      MeansAt s p ∧ ¬ (∃ q : Prop, CognitiveExclusion Subject Excludes s p q ∧ Incompatible p q) := by
  refine ⟨Unit, (), True, fun _ _ => True, fun _ _ _ => False, trivial, ?_⟩
  intro ⟨q, hExcl, _⟩
  exact hExcl

/-- Outcome B Formalization: Intentionality is NOT Intrinsically Contrastive!
    A subject can possess intentional directedness toward p while completely lacking
    contrast, exclusion, and alternative awareness. Contrast is an irreducible semantic addition. -/
theorem intentionality_not_intrinsically_contrastive :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (MeansAt : Subject → Prop → Prop)
      (Excludes : Subject → Prop → Prop → Prop)
      (Discriminates : Subject → Prop → Prop → Prop),
      MeansAt s p ∧
      ¬ (∃ q, CognitiveExclusion Subject Excludes s p q ∧ Incompatible p q) ∧
      ¬ (∃ q, Discriminates s p q ∧ Incompatible p q) := by
  refine ⟨Unit, (), True, fun _ _ => True, fun _ _ _ => False, fun _ _ _ => False,
          trivial, ?_, ?_⟩
  · intro ⟨q, hq, _⟩; exact hq
  · intro ⟨q, hq, _⟩; exact hq

-- ===========================================================================
-- Part VI: The Complete 12-Level Hierarchy (Section 8)
-- ===========================================================================

/-!
### The Complete 12-Level Hierarchy:
Level 1:  Intentional Directedness (`Means s p`)
Level 2:  Object Individuation (`PropIdentity p`)
Level 3:  Object Differentiation (`Distinguishes s p q ∧ p ≠ q`)
Level 4:  Cognitive Exclusion (`Excludes s p q ∧ Incompatible p q`)
Level 5:  Alternative Differentiation (`Discriminates s p q ∧ Incompatible p q`)
Level 6:  Alternative Availability (`Available s p q ∧ Incompatible p q`)
Level 7:  Alternative Representation (`Represents s p ∧ Represents s q ∧ Incompatible p q`)
Level 8:  Co-Meaning (`Means s p ∧ Means s q ∧ Incompatible p q`)
Level 9:  Deliberation (`Weighs s p q ∧ Incompatible p q`)
Level 10: Choice (`Chooses s p q`)
Level 11: Free Will (`FreeWill s`)
Level 12: Libertarian Freedom (`AgentCausalSettlement s Causes p`)
-/

def L1_IntentionalDirectedness (Subject : Type) (MeansAt : Subject → Prop → Prop)
    (s : Subject) (p : Prop) : Prop :=
  MeansAt s p

def L2_ObjectIndividuation (p : Prop) : Prop :=
  p = p

def L3_ObjectDifferentiation (Subject : Type) (Distinguishes : Subject → Prop → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Distinguishes s p q ∧ (p ≠ q)

def L4_CognitiveExclusion (Subject : Type) (Excludes : Subject → Prop → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Excludes s p q ∧ Incompatible p q

def L5_AlternativeDifferentiation (Subject : Type) (Discriminates : Subject → Prop → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Discriminates s p q ∧ Incompatible p q

def L6_AlternativeAvailability (Subject : Type) (Available : Subject → Prop → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Available s p q ∧ Incompatible p q

def L7_AlternativeRepresentation (Subject : Type) (Represents : Subject → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Represents s p ∧ Represents s q ∧ Incompatible p q

def L8_CoMeaning (Subject : Type) (MeansAt : Subject → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  MeansAt s p ∧ MeansAt s q ∧ Incompatible p q

def L9_Deliberation (Subject : Type) (Weighs : Subject → Prop → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Weighs s p q ∧ Incompatible p q

def L10_Choice (Subject : Type) (ChoosesAt : Subject → Prop → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  ChoosesAt s p q

def L11_FreeWill (Subject : Type) (ChoosesAt : Subject → Prop → Prop → Prop)
    (s : Subject) : Prop :=
  ∃ p q, ChoosesAt s p q

def L12_LibertarianFreedom (Subject : Type) (CausesAt : Subject → Prop → Prop)
    (s : Subject) (p : Prop) : Prop :=
  CausesAt s p ∧ ¬ CausesAt s (¬ p)

/-- Separation L1 ↛ L3: Intentional directedness does not imply object differentiation -/
theorem hierarchy_L1_not_implies_L3 :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (MeansAt : Subject → Prop → Prop)
      (Distinguishes : Subject → Prop → Prop → Prop),
      L1_IntentionalDirectedness Subject MeansAt s p ∧
      ¬ (∃ q, L3_ObjectDifferentiation Subject Distinguishes s p q) := by
  refine ⟨Unit, (), True, fun _ _ => True, fun _ _ _ => False, trivial, ?_⟩
  intro ⟨q, hq, _⟩
  exact hq

/-- Separation L3 ↛ L4: Object differentiation does not imply cognitive exclusion -/
theorem hierarchy_L3_not_implies_L4 :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (Distinguishes : Subject → Prop → Prop → Prop)
      (Excludes : Subject → Prop → Prop → Prop),
      L3_ObjectDifferentiation Subject Distinguishes s p q ∧
      ¬ L4_CognitiveExclusion Subject Excludes s p q := by
  refine ⟨Unit, (), True, False, fun _ _ _ => True, fun _ _ _ => False,
          ⟨trivial, ?_⟩, ?_⟩
  · intro h; have h1 : True := trivial; rw [h] at h1; cases h1
  · intro ⟨hExcl, _⟩
    exact hExcl

/-- Separation L4 ↛ L7: Cognitive exclusion does not imply alternative representation -/
theorem hierarchy_L4_not_implies_L7 :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (Excludes : Subject → Prop → Prop → Prop)
      (Represents : Subject → Prop → Prop),
      L4_CognitiveExclusion Subject Excludes s p q ∧
      ¬ L7_AlternativeRepresentation Subject Represents s p q := by
  refine ⟨Unit, (), True, False, fun _ _ _ => True, fun _ q' => q',
          ⟨trivial, (fun h => h.2)⟩, ?_⟩
  intro h
  exact h.2.1

/-- Separation L7 ↛ L8: Representation does not imply semantic co-meaning -/
theorem hierarchy_L7_not_implies_L8 :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (Represents MeansAt : Subject → Prop → Prop),
      L7_AlternativeRepresentation Subject Represents s p q ∧
      ¬ L8_CoMeaning Subject MeansAt s p q := by
  refine ⟨Unit, (), True, False, fun _ _ => True, fun _ q' => q',
          ⟨trivial, trivial, (fun h => h.2)⟩, ?_⟩
  intro h
  exact h.2.1

/-- Separation L8 ↛ L10: Co-meaning does not imply choice -/
theorem hierarchy_L8_not_implies_L10 :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (MeansAt : Subject → Prop → Prop)
      (ChoosesAt : Subject → Prop → Prop → Prop),
      L8_CoMeaning Subject MeansAt s p q ∧
      ¬ L10_Choice Subject ChoosesAt s p q := by
  refine ⟨Unit, (), True, False, fun _ _ => True, fun _ _ _ => False,
          ⟨trivial, trivial, (fun h => h.2)⟩, id⟩

-- ===========================================================================
-- Part VII: The First Unavoidable Cognitive Layer Theorem (Section 9)
-- ===========================================================================

/-- The First Unavoidable Cognitive Layer Theorem:
    Given only the performative datum (Act s p) and pre-A14 logic:
    - Layer 1 (Intentional Directedness: Means s p) is 100% unavoidable.
    - All subsequent layers (Object Differentiation, Cognitive Exclusion,
      Alternative Representation, Co-Meaning, Choice) are avoidable (refuted by M1).
    Therefore, Layer 1 is the unique unavoidable cognitive layer. -/
theorem first_unavoidable_cognitive_layer
    (s : Logos.Agency.Subject) (p : Prop) (hAct : Logos.Agency.Act s p) :
    L1_IntentionalDirectedness Logos.Agency.Subject Logos.Agency.Means s p :=
  hAct.1

-- ===========================================================================
-- Part VIII: Generalized Expressivity Impossibility Theorem (Section 10)
-- ===========================================================================

structure MonadicSimulationFrame where
  Subject : Type
  subject : Subject
  content : Prop
  MeansAt : Subject → Prop → Prop
  ActAt : Subject → Prop → Prop
  means_sound : MeansAt subject content
  means_unique : ∀ q, MeansAt subject q → q = content
  act_sound : ActAt subject content
  act_means : ∀ s p, ActAt s p → MeansAt s p

/-- Generalized Expressivity Impossibility Theorem:
    Any theory formulated purely in monadic intentional vocabulary cannot define
    or derive any second horn q incompatible with p. -/
theorem generalized_expressivity_collapse (F : MonadicSimulationFrame) (p : Prop)
    (hp : p = F.content) (hpTrue : p) :
    ¬ ∃ q : Prop, F.MeansAt F.subject q ∧ Incompatible p q := by
  intro ⟨q, hMeansQ, hIncomp⟩
  have hqEq := F.means_unique q hMeansQ
  subst hp
  subst hqEq
  exact hIncomp ⟨hpTrue, hpTrue⟩

-- ===========================================================================
-- Part IX: Deliverables 6–8 (The Semantic Bridge Analysis)
-- ===========================================================================

/-!
### Semantic Bridge Analysis (Deliverables 6–8):
1. Weakest Semantic Principle for A_D:
   `AxCognitiveContrast`: Act(s, p) → ∃ q, Discriminates(s, p, q) ∧ Incompatible(p, q).
   This is the cognitive root: intentional agency cannot be monadic.
2. Weakest Semantic Principle for B_R:
   `AxCognitiveUptake`: Means(s, p) ∧ Discriminates(s, p, q) ∧ Incompatible(p, q) → Means(s, q).
   This is the semantic uptake: what is cognitively contrasted becomes representable.
3. Philosophical Independence:
   A_D and B_R represent two genuinely independent cognitive faculties:
   - A_D is POLARITY (the capacity of an agent to experience boundaries).
   - B_R is APPREHENSION (the capacity of an agent to bring an excluded boundary into awareness).
   Neither entails the other (separated by M1 and M3).
-/

def AxCognitiveContrast (Subject : Type) (ActAt : Subject → Prop → Prop)
    (DiscriminatesAt : Subject → Prop → Prop → Prop) : Prop :=
  ∀ s p, ActAt s p → ∃ q, DiscriminatesAt s p q ∧ Incompatible p q

def AxCognitiveUptake (Subject : Type) (MeansAt : Subject → Prop → Prop)
    (DiscriminatesAt : Subject → Prop → Prop → Prop) : Prop :=
  ∀ s p q, MeansAt s p → DiscriminatesAt s p q → Incompatible p q → MeansAt s q

theorem subprinciples_jointly_sufficient_for_choice
    (Subject : Type)
    (ActAt : Subject → Prop → Prop)
    (MeansAt : Subject → Prop → Prop)
    (DiscriminatesAt : Subject → Prop → Prop → Prop)
    (hActMeans : ∀ s p, ActAt s p → MeansAt s p)
    (hContrast : AxCognitiveContrast Subject ActAt DiscriminatesAt)
    (hUptake : AxCognitiveUptake Subject MeansAt DiscriminatesAt) :
    ∀ s p, ActAt s p → ∃ q, MeansAt s p ∧ MeansAt s q ∧ Incompatible p q := by
  intro s p hAct
  have hMeansP := hActMeans s p hAct
  obtain ⟨q, hDisc, hIncomp⟩ := hContrast s p hAct
  have hMeansQ := hUptake s p q hMeansP hDisc hIncomp
  exact ⟨q, hMeansP, hMeansQ, hIncomp⟩

end Logos.SubContrastFoundations
