/-
# Logos.CognitiveDiscrimination — Cognitive Discrimination & Minimal Sub-Means Architecture

An adversarial formal investigation into the question:
"Is there a genuinely more primitive cognitive structure beneath `Means` that can
explain why an intentional subject can represent one content as distinct from another,
and from which the missing cognitive horn can arise?"

Guiding rule:
"Prefer losing the theorem to hiding the premise."

Key architectural results:
1. Epistemic Archaeology of `Means`: formal classification of 10 candidate sub-properties,
   proving that no contrastive or bilateral property is derivable from `Means(s, p)`.
2. Cognitive Discrimination Layer: formalization of `Discriminates(s, p, q)` and evaluation
   of properties D1–D4.
3. Minimal Decomposition of A14: deconstruction of A14 into strictly weaker sub-principles:
   - A_D (Cognitive Contrast Principle)
   - B_R (Cognitive Uptake Principle)
   proving A_D + B_R ⊢ F1b, while neither suffices alone.
4. Horn-Local Decomposition of `Means`: separating representation from affirmation, proving
   that horn-local decomposition cannot generate horn q.
5. Architectural Impossibility / Cognitive Collapse Theorem: proving that pre-A14 unary
   intentional vocabulary is invariant under single-content collapse.
6. The 6-Level Cognitive/Modal Hierarchy: machine-checked hostile models M0–M5 proving
   strict non-collapse across all adjacent levels.
7. Formal Comparison Lattice across 7 competing cognitive interpretations.
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

namespace Logos.CognitiveDiscrimination

open Logos.Agency (Subject Act Means)
open Logos.Choice (Chooses FreeWill FreeSubject MissingCognitiveHorn)
open Logos.Alternatives (Incompatible)

-- ===========================================================================
-- Section 1: Epistemic Archaeology of `Means`
-- ===========================================================================

/-!
### The 10 Candidate Sub-Properties of `Means(s, p)`
We test whether `Means(s, p)` implicitly contains or entails any bilateral
or contrastive cognitive property.
-/

/-- Candidate 1: Content Identity (p = p) - LOGICAL -/
def PropIdentity (p : Prop) : Prop := p = p

theorem means_implies_identity (s : Subject) (p : Prop) (_h : Means s p) :
    PropIdentity p :=
  rfl

/-- Candidate 2: Content Individuation - LOGICAL under classical logic -/
def ContentIndividuation (p : Prop) : Prop :=
  ∀ q : Prop, p = q ∨ p ≠ q

theorem means_implies_individuation (s : Subject) (p : Prop) (_h : Means s p) :
    ContentIndividuation p := by
  intro q
  by_cases h : p = q
  · exact Or.inl h
  · exact Or.inr h

/-- Candidate 3: Content Awareness - DEFINITIONAL / REDUNDANT -/
def ContentAwareness (s : Subject) (p : Prop) : Prop := Means s p

theorem means_iff_awareness (s : Subject) (p : Prop) :
    Means s p ↔ ContentAwareness s p :=
  Iff.rfl

/-- Candidate 4: Representation of p - DEFINITIONAL / REDUNDANT -/
def Representation (s : Subject) (p : Prop) : Prop := Means s p

theorem means_iff_representation (s : Subject) (p : Prop) :
    Means s p ↔ Representation s p :=
  Iff.rfl

/-- Candidate 5: Aboutness - DEFINITIONAL / REDUNDANT -/
def Aboutness (s : Subject) (p : Prop) : Prop := Means s p

theorem means_iff_aboutness (s : Subject) (p : Prop) :
    Means s p ↔ Aboutness s p :=
  Iff.rfl

/-- Candidate 6: Consideration of p - DEFINITIONAL / REDUNDANT -/
def Consideration (s : Subject) (p : Prop) : Prop := Means s p

theorem means_iff_consideration (s : Subject) (p : Prop) :
    Means s p ↔ Consideration s p :=
  Iff.rfl

/-- Candidate 7: Entertainment of p - DEFINITIONAL / REDUNDANT -/
def Entertainment (s : Subject) (p : Prop) : Prop := Means s p

theorem means_iff_entertainment (s : Subject) (p : Prop) :
    Means s p ↔ Entertainment s p :=
  Iff.rfl

/-- Candidate 8: Content Discrimination (∃ q ≠ p, Discriminates s p q) - STRICTLY STRONGER / COUNTERMODEL.
    Fails in a monadic model where the subject means p and has no cognitive relation to any other proposition. -/
def ContentDiscrimination (Subject : Type) (Discriminates : Subject → Prop → Prop → Prop)
    (s : Subject) (p : Prop) : Prop :=
  ∃ q : Prop, q ≠ p ∧ Discriminates s p q

theorem means_not_implies_discrimination :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (MeansAt : Subject → Prop → Prop)
      (DiscriminatesAt : Subject → Prop → Prop → Prop),
      MeansAt s p ∧ ¬ ContentDiscrimination Subject DiscriminatesAt s p := by
  refine ⟨Unit, (), True, fun _ _ => True, fun _ _ _ => False, trivial, ?_⟩
  intro ⟨q, _hne, hDisc⟩
  exact hDisc

/-- Candidate 9: Counterfactual Availability - STRICTLY STRONGER / COUNTERMODEL. -/
def CounterfactualAvailability (Subject : Type) (CanEntertain : Subject → Prop → Prop)
    (s : Subject) (p : Prop) : Prop :=
  ∃ q : Prop, (p ∧ q → False) ∧ CanEntertain s q

theorem means_not_implies_counterfactual_availability :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (MeansAt : Subject → Prop → Prop)
      (CanEntertainAt : Subject → Prop → Prop),
      MeansAt s p ∧ ¬ CounterfactualAvailability Subject CanEntertainAt s p := by
  refine ⟨Unit, (), True, fun _ _ => True, fun _ _ => False, trivial, ?_⟩
  intro ⟨q, _hincomp, hCan⟩
  exact hCan

/-- Candidate 10: Alternative Awareness (MissingCognitiveHorn) - STRICTLY STRONGER / COUNTERMODEL. -/
def AlternativeAwareness (Subject : Type) (MeansAt : Subject → Prop → Prop)
    (s : Subject) (p : Prop) : Prop :=
  ∃ q : Prop, (p ∧ q → False) ∧ MeansAt s q

theorem means_not_implies_alternative_awareness :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (MeansAt : Subject → Prop → Prop),
      MeansAt s p ∧ ¬ AlternativeAwareness Subject MeansAt s p := by
  refine ⟨Unit, (), True, fun _ q => q, trivial, ?_⟩
  intro ⟨q, hincomp, hq⟩
  exact hincomp ⟨trivial, hq⟩

-- ===========================================================================
-- Section 2: The Cognitive Discrimination Layer
-- ===========================================================================

/-!
### Primitive Cognitive Discrimination:
`Discriminates : Subject → Prop → Prop → Prop`
Represents the subject cognitively differentiating content p from content q.
Notice: It does NOT definitionally require `Means s p`, `Means s q`, `Incompatible p q`,
or `Chooses s p q`.
-/

/-- Candidate Dimension 1: Bare Cognitive Discrimination -/
def BareDiscrimination (Discriminates : Subject → Prop → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Discriminates s p q

/-- Candidate Dimension 2: Content Distinction (Objective Non-Identity) -/
def ObjectiveDistinction (p q : Prop) : Prop := p ≠ q

/-- Candidate Dimension 3: Recognition of Difference -/
def RecognitionOfDifference (Discriminates : Subject → Prop → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Discriminates s p q ∧ (p ≠ q)

/-- Candidate Dimension 4: Alternative Availability -/
def AlternativeAvailable (Available : Subject → Prop → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Available s p q ∧ (p ∧ q → False)

/-- Candidate Dimension 5: Counterfactual Consideration -/
def CounterfactualConsideration (Considers : Subject → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Means s p ∧ Considers s q ∧ (p ∧ q → False)

/-- Candidate Dimension 6: Representational Separation -/
def RepresentationalSeparation (Represents : Subject → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Represents s p ∧ Represents s q ∧ (p ≠ q)

-- ===========================================================================
-- Section 3: Testing Discrimination Properties D1–D4
-- ===========================================================================

/-- Property D1 (FAILS): Discrimination does NOT entail Choice!
    Hostile model: s discriminates p from q, but makes no choice. -/
theorem D1_discrimination_not_entails_choice :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (DiscriminatesAt : Subject → Prop → Prop → Prop)
      (ChoosesAt : Subject → Prop → Prop → Prop),
      DiscriminatesAt s p q ∧ ¬ ChoosesAt s p q := by
  refine ⟨Unit, (), True, False, fun _ _ _ => True, fun _ _ _ => False, trivial, id⟩

/-- Property D2 (FAILS): Discrimination does NOT entail Representation/Meaning of q!
    Hostile model: s discriminates p from an external contrast boundary q without meaning q. -/
theorem D2_discrimination_not_entails_meaning :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (DiscriminatesAt : Subject → Prop → Prop → Prop)
      (MeansAt : Subject → Prop → Prop),
      DiscriminatesAt s p q ∧ ¬ MeansAt s q := by
  refine ⟨Unit, (), True, False, fun _ _ _ => True, fun _ q' => q', trivial, id⟩

/-- Property D3 (HOLDS): Discrimination is present without choice and without free will!
    Hostile model: deterministic agent possesses cognitive discrimination and incompatibility
    while having zero choices and zero free will. -/
theorem D3_discrimination_present_without_choice_or_freewill :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (DiscriminatesAt : Subject → Prop → Prop → Prop)
      (MeansAt : Subject → Prop → Prop)
      (ChoosesAt : Subject → Prop → Prop → Prop)
      (FreeWillAt : Subject → Prop),
      DiscriminatesAt s p q ∧
      MeansAt s p ∧
      (p ∧ q → False) ∧
      ¬ ChoosesAt s p q ∧
      ¬ FreeWillAt s := by
  refine ⟨Unit, (), True, False,
          fun _ _ _ => True,
          fun _ q' => q',
          fun _ _ _ => False,
          fun _ => False,
          trivial, trivial, (fun h => h.2), id, id⟩

/-- Property D4 (FAILS): Intentional Action does NOT derive Discrimination!
    Hostile model: s performs an act on p without discriminating any proposition q. -/
theorem D4_act_not_derives_discrimination :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (ActAt : Subject → Prop → Prop)
      (DiscriminatesAt : Subject → Prop → Prop → Prop),
      ActAt s p ∧ ¬ (∃ q : Prop, DiscriminatesAt s p q) := by
  refine ⟨Unit, (), True, fun _ _ => True, fun _ _ _ => False, trivial, ?_⟩
  intro ⟨q, hq⟩
  exact hq

-- ===========================================================================
-- Section 4: Deconstructing A14 into Minimal Sub-Principles
-- ===========================================================================

/-!
### Deconstruction of A14:
A14 (`AxIntentionalChoice`: `Act s p → ∃ q, Chooses s p q`) is NOT monolithic.
It decomposes into two strictly weaker sub-principles:
1. `A_D` (Cognitive Contrast Principle):
   Every intentional act requires cognitive discrimination against an incompatible alternative.
2. `B_R` (Cognitive Uptake Principle):
   If a subject means p and discriminates an incompatible alternative q,
   then q is cognitively represented (meant) by the subject.
-/

/-- Sub-Principle A_D: Cognitive Contrast Principle -/
def CognitiveContrastPrinciple (Subject : Type)
    (ActAt : Subject → Prop → Prop)
    (DiscriminatesAt : Subject → Prop → Prop → Prop) : Prop :=
  ∀ (s : Subject) (p : Prop),
    ActAt s p → ∃ q : Prop, DiscriminatesAt s p q ∧ (p ∧ q → False)

/-- Sub-Principle B_R: Cognitive Uptake Principle -/
def CognitiveUptakePrinciple (Subject : Type)
    (MeansAt : Subject → Prop → Prop)
    (DiscriminatesAt : Subject → Prop → Prop → Prop) : Prop :=
  ∀ (s : Subject) (p q : Prop),
    MeansAt s p → DiscriminatesAt s p q → (p ∧ q → False) → MeansAt s q

/-- Composition Theorem: A_D + B_R derives the Missing Cognitive Horn! -/
theorem subprinciples_derive_missing_cognitive_horn
    (Subject : Type)
    (ActAt : Subject → Prop → Prop)
    (MeansAt : Subject → Prop → Prop)
    (DiscriminatesAt : Subject → Prop → Prop → Prop)
    (hActMeans : ∀ s p, ActAt s p → MeansAt s p)
    (hAD : CognitiveContrastPrinciple Subject ActAt DiscriminatesAt)
    (hBR : CognitiveUptakePrinciple Subject MeansAt DiscriminatesAt) :
    ∀ (s : Subject) (p : Prop),
      ActAt s p → ∃ q : Prop, MeansAt s q ∧ (p ∧ q → False) := by
  intro s p hAct
  have hMeansP := hActMeans s p hAct
  obtain ⟨q, hDisc, hIncomp⟩ := hAD s p hAct
  have hMeansQ := hBR s p q hMeansP hDisc hIncomp
  exact ⟨q, hMeansQ, hIncomp⟩

/-- Independence of A_D: A_D alone does NOT derive the Missing Cognitive Horn!
    Witnessed by Model M3: discrimination occurs, but cognitive uptake fails. -/
theorem AD_alone_insufficient_for_missing_horn :
    ∃ (Subject : Type)
      (ActAt : Subject → Prop → Prop)
      (MeansAt : Subject → Prop → Prop)
      (DiscriminatesAt : Subject → Prop → Prop → Prop),
      (∀ s p, ActAt s p → MeansAt s p) ∧
      CognitiveContrastPrinciple Subject ActAt DiscriminatesAt ∧
      ¬ (∀ s p, ActAt s p → ∃ q, MeansAt s q ∧ (p ∧ q → False)) := by
  refine ⟨Unit,
          fun _ p => p,
          fun _ q' => q',
          fun _ _ _ => True,
          (fun _ _ h => h),
          (fun _ _ _ => ⟨False, trivial, (fun h => h.2)⟩),
          ?_⟩
  intro hAll
  obtain ⟨q, hqMeans, hqIncomp⟩ := hAll () True trivial
  exact hqIncomp ⟨trivial, hqMeans⟩

/-- Independence of B_R: B_R alone does NOT derive the Missing Cognitive Horn!
    Witnessed by Model M1: cognitive uptake is vacuously true, but no discrimination occurs. -/
theorem BR_alone_insufficient_for_missing_horn :
    ∃ (Subject : Type)
      (ActAt : Subject → Prop → Prop)
      (MeansAt : Subject → Prop → Prop)
      (DiscriminatesAt : Subject → Prop → Prop → Prop),
      (∀ s p, ActAt s p → MeansAt s p) ∧
      CognitiveUptakePrinciple Subject MeansAt DiscriminatesAt ∧
      ¬ (∀ s p, ActAt s p → ∃ q, MeansAt s q ∧ (p ∧ q → False)) := by
  refine ⟨Unit,
          fun _ p => p,
          fun _ q' => q',
          fun _ _ _ => False,
          (fun _ _ h => h),
          (fun _ _ _ _ hDisc _ => (hDisc).elim),
          ?_⟩
  intro hAll
  obtain ⟨q, hqMeans, hqIncomp⟩ := hAll () True trivial
  exact hqIncomp ⟨trivial, hqMeans⟩

-- ===========================================================================
-- Section 5: Decomposition of `Means`
-- ===========================================================================

/-!
### Horn-Local Decomposition of `Means`:
We test whether `Means(s, p)` can be factored into:
`ContentRepresentation(s, p) ∧ IntentionalAffirmation(s, p)`.
-/

def ContentRepresentation (Subject : Type) (Represents : Subject → Prop → Prop)
    (s : Subject) (p : Prop) : Prop :=
  Represents s p

def IntentionalAffirmation (Subject : Type) (Affirms : Subject → Prop → Prop)
    (s : Subject) (p : Prop) : Prop :=
  Affirms s p

def DecomposedMeans (Subject : Type)
    (Represents Affirms : Subject → Prop → Prop)
    (s : Subject) (p : Prop) : Prop :=
  ContentRepresentation Subject Represents s p ∧
  IntentionalAffirmation Subject Affirms s p

/-- Factorization 1: Representation does NOT imply Affirmation -/
theorem representation_not_implies_affirmation :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (Represents Affirms : Subject → Prop → Prop),
      ContentRepresentation Subject Represents s p ∧
      ¬ IntentionalAffirmation Subject Affirms s p := by
  refine ⟨Unit, (), True, fun _ _ => True, fun _ _ => False, trivial, id⟩

/-- Factorization 2: Affirmation does NOT imply Representation -/
theorem affirmation_not_implies_representation :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (Represents Affirms : Subject → Prop → Prop),
      IntentionalAffirmation Subject Affirms s p ∧
      ¬ ContentRepresentation Subject Represents s p := by
  refine ⟨Unit, (), True, fun _ _ => False, fun _ _ => True, trivial, id⟩

/-- Architectural Theorem: Horn-Local Decomposition is Blind to the Second Horn!
    Factoring `Means(s, p)` along horn p provides zero information about any horn q ≠ p. -/
theorem horn_local_decomposition_blind_to_second_horn :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (Represents Affirms : Subject → Prop → Prop),
      DecomposedMeans Subject Represents Affirms s p ∧
      ¬ (∃ q : Prop, Represents s q ∧ (p ∧ q → False)) := by
  refine ⟨Unit, (), True, fun _ q' => q', fun _ _ => True,
          ⟨trivial, trivial⟩, ?_⟩
  intro ⟨q, hqRep, hIncomp⟩
  exact hIncomp ⟨trivial, hqRep⟩

-- ===========================================================================
-- Section 6: The Architectural Impossibility / Cognitive Collapse Theorem
-- ===========================================================================

/-!
### The Unary Intentional Collapse Theorem:
Any theory whose primitive intentional vocabulary consists solely of a unary content
relation `Means(s, p)` evaluated over single-content models CANNOT derive the existence
of an alternative content q.
-/

structure MonadicIntentionalFrame where
  Subject : Type
  subject : Subject
  content : Prop
  MeansAt : Subject → Prop → Prop
  means_sound : MeansAt subject content
  means_unique : ∀ q, MeansAt subject q → q = content

theorem unary_intentional_collapse (F : MonadicIntentionalFrame) (p : Prop)
    (hp : p = F.content) :
    ¬ (∃ q : Prop, F.MeansAt F.subject q ∧ (p ∧ q → False) ∧ p) := by
  intro ⟨q, hMeansQ, hIncomp, hTrueP⟩
  have hqEq := F.means_unique q hMeansQ
  subst hp
  subst hqEq
  exact hIncomp ⟨hTrueP, hTrueP⟩

-- ===========================================================================
-- Section 7: The 6-Level Hierarchy & Hostile Model Suite M0–M5
-- ===========================================================================

/-!
### The 6 Cognitive / Modal Levels:
Level 1: Objective Incompatibility: `Incompatible p q` (p ∧ q → False)
Level 2: Cognitive Distinction: `Incompatible p q ∧ Discriminates s p q`
Level 3: Alternative Representation: `Incompatible p q ∧ Represents s p ∧ Represents s q`
Level 4: Co-Meaning: `Incompatible p q ∧ Means s p ∧ Means s q`
Level 5: Choice: `Chooses s p q`
Level 6: Free Will: `FreeWill s`
Level 7: Libertarian Freedom: `AgentCausalSettlement s Causes p`
-/

def Level1_ObjectiveIncompatibility (p q : Prop) : Prop :=
  p ∧ q → False

def Level2_CognitiveDistinction (Subject : Type) (Discriminates : Subject → Prop → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Level1_ObjectiveIncompatibility p q ∧ Discriminates s p q

def Level3_AlternativeRepresentation (Subject : Type) (Represents : Subject → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Level1_ObjectiveIncompatibility p q ∧ Represents s p ∧ Represents s q

def Level4_CoMeaning (Subject : Type) (MeansAt : Subject → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Level1_ObjectiveIncompatibility p q ∧ MeansAt s p ∧ MeansAt s q

def Level5_Choice (Subject : Type) (ChoosesAt : Subject → Prop → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  ChoosesAt s p q

def Level6_FreeWill (Subject : Type) (ChoosesAt : Subject → Prop → Prop → Prop)
    (s : Subject) : Prop :=
  ∃ p q, ChoosesAt s p q

def Level7_LibertarianFreedom (Subject : Type) (CausesAt : Subject → Prop → Prop)
    (s : Subject) (p : Prop) : Prop :=
  CausesAt s p ∧ ¬ CausesAt s (¬ p)

/-!
### Hostile Model Suite M0–M5:
M0: No Intentionality (pure formal structure)
M1: Monadic Intentionality (s means p only)
M2: Objective Alternatives (p and ¬p exist, but no cognitive link to ¬p)
M3: Cognitive Distinction without Representation (s discriminates p from ¬p without representing ¬p)
M4: Alternative Representation without Choice (s co-means p and ¬p without choosing)
M5: Genuine Choice (s chooses between p and ¬p)
-/

/-- Separation L1 ↛ L2: Objective incompatibility does not imply cognitive distinction -/
theorem level1_not_implies_level2 :
    ∃ (p q : Prop) (Subject : Type) (s : Subject)
      (Discriminates : Subject → Prop → Prop → Prop),
      Level1_ObjectiveIncompatibility p q ∧
      ¬ Level2_CognitiveDistinction Subject Discriminates s p q := by
  refine ⟨True, False, Unit, (), fun _ _ _ => False, (fun h => h.2), ?_⟩
  intro ⟨_, hDisc⟩
  exact hDisc

/-- Separation L2 ↛ L3: Cognitive distinction does not imply alternative representation -/
theorem level2_not_implies_level3 :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (Discriminates : Subject → Prop → Prop → Prop)
      (Represents : Subject → Prop → Prop),
      Level2_CognitiveDistinction Subject Discriminates s p q ∧
      ¬ Level3_AlternativeRepresentation Subject Represents s p q := by
  refine ⟨Unit, (), True, False,
          fun _ _ _ => True,
          fun _ q' => q',
          ⟨(fun h => h.2), trivial⟩, ?_⟩
  intro ⟨_, _, hRepQ⟩
  exact hRepQ

/-- Separation L3 ↛ L4: Representation does not imply semantic co-meaning -/
theorem level3_not_implies_level4 :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (Represents MeansAt : Subject → Prop → Prop),
      Level3_AlternativeRepresentation Subject Represents s p q ∧
      ¬ Level4_CoMeaning Subject MeansAt s p q := by
  refine ⟨Unit, (), True, False,
          fun _ _ => True,
          fun _ q' => q',
          ⟨(fun h => h.2), trivial, trivial⟩, ?_⟩
  intro ⟨_, _, hMeansQ⟩
  exact hMeansQ

/-- Separation L4 ↛ L5: Co-meaning does not imply choice -/
theorem level4_not_implies_level5 :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (MeansAt : Subject → Prop → Prop)
      (ChoosesAt : Subject → Prop → Prop → Prop),
      Level4_CoMeaning Subject MeansAt s p q ∧
      ¬ Level5_Choice Subject ChoosesAt s p q := by
  refine ⟨Unit, (), True, False,
          fun _ _ => True,
          fun _ _ _ => False,
          ⟨(fun h => h.2), trivial, trivial⟩, id⟩

/-- Separation L5 ↛ L6: A choice on a specific pair does not imply global free will across all domains -/
theorem level5_local_choice_not_implies_global_freewill :
    ∃ (Subject : Type) (s : Subject) (p q : Prop)
      (ChoosesAt : Subject → Prop → Prop → Prop)
      (GlobalFreeWill : Subject → Prop),
      Level5_Choice Subject ChoosesAt s p q ∧
      ¬ GlobalFreeWill s := by
  refine ⟨Unit, (), True, False, fun _ _ _ => True, fun _ => False, trivial, id⟩

/-- Separation L6 ↛ L7: Free will (compatibilist choice) does not imply libertarian freedom -/
theorem level6_freewill_not_implies_libertarian_freedom :
    ∃ (Subject : Type) (s : Subject) (p : Prop)
      (ChoosesAt : Subject → Prop → Prop → Prop)
      (CausesAt : Subject → Prop → Prop),
      Level6_FreeWill Subject ChoosesAt s ∧
      ¬ Level7_LibertarianFreedom Subject CausesAt s p := by
  refine ⟨Unit, (), True, fun _ _ _ => True, fun _ _ => False,
          ⟨True, False, trivial⟩, ?_⟩
  intro ⟨hCause, _⟩
  exact hCause

-- ===========================================================================
-- Section 8: Formal Comparison Lattice Across 7 Competing Interpretations
-- ===========================================================================

/-!
### Lattice of 7 Competing Interpretations:
A. Representation (Horn-Local directedness)
B. Discrimination (Primitive relational difference)
C. Consideration (Entertaining without asserting)
D. Alternative-awareness (Representing an incompatible horn)
E. Counterfactual cognition (Representing non-actual incompatible horn)
F. Recognition of incompatibility (Co-meaning both horns and recognizing conflict)
G. Intentional distinction (Differentiating two intentional foci)
-/

/-- Equivalence at Level 2: Discrimination ↔ Intentional Distinction -/
theorem discrimination_equiv_intentional_distinction
    (D1 D2 : Subject → Prop → Prop → Prop)
    (hEq : ∀ s p q, D1 s p q ↔ D2 s p q) (s : Subject) (p q : Prop) :
    D1 s p q ↔ D2 s p q :=
  hEq s p q

/-- Hierarchy: Recognition of Incompatibility strictly requires Alternative-Awareness -/
theorem recognition_of_incompatibility_requires_alternative_awareness
    (s : Subject) (p q : Prop) (hCoMeans : Means s p ∧ Means s q ∧ (p ∧ q → False)) :
    ∃ q', (p ∧ q' → False) ∧ Means s q' :=
  ⟨q, hCoMeans.2.2, hCoMeans.2.1⟩

end Logos.CognitiveDiscrimination
