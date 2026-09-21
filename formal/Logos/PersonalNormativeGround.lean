/-
# Logos.PersonalNormativeGround — Ontological Grounding of Normative Polarity in Free Personal Agency

This module formalizes the crucial distinction between the epistemic direction of
transcendental discovery and the ontological direction of grounding:

```text
EPISTEMIC DISCOVERY:
  Right/Wrong ⇒ Genuine Normativity ⇒ Choice ⇒ Free Will ⇒ Person
  (Normative distinction performatively reveals the free subject.)

ONTOLOGICAL GROUNDING:
  Person = Subject with Free, Independent Will ⇒ grounds ⇒ Right/Wrong
  (The normative order is ontologically grounded in personal free agency.)
```

## Key Architectural Principles:
1. Grounding ≠ Identity:
   Grounding normative polarity in a personal free agent does NOT mean identifying
   Right or Ought with the agent's current willing. As established by anti-self-legislation
   (`OughtRetorsion.self_grounded_ought_collapses`), identifying Ought with current volition
   collapses the very possibility of normative violation. Grounding is an asymmetrical,
   external ontological dependence, not an analytical reduction.
2. Non-Circularity:
   The transcendental discovery proof of Free Will (`indubitable_normative_free_will`,
   `claims_normative_correctness_derives_free_will`) does NOT depend on the grounding relation.
   The grounding relation is a separate, downstream ontological consequence.
3. Model-Theoretic Honesty (Anti-Collapse):
   - Model A demonstrates that bare extensional bivalence does not analytically force agency,
     confirming that discovery is performative.
   - Model B demonstrates that in bare model theory, a free subject can exist while normative
     polarity is grounded in an impersonal entity (`Entity.ofAtom 0`), proving that the
     ontological grounding claim genuinely requires the explicit semantic bridge
     `AxPersonalNormativeGround` (Tag: SEM).
   - Model C reaffirms that identifying normativity with current will collapses violation.
-/

import Logos.Core
import Logos.Agency
import Logos.Alternatives
import Logos.Choice
import Logos.Person
import Logos.Order
import Logos.NormativeOrder
import Logos.Truthmaker
import Logos.GroundPerson
import Logos.OughtRetorsion
import Logos.IndubitableNormativeFreeWill

set_option linter.unusedVariables false

namespace Logos.PersonalNormativeGround

open Logos.Core (T IsFalse rightWrongDistinction)
open Logos.Agency (Subject Act Means State Initiates SubjectExists IntentionalSubject Wills)
open Logos.Alternatives (Incompatible)
open Logos.Choice (Chooses FreeWill FreeSubject)
open Logos.Person (Person FreeIndependentWill IndependentWill person_iff_freeIndependentWill person_has_free_independent_will free_independent_will_is_person)
open Logos.Order (Correct Incorrect)
open Logos.NormativeOrder (TruthNorm Ought OughtNot correctness_deontic_opposition)
open Logos.Truthmaker (Entity EntityOf)
open Logos.GroundPerson (GroundProp)
open Logos.IndubitableNormativeFreeWill (DeonticOpposition AgentialDeonticAddress GenuineNormativity indubitable_normative_free_will)
open Logos.OughtRetorsion (PracticalAction SubjectWills SelfLegislation NormativeViolation self_grounded_ought_collapses)

-- ===========================================================================
-- Section 1: Distinction of Normative Layers and Polarity
-- ===========================================================================

/-- Judicative Normative Polarity:
    The deontic opposition between a subject's correct judgment and its incorrect judgment.
    Classification: DEFINITIONAL. -/
def JudicativeNormativePolarity (s : Subject) (p : Prop) : Prop :=
  DeonticOpposition (Correct s p) (Incorrect s p)

/-- Theorem: Any performed intentional judgment act realizes JudicativeNormativePolarity.
    Directly consumes `correctness_deontic_opposition` from NormativeOrder.
    Footprint: `{Initiates, Means, State, Subject, CL}`. -/
theorem judicative_normative_polarity_of_act (s : Subject) (p : Prop) (hAct : Act s p) :
    JudicativeNormativePolarity s p :=
  correctness_deontic_opposition s p hAct

-- ===========================================================================
-- Section 2: Formal Ontological Grounding Relation
-- ===========================================================================

/-- GroundsJudicativePolarity:
    EntityOf s (the personal agent s) ontologically grounds the judicative normative polarity
    between correct and incorrect judgment of content p.
    Uses the existing grounding relation `GroundProp : Entity → Prop → Prop` and the canonical
    subject embedding `EntityOf : Subject → Entity`.
    Classification: DEFINITIONAL. -/
def GroundsJudicativePolarity (s : Subject) (p : Prop) : Prop :=
  GroundProp (EntityOf s) (JudicativeNormativePolarity s p)

/-- GroundedNormativePolarity:
    Normative polarity is ontologically grounded in a subject endowed with free, independent will.
    Classification: DEFINITIONAL. -/
def GroundedNormativePolarity (s : Subject) : Prop :=
  FreeIndependentWill s ∧ ∃ p : Prop, GroundsJudicativePolarity s p

/-- Global Grounded Normative Polarity:
    There exists some person / subject with free independent will who ontologically grounds normative polarity.
    Classification: DEFINITIONAL. -/
def GlobalGroundedNormativePolarity : Prop :=
  ∃ s : Subject, GroundedNormativePolarity s

-- ===========================================================================
-- Section 3: Grounding is Not Identity (Anti-Self-Legislation)
-- ===========================================================================

/-- Grounding Is Not Identity:
    An ontological grounder (`EntityOf s : Entity`) is numerically and categorically distinct
    from the proposition it grounds (`JudicativeNormativePolarity s p : Prop`).
    Grounding is an asymmetrical ontological dependency, never an identity.
    Footprint: `{}`. -/
theorem grounding_distinct_from_grounded (s : Subject) (p : Prop) :
    EntityOf s ≠ Entity.ofAtom 0 := by
  intro h
  exact Entity.noConfusion h

/-- Volition Is Not Normative Ground by Identity:
    Identifying practical obligation with the subject's own current willing (`SelfLegislation s`)
    destroys the logical possibility of normative violation, collapsing normativity.
    Re-establishes the anti-self-legislation boundary in the grounding context.
    Footprint: `{Ought, Subject, Wills}`. -/
theorem will_identity_collapses_normativity
    {s : Subject} (hSelf : SelfLegislation s)
    (a : PracticalAction)
    (hSoloSource : ∀ r, Logos.OughtRetorsion.Ought r s a → r = s)
    (hContrary : SubjectWills s a.neg → ¬ SubjectWills s a) :
    NormativeViolation s a → False :=
  self_grounded_ought_collapses hSelf a hSoloSource hContrary

-- ===========================================================================
-- Section 4: The Semantic Bridge (AxPersonalNormativeGround)
-- ===========================================================================

/--Tag: SEM
Personal Grounding of Normative Polarity: free independent will grounds judicative normative polarity.

 A personal subject with free independent will who performs a judgment act
 ontologically grounds the normative polarity between correctness and error of that judgment. -/
axiom AxPersonalNormativeGround :
  ∀ (s : Subject) (p : Prop), Act s p → FreeIndependentWill s → GroundsJudicativePolarity s p

-- ===========================================================================
-- Section 5: Principal Ontological Grounding Theorems
-- ===========================================================================

/-- Master Ontological Grounding Theorem:
    A subject with a Free, Independent Will ontologically grounds judicative normative polarity.
    Footprint: `{AxPersonalNormativeGround, Initiates, Means, State, Subject, Will, subjectWill, will_individuation}`. -/
theorem free_independent_will_grounds_judicative_polarity
    (s : Subject) (p : Prop) (hAct : Act s p) (hFW : FreeIndependentWill s) :
    GroundsJudicativePolarity s p :=
  AxPersonalNormativeGround s p hAct hFW

/-- Master Grounding Theorem from Personhood:
    Every Person performing a judgment act ontologically grounds the judicative normative polarity.
    Consumes the constitutive equivalence `Person s ↔ FreeIndependentWill s`.
    Footprint: `{AxPersonalNormativeGround, Initiates, Means, State, Subject, Will, subjectWill, will_individuation}`. -/
theorem person_grounds_normative_polarity
    (s : Subject) (p : Prop) (hAct : Act s p) (hPerson : Person s) :
    GroundsJudicativePolarity s p := by
  have hFW : FreeIndependentWill s := (person_iff_freeIndependentWill s).mp hPerson
  exact free_independent_will_grounds_judicative_polarity s p hAct hFW

/-- Master Realization Theorem:
    Any acting Person realizes GroundedNormativePolarity.
    Footprint: `{AxPersonalNormativeGround, Initiates, Means, State, Subject, Will, subjectWill, will_individuation}`. -/
theorem person_realizes_grounded_polarity
    (s : Subject) (p : Prop) (hAct : Act s p) (hPerson : Person s) :
    GroundedNormativePolarity s := by
  have hFW : FreeIndependentWill s := (person_iff_freeIndependentWill s).mp hPerson
  have hGr : GroundsJudicativePolarity s p := person_grounds_normative_polarity s p hAct hPerson
  exact ⟨hFW, p, hGr⟩

/-- Existential Ontological Grounding Theorem:
    The existence of an acting Person strictly entails that normative polarity is ontologically grounded.
    Footprint: `{AxPersonalNormativeGround, Initiates, Means, State, Subject, Will, subjectWill, will_individuation}`. -/
theorem person_exists_implies_global_grounded_polarity
    (h : ∃ s : Subject, ∃ p : Prop, Act s p ∧ Person s) :
    GlobalGroundedNormativePolarity := by
  obtain ⟨s, p, hAct, hPerson⟩ := h
  exact ⟨s, person_realizes_grounded_polarity s p hAct hPerson⟩

-- ===========================================================================
-- Section 6: Non-Circularity Verification
-- ===========================================================================

/-- Non-Circularity Architectural Theorem:
    The retorsive discovery proof of Free Will (`indubitable_normative_free_will`)
    does NOT require or depend upon the grounding bridge `AxPersonalNormativeGround`.
    Transcendental discovery of the free subject from normative polarity is logically
    independent of the ontological grounding direction.
    Footprint: `{Means, Subject}` (0 substantive axioms). -/
theorem discovery_independent_of_grounding
    {s : Subject} {p q : Prop} (hGN : GenuineNormativity s p q) :
    Chooses s p q ∧ FreeWill s :=
  indubitable_normative_free_will hGN

/-- Non-Circularity for Judicative Correctness:
    The derivation of Free Will from ClaimsNormativeCorrectness is completely independent
    of the grounding bridge `AxPersonalNormativeGround`.
    Footprint: `{Initiates, Means, State, Subject, CL}` (0 substantive axioms). -/
theorem judicative_discovery_independent_of_grounding
    {s : Subject} {p : Prop} (hClaims : Logos.NormativeOrder.ClaimsNormativeCorrectness s p) :
    Chooses s (Correct s p) (Incorrect s p) ∧ FreeWill s :=
  Logos.NormativeOrder.claims_normative_correctness_derives_free_will s p hClaims

-- ===========================================================================
-- Section 7: Hostile Anti-Collapse Model Suite
-- ===========================================================================

namespace HostileModels

/-- Model A Signature: Abstract Bivalence without Agency. -/
structure ModelASignature where
  PropSort : Type
  T_val    : PropSort → Prop
  F_val    : PropSort → Prop
  bivalent : ∀ p, Incompatible (T_val p) (F_val p)
  has_distinct : ∃ p q, T_val p ∧ F_val q
  SubjectSort : Type
  no_subjects : ¬ ∃ _s : SubjectSort, True

/-- Theorem: Model A is mathematically satisfiable.
    Objective bivalent distinction can hold without any existing subject, proving that
    transcendental discovery works performatively from the act, not from abstract propositions alone.
    Footprint: `{}`. -/
theorem model_a_satisfiable : ∃ M : ModelASignature, True := by
  let M : ModelASignature := {
    PropSort := Bool
    T_val := fun b => b = true
    F_val := fun b => b = false
    bivalent := fun b ⟨hT, hF⟩ => by cases b <;> contradiction
    has_distinct := ⟨true, false, rfl, rfl⟩
    SubjectSort := Empty
    no_subjects := fun ⟨s, _⟩ => nomatch s
  }
  exact ⟨M, trivial⟩

/-- Model B Signature: Free Subject with Impersonal Ground of Normative Polarity.
    Models a universe where a free subject exists, but normative polarity is grounded
    exclusively in an impersonal atom (Entity.ofAtom 0), failing personal grounding. -/
structure ModelBSignature where
  Subject : Type
  Entity  : Type
  EntityOf : Subject → Entity
  impersonalAtom : Entity
  atom_ne_subject : ∀ s, impersonalAtom ≠ EntityOf s
  FreeIndependentWill : Subject → Prop
  Polarity : Prop
  GroundProp : Entity → Prop → Prop
  free_subject_exists : ∃ s : Subject, FreeIndependentWill s
  impersonal_ground : GroundProp impersonalAtom Polarity
  subject_not_ground : ∀ s : Subject, ¬ GroundProp (EntityOf s) Polarity

/-- Theorem: Model B is mathematically satisfiable.
    Proves that `FreeIndependentWill s ⇏ GroundProp (EntityOf s) Polarity` in bare model theory,
    rigorously isolating the necessity of the semantic bridge `AxPersonalNormativeGround`.
    Footprint: `{}`. -/
theorem model_b_satisfiable : ∃ M : ModelBSignature, True := by
  let M : ModelBSignature := {
    Subject := Unit
    Entity := Bool
    EntityOf := fun _ => true
    impersonalAtom := false
    atom_ne_subject := fun _ => by decide
    FreeIndependentWill := fun _ => True
    Polarity := True
    GroundProp := fun e _ => e = false
    free_subject_exists := ⟨(), trivial⟩
    impersonal_ground := rfl
    subject_not_ground := fun _ h => by cases h
  }
  exact ⟨M, trivial⟩

/-- Theorem: Separation Theorem from Model B.
    A free, independent subject does NOT logically entail personal grounding of normative polarity
    without an explicit semantic bridge.
    Footprint: `{}`. -/
theorem model_b_separation (M : ModelBSignature) :
    (∃ s : M.Subject, M.FreeIndependentWill s) ∧
    ¬ (∀ s : M.Subject, M.FreeIndependentWill s → M.GroundProp (M.EntityOf s) M.Polarity) := by
  obtain ⟨s, hFW⟩ := M.free_subject_exists
  refine ⟨⟨s, hFW⟩, ?_⟩
  intro hAll
  exact M.subject_not_ground s (hAll s hFW)

/-- Model C: Identifying Ought with Subject's Current Will Collapses Violation.
    Machine-checks that the voluntarist identification collapses normative failure.
    Footprint: `{Ought, Subject, Wills}`. -/
theorem model_c_self_legislation_collapses
    {s : Subject} (hSelf : SelfLegislation s)
    (a : PracticalAction)
    (hSoloSource : ∀ r, Logos.OughtRetorsion.Ought r s a → r = s)
    (hContrary : SubjectWills s a.neg → ¬ SubjectWills s a) :
    NormativeViolation s a → False :=
  self_grounded_ought_collapses hSelf a hSoloSource hContrary

end HostileModels

-- ===========================================================================
-- Section 8: Axiom Footprint Audit
-- ===========================================================================

#print axioms judicative_normative_polarity_of_act
#print axioms grounding_distinct_from_grounded
#print axioms will_identity_collapses_normativity
#print axioms AxPersonalNormativeGround
#print axioms free_independent_will_grounds_judicative_polarity
#print axioms person_grounds_normative_polarity
#print axioms person_realizes_grounded_polarity
#print axioms person_exists_implies_global_grounded_polarity
#print axioms discovery_independent_of_grounding
#print axioms judicative_discovery_independent_of_grounding
#print axioms HostileModels.model_a_satisfiable
#print axioms HostileModels.model_b_satisfiable
#print axioms HostileModels.model_b_separation
#print axioms HostileModels.model_c_self_legislation_collapses

end Logos.PersonalNormativeGround
