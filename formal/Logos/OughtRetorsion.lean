/-
# Logos.OughtRetorsion — Retorsive Investigation of Practical Ought and Personhood

This module investigates whether genuine objective practical normativity (`Ought r s a`)
retorsively forces a personal normative source distinct from a lone Free Subject, or whether
the singleton impersonal model is mathematically coherent.

Methodological Discipline:
1. Pure Deontic Notion:
   `Ought r s a` is an independent primitive relation between an addresser r, an addressee s,
   and a practical action a. It is NOT defined in terms of epistemic correctness (`ClaimsCorrect`),
   mere intention (`Means`), or will (`Wills`).
2. Independent Violation:
   `NormativeViolation s a` is defined as having an obligation to do `a` while willing `a.neg`.
   This is logically consistent in deontic logic, permitting real failure of duty.
3. Anti-Self-Legislation Retorsion:
   If an agent's obligation is exhausted by its own will (`Ought s s a ↔ Wills s a`),
   then willing `a.neg` dissolves the obligation, making violation impossible.
   This collapses objective normativity into subjective inclination.
4. Impersonal Platonist Countermodel:
   A lone Free Subject governed by an objective practical ought is consistent with
   having no second person (`¬ ∃ s₁ s₂, s₁ ≠ s₂`), proving that `ObjectiveOught ⇏ Plurality`
   by pure logic alone.
5. Second-Personal Bridge (Tag: META):
   Deriving interpersonal plurality from practical obligation explicitly requires the
   relational bridge `AxSecondPersonalAddress` (META).
-/

import Logos.Core
import Logos.Agency
import Logos.Alternatives
import Logos.Choice
import Logos.Person
import Logos.Value
import Logos.Semantics
import Logos.RetorsiveNormativity
import Logos.IndubitableNormativeFreeWill
import Logos.DirectNormativeRetorsion

namespace Logos.OughtRetorsion

open Logos.Core (T IsFalse rightWrongDistinction)
open Logos.Agency (Subject Act Means SubjectExists IntentionalSubject Wills)
open Logos.Alternatives (Incompatible)
open Logos.Choice (Chooses FreeWill FreeSubject)
open Logos.Person (Person person_is_intentional)
open Logos.Value (Alone)

-- ============================================================================
-- 1. Core Signatures: Practical Action and Deontic Ought
-- ============================================================================

/-- Practical action type: candidate actions an agent may deliberate upon or execute. -/
structure PracticalAction where
  prop : Prop

/-- The negation of a practical action (refraining or doing the opposite). -/
def PracticalAction.neg (a : PracticalAction) : PracticalAction :=
  ⟨¬ a.prop⟩

/-- Volition/Will of an agent toward an action: uses the primitive `Wills` from `Agency`. -/
def SubjectWills (s : Subject) (a : PracticalAction) : Prop :=
  Logos.Agency.Wills s a.prop

/--Tag: VOCAB
Vocabulary: primitive deontic obligation relation between source, agent, and action.

 Deontic Ought relation: `Ought r s a` expresses that source r places
    subject s under an objective practical obligation concerning action a.
    This relation is primitive and explicitly deontic: it is NOT defined in terms of
    what s means, what s wills, what s claims, or what is epistemically true. -/
axiom Ought : Subject → Subject → PracticalAction → Prop

/-- Objective Practical Ought for subject s: some source r obligates s to do a.
    Does not assume by definition that r ≠ s or that r is a distinct person. -/
def ObjectiveOught (s : Subject) (a : PracticalAction) : Prop :=
  ∃ r : Subject, Ought r s a

/-- Second-Personal Ought: subject s is obligated by a distinct source r (r ≠ s). -/
def SecondPersonalOught (r s : Subject) (a : PracticalAction) : Prop :=
  Ought r s a ∧ r ≠ s

/-- Normative Violation: subject s is under an objective practical obligation to do a,
    yet s actively wills the contrary (a.neg).
    Under this independent definition, violation is logically possible:
    `ObjectiveOught s a` and `SubjectWills s a.neg` do not contradict each other definitionally. -/
def NormativeViolation (s : Subject) (a : PracticalAction) : Prop :=
  ObjectiveOught s a ∧ SubjectWills s a.neg

/-- Theorem: Logical Possibility of Normative Violation.
    There exists a coherent interpretation where an agent violates an objective obligation.
    Footprint: `{}`. -/
theorem violation_is_logically_possible :
    ∃ (Subj : Type) (O : Subj → Subj → Prop → Prop) (W : Subj → Prop → Prop) (s : Subj) (p : Prop),
      (∃ r, O r s p) ∧ W s (¬p) :=
  ⟨Unit, fun _ _ _ => True, fun _ _ => True, (), True, ⟨(), trivial⟩, trivial⟩

-- ============================================================================
-- 2. Anti-Self-Legislation Retorsion (Self-Grounded Normativity Collapses)
-- ============================================================================

/-- Self-Legislation Hypothesis: the hypothesis that the bindingness of an obligation
    for subject s is completely grounded in and exhausted by s's own will. -/
def SelfLegislation (s : Subject) : Prop :=
  ∀ a : PracticalAction, Ought s s a ↔ SubjectWills s a

/-- Theorem: Self-Legislation Precludes Normative Violation.
    If practical obligation is exhausted by the subject's own will, then whenever the
    subject wills the contrary (SubjectWills s a.neg), the original obligation evaporates.
    Consequently, genuine normative violation is logically impossible.
    Footprint: `{Ought, Subject, Wills}` (zero substantive axioms). -/
theorem self_grounded_ought_collapses
    {s : Subject} (hSelf : SelfLegislation s)
    (a : PracticalAction)
    (hSoloSource : ∀ r, Ought r s a → r = s)
    (hContrary : SubjectWills s a.neg → ¬ SubjectWills s a) :
    NormativeViolation s a → False := by
  intro ⟨⟨r, hOught⟩, hWillsNeg⟩
  have hrEq := hSoloSource r hOught
  rw [hrEq] at hOught
  have hWillsA := (hSelf a).mp hOught
  have hNotWillsA := hContrary hWillsNeg
  exact hNotWillsA hWillsA

/-- Theorem: Performative Incoherence of Asserting Self-Legislation.
    Asserting that an act is objectively obligatory while claiming that its obligatoriness
    is identical to one's own will collapses the distinction between duty and preference.
    Footprint: `{Ought, Subject, Wills}` (zero substantive axioms). -/
theorem self_grounded_assertion_incoherent
    {s : Subject} {a : PracticalAction}
    (hOught : Ought s s a)
    (hSelf : SelfLegislation s)
    (hWillsNeg : SubjectWills s a.neg)
    (hContrary : SubjectWills s a.neg → ¬ SubjectWills s a) :
    False := by
  have hWillsA := (hSelf a).mp hOught
  have hNotWillsA := hContrary hWillsNeg
  exact hNotWillsA hWillsA

-- ============================================================================
-- 3. The Hostile Impersonal Platonist Countermodel
-- ============================================================================

/-- Impersonal Normative Ground: an abstract normative reality (e.g. Platonist moral realm)
    that grounds objective practical obligations without being a second person. -/
structure ImpersonalNormativeGround where
  normativeOrderExists : Prop
  isObjective : Prop
  isImpersonal : Prop

namespace HostileImpersonalModel

/-- A universe containing exactly ONE subject. -/
abbrev S : Type := Unit

def soleSubject : S := ()

/-- The subject chooses between alternatives and has free will. -/
def Chooses (_s : S) (_p _q : Prop) : Prop := True
def FreeWill (_s : S) : Prop := True
def FreeSubject (_s : S) : Prop := True

/-- An impersonal normative ground (abstract moral law). -/
def PlatonistNorm : ImpersonalNormativeGround :=
  ⟨True, True, True⟩

/-- Objective practical ought holds for the sole subject without a second person. -/
def ObjectivePracticalOught (_s : S) (_a : PracticalAction) : Prop := True

/-- There is NO second subject in this universe. -/
theorem no_second_subject : ¬ (∃ s₁ s₂ : S, s₁ ≠ s₂) := by
  rintro ⟨s₁, s₂, hne⟩
  cases s₁; cases s₂
  exact hne rfl

/-- Theorem: The Impersonal Platonist Singleton Model is Mathematically Consistent.
    A lone free subject governed by an objective impersonal practical ought is completely
    consistent with bare logic and performative agency, without requiring a second person.
    Footprint: `{}` (strictly zero axioms). -/
theorem impersonal_model_satisfies_ought_without_person :
    (∃ _s : S, FreeSubject soleSubject ∧ ObjectivePracticalOught soleSubject ⟨True⟩) ∧
    (¬ ∃ s₁ s₂ : S, s₁ ≠ s₂) :=
  ⟨⟨(), trivial, trivial⟩, no_second_subject⟩

end HostileImpersonalModel

-- ============================================================================
-- 4. Retorsion Boundary Principle Analysis
-- ============================================================================

/-- Theorem: Retorsion Boundary on Personal Source.
    Asserting "No personal normative source exists" performatively instantiates the
    speaker's own intentional subjecthood (`IntentionalSubject s`), but does NOT
    performatively instantiate any distinct person `r ≠ s`.
    Footprint: `{Means, Subject, Will, subjectWill}` (zero substantive axioms). -/
theorem asserting_no_personal_source_instantiates_only_judging_subject
    {s : Subject}
    (hDenial : Means s (¬ ∃ r : Subject, Person r ∧ r ≠ s)) :
    IntentionalSubject s :=
  ⟨¬ ∃ r : Subject, Person r ∧ r ≠ s, hDenial⟩

-- ============================================================================
-- 5. The Second-Personal Address Bridge (Tag: META)
-- ============================================================================

/--Tag: META
AxSecondPersonalAddress (META): An objective practical ought that binds an agent with
    second-personal deontic accountability constitutively requires a distinct personal
    source who normatively addresses the agent.

 Philosophical price: This is a substantive meta-ethical / relational bridge (Anscombe-Darwall).
    The impersonal Platonist model proves that bare practical ought does not logically force
    a personal source; this bridge makes the relational personal requirement explicit. -/
axiom AxSecondPersonalAddress :
    (∀ s : Subject, ∀ a : PracticalAction,
      ObjectiveOught s a → ∃ r : Subject, Person r ∧ r ≠ s ∧ Ought r s a)

/-- Theorem: Derivation of Plurality from Objective Ought under AxSecondPersonalAddress.
    Under the second-personal address bridge, an objective practical ought derives a distinct
    person, establishing interpersonal plurality.
    Footprint: `{AxSecondPersonalAddress, Means, Ought, Subject, Will, subjectWill}`. -/
theorem second_personal_ought_derives_plurality
    {s : Subject} {a : PracticalAction}
    (hOught : ObjectiveOught s a) :
    ∃ r : Subject, Person r ∧ r ≠ s := by
  obtain ⟨r, hp, hne, _⟩ := AxSecondPersonalAddress s a hOught
  exact ⟨r, hp, hne⟩

/-- Theorem: A lone subject cannot possess second-personal practical ought under AxSecondPersonalAddress.
    Footprint: `{AxSecondPersonalAddress, Means, Ought, Subject, Will, subjectWill}`. -/
theorem lone_subject_excludes_second_personal_ought
    {s : Subject} (ha : Alone s) (a : PracticalAction) :
    ObjectiveOught s a → False := by
  intro hOught
  obtain ⟨r, _, hne⟩ := second_personal_ought_derives_plurality hOught
  have heq := ha r
  exact hne heq

-- ============================================================================
-- 6. Unified Personhood Theorem & Modal Independence
-- ============================================================================

/-- In the unified ontology, every Free Subject is a Person.
    Footprint: `{Means, Subject, Will, subjectWill, will_individuation}`. -/
theorem free_subject_is_person (s : Subject) (h : FreeSubject s) : Person s :=
  Logos.Person.free_subject_is_person s h

/-- Faithful modal model theorem: A person existing at the actual world does not logically
    force existence across all worlds without modal grounding bridges.
    Footprint: `{}`. -/
theorem faithful_contingent_person_fails_necessary_subject :
    ∃ (World : Type) (actualWorld : World) (Subj : Type)
      (ExistsAt : World → Subj → Prop) (P : Subj → Prop),
      (∃ s : Subj, P s ∧ ExistsAt actualWorld s) ∧
      ¬ (∀ s : Subj, P s → ∀ w : World, ExistsAt w s) := by
  refine ⟨Bool, true, Unit, fun w _ => w = true, fun _ => True, ⟨(), trivial, rfl⟩, ?_⟩
  intro h
  have hFalse := h () trivial false
  cases hFalse

-- ============================================================================
-- 7. Audit Block
-- ============================================================================

#print axioms Ought
#print axioms self_grounded_ought_collapses
#print axioms self_grounded_assertion_incoherent
#print axioms HostileImpersonalModel.impersonal_model_satisfies_ought_without_person
#print axioms asserting_no_personal_source_instantiates_only_judging_subject
#print axioms AxSecondPersonalAddress
#print axioms second_personal_ought_derives_plurality
#print axioms lone_subject_excludes_second_personal_ought
#print axioms free_subject_is_person
#print axioms faithful_contingent_person_fails_necessary_subject

end Logos.OughtRetorsion
