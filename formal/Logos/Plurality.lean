/-
# Logos.Plurality — more than one person (poem P5/P7; theorem T12)

T12 — there are at least two distinct persons.
Reconstructed under hostile semantics: agency and personhood do not entail
plurality by logic alone (settled by the Unit countermodel in `HostileSemantics`).
Plurality is therefore derived under the explicit META bridge `AxTwoSubjects`.

Also hosts the Q2 bridge `EntityOf : Subject → Entity` (each person has an
entity-correlate), decided to close the Subject/Entity gap so the love layer
can attach necessity to the relata (T14).

The existence theorems `T1_subjectExists`, `T4_agentExists`, and `T5_personExists`
are anchored directly on the performative foundation `Agency.Cogito`.
`T12_twoPersons`, `notAlone`, and `T12_directedPair` are the genuine plurality
claims, standing honestly on `{AxTwoSubjects}`.
-/

import Logos.Core
import Logos.Agency
import Logos.Person
import Logos.Choice
import Logos.Value
import Logos.Entity

namespace Logos.Plurality

open Logos.Agency (Subject)
open Logos.Person (Person)
open Logos.Entity (Entity ExistsAt)
open Logos.Semantics (World)
open Logos.Value (AxTwoSubjects Affects PersonsAffectPrinciple)

/-- Q2 bridge: canonical embedding of subjects into the general entity type. -/
def EntityOf : Subject → Entity := Logos.Entity.EntityOf

/-- A subject is necessary iff its entity-correlate exists in every world. -/
def NecessarySubject (s : Subject) : Prop := ∀ w : World, ExistsAt w (EntityOf s)

/--There are at least two distinct persons.

  T12 — there is more than one person (poem P5/P7; PROVEN↑ under `AxTwoSubjects`):
    the reality of right-and-wrong demands plurality. A single act does not entail
    plurality (settled by the Unit countermodel in HostileSemantics). Footprint: `{AxTwoSubjects, Means, Subject, Will, subjectWill}`. -/
theorem T12_twoPersons :
    ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ :=
  AxTwoSubjects Logos.Core.rightWrongDistinction

/-- "Not alone": some pair of distinct persons exists (the same result,
    restated in the poem's vocabulary). -/
theorem notAlone : ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ :=
  T12_twoPersons

/--The intentional subject is exhibited from plurality: someone means something.

 cogito, RESTATED AS A COROLLARY OF PLURALITY: from the demonstrated
    pair of persons, an intentional meaning occurs. -/
theorem cogito_from_T12 : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Means s p := by
  obtain ⟨s₁, _, hp₁, _, _⟩ := T12_twoPersons
  obtain ⟨p, hmp⟩ := Logos.Person.person_is_intentional s₁ hp₁
  exact ⟨s₁, p, hmp⟩

/--At least one subject exists: derived from the performative act-datum.

  T1 (C21) — the subject of the present act exists:
  derived from the existence of an intentional act (C68) via the constitutive rule
  `act_requires_subject` (Case B). Footprint: `{Initiates, Means, State, Subject}` (VOCAB only; decoupled from AxTwoSubjects). -/
theorem T1_subjectExists (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Act s p) :
    ∃ s : Subject, Logos.Agency.SubjectExists s :=
  Logos.Agency.subject_exists_of_act h

/--At least one agent exists: someone who acts.

  T4 (C23) — the subject is an agent (`Agent` is analytical `:= True`):
  derived from the existence of an intentional act (C68 → C21). Footprint: `{Initiates, Means, State, Subject}`. -/
theorem T4_agentExists (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Act s p) :
    ∃ s : Subject, Logos.Agency.SubjectExists s ∧ Logos.Agency.Agent s := by
  obtain ⟨s, hs⟩ := T1_subjectExists h
  exact ⟨s, hs, trivial⟩

/--At least one intentional subject exists: someone who means content.
   Derived from the existence of an intentional act.
   Footprint: `{Initiates, Means, State, Subject}`. -/
theorem T5_intentionalSubjectExists (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Act s p) :
    ∃ s : Subject, Logos.Agency.IntentionalSubject s :=
  Logos.Person.intentionalSubject_exists_of_act h

/-- T1 derived from an intentional assertion. -/
theorem T1_of_assert {s : Subject} {p : Prop} (h : Logos.Agency.Asserts s p) :
    ∃ s' : Subject, Logos.Agency.SubjectExists s' :=
  Logos.Agency.subject_exists_of_assert h

/-- T4 derived from an intentional assertion. -/
theorem T4_of_assert {s : Subject} {p : Prop} (h : Logos.Agency.Asserts s p) :
    ∃ s' : Subject, Logos.Agency.SubjectExists s' ∧ Logos.Agency.Agent s' :=
  ⟨s, Logos.Agency.act_requires_subject s p (Logos.Agency.assertion_is_act h), trivial⟩

/-- An intentional subject exists from an intentional assertion. -/
theorem T5_intentional_of_assert {s : Subject} {p : Prop} (h : Logos.Agency.Asserts s p) :
    ∃ s' : Subject, Logos.Agency.IntentionalSubject s' :=
  ⟨s, Logos.Person.act_implies_intentionalSubject (Logos.Agency.assertion_is_act h)⟩

/-- Corollary of plurality under an initiation bridge: from two distinct persons and an initiation bridge, a subject exists. -/
theorem T1_subjectExists_from_plurality
    (hBridge : ∀ (s : Subject) (p : Prop), Logos.Agency.Means s p → ∃ w w' : Logos.Agency.State, Logos.Agency.Initiates s w w' p) :
    ∃ s : Subject, Logos.Agency.SubjectExists s := by
  obtain ⟨s₁, _, hp₁, _, _⟩ := T12_twoPersons
  obtain ⟨p, hmp⟩ := Logos.Person.person_is_intentional s₁ hp₁
  exact ⟨s₁, p, hmp, hBridge s₁ p hmp⟩

/-- Corollary of plurality under an initiation bridge: from two distinct persons and an initiation bridge, an agent exists. -/
theorem T4_agentExists_from_plurality
    (hBridge : ∀ (s : Subject) (p : Prop), Logos.Agency.Means s p → ∃ w w' : Logos.Agency.State, Logos.Agency.Initiates s w w' p) :
    ∃ s : Subject, Logos.Agency.SubjectExists s ∧ Logos.Agency.Agent s := by
  obtain ⟨s, hs⟩ := T1_subjectExists_from_plurality hBridge
  exact ⟨s, hs, trivial⟩

/-- Corollary of plurality: from two distinct persons, a person exists. -/
theorem T5_personExists_from_plurality : ∃ s : Subject, Person s := by
  obtain ⟨s₁, _, hp₁, _, _⟩ := T12_twoPersons
  exact ⟨s₁, hp₁⟩

/-- T12, directed form (chain node C47): the two-person pair can
    be oriented so that affectivity flows forward, conditional on PersonsAffectPrinciple. -/
theorem T12_directedPair_conditional
    (hAffect : Logos.Value.PersonsAffectPrinciple) :
    ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ Affects s₁ s₂ := by
  obtain ⟨p, q, hp, hq, hne⟩ := T12_twoPersons
  rcases hAffect p q hp hq hne with h1 | h2
  · exact ⟨p, q, hp, hq, hne, h1⟩
  · exact ⟨q, p, hq, hp, hne.symm, h2⟩

/-- Right-and-wrong commits a choice field: where there is truth and error,
    someone is before an incompatible pair.
    Footprint: `{AxTwoSubjects, Means, Subject, Will, subjectWill}`. -/
theorem JUDGE_HAS_CHOICE_FIELD (h : ¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) :
    ∃ s : Subject, ∃ p q : Prop, Logos.Choice.ChoiceField s p q := by
  obtain ⟨s₁, _, hp₁, _, _⟩ := Logos.Value.AxTwoSubjects h
  obtain ⟨p, q, hch⟩ := Logos.Person.person_hasChoiceField hp₁
  exact ⟨s₁, p, q, hch⟩

/-- Right-and-wrong implies someone who means.
    Footprint: `{AxTwoSubjects, Means, Subject, Will, subjectWill}`. -/
theorem rightWrong_implies_someone_means (h : ¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) :
    ∃ s : Subject, ∃ p : Prop, Logos.Agency.Means s p := by
  obtain ⟨s, p, _, hch⟩ := JUDGE_HAS_CHOICE_FIELD h
  exact ⟨s, p, hch.1⟩

end Logos.Plurality

-- Axiom footprint audit
#print axioms Logos.Plurality.T1_subjectExists
#print axioms Logos.Plurality.T4_agentExists
#print axioms Logos.Plurality.T5_intentionalSubjectExists
#print axioms Logos.Plurality.T12_twoPersons
#print axioms Logos.Plurality.T12_directedPair_conditional
#print axioms Logos.Plurality.cogito_from_T12
#print axioms Logos.Plurality.JUDGE_HAS_CHOICE_FIELD
#print axioms Logos.Plurality.rightWrong_implies_someone_means
