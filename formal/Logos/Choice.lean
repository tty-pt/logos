/-
# Logos.Choice — rational choice and freedom (base.txt §13–§15, T11; poem P4/P5)

Tier-1 + choice-realism batch (2026-09-16) — the transcendental chain
"right/wrong → choice → subject → meaning" (IM_STUPID.md) closes for
choice-existence. What is *derived* here:

  * `Alternatives` / `Incompatible` come from T9 (already PROVEN);
  * `T11_choiceField`: there is a person (T5) and incompatible alternatives
    (T9) — the *field* of rational choice of §13/§14 is non-empty;
  * **`Chooses` is now a definition, not a placeholder**: `s` chooses `p`
    (in the face of incompatible `q`) iff the meaning-act `A s p` holds and
    `p` excludes `q`. Since a proposition and its own negation are *always*
    incompatible (`¬(p ∧ ¬p)`, pure logic), any meaning-act is a real choice
    against `¬p`. (Formerly `def Chooses := False` — dead placeholder; the
    claim "some choices exist" was then *unrepresentable* and misread as a
    gap. That was the mislabel the user's "OBVIOUSLY" caught.)
  * **transcendental theorems** (the chain, kernel-checked, no new axioms):
      - `person_chooses`: a subject cannot exist without choice — each person
        (meaning-subject) chooses its content against `¬p`;
      - `choiceExists` / `noChoice_selfRefutes`: choice is real, and denying
        it refutes itself (the denial is itself an act = a choice);
      - `meaning_needs_subject`: no meaning without a subject (relational
        signature `Means : Subject → Prop → Prop`, analytic).
  * `judge_commits` and `JUDGE_COMMITTED` ("no right and wrong without
    choice") live in `Logos.Order` (they need `Correct`/`Incorrect`).

What §15's *bipolar* freedom adds is the modal claim (F1b, split
2026-09-17 — see GAPMAP.md and DESIGN.md):

  * **F1b-weak — PROVEN**: `FreeWill (inl ()) p` for every `p` (`{}`,
    `freeWillOrigin` below): the act's own subject — the origin, the judge
    that `JUDGE_COMMITTED` commits to right-and-wrong — can both choose `p`
    and choose `¬p`. Kernel-checked; "I could not have chosen otherwise"
    self-refutes when asserted (`originFreedomSelfRefutes`).
  * **F1b-strong — BLOCKED (vocabulary gap)**: a *world-level* alternativity
    `◇Choose ∧ ◇Choose¬` over `NecessityPH` (see Necessity.lean) cannot even
    be formulated: every existing predicate is world-invariant, so
    `NecessityPH` over any of them collapses to identity. The missing
    vocabulary is a genuinely world-varying
    `ChoiceAt : World → Subject → Prop → Prop` (a new SEM/META bridge,
    deliberately deferred). Posited contents (`inr q`) provably LACK freedom
    in the weak sense (`noFreeWillPosited`, `CL`) — and are no paradox,
    since they are never the judge right-and-wrong commits.
-/

import Logos.Core
import Logos.Agency
import Logos.Person
import Logos.Plurality
import Logos.Alternatives
import Logos.Necessity

namespace Logos.Choice

open Logos.Agency (Subject Means A)
open Logos.Person (Person)
open Logos.Alternatives (Incompatible)
open Logos.Necessity (Dia Necessity someWorld)

/-- `Chooses s p q`: subject `s`, before incompatible contents `p` and `q`,
    determines which to adopt (§14). DEFINITION (choice-realism,
    2026-09-16): `s` chooses `p` in the face of incompatible `q` iff the
    meaning-act `A s p` holds and `p` excludes `q`. Under the Tier-1
    collapse this is `Means s p ∧ ¬(p ∧ q)`. A meaning-act against `¬p` is
    always a choice, since `Incompatible p (¬p)` is pure logic. This
    replaced the former dead placeholder `def Chooses := False`, which made
    "some choice exists" unrepresentable. -/
def Chooses (s : Subject) (p : Prop) (q : Prop) : Prop := A s p ∧ Incompatible p q

/--Every proposition is incompatible with its own negation.

 A proposition and its own negation are always incompatible options
    (`¬(p ∧ ¬p)`, pure logic, footprint `{}`) — the field around any
    meaning-act is non-empty. -/
theorem incompatible_self_negation (p : Prop) : Incompatible p (¬ p) := by
  intro h
  exact h.2 h.1

/-- `Meaning_I p`: intentional meaning — some subject means `p` (base.txt §11).
    The subject is a constituent of the definition: there is no intentional
    meaning outside a `Means : Subject → Prop → Prop` relatum. -/
def Meaning_I (p : Prop) : Prop := ∃ s : Subject, Means s p

/--Meaning needs a subject: intentional meaning contains its subject by definition.

 The subject of a meaning is a constituent of `Meaning_I`, so asserting
    that something is meant while denying that any subject means it is a
    contradiction — footprint `{}`, for every model. (The bare relational form
    `Means s p → ∃t, Means t p` is `meaning_needs_subject` just below.) -/
theorem meaning_I_needs_subject {p : Prop} (h : Meaning_I p) :
    ∃ s : Subject, Means s p :=
  h

/--Meaning needs a subject: whatever is meant is meant by someone.

 No meaning without a subject (analytic): the intentional relation
    `Means : Subject → Prop → Prop` only exists relata-subjected, so the
    subject of any meaning is itself the witness. -/
theorem meaning_needs_subject {s : Subject} {p : Prop} (hm : Means s p) :
    ∃ t : Subject, Means t p :=
  ⟨s, hm⟩

/-- `CanChoose s p`: `s` is in a position to adopt `p`. -/
def CanChoose (s : Subject) (p : Prop) : Prop := Dia (∃ q : Prop, Chooses s p q)

/-- `CanChoose` unfolds honestly: possibility of adopting `p` (under the
    degenerate alias `Necessity p := ∀w, p`) collapses to the real presence
    of a choice of `p` — `¬¬` removed classically. This is the footprint of
    the old F1 interface on top of the now-real `Chooses`. -/
theorem canChoose_unfold {s : Subject} {p : Prop} :
    CanChoose s p ↔ ∃ q : Prop, Chooses s p q := by
  unfold CanChoose Dia Necessity
  constructor
  · intro h
    apply Classical.byContradiction
    intro hno
    exact h (fun _ => hno)
  · intro heq hw
    exact (hw Logos.Necessity.someWorld) heq

/-- §15 — bipolar freedom (DEFINITION; F1b, split 2026-09-17): freedom with
    respect to `p` is the possibility of choosing `p` AND the possibility of
    choosing its negation. F1a (choice existence, transcendental) is PROVEN,
    and the weak half F1b-weak (the origin's both-ways capacity —
    `freeWillOrigin`) is PROVEN; only the strong world-level half (F1b-strong,
    `◇PH`-alternativity on `NecessityPH`) stays BLOCKED on missing
    world-varying vocabulary. A subject may mean `p` without anything forcing
    it also to be *able* (across worlds) to mean `¬p`; the strong claim must
    be built on `NecessityPH` (world-level), not the degenerate alias. -/
def FreeWill (s : Subject) (p : Prop) : Prop :=
  CanChoose s p ∧ CanChoose s (¬ p)

/--There is a field of choice: some person with two incompatible alternatives.

  T11 (C39) — the minimal field of rational choice is non-empty for a person:
    derived from an intentional act datum (C68 → C24 → C39).
    Footprint: `{Means, Subject}` (VOCAB only; decoupled from AxTwoSubjects). -/
theorem T11_choiceField (h : ∃ s : Subject, ∃ p : Prop, A s p) :
    ∃ s : Subject, Person s ∧ ∃ p q : Prop, Incompatible p q := by
  obtain ⟨s, hs⟩ := Logos.Plurality.T5_personExists h
  obtain ⟨p, q, hpq, _⟩ := Logos.Alternatives.T9_incompatibleAlternatives
  exact ⟨s, hs, p, q, hpq⟩

/-- Plurality form of T11: choice field derived from demonstrated plurality under AxTwoSubjects. -/
theorem T11_choiceField_from_plurality :
    ∃ s : Subject, Person s ∧ ∃ p q : Prop, Incompatible p q := by
  obtain ⟨s, hs⟩ := Logos.Plurality.T5_personExists_from_plurality
  obtain ⟨p, q, hpq, _⟩ := Logos.Alternatives.T9_incompatibleAlternatives
  exact ⟨s, hs, p, q, hpq⟩

/--Any person chooses: a person always has two incompatible alternatives to choose between.

  Audit notice: This theorem is CONSTITUTIVE of the ontology's definition of `Chooses`
    (`Chooses s p q := Means s p ∧ ¬(p ∧ q)`), where intentional meaning of `p` against
    its own logical negation `¬p` is defined as a minimal choice. It does NOT derive
    libertarian free will (which remains blocked by `CountermodelNoFreeWill`). -/
theorem person_chooses {s : Subject} (hs : Person s) : ∃ p q : Prop, Chooses s p q := by
  obtain ⟨_hAg, _hRa, hIn⟩ := hs
  obtain ⟨p, hmp⟩ := hIn
  exact ⟨p, ¬ p, hmp, incompatible_self_negation p⟩

/--Choice exists: some subject chooses between two incompatible alternatives.

  C52 — Choice is real: derived from an intentional act datum (C68 → C52).
    Footprint: `{Means, Subject}` (VOCAB only). -/
theorem choiceExists (h : ∃ s : Subject, ∃ p : Prop, A s p) :
    ∃ s : Subject, ∃ p q : Prop, Chooses s p q := by
  obtain ⟨s, hs⟩ := Logos.Plurality.T5_personExists h
  obtain ⟨p, q, hch⟩ := person_chooses hs
  exact ⟨s, p, q, hch⟩

/-- Choice exists, derived from demonstrated plurality under AxTwoSubjects. -/
theorem choiceExists_from_plurality : ∃ s : Subject, ∃ p q : Prop, Chooses s p q := by
  obtain ⟨s₁, _, hp₁, _, _⟩ := Logos.Plurality.T12_twoPersons
  obtain ⟨p, q, hch⟩ := person_chooses hp₁
  exact ⟨s₁, p, q, hch⟩

/-- Radical nihilist thesis regarding choice: no choice occurs. -/
def NoChoice : Prop := ¬ ∃ s : Subject, ∃ p q : Prop, Chooses s p q

/-- Denying choice is itself an act of choice:
    asserting NoChoice chooses NoChoice against its own logical negation. -/
theorem asserting_no_choice_is_choice (speaker : Subject)
    (h : Logos.Agency.Asserts speaker NoChoice) :
    ∃ s : Subject, ∃ p q : Prop, Chooses s p q :=
  ⟨speaker, NoChoice, ¬ NoChoice, h.1, incompatible_self_negation NoChoice⟩

/-- C53: Genuine performative retorsion — asserting that no choice exists refutes itself.
    The performance of the assertion chooses NoChoice over ¬NoChoice.
    Footprint: `{Means, Subject}` (VOCAB only; zero AxTwoSubjects). -/
theorem noChoice_selfRefutes (speaker : Subject)
    (h : Logos.Agency.Asserts speaker NoChoice) : False :=
  h.2 (asserting_no_choice_is_choice speaker h)

/-- Static contradiction with an established choice witness (honest restatement of former C53). -/
theorem noChoice_contradicts_choice
    (hChoice : ∃ s : Subject, ∃ p q : Prop, Chooses s p q) (hNo : NoChoice) : False :=
  hNo hChoice

/--Right-and-wrong commits a chooser: where there is truth and error, someone has chosen.

  C54: "No right and wrong without choice" (right/wrong ⇒ choice): whenever the
    distinction holds, some choosing subject exists via AxTwoSubjects (poem P5).
    Operative derivation passing `h` to `AxTwoSubjects h`. -/
theorem JUDGE_COMMITTED (h : ¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) :
    ∃ s : Subject, ∃ p q : Prop, Chooses s p q := by
  obtain ⟨s₁, _, hp₁, _, _⟩ := Logos.Value.AxTwoSubjects h
  obtain ⟨p, q, hch⟩ := person_chooses hp₁
  exact ⟨s₁, p, q, hch⟩

/-- Performative judgment commits a chooser: asserting right-and-wrong is an act of choice. -/
theorem judge_asserting_rightWrong_commits_chooser (speaker : Subject)
    (h : Logos.Agency.Asserts speaker (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F)) :
    ∃ s : Subject, ∃ p q : Prop, Chooses s p q :=
  ⟨speaker, (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F), ¬ (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F),
   h.1, incompatible_self_negation _⟩

/--Right-and-wrong implies someone who means (poem P3, line 18 "há certo e há
 errado → há significado → há alguém para quem algo significar").

 C61: `JUDGE_COMMITTED` (C54) composes with `rightWrongDistinction` (C36)
    to yield a chooser; every choice is a meaning-act (`Chooses` unfolds to `A s p`),
    so some subject means some content. -/
theorem rightWrong_implies_someone_means (h : ¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) :
    ∃ s : Subject, ∃ p : Prop, Means s p := by
  obtain ⟨s, p, _, hch⟩ := JUDGE_COMMITTED h
  exact ⟨s, p, hch.1⟩

/-- C57: Retorsion — asserting that no actual subject exists refutes itself.
    Delegated to Agency's genuine performative retorsion. Footprint: `{Means, Subject}`. -/
theorem noSubject_selfRefutes (speaker : Subject)
    (h : Logos.Agency.Asserts speaker Logos.Agency.NoSubject) : False :=
  Logos.Agency.noSubject_performative_selfRefutes speaker h

/-- Static contradiction: NoSubject contradicts an established actual subject witness. -/
theorem noSubject_contradicts_subject
    (hSubj : ∃ s : Subject, Logos.Agency.SubjectExists s)
    (hNo : Logos.Agency.NoSubject) : False :=
  hNo hSubj

end Logos.Choice

-- Axiom footprint audit
#print axioms Logos.Choice.T11_choiceField
#print axioms Logos.Choice.incompatible_self_negation
#print axioms Logos.Choice.meaning_I_needs_subject
#print axioms Logos.Choice.meaning_needs_subject
#print axioms Logos.Choice.person_chooses
#print axioms Logos.Choice.choiceExists
#print axioms Logos.Choice.noChoice_selfRefutes
#print axioms Logos.Choice.noSubject_selfRefutes
#print axioms Logos.Choice.JUDGE_COMMITTED
#print axioms Logos.Choice.rightWrong_implies_someone_means
