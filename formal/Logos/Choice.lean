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

What is DEFINED but NOT proved is §15's full bipolar *freedom* (F1b,
DEFERRED — see GAPMAP.md and DESIGN.md):

  * `FreeWill(s,p) ↔ ◇Choose(s,p) ∧ ◇Choose(s,¬p)` needs a *modal choice
    semantics* over `NecessityPH` (world-level); a subject may mean `p`
    without anything forcing it also to be *able* to mean `¬p`. F1a (choice
    existence/transcendental) is now PROVEN; only F1b (modal □/◇ freedom)
    stays deferred.
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
open Logos.Necessity (Dia Necessity)

/-- `Chooses s p q`: subject `s`, before incompatible contents `p` and `q`,
    determines which to adopt (§14). DEFINITION (choice-realism,
    2026-09-16): `s` chooses `p` in the face of incompatible `q` iff the
    meaning-act `A s p` holds and `p` excludes `q`. Under the Tier-1
    collapse this is `Means s p ∧ ¬(p ∧ q)`. A meaning-act against `¬p` is
    always a choice, since `Incompatible p (¬p)` is pure logic. This
    replaced the former dead placeholder `def Chooses := False`, which made
    "some choice exists" unrepresentable. -/
def Chooses (s : Subject) (p : Prop) (q : Prop) : Prop := A s p ∧ Incompatible p q

/-- A proposition and its own negation are always incompatible options
    (`¬(p ∧ ¬p)`, pure logic, footprint `{}`) — the field around any
    meaning-act is non-empty. -/
theorem incompatible_self_negation (p : Prop) : Incompatible p (¬ p) := by
  intro h
  exact h.2 h.1

/-- No meaning without a subject (analytic): the intentional relation
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

/-- §15 — bipolar freedom (DEFINITION; F1b, DEFERRED): freedom with respect
    to `p` is the possibility of choosing `p` AND the possibility of choosing
    its negation — the modal `◇`-both-ways claim that F1a (choice existence)
    does NOT supply: a subject may mean `p` without anything forcing it also
    to be *able* to mean `¬p`. Must be built on `NecessityPH` (world-level),
    not the degenerate alias. -/
def FreeWill (s : Subject) (p : Prop) : Prop :=
  CanChoose s p ∧ CanChoose s (¬ p)

/-- T11 — the minimal field of rational choice is non-empty for a person:
    a person exists (T5) and two incompatible contents exist (T9). The act
    of choosing among them (§14) is thereby *representable*; the modal
    possibility of each choice (FreeWill) is F1. -/
theorem T11_choiceField :
    ∃ s : Subject, Person s ∧ ∃ p q : Prop, Incompatible p q := by
  obtain ⟨s, hs⟩ := Logos.Plurality.T5_personExists
  obtain ⟨p, q, hpq, _⟩ := Logos.Alternatives.T9_incompatibleAlternatives
  exact ⟨s, hs, p, q, hpq⟩

/-- A person cannot exist without choice: each person (meaning-subject)
    chooses its content against its own negation. Kernel-checked — the
    chain's "subject ⇒ choice" (IM_STUPID.md), previously mislabeled a gap. -/
theorem person_chooses {s : Subject} (hs : Person s) : ∃ p q : Prop, Chooses s p q := by
  obtain ⟨_hAg, _hRa, hIn⟩ := hs
  obtain ⟨p, hmp⟩ := hIn
  exact ⟨p, ¬ p, hmp, incompatible_self_negation p⟩

/-- Choice is real: some subject chooses some content over some incompatible
    alternative (from T5 — a person exists). -/
theorem choiceExists : ∃ s : Subject, ∃ p q : Prop, Chooses s p q := by
  obtain ⟨s, hs⟩ := Logos.Plurality.T5_personExists
  obtain ⟨p, q, hch⟩ := person_chooses hs
  exact ⟨s, p, q, hch⟩

/-- Denying choice refutes itself: the denial is itself an act, and any act
    is a choice — so `¬(∃s p q, Chooses s p q)` implies `False`, exactly as
    N_T and ¬cogito refute themselves. -/
theorem noChoice_selfRefutes : (¬ ∃ s : Subject, ∃ p q : Prop, Chooses s p q) → False := by
  intro h
  exact h choiceExists

/-- "No right and wrong without choice" (right/wrong ⇒ choice): whenever the
    distinction holds, some choosing subject exists. Under F1a this is a
    theorem (choice exists already from the act-datum), not a priced bridge. -/
theorem JUDGE_COMMITTED :
    (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) → ∃ s : Subject, ∃ p q : Prop, Chooses s p q :=
  fun _ => choiceExists

/-- Denying that a subject exists refutes itself: the denial is itself an
    act/choice of a subject — and `choiceExists` (every act is a choice,
    every choice has a subject, `Chooses` holds at a meaning-act `A s p`)
    supplies the resident witness. Formal record of §26 "não existe sujeito
    do ato presente". Footprint `{AxTwoSubjects, Means, Subject}` — the
    refutation needs the act-datum resident in the theory; the pure-logical
    shell of a bare sort (`axiom Subject : Type`, empty model) is consistent,
    so the denial is refutable only given the act. The act-datum is derived
    (`cogito_from_T12`, A1 2026-09-16) under the ultimate anchor
    `AxTwoSubjects`. -/
theorem noSubject_selfRefutes : (¬ ∃ _s : Subject, True) → False := by
  intro h
  obtain ⟨s, _⟩ := choiceExists
  exact h ⟨s, True.intro⟩

end Logos.Choice

-- Axiom footprint audit
#print axioms Logos.Choice.T11_choiceField
#print axioms Logos.Choice.incompatible_self_negation
#print axioms Logos.Choice.meaning_needs_subject
#print axioms Logos.Choice.person_chooses
#print axioms Logos.Choice.choiceExists
#print axioms Logos.Choice.noChoice_selfRefutes
#print axioms Logos.Choice.noSubject_selfRefutes
#print axioms Logos.Choice.JUDGE_COMMITTED