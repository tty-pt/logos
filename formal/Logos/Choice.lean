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

 T11 — the minimal field of rational choice is non-empty for a person:
    a person exists (T5) and two incompatible contents exist (T9). The act
    of choosing among them (§14) is thereby *representable*; the modal
    possibility of each choice (FreeWill) is F1. -/
theorem T11_choiceField :
    ∃ s : Subject, Person s ∧ ∃ p q : Prop, Incompatible p q := by
  obtain ⟨s, hs⟩ := Logos.Plurality.T5_personExists
  obtain ⟨p, q, hpq, _⟩ := Logos.Alternatives.T9_incompatibleAlternatives
  exact ⟨s, hs, p, q, hpq⟩

/--Any person chooses: a person always has two incompatible alternatives to choose between.

 A person cannot exist without choice: each person (meaning-subject)
    chooses its content against its own negation. Kernel-checked — the
    chain's "subject ⇒ choice" (IM_STUPID.md), previously mislabeled a gap. -/
theorem person_chooses {s : Subject} (hs : Person s) : ∃ p q : Prop, Chooses s p q := by
  obtain ⟨_hAg, _hRa, hIn⟩ := hs
  obtain ⟨p, hmp⟩ := hIn
  exact ⟨p, ¬ p, hmp, incompatible_self_negation p⟩

/--Choice exists: some subject chooses between two incompatible alternatives.

 Choice is real: some subject chooses some content over some incompatible
    alternative (from T5 — a person exists). -/
theorem choiceExists : ∃ s : Subject, ∃ p q : Prop, Chooses s p q := by
  obtain ⟨s, hs⟩ := Logos.Plurality.T5_personExists
  obtain ⟨p, q, hch⟩ := person_chooses hs
  exact ⟨s, p, q, hch⟩

/--Denying choice refutes itself: the denial is itself a choice.

 Denying choice refutes itself: the denial is itself an act, and any act
    is a choice — so `¬(∃s p q, Chooses s p q)` implies `False`, exactly as
    N_T and ¬cogito refute themselves. -/
theorem noChoice_selfRefutes : (¬ ∃ s : Subject, ∃ p q : Prop, Chooses s p q) → False := by
  intro h
  exact h choiceExists

/--Right-and-wrong commits a chooser: where there is truth and error, someone has chosen.

 "No right and wrong without choice" (right/wrong ⇒ choice): whenever the
    distinction holds, some choosing subject exists. Under F1a this is a
    theorem (choice exists already from the act-datum), not a priced bridge. -/
theorem JUDGE_COMMITTED :
    (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) → ∃ s : Subject, ∃ p q : Prop, Chooses s p q :=
  fun _ => choiceExists

/--Right-and-wrong implies someone who means (poem P3, line 18 "há certo e há
 errado → há significado → há alguém para quem algo significar").

 `JUDGE_COMMITTED` (C54) composes with `rightWrongDistinction` (C36,
    axiom-free — "há certo e há errado" is PROVEN) to yield a chooser; every
    choice is a meaning-act (`Chooses` unfolds to `A s p`; Tier-1 collapse
    `A := Means`), so some subject means some content. Footprint `{}` —
    the act-datum is now the exhibited theorem `Agency.Cogito`
    (definitional subject, 2026-09-17), which the "há certo e há errado"
    premises already embody performatively. The shorter analytic half
    ("significado → sujeito") is `meaning_needs_subject` (C49, vocab-only). -/
theorem rightWrong_implies_someone_means :
    (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) → ∃ s : Subject, ∃ p : Prop, Means s p := by
  intro h
  obtain ⟨s, p, q, hch⟩ := JUDGE_COMMITTED h
  exact ⟨s, p, hch.1⟩

/--Denying 'a subject exists' refutes itself: the denial is itself an act.

 Denying that a subject exists refutes itself: the denial is itself an
    act/choice of a subject — and `choiceExists` (every act is a choice,
    every choice has a subject, `Chooses` holds at a meaning-act `A s p`)
    supplies the resident witness. Formal record of §26 "não existe sujeito
    do ato presente". Footprint `{}` — the refutation needs the act-datum
    resident in the theory, now the exhibited theorem `Agency.Cogito`
    (definitional subject, 2026-09-17); the pure-logical shell of a bare
    sort (empty model) is consistent, so the denial is refutable only given
    the exhibited act. -/
theorem noSubject_selfRefutes : (¬ ∃ _s : Subject, True) → False := by
  intro h
  obtain ⟨s, _⟩ := choiceExists
  exact h ⟨s, True.intro⟩

-- ---------------------------------------------------------------------------
-- F1b — the freedom split (2026-09-17): the paradox resolved
--   "could not have chosen otherwise" cannot be asserted of the performer.
-- ---------------------------------------------------------------------------

/-- The silent origin means every content: `Means (inl ()) p` for every `p`
    (witness `⟨p, p, rfl⟩` — the origin initiates a movement positing `p`). -/
private theorem means_origin (p : Prop) : Means (Sum.inl ()) p :=
  ⟨p, p, rfl⟩

/-- A posited content means only itself: `Means (inr q) p` requires `q = p`. -/
private theorem means_posited_is_self (q p : Prop) (hm : Means (Sum.inr q) p) : q = p := by
  unfold Means at hm
  obtain ⟨w, w', hww⟩ := hm
  exact hww.1

/-- The origin can choose `p`: `CanChoose (inl ()) p` holds constructively —
    the origin's choice of `p` against `¬p` is real, witnessed by the
    meaning-act; `CanChoose` reduces to `¬∀w ¬⋯`, refuted at `someWorld`.
    Not via `canChoose_unfold` (which would cost `CL`). -/
private theorem canChoose_origin (p : Prop) : CanChoose (Sum.inl ()) p := by
  unfold CanChoose Dia
  intro hnec
  exact hnec someWorld ⟨¬ p, ⟨means_origin p, incompatible_self_negation p⟩⟩

/--The silent origin always could have chosen otherwise: it can choose p and can choose ¬p.

  `FreeWill (inl ()) p` for every `p`, kernel-checked, footprint `{}`.
    The freedom paradox-resolution (2026-09-17): the act's own subject — the
    origin, the `T5_personExists`/`Cogito` witness that `JUDGE_COMMITTED`
    commits to right-and-wrong — can both choose `p` and choose its
    negation. "Could not have chosen otherwise" is therefore false of the
    performer. GAPMAP F1b-weak. -/
theorem freeWillOrigin (p : Prop) : FreeWill (Sum.inl ()) p :=
  ⟨canChoose_origin p, canChoose_origin (¬ p)⟩

/-- A posited content that can choose `p` must be `p` itself (the only
    content `inr q` ever means). Double negation: `CL`. -/
private theorem canChoose_posited_is_self (q p : Prop) :
    CanChoose (Sum.inr q) p → q = p := by
  intro hc
  apply Classical.byContradiction
  intro hne
  unfold CanChoose Dia at hc
  exact hc (fun w hx => by
    obtain ⟨q', hch⟩ := hx
    exact hne (means_posited_is_self q p hch.1))

/--A posited content cannot choose otherwise: `¬ FreeWill (Sum.inr q) p` for every `p`.

  The self-posited contents are provably NOT free — `inr q` can only mean
    `q` itself (`Means (inr q) p` iff `q = p`), so both-ways capacity would
    force `q = p ∧ q = ¬p`, impossible (`p ≠ ¬p`). Footprint `CL` (double
    negation on the `CanChoose → q = p` extraction). Not a paradox: these
    subjects are never the judge that right-and-wrong commits (that witness
    is the free origin) — exactly why "a subject that could not have chosen
    otherwise" never contradicts the undeniable right/wrong. GAPMAP F1b-weak. -/
theorem noFreeWillPosited (q p : Prop) : ¬ FreeWill (Sum.inr q) p := by
  intro hFW
  have hsf : q = p := canChoose_posited_is_self q p hFW.1
  have hsc : q = ¬ p := canChoose_posited_is_self q (¬ p) hFW.2
  have hpneg : p = ¬ p := hsf.symm.trans hsc
  have hiff : p ↔ ¬ p := by
    constructor
    · intro hp
      exact hpneg ▸ hp
    · intro hnp
      exact hpneg.symm ▸ hnp
  have hnp : ¬ p := fun hp => (hiff.mp hp) hp
  have hp : p := hiff.mpr hnp
  exact (hiff.mp hp) hp

/--Denying that you could have chosen otherwise refutes itself: the denial is an act of the free origin.

  `¬ FreeWill (inl ()) p → False`, kernel-checked `{}` from `freeWillOrigin`.
    The agent that asserts "I could not have chosen otherwise" is the origin
    of the present act — the cogito witness — and its assertion is itself a
    both-ways capacity the denial disowns. This dissolves the freedom
    paradox: the determinist alternative cannot be asserted performatively.
    GAPMAP F1b-weak. -/
theorem originFreedomSelfRefutes (p : Prop) : (¬ FreeWill (Sum.inl ()) p) → False := by
  intro h
  exact h (freeWillOrigin p)

/--The chooser that right-and-wrong commits is free: some person can choose both ways.

  `JUDGE_COMMITTED`'s judge is the origin (`T5_personExists`'s witness is
    `inl ()`), and the origin is free (`freeWillOrigin`) — so choice-in-the-
    freedom-sense exists for the very subject the undeniable right/wrong
    commits. Kernel-checked, footprint `{}`. GAPMAP F1b-weak. -/
theorem judgeIsFree : ∃ s : Subject, Person s ∧ ∃ p : Prop, FreeWill s p :=
  ⟨Sum.inl (), ⟨trivial, trivial, ⟨True, means_origin True⟩⟩, True, freeWillOrigin True⟩

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
#print axioms Logos.Choice.freeWillOrigin
#print axioms Logos.Choice.noFreeWillPosited
#print axioms Logos.Choice.originFreedomSelfRefutes
#print axioms Logos.Choice.judgeIsFree
