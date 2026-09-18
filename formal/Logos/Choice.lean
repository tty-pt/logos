/-
# Logos.Choice — rational choice-field and freedom (base.txt §13–§15, T11; poem P4/P5)

Choice-realism batch (2026-09-16), **repaired 2026-09-18** (freedom/choice fix):
the relation formerly named `Chooses` was a *determined occurrence*, not a
choice. With `Chooses s p q := A s p ∧ Incompatible p q` and
`Incompatible p (¬p)` pure logic, `∃ q, Chooses s p q` collapses to `A s p`:
the agent was never related to the rejected horn. The repair splits the
vocabulary into two relations and a definitional freedom:

  * `ChoiceField s p q := A s p ∧ Incompatible p q` — **representability/field**:
    the agent's act is set against an incompatible content. This is the old
    occurrence relation; it is PROVEN for any meaning-act (C51/C52 field form)
    but is *not* a choice.
  * `Chooses s p q := A s p ∧ A s q ∧ Incompatible p q` — **genuine choice**:
    the agent holds *both* incompatible contents (adopts `p` while `q` is
    co-meant). `∃ q, Chooses s p q` is no longer `A s p`.
  * `FreeWill s := ∃ p q, Chooses s p q` — freedom is *definitional* from
    genuine choice (`chooses_implies_freeWill`, footprint `{Means, Subject}` —
    VOCAB only: the logical content is free, the vocabulary is the statement's
    own). The old
    bipolar `FreeWill s p := CanChoose s p ∧ CanChoose s (¬p)` (which unfolds
    to `A s p ∧ A s (¬ p)`) is subsumed by the unary `FreeWill s`.

The exact missing step (F1b, BLOCKED) is the co-meaning of the rejected horn:

    rejectedHornCoMeant :
      (∃ s : Subject, ∃ p : Prop, A s p) →
      ∃ s : Subject, ∃ p : Prop, A s p ∧ A s (¬ p)

Nothing in the tree forces one meaning-act to come with the meaning of its
negation: `Means` is an opaque relation (`Agency.lean`), and `AxTwoSubjects`
yields two *different* subjects, each with a single content. Hence the
*existence* of a genuine chooser is blocked, while the implication
choice → freedom is free. The explicit target is declared as the
`def`-proposition `genuineChoice_exists` (F1b, BLOCKED) and the frontier is
the theorem `freeWillExists_of_genuineChoice : genuineChoice_exists →
∃ s, FreeWill s` — the first implication is the substantive step still to
establish. This replaces the vague "world-varying
alternativity" wording with the prop-level statement; the world-level
`ChoiceAt : World → Subject → Prop → Prop` remains the (future) SEM bridge.

What is *derived* here (field form, unchanged footprints):
  * `person_hasChoiceField`: a person is before an incompatible pair;
  * `choiceField_exists` / `choiceField_exists_from_plurality`: the field is real;
  * `noChoiceField_selfRefutes`: denying the field is itself a field-act;
  * `JUDGE_HAS_CHOICE_FIELD`: right/wrong commits a choice-field.
  * `judge_commits` (field form) lives in `Logos.Order`.
-/

import Logos.Core
import Logos.Agency
import Logos.Person
import Logos.Plurality
import Logos.Alternatives
import Logos.Necessity

namespace Logos.Choice

open Logos.Agency (Subject Means A Asserts)
open Logos.Person (Person)
open Logos.Alternatives (Incompatible)
open Logos.Necessity (Dia Necessity someWorld)

/-- `ChoiceField s p q`: the choice *field* — subject `s` performs a meaning-act
    on `p` against an incompatible content `q` (§13–§14 representability).
    DEFINITION (choice-realism, 2026-09-16; renamed 2026-09-18): this is the
    old `Chooses` body `A s p ∧ Incompatible p q`. It records that an act
    occurs before an incompatible pair; it does NOT relate the agent to `q`,
    so it is not a selection. Genuine choice is `Chooses` below. -/
def ChoiceField (s : Subject) (p : Prop) (q : Prop) : Prop := A s p ∧ Incompatible p q

/-- `Chooses s p q`: subject `s` genuinely chooses between incompatible
    contents `p` and `q` (§14). DEFINITION (freedom/choice fix, 2026-09-18):
    `s` adopts `p` *while `q` is co-meant* — the agent holds both horns. This
    is strictly stronger than `ChoiceField`, which only relates `s` to `p`.
    It does not merely encode that an outcome occurred: `∃ q, Chooses s p q`
    now requires a second, incompatible content the subject relates to. -/
def Chooses (s : Subject) (p : Prop) (q : Prop) : Prop :=
  A s p ∧ A s q ∧ Incompatible p q

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

/-- `CanChoose s p`: `s` is in a position to genuinely adopt `p` (to select it
    against some incompatible alternative). -/
def CanChoose (s : Subject) (p : Prop) : Prop := Dia (∃ q : Prop, Chooses s p q)

/-- `CanChoose` unfolds honestly: possibility of adopting `p` (under the
    degenerate alias `Necessity p := ∀w, p`) collapses to the real presence
    of a genuine choice of `p` — `¬¬` removed classically. -/
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

/-- §15 — freedom (DEFINITION; freedom/choice fix, 2026-09-18): a subject is
    free iff it genuinely chooses between some incompatible pair. The
    implication choice → freedom is definitional (`chooses_implies_freeWill`).
    The *existence* half is BLOCKED on the exact missing lemma
    `rejectedHornCoMeant` (no axiom forces `A s p` to come with `A s (¬p)`),
    so `freeWillExists` is not derivable unconditionally; see the module
    header and GAPMAP F1b. -/
def FreeWill (s : Subject) : Prop := ∃ p q : Prop, Chooses s p q

/--Genuine choice entails freedom — by definition.

  Footprint `{Means, Subject}` (VOCAB only — the statement's own vocabulary;
    the logical content is free). This is the repair's core: freedom is
    *conceptually/definitionally* the existence of a genuine choice between
    incompatible alternatives, not a further metaphysical step from a bare act. -/
theorem chooses_implies_freeWill {s : Subject} {p q : Prop}
    (h : Chooses s p q) : FreeWill s :=
  ⟨p, q, h⟩

/--Freedom exists as soon as a genuine choice witness is supplied. This is the
    formal shape of the target `freeWillExists`; it is *conditional* because
    the unconditional witness is exactly the blocked `rejectedHornCoMeant`. -/
theorem freeWillExists_of_chooses (h : ∃ s : Subject, ∃ p q : Prop, Chooses s p q) :
    ∃ s : Subject, FreeWill s := by
  obtain ⟨s, p, q, hc⟩ := h
  exact ⟨s, chooses_implies_freeWill hc⟩

/--The precise missing lemma of the freedom frontier (F1b, BLOCKED): a genuine
    chooser exists — some subject co-meaning two incompatible contents.

  This is the explicit existence target: `∃ s : Subject, ∃ p q : Prop,
    Chooses s p q`. It is NOT yet derived from the performative datum — the
    exact route is `rejectedHornCoMeant` (nothing forces a meaning-act `A s p`
    to come with `A s (¬ p)`; `AxTwoSubjects` yields two *different* subjects,
    each with one content). It is a `def`-proposition, not a theorem: adding
    it as an axiom or `sorry` is forbidden; the deduction ledger records it as
    BLOCKED. The free direction below is `freeWillExists_of_genuineChoice`. -/
def genuineChoice_exists : Prop := ∃ s : Subject, ∃ p q : Prop, Chooses s p q

/--The precise missing resource (F1b, BLOCKED): one subject co-meaning a content
    and its negation — the same-subject dual meaning-act.

  `rejectedHornCoMeant : ∃ s p, A s p ∧ A s (¬ p)` — the single irreducible
     resource of the freedom frontier (hostile milestone, 2026-09-18). Every
     candidate route collapses onto it: the performative act is a *single*
     meaning (`Act s p := Means s p`), asserting p is truth-laden
     (`Asserts s p := Act s p ∧ p`, so no one can assert both horns,
     `assertion_consistency`), meaning can be *veridical* in a model
     (`Means s p → p` kills co-meaning, `genuineChoice_requires_error_possibility`),
     and even plurality + right-and-wrong give only `ChoiceField` (one horn
     co-meant against pure logic). It is a `def`-proposition, not a theorem:
     adding it as an axiom is forbidden; DEDUCTION records it BLOCKED. Its
     consequent is exactly `genuineChoice_exists`
     (`rejectedHornCoMeant_implies_genuineChoice`). -/
def rejectedHornCoMeant : Prop := ∃ s : Subject, ∃ p : Prop, A s p ∧ A s (¬ p)

/--The formal frontier: genuine choice implies free will.

  `freeWillExists` FOLLOWS from `genuineChoice_exists` — definitional
     (`FreeWill s := ∃ p q, Chooses s p q`) — and is never used as a premise.
     The missing substance is `genuineChoice_exists` itself (F1b, BLOCKED on
     `rejectedHornCoMeant`). Footprint: `{Means, Subject}` (VOCAB only). -/
theorem freeWillExists_of_genuineChoice : genuineChoice_exists → ∃ s : Subject, FreeWill s := by
  intro h
  exact freeWillExists_of_chooses h

/--Co-meaning a negation is the minimal frontier: it suffices for genuine choice.

  The single resource of F1b (`rejectedHornCoMeant`) yields the full target:
     from `A s p ∧ A s (¬ p)` genuine choice follows by `q := ¬ p`
     (`incompatible_self_negation`). Footprint: `{Means, Subject}` (VOCAB
     only). The converse is not needed: a genuine choice may use any
     incompatible pair, but the negation-pair is always the canonical one. -/
theorem rejectedHornCoMeant_implies_genuineChoice :
    rejectedHornCoMeant → genuineChoice_exists := by
  rintro ⟨s, p, hmp, hmn⟩
  exact ⟨s, p, ¬ p, hmp, hmn, incompatible_self_negation p⟩

/--Genuine choice forces the non-veridicality of meaning.

  A genuine chooser (`genuineChoice_exists`) contradicts veridical meaning
     `∀ s p, Means s p → p`: co-meaning two incompatible contents would then
     yield a true contradiction. Hence the frontier is exactly the
     *error-possibility* of `Means` — a resource no axiom supplies. This is
     the formal core of hostile milestone 2026-09-18. Footprint:
     `{Means, Subject}` (VOCAB only; pure logic over the relation). -/
theorem genuineChoice_requires_error_possibility :
    genuineChoice_exists → ¬ (∀ s : Subject, ∀ p : Prop, Means s p → p) := by
  intro hgc hver
  rcases hgc with ⟨s, p, q, hmp, hmq, hI⟩
  exact hI ⟨hver s p hmp, hver s q hmq⟩

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

/--Any person has a choice field: a person is always before two incompatible alternatives.

  Audit notice (freedom/choice fix, 2026-09-18): this yields `ChoiceField`, NOT
    genuine `Chooses`. The agent is related only to the adopted content `p`; the
    rejected horn `¬p` is supplied by pure logic (`incompatible_self_negation`),
    not by the agent. The genuine form (both horns co-meant) is BLOCKED on
    `rejectedHornCoMeant`. -/
theorem person_hasChoiceField {s : Subject} (hs : Person s) : ∃ p q : Prop, ChoiceField s p q := by
  obtain ⟨_hAg, _hRa, hIn⟩ := hs
  obtain ⟨p, hmp⟩ := hIn
  exact ⟨p, ¬ p, hmp, incompatible_self_negation p⟩

/--The choice field exists: some subject is before two incompatible alternatives.

  C52 (field form) — the field is real: derived from an intentional act datum
    (C68 → C52). Footprint: `{Means, Subject}` (VOCAB only). -/
theorem choiceField_exists (h : ∃ s : Subject, ∃ p : Prop, A s p) :
    ∃ s : Subject, ∃ p q : Prop, ChoiceField s p q := by
  obtain ⟨s, hs⟩ := Logos.Plurality.T5_personExists h
  obtain ⟨p, q, hch⟩ := person_hasChoiceField hs
  exact ⟨s, p, q, hch⟩

/-- Choice field exists, derived from demonstrated plurality under AxTwoSubjects. -/
theorem choiceField_exists_from_plurality : ∃ s : Subject, ∃ p q : Prop, ChoiceField s p q := by
  obtain ⟨s₁, _, hp₁, _, _⟩ := Logos.Plurality.T12_twoPersons
  obtain ⟨p, q, hch⟩ := person_hasChoiceField hp₁
  exact ⟨s₁, p, q, hch⟩

/-- Radical nihilist thesis regarding the choice field: no field occurs. -/
def NoChoiceField : Prop := ¬ ∃ s : Subject, ∃ p q : Prop, ChoiceField s p q

/-- Denying the choice field is itself an act of choice-field:
    asserting NoChoiceField sets the assertion against its own logical negation. -/
theorem asserting_noChoiceField_is_choiceField (speaker : Subject)
    (h : Logos.Agency.Asserts speaker NoChoiceField) :
    ∃ s : Subject, ∃ p q : Prop, ChoiceField s p q :=
  ⟨speaker, NoChoiceField, ¬ NoChoiceField, h.1, incompatible_self_negation NoChoiceField⟩

/-- C53 (field form): performative retorsion — asserting that no choice field exists
    refutes itself. Footprint: `{Means, Subject}` (VOCAB only; zero AxTwoSubjects). -/
theorem noChoiceField_selfRefutes (speaker : Subject)
    (h : Logos.Agency.Asserts speaker NoChoiceField) : False :=
  h.2 (asserting_noChoiceField_is_choiceField speaker h)

/-- Static contradiction with an established choice-field witness. -/
theorem noChoiceField_contradicts_field
    (hField : ∃ s : Subject, ∃ p q : Prop, ChoiceField s p q) (hNo : NoChoiceField) : False :=
  hNo hField

/--Right-and-wrong commits a choice field: where there is truth and error,
 someone is before an incompatible pair.

  C54 (field form): "No right and wrong without (a field of) choice" — whenever
    the distinction holds, some subject before a choice field exists via
    AxTwoSubjects (poem P5). The genuine `Chooses` conclusion is BLOCKED on
    `rejectedHornCoMeant`. -/
theorem JUDGE_HAS_CHOICE_FIELD (h : ¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) :
    ∃ s : Subject, ∃ p q : Prop, ChoiceField s p q := by
  obtain ⟨s₁, _, hp₁, _, _⟩ := Logos.Value.AxTwoSubjects h
  obtain ⟨p, q, hch⟩ := person_hasChoiceField hp₁
  exact ⟨s₁, p, q, hch⟩

/-- Performative judgment commits a choice field: asserting right-and-wrong is
    an act set against its own negation. -/
theorem judge_asserting_rightWrong_has_choiceField (speaker : Subject)
    (h : Logos.Agency.Asserts speaker (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F)) :
    ∃ s : Subject, ∃ p q : Prop, ChoiceField s p q :=
  ⟨speaker, (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F), ¬ (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F),
   h.1, incompatible_self_negation _⟩

/--Right-and-wrong implies someone who means (poem P3, line 18 "há certo e há
 errado → há significado → há alguém para quem algo significar").

  C61: `JUDGE_HAS_CHOICE_FIELD` (C54) composes with `rightWrongDistinction` (C36)
    to yield a field; its first conjunct is a meaning-act, so some subject means
    some content. -/
theorem rightWrong_implies_someone_means (h : ¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) :
    ∃ s : Subject, ∃ p : Prop, Means s p := by
  obtain ⟨s, p, _, hch⟩ := JUDGE_HAS_CHOICE_FIELD h
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

/--Assertion is truth-laden: a subject who asserts `p` can never assert `¬ p`.

  `Asserts s p := Act s p ∧ p`; the asserted content is a *truth-claim*.
     The performative act, qua assertion, is therefore single-horned by
     definition — the "asserting is choosing" route to genuine choice is
     impossible (hostile milestone 2026-09-18). Footprint `{Means, Subject}`. -/
theorem assertion_consistency {s : Subject} {p : Prop} (h : Asserts s p) :
    ¬ Asserts s (¬ p) := by
  intro hn
  exact hn.2 h.2

/--No subject can assert both horns of an incompatible pair.

  General form: assertion (the truth-laden performative) can NEVER constitute
     a two-horned genuine choice — `Asserts` is consistent. Genuine choice
     would have to come from *meaning* (truth-neutral `Means`), not from
     asserting. Footprint `{Means, Subject}`. -/
theorem no_one_asserts_incompatible_pair :
    ¬ ∃ s : Subject, ∃ p q : Prop, Asserts s p ∧ Asserts s q ∧ Incompatible p q := by
  rintro ⟨s, p, q, ha, hb, hI⟩
  exact hI ⟨ha.2, hb.2⟩

end Logos.Choice

-- Axiom footprint audit
#print axioms Logos.Choice.T11_choiceField
#print axioms Logos.Choice.incompatible_self_negation
#print axioms Logos.Choice.meaning_I_needs_subject
#print axioms Logos.Choice.meaning_needs_subject
#print axioms Logos.Choice.chooses_implies_freeWill
#print axioms Logos.Choice.freeWillExists_of_chooses
#print axioms Logos.Choice.freeWillExists_of_genuineChoice
#print axioms Logos.Choice.rejectedHornCoMeant_implies_genuineChoice
#print axioms Logos.Choice.genuineChoice_requires_error_possibility
#print axioms Logos.Choice.assertion_consistency
#print axioms Logos.Choice.no_one_asserts_incompatible_pair
#print axioms Logos.Choice.person_hasChoiceField
#print axioms Logos.Choice.choiceField_exists
#print axioms Logos.Choice.noChoiceField_selfRefutes
#print axioms Logos.Choice.noSubject_selfRefutes
#print axioms Logos.Choice.JUDGE_HAS_CHOICE_FIELD
#print axioms Logos.Choice.rightWrong_implies_someone_means
