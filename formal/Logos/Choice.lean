/-
# Logos.Choice — rational choice-field and freedom (base.txt §13–§15, T11; poem P4/P5)

Choice-realism batch (2026-09-16), **repaired 2026-09-18** (freedom/choice fix):
the relation formerly named `Chooses` was a *determined occurrence*, not a
choice. With `Chooses s p q := A s p ∧ Incompatible p q` and
`Incompatible p (¬p)` pure logic, `∃ q, Chooses s p q` collapses to `A s p`:
the agent was never related to the rejected horn. The repair splits the
vocabulary into two relations and a definitional freedom:

  * `ChoiceField s p q := A s p ∧ Incompatible p q` — **representability/field** (Level 1):
    the agent's act is set against an incompatible content. This is the old
    occurrence relation; it is PROVEN for any meaning-act (C51/C52 field form)
    but is *not* a choice.
  * `Selects s p q := Asserts s p ∧ Incompatible p q ∧ ¬ Asserts s q` — **semantic selection** (Level 2):
    the agent commits to `p` against incompatible alternative `q` and does not assert `q`.
    PROVEN for any assertion (`asserts_selects`, `asserts_selects_all_incompatible`),
    establishing that meaningful assertive agency is constitutively selective.
  * `DeliberateChoice s p q := Means s p ∧ Means s q ∧ Incompatible p q ∧ Asserts s p ∧ ¬ Asserts s q` —
    **deliberative choice**: the agent entertains both incompatible alternatives in thought,
    while asserting only one. Entails `Selects` and `Chooses`, but its existence remains unforced
    by the performative datum alone (witnessed by `CountermodelVeridicalMeaning`).
  * `Chooses s p q := A s p ∧ A s q ∧ Incompatible p q` — **genuine choice**:
    the agent holds *both* incompatible contents (adopts `p` while `q` is
    co-meant). `∃ q, Chooses s p q` is no longer `A s p`.
  * `FreeWill s := ∃ p q, Chooses s p q` — freedom (Level 4) is *definitional* from
    genuine choice (`chooses_implies_freeWill`, footprint `{Means, Subject}` —
    VOCAB only). Level 3 (counterfactual possibility of selecting otherwise) is not
    forced by deterministic agency.

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
  * `intentional_hasChoiceField`: the weaker predicate already yields a field
    (`Intentional` → field; the §12 person label adds nothing);
  * `person_hasChoiceField`: a person is before an incompatible pair
    (nominal wrapper of the former);
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

open Logos.Agency (Subject Means A Act Asserts)
open Logos.Person (Person)
open Logos.Alternatives (Incompatible)
open Logos.Necessity (Dia Necessity someWorld)
open Logos.Semantics (Form NecessarilyTrue)

/-- `ChoiceField s p q`: weak choice: incompatible alternatives are present.
    The choice *field* — subject `s` performs an intentional act on `p` against
    an incompatible content `q` (§13–§14 representability).
    Definition: `A s p ∧ Incompatible p q`.
    The agent is related only to `p`; the rejected horn `q` (or `¬p`) is supplied
    by logic, not co-meant by the agent. This records that alternatives are present,
    distinguishable, or available to the subject, but it is NOT genuine selection.
    Genuine choice is `Chooses` below. -/
def ChoiceField (s : Subject) (p : Prop) (q : Prop) : Prop := A s p ∧ Incompatible p q

/-- `Chooses s p q`: strong choice: the subject co-means incompatible alternatives.
    Subject `s` genuinely chooses between incompatible contents `p` and `q` (§14).
    Definition: `A s p ∧ A s q ∧ Incompatible p q`.
    The agent genuinely co-means BOTH incompatible horns. Strictly stronger than
    `ChoiceField`. -/
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

/--Genuine choice exists: some subject co-means two incompatible
    contents; that existence itself remains blocked. The modal side of
    openness is settled and inert — `atoms_are_modally_free` (C95) and
    `some_formula_contingent` (C96), both `{}`, prove content-openness,
    yet even fuelled as an extra datum the modal channel cannot force
    co-meaning (`modal_openness_does_not_entail_genuine_choice(_and_plurality)`,
    `{}`, HostileSemantics); the block is solely `rejectedHornCoMeant`
    (agency-side, option 3), not any modal determination.

  The precise missing lemma of the freedom frontier (F1b, BLOCKED).

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

/--The field needs only intentionality: `Intentional s` already unfolds to
  `∃ p, Means s p`, so the weaker predicate suffices — the §12 person label
  adds nothing here (nominal wrapper `person_hasChoiceField` below).
  Footprint: `{Means, Subject}` (VOCAB only). -/
theorem intentional_hasChoiceField {s : Subject} (hIn : Logos.Person.Intentional s) :
    ∃ p q : Prop, ChoiceField s p q := by
  obtain ⟨p, hmp⟩ := hIn
  exact ⟨p, ¬ p, hmp, incompatible_self_negation p⟩

/--Any person has a choice field: a person is always before two incompatible alternatives.

  Audit notice (freedom/choice fix, 2026-09-18): this yields `ChoiceField`, NOT
    genuine `Chooses`. The agent is related only to the adopted content `p`; the
    rejected horn `¬p` is supplied by pure logic (`incompatible_self_negation`),
    not by the agent. The genuine form (both horns co-meant) is BLOCKED on
    `rejectedHornCoMeant`. Nominal wrapper of `intentional_hasChoiceField`
    (the §12 label adds nothing). -/
theorem person_hasChoiceField {s : Subject} (hs : Person s) : ∃ p q : Prop, ChoiceField s p q :=
  intentional_hasChoiceField hs.2.2

/--The choice field exists: some subject is before two incompatible alternatives.

  C52 (field form) — the field is real: derived from an intentional act datum
    (C68 → C52) through the WEAKER predicate `Intentional` (via
    `act_implies_intentional`), not through the §12 person label:
    `SubjectExists`/`Intentional` suffices. Footprint: `{Means, Subject}`
    (VOCAB only). -/
theorem choiceField_exists (h : ∃ s : Subject, ∃ p : Prop, A s p) :
    ∃ s : Subject, ∃ p q : Prop, ChoiceField s p q := by
  obtain ⟨s, p, ha⟩ := h
  obtain ⟨p', q, hch⟩ :=
    intentional_hasChoiceField (Logos.Person.act_implies_intentional ha)
  exact ⟨s, p', q, hch⟩

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

-- ===========================================================================
-- Semantic Selection Layer (F1b Refined Frontier)
-- Distinguishes Alternatives (ChoiceField) → Selection (Selects) → Free Choice (FreeWill)
-- ===========================================================================

/-- Semantic selection: subject `s` commits to `p` against incompatible alternative `q`.
    The agent asserts `p`, standing against an incompatible proposition `q`,
    and does not assert `q`. This records directed semantic commitment to one horn
    rather than its incompatible alternatives, without requiring co-meaning of the
    rejected horn or libertarian freedom. -/
def Selects (s : Subject) (p : Prop) (q : Prop) : Prop :=
  Asserts s p ∧ Incompatible p q ∧ ¬ Asserts s q

/-- Any assertion constitutes semantic selection against its own negation.
    From `Asserts s p`, the agent is committed to `p`, `p` is incompatible with `¬p`,
    and consistency guarantees that the agent does not assert `¬p`. -/
theorem asserts_selects (s : Subject) (p : Prop) (h : Asserts s p) :
    Selects s p (¬p) := by
  refine ⟨h, incompatible_self_negation p, assertion_consistency h⟩

/-- Assertion selects against every incompatible alternative.
    Whenever a subject asserts `p`, any proposition `q` incompatible with `p` is
    excluded from assertion: the subject cannot assert both horns. -/
theorem asserts_selects_all_incompatible (s : Subject) (p q : Prop)
    (h : Asserts s p) (hI : Incompatible p q) :
    Selects s p q := by
  refine ⟨h, hI, ?_⟩
  intro hq
  exact hI ⟨h.2, hq.2⟩

/-- Semantic selection exists whenever an assertion datum is supplied.
    An assertive performative act immediately furnishes a witness of semantic selection
    between the asserted content and its negation. -/
theorem selection_exists (h : ∃ s : Subject, ∃ p : Prop, Asserts s p) :
    ∃ s : Subject, ∃ p q : Prop, Selects s p q := by
  obtain ⟨s, p, ha⟩ := h
  exact ⟨s, p, ¬p, asserts_selects s p ha⟩

/-- No selection entails no assertion: the contrapositive of semantic selection.
    If a subject cannot or does not select `p` against any alternative, that subject
    does not assert `p`. Meaningful assertive commitment constitutively involves selection. -/
theorem no_selection_no_assertion (s : Subject) (p : Prop)
    (hNo : ∀ q : Prop, ¬ Selects s p q) : ¬ Asserts s p := by
  intro hAss
  exact hNo (¬p) (asserts_selects s p hAss)

-- ===========================================================================
-- Deliberate Choice & Bridge Pricing (Candidate C)
-- ===========================================================================

/-- Deliberate choice: subject `s` entertains both `p` and `q` while asserting only `p`.
    The subject represents both incompatible alternatives in thought (`Means s p ∧ Means s q`),
    recognizes their mutual incompatibility (`Incompatible p q`),
    and commits to one horn by asserting `p` while withholding assertion of `q` (`Asserts s p ∧ ¬ Asserts s q`).
    This formalizes deliberation without requiring contradictory dual assertion. -/
def DeliberateChoice (s : Subject) (p : Prop) (q : Prop) : Prop :=
  Means s p ∧ Means s q ∧ Incompatible p q ∧ Asserts s p ∧ ¬ Asserts s q

/-- Deliberate choice strictly entails semantic selection.
    Any subject who deliberates between `p` and `q` and chooses `p` thereby selects `p` against `q`. -/
theorem deliberateChoice_implies_selects {s : Subject} {p q : Prop}
    (h : DeliberateChoice s p q) : Selects s p q :=
  ⟨h.2.2.2.1, h.2.2.1, h.2.2.2.2⟩

/-- Deliberate choice entails genuine choice in the co-meaning sense.
    Because the deliberating agent entertains both horns in thought, both are meant. -/
theorem deliberateChoice_implies_chooses {s : Subject} {p q : Prop}
    (h : DeliberateChoice s p q) : Chooses s p q :=
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- Exact decomposition of deliberate choice (Route C milestone):
    Deliberate choice between `p` and `q` is definitionally equivalent to
    semantic selection of `p` against `q` plus awareness (intentional representation)
    of the alternative horn `q`. -/
theorem deliberateChoice_iff_selects_and_means (s : Subject) (p q : Prop) :
    DeliberateChoice s p q ↔ Selects s p q ∧ Means s q := by
  constructor
  · intro h
    exact ⟨deliberateChoice_implies_selects h, h.2.1⟩
  · rintro ⟨hSel, hMq⟩
    exact ⟨hSel.1.1, hMq, hSel.2.1, hSel.1, hSel.2.2⟩

/-- Active rejection of an alternative:
    Subject `s` actively rejects `q` when `s` entertains `q` in thought (`Means s q`)
    but does not assert it (`¬ Asserts s q`).
    This formalizes conscious exclusion of a candidate alternative. -/
def Rejects (s : Subject) (q : Prop) : Prop :=
  Means s q ∧ ¬ Asserts s q

/-- Deliberate choice as Selection + Rejection (Route C milestone):
    Choosing deliberately between `p` and `q` is selecting `p` against `q`
    while actively rejecting `q`. -/
theorem deliberateChoice_iff_selects_and_rejects (s : Subject) (p q : Prop) :
    DeliberateChoice s p q ↔ Selects s p q ∧ Rejects s q := by
  constructor
  · intro h
    exact ⟨deliberateChoice_implies_selects h, ⟨h.2.1, h.2.2.2.2⟩⟩
  · rintro ⟨hSel, hRej⟩
    exact ⟨hSel.1.1, hRej.1, hSel.2.1, hSel.1, hRej.2⟩

/-- For self-negation alternatives, deliberate choice reduces to assertion of `p`
    combined with meaning the rejected negation `¬p` (the exact F1b resource `rejectedHornCoMeant`). -/
theorem deliberateChoice_negation_iff (s : Subject) (p : Prop) (hAss : Asserts s p) :
    DeliberateChoice s p (¬p) ↔ Means s (¬p) := by
  constructor
  · intro h
    exact h.2.1
  · intro hMn
    have hSel := asserts_selects s p hAss
    exact (deliberateChoice_iff_selects_and_means s p (¬p)).2 ⟨hSel, hMn⟩

/-- Minimal deliberative resource for genuine choice (exact F1b reduction):
    An actualized subject asserts a proposition `p` while simultaneously
    meaning (entertaining in thought) its incompatible negation `¬p`. -/
def deliberateGenuineChoiceResource : Prop :=
  ∃ s : Subject, ∃ p : Prop, Asserts s p ∧ Means s (¬p)

/-- Deliberate choice existence from the minimal deliberative resource:
    Given an asserted proposition whose negation is entertained in thought,
    an explicit deliberate choice between contradictory alternatives obtains. -/
theorem deliberateChoice_exists_of_assertion_and_negation_meaning
    (h : deliberateGenuineChoiceResource) :
    ∃ s : Subject, ∃ p q : Prop, DeliberateChoice s p q := by
  obtain ⟨s, p, hAss, hMn⟩ := h
  have hDel : DeliberateChoice s p (¬p) :=
    (deliberateChoice_negation_iff s p hAss).2 hMn
  exact ⟨s, p, ¬p, hDel⟩

/-- Genuine choice closure from the minimal deliberative resource (F1b reduction):
    Given an asserted truth whose negation is entertained in thought,
    genuine choice between incompatible contents is strictly derived without substantive axioms. -/
theorem genuineChoice_exists_of_assertion_and_negation_meaning
    (h : deliberateGenuineChoiceResource) :
    genuineChoice_exists := by
  obtain ⟨s, p, hAss, hMn⟩ := h
  have hDel : DeliberateChoice s p (¬p) :=
    (deliberateChoice_negation_iff s p hAss).2 hMn
  exact ⟨s, p, ¬p, deliberateChoice_implies_chooses hDel⟩

/-- Candidate C bridge: every intentional act entails an assertion.
    The explicit semantic proposition that the occurrence of an intentional act
    guarantees an assertive truth-claim. This is an unprovable substantive semantic
    premise, required if semantic selection is to be derived from the bare
    act-datum without the retorsive shortcut. -/
def act_implies_asserts_bridge : Prop :=
  (∃ s : Subject, ∃ p : Prop, Act s p) → ∃ s : Subject, ∃ p : Prop, Asserts s p

/-- Under the explicit Candidate C bridge, an intentional act yields semantic selection.
    Priced explicitly by the bridge premise; without this premise, bare meaning does not
    force selection (witnessed by CountermodelOmniMeaning). -/
theorem selection_exists_of_act (hBridge : act_implies_asserts_bridge)
    (h : ∃ s : Subject, ∃ p : Prop, Act s p) :
    ∃ s : Subject, ∃ p q : Prop, Selects s p q := by
  obtain ⟨s, p, ha⟩ := hBridge h
  exact selection_exists ⟨s, p, ha⟩

-- ===========================================================================
-- Candidate Outcome B: Independent Semantic Principles (Bilateralism / Doubt)
-- ===========================================================================

/-- Candidate Outcome B semantic principle: Bilateral intentionality / representational polarity.
    The substantive semantic thesis that intentional representation of any proposition `p`
    constitutively endows the subject with the capacity to represent its negation `¬p`.
    This formalizes the Frege/Dummett/Wittgenstein bilateralism thesis: to grasp a thought is
    to understand the contrast between its being true and its being false.
    Classified as SEMANTIC; unprovable from bare uninterpreted `Means` (witnessed by
    CountermodelVeridicalMeaning). -/
def bilateral_intentionality_principle : Prop :=
  ∀ (s : Subject) (p : Prop), Means s p → Means s (¬p)

/-- Deliberative genuine choice resource derived under Bilateral Intentionality and Assertion.
    Given bilateral intentionality and an assertive performative act, the minimal deliberative
    resource `deliberateGenuineChoiceResource` is strictly derived. -/
theorem deliberateResource_of_bilateral_intentionality
    (hBilateral : bilateral_intentionality_principle)
    (hAss : ∃ s : Subject, ∃ p : Prop, Asserts s p) :
    deliberateGenuineChoiceResource := by
  obtain ⟨s, p, ha⟩ := hAss
  have hMn : Means s (¬p) := hBilateral s p ha.1
  exact ⟨s, p, ha, hMn⟩

/-- Genuine choice closure under Bilateral Intentionality and Assertion (Outcome B conditional).
    Shows the exact bridge needed to close F1b under an independent, principled theory of
    intentionality rather than an ad hoc postulate of F1b. -/
theorem genuineChoice_exists_of_bilateral_intentionality
    (hBilateral : bilateral_intentionality_principle)
    (hAss : ∃ s : Subject, ∃ p : Prop, Asserts s p) :
    genuineChoice_exists := by
  have hRes := deliberateResource_of_bilateral_intentionality hBilateral hAss
  exact genuineChoice_exists_of_assertion_and_negation_meaning hRes

/-- Candidate Outcome B principle: Cartesian Doubt.
    An act of doubting `p` constitutively involves entertaining both `p` and its contrary `¬p`
    in thought. A subject in doubt is already related to incompatible alternatives. -/
def Doubts (s : Subject) (p : Prop) : Prop :=
  Means s p ∧ Means s (¬p)

/-- An act of Cartesian doubt immediately witnesses genuine choice between incompatible alternatives.
    Shows that if the foundational performative datum were an act of doubt rather than a single-horned
    assertion or meaning-act, genuine choice would be derived immediately without additional bridges. -/
theorem genuineChoice_of_doubt {s : Subject} {p : Prop} (hDoubt : Doubts s p) :
    Chooses s p (¬p) :=
  ⟨hDoubt.1, hDoubt.2, incompatible_self_negation p⟩

/-- Cartesian doubt directly yields freedom for the doubting subject. -/
theorem freeWill_of_doubt {s : Subject} {p : Prop} (hDoubt : Doubts s p) :
    FreeWill s :=
  chooses_implies_freeWill (genuineChoice_of_doubt hDoubt)

/--No one can assert "there is no strong truth": the act of denying the
  world-level datum is destroyed by the datum itself (assertive retorsion of
  C93, completing the retorsion family at the assertion level; footprint
  {Means, Subject, CL}). -/
theorem noStrongTruth_assertable_refutes (speaker : Subject) :
    Asserts speaker (¬ ∃ τ : Form, NecessarilyTrue τ) → False := by
  intro h
  exact Logos.Semantics.noStrongTruth_selfRefutes h.2

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
#print axioms Logos.Choice.intentional_hasChoiceField
#print axioms Logos.Choice.person_hasChoiceField
#print axioms Logos.Choice.choiceField_exists
#print axioms Logos.Choice.noChoiceField_selfRefutes
#print axioms Logos.Choice.noSubject_selfRefutes
#print axioms Logos.Choice.JUDGE_HAS_CHOICE_FIELD
#print axioms Logos.Choice.rightWrong_implies_someone_means
#print axioms Logos.Choice.noStrongTruth_assertable_refutes
#print axioms Logos.Choice.Selects
#print axioms Logos.Choice.asserts_selects
#print axioms Logos.Choice.asserts_selects_all_incompatible
#print axioms Logos.Choice.selection_exists
#print axioms Logos.Choice.no_selection_no_assertion
#print axioms Logos.Choice.DeliberateChoice
#print axioms Logos.Choice.deliberateChoice_implies_selects
#print axioms Logos.Choice.deliberateChoice_implies_chooses
#print axioms Logos.Choice.deliberateChoice_iff_selects_and_means
#print axioms Logos.Choice.Rejects
#print axioms Logos.Choice.deliberateChoice_iff_selects_and_rejects
#print axioms Logos.Choice.deliberateChoice_negation_iff
#print axioms Logos.Choice.deliberateGenuineChoiceResource
#print axioms Logos.Choice.deliberateChoice_exists_of_assertion_and_negation_meaning
#print axioms Logos.Choice.genuineChoice_exists_of_assertion_and_negation_meaning
#print axioms Logos.Choice.act_implies_asserts_bridge
#print axioms Logos.Choice.selection_exists_of_act
#print axioms Logos.Choice.bilateral_intentionality_principle
#print axioms Logos.Choice.deliberateResource_of_bilateral_intentionality
#print axioms Logos.Choice.genuineChoice_exists_of_bilateral_intentionality
#print axioms Logos.Choice.Doubts
#print axioms Logos.Choice.genuineChoice_of_doubt
#print axioms Logos.Choice.freeWill_of_doubt
