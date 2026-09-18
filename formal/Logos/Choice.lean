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

open Logos.Agency (Subject Means A Act Asserts State Initiates)
open Logos.Person (Person)
open Logos.Alternatives (Incompatible)
open Logos.Necessity (Dia Necessity someWorld)
open Logos.Semantics (Form NecessarilyTrue)

/-
### Core Conceptual Distinctions (Preserved Invariants):
1. Weak act vs. Strong Act:
   - `act(s,p)`   : weak act = performed event (pure sort / uninterpreted relation).
   - `Act(s,p)`   : strong Act = meaningful initiation (`Means s p ∧ ∃ w w', Initiates s w w' p`).
2. Choice field vs. Strong choice:
   - `ChoiceField(s,p,q)` : weak choice = means p + incompatibility (alternatives available in reality).
   - `Chooses(s,p,q)`     : strong choice = means p + means q + incompatibility (both horns co-meant in thought).
3. Field ≠ Choice, Choice → FreeWill:
   - `ChoiceField ≠ Chooses`: having a contradictory proposition ¬p available in the object language
     does NOT imply that the agent represents that proposition (`Means s (¬p)`). Object-language
     contradiction is free logic; cognitive representation is an intentional achievement.
   - `Chooses → FreeWill`: definitional (`FreeWill s := ∃ p q, Chooses s p q`).
-/

/-- `ChoiceField s p q`: weak choice: incompatible alternatives are present.
    The choice *field* — subject `s` means `p` against
    an incompatible content `q` (§13–§14 representability).
    Definition: `Means s p ∧ Incompatible p q`.
    The agent is related only to `p`; the rejected horn `q` (or `¬p`) is supplied
    by logic, not co-meant by the agent. This records that alternatives are present,
    distinguishable, or available to the subject, but it is NOT genuine selection.
    Genuine choice is `Chooses` below. -/
def ChoiceField (s : Subject) (p : Prop) (q : Prop) : Prop := Means s p ∧ Incompatible p q

/-- `Chooses s p q`: strong choice: the subject co-means incompatible alternatives.
    Subject `s` genuinely chooses between incompatible contents `p` and `q` (§14).
    Definition: `Means s p ∧ Means s q ∧ Incompatible p q`.
    The agent genuinely co-means BOTH incompatible horns. Strictly stronger than
    `ChoiceField`. -/
def Chooses (s : Subject) (p : Prop) (q : Prop) : Prop :=
  Means s p ∧ Means s q ∧ Incompatible p q

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

/-- A subject is a free subject iff it possesses free will (definitionally, genuinely chooses).
    Distinguished from bare ontological personhood (`Person s := ∃ p, Means s p`):
    every free subject is a person, but a person need not be a free subject. -/
def FreeSubject (s : Subject) : Prop := FreeWill s

/-- FreeSubject and FreeWill are definitionally equivalent. -/
theorem freeSubject_iff_freeWill (s : Subject) : FreeSubject s ↔ FreeWill s :=
  Iff.rfl

/--Genuine choice entails freedom — by definition.

  Footprint `{Means, Subject}` (VOCAB only — the statement's own vocabulary;
    the logical content is free). This is the repair's core: freedom is
    *conceptually/definitionally* the existence of a genuine choice between
    incompatible alternatives, not a further metaphysical step from a bare act. -/
theorem chooses_implies_freeWill {s : Subject} {p q : Prop}
    (h : Chooses s p q) : FreeWill s :=
  ⟨p, q, h⟩

/-- Genuine choice entails a free subject — by definition. -/
theorem chooses_implies_freeSubject {s : Subject} {p q : Prop}
    (h : Chooses s p q) : FreeSubject s :=
  chooses_implies_freeWill h

/-- Every free subject is an intentional subject:
    genuine choice requires meaning at least one proposition. -/
theorem freeSubject_implies_intentionalSubject (s : Subject) (h : FreeSubject s) :
    Logos.Person.IntentionalSubject s := by
  obtain ⟨p, _q, hChooses⟩ := h
  exact ⟨p, hChooses.1⟩

/-- Backward-compatibility alias for intentionality. -/
theorem freeSubject_implies_intentional (s : Subject) (h : FreeSubject s) :
    Logos.Person.Intentional s :=
  freeSubject_implies_intentionalSubject s h

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
def rejectedHornCoMeant : Prop := ∃ s : Subject, ∃ p : Prop, Means s p ∧ Means s (¬ p)

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

/--There is a field of choice: some intentional subject with two incompatible alternatives.

  T11 (C39) — the minimal field of rational choice is non-empty for an intentional subject:
    derived from an intentional act datum (C68 → C21 → C39).
    Footprint: `{Initiates, Means, State, Subject}` (VOCAB only; decoupled from AxTwoSubjects). -/
theorem T11_choiceField (h : ∃ s : Subject, ∃ p : Prop, A s p) :
    ∃ s : Subject, Logos.Person.IntentionalSubject s ∧ ∃ p q : Prop, Incompatible p q := by
  obtain ⟨s, hs⟩ := Logos.Plurality.T5_intentionalSubjectExists h
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
  intentional_hasChoiceField (Logos.Person.person_is_intentional s hs)

/--The choice field exists: some subject is before two incompatible alternatives.

  C52 (field form) — the field is real: derived from an intentional act datum
    (C68 → C52) through the WEAKER predicate `Intentional` (via
    `act_implies_intentional`), not through the §12 person label:
    `SubjectExists`/`Intentional` suffices. Footprint: `{Initiates, Means, State, Subject}`
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
  ⟨speaker, NoChoiceField, ¬ NoChoiceField, h.1.1, incompatible_self_negation NoChoiceField⟩

/-- C53 (field form): performative retorsion — asserting that no choice field exists
    refutes itself. Footprint: `{Initiates, Means, State, Subject}` (VOCAB only; zero AxTwoSubjects). -/
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
   h.1.1, incompatible_self_negation _⟩

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
    Delegated to Agency's genuine performative retorsion. Footprint: `{Initiates, Means, State, Subject}`. -/
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
    exact ⟨hSel.1.1.1, hMq, hSel.2.1, hSel.1, hSel.2.2⟩

/-- Two-factor bridge decomposition of deliberate choice for contradictory alternatives:
    `DeliberateChoice s p (¬p)` factors definitionally into:
    1. Executive Selection: `Selects s p (¬p)` (already provable from `Asserts s p` via `asserts_selects`);
    2. Alternative Awareness: `Means s (¬p)` (the sole missing cognitive bridge). -/
theorem deliberateChoice_negation_decomposition (s : Subject) (p : Prop) :
    DeliberateChoice s p (¬p) ↔ Selects s p (¬p) ∧ Means s (¬p) :=
  deliberateChoice_iff_selects_and_means s p (¬p)

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
    exact ⟨hSel.1.1.1, hRej.1, hSel.2.1, hSel.1, hRej.2⟩

/-- For self-negation alternatives, deliberate choice reduces to assertion of `p`
    combined with meaning the rejected negation `¬p` (the minimal resource sufficient for F1b; its existence remains open). -/
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
    meaning (entertaining in thought) its incompatible negation `¬p`.
    This represents the minimal resource sufficient to prove genuine choice;
    its existence remains open. -/
def deliberateGenuineChoiceResource : Prop :=
  ∃ s : Subject, ∃ p : Prop, Asserts s p ∧ Means s (¬p)

/-- Deliberate choice existence conditional on the minimal deliberative resource:
    Given an asserted proposition whose negation is entertained in thought,
    an explicit deliberate choice between contradictory alternatives obtains. -/
theorem deliberateChoice_exists_of_assertion_and_negation_meaning
    (h : deliberateGenuineChoiceResource) :
    ∃ s : Subject, ∃ p q : Prop, DeliberateChoice s p q := by
  obtain ⟨s, p, hAss, hMn⟩ := h
  have hDel : DeliberateChoice s p (¬p) :=
    (deliberateChoice_negation_iff s p hAss).2 hMn
  exact ⟨s, p, ¬p, hDel⟩

/-- The canonical F1b reduction theorem:
    The minimal deliberative resource (asserting p while meaning ¬p) strictly yields genuine choice.
    Unrolls Asserts s p into Act s p and p, uses act_implies_means to get Means s p,
    and combines with Means s (¬p) and incompatible_self_negation p to produce Chooses s p (¬p),
    without requiring Act on the rejected horn. -/
theorem deliberate_resource_implies_genuine_choice
    (h : deliberateGenuineChoiceResource) :
    genuineChoice_exists := by
  obtain ⟨s, p, hAss, hMn⟩ := h
  have hAct : Act s p := hAss.1
  have hMp : Means s p := Logos.Agency.act_implies_means hAct
  have hChooses : Chooses s p (¬p) := ⟨hMp, hMn, incompatible_self_negation p⟩
  exact ⟨s, p, ¬p, hChooses⟩

/-- Alias for backward compatibility. -/
abbrev genuineChoice_exists_of_assertion_and_negation_meaning :=
  deliberate_resource_implies_genuine_choice

-- ===========================================================================
-- Multi-Layer Agency: From Causal Production to Free Choice
-- ===========================================================================

/-- Causal transition (Layer 0): a physical state transition initiated by subject `s`. -/
def CausalTransition (s : Subject) (p : Prop) : Prop :=
  ∃ w w' : State, Initiates s w w' p

/-- Causal settlement (Layer 0): a physical state transition brings about `p` and suppresses `q`. -/
def CausalSettles (s : Subject) (p : Prop) (q : Prop) : Prop :=
  CausalTransition s p ∧ Incompatible p q ∧ ¬ CausalTransition s q

/-- Strong intentional action (Layer 1) strictly entails causal transition (Layer 0). -/
theorem act_implies_causalTransition {s : Subject} {p : Prop} (h : Act s p) :
    CausalTransition s p :=
  h.2

/-- Strong intentional action (Layer 1) derives an objective alternative field (Layer 2). -/
theorem act_implies_choiceField (s : Subject) (p : Prop) (h : Act s p) :
    ∃ q : Prop, ChoiceField s p q :=
  ⟨¬p, h.1, incompatible_self_negation p⟩

/-- Assertion (Layer 1+) derives semantic selection against contradictory negation (Layer 3). -/
theorem asserts_implies_selects (s : Subject) (p : Prop) (h : Asserts s p) :
    ∃ q : Prop, Selects s p q :=
  ⟨¬p, asserts_selects s p h⟩

/-- Authorship (Layer 3+): the subject's intentional act determines `p` and does not act on `q`.
    Autonomous from alternative representation: does not require `Means s q`. -/
def Authors (s : Subject) (p : Prop) (q : Prop) : Prop :=
  Act s p ∧ Incompatible p q ∧ ¬ Act s q

/-- An intentional act authors a determination against contradictory negation. -/
theorem act_implies_authors (s : Subject) (p : Prop) (h : Act s p)
    (hNoActNeg : ¬ Act s (¬p)) :
    Authors s p (¬p) :=
  ⟨h, incompatible_self_negation p, hNoActNeg⟩

/-- Contemplative co-meaning (Layer 4): the subject entertains both incompatible possibilities in thought.
    Definitionally identical to `Chooses s p q`. -/
def Contemplates (s : Subject) (p : Prop) (q : Prop) : Prop :=
  Means s p ∧ Means s q ∧ Incompatible p q

/-- Contemplation is definitionally equivalent to genuine choice. -/
theorem contemplates_iff_chooses (s : Subject) (p q : Prop) :
    Contemplates s p q ↔ Chooses s p q :=
  Iff.rfl

/-- Contemplation without settlement / action: an agent represents both horns without acting on either. -/
def ContemplatesWithoutSettling (s : Subject) (p : Prop) (q : Prop) : Prop :=
  Contemplates s p q ∧ ¬ Act s p ∧ ¬ Act s q

/-- Contemplation without action still derives FreeWill (freedom of the will is cognitive/deliberative). -/
theorem contemplatesWithoutSettling_implies_freeWill
    {s : Subject} {p q : Prop} (h : ContemplatesWithoutSettling s p q) :
    FreeWill s :=
  chooses_implies_freeWill h.1

/-- Deliberate authorship (Layer 5): the subject authors `p` against `q` while aware of alternative `q`. -/
def DeliberateAuthorship (s : Subject) (p : Prop) (q : Prop) : Prop :=
  Authors s p q ∧ Means s q

/-- Deliberate authorship entails genuine choice. -/
theorem deliberateAuthorship_implies_chooses
    {s : Subject} {p q : Prop} (h : DeliberateAuthorship s p q) :
    Chooses s p q :=
  ⟨h.1.1.1, h.2, h.1.2.1⟩

/-- Deliberate authorship under assertion yields DeliberateChoice. -/
theorem deliberateAuthorship_implies_deliberateChoice
    {s : Subject} {p q : Prop} (h : DeliberateAuthorship s p q)
    (hAss : Asserts s p) (hNoAss : ¬ Asserts s q) :
    DeliberateChoice s p q :=
  ⟨h.1.1.1, h.2, h.1.2.1, hAss, hNoAss⟩

/-- Alternative sensitivity (Layer 4): the subject represents an incompatible alternative in thought. -/
def AlternativeSensitivity (s : Subject) (p : Prop) : Prop :=
  ∃ q : Prop, Means s q ∧ Incompatible p q

/-- Relational intentionality: an intentional act oriented toward `p` while co-meaning alternative `q`. -/
def RelationalIntentionality (s : Subject) (p : Prop) (q : Prop) : Prop :=
  Act s p ∧ Incompatible p q ∧ Means s q

/-- Alternative sensitivity directly yields genuine choice for an active agent. -/
theorem alternativeSensitivity_implies_genuineChoice
    {s : Subject} {p : Prop} (hAct : Act s p) (hSens : AlternativeSensitivity s p) :
    ∃ q : Prop, Chooses s p q := by
  obtain ⟨q, hmq, hincomp⟩ := hSens
  exact ⟨q, hAct.1, hmq, hincomp⟩

/-- Relational intentionality directly derives genuine choice. -/
theorem relationalIntentionality_implies_genuineChoice
    {s : Subject} {p q : Prop} (h : RelationalIntentionality s p q) :
    Chooses s p q :=
  ⟨h.1.1, h.2.2, h.2.1⟩

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

/-- The Act Polarity principle: initiating an intentional act constitutively endows the agent with
    the intentional representation of its contradictory negation.
    Strictly weaker than universal bilateral intentionality: leaves non-active or passive meaning unconstrained. -/
def act_polarity_principle : Prop :=
  ∀ (s : Subject) (p : Prop), Act s p → Means s (¬ p)

/-- Universal bilateral intentionality strictly implies act polarity:
    an agent whose entire meaning relation is bilateral is a fortiori polar in its active initiations. -/
theorem bilateral_implies_act_polarity (h : bilateral_intentionality_principle) :
    act_polarity_principle := by
  intro s p ha
  exact h s p ha.1

/-
### 14-Row Candidate Derivation Route Audit Table (`Act s p` to `Means s (¬p)`):

| Route | Intermediate Step | Classification | Exact Mathematical Obstruction |
|---|---|---|---|
| 1. Act → Means p | Analytic unrolling | DERIVES | `Act s p := Means s p ∧ ...`; only yields positive horn `Means s p`. |
| 2. Act → Asserts | Factive commitment | REQUIRES A NEW BRIDGE | Requires `act_implies_asserts_bridge` (factual truth of `p`). |
| 3. Act → Correct ∨ Incorrect | Bivalent partition | DERIVES | Proved via `act_iff_correct_or_incorrect` (C101). |
| 4. Correct/Incorrect → Means ¬p | Normative truth-value | DOES NOT DERIVE | Concerns truth-value of `p`, not mental representation of `¬p`. |
| 5. ChoiceField → Means ¬p | Incompatible availability | DOES NOT DERIVE | `¬p` occurs only in `Incompatible p (¬p) := ¬(p ∧ ¬p)`, not in `Means s _`. |
| 6. DeliberateChoice → Means ¬p | Deliberative co-meaning | REQUIRES A NEW BRIDGE | `DeliberateChoice` defines co-meaning, but `Act → DeliberateChoice` does not derive. |
| 7. Bivalence / LEM → Means ¬p | Propositional excluded middle | DOES NOT DERIVE | Intensional barrier: `p ∨ ¬p` in `Prop` does not force `Means s (¬p)`. |
| 8. Truth / Falsehood → Means ¬p | Semantic status | DOES NOT DERIVE | External truth-values do not populate intentional relations. |
| 9. Retorsion → Means ¬p | Performative contradiction | DOES NOT DERIVE | Refutes `NoAct`; does not force every act to co-mean contradictory negations. |
| 10. Intentional → Means ¬p | Representation faculty | DOES NOT DERIVE | `Intentional s := ∃ p, Means s p` provides only a single content. |
| 11. Person → Means ¬p | Rational personhood | DOES NOT DERIVE | Inherits only single intentional content of `Intentional s`. |
| 12. Plurality → Means ¬p | Distinct subjects | DOES NOT DERIVE | `AxTwoSubjects` gives two distinct subjects with single contents, not dual co-meaning. |
| 13. Modal Principles → Means ¬p | Propositional necessity | DOES NOT DERIVE | Modal backbone governs world-satisfaction, not internal cognitive representation. |
| 14. Grounding Principles → Means ¬p | Truthmaker grounding | DOES NOT DERIVE | `Ground e p` relates entities to propositions, entirely outside `Means`. |

### Diagnostic Grid of Strong Act and Choice across Model Levels:

| Level | Model Description | Act s p | ChoiceField s p q | Chooses s p q | FreeWill s | FreeSubject s | Verdict |
|---|---|---|---|---|---|---|---|
| M0 | Weak Act (`CountermodelWeakActWithoutMeaning`) | FALSE | FALSE | FALSE | FALSE | FALSE | Event occurs without meaning or strong Act |
| M1 | Factive Strong Act (`hostileAgencyInstance`) | TRUE | TRUE | FALSE | FALSE | FALSE | Strong Act & ChoiceField hold; Chooses fails by veridicality |
| M2 | Branching Initiation (`ModelM2BranchingInitiation`) | TRUE | TRUE | FALSE | FALSE | FALSE | Non-trivial state branching holds; Chooses still fails |
| M3 | Contrastive Agency (`ModelM3ContrastiveAgency`) | TRUE | TRUE | TRUE | TRUE | TRUE | Polar agency validated (AxActPolarity); FreeSubject valid |

### Six-Attack Audit on Deriving Polarity from Strong Act:

| Attack Vector | Candidate Principle | Outcome Classification | Hostile Witness / Model | Exact Separating Valuation & Analysis |
|---|---|---|---|---|
| **Attack 1 (Existential Act Polarity)** | `(∃ s p, Act s p) → ∃ s p, Act s p ∧ Means s (¬p)` | **C. REFUTED BY HOSTILE MODEL** | `fullTheoryHostileInstance` (`not_entails_existential_polarity_from_full_theory`) | Valuation: `s = false, p = True`. In veridical semantics (`Means s p := p`), `Act s p` forces $p$, while `Means s (¬p)` forces $\neg p$, making dual co-meaning an absolute contradiction ($p \land \neg p \equiv \bot$). |
| **Attack 2 (Semantics of Means)** | `Act s p → ∃ q, Means s q ∧ Incompatible p q` | **C. REFUTED BY HOSTILE MODEL** | `CountermodelVeridicalMeaning.Single` (`Single.no_genuine_choice`, `genuineChoice_requires_error_possibility`) | Valuation: `p = True`. If meaning is factive, any incompatible pair $p, q$ would require $p \land q \land \neg(p \land q) \equiv \bot$. Factive meaning mathematically excludes co-meaning incompatible alternatives. |
| **Attack 3 (Contrastive Initiation)** | `Branches (fun w w' => ∃ p, Initiates s w w' p) → ∃ q, Means s q ∧ Incompatible p q` | **C. REFUTED / D. REDUNDANT** | `ModelM2BranchingInitiation` (`m2_diagnostic_separation`) | For physical branching: **C. REFUTED** by Model M2 (`w = false ∧ w' ∈ {true, false}`); physical state transitions are extensional and do not force mental co-meaning. For intentional contrast: **D. REDUNDANT** (extensionally equivalent to A13). |
| **Attack 4 (DeliberateChoice Decomposition)** | `Act s p → ∃ q, DeliberateChoice s p q` | **C. REFUTED BY HOSTILE MODEL** | `hostileAgencyInstance` (`deliberateChoice_negation_decomposition`) | Valuation: `s = false, p = True, q = False`. Executive selection `Selects s p (¬p)` holds by assertion, but alternative awareness `Means s (¬p)` fails by veridicality. Deliberation fails strictly at the missing cognitive horn. |
| **Attack 5 (Performative Doubt & Retorsion)** | `(Asserts speaker NoAct → False) → ∃ s p, Doubts s p` | **C. REFUTED BY HOSTILE MODEL** | `TwoPersons.retorsion_does_not_imply_doubt` | Valuation: `NoAct := ¬ ∃ s p, Act s p`. Retorsion establishes that denying action is performatively self-refuting, but refutation of an assertion does not populate the agent's mind with dual contradictory contents. |
| **Attack 6 (C101 Normative Bivalence)** | `(Act s p ↔ Asserts s p ∨ Incorrect s p) → ∃ s p, Means s p ∧ Means s (¬p)` | **C. REFUTED BY HOSTILE MODEL** | `hostileAgencyInstance` (`hostile_c101`) | Valuation: `s = false, p = True`. Bivalent partition classifies the normative status of the posited content $p$ relative to reality; it tracks the world, not dual cognitive representations in the same subject $s$. |

### Resolution of Cases A, B, and C:
- Case A (Derivable from existing Strong Act in pre-A14 theory): REFUTED.
  Kernel independence theorems `not_entails_act_polarity_from_full_theory` and
  `not_entails_existential_polarity_from_full_theory` prove that all 12 pre-A14 axioms
  of Γ are consistent with veridical semantics where no subject co-means contradictory propositions.
- Case B (Initiates vocabulary is under-specified): EVALUATED & BOUNDED.
  Even when `Initiates` is strengthened to require dynamic state-space branching (`Branches`, Model M2),
  executive transitions between states remain extensional and fail to force mental co-meaning of the alternative.
- Case C (Adoption of Constitutive Semantic Principle A14): ESTABLISHED.
  Strong Choice is not an executive property of transitions, but a cognitive property of contrastive agency.
  Genuine choice is not derivable from Strong Act in the pre-A14 theory.
  Γ therefore adopts `AxIntentionalChoice : Act s p → ∃ q, Chooses s p q` as an authentic, substantive
  SEMANTIC constitutive principle (Tag: SEM), with `AxActPolarity : Act s p → Means s (¬p)` remaining
  an optional stronger contradictory-negation principle.
-/

/-- Structural decomposition: an intentional act decomposes definitionally into an intentional
    horn (`Means s p`) and an executive horn (`Initiates s w w' p`). Neither horn mathematically
    contains the contradictory representation `Means s (¬p)` without an independent bridge. -/
theorem act_decomposition (s : Subject) (p : Prop) :
    Act s p ↔ Means s p ∧ ∃ w w' : State, Initiates s w w' p :=
  Iff.rfl

/-
### Three Levels of Independence in the Pre-A14 Theory:
1. Level 1 (Act decomposition alone):
   `act_decomposition` proves `Act s p ↔ Means s p ∧ ∃ w w', Initiates s w w' p`.
   Neither horn contains the contradictory representation `Means s (¬p)`.
2. Level 2 (Pre-A14 agency-side theory relevant to F1b):
   `HostileSemantics.not_entails_act_polarity_from_preA13` proves that the entire
   pre-A14 agency fragment (act datum, plurality, bivalent order, judge commitment,
   fallibility, retorsion, C101) does not entail `Act s p → Means s (¬p)`.
   Furthermore, `HostileSemantics.not_entails_existential_polarity_from_preA13` proves
   that even the cheaper existential premise `∃ s p, Act s p ∧ Means s (¬p)` is independent.
3. Level 3 (Metatheoretical consequence for full pre-A14 Γ theory):
   The remaining pre-A14 axioms (A1, A3, A4, A7, A8, A9) govern worldly truthmakers and
   grounding and do not mention `Means` or `Initiates`, hence cannot bridge to `Means s (¬p)`.

### Logical Hierarchy:
AxActPolarity (A13, SEM: contradictory negation ¬p)
  ↓ (`act_polarity_implies_intentional_choice`)
AxIntentionalChoice (A14, SEM: incompatible alternative q, adopted constitutive choice principle)
  ↓ (`genuineChoice_exists_of_act_constitutive`)
Genuine choice (`genuineChoice_exists`)
  ↓ (`freeWillExists_of_genuineChoice`)
Free will / Free subject (`∃ s, FreeWill s ↔ FreeSubject s`)
-/

/-- Tag: SEM
Genuine choice is constitutive of intentional action: an intentional act is an initiation performed through the subject's apprehension of an incompatible alternative.

 AxIntentionalChoice (SEM): an intentional act (`Act s p := Means s p ∧ ∃ w w', Initiates s w w' p`)
    constitutively involves the agent's apprehension and co-meaning of an incompatible alternative
    (`Chooses s p q := Means s p ∧ Means s q ∧ Incompatible p q`).
    Adopted constitutive semantic principle closing F1b.
    Strictly weaker than AxActPolarity: does not require the alternative to be contradictory negation ¬p. -/
axiom AxIntentionalChoice :
  ∀ (s : Subject) (p : Prop),
    Act s p → ∃ q, Chooses s p q

/-- Tag: SEM
Act polarity: initiating an intentional act constitutively endows the agent with the representation of its contradictory negation.

 AxActPolarity (SEM): meaningful initiation of movement (`Act s p := Means s p ∧ ∃ w w', Initiates s w w' p`)
    constitutively contrasts against the non-occurrence of the posited state (`Means s (¬p)`).
    Stronger optional semantic principle: requires representation of formal contradictory negation ¬p.
    Strictly implies AxIntentionalChoice via act_polarity_implies_intentional_choice. -/
axiom AxActPolarity : ∀ (s : Subject) (p : Prop), Act s p → Means s (¬ p)

/-- Conditional Act Polarity schema: if an intentional act occurs, some acting subject means its negation.
    Logically weaker than universal AxActPolarity (existential consequence rather than universal law). -/
def conditional_act_polarity : Prop :=
  (∃ s : Subject, ∃ p : Prop, Act s p) → ∃ s : Subject, ∃ p : Prop, Act s p ∧ Means s (¬ p)

/-- Pure existential act polarity: at least one acting subject represents the contradictory negation of its act.
    Suffices constructively for F1b, but functions as an ad hoc existential posit rather than a constitutive law. -/
def existential_act_polarity : Prop :=
  ∃ s : Subject, ∃ p : Prop, Act s p ∧ Means s (¬ p)

/-- Universal act polarity strictly implies conditional act polarity. -/
theorem act_polarity_implies_conditional (h : act_polarity_principle) : conditional_act_polarity := by
  intro hAct
  obtain ⟨s, p, ha⟩ := hAct
  exact ⟨s, p, ha, h s p ha⟩

/-- Universal act polarity with an act datum implies existential act polarity. -/
theorem act_polarity_implies_existential (h : act_polarity_principle) (hAct : ∃ s : Subject, ∃ p : Prop, Act s p) :
    existential_act_polarity :=
  act_polarity_implies_conditional h hAct

/-- Genuine choice derived directly from existential act polarity.
    Demonstrates that existential polarity is sufficient for F1b, while universal AxActPolarity
    remains the preferred constitutive semantic law. -/
theorem genuineChoice_exists_of_existential_act_polarity (h : existential_act_polarity) :
    genuineChoice_exists := by
  obtain ⟨s, p, ha, hmn⟩ := h
  exact ⟨s, p, ¬p, ha.1, hmn, incompatible_self_negation p⟩

/-- Free will derived directly from existential act polarity. -/
theorem freeWill_exists_of_existential_act_polarity (h : existential_act_polarity) :
    ∃ s : Subject, FreeWill s :=
  freeWillExists_of_genuineChoice (genuineChoice_exists_of_existential_act_polarity h)

/-- Contrastive Agency principle: initiating an intentional act constitutively stands against
    some incompatible alternative q that is entertained in thought.
    Logically and conceptually strictly weaker than AxActPolarity: does not require the
    alternative to be the formal contradictory negation ¬p, but merely some mutually exclusive alternative. -/
def contrastive_agency_principle : Prop :=
  ∀ (s : Subject) (p : Prop), Act s p → ∃ q : Prop, Means s q ∧ Incompatible p q

/-- Existential Contrastive Agency schema: if an intentional act occurs, some acting subject
    entertains an incompatible alternative in thought. -/
def existential_contrastive_agency : Prop :=
  (∃ s : Subject, ∃ p : Prop, Act s p) → ∃ s : Subject, ∃ p q : Prop, Act s p ∧ Means s q ∧ Incompatible p q

/-- Universal act polarity strictly implies contrastive agency:
    taking q := ¬p immediately satisfies Incompatible p (¬p). -/
theorem act_polarity_implies_contrastive (h : act_polarity_principle) : contrastive_agency_principle := by
  intro s p ha
  exact ⟨¬p, h s p ha, incompatible_self_negation p⟩

/-- Universal act polarity strictly implies intentional choice:
    taking q := ¬p gives Chooses s p (¬p). -/
theorem act_polarity_implies_intentional_choice (h : act_polarity_principle) :
    ∀ (s : Subject) (p : Prop), Act s p → ∃ q, Chooses s p q := by
  intro s p ha
  exact ⟨¬p, ha.1, h s p ha, incompatible_self_negation p⟩

/-- Intentional choice implies contrastive agency:
    extracting the alternative q and its properties. -/
theorem intentional_choice_implies_contrastive :
    (∀ (s : Subject) (p : Prop), Act s p → ∃ q, Chooses s p q) → contrastive_agency_principle := by
  intro h s p ha
  obtain ⟨q, _, hmq, hincomp⟩ := h s p ha
  exact ⟨q, hmq, hincomp⟩

/-- Contrastive agency implies intentional choice:
    recombining Means s p from the act datum with the alternative. -/
theorem contrastive_implies_intentional_choice :
    contrastive_agency_principle → (∀ (s : Subject) (p : Prop), Act s p → ∃ q, Chooses s p q) := by
  intro h s p ha
  obtain ⟨q, hmq, hincomp⟩ := h s p ha
  exact ⟨q, ha.1, hmq, hincomp⟩

/-- Contrastive agency strictly implies existential contrastive agency. -/
theorem contrastive_agency_implies_existential (h : contrastive_agency_principle) :
    existential_contrastive_agency := by
  rintro ⟨s, p, ha⟩
  obtain ⟨q, hmq, hincomp⟩ := h s p ha
  exact ⟨s, p, q, ha, hmq, hincomp⟩

/-- The existential weakening of intentional choice (A14∃):
    if an intentional act occurs, some agent executes an act with genuine choice. -/
def existential_intentional_choice : Prop :=
  (∃ s : Subject, ∃ p : Prop, Act s p) → ∃ s : Subject, ∃ p q : Prop, Chooses s p q

/-- Universal intentional choice (A14) entails existential intentional choice (A14∃) by pure logic. -/
theorem intentional_choice_implies_existential_choice
    (h : ∀ (s : Subject) (p : Prop), Act s p → ∃ q, Chooses s p q) :
    existential_intentional_choice := by
  rintro ⟨s, p, ha⟩
  obtain ⟨q, hq⟩ := h s p ha
  exact ⟨s, p, q, hq⟩

/-- Free will existence is directly derived from existential intentional choice (A14∃). -/
theorem freeWill_exists_of_existential_choice
    (h : existential_intentional_choice)
    (hAct : ∃ s : Subject, ∃ p : Prop, Act s p) :
    ∃ s : Subject, FreeWill s := by
  obtain ⟨s, p, q, hq⟩ := h hAct
  exact ⟨s, p, q, hq⟩

/-- A14∃ is definitionally equivalent to the existence of free will from an act datum (target F1b). -/
theorem existential_choice_iff_f1b :
    existential_intentional_choice ↔ ((∃ s : Subject, ∃ p : Prop, Act s p) → ∃ s : Subject, FreeWill s) := by
  rfl

/-- Act polarity (A13) entails existential intentional choice (A14∃) via universal A14. -/
theorem act_polarity_implies_existential_choice
    (h : act_polarity_principle) :
    existential_intentional_choice :=
  intentional_choice_implies_existential_choice (act_polarity_implies_intentional_choice h)

/-- The minimal missing cognitive horn: subject `s` cognitively entertains an incompatible alternative `q` to `p`. -/
def MissingCognitiveHorn (s : Subject) (p : Prop) : Prop :=
  ∃ q : Prop, Means s q ∧ Incompatible p q

/-- The exact mathematical frontier for genuine choice:
    a subject genuinely chooses between `p` and an alternative iff the subject means `p`
    and possesses the missing cognitive horn for `p`. -/
theorem means_missing_horn_iff_chooses (s : Subject) (p : Prop) :
    Means s p ∧ MissingCognitiveHorn s p ↔ ∃ q, Chooses s p q := by
  constructor
  · rintro ⟨hmp, q, hmq, hincomp⟩
    exact ⟨q, hmp, hmq, hincomp⟩
  · rintro ⟨q, hmp, hmq, hincomp⟩
    exact ⟨hmp, q, hmq, hincomp⟩

/-- The exact mathematical frontier for FreeWill existence:
    a free subject exists iff some subject means some proposition `p` and possesses
    the missing cognitive horn for `p`. -/
theorem freeWill_iff_means_missing_horn :
    (∃ s : Subject, FreeWill s) ↔ ∃ s : Subject, ∃ p : Prop, Means s p ∧ MissingCognitiveHorn s p := by
  constructor
  · rintro ⟨s, p, q, hc⟩
    exact ⟨s, p, hc.1, q, hc.2.1, hc.2.2⟩
  · rintro ⟨s, p, hmp, q, hmq, hincomp⟩
    exact ⟨s, p, q, hmp, hmq, hincomp⟩

/-- An intentional act equipped with the missing cognitive horn entails genuine choice. -/
theorem act_missing_horn_implies_chooses (s : Subject) (p : Prop) :
    Act s p ∧ MissingCognitiveHorn s p → ∃ q, Chooses s p q := by
  rintro ⟨ha, q, hmq, hincomp⟩
  exact ⟨q, ha.1, hmq, hincomp⟩

/-- For an intentional act, possessing the missing cognitive horn is necessary and sufficient
    for genuine choice. -/
theorem act_missing_horn_iff_chooses (s : Subject) (p : Prop) (hAct : Act s p) :
    MissingCognitiveHorn s p ↔ ∃ q, Chooses s p q := by
  constructor
  · intro hHorn
    exact act_missing_horn_implies_chooses s p ⟨hAct, hHorn⟩
  · rintro ⟨q, _, hmq, hincomp⟩
    exact ⟨q, hmq, hincomp⟩

/-- The Relative Completeness Theorem for F1b:
    relative to pre-A14 vocabulary, the existence of free will from an intentional act datum (target F1b)
    is equivalent to the conditional existence of the missing cognitive horn over the performative datum.
    Footprint: {Initiates, Means, State, Subject} (VOCAB only; pure logic). -/
theorem f1b_iff_missing_cognitive_horn :
    ((∃ s : Subject, ∃ p : Prop, Act s p) → ∃ s : Subject, FreeWill s) ↔
    ((∃ s : Subject, ∃ p : Prop, Act s p) → ∃ s : Subject, ∃ p : Prop, Means s p ∧ MissingCognitiveHorn s p) := by
  constructor
  · intro hF1b hAct
    have hFW := hF1b hAct
    exact freeWill_iff_means_missing_horn.mp hFW
  · intro hHorn hAct
    have hMeansHorn := hHorn hAct
    exact freeWill_iff_means_missing_horn.mpr hMeansHorn

/-- Pointwise frontier: an intentional act produces genuine choice if and only if
    it is accompanied by the missing cognitive horn. -/
theorem act_produces_choice_iff_missing_horn (s : Subject) (p : Prop) (hAct : Act s p) :
    (∃ q : Prop, Chooses s p q) ↔ MissingCognitiveHorn s p :=
  (act_missing_horn_iff_chooses s p hAct).symm

/-- Genuine choice derived directly from contrastive agency.
    Demonstrates that genuine choice does not require formal propositional negation,
    merely any mutually exclusive alternative entertained in thought. -/
theorem genuineChoice_exists_of_contrastive_act
    (h : contrastive_agency_principle)
    (hAct : ∃ s : Subject, ∃ p : Prop, Act s p) :
    genuineChoice_exists := by
  obtain ⟨s, p, ha⟩ := hAct
  obtain ⟨q, hmq, hincomp⟩ := h s p ha
  exact ⟨s, p, q, ha.1, hmq, hincomp⟩

/-- Free will derived directly from contrastive agency. -/
theorem freeWill_exists_of_contrastive_act
    (h : contrastive_agency_principle)
    (hAct : ∃ s : Subject, ∃ p : Prop, Act s p) :
    ∃ s : Subject, FreeWill s :=
  freeWillExists_of_genuineChoice (genuineChoice_exists_of_contrastive_act h hAct)

/-- Free subject derived directly from contrastive agency. -/
theorem freeSubject_exists_of_contrastive_act
    (h : contrastive_agency_principle)
    (hAct : ∃ s : Subject, ∃ p : Prop, Act s p) :
    ∃ s : Subject, FreeSubject s :=
  freeWill_exists_of_contrastive_act h hAct

/-- Deliberative genuine choice resource derived under Act Polarity and Assertion. -/
theorem deliberateResource_of_act_polarity
    (hPolarity : act_polarity_principle)
    (hAss : ∃ s : Subject, ∃ p : Prop, Asserts s p) :
    deliberateGenuineChoiceResource := by
  obtain ⟨s, p, ha⟩ := hAss
  have hMn : Means s (¬p) := hPolarity s p ha.1
  exact ⟨s, p, ha, hMn⟩

/-- Genuine choice closure under Act Polarity and Assertion. -/
theorem genuineChoice_exists_of_act_polarity
    (hPolarity : act_polarity_principle)
    (hAss : ∃ s : Subject, ∃ p : Prop, Asserts s p) :
    genuineChoice_exists := by
  have hRes := deliberateResource_of_act_polarity hPolarity hAss
  exact genuineChoice_exists_of_assertion_and_negation_meaning hRes

/-- Deliberative genuine choice resource derived under Bilateral Intentionality and Assertion.
    Given bilateral intentionality and an assertive performative act, the minimal deliberative
    resource `deliberateGenuineChoiceResource` is strictly derived. -/
theorem deliberateResource_of_bilateral_intentionality
    (hBilateral : bilateral_intentionality_principle)
    (hAss : ∃ s : Subject, ∃ p : Prop, Asserts s p) :
    deliberateGenuineChoiceResource :=
  deliberateResource_of_act_polarity (bilateral_implies_act_polarity hBilateral) hAss

/-- Genuine choice closure under Bilateral Intentionality and Assertion (Outcome B conditional).
    Shows the exact bridge needed to close F1b under an independent, principled theory of
    intentionality rather than an ad hoc postulate of F1b. -/
theorem genuineChoice_exists_of_bilateral_intentionality
    (hBilateral : bilateral_intentionality_principle)
    (hAss : ∃ s : Subject, ∃ p : Prop, Asserts s p) :
    genuineChoice_exists :=
  genuineChoice_exists_of_act_polarity (bilateral_implies_act_polarity hBilateral) hAss

/-- Genuine choice exists: an acting subject co-means contradictory alternatives under act polarity.

 Derived from an intentional act datum under AxActPolarity.
    Footprint: `{AxActPolarity, Initiates, Means, State, Subject}`. -/
theorem genuineChoice_exists_of_act (h : ∃ s : Subject, ∃ p : Prop, Act s p) : genuineChoice_exists := by
  obtain ⟨s, p, ha⟩ := h
  have hmp : Means s p := ha.1
  have hmn : Means s (¬p) := AxActPolarity s p ha
  exact ⟨s, p, ¬p, hmp, hmn, incompatible_self_negation p⟩

/-- Closure of genuine choice from intentional action under the constitutive thesis AxIntentionalChoice.
    Primary constitutive closure for F1b.
    Footprint: `{AxIntentionalChoice, Initiates, Means, State, Subject}`. -/
theorem genuineChoice_exists_of_act_constitutive
    (h : ∃ s : Subject, ∃ p : Prop, Act s p) :
    genuineChoice_exists := by
  obtain ⟨s, p, hAct⟩ := h
  obtain ⟨q, hChoice⟩ := AxIntentionalChoice s p hAct
  exact ⟨s, p, q, hChoice⟩

/-- Free will derived from intentional action under the constitutive thesis AxIntentionalChoice.
    Primary target theorem closing F1b under the performative act datum and AxIntentionalChoice.
    Footprint: `{AxIntentionalChoice, Initiates, Means, State, Subject}`. -/
theorem freeWill_exists_of_act
    (h : ∃ s : Subject, ∃ p : Prop, Act s p) :
    ∃ s : Subject, FreeWill s :=
  freeWillExists_of_genuineChoice (genuineChoice_exists_of_act_constitutive h)

/-- Free subject derived from intentional action under the constitutive thesis AxIntentionalChoice.
    Footprint: `{AxIntentionalChoice, Initiates, Means, State, Subject}`. -/
theorem freeSubject_exists_of_act
    (h : ∃ s : Subject, ∃ p : Prop, Act s p) :
    ∃ s : Subject, FreeSubject s :=
  freeWill_exists_of_act h

/-- Free will exists under the stronger contradictory-negation principle AxActPolarity.
    Footprint: `{AxActPolarity, Initiates, Means, State, Subject}`. -/
theorem freeWill_exists_of_act_polarity (h : ∃ s : Subject, ∃ p : Prop, Act s p) :
    ∃ s : Subject, FreeWill s :=
  freeWillExists_of_genuineChoice (genuineChoice_exists_of_act h)

/-- Free will exists: some subject genuinely chooses between incompatible alternatives.

    Primary target theorem closing F1b under the performative datum of intentional action and the adopted
    constitutive principle AxIntentionalChoice.
    Footprint: `{AxIntentionalChoice, Initiates, Means, State, Subject}`. -/
theorem freeWill_exists (h : ∃ s : Subject, ∃ p : Prop, Act s p) : ∃ s : Subject, FreeWill s :=
  freeWill_exists_of_act h

/-- Free subject exists: some subject is a free subject.
    Proves the full `Act → Chooses → FreeSubject` chain under AxIntentionalChoice.
    Footprint: `{AxIntentionalChoice, Initiates, Means, State, Subject}`. -/
theorem freeSubject_exists (h : ∃ s : Subject, ∃ p : Prop, Act s p) : ∃ s : Subject, FreeSubject s :=
  freeSubject_exists_of_act h

/-- Candidate Outcome B principle: Cartesian Doubt.
    An act of doubting `p` constitutively involves entertaining both `p` and its contrary `¬p`
    in thought. A subject in doubt is already related to incompatible alternatives. -/
def Doubts (s : Subject) (p : Prop) : Prop :=
  Means s p ∧ Means s (¬p)

/-- The Cartesian Doubting Datum (Case A): at least one actual subject doubts some proposition.
    If the foundational transcendental datum is formalized as an act of Cartesian doubt
    rather than a bare factive assertion, genuine choice and freedom are immediate. -/
def DoubtingDatum : Prop :=
  ∃ s : Subject, ∃ p : Prop, Doubts s p

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

/-- Genuine choice exists under the Cartesian doubting datum (Case A closure).
    From the existence of an act of doubt, genuine choice is strictly derived without substantive axioms. -/
theorem genuineChoice_exists_of_doubt_datum (h : DoubtingDatum) :
    genuineChoice_exists := by
  obtain ⟨s, p, hd⟩ := h
  exact ⟨s, p, ¬p, genuineChoice_of_doubt hd⟩

/-- Freedom exists under the Cartesian doubting datum (Case A closure).
    From the existence of an act of doubt, a free subject is strictly derived. -/
theorem freeWill_exists_of_doubt_datum (h : DoubtingDatum) :
    ∃ s : Subject, FreeWill s := by
  obtain ⟨s, p, hd⟩ := h
  exact ⟨s, freeWill_of_doubt hd⟩

/-- Candidate B bridge: every intentional act entails an act of doubt.
    The substantive semantic premise that the presence of intentional agency guarantees
    the occurrence of Cartesian doubt. Unprovable from the bare act (witnessed by veridical models). -/
def doubt_existence_bridge : Prop :=
  (∃ s : Subject, ∃ p : Prop, Act s p) → ∃ s : Subject, ∃ p : Prop, Doubts s p

/-- Genuine choice closure under the doubt existence bridge (Case B conditional). -/
theorem genuineChoice_exists_of_doubt_bridge
    (hBridge : doubt_existence_bridge) (hAct : ∃ s : Subject, ∃ p : Prop, Act s p) :
    genuineChoice_exists :=
  genuineChoice_exists_of_doubt_datum (hBridge hAct)

/-- Freedom closure under the doubt existence bridge (Case B conditional). -/
theorem freeWill_exists_of_doubt_bridge
    (hBridge : doubt_existence_bridge) (hAct : ∃ s : Subject, ∃ p : Prop, Act s p) :
    ∃ s : Subject, FreeWill s :=
  freeWill_exists_of_doubt_datum (hBridge hAct)

/-- Teleological action: an intentional act directed toward an end proposition `g`. -/
def TeleologicalAct (s : Subject) (p : Prop) (g : Prop) : Prop :=
  Act s p ∧ Means s g ∧ (p → g)

/-- Reason-responsive action: an intentional act initiated for reason `r`. -/
def ReasonResponsiveAct (s : Subject) (p : Prop) (r : Prop) : Prop :=
  Act s p ∧ Means s r ∧ (r → p)

/-- Counterfactual action: an intentional act with an alternative initiation in state space. -/
def CounterfactualAct (s : Subject) (p : Prop) (q : Prop) : Prop :=
  Act s p ∧ Incompatible p q ∧ ∃ w w' : State, Initiates s w w' q

/-- Teleological action entails genuine choice under the constitutive choice principle AxIntentionalChoice. -/
theorem teleological_act_implies_genuineChoice
    (s : Subject) (p g : Prop) (h : TeleologicalAct s p g) :
    ∃ q : Prop, Chooses s p q :=
  AxIntentionalChoice s p h.1

/-- Reason-responsive action entails genuine choice under the constitutive choice principle AxIntentionalChoice. -/
theorem reasonResponsive_act_implies_genuineChoice
    (s : Subject) (p r : Prop) (h : ReasonResponsiveAct s p r) :
    ∃ q : Prop, Chooses s p q :=
  AxIntentionalChoice s p h.1

/-- Counterfactual action entails genuine choice under the constitutive choice principle AxIntentionalChoice. -/
theorem counterfactual_act_implies_genuineChoice
    (s : Subject) (p q : Prop) (h : CounterfactualAct s p q) :
    ∃ q' : Prop, Chooses s p q' :=
  AxIntentionalChoice s p h.1

/-- Descriptive action: an intentional act individuated under description `p`. -/
def DescriptiveAct (s : Subject) (p : Prop) : Prop :=
  Act s p ∧ Means s p

/-- Action individuated under description entails genuine choice under AxIntentionalChoice. -/
theorem descriptive_act_implies_genuineChoice
    (s : Subject) (p : Prop) (h : DescriptiveAct s p) :
    ∃ q : Prop, Chooses s p q :=
  AxIntentionalChoice s p h.1

/--No one can assert "there is no strong truth": the act of denying the
  world-level datum is destroyed by the datum itself (assertive retorsion of
  C93, completing the retorsion family at the assertion level; footprint
  {Means, Subject, CL}). -/
theorem noStrongTruth_assertable_refutes (speaker : Subject) :
    Asserts speaker (¬ ∃ τ : Form, NecessarilyTrue τ) → False := by
  intro h
  exact Logos.Semantics.noStrongTruth_selfRefutes h.2

/-- Self-denial of choice: an intentional act positing that this very act contains no genuine choice. -/
def SelfDenialOfChoice (s : Subject) (p : Prop) : Prop :=
  Act s p ∧ (p ↔ ∀ q : Prop, ¬ Chooses s p q)

/-- Under bilateral act polarity (A13), self-denial of choice yields genuine choice. -/
theorem selfDenial_implies_genuineChoice_of_polarity
    {s : Subject} {p : Prop} (hDenial : SelfDenialOfChoice s p) :
    ∃ q : Prop, Chooses s p q := by
  have hAct : Act s p := hDenial.1
  have hMn : Means s (¬p) := AxActPolarity s p hAct
  exact ⟨¬p, hAct.1, hMn, incompatible_self_negation p⟩

/-- Under intentional choice (A14), self-denial of choice directly yields genuine choice. -/
theorem selfDenial_implies_genuineChoice_of_a14
    {s : Subject} {p : Prop} (hDenial : SelfDenialOfChoice s p) :
    ∃ q : Prop, Chooses s p q :=
  AxIntentionalChoice s p hDenial.1

-- ===========================================================================
-- Self-Referential Free Choice & Self-Ascription Audit
-- ===========================================================================

/-- Candidate A: Self-asserted genuine choice.
    The proposition `p` states that this very act contains genuine choice. -/
def SelfAssertedChoice (s : Subject) (p : Prop) : Prop :=
  p ↔ ∃ q : Prop, Chooses s p q

/-- Candidate B: Self-asserted authorship.
    The proposition `p` states that this very act authors `p` against some `q`. -/
def SelfAssertedAuthorship (s : Subject) (p : Prop) : Prop :=
  p ↔ ∃ q : Prop, Authors s p q

/-- Candidate C: Self-asserted deliberate choice.
    The proposition `p` states that this very act deliberately chooses `p` over `q`. -/
def SelfAssertedDeliberateChoice (s : Subject) (p : Prop) : Prop :=
  p ↔ ∃ q : Prop, DeliberateChoice s p q

/-- Candidate D: Self-asserted paradox ("I freely choose not to choose").
    The proposition `p` states that this act is chosen AND contains no choice. -/
def SelfAssertedParadox (s : Subject) (p : Prop) : Prop :=
  p ↔ (∃ q : Prop, Chooses s p q) ∧ (∀ q : Prop, ¬ Chooses s p q)

/-- Candidate A factive detachment: a TRUE self-ascription of choice logically yields genuine choice. -/
theorem selfAssertedChoice_factive_implies_chooses
    {s : Subject} {p : Prop} (hAss : Asserts s p) (hSelf : SelfAssertedChoice s p) :
    ∃ q : Prop, Chooses s p q :=
  hSelf.1 hAss.2

/-- Candidate C factive detachment: a TRUE self-ascription of deliberate choice logically yields genuine choice. -/
theorem selfAssertedDeliberateChoice_factive_implies_chooses
    {s : Subject} {p : Prop} (hAss : Asserts s p) (hSelf : SelfAssertedDeliberateChoice s p) :
    ∃ q : Prop, Chooses s p q := by
  obtain ⟨q, hDelib⟩ := hSelf.1 hAss.2
  exact ⟨q, deliberateChoice_implies_chooses hDelib⟩

/-- Candidate D contradiction: the paradoxical proposition is logically false. -/
theorem selfAssertedParadox_is_false
    {s : Subject} {p : Prop} (hSelf : SelfAssertedParadox s p) :
    ¬ p := by
  intro hp
  obtain ⟨⟨q, hq⟩, hno⟩ := hSelf.1 hp
  exact hno q hq

-- ===========================================================================
-- Reconstructed Ontology of Choice: Determination vs. Deliberation
-- ===========================================================================

/-- Deliberation / Contrastive Representation:
    Simultaneous cognitive representation of both incompatible alternatives in thought.
    Formerly identified with `Chooses`; now recognized as cognitive deliberation. -/
def Deliberates (s : Subject) (p : Prop) (q : Prop) : Prop :=
  Means s p ∧ Means s q ∧ Incompatible p q

/-- Deliberation is definitionally equivalent to the legacy `Chooses` relation. -/
theorem deliberates_iff_chooses (s : Subject) (p q : Prop) :
    Deliberates s p q ↔ Chooses s p q :=
  Iff.rfl

/-- Executive Choice (unary): the subject actively determines and asserts `p` against its contradictory negation.
    Choice proper is an executive act of selection/determination, not the simultaneous co-meaning of alternatives. -/
def Choice (s : Subject) (p : Prop) : Prop :=
  Selects s p (¬p)

/-- Executive Choice holds for any factive assertion by pure logic and definitions. -/
theorem asserts_implies_choice (s : Subject) (p : Prop) (hAss : Asserts s p) :
    Choice s p :=
  asserts_selects s p hAss

/-- Relational Executive Choice: the subject determines and selects `p` over incompatible alternative `q`. -/
def ChoiceRel (s : Subject) (p : Prop) (q : Prop) : Prop :=
  Selects s p q

/-- Authorship Choice: the subject intentionally executes `p` and does not execute `¬p`. -/
def AuthorshipChoice (s : Subject) (p : Prop) : Prop :=
  Authors s p (¬p)

/-- Free Agency: a subject possesses free agency if they can exercise executive choice. -/
def FreeAgency (s : Subject) : Prop :=
  ∃ p : Prop, Choice s p

/-- Every asserting agent exercises free agency by pure logic. -/
theorem asserts_implies_freeAgency {s : Subject} {p : Prop} (hAss : Asserts s p) :
    FreeAgency s :=
  ⟨p, asserts_implies_choice s p hAss⟩

/-- Self-denial of executive choice: an agent asserts of its own assertion that it contains no Choice. -/
def SelfDenialOfExecutiveChoice (s : Subject) (p : Prop) : Prop :=
  Asserts s p ∧ (p ↔ ¬ Choice s p)

/-- The Performative Retorsion Theorem for Executive Choice:
    Denying executive choice in an assertion is self-refuting.
    The very act of making the assertion performs the semantic determination `Choice s p`,
    which contradicts the asserted propositional content `¬ Choice s p`. -/
theorem selfDenialOfExecutiveChoice_selfRefutes
    {s : Subject} {p : Prop} (hDenial : SelfDenialOfExecutiveChoice s p) :
    False := by
  have hAss : Asserts s p := hDenial.1
  have hChoice : Choice s p := asserts_implies_choice s p hAss
  have hNotChoice : ¬ Choice s p := hDenial.2.1 hAss.2
  exact hNotChoice hChoice

/-- Candidate D performative retorsion under factive assertion: one cannot truthfully assert Candidate D. -/
theorem selfAssertedParadox_not_assertable
    {s : Subject} {p : Prop} (hSelf : SelfAssertedParadox s p) :
    Asserts s p → False :=
  fun hAss => selfAssertedParadox_is_false hSelf hAss.2

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
#print axioms Logos.Choice.deliberateChoice_negation_decomposition
#print axioms Logos.Choice.Rejects
#print axioms Logos.Choice.deliberateChoice_iff_selects_and_rejects
#print axioms Logos.Choice.deliberateChoice_negation_iff
#print axioms Logos.Choice.deliberateGenuineChoiceResource
#print axioms Logos.Choice.deliberateChoice_exists_of_assertion_and_negation_meaning
#print axioms Logos.Choice.deliberate_resource_implies_genuine_choice
#print axioms Logos.Choice.genuineChoice_exists_of_assertion_and_negation_meaning
#print axioms Logos.Choice.act_implies_asserts_bridge
#print axioms Logos.Choice.selection_exists_of_act
#print axioms Logos.Choice.bilateral_intentionality_principle
#print axioms Logos.Choice.deliberateResource_of_bilateral_intentionality
#print axioms Logos.Choice.genuineChoice_exists_of_bilateral_intentionality
#print axioms Logos.Choice.AxActPolarity
#print axioms Logos.Choice.act_decomposition
#print axioms Logos.Choice.genuineChoice_exists_of_act
#print axioms Logos.Choice.freeWill_exists
#print axioms Logos.Choice.FreeSubject
#print axioms Logos.Choice.freeSubject_iff_freeWill
#print axioms Logos.Choice.chooses_implies_freeSubject
#print axioms Logos.Choice.freeSubject_implies_intentionalSubject
#print axioms Logos.Choice.freeSubject_exists
#print axioms Logos.Choice.act_polarity_implies_conditional
#print axioms Logos.Choice.act_polarity_implies_existential
#print axioms Logos.Choice.genuineChoice_exists_of_existential_act_polarity
#print axioms Logos.Choice.freeWill_exists_of_existential_act_polarity
#print axioms Logos.Choice.contrastive_agency_principle
#print axioms Logos.Choice.existential_contrastive_agency
#print axioms Logos.Choice.act_polarity_implies_contrastive
#print axioms Logos.Choice.contrastive_agency_implies_existential
#print axioms Logos.Choice.genuineChoice_exists_of_contrastive_act
#print axioms Logos.Choice.freeWill_exists_of_contrastive_act
#print axioms Logos.Choice.freeSubject_exists_of_contrastive_act
#print axioms Logos.Choice.Doubts
#print axioms Logos.Choice.DoubtingDatum
#print axioms Logos.Choice.genuineChoice_of_doubt
#print axioms Logos.Choice.freeWill_of_doubt
#print axioms Logos.Choice.genuineChoice_exists_of_doubt_datum
#print axioms Logos.Choice.freeWill_exists_of_doubt_datum
#print axioms Logos.Choice.doubt_existence_bridge
#print axioms Logos.Choice.genuineChoice_exists_of_doubt_bridge
#print axioms Logos.Choice.freeWill_exists_of_doubt_bridge
#print axioms Logos.Choice.existential_intentional_choice
#print axioms Logos.Choice.intentional_choice_implies_existential_choice
#print axioms Logos.Choice.freeWill_exists_of_existential_choice
#print axioms Logos.Choice.existential_choice_iff_f1b
#print axioms Logos.Choice.act_polarity_implies_existential_choice
#print axioms Logos.Choice.MissingCognitiveHorn
#print axioms Logos.Choice.means_missing_horn_iff_chooses
#print axioms Logos.Choice.freeWill_iff_means_missing_horn
#print axioms Logos.Choice.act_missing_horn_implies_chooses
#print axioms Logos.Choice.act_missing_horn_iff_chooses
#print axioms Logos.Choice.f1b_iff_missing_cognitive_horn
#print axioms Logos.Choice.act_produces_choice_iff_missing_horn
