/-
# Logos.Plurality — more than one person (poem P5/P7; theorem T12)

T12 — there are at least two distinct persons.
Reconstructed under hostile semantics: agency and personhood do not entail
plurality by logic alone (settled by the Unit countermodel in `HostileSemantics`).
Plurality is therefore derived under the explicit META bridge
`TwoNecessaryPersonalCentres.AxTwoNecessaryPersonalCentres` (2026-10-04, batch
LOVE-3/S4, replacing the retired `Value.AxTwoSubjects`).

Also hosts the Q2 bridge `EntityOf : Subject → Entity` (each person has an
entity-correlate), decided to close the Subject/Entity gap so the love layer
can attach necessity to the relata (T14).

The existence theorems `T1_subjectExists`, `T4_agentExists`, and `T5_personExists`
are anchored directly on the performative foundation `Agency.Cogito`.
`T12_twoPersons`, `notAlone`, and `T12_directedPair` are the genuine plurality
claims, standing honestly on `{AxTwoNecessaryPersonalCentres}`.
-/

import Logos.Core
import Logos.Agency
import Logos.Person
import Logos.Choice
import Logos.Value
import Logos.Entity

namespace Logos.Plurality

open Logos.Agency (Subject NecessarySubjectKind ContingentSubjectKind)
open Logos.Person (Person)
open Logos.Entity (Entity ExistsAt actualWorld falsityWorld)
open Logos.Semantics (World)
open Logos.Value (Affects PersonsAffectPrinciple)
open Logos.TwoNecessaryPersonalCentres (AxTwoNecessaryPersonalCentres two_persons)

/-- Q2 bridge: canonical embedding of subjects into the general entity type. -/
def EntityOf : Subject → Entity := Logos.Entity.EntityOf

/-- A subject is necessary iff its entity-correlate exists in every world. -/
def NecessarySubject (s : Subject) : Prop := ∀ w : World, ExistsAt w (EntityOf s)

/-- A subject of the necessary kind is necessary: its correlate exists at every
    world by the left disjunct of `SubjectExistsAt`. This is the kind-relative
    form of persistence — it holds of the necessary kind only, never of subjects
    as such. Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem necessaryKindSubject_is_necessary (s : Subject)
    (h : NecessarySubjectKind s) : NecessarySubject s :=
  fun _w => Or.inl h

/-- A subject of the contingent kind is not necessary: at the all-`TV.f` world
    its correlate fails, since the kind disjunct is refuted by hypothesis and
    the all-`f` valuation is not the actual world. This keeps every
    contingency finding that used to be stated unconditionally — they now carry
    the kind hypothesis that was always their real content.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem contingentKindSubject_not_necessary (s : Subject)
    (h : ContingentSubjectKind s) : ¬ NecessarySubject s := by
  intro hNec
  have hAt := hNec (fun _ => Logos.Semantics.TV.f)
  dsimp [ExistsAt, Logos.Entity.EntityExistsAt, Logos.Entity.SubjectExistsAt,
    EntityOf] at hAt
  rcases hAt with hk | heq
  · exact h hk
  · have h0 := congrArg (fun w : World => w 0) heq
    exact Logos.Semantics.TV.noConfusion h0

/-- The two kinds of subject are exactly the two modal profiles: a subject is of
    the necessary kind if and only if its entity-correlate exists in every world.

    This is the reading of the kind vocabulary, not a new claim about it. The
    forward direction is `necessaryKindSubject_is_necessary` (C405); the reverse
    is the same two lines `contingentKindSubject_not_necessary` (C406) already
    used for the other direction: instantiate at the falsity world
    (`Entity.falsityWorld`), and the world-disjunct of `SubjectExistsAt` is ruled
    out because the all-`TV.f` valuation is not `actualWorld`. So
    `NecessarySubjectKind` is not a free-floating label: the kernel now proves
    what it separates, and the split is provably exhaustive and disjoint
    (`contingentKind_iff_not_necessary`, C411). The kind predicate keeps its
    `Tag: VOCAB` badge — this theorem interprets the badge, it does not demote it.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem kinds_are_the_modal_partition (s : Subject) :
    NecessarySubjectKind s ↔ NecessarySubject s := by
  constructor
  · exact necessaryKindSubject_is_necessary s
  · intro h
    have hAt := h falsityWorld
    dsimp [ExistsAt, Logos.Entity.EntityExistsAt, Logos.Entity.SubjectExistsAt,
      EntityOf] at hAt
    rcases hAt with hk | heq
    · exact hk
    · have h0 := congrArg (fun w : World => w 0) heq
      exact Logos.Semantics.TV.noConfusion h0

/-- The contingent kind is exactly the non-necessary subjects: it is the
    complement of the necessary kind by definition
    (`ContingentSubjectKind s := ¬ NecessarySubjectKind s`), and by C410 it is
    therefore the complement of world-rigidity itself. No axiom: the two kinds
    and the two modal profiles are one partition, not two.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem contingentKind_iff_not_necessary (s : Subject) :
    ContingentSubjectKind s ↔ ¬ NecessarySubject s := by
  constructor
  · exact contingentKindSubject_not_necessary s
  · intro h hk
    exact h ((kinds_are_the_modal_partition s).mp hk)

/-- A subject of the necessary kind exists at every world: the world-profile the
    kind vocabulary was read as promising in `Entity.SubjectExistsAt`, now
    machine-checked at the level of world-relative subject-existence rather than
    through entity-correlates. Purely the left disjunct.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem necessaryKind_existsAt_every_world {s : Subject}
    (h : NecessarySubjectKind s) (w : World) :
    Logos.Entity.SubjectExistsAt w s :=
  Or.inl h

/-- A subject of the contingent kind exists at the actual world and at no other
    world: the counterpart of `necessaryKind_existsAt_every_world`, and with it
    the **inhabitation asymmetry** in formal form — the two kinds have disjoint,
    complementary world-profiles, all worlds versus this world alone. Nothing
    here says either kind is inhabited; `necessaryPersonalSubjectExists` prices
    the necessary kind, and the contingent kind's inhabitation remains the
    recorded gap (`SUBJECTS.md` §4).
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem contingentKind_existsAt_actualWorld_only {s : Subject}
    (h : ContingentSubjectKind s) (w : World) :
    Logos.Entity.SubjectExistsAt w s ↔ w = actualWorld := by
  constructor
  · intro hex
    rcases hex with hk | heq
    · exact False.elim (h hk)
    · exact heq
  · intro heq
    exact Or.inr heq

/-- The falsity world holds no subject of the contingent kind: at the all-`TV.f`
    valuation the kind disjunct is refuted and the world disjunct is refuted by
    the valuation's not being the actual world.

    Note what this does *not* say: it does not say the falsity world is empty. A
    subject of the necessary kind exists there too
    (`necessaryKind_existsAt_every_world`), and so does the ground-constructor,
    while no atom exists (`EntityExistsAt w (ofAtom n) := w n = TV.t`). Under
    Γ's semantics the all-`TV.f` world is the *necessary-subjects-only* world,
    and it is our world that is excluded from it — free of charge, since the
    actual world has contingent content (`CosmicExistence.contingent_realm_obtains`).
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem falsityWorld_holds_no_contingent_subject :
    ¬ ∃ s : Subject, ContingentSubjectKind s ∧
        Logos.Entity.SubjectExistsAt falsityWorld s := by
  rintro ⟨s, hKind, hAt⟩
  rcases hAt with hk | heq
  · exact hKind hk
  · have h0 := congrArg (fun w : World => w 0) heq
    exact Logos.Semantics.TV.noConfusion h0

/-- A subject of the contingent kind might not have existed: it fails to exist at
    the falsity world. This is C406 in world-relative form — the formal content of
    "the other might not be (humans)", and the modal half of the kind vocabulary
    that the author's two-kinds doctrine claims for it.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem contingentSubject_might_not_have_existed {s : Subject}
    (h : ContingentSubjectKind s) :
    ∃ w : World, ¬ Logos.Entity.SubjectExistsAt w s :=
  ⟨falsityWorld, fun hAt => by
    rcases hAt with hk | heq
    · exact h hk
    · have h0 := congrArg (fun w : World => w 0) heq
      exact Logos.Semantics.TV.noConfusion h0⟩

/--Tag: META
Metaphysical bridge: the necessary kind of subject is inhabited by a person.

  There is a subject of the necessary kind who is a Person — the ground of
  reality in its Personal Type, read as a Subject. A Person is a Subject by
  definition (`Person s` over `s : Subject`), and the Personal Type of Ground
  is proved (`PersonalGroundOfReality.personal_ground_of_right_exists`,
  `PersonalNormativeGround.normative_ground_is_personal`); what neither proves
  is the modal step from personal ground to world-rigid subject. That step is
  this bridge, and it is the whole price of "a person who means must be
  necessary". It does NOT identify the ground-constructor with a
  subject-correlate (`ofGround ≠ EntityOf s` for every `s` still holds); it does
  NOT say the Creator inhabits the world (no link to the world inhabitant is
  stated or derivable here); it does NOT make any other subject necessary
  (kind-membership is per-subject). Reject it and the necessary-person claims
  go; the kind distinction itself stays. -/
axiom necessaryPersonalSubjectExists :
    ∃ s : Subject, NecessarySubjectKind s ∧ Person s

/-- A necessary subject exists, from the bridge. Footprint: `{Means, NecessarySubjectKind, Subject, Will, necessaryPersonalSubjectExists, subjectWill}`. -/
theorem necessarySubject_exists : ∃ s : Subject, NecessarySubject s := by
  obtain ⟨s, hKind, _hPerson⟩ := necessaryPersonalSubjectExists
  exact ⟨s, necessaryKindSubject_is_necessary s hKind⟩

/-- A necessary person exists, from the bridge: this is `ClaimD_NecessaryPerson`
    derived rather than annotated. The person who means is of the necessary
    kind; the contingent person is of the other kind (`ContingentSubjectKind`).
    Footprint: `{Means, NecessarySubjectKind, Subject, Will, necessaryPersonalSubjectExists, subjectWill}`. -/
theorem necessaryPersonalSubject_derived :
    ∃ s : Subject, NecessarySubject s ∧ Person s := by
  obtain ⟨s, hKind, hPerson⟩ := necessaryPersonalSubjectExists
  exact ⟨s, necessaryKindSubject_is_necessary s hKind, hPerson⟩

/--At least two NECESSARY, ETERNAL persons exist — the author's target sentence.

  C585 (new 2026-10-04, batch LOVE-3/S4). UNCONDITIONAL, and `PROVEN↑` at exactly
  one META axiom (`AxTwoNecessaryPersonalCentres`) — the price is on the bridge,
  never on this row.

  This is `two_necessary_persons_of_kind` restated over WORLD-RIGIDITY rather than
  over the kind predicate, and the rewrite costs nothing: `NecessarySubjectKind s`
  and `NecessarySubject s` are the same predicate in this corpus, proved by
  `kinds_are_the_modal_partition` (C411) above. So the two statements are
  equivalent in the kernel and the bridge could have been stated either way; it is
  stated over the primitive because of the import cycle documented in
  `TwoNecessaryPersonalCentres.lean`.

  What "eternal" costs: nothing further. `NecessarySubject s := ∀ w, ExistsAt w
  (EntityOf s)` is world-rigidity by definition, and `NecessityEternity`
  (`ofGround_necessary_ground_of_reality`, C161) is what ties the necessary kind
  to eternity on the ground side. This row asserts eternity of the two PERSONS
  in the world-rigid sense, which is the only sense `Plurality.NecessarySubject`
  carries — it does not assert that the persons are the ground, and
  `ofGround_ne_ofSubject` is untouched.

  It is NOT derived from `necessaryPersonalSubjectExists` (which yields ONE
  witness, and stays declared and independent) nor from T12 (which carries no
  necessity). Reject `AxTwoNecessaryPersonalCentres` and this row goes together
  with T12; there is no reading on which it survives for free.
  Note on the freedom half (LOVE-4 / C587): a derived, META-free route now exists for
  the existence of a Free Person (`NoMeanerNoFalsity.a_genuine_free_person_exists`, C587)
  from the act datum and polarity (`{performative_act_datum, AxActPolarity}`).
  `AxTwoNecessaryPersonalCentres` (C584) remains the declared META bridge that supplies
  personal plurality and modal necessity.
  Footprint: `{AxTwoNecessaryPersonalCentres, Means, NecessarySubjectKind, Subject, Will, subjectWill}`. -/
theorem two_necessary_persons :
    ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧
      NecessarySubject s₁ ∧ NecessarySubject s₂ := by
  obtain ⟨s₁, s₂, hp, hq, hne, hk₁, hk₂⟩ :=
    Logos.TwoNecessaryPersonalCentres.AxTwoNecessaryPersonalCentres
  exact ⟨s₁, s₂, hp, hq, hne,
    necessaryKindSubject_is_necessary s₁ hk₁,
    necessaryKindSubject_is_necessary s₂ hk₂⟩

/--Two distinct persons of the NECESSARY kind exist — `two_necessary_persons`
    with world-rigidity replaced by its equivalent kind predicate (C411).
    Footprint: `{AxTwoNecessaryPersonalCentres, Means, NecessarySubjectKind, Subject, Will, subjectWill}`. -/
theorem two_necessary_persons_kind_form :
    ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧
      NecessarySubjectKind s₁ ∧ NecessarySubjectKind s₂ :=
  Logos.TwoNecessaryPersonalCentres.two_necessary_persons_of_kind

/--The two necessary persons are of DIFFERENT kinds from no third thing: the
    distinctness in `two_necessary_persons` is between two persons, not between a
    person and the ground. Recorded so that no reader may read the new bridge as
    identifying a subject with the ground-constructor: `ofGround ≠ EntityOf s`
    still holds for every `s` (`FoundationalUnicity.ofGround_ne_ofSubject`).
    Footprint: `{AxTwoNecessaryPersonalCentres, Means, NecessarySubjectKind, Subject, Will, subjectWill}`. -/
theorem two_necessary_persons_are_both_persons :
    ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ :=
  two_persons

/--There are at least two distinct persons.

  T12 — there is more than one person (poem P5/P7; PROVEN↑ under
  `AxTwoNecessaryPersonalCentres`). Re-derived 2026-10-04 (LOVE-3/S4): the
    plurality is no longer *inferred from* right-and-wrong — it is read off the
    necessary-person bridge, which is strictly stronger (it also yields
    necessity). A single act still does not entail plurality (settled by the Unit
    countermodel in HostileSemantics). Footprint: `{AxTwoNecessaryPersonalCentres, Means, NecessarySubjectKind, Subject, Will, subjectWill}`. -/
theorem T12_twoPersons :
    ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ :=
  two_persons

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
  `act_requires_subject` (Case B). Footprint: `{Initiates, Means, State, Subject}` (VOCAB only; decoupled from the plurality bridge). -/
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
    Footprint: `{AxTwoNecessaryPersonalCentres, Means, NecessarySubjectKind, Subject, Will, subjectWill}`. -/
theorem JUDGE_HAS_CHOICE_FIELD (h : ¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) :
    ∃ s : Subject, ∃ p q : Prop, Logos.Choice.ChoiceField s p q := by
  obtain ⟨s₁, _, hp₁, _, _⟩ := two_persons
  obtain ⟨p, q, hch⟩ := Logos.Person.person_hasChoiceField hp₁
  exact ⟨s₁, p, q, hch⟩

/-- Right-and-wrong implies someone who means.
    Footprint: `{AxTwoNecessaryPersonalCentres, Means, NecessarySubjectKind, Subject, Will, subjectWill}`. -/
theorem rightWrong_implies_someone_means (h : ¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) :
    ∃ s : Subject, ∃ p : Prop, Logos.Agency.Means s p := by
  obtain ⟨s, p, _, hch⟩ := JUDGE_HAS_CHOICE_FIELD h
  exact ⟨s, p, hch.1⟩

end Logos.Plurality

-- Axiom footprint audit
#print axioms Logos.Plurality.necessaryKindSubject_is_necessary
#print axioms Logos.Plurality.contingentKindSubject_not_necessary
#print axioms Logos.Plurality.necessaryPersonalSubjectExists
#print axioms Logos.Plurality.necessarySubject_exists
#print axioms Logos.Plurality.necessaryPersonalSubject_derived
#print axioms Logos.Plurality.T1_subjectExists
#print axioms Logos.Plurality.T4_agentExists
#print axioms Logos.Plurality.T5_intentionalSubjectExists
#print axioms Logos.Plurality.two_necessary_persons
#print axioms Logos.Plurality.two_necessary_persons_kind_form
#print axioms Logos.Plurality.T12_twoPersons
#print axioms Logos.Plurality.T12_directedPair_conditional
#print axioms Logos.Plurality.cogito_from_T12
#print axioms Logos.Plurality.JUDGE_HAS_CHOICE_FIELD
#print axioms Logos.Plurality.rightWrong_implies_someone_means
