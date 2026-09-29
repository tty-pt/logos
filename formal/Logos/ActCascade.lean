/-
# Logos.ActCascade — the act-datum's own consequences, no longer stated as conditionals

Authorised 2026-09-28. The plan of record is `WIN.md`.

## The finding

`Agency.performative_act_datum` (C454) is an **unconditional axiom**: `∃ s, ∃ p, Act s p`. A scan
of every `theorem`/`lemma` statement in `formal/Logos/*.lean` finds **18 theorems across five
modules** whose hypothesis list is *exactly* that proposition and nothing else —

| module | theorems |
|---|---|
| `Agency.lean` | `act_datum_implies_means`, `act_datum_implies_initiates`, `subject_exists_of_act`, `an_actual_subject_exists_of_act`, `T1_subjectExists_of_act` |
| `Choice.lean` | `genuineChoice_exists_of_act`, `genuineChoice_exists_of_act_constitutive`, `freeWill_exists_of_act`, `freeSubject_exists_of_act`, `freeWill_exists_of_act_polarity`, `freeWill_exists`, `freeSubject_exists` |
| `Person.lean` | `intentionalSubject_exists_of_act`, `intentional_exists_of_act` |
| `Plurality.lean` | `T1_subjectExists`, `T4_agentExists`, `T5_intentionalSubjectExists` |
| `MeaningRetorsion.lean` | `noMeaning_is_refuted_from_the_act_datum` |

A hypothesis that is itself a declared axiom of Γ is not a hypothesis; it is a leftover from
before the datum was admitted on 2026-09-28. Each of the 18 is a one-line corollary of a
parent that already exists and whose proof already exists. This module collects those corollaries
in one place. **No axiom is added, no existing proof is altered, and no existing statement is
weakened.** Twelve new theorems; the module is 12 declarations and 12 `#print axioms` lines.

The 18 collapse to 12 new declarations, because the conclusions are not 18 distinct facts:

- `act_datum_implies_initiates` already has its unconditional form — that is **C455**,
  `some_subject_initiates`. Listed only to show the set is complete.
- `subject_exists_of_act`, `T1_subjectExists_of_act`, `T1_subjectExists` are the same statement
  (`∃ s, SubjectExists s`), the last two by `=`.
- `intentionalSubject_exists_of_act` and `T5_intentionalSubjectExists` are the same statement.
- `freeWill_exists_of_act` and `freeWill_exists` are the same; so are
  `freeSubject_exists_of_act` and `freeSubject_exists`.
- `genuineChoice_exists_of_act` and `freeWill_exists_of_act_polarity` reach their conclusion by
  `AxActPolarity` where the `_constitutive` siblings reach it by `AxIntentionalChoice`, so the two
  routes get one row each and their footprints differ.

## The disclosure: this cascade is not free

Every one of the twelve rows **gains `performative_act_datum` in its audited footprint**, and the
rows that close a route through a semantic axiom keep that axiom too. The conditional parents let a
reader believe the act was still an open question; the price was hidden in a binder. The rows below
carry the price **visibly and mandatorily** on their own footprint. That is the whole change, and
it is a disclosure, not a strengthening of Γ: Γ has one more theorem about a seventh thing, not
one more premise.

## What this module does NOT do

**The `Asserts` lane stays closed, by construction.** `Asserts s p := Act s p ∧ p`
(`Agency.lean:401`), so C454 yields no `Asserts`-existential: no proposition is available that is
both `Act`-bearing and true. The bridge `act_implies_asserts_bridge` (`Choice.lean:653`) therefore
remains unpriced, and these twelve theorems **stay conditional** and are deliberately not touched:
`selection_exists_of_act`, `genuineChoice_exists_of_contrastive_act`,
`freeWill_exists_of_contrastive_act`, `freeSubject_exists_of_contrastive_act`,
`genuineChoice_exists_of_doubt_bridge`, `freeWill_exists_of_doubt_bridge`,
`genuineChoice_exists_of_act_polarity`, `genuineChoice_exists_of_bilateral_intentionality`,
`deliberateResource_of_act_polarity`, `deliberateResource_of_bilateral_intentionality`,
`act_polarity_implies_existential`, `freeWill_exists_of_existential_choice`. The first ten are
blocked by a semantic principle or by the unpriced bridge; the last two are blocked by a
*universal* premise about all acts (`act_polarity_principle`, `existential_intentional_choice`),
which a single existential witness cannot discharge.

Also unchanged, and stated here so no row below is read as more than it is:

- **C453 stayed open in this batch.** The datum is a global existential. The per-subject form of initiation is a
  different and stronger claim and was not proved here; `noCogito_selfRefutes` (C456) records this. Chain 13 now closes that stronger universal as non-derivable through C489–C490.
- **Nothing here says which subject acts.** Same reason, same `INHABITED.md` §7 boundary.
- **No `Wills → Initiates`, `Means → Initiates`, `Chooses → Initiates` or `Loves → Initiates`
  bridge** is licensed. These are existentials, not implications, so every separation between
  volition, meaning and initiation in the corpus survives untouched.
- **The ground is not made an agent.** `Entity.ofGround` is still provably not a subject
  (`ofGround_ne_ofSubject`). Nothing here bears on F10 `Produces`, on C462, or on `Creator of
  contingent reality`, and no row about the ground is asserted anywhere in this module.
- **C465/C467 stay conditional** and **F10 stayed `BLOCKED` in this batch** (since closed by the declared C493 bridge, which changes nothing here). Both walls are named and
  machine-checked in `WIN.md` §2; neither is touched here.
- **`NotInSuccession` is not revisited.** Batch S's diagnosis stands untouched.
- **The free-will rows are consequences of C454, not a refutation of C454's denial from nothing.**
  Refuting that denial requires an inhabitant of `Act`, which is precisely what C454 supplies and
  what is unavailable without it (`INHABITED.md` §0). Citing `freeWill_exists_of_act_datum_*` in
  C454's own favour would be circular, exactly as the C456 docstring records for its analogue.

**One row is weaker than its name suggests, and says so.** `an_agent_exists` (C472) is
`∃ s, SubjectExists s ∧ Agent s`, and `Agent (_s : Subject) : Prop := True` (`Agency.lean:78`) —
the second conjunct is vacuous. So C472 is exactly as strong as `someone_exists_as_subject` (C470)
and no stronger. It is a legitimate row because `T4_agentExists` is a named step of the corpus's
T-chain, but it is a *re-packaging* of C470, not a seventh independent result, and the C321
precedent (`capacity_invariance_holds_for_every_entity`, a property of everything that is not a
characterisation) is recorded against it.
-/

import Logos.Core
import Logos.Semantics
import Logos.Entity
import Logos.Agency
import Logos.Person
import Logos.Choice
import Logos.Plurality
import Logos.MeaningRetorsion

namespace Logos.ActCascade

/-! ## Part I: the rows that C454 alone discharges

Each is `parent performative_act_datum`. The hypothesis of every parent is a declared axiom of Γ,
so applying the parent is `exact` and nothing else. -/

/-- Something means something: a subject is related to a proposition by meaning, unconditionally.

    **What it discharges.** C454 (`performative_act_datum`) alone, via
    `Agency.act_datum_implies_means` — which is the `Act`/`Means` half of `Act`'s own definition.

    **What it does NOT do.** It does not say *which* subject means, or what it means: a global
    existential, so C453's per-subject form stayed open in this batch (`INHABITED.md` §7, later closed as non-derivable by Chain 13). It licenses no
    `Means → Initiates` bridge. It does not make the ground an agent, so F10 `Produces` and C462
    are untouched. It did not close C453 in this batch. It is a consequence of C454, **not** a refutation of
    C454's denial from nothing — refuting that denial needs an inhabitant of `Act`, which is what
    C454 supplies and what is unavailable without it (`INHABITED.md` §0), so citing this row in
    the datum's own favour would be circular. The price is `performative_act_datum`, now **visible
    and mandatory**, where the conditional parent let a reader believe the act was still open.

    Footprint: `{Initiates, Means, State, Subject, performative_act_datum}` -/
theorem someone_means_something : ∃ s : Agency.Subject, ∃ p : Prop, Agency.Means s p :=
  Agency.act_datum_implies_means Agency.performative_act_datum

/-- Someone is an actualized subject: subjecthood in actuality obtains.

    **What it discharges.** C454 alone, via `Agency.subject_exists_of_act` →
    `Agency.act_requires_subject`, the constitutive law that an act cannot occur without the
    subject performing it.

    **What it does NOT do.** As `someone_means_something`: a global existential, so nothing about
    which subject, and no volition/meaning/initiation bridge. C453 and C465/C467 and F10 are all
    untouched. It is a consequence of C454 and citing it in the datum's favour is circular. The
    price is `performative_act_datum`, now visible and mandatory.

    Footprint: `{Initiates, Means, State, Subject, performative_act_datum}` -/
theorem someone_exists_as_subject : ∃ s : Agency.Subject, Agency.SubjectExists s :=
  Agency.subject_exists_of_act Agency.performative_act_datum

/-- The existential proposition `AnActualSubjectExists` obtains.

    **What it discharges.** C454 alone, via `Agency.an_actual_subject_exists_of_act`. Definition-
    ally the same claim as `someone_exists_as_subject`: `AnActualSubjectExists` is defined as
    `∃ s, SubjectExists s` (`Agency.lean:276`). The row exists because the corpus states the
    existential proposition in that form, not to add a second result.

    **What it does NOT do.** As `someone_means_something`: no per-subject content, no bridge, no
    bearing on the ground, C453, C465/C467 or F10. A consequence of C454, so circular to cite in
    the datum's favour. The price is `performative_act_datum`, now visible and mandatory.

    Footprint: `{Initiates, Means, State, Subject, performative_act_datum}` -/
theorem an_actual_subject_obtains : Agency.AnActualSubjectExists :=
  Agency.an_actual_subject_exists_of_act Agency.performative_act_datum

/-- An agent exists, in the T4 sense — and the `Agent` field of that sense is vacuous.

    **This row is a re-packaging, and must not be read as a seventh result.** `Agent` is
    `def Agent (_s : Subject) : Prop := True` (`Agency.lean:78`), so the second conjunct of this
    statement is unconditionally true and this row is **exactly as strong as
    `someone_exists_as_subject` and no stronger**. The C321 precedent applies: a property that
    holds of everything is not a characterisation of the thing it names. What this row discharges
    is the T-chain step `T4_agentExists`, which the corpus states in this shape; it is not
    evidence of agency in any sense the word carries outside that `def`.

    **What it discharges.** C454 alone, via `Plurality.T4_agentExists`.

    **What it does NOT do.** It does not establish that anything is an agent in a substantive
    sense; it establishes that subjecthood obtains, under a name whose agent field is `True`. It
    says nothing about which subject, licenses no bridge, and does not make the ground an agent —
    `Entity.ofGround` is provably not a subject, so F10, C462, C465/C467 are untouched. It does
    not close C453. A consequence of C454, so circular to cite in the datum's favour. The price is
    `performative_act_datum`, now visible and mandatory.

    Footprint: `{Initiates, Means, State, Subject, performative_act_datum}` -/
theorem an_agent_exists : ∃ s : Agency.Subject, Agency.SubjectExists s ∧ Agency.Agent s :=
  Plurality.T4_agentExists Agency.performative_act_datum

/-! ## Part II: the rows that instantiate intentionality -/

/-- An intentional subject exists: some subject bears a meaning.

    **What it discharges.** C454 alone, via `Person.intentionalSubject_exists_of_act` →
    `Person.act_implies_intentionalSubject`. Together with `someone_means_something` this is the
    T5 reading: intentionality is instantiated in the same theory, from the same single price.

    **What it does NOT do.** It does not add to `someone_means_something`: `IntentionalSubject s`
    is *defined* as `∃ p, Means s p` (`Agency.lean:96`), so this row is that row with the witness
    re-ordered — it states the T-chain's subject-side shape, not a new fact. It does not say which
    subject is intentional, licenses no `Means → Initiates` or `Intentional → Initiates` bridge,
    and does not make the ground an agent (F10, C462, C465/C467 untouched). It does not close
    C453. A consequence of C454, so circular to cite in the datum's favour. The price is
    `performative_act_datum`, now visible and mandatory.

    Footprint: `{Initiates, Means, State, Subject, performative_act_datum}` -/
theorem an_intentional_subject_exists : ∃ s : Agency.Subject, Agency.IntentionalSubject s :=
  Person.intentionalSubject_exists_of_act Agency.performative_act_datum

/-- Intentionality is instantiated: some subject is intentional.

    **What it discharges.** C454 alone, via `Person.intentional_exists_of_act`. `Intentional` is
    `def Intentional (s : Subject) : Prop := IntentionalSubject s` (`Agency.lean:99`), so this row
    is `an_intentional_subject_exists` under the other of the corpus's two names for the same
    predicate, kept because both names are load-bearing in the prose.

    **What it does NOT do.** Everything `an_intentional_subject_exists` does not do, and one thing
    more: it is the weakest form of "intentional" in the corpus and must not be read as
    intentionality *of a particular act* or as any bridge to volition. No per-subject content, no
    bridge, nothing about the ground, C453, C465/C467 or F10. A consequence of C454, so circular
    to cite in the datum's favour. The price is `performative_act_datum`, now visible and
    mandatory.

    Footprint: `{Initiates, Means, State, Subject, performative_act_datum}` -/
theorem intentionality_is_instantiated : ∃ s : Agency.Subject, Agency.Intentional s :=
  Person.intentional_exists_of_act Agency.performative_act_datum

/-! ## Part III: the genuine-choice and free-will rows, two routes each

Both routes start from C454 and then differ in which *already declared* semantic axiom closes the
step from a meaning to a choice. The two routes are separate rows because their audited footprints
differ, and the corpus prices them separately. -/

/-- Genuine choice exists, via the constitutive route: the act's intentional content is itself
    sufficient for genuine choice.

    **What it discharges.** C454 **plus** `AxIntentionalChoice` (`Tag: SEM`, priced), via
    `Choice.genuineChoice_exists_of_act_constitutive`. The act-datum supplies the witness; the
    semantic axiom supplies the constitutive claim that a chooser with intentional content is
    genuinely choosing. Two prices, both on the row.

    **What it does NOT do.** It does not remove the semantic price — this route is the
    `AxIntentionalChoice` one and `genuineChoice_exists_of_act_datum_polarity` is the
    `AxActPolarity` one; neither is free, and `AxActPolarity` is not a substitute for
    `AxIntentionalChoice` (each is separately declared, `Tag: SEM`). It is an existential: it does
    not say *who* chooses, and it licenses no `Chooses → Initiates` bridge, so the corpus's
    separation between choice and initiation survives untouched. It does not make the ground a
    chooser, so F10 `Produces`, C462, C465/C467 are untouched. It did not close C453 in this batch. It is a
    consequence of C454, **not** a refutation of C454's denial from nothing, and citing it in the
    datum's favour would be circular. The price is `performative_act_datum` **and**
    `AxIntentionalChoice`, both visible and mandatory, where the conditional parent hid both in
    binder and axiom respectively.

    Footprint: `{AxIntentionalChoice, Initiates, Means, State, Subject, performative_act_datum}` -/
theorem genuineChoice_exists_of_act_datum_constitutive : Choice.genuineChoice_exists :=
  Choice.genuineChoice_exists_of_act_constitutive Agency.performative_act_datum

/-- Genuine choice exists, via the polarity route: an act means a proposition and its negation, so
    a chooser faces a real alternative.

    **What it discharges.** C454 **plus** `AxActPolarity` (`Tag: SEM`, priced), via
    `Choice.genuineChoice_exists_of_act`. The act-datum supplies the witness; the semantic axiom
    supplies the claim that an act is polar — that acting on `p` also means `¬p` — which is what
    makes the choice genuine rather than merely free of obstruction.

    **What it does NOT do.** It does not remove the semantic price; see the constitutive row. The
    polarity reading is a *different* semantic choice from the constitutive one, not a stronger
    one, and the corpus declares both. It is an existential: no `Chooses → Initiates` bridge, no
    statement about which subject, nothing about the ground, C453, C465/C467 or F10. A consequence
    of C454, so circular to cite in the datum's favour. The price is `performative_act_datum`
    **and** `AxActPolarity`, both visible and mandatory.

    Footprint: `{AxActPolarity, Initiates, Means, State, Subject, performative_act_datum}` -/
theorem genuineChoice_exists_of_act_datum_polarity : Choice.genuineChoice_exists :=
  Choice.genuineChoice_exists_of_act Agency.performative_act_datum

/-- Some subject has free will, via the constitutive route.

    **What it discharges.** C454 **plus** `AxIntentionalChoice` (`Tag: SEM`, priced), via
    `Choice.freeWill_exists` → `Choice.freeWill_exists_of_act` →
    `Choice.genuineChoice_exists_of_act_constitutive`. This is the row that discharges the
    corpus's headline "free will exists" from the performative datum, in the T-chain's own shape.

    **What it does NOT do.** It does not remove the semantic price. It is an existential over
    subjects: it does not say *which* subject has free will, does not assert that every subject
    does, and licenses no `Wills → Initiates` or `Chooses → Initiates` bridge. It does not make
    the ground a chooser — `Entity.ofGround` is provably not a subject — so F10 `Produces`, C462,
    C465/C467 are untouched. It did not close C453 in this batch. It is a consequence of C454, **not** a
    refutation of C454's denial from nothing, and citing it in the datum's favour would be
    circular. The price is `performative_act_datum` **and** `AxIntentionalChoice`, both visible
    and mandatory, where the conditional parent hid the first in a binder.

    Footprint: `{AxIntentionalChoice, Initiates, Means, State, Subject, performative_act_datum}` -/
theorem freeWill_exists_of_act_datum_constitutive : ∃ s : Agency.Subject, Choice.FreeWill s :=
  Choice.freeWill_exists Agency.performative_act_datum

/-- Some subject has free will, via the polarity route.

    **What it discharges.** C454 **plus** `AxActPolarity` (`Tag: SEM`, priced), via
    `Choice.freeWill_exists_of_act_polarity` → `Choice.genuineChoice_exists_of_act`. A second,
    independent route to the same conclusion, with a different second price.

    **What it does NOT do.** As the constitutive row: an existential, no per-subject content, no
    volition-to-initiation bridge, nothing about the ground, C453, C465/C467 or F10. The polarity
    reading does not strengthen the constitutive one; it is an alternative, separately priced route
    and both remain declared. A consequence of C454, so circular to cite in the datum's favour.
    The price is `performative_act_datum` **and** `AxActPolarity`, both visible and mandatory.

    Footprint: `{AxActPolarity, Initiates, Means, State, Subject, performative_act_datum}` -/
theorem freeWill_exists_of_act_datum_polarity : ∃ s : Agency.Subject, Choice.FreeWill s :=
  Choice.freeWill_exists_of_act_polarity Agency.performative_act_datum

/-- Some subject is a free subject.

    **What it discharges.** C454 **plus** `AxIntentionalChoice` (`Tag: SEM`, priced), via
    `Choice.freeSubject_exists`. `FreeSubject` is *defined* as `FreeWill s` (`Choice.lean:185`), so
    this row is the free-will row under the corpus's third name for the same predicate, kept
    because the prose uses all three and an existential of the narrower name is not literally an
    existential of the wider one until the `def` is read.

    **What it does NOT do.** It adds nothing to `freeWill_exists_of_act_datum_constitutive` beyond
    the `def`; it must not be read as free *subjecthood* in any sense the `def` does not license
    (no capacity claim, no `Asiety`, no F15 `SemanticFinitude` per-subject bound). As that row: an
    existential, no per-subject content, no bridge, nothing about the ground, C453, C465/C467 or
    F10. A consequence of C454, so circular to cite in the datum's favour. The price is
    `performative_act_datum` **and** `AxIntentionalChoice`, both visible and mandatory.

    Footprint: `{AxIntentionalChoice, Initiates, Means, State, Subject, performative_act_datum}` -/
theorem freeSubject_exists_of_act_datum : ∃ s : Agency.Subject, Choice.FreeSubject s :=
  Choice.freeSubject_exists Agency.performative_act_datum

/-! ## Part IV: the retorsion row -/

/-- Meaninglessness is refuted: `¬ NoMeaning`, unconditionally.

    **What it discharges.** C454 alone, via `MeaningRetorsion.noMeaning_is_refuted_from_the_act_datum`
    → `Agency.act_datum_implies_means`. Meaningfulness is not a bridge and not a semantic axiom
    here: `NoMeaning` denies that any proposition is a `Meaning_I`, and the act-datum's `Means`
    horn is already a witness. This is the cheapest row in the batch — one price, and the price is
    the same one every other row pays.

    **What it does NOT do.** It does not enumerate what is meaningful, does not say which subject
    means, and does not bound the meanings (F15 `SemanticFinitude` is untouched and separate). It
    licenses no `Means → Initiates` bridge and does not make the ground meaningful, so F10
    `Produces`, C462, C465/C467 are untouched. It did not close C453 in this batch. A consequence of C454, so
    circular to cite in the datum's favour. The price is `performative_act_datum`, now visible and
    mandatory.

    Footprint: `{Initiates, Means, State, Subject, performative_act_datum}` -/
theorem noMeaning_is_refuted_unconditionally : ¬ MeaningRetorsion.NoMeaning :=
  MeaningRetorsion.noMeaning_is_refuted_from_the_act_datum Agency.performative_act_datum

#print axioms someone_means_something
#print axioms someone_exists_as_subject
#print axioms an_actual_subject_obtains
#print axioms an_agent_exists
#print axioms an_intentional_subject_exists
#print axioms intentionality_is_instantiated
#print axioms genuineChoice_exists_of_act_datum_constitutive
#print axioms genuineChoice_exists_of_act_datum_polarity
#print axioms freeWill_exists_of_act_datum_constitutive
#print axioms freeWill_exists_of_act_datum_polarity
#print axioms freeSubject_exists_of_act_datum
#print axioms noMeaning_is_refuted_unconditionally

end Logos.ActCascade
