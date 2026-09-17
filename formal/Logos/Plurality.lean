/-
# Logos.Plurality — more than one person (poem P5/P7; theorem T12)

T12 — there are at least two distinct persons. From the definitional subject
alone (plurality-discharge, 2026-09-17): the canonical pair (the origin
`Sum.inl ()` and the addressee `Sum.inr True`) is exhibited by
`Person.twoPersonsFromSubject` with no axiom — the former META bridge
`AxTwoSubjects` is retired (its content moved into the definition of a
subject) and the M2 lone-subject countermodel is superseded. Affectivity
between distinct persons is the theorem `AxPersonsAffect` (A3).

Also hosts the Q2 bridge `EntityOf : Subject → Entity` (each person has an
entity-correlate), decided to close the Subject/Entity gap so the love layer
can attach necessity to the relata (T14).

A1 (2026-09-16): the existence theorems `T1_subjectExists`, `T4_agentExists`
(former Agency) and `T5_personExists` (former Person) live HERE; M0
(2026-09-16, FORCED_SUBJECT.md) re-anchored all of them — plus
`cogito_from_T12` — on `Agency.Cogito`, NOT on the plurality bridge, and the
definitional-subject batch (2026-09-17) made `Cogito` itself a theorem.
A1's cycle reason (`Plurality → Value → Person → Agency`)
is respected by importing only the foundation, never proving from T12.
`T12_twoPersons`, `notAlone`, and `T12_directedPair` are the genuine plurality
claims, all now PROVEN `{}`. -/

import Logos.Core
import Logos.Agency
import Logos.Person
import Logos.Value
import Logos.Truthmaker

namespace Logos.Plurality

open Logos.Agency (Subject)
open Logos.Person (Person)
open Logos.Truthmaker (Entity ExistsAt)
open Logos.Semantics (World)
open Logos.Value (Affects AxPersonsAffect)

/-- Q2 bridge, now definitional (C2, 2026-09-15): since `Entity := Subject`
    (Truthmaker), every subject *is already* an entity — first-person acts and
    third-person realities identify the same thing. `EntityOf` is the identity. -/
def EntityOf : Subject → Entity := fun s => s

/-- A subject is necessary iff its entity-correlate exists in every world. -/
def NecessarySubject (s : Subject) : Prop := ∀ w : World, ExistsAt w (EntityOf s)

/--There are at least two distinct persons.

  T12 — there is more than one person (poem P5/P7; PROVEN, definitional
    subject, 2026-09-17): the canonical pair of
    `Person.twoPersonsFromSubject` — the origin and the addressee — with no
    axiom. Formerly PROVEN↑ under the META bridge `AxTwoSubjects` (retired). -/
theorem T12_twoPersons :
    ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ :=
  Logos.Person.twoPersonsFromSubject

/-- "Not alone": some pair of distinct persons exists (the same result,
    restated in the poem's vocabulary). -/
theorem notAlone : ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ :=
  T12_twoPersons

/--The acting subject is exhibited: someone acts on something.

 cogito, RESTATED AS A COROLLARY OF THE THEOREM (definitional subject,
    2026-09-17): the present act is exhibited, not postulated and not derived
    from plurality. `cogito_from_T12` is a corollary of `Agency.Cogito` —
    the former T12-derivation is conserved but re-classified: plurality also
    forces the datum, the datum is not *grounded* on plurality. Its denial
    is refuted by `Agency.noCogito_selfRefutes`, not (any longer) by a
    detour through two persons. -/
theorem cogito_from_T12 : ∃ s : Subject, ∃ p : Prop, Logos.Agency.A s p :=
  Logos.Agency.Cogito

/--At least one subject exists.

 T1 — the subject of the present act exists (definitional subject,
    2026-09-17): corollary of the exhibited act, not of the pair. -/
theorem T1_subjectExists : ∃ s : Subject, Logos.Agency.Exists s := by
  obtain ⟨s, _, _⟩ := Logos.Agency.Cogito
  exact ⟨s, trivial⟩

/--At least one agent exists: someone who acts.

 T4 — the subject is an agent (definitional subject; `Agent` is analytical
    `:= True`). -/
theorem T4_agentExists :
    ∃ s : Subject, Logos.Agency.Exists s ∧ Logos.Agency.Agent s := by
  obtain ⟨s, _, _⟩ := Logos.Agency.Cogito
  exact ⟨s, trivial, trivial⟩

/--At least one person exists.

 T5 — there is a person (definitional subject): from the exhibited act the
    witness subjects own personhood trivially — `Agent`/`Rational` are
    analytical `:= True` and the act's own content witnesses `Intentional`. -/
theorem T5_personExists : ∃ s : Subject, Person s := by
  obtain ⟨s, p, hmp⟩ := Logos.Agency.Cogito
  exact ⟨s, trivial, trivial, p, hmp⟩

/--There are two distinct persons where one bears on the other.

 T12, directed form (chain node C47; M1 2026-09-16): the two-person pair can
    be oriented so that affectivity flows named-forward — under A3
    (`Affects s t := s ≠ t`) distinctness IS the forward direction, so the
    directed pair is `T12_twoPersons` itself wearing its own inequality.
    Direction + stability still must hold of the *same* pair, so T14 is
    built on this pair (rejected: direction and stability unconnected). -/
theorem T12_directedPair :
    ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ Affects s₁ s₂ := by
  obtain ⟨p, q, hp, hq, hne⟩ := T12_twoPersons
  exact ⟨p, q, hp, hq, hne, hne⟩

end Logos.Plurality

-- Axiom footprint audit
#print axioms Logos.Plurality.T1_subjectExists
#print axioms Logos.Plurality.T4_agentExists
#print axioms Logos.Plurality.T5_personExists
#print axioms Logos.Plurality.T12_twoPersons
#print axioms Logos.Plurality.T12_directedPair
#print axioms Logos.Plurality.cogito_from_T12
