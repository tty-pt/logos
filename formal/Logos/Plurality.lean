/-
# Logos.Plurality — more than one person (poem P5/P7; theorem T12)

T12 — from the necessary right/wrong (`Core.rightWrongDistinction`, PROVEN)
and the META bridge `AxTwoSubjects` (Value), there are at least two
distinct persons. This is the poem's "tem de haver mais do que uma pessoa"
and its "não é sózinho". Affectivity between them is the SEM meaning-postulate
`AxPersonsAffect` (C3-I split of the former `AxValueInterpersonal`).

Also hosts the Q2 bridge `EntityOf : Subject → Entity` (each person has an
entity-correlate), decided to close the Subject/Entity gap so the love layer
can attach necessity to the relata (T14).

A1 (2026-09-16): the existence theorems `T1_subjectExists`, `T4_agentExists`
(former Agency) and `T5_personExists` (former Person) live HERE, and M0
(2026-09-16, FORCED_SUBJECT.md) re-anchors all of them — plus
`cogito_from_T12` — on the *forced foundation* `Agency.Cogito`, NOT on the
plurality bridge. A1's cycle reason (`Plurality → Value → Person → Agency`)
is respected by importing only the foundation, never proving from T12.
Only `T12_twoPersons`, `notAlone`, and `T12_directedPair` still stand on
`AxTwoSubjects` — they are the genuine plurality claims. -/

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
open Logos.Value (AxTwoSubjects Affects AxPersonsAffect)

/-- Q2 bridge, now definitional (C2, 2026-09-15): since `Entity := Subject`
    (Truthmaker), every subject *is already* an entity — first-person acts and
    third-person realities identify the same thing. `EntityOf` is the identity. -/
def EntityOf : Subject → Entity := fun s => s

/-- A subject is necessary iff its entity-correlate exists in every world. -/
def NecessarySubject (s : Subject) : Prop := ∀ w : World, ExistsAt w (EntityOf s)

/-- T12 — there is more than one person (poem P5/P7; PROVEN↑ under
    `AxTwoSubjects`). -/
theorem T12_twoPersons :
    ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ :=
  AxTwoSubjects Logos.Core.rightWrongDistinction

/-- "Not alone": some pair of distinct persons exists (the same result,
    restated in the poem's vocabulary). -/
theorem notAlone : ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ :=
  T12_twoPersons

/-- cogito, RESTATED AS A COROLLARY OF THE FORCED FOUNDATION (M0,
    FORCED_SUBJECT.md, 2026-09-16): the present act is *given*, not derived
    from plurality. `cogito_from_T12` survives as a corollary of
    `Agency.Cogito` — the former T12-derivation is conserved but re-classified:
    plurality also forces the datum, the datum is not *grounded* on plurality.
    Its denial is refuted by `Agency.noCogito_selfRefutes`, not (any longer)
    by a detour through two persons. -/
theorem cogito_from_T12 : ∃ s : Subject, ∃ p : Prop, Logos.Agency.A s p :=
  Logos.Agency.Cogito

/-- T1 — the subject of the present act exists (M0 re-anchor, 2026-09-16):
    corollary of the forced foundation, not of the pair. -/
theorem T1_subjectExists : ∃ s : Subject, Logos.Agency.Exists s := by
  obtain ⟨s, _, _⟩ := Logos.Agency.Cogito
  exact ⟨s, trivial⟩

/-- T4 — the subject is an agent (M0 re-anchor; `Agent` is analytical
    `:= True`). -/
theorem T4_agentExists :
    ∃ s : Subject, Logos.Agency.Exists s ∧ Logos.Agency.Agent s := by
  obtain ⟨s, _, _⟩ := Logos.Agency.Cogito
  exact ⟨s, trivial, trivial⟩

/-- T5 — there is a person (M0 re-anchor): from the forced act the witness
    subjects own personhood trivially — `Agent`/`Rational` are analytical
    `:= True` and the act's own content witnesses `Intentional`. -/
theorem T5_personExists : ∃ s : Subject, Person s := by
  obtain ⟨s, p, hmp⟩ := Logos.Agency.Cogito
  exact ⟨s, trivial, trivial, p, hmp⟩

/-- T12, directed form (chain node C47; M1 2026-09-16): the two-person pair can
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