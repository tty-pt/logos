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
(former Agency) and `T5_personExists` (former Person) live HERE as T12
projections. The former `axiom cogito` (Agency) is deleted; its existence
content is resident in `cogito_from_T12` below, and these are its corollaries.
Reason: the `∃ s` witness cannot be manufactured in early modules (the cycle
`Plurality → Value → Person → Agency` blocks imports), so the existence
content moves to where `T12_twoPersons` supplies the witness.
-/

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

/-- cogito, RESTATED AS A THEOREM (cogito-rethinking, 2026-09-15): the former
    performative datum is derivable. From T12 (two persons, `AxTwoSubjects`)
    take one person; `Intentional` gives a content it means, and under the
    Tier-1 collapse (`A s p := Means s p`, `Exists`/`Content`/`Agent`/`Rational`
    all analytical `:= True`) the meaning-act alone fills the act. The denial
    of cogito is therefore refuted by this theorem — exactly as N_T is refuted
    by `Core.notNothingTrue` ("there is no wrong" refutes itself). Only the
    plurality bridge + kind-predicates remain: the price of having the act's
    existence *derived* rather than declared. -/
theorem cogito_from_T12 : ∃ s : Subject, ∃ p : Prop, Logos.Agency.A s p := by
  obtain ⟨s, t, hs, ht, hne⟩ := T12_twoPersons
  obtain ⟨p, hmp⟩ := hs.2.2
  exact ⟨s, p, hmp⟩

/-- T1 — the subject of the present act exists (re-homed from Agency by A1,
    2026-09-16): a corollary of T12 (a person exists, hence a subject exists).
    The former `axiom cogito` is deleted; its existence content lives here. -/
theorem T1_subjectExists : ∃ s : Subject, Logos.Agency.Exists s := by
  obtain ⟨s, _, _, _, _⟩ := T12_twoPersons
  exact ⟨s, trivial⟩

/-- T4 — the subject is an agent (re-homed from Agency by A1; `Agent` is
    analytical `:= True`). -/
theorem T4_agentExists :
    ∃ s : Subject, Logos.Agency.Exists s ∧ Logos.Agency.Agent s := by
  obtain ⟨s, _, _, _, _⟩ := T12_twoPersons
  exact ⟨s, trivial, trivial⟩

/-- T5 — there is a person (re-homed from Person by A1; formerly
    `Person.T5_personExists`, which used the deleted `cogito` axiom). -/
theorem T5_personExists : ∃ s : Subject, Person s := by
  obtain ⟨s, _, hs, _, _⟩ := T12_twoPersons
  exact ⟨s, hs⟩

/-- T12, directed form (chain node C47): the two-person pair can be oriented
    so that affectivity flows named-forward — the C3-I bridge `AxPersonsAffect`
    decides the direction by cases. Adds a named step between T12 and the
    love layer: direction + stability must hold of the *same* pair, so T14 is
    built on this pair rather than on a lone stability-only node (rejected:
    direction and stability would then be unconnected). -/
theorem T12_directedPair :
    ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ Affects s₁ s₂ := by
  obtain ⟨p, q, hp, hq, hne⟩ := T12_twoPersons
  have hA : Affects p q ∨ Affects q p := AxPersonsAffect p q hp hq hne
  cases hA with
  | inl hpq => exact ⟨p, q, hp, hq, hne, hpq⟩
  | inr hqp => exact ⟨q, p, hq, hp, hne.symm, hqp⟩

end Logos.Plurality

-- Axiom footprint audit
#print axioms Logos.Plurality.T1_subjectExists
#print axioms Logos.Plurality.T4_agentExists
#print axioms Logos.Plurality.T5_personExists
#print axioms Logos.Plurality.T12_twoPersons
#print axioms Logos.Plurality.T12_directedPair
#print axioms Logos.Plurality.cogito_from_T12