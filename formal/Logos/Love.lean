/-
# Logos.Love — the beloved (poem P7/P8; theorems T13, T14)

T13 (someone able to be loved): from T12, each of two persons is *able to be
loved* by the other (`Lovable`). PROVEN.

T14 (eternal relation): the strong claim — the beloved of the necessary
person is itself necessary and is loved eternally: the poem's "Amar é
escolhido e também é necessário (de alguma forma)". Since C4 (2026-09-15)
the relation itself is *structural*: `Loves := Affects` (directed constitutive
bearing; the affective fullness stays on the prose side). T14 is now PROVEN↑
under the C3-I bridges + the priced SEM bridge `AxPersonStability` (every
person's entity-correlate exists in all worlds — the "de alguma forma"). The
"chosen" component depends on F1 (freedom, DEFERRED).
-/

import Logos.Core
import Logos.Agency
import Logos.Person
import Logos.Value
import Logos.Plurality
import Logos.Necessity

namespace Logos.Love

open Logos.Agency (Subject)
open Logos.Person (Person)
open Logos.Plurality (EntityOf NecessarySubject)
open Logos.Value (Affects AxPersonsAffect)
open Logos.Semantics (World)
open Logos.Truthmaker (ExistsAt)
open Logos.Necessity (Necessity NecessityPH)

/-- `Loves s t`: `s`'s constitutive bearing is directed at `t` — structural
    reading (C4): love is `Affects` (the "ajuda/não prejudica" of the poem,
    P6). The affective fullness of "Amar" stays on the prose side unless and
    until a future choice enriches the definition. -/
def Loves (s t : Subject) : Prop := Affects s t

/-- `Lovable t`: there is some other person who could love `t` ("quem se
    possa Amar"). -/
def Lovable (t : Subject) : Prop := ∃ s : Subject, s ≠ t ∧ Person s

/-- T13 — there is someone able to be loved (poem P7; PROVEN from T12):
    each member of the two-person pair is lovable by the other. -/
theorem T13_someoneLovable :
    ∃ s t : Subject, Person s ∧ Person t ∧ s ≠ t ∧ Lovable s ∧ Lovable t := by
  obtain ⟨p, q, hp, hq, hne⟩ := Logos.Plurality.T12_twoPersons
  exact ⟨p, q, hp, hq, hne,
    ⟨q, hne.symm, hq⟩,
    ⟨p, hne, hp⟩⟩

/-- AxPersonStability (SEM; poem P8 "de alguma forma", DESIGN.md D-C4): every
    person's entity-correlate exists in every world — persons are NOT
    world-contingent. This carries the *eternal* half of T14, attached to the
    relata rather than declared directly over a relation (C4). Exclusion
    attempt recorded in /tmp/opencode/x2_spikeD.lean: Person's agency structure
    (T5) gives no fact about which worlds the correlate inhabits, so the claim
    is underivable; declared as a priced bridge. -/
axiom AxPersonStability : ∀ s : Subject, Person s → NecessarySubject s

/-- T14 — the eternal love-relation (PROVEN under the C3-I bridges +
    AxPersonStability): a pair of distinct persons who love each other, both
    of whose entity-correlates exist in *every* world — the poem's "Amar é
    escolhido e também é necessário (de alguma forma)". Built on the directed
    pair `Plurality.T12_directedPair` (C47): direction and stability live on
    the *same* pair. -/
theorem T14_eternalRelation :
    ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧
      Loves s₁ s₂ ∧ NecessarySubject s₁ ∧ NecessarySubject s₂ := by
  obtain ⟨p, q, hp, hq, hne, hl⟩ := Logos.Plurality.T12_directedPair
  exact ⟨p, q, hp, hq, hne, hl, AxPersonStability p hp, AxPersonStability q hq⟩

/-- T14, world-anchored form (`NecessityPH`): in every world there is a pair of
    distinct persons who love each other and whose entity-correlates exist in
    that world. This is the honest, world-indexed content of "eternal" — the
    love-relation, the relata, and the stability (from AxPersonStability). -/
theorem T14_world : NecessityPH
    (fun _w : World =>
      ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧
        Loves s₁ s₂ ∧ ExistsAt _w (EntityOf s₁) ∧ ExistsAt _w (EntityOf s₂)) := by
  obtain ⟨p, q, hp, hq, hne, hl, hNs, hNq⟩ := T14_eternalRelation
  intro w
  exact ⟨p, q, hp, hq, hne, hl, hNs w, hNq w⟩

/-- T14 in the *alias* modality (C1: `Necessity p := ∀ _w, p`) — the image of
    the old statement shape `□(∃ loving pair)`, now a theorem by unfolding. -/
theorem T14_square : Necessity
    (∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ Loves s₁ s₂) := by
  intro _w
  obtain ⟨p, q, hp, hq, hne, hl, _, _⟩ := T14_eternalRelation
  exact ⟨p, q, hp, hq, hne, hl⟩

/-- The eternal relation's *content*: there is a pair of loving persons (from
    T14_eternalRelation, past the stability half). -/
theorem T14_content : ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ Loves s₁ s₂ := by
  obtain ⟨p, q, hp, hq, hne, hl, _, _⟩ := T14_eternalRelation
  exact ⟨p, q, hp, hq, hne, hl⟩

end Logos.Love

-- Axiom footprint audit
#print axioms Logos.Love.T13_someoneLovable
#print axioms Logos.Love.T14_eternalRelation
#print axioms Logos.Love.T14_world
#print axioms Logos.Love.T14_square
#print axioms Logos.Love.T14_content