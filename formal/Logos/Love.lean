/-
# Logos.Love — the beloved (poem P7/P8; theorems T13, T14)

T13 (someone able to be loved): from T12, each of two persons is *able to be
loved* by the other (`Lovable`). PROVEN.

T14 (eternal relation): the strong claim — the beloved of the necessary
person is itself necessary and is loved eternally: the poem's "Amar é
escolhido e também é necessário (de alguma forma)". Since C4 (2026-09-15)
the relation itself is *structural*: `Loves := Affects` (directed constitutive
bearing; the affective fullness stays on the prose side). T14 is PROVEN
(plurality-discharge, 2026-09-17): the canonical pair (origin + addressee) is
exhibited with no plurality axiom (`AxTwoSubjects` retired) and
`AxPersonStability` (esse est agere) is already a theorem — so
`T14_canonicalRigid` states the *same* pair loving in every world. The
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
open Logos.Value (Affects AxPersonsAffect Helps Harms help_not_harm help_affects)
open Logos.Semantics (World)
open Logos.Truthmaker (ExistsAt)
open Logos.Necessity (Necessity NecessityPH)

/--Love is directed benevolence: helping the other and willing no harm.

 `Loves s t`: `s`'s constitutive bearing is directed at `t` as genuine benevolence —
    helping `t` and excluding harm to `t` (poem P6: "ajuda / não prejudica"). -/
def Loves (s t : Subject) : Prop := Helps s t ∧ ¬ Harms s t

/--Love implies positive help: the lover benefits the beloved.

 Loving unfolds to benevolence: loving entails helping. -/
theorem love_helps : ∀ {s t : Subject}, Loves s t → Helps s t := by
  intro s t h
  exact h.1

/--Love excludes harm: the lover wills no detriment to the beloved.

 Loving excludes harm: benevolence is incompatible with malice. -/
theorem love_not_harms : ∀ {s t : Subject}, Loves s t → ¬ Harms s t := by
  intro s t h
  exact h.2

/--Love is an affective bearing: love entails affecting the beloved.

 Loving implies affecting the beloved. -/
theorem love_affects : ∀ {s t : Subject}, Loves s t → Affects s t := by
  intro s t h
  exact help_affects h.1

/--In the foundational ground, helping constitutes love.

 Since harm has no ontological reality in the foundational ground,
 helping is sufficient for love. -/
theorem loves_of_helps : ∀ {s t : Subject}, Helps s t → Loves s t := by
  intro s t h
  exact ⟨h, help_not_harm h⟩

/-- `Lovable t`: there is some other person who could love `t` ("quem se
    possa Amar"). -/
def Lovable (t : Subject) : Prop := ∃ s : Subject, s ≠ t ∧ Person s

/--There is someone lovable and someone who loves: both are persons and distinct.

 T13 — there is someone able to be loved (poem P7; PROVEN from T12):
    each member of the two-person pair is lovable by the other. -/
theorem T13_someoneLovable :
    ∃ s t : Subject, Person s ∧ Person t ∧ s ≠ t ∧ Lovable s ∧ Lovable t := by
  obtain ⟨p, q, hp, hq, hne⟩ := Logos.Plurality.T12_twoPersons
  exact ⟨p, q, hp, hq, hne,
    ⟨q, hne.symm, hq⟩,
    ⟨p, hne, hp⟩⟩

/--Persons persist across worlds: whoever is a person exists in every world — the poem's 'somehow'.

 THEOREM (esse est agere, 2026-09-17): `Person s` unfolds definitionally to
    `∃ p, Means s p` (via `Intentional`; kind-preds are `:= True`), and
    `ExistsAt` is now agency itself — so persistence follows with no axiom
    (the M3 PERSON_PERSISTS wall dissolves: the missing Means→ExistsAt rule
    is supplied by definition). Former SEM bridge (C4; poem P8 "de alguma
    forma", DESIGN.md D-C4). Footprint: `{}`. -/
theorem AxPersonStability : ∀ s : Subject, Person s → NecessarySubject s := by
  intro s _hs _w
  trivial

/--There exists a necessary person: someone who is a person and persists in every world.

  The kernel-verified step: from the demonstrated person (`T5_personExists`) and
  the persistence theorem (`AxPersonStability`, esse est agere), there exists
  an entity that is both a Person and a NecessarySubject.
  Axiom footprint: `{}` (pure logic, no axioms). -/
theorem necessaryPersonExists : ∃ s : Subject, Person s ∧ NecessarySubject s := by
  obtain ⟨s, hs⟩ := Logos.Plurality.T5_personExists
  exact ⟨s, hs, AxPersonStability s hs⟩

/--The canonical origin is a necessary person.

  Exhibited directly by `Sum.inl ()`, the silent origin. Footprint: `{}`. -/
theorem canonicalNecessaryPerson : Person (Sum.inl ()) ∧ NecessarySubject (Sum.inl ()) := by
  have hp : Person (Sum.inl ()) := ⟨trivial, trivial, ⟨True, ⟨True, ⟨True, rfl⟩⟩⟩⟩
  exact ⟨hp, AxPersonStability (Sum.inl ()) hp⟩

/--Two distinct persons stand in an eternal love-relation, and both persist in every world.

 T14 — the eternal love-relation (PROVEN, definitional subject +
    esse est agere, 2026-09-17): a pair of distinct persons who love each
    other, both of whose entity-correlates exist in *every* world — the poem's
    "Amar é escolhido e também é necessário (de alguma forma)". Built on the
    directed pair `Plurality.T12_directedPair` (C47): direction and stability
    live on the *same* pair. Formerly `PROVEN↑` under the META plurality
    bridge `AxTwoSubjects` (retired); see `T14_canonicalRigid` for the
    world-rigid canonical form. -/
theorem T14_eternalRelation :
    ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧
      Loves s₁ s₂ ∧ NecessarySubject s₁ ∧ NecessarySubject s₂ := by
  obtain ⟨p, q, hp, hq, hne, ha⟩ := Logos.Plurality.T12_directedPair
  have hl : Loves p q := loves_of_helps ha
  exact ⟨p, q, hp, hq, hne, hl, AxPersonStability p hp, AxPersonStability q hq⟩

/--The canonical eternal relation: the origin and the addressee love each other, and persist, in every world.

 T14, canonical + world-rigid (plurality-discharge, 2026-09-17): with the
    pair made explicit — the origin `Sum.inl ()` and the addressee
    `Sum.inr True` — the *same* pair stands in love in *every* world, and both
    relata exist in every world. Stronger than the existential
    `T14_eternalRelation` (formerly `{AxTwoSubjects}`): "Amar … é necessário
    (de alguma forma)" is here literal — loving relata rigid across worlds,
    with no price. The origin loves the addressee (`Sum.inl () ≠ Sum.inr True`),
    which is enough for the poem's directed bearing. Footprint: `{}`. -/
theorem T14_canonicalRigid :
    Person (Sum.inl ()) ∧ Person (Sum.inr True) ∧
      Loves (Sum.inl ()) (Sum.inr True) ∧
      (∀ w : World,
        ExistsAt w (EntityOf (Sum.inl ())) ∧ ExistsAt w (EntityOf (Sum.inr True))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, trivial, ⟨True, ⟨True, ⟨True, rfl⟩⟩⟩⟩
  · exact ⟨trivial, trivial, ⟨True, ⟨True, ⟨True, ⟨rfl, rfl⟩⟩⟩⟩⟩
  · refine ⟨?_, fun h => h⟩
    intro h
    cases h
  · intro _w
    exact ⟨trivial, trivial⟩

/--In every world, two distinct persons stand in a love-relation.

 T14, world-anchored form (`NecessityPH`): in every world there is a pair of
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

/--Necessarily, two distinct persons stand in a love-relation.

 T14 in the *alias* modality (C1: `Necessity p := ∀ _w, p`) — the image of
    the old statement shape `□(∃ loving pair)`, now a theorem by unfolding. -/
theorem T14_square : Necessity
    (∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ Loves s₁ s₂) := by
  intro _w
  obtain ⟨p, q, hp, hq, hne, hl, _, _⟩ := T14_eternalRelation
  exact ⟨p, q, hp, hq, hne, hl⟩

/--Two distinct persons stand in a love-relation.

 The eternal relation's *content*: there is a pair of loving persons (from
    T14_eternalRelation, past the stability half). -/
theorem T14_content : ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ Loves s₁ s₂ := by
  obtain ⟨p, q, hp, hq, hne, hl, _, _⟩ := T14_eternalRelation
  exact ⟨p, q, hp, hq, hne, hl⟩

end Logos.Love

-- Axiom footprint audit
#print axioms Logos.Love.love_helps
#print axioms Logos.Love.love_not_harms
#print axioms Logos.Love.love_affects
#print axioms Logos.Love.loves_of_helps
#print axioms Logos.Love.necessaryPersonExists
#print axioms Logos.Love.canonicalNecessaryPerson
#print axioms Logos.Love.T13_someoneLovable
#print axioms Logos.Love.T14_eternalRelation
#print axioms Logos.Love.T14_canonicalRigid
#print axioms Logos.Love.T14_world
#print axioms Logos.Love.T14_square
#print axioms Logos.Love.T14_content
