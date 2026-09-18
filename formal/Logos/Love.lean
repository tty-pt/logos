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
import Logos.Modal

namespace Logos.Love

open Logos.Agency (Subject)
open Logos.Person (Person)
open Logos.Plurality (EntityOf NecessarySubject)
open Logos.Value (Affects AxPersonsAffect Helps Harms help_not_harm help_affects)
open Logos.Semantics (World)
open Logos.Truthmaker (ExistsAt Entity)
open Logos.Modal (NecessaryEntity)
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

/--There are two distinct persons, both lovable.

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

/--No person is contingent: nobody who is a person fails to persist in every world.

  Step-6 verdict, concrete form: `¬ NecessarySubject s` is refuted for every
    subject, so the countermodel `Person s ∧ ¬ NecessarySubject s` cannot
    exist. The necessity of persons is *definitional* (`ExistsAt` for
    subject-correlates is agency itself, esse est agere) — it is not a
    stronger metaphysical bridge, and no concrete model can attack it.
    Abstractly the implication is still not a logical law
    (`HostileSemantics.not_entails_person_necessary`). Footprint:
    `{Means, Subject}` (VOCAB only — `Person` unfolds through `Means`). -/
theorem no_contingent_person : ¬ (∃ s : Subject, Person s ∧ ¬ NecessarySubject s) := by
  rintro ⟨s, hs, hnc⟩
  exact hnc (AxPersonStability s hs)

/--There exists a necessary person: someone who is a person and persists in every world.

  C77 (re-anchored, 2026-09-18): from the performative act-datum
     (`h : ∃ s p, Act s p`, C68) a person exists (`T5_personExists`, C24) and
     it is necessary by definition (`AxPersonStability`, esse est agere). The
     old closed form ran through plurality (`T5_personExists_from_plurality`,
     footprint `{AxTwoSubjects, Means, Subject}`); the hypothesis-carrying
  form drops `AxTwoSubjects`. The necessity here is *definitional*
  (`ExistsAt (Subject) := ExistsAt (Entity.ofSubject _) := True`), not a
  bridge — and, like C24 itself, it needs only the actualized
  meaning-subject (`∃ p, Means s p`), not the substantive reading of
  "person". A VOCAB-only kernel footprint does NOT certify semantic
  neutrality of the definitions: this is an ontology-internal constitutive
  necessity, not an ontology-independent metaphysical one.
  Footprint: `{Means, Subject}` (VOCAB only). -/
theorem necessaryPersonExists (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Act s p) :
    ∃ s : Subject, Person s ∧ NecessarySubject s := by
  obtain ⟨s, hs⟩ := Logos.Plurality.T5_personExists h
  exact ⟨s, hs, AxPersonStability s hs⟩

/--There exists a necessary entity: the entity-correlate of the performing person exists in every world.

 E5 / C92 — from the demonstrated person (C24, `T5_personExists`) and its
    persistence (`AxPersonStability`, esse est agere) with the subject→entity
    lift (`Modal.subject_nec_entity_nec`, C91), some entity exists in every
  world. This does NOT close T7: it is the performing person's correlate,
     not a uniform ground of necessary truths (that stays
     `AxGlobalGround`-priced, C18). Like C77, it needs only the actualized
     meaning-subject; a VOCAB-only footprint does NOT certify semantic
     neutrality — this is constitutive necessity, not an ontology-independent
     metaphysical one.
     Footprint: `{Means, Subject}` (VOCAB only;
     no AxTwoSubjects, no SEM/META). -/
theorem necessary_entity_exists (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Act s p) :
    ∃ e : Entity, NecessaryEntity e := by
  obtain ⟨s, hs⟩ := Logos.Plurality.T5_personExists h
  exact ⟨EntityOf s, Logos.Modal.subject_nec_entity_nec s (AxPersonStability s hs)⟩

/--Two distinct persons stand in an eternal love-relation, and both persist in every world.

 T14 — the eternal love-relation: a pair of distinct persons who love each
    other, both of whose entity-correlates exist in *every* world — the poem's
    "Amar é escolhido e também é necessário (de alguma forma)". Built on the
    directed pair `Plurality.T12_directedPair` (C47): direction and stability
    live on the *same* pair. Footprint: `{AxTwoSubjects}`. -/
theorem T14_eternalRelation :
    ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧
      Loves s₁ s₂ ∧ NecessarySubject s₁ ∧ NecessarySubject s₂ := by
  obtain ⟨p, q, hp, hq, hne, ha⟩ := Logos.Plurality.T12_directedPair
  have hl : Loves p q := loves_of_helps ha
  exact ⟨p, q, hp, hq, hne, hl, AxPersonStability p hp, AxPersonStability q hq⟩

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
#print axioms Logos.Love.no_contingent_person
#print axioms Logos.Love.T13_someoneLovable
#print axioms Logos.Love.T14_eternalRelation
#print axioms Logos.Love.T14_world
#print axioms Logos.Love.T14_square
#print axioms Logos.Love.T14_content
#print axioms Logos.Love.necessary_entity_exists
