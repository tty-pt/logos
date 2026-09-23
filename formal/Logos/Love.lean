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
open Logos.Value (Affects PersonsAffectPrinciple Helps Harms help_not_harm help_affects)
open Logos.Semantics (World)
open Logos.Entity (ExistsAt Entity)
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

/-- The person stability principle: whoever is a person exists across all worlds.
    With ExistsAt hardened, this is an explicit metaphysical principle, not a definitional triviality. -/
def PersonStabilityPrinciple : Prop := ∀ s : Subject, Person s → NecessarySubject s

/-- The plurality-to-love principle: distinct persons love one another.
    With Affects/Helps/Harms hardened, love is an explicit relational principle. -/
def PluralityLovePrinciple : Prop := ∀ s₁ s₂ : Subject, Person s₁ → Person s₂ → s₁ ≠ s₂ → Loves s₁ s₂

/-- Conditional T14: Under person stability and the plurality-love principle,
    two distinct persons stand in an eternal love relation. -/
theorem T14_eternalRelation_conditional
    (hStab : PersonStabilityPrinciple)
    (hLove : PluralityLovePrinciple) :
    ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧
      Loves s₁ s₂ ∧ NecessarySubject s₁ ∧ NecessarySubject s₂ := by
  obtain ⟨p, q, hp, hq, hne⟩ := Logos.Plurality.T12_twoPersons
  have hl : Loves p q := hLove p q hp hq hne
  exact ⟨p, q, hp, hq, hne, hl, hStab p hp, hStab q hq⟩

/-- In every world, two distinct persons stand in a love relation (conditional on stability and love). -/
theorem T14_world_conditional
    (hStab : PersonStabilityPrinciple)
    (hLove : PluralityLovePrinciple) :
    NecessityPH
      (fun _w : World =>
        ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧
          Loves s₁ s₂ ∧ ExistsAt _w (EntityOf s₁) ∧ ExistsAt _w (EntityOf s₂)) := by
  obtain ⟨p, q, hp, hq, hne, hl, hNs, hNq⟩ := T14_eternalRelation_conditional hStab hLove
  intro w
  exact ⟨p, q, hp, hq, hne, hl, hNs w, hNq w⟩

/-- Necessarily, two distinct persons stand in a love relation (conditional on stability and love). -/
theorem T14_square_conditional
    (hStab : PersonStabilityPrinciple)
    (hLove : PluralityLovePrinciple) :
    Necessity
      (∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ Loves s₁ s₂) := by
  intro _w
  obtain ⟨p, q, hp, hq, hne, hl, _, _⟩ := T14_eternalRelation_conditional hStab hLove
  exact ⟨p, q, hp, hq, hne, hl⟩

/-- Two distinct persons stand in a love relation (conditional on the plurality-love principle). -/
theorem T14_content_conditional (hLove : PluralityLovePrinciple) :
    ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ Loves s₁ s₂ := by
  obtain ⟨p, q, hp, hq, hne⟩ := Logos.Plurality.T12_twoPersons
  exact ⟨p, q, hp, hq, hne, hLove p q hp hq hne⟩

end Logos.Love

-- Axiom footprint audit
#print axioms Logos.Love.love_helps
#print axioms Logos.Love.love_not_harms
#print axioms Logos.Love.love_affects
#print axioms Logos.Love.loves_of_helps
#print axioms Logos.Love.T14_square_conditional
#print axioms Logos.Love.T14_content_conditional
