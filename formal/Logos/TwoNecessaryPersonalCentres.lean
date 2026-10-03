/-
# Logos.TwoNecessaryPersonalCentres — the plurality bridge, carrying its own reason

Retires `Value.AxTwoSubjects` (2026-10-04, batch LOVE-3/S4). The bridge is not
gone: it is *re-stated as the author's reason* rather than as a bare re-statement
that plurality is required.

  Before: `(¬ N_T ∧ ¬ N_F) → ∃ s₁ s₂, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂`
          — "the reality of right-and-wrong demands a second person".

  After:  `∃ s₁ s₂, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧
                     NecessarySubjectKind s₁ ∧ NecessarySubjectKind s₂`
          — "a NECESSARY, FREE PERSONAL GROUND whose freedom to self-give is
             necessary cannot have that freedom depend on contingent subjects;
             so at least two NECESSARY, ETERNAL persons exist."

Three things changed, all of them narrowing or strengthening:

1. The right-and-wrong antecedent is **dropped**. The old bridge made plurality
   *depend on* `Core.rightWrongDistinction`, so a reader who rejected the
   right/wrong distinction lost plurality too. The argument is not about
   right-and-wrong; the price is paid for necessity, and necessity is what the
   poem's "também é necessário (de alguma forma)" asks for.
2. `NecessarySubjectKind` is **added** to both witnesses. This is strictly
   stronger: the old bridge yielded no necessity at all, and every downstream
   row that wanted a necessary person had to buy it separately (T14 rode on
   `PersonStabilityPrinciple` plus an exhibited kind-pair, both unproved).
3. The `Tag:` stays **META**. This is a substantive claim that at least two
   necessary persons exist — it is not a reading of the vocabulary, and
   re-tagging it VOCAB would be laundering (AGENTS.md).

`NecessarySubjectKind` rather than `NecessarySubject`: this module cannot import
`Logos.Plurality` without a cycle (`Plurality` → `Value` → this module), and
`NecessarySubjectKind` is the *primitive* the world-rigid reading is derived
from. The two statements are the same statement in the kernel —
`Plurality.kinds_are_the_modal_partition` (C411) proves
`NecessarySubjectKind s ↔ NecessarySubject s` — so nothing is lost by positing
the primitive. `Plurality.two_necessary_persons` derives the `NecessarySubject`
form with no further price.

Note what this bridge does NOT do: it does not say the two persons love one
another. `Loves` is a separate relation and remains conditional on the unproved
`PluralityLovePrinciple`; see `Love.T14_eternalRelation_love_only`.
-/

import Logos.Core
import Logos.Agency
import Logos.Person

namespace Logos.TwoNecessaryPersonalCentres

open Logos.Agency (Subject NecessarySubjectKind ContingentSubjectKind)
open Logos.Person (Person)

/--Tag: META
AxTwoNecessaryPersonalCentres — the author's necessity argument for plurality,
  as one bridge. Replaces `Value.AxTwoSubjects` (retired 2026-10-04).

  STATEMENT: at least two NECESSARY, ETERNAL persons exist — distinct, both
  persons, both of the necessary kind.

  THE JUSTIFICATION (the author's reductio, in the form the kernel carries):
  the ground of reality is a NECESSARY, FREE PERSONAL GROUND
  (`NecessityEternity.ofGround_necessary_ground_of_reality`, C161;
  `DivineImmutability.ofGround_stage_invariance`, C199), and the freedom to
  self-give is NECESSARY for it — `SelfDonation` mentions no `World`, so it is
  world-invariant by construction and its necessity follows at zero price. Now
  suppose the distinct other required by that self-giving were contingent. Then
  the necessary ground's freedom would depend on contingent subjects, and a
  freedom that depends on the contingent is itself contingent. So the ground
  would be contingent. That is absurd, and the God of the poem is not absurd.
  Hence the other is not contingent: at least two necessary persons.

  This is why the bridge is narrower AND stronger than what it replaces. It is
  narrower because it no longer makes plurality depend on `Core.rightWrongDistinction`
  (reject the right/wrong distinction and the old bridge was lost; reject it now
  and plurality survives). It is stronger because the old bridge yielded no
  necessity whatsoever, so every necessary-person row had to buy necessity
  separately. Here necessity is what is bought, once, explicitly.

  CONSISTENCY-MODEL NOTE: the bridge is NOT forced by any earlier premise, and
  the corpus machine-checks that it is not. `HostileSemantics.not_entails_plurality`
  (`¬∀ I, (Γ_act I ∧ ∃ s, I.Person s) → TwoPersons I`) and
  `UnitPluralityCountermodel.agency_does_not_imply_plurality` exhibit a world
  with ONE person and a live right/wrong distinction that satisfies every other
  premise in the corpus. `Subject` is `axiom Subject : Type` (`Agency.lean:49`)
  with no constructors, so every existential over `Subject` needs an axiom that
  introduces an inhabitant; there is no signature in which plurality is
  derivable. The countermodel is a *signature* model and is not a candidate
  state (C559) — it witnesses underivability, not a possible world.

  SCOPE NOTE: it does NOT identify any subject with the ground-constructor.
  `FoundationalUnicity.ofGround_ne_ofSubject` still holds: `ofGround ≠ EntityOf s`
  for every `s`. Nor does it say the Creator inhabits the world, nor make any
  third subject necessary — kind-membership is per-subject, and the bridge says
  nothing about a third. The three-person reading
  (`one_necessary_ground_three_free_necessary_persons`) therefore keeps its own
  price and is NOT discharged here.

  PHILOSOPHICAL COST: a substantive interpersonal metaphysics, priced. Two
  distinct necessary persons are posited, not deduced. Reject this bridge and go:
  T12, T13, `notAlone`, `aloneExcluded`, `cogito_from_T12`,
  `T12_directedPair_conditional`, `AsieticChoice.trueChoice_exists`,
  `freeWill_exists`, and every personal-plurality row on the reading path. What
  survives the rejection is the free half: `Core.rightWrongDistinction`, the
  free necessity of self-giving (`SinglePersonDenial.donation_terminus_is_as_necessary_as_the_donor`),
  and the free absurdity C579
  (`SinglePersonDenial.self_gift_cannot_depend_on_a_contingent_person`,
  `donation_makes_contingency_is_refuted`), which never touched plurality.

  Note on the freedom half (batch LOVE-4 / C587): the existence of a Free Person
  is now derived independently without META axioms from the act datum and polarity
  (`NoMeanerNoFalsity.a_genuine_free_person_exists`, C587). This bridge specifically
  supplies personal distinctness (`s₁ ≠ s₂`) and modal necessity (`NecessarySubjectKind`),
  encapsulating the author's necessity argument for plurality.
-/
axiom AxTwoNecessaryPersonalCentres :
    ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧
      NecessarySubjectKind s₁ ∧ NecessarySubjectKind s₂

/-- Two distinct necessary persons exist, stated over the necessary KIND (the
    primitive). This is the author's target sentence with the kind spelled out;
    `Plurality.two_necessary_persons` is the same sentence over world-rigidity,
    derived at no further price by C411.
    Footprint: `{AxTwoNecessaryPersonalCentres, Means, NecessarySubjectKind, Subject, Will, subjectWill}`. -/
theorem two_necessary_persons_of_kind :
    ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧
      NecessarySubjectKind s₁ ∧ NecessarySubjectKind s₂ :=
  AxTwoNecessaryPersonalCentres

/-- At least two distinct persons — the bare plurality of T12, with the
    necessity dropped. This is the replacement for `Value.AxTwoSubjects` at every
    consumer that only ever wanted two people (`aloneExcluded`, T12, T13,
    `cogito_from_T12`, the free-will rows). Necessity is a *conjunct the bridge
    now supplies*, not a premise each consumer has to re-buy.
    Footprint: `{AxTwoNecessaryPersonalCentres, Means, NecessarySubjectKind, Subject, Will, subjectWill}`. -/
theorem two_persons :
    ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ := by
  obtain ⟨s₁, s₂, h₁, h₂, hne, _, _⟩ := AxTwoNecessaryPersonalCentres
  exact ⟨s₁, s₂, h₁, h₂, hne⟩

/-- The necessary kind is inhabited by TWO persons, not merely one: the
    strengthening over `Plurality.necessaryPersonalSubjectExists`, which yields a
    single witness. Both bridges stay declared and are independent; this one is
    not derived from that one and does not subsume it.
    Footprint: `{AxTwoNecessaryPersonalCentres, Means, NecessarySubjectKind, Subject, Will, subjectWill}`. -/
theorem necessary_kind_is_inhabited_by_two :
    ∃ s₁ s₂ : Subject, NecessarySubjectKind s₁ ∧ NecessarySubjectKind s₂ ∧ s₁ ≠ s₂ := by
  obtain ⟨s₁, s₂, _, _, hne, hk₁, hk₂⟩ := AxTwoNecessaryPersonalCentres
  exact ⟨s₁, s₂, hk₁, hk₂, hne⟩

end Logos.TwoNecessaryPersonalCentres

-- Axiom footprint audit
#print axioms Logos.TwoNecessaryPersonalCentres.AxTwoNecessaryPersonalCentres
#print axioms Logos.TwoNecessaryPersonalCentres.two_necessary_persons_of_kind
#print axioms Logos.TwoNecessaryPersonalCentres.two_persons
#print axioms Logos.TwoNecessaryPersonalCentres.necessary_kind_is_inhabited_by_two
