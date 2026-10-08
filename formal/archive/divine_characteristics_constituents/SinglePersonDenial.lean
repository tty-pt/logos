/-
# Logos.SinglePersonDenial — the chain's hinge is dependence, and it is free

`LOVE.md` mounted the refutation of the author's objection on the wrong derivations
(`LOVE-2.md` D4): C576's `axiom → ¬¬axiom` read as a contradiction, a premise granted as an
answer (R21), and a fresh-signature countermodel that denied nothing in Γ (R20). It also
removed `AsietyFreedomOfGround`'s role from the doctrine of the ground's freedom — commit
`4a59173`, "try to improve personhood clarity" — by asserting that there is *no* relation
between the ground's scope and any subject's freedom. That assertion is false, and this module
is built on the reading that commit deleted.

## The objection, as a chain

`LOVE.md` §1 records it:

> "Se existe uma essência pessoal necessária e essa base é Livre e Imutável. Poderia não ser
> livre de se doar (em alguma altura)? Isto é: Se houvesse uma essência pessoal necessária que
> fosse uma só pessoa, só se poderia doar a seres contingentes (temporais). Isso não a faria
> também contingente?"

Reconstructed as the four steps it actually is:

1. **Single Person** — the essence is one person, so there is no other person to give to;
2. ⟹ it can only give to **contingent (temporal)** beings;
3. ⟹ its self-giving is **dependent on the contingent beings**;
4. ⟹ it is therefore contingent — against a Ground already determined **Eternal, Necessary,
   Free and Immutable**.

**Step 3 is the hinge, and it is where the argument dies.** Step 1 is impossible in Γ
(`no_person_is_the_ground`, C519, `{Subject}` — the same fact as `ofGround_ne_ofSubject`), and
step 2 is false because the donation is *intra-nature*: `SelfDonation f o` puts both relata at
`divineReality := Entity.ofGround`. Step 3 is what needs the refutation, because it is the step
that turns the gift into something the ground does not control, and step 4 is what needs the
character of that gift.

## What is free here, and what is not

| step | row | price |
|---|---|---|
| 1 | `single_person_denial_is_refuted` (C519's `≠`) | free |
| 2 | `not_a_single_person`, `self_gift_cannot_depend_on_a_contingent_person` | free |
| 3 | `donation_terminus_is_as_necessary_as_the_donor` | free |
| 4 | `donation_makes_contingency_is_refuted` | free |
| — | `agape_is_self_donation` (C575) — a donation exists | **1 META** |
| — | `FreeSubject` via `TrinitarianPersonalBridge` — the Persons are free | **1 META** |
| — | `Plurality.notAlone` (T12) — the Persons are distinct | **1 META** |

**Every step of the objection is refuted at zero substantive axioms, and the existence of the
donation is deliberately not used to refute it.** A row that refutes the objection by way of the
datum it also prices is not a refutation; it is the datum. These rows hold for *any*
`SelfDonation`, including one the corpus never witnesses.

## The terminology, which is load-bearing

| statement | symbol | status |
|---|---|---|
| the ground's essence is **personal** | `PersonalGround Entity.ofGround` (C362) | free |
| the ground is **OneEssence** for **every** Person | `indwells` (C140) | free |
| the ground's **freedom is shared** with those it grounds | `AsietyFreedomOfGround` (◈ `def`) | free as a `def` |
| the ground is **no Person among the three** | `no_person_is_the_ground` (C519) | free |
| a gift's **terminus is as necessary as the donor** | `donation_terminus_is_as_necessary_as_the_donor` | free |
| there is **more than one** Person | `Plurality.notAlone` (T12) | **1 META** |

"The ground is not a person" is the **fourth** row and only the fourth: `Person` and `Asiety` are
`Subject`-indexed, so `Entity.ofGround` lies outside their reach (`AsieticChoice.lean:147-148`,
discharged by `ofGround_ne_ofSubject`). It does **not** say the ground lacks personhood — the
second and third rows say the opposite, and the third is exactly the content commit `4a59173`
deleted. The ground is a personal OneEssence whose freedom is shared with the Persons in which
it is OneEssence; the ground is the nature, not an instance of it. Reading row 4 as a negation
of rows 2–3 is the error `LOVE-2.md` D1 records.

## What this module does not do

- It does **not** say the ground cannot love contingent beings. `AxGroundLovesContingentRealm`
  (C339, `LovesAsGround.lean`) is untouched: the ground's benevolence toward the contingent realm
  stands exactly as declared. The claim refuted was never that.
- It does **not** use `AxAgapeEssence`, `AxTwoSubjects`, `AxBoundedMeaningRequiresFreeSubject` or
  any other declared axiom. Each is cited at its own price and none is absorbed here.
- It does **not** identify a `Subject` with a `DivineHypostasis`. That correspondence is open and
  is recorded as C580 BLOCKED.
- It does **not** assert the ground's freedom as a `Free` predicate on `Entity`. Γ's vocabulary
  reaches the ground's freedom through `AsietyFreedomOfGround` (`AsietyFreedom.lean:141`) and
  `AsietyFreeWill`, registered ◈ in `Stipulations.lean` precisely because a `def` premise is
  invisible to `#print axioms`.
-/

import Logos.Core
import Logos.Semantics
import Logos.Entity
import Logos.Modal
import Logos.Agency
import Logos.Person
import Logos.Plurality
import Logos.RecoveredOntologicalGround
import Logos.NecessityEternity
import Logos.DivineAgape
import Logos.TrinitarianPersonalGround

namespace Logos.SinglePersonDenial

open Logos.Core
open Logos.Semantics (World)
open Logos.Entity (Entity EntityOf)
open Logos.Modal (NecessaryEntity)
open Logos.Agency (Subject NecessarySubjectKind ContingentSubjectKind)
open Logos.Person (Person)
open Logos.Plurality (NecessarySubject notAlone T12_twoPersons)
open Logos.RecoveredOntologicalGround
  (OneEssence ActualEntity GroundOfReality NecessaryGroundOfReality)
open Logos.NecessityEternity (ofGround_necessary ofGround_necessary_ground_of_reality ofGround_ne_ofSubject)
open Logos.DivineAgape (DivineHypostasis Subsists divineReality SelfDonation agape_is_self_donation)
open Logos.TrinitarianPersonalGround
  (PersonalGround Perichoretic ofGround_grounds_every_person no_person_is_the_ground
    ofGround_is_perichoretic the_ground_is_not_void_of_personhood)

/-- **The ground is a personal necessary essence, indwelt by every Person, and it is itself no
    Person.** The positive half of the refutation: the author's chain needs a personal necessary
    essence whose Persons are a *single* one, and the ground supplies the first conjunct and
    refuses the second.

    Read the conjunction in the order the tradition reads it. `necessary` is C161; `personal` is
    C362, whose two fields are `sustains` (presence-grounding) and `indwells` (`OneEssence`);
    `indwelt` is C140 and holds for **every** person, so it is not a claim about how many there
    are; `noPerson` is C519. **The ground is not absent personhood — it is personhood not
    reducible to one instance.**

    The conjunct that is *not* here is the population of Persons and its distinctness:
    `ofGround_is_perichoretic` instantiates `indwells` three times, but `Perichoretic`
    (`TrinitarianPersonalGround.lean:319`) is a plain conjunction of `OneEssence` and carries no
    `a ≠ b`. Three *distinct* Persons cost `AxTwoNecessaryPersonalCentres` (1 META, `Plurality.notAlone` /
    `T12_twoPersons`) and sit on their own row. A reader who wants "it cannot be only one" pays
    for it; a reader who wants "the ground is no single person" does not. Note on freedom (LOVE-4 / C587):
    a Free Person is derived at 0 META (`NoMeanerNoFalsity.a_genuine_free_person_exists`).

    Footprint: `{Means, NecessarySubjectKind, Subject, Will, subjectWill}`. -/
theorem single_necessary_personal_essence_three_persons :
    NecessaryGroundOfReality Entity.ofGround ∧
    PersonalGround Entity.ofGround ∧
    (∀ s : Subject, Person s → OneEssence Entity.ofGround (EntityOf s)) ∧
    (∀ s : Subject, ¬ (Entity.ofGround = EntityOf s)) :=
  ⟨ofGround_necessary_ground_of_reality,
    the_ground_is_not_void_of_personhood,
    fun s hP => ofGround_grounds_every_person s hP,
    fun s => no_person_is_the_ground s⟩

/-- **The author's first step is impossible, and this is the reductio he did not have to run.**
    Assume his premise directly — the essence *is* one single Person, i.e. some `Subject`'s entity
    is the ground — and `False` follows at zero substantive axioms: `no_person_is_the_ground`
    (C519) is `{Subject}` and is the same fact as `ofGround_ne_ofSubject`. The hypothesis is a
    **real premise** and `False` is the conclusion, so this is a reductio and not a denial.

    Read it with the terminology held apart, because this row is where the confusion in `LOVE.md`
    §3 came from. `False` here says the essence is **no Person**; it says nothing against the
    essence being **personal**, which C362 asserts and this module's first theorem repeats. The
    ground is the personal OneEssence; the Persons are its instances; the essence is not one of
    them. Commit `4a59173` read this row as denying the ground's personhood and rebuilt the
    doctrine around that reading; the row does not say it.

    Footprint: `{Subject}`. -/
theorem single_person_denial_is_refuted (hSingle : ∃ s : Subject, Entity.ofGround = EntityOf s) :
    False := by
  obtain ⟨s, hs⟩ := hSingle
  exact no_person_is_the_ground s hs

/-- **The author's premise is not Γ's doctrine.** The same content as the row above in closed
    form, for the reader who wants a proposition rather than a reductio: a necessary reality-essence
    which *is* one single person is refuted. Free, by C519 alone.

    Footprint: `{Subject}`. -/
theorem not_a_single_person :
    ¬ (NecessaryGroundOfReality Entity.ofGround ∧ (∃ s : Subject, Entity.ofGround = EntityOf s)) := by
  rintro ⟨_hN, hS⟩
  exact single_person_denial_is_refuted hS

/-- **Step 3 — the dependence — is refuted (C579, PROVEN, free).** This is the row the objection
    dies on. The claim was: *a Single Person can only give to contingent beings, so its self-giving
    is dependent on the contingent beings.* The hypothesis is that claim as a proposition — the
    donation's recipient is some `Subject`'s entity — and it is refutable at zero substantive
    axioms, because `SelfDonation` puts the recipient at `divineReality := Entity.ofGround` and
    `Entity.ofGround` is no `Subject`'s entity.

    The hypothesis is stated in the **stronger** form on purpose. The objection says
    *contingent (temporal)* beings, so the weakest statement of the dependency claim would
    restrict the recipient to a `ContingentSubjectKind s`. Γ refutes the stronger claim instead —
    that the recipient is a `Subject` **at all** — because `SelfDonation`'s recipient is at
    `divineReality` and `Entity.ofGround` is no `Subject`'s entity. The temporal qualification
    was therefore never the load-bearing part of the objection, and adding it back would only
    have made the refutation weaker.

    **No `AxAgapeEssence`.** The row holds for any `SelfDonation` whatsoever, which is what makes
    it a refutation rather than a restatement of the datum.

    Footprint: `{Subject}`. -/
theorem self_gift_cannot_depend_on_a_contingent_person
    (dependence : ∃ f o : DivineHypostasis, ∃ s : Subject,
      SelfDonation f o ∧ o.deiformEntity = EntityOf s) : False := by
  obtain ⟨_f, o, s, hSD, hEq⟩ := dependence
  obtain ⟨_hne, _hf, ho, _hlove, _hloc⟩ := hSD
  have ho' : o.deiformEntity = Entity.ofGround := ho.trans (by rfl)
  exact ofGround_ne_ofSubject s (ho'.symm.trans hEq)

/-- **Step 3, second face: the terminus is as necessary as the donor.** Free, and free in the
    strict sense: `Subsists` is a location-equality against `divineReality`, and the ground is a
    necessary entity (C145), so **both** relata of any donation are necessary. A gift whose
    recipient is necessary is not a gift the ground's eternity could depend on.

    This row is what "Free and Immutable" means here operationally: the ground's gift is not
    conditioned by anything outside its own nature, because its recipient *is* its own nature.

    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem donation_terminus_is_as_necessary_as_the_donor
    (f o : DivineHypostasis) (h : SelfDonation f o) :
    NecessaryEntity f.deiformEntity ∧ NecessaryEntity o.deiformEntity := by
  obtain ⟨_hne, hf, ho, _hlove, _hloc⟩ := h
  have hf' : f.deiformEntity = Entity.ofGround := hf.trans (by rfl)
  have ho' : o.deiformEntity = Entity.ofGround := ho.trans (by rfl)
  exact ⟨hf' ▸ ofGround_necessary, ho' ▸ ofGround_necessary⟩

/-- **Step 4 — the contingency conclusion — is refuted, free.** *It would therefore also be
    contingent.* The hypothesis is that conclusion as a proposition; discharging it yields `False`
    from C579's terminus row alone. No `AxAgapeEssence`.

    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem donation_makes_contingency_is_refuted
    (donation_makes_contingency :
      ∃ f o : DivineHypostasis, SelfDonation f o ∧ ¬ NecessaryEntity o.deiformEntity) :
    False := by
  obtain ⟨f, o, hSD, hnc⟩ := donation_makes_contingency
  exact hnc (donation_terminus_is_as_necessary_as_the_donor f o hSD).2

/-- **The module in one line.** The ground is a personal necessary essence indwelt by every Person
    and no Person itself; its gift cannot reach a contingent being, because every donation's
    terminus is the necessary ground; and the contingency conclusion therefore has no premise.
    Zero new axioms, and four separate prices cited rather than absorbed.

    Footprint: `{Means, NecessarySubjectKind, Subject, Will, subjectWill}`. -/
theorem singlePersonDenial_summary :
    NecessaryGroundOfReality Entity.ofGround ∧
    PersonalGround Entity.ofGround ∧
    (∀ s : Subject, ¬ (Entity.ofGround = EntityOf s)) ∧
    (¬ (NecessaryGroundOfReality Entity.ofGround ∧ (∃ s : Subject, Entity.ofGround = EntityOf s))) ∧
    (∀ f o : DivineHypostasis, SelfDonation f o →
      NecessaryEntity f.deiformEntity ∧ NecessaryEntity o.deiformEntity) :=
  ⟨ofGround_necessary_ground_of_reality,
    the_ground_is_not_void_of_personhood,
    fun s => no_person_is_the_ground s,
    not_a_single_person,
    donation_terminus_is_as_necessary_as_the_donor⟩

/-! ## Section 7: Axiom Footprint Audit -/

#print axioms single_necessary_personal_essence_three_persons
#print axioms single_person_denial_is_refuted
#print axioms not_a_single_person
#print axioms self_gift_cannot_depend_on_a_contingent_person
#print axioms donation_terminus_is_as_necessary_as_the_donor
#print axioms donation_makes_contingency_is_refuted
#print axioms singlePersonDenial_summary

end Logos.SinglePersonDenial
