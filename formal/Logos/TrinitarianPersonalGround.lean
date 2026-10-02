/-
# Logos.TrinitarianPersonalGround — the ground is not void of personhood

The record of record is `AGENTS.md` (sync rule) with `GAPMAP.md` (per-claim status); this module was step **S2** of the retired personal-ground plan,
promoting the machine-checked basis of `investigations/trinitarian-probe.lean` (an
audit artifact, never compiled by `lake build`) into the kernel. Nothing here moves the match arm
of `EntityMeans` — that is the point, and Section 2 below records why the arm must not be moved.

## The doctrine

> **God is one essence in three persons, and the essence is alive.** The one essence is not a
> fourth instance of choosing alongside the three; it is the one essence *which the three subsist
> in and which lives by them*. Its freedom is theirs, **shared rather than duplicated**
> (*praeter hoc, quod unus est, tres sunt*, the Nicene formula's own guard against a fourth).

Two facts carry that sentence, and neither may be collapsed into a deficiency or an excess:

1. **`¬ Asiety Entity.ofGround`** — no subject witnesses the ground, so the ground is not an
   asietic entity (`ground_is_not_a_fourth_chooser`). The one essence is not a fourth chooser.
2. **`ground_scope_does_contain_incompatibles`** — the ground's scope takes in **both horns of
   every conflict**, because its arm is `True`. **Plenitude of scope is not freedom.**

The second is the result the checker forced, and it is recorded here because the opposite reading
is the natural mistake. "The ground cannot co-mean incompatible contents" is **false** against
today's arm. Freedom in Γ is not bearing all content; it is `Asiety`, which requires being a
`Subject`. So a total scope does not make the ground maximally free — which would be absurd —
because freedom is subject-indexed.

## Two routes of grounding, both named, neither accidental

`OneEssence` is *meaning-containment*: `∀ p, EntityMeans e p → EntityMeans g p`. Because the
ground's arm is `True`, it holds of everything, **including the atoms vacuously** — an atom means
nothing, so the containment is `True` by empty antecedent rather than by intent. That reason is
now named instead of left to chance:

- **`GroundByBeing`** — presence-grounding: God as sustaining cause, *ST* I q. 44 a. 1 (God is
  the cause of the whole being of creatures). This is the route that covers the atoms for a
  reason nobody chose.
- **`OneEssence`** — providential indwelling, covering persons, and *not* covering a heretic's
  beliefs (`EntityMeans (ofAtom _) p := False`, while a heretic *does* mean heretically).

`ofGround_leaves_nothing_ungrounded` closes the disjunction: nothing is outside the ground.

## What this module does not claim

- **Not hypostatic identity.** `g = EntityOf s` for some `s` is unstatable: `Person` is a
  `Subject → Prop`, `Subject` is an opaque sort with no constructors, and `Entity.ofGround ≠
  EntityOf s` is `Entity.noConfusion`. The claim "the ground is a free subject in its own right"
  is not false here — it has no denotation. Any plan implying otherwise would be dishonest, and
  this plan says so in §1.4 and §11.
- **Not a non-vacuous `OneEssence`.** Adding `∃ s, e = EntityOf s` to `OneEssence` makes the God
  proof **unprovable**: `actualWorld` makes every atom actual, so `GroundOfReality Entity.ofGround`
  must handle `ofAtom n`, and the added conjunct is false for atoms while the meaning arm is
  `False` for them, so neither disjunct fires. Plan §6.2 records the three rejected variants.
- **Not an essence predicate.** Consubstantiality is grounded *in the ground* (`OneEssence`), and
  no `Essence` predicate is introduced. "The three persons share a nature independently of the
  ground" therefore remains unstatable — an author decision recorded here, and still open. A `Consubstantial`
  `def` was carried here for §20.1 and has been **deleted**: at the ground it is `True` of atoms
  (see the `DOCTRINE ROW 3` docstring below). The one-ness it named is `indwells`, which is free.
- **Not a change to `EntityMeans`.** §6.1's rejected alternative (`EntityMeans Entity.ofGround p :=
  T p`) trades infallibility for pure actuality, because `PassiveIntentionalPotency e := ∃ p, ¬
  EntityMeans e p` and `MaximalCapacity e := ∀ p, EntityMeans e p` are **the same field read in two
  directions**. The fix is to re-specify `PassiveIntentionalPotency`, which is filed as its own
  milestone and is **not** part of this plan.

## Price

Every declaration here is a `def`, a `structure`, or a theorem at **zero substantive axioms**. The
non-empty footprints are Γ's vocabulary (`Subject`, `Means`, `Will`, `subjectWill`,
`NecessarySubjectKind`) — the cost of *saying* the claim in Γ's own words, not a price for the
claim. This is the distinction the corpus already draws: "zero *substantive* rather than
axiom-free". No axiom is declared, removed, or re-tagged by this module, and the declared-axiom
count is unchanged at 25 (VOCAB 14 / SEM 7 / META 4).
-/

import Logos.Core
import Logos.Entity
import Logos.Semantics
import Logos.Agency
import Logos.Alternatives
import Logos.Choice
import Logos.Person
import Logos.RecoveredOntologicalGround
import Logos.NecessityEternity
import Logos.AsieticChoice

namespace Logos.TrinitarianPersonalGround

open Logos.Semantics (World)
open Logos.Entity (Entity EntityOf ExistsAt)
open Logos.Agency (Subject Means)
open Logos.Alternatives (Incompatible)
open Logos.Choice (FreeWill)
open Logos.Person (Person)
open Logos.RecoveredOntologicalGround (ActualEntity EntityMeans OneEssence)
open Logos.NecessityEternity (ofGround_ne_ofSubject)
open Logos.AsieticChoice (Asiety)

/-! ## Section 1: presence-grounding, the route that covers the atoms -/

/-- **`GroundByBeing g e`: presence-grounding — `g` is present wherever `e` is.** The second
    grounding route, and the non-vacuous one: `OneEssence` holds of everything by the ground's
    `True` match arm, so of the atoms too, and there for a reason nobody chose. This relation is
    what grounds them *for a reason*, i.e. God as sustaining cause (*ST* I q. 44 a. 1: God is the
    cause of the whole being of creatures), while `OneEssence` is providential indwelling.

    It is deliberately weak — presence, not production. Γ has no causal relation, so "the ground
    sustains" is read as "the ground is there", exactly as `Stipulations.operatesAt_presencePlusObtaining`
    reads omnipotence; the production sense is not claimed and is not derivable here.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
def GroundByBeing (g e : Entity) : Prop :=
  ∀ w : World, ExistsAt w e → ExistsAt w g

/-- **The ground sustains the being of every entity.** `EntityExistsAt _ Entity.ofGround := True`
    is what makes this free, so the sustaining cause of all creatures is **axiom-free** — the whole
    price of presence-grounding is the `True` arm of the world's ground-clause, which is
    `Stipulations.ofGround_meansAll`'s sibling and costs nothing as a `def`.

    This is the row that covers the **atoms** for a reason nobody chose, and the
    reason `ofGround_ground_of_reality` needed a `GroundByBeing`-shaped alternative at all.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem ofGround_grounds_every_being_by_presence (e : Entity) :
    GroundByBeing Entity.ofGround e := by
  intro w _
  trivial

/-! ## Section 2: indwelling, the route that covers the persons -/

/-- **Every person is grounded in the ground by indwelling.** With the `EntityMeans
    Entity.ofGround p := True` arm this is free, and this module's rejection of the truth-restricted
    arm is what keeps it free — that is the load-bearing consequence of *not* moving the match arm.

    This is `homoousios`-shared personhood stated as a relation of the ground to persons: it
    makes the ground indwelt rather than empty, and it is the half of `PersonalGround` that
    `no_person_is_the_ground` and `ground_is_not_a_fourth_chooser` together keep from collapsing
    into the deist picture of a substrate the persons merely use.
    Footprint: `{Means, Subject, Will, subjectWill}`. -/
theorem ofGround_grounds_every_person (s : Subject) (_hP : Person s) :
    OneEssence Entity.ofGround (EntityOf s) := by
  intro p _
  trivial

/-! ## Section 3: nothing is outside the ground -/

/-- **No entity is outside the ground**: the ground sustains its being and contains all its
    meaning, so nothing is left ungrounded. The disjunction this module closes is
    `e = g ∨ (GroundByBeing g e ∨ OneEssence g e)` — identity, presence, or indwelling.

    Note which disjunct actually carries the atoms: `OneEssence`'s atom case is vacuous, so the
    left disjunct (`GroundByBeing`) is doing the work for every `ofAtom n` that `actualWorld`
    makes actual. That is why the second route had to be *named* rather than left to chance.
    Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
theorem ofGround_leaves_nothing_ungrounded (e : Entity) (_hAct : ActualEntity e) :
    e = Entity.ofGround ∨ (GroundByBeing Entity.ofGround e ∨ OneEssence Entity.ofGround e) :=
  Or.inr (Or.inl (ofGround_grounds_every_being_by_presence e))

/-! ## Section 4: what the ground's scope does and does not give -/

/-- **The ground's scope does co-contain incompatible contents** — with the total arm it means
    every proposition, so it takes in both horns of every conflict. This is the result the
    checker forced, and it is the doctrine: **plenitude of scope is not freedom.**

    A rejected alternative asserted the ground "cannot co-mean incompatibles". That is
    simply false against today's arm, and asserting it would have imported a claim nothing
    supports. Freedom in Γ is not bearing all content — it is `Asiety`
    (`ground_is_not_a_fourth_chooser`), which requires being a `Subject`. So the ground's total
    scope does *not* make it maximally free, which would be absurd; it does not, because freedom
    is subject-indexed.

    The witness is degenerate (`True`/`False`, horns trivially excluded) because the claim is about
    the ground's *scope*, not about a substantive pair. It is not evidence that the ground settles
    anything; the content-transfer relation's inability to deliver a choice of contents is priced
    separately in `AsietyFreedom.groundingCannotDeliverTrueChoice` (`{}`).
    Footprint: `{Means, Subject}`. -/
theorem ground_scope_does_contain_incompatibles :
    ∃ p q : Prop, EntityMeans Entity.ofGround p ∧ EntityMeans Entity.ofGround q ∧ Incompatible p q :=
  ⟨True, False, trivial, trivial, fun h => h.2⟩

/-- **The ground is not an asietic entity: no subject, so no true choice at the ground.** This is
    doctrine, not a defect — the one essence is not a fourth instance of choosing alongside the
    three; its freedom is their freedom, shared rather than duplicated (`AsietyFreedomOfGround`,
    `Tag: META`, priced and registered ◈ in `Stipulations.lean`).

    This is *praeter hoc, quod unus est, tres sunt* as a machine-checked row: besides the fact
    that there is one, there are three — and the one is not a fourth. Reading `ofGround`'s `True`
    arm as freedom would be the deist mistake of counting the substrate as a chooser, which is the
    opposite error from `ground_scope_does_contain_incompatibles`.

    Distinct from its two neighbours by scope, not by content: `AsieticChoice.ground_is_not_a_true_chooser`
    (C285) denies the weaker `∃ s, EntityOf s = Entity.ofGround` (no *chooser*), this denies
    `Asiety` (no *true* choice), and `AsieticChoice.ground_is_canonically_aseitous_but_not_asietic`
    is conditional on `hFinite`. The present row is unconditional and is the one the Nicene
    reading needs, since it must hold with or without a finitude premise.
    Footprint: `{Means, Subject}`. -/
theorem ground_is_not_a_fourth_chooser : ¬ Asiety Entity.ofGround := by
  intro h
  obtain ⟨s, _p, _q, hs, _⟩ := h
  exact ofGround_ne_ofSubject s hs

/-- **No person is the ground.** Hypostatic *identity* is not merely unproved but unstatable:
    `Entity.ofGround` and `Entity.ofSubject _` are distinct constructors, so `Entity.noConfusion`
    decides it. This is the row that keeps §1.6's two axes apart — one ground over *entities*
    (`exactly_one_universal_modal_ground`, C320) and three persons over *persons* — so the ground
    is not one of the three and the three are not grounds.

    The apparent contradiction dissolves on the axes, and **no change to the `Entity` type is
    required anywhere in this plan** because of this row.

    Restated in the Nicene form, since `NecessityEternity.ofGround_ne_ofSubject` is the technical
    `≠` and this is the claim the corpus has to be able to cite. Keeping both is deliberate: plan
    §6.3 retired hypostatic identity as the *wrong form of the claim*, and this row is the surviving
    form, not a duplicate of the technical one.
    Footprint: `{Subject}`. -/
theorem no_person_is_the_ground (s : Subject) : ¬ (Entity.ofGround = EntityOf s) :=
  ofGround_ne_ofSubject s

/-! ## Section 5: homoousios, which needs no new relation -/

/-- **`Perichoretic g a b c`: the one essence indwelt by three persons.** What this predicate
    carries is *homoousios* — one essence, three persons — as three `OneEssence` instances
    against the one ground. It needs no new relation, which is why it costs nothing.

    **This is not perichoresis in the strict sense, and it must not be read as one.** Two earlier
    versions of this docstring said it was not perichoresis *because* `OneEssence` is
    **asymmetric**, citing "the generic structure's `asymmetric` field". That was false twice
    over and is retracted here:

    - There is no `asymmetric` field on `PersonalGround`. The structure has exactly two fields,
      `sustains` and `indwells` (`TrinitarianPersonalGround.lean:274`). The only `asymmetric`
      field in the corpus is `PersonalNormativeGround.asymmetric`
      (`PersonalNormativeGround.lean:214`), and it constrains `Grounds`, not `OneEssence`.
    - `OneEssence` is **reflexive**, not asymmetric: `groundsEntity_reflexive`
      (`FoundationalUnicity.lean:116`) proves `OneEssence e e` at every entity. The asymmetry
      statement `AsymmetricGrounding` is **proved unsatisfiable** by C316
      (`not_asymmetric_grounding`, `FoundationalUnicity.lean:145`), which GAPMAP records as
      voiding the C207 route. So "persons cannot ground one another" was never established, and
      the docstring asserted a refuted premise in order to look settled.

    **The real reason strict perichoresis is absent is Modalism, not asymmetry.** Formalising
    mutual grounding *through this relation* is possible — asymmetry would not have blocked it —
    but it is a heresy. For two persons `a b`:

        OneEssence (EntityOf a) (EntityOf b)  =  ∀ p, EntityMeans (EntityOf b) p → EntityMeans (EntityOf a) p
        OneEssence (EntityOf b) (EntityOf a)  =  ∀ p, EntityMeans (EntityOf a) p → EntityMeans (EntityOf b) p

    and the pair is exactly the biconditional `∀ p, EntityMeans (EntityOf a) p ↔ EntityMeans
    (EntityOf b) p`, i.e. **C572**, withdrawn as wrongly shaped because identical meaning across
    the Persons makes them interchangeable — the Son becomes "the one the Father is". So a
    mutual-*grounding* reading is not an unproved lemma we failed to reach; it is a claim we
    should not want.

    Strict perichoresis — the *kyklos*, the Persons in-dwelling **in each other** — is therefore
    not statable with the relation this module has, and is not statable with mutual `OneEssence`
    either. It needs a **new primitive** (symmetric, and deliberately not a meaning-containment
    order) which Γ does not have. That is an open, priced item, recorded in GAPMAP as the
    perichoresis frontier row; it is *not* discharged here, and G8 keeps this paragraph honest
    rather than pinning the retracted asymmetry claim. The classical warrant that the Persons are
    distinguished by relations of origin rather than by essences (*ST* I q. 28 a. 3) points the
    same way, and those relations are open too (the X2 row: which hypostasis each `Subject` is).

    The instantiation `ofGround_is_perichoretic` is therefore unconditional, and §5.1's use of it
    as the last conjunct of the master theorem needs no further price.
    Footprint: `{Means, Subject}`. -/
def Perichoretic (g : Entity) (a b c : Subject) : Prop :=
  OneEssence g (EntityOf a) ∧ OneEssence g (EntityOf b) ∧ OneEssence g (EntityOf c)

/-- **The ground is perichoretic, for any three persons.** Three instantiations of
    `ofGround_grounds_every_person`, so `{}` in the substantive sense. The name is retained for
    continuity with the master theorem's last conjunct, but read `Perichoretic` as its
    definition says — *homoousios*, one essence indwelt by three persons — not as the *kyklos*;
    see the `Perichoretic` docstring for why the latter is Modalism rather than asymmetry.

    The persons are still undistinguished here — nothing in this row says there are exactly three
    of them, or that they are necessary, or that they are related by origin, or that they
    in-dwell each other. The population question is bought by `TrinitarianPersonalBridge`
    (`Tag: META`, GAPMAP C509); the *relations of origin* are the open X2 row; the mutual
    indwelling is the open perichoresis row. So this row is the *form*, and
    `trinitarianPersonalGround_summary`'s last-but-one conjunct is deliberately a universal over
    person-carrying arguments rather than an existential.
    Footprint: `{Means, Subject, Will, subjectWill}`. -/
theorem ofGround_is_perichoretic (a b c : Subject) (ha : Person a) (hb : Person b) (hc : Person c) :
    Perichoretic Entity.ofGround a b c :=
  ⟨ofGround_grounds_every_person a ha,
    ofGround_grounds_every_person b hb,
    ofGround_grounds_every_person c hc⟩

/-! ## Section 6: the personal ground — the module in one line -/

/-- **The ground is a personal ground: it sustains all being and indwells every person.** Not void
    of personhood, and not a fourth chooser: the conjunction is the whole Nicene position in Γ's
    vocabulary, and both halves are needed for it. `indwells` alone would permit a demiurge plus
    three unrelated saints; the doctrine is that everything in the ground that acts acts as one of
    the three, and that the ground is the one essence they subsist in and which lives by them.

    Both fields are `{}`-substantive. `sustains` is `GroundByBeing` (presence-grounding) and
    `indwells` is `OneEssence` (providential indwelling) — this module's two named routes,
    conjoined. The `ActualEntity` restriction on `sustains` is inherited from `GroundOfReality`'s
    shape and is not doing work for the ground's own case: `actualWorld` makes every atom actual,
    so the field ranges over subjects and atoms alike, and `GroundByBeing` covers each.

    **What this is not.** It does not make the ground a subject: `PersonalGround` has no
    `Asiety` field and cannot be given one, since `ground_is_not_a_fourth_chooser` refutes it at
    zero substantive axioms. The ground's personhood is *homoousios*-shared — the three Persons are
    what make the essence alive — and the freedom is transferred, not exercised
    (`AsietyFreedomOfGround`, `Tag: META`).
    Footprint: `{Means, NecessarySubjectKind, Subject, Will, subjectWill}`. -/
structure PersonalGround (g : Entity) : Prop where
  sustains : ∀ e : Entity, ActualEntity e → (e = g ∨ GroundByBeing g e)
  indwells : ∀ s : Subject, Person s → OneEssence g (EntityOf s)

/-- **The ground is not void of personhood.** Every person is grounded in it; it sustains all
    being; and it is not a fourth chooser. This is the headline of this module, and its
    substantive price is **zero**.

    The three Persons are what make the essence alive; this is *homoousios*-shared personhood, not
    subject-predication of the ground, which is impossible
    (`ground_is_not_a_fourth_chooser`). A demiurge plus three saints is machine-refuted by the
    `indwells` field, and a fourth chooser is machine-refuted outright.
    Footprint: `{Means, NecessarySubjectKind, Subject, Will, subjectWill}`. -/
theorem the_ground_is_not_void_of_personhood : PersonalGround Entity.ofGround where
  sustains := fun e _ => Or.inr (ofGround_grounds_every_being_by_presence e)
  indwells := fun _ hP => ofGround_grounds_every_person _ hP

/-- ★ **The module in one line.** Two named grounding routes close the disjunction; the ground
    takes in both horns of every conflict and is nevertheless not a chooser; it sustains all being,
    indwells every person, and is no person's correlate. Zero new axioms.
    Footprint: `{Means, NecessarySubjectKind, Subject, Will, subjectWill}`. -/
theorem trinitarianPersonalGround_summary :
    (∀ e : Entity, GroundByBeing Entity.ofGround e) ∧
    (∀ s : Subject, Person s → OneEssence Entity.ofGround (EntityOf s)) ∧
    (∃ p q : Prop, EntityMeans Entity.ofGround p ∧ EntityMeans Entity.ofGround q ∧ Incompatible p q) ∧
    (¬ Asiety Entity.ofGround) ∧
    (∀ s : Subject, ¬ (Entity.ofGround = EntityOf s)) ∧
    (∀ a b c : Subject, Person a → Person b → Person c → Perichoretic Entity.ofGround a b c) ∧
    PersonalGround Entity.ofGround :=
  ⟨fun e => ofGround_grounds_every_being_by_presence e,
    fun s hP => ofGround_grounds_every_person s hP,
    ground_scope_does_contain_incompatibles,
    ground_is_not_a_fourth_chooser,
    fun s => no_person_is_the_ground s,
    fun a b c ha hb hc => ofGround_is_perichoretic a b c ha hb hc,
    the_ground_is_not_void_of_personhood⟩

-- ============================================================================
-- Section 7: Axiom Footprint Audit
-- ============================================================================

#print axioms GroundByBeing
#print axioms Perichoretic
#print axioms PersonalGround
#print axioms ofGround_grounds_every_being_by_presence
#print axioms ofGround_grounds_every_person
#print axioms ofGround_leaves_nothing_ungrounded
#print axioms ground_scope_does_contain_incompatibles
#print axioms ground_is_not_a_fourth_chooser
#print axioms no_person_is_the_ground
#print axioms ofGround_is_perichoretic
#print axioms the_ground_is_not_void_of_personhood
#print axioms trinitarianPersonalGround_summary

/-! **DOCTRINE ROW 3 (nomenclature; GAPMAP C568): *homoousios* — one essence, three
Persons.** There is no declaration for this, and the deletion of the one that used to be here is
the point of this docstring.

A `Consubstantial g a b := OneEssence g a ∧ OneEssence g b` was carried here (GAPMAP C568) on the
reasoning that `OneEssence` is directional, and therefore cannot express the *mutuality* between
the Persons. **That reasoning was wrong, in the same way the `Perichoretic` docstring was.**
`OneEssence` is not directional in the sense assumed: it is **reflexive**
(`groundsEntity_reflexive`, `FoundationalUnicity.lean:116`), and its asymmetry statement
`AsymmetricGrounding` is **proved unsatisfiable** (C316, `not_asymmetric_grounding`,
`FoundationalUnicity.lean:145`). Nothing blocked a mutual reading.

The declaration was still right to delete, but for a different reason than the one recorded:
`Consubstantial g a b` was not *mutual grounding between persons at all* — it was
`OneEssence g a ∧ OneEssence g b`, **two ground-to-person instances**, which is exactly
`Perichoretic`'s content and adds no third conjunct. Instantiated at the ground it is `True` of
arbitrary entities, including atoms, so it asserted nothing about persons at all. It was a
redundant name, and the mutual-perichoresis question it was meant to answer has to be answered by
a new primitive relation instead (see the `Perichoretic` docstring: the mutual reading *through
`OneEssence`* is C572, withdrawn as Modalism). Instantiated at `g = Entity.ofGround` — the only
ground the doctrine has, and the only one every §20 row uses — `OneEssence Entity.ofGround e` holds
for **every** entity `e`, including `Entity.ofAtom 0`. So `Consubstantial Entity.ofGround e f` is
`True` for arbitrary `e` and `f`: it asserts the ground is consubstantial with everything, including
atoms. The mutual-relation reading it promised is exactly the content it does not have, so it was
`True` twice over — a `{}` price on a `True` proposition, which is a null result and not a proof.
(The vacuity is a theorem, not an inspection: `Consubstantial Entity.ofGround e f ↔ True`.)

What replaced it is what was already there. *One essence* is `PersonalGround`'s `indwells` field
(`ofGround_grounds_every_person`, `{Means, Subject, Will, subjectWill}`): every Person is one with
the one ground. That is the doctrine's one-ness, it is free, and it needs no second relation — a
second relation over `OneEssence` at the ground could only ever be `True` again. And the doctrine's
*distinction* half — that the three cannot be collapsed into one — is `roles_make_the_three_persons_distinct`
(`TrinitarianSubjectBridge.lean:279`), free on `{DivineSubjectRole, Subject}`, already a conjunct of
the §5.1 master theorem. Nothing was missing. The `Consubstantial` family is deleted rather than
repaired: there is no non-vacuous version of "both are one with the ground", because that is `True`,
and `True` is not a relation.

**AUTHOR DECISION (2026-10-03): reading (a) is taken.** Three readings of what the
deletion leaves behind were put to the author, and (a) is adopted:

  (a) *It is enough.* All three Persons stand in the **same** relation to the **same** one, none
      is identical to it, and none is a creature. Consubstantiality is fully expressed by that,
      so the deleted `Consubstantial` was a redundant `True` and its removal is a
      simplification. **No `Essence`/`Nature` predicate is introduced, and none is wanted.**
  (b) *Not enough.* Homoousios is a shared **property** — the three have one nature *as each
      other* — which would need an essence predicate. This reading is **not** taken. It was
      never closed by the deleted relation either, since that relation asserted `True`.
  (c) *Moot, on the economic reading.* The Persons are distinguished by relations of origin
      rather than by essence (*ST* I q. 28 a. 3, cited in Section 5), so "consubstantial" would
      be a conclusion from the ground and the relations rather than a third premise. Compatible
      with (a), and the deeper grounding for it, but the relations among the Persons are **not**
      in Γ (open item X2).

So the doctrine's *one-ness* rests on `indwells` and its *three-ness* on
`roles_make_the_three_persons_distinct`, and that is taken to be sufficient. The one thing still
absent is strict **perichoresis** — the Persons in-dwelling in *each other* rather than all three
in the ground — which needs a relation Γ lacks and is not claimed here; `Perichoretic` is three
`indwells` instances and is labelled a *form* accordingly. G8 keeps that label honest.

Note what the one-ness therefore rests on: `indwells` at the ground is `True` **by definition**
(`EntityMeans Entity.ofGround p := True`, `NecessaryPersonalGround.lean:184`), so
`ofGround_grounds_every_person` closes by `trivial`. That is disclosed rather than repaired — the
truth-restricted arm was rejected, and the rejection is what keeps the row free — but a reader
should see it stated: under reading (a) the *one* is carried by a predicate that is
definitionally satisfied, and the content of the row is the `Person s` hypothesis and the
`no_person_is_the_ground` / `ground_is_not_a_fourth_chooser` separations, not the `True`.

`Perichoretic` (Section 5) is kept and is **not** the same claim: it is the conjunction the master
theorem's last conjunct needs, it is honestly labelled there as a *form* rather than a doctrine row,
and its docstring states that perichoresis is **not** a mutual grounding of the Persons in one
another. The reason it gives is the right one: the mutual reading through this relation is **C572,
withdrawn as Modalism** — identical meaning across the Persons — not asymmetry, which C316 shows
was never available as a premise in the first place (`OneEssence` is reflexive).
`scripts/test_personal_ground_kind.py` G8 pins that disclosure, requires the C316 retraction to
accompany any mention of the old asymmetry premise, and is itself verified by mutation. -/


end Logos.TrinitarianPersonalGround