/-
# Logos.CosmicExistence — the cosmos exists, as a proved theorem

`poem.txt:26-30` asks and answers: "este mundo é necessário? Não.." and then places "a
criação que me parece existir" under a salto de fé. This module makes the *existence* half
of that a **theorem of Γ** while leaving purpose and the incarnation in faith.

## Why it is a theorem, and what it costs

**Corrected 2026-09-27.** This module previously declared the existence of the cosmos as a
`Tag: SEM` axiom, on the stated ground that the lemma it requires had no producer:

    ∃ s : Subject, ∃ p : Prop, Means s p

That ground was **false**. The lemma is already an unconditional theorem —
`Plurality.cogito_from_T12`, of `{Means, Subject, Will, subjectWill, AxTwoSubjects}` — via
`T12_twoPersons` (= `AxTwoSubjects rightWrongDistinction`) and `person_is_intentional`, and
`Logos.Core.rightWrongDistinction` is itself axiom-free. The axiom was therefore
**redundant**: it re-charged for a commitment Γ had already made. It is deleted, and
`cosmos_obtains` is the theorem that replaces it.

So the answer to "does the cosmos exist?" is no longer stipulated. **Γ is not satisfiable by
an empty contingent world**, because Γ contains a theorem that *discovers* a subject: from
two distinct persons (`AxTwoSubjects`, `Tag: META`) a person means something
(`person_is_intentional`), a meaning subject witnesses a realm (`cosmos_presence_model`).

Note the verb, and it is load-bearing throughout this module. A theorem **discovers**; it
does not **manufacture**. Nothing here produces a subject — the two persons are already
there, as a matter the derivation reports rather than causes, and the derivation is what
makes the report *checkable*. Γ fabricates nothing. Read every inhabitation below as a
discovery, never as a construction: see `Logos.Agency`'s module note, which states the same
principle for the act-datum and disowns the term "manufacturing" for exactly this reason.

**The price, stated plainly.** Existence now rests on the **plurality bridge**:
`Logos.Value.AxTwoSubjects` — "the reality of right-and-wrong demands at least two distinct
persons". That is a substantive interpersonal metaphysics already declared and paid for
elsewhere in Γ, and it is a `Tag: META` commitment, not a semantic one. Reject it and the
cosmos's existence goes with it. This is a real relocation of the cost — an ontological
claim now leans on an axiological bridge — and it is *tighter* than the axiom was, because
the position is now falsifiable: it can be refuted by rejecting plurality.

**The earlier objection, and why it does not block this route.** The axiom's docstring
argued that "any deductive route to the cosmos's existence would equally force the judging
subject's own claims to be necessary" — the outcome `poem.txt:26` denies. That was aimed at
the *reality-hook* route,

    theorem content_reality_hook (p : Prop) : (∃ s : Subject, Correct s p) → p

which is unconditional in `p` (`RealityHookAudit.lean:85`) and would indeed make "I am
necessary" necessary. **The plurality route never touches `Correct`.** `Realm.bears_meaning`
is meaning-**capacity** (`∃ q, EntityMeans witness q`), not truth, and `Realm.contingent`
*asserts* the realm is modal-fragile. Nothing in the derivation makes any content
necessary, so the reductio does not apply to it.

## Why a new structure rather than a constructor

The cosmos cannot be identified with anything already in the sort: `Entity` has exactly
three constructors (`Entity.lean:23-26`) and there is no `Cosmos`/`Realm` name in the
library. An atom is contingent already (`an_atom_is_contingent`) but bears no meaning
(`atoms_bear_no_meaning`) and is therefore provably *not* an object of love
(`meaningless_entities_cannot_be_loved`); a subject is the user, not the world; the ground
is `NecessaryEntity`; and `actualWorld` is a `def`. So a **new structure** over a single
witness is the honest move, and it leaves every per-constructor theorem untouched.

**One consequence of that structure, recorded because it is easy to misread.**
`EntityMeans` is `False` on `Entity.ofAtom` and `True` on `Entity.ofGround`
(`NecessaryPersonalGround.lean:151-155`), while `Realm.not_the_ground` bars the ground. So
`bears_meaning` and `not_the_ground` together **force the witness to be a person's entity
correlate**. This is a property of the `def`, it held under the deleted axiom too, and it is
*not* introduced by the derivation. It is flagged here because it is a real constraint on
the theology, and it deserves its own ledger row.

**A second correction: the structure must name *one* realm.** The first version of this
module gave `CreatedRealm` three **independent** existential fields while its own docstring
claimed "something actually obtains, the *same something* is modal-fragile". The three
witnesses could be three different entities, so the module's conclusion was really "the
ground loves *some* contingent entity", not "the ground loves the cosmos". The structure now
carries a single `witness` and every field is about it.

The structure also carries a fourth field, `bears_meaning`. That is not decoration: love
requires the target to bear content (`ground_love_requires_a_meaningful_target`), so
without it the conclusion could never be reached. Its honest consequence is that
satisfiability is **conditional on an inhabitant of `Means`** — see `cosmos_presence_model`
— and, as of 2026-09-27, that inhabitant is *supplied by Γ* via
`Plurality.cogito_from_T12`, so the conditionality is discharged in `cosmos_obtains`.

## What is proven here — and what is deliberately not

- **The existence of the cosmos** (`cosmos_obtains : CreatedRealm`), proved from the
  plurality bridge. Footprint `{propext, Means, Subject, Will, subjectWill, AxTwoSubjects}`.
  This is the batch's whole point: it was a `Tag: SEM` axiom until 2026-09-27 and is now
  a theorem, with the price (`AxTwoSubjects`, `Tag: META`) named in the row.
- **The construction** (`cosmos_presence_model`): the structure is inhabited for any
  inhabitant of `Means`, the library's primitive content vocabulary. `Means`
  (`Agency.lean:74`) still has no derivable instance in Γ *by itself* — but Γ's plurality
  axiom supplies one, which is what `cosmos_obtains` consumes.
- **Non-triviality of the contingency conjunct's shape**
  (`perfect_universe_has_no_contingent_realm`): in a world-rigid universe, the shape
  `ActualEntity t ∧ ∃ w, ¬ ExistsAt w t` is unsatisfiable. This says the contingent content
  is not forced by world structure — it does **not** speak about Γ, because
  `PerfectUniverse` is an unrelated free structure, not a model of Γ.
- What is **not** claimed, because it is not provable in Lean core: that the *negation* of
  the theorem is consistent with all of Γ. That is a model-theoretic statement requiring a
  full interpretation of Γ, and no such model is built here. The honest summary is: the
  existence is **derived** and **conditionally satisfiable**; its *refutability by all of
  Γ* is neither built nor claimed.
- The realm is actual, contingent, **not the ground**, and **bearing content of its own** —
  the machine-checked content of "reality is not exhausted by the necessary ground".
- **The conclusion** `the_ground_loves_the_cosmos`, by applying the declared bridge
  `AxGroundLovesContingentRealm` of `Logos.LovesAsGround` to the realm's contingency and
  content. The footprint names the whole price: the plurality bridge, the ground-love
  bridge, the content vocabulary, and the world structure.
- Separations: the realm's existence yields neither its necessity, nor the ground's
  personality. C110 (`necessary_ground_not_entails_contingent_creation`) is untouched and
  still refutes the deductive route.

## What is deliberately NOT formalized

Purposiveness ("não iria ser sem propósito"), the incarnation, and creation-with-purpose
stay in the **faith** zone: F9 is rescoped, not discharged. No predicate of purpose is
invented for them; they are named as still-requiring-proof in the prose corpus.
-/

import Logos.Entity
import Logos.Agency
import Logos.Semantics
import Logos.RecoveredOntologicalGround
import Logos.TheologicalModalHardening
import Logos.NecessityEternity
import Logos.PersonalNormativeGround
import Logos.LovesAsGround
import Logos.Plurality

namespace Logos.CosmicExistence

open Logos.Semantics (World TV)
open Logos.Agency (Subject)
open Logos.Entity (Entity ExistsAt EntityOf EntityExistsAt SubjectExistsAt actualWorld)
open Logos.RecoveredOntologicalGround (EntityMeans)
open Logos.TheologicalModalHardening
    (ActualEntity ContingentEntity NecessaryEntity necessary_not_contingent)
open Logos.NecessityEternity (ofGround_necessary ofGround_ne_ofSubject)
open Logos.PersonalNormativeGround (PersonalEntity)
open Logos.LovesAsGround
    (GroundBearsGood GroundLoves AxGroundLovesContingentRealm
     the_ground_loves_every_meaningful_contingent_reality
     the_ground_bears_a_directional_good_toward_the_cosmos
     falsityWorld_ne_actualWorld an_atom_is_contingent)

-- ============================================================================
-- Section 1: The realm — one realm, one witness, a meaning-bearing inhabitation
--
-- `Realm` is the *meaning-bearing* realm. It carries a `bears_meaning` field, which is
-- what makes it a possible target of a relation that is more than meaning-capacity
-- (`ground_love_requires_a_meaningful_target`) — and what makes inhabiting it cost
-- `AxTwoSubjects`, since `Subject` is an opaque sort. Nothing in this section was ever a
-- declared datum: `CreatedRealm` is a `def` over a `Type`-valued record, and its
-- inhabitation is the theorem `cosmos_obtains` (Section 2).
-- ============================================================================

/-- **The realm, as one record.** Every field is a predicate over the existing vocabulary
    about **one** entity, so the record really does describe a single realm: it obtains, it
    is modal-fragile, it is not identical with the necessary ground, and it bears content of
    its own.

    The single `witness` is a correction: the earlier three-existential version could be
    witnessed by three different entities, which made "the cosmos" meaningless in the
    conclusion. `bears_meaning` is required because love requires a content-bearing target
    (`ground_love_requires_a_meaningful_target`), and because `EntityMeans (ofAtom _) =
    False`, so a realm that bore nothing could never be loved.

    This is a `Type`-valued record, not a `Prop` structure: a `Prop`-valued structure may
    not carry a data field, so a single witness is only expressible this way. The `Prop`
    form is `CreatedRealm` below, and that `def` is the audited one. -/
structure Realm : Type where
  /-- The realm. -/
  witness : Entity
  /-- The realm actually obtains. -/
  actual : ActualEntity witness
  /-- The realm is modal-fragile: it fails to obtain in some possible world. This is what
      the poem's "este mundo é necessário? Não" asserts. -/
  contingent : ∃ w : World, ¬ ExistsAt w witness
  /-- The realm is distinct from the necessary ground: it is not exhausted by it. -/
  not_the_ground : witness ≠ Entity.ofGround
  /-- The realm bears content of its own, so it can be the target of a relation that is
      not mere meaning-capacity. -/
  bears_meaning : ∃ q : Prop, EntityMeans witness q

/-- **A meaning-bearing created realm exists** — there is a realm of the shape `Realm`.
    Stated as `Nonempty` so it is a `Prop` the ledger can name, while the record it
    inhabits keeps a single witness.

    Inhabiting this is **not** free: the `bears_meaning` field forces the witness to be a
    `Subject`, so any inhabitant costs `AxTwoSubjects`. For the existence claim *without*
    that price see `ContingentRealmObtains` below, and for the two claims derived from each
    see `contingent_realm_obtains` and `cosmos_obtains` respectively.
    Footprint: `{Means, Subject}`. -/
def CreatedRealm : Prop := Nonempty Realm

-- ============================================================================
-- Section 1b: The realm without the meaning condition — existence at no
--            substantive price
-- ============================================================================

/-- A contingent created realm, without the meaning condition: something that obtains, is
    modal-fragile, and is not the necessary ground.

    `Realm` (`:161`) requires `bears_meaning`, and because `EntityMeans` is `False` on
    `ofAtom` and `True` on `ofGround` — the latter excluded by `not_the_ground` — that single
    field forces the witness to be a `Subject`. `Subject` is an opaque sort
    (`Agency.lean:43-49`), so *inhabiting* `Realm` costs `AxTwoSubjects`. **Existence does
    not need that field.** Dropping it is a `structure` change, and it adds no axiom — which
    is what lets cosmos existence be derived rather than charged for.

    **On the word "created".** It labels the *region* of reality this record describes:
    actual, modal-fragile, not the ground. It does **not** assert production. No `Creates`
    relation, no agent and no first moment appear in this structure or in the theorem that
    inhabits it, and none is derivable from them — grounding still does not entail a creation
    record, which is C110's standing result. The only thesis here is that reality is **not
    exhausted by the necessary**. Production is a separate lane, and it is unclaimed.

    **Not the identification of an atom with the cosmos** — the same limit C324 carries. What
    is proved below is that the *shape* has an instance. Which realm that is belongs to
    `cosmos_obtains` (C367), not to this structure.
    As with `Realm`, no footprint marker is claimed here: a `structure` is not listed in
    `axiom_audit.json` (the audit covers `thm`/`def`/`axiom` only), so the machine-checked
    markers sit on `ContingentRealmObtains` and on `contingent_realm_obtains`. -/
structure ContingentRealm : Type where
  /-- The realm. -/
  witness : Entity
  /-- The realm actually obtains. -/
  actual : ActualEntity witness
  /-- The realm is modal-fragile: it fails to obtain in some possible world. -/
  contingent : ∃ w : World, ¬ ExistsAt w witness
  /-- The realm is distinct from the necessary ground: it is not exhausted by it. -/
  not_the_ground : witness ≠ Entity.ofGround

/-- A contingent created realm obtains — the `Prop` form, so the ledger can name it as a
    claim while the record keeps a single witness.
    Footprint: `{Subject}`. -/
def ContingentRealmObtains : Prop := Nonempty ContingentRealm

/-- Contingency-overflow: something obtains, is modal-fragile, and is not the necessary
    ground — and Γ derives it outright, resting on nothing substantive.

    The witness is an atom, reusing `LovesAsGround.an_atom_is_contingent 0`
    (`LovesAsGround.lean:171`), itself `{Subject, propext}`. The reuse is deliberate, and
    the construction is **not** vacuous: `EntityExistsAt w (ofAtom n) := w n = TV.t`
    (`Entity.lean:45-48`) discriminates on the index, so `actualWorld 0 = TV.t` while
    `fun _ => TV.f` falsifies it. Contingency here is a real property of this entity, not an
    artifact of a coarse world sort.

    **What this costs: nothing substantive.** `Subject` enters only as the sort behind
    `Entity`, never as an inhabited existential, and `propext` is Lean's classical
    propositional logic. Before 2026-09-27 the same content cost
    `{propext, Means, Will, subjectWill, AxTwoSubjects}`, because it was obtained by
    destructing a `bears_meaning` witness. The difference between that and this is the whole
    of the change: **existence is derived, not purchased.**

    This does **not** make an atom into the cosmos (C324 forbids it), and it does not say
    anything made the realm — see the structure's docstring.
    Footprint: `{propext, Subject}`. -/
theorem contingent_realm_obtains : ContingentRealmObtains := by
  obtain ⟨ha, hc⟩ := an_atom_is_contingent 0
  exact ⟨⟨Entity.ofAtom 0, ha, hc, Entity.noConfusion⟩⟩

-- ============================================================================
-- Section 2: Consistency and non-triviality
-- ============================================================================

/-- **Conditional satisfiability.** The realm does obtain, for any inhabitant of `Means`.
    The witness is a subject, which is actual at the actual world
    (`SubjectExistsAt w s := w = actualWorld`), refuted at the all-`TV.f` world, distinct
    from the ground by `Entity.noConfusion`, and bearing content because
    `EntityMeans (ofSubject s) p` unfolds to `Means s p`.

    The `Means` hypothesis is not a technicality and is not hidden: `Means` is a primitive
    `Tag: VOCAB` **axiom** (`Agency.lean:74`) with no derivable instance in Γ, so this
    theorem is satisfiability *relative to* Γ's intentional vocabulary being inhabited. It
    is stated that way rather than claimed outright.

    **This is not the identification of a subject with the cosmos** — the model witnesses
    only that the structure is satisfiable, and the witness is forced to be a subject by
    `bears_meaning` + `not_the_ground` together. See `cosmos_obtains` for the theorem that
    consumes it, which reads the witness as *evidence of reality's addressability* rather
    than as the cosmos itself.
    Footprint: `{Means, Subject, propext}`. -/
theorem cosmos_presence_model
    (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Means s p) : CreatedRealm := by
  obtain ⟨s, p, hp⟩ := h
  exact
    ⟨{ witness := EntityOf s
       actual := rfl
       contingent := ⟨(fun _ => TV.f), falsityWorld_ne_actualWorld⟩
       not_the_ground := Entity.noConfusion
       bears_meaning := ⟨p, hp⟩ }⟩

/-- **The realm, on the performative act-datum instead of the plurality bridge.**
    `cosmos_presence_model` is the inhabitation; what it needs is a subject who means
    something, and `Logos.Plurality.cogito_from_T12` gets one by paying
    `Logos.Value.AxTwoSubjects`. That payment is **not forced**. The performative
    act-datum gets the same witness with no bridge at all:
    `Logos.Agency.act_datum_implies_means` turns `∃ s, ∃ p, Act s p` straight into
    `∃ s, ∃ p, Means s p`, because `Act` already contains `Means` as a conjunct.

    This is the God-lane, and it is deliberately a *new row* rather than a
    re-anchoring of `cosmos_obtains`. The two reasons, both of them the project's
    own:

    - **A theorem discovers, it does not manufacture.** Γ cannot supply a subject out
      of nothing, and it is not being asked to: the act-datum is *assumed as given*,
      the way `Logos.Agency` states its foundation — "the present act of reasoning is
      *given*, not inferred" (`Agency.lean:4`). The price moves from a META bridge to
      a TRANS datum. It does not evaporate, and the row is badged ◈ accordingly.
    - **The A1 bug was exactly this made unconditional.** Deleting the act-datum and
      anchoring subject-existence on plurality made it "a consequence of plurality —
      the very datum it must precede" (`GAPMAP.md`, batch A1/M0). A1 was caught and
      reverted for that reason; re-anchoring `cosmos_obtains` now would repeat it.

    So the claim is *not* that the cosmos is free. It is that `AxTwoSubjects` is one
    route to a meaning-bearing realm and not the only one, which is a falsifiable
    difference: reject the bridge and C367 goes, while this row stands on the datum
    alone.
    Footprint: `{propext, Initiates, Means, State, Subject}`. -/
theorem cosmos_presence_model_of_the_act_datum
    (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Act s p) : CreatedRealm :=
  cosmos_presence_model (Logos.Agency.act_datum_implies_means h)

/-- **The cosmos exists** — a contingent created realm, not the necessary ground, actually
    obtains and bears content of its own.

    **This was a `Tag: SEM` axiom until 2026-09-27, and that was an error.**
    `AxContingentCreationObtains` was declared on the ground that the lemma it needs had no
    producer. It does have one. Γ contains a theorem that *discovers* a subject:

        rightWrongDistinction        : ¬ N_T ∧ ¬ N_F                      -- `{}`
        T12_twoPersons               = AxTwoSubjects rightWrongDistinction
        person_is_intentional        : Person s → ∃ p, Means s p
        cogito_from_T12              : ∃ s, ∃ p, Means s p                -- unconditional

    so `cosmos_presence_model cogito_from_T12` inhabits `CreatedRealm` outright. The axiom
    was re-charging for a commitment Γ had already made, and it is deleted.

    **What Γ can now say, and cannot.** It can say the contingent realm exists: Γ is not
    satisfiable by an empty contingent world, because Γ contains a theorem exhibiting a
    subject who means something. It still cannot say the realm's *negation* is consistent
    with all of Γ — that needs a full interpretation of Γ, and no such model is built here.

    **The price, which is the whole cost of this row.** Existence *as such* no longer costs
    anything: see `contingent_realm_obtains` (`{propext, Subject}`), which yields the same
    contingency-overflow with no substantive axiom. What this row costs is the *meaning* half
    of the thesis, and it pays for it through the plurality bridge
    `Logos.Value.AxTwoSubjects` (`Tag: META`): the reality of right-and-wrong demands at least
    two distinct persons. That is a substantive interpersonal metaphysics, already declared
    and paid for elsewhere in Γ, and it is *not* a semantic choice.

    So the correct statement of the price is narrower than it was: **reject `AxTwoSubjects`
    and the realm's *meaning-bearingness* goes, not the realm's existence.** The position is
    tighter than the axiom was, because it is now falsifiable — but a meaning claim now leans
    on an axiological bridge, and that is a relocation of the cost, not a removal of it.

    **This row is C367, not C350.** The 2026-09-27 split moved the bare existence claim to
    `contingent_realm_obtains` (C350, `PROVEN`, `{propext, Subject}`) and left the
    meaning-bearing inhabitation here. What distinguishes the two is `bears_meaning`, and
    what identifies the derived realm as *the cosmos* is this row — not C324's atom, which
    the ledger explicitly forbids reading as the cosmos.

    **Why the old objection does not apply.** The deleted docstring argued that any
    deductive route here "would equally force the judging subject's own claims to be
    necessary", the outcome `poem.txt:26` denies. That was aimed at the reality-hook route
    `(∃ s, Correct s p) → p`, which is unconditional in `p`. This route never touches
    `Correct`: `Realm.bears_meaning` is meaning-**capacity**, and `Realm.contingent`
    *asserts* modal-fragility. Nothing becomes necessary.

    Non-triviality of the contingency content is unchanged and still machine-checked:
    `perfect_universe_has_no_contingent_realm` refutes the `Realm` shape in a world-rigid
    universe. C110's separation also survives untouched — existence is derived, and the
    deductive route from necessary ground to a creation record is still refuted.
    Footprint: `{propext, Means, Subject, Will, subjectWill, AxTwoSubjects}`. -/
theorem cosmos_obtains : CreatedRealm :=
  cosmos_presence_model Logos.Plurality.cogito_from_T12

/-- **No reading of Γ satisfies an empty contingent world.** The subject the derivation
    reports is *discovered inside Γ*, not assumed and not manufactured: `cogito_from_T12`
    has no hypothesis, and its
    input `Logos.Core.rightWrongDistinction` is axiom-free. Stated as a standalone fact so
    the "cannot come about in an empty world" claim is checkable on its own, rather than
    only as a side effect of the row above. (No `propext`: it is `cogito_from_T12` verbatim,
    and the `propext` in `cosmos_obtains` enters only through `Realm`'s record fields.)
    Footprint: `{Means, Subject, Will, subjectWill, AxTwoSubjects}`. -/
theorem gamma_exhibits_a_meaning_subject :
    ∃ s : Subject, ∃ p : Prop, Logos.Agency.Means s p :=
  Logos.Plurality.cogito_from_T12

/-- **A world-rigid universe**, in the `ModalOntologySignature` idiom of
    `TheologicalModalHardening.lean:74-80`. Used as the negative side of the realm's
    consistency story.

    Read the scope carefully: this is an **unrelated free structure, not a model of Γ**. It
    shows that the shape of the realm's contingency field is not forced by world-rigidity
    *in general*; it says nothing about Γ's worlds, on which the contingency claim simply
    holds. -/
structure PerfectUniverse where
  World : Type
  actualWorld : World
  Entity : Type
  ExistsAt : World → Entity → Prop
  /-- World-rigidity of existence: what holds at the actual world holds at every world.
      This is the field that makes contingency impossible in the universe. -/
  WorldRigid : ∀ w : World, ∀ e : Entity, ExistsAt w e ↔ ExistsAt actualWorld e

/-- **Non-triviality of the contingency conjunct's shape.** In a `PerfectUniverse` every
    actual entity is necessary, so the shape `ExistsAt actualWorld t ∧ ∃ w, ¬ ExistsAt w t`
    is unsatisfiable there. The contingency conjunct is therefore not a triviality of the
    world structure.
    Footprint: `{}`. -/
theorem perfect_universe_actual_is_necessary (U : PerfectUniverse) :
    ∀ t : U.Entity, U.ExistsAt U.actualWorld t → ∀ w : U.World, U.ExistsAt w t := by
  intro t ht w
  exact (U.WorldRigid w t).mpr ht

/-- **The contingency shape is refuted.** In a `PerfectUniverse` world-rigidity makes every
    actual entity necessary, so nothing witnesses `ExistsAt actualWorld t ∧ ∃ w,
    ¬ ExistsAt w t` — the shape of `CreatedRealm.contingent`.
    Footprint: `{}`. -/
theorem perfect_universe_has_no_contingent_realm (U : PerfectUniverse) :
    ¬ (∃ t : U.Entity, U.ExistsAt U.actualWorld t ∧ ∃ w : U.World, ¬ U.ExistsAt w t) := by
  rintro ⟨t, ht, w, hw⟩
  exact hw (perfect_universe_actual_is_necessary U t ht w)

/-- **The realm's existence is not refutable** by the theory: the structure is inhabited, so
    no theorem of Γ can refute it. **Renamed 2026-09-27** from
    `the_cosmos_datum_is_not_refutable` — there is no longer a datum to be refuted. The name
    would otherwise have reintroduced the very "declared datum" language this module removes.

    Since 2026-09-27 it also **loses its hypothesis**. It used to require a `Means` inhabitant
    and then refute the emptiness of a *meaning-bearing* `CreatedRealm`, which cost
    `{Means, Subject, propext}`. The bare `ContingentRealmObtains` is inhabited outright, so
    the honest statement is the unconditional one and the hypothesis is gone rather than
    carried as decoration.

    This is the half of the *empirical* character Lean can certify: the claim is consistent
    with the theory that states it. Its **status is derived** (`contingent_realm_obtains`).
    The ambient contingency it appeals to is itself a countermodel
    (`Logos.NecessityEternity.everlasting_but_contingent`), so the contingency content is not
    a triviality of Γ either.
    Footprint: `{propext, Subject}`. -/
theorem the_cosmos_existence_is_not_refutable : ¬ (ContingentRealmObtains → False) :=
  fun hh => hh contingent_realm_obtains

-- ============================================================================
-- Section 3: What the realm is — and is not — machine-checked
-- ============================================================================

/-- Something contingent obtains. This is the whole of what is claimed about existence on
    the free route, and it no longer rides on the meaning-bearing `cosmos_obtains`: since
    2026-09-27 it is read off `contingent_realm_obtains`, which costs nothing substantive.
    Footprint: `{propext, Subject}`. -/
theorem a_created_realm_obtains : ∃ t : Entity, ActualEntity t := by
  obtain ⟨R⟩ := contingent_realm_obtains
  exact ⟨R.witness, R.actual⟩

/-- The realm is contingent. The machine-checked content of the poem's
    "este mundo é necessário? Não" — now at vocabulary-only price, for the same reason as
    `a_created_realm_obtains`.
    Footprint: `{propext, Subject}`. -/
theorem a_contingent_reality_obtains : ∃ t : Entity, ContingentEntity t := by
  obtain ⟨R⟩ := contingent_realm_obtains
  exact ⟨R.witness, ⟨R.actual, R.contingent⟩⟩

/-- The realm is not the ground. This is the *negative* half of the thesis — the
    machine-checked form of "reality is not exhausted by the ground" — and it is the step
    the deductive route (C110) cannot supply in the other direction. Free since 2026-09-27:
    the price used to be `AxTwoSubjects`, carried only by the `bears_meaning` witness.
    Footprint: `{propext, Subject}`. -/
theorem reality_is_not_exhausted_by_the_ground :
    ∃ t : Entity, ActualEntity t ∧ t ≠ Entity.ofGround := by
  obtain ⟨R⟩ := contingent_realm_obtains
  exact ⟨R.witness, ⟨R.actual, R.not_the_ground⟩⟩

/-- The realm bears content of its own — the fact that makes it a *possible* target of a
    relation that is more than meaning-capacity, and the fact that distinguishes the
    meaning-bearing realm from the bare atom-existence of `a_contingent_entity_exists`.

    **This claim keeps its price on purpose.** It is read off `cosmos_obtains` and therefore
    inherits `AxTwoSubjects`, because `bears_meaning` needs a `Subject` and `Subject` is an
    opaque sort. Meaning is the substantive half of the thesis; charging for it is correct,
    and the 2026-09-27 change deliberately did **not** route this through
    `contingent_realm_obtains`. Doing so would be a vacuous proof, and the two shortcuts that
    would have made it free — rescoping love onto an atom, and relaxing `EntityMeans` so
    atoms bear content — were both considered and rejected.
    Footprint: `{propext, Means, Subject, Will, subjectWill, AxTwoSubjects}`. -/
theorem the_realm_bears_meaning : ∃ t : Entity, ∃ q : Prop, EntityMeans t q := by
  obtain ⟨R⟩ := cosmos_obtains
  exact ⟨R.witness, R.bears_meaning⟩

/-- The two poles, side by side: the ground is necessary and the realm is contingent, so
    the realm's existence cannot be read off the ground's necessity. Both halves are
    machine-checked, and together they are the whole content of "not merely a mathematical
    ground" available *before* any love is claimed. **Free since 2026-09-27**: the ground's
    necessity is `{Subject}` (`ofGround_necessary`) and the realm's contingency is
    `{Subject, propext}` (`a_contingent_reality_obtains`), so no substantive axiom appears.
    Footprint: `{propext, Subject}`. -/
theorem the_ground_is_necessary_and_the_realm_is_contingent :
    NecessaryEntity Entity.ofGround ∧ ∃ t : Entity, ContingentEntity t :=
  ⟨ofGround_necessary, a_contingent_reality_obtains⟩

/-- **The conclusion, with both prices visible.** The realm's contingency and content plus
    the declared bridge yield a directional good the ground holds toward the cosmos — "He
    is not merely a mathematical ground, but loves". The footprint names the whole price:
    the meaning vocabulary, the metaphysical bridge, the love bridge, and the world structure.
    The claim is about the ground *as a kind*: no hypostatic identification is made
    (`ofGround_ne_ofSubject`).

    **This price is kept deliberately.** Since 2026-09-27 the existence conjunct is available
    free (`a_contingent_reality_obtains`), so this row is no longer paying for existence; it
    pays only for the *meaning* conjunct and the two declared bridges. That is the correct
    distribution — a realm with no content could not be loved, so the content is what is
    being charged for.
    Footprint: `{propext, Means, Subject, Will, subjectWill, AxTwoSubjects, AxGroundLovesContingentRealm, GroundBearsGood}`. -/
theorem the_ground_loves_the_cosmos :
    ∃ t : Entity, ContingentEntity t ∧ (∃ q, EntityMeans t q) ∧
      ∃ p, GroundBearsGood Entity.ofGround t p := by
  obtain ⟨R⟩ := cosmos_obtains
  obtain ⟨q, hq⟩ := R.bears_meaning
  have hc : ContingentEntity R.witness := ⟨R.actual, R.contingent⟩
  exact ⟨R.witness, hc, ⟨q, hq⟩,
    the_ground_bears_a_directional_good_toward_the_cosmos hc ⟨q, hq⟩⟩

/-- The same conclusion in the library's relational vocabulary: there is a context in which
    the ground's love of the realm holds. Note this is the *relation* `GroundLoves`, not
    interpersonal `Loves` — the two are provably disjoint, and the transfer is unstatable
    rather than merely unproved (`ground_love_cannot_be_read_as_person_love`). Kept priced
    for the same reason as `the_ground_loves_the_cosmos`: the meaning conjunct, not
    existence, is the load-bearing premise.
    Footprint: `{propext, Means, Subject, Will, subjectWill, AxTwoSubjects, AxGroundLovesContingentRealm, GroundBearsGood}`. -/
theorem the_ground_loves_the_cosmos_in_a_context :
    ∃ t : Entity, ContingentEntity t ∧ ∃ a : Prop, GroundLoves Entity.ofGround t a := by
  obtain ⟨R⟩ := cosmos_obtains
  have hc : ContingentEntity R.witness := ⟨R.actual, R.contingent⟩
  exact ⟨R.witness, hc,
    the_ground_loves_every_meaningful_contingent_reality hc R.bears_meaning⟩

-- ============================================================================
-- Section 3b: The God-lane — the ground's-love line without the META bridge
-- ============================================================================

/-- **The conclusion of C351, and the God-lane's payoff: `AxTwoSubjects` is not
    required for the ground's love.** `the_ground_loves_the_cosmos` is C351 and reaches
    its meaning conjunct through `cosmos_obtains`, which is the row that pays the
    plurality bridge. Re-route the *only* step that pays it through
    `cosmos_presence_model_of_the_act_datum` and the bridge drops out of the footprint
    while the statement is byte-identical.

    The love bridge `Logos.LovesAsGround.AxGroundLovesContingentRealm` and the
    relation `GroundBearsGood` remain, and must: a directional good held by the ground
    is not expressible in Γ's grounding vocabulary, which reaches only undirected
    sufficiency, and the corpus has already recorded that no reading of it is `{}`
    (see `LovesAsGround.lean`'s module note).

    What this row removes is the **whole plurality route** — measured, `AxTwoSubjects`
    *and* the `Will`/`subjectWill` that entered only through it: C351's footprint is
    `{AxGroundLovesContingentRealm, AxTwoSubjects, GroundBearsGood, Means, Subject, Will,
    propext, subjectWill}` and this row's is `{AxGroundLovesContingentRealm,
    GroundBearsGood, Initiates, Means, State, Subject, propext}`. Three axioms and a sort
    fewer, statement byte-identical. That matters for a reader's verdict on the price:
    the interpersonal metaphysics is no longer among the premises of the ground's love,
    and the two remaining premises are independent of it, so it is *visible* as removed
    rather than quietly absorbed.

    **This does not make the conclusion free, and the row is not promoted.** The price
    is relocated to the performative act-datum ◈ `performativeActDatum` (`Tag: TRANS`):
    free in axioms, not free in performance, which is the same account the retorsion
    batch gives for C375/C377. A reader who will not grant that an act occurred
    rejects this row; a reader who rejects `AxTwoSubjects` keeps it.
    Footprint: `{propext, Initiates, Means, State, Subject, AxGroundLovesContingentRealm,
    GroundBearsGood}`. -/
theorem the_ground_loves_the_cosmos_from_the_act_datum
    (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Act s p) :
    ∃ t : Entity, ContingentEntity t ∧ (∃ q, EntityMeans t q) ∧
      ∃ p, GroundBearsGood Entity.ofGround t p := by
  obtain ⟨R⟩ := cosmos_presence_model_of_the_act_datum h
  obtain ⟨q, hq⟩ := R.bears_meaning
  have hc : ContingentEntity R.witness := ⟨R.actual, R.contingent⟩
  exact ⟨R.witness, hc, ⟨q, hq⟩,
    the_ground_bears_a_directional_good_toward_the_cosmos hc ⟨q, hq⟩⟩

-- ============================================================================
-- Section 4: Separations — what the free existence result does not buy
-- ============================================================================

/-- The realm's existence does **not** make it necessary. `poem.txt:26`'s negation stands
    as machine-checked: the actual is not the necessary. **Free since 2026-09-27** — read off
    `contingent_realm_obtains`, so the refutation of the necessity reading never touches the
    meaning-bearing record.
    Footprint: `{propext, Subject}`. -/
theorem realm_existence_does_not_imply_realm_necessity :
    ¬ (∀ t : Entity, ActualEntity t → NecessaryEntity t) := by
  obtain ⟨R⟩ := contingent_realm_obtains
  obtain ⟨w, hw⟩ := R.contingent
  intro hall
  exact hw (hall R.witness R.actual w)

/-- Contingency and necessity are exclusive, so the realm's witness is provably not
    necessary. This is why the realm's existence does not collapse C110: the ground's
    necessity still does not yield the realm's contingency, and the realm's contingency does
    not retrofeed the ground's necessity.
    Footprint: `{Subject}`. -/
theorem contingent_reality_is_not_necessary :
    ∀ t : Entity, ContingentEntity t → ¬ NecessaryEntity t :=
  fun t hc hn => necessary_not_contingent t hn hc

/-- The ground is not a person. The hypostatic identification stays blocked: ledger bridge
    #9 (`Ground(e, personal) → Personal(e)`) is untouched, and the ground is provably no
    subject's correlate regardless of what obtains.

    This is deliberately stated **without** a `CreatedRealm` antecedent. The earlier version
    carried one and then ignored it — the proof never used the hypothesis — so the
    antecedent was decoration that made the theorem look like it constrained the realm.
    Footprint: `{Means, Subject, Will, subjectWill}`. -/
theorem the_ground_is_not_personal : ¬ PersonalEntity Entity.ofGround := by
  rintro ⟨s, hs, _⟩
  exact ofGround_ne_ofSubject s hs

end Logos.CosmicExistence

-- Axiom footprint audit
#print axioms Logos.CosmicExistence.Realm
#print axioms Logos.CosmicExistence.CreatedRealm
#print axioms Logos.CosmicExistence.ContingentRealm
#print axioms Logos.CosmicExistence.ContingentRealmObtains
#print axioms Logos.CosmicExistence.contingent_realm_obtains
#print axioms Logos.CosmicExistence.cosmos_presence_model
#print axioms Logos.CosmicExistence.cosmos_obtains
#print axioms Logos.CosmicExistence.gamma_exhibits_a_meaning_subject
#print axioms Logos.CosmicExistence.PerfectUniverse
#print axioms Logos.CosmicExistence.perfect_universe_actual_is_necessary
#print axioms Logos.CosmicExistence.perfect_universe_has_no_contingent_realm
#print axioms Logos.CosmicExistence.the_cosmos_existence_is_not_refutable
#print axioms Logos.CosmicExistence.a_created_realm_obtains
#print axioms Logos.CosmicExistence.a_contingent_reality_obtains
#print axioms Logos.CosmicExistence.reality_is_not_exhausted_by_the_ground
#print axioms Logos.CosmicExistence.the_realm_bears_meaning
#print axioms Logos.CosmicExistence.the_ground_is_necessary_and_the_realm_is_contingent
#print axioms Logos.CosmicExistence.the_ground_loves_the_cosmos
#print axioms Logos.CosmicExistence.the_ground_loves_the_cosmos_in_a_context
#print axioms Logos.CosmicExistence.realm_existence_does_not_imply_realm_necessity
#print axioms Logos.CosmicExistence.contingent_reality_is_not_necessary
#print axioms Logos.CosmicExistence.the_ground_is_not_personal
