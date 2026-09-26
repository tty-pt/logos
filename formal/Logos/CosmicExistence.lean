/-
# Logos.CosmicExistence — the cosmos exists, as an empirical datum

`poem.txt:26-30` asks and answers: "este mundo é necessário? Não.." and then places "a
criação que me parece existir" under a salto de fé. This module makes the *existence* half
of that a **declared empirical datum** while leaving purpose and the incarnation in faith.

## Why it is a datum and not a theorem

The user's reductio is the design constraint: the only deductive route in Γ from *a subject
judges* to *reality obtains* is the reality-hook

    theorem content_reality_hook (p : Prop) : (∃ s : Subject, Correct s p) → p

which is **unconditional in `p`** (`RealityHookAudit.lean:85`). It yields whatever content
anyone judges, so a route through it would equally make "I am necessary" or "Portugal is
necessary" necessary. The hook cannot single out the cosmos. Formalising existence as a
theorem would therefore *manufacture* the very necessity the poem denies.

Nor can the cosmos be identified with anything already in the sort: `Entity` has exactly
three constructors (`Entity.lean:23-26`) and there is no `Cosmos`/`Realm` name in the
library. An atom is contingent already (`an_atom_is_contingent`) but bears no meaning
(`atoms_bear_no_meaning`) and is therefore provably *not* an object of love
(`meaningless_entities_cannot_be_loved`); a subject is the user, not the world; the ground
is `NecessaryEntity`; and `actualWorld` is a `def`. So a **new structure** over a single
witness is the honest move, and it leaves every per-constructor theorem untouched.

## A second correction: the structure must name *one* realm

The first version of this module gave `CreatedRealm` three **independent** existential
fields while its own docstring claimed "something actually obtains, the *same something* is
modal-fragile". The three witnesses could be three different entities, so the module's
conclusion was really "the ground loves *some* contingent entity", not "the ground loves
the cosmos". The structure now carries a single `witness` and every field is about it.

The structure also carries a fourth field, `bears_meaning`. That is not decoration: love
requires the target to bear content (`ground_love_requires_a_meaningful_target`), so
without it the conclusion could never be reached. Its honest consequence is that
satisfiability is **conditional** — see `cosmos_presence_model`.

## What is proven here — and what is deliberately not

- The datum `AxContingentCreationObtains : CreatedRealm` (`Tag: SEM`), with its
  consistency-model note and price.
- **Conditional satisfiability** (`cosmos_presence_model`): the structure is satisfiable
  for any inhabitant of `Means`, the library's primitive content vocabulary. It is *not*
  proved unconditionally, because `Means` (`Agency.lean:74`) has no derivable instance in
  Γ. This is the half of "empirical" that Lean can certify, stated no stronger than it is.
- **Non-triviality of the contingency conjunct's shape**
  (`perfect_universe_has_no_contingent_realm`): in a world-rigid universe, the shape
  `ActualEntity t ∧ ∃ w, ¬ ExistsAt w t` is unsatisfiable. This says the contingent content
  is not forced by world structure — it does **not** speak about Γ, because
  `PerfectUniverse` is an unrelated free structure, not a model of Γ.
- What is **not** claimed, because it is not provable in Lean core: that the *negation* of
  the datum is consistent with all of Γ. That is a model-theoretic statement requiring a
  full interpretation of Γ, and no such model is built here. The honest summary is: the
  datum is **conditionally satisfiable** and its **status is declared** — it was not
  derived, and this module does not pretend otherwise.
- The realm is actual, contingent, **not the ground**, and **bearing content of its own** —
  the machine-checked content of "reality is not exhausted by the necessary ground".
- **The conclusion** `the_ground_loves_the_cosmos`, by applying the declared bridge
  `AxGroundLovesContingentRealm` of `Logos.LovesAsGround` to the realm's contingency and
  content. The footprint names the whole price: the empirical datum, the bridge, the
  content vocabulary, and the world structure.
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
     falsityWorld_ne_actualWorld)

-- ============================================================================
-- Section 1: The datum — one realm, one witness, a declared inhabitation
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
    not carry a data field, so a single witness is only expressible this way. The datum
    itself is the `Prop` `CreatedRealm` below, and that `def` is the audited one. -/
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

/-- **The cosmos exists** — there is a realm of the shape `Realm`. Stated as `Nonempty` so
    the datum is a `Prop` and can be declared as an ordinary axiom, while the record it
    inhabits keeps a single witness.
    Footprint: `{Means, Subject}`. -/
def CreatedRealm : Prop := Nonempty Realm

/--Tag: SEM
Empirical datum: the cosmos exists — a contingent created realm, not the necessary ground,
actually obtains and bears content of its own.

This is a **declared datum, not a theorem**. The user's reductio forces this: the reality
hook is unconditional in its content, so any deductive route to the cosmos's existence
would equally force the judging subject's own claims to be necessary — the outcome the poem
explicitly denies at `poem.txt:26`. Declaring the datum is the honest alternative to
either smuggling the principle of sufficient reason or leaving the question in faith.

The status has direct precedent in the moral pole: `MoralFrontierAudit.Evil` is a declared
`Tag: SEM` datum whose *inhabitation* is what is priced, and `Good` is a fair definition
whose inhabitation is `moral_good_obtains`. Here the *definition* (`CreatedRealm`) is fair
and the *inhabitation* is what this axiom pays for.

Consistency model: the datum introduces no contradiction — `cosmos_presence_model`
inhabits `CreatedRealm` for any inhabitant of `Means` — and its contingency content is
non-trivial, since `perfect_universe_has_no_contingent_realm` refutes its shape in a
world-rigid universe. The datum is not forced by the relying structure, and it is not a
refutation of it either: C110's separation survives untouched. **Not claimed:** that the
negation of the datum is consistent with all of Γ. That is model-theoretic over the whole
theory, is not built here, and is not needed for the datum's declared status.

Philosophical cost: declaring the cosmos's existence a semantic datum commits Γ to there
being something contingent, distinct from the ground, that bears content — a substantive
ontological commitment, not a bookkeeping entry. What is paid is exactly this: Γ's
ontology gains a contingent reality as a *stipulated inhabitant* rather than as a
consequence. A reader who rejects the cost must reject this axiom, and with it
`the_ground_loves_the_cosmos`. The existence half of F9 thereby leaves the faith zone;
purpose and the incarnation do not.
-/
axiom AxContingentCreationObtains : CreatedRealm

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

    **This is not the identification of a subject with the cosmos** — the datum is declared,
    not read off a modelling artifact; the model witnesses only that the structure is
    satisfiable.
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

/-- **A world-rigid universe**, in the `ModalOntologySignature` idiom of
    `TheologicalModalHardening.lean:74-80`. Used as the negative side of the datum's
    consistency story.

    Read the scope carefully: this is an **unrelated free structure, not a model of Γ**. It
    shows that the shape of the datum's contingency field is not forced by world-rigidity
    *in general*; it says nothing about Γ's worlds, on which the datum simply holds. -/
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
    is unsatisfiable there. The contingent content of the datum is therefore not a
    triviality of the world structure.
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

/-- The `CreatedRealm` datum is **not refutable** by the theory: the structure is
    satisfiable, so no theorem of Γ can refute it. This is the half of the datum's
    "empirical" character Lean certifies — it is consistent, and its **status is declared**
    rather than derived. The ambient contingency it appeals to is itself a countermodel
    (`Logos.NecessityEternity.everlasting_but_contingent`), so the contingency content is
    not a triviality of Γ either.
    Footprint: `{Means, Subject, propext}`. -/
theorem the_cosmos_datum_is_not_refutable
    (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Means s p) :
    ¬ (CreatedRealm → False) :=
  fun hh => hh (cosmos_presence_model h)

-- ============================================================================
-- Section 3: What the realm is — and is not — machine-checked
-- ============================================================================

/-- The realm obtains. This is the datum's first face, and the whole of what is claimed
    about existence.
    Footprint: `{AxContingentCreationObtains, Means, Subject}`. -/
theorem a_created_realm_obtains : ∃ t : Entity, ActualEntity t := by
  obtain ⟨R⟩ := AxContingentCreationObtains
  exact ⟨R.witness, R.actual⟩

/-- The realm is contingent. The machine-checked content of the poem's
    "este mundo é necessário? Não".
    Footprint: `{AxContingentCreationObtains, Means, Subject}`. -/
theorem a_contingent_reality_obtains : ∃ t : Entity, ContingentEntity t := by
  obtain ⟨R⟩ := AxContingentCreationObtains
  exact ⟨R.witness, ⟨R.actual, R.contingent⟩⟩

/-- The realm is not the ground. This is the *negative* half of the thesis — the
    machine-checked form of "reality is not exhausted by the ground" — and it is the step
    the deductive route (C110) cannot supply in the other direction.
    Footprint: `{AxContingentCreationObtains, Means, Subject}`. -/
theorem reality_is_not_exhausted_by_the_ground :
    ∃ t : Entity, ActualEntity t ∧ t ≠ Entity.ofGround := by
  obtain ⟨R⟩ := AxContingentCreationObtains
  exact ⟨R.witness, ⟨R.actual, R.not_the_ground⟩⟩

/-- The realm bears content of its own — the fact that makes it a *possible* target of a
    relation that is more than meaning-capacity, and the fact that distinguishes the datum
    from the atom-existence of `a_contingent_entity_exists`.
    Footprint: `{AxContingentCreationObtains, Means, Subject}`. -/
theorem the_realm_bears_meaning : ∃ t : Entity, ∃ q : Prop, EntityMeans t q := by
  obtain ⟨R⟩ := AxContingentCreationObtains
  exact ⟨R.witness, R.bears_meaning⟩

/-- The two poles, side by side: the ground is necessary and the realm is contingent, so
    the realm's existence cannot be read off the ground's necessity. Both halves are
    machine-checked, and together they are the whole content of "not merely a mathematical
    ground" available *before* any love is claimed.
    Footprint: `{AxContingentCreationObtains, Means, Subject}`. -/
theorem the_ground_is_necessary_and_the_realm_is_contingent :
    NecessaryEntity Entity.ofGround ∧ ∃ t : Entity, ContingentEntity t :=
  ⟨ofGround_necessary, a_contingent_reality_obtains⟩

/-- **The conclusion, with both prices visible.** The realm's contingency and content plus
    the declared bridge yield a directional good the ground holds toward the cosmos — "He
    is not merely a mathematical ground, but loves". The footprint names the whole price:
    the empirical datum, the metaphysical bridge, the content vocabulary, and the world
    structure. The claim is about the ground *as a kind*: no hypostatic identification is
    made (`ofGround_ne_ofSubject`).
    Footprint: `{AxContingentCreationObtains, AxGroundLovesContingentRealm, GroundBearsGood, Means, Subject}`. -/
theorem the_ground_loves_the_cosmos :
    ∃ t : Entity, ContingentEntity t ∧ (∃ q, EntityMeans t q) ∧
      ∃ p, GroundBearsGood Entity.ofGround t p := by
  obtain ⟨R⟩ := AxContingentCreationObtains
  obtain ⟨q, hq⟩ := R.bears_meaning
  have hc : ContingentEntity R.witness := ⟨R.actual, R.contingent⟩
  exact ⟨R.witness, hc, ⟨q, hq⟩,
    the_ground_bears_a_directional_good_toward_the_cosmos hc ⟨q, hq⟩⟩

/-- The same conclusion in the library's relational vocabulary: there is a context in which
    the ground's love of the realm holds. Note this is the *relation* `GroundLoves`, not
    interpersonal `Loves` — the two are provably disjoint, and the transfer is unstatable
    rather than merely unproved (`ground_love_cannot_be_read_as_person_love`).
    Footprint: `{AxContingentCreationObtains, AxGroundLovesContingentRealm, GroundBearsGood, Means, Subject}`. -/
theorem the_ground_loves_the_cosmos_in_a_context :
    ∃ t : Entity, ContingentEntity t ∧ ∃ a : Prop, GroundLoves Entity.ofGround t a := by
  obtain ⟨R⟩ := AxContingentCreationObtains
  have hc : ContingentEntity R.witness := ⟨R.actual, R.contingent⟩
  exact ⟨R.witness, hc,
    the_ground_loves_every_meaningful_contingent_reality hc R.bears_meaning⟩

-- ============================================================================
-- Section 4: Separations — what the datum does not buy
-- ============================================================================

/-- The realm's existence does **not** make it necessary. `poem.txt:26`'s negation stands
    as machine-checked: the actual is not the necessary.
    Footprint: `{AxContingentCreationObtains, Means, Subject}`. -/
theorem realm_existence_does_not_imply_realm_necessity :
    ¬ (∀ t : Entity, ActualEntity t → NecessaryEntity t) := by
  obtain ⟨R⟩ := AxContingentCreationObtains
  obtain ⟨w, hw⟩ := R.contingent
  intro hall
  exact hw (hall R.witness R.actual w)

/-- Contingency and necessity are exclusive, so the realm's witness is provably not
    necessary. This is why the datum does not collapse C110: the ground's necessity still
    does not yield the realm's contingency, and the realm's contingency does not retrofeed
    the ground's necessity.
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
#print axioms Logos.CosmicExistence.AxContingentCreationObtains
#print axioms Logos.CosmicExistence.cosmos_presence_model
#print axioms Logos.CosmicExistence.PerfectUniverse
#print axioms Logos.CosmicExistence.perfect_universe_actual_is_necessary
#print axioms Logos.CosmicExistence.perfect_universe_has_no_contingent_realm
#print axioms Logos.CosmicExistence.the_cosmos_datum_is_not_refutable
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
