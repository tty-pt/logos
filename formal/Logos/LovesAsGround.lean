/-
# Logos.LovesAsGround — the ground's love as a distinct, Entity-level relation

The claim that *God is not merely a mathematical ground but loves* needs one thing the
vocabulary does not have. `Loves` is indexed by `Subject`:

    def Loves (s t : Subject) : Prop := Helps s t ∧ ¬ Harms s t   -- Love.lean:49

and the ground is **provably not a `Subject`** (`ofGround_ne_ofSubject`,
`NecessityEternity.lean:155-157`). So "the ground loves" is not well-formed: there is no
`Entity → Entity → Prop` relation anywhere in the library, and every relational predicate
(`Helps`, `Harms`, `Chooses`, `Initiates`, `Grounds`) is `Subject`-indexed.

This module adds the missing relation **without disturbing `Loves`**, and records what it
costs. Design decision: interpersonal love and the ground's love are *kept distinct*
rather than merged, because merging would silently reinterpret `T14` and
`Love.no_contingent_person`.

## A correction: the first version of this module was unsound as advertised

This module previously carried a declared `Tag: META` bridge,
`AxGroundLovesContingentRealm`, and claimed in its own docstring that the inhabitation of
`GroundLoves` was "**not derivable**", that it was "the one substantive commitment of the
module", and that "the axiom is not satisfiable by `True`". **All three claims were
false**, and the defect was invisible to the footprint audit.

The original definition was

    def GroundLoves (g t : Entity) (a : Prop) : Prop :=
      NecessaryEntity g ∧ ActualEntity t ∧ t ≠ g ∧ a

but `NecessaryEntity Entity.ofGround` is *provably trivial* — `ofGround_necessary` closes
by `trivial`, because `EntityExistsAt w .ofGround := True` is a definitional stipulation of
the constructor. So `GroundLoves Entity.ofGround t a` reduced to
`ActualEntity t ∧ t ≠ ofGround ∧ a`, and `a := True` discharged it: the relation was
inhabited for **every** actual entity distinct from the ground, with no content, and the
"price" was zero while being advertised as the module's point.

## Why a primitive is needed, and not merely a fair definition

Stipulating the content conjunctually — say
`NecessaryEntity g ∧ ActualEntity t ∧ t ≠ g ∧ (∃ p, EntityMeans t p ∧ a)` — repairs the
degeneracy, and the separation theorems below then hold. But it does **not** make the
inhabitation a commitment: given a target that is actual, distinct from the ground, and
meaning-bearing, that whole conjunction is provable with `a := True`. The price is again
zero, one level down.

This is the structural reason the price could not be located by stipulation alone. At
`Entity` level the ground is not a `Subject`, there is no entity-indexed content
predicate, and the only necessary entity has trivial meaning-capacity. So *any* first-order
content over `NecessaryEntity`/`ActualEntity`/`EntityMeans` is a function of the target's
own properties, and therefore free.

So the content is a **primitive**, `GroundBearsGood`, exactly as `Means : Subject → Prop →
Prop` is a primitive (`Agency.lean:74`). It is `Tag: VOCAB` — the missing relational
vocabulary — and it constrains nothing, so the inhabitation is a genuine `Tag: META`
commitment. This is the library's own pattern for moral content: `Means` (VOCAB) → `Good`
(fair def) → `AxBenevolentBearingObtains` (META inhabitation). Here no fair definition is
available, so the primitive goes one level deeper.

## Why the bridge is restricted to meaning-bearing targets

The unrestricted bridge `∀ t, ContingentEntity t → ∃ a, GroundLoves Entity.ofGround t a`
is **refutable**, and the module proves it (`meaningful_love_bridge_is_refuted`): an atom is
provably contingent (`an_atom_is_contingent`) and provably meaningless, so the unrestricted
bridge would force an atom to bear meaning. The declared axiom therefore carries the
meaning hypothesis, and the refutation is what justifies the restriction.

## What is proven here

1. **The "merely a mathematical ground" is machine-checked, and it is a *separation*.**
   Grounding reaches *everything*, including an entity that means *nothing at all*
   (`ground_grounds_the_meaningless`); love provably cannot reach it
   (`meaningless_entities_cannot_be_loved`). `grounding_reaches_what_love_cannot` puts the
   two side by side. This is the machine-checked content of "not merely a mathematical
   ground": the two relations differ, and they differ on an entity bearing no meaning.
2. **The inhabitants, at a real price.** `the_ground_loves_every_meaningful_contingent_
   reality` and `the_ground_bears_a_directional_good_toward_the_cosmos` rest on
   `AxGroundLovesContingentRealm`; `the_ground_is_a_liver` adds the existential, and
   `the_ground_is_a_necessary_and_chosen_lover` is the "necessary ∧ chosen" cell of
   `poem.txt:24` with a direction of good in it.
3. **No person can occupy the necessary pole** (`no_subject_is_a_necessary_entity`,
   `only_the_ground_is_necessary`). Note this is **forced by the three-constructor
   ontology** — `EntityExistsAt w .ofGround := True`,
   `SubjectExistsAt w s := w = actualWorld`, atoms fail somewhere — so it is a structural
   fact of the modelling and **not** evidence that the ground loves. Its legitimate
   content is negative: the "necessary ∧ chosen" cell contains no person. The "necessary"
   pole of interpersonal love is handled elsewhere, by T14 / C42–C45, conditionally on
   `PluralityLovePrinciple`.
4. **The two relations are provably disjoint** (`subject_love_is_not_ground_love`,
   `interpersonal_love_never_reaches_the_necessary_quadrant`): `GroundLoves` demands a
   *necessary* lover and no subject is necessary, so `Loves s t` never yields
   `GroundLoves (EntityOf s) _ _`. The transfer the original design asked for is recorded as
   **unstatable, not merely blocked** (`ground_love_cannot_be_read_as_person_love`).
5. **Compatibility with `actus purus`** (`ground_love_preserves_pure_actuality`): the
   ground's love requires no initiation, so `DivinePureActuality` is untouched. Love as
   *act* adds to pure actuality rather than contradicting it (Aquinas, ST I q.20 a.3).

## The price, stated

Two commitments, different in kind:

- `GroundBearsGood` (`Tag: VOCAB`) is **vocabulary**: a primitive relational predicate that
  constrains nothing. It cannot make anything true on its own; it only names what is
  missing. Rejecting it means rejecting the relation's content, not the theory.
- `AxGroundLovesContingentRealm` (`Tag: META`) is the **substance**: it says a necessary
  ground bears a directional good toward every contingent realm that bears content of its
  own. Its consistency model: interpret `GroundBearsGood` everywhere as `False`, which
  satisfies the whole vocabulary, the epistemic reality-hook, and every per-constructor
  theorem of the `Divine*` modules, while every inhabitant theorem below fails. So the
  inhabitation is genuinely not forced by the relying structure.

The `Tag: VOCAB` primitive does not conflict with `ofGround_meansAll`
(`Stipulations.lean:60-61`), which makes `EntityMeans .ofGround p := True`:
`GroundBearsGood` is a *directional* relation about a pair, not a meaning-capacity
judgment, and `GroundLoves` still requires the target to bear content of its own. What is
paid is the admission that the ground's relation to the cosmos is **directed and good**,
where the library's grounding vocabulary can express only undirected sufficiency.
-/

import Logos.Entity
import Logos.Agency
import Logos.Love
import Logos.RecoveredOntologicalGround
import Logos.TheologicalModalHardening
import Logos.NecessityEternity
import Logos.FoundationalOmnipresence
import Logos.DivineImmutability
import Logos.DivinePureActuality

namespace Logos.LovesAsGround

open Logos.Semantics (World TV)
open Logos.Agency (Subject State Initiates)
open Logos.Entity (Entity ExistsAt EntityOf EntityExistsAt SubjectExistsAt actualWorld)
open Logos.RecoveredOntologicalGround (EntityMeans GroundsEntity)
open Logos.Love (Loves)
open Logos.TheologicalModalHardening
    (ActualEntity ContingentEntity NecessaryEntity necessary_not_contingent)
open Logos.NecessityEternity (ofGround_necessary ofGround_ne_ofSubject)
open Logos.FoundationalOmnipresence (UniversalModalGround ofGround_universal_modal_ground)
open Logos.DivineImmutability (TransitionInvariance ofGround_transition_invariance)
open Logos.DivinePureActuality (PassiveTransitionPotency ofGround_no_transition_potency)

-- ============================================================================
-- Section 0: Contingent and meaningful existence (the inhabitation's premises)
-- ============================================================================

/-- The all-`TV.f` valuation is not the actual world, which is all-`TV.t`
    (`Entity.lean:33`). The single witness of modal fragility used throughout this module.
    Footprint: `{propext}`. -/
theorem falsityWorld_ne_actualWorld : (fun _ => TV.f) ≠ actualWorld := by
  intro hc
  have h := congrFun hc 0
  simp [actualWorld] at h

/-- An atom is contingent: actual at the actual world, refuted at the all-`TV.f` world,
    because `EntityExistsAt w (ofAtom n) := w n = TV.t` (`Entity.lean:45-48`).
    Footprint: `{Subject, propext}`. -/
theorem an_atom_is_contingent (n : Nat) : ContingentEntity (Entity.ofAtom n) :=
  ⟨rfl, (fun _ => TV.f), by simp [ExistsAt, EntityExistsAt]⟩

/-- A contingent entity exists, witnessed by an atom. This is the bare *contingency* half
    only. It is **not** the identification of an atom with the cosmos, which
    `investigations/creation.md` and the ledger forbid — and it is explicitly *not* an
    object of love either, since atoms bear no meaning
    (`meaningless_entities_cannot_be_loved`). The cosmos is declared separately, as the
    `CreatedRealm` datum of `Logos.CosmicExistence`.
    Footprint: `{Subject, propext}`. -/
theorem a_contingent_entity_exists : ∃ t : Entity, ContingentEntity t :=
  ⟨Entity.ofAtom 0, an_atom_is_contingent 0⟩

/-- **A contingent entity bearing content exists.** The witness is a subject, whose
    `EntityMeans` unfolds to `Means s p` — a primitive `Tag: VOCAB` **axiom**
    (`Agency.lean:74`). `Means` has no derivable instance in Γ, so this theorem *consumes*
    a `Means` inhabitant rather than producing one: its hypothesis is the honest form of
    that dependency. Note what this does **not** do: it does not identify the subject with
    the cosmos. It supplies only the shape the love inhabitation needs.
    Footprint: `{Means, Subject, propext}`. -/
theorem a_meaningful_contingent_entity_exists
    (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Means s p) :
    ∃ t : Entity, ContingentEntity t ∧ ∃ p, EntityMeans t p := by
  obtain ⟨s, p, hp⟩ := h
  exact ⟨EntityOf s, ⟨rfl, (fun _ => TV.f), falsityWorld_ne_actualWorld⟩, p, hp⟩

-- ============================================================================
-- Section 1: The ground as "merely a mathematical ground", machine-checked
-- ============================================================================

/-- The ground of reality grounds every entity whatsoever: `GroundsEntity` transfers
    meaning, and the ground's meaning-capacity is stipulated to bear all of it.
    Footprint: `{Means, Subject}` (vocabulary-only — the transfer is vacuous, which is
    exactly the point of the next theorem). -/
theorem ground_grounds_every_entity (t : Entity) : GroundsEntity Entity.ofGround t := by
  intro p _hEM
  exact True.intro

/-- An atom bears no meaning at all: `EntityMeans (Entity.ofAtom _) p` reduces to `False`.
    Footprint: `{Means, Subject}` (the match arm alone). -/
theorem atoms_bear_no_meaning (p : Prop) : ¬ EntityMeans (Entity.ofAtom 0) p := by
  intro h
  exact h

/-- The ground grounds even an entity that means nothing whatever. This is the sharpest
    machine-checked sense of "merely a mathematical ground": the ground's relation to
    reality is *undiscriminating* — it holds uniformly, including where there is nothing
    to bear.
    Footprint: `{Means, Subject}`. -/
theorem ground_grounds_the_meaningless :
    GroundsEntity Entity.ofGround (Entity.ofAtom 0) :=
  ground_grounds_every_entity (Entity.ofAtom 0)

/-- Universal modal grounding of the ground, in the library's own form. Retained so the
    contrast with `GroundLoves` is read off a single pair of definitions.
    Footprint: `{Means, Subject}`. -/
theorem the_ground_is_a_universal_modal_ground :
    UniversalModalGround Entity.ofGround :=
  ofGround_universal_modal_ground

/-- No subject is a necessary entity: subjects exist only at the actual world
    (`SubjectExistsAt w s := w = actualWorld`), so a subject fails to exist in every other
    world. This is why no person can occupy the necessary pole.
    Footprint: `{Subject, propext}` (world structure alone). -/
theorem no_subject_is_a_necessary_entity (s : Subject) : ¬ NecessaryEntity (EntityOf s) := by
  intro h
  have hf := h (fun _ => TV.f)
  have hne : (fun _ => TV.f) ≠ actualWorld := falsityWorld_ne_actualWorld
  exact hne hf

/-- The ground is the **unique** necessary entity: every other entity is either a subject
    or an atom, and both are refuted above (atoms fail wherever a value is `TV.f`).

    Read this for what it is. It is **forced by the three-constructor ontology** —
    `EntityExistsAt w .ofGround := True` is a definitional stipulation of the constructor,
    `SubjectExistsAt w s := w = actualWorld`, and atoms are refuted at the all-`TV.f`
    world — so it is a structural fact of the modelling and **not** evidence that the
    ground loves. Its legitimate content is negative: the "necessary ∧ chosen" cell of
    `poem.txt:24` contains no person. The "necessary" pole of love is discharged
    elsewhere, by T14 / C42–C45, conditionally on `PluralityLovePrinciple`.
    Footprint: `{Subject, propext}` (world structure and constructor analysis alone). -/
theorem only_the_ground_is_necessary :
    ∀ e : Entity, NecessaryEntity e → e = Entity.ofGround := by
  intro e h
  cases e with
  | ofSubject s => exact absurd h (no_subject_is_a_necessary_entity s)
  | ofAtom n =>
      have hf := h (fun _ => TV.f)
      simp [ExistsAt, EntityExistsAt] at hf
  | ofGround => rfl

-- ============================================================================
-- Section 2: The missing vocabulary — a primitive directional good
-- ============================================================================

/--Tag: VOCAB
A necessary bearer holds a directional good toward a target, with content `p`.

**Why a primitive and not a fair definition.** The ground's relation to the cosmos is
supposed to be *directional* — good *toward* something — and the library's grounding
vocabulary can express only undirected sufficiency (`GroundsEntity g e := ∀ p,
EntityMeans e p → EntityMeans g p`, which the ground satisfies vacuously, including for an
entity bearing no meaning at all: `ground_grounds_the_meaningless`). The one content
predicate available, `EntityMeans`, is a *capacity* of the target, not an attitude of the
bearer, so it cannot distinguish a bearer that loves from one that merely contains.
`Good s (_a : Prop)` (`MoralFrontierAudit.lean:203-204`) is the right shape but is
`Subject`-indexed, and the ground is provably not a `Subject`. Any first-order definition
over `NecessaryEntity`/`ActualEntity`/`EntityMeans` is therefore a function of the target's
own properties and collapses to a provable conjunction — see the module header for the
concrete instance of that collapse that this module previously shipped by mistake.

Consistency model: the predicate constrains nothing, so it is satisfiable by any
interpretation, including the constant-`False` one under which every inhabitant theorem
below fails. It therefore introduces no inconsistency and forces nothing; it only supplies
the relational shape that the vocabulary lacked.

Philosophical cost: Γ acquires a primitive directed relation at the entity level. This is
new vocabulary, and it is admitted as such — it is *not* reducible to `GroundsEntity`,
whose `∀ p, …` form cannot express a direction. Note it does not conflict with
`ofGround_meansAll` (`Stipulations.lean:60-61`), which fixes the ground's
`EntityMeans` at `True`: `GroundBearsGood` is a relation over a *pair* with a content
argument, not a meaning-capacity judgment. A reader who rejects the cost rejects this
primitive, and with it every inhabitant theorem in Section 3.
-/
axiom GroundBearsGood : Entity → Entity → Prop → Prop

/-- **The ground's love of a target, at a context of evaluation.** The relation says: a
    *necessary* entity bears, directed at this target and at this content, a good the
    target has — the target being actual, other than the lover, and **bearing content of
    its own**.

    The two content-bearing conjuncts are both load-bearing, and the module header records
    why each was added. The `GroundBearsGood` conjunct is what makes the inhabitation a
    real commitment rather than a provable one; the `EntityMeans` conjunct is what makes
    the relation discriminating, and is why love cannot reach the meaningless.

    The `a : Prop` context-of-evaluation argument mirrors `Good s (_a : Prop)`
    (`MoralFrontierAudit.lean:203-204`), the library's existing idiom for a relational
    pole indexed by a context.
    Footprint: `{GroundBearsGood, Means, Subject}`. -/
def GroundLoves (g : Entity) (t : Entity) (a : Prop) : Prop :=
  NecessaryEntity g ∧ ActualEntity t ∧ t ≠ g ∧ (∃ p, GroundBearsGood g t p) ∧
    (∃ q, EntityMeans t q) ∧ a

/-- Ground-level love is eternal in the lover: the lover is necessary. This is one half of
    the formal content of `poem.txt:24`'s "também é necessário" — the other half, that love
    is *chosen*, is the bridge of Section 3, not this conjunct.
    Footprint: `{GroundBearsGood, Means, Subject}`. -/
theorem ground_love_requires_a_necessary_lover {g t : Entity} {a : Prop}
    (h : GroundLoves g t a) : NecessaryEntity g := h.1

/-- Ground-level love is directed at a target distinct from the lover: love is not
    self-regarding. Footprint: `{GroundBearsGood, Means, Subject}`. -/
theorem ground_love_is_directed_at_another {g t : Entity} {a : Prop}
    (h : GroundLoves g t a) : ActualEntity t ∧ t ≠ g := ⟨h.2.1, h.2.2.1⟩

/-- **Ground-level love is content-bearing in the strong sense:** the ground holds some
    directional good *toward* the target. This is the conjunct with no first-order
    substitute, and the one the inhabitation axiom pays for.
    Footprint: `{GroundBearsGood, Means, Subject}`. -/
theorem ground_love_bears_a_directional_good {g t : Entity} {a : Prop}
    (h : GroundLoves g t a) : ∃ p, GroundBearsGood g t p := h.2.2.2.1

/-- **Ground-level love requires the target to bear content of its own:**
    `EntityMeans t q` for some `q`. Since `EntityMeans (ofAtom _) = False` and
    `EntityMeans Entity.ofGround _ = True`, this is what separates love from the ground's
    undiscriminated meaning-capacity.
    Footprint: `{GroundBearsGood, Means, Subject}`. -/
theorem ground_love_requires_a_meaningful_target {g t : Entity} {a : Prop}
    (h : GroundLoves g t a) : ∃ q, EntityMeans t q := h.2.2.2.2.1

/-- **Love cannot reach the meaningless.** A meaningless entity is not loved by the
    ground, in any context. This is the discriminating counterpart of
    `ground_grounds_the_meaningless`: grounding holds there, love does not.
    Footprint: `{GroundBearsGood, Means, Subject}`. -/
theorem meaningless_entities_cannot_be_loved :
    ¬ ∃ a : Prop, GroundLoves Entity.ofGround (Entity.ofAtom 0) a := by
  rintro ⟨a, h⟩
  obtain ⟨q, hq⟩ := h.2.2.2.2.1
  exact atoms_bear_no_meaning q hq

/-- **The separation, in one statement: the ground grounds what it cannot love.** The left
    conjunct is undiscriminated grounding; the right is the failure of love on the very
    same entity. This is the machine-checked content of "not *merely* a mathematical
    ground": the two relations differ, and they differ on an entity bearing no meaning.
    Footprint: `{GroundBearsGood, Means, Subject}`. -/
theorem grounding_reaches_what_love_cannot :
    GroundsEntity Entity.ofGround (Entity.ofAtom 0) ∧
      ¬ ∃ a : Prop, GroundLoves Entity.ofGround (Entity.ofAtom 0) a :=
  ⟨ground_grounds_the_meaningless, meaningless_entities_cannot_be_loved⟩

/-- Grounding is total over entities while love is not: every entity is grounded, and not
    every contingent entity is loved.
    Footprint: `{GroundBearsGood, Means, Subject, propext}`. -/
theorem grounding_is_total_but_love_is_not :
    (∀ t : Entity, GroundsEntity Entity.ofGround t) ∧
      ¬ (∀ t : Entity, ContingentEntity t → ∃ a : Prop, GroundLoves Entity.ofGround t a) := by
  refine ⟨ground_grounds_every_entity, ?_⟩
  rintro hall
  obtain ⟨a, ha⟩ := hall (Entity.ofAtom 0) (an_atom_is_contingent 0)
  obtain ⟨q, hq⟩ := ha.2.2.2.2.1
  exact atoms_bear_no_meaning q hq

-- ============================================================================
-- Section 3: The inhabitation — one declared, priced bridge
-- ============================================================================

/-- **Why the bridge carries a meaning hypothesis.** The unrestricted form
    `∀ t, ContingentEntity t → ∃ a, GroundLoves Entity.ofGround t a` is refutable in Γ: an
    atom is provably contingent and provably meaningless, so it would force an atom to bear
    meaning. This theorem is the machine-checked reason the axiom below is stated over
    meaning-bearing targets only, and it is why this module does not claim the stronger,
    more attractive, and false statement.
    Footprint: `{GroundBearsGood, Means, Subject, propext}`. -/
theorem meaningful_love_bridge_is_refuted :
    ¬ (∀ t : Entity, ContingentEntity t → ∃ a : Prop, GroundLoves Entity.ofGround t a) :=
  fun hall => grounding_is_total_but_love_is_not.2 hall

/--Tag: META
The Ground of Reality bears a directional good toward every contingent realm that bears
content of its own.

The inhabitation of `GroundLoves` is **not derivable**, and this is the module's single
substantive commitment. The primitive `GroundBearsGood` is what makes that true: it
constrains nothing, so no theorem of the vocabulary establishes that a necessary bearer
holds any good toward any target. Nor can the content be read off the existing relations —
universal modal grounding is satisfied *vacuously* by the ground for every entity,
including entities bearing no meaning at all (`ground_grounds_the_meaningless`), so
grounding carries no directed content from which love could follow. The bridge therefore
has to postulate, in the shape of `AxBenevolentBearingObtains` (C177) and
`AxSecondPersonalAddress` (C117): disclosed, priced, with the negative side separated below.

Consistency model: the bridge is not forced by the relying structure. Interpreting
`GroundBearsGood` as `False` everywhere satisfies the whole of the vocabulary, the
epistemic reality-hook and every per-constructor theorem of the `Divine*` modules, while
every inhabitant theorem of this section fails. Conversely the inhabitation is not a
triviality: it is not satisfied by `True`, since the target must be actual, distinct from
the lover, and meaningful, and the good must be directional.

Philosophical cost: declaring the ground a lover is a substantive metaphysical bridge. The
price is that Γ acquires a directed relation at the ground that is **not reducible to its
stipulated meaning-capacity**, and a primitive predicate to say so. The stipulation
`ofGround_meansAll` (`Stipulations.lean:60-61`) makes the ground's `EntityMeans`
undiscriminated (`True`); `GroundBearsGood` is a relation over a *pair* with a content
argument, so the `DivineOmniscience` face `ofGround_truth_exhaustive` stays consistent with
this bridge precisely because it is not a `Means` judgment. What is paid is the admission
that the ground's relation to the cosmos is **directed and good**, where the library's
grounding vocabulary can express only undirected sufficiency. A reader who rejects the
price must reject this axiom, and with it `the_ground_is_a_liver`.
-/
axiom AxGroundLovesContingentRealm :
  ∀ t : Entity, ContingentEntity t → (∃ q, EntityMeans t q) →
    ∃ a : Prop, GroundLoves Entity.ofGround t a

/-- The bridge, applied: the ground loves every contingent created reality that bears
    content of its own.
    Footprint: `{AxGroundLovesContingentRealm, GroundBearsGood, Means, Subject}`. -/
theorem the_ground_loves_every_meaningful_contingent_reality {t : Entity}
    (h : ContingentEntity t) (hm : ∃ q, EntityMeans t q) :
    ∃ a : Prop, GroundLoves Entity.ofGround t a :=
  AxGroundLovesContingentRealm t h hm

/-- **The content of the claim, unwrapped:** a directional good is held toward the realm.
    This is the least an inhabitant theorem can say, and it is where the whole price of the
    module sits — a `{}` reading of "the ground loves" would be a different, much weaker
    claim about meaning-capacity.
    Footprint: `{AxGroundLovesContingentRealm, GroundBearsGood, Means, Subject}`. -/
theorem the_ground_bears_a_directional_good_toward_the_cosmos {t : Entity}
    (h : ContingentEntity t) (hm : ∃ q, EntityMeans t q) :
    ∃ p, GroundBearsGood Entity.ofGround t p := by
  obtain ⟨a, ha⟩ := the_ground_loves_every_meaningful_contingent_reality h hm
  exact ha.2.2.2.1

/-- **The inhabitants, with the price visible.** There exists a contingent entity bearing
    content which the ground loves, and toward which it holds a directional good. The
    `Means` hypothesis is the library's primitive content vocabulary being inhabited, which
    the caller obtains from its own datum (`Logos.CosmicExistence.CreatedRealm.bears_
    meaning`); nothing here identifies that subject with the cosmos.
    Footprint: `{AxGroundLovesContingentRealm, GroundBearsGood, Means, Subject, propext}`. -/
theorem the_ground_is_a_liver
    (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Means s p) :
    ∃ t : Entity, ContingentEntity t ∧ (∃ q, EntityMeans t q) ∧
      ∃ p, GroundBearsGood Entity.ofGround t p := by
  obtain ⟨t, hc, hq⟩ := a_meaningful_contingent_entity_exists h
  exact ⟨t, hc, hq, the_ground_bears_a_directional_good_toward_the_cosmos hc hq⟩

/-- **The "necessary ∧ chosen" cell, occupied.** The ground is a necessary entity and holds
    a chosen directional good toward a contingent realm that bears content — the machine
    form of `poem.txt:24`'s "Amar é escolhido e também é necessário", with the necessity in
    the lover and the choice in the bridge. This is the module's conclusion, and its
    footprint names the whole price: the content vocabulary, the bridge, and the world's
    structure. No axiom of *free choice* is hidden here — the choice is exactly what
    `AxGroundLovesContingentRealm` declares.
    Footprint: `{AxGroundLovesContingentRealm, GroundBearsGood, Means, Subject, propext}`. -/
theorem the_ground_is_a_necessary_and_chosen_lover
    (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Means s p) :
    NecessaryEntity Entity.ofGround ∧
      ∃ t : Entity, ContingentEntity t ∧ (∃ q, EntityMeans t q) ∧
        ∃ p, GroundBearsGood Entity.ofGround t p :=
  ⟨ofGround_necessary, the_ground_is_a_liver h⟩

-- ============================================================================
-- Section 4: Ground-level love and interpersonal love are distinct
-- ============================================================================

/-- The ground is not a personal entity: no subject is its correlate. So the conclusion
    attributes love to the ground **as a kind** and smuggles in no hypostatic
    identification — the open ledger bridge #9 (`Ground(e, personal) → Personal(e)`) is
    untouched by it.
    Footprint: `{Subject}`. -/
theorem the_ground_is_not_a_person :
    ∀ s : Subject, Entity.ofGround ≠ EntityOf s :=
  ofGround_ne_ofSubject

/-- The separation, in one statement: the inhabitation cannot be read as a claim about a
    person. If someone were to identify the ground with a subject, the identification
    itself fails, so no route from the ground's love to a created person exists here.
    Footprint: `{Subject}`. -/
theorem ground_love_does_not_identify_a_person :
    ¬ ∃ s : Subject, Entity.ofGround = EntityOf s := by
  rintro ⟨s, h⟩
  exact ofGround_ne_ofSubject s h

/-- **Interpersonal love never yields ground-level love.** `GroundLoves` demands a
    *necessary* lover and no subject is necessary, so `Loves s t` cannot give
    `GroundLoves (EntityOf s) _ _`. The two relations are provably disjoint.
    Footprint: `{GroundBearsGood, Means, Subject, propext}`. -/
theorem subject_love_is_not_ground_love (s t : Subject) (a : Prop) (_h : Loves s t) :
    ¬ GroundLoves (EntityOf s) (EntityOf t) a :=
  fun hh => no_subject_is_a_necessary_entity s hh.1

/-- The failure holds for *every* subject and *every* love relation, so no amount of
    interpersonal love can populate the necessary quadrant. This is the negative half of
    the transfer the original design asked for.
    Footprint: `{Subject, propext}`. -/
theorem interpersonal_love_never_reaches_the_necessary_quadrant :
    ¬ ∃ s t : Subject, Loves s t ∧ NecessaryEntity (EntityOf s) := by
  rintro ⟨s, _t, _, hn⟩
  exact no_subject_is_a_necessary_entity s hn

/-- **The transfer to interpersonal love is unstatable, not merely blocked.** The design
    originally asked for `GroundLoves → Loves` on the subject side. There is no such
    statement: `Loves` is `Subject`-indexed, the ground is provably no subject, and the
    target of a `GroundLoves` claim is an arbitrary `Entity` rather than a `Subject`. The
    only route would be a hypostatic identification, which the two theorems above refute.
    Footprint: `{GroundBearsGood, Means, Subject, propext}`. -/
theorem ground_love_cannot_be_read_as_person_love :
    ¬ (∃ s : Subject, Entity.ofGround = EntityOf s) ∧
      ∀ s t : Subject, Loves s t → ¬ GroundLoves (EntityOf s) (EntityOf t) True :=
  ⟨ground_love_does_not_identify_a_person,
    fun s t h => subject_love_is_not_ground_love s t True h⟩

/-- Pure actuality is preserved: the ground's love requires no initiation, so
    `DivinePureActuality`'s zero-transition-potency field is untouched. Attributing an
    *act* of love to the ground adds to `ofGround_divine_pure_actuality` rather than
    contradicting it — pure actuality excludes passive potency, not act.
    Footprint: `{GroundBearsGood, Initiates, Means, State, Subject}`. -/
theorem ground_love_preserves_pure_actuality {t : Entity} {a : Prop}
    (_h : GroundLoves Entity.ofGround t a) : ¬ PassiveTransitionPotency Entity.ofGround :=
  ofGround_no_transition_potency

end Logos.LovesAsGround

-- Axiom footprint audit
#print axioms Logos.LovesAsGround.falsityWorld_ne_actualWorld
#print axioms Logos.LovesAsGround.an_atom_is_contingent
#print axioms Logos.LovesAsGround.a_contingent_entity_exists
#print axioms Logos.LovesAsGround.a_meaningful_contingent_entity_exists
#print axioms Logos.LovesAsGround.ground_grounds_every_entity
#print axioms Logos.LovesAsGround.atoms_bear_no_meaning
#print axioms Logos.LovesAsGround.ground_grounds_the_meaningless
#print axioms Logos.LovesAsGround.the_ground_is_a_universal_modal_ground
#print axioms Logos.LovesAsGround.no_subject_is_a_necessary_entity
#print axioms Logos.LovesAsGround.only_the_ground_is_necessary
#print axioms Logos.LovesAsGround.GroundBearsGood
#print axioms Logos.LovesAsGround.GroundLoves
#print axioms Logos.LovesAsGround.ground_love_requires_a_necessary_lover
#print axioms Logos.LovesAsGround.ground_love_is_directed_at_another
#print axioms Logos.LovesAsGround.ground_love_bears_a_directional_good
#print axioms Logos.LovesAsGround.ground_love_requires_a_meaningful_target
#print axioms Logos.LovesAsGround.meaningless_entities_cannot_be_loved
#print axioms Logos.LovesAsGround.grounding_reaches_what_love_cannot
#print axioms Logos.LovesAsGround.grounding_is_total_but_love_is_not
#print axioms Logos.LovesAsGround.meaningful_love_bridge_is_refuted
#print axioms Logos.LovesAsGround.the_ground_loves_every_meaningful_contingent_reality
#print axioms Logos.LovesAsGround.the_ground_bears_a_directional_good_toward_the_cosmos
#print axioms Logos.LovesAsGround.the_ground_is_a_liver
#print axioms Logos.LovesAsGround.the_ground_is_a_necessary_and_chosen_lover
#print axioms Logos.LovesAsGround.the_ground_is_not_a_person
#print axioms Logos.LovesAsGround.ground_love_does_not_identify_a_person
#print axioms Logos.LovesAsGround.subject_love_is_not_ground_love
#print axioms Logos.LovesAsGround.interpersonal_love_never_reaches_the_necessary_quadrant
#print axioms Logos.LovesAsGround.ground_love_cannot_be_read_as_person_love
#print axioms Logos.LovesAsGround.ground_love_preserves_pure_actuality
