import Logos.Agency
import Logos.Core
import Logos.DivineClassicalAttributes
import Logos.DivineTrinitarianAttributes
import Logos.Entity
import Logos.Love
import Logos.Modal
import Logos.Necessity
import Logos.PersonhoodOntologyAudit
import Logos.Plurality
import Logos.RecoveredOntologicalGround
import Logos.Semantics
import Logos.TheologicalModalHardening
import Logos.Value

/-!
================================================================================
DivineThomisticProduction
================================================================================
Consolidated modules:
ThomisticAct, ProductionCountermodel, NecessaryKindAudit, SecondPersonGoodAttempt
================================================================================
-/


/-!
================================================================================
SECTION: ThomisticAct
================================================================================
-/
/-
# Logos.ThomisticAct — to love is to act and to initiate; the ground's love produces

The second half of the succession milestone (`SUCCESSION.md`). Batch S established that Γ's
subject-indexed `Initiates` can say nothing whatever about the ground: the field that seemed to
exclude ground-level action, `NotInSuccession`, is discharged by constructor disjointness
(`Logos.SuccessionAudit`), and the ground's non-agency is **unstatable** rather than refuted — no
entity-level agency relation exists in the vocabulary. This module supplies the vocabulary and the
bridges, at both levels the doctrine needs, and it keeps them apart on purpose.

## The governing distinction: two lanes, never conflated

The operative Thomistic principle is *agere sequitur esse* — action follows being. (`ST I q.2 a.3`;
the corpus's `RecoveredOntologicalGround.lean:57` writes the loose Latin "*esse est agere*" for
`OneEssence`.) Acting corresponds to kind, and the two kinds have different vocabularies:

* a **subject**, whose being is subjecthood, **initiates** — `Initiates : Subject → State → State →
  Prop → Prop` (`Agency.lean:168`), and `Act s p := Means s p ∧ ∃ w w', Initiates s w w' p`;
* the **ground**, whose being is groundhood, **produces** — `Produces : Entity → World → Form → Prop`,
  declared below.

The separation is forced, not stylistic. `Entity.ofGround` is provably not a subject correlate
(`ofGround_ne_ofSubject`), so the ground cannot instantiate `Initiates` at all; and
`Logos.SuccessionCountermodel.a_ground_can_produce_while_outside_succession` (C461) machine-checks
that a production relation and the succession field are compatible **for every interpretation of the
production relation**, because nothing in `NotInSuccession`'s body mentions one. The word "initiate"
was the only thing in tension, and the words were being made to do a job the definitions never gave
them. `DivineImmutability` and C217 are untouched, and `producing_coexists_with_immutability` (C467)
states the two together.

## What is an implication and what is not

"To love is to act" is built as an **implication**, never an identity. `Loves ↔ Act` is false in both
directions and is not what is claimed: acts need not be loving (C455's act is unspecified), and the
slogan lives in the docstrings while the ledger rows carry implications. Conflating the two would
repeat the `CapacityInvariance` vacuity defect (C321) in a new lane.

## Admission tests, run before declaring anything

Per `INHABITED.md` §0, a bridge is admitted as a theorem only if its denial is self-refuting from
nothing; where the denial is merely *refutable* through an alternative, the alternative is what gets
built. Both denials here are **consistent**, so neither bridge is a theorem:

* C464's denial `∃ s t, Loves s t ∧ ∀ p, ¬ Act s p` is satisfied by `BearingOf := fun _ _ =>
  benevolent` together with `Initiates := fun _ _ _ _ => False` — love holds, no act occurs.
* C465's denial `∃ t a, GroundLoves Entity.ofGround t a ∧ ∀ w φ, ¬ Produces Entity.ofGround w φ` is
  satisfied by the present library extended with `Produces := False`: the ground-love theorems
  (C351/C352/C387) do not mention `Produces`, so they all survive.

Both are recorded as tests rather than asserted as necessities, and the prices are declared:
`Tag: VOCAB` for the relation (the `Initiates` precedent, `Agency.lean:164` — it asserts no
connection), `Tag: META` for each bridge (it connects two relations, so `VOCAB` is excluded, and it
is a claim about what love *does* rather than a choice about what love *means*, so `SEM` is excluded).
-/

namespace Logos.ThomisticAct

open Logos.Semantics (World Form)
open Logos.Entity (Entity)
open Logos.Agency (Subject State Initiates Act act_implies_initiates)
open Logos.Love (Loves)
open Logos.LovesAsGround (GroundLoves)
open Logos.DivineImmutability (DivineImmutability ofGround_divine_immutability)

-- ===========================================================================
-- Part I: the vocabulary (C463)
-- ===========================================================================

/--Tag: VOCAB
The entity-level production relation: entity `g` produces form `φ` in world `w`.

 Vocabulary, one level down from `Initiates` and at the other end of the entity/subject divide:
 `Initiates : Subject → State → State → Prop → Prop` is subject-indexed and the ground cannot
 instantiate it (`ofGround_ne_ofSubject`); this relation is entity-indexed and carries no
 subject at all. It is exactly the signature F10 has been asking for — "(1) MISSING
 VOCABULARY — a production relation" (`DivineOmnipotence.lean:55`, `DivineTranscendence.lean:86`).

 `Tag: VOCAB` by the `Initiates` precedent: an uninterpreted relation that asserts no connection.
 It does **not** assert that the ground produces anything; that is the derivation C465 supplies and
 the universal derivation F10 still lacks. Read (1) alone and the ground may still produce nothing.

 Footprint: `{Subject}` — not `{}`, and the reason is the `Entity`-layer floor: `Entity`'s
 `ofSubject` constructor carries a `Subject`, so any entity-indexed relation reaches the `Subject`
 sort. The same reason `FoundationalUnicity.groundsEntity_reflexive` is not `{}`.

 -/
axiom Produces : Entity → World → Form → Prop

-- ===========================================================================
-- Part II: the two bridges (C464, C465)
-- ===========================================================================

/--Tag: META
A loving subject acts: love of another entails some act.

 The subject-level content of "*to love is to act and to initiate*" (`ST I-II q.28`, the will's
 first movement toward the good). `Loves s t` is bearing-level — `Helps s t ∧ ¬ Harms s t`, i.e.
 `BearingOf s t = benevolent ∧ BearingOf s t ≠ harmful` (`Love.lean:49`, `Value.lean:60,64`) — and
 mentions neither `Act` nor `Initiates` nor `Means`; `Act s p` mentions all three. The two lanes
 are joined here and nowhere else.

 `Tag: META`: it connects two relations, so `VOCAB`'s "asserts no connection" rule excludes it, and
 it is a claim about what love *does* rather than a choice about what love *means*, so `SEM` is
 excluded. Lineage: `ST I-II q.28 a.4`.

 **Implication, never identity.** Not `Loves ↔ Act`: acts need not be loving (C455's act carries no
 love witness), and the converse would be a second bridge with no Thomistic text behind it.

 **What it does NOT do.** It does not say the lover initiates — that is C466, a theorem from this
 axiom, so the two halves of the slogan are separately priced. It does not say anything about
 *necessity* or *immutability* of the lover. It does not reach the ground, which is not a subject.
 It does not make love sufficient for any particular act, or for the beloved's benefit.

 Footprint: `{Initiates, Means, State, Subject}` — the four primitives `Act` is built from, which
 the statement mentions. The price of the row is this axiom; the cone it drags in is vocabulary.

 -/
axiom love_implies_act : ∀ s t : Subject, Loves s t → ∃ p : Prop, Act s p

/--Tag: META
The ground's love is efficacious: it produces.

 The ground-level content of "*God causes things by His will*" (`ST I q.19 a.4`). The ground loves
 (`GroundLoves Entity.ofGround t a`, `LovesAsGround.lean:343`) and that love has effects — the
 formal content of the vowels that the ground's love is not merely a disposition.

 **Scoped to `Entity.ofGround`, deliberately.** The general form over `g` would assert production for
 any necessary-kind person-entity standing in the love relation, and
 `LovesAsGround.lean:546-551` records that the necessary quadrant *can* be so populated — which
 would silently cross the blocked necessary-personal-ground frontier (C228). Scoping refuses to
 generalise over the kind. `Tag: META` for C464's reason, one lane over (love → production).

  **The `∃ w φ` is existential and stays so.** The universal production sentence is separately
  declared as C493, not derived from this row: C306 already machine-checks that universal grounding
  entails no causal externality whatever, and C483 shows that C465's existential shape does not entail
  the universal shape. The remaining Creator question is still separate, because production is not
  creation.

 **What it does NOT do.** It does not make the ground an initiator: production is not succession,
 and `NotInSuccession` is untouched by it (C461). It does not identify the ground's producing with
 the ground's being, so it establishes nothing about divine simplicity (`ST I q.3 a.4` needs essence
 vocabulary, Class A, blocked). It does not say the produced form is *good*, or that the ground
 produces every satisfiable form, or that production is creation.

 Footprint: `{GroundBearsGood, Means, NecessarySubjectKind, Produces, Subject}` — the relation it
 introduces, plus the four constants `GroundLoves` and `ActualEntity` reach in their statements.

 -/
axiom ground_love_produces : ∀ t : Entity, ∀ a : Prop, GroundLoves Entity.ofGround t a →
    ∃ w : World, ∃ φ : Form, Produces Entity.ofGround w φ

-- ===========================================================================
-- Part III: the derived rows (C466, C467)
-- ===========================================================================

/-- A loving subject initiates: the "and to initiate" half of the slogan, discharged as a theorem.

 C466 — from C464 by `act_implies_initiates` (`Agency.lean:236`). No new axiom: the word "initiate"
 costs nothing beyond the act-bridge, because `Act` already carries `Initiates` as a conjunct.

 The subject of the initiation is the lover: the witness `s` in C464's conclusion *is* the subject
 that initiates, and the content `p` is the same one. That is the strongest thing this lane can say —
 not that the lover initiates the good, which would need the content of the act to be specified.

 Priced on C464 (`Tag: META`). The honest label is therefore not `PROVEN` but "proved under a declared
 bridge": the reader-facing badge is AXIOMATIC, naming `love_implies_act`.

 Footprint: `{Initiates, Means, State, Subject, love_implies_act}` — C464's cone, and nothing
 else: no new axiom, and the extraction is `obtain`.

 -/
theorem loving_subject_initiates : ∀ s t : Subject, Loves s t →
    ∃ p : Prop, ∃ σ σ' : State, Initiates s σ σ' p := by
  intro s t hLove
  obtain ⟨p, hAct⟩ := love_implies_act s t hLove
  obtain ⟨σ, σ', hInit⟩ := act_implies_initiates hAct
  exact ⟨p, σ, σ', hInit⟩

/-- The ground produces **and** is immutable: the two are proved together, not against each other.

 C467 — the answer to the tension the milestone opened. Batch S found that Γ's exclusion of
 ground-level action was vacuous and that the substantive claim is unstatable; this row states the
 corrected claim and machine-checks that it does not conflict with immutability: the ground's
 producing and `DivineImmutability Entity.ofGround`
 (`DivineImmutability.lean:191-198`, footprint `{Initiates, Means, NecessarySubjectKind, State,
 Subject}`) hold *in the same theory*, with no extra price for their conjunction.

 **The hypothesis is the same love-instance the corpus already pays for** (C351/C352/C387, via
 `the_ground_loves_every_meaningful_contingent_reality` at `LovesAsGround.lean:460`). It cannot be
 discharged here: `GroundLoves Entity.ofGround t a` needs `∃ q, EntityMeans t q` with `t ≠ ofGround`,
 and no atom bears meaning (`EntityMeans (ofAtom _) = False`, `RecoveredOntologicalGround.lean:48-50`),
 while the person-datum route (C367) is not available without a contingent-kind subject, which
 `NecessarySubjectKind` supplies no instance of. So this row is **conditional**, exactly like C387,
  and no unconditional claim about the ground's production is made by this conditional row; the unconditional universal is separately declared as C493.

 That the compatibility is not an artefact of the hypothesis is C461's job: in a free signature a
 ground produces *and* satisfies the succession field, for an arbitrary production relation.

 Footprint: `{GroundBearsGood, Initiates, Means, NecessarySubjectKind, State, Subject, Produces,
 ground_love_produces}` — C465's cone (the hypothesis `GroundLoves` brings `GroundBearsGood`,
 `Means`, `NecessarySubjectKind`) plus the immutability structure's (`Initiates`, `State`).
 `love_implies_act` does **not** occur: the subject lane is not involved.

 -/
theorem producing_coexists_with_immutability {t : Entity} {a : Prop}
    (h : GroundLoves Entity.ofGround t a) :
    DivineImmutability Entity.ofGround ∧ ∃ w : World, ∃ φ : Form, Produces Entity.ofGround w φ :=
  ⟨ofGround_divine_immutability, ground_love_produces t a h⟩

-- ===========================================================================
-- Part IV: the universal derivation (C493)
-- ===========================================================================

/--Tag: META
Universal production by the ground: every satisfiable form is produced somewhere.

  F10's missing derivation (2), declared rather than derived. The denial is consistent:
  C483 exhibits a free-signature interpretation in which the ground produces exactly one of two
  satisfiable forms, while C465's existential shape still holds. The exact universal is therefore
  new substantive content, not a consequence of the declared production relation plus the
  existential love-production bridge.

  `Tag: META`: it connects `Satisfies` and `Produces`, so `VOCAB`'s "asserts no connection" rule
  excludes it; it is a claim about what the ground's production does, not a choice about what
  production or satisfaction *means*, so `SEM` is excluded. It is deliberately scoped to
  `Entity.ofGround`, as C465 is, and it does not identify production with creation: `Produces`
  is not `Creates`, and C110's separation stands.

  Consistency model: extend the present interpretation by taking the ground's production to be
  satisfaction-indexed — for `Entity.ofGround`, produce exactly the satisfiable forms — while
  leaving all other relations and entities untouched. C465's existential conclusion is then a
  consequence of the universal, and C483 remains true as a shape-level independence result about
  an *unconstrained* production relation. The price is one declared metaphysical bridge.

  Footprint: `{Produces, Subject}` plus itself — the production relation it constrains and the
  `Entity`-layer `Subject` floor. No SEM price is removed or added elsewhere.
  -/
axiom ground_produces_every_satisfiable_form :
    ∀ φ : Form, (∃ w : World, Logos.Semantics.Satisfies w φ) →
      ∃ v : World, Produces Entity.ofGround v φ

#print axioms Produces
#print axioms love_implies_act
#print axioms ground_love_produces
#print axioms loving_subject_initiates
#print axioms producing_coexists_with_immutability
#print axioms ground_produces_every_satisfiable_form

end Logos.ThomisticAct


/-!
================================================================================
SECTION: ProductionCountermodel
================================================================================
-/
/-
# Logos.ProductionCountermodel — the ground's production cannot be the causal/creative relation F10 asks for

Companion to the `ACT-CASCADE` batch (`WIN.md` §2 B2) and to `Logos.SuccessionCountermodel`, in the
same free-signature style: a model, not a theorem about Γ's sorts, so that its footprint is `{}`
and it is **not evidence about Γ itself**. What it *is* evidence about is the **shape** of the
missing derivation. Plan of record: `WIN.md`.

## The gap

`DivineOmnipotence.lean` records F10's causal/creative sense as `BLOCKED`, and names its two
missing pieces exactly:

    (1) MISSING VOCABULARY — a production relation, one level down from `Initiates`:
        Produces : Entity → World → Form → Prop
    (2) MISSING DERIVATION — the causal sense, which (1) alone does not give:
        for all g : Entity and all φ : Form,
          (∃ w, Satisfies w φ) → ∃ v, Produces g v φ

Piece (1) was supplied by C463 (`Produces`, `Tag: VOCAB`). What (2) asks for is a
*per-form* relation between satisfiability and production. What C465 (`ground_love_produces`)
delivers is a different statement entirely: given a love-instance, the ground produces **some**
form in **some** world. `∃ w φ, Produces g w φ` is not `∀ φ, (∃ w, Satisfies w φ) → ∃ v,
Produces g v φ`, and nothing in the vocabulary relates them.

**The model below exhibits exactly that gap.** It is a model in which

- the ground produces *something* (C465's conclusion holds), and
- the ground fails to produce a *second satisfiable form* (F10's (2) fails),

  so the two shapes are independent. There is no derivation of (2) from (1) and C465's shape, and
  closing (2) requires a new bridge relating satisfiability to production — which is precisely the
  new substantive content declared as C493 on 2026-09-29. This model remains the proof that the
  bridge was needed; it is not falsified by paying for it.

## Why the counter-interpretation is admissible

`Produces` is a `Tag: VOCAB` axiom. Nothing in the corpus constrains it: it is not monotone, not
functional per form, not total, not grounded in `Satisfies`. The module therefore uses the
interpretation `Produces g w φ := φ = φ₀` — the ground produces one distinguished form and
nothing else. This is *not* a strawman: it is a total, well-defined interpretation of an
unconstrained relation, and `SuccessionCountermodel` uses exactly this device for `Produces`
itself. A row whose conclusion depended on `Produces` being richer than the corpus requires would
be a claim about the axiom, not about Γ's derivability, and would have to be priced.

  **Governed distinction.** The absence of a bridge here is *not* a refutation of F10. F10's former
  `BLOCKED` status is now replaced by the declared C493 bridge, and the corpus's standing note is that (1) alone would not have yielded (2), and
`means_does_not_imply_means_selection` (`HostileSemantics.lean:1861`) already machine-checks that
omni-scope does not entail selection power. What this module buys is that the blockage is now
**settled with its price named** — two named primitives (`Satisfies`, `Produces`) and no bridge
between them — rather than merely asserted in a prose header.
-/

namespace Logos.ProductionCountermodel

/-! ## Part I: the two shapes, over a free signature

`ModelProducesSomething` is the shape of C465's conclusion. `ModelProducesEverySatisfiable` is the
shape of F10's missing derivation (2). They are deliberately stated with no reference to
`GroundLoves`: the countermodel's point is that the *gap between the two shapes* is unbridgeable
without relating the production relation to satisfiability, and the love-hypothesis is not what
would close it. -/

/-- **C465's conclusion, in shape only:** the ground produces *some* form in *some* world.

    Mirrors `ThomisticAct.ground_love_produces` with the love-hypothesis abstracted away, so that
    the countermodel is about the shape of the conclusion and not about Γ's sorts. -/
def ModelProducesSomething (Entity World Form : Type)
    (Produces : Entity → World → Form → Prop) (g : Entity) : Prop :=
  ∃ w : World, ∃ φ : Form, Produces g w φ

/-- **F10's missing derivation (2), in shape only:** every satisfiable form is produced.

    Mirrors `DivineOmnipotence.lean`'s recorded gap, quantifier for quantifier. -/
def ModelProducesEverySatisfiable (Entity World Form : Type)
    (Satisfies : World → Form → Prop)
    (Produces : Entity → World → Form → Prop) (g : Entity) : Prop :=
  ∀ φ : Form, (∃ w : World, Satisfies w φ) → ∃ v : World, Produces g v φ

/-! ## Part II: the countermodel -/

/-- A model in which the ground produces something (C465's shape) but not every satisfiable form
    (F10's shape).

    All four fields are load-bearing, and each blocks a different way of closing the gap:

    - `φ₀_satisfiable` / `φ₁_satisfiable` — the two forms are both *satisfied*, so the failure is
      not "φ₁ is unsatisfiable and F10 does not range over it". This is the field that makes the
      countermodel honest rather than a trick: the antecedent of (2) genuinely holds.
    - `distinct` — φ₁ is a genuinely different form, so the relation is not being asked to produce
      "the same form twice", which would make `φ = φ₀` a non-counterexample.
    - `c465_holds` — C465's conclusion holds. Without this the model would refute (2) in a world
      where the ground produces nothing, which is no tension at all.
    - `f10_fails` — and (2) fails anyway. This is the countermodel. -/
structure ProducesOneFormOnly (Entity World Form : Type)
    (Satisfies : World → Form → Prop)
    (Produces : Entity → World → Form → Prop)
    (g : Entity) (φ₀ φ₁ : Form) : Prop where
  /-- The produced form is satisfiable — the relation is not producing nonsense. -/
  φ₀_satisfiable : ∃ w : World, Satisfies w φ₀
  /-- The unproduced form is satisfiable, so F10's antecedent really holds for it. -/
  φ₁_satisfiable : ∃ w : World, Satisfies w φ₁
  /-- And it is a different form, so (2) is not being trivially satisfied already. -/
  distinct : φ₀ ≠ φ₁
  /-- **C465's shape holds here.** -/
  c465_holds : ModelProducesSomething Entity World Form Produces g
  /-- **F10's shape fails here.** -/
  f10_fails : ¬ ModelProducesEverySatisfiable Entity World Form Satisfies Produces g

/-- **C483 — C465's shape and F10's shape are independent: the ground can produce something
    without producing every satisfiable form.**

    The model, exhibited. `Form := Bool` with `φ₀ := false` and `φ₁ := true`; `World := Unit`;
    `Entity := Unit` with the ground at `()`, so the `g` argument is degenerate and cannot carry
    any of the weight. `Satisfies` is the constant-true relation, so **every** form is satisfiable
    and the antecedent of (2) holds for `true` in particular. `Produces` is
    `φ = false`: total, well-defined, and it produces exactly one form.

    Read against C465 (`ground_love_produces`, `∃ w φ, Produces g w φ` under a love-hypothesis):
    the love-hypothesis, even if Γ could exhibit it, would buy the ground *one* form — because the
    shape of C465's conclusion is an existential, and no amount of satisfying its antecedent turns
    an existential into a universally quantified per-form relation. Read against F10: the
    derivation (2) is not coming from (1) plus C465, and any bridge that would produce it must
    constrain `Produces` in a way nothing in the corpus now does.

    **What this does NOT do.** It does not refute F10. `ModelProducesEverySatisfiable` is a *shape*
    over a free signature; the countermodel shows the two shapes are independent, not that F10 is
    false in Γ. F10 stays `BLOCKED`, and the corpus's own `means_does_not_imply_means_selection`
    (`HostileSemantics.lean:1861`) remains the governing precedent that omni-scope does not entail
    selection power. This row is a `PROVEN` non-entailment result *about the shape*.

    Footprint: `{}`. -/
theorem producing_something_does_not_produce_every_satisfiable_form :
    ∃ (Entity World Form : Type)
      (Satisfies : World → Form → Prop)
      (Produces : Entity → World → Form → Prop)
      (g : Entity) (φ₀ φ₁ : Form),
      ProducesOneFormOnly Entity World Form Satisfies Produces g φ₀ φ₁ := by
  refine ⟨Unit, Unit, Bool, fun _ _ => True, fun _ _ φ => φ = false, (), false, true, ?_⟩
  refine ⟨⟨(), trivial⟩, ⟨(), trivial⟩, by decide, ⟨(), false, rfl⟩, ?_⟩
  rintro h
  obtain ⟨v, hv⟩ := h true ⟨(), trivial⟩
  exact Bool.noConfusion hv

#print axioms producing_something_does_not_produce_every_satisfiable_form

end Logos.ProductionCountermodel


/-!
================================================================================
SECTION: NecessaryKindAudit
================================================================================
-/
/-
# Logos.NecessaryKindAudit — the second necessary being, and the price of the kind vocabulary

`Agency.lean:62` declares `NecessarySubjectKind : Subject → Prop` (`Tag: VOCAB`) and, for a long
time, no theorem in the corpus mentioned it in theorem position at all. It is nonetheless
load-bearing everywhere: `Entity.SubjectExistsAt w s := NecessarySubjectKind s ∨ w = actualWorld`,
so a subject of the necessary kind is **world-rigid by construction** — its entity-correlate
exists in every world, hence is a `NecessaryEntity`.

The kernel already interprets the badge (`Plurality.kinds_are_the_modal_partition`:
`NecessarySubjectKind s ↔ NecessarySubject s`). This module asks the question the interpretation
does not answer: **what does a second necessary being do to the theory?** `Plurality` prices the
*inhabitation* of the necessary kind by the META bridge `necessaryPersonalSubjectExists`
(`∃ s, NecessarySubjectKind s ∧ Person s`). Combined with `ofGround_ne_ofSubject` (a subject's
correlate is provably not the ground), that bridge yields a result no characteristic row in the
corpus records:

- **the necessary being is not unique** — Γ admits an entity that is necessary and provably not
  the ground, so "every property of God is a property of every necessary being" is **refuted**,
  not merely unproved. This is the `ofGround_not_truth_tracking` genre (§14), applied to *ST* I
  q.19 a.4. It is a refutation of a *reading*, resting on one `Tag: META` bridge: reject
  `necessaryPersonalSubjectExists` and the refutation and the grade statement both disappear,
  leaving the question open.
- **necessity is the one characteristic that does not pick the ground out.** The six
  discriminating characteristics each satisfy `∀ e, P e → e = Entity.ofGround` (C439,
  C442–C445, C307 — collected by C446); `NecessaryEntity` does not, and cannot while the
  necessary kind is inhabited: C495 proves `NecessaryEntity` cannot be C446's seventh
  conjunct under that inhabitation.

It also gives the **profile of the second necessary being**: it is necessary and *gaplessly
operative* (it ties the ground there — the reason C443's `universal_ground` field, not
`gapless_operate` alone, is what excludes it from full omnipotence), yet it provably lacks
transcendence, maximal capacity, and pure actuality. The last two are the `SemanticFinitude`
price C445 already pays; nothing new is charged here.

Section 6 (added 2026-09-29) closes the audit **positively**: C515 rules out the necessary atom,
C516 proves the necessary realm is *exhausted* by the ground and the necessary-kind correlates,
and C517 makes the two disjuncts exclusive — the module's final statement is a two-genera
partition, not only a refutation. Those three rows are `PROVEN` and vocabulary-only: the audit
needed no inhabitation axiom to say what the necessary realm *is*, only to say it is *populated*.

**0 new axioms.** The register stays 32. This module only *reads* the kind vocabulary and one
already-declared META bridge; it declares no axioms — its eleven theorems are the only additions.
-/

namespace Logos.NecessaryKindAudit

open Logos.Semantics (World)
open Logos.Necessity (WProp)
open Logos.Entity (Entity EntityOf ExistsAt actualWorld)
open Logos.Agency (Subject Means NecessarySubjectKind)
open Logos.RecoveredOntologicalGround (EntityMeans)
open Logos.Modal (NecessaryEntity)
open Logos.Plurality (NecessarySubject necessaryPersonalSubjectExists)
open Logos.FoundationalUnicity (ofGround_ne_ofSubject)
open Logos.DivineSimplicity (TranscendentGround)
open Logos.FoundationalOmnipresence (MaximalCapacity)
open Logos.SemanticFinitude (GroundTranscendence)
open Logos.DivinePureActuality (DivinePureActuality discriminating_subject_fails_pure_actuality)
open Logos.DivineOmnipotence (GaplessOperate OperatesAt PossibleAt)
open Logos.TheologicalModalHardening (UniversalFrame necessary_not_contingent)
open Logos.LovesAsGround (an_atom_is_contingent)
open Logos.Plurality (kinds_are_the_modal_partition)

-- ============================================================================
-- Section 1 — The lift: a necessary-kind subject's correlate is a necessary entity
-- ============================================================================

/-- **The necessity lift, made explicit.** A subject of the necessary kind is present in every
    world (left disjunct of `SubjectExistsAt`), so its entity-correlate is a `NecessaryEntity`.
    The kernel already contains this as `Plurality.necessaryKindSubject_is_necessary`; it is
    restated here against `NecessaryEntity` (rather than the subject-level `NecessarySubject`)
    so the module reads against one necessity predicate. `Tag: VOCAB` throughout — this is the
    kind distinction being read, not a new claim about it.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem necessary_kind_correlate_is_necessary (s : Subject)
    (hKind : NecessarySubjectKind s) : NecessaryEntity (EntityOf s) := by
  intro w
  exact Or.inl hKind

-- ============================================================================
-- Section 2 — The grade statement: necessity does not single out the ground
-- ============================================================================

/-- **Necessity is not sole-bearer of the ground (C495).** No other characteristic in the corpus
    has this shape: `∀ e, NecessaryEntity e → e = Entity.ofGround` is **false**, because the META
    bridge `necessaryPersonalSubjectExists` inhabits the necessary kind and
    `ofGround_ne_ofSubject` denies that its correlate is the ground. So among the footprint
    characteristics, *necessity is the one that does not pick the ground out* — the honest
    counterpart of the six discriminating results (C439, C442–C445, C307 — collected by C446).
    It proves that `NecessaryEntity` cannot be C446's seventh conjunct while the necessary kind is
    inhabited.

    This is `PROVEN↑` under the META bridge, not a refutation of Γ: it says the ground is not the
    *only* necessary being, not that the ground fails to be necessary (`ofGround_necessary`
    stands). Reject `necessaryPersonalSubjectExists` and this row returns to open.
    Contrast with C489/C490: those are free-signature *countermodels* (`{}`) separating a
    per-kind-subject form from the act-datum without touching Γ, while this row is a *proof inside
    Γ* — the negation is witnessed by the bridge-inhabited necessary kind, so its status is
    `PROVEN↑`, not separation.
    Footprint: `{Means, NecessarySubjectKind, Subject, Will, subjectWill,
      necessaryPersonalSubjectExists}`. -/
theorem necessity_is_not_sole_bearer_of_the_ground :
    ¬ (∀ e : Entity, NecessaryEntity e → e = Entity.ofGround) := by
  intro hSole
  obtain ⟨s, hKind, _hPerson⟩ := necessaryPersonalSubjectExists
  have hNec : NecessaryEntity (EntityOf s) := necessary_kind_correlate_is_necessary s hKind
  have hEq := hSole (EntityOf s) hNec
  exact ofGround_ne_ofSubject s hEq

/-- **The ground is not the only necessary being (C494)** — the refutation of *ST* I q.19 a.4 in
    its extensional reading. The claim that every property of God is shared by every necessary
    being is false: taking `Q := fun e => e = Entity.ofGround`, a necessary-kind subject's
    correlate is a counterexample. This is the `ofGround_not_truth_tracking` genre applied to
    *ST* I q.19 a.4 — a classical reading **refuted**, not merely unproved.

    `PROVEN↑` under the META bridge. It is a refutation of a *reading*, and it rests on one
    declared `Tag: META` inhabitation axiom; it is not a doctrine and not a consistency claim.
    Footprint: `{Means, NecessarySubjectKind, Subject, Will, subjectWill,
      necessaryPersonalSubjectExists}`. -/
theorem the_ground_is_not_the_only_necessary_being :
    ¬ (∀ Q : Entity → Prop, Q Entity.ofGround →
        ∀ e : Entity, NecessaryEntity e → Q e) := by
  intro hShare
  obtain ⟨s, hKind, _hPerson⟩ := necessaryPersonalSubjectExists
  have hNec : NecessaryEntity (EntityOf s) := necessary_kind_correlate_is_necessary s hKind
  have hQ := hShare (fun e => e = Entity.ofGround) rfl (EntityOf s) hNec
  exact ofGround_ne_ofSubject s hQ

-- ============================================================================
-- Section 3 — What the second necessary being lacks
-- ============================================================================

/-- **A necessary-kind subject is not transcendent (C496).** Free in the sense that requires no
    new axiom — `TranscendentGround` is *defined* as "neither an atom nor any subject-correlate"
    (`DivineSimplicity.lean:145-146`), so denying the necessary-kind subject that property is a
    definitional contradiction. The footprint is exactly the two vocabulary axioms the statement
    itself mentions (`NecessarySubjectKind`, `Subject`) — nothing larger. This is the control case:
    it shows the exclusion is not uniformly hard, and that where it *is* paid (below) the price is
    visible.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem necessary_kind_subject_is_not_transcendent (s : Subject)
    (_hKind : NecessarySubjectKind s) :
    ¬ TranscendentGround (EntityOf s) := by
  intro hT
  exact hT.2 s rfl

/-- **A necessary-kind subject is not a maximal-capacity entity (F15).** `MaximalCapacity` is
    `∀ p, EntityMeans e p`; for a subject that is `∀ p, Means s p`, exactly what `SemanticFinitude`
    denies. This is the same `SemanticFinitude` price C445 and C444 pay for the same exclusion;
    nothing new is charged. Footprint: the `SemanticFinitude` bridge plus the vocabulary the
    statement mentions (`Means`, `NecessarySubjectKind`, `Subject`).
    Footprint: `{GroundTranscendence, Means, NecessarySubjectKind, Subject}`. -/
theorem necessary_kind_subject_lacks_maximal_capacity (s : Subject)
    (_hKind : NecessarySubjectKind s) :
    ¬ MaximalCapacity (EntityOf s) := by
  obtain ⟨p, hp⟩ := GroundTranscendence s
  intro hMC
  exact hp (hMC p)

/-- **A necessary-kind subject is not pure actuality (F15).** By the existing
    `discriminating_subject_fails_pure_actuality`: a subject with any content it does not mean has
    passive intentional potency, and the whole necessary kind is subject to `SemanticFinitude`.
    Footprint is shared with that theorem: `SemanticFinitude` plus the four vocabulary axioms
    `DivinePureActuality` itself carries (`Initiates`, `Means`, `State`, `Subject`) and the two of
    this statement (`NecessarySubjectKind`).
    Footprint: `{GroundTranscendence, Initiates, Means, NecessarySubjectKind, State, Subject}`. -/
theorem necessary_kind_subject_fails_pure_actuality (s : Subject)
    (_hKind : NecessarySubjectKind s) :
    ¬ DivinePureActuality (EntityOf s) :=
  discriminating_subject_fails_pure_actuality s (GroundTranscendence s)

-- ============================================================================
-- Section 4 — What the second necessary being has: the operativeness tie
-- ============================================================================

/-- **A necessary-kind subject IS a gapless operator (F15-free, and the honest half of C443).**
    Whoever is present in every world operates everything satisfiable. This is the *forward*
    direction of `DivineOmnipotence.gapless_operators_are_ground_or_necessary_kind` (which is the
    converse) and it is what makes the second necessary being *tie the ground* on operativeness.
    It is precisely why C443's `universal_ground` field — not `gapless_operate` alone — is what
    excludes the necessary-kind subject from full Foundational Omnipotence.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem necessary_kind_subject_is_gapless_operator (s : Subject)
    (hKind : NecessarySubjectKind s) :
    GaplessOperate (UniversalFrame World) OperatesAt (EntityOf s) := by
  intro w P hPoss
  obtain ⟨u, hRw, hPu⟩ := hPoss
  refine ⟨u, hRw, ?_⟩
  exact ⟨Or.inl hKind, hPu⟩

-- ============================================================================
-- Section 5 — The master: the profile of the second necessary being
-- ============================================================================

/-- **The profile of the second necessary being (C497).** For a subject of the necessary kind,
    its entity-correlate:

    - **has** `NecessaryEntity` and `GaplessOperate` — it ties the ground on operativeness;
    - **lacks** `TranscendentGround` (free), `MaximalCapacity` and `DivinePureActuality` (both
      `SemanticFinitude`).

    The combination is the batch's transferable statement: the necessary kind is a *near-ground*
    but is cut off from every discriminating characteristic except operativeness — and there it
    is not cut off at all, which is why the `universal_ground` field exists. The conjunction is a
    new statement about a second necessary being; its cells are the existing vocabulary results.
    Note that "second" is shorthand for "other": the theorem is universal over the kind
    (`∀ s, NecessarySubjectKind s → …`), so it describes *every* non-ground necessary subject's
    correlate, not one particular being.
    Footprint: `{GroundTranscendence, Initiates, Means, NecessarySubjectKind, State, Subject}`. -/
theorem the_second_necessary_being_profile (s : Subject)
    (hKind : NecessarySubjectKind s) :
    NecessaryEntity (EntityOf s) ∧
    GaplessOperate (UniversalFrame World) OperatesAt (EntityOf s) ∧
    ¬ TranscendentGround (EntityOf s) ∧
    ¬ MaximalCapacity (EntityOf s) ∧
    ¬ DivinePureActuality (EntityOf s) :=
  ⟨necessary_kind_correlate_is_necessary s hKind,
   necessary_kind_subject_is_gapless_operator s hKind,
   necessary_kind_subject_is_not_transcendent s hKind,
   necessary_kind_subject_lacks_maximal_capacity s hKind,
   necessary_kind_subject_fails_pure_actuality s hKind⟩

-- ============================================================================
-- Section 6 — The positive closure: the necessary realm has no third shape
-- ============================================================================

/-- **No atom is necessary (C515).** Atoms are contingent (C323, read from `LovesAsGround`) and
    the necessary is never contingent, so no atom — however many, whatever its number — is
    necessary. This is the atom case of the closure below, discharged once and named.
    The footprint is exactly the two vocabulary axioms the statement's own derivation reads,
    plus `propext` (inherited from C323's cone; see GAPMAP's `CL`/raw-grafia note).
    Footprint: `{NecessarySubjectKind, Subject, propext}`. -/
theorem no_necessary_atom (n : Nat) : ¬ NecessaryEntity (Entity.ofAtom n) :=
  fun hNec => necessary_not_contingent _ hNec (an_atom_is_contingent n)

/-- **The necessary is exhausted by the ground and the necessary-kind subjects (C516).**
    Everything necessary is either the ground or a necessary-kind subject's correlate: no
    necessary atom, no necessary matter, no third necessary shape. This is the **positive
    closure** of the audit — C495 showed the ground-only universal is *false*, C496/C497
    profiled the second necessary being, and this row says the second disjunct is not merely
    *a* second necessary being but *all* the rest of the necessary realm.

    Unconditional and free: `PROVEN`, no axiom, no hypothesis beyond `NecessaryEntity e`. The
    subject arm is the partition the kernel already interprets (C410, `.mpr` direction — the
    kernel documents `NecessarySubject s` and `NecessaryEntity (EntityOf s)` as the same
    proposition); the ground arm is `rfl`; the atom arm is C515. Cases analysis on the closed
    `Entity` inductive, the same idiom as C508 (whose row the author filed in the TRINITY
    lote as `C508`; the ids C515–C517 here are the NECESSARY follow-on).

    What it does **not** say: nothing about *who* the ground is, and nothing about inhabiting
    the necessary kind. The first disjunct is read as the ground whatever the reader takes the
    ground to be — a principle, or (per the author's position of 2026-09-29) a Trinity; the
    theorem forces neither reading. Contingent-kind inhabitation remains the open mirror and
    is untouched here.
    Footprint: `{NecessarySubjectKind, Subject, propext}`. -/
theorem necessary_exhaustion (e : Entity) (hNec : NecessaryEntity e) :
    e = Entity.ofGround ∨ ∃ s : Subject, NecessarySubjectKind s ∧ e = EntityOf s := by
  cases e with
  | ofSubject s =>
      exact Or.inr ⟨s, (kinds_are_the_modal_partition s).mpr hNec, rfl⟩
  | ofAtom n => exact False.elim (no_necessary_atom n hNec)
  | ofGround => exact Or.inl rfl

/-- **The necessary realm is the ground and the necessary kind, or nothing (C517).** C516 read
    as a shape statement: the two disjuncts are exclusive (`ofGround_ne_ofSubject`) and the
    ground is not itself a subject's correlate, so the closure is a genuine partition of the
    necessary realm into two genera rather than an overlapping cover. Exclusive, not covering
    twice: nothing is both the ground and a correlate, in either direction.
    Footprint: `{NecessarySubjectKind, Subject, propext}`. -/
theorem necessary_realm_is_two_genera :
    (∀ e : Entity, NecessaryEntity e → e = Entity.ofGround ∨
        (∃ s : Subject, NecessarySubjectKind s ∧ e = EntityOf s)) ∧
    (∀ e : Entity, NecessaryEntity e →
        (e = Entity.ofGround → ∀ s : Subject, e = EntityOf s → False) ∧
        (∀ s : Subject, NecessarySubjectKind s → e = EntityOf s → e ≠ Entity.ofGround)) := by
  refine ⟨necessary_exhaustion, ?_⟩
  intro e _hNec
  constructor
  · intro hGround s hEq
    exact ofGround_ne_ofSubject s (hEq.symm.trans hGround)
  · intro s _hKind hEq hGround
    exact ofGround_ne_ofSubject s (hEq.symm.trans hGround)

-- Axiom footprint audit
#print axioms necessary_kind_correlate_is_necessary
#print axioms necessity_is_not_sole_bearer_of_the_ground
#print axioms no_necessary_atom
#print axioms necessary_exhaustion
#print axioms necessary_realm_is_two_genera
#print axioms the_ground_is_not_the_only_necessary_being
#print axioms necessary_kind_subject_is_not_transcendent
#print axioms necessary_kind_subject_lacks_maximal_capacity
#print axioms necessary_kind_subject_fails_pure_actuality
#print axioms necessary_kind_subject_is_gapless_operator
#print axioms the_second_necessary_being_profile

end Logos.NecessaryKindAudit


/-!
================================================================================
SECTION: SecondPersonGoodAttempt
================================================================================
-/
/-
# Logos.SecondPersonGoodAttempt — a second person does not prove the Good

Machine answer to the author's hypothesis: "If we can prove a second person, we
can prove the Good." The honest attempt delivers two `{}` countermodel witnesses
and a BLOCKED probe:

(1) `lone_will_is_vacuously_individual` (C501) — refutes the personhood-side
retorsion "if a will is individual but there is no one else to be individual
of, how can even a single person exist?". Γ's `IndependentWill` is uniqueness
over the class of *others*; for a lone will the `∀` empties and the conjunct
holds vacuously. A one-subject world whose subject is vacuously an individual
of rational nature with dominion is a legal model, so a single person is not
incoherent. The vacuity is disclosed: the lone will's individuality has NO
contrast content.

(2) `two_persons_do_not_force_good_obtains` (C502) — the plurality-instantiation
reading of C176: two distinct persons (`Unit ⊕ Unit`) can exist while no Good
obtains, because the missing datum is the *bearing value* (opaque
`BearingOf`), never the Other. Distinct persons plus an `unbearing` bearing
layer in every direction is a legal model.

(3) The love-lane probe (C503, BLOCKED, no declaration) — "the ground loves a
person" needs the exact missing lemma
`∃ s : Subject, ContingentSubjectKind s ∧ (∃ q : Prop, Means s q) ∧ Person s`
(WALL 2 instance), WALL 1 (`∃ p, GroundBearsGood Entity.ofGround (EntityOf s) p`),
and an Entity-level → Subject-level projection of the ground's love into
`BearingOf = benevolent` that Γ does not have and this attempt refuses to
force (see plan `OTHER.md`).

No axiom is added; nothing is forced. The moral Good remains PROVEN↑ under the
single disclosed META bridge C177, and C176/C499/C501/C502 are exactly what make
that bridge a disclosed price rather than a hidden premise.
-/

namespace Logos.SecondPersonGoodAttempt

open Logos.PersonhoodOntologyAudit (PersonhoodVocab)
open Logos.PersonhoodOntologyAudit.Vocab
open Logos.Value (InterpersonalBearing)

/-- The lone-will model: a single subject (`Unit`) with a single trivial will
    faculty (`Unit`), meaning everything. Computed, not stipulated. The will is
    `()` and there is no second subject to share it — so every subject is the
    unique owner of its will. A `def`, not an axiom; the counterexample works
    by exhibiting a one-element model. Footprint: `{}`. -/
def LoneWillModel : PersonhoodVocab where
  Subj := Unit
  MeansRel := fun _ _ => True
  WillSort := Unit
  WillOf := fun _ => ()

/-- A lone will is vacuously individual (C501, COUNTERMODEL): there is a
    one-subject world in which that subject owns its will uniquely and is alone.

    Γ's `IndependentWill s := ∀ s' : Subject, s' ≠ s → subjectWill s' ≠
    subjectWill s` quantifies over the class of *others*; for a lone subject that
    class is empty, so the conjunct is vacuously true — exactly how "no one else
    has my fingerprints" is true in a one-person world. The retorsion "if a will
    is individual but there's no one else to be individual of, how can even a
    single person exist?" is therefore answered by vacuity: a single person CAN
    exist, and its individuality is well-formed, true, and content-empty.

    The vacuity caveat (house disclosure pattern, C457/C498): the lone will's
    individuality has NO contrast content — it refutes "a lone person cannot
    exist", not "a lone person is a robust person". Uniqueness is non-sharing;
    it is what GRANTS the "individual" conjunct, not what demands an Other.
    This is the personhood-side twin of the Solitary Universe
    (`AxiomNegationAudit.core_compatible_with_neg_a6`): `will_individuation`
    runs distinctness → will-distinction (it presupposes plurality, never
    generates it — `WillIndividuationAudit`, `{}`), and the corpus has no
    theorem `Person s → ∃ t, t ≠ s`.
    Footprint: `{}`. -/
theorem lone_will_is_vacuously_individual :
    ∃ (M : PersonhoodVocab) (s : M.Subj),
      IndependentWill M s ∧ ∀ t : M.Subj, t = s := by
  refine ⟨LoneWillModel, (), ?_, ?_⟩
  · intro s'
    intro hne
    cases s'
    exact False.elim (hne rfl)
  · intro t
    cases t
    rfl

/-- Two distinct persons do not force the Good (C502, COUNTERMODEL): distinct
    persons can exist while no Good obtains — for any subject vocabulary and
    any propositional act.

    This is the plurality-instantiation reading of C176 (`{}`): `Good`'s
    definiens is `∃ t ≠ s, Person t ∧ Helps s t ∧ ¬ Harms s t` and
    `Helps s t := BearingOf s t = InterpersonalBearing.benevolent` with
    `BearingOf` opaque. In the model below `S := Unit ⊕ Unit`, every
    `P s` holds (two genuine persons), yet every directed bearing is
    `unbearing`, so no pair `s ≠ t` is `benevolent`-joined and the Good never
    obtains. The answer to "if we can prove a second person, we can prove the
    Good" is therefore **no**: the missing datum is the bearing value, not the
    Other — a two-person `unbearing` world is a legal model (the census: no
    theorem or axiom in Γ concludes `BearingOf _ _ = benevolent` except the META
    bridge C177 itself). Free-signature, `{}` — a shape result, not a claim
    about Γ, and not a refutation of C178, which stays PROVEN↑ under C177.
    Footprint: `{}`. -/
theorem two_persons_do_not_force_good_obtains :
    ∃ (S : Type) (P : S → Prop) (B : S → S → InterpersonalBearing),
      (∃ s₁ s₂ : S, s₁ ≠ s₂ ∧ P s₁ ∧ P s₂) ∧
      ¬ ∃ (s : S) (a : Prop),
        ∃ t : S, t ≠ s ∧ P t ∧ B s t = InterpersonalBearing.benevolent ∧
          ¬ (B s t = InterpersonalBearing.harmful) := by
  refine ⟨Unit ⊕ Unit, fun _ => True, fun _ _ => InterpersonalBearing.unbearing, ?_, ?_⟩
  · refine ⟨Sum.inl (), Sum.inr (), ?_, trivial, trivial⟩
    intro h
    cases h
  · rintro ⟨_s, _a, _t, _hne, _hP, hb, _hNotHarmful⟩
    cases hb

end Logos.SecondPersonGoodAttempt

-- ---------------------------------------------------------------------------
-- Axiom footprint audit (expected: `{}` for both witnesses)
-- ---------------------------------------------------------------------------
#print axioms Logos.SecondPersonGoodAttempt.lone_will_is_vacuously_individual
#print axioms Logos.SecondPersonGoodAttempt.two_persons_do_not_force_good_obtains
