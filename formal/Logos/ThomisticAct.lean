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
`GroundsEntity`.) Acting corresponds to kind, and the two kinds have different vocabularies:

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

import Logos.Core
import Logos.Semantics
import Logos.Entity
import Logos.Agency
import Logos.Value
import Logos.Love
import Logos.LovesAsGround
import Logos.DivineImmutability

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
