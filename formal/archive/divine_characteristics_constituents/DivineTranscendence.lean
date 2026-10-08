/-
# Logos.DivineTranscendence — Classical Divine Transcendence and the Four Senses of Externality

This module formalizes the characteristic of **Transcendence and externality**
(the ground is not exhausted by membership in any formal or evaluative system;
`CHARACTERISTICS.md` §1; `CHARS.md` §4.1) for the necessary Ground of Reality
(`Entity.ofGround`).

### This is a boundary batch, not a "prove transcendence" batch

`CHARACTERISTICS.md:36` is explicit about what is missing: *"no live theorem
establishes a foundation external/transcendent to every system."* The word is
**system**. The **ontological** sense of transcendence is already delivered in the
corpus and is **cited here, never re-proved**:

- **C195** `DivineSimplicity.ofGround_transcendent` (`DivineSimplicity.lean:151`),
  footprint `{Subject}`: `Entity.ofGround` is neither `Entity.ofAtom n` for any
  `n` nor `EntityOf s` for any `Subject s`;
- **C213** `FoundationalUnicity.unicity_strictly_transcends_world`
  (`FoundationalUnicity.lean:200`) merely restates C195 — its proof *is*
  `ofGround_transcendent`;
- **C196** `DivineSimplicity.ofGround_divine_simplicity` is already the master
  synthesis for this same ground.

What no live theorem establishes is the **logical** sense, and the reason is an
inferential gap the prose itself names: *"The passage from 'each system needs
something outside itself' to 'one foundation is external to every system' is
asserted but not shown"* (`CHARACTERISTICS.md:64`). The ledger had to retire the
corresponding routes as **C78/C79/C88** (`CHARS.md:142`), the last being
`Modal.transcendental_quantifier_swap`, retired as *"manufactured origin
quantifier swap destroyed"*. **C301 is the machine-checked justification of that
retirement.** It was asserted; here it is proved.

### The design decision `CHARS.md:144` demands, now taken

The prose never defines its own key term — *"External is not defined. It shifts
among logical, ontological, hierarchical, and possibly causal senses"*
(`CHARACTERISTICS.md:63`) — and `CHARS.md:144` requires: *"define whether
externality is logical, ontological, causal, or hierarchical. Do not encode all
four under one name."* So this module **defines four senses separately** and gives
each its own verdict. There is deliberately **no umbrella predicate** here: a
single `Transcendence` would silently pick one sense and hide the other three.

| Sense | Verdict | Claims |
|---|---|---|
| ontological | **already PROVEN** (C195) — nothing added, cited only | — |
| logical (system-externality) | **inference refuted**, conclusion undelivered | C301, C302, C303 |
| hierarchical | **separation shown**: externality ⇏ ungroundedness | C304, C305 |
| causal | **separation shown**: universal grounding ⇏ causal externality | C306 |
| diagonal (GTT shape) | **consistent in both directions**; yields no forced foundation | C308 |

The one new **PROVEN** result is **C307**: the ground is the **sole** entity in
the Γ inventory satisfying `TranscendentGround`. No ledger row said this; C195
says the ground *is* transcendent, C213 repeats it.

### The honest boundary, machine-checked

- **The conclusion is affirmed as consistent, not destroyed.** C301 refutes an
  *inference*; C302 exhibits a model in which the conclusion ("some point is
  outside every system") is *true*, so C301 bounds a real claim rather than a
  fiction. Refuting a route is not refuting a thesis.
- **The route dies at the quantifier swap.** `∀ σ, ∃ e, ¬ In σ e` does not give
  `∃ e, ∀ σ, ¬ In σ e`; the outsides need not coalesce (C301). C303 makes the
  failure concrete at `Entity.ofGround`: the ground really does ground all actual
  reality (`ofGround_ground_of_reality`, `NecessityEternity.lean:140`, reused
  verbatim), and it is nonetheless **inside** an ordinary membership class.
- **No `System` sort exists, so the senses are stated generically.** Γ's only
  evaluator vocabulary is `ProofPresentationRetorsion.{Derivation, conclusion,
  Checker, DerivationSound}` (`ProofPresentationRetorsion.lean:73,79,84`) and it
  is **subject**-indexed, while `Entity.ofGround` is provably not a subject
  correlate (`ofGround_ne_ofSubject`, `NecessityEternity.lean:160`). There is no
  canonical system to be external to; the Γ-specific content is the inference
  failure, and the predicates are abstract over a membership relation.
- **The causal sense has no Γ-side statement to instantiate.** Γ declares no
  production relation: the only initiation relation is
  `Agency.Initiates : Subject → State → State → Prop → Prop`
  (`Agency.lean:168`), a declared VOCAB axiom, and it is subject-indexed;
  `OneEssence` (`RecoveredOntologicalGround.lean:57`) is explanatory
  containment (*esse est agere*), not production. C306 is therefore stated over
  an abstract causal relation. The missing statements are recorded here without
  the `axiom`/`def` keywords on purpose — a line starting with `axiom` inside
  this header is parsed as a real axiom declaration by `depviz` and by
  `scripts/build_deduction.py`, which would register a phantom axiom:

      (1) MISSING VOCABULARY — a production relation, one level down from `Initiates`:
          Produces : Entity → World → Form → Prop
      (2) MISSING DERIVATION — the causal sense, which (1) alone does not give:
          for all g : Entity and all phi : Form,
            (exists w, Satisfies w phi) -> exists v, Produces g v phi

  Note that (1) alone would not give (2): C306 already machine-checks that
  universal grounding entails no causal externality whatever.
- **Aseity is out of scope, deliberately.** `TranscendentGround` is a pair of
  non-identity clauses and says nothing about grounding, so `CanonicalAseity` is
  an independent predicate; it is also not provable of the ground without the
  finite-subjectivity premise (compare
  `CanonicalAseity.lean:163`, `unconditional_aseity_independent_of_bare_agency`,
  an explicit countermodel against unconditional aseity). Since this
  characteristic does not ask for aseity, that premise never enters here, and
  the master synthesis of C195/C196 is left where it already stands.
- **The Gödel/Tarski/Turing diagonal: the shape is formalized, the theorem is not.**
  An earlier draft of this header dismissed the diagonal on the grounds that
  "self-application of a predicate is impredicative and is not expressible in Lean
  4's `Prop`". **That was wrong, and is retracted here.** Self-application is
  perfectly expressible; the real obstacle is different, and the corpus already
  contains the formalized part. `Logos.NegativeRetorsionAudit` defines, at
  `NegativeRetorsionAudit.lean:515`,

      DiagonalSpec (Subject : Type) (Means : Subject → Prop → Prop)
        D : Prop
        spec : D <-> not (exists s : Subject, Means s D)

  — the self-referential proposition "this very proposition is not entertained by
  any subject", i.e. **system-externality instantiated in Γ's own vocabulary**.
  Its four consequences (`:521`, `:530`, `:538`, `:560`) are all `{}`, and the
  module's own analysis at `:506-511` records the result: **the diagonal is
  NEVER paradoxical**, in both directions — consistent as true-and-unmeant and as
  false-and-meant. So the diagonal yields no contradiction and therefore no
  forced foundation.

  What remains unformalized is Gödel's *theorem*, and the reason is a
  **missing-vocabulary** gap, not a missing-effort one: it needs a coding of
  formulas (`Code`), a syntactic `Subst`, a `Diag`, and an internal truth
  predicate `Truth : Form -> Prop` closed under it. Γ declares none of these;
  `Form`, `Satisfies` and `NecessarilyTrue` (`Semantics.lean:22,44,58`) are
  meta-level, and there is no `Form -> Prop` truth predicate anywhere in
  `Logos/`. Adding one would move the declared-axiom register, which this batch's
  invariance test forbids. That obligation is recorded as frontier row **F14**
  with its missing lemma named, and `base.txt:219` already records the liar
  paradox as blocked for the independent reason that no self-referential
  proposition is assumed. Section 7 prices what the diagonal does *not* deliver.
-/

import Logos.Core
import Logos.Semantics
import Logos.Entity
import Logos.Modal
import Logos.Agency
import Logos.RecoveredOntologicalGround
import Logos.NecessityEternity
import Logos.CanonicalAseity
import Logos.DivineSimplicity
import Logos.NegativeRetorsionAudit

namespace Logos.DivineTranscendence

open Logos.Semantics (Form World Satisfies)
open Logos.Entity (Entity EntityOf ExistsAt)
open Logos.Modal (NecessaryEntity)
open Logos.Agency (Subject)
open Logos.RecoveredOntologicalGround
    (OneEssence GroundOfReality ActualEntity)
open Logos.NecessityEternity (ofGround_ground_of_reality)
open Logos.CanonicalAseity (ExternalGrounding CanonicalAseity)
open Logos.DivineSimplicity (TranscendentGround ofGround_transcendent)
open Logos.NegativeRetorsionAudit (DiagonalSpec)

-- ============================================================================
-- Section 1: Vocabulary — Four Senses, Four Names, No Umbrella
-- ============================================================================

/-- Logical externality: the entity stands outside every system in a family of
    systems — no member-relation of the family contains it.
    Footprint: `{Subject}`. -/
def OutsideEverySystem (S : Type) (In : S → Entity → Prop) (e : Entity) : Prop :=
  ∀ σ : S, ¬ In σ e

/-- The prose's step 1 to step 2 premise, in its weakest form: every system has
    *some* outside point. This says nothing about whether those points coincide,
    and that gap is exactly what C301 machine-checks.
    Footprint: `{Subject}`. -/
def EachSystemHasAnOutside (S : Type) (In : S → Entity → Prop) : Prop :=
  ∀ σ : S, ∃ e : Entity, ¬ In σ e

/-- Within-system grounding: `e` is grounded by a member `g` of some `σ`.
    Footprint: `{Subject}`. -/
def GroundedInSystem (S : Type) (In : S → Entity → Prop)
    (Gr : S → Entity → Entity → Prop) (e : Entity) : Prop :=
  ∃ σ : S, ∃ g : Entity, In σ g ∧ Gr σ g e

/-- Hierarchical externality: outside every system **and** grounded in none of
    them. Strictly stronger than `OutsideEverySystem`; C304 machine-checks that
    the two come apart.
    Footprint: `{Subject}`. -/
def HierarchicalExternality (S : Type) (In : S → Entity → Prop)
    (Gr : S → Entity → Entity → Prop) (e : Entity) : Prop :=
  (∀ σ : S, ¬ In σ e) ∧ ¬ GroundedInSystem S In Gr e

/-- Causal externality: no entity in any causal order produces `e`. Stated over
    an abstract causal relation because Γ declares no production relation.
    Footprint: `{Subject}`. -/
def CausalExternality (S : Type) (Caus : S → Entity → Entity → Prop)
    (e : Entity) : Prop :=
  ∀ σ : S, ∀ g : Entity, ¬ Caus σ g e

-- ============================================================================
-- Section 2: The Logical Sense — the Quantifier Swap and Its Two Halves
-- ============================================================================

/-- The quantifier-swap countermodel, and the load-bearing result of this batch:
    "every system has an outside point" does **not** yield "some point is outside
    every system". Witness: two complementary systems — the first contains every
    entity except the ground, the second contains only the ground. Each system
    therefore has an outside (each misses something), yet every entity lies in
    some system, so no point is outside them all. This is the machine-checked
    justification for the retirement of C88
    `transcendental_quantifier_swap`, which had asserted the destruction without
    exhibiting it. Footprint: `{Subject}`. -/
theorem per_system_outside_points_need_not_coalesce :
    ∃ (S : Type) (In : S → Entity → Prop),
      EachSystemHasAnOutside S In ∧ ¬ (∃ e : Entity, OutsideEverySystem S In e) := by
  refine ⟨Bool, fun σ e => match σ with
                          | true => e ≠ Entity.ofGround
                          | false => e = Entity.ofGround, ?_, ?_⟩
  · intro σ
    cases σ with
    | true => exact ⟨Entity.ofGround, fun h => h rfl⟩
    | false => exact ⟨Entity.ofAtom 0, fun h => Entity.noConfusion h⟩
  · intro h
    obtain ⟨e, he⟩ := h
    cases e with
    | ofGround => exact he false rfl
    | ofAtom n => exact he true fun h => Entity.noConfusion h
    | ofSubject s => exact he true fun h => Entity.noConfusion h

/-- The conclusion of the prose route is itself satisfiable, so this batch refutes
    the route and not the thesis: C301 bounds a real claim rather than a fiction.
    Witness: a one-system family containing nothing.
    Footprint: `{Subject}`. -/
theorem externality_to_every_system_is_consistent :
    ∃ (S : Type) (In : S → Entity → Prop) (e : Entity),
      OutsideEverySystem S In e :=
  ⟨Unit, fun _ _ => False, Entity.ofGround, fun _ h => h.elim⟩

/-- At the canonical ground the quantifier swap fails concretely, not
    hypothetically: the ground really does ground all reality — `ActualEntity` is
    vacuous (C457), so "actual" adds nothing —
    (`ofGround_ground_of_reality`, `NecessityEternity.lean:140`, reused verbatim),
    and it is nonetheless **inside** a perfectly ordinary membership class.
    Grounding is not externality. Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
theorem universal_grounding_places_the_ground_inside_a_system :
    ∃ (S : Type) (In : S → Entity → Prop),
      (∀ e : Entity, ActualEntity e → e = Entity.ofGround ∨ OneEssence Entity.ofGround e)
      ∧ ¬ OutsideEverySystem S In Entity.ofGround := by
  refine ⟨Unit, fun _ e => e = Entity.ofGround, ?_, ?_⟩
  · intro e hAct
    exact ofGround_ground_of_reality e hAct
  · intro h
    exact h Unit.unit rfl

-- ============================================================================
-- Section 3: The Hierarchical Sense — Externality Does Not Deliver Freedom
-- ============================================================================

/-- Nonmembership of every class does not deliver being ungrounded. Witness: two
    classes, the singleton `Entity.ofGround`; an atom of that class lies outside
    every class, yet is grounded by the ground, which is a member of the class.
    Membership exclusion and grounding exclusion are independent.
    Footprint: `{Subject}`. -/
theorem membership_exclusion_does_not_entail_grounding_exclusion :
    ∃ (S : Type) (In : S → Entity → Prop) (Gr : S → Entity → Entity → Prop)
      (e : Entity),
      OutsideEverySystem S In e ∧ GroundedInSystem S In Gr e := by
  refine ⟨Bool, fun _ x => x = Entity.ofGround,
          fun _ g _ => g = Entity.ofGround, Entity.ofAtom 0, ?_, ?_⟩
  · intro σ h
    exact Entity.noConfusion h
  · exact ⟨true, Entity.ofGround, rfl, rfl⟩

/-- The same separation instantiated at the ground: `Entity.ofGround` lies outside
    every atom-class, and can still be ordered within one. The order relation is
    abstract on purpose — the ground is *provably* ungrounded by every atom
    (`CanonicalAseity.lean:96`, `atom_cannot_ground_the_ground`), so Γ's own
    `ExternalGrounding` cannot exhibit the ordering. That impossibility is itself
    part of the finding, and it is why the predicate is generic.
    Footprint: `{Subject}`. -/
theorem ofGround_external_to_every_class_may_still_be_ordered :
    ∃ (S : Type) (In : S → Entity → Prop) (Gr : S → Entity → Entity → Prop),
      OutsideEverySystem S In Entity.ofGround
      ∧ GroundedInSystem S In Gr Entity.ofGround := by
  refine ⟨Bool, fun _ x => x = Entity.ofAtom 0,
          fun _ _ x => x = Entity.ofGround, ?_, ?_⟩
  · intro σ h
    exact Entity.noConfusion h
  · exact ⟨false, Entity.ofAtom 0, rfl, rfl⟩

-- ============================================================================
-- Section 4: The Causal Sense — Grounding Is Not Production
-- ============================================================================

/-- Grounding all reality does not deliver causal externality. Γ declares no
    production relation, and for *any* causal relation at all the ground can sit
    inside a causal order. (The `ActualEntity` antecedent below is vacuous — C457 —
    so the range is all entities, not "actual" ones.) This is the exact missing
    statement the module header records as item (2) of the causal gap.
    Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
theorem universal_grounding_does_not_entail_causal_externality :
    ∃ (S : Type) (Caus : S → Entity → Entity → Prop),
      (∀ e : Entity, ActualEntity e → e = Entity.ofGround ∨ OneEssence Entity.ofGround e)
      ∧ ¬ CausalExternality S Caus Entity.ofGround := by
  refine ⟨Unit, fun _ g _ => g = Entity.ofAtom 0, ?_, ?_⟩
  · intro e hAct
    exact ofGround_ground_of_reality e hAct
  · intro h
    exact h Unit.unit (Entity.ofAtom 0) rfl

-- ============================================================================
-- Section 5: The Ontological Sense — Sole Candidacy
-- ============================================================================

/-- Sole candidacy: `Entity.ofGround` is the **only** entity in the Γ inventory
    satisfying `TranscendentGround`. C195 establishes that the ground is
    transcendent; C213 only restates it; no ledger row said it is *uniquely*
    transcendent. Both eliminations are the definition's own non-identity
    clauses, and the three constructors of `Entity` exhaust the inventory.
    Footprint: `{Subject}`. -/
theorem ofGround_sole_transcendent_ground (e : Entity)
    (hT : TranscendentGround e) : e = Entity.ofGround := by
  cases e with
  | ofAtom n => exact (hT.1 n rfl).elim
  | ofSubject s => exact (hT.2 s rfl).elim
  | ofGround => rfl

-- ============================================================================
-- Section 6: The Diagonal Sense — Self-Reference Does Not Force an Outside
-- ============================================================================

/-- C308 — the price of the diagonal, in one statement: even granting the
    **whole** `DiagonalSpec` (the genuine self-referential proposition
    `D ↔ ¬ ∃ s, Means s D`, not a weakened shadow of it), there need be **no**
    entity standing outside every system.

    Witness: satisfy the diagonal exactly as
    `level6_model_diagonal_true_consistent` does — `Subj := Unit`, `Means` meaning
    nothing, `D := True` — and simultaneously take a system family `S := Unit` in
    which *every* system contains *every* entity. The diagonal is fully granted
    and yet nothing is outside anything, because the system membership relation
    `In` and the diagonal's `Means` are **independent parameters**. The diagonal's
    externality is externality from *entertainment*; `OutsideEverySystem` is
    externality from *membership*. Nothing identifies them.

    The premise `_diag` is therefore **inert**, and that is the result rather than a
    defect of the encoding: the statement holds for *every* `DiagonalSpec`,
    because nothing in it constrains `In`. The underscore records the grant
    explicitly — the convention of naming inert premises instead of dropping them —
    so that a reader cannot mistake the unused hypothesis for an oversight. A reader
    who wants the diagonal to *matter* must supply the missing link between `Means`
    and `In`; Γ declares no such link, and inventing one would move the axiom
    register, which this batch's invariance test forbids.

    This is the machine-checked answer to `CHARACTERISTICS.md:65`, which calls the
    extension of the Gödel/Tarski/Turing pattern to normative claims "the decisive
    transcendental move". It is decisive about nothing: the pattern does not
    decide the matter, and a reader must not infer that it was refuted either —
    only that the self-reference it appeals to is already formalized here
    (`NegativeRetorsionAudit.lean:515`) and delivers no foundation.
    Footprint: `{Subject}`. -/
theorem diagonal_does_not_deliver_system_externality
    (Subj : Type) (Means : Subj → Prop → Prop) (_diag : DiagonalSpec Subj Means) :
    ∃ (S : Type) (In : S → Entity → Prop),
      ¬ (∃ e : Entity, OutsideEverySystem S In e) := by
  refine ⟨Unit, fun _ _ => True, ?_⟩
  rintro ⟨e, he⟩
  exact he Unit.unit trivial

-- ============================================================================
-- Section 7: Axiom Footprint Audit
-- ============================================================================

#print axioms OutsideEverySystem
#print axioms EachSystemHasAnOutside
#print axioms GroundedInSystem
#print axioms HierarchicalExternality
#print axioms CausalExternality
#print axioms per_system_outside_points_need_not_coalesce
#print axioms externality_to_every_system_is_consistent
#print axioms universal_grounding_places_the_ground_inside_a_system
#print axioms membership_exclusion_does_not_entail_grounding_exclusion
#print axioms ofGround_external_to_every_class_may_still_be_ordered
#print axioms universal_grounding_does_not_entail_causal_externality
#print axioms ofGround_sole_transcendent_ground
#print axioms diagonal_does_not_deliver_system_externality

end Logos.DivineTranscendence
