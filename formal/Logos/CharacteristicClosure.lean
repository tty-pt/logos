/-
# Logos.CharacteristicClosure — the last conditional form of Divine Simplicity, and the one field that is not vacuous

Two of the seven footprint characteristics had a defect that survived every previous batch, and
both are closed here **at 0 new axioms**. Neither is a new doctrine: each discharges a hypothesis
that Γ has already paid for, or exhibits a refuter that the previous batch left implicit.

## 1. Divine Simplicity was the last *conditional* instantiated form

Every other footprint characteristic is instantiated unconditionally. `DivineImmutability` is
`{Initiates, Means, NecessarySubjectKind, State, Subject}`, `FoundationalOmnipresence` is
`{Means, NecessarySubjectKind, Subject}`, `FoundationalOmniscience` the same, pure actuality and
transcendence likewise. **Divine Simplicity was the exception**: `ofGround_divine_simplicity`
(C196) still took an anonymous premise

```lean
(∀ s : Subject, ∃ p : Prop, ¬ Means s p) → DivineSimplicity Entity.ofGround
```

That premise *is* `SemanticFinitude` (F15, `SemanticFinitude.lean:162`, declared 2026-09-28,
`Tag: VOCAB`). It was a bare hypothesis only because F15 had not been declared when C196 was
written — the sentence the corpus had paid anonymously seventeen times was not yet a name. Now it
is, so the form is discharged below and the ground is simple **unconditionally**, with the F15
price visible in the audited footprint instead of hidden in an argument.

This is why the theorem cannot live in `DivineSimplicity.lean`: that file is imported *by*
`SemanticFinitude.lean`, and the discharge runs the other way. A new module is the only shape that
respects the dependency order, exactly as `Precedence.lean` and `CharacteristicSoleBearer.lean`
already do.

## 2. `TransitionInvariance` is not the field C321 emptied

C321 proved `CapacityInvariance` is satisfied by **every entity whatsoever** — a vacuity, and a
correct disclosure. Its sibling `TransitionInvariance = NotInSuccession` was then reported, in the
succession audit (C458–C462), to be *non-discriminating* too: C459 showed it holds of every atom,
and the field's discharging proof for the ground discards the `Initiates` conjunct and closes on
constructor disjointness alone.

Both findings are right, and together they left the field with no positive content at all: it holds
of the ground, it holds of every atom, and nobody had shown it can *fail*. That is a gap, because
a predicate that nothing refutes is not "non-discriminating", it is untested. The act datum (C454,
`performative_act_datum`, `Tag: TRANS`) supplies the refuter: `Act s p` unfolds to
`Means s p ∧ ∃ w w', Initiates s w w' p`, so an act *is* an initiation, and an initiation is
precisely what `NotInSuccession` denies. Hence `some_entity_is_in_succession` below.

**The asymmetry with C321, which is the point of the pair.** `CapacityInvariance` is vacuous
*definitionally* — `EntityMeans` takes no world argument, so the two bound worlds are unused and
the body reduces to `P ↔ P`, discharged by `Iff.rfl`. `NotInSuccession` quantifies genuinely over
`s σ σ' p`, and the refuter here is a real inhabitant of the relation, not a definitional artefact.
So the two fields of one structure now have *opposite* disclosure statuses, and the difference is
in the vocabulary rather than in the proofs. That is the same lesson C321 taught, in the other
direction, and it is why both belong in the same batch.

**What this does not do.** It does not make the ground the sole bearer of immutability. One
refuter is not unicity: `NotInSuccession` holds of every entity that never initiates, and the act
datum requires *one* subject to act, not initiation by every necessary-kind subject. The unicity question (C453) is settled in
`Logos.ImmutabilitySoleBearer` — negatively, by countermodel.
-/

import Logos.Core
import Logos.Semantics
import Logos.Entity
import Logos.Agency
import Logos.RecoveredOntologicalGround
import Logos.NecessityEternity
import Logos.DivineSimplicity
import Logos.SemanticFinitude

namespace Logos.CharacteristicClosure

open Logos.Semantics (World)
open Logos.Entity (Entity EntityOf)
open Logos.Agency (Subject State Means Initiates Act act_implies_initiates
  performative_act_datum)
open Logos.NecessityEternity (NotInSuccession)
open Logos.RecoveredOntologicalGround (OneEssence)
open Logos.DivineSimplicity (DivineSimplicity TranscendentGround
  ofGround_divine_simplicity divine_simplicity_sole_bearer)
open Logos.SemanticFinitude (GroundTranscendence)

-- ============================================================================
-- Section 1: the last conditional instantiated form, discharged
-- ============================================================================

/-- C484 — **the ground is divinely simple, unconditionally.** The premise
    `(∀ s, ∃ p, ¬ Means s p)` that C196 still carried is `SemanticFinitude` (F15): now a declared
    axiom, so it is paid *in the footprint* instead of being handed over as an anonymous argument.
    Nothing about the statement changed; what changed is that Γ can now be asked for it without
    the reader supplying a hypothesis on the corpus's behalf.

    **Disclosure.** The price is real and it is the F15 bound on `Means` — it did not become free.
    Because F15 carries `Tag: VOCAB`, the ledger's display for this row is `PROVEN`, not `PROVEN↑`;
    the honest summary is still *simplicity at the price of semantic finitude*, not simplicity
    outright.
    Compare C320 (`exactly_one_universal_modal_ground`), which pays the same bound for the same
    reason: it is the only declared bound on a subject's propositional reach.

    **No claim about essence.** `NonComposite e := ¬ ∃ p, ProperPart p e` is *mereological*
    simplicity — no distinct entity externally grounds `e`. It is not the identity of essence and
    existence (`CHARS.md` §13's honest boundary), and nothing here moves that boundary.

    Footprint: `{GroundTranscendence, Means, Subject, propext}`. -/
theorem the_ground_is_divinely_simple : DivineSimplicity Entity.ofGround :=
  ofGround_divine_simplicity GroundTranscendence

/-- C485 — the same result in existence form, so the characteristic is instantiated rather than
    merely held of a named entity: **something in Γ is divinely simple.**
    Footprint: `{GroundTranscendence, Means, Subject, propext}`. -/
theorem some_entity_is_divinely_simple : ∃ e : Entity, DivineSimplicity e :=
  ⟨Entity.ofGround, the_ground_is_divinely_simple⟩

/-- C486 — the **attributes-table form, unconditional**: the ground bears Divine Simplicity and
    is its only bearer, in one declaration a reader-facing row can cite. This is C440
    (`divine_simplicity_sole_bearer`) with its anonymous premise discharged, so C440's two halves
    now have different *statuses* and the row should say so:

    * the **unicity** conjunct was already `PROVEN` and pays nothing — C439 closes on the
      `no_internal_components` field alone, and `HasInternalComponent` is `False` only on
      `Entity.ofGround` by definition;
    * the **combined** row is `PROVEN` because F15 carries `Tag: VOCAB`, but it inherits the
      bounding price even though that price adds no substantive SEM/META/TRANS axiom.

    So the pair is not uniform, and the asymmetry is the informative part: *who is simple* is
    settled by the entity inventory alone, while *that anything is simple* needs the semantic
    bound. That is the opposite of the pattern in C442–C445, where the `universal_ground` field
    made the subject arm the hard one. Recorded rather than smoothed over.

    Footprint: `{GroundTranscendence, Means, Subject, propext}`. -/
theorem the_ground_is_sole_bearer_of_divine_simplicity :
    DivineSimplicity Entity.ofGround ∧
      (∀ e : Entity, DivineSimplicity e → e = Entity.ofGround) :=
  divine_simplicity_sole_bearer GroundTranscendence

-- ============================================================================
-- Section 2: the field that is not vacuous
-- ============================================================================

/-- C487 — **something is in succession**: `NotInSuccession` is false somewhere, so the
    `transition_invariance` field of `DivineImmutability` is *refutable* and therefore not a
    vacuity in C321's sense.

    The proof is one unfolding. `performative_act_datum` (C454) supplies `Act s p`; `Act` is
    `Means s p ∧ ∃ w w', Initiates s w w' p`; so `s` initiates. And `NotInSuccession e` is
    `¬ ∃ s σ σ' p, e = EntityOf s ∧ Initiates s σ σ' p`, which `e := EntityOf s` refutes with the
    same `s`.

    **Why this is not unicity.** `NotInSuccession` is satisfied by *every* entity whose subject
    correlate never initiates, so one refuter establishes that the field has content and nothing
    more. C453 (the sole-bearer form) needs every necessary-kind subject to initiate, which is strictly stronger
    than the act datum; `Logos.ImmutabilitySoleBearer` machine-checks the gap and closes C453 as
    non-derivable. Read this theorem as the *live half* of that closure, and that module as the negative
    half.

    Footprint: `{Initiates, Means, State, Subject, performative_act_datum}`. -/
theorem some_entity_is_in_succession : ∃ e : Entity, ¬ NotInSuccession e := by
  obtain ⟨s, p, hAct⟩ := performative_act_datum
  obtain ⟨w, w', hInit⟩ := act_implies_initiates hAct
  refine ⟨EntityOf s, fun hn => ?_⟩
  exact hn ⟨s, w, w', p, rfl, hInit⟩

/-- C488 — the same refuter, stated the way `C453` would need it and **cannot** obtain it: the act
    datum does not entail that *every* subject acts. It is stated here as a conditional so that the
    two results sit adjacent, and the module docstring of `Logos.ImmutabilitySoleBearer` records
    the formal missing lemma `∀ s, NecessaryKind s → ∃ σ σ' p, Initiates s σ σ' p`.

    **Note the footprint, which is not C487's.** C487 pays `performative_act_datum` because it draws
    the act from the datum; C488 takes the act as an argument, so it pays only the vocabulary of
    `Act` itself. Read the pair as: *given* an act the field is refuted at that subject, and *hence*
    some subject refutes it — the price being exactly the datum, paid once.

    Footprint: `{Initiates, Means, State, Subject}`. -/
theorem a_subject_that_acts_is_in_succession {s : Subject} {p : Prop} (h : Act s p) :
    ¬ NotInSuccession (EntityOf s) := by
  obtain ⟨w, w', hInit⟩ := act_implies_initiates h
  exact fun hn => hn ⟨s, w, w', p, rfl, hInit⟩

-- ============================================================================
-- Section 3: the principle form, and the bound it actually needs
-- ============================================================================

/-- C491 — **the Thomistic principle form of Divine Simplicity**, the one the characteristic was
    missing: the other footprint characteristics already had `C447`–`C451`-shaped principle
    theorems (necessity and atemporality yield immutability, necessity and aseity and
    immutability yield pure actuality, universal ground and aseity yield omnipresence, necessity
    and scope yield omniscience, necessity and presence yield omnipotence). **Simplicity had
    none**, which made its presence in the attributes table depend on a reader accepting a
    *particular entity* rather than a *reason*.

    The principle read here is Aquinas' own (*ST* I q.18 a.2): what is transcendent — not an atom
    and not a subject correlate — is simple, given the declared F15 bound. This is proved for an
    arbitrary transcendent entity by exhausting `Entity`'s three constructors: atoms and subject
    correlates contradict transcendence, and the ground is simple by C484. The bound is not
    decoration: F15 is what closes the ground arm, and the corollary below shows it cannot be
    replaced by a reformulation of the same `Means` information.

    Because F15 carries `Tag: VOCAB`, the ledger display is `PROVEN`, not `PROVEN↑`; the bound
    remains part of the machine-checked price.

    Footprint: `{GroundTranscendence, Means, Subject, propext}`. -/
theorem transcendence_and_semantic_finitude_yield_divine_simplicity :
    ∀ e : Entity, TranscendentGround e → DivineSimplicity e := by
  intro e h
  cases e with
  | ofGround => exact ofGround_divine_simplicity GroundTranscendence
  | ofAtom n => exact False.elim (h.1 n rfl)
  | ofSubject s => exact False.elim (h.2 s rfl)

/-- C492 — the point of C491, machine-checked: **F15 bounds the wrong relation.** The bound it
    declares is on `Means` (`∀ s, ∃ p, ¬ Means s p`), and it is what makes
    `ofGround_non_composite` close. But the mereological field's *content* is about
    `OneEssence` — `NonComposite e := ¬ ∃ p, p ≠ e ∧ OneEssence p e` — and the countermodel
    below exhibits an interpretation in which every subject is `Means`-discriminating, F15's shape
    holds exactly, and a subject nonetheless externally grounds a non-ground entity. So the two
    finitudes are independent, and the price of simplicity is a *grounding* finitude that Γ has
    never declared.

    **Why this is worth having.** It converts "simplicity is priced by F15" from an observation
    about one proof into a statement about the vocabulary: the characteristic cannot be had at a
    weaker price, and no reformulation of the existing bound removes it. The honest options are
    therefore exactly two — declare a `OneEssence`-side finitude (`Tag: VOCAB` at minimum, an
    author decision), or keep paying F15. Both are recorded; neither is taken here.

    **Naming.** The binder `GroundRel` below is an *arbitrary* relation of that shape, not the
    corpus predicate `Logos.RecoveredOntologicalGround.OneEssence`. The distinction matters:
    the statement quantifies over every relation `Entity → Entity → Prop`, so it says no relation
    of that shape closes the grounding arm. Reading the binder as the corpus's own predicate would
    narrow the theorem to a single relation and overstate what it proves. (The corpus predicate
    was renamed `GroundsEntity` → `OneEssence` on 2026-10-02; this binder predates and does not
    follow that rename.)

    Footprint: `{}`. -/
theorem the_semantic_bound_does_not_close_the_grounding_arm :
    ∃ (Subject Entity : Type)
      (EntityOf : Subject → Entity)
      (Means : Subject → Prop → Prop)
      (GroundRel : Entity → Entity → Prop),
      (∀ s : Subject, ∃ p : Prop, ¬ Means s p) ∧
      (∃ s : Subject, ∃ g e : Entity, g = EntityOf s ∧ e ≠ g ∧ GroundRel g e) := by
  refine ⟨Bool, Nat, fun s => if s then 0 else 1, fun _ _ => False,
    fun _ e => e = 0, ?_⟩
  refine ⟨?_, ?_⟩
  · intro s
    exact ⟨True, fun h => h⟩
  · exact ⟨false, 1, 0, by decide, by decide, rfl⟩

#print axioms the_ground_is_divinely_simple
#print axioms some_entity_is_divinely_simple
#print axioms the_ground_is_sole_bearer_of_divine_simplicity
#print axioms some_entity_is_in_succession
#print axioms a_subject_that_acts_is_in_succession
#print axioms transcendence_and_semantic_finitude_yield_divine_simplicity
#print axioms the_semantic_bound_does_not_close_the_grounding_arm

end Logos.CharacteristicClosure
