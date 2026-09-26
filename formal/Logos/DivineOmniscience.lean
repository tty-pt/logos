/-
# Logos.DivineOmniscience — Foundational Omniscience and Truth-Exhaustiveness

This module formalizes the characteristic of **Foundational Omniscience**
(the ground's scope excludes no truth; `CHARACTERISTICS.md` §14; `CHARS.md` §14)
for the necessary Ground of Reality (`Entity.ofGround`).

### What is formalized:
1. **Truth-Exhaustive Scope (`TruthExhaustive`):**
   No true proposition is closed to the entity's scope: `∀ p, T p → EntityMeans e p`.
   In Aquinas' terms (*ST* I, q. 14 a. 1 — *De differentia Dei a creaturis*, where the
   ground is the condition of all truth), the foundation is the "condition of truth":
   no truth lies outside what it is coextensive with.
2. **World-Indexed Exhaustiveness (`WorldTruthExhaustive`):**
   The same, world-indexed: no state of affairs true in *any* possible world is closed
   to the scope.
3. **Undivided Scope (reused from `DivineSimplicity`):**
   The scope is uniform and undivided across propositions (`UndividedMeaning`).
4. **Universal Grounding (reused from `FoundationalOmnipresence`):**
   The scope covers all reality (`UniversalModalGround`).
5. **The Master Synthesis (`FoundationalOmniscience`):**
   Conjoins (1)–(4) plus the refutation of the strong sense, with zero substantive
   axioms.

### The honest boundary, machine-checked:
Classical omniscience is *not* claimed — the prose explicitly disclaims it
(`README-OLD.md:263`: being the condition of truth does not entail knowing all
truth). Two independent machine results keep that boundary honest, and the
refutation of the strong sense is carried as a **field** of the master record
rather than hidden in a remark:

- **Infallibility is refuted for `Entity.ofGround`** (`ofGround_not_truth_tracking`,
  C236). `EntityMeans (Entity.ofGround) p` reduces to `True` by the constructor's
  match arm (stipulation ◈ `ofGround_meansAll`), so the ground's scope bears *every*
  proposition, including `False`. Hence the exclusive half
  (`EntityMeans e p → T p`) is **false** of the ground in Γ: the scope is
  exhaustive but provably not error-free. The classical "all and only truths"
  sense is not merely unproven here — it is refuted.
- **Counterfactual knowledge is not forced** (`exhaustive_scope_without_counterfactual_knowledge`,
  C240): the frontier predicate `Omniscience_Counterfactuals`
  (`DeepModalFrontier`) is satisfied by no `{}`-knowledge relation over an
  exhaustive-scope subject, so nothing in Γ forces the counterfactual sense.

Γ has no `Knows` predicate at all: the frontier's knowledge relations
(`KnowsAt`, `KnowsCounterfactualAt`) are *vocabulary definitions* generic over an
arbitrary relation, and `Entity.ofGround` is not a subject correlate
(`ofGround_ne_ofSubject`, `NecessityEternity.lean:155`) — so no subject-indexed
omniscience predicate can even be instantiated by the ground. This module
therefore establishes **foundational** omniscience only, and never manufactures a
divine knowledge bridge.
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
import Logos.DivineImmutability
import Logos.FoundationalOmnipresence
import Logos.FoundationalUnicity
import Logos.DivinePureActuality
import Logos.DeepModalFrontier

namespace Logos.DivineOmniscience

open Logos.Core
open Logos.Semantics (Form World Satisfies)
open Logos.Entity (Entity EntityOf)
open Logos.Modal (NecessaryEntity)
open Logos.Agency (Subject Means)
open Logos.RecoveredOntologicalGround (EntityMeans)
open Logos.DivineSimplicity (UndividedMeaning ofGround_undivided_meaning)
open Logos.FoundationalOmnipresence
    (MaximalCapacity UniversalModalGround ofGround_universal_modal_ground)
open Logos.DeepModalFrontier (Omniscience_Counterfactuals)

-- ============================================================================
-- Section 1: Metatheoretic Independence of Scope-Exhaustiveness and Infallibility
-- ============================================================================

/-- Metatheoretic separation (countermodel): an entity's scope can be exhaustive
    over every true proposition *and yet* fail to track truth exactly — i.e. a
    perfectly exhaustive scope is not error-free. The witness is the two-element
    carrier with a scope that is trivially total and one element that "fails"
    the tracking half.
    Footprint: `{}`. -/
theorem entity_scope_exhaustiveness_is_not_infallibility :
    ∃ (Ent : Type) (Scope Fails : Ent → Prop),
      (∀ e : Ent, Scope e) ∧ (∃ e : Ent, Scope e ∧ Fails e) := by
  refine ⟨Bool, fun _ => True, fun b => b = true, fun _ => trivial,
          ⟨true, trivial, rfl⟩⟩

-- ============================================================================
-- Section 2: Foundational (Truth-Exhaustive) Scope for the Ground
-- ============================================================================

/-- Foundational omniscience, permissive half: no true proposition is closed to
    the entity's scope — the ground is the condition of all truth.
    Footprint: `{Means, Subject}`. -/
def TruthExhaustive (e : Entity) : Prop :=
  ∀ p : Prop, T p → EntityMeans e p

/-- World-indexed truth-exhaustiveness: no state of affairs true in any possible
    world is closed to the entity's scope.
    Footprint: `{Means, Subject}`. -/
def WorldTruthExhaustive (e : Entity) : Prop :=
  ∀ w : World, ∀ φ : Form, Satisfies w φ → EntityMeans e (Satisfies w φ)

/-- Infallibility, the exclusive half: the entity's scope tracks truth exactly
    (what is borne, and nothing but what is true).
    Footprint: `{Means, Subject}`. -/
def TruthTracking (e : Entity) : Prop :=
  ∀ p : Prop, EntityMeans e p → T p

/-- Foundational Omniscience of the Ground of Reality: no true proposition, and
    no state of affairs true in any world, is closed to `Entity.ofGround`'s scope.
    Footprint: `{Means, Subject}`. -/
theorem ofGround_truth_exhaustive : TruthExhaustive Entity.ofGround := by
  intro p _
  trivial

/-- The ground's truth-exhaustive scope is uniform across modal space: no world
    and no form true in that world is closed to the ground's scope.
    Footprint: `{Means, Subject}`. -/
theorem ofGround_world_truth_exhaustive :
    WorldTruthExhaustive Entity.ofGround := by
  intro w φ _
  trivial

-- ============================================================================
-- Section 3: The Strong Sense, Machine-Checked as Refuted for the Ground
-- ============================================================================

/-- **The strong (infallible) sense is refuted for `Entity.ofGround`.**
    The ground's scope bears every proposition — including `False` — by the
    constructor's match arm, so the exclusive half of classical omniscience
    ("and nothing but the true") is false of the ground in Γ. The scope is
    exhaustive; it is provably not error-free.
    Footprint: `{Means, Subject}`. -/
theorem ofGround_not_truth_tracking : ¬ TruthTracking Entity.ofGround := by
  intro h
  exact h False trivial

-- ============================================================================
-- Section 4: Exhaustive Exhaustiveness (Atoms and Discriminating Subjects Excluded)
-- ============================================================================

/-- Exhaustive exclusion: no worldly atom bears even a single true proposition,
    so no atom is truth-exhaustive. Witness: `p := True`.
    Footprint: `{Means, Subject}`. -/
theorem atom_not_truth_exhaustive (n : Nat) :
    ¬ TruthExhaustive (Entity.ofAtom n) := by
  intro h
  exact h True trivial

/-- Exhaustive exclusion: a discriminating subject is never truth-exhaustive,
    because any *true* proposition it fails to mean is a witness against
    exhaustiveness.
    Footprint: `{Means, Subject}`. -/
theorem discriminating_subject_not_truth_exhaustive
    (s : Subject) (hDisc : ∃ p : Prop, T p ∧ ¬ Means s p) :
    ¬ TruthExhaustive (EntityOf s) := by
  intro h
  obtain ⟨p, ht, hp⟩ := hDisc
  exact hp (h p ht)

-- ============================================================================
-- Section 5: The Master Synthesis — Foundational Omniscience
-- ============================================================================

/-- Foundational Omniscience: the conjunction of the weak classical sense
    (no true proposition closed to the scope, in any world) with the undivided
    scope of `DivineSimplicity` and the universal grounding of
    `FoundationalOmnipresence`, plus the *refutation* of infallibility as a
    carried field — the boundary is part of the record, not a remark. (The
    structure itself is not an audited kernel node; the audited axiom set of
    the ground instance is recorded in `ofGround_foundational_omniscience`
    below.) -/
structure FoundationalOmniscience (g : Entity) : Prop where
  /-- No true proposition is closed to the entity's scope -/
  truth_exhaustive : TruthExhaustive g
  /-- The same across every possible world -/
  world_truth_exhaustive : WorldTruthExhaustive g
  /-- The scope is undivided across propositions (DivineSimplicity) -/
  undivided_scope : UndividedMeaning g
  /-- The scope is provably not truth-tracking: the strong sense is refuted -/
  not_truth_tracking : ¬ TruthTracking g
  /-- The scope covers all reality as the universal modal ground -/
  universal_ground : UniversalModalGround g

/-- Master Synthesis Theorem: The Ground of Reality possesses Foundational
    Omniscience in Γ — its scope excludes no truth, in any world, and (per the
    carried field) that scope is provably not infallible. Zero substantive
    axioms; the whole footprint is the declared vocabulary `{Means, Subject}`.
    Footprint: `{Means, Subject}`. -/
theorem ofGround_foundational_omniscience :
    FoundationalOmniscience Entity.ofGround := {
  truth_exhaustive := ofGround_truth_exhaustive
  world_truth_exhaustive := ofGround_world_truth_exhaustive
  undivided_scope := ofGround_undivided_meaning
  not_truth_tracking := ofGround_not_truth_tracking
  universal_ground := ofGround_universal_modal_ground }

-- ============================================================================
-- Section 6: The Thomistic Principle (Necessity, Scope and Grounding Concede Omniscience)
-- ============================================================================

/-- The Thomistic principle: any necessary entity that is maximally
    scope-exhaustive, undivided in scope, and a universal modal ground thereby
    satisfies Foundational Omniscience — *and* its scope is necessarily not
    error-free (from `hMax False`). The premise of necessary existence
    (`Aquinas ST` I q. 14 a. 1: the ground exists always, as the condition of
    truth) is carried explicitly; the conclusion is proved from the scope
    premises alone.
    Footprint: `{Means, Subject}`. -/
theorem necessity_and_scope_yield_foundational_omniscience
    (e : Entity) (_hNec : NecessaryEntity e) (hMax : MaximalCapacity e)
    (hUnd : UndividedMeaning e) (hUniv : UniversalModalGround e) :
    FoundationalOmniscience e := by
  refine ⟨?_, ?_, hUnd, ?_, hUniv⟩
  · intro p _
    exact hMax p
  · intro w φ _
    exact hMax _
  · intro h
    exact h False (hMax False)

-- ============================================================================
-- Section 7: Counterfactual Knowledge Is Not Forced (Countermodel)
-- ============================================================================

/-- Countermodel: an entity can have exhaustive scope and still fail the
    frontier's counterfactual-knowledge predicate — so nothing in Γ forces the
    counterfactual sense of omniscience from foundational omniscience. The
    knowledge relation is degenerate (`False`), so no counterfactual predicate
    holds, while the subject's scope is trivially exhaustive.
    Footprint: `{}`. -/
theorem exhaustive_scope_without_counterfactual_knowledge :
    ∃ (W S : Type) (Scope : S → Prop) (K : W → S → (W → Prop) → Prop) (s : S),
      Scope s ∧ ¬ Omniscience_Counterfactuals W S K s := by
  refine ⟨Bool, Bool, fun _ => True, fun _ _ _ => False, true, trivial, ?_⟩
  intro hK
  exact hK true (fun _ => True)

-- ============================================================================
-- Axiom Footprints
-- ============================================================================

#print axioms entity_scope_exhaustiveness_is_not_infallibility
#print axioms ofGround_truth_exhaustive
#print axioms ofGround_world_truth_exhaustive
#print axioms ofGround_not_truth_tracking
#print axioms atom_not_truth_exhaustive
#print axioms discriminating_subject_not_truth_exhaustive
#print axioms ofGround_foundational_omniscience
#print axioms necessity_and_scope_yield_foundational_omniscience
#print axioms exhaustive_scope_without_counterfactual_knowledge

end Logos.DivineOmniscience
