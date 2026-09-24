/-
# Logos.RealityHookAudit — Stage 1: the reality-hook of propositional correctness

Refutes the skeptic's line "propositional right and wrong have nothing to do with
reality": in the live consistency model (`T p := p`, Core E0) correctness *is*
content, so `Correct s p → p` holds unconditionally and the disconnection thesis
is *unjudgeable as correct* — the skeptic can mouth it but never correctly judge it.

## What is proven here
- §4.1 tracking: `Correct`/`Incorrect`/`Asserts` each track reality (content is
  the case / fails); the extensional poles are the reality split `T True ∧ ¬ T False`.
- §4.2 the verdict: the disconnection thesis `D` is false, unjudgeable-as-correct,
  and no `ClaimsCorrect` performance (voice-level, deliberately non-factive) is
  ever veridical — refutation bites where the skeptic claims correctness.
- §4.3 hostile degenerate truth-marks: `TrEverything`/`TrNothing` are exactly the
  absolute marks the live semantics refutes; a vacuous mark cannot be a content hook
  (local-model witness). A non-vacuous truth-marks relation forces an internal
  truth/falsity split.

## What is NOT proven here (the unconditional boundary)
No actual judge is *populated* from bivalence alone (`M_inanimate`, C167): tracking
`∀ s p, Correct s p → p` says nothing about whether any subject performs a correct
judgment. Tracking ≠ populating.

## Footprint discipline
Every theorem whose statement names `Correct`/`Incorrect`/`Asserts`/`Act` unfolds
onto the act-bundle's declared VOCAB axioms (`Subject`, `Means`, `State`,
`Initiates`): vocabulary-only `{Initiates, Means, State, Subject}` — zero
substantive (SEM/META) axioms, the same floor as `Order.rightWrong_implies_meaning`.
Pure-logic pieces reach `{}`; the classical split theorem carries `{CL}`.
-/

import Logos.Core
import Logos.Agency
import Logos.Order
import Logos.RetorsiveNormativity

namespace Logos.RealityHookAudit

open Logos.Core (T IsFalse tschema N_T N_F)
open Logos.Agency (Subject Means State Initiates Act Asserts)
open Logos.Order (Correct Incorrect)
open Logos.RetorsiveNormativity (ClaimsCorrect)

-- ===========================================================================
-- §4.1 The tracking theorems (the hook itself)
-- ===========================================================================

/--Correctness tracks reality: whenever a subject's judgment is correct, its content is the case.

 `Correct s p → p`: under `T p := p` correctness is a content-hook by definition —
     unconditional, and vocabulary-only (the act-bundle's declared VOCAB).
    Footprint: `{Initiates, Means, State, Subject}`. -/
theorem correct_tracks_reality (s : Subject) (p : Prop) (h : Correct s p) : p :=
  (tschema p).1 h.2

/--Incorrectness tracks reality: whenever a subject's judgment is incorrect, its content fails.

 `Incorrect s p → ¬ p`: error is the content not being the case, by the same
     definitional union of act and truth-value.
    Footprint: `{Initiates, Means, State, Subject}`. -/
theorem incorrect_tracks_reality (s : Subject) (p : Prop) (h : Incorrect s p) : ¬ p :=
  fun hf => h.2 hf

/--Assertion tracks reality: a strong assertion's content is the case.

 `Asserts s p → p` — from `Asserts s p := Act s p ∧ p`.
    Footprint: `{Initiates, Means, State, Subject}`. -/
theorem assertion_tracks_reality (s : Subject) (p : Prop) (h : Asserts s p) : p :=
  h.2

/--The extensional poles are the reality split: True is true and False is not.

 `T True ∧ ¬ T False`: the forced distinction is a split of *content*, not a
     vacuous marker game.
    Footprint: `{}`. -/
theorem poles_are_reality_split : T True ∧ ¬ T False :=
  ⟨(tschema True).2 trivial, (tschema False).1⟩

/--Content reality hook: wherever a judgment is correct, its content is the case.

 `∀ p, (∃ s, Correct s p) → p`. Tracking ≠ populating — this does not assert
     that any subject judges; it is the unconditional reading of the hook.
    Footprint: `{Initiates, Means, State, Subject}`. -/
theorem content_reality_hook (p : Prop) : (∃ s : Subject, Correct s p) → p :=
  fun ⟨s, h⟩ => correct_tracks_reality s p h

-- ===========================================================================
-- §4.2 The "never correctly judged" verdict (the wishful-thinking collapse)
-- ===========================================================================

/--The disconnection thesis: propositional correctness has nothing to do with reality.

 `D := ¬ ∀ s p, Correct s p → p` — thinking "right and wrong have nothing to do
     with reality" is exactly this claim.
    Footprint: `{Initiates, Means, State, Subject}`. -/
def D : Prop := ¬ ∀ (s : Subject) (p : Prop), Correct s p → p

/--The disconnection thesis is false: correctness does track reality.

 `D` applied to `correct_tracks_reality` is a contradiction.
    Footprint: `{Initiates, Means, State, Subject}`. -/
theorem disconnection_thesis_false : ¬ D :=
  fun hD => hD (fun s p h => correct_tracks_reality s p h)

/--The disconnection thesis is unjudgeable-as-correct: no subject can ever correctly judge it.

 `¬ ∃ s, Correct s D` — the skeptic can mouth the thesis, never correctly judge
     it; if it were correct, it would contradict itself.
    Footprint: `{Initiates, Means, State, Subject}`. -/
theorem disconnection_thesis_unjudgeable_as_correct : ¬ ∃ s : Subject, Correct s D := by
  rintro ⟨s, h⟩
  exact disconnection_thesis_false (correct_tracks_reality s D h)

/--No claim of correctness over the disconnection thesis is ever veridical.

 `∀ s, ClaimsCorrect s D → ¬ Correct s D`: the voice-level claim (deliberately
     non-factive, `RetorsiveNormativity.ClaimsCorrect`) can be performed, but no
     such performance is true — the refutation bites exactly where the skeptic
     claims correctness.
    Footprint: `{Initiates, Means, State, Subject}`. -/
theorem claims_correct_disconnection_never_factive (s : Subject) (_h : ClaimsCorrect s D) :
    ¬ Correct s D :=
  fun hc => disconnection_thesis_false (correct_tracks_reality s D hc)

-- ===========================================================================
-- §4.3 Hostile degenerate truth-marks
-- ===========================================================================

/-- `TrEverything`: the vacuous mark — every proposition marked true. -/
def TrEverything (_p : Prop) : Prop := True

/-- `TrNothing`: the vacuous mark — no proposition marked true. -/
def TrNothing (_p : Prop) : Prop := False

/--Everything is marked true under the vacuous `TrEverything`.

 Footprint: `{}`. -/
theorem tr_everything_all_marked : ∀ p : Prop, TrEverything p := fun _ => trivial

/--Nothing is marked true under the vacuous `TrNothing`.

 Footprint: `{}`. -/
theorem tr_nothing_all_unmarked : ∀ p : Prop, ¬ TrNothing p := fun _p hp => hp

/--`TrEverything` reinstates (absorbs) the absolute `N_F` the live semantics refutes.

 `(∀ p, TrEverything p) ∧ ¬ N_F` — the "everything is true" absolute.
    Footprint: `{}`. -/
theorem tr_everything_absorbs_nf_family : (∀ p : Prop, TrEverything p) ∧ ¬ N_F :=
  ⟨tr_everything_all_marked, Logos.Core.notEverythingTrue⟩

/--`TrNothing` reinstates (absorbs) the absolute `N_T` the live semantics refutes.

 `(∀ p, ¬ TrNothing p) ∧ ¬ N_T` — the "nothing is true" absolute.
    Footprint: `{}`. -/
theorem tr_nothing_absorbs_nt_family : (∀ p : Prop, ¬ TrNothing p) ∧ ¬ N_T :=
  ⟨tr_nothing_all_unmarked, Logos.Core.notNothingTrue⟩

/--A non-vacuous truth-marks relation forces an internal truth/falsity split.

 `(¬ ∀ p, ¬ Tr p) ∧ (¬ ∀ p, Tr p) → ∃ p q, Tr p ∧ ¬ Tr q` — any mark that is
     neither empty nor total must split content into marked and unmarked.
    Footprint: `{CL}` (classical by-contradiction step). -/
theorem nontrivial_truth_forces_internal_split (Tr : Prop → Prop)
    (h : (¬ ∀ p : Prop, ¬ Tr p) ∧ (¬ ∀ p : Prop, Tr p)) :
    ∃ p q : Prop, Tr p ∧ ¬ Tr q := by
  have hp : ∃ p : Prop, Tr p := by
    apply Classical.byContradiction
    intro hno
    exact h.1 (fun p ht => hno ⟨p, ht⟩)
  have hq : ∃ q : Prop, ¬ Tr q := by
    apply Classical.byContradiction
    intro hno
    exact h.2 (fun p => by
      apply Classical.byContradiction
      intro hpnt
      exact hno ⟨p, hpnt⟩)
  rcases hp with ⟨p, htt⟩
  rcases hq with ⟨q, hnf⟩
  exact ⟨p, q, htt, hnf⟩

/--A vacuous mark cannot be a content hook: under `TrEverything`, content tracking fails.

 Local witness (`M := Unit`, `act := fun _ p => p = False`) — an act can reach a
     false content while `TrEverything` marks it true, so `(act s p ∧ TrEverything p) → p`
     does not hold for every act. A mark that never fails is not tracking.
    Footprint: `{}`. -/
theorem tr_everything_destroys_content_tracking :
    ∃ (M : Type) (act : M → Prop → Prop),
      (∃ s : M, ∃ p : Prop, act s p ∧ ¬ p) ∧
      (¬ ∀ (s : M) (p : Prop), (act s p ∧ TrEverything p) → p) := by
  refine ⟨Unit, (fun (_ : Unit) (p : Prop) => p = False), ?_⟩
  constructor
  · refine ⟨(), False, ?_⟩
    constructor
    · rfl
    · intro h
      exact h
  · intro hAll
    exact hAll () False ⟨rfl, trivial⟩

end Logos.RealityHookAudit

-- ---------------------------------------------------------------------------
-- Axiom footprint audit (expected values pinned in WITNESS.md §4; corrected
-- against the true `#print axioms` output after `lake build`)
-- ---------------------------------------------------------------------------
#print axioms Logos.RealityHookAudit.correct_tracks_reality
#print axioms Logos.RealityHookAudit.incorrect_tracks_reality
#print axioms Logos.RealityHookAudit.assertion_tracks_reality
#print axioms Logos.RealityHookAudit.poles_are_reality_split
#print axioms Logos.RealityHookAudit.content_reality_hook
#print axioms Logos.RealityHookAudit.D
#print axioms Logos.RealityHookAudit.disconnection_thesis_false
#print axioms Logos.RealityHookAudit.disconnection_thesis_unjudgeable_as_correct
#print axioms Logos.RealityHookAudit.claims_correct_disconnection_never_factive
#print axioms Logos.RealityHookAudit.TrEverything
#print axioms Logos.RealityHookAudit.TrNothing
#print axioms Logos.RealityHookAudit.tr_everything_all_marked
#print axioms Logos.RealityHookAudit.tr_nothing_all_unmarked
#print axioms Logos.RealityHookAudit.tr_everything_absorbs_nf_family
#print axioms Logos.RealityHookAudit.tr_nothing_absorbs_nt_family
#print axioms Logos.RealityHookAudit.nontrivial_truth_forces_internal_split
#print axioms Logos.RealityHookAudit.tr_everything_destroys_content_tracking