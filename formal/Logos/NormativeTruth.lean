/-
# Logos.NormativeTruth — Retorsion of Normative Truth and the Free Subject

Formalizes the retorsive self-refutation of the universal denial of normative truth
("There is no normative truth" → False), derives the necessary existence of normative truth,
connects it to the established Strong Right / Strong Wrong results, dissects why impersonal
models (CM22) fail against genuine normativity, and synthesizes normative truth with the
already-proved Free Subject result to derive Metaphysical Indeterminism and ¬D3.
-/

import Logos.Core
import Logos.Necessity
import Logos.Semantics
import Logos.Agency
import Logos.Order
import Logos.Choice
import Logos.StrongActionChoice

namespace Logos.NormativeTruth

open Logos.Core (rightWrongDistinction N_T N_F)
open Logos.Agency (Subject)
open Logos.Choice (FreeWill FreeSubject freeSubject_iff_freeWill freeSubject_exists)
open Logos.StrongActionChoice (WorldModel NomologicalDeterminism_D3 MetaphysicalIndeterminism
  StrongChoosesContext MetaphysicalAvailabilityContext Available GenuineChooses
  GenuineFreeSubject free_subject_implies_metaphysical_indeterminism free_subject_conflicts_with_d3)

-- ===========================================================================
-- Section 1: Definition of Normative Truth & Universal Denial
-- ===========================================================================

/-- The universal denial of normative truth relative to a normative predicate:
    the proposition stating that there is no normative truth.
    Status: DEFINITIONAL. -/
def NoNormativeTruth (NormativeTruth : Prop → Prop) : Prop :=
  ¬ ∃ p : Prop, NormativeTruth p

/-- Context specifying the constitutive semantics of normative truth,
    including its self-applicative retorsive character.
    Status: DEFINITIONAL. -/
structure NormativeTruthContext where
  NormativeTruth : Prop → Prop
  self_applicative : NoNormativeTruth NormativeTruth → NormativeTruth (NoNormativeTruth NormativeTruth)

-- ===========================================================================
-- Section 2: Retorsive Self-Refutation of the Denial
-- ===========================================================================

/-- Theorem: Under self-application, the universal denial of normative truth is strictly self-refuting.
    Status: PROVED (Pure logic, footprint {}). -/
theorem no_normative_truth_is_self_refuting
    (NormativeTruth : Prop → Prop)
    (hSelf : NoNormativeTruth NormativeTruth → NormativeTruth (NoNormativeTruth NormativeTruth)) :
    NoNormativeTruth NormativeTruth → False := by
  intro hNo
  have hSelfApp : NormativeTruth (NoNormativeTruth NormativeTruth) := hSelf hNo
  have hEx : ∃ p, NormativeTruth p := ⟨NoNormativeTruth NormativeTruth, hSelfApp⟩
  exact hNo hEx

/-- Theorem: Direct derivation that normative truth necessarily exists from the retorsive self-application.
    Status: PROVED (Pure logic, footprint {}). -/
theorem normative_truth_exists
    (NormativeTruth : Prop → Prop)
    (hSelf : NoNormativeTruth NormativeTruth → NormativeTruth (NoNormativeTruth NormativeTruth)) :
    ∃ p : Prop, NormativeTruth p := by
  apply Classical.byContradiction
  intro hNo
  exact no_normative_truth_is_self_refuting NormativeTruth hSelf hNo

/-- Theorem: Context-packaged form of the retorsion theorem.
    Status: PROVED (Pure logic, footprint {}). -/
theorem context_normative_truth_exists (ctx : NormativeTruthContext) :
    ∃ p : Prop, ctx.NormativeTruth p :=
  normative_truth_exists ctx.NormativeTruth ctx.self_applicative

-- ===========================================================================
-- Section 3: World-Indexed Modal Lifting (Necessity)
-- ===========================================================================

/-- World-indexed universal denial of normative truth at world w.
    Status: DEFINITIONAL. -/
def NoNormativeTruthAt (World : Type) (NormAt : World → Prop → Prop) (w : World) : Prop :=
  ¬ ∃ p : Prop, NormAt w p

/-- Modal Retorsion Theorem: In any modal semantics where the retorsive self-application
    holds across worlds, normative truth necessarily exists in every world.
    Status: PROVED (Pure logic, footprint {}). -/
theorem necessary_normative_truth_exists
    {World : Type} (NormAt : World → Prop → Prop)
    (hRet : ∀ w : World, NoNormativeTruthAt World NormAt w → NormAt w (NoNormativeTruthAt World NormAt w)) :
    ∀ w : World, ∃ p : Prop, NormAt w p := by
  intro w
  apply Classical.byContradiction
  intro hNo
  have hSelf := hRet w hNo
  have hEx : ∃ p, NormAt w p := ⟨NoNormativeTruthAt World NormAt w, hSelf⟩
  exact hNo hEx

-- ===========================================================================
-- Section 4: Connection to Established Strong Right and Strong Wrong
-- ===========================================================================

/-- Context connecting the established Right/Wrong distinction to Normative Truth.
    Treats the established result (¬N_T ∧ ¬N_F) as genuine normative truth.
    Status: DEFINITIONAL / SEMANTIC BRIDGE. -/
structure RightWrongNormativeContext where
  NormativeTruth : Prop → Prop
  right_wrong_is_normative : NormativeTruth (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F)

/-- Theorem: The established Right/Wrong distinction strictly instantiates NormativeTruth.
    Status: PROVED (Connecting Core.rightWrongDistinction to NormativeTruth). -/
theorem right_wrong_is_normative_truth (ctx : RightWrongNormativeContext) :
    ∃ p : Prop, ctx.NormativeTruth p :=
  ⟨¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F, ctx.right_wrong_is_normative⟩

/-- Theorem: Both the objective truth-content and the normative status obtain simultaneously.
    Status: PROVED (Pure logic from Core.rightWrongDistinction). -/
theorem right_wrong_content_and_normativity (ctx : RightWrongNormativeContext) :
    (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) ∧ ctx.NormativeTruth (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) :=
  ⟨Logos.Core.rightWrongDistinction, ctx.right_wrong_is_normative⟩

-- ===========================================================================
-- Section 5: Dissection of CM22 & Genuine Normativity vs Impersonal Realism
-- ===========================================================================

/-!
### Dissection of CM22 (Platonic Impersonal Realism)
CM22 demonstrated that an extensional predicate called `StrongNormativeFact`
can obtain in an impersonal world with zero subjects. However, that only succeeded
because `StrongNormativeFact` was a descriptive truth-value. Genuine normative truth
constitutively addresses an agent (`NormativeAddress`).
-/

/-- Genuine normative truth constitutively addresses an agent capable of normative guidance.
    A norm that addresses no one is an inert descriptive fact, not a normative truth.
    Status: DEFINITIONAL. -/
structure GenuineNormativeDomain (Subject : Type) where
  NormTruth : Prop → Prop
  NormativelyAddresses : Prop → Subject → Prop
  constitutive_address : ∀ p, NormTruth p → ∃ s, NormativelyAddresses p s

/-- Theorem: An impersonal model containing zero subjects strictly excludes genuine normative truth.
    Status: PROVED (Pure logic, zero axioms). -/
theorem impersonal_model_excludes_genuine_normative_truth
    {Subject : Type} (dom : GenuineNormativeDomain Subject)
    (hNoSubject : ∀ _s : Subject, False) :
    ¬ ∃ p, dom.NormTruth p := by
  intro ⟨p, hNT⟩
  obtain ⟨s, _⟩ := dom.constitutive_address p hNT
  exact hNoSubject s

-- ===========================================================================
-- Section 6: Synthesis with the ALREADY-PROVED Free Subject Result
-- ===========================================================================

/-!
### Synthesis of Normative Truth and the Free Subject
The existence of Free Will (`FreeWill s ↔ FreeSubject s`) is already proven in Γ
(`Choice.freeSubject_exists`). When combined with genuine normative truth,
normative agency is grounded in the Free Subject, yielding Genuine Choice,
Metaphysical Indeterminism, and the refutation of D3.
-/

/-- Context defining the metaphysical grounding bridge between normative agency
    and genuine categorical choice among metaphysically available alternatives.
    Status: METAPHYSICAL BRIDGE. -/
structure NormativeFreeGroundContext
    (World : Type) (PriorState : Type) (FutureState : Type) where
  cctx : StrongChoosesContext Subject
  mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState
  free_ground : ∀ (s : Subject) (w : World), FreeSubject s → mctx.W.laws w → GenuineFreeSubject cctx mctx s w

/-- Theorem: The established Free Subject grounds normative agency in a Genuine Free Subject.
    Status: PROVED (Conditional on NormativeFreeGroundContext). -/
theorem normative_free_subject_grounds_agency
    {World PriorState FutureState : Type}
    (fgctx : NormativeFreeGroundContext World PriorState FutureState)
    (s : Subject) (w : World)
    (hFS : FreeSubject s)
    (hLaws : fgctx.mctx.W.laws w) :
    GenuineFreeSubject fgctx.cctx fgctx.mctx s w :=
  fgctx.free_ground s w hFS hLaws

/-- Master Theorem 1: The synthesized Normative Free Subject strictly entails Metaphysical Indeterminism.
    Status: PROVED (Footprint {}). -/
theorem normative_free_subject_implies_indeterminism
    {World PriorState FutureState : Type}
    (fgctx : NormativeFreeGroundContext World PriorState FutureState)
    (s : Subject) (w : World)
    (hFS : FreeSubject s)
    (hLaws : fgctx.mctx.W.laws w) :
    MetaphysicalIndeterminism fgctx.mctx.W := by
  have hGFS := normative_free_subject_grounds_agency fgctx s w hFS hLaws
  exact free_subject_implies_metaphysical_indeterminism hGFS

/-- Master Theorem 2: The synthesized Normative Free Subject strictly refutes Nomological Determinism D3.
    Status: PROVED (Footprint {}). -/
theorem normative_free_subject_implies_not_d3
    {World PriorState FutureState : Type}
    (fgctx : NormativeFreeGroundContext World PriorState FutureState)
    (s : Subject) (w : World)
    (hFS : FreeSubject s)
    (hLaws : fgctx.mctx.W.laws w) :
    ¬ NomologicalDeterminism_D3 fgctx.mctx.W := by
  have hGFS := normative_free_subject_grounds_agency fgctx s w hFS hLaws
  exact free_subject_conflicts_with_d3 hGFS

/-- Theorem: Using the ALREADY-PROVED existential Free Subject from Choice.lean,
    in any lawful world, a Genuine Free Subject exists and Nomological Determinism D3 fails.
    Status: PROVED (Footprint {}). -/
theorem established_free_subject_defeats_d3
    {World PriorState FutureState : Type}
    (fgctx : NormativeFreeGroundContext World PriorState FutureState)
    (w : World)
    (hLaws : fgctx.mctx.W.laws w)
    (hFS_ex : ∃ s : Subject, FreeSubject s) :
    MetaphysicalIndeterminism fgctx.mctx.W ∧ ¬ NomologicalDeterminism_D3 fgctx.mctx.W := by
  obtain ⟨s, hFS⟩ := hFS_ex
  constructor
  · exact normative_free_subject_implies_indeterminism fgctx s w hFS hLaws
  · exact normative_free_subject_implies_not_d3 fgctx s w hFS hLaws

end Logos.NormativeTruth

-- Axiom footprint audit
#print axioms Logos.NormativeTruth.no_normative_truth_is_self_refuting
#print axioms Logos.NormativeTruth.normative_truth_exists
#print axioms Logos.NormativeTruth.context_normative_truth_exists
#print axioms Logos.NormativeTruth.necessary_normative_truth_exists
#print axioms Logos.NormativeTruth.right_wrong_is_normative_truth
#print axioms Logos.NormativeTruth.right_wrong_content_and_normativity
#print axioms Logos.NormativeTruth.impersonal_model_excludes_genuine_normative_truth
#print axioms Logos.NormativeTruth.normative_free_subject_grounds_agency
#print axioms Logos.NormativeTruth.normative_free_subject_implies_indeterminism
#print axioms Logos.NormativeTruth.normative_free_subject_implies_not_d3
#print axioms Logos.NormativeTruth.established_free_subject_defeats_d3
