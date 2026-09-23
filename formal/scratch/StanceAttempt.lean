/-
# Logos.scratch.StanceAttempt — QUARANTINED, NOT PART OF THE ESTABLISHED ARGUMENT

Status: **quarantined scratch**. Not in the `Logos` lean_lib (`lakefile.toml`),
never imported, never compiled: it is invisible to the kernel, the axiom audit,
and the generated README. It is tracked only so the rejected route is on record.

Why these bridges are quarantined and not live-kernel axioms:

The established argument derives free will *under the self-given normative-
judicative stance* with ZERO substantive axioms (`attack_inviable_without_axioms`,
C165; footprint `{Initiates, Means, State, Subject, CL}`). The stance is a
performative datum — the field of every evaluative judgment, irrefutable in the
act of denying it — and C166 (`M_oneway`) / C167 (`M_inanimate`) are the machine
witnesses that no no-input existence theorem exists.

What this file explores, and deliberately rejects: closing the existential
*below any datum* — deriving the stance from bare `Act` and asserting an
unconditional performative act — would make `∃ s, FreeWill s` a no-input
theorem `⚠️ AXIOMATIC (AxJudicativeGrasp, AxJudicativeGraspNeg, PresentActDatum)`,
trading the self-given datum for declared axioms. The honest alternative
(chosen) keeps the stance as the stated, visible premise.

Nothing here is used downstream. If any stanza is ever promoted, it must first
earn a non-declared derivation or an explicit `Tag:` justification review.
-/

import Logos.Agency
import Logos.Order
import Logos.NormativeOrder
import Logos.IndubitableNormativeFreeWill

namespace Logos.StanceAttempt

open Logos.Agency
open Logos.Order
open Logos.NormativeOrder
open Logos.IndubitableNormativeFreeWill

-- Tag: SEM — a semantic choice: every act as such grasps the positive
-- normative standard. The live kernel deliberately has no such bridge.
axiom AxJudicativeGrasp : ∀ (s : Subject) (p : Prop), Act s p → Means s (Logos.Order.Correct s p)

-- Tag: SEM — the negative twin: every act as such grasps the negative
-- normative standard. Quarantined for the same reason.
axiom AxJudicativeGraspNeg : ∀ (s : Subject) (p : Prop), Act s p → Means s (Logos.Order.Incorrect s p)

-- Tag: TRANS — an unconditional performative datum asserting some act occurs.
-- The live kernel has no such unconditional act-datum.
axiom PresentActDatum : ∃ (s : Subject) (p : Prop), Act s p

/-- If those bridges were axioms, the stance would follow from any act. -/
theorem stance_from_act (s : Subject) (p : Prop) (h : Act s p) :
    ClaimsNormativeCorrectness s p :=
  ⟨h, AxJudicativeGrasp s p h, AxJudicativeGraspNeg s p h⟩

/-- ... and the stance would be non-empty unconditionally. -/
theorem stance_exists_unconditional : ∃ (s : Subject) (p : Prop), ClaimsNormativeCorrectness s p := by
  rcases PresentActDatum with ⟨s, p, hAct⟩
  exact ⟨s, p, stance_from_act s p hAct⟩

/-- ... so Free Will would be a no-input theorem, AXIOMATIC over the three
    bridges, reversing the round-4 axiom-free status. This is precisely what
    the quarantine refuses. -/
theorem free_will_unconditional : ∃ (s : Subject), FreeWill s := by
  rcases PresentActDatum with ⟨s, p, hAct⟩
  have hStance : ClaimsNormativeCorrectness s p := stance_from_act s p hAct
  exact ⟨s, (claims_normative_correctness_derives_free_will s p hStance).2⟩

end Logos.StanceAttempt