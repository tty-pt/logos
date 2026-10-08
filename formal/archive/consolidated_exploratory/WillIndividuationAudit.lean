/-
# Logos.WillIndividuationAudit — Independence Audit of `will_individuation` (A18)

`will_individuation` (`Logos.Agency`) is declared `Tag: VOCAB` — a constitutive
meaning-postulate, not a theorem. This module machine-witnesses that status
at the kernel level:

- A hostile model `HostileModel` (spec §5.1: `Subject := Bool`, `Will := Unit`,
  `subjectWill := fun _ => ()`) satisfies the pre-will spine together with its
  performative datum (`hostile_model_satisfies_prewill_spine`, `{}`).
- In that same model the law's own instantiation at `true`/`false` **arrives at
  a contradiction**: `subjectWill true != subjectWill false` is demanded while
  both sides are `()` (`hostile_model_refutes_will_individuation`, `{}`).
- Therefore the law cannot follow from the spine: if it did, it would hold in
  every model of the spine, including this one, where it is refutable
  (`will_individuation_not_forced_by_prewill_spine`, `{}`).

So the VOCAB meaning-postulate status of A18 is a **kernel fact**, witnessed
not by a missing proof but by a model in which the asserted law is contradictory.

Governing methodological rule (shared with `Logos.AxiomNegationAudit`):
  "Prefer losing the theorem to hiding the premise."
-/

import Logos.Core
import Logos.Agency

namespace Logos.WillIndividuationAudit

/-- Pre-Will Spine Signature:
    The Agency layer up to and including the will faculty `subjectWill`, ordered
    BEFORE the individuation law. The performative core (Means/State/Initiates)
    plus the will sorts are uninterpreted: nothing in the spine imposes
    injectivity of `subjectWill`. -/
structure PreWillSpine where
  Subject     : Type
  Means       : Subject → Prop → Prop
  State       : Type
  Initiates   : Subject → State → State → Prop → Prop
  Will        : Type
  subjectWill : Subject → Will

/-- The performative datum of the pre-will spine: some act occurs. -/
def PreWillDatumHolds (S : PreWillSpine) : Prop :=
  ∃ s p, S.Means s p ∧ ∃ w w', S.Initiates s w w' p

/-- The `will_individuation` law over a signature:
    distinct subjects possess numerically distinct will faculties. -/
def WillIndividuationStatement (S : PreWillSpine) : Prop :=
  ∀ s₁ s₂, s₁ ≠ s₂ → S.subjectWill s₁ ≠ S.subjectWill s₂

/-- Negation of `will_individuation`:
    there exist distinct subjects sharing one numerically identical will. -/
def NegWillIndividuation (S : PreWillSpine) : Prop :=
  ∃ s₁ s₂, s₁ ≠ s₂ ∧ S.subjectWill s₁ = S.subjectWill s₂

/-- The hostile pre-will spine model (STRENGTH.md §5.1):
    `Subject := Bool`, `Will := Unit`, `subjectWill := fun _ => ()` — every
    subject is collapsed onto the single trivial will `()`. -/
def HostileModel : PreWillSpine := {
  Subject     := Bool
  Means       := fun _ _ => True
  State       := Unit
  Initiates   := fun _ _ _ _ => True
  Will        := Unit
  subjectWill := fun _ => ()
}

/-- The hostile model satisfies the pre-will spine: the performative datum
    holds (subject `true` acts on proposition `True`). -/
theorem hostile_model_satisfies_prewill_spine :
    PreWillDatumHolds HostileModel := by
  exact ⟨true, True, trivial, ⟨(), (), trivial⟩⟩

/-- The law refutes in the hostile model: forcing `will_individuation` on this
    spine-model arrives at a contradiction, since distinct subjects `true`/`false`
    must then receive distinct wills while `subjectWill true` and
    `subjectWill false` are both `()`. -/
theorem hostile_model_refutes_will_individuation :
    WillIndividuationStatement HostileModel → False := by
  rintro h
  have hd : HostileModel.subjectWill true ≠ HostileModel.subjectWill false :=
    h true false (by intro h'; cases h')
  exact hd rfl

/-- Independence Theorem for `will_individuation`:
    the pre-will spine + its performative datum does NOT force the individuation
    law — the hostile model satisfies the spine while the law is refutable there.
    Hence A18 is a declared meaning-postulate, and its VOCAB status is a kernel
    fact, not a derivation gap. -/
theorem will_individuation_not_forced_by_prewill_spine :
    ∃ S : PreWillSpine, PreWillDatumHolds S ∧ NegWillIndividuation S := by
  exact ⟨HostileModel, hostile_model_satisfies_prewill_spine,
         ⟨true, false, (by intro h'; cases h'), rfl⟩⟩

end Logos.WillIndividuationAudit