/-
# Logos.Modal — necessity, contingency, and T7 (base.txt §22→T7)

T7 in the prose runs: necessary truth τ ⇒ τ is grounded in no *contingent*
entity ⇒ some non-contingent reality grounds τ ⇒ ∃r □Exists(r).

The informal step `∀w ∃r … ⇒ ∃r ∀w …` is **not** a theorem of the axioms
above: it is exactly the quantifier swap that must be declared. We name it
`AxGlobalGround` (SEM). Everything else in T7 is then a theorem.

Sub-question Q7.2 (DEFERRED, see DESIGN.md): can `AxGlobalGround` be replaced
by a *weaker* premise, e.g. "every contingent ground of a necessary truth is
mirrored by a necessary ground"? Recorded, not required for T7 as stated.
-/

import Logos.Core
import Logos.Semantics
import Logos.Truthmaker

namespace Logos.Modal

open Logos.Semantics (Form World)
open Logos.Truthmaker (Entity Ground ExistsAt TrueAt NecessarilyTrue)

/-- The present world (SEM, definitional): the performed actuality of the
    reasoning act needs only *some* fixed world in T7 (`Ground e τ` is invoked
    at it and nothing depends on which world it is). Modeled as the
    always-true valuation (precedent: `Necessity.someWorld`). No longer an
    axiom: `def actualWorld` shrinks the C18–C20 footprints. -/
def actualWorld : World := fun _ => Logos.Semantics.TV.t

/-- An entity is necessary iff it exists in every world. -/
def NecessaryEntity (e : Entity) : Prop := ∀ w : World, ExistsAt w e

/-- An entity is contingent iff it is not necessary. -/
def Contingent (e : Entity) : Prop := ¬ NecessaryEntity e

/--Tag: SEM

 A formula true in every world is grounded by a single entity existing in every world (the quantifier swap).

 AxGlobalGround (SEM): a formula true in every world is grounded by a
    single entity that exists in every world.

    This is the `∀w∃r … → ∃r∀w …` move of the informal T7. It is NOT
    derivable from `groundPrinciple_atom` (the swap is invalid in general); it is
    the declared modal price of the argument. Its negation does not destroy
    the act of denying it, so it stays a semantic axiom, never promoted to
    "transcendental theorem". -/
axiom AxGlobalGround :
  ∀ (φ : Form), NecessarilyTrue φ → ∃ e : Entity, ∀ w : World, ExistsAt w e ∧ Ground e φ

/--Necessary truth forces necessary reality: whatever is true in every world is grounded by an entity existing in every world.

 T7 — necessary truth forces necessary reality (base.txt T7).

    PROVEN↑ {Truthmaker.{Subject,Ground,ExistsAt},
             Semantics.{Form,World}, AxGlobalGround} (E0: no `T`; C2: carrier is `Subject`). -/
theorem T7_necessaryReality {τ : Form} (hτ : NecessarilyTrue τ) :
    ∃ e : Entity, NecessaryEntity e ∧ Ground e τ := by
  obtain ⟨e, he⟩ := AxGlobalGround τ hτ
  exact ⟨e, fun w => (he w).1, (he actualWorld).2⟩

/--There is a necessary reality grounded on the indubitable: some entity existing in every world grounds 'φ or not-φ'.

 T7 instantiated on the excluded-middle tautology: the existential
    "there is a necessary reality grounded on the un-doubtable" holds. -/
theorem T7_excludedMiddleInstance (φ : Form) :
    ∃ e : Entity, NecessaryEntity e ∧ Ground e (Form.or φ (Form.not φ)) :=
  T7_necessaryReality (Logos.Truthmaker.lawExcludedMiddle φ)

/--If every entity were contingent, nothing could be true in every world.

 The reductio shape of the prose: if every entity were contingent, no
    formula could be necessarily true. -/
theorem noNecessaryTruthIfAllContingent :
    (∀ e : Entity, Contingent e) → ∀ φ : Form, ¬ NecessarilyTrue φ := by
  intro hall φ hτ
  obtain ⟨e, hne, _⟩ := T7_necessaryReality hτ
  exact (hall e) hne

end Logos.Modal

-- Axiom footprint audit
#print axioms Logos.Modal.T7_necessaryReality
#print axioms Logos.Modal.noNecessaryTruthIfAllContingent
