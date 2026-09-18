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

Necessity lift subject→entity (2026-09-18, batch lift-necessário): because
`ExistsAt` is a single shared relation and `Plurality.EntityOf` is the
Truthmaker embedding, `Plurality.NecessarySubject s` unfolds to the same
proposition as `NecessaryEntity (EntityOf s)` — `subject_nec_entity_nec` and
its `Iff` form are definitional (footprint `{Subject}`, VOCAB only). The
hostile separation `CountermodelSubjectNecessityNotEntityNecessity`
(HostileSemantics) shows the transfer is not a logical law: it holds because
of these definitions, not by logic alone. This does NOT close T7: it yields
the person's entity-correlate (C91/C92), not a uniform ground of necessary
truths (that stays `AxGlobalGround`-priced, C18).
-/

import Logos.Core
import Logos.Semantics
import Logos.Truthmaker
import Logos.Agency
import Logos.Plurality

namespace Logos.Modal

open Logos.Semantics (Form World)
open Logos.Truthmaker (Entity Ground ExistsAt TrueAt NecessarilyTrue)
open Logos.Agency (Subject)
open Logos.Plurality (NecessarySubject EntityOf)

/-- The present world (SEM, definitional): the performed actuality of the
    reasoning act needs only *some* fixed world in T7 (`Ground e τ` is invoked
    at it and nothing depends on which world it is). Modeled as the
    always-true valuation (precedent: `Necessity.someWorld`). -/
def actualWorld : World := fun _ => Logos.Semantics.TV.t

/-- An entity is necessary iff it exists in every world. -/
def NecessaryEntity (e : Entity) : Prop := ∀ w : World, ExistsAt w e

/-- An entity is contingent iff it is not necessary. -/
def Contingent (e : Entity) : Prop := ¬ NecessaryEntity e

/--Tag: SEM
AxGlobalGround (SEM): a formula true in every world is grounded by a
    single entity that exists in every world.

    This is the `∀w∃r … → ∃r∀w …` move of the informal T7. It is NOT
    derivable from `groundPrinciple_atom` (the swap is invalid in general); it is
    the declared modal price of the argument. Its negation does not destroy
    the act of denying it, so it stays a semantic axiom, never promoted to
    "transcendental theorem".

    Philosophical cost: the declared modal price of the argument. The
    `∀w∃r … → ∃r∀w …` swap is not derivable from the atomic truthmaker
    (`groundPrinciple_atom`); it posits one necessary ground for every
    necessarily-true formula, which the worldwise-but-not-uniform model
    (`CountermodelWorldwiseTruthmaking`) shows is unforced by logic alone. -/
axiom AxGlobalGround :
  ∀ (φ : Form), NecessarilyTrue φ → ∃ e : Entity, ∀ w : World, ExistsAt w e ∧ Ground e φ

/-- T7 — necessary truth forces necessary reality (base.txt T7).

    PROVEN↑ {Truthmaker.{Subject,Ground,ExistsAt},
             Semantics.{Form,World}, AxGlobalGround}. -/
theorem T7_necessaryReality {τ : Form} (hτ : NecessarilyTrue τ) :
    ∃ e : Entity, NecessaryEntity e ∧ Ground e τ := by
  obtain ⟨e, he⟩ := AxGlobalGround τ hτ
  exact ⟨e, fun w => (he w).1, (he actualWorld).2⟩

/-- C19 (closed): Grounding of the necessary excluded-middle reality under AxGlobalGround. -/
theorem T7_excludedMiddleInstance (φ : Form) :
    ∃ e : Entity, NecessaryEntity e ∧ Ground e (Form.or φ (Form.not φ)) :=
  T7_necessaryReality (Logos.Truthmaker.lawExcludedMiddle φ)

/-- The reductio shape of the prose: if every entity were contingent, no
    formula could be necessarily true. -/
theorem noNecessaryTruthIfAllContingent :
    (∀ e : Entity, Contingent e) → ∀ φ : Form, ¬ NecessarilyTrue φ := by
  intro hall φ hτ
  obtain ⟨e, hne, _⟩ := T7_necessaryReality hτ
  exact (hall e) hne

/--A subject that is necessary has an entity-correlate that is a necessary entity.

 Necessity lift (subject → entity, C91): if the subject `s` persists in every
    world (`NecessarySubject s`), its entity-correlate `EntityOf s` is an
    entity that exists in every world. The lift is *definitional*: `ExistsAt`
    is one shared relation and `EntityOf` is the Truthmaker embedding, so both
    sides unfold to `∀ w, ExistsAt w (EntityOf s)`. It carries no SEM/META
    price; its force is exactly the definitions chosen in Plurality/Truthmaker.
    Hostile separation (not a logical law):
    `CountermodelSubjectNecessityNotEntityNecessity` in HostileSemantics.
    Footprint: `{Subject}`. -/
theorem subject_nec_entity_nec (s : Subject) :
    NecessarySubject s → NecessaryEntity (EntityOf s) := by
  intro hs
  exact hs

/-- A subject is necessary iff its entity-correlate is a necessary entity
    (definitionally, see `subject_nec_entity_nec`). -/
theorem subject_nec_entity_nec_iff (s : Subject) :
    NecessarySubject s ↔ NecessaryEntity (EntityOf s) := Iff.rfl

/-- A necessary subject yields a necessary entity: some entity exists in
    every world (premise form of the lift, C91). -/
theorem necessary_entity_exists_of_necessary_subject {s : Subject} (h : NecessarySubject s) :
    ∃ e : Entity, NecessaryEntity e :=
  ⟨EntityOf s, subject_nec_entity_nec s h⟩

end Logos.Modal

-- Axiom footprint audit
#print axioms Logos.Modal.T7_necessaryReality
#print axioms Logos.Modal.T7_excludedMiddleInstance
#print axioms Logos.Modal.noNecessaryTruthIfAllContingent
#print axioms Logos.Modal.subject_nec_entity_nec
#print axioms Logos.Modal.subject_nec_entity_nec_iff
#print axioms Logos.Modal.necessary_entity_exists_of_necessary_subject
