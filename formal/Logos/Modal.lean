/-
# Logos.Modal — necessity, contingency, and modal lifts

Necessity lift subject→entity: because `ExistsAt` is a single shared relation
and `Plurality.EntityOf` is the embedding, `Plurality.NecessarySubject s`
unfolds to the same proposition as `NecessaryEntity (EntityOf s)` —
`subject_nec_entity_nec` and its `Iff` form are definitional (footprint
`{Subject}`, VOCAB only).
-/

import Logos.Core
import Logos.Semantics
import Logos.Entity
import Logos.Agency
import Logos.Plurality

namespace Logos.Modal

open Logos.Semantics (Form World)
open Logos.Entity (Entity ExistsAt TrueAt NecessarilyTrue)
open Logos.Agency (Subject)
open Logos.Plurality (NecessarySubject EntityOf)

/-- The present world (SEM, definitional): modeled as the always-true valuation. -/
def actualWorld : World := fun _ => Logos.Semantics.TV.t

/-- An entity is necessary iff it exists in every world. -/
def NecessaryEntity (e : Entity) : Prop := ∀ w : World, ExistsAt w e

/-- An entity is contingent iff it is not necessary. -/
def Contingent (e : Entity) : Prop := ¬ NecessaryEntity e

/--A subject that is necessary has an entity-correlate that is a necessary entity.

 Necessity lift (subject → entity, C91): if the subject `s` persists in every
    world (`NecessarySubject s`), its entity-correlate `EntityOf s` is an
    entity that exists in every world. The lift is *definitional*: `ExistsAt`
    is one shared relation and `EntityOf` is the embedding, so both
    sides unfold to `∀ w, ExistsAt w (EntityOf s)`.
    Footprint: `{Subject}`. -/
theorem subject_nec_entity_nec (s : Subject) :
    NecessarySubject s → NecessaryEntity (EntityOf s) := by
  intro hs
  exact hs

/-- A subject is necessary iff its entity-correlate is a necessary entity
    (definitionally, see `subject_nec_entity_nec`). -/
theorem subject_nec_entity_nec_iff (s : Subject) :
    NecessarySubject s ↔ NecessaryEntity (EntityOf s) := Iff.rfl

end Logos.Modal

-- Axiom footprint audit
#print axioms Logos.Modal.subject_nec_entity_nec
#print axioms Logos.Modal.subject_nec_entity_nec_iff
