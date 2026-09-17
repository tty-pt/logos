import Logos.Core
import Logos.Semantics
import Logos.Truthmaker
import Logos.Agency
import Logos.Modal

namespace Logos.SpikeGap5_6

open Logos.Semantics (Form World TV)
open Logos.Truthmaker (Entity EntityOf Ground ExistsAt TrueAt NecessarilyTrue)
open Logos.Agency (Subject)
open Logos.Modal (NecessaryEntity Contingent actualWorld subject_is_necessary)

/-- An entity is a transcendental subject entity. -/
def IsSubjectEntity (e : Entity) : Prop := ∃ s : Subject, e = Entity.ofSubject s

/-- An entity is an empirical atomic entity. -/
def IsAtomEntity (e : Entity) : Prop := ∃ n : Nat, e = Entity.ofAtom n

/-- The empty world where all atomic facts are false. -/
def emptyWorld : World := fun _ => TV.f

/-- No empirical entity exists in the empty world. -/
theorem emptyWorld_no_atom (n : Nat) : ¬ ExistsAt emptyWorld (Entity.ofAtom n) := by
  intro h
  nomatch h

/-- Any entity existing in the empty world must be a transcendental subject. -/
theorem entity_in_emptyWorld_is_subject (e : Entity) (he : ExistsAt emptyWorld e) :
    IsSubjectEntity e := by
  cases e with
  | ofSubject s => exact ⟨s, rfl⟩
  | ofAtom n => nomatch he

/-- The Origin is a necessary entity. -/
theorem origin_is_necessary : NecessaryEntity (EntityOf (Sum.inl ())) := by
  apply subject_is_necessary

/-- Every empirical entity is contingent. -/
theorem atom_is_contingent (n : Nat) : Contingent (Entity.ofAtom n) := by
  intro hnec
  have he : ExistsAt emptyWorld (Entity.ofAtom n) := hnec emptyWorld
  exact emptyWorld_no_atom n he

/-- Transcendental Quantifier Swap:
    A necessarily true atomic formula forces a transcendental grounder that exists in every world. -/
theorem transcendental_quantifier_swap (n : Nat) (hnec : NecessarilyTrue (Form.atom n)) :
    ∃ s : Subject, NecessaryEntity (EntityOf s) ∧ Ground (EntityOf s) (Form.atom n) := by
  obtain ⟨e, he_empty, hg⟩ := hnec emptyWorld
  cases e with
  | ofSubject s =>
    refine ⟨s, subject_is_necessary s, hg⟩
  | ofAtom k =>
    nomatch he_empty

/-- Modal Rigidity of the Ground:
    The necessary grounder cannot be an empirical entity; it must transcend empirical contingency. -/
theorem modal_rigidity_of_ground (n : Nat) (hnec : NecessarilyTrue (Form.atom n)) :
    ∃ e : Entity, NecessaryEntity e ∧ IsSubjectEntity e ∧ Ground e (Form.atom n) := by
  obtain ⟨s, hnec_s, hg⟩ := transcendental_quantifier_swap n hnec
  exact ⟨EntityOf s, hnec_s, ⟨s, rfl⟩, hg⟩

end Logos.SpikeGap5_6
