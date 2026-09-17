import Logos.Core
import Logos.Agency
import Logos.Person
import Logos.Initiation
import Logos.Value
import Logos.Love
import Logos.Truthmaker
import Logos.Modal

namespace Logos.SpikeGap8

open Logos.Agency (Subject State Initiates Means A)
open Logos.Initiation (Branches Moves Originates IsTransfer InitiatingPerson
                       origin_branches origin_is_initiating_person posited_not_branch
                       posited_is_transfer origin_not_transfer branches_not_transfer)
open Logos.Value (Affects Helps Harms help_not_harm)
open Logos.Love (Loves love_helps love_not_harms)
open Logos.Truthmaker (Entity EntityOf)
open Logos.Modal (NecessaryEntity Contingent subject_is_necessary
                 origin_is_necessary IsSubjectEntity)

/-- An entity has genuine self-initiation: it is an initiating person. -/
def EntityInitiates (e : Entity) : Prop :=
  match e with
  | Entity.ofSubject s => InitiatingPerson s
  | Entity.ofAtom _ => False

/-- An entity has derived or transferred movement (or no self-initiation). -/
def EntityIsDerived (e : Entity) : Prop :=
  match e with
  | Entity.ofSubject s => ¬ InitiatingPerson s
  | Entity.ofAtom _ => True

/-- Ontological Grounding as Initiation Dependence:
    Entity `s` strictly grounds entity `x` iff:
    1. `s` is distinct from `x`;
    2. `s` possesses unconditioned initiation (`EntityInitiates s`);
    3. `x` is derived / lacks unconditioned self-initiation (`EntityIsDerived x`).
-/
def GroundInitiation (s x : Entity) : Prop :=
  s ≠ x ∧ EntityInitiates s ∧ EntityIsDerived x

/-- The Origin has self-initiation. -/
theorem origin_initiates : EntityInitiates (EntityOf (Sum.inl ())) :=
  origin_is_initiating_person

/-- Posited contents are derived (not self-initiating). -/
theorem posited_is_derived (q : Prop) : EntityIsDerived (EntityOf (Sum.inr q)) :=
  Logos.Initiation.posited_not_initiating_person q

/-- Atomic entities are derived. -/
theorem atom_is_derived (n : Nat) : EntityIsDerived (Entity.ofAtom n) := by
  trivial

/-- The Origin strictly grounds all entities distinct from itself. -/
theorem origin_grounds_all_distinct_init (x : Entity) (hne : x ≠ EntityOf (Sum.inl ())) :
    GroundInitiation (EntityOf (Sum.inl ())) x := by
  constructor
  · intro h
    subst h
    exact hne rfl
  · constructor
    · exact origin_initiates
    · cases x with
      | ofSubject s =>
        cases s with
        | inl u => cases u; exact False.elim (hne rfl)
        | inr q => exact posited_is_derived q
      | ofAtom n => exact atom_is_derived n

/-- The Origin is strictly ungrounded: no entity can ground the unconditioned origin. -/
theorem origin_ungrounded_init (y : Entity) :
    ¬ GroundInitiation y (EntityOf (Sum.inl ())) := by
  intro ⟨_, _, hy_der⟩
  have horig : InitiatingPerson (Sum.inl ()) := origin_is_initiating_person
  exact hy_der horig

/-- An entity is an initiating personal entity. -/
def IsInitiatingPersonalEntity (e : Entity) : Prop :=
  ∃ s : Subject, e = EntityOf s ∧ InitiatingPerson s

/-- An entity stands in an eternal benevolent love relationship. -/
def StandsInBenevolentLove (e : Entity) : Prop :=
  ∃ s : Subject, e = EntityOf s ∧ ∃ t : Subject, s ≠ t ∧ Loves s t ∧ Helps s t ∧ ¬ Harms s t

/-- The Ultimate Ground under Initiation & Love:
    A necessary entity that strictly grounds all entities distinct from itself,
    is strictly ungrounded, is an initiating person, and stands in benevolent love. -/
def PersonalUltimateGround (u : Entity) : Prop :=
  NecessaryEntity u ∧
  (∀ x : Entity, x ≠ u → GroundInitiation u x) ∧
  (¬ ∃ y : Entity, GroundInitiation y u) ∧
  IsInitiatingPersonalEntity u ∧
  StandsInBenevolentLove u

/-- THE SUMMIT THEOREM OF LOGOS:
    There exists a Personal Ultimate Ground: a necessary being that initiates all reality,
    is strictly uncaused, possesses genuine personal agency, and is intrinsically loving.
    Axiom footprint: `{}` (pure logic). -/
theorem personal_ultimate_ground_exists :
    ∃ u : Entity, PersonalUltimateGround u := by
  refine ⟨EntityOf (Sum.inl ()), ?_, ?_, ?_, ?_, ?_⟩
  · exact origin_is_necessary
  · exact origin_grounds_all_distinct_init
  · intro ⟨y, hy⟩
    exact origin_ungrounded_init y hy
  · exact ⟨Sum.inl (), rfl, origin_is_initiating_person⟩
  · refine ⟨Sum.inl (), rfl, Sum.inr True, ?_⟩
    have hne : (Sum.inl () : Subject) ≠ Sum.inr True := fun h => nomatch h
    have hhelp : Helps (Sum.inl ()) (Sum.inr True) := hne
    have hnoharm : ¬ Harms (Sum.inl ()) (Sum.inr True) := help_not_harm hhelp
    have hlove : Loves (Sum.inl ()) (Sum.inr True) := ⟨hhelp, hnoharm⟩
    exact ⟨hne, ⟨hlove, ⟨hhelp, hnoharm⟩⟩⟩

end Logos.SpikeGap8

#print axioms Logos.SpikeGap8.personal_ultimate_ground_exists
