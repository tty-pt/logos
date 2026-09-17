import Logos.Core
import Logos.Agency
import Logos.Person
import Logos.Initiation
import Logos.Truthmaker
import Logos.Modal

namespace Logos.SpikeGap7

open Logos.Agency (Subject State Initiates Means A)
open Logos.Initiation (Branches Moves Originates IsTransfer InitiatingPerson
                       origin_branches origin_is_initiating_person posited_not_branch
                       posited_is_transfer origin_not_transfer branches_not_transfer)
open Logos.Truthmaker (Entity EntityOf)
open Logos.Modal (NecessaryEntity Contingent subject_is_necessary prop_neq_not)

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

/-- The Origin has self-initiation. -/
theorem origin_initiates : EntityInitiates (EntityOf (Sum.inl ())) := by
  change InitiatingPerson (Sum.inl ())
  exact origin_is_initiating_person

/-- Posited contents are derived (not self-initiating). -/
theorem posited_is_derived (q : Prop) : EntityIsDerived (EntityOf (Sum.inr q)) := by
  change ¬ InitiatingPerson (Sum.inr q)
  exact Logos.Initiation.posited_not_initiating_person q

/-- Atomic entities are derived. -/
theorem atom_is_derived (n : Nat) : EntityIsDerived (Entity.ofAtom n) := by
  trivial

/-- Ontological Grounding as Initiation Dependence:
    Entity `s` strictly grounds entity `x` iff:
    1. `s` is distinct from `x`;
    2. `s` possesses unconditioned initiation (`EntityInitiates s`);
    3. `x` is derived / lacks unconditioned self-initiation (`EntityIsDerived x`).
-/
def GroundInitiation (s x : Entity) : Prop :=
  s ≠ x ∧ EntityInitiates s ∧ EntityIsDerived x

/-- Grounding is strictly irreflexive: no entity can ground itself. -/
theorem groundInitiation_irreflexive (x : Entity) : ¬ GroundInitiation x x := by
  intro ⟨hne, _, _⟩
  exact hne rfl

/-- Grounding is strictly asymmetric: if `s` grounds `x`, then `x` cannot ground `s`. -/
theorem groundInitiation_asymmetric {s x : Entity} :
    GroundInitiation s x → ¬ GroundInitiation x s := by
  intro ⟨_, hs_init, hx_der⟩ ⟨_, hx_init, hs_der⟩
  cases x with
  | ofSubject sx =>
    have hx_init' : InitiatingPerson sx := hx_init
    have hx_der' : ¬ InitiatingPerson sx := hx_der
    exact hx_der' hx_init'
  | ofAtom n =>
    nomatch hx_init

/-- Grounding is transitive: initiation grounding chains compose. -/
theorem groundInitiation_transitive {a b c : Entity} :
    GroundInitiation a b → GroundInitiation b c → GroundInitiation a c := by
  intro ⟨_, ha_init, hb_der⟩ ⟨_, hb_init, hc_der⟩
  cases b with
  | ofSubject sb =>
    have hb_init' : InitiatingPerson sb := hb_init
    have hb_der' : ¬ InitiatingPerson sb := hb_der
    exact False.elim (hb_der' hb_init')
  | ofAtom n =>
    nomatch hb_init

/-- The Origin strictly grounds every posited content via initiation dependence. -/
theorem origin_grounds_posited_init (q : Prop) :
    GroundInitiation (EntityOf (Sum.inl ())) (EntityOf (Sum.inr q)) := by
  refine ⟨?_, origin_initiates, posited_is_derived q⟩
  intro h
  nomatch h

/-- The Origin strictly grounds every atomic entity via initiation dependence. -/
theorem origin_grounds_atom_init (n : Nat) :
    GroundInitiation (EntityOf (Sum.inl ())) (Entity.ofAtom n) := by
  refine ⟨?_, origin_initiates, atom_is_derived n⟩
  intro h
  nomatch h

/-- The Origin strictly grounds all entities distinct from itself. -/
theorem origin_grounds_all_distinct_init (x : Entity) (hne : x ≠ EntityOf (Sum.inl ())) :
    GroundInitiation (EntityOf (Sum.inl ())) x := by
  cases x with
  | ofSubject s =>
    cases s with
    | inl u => cases u; exact False.elim (hne rfl)
    | inr q => exact origin_grounds_posited_init q
  | ofAtom n => exact origin_grounds_atom_init n

/-- The Origin is strictly ungrounded: no entity can ground the unconditioned origin. -/
theorem origin_ungrounded_init (y : Entity) :
    ¬ GroundInitiation y (EntityOf (Sum.inl ())) := by
  intro ⟨_, _, hy_der⟩
  have horig : InitiatingPerson (Sum.inl ()) := origin_is_initiating_person
  exact hy_der horig

/-- Ultimate Ground under Initiation:
    An entity is the Ultimate Ground iff it is necessary, strictly grounds all entities
    distinct from itself, and is not grounded by any entity. -/
def UltimateGroundInit (u : Entity) : Prop :=
  NecessaryEntity u ∧
  (∀ x : Entity, x ≠ u → GroundInitiation u x) ∧
  (¬ ∃ y : Entity, GroundInitiation y u)

/-- The Ultimate Ground exists under genuine Initiation Grounding! -/
theorem ultimateGroundInit_exists : ∃ u : Entity, UltimateGroundInit u := by
  refine ⟨EntityOf (Sum.inl ()), subject_is_necessary (Sum.inl ()),
          origin_grounds_all_distinct_init, ?_⟩
  intro ⟨y, hy⟩
  exact origin_ungrounded_init y hy

end Logos.SpikeGap7
