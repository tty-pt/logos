/-
# Logos.Entity — Level 1b: entity and modal semantics

Structural semantics for entities, world-indexed existence, and modal truth.
-/

import Logos.Core
import Logos.Semantics
import Logos.Agency

namespace Logos.Entity

open Logos.Semantics (Form World Satisfies)
open Logos.Agency (Subject)

/-- General ontological type of entities. World-rigid.
    Subjects (capable of agency) are embedded via `Entity.ofSubject`,
    while non-agent worldly entities are represented via `Entity.ofAtom`. -/
inductive Entity : Type
  | ofSubject (s : Subject) : Entity
  | ofAtom (n : Nat) : Entity

/-- The canonical embedding of subjects into entities. -/
def EntityOf (s : Subject) : Entity := Entity.ofSubject s

instance : Coe Subject Entity := ⟨EntityOf⟩

/-- The actual world valuation: all atoms true. -/
def actualWorld : World := fun _ => Logos.Semantics.TV.t

/-- World-relative existence of subjects:
    A subject is actualized at the actual world, but does not automatically exist across all possible worlds. -/
def SubjectExistsAt (w : World) (_s : Subject) : Prop :=
  w = actualWorld

/-- Existence of an entity in a world:
    Subjects exist only at worlds where SubjectExistsAt holds;
    atomic entities exist at worlds where their atomic valuation holds. -/
def EntityExistsAt (w : World) : Entity → Prop
  | Entity.ofSubject s => SubjectExistsAt w s
  | Entity.ofAtom n => w n = Logos.Semantics.TV.t

/-- ExistsAt is the canonical entity existence relation across worlds. -/
def ExistsAt (w : World) (e : Entity) : Prop := EntityExistsAt w e

/-- Truth at a world, defined by standard Tarskian semantic satisfaction. -/
def TrueAt (w : World) (φ : Form) : Prop := Satisfies w φ

/-- Necessarily true: satisfied in every world. -/
def NecessarilyTrue (φ : Form) : Prop := ∀ w : World, TrueAt w φ

/-- Necessarily false: satisfied in no world. -/
def NecessarilyFalse (φ : Form) : Prop := ∀ w : World, ¬ TrueAt w φ

-- Semantic satisfaction clauses for the connectives (definitional via Semantics.Satisfies).

/-- satisfaction clause for disjunction. -/
theorem sat_or {w : World} {φ ψ : Form} :
    TrueAt w (Form.or φ ψ) ↔ TrueAt w φ ∨ TrueAt w ψ := Iff.rfl

/-- satisfaction clause for conjunction. -/
theorem sat_and {w : World} {φ ψ : Form} :
    TrueAt w (Form.and φ ψ) ↔ TrueAt w φ ∧ TrueAt w ψ := Iff.rfl

/-- satisfaction clause for negation. -/
theorem sat_not {w : World} {φ : Form} :
    TrueAt w (Form.not φ) ↔ ¬ TrueAt w φ := Iff.rfl

/-- satisfaction clause for implication. -/
theorem sat_imp {w : World} {φ ψ : Form} :
    TrueAt w (Form.imp φ ψ) ↔ (TrueAt w φ → TrueAt w ψ) := Iff.rfl

/-- Backward-compatibility aliases for satisfaction clauses. -/
theorem sat_ground_or {w : World} {φ ψ : Form} :
    TrueAt w (Form.or φ ψ) ↔ TrueAt w φ ∨ TrueAt w ψ := Iff.rfl

theorem sat_ground_and {w : World} {φ ψ : Form} :
    TrueAt w (Form.and φ ψ) ↔ TrueAt w φ ∧ TrueAt w ψ := Iff.rfl

theorem sat_ground_not {w : World} {φ : Form} :
    TrueAt w (Form.not φ) ↔ ¬ TrueAt w φ := Iff.rfl

theorem sat_ground_imp {w : World} {φ ψ : Form} :
    TrueAt w (Form.imp φ ψ) ↔ (TrueAt w φ → TrueAt w ψ) := Iff.rfl

/--In every world, 'φ or not-φ' is true — composite truth is Tarskian-compositional.

 §22: the excluded middle is always true.
    PROVEN (A2), classical only (`CL`). -/
theorem lawExcludedMiddle (φ : Form) : NecessarilyTrue (Form.or φ (Form.not φ)) := by
  intro w
  exact Classical.em (TrueAt w φ)

/--In every world, 'φ and not-φ' cannot be true.

 §23: a contradiction is true in no world.
    PROVEN (A2). -/
theorem nonContradiction (φ : Form) : NecessarilyFalse (Form.and φ (Form.not φ)) := by
  intro w
  rintro ⟨h1, h2⟩
  exact h2 h1

end Logos.Entity

-- Axiom footprint audit
#print axioms Logos.Entity.lawExcludedMiddle
#print axioms Logos.Entity.nonContradiction
