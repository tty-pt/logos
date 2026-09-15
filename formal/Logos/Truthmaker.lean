/-
# Logos.Truthmaker — Level 1b: truthmaker semantics (base.txt §24a, §22–§23)

Truth is *defined* as being-made-true: `φ is true in w` iff some entity
exists in `w` and grounds `φ`. On that definition the truth-maker principle
of §24a is a lemma, not a hidden assumption:

    groundPrinciple : TrueAt w φ → ∃ e, ExistsAt w e ∧ Ground e φ

Consistency model (SEM, D6/Q1): the "face-value" model with
`Entity := Form`, `ExistsAt w e := (eval w e = t)`, `Ground e φ := (e = φ)`.
There `TrueAt w φ ↔ eval w φ = t`, and the connective axioms below follow
from the classical satisfaction clauses of `Logos.Semantics`. Hence the
axiom system is satisfied by an ordinary Tarskian model.
-/

import Logos.Core
import Logos.Semantics

namespace Logos.Truthmaker

open Logos.Semantics (Form World)

/-- Grounding entities (truthmakers). World-rigid: what an entity *grounds*
    does not vary across worlds; only its existence does (D6). -/
axiom Entity : Type

/-- `Ground e φ`: entity `e` grounds formula `φ`. -/
axiom Ground : Entity → Form → Prop

/-- `ExistsAt w e`: entity `e` exists in world `w`. -/
axiom ExistsAt : World → Entity → Prop

/-- Truth as truthmaking: φ is true in w iff some entity grounding it exists there. -/
def TrueAt (w : World) (φ : Form) : Prop := ∃ e : Entity, ExistsAt w e ∧ Ground e φ

/-- Necessarily true: made true in every world. -/
def NecessarilyTrue (φ : Form) : Prop := ∀ w : World, TrueAt w φ

/-- Necessarily false: made true in no world. -/
def NecessarilyFalse (φ : Form) : Prop := ∀ w : World, ¬ TrueAt w φ

/-- §24a — the truth-maker principle, unfolding the definition of truth. -/
theorem groundPrinciple (w : World) (φ : Form) :
    TrueAt w φ → ∃ e : Entity, ExistsAt w e ∧ Ground e φ := fun h => h

-- Semantic bridge axioms for the connectives (SEM; see consistency model above).

/-- A disjunction is true iff one of its disjuncts is made true. -/
axiom AxOr : ∀ {w : World} {φ ψ : Form}, TrueAt w (Form.or φ ψ) ↔ TrueAt w φ ∨ TrueAt w ψ

/-- A conjunction is true iff both conjuncts are made true. -/
axiom AxAnd : ∀ {w : World} {φ ψ : Form}, TrueAt w (Form.and φ ψ) ↔ TrueAt w φ ∧ TrueAt w ψ

/-- A negation is true iff its prejacent is not made true. -/
axiom AxNot : ∀ {w : World} {φ : Form}, TrueAt w (Form.not φ) ↔ ¬ TrueAt w φ

/-- §22, at the truthmaker level: the excluded middle is always made true. -/
theorem lawExcludedMiddle (φ : Form) : NecessarilyTrue (Form.or φ (Form.not φ)) := by
  intro w
  rw [AxOr, AxNot]
  exact Classical.em (TrueAt w φ)

/-- §23, at the truthmaker level: a contradiction is made true in no world. -/
theorem nonContradiction (φ : Form) : NecessarilyFalse (Form.and φ (Form.not φ)) := by
  intro w
  rw [AxAnd, AxNot]
  intro h
  exact h.2 h.1

end Logos.Truthmaker

-- Axiom footprint audit
#print axioms Logos.Truthmaker.groundPrinciple
#print axioms Logos.Truthmaker.lawExcludedMiddle
#print axioms Logos.Truthmaker.nonContradiction