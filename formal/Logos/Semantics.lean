/-
# Logos.Semantics — Level 1a: object-language syntax and classical semantics

Proves base.txt §22–§23 (necessity of the excluded middle and of
non-contradiction) in a world-based semantics. This module is also the
consistency model ("face-value model") behind the truthmaker axioms of
`Logos.Truthmaker`.

Design (see DESIGN.md, D0/D6):
  * `Form` is a *code* type for formulas: the object language is kept distinct
    from Lean's `Prop`, so truth-at-a-world never conflates levels.
  * `Satisfies` is defined directly by recursion, so the Tarskian clauses
    (`sat_not`, `sat_and`, ...) hold *definitionally* (`Iff.rfl`) — no
    automation is needed and nothing depends on simp-set strength.
-/

import Logos.Core

namespace Logos.Semantics

/-- Object-language formula codes. -/
inductive Form : Type
  | atom : Nat → Form
  | not  : Form → Form
  | and  : Form → Form → Form
  | or   : Form → Form → Form
  | imp  : Form → Form → Form
  deriving DecidableEq, Repr

open Form

/-- Classical truth values. -/
inductive TV : Type
  | t
  | f
  deriving DecidableEq, Repr

open TV

/-- A possible world is a valuation of all atoms. -/
abbrev World : Type := Nat → TV

/-- Satisfaction, by structural recursion (Tarskian clauses, classical). -/
def Satisfies : World → Form → Prop
  | w, Form.atom n => w n = TV.t
  | w, Form.not φ => ¬ Satisfies w φ
  | w, Form.and φ ψ => Satisfies w φ ∧ Satisfies w ψ
  | w, Form.or φ ψ => Satisfies w φ ∨ Satisfies w ψ
  | w, Form.imp φ ψ => Satisfies w φ → Satisfies w ψ

/-- Truth at a world. -/
def TrueAt (w : World) (φ : Form) : Prop := Satisfies w φ

/-- Falsity at a world. -/
def FalseAt (w : World) (φ : Form) : Prop := ¬ Satisfies w φ

/-- Necessity (S5-lite): true in every world. -/
def NecessarilyTrue (φ : Form) : Prop := ∀ w : World, TrueAt w φ

/-- Impossible: false in every world. -/
def NecessarilyFalse (φ : Form) : Prop := ∀ w : World, FalseAt w φ

-- Semantic clauses (definitional).

theorem sat_not : Satisfies w (Form.not φ) ↔ ¬ Satisfies w φ := Iff.rfl

theorem sat_and : Satisfies w (Form.and φ ψ) ↔ Satisfies w φ ∧ Satisfies w ψ := Iff.rfl

theorem sat_or : Satisfies w (Form.or φ ψ) ↔ Satisfies w φ ∨ Satisfies w ψ := Iff.rfl

theorem sat_imp : Satisfies w (Form.imp φ ψ) ↔ (Satisfies w φ → Satisfies w ψ) := Iff.rfl

/-- §22 — the excluded middle is necessary: `⊨ □(φ ∨ ¬φ)`. -/
theorem lawExcludedMiddle (φ : Form) : NecessarilyTrue (Form.or φ (Form.not φ)) := by
  intro w
  unfold TrueAt
  rw [sat_or, sat_not]
  exact Classical.em (Satisfies w φ)

/-- §23 — non-contradiction is impossible: `⊨ □¬(φ ∧ ¬φ)` world-wise falsity. -/
theorem nonContradiction (φ : Form) : NecessarilyFalse (Form.and φ (Form.not φ)) := by
  intro w
  unfold FalseAt
  rw [sat_and, sat_not]
  intro h
  exact h.2 h.1

end Logos.Semantics

-- Axiom footprint audit
#print axioms Logos.Semantics.lawExcludedMiddle
#print axioms Logos.Semantics.nonContradiction
