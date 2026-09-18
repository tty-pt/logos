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

/--In every world, 'φ or not-φ' is true.

 §22 — the excluded middle is necessary: `⊨ □(φ ∨ ¬φ)`. -/
theorem lawExcludedMiddle (φ : Form) : NecessarilyTrue (Form.or φ (Form.not φ)) := by
  intro w
  unfold TrueAt
  rw [sat_or, sat_not]
  exact Classical.em (Satisfies w φ)

/--In every world, 'φ and not-φ' cannot be true.

 §23 — non-contradiction is impossible: `⊨ □¬(φ ∧ ¬φ)` world-wise falsity. -/
theorem nonContradiction (φ : Form) : NecessarilyFalse (Form.and φ (Form.not φ)) := by
  intro w
  unfold FalseAt
  rw [sat_and, sat_not]
  intro h
  exact h.2 h.1

-- ---------------------------------------------------------------------------
-- P2 of poem.txt — "há certo e há errado" at the world level
-- ---------------------------------------------------------------------------

/--In every world there is necessarily-true content and necessarily-false content.

 There is a necessarily-true content AND a necessarily-false one
    (the poem's "há certo E há errado" where "errado" is level-1 falsity),
    witnessed by the excluded-middle tautology and the non-contradiction
    anti-tautology, respectively. -/
theorem bothNecessarilyTrueAndFalse :
    (∃ τ : Form, NecessarilyTrue τ) ∧ (∃ ρ : Form, NecessarilyFalse ρ) := by
  constructor
  · exact ⟨Form.or (Form.atom 0) (Form.not (Form.atom 0)),
      lawExcludedMiddle (Form.atom 0)⟩
  · exact ⟨Form.and (Form.atom 0) (Form.not (Form.atom 0)),
      nonContradiction (Form.atom 0)⟩

/--Strong truth exists: some formula is true in every world — axiom-free, the
  performative "há certo E há errado" (§27, poem.txt), resident as the
  excluded-middle datum C37 (footprint {CL}). -/
theorem strongTruthExists :
    ∃ τ : Form, NecessarilyTrue τ := by
  obtain ⟨hN, _⟩ := bothNecessarilyTrueAndFalse
  exact hN

/--Denying strong truth refutes itself: it cannot be the case that no formula
  is necessarily true — the act of denying strong truth is destroyed by
  strong truth (performative retorsion of C59, footprint {CL}). -/
theorem noStrongTruth_selfRefutes :
    ¬ (¬ ∃ τ : Form, NecessarilyTrue τ) := by
  intro hDenial
  exact hDenial strongTruthExists

/--No atom is necessarily true: a world sending atom `n` to `f` refutes it.

  The atom-wall (C95): strong truth (C59) fixes the excluded-middle law,
  never an atom — the semantic course is modally free in every atomic content
  (footprint {}). -/
theorem atom_not_necessarily_true (n : Nat) : ¬ NecessarilyTrue (Form.atom n) := by
  intro h
  have hw : (fun _ : Nat => TV.f) n = TV.t := h (fun _ => TV.f)
  exact TV.noConfusion hw

/--No atom is necessarily false either: the constant-`t` world refutes it.

  The atom-wall, symmetric horn (footprint {}). -/
theorem atom_not_necessarily_false (n : Nat) : ¬ NecessarilyFalse (Form.atom n) := by
  intro h
  exact h (fun _ => TV.t) rfl

/--The atoms are modally free: no atom is fixed in either modal direction.

  The atom-wall, combined form (footprint {}). -/
theorem atoms_are_modally_free : ∀ n : Nat,
    ¬ NecessarilyTrue (Form.atom n) ∧ ¬ NecessarilyFalse (Form.atom n) :=
  fun n => ⟨atom_not_necessarily_true n, atom_not_necessarily_false n⟩

/--Strong truth exists and is not atomic content: the excluded-middle
  tautology is the witness of C59, and every atom stays modally free (footprint {CL}). -/
theorem strongTruth_is_not_atomic :
    ∃ τ : Form, NecessarilyTrue τ ∧ ∀ n : Nat, ¬ NecessarilyTrue (Form.atom n) :=
  ⟨Form.or (Form.atom 0) (Form.not (Form.atom 0)),
   lawExcludedMiddle (Form.atom 0), atom_not_necessarily_true⟩

/--Contingent content exists — the counterweight of C59 (GAPMAP.md C96): some
  formula is neither necessary nor impossible, derived from the atom-wall
  (footprint {}). -/
theorem some_formula_contingent :
    ∃ τ : Form, ¬ NecessarilyTrue τ ∧ ¬ NecessarilyFalse τ := by
  rcases atoms_are_modally_free 0 with ⟨hT, hF⟩
  exact ⟨Form.atom 0, hT, hF⟩

/--Law and contingent content coexist: the junction of C37 (the witness of
  strong truth) and C96 - some formula is necessary and some is contingent
  (footprint {CL}). -/
theorem strongTruth_and_contingent_content :
    ∃ τ : Form, NecessarilyTrue τ ∧ ∃ σ : Form, ¬ NecessarilyTrue σ ∧ ¬ NecessarilyFalse σ := by
  obtain ⟨⟨τ, hτ⟩, _⟩ := bothNecessarilyTrueAndFalse
  obtain ⟨σ, hσN, hσF⟩ := some_formula_contingent
  exact ⟨τ, hτ, σ, hσN, hσF⟩

end Logos.Semantics

-- Axiom footprint audit
#print axioms Logos.Semantics.lawExcludedMiddle
#print axioms Logos.Semantics.nonContradiction
#print axioms Logos.Semantics.bothNecessarilyTrueAndFalse
#print axioms Logos.Semantics.strongTruthExists
#print axioms Logos.Semantics.noStrongTruth_selfRefutes
#print axioms Logos.Semantics.atom_not_necessarily_true
#print axioms Logos.Semantics.atom_not_necessarily_false
#print axioms Logos.Semantics.atoms_are_modally_free
#print axioms Logos.Semantics.strongTruth_is_not_atomic
#print axioms Logos.Semantics.some_formula_contingent
#print axioms Logos.Semantics.strongTruth_and_contingent_content
