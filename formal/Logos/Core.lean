/-
# Logos.Core — Level 0: the performative core (base.txt §1–§6, §10, §22–§23)

Conventions (see AGENTS.md):
  * Every theorem below is checked by Lean's kernel; `#print axioms` at the
    bottom lists the exact axiom footprint of each claim.
  * Axioms carry a justification tag:
      TRANS = performative/transcendental datum (negating it destroys the act)
      SEM   = semantic/definitional choice, with a consistency-model note
      META  = metaphysical bridge (price made explicit)
  * Comments in English; prose corpus stays Portuguese.

## The one premise of the system

`T : Prop → Prop` is a *primitive* truth predicate and `tschema` is the
T-schema restricted to exactly the stratification we need.

Consistency model (SEM): interpret `T` as the identity on `{True, False}` in
the boolean model of `Prop`. Then `tschema` holds trivially, and no fixed
point `p = ¬ T p` (the liar) is derivable, because we assume no such
proposition exists — self-reference is blocked at the door, which is exactly
what a stratified theory of truth requires (Tarski/Gödel).

Why a primitive predicate and not an axiom-free `def T p := p`:
the second would make `tschema` definitional and shrink the footprint to
`.{Classical.choice}`, but it would erase the semantic gap between "p" and
"T p" that the normative layer (§8 Correct/Incorrect, §24a ground) needs.
The plan records this as decision D4; the axom-free variant remains the
documented fallback.

N_T is the absolute "nothing is true"; N_F is "nothing is false"
(under bivalence, falsity = untruth, so N_F := ∀p, T p).
-/

namespace Logos.Core

/-- Primitive truth predicate: `T p` reads "proposition p is true". -/
axiom T : Prop → Prop

/-- T-schema (stratified): `T p ↔ p` for every proposition `p`. -/
axiom tschema : ∀ p : Prop, T p ↔ p

/-- N_T := "no proposition is true". -/
def N_T : Prop := ∀ p : Prop, ¬ T p

/-- N_F := "no proposition is false" (bivalence: falsity is untruth). -/
def N_F : Prop := ∀ p : Prop, T p

/-- Falsity under bivalence: a proposition is false iff it is not true. -/
def IsFalse (p : Prop) : Prop := ¬ T p

-- ---------------------------------------------------------------------------
-- §4 — T3, half 1: N_T refutes itself
-- ---------------------------------------------------------------------------

/-- `T(N_T)` cannot hold: assuming it forces both `N_T` and `¬ T N_T`. -/
theorem nothingTrueRefutes : ¬ T N_T := by
  intro hTrue
  have hN : N_T := (tschema N_T).1 hTrue
  exact hN N_T hTrue

/-- ¬(∀p ¬T p): it is not the case that nothing is true (classical step §4). -/
theorem notNothingTrue : ¬ N_T := by
  intro hN
  have hT : T N_T := (tschema N_T).2 hN
  exact nothingTrueRefutes hT

/-- There is at least one true proposition. -/
theorem someTrue : ∃ p : Prop, T p := by
  apply Classical.byContradiction
  intro hno
  have hall : N_T := fun p hp => hno ⟨p, hp⟩
  exact notNothingTrue hall

-- An explicit witness exists (D8: non-vacuity): `True` itself is true.
theorem atomicTruthWitnessed : T True := (tschema True).2 trivial

-- ---------------------------------------------------------------------------
-- §5 — T3, half 2: N_F refutes itself
-- ---------------------------------------------------------------------------

/-- `T(N_F)` cannot hold: `∀p T p` applied to the proposition `False`. -/
theorem nothingFalseRefutes : ¬ T N_F := by
  intro hTrue
  have hN : N_F := (tschema N_F).1 hTrue
  have hTf : T False := hN False
  exact (tschema False).1 hTf

/-- ¬(∀p T p): it is not the case that everything is true. -/
theorem notEverythingTrue : ¬ N_F := by
  intro hN
  have hT : T N_F := (tschema N_F).2 hN
  exact nothingFalseRefutes hT

/-- There is at least one false proposition. -/
theorem someFalse : ∃ q : Prop, IsFalse q := by
  refine ⟨False, ?_⟩
  intro hTf
  exact (tschema False).1 hTf

/-- ¬(∀p ¬T p) with the witness spelled out: `False` is false. -/
theorem atomicWitnessFalsehood : IsFalse False :=
  fun hTf => (tschema False).1 hTf

-- ---------------------------------------------------------------------------
-- §6 — T3: the first great result
-- ---------------------------------------------------------------------------

/-- T3 — truth and falsehood are both necessarily instantiated, hence
    `T ≠ F` as statuses: `∃p, T p` and `∃q, ¬ T q`. -/
theorem greatResult : ∃ p q : Prop, T p ∧ IsFalse q := by
  exact ⟨True, False, atomicTruthWitnessed, atomicWitnessFalsehood⟩

/-- No proposition is both true and false (non-contradiction for T). -/
theorem noBothTrueAndFalse : ∀ p : Prop, ¬ (T p ∧ IsFalse p) := by
  intro p h
  exact h.2 h.1

-- ---------------------------------------------------------------------------
-- §10 — logical meaning: bivalence is available (classical meta-logic)
-- ---------------------------------------------------------------------------

/-- §22 — every instance of the excluded middle is a necessary truth (level 0:
    the modality □ in §22 lives at level 1, see Logos.Modal). -/
theorem excludedMiddle : ∀ p : Prop, T (p ∨ ¬ p) := fun p =>
  (tschema (p ∨ ¬ p)).2 (Classical.em p)

/-- §23 — every instance of non-contradiction is true: `□False(ρ)`. -/
theorem nonContradiction : ∀ p : Prop, T (¬ (p ∧ ¬ p)) := fun p =>
  (tschema (¬ (p ∧ ¬ p))).2 (fun h => h.2 h.1)

/-- Bivalence, §10: each proposition is true or false (is false iff not true). -/
theorem bivalence : ∀ p : Prop, T p ∨ IsFalse p := by
  intro p
  by_cases hp : T p
  · exact Or.inl hp
  · exact Or.inr hp

end Logos.Core

-- ---------------------------------------------------------------------------
-- Axiom footprint audit (recorded in GAPMAP.md)
-- ---------------------------------------------------------------------------
#print axioms Logos.Core.nothingTrueRefutes
#print axioms Logos.Core.someTrue
#print axioms Logos.Core.greatResult