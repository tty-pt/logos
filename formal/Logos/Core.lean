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

`T : Prop → Prop` is a *definition* (E0, 2026-09-15): the identity
`def T p := p`. This is the D2 consistency model (T as identity on
`{True, False}`) made definitional. The T-schema `tschema : T p ↔ p` then
becomes a theorem (`Iff.rfl`). No self-referential fixed point is derivable:
Lean's `Prop` has no such proposition assumed to exist, so the liar cannot
form — the exact requirement of a stratified theory of truth (Tarski/Gödel).

Why `p` and not a primitive predicate: the former hypothesis `tschema` was
the *single vulnerable premise* a skeptic could deny without destroying the
act of denying (§29 criterion). Making it a definition removes the attack
surface: the self-refutation core (¬N_T ∧ ¬N_F, "há certo e há errado")
now rests on pure classical logic (§10 bivalence). The world-level
truthmaker semantics (`Logos.Semantics`/`Truthmaker`) are independent of
`T` and carry the genuine modality. The earlier `#print axioms` rows
read `{T, tschema}`; they now read `CL` or `{}` (see GAPMAP.md).

N_T is the absolute "nothing is true"; N_F is "nothing is false"
(under bivalence, falsity = untruth, so N_F := ∀p, T p).
-/

namespace Logos.Core

/-- Truth, *defined* as identity (E0, 2026-09-15): `T p` is `p` itself.
    The proposition/truth gap of the old primitive is made definitional —
    the D2 consistency model adopted as the definition. -/
def T (p : Prop) : Prop := p

/-- T-schema (theorem under E0): `T p ↔ p` unfolds to the identity. -/
theorem tschema (p : Prop) : T p ↔ p := Iff.rfl

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
-- P1/P2 of poem.txt — the two absolutes cannot stand together
-- ---------------------------------------------------------------------------

/-- `¬(N_T ∨ N_F)`: it is not the case that (either nothing is true or nothing
    is false) — the poem's "p1 ∨ p2 is a contradiction"; classically from
    `notNothingTrue` (C2) and `notEverythingTrue` (C6). -/
theorem negatedAbsolutes : ¬ (N_T ∨ N_F) := by
  intro h
  cases h with
  | inl hT => exact notNothingTrue hT
  | inr hF => exact notEverythingTrue hF

/-- Both sides of the distinction are non-empty: there is truth AND there is
    falsehood ("há certo e há errado"), from C3 and C7. -/
theorem someTruthAndSomeFalsehood : (∃ p : Prop, T p) ∧ (∃ q : Prop, IsFalse q) :=
  ⟨someTrue, someFalse⟩

/-- Right AND wrong both obtain: `¬N_T ∧ ¬N_F`, classically from
    `¬(N_T ∨ N_F)` — the direct witness for the poem's P2 conclusion
    "há certo e há errado". -/
theorem rightWrongDistinction : ¬ N_T ∧ ¬ N_F :=
  ⟨notNothingTrue, notEverythingTrue⟩

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