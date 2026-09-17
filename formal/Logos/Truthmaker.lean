/-
# Logos.Truthmaker — Level 1b: truthmaker semantics (base.txt §24a, §22–§23)

Truth is *defined* as being-made-true. Since A2 (2026-09-16) the
definition is structural: an **atom** is true in `w` iff some entity exists
in `w` and grounds it; the connectives are Tarskian-compositional **by
definition** (mirroring `Semantics.Satisfies`). The former SEM axioms
`AxOr`/`AxAnd`/`AxNot` become `Iff.rfl` theorems of this definition, and
`lawExcludedMiddle`/`nonContradiction` are re-proved by definitional
reduction. The truth-maker principle of §24a holds **atom-only**
(`groundPrinciple_atom`); the old formula-level version (`groundPrinciple`)
is deliberately dropped — composite truth is compositional (`Ground e (or …)`
is neither asserted nor denied; only atoms carry existential grounding).

Consistency model (SEM, D6/Q1): the "face-value" model. Since C2
(2026-09-15) the carrier is *defined*, not primitive: `Entity := Subject`
(the Q2/D11 identification becomes definitional), so `EntityOf` is the
identity. `Ground` remains the one real semantics axiom; `ExistsAt` is now the
agency definition (esse est agere, 2026-09-17). There is
no provable `TrueAt = Satisfies` ∈-correspondence in general — the
entity-vocabulary is untouched by the semantics.

Import note: `Logos.Truthmaker` imports `Logos.Agency` (no cycle; Agency
imports only Core).
-/

import Logos.Core
import Logos.Semantics
import Logos.Agency

namespace Logos.Truthmaker

open Logos.Semantics (Form World)
open Logos.Agency (Subject A)

/-- Grounding entities (truthmakers). World-rigid: what an entity *grounds*
    does not vary across worlds; only its existence does (D6).
    Defined (C2, 2026-09-15): the carrier is the subject type itself — the
    Q2/D11 identification (`Entity := Subject`) made definitional. -/
def Entity : Type := Subject

/--Tag: VOCAB

 The truthmaker relation — an entity grounding a formula.

 `Ground e φ`: entity `e` grounds formula `φ`. -/
axiom Ground : Subject → Form → Prop

/--Existence as agency (esse est agere): an entity exists in a world iff it acts.

 `ExistsAt w e`: entity `e` exists in world `w`. Definitional (batch
    esse-est-agere, 2026-09-17): to be is to act — `∃ p, A e p`. The
    world-index is vacuous by principle: `Means` takes no `World` parameter,
    so agency is not world-located; the existential does the real work (only
    actors exist). Former VOCAB axiom, now def — this supplies the missing
    Means→ExistsAt rule (M3 PERSON_PERSISTS), dissolving `AxPersonStability`. -/
def ExistsAt (_w : World) (s : Subject) : Prop := ∃ p : Prop, A s p

/-- Truth as truthmaking, structurally defined (A2, 2026-09-16): an atom is
    true in `w` iff some entity grounding it exists there; the connectives are
    Tarskian-compositional by definition. The former axioms AxOr/AxAnd/AxNot
    became `Iff.rfl` theorems of this definition. -/
def TrueAt (w : World) : Form → Prop
  | Form.atom n => ∃ e : Entity, ExistsAt w e ∧ Ground e (Form.atom n)
  | Form.not φ   => ¬ TrueAt w φ
  | Form.and φ ψ => TrueAt w φ ∧ TrueAt w ψ
  | Form.or φ ψ  => TrueAt w φ ∨ TrueAt w ψ
  | Form.imp φ ψ => TrueAt w φ → TrueAt w ψ

/-- Necessarily true: made true in every world. -/
def NecessarilyTrue (φ : Form) : Prop := ∀ w : World, TrueAt w φ

/-- Necessarily false: made true in no world. -/
def NecessarilyFalse (φ : Form) : Prop := ∀ w : World, ¬ TrueAt w φ

/--Every atomic truth is grounded: where an atom is true, an entity exists there that grounds it.

 §24a — the truth-maker principle, atom-restricted (A2): the truth of an
    atom in any world entails a grounder existing there. (The former
    formula-level `groundPrinciple` is deliberately dropped: composite truth
    is compositional and carries no existential grounding claim — see
    DETAILS.md §6.1/§6.3.) The proof needs no substantive axiom: it is a
    definitional collapse — `TrueAt w (atom n)` *is* the existential
    ground-clause, so the principle is `P → P`; denying it refutes itself
    (`noGround_selfRefutes` below, GAPMAP.md C60). -/
theorem groundPrinciple_atom (w : World) (n : Nat) :
    TrueAt w (Form.atom n) → ∃ e : Entity, ExistsAt w e ∧ Ground e (Form.atom n) := by
  intro ht
  change ∃ e : Entity, ExistsAt w e ∧ Ground e (Form.atom n) at ht
  exact ht

/--The denial that atomic truth is grounded refutes itself: where an atom is true, no world lacks a grounder for it.

 §24a — RAA form of the truth-maker principle. Unfolding `TrueAt w (atom n)`,
    the denial is `(∃e, ExistsAt w e ∧ Ground e (atom n)) ∧ ¬(∃e, …)` — a
    contradiction by definition. No substantive axiom: the kernel footprint is
    only the vocabulary constants the statement itself mentions (GAPMAP.md
    C60 / C15 justification). -/
theorem noGround_selfRefutes :
    ¬ (∃ (w : World) (n : Nat), TrueAt w (Form.atom n) ∧
        ¬ (∃ e : Entity, ExistsAt w e ∧ Ground e (Form.atom n))) := by
  rintro ⟨w, n, ht, hn⟩
  change ∃ e : Entity, ExistsAt w e ∧ Ground e (Form.atom n) at ht
  exact hn ht

-- Truthmaker clauses for the connectives (definitional; former SEM axioms AxOr/AxAnd/AxNot, demoted to theorems by A2).

/-- truthmaker clause for disjunction (former axiom AxOr; now proved). -/
theorem sat_ground_or {w : World} {φ ψ : Form} :
    TrueAt w (Form.or φ ψ) ↔ TrueAt w φ ∨ TrueAt w ψ := Iff.rfl

/-- truthmaker clause for conjunction (former axiom AxAnd; now proved). -/
theorem sat_ground_and {w : World} {φ ψ : Form} :
    TrueAt w (Form.and φ ψ) ↔ TrueAt w φ ∧ TrueAt w ψ := Iff.rfl

/-- truthmaker clause for negation (former axiom AxNot; now proved). -/
theorem sat_ground_not {w : World} {φ : Form} :
    TrueAt w (Form.not φ) ↔ ¬ TrueAt w φ := Iff.rfl

/-- truthmaker clause for implication. -/
theorem sat_ground_imp {w : World} {φ ψ : Form} :
    TrueAt w (Form.imp φ ψ) ↔ (TrueAt w φ → TrueAt w ψ) := Iff.rfl

/--In every world, 'φ or not-φ' is true — composite truth is Tarskian-compositional.

 §22, at the truthmaker level: the excluded middle is always made true.
    PROVEN (A2), classical only (`CL`). -/
theorem lawExcludedMiddle (φ : Form) : NecessarilyTrue (Form.or φ (Form.not φ)) := by
  intro w
  exact Classical.em (TrueAt w φ)

/--In every world, 'φ and not-φ' cannot be true.

 §23, at the truthmaker level: a contradiction is made true in no world.
    PROVEN (A2). -/
theorem nonContradiction (φ : Form) : NecessarilyFalse (Form.and φ (Form.not φ)) := by
  intro w
  intro h
  exact h.2 h.1

end Logos.Truthmaker

-- Axiom footprint audit
#print axioms Logos.Truthmaker.groundPrinciple_atom
#print axioms Logos.Truthmaker.noGround_selfRefutes
#print axioms Logos.Truthmaker.lawExcludedMiddle
#print axioms Logos.Truthmaker.nonContradiction
