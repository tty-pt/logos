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

open Logos.Semantics (Form World Satisfies)
open Logos.Agency (Subject)

/-- Grounding entities (truthmakers). World-rigid: what an entity *grounds*
    does not vary across worlds; only its existence does (D6).
    The general ontological type: subjects (capable of agency) are embedded
    via `Entity.ofSubject`, while non-agent worldly entities (such as atomic
    facts/states) are represented via `Entity.ofAtom`. -/
inductive Entity : Type
  | ofSubject (s : Subject) : Entity
  | ofAtom (n : Nat) : Entity

/-- The canonical embedding of subjects into entities (Q2 bridge). -/
def EntityOf (s : Subject) : Entity := Entity.ofSubject s

instance : Coe Subject Entity := ⟨EntityOf⟩

/--Tag: VOCAB

 The truthmaker relation — an entity grounding a formula.

 `Ground e φ`: entity `e` grounds formula `φ`. -/
axiom Ground : Entity → Form → Prop

/--Existence of an entity in a world, defined independently of agency.

 `ExistsAt w e`: entity `e` exists in world `w`.
 Subjects exist across all worlds; atomic entities exist at worlds where
 their corresponding valuation evaluates to true. -/
def ExistsAt (w : World) : Entity → Prop
  | Entity.ofSubject _ => True
  | Entity.ofAtom n => w n = Logos.Semantics.TV.t

/-- Truth at a world, defined by standard Tarskian semantic satisfaction,
    independent of existential grounding (2026-09-17). -/
def TrueAt (w : World) (φ : Form) : Prop := Satisfies w φ

/-- Necessarily true: satisfied in every world. -/
def NecessarilyTrue (φ : Form) : Prop := ∀ w : World, TrueAt w φ

/-- Necessarily false: satisfied in no world. -/
def NecessarilyFalse (φ : Form) : Prop := ∀ w : World, ¬ TrueAt w φ

/--Tag: SEM
The truthmaker principle: truth is grounded in reality.

 If a formula is satisfied at world `w`, there is some entity `e` existing in `w` that grounds it.
 This is a substantive semantic bridge (`Tag: SEM`), not a definitional collapse.

 Philosophical cost: the price of a realist reading of correspondence — the
    bridge commits Γ to a non-vacuous grounding relation between satisfied
    formulas and existing entities, without deciding what kind of entities
    those must be. A coherence or deflationary account of truth is thereby
    excluded; the principle is posited, not derived. -/
axiom Truthmaker : ∀ (w : World) (φ : Form),
  Satisfies w φ → ∃ e : Entity, ExistsAt w e ∧ Ground e φ

/--Every atomic truth is grounded: where an atom is true, an entity exists there that grounds it.

 §24a — the truth-maker principle, atom-restricted.
    Derived under the substantive semantic bridge `Truthmaker`. -/
theorem groundPrinciple_atom (w : World) (n : Nat) :
    TrueAt w (Form.atom n) → ∃ e : Entity, ExistsAt w e ∧ Ground e (Form.atom n) :=
  Truthmaker w (Form.atom n)

/--The denial that atomic truth is grounded refutes itself under the Truthmaker bridge.

 §24a — RAA form of the truth-maker principle. -/
theorem noGround_selfRefutes :
    ¬ (∃ (w : World) (n : Nat), TrueAt w (Form.atom n) ∧
        ¬ (∃ e : Entity, ExistsAt w e ∧ Ground e (Form.atom n))) := by
  rintro ⟨w, n, ht, hn⟩
  exact hn (Truthmaker w (Form.atom n) ht)

-- Truthmaker clauses for the connectives (definitional via Semantics.Satisfies).

/-- truthmaker clause for disjunction. -/
theorem sat_ground_or {w : World} {φ ψ : Form} :
    TrueAt w (Form.or φ ψ) ↔ TrueAt w φ ∨ TrueAt w ψ := Iff.rfl

/-- truthmaker clause for conjunction. -/
theorem sat_ground_and {w : World} {φ ψ : Form} :
    TrueAt w (Form.and φ ψ) ↔ TrueAt w φ ∧ TrueAt w ψ := Iff.rfl

/-- truthmaker clause for negation. -/
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
  rintro ⟨h1, h2⟩
  exact h2 h1

end Logos.Truthmaker

-- Axiom footprint audit
#print axioms Logos.Truthmaker.groundPrinciple_atom
#print axioms Logos.Truthmaker.noGround_selfRefutes
#print axioms Logos.Truthmaker.lawExcludedMiddle
#print axioms Logos.Truthmaker.nonContradiction
