/-
# Logos.Order — Level 2d: objective correctness and truth transcending the will (base.txt §7–§9, T6)

Renders §8 (Correct/Incorrect are objective, tracked by truth), the
consequence-normativity of §9, and T6 (truth ≠ the will of the agent,
base.txt §7, T6).

`Fallible` may be opaque but is realized by a trivial consistent model:
`Fallible _ p := (p = False)` (see DESIGN.md, consistency note).
-/

import Logos.Core
import Logos.Agency

namespace Logos.Order

open Logos.Core (T IsFalse tschema someTrue)
open Logos.Agency (Subject A)

/-- Correctness: asserting p is correct iff p is true (§8). -/
def Correct (_s : Subject) (p : Prop) : Prop := T p

/-- Incorrectness: asserting p is incorrect iff p is false (§8). -/
def Incorrect (_s : Subject) (p : Prop) : Prop := IsFalse p

/-- `Fallible s p`: subject s is able to assert p. Deliberately opaque and
    not tied to truth by definition — that non-tie IS the content of T6. -/
axiom Fallible : Subject → Prop → Prop

/-- Fallibility (T6 premise): some subject can assert some false content.
    Consistency model: `Fallible _ p := (p = False)` satisfies it, since
    `False` is false (Core.atomicWitnessFalsehood). -/
axiom fallible_false : ∃ s : Subject, ∃ p : Prop, Fallible s p ∧ IsFalse p

/-- T6 — truth is not created by asserting: assertion ⇒ truth fails. -/
theorem T6_fallibility : ¬ (∀ s : Subject, ∀ p : Prop, Fallible s p → T p) := by
  intro h
  obtain ⟨s, p, hf, hnt⟩ := fallible_false
  exact hnt (h s p hf)

/-- T6, second form: `Truth ≠ WillOfAgent` — no equivalence can hold between
    willing-asserting and being true. -/
theorem T6_truthTranscendsWill : ¬ (∀ s : Subject, ∀ p : Prop, Fallible s p ↔ T p) := by
  intro h
  obtain ⟨s, p, hf, hnt⟩ := fallible_false
  exact hnt ((h s p).1 hf)

/-- §8 — Correct ≠ Incorrect: the two normative predicates are distinct. -/
theorem correctness_distinct : ¬ (∀ s : Subject, ∀ p : Prop, Correct s p ↔ Incorrect s p) := by
  intro h
  obtain ⟨p, hp⟩ := someTrue
  obtain ⟨s, _, _⟩ := Logos.Agency.cogito
  exact (h s p).1 hp hp

/-- §9 — logical consequence preserves truth (rendering: the object-level
    consequence `p₁, p₂ ⊢ q` carries truth upward). -/
theorem consequence_preserves_truth {p₁ p₂ q : Prop}
    (himp : p₁ → p₂ → q) (h1 : T p₁) (h2 : T p₂) : T q := by
  exact (tschema q).2 (himp ((tschema p₁).1 h1) ((tschema p₂).1 h2))

end Logos.Order

-- Axiom footprint audit
#print axioms Logos.Order.T6_fallibility
#print axioms Logos.Order.T6_truthTranscendsWill
#print axioms Logos.Order.correctness_distinct
#print axioms Logos.Order.consequence_preserves_truth
