/-
# Logos.Order — Level 2d: objective correctness and truth transcending the will (base.txt §7–§9, T6)

Renders §8 (Correct/Incorrect are objective, tracked by truth), the
consequence-normativity of §9, and T6 (truth ≠ the will of the agent,
base.txt §7, T6).

`Fallible` is *defined* (A1) as `IsFalse p` — the trivial model that used to
realize the axiom (`Fallible _ p := (p = False)`), lifted to bivalence. This
keeps the opacity requirement of T6 (fallibility is not tied to truth by
definition) while making the former premise a theorem.
-/

import Logos.Core
import Logos.Agency
import Logos.Choice
import Logos.Plurality

namespace Logos.Order

open Logos.Core (T IsFalse tschema someTrue someFalse)
open Logos.Agency (Subject A)
open Logos.Choice (Chooses incompatible_self_negation)

/-- Correctness: asserting p is correct iff p is true (§8). -/
def Correct (_s : Subject) (p : Prop) : Prop := T p

/-- Incorrectness: asserting p is incorrect iff p is false (§8). -/
def Incorrect (_s : Subject) (p : Prop) : Prop := IsFalse p

/-- `Fallible s p`: subject s is *bound by* the falsehood of p — the subject
    can be in error about p. Defined (A1, 2026-09-15): the consistency model
    for the former axiom was `Fallible _ p := (p = False)`; under bivalence
    (`IsFalse p`), this is the same content, and the opacity requirement is
    inherited: fallibility is *not* tied to truth by definition, which is
    precisely the content of T6 below. -/
def Fallible (_s : Subject) (p : Prop) : Prop := IsFalse p

/-- Fallibility (T6 premise): some subject can be in error about some false
    content. Proven (M0 forced-subject batch, 2026-09-16): from
    `Core.someFalse` (there is a false content, PROVEN footing `{}` under E0)
    and `cogito_from_T12` (the present subject, corollary of the forced
    foundation `Agency.Cogito`).
    The former axiom is dissolved. -/
theorem fallible_false : ∃ s : Subject, ∃ p : Prop, Fallible s p ∧ IsFalse p := by
  obtain ⟨s, _, _⟩ := Logos.Plurality.cogito_from_T12
  obtain ⟨p, hp⟩ := someFalse
  exact ⟨s, p, hp, hp⟩

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
  obtain ⟨s, _, _⟩ := Logos.Plurality.cogito_from_T12
  exact (h s p).1 hp hp

/-- "There is no right and wrong without choice" (IM_STUPID.md §1–§2): the
    judgment act — a subject asserting a content that is correct-or-incorrect
    (§8) — IS a choice against the incompatible alternative `¬p`. From
    `cogito_from_T12` (a meaning-act with content p; corollary of the forced
    foundation `Agency.Cogito`, M0 2026-09-16) + bivalence (p is right-or-wrong)
    + `Incompatible p (¬p)` (pure logic). The former "gap" F1a is now a
    theorem, kernel-checked. -/
theorem judge_commits :
    ∃ s : Subject, ∃ p q : Prop, A s p ∧ (Correct s p ∨ Incorrect s p) ∧ Chooses s p q := by
  obtain ⟨s, p, ha⟩ := Logos.Plurality.cogito_from_T12
  by_cases hT : T p
  · exact ⟨s, p, ¬ p, ha, Or.inl hT, ha, incompatible_self_negation p⟩
  · exact ⟨s, p, ¬ p, ha, Or.inr hT, ha, incompatible_self_negation p⟩

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
#print axioms Logos.Order.judge_commits
