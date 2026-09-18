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
open Logos.Choice (ChoiceField incompatible_self_negation)

/-- Correctness: a subject's act of *meaning* p is correct iff p is true
    (§8, literal form `Correct(A(s,p)) ↔ True(p)`). The act is constitutive:
    `A s p := Means s p` (Tier-1 collapse), so every correct judgment is
    already a meaning-act — you cannot have right/wrong without meaning. -/
def Correct (s : Subject) (p : Prop) : Prop := A s p ∧ T p

/-- Incorrectness: a subject's act of *meaning* p is incorrect iff p is false
    (§8, literal form `Incorrect(A(s,p)) ↔ False(p)`). Same as `Correct`:
    the meaning-act `A s p` is a conjunct, hence unavoidable. -/
def Incorrect (s : Subject) (p : Prop) : Prop := A s p ∧ IsFalse p

/--Right and wrong need meaning: the normative predicates are properties of
 meaning-acts, so wherever right-or-wrong is realized, a meaning (and thus a
 subject, C49) is realized.

 "For right to be distinct from wrong, meaning must be a thing" (poem P3,
    line 18). Pure projection from the §8 definitions: `Correct s p` unfolds
    to `A s p ∧ T p` with `A s p := Means s p`, so the witness content `p`,
    meant by `s`, is a `Meaning_I`. Footprint `{Means, Subject}` (vocab-only —
    no substantive axiom): no model can assert `Correct`/`Incorrect` while
    denying meaning, because `A s p` is a conjunct. -/
theorem rightWrong_implies_meaning
    (h : (∃ s : Subject, ∃ p : Prop, Correct s p) ∨
         (∃ s : Subject, ∃ p : Prop, Incorrect s p)) :
    ∃ p : Prop, Logos.Choice.Meaning_I p := by
  cases h with
  | inl hc =>
      obtain ⟨s, p, hc⟩ := hc
      exact ⟨p, s, hc.1⟩
  | inr hw =>
      obtain ⟨s, p, hw⟩ := hw
      exact ⟨p, s, hw.1⟩

/--The strong form: right *and* wrong both realized entails meaning.
 `Correct` and `Incorrect` are each a meaning-act, so the distinction
    itself witnesses `Meaning_I` — purely derived, footprint `{Means, Subject}`
    (vocab-only, no substantive axiom). -/
theorem rightDistinctWrong_implies_meaning
    (h : (∃ s : Subject, ∃ p : Prop, Correct s p) ∧
         (∃ s : Subject, ∃ p : Prop, Incorrect s p)) :
    ∃ p : Prop, Logos.Choice.Meaning_I p :=
  rightWrong_implies_meaning (Or.inl h.1)

/-- `Fallible s p`: subject s is *bound by* the falsehood of p — the subject
    can be in error about p. Defined (A1, 2026-09-15): the consistency model
    for the former axiom was `Fallible _ p := (p = False)`; under bivalence
    (`IsFalse p`), this is the same content, and the opacity requirement is
    inherited: fallibility is *not* tied to truth by definition, which is
    precisely the content of T6 below. -/
def Fallible (_s : Subject) (p : Prop) : Prop := IsFalse p

/-- Fallibility (T6 premise): some subject can be in error about some false
    content. Proven (definitional subject, 2026-09-17): from
    `Core.someFalse` (there is a false content, PROVEN footing `{}` under E0)
    and `cogito_from_T12` (the present subject, corollary of the exhibited
    `Agency.Cogito`).
    The former axiom is dissolved. -/
theorem fallible_false : ∃ s : Subject, ∃ p : Prop, Fallible s p ∧ IsFalse p := by
  obtain ⟨s, _, _⟩ := Logos.Plurality.cogito_from_T12
  obtain ⟨p, hp⟩ := someFalse
  exact ⟨s, p, hp, hp⟩

/--A fallible judgment need not be true: fallibility is real.

 T6 — truth is not created by asserting: assertion ⇒ truth fails. -/
theorem T6_fallibility : ¬ (∀ s : Subject, ∀ p : Prop, Fallible s p → T p) := by
  intro h
  obtain ⟨s, p, hf, hnt⟩ := fallible_false
  exact hnt (h s p hf)

/--Truth is not the same as being fallibly judged: what is true transcends the will to judge.

 T6, second form: `Truth ≠ WillOfAgent` — no equivalence can hold between
    willing-asserting and being true. -/
theorem T6_truthTranscendsWill : ¬ (∀ s : Subject, ∀ p : Prop, Fallible s p ↔ T p) := by
  intro h
  obtain ⟨s, p, hf, hnt⟩ := fallible_false
  exact hnt ((h s p).1 hf)

/--Correct and incorrect judging are distinct: correctness is not incorrectness.

 §8 — Correct ≠ Incorrect: the two normative predicates are distinct. -/
theorem correctness_distinct : ¬ (∀ s : Subject, ∀ p : Prop, Correct s p ↔ Incorrect s p) := by
  intro h
  obtain ⟨s, p, ha⟩ := Logos.Plurality.cogito_from_T12
  by_cases hT : T p
  · exact ((h s p).1 ⟨ha, hT⟩).2 hT
  · exact hT ((h s p).2 ⟨ha, hT⟩).2

/--The judge is before a choice field: whoever judges acts, correctly or incorrectly.

  "There is no right and wrong without (a field of) choice" (IM_STUPID.md §1–§2):
     the judgment act — a subject asserting a content that is correct-or-incorrect
     (§8) — IS set against the incompatible alternative `¬p`. From
     `cogito_from_T12` (a meaning-act with content p; corollary of the
     exhibited `Agency.Cogito`, 2026-09-17) + bivalence (p is right-or-wrong)
    + `Incompatible p (¬p)` (pure logic).

  Audit notice (freedom/choice fix, 2026-09-18): this delivers `ChoiceField`,
    not genuine `Chooses`. The judge relates only to the judged content `p`; the
    rejected horn `¬p` is pure logic. Genuine choice needs the co-meaned horn
    (`Choice.rejectedHornCoMeant`, BLOCKED). -/
theorem judge_commits :
    ∃ s : Subject, ∃ p q : Prop, A s p ∧ (Correct s p ∨ Incorrect s p) ∧ ChoiceField s p q := by
  obtain ⟨s, p, ha⟩ := Logos.Plurality.cogito_from_T12
  by_cases hT : T p
  · exact ⟨s, p, ¬ p, ha, Or.inl ⟨ha, hT⟩, ha, incompatible_self_negation p⟩
  · exact ⟨s, p, ¬ p, ha, Or.inr ⟨ha, hT⟩, ha, incompatible_self_negation p⟩

/--The full poetic conditional, with the exhibited step made explicit: the bare
 distinction `¬N_T ∧ ¬N_F` forces an actual judging act (`judge_commits`,
 paying only the exhibited `Cogito`), after which the *pure* bridge
 `rightWrong_implies_meaning` (vocab-only) yields meaning. -/
theorem rightWrongDistinction_implies_meaning
    (_h : ¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) :
    ∃ p : Prop, Logos.Choice.Meaning_I p := by
  obtain ⟨s, p, _q, _ha, hci, _⟩ := judge_commits
  rcases hci with hc | hw
  · exact rightWrong_implies_meaning (Or.inl ⟨s, p, hc⟩)
  · exact rightWrong_implies_meaning (Or.inr ⟨s, p, hw⟩)

/--Consequence preserves truth: whatever two true premises jointly imply is true.

 §9 — logical consequence preserves truth (rendering: the object-level
    consequence `p₁, p₂ ⊢ q` carries truth upward). -/
theorem consequence_preserves_truth {p₁ p₂ q : Prop}
    (himp : p₁ → p₂ → q) (h1 : T p₁) (h2 : T p₂) : T q := by
  exact (tschema q).2 (himp ((tschema p₁).1 h1) ((tschema p₂).1 h2))

/-- The proposition asserting that no reasoning act occurs. -/
def NoAct : Prop := ¬ ∃ s : Subject, ∃ p : Prop, A s p

/-- The Cartesian Retortion (half 1): no subject can ever correctly judge that no act occurs.
    The very occurrence of the judgment contradicts its truth-claim. -/
theorem no_correct_judgment_of_no_act (s : Subject) : ¬ Correct s NoAct := by
  intro hc
  have hex : ∃ s' p', A s' p' := ⟨s, NoAct, hc.1⟩
  exact hc.2 hex

/-- The Cartesian Retortion (half 2): whoever judges that no act occurs is necessarily incorrect.
    Error is the only possible status of the denial of the act. -/
theorem judgment_of_no_act_is_incorrect (s : Subject)
    (h : Correct s NoAct ∨ Incorrect s NoAct) : Incorrect s NoAct := by
  cases h with
  | inl hc => exact False.elim (no_correct_judgment_of_no_act s hc)
  | inr hi => exact hi

/-- An objective judgment (correct or incorrect) implies that the reasoning act occurs. -/
theorem judgment_implies_act {s : Subject} {p : Prop} (h : Correct s p ∨ Incorrect s p) : A s p := by
  cases h with
  | inl hc => exact hc.1
  | inr hi => exact hi.1

/-- The Retorsive Cogito: even the skeptic's denial that any act occurs strictly witnesses
    that an act occurs. The act cannot be denied without providing the witness that refutes the denial. -/
theorem judgment_of_no_act_proves_act (s : Subject)
    (h : Correct s NoAct ∨ Incorrect s NoAct) : ∃ s' : Subject, ∃ p' : Prop, A s' p' :=
  ⟨s, NoAct, judgment_implies_act h⟩

/-- Any objective judgment of right or wrong strictly entails that an act of reasoning occurs. -/
theorem judgment_implies_cogito
    (h : (∃ s : Subject, ∃ p : Prop, Correct s p) ∨
         (∃ s : Subject, ∃ p : Prop, Incorrect s p)) :
    ∃ s : Subject, ∃ p : Prop, A s p := by
  cases h with
  | inl hc =>
      obtain ⟨s, p, hc⟩ := hc
      exact ⟨s, p, hc.1⟩
  | inr hi =>
      obtain ⟨s, p, hi⟩ := hi
      exact ⟨s, p, hi.1⟩

end Logos.Order

-- Axiom footprint audit
#print axioms Logos.Order.T6_fallibility
#print axioms Logos.Order.T6_truthTranscendsWill
#print axioms Logos.Order.correctness_distinct
#print axioms Logos.Order.consequence_preserves_truth
#print axioms Logos.Order.judge_commits
#print axioms Logos.Order.rightWrong_implies_meaning
#print axioms Logos.Order.rightDistinctWrong_implies_meaning
#print axioms Logos.Order.rightWrongDistinction_implies_meaning
#print axioms Logos.Order.no_correct_judgment_of_no_act
#print axioms Logos.Order.judgment_of_no_act_is_incorrect
#print axioms Logos.Order.judgment_implies_act
#print axioms Logos.Order.judgment_of_no_act_proves_act
#print axioms Logos.Order.judgment_implies_cogito
