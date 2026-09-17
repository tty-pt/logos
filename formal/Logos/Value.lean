/-
# Logos.Value — interpersonal value (poem P5/P6; the "ser sozinho" premise)

P6 of the poem: "um Ser sózinho pode agir de uma forma ou de outra, não ajuda
nem prejudica ninguém." Formal content:

  * `Affects` is now a *structural definition* (A3, M1 batch of
    `FORCED_SUBJECT.md`, 2026-09-15→16): bearing = distinctness
    (`Affects s t := s ≠ t`); `Helps`/`Harms` are its definitional
    projections; faithful to P6 ("não ajuda nem prejudica ninguém" — the lone
    subject affects no other);
  * lemma `alone_no_other_help_harm`: a lone subject helps/harms no *other*
    subject (an other = a t with t ≠ s). Now carries no `Affects` axiom.

The poem's *leap* (P5, "para haver escolha com significado, é preciso mais do
que uma pessoa") — the reality of right-and-wrong is *interpersonal* — is NOT
derivable from the axioms alone (failure traces in DESIGN.md D14 + C3-I spike;
the named missing lemma is `ALONE_EXCLUDED : ¬ ∃ s, Person s ∧ Alone s`). The
former single bridge `AxValueInterpersonal` was split (C3-I, 2026-09-15) into
plurality (`AxTwoSubjects`, META) + affectivity (`AxPersonsAffect`, SEM); M1
(2026-09-16) folds the SEM half: `AxPersonsAffect` is now a **theorem** of A3.
Only the **plurality-claim** `AxTwoSubjects` (META: from right-and-wrong to two
distinct persons) stays declared — the leap's price is isolated at its only
honest site: a second distinct person. `valueInterpersonal_of_split` recovers
the exact old statement, so no strength is lost. Priced, never pure deduction
(§29).

The poem's *leap* (P5, "para haver escolha com significado, é preciso mais do
que uma pessoa") — the reality of right-and-wrong is *interpersonal* — is NOT
derivable from the axioms alone (failure traces in DESIGN.md D14 + C3-I spike;
the named missing lemma is `ALONE_EXCLUDED : ¬ ∃ s, Person s ∧ Alone s`). Only the
**plurality-claim** `AxTwoSubjects` (META: from right-and-wrong to two distinct
persons) remains declared — M1 folds the affectivity half into A3.
`valueInterpersonal_of_split` recovers the exact old statement, so no strength
is lost. Priced, never pure deduction (§29).
-/

import Logos.Core
import Logos.Agency
import Logos.Person

namespace Logos.Value

open Logos.Agency (Subject)
open Logos.Person (Person)

/-- `Affects s t`: what `s` does bears on `t`. NOW a structural DEFINITION
    (A3, batch M1 of `FORCED_SUBJECT.md`, 2026-09-16): bearing = distinctness —
    a subject bears on what is *other*; the lone subject bears on nothing
    (P6: "não ajuda nem prejudica ninguém"). `Helps`/`Harms` are its
    definitional *projections* (see below).

    This is a SEM *position*, recorded and owned (same class as A2's structural
    `TrueAt`): it defines the minimal structural content of affectivity, it
    does not pretend to *derive* it. The former two-declaration swing
    (`axiom Affects` + `axiom AxPersonsAffect`) collapses to zero.

    Prose price: "Amar é escolhido" now rests entirely on `FreeWill` (F1,
    DEFERRED); `Loves := Affects` in Love.lean reads as the directed
    constitutive bearing of one subject on a *distinct* one. -/
def Affects (s t : Subject) : Prop := s ≠ t

/-- `Helps s t`: `s` benefits `t` — definitional projection of `Affects`
    (the helps-direction). -/
def Helps (s t : Subject) : Prop := Affects s t

/-- `Harms s t`: `s` harms `t` — definitional projection of `Affects`
    (the harms-direction). -/
def Harms (s t : Subject) : Prop := Affects s t

/-- Helping is a way of affecting (unfolds to the identity). -/
theorem help_affects : ∀ {s t : Subject}, Helps s t → Affects s t := by
  intro s t h
  exact h

/-- Harming is a way of affecting (unfolds to the identity). -/
theorem harm_affects : ∀ {s t : Subject}, Harms s t → Affects s t := by
  intro s t h
  exact h

/-- `OtherAffects s`: `s`'s doings bear on some *other* subject. -/
def OtherAffects (s : Subject) : Prop := ∃ t : Subject, t ≠ s ∧ Affects s t

/-- `Alone s`: there is no other subject (the only subject is `s`). -/
def Alone (s : Subject) : Prop := ∀ t : Subject, t = s

/-- P6, half 1 — a lone subject's doings affect no other. -/
theorem alone_no_other_affects {s : Subject} (ha : Alone s) : ¬ OtherAffects s := by
  intro h
  obtain ⟨t, hne, _⟩ := h
  exact hne (ha t)

/--A lone subject neither helps nor harms anyone else.

 P6, whole — a lone subject helps no other AND harms no other. -/
theorem alone_no_other_help_harm {s : Subject} (ha : Alone s) :
    (¬ ∃ t : Subject, t ≠ s ∧ Helps s t) ∧ (¬ ∃ t : Subject, t ≠ s ∧ Harms s t) := by
  constructor
  · intro h
    obtain ⟨t, hne, hh⟩ := h
    exact hne (ha t)
  · intro h
    obtain ⟨t, hne, hh⟩ := h
    exact hne (ha t)

/--Tag: META

 The plurality bridge: right-and-wrong demands two distinct persons.

 AxTwoSubjects (META; poem P5/P7, failure traces in DESIGN.md D14 and
    spike x2_spikeA): the *reality* of right-and-wrong demands that there be
    at least two distinct persons. Narrower than the former single bridge
    `AxValueInterpersonal` (plurality only; affectivity is AxPersonsAffect).
    Exclusion attempt recorded in /tmp/opencode/x2_spikeA.lean: the lone-subject
    scenario `Alone s` is consistent with cogito + T6 + P6, so no contradiction
    is derivable; named missing lemma `ALONE_EXCLUDED`. -/
axiom AxTwoSubjects :
    (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) →
      ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂

/-- AxPersonsAffect (theorem of A3, M1 2026-09-16; formerly a SEM
    meaning-postulate): distinct persons necessarily bear on each other in at
    least one direction — because bearing IS distinctness, `hne : s₁ ≠ s₂`
    is the left disjunct itself. This formerly stood as a declared axiom
    (`axiom` with no introduction rule; exclusion attempt in
    /tmp/opencode/x2_spikeB.lean); the A3 definition supplies the missing
    introduction rule. -/
theorem AxPersonsAffect (s₁ s₂ : Subject) (_hs₁ : Person s₁) (_hs₂ : Person s₂)
    (hne : s₁ ≠ s₂) : Affects s₁ s₂ ∨ Affects s₂ s₁ :=
  Or.inl hne

/--Right-and-wrong yields two distinct persons who bear on each other.

 Recovery theorem: the exact statement of the deleted `AxValueInterpersonal`
    (line 70-73, 2026-09-14) is a theorem of the split — no strength lost. -/
theorem valueInterpersonal_of_split :
    (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) →
      ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧
        (Affects s₁ s₂ ∨ Affects s₂ s₁) := by
  intro h
  obtain ⟨s₁, s₂, hs₁, hs₂, hne⟩ := AxTwoSubjects h
  exact ⟨s₁, s₂, hs₁, hs₂, hne, AxPersonsAffect s₁ s₂ hs₁ hs₂ hne⟩

end Logos.Value

-- Axiom footprint audit
#print axioms Logos.Value.alone_no_other_help_harm
#print axioms Logos.Value.valueInterpersonal_of_split
