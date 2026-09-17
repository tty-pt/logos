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
derivable from a single act or Cogito alone (proven by the Unit countermodel
in `HostileSemantics`). The former pseudo-proof via `otherSubject` (swapping
`Sum.inl` and `Sum.inr`) is destroyed. Plurality requires the explicit
metaphysical bridge `AxTwoSubjects` (META: from right-and-wrong to two
distinct persons). `valueInterpersonal_of_split` recovers the exact old
statement; no strength is lost.
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

/--Positive constitutive bearing: a subject benefiting another.

 `Helps s t`: `s` benefits `t` — definitional projection of `Affects`
    (the helps-direction). -/
def Helps (s t : Subject) : Prop := Affects s t

/--Detrimental constitutive bearing: a subject harming another.

 `Harms s t`: `s` harms `t` — in the foundational ground, harm has no
    ontological standing. -/
def Harms (_s _t : Subject) : Prop := False

/--Helping is a way of affecting (unfolds to the identity). -/
theorem help_affects : ∀ {s t : Subject}, Helps s t → Affects s t := by
  intro s t h
  exact h

/--Harming is a way of affecting (vacuously true in the foundational ground). -/
theorem harm_affects : ∀ {s t : Subject}, Harms s t → Affects s t := by
  intro s t h
  exact False.elim h

/--Helping excludes harming: benevolence is incompatible with malice.

 Benevolence principle: in the foundational order, what helps does not harm. -/
theorem help_not_harm : ∀ {s t : Subject}, Helps s t → ¬ Harms s t := by
  intro s t _h hh
  exact hh

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
    obtain ⟨t, hne, _⟩ := h
    exact hne (ha t)
  · intro h
    obtain ⟨t, _, hh⟩ := h
    exact hh

/--Tag: META
AxTwoSubjects (META; poem P5/P7, failure traces in DESIGN.md D14 and
    HostileSemantics): the *reality* of right-and-wrong demands that there be
    at least two distinct persons. Narrower than the former single bridge
    `AxValueInterpersonal` (plurality only; affectivity is AxPersonsAffect).
    A single act does not entail plurality (settled by the Unit countermodel). -/
axiom AxTwoSubjects :
    (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) →
      ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂

/--No person is alone: there is no personal lone subject under the plurality bridge.

 `aloneExcluded` — under `AxTwoSubjects`, a lone person is excluded:
    there exist distinct persons, so no single subject can encompass all subjects.
    Footprint: `{AxTwoSubjects}`. -/
theorem aloneExcluded : ¬ ∃ s : Subject, Person s ∧ Alone s := by
  intro ⟨s, _, ha⟩
  obtain ⟨s₁, s₂, _, _, hne⟩ := AxTwoSubjects Logos.Core.rightWrongDistinction
  have h1 := ha s₁
  have h2 := ha s₂
  subst h1 h2
  exact hne rfl

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
#print axioms Logos.Value.AxTwoSubjects
#print axioms Logos.Value.aloneExcluded
#print axioms Logos.Value.AxPersonsAffect
#print axioms Logos.Value.valueInterpersonal_of_split
#print axioms Logos.Value.help_not_harm
