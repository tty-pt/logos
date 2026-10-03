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
`Sum.inl` and `Sum.inr`) is destroyed. Plurality requires an explicit
metaphysical bridge — until 2026-10-04 that was `AxTwoSubjects` (META: from
right-and-wrong to two distinct persons), now RETIRED and replaced by
`TwoNecessaryPersonalCentres.AxTwoNecessaryPersonalCentres`, which carries the
author's necessity argument instead of a right-and-wrong assertion and yields
necessity as well as plurality. `valueInterpersonal_of_split` recovers the exact
old statement; no strength is lost.

2026-09-24 set the moral frontier: the positive close carries the disclosed META
bridge `AxBenevolentBearingObtains` ("some person is actually helped"). That lease
was REPAIRED 2026-09-29 (see `INCONSISTENT.md`): `BearingOf` had been a closed def
returning `unbearing`, which made `Helps`/`Harms`/`Affects` refutable for every
pair — and since the bridge asserts an instance, Γ proved `False`. `BearingOf` is
now `opaque` (kernel-inaccessible value), so the "empty value layer" is a
*{}-countermodel* (C176), not a Γ theorem; the old refutations are replaced by the
schema independence lemma `no_help_in_uniformly_unbearing_layer`.
-/

import Logos.Core
import Logos.Agency
import Logos.Person
import Logos.TwoNecessaryPersonalCentres

namespace Logos.Value

open Logos.Agency (Subject)
open Logos.Person (Person)

/-- Directed interpersonal bearing of a subject toward another. -/
inductive InterpersonalBearing : Type
  | unbearing : InterpersonalBearing
  | affects_only : InterpersonalBearing
  | benevolent : InterpersonalBearing
  | harmful : InterpersonalBearing

/-- The interpersonal bearing of s toward t — RE-OPENED 2026-09-29 (see
    `INCONSISTENT.md`): an `opaque` constant. The historical body `unbearing` is
    preserved only as the minimal semantic reading; because the declaration is
    opaque, the kernel cannot reduce on it, so `Helps`/`Harms`/`Affects` are NOT
    refutable from the definitions alone, and the META bridge
    `AxBenevolentBearingObtains` is a genuine, priced commitment. The "empty
    value layer" is a `{}`-countermodel (C176), not a Γ theorem. -/
opaque BearingOf (_s _t : Subject) : InterpersonalBearing :=
  InterpersonalBearing.unbearing

/-- Affects: what s does bears on t (through help, harm, or pure affectivity).
    Decoupled from bare non-identity s ≠ t. -/
def Affects (s t : Subject) : Prop :=
  BearingOf s t = InterpersonalBearing.benevolent ∨
  BearingOf s t = InterpersonalBearing.harmful ∨
  BearingOf s t = InterpersonalBearing.affects_only

/-- Helps: positive constitutive bearing — s benefits t. -/
def Helps (s t : Subject) : Prop :=
  BearingOf s t = InterpersonalBearing.benevolent

/-- Harms: detrimental constitutive bearing — s harms t. -/
def Harms (s t : Subject) : Prop :=
  BearingOf s t = InterpersonalBearing.harmful

/-- Helping is an affective bearing: helping entails affecting. -/
theorem help_affects : ∀ {s t : Subject}, Helps s t → Affects s t := by
  intro s t h
  left
  exact h

/-- Harming is an affective bearing: harming entails affecting. -/
theorem harm_affects : ∀ {s t : Subject}, Harms s t → Affects s t := by
  intro s t h
  right; left
  exact h

/-- Benevolence principle: in the foundational order, what helps does not harm. -/
theorem help_not_harm : ∀ {s t : Subject}, Helps s t → ¬ Harms s t := by
  intro s t hh hharm
  dsimp [Helps, Harms] at hh hharm
  rw [hh] at hharm
  cases hharm

/-- The empty value layer is a *countermodel*, not a Γ fact (REPAIRED 2026-09-29,
    `INCONSISTENT.md`): in every world whose bearing is uniformly `unbearing`, no
    pair of distinct subjects is joined by help — whatever that world's subject
    vocabulary `S`. Parameterised over `S`, so it mentions no Γ axiom (`{}`) and
    constrains nothing about Γ's `BearingOf` (opaque since 2026-09-29): it refutes
    only the claim that benevolence is *forced*. This is the machine-witness for
why the positive close pays the META bridge `AxBenevolentBearingObtains`
     (C177) as a price, not a derivation — the bridge's own countermodel (C176).
     Its harm twin is `no_harm_in_uniformly_unbearing_layer` (C499).
     Footprint: `{}` (pure logic). -/
theorem no_help_in_uniformly_unbearing_layer {S : Type}
    (B : S → S → InterpersonalBearing) :
    (∀ s t : S, B s t = InterpersonalBearing.unbearing) →
      ¬ ∃ s t : S, s ≠ t ∧ B s t = InterpersonalBearing.benevolent := by
  intro hB hE
  rcases hE with ⟨s, t, _, hhelp⟩
  have hs := hB s t
  rw [hhelp] at hs
  cases hs

/-- The harm twin of the empty-layer countermodel (REPAIRED 2026-09-29,
    `INCONSISTENT.md`, C499): in every world whose bearing is uniformly
    `unbearing`, no pair of distinct subjects is joined by harm. The machine
    witness that the negative moral pole's fair reading ("harms another person")
    is *no more forced* than the positive pole's (twin C176): inhabiting Evil
    would require a separate disclosed "some harm occurs" bridge, which was not
    commissioned — SEM datum by declaration.
    Classification: COUNTERMODEL.
    Footprint: `{}` (pure logic). -/
theorem no_harm_in_uniformly_unbearing_layer {S : Type}
    (B : S → S → InterpersonalBearing) :
    (∀ s t : S, B s t = InterpersonalBearing.unbearing) →
      ¬ ∃ s t : S, s ≠ t ∧ B s t = InterpersonalBearing.harmful := by
  intro hB hE
  rcases hE with ⟨s, t, _, hharm⟩
  have hs := hB s t
  rw [hharm] at hs
  cases hs

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
  · rintro ⟨t, hne, _⟩
    exact hne (ha t)
  · rintro ⟨t, hne, _⟩
    exact hne (ha t)

/- RETIRED 2026-10-04 (batch LOVE-3/S4). The declaration below was DELETED, not
re-tagged. It is quoted here so the reader can see what was withdrawn.

  The quote deliberately does NOT put the keyword at the start of a line. That was
  a workaround for D7 — `build_deduction.parse_lean_sources` had no block-comment
  tracking, so this very note registered a *live* phantom axiom with an empty tag
  and `gapmap_taxonomy.py` read 40 where the kernel holds 39. D7 is fixed
  (2026-10-04: the scanner now uses `check_consistency.lean_code_lines`, a
  whole-file projection, and `test_axiom_census.py` asserts it), so the constraint
  no longer binds; the wording is kept because it reads better anyway. With
  `Tag: META` the withdrawn statement read:

    AxTwoSubjects :                       -- Tag: META
        (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) →
          ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂

  Original justification, kept for the record: "the *reality* of right-and-wrong
  demands that there be at least two distinct persons ... A single act does not
  entail plurality (settled by the Unit countermodel)." Philosophical cost: a
  substantive interpersonal metaphysics; plural personal reality was bought with
  this declared bridge.

  Replaced by `TwoNecessaryPersonalCentres.AxTwoNecessaryPersonalCentres`, which
  drops the right-and-wrong antecedent (so rejecting `Core.rightWrongDistinction`
  no longer costs plurality) and ADDS `NecessarySubjectKind` to both witnesses
  (so necessity is bought once, explicitly, instead of separately per consumer).
  The bridge is a re-statement of the author's reason, not of the conclusion. -/

/--No person is alone: there is no personal lone subject under the plurality bridge.

  `aloneExcluded` — under `AxTwoNecessaryPersonalCentres`, a lone person is excluded:
    there exist distinct persons, so no single subject can encompass all subjects.
    Re-derived 2026-10-04 (LOVE-3/S4): the proof is unchanged in shape, but it now
    reads the necessary-person bridge instead of `AxTwoSubjects rightWrongDistinction`,
    so it no longer needs the right-and-wrong premise. `Alone` lives here, so the
    theorem stays here rather than moving to the new module.
    Footprint: `{AxTwoNecessaryPersonalCentres, Means, NecessarySubjectKind, Subject, Will, subjectWill}`. -/
theorem aloneExcluded : ¬ ∃ s : Subject, Person s ∧ Alone s := by
  intro ⟨s, _, ha⟩
  obtain ⟨s₁, s₂, _, _, hne⟩ := Logos.TwoNecessaryPersonalCentres.two_persons
  have h1 := ha s₁
  have h2 := ha s₂
  subst h1 h2
  exact hne rfl

/--Tag: META
Some person is actually helped: benevolence is not merely definable but obtains.
  The *reality* of interpersonal value demands that at least one subject actually
  helps another distinct person (the positive moral datum the poem's "ajuda" asserts
  in the world, not only in the definition). This is a genuine, disclosed price:
  `BearingOf` is open (`opaque` since 2026-09-29), so nothing forces a help relation.

  Consistency-model note: the bridge is not forced by any earlier premise — the empty
  value layer is a `{}`-countermodel (`no_help_in_uniformly_unbearing_layer`, C176:
  in a world whose bearing is uniformly `unbearing`, no help ever obtains), so the
  hostile local universes (`M_amoral`, the Unit models) live in *separate* `S` and
  are untouched by this global value-layer datum.

  Philosophical cost: a substantive interpersonal-value metaphysics — that benevolence
  occurs in the world, not only in the definitions. Bought with this declared bridge,
  and carried openly in the footprint of every moral conclusion. -/
axiom AxBenevolentBearingObtains :
    ∃ s t : Subject, s ≠ t ∧ Person t ∧ Helps s t

/--Under the benevolence bridge, some person is actually helped by another (a help
  relation toward a distinct person obtains).
  Footprint: `{AxBenevolentBearingObtains, Means, Subject, Will, subjectWill}`. -/
theorem some_person_is_helped :
    ∃ s t : Subject, s ≠ t ∧ Person t ∧ Helps s t :=
  AxBenevolentBearingObtains

/-- PersonsAffectPrinciple: distinct persons bear on each other in at least one direction.
With Affects/Helps/Harms hardened, this is an explicit metaphysical principle. -/
def PersonsAffectPrinciple : Prop :=
  ∀ (s₁ s₂ : Subject), Person s₁ → Person s₂ → s₁ ≠ s₂ → Affects s₁ s₂ ∨ Affects s₂ s₁

/-- Right-and-wrong yields two distinct persons who bear on each other,
    conditional on the PersonsAffectPrinciple.
    Re-derived 2026-10-04 (LOVE-3/S4) off `AxTwoNecessaryPersonalCentres`; the
    `h` premise is now unused, because the bridge no longer runs on
    right-and-wrong. Kept as a premise so the call sites stay source-compatible.
    Footprint: `{AxTwoNecessaryPersonalCentres, Means, NecessarySubjectKind, Subject, Will, subjectWill}`. -/
theorem valueInterpersonal_of_split_conditional
    (hAffect : PersonsAffectPrinciple)
    (h : ¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) :
    ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧
      (Affects s₁ s₂ ∨ Affects s₂ s₁) := by
  obtain ⟨s₁, s₂, hs₁, hs₂, hne⟩ := Logos.TwoNecessaryPersonalCentres.two_persons
  exact ⟨s₁, s₂, hs₁, hs₂, hne, hAffect s₁ s₂ hs₁ hs₂ hne⟩

end Logos.Value

-- Axiom footprint audit
#print axioms Logos.Value.alone_no_other_help_harm
#print axioms Logos.TwoNecessaryPersonalCentres.AxTwoNecessaryPersonalCentres
#print axioms Logos.Value.no_help_in_uniformly_unbearing_layer
#print axioms Logos.Value.no_harm_in_uniformly_unbearing_layer
#print axioms Logos.Value.AxBenevolentBearingObtains
#print axioms Logos.Value.some_person_is_helped
#print axioms Logos.Value.aloneExcluded
#print axioms Logos.Value.help_not_harm
#print axioms Logos.Value.help_affects
