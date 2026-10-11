/-
# step1_audit_probe.lean — the machine-checked core of the Issue-K meaning-coherence audit

Status: **audit artifact, NOT in the kernel.** This file is not in the `Logos`
lean_lib (`lakefile.toml`), is never imported, and is never compiled by
`lake build`. It is the evidence for
`investigations/issue-k-meaning-coherence-audit.md`, kept in the tree so that every
claim in that write-up can be re-checked by running the kernel rather than read
off a transcript.

Run it (from `formal/`):

```sh
export PATH="$HOME/.elan/bin:$PATH"
cd formal && lake env lean ../investigations/issue-k/step1_audit_probe.lean
```

Expected output: the `#print axioms` lines below and nothing else. Every
`[]` printed means the declaration rests on no axiom at all — no `CL`, no
`propext`, no `Classical.em`. A `sorryAx` anywhere is a failure of the audit.

Sections map one-to-one onto the audit's findings:
  A/E/F  → `AsieticChoice.singleContentModelRefutesBareRejectedHorn` (C273/C274)
  B/C/D  → the stale `BLOCKED` verdict on `bareRejectedHornCoMeant` (F11)
  G/H    → `AsietyFreedom.rightWrongFactYieldsNoChooser` (C294)
-/

import Logos

open Logos Logos.Agency Logos.Alternatives Logos.Choice Logos.AsieticChoice
open Logos.Entity

/-!
## A. The bare rejected horn is DERIVED in Γ

`GAPMAP.md` C273/C274 and frontier row F11 record `bareRejectedHornCoMeant` as
`BLOCKED` and "refuted, not merely open", on the stated ground that "no axiom of
Γ supplies an `Initiates` witness". That ground is false: `performative_act_datum`
(C454, `Tag: TRANS`) *is* such a witness, because `Act s p` unfolds to
`Means s p ∧ ∃ w w', Initiates s w w' p` (`Agency.lean:22`). Together with
`AxActPolarity` (SEM, premise `Act s p`) the horn follows in two lines.
-/

theorem probe_bareRejectedHornCoMeant_is_derived :
    Logos.AsieticChoice.bareRejectedHornCoMeant :=
  fun _ => by
    obtain ⟨s, p, hAct⟩ := performative_act_datum
    exact ⟨s, p, act_implies_means hAct, AxActPolarity s p hAct⟩

#print axioms probe_bareRejectedHornCoMeant_is_derived
-- [Initiates, Means, State, Subject, performative_act_datum, AxActPolarity]

theorem probe_bareHorn_yields_trueChoice :
    ∃ s : Subject, ∃ p : Prop, TrueChoice s p (¬ p) := by
  obtain ⟨s, p, hAct⟩ := performative_act_datum
  exact ⟨s, p, chooses_implies_trueChoice ⟨act_implies_means hAct,
    AxActPolarity s p hAct, incompatible_self_negation p⟩⟩

#print axioms probe_bareHorn_yields_trueChoice
-- [Initiates, Means, State, Subject, performative_act_datum, AxActPolarity]

/-! ## B–D. Free will, free subject and true freedom at the same price

Compare the currently-ledgered route `AsieticChoice.freeWill_exists` / C278 and
`an_asietic_entity_exists`, both at `{AxTwoSubjects, Means, Subject, Will,
subjectWill}` — `AxTwoSubjects` is `Tag: META`. The probes below reach the same
conclusions at `{performative_act_datum, AxActPolarity}`: one `TRANS` datum and
one `SEM` constitutive principle, with no `META` bridge on the route.
-/

theorem probe_freeWill_from_act_datum_and_polarity :
    ∃ s : Subject, FreeWill s := by
  obtain ⟨s, p, hAct⟩ := performative_act_datum
  exact ⟨s, trueChoice_implies_freeWill (chooses_implies_trueChoice
    ⟨act_implies_means hAct, AxActPolarity s p hAct, incompatible_self_negation p⟩)⟩

#print axioms probe_freeWill_from_act_datum_and_polarity
-- [Initiates, Means, State, Subject, performative_act_datum, AxActPolarity]

theorem probe_asiety_from_act_datum_and_polarity : ∃ e : Entity, Asiety e := by
  obtain ⟨s, p, hAct⟩ := performative_act_datum
  exact ⟨EntityOf s, s, p, ¬ p, rfl,
    chooses_implies_trueChoice ⟨act_implies_means hAct, AxActPolarity s p hAct,
      incompatible_self_negation p⟩⟩

#print axioms probe_asiety_from_act_datum_and_polarity
-- [Initiates, Means, State, Subject, performative_act_datum, AxActPolarity]

/-!
## E. `p = ¬ p` is intuitionistically false — the docstring's contrary claim is `{}`-refuted

`AsieticChoice.lean:341-344` and `:357-359` justify the `Faithful` field by
saying "from `p = ¬ p` no contradiction follows in general, because `p` need not
be provable". That is false, and it is refutable with no axioms at all.
-/

theorem probe_eq_negp_is_false (p : Prop) (h : p = ¬ p) : False := by
  have h2 : p → (p → False) := Eq.mp h
  have h1 : (p → False) → p := Eq.mp h.symm
  have f : p → False := fun hp => h2 hp hp
  exact f (h1 f)

#print axioms probe_eq_negp_is_false
-- []

/-!
## F. Genuine single-valuedness refutes the horn, with no truth constraint

This is the repair the audit prescribes for `SingleContentSignature`: replace the
truth-only `faithful : ∀ s p, means s p → p` by genuine single-valuedness
`single : ∀ s p, means s p → p = content s`, which does **not** forbid relating a
subject to a falsehood. The refutation survives at `{}`, so `Faithful` was never
load-bearing.
-/

structure SingleValuedSignature where
  Subject : Type
  content : Subject → Prop
  means : Subject → Prop → Prop
  single : ∀ (s : Subject) (p : Prop), means s p → p = content s

def singleValuedBareHorn (S : SingleValuedSignature) : Prop :=
  (∃ s : S.Subject, ∃ p : Prop, S.means s p) →
    ∃ s : S.Subject, ∃ p : Prop, S.means s p ∧ S.means s (¬ p)

theorem probe_singleValuedness_refutes_bareHorn
    (S : SingleValuedSignature)
    (hAntec : ∃ s : S.Subject, ∃ p : Prop, S.means s p) :
    ¬ singleValuedBareHorn S := by
  intro hHorn
  obtain ⟨t, q, hq1, hq2⟩ := hHorn hAntec
  exact probe_eq_negp_is_false q ((S.single t q hq1).trans (S.single t (¬ q) hq2).symm)

#print axioms probe_singleValuedness_refutes_bareHorn
-- []

/-! A concrete witness: each subject means exactly one content, and that content
may be `False` — i.e. the model instantiates meaning, falsehood included. -/

def singleValuedModel : SingleValuedSignature where
  Subject := Bool
  content := fun _ => False
  means := fun _ p => p = False
  single := fun _ _ h => h

theorem probe_singleValuedModel_witnesses_antecedent :
    (∃ s : Bool, ∃ p : Prop, singleValuedModel.means s p) ∧
      singleValuedModel.means false False :=
  ⟨⟨false, False, rfl⟩, rfl⟩

#print axioms probe_singleValuedModel_witnesses_antecedent
-- []

/-!
## G. `rightWrongFactYieldsNoChooser`'s witness is FORCED to be meaning-free

`AsietyFreedom.rightWrongFactYieldsNoChooser` (C294) exhibits
`¬ (∃ s : S, ∃ p q : Prop, M s p ∧ M s q)`. Because `p` and `q` are not required
to be distinct, that statement is *equivalent* to `¬ (∃ s p, M s p)` — so every
possible witness of that countermodel is a world in which **nothing at all** is
meant, and the author's objection to it ("a meaning-vocabulary in which the
meaning-relation is just the constant-false predicate") is a theorem, not a
reading.
-/

theorem probe_pairq_forces_meaninglessness
    (M : Unit → Prop → Prop)
    (h : ¬ (∃ s : Unit, ∃ p q : Prop, M s p ∧ M s q)) :
    ¬ (∃ s : Unit, ∃ p : Prop, M s p) := by
  rintro ⟨s, p, hMp⟩
  exact h ⟨s, p, p, hMp, hMp⟩

#print axioms probe_pairq_forces_meaninglessness
-- []

/-!
## H. The repaired form: the model must instantiate meaning

The `NegativeRetorsionSignature` repair shape (`objectivity_grounded : EO → ∃ s,
Free s ∧ ∃ p, Means s p`, which makes the pre-fix witness a compile error) applied
to C294: require distinct contents *and* force meaning to exist. The witness
`M := fun _ p => p = True` then means something and still denies the pair.
-/

theorem probe_repaired_rightWrong_no_pairwise_chooser :
    (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) ∧
      ∃ (S : Type) (M : S → Prop → Prop),
        (∃ s : S, ∃ p : Prop, M s p) ∧
        ¬ (∃ s : S, ∃ p q : Prop, p ≠ q ∧ M s p ∧ M s q) := by
  refine ⟨Logos.Core.rightWrongDistinction, Unit, fun _ p => p = True,
    ⟨(), True, rfl⟩, ?_⟩
  rintro ⟨s, p, q, hpq, h1, h2⟩
  have : p = q := h1.trans h2.symm
  exact hpq this

#print axioms probe_repaired_rightWrong_no_pairwise_chooser
-- []