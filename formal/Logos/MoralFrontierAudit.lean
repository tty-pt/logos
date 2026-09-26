/-
# Logos.MoralFrontierAudit — Stage 2: the moral frontier, machine-separated

Runs the Stage-1 method against the practical domain. The method transfers but the
**verdict flips**: the practical pole `Ought` is a **declared primitive** (axiom,
`OughtRetorsion.Ought`, VOCAB) — not a definitional pole like `Correct`
(`Order.lean:29`, a def over `T := p`). So the *amoralist* thesis
(`¬ ∃ r s a, OughtStar r s a`) is **satisfiable**: the hostile local model `M_amoral`
instantiates the full epistemic reality-hook and agential normativity while practical
bindingness stays false everywhere.

## What is proven here (all `{}`, strictly zero axioms — `HostileImpersonalModel` idiom)
- `M_amoral` is a local universe (`S := Unit`) of defs; `CorrectStar`/`IncorrectStar`
  are the Stage-1 tracking shape reused; `RightWrongStar` at poles `⟨True, False⟩`
  re-instantiates judicative-pole agential normativity.
- `epistemic_normativity_without_practical_obligation` — **the F3 separation** (the
  frontier C175): epistemic agential normativity does NOT force practical bindingness.
- `amoral_disconnection_is_judgeable_as_correct` — the flip made formal: in contrast
  with the epistemic `D` (unjudgeable-as-correct), the amoralist thesis is *true in the
  model*, hence correctly judgeable — satisfiable, not self-refuting.

## The positive moral close (2026-09-24): the fair relational `Good`

The separation above stays `{}` forever: normative structure alone never forces moral
poles. But the *positive* pole no longer has to be **postulated**. Following the
"other-first" program (MORAL.md), `Good` is now a **fair definition** — helpfulness
toward another *person* (`∃ t ≠ s, Person t ∧ Helps s t ∧ ¬ Harms s t`) — and it
**obtains** (`moral_good_obtains`) under one disclosed, priced META bridge
`AxBenevolentBearingObtains` ("some person is actually helped"). The bare value layer
is provably empty (`Logos.Value.helps_unobtainable`, `no_help_obtains`), so the bridge
is a genuine paid commitment, carried openly in the footprint — not a hidden derivation.
The negative pole `Evil` remains a declared SEM datum (its fair relational reading is
uninhabited without a parallel "some harm occurs" bridge — not yet declared).

## Structural difference (why the method flips — recorded, not re-derived)
`Ought` is an axiom (`OughtRetorsion.lean:72`) while `Correct` is a **def**. Stage 1
needed the poles to be definitions (they were); for morality the poles are a declared
primitive, so no `moral_pole_not_definitional` theorem is needed — the model machine-
witness the gap instead.

## Footprint discipline
M_amoral theorems stay `{}` (local defs + definitional `DeonticOpposition` /
`Incompatible`). The fair `Good` def is vocabulary-only (its inhabitation is priced
separately in `moral_good_obtains`, which carries `{AxBenevolentBearingObtains, ...}`).
`Evil` still lists itself in the `ClaimsMoralRectitude`/`stance_exhibits_moral_poles`
footprints. `moral_pole_postulate_is_not_a_consequence` is vocabulary-only
`{Initiates, Means, State, Subject}` and remains the machine proof that no pole is
forced by the relying structure alone.
-/

import Logos.RealityHookAudit
import Logos.OughtRetorsion
import Logos.IndubitableNormativeFreeWill
import Logos.Agency
import Logos.Person
import Logos.Value

namespace Logos.MoralFrontierAudit

open Logos.Core (T IsFalse)
open Logos.Agency (Subject Means State Initiates Act)
open Logos.Order (Correct Incorrect)
open Logos.OughtRetorsion (PracticalAction)
open Logos.RealityHookAudit (correct_tracks_reality)
open Logos.Person (Person)
open Logos.Value (Helps Harms help_not_harm some_person_is_helped)

-- ===========================================================================
-- §5.1 The amoral hostile model `M_amoral` — local universe, all defs
-- ===========================================================================
namespace M_amoral

/-- The amoral model's universe holds exactly one subject. -/
abbrev S : Type := Unit

/-- The sole inhabitant of the amoral model. -/
def soleSubject : S := ()

/-- Local means-relation: the subject's judgement always reaches any content. -/
def Means (_s : S) (_p : Prop) : Prop := True

/-- Local state type (one world-region). -/
def State : Type := Unit

/-- Local initiations-relation: any state transition reaches any content. -/
def Initiates (_s : S) (_w _w' : State) (_p : Prop) : Prop := True

/-- Local act: means-command over content plus an initiating transition. -/
def Act (s : S) (p : Prop) : Prop := Means s p ∧ ∃ w w', Initiates s w w' p

/-- Local correctness: identity-preserving hook, the Stage-1 tracking shape reused. -/
def CorrectStar (s : S) (p : Prop) : Prop := Act s p ∧ p

/-- Local incorrectness: content fails. -/
def IncorrectStar (s : S) (p : Prop) : Prop := Act s p ∧ ¬ p

/-- Local practical obligation: NEVER binds (false for every source, subject, action). -/
def OughtStar (_r _s : S) (_a : PracticalAction) : Prop := False

/-- Local genuine normativity: deontic opposition of the poles + agential address. -/
def GenuineNormativityStar (s : S) (p q : Prop) : Prop :=
  Logos.IndubitableNormativeFreeWill.DeonticOpposition p q ∧ (Means s p ∧ Means s q)

/-- Local right/wrong: some opposed, addressed pole-pair is instantiated. -/
def RightWrongStar (s : S) : Prop := ∃ p q, GenuineNormativityStar s p q

/-- The amoralist thesis: no source places anyone under any practical obligation. -/
def AmoralistThesis : Prop := ¬ ∃ r : S, ∃ s : S, ∃ a : PracticalAction, OughtStar r s a

-- ===========================================================================
-- §5.2 The separation theorems — all `{}` (HostileImpersonalModel precedent)
-- ===========================================================================

/--Correctness tracks reality inside the amoral model: a correct judgement's content holds.
-/
theorem correct_star_tracks_reality (s : S) (p : Prop) (h : CorrectStar s p) : p :=
  h.2

/--The amoral model satisfies epistemic agential normativity at the poles ⟨True, False⟩.
-/
theorem amoral_model_satisfies_epistemic_agential_normativity :
    ∃ s : S, RightWrongStar s :=
  ⟨soleSubject, ⟨True, False, ⟨⟨fun h => h.2, fun h => Eq.mp h True.intro⟩, ⟨trivial, trivial⟩⟩⟩⟩

/--The amoral model has NO practical obligation: `OughtStar` is false everywhere.
-/
theorem amoral_model_has_no_practical_obligation :
    ¬ ∃ r : S, ∃ s : S, ∃ a : PracticalAction, OughtStar r s a := by
  rintro ⟨r, s, a, ho⟩
  exact ho

/--Epistemic agential normativity does not force practical bindingness.
  The amoral model `M_amoral` re-instantiates the full Stage-1 reality-hook and
  judicative-pole agential normativity (`CorrectStar s True ≡ True` —
  `RightWrongStar` witness at poles `⟨True, False⟩` IS the pair at content `True`)
  while `OughtStar` stays false everywhere: separation made machine-explicit.
  Footprint: `{}` (local defs only; strictly zero axioms). -/
theorem amoral_model_separation :
    (∃ s : S, RightWrongStar s) ∧ (¬ ∃ r : S, ∃ s : S, ∃ a : PracticalAction, OughtStar r s a) :=
  ⟨amoral_model_satisfies_epistemic_agential_normativity, amoral_model_has_no_practical_obligation⟩

/--The amoralist thesis holds in the amoral model.
-/
theorem amoralist_thesis_true_in_model : AmoralistThesis := by
  intro h
  rcases h with ⟨r, s, a, ho⟩
  exact ho

/--The amoralist thesis is judgeable-as-correct in the model: satisfiable, not self-refuting.
  The flip made formal: `AmoralistThesis` is TRUE here (unlike epistemic `D`),
  so a correct judgement of it is witnessed.
  Footprint: `{}`. -/
theorem amoral_disconnection_is_judgeable_as_correct :
    ∃ s : S, CorrectStar s AmoralistThesis :=
  ⟨soleSubject, ⟨⟨trivial, ⟨(), (), trivial⟩⟩, amoralist_thesis_true_in_model⟩⟩

/--The amoralist thesis is consistent with the epistemic reality-hook.
  Full consistency package: no practical bindingness, agential normativity present,
  and every correct judgement tracks reality — the countermodel is total.
  Footprint: `{}`. -/
theorem amoralist_consistent_with_reality_hook :
    AmoralistThesis ∧ (∃ s : S, RightWrongStar s) ∧
      (∀ s : S, ∀ p : Prop, CorrectStar s p → p) :=
  ⟨amoralist_thesis_true_in_model, amoral_model_satisfies_epistemic_agential_normativity,
   fun s p h => correct_star_tracks_reality s p h⟩

end M_amoral

-- ===========================================================================
-- §5.2b The F3 separation (row-of-record for the frontier countermodel C175)
-- ===========================================================================

/--Epistemic agential normativity does not force practical bindingness: the machine witness
  of the moral frontier's separation (F3 → countermodel frontier, ledger row C175).
  The hostile local model `M_amoral` keeps the full epistemic reality-hook and
  judicative-pole agential normativity while practical obligation is false everywhere;
  the moral bridge is therefore OPEN, not closed.
  Footprint: `{}` (strictly zero axioms). -/
theorem epistemic_normativity_without_practical_obligation :
    (∃ s : M_amoral.S, M_amoral.RightWrongStar s) ∧
      (¬ ∃ r : M_amoral.S, ∃ s : M_amoral.S, ∃ a : PracticalAction, M_amoral.OughtStar r s a) :=
  ⟨M_amoral.amoral_model_satisfies_epistemic_agential_normativity,
   M_amoral.amoral_model_has_no_practical_obligation⟩

-- ===========================================================================
-- §5.4 The fair relational Good (2026-09-24) — the positive close of F3
-- ===========================================================================

/--Moral good, defined fairly as genuine benevolence toward another person.
  A subject's practical action is *good* (the positive moral pole) exactly when the
  subject helps some other person and harms no one — the poem's "ajuda / não
  prejudica" read relationally ("não ajuda nem prejudica ninguém", P6) with the
  'other' supplied as a real person by the plural/value layer.

  This is a *fair definition* (MORAL.md §8b): the definiendum is the intended content
  of the positive moral pole — helpfulness toward the other IS moral good — so the
  consequences that follow are declared, not smuggled. It is NOT an epistemic collapse
  (Good is not Correct) and NOT self-legislation (Good is not my inclination). The
  action argument `a` is the context of evaluation; the value layer indexes bearing by
  subject-pairs, so the moral character at `a` is the subject's bearing toward the other.
  Footprint: `{Means, Subject, Will, subjectWill}` (vocabulary-only — the definition itself smuggles nothing;
  only the pole's *inhabitation* pays the disclosed bridge, in `moral_good_obtains`). -/
def Good (s : Subject) (_a : Prop) : Prop :=
  ∃ t : Subject, t ≠ s ∧ Person t ∧ Helps s t ∧ ¬ Harms s t

/--Moral good obtains: some subject's action is genuinely good.
  Under the disclosed META bridge `AxBenevolentBearingObtains` ("some person is
  actually helped"), the fair positive pole `Good` is inhabited — the F3 frontier's
  positive close, earned honestly: the pole is *defined* (fairly, no hidden axiom) and
  its *existence* rests on one declared, priced bridge. Footprint:
  `{AxBenevolentBearingObtains, Means, Subject, Will, subjectWill}` (the price, written out loud). -/
theorem moral_good_obtains : ∃ s : Subject, ∃ a : Prop, Good s a := by
  obtain ⟨s, t, hne, hpt, hh⟩ := some_person_is_helped
  exact ⟨s, True, ⟨t, Ne.symm hne, hpt, hh, help_not_harm hh⟩⟩

/--
Tag: SEM
Evil: the negative moral pole of a subject's practical action — a declared semantic datum.

The negative pole is still *declared*, not yet derived: the fair relational reading of
Evil ("harms another person") is uninhabited in the pure theory, because `Harms` is
refutable for every pair (`Logos.Value.harms_unobtainable`) — harm does not obtain
without a disclosed datum parallel to `AxBenevolentBearingObtains`. Until that parallel
"some harm occurs" bridge is declared and disclosed, the negative moral pole keeps its
declared SEM status. The positive pole `Good` is already derived (see `moral_good_obtains`).

The poles are genuinely additional, never forced: the consistency witness
`moral_pole_postulate_is_not_a_consequence` interprets any poles as false everywhere
while the epistemic reality-hook stays intact; the amoral model `M_amoral` proves the
relying structure carries no practical obligation, so any positive bridge must postulate.

Philosophical cost: declaring the negative moral pole (Evil) is a substantive semantic
commitment — the price sheet of the moral-frontier bridge (F3): epistemic agential
normativity is machine-separated from practical bindingness (`M_amoral`, C175), so
bindingness cannot be read off the relying structure. The positive pole no longer pays
this price (it is derived); the negative pole still does.
-/
axiom Evil : Subject → Prop → Prop

/--The moral-judicative stance: the subject performs its act and means its action's Good and
  Evil — mirroring the normative-judicative stance with the fair positive pole and the
  declared negative pole.
  Footprint: `{Evil, Initiates, Means, State, Subject, Will, subjectWill}` — the fair `Good` def is
  vocabulary-only, so the *stance* costs only the still-declared negative pole. -/
def ClaimsMoralRectitude (s : Subject) (a : PracticalAction) : Prop :=
  Act s a.prop ∧ Means s (Good s a.prop) ∧ Means s (Evil s a.prop)

/--The stance exhibits both moral poles: moral rectitude towards an action means the subject
  means its goodness and its evil.
  Footprint: `{Evil, Initiates, Means, State, Subject, Will, subjectWill}`. -/
theorem stance_exhibits_moral_poles (s : Subject) (a : PracticalAction)
    (h : ClaimsMoralRectitude s a) : Means s (Good s a.prop) ∧ Means s (Evil s a.prop) :=
  h.2

/--The moral poles are genuinely additional: interpretable as false everywhere with the
  epistemic reality-hook intact — never forced by the relying structure. (This remains true
  after the positive close: `Good` obtains only under the *declared* bridge
  `AxBenevolentBearingObtains`, never as a consequence of the normative relying structure
  alone — which is exactly what this countermodel certifies.)
  Footprint: `{Initiates, Means, State, Subject}` (vocabulary-only). -/
theorem moral_pole_postulate_is_not_a_consequence :
    ∃ G E : Subject → Prop → Prop,
      (¬ ∃ s : Subject, ∃ p : Prop, G s p) ∧
      (¬ ∃ s : Subject, ∃ p : Prop, E s p) ∧
      (∀ s : Subject, ∀ p : Prop, Correct s p → p) :=
  ⟨fun _ _ => False, fun _ _ => False,
   (by rintro ⟨s, p, h⟩; exact h),
   (by rintro ⟨s, p, h⟩; exact h),
   fun s p h => correct_tracks_reality s p h⟩

end Logos.MoralFrontierAudit

-- ---------------------------------------------------------------------------
-- Axiom footprint audit (expected values pinned in WITNESS.md §5; corrected
-- against the true `#print axioms` output after `lake build`)
-- ---------------------------------------------------------------------------
#print axioms Logos.MoralFrontierAudit.M_amoral.S
#print axioms Logos.MoralFrontierAudit.M_amoral.soleSubject
#print axioms Logos.MoralFrontierAudit.M_amoral.Means
#print axioms Logos.MoralFrontierAudit.M_amoral.State
#print axioms Logos.MoralFrontierAudit.M_amoral.Initiates
#print axioms Logos.MoralFrontierAudit.M_amoral.Act
#print axioms Logos.MoralFrontierAudit.M_amoral.CorrectStar
#print axioms Logos.MoralFrontierAudit.M_amoral.IncorrectStar
#print axioms Logos.MoralFrontierAudit.M_amoral.OughtStar
#print axioms Logos.MoralFrontierAudit.M_amoral.GenuineNormativityStar
#print axioms Logos.MoralFrontierAudit.M_amoral.RightWrongStar
#print axioms Logos.MoralFrontierAudit.M_amoral.AmoralistThesis
#print axioms Logos.MoralFrontierAudit.M_amoral.correct_star_tracks_reality
#print axioms Logos.MoralFrontierAudit.M_amoral.amoral_model_satisfies_epistemic_agential_normativity
#print axioms Logos.MoralFrontierAudit.M_amoral.amoral_model_has_no_practical_obligation
#print axioms Logos.MoralFrontierAudit.M_amoral.amoral_model_separation
#print axioms Logos.MoralFrontierAudit.M_amoral.amoralist_thesis_true_in_model
#print axioms Logos.MoralFrontierAudit.M_amoral.amoral_disconnection_is_judgeable_as_correct
#print axioms Logos.MoralFrontierAudit.M_amoral.amoralist_consistent_with_reality_hook
#print axioms Logos.MoralFrontierAudit.epistemic_normativity_without_practical_obligation
#print axioms Logos.MoralFrontierAudit.Good
#print axioms Logos.MoralFrontierAudit.moral_good_obtains
#print axioms Logos.MoralFrontierAudit.Evil
#print axioms Logos.MoralFrontierAudit.ClaimsMoralRectitude
#print axioms Logos.MoralFrontierAudit.stance_exhibits_moral_poles
#print axioms Logos.MoralFrontierAudit.moral_pole_postulate_is_not_a_consequence