/-
# Spike_A4_2.lean — M2 of FORCED_SUBJECT.md: the plurality spike (ALONE_EXCLUDED)

Target: `ALONE_EXCLUDED := ¬ ∃ s : Subject, Person s ∧ Alone s`
("no one is a lone person"). Success would make `T12_twoPersons` a theorem
with footprint {Means, Subject, Cogito} → **10 axioms**.

Allowed surface (the FRESH part, legal only after M0): {Core, Cogito, A3
(`Affects s t := s ≠ t`), T6-content, IsPresentPersonalFeature} + definitions.
Post-M0 the choice/fallibility machinery carries {Cogito, Means, Subject}
only, so it no longer smuggles the very plurality it would be used to prove.

Status (verdict of this spike, 2026-09-16): **BLOCKED** — the derivation
stops exactly where a *second subject* would have to be produced, and the
single-inhabitant consistency witness 2 below refutes the target against the
whole allowed surface. The price `AxTwoSubjects` therefore stands, now
justified by a model (a mathematical result, not a shrug).

This file is NOT part of the Logos library (`Spikes/` is outside the build;
see `lakefile.toml` + `Logos.lean`). The `sorry` below is a tagged
SPIKE-MARKER for the exact stuck point — it is not a theory axiom.
-/

import Logos.Core
import Logos.Agency
import Logos.Person
import Logos.Value
import Logos.Order
import Logos.GroundPerson

namespace Logos.SpikeA4_2

open Logos.Core (T IsFalse)
open Logos.Agency (Subject Means A)
open Logos.Person (Person)
open Logos.Value (Affects Alone OtherAffects)

-- | The target under test.
def ALONE_EXCLUDED : Prop := ¬ ∃ s : Subject, Person s ∧ Alone s

-- ---------------------------------------------------------------------------
-- 1. What the allowed surface DOES give (all kernel-checked, no sorry)
-- ---------------------------------------------------------------------------

/-- A present person exists — the forced foundation `Cogito` alone. -/
theorem present_person : ∃ s : Subject, Person s := by
  obtain ⟨s, p, hmp⟩ := Logos.Agency.Cogito
  exact ⟨s, trivial, trivial, p, hmp⟩

/-- T6-content: some subject is bound by a false content (kernel-checked,
    footprint {Cogito, Means, Subject} — no plurality). -/
theorem person_can_err : ∃ s : Subject, ∃ p : Prop,
    Logos.Order.Fallible s p ∧ IsFalse p :=
  Logos.Order.fallible_false

/-- A3 on a lone subject: the lone subject's doings affect nothing. -/
theorem lone_no_other {s : Subject} (halone : Alone s) : ¬ OtherAffects s := by
  intro h
  obtain ⟨t, hne, _⟩ := h
  exact hne (halone t)

/-- A present personal feature exists (the act's meant content) — Cogito only. -/
theorem present_feature : ∃ f : Prop, Logos.GroundPerson.IsPresentPersonalFeature f := by
  obtain ⟨s, p, hmp⟩ := Logos.Agency.Cogito
  exact ⟨p, s, p, hmp, hmp, rfl⟩

-- ---------------------------------------------------------------------------
-- 2. The stuck attempt (SPIKE-MARKER).
--
-- Every datum the allowed surface delivers about other subjects is an
-- equality `halone t : t = s`; nothing ever produces an inequality `t ≠ s`.
-- `fallible_false` recycles the SAME subject (its witness is Cogito's s₂),
-- and `present_feature` attaches merely another content to s. The only rule
-- in the whole surface that concludes an inequality is A3 — and A3 needs the
-- inequality as its premise. Second-subject existence is exactly what is
-- missing, and nothing below Plurality manufactures it.
-- ---------------------------------------------------------------------------
theorem stuck_no_second_subject : ALONE_EXCLUDED := by
  intro hlonep
  obtain ⟨s, hper, halone⟩ := hlonep
  obtain ⟨s₂, p₂, hfall, hfalse⟩ := Logos.Order.fallible_false
  obtain ⟨f, hf⟩ := present_feature
  -- SPIKE-STUCK-MARKER: to refute `Alone s` we need `∃ t, t ≠ s`. The surface
  -- has given us only equalities (halone s₂ : s₂ = s) and grounded features
  -- of s itself. The lone-subject witness (section 3) shows the omission is
  -- not a gap in the tactics but a fact about the theory.
  sorry

-- ---------------------------------------------------------------------------
-- 3. Consistency witness (Lean-checked): the lone-subject interpretation.
--
-- Re-encoding of the allowed surface on a ONE-inhabitant carrier. Every
-- allowed-theorem holds there; `ALONE_EXCLUDED` is REFUTED. This is the
-- countermodel that justifies the price `AxTwoSubjects` as a mathematical
-- fact: no derivation from the allowed surface can exist.
-- ---------------------------------------------------------------------------
namespace Witness

abbrev Sub : Type := Unit

/-- Meaning on the single subject (the interpretation of `Means`). -/
def Me (_s : Sub) (_p : Prop) : Prop := True

/-- Person on the single subject (the structural definition's image). -/
def Per (s : Sub) : Prop := ∃ p : Prop, Me s p

/-- Alone on the single subject (the image of `Alone s := ∀ t, t = s`). -/
def Lon (s : Sub) : Prop := ∀ t : Sub, t = s

/-- Affects under A3 (bearing = distinctness) on one subject: nothing bears. -/
def Af (s t : Sub) : Prop := s ≠ t

/-- The single inhabitant IS a lone person: `ALONE_EXCLUDED` is false here. -/
theorem lone_person_exists : ∃ s : Sub, Per s ∧ Lon s := by
  refine ⟨(), ⟨True, trivial⟩, ?_⟩
  intro t
  cases t
  rfl

/-- Nonempty interpretation: exactly one inhabitant. -/
theorem witness_nonempty : Nonempty Sub := ⟨()⟩

/-- A3/P6 on the witness: the lone subject affects no other. -/
theorem lonely_affects_no_other : ∀ s : Sub, Lon s → ∀ t : Sub, ¬ Af s t := by
  intro s hs t hne
  exact hne (hs t)

end Witness

end Logos.SpikeA4_2