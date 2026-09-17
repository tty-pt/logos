/-
# Spike_PersonStability.lean — M3 of FORCED_SUBJECT.md: AxPersonStability re-spike

Target: `PERSON_PERSISTS := ∀ s : Subject, Person s → NecessarySubject s`
("every person's entity-correlate exists in every world"). Success would
promote `AxPersonStability` to a theorem and drop 1 declaration.

Newly available (post-M0/M1): `Cogito` (a present person), T8's necessary
personal entity `e₀ : Entity` (via `AxPersonalGround` + a present feature),
and A3 distinctness.

Status (verdict of this spike, 2026-09-16): **BLOCKED**. The theory produces
a NECESSARY entity `e₀` (exists in all worlds) grounded on a present personal
feature — but `Realizes e₀ f` does NOT identify `e₀` with the present person
`s` of the act, and nothing forces the *act's* subject to exist in all
worlds. `NecessarySubject s` needs `∀ w, ExistsAt w s`, and `Person` (=
`∃ p, Means s p`) has no connection to `ExistsAt`. The priced SEM bridge
`AxPersonStability` stands (designated countermodel: persons contingent, one
necessary non-personal subject).

SUPERSEDED 2026-09-17 by esse-est-agere (transcript preserved): `ExistsAt`
is now the agency definition, supplying the missing Means→ExistsAt rule, so
`AxPersonStability` is a `{}` theorem in `Logos.Love` and this spike's target
is proven. The `sorry` below remains as the historical record of the wall.

Not part of the library build. The `sorry` is a tagged SPIKE-MARKER.
-/

import Logos.Core
import Logos.Agency
import Logos.Person
import Logos.Plurality
import Logos.Value
import Logos.GroundPerson
import Logos.Modal

namespace Logos.SpikePersonStability

open Logos.Agency (Subject Means A)
open Logos.Person (Person)
open Logos.Plurality (NecessarySubject EntityOf)
open Logos.Truthmaker (ExistsAt Entity)
open Logos.Modal (NecessaryEntity)

-- | The target under test.
def PERSON_PERSISTS : Prop := ∀ s : Subject, Person s → NecessarySubject s

-- ---------------------------------------------------------------------------
-- 1. What the theory gives (kernel-checked, no sorry)
-- ---------------------------------------------------------------------------

/-- A present personal feature (from Cogito). -/
theorem present_feature : ∃ f : Prop, Logos.GroundPerson.IsPresentPersonalFeature f := by
  obtain ⟨s, p, hmp⟩ := Logos.Agency.Cogito
  exact ⟨p, s, p, hmp, hmp, rfl⟩

/-- T8 content: the necessary reality grounds the present personal feature —
    a NECESSARY entity `e₀` exists and realizes the feature (under the META
    bridge `AxPersonalGround`). -/
theorem necessary_ground_of_present : ∃ e : Entity,
    NecessaryEntity e ∧ ∃ f : Prop, Logos.GroundPerson.Realizes e f := by
  obtain ⟨f, hf⟩ := present_feature
  obtain ⟨e, hne, hg⟩ := Logos.GroundPerson.AxPersonalGround hf
  exact ⟨e, hne, f, hg⟩

-- ---------------------------------------------------------------------------
-- 2. The stuck attempt (SPIKE-MARKER).
--
-- The bridge pays for a necessary entity `e₀` *grounding a feature*; the
-- love layer needs the ACT's subject `s` to persist across worlds. Nothing
-- connects them: `Entity := Subject` only says the carrier coincides, and
-- `Realizes e f` is `GroundProp e f` — a grounding judgment, not an identity.
-- `Person s` (∃ p, Means s p) is a fact at the act level; `ExistsAt` is a
-- separate vocabulary relation with no introduction rule from `Means`.
-- ---------------------------------------------------------------------------
theorem stuck_person_persists : PERSON_PERSISTS := by
  intro s hs
  obtain ⟨e₀, hne₀⟩ := (show ∃ e : Entity, NecessaryEntity e by
    obtain ⟨e, hne, _⟩ := necessary_ground_of_present
    exact ⟨e, hne⟩)
  -- SPIKE-STUCK-MARKER: we have a necessary subject e₀, but `NecessarySubject s`
  -- requires `∀ w, ExistsAt w s`. No rule turns (Means s p / GroundProp e₀ f /
  -- NecessaryEntity e₀) into ExistsAt-w-persistence of s itself. Designated
  -- countermodel: two subjects, one necessary (e₀), one contingent person (s).
  sorry

end Logos.SpikePersonStability