/-
# Spike_A6_probe.lean — M4 of FORCED_SUBJECT.md: AxGlobalGround price-reduction probe

`AxGlobalGround` (Modal.lean, SEM) is the declared `∀w∃r ⇒ ∃r∀w` swap of T7:

    NecessarilyTrue φ → ∃ e, ∀ w, ExistsAt w e ∧ Ground e φ

The swap is invalid in general (standard model-theoretic counterexamples), so
a full derivation is not expected. Q7.2 asks whether a *weaker* premise can
carry the same theorems. This probe tests the candidate weakening:

    AxGlobalMirror :  NecessarilyTrue φ →
        (∃ w, ExistsAt w e ∧ Ground e φ) → ∃ e', NecessaryEntity e' ∧ Ground e' φ

("every *world-contingent ground* of a necessary truth is mirrored by a
necessary ground"). It only constrains grounds that already exist in some
world — no direct `∃r∀w` over `τ`.

VERDICT (2026-09-16): **price-reduction possible, footprint shrinks by one
grounding-load clause; coverage narrows to atoms.** Concretely:

  * T7 restricted to ATOMS is derivable from `AxGlobalMirror` alone
    (`T7_atom_via_mirror` below, kernel-checked): `groundPrinciple_atom`
    lends a world-contingent ground, Mirror upgrades it to a necessary one.
    The `∀ w, ExistsAt w e ∧ Ground e φ` clause is not needed — the
    `Ground`-load at all other worlds is a free gift of the stronger axiom,
    and Mirror does the same job with less.
  * The COMPOUND path is unavailable (SPIKE-STUCK below): T7's
    excluded-middle instance needs an existential ground of a compound
    `or φ (not φ)`, which A2 deliberately leaves unforced (structural
    TrueAt: only atoms carry existential grounding). So a full
    replacement of `AxGlobalGround` by `AxGlobalMirror` would change what
    T7 covers — NOT a clean demotion.

Report for FORCED_SUBJECT.md: **stays priced (smaller).** `AxGlobalGround`
is not demoted; the recorded, weaker candidate exists and is honest, but it
is a *different axiom* (atom-restricted coverage), not a footprint-preserving
replacement. Adopting it is a semantic choice to be rejected or accepted as
a SEPARATE recorded position.

Not part of the library build (Spikes/ excluded). `sorry` = SPIKE-MARKER.
-/

import Logos.Core
import Logos.Semantics
import Logos.Truthmaker
import Logos.Modal

namespace Logos.SpikeA6

open Logos.Semantics (Form World)
open Logos.Truthmaker (Entity Ground ExistsAt TrueAt NecessarilyTrue groundPrinciple_atom)
open Logos.Modal (NecessaryEntity actualWorld)
open Logos.Agency (Subject)

-- | The candidate weaker premise (NOT added to the theory; probe only).
axiom AxGlobalMirror : ∀ (φ : Form), NecessarilyTrue φ →
    ∀ (e : Subject), (∃ w : World, ExistsAt w e ∧ Ground e φ) →
      ∃ e' : Subject, NecessaryEntity e' ∧ Ground e' φ

/-- T7 restricted to atoms IS derivable from the weak premise alone.
    `groundPrinciple_atom` supplies a world-contingent ground (at the present
    world); `AxGlobalMirror` upgrades it to a necessary one. Kernel-checked:
    the footprint of this theorem is {Subject, Means, ExistsAt, Ground,
    AxGlobalMirror} — it does NOT use `AxGlobalGround`. -/
theorem T7_atom_via_mirror (n : Nat) (hnec : NecessarilyTrue (Form.atom n)) :
    ∃ e' : Subject, NecessaryEntity e' ∧ Ground e' (Form.atom n) := by
  have hg : ∃ e : Subject, ExistsAt actualWorld e ∧ Ground e (Form.atom n) :=
    groundPrinciple_atom actualWorld n (hnec actualWorld)
  obtain ⟨e, he_w, hg_e⟩ := hg
  exact AxGlobalMirror (Form.atom n) hnec e ⟨actualWorld, he_w, hg_e⟩

/-- The COMPOUND path fails under the weak premise (SPIKE-STUCK-MARKER):
    for `φ := or θ (not θ)` the structural (A2) truthmaker gives `TrueAt`
    without any existential ground — so no world-contingent ground exists to
    feed Mirror. The strong axiom's `∃r∀w` over the whole formula is doing
    the work here, and the weak premise cannot replace it. -/
theorem T7_excludedMiddle_via_mirror (θ : Form) :
    ∃ e' : Subject, NecessaryEntity e' ∧ Ground e' (Form.or θ (Form.not θ)) := by
  sorry

end Logos.SpikeA6