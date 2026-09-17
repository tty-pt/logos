/-
# Logos.Modal — necessity, contingency, and T7 (base.txt §22→T7)

T7 in the prose runs: necessary truth τ ⇒ τ is grounded in no *contingent*
entity ⇒ some non-contingent reality grounds τ ⇒ ∃r □Exists(r).

The informal step `∀w∃r … ⇒ ∃r∀w …` is now a THEOREM for atoms
(batch A2-swap-theorem, 2026-09-17): `ExistsAt` is world-vacuous by
definition (esse est agere), so the witness from any one world works for
all worlds definitionally — no swap axiom is needed. The compound
excluded-middle instance stays unforced (structural `TrueAt` carries no
existential ground for compounds; M4 spike) and is recorded BLOCKED with
its exact missing lemma (GAPMAP.md C19).

Sub-question Q7.2 (ANSWERED, see DESIGN.md): for atoms the swap needs no
weaker premise — it is definitional; the compound instance is a different,
unforced claim, not a footprint-preserving replacement.
-/

import Logos.Core
import Logos.Semantics
import Logos.Truthmaker

namespace Logos.Modal

open Logos.Semantics (Form World)
open Logos.Truthmaker (Entity Ground ExistsAt TrueAt NecessarilyTrue)

/-- The present world (SEM, definitional): the performed actuality of the
    reasoning act needs only *some* fixed world in T7 (`Ground e τ` is invoked
    at it and nothing depends on which world it is). Modeled as the
    always-true valuation (precedent: `Necessity.someWorld`). No longer an
    axiom: `def actualWorld` shrinks the C18–C20 footprints. -/
def actualWorld : World := fun _ => Logos.Semantics.TV.t

/-- An entity is necessary iff it exists in every world. -/
def NecessaryEntity (e : Entity) : Prop := ∀ w : World, ExistsAt w e

/-- An entity is contingent iff it is not necessary. -/
def Contingent (e : Entity) : Prop := ¬ NecessaryEntity e

/--An atomic formula true in every world is grounded by a single entity existing in every world (the quantifier swap, atom-restricted).

 AxGlobalGround (theorem, batch A2-swap-theorem 2026-09-17; former SEM
    axiom, D7): a necessarily-true atom is grounded by a single entity
    that exists in every world. Name kept (precedent: `AxPersonStability`).

    Proof: `groundPrinciple_atom` at any one world supplies the grounder;
    `ExistsAt` is world-vacuous by definition (esse est agere) and `Ground`
    is world-rigid, so the same entity works at every world — the swap
    dissolves definitionally. Restricted to atoms: structural `TrueAt`
    carries no existential ground for compounds, so the excluded-middle
    instance `∃ e, Ground e (or θ (not θ))` stays unforced (recorded
    BLOCKED, GAPMAP.md C19; M4 transcript in
    `formal/Spikes/Spike_A6_probe.lean`). -/
theorem AxGlobalGround (n : Nat) (hnec : NecessarilyTrue (Form.atom n)) :
    ∃ e : Entity, ∀ w : World, ExistsAt w e ∧ Ground e (Form.atom n) := by
  obtain ⟨e, he_w, hg_e⟩ :=
    Logos.Truthmaker.groundPrinciple_atom actualWorld n (hnec actualWorld)
  exact ⟨e, fun w => ⟨he_w, hg_e⟩⟩

/--Atomic necessary truth forces necessary reality: whatever atom is true in every world is grounded by an entity existing in every world.

 T7 — atomic necessary truth forces necessary reality (base.txt T7,
    atom-restricted).

    PROVEN {Ground}-vocab (batch A2-swap-theorem; former PROVEN↑ under the
    `AxGlobalGround` axiom). -/
theorem T7_necessaryReality (n : Nat) (hnec : NecessarilyTrue (Form.atom n)) :
    ∃ e : Entity, NecessaryEntity e ∧ Ground e (Form.atom n) := by
  obtain ⟨e, he⟩ := AxGlobalGround n hnec
  exact ⟨e, fun w => (he w).1, (he actualWorld).2⟩

/--If every entity were contingent, no atom could be true in every world.

 The reductio shape of the prose, atom-restricted: if every entity were
    contingent, no atomic formula could be necessarily true. -/
theorem noNecessaryTruthIfAllContingent :
    (∀ e : Entity, Contingent e) → ∀ n : Nat, ¬ NecessarilyTrue (Form.atom n) := by
  intro hall n hτ
  obtain ⟨e, hne, _⟩ := T7_necessaryReality n hτ
  exact (hall e) hne

end Logos.Modal

-- Axiom footprint audit
#print axioms Logos.Modal.AxGlobalGround
#print axioms Logos.Modal.T7_necessaryReality
#print axioms Logos.Modal.noNecessaryTruthIfAllContingent
