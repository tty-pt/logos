/-
# Logos.SuccessionCountermodel — the succession field places no constraint on entity-level production

Companion to `Logos.SuccessionAudit`, in the free-signature style of `ModalPossibilityFrontier.lean`
and `DeepModalFrontier.lean`: a model, not a theorem about Γ's sorts, so that its footprint is `{}`
and it is not evidence about Γ itself. What it *is* evidence about is the **shape** of
`NotInSuccession`.

Governing rule, from `AGENTS.md` and from C321: a property that holds of everything is not a
characterisation, and the way to show that is to exhibit a model in which the property holds of a
thing it is supposed to exclude. C321 did it for `capacity_invariance`; this module does it for
`transition_invariance`, and the thing it must fail to exclude is **entity-level production**.

The model keeps the live definition's shape verbatim —

    ¬ ∃ s σ σ' p, e = EntityOf s ∧ Initiates s σ σ' p

— and adds a production relation `Produces : Entity → World → Form → Prop`, which is the signature
F10 asks for (`DivineOmnipotence.lean:55`). The ground is given the trivial production relation and
is still outside succession. Nothing in the definition mentions `Produces`, so nothing could have
excluded it: the two-lane design that `agere sequitur esse` requires is not a subtlety of wording, it
is forced by which relations the definitions quantify over.

This is the model-theoretic shadow of C467 in the live batch: there, the ground produces *and* is
immutable, both machine-checked. Here, the claim is only that the succession field cannot object.
-/

import Logos.Core

namespace Logos.SuccessionCountermodel

-- ===========================================================================
-- Part I: The definition under test, in the live shape
-- ===========================================================================

/-- The live body of `NotInSuccession` (`NecessityEternity.lean:102-104`), reproduced verbatim over a
    free signature so the model tests the shape rather than Γ's sorts. -/
def ModelNotInSuccession {Entity Subject State : Type} (EntityOf : Subject → Entity)
    (Initiates : Subject → State → State → Prop → Prop) (e : Entity) : Prop :=
  ¬ ∃ s σ σ' p, e = EntityOf s ∧ Initiates s σ σ' p

/-- A model in which the ground is outside succession **and** produces.

 `Produces` is a parameter, so the model says: *for some production relation, a ground-like entity
 is both inert with respect to succession and a producer.* It is deliberately left arbitrary rather
 than fixed to the trivial relation, because the point is that nothing in
 `ModelNotInSuccession`'s body constrains it. -/
structure GroundProducesCountermodel (Entity Subject State World Form : Type)
    (EntityOf : Subject → Entity)
    (Initiates : Subject → State → State → Prop → Prop)
    (Produces : Entity → World → Form → Prop)
    (g : Entity) (w : World) (φ : Form) : Prop where
  /-- The ground is the correlate of no subject — the type fact that discharges the field. -/
  g_is_no_correlate : ∀ s : Subject, EntityOf s ≠ g
  /-- The live succession field, in the live shape. -/
  g_outside_succession : ModelNotInSuccession EntityOf Initiates g
  /-- And yet it produces a form in a world. -/
  g_produces : Produces g w φ

/-- C461 — a ground-like entity can produce a form in a world while satisfying the succession field.

 The countermodel, exhibited. `Entity := Bool` with the ground at `true` and every subject's correlate
 at `false`, so the ground is nobody's correlate and the field is satisfied by disjointness alone;
 `Produces` is the constant-true relation, so the ground produces; `Initiates` is never even
 reachable, and is set to `False` throughout to make the point that its *value* is irrelevant.

 Read against C459: the field distinguishes the ground from nothing, and this row shows what that
 costs — a reading of immutability in which the ground cannot act is *available in the models* and
 therefore cannot be the content of the definition. The two lanes (`Initiates` for subjects,
 `Produces` for entities) are compatible because the definitions are about different things; the
 conflict was never in the relations but in a **word**.

 Footprint: `{}`. -/
theorem a_ground_can_produce_while_outside_succession :
    ∃ (Entity Subject State World Form : Type)
      (EntityOf : Subject → Entity)
      (Initiates : Subject → State → State → Prop → Prop)
      (Produces : Entity → World → Form → Prop)
      (g : Entity) (w : World) (φ : Form),
      GroundProducesCountermodel Entity Subject State World Form EntityOf Initiates Produces g w φ := by
  refine ⟨Bool, Unit, Unit, Unit, Unit, fun _ => false, fun _ _ _ _ => False, fun _ _ _ => True,
    true, (), (), ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro _s
    decide
  · rintro ⟨s, _σ, _σ', _p, hEq, _hInit⟩
    exact nomatch hEq
  · trivial

#print axioms a_ground_can_produce_while_outside_succession

end Logos.SuccessionCountermodel
