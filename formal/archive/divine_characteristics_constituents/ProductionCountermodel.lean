/-
# Logos.ProductionCountermodel — the ground's production cannot be the causal/creative relation F10 asks for

Companion to the `ACT-CASCADE` batch (`WIN.md` §2 B2) and to `Logos.SuccessionCountermodel`, in the
same free-signature style: a model, not a theorem about Γ's sorts, so that its footprint is `{}`
and it is **not evidence about Γ itself**. What it *is* evidence about is the **shape** of the
missing derivation. Plan of record: `WIN.md`.

## The gap

`DivineOmnipotence.lean` records F10's causal/creative sense as `BLOCKED`, and names its two
missing pieces exactly:

    (1) MISSING VOCABULARY — a production relation, one level down from `Initiates`:
        Produces : Entity → World → Form → Prop
    (2) MISSING DERIVATION — the causal sense, which (1) alone does not give:
        for all g : Entity and all φ : Form,
          (∃ w, Satisfies w φ) → ∃ v, Produces g v φ

Piece (1) was supplied by C463 (`Produces`, `Tag: VOCAB`). What (2) asks for is a
*per-form* relation between satisfiability and production. What C465 (`ground_love_produces`)
delivers is a different statement entirely: given a love-instance, the ground produces **some**
form in **some** world. `∃ w φ, Produces g w φ` is not `∀ φ, (∃ w, Satisfies w φ) → ∃ v,
Produces g v φ`, and nothing in the vocabulary relates them.

**The model below exhibits exactly that gap.** It is a model in which

- the ground produces *something* (C465's conclusion holds), and
- the ground fails to produce a *second satisfiable form* (F10's (2) fails),

  so the two shapes are independent. There is no derivation of (2) from (1) and C465's shape, and
  closing (2) requires a new bridge relating satisfiability to production — which is precisely the
  new substantive content declared as C493 on 2026-09-29. This model remains the proof that the
  bridge was needed; it is not falsified by paying for it.

## Why the counter-interpretation is admissible

`Produces` is a `Tag: VOCAB` axiom. Nothing in the corpus constrains it: it is not monotone, not
functional per form, not total, not grounded in `Satisfies`. The module therefore uses the
interpretation `Produces g w φ := φ = φ₀` — the ground produces one distinguished form and
nothing else. This is *not* a strawman: it is a total, well-defined interpretation of an
unconstrained relation, and `SuccessionCountermodel` uses exactly this device for `Produces`
itself. A row whose conclusion depended on `Produces` being richer than the corpus requires would
be a claim about the axiom, not about Γ's derivability, and would have to be priced.

  **Governed distinction.** The absence of a bridge here is *not* a refutation of F10. F10's former
  `BLOCKED` status is now replaced by the declared C493 bridge, and the corpus's standing note is that (1) alone would not have yielded (2), and
`means_does_not_imply_means_selection` (`HostileSemantics.lean:1861`) already machine-checks that
omni-scope does not entail selection power. What this module buys is that the blockage is now
**settled with its price named** — two named primitives (`Satisfies`, `Produces`) and no bridge
between them — rather than merely asserted in a prose header.
-/

import Logos.Core

namespace Logos.ProductionCountermodel

/-! ## Part I: the two shapes, over a free signature

`ModelProducesSomething` is the shape of C465's conclusion. `ModelProducesEverySatisfiable` is the
shape of F10's missing derivation (2). They are deliberately stated with no reference to
`GroundLoves`: the countermodel's point is that the *gap between the two shapes* is unbridgeable
without relating the production relation to satisfiability, and the love-hypothesis is not what
would close it. -/

/-- **C465's conclusion, in shape only:** the ground produces *some* form in *some* world.

    Mirrors `ThomisticAct.ground_love_produces` with the love-hypothesis abstracted away, so that
    the countermodel is about the shape of the conclusion and not about Γ's sorts. -/
def ModelProducesSomething (Entity World Form : Type)
    (Produces : Entity → World → Form → Prop) (g : Entity) : Prop :=
  ∃ w : World, ∃ φ : Form, Produces g w φ

/-- **F10's missing derivation (2), in shape only:** every satisfiable form is produced.

    Mirrors `DivineOmnipotence.lean`'s recorded gap, quantifier for quantifier. -/
def ModelProducesEverySatisfiable (Entity World Form : Type)
    (Satisfies : World → Form → Prop)
    (Produces : Entity → World → Form → Prop) (g : Entity) : Prop :=
  ∀ φ : Form, (∃ w : World, Satisfies w φ) → ∃ v : World, Produces g v φ

/-! ## Part II: the countermodel -/

/-- A model in which the ground produces something (C465's shape) but not every satisfiable form
    (F10's shape).

    All four fields are load-bearing, and each blocks a different way of closing the gap:

    - `φ₀_satisfiable` / `φ₁_satisfiable` — the two forms are both *satisfied*, so the failure is
      not "φ₁ is unsatisfiable and F10 does not range over it". This is the field that makes the
      countermodel honest rather than a trick: the antecedent of (2) genuinely holds.
    - `distinct` — φ₁ is a genuinely different form, so the relation is not being asked to produce
      "the same form twice", which would make `φ = φ₀` a non-counterexample.
    - `c465_holds` — C465's conclusion holds. Without this the model would refute (2) in a world
      where the ground produces nothing, which is no tension at all.
    - `f10_fails` — and (2) fails anyway. This is the countermodel. -/
structure ProducesOneFormOnly (Entity World Form : Type)
    (Satisfies : World → Form → Prop)
    (Produces : Entity → World → Form → Prop)
    (g : Entity) (φ₀ φ₁ : Form) : Prop where
  /-- The produced form is satisfiable — the relation is not producing nonsense. -/
  φ₀_satisfiable : ∃ w : World, Satisfies w φ₀
  /-- The unproduced form is satisfiable, so F10's antecedent really holds for it. -/
  φ₁_satisfiable : ∃ w : World, Satisfies w φ₁
  /-- And it is a different form, so (2) is not being trivially satisfied already. -/
  distinct : φ₀ ≠ φ₁
  /-- **C465's shape holds here.** -/
  c465_holds : ModelProducesSomething Entity World Form Produces g
  /-- **F10's shape fails here.** -/
  f10_fails : ¬ ModelProducesEverySatisfiable Entity World Form Satisfies Produces g

/-- **C483 — C465's shape and F10's shape are independent: the ground can produce something
    without producing every satisfiable form.**

    The model, exhibited. `Form := Bool` with `φ₀ := false` and `φ₁ := true`; `World := Unit`;
    `Entity := Unit` with the ground at `()`, so the `g` argument is degenerate and cannot carry
    any of the weight. `Satisfies` is the constant-true relation, so **every** form is satisfiable
    and the antecedent of (2) holds for `true` in particular. `Produces` is
    `φ = false`: total, well-defined, and it produces exactly one form.

    Read against C465 (`ground_love_produces`, `∃ w φ, Produces g w φ` under a love-hypothesis):
    the love-hypothesis, even if Γ could exhibit it, would buy the ground *one* form — because the
    shape of C465's conclusion is an existential, and no amount of satisfying its antecedent turns
    an existential into a universally quantified per-form relation. Read against F10: the
    derivation (2) is not coming from (1) plus C465, and any bridge that would produce it must
    constrain `Produces` in a way nothing in the corpus now does.

    **What this does NOT do.** It does not refute F10. `ModelProducesEverySatisfiable` is a *shape*
    over a free signature; the countermodel shows the two shapes are independent, not that F10 is
    false in Γ. F10 stays `BLOCKED`, and the corpus's own `means_does_not_imply_means_selection`
    (`HostileSemantics.lean:1861`) remains the governing precedent that omni-scope does not entail
    selection power. This row is a `PROVEN` non-entailment result *about the shape*.

    Footprint: `{}`. -/
theorem producing_something_does_not_produce_every_satisfiable_form :
    ∃ (Entity World Form : Type)
      (Satisfies : World → Form → Prop)
      (Produces : Entity → World → Form → Prop)
      (g : Entity) (φ₀ φ₁ : Form),
      ProducesOneFormOnly Entity World Form Satisfies Produces g φ₀ φ₁ := by
  refine ⟨Unit, Unit, Bool, fun _ _ => True, fun _ _ φ => φ = false, (), false, true, ?_⟩
  refine ⟨⟨(), trivial⟩, ⟨(), trivial⟩, by decide, ⟨(), false, rfl⟩, ?_⟩
  rintro h
  obtain ⟨v, hv⟩ := h true ⟨(), trivial⟩
  exact Bool.noConfusion hv

#print axioms producing_something_does_not_produce_every_satisfiable_form

end Logos.ProductionCountermodel
