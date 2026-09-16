/-
# Logos.Necessity — propositional modal operator (DESIGN.md D12, hardened C1)

The prose (§15, §25, §27, poem.txt) uses □ and ◇ at the level of ordinary
propositions. Two layers are now distinguished (C1, 2026-09-15):

1. `NecessityPH (P : World → Prop) : Prop := ∀ w : World, P w` — the *real*,
   semantics-grounded modal operator: a world-indexed proposition holds in
   every world. For this operator the S4 rules K, T, 4 are *theorems* (plain
   universal quantification), so nothing modal is axiomatized anymore.

2. `Necessity (p : Prop) : Prop := NecessityPH (fun _ => p)` — the *degenerate
   identity-model alias* (D12's declared consistency model, `Necessity p := p`):
   a world-invariant proposition's "necessity" is just its truth. Its K/T/4
   rules are also theorems. It is the *interface* the old API provided and the
   reason it exists is compatibility; the genuinely non-trivial modality lives
   at the world level (freedom F1, and the eternal love of T14, must be built
   on `NecessityPH`, never on the degenerate alias).

`Dia p := ¬ Necessity (¬ p)` (possibility). A *general* rule
`p → Necessity p` is deliberately NOT a named rule beyond T: for the alias it
divides trivially (the alias IS truth), and the contingency of the world
(poem P9, "este mundo é necessário? Não") is expressed at the world level by
`Semantics` (contingent forms), not by the degenerate prop-level box.

Necessity of the core result (poem P2):
  * `necDistinction : Necessity (¬ N_T ∧ ¬ N_F)` is now a *theorem* — under the
    alias it is `rightWrongDistinction` itself (core, PROVEN `{}` under E0).
    Its genuine world-level content is `Semantics.bothNecessarilyTrueAndFalse`
    (C37, PROVEN): in every world there is necessarily-true content and
    necessarily-false content. The former SEM axiom `necDistinction` and the
    FAITH-1 entry in GAPMAP.md are dissolved.
-/

import Logos.Core
import Logos.Semantics

namespace Logos.Necessity

open Logos.Core (N_T N_F rightWrongDistinction)
open Logos.Semantics (World)

/-- A concrete world (any inhabitant will do for the degenerate alias): the
    always-true valuation. Used to witness T without the `actualWorld` axiom. -/
def someWorld : World := fun _ => Logos.Semantics.TV.t

/-- Prop-level necessity, degenerate alias (C1): a world-invariant proposition
    is "necessary" iff it holds — the identity-model reading recorded in D12.
    The non-trivial modality is `NecessityPH`; this is the compatibility
    interface. -/
def Necessity (p : Prop) : Prop := ∀ _w : World, p

/-- Normality (K): necessity distributes over material implication. -/
theorem necK : ∀ {p q : Prop}, Necessity (p → q) → Necessity p → Necessity q := by
  intro p q hpq hp w
  exact (hpq w) (hp w)

/-- Truth (T): what is necessary is the case (instantiate at `someWorld`). -/
theorem necT : ∀ {p : Prop}, Necessity p → p := by
  intro p hp
  exact hp someWorld

/-- Positive introspection (4): what is necessary is necessarily necessary. -/
theorem nec4 : ∀ {p : Prop}, Necessity p → Necessity (Necessity p) := by
  intro p hp _
  exact hp

/-- Possibility, `◇p := ¬□¬p`. -/
def Dia (p : Prop) : Prop := ¬ Necessity (¬ p)

/-- `Dia` unfolds definitionally. -/
theorem dia_def {p : Prop} : Dia p ↔ ¬ Necessity (¬ p) := Iff.rfl

/-- Necessity yields its content (instance of T). -/
theorem nec_apply {p : Prop} (hp : Necessity p) : p := necT hp

/-- Modus ponens under necessity (K instantiated). -/
theorem necMP {p q : Prop} (hpq : Necessity (p → q)) (hp : Necessity p) :
    Necessity q := necK hpq hp

-- ---------------------------------------------------------------------------
-- The real, semantics-grounded operator (C1)
-- ---------------------------------------------------------------------------

/-- World-indexed proposition. -/
abbrev WProp : Type := World → Prop

/--World-level necessity: a claim about worlds holds if it holds in every world.

 Necessity at the world level (C1): a world-indexed proposition holds in
    every world. This is the modality the object-language semantics actually
    supports (it is `Semantics.NecessarilyTrue` lifted to arbitrary
    world-indexed propositions). -/
def NecessityPH (P : WProp) : Prop := ∀ w : World, P w

/-- K for `NecessityPH`: necessity distributes over implication. -/
theorem necKPH {P Q : WProp} :
    NecessityPH (fun w => P w → Q w) → NecessityPH P → NecessityPH Q :=
  fun hPQ hP w => (hPQ w) (hP w)

/-- T for `NecessityPH`: what is necessary at every world holds at some world. -/
theorem necTPH {P : WProp} : NecessityPH P → P someWorld := by
  intro h
  exact h someWorld

/-- 4 for `NecessityPH`: world-universality reflects into itself (the inner
    necessity is lifted through the world binder). -/
theorem nec4PH {P : WProp} : NecessityPH P → NecessityPH (fun _ => NecessityPH P) := by
  intro hP w
  exact hP

/--The distinction between right and wrong is necessary: it is false that nothing is true, and false that everything is true.

 Necessity of the distinction (poem P2), as a theorem (C1): under the
    identity-model alias this is exactly the proven Prose-result
    `¬N_T ∧ ¬N_F`. Its intended reading is the world-level content
    (see module header). -/
theorem necDistinction : Necessity (¬ N_T ∧ ¬ N_F) :=
  fun _w => rightWrongDistinction

/-- `necDistinction`'s truth-content is proven (the alias is truth). -/
theorem necDistinction_content : ¬ N_T ∧ ¬ N_F := nec_apply necDistinction

end Logos.Necessity

-- Axiom footprint audit
#print axioms Logos.Necessity.necDistinction_content
#print axioms Logos.Necessity.nec_apply
#print axioms Logos.Necessity.necKPH
#print axioms Logos.Necessity.nec4PH
