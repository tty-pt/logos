/-
# Spike_Initiation.lean — the act is the initiation of movement, not its transfer

User's correction (decisions locked, 2026-09-17):
  1. A subject is *one who acts*, not the act itself — the subject is the
     act's ORIGIN, never a component of it.
  2. An act is the INITIATION of movement, not its TRANSFER. A transfer is
     movement determined by its source (a function `f : X → Y`); an
     initiation begins movement and is not so determined. Its formal mark is
     `Branches`: the same source, two genuinely distinct outcomes.

This spike lives OUTSIDE the build barrel (`Logos.lean` does not import it).
It changes no resident module and adds no barrel axiom. It is compiled with

    cd formal && lake env lean Spikes/Spike_Initiation.lean

Project metrics (mandatory, measured):
  - `sorryAx : 0`.
  - `branches_not_transfer` footprint `{}` (pure logic).
  - `originates_not_transfer`, `noInitiation_selfRefutes` footprint
    `{Initiates, Subject}` (vocabulary only).
  - The state space is an ABSTRACT sort `State`, deliberately NOT
    `Semantics.World`: the act begins movement; it is not a valuation-state
    (a state is a transfer-object — that is exactly the objection).

Honest scope: this does NOT derive the subject. By the soundness obstruction
(THOUGHTS.md §3, FORCED_SUBJECT.md §1) no static vocabulary admits
`Originates`. What this spike establishes is the *kind*: the corrected
definition of the act, and `initiation ≠ transfer` as a kernel theorem.
`Cogito` is RELABELED (documentation), not removed: `Cogito_Init` below is
its restated form; the barrel is untouched in this pass.
-/

import Logos.Core
import Logos.Agency

namespace Logos.SpikeInitiation

open Logos.Agency (Subject)

/--Abstract state space of the initiation layer.

 The act begins movement; it is therefore indexed by states of a generic
 sort, not by `Semantics.World`. A world is a valuation — a state, i.e. a
 transfer-object — which is exactly what the act must not be reduced to. -/
axiom State : Type

/--A relation is a transfer when the outcome is determined by the source — i.e. when it is the graph of a function.

 A transfer is deterministic propagation: effect as a function of prior
    state. `IsTransfer R` says some `f` reproduces `R` exactly. This is the
    precise formal content of "transfer of movement". -/
def IsTransfer {α β : Type} (R : α → β → Prop) : Prop :=
  ∃ f : α → β, ∀ a b, R a b ↔ b = f a

/--A relation branches when the same source admits two genuinely distinct outcomes.

 Genuine alternatives at a source: two outcomes, distinct, both possible.
    This is the formal mark of initiation — the negation of transfer. -/
def Branches {α β : Type} (R : α → β → Prop) : Prop :=
  ∃ a b₁ b₂, R a b₁ ∧ R a b₂ ∧ b₁ ≠ b₂

/--Initiation is not transfer: a relation with genuine alternatives is not the graph of any function.

 The kernel content of "the act is the initiation of movement, not its
    transfer". Pure logic — footprint `{}`. -/
theorem branches_not_transfer {α β : Type} {R : α → β → Prop} (h : Branches R) :
    ¬ IsTransfer R := by
  rintro ⟨f, hf⟩
  obtain ⟨a, b₁, b₂, r₁, r₂, hne⟩ := h
  have h₁ : b₁ = f a := (hf a b₁).mp r₁
  have h₂ : b₂ = f a := (hf a b₂).mp r₂
  exact hne (h₁.trans h₂.symm)

/--The subject initiates a movement from `w` to `w'` positing content `p`.

 VOCABULARY (like `Means`): the generic act relation. The subject occurs as
    the ORIGIN INDEX of the transition, not as a component of a state. -/
axiom Initiates : Subject → State → State → Prop → Prop

/--The subject's movement, content erased: `s` can move `w → w'`. -/
def Moves (s : Subject) (w w' : State) : Prop := ∃ p : Prop, Initiates s w w' p

/--The subject originates a movement: it is the source of some initiation.

 Origin is untransferred spontaneity: `s` begins a movement. This is weaker
    than branching (one act, not yet genuine alternatives) — F1b freedom is
    not smuggled in. -/
def Originates (s : Subject) : Prop := ∃ w w' p, Initiates s w w' p

/--A subject whose movement branches does not transfer movement: its outcome is not a function of its prior state.

 Vocabulary-only footprint `{Initiates, Subject}`. This is the formal reason
    a purely derived subject could only ever be an effect: derivation is
    transfer. -/
theorem originates_not_transfer {s : Subject} (h : Branches (Moves s)) :
    ¬ IsTransfer (Moves s) :=
  branches_not_transfer h

/--THE FORCED FOUNDATION, restated: the present subject originates an act.

 Relabel of the resident `Agency.Cogito` (`∃ s p, A s p`): the present act is
    an INITIATION of a subject, and the subject is its origin. Kept as a
    posit — the soundness obstruction forbids derivation; the Walls
    (FORCED_SUBJECT.md §1) forbid a carrier. Same kind as `Classical.choice`:
    the first given, without which no proof and no denial exist. -/
axiom Cogito_Init : ∃ s : Subject, Originates s

/--Denying that any subject originates an act refutes itself: the denial is itself such an act.

 Mirror of `noCogito_selfRefutes`, now at the initiation layer. Footprint
    `{Cogito_Init, Initiates, Subject}`. -/
theorem noInitiation_selfRefutes : (¬ ∃ s : Subject, Originates s) → False :=
  fun h => h Cogito_Init

end Logos.SpikeInitiation

-- Axiom footprint audit
#print axioms Logos.SpikeInitiation.branches_not_transfer
#print axioms Logos.SpikeInitiation.originates_not_transfer
#print axioms Logos.SpikeInitiation.noInitiation_selfRefutes
