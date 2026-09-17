/-
# Logos.Initiation — the act is the initiation of movement, not its transfer
(base.txt §1; THOUGHTS.md §5)

A transfer is deterministic propagation (effect as a function of prior
state). An initiation begins movement and is not so determined; its formal
mark is `Branches`.

Under hostile semantics, `initiation ≠ transfer` is a pure-logic kernel
theorem (`branches_not_transfer`). Hardcoded constructor evaluations
(`origin_branches`, `posited_not_branch`) are excised.
-/

import Logos.Core

namespace Logos.Initiation

/--A relation is a transfer when the outcome is determined by the source — i.e. it is the graph of a function. -/
def IsTransfer {α β : Type} (R : α → β → Prop) : Prop :=
  ∃ f : α → β, ∀ a b, R a b ↔ b = f a

/--A relation branches when the same source admits two genuinely distinct outcomes. -/
def Branches {α β : Type} (R : α → β → Prop) : Prop :=
  ∃ a b₁ b₂, R a b₁ ∧ R a b₂ ∧ b₁ ≠ b₂

/--Initiation is not transfer: a relation with genuine alternatives is not the graph of any function. -/
theorem branches_not_transfer {α β : Type} {R : α → β → Prop} (h : Branches R) :
    ¬ IsTransfer R := by
  rintro ⟨f, hf⟩
  obtain ⟨a, b₁, b₂, r₁, r₂, hne⟩ := h
  have h₁ : b₁ = f a := (hf a b₁).mp r₁
  have h₂ : b₂ = f a := (hf a b₂).mp r₂
  exact hne (h₁.trans h₂.symm)

end Logos.Initiation

-- Axiom footprint audit
#print axioms Logos.Initiation.branches_not_transfer
