/-
# Logos.Initiation — the act is the initiation of movement, not its transfer
(base.txt §1; THOUGHTS.md §5)

A transfer is deterministic propagation (effect as a function of prior
state). An initiation begins movement and is not so determined; its formal
mark is `Branches`. The subject is the ORIGIN of the initiation.

The subject itself is exhibited: the definitional underlier (`Unit ⊕ Prop`)
supplies the witness outright, so the act-datum is the theorem
`Agency.Cogito`; `Cogito_Init` below is the restated (relabeled) form.
-/

import Logos.Core
import Logos.Agency
import Logos.Person

namespace Logos.Initiation

open Logos.Agency (Subject State Initiates Means A Cogito)
open Logos.Person (Person)

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

/--The subject's movement, content erased: `s` can move `w → w'`. -/
def Moves (s : Subject) (w w' : State) : Prop := ∃ p : Prop, Initiates s w w' p

/--The subject originates a movement: it is the source of some initiation. -/
def Originates (s : Subject) : Prop := ∃ w w' : State, ∃ p : Prop, Initiates s w w' p

/--A subject whose movement branches does not transfer movement: its outcome is not a function of its prior state. -/
theorem originates_not_transfer {s : Subject} (h : Branches (Moves s)) :
    ¬ IsTransfer (Moves s) :=
  branches_not_transfer h

/--A person is exactly a subject that originates an act. -/
theorem person_iff_originates (s : Subject) : Person s ↔ Originates s := by
  constructor
  · intro h
    obtain ⟨p, hm⟩ := h.2.2
    obtain ⟨w, w', hi⟩ := hm
    exact ⟨w, w', p, hi⟩
  · intro h
    obtain ⟨w, w', p, hi⟩ := h
    exact ⟨trivial, trivial, p, ⟨w, w', hi⟩⟩

/--The exhibited act, restated: the present subject originates an act. -/
theorem Cogito_Init : ∃ s : Subject, Originates s := by
  obtain ⟨s, p, ha⟩ := Cogito
  unfold A Means at ha
  obtain ⟨w, w', hi⟩ := ha
  exact ⟨s, w, w', p, hi⟩

/--Denying that any subject originates an act refutes itself: the origin is exhibited, no axiom cited. -/
theorem noInitiation_selfRefutes : (¬ ∃ s : Subject, Originates s) → False :=
  fun h => h Cogito_Init

/-- Posited contents do not branch: a proposition posited by definition moves deterministically. -/
theorem posited_not_branch (q : Prop) : ¬ Branches (Moves (Sum.inr q)) := by
  rintro ⟨a, b₁, b₂, ⟨p₁, hp₁, heq₁⟩, ⟨p₂, hp₂, heq₂⟩, hne⟩
  subst heq₁ heq₂ hp₁ hp₂
  exact hne rfl

/-- Posited contents are deterministic transfers: their movement is a constant function. -/
theorem posited_is_transfer (q : Prop) : IsTransfer (Moves (Sum.inr q)) := by
  refine ⟨fun _ => q, ?_⟩
  intro a b
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp.symm
  · intro hb
    exact ⟨q, rfl, hb⟩

/-- The silent origin genuinely branches: its initiation is not a transfer. -/
theorem origin_branches : Branches (Moves (Sum.inl ())) := by
  refine ⟨True, True, False, ?_, ?_, ?_⟩
  · exact ⟨True, rfl⟩
  · exact ⟨False, rfl⟩
  · intro h
    exact False.elim (cast h True.intro)

/-- The silent origin does not transfer movement: genuine untransferred spontaneity. -/
theorem origin_not_transfer : ¬ IsTransfer (Moves (Sum.inl ())) :=
  branches_not_transfer origin_branches

/-- Genuine personal agency: an initiating person is a person whose movement
    is an initiation, not a transfer — marked by branching alternatives. -/
def InitiatingPerson (s : Subject) : Prop :=
  Person s ∧ Branches (Moves s)

/-- The silent origin is a genuine initiating person. -/
theorem origin_is_initiating_person : InitiatingPerson (Sum.inl ()) := by
  constructor
  · exact ⟨trivial, trivial, ⟨True, ⟨True, ⟨True, rfl⟩⟩⟩⟩
  · exact origin_branches

/-- Posited contents are NOT initiating persons: they are deterministic transfers. -/
theorem posited_not_initiating_person (q : Prop) : ¬ InitiatingPerson (Sum.inr q) := by
  intro ⟨_, hb⟩
  exact posited_not_branch q hb

/-- Every propositional content fails to be an initiating person:
    pan-personalism is formally refuted at the initiation layer. -/
theorem no_content_is_initiating_person :
    ∀ q : Prop, ¬ InitiatingPerson (Sum.inr q) :=
  posited_not_initiating_person

end Logos.Initiation

-- Axiom footprint audit
#print axioms Logos.Initiation.branches_not_transfer
#print axioms Logos.Initiation.originates_not_transfer
#print axioms Logos.Initiation.person_iff_originates
#print axioms Logos.Initiation.Cogito_Init
#print axioms Logos.Initiation.noInitiation_selfRefutes
#print axioms Logos.Initiation.posited_not_branch
#print axioms Logos.Initiation.posited_is_transfer
#print axioms Logos.Initiation.origin_branches
#print axioms Logos.Initiation.origin_not_transfer
#print axioms Logos.Initiation.origin_is_initiating_person
#print axioms Logos.Initiation.posited_not_initiating_person
#print axioms Logos.Initiation.no_content_is_initiating_person
