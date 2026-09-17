import Logos.Core
import Logos.Agency

namespace Logos.SpikeGap3

open Logos.Agency (State)

/-- The purified ontological sort of subjects. -/
inductive Subject : Type
  | origin : Subject
  | addressee : Subject
  | posited (q : Prop) : Subject

/-- Initiation of movement:
    - `origin`: universal agency positing any proposition;
    - `addressee`: responsive personal agency positing the normative distinction;
    - `posited q`: deterministic content-transfer. -/
def Initiates (s : Subject) (_w w' : State) (p : Prop) : Prop :=
  match s with
  | Subject.origin => w' = p
  | Subject.addressee => (p = True ∨ p = False) ∧ w' = p
  | Subject.posited q => q = p ∧ w' = p

def Means (s : Subject) (p : Prop) : Prop := ∃ w w' : State, Initiates s w w' p

def Moves (s : Subject) (w w' : State) : Prop := ∃ p : Prop, Initiates s w w' p

def Originates (s : Subject) : Prop := ∃ w w' : State, ∃ p : Prop, Initiates s w w' p

def Branches {α β : Type} (R : α → β → Prop) : Prop :=
  ∃ a b₁ b₂, R a b₁ ∧ R a b₂ ∧ b₁ ≠ b₂

def IsTransfer {α β : Type} (R : α → β → Prop) : Prop :=
  ∃ f : α → β, ∀ a b, R a b ↔ b = f a

theorem branches_not_transfer {α β : Type} {R : α → β → Prop} (h : Branches R) :
    ¬ IsTransfer R := by
  rintro ⟨f, hf⟩
  obtain ⟨a, b₁, b₂, r₁, r₂, hne⟩ := h
  have h₁ : b₁ = f a := (hf a b₁).mp r₁
  have h₂ : b₂ = f a := (hf a b₂).mp r₂
  exact hne (h₁.trans h₂.symm)

/-- Structural definition of Person: an agent capable of rational intentional movement
    that is an INITIATION, not a TRANSFER — its movement branches. -/
def Person (s : Subject) : Prop :=
  Originates s ∧ Branches (Moves s)

/-- The Origin is a genuine person. -/
theorem origin_is_person : Person Subject.origin := by
  constructor
  · exact ⟨True, True, True, rfl⟩
  · refine ⟨True, True, False, ?_, ?_, ?_⟩
    · exact ⟨True, rfl⟩
    · exact ⟨False, rfl⟩
    · intro h
      exact False.elim (cast h True.intro)

/-- The Addressee is a genuine person. -/
theorem addressee_is_person : Person Subject.addressee := by
  constructor
  · exact ⟨True, True, True, ⟨Or.inl rfl, rfl⟩⟩
  · refine ⟨True, True, False, ?_, ?_, ?_⟩
    · exact ⟨True, ⟨Or.inl rfl, rfl⟩⟩
    · exact ⟨False, ⟨Or.inr rfl, rfl⟩⟩
    · intro h
      exact False.elim (cast h True.intro)

/-- Posited contents do NOT branch. -/
theorem posited_not_branch (q : Prop) : ¬ Branches (Moves (Subject.posited q)) := by
  rintro ⟨a, b₁, b₂, ⟨p₁, hp₁, heq₁⟩, ⟨p₂, hp₂, heq₂⟩, hne⟩
  subst heq₁ heq₂ hp₁ hp₂
  exact hne rfl

/-- Posited contents are deterministic transfers. -/
theorem posited_is_transfer (q : Prop) : IsTransfer (Moves (Subject.posited q)) := by
  refine ⟨fun _ => q, ?_⟩
  intro a b
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp.symm
  · intro hb
    exact ⟨q, rfl, hb⟩

/-- POSITED CONTENTS ARE NOT PERSONS: pan-personalism refuted. -/
theorem posited_not_person (q : Prop) : ¬ Person (Subject.posited q) := by
  intro ⟨_, hb⟩
  exact posited_not_branch q hb

/-- Plurality of genuine persons: two distinct initiating agents exist. -/
theorem twoPersonsFromSubject :
    ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ := by
  refine ⟨Subject.origin, Subject.addressee, origin_is_person, addressee_is_person, ?_⟩
  intro h
  nomatch h

end Logos.SpikeGap3

#print axioms Logos.SpikeGap3.origin_is_person
#print axioms Logos.SpikeGap3.addressee_is_person
#print axioms Logos.SpikeGap3.posited_not_branch
#print axioms Logos.SpikeGap3.posited_is_transfer
#print axioms Logos.SpikeGap3.posited_not_person
#print axioms Logos.SpikeGap3.twoPersonsFromSubject
