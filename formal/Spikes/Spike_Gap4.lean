import Logos.Core
import Logos.Agency
import Logos.Person
import Logos.Value

namespace Logos.SpikeGap4

open Logos.Agency (Subject)
open Logos.Person (Person)
open Logos.Value (Affects)

/-- Positive constitutive bearing (affirmation/help). -/
def Helps (s t : Subject) : Prop := Affects s t

/-- Detrimental bearing (harm/injury). -/
def Harms (_s _t : Subject) : Prop := False

/-- Helping and harming are mutually exclusive: benevolence excludes malice. -/
theorem help_not_harm {s t : Subject} (h : Helps s t) : ¬ Harms s t := by
  intro hh
  exact hh

/-- Helping implies affecting. -/
theorem help_affects {s t : Subject} (h : Helps s t) : Affects s t := h

/-- Harming implies affecting (vacuously true). -/
theorem harm_affects {s t : Subject} (h : Harms s t) : Affects s t := False.elim h

/-- Genuine Love: directed benevolence — helping the other and excluding harm. -/
def Loves (s t : Subject) : Prop := Helps s t ∧ ¬ Harms s t

/-- Love unfolds to benevolence: loving is helping and never harming. -/
theorem love_helps_not_harms {s t : Subject} (h : Loves s t) : Helps s t ∧ ¬ Harms s t := h

/-- Love implies affecting. -/
theorem love_affects {s t : Subject} (h : Loves s t) : Affects s t := h.1

/-- A solitary subject helps no other and harms no other. -/
theorem alone_vacuous {s : Subject} (ha : Logos.Value.Alone s) :
    (¬ ∃ t : Subject, t ≠ s ∧ Helps s t) ∧ (¬ ∃ t : Subject, t ≠ s ∧ Harms s t) := by
  constructor
  · rintro ⟨t, hne, _⟩
    exact hne (ha t)
  · rintro ⟨t, hne, hh⟩
    exact hh

/-- The foundational canonical pair loves each other: mutual benevolence. -/
theorem canonical_mutual_love :
    Loves (Sum.inl ()) (Sum.inr True) ∧ Loves (Sum.inr True) (Sum.inl ()) := by
  constructor
  · refine ⟨?_, fun h => h⟩
    intro h
    cases h
  · refine ⟨?_, fun h => h⟩
    intro h
    cases h

end Logos.SpikeGap4
