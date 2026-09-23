/-
# Logos.GroundPerson — Level 2e: personal features of rational acts
-/

import Logos.Core
import Logos.Agency
import Logos.Person

namespace Logos.GroundPerson

open Logos.Agency (Subject A Means)

/-- A feature present in the present rational act on its personal side:
    it is the content *meant* by the acting subject. -/
def IsPresentPersonalFeature (f : Prop) : Prop :=
  ∃ s : Subject, ∃ p : Prop, A s p ∧ Means s p ∧ f = p

end Logos.GroundPerson
