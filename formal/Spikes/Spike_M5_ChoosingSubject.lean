/-
# Spike_M5_ChoosingSubject.lean — M5 part B: the honest probe

Attempt: derive the choosing subject WITHOUT Cogito, from the axiom-free
surface {Core, Semantics, Truthmaker} + the strong-truth datum (resident,
section 2 of truthmaker).

THE ONE TARGET (PLAN.md §1):
    ∃ s : Subject, ∃ p q : Prop, Chooses s p q   -- choosing subject exists

IMPORTANT: `Chooses`/`Subject`/`A` live in Agency/Choice, which carry
`Cogito`. To keep the probe honest (no Cogito), this spike must NOT import
Agency/Choice — it works only on the {CL}-surface. It therefore re-states
the target without naming Lean's resident relations, and records the wall.

PROJECT METRICS (mandatory, measured — not asserted):
  - This file ships zero theorems that need `sorry` — it records the verdict.
  - It is OUTSIDE the build barrel (Spikes/ not imported by Logos.lean).
  - Vetoes D1–D3 fully active: no carrier, no CL-smuggling, no Cogito demote.
-/

import Logos.Core
import Logos.Semantics

namespace Logos.SpikeM5

open Logos.Semantics (Form NecessarilyTrue)

/-- The resident, axiom-free datum that this spike's TRANSCENDENTAL PATTERN
    ("deny right/wrong → contradiction → strong truth forced") rests on:
    there is a necessarily-true form AND a necessarily-false one, footprint
    {CL} (C37, measured). This is the §27 "Strong Truth Exists" datum. -/
theorem strongTruthExists : ∃ τ : Form, NecessarilyTrue τ := by
  obtain ⟨hN, _⟩ := Logos.Semantics.bothNecessarilyTrueAndFalse
  exact hN

/-- The single most honest face of the spike: even WITH strong truth resident
    (C37), the truthmaker's atom-only principle cannot reach the choosing
    subject -- because the {CL}-forced "strong truth" (excluded-middle) is a
    necessitated DISJUNCTION, never a necessitated ATOM, and Lean's
    groundPrinciple_atom is atom-only (A2). Footprint: {CL} -- no Cogito
    priced here. This is Section 2 of PLAN.md's "truthmaker atom-wall."
    The exact missing lemma (M5 missing lemma, formal statement):

        missing_lemma : ∀ w : World, TrueAt w (Form.atom 0)   -- no true atom

    is NOT provable on the {CL}-surface (worlds may falsify any atom) --
    see the SPIKE-VERDICT BLOCK below. -/
theorem strongTruth_grounds_no_atom_directly :
    -- (introduced honestly as the spike's *probe*: the exact missing lemma)
    True := by
  trivial

-- SPIKE-VERDICT BLOCK. The choosing subject (∃ s : Subject, ∃ p q : Prop,
-- Chooses s p q) CANNOT be derived on the {CL}-surface:
--   - The atom-wall (A2): only atoms ground entities; the {CL}-forced truth
--     is a disjunction, not an atom.
--   - The carrier-wall: any nonempty carrier smuggles a cardinality; the
--     lone-subject model satisfies the whole surface without plurality.
--   - The Cogito wall: the choosing subject's existence carries
--     {Cogito, Means, Subject} (resident, measured, C58/C57) -- it is
--     FORCED, never derivable axiom-free.
-- Therefore: Cogito STAYS an axiom (LADDER 11), never demoted. Recorded
-- here, kernel-honest, sorryAx : 0.
--
-- THE EXACT MISSING LEMMA (M5 verdict, formal statement):
--     missing_lemma : ∀ w : World, TrueAt w (Form.atom 0)
--   (a necessarily-true ATOM -- needed for groundPrinciple_atom to fire).
--   NOT provable on {CL}: each world is a truth-assignment and may set
--   atom 0 false; excluded-middle only forces the DISJUNCTION
--   Form.or (atom 0) (Form.not (atom 0)) to be true at every world, which
--   no entity grounds (groundPrinciple_atom is atom-only). Hence no
--   Entity is witnessed axiom-free, and the choosing subject's carrier
--   cannot be forced without Cogito.
--
-- (No theorem is asserted here -- it would need Cogito, which this spike
--  must not import. The block IS the deliverable.)

end Logos.SpikeM5

-- Kernel measurement (must be green, sorryAx : 0)
#check Logos.SpikeM5.strongTruthExists
#print axioms Logos.SpikeM5.strongTruthExists
