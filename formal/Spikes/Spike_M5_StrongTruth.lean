/-
# Spike_M5_StrongTruth.lean — M5 part A: Strong Truth Exists (axiom-free)

LADDER 11 → 10 probe (PLAN.md §1–§3). Ladder currently 11 (C29, Cogito
axiom resident/FORCED, footprint {Cogito, Means, Subject}).

## What this file establishes, measured

The transcendental datum of en.md §27 ("Strong Truth Exists") — "there is
right and there is wrong", "há certo E há errado" — is *already resident
axiom-free* in the Corpus (C37: `Semantics.bothNecessarilyTrueAndFalse`).
This spike re-provisions it as a named corollary:

```lean
strongTruthExists : ∃ τ : Form, NecessarilyTrue τ
```

**Footprint: {CL}** (excluded-middle, FORCED; no Cogito, no Means, no
Subject-priced witness). Kernel-measured, sorryAx: 0.

## What this file does NOT do (Vetoes active: D1/D2/D3)
- Does NOT import Agency (Cogito) → the choosing-subject existence is NOT
  derived here.
- Does NOT import Truthmaker (which imports Agency).
- Does NOT use Classical to *witness* a subject (Carrier-smuggling Veto).
-/

import Logos.Core
import Logos.Semantics

namespace Logos.SpikeM5

/-- §27 "Strong Truth Exists": there exists a form that is necessarily true
    (and one necessarily false), axiom-free — the performative "há certo E
    há errado" (poem.txt), resident as the excluded-middle datum C37.
    Footprint: {CL} only. 2026-09-16. -/
theorem strongTruthExists :
    ∃ τ : Logos.Semantics.Form, Logos.Semantics.NecessarilyTrue τ := by
  obtain ⟨hN, _⟩ := Logos.Semantics.bothNecessarilyTrueAndFalse
  exact hN

end Logos.SpikeM5

#print axioms Logos.SpikeM5.strongTruthExists
