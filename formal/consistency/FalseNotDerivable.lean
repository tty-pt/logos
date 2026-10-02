/-
# FalseNotDerivable — the S4 negative-compilation consistency guard

**This file MUST FAIL TO COMPILE. That is the pass condition.**

It is not part of the `Logos` library (`formal/lakefile.toml` roots `lean_lib Logos` at
`formal/Logos/`), so `lake build` never sees it. It is compiled on purpose, alone, by
`scripts/check_consistency.py`, which requires a *type* error and rejects the three ways a
negative compile can pass for the wrong reason: a timeout, an out-of-memory kill, or a
depth-limit crash.

## The defect it pins

Plan S4 originally stated `TrinitarianPersonalBridge` with three conjuncts

```lean
EntityOf a = divineReality ∧ EntityOf b = divineReality ∧ EntityOf c = divineReality
```

Since `divineReality := Entity.ofGround` is a `def` (`DivineAgape.lean:70`) and the corpus proves
`ofGround_ne_ofSubject (s) : EntityOf s ≠ Entity.ofGround` (`FoundationalUnicity.lean:134`), the
axiom was **refuted by a theorem of the same theory**: the whole kernel derived `False`. No
existing gate could see it. `audit_footprints.py` forbids only `sorryAx`, and `#print axioms`
reports the footprint of a declaration without ever asking whether the theory is consistent — an
inconsistent theory prints the *same* "0 substantive axioms" rows as a sound one, which is why the
defect was invisible in every badge, every `README.md` price, and every ledger figure.

## What makes the guard bite

The term below closes `False` from the two facts, using the exact `obtain` pattern of the
defective 16-conjunct axiom. So:

- **the defect is gone (now):** the axiom has 13 conjuncts, the pattern does not match, and
  elaboration fails — the intended result.
- **the defect returns verbatim:** the pattern matches, `hEqA : EntityOf a = divineReality`
  unfolds to `EntityOf a = Entity.ofGround`, `ofGround_ne_ofSubject` closes `False`, the file
  compiles, and `check_consistency.py` reports a *clean* compile as the failure it is.

This probe is deliberately pinned to one exact shape. A re-introduced identity conjunct at a
different position, or written `Entity.ofGround = EntityOf a` instead of the reverse, would defeat
this pattern and is caught instead by the syntactic scan in `scripts/check_consistency.py`. The two
gates are complementary: the negative compile is precise and position-blind, the scan is
position-exact and shape-blind. Neither alone is sufficient.
-/

import Logos.TrinitarianSubjectBridge
import Logos.FoundationalUnicity

open Logos.Entity (Entity EntityOf)
open Logos.Agency (Subject)
open Logos.FoundationalUnicity (ofGround_ne_ofSubject)
open Logos.TrinitarianSubjectBridge (TrinitarianPersonalBridge)

namespace Logos.Consistency.FalseNotDerivable

/-- If `TrinitarianPersonalBridge` again asserts that one of the three divine persons *is* the
    ground, then this term closes `False` and the file compiles. **A compiling file is a guard
    failure, not a success.** -/
theorem the_S4_identity_conjunct_would_close_False : False := by
  obtain ⟨a, b, c, _, _, _, hEqA, _, _, _, _, _, _, _, _, _, _⟩ := TrinitarianPersonalBridge
  exact ofGround_ne_ofSubject a hEqA

end Logos.Consistency.FalseNotDerivable