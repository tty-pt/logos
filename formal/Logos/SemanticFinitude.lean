/-
# Logos.SemanticFinitude — the F15 sentence, promoted from ◈ stipulation to declared axiom (2026-09-28)

F15 identified a lemma that the corpus had already paid as an anonymous premise,
nineteen times across five files (fourteen of them carrying the exact ∀-form), and
never registered: the per-subject meaning
bound `∀ s, ∃ p, ¬ Means s p` — no subject means every proposition, no creature is
semantically omnipotent. On 2026-09-27 this module *named* that bound
(`SemanticFinitude`), registered it as a ◈ stipulation in `Stipulations.lean`, and
provided ten priced corollaries, each keyed to the single named sentence.

## What changed on 2026-09-28, and why

The ◈ form was a reporting convenience, and it had a cost the author judged higher
than the cost it hid. Because the premise was a `def` of a `Prop` taken as an
*argument*, `#print axioms` could not see it: the ten corollaries reported exactly
the same footprint as the anonymous conditional theorems they mirrored, the declared
count of axioms did not move, and **no footprint tool in the repository could price
the batch at all**. The bound was simultaneously the most load-bearing premise in the
divine-attribute lane and the only major premise in the corpus that the kernel could
not see.

So the bound is now a **declared `Tag: VOCAB` axiom** (the 27th). The ten
corollaries lose their `hf` parameter and become unconditional theorems of Γ. The
price is now visible in every footprint, in `#print axioms`, in the axiom registry,
and in `formal/axiom_audit.json`.

## The tag is `VOCAB`, deliberately, and this is a considered decision

`SemanticFinitude` bounds one uninterpreted relation (`Means`) on one nullary sort
(`Subject`) and asserts **no connection between entities**, no modality, and no
metaphysics. That is precisely the project's stated criterion for a vocabulary
commitment, and the same status as `ofGround_existsAt`. It is therefore `VOCAB`
rather than `SEM`.

This is not a device to protect a badge. The generator's `footprint_parts` treats
only `SEM`/`META`/`TRANS` as substantive, so a `VOCAB` axiom yields `✅ PROVEN` while
`SEM` would yield `⚠️ AXIOMATIC` — and the ten corollaries keep the badge they had
under ◈. Re-tagging to `SEM` would have bought no additional honesty (the axiom is
declared, tagged, justified, listed and audited either way) and would have cost ten
visible badge regressions. If a future author judges the bound to be a genuine
semantic choice, the correct move is to re-tag it and *accept* the badge change.

## What this batch still is not

Not a derivation. `SemanticFinitude` is not provable in Γ and is correctly absent as
a theorem: the countermodel `semantic_omnipotence_is_consistent` in this module is a
model of its **negation**. The bound is falsifiable, not vacuous — which is exactly
why the unicity of C320 genuinely rests on it and must be priced rather than assumed.

**Existence is untouched.** The existence of a universal modal ground (C319) was and
remains `PROVEN` unconditionally. What rests on the bound is **unicity**, and every
divine attribute that was conditional on an anonymous copy of it.

**The `_stipulated` suffix on the ten corollaries is historical.** They are no longer
stipulations. The names are retained rather than renamed because they are referenced
from `formal/GAPMAP.md`, the prose corpus, and the generated chain list; renaming
would change a lot of text without changing a single fact. Read `_stipulated` as
"keyed to the named bound", which is still true.

**Census method, for the record — and two measures, because "how many times" has no
single answer here.** `scripts/census_semantic_finitude.py` counts the occurrences and
`--check` fails the build if this docstring drifts from the kernel.

- **`any` = 20.** Every top-level declaration across the five attribute modules whose
  *statement* mentions the bound, in the ∀-form (F15 itself, as a hypothesis) or in the
  per-subject ∃-form (`hDisc : ∃ p, ¬ Means s p`). Per file: `DivinePureActuality` 5,
  `FoundationalUnicity` 6, `CanonicalAseity` 4, `DivineSimplicity` 4, `AsieticChoice` 1.
- **`forall` = 15.** Only the declarations carrying the exact F15 ∀-form — the ones
  that pay the price Γ actually declares. Per file: 3, 5, 2, 4, 1.

**Delta 2026-09-28 (batch SOLE-BEARER-AND-DERIVABILITY).** The figures moved 19 → 20 and
14 → 15, both in `DivineSimplicity` (3 → 4). The new payer is
`divine_simplicity_sole_bearer` (C440), whose `hFinite` premise is the bound. The module's
other new declaration, `divine_simplicity_is_unique_to_the_ground` (C439), does **not** pay:
unicity reads only the structure's `no_internal_components` field, so the *existence* half of
C440 pays the bound and the *unicity* half does not. That asymmetry is the point of the row —
and it is why the count of payers went up by one while the count of `{}`-class rows did not.

Proof bodies are excluded: an occurrence in a proof is a *use* of a price already
paid, not a new payment. The robust statement, which holds under either measure, is
that Γ pays this price by **five distinct attribute arguments** (canonical aseity,
divine simplicity, divine pure actuality, asietic choice, foundational unicity) in
**all five modules**.

**On the earlier figures.** The prose corpus carried "20", then "19 occurrences
(17 premissas + 2 campos de estrutura)", then "17", then (after this batch) 20. Of those,
the bare "17" belongs to no consistent measure at all, and the per-file breakdown attached
to the "19" was wrong twice over (`FoundationalUnicity` is 6, not 7; `DivinePureActuality`
is 5, not 4). The `any` total is now **20**, the `forall` total **15** — see the delta note
above. The lesson is not the number: it is that a single integer quoted without a stated
measure, a method, and a per-file breakdown is not a fact, and two of the four historical
figures were wrong in exactly that way. What was actually wrong is the presentation, not the
conclusion: a single integer was quoted as if the measure were the only possible one,
with no method stated and a wrong per-file breakdown behind it. Hence two measures and
a checking script.

**Scanning note (learned the hard way, 2026-09-28).** No line in this module
docstring may begin, at column 0, with the token `axiom` followed by an identifier —
`gapmap_taxonomy.py` builds the axiom inventory through `build_deduction.load_decls`,
which does **not** strip comments, so such a line is read as a 28th axiom declaration
and shows up as `Tag: UNTAGGED`. `audit_stipulated_defs.py` *does* strip comments and is
therefore blind to it. Reword to "count of axioms" / "an axiom" instead. (An earlier
version of this note claimed `audit_stipulated_defs.py` made the hazard moot; it did
not, because a second scanner in the pipeline does not strip comments.)
-/

import Logos.Core
import Logos.Semantics
import Logos.Entity
import Logos.Agency
import Logos.RecoveredOntologicalGround
import Logos.ModalPossibilityFrontier
import Logos.FoundationalOmnipresence
import Logos.CanonicalAseity
import Logos.DivineSimplicity
import Logos.DivinePureActuality
import Logos.FoundationalUnicity
import Logos.AsieticChoice

namespace Logos.SemanticFinitude

open Logos.Semantics
open Logos.Entity
open Logos.Agency
open Logos.RecoveredOntologicalGround
open Logos.ModalPossibilityFrontier
open Logos.FoundationalOmnipresence
open Logos.CanonicalAseity
open Logos.DivineSimplicity
open Logos.DivinePureActuality
open Logos.FoundationalUnicity
open Logos.AsieticChoice

-- ============================================================================
-- Section 0: The named sentence
-- ============================================================================

/--Tag: VOCAB
    **Semantic finitude.** No subject means every proposition: no creature is
    semantically omnipotent.

    This is the sentence F15 named as the missing lemma, and the corpus already paid
    it seventeen times as an anonymous explicit premise before it was ever declared.
    It is a **vocabulary** commitment, not a semantic one: it bounds one
    uninterpreted relation (`Means`) on one nullary sort (`Subject`) and asserts no
    connection between entities, no modality, and no metaphysics — the same status as
    `ofGround_existsAt`.

    **The price, stated.** Rejecting it gives a semantically omnipotent carrier, i.e.
    a subject meaning every proposition; `semantic_omnipotence_is_consistent` below
    is that model, so the bound is falsifiable rather than vacuous. **The reward.**
    On it rest the unicity of the universal modal ground (C320) and every divine
    attribute in Γ's attribute lane — Divine Simplicity, Divine Pure Actuality,
    Canonical Aseity and its modal form, non-compositeness, zero grounding potency —
    which are otherwise unprovable, because nothing in Γ bounds a subject's
    propositional reach.

    **Provenance.** Declared 2026-09-28, promoted from a ◈ `def`-stipulation because a
    `def` premise is invisible to `#print axioms` and no footprint tool in the
    repository could price it.  Footprint: `{Means, Subject}`. -/
axiom SemanticFinitude : ∀ s : Subject, ∃ p : Prop, ¬ Means s p

-- ============================================================================
-- Section 1: The ten corollaries
--
-- Each is the corresponding pre-existing theorem with its anonymous premise
-- (`hNoTotal` / `hFinite`) discharged by the now-*declared* `SemanticFinitude`.
-- Since 2026-09-28 these carry no parameter: they are unconditional theorems of Γ,
-- and the declared axiom appears in their audited footprint.
--
-- The `_stipulated` suffix is historical — see the module docstring. The names are
-- kept because GAPMAP, the prose corpus and the generated chain list all cite them.
-- No existing theorem is edited and no existing name is shadowed: the originals
-- still take their anonymous hypothesis.
-- ============================================================================

/-- Exactly one universal modal ground exists — the unicity conjunct now rests on the
    *declared* finitude axiom rather than an anonymous premise.
    Footprint: `{Means, NecessarySubjectKind, SemanticFinitude, Subject}`. -/
theorem exactly_one_universal_modal_ground_stipulated :
    ∃ g : Entity, UniversalModalGround g ∧
      (∀ g' : Entity, UniversalModalGround g' → g' = g) :=
  exactly_one_universal_modal_ground SemanticFinitude

/-- The ground of reality is the sole universal grounding principle, on the declared
    finitude axiom.
    Footprint: `{Means, NecessarySubjectKind, SemanticFinitude, Subject}`. -/
theorem ofGround_sole_universal_grounding_stipulated :
    SoleUniversalGrounding Entity.ofGround :=
  ofGround_sole_universal_grounding SemanticFinitude

/-- Canonical Aseity of the ground, on the declared finitude axiom.
    Footprint: `{Means, SemanticFinitude, Subject}`. -/
theorem conditional_canonical_aseity_stipulated :
    CanonicalAseity Entity.ofGround :=
  conditional_canonical_aseity SemanticFinitude

/-- Modal Aseity of the ground with respect to `CanonicalExtDepAt`, on the declared
    finitude axiom.
    Footprint: `{Means, NecessarySubjectKind, SemanticFinitude, Subject}`. -/
theorem ofGround_modal_aseity_conditional_stipulated :
    Aseity World Entity CanonicalExtDepAt Entity.ofGround :=
  ofGround_modal_aseity_conditional SemanticFinitude

/-- Divine Pure Actuality of the ground (actus purus), on the declared finitude axiom.
    Footprint: `{Initiates, Means, NecessarySubjectKind, SemanticFinitude, State, Subject}`. -/
theorem ofGround_divine_pure_actuality_stipulated :
    DivinePureActuality Entity.ofGround :=
  ofGround_divine_pure_actuality SemanticFinitude

/-- The ground has zero passive grounding potency, on the declared finitude axiom.
    Footprint: `{Means, SemanticFinitude, Subject}`. -/
theorem ofGround_no_grounding_potency_stipulated :
    ¬ PassiveGroundingPotency Entity.ofGround :=
  ofGround_no_grounding_potency SemanticFinitude

/-- Divine Simplicity of the ground, on the declared finitude axiom.
    Footprint: `{Means, SemanticFinitude, Subject, propext}`. -/
theorem ofGround_divine_simplicity_stipulated :
    DivineSimplicity Entity.ofGround :=
  ofGround_divine_simplicity SemanticFinitude

/-- The ground is non-composite (no proper ontological parts), on the declared finitude
    axiom.
    Footprint: `{Means, SemanticFinitude, Subject, propext}`. -/
theorem ofGround_non_composite_stipulated :
    NonComposite Entity.ofGround :=
  ofGround_non_composite SemanticFinitude

/-- Divine Simplicity and Transcendence of the ground, on the declared finitude axiom.
    Footprint: `{Means, SemanticFinitude, Subject, propext}`. -/
theorem ofGround_simplicity_and_transcendence_stipulated :
    DivineSimplicity Entity.ofGround ∧ TranscendentGround Entity.ofGround :=
  ofGround_simplicity_and_transcendence SemanticFinitude

/-- The ground is canonically aseitous but not itself asietic, on the declared finitude
    axiom.
    Footprint: `{Means, SemanticFinitude, Subject}`. -/
theorem ground_is_canonically_aseitous_but_not_asietic_stipulated :
    CanonicalAseity Entity.ofGround ∧ ¬ Asiety Entity.ofGround :=
  ground_is_canonically_aseitous_but_not_asietic SemanticFinitude

-- ============================================================================
-- Section 2: The bound is load-bearing in both directions, machine-checked
-- ============================================================================

/-- **Falsifiability (the `ofGround`-side counter-reading).** A semantically
    omnipotent carrier is a model of the negation of `SemanticFinitude`: take
    `S := Unit` and `M := fun _ _ => True`, so every subject means every
    proposition and `¬ (∀ s, ∃ p, ¬ M s p)` holds. The declared axiom is therefore
    falsifiable, not vacuous — which is why the unicity of C320 really rests on it
    and must be priced rather than assumed.
    Footprint: `{}`. -/
theorem semantic_omnipotence_is_consistent :
    ∃ (S : Type) (M : S → Prop → Prop),
      (∀ s p, M s p) ∧ ¬ (∀ s, ∃ p, ¬ M s p) := by
  refine ⟨Unit, fun _ _ => True, fun _ _ => trivial, ?_⟩
  intro hall
  obtain ⟨p, hp⟩ := hall ()
  exact hp trivial

/-- **The bound does real work (the `ofGround_meansAll` side).** The registered
    match arm `EntityMeans .ofGround p := True` gives the ground *every*
    proposition, so the finitude axiom is exactly what keeps the ground off the
    `Subject` sort: if some subject were the ground, that subject would mean
    every proposition, contradicting the axiom at that subject. The proof is
    routed through the axiom so the dependence is visible. (The conclusion is
    also available unconditionally from `ofGround_ne_ofSubject`; the point of
    stating it here is that it is the *bound* that forbids it, on the same
    reading of the ground that the rest of Γ uses.)
    Footprint: `{Means, SemanticFinitude, Subject}`. -/
theorem semanticFinitude_excludes_ground_from_subjects (s : Subject) :
    EntityOf s ≠ Entity.ofGround := by
  intro hEq
  obtain ⟨p, hp⟩ := SemanticFinitude s
  have hMeans : Means s p := by
    have hAll : EntityMeans (EntityOf s) p := by
      rw [hEq]
      exact True.intro
    exact hAll
  exact hp hMeans

end Logos.SemanticFinitude
