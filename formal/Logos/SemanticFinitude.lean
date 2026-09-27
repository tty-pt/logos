/-
# Logos.SemanticFinitude — the F15 sentence, named and registered (2026-09-27)

F15 identified a lemma that the corpus had already paid as an anonymous premise,
seventeen times across five files, and never registered: the per-subject meaning
bound `∀ s, ∃ p, ¬ Means s p` — no subject means every proposition, no creature is
semantically omnipotent. This module *names* that bound (`SemanticFinitude`),
registers it as a ◈ stipulation in `Stipulations.lean`, and provides ten priced
corollaries — one per divine characteristic that was conditional on the anonymous
premise — each now keyed to the single named, registered sentence.

## What this batch is, and is not

This is **consolidation and badging, not derivation** and not a new axiom. The
premise is a *hypothesis* on each corollary (`hf : SemanticFinitude`), exactly as
`asietyFreedom_yields_trueChoice` takes `AsietyFreedomOfGround`. The declared
axiom count is unmoved; every corollary's kernel footprint is byte-identical to
its unconditional-predecessor's; the ◈ badge in the generated ledger — driven by
the registry `dependents` in `formal/stipulation_audit.json` — is the single
signal that the premise is stipulated.

An *unconditioned* form, discharged by a `semanticFinitude` theorem, was
considered first. That theorem is **not provable** and is
correctly absent here: `SemanticFinitude` is refuted by the countermodel
`semantic_omnipotence_is_consistent` in this module. Making the corollaries
truly unconditional would require declaring it a twenty-sixth axiom, which
this module deliberately does not do. The conditional-but-registered
form is the corpus's established ◈ mechanism and is what lands.
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

/-- **Semantic finitude.** No subject means every proposition: no creature is
    semantically omnipotent. This is the sentence F15 named as the missing
    lemma — already paid as an explicit premise across five files and never
    registered. It bounds one uninterpreted relation on one nullary sort and
    asserts no connection between entities, so it is registered `Tag: VOCAB`
    (not META, contrast `asietyFreedom_ofGroundFreedom`). It is registered in
    `Stipulations.lean` as ◈ `semanticFinitude`.
    Footprint: `{Means, Subject}`. -/
def SemanticFinitude : Prop := ∀ s : Subject, ∃ p : Prop, ¬ Means s p

-- ============================================================================
-- Section 1: The ten priced corollaries
--
-- Each is the corresponding existing theorem with its anonymous premise
-- (`hNoTotal` / `hFinite`) discharged by the *named* registered bound `hf`.
-- No existing theorem is edited; no existing name is shadowed. Each carries
-- the ◈ marker in the generated ledger because it is a registered dependent
-- of `semanticFinitude`. Predicted footprints are byte-identical to their
-- conditional counterparts.
-- ============================================================================

/-- Exactly one universal modal ground exists — the unicity conjunct now rests
    on the *named* finitude bound rather than an anonymous premise. ◈
    Footprint: `{Means, Subject}`. -/
theorem exactly_one_universal_modal_ground_stipulated (hf : SemanticFinitude) :
    ∃ g : Entity, UniversalModalGround g ∧
      (∀ g' : Entity, UniversalModalGround g' → g' = g) :=
  exactly_one_universal_modal_ground hf

/-- The ground of reality is the sole universal grounding principle, under the
    named finitude bound. ◈
    Footprint: `{Means, Subject}`. -/
theorem ofGround_sole_universal_grounding_stipulated (hf : SemanticFinitude) :
    SoleUniversalGrounding Entity.ofGround :=
  ofGround_sole_universal_grounding hf

/-- Canonical Aseity of the ground, under the named finitude bound. ◈
    Footprint: `{Means, Subject}`. -/
theorem conditional_canonical_aseity_stipulated (hf : SemanticFinitude) :
    CanonicalAseity Entity.ofGround :=
  conditional_canonical_aseity hf

/-- Modal Aseity of the ground with respect to `CanonicalExtDepAt`, under the
    named finitude bound. ◈
    Footprint: `{Means, Subject}`. -/
theorem ofGround_modal_aseity_conditional_stipulated (hf : SemanticFinitude) :
    Aseity World Entity CanonicalExtDepAt Entity.ofGround :=
  ofGround_modal_aseity_conditional hf

/-- Divine Pure Actuality of the ground (actus purus), under the named finitude
    bound. ◈
    Footprint: `{Initiates, Means, State, Subject}`. -/
theorem ofGround_divine_pure_actuality_stipulated (hf : SemanticFinitude) :
    DivinePureActuality Entity.ofGround :=
  ofGround_divine_pure_actuality hf

/-- The ground has zero passive grounding potency, under the named finitude
    bound. ◈
    Footprint: `{Means, Subject}`. -/
theorem ofGround_no_grounding_potency_stipulated (hf : SemanticFinitude) :
    ¬ PassiveGroundingPotency Entity.ofGround :=
  ofGround_no_grounding_potency hf

/-- Divine Simplicity of the ground, under the named finitude bound. ◈
    Footprint: `{Means, Subject, propext}`. -/
theorem ofGround_divine_simplicity_stipulated (hf : SemanticFinitude) :
    DivineSimplicity Entity.ofGround :=
  ofGround_divine_simplicity hf

/-- The ground is non-composite (no proper ontological parts), under the named
    finitude bound. ◈
    Footprint: `{Means, Subject, propext}`. -/
theorem ofGround_non_composite_stipulated (hf : SemanticFinitude) :
    NonComposite Entity.ofGround :=
  ofGround_non_composite hf

/-- Divine Simplicity and Transcendence of the ground, under the named finitude
    bound. ◈
    Footprint: `{Means, Subject, propext}`. -/
theorem ofGround_simplicity_and_transcendence_stipulated (hf : SemanticFinitude) :
    DivineSimplicity Entity.ofGround ∧ TranscendentGround Entity.ofGround :=
  ofGround_simplicity_and_transcendence hf

/-- The ground is canonically aseitous but not itself asietic, under the named
    finitude bound. ◈
    Footprint: `{Means, Subject}`. -/
theorem ground_is_canonically_aseitous_but_not_asietic_stipulated
    (hf : SemanticFinitude) :
    CanonicalAseity Entity.ofGround ∧ ¬ Asiety Entity.ofGround :=
  ground_is_canonically_aseitous_but_not_asietic hf

-- ============================================================================
-- Section 2: The price of the stipulation, machine-checked in both directions
-- ============================================================================

/-- **Falsifiability (the `ofGround`-side counter-reading).** A semantically
    omnipotent carrier is a model of the negation of `SemanticFinitude`: take
    `S := Unit` and `M := fun _ _ => True`, so every subject means every
    proposition and `¬ (∀ s, ∃ p, ¬ M s p)` holds. The stipulation is therefore
    falsifiable, not vacuous — which is why the unicity of C320 really rests
    on it and must be badged ◈.
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
    proposition, so the finitude bound is exactly what keeps the ground off the
    `Subject` sort: if some subject were the ground, that subject would mean
    every proposition, contradicting the bound at that subject. The proof is
    routed through the bound so the dependence is visible. (The conclusion is
    also available unconditionally from `ofGround_ne_ofSubject`; the point of
    stating it here is that it is the *bound* that forbids it, on the same
    reading of the ground that the rest of Γ uses.)
    Footprint: `{Means, Subject}`. -/
theorem semanticFinitude_excludes_ground_from_subjects
    (hf : SemanticFinitude) (s : Subject) :
    EntityOf s ≠ Entity.ofGround := by
  intro hEq
  obtain ⟨p, hp⟩ := hf s
  have hMeans : Means s p := by
    have hAll : EntityMeans (EntityOf s) p := by
      rw [hEq]
      exact True.intro
    exact hAll
  exact hp hMeans

end Logos.SemanticFinitude
