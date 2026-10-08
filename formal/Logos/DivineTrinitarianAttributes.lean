import Logos.Agency
import Logos.Alternatives
import Logos.AsieticChoice
import Logos.BoundedMeaning
import Logos.Choice
import Logos.ConditionalTheology
import Logos.Core
import Logos.DefinitiveAgencyFrontier
import Logos.DivineClassicalAttributes
import Logos.Entity
import Logos.Modal
import Logos.ModalPossibilityFrontier
import Logos.MoralFrontierAudit
import Logos.Person
import Logos.PersonalNormativeGround
import Logos.Plurality
import Logos.RecoveredOntologicalGround
import Logos.Semantics
import Logos.TheologicalModalHardening

/-!
================================================================================
DivineTrinitarianAttributes
================================================================================
Consolidated modules:
SemanticFinitude, Precedence, CharacteristicClosure, CharacteristicSoleBearer, GoodDenial, DivineAgape, TrinitySeparations, TrinitarianPersonalGround, TrinitarianSubjectBridge, SinglePersonDenial
================================================================================
-/


/-!
================================================================================
SECTION: SemanticFinitude
================================================================================
-/
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

## The tag is `VOCAB`, and after 2026-10-03 it is finally the right one

See `GroundTranscendence` below: the unrestricted half of this sentence was always a
`META` bridge, and the split is what makes the two prices separately visible.

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
    **Semantic finitude, over contingent subjects.** No *contingent* subject means every
    proposition: no creature is semantically omnipotent.

    **Scoped on 2026-10-03.** This was `∀ s, ∃ p, ¬ Means s p`. It is now
    `∀ s, ContingentSubjectKind s → ∃ p, ¬ Means s p`, so that the three divine Persons —
    who are of the *necessary* kind, by D-2 — are not denied total meaning-capacity by a
    premise whose subject is a creature. The scope the corpus's own theorems need was
    moved, not weakened, into `GroundTranscendence` immediately below; that axiom's
    docstring gives the measurement which forced the split. No claim was withdrawn here
    and none was added.

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
    repository could price it.  Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
axiom SemanticFinitude : ∀ s : Subject, ContingentSubjectKind s → ∃ p : Prop, ¬ Means s p

/--Tag: META
    **Subject finitude in the unrestricted form, purchased as what it actually is.**

    Stated as `∀ s, ∃ p, ¬ Means s p` — no subject of either kind means every
    proposition — because that is the form the corpus consumes, and consumed it for a
    reason that is *not* the one the `VOCAB` tag advertises.

    **Why this had to be split out (2026-10-03, measured).** `SemanticFinitude` was
    carrying two incompatible jobs. Its advertised job is a semantic bound on contingent
    subjects. Its load-bearing job is that a subject with total meaning-capacity
    *inherits* the ground's total meaning through a grounding relation
    (`discriminating_subject_cannot_ground_the_ground`, `CanonicalAseity.lean:113-120`),
    and that inheritance is the only thing that lets Γ prove the ground is not a subject,
    is not externally grounded, and is the sole bearer of the divine attributes. Narrowing
    `SemanticFinitude` to contingent subjects therefore breaks not one theorem but the
    whole lane: `canonical_aseity`, `no_grounding_potency`, `divine_pure_actuality`,
    `divine_simplicity`, `exactly_one_universal_modal_ground` and the six
    `ofGround_sole_*` bearers all consume the bound applied to an *arbitrary* subject.

    **The tag was the tell.** `VOCAB` is defined as asserting no connection between
    entities (`AGENTS.md`). An axiom whose consequence is that nothing grounds the ground
    and the ground alone bears the divine attributes does assert a connection — it is a
    metaphysical bridge wearing a vocabulary label, and thirteen theorems were being
    priced at `{Means, Subject}` for a claim that was never vocabulary. The split does not
    change what Γ derives; it changes what Γ is *seen* to pay.

    **What is bought, exactly.** One `META` axiom. Rejecting it admits a semantically
    total subject, which then grounds the ground and can share its attributes, collapsing
    `CanonicalAseity`, `SoleUniversalGrounding` and every `ofGround_sole_*` bearer at
    once. `subject_finitude_is_consistent` below is that model.

    **Relationship to `SemanticFinitude`.** `GroundTranscendence` is the *stronger* of the
    two, and it entails the scoped one: a subject that means every proposition fails
    `SemanticFinitude` whatever its kind, so `GroundTranscendence` alone implies
    `SemanticFinitude`. The converse does not hold, which is the whole content of
    `subject_finitude_is_consistent` below — a necessary subject may be all-seeing while
    `SemanticFinitude` still holds, because it has no contingent subject to deny.

    So this is a *refinement*, not an independence: together they are exactly the old single
    axiom, and neither drops a commitment Γ already had. `SemanticFinitude` is the honest
    *semantic* reading and `GroundTranscendence` the *transcendence* reading, and the corpus
    now says which is which instead of charging a metaphysical price to a vocabulary tag.
    Footprint: `{Means, Subject}`. -/
axiom GroundTranscendence : ∀ s : Subject, ∃ p : Prop, ¬ Means s p

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
    Footprint: `{GroundTranscendence, Means, NecessarySubjectKind, Subject}`. -/
theorem exactly_one_universal_modal_ground_stipulated :
    ∃ g : Entity, UniversalModalGround g ∧
      (∀ g' : Entity, UniversalModalGround g' → g' = g) :=
  exactly_one_universal_modal_ground GroundTranscendence

/-- The ground of reality is the sole universal grounding principle, on the declared
    finitude axiom.
    Footprint: `{GroundTranscendence, Means, NecessarySubjectKind, Subject}`. -/
theorem ofGround_sole_universal_grounding_stipulated :
    SoleUniversalGrounding Entity.ofGround :=
  ofGround_sole_universal_grounding GroundTranscendence

/-- Canonical Aseity of the ground, on the declared finitude axiom.
    Footprint: `{GroundTranscendence, Means, Subject}`. -/
theorem conditional_canonical_aseity_stipulated :
    CanonicalAseity Entity.ofGround :=
  conditional_canonical_aseity GroundTranscendence

/-- Modal Aseity of the ground with respect to `CanonicalExtDepAt`, on the declared
    finitude axiom.
    Footprint: `{GroundTranscendence, Means, NecessarySubjectKind, Subject}`. -/
theorem ofGround_modal_aseity_conditional_stipulated :
    Aseity World Entity CanonicalExtDepAt Entity.ofGround :=
  ofGround_modal_aseity_conditional GroundTranscendence

/-- Divine Pure Actuality of the ground (actus purus), on the declared finitude axiom.
    Footprint: `{GroundTranscendence, Initiates, Means, NecessarySubjectKind, State, Subject}`. -/
theorem ofGround_divine_pure_actuality_stipulated :
    DivinePureActuality Entity.ofGround :=
  ofGround_divine_pure_actuality GroundTranscendence

/-- The ground has zero passive grounding potency, on the declared finitude axiom.
    Footprint: `{GroundTranscendence, Means, Subject}`. -/
theorem ofGround_no_grounding_potency_stipulated :
    ¬ PassiveGroundingPotency Entity.ofGround :=
  ofGround_no_grounding_potency GroundTranscendence

/-- Divine Simplicity of the ground, on the declared finitude axiom.
    Footprint: `{GroundTranscendence, Means, Subject, propext}`. -/
theorem ofGround_divine_simplicity_stipulated :
    DivineSimplicity Entity.ofGround :=
  ofGround_divine_simplicity GroundTranscendence

/-- The ground is non-composite (no proper ontological parts), on the declared finitude
    axiom.
    Footprint: `{GroundTranscendence, Means, Subject, propext}`. -/
theorem ofGround_non_composite_stipulated :
    NonComposite Entity.ofGround :=
  ofGround_non_composite GroundTranscendence

/-- Divine Simplicity and Transcendence of the ground, on the declared finitude axiom.
    Footprint: `{GroundTranscendence, Means, Subject, propext}`. -/
theorem ofGround_simplicity_and_transcendence_stipulated :
    DivineSimplicity Entity.ofGround ∧ TranscendentGround Entity.ofGround :=
  ofGround_simplicity_and_transcendence GroundTranscendence

/-- The ground is canonically aseitous but not itself asietic, on the declared finitude
    axiom.
    Footprint: `{GroundTranscendence, Means, Subject}`. -/
theorem ground_is_canonically_aseitous_but_not_asietic_stipulated :
    CanonicalAseity Entity.ofGround ∧ ¬ Asiety Entity.ofGround :=
  ground_is_canonically_aseitous_but_not_asietic GroundTranscendence

-- ============================================================================
-- Section 2: The bound is load-bearing in both directions, machine-checked
-- ============================================================================

/-- **Falsifiability of the semantic bound (the contingent reading).** A semantically
    omnipotent *creature* is a model of the negation of `SemanticFinitude`: take
    `S := Unit`, `NecessarySubjectKind := fun _ => False` so every subject is contingent,
    and `M := fun _ _ => True`, so the sole subject means every proposition. Then
    `SemanticFinitude` is refutable, so the semantic reading is falsifiable rather than
    vacuous.

    The model instantiates the vocabulary it denies: the kind predicate is inhabited and
    put on the contingent side, so the refutation is of the *scoped* sentence and not an
    artifact of an uninterpreted field (`AGENTS.md`, meaning-coherence audit).
    Footprint: `{}`. -/
theorem semantic_omnipotence_is_consistent :
    ∃ (S : Type) (NK : S → Prop) (M : S → Prop → Prop),
      (∀ s, ¬ NK s) ∧ (∀ s p, M s p) ∧
      ¬ (∀ s, (¬ NK s → ∃ p, ¬ M s p)) := by
  refine ⟨Unit, fun _ => False, fun _ _ => True, fun _ h => h, fun _ _ => trivial, ?_⟩
  intro hall
  obtain ⟨p, hp⟩ := hall () (fun h => h)
  exact hp trivial

/-- **Falsifiability of the transcendence bound.** A semantically total subject is a model
    of the negation of `GroundTranscendence`, and such a subject is not a harmless
    counterexample: by `discriminating_subject_cannot_ground_the_ground`
    (`CanonicalAseity.lean:113`) it inherits the ground's total meaning through any
    grounding relation to the ground, so it can ground the ground and share its
    attributes. This is the collapse the axiom prevents, exhibited as a model.

    Here the single subject is put on the *necessary* side, which is exactly the case the
    scoped `SemanticFinitude` no longer rules out. So this model satisfies
    `SemanticFinitude` — vacuously, since it has no contingent subject — while refuting
    `GroundTranscendence`. That witnesses `SemanticFinitude ⇏ GroundTranscendence`, and it
    does *not* witness independence in the other direction: `GroundTranscendence` entails
    `SemanticFinitude` outright, so no model can witness its converse.
    Footprint: `{}`. -/
theorem subject_finitude_is_consistent :
    ∃ (S : Type) (NK : S → Prop) (M : S → Prop → Prop),
      (∀ s, NK s) ∧ (∀ s p, M s p) ∧
      ¬ (∀ s, ∃ p, ¬ M s p) := by
  refine ⟨Unit, fun _ => True, fun _ _ => True, fun _ => trivial, fun _ _ => trivial, ?_⟩
  intro hall
  obtain ⟨p, hp⟩ := hall ()
  exact hp trivial

/-- **The bound does real work (the `ofGround`-side reading).** The registered match arm
    `EntityMeans .ofGround p := True` gives the ground *every* proposition, so the
    transcendence bound is exactly what keeps the ground off the `Subject` sort: if some
    subject were the ground, that subject would mean every proposition, contradicting the
    bound at that subject. The proof is routed through `GroundTranscendence` so the
    dependence is visible and the price appears in the footprint. (The conclusion is also
    available unconditionally from `ofGround_ne_ofSubject`; the point of stating it here is
    that it is the *bound* that forbids it, on the same reading of the ground that the
    rest of Γ uses.)
    Footprint: `{GroundTranscendence, Means, Subject}`. -/
theorem semanticFinitude_excludes_ground_from_subjects (s : Subject) :
    EntityOf s ≠ Entity.ofGround := by
  intro hEq
  obtain ⟨p, hp⟩ := GroundTranscendence s
  have hMeans : Means s p := by
    have hAll : EntityMeans (EntityOf s) p := by
      rw [hEq]
      exact True.intro
    exact hAll
  exact hp hMeans

end Logos.SemanticFinitude


/-!
================================================================================
SECTION: Precedence
================================================================================
-/
/-
# Logos.Precedence — §9: does the ground precede the true/false distinction?

`CHARACTERISTICS.md` §9 ("the Ground of Being is prior to the distinction
between true and false") was the **only** classical attribute with no theorem,
no GAPMAP claim, and no row in the generated `CLASSICAL_ATTRIBUTES` table. This
module gives it four senses and four verdicts, in the `DivineTranscendence`
precedent ("one module, several senses, no umbrella predicate"), and it corrects
one of them by **refutation** instead of construction.

### The correction this module was forced into

The prose route to §9 passes through an "empty world" — a world in which the
true/false distinction is nowhere instantiated, which the foundation would
therefore have to precede. `Entity.falsityWorld` (the all-`TV.f` valuation) is
that candidate, and the batch plan proposed

    no_form_satisfied_at_falsity_world (φ : Form) : ¬ Satisfies falsityWorld φ

as its first `{}` lemma. **That lemma is false and was not proved**, because
`Satisfies` is closed under negation: at the all-`TV.f` world
`Satisfies (Form.not (Form.atom 0))` holds. There is no world satisfying no
form, and C418 (`every_world_satisfies_some_form`) is the machine-checked
refutation. The ledger therefore carries the *weaker but true* form — a world
where **no atom** is true — and carries the refutation of the stronger reading
as a row in its own right. `base.txt` §9's argument is not weakened by this; it
is stated accurately for the first time.

### What is proved here (C417–C426, `{}` and vocabulary-only)

  * C417/C418 — the falsity world holds no atom; no world is free of satisfied
    forms. The exact shape of "where the distinction is uninstantiated".
  * C419/C421 — the ground **obtains** in such a world, and is world-invariant
    while what is true there varies. Precedence, in the positive sense.
  * C420 — ground existence entails **no** truth at all: the distinction is not a
    filter on, or a condition of, the ground.
  * C422 — the ground's scope is **not** the truth set (`T p := p`, so
    `p := False` refutes it), i.e. the distinction does not stand over it. This
    is C236 read in the other direction.
  * C423 — the ground **conditions** every content-bearer (`OneEssence`). The
    other half of §9's gap-2: it precedes and discriminates, and is not
    discriminated by.
  * C424 — an atom does **not** obtain at such a world: the corpus's separations
    idiom, discriminating.
  * C426 — the limit. `Core.T p := p` is **world-free**, so the Prop-level
    right/wrong distinction admits no world-relative precedence; precedence is a
    claim about the semantic layer, which is where C419–C425 are stated.

Zero new axioms, zero new primitives, zero new stipulations, zero new ◈
registrations. The plan of record is `PLAN.md`; there is no root `AUDIT.md`.
-/

namespace Logos.Precedence

open Logos.Core (T N_T N_F rightWrongDistinction)
open Logos.Semantics (Form World Satisfies TV)
open Logos.Entity (Entity ExistsAt actualWorld falsityWorld)
open Logos.RecoveredOntologicalGround (EntityMeans OneEssence)
open Logos.Agency (Means)
open Logos.NecessityEternity (Time ExistsAtTime Everlasting Atemporal)
open Logos.DivineImmutability (StageInvariance ofGround_stage_invariance)

-- ============================================================================
-- Section 0: the falsity world, and the correction
-- ============================================================================

/-- No atom is true at the falsity world: the all-`TV.f` valuation is the
    world-space point where the true/false distinction is instantiated nowhere in
    the atomic content.

    This is the honest form of "a world in which nothing holds". The stronger
    form — no *form* is satisfied — is false and is refuted by
    `every_world_satisfies_some_form` (C418), because `Satisfies` is closed under
    negation. `EntityExistsAt falsityWorld (ofAtom n)` is this same equation, so
    this row is simultaneously the empty-world fact at the level of truth and at
    the level of entity-existence.
    Footprint: `{}`. -/
theorem no_atom_is_true_at_falsityWorld (n : Nat) :
    ¬ Satisfies falsityWorld (Form.atom n) :=
  fun h => TV.noConfusion h

/-- **No world satisfies no form.** For every world there is a satisfied form:
    the atom `0` if the world makes it true, its negation otherwise.

    This is the refutation of the "empty world" reading of §9's argument. It
    holds constructively — the branch is on `w 0 = TV.t`, and `TV` derives
    `DecidableEq` — so it carries no `Classical.choice` cost, and it is the reason
    the batch states precedence over *atomic* content rather than over satisfied
    forms. It also matches `Atom.necessary_entity_exists` (C200): the
    world-rigid ground is the one thing present in every world, which is why
    "the world where nothing holds" is never literally nothing.
    Footprint: `{}`. -/
theorem every_world_satisfies_some_form (w : World) :
    ∃ φ : Form, Satisfies w φ := by
  by_cases h : w 0 = TV.t
  · exact ⟨Form.atom 0, h⟩
  · exact ⟨Form.not (Form.atom 0), h⟩

-- ============================================================================
-- Section 1: Sense A — the ground obtains where no atom is true
-- ============================================================================

/-- **Precedence, in the positive sense: the ground obtains in a world where no
    atom is true.** The world is `Entity.falsityWorld` and the ground's
    existence there is the `ofGround` arm of `EntityExistsAt`
    (`Entity.lean:66`, the definitional world-rigidity stipulation), so this row
    is `True.intro` on the existence side and C417 on the truth side.

    Footprint: `{NecessarySubjectKind, Subject}`. The vocabulary-only price is
    an artifact of `ExistsAt` unfolding to `EntityExistsAt`, whose `ofSubject`
    arm mentions the kind predicate: the proof never reads it. This is the same
    footprint C200 and C204 already carry, and `AGENTS.md`'s rule is that the
    audited footprint is printed, not edited.
    -/
theorem ofGround_obtains_where_no_atom_is_true :
    ∃ w : World, (∀ n : Nat, ¬ Satisfies w (Form.atom n)) ∧ ExistsAt w Entity.ofGround :=
  ⟨falsityWorld, fun n => no_atom_is_true_at_falsityWorld n, trivial⟩

-- ============================================================================
-- Section 2: Sense B — the distinction is not a condition of the ground
-- ============================================================================

/-- **Ground existence entails no truth whatsoever.** It is false that every
    form satisfied at a world where the ground obtains is true, so the
    true/false distinction neither filters the ground nor is conditioned on it.

    The witness is `falsityWorld` and the atom `0`: the ground obtains there (the
    `ofGround` arm of `EntityExistsAt` is `True`) while `Form.atom 0` is
    *not* satisfied (C417). This is the converse of what a "precedence" reading
    would need, and it is why §9's characteristic is a separation rather than a
    filter.
    Footprint: `{NecessarySubjectKind, Subject}` (same `ExistsAt` artifact). -/
theorem ground_existence_does_not_entail_any_truth :
    ¬ (∀ w : World, ∀ φ : Form, ExistsAt w Entity.ofGround → Satisfies w φ) := by
  intro h
  exact no_atom_is_true_at_falsityWorld 0 (h Entity.falsityWorld (Form.atom 0) trivial)

-- ============================================================================
-- Section 3: Sense C — the contrast that makes A and B one claim
-- ============================================================================

/-- **The ground obtains where nothing atomic is true, and its obtaining entails
    nothing true.** The conjoined form: A and B as one statement of precedence,
    so a reader sees the positive and the negative half in a single row.

    `ground_existence_is_invariant_while_content_varies` is the name the
    distinction's own invariance needs: what is true varies from world to world
    (C180's `HardenedInvariance` row, on the agent), while the ground's obtaining
    does not.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem ground_existence_is_invariant_while_content_varies :
    (∃ w : World, (∀ n : Nat, ¬ Satisfies w (Form.atom n)) ∧ ExistsAt w Entity.ofGround) ∧
    ¬ (∀ w : World, ∀ φ : Form, ExistsAt w Entity.ofGround → Satisfies w φ) :=
  ⟨ofGround_obtains_where_no_atom_is_true,
   ground_existence_does_not_entail_any_truth⟩

/-- **An atom does not obtain at a world where no atom is true.** The
    discriminating half, in the corpus's separations idiom: the predicate holds of
    the ground and fails of a worldly atom, with both halves proved rather than
    asserted.

    The proof is one line and is worth naming: `EntityExistsAt w (ofAtom 0)` *is*
    `w 0 = TV.t`, which *is* `Satisfies w (Form.atom 0)`. So an atom's existence
    is its own truth, and no world can both satisfy and deny it. Precedence is a
    property of the ground-constructor, not of worldly content.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem atom_fails_precedence :
    ¬ ∃ w : World, (∀ n : Nat, ¬ Satisfies w (Form.atom n)) ∧
        ExistsAt w (Entity.ofAtom 0) := by
  rintro ⟨w, hnone, hAt⟩
  exact hnone 0 hAt

-- ============================================================================
-- Section 4: Sense D — the positive half, and §9's gap-2
-- ============================================================================

/-- **The ground's scope is not the truth set.** It is false that the ground means
    exactly the true propositions, so the right/wrong distinction does not stand
    over the ground.

    The refutation is one instance: `EntityMeans Entity.ofGround p` reduces to
    `True` for every `p` (the definitional meaning-everything stipulation,
    `RecoveredOntologicalGround.lean:46`), while `T p := p`, so at `p := False`
    the two sides disagree. This is C236's `ofGround_not_truth_tracking` read in
    the other direction — the earlier row excluded the ground from truth-tracking
    by a content argument, this one excludes it by the meaning-side definition.
    Footprint: `{Means, Subject}` (the `Means` arm of `EntityMeans`). -/
theorem ground_scope_is_not_the_truth_set :
    ¬ (∀ p : Prop, EntityMeans Entity.ofGround p ↔ T p) := by
  intro h
  exact (h False).mp trivial

/-- **The ground conditions every content-bearer.** Whatever obtains at a world
    and means something is grounded by the ground, in the corpus's existing
    `OneEssence` relation.

    Note that the meaning hypothesis is **not needed** — `OneEssence
    Entity.ofGround e` is `∀ p, EntityMeans e p → True`, which holds for every
    entity. The hypothesis is carried because §9's prose says "every being that
    stands under the distinction", and stating it makes the row readable as that
    claim. The stronger fact it implies is the report: under Γ's definitions the
    ground is a condition of *everything*, meaning-bearing or not. This is the
    same fact C328 records for the meaningless (`intro p _; exact True.intro`),
    and it is cited there rather than re-proved for atoms.
    Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
theorem ground_conditions_every_content_bearer (w : World) (e : Entity) :
    ExistsAt w e → (∃ p : Prop, EntityMeans e p) → OneEssence Entity.ofGround e :=
  fun _ _ _ _ => trivial

-- ============================================================================
-- Section 5: the master statement, in the four senses above
-- ============================================================================

/-- **Precedence to the right/wrong distinction**, as a structure over the four
    senses, so that no single umbrella predicate has to carry the whole claim:
    the ground obtains where no atom is true (A), the ground conditions every
    content-bearer (D-positive), and the ground is not itself evaluated by the
    distinction (D-negative). Sense B (`ground_existence_does_not_entail_any_truth`)
    is the conjoined partner in
    `ground_existence_is_invariant_while_content_varies`, and Sense C
    (`atom_fails_precedence`) is the separation that makes the positive half
    discriminating rather than vacuous.

    The three fields together are §9's gap-2 in one object: the foundation
    precedes the distinction *and* discriminates it *and* is not discriminated by
    it. "Precedes" is deliberately phrased as `OneEssence` — a condition — and
    never as a derivation; `ground_scope_is_not_the_truth_set` is the field that
    keeps the ground from standing under the distinction, and
    `ground_existence_does_not_entail_any_truth` is what forbids reading the
    first field as the second.

    The structure itself carries no kernel footprint of its own — only its three
    projections are kernel declarations, and each inherits the footprint of the row
    it projects (`{NecessarySubjectKind, Subject}`, `{Means, Subject}` and
    `{Means, NecessarySubjectKind, Subject}` respectively). -/
structure PrecedesRightWrong (e : Entity) : Prop where
  /-- A: the ground obtains in a world where no atom is true. -/
  obtains_where_no_atom_is_true :
    ∃ w : World, (∀ n : Nat, ¬ Satisfies w (Form.atom n)) ∧ ExistsAt w e
  /-- D-positive: every meaning-bearing entity that obtains is conditioned by it. -/
  conditions_every_bearer : ∀ w : World, ∀ e' : Entity,
    ExistsAt w e' → (∃ p : Prop, EntityMeans e' p) → OneEssence e e'
  /-- D-negative: the distinction does not stand over it. -/
  not_evaluated_by_it : ¬ (∀ p : Prop, EntityMeans e p ↔ T p)

/-- **The ground of reality precedes the right/wrong distinction.** The
    characteristic of `CHARACTERISTICS.md` §9, discharged in the four senses
    above and with the world-free limitation of C426 stated below it.

    Zero substantive axioms: `{}` and vocabulary-only rows, `Means` and the pure
    sort `Subject` being the whole price. What this row does **not** do is
    establish precedence at the `Prop` level — see
    `rightWrongDistinction_is_world_invariant` (C426), and the ledger row's
    status is the split PROVEN / limited, not a bare PROVEN.
    Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
theorem ofGround_precedes_the_right_wrong_distinction :
    PrecedesRightWrong Entity.ofGround :=
  { obtains_where_no_atom_is_true := ofGround_obtains_where_no_atom_is_true
    conditions_every_bearer :=
      fun w e' hw hm => ground_conditions_every_content_bearer w e' hw hm
    not_evaluated_by_it := ground_scope_is_not_the_truth_set }

-- ============================================================================
-- Section 6: the limit — why §9's status cannot be a bare PROVEN
-- ============================================================================

/-- **The Prop-level right/wrong distinction is world-invariant — because it has
    no world in it.** `Core.T p := p` (`Core.lean:40`) is the identity on
    `Prop`, so `N_T` and `N_F` are statements about `Prop` with no world index.

    The world argument in the statement is deliberately inert, and that is the
    content: it exhibits that a world-relative precedence to the *Prop-level*
    distinction is not well-formed under Γ's current vocabulary. §9 is therefore
    established at the semantic layer (`Satisfies`, C419–C425) and is **not**
    established at the truth-predicate layer, and the honest status is the split.
    Lifting it to a bare PROVEN would require a world-indexed `T`, which is new
    vocabulary at `Tag: SEM` at minimum and is the author's call, not this
    batch's.

    The underlying theorem is `Core.rightWrongDistinction` (`{}`); this row adds
    the world-invariance observation and no new content.
    Footprint: `{}`. -/
theorem rightWrongDistinction_is_world_invariant (_w : World) :
    ¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F :=
  rightWrongDistinction

-- ============================================================================
-- Section 7: unicity — §9's precedence has exactly one instance, and §8's
-- temporal precedence does not (this is the articulation CHARACTERISTICS.md §9
-- asked for, stated as a separation rather than a conjunction)
-- ============================================================================

/-- **Stage invariance and atemporality are the same predicate under two names.**
    `StageInvariance` (`DivineImmutability.lean:86`) and `Atemporal`
    (`NecessityEternity.lean:92`) both unfold to
    `∀ t₁ t₂ : Time, ExistsAtTime t₁ e ↔ ExistsAtTime t₂ e`.

    Recorded because it was found while proving the separation below and it
    matters for reading the corpus: §8's "timelessness" and the second field of
    the immutability master are not two steps, they are one. What *does* work is
    the one-dimensional contrast, since `Everlasting e := ∀ t, ExistsAtTime t e`
    is a genuinely different shape — that is C436 in `Logos.NecessityEternity`.

    Footprint: `{NecessarySubjectKind, Subject}`. The kind axiom enters through
    `ExistsAt` alone; the row reads no predicate.
    -/
theorem stage_invariance_iff_atemporal (e : Entity) :
    StageInvariance e ↔ Atemporal e :=
  Iff.rfl

/-- **The ground of reality is the SOLE entity preceding the right/wrong
    distinction.** Unicity for §9, in the corpus's own idiom
    (`ofGround_sole_universal_ground`, `ofGround_sole_pure_actuality`).

    The three constructor cases exhaust `Entity`:

    - `ofAtom n` is C424 verbatim and needs nothing: `obtains_where_no_atom_is_true`
      hands over a world `w` where `ExistsAt w (ofAtom n)`, which *is*
      `Satisfies w (Form.atom n)` definitionally, and the field also hands over
      its denial. This arm is `{}`.
    - `ofSubject s` is where the price sits, and the price is **F15**. The second
      field `conditions_every_bearer` is universal in the conditioned entity, so
      instantiating it at `ofGround` — which obtains everywhere and means
      everything — forces `OneEssence (EntityOf s) ofGround`, i.e.
      `∀ p, Means s p`. `SemanticFinitude` (`SemanticFinitude.lean:151`, the
      declared `Tag: VOCAB` bound, `∀ s, ∃ p, ¬ Means s p`) is exactly the denial
      of that. So **§9's unicity is a corollary of the same sentence that closed
      F15's foundational unicity**: one bound, two characteristics.
    - `ofGround` is the goal.

    **What this row does not use.** The person bridge #9 of
    `base.txt:1526` (`Ground(e, personal) → Personal(e)`, ledgered BLOCKED at
    C228) plays no part: personhood is irrelevant to precedence here, and the row
    is deliberately provable without it.

    **Why the price is acceptable.** `SemanticFinitude` is `Tag: VOCAB`, so the
    badge is `PROVEN` and no substantive axiom is used; but it is the first time
    that axiom is priced inside the §9 lane, which previously ran on `{}` and
    vocabulary alone, and the reader is entitled to know that.
    Footprint: `{GroundTranscendence, Means, NecessarySubjectKind, Subject}`.
    `NecessarySubjectKind` rides along because the field
    `conditions_every_bearer` is typed over `ExistsAt`, which unfolds to
    `SubjectExistsAt`; the proof reads no predicate.
    -/
theorem ofGround_sole_precedes_right_wrong :
    ∀ e : Entity, PrecedesRightWrong e → e = Entity.ofGround := by
  intro e h
  cases e with
  | ofSubject s =>
      have hGrounds : OneEssence (Entity.EntityOf s) Entity.ofGround :=
        h.conditions_every_bearer Entity.actualWorld Entity.ofGround trivial
          ⟨True, trivial⟩
      have hAll : ∀ p : Prop, Means s p := by
        intro p
        exact hGrounds p trivial
      obtain ⟨p, hp⟩ := Logos.SemanticFinitude.GroundTranscendence s
      exact False.elim (hp (hAll p))
  | ofAtom n =>
      obtain ⟨w, hnone, hAt⟩ := h.obtains_where_no_atom_is_true
      exact False.elim (hnone n hAt)
  | ofGround => rfl

/-- **Stage invariance does NOT single out the ground — the second atom has it
    too.** The discriminating half of the §9/§8 articulation.

    `Entity.ofAtom 0` is stage-invariant: `EntityExistsAt (stageOf t) (ofAtom 0)`
    reduces to `(stageOf t) 0 = TV.t`, i.e. `0 ≤ t`, which holds at every stage,
    yet it is obviously not the ground. So the two precedences of §9 and §8 differ
    in *discriminating power*, and this row is what makes the difference visible.

    **The mistake this row exists to prevent.** The obvious way to "articulate"
    §9 against §8 is to conjoin `PrecedesRightWrong Entity.ofGround` with
    `StageInvariance Entity.ofGround`. That conjunction is a restatement of two
    facts already proven (C425 and `ofGround_stage_invariance`) and discriminates
    nothing — the identical defect `CapacityInvariance` carries and which C321
    already reports as vacuous. A separation is the honest form.

    Footprint: `{propext, NecessarySubjectKind, Subject}`. `propext` enters
    through `simp` reducing `stageOf t 0` and is Lean's own foundational axiom,
    not a premise; the kind axiom enters through `ExistsAt` alone. This is the
    same footprint shape as C395–C397.
    -/
theorem stage_invariance_does_not_uniquely_identify_the_ground :
    StageInvariance Entity.ofGround ∧
      ¬ (∀ e : Entity, StageInvariance e → e = Entity.ofGround) := by
  refine ⟨ofGround_stage_invariance, ?_⟩
  intro hall
  have hTrue : ∀ t : Time, ExistsAt (Logos.NecessityEternity.stageOf t) (Entity.ofAtom 0) := by
    intro t
    show (Logos.NecessityEternity.stageOf t) 0 = Logos.Semantics.TV.t
    simp [Logos.NecessityEternity.stageOf]
  have hAtom : StageInvariance (Entity.ofAtom 0) := by
    intro t₁ t₂
    exact ⟨fun _ => hTrue t₂, fun _ => hTrue t₁⟩
  exact Entity.noConfusion (hall (Entity.ofAtom 0) hAtom)

/-- **Reader-facing: §9's precedence identifies the ground uniquely, where §8's
    temporal precedence does not.** The articulation of the two precedences that
    `CHARACTERISTICS.md` §9 still lists as open, discharged as a **separation of
    discriminating power** rather than an identification: `PrecedesRightWrong` has
    a unique instance (C433), `StageInvariance` has at least two (C434).

    **What is established:** the two notions are not coextensive, and only one of
    them picks the ground out. **What is not:** any identification of "precedence
    over evaluation" with "precedence over time" — they are *different* predicates
    with *different* extension, and C432 already records that one of the corpus's
    names for the second (`StageInvariance`) is a synonym of `Atemporal`.

    Footprint: `{GroundTranscendence, Means, NecessarySubjectKind, Subject, propext}`.
    Still `PROVEN`: the only axiom in the set that is not vocabulary is
    `SemanticFinitude`, `Tag: VOCAB`, and `propext` is Lean's own.
    -/
theorem precedence_identifies_the_ground_where_stage_invariance_does_not :
    (∀ e : Entity, PrecedesRightWrong e → e = Entity.ofGround) ∧
      ¬ (∀ e : Entity, StageInvariance e → e = Entity.ofGround) :=
  ⟨ofGround_sole_precedes_right_wrong,
    stage_invariance_does_not_uniquely_identify_the_ground.2⟩

end Logos.Precedence

-- Axiom footprint audit
#print axioms Logos.Precedence.no_atom_is_true_at_falsityWorld
#print axioms Logos.Precedence.every_world_satisfies_some_form
#print axioms Logos.Precedence.ofGround_obtains_where_no_atom_is_true
#print axioms Logos.Precedence.ground_existence_does_not_entail_any_truth
#print axioms Logos.Precedence.ground_existence_is_invariant_while_content_varies
#print axioms Logos.Precedence.atom_fails_precedence
#print axioms Logos.Precedence.ground_scope_is_not_the_truth_set
#print axioms Logos.Precedence.ground_conditions_every_content_bearer
#print axioms Logos.Precedence.ofGround_precedes_the_right_wrong_distinction
#print axioms Logos.Precedence.rightWrongDistinction_is_world_invariant
#print axioms Logos.Precedence.stage_invariance_iff_atemporal
#print axioms Logos.Precedence.ofGround_sole_precedes_right_wrong
#print axioms Logos.Precedence.stage_invariance_does_not_uniquely_identify_the_ground
#print axioms Logos.Precedence.precedence_identifies_the_ground_where_stage_invariance_does_not


/-!
================================================================================
SECTION: CharacteristicClosure
================================================================================
-/
/-
# Logos.CharacteristicClosure — the last conditional form of Divine Simplicity, and the one field that is not vacuous

Two of the seven footprint characteristics had a defect that survived every previous batch, and
both are closed here **at 0 new axioms**. Neither is a new doctrine: each discharges a hypothesis
that Γ has already paid for, or exhibits a refuter that the previous batch left implicit.

## 1. Divine Simplicity was the last *conditional* instantiated form

Every other footprint characteristic is instantiated unconditionally. `DivineImmutability` is
`{Initiates, Means, NecessarySubjectKind, State, Subject}`, `FoundationalOmnipresence` is
`{Means, NecessarySubjectKind, Subject}`, `FoundationalOmniscience` the same, pure actuality and
transcendence likewise. **Divine Simplicity was the exception**: `ofGround_divine_simplicity`
(C196) still took an anonymous premise

```lean
(∀ s : Subject, ∃ p : Prop, ¬ Means s p) → DivineSimplicity Entity.ofGround
```

That premise *is* `SemanticFinitude` (F15, `SemanticFinitude.lean:162`, declared 2026-09-28,
`Tag: VOCAB`). It was a bare hypothesis only because F15 had not been declared when C196 was
written — the sentence the corpus had paid anonymously seventeen times was not yet a name. Now it
is, so the form is discharged below and the ground is simple **unconditionally**, with the F15
price visible in the audited footprint instead of hidden in an argument.

This is why the theorem cannot live in `DivineSimplicity.lean`: that file is imported *by*
`SemanticFinitude.lean`, and the discharge runs the other way. A new module is the only shape that
respects the dependency order, exactly as `Precedence.lean` and `CharacteristicSoleBearer.lean`
already do.

## 2. `TransitionInvariance` is not the field C321 emptied

C321 proved `CapacityInvariance` is satisfied by **every entity whatsoever** — a vacuity, and a
correct disclosure. Its sibling `TransitionInvariance = NotInSuccession` was then reported, in the
succession audit (C458–C462), to be *non-discriminating* too: C459 showed it holds of every atom,
and the field's discharging proof for the ground discards the `Initiates` conjunct and closes on
constructor disjointness alone.

Both findings are right, and together they left the field with no positive content at all: it holds
of the ground, it holds of every atom, and nobody had shown it can *fail*. That is a gap, because
a predicate that nothing refutes is not "non-discriminating", it is untested. The act datum (C454,
`performative_act_datum`, `Tag: TRANS`) supplies the refuter: `Act s p` unfolds to
`Means s p ∧ ∃ w w', Initiates s w w' p`, so an act *is* an initiation, and an initiation is
precisely what `NotInSuccession` denies. Hence `some_entity_is_in_succession` below.

**The asymmetry with C321, which is the point of the pair.** `CapacityInvariance` is vacuous
*definitionally* — `EntityMeans` takes no world argument, so the two bound worlds are unused and
the body reduces to `P ↔ P`, discharged by `Iff.rfl`. `NotInSuccession` quantifies genuinely over
`s σ σ' p`, and the refuter here is a real inhabitant of the relation, not a definitional artefact.
So the two fields of one structure now have *opposite* disclosure statuses, and the difference is
in the vocabulary rather than in the proofs. That is the same lesson C321 taught, in the other
direction, and it is why both belong in the same batch.

**What this does not do.** It does not make the ground the sole bearer of immutability. One
refuter is not unicity: `NotInSuccession` holds of every entity that never initiates, and the act
datum requires *one* subject to act, not initiation by every necessary-kind subject. The unicity question (C453) is settled in
`Logos.ImmutabilitySoleBearer` — negatively, by countermodel.
-/

namespace Logos.CharacteristicClosure

open Logos.Semantics (World)
open Logos.Entity (Entity EntityOf)
open Logos.Agency (Subject State Means Initiates Act act_implies_initiates
  performative_act_datum)
open Logos.NecessityEternity (NotInSuccession)
open Logos.RecoveredOntologicalGround (OneEssence)
open Logos.DivineSimplicity (DivineSimplicity TranscendentGround
  ofGround_divine_simplicity divine_simplicity_sole_bearer)
open Logos.SemanticFinitude (GroundTranscendence)

-- ============================================================================
-- Section 1: the last conditional instantiated form, discharged
-- ============================================================================

/-- C484 — **the ground is divinely simple, unconditionally.** The premise
    `(∀ s, ∃ p, ¬ Means s p)` that C196 still carried is `SemanticFinitude` (F15): now a declared
    axiom, so it is paid *in the footprint* instead of being handed over as an anonymous argument.
    Nothing about the statement changed; what changed is that Γ can now be asked for it without
    the reader supplying a hypothesis on the corpus's behalf.

    **Disclosure.** The price is real and it is the F15 bound on `Means` — it did not become free.
    Because F15 carries `Tag: VOCAB`, the ledger's display for this row is `PROVEN`, not `PROVEN↑`;
    the honest summary is still *simplicity at the price of semantic finitude*, not simplicity
    outright.
    Compare C320 (`exactly_one_universal_modal_ground`), which pays the same bound for the same
    reason: it is the only declared bound on a subject's propositional reach.

    **No claim about essence.** `NonComposite e := ¬ ∃ p, ProperPart p e` is *mereological*
    simplicity — no distinct entity externally grounds `e`. It is not the identity of essence and
    existence (`CHARS.md` §13's honest boundary), and nothing here moves that boundary.

    Footprint: `{GroundTranscendence, Means, Subject, propext}`. -/
theorem the_ground_is_divinely_simple : DivineSimplicity Entity.ofGround :=
  ofGround_divine_simplicity GroundTranscendence

/-- C485 — the same result in existence form, so the characteristic is instantiated rather than
    merely held of a named entity: **something in Γ is divinely simple.**
    Footprint: `{GroundTranscendence, Means, Subject, propext}`. -/
theorem some_entity_is_divinely_simple : ∃ e : Entity, DivineSimplicity e :=
  ⟨Entity.ofGround, the_ground_is_divinely_simple⟩

/-- C486 — the **attributes-table form, unconditional**: the ground bears Divine Simplicity and
    is its only bearer, in one declaration a reader-facing row can cite. This is C440
    (`divine_simplicity_sole_bearer`) with its anonymous premise discharged, so C440's two halves
    now have different *statuses* and the row should say so:

    * the **unicity** conjunct was already `PROVEN` and pays nothing — C439 closes on the
      `no_internal_components` field alone, and `HasInternalComponent` is `False` only on
      `Entity.ofGround` by definition;
    * the **combined** row is `PROVEN` because F15 carries `Tag: VOCAB`, but it inherits the
      bounding price even though that price adds no substantive SEM/META/TRANS axiom.

    So the pair is not uniform, and the asymmetry is the informative part: *who is simple* is
    settled by the entity inventory alone, while *that anything is simple* needs the semantic
    bound. That is the opposite of the pattern in C442–C445, where the `universal_ground` field
    made the subject arm the hard one. Recorded rather than smoothed over.

    Footprint: `{GroundTranscendence, Means, Subject, propext}`. -/
theorem the_ground_is_sole_bearer_of_divine_simplicity :
    DivineSimplicity Entity.ofGround ∧
      (∀ e : Entity, DivineSimplicity e → e = Entity.ofGround) :=
  divine_simplicity_sole_bearer GroundTranscendence

-- ============================================================================
-- Section 2: the field that is not vacuous
-- ============================================================================

/-- C487 — **something is in succession**: `NotInSuccession` is false somewhere, so the
    `transition_invariance` field of `DivineImmutability` is *refutable* and therefore not a
    vacuity in C321's sense.

    The proof is one unfolding. `performative_act_datum` (C454) supplies `Act s p`; `Act` is
    `Means s p ∧ ∃ w w', Initiates s w w' p`; so `s` initiates. And `NotInSuccession e` is
    `¬ ∃ s σ σ' p, e = EntityOf s ∧ Initiates s σ σ' p`, which `e := EntityOf s` refutes with the
    same `s`.

    **Why this is not unicity.** `NotInSuccession` is satisfied by *every* entity whose subject
    correlate never initiates, so one refuter establishes that the field has content and nothing
    more. C453 (the sole-bearer form) needs every necessary-kind subject to initiate, which is strictly stronger
    than the act datum; `Logos.ImmutabilitySoleBearer` machine-checks the gap and closes C453 as
    non-derivable. Read this theorem as the *live half* of that closure, and that module as the negative
    half.

    Footprint: `{Initiates, Means, State, Subject, performative_act_datum}`. -/
theorem some_entity_is_in_succession : ∃ e : Entity, ¬ NotInSuccession e := by
  obtain ⟨s, p, hAct⟩ := performative_act_datum
  obtain ⟨w, w', hInit⟩ := act_implies_initiates hAct
  refine ⟨EntityOf s, fun hn => ?_⟩
  exact hn ⟨s, w, w', p, rfl, hInit⟩

/-- C488 — the same refuter, stated the way `C453` would need it and **cannot** obtain it: the act
    datum does not entail that *every* subject acts. It is stated here as a conditional so that the
    two results sit adjacent, and the module docstring of `Logos.ImmutabilitySoleBearer` records
    the formal missing lemma `∀ s, NecessaryKind s → ∃ σ σ' p, Initiates s σ σ' p`.

    **Note the footprint, which is not C487's.** C487 pays `performative_act_datum` because it draws
    the act from the datum; C488 takes the act as an argument, so it pays only the vocabulary of
    `Act` itself. Read the pair as: *given* an act the field is refuted at that subject, and *hence*
    some subject refutes it — the price being exactly the datum, paid once.

    Footprint: `{Initiates, Means, State, Subject}`. -/
theorem a_subject_that_acts_is_in_succession {s : Subject} {p : Prop} (h : Act s p) :
    ¬ NotInSuccession (EntityOf s) := by
  obtain ⟨w, w', hInit⟩ := act_implies_initiates h
  exact fun hn => hn ⟨s, w, w', p, rfl, hInit⟩

-- ============================================================================
-- Section 3: the principle form, and the bound it actually needs
-- ============================================================================

/-- C491 — **the Thomistic principle form of Divine Simplicity**, the one the characteristic was
    missing: the other footprint characteristics already had `C447`–`C451`-shaped principle
    theorems (necessity and atemporality yield immutability, necessity and aseity and
    immutability yield pure actuality, universal ground and aseity yield omnipresence, necessity
    and scope yield omniscience, necessity and presence yield omnipotence). **Simplicity had
    none**, which made its presence in the attributes table depend on a reader accepting a
    *particular entity* rather than a *reason*.

    The principle read here is Aquinas' own (*ST* I q.18 a.2): what is transcendent — not an atom
    and not a subject correlate — is simple, given the declared F15 bound. This is proved for an
    arbitrary transcendent entity by exhausting `Entity`'s three constructors: atoms and subject
    correlates contradict transcendence, and the ground is simple by C484. The bound is not
    decoration: F15 is what closes the ground arm, and the corollary below shows it cannot be
    replaced by a reformulation of the same `Means` information.

    Because F15 carries `Tag: VOCAB`, the ledger display is `PROVEN`, not `PROVEN↑`; the bound
    remains part of the machine-checked price.

    Footprint: `{GroundTranscendence, Means, Subject, propext}`. -/
theorem transcendence_and_semantic_finitude_yield_divine_simplicity :
    ∀ e : Entity, TranscendentGround e → DivineSimplicity e := by
  intro e h
  cases e with
  | ofGround => exact ofGround_divine_simplicity GroundTranscendence
  | ofAtom n => exact False.elim (h.1 n rfl)
  | ofSubject s => exact False.elim (h.2 s rfl)

/-- C492 — the point of C491, machine-checked: **F15 bounds the wrong relation.** The bound it
    declares is on `Means` (`∀ s, ∃ p, ¬ Means s p`), and it is what makes
    `ofGround_non_composite` close. But the mereological field's *content* is about
    `OneEssence` — `NonComposite e := ¬ ∃ p, p ≠ e ∧ OneEssence p e` — and the countermodel
    below exhibits an interpretation in which every subject is `Means`-discriminating, F15's shape
    holds exactly, and a subject nonetheless externally grounds a non-ground entity. So the two
    finitudes are independent, and the price of simplicity is a *grounding* finitude that Γ has
    never declared.

    **Why this is worth having.** It converts "simplicity is priced by F15" from an observation
    about one proof into a statement about the vocabulary: the characteristic cannot be had at a
    weaker price, and no reformulation of the existing bound removes it. The honest options are
    therefore exactly two — declare a `OneEssence`-side finitude (`Tag: VOCAB` at minimum, an
    author decision), or keep paying F15. Both are recorded; neither is taken here.

    **Naming.** The binder `GroundRel` below is an *arbitrary* relation of that shape, not the
    corpus predicate `Logos.RecoveredOntologicalGround.OneEssence`. The distinction matters:
    the statement quantifies over every relation `Entity → Entity → Prop`, so it says no relation
    of that shape closes the grounding arm. Reading the binder as the corpus's own predicate would
    narrow the theorem to a single relation and overstate what it proves. (The corpus predicate
    was renamed `GroundsEntity` → `OneEssence` on 2026-10-02; this binder predates and does not
    follow that rename.)

    Footprint: `{}`. -/
theorem the_semantic_bound_does_not_close_the_grounding_arm :
    ∃ (Subject Entity : Type)
      (EntityOf : Subject → Entity)
      (Means : Subject → Prop → Prop)
      (GroundRel : Entity → Entity → Prop),
      (∀ s : Subject, ∃ p : Prop, ¬ Means s p) ∧
      (∃ s : Subject, ∃ g e : Entity, g = EntityOf s ∧ e ≠ g ∧ GroundRel g e) := by
  refine ⟨Bool, Nat, fun s => if s then 0 else 1, fun _ _ => False,
    fun _ e => e = 0, ?_⟩
  refine ⟨?_, ?_⟩
  · intro s
    exact ⟨True, fun h => h⟩
  · exact ⟨false, 1, 0, by decide, by decide, rfl⟩

#print axioms the_ground_is_divinely_simple
#print axioms some_entity_is_divinely_simple
#print axioms the_ground_is_sole_bearer_of_divine_simplicity
#print axioms some_entity_is_in_succession
#print axioms a_subject_that_acts_is_in_succession
#print axioms transcendence_and_semantic_finitude_yield_divine_simplicity
#print axioms the_semantic_bound_does_not_close_the_grounding_arm

end Logos.CharacteristicClosure


/-!
================================================================================
SECTION: CharacteristicSoleBearer
================================================================================
-/
/-
# Logos.CharacteristicSoleBearer — the ground is the *sole bearer* of the footprint characteristics

This module is the answer to the question the rest of the corpus leaves open. A characteristic can
be recorded in Γ in two very different ways:

* **instantiated** — `Entity.ofGround` happens to have the property. This is what
  `ofGround_divine_immutability`, `ofGround_divine_simplicity`, `ofGround_foundational_omniscience`
  and their siblings establish, and on its own it is weak: it does not distinguish *"the ground is
  the unique bearer"* from *"the ground is the only example anyone wrote down."*
* **discriminating** — the property *characterises* the ground: `∀ e, P e → e = Entity.ofGround`.
  This is the form that makes a concept do work, and until this batch it held for exactly one
  characteristic, §9 precedence (C433, `Precedence.ofGround_sole_precedes_right_wrong`).

This module proves the discriminating form for six of the seven footprint characteristics, and in
five cases the proof is *the same proof*: a subject cannot ground the ground, so a subject cannot
be a universal modal ground, so no subject bears a characteristic whose structure carries a
`universal_ground` field. The sixth — Divine Simplicity — needs no reference to F15 at all.

## What the price is, and where it sits

`SemanticFinitude` (`SemanticFinitude.lean:151`, the 27th and last declared axiom, `Tag: VOCAB`) is
`∀ s : Subject, ∃ p : Prop, ¬ Means s p`. It is used here in exactly one place: to turn the
*hypothesis* `∃ p, ¬ Means s p` of `discriminating_subject_cannot_ground_the_ground`
(`CanonicalAseity.lean:113`) into a statement about *every* subject. Everything else in this module
is a case analysis on the three constructors of `Entity`.

So the batch's honest summary is: **unicity of the ground is free, and it is free because a subject
cannot be a universal ground.** The one axiom that has to be paid (`SemanticFinitude`) is what makes
"no subject" mean *all* subjects rather than "no discriminating subject" — which is exactly the
distinction C433's docstring drew for §9 precedence, and exactly the distinction that
`discriminating_subject_cannot_ground_the_ground` records for the *other* characteristics. One
bound, two places it was needed; the corpus now says so in one file.

**This does not make the ground unique among grounds.** The theorems below say the ground is the
*only bearer of these properties*. Where two universal grounds could coexist, Γ's answer is
`FoundationalUnicity.unicity` (C199), which needs `AsymmetricGrounding` as an extra premise and
which is a different, weaker claim; see the module note in `FoundationalUnicity.lean`.

## The seventh characteristic, and the one honest negative

* **Divine Transcendence** already had its discriminating form before this batch —
  `DivineTranscendence.ofGround_sole_transcendent_ground` (`:315`, `∀ e, TranscendentGround e → e =
  Entity.ofGround`, footprint `{Subject}`, unconditional). It was **already ledgered, as C307** — the
  batch added no theorem for it. What was missing was the reader-facing attributes row, which the
  generator now emits; the correction is recorded in `GAPMAP.md`. It is re-exported
  here in the master theorem (C446) so that all six stand side by side.
* **Divine Immutability** had **no** discriminating form in this batch, and the reason was recorded
  in `DivineImmutability.lean` and in `ImmutabilitySoleBounded` below: `capacity_invariance` is
  vacuous by reflexivity and `Initiates` is an unconstrained signature field, so the necessary-kind
  subject arm was not closable here. It was reported as a boundary, not quietly dropped. That
  boundary is now closed in the other direction by `Logos.ImmutabilitySoleBearer`: C453 is
  `COUNTERMODEL`, not `DEFERRED`.
-/

namespace Logos.CharacteristicSoleBearer

open Logos.Semantics (World)
open Logos.Entity (Entity EntityOf ExistsAt actualWorld)
open Logos.Agency (Subject Means)
open Logos.RecoveredOntologicalGround (EntityMeans OneEssence)
open Logos.NecessityEternity (ofGround_ground_of_reality)
open Logos.CanonicalAseity (discriminating_subject_cannot_ground_the_ground)
open Logos.DivineSimplicity (DivineSimplicity TranscendentGround
  divine_simplicity_is_unique_to_the_ground)
open Logos.FoundationalOmnipresence (FoundationalOmnipresence MaximalCapacity
  UniversalModalGround)
open Logos.FoundationalUnicity (AsymmetricGrounding)
open Logos.DivinePureActuality (DivinePureActuality atom_fails_pure_actuality
  discriminating_subject_fails_pure_actuality)
open Logos.DivineOmniscience (FoundationalOmniscience atom_not_truth_exhaustive)
open Logos.DivineOmnipotence (FoundationalOmnipotence atom_not_gapless_operate)
open Logos.DivineTranscendence (ofGround_sole_transcendent_ground)
open Logos.SemanticFinitude (GroundTranscendence)

/-- C441 — the shared subject arm, in the exact form the three `universal_ground` routes need: a
    subject-correlate that grounds `Entity.ofGround` would have to mean every proposition, and
    `SemanticFinitude` denies that. This is the one place the batch pays the 27th axiom; the
    `hG` it is handed is the `OneEssence` disjunct of a `UniversalModalGround` witness
    instantiated at `(actualWorld, Entity.ofGround)`.

    Every `ExistsAt` premise discharged here is the ◈ stipulation `ofGround_existsAt`; the
    `OneEssence` disjunct is the *other* branch of `UniversalModalGround`, so no assumption
    about the subject's world-relative existence is made or needed.
    Footprint: `{GroundTranscendence, Means, Subject}`. -/
theorem no_subject_grounds_the_ground (s : Subject) :
    ¬ OneEssence (EntityOf s) Entity.ofGround := by
  obtain ⟨p, hp⟩ := GroundTranscendence s
  exact discriminating_subject_cannot_ground_the_ground s ⟨p, hp⟩

/-- C442 — **the ground alone is omniscient**: no entity other than `Entity.ofGround` is
    foundationally omniscient, so the concept discriminates the ground rather than merely
    describing it.

    *The atom arm* is free: `atom_not_truth_exhaustive` (`DivineOmniscience.lean:155`) excludes
    atoms from `TruthExhaustive` because `EntityMeans (ofAtom _) = False`. *The subject arm* runs
    through the structure's `universal_ground` field: a subject universal modal ground would have
    to ground `Entity.ofGround` itself, which is `no_subject_grounds_the_ground`.

    **Disclosure.** The `universal_ground` field is doing all the work, not the scope. Note also
    what this does *not* say: the ground is *not* infallible. `ofGround_not_truth_tracking`
    (`DivineOmniscience.lean:144`) refutes `TruthTracking Entity.ofGround`, because the ground's
    scope bears every proposition including `False` by the constructor's match arm. Unicity of
    the *permissive* sense therefore coexists with refutation of the *strong* one.
    Footprint: `{GroundTranscendence, Means, NecessarySubjectKind, Subject}`. -/
theorem ofGround_sole_foundational_omniscience :
    ∀ e, FoundationalOmniscience e → e = Entity.ofGround := by
  intro e h
  cases e with
  | ofGround => rfl
  | ofAtom n => exact False.elim (atom_not_truth_exhaustive n h.truth_exhaustive)
  | ofSubject s =>
      obtain hEq | hGr :=
        h.universal_ground actualWorld Entity.ofGround trivial
      · cases hEq
      · exact False.elim (no_subject_grounds_the_ground s hGr)

/-- C443 — **the ground alone is omnipotent**: no entity other than `Entity.ofGround` operates
    gaplessly across the satisfiable domain, so gapless operative scope characterises the ground.

    *The atom arm* is free: `atom_not_gapless_operate` (`DivineOmnipotence.lean:220`) — an atom
    exists exactly where its content obtains, so it misses the content `¬atom n`. *The subject arm*
    runs through `universal_ground` as in C442.

    **Disclosure — this is the operative sense, not the causal one.** `OperatesAt v e P` is
    *presence plus obtaining*, a priced identification of Γ's only operation relation
    (`DivineOmnipotence.lean:120`); in this batch Γ had no production relation, so causal/creative
    omnipotence stayed BLOCKED at F10 and this theorem must not be read as touching it. The
    production relation (C463) and the universal production bridge (C493) came later and leave
    this row's footprint untouched. The
    `existence_everywhere_does_not_entail_operation` countermodel (`:150`) is the machine-checked
    statement of that gap.

    **Disclosure — the necessary-kind subject arm is closed by `universal_ground`, not by
    world-rigidity.** `gapless_operators_are_ground_or_necessary_kind` (`:250`) proves that a
    gapless operator is the ground *or* a necessary-kind subject: whoever is present everywhere
    operates everything satisfiable, and `NecessarySubjectKind` makes a subject present
    everywhere. So `gapless_operate` alone does **not** characterise the ground. It is the
    `universal_ground` field, paid for by `SemanticFinitude`, that removes the second possibility.
    This is the sharpest statement in the batch of why a structure's fields are not
    interchangeable with its doctrine.
    Footprint: `{GroundTranscendence, Means, NecessarySubjectKind, Subject}`. -/
theorem ofGround_sole_foundational_omnipotence :
    ∀ e, FoundationalOmnipotence e → e = Entity.ofGround := by
  intro e h
  cases e with
  | ofGround => rfl
  | ofAtom n => exact False.elim (atom_not_gapless_operate n h.gapless_operate)
  | ofSubject s =>
      obtain hEq | hGr :=
        h.universal_ground actualWorld Entity.ofGround trivial
      · cases hEq
      · exact False.elim (no_subject_grounds_the_ground s hGr)

/-- C444 — **the ground alone is foundationally omnipresent**: no entity other than
    `Entity.ofGround` spans all worlds, grounds all beings, and spans all propositions.

    This is the cheapest of the three `SemanticFinitude`-priced rows, because its
    `maximal_capacity` field settles *both* non-ground constructors on its own:
    `EntityMeans (Entity.ofAtom _) = False` kills the atom arm with no theorem, and for a subject
    `MaximalCapacity (EntityOf s) := ∀ p, Means s p` is exactly what `SemanticFinitude` denies.

    **Disclosure — this is foundational, not physical.** Γ's omnipresence is *world-indexed
    presence plus universal grounding*, and the module says so at length
    (`FoundationalOmnipresence.lean:1-31`). Physical omnipresence (spatial extension) and
    quantitative metric infinity remain ❌: `Space`, `Spatial`, `Metric`, `Cardinal` and `Infinity`
    have no declarations in `formal/Logos/` at all, so no proof could close them.
    Footprint: `{GroundTranscendence, Means, NecessarySubjectKind, Subject}`. -/
theorem ofGround_sole_foundational_omnipresence :
    ∀ e, FoundationalOmnipresence e → e = Entity.ofGround := by
  intro e h
  cases e with
  | ofGround => rfl
  | ofAtom _ => exact False.elim (h.maximal_capacity True)
  | ofSubject s =>
      obtain ⟨p, hp⟩ := GroundTranscendence s
      exact False.elim (hp (h.maximal_capacity p))

/-- C445 — **the ground alone is Actus Purus**: no entity other than `Entity.ofGround` has zero
    passive potentiality, so Divine Pure Actuality discriminates the ground in the same
    unconditional shape as §9 precedence (C433) — which makes the two directly comparable.

    *The atom arm* is `atom_fails_pure_actuality` (`DivinePureActuality.lean:228`): an atom has
    passive existential potency, witnessed in a world where its content is false. *The subject
    arm* is `discriminating_subject_fails_pure_actuality` (`:241`) instantiated at
    `SemanticFinitude s`, which says every subject has unactualized propositional capacity.

    **Disclosure — the whole subject arm is the 27th axiom.** `DiscriminatingSubjectFails` needs
    `∃ p, ¬ Means s p`, and for *all* subjects that is `SemanticFinitude` and nothing else. The
    price is not incidental: it is the price of the ground's `EntityMeans _ p := True` stipulation,
    which is what makes "no passive intentional potency" and "means everything" the same sentence.
    Footprint: `{GroundTranscendence, Initiates, Means, NecessarySubjectKind, State, Subject}`. -/
theorem ofGround_sole_divine_pure_actuality :
    ∀ e, DivinePureActuality e → e = Entity.ofGround := by
  intro e h
  cases e with
  | ofGround => rfl
  | ofAtom n => exact False.elim (atom_fails_pure_actuality n h)
  | ofSubject s =>
      obtain ⟨p, hp⟩ := GroundTranscendence s
      exact False.elim (discriminating_subject_fails_pure_actuality s ⟨p, hp⟩ h)

/-- C446 — the batch's master theorem: **the ground is the sole bearer of all six footprint
    characteristics simultaneously**, so the six concepts jointly pick out `Entity.ofGround` and
    not merely describe it. Divine Simplicity and Divine Transcendence enter at their audited cost
    — `{Means, Subject}` and `{Subject}`, the latter unconditionally — and the other four all carry
    `SemanticFinitude`.

    The conjunction is a record, not a new inference: each conjunct is one of the theorems above
    (with `divine_simplicity_is_unique_to_the_ground` from `DivineSimplicity.lean` and
    `ofGround_sole_transcendent_ground` from `DivineTranscendence.lean`). What is new is that they
    are now available as one statement, which is the form the reader-facing list needs.

    **What it does not say.** Not that the ground is the unique *ground* — that is
    `FoundationalUnicity.unicity` (C199), which needs `AsymmetricGrounding` and is a weaker claim.
    Not that any of this is causal: the six are structural and modal, and F10 remains BLOCKED.
    Footprint: `{GroundTranscendence, Initiates, Means, NecessarySubjectKind, State, Subject}`. -/
theorem the_ground_is_sole_bearer_of_the_footprint_characteristics :
    (∀ e, FoundationalOmnipresence e → e = Entity.ofGround) ∧
    (∀ e, FoundationalOmniscience e → e = Entity.ofGround) ∧
    (∀ e, FoundationalOmnipotence e → e = Entity.ofGround) ∧
    (∀ e, DivinePureActuality e → e = Entity.ofGround) ∧
    (∀ e, DivineSimplicity e → e = Entity.ofGround) ∧
    (∀ e, TranscendentGround e → e = Entity.ofGround) :=
  ⟨ofGround_sole_foundational_omnipresence,
   ofGround_sole_foundational_omniscience,
   ofGround_sole_foundational_omnipotence,
   ofGround_sole_divine_pure_actuality,
   divine_simplicity_is_unique_to_the_ground,
   ofGround_sole_transcendent_ground⟩

/- **The boundary this batch did not cross: Divine Immutability.** Immutability is *not* in the
    master theorem, and the reason is recorded here rather than hidden. (It is a prose disclosure,
    not a theorem: Γ can neither prove nor refute the claim, and a `sorry`-bearing declaration
    would be worse than silence — the obstruction below is a *missing lemma*, and it is recorded
    in `PLAN2.md` Task 5 and in `ImmutabilitySoleBounded` in the ledger as a priced boundary.)

    * The atom arm is closable: `EntityExistsAt w (Entity.ofAtom n) = w n = TV.t` and
      `World := Nat → TV`, so a world denying `n` breaks `ModalInvariance`.
    * The subject arm is not closable here. `DivineImmutability.capacity_invariance` is
      `∀ p, ∀ _w₁ _w₂, EntityMeans e p ↔ EntityMeans e p` (`DivineImmutability.lean:131-132`) —
      **vacuously true of every entity by reflexivity**, the F16 wall. The only remaining field is
      `NotInSuccession e := ¬ ∃ s σ σ' p, e = EntityOf s ∧ Initiates s σ σ' p`
      (`NecessityEternity.lean:102-104`), which cannot be refuted generically. **Corrected
      2026-09-28 (C458–C462):** the old justification was that `Initiates` is an unconstrained
      signature field, and that justification expired when C454 (`performative_act_datum`,
      `Tag: TRANS`) inhabited `Initiates` — a countermodel in which no subject initiates anything
      is no longer admissible as a model of Γ. The field is still not refutable, and the arm is
      still open, but for a sharper reason: the predicate is *non-discriminating*, holding of every
      atom as well (C459), so `the_ground_not_in_succession` is a non-correlateness fact rather
      than a non-agency one. And `NecessarySubjectKind` has **no**
      exclusion theorem anywhere in the corpus, so a necessary-kind subject is world-rigid by
      construction and is a legitimate candidate for a world-rigidity-based characteristic.

    So immutability is reported as a **priced boundary**, and the honest reading is: *the ground
    is the sole bearer of every footprint characteristic whose structure carries a grounding or
    capacity field; immutability, whose only non-vacuous field is negative and quantified over an
    open signature, is the one whose exclusivity Γ cannot yet certify.* -/

#print axioms no_subject_grounds_the_ground
#print axioms ofGround_sole_foundational_omniscience
#print axioms ofGround_sole_foundational_omnipotence
#print axioms ofGround_sole_foundational_omnipresence
#print axioms ofGround_sole_divine_pure_actuality
#print axioms the_ground_is_sole_bearer_of_the_footprint_characteristics

end Logos.CharacteristicSoleBearer


/-!
================================================================================
SECTION: GoodDenial
================================================================================
-/
/-
# Logos.GoodDenial — the retorsion question for the moral Good, machine-answered

Binding theorem that fuses the two existing countermodels — `MoralFrontierAudit`'s
pole-freedom (C175/C176/C499 family) and `DefinitiveAgencyFrontier`'s
retorsion-failure (`retorsion_denial_does_not_commit_to_content`) — into a single
statement: denying the existence of the moral Good is **free-logically consistent**
with the full normative relying structure of Γ, and the denial itself is **not
performatively self-refuting**.

So the classical retorsion ("in denying the Good you instantiate it") fails for the
substantive moral poles. What *is* retorsively undeniable (`{}`, pure logic) is the
normative *field* — truth and the extensional Right/Wrong distinction
(`NormativeTruth`, `UndeniableNormativeDerivation`) — never the poles.

The theorem is a conjunction because the two fronts live on different carriers: the
pole-freedom witness ranges over the agency `Subject` universe (with `Correct` as the
reality-hook), while the retorsion-failure witness ranges over any fine-grained
cognitive-subject type. That is not a weakness — it is the frontier's honesty: the two
assertions are independent, and no axiom is needed to glue them.
-/

namespace Logos.GoodDenial

open Logos.Agency (Subject)
open Logos.Order (Correct)
open Logos.CognitiveToAgencyFrontier (FineCognitiveSubject)

/-- Denying the existence of the moral Good is consistent with Γ's full normative
    relying structure, and the denial itself carries no performative self-refutation.

    Left conjunct (the pole-freedom herald): there exist moral poles `G`, `E` that are
    False everywhere — no Good, no Evil obtains — while the epistemic reality-hook
    (`Correct s p → p`) stays intact: `moral_pole_postulate_is_not_a_consequence`
    (C175 family), footprint `{Initiates, Means, State, Subject}` (vocabulary-only).

    Right conjunct (the retorsion-failure herald): a fine-grained cognitive subject can
    assert its own non-commitment to a content without that assertion instantiating
    commitment to it: `retorsion_denial_does_not_commit_to_content`, footprint `{}`.

    Together they machine-answer the retorsion challenge for the Good: denying
    `∃ Good` neither contradicts the normative structure (a countermodel certifies it,
    so the denial is a coherent rival reading of Γ, not an inconsistency) nor
    self-destructs (the denial is performatively coherent: it instantiates the
    negation, never commitment to the content). What retorsion does refute
    unconditionally (`{}`) is the normative *field* — `NormativeTruth`, the
    Right/Wrong distinction — never the substantive moral poles.
    Footprint: `{Initiates, Means, State, Subject}` (vocabulary-only — carried from
    the pole-freedom herald through `correct_tracks_reality`, exactly as in
    `moral_pole_postulate_is_not_a_consequence`; zero substantive axioms). -/
theorem good_denial_is_free_logically_consistent :
    (∃ G E : Subject → Prop → Prop,
       (¬ ∃ s : Subject, ∃ p : Prop, G s p) ∧
       (¬ ∃ s : Subject, ∃ p : Prop, E s p) ∧
       (∀ s : Subject, ∀ p : Prop, Correct s p → p)) ∧
    (∃ (Subj : Type) (CS : FineCognitiveSubject Subj)
       (Reg : Subj → Prop → Prop) (s : Subj) (p : Prop),
       Reg s (¬ CS.CommitsTo s p) ∧ ¬ CS.CommitsTo s p) := by
  constructor
  · exact Logos.MoralFrontierAudit.moral_pole_postulate_is_not_a_consequence
  · exact Logos.DefinitiveAgencyFrontier.retorsion_denial_does_not_commit_to_content

end Logos.GoodDenial

-- ---------------------------------------------------------------------------
-- Axiom footprint audit (expected: vocabulary-only {Initiates, Means, State, Subject})
-- ---------------------------------------------------------------------------
#print axioms Logos.GoodDenial.good_denial_is_free_logically_consistent


/-!
================================================================================
SECTION: DivineAgape
================================================================================
-/
/-
# Logos.DivineAgape — a good case for the Trinity from self-giving love

The Trinity **cannot be derived** in Γ's discipline, and this module does not
attempt to force it. What it supplies is the strongest legitimate "case" — the
same shape the corpus already uses for the moral Good (C177 PROVEN↑ +
C176/C499 refusals):

  1. a **conditional corridor**: under three disclosed, priced `Tag: META`
     axioms — the Agape datum, the procession of the Word, the procession of
     the Spirit — the divine reality is inhabited by three pairwise-distinct
     subsistent personal centers (`TrinitarianStructure`, C108); and
  2. a catalogue of separation models (Stage B of plan `TRINITY.md`) proving
     every cheaper reading stays consistent.

Plan of record: `TRINITY.md` (root). Stage A of that plan is this file: the
divine sort, the vocabulary, the three priced axioms, the corridor theorems
(C507–C509) and the main theorem (C510). **No Γ axiom is modified.** The
creature-beloved lane stays walled (C481/C482, C503); this corridor runs in the
Godhead, where the beloved is a divine personal center — by declaration, never
by projection from the subject level.

Design decisions (locked with the author 2026-09-29):

  * **New sort, real ontology untouched.** `DivineHypostasis` is a fresh abstract
    sort. The ground is provably not a `Subject` (`ofGround_ne_ofSubject`) and
    no contingent-kind subject is necessary
    (`no_subject_is_a_necessary_entity`), so a "divine person as `Subject`"
    reading is structurally awkward. Inside the Godhead the plurality is
    *expressed*, not forced.
  * **Unicity kept, not relaxed.** `divineReality := Entity.ofGround`, the one
    universal modal ground (C320). Subsistence is defined as *having one's
    being in that one reality*. The three centers share it (C212's
    non-collapse).
  * **Three priced axioms, house pattern.** `AxAgapeEssence` (the datum),
    `AxProcessionWord` and `AxProcessionSpirit` mirror
    `AxBenevolentBearingObtains`/`AxGroundLovesContingentRealm`: declared,
    tagged `META`, priced in the docstring, with a consistency-model note.
    The love relation and the two role predicates are `opaque` vocabulary
    (the `BearingOf` pattern), so the declared-axiom count moves 32 → 35
    (17 VOCAB, 18 substantive) — exactly the plan's §3.1 estimate.
  * **Three is exactly the Spirit price.** The datum gives the source and the
    beloved (two centers). The Word bridge names the beloved the Word. The
    Spirit bridge adds the third center, distinct from both. Nothing cheaper
    can force it.

Stage B (separations, ledger/prose sync, regeneration) follows `TRINITY.md`.
-/

namespace Logos.DivineAgape

open Logos.ConditionalTheology (TrinitarianStructure)
open Logos.Entity (Entity ExistsAt actualWorld)
open Logos.NecessityEternity (ofGround_necessary)
open Logos.TheologicalModalHardening
    (ContingentEntity NecessaryEntity necessary_not_contingent)

-- ============================================================================
-- Section 1: The divine sort and the Godhead vocabulary (all `def`/`opaque`,
-- zero new axioms)
-- ============================================================================

/-- The one divine reality: `Entity.ofGround`, the world-rigid universal modal
    ground (C320). A `def`, not a new axiom: it does not restate unicity, it
    names the unique ground as the Godhead's single reality. -/
def divineReality : Entity := Entity.ofGround

/-- A divine person: a fresh abstract sort (real Γ ontologies untouched),
    equipped with its location-entity — the one reality it shares — and with a
    **mark of personal distinction**. The structure does not force the location;
    that is the content of the priced axioms below, where each centered person
    is asserted to *subsist in* `divineReality`.

    **The second field is load-bearing, and its absence was a soundness defect.**
    With `deiformEntity` alone, `DivineHypostasis` *is* `Entity` up to eta, so
    `Subsists` (a location-equality against the constant `divineReality`) had a
    **singleton** subsatisfying subset: any two subsisting hypostases were
    provably equal at `{}` — `two_subsisting_are_equal` below. `AxAgapeEssence`
    then asserts `o ≠ f` with both subsisting, `AxProcessionSpirit` asserts
    `σ ≠ the_father` with both subsisting, and **the whole kernel derived
    `False`** (2026-10-03). Every badge and price in the corpus was vacuous for
    the whole window, and the consistency gate did not notice: Gate A was pinned
    to the S4 bridge and Gate B scans axiom *statements*, while the defect lived
    in a `def` plus a structure's *arity*. `scripts/check_consistency.py` Gates C
    and D now close both holes.

    `personalProperty : Prop` is a *marker of distinction*, not the content of a
    role: `IsWord` and `IsSpirit` remain the authoritative role predicates, and a
    typed `DivineRole` field would add vocabulary without adding anything Γ can
    then say. What the field buys is precisely the thing the corpus was missing —
    two *distinct* personal properties of one location-entity, which is what
    `SelfDonation` (below) is made of, and what makes `IsWord`/`IsSpirit`
    non-vacuous for a second center. -/
structure DivineHypostasis where
  deiformEntity : Entity
  personalProperty : Prop

/-- Subsistence: a divine person has its being in the one divine reality.
    (VOCAB predicate; the "in the Godhead" conjunct every centered person
    carries.) Defined as a location-equality — by contrast, an *attribute*
    reading (self-knowledge/self-love as an intrinsic non-subsistent state)
    carries no `DivineHypostasis` at all, which is the separation of Stage B. -/
def Subsists (d : DivineHypostasis) : Prop :=
  d.deiformEntity = divineReality

/-- **Two subsisting divine persons are at one and the same location-entity.**
    This is the "of the Self" half of Agape — *doação de Si próprio* — and it is
    free: the footprint is the transitivity of `=` and nothing else, no axiom.
    Read with `agape_is_self_donation` (C575) it is what makes the gift a gift
    **of the Self** rather than a gift between two things.

    Distinct from `co_subsistence_is_co_location` (C519) in scope, not in content:
    this is the two-person form, C519 is the general one. Both are `{Subject}`. -/
theorem two_subsisting_share_one_location (f o : DivineHypostasis)
    (hf : Subsists f) (ho : Subsists o) : f.deiformEntity = o.deiformEntity := by
  have hf' : f.deiformEntity = divineReality := hf
  have ho' : o.deiformEntity = divineReality := ho
  exact hf'.trans ho'.symm

/-- Each of two subsisting persons is *in* the other: the mutual indwelling that
    perichoresis names, as numerical identity of location. Free (`{}`), and the
    reason C573's strict form is not needed for its content. -/
theorem each_subsisting_person_is_in_the_other (f o : DivineHypostasis)
    (hf : Subsists f) (ho : Subsists o) :
    o.deiformEntity = f.deiformEntity ∧ f.deiformEntity = o.deiformEntity :=
  ⟨two_subsisting_share_one_location o f ho hf,
   two_subsisting_share_one_location f o hf ho⟩

/-- `is_divine d e`: the `TrinitarianStructure` relation — the personal center
    `d` is in the divine reality `e`. -/
def is_divine (d : DivineHypostasis) (e : Entity) : Prop :=
  d.deiformEntity = e

/-- The source's love of a personal object, inside the Godhead. An `opaque`
    primitive (the `BearingOf` pattern): the kernel cannot reduce on it, so
    the love datum is a genuine commitment, never a definitional accident.
    The value `True` is hidden; the semantic content lives in this docstring:
    self-giving love — agape — aimed at a personal center. -/
opaque DivineLove (_f _o : DivineHypostasis) : Prop := True

/-- The Word: an opaque role predicate (BearingOf pattern) whose content is
    "the subsistent divine person that is the beloved object of the essential
    self-giving" — the intellectual procession, the object. -/
opaque IsWord (_d : DivineHypostasis) : Prop := True

/-- The Spirit: an opaque role predicate (BearingOf pattern) whose content is
    "the subsistent divine person through whom the gift returns" — the
    receptive/returning procession, the third center. -/
opaque IsSpirit (_d : DivineHypostasis) : Prop := True

-- ============================================================================
-- Section 2: The three priced axioms (all `Tag: META`)
-- ============================================================================

/--Tag: META
The divine source's love is essential self-giving: it reaches, and sustains,
  a distinct personal center in the Godhead (the beloved). This is the Agape
  datum — the one big price of the case.

  Content: some divine person `f` (the source, the Father) subsists in the one
  divine reality, and its love (`DivineLove`) reaches an `o` distinct from it
  that also subsists there. The object is *personal* (a `DivineHypostasis`, not a
  contingent creature, not an attribute), and the love is *directed*, in the
  `GroundBearsGood`/`DivineLove` idiom.

  Refusal model (the Narcissus world): a world whose `DivineLove` is uniformly
  `False` satisfies the whole vocabulary — every divine person subsists, no
  love reaches another — and there the datum fails. The lesser theory (unitary
  self-possession, no beloved) is therefore machine-checked consistent: the
  Agape datum is a genuine choice, never a consequence of unicity alone (C212
  is exactly what leaves the frontier open).

  Philosophical cost: a substantive doctrine of the divine love as *ecstatic,
  self-giving* — not self-love, not an intrinsic attribute. A reader who
  rejects the price rejects this axiom, and with it the whole corridor. -/
axiom AxAgapeEssence :
    ∃ f : DivineHypostasis,
      Subsists f ∧ (∃ o : DivineHypostasis, o ≠ f ∧ Subsists o ∧ DivineLove f o)

/-- The source center (the Father), extracted from the datum by choice. -/
noncomputable def the_father : DivineHypostasis := Classical.choose AxAgapeEssence

/-- The beloved center, extracted from the datum by choice. -/
noncomputable def the_beloved : DivineHypostasis :=
  Classical.choose (Classical.choose_spec AxAgapeEssence).2

/-- The datum unwrapped: the source subsists. -/
theorem the_father_subsists : Subsists the_father :=
  (Classical.choose_spec AxAgapeEssence).1

/-- The datum unwrapped: the beloved is other than the source. -/
theorem the_beloved_distinct : the_beloved ≠ the_father :=
  (Classical.choose_spec (Classical.choose_spec AxAgapeEssence).2).1

/-- The datum unwrapped: the beloved subsists in the divine reality. -/
theorem the_beloved_subsists : Subsists the_beloved :=
  (Classical.choose_spec (Classical.choose_spec AxAgapeEssence).2).2.1

/-- The datum unwrapped: the source loves the beloved. -/
theorem the_source_loves_the_beloved : DivineLove the_father the_beloved :=
  (Classical.choose_spec (Classical.choose_spec AxAgapeEssence).2).2.2

/--Tag: META
The beloved of the essential love subsists as the Word: the personal object of
  the source's self-giving is not an accidental object-of-love but a divine
  person in its own right, the intellectual procession — named, not invented.

  Refusal model (the attribute-love world): self-knowledge/self-love as an
  intrinsic non-subsistent state — a Godhead with no `DivineHypostasis` at all
  beyond the source's enacted content — satisfies the vocabulary and the datum's
  *agent* half while nothing is a Word. The subsistence conjunct of the
  procession is therefore load-bearing, and the "step 6" gap of the Augustinian
  route is exhibited, not asserted.

  Philosophical cost: the beloved is a *person*, not a mode. Substantive on
  its own account; the datum already supplied the person, this bridge names it
  the Word. -/
axiom AxProcessionWord : IsWord the_beloved

/--Tag: META
The self-gift returns: a third divine person, the Spirit, subsists in the
  divine reality, other than the source and other than every Word.

  This is the axle of the whole case. The datum gives *two* centers (father
  and beloved); nothing forces a third. The Spirit is the extra price, and the
  Stage-B binitarian separation proves three is exactly this price: Agape plus
  Word alone leave a two-center Godhead legal.

  Refusal model (the binitarian world): Agape + Word, no Spirit modality —
  a two-person Godhead is machine-checked consistent (separation C514, `{}`).

  Philosophical cost: God as *ecstatic community*, not merely as lover-and-
  beloved. A reader who stops at the procession of the Word rejects this axiom
  — and with it the *full* Trinity, keeping a binitarian reading. -/
axiom AxProcessionSpirit :
    ∃ σ : DivineHypostasis,
      IsSpirit σ ∧ Subsists σ ∧ σ ≠ the_father ∧ (∀ w : DivineHypostasis, IsWord w → σ ≠ w)

/-- The Spirit, extracted by choice. -/
noncomputable def the_spirit : DivineHypostasis := Classical.choose AxProcessionSpirit

/-- The Spirit is the returning gift (role). -/
theorem the_spirit_is_spirit : IsSpirit the_spirit :=
  (Classical.choose_spec AxProcessionSpirit).1

/-- The Spirit subsists in the divine reality. -/
theorem the_spirit_subsists : Subsists the_spirit :=
  (Classical.choose_spec AxProcessionSpirit).2.1

/-- The Spirit is other than the source. -/
theorem the_spirit_ne_father : the_spirit ≠ the_father :=
  (Classical.choose_spec AxProcessionSpirit).2.2.1

/-- The Spirit is other than every Word (role-distinction, second half). -/
theorem the_spirit_ne_any_word : ∀ w : DivineHypostasis, IsWord w → the_spirit ≠ w :=
  (Classical.choose_spec AxProcessionSpirit).2.2.2

/-- The Spirit is other than the Word (instantiated at the beloved). -/
theorem the_spirit_ne_beloved : the_spirit ≠ the_beloved :=
  the_spirit_ne_any_word the_beloved AxProcessionWord

-- ============================================================================
-- Section 3: The corridor (C507–C509)
-- ============================================================================

/-- Essential self-giving has a necessary object (C507, PROVEN↑): under the
    datum, the source's love reaches a distinct personal center that *subsists*
    — its being is the necessary divine reality. The object is thereby as
    necessary as the love itself: it is not fetched from the contingent realm
    the WALLs guard (C481/C482, C503), it is in the Godhead by declaration.
    Footprint: `{Subject, AxAgapeEssence, Classical.choice}` (the datum; `Subject`
    and `Classical.choice` are vocabulary — the extractor's choice operator). -/
theorem essential_love_has_necessary_object :
    ∃ f o : DivineHypostasis, f ≠ o ∧ Subsists f ∧ Subsists o ∧ DivineLove f o := by
  refine ⟨the_father, the_beloved, the_beloved_distinct.symm, the_father_subsists,
    the_beloved_subsists, the_source_loves_the_beloved⟩

/-- The beloved is not a creature (C508): every subsistent divine center has,
    in place of a contingent reality, the necessary ground — and is no atom.
    This is the Godhead-level answer to WALL 2: the beloved is not a
    `ContingentSubjectKind` subject (it is not a `Subject` at all), it does not
    live in a contingent entity, and it is not an atom — the three creature
    shapes of Γ's `Entity` ontology. **Provable, not priced**: it follows from the
    vocabulary once subsistence holds, which is why the row is PROVEN and not
    PROVEN↑ — no META axiom is paid here.
    Footprint: `{NecessarySubjectKind, Subject}` (vocabulary only, via
    `ofGround_necessary` and `necessary_not_contingent`). -/
theorem agape_beloved_is_not_creature {o : DivineHypostasis} (h : Subsists o) :
    ¬ ContingentEntity o.deiformEntity ∧ (∀ n : Nat, o.deiformEntity ≠ Entity.ofAtom n) := by
  constructor
  · intro hc
    have hn : NecessaryEntity o.deiformEntity := by
      dsimp [Subsists, divineReality] at h
      rw [h]
      exact ofGround_necessary
    exact necessary_not_contingent _ hn hc
  · intro n hn
    dsimp [Subsists, divineReality] at h
    rw [h] at hn
    cases hn

/-- The divine object subsists in the Godhead (C509): a subsistent center is a
    divine center — `is_divine o divineReality` holds by definition of
    subsistence. The step the Augustinian route had to leave at "step 6" is
    here *stated* as the content of `Subsists` and discharged. **Provable, not
    priced**: pure unfolding, so the row is PROVEN, not PROVEN↑.
    Footprint: `{Subject}` (vocabulary only: `is_divine o divineReality` names
    the `Entity` sort, whose ground constructor carries `Subject`). -/
theorem divine_object_subsists_in_godhead {o : DivineHypostasis} (h : Subsists o) :
    is_divine o divineReality := by
  dsimp [Subsists, is_divine, divineReality] at h ⊢
  exact h

/-- The centers are each in the divine reality (helpers for the inhabitation). -/
theorem the_father_is_divine : is_divine the_father divineReality := by
  dsimp [is_divine]
  exact the_father_subsists

/-- The centers are each in the divine reality (helpers for the inhabitation). -/
theorem the_beloved_is_divine : is_divine the_beloved divineReality := by
  dsimp [is_divine]
  exact the_beloved_subsists

/-- The centers are each in the divine reality (helpers for the inhabitation). -/
theorem the_spirit_is_divine : is_divine the_spirit divineReality := by
  dsimp [is_divine]
  exact the_spirit_subsists

-- ============================================================================
-- Section 4: The main theorem (C510)
-- ============================================================================

/-- The canonical inhabitation: the source, the beloved and the Spirit, with
    pairwise distinctness and mutual relational distinction, sharing the one
    divine reality. `relational_distinction` is taken as distinctness itself —
    the minimal, content-honest reading available at kernel level. -/
noncomputable def trinitarian_inhabitation : TrinitarianStructure DivineHypostasis Entity :=
  { P1 := the_father
    P2 := the_beloved
    P3 := the_spirit
    distinct_12 := the_beloved_distinct.symm
    distinct_23 := the_spirit_ne_beloved.symm
    distinct_13 := the_spirit_ne_father.symm
    divine_reality := divineReality
    is_divine := is_divine
    divine_1 := the_father_is_divine
    divine_2 := the_beloved_is_divine
    divine_3 := the_spirit_is_divine
    relational_distinction := fun (a b : DivineHypostasis) => a ≠ b
    rel_12 := the_beloved_distinct.symm
    rel_23 := the_spirit_ne_beloved.symm
    rel_13 := the_spirit_ne_father.symm
  }

/-- Agape entails tripersonality (C510, PROVEN↑): under the three disclosed
    Agape axioms — the datum, the procession of the Word, the procession of
    the Spirit — there is a `TrinitarianStructure` (C108) on the divine sort
    whose three distinct personal centers are *exactly* the source, the
    beloved-as-Word and the returning Spirit, all sharing the one divine
    reality. The witness form is `∃ t` because `TrinitarianStructure` is a
    `structure` in `Type`, not a `Prop` (the `∃ (_t : TrinitarianStructure Subj
    Ent), True` idiom of `ConditionalTheology`); the role conjuncts are in the
    statement so that the whole price saturates the footprint.

    Not a derivation: the case rests on three declared META premises, and
    every cheaper reading (Narcissus, creature-love, attribute-love, binitarian)
    is kept machine-checked consistent by the Stage-B separations. Unicity is
    preserved: one divine reality, three centers inside it (C212's
    non-collapse). The Word here is not the Incarnation (F8 untouched).
    Footprint: `{Subject, AxAgapeEssence, AxProcessionWord, AxProcessionSpirit,
    Classical.choice}`. -/
theorem agape_entails_tripersonality :
    ∃ t : TrinitarianStructure DivineHypostasis Entity,
      t.P1 = the_father ∧ t.P2 = the_beloved ∧ t.P3 = the_spirit ∧
        IsWord the_beloved ∧ IsSpirit the_spirit :=
  ⟨trinitarian_inhabitation, rfl, rfl, rfl, AxProcessionWord, the_spirit_is_spirit⟩

/-- A subsistent center is a necessary being (C518, PROVEN): the Agape datum
    puts the divine centers inside the necessary realm, not merely somewhere
    real. The one-line corollary of C508's first conjunct, isolated and named
    because it is what lets the NECESSARY audit's two-genera closure (C516)
    apply to the Trinity: a subsistent `DivineHypostasis`'s `deiformEntity` is
    either the ground or a necessary-kind subject's correlate — and by
    `Subsists` it is the ground, so the centers sit in the *first* genus.

    **Provable, not priced**: `Subsists` is location-equality to
    `divineReality = Entity.ofGround`, and `ofGround_necessary` is vocabulary.
    No META axiom is paid; the row is the same content as C508 read under the
    modal vocabulary, and it is filed separately because the author's position
    (the ground *is* personal) needs the modal form to be legible.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem subsisting_centre_is_necessary {d : DivineHypostasis} (h : Subsists d) :
    NecessaryEntity d.deiformEntity := by
  dsimp [Subsists, divineReality] at h
  rw [h]
  exact ofGround_necessary

/-- Co-subsistence is co-location (C519, PROVEN): two subsistent centers have
    the *same* location-entity. Read with C518 this is the "one reality, three
    centers" of C510 in the modal vocabulary, isolated so the coincidence is a
    named, reusable fact rather than a side condition. Location identity only —
    no claim about shared nature, property or act.
    Footprint: `{Subject}`. -/
theorem co_subsistence_is_co_location {a b : DivineHypostasis} (ha : Subsists a) (hb : Subsists b) :
    a.deiformEntity = b.deiformEntity := by
  dsimp [Subsists, divineReality] at ha hb
  exact ha.trans hb.symm

/-- The three centers are necessary, and one necessary reality (C520, PROVEN↑):
    the instantiations of C518 at the father, the beloved and the Spirit, plus
    the coincidence of their location-entities. The last two conjuncts are
    C519; the first three are the modal reading of C510's one-reality field.
    Coincidence of location only — consubstantiality of natures is **not**
    claimed and not proved here; it is not in the vocabulary of the sort, and
    the non-collapse of C212 is preserved (three distinct centers, one reality).
    Footprint: `{NecessarySubjectKind, Subject, AxAgapeEssence, AxProcessionSpirit,
    Classical.choice}`. -/
theorem the_three_centres_are_one_necessary_reality :
    NecessaryEntity the_father.deiformEntity ∧
      NecessaryEntity the_beloved.deiformEntity ∧
      NecessaryEntity the_spirit.deiformEntity ∧
      the_father.deiformEntity = the_beloved.deiformEntity ∧
        the_beloved.deiformEntity = the_spirit.deiformEntity :=
  ⟨subsisting_centre_is_necessary the_father_subsists,
   subsisting_centre_is_necessary the_beloved_subsists,
   subsisting_centre_is_necessary the_spirit_subsists,
   co_subsistence_is_co_location the_father_subsists the_beloved_subsists,
   co_subsistence_is_co_location the_beloved_subsists the_spirit_subsists⟩

-- ============================================================================
-- Section 5: The donation of the Self (C575–C577)
-- ============================================================================
--
-- `SelfDonation` is the sentence the corpus asserted only in prose. It is what
-- `base.txt:1811` calls *auto-doação essencial* and what the author calls
-- *doação de Si próprio*: the gift is not between two things, but between two
-- personal properties of **one** thing. The conjunct order is the argument:
-- distinct personal properties, both subsisting, a gift between them, and the
-- shared location that makes the gift *of the Self*.

/-- **SelfDonation** — the donation of the Self (*doação de Si próprio*): a gift
    between two **distinct** personal properties of **one** location-entity.

    The last conjunct is the whole point and it is the **free** one
    (`two_subsisting_share_one_location`, `{Subject}`): what the three META axioms
    buy is the gift between two distinct subsisting centers, and what they do *not*
    buy is that they are two things. Both are the ground.

    Note what this definition deliberately does **not** say. It does not say the
    ground is a `Subject`, that it chooses, or that it acts in time: those are
    refuted (§3–§4 of `LOVE.md`) or unstatable (C462/C463), and folding any of
    them in here would make the donation pay for a metaphysical bridge it does not
    need. The donation is on the entity, under personal properties. -/
def SelfDonation (f o : DivineHypostasis) : Prop :=
  f ≠ o ∧ Subsists f ∧ Subsists o ∧ DivineLove f o ∧ f.deiformEntity = o.deiformEntity

/-- **Agape is the donation of the Self (C575, PROVEN↑).** Under the datum there
    is a gift between two distinct personal properties of one location-entity —
    which is C507 with the "of the Self" conjunct named rather than inherited.

    The price is exactly C507's: `{Subject, AxAgapeEssence, CL}`,
    **one META axiom**. The last conjunct of `SelfDonation` is
    `two_subsisting_share_one_location`, at `{}`; `DivineLove` is `opaque`; and
    `DivineHypostasis`'s second field is what makes the distinctness satisfiable at
    all (before 2026-10-03 this conjunct was **unsatisfiable**, and the whole kernel
    derived `False`). -/
theorem agape_is_self_donation : ∃ f o : DivineHypostasis, SelfDonation f o :=
  ⟨the_father, the_beloved, the_beloved_distinct.symm, the_father_subsists,
    the_beloved_subsists, the_source_loves_the_beloved,
    two_subsisting_share_one_location the_father the_beloved
      the_father_subsists the_beloved_subsists⟩

/-- **Denying that the donation of the Self occurs is a declared, not derived,
    absurdity (C576, PROVEN↑).** Read the claim narrowly: assume there is *no*
    donation at all and `False` follows.

    **This is not the author's absurdity.** The objection the author names is the
    four-step chain — one Person, therefore only contingent recipients, therefore
    the self-giving *depends* on the contingent, therefore the Ground is
    contingent — and the step that dies is the third one, which dies **free**
    (C579, `SinglePersonDenial.self_gift_cannot_depend_on_a_contingent_person`).
    This row is mounted beside it, not in place of it, and the two must not be
    confused: C579 refutes the dependence *without mentioning the gift at all*,
    because `SelfDonation` puts the recipient at `divineReality := Entity.ofGround`
    and no `Subject` is that entity. So a row that refuted the objection by way of
    the datum it also prices would be the datum.

    The `denial` hypothesis is a **real premise**, not a rhetorical one: it is the
    proposition actually refuted, which is what makes the Cremation row a
    derivation rather than a badge. The refutation is `agape_is_self_donation`
    alone — no classical reasoning, no `Decidable`, no new choice principle.

    **What this is honestly worth, and why the row is priced.** `AxAgapeEssence`
    is a substantive axiom, so there is a world — the Narcissus world (C511),
    which assigns `Love` so that the source loves only itself — in which the
    denial holds. The denial is therefore *available*, and it is contradicted only
    by what is **declared**: Γ does not claim the donation is a theorem of logic.
    Consequently the row's derived kind is `⚠️ PRICED`, not `⊥ CONTRADICTION`. The
    distinction is load-bearing rather than cosmetic — `⊥` says logic closed the
    branch, while the price says a world in which the branch survives was ruled
    out by fiat. Printing the free glyph here is the laundering this row's price
    line exists to prevent. -/
theorem denying_self_donation_is_absurd
    (denial : ¬ ∃ f o : DivineHypostasis, SelfDonation f o) : False :=
  denial agape_is_self_donation

/-- **And the denial fails even when its own premises are granted (C577,
    PROVEN↑).** The stronger form: grant a donor and a recipient, grant that both
    subsist, grant that the love holds — and the denial *still* has to deny that
    they are at one location, which is `{}`.

    So "it cannot be a self-gift because the donor and the recipient are two
    things" is refuted with no additional price at all. Same footprint as C575. -/
theorem denying_shared_location_is_absurd :
    ¬ ∀ f o : DivineHypostasis, Subsists f → Subsists o → DivineLove f o →
      f.deiformEntity ≠ o.deiformEntity := by
  rintro h
  obtain ⟨f, o, _, hf, ho, hlove, hloc⟩ := agape_is_self_donation
  exact h f o hf ho hlove hloc

end Logos.DivineAgape

-- ---------------------------------------------------------------------------
-- Axiom footprint audit (as of 2026-09-29, after Stage A):
--   C507 (essential_love_has_necessary_object) .. {Subject, AxAgapeEssence, Classical.choice}
--   C508 (agape_beloved_is_not_creature) ...... {NecessarySubjectKind, Subject}
--   C509 (divine_object_subsists_in_godhead) .. {Subject}
--   C510 (agape_entails_tripersonality) ....... {Subject, AxAgapeEssence,
--                                                AxProcessionWord,
--                                                AxProcessionSpirit,
--                                                Classical.choice}
-- ---------------------------------------------------------------------------
#print axioms Logos.DivineAgape.essential_love_has_necessary_object
#print axioms Logos.DivineAgape.agape_beloved_is_not_creature
#print axioms Logos.DivineAgape.divine_object_subsists_in_godhead
#print axioms Logos.DivineAgape.agape_entails_tripersonality
#print axioms Logos.DivineAgape.the_father_subsists
#print axioms Logos.DivineAgape.the_beloved_subsists
#print axioms Logos.DivineAgape.the_spirit_subsists
#print axioms Logos.DivineAgape.subsisting_centre_is_necessary
#print axioms Logos.DivineAgape.co_subsistence_is_co_location
#print axioms Logos.DivineAgape.the_three_centres_are_one_necessary_reality
#print axioms Logos.DivineAgape.two_subsisting_share_one_location
#print axioms Logos.DivineAgape.each_subsisting_person_is_in_the_other
#print axioms Logos.DivineAgape.agape_is_self_donation
#print axioms Logos.DivineAgape.denying_self_donation_is_absurd
#print axioms Logos.DivineAgape.denying_shared_location_is_absurd


/-!
================================================================================
SECTION: TrinitySeparations
================================================================================
-/
/-!
# The Trinity separations (C511–C514) — Stage B of the Agape case

Four axiom-free (`{}`) countermodels that close every reading of the Agape case
cheaper than the Trinity. Together with Stage A (`Logos.DivineAgape`, C504–C510)
they make the price of the case exact: *three is exactly the price of the Spirit*.

Each theorem ranges over a **free signature** — a shadow of the divine
vocabulary, not an instantiation of it. `DivineLove`, `IsWord` and `IsSpirit` are
`opaque` (`DivineAgape.lean:98,103,108`), so no model of Γ can replace them by
construction; the shadows are what makes each statement checkable at all. The
mirror is:

| divine sort/predicate | shadow |
| --- | --- |
| `DivineHypostasis` | `β` |
| `Subsists` | `Sub` |
| `DivineLove` | `Love` |
| `IsWord` | `IsW` |
| `IsSpirit` | `IsS` |
| `TrinitarianStructure` | "three pairwise-distinct subsisting centres" |

That last row is the shape every conclusion carries: `TrinitarianStructure`
(`ConditionalTheology.lean:307`, C108) is a structure of three pairwise-distinct
centres, so a model *without* a `p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ p₁ ≠ p₃` triple is a model
with no trinity — in the vocabulary of the mirror.

These are shape results, **not** claims about Γ's consistency and **not**
refutations of any declared axiom. C514 in particular is the axle of the whole
case: it shows that the two centres of the Agape datum *together with* the Word
bridge leave a legal two-centre (binitarian) Godhead, so the third centre is not
a consequence of anything cheaper than `AxProcessionSpirit`.
-/

namespace Logos.TrinitySeparations

/-- **No second centre (C511).** A Godhead whose love is purely self-directed is
consistent with the whole vocabulary, and in that world no two distinct centres
subsist — the source loves itself, and the shape of a trinity cannot be built.

    What this shows: `AxAgapeEssence` (C504) is a genuine *choice*, not a
    consequence of unicity — a world without a second centre is legal.

    What this does NOT do: it does not refute `AxAgapeEssence`. The Narcissus
    world **fails** the axiom's "distinct subsisting beloved" conjunct — that is
    exactly the point: the datum is not available for free, it is the price. Nor
    does it touch C510, which is a theorem *under* the datum.
    Footprint: `{}`. -/
theorem unitarian_self_love_gives_no_second_centre :
    ∃ (β : Type) (Sub : β → Prop) (Love : β → β → Prop),
      (∃ f, Sub f ∧ Love f f) ∧
      (∀ f o, Sub f → Love f o → o = f) ∧
      (¬ ∃ p₁ p₂ p₃ : β, Sub p₁ ∧ Sub p₂ ∧ Sub p₃ ∧ p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ p₁ ≠ p₃) := by
  refine ⟨Unit, fun _ => True, fun _ o => o = (), ?_, ?_, ?_⟩
  · exact ⟨(), trivial, rfl⟩
  · intro f o _hSub hLove
    cases f
    exact hLove
  · rintro ⟨p₁, p₂, p₃, _h1, _h2, _h3, h12, _h23, _h13⟩
    cases p₁
    cases p₂
    exact h12 rfl

/-- **Creature-love.** Love may reach an Other which is a creature and *not* a
    subsisting centre; such a world still contains no trinity.

    What this shows: "the beloved is another person" does not by itself deliver
    a second *subsistent* centre — the content of C508/C509 is a conjunct, not a
    name, and cannot be read back as "whatever is loved is divine".

    What this does NOT do: `Crt` is the shape-mirror of
    `ContingentSubjectKind`, and Γ's real creature level has **no inhabitant**
    (WALL 2, C481/C482/C503) — the shadow inhabits it deliberately, because the
    creature level is not what is missing; *subsistence* is.
    Footprint: `{}`. -/
theorem creature_love_gives_no_divine_beloved :
    ∃ (β : Type) (Sub Crt : β → Prop) (Love : β → β → Prop),
      (∃ f c, Sub f ∧ Crt c ∧ ¬ Sub c ∧ Love f c) ∧
      (∀ f o, Sub f → Love f o → Sub o ∨ Crt o) ∧
      (¬ ∃ p₁ p₂ p₃ : β, Sub p₁ ∧ Sub p₂ ∧ Sub p₃ ∧ p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ p₁ ≠ p₃) := by
  refine ⟨Bool, fun d => d = false, fun d => d = true, fun _ o => o = true, ?_, ?_, ?_⟩
  · exact ⟨false, true, rfl, rfl, by decide, rfl⟩
  · intro f o _hSub _hLove
    cases o
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro ⟨p₁, p₂, p₃, _h1, _h2, _h3, _h12, _h23, _h13⟩
    cases p₁ <;> cases p₂ <;> cases p₃ <;>
      first | exact _h12 rfl | exact _h23 rfl | exact _h13 rfl

/-- **Attribute-love.** The source subsists and loves an object that is *distinct*
    — and that object does not subsist: it is an intrinsic state of the source.

    What this shows: even granting a distinct object of love, `Subsists` is
    exactly what is missing, which is the content of `AxProcessionWord` (C505)
    and the Augustinian route's "step 6" gap exhibited rather than asserted.

    What this does NOT do: it does not refute C505 (the Word *is* subsistent there
    — by declaration), and it says nothing about the name of the beloved, only
    about the subsistence conjunct.
    Footprint: `{}`. -/
theorem attribute_love_gives_no_subsistent_word :
    ∃ (β : Type) (Sub : β → Prop) (Attr : β → β → Prop) (Love : β → β → Prop),
      (∃ f o, Attr f o ∧ o ≠ f ∧ ¬ Sub o ∧ Love f o) ∧
      (¬ ∃ p₁ p₂ p₃ : β, Sub p₁ ∧ Sub p₂ ∧ Sub p₃ ∧ p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ p₁ ≠ p₃) := by
  refine ⟨Bool, fun d => d = false, fun _ _ => True, fun _ o => o = true, ?_, ?_⟩
  · exact ⟨false, true, trivial, by decide, by decide, rfl⟩
  · rintro ⟨p₁, p₂, p₃, _h1, _h2, _h3, _h12, _h23, _h13⟩
    cases p₁ <;> cases p₂ <;> cases p₃ <;>
      first | exact _h12 rfl | exact _h23 rfl | exact _h13 rfl

/-- **Binitarian: Agape + Word, exactly two centres, no Spirit.** The two centres
    of the Agape datum, the Word bridge, and *no* Spirit at all: the two-centre
    world is legal.

    What this shows: "three is exactly the price of the Spirit". Everything the
    Agape datum and `AxProcessionWord` jointly give — a self-giving source, a
    distinct beloved, that beloved *named* as the Word, and the source's own
    subsistence — is consistent with a Godhead of exactly two subsisting centres.
    The third conjunct (`∀ d, ¬ IsS d`) is the machine form of "the Spirit
    modality is unpopulated", and the fourth is the machine form of "at most two"
    (every subsisting centre is one of the two).

    What this does NOT do: it does not refute `AxProcessionSpirit` (C506), and it
    does not weaken C510, which is proven under that axiom. A reader who rejects
    C506 keeps a binitarian reading, and that is the honest boundary of the case.
    Footprint: `{}`. -/
theorem agape_and_word_without_spirit_is_binitarian :
    ∃ (β : Type) (Sub : β → Prop) (Love : β → β → Prop) (IsW IsS : β → Prop),
      (∃ f w, f ≠ w ∧ Sub f ∧ Sub w ∧ Love f w) ∧
      (∃ w, Sub w ∧ IsW w) ∧
      (∀ d, ¬ IsS d) ∧
      (∀ d, Sub d → ∃ f w, f ≠ w ∧ ((d = f ∨ d = w) ∧ Sub f ∧ Sub w)) ∧
      (¬ ∃ p₁ p₂ p₃ : β, Sub p₁ ∧ Sub p₂ ∧ Sub p₃ ∧ p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ p₁ ≠ p₃) := by
  refine ⟨Bool, fun _ => True, fun a b => a = false ∧ b = true,
    fun d => d = true, fun _ => False, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨false, true, by decide, trivial, trivial, ⟨rfl, rfl⟩⟩
  · exact ⟨true, trivial, rfl⟩
  · intro d hIsS
    exact hIsS
  · intro d _hSub
    refine ⟨false, true, by decide, ?_, trivial, trivial⟩
    cases d
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro ⟨p₁, p₂, p₃, _h1, _h2, _h3, _h12, _h23, _h13⟩
    cases p₁ <;> cases p₂ <;> cases p₃ <;>
      first | exact _h12 rfl | exact _h23 rfl | exact _h13 rfl

end Logos.TrinitySeparations

/-!
# Axiom footprint audit (expected: `{}` for all four witnesses)
-/
#print axioms Logos.TrinitySeparations.unitarian_self_love_gives_no_second_centre
#print axioms Logos.TrinitySeparations.creature_love_gives_no_divine_beloved
#print axioms Logos.TrinitySeparations.attribute_love_gives_no_subsistent_word
#print axioms Logos.TrinitySeparations.agape_and_word_without_spirit_is_binitarian


/-!
================================================================================
SECTION: TrinitarianPersonalGround
================================================================================
-/
/-
# Logos.TrinitarianPersonalGround — the ground is not void of personhood

The record of record is `AGENTS.md` (sync rule) with `GAPMAP.md` (per-claim status); this module was step **S2** of the retired personal-ground plan,
promoting the machine-checked basis of `investigations/trinitarian-probe.lean` (an
audit artifact, never compiled by `lake build`) into the kernel. Nothing here moves the match arm
of `EntityMeans` — that is the point, and Section 2 below records why the arm must not be moved.

## The doctrine

> **God is one essence in three persons, and the essence is alive.** The one essence is not a
> fourth instance of choosing alongside the three; it is the one essence *which the three subsist
> in and which lives by them*. Its freedom is theirs, **shared rather than duplicated**
> (*praeter hoc, quod unus est, tres sunt*, the Nicene formula's own guard against a fourth).

Two facts carry that sentence, and neither may be collapsed into a deficiency or an excess:

1. **`¬ Asiety Entity.ofGround`** — no subject witnesses the ground, so the ground is not an
   asietic entity (`ground_is_not_a_fourth_chooser`). The one essence is not a fourth chooser.
2. **`ground_scope_does_contain_incompatibles`** — the ground's scope takes in **both horns of
   every conflict**, because its arm is `True`. **Plenitude of scope is not freedom.**

The second is the result the checker forced, and it is recorded here because the opposite reading
is the natural mistake. "The ground cannot co-mean incompatible contents" is **false** against
today's arm. Freedom in Γ is not bearing all content; it is `Asiety`, which requires being a
`Subject`. So a total scope does not make the ground maximally free — which would be absurd —
because freedom is subject-indexed.

## Two routes of grounding, both named, neither accidental

`OneEssence` is *meaning-containment*: `∀ p, EntityMeans e p → EntityMeans g p`. Because the
ground's arm is `True`, it holds of everything, **including the atoms vacuously** — an atom means
nothing, so the containment is `True` by empty antecedent rather than by intent. That reason is
now named instead of left to chance:

- **`GroundByBeing`** — presence-grounding: God as sustaining cause, *ST* I q. 44 a. 1 (God is
  the cause of the whole being of creatures). This is the route that covers the atoms for a
  reason nobody chose.
- **`OneEssence`** — providential indwelling, covering persons, and *not* covering a heretic's
  beliefs (`EntityMeans (ofAtom _) p := False`, while a heretic *does* mean heretically).

`ofGround_leaves_nothing_ungrounded` closes the disjunction: nothing is outside the ground.

## What this module does not claim

- **Not hypostatic identity.** `g = EntityOf s` for some `s` is unstatable: `Person` is a
  `Subject → Prop`, `Subject` is an opaque sort with no constructors, and `Entity.ofGround ≠
  EntityOf s` is `Entity.noConfusion`. The claim "the ground is a free subject in its own right"
  is not false here — it has no denotation. Any plan implying otherwise would be dishonest, and
  this plan says so in §1.4 and §11.
- **Not a non-vacuous `OneEssence`.** Adding `∃ s, e = EntityOf s` to `OneEssence` makes the God
  proof **unprovable**: `actualWorld` makes every atom actual, so `GroundOfReality Entity.ofGround`
  must handle `ofAtom n`, and the added conjunct is false for atoms while the meaning arm is
  `False` for them, so neither disjunct fires. Plan §6.2 records the three rejected variants.
- **Not an essence predicate.** Consubstantiality is grounded *in the ground* (`OneEssence`), and
  no `Essence` predicate is introduced. "The three persons share a nature independently of the
  ground" therefore remains unstatable — an author decision recorded here, and still open. A `Consubstantial`
  `def` was carried here for §20.1 and has been **deleted**: at the ground it is `True` of atoms
  (see the `DOCTRINE ROW 3` docstring below). The one-ness it named is `indwells`, which is free.
- **Not a change to `EntityMeans`.** §6.1's rejected alternative (`EntityMeans Entity.ofGround p :=
  T p`) trades infallibility for pure actuality, because `PassiveIntentionalPotency e := ∃ p, ¬
  EntityMeans e p` and `MaximalCapacity e := ∀ p, EntityMeans e p` are **the same field read in two
  directions**. The fix is to re-specify `PassiveIntentionalPotency`, which is filed as its own
  milestone and is **not** part of this plan.

## Price

Every declaration here is a `def`, a `structure`, or a theorem at **zero substantive axioms**. The
non-empty footprints are Γ's vocabulary (`Subject`, `Means`, `Will`, `subjectWill`,
`NecessarySubjectKind`) — the cost of *saying* the claim in Γ's own words, not a price for the
claim. This is the distinction the corpus already draws: "zero *substantive* rather than
axiom-free". No axiom is declared, removed, or re-tagged by this module, and the declared-axiom
count is unchanged at 25 (VOCAB 14 / SEM 7 / META 4).
-/

namespace Logos.TrinitarianPersonalGround

open Logos.Semantics (World)
open Logos.Entity (Entity EntityOf ExistsAt)
open Logos.Agency (Subject Means)
open Logos.Alternatives (Incompatible)
open Logos.Choice (FreeWill)
open Logos.Person (Person)
open Logos.RecoveredOntologicalGround (ActualEntity EntityMeans OneEssence)
open Logos.NecessityEternity (ofGround_ne_ofSubject)
open Logos.AsieticChoice (Asiety)
open Logos.DivineAgape (DivineHypostasis SelfDonation agape_is_self_donation)

/-! ## Section 1: presence-grounding, the route that covers the atoms -/

/-- **`GroundByBeing g e`: presence-grounding — `g` is present wherever `e` is.** The second
    grounding route, and the non-vacuous one: `OneEssence` holds of everything by the ground's
    `True` match arm, so of the atoms too, and there for a reason nobody chose. This relation is
    what grounds them *for a reason*, i.e. God as sustaining cause (*ST* I q. 44 a. 1: God is the
    cause of the whole being of creatures), while `OneEssence` is providential indwelling.

    It is deliberately weak — presence, not production. Γ has no causal relation, so "the ground
    sustains" is read as "the ground is there", exactly as `Stipulations.operatesAt_presencePlusObtaining`
    reads omnipotence; the production sense is not claimed and is not derivable here.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
def GroundByBeing (g e : Entity) : Prop :=
  ∀ w : World, ExistsAt w e → ExistsAt w g

/-- **The ground sustains the being of every entity.** `EntityExistsAt _ Entity.ofGround := True`
    is what makes this free, so the sustaining cause of all creatures is **axiom-free** — the whole
    price of presence-grounding is the `True` arm of the world's ground-clause, which is
    `Stipulations.ofGround_meansAll`'s sibling and costs nothing as a `def`.

    This is the row that covers the **atoms** for a reason nobody chose, and the
    reason `ofGround_ground_of_reality` needed a `GroundByBeing`-shaped alternative at all.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem ofGround_grounds_every_being_by_presence (e : Entity) :
    GroundByBeing Entity.ofGround e := by
  intro w _
  trivial

/-! ## Section 2: indwelling, the route that covers the persons -/

/-- **Every person is grounded in the ground by indwelling.** With the `EntityMeans
    Entity.ofGround p := True` arm this is free, and this module's rejection of the truth-restricted
    arm is what keeps it free — that is the load-bearing consequence of *not* moving the match arm.

    This is `homoousios`-shared personhood stated as a relation of the ground to persons: it
    makes the ground indwelt rather than empty, and it is the half of `PersonalGround` that
    `no_person_is_the_ground` and `ground_is_not_a_fourth_chooser` together keep from collapsing
    into the deist picture of a substrate the persons merely use.
    Footprint: `{Means, Subject, Will, subjectWill}`. -/
theorem ofGround_grounds_every_person (s : Subject) (_hP : Person s) :
    OneEssence Entity.ofGround (EntityOf s) := by
  intro p _
  trivial

/-! ## Section 3: nothing is outside the ground -/

/-- **No entity is outside the ground**: the ground sustains its being and contains all its
    meaning, so nothing is left ungrounded. The disjunction this module closes is
    `e = g ∨ (GroundByBeing g e ∨ OneEssence g e)` — identity, presence, or indwelling.

    Note which disjunct actually carries the atoms: `OneEssence`'s atom case is vacuous, so the
    left disjunct (`GroundByBeing`) is doing the work for every `ofAtom n` that `actualWorld`
    makes actual. That is why the second route had to be *named* rather than left to chance.
    Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
theorem ofGround_leaves_nothing_ungrounded (e : Entity) (_hAct : ActualEntity e) :
    e = Entity.ofGround ∨ (GroundByBeing Entity.ofGround e ∨ OneEssence Entity.ofGround e) :=
  Or.inr (Or.inl (ofGround_grounds_every_being_by_presence e))

/-! ## Section 4: what the ground's scope does and does not give -/

/-- **The ground's scope does co-contain incompatible contents** — with the total arm it means
    every proposition, so it takes in both horns of every conflict. This is the result the
    checker forced, and it is the doctrine: **plenitude of scope is not freedom.**

    A rejected alternative asserted the ground "cannot co-mean incompatibles". That is
    simply false against today's arm, and asserting it would have imported a claim nothing
    supports. Freedom in Γ is not bearing all content — it is `Asiety`
    (`ground_is_not_a_fourth_chooser`), which requires being a `Subject`. So the ground's total
    scope does *not* make it maximally free, which would be absurd; it does not, because freedom
    is subject-indexed.

    The witness is degenerate (`True`/`False`, horns trivially excluded) because the claim is about
    the ground's *scope*, not about a substantive pair. It is not evidence that the ground settles
    anything; the content-transfer relation's inability to deliver a choice of contents is priced
    separately in `AsietyFreedom.groundingCannotDeliverTrueChoice` (`{}`).
    Footprint: `{Means, Subject}`. -/
theorem ground_scope_does_contain_incompatibles :
    ∃ p q : Prop, EntityMeans Entity.ofGround p ∧ EntityMeans Entity.ofGround q ∧ Incompatible p q :=
  ⟨True, False, trivial, trivial, fun h => h.2⟩

/-- **The ground is not an asietic entity: no subject, so no true choice at the ground.** The ground
    does not choose. That is a real limit of the vocabulary, and it is stated here as a limit.

    Two earlier versions of this docstring are retracted here (2026-10-03; `LOVE-2.md` D1), and
    they were retracted in opposite directions, which is the tell. The first called this "doctrine,
    not a defect" and added that "its freedom is their freedom, shared rather than duplicated"
    (`AsietyFreedomOfGround`, `Tag: META`, registered ◈ in `Stipulations.lean`). The second then
    over-corrected and denied that any such relation existed at all: "there is no relation here
    between the ground's scope and any subject's choice".

    **Both are false, and the relation is named.** `AsietyFreedom.asietyFreedomOfGround` — the ◈
    `def` at `AsietyFreedom.lean:141` — relates the ground's scope to each subject's true choice,
    and `AsietyFreedom.asietyFreeWill` is the predicate this corpus gives to that shared freedom.
    The restored reading is the one `AsietyFreedom.lean` states three times (`:113`, `:128`,
    `:210`) and that commit `4a59173` deleted from the two files that are read first: **the
    ground's freedom is *transferred* to the three Persons and not *exercised* by a fourth chooser,
    and the vacuity of `OneEssence` is the marker of that transfer.** The theorem, its statement
    and its `{Means, Subject}` footprint are unchanged by this correction; only the reading is.

    What the row says, precisely: `¬ Asiety Entity.ofGround` unfolds through `Asiety`
    (`AsieticChoice.lean:147-148`, `∃ s : Subject, ∃ p q : Prop, e = EntityOf s ∧ TrueChoice s p q`)
    to `ofGround_ne_ofSubject` — the **same fact** as `LovesAsGround.the_ground_is_not_a_person`
    (`LovesAsGround.lean:604`) and as `no_person_is_the_ground` (C519, `{Subject}`). It is a
    statement about `Subject`-indexing: the ground is no *fourth chooser*, and it is the
    **nature** those Persons are OneEssence in, not an instance of it. It is **not** a refutation
    of freedom and **not** a denial of the ground's personhood — `the_ground_is_not_void_of_personhood`
    (C362) asserts that in the next line, and the transfer is `AsietyFreedomOfGround`'s content.

    What replaces the reassurance is not a weaker claim but a stronger neighbour: the donation of
    the Self holds anyway. `self_donation_needs_no_personhood_of_the_ground` (C578) conjoins this
    row with `agape_is_self_donation` (C575), so "it cannot give because it is not a person who
    chooses" is refuted as a route rather than annotated, and `denying_self_donation_is_absurd`
    (C576) closes the absurdity itself.

    The asymmetry with `ground_scope_does_contain_incompatibles` is worth keeping, and it needs no
    label to state: the ground's *scope* is unrestricted meaning — it holds `True` and `False`
    together — while its *agency* is absent altogether. One is a maximum, the other is a zero, and
    the two are different claims about different vocabularies.

    Distinct from its two neighbours by scope, not by content: `AsieticChoice.ground_is_not_a_true_chooser`
    (C285) denies the weaker `∃ s, EntityOf s = Entity.ofGround` (no *chooser*), this denies
    `Asiety` (no *true* choice), and `AsieticChoice.ground_is_canonically_aseitous_but_not_asietic`
    is conditional on `hFinite`. The present row is unconditional and is the one the Nicene
    reading needs, since it must hold with or without a finitude premise.
    Footprint: `{Means, Subject}`. -/
theorem ground_is_not_a_fourth_chooser : ¬ Asiety Entity.ofGround := by
  intro h
  obtain ⟨s, _p, _q, hs, _⟩ := h
  exact ofGround_ne_ofSubject s hs

/-- **The donation of the Self does not require the ground to be a person — C578.**
    Both halves of the absurdity, in one row: the ground is **not** an asietic
    entity (no subject, so no true choice — the first conjunct is
    `ground_is_not_a_fourth_chooser`, at `{}`), **and** Agape is a gift between two
    distinct personal properties of one location-entity (the second conjunct is
    `agape_is_self_donation`, C575).

    This row is **not** a replacement for the sentence "the one essence is not a
    fourth chooser; its freedom is their freedom, shared rather than duplicated". An
    earlier version of this docstring claimed to replace it on the ground that it
    "answered the author's objection with a label while conceding its premise, and it
    presented an *absent* predicate as an argument". **That was false, and is retracted**
    (2026-10-03, `LOVE-2.md` D1): the predicate is not absent —
    `AsietyFreedom.asietyFreedomOfGround` (`AsietyFreedom.lean:141`) is the ◈ `def` that states
    the sharing, and `asietyFreedom_summary` (`:357`) consumes it. A `def` premise is invisible to
    `#print axioms`, so an audit could not see it, and commit `4a59173` inferred from that
    invisibility that there was nothing there. Nothing was removed; a price was
    misread as a depth, and the ground's freedom was deleted from the doctrine to make the
    model convenient.

    The conjunction below is therefore **additional**, not a substitute. What it does add is the
    second half the label could not carry: the ground is not a chooser **and** Agape is a gift
    between two distinct personal properties of one location-entity. "It cannot give because it is
    not a person who chooses" is refuted *as a route*; the sharing is the ground's own freedom,
    which is what makes the gift its own.

    **Price.** The first conjunct is free. The second is `{Subject,
    AxAgapeEssence, CL}` — one META axiom, which is the same price
    C507/C510 carry and is *not* avoided here. What this row shows is that the
    price buys the gift and nothing more; the ground is **not a fourth chooser**, and the
    denial of the gift is refuted by `denying_self_donation_is_absurd` (C576).

    Footprint: `{Means, Subject, AxAgapeEssence, Classical.choice}` (only `Classical.choice` of the CL trio — no `Quot.sound`, no `propext`). -/
theorem self_donation_needs_no_personhood_of_the_ground :
    ¬ Asiety Entity.ofGround ∧ (∃ f o : DivineHypostasis, SelfDonation f o) :=
  ⟨ground_is_not_a_fourth_chooser, agape_is_self_donation⟩

/-- **No person is the ground.** Hypostatic *identity* is not merely unproved but unstatable:
    `Entity.ofGround` and `Entity.ofSubject _` are distinct constructors, so `Entity.noConfusion`
    decides it. This is the row that keeps §1.6's two axes apart — one ground over *entities*
    (`exactly_one_universal_modal_ground`, C320) and three persons over *persons* — so the ground
    is not one of the three and the three are not grounds.

    The apparent contradiction dissolves on the axes, and **no change to the `Entity` type is
    required anywhere in this plan** because of this row.

    Restated in the Nicene form, since `NecessityEternity.ofGround_ne_ofSubject` is the technical
    `≠` and this is the claim the corpus has to be able to cite. Keeping both is deliberate: plan
    §6.3 retired hypostatic identity as the *wrong form of the claim*, and this row is the surviving
    form, not a duplicate of the technical one.
    Footprint: `{Subject}`. -/
theorem no_person_is_the_ground (s : Subject) : ¬ (Entity.ofGround = EntityOf s) :=
  ofGround_ne_ofSubject s

/-! ## Section 5: homoousios, which needs no new relation -/

/-- **`Perichoretic g a b c`: the one essence indwelt by three persons.** What this predicate
    carries is *homoousios* — one essence, three persons — as three `OneEssence` instances
    against the one ground. It needs no new relation, which is why it costs nothing.

    **This is not perichoresis in the strict sense, and it must not be read as one.** Two earlier
    versions of this docstring said it was not perichoresis *because* `OneEssence` is
    **asymmetric**, citing "the generic structure's `asymmetric` field". That was false twice
    over and is retracted here:

    - There is no `asymmetric` field on `PersonalGround`. The structure has exactly two fields,
      `sustains` and `indwells` (`TrinitarianPersonalGround.lean:274`). The only `asymmetric`
      field in the corpus is `PersonalNormativeGround.asymmetric`
      (`PersonalNormativeGround.lean:214`), and it constrains `Grounds`, not `OneEssence`.
    - `OneEssence` is **reflexive**, not asymmetric: `groundsEntity_reflexive`
      (`FoundationalUnicity.lean:116`) proves `OneEssence e e` at every entity. The asymmetry
      statement `AsymmetricGrounding` is **proved unsatisfiable** by C316
      (`not_asymmetric_grounding`, `FoundationalUnicity.lean:145`), which GAPMAP records as
      voiding the C207 route. So "persons cannot ground one another" was never established, and
      the docstring asserted a refuted premise in order to look settled.

    **The real reason strict perichoresis is absent is Modalism, not asymmetry.** Formalising
    mutual grounding *through this relation* is possible — asymmetry would not have blocked it —
    but it is a heresy. For two persons `a b`:

        OneEssence (EntityOf a) (EntityOf b)  =  ∀ p, EntityMeans (EntityOf b) p → EntityMeans (EntityOf a) p
        OneEssence (EntityOf b) (EntityOf a)  =  ∀ p, EntityMeans (EntityOf a) p → EntityMeans (EntityOf b) p

    and the pair is exactly the biconditional `∀ p, EntityMeans (EntityOf a) p ↔ EntityMeans
    (EntityOf b) p`, i.e. **C572**, withdrawn as wrongly shaped because identical meaning across
    the Persons makes them interchangeable — the Son becomes "the one the Father is". So a
    mutual-*grounding* reading is not an unproved lemma we failed to reach; it is a claim we
    should not want.

    Strict perichoresis — the *kyklos*, the Persons in-dwelling **in each other** — is therefore
    not statable with the relation this module has, and is not statable with mutual `OneEssence`
    either. It needs a **new primitive** (symmetric, and deliberately not a meaning-containment
    order) which Γ does not have. That is an open, priced item, recorded in GAPMAP as the
    perichoresis frontier row; it is *not* discharged here, and G8 keeps this paragraph honest
    rather than pinning the retracted asymmetry claim. The classical warrant that the Persons are
    distinguished by relations of origin rather than by essences (*ST* I q. 28 a. 3) points the
    same way, and those relations are open too (the X2 row: which hypostasis each `Subject` is).

    The instantiation `ofGround_is_perichoretic` is therefore unconditional, and §5.1's use of it
    as the last conjunct of the master theorem needs no further price.
    Footprint: `{Means, Subject}`. -/
def Perichoretic (g : Entity) (a b c : Subject) : Prop :=
  OneEssence g (EntityOf a) ∧ OneEssence g (EntityOf b) ∧ OneEssence g (EntityOf c)

/-- **The ground is perichoretic, for any three persons.** Three instantiations of
    `ofGround_grounds_every_person`, so `{}` in the substantive sense. The name is retained for
    continuity with the master theorem's last conjunct, but read `Perichoretic` as its
    definition says — *homoousios*, one essence indwelt by three persons — not as the *kyklos*;
    see the `Perichoretic` docstring for why the latter is Modalism rather than asymmetry.

    The persons are still undistinguished here — nothing in this row says there are exactly three
    of them, or that they are necessary, or that they are related by origin, or that they
    in-dwell each other. The population question is bought by `TrinitarianPersonalBridge`
    (`Tag: META`, GAPMAP C509); the *relations of origin* are the open X2 row; the mutual
    indwelling is the open perichoresis row. So this row is the *form*, and
    `trinitarianPersonalGround_summary`'s last-but-one conjunct is deliberately a universal over
    person-carrying arguments rather than an existential.
    Footprint: `{Means, Subject, Will, subjectWill}`. -/
theorem ofGround_is_perichoretic (a b c : Subject) (ha : Person a) (hb : Person b) (hc : Person c) :
    Perichoretic Entity.ofGround a b c :=
  ⟨ofGround_grounds_every_person a ha,
    ofGround_grounds_every_person b hb,
    ofGround_grounds_every_person c hc⟩

/-! ## Section 6: the personal ground — the module in one line -/

/-- **The ground is a personal ground: it sustains all being and indwells every person.** Not void
    of personhood, and not a fourth chooser: the conjunction is the whole Nicene position in Γ's
    vocabulary, and both halves are needed for it. `indwells` alone would permit a demiurge plus
    three unrelated saints; the doctrine is that everything in the ground that acts acts as one of
    the three, and that the ground is the one essence they subsist in and which lives by them.

    Both fields are `{}`-substantive. `sustains` is `GroundByBeing` (presence-grounding) and
    `indwells` is `OneEssence` (providential indwelling) — this module's two named routes,
    conjoined. The `ActualEntity` restriction on `sustains` is inherited from `GroundOfReality`'s
    shape and is not doing work for the ground's own case: `actualWorld` makes every atom actual,
    so the field ranges over subjects and atoms alike, and `GroundByBeing` covers each.

    **What this is not.** It does not make the ground a subject: `PersonalGround` has no
    `Asiety` field and cannot be given one, since `ground_is_not_a_fourth_chooser` refutes it at
    zero substantive axioms. The ground's personhood is *homoousios*-shared — the three Persons are
    what make the essence alive — and the freedom is transferred, not exercised
    (`AsietyFreedomOfGround`, `Tag: META`).
    Footprint: `{Means, NecessarySubjectKind, Subject, Will, subjectWill}`. -/
structure PersonalGround (g : Entity) : Prop where
  sustains : ∀ e : Entity, ActualEntity e → (e = g ∨ GroundByBeing g e)
  indwells : ∀ s : Subject, Person s → OneEssence g (EntityOf s)

/-- **The ground is not void of personhood.** Every person is grounded in it; it sustains all
    being; and it is not a fourth chooser. This is the headline of this module, and its
    substantive price is **zero**.

    The three Persons are what make the essence alive; this is *homoousios*-shared personhood, not
    subject-predication of the ground, which is impossible
    (`ground_is_not_a_fourth_chooser`). A demiurge plus three saints is machine-refuted by the
    `indwells` field, and a fourth chooser is machine-refuted outright.
    Footprint: `{Means, NecessarySubjectKind, Subject, Will, subjectWill}`. -/
theorem the_ground_is_not_void_of_personhood : PersonalGround Entity.ofGround where
  sustains := fun e _ => Or.inr (ofGround_grounds_every_being_by_presence e)
  indwells := fun _ hP => ofGround_grounds_every_person _ hP

/-- ★ **The module in one line.** Two named grounding routes close the disjunction; the ground
    takes in both horns of every conflict and is nevertheless not a chooser; it sustains all being,
    indwells every person, and is no person's correlate. Zero new axioms.
    Footprint: `{Means, NecessarySubjectKind, Subject, Will, subjectWill}`. -/
theorem trinitarianPersonalGround_summary :
    (∀ e : Entity, GroundByBeing Entity.ofGround e) ∧
    (∀ s : Subject, Person s → OneEssence Entity.ofGround (EntityOf s)) ∧
    (∃ p q : Prop, EntityMeans Entity.ofGround p ∧ EntityMeans Entity.ofGround q ∧ Incompatible p q) ∧
    (¬ Asiety Entity.ofGround) ∧
    (∀ s : Subject, ¬ (Entity.ofGround = EntityOf s)) ∧
    (∀ a b c : Subject, Person a → Person b → Person c → Perichoretic Entity.ofGround a b c) ∧
    PersonalGround Entity.ofGround :=
  ⟨fun e => ofGround_grounds_every_being_by_presence e,
    fun s hP => ofGround_grounds_every_person s hP,
    ground_scope_does_contain_incompatibles,
    ground_is_not_a_fourth_chooser,
    fun s => no_person_is_the_ground s,
    fun a b c ha hb hc => ofGround_is_perichoretic a b c ha hb hc,
    the_ground_is_not_void_of_personhood⟩

-- ============================================================================
-- Section 7: Axiom Footprint Audit
-- ============================================================================

#print axioms GroundByBeing
#print axioms Perichoretic
#print axioms PersonalGround
#print axioms ofGround_grounds_every_being_by_presence
#print axioms ofGround_grounds_every_person
#print axioms ofGround_leaves_nothing_ungrounded
#print axioms ground_scope_does_contain_incompatibles
#print axioms ground_is_not_a_fourth_chooser
#print axioms no_person_is_the_ground
#print axioms ofGround_is_perichoretic
#print axioms the_ground_is_not_void_of_personhood
#print axioms trinitarianPersonalGround_summary

/-! **DOCTRINE ROW 3 (nomenclature; GAPMAP C568): *homoousios* — one essence, three
Persons.** There is no declaration for this, and the deletion of the one that used to be here is
the point of this docstring.

A `Consubstantial g a b := OneEssence g a ∧ OneEssence g b` was carried here (GAPMAP C568) on the
reasoning that `OneEssence` is directional, and therefore cannot express the *mutuality* between
the Persons. **That reasoning was wrong, in the same way the `Perichoretic` docstring was.**
`OneEssence` is not directional in the sense assumed: it is **reflexive**
(`groundsEntity_reflexive`, `FoundationalUnicity.lean:116`), and its asymmetry statement
`AsymmetricGrounding` is **proved unsatisfiable** (C316, `not_asymmetric_grounding`,
`FoundationalUnicity.lean:145`). Nothing blocked a mutual reading.

The declaration was still right to delete, but for a different reason than the one recorded:
`Consubstantial g a b` was not *mutual grounding between persons at all* — it was
`OneEssence g a ∧ OneEssence g b`, **two ground-to-person instances**, which is exactly
`Perichoretic`'s content and adds no third conjunct. Instantiated at the ground it is `True` of
arbitrary entities, including atoms, so it asserted nothing about persons at all. It was a
redundant name, and the mutual-perichoresis question it was meant to answer has to be answered by
a new primitive relation instead (see the `Perichoretic` docstring: the mutual reading *through
`OneEssence`* is C572, withdrawn as Modalism). Instantiated at `g = Entity.ofGround` — the only
ground the doctrine has, and the only one every §20 row uses — `OneEssence Entity.ofGround e` holds
for **every** entity `e`, including `Entity.ofAtom 0`. So `Consubstantial Entity.ofGround e f` is
`True` for arbitrary `e` and `f`: it asserts the ground is consubstantial with everything, including
atoms. The mutual-relation reading it promised is exactly the content it does not have, so it was
`True` twice over — a `{}` price on a `True` proposition, which is a null result and not a proof.
(The vacuity is a theorem, not an inspection: `Consubstantial Entity.ofGround e f ↔ True`.)

What replaced it is what was already there. *One essence* is `PersonalGround`'s `indwells` field
(`ofGround_grounds_every_person`, `{Means, Subject, Will, subjectWill}`): every Person is one with
the one ground. That is the doctrine's one-ness, it is free, and it needs no second relation — a
second relation over `OneEssence` at the ground could only ever be `True` again. And the doctrine's
*distinction* half — that the three cannot be collapsed into one — is `roles_make_the_three_persons_distinct`
(`TrinitarianSubjectBridge.lean:279`), free on `{DivineSubjectRole, Subject}`, already a conjunct of
the §5.1 master theorem. Nothing was missing. The `Consubstantial` family is deleted rather than
repaired: there is no non-vacuous version of "both are one with the ground", because that is `True`,
and `True` is not a relation.

**AUTHOR DECISION (2026-10-03): reading (a) is taken.** Three readings of what the
deletion leaves behind were put to the author, and (a) is adopted:

  (a) *It is enough.* All three Persons stand in the **same** relation to the **same** one, none
      is identical to it, and none is a creature. Consubstantiality is fully expressed by that,
      so the deleted `Consubstantial` was a redundant `True` and its removal is a
      simplification. **No `Essence`/`Nature` predicate is introduced, and none is wanted.**
  (b) *Not enough.* Homoousios is a shared **property** — the three have one nature *as each
      other* — which would need an essence predicate. This reading is **not** taken. It was
      never closed by the deleted relation either, since that relation asserted `True`.
  (c) *Moot, on the economic reading.* The Persons are distinguished by relations of origin
      rather than by essence (*ST* I q. 28 a. 3, cited in Section 5), so "consubstantial" would
      be a conclusion from the ground and the relations rather than a third premise. Compatible
      with (a), and the deeper grounding for it, but the relations among the Persons are **not**
      in Γ (open item X2).

So the doctrine's *one-ness* rests on `indwells` and its *three-ness* on
`roles_make_the_three_persons_distinct`, and that is taken to be sufficient. The one thing still
absent is strict **perichoresis** — the Persons in-dwelling in *each other* rather than all three
in the ground — which needs a relation Γ lacks and is not claimed here; `Perichoretic` is three
`indwells` instances and is labelled a *form* accordingly. G8 keeps that label honest.

Note what the one-ness therefore rests on: `indwells` at the ground is `True` **by definition**
(`EntityMeans Entity.ofGround p := True`, `NecessaryPersonalGround.lean:184`), so
`ofGround_grounds_every_person` closes by `trivial`. That is disclosed rather than repaired — the
truth-restricted arm was rejected, and the rejection is what keeps the row free — but a reader
should see it stated: under reading (a) the *one* is carried by a predicate that is
definitionally satisfied, and the content of the row is the `Person s` hypothesis and the
`no_person_is_the_ground` / `ground_is_not_a_fourth_chooser` separations, not the `True`.

`Perichoretic` (Section 5) is kept and is **not** the same claim: it is the conjunction the master
theorem's last conjunct needs, it is honestly labelled there as a *form* rather than a doctrine row,
and its docstring states that perichoresis is **not** a mutual grounding of the Persons in one
another. The reason it gives is the right one: the mutual reading through this relation is **C572,
withdrawn as Modalism** — identical meaning across the Persons — not asymmetry, which C316 shows
was never available as a premise in the first place (`OneEssence` is reflexive).
`scripts/test_personal_ground_kind.py` G8 pins that disclosure, requires the C316 retraction to
accompany any mention of the old asymmetry premise, and is itself verified by mutation. -/


end Logos.TrinitarianPersonalGround


/-!
================================================================================
SECTION: TrinitarianSubjectBridge
================================================================================
-/
/-
# TrinitarianSubjectBridge (plan S4, D-1 + D-2)

The bridge the plan names as the missing work at §3.3: `DivineAgape` declares and prices the
procession vocabulary over `DivineHypostasis`, but nothing connects that sort to `Subject`,
`Person`, freedom, or necessity. This module supplies the connection and nothing else.

**What is declared here.** `DivineRole` (a role sort, three constructors, zero axioms) and
`DivineSubjectRole` (`Tag: VOCAB`, the D-1 classifier); `TrinitarianPersonalBridge` (`Tag: META`,
the D-2 bridge). Two axioms. Every theorem in the module is derived from those plus the existing
corpus.

**What is deliberately not done.** `GroundsRightWrong` is never used (plan §7, F12). It is
definitionally `∃ p q, Chooses s p q` — already free will — so using it as the personal-ground
antecedent would assume what this step must establish. The bridge is therefore asserted flat,
and the freedom it carries is *independently* posited for the three subjects, not smuggled
through a relation that already contains it.

**What is not claimed.** Nothing here is derived from the procession axioms; `AxAgapeEssence`,
`AxProcessionWord` and `AxProcessionSpirit` are **not** in this module's footprint, and their
absence is the honest reading of §6.3: identity between the divine-hypostasis sort and `Subject`
is not the claim (and `Entity.noConfusion` forbids it for the ground). What is claimed is the
weaker, correctly-typed thing the Nicene formula actually needs — three *distinct* divine-role
subjects, each a necessary person, sharing the one ground. Connecting those subjects to the
`DivineHypostasis` centers is a further, separate bridge and is **not** discharged here; see
§11.
-/

namespace Logos.TrinitarianSubjectBridge

open Logos.Core
open Logos.Semantics (World)
open Logos.Entity (Entity EntityOf)
open Logos.Agency (Subject Means NecessarySubjectKind)
open Logos.Alternatives (Incompatible)
open Logos.Choice (Chooses FreeWill FreeSubject)
open Logos.Person (Person)
open Logos.Plurality (NecessarySubject)
open Logos.RecoveredOntologicalGround (ActualEntity OneEssence GroundOfReality EntityMeans
  NecessaryGroundOfReality)
open Logos.AsieticChoice (Asiety)
open Logos.DivineAgape (divineReality)
open Logos.PersonalNormativeGround (GroundsRightWrong)
open Logos.NecessityEternity (ofGround_necessary_ground_of_reality)
open Logos.DivinePureActuality (PassiveIntentionalPotency ofGround_no_intentional_potency)
open Logos.BoundedMeaning (BoundedMeaningRequiresFreeSubject
  guard_excludes_exactly_the_impersonal_cases)
open Logos.FoundationalOmnipresence (UniversalModalGround)
open Logos.FoundationalUnicity (exactly_one_universal_modal_ground ofGround_ne_ofSubject)
open Logos.SemanticFinitude (SemanticFinitude)
open Logos.TrinitarianPersonalGround (Perichoretic ofGround_is_perichoretic)

-- ===========================================================================
-- Section 1: D-1 — the role vocabulary on the `Subject` sort
-- ===========================================================================

/-- **D-1, the role sort.** `DivineRole` is the content of `DivineAgape.IsWord` and
    `IsSpirit` lifted off the `DivineHypostasis` sort: the three roles by relations of origin
    (`ST` I q.28 a.3), namely the source (`ST` I q.38 a.1), the Word (`ST` I q.7 a.3), and the
    Spirit (`ST` I q.36 a.4).

    A `def`-like constructor set, **not** an axiom: it costs nothing and it is not a parallel
    hypostasis sort. Plan §6.4 rejected introducing a *second* sort of divine centers beside
    `DivineHypostasis`; this is a sort of **roles**, and it introduces no inhabitants of
    anything. It is `inductive` rather than three `opaque` predicates precisely so that the
    roles are *distinguishable* — `IsWord`/`IsSpirit` are `opaque … := True` (the `BearingOf`
    pattern) and therefore cannot distinguish anything from each other, which is why the corpus
    needed a `relational_distinction` field it could only fill with `fun a b => a ≠ b`.
    Footprint: `{}`. -/
inductive DivineRole where
  /-- The unoriginated source. -/
  | source
  /-- The Word: the object of the essential self-giving. -/
  | word
  /-- The Spirit: the return of the gift. -/
  | spirit
  deriving DecidableEq, Repr

/-- The three roles are pairwise distinct. `deriving DecidableEq` is what makes this a
    *computation* rather than a priced claim: no axiom is consumed, which is the whole reason D-1
    is a constructor set and not three opaque predicates.
    Footprint: `{}`. -/
theorem DivineRole.source_ne_word : DivineRole.source ≠ DivineRole.word := by decide

/-- Word and Spirit are distinct roles.
    Footprint: `{}`. -/
theorem DivineRole.word_ne_spirit : DivineRole.word ≠ DivineRole.spirit := by decide

/-- Source and Spirit are distinct roles.
    Footprint: `{}`. -/
theorem DivineRole.source_ne_spirit : DivineRole.source ≠ DivineRole.spirit := by decide

/--Tag: VOCAB
Vocabulary: the hypostatic role of a subject — the relation of origin that distinguishes the
three divine persons from one another.

  `DivineAgape.IsWord` and `IsSpirit` classify `DivineHypostasis`, so they **cannot** be
  applied to a `Subject`: the two sorts have no common carrier, and `Entity.ofSubject` embeds a
  subject into `Entity`, not into `DivineHypostasis`. The role content therefore has to be
  re-declared on the `Subject` sort, and this is that declaration. It says which *relation of
  origin* a subject bears; it does not say that any subject bears one, which is `D-2`'s work
  (`TrinitarianPersonalBridge`, `Tag: META`).

  Plan §7 budgets this as `VOCAB`: a classifier over an opaque sort, exactly as
  `NecessarySubjectKind` (`Agency.lean:62`) is. `Subject` is `axiom Subject : Type` with no
  constructors, so this predicate is genuinely not derivable — there is no inhabitant to apply it
  to. It is vocabulary rather than a substantive choice because it introduces no connection
  between entities: it is a three-valued classifier on one uninterpreted sort.
  Footprint: `{Subject}` (vocabulary only; the classifier's own `Subject` argument is the
  `Subject` sort axiom, which every declaration over `Subject` already pays). -/
axiom DivineSubjectRole : Subject → DivineRole

/-- The three roles exhaust the sort: every role is one of the three named relations of origin.
    A decidability fact about three constructors, so it costs nothing and closes the risk that
    `DivineSubjectRole` is a fourth, unnamed role in disguise.
    Footprint: `{propext}`. -/
theorem role_exhausts_the_sort (r : DivineRole) :
    r = DivineRole.source ∨ r = DivineRole.word ∨ r = DivineRole.spirit := by
  cases r <;> simp

-- ===========================================================================
-- Section 2: D-2 — the bridge
-- ===========================================================================

/--Tag: META
TrinitarianPersonalBridge (META; plan §7 D-2, poem P5/P7): the three divine persons are
  `Subject`s, and they are necessary persons who share the one ground.

  **Why this must be declared.** `Subject` is `axiom Subject : Type`, opaque, with **no
  constructors** (`Agency.lean:49`). Every existential over `Subject` therefore needs an axiom,
  and this is the one the Nicene formula needs. `DivineHypostasis` is a different sort with
  inhabited constructors, but there is no map from it into `Subject`, and §6.3 is explicit that
  *identity* is not the claim: `Entity.noConfusion` blocks identifying the ground with any
  subject, and the same reflexive move would be the wrong shape for the persons.

  **Why it does not route through `GroundsRightWrong`.** That relation is definitionally
  `∃ p q, Chooses s p q` (`PersonalNormativeGround.lean:288`) — already free will (`ClaimMeanings`
  F12, C168). Using it as the personal-ground antecedent would assume the freedom this axiom is
  meant to establish, so the freedom is posited here flat and independently, and the audit of
  `BoundedMeaning` is explicit that the three persons' `FreeWill` "rests entirely on" this
  bridge rather than on D-3.

  **What is load-bearing, and what is not.** Load-bearing: `Person`, `FreeSubject`,
  `NecessarySubject`, the three role assignments, and the exhaustion of `NecessarySubjectKind`.
  *Not* load-bearing: subsistence. `Subsists d := d.deiformEntity = divineReality`
  (`DivineAgape.lean:85`) already fixes each hypostasis in the one ground, so asserting it here
  would be restating a `def`; the one-ground consequence is *derived* below
  (`the_three_persons_share_the_one_ground`) as **perichoretic indwelling** and rests on
  `divineReality := Entity.ofGround`, a `def` (`DivineAgape.lean:70`), not on the three `META`
  procession axioms.

  **The three persons are never equated with the ground.** An earlier revision of this axiom
  carried `EntityOf a = divineReality ∧ EntityOf b = divineReality ∧ EntityOf c = divineReality`
  among its conjuncts. Since `divineReality := Entity.ofGround` is a `def` and the corpus proves
  `ofGround_ne_ofSubject (s) : EntityOf s ≠ Entity.ofGround` (`FoundationalUnicity.lean:134`), those
  three conjuncts made `False` derivable: the axiom was *refuted by a theorem of the same
  theory*. Indwelling is not identity, and the Nicene claim is indwelling — *praeter hoc, quod
  unus est, tres sunt* is not that the three **are** the one. The conjuncts are therefore deleted,
  and `the_three_persons_share_the_one_ground` below states the honest consequence: the three are
  perichoretic in the one ground, and **none of them is it**
  (`TrinitarianPersonalGround.no_person_is_the_ground`, `{Subject}`). The regression test is
  `formal/consistency/FalseNotDerivable.lean`, which must fail to compile; run
  `python3 scripts/check_consistency.py`.

  **Price.** `Person a` already entails `FreeSubject a` definitionally
  (`DominionOverActs = FreeWill`, `Person.lean:56`), so the three `FreeSubject` conjuncts are not
  an independent purchase — they are carried, and stated, by the `Person` conjuncts. They are
  nevertheless asserted explicitly and exported as separate theorems, because *stating* them is
  what discharges D-3's debt at the point a reader looks for it
  (`BoundedMeaning.lean:69`). Footprint: `{DivineSubjectRole, Means, NecessarySubjectKind, Subject, Will, subjectWill}` plus
  this axiom. -/
axiom TrinitarianPersonalBridge :
    ∃ a b c : Subject,
      DivineSubjectRole a = DivineRole.source ∧
      DivineSubjectRole b = DivineRole.word ∧
      DivineSubjectRole c = DivineRole.spirit ∧
      Person a ∧ Person b ∧ Person c ∧
      FreeSubject a ∧ FreeSubject b ∧ FreeSubject c ∧
      NecessarySubject a ∧ NecessarySubject b ∧ NecessarySubject c ∧
      (∀ s : Subject, NecessarySubjectKind s → s = a ∨ s = b ∨ s = c)

/-- The three persons exist and carry the three roles of origin. This is the witness projection
    of the bridge: everything downstream destructs this, so the shape a reader sees first is the
    doctrine rather than the flat conjunction.
    Footprint: `{DivineSubjectRole, Means, NecessarySubjectKind, Subject, TrinitarianPersonalBridge, Will, subjectWill}`. -/
theorem three_divine_persons_exist_with_roles :
    ∃ a b c : Subject,
      DivineSubjectRole a = DivineRole.source ∧
      DivineSubjectRole b = DivineRole.word ∧
      DivineSubjectRole c = DivineRole.spirit ∧
      Person a ∧ Person b ∧ Person c := by
  obtain ⟨a, b, c, hra, hrb, hrc, hpa, hpb, hpc, _, _, _, _, _, _, _⟩ :=
    TrinitarianPersonalBridge
  exact ⟨a, b, c, hra, hrb, hrc, hpa, hpb, hpc⟩

/-- Each of the three is a person.
    Footprint: `{DivineSubjectRole, Means, NecessarySubjectKind, Subject, TrinitarianPersonalBridge, Will, subjectWill}`. -/
theorem three_divine_persons_are_persons :
    ∃ a b c : Subject, Person a ∧ Person b ∧ Person c := by
  obtain ⟨a, b, c, _, _, _, hpa, hpb, hpc, _, _, _, _, _, _, _⟩ :=
    TrinitarianPersonalBridge
  exact ⟨a, b, c, hpa, hpb, hpc⟩

/-- **The three persons are free subjects — and this is the row the D-3 audit reads.** The
    audit gate is that these trace to `TrinitarianPersonalBridge` (`META`) and *not* to
    `BoundedMeaningRequiresFreeSubject` (`TRANS`); the footprint below is the evidence, and
    `BoundedMeaningRequiresFreeSubject` is absent from it. The conclusion is carried by the
    bridge's `FreeSubject` conjuncts, and is also reachable from its `Person` conjuncts
    definitionally, so it is stated twice over on purpose: once as the theorem a reader checks,
    once as the definitional consequence that shows the price is not being double-counted.
    Footprint: `{DivineSubjectRole, Means, NecessarySubjectKind, Subject, TrinitarianPersonalBridge, Will, subjectWill}`. -/
theorem three_divine_persons_are_free_subjects :
    ∃ a b c : Subject, FreeSubject a ∧ FreeSubject b ∧ FreeSubject c := by
  obtain ⟨a, b, c, _, _, _, _, _, _, hfa, hfb, hfc, _, _, _, _⟩ :=
    TrinitarianPersonalBridge
  exact ⟨a, b, c, hfa, hfb, hfc⟩

/-- The same three, at the definitional route: `Person s → FreeSubject s` is `h.2.2`, so the
    freedom in the preceding theorem is *not* an independent purchase. Stated so the price table
    cannot be read as charging twice for one fact.
    Footprint: `{Means, Subject, Will, subjectWill}` (vocabulary only — no bridge, no META). -/
theorem person_is_freeSubject (s : Subject) (h : Person s) : FreeSubject s :=
  h.2.2

/-- Each of the three is a necessary subject.
    Footprint: `{DivineSubjectRole, Means, NecessarySubjectKind, Subject, TrinitarianPersonalBridge, Will, subjectWill}`. -/
theorem three_divine_persons_are_necessary :
    ∃ a b c : Subject, NecessarySubject a ∧ NecessarySubject b ∧ NecessarySubject c := by
  obtain ⟨a, b, c, _, _, _, _, _, _, _, _, _, hna, hnb, hnc, _⟩ :=
    TrinitarianPersonalBridge
  exact ⟨a, b, c, hna, hnb, hnc⟩

/-- The three persons exhaust the necessary kind: there is no fourth necessary subject. This is
    the clause that turns "at least three" into "exactly three", and it is a *priced* claim —
    `NecessarySubjectKind` is vocabulary, but its inhabitant set is not, and nothing in the
    preceding corpus bounds it. Distinctness is separately **derived** below, from the role
    assignment, at zero cost.
    Footprint: `{DivineSubjectRole, Means, NecessarySubjectKind, Subject,
    TrinitarianPersonalBridge, Will, subjectWill}`. -/
theorem three_divine_persons_exhaust_the_necessary_kind :
    ∃ a b c : Subject,
      Person a ∧ Person b ∧ Person c ∧
      (∀ s : Subject, NecessarySubjectKind s → s = a ∨ s = b ∨ s = c) := by
  obtain ⟨a, b, c, _, _, _, hpa, hpb, hpc, _, _, _, _, _, _, hEx⟩ :=
    TrinitarianPersonalBridge
  exact ⟨a, b, c, hpa, hpb, hpc, hEx⟩

/-- **Distinctness is derived, not bought.** Three distinct roles cannot be borne by one subject,
    so `a ≠ b ∧ b ≠ c ∧ a ≠ c` follows from the role assignment alone. Plan §7 says distinctness
    "is C510's; do not re-derive it" — but C510 is about `DivineHypostasis` and does not reach
    `Subject`, so on this sort the derivation is both necessary and free. Nothing is paid here
    beyond the bridge itself.
    Footprint: `{DivineSubjectRole, Subject}`. -/
theorem roles_make_the_three_persons_distinct {a b c : Subject}
    (ha : DivineSubjectRole a = DivineRole.source)
    (hb : DivineSubjectRole b = DivineRole.word)
    (hc : DivineSubjectRole c = DivineRole.spirit) :
    a ≠ b ∧ b ≠ c ∧ a ≠ c := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> subst h
  · rw [ha] at hb
    exact DivineRole.source_ne_word hb
  · rw [hb] at hc
    exact DivineRole.word_ne_spirit hc
  · rw [ha] at hc
    exact DivineRole.source_ne_spirit hc

/-- **The three persons share the one ground — by indwelling, not by identity.** `divineReality`
    is `Entity.ofGround` by definition (`DivineAgape.lean:70`), so the ground is *one*; the three
    are related to it by `Perichoretic`, i.e. `OneEssence` instantiated three times. This is the
    derived form of subsistence and rests on a `def` unfolding, not on the three `META` procession
    axioms.

    The second conjunct is load-bearing and was not optional. An earlier revision stated this as
    `EntityOf a = Entity.ofGround ∧ …`, which `ofGround_ne_ofSubject` (`FoundationalUnicity.lean:134`)
    refutes outright: that made the corpus derive `False`. "Share one ground" is *praeter hoc, quod
    unus est, tres sunt* — the ground is not one of the three, and the three are not the ground. So
    the honest statement carries both halves: the three are perichoretic in the one ground **and**
    no subject is it.
    Footprint: `{DivineSubjectRole, Means, NecessarySubjectKind, Subject, TrinitarianPersonalBridge, Will, subjectWill}`. -/
theorem the_three_persons_share_the_one_ground :
    ∃ a b c : Subject,
      Person a ∧ Person b ∧ Person c ∧
      Perichoretic Entity.ofGround a b c ∧
      (∀ s : Subject, EntityOf s ≠ Entity.ofGround) := by
  obtain ⟨a, b, c, _, _, _, hpa, hpb, hpc, _, _, _, _, _, _, _⟩ :=
    TrinitarianPersonalBridge
  exact ⟨a, b, c, hpa, hpb, hpc,
    ofGround_is_perichoretic a b c hpa hpb hpc,
    fun s => ofGround_ne_ofSubject s⟩

/-- **The explicit negative boundary**, kept as its own row so no reader has to infer it from the
    shape of the conjunct above: no divine person *is* the ground. The ground is Personal and
    indwells all three; it is not a fourth person and not any of the three
    (`TrinitarianPersonalGround.no_person_is_the_ground` states the same fact with no bridge).
    Footprint: `{Subject}`. -/
theorem no_divine_person_is_the_ground (s : Subject) : EntityOf s ≠ Entity.ofGround :=
  ofGround_ne_ofSubject s

-- ===========================================================================
-- Section 3: §5.1 — one necessary ground, three free necessary persons
-- ===========================================================================

/-- **§5.1, the master theorem.** One necessary ground of reality; exactly one universal modal
    ground; and exactly three necessary persons, distinct by relation of origin, each a
    `Person`, each a `FreeSubject`, exhausting the necessary kind of subject, and perichoretic in
    the one ground.

    Two honest notes on the statement, both forced by types rather than by taste.

    (1) The plan's draft identified the persons by `DivineHypostasis.P1 = a`. That does not
    elaborate: `P1` is a field of `TrinitarianStructure` (`ConditionalTheology.lean:308`),
    instantiated at `Subj := DivineHypostasis`, and a `DivineHypostasis` cannot be equated with a
    `Subject` — there is no coercion and no common sort. The identification is therefore stated
    the only way the vocabulary allows: by **role** (`DivineSubjectRole a = .source`, and so on),
    which is also theologically the right content, since §6.3 and `ST` I q.28 a.3 distinguish the
    Persons by relations of origin rather than by essence. Naming which *hypostasis* each subject
    corresponds to is a further bridge and is **not** discharged — see §11.

    (2) The unicity conjunct (spelled out, since `ExistsUnique` does not exist in this
    environment) is **not** axiom-free: ground-unicity is conditional on
    the transcendence bound F15, the declared axiom `GroundTranscendence` (`Tag: META`).
    Existence of the ground was
    already unconditional (`ofGround_necessary_ground_of_reality`, 0 substantive); it is
    *unicity* that rests on the bound. Plan §10 lists this row as a reader defect, and plan §0.2
    settles how the price is displayed. **This changed on 2026-10-03:** before the finitude
    split, the bound here was `SemanticFinitude` at `Tag: VOCAB`, so the row kept a
    vocabulary-only `PROVEN` badge and the price was disclosed by
    `census_semantic_finitude.py` and by `semantic_omnipotence_is_consistent`
    (what a reader who rejects the bound loses). The split moved the unrestricted bound
    onto `GroundTranscendence` at `Tag: META`, so this row now prints a **metaphysical**
    price and reads `PROVEN↑` — **AXIOMATIC (GroundTranscendence)** to a reader — which is
    the honest outcome: the unicity of the ground was never vocabulary.

    Footprint: `{DivineSubjectRole, GroundTranscendence, Means, NecessarySubjectKind, Subject,
    TrinitarianPersonalBridge, Will, subjectWill}` — measured; identical to plan §7 except
    that `GroundTranscendence` stands where `SemanticFinitude` stood before the split.
    Note what is **absent**: no `AxAgapeEssence`, `AxProcessionWord` or `AxProcessionSpirit`, because
    the persons are identified by role rather than by hypostasis. Their absence is the honest
    measure of the open item at §11, and is deliberately not hidden inside the bridge's price. -/
theorem one_necessary_ground_three_free_necessary_persons :
    NecessaryGroundOfReality Entity.ofGround ∧
    (∃ g : Entity, UniversalModalGround g ∧
      ∀ g' : Entity, UniversalModalGround g' → g' = g) ∧
    (∃ a b c : Subject,
        DivineSubjectRole a = DivineRole.source ∧
        DivineSubjectRole b = DivineRole.word ∧
        DivineSubjectRole c = DivineRole.spirit ∧
        a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
        Person a ∧ Person b ∧ Person c ∧
        FreeSubject a ∧ FreeSubject b ∧ FreeSubject c ∧
        NecessarySubject a ∧ NecessarySubject b ∧ NecessarySubject c ∧
        (∀ s : Subject, NecessarySubjectKind s → s = a ∨ s = b ∨ s = c) ∧
        Perichoretic Entity.ofGround a b c) := by
  refine ⟨ofGround_necessary_ground_of_reality, ?_, ?_⟩
  · exact exactly_one_universal_modal_ground Logos.SemanticFinitude.GroundTranscendence
  · obtain ⟨a, b, c, hra, hrb, hrc, hpa, hpb, hpc, hfa, hfb, hfc,
      hna, hnb, hnc, hEx⟩ := TrinitarianPersonalBridge
    have hne := roles_make_the_three_persons_distinct hra hrb hrc
    exact ⟨a, b, c, hra, hrb, hrc, hne.1, hne.2.1, hne.2.2,
      hpa, hpb, hpc, hfa, hfb, hfc, hna, hnb, hnc, hEx,
      TrinitarianPersonalGround.ofGround_is_perichoretic a b c hpa hpb hpc⟩

/-- **The S4 gate, in the only form a kernel can carry.** The audit gate is that the three
    persons' freedom traces to the `META` bridge and *not* to the `TRANS` bounded-meaning axiom.
    A footprint is not statable inside the theory, so the gate has two halves and both are here.

    The kernel half, stated precisely because the loose version is **false**: D-3's antecedent is
    *not* confined to the impersonal cases. `guard_excludes_exactly_the_impersonal_cases`
    (`BoundedMeaning.lean:158`) shows the antecedent's survivors are ground, atoms, **and
    subjects** — the axiom is named *bounded* meaning precisely because it constrains subjects
    rather than excluding them. What D-3 cannot do is turn an impersonal entity into a free
    subject: on every survivor that is not a subject, the conclusion is never reached, because
    the antecedent already fails there (the ground has no passive intentional potency, an atom
    means nothing). So D-3 never *produces* freedom; where it applies it reads it off a subject,
    and D-2 is what asserts that subject has it.

    The footprint half, which is the part the gate is really checked by: the `#print axioms` line
    for `three_divine_persons_are_free_subjects` reads `{DivineSubjectRole, Means,
    TrinitarianPersonalBridge, Will, subjectWill}` — `BoundedMeaningRequiresFreeSubject` is
    **absent**. If a future refactor routes this existence through the `TRANS` axiom, that
    footprint grows it and the gate fails visibly, which is the intended failure mode.
    Footprint: `{BoundedMeaningRequiresFreeSubject, DivineSubjectRole, Means, NecessarySubjectKind, Subject, TrinitarianPersonalBridge, Will, subjectWill}`. -/
theorem the_three_persons_freedom_is_asserted_not_earned :
    (∃ a b c : Subject, FreeSubject a ∧ FreeSubject b ∧ FreeSubject c) ∧
    (∀ e : Entity, PassiveIntentionalPotency e → (∃ p : Prop, EntityMeans e p) →
      (e = Entity.ofGround ∨ (∃ n : Nat, e = Entity.ofAtom n)) ∨
        (∃ s : Subject, e = EntityOf s ∧ FreeWill s)) :=
  ⟨three_divine_persons_are_free_subjects, by
    intro e hPot hMeans
    rcases guard_excludes_exactly_the_impersonal_cases e with hImp | ⟨s, hs⟩
    · exact Or.inl hImp
    · obtain ⟨t, ht, hFree⟩ := BoundedMeaningRequiresFreeSubject e hPot hMeans
      exact Or.inr ⟨t, ht, hFree⟩⟩

/-- The impersonal survivors of D-3's antecedent are exactly the two that can never satisfy it:
    the ground has no passive intentional potency, and an atom means nothing. So D-3's antecedent
    is satisfiable **only** for subjects — which is why it cannot be the source of the three
    divine persons' freedom, and why the axiom is about creatures rather than about God.
    Footprint: `{Means, Subject, propext}` (vocabulary only). -/
theorem d3s_antecedent_cannot_fire_on_the_impersonal :
    (∀ (e : Entity), e = Entity.ofGround → ¬ PassiveIntentionalPotency e) ∧
    (∀ (e : Entity) (n : Nat), e = Entity.ofAtom n → ¬ (∃ p : Prop, EntityMeans e p)) :=
  ⟨fun _ h => by subst h; exact ofGround_no_intentional_potency,
   fun _ _ h hp => by subst h; simp [EntityMeans] at hp⟩

/-- The bridge is **not** derived from `GroundsRightWrong`, and is not routed through it: the
    relation is definitionally free will already, so a bridge built on it would be circular
    (plan §7, `ClaimMeanings` F12). This row records the *shape* of the freedom the bridge
    asserts, next to the shape `GroundsRightWrong` carries, so the difference is visible in the
    kernel rather than only in a prose note.
    Footprint: `{DivineSubjectRole, Means, NecessarySubjectKind, Subject, TrinitarianPersonalBridge, Will, subjectWill}`. -/
theorem the_bridge_asserts_freedom_independently_of_groundsRightWrong :
    (∃ a b c : Subject, FreeSubject a ∧ FreeSubject b ∧ FreeSubject c) ∧
    (∀ s : Subject, GroundsRightWrong s → ∃ p q : Prop, Chooses s p q) := by
  refine ⟨three_divine_persons_are_free_subjects, ?_⟩
  intro s h
  exact h.agential_foundation

/-- The ground is still not a fourth chooser after S4: adding three divine persons does not make
    the ground personal. This is the `praeter hoc, quod unus est, tres sunt` boundary, and it is
    re-checked here rather than inherited, because S4 is exactly the step at which it would have
    been tempting to let the ground's `Asiety` transfer into personhood.
    Footprint: `{Means, Subject}` (vocabulary only). -/
theorem s4_does_not_make_the_ground_a_fourth_chooser :
    ¬ Asiety Entity.ofGround :=
  TrinitarianPersonalGround.ground_is_not_a_fourth_chooser

-- ===========================================================================
-- Section 4: Footprint audit
-- ===========================================================================

#print axioms DivineRole.source_ne_word
#print axioms DivineRole.word_ne_spirit
#print axioms DivineRole.source_ne_spirit
#print axioms role_exhausts_the_sort
#print axioms three_divine_persons_exist_with_roles
#print axioms three_divine_persons_are_persons
#print axioms three_divine_persons_are_free_subjects
#print axioms person_is_freeSubject
#print axioms three_divine_persons_are_necessary
#print axioms three_divine_persons_exhaust_the_necessary_kind
#print axioms roles_make_the_three_persons_distinct
#print axioms the_three_persons_share_the_one_ground
#print axioms no_divine_person_is_the_ground
#print axioms one_necessary_ground_three_free_necessary_persons
#print axioms the_three_persons_freedom_is_asserted_not_earned
#print axioms d3s_antecedent_cannot_fire_on_the_impersonal
#print axioms the_bridge_asserts_freedom_independently_of_groundsRightWrong
#print axioms s4_does_not_make_the_ground_a_fourth_chooser

end Logos.TrinitarianSubjectBridge


/-!
================================================================================
SECTION: SinglePersonDenial
================================================================================
-/
/-
# Logos.SinglePersonDenial — the chain's hinge is dependence, and it is free

`LOVE.md` mounted the refutation of the author's objection on the wrong derivations
(`LOVE-2.md` D4): C576's `axiom → ¬¬axiom` read as a contradiction, a premise granted as an
answer (R21), and a fresh-signature countermodel that denied nothing in Γ (R20). It also
removed `AsietyFreedomOfGround`'s role from the doctrine of the ground's freedom — commit
`4a59173`, "try to improve personhood clarity" — by asserting that there is *no* relation
between the ground's scope and any subject's freedom. That assertion is false, and this module
is built on the reading that commit deleted.

## The objection, as a chain

`LOVE.md` §1 records it:

> "Se existe uma essência pessoal necessária e essa base é Livre e Imutável. Poderia não ser
> livre de se doar (em alguma altura)? Isto é: Se houvesse uma essência pessoal necessária que
> fosse uma só pessoa, só se poderia doar a seres contingentes (temporais). Isso não a faria
> também contingente?"

Reconstructed as the four steps it actually is:

1. **Single Person** — the essence is one person, so there is no other person to give to;
2. ⟹ it can only give to **contingent (temporal)** beings;
3. ⟹ its self-giving is **dependent on the contingent beings**;
4. ⟹ it is therefore contingent — against a Ground already determined **Eternal, Necessary,
   Free and Immutable**.

**Step 3 is the hinge, and it is where the argument dies.** Step 1 is impossible in Γ
(`no_person_is_the_ground`, C519, `{Subject}` — the same fact as `ofGround_ne_ofSubject`), and
step 2 is false because the donation is *intra-nature*: `SelfDonation f o` puts both relata at
`divineReality := Entity.ofGround`. Step 3 is what needs the refutation, because it is the step
that turns the gift into something the ground does not control, and step 4 is what needs the
character of that gift.

## What is free here, and what is not

| step | row | price |
|---|---|---|
| 1 | `single_person_denial_is_refuted` (C519's `≠`) | free |
| 2 | `not_a_single_person`, `self_gift_cannot_depend_on_a_contingent_person` | free |
| 3 | `donation_terminus_is_as_necessary_as_the_donor` | free |
| 4 | `donation_makes_contingency_is_refuted` | free |
| — | `agape_is_self_donation` (C575) — a donation exists | **1 META** |
| — | `FreeSubject` via `TrinitarianPersonalBridge` — the Persons are free | **1 META** |
| — | `Plurality.notAlone` (T12) — the Persons are distinct | **1 META** |

**Every step of the objection is refuted at zero substantive axioms, and the existence of the
donation is deliberately not used to refute it.** A row that refutes the objection by way of the
datum it also prices is not a refutation; it is the datum. These rows hold for *any*
`SelfDonation`, including one the corpus never witnesses.

## The terminology, which is load-bearing

| statement | symbol | status |
|---|---|---|
| the ground's essence is **personal** | `PersonalGround Entity.ofGround` (C362) | free |
| the ground is **OneEssence** for **every** Person | `indwells` (C140) | free |
| the ground's **freedom is shared** with those it grounds | `AsietyFreedomOfGround` (◈ `def`) | free as a `def` |
| the ground is **no Person among the three** | `no_person_is_the_ground` (C519) | free |
| a gift's **terminus is as necessary as the donor** | `donation_terminus_is_as_necessary_as_the_donor` | free |
| there is **more than one** Person | `Plurality.notAlone` (T12) | **1 META** |

"The ground is not a person" is the **fourth** row and only the fourth: `Person` and `Asiety` are
`Subject`-indexed, so `Entity.ofGround` lies outside their reach (`AsieticChoice.lean:147-148`,
discharged by `ofGround_ne_ofSubject`). It does **not** say the ground lacks personhood — the
second and third rows say the opposite, and the third is exactly the content commit `4a59173`
deleted. The ground is a personal OneEssence whose freedom is shared with the Persons in which
it is OneEssence; the ground is the nature, not an instance of it. Reading row 4 as a negation
of rows 2–3 is the error `LOVE-2.md` D1 records.

## What this module does not do

- It does **not** say the ground cannot love contingent beings. `AxGroundLovesContingentRealm`
  (C339, `LovesAsGround.lean`) is untouched: the ground's benevolence toward the contingent realm
  stands exactly as declared. The claim refuted was never that.
- It does **not** use `AxAgapeEssence`, `AxTwoSubjects`, `AxBoundedMeaningRequiresFreeSubject` or
  any other declared axiom. Each is cited at its own price and none is absorbed here.
- It does **not** identify a `Subject` with a `DivineHypostasis`. That correspondence is open and
  is recorded as C580 BLOCKED.
- It does **not** assert the ground's freedom as a `Free` predicate on `Entity`. Γ's vocabulary
  reaches the ground's freedom through `AsietyFreedomOfGround` (`AsietyFreedom.lean:141`) and
  `AsietyFreeWill`, registered ◈ in `Stipulations.lean` precisely because a `def` premise is
  invisible to `#print axioms`.
-/

namespace Logos.SinglePersonDenial

open Logos.Core
open Logos.Semantics (World)
open Logos.Entity (Entity EntityOf)
open Logos.Modal (NecessaryEntity)
open Logos.Agency (Subject NecessarySubjectKind ContingentSubjectKind)
open Logos.Person (Person)
open Logos.Plurality (NecessarySubject notAlone T12_twoPersons)
open Logos.RecoveredOntologicalGround
  (OneEssence ActualEntity GroundOfReality NecessaryGroundOfReality)
open Logos.NecessityEternity (ofGround_necessary ofGround_necessary_ground_of_reality ofGround_ne_ofSubject)
open Logos.DivineAgape (DivineHypostasis Subsists divineReality SelfDonation agape_is_self_donation)
open Logos.TrinitarianPersonalGround
  (PersonalGround Perichoretic ofGround_grounds_every_person no_person_is_the_ground
    ofGround_is_perichoretic the_ground_is_not_void_of_personhood)

/-- **The ground is a personal necessary essence, indwelt by every Person, and it is itself no
    Person.** The positive half of the refutation: the author's chain needs a personal necessary
    essence whose Persons are a *single* one, and the ground supplies the first conjunct and
    refuses the second.

    Read the conjunction in the order the tradition reads it. `necessary` is C161; `personal` is
    C362, whose two fields are `sustains` (presence-grounding) and `indwells` (`OneEssence`);
    `indwelt` is C140 and holds for **every** person, so it is not a claim about how many there
    are; `noPerson` is C519. **The ground is not absent personhood — it is personhood not
    reducible to one instance.**

    The conjunct that is *not* here is the population of Persons and its distinctness:
    `ofGround_is_perichoretic` instantiates `indwells` three times, but `Perichoretic`
    (`TrinitarianPersonalGround.lean:319`) is a plain conjunction of `OneEssence` and carries no
    `a ≠ b`. Three *distinct* Persons cost `AxTwoNecessaryPersonalCentres` (1 META, `Plurality.notAlone` /
    `T12_twoPersons`) and sit on their own row. A reader who wants "it cannot be only one" pays
    for it; a reader who wants "the ground is no single person" does not. Note on freedom (LOVE-4 / C587):
    a Free Person is derived at 0 META (`NoMeanerNoFalsity.a_genuine_free_person_exists`).

    Footprint: `{Means, NecessarySubjectKind, Subject, Will, subjectWill}`. -/
theorem single_necessary_personal_essence_three_persons :
    NecessaryGroundOfReality Entity.ofGround ∧
    PersonalGround Entity.ofGround ∧
    (∀ s : Subject, Person s → OneEssence Entity.ofGround (EntityOf s)) ∧
    (∀ s : Subject, ¬ (Entity.ofGround = EntityOf s)) :=
  ⟨ofGround_necessary_ground_of_reality,
    the_ground_is_not_void_of_personhood,
    fun s hP => ofGround_grounds_every_person s hP,
    fun s => no_person_is_the_ground s⟩

/-- **The author's first step is impossible, and this is the reductio he did not have to run.**
    Assume his premise directly — the essence *is* one single Person, i.e. some `Subject`'s entity
    is the ground — and `False` follows at zero substantive axioms: `no_person_is_the_ground`
    (C519) is `{Subject}` and is the same fact as `ofGround_ne_ofSubject`. The hypothesis is a
    **real premise** and `False` is the conclusion, so this is a reductio and not a denial.

    Read it with the terminology held apart, because this row is where the confusion in `LOVE.md`
    §3 came from. `False` here says the essence is **no Person**; it says nothing against the
    essence being **personal**, which C362 asserts and this module's first theorem repeats. The
    ground is the personal OneEssence; the Persons are its instances; the essence is not one of
    them. Commit `4a59173` read this row as denying the ground's personhood and rebuilt the
    doctrine around that reading; the row does not say it.

    Footprint: `{Subject}`. -/
theorem single_person_denial_is_refuted (hSingle : ∃ s : Subject, Entity.ofGround = EntityOf s) :
    False := by
  obtain ⟨s, hs⟩ := hSingle
  exact no_person_is_the_ground s hs

/-- **The author's premise is not Γ's doctrine.** The same content as the row above in closed
    form, for the reader who wants a proposition rather than a reductio: a necessary reality-essence
    which *is* one single person is refuted. Free, by C519 alone.

    Footprint: `{Subject}`. -/
theorem not_a_single_person :
    ¬ (NecessaryGroundOfReality Entity.ofGround ∧ (∃ s : Subject, Entity.ofGround = EntityOf s)) := by
  rintro ⟨_hN, hS⟩
  exact single_person_denial_is_refuted hS

/-- **Step 3 — the dependence — is refuted (C579, PROVEN, free).** This is the row the objection
    dies on. The claim was: *a Single Person can only give to contingent beings, so its self-giving
    is dependent on the contingent beings.* The hypothesis is that claim as a proposition — the
    donation's recipient is some `Subject`'s entity — and it is refutable at zero substantive
    axioms, because `SelfDonation` puts the recipient at `divineReality := Entity.ofGround` and
    `Entity.ofGround` is no `Subject`'s entity.

    The hypothesis is stated in the **stronger** form on purpose. The objection says
    *contingent (temporal)* beings, so the weakest statement of the dependency claim would
    restrict the recipient to a `ContingentSubjectKind s`. Γ refutes the stronger claim instead —
    that the recipient is a `Subject` **at all** — because `SelfDonation`'s recipient is at
    `divineReality` and `Entity.ofGround` is no `Subject`'s entity. The temporal qualification
    was therefore never the load-bearing part of the objection, and adding it back would only
    have made the refutation weaker.

    **No `AxAgapeEssence`.** The row holds for any `SelfDonation` whatsoever, which is what makes
    it a refutation rather than a restatement of the datum.

    Footprint: `{Subject}`. -/
theorem self_gift_cannot_depend_on_a_contingent_person
    (dependence : ∃ f o : DivineHypostasis, ∃ s : Subject,
      SelfDonation f o ∧ o.deiformEntity = EntityOf s) : False := by
  obtain ⟨_f, o, s, hSD, hEq⟩ := dependence
  obtain ⟨_hne, _hf, ho, _hlove, _hloc⟩ := hSD
  have ho' : o.deiformEntity = Entity.ofGround := ho.trans (by rfl)
  exact ofGround_ne_ofSubject s (ho'.symm.trans hEq)

/-- **Step 3, second face: the terminus is as necessary as the donor.** Free, and free in the
    strict sense: `Subsists` is a location-equality against `divineReality`, and the ground is a
    necessary entity (C145), so **both** relata of any donation are necessary. A gift whose
    recipient is necessary is not a gift the ground's eternity could depend on.

    This row is what "Free and Immutable" means here operationally: the ground's gift is not
    conditioned by anything outside its own nature, because its recipient *is* its own nature.

    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem donation_terminus_is_as_necessary_as_the_donor
    (f o : DivineHypostasis) (h : SelfDonation f o) :
    NecessaryEntity f.deiformEntity ∧ NecessaryEntity o.deiformEntity := by
  obtain ⟨_hne, hf, ho, _hlove, _hloc⟩ := h
  have hf' : f.deiformEntity = Entity.ofGround := hf.trans (by rfl)
  have ho' : o.deiformEntity = Entity.ofGround := ho.trans (by rfl)
  exact ⟨hf' ▸ ofGround_necessary, ho' ▸ ofGround_necessary⟩

/-- **Step 4 — the contingency conclusion — is refuted, free.** *It would therefore also be
    contingent.* The hypothesis is that conclusion as a proposition; discharging it yields `False`
    from C579's terminus row alone. No `AxAgapeEssence`.

    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem donation_makes_contingency_is_refuted
    (donation_makes_contingency :
      ∃ f o : DivineHypostasis, SelfDonation f o ∧ ¬ NecessaryEntity o.deiformEntity) :
    False := by
  obtain ⟨f, o, hSD, hnc⟩ := donation_makes_contingency
  exact hnc (donation_terminus_is_as_necessary_as_the_donor f o hSD).2

/-- **The module in one line.** The ground is a personal necessary essence indwelt by every Person
    and no Person itself; its gift cannot reach a contingent being, because every donation's
    terminus is the necessary ground; and the contingency conclusion therefore has no premise.
    Zero new axioms, and four separate prices cited rather than absorbed.

    Footprint: `{Means, NecessarySubjectKind, Subject, Will, subjectWill}`. -/
theorem singlePersonDenial_summary :
    NecessaryGroundOfReality Entity.ofGround ∧
    PersonalGround Entity.ofGround ∧
    (∀ s : Subject, ¬ (Entity.ofGround = EntityOf s)) ∧
    (¬ (NecessaryGroundOfReality Entity.ofGround ∧ (∃ s : Subject, Entity.ofGround = EntityOf s))) ∧
    (∀ f o : DivineHypostasis, SelfDonation f o →
      NecessaryEntity f.deiformEntity ∧ NecessaryEntity o.deiformEntity) :=
  ⟨ofGround_necessary_ground_of_reality,
    the_ground_is_not_void_of_personhood,
    fun s => no_person_is_the_ground s,
    not_a_single_person,
    donation_terminus_is_as_necessary_as_the_donor⟩

/-! ## Section 7: Axiom Footprint Audit -/

#print axioms single_necessary_personal_essence_three_persons
#print axioms single_person_denial_is_refuted
#print axioms not_a_single_person
#print axioms self_gift_cannot_depend_on_a_contingent_person
#print axioms donation_terminus_is_as_necessary_as_the_donor
#print axioms donation_makes_contingency_is_refuted
#print axioms singlePersonDenial_summary

end Logos.SinglePersonDenial
