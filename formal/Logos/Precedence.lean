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
  * C423 — the ground **conditions** every content-bearer (`GroundsEntity`). The
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

import Logos.Core
import Logos.Semantics
import Logos.Entity
import Logos.RecoveredOntologicalGround
import Logos.DivineImmutability
import Logos.SemanticFinitude

namespace Logos.Precedence

open Logos.Core (T N_T N_F rightWrongDistinction)
open Logos.Semantics (Form World Satisfies TV)
open Logos.Entity (Entity ExistsAt actualWorld falsityWorld)
open Logos.RecoveredOntologicalGround (EntityMeans GroundsEntity)
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
    `GroundsEntity` relation.

    Note that the meaning hypothesis is **not needed** — `GroundsEntity
    Entity.ofGround e` is `∀ p, EntityMeans e p → True`, which holds for every
    entity. The hypothesis is carried because §9's prose says "every being that
    stands under the distinction", and stating it makes the row readable as that
    claim. The stronger fact it implies is the report: under Γ's definitions the
    ground is a condition of *everything*, meaning-bearing or not. This is the
    same fact C328 records for the meaningless (`intro p _; exact True.intro`),
    and it is cited there rather than re-proved for atoms.
    Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
theorem ground_conditions_every_content_bearer (w : World) (e : Entity) :
    ExistsAt w e → (∃ p : Prop, EntityMeans e p) → GroundsEntity Entity.ofGround e :=
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
    it. "Precedes" is deliberately phrased as `GroundsEntity` — a condition — and
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
    ExistsAt w e' → (∃ p : Prop, EntityMeans e' p) → GroundsEntity e e'
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
      everything — forces `GroundsEntity (EntityOf s) ofGround`, i.e.
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
    Footprint: `{Means, NecessarySubjectKind, SemanticFinitude, Subject}`.
    `NecessarySubjectKind` rides along because the field
    `conditions_every_bearer` is typed over `ExistsAt`, which unfolds to
    `SubjectExistsAt`; the proof reads no predicate.
    -/
theorem ofGround_sole_precedes_right_wrong :
    ∀ e : Entity, PrecedesRightWrong e → e = Entity.ofGround := by
  intro e h
  cases e with
  | ofSubject s =>
      have hGrounds : GroundsEntity (Entity.EntityOf s) Entity.ofGround :=
        h.conditions_every_bearer Entity.actualWorld Entity.ofGround trivial
          ⟨True, trivial⟩
      have hAll : ∀ p : Prop, Means s p := by
        intro p
        exact hGrounds p trivial
      obtain ⟨p, hp⟩ := Logos.SemanticFinitude.SemanticFinitude s
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

    Footprint: `{propext, Means, NecessarySubjectKind, SemanticFinitude, Subject}`.
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
