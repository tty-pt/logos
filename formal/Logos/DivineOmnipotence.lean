/-
# Logos.DivineOmnipotence — Foundational Omnipotence and the Non-Contradictory Restriction

This module formalizes the characteristic of **Foundational Omnipotence**
(the ground's operative scope excludes no non-contradictory state of affairs;
`CHARACTERISTICS.md` §15; `CHARS.md` §15) for the necessary Ground of Reality
(`Entity.ofGround`).

### What is formalized:
1. **The price of the operational identification (`OperatesAt`, C241's model):**
   Γ has **no** causal production relation, so the canonical operation relation is
   *presence plus obtaining*. C241 is a machine-checked countermodel showing this
   price is real: an entity can be present in every world and still operate
   nothing — presence is not production.
2. **Gapless operative scope (`GaplessOperate`, C242):**
   No state of affairs satisfiable in any accessible world is closed to the
   ground's operative scope. In Aquinas' own terms (*ST* I, q. 25, a. 5, ad 1 —
   *De potentia Dei*), omnipotence is power over *whatever does not involve a
   contradiction*; C242 proves exactly that for Γ's satisfiable domain.
3. **The non-contradictory restriction, as a theorem (C243, C244):**
   The ground operates only what obtains, and therefore can never operate
   `φ ∧ ¬φ` — because no world satisfies a contradiction
   (`Semantics.nonContradiction`, `Semantics.lean:85`).
4. **Exhaustive exclusion and uniqueness (C245–C247):** no worldly atom and no
   discriminating subject is a gapless operator, so `Entity.ofGround` is the
   **sole** gapless operator in the Γ inventory.
5. **The master synthesis (`FoundationalOmnipotence`, C248 + companion):**
   Conjoins (2)–(4) with the universal grounding of `FoundationalOmnipresence`,
   at zero new substantive axioms.

### The honest boundary, machine-checked:
- **The orthodox reading is affirmed, not refuted.** Aquinas' restriction to the
  non-contradictory is *not* a weakening of omnipotence that Γ fails to reach;
  it is machine-checked here (C242) and its domain is machine-checked
  contradiction-free (C250, `{}`). The reading is also non-vacuous: the
  satisfiable domain is non-empty, so "power over everything that does not
  involve a contradiction" is a substantive, non-trivial scope.
- **What is refuted is only the contradiction-omni reading** (C244) — "power over
  everything conceivable, *including contradictions*". It is refuted *because of*
  the orthodox restriction, not against it: `φ ∧ ¬φ` is unsatisfiable in every
  world of Γ's classical valuation semantics, so it can never be operated. This
  is a coherence result of the framework, not a criticism of any doctrine.
- **The causal/creative sense remains BLOCKED** and is *not* claimed here. "Can
  bring X about" needs a production relation Γ does not have: the only initiation
  relation is `Agency.Initiates : Subject → State → State → Prop → Prop`
  (`Agency.lean:150`), a declared VOCAB axiom, and it is **subject**-indexed while
  `Entity.ofGround` is provably not a subject correlate
  (`ofGround_ne_ofSubject`, `NecessityEternity.lean:155`). The exact missing
  statements are recorded in `formal/GAPMAP.md` (Level 17) and `theorems/T27.txt`
  (written here without the `axiom`/`def` keywords on purpose — a line starting
  with `axiom` inside this header is parsed as a real axiom declaration by `depviz`
  and by `scripts/build_deduction.py`, which would register a phantom axiom):

      (1) MISSING VOCABULARY — a production relation, one level down from `Initiates`:
          Produces : Entity → World → Form → Prop
      (2) MISSING DERIVATION — the causal sense, which (1) alone does not give:
          for all g : Entity and all φ : Form,
            (∃ w, Satisfies w φ) → ∃ v, Produces g v φ

  Note that (1) alone would not yield (2): `GroundsEntity`
  (`RecoveredOntologicalGround.lean:57`) is explanatory containment (*esse est
  agere*), and `means_does_not_imply_means_selection` (`HostileSemantics.lean:1861`)
  already machine-checks that omni-scope does not entail selection power.
- **One further boundary, machine-checked (C249):** Γ's Kripke accessibility is
  not conjunctive, so gapless scope over accessible states of affairs is strictly
  weaker than power over every pair of jointly accessible contents. C249 is the
  generic separation, not a refutation of classical omnipotence.

A note on vocabulary: because `Core.T p` is the identity (`Core.lean:40`), no
consistency predicate is built on `T` here. "Does not involve a contradiction" is
read as *satisfiability in Γ's classical valuation semantics*
(`∃ w, Satisfies w φ`), which is non-degenerate and is discharged by
`Semantics.nonContradiction`.
-/

import Logos.Core
import Logos.Semantics
import Logos.Entity
import Logos.Modal
import Logos.Agency
import Logos.Necessity
import Logos.RecoveredOntologicalGround
import Logos.NecessityEternity
import Logos.FoundationalOmnipresence
import Logos.TheologicalModalHardening

namespace Logos.DivineOmnipotence

open Logos.Semantics (Form World Satisfies sat_and sat_not)
open Logos.Entity (Entity EntityOf ExistsAt actualWorld)
open Logos.Modal (NecessaryEntity)
open Logos.Agency (Subject)
open Logos.Necessity (WProp)
open Logos.RecoveredOntologicalGround (GroundsEntity)
open Logos.FoundationalOmnipresence
    (WorldRigidPresence UniversalModalGround ofGround_universal_modal_ground)
open Logos.TheologicalModalHardening (KripkeFrame UniversalFrame)

-- ============================================================================
-- Section 1: The Scope Domain — Satisfiable States of Affairs
-- ============================================================================

/-- A state of affairs P is possible at `w` when it is satisfied in some world
    accessible from `w` under `frame`. With the weakest frame
    (`UniversalFrame`, every world accessible) this is exactly Γ's satisfiable
    domain: `∃ v, Satisfies v P`.
    Footprint: `{}`. -/
def PossibleAt (frame : KripkeFrame World) (w : World) (P : WProp) : Prop :=
  ∃ v, frame.R w v ∧ P v

/-- **THE PRICED IDENTIFICATION — the founding decision of this batch.**
    Γ has no causal production relation (see the module header), so the canonical
    operation relation is *presence plus obtaining*: the entity is present at `v`
    and the content P obtains at `v`. This is a **definition**, not a derivation:
    C241 machine-checks that the price is real (presence ⇏ production), and the
    causal/creative sense stays BLOCKED.
    Footprint: `{Subject}`. -/
def OperatesAt (v : World) (e : Entity) (P : WProp) : Prop :=
  ExistsAt v e ∧ P v

/-- Gapless operative scope: no possible state of affairs is closed to the
    entity's operative scope at the evaluating world — the weak (Thomistic)
    classical sense of omnipotence, generic over carrier and operation relation.
    Footprint: `{}`. -/
def GaplessOperate (frame : KripkeFrame World) {Ent : Type}
    (Operates : World → Ent → WProp → Prop) (e : Ent) : Prop :=
  ∀ w P, PossibleAt frame w P → ∃ v, frame.R w v ∧ Operates v e P

/-- Conjunctive power: every *pair* of possible states of affairs, jointly
    possible, is operated together at one world. Strictly stronger than
    `GaplessOperate`; C249 machine-checks that the two come apart.
    Footprint: `{}`. -/
def ConjunctivePower (frame : KripkeFrame World) {Ent : Type}
    (Operates : World → Ent → WProp → Prop) (e : Ent) : Prop :=
  ∀ w P Q, PossibleAt frame w P → PossibleAt frame w Q →
    ∃ v, frame.R w v ∧ Operates v e (fun u => P u ∧ Q u)

-- ============================================================================
-- Section 2: The Price of the Identification (Countermodel)
-- ============================================================================

/-- **The price of the operational identification, machine-checked.**
    An entity can be present in *every* world and still operate nothing: presence
    is not production. The witness is the two-element carrier where one element is
    universally present but no content is ever operated at it, and the operation
    relation is the one Γ actually uses — the second conjunct of a content at the
    evaluating world. This is what licenses the `README-OLD.md:263` disclaimer
    for the causal sense, and it is why C248 below is a *foundational* record.
    Footprint: `{}`. -/
theorem existence_everywhere_does_not_entail_operation :
    ∃ (Ent : Type) (ExistsAtRel : World → Ent → Prop)
      (Operates : World → Ent → WProp → Prop) (e : Ent),
      (∀ w : World, ExistsAtRel w e) ∧
      ¬ GaplessOperate (UniversalFrame World) Operates e := by
  let Ent : Type := Bool
  let ExistsAtRel : World → Ent → Prop := fun _ _ => True
  let Operates : World → Ent → WProp → Prop :=
    fun _ b P => b = true ∧ ∀ v, P v
  refine ⟨Ent, ExistsAtRel, Operates, false, fun _ => trivial, ?_⟩
  intro hG
  obtain ⟨v, _, hOp⟩ :=
    hG actualWorld (fun u => Satisfies u (Form.atom 0)) ⟨actualWorld, trivial, rfl⟩
  exact Logos.Semantics.TV.noConfusion (hOp.2 (fun _ => Logos.Semantics.TV.f))

-- ============================================================================
-- Section 3: The Doctrine — Gapless Operative Scope for the Ground
-- ============================================================================

/-- **Foundational Omnipotence, the doctrine (Aquinas *ST* I, q. 25, a. 5, ad 1):
    no state of affairs that is satisfiable in any accessible world is closed to
    the ground's operative scope.** With `UniversalFrame` the scope is Γ's whole
    satisfiable domain, and `OperatesAt` is the priced identification of §1. The
    proof is the two clauses of `OperatesAt`: the ground is present at `v` by the
    world-rigid constructor (stipulation ◈ `ofGround_existsAt`) and the content
    obtains at `v` by the witness. Zero substantive axioms.
    Footprint: `{Subject}`. -/
theorem ofGround_gapless_operative_scope :
    GaplessOperate (UniversalFrame World) OperatesAt Entity.ofGround := by
  intro w P ⟨v, hRv, hPv⟩
  exact ⟨v, hRv, trivial, hPv⟩

/-- The non-contradictory restriction, first horn: the ground operates **only what
    obtains**. Nothing unobtained — hence nothing unsatisfiable — is within the
    ground's operative scope. (Holds of every entity under `OperatesAt`, hence of
    the ground with no premise at all.)
    Footprint: `{Subject}`. -/
theorem ofGround_operates_only_what_obtains :
    ∀ v : World, ∀ P : WProp, OperatesAt v Entity.ofGround P → P v := by
  intro v P h
  exact h.2

/-- **The non-contradictory restriction, second horn: the ground cannot operate a
    contradiction — ever, at no world.** `φ ∧ ¬φ` is unsatisfiable in every world
    of Γ's classical valuation semantics (`Semantics.nonContradiction`), so the
    ground's operative scope excludes it. This is the *only* sense of omnipotence
    refuted here — the contradiction-omni reading ("everything conceivable,
    including contradictions") — and it is refuted **by** the orthodox
    restriction, not against it. The cost is `propext`, inherited from
    `Semantics.nonContradiction` (C14, `CL`).
    Footprint: `{propext, Subject}`. -/
theorem ofGround_does_not_operate_contradictions (v : World) (φ : Form) :
    ¬ OperatesAt v Entity.ofGround
        (fun u => Satisfies u (Form.and φ (Form.not φ))) := by
  intro h
  have hSat : Satisfies v (Form.and φ (Form.not φ)) := h.2
  have hNo : ¬ Satisfies v (Form.and φ (Form.not φ)) :=
    Logos.Semantics.nonContradiction φ v
  rw [sat_and, sat_not] at hSat hNo
  exact hNo hSat

-- ============================================================================
-- Section 4: Exhaustive Exclusion (Atoms and Discriminating Subjects)
-- ============================================================================

/-- Exhaustive exclusion: no worldly atom is a gapless operator. An atom exists
    exactly where its atomic content obtains, so it misses every world in which
    that content is denied — the witness being the content `¬atom n` itself, which
    is satisfiable (`(fun _ => TV.f)`) and yet unobtained wherever the atom
    exists. Footprint: `{Subject}`. -/
theorem atom_not_gapless_operate (n : Nat) :
    ¬ GaplessOperate (UniversalFrame World) OperatesAt (Entity.ofAtom n) := by
  intro hG
  obtain ⟨v, _, hEv, hPv⟩ :=
    hG actualWorld (fun u => Satisfies u (Form.not (Form.atom n)))
      ⟨fun _ => Logos.Semantics.TV.f, trivial, fun hc =>
        Logos.Semantics.TV.noConfusion hc⟩
  exact hPv hEv

/-- Exhaustive exclusion: a subject is not a gapless operator. A subject exists
    only at the actual world, so it misses every satisfiable content denied there
    — witness `¬atom 0`, which is satisfiable in `(fun _ => TV.f)` and yet denied
    at `actualWorld`. Footprint: `{Subject}`. -/
theorem discriminating_subject_not_gapless_operate (s : Subject) :
    ¬ GaplessOperate (UniversalFrame World) OperatesAt (EntityOf s) := by
  intro hG
  obtain ⟨v, _, hEv, hPv⟩ :=
    hG actualWorld (fun u => Satisfies u (Form.not (Form.atom 0)))
      ⟨fun _ => Logos.Semantics.TV.f, trivial, fun hc =>
        Logos.Semantics.TV.noConfusion hc⟩
  have hEvEq : v = actualWorld := hEv
  subst v
  exact hPv rfl

/-- **The ground is the sole gapless operator in the Γ inventory.** Together with
    the exclusions of §4, this closes the characteristic: among the three
    constructors of `Entity`, only `Entity.ofGround` has gapless operative scope.
    Footprint: `{Subject}`. -/
theorem ofGround_sole_gapless_operator (e : Entity)
    (h : GaplessOperate (UniversalFrame World) OperatesAt e) :
    e = Entity.ofGround := by
  cases e with
  | ofSubject s => exact False.elim (discriminating_subject_not_gapless_operate s h)
  | ofAtom n => exact False.elim (atom_not_gapless_operate n h)
  | ofGround => rfl

-- ============================================================================
-- Section 5: The Master Synthesis — Foundational Omnipotence
-- ============================================================================

/-- Foundational Omnipotence: the conjunction of gapless operative scope over the
    satisfiable domain, the two horns of the non-contradictory restriction
    (operates only what obtains; operates no contradiction — the second being the
    machine-checked exclusion of the contradiction-omni reading), and the
    universal grounding of `FoundationalOmnipresence`. (The structure itself is
    not an audited kernel node; the audited axiom set of the ground instance is
    recorded in `ofGround_foundational_omnipotence` below.) -/
structure FoundationalOmnipotence (g : Entity) : Prop where
  /-- No satisfiable state of affairs is closed to the entity's operative scope -/
  gapless_operate : GaplessOperate (UniversalFrame World) OperatesAt g
  /-- Only what obtains is operated -/
  operates_only_obtaining : ∀ v : World, ∀ P : WProp, OperatesAt v g P → P v
  /-- No contradiction is ever operated -/
  operates_no_contradiction :
    ∀ v : World, ∀ φ : Form,
      ¬ OperatesAt v g (fun u => Satisfies u (Form.and φ (Form.not φ)))
  /-- The scope covers all reality as the universal modal ground -/
  universal_ground : UniversalModalGround g

/-- Master Synthesis Theorem: The Ground of Reality possesses Foundational
    Omnipotence in Γ — its operative scope excludes no non-contradictory state of
    affairs, it operates only what obtains, and (per the carried field) it can
    never operate a contradiction. Zero substantive axioms; the whole footprint is
    the declared vocabulary `{Means, Subject}` (plus `propext`, from C14).
    Footprint: `{Means, Subject, propext}`. -/
theorem ofGround_foundational_omnipotence :
    FoundationalOmnipotence Entity.ofGround :=
  { gapless_operate := ofGround_gapless_operative_scope
    operates_only_obtaining := ofGround_operates_only_what_obtains
    operates_no_contradiction := ofGround_does_not_operate_contradictions
    universal_ground := ofGround_universal_modal_ground }

/-- The Thomistic principle: any necessary entity that is present in every
    possible world and is a universal modal ground thereby satisfies Foundational
    Omnipotence. The premise of necessary existence is carried explicitly
    (Aquinas *ST* I q. 25 a. 5: the ground is *semper et ubique*); the conclusion
    is proved from world-rigid presence and universal grounding alone — the two
    non-contradictory horns hold of every entity under `OperatesAt` with no
    premise at all. Footprint: `{Means, Subject, propext}`. -/
theorem necessity_and_presence_yield_foundational_omnipotence
    (e : Entity) (_hNec : NecessaryEntity e) (hPres : WorldRigidPresence e)
    (hUniv : UniversalModalGround e) :
    FoundationalOmnipotence e :=
  { gapless_operate := by
      intro w P ⟨v, hRv, hPv⟩
      exact ⟨v, hRv, hPres v, hPv⟩
    operates_only_obtaining := by
      intro v P h
      exact h.2
    operates_no_contradiction := by
      intro v φ h
      have hSat : Satisfies v (Form.and φ (Form.not φ)) := h.2
      have hNo : ¬ Satisfies v (Form.and φ (Form.not φ)) :=
        Logos.Semantics.nonContradiction φ v
      rw [sat_and, sat_not] at hSat hNo
      exact hNo hSat
    universal_ground := hUniv }

-- ============================================================================
-- Section 6: The Scope Domain Is Non-Empty and Contradiction-Free
-- ============================================================================

/-- **The domain of C242 is non-empty and contradiction-free** — the two facts
    that make the orthodox reading substantive rather than vacuous, and that
    license reading it as "power over whatever does not involve a contradiction"
    (Aquinas *ST* I, q. 25, a. 5, ad 1) in Γ's classical valuation semantics.
    Non-emptiness: the content `atom 0` is satisfied at `actualWorld`.
    Contradiction-freedom: no content of the form `φ ∧ ¬φ` is satisfied at any
    world (`Semantics.nonContradiction`, C14 — hence the `propext` cost).
    Footprint: `{propext}`. -/
theorem satisfiable_scope_is_nonempty_and_contradiction_free :
    (∃ v : World, ∃ φ : Form, Satisfies v φ) ∧
    (∀ (φ : Form) (v : World),
      ¬ Satisfies v (Form.and φ (Form.not φ))) :=
  ⟨⟨actualWorld, Form.atom 0, rfl⟩,
   fun φ v => Logos.Semantics.nonContradiction φ v⟩
-- ============================================================================
-- Section 7: Separations (Countermodel) — What Gapless Scope Does Not Give
-- ============================================================================

/-- Countermodel: gapless operative scope does **not** entail conjunctive power.
    Under the weakest frame every world is accessible, yet accessibility in Γ is
    not conjunctive: the contents `atom 0` and `¬atom 0` are each possible and no
    single world operates both. This bounds the batch's own claim: the
    non-contradictory restriction is machine-checked, but "jointly possible pairs"
    is strictly stronger than what Γ's modal accessibility delivers. Footprint: `{}`. -/
theorem gapless_operative_scope_without_conjunctive_power :
    ∃ (Ent : Type) (Operates : World → Ent → WProp → Prop) (e : Ent),
      GaplessOperate (UniversalFrame World) Operates e ∧
      ¬ ConjunctivePower (UniversalFrame World) Operates e := by
  let Ent : Type := Bool
  let Operates : World → Ent → WProp → Prop := fun v b P => b = true ∧ P v
  refine ⟨Ent, Operates, true, ?_, ?_⟩
  · intro w P ⟨v, hRv, hPv⟩
    exact ⟨v, hRv, rfl, hPv⟩
  · intro hCP
    obtain ⟨v, _, hOp⟩ :=
      hCP actualWorld
        (fun u => Satisfies u (Form.atom 0))
        (fun u => Satisfies u (Form.not (Form.atom 0)))
        ⟨actualWorld, trivial, rfl⟩
        ⟨fun _ => Logos.Semantics.TV.f, trivial, fun hc =>
          Logos.Semantics.TV.noConfusion hc⟩
    exact hOp.2.2 hOp.2.1

/-- Countermodel: an **exhaustively meaningful scope does not entail operative
    scope**. The witness carries a total meaning relation (`∀ P, Scope e P`) and
    an empty operation relation, so maximal scope — the same scope the ground has
    by stipulation ◈ `ofGround_meansAll` — buys no operative scope whatever. This
    is the operational analogue of `means_does_not_imply_means_selection`
    (`HostileSemantics.lean:1861`): scope is not power. It is why C242 is proved
    from world-rigid *presence* (◈ `ofGround_existsAt`) and never read off the
    meaning-exhaustive scope of `FoundationalOmniscience`. Footprint: `{}`. -/
theorem exhaustive_scope_without_operative_scope :
    ∃ (Ent : Type) (Scope : Ent → WProp → Prop)
      (Operates : World → Ent → WProp → Prop) (e : Ent),
      (∀ P : WProp, Scope e P) ∧
      ¬ GaplessOperate (UniversalFrame World) Operates e := by
  let Ent : Type := Bool
  let Scope : Ent → WProp → Prop := fun _ _ => True
  let Operates : World → Ent → WProp → Prop := fun _ _ _ => False
  refine ⟨Ent, Scope, Operates, true, fun _ => trivial, ?_⟩
  intro hG
  obtain ⟨v, _, hOp⟩ :=
    hG actualWorld (fun u => Satisfies u (Form.atom 0)) ⟨actualWorld, trivial, rfl⟩
  exact hOp

-- ============================================================================
-- Axiom Footprints
-- ============================================================================

#print axioms existence_everywhere_does_not_entail_operation
#print axioms ofGround_gapless_operative_scope
#print axioms ofGround_operates_only_what_obtains
#print axioms ofGround_does_not_operate_contradictions
#print axioms atom_not_gapless_operate
#print axioms discriminating_subject_not_gapless_operate
#print axioms ofGround_sole_gapless_operator
#print axioms ofGround_foundational_omnipotence
#print axioms necessity_and_presence_yield_foundational_omnipotence
#print axioms satisfiable_scope_is_nonempty_and_contradiction_free
#print axioms gapless_operative_scope_without_conjunctive_power
#print axioms exhaustive_scope_without_operative_scope

end Logos.DivineOmnipotence
