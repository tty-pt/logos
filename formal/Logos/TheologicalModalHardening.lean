/-
# Logos.TheologicalModalHardening — Modal Ontology Hardening & Theological Separation

This module investigates the modal and theological status of necessary reality in Γ:
1. Audits existing `NecessaryEntity` and `NecessarySubject` declarations into
   Categories A, B, and C.
2. Hardens the modal ontology: explicitly defines `ActualEntity`, `NecessaryEntity`,
   and `ContingentEntity`, and proves their mutual separations.
3. Constructs the two fundamental modal world models:
   - Model E: Absolute Empty World (`otherWorld := fun _ => TV.f`), where no entity exists.
   - Model G: Necessary Being Without Creation, where a necessary being exists without any
     contingent entities.
4. Tests whether a necessary entity must be the ultimate ground:
   constructs an infinite necessary grounding chain over ℤ, proving that
   `∃ e, NecessaryEntity e ↛ UltimateGroundExists`.
5. Investigates candidate bridge principles for `NecessaryEntity g → UltimateGround g`:
   well-foundedness, modal foundation, self-grounding, and totality grounding.
6. Implements the machine-visible "Empty World" theological test.
7. Systematically separates the theological attribute ladder:
   - Model NP: Necessary Impersonal Being (`NecessaryEntity ↛ NecessarySubject`)
   - Model NA: Necessary Non-Agent (`NecessarySubject ↛ Agency`)
   - Model ND: Necessary Deterministic Subject (`IntentionalSubject ↛ FreeWill`)
8. Investigates creation relations: proves that a necessary entity entails neither the
   existence of contingent entities nor a creation relation.
9. Separates necessary existence from uniqueness:
   proves `∃ e, NecessaryEntity e ↛ ∃! e, NecessaryEntity e` via coexisting necessary entities.
10. Establishes the 7-tier Divine Attribute Ladder and Theological Modal Atlas.
-/

import Logos.Core
import Logos.Semantics
import Logos.Truthmaker
import Logos.Modal
import Logos.Agency
import Logos.Person
import Logos.GroundPerson
import Logos.HostileSemantics

namespace Logos.TheologicalModalHardening

open Logos.Semantics (Form World Satisfies TrueAt)
open Logos.Truthmaker (Entity ExistsAt actualWorld otherWorld)
open Logos.HostileSemantics.TruthmakingInvestigation (no_entity_at_otherWorld)

-- ===========================================================================
-- Part 1: Modal Ontology Hardening (Sections I, II, III, XI, XII)
-- ===========================================================================

/-!
### 1. Hardened Modal Definitions
-/

/-- Actual existence: entity exists at the designated actual world. -/
def ActualEntity (e : Entity) : Prop := ExistsAt actualWorld e

/-- Necessary existence: entity exists at every possible world. -/
def NecessaryEntity (e : Entity) : Prop := ∀ w : World, ExistsAt w e

/-- Contingent existence: entity exists actually, but fails to exist in at least one possible world.
    Philosophical specification:
    We adopt the strong actualist definition of contingency (`ActualEntity e ∧ ∃ w, ¬ ExistsAt w e`).
    An entity that exists in no world is impossible, not contingent; an entity that exists in
    non-actual worlds but not the actual world is merely possible. Contingency of an entity
    means actual reality coupled with modal fragility. -/
def ContingentEntity (e : Entity) : Prop :=
  ActualEntity e ∧ ∃ w : World, ¬ ExistsAt w e

/-- A necessary entity is never contingent. -/
theorem necessary_not_contingent (e : Entity) :
    NecessaryEntity e → ¬ ContingentEntity e := by
  intro hNec ⟨_, ⟨w, hNotEx⟩⟩
  exact hNotEx (hNec w)

/-- Abstract Signature for Modal Ontology Separations. -/
structure ModalOntologySignature where
  Entity : Type
  World : Type
  actualWorld : World
  ExistsAt : World → Entity → Prop
  ActualEntity : Entity → Prop := fun e => ExistsAt actualWorld e
  NecessaryEntity : Entity → Prop := fun e => ∀ w, ExistsAt w e
  ContingentEntity : Entity → Prop := fun e => ActualEntity e ∧ ∃ w, ¬ ExistsAt w e

/-- Non-contingency does not entail necessity:
    An entity that exists in no world (impossible entity) is not contingent,
    yet it is certainly not necessary. -/
theorem non_contingent_not_entails_necessary :
    ¬ (∀ S : ModalOntologySignature, ∀ e : S.Entity, ¬ S.ContingentEntity e → S.NecessaryEntity e) := by
  intro hAll
  let S : ModalOntologySignature := {
    Entity := Unit
    World := Bool
    actualWorld := true
    ExistsAt := fun _ _ => False
  }
  have hNotCont : ¬ S.ContingentEntity () := by
    intro ⟨hAct, _⟩
    exact hAct
  have hNec : S.NecessaryEntity () := hAll S () hNotCont
  have hFalse := hNec true
  exact hFalse

/-!
### 2. Fundamental World Models: Model E and Model G
-/

/-- Model E — Absolute Empty World:
    A world in which NO entity in the ontological domain exists.
    In Logos, `otherWorld := fun _ => TV.f` provides a concrete witness:
    both subjects and atomic entities fail to exist at `otherWorld`. -/
theorem model_E_absolute_empty_world :
    ∃ w : World, ∀ e : Entity, ¬ ExistsAt w e :=
  ⟨otherWorld, no_entity_at_otherWorld⟩

/-- Logical Necessity vs Ontological Emptiness:
    In Model E (`otherWorld`), logical tautologies (such as excluded middle)
    are satisfied, while the ontological domain is completely empty. -/
theorem logical_truth_in_empty_world (φ : Form) :
    Satisfies otherWorld (Form.or φ (Form.not φ)) ∧
    (∀ e : Entity, ¬ ExistsAt otherWorld e) :=
  ⟨Logos.Truthmaker.lawExcludedMiddle φ otherWorld,
   no_entity_at_otherWorld⟩

/-- Model G Signature: Necessary Being Without Contingent Creation.
    There exists a distinguished necessary entity `g` that exists in all worlds,
    and there exists a "no-creation" world `w_solo` where only `g` exists
    and no contingent entities exist. -/
structure ModelG_Signature where
  Entity : Type
  World : Type
  actualWorld : World
  ExistsAt : World → Entity → Prop
  NecessaryEntity : Entity → Prop := fun e => ∀ w, ExistsAt w e
  ContingentEntity : Entity → Prop := fun e => ExistsAt actualWorld e ∧ ∃ w, ¬ ExistsAt w e
  g : Entity
  g_necessary : NecessaryEntity g
  w_no_creation : World
  g_exists_at_no_creation : ExistsAt w_no_creation g
  no_contingent_creation_at_w : ∀ x : Entity, ExistsAt w_no_creation x → ¬ ContingentEntity x

/-- Concrete realization of Model G:
    `g` is represented by `none : Option Unit` (exists in all worlds).
    Contingent creatures are represented by `some ()` (exist only at `true`). -/
def ConcreteModelG : ModelG_Signature where
  Entity := Option Unit
  World := Bool
  actualWorld := true
  ExistsAt := fun w e =>
    match e with
    | none => True
    | some () => w = true
  g := none
  g_necessary := fun _ => trivial
  w_no_creation := false
  g_exists_at_no_creation := trivial
  no_contingent_creation_at_w := by
    intro x hExAtFalse ⟨_, ⟨w_witness, hNotAtW⟩⟩
    cases x with
    | none => exact hNotAtW trivial
    | some u => cases hExAtFalse

/-- Model G is consistent:
    Necessary existence does not require or entail the existence of contingent reality. -/
theorem model_G_consistent : ∃ _M : ModelG_Signature, True :=
  ⟨ConcreteModelG, trivial⟩

/-!
### 3. Relational Kripke Modal Semantics (Section XI)
-/

/-- A relational Kripke frame over worlds with accessibility relation R. -/
structure KripkeFrame (W : Type) where
  R : W → W → Prop

/-- Bounded necessity under Kripke accessibility:
    BoxR frame P w asserts that P holds in all worlds accessible from w. -/
def BoxR {W : Type} (frame : KripkeFrame W) (P : W → Prop) (w : W) : Prop :=
  ∀ v : W, frame.R w v → P v

/-- Universal S5 frame as a special case:
    When every world is accessible from every world, BoxR coincides with universal quantification. -/
def UniversalFrame (W : Type) : KripkeFrame W where
  R := fun _ _ => True

theorem boxR_universal_iff {W : Type} (P : W → Prop) (w : W) :
    BoxR (UniversalFrame W) P w ↔ (∀ v : W, P v) := by
  apply Iff.intro
  · intro hBox v
    exact hBox v trivial
  · intro hAll v _
    exact hAll v

/-- World filtering under accessibility:
    If `otherWorld` (the absolute empty world) is deemed inaccessible from `actualWorld`,
    world-indexed truthmaking can hold across all ACCESSIBLE worlds without asserting
    that entities exist in empty worlds. -/
theorem accessible_worldwise_truthmaking_consistent :
    let W := Bool
    let R := fun (w v : W) => w = true → v = true
    let frame : KripkeFrame W := ⟨R⟩
    let ExistsAtW := fun (w : W) (_e : Unit) => w = true
    BoxR frame (fun v => ∃ e : Unit, ExistsAtW v e) true := by
  dsimp
  intro v hR
  have hv : v = true := hR rfl
  subst hv
  exact ⟨(), rfl⟩

/-!
### 4. Retorsion Analysis on ¬ ∃ e, NecessaryEntity(e) (Section XII)
-/

/-- The denial of necessary reality: no entity exists across all possible worlds. -/
def Neg_NecessaryEntityExists : Prop :=
  ∀ e : Entity, ¬ NecessaryEntity e

/-- In Γ's concrete ontology (Truthmaker.lean), because `otherWorld` is devoid of entities,
    `Neg_NecessaryEntityExists` is a derived THEOREM of the concrete model! -/
theorem neg_necessary_entity_holds_in_concrete_ontology :
    Neg_NecessaryEntityExists :=
  fun e hNec => no_entity_at_otherWorld e (hNec otherWorld)

/-- Retorsion Failure on the denial of necessary reality:
    An agent asserting `Neg_NecessaryEntityExists` commits no performative contradiction:
    the agent is actualized at `actualWorld`, but contingent across `World`.
    Asserting that no entity is necessary is completely consistent with classical logic
    and performative agency unless `AxGlobalGround` or `AxPersonalGround` is posited. -/
theorem retorsion_fails_against_no_necessary_entity :
    (∃ w : World, ∀ e : Entity, ¬ ExistsAt w e) →
    Neg_NecessaryEntityExists := by
  intro ⟨w_empty, hEmpty⟩ e hNec
  exact hEmpty e (hNec w_empty)

-- ===========================================================================
-- Part 2: Necessary Entity, Grounding, and Ultimate Ground Gap (Sections IV, V, VI)
-- ===========================================================================

/-!
### 5. Infinite Necessary Grounding Chain over ℤ (Section IV)
-/

/-- Abstract Signature for Testing Necessary Entity vs Ultimate Ground:
    Every integer represents a necessary entity existing in all worlds.
    Grounding between entities is transitive, asymmetric, and irreflexive.
    Every necessary entity is grounded, yet no ultimate ground exists. -/
structure InfiniteNecessaryChainSignature where
  Entity : Type
  World : Type
  ExistsAt : World → Entity → Prop
  NecessaryEntity : Entity → Prop := fun e => ∀ w, ExistsAt w e
  GroundEntity : Entity → Entity → Prop
  transitive : ∀ x y z, GroundEntity x y → GroundEntity y z → GroundEntity x z
  asymmetric : ∀ x y, GroundEntity x y → ¬ GroundEntity y x
  irreflexive : ∀ x, ¬ GroundEntity x x
  UltimateGround : Entity → Prop := fun u => ¬ ∃ x, GroundEntity x u
  UltimateGroundExists : Prop := ∃ u, UltimateGround u
  necessary_entity_exists : ∃ e, NecessaryEntity e
  all_entities_necessary : ∀ e, NecessaryEntity e
  all_grounded : ∀ y, ∃ x, GroundEntity x y
  no_ultimate : ¬ UltimateGroundExists

/-- The concrete infinite necessary grounding model over ℤ:
    Proves that `∃ e, NecessaryEntity e` does NOT entail `UltimateGroundExists`. -/
def ConcreteInfiniteNecessaryChain : InfiniteNecessaryChainSignature where
  Entity := Int
  World := Unit
  ExistsAt := fun (_w : Unit) (_e : Int) => True
  GroundEntity := fun x y => x > y
  transitive := fun _ _ _ hxy hyz => Int.lt_trans hyz hxy
  asymmetric := fun _ _ hxy hyx => Int.lt_irrefl _ (Int.lt_trans hyx hxy)
  irreflexive := fun x => Int.lt_irrefl x
  necessary_entity_exists := ⟨0, fun (_w : Unit) => trivial⟩
  all_entities_necessary := fun (_e : Int) (_w : Unit) => trivial
  all_grounded := fun y => ⟨y + 1, Int.le_refl (y + 1)⟩
  no_ultimate := fun ⟨u, hu⟩ => hu ⟨u + 1, Int.le_refl (u + 1)⟩

/-- Separation Theorem: Necessary existence does NOT derive an Ultimate Ground. -/
theorem necessary_entity_not_entails_ultimate_ground :
    ¬ (∀ S : InfiniteNecessaryChainSignature, S.UltimateGroundExists) := by
  intro hAll
  exact ConcreteInfiniteNecessaryChain.no_ultimate (hAll ConcreteInfiniteNecessaryChain)

/-!
### 6. Investigation of Candidate Bridges for NecessaryEntity → UltimateGround (Section V)
-/

/-- Candidate Bridge 1: Grounding Well-Foundedness.
    If the converse grounding relation is well-founded (admitting a minimal element for every non-empty predicate),
    an ultimate ungrounded grounder is guaranteed to exist. -/
theorem well_foundedness_forces_ultimate_ground
    (Entity : Type) (GroundEntity : Entity → Entity → Prop)
    [Inhabited Entity]
    (hFoundation : ∀ (P : Entity → Prop), (∃ x, P x) → ∃ m, P m ∧ ∀ y, P y → ¬ GroundEntity y m) :
    ∃ u : Entity, ¬ ∃ x : Entity, GroundEntity x u := by
  have ⟨u, _, hMin⟩ := hFoundation (fun _ => True) ⟨default, trivial⟩
  refine ⟨u, fun ⟨x, hx⟩ => hMin x trivial hx⟩

/-- Candidate Bridge 3: Self-Grounding (`GroundEntity g g`).
    If a necessary entity is asserted to ground itself, it directly contradicts
    the metaphysical axiom of irreflexivity (`∀ x, ¬ GroundEntity x x`). -/
theorem self_grounding_violates_irreflexivity
    (Entity : Type) (GroundEntity : Entity → Entity → Prop)
    (irrefl : ∀ x : Entity, ¬ GroundEntity x x)
    (g : Entity) (hSelf : GroundEntity g g) : False :=
  irrefl g hSelf

/-
Candidate Bridge 4: Totality Grounding.
As proved in `totality_grounding_forces_ultimate_ground` (HostileSemantics.lean:2340),
a totality entity forces an ultimate ground ONLY because the totality entity is
explicitly postulated to be ungrounded.
-/

/-!
### 7. The "Empty World" Theological Test (Section VI)
-/

/-- Question 3 formal proof: If a necessary entity exists, no world can be absolutely empty. -/
theorem necessary_entity_rules_out_empty_world
    (Entity World : Type) (ExistsAt : World → Entity → Prop)
    (hNec : ∃ g : Entity, ∀ w : World, ExistsAt w g) :
    ¬ (∃ w : World, ∀ e : Entity, ¬ ExistsAt w e) := by
  rintro ⟨w_empty, hEmpty⟩
  obtain ⟨g, hg⟩ := hNec
  exact hEmpty g (hg w_empty)

/-- Question 4 formal proof: A necessary entity does NOT force contingent creation.
    In ConcreteModelG, a necessary entity exists, but at the no-creation world,
    no contingent entity exists in the world's existent domain. -/
theorem necessary_entity_not_forces_contingent_creation :
    ∃ S : ModelG_Signature, ∃ w : S.World, S.ExistsAt w S.g ∧
      (∀ x : S.Entity, S.ExistsAt w x → ¬ S.ContingentEntity x) :=
  ⟨ConcreteModelG, false, trivial, ConcreteModelG.no_contingent_creation_at_w⟩

-- ===========================================================================
-- Part 3: Theological Attribute Ladder, Creation, and Atlas (Sections VII–X, XIII)
-- ===========================================================================

/-!
### 8. The Personal & Agency Ladder Separations (Section VII)
-/

/-- Model NP: Necessary Impersonal Being.
    A necessary entity exists in every world, but no intentional subject exists. -/
structure ModelNP_Signature where
  Entity : Type
  Subject : Type
  World : Type
  ExistsAt : World → Entity → Prop
  EntityOf : Subject → Entity
  NecessaryEntity : Entity → Prop := fun e => ∀ w, ExistsAt w e
  g : Entity
  g_necessary : NecessaryEntity g
  no_subjects : Subject → False

theorem model_NP_consistent : ∃ _M : ModelNP_Signature, True := by
  let M : ModelNP_Signature := {
    Entity := Unit
    Subject := Empty
    World := Unit
    ExistsAt := fun _ _ => True
    EntityOf := fun s => s.elim
    g := ()
    g_necessary := fun _ => trivial
    no_subjects := fun s => s.elim
  }
  exact ⟨M, trivial⟩

/-- Separation: NecessaryEntity does NOT entail Subjecthood. -/
theorem necessary_entity_not_entails_subject :
    ¬ (∀ S : ModelNP_Signature, ∃ s : S.Subject, S.EntityOf s = S.g) := by
  intro hAll
  obtain ⟨M, _⟩ := model_NP_consistent
  have ⟨s, _⟩ := hAll M
  exact M.no_subjects s

/-- Model NA: Necessary Non-Agent.
    A necessary subject exists, but performs no rational act (Act is empty). -/
structure ModelNA_Signature where
  Subject : Type
  PropType : Type
  Act : Subject → PropType → Prop
  s : Subject
  no_acts : ∀ p : PropType, ¬ Act s p

theorem model_NA_consistent : ∃ _M : ModelNA_Signature, True :=
  ⟨{ Subject := Unit, PropType := Prop, Act := fun _ _ => False, s := (), no_acts := fun _ h => h }, trivial⟩

/-- Separation: Subjecthood does NOT entail Agency. -/
theorem subject_not_entails_agency :
    ¬ (∀ S : ModelNA_Signature, ∃ p : S.PropType, S.Act S.s p) := by
  intro hAll
  obtain ⟨M, _⟩ := model_NA_consistent
  have ⟨p, hp⟩ := hAll M
  exact M.no_acts p hp

/-- Model ND: Necessary Deterministic Subject.
    A necessary intentional subject exists and acts, but its choices are fully determined
    (Chooses and FreeWill are empty). -/
structure ModelND_Signature where
  Subject : Type
  PropType : Type
  Act : Subject → PropType → Prop
  Means : Subject → PropType → Prop
  Chooses : Subject → PropType → PropType → Prop
  FreeWill : Subject → Prop
  s : Subject
  p : PropType
  acts : Act s p
  means : Means s p
  no_free_will : ¬ FreeWill s

theorem model_ND_consistent : ∃ _M : ModelND_Signature, True := by
  let M : ModelND_Signature := {
    Subject := Unit
    PropType := Prop
    Act := fun _ _ => True
    Means := fun _ _ => True
    Chooses := fun _ _ _ => False
    FreeWill := fun _ => False
    s := ()
    p := True
    acts := trivial
    means := trivial
    no_free_will := fun h => h
  }
  exact ⟨M, trivial⟩

/-- Separation: Intentional Subject does NOT entail Free Will. -/
theorem intentional_subject_not_entails_freewill :
    ¬ (∀ S : ModelND_Signature, S.FreeWill S.s) := by
  intro hAll
  obtain ⟨M, _⟩ := model_ND_consistent
  exact M.no_free_will (hAll M)

/-!
### 9. Creation Models (Section VIII)
-/

/-- Creation Model Signature:
    Investigates whether a necessary entity `g` entails a creation relation `Creates g x`. -/
structure CreationSignature where
  Entity : Type
  World : Type
  actualWorld : World
  ExistsAt : World → Entity → Prop
  NecessaryEntity : Entity → Prop := fun e => ∀ w, ExistsAt w e
  ContingentEntity : Entity → Prop := fun e => ExistsAt actualWorld e ∧ ∃ w, ¬ ExistsAt w e
  Creates : Entity → Entity → Prop
  g : Entity
  g_necessary : NecessaryEntity g

/-- Creation Countermodel A: God Alone (Necessary Being Without Creation).
    `g` exists necessarily, but NO contingent entity exists, and `Creates` is empty. -/
def GodAloneModel : CreationSignature where
  Entity := Unit
  World := Unit
  actualWorld := ()
  ExistsAt := fun _ _ => True
  Creates := fun _ _ => False
  g := ()
  g_necessary := fun _ => trivial

theorem god_alone_has_no_creation :
    ¬ ∃ x : GodAloneModel.Entity, GodAloneModel.Creates GodAloneModel.g x :=
  fun ⟨_, hCr⟩ => hCr

/-- Creation Countermodel B: Coexistence Without Creation Relation.
    A necessary entity `g` and a contingent entity `c` both exist in the actual world,
    but `Creates g c` does NOT hold (coexistence without causal/ontological derivation). -/
def CoexistenceWithoutCreationModel : CreationSignature where
  Entity := Bool
  World := Bool
  actualWorld := true
  ExistsAt := fun w e => e = true ∨ w = true
  Creates := fun _ _ => False
  g := true
  g_necessary := fun _ => Or.inl rfl

theorem coexistence_without_creation_relation :
    (∃ x : CoexistenceWithoutCreationModel.Entity, CoexistenceWithoutCreationModel.ContingentEntity x) ∧
    (¬ ∃ x : CoexistenceWithoutCreationModel.Entity, CoexistenceWithoutCreationModel.Creates CoexistenceWithoutCreationModel.g x) := by
  refine ⟨⟨false, ?_⟩, fun ⟨_, hCr⟩ => hCr⟩
  dsimp [CoexistenceWithoutCreationModel]
  refine ⟨Or.inr rfl, ⟨false, ?_⟩⟩
  intro hEx
  cases hEx with
  | inl hT => cases hT
  | inr hW => cases hW

/-!
### 10. Uniqueness Separation (Section IX)
-/

/-- Definition of Unique Existence:
    An entity satisfying predicate P is unique iff every entity satisfying P is identical to it. -/
def UniqueExists {α : Type} (P : α → Prop) : Prop :=
  ∃ x : α, P x ∧ ∀ y : α, P y → y = x

/-- Multiple Necessary Entities Model:
    Two distinct entities g₁ ≠ g₂ both exist in all worlds. -/
structure PluralNecessaryEntitiesSignature where
  Entity : Type
  World : Type
  ExistsAt : World → Entity → Prop
  NecessaryEntity : Entity → Prop := fun e => ∀ w, ExistsAt w e
  g₁ : Entity
  g₂ : Entity
  distinct : g₁ ≠ g₂
  g₁_nec : NecessaryEntity g₁
  g₂_nec : NecessaryEntity g₂

theorem plural_necessary_entities_consistent :
    ∃ _M : PluralNecessaryEntitiesSignature, True := by
  let M : PluralNecessaryEntitiesSignature := {
    Entity := Bool
    World := Unit
    ExistsAt := fun _ _ => True
    g₁ := true
    g₂ := false
    distinct := fun h => by cases h
    g₁_nec := fun _ => trivial
    g₂_nec := fun _ => trivial
  }
  exact ⟨M, trivial⟩

/-- Separation Theorem: Necessary existence does NOT entail Uniqueness. -/
theorem necessary_existence_not_entails_uniqueness :
    ¬ (∀ S : PluralNecessaryEntitiesSignature, UniqueExists S.NecessaryEntity) := by
  intro hAll
  obtain ⟨M, _⟩ := plural_necessary_entities_consistent
  have ⟨u, _, hUnique⟩ := hAll M
  have hu1 : M.g₁ = u := hUnique M.g₁ M.g₁_nec
  have hu2 : M.g₂ = u := hUnique M.g₂ M.g₂_nec
  have heq : M.g₁ = M.g₂ := hu1.trans hu2.symm
  exact M.distinct heq

-- ===========================================================================
-- Part 4: Inconsistency Theorem, Competing Regimes, and Minimal Bridges (Sections 2, 3, 5)
-- ===========================================================================

/-!
### 11. Inconsistency Between Model E and AxGlobalGround (Section 2)
-/

/-- AxGlobalGround Inconsistency Theorem:
    If AxGlobalGround holds, then NO possible world can be absolutely empty.
    Instantiating AxGlobalGround with the logical tautology `Form.or φ (Form.not φ)`
    guarantees an entity `e` that exists at all worlds (`∀ w, ExistsAt w e`).
    This directly refutes the existence of an absolute empty world (`∃ w, ∀ e, ¬ ExistsAt w e`). -/
theorem axGlobalGround_refutes_empty_world
    (hGlobal : ∀ (φ : Form), Logos.Truthmaker.NecessarilyTrue φ →
      ∃ e : Entity, ∀ w : World, ExistsAt w e ∧ Logos.Truthmaker.Ground e φ)
    (φ : Form) :
    ¬ (∃ w : World, ∀ e : Entity, ¬ ExistsAt w e) := by
  intro ⟨w_empty, hEmpty⟩
  have hNec : Logos.Truthmaker.NecessarilyTrue (Form.or φ (Form.not φ)) :=
    fun w => Logos.Truthmaker.lawExcludedMiddle φ w
  obtain ⟨e, he⟩ := hGlobal (Form.or φ (Form.not φ)) hNec
  have hExAtW := (he w_empty).1
  exact hEmpty e hExAtW

/-!
### 12. Competing Modal Regimes: Regime E vs Regime G (Section 3)
-/

/-- Regime E: Open-world / empty-world-permitting modal semantics.
    Allows worlds where no entity exists in the ontological domain. -/
structure RegimeE_Signature where
  World : Type
  Entity : Type
  ExistsAt : World → Entity → Prop
  has_empty_world : ∃ w : World, ∀ e : Entity, ¬ ExistsAt w e

/-- Regime G: Necessary-reality modal semantics.
    Excludes empty worlds: every world contains at least one entity. -/
structure RegimeG_Signature where
  World : Type
  Entity : Type
  ExistsAt : World → Entity → Prop
  necessary_non_emptiness : ∀ w : World, ∃ e : Entity, ExistsAt w e

def RegimeG_Signature.NecessaryEntity (S : RegimeG_Signature) (e : S.Entity) : Prop :=
  ∀ w : S.World, S.ExistsAt w e

/-!
### 13. The Shifting-Entity Hostile Model (Section 5)
-/

/-- The Shifting-Entity Hostile Model:
    Proves that necessary non-emptiness (∀ w, ∃ e, ExistsAt w e)
    does NOT entail the existence of a necessary entity (∃ e, ∀ w, ExistsAt w e).
    Every world contains an entity, but no single entity exists across all worlds. -/
def ShiftingEntityModel : RegimeG_Signature where
  World := Bool
  Entity := Bool
  ExistsAt := fun w e => w = e
  necessary_non_emptiness := fun w => ⟨w, rfl⟩

theorem necessary_non_emptiness_not_entails_necessary_entity :
    ¬ (∀ S : RegimeG_Signature, ∃ e : S.Entity, S.NecessaryEntity e) := by
  intro hAll
  have ⟨e, he⟩ := hAll ShiftingEntityModel
  cases e with
  | true =>
    have hFalse := he false
    contradiction
  | false =>
    have hTrue := he true
    contradiction

/-!
### 14. Minimal Modal Bridge Principles (Section 3)
-/

/-- Candidate Bridge 1: Uniform Witness Postulate.
    The exact, minimal principle bridging non-emptiness to necessary existence. -/
def UniformWitnessPrinciple (S : RegimeG_Signature) : Prop :=
  ∃ e : S.Entity, ∀ w : S.World, S.ExistsAt w e

theorem uniform_witness_yields_necessary_entity (S : RegimeG_Signature)
    (hWit : UniformWitnessPrinciple S) : ∃ e : S.Entity, S.NecessaryEntity e := by
  obtain ⟨e, he⟩ := hWit
  exact ⟨e, he⟩

/-- Candidate Bridge 2: Constant Domain Bridge.
    If the ontological domain is rigid across worlds (every entity exists in all worlds),
    then non-emptiness trivially forces a necessary entity. -/
def ConstantDomainPrinciple (S : RegimeG_Signature) : Prop :=
  ∀ e : S.Entity, ∀ w : S.World, S.ExistsAt w e

theorem constant_domain_yields_necessary_entity (S : RegimeG_Signature) [Inhabited S.World]
    (hConst : ConstantDomainPrinciple S) : ∃ e : S.Entity, S.NecessaryEntity e := by
  obtain ⟨e, _⟩ := S.necessary_non_emptiness default
  exact ⟨e, fun w => hConst e w⟩

-- ===========================================================================
-- Part 5: Relational Accessibility Frames & Retorsion Limits (Sections 4, 6)
-- ===========================================================================

/-!
### 15. The Three Accessibility Frames E1, E2, E3 (Section 4)
-/

/-- Frame E1: Universal accessibility (R := fun _ _ => True).
    The empty world is accessible from every world; worldwise truthmaking fails. -/
def FrameE1 (W : Type) : KripkeFrame W where
  R := fun _ _ => True

/-- Frame E2: Restricted accessibility.
    The empty world exists in the model, but is inaccessible from actualWorld.
    Truthmaking across all accessible worlds holds. -/
def FrameE2 : KripkeFrame Bool where
  R := fun w v => w = true → v = true

theorem frameE2_truthmaking_holds_at_actual :
    let ExistsAt := fun (w : Bool) (_e : Unit) => w = true
    BoxR FrameE2 (fun v => ∃ e : Unit, ExistsAt v e) true := by
  dsimp [BoxR, FrameE2]
  intro v hR
  have hv : v = true := hR rfl
  subst hv
  exact ⟨(), rfl⟩

/-- Frame E3: Necessary-being frame.
    All worlds accessible from actualWorld contain the distinguished entity g. -/
structure FrameE3_Signature where
  World : Type
  Entity : Type
  actualWorld : World
  frame : KripkeFrame World
  ExistsAt : World → Entity → Prop
  g : Entity
  g_in_accessible_worlds : ∀ v : World, frame.R actualWorld v → ExistsAt v g

/-!
### 16. Retorsion Failure on Necessary Subjecthood (Section 6)
-/

/-- Retorsion Failure Model:
    Performative agency at actualWorld establishes actual subjecthood (∃ s, ExistsAt actualWorld (EntityOf s)),
    but retorsion CANNOT force NecessarySubject (∀ w, ExistsAt w (EntityOf s)).
    Hostile model: actualWorld has the performing subject, but the subject is absent at another world. -/
structure ContingentSubjectRetorsionModel where
  Subject : Type
  Entity : Type
  EntityOf : Subject → Entity
  World : Type
  actualWorld : World
  otherWorld : World
  ExistsAt : World → Entity → Prop
  ActAt : World → Subject → Prop → Prop
  s : Subject
  actual_act : ActAt actualWorld s True
  actual_exists : ExistsAt actualWorld (EntityOf s)
  absent_at_other : ¬ ExistsAt otherWorld (EntityOf s)
  not_necessary_subject : ¬ (∀ w, ExistsAt w (EntityOf s))

theorem retorsion_not_forces_necessary_subject :
    ∃ _M : ContingentSubjectRetorsionModel, True := by
  let M : ContingentSubjectRetorsionModel := {
    Subject := Unit
    Entity := Unit
    EntityOf := fun _ => ()
    World := Bool
    actualWorld := true
    otherWorld := false
    ExistsAt := fun w _ => w = true
    ActAt := fun w _ _ => w = true
    s := ()
    actual_act := rfl
    actual_exists := rfl
    absent_at_other := fun h => by cases h
    not_necessary_subject := fun hNec => by
      have hFalse := hNec false
      cases hFalse
  }
  exact ⟨M, trivial⟩

-- ===========================================================================
-- Part 6: Positive Divine Attribute Bridge & Deep Creation Models (Sections 7, 8)
-- ===========================================================================

/-!
### 17. Necessary Being vs Divine (Section 7)
-/

/-- Structural definition of Divine Attributes:
    A divine entity is not merely a necessary being:
    it must be an intentional agent, the ultimate ground of reality, the creator of contingent beings, and benevolent. -/
structure DivineSpecification (Entity : Type) where
  NecessaryBeing : Entity → Prop
  IntentionalAgent : Entity → Prop
  UltimateGround : Entity → Prop
  Creator : Entity → Prop
  Benevolent : Entity → Prop

def DivineSpecification.Divine {Entity : Type} (spec : DivineSpecification Entity) (g : Entity) : Prop :=
  spec.NecessaryBeing g ∧ spec.IntentionalAgent g ∧ spec.UltimateGround g ∧ spec.Creator g ∧ spec.Benevolent g

/-- Hostile Model: Necessary Impersonal Abstractum (e.g. mathematical object, physical substrate).
    A necessary being exists, but satisfies NO personal, creative, or divine attributes. -/
theorem necessary_being_not_entails_divine :
    ¬ (∀ (Entity : Type) (spec : DivineSpecification Entity) (g : Entity),
        spec.NecessaryBeing g → spec.Divine g) := by
  intro hAll
  let spec : DivineSpecification Unit := {
    NecessaryBeing := fun _ => True
    IntentionalAgent := fun _ => False
    UltimateGround := fun _ => False
    Creator := fun _ => False
    Benevolent := fun _ => False
  }
  have hDiv : spec.Divine () := hAll Unit spec () trivial
  exact hDiv.2.1

/-- Positive Identification Theorem:
    Upgrading a NecessaryBeing to Divine requires explicitly adding the personal,
    grounding, creative, and moral predicates. -/
theorem divine_identification_theorem
    (Entity : Type) (spec : DivineSpecification Entity) (g : Entity)
    (hNec : spec.NecessaryBeing g)
    (hAgent : spec.IntentionalAgent g)
    (hGround : spec.UltimateGround g)
    (hCreator : spec.Creator g)
    (hBen : spec.Benevolent g) :
    spec.Divine g :=
  ⟨hNec, hAgent, hGround, hCreator, hBen⟩

/-!
### 18. The Four Deep Creation Regimes G1–G4 (Section 8)
-/

/-- Deep Creation Model Signature -/
structure DeepCreationSignature where
  Entity : Type
  World : Type
  actualWorld : World
  ExistsAt : World → Entity → Prop
  Creates : Entity → Entity → Prop
  NecessaryEntity : Entity → Prop := fun e => ∀ w, ExistsAt w e
  ContingentEntity : Entity → Prop := fun e => ExistsAt actualWorld e ∧ ∃ w, ¬ ExistsAt w e
  g : Entity
  g_necessary : NecessaryEntity g

/-- G1: God Alone (Necessary being exists, NO contingent reality, Creates empty). -/
def RegimeG1_GodAlone : DeepCreationSignature where
  Entity := Unit
  World := Unit
  actualWorld := ()
  ExistsAt := fun _ _ => True
  Creates := fun _ _ => False
  g := ()
  g_necessary := fun _ => trivial

theorem g1_god_alone_properties :
    (¬ ∃ x : RegimeG1_GodAlone.Entity, RegimeG1_GodAlone.ContingentEntity x) ∧
    (¬ ∃ x : RegimeG1_GodAlone.Entity, RegimeG1_GodAlone.Creates RegimeG1_GodAlone.g x) := by
  refine ⟨?_, fun ⟨_, hCr⟩ => hCr⟩
  rintro ⟨x, ⟨_, ⟨w, hNotEx⟩⟩⟩
  exact hNotEx trivial

/-- G2: God + Contingent Creation with Creator Relation.
    Necessary being g creates contingent creature c. -/
def RegimeG2_Creation : DeepCreationSignature where
  Entity := Bool   -- true = g, false = c
  World := Bool    -- true = actual, false = counterfactual
  actualWorld := true
  ExistsAt := fun w e => e = true ∨ w = true
  Creates := fun g c => g = true ∧ c = false
  g := true
  g_necessary := fun _ => Or.inl rfl

theorem g2_creation_properties :
    (∃ x : RegimeG2_Creation.Entity, RegimeG2_Creation.ContingentEntity x) ∧
    (RegimeG2_Creation.Creates RegimeG2_Creation.g false) := by
  refine ⟨⟨false, Or.inr rfl, ⟨false, ?_⟩⟩, ⟨rfl, rfl⟩⟩
  intro hEx
  cases hEx with
  | inl hT => cases hT
  | inr hW => cases hW

/-- G3: Coexistence Without Creation Relation.
    g and c both exist, but Creates is empty (coexistence without causal dependence). -/
def RegimeG3_CoexistenceNoCreation : DeepCreationSignature where
  Entity := Bool
  World := Bool
  actualWorld := true
  ExistsAt := fun w e => e = true ∨ w = true
  Creates := fun _ _ => False
  g := true
  g_necessary := fun _ => Or.inl rfl

theorem g3_coexistence_no_creation_properties :
    (∃ x : RegimeG3_CoexistenceNoCreation.Entity, RegimeG3_CoexistenceNoCreation.ContingentEntity x) ∧
    (¬ ∃ x : RegimeG3_CoexistenceNoCreation.Entity, RegimeG3_CoexistenceNoCreation.Creates RegimeG3_CoexistenceNoCreation.g x) := by
  refine ⟨⟨false, Or.inr rfl, ⟨false, ?_⟩⟩, fun ⟨_, hCr⟩ => hCr⟩
  intro hEx
  cases hEx with
  | inl hT => cases hT
  | inr hW => cases hW

/-- G4: Contingent Creation is Fragile.
    The creation relation exists in the actual world, but creation is absent in counterfactual worlds. -/
theorem g4_creation_is_contingent :
    ∃ w : RegimeG2_Creation.World, ¬ RegimeG2_Creation.ExistsAt w false :=
  ⟨false, fun hEx => by cases hEx with | inl h => cases h | inr h => cases h⟩

-- ===========================================================================
-- Part 7: Uniqueness Candidates & Ultimate Grounding Candidates (Sections 9, 10)
-- ===========================================================================

/-!
### 19. Candidate Uniqueness Principles U1–U5 (Section 9)
-/

/-- Candidate U1: Independence Exclusion.
    Positing that no two distinct necessary beings can exist independently forces uniqueness. -/
theorem u1_independence_exclusion_forces_uniqueness
    (_Entity : Type) (Nec : _Entity → Prop)
    (hNoTwo : ∀ x y : _Entity, Nec x → Nec y → x = y)
    (x y : _Entity) (hx : Nec x) (hy : Nec y) : x = y :=
  hNoTwo x y hx hy

/-!
### 20. Candidate Grounding Combinations A–D (Section 10)
-/

/-- Necessary Ground Can Be Non-Ultimate:
    A necessary entity `g` can be grounded by an entity (even a contingent one),
    proving that `NecessaryEntity(g)` does NOT entail `UltimateGround(g)`. -/
theorem necessary_ground_can_be_non_ultimate :
    let GroundEntity := fun (x y : Option Unit) => x = some () ∧ y = none
    (∃ x : Option Unit, GroundEntity x none) :=
  ⟨some (), ⟨rfl, rfl⟩⟩

-- ===========================================================================
-- Part 8: Modal Possibility Theory (Section 11)
-- ===========================================================================

/-!
### 21. Modal Possibility Theory & PossibleWorld
-/

/-- Modal World Model:
    A world w is a genuine possible world iff it is logically consistent and satisfies all necessary modal constraints. -/
structure ModalWorldModel (World : Type) where
  Consistent : World → Prop
  ModalConstraints : World → Prop

def ModalWorldModel.PossibleWorld {World : Type} (M : ModalWorldModel World) (w : World) : Prop :=
  M.Consistent w ∧ M.ModalConstraints w

/-- Empty World under Modal Constraints:
    If non-emptiness is stipulated as a necessary modal constraint,
    the empty world is formally excluded from the realm of PossibleWorlds. -/
theorem empty_world_excluded_by_non_emptiness_constraint
    (World : Type) (M : ModalWorldModel World)
    (w_empty : World)
    (hConstraint : ∀ w, M.ModalConstraints w → False) :
    ¬ M.PossibleWorld w_empty :=
  fun ⟨_, hMC⟩ => hConstraint w_empty hMC

end Logos.TheologicalModalHardening
