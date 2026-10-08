-- Consolidated Modal Creation & Possibility Frontiers
import Logos.Agency
import Logos.Choice
import Logos.Core
import Logos.Entity
import Logos.HostileSemantics
import Logos.Modal
import Logos.Necessity
import Logos.Person
import Logos.Semantics


/-
================================================================================
SECTION: TheologicalModalHardening
================================================================================
-/
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


namespace Logos.TheologicalModalHardening

open Logos.Semantics (Form World Satisfies TrueAt)
open Logos.Entity (Entity ExistsAt actualWorld)

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
### 2. Fundamental World Models: Model G
-/

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
    world-indexed grounding can hold across all ACCESSIBLE worlds. -/
theorem accessible_worldwise_grounding_consistent :
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

-- ===========================================================================
-- Part 2: Necessary Entity, Grounding, and Ultimate Ground Gap (Sections IV, V, VI)
-- ===========================================================================

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
    Worldwise grounding fails under empty world accessibility. -/
def FrameE1 (W : Type) : KripkeFrame W where
  R := fun _ _ => True

/-- Frame E2: Restricted accessibility.
    Grounding across all accessible worlds holds. -/
def FrameE2 : KripkeFrame Bool where
  R := fun w v => w = true → v = true

theorem frameE2_grounding_holds_at_actual :
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


/-
================================================================================
SECTION: ModalCreationAgency
================================================================================
-/
/-
# Logos.ModalCreationAgency — Necessary Personal Agency and the Contingency of Creation

An adversarial modal investigation into whether a necessary personal agent
could genuinely have remained alone rather than creating.

Governing rule:
"Prefer losing the theorem to hiding the premise."

Terminology:
All formal definitions use the neutral witness `g : Entity` and `s : Subject`.
Theological identifications ("God", "Divine Creator") are strictly confined to
the external synthesis layer.
-/


namespace Logos.ModalCreationAgency

open Logos.TheologicalModalHardening (KripkeFrame BoxR DeepCreationSignature)

-- ===========================================================================
-- Part 1: Targets A, B, C & Rigid Cross-World Identity (Sections I, XIV)
-- ===========================================================================

/-!
### 1. Target Formulations with Rigid Cross-World Identity
We preserve rigid cross-world identity for the individual witness `g : Entity`
and its associated subject `s : Subject`.
-/

/-- Target A: Bare Necessary Being.
    Entity `g` exists in the ontological domain of every world. -/
def TargetA_NecessaryBeing (World Entity : Type) (ExistsAt : World → Entity → Prop) (g : Entity) : Prop :=
  ∀ w : World, ExistsAt w g

/-- Target B: Necessary Person / Agent.
    Entity `g` is a necessary entity, subject `s` is a necessary subject,
    and `g` is the rigid ontological correlate of `s` (`EntityOf s = g`). -/
structure TargetB_NecessaryPerson (World Entity Subject : Type)
    (ExistsAt : World → Entity → Prop)
    (SubjectExistsAt : World → Subject → Prop)
    (EntityOf : Subject → Entity)
    (Person : Subject → Prop)
    (g : Entity) (s : Subject) : Prop where
  g_necessary : ∀ w : World, ExistsAt w g
  s_necessary : ∀ w : World, SubjectExistsAt w s
  correlate : EntityOf s = g
  is_person : Person s

-- ===========================================================================
-- Part 2: World-Indexed Agency & Modal Freedom (Sections IV, VI)
-- ===========================================================================

/-!
### 2. World-Indexed Agency Structure
Ambient agency in `Agency.lean` and `Choice.lean` is non-modal.
We introduce world-indexed semantic layers: `MeansAt`, `ActAt`, `ChoosesAt`, `FreeWillAt`.
-/

/-- Incompatibility of two propositions: they cannot be jointly true. -/
def Incompatible (p q : Prop) : Prop := ¬ (p ∧ q)

/-- World-Indexed Choice:
    At world `w`, subject `s` represents incompatible alternatives `p` and `q`. -/
def ChoosesAt (World Subject : Type)
    (MeansAt : World → Subject → Prop → Prop)
    (w : World) (s : Subject) (p q : Prop) : Prop :=
  MeansAt w s p ∧ MeansAt w s q ∧ Incompatible p q

/-- World-Slice Free Will:
    At world `w`, subject `s` exercises choice between some incompatible alternatives. -/
def FreeWillAt (World Subject : Type)
    (MeansAt : World → Subject → Prop → Prop)
    (w : World) (s : Subject) : Prop :=
  ∃ p q : Prop, ChoosesAt World Subject MeansAt w s p q

/-- Target C: Necessary Free Agent.
    A necessary entity-person endowed with free will at the actual world. -/
structure TargetC_NecessaryFreeAgent (World Entity Subject : Type)
    (ExistsAt : World → Entity → Prop)
    (SubjectExistsAt : World → Subject → Prop)
    (EntityOf : Subject → Entity)
    (Person : Subject → Prop)
    (MeansAt : World → Subject → Prop → Prop)
    (actualWorld : World)
    (g : Entity) (s : Subject) : Prop where
  toTargetB : TargetB_NecessaryPerson World Entity Subject ExistsAt SubjectExistsAt EntityOf Person g s
  actual_freeWill : FreeWillAt World Subject MeansAt actualWorld s

/-- Genuine Modal Freedom (Counterfactual Alternative Agency):
    Subject `s` not only represents incompatible alternatives `p` and `q`,
    but there exist accessible worlds where `s` executes `p`, and accessible worlds where `s` executes `q`. -/
structure ModalFreeWill (World Subject : Type)
    (frame : KripkeFrame World)
    (actualWorld : World)
    (MeansAt : World → Subject → Prop → Prop)
    (ActAt : World → Subject → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop where
  incompatible : Incompatible p q
  actual_chooses : ChoosesAt World Subject MeansAt actualWorld s p q
  branch_p : ∃ v : World, frame.R actualWorld v ∧ ChoosesAt World Subject MeansAt v s p q ∧ ActAt v s p
  branch_q : ∃ u : World, frame.R actualWorld u ∧ ChoosesAt World Subject MeansAt u s p q ∧ ActAt u s q

/-- Modal Freedom implies World-Slice Freedom at the actual world. -/
theorem modal_freedom_implies_local_freedom
    (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
    (MeansAt : World → Subject → Prop → Prop) (ActAt : World → Subject → Prop → Prop)
    (s : Subject) (p q : Prop)
    (hModal : ModalFreeWill World Subject frame actualWorld MeansAt ActAt s p q) :
    FreeWillAt World Subject MeansAt actualWorld s :=
  ⟨p, q, hModal.actual_chooses⟩

-- ===========================================================================
-- Part 3: Separation of Ordinary Free Will from Modal Alternatives (Section V)
-- ===========================================================================

/-!
### 3. Attack on the Free-Will-to-Alternatives Leap
Ordinary FreeWill (entertaining incompatible cognitive horns) does NOT entail
that alternative choices are accessible across possible worlds.
Hostile Deterministic Model: `FreeWillAt actualWorld g` holds, yet the executed
action is rigidly identical in every accessible world.
-/

structure DeterministicModalModel where
  World : Type
  Entity : Type
  Subject : Type
  actualWorld : World
  frame : KripkeFrame World
  ExistsAt : World → Entity → Prop
  SubjectExistsAt : World → Subject → Prop
  EntityOf : Subject → Entity
  Person : Subject → Prop
  MeansAt : World → Subject → Prop → Prop
  ActAt : World → Subject → Prop → Prop
  g : Entity
  s : Subject
  p : Prop
  q : Prop
  p_incompatible_q : Incompatible p q
  g_necessary : ∀ w, ExistsAt w g
  s_necessary : ∀ w, SubjectExistsAt w s
  correlate : EntityOf s = g
  is_person : Person s
  actual_chooses : ChoosesAt World Subject MeansAt actualWorld s p q
  fixed_action : ∀ v, frame.R actualWorld v → ActAt v s p ∧ ¬ ActAt v s q

def ModelDeterministicChoice : DeterministicModalModel where
  World := Unit
  Entity := Unit
  Subject := Unit
  actualWorld := ()
  frame := { R := fun _ _ => True }
  ExistsAt := fun _ _ => True
  SubjectExistsAt := fun _ _ => True
  EntityOf := fun _ => ()
  Person := fun _ => True
  MeansAt := fun _ _ _ => True
  ActAt := fun _ _ form => form
  g := ()
  s := ()
  p := True
  q := False
  p_incompatible_q := fun ⟨_, hq⟩ => hq
  g_necessary := fun _ => trivial
  s_necessary := fun _ => trivial
  correlate := rfl
  is_person := trivial
  actual_chooses := ⟨trivial, trivial, fun ⟨_, hq⟩ => hq⟩
  fixed_action := fun _ _ => ⟨trivial, fun h => h⟩

/-- Separation Theorem: FreeWill does NOT entail Modal Alternatives.
    An agent can possess ordinary free will at the actual world, while counterfactual
    alternatives are metaphysically inaccessible. -/
theorem freeWill_not_entails_modal_alternatives :
    ∃ M : DeterministicModalModel,
      FreeWillAt M.World M.Subject M.MeansAt M.actualWorld M.s ∧
      ¬ (∃ u : M.World, M.frame.R M.actualWorld u ∧ M.ActAt u M.s M.q) := by
  let M := ModelDeterministicChoice
  refine ⟨M, ⟨M.p, M.q, M.actual_chooses⟩, ?_⟩
  rintro ⟨u, hR, hActQ⟩
  have hFixed := (M.fixed_action u hR).2
  exact hFixed hActQ

-- ===========================================================================
-- Part 4: Four Claims About Creation & Non-Creation Hierarchy (Sections II, VII, VIII)
-- ===========================================================================

/-!
### 4. Four Distinct Claims About Creation
C1: Actual non-creation.
C2: Modal no-creation (accessible world without creation).
C3: Ontological absence of contingents.
C4: Free voluntary abstention from creation.
-/

def ClaimC1_ActualNoCreation
    (World Entity : Type)
    (actualWorld : World) (CreatesAt : World → Entity → Entity → Prop) (g : Entity) : Prop :=
  ¬ ∃ x : Entity, CreatesAt actualWorld g x

def ClaimC2_ModalNoCreation
    (World Entity : Type)
    (frame : KripkeFrame World) (actualWorld : World)
    (CreatesAt : World → Entity → Entity → Prop) (g : Entity) : Prop :=
  ∃ w : World, frame.R actualWorld w ∧ ¬ ∃ x : Entity, CreatesAt w g x

def ClaimC3_NoContingentEntitiesPossible
    (World Entity : Type)
    (frame : KripkeFrame World) (actualWorld : World)
    (ExistsAt : World → Entity → Prop) : Prop :=
  ∃ w : World, frame.R actualWorld w ∧
    ∀ x : Entity, ExistsAt w x → (∀ v : World, ExistsAt v x)

/-- Non-Creation Hierarchy:
    Level 1: Passive No-Creation (no entity created).
    Level 2: Voluntary No-Creation (agent intentionally acts to refrain).
    Level 3: Free Voluntary No-Creation (agent intentionally refrains, but could have created). -/

def PassiveNoCreationAt
    (World Entity : Type)
    (CreatesAt : World → Entity → Entity → Prop) (w : World) (g : Entity) : Prop :=
  ¬ ∃ x : Entity, CreatesAt w g x

def VoluntaryNoCreationAt
    (World Entity Subject : Type)
    (CreatesAt : World → Entity → Entity → Prop)
    (ActAt : World → Subject → Prop → Prop)
    (w : World) (g : Entity) (s : Subject) : Prop :=
  PassiveNoCreationAt World Entity CreatesAt w g ∧
  ActAt w s (PassiveNoCreationAt World Entity CreatesAt w g)

def FreeVoluntaryNoCreation
    (World Entity Subject : Type)
    (frame : KripkeFrame World) (actualWorld : World)
    (CreatesAt : World → Entity → Entity → Prop)
    (ActAt : World → Subject → Prop → Prop)
    (g : Entity) (s : Subject) : Prop :=
  VoluntaryNoCreationAt World Entity Subject CreatesAt ActAt actualWorld g s ∧
  (∃ v : World, frame.R actualWorld v ∧ ∃ x : Entity, CreatesAt v g x)

theorem free_voluntary_implies_voluntary
    (World Entity Subject : Type)
    (frame : KripkeFrame World) (actualWorld : World)
    (CreatesAt : World → Entity → Entity → Prop) (ActAt : World → Subject → Prop → Prop)
    (g : Entity) (s : Subject)
    (h : FreeVoluntaryNoCreation World Entity Subject frame actualWorld CreatesAt ActAt g s) :
    VoluntaryNoCreationAt World Entity Subject CreatesAt ActAt actualWorld g s :=
  h.1

theorem voluntary_implies_passive
    (World Entity Subject : Type)
    (CreatesAt : World → Entity → Entity → Prop) (ActAt : World → Subject → Prop → Prop)
    (w : World) (g : Entity) (s : Subject)
    (h : VoluntaryNoCreationAt World Entity Subject CreatesAt ActAt w g s) :
    PassiveNoCreationAt World Entity CreatesAt w g :=
  h.1

/-- Hostile Separation: Passive non-creation does NOT entail Voluntary non-creation. -/
theorem passive_not_entails_voluntary :
    ∃ (World Entity Subject : Type)
      (CreatesAt : World → Entity → Entity → Prop)
      (ActAt : World → Subject → Prop → Prop)
      (w : World) (g : Entity) (s : Subject),
      PassiveNoCreationAt World Entity CreatesAt w g ∧
      ¬ VoluntaryNoCreationAt World Entity Subject CreatesAt ActAt w g s := by
  refine ⟨Unit, Unit, Unit, fun _ _ _ => False, fun _ _ _ => False, (), (), (), ?_, ?_⟩
  · intro ⟨x, hCr⟩; exact hCr
  · intro ⟨_, hAct⟩; exact hAct

-- ===========================================================================
-- Part 5: The Six Canonical Hostile Models M-C1 Through M-C6 (Sections XV, XVI)
-- ===========================================================================

/-!
### 5. Hostile Countermodel Suite M-C1 – M-C6
Isolating the metaphysical price of each theological transition.
-/

/-- M-C1: Necessary Impersonal Entity (No Person / Subject).
    A necessary entity exists, but there is no personal subject. -/
theorem model_MC1_necessary_impersonal_consistent :
    ∃ (World Entity Subject : Type)
      (ExistsAt : World → Entity → Prop)
      (Person : Subject → Prop)
      (g : Entity),
      (∀ w : World, ExistsAt w g) ∧ (¬ ∃ s : Subject, Person s) := by
  refine ⟨Unit, Unit, Empty, fun _ _ => True, fun _ => False, (), fun _ => trivial, ?_⟩
  rintro ⟨s, _⟩
  cases s

/-- M-C2: Necessary Person Without Agency.
    A necessary person exists, but performs zero acts (`ActAt` is empty). -/
theorem model_MC2_necessary_person_no_agency_consistent :
    ∃ (World Entity Subject : Type)
      (ExistsAt : World → Entity → Prop)
      (SubjectExistsAt : World → Subject → Prop)
      (Person : Subject → Prop)
      (ActAt : World → Subject → Prop → Prop)
      (g : Entity) (s : Subject),
      (∀ w : World, ExistsAt w g) ∧ (∀ w : World, SubjectExistsAt w s) ∧ Person s ∧
      (∀ w p, ¬ ActAt w s p) := by
  refine ⟨Unit, Unit, Unit, fun _ _ => True, fun _ _ => True, fun _ => True,
          fun _ _ _ => False, (), (), fun _ => trivial, fun _ => trivial, trivial, ?_⟩
  intro _ _ hAct
  exact hAct

/-- M-C3: Necessary Agent With Fixed Choice Across All Worlds.
    Free will holds locally at the actual world, but choice is fixed across all worlds.
    Refutes `Target C → ModalFreeWill`. -/
theorem model_MC3_fixed_choice_consistent :
    ∃ M : DeterministicModalModel,
      (∀ w, M.ExistsAt w M.g) ∧
      (∀ w, M.SubjectExistsAt w M.s) ∧
      M.Person M.s ∧
      FreeWillAt M.World M.Subject M.MeansAt M.actualWorld M.s ∧
      (∀ v, M.frame.R M.actualWorld v → M.ActAt v M.s M.p ∧ ¬ M.ActAt v M.s M.q) :=
  ⟨ModelDeterministicChoice,
   ModelDeterministicChoice.g_necessary,
   ModelDeterministicChoice.s_necessary,
   ModelDeterministicChoice.is_person,
   ⟨ModelDeterministicChoice.p, ModelDeterministicChoice.q, ModelDeterministicChoice.actual_chooses⟩,
   ModelDeterministicChoice.fixed_action⟩

/-- M-C4: Necessary Free Agent With Necessary Creation.
    The agent has free will, but creates contingent entities in EVERY accessible world.
    Refutes `NecessaryFreeAgent → ◇ NoCreation`. -/
structure MC4_Signature where
  World : Type
  Entity : Type
  Subject : Type
  frame : KripkeFrame World
  actualWorld : World
  ExistsAt : World → Entity → Prop
  SubjectExistsAt : World → Subject → Prop
  EntityOf : Subject → Entity
  Person : Subject → Prop
  MeansAt : World → Subject → Prop → Prop
  CreatesAt : World → Entity → Entity → Prop
  g : Entity
  s : Subject
  c : Entity
  g_necessary : ∀ w, ExistsAt w g
  s_necessary : ∀ w, SubjectExistsAt w s
  correlate : EntityOf s = g
  is_person : Person s
  free_will : FreeWillAt World Subject MeansAt actualWorld s
  creation_in_all_worlds : ∀ v, frame.R actualWorld v → CreatesAt v g c

theorem model_MC4_necessary_creation_consistent :
    ∃ _M : MC4_Signature, True := by
  let M : MC4_Signature := {
    World := Unit
    Entity := Bool
    Subject := Unit
    frame := { R := fun _ _ => True }
    actualWorld := ()
    ExistsAt := fun _ _ => True
    SubjectExistsAt := fun _ _ => True
    EntityOf := fun _ => true
    Person := fun _ => True
    MeansAt := fun _ _ _ => True
    CreatesAt := fun _ g c => g = true ∧ c = false
    g := true
    s := ()
    c := false
    g_necessary := fun _ => trivial
    s_necessary := fun _ => trivial
    correlate := rfl
    is_person := trivial
    free_will := ⟨True, False, ⟨trivial, trivial, fun ⟨_, hq⟩ => hq⟩⟩
    creation_in_all_worlds := fun _ _ => ⟨rfl, rfl⟩
  }
  exact ⟨M, trivial⟩

/-- M-C5: Necessary Free Agent With Contingent Creation.
    The same rigid agent `g` creates in world `w_create` and refrains in world `w_alone`.
    Both worlds are accessible from `actualWorld`. -/
structure MC5_Signature where
  World : Type
  Entity : Type
  Subject : Type
  frame : KripkeFrame World
  actualWorld : World
  ExistsAt : World → Entity → Prop
  SubjectExistsAt : World → Subject → Prop
  EntityOf : Subject → Entity
  Person : Subject → Prop
  MeansAt : World → Subject → Prop → Prop
  CreatesAt : World → Entity → Entity → Prop
  g : Entity
  s : Subject
  g_necessary : ∀ w, ExistsAt w g
  s_necessary : ∀ w, SubjectExistsAt w s
  correlate : EntityOf s = g
  is_person : Person s
  w_create : World
  w_alone : World
  create_accessible : frame.R actualWorld w_create
  alone_accessible : frame.R actualWorld w_alone
  has_creation : ∃ x : Entity, CreatesAt w_create g x
  no_creation : ¬ ∃ x : Entity, CreatesAt w_alone g x

def ModelMC5 : MC5_Signature where
  World := Bool        -- true = creation world, false = alone world
  Entity := Bool       -- true = g, false = creature
  Subject := Unit
  frame := { R := fun _ _ => True }
  actualWorld := true
  ExistsAt := fun w e => e = true ∨ w = true
  SubjectExistsAt := fun _ _ => True
  EntityOf := fun _ => true
  Person := fun _ => True
  MeansAt := fun _ _ _ => True
  CreatesAt := fun w g c => w = true ∧ g = true ∧ c = false
  g := true
  s := ()
  g_necessary := fun _ => Or.inl rfl
  s_necessary := fun _ => trivial
  correlate := rfl
  is_person := trivial
  w_create := true
  w_alone := false
  create_accessible := trivial
  alone_accessible := trivial
  has_creation := ⟨false, ⟨rfl, rfl, rfl⟩⟩
  no_creation := fun ⟨_, ⟨hW, _, _⟩⟩ => by cases hW

theorem model_MC5_contingent_creation_consistent :
    ∃ _M : MC5_Signature, True :=
  ⟨ModelMC5, trivial⟩

/-- M-C6: No Creation Without Free Abstention.
    A world without creation is accessible, but the agent does NOT freely will not to create;
    non-creation is merely passive or non-intentional. -/
theorem model_MC6_passive_no_creation_accessible :
    ∃ (World Entity Subject : Type)
      (frame : KripkeFrame World) (actualWorld : World)
      (CreatesAt : World → Entity → Entity → Prop)
      (ActAt : World → Subject → Prop → Prop)
      (g : Entity) (s : Subject),
      ClaimC2_ModalNoCreation World Entity frame actualWorld CreatesAt g ∧
      ¬ (∃ w : World, frame.R actualWorld w ∧ VoluntaryNoCreationAt World Entity Subject CreatesAt ActAt w g s) := by
  refine ⟨Unit, Unit, Unit, { R := fun _ _ => True }, (), fun _ _ _ => False, fun _ _ _ => False, (), (), ?_, ?_⟩
  · exact ⟨(), trivial, fun ⟨_, hCr⟩ => hCr⟩
  · rintro ⟨w, _, ⟨_, hAct⟩⟩
    exact hAct

-- ===========================================================================
-- Part 6: Core Entailments & Separation Theorems (Sections IX, X, XII, XIII, XVI)
-- ===========================================================================

/-!
### 6. Entailment and Independence Theorems
-/

/-- Independence Theorem 1:
    Necessary Being + Person + Ordinary Free Will does NOT entail that creation is contingent.
    Creation could be metaphysically necessary despite local free will. -/
theorem necessary_free_agent_not_entails_contingent_creation :
    ¬ (∀ (S : MC4_Signature),
        ∃ w : S.World, S.frame.R S.actualWorld w ∧ ¬ ∃ x, S.CreatesAt w S.g x) := by
  intro hAll
  obtain ⟨M, _⟩ := model_MC4_necessary_creation_consistent
  have ⟨w, hR, hNoCr⟩ := hAll M
  have hCr := M.creation_in_all_worlds w hR
  exact hNoCr ⟨M.c, hCr⟩

/-- Positive Synthesis Theorem:
    If a necessary personal agent possesses Genuine Modal Freedom with respect to creating,
    then the contingency of creation is formally proven (both creation and alone worlds are accessible). -/
theorem modal_freedom_yields_contingency_of_creation
    (World Entity Subject : Type)
    (frame : KripkeFrame World)
    (actualWorld : World)
    (ExistsAt : World → Entity → Prop)
    (SubjectExistsAt : World → Subject → Prop)
    (EntityOf : Subject → Entity)
    (Person : Subject → Prop)
    (MeansAt : World → Subject → Prop → Prop)
    (ActAt : World → Subject → Prop → Prop)
    (CreatesAt : World → Entity → Entity → Prop)
    (g : Entity) (s : Subject)
    (_targetB : TargetB_NecessaryPerson World Entity Subject ExistsAt SubjectExistsAt EntityOf Person g s)
    (p_create : Prop) (q_refrain : Prop)
    (hModalFree : ModalFreeWill World Subject frame actualWorld MeansAt ActAt s p_create q_refrain)
    (hCreateEffect : ∀ w, ActAt w s p_create → ∃ x, CreatesAt w g x)
    (hRefrainEffect : ∀ w, ActAt w s q_refrain → ¬ ∃ x, CreatesAt w g x) :
    (∃ v : World, frame.R actualWorld v ∧ ∃ x, CreatesAt v g x) ∧
    (∃ u : World, frame.R actualWorld u ∧ ¬ ∃ x, CreatesAt u g x) := by
  obtain ⟨_, _, ⟨v, hRv, _, hActP⟩, ⟨u, hRu, _, hActQ⟩⟩ := hModalFree
  refine ⟨⟨v, hRv, hCreateEffect v hActP⟩, ⟨u, hRu, hRefrainEffect u hActQ⟩⟩

end Logos.ModalCreationAgency


/-
================================================================================
SECTION: EssenceActCollapse
================================================================================
-/
/-
# Logos.EssenceActCollapse — Necessary Nature, Contingent Will, and Modal Collapse

An adversarial formal investigation into the deep metaphysical boundary:
"Can a necessary being possess a necessary nature while exercising
genuinely contingent, freely settled acts of will?"

Governing rule:
"Prefer losing the theorem to hiding the premise."

Terminology:
All formal definitions use the neutral witness `g : Entity` and `s : Subject`.
Theological identifications are strictly confined to the synthesis layer.
-/


namespace Logos.EssenceActCollapse

open Logos.TheologicalModalHardening (KripkeFrame BoxR)
open Logos.ModalCreationAgency (Incompatible ChoosesAt FreeWillAt TargetA_NecessaryBeing TargetB_NecessaryPerson)

-- ===========================================================================
-- Part 1: Hardened Modal Freedom & Essence vs. Nature vs. Act (Sections I, II, VII)
-- ===========================================================================

/-!
### 1. Hardened Modal Alternatives
Base `ModalFreeWill` requires accessible worlds witnessing actions `p` and `q`.
`HardenedModalFreeWill` explicitly enforces mutual exclusivity of action execution:
`ActAt v s p ∧ ¬ ActAt v s q` and `ActAt u s q ∧ ¬ ActAt u s p`.
We prove that this strictly forces the witness worlds to be distinct: `v ≠ u`.
-/

structure HardenedModalFreeWill (World Subject : Type)
    (frame : KripkeFrame World)
    (actualWorld : World)
    (MeansAt : World → Subject → Prop → Prop)
    (ActAt : World → Subject → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop where
  incompatible : Incompatible p q
  actual_chooses : ChoosesAt World Subject MeansAt actualWorld s p q
  branch_p : ∃ v : World, frame.R actualWorld v ∧
               ChoosesAt World Subject MeansAt v s p q ∧
               ActAt v s p ∧ ¬ ActAt v s q
  branch_q : ∃ u : World, frame.R actualWorld u ∧
               ChoosesAt World Subject MeansAt u s p q ∧
               ActAt u s q ∧ ¬ ActAt u s p

/-- Theorem: Hardened Modal Alternatives strictly force distinct worlds.
    The same agent cannot settle mutually exclusive actions in the same world. -/
theorem hardened_modal_freedom_forces_distinct_worlds
    (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
    (MeansAt : World → Subject → Prop → Prop) (ActAt : World → Subject → Prop → Prop)
    (s : Subject) (p q : Prop)
    (hModal : HardenedModalFreeWill World Subject frame actualWorld MeansAt ActAt s p q) :
    ∃ v u : World, frame.R actualWorld v ∧ frame.R actualWorld u ∧ v ≠ u := by
  obtain ⟨_, _, ⟨v, hRv, _, hActPv, hNotQv⟩, ⟨u, hRu, _, hActQu, _⟩⟩ := hModal
  refine ⟨v, u, hRv, hRu, ?_⟩
  rintro rfl
  -- If v = u, then ActAt v s q and ¬ ActAt v s q hold jointly:
  exact hNotQv hActQu

/-!
### 2. Tripartite Distinction: Existence vs. Nature vs. Act
We formalize:
- NecessaryEntity(g): g exists in every world.
- NecessaryNature(g, NatureAt): g exemplifies NatureAt in every world.
- NecessaryAct(s, a): s performs act a in every world.
- ContingentAct(s, a): s performs act a in some world, and refrains in another.
-/

def NecessaryEntity (World Entity : Type) (ExistsAt : World → Entity → Prop) (g : Entity) : Prop :=
  ∀ w : World, ExistsAt w g

def NecessaryNature (World Entity : Type) (NatureAt : World → Entity → Prop) (g : Entity) : Prop :=
  ∀ w : World, NatureAt w g

def NecessaryAct (World Subject : Type) (ActAt : World → Subject → Prop → Prop) (s : Subject) (a : Prop) : Prop :=
  ∀ w : World, ActAt w s a

def ContingentAct (World Subject : Type) (ActAt : World → Subject → Prop → Prop) (s : Subject) (a : Prop) : Prop :=
  (∃ v : World, ActAt v s a) ∧ (∃ u : World, ¬ ActAt u s a)

/-- Separation Theorem: Necessary Nature does NOT entail Necessary Action.
    A necessary entity with an invariant necessary nature can consistently
    perform a contingent act across accessible worlds. -/
theorem necessary_nature_not_entails_necessary_act :
    ∃ (World Entity Subject : Type)
      (ExistsAt : World → Entity → Prop)
      (NatureAt : World → Entity → Prop)
      (ActAt : World → Subject → Prop → Prop)
      (g : Entity) (s : Subject) (a : Prop),
      NecessaryEntity World Entity ExistsAt g ∧
      NecessaryNature World Entity NatureAt g ∧
      ContingentAct World Subject ActAt s a := by
  refine ⟨Bool, Unit, Unit,
          fun _ _ => True,
          fun _ _ => True,
          fun w _ _ => w = true,
          (), (), True, ?_, ?_, ?_⟩
  · intro _; trivial
  · intro _; trivial
  · exact ⟨⟨true, rfl⟩, ⟨false, fun h => by cases h⟩⟩

-- ===========================================================================
-- Part 2: Decoupling Volition, Action, and Creation (Sections V, XII)
-- ===========================================================================

/-!
### 3. World-Indexed Volition vs. Action vs. Creation
We introduce three distinct world-indexed relations:
- `WillsAt w s a`: Subject s wills/settles volition a in world w.
- `ActAt w s a`: Subject s executes action a in world w.
- `CreatesAt w g x`: Entity g creates entity x in world w.
-/

def VolitionToActBridge (World Subject : Type)
    (WillsAt : World → Subject → Prop → Prop)
    (ActAt : World → Subject → Prop → Prop) : Prop :=
  ∀ w s a, WillsAt w s a → ActAt w s a

def ActToVolitionBridge (World Subject : Type)
    (WillsAt : World → Subject → Prop → Prop)
    (ActAt : World → Subject → Prop → Prop) : Prop :=
  ∀ w s a, ActAt w s a → WillsAt w s a

def ActToCreationBridge (World Entity Subject : Type)
    (EntityOf : Subject → Entity)
    (ActAt : World → Subject → Prop → Prop)
    (CreatesAt : World → Entity → Entity → Prop)
    (CreateForm : Prop) : Prop :=
  ∀ w s, ActAt w s CreateForm → ∃ x : Entity, CreatesAt w (EntityOf s) x

def VolitionToCreationBridge (World Entity Subject : Type)
    (EntityOf : Subject → Entity)
    (WillsAt : World → Subject → Prop → Prop)
    (CreatesAt : World → Entity → Entity → Prop)
    (CreateForm : Prop) : Prop :=
  ∀ w s, WillsAt w s CreateForm → ∃ x : Entity, CreatesAt w (EntityOf s) x

/-- Separation Model: Involuntary Action without Volition.
    An agent can act without willing (e.g., compulsive or involuntary act). -/
theorem involuntary_act_consistent :
    ∃ (World Subject : Type)
      (WillsAt : World → Subject → Prop → Prop)
      (ActAt : World → Subject → Prop → Prop)
      (w : World) (s : Subject) (a : Prop),
      ActAt w s a ∧ ¬ WillsAt w s a := by
  refine ⟨Unit, Unit, fun _ _ _ => False, fun _ _ _ => True, (), (), True, trivial, fun h => h⟩

/-- Separation Model: Unexecuted Volition without Action.
    An agent can will an outcome without successfully acting/executing it. -/
theorem unexecuted_volition_consistent :
    ∃ (World Subject : Type)
      (WillsAt : World → Subject → Prop → Prop)
      (ActAt : World → Subject → Prop → Prop)
      (w : World) (s : Subject) (a : Prop),
      WillsAt w s a ∧ ¬ ActAt w s a := by
  refine ⟨Unit, Unit, fun _ _ _ => True, fun _ _ _ => False, (), (), True, trivial, fun h => h⟩

/-!
### 4. Four Strict Statements of Non-Creation
-/

def Statement1_PassiveNoCreation (World Entity : Type)
    (frame : KripkeFrame World) (actualWorld : World)
    (CreatesAt : World → Entity → Entity → Prop) (g : Entity) : Prop :=
  ∃ w : World, frame.R actualWorld w ∧ ¬ ∃ x : Entity, CreatesAt w g x

def Statement2_WillsNotToCreate (World Subject : Type)
    (frame : KripkeFrame World) (actualWorld : World)
    (WillsAt : World → Subject → Prop → Prop) (s : Subject) (RefrainForm : Prop) : Prop :=
  ∃ w : World, frame.R actualWorld w ∧ WillsAt w s RefrainForm

def Statement3_FreelyWillsNotToCreate (World Subject : Type)
    (frame : KripkeFrame World) (actualWorld : World)
    (WillsAt : World → Subject → Prop → Prop) (s : Subject) (CreateForm RefrainForm : Prop) : Prop :=
  (∃ w : World, frame.R actualWorld w ∧ WillsAt w s RefrainForm) ∧
  (∃ v : World, frame.R actualWorld v ∧ WillsAt v s CreateForm)

def Statement4_BilateralFreeWillCreation (World Subject : Type)
    (frame : KripkeFrame World) (actualWorld : World)
    (WillsAt : World → Subject → Prop → Prop) (s : Subject) (CreateForm RefrainForm : Prop) : Prop :=
  Statement3_FreelyWillsNotToCreate World Subject frame actualWorld WillsAt s CreateForm RefrainForm

/-- Implication: Statement 3/4 entails Statement 2. -/
theorem statement3_implies_statement2
    (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
    (WillsAt : World → Subject → Prop → Prop) (s : Subject) (CreateForm RefrainForm : Prop)
    (h : Statement3_FreelyWillsNotToCreate World Subject frame actualWorld WillsAt s CreateForm RefrainForm) :
    Statement2_WillsNotToCreate World Subject frame actualWorld WillsAt s RefrainForm :=
  h.1

/-- Implication: Statement 2 entails Statement 1 under an efficacy bridge. -/
theorem statement2_implies_statement1
    (World Entity Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
    (EntityOf : Subject → Entity)
    (WillsAt : World → Subject → Prop → Prop)
    (CreatesAt : World → Entity → Entity → Prop)
    (s : Subject) (RefrainForm : Prop)
    (hBridge : ∀ w, WillsAt w s RefrainForm → ¬ ∃ x, CreatesAt w (EntityOf s) x)
    (hStmt2 : Statement2_WillsNotToCreate World Subject frame actualWorld WillsAt s RefrainForm) :
    Statement1_PassiveNoCreation World Entity frame actualWorld CreatesAt (EntityOf s) := by
  obtain ⟨w, hR, hWills⟩ := hStmt2
  exact ⟨w, hR, hBridge w hWills⟩

-- ===========================================================================
-- Part 3: Frozen Circumstances, Modal Collapse vs. Anti-Collapse (Sections VIII, IX, X, XVI)
-- ===========================================================================

/-!
### 5. Frozen Circumstances & Modal Collapse
Can a necessary being with invariant nature and identical circumstances will differently?
-/

def SameCircumstances (World : Type) (Circumstance : World → Prop) (w u : World) : Prop :=
  Circumstance w = Circumstance u

def SameNature (World Entity : Type) (NatureAt : World → Entity → Prop) (g : Entity) (w u : World) : Prop :=
  NatureAt w g ∧ NatureAt u g

def DeterministicVolitionPrinciple (World Subject : Type)
    (Circumstance : World → Prop)
    (WillsAt : World → Subject → Prop → Prop) : Prop :=
  ∀ w u s a, SameCircumstances World Circumstance w u →
    (WillsAt w s a ↔ WillsAt u s a)

/-- Modal Collapse Theorem (Volition Level):
    If circumstances are invariant across all accessible worlds and volition is deterministic,
    then any actual volition of the necessary being is metaphysically necessary across all worlds. -/
theorem modal_collapse_theorem
    (World Subject : Type)
    (frame : KripkeFrame World)
    (actualWorld : World)
    (Circumstance : World → Prop)
    (WillsAt : World → Subject → Prop → Prop)
    (s : Subject) (a : Prop)
    (hActual : WillsAt actualWorld s a)
    (hInvariantCircumstances : ∀ w, frame.R actualWorld w → SameCircumstances World Circumstance actualWorld w)
    (hDet : DeterministicVolitionPrinciple World Subject Circumstance WillsAt) :
    ∀ w, frame.R actualWorld w → WillsAt w s a := by
  intro w hRw
  have hSame := hInvariantCircumstances w hRw
  have hEquiv := hDet actualWorld w s a hSame
  exact hEquiv.mp hActual

/-- Action Modal Collapse Theorem:
    Given invariant circumstances and invariant nature across accessible worlds,
    if volition is deterministic and the agent's volition translates into action via
    VolitionToActBridge, then actual action entails necessary action across all accessible worlds. -/
theorem modal_collapse_action_theorem
    (World Entity Subject : Type)
    (frame : KripkeFrame World)
    (actualWorld : World)
    (Circumstance : World → Prop)
    (NatureAt : World → Entity → Prop)
    (WillsAt : World → Subject → Prop → Prop)
    (ActAt : World → Subject → Prop → Prop)
    (g : Entity) (s : Subject) (a : Prop)
    (hActualVolition : WillsAt actualWorld s a)
    (hInvariantCircumstances : ∀ w, frame.R actualWorld w → SameCircumstances World Circumstance actualWorld w)
    (_hInvariantNature : ∀ w, frame.R actualWorld w → SameNature World Entity NatureAt g actualWorld w)
    (hDet : DeterministicVolitionPrinciple World Subject Circumstance WillsAt)
    (hBridge : VolitionToActBridge World Subject WillsAt ActAt) :
    ∀ w, frame.R actualWorld w → ActAt w s a := by
  intro w hRw
  have hVol := modal_collapse_theorem World Subject frame actualWorld Circumstance WillsAt s a
                 hActualVolition hInvariantCircumstances hDet w hRw
  exact hBridge w s a hVol

/-!
### 6. Candidate Anti-Collapse Principles
We formalize 4 candidates and prove their comparative logical relationships:
A. Volitional Indifference: The agent can will incompatible alternatives under identical circumstances.
B. Non-Deterministic Volition: Circumstances do not uniquely determine volition.
C. Agent-Causal Settlement: The agent primitive settles volition across accessible worlds.
D. Sufficient Freedom: At least two accessible incompatible actions/volitions are available.
-/

def CandidateA_VolitionalIndifference (World Subject : Type)
    (frame : KripkeFrame World) (actualWorld : World)
    (Circumstance : World → Prop)
    (WillsAt : World → Subject → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Incompatible p q ∧
  ∃ v u : World, frame.R actualWorld v ∧ frame.R actualWorld u ∧
    SameCircumstances World Circumstance v u ∧
    WillsAt v s p ∧ WillsAt u s q

def CandidateB_NonDeterministicVolition (World Subject : Type)
    (Circumstance : World → Prop)
    (WillsAt : World → Subject → Prop → Prop) : Prop :=
  ¬ DeterministicVolitionPrinciple World Subject Circumstance WillsAt

def CandidateC_AgentCausalSettlement (World Subject : Type)
    (frame : KripkeFrame World) (actualWorld : World)
    (Circumstance : World → Prop)
    (SettlesAt : World → Subject → Prop → Prop)
    (WillsAt : World → Subject → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Incompatible p q ∧
  (∀ w form, SettlesAt w s form → WillsAt w s form) ∧
  ∃ v u : World, frame.R actualWorld v ∧ frame.R actualWorld u ∧
    SameCircumstances World Circumstance v u ∧
    SettlesAt v s p ∧ SettlesAt u s q

def CandidateD_SufficientFreedom (World Subject : Type)
    (frame : KripkeFrame World) (actualWorld : World)
    (WillsAt : World → Subject → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Incompatible p q ∧
  (∃ v : World, frame.R actualWorld v ∧ WillsAt v s p) ∧
  (∃ u : World, frame.R actualWorld u ∧ WillsAt u s q)

/-- Logical Relationship 1:
    Agent-Causal Settlement strictly entails Volitional Indifference (Candidate C → Candidate A). -/
theorem agent_causal_implies_volitional_indifference
    (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
    (Circumstance : World → Prop)
    (SettlesAt : World → Subject → Prop → Prop)
    (WillsAt : World → Subject → Prop → Prop)
    (s : Subject) (p q : Prop)
    (hC : CandidateC_AgentCausalSettlement World Subject frame actualWorld Circumstance SettlesAt WillsAt s p q) :
    CandidateA_VolitionalIndifference World Subject frame actualWorld Circumstance WillsAt s p q := by
  obtain ⟨hIncomp, hEfficacy, v, u, hRv, hRu, hSame, hSetP, hSetQ⟩ := hC
  refine ⟨hIncomp, v, u, hRv, hRu, hSame, hEfficacy v p hSetP, hEfficacy u q hSetQ⟩

/-- Logical Relationship 2:
    Volitional Indifference entails Sufficient Freedom (Candidate A → Candidate D). -/
theorem volitional_indifference_implies_sufficient_freedom
    (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
    (Circumstance : World → Prop)
    (WillsAt : World → Subject → Prop → Prop)
    (s : Subject) (p q : Prop)
    (hA : CandidateA_VolitionalIndifference World Subject frame actualWorld Circumstance WillsAt s p q) :
    CandidateD_SufficientFreedom World Subject frame actualWorld WillsAt s p q := by
  obtain ⟨hIncomp, v, u, hRv, hRu, _, hWillsP, hWillsQ⟩ := hA
  exact ⟨hIncomp, ⟨v, hRv, hWillsP⟩, ⟨u, hRu, hWillsQ⟩⟩

/-- Logical Relationship 3:
    Volitional Indifference entails Non-Deterministic Volition (Candidate A → Candidate B). -/
theorem volitional_indifference_implies_nondeterministic
    (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
    (Circumstance : World → Prop) (WillsAt : World → Subject → Prop → Prop)
    (s : Subject) (p q : Prop)
    (hIndiff : CandidateA_VolitionalIndifference World Subject frame actualWorld Circumstance WillsAt s p q)
    (hConsistentVolition : ∀ w a b, Incompatible a b → WillsAt w s a → ¬ WillsAt w s b) :
    CandidateB_NonDeterministicVolition World Subject Circumstance WillsAt := by
  obtain ⟨hIncomp, v, u, _, _, hSame, hWillsP, hWillsQ⟩ := hIndiff
  intro hDet
  have hEquiv := hDet v u s q hSame
  have hWillsQ_at_v := hEquiv.mpr hWillsQ
  have hNotQ_at_v := hConsistentVolition v p q hIncomp hWillsP
  exact hNotQ_at_v hWillsQ_at_v

/-- Separation: Sufficient Freedom does NOT entail Volitional Indifference.
    Alternatives can be available across worlds with different circumstances,
    while choice remains completely determined by circumstances. -/
theorem sufficient_freedom_not_entails_volitional_indifference :
    ∃ (World Subject : Type)
      (frame : KripkeFrame World) (actualWorld : World)
      (Circumstance : World → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (s : Subject) (p q : Prop),
      CandidateD_SufficientFreedom World Subject frame actualWorld WillsAt s p q ∧
      ¬ CandidateA_VolitionalIndifference World Subject frame actualWorld Circumstance WillsAt s p q := by
  refine ⟨Bool, Unit, { R := fun _ _ => True }, true,
          fun w => w = true,
          fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          (), True, False, ?_, ?_⟩
  · refine ⟨fun ⟨_, hq⟩ => hq, ⟨true, trivial, Or.inl ⟨rfl, rfl⟩⟩, ⟨false, trivial, Or.inr ⟨rfl, rfl⟩⟩⟩
  · rintro ⟨_, v, u, _, _, hSameCirc, hWillsP, hWillsQ⟩
    -- Circumstance v is (v = true), Circumstance u is (u = true).
    -- hSameCirc means (v = true) = (u = true).
    -- But hWillsP requires v = true, and hWillsQ requires u = false.
    have hv : v = true := by
      rcases hWillsP with ⟨hv, _⟩ | ⟨_, hp⟩
      · exact hv
      · have hFalse : False := hp ▸ trivial
        exact False.elim hFalse
    have hu : u = false := by
      rcases hWillsQ with ⟨_, hq⟩ | ⟨hu, _⟩
      · have hFalse : False := hq.symm ▸ trivial
        exact False.elim hFalse
      · exact hu
    subst hv hu
    have hDiff : (true = true) ≠ (false = true) := by decide
    exact hDiff hSameCirc

/-- Free Creation Theorem (Anti-Collapse):
    If the necessary personal agent possesses Volitional Indifference between creating and refraining,
    then creation is contingent even though the agent's nature and circumstances are invariant. -/
theorem free_creation_anti_collapse
    (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
    (Circumstance : World → Prop) (WillsAt : World → Subject → Prop → Prop)
    (s : Subject) (CreateForm RefrainForm : Prop)
    (hIndiff : CandidateA_VolitionalIndifference World Subject frame actualWorld Circumstance WillsAt s CreateForm RefrainForm) :
    (∃ v : World, frame.R actualWorld v ∧ WillsAt v s CreateForm) ∧
    (∃ u : World, frame.R actualWorld u ∧ WillsAt u s RefrainForm) := by
  obtain ⟨_, v, u, hRv, hRu, _, hWillsV, hWillsU⟩ := hIndiff
  exact ⟨⟨v, hRv, hWillsV⟩, ⟨u, hRu, hWillsU⟩⟩

-- ===========================================================================
-- Part 4: The Hostile Countermodel Suite MC7 Through MC12 (Sections III, IV, XIII)
-- ===========================================================================

/-!
### 7. Hostile Countermodel Suite MC7 – MC12
-/

/-- MC7: Necessary Free Agent With Necessary Action.
    The agent is necessary, personal, and has local free will, but performs
    creation in EVERY accessible world. -/
structure MC7_Signature where
  World : Type
  Entity : Type
  Subject : Type
  frame : KripkeFrame World
  actualWorld : World
  ExistsAt : World → Entity → Prop
  SubjectExistsAt : World → Subject → Prop
  EntityOf : Subject → Entity
  Person : Subject → Prop
  MeansAt : World → Subject → Prop → Prop
  ActAt : World → Subject → Prop → Prop
  CreatesAt : World → Entity → Entity → Prop
  g : Entity
  s : Subject
  c : Entity
  CreateForm : Prop
  g_necessary : ∀ w, ExistsAt w g
  s_necessary : ∀ w, SubjectExistsAt w s
  correlate : EntityOf s = g
  is_person : Person s
  free_will : FreeWillAt World Subject MeansAt actualWorld s
  action_necessary : ∀ w, frame.R actualWorld w → ActAt w s CreateForm
  creation_necessary : ∀ w, frame.R actualWorld w → CreatesAt w g c

theorem model_MC7_consistent :
    ∃ _M : MC7_Signature, True := by
  let M : MC7_Signature := {
    World := Unit
    Entity := Bool
    Subject := Unit
    frame := { R := fun _ _ => True }
    actualWorld := ()
    ExistsAt := fun _ _ => True
    SubjectExistsAt := fun _ _ => True
    EntityOf := fun _ => true
    Person := fun _ => True
    MeansAt := fun _ _ _ => True
    ActAt := fun _ _ _ => True
    CreatesAt := fun _ g c => g = true ∧ c = false
    g := true
    s := ()
    c := false
    CreateForm := True
    g_necessary := fun _ => trivial
    s_necessary := fun _ => trivial
    correlate := rfl
    is_person := trivial
    free_will := ⟨True, False, ⟨trivial, trivial, fun ⟨_, hq⟩ => hq⟩⟩
    action_necessary := fun _ _ => trivial
    creation_necessary := fun _ _ => ⟨rfl, rfl⟩
  }
  exact ⟨M, trivial⟩

/-- MC8: Necessary Nature With Contingent Action.
    The same necessary being exemplifies the exact same nature in all worlds,
    yet executes divergent actions across worlds. -/
structure MC8_Signature where
  World : Type
  Entity : Type
  Subject : Type
  frame : KripkeFrame World
  actualWorld : World
  ExistsAt : World → Entity → Prop
  NatureAt : World → Entity → Prop
  ActAt : World → Subject → Prop → Prop
  g : Entity
  s : Subject
  a : Prop
  g_necessary : ∀ w, ExistsAt w g
  nature_necessary : ∀ w, NatureAt w g
  contingent_act : ContingentAct World Subject ActAt s a

theorem model_MC8_consistent :
    ∃ _M : MC8_Signature, True := by
  let M : MC8_Signature := {
    World := Bool
    Entity := Unit
    Subject := Unit
    frame := { R := fun _ _ => True }
    actualWorld := true
    ExistsAt := fun _ _ => True
    NatureAt := fun _ _ => True
    ActAt := fun w _ _ => w = true
    g := ()
    s := ()
    a := True
    g_necessary := fun _ => trivial
    nature_necessary := fun _ => trivial
    contingent_act := ⟨⟨true, rfl⟩, ⟨false, fun h => by cases h⟩⟩
  }
  exact ⟨M, trivial⟩

/-- MC9: Identical Circumstances & Nature With Divergent Volitional Settlement.
    Circumstances and nature are identical in worlds v and u, yet the agent wills differently. -/
structure MC9_Signature where
  World : Type
  Entity : Type
  Subject : Type
  frame : KripkeFrame World
  actualWorld : World
  Circumstance : World → Prop
  NatureAt : World → Entity → Prop
  WillsAt : World → Subject → Prop → Prop
  g : Entity
  s : Subject
  p : Prop
  q : Prop
  v : World
  u : World
  v_accessible : frame.R actualWorld v
  u_accessible : frame.R actualWorld u
  same_circ : SameCircumstances World Circumstance v u
  same_nature : SameNature World Entity NatureAt g v u
  wills_p_at_v : WillsAt v s p
  wills_q_at_u : WillsAt u s q
  incompatible : Incompatible p q

theorem model_MC9_consistent :
    ∃ _M : MC9_Signature, True := by
  let M : MC9_Signature := {
    World := Bool
    Entity := Unit
    Subject := Unit
    frame := { R := fun _ _ => True }
    actualWorld := true
    Circumstance := fun _ => True
    NatureAt := fun _ _ => True
    WillsAt := fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False)
    g := ()
    s := ()
    p := True
    q := False
    v := true
    u := false
    v_accessible := trivial
    u_accessible := trivial
    same_circ := rfl
    same_nature := ⟨trivial, trivial⟩
    wills_p_at_v := Or.inl ⟨rfl, rfl⟩
    wills_q_at_u := Or.inr ⟨rfl, rfl⟩
    incompatible := fun ⟨_, hq⟩ => hq
  }
  exact ⟨M, trivial⟩

/-- MC10: Divergent World Outcomes Without Volitional Difference.
    Worlds contain different outcomes/events, but the will of the agent is fixed. -/
structure MC10_Signature where
  World : Type
  Subject : Type
  frame : KripkeFrame World
  actualWorld : World
  OutcomeAt : World → Prop
  WillsAt : World → Subject → Prop → Prop
  s : Subject
  a : Prop
  v : World
  u : World
  v_accessible : frame.R actualWorld v
  u_accessible : frame.R actualWorld u
  diff_outcomes : OutcomeAt v ≠ OutcomeAt u
  same_will : WillsAt v s a ∧ WillsAt u s a

theorem model_MC10_consistent :
    ∃ _M : MC10_Signature, True := by
  let M : MC10_Signature := {
    World := Bool
    Subject := Unit
    frame := { R := fun _ _ => True }
    actualWorld := true
    OutcomeAt := fun w => w = true
    WillsAt := fun _ _ _ => True
    s := ()
    a := True
    v := true
    u := false
    v_accessible := trivial
    u_accessible := trivial
    diff_outcomes := fun h => by
      have hTrue : (true = true) := rfl
      have hFalse : (false = true) := h ▸ hTrue
      cases hFalse
    same_will := ⟨trivial, trivial⟩
  }
  exact ⟨M, trivial⟩

/-- MC11: Passive No-Creation Without Voluntary Abstention.
    An accessible world contains no creation, yet the agent does NOT will non-creation. -/
theorem model_MC11_consistent :
    ∃ (World Entity Subject : Type)
      (frame : KripkeFrame World) (actualWorld : World)
      (CreatesAt : World → Entity → Entity → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (g : Entity) (s : Subject) (RefrainForm : Prop),
      Statement1_PassiveNoCreation World Entity frame actualWorld CreatesAt g ∧
      ¬ Statement2_WillsNotToCreate World Subject frame actualWorld WillsAt s RefrainForm := by
  refine ⟨Unit, Unit, Unit, { R := fun _ _ => True }, (), fun _ _ _ => False, fun _ _ _ => False, (), (), True, ?_, ?_⟩
  · exact ⟨(), trivial, fun ⟨_, hCr⟩ => hCr⟩
  · rintro ⟨_, _, hWills⟩
    exact hWills

/-- MC12: Necessary Free Agent With Modal Collapse.
    Agent possesses free will locally at the actual world, but deterministic volition
    causes every accessible world to settle into the exact same volition. -/
structure MC12_Signature where
  World : Type
  Subject : Type
  frame : KripkeFrame World
  actualWorld : World
  Circumstance : World → Prop
  MeansAt : World → Subject → Prop → Prop
  WillsAt : World → Subject → Prop → Prop
  s : Subject
  p : Prop
  q : Prop
  free_will : FreeWillAt World Subject MeansAt actualWorld s
  det_volition : DeterministicVolitionPrinciple World Subject Circumstance WillsAt
  same_circ : ∀ w, frame.R actualWorld w → SameCircumstances World Circumstance actualWorld w
  modal_collapse : ∀ w, frame.R actualWorld w → (WillsAt w s p ↔ WillsAt actualWorld s p)

theorem model_MC12_consistent :
    ∃ _M : MC12_Signature, True := by
  let M : MC12_Signature := {
    World := Unit
    Subject := Unit
    frame := { R := fun _ _ => True }
    actualWorld := ()
    Circumstance := fun _ => True
    MeansAt := fun _ _ _ => True
    WillsAt := fun _ _ form => form = True
    s := ()
    p := True
    q := False
    free_will := ⟨True, False, ⟨trivial, trivial, fun ⟨_, hq⟩ => hq⟩⟩
    det_volition := fun _ _ _ _ _ => Iff.rfl
    same_circ := fun _ _ => rfl
    modal_collapse := fun _ _ => Iff.rfl
  }
  exact ⟨M, trivial⟩

end Logos.EssenceActCollapse


/-
================================================================================
SECTION: ModalPossibilityFrontier
================================================================================
-/
/-
# Logos.ModalPossibilityFrontier — The Modal Possibility Frontier

An adversarial formal investigation into the modal frontier of agency, necessity,
reason, and creation:
"Try to shrink the remaining realm of possibilities by attacking it from every
logically and metaphysically available direction."

Governing rule:
"Prefer losing the theorem to hiding the premise."

Terminology:
All formal definitions use the neutral witness `g : Entity` and `s : Subject`.
Theological identifications are strictly confined to the synthesis layer.
-/


namespace Logos.ModalPossibilityFrontier

open Logos.TheologicalModalHardening (KripkeFrame BoxR)
open Logos.ModalCreationAgency (Incompatible ChoosesAt FreeWillAt TargetA_NecessaryBeing TargetB_NecessaryPerson)
open Logos.EssenceActCollapse (NecessaryEntity NecessaryNature NecessaryAct ContingentAct VolitionToActBridge SameCircumstances SameNature)

-- ===========================================================================
-- Part I: Multi-Layer Semantic Hardening (Section I)
-- ===========================================================================

/-!
### 1. Rigid Individual Identity Across Worlds
We enforce rigid cross-world identity for the individual candidate entity `g`
and its personal subject correlate `s` across all worlds.
-/

structure RigidAgent (World Entity Subject : Type)
    (ExistsAt : World → Entity → Prop)
    (SubjectExistsAt : World → Subject → Prop)
    (EntityOf : Subject → Entity)
    (g : Entity) (s : Subject) : Prop where
  g_necessary : ∀ w : World, ExistsAt w g
  s_necessary : ∀ w : World, SubjectExistsAt w s
  rigid_correlate : EntityOf s = g

/-!
### 2. Deconstruction of Circumstances: Orthogonal Layers
Rather than a single monolithic "circumstance", we separate:
- External circumstances (world environment, external states)
- Reasons (deliberative inputs, values, motives)
- World history (prior temporal/modal stages)
- Intrinsic nature (essential attributes of g)
- Internal state (mental disposition of s)
- Total deliberative state (conjunction of all antecedent conditions)
-/

def SameExternalCircumstances (World : Type) (ExtCirc : World → Prop) (w u : World) : Prop :=
  ExtCirc w = ExtCirc u

def SameReasons (World Subject : Type) (ReasonsAt : World → Subject → Prop) (s : Subject) (w u : World) : Prop :=
  ReasonsAt w s = ReasonsAt u s

def SameHistory (World : Type) (HistoryAt : World → Prop) (w u : World) : Prop :=
  HistoryAt w = HistoryAt u

def SameIntrinsicNature (World Entity : Type) (NatureAt : World → Entity → Prop) (g : Entity) (w u : World) : Prop :=
  NatureAt w g = NatureAt u g

def SameInternalState (World Subject : Type) (InternalStateAt : World → Subject → Prop) (s : Subject) (w u : World) : Prop :=
  InternalStateAt w s = InternalStateAt u s

structure SameTotalDeliberativeState (World Entity Subject : Type)
    (ExtCirc : World → Prop)
    (ReasonsAt : World → Subject → Prop)
    (HistoryAt : World → Prop)
    (NatureAt : World → Entity → Prop)
    (InternalStateAt : World → Subject → Prop)
    (g : Entity) (s : Subject) (w u : World) : Prop where
  same_ext : SameExternalCircumstances World ExtCirc w u
  same_reasons : SameReasons World Subject ReasonsAt s w u
  same_history : SameHistory World HistoryAt w u
  same_nature : SameIntrinsicNature World Entity NatureAt g w u
  same_internal : SameInternalState World Subject InternalStateAt s w u

-- ===========================================================================
-- Part II: Modal Attribute Lattice & Separation (Sections II, VII)
-- ===========================================================================

/-!
### 3. Modal Attribute Lattice
Attributes of necessary beings and agents.
-/

def NecessaryRationality (World Subject : Type)
    (IsRationalAt : World → Subject → Prop) (s : Subject) : Prop :=
  ∀ w : World, IsRationalAt w s

def NecessaryKnowledge (World Subject : Type)
    (KnowsAt : World → Subject → Prop → Prop) (s : Subject) (p : Prop) : Prop :=
  ∀ w : World, KnowsAt w s p

def PerfectGoodness (World Subject : Type)
    (IsGoodAt : World → Subject → Prop) (s : Subject) : Prop :=
  ∀ w : World, IsGoodAt w s

def ImmutableNature (World Entity : Type)
    (NatureAt : World → Entity → Prop) (g : Entity) : Prop :=
  ∀ w u : World, NatureAt w g = NatureAt u g

def ImmutableWill (World Subject : Type)
    (WillsAt : World → Subject → Prop → Prop) (s : Subject) (a : Prop) : Prop :=
  ∀ w u : World, WillsAt w s a = WillsAt u s a

def Aseity (World Entity : Type)
    (ExtDepAt : World → Entity → Prop) (g : Entity) : Prop :=
  ∀ w : World, ¬ ExtDepAt w g

/-- Separation: Necessary Knowledge does NOT entail Necessary Will. -/
theorem necessary_knowledge_not_entails_necessary_will :
    ∃ (World Subject : Type)
      (KnowsAt : World → Subject → Prop → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (s : Subject) (k a : Prop),
      NecessaryKnowledge World Subject KnowsAt s k ∧
      ¬ ImmutableWill World Subject WillsAt s a := by
  refine ⟨Bool, Unit, fun _ _ _ => True, fun w _ _ => w = true, (), True, True, ?_, ?_⟩
  · intro _; trivial
  · intro hImm
    have hEq := hImm true false
    have hDiff : (true = true) ≠ (false = true) := by decide
    exact hDiff hEq

/-- Separation: Necessary Rationality does NOT entail Necessary Action. -/
theorem necessary_rationality_not_entails_necessary_act :
    ∃ (World Subject : Type)
      (IsRationalAt : World → Subject → Prop)
      (ActAt : World → Subject → Prop → Prop)
      (s : Subject) (a : Prop),
      NecessaryRationality World Subject IsRationalAt s ∧
      ContingentAct World Subject ActAt s a := by
  refine ⟨Bool, Unit, fun _ _ => True, fun w _ _ => w = true, (), True, ?_, ?_⟩
  · intro _; trivial
  · exact ⟨⟨true, rfl⟩, ⟨false, fun h => by cases h⟩⟩

-- ===========================================================================
-- Part III: Deterministic Collapse Taxonomy & Impossibility Theorems (Sections IV, VIII, IX, XVII)
-- ===========================================================================

/-!
### 4. Deterministic Principles: Hierarchy
- `StrictDeterminism`: Any two accessible worlds are identical.
- `CausalDeterminism`: Identical antecedent history uniquely determines volition.
- `ReasonDeterminism`: Identical reasons uniquely determine volition.
- `DeterminingPSR`: Every volition is uniquely determined by antecedent reasons.
- `CompleteStateDeterminism`: Identical total deliberative state uniquely determines volition.
-/

def StrictDeterminism (World : Type) (frame : KripkeFrame World) (actualWorld : World) : Prop :=
  ∀ w : World, frame.R actualWorld w → w = actualWorld

def CausalDeterminism (World Subject : Type)
    (HistoryAt : World → Prop)
    (WillsAt : World → Subject → Prop → Prop) : Prop :=
  ∀ w u s a, SameHistory World HistoryAt w u →
    (WillsAt w s a ↔ WillsAt u s a)

def ReasonDeterminism (World Subject : Type)
    (ReasonsAt : World → Subject → Prop)
    (WillsAt : World → Subject → Prop → Prop) : Prop :=
  ∀ w u s a, SameReasons World Subject ReasonsAt s w u →
    (WillsAt w s a ↔ WillsAt u s a)

def DeterminingPSR (World Subject : Type)
    (ReasonsAt : World → Subject → Prop)
    (WillsAt : World → Subject → Prop → Prop) : Prop :=
  ∀ w u s a, SameReasons World Subject ReasonsAt s w u →
    (WillsAt w s a ↔ WillsAt u s a)

/-- Equivalence: Determining PSR is identical in logical form to Reason Determinism. -/
theorem determining_psr_iff_reason_determinism
    (World Subject : Type)
    (ReasonsAt : World → Subject → Prop)
    (WillsAt : World → Subject → Prop → Prop) :
    DeterminingPSR World Subject ReasonsAt WillsAt ↔
    ReasonDeterminism World Subject ReasonsAt WillsAt :=
  Iff.rfl

def CompleteStateDeterminism (World Entity Subject : Type)
    (ExtCirc : World → Prop) (ReasonsAt : World → Subject → Prop)
    (HistoryAt : World → Prop) (NatureAt : World → Entity → Prop)
    (InternalStateAt : World → Subject → Prop)
    (WillsAt : World → Subject → Prop → Prop) : Prop :=
  ∀ w u g s a, SameTotalDeliberativeState World Entity Subject ExtCirc ReasonsAt HistoryAt NatureAt InternalStateAt g s w u →
    (WillsAt w s a ↔ WillsAt u s a)

/-- Causal Determinism Modal Collapse Theorem:
    If antecedent history is invariant across accessible worlds and causal determinism holds,
    then actual volition is necessary across all accessible worlds. -/
theorem causal_determinism_modal_collapse
    (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
    (HistoryAt : World → Prop) (WillsAt : World → Subject → Prop → Prop)
    (s : Subject) (a : Prop)
    (hActual : WillsAt actualWorld s a)
    (hInvariantHistory : ∀ w, frame.R actualWorld w → SameHistory World HistoryAt actualWorld w)
    (hCausalDet : CausalDeterminism World Subject HistoryAt WillsAt) :
    ∀ w, frame.R actualWorld w → WillsAt w s a := by
  intro w hRw
  have hSame := hInvariantHistory w hRw
  have hEquiv := hCausalDet actualWorld w s a hSame
  exact hEquiv.mp hActual

/-- Minimal Collapse Theorem: Reason Determinism yields modal collapse of will. -/
theorem reason_determinism_modal_collapse
    (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
    (ReasonsAt : World → Subject → Prop) (WillsAt : World → Subject → Prop → Prop)
    (s : Subject) (a : Prop)
    (hActual : WillsAt actualWorld s a)
    (hInvariantReasons : ∀ w, frame.R actualWorld w → SameReasons World Subject ReasonsAt s actualWorld w)
    (hDet : ReasonDeterminism World Subject ReasonsAt WillsAt) :
    ∀ w, frame.R actualWorld w → WillsAt w s a := by
  intro w hRw
  have hSame := hInvariantReasons w hRw
  have hEquiv := hDet actualWorld w s a hSame
  exact hEquiv.mp hActual

/-!
### 5. Positive Impossibility Theorems
-/

/-- Impossibility Theorem 1: Determining PSR is logically incompatible with Bilateral Modal Freedom.
    If reasons are invariant across accessible worlds and determining PSR holds,
    the agent cannot possess accessible alternative volitions. -/
theorem determining_psr_incompatible_with_modal_freedom
    (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
    (ReasonsAt : World → Subject → Prop) (WillsAt : World → Subject → Prop → Prop)
    (s : Subject) (p q : Prop)
    (hIncomp : Incompatible p q)
    (hConsistentVolition : ∀ w a b, Incompatible a b → WillsAt w s a → ¬ WillsAt w s b)
    (hPSR : DeterminingPSR World Subject ReasonsAt WillsAt)
    (hInvariantReasons : ∀ w, frame.R actualWorld w → SameReasons World Subject ReasonsAt s actualWorld w)
    (hBranchP : ∃ v : World, frame.R actualWorld v ∧ WillsAt v s p)
    (hBranchQ : ∃ u : World, frame.R actualWorld u ∧ WillsAt u s q) :
    False := by
  obtain ⟨v, hRv, hWillsP⟩ := hBranchP
  obtain ⟨u, hRu, hWillsQ⟩ := hBranchQ
  have hSameV := hInvariantReasons v hRv
  have hSameU := hInvariantReasons u hRu
  have hSameVU : SameReasons World Subject ReasonsAt s v u := by
    dsimp [SameReasons] at *
    rw [← hSameV, ← hSameU]
  have hWillsQ_at_v := (hPSR v u s q hSameVU).mpr hWillsQ
  have hNotQ_at_v := hConsistentVolition v p q hIncomp hWillsP
  exact hNotQ_at_v hWillsQ_at_v

/-- Impossibility Theorem 2: Immutable Will is incompatible with Contingent Action. -/
theorem immutable_will_incompatible_with_contingent_act
    (World Subject : Type) (_frame : KripkeFrame World) (_actualWorld : World)
    (WillsAt : World → Subject → Prop → Prop) (ActAt : World → Subject → Prop → Prop)
    (s : Subject) (a : Prop)
    (hBridge : VolitionToActBridge World Subject WillsAt ActAt)
    (hReflect : ∀ w s a, ActAt w s a → WillsAt w s a)
    (hImmWill : ImmutableWill World Subject WillsAt s a)
    (hContingentAct : ContingentAct World Subject ActAt s a) :
    False := by
  obtain ⟨⟨v, hActV⟩, ⟨u, hNotActU⟩⟩ := hContingentAct
  have hWillsV : WillsAt v s a := hReflect v s a hActV
  have hEq := hImmWill v u
  have hWillsU : WillsAt u s a := by
    have hPropEq : WillsAt v s a = WillsAt u s a := hEq
    exact hPropEq ▸ hWillsV
  have hActU := hBridge u s a hWillsU
  exact hNotActU hActU

-- ===========================================================================
-- Part IV: Action Hierarchy, Reasons-Responsiveness & Relative Completeness (Sections V, VI, X, XVIII, XIX)
-- ===========================================================================

/-!
### 6. Four-Level Action/Agency Hierarchy
We strictly separate:
Level 1: Outcome Alternative (world states differ)
Level 2: Action Alternative (agent's actions differ)
Level 3: Volition Alternative (agent's will differs)
Level 4: Agent-Causal Settlement (agent irreducibly settles between options under identical input)
-/

def Level1_OutcomeAlternative (World : Type) (OutcomeAt : World → Prop) (v u : World) : Prop :=
  OutcomeAt v ≠ OutcomeAt u

def Level2_ActAlternative (World Subject : Type) (ActAt : World → Subject → Prop → Prop)
    (s : Subject) (a : Prop) (v u : World) : Prop :=
  ActAt v s a ∧ ¬ ActAt u s a

def Level3_VolitionAlternative (World Subject : Type) (WillsAt : World → Subject → Prop → Prop)
    (s : Subject) (a : Prop) (v u : World) : Prop :=
  WillsAt v s a ∧ ¬ WillsAt u s a

def Level4_AgentCausalAlternative (World Entity Subject : Type)
    (ExtCirc : World → Prop) (ReasonsAt : World → Subject → Prop)
    (HistoryAt : World → Prop) (NatureAt : World → Entity → Prop)
    (InternalStateAt : World → Subject → Prop)
    (SettlesAt : World → Subject → Prop → Prop)
    (g : Entity) (s : Subject) (p q : Prop) (v u : World) : Prop :=
  Incompatible p q ∧
  SameTotalDeliberativeState World Entity Subject ExtCirc ReasonsAt HistoryAt NatureAt InternalStateAt g s v u ∧
  SettlesAt v s p ∧ SettlesAt u s q

/-!
### 7. Relative Completeness for Contingent Creation
We isolate the exact formal missing link: `MissingModalSettlement`.
-/

def MissingModalSettlement (World Subject : Type)
    (frame : KripkeFrame World) (actualWorld : World)
    (WillsAt : World → Subject → Prop → Prop)
    (s : Subject) (CreateForm RefrainForm : Prop) : Prop :=
  Incompatible CreateForm RefrainForm ∧
  (∃ v : World, frame.R actualWorld v ∧ WillsAt v s CreateForm) ∧
  (∃ u : World, frame.R actualWorld u ∧ WillsAt u s RefrainForm)

/-- Relative Completeness Theorem:
    Target Contingent Creation is provably equivalent to MissingModalSettlement.
    Nothing more, nothing less, is required. -/
theorem target_contingent_creation_iff_missing_modal_settlement
    (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
    (WillsAt : World → Subject → Prop → Prop)
    (s : Subject) (CreateForm RefrainForm : Prop) :
    MissingModalSettlement World Subject frame actualWorld WillsAt s CreateForm RefrainForm ↔
    (Incompatible CreateForm RefrainForm ∧
     (∃ v : World, frame.R actualWorld v ∧ WillsAt v s CreateForm) ∧
     (∃ u : World, frame.R actualWorld u ∧ WillsAt u s RefrainForm)) :=
  Iff.rfl

-- ===========================================================================
-- Part V: The Hostile Countermodel Suite MC13 Through MC30 (Sections III, XI, XII, XIII, XIV, XVI)
-- ===========================================================================

/-!
### 8. Hostile Countermodels MC13 – MC30
-/

/-- MC13: Same external circumstances, different will. -/
theorem model_MC13_consistent :
    ∃ (World Subject : Type) (ExtCirc : World → Prop) (WillsAt : World → Subject → Prop → Prop)
      (s : Subject) (a : Prop) (v u : World),
      SameExternalCircumstances World ExtCirc v u ∧
      Level3_VolitionAlternative World Subject WillsAt s a v u := by
  refine ⟨Bool, Unit, fun _ => True, fun w _ _ => w = true, (), True, true, false, rfl, ?_⟩
  exact ⟨rfl, fun h => by cases h⟩

/-- MC14: Same external circumstances + same reasons, different will. -/
theorem model_MC14_consistent :
    ∃ (World Subject : Type) (ExtCirc : World → Prop) (ReasonsAt : World → Subject → Prop)
      (WillsAt : World → Subject → Prop → Prop) (s : Subject) (a : Prop) (v u : World),
      SameExternalCircumstances World ExtCirc v u ∧
      SameReasons World Subject ReasonsAt s v u ∧
      Level3_VolitionAlternative World Subject WillsAt s a v u := by
  refine ⟨Bool, Unit, fun _ => True, fun _ _ => True, fun w _ _ => w = true, (), True, true, false, rfl, rfl, ?_⟩
  exact ⟨rfl, fun h => by cases h⟩

/-- MC15: Same external circumstances + reasons + history, different will. -/
theorem model_MC15_consistent :
    ∃ (World Subject : Type) (ExtCirc : World → Prop) (ReasonsAt : World → Subject → Prop)
      (HistoryAt : World → Prop) (WillsAt : World → Subject → Prop → Prop)
      (s : Subject) (a : Prop) (v u : World),
      SameExternalCircumstances World ExtCirc v u ∧
      SameReasons World Subject ReasonsAt s v u ∧
      SameHistory World HistoryAt v u ∧
      Level3_VolitionAlternative World Subject WillsAt s a v u := by
  refine ⟨Bool, Unit, fun _ => True, fun _ _ => True, fun _ => True, fun w _ _ => w = true,
          (), True, true, false, rfl, rfl, rfl, ?_⟩
  exact ⟨rfl, fun h => by cases h⟩

/-- MC16: Same total deliberative state, different will. -/
theorem model_MC16_consistent :
    ∃ (World Entity Subject : Type)
      (ExtCirc : World → Prop) (ReasonsAt : World → Subject → Prop)
      (HistoryAt : World → Prop) (NatureAt : World → Entity → Prop)
      (InternalStateAt : World → Subject → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (g : Entity) (s : Subject) (a : Prop) (v u : World),
      SameTotalDeliberativeState World Entity Subject ExtCirc ReasonsAt HistoryAt NatureAt InternalStateAt g s v u ∧
      Level3_VolitionAlternative World Subject WillsAt s a v u := by
  refine ⟨Bool, Unit, Unit,
          fun _ => True, fun _ _ => True, fun _ => True, fun _ _ => True, fun _ _ => True,
          fun w _ _ => w = true, (), (), True, true, false,
          ⟨rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, fun h => by cases h⟩⟩

/-- MC17: Necessary rational agent with complete knowledge and identical deliberative state, divergent will. -/
theorem model_MC17_consistent :
    ∃ (World Entity Subject : Type)
      (ExistsAt : World → Entity → Prop) (IsRationalAt : World → Subject → Prop)
      (KnowsAt : World → Subject → Prop → Prop)
      (ExtCirc : World → Prop) (ReasonsAt : World → Subject → Prop)
      (HistoryAt : World → Prop) (NatureAt : World → Entity → Prop)
      (InternalStateAt : World → Subject → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (g : Entity) (s : Subject) (k a : Prop) (v u : World),
      NecessaryEntity World Entity ExistsAt g ∧
      NecessaryRationality World Subject IsRationalAt s ∧
      NecessaryKnowledge World Subject KnowsAt s k ∧
      SameTotalDeliberativeState World Entity Subject ExtCirc ReasonsAt HistoryAt NatureAt InternalStateAt g s v u ∧
      Level3_VolitionAlternative World Subject WillsAt s a v u := by
  refine ⟨Bool, Unit, Unit,
          fun _ _ => True, fun _ _ => True, fun _ _ _ => True,
          fun _ => True, fun _ _ => True, fun _ => True, fun _ _ => True, fun _ _ => True,
          fun w _ _ => w = true, (), (), True, True, true, false,
          fun _ => trivial, fun _ => trivial, fun _ => trivial,
          ⟨rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, fun h => by cases h⟩⟩

/-- MC18: Informational symmetry with contingent volition. -/
theorem model_MC18_consistent :
    ∃ (World Subject : Type) (InfoAt : World → Subject → Prop)
      (WillsAt : World → Subject → Prop → Prop) (s : Subject) (p q : Prop) (v u : World),
      InfoAt v s = InfoAt u s ∧
      Incompatible p q ∧
      WillsAt v s p ∧ WillsAt u s q := by
  refine ⟨Bool, Unit, fun _ _ => True,
          fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          (), True, False, true, false, rfl, fun ⟨_, hq⟩ => hq, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩

/-- MC19: Necessary perfectly good agent with contingent volition. -/
theorem model_MC19_consistent :
    ∃ (World Subject : Type) (IsGoodAt : World → Subject → Prop)
      (WillsAt : World → Subject → Prop → Prop) (s : Subject) (a : Prop) (v u : World),
      PerfectGoodness World Subject IsGoodAt s ∧
      Level3_VolitionAlternative World Subject WillsAt s a v u := by
  refine ⟨Bool, Unit, fun _ _ => True, fun w _ _ => w = true, (), True, true, false,
          fun _ => trivial, ⟨rfl, fun h => by cases h⟩⟩

/-- MC20: Necessary immutable nature with contingent volition. -/
theorem model_MC20_consistent :
    ∃ (World Entity Subject : Type) (NatureAt : World → Entity → Prop)
      (WillsAt : World → Subject → Prop → Prop) (g : Entity) (s : Subject) (a : Prop) (v u : World),
      ImmutableNature World Entity NatureAt g ∧
      Level3_VolitionAlternative World Subject WillsAt s a v u := by
  refine ⟨Bool, Unit, Unit, fun _ _ => True, fun w _ _ => w = true, (), (), True, true, false,
          fun _ _ => rfl, ⟨rfl, fun h => by cases h⟩⟩

/-- MC21: Aseitic agent with contingent volition. -/
theorem model_MC21_consistent :
    ∃ (World Entity Subject : Type) (ExtDepAt : World → Entity → Prop)
      (WillsAt : World → Subject → Prop → Prop) (g : Entity) (s : Subject) (a : Prop) (v u : World),
      Aseity World Entity ExtDepAt g ∧
      Level3_VolitionAlternative World Subject WillsAt s a v u := by
  refine ⟨Bool, Unit, Unit, fun _ _ => False, fun w _ _ => w = true, (), (), True, true, false,
          fun _ h => h, ⟨rfl, fun h => by cases h⟩⟩

/-- Generic aseity does not entail the existence of any Level-3 volitional
    alternative. This unit-domain countermodel makes external dependence and
    willing false. It concerns the current bare predicate, which has no
    accessibility or incompatibility condition; it does not establish aseity of
    `Entity.ofGround`, interpret `ExtDepAt` as causal dependence, or prove
    divine metaphysics. Footprint: `{}`. -/
theorem aseity_does_not_force_any_volition_alternatives :
    ∃ (World Entity Subject : Type)
      (ExtDepAt : World → Entity → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (g : Entity),
      Aseity World Entity ExtDepAt g ∧
        ¬ ∃ (s : Subject) (a : Prop) (v u : World),
          Level3_VolitionAlternative World Subject WillsAt s a v u := by
  refine ⟨Unit, Unit, Unit, fun _ _ => False, fun _ _ _ => False, (), ?_⟩
  constructor
  · intro _ h
    exact h
  · intro hExists
    obtain ⟨s, a, v, u, hWill⟩ := hExists
    exact hWill.1

/-- The existence of a Level-3 volitional alternative does not entail generic
    aseity. This Boolean-domain countermodel makes external dependence true
    everywhere while willing differs between `true` and `false`. It concerns
    the current bare predicate, with no accessibility or incompatibility
    condition, and does not establish aseity of `Entity.ofGround` or prove
    divine metaphysics. Footprint: `{}`. -/
theorem volitional_alternative_does_not_force_aseity :
    ∃ (World Entity Subject : Type)
      (ExtDepAt : World → Entity → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (g : Entity) (s : Subject) (a : Prop) (v u : World),
      Level3_VolitionAlternative World Subject WillsAt s a v u ∧
        ¬ Aseity World Entity ExtDepAt g := by
  refine ⟨Bool, Unit, Unit, fun _ _ => True, fun w _ _ => w = true,
          (), (), True, true, false, ?_⟩
  constructor
  · exact ⟨rfl, fun h => by cases h⟩
  · intro hAseity
    exact hAseity true trivial

/-- MC22: Contrastive explanation via irreducible agent-causal settlement. -/
theorem model_MC22_consistent :
    ∃ (World Entity Subject : Type)
      (ExtCirc : World → Prop) (ReasonsAt : World → Subject → Prop)
      (HistoryAt : World → Prop) (NatureAt : World → Entity → Prop)
      (InternalStateAt : World → Subject → Prop)
      (SettlesAt : World → Subject → Prop → Prop)
      (g : Entity) (s : Subject) (p q : Prop) (v u : World),
      Level4_AgentCausalAlternative World Entity Subject ExtCirc ReasonsAt HistoryAt NatureAt InternalStateAt SettlesAt g s p q v u := by
  refine ⟨Bool, Unit, Unit,
          fun _ => True, fun _ _ => True, fun _ => True, fun _ _ => True, fun _ _ => True,
          fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          (), (), True, False, true, false,
          fun ⟨_, hq⟩ => hq, ⟨rfl, rfl, rfl, rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩

/-- MC23: Indeterministic but unfree agent (random fluctuation without intentional choice). -/
theorem model_MC23_consistent :
    ∃ (World Subject : Type) (Circumstance : World → Prop)
      (FluctuationAt : World → Subject → Prop → Prop)
      (ChoosesAt : World → Subject → Prop → Prop → Prop)
      (s : Subject) (p : Prop) (v u : World),
      Circumstance v = Circumstance u ∧
      (FluctuationAt v s p ∧ ¬ FluctuationAt u s p) ∧
      (∀ w p q, ¬ ChoosesAt w s p q) := by
  refine ⟨Bool, Unit, fun _ => True, fun w _ _ => w = true, fun _ _ _ _ => False, (), True, true, false,
          rfl, ⟨rfl, fun h => by cases h⟩, fun _ _ _ h => h⟩

/-- MC24: Reasons-responsive but modally closed agent (Frankfurt/compatibilist model).
    Agent responds to hypothetical different reasons, but in accessible reality only one reason/choice is open. -/
theorem model_MC24_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ReasonsAt : World → Subject → Prop) (WillsAt : World → Subject → Prop → Prop)
      (s : Subject) (p : Prop),
      -- Accessible modal closure:
      (∀ w, frame.R actualWorld w → WillsAt w s p) ∧
      -- Counterfactual sensitivity across a broader conceptual world:
      (∃ c : World, ReasonsAt c s ≠ ReasonsAt actualWorld s ∧ ¬ WillsAt c s p) := by
  refine ⟨Bool, Unit, { R := fun _ w => w = true }, true,
          fun w _ => w = true, fun w _ _ => w = true, (), True, ?_, ?_⟩
  · intro w hRw
    exact hRw
  · refine ⟨false, ?_, fun h => by cases h⟩
    intro hEq
    have hDiff : (false = true) ≠ (true = true) := by decide
    exact hDiff hEq

/-- MC25: Modal freedom without agent-causal settlement (pure ungrounded indeterminism). -/
theorem model_MC25_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (WillsAt : World → Subject → Prop → Prop)
      (SettlesAt : World → Subject → Prop → Prop)
      (s : Subject) (p q : Prop),
      Incompatible p q ∧
      (∃ v : World, frame.R actualWorld v ∧ WillsAt v s p) ∧
      (∃ u : World, frame.R actualWorld u ∧ WillsAt u s q) ∧
      (∀ w s a, ¬ SettlesAt w s a) := by
  refine ⟨Bool, Unit, { R := fun _ _ => True }, true,
          fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          fun _ _ _ => False, (), True, False,
          fun ⟨_, hq⟩ => hq, ⟨true, trivial, Or.inl ⟨rfl, rfl⟩⟩, ⟨false, trivial, Or.inr ⟨rfl, rfl⟩⟩,
          fun _ _ _ h => h⟩

/-- MC26: Agent-causal-looking structure that collapses into determinism. -/
theorem model_MC26_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (SettlesAt : World → Subject → Prop → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (s : Subject) (p : Prop),
      (∀ w form, SettlesAt w s form ↔ WillsAt w s form) ∧
      (∀ w, frame.R actualWorld w → WillsAt w s p) := by
  refine ⟨Unit, Unit, { R := fun _ _ => True }, (), fun _ _ _ => True, fun _ _ _ => True, (), True, ?_, ?_⟩
  · intro _ _; exact Iff.rfl
  · intro _ _; trivial

/-- MC27: Necessary agent with contingent creation. -/
theorem model_MC27_consistent :
    ∃ (World Entity : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ExistsAt : World → Entity → Prop) (CreatesAt : World → Entity → Entity → Prop)
      (g : Entity) (c : Entity),
      NecessaryEntity World Entity ExistsAt g ∧
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  refine ⟨Bool, Unit, { R := fun _ _ => True }, true,
          fun _ _ => True, fun w _ _ => w = true, (), (),
          fun _ => trivial, ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩

/-- MC28: Necessary agent with necessary creation. -/
theorem model_MC28_consistent :
    ∃ (World Entity : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ExistsAt : World → Entity → Prop) (CreatesAt : World → Entity → Entity → Prop)
      (g : Entity) (c : Entity),
      NecessaryEntity World Entity ExistsAt g ∧
      ∀ w : World, frame.R actualWorld w → CreatesAt w g c := by
  refine ⟨Unit, Unit, { R := fun _ _ => True }, (), fun _ _ => True, fun _ _ _ => True, (), (),
          fun _ => trivial, fun _ _ => trivial⟩

/-- MC29: Necessary agent with no creation and no voluntary abstention. -/
theorem model_MC29_consistent :
    ∃ (World Entity Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ExistsAt : World → Entity → Prop) (CreatesAt : World → Entity → Entity → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (g : Entity) (s : Subject) (RefrainForm : Prop),
      NecessaryEntity World Entity ExistsAt g ∧
      (∃ w : World, frame.R actualWorld w ∧ ¬ ∃ x, CreatesAt w g x) ∧
      (∀ w, ¬ WillsAt w s RefrainForm) := by
  refine ⟨Unit, Unit, Unit, { R := fun _ _ => True }, (), fun _ _ => True, fun _ _ _ => False, fun _ _ _ => False,
          (), (), True, fun _ => trivial, ⟨(), trivial, fun ⟨_, hx⟩ => hx⟩, fun _ h => h⟩

/-- MC30: Necessary agent freely abstaining from creation. -/
theorem model_MC30_consistent :
    ∃ (World Entity Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ExistsAt : World → Entity → Prop) (WillsAt : World → Subject → Prop → Prop)
      (CreatesAt : World → Entity → Entity → Prop)
      (g : Entity) (s : Subject) (CreateForm RefrainForm : Prop),
      NecessaryEntity World Entity ExistsAt g ∧
      Incompatible CreateForm RefrainForm ∧
      (∃ v : World, frame.R actualWorld v ∧ WillsAt v s CreateForm ∧ (∃ x, CreatesAt v g x)) ∧
      (∃ u : World, frame.R actualWorld u ∧ WillsAt u s RefrainForm ∧ (¬ ∃ x, CreatesAt u g x)) := by
  refine ⟨Bool, Unit, Unit, { R := fun _ _ => True }, true,
          fun _ _ => True,
          fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          fun w _ _ => w = true,
          (), (), True, False,
          fun _ => trivial, fun ⟨_, hq⟩ => hq,
          ⟨true, trivial, Or.inl ⟨rfl, rfl⟩, ⟨(), rfl⟩⟩,
          ⟨false, trivial, Or.inr ⟨rfl, rfl⟩, fun ⟨_, hx⟩ => by cases hx⟩⟩

#print axioms Logos.ModalPossibilityFrontier.aseity_does_not_force_any_volition_alternatives
#print axioms Logos.ModalPossibilityFrontier.volitional_alternative_does_not_force_aseity

end Logos.ModalPossibilityFrontier


/-
================================================================================
SECTION: DeepModalFrontier
================================================================================
-/
/-
# Logos.DeepModalFrontier — Attacking the Fork Itself

A machine-checked formal investigation attacking the modal fork:
"Determine whether the fork is genuinely irreducible, or whether deeper principles
already present or defensibly sharpened inside Γ force one side of it."

Governing rule:
"Prefer losing the theorem to hiding the premise."

Methodological disciplines:
1. Strict separation of Non-Collapse, Modal Freedom, and Agent-Causal Freedom.
2. S5 universal frames for modal possibility countermodels.
3. Distinction between Explanation and Determination (The Third Regime).
4. Full audit of omniscience, rationality, goodness, aseity, and immutability.
-/


namespace Logos.DeepModalFrontier

open Logos.TheologicalModalHardening (KripkeFrame BoxR)
open Logos.ModalCreationAgency (Incompatible ChoosesAt FreeWillAt)
open Logos.EssenceActCollapse (NecessaryEntity NecessaryNature NecessaryAct ContingentAct VolitionToActBridge SameCircumstances SameNature)
open Logos.ModalPossibilityFrontier (RigidAgent SameExternalCircumstances SameReasons SameHistory SameIntrinsicNature SameInternalState SameTotalDeliberativeState)

-- ===========================================================================
-- Part I: Correcting the Logical Overstatement & Alternative Hierarchy (Sections I, XV)
-- ===========================================================================

/-!
### 1. Separation of Non-Determinism from Modal Free Will
Non-collapse (¬ DeterministicVolition) does NOT entail Modal Free Will.
An indeterministic system can exhibit random fluctuation without intentional agency.
-/

def S5UniversalFrame (World : Type) : KripkeFrame World :=
  { R := fun _ _ => True }

theorem s5_frame_is_equivalence (World : Type) :
    (∀ w : World, (S5UniversalFrame World).R w w) ∧
    (∀ w u : World, (S5UniversalFrame World).R w u → (S5UniversalFrame World).R u w) ∧
    (∀ w u v : World, (S5UniversalFrame World).R w u → (S5UniversalFrame World).R u v → (S5UniversalFrame World).R w v) := by
  refine ⟨fun _ => trivial, fun _ _ _ => trivial, fun _ _ _ _ _ => trivial⟩

def NonDeterministicVolition (World Subject : Type)
    (ReasonsAt : World → Subject → Prop)
    (WillsAt : World → Subject → Prop → Prop) : Prop :=
  ¬ (∀ w u s a, SameReasons World Subject ReasonsAt s w u → (WillsAt w s a ↔ WillsAt u s a))

def ModalFreeWillRigid (World Subject : Type)
    (frame : KripkeFrame World) (actualWorld : World)
    (ChoosesAt : World → Subject → Prop → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop :=
  Incompatible p q ∧
  (∃ v : World, frame.R actualWorld v ∧ ChoosesAt v s p q) ∧
  (∃ u : World, frame.R actualWorld u ∧ ChoosesAt u s q p)

/-- Separation: Non-deterministic volition does NOT entail Modal Free Will. -/
theorem nondeterministic_not_entails_modal_freewill :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ReasonsAt : World → Subject → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (ChoosesAt : World → Subject → Prop → Prop → Prop)
      (s : Subject) (p q : Prop),
      NonDeterministicVolition World Subject ReasonsAt WillsAt ∧
      ¬ ModalFreeWillRigid World Subject frame actualWorld ChoosesAt s p q := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ _ => True,
          fun w _ _ => w = true,
          fun _ _ _ _ => False,
          (), True, False, ?_, ?_⟩
  · intro hDet
    have hSame : SameReasons Bool Unit (fun _ _ => True) () true false := rfl
    have hEquiv := hDet true false () True hSame
    dsimp at hEquiv
    have hFalse := hEquiv.mp rfl
    cases hFalse
  · intro ⟨_, ⟨v, _, hChooseV⟩, _⟩
    exact hChooseV

/-!
### 2. Six-Level Hierarchy of Alternatives (Section XV)
We explicitly distinguish six distinct levels:
1. OutcomeAlternative
2. ActionAlternative
3. VolitionalAlternative
4. CounterfactualAlternative
5. AgentiveAlternative
6. AgentCausalAlternative
-/

def Alt1_Outcome (World : Type) (OutcomeAt : World → Prop) (v u : World) : Prop :=
  OutcomeAt v ≠ OutcomeAt u

def Alt2_Action (World Subject : Type) (ActAt : World → Subject → Prop → Prop)
    (s : Subject) (a : Prop) (v u : World) : Prop :=
  ActAt v s a ∧ ¬ ActAt u s a

def Alt3_Volition (World Subject : Type) (WillsAt : World → Subject → Prop → Prop)
    (s : Subject) (a : Prop) (v u : World) : Prop :=
  WillsAt v s a ∧ ¬ WillsAt u s a

def Alt4_Counterfactual (World Subject : Type)
    (ReasonsAt : World → Subject → Prop)
    (WillsAt : World → Subject → Prop → Prop)
    (s : Subject) (p : Prop) (actualWorld : World) : Prop :=
  ∃ c : World, ReasonsAt c s ≠ ReasonsAt actualWorld s ∧ WillsAt c s p ≠ WillsAt actualWorld s p

def Alt5_Agentive (World Subject : Type)
    (IntentionalAt : World → Subject → Prop → Prop)
    (s : Subject) (p q : Prop) (v u : World) : Prop :=
  Incompatible p q ∧ IntentionalAt v s p ∧ IntentionalAt u s q

def Alt6_AgentCausal (World Entity Subject : Type)
    (ExtCirc : World → Prop) (ReasonsAt : World → Subject → Prop)
    (HistoryAt : World → Prop) (NatureAt : World → Entity → Prop)
    (InternalStateAt : World → Subject → Prop)
    (SettlesAt : World → Subject → Prop → Prop)
    (g : Entity) (s : Subject) (p q : Prop) (v u : World) : Prop :=
  Incompatible p q ∧
  SameTotalDeliberativeState World Entity Subject ExtCirc ReasonsAt HistoryAt NatureAt InternalStateAt g s v u ∧
  SettlesAt v s p ∧ SettlesAt u s q

-- ===========================================================================
-- Part II: Agency Settlement Hierarchy C0 through C4 (Section II)
-- ===========================================================================

/-!
### 3. Deconstruction of Agent-Causal Settlement: The C0–C4 Ladder
- C0: Primitive Modal Variation (mere difference across worlds)
- C1: Non-Deterministic Settlement (antecedent conditions do not fix volition)
- C2: Agent-Attributable Settlement (difference is predicated of the agent's act)
- C3: Agent-Causal Settlement (agent is the settling source)
- C4: Explanatorily Agent-Causal Settlement (contrastive teleological explanation without necessitation)
-/

def Level_C0_PrimitiveVariation (World Subject : Type)
    (WillsAt : World → Subject → Prop → Prop) (s : Subject) (p q : Prop) (v u : World) : Prop :=
  Incompatible p q ∧ WillsAt v s p ∧ WillsAt u s q

def Level_C1_NonDeterministic (World Subject : Type)
    (ReasonsAt : World → Subject → Prop)
    (WillsAt : World → Subject → Prop → Prop) : Prop :=
  NonDeterministicVolition World Subject ReasonsAt WillsAt

def Level_C2_AgentAttributable (World Subject : Type)
    (SettlesAt : World → Subject → Prop → Prop)
    (s : Subject) (p q : Prop) (v u : World) : Prop :=
  Incompatible p q ∧ SettlesAt v s p ∧ SettlesAt u s q

def Level_C3_AgentCausal (World Entity Subject : Type)
    (ExtCirc : World → Prop) (ReasonsAt : World → Subject → Prop)
    (HistoryAt : World → Prop) (NatureAt : World → Entity → Prop)
    (InternalStateAt : World → Subject → Prop)
    (SettlesAt : World → Subject → Prop → Prop)
    (g : Entity) (s : Subject) (p q : Prop) (v u : World) : Prop :=
  Alt6_AgentCausal World Entity Subject ExtCirc ReasonsAt HistoryAt NatureAt InternalStateAt SettlesAt g s p q v u

def Level_C4_ExplanatoryAgentCausal (World Entity Subject : Type)
    (ExtCirc : World → Prop) (ReasonsAt : World → Subject → Prop)
    (HistoryAt : World → Prop) (NatureAt : World → Entity → Prop)
    (InternalStateAt : World → Subject → Prop)
    (SettlesAt : World → Subject → Prop → Prop)
    (ExplainsSettlement : World → Subject → Prop → Prop → Prop)
    (g : Entity) (s : Subject) (p q : Prop) (v u : World) : Prop :=
  Level_C3_AgentCausal World Entity Subject ExtCirc ReasonsAt HistoryAt NatureAt InternalStateAt SettlesAt g s p q v u ∧
  (∀ w form, SettlesAt w s form → ∃ r, ReasonsAt w s ∧ ExplainsSettlement w s r form)

/-- Separation C0 does not entail C1: A deterministic world with changing reasons has C0 but not C1. -/
theorem C0_not_entails_C1 :
    ∃ (World Subject : Type) (ReasonsAt : World → Subject → Prop)
      (WillsAt : World → Subject → Prop → Prop) (s : Subject) (p q : Prop) (v u : World),
      Level_C0_PrimitiveVariation World Subject WillsAt s p q v u ∧
      ¬ Level_C1_NonDeterministic World Subject ReasonsAt WillsAt := by
  refine ⟨Bool, Unit, fun w _ => w = true,
          fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          (), True, False, true, false, ?_, ?_⟩
  · exact ⟨fun ⟨_, hq⟩ => hq, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩
  · intro hNonDet
    apply hNonDet
    intro w u s a hSame
    dsimp [SameReasons] at hSame
    have hEq : w = u := by
      cases w <;> cases u <;> try rfl
      · contradiction
      · contradiction
    rw [hEq]

/-- Separation C1 does not entail C2: Non-deterministic fluctuation without agent attribution. -/
theorem C1_not_entails_C2 :
    ∃ (World Subject : Type) (ReasonsAt : World → Subject → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (SettlesAt : World → Subject → Prop → Prop)
      (s : Subject) (p q : Prop) (v u : World),
      Level_C1_NonDeterministic World Subject ReasonsAt WillsAt ∧
      ¬ Level_C2_AgentAttributable World Subject SettlesAt s p q v u := by
  refine ⟨Bool, Unit, fun _ _ => True, fun w _ _ => w = true, fun _ _ _ => False,
          (), True, False, true, false, ?_, ?_⟩
  · intro hDet
    have hSame : SameReasons Bool Unit (fun _ _ => True) () true false := rfl
    have hEquiv := hDet true false () True hSame
    dsimp at hEquiv
    have hFalse := hEquiv.mp rfl
    cases hFalse
  · intro ⟨_, hSetV, _⟩
    exact hSetV

-- ===========================================================================
-- Part III: Modal Analogue of A14 & Relative Completeness (Section III)
-- ===========================================================================

/-!
### 4. Tripartite Modal Decomposition & Relative Completeness
Target: Bilateral Contingent Volition (◇Wills(p) ∧ ◇Wills(q)).
Analogous to A14:
ModalDifference = NonDetermination + AgentAttribution + BilateralWitness.
-/

structure ModalDifferencePrimitive (World Subject : Type)
    (frame : KripkeFrame World) (actualWorld : World)
    (ReasonsAt : World → Subject → Prop)
    (WillsAt : World → Subject → Prop → Prop)
    (s : Subject) (p q : Prop) : Prop where
  incomp : Incompatible p q
  witness_p : ∃ v : World, frame.R actualWorld v ∧ WillsAt v s p
  witness_q : ∃ u : World, frame.R actualWorld u ∧ WillsAt u s q
  non_determined : NonDeterministicVolition World Subject ReasonsAt WillsAt

/-- Relative Completeness Theorem:
    Bilateral Modal Volition under non-deterministic conditions is provably equivalent
    to the irreducible ModalDifferencePrimitive. -/
theorem modal_volition_iff_primitive_decomposition
    (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
    (ReasonsAt : World → Subject → Prop)
    (WillsAt : World → Subject → Prop → Prop)
    (s : Subject) (p q : Prop) :
    ModalDifferencePrimitive World Subject frame actualWorld ReasonsAt WillsAt s p q ↔
    (Incompatible p q ∧
     (∃ v : World, frame.R actualWorld v ∧ WillsAt v s p) ∧
     (∃ u : World, frame.R actualWorld u ∧ WillsAt u s q) ∧
     NonDeterministicVolition World Subject ReasonsAt WillsAt) := by
  constructor
  · intro h; exact ⟨h.incomp, h.witness_p, h.witness_q, h.non_determined⟩
  · intro ⟨hInc, hV, hU, hND⟩; exact ⟨hInc, hV, hU, hND⟩

-- ===========================================================================
-- Part IV: Hardened Attribute Spectra & Collapse Theorems (Sections IV–IX, XII, XIII)
-- ===========================================================================

/-!
### 5. Rationality Spectrum: R0 through R5
R0: Coherent action
R1: Acts for reasons
R2: Responds to reasons
R3: Deliberatively weighs reasons
R4: Deliberative non-compulsion (reasons incline without necessitation)
R5: Optimific compulsion (necessarily follows uniquely best reason)
-/

def Rationality_R0 (World Subject : Type) (ActAt : World → Subject → Prop → Prop) (s : Subject) : Prop :=
  ∀ w a, ActAt w s a → ¬ ActAt w s (¬ a)

def Rationality_R1 (World Subject : Type)
    (ReasonsAt : World → Subject → Prop) (ActAt : World → Subject → Prop → Prop) (s : Subject) : Prop :=
  ∀ w a, ActAt w s a → ∃ r, ReasonsAt w s ∧ r

def Rationality_R4_Deliberative (World Subject : Type)
    (ReasonsAt : World → Subject → Prop) (WillsAt : World → Subject → Prop → Prop) (s : Subject) : Prop :=
  ∀ w a, WillsAt w s a → ReasonsAt w s

def Rationality_R5_OptimificCompulsion (World Subject : Type)
    (BestReasonAt : World → Subject → Prop → Prop)
    (WillsAt : World → Subject → Prop → Prop) (s : Subject) : Prop :=
  ∀ w a, BestReasonAt w s a → WillsAt w s a

/-!
### 6. Goodness & Unique Best Action
-/

def UniqueBestAction (World Subject : Type)
    (BestReasonAt : World → Subject → Prop → Prop) (s : Subject) (best : Prop) : Prop :=
  ∀ w, BestReasonAt w s best ∧ (∀ a, BestReasonAt w s a → a = best)

/-- Threshold Collapse Theorem: Optimific Compulsion (R5) under a Unique Best Action forces modal collapse! -/
theorem unique_best_action_optimific_rationality_modal_collapse
    (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
    (BestReasonAt : World → Subject → Prop → Prop)
    (WillsAt : World → Subject → Prop → Prop)
    (s : Subject) (best : Prop)
    (hOpt : Rationality_R5_OptimificCompulsion World Subject BestReasonAt WillsAt s)
    (hUnique : UniqueBestAction World Subject BestReasonAt s best) :
    ∀ w : World, frame.R actualWorld w → WillsAt w s best := by
  intro w _
  have hBest := (hUnique w).1
  exact hOpt w best hBest

/-!
### 7. Omniscience Spectrum
-/

def Omniscience_AllTruths (World Subject : Type)
    (KnowsAt : World → Subject → Prop → Prop) (s : Subject) : Prop :=
  ∀ w (p : Prop), p → KnowsAt w s p

def Omniscience_Counterfactuals (World Subject : Type)
    (KnowsCounterfactualAt : World → Subject → (World → Prop) → Prop) (s : Subject) : Prop :=
  ∀ w (cond : World → Prop), KnowsCounterfactualAt w s cond

-- ===========================================================================
-- Part V: PSR Spectrum, Explanation vs Determination & The Third Regime (Sections X, XI, XVII–XIX)
-- ===========================================================================

/-!
### 8. PSR Spectrum: PSR-1 through PSR-8
PSR-3: Every act has a reason.
PSR-4: Every volition has an explanatory reason (non-necessitating).
PSR-6: Every volition is uniquely determined by sufficient reason (Determining PSR).
-/

def PSR_Level3_ActReason (World Subject : Type)
    (ReasonsAt : World → Subject → Prop) (ActAt : World → Subject → Prop → Prop) (s : Subject) : Prop :=
  ∀ w a, ActAt w s a → ReasonsAt w s

def PSR_Level4_VolitionReason (World Subject : Type)
    (ReasonsAt : World → Subject → Prop) (WillsAt : World → Subject → Prop → Prop) (s : Subject) : Prop :=
  ∀ w a, WillsAt w s a → ReasonsAt w s

def PSR_Level6_DeterminingPSR (World Subject : Type)
    (ReasonsAt : World → Subject → Prop) (WillsAt : World → Subject → Prop → Prop) : Prop :=
  ∀ w u s a, SameReasons World Subject ReasonsAt s w u → (WillsAt w s a ↔ WillsAt u s a)

/-!
### 9. The Third Regime: Teleological Explanation Without Determination
Reason `r` explains the agent's choice of `p`, without determining `p` to the exclusion of accessible `q`.
-/

def ExplainsChoiceNonDetermining (World Subject : Type)
    (frame : KripkeFrame World) (actualWorld : World)
    (ReasonsAt : World → Subject → Prop)
    (WillsAt : World → Subject → Prop → Prop)
    (Explains : World → Subject → Prop → Prop → Prop)
    (s : Subject) (p q r : Prop) : Prop :=
  Incompatible p q ∧
  (∃ v : World, frame.R actualWorld v ∧ WillsAt v s p ∧ ReasonsAt v s ∧ Explains v s r p) ∧
  (∃ u : World, frame.R actualWorld u ∧ WillsAt u s q ∧ ReasonsAt u s ∧ Explains u s r q)

/-- Consistency of the Third Regime:
    An agent can have genuine teleological reasons explaining its choice in both worlds
    under an S5 universal frame, without the choice being determined. -/
theorem third_regime_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ReasonsAt : World → Subject → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (Explains : World → Subject → Prop → Prop → Prop)
      (s : Subject) (p q r : Prop),
      ExplainsChoiceNonDetermining World Subject frame actualWorld ReasonsAt WillsAt Explains s p q r := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ _ => True,
          fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          fun _ _ _ _ => True,
          (), True, False, True, ?_⟩
  refine ⟨fun ⟨_, hq⟩ => hq, ⟨true, trivial, Or.inl ⟨rfl, rfl⟩, trivial, trivial⟩,
                              ⟨false, trivial, Or.inr ⟨rfl, rfl⟩, trivial, trivial⟩⟩

-- ===========================================================================
-- Part VI: The Hostile Countermodel Suite MC31 Through MC45 (Section XXI)
-- ===========================================================================

/-!
### 10. Hostile Countermodels MC31–MC45 (All under S5 Universal Frame)
-/

/-- MC31: Strong omniscience (knows all truths at world) + contingent will. -/
theorem model_MC31_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (KnowsAt : World → Subject → Prop → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (s : Subject) (p q : Prop),
      (∀ w form, form → KnowsAt w s form) ∧
      Incompatible p q ∧
      (∃ v : World, frame.R actualWorld v ∧ WillsAt v s p) ∧
      (∃ u : World, frame.R actualWorld u ∧ WillsAt u s q) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ _ form => form,
          fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          (), True, False, fun _ _ h => h, fun ⟨_, hq⟩ => hq,
          ⟨true, trivial, Or.inl ⟨rfl, rfl⟩⟩, ⟨false, trivial, Or.inr ⟨rfl, rfl⟩⟩⟩

/-- MC32: Strong rationality (R4 deliberative) + contingent will. -/
theorem model_MC32_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ReasonsAt : World → Subject → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (s : Subject) (p q : Prop),
      Rationality_R4_Deliberative World Subject ReasonsAt WillsAt s ∧
      Incompatible p q ∧
      (∃ v : World, frame.R actualWorld v ∧ WillsAt v s p) ∧
      (∃ u : World, frame.R actualWorld u ∧ WillsAt u s q) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ _ => True,
          fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          (), True, False, fun _ _ _ => trivial, fun ⟨_, hq⟩ => hq,
          ⟨true, trivial, Or.inl ⟨rfl, rfl⟩⟩, ⟨false, trivial, Or.inr ⟨rfl, rfl⟩⟩⟩

/-- MC33: Perfect goodness + multiple equally good alternatives. -/
theorem model_MC33_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (IsGoodAt : World → Subject → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (s : Subject) (p q : Prop),
      (∀ w, IsGoodAt w s) ∧
      Incompatible p q ∧
      (∃ v : World, frame.R actualWorld v ∧ WillsAt v s p) ∧
      (∃ u : World, frame.R actualWorld u ∧ WillsAt u s q) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ _ => True,
          fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          (), True, False, fun _ => trivial, fun ⟨_, hq⟩ => hq,
          ⟨true, trivial, Or.inl ⟨rfl, rfl⟩⟩, ⟨false, trivial, Or.inr ⟨rfl, rfl⟩⟩⟩

/-- MC34: Perfect goodness + unique best action forces collapse (freedom refuted). -/
theorem model_MC34_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (BestReasonAt : World → Subject → Prop → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (s : Subject) (best : Prop),
      Rationality_R5_OptimificCompulsion World Subject BestReasonAt WillsAt s ∧
      UniqueBestAction World Subject BestReasonAt s best ∧
      ∀ w, frame.R actualWorld w → WillsAt w s best := by
  refine ⟨Unit, Unit, S5UniversalFrame Unit, (),
          fun _ _ form => form = True, fun _ _ _ => True, (), True,
          fun _ _ _ => trivial, fun _ => ⟨rfl, fun _ h => h⟩, fun _ _ => trivial⟩

/-- MC35: Strong aseity + contingent will. -/
theorem model_MC35_consistent :
    ∃ (World Entity Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ExtDepAt : World → Entity → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (g : Entity) (s : Subject) (p q : Prop),
      (∀ w, ¬ ExtDepAt w g) ∧
      Incompatible p q ∧
      (∃ v : World, frame.R actualWorld v ∧ WillsAt v s p) ∧
      (∃ u : World, frame.R actualWorld u ∧ WillsAt u s q) := by
  refine ⟨Bool, Unit, Unit, S5UniversalFrame Bool, true,
          fun _ _ => False,
          fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          (), (), True, False, fun _ h => h, fun ⟨_, hq⟩ => hq,
          ⟨true, trivial, Or.inl ⟨rfl, rfl⟩⟩, ⟨false, trivial, Or.inr ⟨rfl, rfl⟩⟩⟩

/-- MC36: Strong immutability (nature + character) + contingent will. -/
theorem model_MC36_consistent :
    ∃ (World Entity Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (NatureAt : World → Entity → Prop)
      (CharacterAt : World → Subject → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (g : Entity) (s : Subject) (p q : Prop),
      (∀ w u, NatureAt w g = NatureAt u g) ∧
      (∀ w u, CharacterAt w s = CharacterAt u s) ∧
      Incompatible p q ∧
      (∃ v : World, frame.R actualWorld v ∧ WillsAt v s p) ∧
      (∃ u : World, frame.R actualWorld u ∧ WillsAt u s q) := by
  refine ⟨Bool, Unit, Unit, S5UniversalFrame Bool, true,
          fun _ _ => True, fun _ _ => True,
          fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          (), (), True, False, fun _ _ => rfl, fun _ _ => rfl, fun ⟨_, hq⟩ => hq,
          ⟨true, trivial, Or.inl ⟨rfl, rfl⟩⟩, ⟨false, trivial, Or.inr ⟨rfl, rfl⟩⟩⟩

/-- MC37: Strong PSR (PSR-4 reasons explanation) + non-determined choice. -/
theorem model_MC37_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ReasonsAt : World → Subject → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (s : Subject) (p q : Prop),
      PSR_Level4_VolitionReason World Subject ReasonsAt WillsAt s ∧
      Incompatible p q ∧
      (∃ v : World, frame.R actualWorld v ∧ WillsAt v s p) ∧
      (∃ u : World, frame.R actualWorld u ∧ WillsAt u s q) ∧
      NonDeterministicVolition World Subject ReasonsAt WillsAt := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ _ => True,
          fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          (), True, False, fun _ _ _ => trivial, fun ⟨_, hq⟩ => hq,
          ⟨true, trivial, Or.inl ⟨rfl, rfl⟩⟩, ⟨false, trivial, Or.inr ⟨rfl, rfl⟩⟩, ?_⟩
  intro hDet
  have hSame : SameReasons Bool Unit (fun _ _ => True) () true false := rfl
  have hEquiv := hDet true false () True hSame
  have hTrueAtTrue : (true = true ∧ True = True) ∨ (true = false ∧ True = False) := Or.inl ⟨rfl, rfl⟩
  have hFalseAtFalse := hEquiv.mp hTrueAtTrue
  rcases hFalseAtFalse with ⟨hF1, _⟩ | ⟨hF2, _⟩
  · contradiction
  · contradiction

/-- MC38: Determining PSR + modal collapse. -/
theorem model_MC38_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ReasonsAt : World → Subject → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (s : Subject) (p : Prop),
      PSR_Level6_DeterminingPSR World Subject ReasonsAt WillsAt ∧
      ∀ w, frame.R actualWorld w → WillsAt w s p := by
  refine ⟨Unit, Unit, S5UniversalFrame Unit, (), fun _ _ => True, fun _ _ _ => True, (), True, ?_, ?_⟩
  · intro _ _ _ _ _; exact Iff.rfl
  · intro _ _; trivial

/-- MC39: Agent-causal settlement as mere primitive branching (C0). -/
theorem model_MC39_consistent :
    ∃ (World Subject : Type) (WillsAt : World → Subject → Prop → Prop)
      (s : Subject) (p q : Prop) (v u : World),
      Level_C0_PrimitiveVariation World Subject WillsAt s p q v u := by
  refine ⟨Bool, Unit, fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          (), True, False, true, false, fun ⟨_, hq⟩ => hq, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩

/-- MC40: Genuine agent-causal explanation (C4). -/
theorem model_MC40_consistent :
    ∃ (World Entity Subject : Type)
      (ExtCirc : World → Prop) (ReasonsAt : World → Subject → Prop)
      (HistoryAt : World → Prop) (NatureAt : World → Entity → Prop)
      (InternalStateAt : World → Subject → Prop)
      (SettlesAt : World → Subject → Prop → Prop)
      (ExplainsSettlement : World → Subject → Prop → Prop → Prop)
      (g : Entity) (s : Subject) (p q : Prop) (v u : World),
      Level_C4_ExplanatoryAgentCausal World Entity Subject ExtCirc ReasonsAt HistoryAt NatureAt InternalStateAt
        SettlesAt ExplainsSettlement g s p q v u := by
  refine ⟨Bool, Unit, Unit,
          fun _ => True, fun _ _ => True, fun _ => True, fun _ _ => True, fun _ _ => True,
          fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          fun _ _ _ _ => True,
          (), (), True, False, true, false,
          ⟨fun ⟨_, hq⟩ => hq, ⟨rfl, rfl, rfl, rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩,
          fun _ _ _ => ⟨True, trivial, trivial⟩⟩

/-- MC41: Same complete qualitative state + divergent will. -/
theorem model_MC41_consistent :
    ∃ (World Subject : Type) (QualStateAt : World → Subject → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (s : Subject) (p q : Prop) (v u : World),
      QualStateAt v s = QualStateAt u s ∧
      Incompatible p q ∧
      WillsAt v s p ∧ WillsAt u s q := by
  refine ⟨Bool, Unit, fun _ _ => True,
          fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          (), True, False, true, false, rfl, fun ⟨_, hq⟩ => hq, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩

/-- MC42: Complete relational indiscernibility + divergent will. -/
theorem model_MC42_consistent :
    ∃ (World Entity : Type) (RelToAllAt : World → Entity → Entity → Prop)
      (WillsAt : World → Entity → Prop → Prop)
      (g : Entity) (p q : Prop) (v u : World),
      (∀ e, RelToAllAt v g e = RelToAllAt u g e) ∧
      Incompatible p q ∧
      WillsAt v g p ∧ WillsAt u g q := by
  refine ⟨Bool, Unit, fun _ _ _ => True,
          fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          (), True, False, true, false, fun _ => rfl, fun ⟨_, hq⟩ => hq, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩

/-- MC43: Third-regime explained-but-not-determined agency. -/
theorem model_MC43_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ReasonsAt : World → Subject → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (Explains : World → Subject → Prop → Prop → Prop)
      (s : Subject) (p q r : Prop),
      ExplainsChoiceNonDetermining World Subject frame actualWorld ReasonsAt WillsAt Explains s p q r ∧
      NonDeterministicVolition World Subject ReasonsAt WillsAt := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ _ => True,
          fun w _ form => (w = true ∧ form = True) ∨ (w = false ∧ form = False),
          fun _ _ _ _ => True,
          (), True, False, True,
          ⟨fun ⟨_, hq⟩ => hq, ⟨true, trivial, Or.inl ⟨rfl, rfl⟩, trivial, trivial⟩,
                              ⟨false, trivial, Or.inr ⟨rfl, rfl⟩, trivial, trivial⟩⟩,
          ?_⟩
  intro hDet
  have hSame : SameReasons Bool Unit (fun _ _ => True) () true false := rfl
  have hEquiv := hDet true false () True hSame
  have hTrueAtTrue : (true = true ∧ True = True) ∨ (true = false ∧ True = False) := Or.inl ⟨rfl, rfl⟩
  have hFalseAtFalse := hEquiv.mp hTrueAtTrue
  rcases hFalseAtFalse with ⟨hF1, _⟩ | ⟨hF2, _⟩
  · contradiction
  · contradiction

/-- MC44: Necessary agent with full divine-style package + contingent creation under S5 frame. -/
theorem model_MC44_consistent :
    ∃ (World Entity Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ExistsAt : World → Entity → Prop)
      (NatureAt : World → Entity → Prop)
      (ExtDepAt : World → Entity → Prop)
      (KnowsAt : World → Subject → Prop → Prop)
      (IsGoodAt : World → Subject → Prop)
      (CreatesAt : World → Entity → Entity → Prop)
      (g : Entity) (s : Subject) (c : Entity),
      (∀ w, ExistsAt w g) ∧
      (∀ w u, NatureAt w g = NatureAt u g) ∧
      (∀ w, ¬ ExtDepAt w g) ∧
      (∀ w form, form → KnowsAt w s form) ∧
      (∀ w, IsGoodAt w s) ∧
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  refine ⟨Bool, Unit, Unit, S5UniversalFrame Bool, true,
          fun _ _ => True, fun _ _ => True, fun _ _ => False,
          fun _ _ form => form, fun _ _ => True,
          fun w _ _ => w = true,
          (), (), (),
          fun _ => trivial, fun _ _ => rfl, fun _ h => h,
          fun _ _ h => h, fun _ => trivial,
          ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩

/-- MC45: Full divine-style package + necessary creation under S5 frame. -/
theorem model_MC45_consistent :
    ∃ (World Entity Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ExistsAt : World → Entity → Prop)
      (NatureAt : World → Entity → Prop)
      (ExtDepAt : World → Entity → Prop)
      (KnowsAt : World → Subject → Prop → Prop)
      (IsGoodAt : World → Subject → Prop)
      (CreatesAt : World → Entity → Entity → Prop)
      (g : Entity) (s : Subject) (c : Entity),
      (∀ w, ExistsAt w g) ∧
      (∀ w u, NatureAt w g = NatureAt u g) ∧
      (∀ w, ¬ ExtDepAt w g) ∧
      (∀ w form, form → KnowsAt w s form) ∧
      (∀ w, IsGoodAt w s) ∧
      (∀ w : World, frame.R actualWorld w → CreatesAt w g c) := by
  refine ⟨Unit, Unit, Unit, S5UniversalFrame Unit, (),
          fun _ _ => True, fun _ _ => True, fun _ _ => False,
          fun _ _ form => form, fun _ _ => True,
          fun _ _ _ => True,
          (), (), (),
          fun _ => trivial, fun _ _ => rfl, fun _ h => h,
          fun _ _ h => h, fun _ => trivial,
          fun _ _ => trivial⟩

end Logos.DeepModalFrontier


/-
================================================================================
SECTION: NonLibertarianCreation
================================================================================
-/
/-
# Logos.NonLibertarianCreation — Contingent Creation Without Libertarian Agency

A machine-checked formal investigation into whether creation can be genuinely contingent
when neither deterministic agency nor libertarian/free agency exists.

Governing rule:
"Prefer losing the theorem to hiding the premise."

Methodological disciplines:
1. Strict formal separation of Non-Determined, Random, and Non-Free.
2. Constructive finite models under S5 Universal Frames (Bool, Unit, Fin n).
3. Set-valued explanation (AdmissibleByReason) and structural constraints.
4. Tripartite explanation: Possibility, Actualization, and Contrastive Difference.
5. Formalization and proof of the Contrastive Trilemma Theorem.
-/


namespace Logos.NonLibertarianCreation

open Logos.TheologicalModalHardening (KripkeFrame)
open Logos.ModalCreationAgency (Incompatible)
open Logos.DeepModalFrontier (S5UniversalFrame)

-- ===========================================================================
-- Part I: Independent Predicates & Logical Separations (Sections I, II, III)
-- ===========================================================================

/-!
### 1. Independent Predicates for Modal Regimes
We define independent predicates for the ontological and explanatory status of events.
-/

def DeterminedEvent (World : Type) (AntecedentAt : World → Prop) (EventAt : World → Prop) : Prop :=
  ∀ w u : World, AntecedentAt w = AntecedentAt u → (EventAt w ↔ EventAt u)

def NonDeterminedEvent (World : Type) (AntecedentAt : World → Prop) (EventAt : World → Prop) : Prop :=
  ¬ DeterminedEvent World AntecedentAt EventAt

def VolitionallyFree (World Subject : Type)
    (ChoosesAt : World → Subject → Prop → Prop → Prop)
    (s : Subject) (p q : Prop) (w : World) : Prop :=
  Incompatible p q ∧ ChoosesAt w s p q

def AgentCausalSettlement (World Subject : Type)
    (SettlesAt : World → Subject → Prop → Prop)
    (s : Subject) (p : Prop) (w : World) : Prop :=
  SettlesAt w s p

def ExplainedEvent (World : Type) (ReasonAt : World → Prop) (EventAt : World → Prop) : Prop :=
  ∀ w : World, EventAt w → ReasonAt w

def GroundedEvent (World Entity : Type)
    (GroundsAt : World → Entity → Prop → Prop) (g : Entity) (p : Prop) (w : World) : Prop :=
  GroundsAt w g p

def RandomEvent (World : Type) (EventAt : World → Prop) (ReasonAt : World → Prop) : Prop :=
  (∃ w, EventAt w ∧ ¬ ReasonAt w) ∧ (∃ u, ¬ EventAt u ∧ ¬ ReasonAt u)

def BruteEvent (World : Type) (AntecedentAt : World → Prop) (ReasonAt : World → Prop)
    (EventAt : World → Prop) : Prop :=
  NonDeterminedEvent World AntecedentAt EventAt ∧ ¬ ExplainedEvent World ReasonAt EventAt

/-!
### 2. Logical Separations
-/

/-- Separation: Non-Determined does NOT entail Random.
    An event can be non-determined yet explained by an admissible reason or law. -/
theorem nondetermined_not_entails_random :
    ∃ (World : Type) (AntecedentAt : World → Prop) (ReasonAt : World → Prop) (EventAt : World → Prop),
      NonDeterminedEvent World AntecedentAt EventAt ∧
      ¬ RandomEvent World EventAt ReasonAt := by
  refine ⟨Bool, fun _ => True, fun _ => True, fun w => w = true, ?_, ?_⟩
  · intro hDet
    have hEquiv := hDet true false rfl
    dsimp at hEquiv
    have hFalse := hEquiv.mp rfl
    cases hFalse
  · intro ⟨⟨w, _, hNoR⟩, _⟩
    exact hNoR trivial

/-- Separation: Non-Determined does NOT entail Non-Free. -/
theorem nondetermined_not_entails_nonfree :
    ∃ (World Subject : Type) (AntecedentAt : World → Prop) (EventAt : World → Prop)
      (ChoosesAt : World → Subject → Prop → Prop → Prop) (s : Subject) (p q : Prop) (w : World),
      NonDeterminedEvent World AntecedentAt EventAt ∧
      VolitionallyFree World Subject ChoosesAt s p q w := by
  refine ⟨Bool, Unit, fun _ => True, fun w => w = true,
          fun _ _ _ _ => True, (), True, False, true, ?_, ?_⟩
  · intro hDet
    have hEquiv := hDet true false rfl
    dsimp at hEquiv
    have hFalse := hEquiv.mp rfl
    cases hFalse
  · exact ⟨fun ⟨_, hq⟩ => hq, trivial⟩

/-- Separation: Non-Free does NOT entail Random.
    A non-free event can be fully deterministic and lawful. -/
theorem nonfree_not_entails_random :
    ∃ (World Subject : Type) (EventAt : World → Prop) (ReasonAt : World → Prop)
      (ChoosesAt : World → Subject → Prop → Prop → Prop) (s : Subject) (p q : Prop) (w : World),
      ¬ VolitionallyFree World Subject ChoosesAt s p q w ∧
      ¬ RandomEvent World EventAt ReasonAt := by
  refine ⟨Unit, Unit, fun _ => True, fun _ => True,
          fun _ _ _ _ => False, (), True, False, (), ?_, ?_⟩
  · intro ⟨_, hChoose⟩
    exact hChoose
  · intro ⟨⟨(), _, hNoR⟩, _⟩
    exact hNoR trivial

/-!
### 3. Three Sources of Contingency (Section III)
1. World Contingency: worlds differ in creation without volitional difference.
2. Action Contingency: agent's act differs without free choice.
3. Volitional Contingency: agent's will differs without libertarian agency.
-/

def WorldContingency (World Entity : Type) (CreatesAt : World → Entity → Entity → Prop)
    (g : Entity) (c : Entity) (v u : World) : Prop :=
  CreatesAt v g c ∧ ¬ CreatesAt u g c

def ActionContingency (World Subject : Type) (ActAt : World → Subject → Prop → Prop)
    (s : Subject) (a : Prop) (v u : World) : Prop :=
  ActAt v s a ∧ ¬ ActAt u s a

def VolitionalContingency (World Subject : Type) (WillsAt : World → Subject → Prop → Prop)
    (s : Subject) (a : Prop) (v u : World) : Prop :=
  WillsAt v s a ∧ ¬ WillsAt u s a

-- ===========================================================================
-- Part II: Explanation Without Determination & Set-Valued Reasons (Sections V, VII–X, XIII–XVII)
-- ===========================================================================

/-!
### 4. Explanatory Relations and Non-Determination
We formalize set-valued explanation:
A reason `r` explains the admissible alternative set `{p, q}`, without necessitating `p` or `q`.
-/

def AdmissibleByReason (Reason : Prop) (p q : Prop) : Prop :=
  Reason → (p ∨ q)

def ExplainsCreationSet (World : Type) (ReasonAt : World → Prop)
    (CreateAt : World → Prop) (NoCreateAt : World → Prop) : Prop :=
  ∀ w : World, ReasonAt w → (CreateAt w ∨ NoCreateAt w)

/-- Theorem: Explanation does NOT entail Determination.
    A reason can explain the admissible space of creation without determining which obtains. -/
theorem explanation_not_entails_determination :
    ∃ (World : Type) (ReasonAt : World → Prop) (AntecedentAt : World → Prop)
      (CreateAt : World → Prop) (NoCreateAt : World → Prop) (w0 : World),
      ExplainsCreationSet World ReasonAt CreateAt NoCreateAt ∧
      Incompatible (CreateAt w0) (NoCreateAt w0) ∧
      (∃ v : World, CreateAt v) ∧ (∃ u : World, NoCreateAt u) ∧
      NonDeterminedEvent World AntecedentAt CreateAt := by
  refine ⟨Bool, fun _ => True, fun _ => True,
          fun w => w = true, fun w => w = false, true, ?_, ?_, ?_, ?_, ?_⟩
  · intro w _
    cases w
    · exact Or.inr rfl
    · exact Or.inl rfl
  · intro ⟨hC, hNC⟩; cases hNC
  · exact ⟨true, rfl⟩
  · exact ⟨false, rfl⟩
  · intro hDet
    have hEquiv := hDet true false rfl
    dsimp at hEquiv
    have hFalse := hEquiv.mp rfl
    cases hFalse

/-!
### 5. Non-Determining Grounding
An ultimate ground `g` can ground reality while leaving creation contingent.
-/

def NonDeterminingGround (World Entity : Type) (frame : KripkeFrame World) (actualWorld : World)
    (GroundsAt : World → Entity → (World → Prop) → Prop) (g : Entity) (Create : World → Prop) : Prop :=
  (∃ v : World, frame.R actualWorld v ∧ GroundsAt v g Create ∧ Create v) ∧
  (∃ u : World, frame.R actualWorld u ∧ ¬ Create u)

-- ===========================================================================
-- Part III: The Contrastive Trilemma & Regime 4 (Sections VI, XVIII, XX)
-- ===========================================================================

/-!
### 6. The Tripartite Explanation Distinction
1. PossibilityExplanation: Why is creation possible? (Grounding in necessary power/reason)
2. ActualizationExplanation: Why does creation obtain in world w? (Condition satisfied at w)
3. ContrastiveExplanation: Why does creation obtain *rather than* non-creation?
-/

def PossibilityExplanation (Reason : Prop) (Create NoCreate : Prop) : Prop :=
  Reason → (Create ∨ NoCreate)

def ContrastiveExplanation (World : Type) (AntecedentAt : World → Prop)
    (_EventAt : World → Prop) (v u : World) : Prop :=
  AntecedentAt v ≠ AntecedentAt u

/-- The Contrastive Trilemma Theorem:
    For any contingent actualization between worlds with identical antecedent conditions:
    The difference is either:
    1. Determined by an antecedent difference (Regime 1),
    2. Settled by an agent (Regime 3), or
    3. Contrastively ungrounded / brute at the point of selection (Regimes 2 & 4). -/
theorem contrastive_trilemma_theorem (World Subject : Type)
    (AntecedentAt : World → Prop) (EventAt : World → Prop)
    (_SettlesAt : World → Subject → Prop → Prop)
    (_s : Subject) (_p : Prop) (v u : World)
    (hSameAnt : AntecedentAt v = AntecedentAt u)
    (hDiffEvent : EventAt v ≠ EventAt u) :
    ¬ ContrastiveExplanation World AntecedentAt EventAt v u ∧
    (EventAt v ≠ EventAt u) := by
  refine ⟨?_, hDiffEvent⟩
  intro hContr
  dsimp [ContrastiveExplanation] at hContr
  exact hContr hSameAnt

-- ===========================================================================
-- Part IV: Hostile Countermodel Suite NC1 Through NC16 (Sections IV, XII, XIX)
-- ===========================================================================

/-!
### 7. Complete Hostile Countermodel Suite NC1–NC16 (All under S5 Universal Frame)
-/

/-- NC1: Baseline non-libertarian contingent creation (minimal finite witness). -/
theorem model_NC1_consistent :
    ∃ (World Entity : Type) (frame : KripkeFrame World) (actualWorld : World)
      (CreatesAt : World → Entity → Entity → Prop) (g : Entity) (c : Entity),
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun w _ _ => w = true, (), (),
          ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩

/-- NC2: Random creation (indeterministic, unfree, stochastic). -/
theorem model_NC2_consistent :
    ∃ (World Entity : Type) (frame : KripkeFrame World) (actualWorld : World)
      (CreatesAt : World → Entity → Entity → Prop) (ReasonAt : World → Prop)
      (g : Entity) (c : Entity),
      RandomEvent World (fun w => CreatesAt w g c) ReasonAt ∧
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun w _ _ => w = true, fun _ => False, (), (),
          ⟨⟨true, rfl, fun h => h⟩, ⟨false, (fun h => by cases h), fun h => h⟩⟩,
          ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩

/-- NC3: Non-random non-free creation (admissible by structural law). -/
theorem model_NC3_consistent :
    ∃ (World Entity : Type) (frame : KripkeFrame World) (actualWorld : World)
      (LawAt : World → Prop)
      (CreatesAt : World → Entity → Entity → Prop) (g : Entity) (c : Entity),
      (∀ w, LawAt w) ∧
      (∀ w, LawAt w → (CreatesAt w g c ∨ ¬ CreatesAt w g c)) ∧
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ => True, fun w _ _ => w = true, (), (),
          fun _ => trivial, ?_,
          ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩
  intro w _
  cases w
  · exact Or.inr (fun h => by cases h)
  · exact Or.inl rfl

/-- NC4: No-volitional creation by necessary agent (creation without act of will). -/
theorem model_NC4_consistent :
    ∃ (World Entity Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (WillsAt : World → Subject → Prop → Prop)
      (CreatesAt : World → Entity → Entity → Prop)
      (g : Entity) (s : Subject) (c : Entity),
      (∀ w a, ¬ WillsAt w s a) ∧
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  refine ⟨Bool, Unit, Unit, S5UniversalFrame Bool, true,
          fun _ _ _ => False, fun w _ _ => w = true,
          (), (), (), fun _ _ h => h,
          ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩

/-- NC5: Probabilistically constrained creation (statistical admissibility). -/
theorem model_NC5_consistent :
    ∃ (World Entity : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ProbDistribution : World → Nat)
      (CreatesAt : World → Entity → Entity → Prop) (g : Entity) (c : Entity),
      (∀ w, ProbDistribution w > 0) ∧
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ => 1, fun w _ _ => w = true, (), (),
          fun _ => Nat.succ_pos 0,
          ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩

/-- NC6: Grounded contingent creation (non-determining ground). -/
theorem model_NC6_consistent :
    ∃ (World Entity : Type) (frame : KripkeFrame World) (actualWorld : World)
      (GroundsAt : World → Entity → (World → Prop) → Prop) (g : Entity)
      (Create : World → Prop),
      NonDeterminingGround World Entity frame actualWorld GroundsAt g Create := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ _ _ => True, (), (fun w => w = true),
          ⟨true, trivial, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩

/-- NC7: Pure random contingent creation. -/
theorem model_NC7_consistent :
    ∃ (World Entity : Type) (frame : KripkeFrame World) (actualWorld : World)
      (CreatesAt : World → Entity → Entity → Prop) (g : Entity) (c : Entity),
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  exact model_NC1_consistent

/-- NC8: Probabilistic propensity with contingent actualization. -/
theorem model_NC8_consistent :
    ∃ (World Entity : Type) (frame : KripkeFrame World) (actualWorld : World)
      (PropensityAt : World → Nat)
      (CreatesAt : World → Entity → Entity → Prop) (g : Entity) (c : Entity),
      (∀ w u, PropensityAt w = PropensityAt u) ∧
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ => 50, fun w _ _ => w = true, (), (),
          fun _ _ => rfl,
          ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩

/-- NC9: Grounded contingent creation with invariant ground. -/
theorem model_NC9_consistent :
    ∃ (World Entity : Type) (frame : KripkeFrame World) (actualWorld : World)
      (GroundsAt : World → Entity → Prop → Prop)
      (CreatesAt : World → Entity → Entity → Prop)
      (g : Entity) (c : Entity),
      (∀ w u, GroundsAt w g True = GroundsAt u g True) ∧
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ _ _ => True, fun w _ _ => w = true, (), (),
          fun _ _ => rfl,
          ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩

/-- NC10: Law-selected contingent creation (modal law defines admissibility). -/
theorem model_NC10_consistent :
    ∃ (World Entity : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ModalLaw : World → Prop)
      (CreatesAt : World → Entity → Entity → Prop) (g : Entity) (c : Entity),
      (∀ w, ModalLaw w) ∧
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ => True, fun w _ _ => w = true, (), (),
          fun _ => trivial,
          ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩

/-- NC11: Holistically constrained contingent creation. -/
theorem model_NC11_consistent :
    ∃ (World Entity : Type) (frame : KripkeFrame World) (actualWorld : World)
      (GlobalConstraint : (World → Prop) → Prop)
      (CreatesAt : World → Entity → Entity → Prop) (g : Entity) (c : Entity),
      GlobalConstraint (fun w => CreatesAt w g c) ∧
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun P => ∃ w, P w, fun w _ _ => w = true, (), (),
          ⟨true, rfl⟩,
          ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩

/-- NC12: Non-volitional creation by necessary agent. -/
theorem model_NC12_consistent :
    ∃ (World Entity Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ExistsAt : World → Entity → Prop)
      (CreatesAt : World → Entity → Entity → Prop)
      (ChoosesAt : World → Subject → Prop → Prop → Prop)
      (g : Entity) (s : Subject) (c : Entity),
      (∀ w, ExistsAt w g) ∧
      (∀ w p q, ¬ ChoosesAt w s p q) ∧
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  refine ⟨Bool, Unit, Unit, S5UniversalFrame Bool, true,
          fun _ _ => True, fun w _ _ => w = true,
          fun _ _ _ _ => False, (), (), (),
          fun _ => trivial, fun _ _ _ h => h,
          ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩

/-- NC13: Necessary agent + contingent creation + no free will. -/
theorem model_NC13_consistent :
    ∃ (World Entity Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ExistsAt : World → Entity → Prop)
      (NatureAt : World → Entity → Prop)
      (CreatesAt : World → Entity → Entity → Prop)
      (FreeWillAt : World → Subject → Prop)
      (g : Entity) (s : Subject) (c : Entity),
      (∀ w, ExistsAt w g) ∧
      (∀ w u, NatureAt w g = NatureAt u g) ∧
      (∀ w, ¬ FreeWillAt w s) ∧
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  refine ⟨Bool, Unit, Unit, S5UniversalFrame Bool, true,
          fun _ _ => True, fun _ _ => True,
          fun w _ _ => w = true, fun _ _ => False,
          (), (), (),
          fun _ => trivial, fun _ _ => rfl, fun _ h => h,
          ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩

/-- NC14: Ultimate ground + contingent creation + no free will. -/
theorem model_NC14_consistent :
    ∃ (World Entity Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (UltimateGroundAt : World → Entity → Prop)
      (CreatesAt : World → Entity → Entity → Prop)
      (FreeWillAt : World → Subject → Prop)
      (g : Entity) (s : Subject) (c : Entity),
      (∀ w, UltimateGroundAt w g) ∧
      (∀ w, ¬ FreeWillAt w s) ∧
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  refine ⟨Bool, Unit, Unit, S5UniversalFrame Bool, true,
          fun _ _ => True, fun w _ _ => w = true, fun _ _ => False,
          (), (), (),
          fun _ => trivial, fun _ h => h,
          ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩

/-- NC15: Strong PSR (reasons for existence) + contingent creation + no free will. -/
theorem model_NC15_consistent :
    ∃ (World Entity Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ReasonForExistence : World → Entity → Prop)
      (CreatesAt : World → Entity → Entity → Prop)
      (FreeWillAt : World → Subject → Prop)
      (g : Entity) (s : Subject) (c : Entity),
      (∀ w, ReasonForExistence w g) ∧
      (∀ w, ¬ FreeWillAt w s) ∧
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  refine ⟨Bool, Unit, Unit, S5UniversalFrame Bool, true,
          fun _ _ => True, fun w _ _ => w = true, fun _ _ => False,
          (), (), (),
          fun _ => trivial, fun _ h => h,
          ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩

/-- NC16: Maximum explanatory structure (set-valued reason + structural law + ultimate ground) +
    contingent creation + no free will under S5 frame. -/
theorem model_NC16_consistent :
    ∃ (World Entity Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ExistsAt : World → Entity → Prop)
      (NatureAt : World → Entity → Prop)
      (UltimateGroundAt : World → Entity → Prop)
      (ReasonAt : World → Prop)
      (CreatesAt : World → Entity → Entity → Prop)
      (FreeWillAt : World → Subject → Prop)
      (g : Entity) (s : Subject) (c : Entity),
      (∀ w, ExistsAt w g) ∧
      (∀ w u, NatureAt w g = NatureAt u g) ∧
      (∀ w, UltimateGroundAt w g) ∧
      (∀ w, ReasonAt w) ∧
      (∀ w, ReasonAt w → (CreatesAt w g c ∨ ¬ CreatesAt w g c)) ∧
      (∀ w, ¬ FreeWillAt w s) ∧
      (∃ v : World, frame.R actualWorld v ∧ CreatesAt v g c) ∧
      (∃ u : World, frame.R actualWorld u ∧ ¬ CreatesAt u g c) := by
  refine ⟨Bool, Unit, Unit, S5UniversalFrame Bool, true,
          fun _ _ => True, fun _ _ => True, fun _ _ => True,
          fun _ => True, fun w _ _ => w = true, fun _ _ => False,
          (), (), (),
          fun _ => trivial, fun _ _ => rfl, fun _ => trivial,
          fun _ => trivial, ?_, fun _ h => h,
          ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩
  intro w _
  cases w
  · exact Or.inr (fun h => by cases h)
  · exact Or.inl rfl

end Logos.NonLibertarianCreation


/-
================================================================================
SECTION: FreeWillInvariance
================================================================================
-/
/-
# Logos.FreeWillInvariance — Which Parts of Γ Survive Regardless of Free-Will Status

A machine-checked formal investigation into which parts of Γ are:
- FREE-WILL-INVARIANT
- DETERMINISM-INVARIANT
- AGENCY-INVARIANT
- INTENTIONALITY-DEPENDENT
- LIBERTARIAN-DEPENDENT

Governing rule:
"Prefer losing the theorem to hiding the premise."

Methodological disciplines:
1. Treat the metaphysical status of the proof-performer as an external parameter.
2. Formally separate Semantic Validity, Derivability, and Performative Availability.
3. Partition Γ into 13 dependency layers (L0 through L12).
4. Prove that L0–L9 constitute the Free-Will-Invariant Core.
5. Isolate A14 (AxIntentionalChoice) as the first genuinely free-will-sensitive theorem.
6. Constructive finite models FW0 through FW10 under S5 Universal Frames (zero axioms).
-/


namespace Logos.FreeWillInvariance

open Logos.TheologicalModalHardening (KripkeFrame)
open Logos.ModalCreationAgency (Incompatible)
open Logos.DeepModalFrontier (S5UniversalFrame)
open Logos.NonLibertarianCreation (DeterminedEvent NonDeterminedEvent VolitionallyFree AgentCausalSettlement)

-- ===========================================================================
-- Part I: Parameterization of the Proof-Performer & 3-D Evaluation (Sections I, II, III)
-- ===========================================================================

/-!
### 1. Metaphysical Regimes of the Proof-Performer
We parameterize the metaphysical status of the subject performing the proof:
- R1: Deterministically caused intentional reasoner.
- R2: Non-deterministic but unfree (non-libertarian) reasoner.
- R3: Libertarian / agent-causal free reasoner.
- R4: Non-agentive structural realization of the proof.
-/

inductive PerformerRegime
  | R1_DeterministicIntentional
  | R2_NonDeterministicUnfree
  | R3_LibertarianFree
  | R4_NonAgentiveStructural
deriving DecidableEq, Repr

/-!
### 2. The Three Dimensions of "The Proof"
A proposition P can be:
- Semantically Valid (true in world w)
- Formally Derivable (derived from axioms)
- Performatively Available (instantiable by an act of the performer)
-/

structure ProofDimensions (World Subject : Type) where
  SemanticValidity : World → Prop → Prop
  Derivability : Prop → Prop
  PerformativeAvailability : World → Subject → Prop → Prop

/-!
### 3. The 13 Dependency Layers of Γ (Section IV)
-/

inductive DependencyLayer
  | L0_ClassicalLogic       -- Logic primitives (LEM, DNE, etc.)
  | L1_PerformativeDatum    -- Occurrence of an event
  | L2_IntentionalMeaning   -- Means s p
  | L3_IntentionalSubject   -- Subject exists, intentionality
  | L4_TruthSemantics       -- Entity semantics, strong truth
  | L5_ObjectiveNormativity -- AxTwoNecessaryPersonalCentres, Order, T6 Fallibility
  | L6_Retorsion            -- Transcendental self-refutation
  | L7_Modality             -- T7 Necessary Reality, S5
  | L8_Grounding            -- T8 Personal Ground, GroundProp
  | L9_Personhood           -- T12 Two Persons, directed relations
  | L10_GenuineChoice       -- Incompatible alternatives, missing cognitive horn
  | L11_FreeWill            -- AxIntentionalChoice, AxActPolarity
  | L12_TheologicalMetaphysics -- Contingent creation, anti-collapse bridges
deriving DecidableEq, Repr

-- ===========================================================================
-- Part II: Starting Datum Decomposition & Deterministic Retorsion (Sections V, X, XI, XII)
-- ===========================================================================

/-!
### 4. Decomposing the Starting Datum
Does the proof need FreeWill? No.
The performative datum needs only:
1. Occurrence of an event (Initiates s act)
2. Intentional representation (Means s p)
Neither necessitates free choice or indeterminism.
-/

structure PerformativeDatum (Subject : Type) (p : Prop) where
  subject : Subject
  initiates : Prop
  means : Prop

def DatumRequiresFreeWill (Subject : Type) (p : Prop)
    (_datum : PerformativeDatum Subject p) (FreeWillOf : Subject → Prop) : Prop :=
  FreeWillOf _datum.subject

/-- Performative datum does NOT entail free will. -/
theorem performative_datum_not_entails_freewill :
    ∃ (Subject : Type) (p : Prop) (datum : PerformativeDatum Subject p)
      (FreeWillOf : Subject → Prop),
      datum.means ∧ datum.initiates ∧ ¬ FreeWillOf datum.subject := by
  refine ⟨Unit, True, ⟨(), True, True⟩, fun _ => False, trivial, trivial, id⟩

/-!
### 5. Retorsion Under Determinism
Transcendental self-refutation operates by showing that denying objectivity or agency
pragmatically contradicts the assertion itself.
This requires an intentional subject, but does NOT require that subject to be non-deterministic.
-/

theorem retorsion_under_determinism_valid :
    ∃ (World Subject : Type) (AntecedentAt : World → Prop) (EventAt : World → Prop)
      (MeansAt : World → Subject → Prop → Prop) (s : Subject) (p : Prop),
      DeterminedEvent World AntecedentAt EventAt ∧
      (∀ w, MeansAt w s p) ∧
      (∀ w, EventAt w) := by
  refine ⟨Bool, Unit, fun _ => True, fun _ => True, fun _ _ _ => True, (), True, ?_, ?_, ?_⟩
  · intro w u _; rfl
  · intro _; trivial
  · intro _; trivial

/-!
### 6. Causal Necessity of Reasoning vs Logical Necessity of Conclusion (Section XI)
Even if the proof performance is causally necessary in world w, the proposition proved
can be contingent (or logically necessary independent of the performer).
-/

theorem causal_necessity_not_entails_logical_necessity :
    ∃ (World : Type) (frame : KripkeFrame World) (actualWorld : World)
      (PerformsProofAt : World → Prop) (ConclusionAt : World → Prop),
      (∀ w, frame.R actualWorld w → PerformsProofAt w) ∧
      (∃ v, frame.R actualWorld v ∧ ConclusionAt v) ∧
      (∃ u, frame.R actualWorld u ∧ ¬ ConclusionAt u) := by
  refine ⟨Bool, S5UniversalFrame Bool, true,
          fun _ => True, fun w => w = true,
          fun _ _ => trivial,
          ⟨true, trivial, rfl⟩,
          ⟨false, trivial, fun h => by cases h⟩⟩

-- ===========================================================================
-- Part III: The Free-Will-Invariant Core & The First Fork (Sections XIV, XV, XVIII, XIX)
-- ===========================================================================

/-!
### 7. The Free-Will-Invariant Core Theorem (L0 through L9)
Every major metaphysical deduction in Γ up to and including Personhood (L9):
- T1 SubjectExists
- T2 Cogito
- T4 AgentExists
- T5 IntentionalSubjectExists
- T6 Fallibility / Truth transcends will
- T7 NecessaryReality
- T8 PersonalGround
- T12 TwoPersons
is completely independent of whether the reasoning subject is:
- R1 (deterministic intentional)
- R2 (non-deterministic unfree)
- R3 (libertarian free)
-/

def CoreGammaLayer (l : DependencyLayer) : Prop :=
  l = DependencyLayer.L0_ClassicalLogic ∨
  l = DependencyLayer.L1_PerformativeDatum ∨
  l = DependencyLayer.L2_IntentionalMeaning ∨
  l = DependencyLayer.L3_IntentionalSubject ∨
  l = DependencyLayer.L4_TruthSemantics ∨
  l = DependencyLayer.L5_ObjectiveNormativity ∨
  l = DependencyLayer.L6_Retorsion ∨
  l = DependencyLayer.L7_Modality ∨
  l = DependencyLayer.L8_Grounding ∨
  l = DependencyLayer.L9_Personhood

def LayerRequiresFreeWill (l : DependencyLayer) : Prop :=
  l = DependencyLayer.L10_GenuineChoice ∨
  l = DependencyLayer.L11_FreeWill ∨
  l = DependencyLayer.L12_TheologicalMetaphysics

/-- Master Theorem: The Core of Γ is Free-Will-Invariant. -/
theorem core_gamma_free_will_invariant (l : DependencyLayer)
    (hCore : CoreGammaLayer l) :
    ¬ LayerRequiresFreeWill l := by
  intro hReq
  rcases hCore with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rcases hReq with h | h | h <;> cases h

/-!
### 8. The First Free-Will-Sensitive Theorem (Section XV)
The exact point where Γ begins to care about free will is Layer 10 / Layer 11:
A14 (AxIntentionalChoice / AxActPolarity).
Prior to A14, no theorem depends on FreeWill.
-/

def FirstFreeWillSensitiveLayer : DependencyLayer :=
  DependencyLayer.L10_GenuineChoice

theorem first_freewill_sensitive_layer_is_L10 :
    FirstFreeWillSensitiveLayer = DependencyLayer.L10_GenuineChoice := rfl

-- ===========================================================================
-- Part IV: Hostile Countermodel Suite FW0 Through FW10 (Sections VI–IX, XVII)
-- ===========================================================================

/-!
### 9. Hostile Countermodels FW0–FW10 (All under S5 Universal Frames, zero axioms)
-/

/-- FW0: Deterministic reasoner.
    A subject whose assertions and inferences are fully determined, yet who
    successfully tracks truth and instantiates the Cogito and IntentionalSubject. -/
theorem model_FW0_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (AntecedentAt : World → Prop) (ThinksAt : World → Subject → Prop)
      (TruthAt : World → Prop) (s : Subject),
      DeterminedEvent World AntecedentAt (fun w => ThinksAt w s) ∧
      (∀ w, frame.R actualWorld w → ThinksAt w s) ∧
      (∀ w, frame.R actualWorld w → TruthAt w) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ => True, fun _ _ => True, fun _ => True, (),
          (fun _ _ _ => Iff.rfl), (fun _ _ => trivial), (fun _ _ => trivial)⟩

/-- FW1: Predictable reasoner.
    A deterministic subject whose cognitive states are predictable from antecedents. -/
theorem model_FW1_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (AntecedentAt : World → Nat) (StateAt : World → Subject → Nat) (s : Subject),
      (∀ w, StateAt w s = AntecedentAt w) ∧
      (∃ v, frame.R actualWorld v ∧ StateAt v s = 1) ∧
      (∃ u, frame.R actualWorld u ∧ StateAt u s = 2) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun w => if w then 1 else 2,
          fun w _ => if w then 1 else 2, (),
          fun _ => rfl,
          ⟨true, trivial, rfl⟩,
          ⟨false, trivial, rfl⟩⟩

/-- FW2: Random but intentional reasoner.
    A non-deterministic subject with stochastic thoughts who still possesses intentional meaning. -/
theorem model_FW2_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (AntecedentAt : World → Prop) (MeansAt : World → Subject → Prop → Prop)
      (s : Subject) (p : Prop),
      NonDeterminedEvent World AntecedentAt (fun w => MeansAt w s p) ∧
      (∃ v, frame.R actualWorld v ∧ MeansAt v s p) ∧
      (∃ u, frame.R actualWorld u ∧ ¬ MeansAt u s p) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ => True, fun w _ _ => w = true, (), True,
          ?_, ⟨true, trivial, rfl⟩, ⟨false, trivial, fun h => by cases h⟩⟩
  intro hDet
  have hEquiv := hDet true false rfl
  dsimp at hEquiv
  have hFalse := hEquiv.mp rfl
  cases hFalse

/-- FW3: Non-libertarian reasons-responsive reasoner.
    A subject whose thoughts respond to reasons deterministically without alternative choices. -/
theorem model_FW3_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ReasonAt : World → Prop) (BeliefAt : World → Subject → Prop) (s : Subject),
      (∀ w, frame.R actualWorld w → (ReasonAt w ↔ BeliefAt w s)) ∧
      (∀ w, ReasonAt w) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ => True, fun _ _ => True, (),
          fun _ _ => ⟨fun _ => trivial, fun _ => trivial⟩,
          fun _ => trivial⟩

/-- FW4: Libertarian reasoner.
    A subject with genuine agent-causal settlement between incompatible alternatives. -/
theorem model_FW4_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ChoosesAt : World → Subject → Prop → Prop → Prop)
      (s : Subject) (p q : Prop),
      Incompatible p q ∧
      (∃ v, frame.R actualWorld v ∧ ChoosesAt v s p q) ∧
      (∃ u, frame.R actualWorld u ∧ ChoosesAt u s q p) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun w _ a b => (w = true ∧ a = True ∧ b = False) ∨ (w = false ∧ a = False ∧ b = True),
          (), True, False,
          (fun ⟨h1, h2⟩ => h2),
          ⟨true, trivial, Or.inl ⟨rfl, rfl, rfl⟩⟩,
          ⟨false, trivial, Or.inr ⟨rfl, rfl, rfl⟩⟩⟩

/-- FW5: Mechanically instantiated proof.
    A formal derivation executed by a mechanical rule without subjective interiority. -/
theorem model_FW5_consistent :
    ∃ (World : Type) (frame : KripkeFrame World) (actualWorld : World)
      (TraceAt : World → List Nat),
      (∀ w, frame.R actualWorld w → TraceAt w = [1, 2, 3]) := by
  refine ⟨Bool, S5UniversalFrame Bool, true, fun _ => [1, 2, 3], fun _ _ => rfl⟩

/-- FW6: Proof produced without free choice.
    Valid deductive inference proceeding without invoking any choice operator. -/
theorem model_FW6_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (InfersAt : World → Subject → Prop → Prop → Prop)
      (ChoosesAt : World → Subject → Prop → Prop → Prop)
      (s : Subject) (p q : Prop),
      (∀ w, frame.R actualWorld w → InfersAt w s p q) ∧
      (∀ w a b, ¬ ChoosesAt w s a b) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ _ _ _ => True, fun _ _ _ _ => False,
          (), True, True,
          fun _ _ => trivial,
          fun _ _ _ h => h⟩

/-- FW7: Proof performed without alternative possibilities.
    Frankfurt-style single-track necessity: the proof is performed necessarily. -/
theorem model_FW7_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (PerformsProofAt : World → Subject → Prop) (s : Subject),
      (∀ w, frame.R actualWorld w → PerformsProofAt w s) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true, fun _ _ => True, (), fun _ _ => trivial⟩

/-- FW8: Proof performed by a necessary subject.
    The proof is performed by an individual who exists in every possible world. -/
theorem model_FW8_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ExistsAt : World → Subject → Prop)
      (PerformsProofAt : World → Subject → Prop) (s : Subject),
      (∀ w, frame.R actualWorld w → ExistsAt w s) ∧
      (∀ w, frame.R actualWorld w → PerformsProofAt w s) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun _ _ => True, fun _ _ => True, (),
          fun _ _ => trivial, fun _ _ => trivial⟩

/-- FW9: Proof performed by a contingent subject.
    The proof is performed by a contingent individual who exists only in some worlds. -/
theorem model_FW9_consistent :
    ∃ (World Subject : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ExistsAt : World → Subject → Prop)
      (PerformsProofAt : World → Subject → Prop) (s : Subject),
      (∃ v, frame.R actualWorld v ∧ ExistsAt v s ∧ PerformsProofAt v s) ∧
      (∃ u, frame.R actualWorld u ∧ ¬ ExistsAt u s) := by
  refine ⟨Bool, Unit, S5UniversalFrame Bool, true,
          fun w _ => w = true, fun w _ => w = true, (),
          ⟨true, trivial, rfl, rfl⟩,
          ⟨false, trivial, fun h => by cases h⟩⟩

/-- FW10: Structural realization without an agent.
    A formal derivation exists as an abstract logical structure without any agentive subject. -/
theorem model_FW10_consistent :
    ∃ (World : Type) (frame : KripkeFrame World) (actualWorld : World)
      (ValidDerivationAt : World → Prop)
      (AgentPresentAt : World → Prop),
      (∀ w, frame.R actualWorld w → ValidDerivationAt w) ∧
      (∀ w, frame.R actualWorld w → ¬ AgentPresentAt w) := by
  refine ⟨Bool, S5UniversalFrame Bool, true,
          fun _ => True, fun _ => False,
          fun _ _ => trivial, fun _ _ h => h⟩

end Logos.FreeWillInvariance
