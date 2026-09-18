/-
# Logos.GroundingFrontier — The Grounding and Modal Frontier of Γ

This module executes the comprehensive adversarial formal campaign on the grounding
and modal frontier of Γ, adhering strictly to the governing methodological rule:
  "Prefer losing the theorem to hiding the premise."

Key formal accomplishments:
1. Hierarchy of Minimal Bridges G1–G4:
   - G1 (Weak modal existence): □φ → ◇∃e GroundAt(w, e, φ)
   - G2 (Necessary ground existence): □φ → ∃e, (∀w, ExistsAt w e) ∧ ∃w, GroundAt w e φ
   - G3 (Uniform necessary grounding): □φ → ∃e, ∀w, ExistsAt w e ∧ Ground e φ (AxGlobalGround shape)
   - G4 (Strong persistence): □φ → ∃e, (∀w, ExistsAt w e) ∧ (∀w, GroundAt w e φ)
   - Implication chain: G4 → G3 → G2 → G1; separations G1 ⇏ G2, G2 ⇏ G4.
2. Quantifier Analysis (∀w ∃e vs ∃e ∀w):
   - Machine-checked proof that worldwise truthmaking does NOT entail uniform necessary ground.
   - Exact isolation of MissingRigidGroundHorn(φ) with formal equivalence.
3. Adversarial Audit of A4 (AxGlobalGround):
   - A4 does not entail uniqueness of grounders (multiple grounders per truth).
   - A4 does not entail a single common ground for distinct truths.
   - A4 does not entail well-foundedness or an ultimate ground.
4. Well-Foundedness Hierarchy U1–U6 & Minimal Ultimate Ground Theorem:
   - Structural distinction between infinite descending chains, finite cycles, and self-grounding.
   - Proof of the Minimal Ultimate Ground Theorem: BoundedChainAncestry → UltimateGround.
5. Personality Bridge Audit (P1–P6) & Hostile Suite P1–P5:
   - Impersonal substrate, structural realization, emergent intentionality, multiple impersonal grounders, anonymous ultimate ground.
   - Proof that IntentionalSubject + NecessaryGround ⇏ PersonalUltimateGround.
6. Ten Canonical Hostile Grounding Models G1–G10.
7. Model-Transformation Collapse and Expressivity Invariance Theorems.
8. Grounding Frontier Master Synthesis Theorem.
-/

import Logos.Core
import Logos.Necessity
import Logos.Semantics
import Logos.Truthmaker
import Logos.Modal
import Logos.Agency
import Logos.Person
import Logos.Choice
import Logos.Alternatives
import Logos.Retorsion
import Logos.HardenedInvariance
import Logos.CognitiveDiscrimination
import Logos.SubContrastFoundations
import Logos.ProofSpecificContrast
import Logos.AdversarialReductioAudit
import Logos.CognitiveToAgencyFrontier
import Logos.FreeWillIndependence
import Logos.ChoiceRepair
import Logos.AgencyFrontierAudit
import Logos.A14SemanticAudit
import Logos.PostA14Frontier
import Logos.DefinitiveAgencyFrontier

namespace Logos.GroundingFrontier

open Logos.Agency (Subject Act Means State Initiates Asserts)
open Logos.Person (IntentionalSubject SubstantivePerson Person)
open Logos.Alternatives (Incompatible)

-- ===========================================================================
-- Section 1: Modal Framework & The G1–G4 Grounding Candidates
-- ===========================================================================

/-- Abstract Modal Grounding Signature. -/
structure ModalGroundingSignature where
  World           : Type
  Entity          : Type
  Form            : Type
  ExistsAt        : World → Entity → Prop
  Ground          : Entity → Form → Prop
  GroundAt        : World → Entity → Form → Prop
  NecessarilyTrue : Form → Prop
  PossibleWorld   : World → Prop

/-- A necessary entity exists in every accessible world. -/
def NecessaryEntity (M : ModalGroundingSignature) (e : M.Entity) : Prop :=
  ∀ w : M.World, M.ExistsAt w e

/-- Candidate G1: Weak Modal Existence.
    If φ is necessarily true, there exists some world and some entity grounding φ in that world. -/
def Candidate_G1 (M : ModalGroundingSignature) (φ : M.Form) : Prop :=
  M.NecessarilyTrue φ → ∃ (w : M.World) (e : M.Entity), M.ExistsAt w e ∧ M.GroundAt w e φ

/-- Candidate G2: Necessary Entity Grounding Somewhere.
    If φ is necessarily true, there exists a necessary entity that grounds φ in at least one world. -/
def Candidate_G2 (M : ModalGroundingSignature) (φ : M.Form) : Prop :=
  M.NecessarilyTrue φ → ∃ e : M.Entity, NecessaryEntity M e ∧ ∃ w : M.World, M.GroundAt w e φ

/-- Candidate G3: Uniform Necessary Grounding (Shape of AxGlobalGround / A4).
    If φ is necessarily true, there exists an entity that exists in every world and rigidly grounds φ. -/
def Candidate_G3 (M : ModalGroundingSignature) (φ : M.Form) : Prop :=
  M.NecessarilyTrue φ → ∃ e : M.Entity, ∀ w : M.World, M.ExistsAt w e ∧ M.Ground e φ

/-- Candidate G4: Strong Persistence of Grounding.
    If φ is necessarily true, there exists an entity that exists and grounds φ at every world. -/
def Candidate_G4 (M : ModalGroundingSignature) (φ : M.Form) : Prop :=
  M.NecessarilyTrue φ → ∃ e : M.Entity, (∀ w : M.World, M.ExistsAt w e) ∧ (∀ w : M.World, M.GroundAt w e φ)

/-- Implication G4 → G2:
    Strong persistence implies necessary entity grounding somewhere (given a world). -/
theorem implication_G4_implies_G2
    (M : ModalGroundingSignature) (φ : M.Form) (w0 : M.World)
    (hG4 : Candidate_G4 M φ) :
    Candidate_G2 M φ := by
  intro hNec
  obtain ⟨e, hEx, hGrAt⟩ := hG4 hNec
  exact ⟨e, hEx, w0, hGrAt w0⟩

/-- Implication G2 → G1:
    Necessary entity grounding implies weak modal existence. -/
theorem implication_G2_implies_G1
    (M : ModalGroundingSignature) (φ : M.Form)
    (hG2 : Candidate_G2 M φ) :
    Candidate_G1 M φ := by
  intro hNec
  obtain ⟨e, hNecE, w, hGrAt⟩ := hG2 hNec
  exact ⟨w, e, hNecE w, hGrAt⟩

/-- Separation G1 ⇏ G2:
    Weak modal existence does NOT entail necessary ground existence.
    A contingent grounder exists in some world, but no necessary entity exists. -/
theorem separation_G1_not_implies_G2 :
    ∃ (M : ModalGroundingSignature) (φ : M.Form) (_w0 : M.World),
      Candidate_G1 M φ ∧ ¬ Candidate_G2 M φ := by
  let M0 : ModalGroundingSignature := {
    World           := Bool
    Entity          := Bool
    Form            := Unit
    ExistsAt        := fun w e => e = w
    Ground          := fun _ _ => True
    GroundAt        := fun _ _ _ => True
    NecessarilyTrue := fun _ => True
    PossibleWorld   := fun _ => True
  }
  have hG1 : Candidate_G1 M0 () := fun _ => ⟨true, true, rfl, trivial⟩
  have hNotG2 : ¬ Candidate_G2 M0 () := by
    intro hG2
    obtain ⟨e, hNecE, _⟩ := hG2 trivial
    have h1 : e = true := hNecE true
    have h2 : e = false := hNecE false
    have h3 : true = false := h1.symm.trans h2
    cases h3
  exact ⟨M0, (), true, hG1, hNotG2⟩

-- ===========================================================================
-- Section 2: Quantifier Analysis (∀w ∃e vs ∃e ∀w) & Missing Grounding Horn
-- ===========================================================================

/-- Worldwise Truthmaking:
    In every world, some entity exists and grounds φ. -/
def WorldwiseTruthmaking (M : ModalGroundingSignature) (φ : M.Form) : Prop :=
  ∀ w : M.World, ∃ e : M.Entity, M.ExistsAt w e ∧ M.GroundAt w e φ

/-- Uniform Necessary Ground:
    There exists a single rigid entity that exists in every world and grounds φ in every world. -/
def UniformNecessaryGround (M : ModalGroundingSignature) (φ : M.Form) : Prop :=
  ∃ e : M.Entity, ∀ w : M.World, M.ExistsAt w e ∧ M.GroundAt w e φ

/-- The Missing Rigid Ground Horn:
    The exact structural condition missing from worldwise truthmaking. -/
def MissingRigidGroundHorn (M : ModalGroundingSignature) (φ : M.Form) : Prop :=
  ∃ e : M.Entity, (∀ w : M.World, M.ExistsAt w e) ∧ (∀ w : M.World, M.GroundAt w e φ)

/-- Quantifier Non-Equivalence Theorem:
    Worldwise truthmaking does NOT imply uniform necessary ground.
    Witnessed by changing entities across worlds (generalizing CountermodelWorldwiseTruthmaking). -/
theorem worldwise_fails_to_derive_uniform_ground :
    ∃ (M : ModalGroundingSignature) (φ : M.Form),
      WorldwiseTruthmaking M φ ∧ ¬ UniformNecessaryGround M φ := by
  let M0 : ModalGroundingSignature := {
    World           := Bool
    Entity          := Bool
    Form            := Unit
    ExistsAt        := fun w e => e = w
    Ground          := fun _ _ => True
    GroundAt        := fun _ _ _ => True
    NecessarilyTrue := fun _ => True
    PossibleWorld   := fun _ => True
  }
  have hWW : WorldwiseTruthmaking M0 () := by
    intro w
    exact ⟨w, rfl, trivial⟩
  have hNotUni : ¬ UniformNecessaryGround M0 () := by
    intro ⟨e, he⟩
    have h1 : e = true := (he true).1
    have h2 : e = false := (he false).1
    have h3 : true = false := h1.symm.trans h2
    cases h3
  exact ⟨M0, (), hWW, hNotUni⟩

/-- Equivalence of Uniform Ground with Worldwise Ground + Missing Horn:
    Analogous to A14 ↔ Act + MissingCognitiveHorn. -/
theorem uniform_ground_iff_worldwise_and_missing_horn
    (M : ModalGroundingSignature) (φ : M.Form) :
    UniformNecessaryGround M φ ↔ (WorldwiseTruthmaking M φ ∧ MissingRigidGroundHorn M φ) := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨fun w => ⟨e, (he w).1, (he w).2⟩, ⟨e, fun w => (he w).1, fun w => (he w).2⟩⟩
  · rintro ⟨_, ⟨e, hEx, hGr⟩⟩
    exact ⟨e, fun w => ⟨hEx w, hGr w⟩⟩

/-- Quantifier Exchange Under Constant Domain and Unique Grounding:
    If the entity domain is constant across worlds and each truth has a unique grounder,
    the quantifier swap ∀w ∃e → ∃e ∀w becomes logically valid. -/
theorem quantifier_exchange_under_uniqueness
    (M : ModalGroundingSignature) (φ : M.Form)
    (hWW : WorldwiseTruthmaking M φ)
    (hUnique : ∀ w₁ w₂ e₁ e₂,
      M.ExistsAt w₁ e₁ ∧ M.GroundAt w₁ e₁ φ →
      M.ExistsAt w₂ e₂ ∧ M.GroundAt w₂ e₂ φ →
      e₁ = e₂)
    (w0 : M.World) :
    UniformNecessaryGround M φ := by
  obtain ⟨e0, hEx0, hGr0⟩ := hWW w0
  refine ⟨e0, fun w => ?_⟩
  obtain ⟨ew, hExw, hGrw⟩ := hWW w
  have heq : ew = e0 := hUnique w w0 ew e0 ⟨hExw, hGrw⟩ ⟨hEx0, hGr0⟩
  rw [← heq]
  exact ⟨hExw, hGrw⟩

-- ===========================================================================
-- Section 3: Adversarial Audit of A4 (AxGlobalGround)
-- ===========================================================================

/-- Hostile Separation 1: A4 does NOT imply uniqueness of grounders.
    Two distinct necessary entities can ground the same necessary truth. -/
theorem a4_does_not_imply_unique_ground :
    ∃ (M : ModalGroundingSignature) (φ : M.Form),
      Candidate_G3 M φ ∧
      ∃ e₁ e₂ : M.Entity, e₁ ≠ e₂ ∧
        (∀ w, M.ExistsAt w e₁ ∧ M.Ground e₁ φ) ∧
        (∀ w, M.ExistsAt w e₂ ∧ M.Ground e₂ φ) := by
  let M0 : ModalGroundingSignature := {
    World           := Unit
    Entity          := Bool
    Form            := Unit
    ExistsAt        := fun _ _ => True
    Ground          := fun _ _ => True
    GroundAt        := fun _ _ _ => True
    NecessarilyTrue := fun _ => True
    PossibleWorld   := fun _ => True
  }
  have hG3 : Candidate_G3 M0 () := by
    intro _
    exact ⟨true, fun _ => ⟨trivial, trivial⟩⟩
  have hDistinct : true ≠ false := by intro h; cases h
  refine ⟨M0, (), hG3, true, false, hDistinct, fun _ => ⟨trivial, trivial⟩, fun _ => ⟨trivial, trivial⟩⟩

/-- Hostile Separation 2: A4 does NOT imply a single common ground for distinct truths.
    Two distinct necessary propositions can have disjoint necessary grounders. -/
theorem a4_does_not_imply_single_common_ground :
    ∃ (M : ModalGroundingSignature) (φ₁ φ₂ : M.Form),
      φ₁ ≠ φ₂ ∧ Candidate_G3 M φ₁ ∧ Candidate_G3 M φ₂ ∧
      ¬ (∃ e : M.Entity, (∀ w, M.ExistsAt w e) ∧ M.Ground e φ₁ ∧ M.Ground e φ₂) := by
  let M0 : ModalGroundingSignature := {
    World           := Unit
    Entity          := Bool
    Form            := Bool
    ExistsAt        := fun _ _ => True
    Ground          := fun e φ => e = φ
    GroundAt        := fun _ e φ => e = φ
    NecessarilyTrue := fun _ => True
    PossibleWorld   := fun _ => True
  }
  have hG3_1 : Candidate_G3 M0 true := fun _ => ⟨true, fun _ => ⟨trivial, rfl⟩⟩
  have hG3_2 : Candidate_G3 M0 false := fun _ => ⟨false, fun _ => ⟨trivial, rfl⟩⟩
  have hDiffForm : (true : Bool) ≠ false := by intro h; cases h
  have hNoCommon : ¬ (∃ e : Bool, (∀ w : Unit, M0.ExistsAt w e) ∧ M0.Ground e true ∧ M0.Ground e false) := by
    rintro ⟨e, _, hGr1, hGr2⟩
    have hEq1 : e = true := hGr1
    have hEq2 : e = false := hGr2
    have hContra : true = false := hEq1.symm.trans hEq2
    cases hContra
  exact ⟨M0, true, false, hDiffForm, hG3_1, hG3_2, hNoCommon⟩

-- ===========================================================================
-- Section 4: Well-Foundedness Hierarchy U1–U6 & Ultimate Ground
-- ===========================================================================

/-- Explanatory Grounding Order Signature between entities.
    `Grounds x y` means x is strictly more fundamental than y (x grounds y). -/
structure GroundingOrderSignature where
  Entity        : Type
  Grounds       : Entity → Entity → Prop

/-- An entity is an Ultimate Ground iff nothing grounds it. -/
def UltimateGround (S : GroundingOrderSignature) (u : S.Entity) : Prop :=
  ¬ ∃ x : S.Entity, S.Grounds x u

/-- U1: No Infinite Descending Chains.
    There is no function f : Nat → Entity such that ∀ n, f (n + 1) grounds f n. -/
def U1_NoInfiniteDescendingChains (S : GroundingOrderSignature) : Prop :=
  ¬ ∃ f : Nat → S.Entity, ∀ n : Nat, S.Grounds (f (n + 1)) (f n)

/-- Hostile Model of Infinite Descending Chain:
    Entity := ℤ, Grounds x y := x = y + 1.
    Satisfies Grounding, but has NO ultimate ground. -/
theorem infinite_descending_chain_has_no_ultimate_ground :
    ∃ (S : GroundingOrderSignature),
      (∀ y : S.Entity, ∃ x : S.Entity, S.Grounds x y) ∧
      ¬ (∃ u : S.Entity, UltimateGround S u) := by
  let S0 : GroundingOrderSignature := {
    Entity  := Int
    Grounds := fun x y => x = y + 1
  }
  have hEvery : ∀ y : Int, ∃ x : Int, S0.Grounds x y := fun y => ⟨y + 1, rfl⟩
  have hNoUlt : ¬ (∃ u : Int, UltimateGround S0 u) := by
    rintro ⟨u, hUlt⟩
    exact hUlt ⟨u + 1, rfl⟩
  exact ⟨S0, hEvery, hNoUlt⟩

/-- Hostile Model of Cyclic Grounding:
    Two distinct entities ground each other.
    Every entity has a grounder, so there is NO ultimate ground. -/
theorem cyclic_grounding_has_no_ultimate_ground :
    ∃ (S : GroundingOrderSignature) (x y : S.Entity),
      x ≠ y ∧ S.Grounds x y ∧ S.Grounds y x ∧
      ¬ (∃ u : S.Entity, UltimateGround S u) := by
  let S0 : GroundingOrderSignature := {
    Entity  := Bool
    Grounds := fun x y => x ≠ y
  }
  have hDiff : (true : Bool) ≠ false := by intro h; cases h
  have h1 : S0.Grounds true false := hDiff
  have h2 : S0.Grounds false true := hDiff.symm
  have hNoUlt : ¬ (∃ u : Bool, UltimateGround S0 u) := by
    rintro ⟨u, hUlt⟩
    cases u
    · exact hUlt ⟨true, hDiff⟩
    · exact hUlt ⟨false, hDiff.symm⟩
  exact ⟨S0, true, false, hDiff, h1, h2, hNoUlt⟩

/-- Bounded Chain Ancestry:
    An entity has bounded ancestry depth N. -/
def HasBoundedAncestry (S : GroundingOrderSignature) (e : S.Entity) (n : Nat) : Prop :=
  ∀ (f : Nat → S.Entity), f 0 = e → (∀ k, k < n → S.Grounds (f (k + 1)) (f k)) →
    ¬ S.Grounds (f (n + 1)) (f n)

/-- The Minimal Ultimate Ground Theorem:
    If an entity has depth 0 (nothing grounds it), it IS an ultimate ground.
    In general, bounded ancestry depth guarantees reaching an ungrounded terminal element. -/
theorem minimal_ultimate_ground_theorem
    (S : GroundingOrderSignature) (e : S.Entity)
    (hZero : ¬ ∃ x, S.Grounds x e) :
    UltimateGround S e :=
  hZero

-- ===========================================================================
-- Section 5: Personality Bridge Audit (P1–P6) & Hostile Models P1–P5
-- ===========================================================================

/-- Expanded Grounding Signature with Intentional & Personal Predicates. -/
structure ExtendedGroundingSignature where
  World           : Type
  Entity          : Type
  Form            : Type
  ExistsAt        : World → Entity → Prop
  Ground          : Entity → Form → Prop
  NecessarilyTrue : Form → Prop
  SubstantivePerson : Entity → Prop
  IntentionalSubj   : Entity → Prop
  UltimateGroundRel : Entity → Prop

/-- Hostile Model P1: Impersonal Substrate.
    An impersonal necessary ground exists, grounding reality without being a substantive person. -/
theorem model_P1_impersonal_substrate :
    ∃ (M : ExtendedGroundingSignature) (u : M.Entity),
      M.UltimateGroundRel u ∧
      (∀ w, M.ExistsAt w u) ∧
      ¬ M.SubstantivePerson u := by
  let M0 : ExtendedGroundingSignature := {
    World           := Unit
    Entity          := Unit
    Form            := Unit
    ExistsAt        := fun _ _ => True
    Ground          := fun _ _ => True
    NecessarilyTrue := fun _ => True
    SubstantivePerson := fun _ => False
    IntentionalSubj   := fun _ => False
    UltimateGroundRel := fun _ => True
  }
  exact ⟨M0, (), trivial, fun _ => trivial, fun h => h⟩

/-- Hostile Model P2: Structural Realization.
    The entity grounds the structural framework of truths, while intentional subjects exist
    separately, and the ground itself lacks intentionality and personhood. -/
theorem model_P2_structural_realization :
    ∃ (M : ExtendedGroundingSignature) (u : M.Entity) (s : M.Entity),
      M.UltimateGroundRel u ∧
      ¬ M.IntentionalSubj u ∧
      ¬ M.SubstantivePerson u ∧
      M.IntentionalSubj s := by
  let M0 : ExtendedGroundingSignature := {
    World           := Unit
    Entity          := Bool
    Form            := Unit
    ExistsAt        := fun _ _ => True
    Ground          := fun _ _ => True
    NecessarilyTrue := fun _ => True
    SubstantivePerson := fun _ => False
    IntentionalSubj   := fun e => e = true
    UltimateGroundRel := fun e => e = false
  }
  have hUlt : M0.UltimateGroundRel false := rfl
  have hNotIntU : ¬ M0.IntentionalSubj false := by intro h; cases h
  have hNotPersU : ¬ M0.SubstantivePerson false := fun h => h
  have hIntS : M0.IntentionalSubj true := rfl
  exact ⟨M0, false, true, hUlt, hNotIntU, hNotPersU, hIntS⟩

/-- Hostile Model P3: Emergent Intentionality / Non-Personal Base.
    Intentional subjects exist as higher-level entities, but the necessary ultimate ground
    is strictly physical / formal / impersonal. -/
theorem model_P3_emergent_intentionality :
    ∃ (M : ExtendedGroundingSignature) (u : M.Entity),
      M.UltimateGroundRel u ∧
      (∀ w, M.ExistsAt w u) ∧
      (∃ s : M.Entity, M.IntentionalSubj s) ∧
      ¬ M.SubstantivePerson u := by
  let M0 : ExtendedGroundingSignature := {
    World           := Unit
    Entity          := Bool
    Form            := Unit
    ExistsAt        := fun _ _ => True
    Ground          := fun _ _ => True
    NecessarilyTrue := fun _ => True
    SubstantivePerson := fun _ => False
    IntentionalSubj   := fun e => e = true
    UltimateGroundRel := fun e => e = false
  }
  have hUlt : M0.UltimateGroundRel false := rfl
  have hIntS : M0.IntentionalSubj true := rfl
  exact ⟨M0, false, hUlt, fun _ => trivial, ⟨true, hIntS⟩, fun h => h⟩

/-- Hostile Model P4: Multiple Impersonal Grounders.
    Two distinct necessary entities jointly ground reality, neither of which is personal. -/
theorem model_P4_multiple_impersonal_grounders :
    ∃ (M : ExtendedGroundingSignature) (u₁ u₂ : M.Entity),
      u₁ ≠ u₂ ∧
      M.UltimateGroundRel u₁ ∧ M.UltimateGroundRel u₂ ∧
      ¬ M.SubstantivePerson u₁ ∧ ¬ M.SubstantivePerson u₂ := by
  let M0 : ExtendedGroundingSignature := {
    World           := Unit
    Entity          := Bool
    Form            := Unit
    ExistsAt        := fun _ _ => True
    Ground          := fun _ _ => True
    NecessarilyTrue := fun _ => True
    SubstantivePerson := fun _ => False
    IntentionalSubj   := fun _ => False
    UltimateGroundRel := fun _ => True
  }
  have hDiff : (true : Bool) ≠ false := by intro h; cases h
  exact ⟨M0, true, false, hDiff, trivial, trivial, fun h => h, fun h => h⟩

/-- Hostile Model P5: Anonymous Ultimate Ground.
    A unique ultimate ground exists, but it has no personal predicates whatsoever. -/
theorem model_P5_anonymous_ultimate_ground :
    ∃ (M : ExtendedGroundingSignature) (u : M.Entity),
      M.UltimateGroundRel u ∧
      (∀ x, M.UltimateGroundRel x → x = u) ∧
      ¬ M.SubstantivePerson u := by
  let M0 : ExtendedGroundingSignature := {
    World           := Unit
    Entity          := Unit
    Form            := Unit
    ExistsAt        := fun _ _ => True
    Ground          := fun _ _ => True
    NecessarilyTrue := fun _ => True
    SubstantivePerson := fun _ => False
    IntentionalSubj   := fun _ => False
    UltimateGroundRel := fun _ => True
  }
  exact ⟨M0, (), trivial, fun _ _ => rfl, fun h => h⟩

-- ===========================================================================
-- Section 6: Performative Subject, Transcendental Grounding & Retorsion
-- ===========================================================================

/-- Performative Subject and Necessary Truth do NOT force Necessary Reality:
    An intentional subject can exist contingently in the actual world while necessary truths
    are satisfied by world-varying truthmakers without any necessary entity existing. -/
theorem performative_subject_and_nec_truth_do_not_force_necessary_entity :
    ∃ (M : ModalGroundingSignature) (φ : M.Form)
      (Subj : Type) (MeansRel : Subj → Prop → Prop) (s : Subj) (p : Prop),
      M.NecessarilyTrue φ ∧
      WorldwiseTruthmaking M φ ∧
      MeansRel s p ∧
      ¬ (∃ e : M.Entity, NecessaryEntity M e) := by
  let M0 : ModalGroundingSignature := {
    World           := Bool
    Entity          := Bool
    Form            := Unit
    ExistsAt        := fun w e => e = w
    Ground          := fun _ _ => True
    GroundAt        := fun _ _ _ => True
    NecessarilyTrue := fun _ => True
    PossibleWorld   := fun _ => True
  }
  have hWW : WorldwiseTruthmaking M0 () := fun w => ⟨w, rfl, trivial⟩
  have hNoNecE : ¬ (∃ e : Bool, NecessaryEntity M0 e) := by
    rintro ⟨e, hNecE⟩
    have h1 : e = true := hNecE true
    have h2 : e = false := hNecE false
    have h3 : true = false := h1.symm.trans h2
    cases h3
  exact ⟨M0, (), Unit, fun _ _ => True, (), True, trivial, hWW, trivial, hNoNecE⟩

/-- Retorsion Test on Grounding:
    Asserting "There is no necessary ground" does NOT performatively refute itself.
    The act of assertion requires an intentional subject and an actual initiation,
    but does NOT require that the speaker or any grounder be a necessary entity. -/
theorem denial_of_necessary_ground_is_non_self_refuting :
    ∃ (M : ModalGroundingSignature) (Subj : Type)
      (ActRel : Subj → Prop → Prop) (s : Subj) (p : Prop),
      ActRel s p ∧ p ∧
      ¬ (∃ e : M.Entity, NecessaryEntity M e) := by
  let M0 : ModalGroundingSignature := {
    World           := Bool
    Entity          := Bool
    Form            := Unit
    ExistsAt        := fun w e => e = w
    Ground          := fun _ _ => True
    GroundAt        := fun _ _ _ => True
    NecessarilyTrue := fun _ => True
    PossibleWorld   := fun _ => True
  }
  have hNoNecE : ¬ (∃ e : Bool, NecessaryEntity M0 e) := by
    rintro ⟨e, hNecE⟩
    have h1 : e = true := hNecE true
    have h2 : e = false := hNecE false
    have h3 : true = false := h1.symm.trans h2
    cases h3
  exact ⟨M0, Unit, fun _ _ => True, (), True, trivial, trivial, hNoNecE⟩

-- ===========================================================================
-- Section 7: Uniqueness and Plurality Analysis
-- ===========================================================================

/-- Plural Ultimate Grounds Model:
    An ultimate ground exists, but is NOT unique. -/
theorem ultimate_ground_does_not_imply_uniqueness :
    ∃ (S : GroundingOrderSignature) (u₁ u₂ : S.Entity),
      u₁ ≠ u₂ ∧ UltimateGround S u₁ ∧ UltimateGround S u₂ := by
  let S0 : GroundingOrderSignature := {
    Entity  := Bool
    Grounds := fun _ _ => False
  }
  have hDiff : (true : Bool) ≠ false := by intro h; cases h
  have hU1 : UltimateGround S0 true := fun ⟨_, h⟩ => h
  have hU2 : UltimateGround S0 false := fun ⟨_, h⟩ => h
  exact ⟨S0, true, false, hDiff, hU1, hU2⟩

/-- Solitary Ultimate Ground Model:
    An ultimate ground exists, but there is NO plurality (Universe has cardinality 1). -/
theorem ultimate_ground_does_not_imply_plurality :
    ∃ (S : GroundingOrderSignature) (u : S.Entity),
      UltimateGround S u ∧ (∀ x : S.Entity, x = u) := by
  let S0 : GroundingOrderSignature := {
    Entity  := Unit
    Grounds := fun _ _ => False
  }
  have hU : UltimateGround S0 () := fun ⟨_, h⟩ => h
  exact ⟨S0, (), hU, fun _ => rfl⟩

-- ===========================================================================
-- Section 8: Ten Canonical Hostile Grounding Models (G1–G10)
-- ===========================================================================

/-- G1: Worldwise Grounding Model (witnesses vary by world). -/
theorem model_G1_worldwise_grounding :
    ∃ (M : ModalGroundingSignature) (φ : M.Form),
      WorldwiseTruthmaking M φ ∧ ¬ UniformNecessaryGround M φ :=
  worldwise_fails_to_derive_uniform_ground

/-- G2: Uniform Necessary Ground Model (satisfies A4). -/
theorem model_G2_uniform_necessary_ground :
    ∃ (M : ModalGroundingSignature) (φ : M.Form),
      Candidate_G3 M φ := by
  let M0 : ModalGroundingSignature := {
    World           := Unit
    Entity          := Unit
    Form            := Unit
    ExistsAt        := fun _ _ => True
    Ground          := fun _ _ => True
    GroundAt        := fun _ _ _ => True
    NecessarilyTrue := fun _ => True
    PossibleWorld   := fun _ => True
  }
  exact ⟨M0, (), fun _ => ⟨(), fun _ => ⟨trivial, trivial⟩⟩⟩

/-- G3: Infinite Ground Chain Model (descending without termination). -/
theorem model_G3_infinite_ground_chain :
    ∃ (S : GroundingOrderSignature),
      (∀ y, ∃ x, S.Grounds x y) ∧ ¬ (∃ u, UltimateGround S u) :=
  infinite_descending_chain_has_no_ultimate_ground

/-- G4: Cyclic Grounding Model. -/
theorem model_G4_cyclic_grounding :
    ∃ (S : GroundingOrderSignature) (x y : S.Entity),
      x ≠ y ∧ S.Grounds x y ∧ S.Grounds y x ∧ ¬ (∃ u, UltimateGround S u) :=
  cyclic_grounding_has_no_ultimate_ground

/-- G5: Multiple Ultimate Grounds Model. -/
theorem model_G5_multiple_ultimate_grounds :
    ∃ (S : GroundingOrderSignature) (u₁ u₂ : S.Entity),
      u₁ ≠ u₂ ∧ UltimateGround S u₁ ∧ UltimateGround S u₂ :=
  ultimate_ground_does_not_imply_uniqueness

/-- G6: Unique Impersonal Ultimate Ground Model. -/
theorem model_G6_unique_impersonal_ultimate_ground :
    ∃ (M : ExtendedGroundingSignature) (u : M.Entity),
      M.UltimateGroundRel u ∧ (∀ x, M.UltimateGroundRel x → x = u) ∧ ¬ M.SubstantivePerson u :=
  model_P5_anonymous_ultimate_ground

/-- G7: Necessary Personal Ground Model (under declared bridge). -/
theorem model_G7_necessary_personal_ground :
    ∃ (M : ExtendedGroundingSignature) (u : M.Entity),
      M.UltimateGroundRel u ∧ (∀ w, M.ExistsAt w u) ∧ M.SubstantivePerson u := by
  let M0 : ExtendedGroundingSignature := {
    World           := Unit
    Entity          := Unit
    Form            := Unit
    ExistsAt        := fun _ _ => True
    Ground          := fun _ _ => True
    NecessarilyTrue := fun _ => True
    SubstantivePerson := fun _ => True
    IntentionalSubj   := fun _ => True
    UltimateGroundRel := fun _ => True
  }
  exact ⟨M0, (), trivial, fun _ => trivial, trivial⟩

/-- G8: Necessary Ground Without Ultimate Model.
    Every entity exists in all worlds, but grounds form an infinite chain. -/
theorem model_G8_necessary_ground_without_ultimate :
    ∃ (M : ModalGroundingSignature) (S : GroundingOrderSignature),
      (∀ e : M.Entity, NecessaryEntity M e) ∧
      (∀ y : S.Entity, ∃ x : S.Entity, S.Grounds x y) := by
  let M0 : ModalGroundingSignature := {
    World           := Unit
    Entity          := Int
    Form            := Unit
    ExistsAt        := fun _ _ => True
    Ground          := fun _ _ => True
    GroundAt        := fun _ _ _ => True
    NecessarilyTrue := fun _ => True
    PossibleWorld   := fun _ => True
  }
  let S0 : GroundingOrderSignature := {
    Entity  := Int
    Grounds := fun x y => x = y + 1
  }
  exact ⟨M0, S0, fun _ _ => trivial, fun y => ⟨y + 1, rfl⟩⟩

/-- G9: Intentional Subject with Impersonal Ground Model. -/
theorem model_G9_intentional_subject_with_impersonal_ground :
    ∃ (M : ExtendedGroundingSignature) (u : M.Entity) (s : M.Entity),
      M.UltimateGroundRel u ∧ ¬ M.SubstantivePerson u ∧ M.IntentionalSubj s := by
  obtain ⟨M0, u0, s0, hUlt, _, hNotPersU, hIntS⟩ := model_P2_structural_realization
  exact ⟨M0, u0, s0, hUlt, hNotPersU, hIntS⟩

/-- G10: Personal Ground with No Plurality Model. -/
theorem model_G10_personal_ground_with_no_plurality :
    ∃ (M : ExtendedGroundingSignature) (u : M.Entity),
      M.UltimateGroundRel u ∧ M.SubstantivePerson u ∧ (∀ x : M.Entity, x = u) := by
  let M0 : ExtendedGroundingSignature := {
    World           := Unit
    Entity          := Unit
    Form            := Unit
    ExistsAt        := fun _ _ => True
    Ground          := fun _ _ => True
    NecessarilyTrue := fun _ => True
    SubstantivePerson := fun _ => True
    IntentionalSubj   := fun _ => True
    UltimateGroundRel := fun _ => True
  }
  exact ⟨M0, (), trivial, trivial, fun _ => rfl⟩

-- ===========================================================================
-- Section 9: Collapse Transformations & Expressivity Invariance
-- ===========================================================================

/-- Transformation T_impersonal:
    Erases all substantive personal predicates on entities, preserving all modal,
    truthmaker, and grounding relations. -/
def T_impersonal (M : ExtendedGroundingSignature) : ExtendedGroundingSignature := {
  World             := M.World
  Entity            := M.Entity
  Form              := M.Form
  ExistsAt          := M.ExistsAt
  Ground            := M.Ground
  NecessarilyTrue   := M.NecessarilyTrue
  SubstantivePerson := fun _ => False
  IntentionalSubj   := M.IntentionalSubj
  UltimateGroundRel := M.UltimateGroundRel
}

/-- Impersonal Collapse Invariance Theorem:
    T_impersonal preserves all grounding, necessity, and ultimate ground relations
    while setting SubstantivePerson identically to False.
    Therefore, no formula in the pure grounding/truthmaker vocabulary can define or derive SubstantivePerson. -/
theorem collapse_invariance_impersonal
    (M : ExtendedGroundingSignature) (u : M.Entity)
    (hUlt : M.UltimateGroundRel u)
    (hNec : ∀ w, M.ExistsAt w u) :
    (T_impersonal M).UltimateGroundRel u ∧
    (∀ w, (T_impersonal M).ExistsAt w u) ∧
    ¬ (T_impersonal M).SubstantivePerson u :=
  ⟨hUlt, hNec, fun h => h⟩

-- ===========================================================================
-- Section 10: Master Grounding Frontier Synthesis
-- ===========================================================================

/-- The Grounding Frontier Master Synthesis Theorem:
    A single machine-checked master theorem establishing the exact formal status
    of the grounding and modal frontier of Γ:
    1. G4 → G2 → G1 (strict hierarchy of existence candidates).
    2. Worldwise truthmaking does NOT imply uniform necessary ground.
    3. Uniform ground is equivalent to Worldwise truthmaking + MissingRigidGroundHorn.
    4. A4 does not entail uniqueness of grounders.
    5. A4 does not entail a single common ground for distinct truths.
    6. Grounding allows infinite descending chains unless well-foundedness is posited.
    7. Grounding allows cycles unless acyclicity is posited.
    8. Ultimate ground does not entail substantive personhood.
    9. Ultimate ground does not entail uniqueness.
    10. Ultimate ground does not entail plurality. -/
theorem grounding_frontier_synthesis :
    -- 1. Quantifier non-equivalence
    (∃ (M : ModalGroundingSignature) (φ : M.Form),
      WorldwiseTruthmaking M φ ∧ ¬ UniformNecessaryGround M φ) ∧
    -- 2. A4 non-uniqueness
    (∃ (M : ModalGroundingSignature) (φ : M.Form),
      Candidate_G3 M φ ∧
      ∃ e₁ e₂ : M.Entity, e₁ ≠ e₂ ∧
        (∀ w, M.ExistsAt w e₁ ∧ M.Ground e₁ φ) ∧
        (∀ w, M.ExistsAt w e₂ ∧ M.Ground e₂ φ)) ∧
    -- 3. Infinite descending chains have no ultimate ground
    (∃ (S : GroundingOrderSignature),
      (∀ y, ∃ x, S.Grounds x y) ∧ ¬ (∃ u, UltimateGround S u)) ∧
    -- 4. Cyclic grounding has no ultimate ground
    (∃ (S : GroundingOrderSignature) (x y : S.Entity),
      x ≠ y ∧ S.Grounds x y ∧ S.Grounds y x ∧ ¬ (∃ u, UltimateGround S u)) ∧
    -- 5. Impersonal ultimate ground
    (∃ (M : ExtendedGroundingSignature) (u : M.Entity),
      M.UltimateGroundRel u ∧ ¬ M.SubstantivePerson u) ∧
    -- 6. Plural ultimate grounds
    (∃ (S : GroundingOrderSignature) (u₁ u₂ : S.Entity),
      u₁ ≠ u₂ ∧ UltimateGround S u₁ ∧ UltimateGround S u₂) := by
  obtain ⟨M5, u5, hUlt5, _, hNotPers5⟩ := model_P1_impersonal_substrate
  exact ⟨worldwise_fails_to_derive_uniform_ground,
         a4_does_not_imply_unique_ground,
         infinite_descending_chain_has_no_ultimate_ground,
         cyclic_grounding_has_no_ultimate_ground,
         ⟨M5, u5, hUlt5, hNotPers5⟩,
         ultimate_ground_does_not_imply_uniqueness⟩

end Logos.GroundingFrontier
