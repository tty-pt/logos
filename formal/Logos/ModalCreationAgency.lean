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

import Logos.Core
import Logos.Necessity
import Logos.Semantics
import Logos.Entity
import Logos.Modal
import Logos.Agency
import Logos.Person
import Logos.Choice
import Logos.TheologicalModalHardening

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
