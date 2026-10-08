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

import Logos.Core
import Logos.Necessity
import Logos.Semantics
import Logos.Entity
import Logos.Modal
import Logos.Agency
import Logos.Person
import Logos.Choice
import Logos.TheologicalModalHardening
import Logos.ModalCreationAgency

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
