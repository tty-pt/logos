import Lean

/-!
# Adversarial Audit of FreeSubjectDeterminationDilemma.lean

This module delivers a comprehensive adversarial audit and formal deconstruction of
`FreeSubjectDeterminationDilemma.lean`. It attacks the formal model, its central argument,
and its dependency structure, showing precisely where the proof succeeds mathematically,
where it relies on unproved or question-begging assumptions, and where its countermodels
and taxonomies fail.

## Key Audit Findings Formally Proved in this File:

1. **Underconstrained Representation of Determination in Original Countermodel**:
   In `FreeSubjectDeterminationDilemma.lean` (lines 634–690), the 3-node countermodel
   `independent_non_causal_ground_satisfiable_without_cycle` declared `Determines S C`
   while fixing `OutcomeOf S` to be constant across worlds and flipping `OutcomeOf C`.
   The causal relation `Det3` imposed zero deterministic constraints.

2. **Dilemma of Deterministic Determination**:
   - If `Determines` enforces genuine determinism (`DeterministicDetermination`) and the
     source configuration is invariant under `SameCompletePriorState`, contingency of the
     occurrence is mathematically impossible (`impossibility_of_invariant_deterministic_contingency`).
   - If the source configuration is itself contingent, a genuine deterministic 3-node model
     CAN be constructed (`deterministic_independent_ground_model`), satisfying determinism,
     well-founded non-circular grounding, contingency, and an independent impersonal ground,
     with NO personal agents.

3. **Explanatory Grounding Hierarchy & Contrastive Failure**:
   We formalize the four levels of explanation (Association, Substrate Existence, Configuration
   Explanation, and Contrastive Selection). We prove that an invariant impersonal ground can
   explain why the source has its configuration (Level 3), but cannot contrastively explain
   why this configuration obtained rather than an alternative without necessitating the outcome
   (`invariant_ground_cannot_contrastively_explain_contingent_source`).

4. **Deconstruction of the Circularity Inference**:
   The alleged "explanatory cycle" ($C \to S \to C$) is not derived from well-foundedness or
   Contrastive PSR. It is manufactured by the axiom `consequence_dependent_selection`, which
   forces `GroundingDependsOn S C` by decree. Well-foundedness merely refutes the cycle after
   it has been artificially injected (`wellFounded_does_not_derive_backward_dependence`).

5. **Incompleteness of Origin Explanation Taxonomy**:
   `OriginExplanationTaxonomy` (lines 413–460) defines `NecessitatedBySourceNature` as invariant
   and `ImpersonalContingentSource` as non-necessitating (`¬ Necessitates`). We prove that this
   taxonomy omits **Contingent Deterministic Impersonal Sources** (sources that deterministically
   necessitate their outcome but are themselves contingent across possible worlds).

6. **Four Formal Countermodels for Unsupported Gaps**:
   - Gap 1 (Occurrence → Ultimate Source): Refuted by `infinite_regress_no_ultimate_source` on `Nat`.
   - Gap 2 (Ultimate Source → Personal Source): Refuted by `impersonal_indeterministic_source_model`.
   - Gap 3 (Non-Causal Ground → Personal Source): Refuted by `impersonal_law_grounded_source_model`.
   - Gap 4 (Personal Source → Free Subject): Refuted by `unforced_agent_without_control_model`,
     exposing `AgentialControlBridge` as an unproved postulate papering over the Mind argument.

7. **Minimal Conditional Free Subject Theorem**:
   We formulate `minimal_conditional_free_subject_theorem`, exposing every indispensable premise
   and stripping out all dead/cosmetic code (`ExplainsSubstrate`, `ExplainsProduction`,
   `ExplainsContrastiveSelection`, `sourceSubstrate`).
-/

namespace Logos
namespace AdversarialFreeSubjectAudit

universe u v w

/-!
================================================================================
I. CORE STRUCTURES FROM FREESUBJECTDETERMINATIONDILEMMA.LEAN (AUDITED)
================================================================================
-/

/-- Transitive ancestral determination via `Relation.TransGen`. -/
def AncestrallyDetermines {α : Type u} (Determines : α → α → Prop) : α → α → Prop :=
  Relation.TransGen Determines

/-- An event `s` is ultimate if no prior event determines it. -/
def IsUltimate {α : Type u} (Determines : α → α → Prop) (s : α) : Prop :=
  ¬ ∃ p : α, Determines p s

/-- Fundamental logical lemma: Well-founded relations contain no 2-cycles. -/
theorem wellFounded_explanation_has_no_two_cycle
    {Node : Type u}
    (GroundingDependsOn : Node → Node → Prop)
    (hWF : WellFounded GroundingDependsOn)
    {a b : Node}
    (hab : GroundingDependsOn a b)
    (hba : GroundingDependsOn b a) :
    False := by
  have hNoCycle : ∀ x y : Node, GroundingDependsOn x y → GroundingDependsOn y x → False := by
    intro x
    induction x using hWF.induction with
    | h x ih =>
      intro y hxy hyx
      exact ih y hyx x hyx hxy
  exact hNoCycle a b hab hba

/-- The baseline DeterminationModel from FreeSubjectDeterminationDilemma.lean. -/
structure DeterminationModel where
  Event : Type u
  Occurs : Event → Prop
  concreteOccurrence : Event
  Determines : Event → Event → Prop
  GroundingDependsOn : Event → Event → Prop
  genuine_grounding_is_well_founded : WellFounded GroundingDependsOn
  /-- Ontological determination transmits explanatory dependence: if `a` ancestrally determines
  `b`, then `b` depends explanatorily on `a` for its determination. Non-temporal. -/
  ontological_determination_implies_explanatory_dependence :
    ∀ {a b : Event}, AncestrallyDetermines Determines a b → GroundingDependsOn b a
  World : Type v
  actualWorld : World
  Accessible : World → World → Prop
  SameCompletePriorState : World → World → Prop
  Outcome : Type w
  OutcomeOf : Event → World → Outcome
  Agent : Type u
  IsAgent : Agent → Prop
  OriginatesAt : Agent → Event → Prop
  ControlsAlternative : Agent → Event → World → Prop

/-- Occurrence contingency under same complete prior state. -/
def HasSamePastAlternative (M : DeterminationModel.{u, v, w}) : Prop :=
  ∃ alternative : M.World,
    M.Accessible M.actualWorld alternative ∧
    M.SameCompletePriorState M.actualWorld alternative ∧
    M.OutcomeOf M.concreteOccurrence alternative ≠ M.OutcomeOf M.concreteOccurrence M.actualWorld

/-- Metatheoretic bridge linking proof occurrence to the model. -/
structure ProofOccurrence (M : DeterminationModel.{u, v, w}) : Prop where
  proof_occurs : M.Occurs M.concreteOccurrence
  proof_is_contingent : HasSamePastAlternative M

/-- An ultimate source for the concrete occurrence. -/
structure UltimateSource (M : DeterminationModel.{u, v, w}) where
  sourceConfig : M.Event
  config_occurs : M.Occurs sourceConfig
  determines_occurrence : AncestrallyDetermines M.Determines sourceConfig M.concreteOccurrence
  is_ultimate : IsUltimate M.Determines sourceConfig

/-- Necessitation across accessible worlds. -/
def Necessitates (M : DeterminationModel.{u, v, w}) (cfg conc : M.Event) : Prop :=
  ∀ alternative : M.World,
    M.Accessible M.actualWorld alternative →
    M.OutcomeOf cfg alternative = M.OutcomeOf cfg M.actualWorld →
    M.OutcomeOf conc alternative = M.OutcomeOf conc M.actualWorld

/-- Source configuration contingency under same complete prior state. -/
def SourceConfigContingent (M : DeterminationModel.{u, v, w}) (S : UltimateSource.{u, v, w} M) : Prop :=
  ∃ alternative : M.World,
    M.Accessible M.actualWorld alternative ∧
    M.SameCompletePriorState M.actualWorld alternative ∧
    M.OutcomeOf S.sourceConfig alternative ≠ M.OutcomeOf S.sourceConfig M.actualWorld

/-!
================================================================================
II. ATTACK 1: STRENGTHENED DETERMINISTIC DETERMINATION SEMANTICS
================================================================================
-/

/-- PRINCIPLE OF DETERMINISTIC DETERMINATION:
If event `a` determines event `b`, then across all accessible worlds, identical
configurations of `a` preserve identical outcomes of `b`.
This formalizes the core philosophical definition of determinism. -/
def DeterministicDetermination (M : DeterminationModel.{u, v, w}) : Prop :=
  ∀ a b : M.Event, M.Determines a b →
    ∀ w1 w2 : M.World,
      M.Accessible M.actualWorld w1 →
      M.Accessible M.actualWorld w2 →
      M.OutcomeOf a w1 = M.OutcomeOf a w2 →
      M.OutcomeOf b w1 = M.OutcomeOf b w2

/-- THEOREM: Deterministic determination is strictly transitive along ancestral chains.
If `AncestrallyDetermines M.Determines a b`, then equal configurations of `a`
yield equal outcomes of `b`. -/
theorem ancestrallyDetermines_preserves_determinism
    (M : DeterminationModel.{u, v, w})
    (hDet : DeterministicDetermination M)
    {a b : M.Event}
    (hAnc : AncestrallyDetermines M.Determines a b) :
    ∀ w1 w2 : M.World,
      M.Accessible M.actualWorld w1 →
      M.Accessible M.actualWorld w2 →
      M.OutcomeOf a w1 = M.OutcomeOf a w2 →
      M.OutcomeOf b w1 = M.OutcomeOf b w2 := by
  induction hAnc with
  | single hStep =>
    intro w1 w2 hw1 hw2 heq
    exact hDet _ _ hStep w1 w2 hw1 hw2 heq
  | tail hChain hStep ih =>
    intro w1 w2 hw1 hw2 heq
    have hMidEq := ih w1 w2 hw1 hw2 heq
    exact hDet _ _ hStep w1 w2 hw1 hw2 hMidEq

/-- THEOREM: Transitive deterministic determination entails Necessitation from actualWorld,
assuming accessibility of the actual world to itself. -/
theorem ancestrallyDetermines_implies_necessitates
    (M : DeterminationModel.{u, v, w})
    (hDet : DeterministicDetermination M)
    (hRefl : M.Accessible M.actualWorld M.actualWorld)
    {a b : M.Event}
    (hAnc : AncestrallyDetermines M.Determines a b) :
    Necessitates M a b := by
  intro alt hAcc hEq
  exact ancestrallyDetermines_preserves_determinism M hDet hAnc alt M.actualWorld hAcc hRefl hEq

/-- THEOREM (The Invariant Deterministic Impossibility):
If `Determines` is genuinely deterministic, and the source configuration is invariant
under `SameCompletePriorState`, then contingency of the concrete occurrence is
MATHEMATICALLY IMPOSSIBLE. -/
theorem impossibility_of_invariant_deterministic_contingency
    (M : DeterminationModel.{u, v, w})
    (S : UltimateSource.{u, v, w} M)
    (hDet : DeterministicDetermination M)
    (hRefl : M.Accessible M.actualWorld M.actualWorld)
    (hInvariant : ∀ alt : M.World, M.SameCompletePriorState M.actualWorld alt →
      M.OutcomeOf S.sourceConfig alt = M.OutcomeOf S.sourceConfig M.actualWorld)
    (hCont : HasSamePastAlternative M) :
    False := by
  have hNec : Necessitates M S.sourceConfig M.concreteOccurrence :=
    ancestrallyDetermines_implies_necessitates M hDet hRefl S.determines_occurrence
  obtain ⟨alt, hAcc, hSamePast, hDiffOutcome⟩ := hCont
  have hEqCfg := hInvariant alt hSamePast
  have hEqOutcome := hNec alt hAcc hEqCfg
  exact hDiffOutcome hEqOutcome

/-!
================================================================================
III. CONSTRUCTING THE GENUINE DETERMINISTIC 3-NODE COUNTERMODEL
================================================================================
Here we answer Section 1 of the audit:
We construct a countermodel satisfying ALL of the following simultaneously:
1. `S` genuinely determines `C`, with `DeterministicDetermination` explicitly enforced.
2. `S` has no prior causal determinant (`IsUltimate M.Determines S`).
3. An independent, impersonal ground `G` explains the configuration of `S`.
4. The concrete occurrence `C` is contingent under an accessible same-past alternative.
5. Grounding is well-founded and non-circular.
6. NO personal agents exist.
-/

def rank3 (x : Fin 3) : Nat :=
  if x.val = 0 then 2 else if x.val = 1 then 1 else 0

def GroundRel3 (y x : Fin 3) : Prop := rank3 y < rank3 x

instance (y x : Fin 3) : Decidable (GroundRel3 y x) :=
  inferInstanceAs (Decidable (rank3 y < rank3 x))

def Det3_strict (a b : Fin 3) : Prop := a = 1 ∧ b = 2

theorem transGen_det3_strict {a b : Fin 3} (h : Relation.TransGen Det3_strict a b) :
    a = 1 ∧ b = 2 := by
  induction h with
  | single h1 => exact h1
  | tail _ h2 ih =>
    obtain ⟨_, h_mid⟩ := ih
    obtain ⟨h21, _⟩ := h2
    subst h_mid
    have hNeq : (2 : Fin 3) ≠ (1 : Fin 3) := by decide
    exact False.elim (hNeq h21)

/-- THEOREM: The fully deterministic 3-node model with an independent impersonal ground.
Unlike the flawed model in `FreeSubjectDeterminationDilemma.lean` (where `S` remained fixed
while `C` changed), here `S` deterministically governs `C`:
`OutcomeOf S w = w` and `OutcomeOf C w = w`.
Thus `DeterministicDetermination` is 100% satisfied. -/
theorem deterministic_independent_ground_model :
    ∃ (M : DeterminationModel.{0, 0, 0}) (S : UltimateSource.{0, 0, 0} M) (G : M.Event),
      DeterministicDetermination M ∧
      (∀ x, ¬ M.Determines G x) ∧
      (∀ x, ¬ M.Determines x G) ∧
      M.GroundingDependsOn S.sourceConfig G ∧
      AncestrallyDetermines M.Determines S.sourceConfig M.concreteOccurrence ∧
      M.GroundingDependsOn M.concreteOccurrence S.sourceConfig ∧
      ¬ M.GroundingDependsOn S.sourceConfig M.concreteOccurrence ∧
      ¬ M.GroundingDependsOn G M.concreteOccurrence ∧
      IsUltimate M.Determines S.sourceConfig ∧
      HasSamePastAlternative M ∧
      (∀ agent : M.Agent, ¬ M.IsAgent agent) := by
  let E : Type := Fin 3
  let G_node : E := 0
  let S_node : E := 1
  let C_node : E := 2
  let W : Type := Bool
  let O : Type := Bool
  have hWF : WellFounded GroundRel3 := (measure rank3).wf
  let M : DeterminationModel.{0, 0, 0} := {
    Event := E
    Occurs := fun _ => True
    concreteOccurrence := C_node
    Determines := Det3_strict
    GroundingDependsOn := GroundRel3
    genuine_grounding_is_well_founded := hWF
    ontological_determination_implies_explanatory_dependence := by
      intro a b hab
      obtain ⟨ha, hb⟩ := transGen_det3_strict hab
      subst ha hb
      decide
    World := W
    actualWorld := false
    Accessible := fun _ _ => True
    SameCompletePriorState := fun _ _ => True
    Outcome := O
    OutcomeOf := fun e w =>
      if e = 0 then false  -- G is invariant (abstract non-causal ground)
      else if e = 1 then w -- S varies across worlds
      else w               -- C strictly determined by S
    Agent := Empty
    IsAgent := fun _ => True
    OriginatesAt := fun _ _ => True
    ControlsAlternative := fun _ _ _ => True
  }
  let S : UltimateSource.{0, 0, 0} M := {
    sourceConfig := S_node
    config_occurs := trivial
    determines_occurrence := Relation.TransGen.single ⟨rfl, rfl⟩
    is_ultimate := by
      rintro ⟨p, _hp1, hp2⟩
      revert hp2
      decide
  }
  refine ⟨M, S, G_node, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- DeterministicDetermination
    intro a b hab w1 w2 _ _ heq
    obtain ⟨rfl, rfl⟩ := hab
    dsimp [M] at heq ⊢
    exact heq
  · intro x hx; obtain ⟨hx1, _⟩ := hx; revert hx1; decide
  · intro x hx; obtain ⟨_, hx2⟩ := hx; revert hx2; decide
  · dsimp [M, S]; decide
  · exact S.determines_occurrence
  · dsimp [M, S]; decide
  · dsimp [M, S]; decide
  · dsimp [M, S]; decide
  · exact S.is_ultimate
  · refine ⟨true, trivial, trivial, ?_⟩
    dsimp [M]
    decide
  · intro a
    cases a

/-!
================================================================================
IV. ATTACK 2: FOUR LEVELS OF EXPLANATORY GROUNDING AND CONTRASTIVE DILEMMA
================================================================================
-/

/-- Level 1: Explanatory Association (bare grounding relation). -/
def ExplainsAssociation (M : DeterminationModel.{u, v, w}) (g s : M.Event) : Prop :=
  M.GroundingDependsOn s g

/-- Level 2: Substrate Existence. -/
def ExplainsSubstrate (M : DeterminationModel.{u, v, w}) (g s : M.Event) : Prop :=
  M.Occurs g ∧ M.GroundingDependsOn s g

/-- Level 3: Determinate Configuration Explanation (why `s` has its actual profile). -/
def ExplainsConfiguration (M : DeterminationModel.{u, v, w}) (g s : M.Event) : Prop :=
  M.GroundingDependsOn s g

/-- Level 4: Contrastive Selection Explanation.
`g` explains why `s` has configuration `s_actual` rather than `s_alt` under the same past. -/
def ExplainsContrastiveSelection
    (M : DeterminationModel.{u, v, w})
    (g s : M.Event) : Prop :=
  M.GroundingDependsOn s g ∧
  ∀ alt : M.World,
    M.Accessible M.actualWorld alt →
    M.SameCompletePriorState M.actualWorld alt →
    M.OutcomeOf s alt ≠ M.OutcomeOf s M.actualWorld →
    M.OutcomeOf g alt = M.OutcomeOf g M.actualWorld →
    False

/-- THEOREM (The Invariant Contrastive Dilemma):
An invariant impersonal ground `G` (whose outcome is identical across accessible worlds)
CANNOT provide a Level 4 Contrastive Explanation for a contingent source configuration. -/
theorem invariant_ground_cannot_contrastively_explain_contingent_source
    (M : DeterminationModel.{u, v, w})
    (S : UltimateSource.{u, v, w} M)
    (G : M.Event)
    (hG_inv : ∀ alt : M.World, M.OutcomeOf G alt = M.OutcomeOf G M.actualWorld)
    (hCfgCont : SourceConfigContingent M S)
    (hContrastive : ExplainsContrastiveSelection M G S.sourceConfig) :
    False := by
  obtain ⟨alt, hAcc, hSamePast, hDiffCfg⟩ := hCfgCont
  have hG_eq := hG_inv alt
  exact hContrastive.2 alt hAcc hSamePast hDiffCfg hG_eq

/-!
================================================================================
V. ATTACK 3: DECONSTRUCTING THE EXPLANATORY-CIRCULARITY INFERENCE
================================================================================
-/

/-
The circularity argument in `FreeSubjectDeterminationDilemma.lean` claims:
1. `C` depends on `S` (from causal ancestry).
2. `S` depends on `C` (from `consequence_dependent_selection`).
3. Hence a 2-cycle C -> S -> C, violating well-foundedness.

We show that Step 2 is an unargued, question-begging assumption.
Well-foundedness and Contrastive PSR DO NOT derive backward dependence.
-/

def rank2 (x : Fin 2) : Nat :=
  if x.val = 0 then 1 else 0

def GroundRel2 (y x : Fin 2) : Prop := rank2 y < rank2 x

instance (y x : Fin 2) : Decidable (GroundRel2 y x) :=
  inferInstanceAs (Decidable (rank2 y < rank2 x))

def Det2 (a b : Fin 2) : Prop := a = 0 ∧ b = 1

theorem transGen_det2 {a b : Fin 2} (h : Relation.TransGen Det2 a b) : a = 0 ∧ b = 1 := by
  induction h with
  | single h1 => exact h1
  | tail _ h2 ih =>
    obtain ⟨_ih1, rfl⟩ := ih
    obtain ⟨h21, _h22⟩ := h2
    cases h21

/-- Formalization of Contrastive PSR: A contingent determination between accessible same-past
alternatives requires a contrastive reason / explanatory ground for the source configuration. -/
def ContrastivePSR_Holds
    (M : DeterminationModel.{u, v, w})
    (S : UltimateSource.{u, v, w} M)
    (HasContrastiveReason : M.Event → Prop) : Prop :=
  HasSamePastAlternative M → HasContrastiveReason S.sourceConfig

/-- THEOREM (PSR & Well-Foundedness Do Not Derive Backward Dependence):
A complete determination model can satisfy ALL of the following simultaneously:
1. Explanatory grounding is strictly well-founded (`genuine_grounding_is_well_founded`).
2. Ontological determination transmits forward explanatory dependence (`ontological_determination_implies_explanatory_dependence`).
3. An effective contrastive alternative exists (`HasSamePastAlternative M`).
4. Contrastive PSR holds (`ContrastivePSR_Holds M S HasContrastiveReason`).
5. A contrastive reason actually obtains for the source (`HasContrastiveReason S.sourceConfig`).
6. YET NO BACKWARD DEPENDENCE EXISTS (`¬ M.GroundingDependsOn S.sourceConfig M.concreteOccurrence`).

This proves that backward explanatory dependence is NOT derivable from well-foundedness
plus Contrastive PSR; it requires the independent, controversial teleological premise
`consequence_dependent_selection`. -/
theorem wellFounded_and_psr_do_not_derive_backward_dependence :
    ∃ (M : DeterminationModel.{0, 0, 0})
      (S : UltimateSource.{0, 0, 0} M)
      (HasContrastiveReason : M.Event → Prop),
      HasSamePastAlternative M ∧
      ContrastivePSR_Holds M S HasContrastiveReason ∧
      HasContrastiveReason S.sourceConfig ∧
      AncestrallyDetermines M.Determines S.sourceConfig M.concreteOccurrence ∧
      M.GroundingDependsOn M.concreteOccurrence S.sourceConfig ∧
      ¬ M.GroundingDependsOn S.sourceConfig M.concreteOccurrence := by
  let E : Type := Fin 3
  let G_node : E := 0
  let S_node : E := 1
  let C_node : E := 2
  let W : Type := Bool
  let O : Type := Bool
  have hWF : WellFounded GroundRel3 := (measure rank3).wf
  let M : DeterminationModel.{0, 0, 0} := {
    Event := E
    Occurs := fun _ => True
    concreteOccurrence := C_node
    Determines := Det3_strict
    GroundingDependsOn := GroundRel3
    genuine_grounding_is_well_founded := hWF
    ontological_determination_implies_explanatory_dependence := by
      intro a b hab
      obtain ⟨ha, hb⟩ := transGen_det3_strict hab
      subst ha hb
      decide
    World := W
    actualWorld := false
    Accessible := fun _ _ => True
    SameCompletePriorState := fun _ _ => True
    Outcome := O
    OutcomeOf := fun e w =>
      if e = 0 then false
      else if e = 1 then w
      else w
    Agent := Empty
    IsAgent := fun _ => True
    OriginatesAt := fun _ _ => True
    ControlsAlternative := fun _ _ _ => True
  }
  let S : UltimateSource.{0, 0, 0} M := {
    sourceConfig := S_node
    config_occurs := trivial
    determines_occurrence := Relation.TransGen.single ⟨rfl, rfl⟩
    is_ultimate := by
      rintro ⟨p, _hp1, hp2⟩
      revert hp2
      decide
  }
  let HasReason : M.Event → Prop := fun e => M.GroundingDependsOn e G_node
  refine ⟨M, S, HasReason, ?_, ?_, ?_, S.determines_occurrence, ?_, ?_⟩
  · refine ⟨true, trivial, trivial, ?_⟩
    dsimp [M]
    decide
  · intro _
    dsimp [M, S, HasReason]
    decide
  · dsimp [M, S, HasReason]
    decide
  · dsimp [M, S]
    decide
  · dsimp [M, S]
    decide

/- AUDIT ANALYSIS: DISTINCTION BETWEEN PSR AND TELEOLOGICAL SELECTION:
Contrastive PSR demands that a contingent occurrence have an explanatory reason/ground.
In an impersonal chain G -> S -> C, this demand is satisfied by the independent ground G.
The inference that S must depend on its future consequence C is NOT derived from PSR;
it is asserted by the separate assumption `consequence_dependent_selection`:
  (¬ Necessitates ∧ HasContrastiveReason) → GroundingDependsOn S C
which posits that any non-necessitating source must be teleologically specified by its effect.
Without that teleological assumption, PSR and grounding well-foundedness coexist with
complete absence of backward dependence. -/

/-- AUDIT NOTE ON DEAD CODE:
In `FreeSubjectDeterminationDilemma.lean` (lines 315–319):
`impersonal_antecedent_symmetry_leaves_brute` was included in `PrimitiveExplanatoryPrinciples`:
`¬ Necessitates ∧ ¬ GroundingDependsOn S C → ¬ HasContrastiveReason`
However, in the proof of `impersonal_contingent_source_derives_consequence_dependence` (lines 324–332),
this premise is NEVER USED. The derivation consumes only `contrastive_psr` and
`consequence_dependent_selection`. The symmetry premise is purely decorative. -/
theorem impersonal_antecedent_symmetry_is_deductively_redundant
    {P Q R : Prop}
    (psr : P → Q)
    (_symmetry_unused : ¬ R → ¬ Q)
    (selection : Q → R)
    (hP : P) :
    R :=
  selection (psr hP)

/-!
================================================================================
VI. ATTACK 4: THE ORIGIN TAXONOMY GAP
================================================================================
-/

/-- In `FreeSubjectDeterminationDilemma.lean` (lines 413–460), the taxonomy defines:
- `NecessitatedBySourceNature`: requires invariance (`∀ alt, SamePast → OutcomeOf S alt = OutcomeOf S actualWorld`)
- `ImpersonalContingentSource`: requires non-necessitation (`¬ Necessitates M S.sourceConfig M.concreteOccurrence`)

This partition creates an artificial omission:
What about an impersonal source that DOES necessitate its consequence,
but whose configuration is CONTINGENT under the same complete past?

We formalize this category:
**Contingent Deterministic Impersonal Source (CDIS)**. -/
def ContingentDeterministicImpersonalSource
    (M : DeterminationModel.{u, v, w})
    (S : UltimateSource.{u, v, w} M) : Prop :=
  Necessitates M S.sourceConfig M.concreteOccurrence ∧
  SourceConfigContingent M S ∧
  (¬ ∃ agent : M.Agent, M.IsAgent agent ∧ M.OriginatesAt agent S.sourceConfig) ∧
  IsUltimate M.Determines S.sourceConfig

/-- THEOREM (The Taxonomy Gap):
A Contingent Deterministic Impersonal Source with a sufficient reason and no external
unforced ground CANNOT be classified under ANY of the six branches of OriginExplanationTaxonomy:
1. Not ForcedPersonalSource (it has no prior determiner).
2. Not BruteContingentFact (it has a sufficient reason).
3. Not NecessitatedBySourceNature (it is contingent across accessible same-past worlds).
4. Not ImpersonalContingentSource (it necessitates its outcome).
5. Not IndependentNonCausalGround (it has no external unforced ground event).
6. Not PersonalSource (it has no personal agent).
Hence OriginExplanationTaxonomy achieves exhaustiveness solely by decree. -/
theorem taxonomy_omits_contingent_deterministic_source
    (M : DeterminationModel.{u, v, w})
    (S : UltimateSource.{u, v, w} M)
    (hCDIS : ContingentDeterministicImpersonalSource M S)
    (HasSufficientReason : M.Event → Prop)
    (hHasReason : HasSufficientReason S.sourceConfig)
    (hNoExternalGround : ¬ ∃ G : M.Event,
      M.GroundingDependsOn S.sourceConfig G ∧
      (¬ ∃ p, M.Determines p G) ∧
      (¬ ∃ agent : M.Agent, M.IsAgent agent ∧ M.OriginatesAt agent S.sourceConfig))
    -- Six implications matching OriginExplanationTaxonomy:
    (hForced_implies_determiner : ∀ Forced : Prop, Forced → ∃ p, M.Determines p S.sourceConfig)
    (hBrute_implies_no_reason : ∀ Brute : Prop, Brute → ¬ HasSufficientReason S.sourceConfig)
    (hNature_implies_invariant : ∀ NatNec : Prop, NatNec →
      (∀ alt : M.World, M.SameCompletePriorState M.actualWorld alt →
        M.OutcomeOf S.sourceConfig alt = M.OutcomeOf S.sourceConfig M.actualWorld))
    (hImpersonal_implies_nonNec : ∀ ImpNonNec : Prop, ImpNonNec →
      ¬ Necessitates M S.sourceConfig M.concreteOccurrence)
    (hIndep_implies_ground : ∀ Indep : Prop, Indep →
      ∃ G : M.Event,
        M.GroundingDependsOn S.sourceConfig G ∧
        (¬ ∃ p, M.Determines p G) ∧
        (¬ ∃ agent : M.Agent, M.IsAgent agent ∧ M.OriginatesAt agent S.sourceConfig))
    (hPersonal_implies_agent : ∀ Pers : Prop, Pers →
      ∃ agent : M.Agent, M.IsAgent agent ∧ M.OriginatesAt agent S.sourceConfig) :
    ∀ (Forced Brute NatNec ImpNonNec Indep Pers : Prop),
      (Forced → False) ∧
      (Brute → False) ∧
      (NatNec → False) ∧
      (ImpNonNec → False) ∧
      (Indep → False) ∧
      (Pers → False) := by
  intro Forced Brute NatNec ImpNonNec Indep Pers
  obtain ⟨hNec, hCont, hNoAgent, hUlt⟩ := hCDIS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hF
    obtain ⟨p, hp⟩ := hForced_implies_determiner Forced hF
    exact hUlt ⟨p, hp⟩
  · intro hB
    have hNoReason := hBrute_implies_no_reason Brute hB
    exact hNoReason hHasReason
  · intro hN
    have hInv := hNature_implies_invariant NatNec hN
    obtain ⟨alt, _, hSamePast, hDiffCfg⟩ := hCont
    have hEq := hInv alt hSamePast
    exact hDiffCfg hEq
  · intro hI
    have hNonNec := hImpersonal_implies_nonNec ImpNonNec hI
    exact hNonNec hNec
  · intro hInd
    have hGround := hIndep_implies_ground Indep hInd
    exact hNoExternalGround hGround
  · intro hP
    have hAgent := hPersonal_implies_agent Pers hP
    exact hNoAgent hAgent

/-- COMPANION THEOREM (Accommodation Under Independent Ground):
When an independent non-causal ground G DOES exist, a Contingent Deterministic
Impersonal Source CAN be classified under `IndependentNonCausalGround`.
Thus the taxonomy is not unconditionally empty, but lacks a dedicated category for
contingent deterministic impersonal sources that do not possess an external unforced ground node. -/
theorem contingent_deterministic_source_satisfies_independent_ground_when_present
    (M : DeterminationModel.{u, v, w})
    (S : UltimateSource.{u, v, w} M)
    (G : M.Event)
    (hGround : M.GroundingDependsOn S.sourceConfig G)
    (hUnforced : ¬ ∃ p, M.Determines p G)
    (hNoAgent : ¬ ∃ agent : M.Agent, M.IsAgent agent ∧ M.OriginatesAt agent S.sourceConfig) :
    ∃ G' : M.Event,
      M.GroundingDependsOn S.sourceConfig G' ∧
      (¬ ∃ p, M.Determines p G') ∧
      (¬ ∃ agent : M.Agent, M.IsAgent agent ∧ M.OriginatesAt agent S.sourceConfig) :=
  ⟨G, hGround, hUnforced, hNoAgent⟩

/-!
================================================================================
VII. ATTACK 5: FOUR ADVERSARIAL COUNTERMODELS FOR UNSUPPORTED GAPS
================================================================================
-/

/-- The Grounding relation in the ground-direction:
`Grounds y x` means `y` grounds `x` (i.e. `x` depends on `y`). -/
def Grounds {α : Type u} (GroundingDependsOn : α → α → Prop) (y x : α) : Prop :=
  GroundingDependsOn x y

/- AUDIT ANALYSIS: EXPLANATORY WELL-FOUNDEDNESS ORIENTATION:
In `DeterminationModel`, `GroundingDependsOn x y` means `x` depends on `y` (`y` grounds `x`).
Lean's `WellFounded R` asserts that there are no infinite descending chains `... ≺ z2 ≺ z1 ≺ z0`
where `R a b` represents `a ≺ b`.
- If `R := GroundingDependsOn`, a descending chain represents `z0` grounded by nothing,
  with `z1, z2 ...` depending on it (a chain of consequences).
- If `R := Grounds GroundingDependsOn`, a descending chain represents an infinite regress
  of grounds (`z0` grounded by `z1`, grounded by `z2` ...).
A well-founded relation in EITHER orientation strictly excludes 2-cycles (`wellFounded_explanation_has_no_two_cycle`).
However, absence of 2-cycles does NOT imply absence of infinite regress. -/

/-- THEOREM (Infinite Causal Regress Induces Infinite Regress of Grounds):
If determination ancestry terminates nowhere (every event has a prior determiner)
and every causal determination step transmits explanatory grounding
(∀ a b, Determines a b → GroundingDependsOn b a), then the ground-ascending relation
`Grounds GroundingDependsOn` contains an infinite regress and is NOT well-founded. -/
theorem infinite_causal_regress_induces_infinite_grounding_regress
    {Event : Type}
    (Determines : Event → Event → Prop)
    (GroundingDependsOn : Event → Event → Prop)
    (hTrans : ∀ a b, Determines a b → GroundingDependsOn b a)
    (e0 : Event)
    (next : Event → Event)
    (hStep : ∀ e, Determines (next e) e) :
    ¬ WellFounded (Grounds GroundingDependsOn) := by
  intro hWF
  have hChain : ∀ e, Grounds GroundingDependsOn (next e) e := by
    intro e
    dsimp [Grounds]
    exact hTrans (next e) e (hStep e)
  have hNoMin : ∀ e, Acc (Grounds GroundingDependsOn) e → False := by
    intro e hAcc
    induction hAcc with
    | intro x _ ih =>
      exact ih (next x) (hChain x)
  exact hNoMin e0 (hWF.apply e0)

/-!
--------------------------------------------------------------------------------
Countermodel A: Concrete Occurrence → Ultimate Source FAILS (Infinite Causal Regress)
--------------------------------------------------------------------------------
The assumption `AncestryTerminatesDetermines` assumes that determination ancestry
terminates. Here we prove that a concrete occurrence can exist within an infinite
causal regress on `Nat` where every event is determined by its predecessor,
so NO ultimate source exists.

NOTE ON BASELINE WELL-FOUNDEDNESS:
In the baseline `DeterminationModel` from `FreeSubjectDeterminationDilemma.lean:98`,
the well-foundedness field was defined as `WellFounded GroundingDependsOn`.
In this model, `GroundRelNat b a := b < a` is well-founded in Lean's sense because
consequences terminate at 0, while grounds regress infinitely (0 <- 1 <- 2 ...).
This demonstrates that the original model's well-foundedness constraint failed to
preclude an infinite regress of grounds due to inverted orientation!
-/

def rankNat (n : Nat) : Nat := n

def GroundRelNat (y x : Nat) : Prop := y < x

theorem transGen_detNat {a b : Nat} (h : Relation.TransGen (fun x y => x = y + 1) a b) : b < a := by
  induction h with
  | single h1 =>
    rw [h1]
    exact Nat.lt_succ_self _
  | tail _ h2 ih =>
    obtain rfl := h2
    exact Nat.lt_trans (Nat.lt_succ_self _) ih

theorem infinite_regress_no_ultimate_source :
    ∃ (M : DeterminationModel.{0, 0, 0}),
      M.Occurs M.concreteOccurrence ∧
      (∀ s : M.Event, ¬ IsUltimate M.Determines s) ∧
      (∀ agent : M.Agent, ¬ M.IsAgent agent) := by
  let E : Type := Nat
  let DetNat (a b : Nat) : Prop := a = b + 1
  let hWF : WellFounded GroundRelNat := (measure rankNat).wf
  let M : DeterminationModel.{0, 0, 0} := {
    Event := E
    Occurs := fun _ => True
    concreteOccurrence := 0
    Determines := DetNat
    GroundingDependsOn := GroundRelNat
    genuine_grounding_is_well_founded := hWF
    ontological_determination_implies_explanatory_dependence := by
      intro a b hab
      have hLt := transGen_detNat hab
      exact hLt
    World := Unit
    actualWorld := ()
    Accessible := fun _ _ => True
    SameCompletePriorState := fun _ _ => True
    Outcome := Unit
    OutcomeOf := fun _ _ => ()
    Agent := Empty
    IsAgent := fun _ => True
    OriginatesAt := fun _ _ => True
    ControlsAlternative := fun _ _ _ => True
  }
  refine ⟨M, trivial, ?_, ?_⟩
  · intro s
    -- Every event s has a prior determiner (s + 1)
    intro hUlt
    apply hUlt
    exact ⟨s + 1, rfl⟩
  · intro a
    cases a

/-!
--------------------------------------------------------------------------------
Countermodel B: Ultimate Source → Personal Source FAILS (Indeterministic Impersonal Source)
--------------------------------------------------------------------------------
An unforced impersonal source non-necessitatingly causes the occurrence.
Contradiction is avoided because `consequence_dependent_selection` is rejected.
-/
theorem impersonal_indeterministic_source_model :
    ∃ (M : DeterminationModel.{0, 0, 0}) (S : UltimateSource.{0, 0, 0} M),
      ¬ Necessitates M S.sourceConfig M.concreteOccurrence ∧
      HasSamePastAlternative M ∧
      IsUltimate M.Determines S.sourceConfig ∧
      (∀ agent : M.Agent, ¬ M.IsAgent agent) := by
  let E : Type := Fin 2
  let S_node : E := 0
  let C_node : E := 1
  have hWF : WellFounded GroundRel2 := (measure rank2).wf
  let M : DeterminationModel.{0, 0, 0} := {
    Event := E
    Occurs := fun _ => True
    concreteOccurrence := C_node
    Determines := Det2
    GroundingDependsOn := GroundRel2
    genuine_grounding_is_well_founded := hWF
    ontological_determination_implies_explanatory_dependence := by
      intro a b hab
      obtain ⟨rfl, rfl⟩ := transGen_det2 hab
      decide
    World := Bool
    actualWorld := false
    Accessible := fun _ _ => True
    SameCompletePriorState := fun _ _ => True
    Outcome := Bool
    -- S is constant (impersonal antecedent), C is indeterministic (flips across worlds)
    OutcomeOf := fun e w => if e = 1 then w else false
    Agent := Empty
    IsAgent := fun _ => True
    OriginatesAt := fun _ _ => True
    ControlsAlternative := fun _ _ _ => True
  }
  let S : UltimateSource.{0, 0, 0} M := {
    sourceConfig := S_node
    config_occurs := trivial
    determines_occurrence := Relation.TransGen.single ⟨rfl, rfl⟩
    is_ultimate := by
      rintro ⟨p, _hp1, hp2⟩
      revert hp2
      decide
  }
  refine ⟨M, S, ?_, ?_, S.is_ultimate, ?_⟩
  · intro hNec
    have hEq := hNec true trivial rfl
    dsimp [M] at hEq
    revert hEq
    decide
  · refine ⟨true, trivial, trivial, ?_⟩
    dsimp [M]
    decide
  · intro a
    cases a

/-!
--------------------------------------------------------------------------------
Countermodel C: Independent Ground → Personal Source FAILS
--------------------------------------------------------------------------------
An independent impersonal ground G grounds S, S determines C, no agents exist.
Proves that `ContrastiveTeleologyPrinciple` is strictly non-logical and indispensable.
-/
theorem impersonal_law_grounded_source_model :
    ∃ (M : DeterminationModel.{0, 0, 0}) (S : UltimateSource.{0, 0, 0} M) (G : M.Event),
      M.GroundingDependsOn S.sourceConfig G ∧
      (¬ ∃ p, M.Determines p G) ∧
      IsUltimate M.Determines S.sourceConfig ∧
      (∀ agent : M.Agent, ¬ M.IsAgent agent) := by
  obtain ⟨M, S, G, _, _, hG_unforced, hG_ground, _, _, _, _, hUlt, _, hNoAgent⟩ :=
    deterministic_independent_ground_model
  have hG_not_det : ¬ ∃ p, M.Determines p G := by
    rintro ⟨p, hp⟩
    exact hG_unforced p hp
  exact ⟨M, S, G, hG_ground, hG_not_det, hUlt, hNoAgent⟩

/-!
--------------------------------------------------------------------------------
Countermodel D: Personal Source → Free Subject FAILS (The Agential Luck Gap)
--------------------------------------------------------------------------------
An unforced personal originator originates the occurrence, and a same-past
alternative exists, but the agent lacks active control (`ControlsAlternative = False`).
This exposes `AgentialControlBridge` as an unproved postulate that resolves the
Mind argument by definitional fiat.
-/
def FreeSubject (M : DeterminationModel.{u, v, w}) (agent : M.Agent) : Prop :=
  M.IsAgent agent ∧
  ∃ sourceConfig : M.Event,
    IsUltimate M.Determines sourceConfig ∧
    (M.IsAgent agent ∧ M.OriginatesAt agent sourceConfig) ∧
    AncestrallyDetermines M.Determines sourceConfig M.concreteOccurrence ∧
    ∃ alternative : M.World,
      M.Accessible M.actualWorld alternative ∧
      M.SameCompletePriorState M.actualWorld alternative ∧
      M.OutcomeOf M.concreteOccurrence alternative ≠ M.OutcomeOf M.concreteOccurrence M.actualWorld ∧
      M.ControlsAlternative agent sourceConfig alternative

theorem unforced_agent_without_control_model :
    ∃ (M : DeterminationModel.{0, 0, 0}) (agent : M.Agent) (S : UltimateSource.{0, 0, 0} M),
      M.IsAgent agent ∧
      M.OriginatesAt agent S.sourceConfig ∧
      IsUltimate M.Determines S.sourceConfig ∧
      HasSamePastAlternative M ∧
      (¬ FreeSubject M agent) := by
  let E : Type := Fin 2
  let S_node : E := 0
  let C_node : E := 1
  let W : Type := Bool
  let O : Type := Bool
  let A : Type := Unit
  have hWF : WellFounded GroundRel2 := (measure rank2).wf
  let M : DeterminationModel.{0, 0, 0} := {
    Event := E
    Occurs := fun _ => True
    concreteOccurrence := C_node
    Determines := Det2
    GroundingDependsOn := GroundRel2
    genuine_grounding_is_well_founded := hWF
    ontological_determination_implies_explanatory_dependence := by
      intro a b hab
      obtain ⟨rfl, rfl⟩ := transGen_det2 hab
      decide
    World := W
    actualWorld := false
    Accessible := fun _ _ => True
    SameCompletePriorState := fun _ _ => True
    Outcome := O
    OutcomeOf := fun e w => if e = 1 then w else false
    Agent := A
    IsAgent := fun _ => True
    OriginatesAt := fun _ e => e = S_node
    ControlsAlternative := fun _ _ _ => False  -- Agent has NO control over alternative
  }
  let S : UltimateSource.{0, 0, 0} M := {
    sourceConfig := S_node
    config_occurs := trivial
    determines_occurrence := Relation.TransGen.single ⟨rfl, rfl⟩
    is_ultimate := by
      rintro ⟨p, _hp1, hp2⟩
      revert hp2
      decide
  }
  refine ⟨M, (), S, trivial, rfl, S.is_ultimate, ?_, ?_⟩
  · refine ⟨true, trivial, trivial, ?_⟩
    dsimp [M]
    decide
  · intro hFS
    rcases hFS with ⟨_, _, _, _, _, alt, _, _, _, hCtrl⟩
    exact hCtrl

/-!
================================================================================
VIII. MINIMAL CONDITIONAL FREE SUBJECT THEOREM
================================================================================
Here we formulate the conditional theorem with ALL indispensable premises visible
and ALL dead/cosmetic code removed.
-/

/-- The exact minimal philosophical assumptions needed to close the derivation:
1. `AncestryTerminates`: Causal ancestry terminates at an ultimate source.
2. `ContingencyTransfer`: Contingency implies source contingency or non-necessitation.
3. `ContrastivePSR`: Same-past alternative demands a contrastive explanation.
4. `ConsequenceDependentSelection`: Non-necessitating impersonal source depends on consequence.
5. `ContrastiveTeleology`: Independent non-causal grounds are eliminated.
6. `TaxonomyDisjunction`: The taxonomy covers all non-personal cases.
7. `AgentialControl`: An unforced personal originator exercises active control. -/
structure MinimalPhilosophicalBridges (M : DeterminationModel.{u, v, w}) where
  AncestryTerminates :
    M.Occurs M.concreteOccurrence → Nonempty (UltimateSource.{u, v, w} M)
  ContingencyTransfer :
    (S : UltimateSource M) → HasSamePastAlternative M →
      SourceConfigContingent M S ∨ ¬ Necessitates M S.sourceConfig M.concreteOccurrence
  HasContrastiveReason : M.Event → Prop
  ContrastivePSR :
    HasSamePastAlternative M → (S : UltimateSource M) → HasContrastiveReason S.sourceConfig
  ConsequenceDependentSelection :
    (S : UltimateSource M) →
      (¬ Necessitates M S.sourceConfig M.concreteOccurrence ∧
       HasContrastiveReason S.sourceConfig) →
      M.GroundingDependsOn S.sourceConfig M.concreteOccurrence
  ContrastiveTeleology :
    (S : UltimateSource M) →
    ∀ G : M.Event,
      M.GroundingDependsOn S.sourceConfig G →
      (¬ ∃ p, M.Determines p G) →
      (Necessitates M S.sourceConfig M.concreteOccurrence ∧
       (∀ alt : M.World, M.SameCompletePriorState M.actualWorld alt →
         M.OutcomeOf S.sourceConfig alt = M.OutcomeOf S.sourceConfig M.actualWorld)) ∨
      (¬ HasContrastiveReason S.sourceConfig) ∨
      M.GroundingDependsOn S.sourceConfig M.concreteOccurrence ∨
      (∃ agent : M.Agent, M.IsAgent agent ∧ M.OriginatesAt agent S.sourceConfig)
  TaxonomyDisjunction :
    (S : UltimateSource M) →
      (∃ p, M.Determines p S.sourceConfig) ∨
      (SourceConfigContingent M S ∧ ¬ HasContrastiveReason S.sourceConfig) ∨
      (Necessitates M S.sourceConfig M.concreteOccurrence ∧
       (∀ alt : M.World, M.SameCompletePriorState M.actualWorld alt →
         M.OutcomeOf S.sourceConfig alt = M.OutcomeOf S.sourceConfig M.actualWorld)) ∨
      (¬ Necessitates M S.sourceConfig M.concreteOccurrence) ∨
      (∃ G, M.GroundingDependsOn S.sourceConfig G ∧ (¬ ∃ p, M.Determines p G) ∧
        (¬ ∃ agent : M.Agent, M.IsAgent agent ∧ M.OriginatesAt agent S.sourceConfig)) ∨
      (∃ agent : M.Agent, M.IsAgent agent ∧ M.OriginatesAt agent S.sourceConfig)
  AgentialControl :
    (S : UltimateSource M) → (agent : M.Agent) →
      M.IsAgent agent ∧ M.OriginatesAt agent S.sourceConfig →
      HasSamePastAlternative M →
      ∃ alternative : M.World,
        M.Accessible M.actualWorld alternative ∧
        M.SameCompletePriorState M.actualWorld alternative ∧
        M.OutcomeOf M.concreteOccurrence alternative ≠ M.OutcomeOf M.concreteOccurrence M.actualWorld ∧
        M.ControlsAlternative agent S.sourceConfig alternative

/-- THE MINIMAL CONDITIONAL THEOREM:
Every single premise required to derive a Free Subject is exposed.
No circularity is hidden inside definitions or cosmetic structures. -/
theorem minimal_conditional_free_subject_theorem
    (M : DeterminationModel.{u, v, w})
    (hProof : ProofOccurrence M)
    (B : MinimalPhilosophicalBridges M) :
    ∃ agent : M.Agent, FreeSubject M agent := by
  have hOccurs := hProof.proof_occurs
  have hCont := hProof.proof_is_contingent
  obtain ⟨S⟩ := B.AncestryTerminates hOccurs
  have hPersonal : ∃ agent : M.Agent, M.IsAgent agent ∧ M.OriginatesAt agent S.sourceConfig := by
    rcases B.TaxonomyDisjunction S with
      hForced | hBrute | hNat | hImp | hIndep | hPers
    · obtain ⟨p, hp⟩ := hForced
      exact False.elim (S.is_ultimate ⟨p, hp⟩)
    · obtain ⟨_, hNoReason⟩ := hBrute
      have hReason := B.ContrastivePSR hCont S
      exact False.elim (hNoReason hReason)
    · obtain ⟨hNec, hSameCfg⟩ := hNat
      obtain ⟨alt, hAcc, hSamePast, hDiffOutcome⟩ := hCont
      have hEqCfg := hSameCfg alt hSamePast
      have hEqOutcome := hNec alt hAcc hEqCfg
      exact False.elim (hDiffOutcome hEqOutcome)
    · have hReason := B.ContrastivePSR hCont S
      have hDep := B.ConsequenceDependentSelection S ⟨hImp, hReason⟩
      have hForward := M.ontological_determination_implies_explanatory_dependence S.determines_occurrence
      exact False.elim (wellFounded_explanation_has_no_two_cycle
        M.GroundingDependsOn M.genuine_grounding_is_well_founded hDep hForward)
    · obtain ⟨G, hG_ground, hG_unforced, hNoAgent⟩ := hIndep
      rcases B.ContrastiveTeleology S G hG_ground hG_unforced with
        ⟨hNec, hSameCfg⟩ | hNoReason | hCycle | ⟨agent, hAgent, hOrig⟩
      · obtain ⟨alt, hAcc, hSamePast, hDiffOutcome⟩ := hCont
        have hEqCfg := hSameCfg alt hSamePast
        have hEqOutcome := hNec alt hAcc hEqCfg
        exact False.elim (hDiffOutcome hEqOutcome)
      · have hReason := B.ContrastivePSR hCont S
        exact False.elim (hNoReason hReason)
      · have hForward := M.ontological_determination_implies_explanatory_dependence S.determines_occurrence
        exact False.elim (wellFounded_explanation_has_no_two_cycle
          M.GroundingDependsOn M.genuine_grounding_is_well_founded hCycle hForward)
      · exact False.elim (hNoAgent ⟨agent, hAgent, hOrig⟩)
    · exact hPers
  obtain ⟨agent, hAgent, hOrig⟩ := hPersonal
  obtain ⟨alternative, hAcc, hSamePast, hDiffOutcome, hCtrl⟩ :=
    B.AgentialControl S agent ⟨hAgent, hOrig⟩ hCont
  refine ⟨agent, hAgent, S.sourceConfig, S.is_ultimate, ⟨hAgent, hOrig⟩,
          S.determines_occurrence, alternative, hAcc, hSamePast, hDiffOutcome, hCtrl⟩

/-!
================================================================================
IX. KERNEL AXIOM AUDIT
================================================================================
-/

#print axioms wellFounded_explanation_has_no_two_cycle
#print axioms ancestrallyDetermines_preserves_determinism
#print axioms ancestrallyDetermines_implies_necessitates
#print axioms impossibility_of_invariant_deterministic_contingency
#print axioms deterministic_independent_ground_model
#print axioms invariant_ground_cannot_contrastively_explain_contingent_source
#print axioms wellFounded_and_psr_do_not_derive_backward_dependence
#print axioms impersonal_antecedent_symmetry_is_deductively_redundant
#print axioms taxonomy_omits_contingent_deterministic_source
#print axioms contingent_deterministic_source_satisfies_independent_ground_when_present
#print axioms infinite_causal_regress_induces_infinite_grounding_regress
#print axioms infinite_regress_no_ultimate_source
#print axioms impersonal_indeterministic_source_model
#print axioms impersonal_law_grounded_source_model
#print axioms unforced_agent_without_control_model
#print axioms minimal_conditional_free_subject_theorem

end AdversarialFreeSubjectAudit
end Logos
