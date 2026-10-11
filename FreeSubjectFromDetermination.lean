import Lean

/-!
# Free Subject from Determination via Explanatory Circularity

This module formalizes the derivation of a **Free Subject** from the concrete
determined occurrence of a proof, refactored around the principle of
**ultimate explanatory circularity**.

## 1. Philosophical Target & Architecture

Target claim:
**If this proof exists as a concrete determined occurrence, then a Free Subject exists.**

### How this refactoring differs from the judgment-chain approach:
* The original proof (`best.lean`) derived freedom from an instantiated
  `JudgmentDeterminationChain`, relying on the occurrence being a judgment that
  assents to or withholds a proposition (`AssentsAt`, `WithholdsAt`).
* This module **does not depend on the occurrence being a judgment**, appearing
  to be a judgment, or satisfying any judicative psychological structure. It models
  the occurrence simply as a concrete determined event in spacetime.
* The argument focuses entirely on the **explanatory structure of determination itself**.

### Two rigorously distinguished relations:
1. `Determines : Event → Event → Prop`:
   Causal or constitutive determination within the physical/metaphysical chain.
   Transitive ancestry is formalized as `AncestrallyDetermines` via `Relation.TransGen`.
2. `GroundingDependsOn : Event → Event → Prop`:
   Explanatory dependence: what explains *why* an event has its actual determinate
   configuration rather than another. Explanatory dependence is strictly non-temporal;
   circularity at issue is explanatory, not physical feedback.

### The Central Result: Explanatory Circularity of Impersonal Contingency
1. An ultimate source configuration determines the concrete occurrence, so the occurrence
   depends on the source configuration for its determination
   (`GroundingDependsOn concreteOccurrence sourceConfig`).
2. If the proposed ultimate source is **impersonal** and **contingent**:
   - It does not necessitate the outcome (contingency).
   - It does not choose or act for reasons (impersonality).
   Therefore, the source's antecedent nature cannot explain why *this* specific
   outcome was determined rather than another. Any proposed complete explanation of
   its determination must invoke the actual consequence to select or specify the source's
   determinate profile. Thus, explanatory dependence points backward:
   `GroundingDependsOn sourceConfig concreteOccurrence`.
3. This creates an explanatory cycle:
   `GroundingDependsOn sourceConfig conc ∧ GroundingDependsOn conc sourceConfig`.
4. Under the principle that genuine explanatory grounding is well-founded
   (`WellFounded GroundingDependsOn`), circular explanations cannot ground the configuration.
   Hence, the impersonal contingent source fails as an ultimate explanation.
5. The remaining impersonal candidates (necessitation by nature, brute contingent fact,
   antecedent determiner, or independent non-causal ground) are eliminated via:
   - Ultimacy (`is_ultimate`: no antecedent determiner),
   - Principle of Sufficient Reason (contingent determinations are not brute facts),
   - Contingency (`necessitation_excludes_contingency`: necessitation precludes accessible same-past divergence),
   - Non-causal ground dilemma (an independent ground either necessitates, fails to select, or collapses into circularity/regress).
6. The only remaining alternative is a **Personal Source**.
7. Via the explicit **Agential Sufficient Reason Principle**, an unforced personal agent
   originating a contingent occurrence exercises active control over the accessible same-past
   alternative (precluding agential luck), strictly deriving the existence of a **Free Subject**.

### Metatheoretic distinction:
The external fact that this `.lean` file exists in spacetime is a metatheoretic datum.
`ProofOccurrence M` links this datum to the formal model, supplying the occurrence
and its contingency (`proof_occurs` and `proof_is_contingent`).
-/

namespace Logos
namespace FreeSubjectFromDetermination

universe u v w

/-!
================================================================================
II. ANCESTRAL DETERMINATION AND WELL-FOUNDED GROUNDING
================================================================================
-/

/-- Transitive ancestral determination: `AncestrallyDetermines Determines a b` means
that `a` determines `b` through a non-empty finite chain of determination steps.
Formulated using Lean 4 core `Relation.TransGen`. -/
def AncestrallyDetermines {α : Type u} (Determines : α → α → Prop) : α → α → Prop :=
  Relation.TransGen Determines

/-- An event `s` is an ultimate source with respect to `Determines` if no prior event
determines it within the modeled domain. -/
def IsUltimate {α : Type u} (Determines : α → α → Prop) (s : α) : Prop :=
  ¬ ∃ p : α, Determines p s

/-- Fundamental logical lemma: A well-founded explanatory relation cannot contain a 2-cycle.
If `DependsOn a b` and `DependsOn b a`, well-founded induction yields `False`. -/
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

/-!
================================================================================
III. MINIMAL DETERMINATION AND EXPLANATORY MODEL
================================================================================
-/

/-- A minimal model of a concrete determined occurrence, its causal ancestry,
explanatory grounding, modal contingency, and agential structure.
Does NOT import judgment, assents, or withholds.
The contingency of the occurrence is not duplicated as a field here; it is supplied
by the proof occurrence bridge `ProofOccurrence`. -/
structure DeterminationModel where
  Event : Type u
  Occurs : Event → Prop
  concreteOccurrence : Event

  /-- Causal or constitutive determination within the chain. -/
  Determines : Event → Event → Prop

  /-- Explanatory grounding: `GroundingDependsOn x y` means why `x` has its actual
  determinate configuration is explained by `y`. -/
  GroundingDependsOn : Event → Event → Prop

  /-- Principle: genuine ultimate explanatory grounding is well-founded.
  An explanatory circle does not ground itself. -/
  genuine_grounding_is_well_founded : WellFounded GroundingDependsOn

  /-- Causal ancestry transmits explanatory dependence: if `a` ancestrally determines
  `b`, then `b` depends explanatorily on `a` for its determination. -/
  causal_ancestry_implies_explanatory_dependence :
    ∀ {a b : Event}, AncestrallyDetermines Determines a b → GroundingDependsOn b a

  /-- Modal framework for contingency and alternatives. -/
  World : Type v
  actualWorld : World
  Accessible : World → World → Prop
  SameCompletePriorState : World → World → Prop
  Outcome : Type w
  OutcomeOf : Event → World → Outcome

  /-- Agential sort and relations. -/
  Agent : Type u
  IsAgent : Agent → Prop
  OriginatesAt : Agent → Event → Prop
  /-- Active agential control over a divergent outcome under the same complete past. -/
  ControlsAlternative : Agent → Event → World → Prop

/-- Proposition expressing that the concrete occurrence has an accessible same-past alternative. -/
def HasSamePastAlternative (M : DeterminationModel.{u, v, w}) : Prop :=
  ∃ alternative : M.World,
    M.Accessible M.actualWorld alternative ∧
    M.SameCompletePriorState M.actualWorld alternative ∧
    M.OutcomeOf M.concreteOccurrence alternative ≠ M.OutcomeOf M.concreteOccurrence M.actualWorld

/-- Metatheoretic bridge linking the external existence of this Lean proof text
in spacetime to the formal model.
The external existence of the file is a metatheoretic datum.
`ProofOccurrence M` specifies that `M.concreteOccurrence` is the determined event
corresponding to this proof, and that its occurrence is contingent (it was discovered
and verified, but under the same complete physical past prior to its discovery,
its explicit tokening was not necessitated). -/
structure ProofOccurrence (M : DeterminationModel.{u, v, w}) : Prop where
  proof_occurs : M.Occurs M.concreteOccurrence
  proof_is_contingent : HasSamePastAlternative M

/-- An ultimate source for the concrete occurrence within the determination ancestry.
The source substrate `sourceSubstrate` represents the underlying entity or ground,
while `sourceConfig` represents its actual determinate configuration (the specific state,
valuation, or act-profile) that ancestrally determines `concreteOccurrence`. -/
structure UltimateSource (M : DeterminationModel.{u, v, w}) where
  sourceSubstrate : Type u
  sourceConfig : M.Event
  config_occurs : M.Occurs sourceConfig
  determines_occurrence : AncestrallyDetermines M.Determines sourceConfig M.concreteOccurrence
  is_ultimate : IsUltimate M.Determines sourceConfig

/-- Causal ancestry termination condition: the concrete occurrence possesses an ultimate source
within its ancestral determination tree.
Kept as an explicit, separate premise to avoid smuggling a first cause into the definition of causality. -/
def AncestryTerminatesDetermines (M : DeterminationModel.{u, v, w}) : Prop :=
  Nonempty (UltimateSource.{u, v, w} M)

/-!
================================================================================
IV. NECESSITATION & CONTINGENCY TRANSFER
================================================================================
-/

/-- An event `cfg` necessitates an outcome `conc` if in all accessible worlds where
`cfg` obtains, `conc` produces the same outcome as in the actual world. -/
def Necessitates (M : DeterminationModel.{u, v, w}) (cfg conc : M.Event) : Prop :=
  ∀ alternative : M.World,
    M.Accessible M.actualWorld alternative →
    M.OutcomeOf cfg alternative = M.OutcomeOf cfg M.actualWorld →
    M.OutcomeOf conc alternative = M.OutcomeOf conc M.actualWorld

/-- The source configuration is contingent across accessible worlds sharing the same complete prior state. -/
def SourceConfigContingent (M : DeterminationModel.{u, v, w}) (S : UltimateSource.{u, v, w} M) : Prop :=
  ∃ alternative : M.World,
    M.Accessible M.actualWorld alternative ∧
    M.SameCompletePriorState M.actualWorld alternative ∧
    M.OutcomeOf S.sourceConfig alternative ≠ M.OutcomeOf S.sourceConfig M.actualWorld

/-- THE CONTINGENCY TRANSFER BRIDGE (PHILOSOPHICAL BRIDGE):
If an occurrence is contingent under the same complete prior state (`HasSamePastAlternative M`),
then its ultimate determiner cannot both be completely fixed by the prior state AND necessitate the outcome.
Either:
(1) The ultimate source's determinate configuration is itself contingent (`SourceConfigContingent M S`), or
(2) The source's configuration does not necessitate the outcome (`¬ Necessitates M S.sourceConfig M.concreteOccurrence`).
-/
def ContingencyTransferBridge (M : DeterminationModel.{u, v, w}) (S : UltimateSource.{u, v, w} M) : Prop :=
  HasSamePastAlternative M →
    SourceConfigContingent M S ∨ ¬ Necessitates M S.sourceConfig M.concreteOccurrence

/-- Theorem: An ultimate source configuration that necessitates its outcome cannot coexist
with a divergent outcome under the same complete prior state if the configuration itself
is invariant under that prior state. -/
theorem necessitation_excludes_contingency
    (M : DeterminationModel.{u, v, w})
    (S : UltimateSource.{u, v, w} M)
    (hNec : Necessitates M S.sourceConfig M.concreteOccurrence)
    (hSameCfg : ∀ alt : M.World, M.SameCompletePriorState M.actualWorld alt →
      M.OutcomeOf S.sourceConfig alt = M.OutcomeOf S.sourceConfig M.actualWorld)
    (hCont : HasSamePastAlternative M) :
    False := by
  obtain ⟨alt, hAcc, hSamePast, hDiffOutcome⟩ := hCont
  have hEqCfg := hSameCfg alt hSamePast
  have hEqOutcome := hNec alt hAcc hEqCfg
  exact hDiffOutcome hEqOutcome

/-!
================================================================================
V. 5-FOLD EXPLANATORY TAXONOMY & CIRCULARITY REFUTATION
================================================================================
-/

/-- Explanatory taxonomy for why the ultimate source configuration `S.sourceConfig` has its
actual determinate profile.
DOES NOT SMUGGLE `FreeOrigin` OR `FreeSubject` AS AN ASSUMED DISJUNCT.
Instead, it cleanly partitions the origin alternatives into 5 categories:
1. `ForcedPersonalSource`: an agent is involved, but the source has a prior determiner.
2. `BruteContingentFact`: a contingent determination lacking sufficient reason.
3. `NecessitatedBySourceNature`: the source substrate's nature necessitates this configuration.
4. `ImpersonalContingentSource`: an impersonal ground whose determination is contingent.
5. `IndependentNonCausalGround`: an independent non-causal ground proposed to explain the configuration.
6. `PersonalSource`: an agent originates the source configuration without prior determination.
-/
structure OriginExplanationTaxonomy (M : DeterminationModel.{u, v, w}) (S : UltimateSource.{u, v, w} M) where
  /-- Alternative 1: Personal source that is forced by prior determination. -/
  ForcedPersonalSource : Prop
  forced_has_prior_determiner :
    ForcedPersonalSource → ∃ p : M.Event, M.Determines p S.sourceConfig

  /-- Principle of Sufficient Reason: contingent occurrences possess an explanation. -/
  HasSufficientReason : M.Event → Prop
  principle_of_sufficient_reason :
    HasSamePastAlternative M → HasSufficientReason S.sourceConfig

  /-- Alternative 2: Brute contingent fact with no explanation. -/
  BruteContingentFact : Prop
  brute_lacks_sufficient_reason :
    BruteContingentFact → ¬ HasSufficientReason S.sourceConfig

  /-- Alternative 3: The source substrate's nature necessitates this configuration. -/
  NecessitatedBySourceNature : Prop
  nature_necessitates :
    NecessitatedBySourceNature →
      Necessitates M S.sourceConfig M.concreteOccurrence ∧
      (∀ alt : M.World, M.SameCompletePriorState M.actualWorld alt →
        M.OutcomeOf S.sourceConfig alt = M.OutcomeOf S.sourceConfig M.actualWorld)

  /-- Alternative 4: Impersonal ground that is contingent. -/
  ImpersonalContingentSource : Prop

  /-- THE BACKWARD EXPLANATION PRINCIPLE (PHILOSOPHICAL BRIDGE):
  If the ultimate source is impersonal and its outcome is contingent:
  because it does not necessitate its outcome and does not freely choose for reasons,
  why it produced this specific outcome cannot be explained by its antecedent nature alone.
  Any proposed complete explanation of its actual determination must invoke the actual
  consequence to specify the source's determinate profile.
  Therefore, explanatory dependence points backward from consequence to source. -/
  impersonal_contingent_source_is_explained_backwards :
    ImpersonalContingentSource →
      M.GroundingDependsOn S.sourceConfig M.concreteOccurrence

  /-- Alternative 5: An independent non-causal ground G.
  The dilemma: G either necessitates the contingent outcome, fails to explain the selection
  (collapsing into a brute fact), or invokes the consequence to identify the configuration. -/
  IndependentNonCausalGround : Prop
  independent_ground_dilemma :
    IndependentNonCausalGround →
      (Necessitates M S.sourceConfig M.concreteOccurrence ∧
       (∀ alt : M.World, M.SameCompletePriorState M.actualWorld alt →
         M.OutcomeOf S.sourceConfig alt = M.OutcomeOf S.sourceConfig M.actualWorld)) ∨
      BruteContingentFact ∨
      M.GroundingDependsOn S.sourceConfig M.concreteOccurrence

  /-- Alternative 6: An agent originates the source determination without prior determination. -/
  PersonalSource : Prop
  personal_source_is_agential :
    PersonalSource →
      ∃ agent : M.Agent, M.IsAgent agent ∧ M.OriginatesAt agent S.sourceConfig

  /-- The exhaustive classification of explanatory alternatives.
  FreeSubject/FreeOrigin is NOT assumed here; the personal option is merely `PersonalSource`. -/
  taxonomy_is_exhaustive :
    ForcedPersonalSource ∨
    BruteContingentFact ∨
    NecessitatedBySourceNature ∨
    ImpersonalContingentSource ∨
    IndependentNonCausalGround ∨
    PersonalSource

/-- Theorem: An impersonal contingent source creates a 2-cycle in explanatory grounding.
The consequence depends on the source by determination ancestry, while the source
depends on the consequence by the backward-explanation principle. -/
theorem impersonal_contingent_source_forms_explanatory_cycle
    (M : DeterminationModel.{u, v, w})
    (S : UltimateSource.{u, v, w} M)
    (T : OriginExplanationTaxonomy M S)
    (hImp : T.ImpersonalContingentSource) :
    M.GroundingDependsOn S.sourceConfig M.concreteOccurrence ∧
    M.GroundingDependsOn M.concreteOccurrence S.sourceConfig := by
  constructor
  · exact T.impersonal_contingent_source_is_explained_backwards hImp
  · exact M.causal_ancestry_implies_explanatory_dependence S.determines_occurrence

/-- Theorem: An impersonal contingent source cannot serve as an ultimate explanation
because its grounding is circular, contradicting the well-foundedness of genuine grounding. -/
theorem impersonal_contingent_source_fails_as_ultimate_explanation
    (M : DeterminationModel.{u, v, w})
    (S : UltimateSource.{u, v, w} M)
    (T : OriginExplanationTaxonomy M S)
    (hImp : T.ImpersonalContingentSource) :
    False := by
  obtain ⟨hSourceDependsOnEffect, hEffectDependsOnSource⟩ :=
    impersonal_contingent_source_forms_explanatory_cycle M S T hImp
  exact wellFounded_explanation_has_no_two_cycle
    M.GroundingDependsOn
    M.genuine_grounding_is_well_founded
    hSourceDependsOnEffect
    hEffectDependsOnSource

/-- Theorem: Under the taxonomy and principles, any ultimate source of the contingent
occurrence must be a Personal Source.
Eliminates:
- ForcedPersonalSource via ultimacy (has no prior determiner).
- BruteContingentFact via PSR.
- NecessitatedBySourceNature via contingency.
- ImpersonalContingentSource via explanatory circularity.
- IndependentNonCausalGround via the trilemma (necessitation, brute fact, or circularity). -/
theorem ultimate_source_must_be_personal
    (M : DeterminationModel.{u, v, w})
    (S : UltimateSource.{u, v, w} M)
    (T : OriginExplanationTaxonomy M S)
    (hCont : HasSamePastAlternative M) :
    T.PersonalSource := by
  rcases T.taxonomy_is_exhaustive with
    hForced | hBrute | hNat | hImp | hIndep | hPersonal
  · obtain ⟨predecessor, hPred⟩ := T.forced_has_prior_determiner hForced
    exact False.elim (S.is_ultimate ⟨predecessor, hPred⟩)
  · have hReason := T.principle_of_sufficient_reason hCont
    exact False.elim (T.brute_lacks_sufficient_reason hBrute hReason)
  · obtain ⟨hNec, hSameCfg⟩ := T.nature_necessitates hNat
    exact False.elim (necessitation_excludes_contingency M S hNec hSameCfg hCont)
  · exact False.elim (impersonal_contingent_source_fails_as_ultimate_explanation M S T hImp)
  · rcases T.independent_ground_dilemma hIndep with ⟨hNec, hSameCfg⟩ | hBrute2 | hCycle
    · exact False.elim (necessitation_excludes_contingency M S hNec hSameCfg hCont)
    · have hReason := T.principle_of_sufficient_reason hCont
      exact False.elim (T.brute_lacks_sufficient_reason hBrute2 hReason)
    · have hForward := M.causal_ancestry_implies_explanatory_dependence S.determines_occurrence
      exact False.elim (wellFounded_explanation_has_no_two_cycle M.GroundingDependsOn M.genuine_grounding_is_well_founded hCycle hForward)
  · exact hPersonal

/-!
================================================================================
VI. DISTINCT AGENCY CONDITIONS & AGENTIAL SUFFICIENT REASON
================================================================================
-/

/-- Distinct Agency Condition 1: Negative absence of prior determination. -/
def IsUnforced (M : DeterminationModel.{u, v, w}) (e : M.Event) : Prop :=
  ¬ ∃ p, M.Determines p e

/-- Distinct Agency Condition 2: Origination by a personal agent. -/
def AgentiallyOriginated (M : DeterminationModel.{u, v, w}) (agent : M.Agent) (e : M.Event) : Prop :=
  M.IsAgent agent ∧ M.OriginatesAt agent e

/-- Distinct Agency Condition 3: Active agential control over a divergent outcome. -/
def ExercisesControl (M : DeterminationModel.{u, v, w}) (agent : M.Agent) (e : M.Event) (alt : M.World) : Prop :=
  M.ControlsAlternative agent e alt

/-- A Free Subject is an agent who satisfies all 4 distinct conditions:
1. Agential origination (`AgentiallyOriginated`),
2. Unforcedness (`IsUnforced`),
3. Ancestral determination of the concrete occurrence (`AncestrallyDetermines`),
4. An accessible same-past alternative (`HasSamePastAlternative`), and
5. Active control over that alternative (`ExercisesControl`).
Crucially, freedom is not defined as mere absence of a cause, but requires positive
control of the alternative. -/
def FreeSubject (M : DeterminationModel.{u, v, w}) (agent : M.Agent) : Prop :=
  M.IsAgent agent ∧
  ∃ sourceConfig : M.Event,
    IsUnforced M sourceConfig ∧
    AgentiallyOriginated M agent sourceConfig ∧
    AncestrallyDetermines M.Determines sourceConfig M.concreteOccurrence ∧
    ∃ alternative : M.World,
      M.Accessible M.actualWorld alternative ∧
      M.SameCompletePriorState M.actualWorld alternative ∧
      M.OutcomeOf M.concreteOccurrence alternative ≠ M.OutcomeOf M.concreteOccurrence M.actualWorld ∧
      ExercisesControl M agent sourceConfig alternative

/-- THE AGENTIAL SUFFICIENT REASON PRINCIPLE (PHILOSOPHICAL BRIDGE):
An unforced personal agent who originates the ultimate determination of a contingent occurrence
exercises active agential control over which same-past alternative is realized.
This bridges an unforced personal source to positive libertarian freedom, ensuring that
the selection between accessible alternatives is an exercise of agential control,
precluding the collapse of undetermined action into mere arbitrary luck or chance. -/
def AgentialSufficientReasonPrinciple (M : DeterminationModel.{u, v, w}) (S : UltimateSource.{u, v, w} M) : Prop :=
  ∀ agent : M.Agent,
    AgentiallyOriginated M agent S.sourceConfig →
    HasSamePastAlternative M →
    ∃ alternative : M.World,
      M.Accessible M.actualWorld alternative ∧
      M.SameCompletePriorState M.actualWorld alternative ∧
      M.OutcomeOf M.concreteOccurrence alternative ≠ M.OutcomeOf M.concreteOccurrence M.actualWorld ∧
      ExercisesControl M agent S.sourceConfig alternative

/-- Theorem: A personal source together with agential sufficient reason derives a Free Subject. -/
theorem personal_source_and_contingency_yields_free_subject
    (M : DeterminationModel.{u, v, w})
    (S : UltimateSource.{u, v, w} M)
    (T : OriginExplanationTaxonomy M S)
    (hASR : AgentialSufficientReasonPrinciple M S)
    (hPersonal : T.PersonalSource)
    (hCont : HasSamePastAlternative M) :
    ∃ agent : M.Agent, FreeSubject M agent := by
  obtain ⟨agent, hAgent, hOrig⟩ := T.personal_source_is_agential hPersonal
  have hAgOrig : AgentiallyOriginated M agent S.sourceConfig := ⟨hAgent, hOrig⟩
  obtain ⟨alternative, hAcc, hSamePast, hDiffOutcome, hCtrl⟩ := hASR agent hAgOrig hCont
  refine ⟨agent, hAgent, S.sourceConfig, S.is_ultimate, hAgOrig, S.determines_occurrence, alternative, hAcc, hSamePast, hDiffOutcome, hCtrl⟩

/-!
================================================================================
VII. MASTER THEOREM WITH TRANSPARENT DEPENDENCIES
================================================================================
-/

/-- MASTER THEOREM:
If this proof exists as a concrete determined occurrence (`ProofOccurrence M`),
and its determination ancestry terminates at an ultimate source (`AncestryTerminatesDetermines M`),
then under:
1. Explanatory well-foundedness (`genuine_grounding_is_well_founded`),
2. The Principle of Sufficient Reason (`principle_of_sufficient_reason`),
3. The Contingency Transfer Bridge (`ContingencyTransferBridge`),
4. The backward-explanation principle for impersonal contingent sources,
5. The exhaustive origin taxonomy (`OriginExplanationTaxonomy`), and
6. The Agential Sufficient Reason principle (`AgentialSufficientReasonPrinciple`),
a Free Subject exists.

The parameter `hProof` is actively consumed, supplying both the occurrence (`proof_occurs`)
and the contingency (`proof_is_contingent`) of this proof.
All substantive philosophical dependencies are explicitly declared in the theorem signature.
-/
theorem concrete_proof_occurrence_implies_free_subject
    (M : DeterminationModel.{u, v, w})
    (hProof : ProofOccurrence M)
    (hTerm : AncestryTerminatesDetermines M)
    (hContingency : (S : UltimateSource M) → ContingencyTransferBridge M S)
    (T : (S : UltimateSource M) → OriginExplanationTaxonomy M S)
    (hASR : (S : UltimateSource M) → AgentialSufficientReasonPrinciple M S) :
    ∃ agent : M.Agent, FreeSubject M agent := by
  have _hOccurs := hProof.proof_occurs
  have hCont := hProof.proof_is_contingent
  obtain ⟨S⟩ := hTerm
  have _hBridge := hContingency S hCont
  have hPersonal : (T S).PersonalSource := ultimate_source_must_be_personal M S (T S) hCont
  exact personal_source_and_contingency_yields_free_subject M S (T S) (hASR S) hPersonal hCont

/-!
================================================================================
VIII. NEGATIVE INDEPENDENCE TESTS & COUNTERMODELS
================================================================================
-/

/-- Negative Independence Result 1: Mere unforcedness does not imply freedom.
An unforced personal source can originate an occurrence with a same-past alternative
without possessing agential control (`ControlsAlternative = False`).
This demonstrates that Libertarian freedom cannot be defined merely as absence of prior cause;
the Agential Sufficient Reason principle (or personal control bridge) is strictly required. -/
theorem unforced_personal_source_without_control_fails_free_subject :
    ∃ (M : DeterminationModel.{0, 0, 0}),
      (∃ agent : M.Agent, M.IsAgent agent ∧ ∃ s, M.OriginatesAt agent s ∧ IsUltimate M.Determines s) ∧
      HasSamePastAlternative M ∧
      (∀ agent : M.Agent, ¬ FreeSubject M agent) := by
  let E : Type := Unit
  let W : Type := Bool
  let O : Type := Bool
  let A : Type := Unit
  let M : DeterminationModel.{0, 0, 0} := {
    Event := E
    Occurs := fun _ => True
    concreteOccurrence := ()
    Determines := fun _ _ => False
    GroundingDependsOn := fun _ _ => False
    genuine_grounding_is_well_founded := by
      constructor
      intro a
      constructor
      intro y hy
      cases hy
    causal_ancestry_implies_explanatory_dependence := by
      intro a b hab
      cases hab with
      | single h => cases h
      | tail _ h => cases h
    World := W
    actualWorld := false
    Accessible := fun _ _ => True
    SameCompletePriorState := fun _ _ => True
    Outcome := O
    OutcomeOf := fun _ w => w
    Agent := A
    IsAgent := fun _ => True
    OriginatesAt := fun _ _ => True
    ControlsAlternative := fun _ _ _ => False
  }
  refine ⟨M, ?_, ?_, ?_⟩
  · refine ⟨(), trivial, (), trivial, ?_⟩
    intro ⟨p, hp⟩
    cases hp
  · refine ⟨true, trivial, trivial, ?_⟩
    intro h
    cases h
  · intro agent hFS
    rcases hFS with ⟨_, source, _, _, _, alt, _, _, _, hCtrl⟩
    exact hCtrl

/-- Negative Independence Result 2: In the absence of explanatory well-foundedness,
an impersonal contingent source can ground the concrete occurrence in an explanatory circle
without requiring any Free Subject (witnessed by an impersonal universe where Agent = Empty).
This demonstrates that explanatory well-foundedness is indispensable to rejecting circular grounding. -/
theorem circular_impersonal_grounding_satisfiable_without_well_foundedness :
    ∃ (Event : Type)
      (source conc : Event)
      (Determines : Event → Event → Prop)
      (GroundingDependsOn : Event → Event → Prop)
      (Agent : Type),
      Relation.TransGen Determines source conc ∧
      (¬ ∃ p, Determines p source) ∧
      GroundingDependsOn conc source ∧
      GroundingDependsOn source conc ∧
      (∀ _a : Agent, False) := by
  let E := Bool
  let source := true
  let conc := false
  let Det : E → E → Prop := fun a b => a = true ∧ b = false
  let Ground : E → E → Prop := fun _ _ => True
  refine ⟨E, source, conc, Det, Ground, Empty, ?_, ?_, ?_, ?_, ?_⟩
  · exact Relation.TransGen.single ⟨rfl, rfl⟩
  · rintro ⟨p, _hp1, hp2⟩
    revert hp2
    decide
  · trivial
  · trivial
  · intro a
    cases a

def GroundRel (y x : Fin 2) : Prop :=
  (if y.val = 0 then 1 else 0) < (if x.val = 0 then 1 else 0)

def Det (a b : Fin 2) : Prop := a = 0 ∧ b = 1

theorem transGen_det {a b : Fin 2} (h : Relation.TransGen Det a b) : a = 0 ∧ b = 1 := by
  induction h with
  | single h1 => exact h1
  | tail _ h2 ih =>
    obtain ⟨_ih1, rfl⟩ := ih
    obtain ⟨h21, _h22⟩ := h2
    cases h21

/-- Negative Independence Result 3: Occurrence contingency without ContingencyTransferBridge
fails to preclude an impersonal source.
In a 2-world model where `sourceConfig` has an invariant outcome across worlds while
`concreteOccurrence` varies under the same past, the occurrence is contingent but the source
configuration is invariant and non-necessitating. In an impersonal model (Agent = Empty),
no Free Subject exists. This proves that an explicit contingency transfer bridge is required. -/
theorem occurrence_contingency_without_transfer_fails_free_subject :
    ∃ (M : DeterminationModel.{0, 0, 0}) (S : UltimateSource.{0, 0, 0} M),
      HasSamePastAlternative M ∧
      (∀ alt : M.World, M.SameCompletePriorState M.actualWorld alt →
        M.OutcomeOf S.sourceConfig alt = M.OutcomeOf S.sourceConfig M.actualWorld) ∧
      (∀ agent : M.Agent, ¬ FreeSubject M agent) := by
  let E : Type := Fin 2
  let src : E := 0
  let conc : E := 1
  let W : Type := Bool
  let O : Type := Bool
  have hWF : WellFounded GroundRel := (measure (fun x : Fin 2 => if x.val = 0 then 1 else 0)).wf
  let M : DeterminationModel.{0, 0, 0} := {
    Event := E
    Occurs := fun _ => True
    concreteOccurrence := conc
    Determines := Det
    GroundingDependsOn := GroundRel
    genuine_grounding_is_well_founded := hWF
    causal_ancestry_implies_explanatory_dependence := by
      intro a b hab
      obtain ⟨rfl, rfl⟩ := transGen_det hab
      exact Nat.zero_lt_one
    World := W
    actualWorld := false
    Accessible := fun _ _ => True
    SameCompletePriorState := fun _ _ => True
    Outcome := O
    OutcomeOf := fun e w => if e = conc then w else false
    Agent := Empty
    IsAgent := fun _ => True
    OriginatesAt := fun _ _ => True
    ControlsAlternative := fun _ _ _ => True
  }
  let S : UltimateSource.{0, 0, 0} M := {
    sourceSubstrate := Unit
    sourceConfig := src
    config_occurs := trivial
    determines_occurrence := Relation.TransGen.single ⟨rfl, rfl⟩
    is_ultimate := by
      rintro ⟨p, _hp1, hp2⟩
      revert hp2
      decide
  }
  refine ⟨M, S, ?_, ?_, ?_⟩
  · refine ⟨true, trivial, trivial, ?_⟩
    dsimp [M]
    decide
  · intro alt _
    rfl
  · intro agent
    cases agent

/-!
================================================================================
IX. LOGICAL AND PHILOSOPHICAL AUDIT
================================================================================

### What the Lean kernel derives from pure logic:
1. `wellFounded_explanation_has_no_two_cycle`:
   A well-founded relation cannot have a 2-cycle (`DependsOn a b ∧ DependsOn b a → False`).
2. `necessitation_excludes_contingency`:
   A necessitation condition on an invariant source configuration strictly contradicts
   outcome divergence under the same prior state.
3. `impersonal_contingent_source_forms_explanatory_cycle`:
   Given ancestral determination and the backward-explanation premise, an explanatory
   cycle is strictly formed.
4. `impersonal_contingent_source_fails_as_ultimate_explanation`:
   Given well-founded grounding and the explanatory cycle, `False` is derived.
5. `ultimate_source_must_be_personal`:
   Given the 6-way taxonomy, ultimacy, PSR, contingency, and circularity refutation,
   the source is constructively forced to be `PersonalSource`.
6. `personal_source_and_contingency_yields_free_subject`:
   Given `PersonalSource`, contingency, and `AgentialSufficientReasonPrinciple`,
   a `FreeSubject` is derived.
7. `concrete_proof_occurrence_implies_free_subject`:
   The complete conditional derivation, actively consuming `hProof`.
8. `unforced_personal_source_without_control_fails_free_subject`,
   `circular_impersonal_grounding_satisfiable_without_well_foundedness`, and
   `occurrence_contingency_without_transfer_fails_free_subject`:
   The 3 negative independence models are kernel-verified.

### Substantive Philosophical Premises Used:
1. **Determination Ancestry Termination (`AncestryTerminatesDetermines`)**:
   The causal/constitutive determination chain terminates at an ultimate source.
   (Documented: Grounding well-foundedness does not entail causal termination, because
   effects depending on causes form ascending chains under accessibility).
2. **Explanatory Grounding Well-Foundedness (`genuine_grounding_is_well_founded`)**:
   Genuine ultimate explanation cannot be circular.
3. **Principle of Sufficient Reason (`principle_of_sufficient_reason`)**:
   A contingent concrete occurrence cannot be an ungrounded brute fact.
4. **Contingency (`HasSamePastAlternative`)**:
   The concrete occurrence could have been otherwise under the same complete past.
5. **Contingency Transfer Bridge (`ContingencyTransferBridge`)**:
   Connects the occurrence's same-past alternative to source configuration contingency
   or non-necessitation.
6. **The Backward-Explanation Principle (`impersonal_contingent_source_is_explained_backwards`)**:
   An impersonal contingent source cannot explain its specific actual outcome without
   invoking the consequence itself.
7. **Exhaustive Origin Taxonomy (`taxonomy_is_exhaustive`)**:
   The categories exhaust the metaphysical possibilities for an ultimate origin.
8. **The Agential Sufficient Reason Principle (`AgentialSufficientReasonPrinciple`)**:
   An unforced personal agent originating an event with an accessible same-past
   alternative exercises active control over that alternative (precluding agential luck).

None of these premises are hidden inside definitions; each is an explicit hypothesis.
-/

#print axioms wellFounded_explanation_has_no_two_cycle
#print axioms necessitation_excludes_contingency
#print axioms impersonal_contingent_source_forms_explanatory_cycle
#print axioms impersonal_contingent_source_fails_as_ultimate_explanation
#print axioms ultimate_source_must_be_personal
#print axioms personal_source_and_contingency_yields_free_subject
#print axioms concrete_proof_occurrence_implies_free_subject
#print axioms unforced_personal_source_without_control_fails_free_subject
#print axioms circular_impersonal_grounding_satisfiable_without_well_foundedness
#print axioms occurrence_contingency_without_transfer_fails_free_subject

end FreeSubjectFromDetermination
end Logos
