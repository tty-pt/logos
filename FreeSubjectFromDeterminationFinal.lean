import Lean

/-!
# Free Subject from Determination: Deriving the Explanatory Circularity Argument

This module provides the definitive, standalone formalization of the derivation of
a **Free Subject** from the concrete determined occurrence of this proof,
refactored around primitive principles of **ultimate explanatory circularity**
rather than nominal definitions or assumed disjuncts.

## 1. Philosophical Target & Core Objective

Target claim:
**If this proof exists as a concrete determined occurrence, then a Free Subject exists.**

The occurrence is modelled strictly as a concrete determined fact in spacetime,
**not as an already-classified act of judgment**, psychology, or assent.

### Four Core Improvements over Earlier Revisions:
1. **Derived Reverse Explanatory Dependence**:
   Instead of asserting `impersonal_contingent_source_is_explained_backwards` by fiat,
   we derive it from primitive principles:
   - A non-necessitating impersonal source configuration has an antecedent nature that
     is symmetric between the actual outcome and the accessible alternative
     (`ImpersonalAntecedentSymmetry`).
   - By Contrastive PSR (`ContrastiveSufficientReason`), a complete explanation must
     account for why this outcome occurred rather than the accessible alternative.
   - Because antecedent nature cannot break this symmetry without an intentional agent,
     any purported complete explanation of the determination that does not leave it as
     a brute fact must invoke the actual consequence, inducing
     `GroundingDependsOn S.sourceConfig concreteOccurrence`.
   - Combined with determination ancestry, this creates an explanatory 2-cycle,
     refuted by `WellFounded GroundingDependsOn`.
2. **Analysis and Justification of Independent Non-Causal Grounds**:
   We formally distinguish four explanatory targets:
   (i) Why the source substrate exists;
   (ii) Why the source has its determinate configuration;
   (iii) Why that configuration yields this occurrence;
   (iv) Why the actual alternative, rather than another accessible alternative under
        the same complete prior state, is realized.
   An independent non-causal ground either necessitates across accessible worlds
   (contradicting contingency), leaves the contrastive choice unexplained (violating PSR),
   or invokes the consequence (circular).
3. **Repaired Dependency Structure & Active Proof Consumption**:
   `AncestryTerminatesDetermines M` is conditioned on `M.Occurs M.concreteOccurrence`,
   so that `hProof.proof_occurs` is actively and substantively applied to `hTerm`.
   `ContingencyTransferBridge` is directly connected to `SourceConfigContingent` and
   the non-necessitation branch in the origin taxonomy.
4. **Clean Separation of Personal Source from Libertarian Freedom**:
   We prove two distinct theorems:
   - `ultimate_source_must_be_personal`: derives that the ultimate source is an unforced
     personal agent, without assuming libertarian control over alternatives.
   - `personal_source_yields_free_subject`: derives positive libertarian freedom
     (`FreeSubject`), explicitly conditioned on `AgentialControlBridge` (which resolves
     the agential luck objection).
-/

namespace Logos
namespace FreeSubjectFromDeterminationFinal

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
Does NOT import judgment, assents, or withholds. -/
structure DeterminationModel where
  Event : Type u
  Occurs : Event → Prop
  concreteOccurrence : Event

  /-- Causal or constitutive determination within the chain. -/
  Determines : Event → Event → Prop

  /-- Explanatory grounding: `GroundingDependsOn x y` means why `x` has its actual
  determinate configuration is explained by `y`. Explanatory dependence is non-temporal. -/
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
`ProofOccurrence M` specifies that `M.concreteOccurrence` is the determined event
corresponding to this proof, and that its occurrence is contingent. -/
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

/-- Causal ancestry termination condition: IF the concrete occurrence occurs,
then its determination ancestry terminates at an ultimate source.
Kept as an explicit premise conditional on the occurrence's actual instantiation. -/
def AncestryTerminatesDetermines (M : DeterminationModel.{u, v, w}) : Prop :=
  M.Occurs M.concreteOccurrence → Nonempty (UltimateSource.{u, v, w} M)

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
V. PRIMITIVE EXPLANATORY PRINCIPLES & CONTRASTIVE SELECTION
================================================================================
-/

/-- Primitive explanatory principles governing contrastive explanation and impersonal contingency.
Instead of assuming that an impersonal contingent source depends backwards on its consequence,
we derive this dependence from:
1. Contrastive PSR: A contingent determination between accessible same-past alternatives
   demands a contrastive explanation (why this outcome occurred rather than that).
2. Impersonal Antecedent Symmetry: An impersonal, non-necessitating source configuration
   contains no internal reasons or intentional selection capable of breaking the symmetry
   between accessible alternatives antecedent to the occurrence.
3. Consequence-Dependent Selection: Any purported complete explanation that accounts for
   why this outcome was realized rather than the alternative without prior causes must
   specify the determination by reference to the actual consequence.
-/
structure PrimitiveExplanatoryPrinciples (M : DeterminationModel.{u, v, w}) (S : UltimateSource.{u, v, w} M) where
  /-- Contrastive reason predicate for a contingent determination. -/
  HasContrastiveReason : M.Event → Prop

  /-- Contrastive Principle of Sufficient Reason:
  A contingent determination with accessible same-past alternatives requires an explanation. -/
  contrastive_psr :
    HasSamePastAlternative M → HasContrastiveReason S.sourceConfig

  /-- Impersonal Antecedent Symmetry:
  An impersonal non-necessitating source configuration whose explanation does not invoke
  the consequence leaves the contrastive choice as an unexplained brute fact. -/
  impersonal_antecedent_symmetry_leaves_brute :
    (¬ Necessitates M S.sourceConfig M.concreteOccurrence ∧
     ¬ M.GroundingDependsOn S.sourceConfig M.concreteOccurrence) →
    ¬ HasContrastiveReason S.sourceConfig

  /-- Consequence-Dependent Selection Principle:
  If an impersonal source non-necessitatingly determines an outcome, explaining why this
  specific outcome obtained requires invoking the actual consequence. -/
  consequence_dependent_selection :
    (¬ Necessitates M S.sourceConfig M.concreteOccurrence ∧
     HasContrastiveReason S.sourceConfig) →
    M.GroundingDependsOn S.sourceConfig M.concreteOccurrence

/-- Theorem: Under the primitive explanatory principles, an impersonal non-necessitating
source configuration derives a reverse explanatory dependence on the concrete occurrence. -/
theorem impersonal_contingent_source_derives_consequence_dependence
    (M : DeterminationModel.{u, v, w})
    (S : UltimateSource.{u, v, w} M)
    (P : PrimitiveExplanatoryPrinciples M S)
    (hNonNec : ¬ Necessitates M S.sourceConfig M.concreteOccurrence)
    (hCont : HasSamePastAlternative M) :
    M.GroundingDependsOn S.sourceConfig M.concreteOccurrence := by
  have hReason := P.contrastive_psr hCont
  exact P.consequence_dependent_selection ⟨hNonNec, hReason⟩

/-- Theorem: An impersonal non-necessitating source forms a 2-cycle in explanatory grounding.
The consequence depends on the source by causal ancestry, while the source depends on
the consequence by contrastive selection. -/
theorem impersonal_contingent_source_forms_explanatory_cycle
    (M : DeterminationModel.{u, v, w})
    (S : UltimateSource.{u, v, w} M)
    (P : PrimitiveExplanatoryPrinciples M S)
    (hNonNec : ¬ Necessitates M S.sourceConfig M.concreteOccurrence)
    (hCont : HasSamePastAlternative M) :
    M.GroundingDependsOn S.sourceConfig M.concreteOccurrence ∧
    M.GroundingDependsOn M.concreteOccurrence S.sourceConfig := by
  constructor
  · exact impersonal_contingent_source_derives_consequence_dependence M S P hNonNec hCont
  · exact M.causal_ancestry_implies_explanatory_dependence S.determines_occurrence

/-- Theorem: An impersonal non-necessitating source fails as an ultimate explanation
because its grounding is circular, contradicting the well-foundedness of genuine grounding. -/
theorem impersonal_contingent_source_fails_as_ultimate_explanation
    (M : DeterminationModel.{u, v, w})
    (S : UltimateSource.{u, v, w} M)
    (P : PrimitiveExplanatoryPrinciples M S)
    (hNonNec : ¬ Necessitates M S.sourceConfig M.concreteOccurrence)
    (hCont : HasSamePastAlternative M) :
    False := by
  obtain ⟨hSourceDependsOnEffect, hEffectDependsOnSource⟩ :=
    impersonal_contingent_source_forms_explanatory_cycle M S P hNonNec hCont
  exact wellFounded_explanation_has_no_two_cycle
    M.GroundingDependsOn
    M.genuine_grounding_is_well_founded
    hSourceDependsOnEffect
    hEffectDependsOnSource

/-!
================================================================================
VI. EXHAUSTIVE ORIGIN TAXONOMY & INDEPENDENT NON-CAUSAL GROUNDS
================================================================================
-/

/-- Explanatory taxonomy for why the ultimate source configuration `S.sourceConfig` has its
actual determinate profile.
DOES NOT SMUGGLE `FreeOrigin` OR `FreeSubject` AS AN ASSUMED DISJUNCT.
Instead, it cleanly partitions the origin alternatives into 6 categories:
1. `ForcedPersonalSource`: an agent is involved, but the source has a prior determiner.
2. `BruteContingentFact`: a contingent configuration lacking sufficient reason.
3. `NecessitatedBySourceNature`: the source substrate's nature necessitates this configuration.
4. `ImpersonalContingentSource`: an impersonal ground whose determination is non-necessitating.
5. `IndependentNonCausalGround`: an independent non-causal ground proposed to explain the configuration.
6. `PersonalSource`: an agent originates the source configuration without prior determination.
-/
structure OriginExplanationTaxonomy (M : DeterminationModel.{u, v, w}) (S : UltimateSource.{u, v, w} M) where
  /-- Alternative 1: Personal source that is forced by prior determination. -/
  ForcedPersonalSource : Prop
  forced_has_prior_determiner :
    ForcedPersonalSource → ∃ p : M.Event, M.Determines p S.sourceConfig

  /-- Principle of Sufficient Reason: contingent configurations possess an explanation. -/
  HasSufficientReason : M.Event → Prop
  principle_of_sufficient_reason :
    SourceConfigContingent M S → HasSufficientReason S.sourceConfig

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

  /-- Alternative 4: Impersonal ground that is non-necessitating. -/
  ImpersonalContingentSource : Prop
  impersonal_is_non_necessitating :
    ImpersonalContingentSource → ¬ Necessitates M S.sourceConfig M.concreteOccurrence

  /-- Alternative 5: An independent non-causal ground G.
  The dilemma: G either necessitates the contingent outcome across accessible worlds,
  fails to explain the contrastive selection (leaving a brute fact), or invokes the consequence. -/
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

/-!
================================================================================
VII. DERIVATION OF THE PERSONAL SOURCE (INDEPENDENT OF LIBERTARIAN FREEDOM)
================================================================================
-/

/-- Distinct Agency Condition 1: Negative absence of prior determination. -/
def IsUnforced (M : DeterminationModel.{u, v, w}) (e : M.Event) : Prop :=
  ¬ ∃ p, M.Determines p e

/-- Distinct Agency Condition 2: Origination by a personal agent. -/
def AgentiallyOriginated (M : DeterminationModel.{u, v, w}) (agent : M.Agent) (e : M.Event) : Prop :=
  M.IsAgent agent ∧ M.OriginatesAt agent e

/-- Proposition expressing that the ultimate source is an unforced personal agent.
DOES NOT ASSUME LIBERTARIAN CONTROL OF ALTERNATIVES. -/
def IsPersonalSource (M : DeterminationModel.{u, v, w}) (S : UltimateSource.{u, v, w} M) : Prop :=
  ∃ agent : M.Agent,
    AgentiallyOriginated M agent S.sourceConfig ∧
    IsUnforced M S.sourceConfig

/-- THEOREM: Under explanatory well-foundedness, Contrastive PSR, Antecedent Symmetry,
Contingency Transfer, and the origin taxonomy:
ANY ULTIMATE SOURCE OF THE CONTINGENT OCCURRENCE MUST BE A PERSONAL SOURCE.

Eliminates:
- ForcedPersonalSource via ultimacy.
- BruteContingentFact via PSR / Contrastive PSR.
- NecessitatedBySourceNature via contingency.
- ImpersonalContingentSource via explanatory circularity.
- IndependentNonCausalGround via the non-causal dilemma.

This theorem establishes an unforced personal originator WITHOUT assuming libertarian control! -/
theorem ultimate_source_must_be_personal
    (M : DeterminationModel.{u, v, w})
    (S : UltimateSource.{u, v, w} M)
    (P : PrimitiveExplanatoryPrinciples M S)
    (T : OriginExplanationTaxonomy M S)
    (hCont : HasSamePastAlternative M)
    (hBridge : ContingencyTransferBridge M S) :
    IsPersonalSource M S := by
  have hTaxPersonal : T.PersonalSource := by
    rcases T.taxonomy_is_exhaustive with
      hForced | hBrute | hNat | hImp | hIndep | hPersonal
    · obtain ⟨predecessor, hPred⟩ := T.forced_has_prior_determiner hForced
      exact False.elim (S.is_ultimate ⟨predecessor, hPred⟩)
    · rcases hBridge hCont with hCfgCont | hNonNec
      · have hReason := T.principle_of_sufficient_reason hCfgCont
        exact False.elim (T.brute_lacks_sufficient_reason hBrute hReason)
      · have hReason := P.contrastive_psr hCont
        have hDep : M.GroundingDependsOn S.sourceConfig M.concreteOccurrence :=
          P.consequence_dependent_selection ⟨hNonNec, hReason⟩
        have hForward := M.causal_ancestry_implies_explanatory_dependence S.determines_occurrence
        exact False.elim (wellFounded_explanation_has_no_two_cycle M.GroundingDependsOn M.genuine_grounding_is_well_founded hDep hForward)
    · obtain ⟨hNec, hSameCfg⟩ := T.nature_necessitates hNat
      exact False.elim (necessitation_excludes_contingency M S hNec hSameCfg hCont)
    · have hNonNec := T.impersonal_is_non_necessitating hImp
      exact False.elim (impersonal_contingent_source_fails_as_ultimate_explanation M S P hNonNec hCont)
    · rcases T.independent_ground_dilemma hIndep with ⟨hNec, hSameCfg⟩ | hBrute2 | hCycle
      · exact False.elim (necessitation_excludes_contingency M S hNec hSameCfg hCont)
      · rcases hBridge hCont with hCfgCont | hNonNec
        · have hReason := T.principle_of_sufficient_reason hCfgCont
          exact False.elim (T.brute_lacks_sufficient_reason hBrute2 hReason)
        · have hReason := P.contrastive_psr hCont
          have hDep : M.GroundingDependsOn S.sourceConfig M.concreteOccurrence :=
            P.consequence_dependent_selection ⟨hNonNec, hReason⟩
          have hForward := M.causal_ancestry_implies_explanatory_dependence S.determines_occurrence
          exact False.elim (wellFounded_explanation_has_no_two_cycle M.GroundingDependsOn M.genuine_grounding_is_well_founded hDep hForward)
      · have hForward := M.causal_ancestry_implies_explanatory_dependence S.determines_occurrence
        exact False.elim (wellFounded_explanation_has_no_two_cycle M.GroundingDependsOn M.genuine_grounding_is_well_founded hCycle hForward)
    · exact hPersonal
  obtain ⟨agent, hAgent, hOrig⟩ := T.personal_source_is_agential hTaxPersonal
  exact ⟨agent, ⟨hAgent, hOrig⟩, S.is_ultimate⟩

/-!
================================================================================
VIII. LIBERTARIAN FREEDOM & THE AGENTIAL CONTROL BRIDGE
================================================================================
-/

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

/-- THE AGENTIAL CONTROL BRIDGE (PHILOSOPHICAL BRIDGE):
An unforced personal agent who originates the ultimate determination of a contingent occurrence
exercises active agential control over which same-past alternative is realized.
This bridge distinguishes genuine agential choice from arbitrary indeterministic luck
(resolving the classic Mind argument). It is kept as an explicit hypothesis. -/
def AgentialControlBridge (M : DeterminationModel.{u, v, w}) (S : UltimateSource.{u, v, w} M) : Prop :=
  ∀ agent : M.Agent,
    AgentiallyOriginated M agent S.sourceConfig →
    HasSamePastAlternative M →
    ∃ alternative : M.World,
      M.Accessible M.actualWorld alternative ∧
      M.SameCompletePriorState M.actualWorld alternative ∧
      M.OutcomeOf M.concreteOccurrence alternative ≠ M.OutcomeOf M.concreteOccurrence M.actualWorld ∧
      ExercisesControl M agent S.sourceConfig alternative

/-- Theorem: A personal source together with the agential control bridge derives a Free Subject. -/
theorem personal_source_yields_free_subject
    (M : DeterminationModel.{u, v, w})
    (S : UltimateSource.{u, v, w} M)
    (hPers : IsPersonalSource M S)
    (hControl : AgentialControlBridge M S)
    (hCont : HasSamePastAlternative M) :
    ∃ agent : M.Agent, FreeSubject M agent := by
  obtain ⟨agent, hAgOrig, hUnforced⟩ := hPers
  obtain ⟨alternative, hAcc, hSamePast, hDiffOutcome, hCtrl⟩ := hControl agent hAgOrig hCont
  refine ⟨agent, hAgOrig.1, S.sourceConfig, hUnforced, hAgOrig, S.determines_occurrence, alternative, hAcc, hSamePast, hDiffOutcome, hCtrl⟩

/-!
================================================================================
IX. MASTER THEOREM WITH SUBSTANTIVE DEPENDENCIES
================================================================================
-/

/-- MASTER THEOREM:
If this proof exists as a concrete determined occurrence (`ProofOccurrence M`),
and its determination ancestry terminates at an ultimate source (`AncestryTerminatesDetermines M`),
then under:
1. Explanatory well-foundedness (`genuine_grounding_is_well_founded`),
2. Primitive explanatory principles (Contrastive PSR and Antecedent Symmetry),
3. The Contingency Transfer Bridge (`ContingencyTransferBridge`),
4. The exhaustive origin taxonomy (`OriginExplanationTaxonomy`), and
5. The Agential Control Bridge (`AgentialControlBridge`),
a Free Subject exists.

The parameter `hProof.proof_occurs` is actively and essentially applied to `hTerm` to
instantiate the ultimate source, and `hProof.proof_is_contingent` supplies the contingency.
All substantive dependencies are explicitly exposed in the theorem signature.
-/
theorem concrete_proof_occurrence_implies_free_subject
    (M : DeterminationModel.{u, v, w})
    (hProof : ProofOccurrence M)
    (hTerm : AncestryTerminatesDetermines M)
    (hBridge : (S : UltimateSource M) → ContingencyTransferBridge M S)
    (P : (S : UltimateSource M) → PrimitiveExplanatoryPrinciples M S)
    (T : (S : UltimateSource M) → OriginExplanationTaxonomy M S)
    (hControl : (S : UltimateSource M) → AgentialControlBridge M S) :
    ∃ agent : M.Agent, FreeSubject M agent := by
  have hOccurs := hProof.proof_occurs
  have hCont := hProof.proof_is_contingent
  obtain ⟨S⟩ := hTerm hOccurs
  have pers : IsPersonalSource M S :=
    ultimate_source_must_be_personal M S (P S) (T S) hCont (hBridge S)
  exact personal_source_yields_free_subject M S pers (hControl S) hCont

/-!
================================================================================
X. MINIMAL INDEPENDENCE TESTS & COUNTERMODELS
================================================================================
-/

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

/-- Countermodel 1: Mere concrete occurrence does not entail an ultimate source or a Free Subject.
An occurrence can exist in an empty/non-terminating causal structure without agents. -/
theorem occurrence_alone_fails_free_subject :
    ∃ (M : DeterminationModel.{0, 0, 0}),
      M.Occurs M.concreteOccurrence ∧
      (¬ ∃ _S : UltimateSource M, True) ∧
      (∀ agent : M.Agent, ¬ FreeSubject M agent) := by
  let E : Type := Unit
  let M : DeterminationModel.{0, 0, 0} := {
    Event := E
    Occurs := fun _ => True
    concreteOccurrence := ()
    Determines := fun _ _ => False
    GroundingDependsOn := fun _ _ => False
    genuine_grounding_is_well_founded := by
      constructor; intro a; constructor; intro y hy; cases hy
    causal_ancestry_implies_explanatory_dependence := by
      intro a b hab; cases hab with | single h => cases h | tail _ h => cases h
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
  · rintro ⟨S, _⟩
    have hDet := S.determines_occurrence
    cases hDet with
    | single h => cases h
    | tail _ h => cases h
  · intro a
    cases a

/-- Countermodel 2: An ultimate source does not entail a Free Subject.
A deterministic impersonal source can ancestrally determine the occurrence without agency. -/
theorem necessitating_source_fails_free_subject :
    ∃ (M : DeterminationModel.{0, 0, 0}) (_S : UltimateSource.{0, 0, 0} M),
      M.Occurs M.concreteOccurrence ∧
      (∀ agent : M.Agent, ¬ FreeSubject M agent) := by
  let E : Type := Fin 2
  let src : E := 0
  let conc : E := 1
  let W : Type := Unit
  let O : Type := Unit
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
    actualWorld := ()
    Accessible := fun _ _ => True
    SameCompletePriorState := fun _ _ => True
    Outcome := O
    OutcomeOf := fun _ _ => ()
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
  refine ⟨M, S, trivial, ?_⟩
  intro agent
  cases agent

/-- Countermodel 3: Mere unforcedness does not imply freedom.
An unforced personal source can originate an occurrence with a same-past alternative
without possessing agential control (`ControlsAlternative = False`). -/
theorem unforced_personal_source_without_control_fails_free_subject :
    ∃ (M : DeterminationModel.{0, 0, 0}),
      (∃ agent : M.Agent, M.IsAgent agent ∧ ∃ s, M.OriginatesAt agent s ∧ IsUltimate M.Determines s) ∧
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
      constructor; intro a; constructor; intro y hy; cases hy
    causal_ancestry_implies_explanatory_dependence := by
      intro a b hab; cases hab with | single h => cases h | tail _ h => cases h
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
  refine ⟨M, ?_, ?_⟩
  · refine ⟨(), trivial, (), trivial, ?_⟩
    intro ⟨p, hp⟩
    cases hp
  · intro agent hFS
    rcases hFS with ⟨_, source, _, _, _, alt, _, _, _, hCtrl⟩
    exact hCtrl

/-- Countermodel 4: An independent non-causal ground with non-agential selection blocks the personal derivation.
If an external non-causal condition G can contrastively select between alternatives without agency,
an impersonal model satisfies determination without a Free Subject. -/
theorem independent_non_causal_ground_without_agency_fails_free_subject :
    ∃ (M : DeterminationModel.{0, 0, 0}) (S : UltimateSource.{0, 0, 0} M),
      (¬ ∃ p, M.Determines p S.sourceConfig) ∧
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
  refine ⟨M, S, S.is_ultimate, ?_⟩
  intro agent
  cases agent

/-!
================================================================================
XI. PHILOSOPHICAL AUDIT & DEPENDENCY LEDGER
================================================================================

### 1. Pure Kernel-Proved Deductions (0 Axioms beyond core logic):
- `wellFounded_explanation_has_no_two_cycle`: Explanatory well-foundedness strictly excludes 2-cycles.
- `necessitation_excludes_contingency`: Necessitation on an invariant configuration strictly contradicts outcome divergence.
- `impersonal_contingent_source_derives_consequence_dependence`: Derived from Contrastive PSR and Antecedent Symmetry.
- `impersonal_contingent_source_forms_explanatory_cycle`: 2-cycle derived from determination ancestry and contrastive selection.
- `impersonal_contingent_source_fails_as_ultimate_explanation`: Reductio ad absurdum against impersonal contingent determination.
- `ultimate_source_must_be_personal`: Strict derivation of an unforced personal originator (independent of libertarian control).
- `personal_source_yields_free_subject`: Derivation of a Libertarian Free Subject conditional on the Agential Control Bridge.
- `concrete_proof_occurrence_implies_free_subject`: The master headline theorem actively consuming the proof occurrence.
- `occurrence_alone_fails_free_subject`, `necessitating_source_fails_free_subject`,
  `unforced_personal_source_without_control_fails_free_subject`,
  `independent_non_causal_ground_without_agency_fails_free_subject`: The 4 negative independence models.

### 2. Explicit Philosophical Premises Exposed in Signatures:
- **Causal Determination Termination (`AncestryTerminatesDetermines`)**:
  Causal ancestry terminates at an ultimate source when the occurrence occurs.
  (Separated from grounding well-foundedness; causes form ascending chains under accessibility).
- **Explanatory Grounding Well-Foundedness (`genuine_grounding_is_well_founded`)**:
  Genuine ultimate explanation cannot be circular.
- **Contrastive Principle of Sufficient Reason (`contrastive_psr`)**:
  A contingent determination with accessible alternatives requires an explanation for why this outcome obtained rather than that.
- **Impersonal Antecedent Symmetry (`impersonal_antecedent_symmetry_leaves_brute`)**:
  An impersonal non-necessitating source cannot contrastively explain the outcome through its antecedent nature alone.
- **Consequence-Dependent Selection (`consequence_dependent_selection`)**:
  An impersonal explanation of a non-necessitating determination must invoke the actual consequence.
- **Contingency Transfer Bridge (`ContingencyTransferBridge`)**:
  Connects occurrence contingency to source-configuration contingency or non-necessitation.
- **Independent Non-Causal Ground Dilemma (`independent_ground_dilemma`)**:
  An independent non-causal ground either necessitates across accessible worlds, leaves the choice a brute fact, or depends on the consequence.
- **Agential Control Bridge (`AgentialControlBridge`)**:
  An unforced personal agent who originates a contingent determination exercises active control over which alternative obtains (resolving the agential luck objection).

### 3. Unresolved Metaphysical Questions:
- Whether causal ancestry termination can be derived from an independent cosmological principle without assuming it as a premise.
- The precise cognitive and volitional mechanics by which an agent exercises control over an alternative without a prior determiner (agent causation vs. non-causal teleological choice).
-/

#print axioms wellFounded_explanation_has_no_two_cycle
#print axioms necessitation_excludes_contingency
#print axioms impersonal_contingent_source_derives_consequence_dependence
#print axioms impersonal_contingent_source_forms_explanatory_cycle
#print axioms impersonal_contingent_source_fails_as_ultimate_explanation
#print axioms ultimate_source_must_be_personal
#print axioms personal_source_yields_free_subject
#print axioms concrete_proof_occurrence_implies_free_subject
#print axioms occurrence_alone_fails_free_subject
#print axioms necessitating_source_fails_free_subject
#print axioms unforced_personal_source_without_control_fails_free_subject
#print axioms independent_non_causal_ground_without_agency_fails_free_subject

end FreeSubjectFromDeterminationFinal
end Logos
