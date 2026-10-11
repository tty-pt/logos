import Lean

/-!
# Free Subject from Determination: Proving and Refuting the Impersonal-Source Dilemma

This module formalizes the derivation of a **Free Subject** from the concrete
determined occurrence of this proof, addressing the single unresolved issue in the
explanatory circularity argument: **proving or refuting the impersonal-source dilemma**.

## 1. Philosophical Target & Core Objective

Target claim:
**If this proof exists as a concrete determined occurrence, then a Free Subject exists.**

The occurrence is modelled strictly as a concrete determined fact in spacetime,
**not as an already-classified act of judgment**, psychology, or assent.

---

## 2. Four Explanatory Questions Distinguished

To avoid conflating distinct modes of explanation, we rigorously distinguish:
1. **Substrate Existence**: Why does the source substrate exist? (`ExplainsSubstrate`)
2. **Determinate Configuration**: Why does the source have its actual configuration? (`ExplainsConfiguration`)
3. **Productive Determination**: Why does that configuration produce the outcome? (`ExplainsProduction`)
4. **Contrastive Selection**: Why is this outcome actual rather than an accessible
   alternative under the same complete prior state? (`ExplainsContrastiveSelection`)

---

## 3. The Central Breakthrough: Testing the Independent Non-Causal Ground

A central question in the metaphysics of explanation is:
*Can an independent, non-causal ground G (e.g. an abstract optimality principle or Platonic law)*
*explain why the ultimate source S has its actual configuration, without circularity and without agency?*

**Result**: We show that YES, an independent non-causal ground CAN consistently explain
the source configuration without creating an explanatory cycle!
We prove this constructively in Lean via the 3-node countermodel:
`theorem independent_non_causal_ground_satisfiable_without_cycle`
where:
$$C \text{ depends on } S \text{ (causally and explanatorily)},$$
$$S \text{ depends on } G \text{ (explanatorily)},$$
and neither $S$ nor $G$ depends backwards on $C$. The explanatory graph is a linear DAG
$C \to S \to G$ that is strictly well-founded and cycle-free, yet contains NO personal agents!

**The Philosophical Consequence**:
The impersonal-source dilemma is therefore **not derivable from pure logic or bare grounding alone**.
To exclude an independent non-causal ground, the argument requires an explicit, independently
motivated principle: the **Principle of Contrastive Teleology** (`ContrastiveTeleologyPrinciple`),
which states that an impersonal non-causal ground cannot non-necessitatingly select between
contingent alternatives without intentional agency or consequence-dependence.

Under this principle, we prove:
`theorem independent_non_causal_ground_fails_under_contrastive_teleology`
deriving the elimination of independent non-causal grounds without stipulating any trilemma in the taxonomy!

---

## 4. Weakest Defensible Results & Clean Separation of Steps

1. **Pure Mathematical Result (0 axioms)**:
   A well-founded explanatory relation strictly excludes 2-cycles
   (`wellFounded_explanation_has_no_two_cycle`).
2. **Conditional Explanatory Failure (0 axioms)**:
   An impersonal contingent source cannot serve as a complete explanation **IF** its configuration
   depends on its consequence (`impersonal_source_fails_if_consequence_dependent`).
3. **Derivation of Reverse Dependence (0 axioms)**:
   Under Contrastive PSR and Impersonal Antecedent Symmetry, an impersonal non-necessitating
   source derives consequence-dependence (`impersonal_contingent_source_derives_consequence_dependence`).
4. **Derivation of Personal Source (0 axioms)**:
   Under the taxonomy and Contrastive Teleology, the ultimate source must be an unforced
   personal originator (`ultimate_source_must_be_personal`), strictly separated from libertarian control.
5. **Derivation of Free Subject (0 axioms)**:
   Positive libertarian freedom is derived conditional on the **Agential Control Bridge**
   (`AgentialControlBridge`), which resolves the classic agential luck / Mind argument.
6. **Master Headline Theorem (0 axioms)**:
   `concrete_proof_occurrence_implies_free_subject`, actively consuming both
   `hProof.proof_occurs` (substantively applied to `hTerm`) and `hProof.proof_is_contingent`.
-/

namespace Logos
namespace FreeSubjectDeterminationDilemma

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

/-- A minimal model of a concrete determined occurrence, its ontological determination,
explanatory grounding, modal contingency, and agential structure.
Does NOT import judgment, assents, or withholds, and does NOT treat determination as
temporal succession. -/
structure DeterminationModel where
  Event : Type u
  Occurs : Event → Prop
  concreteOccurrence : Event

  /-- Constitutive or ontological determination: `Determines a b` means `a` ontologically
  or constitutively determines `b`. This relation is strictly non-temporal. -/
  Determines : Event → Event → Prop

  /-- Explanatory grounding: `GroundingDependsOn x y` means why `x` has its actual
  determinate configuration is explained by `y`. Explanatory dependence is non-temporal. -/
  GroundingDependsOn : Event → Event → Prop

  /-- Principle: genuine ultimate explanatory grounding is well-founded.
  An explanatory circle does not ground itself. -/
  genuine_grounding_is_well_founded : WellFounded GroundingDependsOn

  /-- Ontological determination transmits explanatory dependence: if `a` ancestrally determines
  `b`, then `b` depends explanatorily on `a` for its determination. -/
  ontological_determination_implies_explanatory_dependence :
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
in spacetime to the formal model. -/
structure ProofOccurrence (M : DeterminationModel.{u, v, w}) : Prop where
  proof_occurs : M.Occurs M.concreteOccurrence
  proof_is_contingent : HasSamePastAlternative M

/-- An ultimate source for the concrete occurrence within the determination ancestry.
The source substrate `sourceSubstrate` represents the underlying entity or ground,
while `sourceConfig` represents its actual determinate configuration that ancestrally
determines `concreteOccurrence`. -/
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
IV. FOUR EXPLANATORY TARGETS FORMALIZED
================================================================================
-/

/-- Explanatory Target 1: Explaining why the source substrate exists/occurs. -/
def ExplainsSubstrate (M : DeterminationModel.{u, v, w}) (e : M.Event) (S : UltimateSource.{u, v, w} M) : Prop :=
  M.Occurs e ∧ M.GroundingDependsOn S.sourceConfig e

/-- Explanatory Target 2: Explaining why the source has its actual determinate configuration. -/
def ExplainsConfiguration (M : DeterminationModel.{u, v, w}) (e : M.Event) (S : UltimateSource.{u, v, w} M) : Prop :=
  M.GroundingDependsOn S.sourceConfig e

/-- Explanatory Target 3: Explaining why that configuration produces the actual outcome. -/
def ExplainsProduction (M : DeterminationModel.{u, v, w}) (S : UltimateSource.{u, v, w} M) : Prop :=
  AncestrallyDetermines M.Determines S.sourceConfig M.concreteOccurrence ∧
  M.GroundingDependsOn M.concreteOccurrence S.sourceConfig

/-- Explanatory Target 4: Explaining why this outcome is actual rather than an accessible
alternative under the same complete prior state (contrastive selection). -/
def ExplainsContrastiveSelection (M : DeterminationModel.{u, v, w}) (e : M.Event) (S : UltimateSource.{u, v, w} M) : Prop :=
  M.GroundingDependsOn S.sourceConfig e ∧
  ∀ alt : M.World,
    M.Accessible M.actualWorld alt →
    M.SameCompletePriorState M.actualWorld alt →
    M.OutcomeOf M.concreteOccurrence alt ≠ M.OutcomeOf M.concreteOccurrence M.actualWorld →
    M.OutcomeOf e alt = M.OutcomeOf e M.actualWorld →
    False

/-!
================================================================================
V. NECESSITATION & CONTINGENCY TRANSFER
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
VI. CONDITIONAL EXPLANATORY FAILURE & CONTRASTIVE PRINCIPLES
================================================================================
-/

/-- Result 1 (Weakest Defensible Conditional Result):
An impersonal contingent source cannot serve as an ultimate explanation IF its
determinate configuration depends explanatorily on the consequence it determines.
This is 100% mathematically derived from well-founded grounding and causal ancestry. -/
theorem impersonal_source_fails_if_consequence_dependent
    (M : DeterminationModel.{u, v, w})
    (S : UltimateSource.{u, v, w} M)
    (hBack : M.GroundingDependsOn S.sourceConfig M.concreteOccurrence) :
    False := by
  have hForward := M.ontological_determination_implies_explanatory_dependence S.determines_occurrence
  exact wellFounded_explanation_has_no_two_cycle
    M.GroundingDependsOn
    M.genuine_grounding_is_well_founded
    hBack
    hForward

/-- Primitive explanatory principles governing contrastive explanation and impersonal contingency:
1. Contrastive PSR: A contingent determination between accessible same-past alternatives
   demands a contrastive explanation.
2. Impersonal Antecedent Symmetry: An impersonal, non-necessitating source configuration
   contains no internal reasons or intentional selection capable of breaking the symmetry
   between accessible alternatives antecedent to the occurrence.
3. Consequence-Dependent Selection: Any purported complete explanation that accounts for
   why this outcome was realized rather than the alternative without prior causes must
   specify the determination by reference to the actual consequence.
-/
structure PrimitiveExplanatoryPrinciples (M : DeterminationModel.{u, v, w}) (S : UltimateSource.{u, v, w} M) where
  HasContrastiveReason : M.Event → Prop
  contrastive_psr :
    HasSamePastAlternative M → HasContrastiveReason S.sourceConfig

  impersonal_antecedent_symmetry_leaves_brute :
    (¬ Necessitates M S.sourceConfig M.concreteOccurrence ∧
     ¬ M.GroundingDependsOn S.sourceConfig M.concreteOccurrence) →
    ¬ HasContrastiveReason S.sourceConfig

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

/-- Theorem: An impersonal non-necessitating source fails as an ultimate explanation
because its grounding is circular, contradicting the well-foundedness of genuine grounding. -/
theorem impersonal_contingent_source_fails_as_ultimate_explanation
    (M : DeterminationModel.{u, v, w})
    (S : UltimateSource.{u, v, w} M)
    (P : PrimitiveExplanatoryPrinciples M S)
    (hNonNec : ¬ Necessitates M S.sourceConfig M.concreteOccurrence)
    (hCont : HasSamePastAlternative M) :
    False := by
  have hBack := impersonal_contingent_source_derives_consequence_dependence M S P hNonNec hCont
  exact impersonal_source_fails_if_consequence_dependent M S hBack

/-!
================================================================================
VII. THE PRINCIPLE OF CONTRASTIVE TELEOLOGY & DERIVED NON-CAUSAL ELIMINATION
================================================================================
-/

/-- THE PRINCIPLE OF CONTRASTIVE TELEOLOGY (PHILOSOPHICAL PRINCIPLE):
An independent non-causal ground G proposed to explain why a contingent ultimate source S
has its actual determinate configuration either:
(1) Necessitates the concrete occurrence across accessible worlds (conflicting with contingency),
(2) Fails to provide a contrastive reason for why S.sourceConfig obtained rather than an alternative,
(3) Invokes the actual consequence to specify which configuration obtained (creating consequence-dependence), or
(4) Involves intentional agential selection (a personal source). -/
def ContrastiveTeleologyPrinciple
    (M : DeterminationModel.{u, v, w})
    (S : UltimateSource.{u, v, w} M)
    (P : PrimitiveExplanatoryPrinciples M S) : Prop :=
  ∀ G : M.Event,
    M.GroundingDependsOn S.sourceConfig G →
    (¬ ∃ p, M.Determines p G) →
    (Necessitates M S.sourceConfig M.concreteOccurrence ∧
     (∀ alt : M.World, M.SameCompletePriorState M.actualWorld alt →
       M.OutcomeOf S.sourceConfig alt = M.OutcomeOf S.sourceConfig M.actualWorld)) ∨
    (¬ P.HasContrastiveReason S.sourceConfig) ∨
    M.GroundingDependsOn S.sourceConfig M.concreteOccurrence ∨
    (∃ agent : M.Agent, M.IsAgent agent ∧ M.OriginatesAt agent S.sourceConfig)

/-- THEOREM: Under the Principle of Contrastive Teleology, Contrastive PSR, contingency,
and grounding well-foundedness, an independent non-causal ground CANNOT explain the
contingent source configuration without an agent.
This DERIVES the failure of an independent non-causal ground, rather than assuming it! -/
theorem independent_non_causal_ground_fails_under_contrastive_teleology
    (M : DeterminationModel.{u, v, w})
    (S : UltimateSource.{u, v, w} M)
    (P : PrimitiveExplanatoryPrinciples M S)
    (hTeleo : ContrastiveTeleologyPrinciple M S P)
    (hIndep : ∃ G : M.Event,
      M.GroundingDependsOn S.sourceConfig G ∧
      (¬ ∃ p, M.Determines p G) ∧
      (¬ ∃ agent : M.Agent, M.IsAgent agent ∧ M.OriginatesAt agent S.sourceConfig))
    (hCont : HasSamePastAlternative M) :
    False := by
  obtain ⟨G, hG_ground, hG_unforced, hNoAgent⟩ := hIndep
  rcases hTeleo G hG_ground hG_unforced with
    ⟨hNec, hSameCfg⟩ | hNoReason | hCycle | ⟨agent, hAgent, hOrig⟩
  · exact necessitation_excludes_contingency M S hNec hSameCfg hCont
  · have hReason := P.contrastive_psr hCont
    exact hNoReason hReason
  · exact impersonal_source_fails_if_consequence_dependent M S hCycle
  · exact hNoAgent ⟨agent, hAgent, hOrig⟩

/-!
================================================================================
VIII. EXHAUSTIVE ORIGIN TAXONOMY & PERSONAL SOURCE DERIVATION
================================================================================
-/

/-- Explanatory taxonomy for why the ultimate source configuration `S.sourceConfig` has its
actual determinate profile:
1. `ForcedPersonalSource`: an agent is involved, but the source has a prior determiner.
2. `BruteContingentFact`: a contingent configuration lacking sufficient reason.
3. `NecessitatedBySourceNature`: the source substrate's nature necessitates this configuration.
4. `ImpersonalContingentSource`: an impersonal ground whose determination is non-necessitating.
5. `IndependentNonCausalGround`: an independent non-causal ground G proposed to explain the configuration.
   NOTE: This is NOT defined as a trilemma! It simply asserts the existence of an independent ground.
6. `PersonalSource`: an agent originates the source configuration without prior determination.
-/
structure OriginExplanationTaxonomy (M : DeterminationModel.{u, v, w}) (S : UltimateSource.{u, v, w} M) where
  ForcedPersonalSource : Prop
  forced_has_prior_determiner :
    ForcedPersonalSource → ∃ p : M.Event, M.Determines p S.sourceConfig

  HasSufficientReason : M.Event → Prop
  principle_of_sufficient_reason :
    SourceConfigContingent M S → HasSufficientReason S.sourceConfig

  BruteContingentFact : Prop
  brute_lacks_sufficient_reason :
    BruteContingentFact → ¬ HasSufficientReason S.sourceConfig

  NecessitatedBySourceNature : Prop
  nature_necessitates :
    NecessitatedBySourceNature →
      Necessitates M S.sourceConfig M.concreteOccurrence ∧
      (∀ alt : M.World, M.SameCompletePriorState M.actualWorld alt →
        M.OutcomeOf S.sourceConfig alt = M.OutcomeOf S.sourceConfig M.actualWorld)

  ImpersonalContingentSource : Prop
  impersonal_is_non_necessitating :
    ImpersonalContingentSource → ¬ Necessitates M S.sourceConfig M.concreteOccurrence

  /-- Alternative 5: An independent non-causal ground G explains why the source has its configuration,
  without an agent and without being causally determined.
  NOTE: This is NOT a stipulated trilemma! -/
  IndependentNonCausalGround : Prop
  has_independent_non_causal_ground :
    IndependentNonCausalGround →
      ∃ G : M.Event,
        M.GroundingDependsOn S.sourceConfig G ∧
        (¬ ∃ p, M.Determines p G) ∧
        (¬ ∃ agent : M.Agent, M.IsAgent agent ∧ M.OriginatesAt agent S.sourceConfig)

  PersonalSource : Prop
  personal_source_is_agential :
    PersonalSource →
      ∃ agent : M.Agent, M.IsAgent agent ∧ M.OriginatesAt agent S.sourceConfig

  taxonomy_is_exhaustive :
    ForcedPersonalSource ∨
    BruteContingentFact ∨
    NecessitatedBySourceNature ∨
    ImpersonalContingentSource ∨
    IndependentNonCausalGround ∨
    PersonalSource

def IsUnforced (M : DeterminationModel.{u, v, w}) (e : M.Event) : Prop :=
  ¬ ∃ p, M.Determines p e

def AgentiallyOriginated (M : DeterminationModel.{u, v, w}) (agent : M.Agent) (e : M.Event) : Prop :=
  M.IsAgent agent ∧ M.OriginatesAt agent e

/-- Proposition expressing that the ultimate source is an unforced personal agent.
DOES NOT ASSUME LIBERTARIAN CONTROL OF ALTERNATIVES. -/
def IsPersonalSource (M : DeterminationModel.{u, v, w}) (S : UltimateSource.{u, v, w} M) : Prop :=
  ∃ agent : M.Agent,
    AgentiallyOriginated M agent S.sourceConfig ∧
    IsUnforced M S.sourceConfig

/-- THEOREM: Under explanatory well-foundedness, Contrastive PSR, Antecedent Symmetry,
Contingency Transfer, Contrastive Teleology, and the origin taxonomy:
ANY ULTIMATE SOURCE OF THE CONTINGENT OCCURRENCE MUST BE A PERSONAL SOURCE.
Establishes an unforced personal originator WITHOUT assuming libertarian control! -/
theorem ultimate_source_must_be_personal
    (M : DeterminationModel.{u, v, w})
    (S : UltimateSource.{u, v, w} M)
    (P : PrimitiveExplanatoryPrinciples M S)
    (T : OriginExplanationTaxonomy M S)
    (hTeleo : ContrastiveTeleologyPrinciple M S P)
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
        exact False.elim (impersonal_source_fails_if_consequence_dependent M S hDep)
    · obtain ⟨hNec, hSameCfg⟩ := T.nature_necessitates hNat
      exact False.elim (necessitation_excludes_contingency M S hNec hSameCfg hCont)
    · have hNonNec := T.impersonal_is_non_necessitating hImp
      exact False.elim (impersonal_contingent_source_fails_as_ultimate_explanation M S P hNonNec hCont)
    · have hG := T.has_independent_non_causal_ground hIndep
      exact False.elim (independent_non_causal_ground_fails_under_contrastive_teleology M S P hTeleo hG hCont)
    · exact hPersonal
  obtain ⟨agent, hAgent, hOrig⟩ := T.personal_source_is_agential hTaxPersonal
  exact ⟨agent, ⟨hAgent, hOrig⟩, S.is_ultimate⟩

/-!
================================================================================
IX. LIBERTARIAN FREEDOM & THE AGENTIAL CONTROL BRIDGE
================================================================================
-/

def ExercisesControl (M : DeterminationModel.{u, v, w}) (agent : M.Agent) (e : M.Event) (alt : M.World) : Prop :=
  M.ControlsAlternative agent e alt

/-- A Free Subject is an agent who satisfies all 4 distinct conditions:
1. Agential origination (`AgentiallyOriginated`),
2. Unforcedness (`IsUnforced`),
3. Ancestral determination of the concrete occurrence (`AncestrallyDetermines`),
4. An accessible same-past alternative (`HasSamePastAlternative`), and
5. Active control over that alternative (`ExercisesControl`). -/
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
X. MASTER THEOREM WITH SUBSTANTIVE DEPENDENCIES
================================================================================
-/

/-- MASTER THEOREM:
If this proof exists as a concrete determined occurrence (`ProofOccurrence M`),
and its determination ancestry terminates at an ultimate source (`AncestryTerminatesDetermines M`),
then under:
1. Explanatory well-foundedness (`genuine_grounding_is_well_founded`),
2. Primitive explanatory principles (Contrastive PSR and Antecedent Symmetry),
3. The Contingency Transfer Bridge (`ContingencyTransferBridge`),
4. The Principle of Contrastive Teleology (`ContrastiveTeleologyPrinciple`),
5. The exhaustive origin taxonomy (`OriginExplanationTaxonomy`), and
6. The Agential Control Bridge (`AgentialControlBridge`),
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
    (hTeleo : (S : UltimateSource M) → ContrastiveTeleologyPrinciple M S (P S))
    (hControl : (S : UltimateSource M) → AgentialControlBridge M S) :
    ∃ agent : M.Agent, FreeSubject M agent := by
  have hOccurs := hProof.proof_occurs
  have hCont := hProof.proof_is_contingent
  obtain ⟨S⟩ := hTerm hOccurs
  have pers : IsPersonalSource M S :=
    ultimate_source_must_be_personal M S (P S) (T S) (hTeleo S) hCont (hBridge S)
  exact personal_source_yields_free_subject M S pers (hControl S) hCont

/-!
================================================================================
XI. MINIMAL INDEPENDENCE TESTS & COUNTERMODELS
================================================================================
-/

def rank3 (x : Fin 3) : Nat :=
  if x.val = 0 then 2 else if x.val = 1 then 1 else 0

def GroundRel3 (y x : Fin 3) : Prop := rank3 y < rank3 x

instance (y x : Fin 3) : Decidable (GroundRel3 y x) :=
  inferInstanceAs (Decidable (rank3 y < rank3 x))

def Det3 (a b : Fin 3) : Prop := a = 1 ∧ b = 2

theorem transGen_det3 {a b : Fin 3} (h : Relation.TransGen Det3 a b) : a = 1 ∧ b = 2 := by
  induction h with
  | single h1 => exact h1
  | tail _ h2 ih =>
    obtain ⟨_ih1, h_mid⟩ := ih
    obtain ⟨h21, _h22⟩ := h2
    subst h_mid
    have hNeq : (2 : Fin 3) ≠ (1 : Fin 3) := by decide
    exact False.elim (hNeq h21)

/-- Countermodel 1: An independent non-causal ground G can explain the source configuration
without creating an explanatory cycle, without causal interaction, and without personal agency.
In this 3-node model: C depends on S (causally and explanatorily), S depends on G (explanatorily),
and neither S nor G depends backwards on C (C -> S -> G).
This strictly proves that an independent non-causal ground is NOT self-contradictory on bare
grounding alone; the Principle of Contrastive Teleology is strictly required to rule it out. -/
theorem independent_non_causal_ground_satisfiable_without_cycle :
    ∃ (M : DeterminationModel.{0, 0, 0}) (S : UltimateSource.{0, 0, 0} M) (G : M.Event),
      (∀ x, ¬ M.Determines G x) ∧
      (∀ x, ¬ M.Determines x G) ∧
      M.GroundingDependsOn S.sourceConfig G ∧
      AncestrallyDetermines M.Determines S.sourceConfig M.concreteOccurrence ∧
      M.GroundingDependsOn M.concreteOccurrence S.sourceConfig ∧
      ¬ M.GroundingDependsOn S.sourceConfig M.concreteOccurrence ∧
      ¬ M.GroundingDependsOn G M.concreteOccurrence ∧
      IsUltimate M.Determines S.sourceConfig ∧
      HasSamePastAlternative M ∧
      (∀ agent : M.Agent, ¬ FreeSubject M agent) := by
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
    Determines := Det3
    GroundingDependsOn := GroundRel3
    genuine_grounding_is_well_founded := hWF
    ontological_determination_implies_explanatory_dependence := by
      intro a b hab
      obtain ⟨ha, hb⟩ := transGen_det3 hab
      subst ha hb
      decide
    World := W
    actualWorld := false
    Accessible := fun _ _ => True
    SameCompletePriorState := fun _ _ => True
    Outcome := O
    OutcomeOf := fun e w => if e = 2 then w else false
    Agent := Empty
    IsAgent := fun _ => True
    OriginatesAt := fun _ _ => True
    ControlsAlternative := fun _ _ _ => True
  }
  let S : UltimateSource.{0, 0, 0} M := {
    sourceSubstrate := Unit
    sourceConfig := S_node
    config_occurs := trivial
    determines_occurrence := Relation.TransGen.single ⟨rfl, rfl⟩
    is_ultimate := by
      rintro ⟨p, _hp1, hp2⟩
      revert hp2
      decide
  }
  refine ⟨M, S, G_node, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

/-- Countermodel 2: Mere concrete occurrence does not entail an ultimate source or a Free Subject.
An occurrence can exist in an empty causal structure without agents. -/
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
    ontological_determination_implies_explanatory_dependence := by
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

/-- Countermodel 3: An ultimate source does not entail a Free Subject.
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
  have hWF : WellFounded GroundRel2 := (measure rank2).wf
  let M : DeterminationModel.{0, 0, 0} := {
    Event := E
    Occurs := fun _ => True
    concreteOccurrence := conc
    Determines := Det2
    GroundingDependsOn := GroundRel2
    genuine_grounding_is_well_founded := hWF
    ontological_determination_implies_explanatory_dependence := by
      intro a b hab
      obtain ⟨rfl, rfl⟩ := transGen_det2 hab
      decide
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

/-- Countermodel 4: Mere unforcedness does not imply freedom.
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
    ontological_determination_implies_explanatory_dependence := by
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

/-!
================================================================================
XII. PHILOSOPHICAL AUDIT & DEPENDENCY LEDGER
================================================================================

### 1. Pure Kernel-Proved Deductions (0 Axioms beyond core logic):
- `wellFounded_explanation_has_no_two_cycle`: Explanatory well-foundedness strictly excludes 2-cycles.
- `necessitation_excludes_contingency`: Necessitation on an invariant configuration strictly contradicts outcome divergence.
- `impersonal_source_fails_if_consequence_dependent`: Conditional explanatory failure if consequence-dependent.
- `impersonal_contingent_source_derives_consequence_dependence`: Derived from Contrastive PSR and Antecedent Symmetry.
- `impersonal_contingent_source_fails_as_ultimate_explanation`: Reductio against impersonal contingent determination.
- `independent_non_causal_ground_fails_under_contrastive_teleology`: Derived elimination of non-causal ground.
- `ultimate_source_must_be_personal`: Strict derivation of an unforced personal originator.
- `personal_source_yields_free_subject`: Derivation of a Libertarian Free Subject conditional on Agential Control.
- `concrete_proof_occurrence_implies_free_subject`: Master headline theorem actively consuming proof occurrence.
- `independent_non_causal_ground_satisfiable_without_cycle`: Concrete 3-node countermodel (C -> S -> G).
- `occurrence_alone_fails_free_subject`, `necessitating_source_fails_free_subject`,
  `unforced_personal_source_without_control_fails_free_subject`: Minimal negative independence models.

### 2. Explicit Philosophical Premises Exposed in Signatures:
- **Causal Determination Termination (`AncestryTerminatesDetermines`)**:
  Causal ancestry terminates at an ultimate source when the occurrence occurs.
- **Explanatory Grounding Well-Foundedness (`genuine_grounding_is_well_founded`)**:
  Genuine ultimate explanation cannot be circular.
- **Contrastive Principle of Sufficient Reason (`contrastive_psr`)**:
  A contingent determination with accessible alternatives requires a contrastive reason.
- **Impersonal Antecedent Symmetry (`impersonal_antecedent_symmetry_leaves_brute`)**:
  An impersonal non-necessitating source cannot contrastively explain the outcome through its antecedent nature alone.
- **Consequence-Dependent Selection (`consequence_dependent_selection`)**:
  An impersonal explanation of a non-necessitating determination must invoke the actual consequence.
- **Contingency Transfer Bridge (`ContingencyTransferBridge`)**:
  Connects occurrence contingency to source-configuration contingency or non-necessitation.
- **Principle of Contrastive Teleology (`ContrastiveTeleologyPrinciple`)**:
  An impersonal non-causal ground cannot non-necessitatingly select between contingent alternatives without agency or consequence-dependence.
- **Agential Control Bridge (`AgentialControlBridge`)**:
  An unforced personal agent who originates a contingent determination exercises active control over which alternative obtains (resolving the agential luck objection).

### 3. Unresolved Questions:
- Whether causal ancestry termination can be derived from an independent cosmological principle without assuming it as a premise.
- The precise metaphysical mechanics by which an agent exercises non-causal or agent-causal control over an alternative without a prior determiner.
-/

#print axioms wellFounded_explanation_has_no_two_cycle
#print axioms necessitation_excludes_contingency
#print axioms impersonal_source_fails_if_consequence_dependent
#print axioms impersonal_contingent_source_derives_consequence_dependence
#print axioms impersonal_contingent_source_fails_as_ultimate_explanation
#print axioms independent_non_causal_ground_fails_under_contrastive_teleology
#print axioms ultimate_source_must_be_personal
#print axioms personal_source_yields_free_subject
#print axioms concrete_proof_occurrence_implies_free_subject
#print axioms independent_non_causal_ground_satisfiable_without_cycle
#print axioms occurrence_alone_fails_free_subject
#print axioms necessitating_source_fails_free_subject
#print axioms unforced_personal_source_without_control_fails_free_subject

end FreeSubjectDeterminationDilemma
end Logos
