import Lean
import Logos.System

open Classical

namespace Logos
namespace OntologicalIncompleteness


/-- GENERAL CONTRASTIVE PSR: Decoupled from the necessity (aseity) of the ground.
If the system is a contingent concrete reality, there must exist an explanatory ground
that grounds its concrete actuality and provides a contrastive justification for why
the actual configuration obtained rather than an accessible alternative. -/
def GeneralContrastivePSR (S : ConcreteSystem.{u}) : Prop :=
  ContingentSystem S →
    ∃ T : CandidateGround S,
      T.GroundsConcreteActuality T.ground S.actualWorld ∧
      ∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
        (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
        ContrastiveExplanationForTotality S T w_alt

/-- METAPHYSICAL PRINCIPLE OF ASEITY (CORRECTED SCOPE):
Tag: META.
An ultimate ground that completely and contrastively explains the contingent totality must exist necessarily
(Aseity). Artificial or contingent candidates that do not supply a contrastive explanation
for the totality across alternatives are not forced into necessity. -/
def GroundingTotalityTerminatesInAseity
    (S : ConcreteSystem.{u})
    (T : CandidateGround S) : Prop :=
  T.GroundsConcreteActuality T.ground S.actualWorld →
  (∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
    (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
    ContrastiveExplanationForTotality S T w_alt) →
  IsNecessary S T

/-!
================================================================================
III. SUBSTANTIVE DEDUCTION OF THE NECESSARY, PERSONAL, AND FREE SOURCE
================================================================================
We analyze the three exhaustive possibilities for the Transcendent Ground:
1. Impersonal Necessitating Ground
2. Impersonal Non-Necessitating Ground
3. Free Personal Ground
================================================================================
-/

/-- Possibility 1: Impersonal Necessitating Ground.
T is necessary, and its determination rigidly necessitates the system's actual configuration. -/
def ImpersonalNecessitatingGround (S : ConcreteSystem.{u}) (T : CandidateGround S) : Prop :=
  IsNecessary S T ∧
  (∀ w : S.World, S.Accessible S.actualWorld w →
    T.ExistsAt T.ground w → (S.InstantiatedIn w ∧ S.ConfigurationIn w = S.ConfigurationIn S.actualWorld))

/-- THEOREM 4 (Impersonal Necessitation Destroys Contingency):
An impersonal necessary cause that rigidly determines the system makes the system
invariant across all accessible worlds, contradicting its genuine contingency.
(0 axioms). -/
theorem necessary_impersonal_ground_contradicts_contingency
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (hImpNec : ImpersonalNecessitatingGround S T)
    (hCont : ContingentSystem S) :
    False := by
  obtain ⟨hNec, hProd⟩ := hImpNec
  obtain ⟨_, w_alt, hAcc, hAlt⟩ := hCont
  have hT_at_alt := hNec w_alt hAcc
  have ⟨hInstAlt, hCfgAlt⟩ := hProd w_alt hAcc hT_at_alt
  cases hAlt with
  | inl hNotInst => exact hNotInst hInstAlt
  | inr hDiffCfg => exact hDiffCfg hCfgAlt

/-- Impersonal Non-Necessitating condition evaluated at a specific alternative world w_alt:
T fails to provide a contrastive justification favoring actualWorld over w_alt. -/
def UnjustifiedContrastiveAlternativeAt (S : ConcreteSystem.{u}) (T : CandidateGround S) (w_alt : S.World) : Prop :=
  ¬ T.ProvidesContrastiveJustification T.ground S.actualWorld w_alt

/-- THEOREM 5 (Unjustified Alternative Fails Contrastive Explanation at w_alt):
An alternative world where T fails to provide a contrastive justification contradicts
the requirement of ContrastiveExplanationForTotality at w_alt.
(0 axioms). -/
theorem unjustified_alternative_fails_contrastive_at
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (w_alt : S.World)
    (hUnjustified : UnjustifiedContrastiveAlternativeAt S T w_alt)
    (hExpl : ContrastiveExplanationForTotality S T w_alt) :
    False :=
  hUnjustified hExpl.2

/-- An impersonal ground is one that lacks personal agency (i.e. lacks cognitive apprehension
of alternative possible states of affairs). -/
def IsImpersonal (S : ConcreteSystem.{u}) (T : CandidateGround S) : Prop :=
  ¬ IsPersonalAgent S T

/-- Consequence-Dependent Determination Mode relative to candidate entity e:
The condition C accounting for why e grounds the actual configuration rather than
an alternative depends ontologically on the grounded totality S (ConstitutivePriority CandidateOnticItem.totality CandidateOnticItem.condition)
and conditions e's determination (ConstitutivePriority CandidateOnticItem.condition (CandidateOnticItem.candidate e)). -/
def ConsequenceDependentDetermination
    {Node : Type u} {Ext : Type u}
    (ConstitutivePriority : CandidateOnticItem Node Ext → CandidateOnticItem Node Ext → Prop)
    (e : Ext) : Prop :=
  ConstitutivePriority CandidateOnticItem.totality CandidateOnticItem.condition ∧
  ConstitutivePriority CandidateOnticItem.condition (CandidateOnticItem.candidate e)

/-- THEOREM 5C (Consequence-Dependent Determination Fails Well-Foundedness for Candidate e):
If the candidate ground entity e grounds the totality S, and the condition explaining e's determination
depends on the totality S, then e constitutively depends on itself, deriving False.
Hence consequence-dependent grounding fails to provide an ultimate explanation.
(0 axioms). -/
theorem consequence_dependent_mode_fails_well_foundedness
    {Node : Type u} {Ext : Type u}
    (ConstitutivePriority : CandidateOnticItem Node Ext → CandidateOnticItem Node Ext → Prop)
    (prior_wf : WellFounded ConstitutivePriority)
    (prior_trans : ∀ {a b c}, ConstitutivePriority a b → ConstitutivePriority b c → ConstitutivePriority a c)
    (e : Ext)
    (hGroundsTotality : ConstitutivePriority (CandidateOnticItem.candidate e) CandidateOnticItem.totality)
    (hConsequenceDep : ConsequenceDependentDetermination ConstitutivePriority e) :
    False :=
  candidate_consequence_circularity_refutation
    ConstitutivePriority prior_wf prior_trans e hGroundsTotality hConsequenceDep.1 hConsequenceDep.2

/-- Direct Consequence-Dependence relative to candidate entity e:
Why e is determined to ground the actual configuration appeals directly to the totality S that e grounds. -/
def DirectConsequenceDependence
    {Node : Type u} {Ext : Type u}
    (ConstitutivePriority : CandidateOnticItem Node Ext → CandidateOnticItem Node Ext → Prop)
    (e : Ext) : Prop :=
  ConstitutivePriority CandidateOnticItem.totality (CandidateOnticItem.candidate e)

/-- THEOREM 5D (Direct Consequence Dependence Fails Well-Foundedness for Candidate e):
Direct dependence of candidate entity e's determination on the grounded totality violates priority irreflexivity.
(0 axioms). -/
theorem direct_consequence_mode_fails_well_foundedness
    {Node : Type u} {Ext : Type u}
    (ConstitutivePriority : CandidateOnticItem Node Ext → CandidateOnticItem Node Ext → Prop)
    (prior_wf : WellFounded ConstitutivePriority)
    (prior_trans : ∀ {a b c}, ConstitutivePriority a b → ConstitutivePriority b c → ConstitutivePriority a c)
    (e : Ext)
    (hGroundsTotality : ConstitutivePriority (CandidateOnticItem.candidate e) CandidateOnticItem.totality)
    (hDirectDep : DirectConsequenceDependence ConstitutivePriority e) :
    False :=
  candidate_direct_consequence_cycle_refutation
    ConstitutivePriority prior_wf prior_trans e hGroundsTotality hDirectDep

/-- Independent Condition Mode relative to candidate entity e:
An external condition C determines the candidate ground entity e independently of the grounded totality S.
Directional Reading:
- `ConstitutivePriority CandidateOnticItem.condition (CandidateOnticItem.candidate e)`:
  Formally `CandidateOnticItem.condition ≺ CandidateOnticItem.candidate e` (C ≺ e), asserting that
  condition C is ontologically prior to and determines candidate ground e.
- `¬ ConstitutivePriority CandidateOnticItem.totality CandidateOnticItem.condition`:
  Formally `¬ (CandidateOnticItem.totality ≺ CandidateOnticItem.condition)` (¬ (S ≺ C)), asserting that
  the grounded totality S is NOT ontologically prior to condition C (C is independent of S; C does not depend on S).
Philosophical Clarification:
This isolates the branch where C is an independent prior condition rather than a consequence-dependent condition.
It does NOT assert that C has no relation whatsoever to the totality or reality; it asserts specifically that
C is not grounded in or conditioned by the consequence S. -/
def IndependentConditionMode
    {Node : Type u} {Ext : Type u}
    (ConstitutivePriority : CandidateOnticItem Node Ext → CandidateOnticItem Node Ext → Prop)
    (e : Ext) : Prop :=
  ConstitutivePriority CandidateOnticItem.condition (CandidateOnticItem.candidate e) ∧
  ¬ ConstitutivePriority CandidateOnticItem.totality CandidateOnticItem.condition

/-- Ultimacy of an explanatory ground:
T provides an ultimate, self-sufficient explanation of the concrete totality S.
Formally decouples factual grounding of concrete actuality (GroundsConcreteActuality)
from ultimate explanatory self-sufficiency (absence of prior independent determining conditions). -/
def IsUltimateGround
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop) : Prop :=
  T.GroundsConcreteActuality T.ground S.actualWorld ∧
  ∀ (e : T.ExtEntity), T.ground = GroundIdentity.external e →
    ¬ IndependentConditionMode (ConstitutivePriority T.ExtEntity) e

/-- THEOREM 5E (Independent Prior Condition Contradicts Ultimacy):
If an independent external condition C determines the candidate ground entity e (C ≺ e),
then T is an intermediate ground rather than an ultimate self-sufficient explanation of S.
Derived directly from the definition of ultimate explanatory sufficiency!
(0 axioms). -/
theorem independent_condition_contradicts_ultimacy
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (e : T.ExtEntity)
    (hExt : T.ground = GroundIdentity.external e)
    (hIndep : IndependentConditionMode (ConstitutivePriority T.ExtEntity) e)
    (hUlt : IsUltimateGround S T ConstitutivePriority) :
    False :=
  hUlt.2 e hExt hIndep

/-- METAPHYSICAL BRIDGE 1 (Principle of Explanatory Ultimacy):
Tag: META.
- Philosophical Justification:
  The Cosmological Principle of Sufficient Reason applied to the contingent totality requires that an entity
  that grounds the concrete actuality of S terminates the explanatory chain as an ultimate self-sufficient
  ground, rather than an intermediate ground whose determination depends on an independent external condition.
  (Defended in treatise `investigations/ontological_incompleteness_and_transcendent_source.md` §3.1.1, §3.1.3, §4 Step 6).
- Formal Status:
  Explicit metaphysical premise supplied as a formal parameter to the master theorem.
  Lean derives the conditional result: IF the PSR demands explanatory ultimacy,
  THEN an independent prior condition contradicts that ultimacy (`independent_condition_contradicts_ultimacy`).
- Role in Master Theorem:
  Eliminates the independent condition branch (`hIndep`) in the reductio of `contingent_system_derives_free_personal_source`.
- Corrected Scope:
  A candidate ground that provides a complete contrastive explanation for the totality of a contingent system
  cannot depend on an independent external condition. Artificial candidates that fail to explain the
  divergent alternatives are not forced into ultimacy. -/
def ExplanatoryUltimacyRequirement
    (S : ConcreteSystem.{u})
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop) : Prop :=
  ∀ (T : CandidateGround S),
    T.GroundsConcreteActuality T.ground S.actualWorld →
    (∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
      (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
      ContrastiveExplanationForTotality S T w_alt) →
    IsUltimateGround S T ConstitutivePriority

/-- Substantive Grounding Modes:
1. Necessitating Mode: rigidly necessitates the system.
2. Guided by Justification Mode: supplies a contrastive justification for all divergent alternatives. -/
def NecessitatingMode (S : ConcreteSystem.{u}) (T : CandidateGround S) : Prop :=
  ∀ w : S.World, S.Accessible S.actualWorld w →
    T.ExistsAt T.ground w → (S.InstantiatedIn w ∧ S.ConfigurationIn w = S.ConfigurationIn S.actualWorld)

def GuidedByJustificationMode (S : ConcreteSystem.{u}) (T : CandidateGround S) : Prop :=
  ∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
    (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
    T.ProvidesContrastiveJustification T.ground S.actualWorld w_alt

/-- THEOREM 4B (A Necessary Ground Cannot Rigidly Necessitate a Contingent System):
If a system is contingent and a candidate ground is necessary, the ground cannot rigidly necessitate
the system's actual configuration in all accessible worlds.
Reuses `necessary_impersonal_ground_contradicts_contingency`.
(0 axioms). -/
theorem necessary_ground_cannot_rigidly_necessitate_contingent_system
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (hCont : ContingentSystem S)
    (hNec : IsNecessary S T) :
    ¬ NecessitatingMode S T := by
  intro hNecMode
  have hImpNec : ImpersonalNecessitatingGround S T := ⟨hNec, hNecMode⟩
  exact necessary_impersonal_ground_contradicts_contingency S T hImpNec hCont

/-- THEOREM 4C (A Cadeia Não Pode Ser Forçada do Princípio ao Fim):
Reúne as duas impossibilidades complementares que governam o argumento ontológico:
(1) Forçagem inteiramente interna impossível: a determinação interna dos elos não pode
    fechar-se sobre si própria (`¬ SystemFullyInternallyDetermined S`).
    O nó terminal interno resultante testemunha o limite da explicação interna,
    mas não pode fundamentar a totalidade sem circularidade constitutiva (`internal_candidate_cannot_ground_totality`);
(2) Forçagem necessária rígida impossível: a totalidade contingente não pode ser rigidamente
    necessitada por um fundamento necessário (`¬ NecessitatingMode S T`).
CALIBRAÇÃO PRECISA DO ÂMBITO EXPLICATIVO E DISTINÇÃO CATEGORIAL:
(1) Este teorema estabelece formalmente que a determinação interna dos elos não explica a instanciação global da cadeia,
    e que a necessitação rígida da totalidade por um fundamento necessário destruiria a contingência assumida.
(2) Distingue-se cuidadosamente a conclusão formal deste teorema (`¬ SystemFullyInternallyDetermined S ∧ ¬ NecessitatingMode S T`),
    deduzida estritamente com 0 axiomas, da tese filosófica mais abrangente de que uma cadeia de determinações não pode
    subsistir sem uma Fonte Livre.
(3) A primeira conclusão NÃO acarreta automaticamente a segunda: a transição da não-forçagem mecânica para a Liberdade Libertária
    positiva exige premissas pontes adicionais irredutíveis (nomeadamente a transcendência estrutural, a irreflexividade da
    ordem bem-fundada, a integridade explicativa de razões e a soberania agencial), deduzidas no Teorema Mestre
    (`contingent_system_derives_free_personal_source` e `consolidated_ontological_incompleteness_derives_free_personal_source`).
(0 axioms). -/
theorem chain_cannot_be_exhaustively_forced
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (hNonEmpty : Nonempty S.Node)
    (hCont : ContingentSystem S)
    (hNec : IsNecessary S T) :
    (¬ SystemFullyInternallyDetermined S) ∧ (¬ NecessitatingMode S T) :=
  ⟨concrete_system_cannot_be_fully_internally_determined S hNonEmpty,
   necessary_ground_cannot_rigidly_necessitate_contingent_system S T hCont hNec⟩

/-- THEOREM 5B (Classical Deduction of Grounding Modes Exhaustiveness):
Demonstrates that every candidate ground either rigidly necessitates the system,
or provides contrastive justification for all divergent alternatives,
or contains an alternative world lacking contrastive justification.
Derived purely as an auxiliary classical theorem without unproved metaphysical premise! -/
theorem grounding_modes_exhaustive
    (S : ConcreteSystem.{u})
    (T : CandidateGround S) :
    NecessitatingMode S T ∨
    GuidedByJustificationMode S T ∨
    (∃ w_alt : S.World, S.Accessible S.actualWorld w_alt ∧
      (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) ∧
      UnjustifiedContrastiveAlternativeAt S T w_alt) := by
  by_cases hNec : NecessitatingMode S T
  · exact Or.inl hNec
  · right
    by_cases hGuided : GuidedByJustificationMode S T
    · exact Or.inl hGuided
    · right
      apply Classical.byContradiction
      intro hNotExists
      apply hGuided
      intro w_alt hAcc hAlt
      apply Classical.byContradiction
      intro hNotJust
      apply hNotExists
      exact ⟨w_alt, hAcc, hAlt, hNotJust⟩

/-- Priority relation on ontic items for the control countermodel. -/
def toyPriority : (Ext : Type 0) → CandidateOnticItem countermodelS.Node Ext → CandidateOnticItem countermodelS.Node Ext → Prop :=
  fun _ a b =>
    (∃ n, a = CandidateOnticItem.node n ∧ b = CandidateOnticItem.totality) ∨
    (∃ e, a = CandidateOnticItem.candidate e ∧ b = CandidateOnticItem.totality)

theorem toyPriority_wf : ∀ Ext, WellFounded (toyPriority Ext) := by
  intro Ext
  constructor
  intro x
  constructor
  intro y hy
  rcases hy with ⟨n, rfl, rfl⟩ | ⟨e, rfl, rfl⟩
  · constructor
    intro z hz
    rcases hz with ⟨n2, _, hEq⟩ | ⟨e2, _, hEq⟩
    · injection hEq
    · injection hEq
  · constructor
    intro z hz
    rcases hz with ⟨n2, _, hEq⟩ | ⟨e2, _, hEq⟩
    · injection hEq
    · injection hEq

theorem toyPriority_trans :
    ∀ Ext {a b c : CandidateOnticItem countermodelS.Node Ext},
      toyPriority Ext a b → toyPriority Ext b c → toyPriority Ext a c := by
  intro Ext a b c h1 h2
  rcases h1 with ⟨n, rfl, rfl⟩ | ⟨e, rfl, rfl⟩
  · rcases h2 with ⟨n2, hEq, _⟩ | ⟨e2, hEq, _⟩
    · injection hEq
    · injection hEq
  · rcases h2 with ⟨n2, hEq, _⟩ | ⟨e2, hEq, _⟩
    · injection hEq
    · injection hEq

theorem countermodelT_ultimate : IsUltimateGround countermodelS countermodelT toyPriority := by
  refine ⟨rfl, ?_⟩
  intro e hExt hIndep
  rcases hIndep.1 with ⟨n, hEq, _⟩ | ⟨e2, hEq, _⟩
  · injection hEq
  · injection hEq

theorem countermodelT_not_necessitating : ¬ NecessitatingMode countermodelS countermodelT := by
  intro hNec
  have hFalseCfg := (hNec false trivial trivial).2
  have hT := congrFun hFalseCfg ()
  revert hT
  decide

theorem toyConstitutiveOfTotality :
    ∀ Ext (n : countermodelS.Node), toyPriority Ext (CandidateOnticItem.node n) CandidateOnticItem.totality :=
  fun _ n => Or.inl ⟨n, rfl, rfl⟩

theorem toyGroundsTotality :
    ∀ (e : countermodelT.ExtEntity),
      countermodelT.ground = GroundIdentity.external e →
      toyPriority countermodelT.ExtEntity (CandidateOnticItem.candidate e) CandidateOnticItem.totality :=
  fun e _ => Or.inr ⟨e, rfl, rfl⟩

theorem toyInternalGroundsTotality :
    ∀ (n : countermodelS.Node),
      countermodelT.ground = GroundIdentity.internal n →
      ∀ Ext, toyPriority Ext CandidateOnticItem.totality (CandidateOnticItem.node n) := by
  intro n hInternal
  injection hInternal

theorem countermodelT_guided : GuidedByJustificationMode countermodelS countermodelT := by
  intro w_alt _ hDiff
  cases w_alt
  · refine ⟨?_, ⟨rfl, true_is_maximal⟩⟩
    change strictOutcomePreference (SystemOutcomeAt countermodelS true) (SystemOutcomeAt countermodelS false)
    rw [outcome_true, outcome_false]
    dsimp [strictOutcomePreference, configurationValue, countermodelS]
    decide
  · cases hDiff with
    | inl hNotInst => contradiction
    | inr hDiffCfg => contradiction

theorem countermodelS_psr : GeneralContrastivePSR countermodelS := by
  intro _
  refine ⟨countermodelT, rfl, ?_⟩
  intro w_alt hAcc hDiff
  refine ⟨trivial, countermodelT_guided w_alt hAcc hDiff⟩

theorem countermodelT_aseity : GroundingTotalityTerminatesInAseity countermodelS countermodelT := by
  intro _ _
  exact countermodelT_necessary

/-- THEOREM 5B₁ (Comprehensive Control Countermodel — Rational Intellectualist Determinism):
Demonstrates that a personal ground that satisfies the FULL explanatory structure:
(1) `ContingentSystem S` (genuine modal contingency of the totality),
(2) `IsNecessary S T` (Aseity),
(3) `NatureInvariant S T` (essential nature and rational faculties invariant across worlds),
(4) `IsPersonalAgent S T` (apprehends alternative states of affairs),
(5) `SelectsIntentionally S T` (intentionally chooses the actual configuration for reasons),
(6) `GuidedByJustificationMode S T` (supplies contrastive justification across divergent alternatives),
(7) `IsUltimateGround S T` (free of prior independent determining conditions),
(8) `¬ NecessitatingMode S T` (does not rigidly necessitate the system across worlds),
does NOT, by bare modal or classical logic, deduce `ActsFreely S T`.
PHILOSOPHICAL CORRELATE:
This model formalizes Leibnizian/Rationalist Determinism (or Theological Intellectualism):
God apprehends alternative possible worlds, God's reasons favor the actual world, God's nature is invariant,
and no external cause conditions God; yet God is determined by reasons (the moral necessity of the best)
and possesses no libertarian power to choose an alternative world under that identical nature.
This proves that closing the gap to Libertarian Freedom requires a substantive principle of agential causality.
(0 axioms). -/
theorem rational_intellectualist_control_model :
    ContingentSystem countermodelS ∧
    IsNecessary countermodelS countermodelT ∧
    NatureInvariant countermodelS countermodelT ∧
    IsPersonalAgent countermodelS countermodelT ∧
    SelectsIntentionally countermodelS countermodelT ∧
    GuidedByJustificationMode countermodelS countermodelT ∧
    IsUltimateGround countermodelS countermodelT toyPriority ∧
    (¬ NecessitatingMode countermodelS countermodelT) ∧
    (¬ ActsFreely countermodelS countermodelT) :=
  ⟨countermodelS_contingent,
   countermodelT_necessary,
   countermodelT_nature_invariant,
   countermodelT_personal_agent,
   countermodelT_selects_intentionally,
   countermodelT_guided,
   countermodelT_ultimate,
   countermodelT_not_necessitating,
   countermodelT_fails_acts_freely⟩

/-- METAPHYSICAL BRIDGE 2 (Principle of Explanatory Symmetry and Extrinsic Differentiation):
Tag: META.
- Philosophical Justification:
  Leibnizian Symmetry Principle & Contrastive PSR (van Fraassen 1980, Peter Lipton 2004 Difference Condition):
  Identical intrinsic conditions across alternatives cannot contrastively explain why one contingent configuration
  obtains rather than another without rigidly necessitating it.
  For an impersonal necessary ground with invariant essence across accessible worlds (`IsImpersonal ∧ NatureInvariant`),
  its intrinsic profile is strictly symmetric between the actual world and an unnecessitated alternative.
  Therefore, if it provides contrastive justification favoring the actual world over that alternative,
  that justification cannot be intrinsic: it necessarily requires an extrinsic explanatory condition in
  the ontic priority domain (`ConstitutivePriority CandidateOnticItem.condition (CandidateOnticItem.candidate e)`).
  (Defended in treatise `investigations/ontological_incompleteness_and_transcendent_source.md` §3.1.1, §3.1.2, §4 Step 3).
- Formal Status:
  Explicit metaphysical premise supplied as a formal hypothesis/parameter to the master theorem.
  Lean does not derive Leibniz's symmetry principle from bare logic; it formalizes the semantic constraint
  ruling out the unconstrained countermodel where `ProvidesContrastiveJustification` is asserted in vacuo.
- Role in Master Theorem:
  Forces an unnecessitating impersonal ground providing contrastive justification to depend on an extrinsic condition,
  which Lean then provably bifurcates into consequence-dependence or an independent condition
  (`impersonal_ground_forces_consequence_or_independent_condition`). -/
def ExplanatorySymmetryPrinciple
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop) : Prop :=
  ∀ (e : T.ExtEntity), T.ground = GroundIdentity.external e →
    IsImpersonal S T →
    NatureInvariant S T →
    ¬ NecessitatingMode S T →
    GuidedByJustificationMode S T →
    ConstitutivePriority T.ExtEntity CandidateOnticItem.condition (CandidateOnticItem.candidate e)

/-- THEOREM 5D₂ (The Impersonal Bridge Theorem — Deduced Trifurcation):
Under the Principle of Explanatory Symmetry, if an impersonal necessary ground with invariant essence
does not rigidly necessitate the contingent system, yet provides contrastive justification across divergent
alternatives, its determination MUST be either consequence-dependent or dependent on an independent condition.
DEDUCED as a theorem from the structural partition of extrinsic conditions in the ontic domain!
(0 axioms beyond core classical logic and the stated symmetry principle). -/
theorem impersonal_ground_forces_consequence_or_independent_condition
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (e : T.ExtEntity)
    (hExt : T.ground = GroundIdentity.external e)
    (hSymmPrinciple : ExplanatorySymmetryPrinciple S T ConstitutivePriority)
    (hImp : IsImpersonal S T)
    (hNature : NatureInvariant S T)
    (hNotNec : ¬ NecessitatingMode S T)
    (hGuided : GuidedByJustificationMode S T) :
    ConsequenceDependentDetermination (ConstitutivePriority T.ExtEntity) e ∨
    IndependentConditionMode (ConstitutivePriority T.ExtEntity) e := by
  have hExtCond := hSymmPrinciple e hExt hImp hNature hNotNec hGuided
  by_cases hDep : ConstitutivePriority T.ExtEntity CandidateOnticItem.totality CandidateOnticItem.condition
  · exact Or.inl ⟨hDep, hExtCond⟩
  · exact Or.inr ⟨hExtCond, hDep⟩

/-- METAPHYSICAL BRIDGE 3 (Teleological Agency Principle):
Tag: META.
- Philosophical Justification:
  An agent capable of apprehending alternatives (`IsPersonalAgent S T`) that operates in a mode guided by
  contrastive justification (`GuidedByJustificationMode S T`) selects intentionally in virtue of reasons.
  Rational agency is defined teleologically by intentional action oriented by reasons.
  (Defended in treatise `investigations/ontological_incompleteness_and_transcendent_source.md` §3.1.1, §3.1.3, §4 Step 8).
- Formal Status:
  Explicit metaphysical premise supplied as a formal parameter.
- Role in Master Theorem:
  Derives `SelectsIntentionally S T` from the surviving reason-guided agential branch, feeding into `FreePersonalSource`. -/
def TeleologicalAgencyPrinciple
    (S : ConcreteSystem.{u})
    (T : CandidateGround S) : Prop :=
  IsPersonalAgent S T →
  GuidedByJustificationMode S T →
  SelectsIntentionally S T

/-- METAPHYSICAL BRIDGE 4 (Aseity Preserves Nature for Impersonal Grounds):
Tag: META.
- Philosophical Justification:
  Aseity of a necessary impersonal entity entails that its essential nature and physical/metaphysical laws
  are invariant across all accessible possible worlds.
  (Defended in treatise `investigations/ontological_incompleteness_and_transcendent_source.md` §3.1.1, §4 Step 3).
- Formal Status:
  Explicit metaphysical premise supplied as a formal parameter.
- Role in Master Theorem:
  Ensures `NatureInvariant S T` holds for the candidate impersonal ground in the reductio of `contingent_system_derives_free_personal_source`. -/
def ImpersonalAseityPreservesNature
    (S : ConcreteSystem.{u})
    (T : CandidateGround S) : Prop :=
  IsImpersonal S T →
  IsNecessary S T →
  NatureInvariant S T

theorem countermodelT_impersonal_nature : ImpersonalAseityPreservesNature countermodelS countermodelT := by
  intro hImp _
  exfalso
  exact hImp countermodelT_personal_agent

/-- METAPHYSICAL BRIDGE 4B (Personal Aseity Preserves Nature):
Tag: META.
- Philosophical Justification:
  Aseity of the necessary personal ground entails that its essential nature and rational faculties
  are invariant across all accessible possible worlds.
  (Defended in treatise `investigations/ontological_incompleteness_and_transcendent_source.md` §3.1.1, §4 Step 8).
- Formal Status:
  Explicit metaphysical premise supplied as a formal parameter.
- Role in Master Theorem:
  Ensures `NatureInvariant S T` holds for the candidate personal ground, enabling the derivation
  of positive libertarian freedom via `agential_freedom_derived`. -/
def PersonalAseityPreservesNature
    (S : ConcreteSystem.{u})
    (T : CandidateGround S) : Prop :=
  IsPersonalAgent S T →
  IsNecessary S T →
  NatureInvariant S T

/-- METAPHYSICAL PRINCIPLE OF AGENTIAL SOVEREIGNTY OVER ALTERNATIVES (Princípio da Soberania Agencial):
Tag: META.
- Philosophical Justification:
  For an ultimate personal ground (`IsPersonalAgent ∧ IsUltimateGround`) whose nature does not rigidly
  necessitate the contingent totality (`¬ NecessitatingMode`), the space of divergent accessible alternative
  outcomes of the contingent system constitutes agential choice options of that personal source.
  Because T is the ultimate explanatory ground and no independent external condition determines S,
  any accessible alternative configuration of S under that same invariant nature is an outcome that T
  could choose in that world (`T.ChoosesOutcomeAt T.ground w_alt (SystemOutcomeAt S w_alt)`).
  This principle formalizes that counterfactual divergence from an ultimate personal source is not
  an unchosen, detached accident or brute blind deviation, but an agential exercise of sovereign determination.
- Formal Status:
  Explicit metaphysical premise on the nature of personal causality.
  As proven by `rational_intellectualist_control_model`, this premise is MINIMAL and INDISPENSABLE to
  rule out Leibnizian rational determinism (theological intellectualism).
- Role in Master Theorem:
  Deduces `AgentialCounterfactualChoiceBridge` via `agential_counterfactual_choice_bridge_from_sovereignty`. -/
def AgentialSovereigntyOverAlternatives
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop) : Prop :=
  IsPersonalAgent S T →
  IsUltimateGround S T ConstitutivePriority →
  ¬ NecessitatingMode S T →
  ∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
    SystemOutcomeAt S w_alt ≠ SystemOutcomeAt S S.actualWorld →
    T.ChoosesOutcomeAt T.ground w_alt (SystemOutcomeAt S w_alt)

/-- THEOREM 6B₂ (Deduction of Counterfactual Choice Bridge from Agential Sovereignty):
Demonstrates that `AgentialCounterfactualChoiceBridge` is DEDUCED as a theorem from:
(1) Agential Sovereignty over Alternatives (`AgentialSovereigntyOverAlternatives`),
(2) Personal Agency (`IsPersonalAgent`),
(3) Explanatory Ultimacy (`IsUltimateGround`),
(4) Non-necessitation of the contingent system (`¬ NecessitatingMode`).
(0 axioms). -/
theorem agential_counterfactual_choice_bridge_from_sovereignty
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (hSovereign : AgentialSovereigntyOverAlternatives S T ConstitutivePriority)
    (hAgent : IsPersonalAgent S T)
    (hUlt : IsUltimateGround S T ConstitutivePriority)
    (hNotNec : ¬ NecessitatingMode S T) :
    AgentialCounterfactualChoiceBridge S T := by
  intro _ _ w_alt hAcc hDiff
  exact hSovereign hAgent hUlt hNotNec w_alt hAcc hDiff

/-- Pre-correction unconstrained explanation definition (maintained for vulnerability demonstration): -/
def OldExplainsOutcomeAt
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (w : S.World)
    (out : Option (S.Node → Bool)) : Prop :=
  T.ExistsAt T.ground w ∧ SystemOutcomeAt S w = out ∧
  T.DeterminesOutcomeAt T.ground w out

def OldUniversalOutcomePSR (S : ConcreteSystem.{u}) : Prop :=
  ∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
    ∃ T' : CandidateGround S, OldExplainsOutcomeAt S T' w_alt (SystemOutcomeAt S w_alt)

/-- VULNERABILITY THEOREM (The Pre-Correction Definition of PSR Was Vacuously Provable):
Demonstrates that under the unconstrained definition of explanation (`OldExplainsOutcomeAt`),
an artificial dummy candidate with `GroundsConcreteActuality := fun _ _ => False` and
unconstrained `DeterminesOutcomeAt := fun _ _ _ => True` vacuously proves `OldUniversalOutcomePSR S`
for ANY concrete system S, formally witnessing the semantic defect identified in the audit.
(0 axioms). -/
theorem pre_correction_psr_vacuously_provable_by_synthetic_candidate
    (S : ConcreteSystem.{u}) :
    OldUniversalOutcomePSR S := by
  intro w_alt _
  let dummy : CandidateGround S := {
    ExtEntity := PUnit
    ground := GroundIdentity.external PUnit.unit
    ExistsAt := fun _ _ => True
    GroundsConcreteActuality := fun _ _ => False
    grounding_binds_actuality := fun _ h => False.elim h
    EssenceOf := fun _ _ => ⟨0, 0⟩
    ProvidesContrastiveJustification := fun _ _ _ => True
    ApprehendsAlternative := fun _ _ => True
    ReasonsFavor := fun _ _ _ => True
    ChoosesOutcomeAt := fun _ _ _ => True
    DeterminesOutcomeAt := fun _ _ _ => True
  }
  refine ⟨dummy, ?_⟩
  refine ⟨trivial, rfl, trivial⟩

/-- Foundational Causal Access:
An external ground e has foundational causal access to node n in system S under ConstitutivePriority
if e grounds an internal terminal node b in priority, and n is reachable from b via finite internal determinations in S: -/
def HasFoundationalCausalAccess
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (n : S.Node) : Prop :=
  ∃ (e : T.ExtEntity), T.ground = GroundIdentity.external e ∧
    ∃ (b : S.Node), IsInternalTerminalNode S b ∧
      ConstitutivePriority T.ExtEntity (CandidateOnticItem.candidate e) (CandidateOnticItem.node b) ∧
      (b = n ∨ DeterminesAncestrally S.Determines b n)

/-- Genuine Ontic Grounding of System Non-Instantiation:
An external candidate ground T genuinely grounds why the concrete system S is not instantiated
at world w under ConstitutivePriority if:
(1) T exists at world w (`T.ExistsAt T.ground w`);
(2) S is not instantiated at world w (`¬ S.InstantiatedIn w`);
(3) T is an external entity holding constitutive priority over the totality of S;
(4) T provides contrastive justification for the non-actualization of S at w relative to the actual world
    (`T.ProvidesContrastiveJustification T.ground S.actualWorld w`).
Precludes vacuous explanation of absence by mere coexistence in a world where S is uninstantiated. -/
def CandidateGround.GroundsNonInstantiationAt
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (w : S.World) : Prop :=
  T.ExistsAt T.ground w ∧
  ¬ S.InstantiatedIn w ∧
  (∃ (e : T.ExtEntity), T.ground = GroundIdentity.external e ∧
    ConstitutivePriority T.ExtEntity (CandidateOnticItem.candidate e) CandidateOnticItem.totality) ∧
  T.ProvidesContrastiveJustification T.ground S.actualWorld w

/-- Genuine Ontic Grounding of a System Outcome at World w:
Distinguishes two exhaustive, non-arbitrary modes of ontic grounding:
(1) Instantiated Outcome (out = some cfg): S is instantiated at world w, out matches the actual
    configuration of S at w, and T possesses foundational causal access to all nodes in S;
(2) Uninstantiated Outcome (out = none): out is none, and T genuinely grounds the non-instantiation
    of S at world w (`T.GroundsNonInstantiationAt S ConstitutivePriority w`).
In both cases, T exists at world w (`T.ExistsAt T.ground w`). -/
def CandidateGround.GroundsOutcomeAt
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (w : S.World)
    (out : Option (S.Node → Bool)) : Prop :=
  T.ExistsAt T.ground w ∧
  ((S.InstantiatedIn w ∧ out = some (S.ConfigurationIn w) ∧ (∀ n : S.Node, HasFoundationalCausalAccess S T ConstitutivePriority n)) ∨
   (out = none ∧ T.GroundsNonInstantiationAt S ConstitutivePriority w))

/-- Onto-Causal Determination Fidelity:
Establishes the constitutive connection between a candidate ground's determination predicate
(`T.DeterminesOutcomeAt`), the causal access structure, and the concrete configuration of the system.
Precludes arbitrary decoupled predicates from counting as ontological determination:
(1) Instantiated World: if T determines outcome `out` at world w where S is instantiated,
    then `out` must be `some (S.ConfigurationIn w)`, T must possess foundational causal access to
    every terminal boundary node b (`IsInternalTerminalNode S b`), and to all nodes n in S;
(2) Uninstantiated World: if T determines outcome `out` at world w where S is not instantiated,
    then `out` must be `none`, and T genuinely grounds the non-instantiation of S at w.
Crucially, free intentional choice (`ChoosesOutcomeAt`) is completely omitted from this condition,
preserving strict neutrality between personal and impersonal determination modes. -/
def CausalDeterminationCoherence
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop) : Prop :=
  ∀ (w : S.World) (out : Option (S.Node → Bool)),
    T.DeterminesOutcomeAt T.ground w out →
      ((S.InstantiatedIn w ∧ out = some (S.ConfigurationIn w) ∧
        (∀ b : S.Node, IsInternalTerminalNode S b → HasFoundationalCausalAccess S T ConstitutivePriority b) ∧
        (∀ n : S.Node, HasFoundationalCausalAccess S T ConstitutivePriority n)) ∨
       (out = none ∧ T.GroundsNonInstantiationAt S ConstitutivePriority w))

/-- THEOREM (Causal Determination Fidelity Entails Ontic Grounding of Outcome):
Demonstrates that if an external candidate ground exists at world w and its determination
satisfies onto-causal determination fidelity, its determination of `out` at w strictly entails
that it genuinely grounds the outcome at w (`T.GroundsOutcomeAt S ConstitutivePriority w out`).
(0 axioms). -/
theorem causal_determination_fidelity_implies_grounds_outcome
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (hCoh : CausalDeterminationCoherence S T ConstitutivePriority)
    (w : S.World)
    (out : Option (S.Node → Bool))
    (hExists : T.ExistsAt T.ground w)
    (hDet : T.DeterminesOutcomeAt T.ground w out) :
    T.GroundsOutcomeAt S ConstitutivePriority w out := by
  refine ⟨hExists, ?_⟩
  cases hCoh w out hDet with
  | inl hInst =>
    exact Or.inl ⟨hInst.1, hInst.2.1, hInst.2.2.2⟩
  | inr hUninst =>
    exact Or.inr ⟨hUninst.1, hUninst.2⟩

/-- Genuine explanation of a concrete system outcome at a specific world w:
A candidate ground T explains outcome `out` of system S at world w under constitutive priority if:
(1) T exists at world w (`T.ExistsAt T.ground w`);
(2) SystemOutcomeAt S w = out;
(3) T determines `out` at w (`T.DeterminesOutcomeAt T.ground w out`);
(4) T is an external candidate grounding the totality in ConstitutivePriority;
(5) T genuinely grounds the outcome at w (`T.GroundsOutcomeAt S ConstitutivePriority w out`);
(6) T's determination satisfies onto-causal determination fidelity (`CausalDeterminationCoherence S T ConstitutivePriority`).
This relation is ontologically tied to the priority structure, node-level grounding, and causal coherence,
preventing synthetic records from satisfying the PSR vacuously.
Crucially, `ChoosesOutcomeAt` is completely omitted from this definition, ensuring strict ontological
neutrality between agential and non-agential determination. -/
def ExplainsOutcomeAt
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (w : S.World)
    (out : Option (S.Node → Bool)) : Prop :=
  T.ExistsAt T.ground w ∧
  SystemOutcomeAt S w = out ∧
  T.DeterminesOutcomeAt T.ground w out ∧
  (∃ (e : T.ExtEntity), T.ground = GroundIdentity.external e ∧
    ConstitutivePriority T.ExtEntity (CandidateOnticItem.candidate e) CandidateOnticItem.totality) ∧
  T.GroundsOutcomeAt S ConstitutivePriority w out ∧
  CausalDeterminationCoherence S T ConstitutivePriority

/-- THEOREM (Candidate Without Causal Access Fails Explanation):
Demonstrates that if an external candidate lacks foundational causal access to some node n of an
instantiated system S at world w, it strictly FAILS ExplainsOutcomeAt.
(0 axioms). -/
theorem candidate_without_causal_access_fails_explanation
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (n : S.Node)
    (hNoAccess : ¬ HasFoundationalCausalAccess S T ConstitutivePriority n)
    (w : S.World)
    (hInst : S.InstantiatedIn w)
    (out : Option (S.Node → Bool)) :
    ¬ ExplainsOutcomeAt S T ConstitutivePriority w out := by
  intro ⟨_, _, _, _, hGrounds, _⟩
  cases hGrounds.2 with
  | inl hBranch => exact hNoAccess (hBranch.2.2 n)
  | inr hUninst => exact hUninst.2.2.1 hInst

/-- NON-VACUITY THEOREM (Synthetic Candidate Lacking Constitutive Priority Fails ExplainsOutcomeAt):
Demonstrates that under the corrected semantics, a synthetic dummy candidate that is not an
external candidate grounding totality in ConstitutivePriority strictly FAILS ExplainsOutcomeAt.
(0 axioms). -/
theorem synthetic_candidate_without_constitutive_priority_fails_psr
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (hNotExt : ∀ (e : T.ExtEntity), T.ground = GroundIdentity.external e →
      ¬ ConstitutivePriority T.ExtEntity (CandidateOnticItem.candidate e) CandidateOnticItem.totality)
    (w : S.World)
    (out : Option (S.Node → Bool)) :
    ¬ ExplainsOutcomeAt S T ConstitutivePriority w out := by
  intro ⟨_, _, _, ⟨e, he, hTot⟩, _⟩
  exact (hNotExt e he) hTot

/-- Brute / Ungrounded Outcome at an accessible alternative world:
The divergent outcome at w_alt obtains without being explained by the candidate ground T. -/
def BruteOutcomeAt
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (w : S.World) : Prop :=
  ¬ ExplainsOutcomeAt S T ConstitutivePriority w (SystemOutcomeAt S w)

/-- Impersonally Determined Outcome at an accessible alternative world:
The ground T is impersonal and explains the outcome at world w. -/
def ImpersonallyDeterminedOutcomeAt
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (w : S.World) : Prop :=
  IsImpersonal S T ∧ ExplainsOutcomeAt S T ConstitutivePriority w (SystemOutcomeAt S w)

/-- PRINCIPLE OF MODAL EXPLANATORY EXHAUSTION AT ACCESSIBLE ALTERNATIVES:
Tag: META.
- Philosophical Justification:
  Metaphysical Exhaustion of Actuality Explanations across Modal Space:
  For any accessible alternative world where the concrete system outcome diverges from the actual world,
  the divergent actuality must fall under one of three exhaustive metaphysical modes relative to ground T:
  (1) It is an intentional agential choice of the personal ground T;
  (2) It is impersonally determined by T operating as an impersonal ground;
  (3) It is an ungrounded brute fact relative to T. -/
def ModalExplanatoryExhaustionAtAlternatives
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop) : Prop :=
  ∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
    SystemOutcomeAt S w_alt ≠ SystemOutcomeAt S S.actualWorld →
    (T.ChoosesOutcomeAt T.ground w_alt (SystemOutcomeAt S w_alt) ∨
     ImpersonallyDeterminedOutcomeAt S T ConstitutivePriority w_alt ∨
     BruteOutcomeAt S T ConstitutivePriority w_alt)

/-- PRINCIPLE OF UNIVERSAL EXPLANATORY GROUNDING AT ACCESSIBLE ALTERNATIVES (Universal Contrastive PSR):
Tag: META.
- Philosophical Justification:
  The Principle of Sufficient Reason applied across accessible possible worlds rejects ungrounded
  brute facts: every concrete configuration in an accessible world possesses an explanatory ground. -/
def UniversalExplanatoryGroundingAtAlternatives
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop) : Prop :=
  ∀ w_alt : S.World, S.Accessible S.actualWorld w_alt → ¬ BruteOutcomeAt S T ConstitutivePriority w_alt

/-- Neutral Principle of Sufficient Reason across Accessible Worlds:
Every concrete outcome in an accessible alternative world possesses SOME explanatory ground,
without presupposing that it must be explained by the specific ground T. -/
def UniversalOutcomePSR
    (S : ConcreteSystem.{u})
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop) : Prop :=
  ∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
    ∃ T' : CandidateGround S, ExplainsOutcomeAt S T' ConstitutivePriority w_alt (SystemOutcomeAt S w_alt)

/-- PRINCIPLE OF ULTIMATE GROUND EXPLANATORY SCOPE (Tag: META):
- Philosophical Justification:
  Metaphysical Unicity and Ultimacy of the Ground of Reality:
  If T is an ultimate personal ground with necessary existence, the explanation of any accessible
  actualization of the contingent totality S cannot terminate in an independent rival source T' ≠ T
  without destroying either the unicity (DivineClassicalAttributes.universal_ground_unicity)
  or the ultimacy of the foundational ground of the cosmos.
  Therefore, any accessible actualization of S explained by some ground is explained by T itself.
- Formal Status:
  Explicit metaphysical bridge supplied as a formal parameter. -/
def UltimateGroundExplanatoryScope
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop) : Prop :=
  IsPersonalAgent S T →
  IsUltimateGround S T ConstitutivePriority →
  IsNecessary S T →
  ∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
    (∃ T' : CandidateGround S, ExplainsOutcomeAt S T' ConstitutivePriority w_alt (SystemOutcomeAt S w_alt)) →
    ExplainsOutcomeAt S T ConstitutivePriority w_alt (SystemOutcomeAt S w_alt)

/-- Item is ungrounded in priority order:
No candidate ontic item is constitutively prior to candidate e. -/
def IsUngroundedInPriority
    {Node : Type u}
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem Node Ext → CandidateOnticItem Node Ext → Prop)
    {Ext : Type u}
    (e : Ext) : Prop :=
  ∀ (x : CandidateOnticItem Node Ext), ¬ ConstitutivePriority Ext x (CandidateOnticItem.candidate e)

/-- Inductive Priority Path in Constitutive Priority:
A multi-step priority chain representing an explicit sequence of intermediate priority steps. -/
inductive PriorityPath
    {Node : Type u}
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem Node Ext → CandidateOnticItem Node Ext → Prop)
    (Ext : Type u) :
    CandidateOnticItem Node Ext → CandidateOnticItem Node Ext → Prop
  | single (x y : CandidateOnticItem Node Ext) :
      ConstitutivePriority Ext x y → PriorityPath ConstitutivePriority Ext x y
  | step (x y z : CandidateOnticItem Node Ext) :
      ConstitutivePriority Ext x y → PriorityPath ConstitutivePriority Ext y z →
      PriorityPath ConstitutivePriority Ext x z

/-- Complete Explanatory Chain in Constitutive Priority:
An explanatory chain connecting an initial explanatory candidate T' to the ultimate ground T:
(1) T' has external entity e' grounding totality in priority;
(2) T has external entity e_ult that is ungrounded in priority;
(3) there is a domain identification he : T'.ExtEntity = T.ExtEntity;
(4) there is an explanatory path (either identity or intermediate priority steps)
    from e_ult to e' in the shared external domain.
Precludes vacuous explanation by connecting endpoints through real priority steps. -/
def CompleteExplanatoryChain
    (S : ConcreteSystem.{u})
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (T' T : CandidateGround S) : Prop :=
  ∃ (he : T'.ExtEntity = T.ExtEntity) (e' : T'.ExtEntity) (e_ult : T.ExtEntity),
    T'.ground = GroundIdentity.external e' ∧
    T.ground = GroundIdentity.external e_ult ∧
    ConstitutivePriority T'.ExtEntity (CandidateOnticItem.candidate e') CandidateOnticItem.totality ∧
    IsUngroundedInPriority ConstitutivePriority e_ult ∧
    (he ▸ e' = e_ult ∨
     PriorityPath ConstitutivePriority T.ExtEntity (CandidateOnticItem.candidate e_ult) (CandidateOnticItem.candidate (he ▸ e')))

/-- Mediated Explanatory Scope (Genuinely Distinct from Direct Scope):
Universally quantifies over every local explanation at accessible alternative worlds
and requires an actual explanatory chain connecting the local candidate T' to the
ultimate ground T, accommodating secondary causes. -/
def MediatedExplanatoryScope
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop) : Prop :=
  IsPersonalAgent S T →
  IsUltimateGround S T ConstitutivePriority →
  IsNecessary S T →
  ∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
    ∀ T' : CandidateGround S,
      ExplainsOutcomeAt S T' ConstitutivePriority w_alt (SystemOutcomeAt S w_alt) →
      CompleteExplanatoryChain S ConstitutivePriority T' T

/-- Explanatory Transmission Bridge (Tag: META):
Metaphysical bridge asserting that when a local secondary cause T' explains an outcome
at world w_alt and lies on a complete explanatory chain terminating at ultimate ground T,
the explanatory efficacy is transmitted to the foundational source T. -/
def ExplanatoryTransmission
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop) : Prop :=
  ∀ (T' : CandidateGround S) (w_alt : S.World),
    ExplainsOutcomeAt S T' ConstitutivePriority w_alt (SystemOutcomeAt S w_alt) →
    CompleteExplanatoryChain S ConstitutivePriority T' T →
    ExplainsOutcomeAt S T ConstitutivePriority w_alt (SystemOutcomeAt S w_alt)

/-- THEOREM (Mediated Scope and Explanatory Transmission Entail Direct Scope):
Demonstrates that under the explicit metaphysical bridge of Explanatory Transmission,
MediatedExplanatoryScope deductively yields UltimateGroundExplanatoryScope.
(0 axioms beyond the explicit transmission hypothesis). -/
theorem mediated_scope_to_ultimate_scope_under_transmission
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (hMed : MediatedExplanatoryScope S T ConstitutivePriority)
    (hTrans : ExplanatoryTransmission S T ConstitutivePriority) :
    UltimateGroundExplanatoryScope S T ConstitutivePriority := by
  intro hAgent hUlt hNec w_alt hAcc hExSome
  obtain ⟨T', hExpT'⟩ := hExSome
  have hChain := hMed hAgent hUlt hNec w_alt hAcc T' hExpT'
  exact hTrans T' w_alt hExpT' hChain

/-- Candidate Ground has external identity matching the universal modal ground g: -/
def IsUniversalGroundCandidate (S : ConcreteSystem.{0}) (g : Logos.Entity.Entity) (T : CandidateGround S) : Prop :=
  ∃ (he : T.ExtEntity = Logos.Entity.Entity), T.ground = he ▸ GroundIdentity.external g

/-- Priority-Grounding Relational Homomorphism:
Specifies the formal representation embedding the constitutive priority order of S
into the universal modal grounding of reality in Logos. -/
structure PriorityGroundingHomomorphism
    (S : ConcreteSystem.{0})
    (ConstitutivePriority : (Ext : Type 0) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (g : Logos.Entity.Entity) where
  itemToEntity : (Ext : Type 0) → CandidateOnticItem S.Node Ext → Logos.Entity.Entity
  itemToEntity_universal : itemToEntity Logos.Entity.Entity (CandidateOnticItem.candidate g) = g
  terminal_unicity : ∀ (Ext : Type 0) (e : Ext),
    IsUngroundedInPriority ConstitutivePriority e →
    itemToEntity Ext (CandidateOnticItem.candidate e) = g
  priority_chain_has_terminus : ∀ (T' : CandidateGround S),
    (∃ e' : T'.ExtEntity, T'.ground = GroundIdentity.external e' ∧
      ConstitutivePriority T'.ExtEntity (CandidateOnticItem.candidate e') CandidateOnticItem.totality) →
    ∃ (e' : T'.ExtEntity) (e_ult : T'.ExtEntity),
      T'.ground = GroundIdentity.external e' ∧
      ConstitutivePriority T'.ExtEntity (CandidateOnticItem.candidate e') CandidateOnticItem.totality ∧
      IsUngroundedInPriority ConstitutivePriority e_ult ∧
      (e' = e_ult ∨
       PriorityPath ConstitutivePriority T'.ExtEntity (CandidateOnticItem.candidate e_ult) (CandidateOnticItem.candidate e'))

/-- THEOREM (Universal Modal Ground Unicity of Explanatory Chain Terminus):
Demonstrates that under a priority-grounding homomorphism, the ungrounded terminus of any
priority chain is mapped to the unique universal modal ground g.
Refutes polytheistic rival terminal sources without fallaciously claiming that direct
outcome determination is derived from modal unicity alone.
(0 axioms). -/
theorem universal_ground_chain_terminus_unicity
    (S : ConcreteSystem.{0})
    (g : Logos.Entity.Entity)
    (ConstitutivePriority : (Ext : Type 0) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (hHomo : PriorityGroundingHomomorphism S ConstitutivePriority g)
    (hU : Logos.FoundationalOmnipresence.UniversalModalGround g)
    (hNoTotal : ∀ s : Logos.Agency.Subject, ∃ p, ¬ Logos.Agency.Means s p)
    (T' : CandidateGround S)
    (hExt' : ∃ e' : T'.ExtEntity, T'.ground = GroundIdentity.external e' ∧
      ConstitutivePriority T'.ExtEntity (CandidateOnticItem.candidate e') CandidateOnticItem.totality) :
    ∃ (e_ult : T'.ExtEntity),
      IsUngroundedInPriority ConstitutivePriority e_ult ∧
      hHomo.itemToEntity T'.ExtEntity (CandidateOnticItem.candidate e_ult) = g := by
  have hExist := Logos.FoundationalUnicity.exactly_one_universal_modal_ground hNoTotal
  obtain ⟨g_unique, _hU_unique, hUniq⟩ := hExist
  have _hEqG : g = g_unique := hUniq g hU
  obtain ⟨_e', e_ult, _hGrd, _hPrio, hUngrounded, _hPath⟩ := hHomo.priority_chain_has_terminus T' hExt'
  refine ⟨e_ult, hUngrounded, ?_⟩
  exact hHomo.terminal_unicity T'.ExtEntity e_ult hUngrounded

/-- LEMMA (Deduction of Ground-Indexed Explanation from Neutral PSR and Scope):
Demonstrates that under the neutral Universal PSR and the Explanatory Scope of an ultimate ground,
the ground T explains every accessible outcome of the system.
(0 axioms). -/
theorem universal_grounding_of_ultimate_ground
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (hPSR : UniversalOutcomePSR S ConstitutivePriority)
    (hScope : UltimateGroundExplanatoryScope S T ConstitutivePriority)
    (hAgent : IsPersonalAgent S T)
    (hUlt : IsUltimateGround S T ConstitutivePriority)
    (hNec : IsNecessary S T) :
    UniversalExplanatoryGroundingAtAlternatives S T ConstitutivePriority := by
  intro w_alt hAcc
  dsimp [BruteOutcomeAt]
  have hExSome := hPSR w_alt hAcc
  have hExpT := hScope hAgent hUlt hNec w_alt hAcc hExSome
  intro hNotExp
  exact hNotExp hExpT

/-- PRINCIPLE OF AGENTIAL INTENTIONAL DETERMINATION (Tag: META):
- Philosophical Justification:
  Action-Theoretic Grounding in Foundational Agency (Choice.lean:779 AxIntentionalChoice):
  In foundational action theory, an intentional action is constitutively an exercise of choice
  (`AxIntentionalChoice : Act s p → ∃ q, Chooses s p q`). For an ultimate, self-sufficient personal
  ground whose essential nature is invariant across accessible worlds, any contingent outcome that
  the personal agent determines across accessible worlds is determined via its intentional choice
  (`ChoosesOutcomeAt`), rather than by a blind, sub-personal, or involuntary mechanical reflex.
- Formal Status:
  Explicit metaphysical bridge supplied as a formal parameter. -/
def AgentialDeterminationIsChoice
    (S : ConcreteSystem.{u})
    (T : CandidateGround S) : Prop :=
  IsPersonalAgent S T →
  NatureInvariant S T →
  ∀ (w : S.World) (out : Option (S.Node → Bool)),
    T.DeterminesOutcomeAt T.ground w out ↔ T.ChoosesOutcomeAt T.ground w out

/-- Restricted Forward Implication: Agential Determination Entails Choice across Divergent Alternatives.
Weaker, strictly sufficient forward implication matching the exact scope of accessible divergent
alternatives needed to deduce Agential Sovereignty and ActsFreely. -/
def AgentialDeterminationEntailsChoice
    (S : ConcreteSystem.{u})
    (T : CandidateGround S) : Prop :=
  IsPersonalAgent S T →
  NatureInvariant S T →
  ∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
    SystemOutcomeAt S w_alt ≠ SystemOutcomeAt S S.actualWorld →
    ∀ (out : Option (S.Node → Bool)),
      T.DeterminesOutcomeAt T.ground w_alt out → T.ChoosesOutcomeAt T.ground w_alt out

/-- LEMMA (The Forward Implication is Deduced from the Biconditional):
(0 axioms). -/
theorem agential_determination_entails_choice_of_biconditional
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (hBicond : AgentialDeterminationIsChoice S T) :
    AgentialDeterminationEntailsChoice S T := by
  intro hAgent hNature w_alt _ _ out hDet
  exact (hBicond hAgent hNature w_alt out).mp hDet

/-- State-Space Propositional Representation of Outcomes:
Represents that the outcome of system S at world w is `out`. -/
def OutcomeAt (S : ConcreteSystem.{u}) (w : S.World) (out : Option (S.Node → Bool)) : Prop :=
  SystemOutcomeAt S w = out

/-- THEOREM (Pairwise Incompatibility of Distinct Outcomes at the Same World):
Demonstrates that for distinct outcomes out1 ≠ out2 evaluated at the same world w,
their realization propositions are strictly incompatible in standard propositional logic.
(0 axioms). -/
theorem incompatible_outcomes_at_world
    (S : ConcreteSystem.{u})
    (w : S.World)
    (out1 out2 : Option (S.Node → Bool))
    (hDiff : out1 ≠ out2) :
    Logos.Alternatives.Incompatible (OutcomeAt S w out1) (OutcomeAt S w out2) := by
  intro ⟨h1, h2⟩
  dsimp [OutcomeAt] at h1 h2
  rw [h1] at h2
  exact hDiff h2

/-- Outcome-Specific Representation of Incompatible Alternative:
A proposition q represents an incompatible alternative outcome out' of system S at world w
if q entails that the outcome at w is out'.
Precludes vacuous choice reflection by formally binding q's content to the alternative configuration. -/
def RepresentsAlternativeOutcome
    (S : ConcreteSystem.{u})
    (w : S.World)
    (out' : Option (S.Node → Bool))
    (q : Prop) : Prop :=
  q → OutcomeAt S w out'

/-- Binary Contrast Space on Accessible System Outcomes:
Specifies that at world w_alt, any outcome distinct from the divergent outcome out_alt
is identically the actual-world alternative outcome out_act. -/
def BinaryContrastSpace
    (S : ConcreteSystem.{u})
    (_w_alt : S.World)
    (out_alt out_act : Option (S.Node → Bool)) : Prop :=
  ∀ out : Option (S.Node → Bool), out ≠ out_alt → out = out_act

/-- LEMMA (Binary Contrast Space Entails Polarity Alternative Representation):
Demonstrates that in a binary contrast space, the contradictory negation of the determined outcome
strictly entails and represents the actual-world alternative outcome.
(0 axioms). -/
theorem binary_contrast_space_entails_polarity_alternative
    (S : ConcreteSystem.{u})
    (w_alt : S.World)
    (out_alt out_act : Option (S.Node → Bool))
    (hBinary : BinaryContrastSpace S w_alt out_alt out_act) :
    RepresentsAlternativeOutcome S w_alt out_act (¬ OutcomeAt S w_alt out_alt) := by
  intro hNotOutAlt
  dsimp [OutcomeAt] at *
  exact hBinary (SystemOutcomeAt S w_alt) hNotOutAlt

end OntologicalIncompleteness
end Logos
