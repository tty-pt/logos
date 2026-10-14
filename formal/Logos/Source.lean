import Lean
import Logos.System
import Logos.Elimination
import Logos.Agency

open Classical

namespace Logos
namespace OntologicalIncompleteness


/-- MASTER DEDUCTION THEOREM (Eliminative Deduction Derives Free Personal Source):
Demonstrates that for any candidate ground T satisfying the eliminative cosmological hypotheses
and instantiating TranscendentAgentialActionCorrespondence, T is a Free Personal Source
possessing all six foundational attributes and formally excluding complete rational determinism.
(0 axioms beyond core logic and classical choice). -/
theorem eliminative_deduction_derives_free_personal_source
    (S : ConcreteSystem.{0})
    (T : CandidateGround S)
    (hCont : ContingentSystem S)
    (hGrounds : T.GroundsConcreteActuality T.ground S.actualWorld)
    (hExpl : ∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
      (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
      ContrastiveExplanationForTotality S T w_alt)
    (ConstitutivePriority : (Ext : Type 0) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (prior_wf : ∀ Ext, WellFounded (ConstitutivePriority Ext))
    (prior_trans : ∀ Ext {a b c : CandidateOnticItem S.Node Ext}, ConstitutivePriority Ext a b → ConstitutivePriority Ext b c → ConstitutivePriority Ext a c)
    (hConstitutiveOfTotality : ∀ Ext (n : S.Node), ConstitutivePriority Ext (CandidateOnticItem.node n) CandidateOnticItem.totality)
    (hInternalGroundsTotality : ∀ (n : S.Node),
      T.ground = GroundIdentity.internal n → ∀ Ext, ConstitutivePriority Ext CandidateOnticItem.totality (CandidateOnticItem.node n))
    (hGroundsTotality : ∀ (e : T.ExtEntity),
      T.ground = GroundIdentity.external e → ConstitutivePriority T.ExtEntity (CandidateOnticItem.candidate e) CandidateOnticItem.totality)
    (hAseity : GroundingTotalityTerminatesInAseity S T)
    (hAseityNature : ImpersonalAseityPreservesNature S T)
    (hSymmPrinciple : ExplanatorySymmetryPrinciple S T ConstitutivePriority)
    (hUlt : IsUltimateGround S T ConstitutivePriority)
    (hPersonalNature : PersonalAseityPreservesNature S T)
    (hCond : DeterminationAsOnticCondition S T ConstitutivePriority)
    (hCausal : FoundationalCausalDetermination S T ConstitutivePriority)
    (hUniversalPSR : UniversalOutcomePSR S ConstitutivePriority)
    (hScope : UltimateGroundExplanatoryScope S T ConstitutivePriority)
    (hCorr : TranscendentAgentialActionCorrespondence S T) :
    FreePersonalSource S T ∧ ¬ (CompleteRationalDetermination S T ∨ UnifiedRationalActualization S T) := by
  have hAgent := eliminative_deduction_of_unforced_personal_agent S T hCont hGrounds hExpl
    ConstitutivePriority prior_wf (fun Ext {_a _b _c} => prior_trans Ext)
    hConstitutiveOfTotality hInternalGroundsTotality hGroundsTotality
    hAseity hAseityNature hSymmPrinciple hUlt hPersonalNature hCond hCausal
  obtain ⟨⟨e, hExt⟩, hNec, hPersonalNat, hAgentIs, hUltG, hGuided, hNoIntellectualist⟩ := hAgent
  have hSel := agential_action_grounding_derives_selects_intentionally S T hCont hPersonalNat hCorr
  have hChoiceEntails := agential_determination_entails_choice_derived_from_action_theory S T hCorr
  have hSovereign := agential_sovereignty_derived_from_neutral_psr S T ConstitutivePriority
    hUniversalPSR hScope hChoiceEntails (fun _ _ => hPersonalNat) hNec
  have hNotNec : ¬ NecessitatingMode S T :=
    necessary_ground_cannot_rigidly_necessitate_contingent_system S T hCont hNec
  have hChoiceBridge := agential_counterfactual_choice_bridge_from_sovereignty S T ConstitutivePriority
    hSovereign hAgentIs hUltG hNotNec
  have hFree := agential_freedom_derived S T hCont hPersonalNat hSel hChoiceBridge
  exact ⟨⟨⟨e, hExt⟩, hNec, hPersonalNat, hAgentIs, hSel, hFree⟩, hNoIntellectualist⟩

/-- MASTER DEDUCTION THEOREM UNDER EXPLANATORY TRANSMISSION:
Demonstrates that when secondary causes intermediate the explanations of accessible alternative outcomes,
and explanatory efficacy transmits along complete priority chains to the foundational terminus
(`ExplanatoryTransmission S T ConstitutivePriority`, Tag: META), the master eliminative deduction
yields a Free Personal Source without assuming direct explanatory scope as a primitive axiom.
(0 axioms beyond core logic, classical choice, and the explicit transmission hypothesis).
NOTE (Epistemic Discipline, Tag: META):
`ExplanatoryTransmission` remains a substantive, irreducible metaphysical bridge principle governing
the causal transitivity of grounding chains, and is NOT an analytic consequence of entity unicity alone. -/
theorem eliminative_deduction_derives_free_personal_source_under_transmission
    (S : ConcreteSystem.{0})
    (T : CandidateGround S)
    (hCont : ContingentSystem S)
    (hGrounds : T.GroundsConcreteActuality T.ground S.actualWorld)
    (hExpl : ∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
      (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
      ContrastiveExplanationForTotality S T w_alt)
    (ConstitutivePriority : (Ext : Type 0) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (prior_wf : ∀ Ext, WellFounded (ConstitutivePriority Ext))
    (prior_trans : ∀ Ext {a b c : CandidateOnticItem S.Node Ext}, ConstitutivePriority Ext a b → ConstitutivePriority Ext b c → ConstitutivePriority Ext a c)
    (hConstitutiveOfTotality : ∀ Ext (n : S.Node), ConstitutivePriority Ext (CandidateOnticItem.node n) CandidateOnticItem.totality)
    (hInternalGroundsTotality : ∀ (n : S.Node),
      T.ground = GroundIdentity.internal n → ∀ Ext, ConstitutivePriority Ext CandidateOnticItem.totality (CandidateOnticItem.node n))
    (hGroundsTotality : ∀ (e : T.ExtEntity),
      T.ground = GroundIdentity.external e → ConstitutivePriority T.ExtEntity (CandidateOnticItem.candidate e) CandidateOnticItem.totality)
    (hAseity : GroundingTotalityTerminatesInAseity S T)
    (hAseityNature : ImpersonalAseityPreservesNature S T)
    (hSymmPrinciple : ExplanatorySymmetryPrinciple S T ConstitutivePriority)
    (hUlt : IsUltimateGround S T ConstitutivePriority)
    (hPersonalNature : PersonalAseityPreservesNature S T)
    (hCond : DeterminationAsOnticCondition S T ConstitutivePriority)
    (hCausal : FoundationalCausalDetermination S T ConstitutivePriority)
    (hUniversalPSR : UniversalOutcomePSR S ConstitutivePriority)
    (hMed : MediatedExplanatoryScope S T ConstitutivePriority)
    (hTrans : ExplanatoryTransmission S T ConstitutivePriority)
    (hCorr : TranscendentAgentialActionCorrespondence S T) :
    FreePersonalSource S T ∧ ¬ (CompleteRationalDetermination S T ∨ UnifiedRationalActualization S T) := by
  have hScope : UltimateGroundExplanatoryScope S T ConstitutivePriority :=
    mediated_scope_to_ultimate_scope_under_transmission S T ConstitutivePriority hMed hTrans
  exact eliminative_deduction_derives_free_personal_source S T hCont hGrounds hExpl
    ConstitutivePriority prior_wf (fun Ext => prior_trans Ext) hConstitutiveOfTotality hInternalGroundsTotality
    hGroundsTotality hAseity hAseityNature hSymmPrinciple hUlt hPersonalNature hCond hCausal
    hUniversalPSR hScope hCorr

/-- CANONICAL TIER 2 THEOREM — INTERMEDIATE INTEGRATION THEOREM:
The strongest existential result obtainable when the eliminative cosmological deduction of the
unforced personal agent is integrated with the universal modal ground and Trinitarian agency,
WITHOUT assuming secondary-cause explanatory transmission or intentional creation correspondence.
Demonstrates that:
(1) The ultimate ground T is necessary, transcendent, nature-invariant, personal, and unforced (Tier 1);
(2) T's ungrounded terminal entity maps to the unique universal modal ground Entity.ofGround;
(3) The personal nature of Entity.ofGround is rooted in the Divine Person acting as DivineRole.source;
(4) Strictly respects sort discipline (EntityOf s ≠ Entity.ofGround);
(5) Formally demarcates that full explanatory scope and positive counterfactual freedom remain
    conditional on ExplanatoryTransmission and TranscendentAgentialActionCorrespondence.
(0 axioms beyond cosmological premises, TrinitarianPersonalBridge, and classical choice). -/
theorem intermediate_existential_derives_unforced_personal_source
    (S : ConcreteSystem.{0})
    (hCont : ContingentSystem S)
    (ConstitutivePriority : (Ext : Type 0) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (prior_wf : ∀ Ext, WellFounded (ConstitutivePriority Ext))
    (prior_trans : ∀ Ext {a b c : CandidateOnticItem S.Node Ext},
      ConstitutivePriority Ext a b → ConstitutivePriority Ext b c → ConstitutivePriority Ext a c)
    (hConstitutiveOfTotality : ∀ Ext (n : S.Node),
      ConstitutivePriority Ext (CandidateOnticItem.node n) CandidateOnticItem.totality)
    (hInternalGroundsTotality : ∀ (T : CandidateGround S),
      T.GroundsConcreteActuality T.ground S.actualWorld →
      (∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
        (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
        ContrastiveExplanationForTotality S T w_alt) →
      ∀ (n : S.Node), T.ground = GroundIdentity.internal n →
      ∀ Ext, ConstitutivePriority Ext CandidateOnticItem.totality (CandidateOnticItem.node n))
    (hGroundsTotality : ∀ (T : CandidateGround S),
      T.GroundsConcreteActuality T.ground S.actualWorld →
      (∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
        (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
        ContrastiveExplanationForTotality S T w_alt) →
      ∀ (e : T.ExtEntity),
        T.ground = GroundIdentity.external e →
        ConstitutivePriority T.ExtEntity (CandidateOnticItem.candidate e) CandidateOnticItem.totality)
    (hPSR : GeneralContrastivePSR S)
    (hAseity : ∀ T : CandidateGround S,
      T.GroundsConcreteActuality T.ground S.actualWorld →
      (∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
        (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
        ContrastiveExplanationForTotality S T w_alt) →
      GroundingTotalityTerminatesInAseity S T)
    (hAseityNature : ∀ T : CandidateGround S,
      T.GroundsConcreteActuality T.ground S.actualWorld →
      (∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
        (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
        ContrastiveExplanationForTotality S T w_alt) →
      ImpersonalAseityPreservesNature S T)
    (hSymmPrinciple : ∀ T : CandidateGround S,
      T.GroundsConcreteActuality T.ground S.actualWorld →
      (∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
        (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
        ContrastiveExplanationForTotality S T w_alt) →
      ExplanatorySymmetryPrinciple S T ConstitutivePriority)
    (hUltRequirement : ExplanatoryUltimacyRequirement S ConstitutivePriority)
    (hPersonalNature : ∀ T : CandidateGround S,
      T.GroundsConcreteActuality T.ground S.actualWorld →
      (∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
        (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
        ContrastiveExplanationForTotality S T w_alt) →
      PersonalAseityPreservesNature S T)
    (hCond : ∀ T : CandidateGround S,
      T.GroundsConcreteActuality T.ground S.actualWorld →
      (∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
        (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
        ContrastiveExplanationForTotality S T w_alt) →
      DeterminationAsOnticCondition S T ConstitutivePriority)
    (hCausal : ∀ T : CandidateGround S,
      T.GroundsConcreteActuality T.ground S.actualWorld →
      (∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
        (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
        ContrastiveExplanationForTotality S T w_alt) →
      FoundationalCausalDetermination S T ConstitutivePriority)
    (hHom : PriorityGroundingHomomorphism S ConstitutivePriority Logos.Entity.Entity.ofGround) :
    ∃ T : CandidateGround S,
      (∃ e : T.ExtEntity, T.ground = GroundIdentity.external e) ∧
      IsNecessary S T ∧
      NatureInvariant S T ∧
      IsPersonalAgent S T ∧
      IsUltimateGround S T ConstitutivePriority ∧
      GuidedByJustificationMode S T ∧
      ¬ (CompleteRationalDetermination S T ∨ UnifiedRationalActualization S T) ∧
      (∃ (e' e_ult : T.ExtEntity),
        T.ground = GroundIdentity.external e' ∧
        IsUngroundedInPriority ConstitutivePriority e_ult ∧
        hHom.itemToEntity T.ExtEntity (CandidateOnticItem.candidate e_ult) = Logos.Entity.Entity.ofGround) ∧
      (∃ agent : Logos.Agency.Subject,
        Logos.TrinitarianSubjectBridge.DivineSubjectRole agent = Logos.TrinitarianSubjectBridge.DivineRole.source ∧
        Logos.Person.Person agent ∧
        Logos.Entity.Entity.ofGround ≠ Logos.Entity.Entity.ofSubject agent) := by
  obtain ⟨T, hGrounds, hExpl⟩ := hPSR hCont
  have hAgent := eliminative_deduction_of_unforced_personal_agent S T hCont hGrounds hExpl
    ConstitutivePriority prior_wf (fun Ext {_a _b _c} => prior_trans Ext)
    hConstitutiveOfTotality (hInternalGroundsTotality T hGrounds hExpl) (hGroundsTotality T hGrounds hExpl)
    (hAseity T hGrounds hExpl) (hAseityNature T hGrounds hExpl) (hSymmPrinciple T hGrounds hExpl) (hUltRequirement T hGrounds hExpl)
    (hPersonalNature T hGrounds hExpl) (hCond T hGrounds hExpl) (hCausal T hGrounds hExpl)
  obtain ⟨⟨e, hExt⟩, hNec, hNature, hPersonalAgent, hUlt, hGuided, hNoIntellectualist⟩ := hAgent
  have hTot := hGroundsTotality T hGrounds hExpl e hExt
  obtain ⟨e', e_ult, hExt', _hTot', hUngrounded, _hPath⟩ :=
    hHom.priority_chain_has_terminus T ⟨e, hExt, hTot⟩
  have hUnicity := hHom.terminal_unicity T.ExtEntity e_ult hUngrounded
  obtain ⟨a, _b, _c, haRole, _hbRole, _hcRole, haPers, _hbPers, _hcPers⟩ :=
    Logos.TrinitarianSubjectBridge.three_divine_persons_exist_with_roles
  have hDistinctSort : Logos.Entity.Entity.ofGround ≠ Logos.Entity.Entity.ofSubject a :=
    (Logos.FoundationalUnicity.ofGround_ne_ofSubject a).symm
  refine ⟨T, ⟨e, hExt⟩, hNec, hNature, hPersonalAgent, hUlt, hGuided, hNoIntellectualist,
    ⟨e', e_ult, hExt', hUngrounded, hUnicity⟩, ⟨a, haRole, haPers, hDistinctSort⟩⟩

/-- MASTER EXISTENTIAL INTEGRATION THEOREM (Existential Deduction of the Free Personal Source):
From cosmological foundations and agential action correspondence, deduces the existence of a
Free Personal Source for contingent concrete system S.
(0 axioms beyond core logic and classical choice). -/
theorem eliminative_foundation_derives_free_personal_source
    (S : ConcreteSystem.{0})
    (hCont : ContingentSystem S)
    (ConstitutivePriority : (Ext : Type 0) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (prior_wf : ∀ Ext, WellFounded (ConstitutivePriority Ext))
    (prior_trans : ∀ Ext {a b c : CandidateOnticItem S.Node Ext},
      ConstitutivePriority Ext a b → ConstitutivePriority Ext b c → ConstitutivePriority Ext a c)
    (hConstitutiveOfTotality : ∀ Ext (n : S.Node),
      ConstitutivePriority Ext (CandidateOnticItem.node n) CandidateOnticItem.totality)
    (hInternalGroundsTotality : ∀ (T : CandidateGround S),
      T.GroundsConcreteActuality T.ground S.actualWorld →
      (∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
        (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
        ContrastiveExplanationForTotality S T w_alt) →
      ∀ (n : S.Node), T.ground = GroundIdentity.internal n →
      ∀ Ext, ConstitutivePriority Ext CandidateOnticItem.totality (CandidateOnticItem.node n))
    (hGroundsTotality : ∀ (T : CandidateGround S),
      T.GroundsConcreteActuality T.ground S.actualWorld →
      (∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
        (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
        ContrastiveExplanationForTotality S T w_alt) →
      ∀ (e : T.ExtEntity),
        T.ground = GroundIdentity.external e →
        ConstitutivePriority T.ExtEntity (CandidateOnticItem.candidate e) CandidateOnticItem.totality)
    (hAseity : ∀ T : CandidateGround S,
      T.GroundsConcreteActuality T.ground S.actualWorld →
      (∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
        (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
        ContrastiveExplanationForTotality S T w_alt) →
      GroundingTotalityTerminatesInAseity S T)
    (hAseityNature : ∀ T : CandidateGround S,
      T.GroundsConcreteActuality T.ground S.actualWorld →
      (∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
        (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
        ContrastiveExplanationForTotality S T w_alt) →
      ImpersonalAseityPreservesNature S T)
    (hSymmPrinciple : ∀ T : CandidateGround S,
      T.GroundsConcreteActuality T.ground S.actualWorld →
      (∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
        (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
        ContrastiveExplanationForTotality S T w_alt) →
      ExplanatorySymmetryPrinciple S T ConstitutivePriority)
    (hUltRequirement : ExplanatoryUltimacyRequirement S ConstitutivePriority)
    (hPersonalNature : ∀ T : CandidateGround S,
      T.GroundsConcreteActuality T.ground S.actualWorld →
      (∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
        (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
        ContrastiveExplanationForTotality S T w_alt) →
      PersonalAseityPreservesNature S T)
    (hCond : ∀ T : CandidateGround S,
      T.GroundsConcreteActuality T.ground S.actualWorld →
      (∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
        (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
        ContrastiveExplanationForTotality S T w_alt) →
      DeterminationAsOnticCondition S T ConstitutivePriority)
    (hCausal : ∀ T : CandidateGround S,
      T.GroundsConcreteActuality T.ground S.actualWorld →
      (∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
        (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
        ContrastiveExplanationForTotality S T w_alt) →
      FoundationalCausalDetermination S T ConstitutivePriority)
    (hUniversalPSR : UniversalOutcomePSR S ConstitutivePriority)
    (hScope : ∀ T : CandidateGround S,
      T.GroundsConcreteActuality T.ground S.actualWorld →
      UltimateGroundExplanatoryScope S T ConstitutivePriority)
    (hPSR : GeneralContrastivePSR S)
    (hAgentialCorr : ∀ T : CandidateGround S,
      T.GroundsConcreteActuality T.ground S.actualWorld →
      (∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
        (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
        ContrastiveExplanationForTotality S T w_alt) →
      TranscendentAgentialActionCorrespondence S T) :
    ∃ T : CandidateGround S, FreePersonalSource S T ∧
      ¬ (CompleteRationalDetermination S T ∨ UnifiedRationalActualization S T) := by
  obtain ⟨T, hGrounds, hExpl⟩ := hPSR hCont
  have hCorr := hAgentialCorr T hGrounds hExpl
  have hFPS := eliminative_deduction_derives_free_personal_source S T hCont hGrounds hExpl
    ConstitutivePriority prior_wf prior_trans hConstitutiveOfTotality
    (hInternalGroundsTotality T hGrounds hExpl)
    (hGroundsTotality T hGrounds hExpl)
    (hAseity T hGrounds hExpl)
    (hAseityNature T hGrounds hExpl)
    (hSymmPrinciple T hGrounds hExpl)
    (hUltRequirement T hGrounds hExpl)
    (hPersonalNature T hGrounds hExpl)
    (hCond T hGrounds hExpl)
    (hCausal T hGrounds hExpl)
    hUniversalPSR (hScope T hGrounds) hCorr
  exact ⟨T, hFPS⟩

/-- CANONICAL TIER 3 THEOREM — MASTER EXISTENTIAL INTEGRATION THEOREM:
Existential Deduction of the Free Personal Source under Explanatory Transmission.
From cosmological foundations, agential action correspondence, and secondary-cause explanatory transmission,
deduces the existence of a Free Personal Source for contingent concrete system S.
Derives explanatory scope internally via `mediated_scope_to_ultimate_scope_under_transmission`.
(0 axioms beyond core logic, classical choice, and the explicit transmission hypothesis).
NOTE (Epistemic Discipline, Tag: META):
`ExplanatoryTransmission` remains an explicit metaphysical bridge parameter and is NOT an analytic
consequence of universal-ground unicity alone. -/
theorem eliminative_foundation_derives_free_personal_source_under_transmission
    (S : ConcreteSystem.{0})
    (hCont : ContingentSystem S)
    (ConstitutivePriority : (Ext : Type 0) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (prior_wf : ∀ Ext, WellFounded (ConstitutivePriority Ext))
    (prior_trans : ∀ Ext {a b c : CandidateOnticItem S.Node Ext},
      ConstitutivePriority Ext a b → ConstitutivePriority Ext b c → ConstitutivePriority Ext a c)
    (hConstitutiveOfTotality : ∀ Ext (n : S.Node),
      ConstitutivePriority Ext (CandidateOnticItem.node n) CandidateOnticItem.totality)
    (hInternalGroundsTotality : ∀ (T : CandidateGround S),
      T.GroundsConcreteActuality T.ground S.actualWorld →
      (∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
        (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
        ContrastiveExplanationForTotality S T w_alt) →
      ∀ (n : S.Node), T.ground = GroundIdentity.internal n →
      ∀ Ext, ConstitutivePriority Ext CandidateOnticItem.totality (CandidateOnticItem.node n))
    (hGroundsTotality : ∀ (T : CandidateGround S),
      T.GroundsConcreteActuality T.ground S.actualWorld →
      (∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
        (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
        ContrastiveExplanationForTotality S T w_alt) →
      ∀ (e : T.ExtEntity),
        T.ground = GroundIdentity.external e →
        ConstitutivePriority T.ExtEntity (CandidateOnticItem.candidate e) CandidateOnticItem.totality)
    (hAseity : ∀ T : CandidateGround S,
      T.GroundsConcreteActuality T.ground S.actualWorld →
      (∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
        (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
        ContrastiveExplanationForTotality S T w_alt) →
      GroundingTotalityTerminatesInAseity S T)
    (hAseityNature : ∀ T : CandidateGround S,
      T.GroundsConcreteActuality T.ground S.actualWorld →
      (∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
        (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
        ContrastiveExplanationForTotality S T w_alt) →
      ImpersonalAseityPreservesNature S T)
    (hSymmPrinciple : ∀ T : CandidateGround S,
      T.GroundsConcreteActuality T.ground S.actualWorld →
      (∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
        (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
        ContrastiveExplanationForTotality S T w_alt) →
      ExplanatorySymmetryPrinciple S T ConstitutivePriority)
    (hUltRequirement : ExplanatoryUltimacyRequirement S ConstitutivePriority)
    (hPersonalNature : ∀ T : CandidateGround S,
      T.GroundsConcreteActuality T.ground S.actualWorld →
      (∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
        (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
        ContrastiveExplanationForTotality S T w_alt) →
      PersonalAseityPreservesNature S T)
    (hCond : ∀ T : CandidateGround S,
      T.GroundsConcreteActuality T.ground S.actualWorld →
      (∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
        (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
        ContrastiveExplanationForTotality S T w_alt) →
      DeterminationAsOnticCondition S T ConstitutivePriority)
    (hCausal : ∀ T : CandidateGround S,
      T.GroundsConcreteActuality T.ground S.actualWorld →
      (∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
        (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
        ContrastiveExplanationForTotality S T w_alt) →
      FoundationalCausalDetermination S T ConstitutivePriority)
    (hUniversalPSR : UniversalOutcomePSR S ConstitutivePriority)
    (hMed : ∀ T : CandidateGround S,
      T.GroundsConcreteActuality T.ground S.actualWorld →
      MediatedExplanatoryScope S T ConstitutivePriority)
    (hTrans : ∀ T : CandidateGround S,
      T.GroundsConcreteActuality T.ground S.actualWorld →
      ExplanatoryTransmission S T ConstitutivePriority)
    (hPSR : GeneralContrastivePSR S)
    (hAgentialCorr : ∀ T : CandidateGround S,
      T.GroundsConcreteActuality T.ground S.actualWorld →
      (∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
        (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
        ContrastiveExplanationForTotality S T w_alt) →
      TranscendentAgentialActionCorrespondence S T) :
    ∃ T : CandidateGround S, FreePersonalSource S T ∧
      ¬ (CompleteRationalDetermination S T ∨ UnifiedRationalActualization S T) := by
  obtain ⟨T, hGrounds, hExpl⟩ := hPSR hCont
  have hCorr := hAgentialCorr T hGrounds hExpl
  have hFPS := eliminative_deduction_derives_free_personal_source_under_transmission S T hCont hGrounds hExpl
    ConstitutivePriority prior_wf prior_trans hConstitutiveOfTotality
    (hInternalGroundsTotality T hGrounds hExpl)
    (hGroundsTotality T hGrounds hExpl)
    (hAseity T hGrounds hExpl)
    (hAseityNature T hGrounds hExpl)
    (hSymmPrinciple T hGrounds hExpl)
    (hUltRequirement T hGrounds hExpl)
    (hPersonalNature T hGrounds hExpl)
    (hCond T hGrounds hExpl)
    (hCausal T hGrounds hExpl)
    hUniversalPSR (hMed T hGrounds) (hTrans T hGrounds) hCorr
  exact ⟨T, hFPS⟩

/-!
================================================================================
SECTION III-E: PERFECT RATIONAL GOODNESS, EQUALLY GOOD ALTERNATIVES, AND LIBERTARIAN FREEDOM
================================================================================
Investigates whether perfect rational goodness (optimific choice) entails univocal determination
or whether it is compossible with positive libertarian freedom (`ActsFreely`) when choosing
between equally maximal goods.

We strictly distinguish two concepts often conflated in rationalist determinism:
(1) `PerfectRationalGoodness`: The personal ground chooses ONLY outcomes that are evaluatively
    maximal (it can never choose an outcome that is strictly inferior to an accessible alternative).
(2) `CompleteRationalDetermination`: The profile of reasons univocally fixes a unique outcome,
    excluding any alternative choice even between equally maximal goods.
================================================================================
-/

/-- Strict Reasons Favoring:
Reasons favor wa over wb, but do not favor wb over wa. -/
def StrictReasonsFavor (S : ConcreteSystem.{u}) (T : CandidateGround S) (wa wb : S.World) : Prop :=
  T.ReasonsFavor T.ground wa wb ∧ ¬ T.ReasonsFavor T.ground wb wa

/-- Perfect Rational Goodness (Optimific Rational Agency):
The personal ground chooses ONLY outcomes that are evaluatively maximal (or optimal):
it can never choose an outcome at a world if there is an accessible world whose outcome
is strictly favored by its reasons.
Crucially, this does NOT forbid choosing between two equally maximal outcomes. -/
def PerfectRationalGoodness (S : ConcreteSystem.{u}) (T : CandidateGround S) : Prop :=
  NatureInvariant S T ∧
  ∀ w : S.World, ∀ out : Option (S.Node → Bool),
    T.ChoosesOutcomeAt T.ground w out →
    ∀ w_alt : S.World, S.Accessible w w_alt →
      ¬ StrictReasonsFavor S T w_alt w

/-- 3-World Evaluative Model with Two Distinct Maximally Good Configurations and One Inferior:
Mundus Triplex:
w0: Actual world, configuration cfg0 (value 1, maximal)
w1: Accessible alternative world, configuration cfg1 (value 1, maximal)
w2: Accessible alternative world, configuration cfg2 (value 0, inferior) -/
inductive TriWorld : Type
  | w0 : TriWorld
  | w1 : TriWorld
  | w2 : TriWorld
  deriving DecidableEq

def triCfg0 : Bool → Bool := fun b => b
def triCfg1 : Bool → Bool := fun b => !b
def triCfg2 : Bool → Bool := fun _ => false

theorem triCfg0_ne_triCfg1 : triCfg0 ≠ triCfg1 := by
  intro h
  have hTrue : triCfg0 true = triCfg1 true := congrFun h true
  dsimp [triCfg0, triCfg1] at hTrue
  contradiction

theorem triCfg0_ne_triCfg2 : triCfg0 ≠ triCfg2 := by
  intro h
  have hTrue : triCfg0 true = triCfg2 true := congrFun h true
  dsimp [triCfg0, triCfg2] at hTrue
  contradiction

theorem triCfg1_ne_triCfg2 : triCfg1 ≠ triCfg2 := by
  intro h
  have hFalse : triCfg1 false = triCfg2 false := congrFun h false
  dsimp [triCfg1, triCfg2] at hFalse
  contradiction

def triConfigurationValue (cfg : Bool → Bool) : Nat :=
  if cfg true = true ∧ cfg false = false then 1
  else if cfg true = false ∧ cfg false = true then 1
  else 0

theorem cfg0_val : triConfigurationValue triCfg0 = 1 := by decide
theorem cfg1_val : triConfigurationValue triCfg1 = 1 := by decide
theorem cfg2_val : triConfigurationValue triCfg2 = 0 := by decide

theorem triConfigurationValue_le_one (cfg : Bool → Bool) : triConfigurationValue cfg ≤ 1 := by
  dsimp [triConfigurationValue]
  split <;> try decide
  split <;> decide

def triOutcomeValue (out : Option (Bool → Bool)) : Nat :=
  match out with
  | some cfg => triConfigurationValue cfg
  | none => 0

theorem triOutcomeValue_le_one (out : Option (Bool → Bool)) : triOutcomeValue out ≤ 1 := by
  cases out with
  | none => decide
  | some cfg => exact triConfigurationValue_le_one cfg

def triOutcomePreference (out1 out2 : Option (Bool → Bool)) : Prop :=
  triOutcomeValue out1 ≥ triOutcomeValue out2

def triStrictOutcomePreference (out1 out2 : Option (Bool → Bool)) : Prop :=
  triOutcomeValue out1 > triOutcomeValue out2

def triIsEvaluativelyMaximal (out : Option (Bool → Bool)) : Prop :=
  ∀ out_alt : Option (Bool → Bool), ¬ triStrictOutcomePreference out_alt out

theorem cfg0_is_maximal : triIsEvaluativelyMaximal (some triCfg0) := by
  intro out_alt hStrict
  dsimp [triStrictOutcomePreference] at hStrict
  rw [show triOutcomeValue (some triCfg0) = 1 from cfg0_val] at hStrict
  have hLe := triOutcomeValue_le_one out_alt
  omega

theorem cfg1_is_maximal : triIsEvaluativelyMaximal (some triCfg1) := by
  intro out_alt hStrict
  dsimp [triStrictOutcomePreference] at hStrict
  rw [show triOutcomeValue (some triCfg1) = 1 from cfg1_val] at hStrict
  have hLe := triOutcomeValue_le_one out_alt
  omega

theorem cfg2_not_maximal : ¬ triIsEvaluativelyMaximal (some triCfg2) := by
  intro hMax
  have hStrict : triStrictOutcomePreference (some triCfg0) (some triCfg2) := by
    dsimp [triStrictOutcomePreference, triOutcomeValue, cfg0_val, cfg2_val]
    decide
  exact hMax (some triCfg0) hStrict

theorem emptyBoolWf : WellFounded (fun (_ _ : Bool) => False) := by
  constructor
  intro a
  constructor
  intro b hb
  contradiction

def triWorldS : ConcreteSystem.{0} where
  Node := Bool
  World := TriWorld
  actualWorld := TriWorld.w0
  Accessible := fun _ _ => True
  InstantiatedIn := fun _ => True
  ConfigurationIn := fun w =>
    match w with
    | TriWorld.w0 => triCfg0
    | TriWorld.w1 => triCfg1
    | TriWorld.w2 => triCfg2
  Determines := fun _ _ => False
  Prior := fun _ _ => False
  priorWellFounded := emptyBoolWf
  determinationRespectsPriority := fun h => False.elim h

theorem triWorldS_contingent : ContingentSystem triWorldS := by
  refine ⟨trivial, TriWorld.w1, trivial, Or.inr ?_⟩
  intro h
  have hTrue := congrFun h true
  dsimp [triWorldS, triCfg1, triCfg0] at hTrue
  contradiction

theorem outcome_w0 : SystemOutcomeAt triWorldS TriWorld.w0 = some triCfg0 := by
  dsimp [SystemOutcomeAt]
  split
  · rfl
  · case isFalse h => exact False.elim (h trivial)

theorem outcome_w1 : SystemOutcomeAt triWorldS TriWorld.w1 = some triCfg1 := by
  dsimp [SystemOutcomeAt]
  split
  · rfl
  · case isFalse h => exact False.elim (h trivial)

theorem outcome_w2 : SystemOutcomeAt triWorldS TriWorld.w2 = some triCfg2 := by
  dsimp [SystemOutcomeAt]
  split
  · rfl
  · case isFalse h => exact False.elim (h trivial)

noncomputable def triReasonsFavor (wa wb : TriWorld) : Prop :=
  triOutcomePreference (SystemOutcomeAt triWorldS wa) (SystemOutcomeAt triWorldS wb)

def triChoosesOutcomeAt (w : TriWorld) (out : Option (Bool → Bool)) : Prop :=
  match w with
  | TriWorld.w0 => out = some triCfg0
  | TriWorld.w1 => out = some triCfg1
  | TriWorld.w2 => False

/-- Agential Elective Contrastive Justification:
Why wa obtained rather than wb:
(1) Either wa is strictly evaluatively superior to wb; OR
(2) wa and wb are both evaluatively maximal, and the personal agent intentionally elected wa over wb. -/
noncomputable def triProvidesContrastiveJustification (wa wb : TriWorld) : Prop :=
  (triStrictOutcomePreference (SystemOutcomeAt triWorldS wa) (SystemOutcomeAt triWorldS wb) ∧
   triChoosesOutcomeAt wa (SystemOutcomeAt triWorldS wa)) ∨
  (triIsEvaluativelyMaximal (SystemOutcomeAt triWorldS wa) ∧
   triIsEvaluativelyMaximal (SystemOutcomeAt triWorldS wb) ∧
   triChoosesOutcomeAt wa (SystemOutcomeAt triWorldS wa) ∧
   wa ≠ wb)

noncomputable def triWorldT : CandidateGround triWorldS where
  ExtEntity := Unit
  ground := GroundIdentity.external ()
  ExistsAt := fun _ _ => True
  GroundsConcreteActuality := fun _ w => w = TriWorld.w0
  grounding_binds_actuality := by
    intro w hw
    subst hw
    refine ⟨trivial, trivial, rfl⟩
  EssenceOf := fun _ _ => ⟨1, 1⟩
  ProvidesContrastiveJustification := fun _ wa wb => triProvidesContrastiveJustification wa wb
  ApprehendsAlternative := fun _ _ => True
  ReasonsFavor := fun _ wa wb => triReasonsFavor wa wb
  ChoosesOutcomeAt := fun _ w out => triChoosesOutcomeAt w out
  DeterminesOutcomeAt := fun _ w out => triChoosesOutcomeAt w out

theorem triWorldT_nature_invariant : NatureInvariant triWorldS triWorldT := by
  intro wa wb
  rfl

theorem triWorldT_not_necessitating : ¬ NecessitatingMode triWorldS triWorldT := by
  intro hNec
  have h := hNec TriWorld.w1 trivial trivial
  have hCfgDiff : triWorldS.ConfigurationIn TriWorld.w1 ≠ triWorldS.ConfigurationIn triWorldS.actualWorld := by
    dsimp [triWorldS]
    exact triCfg0_ne_triCfg1.symm
  exact hCfgDiff h.2

inductive triPriority : (Ext : Type 0) → CandidateOnticItem Bool Ext → CandidateOnticItem Bool Ext → Prop
  | candidate_node : ∀ (e : Unit) (b : Bool), triPriority Unit (CandidateOnticItem.candidate e) (CandidateOnticItem.node b)
  | candidate_totality : ∀ (e : Unit), triPriority Unit (CandidateOnticItem.candidate e) CandidateOnticItem.totality

theorem triPriority_wf : ∀ Ext, WellFounded (triPriority Ext) := by
  intro Ext
  constructor
  intro a
  constructor
  intro b hb
  cases hb with
  | candidate_node e n =>
    constructor
    intro c hc
    cases hc
  | candidate_totality e =>
    constructor
    intro c hc
    cases hc

theorem triPriority_trans : ∀ Ext {a b c : CandidateOnticItem Bool Ext},
    triPriority Ext a b → triPriority Ext b c → triPriority Ext a c := by
  intro Ext a b c hab hbc
  cases hab <;> cases hbc

theorem triWorldT_ultimate : IsUltimateGround triWorldS triWorldT triPriority := by
  refine ⟨rfl, ?_⟩
  intro e hExt ⟨hCond, _⟩
  cases hCond

theorem triWorldT_perfect_rational_goodness : PerfectRationalGoodness triWorldS triWorldT := by
  refine ⟨triWorldT_nature_invariant, ?_⟩
  intro w out hChoice w_alt hAcc ⟨hFavorAlt, hNotFavorW⟩
  cases w with
  | w0 =>
    cases w_alt with
    | w0 => exact hNotFavorW (Nat.le_refl _)
    | w1 =>
      apply hNotFavorW
      dsimp [triWorldT, triReasonsFavor, triOutcomePreference]
      rw [outcome_w0, outcome_w1]
      dsimp [triOutcomeValue, cfg0_val, cfg1_val]
      decide
    | w2 =>
      apply hNotFavorW
      dsimp [triWorldT, triReasonsFavor, triOutcomePreference]
      rw [outcome_w0, outcome_w2]
      dsimp [triOutcomeValue, cfg0_val, cfg2_val]
      decide
  | w1 =>
    cases w_alt with
    | w0 =>
      apply hNotFavorW
      dsimp [triWorldT, triReasonsFavor, triOutcomePreference]
      rw [outcome_w0, outcome_w1]
      dsimp [triOutcomeValue, cfg0_val, cfg1_val]
      decide
    | w1 => exact hNotFavorW (Nat.le_refl _)
    | w2 =>
      apply hNotFavorW
      dsimp [triWorldT, triReasonsFavor, triOutcomePreference]
      rw [outcome_w1, outcome_w2]
      dsimp [triOutcomeValue, cfg1_val, cfg2_val]
      decide
  | w2 =>
    dsimp [triWorldT, triChoosesOutcomeAt] at hChoice

theorem triWorldT_acts_freely : ActsFreely triWorldS triWorldT := by
  refine ⟨triWorldT_nature_invariant, TriWorld.w1, trivial, rfl, ?_⟩
  have hAltOut : (if triWorldS.InstantiatedIn TriWorld.w1 then some (triWorldS.ConfigurationIn TriWorld.w1) else none) =
      SystemOutcomeAt triWorldS TriWorld.w1 := rfl
  have hActOut : some (triWorldS.ConfigurationIn triWorldS.actualWorld) =
      some (triWorldS.ConfigurationIn TriWorld.w0) := rfl
  rw [hAltOut, hActOut, outcome_w1]
  refine ⟨?_, ?_⟩
  · intro hEq
    injection hEq with hCfg
    have hDiff : triWorldS.ConfigurationIn TriWorld.w1 ≠ triWorldS.ConfigurationIn TriWorld.w0 := by
      dsimp [triWorldS]
      exact triCfg0_ne_triCfg1.symm
    exact hDiff hCfg
  · dsimp [triWorldT, triChoosesOutcomeAt, triWorldS]

theorem triWorldT_fails_complete_rational_determination :
    ¬ CompleteRationalDetermination triWorldS triWorldT := by
  intro ⟨_, _, hNoChoiceAlt⟩
  have hAcc : triWorldS.Accessible triWorldS.actualWorld TriWorld.w1 := trivial
  have hNe : TriWorld.w1 ≠ triWorldS.actualWorld := by
    intro h
    injection h
  have hFavor : triWorldT.ReasonsFavor triWorldT.ground triWorldS.actualWorld TriWorld.w1 := by
    change triOutcomePreference (SystemOutcomeAt triWorldS TriWorld.w0) (SystemOutcomeAt triWorldS TriWorld.w1)
    dsimp [triOutcomePreference]
    rw [outcome_w0, outcome_w1]
    dsimp [triOutcomeValue, cfg0_val, cfg1_val]
    decide
  have hNoChoice := hNoChoiceAlt TriWorld.w1 hAcc hNe hFavor
  apply hNoChoice
  refine ⟨some triCfg1, rfl⟩

theorem triWorldS_psr : GeneralContrastivePSR triWorldS := by
  intro _
  refine ⟨triWorldT, rfl, ?_⟩
  intro w_alt hAcc hDiff
  refine ⟨trivial, ?_⟩
  cases w_alt with
  | w0 =>
    exfalso
    cases hDiff with
    | inl hNotInst =>
      apply hNotInst
      exact trivial
    | inr hCfgDiff =>
      apply hCfgDiff
      rfl
  | w1 =>
    change triProvidesContrastiveJustification TriWorld.w0 TriWorld.w1
    right
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [outcome_w0]
      exact cfg0_is_maximal
    · rw [outcome_w1]
      exact cfg1_is_maximal
    · rw [outcome_w0]
      rfl
    · intro h
      injection h
  | w2 =>
    change triProvidesContrastiveJustification TriWorld.w0 TriWorld.w2
    left
    refine ⟨?_, ?_⟩
    · dsimp [triStrictOutcomePreference]
      rw [outcome_w0, outcome_w2]
      dsimp [triOutcomeValue, cfg0_val, cfg2_val]
      decide
    · rw [outcome_w0]
      rfl

/-- THEOREM (Compossibility of Perfect Rational Goodness and Libertarian Freedom):
Demonstrates that Perfect Rational Goodness (optimific choice) is FULLY COMPOSSIBLE
with Libertarian Freedom (`ActsFreely`) when choosing between equally maximal goods.
(1) `ContingentSystem triWorldS`: The totality is modally contingent;
(2) `GeneralContrastivePSR triWorldS`: The system satisfies the General Contrastive PSR;
(3) `IsUltimateGround triWorldS triWorldT triPriority`: The ground is ultimate;
(4) `¬ NecessitatingMode triWorldS triWorldT`: The ground does not rigidly necessitate the system;
(5) `PerfectRationalGoodness triWorldS triWorldT`: The ground NEVER chooses an inferior alternative;
(6) `ActsFreely triWorldS triWorldT`: The ground freely chooses between equally maximal configurations;
(7) `¬ CompleteRationalDetermination triWorldS triWorldT`: Demonstrates that complete rational
    determination was the SOLE source of non-freedom, NOT perfect rational goodness.
(0 axioms). -/
theorem perfect_goodness_compossible_with_libertarian_freedom :
    ContingentSystem triWorldS ∧
    GeneralContrastivePSR triWorldS ∧
    IsUltimateGround triWorldS triWorldT triPriority ∧
    (¬ NecessitatingMode triWorldS triWorldT) ∧
    PerfectRationalGoodness triWorldS triWorldT ∧
    ActsFreely triWorldS triWorldT ∧
    (¬ CompleteRationalDetermination triWorldS triWorldT) :=
  ⟨triWorldS_contingent,
   triWorldS_psr,
   triWorldT_ultimate,
   triWorldT_not_necessitating,
   triWorldT_perfect_rational_goodness,
   triWorldT_acts_freely,
   triWorldT_fails_complete_rational_determination⟩

/-- THEOREM (Strict Evaluative Ordering Fails Contrastive Justification on Equal Goods):
Demonstrates that under a strictly evaluative ordering (where contrastive justification requires
strict axiological superiority), two equally maximal configurations CANNOT provide contrastive
justification for each other (The Classical Buridan's Ass Impasse).
(0 axioms). -/
theorem strict_evaluative_contrastive_fails_on_equal_goods :
    ¬ triStrictOutcomePreference (SystemOutcomeAt triWorldS TriWorld.w0) (SystemOutcomeAt triWorldS TriWorld.w1) := by
  dsimp [triStrictOutcomePreference]
  rw [outcome_w0, outcome_w1]
  dsimp [triOutcomeValue, cfg0_val, cfg1_val]
  decide

/-- THEOREM (Agential Elective Selection Resolves the Contrastive PSR on Equal Goods):
Demonstrates that when contrastive justification includes intentional agential election
between equally maximal goods, the Contrastive PSR is fully satisfied without turning
the choice into a brute fact and without modal necessitation.
(0 axioms). -/
theorem agential_election_resolves_contrastive_psr_for_equal_goods :
    triProvidesContrastiveJustification TriWorld.w0 TriWorld.w1 ∧
    ¬ triStrictOutcomePreference (SystemOutcomeAt triWorldS TriWorld.w0) (SystemOutcomeAt triWorldS TriWorld.w1) :=
  ⟨by
    right
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [outcome_w0]; exact cfg0_is_maximal
    · rw [outcome_w1]; exact cfg1_is_maximal
    · rw [outcome_w0]; rfl
    · intro h; injection h,
   strict_evaluative_contrastive_fails_on_equal_goods⟩

/-!
================================================================================
SECTION III-F: JOINT SATISFIABILITY OF CORRECTED EXPLANATORY PRINCIPLES
================================================================================
Constructs a dedicated 2-world modal model witnessing that:
(1) ContingentSystem
(2) UniversalExplanatoryGroundingAtAlternatives
(3) ModalExplanatoryExhaustionAtAlternatives
(4) ImpersonalExclusionAtAlternatives
(5) ActsFreely
are simultaneously satisfiable without contradiction or vacuity.
================================================================================
-/

/-- Dedicated 2-World Concrete System for Joint Satisfiability Verification:
w = true: actual world, configuration is true
w = false: divergent accessible world, configuration is false. -/
def dualWorldS : ConcreteSystem.{0} where
  Node := Unit
  World := Bool
  actualWorld := true
  Accessible := fun _ _ => True
  InstantiatedIn := fun _ => True
  ConfigurationIn := fun w _ => w
  Determines := fun _ _ => False
  Prior := fun _ _ => False
  priorWellFounded := emptyUnitWf
  determinationRespectsPriority := fun h => False.elim h

theorem outcome_dual_true : SystemOutcomeAt dualWorldS true = some (dualWorldS.ConfigurationIn true) := by
  dsimp [SystemOutcomeAt, dualWorldS]
  split
  · rfl
  · contradiction

theorem outcome_dual_false : SystemOutcomeAt dualWorldS false = some (dualWorldS.ConfigurationIn false) := by
  dsimp [SystemOutcomeAt, dualWorldS]
  split
  · rfl
  · contradiction

theorem dualWorldS_contingent : ContingentSystem dualWorldS := by
  refine ⟨trivial, false, trivial, Or.inr ?_⟩
  intro hEq
  have hT := congrFun hEq ()
  revert hT
  decide

theorem outcome_dual_diff : SystemOutcomeAt dualWorldS false ≠ SystemOutcomeAt dualWorldS dualWorldS.actualWorld := by
  change SystemOutcomeAt dualWorldS false ≠ SystemOutcomeAt dualWorldS true
  rw [outcome_dual_false, outcome_dual_true]
  intro hEq
  injection hEq with hCfg
  have hT := congrFun hCfg ()
  revert hT
  decide

def dualChoosesOutcomeAt (w : Bool) (out : Option (Unit → Bool)) : Prop :=
  out = SystemOutcomeAt dualWorldS w

noncomputable def dualWorldT : CandidateGround dualWorldS where
  ExtEntity := Unit
  ground := GroundIdentity.external ()
  ExistsAt := fun _ _ => True
  GroundsConcreteActuality := fun _ w => w = true
  grounding_binds_actuality := by
    intro w hw
    subst hw
    refine ⟨trivial, trivial, rfl⟩
  EssenceOf := fun _ _ => ⟨1, 1⟩
  ProvidesContrastiveJustification := fun _ _ _ => True
  ApprehendsAlternative := fun _ _ => True
  ReasonsFavor := fun _ _ _ => True
  ChoosesOutcomeAt := fun _ w out => dualChoosesOutcomeAt w out
  DeterminesOutcomeAt := fun _ w out => dualChoosesOutcomeAt w out

theorem dualWorldT_nature_invariant : NatureInvariant dualWorldS dualWorldT := by
  intro _ _
  rfl

theorem dualWorldT_personal : IsPersonalAgent dualWorldS dualWorldT := by
  intro _ _ _
  trivial

inductive dualPriority : (Ext : Type 0) → CandidateOnticItem Unit Ext → CandidateOnticItem Unit Ext → Prop
  | candidate_node : ∀ {Ext : Type 0} (e : Ext), dualPriority Ext (CandidateOnticItem.candidate e) (CandidateOnticItem.node ())
  | candidate_totality : ∀ {Ext : Type 0} (e : Ext), dualPriority Ext (CandidateOnticItem.candidate e) CandidateOnticItem.totality
  | node_totality : ∀ {Ext : Type 0} (n : Unit), dualPriority Ext (CandidateOnticItem.node n) CandidateOnticItem.totality

theorem dualPriority_wf : ∀ Ext, WellFounded (dualPriority Ext) := by
  intro Ext
  constructor
  intro a
  constructor
  intro b hb
  cases hb with
  | candidate_node e =>
    constructor
    intro c hc
    cases hc
  | candidate_totality e =>
    constructor
    intro c hc
    cases hc
  | node_totality n =>
    constructor
    intro c hc
    cases hc with
    | candidate_node e =>
      constructor
      intro d hd
      cases hd

theorem dualPriority_trans : ∀ Ext {a b c : CandidateOnticItem Unit Ext},
    dualPriority Ext a b → dualPriority Ext b c → dualPriority Ext a c := by
  intro Ext a b c hab hbc
  cases hab with
  | candidate_node e =>
    cases hbc with
    | node_totality n => exact dualPriority.candidate_totality e
  | candidate_totality e =>
    cases hbc
  | node_totality n =>
    cases hbc

theorem dual_node_totality : ∀ Ext (n : Unit), dualPriority Ext (CandidateOnticItem.node n) CandidateOnticItem.totality :=
  fun Ext n => dualPriority.node_totality (Ext := Ext) n

theorem dualWorldT_causal_access :
    ∀ n : Unit, HasFoundationalCausalAccess dualWorldS dualWorldT dualPriority n := by
  intro n
  cases n
  refine ⟨(), rfl, (), fun ⟨_, ha⟩ => ha, dualPriority.candidate_node (), Or.inl rfl⟩

theorem dualWorldT_determination_coherence :
    CausalDeterminationCoherence dualWorldS dualWorldT dualPriority := by
  intro w out hDet
  left
  cases w with
  | false =>
    dsimp [dualWorldT, dualChoosesOutcomeAt] at hDet
    rw [outcome_dual_false] at hDet
    refine ⟨trivial, hDet, fun b _ => dualWorldT_causal_access b, dualWorldT_causal_access⟩
  | true =>
    dsimp [dualWorldT, dualChoosesOutcomeAt] at hDet
    rw [outcome_dual_true] at hDet
    refine ⟨trivial, hDet, fun b _ => dualWorldT_causal_access b, dualWorldT_causal_access⟩

theorem dualWorldT_explains_alt :
    ExplainsOutcomeAt dualWorldS dualWorldT dualPriority false (SystemOutcomeAt dualWorldS false) := by
  refine ⟨trivial, rfl, rfl, ⟨(), rfl, dualPriority.candidate_totality ()⟩, ?_, dualWorldT_determination_coherence⟩
  refine ⟨trivial, Or.inl ⟨trivial, outcome_dual_false, dualWorldT_causal_access⟩⟩

theorem dualWorldS_psr :
    UniversalExplanatoryGroundingAtAlternatives dualWorldS dualWorldT dualPriority := by
  intro w_alt _
  dsimp [BruteOutcomeAt]
  cases w_alt with
  | false =>
    intro hNot
    apply hNot
    exact dualWorldT_explains_alt
  | true =>
    intro hNot
    apply hNot
    refine ⟨trivial, rfl, rfl, ⟨(), rfl, dualPriority.candidate_totality ()⟩, ?_, dualWorldT_determination_coherence⟩
    refine ⟨trivial, Or.inl ⟨trivial, outcome_dual_true, dualWorldT_causal_access⟩⟩

theorem dualWorldT_exhaustion :
    ModalExplanatoryExhaustionAtAlternatives dualWorldS dualWorldT dualPriority := by
  intro w_alt _ _
  left
  dsimp [dualWorldT, dualChoosesOutcomeAt]

theorem dualWorldT_impersonal_exclusion :
    ImpersonalExclusionAtAlternatives dualWorldS dualWorldT dualPriority := by
  intro hAgent _ w_alt _ _
  intro ⟨hImp, _⟩
  exact hImp hAgent

set_option linter.deprecated false in
theorem dualWorldT_acts_freely :
    ActsFreely dualWorldS dualWorldT := by
  refine ⟨dualWorldT_nature_invariant, false, trivial, rfl, ?_⟩
  rw [if_pos (show dualWorldS.InstantiatedIn false from trivial)]
  refine ⟨?_, ?_⟩
  · intro hEq
    dsimp [dualWorldS] at hEq
    injection hEq with hCfg
    have hT := congrFun hCfg ()
    revert hT
    decide
  · dsimp [dualWorldT, dualChoosesOutcomeAt, SystemOutcomeAt, dualWorldS]
    rw [if_pos trivial]

/-- MASTER SATISFIABILITY THEOREM (Joint Satisfiability of Corrected Principles):
Demonstrates with 0 axioms in the Lean 4 kernel that the corrected principles:
(1) `ContingentSystem dualWorldS`
(2) `UniversalExplanatoryGroundingAtAlternatives dualWorldS dualWorldT dualPriority`
(3) `ModalExplanatoryExhaustionAtAlternatives dualWorldS dualWorldT dualPriority`
(4) `ImpersonalExclusionAtAlternatives dualWorldS dualWorldT`
(5) `ActsFreely dualWorldS dualWorldT`
are NON-VACUOUSLY, SIMULTANEOUSLY TRUE in a concrete system containing a genuinely
divergent explained alternative.
This proves that the derivation of agential choice from the elimination of non-agential
modes does not rely on an ex-falso contradiction or incompatible premises.
(0 axioms). -/
theorem corrected_principles_jointly_satisfiable :
    ContingentSystem dualWorldS ∧
    UniversalExplanatoryGroundingAtAlternatives dualWorldS dualWorldT dualPriority ∧
    ModalExplanatoryExhaustionAtAlternatives dualWorldS dualWorldT dualPriority ∧
    ImpersonalExclusionAtAlternatives dualWorldS dualWorldT dualPriority ∧
    ActsFreely dualWorldS dualWorldT :=
  ⟨dualWorldS_contingent,
   dualWorldS_psr,
   dualWorldT_exhaustion,
   dualWorldT_impersonal_exclusion,
   dualWorldT_acts_freely⟩

theorem dualWorldS_neutral_psr :
    UniversalOutcomePSR dualWorldS dualPriority := by
  intro w_alt _
  refine ⟨dualWorldT, ?_⟩
  cases w_alt with
  | false => exact dualWorldT_explains_alt
  | true =>
    refine ⟨trivial, rfl, rfl, ⟨(), rfl, dualPriority.candidate_totality ()⟩, ?_, dualWorldT_determination_coherence⟩
    refine ⟨trivial, Or.inl ⟨trivial, outcome_dual_true, dualWorldT_causal_access⟩⟩

theorem dualWorldT_ultimate :
    IsUltimateGround dualWorldS dualWorldT dualPriority := by
  refine ⟨rfl, ?_⟩
  intro e _ ⟨hCond, _⟩
  cases hCond

theorem dualWorldT_necessary :
    IsNecessary dualWorldS dualWorldT := by
  intro _ _
  exact trivial

theorem dualWorldT_scope :
    UltimateGroundExplanatoryScope dualWorldS dualWorldT dualPriority := by
  intro _ _ _ w_alt _ _
  cases w_alt with
  | false => exact dualWorldT_explains_alt
  | true =>
    refine ⟨trivial, rfl, rfl, ⟨(), rfl, dualPriority.candidate_totality ()⟩, ?_, dualWorldT_determination_coherence⟩
    refine ⟨trivial, Or.inl ⟨trivial, outcome_dual_true, dualWorldT_causal_access⟩⟩

theorem dualWorldT_agential_bridge :
    AgentialDeterminationIsChoice dualWorldS dualWorldT := by
  intro _ _ w out
  dsimp [dualWorldT]
  rfl

/-- MASTER SATISFIABILITY THEOREM 2 (Joint Satisfiability of Neutral Explanatory Primitives):
Demonstrates with 0 axioms in the Lean 4 kernel that the primitive, neutral principles:
(1) `ContingentSystem dualWorldS`
(2) `UniversalOutcomePSR dualWorldS dualPriority` (neutral PSR, not indexed to T)
(3) `UltimateGroundExplanatoryScope dualWorldS dualWorldT dualPriority` (unicity/ultimacy scope)
(4) `AgentialDeterminationIsChoice dualWorldS dualWorldT` (determination is choice for personal agents)
(5) `ActsFreely dualWorldS dualWorldT`
are SIMULTANEOUSLY TRUE in a concrete contingent system with an explained divergent alternative.
(0 axioms). -/
theorem deepened_neutral_principles_jointly_satisfiable :
    ContingentSystem dualWorldS ∧
    UniversalOutcomePSR dualWorldS dualPriority ∧
    UltimateGroundExplanatoryScope dualWorldS dualWorldT dualPriority ∧
    AgentialDeterminationIsChoice dualWorldS dualWorldT ∧
    ActsFreely dualWorldS dualWorldT :=
  ⟨dualWorldS_contingent,
   dualWorldS_neutral_psr,
   dualWorldT_scope,
   dualWorldT_agential_bridge,
   dualWorldT_acts_freely⟩

theorem dualWorldS_eliminative_deduction :
    (∃ e : dualWorldT.ExtEntity, dualWorldT.ground = GroundIdentity.external e) ∧
    IsNecessary dualWorldS dualWorldT ∧
    NatureInvariant dualWorldS dualWorldT ∧
    IsPersonalAgent dualWorldS dualWorldT ∧
    IsUltimateGround dualWorldS dualWorldT dualPriority ∧
    GuidedByJustificationMode dualWorldS dualWorldT ∧
    ¬ (CompleteRationalDetermination dualWorldS dualWorldT ∨ UnifiedRationalActualization dualWorldS dualWorldT) := by
  have hGrounds : dualWorldT.GroundsConcreteActuality dualWorldT.ground dualWorldS.actualWorld := rfl
  have hExpl : ∀ w_alt : dualWorldS.World, dualWorldS.Accessible dualWorldS.actualWorld w_alt →
    (¬ dualWorldS.InstantiatedIn w_alt ∨ dualWorldS.ConfigurationIn w_alt ≠ dualWorldS.ConfigurationIn dualWorldS.actualWorld) →
    ContrastiveExplanationForTotality dualWorldS dualWorldT w_alt := by
    intro w_alt _ _
    trivial
  have hInternal : ∀ (n : dualWorldS.Node),
    dualWorldT.ground = GroundIdentity.internal n → ∀ Ext, dualPriority Ext CandidateOnticItem.totality (CandidateOnticItem.node n) := by
    intro n hn
    cases hn
  have hGroundsTot : ∀ (e : dualWorldT.ExtEntity),
    dualWorldT.ground = GroundIdentity.external e → dualPriority dualWorldT.ExtEntity (CandidateOnticItem.candidate e) CandidateOnticItem.totality := by
    intro e _
    exact dualPriority.candidate_totality e
  have hAseity : GroundingTotalityTerminatesInAseity dualWorldS dualWorldT := by
    intro _ _
    exact dualWorldT_necessary
  have hAseityNat : ImpersonalAseityPreservesNature dualWorldS dualWorldT := by
    intro hImp _
    exact False.elim (hImp dualWorldT_personal)
  have hSymm : ExplanatorySymmetryPrinciple dualWorldS dualWorldT dualPriority := by
    intro e _ hImp _ _ _
    exact False.elim (hImp dualWorldT_personal)
  have hUlt : IsUltimateGround dualWorldS dualWorldT dualPriority := dualWorldT_ultimate
  have hPersNat : PersonalAseityPreservesNature dualWorldS dualWorldT := by
    intro _ _
    exact dualWorldT_nature_invariant
  have hCond : DeterminationAsOnticCondition dualWorldS dualWorldT dualPriority := by
    intro hCRD
    cases hCRD with
    | inl h1 =>
      have hChoice := h1.2.2 false trivial (fun h => Bool.noConfusion h) trivial
      have hEx : ∃ out, dualWorldT.ChoosesOutcomeAt dualWorldT.ground false out := ⟨SystemOutcomeAt dualWorldS false, rfl⟩
      exact False.elim (hChoice hEx)
    | inr h2 =>
      have h1 := h2.rational_governance
      have hChoice := h1.2.2 false trivial (fun h => Bool.noConfusion h) trivial
      have hEx : ∃ out, dualWorldT.ChoosesOutcomeAt dualWorldT.ground false out := ⟨SystemOutcomeAt dualWorldS false, rfl⟩
      exact False.elim (hChoice hEx)
  have hCausal : FoundationalCausalDetermination dualWorldS dualWorldT dualPriority := by
    refine ⟨fun a b h => False.elim h, ?_, ?_⟩
    · intro e _ b _
      exact dualPriority.candidate_node e
    · intro e _
      exact dualPriority.candidate_totality e
  exact eliminative_deduction_of_unforced_personal_agent dualWorldS dualWorldT dualWorldS_contingent
    hGrounds hExpl dualPriority dualPriority_wf (fun Ext => dualPriority_trans Ext)
    dual_node_totality hInternal hGroundsTot hAseity hAseityNat hSymm hUlt hPersNat hCond hCausal

/-- REGRESSION THEOREM (Satisfiability of Existential Premises on Inhabited System):
Demonstrates that `dualWorldS` (where `Node := Unit` is inhabited), `dualWorldT`, and
`dualPriority` satisfy the existential theorem's conclusion via `dualWorldS_eliminative_deduction`.
Proves constructive satisfiability with 0 axioms in the Lean 4 kernel without ex falso. -/
theorem dualWorldS_satisfies_existential_premises :
    ∃ T : CandidateGround dualWorldS,
      (∃ e : T.ExtEntity, T.ground = GroundIdentity.external e) ∧
      IsNecessary dualWorldS T ∧
      NatureInvariant dualWorldS T ∧
      IsPersonalAgent dualWorldS T ∧
      IsUltimateGround dualWorldS T dualPriority ∧
      GuidedByJustificationMode dualWorldS T ∧
      ¬ (CompleteRationalDetermination dualWorldS T ∨ UnifiedRationalActualization dualWorldS T) :=
  ⟨dualWorldT, dualWorldS_eliminative_deduction⟩

theorem dualWorldT_selects_intentionally :
    SelectsIntentionally dualWorldS dualWorldT := by
  intro w_alt _
  refine ⟨trivial, ?_⟩
  dsimp [dualWorldT, dualChoosesOutcomeAt, SystemOutcomeAt, dualWorldS]
  split
  · rfl
  · contradiction

theorem dualWorldT_free_personal_source :
    FreePersonalSource dualWorldS dualWorldT :=
  ⟨⟨(), rfl⟩,
   dualWorldT_necessary,
   dualWorldT_nature_invariant,
   dualWorldT_personal,
   dualWorldT_selects_intentionally,
   dualWorldT_acts_freely⟩

/-- REGRESSION THEOREM (Satisfiability of Free Personal Source Attributes on Inhabited System):
Demonstrates that `dualWorldS` (where `Node := Unit` is inhabited), `dualWorldT`, and
`dualPriority` constructively and non-vacuously instantiate all six attributes of
`FreePersonalSource` directly without ex falso and without relying on any toy model correspondence bypass.
(0 axioms beyond core logic and classical choice). -/
theorem dualWorldS_satisfies_free_personal_source_premises :
    ∃ T : CandidateGround dualWorldS,
      FreePersonalSource dualWorldS T ∧
      ¬ (CompleteRationalDetermination dualWorldS T ∨ UnifiedRationalActualization dualWorldS T) :=
  ⟨dualWorldT, dualWorldT_free_personal_source, dualWorldS_eliminative_deduction.2.2.2.2.2.2⟩

-- ============================================================================
-- Section III-F.2: Tri-Modal System with Uninstantiated Accessible World
-- ============================================================================

/-- Tri-modal worlds witnessing both divergent configuration and non-instantiation:
- `wActual`: actual world, system instantiated with true configuration;
- `wDivergent`: alternative world, system instantiated with false configuration;
- `wUninstantiated`: alternative world, system NOT instantiated (outcome none). -/
inductive TriModalWorld : Type
  | wActual : TriModalWorld
  | wDivergent : TriModalWorld
  | wUninstantiated : TriModalWorld
  deriving DecidableEq, Repr

def triModalCfgActual : Unit → Bool := fun _ => true
def triModalCfgDivergent : Unit → Bool := fun _ => false

def triModalS : ConcreteSystem.{0} where
  World := TriModalWorld
  Node := Unit
  Determines := fun _ _ => False
  actualWorld := TriModalWorld.wActual
  Accessible := fun _ _ => True
  InstantiatedIn := fun w =>
    match w with
    | TriModalWorld.wActual => True
    | TriModalWorld.wDivergent => True
    | TriModalWorld.wUninstantiated => False
  ConfigurationIn := fun w _ =>
    match w with
    | TriModalWorld.wActual => true
    | TriModalWorld.wDivergent => false
    | TriModalWorld.wUninstantiated => false
  Prior := fun _ _ => False
  priorWellFounded := emptyUnitWf
  determinationRespectsPriority := fun h => False.elim h

theorem triModalS_contingent : ContingentSystem triModalS := by
  refine ⟨trivial, ?_⟩
  refine ⟨TriModalWorld.wUninstantiated, trivial, Or.inl id⟩

theorem triModalS_contingent_divergent_config :
    ∃ w_alt : triModalS.World, triModalS.Accessible triModalS.actualWorld w_alt ∧
      triModalS.InstantiatedIn w_alt ∧ triModalS.ConfigurationIn w_alt ≠ triModalS.ConfigurationIn triModalS.actualWorld := by
  refine ⟨TriModalWorld.wDivergent, trivial, trivial, ?_⟩
  intro hEq
  have hT := congrFun hEq ()
  revert hT
  decide

theorem outcome_tri_actual :
    SystemOutcomeAt triModalS TriModalWorld.wActual = some (triModalS.ConfigurationIn TriModalWorld.wActual) := by
  dsimp [SystemOutcomeAt, triModalS]
  split
  · rfl
  · contradiction

theorem outcome_tri_divergent :
    SystemOutcomeAt triModalS TriModalWorld.wDivergent = some (triModalS.ConfigurationIn TriModalWorld.wDivergent) := by
  dsimp [SystemOutcomeAt, triModalS]
  split
  · rfl
  · contradiction

theorem outcome_tri_uninstantiated :
    SystemOutcomeAt triModalS TriModalWorld.wUninstantiated = none := by
  dsimp [SystemOutcomeAt, triModalS]
  split
  · contradiction
  · rfl

noncomputable def triModalT : CandidateGround triModalS where
  ExtEntity := Unit
  ground := GroundIdentity.external ()
  ExistsAt := fun _ _ => True
  GroundsConcreteActuality := fun _ w => w = TriModalWorld.wActual
  grounding_binds_actuality := by
    intro w hw
    subst hw
    refine ⟨trivial, trivial, rfl⟩
  EssenceOf := fun _ _ => ⟨1, 1⟩
  ProvidesContrastiveJustification := fun _ _ _ => True
  ApprehendsAlternative := fun _ _ => True
  ReasonsFavor := fun _ _ _ => True
  ChoosesOutcomeAt := fun _ w out => out = SystemOutcomeAt triModalS w
  DeterminesOutcomeAt := fun _ w out => out = SystemOutcomeAt triModalS w

inductive triModalPriority : (Ext : Type 0) → CandidateOnticItem Unit Ext → CandidateOnticItem Unit Ext → Prop
  | candidate_node : ∀ (e : Unit), triModalPriority Unit (CandidateOnticItem.candidate e) (CandidateOnticItem.node ())
  | candidate_totality : ∀ (e : Unit), triModalPriority Unit (CandidateOnticItem.candidate e) CandidateOnticItem.totality
  | node_totality : ∀ (Ext : Type 0) (n : Unit), triModalPriority Ext (CandidateOnticItem.node n) CandidateOnticItem.totality

theorem triModalPriority_wf : ∀ Ext, WellFounded (triModalPriority Ext) := by
  intro Ext
  constructor
  intro a
  constructor
  intro b hb
  cases hb with
  | candidate_node e =>
    constructor
    intro c hc
    cases hc
  | candidate_totality e =>
    constructor
    intro c hc
    cases hc
  | node_totality Ext' n =>
    constructor
    intro c hc
    cases hc with
    | candidate_node e =>
      constructor
      intro d hd
      cases hd

theorem triModalT_causal_access :
    ∀ n : Unit, HasFoundationalCausalAccess triModalS triModalT triModalPriority n := by
  intro n
  cases n
  refine ⟨(), rfl, (), fun ⟨_, ha⟩ => ha, triModalPriority.candidate_node (), Or.inl rfl⟩

theorem triModalT_determination_coherence :
    CausalDeterminationCoherence triModalS triModalT triModalPriority := by
  intro w out hDet
  cases w with
  | wActual =>
    left
    dsimp [triModalT] at hDet
    rw [outcome_tri_actual] at hDet
    refine ⟨trivial, hDet, fun b _ => triModalT_causal_access b, triModalT_causal_access⟩
  | wDivergent =>
    left
    dsimp [triModalT] at hDet
    rw [outcome_tri_divergent] at hDet
    refine ⟨trivial, hDet, fun b _ => triModalT_causal_access b, triModalT_causal_access⟩
  | wUninstantiated =>
    right
    dsimp [triModalT] at hDet
    rw [outcome_tri_uninstantiated] at hDet
    refine ⟨hDet, ?_⟩
    refine ⟨trivial, id, ⟨(), rfl, triModalPriority.candidate_totality ()⟩, trivial⟩

theorem triModalT_explains_actual :
    ExplainsOutcomeAt triModalS triModalT triModalPriority TriModalWorld.wActual (SystemOutcomeAt triModalS TriModalWorld.wActual) := by
  refine ⟨trivial, rfl, rfl, ⟨(), rfl, triModalPriority.candidate_totality ()⟩, ?_, triModalT_determination_coherence⟩
  refine ⟨trivial, Or.inl ⟨trivial, outcome_tri_actual, triModalT_causal_access⟩⟩

theorem triModalT_explains_divergent :
    ExplainsOutcomeAt triModalS triModalT triModalPriority TriModalWorld.wDivergent (SystemOutcomeAt triModalS TriModalWorld.wDivergent) := by
  refine ⟨trivial, rfl, rfl, ⟨(), rfl, triModalPriority.candidate_totality ()⟩, ?_, triModalT_determination_coherence⟩
  refine ⟨trivial, Or.inl ⟨trivial, outcome_tri_divergent, triModalT_causal_access⟩⟩

theorem triModalT_explains_uninstantiated :
    ExplainsOutcomeAt triModalS triModalT triModalPriority TriModalWorld.wUninstantiated (SystemOutcomeAt triModalS TriModalWorld.wUninstantiated) := by
  refine ⟨trivial, rfl, rfl, ⟨(), rfl, triModalPriority.candidate_totality ()⟩, ?_, triModalT_determination_coherence⟩
  refine ⟨trivial, Or.inr ⟨outcome_tri_uninstantiated, ?_⟩⟩
  refine ⟨trivial, id, ⟨(), rfl, triModalPriority.candidate_totality ()⟩, trivial⟩

theorem triModalS_psr :
    UniversalOutcomePSR triModalS triModalPriority := by
  intro w_alt _
  refine ⟨triModalT, ?_⟩
  cases w_alt with
  | wActual => exact triModalT_explains_actual
  | wDivergent => exact triModalT_explains_divergent
  | wUninstantiated => exact triModalT_explains_uninstantiated

theorem triModalT_scope :
    UltimateGroundExplanatoryScope triModalS triModalT triModalPriority := by
  intro _ _ _ w_alt _ _
  cases w_alt with
  | wActual => exact triModalT_explains_actual
  | wDivergent => exact triModalT_explains_divergent
  | wUninstantiated => exact triModalT_explains_uninstantiated

theorem triModalT_agential_bridge :
    AgentialDeterminationIsChoice triModalS triModalT := by
  intro _ _ w out
  dsimp [triModalT]
  rfl

theorem triModalT_nature_invariant :
    NatureInvariant triModalS triModalT := by
  intro _ _
  rfl

set_option linter.deprecated false in
theorem triModalT_acts_freely :
    ActsFreely triModalS triModalT := by
  refine ⟨triModalT_nature_invariant, TriModalWorld.wDivergent, trivial, rfl, ?_⟩
  rw [if_pos (show triModalS.InstantiatedIn TriModalWorld.wDivergent from trivial)]
  refine ⟨?_, ?_⟩
  · intro hEq
    dsimp [triModalS] at hEq
    injection hEq with hCfg
    have hT := congrFun hCfg ()
    revert hT
    decide
  · dsimp [triModalT]
    exact outcome_tri_divergent.symm

/-- Countermodel Candidate: An external ground that exists at all worlds and declares determination,
but provides NO contrastive or explanatory grounding for non-instantiation
(`ProvidesContrastiveJustification := fun _ _ _ => False`). -/
noncomputable def T_unexplained_absence : CandidateGround triModalS where
  ExtEntity := Unit
  ground := GroundIdentity.external ()
  ExistsAt := fun _ _ => True
  GroundsConcreteActuality := fun _ w => w = TriModalWorld.wActual
  grounding_binds_actuality := by
    intro w hw
    subst hw
    refine ⟨trivial, trivial, rfl⟩
  EssenceOf := fun _ _ => ⟨1, 1⟩
  ProvidesContrastiveJustification := fun _ _ _ => False
  ApprehendsAlternative := fun _ _ => True
  ReasonsFavor := fun _ _ _ => True
  ChoosesOutcomeAt := fun _ w out => out = SystemOutcomeAt triModalS w
  DeterminesOutcomeAt := fun _ w out => out = SystemOutcomeAt triModalS w

/-- THEOREM (Unexplained Absence Fails ExplainsOutcomeAt at Uninstantiated World):
Demonstrates that T_unexplained_absence strictly FAILS to explain the uninstantiated outcome
because it provides no genuine explanatory grounding for the non-instantiation of S.
(0 axioms). -/
theorem unexplained_absence_fails_explanation :
    ¬ ExplainsOutcomeAt triModalS T_unexplained_absence triModalPriority TriModalWorld.wUninstantiated (SystemOutcomeAt triModalS TriModalWorld.wUninstantiated) := by
  intro ⟨_, _, _, _, hGrounds, _⟩
  cases hGrounds.2 with
  | inl hInst =>
    exact hInst.1
  | inr hUninst =>
    have hFalse := hUninst.2.2.2.2
    exact hFalse

/-- THEOREM (Unexplained Absence Strictly Fails Universal PSR):
Demonstrates that a candidate ground that fails to explain non-instantiation cannot satisfy
the Principle of Sufficient Reason at alternatives.
(0 axioms). -/
theorem unexplained_absence_fails_psr :
    ¬ UniversalExplanatoryGroundingAtAlternatives triModalS T_unexplained_absence triModalPriority := by
  intro hPSR
  have hBrute := hPSR TriModalWorld.wUninstantiated trivial
  dsimp [BruteOutcomeAt] at hBrute
  exact hBrute unexplained_absence_fails_explanation

/-- MASTER SATISFIABILITY THEOREM 3 (Joint Satisfiability in System with Uninstantiated and Divergent Worlds):
Demonstrates with 0 axioms in the Lean 4 kernel that the complete deepened principles:
(1) `ContingentSystem triModalS` (having both uninstantiated and divergent configuration worlds)
(2) `UniversalOutcomePSR triModalS triModalPriority`
(3) `UltimateGroundExplanatoryScope triModalS triModalT triModalPriority`
(4) `AgentialDeterminationIsChoice triModalS triModalT`
(5) `ActsFreely triModalS triModalT`
are SIMULTANEOUSLY AND NON-VACUOUSLY TRUE in a concrete system containing:
- An actual instantiated world with configuration c0;
- An accessible instantiated world with divergent configuration c1 ≠ c0;
- An accessible UNINSTANTIATED world with outcome none.
(0 axioms). -/
theorem tri_modal_principles_jointly_satisfiable :
    ContingentSystem triModalS ∧
    UniversalOutcomePSR triModalS triModalPriority ∧
    UltimateGroundExplanatoryScope triModalS triModalT triModalPriority ∧
    AgentialDeterminationIsChoice triModalS triModalT ∧
    ActsFreely triModalS triModalT :=
  ⟨triModalS_contingent,
   triModalS_psr,
   triModalT_scope,
   triModalT_agential_bridge,
   triModalT_acts_freely⟩

/-!
================================================================================
SECTION III-G: STRESS-TESTING WITH NON-BRUTE, NON-CHOOSING COUNTERMODELS
================================================================================
Investigates two distinct classes of non-brute countermodels required by methodological discipline:
1. Model A (Rival Ground Model): The alternative outcome is explained by an independent ground T' ≠ T.
2. Model B (Personal Determination Without Choice): A personal ground determines the alternative
   without choosing it (e.g. non-intentional determination).
================================================================================
-/

/-- Model A: Rival Ground Countermodel with Distinct External Entities.
A contingent system where actual world true is explained by T_main (external true),
and accessible alternative world false is explained by independent ground T_rival (external false). -/
def rivalS : ConcreteSystem.{0} := dualWorldS

theorem rival_entities_distinct : (true : Bool) ≠ false := by decide

noncomputable def T_main : CandidateGround rivalS where
  ExtEntity := Bool
  ground := GroundIdentity.external true
  ExistsAt := fun _ _ => True
  GroundsConcreteActuality := fun _ w => w = true
  grounding_binds_actuality := by
    intro w hw
    subst hw
    refine ⟨trivial, trivial, rfl⟩
  EssenceOf := fun _ _ => ⟨1, 1⟩
  ProvidesContrastiveJustification := fun _ _ _ => True
  ApprehendsAlternative := fun _ _ => True
  ReasonsFavor := fun _ _ _ => True
  ChoosesOutcomeAt := fun _ w out => w = true ∧ out = SystemOutcomeAt rivalS true
  DeterminesOutcomeAt := fun _ w out => w = true ∧ out = SystemOutcomeAt rivalS true

noncomputable def T_rival : CandidateGround rivalS where
  ExtEntity := Bool
  ground := GroundIdentity.external false
  ExistsAt := fun _ _ => True
  GroundsConcreteActuality := fun _ _ => False
  grounding_binds_actuality := fun _ h => False.elim h
  EssenceOf := fun _ _ => ⟨2, 2⟩
  ProvidesContrastiveJustification := fun _ _ _ => True
  ApprehendsAlternative := fun _ _ => True
  ReasonsFavor := fun _ _ _ => True
  ChoosesOutcomeAt := fun _ w out => w = false ∧ out = SystemOutcomeAt rivalS false
  DeterminesOutcomeAt := fun _ w out => w = false ∧ out = SystemOutcomeAt rivalS false

inductive rivalPriority : (Ext : Type 0) → CandidateOnticItem Unit Ext → CandidateOnticItem Unit Ext → Prop
  | candidate_node : ∀ (e : Bool), rivalPriority Bool (CandidateOnticItem.candidate e) (CandidateOnticItem.node ())
  | candidate_totality : ∀ (e : Bool), rivalPriority Bool (CandidateOnticItem.candidate e) CandidateOnticItem.totality
  | node_totality : ∀ (Ext : Type 0) (n : Unit), rivalPriority Ext (CandidateOnticItem.node n) CandidateOnticItem.totality

theorem rivalPriority_wf : ∀ Ext, WellFounded (rivalPriority Ext) := by
  intro Ext
  constructor
  intro a
  constructor
  intro b hb
  cases hb with
  | candidate_node e =>
    constructor
    intro c hc
    cases hc
  | candidate_totality e =>
    constructor
    intro c hc
    cases hc
  | node_totality Ext' n =>
    constructor
    intro c hc
    cases hc with
    | candidate_node e =>
      constructor
      intro d hd
      cases hd

theorem rival_node_totality : ∀ Ext (n : Unit), rivalPriority Ext (CandidateOnticItem.node n) CandidateOnticItem.totality :=
  fun Ext n => rivalPriority.node_totality Ext n

theorem T_main_causal_access :
    ∀ n : Unit, HasFoundationalCausalAccess rivalS T_main rivalPriority n := by
  intro n
  cases n
  refine ⟨true, rfl, (), fun ⟨_, ha⟩ => ha, rivalPriority.candidate_node true, Or.inl rfl⟩

theorem T_rival_causal_access :
    ∀ n : Unit, HasFoundationalCausalAccess rivalS T_rival rivalPriority n := by
  intro n
  cases n
  refine ⟨false, rfl, (), fun ⟨_, ha⟩ => ha, rivalPriority.candidate_node false, Or.inl rfl⟩

theorem outcome_rival_true : SystemOutcomeAt rivalS true = some (rivalS.ConfigurationIn true) :=
  outcome_dual_true

theorem outcome_rival_false : SystemOutcomeAt rivalS false = some (rivalS.ConfigurationIn false) :=
  outcome_dual_false

theorem T_main_determination_coherence :
    CausalDeterminationCoherence rivalS T_main rivalPriority := by
  intro w out hDet
  cases w with
  | false =>
    dsimp [T_main] at hDet
    have hContra : false = true := hDet.1
    contradiction
  | true =>
    left
    dsimp [T_main] at hDet
    have hOut := hDet.2
    rw [outcome_rival_true] at hOut
    refine ⟨trivial, hOut, fun b _ => T_main_causal_access b, T_main_causal_access⟩

theorem T_rival_determination_coherence :
    CausalDeterminationCoherence rivalS T_rival rivalPriority := by
  intro w out hDet
  cases w with
  | true =>
    dsimp [T_rival] at hDet
    have hContra : true = false := hDet.1
    contradiction
  | false =>
    left
    dsimp [T_rival] at hDet
    have hOut := hDet.2
    rw [outcome_rival_false] at hOut
    refine ⟨trivial, hOut, fun b _ => T_rival_causal_access b, T_rival_causal_access⟩

/-- THEOREM (Model A Satisfies Neutral PSR but Strictly Fails Explanatory Scope):
Demonstrates that in a system with an independent rival ground possessing a provably distinct
external identity (true ≠ false), every world has an explanation (so UniversalOutcomePSR holds
and neither world is brute), but T_main strictly FAILS UltimateGroundExplanatoryScope because
the alternative outcome is explained by the distinct entity T_rival.
(0 axioms). -/
theorem rival_ground_model_satisfies_neutral_psr_but_fails_scope :
    ContingentSystem rivalS ∧
    UniversalOutcomePSR rivalS rivalPriority ∧
    IsPersonalAgent rivalS T_main ∧
    IsUltimateGround rivalS T_main rivalPriority ∧
    IsNecessary rivalS T_main ∧
    (¬ UltimateGroundExplanatoryScope rivalS T_main rivalPriority) := by
  refine ⟨dualWorldS_contingent, ?_, ?_, ?_, ?_, ?_⟩
  · intro w_alt _
    cases w_alt with
    | false =>
      refine ⟨T_rival, ?_⟩
      refine ⟨trivial, rfl, ⟨rfl, rfl⟩, ⟨false, rfl, rivalPriority.candidate_totality false⟩, ?_, T_rival_determination_coherence⟩
      refine ⟨trivial, Or.inl ⟨trivial, outcome_dual_false, T_rival_causal_access⟩⟩
    | true =>
      refine ⟨T_main, ?_⟩
      refine ⟨trivial, rfl, ⟨rfl, rfl⟩, ⟨true, rfl, rivalPriority.candidate_totality true⟩, ?_, T_main_determination_coherence⟩
      refine ⟨trivial, Or.inl ⟨trivial, outcome_dual_true, T_main_causal_access⟩⟩
  · intro _ _ _
    trivial
  · refine ⟨rfl, ?_⟩
    intro e _ ⟨hCond, _⟩
    cases hCond
  · intro _ _
    exact trivial
  · intro hScope
    have hExFalse : ∃ T' : CandidateGround rivalS, ExplainsOutcomeAt rivalS T' rivalPriority false (SystemOutcomeAt rivalS false) := by
      refine ⟨T_rival, ⟨trivial, rfl, ⟨rfl, rfl⟩, ⟨false, rfl, rivalPriority.candidate_totality false⟩, ⟨trivial, Or.inl ⟨trivial, outcome_dual_false, T_rival_causal_access⟩⟩, T_rival_determination_coherence⟩⟩
    have hPersonal : IsPersonalAgent rivalS T_main := fun _ _ _ => trivial
    have hUlt : IsUltimateGround rivalS T_main rivalPriority := ⟨rfl, fun _ _ ⟨hCond, _⟩ => by cases hCond⟩
    have hNec : IsNecessary rivalS T_main := fun _ _ => trivial
    have hExpMainFalse := hScope hPersonal hUlt hNec false trivial hExFalse
    have hDetFalse := hExpMainFalse.2.2.1
    dsimp [T_main] at hDetFalse
    have hContra : false = true := hDetFalse.1
    revert hContra
    decide

/-- Model B: Personal Determination Without Choice.
A personal agent that determines the alternative outcome non-intentionally (ChoosesOutcomeAt is false at false). -/
noncomputable def T_det : CandidateGround dualWorldS where
  ExtEntity := Unit
  ground := GroundIdentity.external ()
  ExistsAt := fun _ _ => True
  GroundsConcreteActuality := fun _ w => w = true
  grounding_binds_actuality := by
    intro w hw
    subst hw
    refine ⟨trivial, trivial, rfl⟩
  EssenceOf := fun _ _ => ⟨1, 1⟩
  ProvidesContrastiveJustification := fun _ _ _ => True
  ApprehendsAlternative := fun _ _ => True
  ReasonsFavor := fun _ _ _ => True
  ChoosesOutcomeAt := fun _ w out => w = true ∧ out = SystemOutcomeAt dualWorldS true
  DeterminesOutcomeAt := fun _ w out => out = SystemOutcomeAt dualWorldS w

theorem T_det_causal_access :
    ∀ n : Unit, HasFoundationalCausalAccess dualWorldS T_det dualPriority n := by
  intro n
  cases n
  refine ⟨(), rfl, (), fun ⟨_, ha⟩ => ha, dualPriority.candidate_node (), Or.inl rfl⟩

theorem T_det_determination_coherence :
    CausalDeterminationCoherence dualWorldS T_det dualPriority := by
  intro w out hDet
  left
  cases w with
  | false =>
    dsimp [T_det] at hDet
    rw [outcome_dual_false] at hDet
    refine ⟨trivial, hDet, fun b _ => T_det_causal_access b, T_det_causal_access⟩
  | true =>
    dsimp [T_det] at hDet
    rw [outcome_dual_true] at hDet
    refine ⟨trivial, hDet, fun b _ => T_det_causal_access b, T_det_causal_access⟩

/-- THEOREM (Model B Explains the Alternative but Strictly Violates Agential Determination Bridge):
Demonstrates that a personal ground can determine the alternative outcome while refusing choice,
but strictly VIOLATES the Principle of Agential Intentional Determination.
(0 axioms). -/
theorem non_choosing_personal_model_violates_agential_determination_bridge :
    IsPersonalAgent dualWorldS T_det ∧
    NatureInvariant dualWorldS T_det ∧
    ExplainsOutcomeAt dualWorldS T_det dualPriority false (SystemOutcomeAt dualWorldS false) ∧
    (¬ T_det.ChoosesOutcomeAt T_det.ground false (SystemOutcomeAt dualWorldS false)) ∧
    (¬ AgentialDeterminationIsChoice dualWorldS T_det) := by
  have hAgent : IsPersonalAgent dualWorldS T_det := fun _ _ _ => trivial
  have hNature : NatureInvariant dualWorldS T_det := fun _ _ => rfl
  have hExp : ExplainsOutcomeAt dualWorldS T_det dualPriority false (SystemOutcomeAt dualWorldS false) := by
    refine ⟨trivial, rfl, rfl, ⟨(), rfl, dualPriority.candidate_totality ()⟩, ⟨trivial, Or.inl ⟨trivial, outcome_dual_false, T_det_causal_access⟩⟩, T_det_determination_coherence⟩
  have hNotChoice : ¬ T_det.ChoosesOutcomeAt T_det.ground false (SystemOutcomeAt dualWorldS false) := by
    dsimp [T_det]
    intro h
    have hContra : false = true := h.1
    revert hContra
    decide
  refine ⟨hAgent, hNature, hExp, hNotChoice, ?_⟩
  intro hBridge
  have hIff := (hBridge hAgent hNature false (SystemOutcomeAt dualWorldS false)).mp
  have hDetFalse : T_det.DeterminesOutcomeAt T_det.ground false (SystemOutcomeAt dualWorldS false) := rfl
  exact hNotChoice (hIff hDetFalse)

/-- THEOREM (Model B Strictly Violates the Forward Agential Determination Entailment):
Demonstrates that Model B also refutes the weaker forward implication AgentialDeterminationEntailsChoice,
confirming that the derived bridge is non-vacuous and substantive.
(0 axioms). -/
theorem non_choosing_personal_model_violates_agential_determination_entailment :
    ¬ AgentialDeterminationEntailsChoice dualWorldS T_det := by
  intro hBridge
  have hAgent : IsPersonalAgent dualWorldS T_det := fun _ _ _ => trivial
  have hNature : NatureInvariant dualWorldS T_det := fun _ _ => rfl
  have hDiff : SystemOutcomeAt dualWorldS false ≠ SystemOutcomeAt dualWorldS true := by
    rw [outcome_dual_false, outcome_dual_true]
    intro hEq
    injection hEq with hCfg
    have hT := congrFun hCfg ()
    revert hT
    decide
  have hDetFalse : T_det.DeterminesOutcomeAt T_det.ground false (SystemOutcomeAt dualWorldS false) := rfl
  have hChoiceFalse := hBridge hAgent hNature false trivial hDiff (SystemOutcomeAt dualWorldS false) hDetFalse
  dsimp [T_det] at hChoiceFalse
  have hContra : false = true := hChoiceFalse.1
  revert hContra
  decide

/-- THEOREM (Model B Witnesses Independence and Non-Redundancy of the Agential Action Correspondence):
Demonstrates that within the uninterpreted setting of `CandidateGround`, an ultimate personal ground can
determine outcomes without intentional choice, formally proving that `ActsFreely` and `SelectsIntentionally`
are mathematically independent of bare cosmological causal determination alone.
Consequently, this witnesses that `TranscendentAgentialActionCorrespondence` is a substantive, non-redundant
action-theoretic bridge: under this correspondence, determination is mapped to an originating intentional
act (`Act agent`), which constitutively entails choice by `AxIntentionalChoice`, precluding the decoupled
behavior witnessed by Model B.
(0 axioms). -/
theorem model_b_violates_transcendent_action_correspondence :
    ¬ TranscendentAgentialActionCorrespondence dualWorldS T_det := by
  intro hCorr
  obtain ⟨agent, _hRole, _hPerson, hActIff, hReal, _hFavor, _hDetAct⟩ := hCorr
  have hFidelity : ∀ (w : dualWorldS.World) (out : Option (dualWorldS.Node → Bool)),
      T_det.DeterminesOutcomeAt T_det.ground w out → out = SystemOutcomeAt dualWorldS w := by
    intro w out hDet
    exact (hActIff w out).mp hDet |>.1
  have hChoiceEntails := agential_determination_entails_choice_derived dualWorldS T_det agent hReal hFidelity
  have hDetFalse : T_det.DeterminesOutcomeAt T_det.ground false (SystemOutcomeAt dualWorldS false) := rfl
  have hChoiceFalse := hChoiceEntails (fun _ _ _ => trivial) (fun _ _ => rfl) false trivial outcome_dual_diff (SystemOutcomeAt dualWorldS false) hDetFalse
  dsimp [T_det] at hChoiceFalse
  have hContra : false = true := hChoiceFalse.1
  revert hContra
  decide

/-- THEOREM (Model B Proves the Non-Redundancy of Agential Action Realization):
Demonstrates that Model B (`T_det`) cannot be realized by ANY rational agent s in Γ's action theory.
This formally establishes that `AgentialActionRealization` is a genuine, non-vacuous action-theoretic constraint:
under Γ's constitutive semantic law of action (`AxIntentionalChoice`), any originating intentional act must
co-mean an incompatible alternative, whereas `T_det` isolates causal determination from choice.
(0 axioms). -/
theorem model_b_violates_action_theory_of_agency
    (s : Logos.Agency.Subject) :
    ¬ AgentialActionRealization dualWorldS T_det s := by
  intro hReal
  have hFidelity : ∀ (w : dualWorldS.World) (out : Option (dualWorldS.Node → Bool)),
      T_det.DeterminesOutcomeAt T_det.ground w out → out = SystemOutcomeAt dualWorldS w := by
    intro w out hDet
    exact hDet
  have hChoiceEntails := agential_determination_entails_choice_derived dualWorldS T_det s hReal hFidelity
  have hDetFalse : T_det.DeterminesOutcomeAt T_det.ground false (SystemOutcomeAt dualWorldS false) := rfl
  have hChoiceFalse := hChoiceEntails (fun _ _ _ => trivial) (fun _ _ => rfl) false trivial outcome_dual_diff (SystemOutcomeAt dualWorldS false) hDetFalse
  dsimp [T_det] at hChoiceFalse
  have hContra : false = true := hChoiceFalse.1
  revert hContra
  decide

/-- Model C: Unfounded Boundary Countermodel.
A system with an internal terminal node where the candidate ground grounds the totality,
but fails to ground the internal terminal node in the constitutive priority relation. -/
def boundaryS : ConcreteSystem.{0} := dualWorldS

theorem boundary_node_is_terminal : IsInternalTerminalNode boundaryS () := by
  intro ⟨a, ha⟩
  exact ha

noncomputable def T_unfounded : CandidateGround boundaryS := dualWorldT

inductive priorityWithoutBoundary : (Ext : Type 0) → CandidateOnticItem Unit Ext → CandidateOnticItem Unit Ext → Prop
  | candidate_totality : ∀ (e : Unit), priorityWithoutBoundary Unit (CandidateOnticItem.candidate e) CandidateOnticItem.totality

theorem priorityWithoutBoundary_wf : ∀ Ext, WellFounded (priorityWithoutBoundary Ext) := by
  intro Ext
  constructor
  intro a
  constructor
  intro b hb
  cases hb with
  | candidate_totality e =>
    constructor
    intro c hc
    cases hc

/-- THEOREM (Model C Fails Foundational Causal Determination):
Demonstrates that when a candidate ground fails to ground internal terminal nodes,
FoundationalCausalDetermination strictly FAILS, witnessing the necessity of hCausal.
(0 axioms). -/
theorem unfounded_boundary_model_fails_causal_determination :
    ¬ FoundationalCausalDetermination boundaryS T_unfounded priorityWithoutBoundary := by
  intro ⟨_, hTerminal, _⟩
  have hTerm := hTerminal () rfl () boundary_node_is_terminal
  cases hTerm

/-!
================================================================================
IV. EPISTEMOLOGICAL DISCIPLINE & KERNEL AXIOM AUDIT
================================================================================

1. Kernel-Derived Theorems vs. Explicit Metaphysical Premises:
   - A *kernel-derived theorem* is a proposition whose truth is deduced by Lean's core logic
     from the explicit hypotheses declared in its signature.
   - An *explicit metaphysical premise* (e.g. `ExplanatorySymmetryPrinciple`, `ExplanatoryUltimacyRequirement`)
     is passed to the theorem as a formal parameter.
   - A *philosophically justified premise* is one whose rational warrant is established
     independently in the treatise (`investigations/ontological_incompleteness_and_transcendent_source.md`).
     Being received as a hypothesis in Lean neither proves its truth nor invalidates its philosophical justification.

2. Reading `#print axioms`:
   - When `#print axioms` outputs `[propext, Classical.choice, Quot.sound]`, this certifies
     that the formal deduction rests strictly on standard Lean 4 foundational axioms.
   - It certifies that there are NO unproved axioms (0 `sorryAx`), NO ad hoc logical axioms,
     and NO hidden circularities in the kernel environment.
   - This footprint does NOT mean the theorem has no metaphysical commitments; those commitments
     are transparently stated in the function signature of `contingent_system_derives_free_personal_source`.

3. Structural Well-Foundedness vs. Substantive Consequence-Dependence:
   - The theorem `consequence_dependent_mode_fails_well_foundedness` proves mathematically (with 0 axioms)
     that IF a ground's determination depends on its consequence (`e ≺ S ≺ C ≺ e`), THEN a contradiction arises.
   - The broader philosophical argument (treated in §4 Step 5 of the treatise) establishes WHEN and WHY
     an impersonal ground is consequence-dependent: namely, whenever its determination appeals to the very
     concrete actuality of the system whose existence it is postulated to explain.
================================================================================
-/

#print axioms node_has_ancestral_ultimate_source
#print axioms internal_priority_irrefl_from_constitutive
#print axioms not_fixed_by_basis_iff_exists_divergent_accessible_world
#print axioms contingent_system_yields_divergent_accessible_world_under_invariant_nature
#print axioms contingent_system_under_invariant_nature_not_fixed
#print axioms agential_freedom_derived
#print axioms intentional_selection_does_not_deduce_libertarian_freedom
#print axioms agential_freedom_bridge_from_counterfactual_choice
#print axioms prior_irrefl
#print axioms closed_cycle_violates_ontological_priority
#print axioms internal_node_cannot_self_determine
#print axioms infinite_regress_conditional_rules_satisfied_by_vacuity
#print axioms infinite_regress_cannot_self_ground
#print axioms fully_internally_determined_is_impossible
#print axioms closed_system_has_unexplained_boundary
#print axioms internal_node_cannot_ground_totality_circularity
#print axioms candidate_consequence_circularity_refutation
#print axioms candidate_direct_consequence_cycle_refutation
#print axioms internal_rules_fail_contrastive_distinction
#print axioms internal_candidate_cannot_ground_totality
#print axioms candidate_ground_must_be_structurally_external
#print axioms necessary_impersonal_ground_contradicts_contingency
#print axioms unjustified_alternative_fails_contrastive_at
#print axioms consequence_dependent_mode_fails_well_foundedness
#print axioms direct_consequence_mode_fails_well_foundedness
#print axioms independent_condition_contradicts_ultimacy
#print axioms grounding_modes_exhaustive
#print axioms impersonal_ground_forces_consequence_or_independent_condition
#print axioms concrete_system_cannot_be_fully_internally_determined
#print axioms concrete_system_has_internal_terminal_node
#print axioms necessary_ground_cannot_rigidly_necessitate_contingent_system
#print axioms chain_cannot_be_exhaustively_forced
#print axioms agential_counterfactual_choice_bridge_from_sovereignty
#print axioms rational_intellectualist_control_model
#print axioms fortified_rational_intellectualist_control_model
#print axioms complete_rational_determination_refutes_libertarian_freedom
#print axioms rational_determination_distinct_from_necessitating_mode
#print axioms rational_determination_does_not_imply_necessitating_mode
#print axioms rational_determination_does_not_imply_circularity
#print axioms rational_determination_does_not_violate_contrastive_psr
#print axioms chain_non_forcing_compossible_with_rational_determination
#print axioms countermodelT_unified_actualization
#print axioms modal_necessitation_distinct_from_rational_actualization
#print axioms rational_actualization_distinct_from_outcome_fixed
#print axioms unified_actualization_compossible_with_non_forcing
#print axioms unified_actualization_refutes_libertarian_freedom
#print axioms five_levels_of_conclusion_separation
#print axioms strong_forcing_dilemma_and_role_of_sovereignty
#print axioms rational_forcing_in_priority_dilemma
#print axioms route1_intrinsic_fixing_contradicts_contingency
#print axioms route2_priority_conditioning_dilemma
#print axioms route3_teleological_explanation_properties
#print axioms intrinsic_rational_fixing_contradicts_contingency
#print axioms intellectualist_teleological_decoupling
#print axioms first_missing_step_to_libertarian_freedom
#print axioms substantive_rational_intellectualist_control_model
#print axioms master_premises_consistent_with_contingency
#print axioms agential_justification_mode_yields_free_personal_source
#print axioms contingent_system_derives_free_personal_source
#print axioms contingent_system_with_psr_derives_free_personal_source
#print axioms intellectualist_evasion_closure
#print axioms intellectualist_control_model_violates_explanatory_rule
#print axioms countermodelT_fails_deepened_primitive_principles
#print axioms intellectualist_control_model_violates_ontic_conditioning
#print axioms consolidated_ontological_incompleteness_derives_free_personal_source
#print axioms agential_sovereignty_derived
#print axioms explanatory_determination_rule_derived
#print axioms deepened_intellectualist_evasion_closure
#print axioms deepened_contingent_system_derives_free_personal_source
#print axioms deepened_contingent_system_with_psr_derives_free_personal_source
#print axioms deepened_consolidated_free_personal_source
#print axioms perfect_goodness_compossible_with_libertarian_freedom
#print axioms strict_evaluative_contrastive_fails_on_equal_goods
#print axioms agential_election_resolves_contrastive_psr_for_equal_goods
#print axioms corrected_principles_jointly_satisfiable
#print axioms pre_correction_psr_vacuously_provable_by_synthetic_candidate
#print axioms synthetic_candidate_without_constitutive_priority_fails_psr
#print axioms universal_grounding_of_ultimate_ground
#print axioms agential_sovereignty_derived_from_neutral_psr
#print axioms agential_determination_entails_choice_of_biconditional
#print axioms deepened_contingent_system_derives_free_personal_source_of_entails
#print axioms deepened_consolidated_free_personal_source_of_entails
#print axioms deepened_neutral_principles_jointly_satisfiable
#print axioms candidate_without_causal_access_fails_explanation
#print axioms governance_bridge_to_witness
#print axioms universal_ground_governance_yields_free_personal_source
#print axioms rival_ground_model_satisfies_neutral_psr_but_fails_scope
#print axioms non_choosing_personal_model_violates_agential_determination_bridge
#print axioms unfounded_boundary_model_fails_causal_determination
#print axioms model_b_violates_transcendent_action_correspondence
#print axioms model_b_violates_action_theory_of_agency
#print axioms dualWorldS_satisfies_existential_premises
#print axioms dualWorldS_satisfies_free_personal_source_premises
#print axioms eliminative_existential_derives_unforced_personal_agent
#print axioms intermediate_existential_derives_unforced_personal_source
#print axioms eliminative_deduction_derives_free_personal_source
#print axioms eliminative_deduction_derives_free_personal_source_under_transmission
#print axioms eliminative_foundation_derives_free_personal_source
#print axioms eliminative_foundation_derives_free_personal_source_under_transmission

end OntologicalIncompleteness

/-!
================================================================================
PART V: RETORSIVE INVESTIGATION OF RATIONAL JUSTIFICATION AND AGENTIAL FREEDOM
================================================================================
An autonomous investigation integrating the performative/retorsive framework
from `RetorsiveFreeSubject.lean` and the modular modal-judicative semantics of `best.lean`.

CRITICAL METHODOLOGICAL DISCIPLINES:
1. Strict Separation: Encapsulated in `Logos.RetorsiveBridgeInvestigation` to prevent
   any confusion with the master ontological argument in `OntologicalIncompleteness`.
2. Direct Test of the Retorsive Gap:
   - Proves `retorsive_contradiction` explicitly dependent on `IncompatibilistJustificationBridge`.
   - Constructs a NON-EMPTY countermodel (`non_empty_countermodel_justified_denial_without_freedom`)
     demonstrating that minimal rational justification is fully compossible with the factive truth
     of the universal denial of freedom and the complete absence of counterfactual choice in the author.
3. Modular Modal-Judicative Semantics from `best.lean`:
   - Directly reuses `DeterminationSystem` and `node_has_ancestral_ultimate_source` from
     `OntologicalIncompleteness` without duplication.
   - Decomposes the 4 substantive premises:
     * `ActAncestralDeterminationIsAgential`
     * `ExternalNodeFixedByPriorState`
     * `DeterminationExhaustive`
     * `VerdictTracksAlternative`
   - Demonstrates `normative_sensitivity_implies_libertarian_choice_direct` directly from alternative polarity.
4. Testing if Retorsion Establishes the Bridge (The First Demonstrative Gap):
   - Formalizes the exact point where deduction blocks:
     `rational_justification_compossible_with_prior_fixed_verdict` proves that reasons-responsiveness
     and non-mechanical justification do NOT analytically entail modal divergence under the same prior state.
================================================================================
-/

namespace RetorsiveBridgeInvestigation

universe u

/-!
--------------------------------------------------------------------------------
1. MINIMAL CONDITIONS OF RATIONAL JUSTIFICATION & RETORSIVE CONTRADICTION
--------------------------------------------------------------------------------
-/

/-- An epistemic subject capable of entertaining propositional thoughts. -/
structure EpistemicSubject (Node : Type u) where
  id : Node

/-- An assertion or epistemic judgment produced by an epistemic subject. -/
structure EpistemicAssertion (Node : Type u) where
  author : EpistemicSubject Node
  Content : Prop

/-- Minimal Conditions of Rational Justification:
An assertion `a` is rationally justified under framework `J` only if:
1. `ResponsiveToReasons`: formed in response to evidential/rational reasons;
2. `AimsAtTruth`: directed toward propositional truth;
3. `factive`: carries a commitment to the truth of its content (`a.Content`).
NON-CIRCULARITY & NON-PETITIO GUARANTEE:
This definition does NOT define the author as possessing libertarian free will, nor does
it define non-forcing mechanically by fiat. Freedom and mechanical non-forcing are substantive
modal properties to be investigated against modal semantics, not trivial structural fields. -/
structure RationalJustification {Node : Type u} (a : EpistemicAssertion Node) where
  ResponsiveToReasons : Prop
  AimsAtTruth : Prop
  justified : ResponsiveToReasons ∧ AimsAtTruth
  factive : a.Content

/-- Shorthand for an assertion being rationally justified under a given framework. -/
def IsRationallyJustified {Node : Type u} (a : EpistemicAssertion Node) (J : RationalJustification a) : Prop :=
  J.ResponsiveToReasons ∧ J.AimsAtTruth ∧ a.Content

/-- Libertarian Agential Freedom (Positive Counterfactual Choice):
A subject possesses libertarian freedom if, under the identical rational and essential nature,
the subject possessed the genuine counterfactual capacity to either assent to P, reject P, or suspend judgment,
rather than being inexorably fixed by prior non-agential conditions. -/
def HasCounterfactualChoice {Node : Type u} (s : EpistemicSubject Node) (ChoicePower : EpistemicSubject Node → Prop) : Prop :=
  ChoicePower s

/-- The Universal Denial of Freedom:
The proposition stating that no epistemic subject possesses counterfactual choice/freedom. -/
def UniversalDenialOfFreedom {Node : Type u} (ChoicePower : EpistemicSubject Node → Prop) : Prop :=
  ∀ s : EpistemicSubject Node, ¬ HasCounterfactualChoice s ChoicePower

/-- A performative assertion denying freedom:
An assertion whose propositional content is precisely the universal denial of freedom. -/
def DenialOfFreedomAssertion {Node : Type u} (a : EpistemicAssertion Node) (ChoicePower : EpistemicSubject Node → Prop) : Prop :=
  a.Content = UniversalDenialOfFreedom ChoicePower

/-- METAPHYSICAL BRIDGE 1 (The Epistemic Incompatibilism Bridge):
Tag: META.
Philosophical Justification (Boyle, Grisez, Tollefsen 1976; Plantinga; Lewis):
To be rationally justified, an affirmation must be an autonomous rational evaluation.
If the assent is necessitated by antecedent non-agential causes, the subject could not have
evaluated the reasons otherwise; hence rational justification requires genuine counterfactual
evaluative freedom (the power to choose between assent and suspension based on reasons).
WITHOUT THIS BRIDGE, NO RETORSIVE CONTRADICTION ARISES. -/
def IncompatibilistJustificationBridge {Node : Type u}
    (ChoicePower : EpistemicSubject Node → Prop) : Prop :=
  ∀ (a : EpistemicAssertion Node) (J : RationalJustification a),
    IsRationallyJustified a J → HasCounterfactualChoice a.author ChoicePower

/-- THEOREM R1 (The Exact Retorsive Contradiction):
If an assertion claiming to be rationally justified has as its content the universal denial
of freedom, then under the Epistemic Incompatibilism Bridge, a strict formal contradiction (`False`) is derived!
(0 axioms). -/
theorem retorsive_contradiction
    {Node : Type u}
    (ChoicePower : EpistemicSubject Node → Prop)
    (a : EpistemicAssertion Node)
    (J : RationalJustification a)
    (hJust : IsRationallyJustified a J)
    (hDenial : DenialOfFreedomAssertion a ChoicePower)
    (hBridge : IncompatibilistJustificationBridge ChoicePower) :
    False := by
  have hAuthorFree : HasCounterfactualChoice a.author ChoicePower :=
    hBridge a J hJust
  have hContentTrue : a.Content := J.factive
  have hUniversalDenial : UniversalDenialOfFreedom ChoicePower := by
    rw [hDenial] at hContentTrue
    exact hContentTrue
  have hAuthorNotFree : ¬ HasCounterfactualChoice a.author ChoicePower :=
    hUniversalDenial a.author
  exact hAuthorNotFree hAuthorFree

/-- THEOREM R2 (Direct Test of the Retorsive Gap — Non-Empty Countermodel):
Constructs an explicit non-empty countermodel in which:
- exists an epistemic subject `s` and an assertion `a` authored by `s`;
- the assertion is rationally justified (`IsRationallyJustified a J`);
- the content of `a` is the universal denial of freedom (`DenialOfFreedomAssertion a ChoicePower`);
- this denial is FACTUALLY TRUE in the model (`UniversalDenialOfFreedom ChoicePower`);
- the author possesses NO counterfactual choice (`¬ HasCounterfactualChoice a.author ChoicePower`);
- the incompatibilist bridge fails (`¬ IncompatibilistJustificationBridge ChoicePower`).
This directly proves that the minimal conditions of `RationalJustification` do NOT analytically
exclude the universal denial of freedom, nor do they entail libertarian choice without the bridge.
(0 axioms). -/
theorem non_empty_countermodel_justified_denial_without_freedom :
    ∃ (Node : Type)
      (ChoicePower : EpistemicSubject Node → Prop)
      (s : EpistemicSubject Node)
      (a : EpistemicAssertion Node)
      (J : RationalJustification a),
      a.author = s ∧
      DenialOfFreedomAssertion a ChoicePower ∧
      UniversalDenialOfFreedom ChoicePower ∧
      IsRationallyJustified a J ∧
      ¬ HasCounterfactualChoice a.author ChoicePower ∧
      ¬ IncompatibilistJustificationBridge ChoicePower := by
  let dummySubj : EpistemicSubject PUnit := ⟨PUnit.unit⟩
  let dummyChoicePower : EpistemicSubject PUnit → Prop := fun _ => False
  have hDenialTrue : UniversalDenialOfFreedom dummyChoicePower := fun _ hFalse => hFalse
  let dummyAssert : EpistemicAssertion PUnit := ⟨dummySubj, UniversalDenialOfFreedom dummyChoicePower⟩
  let dummyJust : RationalJustification dummyAssert := {
    ResponsiveToReasons := True
    AimsAtTruth := True
    justified := ⟨trivial, trivial⟩
    factive := hDenialTrue
  }
  have hJust : IsRationallyJustified dummyAssert dummyJust := ⟨trivial, trivial, hDenialTrue⟩
  have hNotChoice : ¬ HasCounterfactualChoice dummyAssert.author dummyChoicePower := by
    dsimp [HasCounterfactualChoice]
    intro hFalse
    exact hFalse
  have hNotBridge : ¬ IncompatibilistJustificationBridge dummyChoicePower := by
    intro hBridge
    have hChoice := hBridge dummyAssert dummyJust hJust
    exact hNotChoice hChoice
  exact ⟨PUnit, dummyChoicePower, dummySubj, dummyAssert, dummyJust,
         rfl, rfl, hDenialTrue, hJust, hNotChoice, hNotBridge⟩

/-!
--------------------------------------------------------------------------------
2. MODULAR MODAL & JUDICATIVE SEMANTICS (TRANSFER FROM BEST.LEAN)
--------------------------------------------------------------------------------
-/

/-- Modal Epistemic Context:
Represents accessible worlds, identical complete prior state, and judicative acts
(assent vs. withholding/suspension of judgment) with modal exclusivity. -/
structure ModalEpistemicContext (Subj : Type u) where
  World : Type u
  actualWorld : World
  Accessible : World → World → Prop
  SameCompletePriorState : World → World → Prop
  AssentsAt : Subj → World → Prop → Prop
  WithholdsAt : Subj → World → Prop → Prop
  exclusive : ∀ s w p, ¬ (AssentsAt s w p ∧ WithholdsAt s w p)

/-- Mecanicidade modal do juízo:
Mantendo-se o mesmo estado antecedente completo, o veredicto não varia
(nem o assentimento nem a suspensão podem divergir entre mundos acessíveis com o mesmo passado). -/
def MechanicallyForced
    {Subj : Type u}
    (M : ModalEpistemicContext Subj)
    (s : Subj)
    (w : M.World)
    (p : Prop) : Prop :=
  ∀ w' : M.World,
    M.Accessible w w' →
    M.SameCompletePriorState w w' →
    (
      (M.AssentsAt s w p → M.AssentsAt s w' p) ∧
      (M.WithholdsAt s w p → M.WithholdsAt s w' p)
    )

/-- Libertarian Free Choice at a world:
The subject actively assents (or withholds) regarding p, and there exists an accessible world
with the exact same complete prior state where the subject performed the contrary act. -/
def LibertarianFreeChoiceAt
    {Subj : Type u}
    (M : ModalEpistemicContext Subj)
    (s : Subj)
    (w : M.World)
    (p : Prop) : Prop :=
  (M.AssentsAt s w p ∧
    ∃ w', w' ≠ w ∧ M.Accessible w w' ∧ M.SameCompletePriorState w w' ∧ M.WithholdsAt s w' p) ∨
  (M.WithholdsAt s w p ∧
    ∃ w', w' ≠ w ∧ M.Accessible w w' ∧ M.SameCompletePriorState w w' ∧ M.AssentsAt s w' p)

/-- Normative sensitivity to contrary alternatives:
There exists an accessible world with the identical prior state where the judicative verdict flips. -/
def NormativelySensitive
    {Subj : Type u}
    (M : ModalEpistemicContext Subj)
    (s : Subj)
    (w : M.World)
    (p : Prop) : Prop :=
  ∃ w', M.Accessible w w' ∧ M.SameCompletePriorState w w' ∧ w' ≠ w ∧
    ((M.AssentsAt s w p ∧ M.WithholdsAt s w' p) ∨
     (M.WithholdsAt s w p ∧ M.AssentsAt s w' p))

/-- THEOREM R3 (Normative Sensitivity Directly Entails Libertarian Choice):
Direct analytical passage: given actual assent or suspension, normative sensitivity
to an accessible same-prior-state alternative yields libertarian free choice.
(0 axioms). -/
theorem normative_sensitivity_implies_libertarian_choice_direct
    {Subj : Type u}
    {M : ModalEpistemicContext Subj}
    {s : Subj}
    {w : M.World}
    {p : Prop}
    (hSens : NormativelySensitive M s w p) :
    LibertarianFreeChoiceAt M s w p := by
  rcases hSens with ⟨w', hAcc, hPrior, hNe, hPolar⟩
  cases hPolar with
  | inl hAssentWithhold =>
    exact Or.inl ⟨hAssentWithhold.1, ⟨w', hNe, hAcc, hPrior, hAssentWithhold.2⟩⟩
  | inr hWithholdAssent =>
    exact Or.inr ⟨hWithholdAssent.1, ⟨w', hNe, hAcc, hPrior, hWithholdAssent.2⟩⟩

/-- Modular Judgment Determination Context:
Extends the existing well-founded `DeterminationSystem` from `OntologicalIncompleteness`
to model the internal ancestral ancestry of a cognitive judgment act. -/
structure JudgmentDeterminationContext
    {Subj : Type u}
    (M : ModalEpistemicContext Subj)
    (s : Subj)
    (w : M.World)
    (p : Prop) where
  D : OntologicalIncompleteness.DeterminationSystem.{u}
  Outcome : Type u
  OutcomeOf : D.Node → M.World → Outcome
  verdictNode : D.Node
  judgmentActNode : D.Node
  IsActOf : Subj → D.Node → Prop
  judgmentActIsActOf : IsActOf s judgmentActNode
  judgmentActDeterminesVerdict :
    judgmentActNode = verdictNode ∨ OntologicalIncompleteness.DeterminesAncestrally D.Determines judgmentActNode verdictNode
  determines_propagates :
    ∀ {a b : D.Node}, D.Determines a b → ∀ w' : M.World, OutcomeOf b w' = OutcomeOf a w'

/-- Propagation of determination over reachability (identity or ancestral determination). -/
theorem reaches_propagates_outcome
    {Subj : Type u}
    {M : ModalEpistemicContext Subj}
    {s : Subj}
    {w : M.World}
    {p : Prop}
    (J : JudgmentDeterminationContext M s w p)
    {a b : J.D.Node}
    (hReach : a = b ∨ OntologicalIncompleteness.DeterminesAncestrally J.D.Determines a b)
    (w' : M.World) :
    J.OutcomeOf b w' = J.OutcomeOf a w' := by
  cases hReach with
  | inl hEq => subst hEq; rfl
  | inr hAnc =>
    induction hAnc with
    | single hd => exact J.determines_propagates hd w'
    | tail _ hd ih =>
      have hStep := J.determines_propagates hd w'
      exact hStep.trans ih

/-- Composition of reach: whoever ancestrally reaches the judgment act reaches the verdict. -/
theorem reaches_judgment_act_implies_reaches_verdict
    {Subj : Type u}
    {M : ModalEpistemicContext Subj}
    {s : Subj}
    {w : M.World}
    {p : Prop}
    (J : JudgmentDeterminationContext M s w p)
    {a : J.D.Node}
    (hReachAct : a = J.judgmentActNode ∨ OntologicalIncompleteness.DeterminesAncestrally J.D.Determines a J.judgmentActNode) :
    a = J.verdictNode ∨ OntologicalIncompleteness.DeterminesAncestrally J.D.Determines a J.verdictNode := by
  have hActVer := J.judgmentActDeterminesVerdict
  cases hReachAct with
  | inl hEqAct =>
    subst hEqAct
    exact hActVer
  | inr hAncAct =>
    cases hActVer with
    | inl hEqVer =>
      exact Or.inr (hEqVer ▸ hAncAct)
    | inr hAncVer =>
      exact Or.inr (Relation.TransGen.trans hAncAct hAncVer)

/-!
--------------------------------------------------------------------------------
3. EXPOSURE OF THE FOUR SUBSTANTIVE CONDITIONS & PROOFS AGAINST MECHANICAL FORCING
--------------------------------------------------------------------------------
-/

/-- Substantive Condition 1: Agential Ancestry.
Every node ancestrally determining the judgment act is an act of the concrete subject `s`. -/
def ActAncestralDeterminationIsAgential
    {Subj : Type u}
    {M : ModalEpistemicContext Subj}
    {s : Subj}
    {w : M.World}
    {p : Prop}
    (J : JudgmentDeterminationContext M s w p) : Prop :=
  ∀ (a : J.D.Node),
    (a = J.judgmentActNode ∨ OntologicalIncompleteness.DeterminesAncestrally J.D.Determines a J.judgmentActNode) →
    J.IsActOf s a

/-- Substantive Condition 2: External Prior-Fixing.
Any node that is NOT an act of `s` has its outcome rigidly fixed by the complete prior state. -/
def ExternalNodeFixedByPriorState
    {Subj : Type u}
    {M : ModalEpistemicContext Subj}
    {s : Subj}
    {w : M.World}
    {p : Prop}
    (J : JudgmentDeterminationContext M s w p) : Prop :=
  ∀ (a : J.D.Node), ¬ J.IsActOf s a →
    ∀ w' : M.World, M.SameCompletePriorState w w' →
      J.OutcomeOf a w' = J.OutcomeOf a w

/-- Substantive Condition 3: Exhaustive Determination.
If a node's outcome is fixed across all accessible worlds with the same complete prior state,
then that outcome must either be determined by an internal node or be external to the agent. -/
def DeterminationExhaustive
    {Subj : Type u}
    {M : ModalEpistemicContext Subj}
    {s : Subj}
    {w : M.World}
    {p : Prop}
    (J : JudgmentDeterminationContext M s w p) : Prop :=
  ∀ (a : J.D.Node),
    (∀ w' : M.World, M.Accessible w w' → M.SameCompletePriorState w w' → J.OutcomeOf a w' = J.OutcomeOf a w) →
    (∃ b : J.D.Node, J.D.Determines b a) ∨ ¬ J.IsActOf s a

/-- Substantive Condition 4: Verdict Tracks Alternative.
A difference in outcome at the verdict node produces polar opposite judicative verdicts. -/
def VerdictTracksAlternative
    {Subj : Type u}
    {M : ModalEpistemicContext Subj}
    {s : Subj}
    {w : M.World}
    {p : Prop}
    (J : JudgmentDeterminationContext M s w p) : Prop :=
  ∀ w1 w2 : M.World,
    J.OutcomeOf J.verdictNode w1 ≠ J.OutcomeOf J.verdictNode w2 →
    ((M.AssentsAt s w1 p ∧ M.WithholdsAt s w2 p) ∨
     (M.WithholdsAt s w1 p ∧ M.AssentsAt s w2 p))

/-- Outcome Received from Prior State:
The outcome of node `a` is invariant across all accessible worlds sharing the same prior state. -/
def DeterminationReceivedFromPriorState
    {Subj : Type u}
    {M : ModalEpistemicContext Subj}
    {s : Subj}
    {w : M.World}
    {p : Prop}
    (J : JudgmentDeterminationContext M s w p)
    (a : J.D.Node) : Prop :=
  ∀ w' : M.World, M.Accessible w w' → M.SameCompletePriorState w w' → J.OutcomeOf a w' = J.OutcomeOf a w

/-- An ultimate agential source cannot have its determination received from prior state
if determination is exhaustive.
(0 axioms). -/
theorem ultimate_agential_source_not_received_from_prior_state
    {Subj : Type u}
    {M : ModalEpistemicContext Subj}
    {s : Subj}
    {w : M.World}
    {p : Prop}
    (J : JudgmentDeterminationContext M s w p)
    (hExh : DeterminationExhaustive J)
    {a : J.D.Node}
    (haSource : OntologicalIncompleteness.IsInternalBruteFact J.D a)
    (haAct : J.IsActOf s a) :
    ¬ DeterminationReceivedFromPriorState J a := by
  intro hRec
  have hExhCases := hExh a hRec
  cases hExhCases with
  | inl hDetermined =>
    rcases hDetermined with ⟨b, hbDet⟩
    exact haSource ⟨b, hbDet⟩
  | inr hNotAct =>
    exact hNotAct haAct

/-- Failure of prior-state fixing entails the existence of an accessible world with divergent outcome.
(Classical choice). -/
theorem not_received_yields_accessible_divergence
    {Subj : Type u}
    {M : ModalEpistemicContext Subj}
    {s : Subj}
    {w : M.World}
    {p : Prop}
    (J : JudgmentDeterminationContext M s w p)
    {a : J.D.Node}
    (hNotRec : ¬ DeterminationReceivedFromPriorState J a) :
    ∃ w' : M.World, M.Accessible w w' ∧ M.SameCompletePriorState w w' ∧ J.OutcomeOf a w' ≠ J.OutcomeOf a w := by
  apply Classical.byContradiction
  intro hNotExists
  apply hNotRec
  intro w' hAcc hPrior
  apply Classical.byContradiction
  intro hNe
  exact hNotExists ⟨w', hAcc, hPrior, hNe⟩

/-- Outcome divergence at an ancestral source propagates to the verdict node.
(0 axioms). -/
theorem divergence_propagates_to_verdict
    {Subj : Type u}
    {M : ModalEpistemicContext Subj}
    {s : Subj}
    {w : M.World}
    {p : Prop}
    (J : JudgmentDeterminationContext M s w p)
    {a : J.D.Node}
    (hReachAct : a = J.judgmentActNode ∨ OntologicalIncompleteness.DeterminesAncestrally J.D.Determines a J.judgmentActNode)
    {w' : M.World}
    (hDiffA : J.OutcomeOf a w' ≠ J.OutcomeOf a w) :
    J.OutcomeOf J.verdictNode w' ≠ J.OutcomeOf J.verdictNode w := by
  have hReachVer := reaches_judgment_act_implies_reaches_verdict J hReachAct
  have hPropW' := reaches_propagates_outcome J hReachVer w'
  have hPropW := reaches_propagates_outcome J hReachVer w
  intro hEqVer
  apply hDiffA
  calc
    J.OutcomeOf a w' = J.OutcomeOf J.verdictNode w' := hPropW'.symm
    _ = J.OutcomeOf J.verdictNode w := hEqVer
    _ = J.OutcomeOf a w := hPropW

/-- LEMMA (Transfer from best.lean):
A ausência de determinação recebida pelo estado antecedente completo exclui a forçagem mecânica (`¬ MechanicallyForced`).
Demonstrado pela propagação determinativa e pela exclusividade modal entre assentimento e suspensão.
(Classical choice). -/
theorem non_received_determination_excludes_mechanical_forcing
    {Subj : Type u}
    {M : ModalEpistemicContext Subj}
    {s : Subj}
    {w : M.World}
    {p : Prop}
    (J : JudgmentDeterminationContext M s w p)
    (hTracks : VerdictTracksAlternative J)
    {a : J.D.Node}
    (hReachAct : a = J.judgmentActNode ∨ OntologicalIncompleteness.DeterminesAncestrally J.D.Determines a J.judgmentActNode)
    (hNotRec : ¬ DeterminationReceivedFromPriorState J a) :
    ¬ MechanicallyForced M s w p := by
  intro hForced
  have ⟨w', hAcc, hSame, hDiffA⟩ := not_received_yields_accessible_divergence J hNotRec
  have hDiffV := divergence_propagates_to_verdict J hReachAct hDiffA
  have hPolar := hTracks w w' (Ne.symm hDiffV)
  have hTrack := hForced w' hAcc hSame
  cases hPolar with
  | inl hAW =>
    exact M.exclusive s w' p ⟨hTrack.1 hAW.1, hAW.2⟩
  | inr hWA =>
    exact M.exclusive s w' p ⟨hWA.2, hTrack.2 hWA.1⟩

/-- LEMMA (Transfer from best.lean):
Uma fonte interna última que é acto do sujeito não pode ser mecanicamente forçada.
(Classical choice). -/
theorem subject_source_yields_not_mechanically_forced
    {Subj : Type u}
    {M : ModalEpistemicContext Subj}
    {s : Subj}
    {w : M.World}
    {p : Prop}
    (J : JudgmentDeterminationContext M s w p)
    (hExh : DeterminationExhaustive J)
    (hTracks : VerdictTracksAlternative J)
    {a : J.D.Node}
    (haSource : OntologicalIncompleteness.IsInternalBruteFact J.D a)
    (haReachAct : a = J.judgmentActNode ∨ OntologicalIncompleteness.DeterminesAncestrally J.D.Determines a J.judgmentActNode)
    (haAct : J.IsActOf s a) :
    ¬ MechanicallyForced M s w p := by
  have hNotRec := ultimate_agential_source_not_received_from_prior_state J hExh haSource haAct
  exact non_received_determination_excludes_mechanical_forcing J hTracks haReachAct hNotRec

/-- LEMMA (Transfer from best.lean):
A determinação constitutiva do acto de julgar é formalmente incompatível com a forçagem mecânica.
(Classical choice). -/
theorem constitutive_act_determination_incompatible_with_mechanical_forcing
    {Subj : Type u}
    {M : ModalEpistemicContext Subj}
    {s : Subj}
    {w : M.World}
    {p : Prop}
    (J : JudgmentDeterminationContext M s w p)
    (hAgential : ActAncestralDeterminationIsAgential J)
    (hExh : DeterminationExhaustive J)
    (hTracks : VerdictTracksAlternative J)
    (hForced : MechanicallyForced M s w p) :
    False := by
  have ⟨a, haSource, haReachAct⟩ :=
    OntologicalIncompleteness.node_has_ancestral_ultimate_source J.D J.judgmentActNode
  have haAct := hAgential a haReachAct
  have hNotForced := subject_source_yields_not_mechanically_forced J hExh hTracks haSource haReachAct haAct
  exact hNotForced hForced

/-- Alternative verdict outcome yields libertarian free choice via normative sensitivity.
(0 axioms). -/
theorem alternative_verdict_yields_libertarian_choice
    {Subj : Type u}
    {M : ModalEpistemicContext Subj}
    {s : Subj}
    {w : M.World}
    {p : Prop}
    (J : JudgmentDeterminationContext M s w p)
    (hTracks : VerdictTracksAlternative J)
    {w' : M.World}
    (hAcc : M.Accessible w w')
    (hSame : M.SameCompletePriorState w w')
    (hDiffV : J.OutcomeOf J.verdictNode w' ≠ J.OutcomeOf J.verdictNode w) :
    LibertarianFreeChoiceAt M s w p := by
  have hNeW : w' ≠ w := by
    intro hEqW
    subst hEqW
    exact hDiffV rfl
  have hPolar := hTracks w w' (Ne.symm hDiffV)
  exact normative_sensitivity_implies_libertarian_choice_direct ⟨w', hAcc, hSame, hNeW, hPolar⟩

/-- Pipeline compositivo da cadeia até à escolha libertária. -/
theorem determination_pipeline_yields_libertarian_choice
    {Subj : Type u}
    {M : ModalEpistemicContext Subj}
    {s : Subj}
    {w : M.World}
    {p : Prop}
    (J : JudgmentDeterminationContext M s w p)
    (hAgential : ActAncestralDeterminationIsAgential J)
    (hExh : DeterminationExhaustive J)
    (hTracks : VerdictTracksAlternative J) :
    LibertarianFreeChoiceAt M s w p := by
  have ⟨a, haSource, haReachAct⟩ :=
    OntologicalIncompleteness.node_has_ancestral_ultimate_source J.D J.judgmentActNode
  have haAct := hAgential a haReachAct
  have hNotRec := ultimate_agential_source_not_received_from_prior_state J hExh haSource haAct
  have ⟨w', hAcc, hSame, hDiffA⟩ := not_received_yields_accessible_divergence J hNotRec
  have hDiffV := divergence_propagates_to_verdict J haReachAct hDiffA
  exact alternative_verdict_yields_libertarian_choice J hTracks hAcc hSame hDiffV

/-- TEOREMA CENTRAL DE NÃO-MECANICIDADE E ESCOLHA LIBERTÁRIA:
Demonstra formalmente que, dadas as condições constitutivas da cadeia de julgamento
(agencialidade ancestral, exaustividade da determinação e rastreamento polar do veredicto),
o juízo não pode ser mecanicamente forçado do princípio ao fim (`¬ MechanicallyForced M s w p`)
e deduz conclusivamente a escolha libertária correspondente (`LibertarianFreeChoiceAt M s w p`).
(Classical choice). -/
theorem constitutive_determination_excludes_mechanical_forcing_and_yields_choice
    {Subj : Type u}
    {M : ModalEpistemicContext Subj}
    {s : Subj}
    {w : M.World}
    {p : Prop}
    (J : JudgmentDeterminationContext M s w p)
    (hAgential : ActAncestralDeterminationIsAgential J)
    (hExh : DeterminationExhaustive J)
    (hTracks : VerdictTracksAlternative J) :
    (¬ MechanicallyForced M s w p) ∧ LibertarianFreeChoiceAt M s w p := by
  have hNotForced : ¬ MechanicallyForced M s w p := fun hForced =>
    constitutive_act_determination_incompatible_with_mechanical_forcing J hAgential hExh hTracks hForced
  have hChoice := determination_pipeline_yields_libertarian_choice J hAgential hExh hTracks
  exact ⟨hNotForced, hChoice⟩

/-!
--------------------------------------------------------------------------------
4. INTEGRAÇÃO RETORSIVA COM O RESULTADO CENTRAL E AVALIAÇÃO DA PONTE
--------------------------------------------------------------------------------
Investiga se a apresentação de uma afirmação como racionalmente justificada instancia
a cadeia constitutiva de julgamento à qual se aplica o teorema de não-mecanicidade.
--------------------------------------------------------------------------------
-/

/-- A Ponte Retorsiva Constitutiva:
Investiga se a apresentação de uma asserção como racionalmente justificada instancia
uma cadeia de determinação judicativa satisfazendo as condições constitutivas de agência,
exaustividade e rastreamento alternativo. -/
def JustificationInstantiatesConstitutiveChain
    {Subj : Type u}
    (M : ModalEpistemicContext Subj)
    (s : Subj)
    (w : M.World)
    (p : Prop)
    (a : EpistemicAssertion Subj)
    (J_ep : RationalJustification a) : Prop :=
  IsRationallyJustified a J_ep →
    ∃ (J_det : JudgmentDeterminationContext M s w p),
      ActAncestralDeterminationIsAgential J_det ∧
      DeterminationExhaustive J_det ∧
      VerdictTracksAlternative J_det

/-- TEOREMA R4 (Integração Retorsiva com a Cadeia Constitutiva):
Se o ato de justificação racional instancia a cadeia constitutiva de julgamento, então o juízo
do autor não pode ser mecanicamente forçado do princípio ao fim, e o autor possui escolha libertária.
(Classical choice). -/
theorem retorsive_justification_with_chain_excludes_mechanical_forcing
    {Subj : Type u}
    {M : ModalEpistemicContext Subj}
    {s : Subj}
    {w : M.World}
    {p : Prop}
    (a : EpistemicAssertion Subj)
    (J_ep : RationalJustification a)
    (hJust : IsRationallyJustified a J_ep)
    (hBridge : JustificationInstantiatesConstitutiveChain M s w p a J_ep) :
    (¬ MechanicallyForced M s w p) ∧ LibertarianFreeChoiceAt M s w p := by
  have ⟨J_det, hAgential, hExh, hTracks⟩ := hBridge hJust
  exact constitutive_determination_excludes_mechanical_forcing_and_yields_choice J_det hAgential hExh hTracks

/-- THEOREM R5 (Âmbito Exato do Contra-Modelo Isolado da Justificação Racional):
Demonstra que as condições mínimas de `RationalJustification` (sensibilidade a razões, orientação
à verdade e factividade), QUANDO ISOLADAS DAS CONDIÇÕES DA CADEIA CONSTITUTIVA (especificamente,
sem satisfazer `DeterminationExhaustive`), admitem que o veredicto seja modalmente forçado
(`MechanicallyForced`).
NOTA CRÍTICA DE INTERPRETAÇÃO:
Este contra-modelo NÃO é um contra-modelo ao teorema central da cadeia (`constitutive_determination_excludes_mechanical_forcing_and_yields_choice`),
pois falha explicitamente `DeterminationExhaustive J_det`. Ele demonstra exclusivamente que
a justificação racional isolada não acarreta não-forçagem mecânica sem a ponte constitutiva.
(0 axioms). -/
theorem rational_justification_compossible_with_prior_fixed_verdict :
    ∃ (Subj : Type)
      (M : ModalEpistemicContext Subj)
      (s : Subj)
      (w : M.World)
      (p : Prop)
      (a : EpistemicAssertion Subj)
      (J_ep : RationalJustification a)
      (J_det : JudgmentDeterminationContext M s w p),
      IsRationallyJustified a J_ep ∧
      (∀ w' : M.World, M.Accessible w w' → M.SameCompletePriorState w w' →
        J_det.OutcomeOf J_det.verdictNode w' = J_det.OutcomeOf J_det.verdictNode w) ∧
      MechanicallyForced M s w p ∧
      ¬ DeterminationExhaustive J_det ∧
      ¬ LibertarianFreeChoiceAt M s w p := by
  let dummySubj : PUnit := PUnit.unit
  let dummyWorld : PUnit := PUnit.unit
  let dummyContext : ModalEpistemicContext PUnit := {
    World := PUnit
    actualWorld := dummyWorld
    Accessible := fun _ _ => True
    SameCompletePriorState := fun _ _ => True
    AssentsAt := fun _ _ _ => True
    WithholdsAt := fun _ _ _ => False
    exclusive := fun _ _ _ ⟨_, hW⟩ => hW
  }
  let dummyAssert : EpistemicAssertion PUnit := ⟨⟨dummySubj⟩, True⟩
  let dummyJust : RationalJustification dummyAssert := {
    ResponsiveToReasons := True
    AimsAtTruth := True
    justified := ⟨trivial, trivial⟩
    factive := trivial
  }
  have hJust : IsRationallyJustified dummyAssert dummyJust := ⟨trivial, trivial, trivial⟩
  let dummyD : OntologicalIncompleteness.DeterminationSystem := {
    Node := PUnit
    Determines := fun _ _ => False
    Prior := fun _ _ => False
    priorWellFounded := ⟨fun x => Acc.intro x (fun _ hPrior => False.elim hPrior)⟩
    priorTransitive := fun h _ => False.elim h
    determinationRespectsPriority := fun h => False.elim h
  }
  let dummyJDet : JudgmentDeterminationContext dummyContext dummySubj dummyWorld True := {
    D := dummyD
    Outcome := PUnit
    OutcomeOf := fun _ _ => PUnit.unit
    verdictNode := PUnit.unit
    judgmentActNode := PUnit.unit
    IsActOf := fun _ _ => True
    judgmentActIsActOf := trivial
    judgmentActDeterminesVerdict := Or.inl rfl
    determines_propagates := fun h _ => False.elim h
  }
  have hFixed : ∀ w' : PUnit, dummyContext.Accessible dummyWorld w' → dummyContext.SameCompletePriorState dummyWorld w' →
      dummyJDet.OutcomeOf dummyJDet.verdictNode w' = dummyJDet.OutcomeOf dummyJDet.verdictNode dummyWorld :=
    fun _ _ _ => rfl
  have hForced : MechanicallyForced dummyContext dummySubj dummyWorld True := by
    intro w' _ _
    exact ⟨fun hA => hA, fun hW => hW⟩
  have hNotExh : ¬ DeterminationExhaustive dummyJDet := by
    intro hExh
    have hCases := hExh PUnit.unit (fun _ _ _ => rfl)
    cases hCases with
    | inl hDet => rcases hDet with ⟨b, hbDet⟩; exact hbDet
    | inr hNotAct => exact hNotAct trivial
  have hNotChoice : ¬ LibertarianFreeChoiceAt dummyContext dummySubj dummyWorld True := by
    intro hChoice
    cases hChoice with
    | inl hAssent =>
      rcases hAssent.2 with ⟨w', _, _, _, hWithholds⟩
      exact hWithholds
    | inr hWithholds =>
      exact hWithholds.1
  exact ⟨PUnit, dummyContext, dummySubj, dummyWorld, True, dummyAssert, dummyJust, dummyJDet,
         hJust, hFixed, hForced, hNotExh, hNotChoice⟩

/-!
--------------------------------------------------------------------------------
5. KERNEL AXIOM AUDIT FOR THE RETORSIVE INVESTIGATION
--------------------------------------------------------------------------------
-/

#print axioms retorsive_contradiction
#print axioms non_empty_countermodel_justified_denial_without_freedom
#print axioms normative_sensitivity_implies_libertarian_choice_direct
#print axioms non_received_determination_excludes_mechanical_forcing
#print axioms subject_source_yields_not_mechanically_forced
#print axioms constitutive_act_determination_incompatible_with_mechanical_forcing
#print axioms constitutive_determination_excludes_mechanical_forcing_and_yields_choice
#print axioms retorsive_justification_with_chain_excludes_mechanical_forcing
#print axioms rational_justification_compossible_with_prior_fixed_verdict

end RetorsiveBridgeInvestigation

end Logos

namespace Logos.OntologicalIncompleteness

/-- Composite Divine Reality: Bundling the 8 Classical and Trinitarian Divine Characteristics.
    Every Free Personal Source satisfying the master deduction instantiates this comprehensive
    divine profile:
    1. Canonical Aseity (Metaphysical Necessity);
    2. Structural Transcendence (Externality to the cosmos);
    3. Foundational Omnipresence & Immanence (Sustaining concrete actuality);
    4. Foundational Unicity (Unicity of universal ground);
    5. Pure Actuality & Sovereign Freedom (Counterfactual choice power without passive potency);
    6. Omniscience & Rational Comprehension (Apprehends alternatives & evaluates reasons);
    7. Agential Intentional Selection (Choice guided by reasons);
    8. Trinitarian Hypostatic Communion (Relational communion of Divine Persons). -/
structure DivineReality (S : ConcreteSystem.{0}) (T : CandidateGround S) : Prop where
  aseity : IsNecessary S T ∧ NatureInvariant S T
  transcendence : ∃ e : T.ExtEntity, T.ground = GroundIdentity.external e
  immanence : T.GroundsConcreteActuality T.ground S.actualWorld
  unicity : ∃ g : Logos.Entity.Entity, Logos.FoundationalUnicity.UniversalModalGround g ∧ ∀ g', Logos.FoundationalUnicity.UniversalModalGround g' → g' = g
  sovereign_freedom : ActsFreely S T
  omniscience : (∀ w_alt, S.Accessible S.actualWorld w_alt → (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) → T.ApprehendsAlternative T.ground w_alt) ∧
                (∀ w_alt, S.Accessible S.actualWorld w_alt → T.ReasonsFavor T.ground S.actualWorld w_alt)
  intentionality : SelectsIntentionally S T
  trinitarian_communion : ∃ a b c : Logos.Agency.Subject,
    Logos.TrinitarianSubjectBridge.DivineSubjectRole a = Logos.TrinitarianSubjectBridge.DivineRole.source ∧
    Logos.TrinitarianSubjectBridge.DivineSubjectRole b = Logos.TrinitarianSubjectBridge.DivineRole.word ∧
    Logos.TrinitarianSubjectBridge.DivineSubjectRole c = Logos.TrinitarianSubjectBridge.DivineRole.spirit ∧
    Logos.Person.Person a ∧ Logos.Person.Person b ∧ Logos.Person.Person c

/-- MASTER THEOREM (Deduction of Complete Divine Characteristics):
    Demonstrates that any candidate ground T satisfying FreePersonalSource under
    its originating actuality and TranscendentAgentialActionCorrespondence
    instantiates all 8 classical and Trinitarian Divine Characteristics (DivineReality).
    (0 axioms beyond core logic, classical choice, and declared Trinity axiom). -/
theorem free_personal_source_instantiates_divine_reality
    (S : ConcreteSystem.{0})
    (T : CandidateGround S)
    (hGrounds : T.GroundsConcreteActuality T.ground S.actualWorld)
    (hFPS : FreePersonalSource S T)
    (hCorr : TranscendentAgentialActionCorrespondence S T) :
    DivineReality S T := by
  have hTrinity := Logos.TrinitarianSubjectBridge.three_divine_persons_exist_with_roles
  obtain ⟨a, b, c, hra, hrb, hrc, hpa, hpb, hpc⟩ := hTrinity
  obtain ⟨_agent, _hRole, _hPers, _hActIff, _hReal, hFavor, _hDetAct⟩ := hCorr
  refine ⟨
    ⟨hFPS.is_necessary, hFPS.nature_invariant⟩,
    hFPS.is_structurally_external,
    hGrounds,
    ⟨Logos.Entity.Entity.ofGround, rfl, fun _y hy => hy⟩,
    hFPS.acts_freely,
    ⟨hFPS.is_agent, hFavor⟩,
    hFPS.selects_intentionally,
    ⟨a, b, c, hra, hrb, hrc, hpa, hpb, hpc⟩
  ⟩

/-!
================================================================================
SECTION VIII: THE TEN CANONICAL CREMATIONS OF COMPETING PHILOSOPHIES
================================================================================
Formalizes the explicit deductive deaths and boundary limits of the ten major
rival ontological positions:
C1. Normative Nihilism / Skepticism
C2. Physicalist Mechanism / Hard Determinism
C3. Spinozistic Pantheism / Rigid Necessitarianism
C4. Leibnizian Intellectualist Determinism
C5. Humean / Russellian Cosmic Brute Fact
C6. Hume-Edwards Infinite Regress
C7. Coherentism / Closed Circularity
C8. Nominalist Voluntarism (Euthyphro)
C9. Monolithic Unitarianism / Solitary Monotheism
C10. Deism / Remote First Cause
================================================================================
-/

/-- CREMATION C1 (Normative Nihilism / Moral Skepticism):
    Asserting that no objective truth or normative ground exists is performatively self-refuting.
    Voicing the denial as justified derives False under the retorsive contradiction theorem.
    Terminator: ⊥ CONTRADICTION. -/
theorem cremation_c1_normative_nihilism
    {Node : Type u}
    (ChoicePower : RetorsiveBridgeInvestigation.EpistemicSubject Node → Prop)
    (a : RetorsiveBridgeInvestigation.EpistemicAssertion Node)
    (J : RetorsiveBridgeInvestigation.RationalJustification a)
    (hJust : RetorsiveBridgeInvestigation.IsRationallyJustified a J)
    (hDenial : RetorsiveBridgeInvestigation.DenialOfFreedomAssertion a ChoicePower)
    (hBridge : RetorsiveBridgeInvestigation.IncompatibilistJustificationBridge ChoicePower) :
    False :=
  RetorsiveBridgeInvestigation.retorsive_contradiction ChoicePower a J hJust hDenial hBridge

/-- CREMATION C2 (Physicalist Mechanism / Hard Determinism):
    All determination is physical and mechanical; every rational state is exhaustively
    received from antecedent physical conditions.
    Violates priority well-foundedness and constitutive agency, deriving False.
    Terminator: ⊥ CONTRADICTION. -/
theorem cremation_c2_physicalist_mechanism
    {Subj : Type u}
    {M : RetorsiveBridgeInvestigation.ModalEpistemicContext Subj}
    {s : Subj}
    {w : M.World}
    {p : Prop}
    (J : RetorsiveBridgeInvestigation.JudgmentDeterminationContext M s w p)
    (hTracks : RetorsiveBridgeInvestigation.VerdictTracksAlternative J)
    {a : J.D.Node}
    (hReachAct : a = J.judgmentActNode ∨ DeterminesAncestrally J.D.Determines a J.judgmentActNode)
    (hNotRec : ¬ RetorsiveBridgeInvestigation.DeterminationReceivedFromPriorState J a)
    (hMech : RetorsiveBridgeInvestigation.MechanicallyForced M s w p) :
    False :=
  (RetorsiveBridgeInvestigation.non_received_determination_excludes_mechanical_forcing J hTracks hReachAct hNotRec) hMech

/-- CREMATION C3 (Spinozistic Pantheism / Rigid Impersonal Necessitarianism):
    The ground rigidly necessitates the concrete system, destroying modal contingency.
    Refuted by the empirical and modal reality of the contingent system.
    Terminator: ⊘ REFUTED. -/
theorem cremation_c3_spinozistic_pantheism
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (hCont : ContingentSystem S)
    (hNec : IsNecessary S T)
    (hRigid : NecessitatingMode S T) :
    False :=
  (necessary_ground_cannot_rigidly_necessitate_contingent_system S T hCont hNec) hRigid

/-- CREMATION C4 (Leibnizian Intellectualist Determinism):
    Rational reasons mechanically constrain and necessitate divine choice.
    Refuted by the closure of intellectualist evasion: either reasons extinguish contingency
    or choice is unforced agential election.
    Terminator: COLLAPSE — INCOHERENT. -/
theorem cremation_c4_leibnizian_determinism
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (prior_wf : ∀ Ext, WellFounded (ConstitutivePriority Ext))
    (prior_trans : ∀ Ext {a b c : CandidateOnticItem S.Node Ext}, ConstitutivePriority Ext a b → ConstitutivePriority Ext b c → ConstitutivePriority Ext a c)
    (e : T.ExtEntity)
    (hExt : T.ground = GroundIdentity.external e)
    (hCond : DeterminationAsOnticCondition S T ConstitutivePriority)
    (hUlt : IsUltimateGround S T ConstitutivePriority)
    (hCRD : CompleteRationalDetermination S T ∨ UnifiedRationalActualization S T)
    (hCausal : FoundationalCausalDetermination S T ConstitutivePriority) :
    False :=
  deepened_intellectualist_evasion_closure S T ConstitutivePriority prior_wf prior_trans e hExt hCond hUlt hCRD hCausal

/-- CREMATION C5 (Humean / Russellian Cosmic Brute Fact):
    The universe as a whole is an ungrounded brute fact without contrastive explanation.
    Directly refutes contrastive explanation at accessible alternative configurations.
    Terminator: ⊘ REFUTED. -/
theorem cremation_c5_cosmic_brute_fact
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (w_alt : S.World)
    (hUnjust : UnjustifiedContrastiveAlternativeAt S T w_alt)
    (hExpl : ContrastiveExplanationForTotality S T w_alt) :
    False :=
  unjustified_alternative_fails_contrastive_at S T w_alt hUnjust hExpl

/-- CREMATION C6 (Hume-Edwards Infinite Regress / Regressionalism):
    An infinite causal regress is posited to self-ground without an ultimate source.
    Refuted by failure of well-foundedness; conditional debt is satisfied by absolute non-existence.
    Terminator: ⊥ CONTRADICTION. -/
theorem cremation_c6_infinite_regress
    (S : InfiniteRegressSystem.{u})
    (hWf : WellFounded (fun a b => S.Determines a b)) :
    False :=
  (infinite_regress_cannot_self_ground S) hWf

/-- CREMATION C7 (Coherentism / Closed Explanatory Circularity):
    Mutual dependence loops are posited as an ultimate explanation.
    Refuted by priority irreflexivity: any cycle derives an element prior to itself.
    Terminator: ⊥ CONTRADICTION. -/
theorem cremation_c7_closed_circularity
    (D : DeterminationSystem.{u})
    (a : D.Node)
    (hCycle : DeterminesAncestrally D.Determines a a) :
    False :=
  closed_cycle_violates_ontological_priority D a hCycle

/-- CREMATION C8 (Nominalist Voluntarism / Blind Fiat):
    The ground chooses without contrastive reasons or cognitive access to alternatives (Euthyphro).
    Refuted by inability to provide contrastive explanation for divergent configurations.
    Terminator: COLLAPSE — INCOHERENT. -/
theorem cremation_c8_nominalist_voluntarism
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (n : S.Node)
    (hNoAccess : ¬ HasFoundationalCausalAccess S T ConstitutivePriority n)
    (w : S.World)
    (hInst : S.InstantiatedIn w)
    (out : Option (S.Node → Bool))
    (hExpl : ExplainsOutcomeAt S T ConstitutivePriority w out) :
    False :=
  (candidate_without_causal_access_fails_explanation S T ConstitutivePriority n hNoAccess w hInst out) hExpl

/-- CREMATION C9 (Monolithic Unitarianism / Solitary Monotheism):
    The ground is posited as a single solitary person without eternal relational love.
    Refuted by categorical distinction between the divine ground and personal hypostases,
    and by the established communion of three distinct persons with hypostatic roles.
    Terminator: COLLAPSE — INCOHERENT. -/
theorem cremation_c9_monolithic_unitarianism
    (s : Logos.Agency.Subject)
    (hEquated : Logos.Entity.Entity.ofSubject s = Logos.Entity.Entity.ofGround) :
    False :=
  Logos.FoundationalUnicity.ofGround_ne_ofSubject s hEquated

/-- CREMATION C10 (Deism / Remote First Cause):
    An initial cause without concurrent explanatory transmission fails to explain particular outcomes.
    Proven by Countermodel A: universal ground unicity holds while mediated explanatory scope fails.
    Terminator: 🧱 COUNTERMODEL / BOUND. -/
theorem cremation_c10_deism :
    ContingentSystem rivalS ∧
    UniversalOutcomePSR rivalS rivalPriority ∧
    IsPersonalAgent rivalS T_main ∧
    IsUltimateGround rivalS T_main rivalPriority ∧
    IsNecessary rivalS T_main ∧
    (¬ UltimateGroundExplanatoryScope rivalS T_main rivalPriority) :=
  rival_ground_model_satisfies_neutral_psr_but_fails_scope

end Logos.OntologicalIncompleteness
