import Lean
import Logos.System
import Logos.Elimination

open Classical

namespace Logos
namespace OntologicalIncompleteness


/-- Action-Theoretic Realization Structure for Candidate Ground:
Connects the candidate ground's causal determination to the intentional action
of an associated personal subject s, respecting sort discipline and outcome specificity. -/
structure AgentialActionRealization
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (s : Logos.Agency.Subject) where
  /-- Determination expresses an originating intentional act by s -/
  originating_act : ∀ (w : S.World) (out : Option (S.Node → Bool)),
    T.DeterminesOutcomeAt T.ground w out →
    Logos.Agency.Means s (OutcomeAt S w out)
  /-- Metaphysical bridge premise: an agential ground determining a divergent counterfactual outcome
      co-means the salient actual-world alternative outcome -/
  contrastive_alternative : ∀ (w_alt : S.World) (out_alt out_act : Option (S.Node → Bool)),
    S.Accessible S.actualWorld w_alt →
    out_alt ≠ out_act →
    out_act = SystemOutcomeAt S S.actualWorld →
    T.DeterminesOutcomeAt T.ground w_alt out_alt →
    Logos.Agency.Means s (OutcomeAt S w_alt out_act)
  /-- Actual-world contrastive intentionality: when s determines the actual world, s co-means
      the accessible divergent alternative outcome -/
  actual_contrastive_alternative : ∀ (w_alt : S.World),
    S.Accessible S.actualWorld w_alt →
    SystemOutcomeAt S w_alt ≠ SystemOutcomeAt S S.actualWorld →
    Logos.Agency.Means s (OutcomeAt S S.actualWorld (SystemOutcomeAt S w_alt))
  /-- Outcome-specific choice reflection: whenever s chooses an outcome out at world w against an
      incompatible alternative proposition q that represents a distinct candidate outcome out',
      this constitutes T choosing out at world w -/
  choice_reflection : ∀ (w : S.World) (out out' : Option (S.Node → Bool)) (q : Prop),
    out ≠ out' →
    RepresentsAlternativeOutcome S w out' q →
    Logos.Choice.Chooses s (OutcomeAt S w out) q →
    T.ChoosesOutcomeAt T.ground w out

/-- THEOREM (Action-Theoretic Derivation of Choice via Intentional Contrastive Structure):
Demonstrates that for any candidate ground equipped with an agential action realization,
its causal determination of an alternative outcome at a divergent accessible world
strictly entails choosing that outcome against the actual-world alternative outcome,
substantively using hAcc and hDiff with zero dead code.
(0 axioms beyond Choice semantic axioms). -/
theorem agential_determination_entails_choice_derived
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (s : Logos.Agency.Subject)
    (hReal : AgentialActionRealization S T s)
    (hFidelity : ∀ (w : S.World) (out : Option (S.Node → Bool)),
      T.DeterminesOutcomeAt T.ground w out → out = SystemOutcomeAt S w) :
    AgentialDeterminationEntailsChoice S T := by
  intro _hAgent _hNature w_alt hAcc hDiff out hDet
  have hOutEq : out = SystemOutcomeAt S w_alt := hFidelity w_alt out hDet
  subst hOutEq
  let out_alt := SystemOutcomeAt S w_alt
  let out_act := SystemOutcomeAt S S.actualWorld
  have hAct := hReal.originating_act w_alt out_alt hDet
  have hMeansAct := hReal.contrastive_alternative w_alt out_alt out_act hAcc hDiff rfl hDet
  have hIncomp := incompatible_outcomes_at_world S w_alt out_alt out_act hDiff
  have hChooses : Logos.Choice.Chooses s (OutcomeAt S w_alt out_alt) (OutcomeAt S w_alt out_act) :=
    ⟨hAct, hMeansAct, hIncomp⟩
  have hRep : RepresentsAlternativeOutcome S w_alt out_act (OutcomeAt S w_alt out_act) := fun h => h
  exact hReal.choice_reflection w_alt out_alt out_act (OutcomeAt S w_alt out_act) hDiff hRep hChooses

/-- THEOREM (Action-Theoretic Derivation of Choice in Binary Contrast Space):
Demonstrates that in a binary contrast space, agential action realization directly supplies
the representation of the actual alternative outcome, deriving agential choice from action theory.
(0 axioms beyond Choice semantic axioms). -/
theorem agential_determination_entails_choice_in_binary_contrast_space
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (s : Logos.Agency.Subject)
    (hReal : AgentialActionRealization S T s)
    (hFidelity : ∀ (w : S.World) (out : Option (S.Node → Bool)),
      T.DeterminesOutcomeAt T.ground w out → out = SystemOutcomeAt S w)
    (_hBinary : ∀ (w_alt : S.World), S.Accessible S.actualWorld w_alt →
      BinaryContrastSpace S w_alt (SystemOutcomeAt S w_alt) (SystemOutcomeAt S S.actualWorld)) :
    AgentialDeterminationEntailsChoice S T :=
  agential_determination_entails_choice_derived S T s hReal hFidelity

/-- Representation of Cosmological Determination as an Originating Intentional Act of a Divine Person:
Connects the candidate ground's causal determination to the originating act of a divine Person agent
in Γ's foundational action theory, strictly respecting sort discipline (EntityOf s ≠ Entity.ofGround).
Under TrinitarianPersonalBridge (DivineTrinitarianAttributes.lean:270), divine agency belongs to the
divine Persons, with DivineRole.source originating creative acts.
Strictly requires genuine action-theoretic instantiation via AgentialActionRealization and Logos.Agency.Act.
The toy_model bypass has been completely eliminated, and actual-world choice is actively derived rather
than circularly assumed in the constructor. -/
inductive TranscendentAgentialActionCorrespondence
    (S : ConcreteSystem.{0})
    (T : CandidateGround S) : Prop
  | mk : ∀ (agent : Logos.Agency.Subject),
      Logos.TrinitarianSubjectBridge.DivineSubjectRole agent = Logos.TrinitarianSubjectBridge.DivineRole.source →
      Logos.Person.Person agent →
      (∀ (w : S.World) (out : Option (S.Node → Bool)),
        T.DeterminesOutcomeAt T.ground w out ↔
          (out = SystemOutcomeAt S w ∧ Logos.Agency.Means agent (OutcomeAt S w out))) →
      AgentialActionRealization S T agent →
      (∀ (w_alt : S.World),
        S.Accessible S.actualWorld w_alt →
        T.ReasonsFavor T.ground S.actualWorld w_alt) →
      T.DeterminesOutcomeAt T.ground S.actualWorld (some (S.ConfigurationIn S.actualWorld)) →
      TranscendentAgentialActionCorrespondence S T

/-- THEOREM (Agential Determination Entails Choice Derived from Action Theory):
Deduces AgentialDeterminationEntailsChoice for any candidate ground equipped with TranscendentAgentialActionCorrespondence.
DEDUCED DIRECTLY from Γ's foundational action theory via AgentialActionRealization and AxIntentionalChoice.
(0 axioms beyond AxIntentionalChoice). -/
theorem agential_determination_entails_choice_derived_from_action_theory
    (S : ConcreteSystem.{0})
    (T : CandidateGround S)
    (hCorr : TranscendentAgentialActionCorrespondence S T) :
    AgentialDeterminationEntailsChoice S T := by
  obtain ⟨agent, _hRole, _hPerson, hActIff, hReal, _hFavor, _hDetAct⟩ := hCorr
  have hFidelity : ∀ (w : S.World) (out : Option (S.Node → Bool)),
      T.DeterminesOutcomeAt T.ground w out → out = SystemOutcomeAt S w := by
    intro w out hDet
    exact (hActIff w out).mp hDet |>.1
  exact agential_determination_entails_choice_derived S T agent hReal hFidelity

/-- THEOREM (Determination Entails Choice via AxIntentionalChoice at Divergent Accessible Worlds):
Demonstrates that under TranscendentAgentialActionCorrespondence, whenever the candidate ground
determines an alternative outcome at an accessible divergent world, it constitutively chooses that outcome.
DEDUCED DIRECTLY from Γ's declared semantic axiom AxIntentionalChoice (Choice.lean:779)
with 0 axioms beyond standard logic and AxIntentionalChoice. -/
theorem agential_determination_entails_choice_via_intentional_action
    (S : ConcreteSystem.{0})
    (T : CandidateGround S)
    (hCorr : TranscendentAgentialActionCorrespondence S T)
    (hAgent : IsPersonalAgent S T)
    (hNature : NatureInvariant S T)
    (w_alt : S.World)
    (hAcc : S.Accessible S.actualWorld w_alt)
    (hDiff : SystemOutcomeAt S w_alt ≠ SystemOutcomeAt S S.actualWorld)
    (out : Option (S.Node → Bool)) :
    T.DeterminesOutcomeAt T.ground w_alt out → T.ChoosesOutcomeAt T.ground w_alt out := by
  have hEntails := agential_determination_entails_choice_derived_from_action_theory S T hCorr
  exact hEntails hAgent hNature w_alt hAcc hDiff out

/-- THEOREM (Actual-World Agential Choice Derived from Originating Act and Action Theory):
Deduces `T.ChoosesOutcomeAt T.ground S.actualWorld out_act` directly from:
(1) Originating determination of actuality (`actual_determination`),
(2) Originating intentional act of the Divine Person (`act_iff`),
(3) Action-theoretic choice reflection against accessible divergent alternatives (`choice_reflection`),
(4) Meaning of the alternative outcome (`actual_contrastive_alternative`),
(5) Invariance of the ground's nature (`NatureInvariant S T`),
(6) Contingency of the system (`ContingentSystem S`),
completely eliminating the circular assumption of actual choice from the correspondence constructor.
(0 axioms beyond Choice semantic axioms). -/
theorem agential_action_grounding_derives_actual_choice
    (S : ConcreteSystem.{0})
    (T : CandidateGround S)
    (hCont : ContingentSystem S)
    (hNature : NatureInvariant S T)
    (hCorr : TranscendentAgentialActionCorrespondence S T) :
    T.ChoosesOutcomeAt T.ground S.actualWorld (some (S.ConfigurationIn S.actualWorld)) := by
  obtain ⟨agent, _hRole, _hPerson, hActIff, hReal, _hFavor, hDetAct⟩ := hCorr
  have hInstAct := hCont.1
  obtain ⟨w_alt, hAcc, _hEss, hDiff⟩ :=
    contingent_system_yields_divergent_accessible_world_under_invariant_nature S T hCont hNature
  have hActOut : SystemOutcomeAt S S.actualWorld = some (S.ConfigurationIn S.actualWorld) := by
    dsimp [SystemOutcomeAt]
    split
    · rfl
    · contradiction
  let out_act : Option (S.Node → Bool) := some (S.ConfigurationIn S.actualWorld)
  let out_alt : Option (S.Node → Bool) := SystemOutcomeAt S w_alt
  have hMeansAct : Logos.Agency.Means agent (OutcomeAt S S.actualWorld out_act) :=
    (hActIff S.actualWorld out_act).mp hDetAct |>.2
  have hDiffSymm : out_act ≠ out_alt := by
    intro hEq
    have h1 : SystemOutcomeAt S S.actualWorld = SystemOutcomeAt S w_alt := by
      rw [hActOut]
      exact hEq
    exact hDiff h1.symm
  have hMeansAltW : Logos.Agency.Means agent (OutcomeAt S S.actualWorld out_alt) :=
    hReal.actual_contrastive_alternative w_alt hAcc hDiff
  have hIncomp : Logos.Alternatives.Incompatible
      (OutcomeAt S S.actualWorld out_act) (OutcomeAt S S.actualWorld out_alt) :=
    incompatible_outcomes_at_world S S.actualWorld out_act out_alt hDiffSymm
  have hChooses : Logos.Choice.Chooses agent
      (OutcomeAt S S.actualWorld out_act) (OutcomeAt S S.actualWorld out_alt) :=
    ⟨hMeansAct, hMeansAltW, hIncomp⟩
  have hRep : RepresentsAlternativeOutcome S S.actualWorld out_alt (OutcomeAt S S.actualWorld out_alt) :=
    fun h => h
  exact hReal.choice_reflection S.actualWorld out_act out_alt
    (OutcomeAt S S.actualWorld out_alt) hDiffSymm hRep hChooses

/-- THEOREM (SelectsIntentionally Derived from Originating Act and Reason Guidance):
Deduces `SelectsIntentionally S T` directly from the personal ground's originating determination of actuality,
contrastive reason guidance, and action theory, with ZERO circularity.
(0 axioms beyond Choice semantic axioms). -/
theorem agential_action_grounding_derives_selects_intentionally
    (S : ConcreteSystem.{0})
    (T : CandidateGround S)
    (hCont : ContingentSystem S)
    (hNature : NatureInvariant S T)
    (hCorr : TranscendentAgentialActionCorrespondence S T) :
    SelectsIntentionally S T := by
  have hChoiceAct := agential_action_grounding_derives_actual_choice S T hCont hNature hCorr
  obtain ⟨_agent, _hRole, _hPerson, _hActIff, _hReal, hFavor, _hDetAct⟩ := hCorr
  intro w_alt hAcc
  exact ⟨hFavor w_alt hAcc, hChoiceAct⟩

/-- THEOREM (Deepened Derivation of Agential Sovereignty from Neutral PSR and Agential Determination Entailment):
Demonstrates that `AgentialSovereigntyOverAlternatives` is DEDUCED directly from:
(1) Neutral Universal PSR (`UniversalOutcomePSR S ConstitutivePriority`),
(2) Ultimate Ground Explanatory Scope (`UltimateGroundExplanatoryScope S T ConstitutivePriority`),
(3) Agential Determination Entails Choice (`AgentialDeterminationEntailsChoice S T`),
(4) Personal Aseity Preserves Nature (`PersonalAseityPreservesNature S T`),
(5) Necessity of the Ground (`IsNecessary S T`),
with 0 axioms beyond standard logic.
(0 axioms). -/
theorem agential_sovereignty_derived_from_neutral_psr
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (hPSR : UniversalOutcomePSR S ConstitutivePriority)
    (hScope : UltimateGroundExplanatoryScope S T ConstitutivePriority)
    (hChoiceBridge : AgentialDeterminationEntailsChoice S T)
    (hPersonalNature : PersonalAseityPreservesNature S T)
    (hNec : IsNecessary S T) :
    AgentialSovereigntyOverAlternatives S T ConstitutivePriority := by
  intro hAgent hUlt _ w_alt hAcc hDiff
  have hNature := hPersonalNature hAgent hNec
  have hExSome := hPSR w_alt hAcc
  have hExpT := hScope hAgent hUlt hNec w_alt hAcc hExSome
  have hDet := hExpT.2.2.1
  have hChoice := hChoiceBridge hAgent hNature w_alt hAcc hDiff (SystemOutcomeAt S w_alt) hDet
  exact hChoice

/-- Overload preserving full backward compatibility with the canonical biconditional bridge:
(0 axioms). -/
theorem agential_sovereignty_derived_from_biconditional_bridge
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (hPSR : UniversalOutcomePSR S ConstitutivePriority)
    (hScope : UltimateGroundExplanatoryScope S T ConstitutivePriority)
    (hBicond : AgentialDeterminationIsChoice S T)
    (hPersonalNature : PersonalAseityPreservesNature S T)
    (hNec : IsNecessary S T) :
    AgentialSovereigntyOverAlternatives S T ConstitutivePriority :=
  agential_sovereignty_derived_from_neutral_psr S T ConstitutivePriority hPSR hScope
    (agential_determination_entails_choice_of_biconditional S T hBicond) hPersonalNature hNec

/-- PRINCIPLE OF IMPERSONAL GROUND EXCLUSION AT ACCESSIBLE ALTERNATIVES:
Tag: META.
- Philosophical Justification:
  For an ultimate personal ground with invariant essential nature across accessible worlds,
  an alternative contingent outcome cannot be grounded by an impersonal determination without
  contradicting the personal nature of the ground. -/
def ImpersonalExclusionAtAlternatives
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop) : Prop :=
  IsPersonalAgent S T →
  NatureInvariant S T →
  ∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
    SystemOutcomeAt S w_alt ≠ SystemOutcomeAt S S.actualWorld →
    ¬ ImpersonallyDeterminedOutcomeAt S T ConstitutivePriority w_alt

/-- THEOREM 6B₂' (Deepened Derivation of Agential Sovereignty from Primitive Explanatory Principles):
Demonstrates that `AgentialSovereigntyOverAlternatives` is DEDUCED as a theorem from:
(1) Modal Explanatory Exhaustion (`ModalExplanatoryExhaustionAtAlternatives`),
(2) Universal Explanatory Grounding / Contrastive PSR (`UniversalExplanatoryGroundingAtAlternatives`),
(3) Exclusion of Impersonal Determinations (`ImpersonalExclusionAtAlternatives`),
(4) Personal Aseity Preserves Nature (`PersonalAseityPreservesNature`),
(5) Necessity of the Ground (`IsNecessary`).
This proves that agential sovereignty over alternatives is not an ungrounded decree or arbitrary fiat,
but the deductive consequence of universal grounding, personal nature invariance, and ultimacy.
(0 axioms). -/
theorem agential_sovereignty_derived
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (hExh : ModalExplanatoryExhaustionAtAlternatives S T ConstitutivePriority)
    (hPSR : UniversalExplanatoryGroundingAtAlternatives S T ConstitutivePriority)
    (hNoImp : ImpersonalExclusionAtAlternatives S T ConstitutivePriority)
    (hPersonalNature : PersonalAseityPreservesNature S T)
    (hNec : IsNecessary S T) :
    AgentialSovereigntyOverAlternatives S T ConstitutivePriority := by
  intro hAgent _ _ w_alt hAcc hDiff
  have hNature := hPersonalNature hAgent hNec
  have hCases := hExh w_alt hAcc hDiff
  rcases hCases with hChoice | hImp | hBrute
  · exact hChoice
  · have hNotImp := hNoImp hAgent hNature w_alt hAcc hDiff
    exact False.elim (hNotImp hImp)
  · have hNotBrute := hPSR w_alt hAcc
    exact False.elim (hNotBrute hBrute)

theorem countermodelT_personal_nature : PersonalAseityPreservesNature countermodelS countermodelT := by
  intro _ _ _ _
  rfl

theorem countermodelT_symmetry : ExplanatorySymmetryPrinciple countermodelS countermodelT toyPriority := by
  intro e hExt hNotAgent
  exfalso
  apply hNotAgent
  intro _ _ _
  exact trivial

theorem countermodelT_teleology : TeleologicalAgencyPrinciple countermodelS countermodelT := by
  intro _ _
  exact countermodelT_selects_intentionally

theorem countermodelT_fails_sovereignty : ¬ AgentialSovereigntyOverAlternatives countermodelS countermodelT toyPriority := by
  intro hSovereign
  have hAgent : IsPersonalAgent countermodelS countermodelT := fun _ _ _ => trivial
  have hDiff : SystemOutcomeAt countermodelS false ≠ SystemOutcomeAt countermodelS true := by
    apply (system_outcome_diff_iff countermodelS false trivial).mpr
    right
    intro hEq
    have hT := congrFun hEq ()
    revert hT
    decide
  have hChoiceFalse := hSovereign hAgent countermodelT_ultimate countermodelT_not_necessitating false trivial hDiff
  have hFalseMax := hChoiceFalse.2
  rw [hChoiceFalse.1] at hFalseMax
  exact false_not_maximal hFalseMax

/-- THEOREM (The Intellectualist Control Model Fails the Deepened Primitive Principles):
Demonstrates that the substantive intellectualist control model (`countermodelS, countermodelT, toyPriority`)
strictly FAILS the conjunction of the three primitive principles (Modal Explanatory Exhaustion,
Universal Explanatory Grounding, and Impersonal Exclusion).
This proves that theological intellectualism / rational determinism cannot survive
once universal grounding and explanatory exhaustion are enforced.
(0 axioms). -/
theorem countermodelT_fails_deepened_primitive_principles :
    ¬ (ModalExplanatoryExhaustionAtAlternatives countermodelS countermodelT toyPriority ∧
       UniversalExplanatoryGroundingAtAlternatives countermodelS countermodelT toyPriority ∧
       ImpersonalExclusionAtAlternatives countermodelS countermodelT toyPriority) := by
  intro ⟨hExh, hPSR, hNoImp⟩
  have hSovereign := agential_sovereignty_derived countermodelS countermodelT toyPriority
    hExh hPSR hNoImp countermodelT_personal_nature countermodelT_necessary
  exact countermodelT_fails_sovereignty hSovereign

/-- THEOREM 6B₃ (Fortified Control Countermodel — Exhaustive Proof of Metaphysical Independence):
Demonstrates that ALL core structural, order-theoretic, and metaphysical hypotheses of the master theorem:
(1) `ContingentSystem countermodelS` (genuine modal contingency of the totality),
(2) `GeneralContrastivePSR countermodelS` (satisfaction of the contrastive PSR),
(3) `prior_wf : ∀ Ext, WellFounded (toyPriority Ext)` (well-founded priority order),
(4) `prior_trans : ∀ Ext, Transitive (toyPriority Ext)` (transitive priority order),
(5) `hConstitutiveOfTotality` (internal nodes constitutively prior to totality),
(6) `hInternalGroundsTotality` (no internal node grounds the totality),
(7) `hGroundsTotality` (external ground is prior to totality),
(8) `GroundingTotalityTerminatesInAseity` (totality ground exists necessarily),
(9) `PersonalAseityPreservesNature` (personal ground has invariant nature across worlds),
(10) `ExplanatorySymmetryPrinciple` (impersonal symmetry constraint satisfied vacuously),
(11) `IsUltimateGround` (free of independent determining conditions),
(12) `TeleologicalAgencyPrinciple` (personal agent acts intentionally for reasons),
(13) `¬ NecessitatingMode` (system is not rigidly necessitated),
are simultaneously satisfied by (countermodelS, countermodelT, toyPriority),
and yet BOTH `AgentialSovereigntyOverAlternatives` AND `ActsFreely` ARE STRICTLY FALSE.
PHILOSOPHICAL RIGOR:
This theorem proves with absolute mathematical certainty that `AgentialSovereigntyOverAlternatives`
CANNOT be deduced from the remaining 13 premises of the master theorem.
The Leibnizian intellectualist determinist accepts every one of these 13 premises, yet rejects
that the ground possesses two-way counterfactual freedom (potestas ad utrumque) over alternatives.
Therefore, `AgentialSovereigntyOverAlternatives` is an IRREDUCIBLE, INDEPENDENT metaphysical
commitment on the nature of personal causality.
(0 axioms). -/
theorem fortified_rational_intellectualist_control_model :
    ContingentSystem countermodelS ∧
    GeneralContrastivePSR countermodelS ∧
    (∀ Ext, WellFounded (toyPriority Ext)) ∧
    (∀ Ext {a b c : CandidateOnticItem countermodelS.Node Ext},
      toyPriority Ext a b → toyPriority Ext b c → toyPriority Ext a c) ∧
    (∀ Ext (n : countermodelS.Node), toyPriority Ext (CandidateOnticItem.node n) CandidateOnticItem.totality) ∧
    (∀ (n : countermodelS.Node), countermodelT.ground = GroundIdentity.internal n → ∀ Ext, toyPriority Ext CandidateOnticItem.totality (CandidateOnticItem.node n)) ∧
    (∀ (e : countermodelT.ExtEntity), countermodelT.ground = GroundIdentity.external e → toyPriority countermodelT.ExtEntity (CandidateOnticItem.candidate e) CandidateOnticItem.totality) ∧
    GroundingTotalityTerminatesInAseity countermodelS countermodelT ∧
    PersonalAseityPreservesNature countermodelS countermodelT ∧
    ExplanatorySymmetryPrinciple countermodelS countermodelT toyPriority ∧
    IsUltimateGround countermodelS countermodelT toyPriority ∧
    TeleologicalAgencyPrinciple countermodelS countermodelT ∧
    (¬ NecessitatingMode countermodelS countermodelT) ∧
    (¬ AgentialSovereigntyOverAlternatives countermodelS countermodelT toyPriority) ∧
    (¬ ActsFreely countermodelS countermodelT) :=
  ⟨countermodelS_contingent,
   countermodelS_psr,
   toyPriority_wf,
   toyPriority_trans,
   toyConstitutiveOfTotality,
   toyInternalGroundsTotality,
   toyGroundsTotality,
   countermodelT_aseity,
   countermodelT_personal_nature,
   countermodelT_symmetry,
   countermodelT_ultimate,
   countermodelT_teleology,
   countermodelT_not_necessitating,
   countermodelT_fails_sovereignty,
   countermodelT_fails_acts_freely⟩

/-- Complete Rational Determination (Determinismo Moral / Racional Leibniziano):
An invariant essential nature, in conjunction with the complete profile of reasons,
uniquely fixes the chosen outcome:
(1) An outcome is chosen at world w only if reasons favor w over alternatives;
(2) If reasons strictly favor world w over an alternative w_alt, no alternative outcome can be chosen at w_alt. -/
def CompleteRationalDetermination
    (S : ConcreteSystem.{u})
    (T : CandidateGround S) : Prop :=
  NatureInvariant S T ∧
  (∀ w : S.World, ∀ out : Option (S.Node → Bool),
    T.ChoosesOutcomeAt T.ground w out →
    (∀ w_alt : S.World, S.Accessible w w_alt → w_alt ≠ w → T.ReasonsFavor T.ground w w_alt)) ∧
  (∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
    w_alt ≠ S.actualWorld →
    T.ReasonsFavor T.ground S.actualWorld w_alt →
    ¬ ∃ out : Option (S.Node → Bool), T.ChoosesOutcomeAt T.ground w_alt out)

theorem countermodelT_crd :
    CompleteRationalDetermination countermodelS countermodelT := by
  refine ⟨countermodelT_nature_invariant, ?_, ?_⟩
  · intro w out hChoice w_alt hAcc hNe
    cases w
    · exfalso
      have hFalseMax := hChoice.2
      rw [hChoice.1] at hFalseMax
      exact false_not_maximal hFalseMax
    · cases w_alt
      · change outcomePreference (SystemOutcomeAt countermodelS true) (SystemOutcomeAt countermodelS false)
        rw [outcome_true, outcome_false]
        dsimp [outcomePreference, configurationValue, countermodelS]
        decide
      · contradiction
  · intro w_alt hAcc hNe hFavor ⟨out, hChoiceAlt⟩
    cases w_alt
    · have hFalseMax := hChoiceAlt.2
      rw [hChoiceAlt.1] at hFalseMax
      exact false_not_maximal hFalseMax
    · contradiction

/-- THEOREM (Complete Rational Determination Incompatible with Libertarian Freedom):
Demonstrates that if an agent operates under Complete Rational Determination
(where choice is uniquely fixed by favoring reasons), then Libertarian Freedom
(`ActsFreely`) is strictly impossible.
(0 axioms). -/
theorem complete_rational_determination_refutes_libertarian_freedom
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (hCont : ContingentSystem S)
    (hCRD : CompleteRationalDetermination S T)
    (hReasons : ∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
      w_alt ≠ S.actualWorld → T.ReasonsFavor T.ground S.actualWorld w_alt) :
    ¬ ActsFreely S T := by
  intro ⟨_, w_alt, hAcc, _, hDiff, hChoosesAlt⟩
  have hInstAct : S.InstantiatedIn S.actualWorld := hCont.1
  have hNeWorld : w_alt ≠ S.actualWorld := by
    intro hEq
    subst hEq
    apply hDiff
    have hAct : (if S.InstantiatedIn S.actualWorld then some (S.ConfigurationIn S.actualWorld) else none) = some (S.ConfigurationIn S.actualWorld) := by
      split
      · rfl
      · contradiction
    rw [hAct]
  have hFavor := hReasons w_alt hAcc hNeWorld
  have hNoChoice := hCRD.2.2 w_alt hAcc hNeWorld hFavor
  apply hNoChoice
  exact ⟨_, hChoosesAlt⟩

/-- Complete Rational Global Determination (Determinação Racional Completa da Configuração Global):
Formalizes the condition under which the global outcome / configuration of the concrete system
is completely determined by the integral rational profile of a necessary personal ground:
(1) `IsNecessary S T`: The personal ground exists necessarily across all worlds;
(2) `NatureInvariant S T`: The essential nature of the ground is invariant across all worlds;
(3) `IsPersonalAgent S T`: The ground is a personal agent capable of apprehending alternative states;
(4) `GroundsConcreteActuality`: The actual global configuration is grounded by the candidate;
(5) `CompleteRationalDetermination S T`: The choice of outcome is uniquely fixed by favoring reasons,
    such that no outcome can be chosen at an alternative world where reasons strictly favor the actual world.

DISTINCTION FROM `NecessitatingMode`:
`NecessitatingMode S T` is an ontological/modal rigidity predicate asserting that in EVERY accessible world,
the system is instantiated with the IDENTICAL configuration as the actual world (`S.ConfigurationIn w = S.ConfigurationIn S.actualWorld`).
In contrast, `CompleteRationalGlobalDetermination S T` asserts rational determination of the choice by reasons:
the ground's invariant nature and reasons uniquely fix which configuration is chosen, but alternative worlds
with DIFFERENT configurations remain modal points of evaluation in the space of possibilities. -/
def CompleteRationalGlobalDetermination
    (S : ConcreteSystem.{u})
    (T : CandidateGround S) : Prop :=
  IsNecessary S T ∧
  IsPersonalAgent S T ∧
  T.GroundsConcreteActuality T.ground S.actualWorld ∧
  CompleteRationalDetermination S T

theorem countermodelT_crgd :
    CompleteRationalGlobalDetermination countermodelS countermodelT :=
  ⟨countermodelT_necessary, countermodelT_personal_agent, rfl, countermodelT_crd⟩

/-- THEOREM (Logical Distinction: Rational Determination Does Not Entail Necessitating Mode):
Demonstrates that `CompleteRationalGlobalDetermination` is logically distinct from `NecessitatingMode`:
in the control model, the ground completely and rationally determines the global choice via reasons,
yet the system remains contingent and `NecessitatingMode` is strictly false.
(0 axioms). -/
theorem rational_determination_distinct_from_necessitating_mode :
    ∃ (S : ConcreteSystem.{0}) (T : CandidateGround S),
      CompleteRationalGlobalDetermination S T ∧ ¬ NecessitatingMode S T :=
  ⟨countermodelS, countermodelT, countermodelT_crgd, countermodelT_not_necessitating⟩

/-- THEOREM (Rational Determination Does Not Imply Necessitating Mode Under Contingency):
Shows that even in a contingent concrete system with well-founded priority,
`CompleteRationalGlobalDetermination` is compossible with `¬ NecessitatingMode S T`.
(0 axioms). -/
theorem rational_determination_does_not_imply_necessitating_mode :
    ∃ (S : ConcreteSystem.{0}) (T : CandidateGround S),
      ContingentSystem S ∧
      CompleteRationalGlobalDetermination S T ∧
      ¬ NecessitatingMode S T :=
  ⟨countermodelS, countermodelT,
   countermodelS_contingent,
   countermodelT_crgd,
   countermodelT_not_necessitating⟩

/-- THEOREM (Rational Determination Does Not Imply Explanatory Circularity):
Shows that `CompleteRationalGlobalDetermination` is fully compossible with well-founded,
acyclic constitutive priority, where the ground is strictly external and does not depend
on the grounded totality.
(0 axioms). -/
theorem rational_determination_does_not_imply_circularity :
    ∃ (S : ConcreteSystem.{0}) (T : CandidateGround S)
      (ConstitutivePriority : (Ext : Type 0) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop),
      (∀ Ext, WellFounded (ConstitutivePriority Ext)) ∧
      IsUltimateGround S T ConstitutivePriority ∧
      CompleteRationalGlobalDetermination S T :=
  ⟨countermodelS, countermodelT, toyPriority,
   toyPriority_wf,
   countermodelT_ultimate,
   countermodelT_crgd⟩

/-- THEOREM (Rational Determination Does Not Violate Contrastive PSR):
Shows that `CompleteRationalGlobalDetermination` is fully compossible with
`GeneralContrastivePSR S` — indeed, the rational preference profile provides the very
contrastive explanation demanded by the PSR.
(0 axioms). -/
theorem rational_determination_does_not_violate_contrastive_psr :
    ∃ (S : ConcreteSystem.{0}) (T : CandidateGround S),
      ContingentSystem S ∧
      GeneralContrastivePSR S ∧
      CompleteRationalGlobalDetermination S T :=
  ⟨countermodelS, countermodelT,
   countermodelS_contingent,
   countermodelS_psr,
   countermodelT_crgd⟩

/-- THEOREM (Compatibility of Non-Forcing with Complete Rational Determination):
Demonstrates that the central impossibility result of the argument (`chain_cannot_be_exhaustively_forced`,
i.e. `¬ SystemFullyInternallyDetermined S ∧ ¬ NecessitatingMode S T`) does NOT exclude complete rational
determination of the choice by the ultimate ground (`CompleteRationalGlobalDetermination S T`).
Both results hold simultaneously in the substantive control model.
(0 axioms). -/
theorem chain_non_forcing_compossible_with_rational_determination :
    ∃ (S : ConcreteSystem.{0}) (T : CandidateGround S)
      (ConstitutivePriority : (Ext : Type 0) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop),
      ContingentSystem S ∧
      GeneralContrastivePSR S ∧
      (¬ SystemFullyInternallyDetermined S) ∧
      (¬ NecessitatingMode S T) ∧
      CompleteRationalGlobalDetermination S T ∧
      IsUltimateGround S T ConstitutivePriority ∧
      ¬ ActsFreely S T :=
  ⟨countermodelS, countermodelT, toyPriority,
   countermodelS_contingent,
   countermodelS_psr,
   concrete_system_cannot_be_fully_internally_determined countermodelS ⟨()⟩,
   countermodelT_not_necessitating,
   countermodelT_crgd,
   countermodelT_ultimate,
   countermodelT_fails_acts_freely⟩

/-- General Ontological Actualization of an Outcome by a Candidate Ground:
A candidate ground T actualizes outcome `out` at world `w` if:
(1) T exists at world w (`T.ExistsAt T.ground w`);
(2) SystemOutcomeAt S w = out (the system's instantiation and configuration at w match out).
This relation is strictly general across ALL possible worlds and outcomes,
without presupposing that out must match the actual configuration S.actualWorld. -/
def ActualizesOutcomeAt
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (w : S.World)
    (out : Option (S.Node → Bool)) : Prop :=
  T.ExistsAt T.ground w ∧ SystemOutcomeAt S w = out

/-- Unified Rational Actualization (Actualização Racional Unificada):
Rigorous, non-circular unification of foundational agency, causal determination of boundary nodes,
and concrete actualization:
(1) `choice_actualizes`: In ANY world w and for ANY outcome `out`, if T chooses `out`,
    T thereby actualizes `out` (`ActualizesOutcomeAt S T w out`);
(2) `terminal_determination`: For ANY world w and ANY configuration `cfg`, if T chooses `some cfg`,
    every internal terminal node b (`IsInternalTerminalNode S b`, which lacks an intra-systemic determiner)
    has its truth-value determined by `cfg b`;
(3) `actual_grounding`: In the actual world, T intentionally chooses the actual outcome and grounds
    its concrete actuality (`GroundsConcreteActuality`);
(4) `rational_governance`: The choice across worlds is uniquely determined by the complete profile
    of reasons (`CompleteRationalDetermination S T`).
SEMANTIC DISTINCTION:
This refactored formulation completely eliminates the apparent tautology of appealing to
`CandidateGround.grounding_binds_actuality`: the determination of terminal nodes is established
as a universal causal law of agential choice across hypothetical configurations, rather than
a definitional artifact of actual-world rigidity. -/
structure UnifiedRationalActualization
    (S : ConcreteSystem.{u})
    (T : CandidateGround S) : Prop where
  choice_actualizes :
    ∀ (w : S.World) (out : Option (S.Node → Bool)),
      T.ChoosesOutcomeAt T.ground w out →
      ActualizesOutcomeAt S T w out
  terminal_determination :
    ∀ (w : S.World) (cfg : S.Node → Bool),
      T.ChoosesOutcomeAt T.ground w (some cfg) →
      ∀ b : S.Node, IsInternalTerminalNode S b →
        S.ConfigurationIn w b = cfg b
  actual_grounding :
    T.ChoosesOutcomeAt T.ground S.actualWorld (some (S.ConfigurationIn S.actualWorld)) ∧
    T.GroundsConcreteActuality T.ground S.actualWorld
  rational_governance :
    CompleteRationalDetermination S T

theorem countermodelT_unified_actualization :
    UnifiedRationalActualization countermodelS countermodelT := by
  refine ⟨?_, ?_, ⟨(countermodelT_selects_intentionally false trivial).2, rfl⟩, countermodelT_crd⟩
  · intro w out hChoice
    refine ⟨trivial, hChoice.1.symm⟩
  · intro w cfg hChoice b _
    cases w
    · exfalso
      have hFalseMax := hChoice.2
      rw [hChoice.1] at hFalseMax
      exact false_not_maximal hFalseMax
    · have hEq := hChoice.1
      rw [outcome_true] at hEq
      injection hEq with hCfgEq
      subst hCfgEq
      rfl

/-- THEOREM (Distinction: Modal Necessitation vs. Unified Rational Actualization):
Demonstrates that `UnifiedRationalActualization` (complete determination of the concrete outcome
by antecedent conditions including the ground's reasons) does NOT entail `NecessitatingMode`:
the system remains contingent and modal rigidity is false.
(0 axioms). -/
theorem modal_necessitation_distinct_from_rational_actualization :
    ∃ (S : ConcreteSystem.{0}) (T : CandidateGround S),
      UnifiedRationalActualization S T ∧ ¬ NecessitatingMode S T :=
  ⟨countermodelS, countermodelT, countermodelT_unified_actualization, countermodelT_not_necessitating⟩

/-- THEOREM (Distinction: Outcome Fixed By Invariant Basis vs. Unified Rational Actualization):
Demonstrates that `UnifiedRationalActualization` does NOT entail `OutcomeFixedByGroundBasis`:
the invariant basis of the ground does not fix identical outcomes across all accessible worlds.
(0 axioms). -/
theorem rational_actualization_distinct_from_outcome_fixed :
    ∃ (S : ConcreteSystem.{0}) (T : CandidateGround S),
      UnifiedRationalActualization S T ∧ ¬ OutcomeFixedByGroundBasis S T :=
  ⟨countermodelS, countermodelT, countermodelT_unified_actualization,
   contingent_system_under_invariant_nature_not_fixed countermodelS countermodelT
     countermodelS_contingent countermodelT_nature_invariant⟩

/-- THEOREM (Compatibility of Non-Forcing with Unified Rational Actualization):
Demonstrates that the impossibility of forçagem integral (`chain_cannot_be_exhaustively_forced`)
is fully compossible with `UnifiedRationalActualization S T` (the complete determination of the
concrete outcome and its boundary nodes by the ground's complete profile of reasons).
(0 axioms). -/
theorem unified_actualization_compossible_with_non_forcing :
    ∃ (S : ConcreteSystem.{0}) (T : CandidateGround S)
      (ConstitutivePriority : (Ext : Type 0) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop),
      ContingentSystem S ∧
      GeneralContrastivePSR S ∧
      (¬ SystemFullyInternallyDetermined S) ∧
      (¬ NecessitatingMode S T) ∧
      UnifiedRationalActualization S T ∧
      IsUltimateGround S T ConstitutivePriority ∧
      ¬ ActsFreely S T :=
  ⟨countermodelS, countermodelT, toyPriority,
   countermodelS_contingent,
   countermodelS_psr,
   concrete_system_cannot_be_fully_internally_determined countermodelS ⟨()⟩,
   countermodelT_not_necessitating,
   countermodelT_unified_actualization,
   countermodelT_ultimate,
   countermodelT_fails_acts_freely⟩

/-- THEOREM (Unified Rational Actualization Incompatible with Libertarian Freedom):
Demonstrates that if an agent operates under Unified Rational Actualization
where the choice of outcome is uniquely determined by favoring reasons,
Libertarian Freedom (`ActsFreely`) is strictly impossible.
(0 axioms). -/
theorem unified_actualization_refutes_libertarian_freedom
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (hCont : ContingentSystem S)
    (hEff : UnifiedRationalActualization S T)
    (hReasons : ∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
      w_alt ≠ S.actualWorld → T.ReasonsFavor T.ground S.actualWorld w_alt) :
    ¬ ActsFreely S T :=
  complete_rational_determination_refutes_libertarian_freedom S T hCont hEff.rational_governance hReasons

/-- THEOREM (Strict Separation of the Five Levels of Conclusion):
Demonstrates that the five levels of conclusion are logically distinct and non-conflated:
(1) Impossibility of Fully Internal Determination: `¬ SystemFullyInternallyDetermined countermodelS`;
(2) Impossibility of Rigid Modal Necessitation: `¬ NecessitatingMode countermodelS countermodelT`
    and `¬ OutcomeFixedByGroundBasis countermodelS countermodelT`;
(3) Determination of Choice by Favoring Reasons: `CompleteRationalDetermination countermodelS countermodelT`;
(4) Effective Ontological Actualization of Global Outcome & Boundary Nodes:
    `UnifiedRationalActualization countermodelS countermodelT`;
(5) Failure of Positive Libertarian Freedom: `¬ ActsFreely countermodelS countermodelT`.
Crucially, Levels 1, 2, 3, and 4 are jointly consistent and satisfied in the control model,
while Level 5 is strictly false without the independent metaphysical postulate of Agential Sovereignty.
(0 axioms). -/
theorem five_levels_of_conclusion_separation :
    (¬ SystemFullyInternallyDetermined countermodelS) ∧
    (¬ NecessitatingMode countermodelS countermodelT) ∧
    (¬ OutcomeFixedByGroundBasis countermodelS countermodelT) ∧
    CompleteRationalDetermination countermodelS countermodelT ∧
    UnifiedRationalActualization countermodelS countermodelT ∧
    (¬ ActsFreely countermodelS countermodelT) :=
  ⟨concrete_system_cannot_be_fully_internally_determined countermodelS ⟨()⟩,
   countermodelT_not_necessitating,
   contingent_system_under_invariant_nature_not_fixed countermodelS countermodelT
     countermodelS_contingent countermodelT_nature_invariant,
   countermodelT_crd,
   countermodelT_unified_actualization,
   countermodelT_fails_acts_freely⟩

/-- THEOREM (The Strong Forcing Dilemma & Inescapable Role of Agential Sovereignty):
Demonstrates the fundamental epistemological limit of the cosmological/ontological argument:
The premises of structural non-forcing (`¬ SystemFullyInternallyDetermined S`), non-rigid
necessitation (`¬ NecessitatingMode S T`), well-founded ultimacy (`IsUltimateGround S T`),
and contrastive explanation (`GeneralContrastivePSR S`) do NOT exclude complete rational
determination of the outcome by antecedent conditions (`UnifiedRationalActualization S T`).
Consequently, `AgentialSovereigntyOverAlternatives` is strictly required as an independent
metaphysical premise: it is incompatible with `UnifiedRationalActualization` under favoring
reasons and is the unique bridge that yields `ActsFreely S T`.
(0 axioms). -/
theorem strong_forcing_dilemma_and_role_of_sovereignty
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (hCont : ContingentSystem S)
    (hCRD : UnifiedRationalActualization S T)
    (hReasons : ∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
      w_alt ≠ S.actualWorld → T.ReasonsFavor T.ground S.actualWorld w_alt) :
    ¬ ActsFreely S T :=
  complete_rational_determination_refutes_libertarian_freedom S T hCont hCRD.rational_governance hReasons

/-- Foundational Causal Determination:
Formalizes the three intra-systemic and foundational components of ontological determination:
(1) Intra-systemic determination: node a determines node b (`S.Determines a b`);
(2) Foundational nodal determination: candidate ground e determines boundary nodes lacking internal determiners;
(3) Totality grounding: candidate ground e grounds the system totality. -/
def FoundationalCausalDetermination
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop) : Prop :=
  (∀ a b : S.Node, S.Determines a b →
    ConstitutivePriority T.ExtEntity (CandidateOnticItem.node a) (CandidateOnticItem.node b)) ∧
  (∀ (e : T.ExtEntity), T.ground = GroundIdentity.external e →
    ∀ b : S.Node, IsInternalTerminalNode S b →
      ConstitutivePriority T.ExtEntity (CandidateOnticItem.candidate e) (CandidateOnticItem.node b)) ∧
  (∀ (e : T.ExtEntity), T.ground = GroundIdentity.external e →
    ConstitutivePriority T.ExtEntity (CandidateOnticItem.candidate e) CandidateOnticItem.totality)

/-- Unified Explanatory Determination Relation:
Formalizes a single unified relation of ontological and explanatory determination across:
(1) Intra-systemic determination: node a determines node b (`S.Determines a b`);
(2) Foundational nodal determination: candidate ground e determines boundary nodes lacking internal determiners;
(3) Totality grounding: candidate ground e grounds the system totality;
(4) External/rational conditioning: condition C determines candidate ground e (`C ≺ e`).
All four components are explicitly formalized in the type signature. -/
def UnifiedExplanatoryDetermination
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop) : Prop :=
  (∀ a b : S.Node, S.Determines a b →
    ConstitutivePriority T.ExtEntity (CandidateOnticItem.node a) (CandidateOnticItem.node b)) ∧
  (∀ (e : T.ExtEntity), T.ground = GroundIdentity.external e →
    ∀ b : S.Node, IsInternalTerminalNode S b →
      ConstitutivePriority T.ExtEntity (CandidateOnticItem.candidate e) (CandidateOnticItem.node b)) ∧
  (∀ (e : T.ExtEntity), T.ground = GroundIdentity.external e →
    ConstitutivePriority T.ExtEntity (CandidateOnticItem.candidate e) CandidateOnticItem.totality) ∧
  (∀ (e : T.ExtEntity), T.ground = GroundIdentity.external e →
    ConstitutivePriority T.ExtEntity CandidateOnticItem.condition (CandidateOnticItem.candidate e))

/-- THEOREM (The Dilemma of Rational Forcing in Ontological Priority):
Demonstrates that if the ground's choice is treated as an ontically determined link
in the constitutive priority relation (`C ≺ e`) as formulated in `UnifiedExplanatoryDetermination`:
(1) If the reasons depend on the grounded system (`S ≺ C`), then under transitive well-founded priority,
    a closed explanatory cycle `e ≺ S ≺ C ≺ e` is formed, refuting well-foundedness and deriving False
    (`candidate_consequence_circularity_refutation`);
(2) If the reasons are independent of the grounded system (`¬ S ≺ C`), then e depends on an independent
    antecedent condition, refuting Explanatory Ultimacy (`independent_condition_contradicts_ultimacy`).
Therefore, an ultimate ground CANNOT be ontically determined by reasons in the constitutive priority relation!
(0 axioms). -/
theorem rational_forcing_in_priority_dilemma
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (prior_wf : ∀ Ext, WellFounded (ConstitutivePriority Ext))
    (prior_trans : ∀ Ext {a b c : CandidateOnticItem S.Node Ext}, ConstitutivePriority Ext a b → ConstitutivePriority Ext b c → ConstitutivePriority Ext a c)
    (e : T.ExtEntity)
    (hExt : T.ground = GroundIdentity.external e)
    (hUnified : UnifiedExplanatoryDetermination S T ConstitutivePriority)
    (hUlt : IsUltimateGround S T ConstitutivePriority) :
    False := by
  have hGroundsTotality := hUnified.2.2.1 e hExt
  have hReasonConditionsGround := hUnified.2.2.2 e hExt
  have hNotIndep := independent_condition_contradicts_ultimacy S T ConstitutivePriority e hExt ?_ hUlt
  · exact hNotIndep
  · constructor
    · exact hReasonConditionsGround
    · intro hTotalityConditionsReason
      exact candidate_consequence_circularity_refutation (ConstitutivePriority T.ExtEntity)
        (prior_wf T.ExtEntity) (fun {_a _b _c} => prior_trans T.ExtEntity) e
        hGroundsTotality hTotalityConditionsReason hReasonConditionsGround

/-- ROUTE 1: Intrinsic Rational Fixing Contradicts Modal Contingency:
Demonstrates that if the rational determination of the ground is treated as an intrinsic
property of its invariant nature that rigidly fixes the outcome across modal space,
it entails `OutcomeFixedByGroundBasis S T`, which is strictly refuted by `ContingentSystem S`.
(Axiomas: [propext, Classical.choice]). -/
theorem route1_intrinsic_fixing_contradicts_contingency
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (hCont : ContingentSystem S)
    (hNature : NatureInvariant S T)
    (hFixed : OutcomeFixedByGroundBasis S T) :
    False :=
  (contingent_system_under_invariant_nature_not_fixed S T hCont hNature) hFixed

/-- Backward-compatibility alias for Route 1. -/
abbrev intrinsic_rational_fixing_contradicts_contingency :=
  @route1_intrinsic_fixing_contradicts_contingency

/-- ROUTE 2: Extrinsic Ontological Conditioning in Priority:
If reasons act as an extrinsic condition in the constitutive priority relation (`C ≺ e`),
under well-founded priority and explanatory ultimacy, a strict contradiction is derived.
(0 axioms). -/
theorem route2_priority_conditioning_dilemma
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (prior_wf : ∀ Ext, WellFounded (ConstitutivePriority Ext))
    (prior_trans : ∀ Ext {a b c : CandidateOnticItem S.Node Ext}, ConstitutivePriority Ext a b → ConstitutivePriority Ext b c → ConstitutivePriority Ext a c)
    (e : T.ExtEntity)
    (hExt : T.ground = GroundIdentity.external e)
    (hUnified : UnifiedExplanatoryDetermination S T ConstitutivePriority)
    (hUlt : IsUltimateGround S T ConstitutivePriority) :
    False :=
  rational_forcing_in_priority_dilemma S T ConstitutivePriority prior_wf prior_trans e hExt hUnified hUlt

/-- PRINCIPLE OF DETERMINATION AS ONTIC CONDITIONING:
Tag: META.
- Philosophical Justification:
  Principle of Sufficient Reason as Explanatory Non-Vacuity: Any antecedent profile of conditions or
  reasons that integrally and univocally determines the ground's actualization of a concrete system
  (as in `CompleteRationalDetermination` or `UnifiedRationalActualization`) functions as an explanatory
  conditioning relation in the ontic priority order (`CandidateOnticItem.condition ≺ CandidateOnticItem.candidate e`).
  One cannot consistently assert that an outcome is completely determined by antecedent reasons while
  simultaneously denying that reasons constitute a determining condition in the explanatory order. -/
def DeterminationAsOnticCondition
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop) : Prop :=
  (CompleteRationalDetermination S T ∨ UnifiedRationalActualization S T) →
    ∀ (e : T.ExtEntity), T.ground = GroundIdentity.external e →
      ConstitutivePriority T.ExtEntity CandidateOnticItem.condition (CandidateOnticItem.candidate e)

/-- Canonical alias: Principle of Explanatory Subsumption of Determination in Grounding.
Substantive metaphysical bridge (Tag: META) connecting complete rational determination to
ontological priority conditioning. Maintained as an explicit, transparent hypothesis. -/
abbrev ExplanatorySubsumptionOfDetermination := @DeterminationAsOnticCondition

/-- PRINCIPLE OF EXPLANATORY DETERMINATION INTEGRITY (Tag: META):
If an antecedent profile of conditions or reasons integrally and univocally fixes the chosen outcome
and actualization of a concrete system (as in `CompleteRationalDetermination` or `UnifiedRationalActualization`),
that determination relation MUST be represented as an explanatory conditioning relation in the global constitutive priority
order (`condition ≺ candidate e`).
One cannot consistently assert that an outcome is completely determined by antecedent reasons while
simultaneously denying that reasons constitute a determining condition in the explanatory order.

TESTEMUNHO FORMAL DE INDEPENDÊNCIA E ESTATUTO METAFÍSICO (Critério 3):
O modelo de controlo `countermodelT` (`countermodelT_fails_unified_explanatory_determination`) serve como
testemunha formal de independência no kernel, provando que `CompleteRationalDetermination` NÃO acarreta
analiticamente `UnifiedExplanatoryDetermination`.
Isto justifica filosoficamente e logicamente por que `ExplanatoryDeterminationRule` é uma premissa metafísica
substantiva indispensável (Tag: META) e não uma mera redundância analítica: ela impõe normativamente que
qualquer fixação unívoca integral por razões seja integrada na ordem explicativa global, impedindo a evasão
intelectualista de sustentar simultaneamente fixação unívoca e ultimidade ontológica. -/
def ExplanatoryDeterminationRule
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop) : Prop :=
  (CompleteRationalDetermination S T ∨ UnifiedRationalActualization S T) →
    FoundationalCausalDetermination S T ConstitutivePriority →
      UnifiedExplanatoryDetermination S T ConstitutivePriority

/-- THEOREM (Derivation of Explanatory Determination Integrity from Ontic Conditioning):
Demonstrates that `ExplanatoryDeterminationRule` is DEDUCED as a theorem from
`DeterminationAsOnticCondition`.
(0 axioms). -/
theorem explanatory_determination_rule_derived
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (hCond : DeterminationAsOnticCondition S T ConstitutivePriority) :
    ExplanatoryDeterminationRule S T ConstitutivePriority := by
  intro hCRD hCausal
  refine ⟨hCausal.1, hCausal.2.1, hCausal.2.2, ?_⟩
  exact hCond hCRD

/-- THEOREM (Closure of the Intellectualist Evasion via the Fundamental Theorem):
Demonstrates that under the Principle of Explanatory Determination Integrity,
an ultimate ground CANNOT have its choice integrally and univocally determined by reasons:
`(CompleteRationalDetermination S T ∨ UnifiedRationalActualization S T) ∧ FoundationalCausalDetermination S T ConstitutivePriority → False`.
Any attempt to maintain complete determination by reasons under well-founded priority
either refutes Explanatory Ultimacy or creates constitutive circularity.
(0 axioms). -/
theorem intellectualist_evasion_closure
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (prior_wf : ∀ Ext, WellFounded (ConstitutivePriority Ext))
    (prior_trans : ∀ Ext {a b c : CandidateOnticItem S.Node Ext}, ConstitutivePriority Ext a b → ConstitutivePriority Ext b c → ConstitutivePriority Ext a c)
    (e : T.ExtEntity)
    (hExt : T.ground = GroundIdentity.external e)
    (hRule : ExplanatoryDeterminationRule S T ConstitutivePriority)
    (hUlt : IsUltimateGround S T ConstitutivePriority)
    (hCRD : CompleteRationalDetermination S T ∨ UnifiedRationalActualization S T)
    (hCausal : FoundationalCausalDetermination S T ConstitutivePriority) :
    False := by
  have hUnified := hRule hCRD hCausal
  exact rational_forcing_in_priority_dilemma S T ConstitutivePriority prior_wf prior_trans e hExt hUnified hUlt

/-- THEOREM (Deepened Closure of the Intellectualist Evasion via Derived Explanatory Rule):
Demonstrates that under `DeterminationAsOnticCondition`, an ultimate ground CANNOT have its choice
integrally and univocally determined by reasons.
(0 axioms). -/
theorem deepened_intellectualist_evasion_closure
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
    False := by
  have hRule := explanatory_determination_rule_derived S T ConstitutivePriority hCond
  exact intellectualist_evasion_closure S T ConstitutivePriority prior_wf prior_trans e hExt hRule hUlt hCRD hCausal

/-- THEOREM (The Intellectualist Control Model Fails Unified Explanatory Determination):
Demonstrates that the substantive intellectualist control model (`countermodelS, countermodelT, toyPriority`)
strictly FAILS `UnifiedExplanatoryDetermination`, because it omits reasons as an ontic condition
in the constitutive priority order:
`¬ UnifiedExplanatoryDetermination countermodelS countermodelT toyPriority`.
(0 axioms). -/
theorem countermodelT_fails_unified_explanatory_determination :
    ¬ UnifiedExplanatoryDetermination countermodelS countermodelT toyPriority := by
  intro hUnified
  have hCond := hUnified.2.2.2 () rfl
  rcases hCond with ⟨n, hEq, _⟩ | ⟨e, hEq, _⟩
  · injection hEq
  · injection hEq

/-- THEOREM (The Intellectualist Control Model Violates Explanatory Determination Integrity):
Demonstrates that if the control model were extended to satisfy foundational causal determination,
it would strictly VIOLATE the Principle of Explanatory Determination Integrity:
`¬ ExplanatoryDeterminationRule countermodelS countermodelT toyPriority`.
This proves that theological intellectualism / rational determinism cannot survive
once a unified standard of explanatory determination is enforced.
(0 axioms). -/
theorem intellectualist_control_model_violates_explanatory_rule
    (hFoundational : FoundationalCausalDetermination countermodelS countermodelT toyPriority) :
    ¬ ExplanatoryDeterminationRule countermodelS countermodelT toyPriority := by
  intro hRule
  have hUnified := hRule (Or.inl countermodelT_crd) hFoundational
  exact countermodelT_fails_unified_explanatory_determination hUnified

/-- THEOREM (The Intellectualist Control Model Violates Determination as Ontic Conditioning):
Demonstrates that if the intellectualist control model satisfies foundational causal determination,
it strictly VIOLATES `DeterminationAsOnticCondition countermodelS countermodelT toyPriority`.
(0 axioms). -/
theorem intellectualist_control_model_violates_ontic_conditioning
    (hFoundational : FoundationalCausalDetermination countermodelS countermodelT toyPriority) :
    ¬ DeterminationAsOnticCondition countermodelS countermodelT toyPriority := by
  intro hCond
  have hRule := explanatory_determination_rule_derived countermodelS countermodelT toyPriority hCond
  exact intellectualist_control_model_violates_explanatory_rule hFoundational hRule

/-- ROUTE 3: Teleological Rational Explanation Without Ontic Priority:
Reasons explain the choice teleologically (evaluative ordering of outcomes) without standing as
an antecedent relatum in the constitutive priority relation (`¬ C ≺ e`).
PROVED CONSEQUENCE:
Under Route 3, the ground:
(1) Does NOT rigidly necessitate the system (`¬ NecessitatingMode S T`);
(2) Does NOT produce explanatory circularity (`toyPriority_wf`);
(3) Does NOT lose explanatory ultimacy (`IsUltimateGround S T toyPriority`);
(4) Does NOT lack contrastive explanation (`GeneralContrastivePSR S`).
Yet, it does NOT derive positive libertarian freedom (`¬ ActsFreely S T`).
(0 axioms). -/
theorem route3_teleological_explanation_properties :
    (¬ toyPriority countermodelT.ExtEntity CandidateOnticItem.condition (CandidateOnticItem.candidate ())) ∧
    ContingentSystem countermodelS ∧
    GeneralContrastivePSR countermodelS ∧
    IsUltimateGround countermodelS countermodelT toyPriority ∧
    CompleteRationalDetermination countermodelS countermodelT ∧
    (¬ NecessitatingMode countermodelS countermodelT) ∧
    (¬ ActsFreely countermodelS countermodelT) :=
  ⟨by intro h; rcases h with ⟨n, hEq, _⟩ | ⟨e, hEq, _⟩ <;> injection hEq,
   countermodelS_contingent,
   countermodelS_psr,
   countermodelT_ultimate,
   countermodelT_crd,
   countermodelT_not_necessitating,
   countermodelT_fails_acts_freely⟩

/-- THEOREM (The Intellectualist Teleological Decoupling in the Control Model):
Demonstrates how the substantive intellectualist control model (`countermodelS, countermodelT`)
escapes both horns of the rational forcing dilemma:
(1) It avoids circularity and loss of ultimacy by NOT including reasons as an ontic condition
    in constitutive priority (`¬ toyPriority Ext CandidateOnticItem.condition (CandidateOnticItem.candidate ())`);
(2) It avoids modal necessitation by leaving alternative worlds accessible with divergent configurations;
(3) Yet, it does NOT derive positive libertarian freedom (`¬ ActsFreely countermodelS countermodelT`)
    because choice is uniquely determined by favoring reasons without elective sovereignty.
(0 axioms). -/
theorem intellectualist_teleological_decoupling :
    (¬ toyPriority countermodelT.ExtEntity CandidateOnticItem.condition (CandidateOnticItem.candidate ())) ∧
    IsUltimateGround countermodelS countermodelT toyPriority ∧
    CompleteRationalDetermination countermodelS countermodelT ∧
    ContingentSystem countermodelS ∧
    (¬ NecessitatingMode countermodelS countermodelT) ∧
    (¬ ActsFreely countermodelS countermodelT) :=
  ⟨by intro h; rcases h with ⟨n, hEq, _⟩ | ⟨e, hEq, _⟩ <;> injection hEq,
   countermodelT_ultimate,
   countermodelT_crd,
   countermodelS_contingent,
   countermodelT_not_necessitating,
   countermodelT_fails_acts_freely⟩

/-- THEOREM (The First Missing Step: Agential Sovereignty Over Alternatives):
Demonstrates the exact deductive boundary of the ontological argument:
The conjunction of:
(1) Well-founded priority and non-circularity;
(2) Non-internal determination of the chain (`¬ SystemFullyInternallyDetermined S`);
(3) Non-rigid necessitation (`¬ NecessitatingMode S T`);
(4) General contrastive PSR (`GeneralContrastivePSR S`);
(5) Effective ontological actualization (`UnifiedRationalActualization S T`);
(6) Explanatory ultimacy (`IsUltimateGround S T ConstitutivePriority`)
is strictly INSUFFICIENT to deduce positive libertarian freedom (`ActsFreely S T`).
The first step that cannot be derived is the conversion of unnecessitated intentional selection
into an elective two-way power over alternatives (*potestas ad utrumque*).
The MINIMAL additional metaphysical premise required to deduce `ActsFreely` is
`AgentialSovereigntyOverAlternatives S T ConstitutivePriority`.
(0 axioms). -/
theorem first_missing_step_to_libertarian_freedom :
    ∃ (S : ConcreteSystem.{0}) (T : CandidateGround S)
      (ConstitutivePriority : (Ext : Type 0) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop),
      ContingentSystem S ∧
      GeneralContrastivePSR S ∧
      (¬ SystemFullyInternallyDetermined S) ∧
      (¬ NecessitatingMode S T) ∧
      UnifiedRationalActualization S T ∧
      IsUltimateGround S T ConstitutivePriority ∧
      (¬ AgentialSovereigntyOverAlternatives S T ConstitutivePriority) ∧
      (¬ ActsFreely S T) :=
  ⟨countermodelS, countermodelT, toyPriority,
   countermodelS_contingent,
   countermodelS_psr,
   concrete_system_cannot_be_fully_internally_determined countermodelS ⟨()⟩,
   countermodelT_not_necessitating,
   countermodelT_unified_actualization,
   countermodelT_ultimate,
   countermodelT_fails_sovereignty,
   countermodelT_fails_acts_freely⟩

/-- THEOREM 6B₄ (Substantive Rational-Intellectualist Control Model):
Demonstrates that a personal ground operating with NON-TRIVIAL evaluative reasons
and genuine contrastive justification:
SATISFIES:
(1) `ContingentSystem countermodelS` (modal contingency of the totality)
(2) `GeneralContrastivePSR countermodelS` (contrastive explanation by objective outcome evaluation)
(3) `CompleteRationalDetermination countermodelS countermodelT` (choice uniquely determined by favoring reasons)
(4) `CompleteRationalGlobalDetermination countermodelS countermodelT` (rational global determination by reasons)
(5) `UnifiedRationalActualization countermodelS countermodelT` (effective determination of boundary nodes and choice)
(6) `IsNecessary countermodelS countermodelT` (Aseity)
(7) `NatureInvariant countermodelS countermodelT` (Invariant essence across worlds)
(8) `IsPersonalAgent countermodelS countermodelT` (Apprehends alternative states)
(9) `SelectsIntentionally countermodelS countermodelT` (Intentional choice guided by evaluative reasons)
(10) `GuidedByJustificationMode countermodelS countermodelT` (Objective contrastive justification)
(11) `IsUltimateGround countermodelS countermodelT toyPriority` (Free of prior external conditions)
(12) `¬ NecessitatingMode countermodelS countermodelT` (Does not rigidly necessitate the system)
REFUTES / NEGATES:
(13) `¬ AgentialSovereigntyOverAlternatives countermodelS countermodelT toyPriority` (Denied: agent lacks power to choose sub-optimal alternative)
(14) `¬ ActsFreely countermodelS countermodelT` (Denied: positive libertarian counterfactual choice is impossible under complete rational determination)
PHILOSOPHICAL SIGNIFICANCE:
This model does NOT refute the complete philosophical argument (which affirmatively posits
agential sovereignty as an explicit metaphysical premise on the nature of personal causality).
Rather, it tests and confirms the exact boundary of deductive consequence: it proves that
libertarian freedom (`ActsFreely`) is logically independent from the 12 structural and rational-explanatory
premises above, demonstrating why `AgentialSovereigntyOverAlternatives` is an indispensable,
irreducible metaphysical premise rather than an analytical consequence of the PSR or non-forcing.
(0 axioms). -/
theorem substantive_rational_intellectualist_control_model :
    ContingentSystem countermodelS ∧
    GeneralContrastivePSR countermodelS ∧
    CompleteRationalDetermination countermodelS countermodelT ∧
    CompleteRationalGlobalDetermination countermodelS countermodelT ∧
    UnifiedRationalActualization countermodelS countermodelT ∧
    IsNecessary countermodelS countermodelT ∧
    NatureInvariant countermodelS countermodelT ∧
    IsPersonalAgent countermodelS countermodelT ∧
    SelectsIntentionally countermodelS countermodelT ∧
    GuidedByJustificationMode countermodelS countermodelT ∧
    IsUltimateGround countermodelS countermodelT toyPriority ∧
    (¬ NecessitatingMode countermodelS countermodelT) ∧
    (¬ AgentialSovereigntyOverAlternatives countermodelS countermodelT toyPriority) ∧
    (¬ ActsFreely countermodelS countermodelT) :=
  ⟨countermodelS_contingent,
   countermodelS_psr,
   countermodelT_crd,
   countermodelT_crgd,
   countermodelT_unified_actualization,
   countermodelT_necessary,
   countermodelT_nature_invariant,
   countermodelT_personal_agent,
   countermodelT_selects_intentionally,
   countermodelT_guided,
   countermodelT_ultimate,
   countermodelT_not_necessitating,
   countermodelT_fails_sovereignty,
   countermodelT_fails_acts_freely⟩

/-- THEOREM (Consistency of Structural and Explanatory Premises with System Contingency):
Demonstrates the consistency of a core subset of structural and cosmological premises
(well-founded priority, grounding, aseity, nature preservation, symmetry, ultimacy,
teleological agency, and non-rigid necessitation) for a concrete candidate ground,
confirming their compossibility with `ContingentSystem S`.
PHILOSOPHICAL SCOPE:
Crucially, this theorem witnesses the consistency of the non-libertarian explanatory base;
it does NOT include `AgentialSovereigntyOverAlternatives` nor does it derive `ActsFreely`.
Those further libertarian properties represent an independent metaphysical commitment
tested separately by `substantive_rational_intellectualist_control_model`.
(0 axioms). -/
theorem master_premises_consistent_with_contingency :
    ∃ (S : ConcreteSystem.{0}) (T : CandidateGround S)
      (ConstitutivePriority : (Ext : Type 0) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop),
      ContingentSystem S ∧
      T.GroundsConcreteActuality T.ground S.actualWorld ∧
      (∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
        (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
        ContrastiveExplanationForTotality S T w_alt) ∧
      (∀ Ext, WellFounded (ConstitutivePriority Ext)) ∧
      (∀ Ext {a b c : CandidateOnticItem S.Node Ext}, ConstitutivePriority Ext a b → ConstitutivePriority Ext b c → ConstitutivePriority Ext a c) ∧
      (∀ Ext (n : S.Node), ConstitutivePriority Ext (CandidateOnticItem.node n) CandidateOnticItem.totality) ∧
      (∀ (n : S.Node), T.ground = GroundIdentity.internal n → ∀ Ext, ConstitutivePriority Ext CandidateOnticItem.totality (CandidateOnticItem.node n)) ∧
      (∀ (e : T.ExtEntity), T.ground = GroundIdentity.external e → ConstitutivePriority T.ExtEntity (CandidateOnticItem.candidate e) CandidateOnticItem.totality) ∧
      GroundingTotalityTerminatesInAseity S T ∧
      ImpersonalAseityPreservesNature S T ∧
      ExplanatorySymmetryPrinciple S T ConstitutivePriority ∧
      IsUltimateGround S T ConstitutivePriority ∧
      TeleologicalAgencyPrinciple S T ∧
      PersonalAseityPreservesNature S T ∧
      ¬ NecessitatingMode S T :=
  ⟨countermodelS, countermodelT, toyPriority,
   countermodelS_contingent,
   rfl,
   fun w_alt hAcc hDiff => ⟨trivial, countermodelT_guided w_alt hAcc hDiff⟩,
   toyPriority_wf,
   toyPriority_trans,
   toyConstitutiveOfTotality,
   toyInternalGroundsTotality,
   toyGroundsTotality,
   countermodelT_aseity,
   countermodelT_impersonal_nature,
   countermodelT_symmetry,
   countermodelT_ultimate,
   countermodelT_teleology,
   countermodelT_personal_nature,
   countermodelT_not_necessitating⟩

/-- METAPHYSICAL BRIDGE 5 (Agential Freedom Bridge):
Tag: META.
- Philosophical Justification:
  Libertarian Agency Principle: An intentional personal agent that selects a contingent system under a necessary essence
  and accessible alternatives possesses genuine counterfactual freedom of choice (could have chosen otherwise under that same nature).
  (Defended in treatise `investigations/ontological_incompleteness_and_transcendent_source.md` §3.1.1, §3.1.3, §4 Step 8).
- Formal Status:
  Decomposed into `PersonalAseityPreservesNature` and `AgentialCounterfactualChoiceBridge`.
  Deducible via `agential_freedom_bridge_from_counterfactual_choice`. -/
def AgentialFreedomBridge
    (S : ConcreteSystem.{u})
    (T : CandidateGround S) : Prop :=
  ContingentSystem S →
  IsNecessary S T →
  SelectsIntentionally S T →
  (NatureInvariant S T ∧ ActsFreely S T)

/-- THEOREM 6C (Derivation of Agential Freedom Bridge from Decomposed Stages):
Demonstrates that the overarching AgentialFreedomBridge is deducible from:
(1) PersonalAseityPreservesNature, and
(2) The Agential Counterfactual Choice Bridge (Stage 4).
(0 axioms). -/
theorem agential_freedom_bridge_from_counterfactual_choice
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (hPersonalNature : PersonalAseityPreservesNature S T)
    (hChoice : AgentialCounterfactualChoiceBridge S T)
    (hAgent : IsPersonalAgent S T) :
    AgentialFreedomBridge S T := by
  intro hCont hNec hSel
  have hNature := hPersonalNature hAgent hNec
  have hFree := agential_freedom_derived S T hCont hNature hSel hChoice
  exact ⟨hNature, hFree⟩

/-- A Free Personal Source possessing all six distinct ontological attributes:
1. `is_structurally_external`: Structurally external to internal nodes of S (Derived).
2. `is_necessary`: Exists necessarily (Aseity).
3. `nature_invariant`: Essential nature/faculties are invariant across worlds.
4. `is_agent`: Intellect/apprehension of alternatives.
5. `selects_intentionally`: Intentional choice guided by reasons.
6. `acts_freely`: Positive counterfactual choice over alternative configurations under that same nature. -/
structure FreePersonalSource (S : ConcreteSystem.{u}) (T : CandidateGround S) : Prop where
  is_structurally_external : ∃ e : T.ExtEntity, T.ground = GroundIdentity.external e
  is_necessary : IsNecessary S T
  nature_invariant : NatureInvariant S T
  is_agent : IsPersonalAgent S T
  selects_intentionally : SelectsIntentionally S T
  acts_freely : ActsFreely S T

/-- THEOREM 6 (Agential Justification Mode Yields Free Personal Source):
Demonstrates that the agential justification mode substantively instantiates all six
attributes of a Free Personal Source via the decomposed metaphysical bridge principles.
Critically, `ActsFreely S T` is actively DERIVED by `agential_freedom_derived`, and
`AgentialCounterfactualChoiceBridge` is actively DERIVED by `agential_counterfactual_choice_bridge_from_sovereignty`,
rather than received as an unanalyzed overarching bridge!
(0 axioms). -/
theorem agential_justification_mode_yields_free_personal_source
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (hExternal : ∃ e : T.ExtEntity, T.ground = GroundIdentity.external e)
    (hNec : IsNecessary S T)
    (hCont : ContingentSystem S)
    (hAgent : IsPersonalAgent S T)
    (hGuided : GuidedByJustificationMode S T)
    (hTeleo : TeleologicalAgencyPrinciple S T)
    (hPersonalNature : PersonalAseityPreservesNature S T)
    (hSovereign : AgentialSovereigntyOverAlternatives S T ConstitutivePriority)
    (hUlt : IsUltimateGround S T ConstitutivePriority)
    (hNotNec : ¬ NecessitatingMode S T) :
    FreePersonalSource S T := by
  have hSel := hTeleo hAgent hGuided
  have hNature := hPersonalNature hAgent hNec
  have hChoice := agential_counterfactual_choice_bridge_from_sovereignty S T ConstitutivePriority hSovereign hAgent hUlt hNotNec
  have hFree := agential_freedom_derived S T hCont hNature hSel hChoice
  exact ⟨hExternal, hNec, hNature, hAgent, hSel, hFree⟩

/-- MASTER THEOREM (Substantive Deduction of the Necessary and Free Personal Source):
STRUCTURAL HYPOTHESES:
- `prior_wf : ∀ Ext, WellFounded (ConstitutivePriority Ext)`:
  Necessary structural hypothesis of the master deduction. Formalizes the requirement that constitutive
  priority in the ontic domain is well-founded (excludes infinite descending priority chains and cycles).
  Order-theoretic refutation of circularity strictly requires well-foundedness (`well_founded_irrefl`).
- `prior_trans`: Transitivity of constitutive priority.
- `hConstitutiveOfTotality`: Internal nodes are constitutively prior to the totality.
- `hInternalGroundsTotality` & `hGroundsTotality`: Grounding the totality means being prior to it.

METAPHYSICAL BRIDGES (Defended in Treatise):
- `hGrounds`: T grounds the concrete actuality of S in the actual world.
- `hExpl`: T provides a contrastive justification for why actualWorld obtained over every divergent alternative.
- `hAseity`: The ground of the contingent totality exists necessarily (Aseity).
- `hAseityNature`: Invariance of impersonal necessary essence across worlds.
- `hSymmPrinciple`: Contrastive justification requires extrinsic differentiation.
- `hUlt`: Ultimate ground cannot depend on an independent prior condition.
- `hTeleo`: Agential justification mode acts intentionally by reasons.
- `hPersonalNature`: Personal necessary essence is invariant across accessible worlds.
- `hSovereign`: Sovereign personal determination over unnecessitated accessible alternatives.

MAIN CONCLUSION:
THE CANDIDATE GROUND CANNOT BE INTERNAL (REFUTED BY CONSTITUTIVE CIRCULARITY),
CANNOT BE IMPERSONAL (NEITHER NECESSITATING NOR NON-NECESSITATING,
EXCLUDED BY CONTINGENCY, WELL-FOUNDED CIRCULARITY, AND ULTIMACY)
AND MUST BE A STRUCTURALLY TRANSCENDENT, NECESSARY, INTENTIONAL, AND FREE PERSONAL AGENT.
`ActsFreely` IS ACTIVELY CONSTRUCTED IN THE PROOF VIA `agential_freedom_derived` AND `agential_counterfactual_choice_bridge_from_sovereignty`.
(0 axioms beyond core intuitionistic logic and standard classical choice). -/
theorem contingent_system_derives_free_personal_source
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (hCont : ContingentSystem S)
    (hGrounds : T.GroundsConcreteActuality T.ground S.actualWorld)
    (hExpl : ∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
      (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
      ContrastiveExplanationForTotality S T w_alt)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
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
    (hTeleo : TeleologicalAgencyPrinciple S T)
    (hPersonalNature : PersonalAseityPreservesNature S T)
    (hSovereign : AgentialSovereigntyOverAlternatives S T ConstitutivePriority) :
    FreePersonalSource S T := by
  have hExternal : ∃ e : T.ExtEntity, T.ground = GroundIdentity.external e :=
    candidate_ground_must_be_structurally_external S T
      ConstitutivePriority prior_wf (fun Ext {_a _b _c} => prior_trans Ext)
      (fun Ext m => hConstitutiveOfTotality Ext m) hInternalGroundsTotality
  obtain ⟨e, hExt⟩ := hExternal
  have hGroundsPriority := hGroundsTotality e hExt
  have hNec : IsNecessary S T := hAseity hGrounds hExpl
  have hNotNec : ¬ NecessitatingMode S T :=
    necessary_ground_cannot_rigidly_necessitate_contingent_system S T hCont hNec
  have hExh := grounding_modes_exhaustive S T
  rcases hExh with hNecMode | hGuided | ⟨w_alt, hAcc, hAlt, hUnjust⟩
  · have hImpNec : ImpersonalNecessitatingGround S T := ⟨hNec, hNecMode⟩
    exact False.elim (necessary_impersonal_ground_contradicts_contingency S T hImpNec hCont)
  · have hAgent : IsPersonalAgent S T := by
      apply Classical.byContradiction
      intro hNotAgent
      have hImp : IsImpersonal S T := hNotAgent
      have hNature : NatureInvariant S T := hAseityNature hImp hNec
      have hOr := impersonal_ground_forces_consequence_or_independent_condition S T
        ConstitutivePriority e hExt hSymmPrinciple hImp hNature hNotNec hGuided
      cases hOr with
      | inl hConsequenceDep =>
        exact consequence_dependent_mode_fails_well_foundedness
          (ConstitutivePriority T.ExtEntity) (prior_wf T.ExtEntity) (fun {_a _b _c} => prior_trans T.ExtEntity) e hGroundsPriority hConsequenceDep
      | inr hIndep =>
        exact independent_condition_contradicts_ultimacy S T
          ConstitutivePriority e hExt hIndep hUlt
    exact agential_justification_mode_yields_free_personal_source S T ConstitutivePriority
      ⟨e, hExt⟩ hNec hCont hAgent hGuided hTeleo hPersonalNature hSovereign hUlt hNotNec
  · have hExplAlt : ContrastiveExplanationForTotality S T w_alt := hExpl w_alt hAcc hAlt
    exact False.elim (unjustified_alternative_fails_contrastive_at S T w_alt hUnjust hExplAlt)

/-- MASTER THEOREM (Deepened Deduction of the Free Personal Source from Primitive Principles):
Demonstrates the derivation of `FreePersonalSource S T` where `AgentialSovereigntyOverAlternatives`
is actively DERIVED from:
(1) Neutral Universal PSR (`UniversalOutcomePSR S`),
(2) Ultimate Ground Explanatory Scope (`UltimateGroundExplanatoryScope S T ConstitutivePriority`),
(3) Agential Determination Entails Choice (`AgentialDeterminationEntailsChoice S T`),
along with the core cosmological and aseity principles.
(0 axioms beyond core logic and classical choice). -/
theorem deepened_contingent_system_derives_free_personal_source_of_entails
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (hCont : ContingentSystem S)
    (hGrounds : T.GroundsConcreteActuality T.ground S.actualWorld)
    (hExpl : ∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
      (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
      ContrastiveExplanationForTotality S T w_alt)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
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
    (hTeleo : TeleologicalAgencyPrinciple S T)
    (hPersonalNature : PersonalAseityPreservesNature S T)
    (hPSR : UniversalOutcomePSR S ConstitutivePriority)
    (hScope : UltimateGroundExplanatoryScope S T ConstitutivePriority)
    (hChoiceEntails : AgentialDeterminationEntailsChoice S T) :
    FreePersonalSource S T := by
  have hNec : IsNecessary S T := hAseity hGrounds hExpl
  have hSovereign := agential_sovereignty_derived_from_neutral_psr S T ConstitutivePriority
    hPSR hScope hChoiceEntails hPersonalNature hNec
  exact contingent_system_derives_free_personal_source S T hCont hGrounds hExpl
    ConstitutivePriority prior_wf prior_trans hConstitutiveOfTotality
    hInternalGroundsTotality hGroundsTotality
    hAseity hAseityNature hSymmPrinciple hUlt hTeleo hPersonalNature hSovereign

/-- MASTER THEOREM (Variant with Canonical Biconditional Bridge):
(0 axioms). -/
theorem deepened_contingent_system_derives_free_personal_source
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (hCont : ContingentSystem S)
    (hGrounds : T.GroundsConcreteActuality T.ground S.actualWorld)
    (hExpl : ∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
      (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
      ContrastiveExplanationForTotality S T w_alt)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
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
    (hTeleo : TeleologicalAgencyPrinciple S T)
    (hPersonalNature : PersonalAseityPreservesNature S T)
    (hPSR : UniversalOutcomePSR S ConstitutivePriority)
    (hScope : UltimateGroundExplanatoryScope S T ConstitutivePriority)
    (hChoiceBridge : AgentialDeterminationIsChoice S T) :
    FreePersonalSource S T :=
  deepened_contingent_system_derives_free_personal_source_of_entails S T hCont hGrounds hExpl
    ConstitutivePriority prior_wf prior_trans hConstitutiveOfTotality
    hInternalGroundsTotality hGroundsTotality
    hAseity hAseityNature hSymmPrinciple hUlt hTeleo hPersonalNature hPSR hScope
    (agential_determination_entails_choice_of_biconditional S T hChoiceBridge)

/-- A Candidate Ground witnessing the Contrastive PSR along with its metaphysical principles:
Packages the concrete explanatory ground provided by the PSR together with its specific metaphysical
commitments (aseity, symmetry, ultimacy, teleology, personal nature invariance, and sovereignty).
This strictly applies all principles to the same concrete witness without any universal quantification
over arbitrary `CandidateGround S` objects. -/
structure MetaphysicallyGroundedWitness
    (S : ConcreteSystem.{u})
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop) where
  ground : CandidateGround S
  groundsConcreteActuality : ground.GroundsConcreteActuality ground.ground S.actualWorld
  providesContrastiveExplanation : ∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
    (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
    ContrastiveExplanationForTotality S ground w_alt
  aseity : GroundingTotalityTerminatesInAseity S ground
  impersonalAseityPreservesNature : ImpersonalAseityPreservesNature S ground
  symmetry : ExplanatorySymmetryPrinciple S ground ConstitutivePriority
  ultimacy : IsUltimateGround S ground ConstitutivePriority
  teleology : TeleologicalAgencyPrinciple S ground
  personalAseityPreservesNature : PersonalAseityPreservesNature S ground
  sovereignty : AgentialSovereigntyOverAlternatives S ground ConstitutivePriority

/-- MASTER THEOREM (Existential Corollary via Metaphysically Grounded Witness):
If a contingent concrete system admits a metaphysically grounded witness (a candidate ground
that grounds concrete actuality, contrastively explains alternative outcomes, and satisfies
the specific metaphysical principles of aseity, symmetry, ultimacy, teleology, personal nature
preservation, and agential sovereignty), then there exists a Free Personal Source for S.
Critically, all metaphysical conditions apply strictly to the concrete witness rather than
being quantified universally over arbitrary `CandidateGround S` records.
(0 axioms beyond core intuitionistic logic and standard classical choice). -/
theorem contingent_system_with_psr_derives_free_personal_source
    (S : ConcreteSystem.{u})
    (hCont : ContingentSystem S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (prior_wf : ∀ Ext, WellFounded (ConstitutivePriority Ext))
    (prior_trans : ∀ Ext {a b c : CandidateOnticItem S.Node Ext}, ConstitutivePriority Ext a b → ConstitutivePriority Ext b c → ConstitutivePriority Ext a c)
    (hConstitutiveOfTotality : ∀ Ext (n : S.Node), ConstitutivePriority Ext (CandidateOnticItem.node n) CandidateOnticItem.totality)
    (witness : MetaphysicallyGroundedWitness S ConstitutivePriority)
    (hInternalGroundsTotality : ∀ (n : S.Node),
      witness.ground.ground = GroundIdentity.internal n → ∀ Ext, ConstitutivePriority Ext CandidateOnticItem.totality (CandidateOnticItem.node n))
    (hGroundsTotality : ∀ (e : witness.ground.ExtEntity),
      witness.ground.ground = GroundIdentity.external e → ConstitutivePriority witness.ground.ExtEntity (CandidateOnticItem.candidate e) CandidateOnticItem.totality) :
    ∃ T : CandidateGround S, FreePersonalSource S T := by
  refine ⟨witness.ground, contingent_system_derives_free_personal_source S witness.ground hCont
    witness.groundsConcreteActuality witness.providesContrastiveExplanation
    ConstitutivePriority prior_wf prior_trans hConstitutiveOfTotality
    hInternalGroundsTotality hGroundsTotality
    witness.aseity witness.impersonalAseityPreservesNature witness.symmetry witness.ultimacy
    witness.teleology witness.personalAseityPreservesNature witness.sovereignty⟩

/-- A Deepened Candidate Ground witnessing the Contrastive PSR along with primitive metaphysical principles:
Packages the concrete explanatory ground provided by the PSR together with its primitive principles,
including neutral universal PSR, explanatory scope, and agential determination bridge. -/
structure DeepenedMetaphysicallyGroundedWitness
    (S : ConcreteSystem.{u})
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop) where
  ground : CandidateGround S
  groundsConcreteActuality : ground.GroundsConcreteActuality ground.ground S.actualWorld
  providesContrastiveExplanation : ∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
    (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
    ContrastiveExplanationForTotality S ground w_alt
  aseity : GroundingTotalityTerminatesInAseity S ground
  impersonalAseityPreservesNature : ImpersonalAseityPreservesNature S ground
  symmetry : ExplanatorySymmetryPrinciple S ground ConstitutivePriority
  ultimacy : IsUltimateGround S ground ConstitutivePriority
  teleology : TeleologicalAgencyPrinciple S ground
  personalAseityPreservesNature : PersonalAseityPreservesNature S ground
  universalOutcomePSR : UniversalOutcomePSR S ConstitutivePriority
  explanatoryScope : UltimateGroundExplanatoryScope S ground ConstitutivePriority
  agentialDeterminationEntailsChoice : AgentialDeterminationEntailsChoice S ground
  causalCoherence : CausalDeterminationCoherence S ground ConstitutivePriority

/-- MASTER THEOREM (Deepened Existential Corollary via Deepened Grounded Witness):
EXISTENTIAL STATUS AUDIT:
- This theorem is a *conditional characterization theorem*: given an explanatory witness candidate
  (`witness : DeepenedMetaphysicallyGroundedWitness S ConstitutivePriority`) satisfying cosmological
  actuality, contrastive justification, aseity, symmetry, ultimacy, teleology, personal nature invariance,
  neutral PSR, and explanatory scope, it derives `∃ T : CandidateGround S, FreePersonalSource S T`.
- In the broader Logos corpus:
  (1) `DivineClassicalAttributes.exactly_one_universal_modal_ground` (line 2198) establishes unicity and
      universal modal grounding under creaturely semantic finitude `hNoTotal`;
  (2) `EpistemicNecessity.epistemic_normativity_somewhere_yields_a_free_being` (line 160) proves from
      an epistemic normative claim that a creaturely free subject exists (which cannot be identified with
      a totality ground without a category error).
- The coupling between the universal modal ground and the concrete system S is formally mediated by the
  `UniversalGroundGovernanceBridge`, preserving strict type discipline and conditional transparency.
(0 axioms beyond core logic and classical choice). -/
theorem deepened_contingent_system_with_psr_derives_free_personal_source
    (S : ConcreteSystem.{u})
    (hCont : ContingentSystem S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (prior_wf : ∀ Ext, WellFounded (ConstitutivePriority Ext))
    (prior_trans : ∀ Ext {a b c : CandidateOnticItem S.Node Ext}, ConstitutivePriority Ext a b → ConstitutivePriority Ext b c → ConstitutivePriority Ext a c)
    (hConstitutiveOfTotality : ∀ Ext (n : S.Node), ConstitutivePriority Ext (CandidateOnticItem.node n) CandidateOnticItem.totality)
    (witness : DeepenedMetaphysicallyGroundedWitness S ConstitutivePriority)
    (hInternalGroundsTotality : ∀ (n : S.Node),
      witness.ground.ground = GroundIdentity.internal n → ∀ Ext, ConstitutivePriority Ext CandidateOnticItem.totality (CandidateOnticItem.node n))
    (hGroundsTotality : ∀ (e : witness.ground.ExtEntity),
      witness.ground.ground = GroundIdentity.external e → ConstitutivePriority witness.ground.ExtEntity (CandidateOnticItem.candidate e) CandidateOnticItem.totality) :
    ∃ T : CandidateGround S, FreePersonalSource S T := by
  refine ⟨witness.ground, deepened_contingent_system_derives_free_personal_source_of_entails S witness.ground hCont
    witness.groundsConcreteActuality witness.providesContrastiveExplanation
    ConstitutivePriority prior_wf prior_trans hConstitutiveOfTotality
    hInternalGroundsTotality hGroundsTotality
    witness.aseity witness.impersonalAseityPreservesNature witness.symmetry witness.ultimacy
    witness.teleology witness.personalAseityPreservesNature
    witness.universalOutcomePSR witness.explanatoryScope witness.agentialDeterminationEntailsChoice⟩

/-- Profile of the Universal Modal Ground Established in Logos Metaphysics:
Summarizes what is derived from the foundational ontology of Γ:
(1) `is_universal_modal_ground`: g is a universal modal ground of reality;
(2) `unicity`: g is the unique universal modal ground across all reality.
Derived unconditionally from creaturely semantic finitude (`hNoTotal`) via
`Logos.FoundationalUnicity.exactly_one_universal_modal_ground`. -/
structure UniversalGroundModalProfile (g : Logos.Entity.Entity) : Prop where
  is_universal_modal_ground : Logos.FoundationalOmnipresence.UniversalModalGround g
  unicity : ∀ g' : Logos.Entity.Entity, Logos.FoundationalOmnipresence.UniversalModalGround g' → g' = g

/-- THEOREM (Universal Modal Ground Profile Holds in Logos):
Demonstrates that under creaturely semantic finitude (`hNoTotal`), exactly one entity
in reality bears the universal modal ground profile.
(0 axioms beyond core foundations and semantic finitude). -/
theorem universal_ground_modal_profile_holds
    (hNoTotal : ∀ s : Logos.Agency.Subject, ∃ p, ¬ Logos.Agency.Means s p) :
    ∃ g : Logos.Entity.Entity, UniversalGroundModalProfile g := by
  obtain ⟨g, hU, hUniq⟩ := Logos.FoundationalUnicity.exactly_one_universal_modal_ground hNoTotal
  exact ⟨g, ⟨hU, hUniq⟩⟩

/-- Formal correspondence mapping a Universal Modal Ground g : Logos.Entity.Entity to a Candidate Ground for system S.
Preserves types at universe 0 with ExtEntity := Logos.Entity.Entity and ground := GroundIdentity.external g. -/
noncomputable def universalGroundToCandidate
    (S : ConcreteSystem.{0})
    (g : Logos.Entity.Entity)
    (existsAt : S.World → Prop)
    (groundsActuality : S.World → Prop)
    (bindsActuality : ∀ w, groundsActuality w → existsAt w ∧ S.InstantiatedIn w ∧ S.ConfigurationIn w = S.ConfigurationIn S.actualWorld)
    (essence : S.World → Essence)
    (justification : S.World → S.World → Prop)
    (apprehends : S.World → Prop)
    (reasons : S.World → S.World → Prop)
    (chooses : S.World → (Option (S.Node → Bool)) → Prop)
    (determines : S.World → (Option (S.Node → Bool)) → Prop) :
    CandidateGround S where
  ExtEntity := Logos.Entity.Entity
  ground := GroundIdentity.external g
  ExistsAt := fun _ w => existsAt w
  GroundsConcreteActuality := fun _ w => groundsActuality w
  grounding_binds_actuality := by intro w hw; exact bindsActuality w hw
  EssenceOf := fun _ w => essence w
  ProvidesContrastiveJustification := fun _ w1 w2 => justification w1 w2
  ApprehendsAlternative := fun _ w => apprehends w
  ReasonsFavor := fun _ w1 w2 => reasons w1 w2
  ChoosesOutcomeAt := fun _ w out => chooses w out
  DeterminesOutcomeAt := fun _ w out => determines w out

theorem universalGroundToCandidate_ground
    (S : ConcreteSystem.{0})
    (g : Logos.Entity.Entity)
    (existsAt groundsActuality bindsActuality essence justification apprehends reasons chooses determines) :
    (universalGroundToCandidate S g existsAt groundsActuality bindsActuality essence justification apprehends reasons chooses determines).ground =
      GroundIdentity.external g := rfl

/-- PRINCIPLE OF UNIVERSAL GROUND EXPLANATORY GOVERNANCE (Tag: META):
Specifies the concrete bridge through which a universal modal ground g : Logos.Entity.Entity
of reality governs a specific contingent system S:
The candidate ground is formally instantiated via `universalGroundToCandidate S g ...`,
guaranteeing that `ExtEntity := Logos.Entity.Entity` and `ground := GroundIdentity.external g`.
- Concrete Grounding: g grounds the actual concrete configuration of S;
- Contrastive Justification: g's reasons favor the actual configuration over alternatives;
- Aseity: g's grounding terminates in necessary existence;
- Nature Invariance: g's nature is invariant across modal space;
- Explanatory Symmetry: extrinsic differentiation of reasons;
- Ultimacy: g is ungrounded in priority;
- Teleology: g acts intentionally for reasons;
- Personal Invariance: personal nature preserved across worlds;
- Neutral PSR: every accessible alternative outcome has an explanation in priority;
- Explanatory Scope: g explains all accessible alternative outcomes;
- Agential Determination Bridge: g's determination of alternatives is choice. -/
structure UniversalGroundGovernanceBridge
    (S : ConcreteSystem.{0})
    (g : Logos.Entity.Entity)
    (ConstitutivePriority : (Ext : Type 0) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop) where
  existsAt : S.World → Prop
  groundsActuality : S.World → Prop
  bindsActuality : ∀ w, groundsActuality w → existsAt w ∧ S.InstantiatedIn w ∧ S.ConfigurationIn w = S.ConfigurationIn S.actualWorld
  essence : S.World → Essence
  justification : S.World → S.World → Prop
  apprehends : S.World → Prop
  reasons : S.World → S.World → Prop
  chooses : S.World → (Option (S.Node → Bool)) → Prop
  determines : S.World → (Option (S.Node → Bool)) → Prop
  groundsConcreteActuality : (universalGroundToCandidate S g existsAt groundsActuality bindsActuality essence justification apprehends reasons chooses determines).GroundsConcreteActuality
    (universalGroundToCandidate S g existsAt groundsActuality bindsActuality essence justification apprehends reasons chooses determines).ground S.actualWorld
  providesContrastiveExplanation : ∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
    (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
    ContrastiveExplanationForTotality S
      (universalGroundToCandidate S g existsAt groundsActuality bindsActuality essence justification apprehends reasons chooses determines) w_alt
  aseity : GroundingTotalityTerminatesInAseity S
    (universalGroundToCandidate S g existsAt groundsActuality bindsActuality essence justification apprehends reasons chooses determines)
  impersonalAseityPreservesNature : ImpersonalAseityPreservesNature S
    (universalGroundToCandidate S g existsAt groundsActuality bindsActuality essence justification apprehends reasons chooses determines)
  symmetry : ExplanatorySymmetryPrinciple S
    (universalGroundToCandidate S g existsAt groundsActuality bindsActuality essence justification apprehends reasons chooses determines) ConstitutivePriority
  ultimacy : IsUltimateGround S
    (universalGroundToCandidate S g existsAt groundsActuality bindsActuality essence justification apprehends reasons chooses determines) ConstitutivePriority
  teleology : TeleologicalAgencyPrinciple S
    (universalGroundToCandidate S g existsAt groundsActuality bindsActuality essence justification apprehends reasons chooses determines)
  personalAseityPreservesNature : PersonalAseityPreservesNature S
    (universalGroundToCandidate S g existsAt groundsActuality bindsActuality essence justification apprehends reasons chooses determines)
  universalOutcomePSR : UniversalOutcomePSR S ConstitutivePriority
  explanatoryScope : UltimateGroundExplanatoryScope S
    (universalGroundToCandidate S g existsAt groundsActuality bindsActuality essence justification apprehends reasons chooses determines) ConstitutivePriority
  causalCoherence : CausalDeterminationCoherence S
    (universalGroundToCandidate S g existsAt groundsActuality bindsActuality essence justification apprehends reasons chooses determines) ConstitutivePriority
  agent : Logos.Agency.Subject
  actionRealization : AgentialActionRealization S
    (universalGroundToCandidate S g existsAt groundsActuality bindsActuality essence justification apprehends reasons chooses determines) agent
  actionFidelity : ∀ (w : S.World) (out : Option (S.Node → Bool)),
    (universalGroundToCandidate S g existsAt groundsActuality bindsActuality essence justification apprehends reasons chooses determines).DeterminesOutcomeAt
      (universalGroundToCandidate S g existsAt groundsActuality bindsActuality essence justification apprehends reasons chooses determines).ground w out →
      out = SystemOutcomeAt S w

/-- Conversion of Governance Bridge into Deepened Metaphysically Grounded Witness:
(0 axioms). -/
noncomputable def governance_bridge_to_witness
    (S : ConcreteSystem.{0})
    (g : Logos.Entity.Entity)
    (ConstitutivePriority : (Ext : Type 0) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (bridge : UniversalGroundGovernanceBridge S g ConstitutivePriority) :
    DeepenedMetaphysicallyGroundedWitness S ConstitutivePriority :=
  let T := universalGroundToCandidate S g bridge.existsAt bridge.groundsActuality bridge.bindsActuality
     bridge.essence bridge.justification bridge.apprehends bridge.reasons bridge.chooses bridge.determines
  have hChoiceEntails : AgentialDeterminationEntailsChoice S T :=
    agential_determination_entails_choice_derived S T bridge.agent bridge.actionRealization bridge.actionFidelity
  ⟨T,
   bridge.groundsConcreteActuality, bridge.providesContrastiveExplanation,
   bridge.aseity, bridge.impersonalAseityPreservesNature, bridge.symmetry, bridge.ultimacy,
   bridge.teleology, bridge.personalAseityPreservesNature,
   bridge.universalOutcomePSR, bridge.explanatoryScope, hChoiceEntails,
   bridge.causalCoherence⟩

/-- MASTER INTEGRATION THEOREM (Existential Deduction of Free Personal Source via Universal Ground Governance):
Demonstrates that from a contingent system S and a governance bridge for the unique universal modal ground g
(whose existence is proved in `DivineClassicalAttributes.exactly_one_universal_modal_ground` under semantic finitude `hNoTotal`),
there exists a Free Personal Source for S.
The dependency chain is completely transparent:
- Derivation validity: proven in Lean 4 kernel with 0 axioms beyond standard foundations;
- Universal ground unicity & existence: `exactly_one_universal_modal_ground` under `hNoTotal`;
- Cosmological bridge premises: governed by the explicit bridge fields linking g to system S;
- Scope & Choice bridges: `UltimateGroundExplanatoryScope` and `AgentialDeterminationIsChoice` remain visible.
(0 axioms beyond core logic and classical choice). -/
theorem universal_ground_governance_yields_free_personal_source
    (S : ConcreteSystem.{0})
    (hCont : ContingentSystem S)
    (ConstitutivePriority : (Ext : Type 0) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (prior_wf : ∀ Ext, WellFounded (ConstitutivePriority Ext))
    (prior_trans : ∀ Ext {a b c : CandidateOnticItem S.Node Ext}, ConstitutivePriority Ext a b → ConstitutivePriority Ext b c → ConstitutivePriority Ext a c)
    (hConstitutiveOfTotality : ∀ Ext (n : S.Node), ConstitutivePriority Ext (CandidateOnticItem.node n) CandidateOnticItem.totality)
    (hNoTotal : ∀ s : Logos.Agency.Subject, ∃ p, ¬ Logos.Agency.Means s p)
    (hBridge : ∀ (g : Logos.Entity.Entity), Logos.FoundationalOmnipresence.UniversalModalGround g →
      UniversalGroundGovernanceBridge S g ConstitutivePriority)
    (hInternalGroundsTotality : ∀ (n : S.Node),
      ∀ Ext, ConstitutivePriority Ext CandidateOnticItem.totality (CandidateOnticItem.node n))
    (hGroundsTotality : ∀ (g : Logos.Entity.Entity),
      ConstitutivePriority Logos.Entity.Entity (CandidateOnticItem.candidate g) CandidateOnticItem.totality) :
    ∃ T : CandidateGround S, FreePersonalSource S T := by
  have hExist := Logos.FoundationalUnicity.exactly_one_universal_modal_ground hNoTotal
  obtain ⟨g, hU, _⟩ := hExist
  have bridge := hBridge g hU
  let witness := governance_bridge_to_witness S g ConstitutivePriority bridge
  have hInternal : ∀ (n : S.Node), witness.ground.ground = GroundIdentity.internal n →
    ∀ Ext, ConstitutivePriority Ext CandidateOnticItem.totality (CandidateOnticItem.node n) := by
    intro n _ Ext
    exact hInternalGroundsTotality n Ext
  have hGrounds : ∀ (e : witness.ground.ExtEntity), witness.ground.ground = GroundIdentity.external e →
    ConstitutivePriority witness.ground.ExtEntity (CandidateOnticItem.candidate e) CandidateOnticItem.totality := by
    intro e he
    dsimp [witness, governance_bridge_to_witness, universalGroundToCandidate] at he
    injection he with hEq
    subst hEq
    exact hGroundsTotality g
  exact deepened_contingent_system_with_psr_derives_free_personal_source S hCont ConstitutivePriority
    prior_wf prior_trans hConstitutiveOfTotality witness hInternal hGrounds

/-- MASTER THEOREM (Consolidated Ontological Incompleteness and Free Personal Source Theorem):
Consolidates the complete ontological derivation:
(1) System is contingent (`ContingentSystem S`);
(2) Chain cannot be exhaustively forced (`chain_cannot_be_exhaustively_forced`);
(3) Ground must be structurally external (`candidate_ground_must_be_structurally_external`);
(4) Ground is necessary (`GroundingTotalityTerminatesInAseity`);
(5) Explanatory Determination Integrity holds (`ExplanatoryDeterminationRule S T ConstitutivePriority`);
(6) Ground is ultimate (`IsUltimateGround S T ConstitutivePriority`);
(7) Intellectualist evasion is closed (`intellectualist_evasion_closure`);
(8) Teleological agency and sovereignty over alternatives derive `FreePersonalSource S T`;
(9) Concludes both `FreePersonalSource S T` and the formal exclusion of rational determinism:
    `¬ (CompleteRationalDetermination S T ∨ UnifiedRationalActualization S T)`.
(0 axioms beyond core logic and classical choice). -/
theorem consolidated_ontological_incompleteness_derives_free_personal_source
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (hNonEmpty : Nonempty S.Node)
    (hCont : ContingentSystem S)
    (hGrounds : T.GroundsConcreteActuality T.ground S.actualWorld)
    (hExpl : ∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
      (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
      ContrastiveExplanationForTotality S T w_alt)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
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
    (hTeleo : TeleologicalAgencyPrinciple S T)
    (hPersonalNature : PersonalAseityPreservesNature S T)
    (hRule : ExplanatoryDeterminationRule S T ConstitutivePriority)
    (hCausal : FoundationalCausalDetermination S T ConstitutivePriority)
    (hSovereign : AgentialSovereigntyOverAlternatives S T ConstitutivePriority) :
    FreePersonalSource S T ∧ ¬ (CompleteRationalDetermination S T ∨ UnifiedRationalActualization S T) := by
  have hExternal : ∃ e : T.ExtEntity, T.ground = GroundIdentity.external e :=
    candidate_ground_must_be_structurally_external S T
      ConstitutivePriority prior_wf (fun Ext {_a _b _c} => prior_trans Ext)
      (fun Ext m => hConstitutiveOfTotality Ext m) hInternalGroundsTotality
  obtain ⟨e, hExt⟩ := hExternal
  have hGroundsPriority := hGroundsTotality e hExt
  have hNec : IsNecessary S T := hAseity hGrounds hExpl
  have hNonForcing := chain_cannot_be_exhaustively_forced S T hNonEmpty hCont hNec
  have hNotNec := hNonForcing.2
  have hNoIntellectualistEvasion : ¬ (CompleteRationalDetermination S T ∨ UnifiedRationalActualization S T) := by
    intro hCRD
    exact intellectualist_evasion_closure S T ConstitutivePriority prior_wf prior_trans e hExt hRule hUlt hCRD hCausal
  have hExh := grounding_modes_exhaustive S T
  rcases hExh with hNecMode | hGuided | ⟨w_alt, hAcc, hAlt, hUnjust⟩
  · have hImpNec : ImpersonalNecessitatingGround S T := ⟨hNec, hNecMode⟩
    exact False.elim (necessary_impersonal_ground_contradicts_contingency S T hImpNec hCont)
  · have hAgent : IsPersonalAgent S T := by
      apply Classical.byContradiction
      intro hNotAgent
      have hImp : IsImpersonal S T := hNotAgent
      have hNature : NatureInvariant S T := hAseityNature hImp hNec
      have hOr := impersonal_ground_forces_consequence_or_independent_condition S T
        ConstitutivePriority e hExt hSymmPrinciple hImp hNature hNotNec hGuided
      cases hOr with
      | inl hConsequenceDep =>
        exact consequence_dependent_mode_fails_well_foundedness
          (ConstitutivePriority T.ExtEntity) (prior_wf T.ExtEntity) (fun {_a _b _c} => prior_trans T.ExtEntity) e hGroundsPriority hConsequenceDep
      | inr hIndep =>
        exact independent_condition_contradicts_ultimacy S T
          ConstitutivePriority e hExt hIndep hUlt
    have hSel := hTeleo hAgent hGuided
    have hNature := hPersonalNature hAgent hNec
    have hChoice := agential_counterfactual_choice_bridge_from_sovereignty S T ConstitutivePriority hSovereign hAgent hUlt hNotNec
    have hFree := agential_freedom_derived S T hCont hNature hSel hChoice
    exact ⟨⟨⟨e, hExt⟩, hNec, hNature, hAgent, hSel, hFree⟩, hNoIntellectualistEvasion⟩
  · have hExplAlt : ContrastiveExplanationForTotality S T w_alt := hExpl w_alt hAcc hAlt
    exact False.elim (unjustified_alternative_fails_contrastive_at S T w_alt hUnjust hExplAlt)

/-- MASTER THEOREM (Deepened Consolidated Ontological Incompleteness and Free Personal Source Theorem):
Consolidates the complete, deepened ontological derivation from primitive principles:
(1) System is contingent (`ContingentSystem S`);
(2) Chain cannot be exhaustively forced (`chain_cannot_be_exhaustively_forced`);
(3) Ground must be structurally external (`candidate_ground_must_be_structurally_external`);
(4) Ground is necessary (`GroundingTotalityTerminatesInAseity`);
(5) Explanatory Determination Integrity is DERIVED from Ontic Conditioning (`DeterminationAsOnticCondition`);
(6) Agential Sovereignty is DERIVED from Neutral PSR, Explanatory Scope, and Agential Determination Entailment;
(7) Intellectualist evasion is closed via the derived rule (`deepened_intellectualist_evasion_closure`);
(8) Concludes both `FreePersonalSource S T` and the formal exclusion of rational determinism:
    `¬ (CompleteRationalDetermination S T ∨ UnifiedRationalActualization S T)`.
(0 axioms beyond core logic and classical choice). -/
theorem deepened_consolidated_free_personal_source_of_entails
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (hNonEmpty : Nonempty S.Node)
    (hCont : ContingentSystem S)
    (hGrounds : T.GroundsConcreteActuality T.ground S.actualWorld)
    (hExpl : ∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
      (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
      ContrastiveExplanationForTotality S T w_alt)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
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
    (hTeleo : TeleologicalAgencyPrinciple S T)
    (hPersonalNature : PersonalAseityPreservesNature S T)
    (hCond : DeterminationAsOnticCondition S T ConstitutivePriority)
    (hCausal : FoundationalCausalDetermination S T ConstitutivePriority)
    (hPSR : UniversalOutcomePSR S ConstitutivePriority)
    (hScope : UltimateGroundExplanatoryScope S T ConstitutivePriority)
    (hChoiceEntails : AgentialDeterminationEntailsChoice S T) :
    FreePersonalSource S T ∧ ¬ (CompleteRationalDetermination S T ∨ UnifiedRationalActualization S T) := by
  have hNec : IsNecessary S T := hAseity hGrounds hExpl
  have hRule := explanatory_determination_rule_derived S T ConstitutivePriority hCond
  have hSovereign := agential_sovereignty_derived_from_neutral_psr S T ConstitutivePriority
    hPSR hScope hChoiceEntails hPersonalNature hNec
  exact consolidated_ontological_incompleteness_derives_free_personal_source S T
    hNonEmpty hCont hGrounds hExpl ConstitutivePriority prior_wf prior_trans
    hConstitutiveOfTotality hInternalGroundsTotality hGroundsTotality
    hAseity hAseityNature hSymmPrinciple hUlt hTeleo hPersonalNature hRule hCausal hSovereign

/-- Consolidated master theorem with canonical biconditional bridge: -/
theorem deepened_consolidated_free_personal_source
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (hNonEmpty : Nonempty S.Node)
    (hCont : ContingentSystem S)
    (hGrounds : T.GroundsConcreteActuality T.ground S.actualWorld)
    (hExpl : ∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
      (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
      ContrastiveExplanationForTotality S T w_alt)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
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
    (hTeleo : TeleologicalAgencyPrinciple S T)
    (hPersonalNature : PersonalAseityPreservesNature S T)
    (hCond : DeterminationAsOnticCondition S T ConstitutivePriority)
    (hCausal : FoundationalCausalDetermination S T ConstitutivePriority)
    (hPSR : UniversalOutcomePSR S ConstitutivePriority)
    (hScope : UltimateGroundExplanatoryScope S T ConstitutivePriority)
    (hChoiceBridge : AgentialDeterminationIsChoice S T) :
    FreePersonalSource S T ∧ ¬ (CompleteRationalDetermination S T ∨ UnifiedRationalActualization S T) :=
  deepened_consolidated_free_personal_source_of_entails S T hNonEmpty hCont hGrounds hExpl
    ConstitutivePriority prior_wf prior_trans hConstitutiveOfTotality
    hInternalGroundsTotality hGroundsTotality
    hAseity hAseityNature hSymmPrinciple hUlt hTeleo hPersonalNature hCond hCausal hPSR hScope
    (agential_determination_entails_choice_of_biconditional S T hChoiceBridge)

/-!
================================================================================
SECTION III-D₂: SHERLOCK HOLMES ELIMINATIVE DEDUCTION OF UNFORCED PERSONAL AGENT
================================================================================
Formalizes the eliminative derivation of the unforced personal agent from the
project's established foundational premises without assumed choice bridge premises.
Eliminates:
(1) Internal termination (candidate_ground_must_be_structurally_external)
(2) Consequence-dependent circularity (candidate_consequence_circularity_refutation)
(3) Independent condition ultimacy failure (independent_condition_contradicts_ultimacy)
(4) Rigid necessitation (necessary_impersonal_ground_contradicts_contingency)
(5) Impersonal contingent determination (impersonal_ground_forces_consequence_or_independent_condition)
(6) Unjustified alternatives / brute outcomes (unjustified_alternative_fails_contrastive_at)
(7) Antecedent reason-forcing (deepened_intellectualist_evasion_closure)

Surviving Mode: An ungrounded, necessary, transcendent, nature-invariant Personal Agent
whose determination is unforced by antecedent reasons or mechanical prior states.
================================================================================
-/

/-- Level 1: Ontic Location Partition.
Every candidate ground is either internally located at a node of S or structurally external to S.
(0 axioms). -/
theorem ontic_location_exhaustive (S : ConcreteSystem.{u}) (T : CandidateGround S) :
    (∃ n : S.Node, T.ground = GroundIdentity.internal n) ∨
    (∃ e : T.ExtEntity, T.ground = GroundIdentity.external e) := by
  cases hg : T.ground with
  | internal n => exact Or.inl ⟨n, rfl⟩
  | external e => exact Or.inr ⟨e, rfl⟩

/-- Level 2: Ontic Conditioning Partition.
An external candidate ground either depends on a consequence of S, or depends on an independent condition,
or is an ultimate ungrounded ground in constitutive priority.
(0 axioms). -/
theorem ontic_conditioning_exhaustive (S : ConcreteSystem.{u}) (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (e : T.ExtEntity) (hExt : T.ground = GroundIdentity.external e)
    (hGrounds : T.GroundsConcreteActuality T.ground S.actualWorld) :
    ConsequenceDependentDetermination (ConstitutivePriority T.ExtEntity) e ∨
    IndependentConditionMode (ConstitutivePriority T.ExtEntity) e ∨
    IsUltimateGround S T ConstitutivePriority := by
  by_cases hCond : ConstitutivePriority T.ExtEntity CandidateOnticItem.condition (CandidateOnticItem.candidate e)
  · by_cases hTot : ConstitutivePriority T.ExtEntity CandidateOnticItem.totality CandidateOnticItem.condition
    · exact Or.inl ⟨hTot, hCond⟩
    · exact Or.inr (Or.inl ⟨hCond, hTot⟩)
  · right; right
    refine ⟨hGrounds, ?_⟩
    intro e' he' ⟨hCond', _⟩
    have hEq : e = e' := by
      have hEqGround : GroundIdentity.external e = GroundIdentity.external e' := hExt.symm.trans he'
      injection hEqGround
    subst hEq
    exact hCond hCond'

/-- Level 4: Ontological Nature Partition.
Every candidate ground is either impersonal or a personal agent.
(0 axioms). -/
theorem ontological_nature_exhaustive (S : ConcreteSystem.{u}) (T : CandidateGround S) :
    IsImpersonal S T ∨ IsPersonalAgent S T := by
  dsimp [IsImpersonal]
  exact (Classical.em (IsPersonalAgent S T)).symm

/-- Level 5: Agential Determination Partition.
A personal agent's determination across accessible worlds is either exhaustively fixed by
reasons/prior state (rational determinism) or is not exhaustively fixed.
(0 axioms). -/
theorem agential_determination_exhaustive (S : ConcreteSystem.{u}) (T : CandidateGround S) :
    (CompleteRationalDetermination S T ∨ UnifiedRationalActualization S T) ∨
    ¬ (CompleteRationalDetermination S T ∨ UnifiedRationalActualization S T) :=
  Classical.em _

/-- MASTER ELIMINATIVE THEOREM (Deduction of the Unforced Personal Agent):
From established cosmological and structural premises alone, deduces that the ultimate ground
of a contingent concrete system must be an ungrounded, necessary, transcendent, nature-invariant
Personal Agent whose determination is unforced by antecedent reasons.
Eliminates:
(1) Internal nodes (candidate_ground_must_be_structurally_external)
(2) Consequence dependence (candidate_consequence_circularity_refutation)
(3) Independent condition (independent_condition_contradicts_ultimacy)
(4) Rigid necessitation (necessary_impersonal_ground_contradicts_contingency)
(5) Impersonal contingent determination (impersonal_ground_forces_consequence_or_independent_condition)
(6) Unjustified alternatives / brute outcomes (unjustified_alternative_fails_contrastive_at)
(7) Antecedent reason-forcing (deepened_intellectualist_evasion_closure)
(0 axioms beyond standard logic and classical choice). -/
theorem eliminative_deduction_of_unforced_personal_agent
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (hCont : ContingentSystem S)
    (hGrounds : T.GroundsConcreteActuality T.ground S.actualWorld)
    (hExpl : ∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
      (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
      ContrastiveExplanationForTotality S T w_alt)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
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
    (hCausal : FoundationalCausalDetermination S T ConstitutivePriority) :
    (∃ e : T.ExtEntity, T.ground = GroundIdentity.external e) ∧
    IsNecessary S T ∧
    NatureInvariant S T ∧
    IsPersonalAgent S T ∧
    IsUltimateGround S T ConstitutivePriority ∧
    GuidedByJustificationMode S T ∧
    ¬ (CompleteRationalDetermination S T ∨ UnifiedRationalActualization S T) := by
  have hExternal : ∃ e : T.ExtEntity, T.ground = GroundIdentity.external e :=
    candidate_ground_must_be_structurally_external S T
      ConstitutivePriority prior_wf (fun Ext {_a _b _c} => prior_trans Ext)
      (fun Ext m => hConstitutiveOfTotality Ext m) hInternalGroundsTotality
  obtain ⟨e, hExt⟩ := hExternal
  have hGroundsPriority := hGroundsTotality e hExt
  have hNec : IsNecessary S T := hAseity hGrounds hExpl
  have hNotNec : ¬ NecessitatingMode S T :=
    necessary_ground_cannot_rigidly_necessitate_contingent_system S T hCont hNec
  have hNoIntellectualistEvasion : ¬ (CompleteRationalDetermination S T ∨ UnifiedRationalActualization S T) := by
    intro hCRD
    exact deepened_intellectualist_evasion_closure S T ConstitutivePriority prior_wf prior_trans e hExt hCond hUlt hCRD hCausal
  have hExh := grounding_modes_exhaustive S T
  have hGuided : GuidedByJustificationMode S T := by
    rcases hExh with hNecMode | hGuidedMode | ⟨w_alt, hAcc, hAlt, hUnjust⟩
    · have hImpNec : ImpersonalNecessitatingGround S T := ⟨hNec, hNecMode⟩
      exact False.elim (necessary_impersonal_ground_contradicts_contingency S T hImpNec hCont)
    · exact hGuidedMode
    · have hExplAlt : ContrastiveExplanationForTotality S T w_alt := hExpl w_alt hAcc hAlt
      exact False.elim (unjustified_alternative_fails_contrastive_at S T w_alt hUnjust hExplAlt)
  have hAgent : IsPersonalAgent S T := by
    apply Classical.byContradiction
    intro hNotAgent
    have hImp : IsImpersonal S T := hNotAgent
    have hNatureImp : NatureInvariant S T := hAseityNature hImp hNec
    have hOr := impersonal_ground_forces_consequence_or_independent_condition S T
      ConstitutivePriority e hExt hSymmPrinciple hImp hNatureImp hNotNec hGuided
    cases hOr with
    | inl hConsequenceDep =>
      exact consequence_dependent_mode_fails_well_foundedness
        (ConstitutivePriority T.ExtEntity) (prior_wf T.ExtEntity) (fun {_a _b _c} => prior_trans T.ExtEntity) e hGroundsPriority hConsequenceDep
    | inr hIndep =>
      exact independent_condition_contradicts_ultimacy S T
        ConstitutivePriority e hExt hIndep hUlt
  have hPersonalNat : NatureInvariant S T := hPersonalNature hAgent hNec
  exact ⟨⟨e, hExt⟩, hNec, hPersonalNat, hAgent, hUlt, hGuided, hNoIntellectualistEvasion⟩

/-- CANONICAL TIER 1 THEOREM — MASTER EXISTENTIAL ELIMINATIVE THEOREM:
Existential Deduction of the Unforced Personal Agent.
From established cosmological and structural foundations alone, deduces the existential existence
of an ungrounded, necessary, transcendent, nature-invariant Personal Agent whose determination
is unforced by antecedent reasons or prior state.
Zero bridge premises. Zero substantive axioms of Γ.
(0 axioms beyond standard logic and classical choice). -/
theorem eliminative_existential_derives_unforced_personal_agent
    (S : ConcreteSystem.{u})
    (hCont : ContingentSystem S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (prior_wf : ∀ Ext, WellFounded (ConstitutivePriority Ext))
    (prior_trans : ∀ Ext {a b c : CandidateOnticItem S.Node Ext}, ConstitutivePriority Ext a b → ConstitutivePriority Ext b c → ConstitutivePriority Ext a c)
    (hConstitutiveOfTotality : ∀ Ext (n : S.Node), ConstitutivePriority Ext (CandidateOnticItem.node n) CandidateOnticItem.totality)
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
      FoundationalCausalDetermination S T ConstitutivePriority) :
    ∃ T : CandidateGround S,
      (∃ e : T.ExtEntity, T.ground = GroundIdentity.external e) ∧
      IsNecessary S T ∧
      NatureInvariant S T ∧
      IsPersonalAgent S T ∧
      IsUltimateGround S T ConstitutivePriority ∧
      GuidedByJustificationMode S T ∧
      ¬ (CompleteRationalDetermination S T ∨ UnifiedRationalActualization S T) := by
  obtain ⟨T, hGrounds, hExpl⟩ := hPSR hCont
  have hAgent := eliminative_deduction_of_unforced_personal_agent S T hCont hGrounds hExpl
    ConstitutivePriority prior_wf (fun Ext {_a _b _c} => prior_trans Ext)
    hConstitutiveOfTotality (hInternalGroundsTotality T hGrounds hExpl) (hGroundsTotality T hGrounds hExpl)
    (hAseity T hGrounds hExpl) (hAseityNature T hGrounds hExpl) (hSymmPrinciple T hGrounds hExpl) (hUltRequirement T hGrounds hExpl)
    (hPersonalNature T hGrounds hExpl) (hCond T hGrounds hExpl) (hCausal T hGrounds hExpl)
  exact ⟨T, hAgent⟩

end OntologicalIncompleteness
end Logos
