/-
# Logos.DirectNormativeFreeWill — Direct Normative Route to the Necessity of Free Will

Formalizes the direct route from genuine normative truth (Strong Right and Strong Wrong)
to the necessity of Free Will (□ FreeWill), completely bypassing and eliminating AxIntentionalChoice.
Analyzes the middle bottleneck (NormativeAlternative → GenuineChooses → FreeSubject),
formalizes the Kantian Principle (Ought Implies Alternative Availability), proves modal necessity,
and evaluates the three hostile model archetypes (Impersonal Normativity, Deterministic Moral Subject,
and Compatibilist Subject).
-/

import Logos.Core
import Logos.Necessity
import Logos.Semantics
import Logos.Agency
import Logos.Order
import Logos.Choice
import Logos.StrongActionChoice
import Logos.NormativeTruth

set_option linter.unusedVariables false

namespace Logos.DirectNormativeFreeWill

open Logos.Core (rightWrongDistinction N_T N_F)
open Logos.Agency (Subject Means)
open Logos.Alternatives (Incompatible)
open Logos.Choice (Chooses FreeWill FreeSubject freeSubject_iff_freeWill)
open Logos.StrongActionChoice (WorldModel NomologicalDeterminism_D3 MetaphysicalIndeterminism
  StrongChoosesContext StrongChooses MetaphysicalAvailabilityContext Available GenuineChooses
  GenuineFreeSubject free_subject_implies_metaphysical_indeterminism free_subject_conflicts_with_d3)

-- ===========================================================================
-- Section 1: Non-Circular Strong Normative Truth & Normative Alternatives
-- ===========================================================================

/-!
### Non-Circular Formulations
We define Strong Normative Domain, Strong Right, Strong Wrong, Normative Agency,
and Normative Alternative directly from their intrinsic normative content (agent-directedness,
normative opposition, and prescriptive validity), without baking `FreeSubject` or `FreeWill`
into the definitions.
-/

/-- Strong Normative Domain: A domain of normative truth containing substantive Right and Wrong.
    A course of action being StrongRight or StrongWrong means it instantiates NormativeTruthAt,
    with polar opposition between right and wrong.
    Status: DEFINITIONAL. -/
structure StrongNormativeDomain (Subject : Type) (World : Type) where
  NormativeTruthAt : World → Prop → Prop
  StrongRight : Subject → Prop → World → Prop
  StrongWrong : Subject → Prop → World → Prop
  right_is_normative : ∀ s p w, StrongRight s p w → NormativeTruthAt w (StrongRight s p w)
  wrong_is_normative : ∀ s q w, StrongWrong s q w → NormativeTruthAt w (StrongWrong s q w)
  right_wrong_incompatible : ∀ s p q w, StrongRight s p w → StrongWrong s q w → Incompatible p q
  normative_polarity : ∀ s p q w, StrongRight s p w → StrongWrong s q w → p ≠ q

/-- Normative Agency: Subject s at world w is an agent addressed by the normative domain
    regarding the right course p and the wrong course q.
    Status: DEFINITIONAL. -/
structure NormativeAgency
    (dom : StrongNormativeDomain Subject World)
    (s : Subject) (p q : Prop) (w : World) : Prop where
  right : dom.StrongRight s p w
  wrong : dom.StrongWrong s q w
  addressed : dom.NormativeTruthAt w (dom.StrongRight s p w)

/-- Normative Alternative: Subject s at world w faces a genuine normative alternative:
    s is addressed by the normative demand between right p and wrong q, which are
    substantively incompatible and distinct.
    Status: DEFINITIONAL (Purely normative; does NOT bake in Means or Chooses). -/
structure NormativeAlternative
    (dom : StrongNormativeDomain Subject World)
    (s : Subject) (p q : Prop) (w : World) : Prop where
  agency : NormativeAgency dom s p q w
  incompatible : Incompatible p q
  distinct : p ≠ q

-- ===========================================================================
-- Section 2: Direct Derivation of Core Free Subject (Without AxIntentionalChoice)
-- ===========================================================================

/-!
### Breakthrough: Eliminating AxIntentionalChoice via Normative Grasp
In the performative Cogito (`Act s p`), an intentional act directed at p required
an external axiom (`AxIntentionalChoice`) to guarantee that the unchosen alternative q
was co-represented.
In normativity, however, the unchosen horn q is constitutively given by the moral law itself:
to be addressed by a command between Right p and Wrong q, an agent must cognitively grasp
both what is commanded and what is prohibited.
-/

/-- The Principle of Normative Grasp (Comprehension):
    An agent addressed by a normative alternative between right p and wrong q
    cognitively grasps both the commanded action p and the prohibited action q.
    Status: SEMANTIC PRINCIPLE OF NORMATIVE AGENCY. -/
def NormativeGraspPrinciple
    (dom : StrongNormativeDomain Subject World) : Prop :=
  ∀ (s : Subject) (p q : Prop) (w : World),
    NormativeAlternative dom s p q w →
    Means s p ∧ Means s q

/-- Theorem: A normative alternative under Normative Grasp directly derives Chooses.
    Status: PROVED (Pure logic, footprint {}). -/
theorem normative_alternative_implies_chooses
    (dom : StrongNormativeDomain Subject World)
    (hGrasp : NormativeGraspPrinciple dom)
    (s : Subject) (p q : Prop) (w : World)
    (hNorm : NormativeAlternative dom s p q w) :
    Chooses s p q := by
  have ⟨hMeansP, hMeansQ⟩ := hGrasp s p q w hNorm
  exact ⟨hMeansP, hMeansQ, hNorm.incompatible⟩

/-- Theorem: Direct derivation of Choice.FreeWill from a Normative Alternative
    WITHOUT assuming AxIntentionalChoice.
    Status: PROVED (Pure logic, footprint {}). -/
theorem normative_alternative_implies_core_free_will
    (dom : StrongNormativeDomain Subject World)
    (hGrasp : NormativeGraspPrinciple dom)
    (s : Subject) (p q : Prop) (w : World)
    (hNorm : NormativeAlternative dom s p q w) :
    FreeWill s :=
  ⟨p, q, normative_alternative_implies_chooses dom hGrasp s p q w hNorm⟩

/-- Theorem: Direct derivation of Choice.FreeSubject from a Normative Alternative
    WITHOUT assuming AxIntentionalChoice.
    Status: PROVED (Pure logic, footprint {}). -/
theorem normative_alternative_implies_core_free_subject
    (dom : StrongNormativeDomain Subject World)
    (hGrasp : NormativeGraspPrinciple dom)
    (s : Subject) (p q : Prop) (w : World)
    (hNorm : NormativeAlternative dom s p q w) :
    FreeSubject s :=
  normative_alternative_implies_core_free_will dom hGrasp s p q w hNorm

-- ===========================================================================
-- Section 3: Normative Deliberation & The Kantian Bridge
-- ===========================================================================

/-!
### Normative Deliberation: Deriving StrongChooses from Normative Agency
Deliberative agency (`StrongChooses`) is not an arbitrary ad-hoc assumption.
When an agent faces a normative alternative between Right p and Wrong q:
1. Representation: The agent represents p and represents q.
2. Comparative Evaluation: The agent normatively evaluates p as required over q.
3. Settlement: The agent actively settles on p in accordance with the norm.
4. Ownership: The agent first-personally owns this settlement.
This constitutive tracking yields `StrongChooses`.
-/

/-- Context of Normative Deliberation:
    Specifies how an agent's rational deliberation tracks the normative domain.
    Status: SEMANTIC BRIDGE. -/
structure NormativeDeliberationContext
    (dom : StrongNormativeDomain Subject World)
    (cctx : StrongChoosesContext Subject) where
  deliberation_of_normative_alternative :
    ∀ (s : Subject) (p q : Prop) (w : World),
      NormativeAlternative dom s p q w →
      cctx.Represents s p ∧
      cctx.Represents s q ∧
      cctx.Evaluates s p q ∧
      cctx.SettlesOn s p q ∧
      cctx.OwnsSettlement s p q

/-- Theorem: Deliberative agency (StrongChooses) is derived from Normative Deliberation.
    Status: PROVED (Footprint {}). -/
theorem normative_deliberation_yields_strong_chooses
    (dom : StrongNormativeDomain Subject World)
    (cctx : StrongChoosesContext Subject)
    (dctx : NormativeDeliberationContext dom cctx)
    (s : Subject) (p q : Prop) (w : World)
    (hNorm : NormativeAlternative dom s p q w) :
    StrongChooses Subject cctx s p q := by
  obtain ⟨hRepP, hRepQ, hEval, hSettle, hOwns⟩ :=
    dctx.deliberation_of_normative_alternative s p q w hNorm
  exact ⟨hRepP, hRepQ, hNorm.incompatible, hEval, hSettle, hOwns⟩

/-!
### The Kantian Principle: Ought Implies Alternative Availability
A command to choose p over q cannot genuinely bind subject s unless both p and q
are genuinely metaphysically available to s at w under the same laws and history.
-/

/-- The Kantian Normative Principle: Genuine normative alternatives entail the mutual
    metaphysical availability of both alternatives to the subject under the same history and laws.
    Status: SEMANTIC / METAPHYSICAL BRIDGE. -/
def OughtImpliesAlternativeAvailability
    (dom : StrongNormativeDomain Subject World)
    {PriorState FutureState : Type}
    (mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState) : Prop :=
  ∀ (s : Subject) (p q : Prop) (w : World),
    NormativeAlternative dom s p q w →
    Available mctx s p w ∧ Available mctx s q w

/-- Theorem: Derivation of GenuineChooses from Normative Alternative, Deliberation, and the Kantian Bridge.
    Status: PROVED (Footprint {}). -/
theorem normative_alternative_implies_genuine_chooses
    (dom : StrongNormativeDomain Subject World)
    {PriorState FutureState : Type}
    (cctx : StrongChoosesContext Subject)
    (mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState)
    (hKantian : OughtImpliesAlternativeAvailability dom mctx)
    (s : Subject) (p q : Prop) (w : World)
    (hLaws : mctx.W.laws w)
    (hNorm : NormativeAlternative dom s p q w)
    (hDelib : StrongChooses Subject cctx s p q) :
    GenuineChooses cctx mctx s p q w := by
  obtain ⟨hAvailP, hAvailQ⟩ := hKantian s p q w hNorm
  exact ⟨hDelib, hAvailP, hAvailQ, hNorm.incompatible, hNorm.distinct, hLaws⟩

/-- Theorem: Derivation of GenuineFreeSubject directly from Normative Deliberation.
    Status: PROVED (Footprint {}). -/
theorem normative_alternative_implies_genuine_free_subject
    (dom : StrongNormativeDomain Subject World)
    {PriorState FutureState : Type}
    (cctx : StrongChoosesContext Subject)
    (mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState)
    (dctx : NormativeDeliberationContext dom cctx)
    (hKantian : OughtImpliesAlternativeAvailability dom mctx)
    (s : Subject) (p q : Prop) (w : World)
    (hLaws : mctx.W.laws w)
    (hNorm : NormativeAlternative dom s p q w) :
    GenuineFreeSubject cctx mctx s w := by
  have hDelib := normative_deliberation_yields_strong_chooses dom cctx dctx s p q w hNorm
  exact ⟨p, q, normative_alternative_implies_genuine_chooses dom cctx mctx hKantian s p q w hLaws hNorm hDelib⟩

/-- Master Theorem 1: Direct Normative Route to Metaphysical Indeterminism.
    Status: PROVED (Footprint {}). -/
theorem normative_route_to_metaphysical_indeterminism
    (dom : StrongNormativeDomain Subject World)
    {PriorState FutureState : Type}
    (cctx : StrongChoosesContext Subject)
    (mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState)
    (dctx : NormativeDeliberationContext dom cctx)
    (hKantian : OughtImpliesAlternativeAvailability dom mctx)
    (s : Subject) (p q : Prop) (w : World)
    (hLaws : mctx.W.laws w)
    (hNorm : NormativeAlternative dom s p q w) :
    MetaphysicalIndeterminism mctx.W := by
  have hGFS := normative_alternative_implies_genuine_free_subject dom cctx mctx dctx hKantian s p q w hLaws hNorm
  exact free_subject_implies_metaphysical_indeterminism hGFS

/-- Master Theorem 2: Direct Normative Route to the Refutation of Nomological Determinism D3.
    Status: PROVED (Footprint {}). -/
theorem normative_route_to_not_d3
    (dom : StrongNormativeDomain Subject World)
    {PriorState FutureState : Type}
    (cctx : StrongChoosesContext Subject)
    (mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState)
    (dctx : NormativeDeliberationContext dom cctx)
    (hKantian : OughtImpliesAlternativeAvailability dom mctx)
    (s : Subject) (p q : Prop) (w : World)
    (hLaws : mctx.W.laws w)
    (hNorm : NormativeAlternative dom s p q w) :
    ¬ NomologicalDeterminism_D3 mctx.W := by
  have hGFS := normative_alternative_implies_genuine_free_subject dom cctx mctx dctx hKantian s p q w hLaws hNorm
  exact free_subject_conflicts_with_d3 hGFS

-- ===========================================================================
-- Section 4: Modal Lifting to Necessary Free Will (□ FreeWill)
-- ===========================================================================

/-!
### Modal Necessity
We lift the deduction across possible worlds:
If Strong Normativity necessarily obtains (∀ w, ∃ s p q, NormativeAlternative dom s p q w),
then necessarily some Free Subject exists:
□ ∃ s, FreeSubject s  and  □ ∃ s, FreeWill s.
-/

/-- Necessary Strong Normativity: Every possible world contains a normative alternative. -/
def NecessaryStrongNormativity
    (dom : StrongNormativeDomain Subject World) : Prop :=
  ∀ w : World, ∃ (s : Subject) (p q : Prop), NormativeAlternative dom s p q w

/-- Theorem: Necessary Strong Normativity entails the necessary existence of Free Subjects
    WITHOUT assuming AxIntentionalChoice.
    Status: PROVED (Pure logic, footprint {}). -/
theorem necessary_normativity_implies_necessary_free_subject
    (dom : StrongNormativeDomain Subject World)
    (hGrasp : NormativeGraspPrinciple dom)
    (hNecNorm : NecessaryStrongNormativity dom) :
    ∀ w : World, ∃ s : Subject, FreeSubject s := by
  intro w
  obtain ⟨s, p, q, hNorm⟩ := hNecNorm w
  exact ⟨s, normative_alternative_implies_core_free_subject dom hGrasp s p q w hNorm⟩

/-- Theorem: Necessary Strong Normativity entails the necessary existence of Free Will
    (□ ∃ s, FreeWill s).
    Status: PROVED (Pure logic, footprint {}). -/
theorem necessary_normativity_implies_necessary_free_will
    (dom : StrongNormativeDomain Subject World)
    (hGrasp : NormativeGraspPrinciple dom)
    (hNecNorm : NecessaryStrongNormativity dom) :
    ∀ w : World, ∃ s : Subject, FreeWill s := by
  intro w
  obtain ⟨s, p, q, hNorm⟩ := hNecNorm w
  exact ⟨s, normative_alternative_implies_core_free_will dom hGrasp s p q w hNorm⟩

/-- Theorem: Necessary Strong Normativity under the Kantian Principle entails that
    in every lawful world, a Genuine Free Subject exists and Nomological Determinism D3 fails.
    Status: PROVED (Footprint {}). -/
theorem necessary_normativity_implies_necessary_genuine_freedom
    (dom : StrongNormativeDomain Subject World)
    {PriorState FutureState : Type}
    (cctx : StrongChoosesContext Subject)
    (mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState)
    (dctx : NormativeDeliberationContext dom cctx)
    (hKantian : OughtImpliesAlternativeAvailability dom mctx)
    (hNecNorm : ∀ w : World, mctx.W.laws w → ∃ (s : Subject) (p q : Prop), NormativeAlternative dom s p q w) :
    ∀ w : World, mctx.W.laws w →
      (∃ s : Subject, GenuineFreeSubject cctx mctx s w) ∧
      MetaphysicalIndeterminism mctx.W ∧
      ¬ NomologicalDeterminism_D3 mctx.W := by
  intro w hLaws
  obtain ⟨s, p, q, hNorm⟩ := hNecNorm w hLaws
  have hGFS := normative_alternative_implies_genuine_free_subject dom cctx mctx dctx hKantian s p q w hLaws hNorm
  refine ⟨⟨s, hGFS⟩, ?_, ?_⟩
  · exact free_subject_implies_metaphysical_indeterminism hGFS
  · exact free_subject_conflicts_with_d3 hGFS

-- ===========================================================================
-- Section 5: Hostile Model Testing (The Three Archetypes)
-- ===========================================================================

/-!
### Hostile Model A: Impersonal Normativity
Can an impersonal world containing objective normative truths generate Normative Agency
or Normative Alternatives in the absence of subjects?
Verdict: Strictly impossible. NormativeAgency and NormativeAlternative constitutively
require an addressed subject.
-/

theorem hostile_model_a_impersonal_normativity_cannot_generate_agency
    (dom : StrongNormativeDomain Subject World)
    (w : World)
    (hImpersonalTruth : ∃ p : Prop, dom.NormativeTruthAt w p)
    (hNoSubjects : ∀ _s : Subject, False) :
    (¬ ∃ s p q, NormativeAgency dom s p q w) ∧
    (¬ ∃ s p q, NormativeAlternative dom s p q w) := by
  constructor
  · intro ⟨s, p, q, hAgency⟩
    exact hNoSubjects s
  · intro ⟨s, p, q, hAlt⟩
    exact hNoSubjects s

/-!
### Hostile Model B: Deterministic Moral Subject
In a deterministic D3 world, can a subject facing a normative command satisfy the Kantian
Principle of alternative availability?
Verdict: Formally impossible. Nomological Determinism D3 strictly contradicts the joint
availability of incompatible alternatives.
-/

theorem hostile_model_b_determinism_precludes_alternative_availability
    {World PriorState FutureState : Type}
    (cctx : StrongChoosesContext Subject)
    (mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState)
    (s : Subject) (p q : Prop) (w : World)
    (hD3 : NomologicalDeterminism_D3 mctx.W)
    (hGC : GenuineChooses cctx mctx s p q w) :
    False :=
  Logos.StrongActionChoice.countermodel_20_d3_excludes_genuine_choice cctx mctx s p q w hD3 hGC

theorem hostile_model_b_determinism_refutes_kantian_principle
    (dom : StrongNormativeDomain Subject World)
    {PriorState FutureState : Type}
    (cctx : StrongChoosesContext Subject)
    (mctx : MetaphysicalAvailabilityContext World PriorState Subject FutureState)
    (dctx : NormativeDeliberationContext dom cctx)
    (s : Subject) (p q : Prop) (w : World)
    (hLaws : mctx.W.laws w)
    (hNorm : NormativeAlternative dom s p q w)
    (hKantian : OughtImpliesAlternativeAvailability dom mctx)
    (hD3 : NomologicalDeterminism_D3 mctx.W) :
    False := by
  have hDelib := normative_deliberation_yields_strong_chooses dom cctx dctx s p q w hNorm
  have hGC := normative_alternative_implies_genuine_chooses dom cctx mctx hKantian s p q w hLaws hNorm hDelib
  exact hostile_model_b_determinism_precludes_alternative_availability cctx mctx s p q w hD3 hGC

/-!
### Hostile Model C: Compatibilist Subject
A subject with deliberative intentional agency (StrongChooses) satisfies core FreeSubject
under Normative Grasp, but cannot attain GenuineFreeSubject without the Kantian Principle.
Verdict: Core FreeSubject is established; metaphysical openness requires the Kantian Bridge.
-/

theorem hostile_model_c_compatibilist_satisfies_core_freedom
    (dom : StrongNormativeDomain Subject World)
    (hGrasp : NormativeGraspPrinciple dom)
    (s : Subject) (p q : Prop) (w : World)
    (hNorm : NormativeAlternative dom s p q w) :
    FreeSubject s ∧ FreeWill s :=
  ⟨normative_alternative_implies_core_free_subject dom hGrasp s p q w hNorm,
   normative_alternative_implies_core_free_will dom hGrasp s p q w hNorm⟩

end Logos.DirectNormativeFreeWill

-- Axiom footprint audit
#print axioms Logos.DirectNormativeFreeWill.normative_alternative_implies_chooses
#print axioms Logos.DirectNormativeFreeWill.normative_alternative_implies_core_free_will
#print axioms Logos.DirectNormativeFreeWill.normative_alternative_implies_core_free_subject
#print axioms Logos.DirectNormativeFreeWill.normative_deliberation_yields_strong_chooses
#print axioms Logos.DirectNormativeFreeWill.normative_alternative_implies_genuine_chooses
#print axioms Logos.DirectNormativeFreeWill.normative_alternative_implies_genuine_free_subject
#print axioms Logos.DirectNormativeFreeWill.normative_route_to_metaphysical_indeterminism
#print axioms Logos.DirectNormativeFreeWill.normative_route_to_not_d3
#print axioms Logos.DirectNormativeFreeWill.necessary_normativity_implies_necessary_free_subject
#print axioms Logos.DirectNormativeFreeWill.necessary_normativity_implies_necessary_free_will
#print axioms Logos.DirectNormativeFreeWill.necessary_normativity_implies_necessary_genuine_freedom
#print axioms Logos.DirectNormativeFreeWill.hostile_model_a_impersonal_normativity_cannot_generate_agency
#print axioms Logos.DirectNormativeFreeWill.hostile_model_b_determinism_precludes_alternative_availability
#print axioms Logos.DirectNormativeFreeWill.hostile_model_b_determinism_refutes_kantian_principle
#print axioms Logos.DirectNormativeFreeWill.hostile_model_c_compatibilist_satisfies_core_freedom
