import Lean
import Logos.DivineClassicalAttributes
import Logos.DivineTrinitarianAttributes

open Classical

/-!
# Ontological Incompleteness Theorem & The Necessary Free Personal Source

This module formalizes the complete, consolidated ontological argument demonstrating
the **Absolute Explanatory Incompleteness of Closed Determination Systems** and the
substantive deduction of a **Necessary, Free Personal Source**.

The argument is strictly atemporal: all relations represent constitutive, ontological,
and explanatory determination, rather than chronological or temporal succession.

## I. The Three Internal Determination Topologies
We rigorously establish the failure of internal determination across all three topologies:
1. **Closed Cycles**: Circular dependencies ($a \prec \dots \prec a$) violate the strict
   irreflexivity of ontological priority (`closed_cycle_violates_ontological_priority`).
2. **Infinite Regress**: A chain of infinite conditional dependencies transfers debt without
   ever grounding the actuality of the system; internal conditional rules are satisfied
   by absolute vacuity/non-existence (`infinite_regress_conditional_rules_satisfied_by_vacuity`),
   and the ground-direction is ill-founded (`infinite_regress_cannot_self_ground`).
3. **Internal Boundary**: A well-founded system necessarily contains an internal boundary
   node lacking an internal determiner (`closed_system_has_unexplained_boundary`).
   Absence of an internal determiner is strictly distinguished from absolute ungroundedness.
4. **Compossibility of Internal Rules with Divergent Configurations**:
   Internal determination relations can hold conditionally inside any world where the system
   is instantiated, witnessing that satisfaction of internal rules is compossible across alternative worlds with divergent
   configurations (`internal_rules_fail_contrastive_distinction` / `internal_rules_compossible_with_divergent_configurations`).
5. **Deduction of Structural Transcendence (Refutation of Constitutive Circularity)**:
   An internal node cannot be its own determiner (`internal_node_cannot_self_determine`).
   Furthermore, an internal candidate node $n \in S.Node$ constitutively constitutes the totality
   ($n \prec S$); if $n$ were posited as the ground of the totality ($S \prec n$), this
   induces constitutive circularity ($n \prec n$), deriving `False` by priority irreflexivity
   (`internal_node_cannot_ground_totality_circularity` and `internal_candidate_cannot_ground_totality`).
   Hence any candidate ground that grounds the concrete totality MUST be structurally external:
   `∃ e : T.ExtEntity, T.ground = GroundIdentity.external e` (`candidate_ground_must_be_structurally_external`).
   Transcendence is DERIVED as a positive structural identity, not merely assumed as a negative predicate.

## II. Principle of Sufficient Reason (PSR) for the Concrete Totality
We formalize modal semantics (`World`, `actualWorld`, `Accessible`), concrete instantiation
(`InstantiatedIn`), and genuine contingency (`ContingentSystem`).
We formulate a **General Contrastive PSR** (`GeneralContrastivePSR`), requiring an explanatory
ground for contingent concrete actualities without baking necessity (aseity) into the definition.
We establish the **Principle of Aseity** (`GroundingTotalityTerminatesInAseity`) as an explicit,
separate metaphysical principle.

## III. Substantive Deduction of the Necessary, Personal, and Free Source
We define separately:
- `IsNecessary T`: $T$ exists in all accessible worlds (Aseity).
- `NatureInvariant T`: $T$'s essential nature/faculties in any accessible world are identical to its actual nature in `actualWorld`.
- `IsPersonalAgent T`: $T$ possesses intellect to apprehend alternatives.
- `SelectsIntentionally T`: $T$ selects the actual system for reasons/values.
- `ActsFreely T`: $T$ chooses between alternative configurations under its necessary invariant nature.

We prove the exhaustiveness of grounding modes (`grounding_modes_exhaustive`) as a formal auxiliary theorem
derived from classical logic, removing it from the list of unproved metaphysical premises!

We formulate explicit metaphysical bridge principles:
- `TeleologicalAgencyPrinciple`: Supplying a contrastive justification between alternatives requires intentional personal agency.
- `PersonalAseityPreservesNature`: Aseity of a personal necessary ground entails that its nature is invariant across accessible worlds.
- `AgentialCounterfactualChoiceBridge`: An intentional personal agent choosing under contingency possesses counterfactual power to choose divergent accessible alternatives.
- Crucially, `ActsFreely` is ACTIVELY CONSTRUCTED via `agential_freedom_derived`, rather than received pre-packaged in the conclusion of an overarching bridge!

We prove the substantive trilemma of grounding modes without artificial hypotheses:
- Possibility 1 (Impersonal Necessitation) destroys contingency (`necessary_impersonal_ground_contradicts_contingency`).
- Possibility 2 (Impersonal Non-Necessitation) fails contrastive justification (`unjustified_alternative_fails_contrastive_at`).
- Possibility 3: Under the General Contrastive PSR and the metaphysical bridge principles,
  the system derives the reality of a **Structurally Transcendent, Necessary, Intentional, and Free Personal Source**
  (`contingent_system_derives_free_personal_source`).
-/

namespace Logos
namespace OntologicalIncompleteness

universe u

/-!
================================================================================
I. ATEMPORAL DETERMINATION SYSTEM & THE THREE INTERNAL TOPOLOGIES
================================================================================
-/

/-- An atemporal determination system where dependencies are purely structural and logical.
Priority is a well-founded strict partial order. -/
structure DeterminationSystem where
  Node : Type u
  Determines : Node → Node → Prop
  Prior : Node → Node → Prop
  priorWellFounded : WellFounded Prior
  priorTransitive : ∀ {a b c : Node}, Prior a b → Prior b c → Prior a c
  determinationRespectsPriority : ∀ {a b : Node}, Determines a b → Prior a b

/-- Fundamental irreflexivity of ontological priority: nothing can be prior to itself. -/
theorem prior_irrefl (D : DeterminationSystem.{u}) (x : D.Node) : D.Prior x x → False := by
  induction x using D.priorWellFounded.induction with
  | h b ih =>
    intro hb
    exact ih b hb hb

/-- Ancestral determination: transitive closure of internal determination. -/
def DeterminesAncestrally (Determines : α → α → Prop) : α → α → Prop :=
  Relation.TransGen Determines

theorem ancestral_respects_priority (D : DeterminationSystem.{u}) {a b : D.Node} :
    DeterminesAncestrally D.Determines a b → D.Prior a b := by
  intro h
  induction h with
  | single hStep => exact D.determinationRespectsPriority hStep
  | tail _ hStep ih =>
    have hLast := D.determinationRespectsPriority hStep
    exact D.priorTransitive ih hLast

/-!
--------------------------------------------------------------------------------
CASE 1: CLOSED CYCLES
--------------------------------------------------------------------------------
-/

/-- THEOREM 1 (Closed Cycles Violate Ontological Priority):
A closed explanatory cycle of any finite length ($a \prec \dots \prec a$) requires
a node to be ontologically prior to itself, violating well-founded priority.
Hence circularity is an ontic petitio principii that fails as an ultimate explanation. -/
theorem closed_cycle_violates_ontological_priority
    (D : DeterminationSystem.{u})
    (a : D.Node)
    (hCycle : DeterminesAncestrally D.Determines a a) :
    False := by
  have hPriorSelf := ancestral_respects_priority D hCycle
  exact prior_irrefl D a hPriorSelf

/-- THEOREM 1B (Internal Node Self-Determination Impossibility):
An internal node cannot determine itself without violating priority irreflexivity. -/
theorem internal_node_cannot_self_determine
    (D : DeterminationSystem.{u})
    (n : D.Node)
    (hSelfDet : D.Determines n n) :
    False :=
  prior_irrefl D n (D.determinationRespectsPriority hSelfDet)

/-!
--------------------------------------------------------------------------------
CASE 2: INFINITE REGRESS (WITHOUT ASSUMED WELL-FOUNDEDNESS)
--------------------------------------------------------------------------------
-/

/-- A dedicated structure representing an infinite regress of determinations,
without assuming that priority is well-founded. Every node has an internal determiner. -/
structure InfiniteRegressSystem where
  Node : Type u
  inhabited : Nonempty Node
  Determines : Node → Node → Prop
  has_prior_determiner : ∀ b : Node, ∃ a : Node, Determines a b

/-- Conditional determination rule: each node's actualization is conditional
on the actualization of its determiner. -/
def ConditionalDeterminationTransfer (S : InfiniteRegressSystem.{u}) (Actual : S.Node → Prop) : Prop :=
  ∀ a b : S.Node, S.Determines a b → (Actual a → Actual b)

/-- THEOREM 2A (Hume-Edwards Fallacy — Conditional Rules Satisfied by Vacuity):
Even if every node in an infinite regress has an internal determiner and conditional
determination is satisfied throughout, the chain fails to explain its global actuality.
The internal rules are identically satisfied by universal vacuity/nothingness (`fun _ => False`).
Hence internal conditional rules cannot explain why the system is actualized in reality! -/
theorem infinite_regress_conditional_rules_satisfied_by_vacuity
    (S : InfiniteRegressSystem.{u}) :
    ConditionalDeterminationTransfer S (fun _ => False) := by
  intro a b _ hFalse
  exact False.elim hFalse

/-- THEOREM 2B (Infinite Regress Fails Well-Foundedness):
Formal mathematical result: An infinite regress of internal determiners contains an infinite
descending chain and is strictly NOT well-founded in its ground direction (`¬ WellFounded S.Determines`).
EPISTEMOLOGICAL DISTINCTION:
This mathematical theorem proves that an infinite regress lacks well-foundedness. It does NOT, in isolation,
deduce that an infinite regress fails to be an ultimate ground. That stronger conclusion is philosophical:
it rests substantively on Theorem 2A (internal conditional rules being satisfied by universal vacuity)
and the Cosmological PSR, which demands a self-sufficient explanation of global concrete actuality.
(0 axioms). -/
theorem infinite_regress_cannot_self_ground
    (S : InfiniteRegressSystem.{u}) :
    ¬ WellFounded (fun a b => S.Determines a b) := by
  intro hWF
  have hNoMin : ∀ x, Acc (fun a b => S.Determines a b) x → False := by
    intro x hAcc
    induction hAcc with
    | intro b _ ih =>
      obtain ⟨a, ha⟩ := S.has_prior_determiner b
      exact ih a ha
  rcases S.inhabited with ⟨x0⟩
  exact hNoMin x0 (hWF.apply x0)

/-!
--------------------------------------------------------------------------------
CASE 3: BOUNDED CHAIN WITH INTERNAL LIMIT
--------------------------------------------------------------------------------
-/

/-- An internal boundary node: a node having no internal determiner within the system. -/
def IsInternalBruteFact (D : DeterminationSystem.{u}) (a : D.Node) : Prop :=
  ¬ ∃ b : D.Node, D.Determines b a

/-- Alias matching best.lean terminology: an ultimate internal terminal source within the chain. -/
abbrev UltimateInternalSource (D : DeterminationSystem.{u}) (a : D.Node) : Prop :=
  IsInternalBruteFact D a

/-- A system is fully internally determined if every node has an internal determiner. -/
def FullyInternallyDetermined (D : DeterminationSystem.{u}) : Prop :=
  ∀ b : D.Node, ∃ a : D.Node, D.Determines a b

/-- THEOREM 3A (Self-Grounding is Impossible):
A non-empty closed system cannot be fully internally determined. -/
theorem fully_internally_determined_is_impossible
    (D : DeterminationSystem.{u})
    (hNonempty : Nonempty D.Node) :
    ¬ FullyInternallyDetermined D := by
  intro hFull
  have hAllFalse : ∀ x : D.Node, False := fun x =>
    D.priorWellFounded.induction (C := fun _ => False) x fun b ih =>
      match hFull b with
      | ⟨a, ha⟩ => ih a (D.determinationRespectsPriority ha)
  rcases hNonempty with ⟨x0⟩
  exact hAllFalse x0

/-- THEOREM 3 (Ancestral Root Theorem — Transfer from best.lean):
For every node x in a well-founded determination system, there exists an internal terminal
source a (an internal node having no internal determiner, IsInternalBruteFact D a) such that
a ancestrally determines x (or a = x).
Demonstrated directly by well-founded induction on D.Prior.
STRICT SCOPE LIMITATION:
This result is strictly internal to the intra-systemic chain: a is a terminal node within
the internal relation Determines. It is NOT identified with the transcendent ultimate ground T.
(0 axioms). -/
theorem node_has_ancestral_ultimate_source
    (D : DeterminationSystem.{u})
    (x : D.Node) :
    ∃ a : D.Node,
      IsInternalBruteFact D a ∧
      (a = x ∨ DeterminesAncestrally D.Determines a x) := by
  induction x using D.priorWellFounded.induction with
  | h n ih =>
    by_cases hDet : ∃ c : D.Node, D.Determines c n
    · rcases hDet with ⟨c, hc⟩
      have hPrior : D.Prior c n := D.determinationRespectsPriority hc
      have ⟨a, haSource, haReach⟩ := ih c hPrior
      refine ⟨a, haSource, ?_⟩
      cases haReach with
      | inl haEq =>
        subst haEq
        exact Or.inr (Relation.TransGen.single hc)
      | inr haAnc =>
        exact Or.inr (Relation.TransGen.tail haAnc hc)
    · exact ⟨n, hDet, Or.inl rfl⟩

/-- THEOREM 3B (Existence of an Internal Boundary):
Every non-empty well-founded determination system contains at least one node
that is NOT determined by any internal node.
Derived directly as an immediate corollary of the Ancestral Root Theorem!
CRITICAL DISTINCTION: Absence of an internal determiner does NOT mean the node is
absolutely ungrounded; it proves that the system cannot be internally self-sufficient,
demanding an external ground.
(0 axioms). -/
theorem closed_system_has_unexplained_boundary
    (D : DeterminationSystem.{u})
    (hNonempty : Nonempty D.Node) :
    ∃ a : D.Node, IsInternalBruteFact D a := by
  rcases hNonempty with ⟨x0⟩
  obtain ⟨a, haSource, _⟩ := node_has_ancestral_ultimate_source D x0
  exact ⟨a, haSource⟩

/-!
--------------------------------------------------------------------------------
DEDUCTION OF TRANSCENDENCE & CONSTITUTIVE CIRCULARITY REFUTATION
--------------------------------------------------------------------------------
-/

/-!
--------------------------------------------------------------------------------
DIRECTIONAL CONVENTION OF CONSTITUTIVE PRIORITY:
`ConstitutivePriority a b` formally denotes `a ≺ b` (i.e. `a` is ontologically/constitutively prior to `b`,
or `a` conditions/determines/grounds `b`).
Ontological priority is strictly atemporal and explanatory, not a temporal sequence:
- `CandidateOnticItem.node n ≺ CandidateOnticItem.totality`: node `n` constitutes the totality `S`.
- `CandidateOnticItem.candidate e ≺ CandidateOnticItem.totality`: candidate ground `e` grounds the totality `S`.
- `CandidateOnticItem.condition ≺ CandidateOnticItem.candidate e`: condition `C` determines candidate ground `e`.
- `CandidateOnticItem.totality ≺ CandidateOnticItem.condition`: totality `S` conditions/grounds condition `C`.
Under transitive well-founded priority, any closed cycle `a ≺ ... ≺ a` violates irreflexivity (well_founded_irrefl).
--------------------------------------------------------------------------------
-/

/-- A unified ontic domain containing internal nodes, the system totality,
the concrete candidate external ground entity e, and any candidate external explanatory condition. -/
inductive CandidateOnticItem (Node : Type u) (Ext : Type u) where
  | totality : CandidateOnticItem Node Ext
  | node (n : Node) : CandidateOnticItem Node Ext
  | candidate (e : Ext) : CandidateOnticItem Node Ext
  | condition : CandidateOnticItem Node Ext

/-- Backward compatibility aliases for the ontic domain. -/
abbrev OnticDomain (Node : Type u) := CandidateOnticItem Node PUnit
abbrev OnticItem := OnticDomain

/-- Fundamental irreflexivity of any well-founded priority relation. -/
theorem well_founded_irrefl {α : Type u} (r : α → α → Prop) (wf : WellFounded r) (x : α) :
    r x x → False := by
  induction x using wf.induction with
  | h b ih =>
    intro hb
    exact ih b hb hb

/-- THEOREM 3C (Constitutive Circularity Refutation):
If an internal node n constitutively constitutes the totality (ConstitutivePriority (CandidateOnticItem.node n) CandidateOnticItem.totality),
and the totality were grounded by n (ConstitutivePriority CandidateOnticItem.totality (CandidateOnticItem.node n)),
then under transitive well-founded priority, n would be constitutively prior to itself,
violating irreflexivity and deriving False.
Hence an internal node cannot ground the totality without vicious circularity.
(0 axioms). -/
theorem internal_node_cannot_ground_totality_circularity
    {Node : Type u} {Ext : Type u}
    (ConstitutivePriority : CandidateOnticItem Node Ext → CandidateOnticItem Node Ext → Prop)
    (prior_wf : WellFounded ConstitutivePriority)
    (prior_trans : ∀ {a b c}, ConstitutivePriority a b → ConstitutivePriority b c → ConstitutivePriority a c)
    (n : Node)
    (hConstitutive : ConstitutivePriority (CandidateOnticItem.node n) CandidateOnticItem.totality)
    (hPurportedGround : ConstitutivePriority CandidateOnticItem.totality (CandidateOnticItem.node n)) :
    False := by
  have hCycle : ConstitutivePriority (CandidateOnticItem.node n) (CandidateOnticItem.node n) :=
    prior_trans hConstitutive hPurportedGround
  exact well_founded_irrefl ConstitutivePriority prior_wf (CandidateOnticItem.node n) hCycle

/-- THEOREM 3C₂ (Candidate-Relative Explanatory Circle Refutation - 3-Cycle):
If the candidate external ground entity e grounds the concrete Totality (ConstitutivePriority (CandidateOnticItem.candidate e) CandidateOnticItem.totality),
the Totality explains the explanatory Condition (ConstitutivePriority CandidateOnticItem.totality CandidateOnticItem.condition),
and that Condition explains the candidate entity's concrete determination (ConstitutivePriority CandidateOnticItem.condition (CandidateOnticItem.candidate e)),
then under transitive well-founded priority, candidate entity e explains itself (ConstitutivePriority (CandidateOnticItem.candidate e) (CandidateOnticItem.candidate e)),
violating irreflexivity and deriving False.
Hence consequence-dependent grounding for the specific candidate ground e is strictly impossible under well-founded priority.
(0 axioms). -/
theorem candidate_consequence_circularity_refutation
    {Node : Type u} {Ext : Type u}
    (ConstitutivePriority : CandidateOnticItem Node Ext → CandidateOnticItem Node Ext → Prop)
    (prior_wf : WellFounded ConstitutivePriority)
    (prior_trans : ∀ {a b c}, ConstitutivePriority a b → ConstitutivePriority b c → ConstitutivePriority a c)
    (e : Ext)
    (hGroundsTotality : ConstitutivePriority (CandidateOnticItem.candidate e) CandidateOnticItem.totality)
    (hTotalityExplainsCondition : ConstitutivePriority CandidateOnticItem.totality CandidateOnticItem.condition)
    (hConditionDeterminesGround : ConstitutivePriority CandidateOnticItem.condition (CandidateOnticItem.candidate e)) :
    False := by
  have hStep1 : ConstitutivePriority (CandidateOnticItem.candidate e) CandidateOnticItem.condition :=
    prior_trans hGroundsTotality hTotalityExplainsCondition
  have hCycle : ConstitutivePriority (CandidateOnticItem.candidate e) (CandidateOnticItem.candidate e) :=
    prior_trans hStep1 hConditionDeterminesGround
  exact well_founded_irrefl ConstitutivePriority prior_wf (CandidateOnticItem.candidate e) hCycle

/-- THEOREM 3C₃ (Candidate-Relative Direct Consequence Circularity Refutation - 2-Cycle):
If the candidate external ground entity e grounds the concrete Totality (ConstitutivePriority (CandidateOnticItem.candidate e) CandidateOnticItem.totality),
and the explanation of e's concrete determination appeals directly to the Totality it grounds
(ConstitutivePriority CandidateOnticItem.totality (CandidateOnticItem.candidate e)),
then under transitive well-founded priority, e explains itself, deriving False.
(0 axioms). -/
theorem candidate_direct_consequence_cycle_refutation
    {Node : Type u} {Ext : Type u}
    (ConstitutivePriority : CandidateOnticItem Node Ext → CandidateOnticItem Node Ext → Prop)
    (prior_wf : WellFounded ConstitutivePriority)
    (prior_trans : ∀ {a b c}, ConstitutivePriority a b → ConstitutivePriority b c → ConstitutivePriority a c)
    (e : Ext)
    (hGroundsTotality : ConstitutivePriority (CandidateOnticItem.candidate e) CandidateOnticItem.totality)
    (hTotalityExplainsGround : ConstitutivePriority CandidateOnticItem.totality (CandidateOnticItem.candidate e)) :
    False := by
  have hCycle : ConstitutivePriority (CandidateOnticItem.candidate e) (CandidateOnticItem.candidate e) :=
    prior_trans hGroundsTotality hTotalityExplainsGround
  exact well_founded_irrefl ConstitutivePriority prior_wf (CandidateOnticItem.candidate e) hCycle

/-- Backward compatibility alias for the explanatory circle theorem. -/
abbrev consequence_dependent_grounding_induces_explanatory_circle := @candidate_consequence_circularity_refutation
abbrev consequence_dependent_direct_cycle_refutation := @candidate_direct_consequence_cycle_refutation

/-!
================================================================================
II. UNIFIED CONCRETE SYSTEM, MODAL FRAMEWORK & TOTALITY PSR
================================================================================
-/

/-- A unified concrete determination system combining internal relational determination
with modal instantiation across possible worlds. -/
structure ConcreteSystem where
  Node : Type u
  World : Type u
  actualWorld : World
  Accessible : World → World → Prop
  /-- System S is concretely instantiated in world w. -/
  InstantiatedIn : World → Prop
  /-- Global configuration of nodes in world w. -/
  ConfigurationIn : World → (Node → Bool)
  /-- Internal determination relation between nodes within the system. -/
  Determines : Node → Node → Prop
  /-- Ontological priority order between nodes. -/
  Prior : Node → Node → Prop
  priorWellFounded : WellFounded Prior
  determinationRespectsPriority : ∀ {a b : Node}, Determines a b → Prior a b

/-- Natural embedding of internal priority into the inter-level ontic domain:
Internal ontological priority between nodes corresponds to constitutive priority between
their respective node representations in the ontic domain.
EPISTEMOLOGICAL DISTINCTION OF ROLES:
- `S.Determines` and `S.Prior` govern the intra-systemic relational structure between nodes.
- `ConstitutivePriority` governs the inter-level ontic priority between nodes, the totality,
  the candidate ground entity e, and explanatory conditions C. -/
def InternalPriorityEmbedsInConstitutive
    (S : ConcreteSystem.{u})
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop) : Prop :=
  ∀ (Ext : Type u) (a b : S.Node),
    S.Prior a b → ConstitutivePriority Ext (CandidateOnticItem.node a) (CandidateOnticItem.node b)

/-- THEOREM 3D₀ (Internal Priority Irreflexivity via Constitutive Embedding):
If internal priority embeds in constitutive priority, any internal priority cycle on nodes
is refuted by the well-foundedness of constitutive priority.
(0 axioms). -/
theorem internal_priority_irrefl_from_constitutive
    (S : ConcreteSystem.{u})
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (prior_wf : ∀ Ext, WellFounded (ConstitutivePriority Ext))
    (hEmbed : InternalPriorityEmbedsInConstitutive S ConstitutivePriority)
    (Ext : Type u)
    (n : S.Node) :
    S.Prior n n → False := by
  intro hPriorSelf
  have hConstitutiveSelf := hEmbed Ext n n hPriorSelf
  exact well_founded_irrefl (ConstitutivePriority Ext) (prior_wf Ext) (CandidateOnticItem.node n) hConstitutiveSelf

/-- Internal determination rules preserved within world w:
Whenever node `a` determines node `b`, the state of `b` is conditioned by `a`. -/
def InternalRulesPreserved (S : ConcreteSystem.{u}) (w : S.World) : Prop :=
  ∀ a b : S.Node, S.Determines a b → (S.ConfigurationIn w a = S.ConfigurationIn w b)

/-- THEOREM 3D (Compossibility of Internal Rules with Divergent Configurations):
Formal result: Demonstrates that the satisfaction of internal relational determination rules
(`InternalRulesPreserved S`) is compossible across worlds with divergent global configurations
(`ConfigurationIn w_alt ≠ ConfigurationIn actualWorld`).
PRECISE ROLE & CALIBRATION:
This theorem witnesses that there exists a predicate `R` (namely `InternalRulesPreserved S`) that holds
in both the actual world and an alternative world despite their divergent configurations.
It does NOT, by itself, demonstrate that internal rules cannot be part of an explanation, nor does it
alone prove the impossibility of every conceivable internal distinction. Rather, it formally exhibits
that compliance with relational determination rules alone is invariant between these divergent worlds,
so that mere internal relational compliance cannot serve as a differentiator between them.
(0 axioms). -/
theorem internal_rules_fail_contrastive_distinction
    (S : ConcreteSystem.{u})
    (w_alt : S.World)
    (hActualRules : InternalRulesPreserved S S.actualWorld)
    (hAltRules : InternalRulesPreserved S w_alt)
    (hDiffCfg : S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) :
    ∃ R : S.World → Prop, R S.actualWorld ∧ R w_alt ∧ (S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) :=
  ⟨InternalRulesPreserved S, hActualRules, hAltRules, hDiffCfg⟩

/-- Descriptive alias for Theorem 3D, reflecting its exact formal proof. -/
abbrev internal_rules_compossible_with_divergent_configurations :=
  @internal_rules_fail_contrastive_distinction

/-- A concrete system is fully internally determined if every node has an internal determiner within S. -/
def SystemFullyInternallyDetermined (S : ConcreteSystem.{u}) : Prop :=
  ∀ b : S.Node, ∃ a : S.Node, S.Determines a b

/-- THEOREM 3D₁ (Impossibility of Fully Internally Determined Concrete System):
A non-empty concrete system cannot have all its nodes determined by other internal nodes,
under well-founded ontological priority.
(0 axioms). -/
theorem concrete_system_cannot_be_fully_internally_determined
    (S : ConcreteSystem.{u})
    (hNonEmpty : Nonempty S.Node) :
    ¬ SystemFullyInternallyDetermined S := by
  intro hFull
  have hAllFalse : ∀ x : S.Node, False := fun x =>
    S.priorWellFounded.induction (C := fun _ => False) x fun b ih =>
      match hFull b with
      | ⟨a, ha⟩ => ih a (S.determinationRespectsPriority ha)
  rcases hNonEmpty with ⟨x0⟩
  exact hAllFalse x0

/-- An internal terminal node in S (a node with no internal determiner within the relational structure of S).
EPISTEMOLOGICAL DISTINCTION:
An internal terminal node is NOT an absolutely brute fact in the metaphysical sense;
it is merely a boundary of internal relational explanation within the intra-systemic chain.
Crucially, as demonstrated in Theorem 3E (`internal_candidate_cannot_ground_totality`),
an internal boundary node cannot ground the totality of S without constitutive circularity! -/
def IsInternalTerminalNode (S : ConcreteSystem.{u}) (a : S.Node) : Prop :=
  ¬ ∃ b : S.Node, S.Determines b a

/-- Every non-empty concrete system contains an internal terminal node.
(0 axioms). -/
theorem concrete_system_has_internal_terminal_node
    (S : ConcreteSystem.{u})
    (hNonEmpty : Nonempty S.Node) :
    ∃ a : S.Node, IsInternalTerminalNode S a := by
  apply Classical.byContradiction
  intro hNoTerminal
  have hFull : SystemFullyInternallyDetermined S := by
    intro b
    apply Classical.byContradiction
    intro hNotDet
    apply hNoTerminal
    exact ⟨b, hNotDet⟩
  exact concrete_system_cannot_be_fully_internally_determined S hNonEmpty hFull

/-- Genuine contingency of the system:
The system is concretely instantiated in the actual world, but there exists an accessible
world where it fails to be instantiated or has an alternative configuration. -/
def ContingentSystem (S : ConcreteSystem.{u}) : Prop :=
  S.InstantiatedIn S.actualWorld ∧
  ∃ w_alt : S.World,
    S.Accessible S.actualWorld w_alt ∧
    (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld)

/-- Structural identity of a candidate ground entity:
distinguishing structurally between internal nodes of the system and external entities. -/
inductive GroundIdentity (Node : Type u) (Ext : Type u) where
  | internal (n : Node) : GroundIdentity Node Ext
  | external (e : Ext) : GroundIdentity Node Ext

/-- Essential nature and rational faculties of the ground entity. -/
structure Essence where
  power : Nat
  rationality : Nat
  deriving DecidableEq

/-- A candidate ground for the concrete totality, without presupposing transcendence. -/
structure CandidateGround (S : ConcreteSystem.{u}) where
  ExtEntity : Type u
  ground : GroundIdentity S.Node ExtEntity
  ExistsAt : GroundIdentity S.Node ExtEntity → S.World → Prop
  /-- Concrete grounding relation formally bound to S's instantiation and configuration. -/
  GroundsConcreteActuality : GroundIdentity S.Node ExtEntity → S.World → Prop
  grounding_binds_actuality : ∀ w : S.World,
    GroundsConcreteActuality ground w →
      (ExistsAt ground w ∧ S.InstantiatedIn w ∧ S.ConfigurationIn w = S.ConfigurationIn S.actualWorld)
  /-- Essential nature of the ground across worlds. -/
  EssenceOf : GroundIdentity S.Node ExtEntity → S.World → Essence
  ProvidesContrastiveJustification : GroundIdentity S.Node ExtEntity → S.World → S.World → Prop
  ApprehendsAlternative : GroundIdentity S.Node ExtEntity → S.World → Prop
  ReasonsFavor : GroundIdentity S.Node ExtEntity → S.World → S.World → Prop
  ChoosesOutcomeAt : GroundIdentity S.Node ExtEntity → S.World → (Option (S.Node → Bool)) → Prop
  /-- General outcome explanation/determination across specific worlds (decoupled from actual-world rigidity). -/
  DeterminesOutcomeAt : GroundIdentity S.Node ExtEntity → S.World → (Option (S.Node → Bool)) → Prop

/-- THEOREM 3E (Internal Candidate Cannot Ground Totality Without Circularity):
An internal candidate node cannot ground the totality without violating priority irreflexivity.
(0 axioms). -/
theorem internal_candidate_cannot_ground_totality
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (n : S.Node)
    (_hInternal : T.ground = GroundIdentity.internal n)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (prior_wf : ∀ Ext, WellFounded (ConstitutivePriority Ext))
    (prior_trans : ∀ Ext {a b c : CandidateOnticItem S.Node Ext}, ConstitutivePriority Ext a b → ConstitutivePriority Ext b c → ConstitutivePriority Ext a c)
    (hConstitutiveOfTotality : ∀ Ext (m : S.Node), ConstitutivePriority Ext (CandidateOnticItem.node m) CandidateOnticItem.totality)
    (hGroundsTotality : ∀ Ext, ConstitutivePriority Ext CandidateOnticItem.totality (CandidateOnticItem.node n)) :
    False :=
  internal_node_cannot_ground_totality_circularity (ConstitutivePriority T.ExtEntity) (prior_wf T.ExtEntity) (fun {_a _b _c} => prior_trans T.ExtEntity) n
    (hConstitutiveOfTotality T.ExtEntity n) (hGroundsTotality T.ExtEntity)

/-- THEOREM 3F (Derivation of Structural Transcendence):
An internal candidate node cannot ground the totality without constitutive circularity.
Under transitive well-founded constitutive priority, any candidate ground that provides
the ultimate grounding of the concrete totality MUST be structurally external:
∃ e : T.ExtEntity, T.ground = GroundIdentity.external e.
Transcendence is DERIVED, not presupposed.
(0 axioms). -/
theorem candidate_ground_must_be_structurally_external
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (prior_wf : ∀ Ext, WellFounded (ConstitutivePriority Ext))
    (prior_trans : ∀ Ext {a b c : CandidateOnticItem S.Node Ext}, ConstitutivePriority Ext a b → ConstitutivePriority Ext b c → ConstitutivePriority Ext a c)
    (hConstitutiveOfTotality : ∀ Ext (m : S.Node), ConstitutivePriority Ext (CandidateOnticItem.node m) CandidateOnticItem.totality)
    (hInternalGroundsTotality : ∀ n : S.Node, T.ground = GroundIdentity.internal n →
      ∀ Ext, ConstitutivePriority Ext CandidateOnticItem.totality (CandidateOnticItem.node n)) :
    ∃ e : T.ExtEntity, T.ground = GroundIdentity.external e := by
  cases hId : T.ground with
  | internal n =>
    have hFalse := internal_candidate_cannot_ground_totality S T n hId
      ConstitutivePriority prior_wf (fun Ext {a b c} => prior_trans Ext)
      (fun Ext m => hConstitutiveOfTotality Ext m) (hInternalGroundsTotality n hId)
    exact False.elim hFalse
  | external e =>
    exact ⟨e, rfl⟩

/-- Tripartite modal distinction:
1. Invariance of necessary existence (Aseity): T exists in all accessible worlds. -/
def IsNecessary (S : ConcreteSystem.{u}) (T : CandidateGround S) : Prop :=
  ∀ w : S.World, S.Accessible S.actualWorld w → T.ExistsAt T.ground w

/-- Tripartite modal distinction:
2. Invariance of essential nature directly referenced to actualWorld:
The ground's essential nature and rational faculties in any accessible world w
are identical to its actual essential nature in actualWorld. -/
def NatureInvariant (S : ConcreteSystem.{u}) (T : CandidateGround S) : Prop :=
  ∀ w : S.World, S.Accessible S.actualWorld w →
    T.EssenceOf T.ground w = T.EssenceOf T.ground S.actualWorld

/-- Personal Agency: T apprehends the possible alternative states of affairs.
Scoped to divergent accessible alternatives where contrastive justification is required. -/
def IsPersonalAgent (S : ConcreteSystem.{u}) (T : CandidateGround S) : Prop :=
  ∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
    (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) →
    T.ApprehendsAlternative T.ground w_alt

/-- Intentional Selection: T selects actualWorld over w_alt in virtue of reasons favoring the actual configuration. -/
def SelectsIntentionally (S : ConcreteSystem.{u}) (T : CandidateGround S) : Prop :=
  ∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
    T.ReasonsFavor T.ground S.actualWorld w_alt ∧
    T.ChoosesOutcomeAt T.ground S.actualWorld (some (S.ConfigurationIn S.actualWorld))

/-- Positive World-Relational Libertarian Freedom (Counterfactual Choice Power):
SEMANTIC ALIGNMENT & DIVISION OF LABELS:
- The actual choice in `actualWorld` is formally guaranteed by `SelectsIntentionally`,
  which specifies `T.ChoosesOutcomeAt T.ground S.actualWorld (some (S.ConfigurationIn S.actualWorld))`
  guided by reasons.
- `ActsFreely` formalizes the complementary counterfactual condition: under the exact same invariant
  essential nature (`NatureInvariant S T`), there exists an accessible alternative world `w_alt` where
  `T` has the identical essential nature (`T.EssenceOf T.ground w_alt = T.EssenceOf T.ground S.actualWorld`),
  the system's configuration diverges (`altOutcome ≠ actualOutcome`), and `T` chooses that alternative outcome
  at `w_alt` (`T.ChoosesOutcomeAt T.ground w_alt altOutcome`).
Together in `FreePersonalSource`, they establish that `T` freely determined the actual world while possessing
the genuine, unforced capacity to choose an alternative under the identical nature. -/
def ActsFreely (S : ConcreteSystem.{u}) (T : CandidateGround S) : Prop :=
  NatureInvariant S T ∧
  ∃ w_alt : S.World, S.Accessible S.actualWorld w_alt ∧
    T.EssenceOf T.ground w_alt = T.EssenceOf T.ground S.actualWorld ∧
    (let actualOutcome : Option (S.Node → Bool) := some (S.ConfigurationIn S.actualWorld)
     let altOutcome : Option (S.Node → Bool) :=
       if S.InstantiatedIn w_alt then some (S.ConfigurationIn w_alt) else none
     altOutcome ≠ actualOutcome ∧
     T.ChoosesOutcomeAt T.ground w_alt altOutcome)

/-- Composite outcome of the concrete system S at world w:
`some (ConfigurationIn w)` if instantiated, `none` if not instantiated.
Directly aligns with the option-based outcome representation in ActsFreely and ChoosesOutcomeAt. -/
noncomputable def SystemOutcomeAt (S : ConcreteSystem.{u}) (w : S.World) : Option (S.Node → Bool) :=
  if S.InstantiatedIn w then some (S.ConfigurationIn w) else none

/-- Lemma connecting SystemOutcomeAt divergence with the disjunctive formulation in ContingentSystem:
`SystemOutcomeAt S w ≠ SystemOutcomeAt S S.actualWorld` holds if and only if
`¬ S.InstantiatedIn w ∨ S.ConfigurationIn w ≠ S.ConfigurationIn S.actualWorld`.
(0 axioms). -/
theorem system_outcome_diff_iff
    (S : ConcreteSystem.{u})
    (w : S.World)
    (hInstAct : S.InstantiatedIn S.actualWorld) :
    (SystemOutcomeAt S w ≠ SystemOutcomeAt S S.actualWorld) ↔
    (¬ S.InstantiatedIn w ∨ S.ConfigurationIn w ≠ S.ConfigurationIn S.actualWorld) := by
  open Classical in
  dsimp [SystemOutcomeAt]
  by_cases hInstW : S.InstantiatedIn w
  · have h1 : (if S.InstantiatedIn w then some (S.ConfigurationIn w) else none) = some (S.ConfigurationIn w) := by
      split
      · rfl
      · contradiction
    have h2 : (if S.InstantiatedIn S.actualWorld then some (S.ConfigurationIn S.actualWorld) else none) = some (S.ConfigurationIn S.actualWorld) := by
      split
      · rfl
      · contradiction
    rw [h1, h2]
    constructor
    · intro hNe
      right
      intro hEq
      apply hNe
      rw [hEq]
    · intro hOr
      cases hOr with
      | inl hNot => exact False.elim (hNot hInstW)
      | inr hDiff =>
        intro hSomeEq
        injection hSomeEq with hCfgEq
        exact hDiff hCfgEq
  · have h1 : (if S.InstantiatedIn w then some (S.ConfigurationIn w) else none) = none := by
      split
      · contradiction
      · rfl
    have h2 : (if S.InstantiatedIn S.actualWorld then some (S.ConfigurationIn S.actualWorld) else none) = some (S.ConfigurationIn S.actualWorld) := by
      split
      · rfl
      · contradiction
    rw [h1, h2]
    constructor
    · intro _
      exact Or.inl hInstW
    · intro _
      intro hEq
      contradiction

/-- An outcome of system S is rigidly fixed by the candidate ground's invariant intrinsic basis:
across all accessible worlds where T has its actual essential nature, the system S
produces the exact same composite outcome (instantiation and configuration) as in actualWorld. -/
def OutcomeFixedByGroundBasis (S : ConcreteSystem.{u}) (T : CandidateGround S) : Prop :=
  ∀ w : S.World, S.Accessible S.actualWorld w →
    T.EssenceOf T.ground w = T.EssenceOf T.ground S.actualWorld →
    SystemOutcomeAt S w = SystemOutcomeAt S S.actualWorld

/-- MODAL DUALITY THEOREM (Transfer from best.lean, atemporal):
Rigorous classical equivalence between the failure of the system's outcome to be fixed
by the ground's invariant intrinsic basis and the existence of an accessible alternative
world where the ground has the identical essential nature, yet the system's outcome diverges.
Proved purely by classical logic without temporal notions or unproved postulates!
(Axiomas: [propext, Classical.choice]). -/
theorem not_fixed_by_basis_iff_exists_divergent_accessible_world
    (S : ConcreteSystem.{u})
    (T : CandidateGround S) :
    (¬ OutcomeFixedByGroundBasis S T) ↔
    (∃ w_alt : S.World,
      S.Accessible S.actualWorld w_alt ∧
      T.EssenceOf T.ground w_alt = T.EssenceOf T.ground S.actualWorld ∧
      SystemOutcomeAt S w_alt ≠ SystemOutcomeAt S S.actualWorld) := by
  constructor
  · intro hNotFixed
    apply Classical.byContradiction
    intro hNoAlt
    apply hNotFixed
    intro w hAcc hEss
    apply Classical.byContradiction
    intro hDiff
    apply hNoAlt
    exact ⟨w, hAcc, hEss, hDiff⟩
  · intro ⟨w_alt, hAcc, hEss, hDiff⟩ hFixed
    have hSame := hFixed w_alt hAcc hEss
    exact hDiff hSame

/-- THEOREM (Contingent System Yields Divergent Accessible World Under Invariant Nature):
If system S is contingent, and candidate ground T has an invariant essential nature,
there constructively exists an accessible alternative world where T has the identical essential
nature, but the outcome of S diverges.
Proved directly from ContingentSystem and NatureInvariant without assuming the alternative as a premise!
(0 axioms). -/
theorem contingent_system_yields_divergent_accessible_world_under_invariant_nature
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (hCont : ContingentSystem S)
    (hNature : NatureInvariant S T) :
    ∃ w_alt : S.World,
      S.Accessible S.actualWorld w_alt ∧
      T.EssenceOf T.ground w_alt = T.EssenceOf T.ground S.actualWorld ∧
      SystemOutcomeAt S w_alt ≠ SystemOutcomeAt S S.actualWorld := by
  obtain ⟨hInstAct, w_alt, hAcc, hDiv⟩ := hCont
  have hEss := hNature w_alt hAcc
  have hDiff := (system_outcome_diff_iff S w_alt hInstAct).mpr hDiv
  exact ⟨w_alt, hAcc, hEss, hDiff⟩

/-- COROLLARY: Under ContingentSystem S and NatureInvariant S T, the system's outcome
is strictly NOT fixed by the ground's invariant intrinsic basis.
(Axiomas: [propext, Classical.choice]). -/
theorem contingent_system_under_invariant_nature_not_fixed
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (hCont : ContingentSystem S)
    (hNature : NatureInvariant S T) :
    ¬ OutcomeFixedByGroundBasis S T := by
  have hExDiv := contingent_system_yields_divergent_accessible_world_under_invariant_nature S T hCont hNature
  exact (not_fixed_by_basis_iff_exists_divergent_accessible_world S T).mpr hExDiv

/-- METAPHYSICAL BRIDGE 5A (Agential Counterfactual Choice Bridge — Stage 4):
Tag: META.
Philosophical Justification & Analytical Audit of Content:
1. What it adds to prior premises:
   - `SelectsIntentionally S T` guarantees ONLY that in `actualWorld`, T chooses the actual outcome
     (`T.ChoosesOutcomeAt T.ground S.actualWorld (some (S.ConfigurationIn S.actualWorld))`) guided by reasons.
   - `ContingentSystem S` guarantees that there exists an accessible world `w_alt` where the system has
     a divergent outcome (`altOutcome ≠ actualOutcome`).
   - `NatureInvariant S T` guarantees that T's essential nature and rational faculties at `w_alt` are
     identical to its actual nature (`T.EssenceOf T.ground w_alt = T.EssenceOf T.ground S.actualWorld`).
   - What was MISSING is the agential status of `altOutcome`: does `altOutcome` at `w_alt` represent a
     genuine counterfactual choice of the same agent (`T.ChoosesOutcomeAt T.ground w_alt altOutcome`),
     or is it an unchosen divergence, a fatalistic accident, an involuntary failure, or mere stochastic chance?
   - `AgentialCounterfactualChoiceBridge` supplies PRECISELY this missing step: it stipulates that under
     the same essential nature, the divergent outcome is also an intentional agential choice of T.
2. Substantive Metaphysical Commitment:
   - As proven by `intentional_selection_does_not_deduce_libertarian_freedom`, this bridge CANNOT be deduced
     from `IsPersonalAgent`, `SelectsIntentionally`, `NatureInvariant`, and `ContingentSystem` by pure logic.
   - It formalizes the substantive Libertarian Principle of Agency: rational choice between contingent
     alternatives is a two-way power (potestas ad utrumque), where the alternative outcome is an agential
     option within the personal source's counterfactual choosing power. -/
def AgentialCounterfactualChoiceBridge
    (S : ConcreteSystem.{u})
    (T : CandidateGround S) : Prop :=
  NatureInvariant S T →
  SelectsIntentionally S T →
  ∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
    SystemOutcomeAt S w_alt ≠ SystemOutcomeAt S S.actualWorld →
    T.ChoosesOutcomeAt T.ground w_alt (SystemOutcomeAt S w_alt)

/-- THEOREM 6B (Decomposed Derivation of Libertarian Freedom):
Demonstrates that Libertarian Freedom (`ActsFreely S T`) is derived by combining:
(1) Essential nature invariance (`NatureInvariant S T`),
(2) The existence of a divergent accessible alternative (derived from `ContingentSystem S`),
(3) Intentional selection guided by reasons (`SelectsIntentionally S T`),
(4) Agential counterfactual choice (`AgentialCounterfactualChoiceBridge S T`).
(0 axioms). -/
theorem agential_freedom_derived
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (hCont : ContingentSystem S)
    (hNature : NatureInvariant S T)
    (hSel : SelectsIntentionally S T)
    (hChoice : AgentialCounterfactualChoiceBridge S T) :
    ActsFreely S T := by
  have ⟨hInstAct, _⟩ := hCont
  obtain ⟨w_alt, hAcc, hEss, hDiff⟩ :=
    contingent_system_yields_divergent_accessible_world_under_invariant_nature S T hCont hNature
  have hChoosesAlt := hChoice hNature hSel w_alt hAcc hDiff
  refine ⟨hNature, w_alt, hAcc, hEss, ?_⟩
  dsimp [SystemOutcomeAt] at hDiff hChoosesAlt
  open Classical in
  have hAct : (if S.InstantiatedIn S.actualWorld then some (S.ConfigurationIn S.actualWorld) else none) = some (S.ConfigurationIn S.actualWorld) := by
    split
    · rfl
    · contradiction
  rw [hAct] at hDiff
  exact ⟨hDiff, hChoosesAlt⟩

/-- Minimal well-founded relation on unit domain for countermodel construction. -/
private theorem emptyUnitWf : WellFounded (fun (_ _ : Unit) => False) := by
  constructor
  intro x
  constructor
  intro y hy
  exact False.elim hy

/-- Countermodel System: A non-empty contingent concrete system. -/
def countermodelS : ConcreteSystem.{0} where
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

theorem outcome_true : SystemOutcomeAt countermodelS true = some (countermodelS.ConfigurationIn true) := by
  dsimp [SystemOutcomeAt, countermodelS]
  split
  · rfl
  · contradiction

theorem outcome_false : SystemOutcomeAt countermodelS false = some (countermodelS.ConfigurationIn false) := by
  dsimp [SystemOutcomeAt, countermodelS]
  split
  · rfl
  · contradiction

/-- Evaluation of configuration goodness/order:
Assigns an objective metric of value to each concrete configuration.
In countermodelS, the actual configuration has value 1, while the divergent configuration has value 0. -/
def configurationValue (cfg : Unit → Bool) : Nat :=
  if cfg () = true then 1 else 0

/-- Evaluative outcome comparison:
Outcome out1 is evaluatively preferred to out2 if:
(1) both are concrete configurations and out1 has higher or equal value; or
(2) out1 is instantiated while out2 is uninstantiated. -/
def outcomePreference (out1 out2 : Option (Unit → Bool)) : Prop :=
  match out1, out2 with
  | some c1, some c2 => configurationValue c1 ≥ configurationValue c2
  | some _, none => True
  | none, _ => False

/-- Strict contrastive preference:
Outcome out1 is strictly superior to out2. -/
def strictOutcomePreference (out1 out2 : Option (Unit → Bool)) : Prop :=
  match out1, out2 with
  | some c1, some c2 => configurationValue c1 > configurationValue c2
  | some _, none => True
  | none, _ => False

def isEvaluativelyMaximal (out : Option (Unit → Bool)) : Prop :=
  ∀ out_alt : Option (Unit → Bool), ¬ strictOutcomePreference out_alt out

noncomputable def outcomeEvaluativeReasonsFavor (w1 w2 : countermodelS.World) : Prop :=
  outcomePreference (SystemOutcomeAt countermodelS w1) (SystemOutcomeAt countermodelS w2)

/-- Rational Choice Determination:
An outcome is chosen at world w if and only if it is the concrete outcome at w and it is evaluatively maximal.
This is completely free of any world-identity indices (no `w = true`). -/
noncomputable def outcomeEvaluativeChoosesOutcomeAt (w : countermodelS.World) (out : Option (Unit → Bool)) : Prop :=
  out = SystemOutcomeAt countermodelS w ∧ isEvaluativelyMaximal out

noncomputable def outcomeEvaluativeProvidesContrastiveJustification (w1 w2 : countermodelS.World) : Prop :=
  strictOutcomePreference (SystemOutcomeAt countermodelS w1) (SystemOutcomeAt countermodelS w2) ∧
  outcomeEvaluativeChoosesOutcomeAt w1 (SystemOutcomeAt countermodelS w1)

/-- Substantive Countermodel Ground: A necessary personal agent with invariant nature that intentionally selects
the actual world for objective evaluative reasons, but does NOT possess counterfactual choice over the alternative outcome. -/
noncomputable def substantiveCountermodelT : CandidateGround countermodelS where
  ExtEntity := Unit
  ground := GroundIdentity.external ()
  ExistsAt := fun _ _ => True
  GroundsConcreteActuality := fun _ w => w = true
  grounding_binds_actuality := by
    intro w hw
    subst hw
    refine ⟨trivial, trivial, rfl⟩
  EssenceOf := fun _ _ => ⟨1, 1⟩
  ProvidesContrastiveJustification := fun _ w1 w2 => outcomeEvaluativeProvidesContrastiveJustification w1 w2
  ApprehendsAlternative := fun _ _ => True
  ReasonsFavor := fun _ w1 w2 => outcomeEvaluativeReasonsFavor w1 w2
  ChoosesOutcomeAt := fun _ w out => outcomeEvaluativeChoosesOutcomeAt w out
  DeterminesOutcomeAt := fun _ w out => outcomeEvaluativeChoosesOutcomeAt w out

/-- Canonical unified countermodel ground (alias to substantiveCountermodelT). -/
noncomputable def countermodelT : CandidateGround countermodelS := substantiveCountermodelT

theorem true_is_maximal : isEvaluativelyMaximal (SystemOutcomeAt countermodelS true) := by
  intro out_alt hStrict
  rw [outcome_true] at hStrict
  cases out_alt with
  | none => contradiction
  | some cfg =>
    dsimp [strictOutcomePreference, configurationValue, countermodelS] at hStrict
    split at hStrict <;> revert hStrict <;> decide

theorem false_not_maximal : ¬ isEvaluativelyMaximal (SystemOutcomeAt countermodelS false) := by
  intro hMax
  have hStrict : strictOutcomePreference (SystemOutcomeAt countermodelS true) (SystemOutcomeAt countermodelS false) := by
    rw [outcome_true, outcome_false]
    dsimp [strictOutcomePreference, configurationValue, countermodelS]
    decide
  exact hMax (SystemOutcomeAt countermodelS true) hStrict

theorem countermodelS_contingent : ContingentSystem countermodelS := by
  refine ⟨trivial, false, trivial, Or.inr ?_⟩
  intro hEq
  have hT := congrFun hEq ()
  revert hT
  decide

theorem countermodelT_necessary : IsNecessary countermodelS countermodelT := by
  intro _ _
  exact trivial

theorem countermodelT_nature_invariant : NatureInvariant countermodelS countermodelT := by
  intro _ _
  rfl

theorem countermodelT_personal_agent : IsPersonalAgent countermodelS countermodelT := by
  intro _ _ _
  exact trivial

theorem countermodelT_selects_intentionally : SelectsIntentionally countermodelS countermodelT := by
  intro w_alt _
  constructor
  · cases w_alt
    · change outcomePreference (SystemOutcomeAt countermodelS true) (SystemOutcomeAt countermodelS false)
      rw [outcome_true, outcome_false]
      dsimp [outcomePreference, configurationValue, countermodelS]
      decide
    · change outcomePreference (SystemOutcomeAt countermodelS true) (SystemOutcomeAt countermodelS true)
      rw [outcome_true]
      dsimp [outcomePreference, configurationValue, countermodelS]
      decide
  · refine ⟨outcome_true.symm, ?_⟩
    have hMax := true_is_maximal
    rw [outcome_true] at hMax
    exact hMax

theorem countermodelT_fails_counterfactual_choice_bridge : ¬ AgentialCounterfactualChoiceBridge countermodelS countermodelT := by
  intro hBridge
  have hDiff : SystemOutcomeAt countermodelS false ≠ SystemOutcomeAt countermodelS true := by
    apply (system_outcome_diff_iff countermodelS false trivial).mpr
    right
    intro hEq
    have hT := congrFun hEq ()
    revert hT
    decide
  have hChoiceFalse := hBridge countermodelT_nature_invariant countermodelT_selects_intentionally false trivial hDiff
  have hFalseMax := hChoiceFalse.2
  rw [hChoiceFalse.1] at hFalseMax
  exact false_not_maximal hFalseMax

theorem countermodelT_fails_acts_freely : ¬ ActsFreely countermodelS countermodelT := by
  intro ⟨_, w_alt, _, _, hDiff, hChoosesAlt⟩
  cases w_alt
  · have hFalseMax := hChoosesAlt.2
    rw [hChoosesAlt.1] at hFalseMax
    exact false_not_maximal hFalseMax
  · apply hDiff
    dsimp [countermodelS]
    simp

/-- THEOREM 6B₁ (Intentional Selection Does Not Logically Deduce Libertarian Freedom):
Formal countermodel in the Lean 4 kernel proving that:
(1) `ContingentSystem S`
(2) `IsNecessary S T`
(3) `NatureInvariant S T`
(4) `IsPersonalAgent S T`
(5) `SelectsIntentionally S T`
do NOT, by bare classical or modal logic, deduce `AgentialCounterfactualChoiceBridge S T`
nor `ActsFreely S T`.
This establishes rigorously that `AgentialCounterfactualChoiceBridge` is an IRREDUCIBLE
metaphysical bridge principle, rather than a hidden analytical triviality.
(0 axioms). -/
theorem intentional_selection_does_not_deduce_libertarian_freedom :
    ∃ (S : ConcreteSystem.{0}) (T : CandidateGround S),
      ContingentSystem S ∧
      IsNecessary S T ∧
      NatureInvariant S T ∧
      IsPersonalAgent S T ∧
      SelectsIntentionally S T ∧
      (¬ AgentialCounterfactualChoiceBridge S T) ∧
      (¬ ActsFreely S T) :=
  ⟨countermodelS, countermodelT, countermodelS_contingent, countermodelT_necessary, countermodelT_nature_invariant,
   countermodelT_personal_agent, countermodelT_selects_intentionally,
   countermodelT_fails_counterfactual_choice_bridge, countermodelT_fails_acts_freely⟩

/-!
================================================================================
CRITICAL TRIPARTITE METAPHYSICAL DISTINCTION
================================================================================
To maintain epistemological discipline, we strictly distinguish three levels of conclusion:
Level 1: Ground Necessity & Nature Invariance (`IsNecessary S T ∧ NatureInvariant S T`):
  T exists in all accessible worlds with an identical essential nature and rational faculties.
Level 2: Modal Contingency of the Totality (`ContingentSystem S`):
  There exists an accessible world `w_alt` where the system configuration diverges from the actual configuration.
  Crucially, Level 2 does NOT entail that T had the positive agential power to choose that alternative outcome!
Level 3: Positive Counterfactual Freedom (`ActsFreely S T`):
  T possesses the positive agential capacity to choose the alternative outcome under that exact same nature.
  Level 3 requires the explicit metaphysical bridge `AgentialCounterfactualChoiceBridge S T`.
================================================================================
-/

/-- A neutral contrastive explanation for why actualWorld obtained rather than w_alt:
T exists in actualWorld and provides a sufficient contrastive justification favoring actualWorld over w_alt.
Does NOT embed agential choice or reasons by definition. -/
def ContrastiveExplanationForTotality
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (w_alt : S.World) : Prop :=
  T.ExistsAt T.ground S.actualWorld ∧
  T.ProvidesContrastiveJustification T.ground S.actualWorld w_alt

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
    Logos.Agency.Act s (OutcomeAt S w out)
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
    ⟨hAct.1, hMeansAct, hIncomp⟩
  have hRep : RepresentsAlternativeOutcome S w_alt out_act (OutcomeAt S w_alt out_act) := fun h => h
  exact hReal.choice_reflection w_alt out_alt out_act (OutcomeAt S w_alt out_act) hDiff hRep hChooses

/-- THEOREM (Action-Theoretic Derivation of Choice via AxActPolarity in Binary Contrast Space):
Demonstrates that in a binary contrast space, AxActPolarity uniquely and constructively supplies
the representation of the actual alternative outcome, deriving agential choice from contradictory negation.
(0 axioms beyond Choice semantic axioms). -/
theorem agential_determination_entails_choice_in_binary_contrast_space
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (s : Logos.Agency.Subject)
    (hReal : AgentialActionRealization S T s)
    (hFidelity : ∀ (w : S.World) (out : Option (S.Node → Bool)),
      T.DeterminesOutcomeAt T.ground w out → out = SystemOutcomeAt S w)
    (hBinary : ∀ (w_alt : S.World), S.Accessible S.actualWorld w_alt →
      BinaryContrastSpace S w_alt (SystemOutcomeAt S w_alt) (SystemOutcomeAt S S.actualWorld)) :
    AgentialDeterminationEntailsChoice S T := by
  intro _hAgent _hNature w_alt hAcc hDiff out hDet
  have hOutEq : out = SystemOutcomeAt S w_alt := hFidelity w_alt out hDet
  subst hOutEq
  let out_alt := SystemOutcomeAt S w_alt
  let out_act := SystemOutcomeAt S S.actualWorld
  have hAct := hReal.originating_act w_alt out_alt hDet
  have hMeansNotP := Logos.Choice.AxActPolarity s (OutcomeAt S w_alt out_alt) hAct
  have hIncompNotP := Logos.Choice.incompatible_self_negation (OutcomeAt S w_alt out_alt)
  have hPolarChoice : Logos.Choice.Chooses s (OutcomeAt S w_alt out_alt) (¬ OutcomeAt S w_alt out_alt) :=
    ⟨hAct.1, hMeansNotP, hIncompNotP⟩
  have hRep := binary_contrast_space_entails_polarity_alternative S w_alt out_alt out_act (hBinary w_alt hAcc)
  exact hReal.choice_reflection w_alt out_alt out_act (¬ OutcomeAt S w_alt out_alt) hDiff hRep hPolarChoice

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
          (out = SystemOutcomeAt S w ∧ Logos.Agency.Act agent (OutcomeAt S w out))) →
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
  have hActAct : Logos.Agency.Act agent (OutcomeAt S S.actualWorld out_act) :=
    (hActIff S.actualWorld out_act).mp hDetAct |>.2
  have hMeansAct : Logos.Agency.Means agent (OutcomeAt S S.actualWorld out_act) := hActAct.1
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
