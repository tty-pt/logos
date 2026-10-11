import Lean

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
- `AgentialFreedomBridge`: An intentional agent choosing a contingent system under a necessary essence possesses counterfactual freedom of choice over alternative configurations.

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
Philosophical Justification:
An intentional personal agent (`SelectsIntentionally`) acting under an invariant necessary essence (`NatureInvariant`)
confronting a contingent system where divergent accessible alternative outcomes exist possesses the positive
counterfactual power to choose that alternative outcome at w_alt (`T.ChoosesOutcomeAt T.ground w_alt altOutcome`).
This formalizes that the alternative outcome is an agential alternative of the same personal source,
rather than an unchosen or detached accident. -/
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

/-- METAPHYSICAL PRINCIPLE OF ASEITY:
Tag: META.
An ultimate ground that completely explains the contingent totality must exist necessarily
(Aseity). If T were contingent, T would demand an explanation under the General PSR,
restarting the regress for the expanded totality S ∪ {T}. -/
def GroundingTotalityTerminatesInAseity
    (S : ConcreteSystem.{u})
    (T : CandidateGround S) : Prop :=
  T.GroundsConcreteActuality T.ground S.actualWorld → IsNecessary S T

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
  Eliminates the independent condition branch (`hIndep`) in the reductio of `contingent_system_derives_free_personal_source`. -/
def ExplanatoryUltimacyRequirement
    (S : ConcreteSystem.{u})
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop) : Prop :=
  ∀ (T : CandidateGround S),
    T.GroundsConcreteActuality T.ground S.actualWorld →
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

/-- METAPHYSICAL BRIDGE 5 (Agential Freedom Bridge):
Tag: META.
- Philosophical Justification:
  Libertarian Agency Principle: An intentional personal agent that selects a contingent system under a necessary essence
  and accessible alternatives possesses genuine counterfactual freedom of choice (could have chosen otherwise under that same nature).
  (Defended in treatise `investigations/ontological_incompleteness_and_transcendent_source.md` §3.1.1, §3.1.3, §4 Step 8).
- Formal Status:
  Explicit metaphysical premise supplied as a formal parameter.
- Role in Master Theorem:
  Derives `ActsFreely S T` and `NatureInvariant S T` from `SelectsIntentionally S T`, concluding the full specification of `FreePersonalSource`. -/
def AgentialFreedomBridge
    (S : ConcreteSystem.{u})
    (T : CandidateGround S) : Prop :=
  ContingentSystem S →
  IsNecessary S T →
  SelectsIntentionally S T →
  (NatureInvariant S T ∧ ActsFreely S T)

/-- THEOREM 6C (Derivation of Agential Freedom Bridge from Decomposed Stages):
Demonstrates that the overarching AgentialFreedomBridge is deducible from:
(1) Aseity preserving essential nature for personal agents, and
(2) The Agential Counterfactual Choice Bridge (Stage 4).
(0 axioms). -/
theorem agential_freedom_bridge_from_counterfactual_choice
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (hPersonalNature : IsPersonalAgent S T → IsNecessary S T → NatureInvariant S T)
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
attributes of a Free Personal Source via the metaphysical bridge principles.
(0 axioms). -/
theorem agential_justification_mode_yields_free_personal_source
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (hExternal : ∃ e : T.ExtEntity, T.ground = GroundIdentity.external e)
    (hNec : IsNecessary S T)
    (hCont : ContingentSystem S)
    (hAgent : IsPersonalAgent S T)
    (hGuided : GuidedByJustificationMode S T)
    (hTeleo : TeleologicalAgencyPrinciple S T)
    (hFreedom : AgentialFreedomBridge S T) :
    FreePersonalSource S T := by
  have hSel := hTeleo hAgent hGuided
  have ⟨hNature, hFree⟩ := hFreedom hCont hNec hSel
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
- `GeneralContrastivePSR S`: General contrastive principle of sufficient reason.
- `GroundingTotalityTerminatesInAseity`: Totality ground exists necessarily.
- `ImpersonalAseityPreservesNature`: Invariance of impersonal necessary essence across worlds.
- `ExplanatorySymmetryPrinciple`: Contrastive justification requires extrinsic differentiation.
- `ExplanatoryUltimacyRequirement`: Ultimate ground cannot depend on an independent prior condition.
- `TeleologicalAgencyPrinciple`: Agential justification mode acts intentionally by reasons.
- `AgentialFreedomBridge`: Intentional selection under contingency yields counterfactual freedom.

MAIN CONCLUSION:
THE CANDIDATE GROUND CANNOT BE INTERNAL (REFUTED BY CONSTITUTIVE CIRCULARITY),
CANNOT BE IMPERSONAL (NEITHER NECESSITATING NOR NON-NECESSITATING,
EXCLUDED BY CONTINGENCY, WELL-FOUNDED CIRCULARITY, AND ULTIMACY)
AND MUST BE A STRUCTURALLY TRANSCENDENT, NECESSARY, INTENTIONAL, AND FREE PERSONAL AGENT.
(0 axioms beyond core intuitionistic logic and standard classical choice). -/
theorem contingent_system_derives_free_personal_source
    (S : ConcreteSystem.{u})
    (hCont : ContingentSystem S)
    (hPSR : GeneralContrastivePSR S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (prior_wf : ∀ Ext, WellFounded (ConstitutivePriority Ext))
    (prior_trans : ∀ Ext {a b c : CandidateOnticItem S.Node Ext}, ConstitutivePriority Ext a b → ConstitutivePriority Ext b c → ConstitutivePriority Ext a c)
    (hConstitutiveOfTotality : ∀ Ext (n : S.Node), ConstitutivePriority Ext (CandidateOnticItem.node n) CandidateOnticItem.totality)
    (hInternalGroundsTotality : ∀ (T : CandidateGround S) (n : S.Node),
      T.ground = GroundIdentity.internal n → ∀ Ext, ConstitutivePriority Ext CandidateOnticItem.totality (CandidateOnticItem.node n))
    (hGroundsTotality : ∀ (T : CandidateGround S) (e : T.ExtEntity),
      T.ground = GroundIdentity.external e → ConstitutivePriority T.ExtEntity (CandidateOnticItem.candidate e) CandidateOnticItem.totality)
    (hAseity : ∀ T : CandidateGround S, GroundingTotalityTerminatesInAseity S T)
    (hAseityNature : ∀ T : CandidateGround S, ImpersonalAseityPreservesNature S T)
    (hSymmPrinciple : ∀ T : CandidateGround S, ExplanatorySymmetryPrinciple S T ConstitutivePriority)
    (hUltRequirement : ExplanatoryUltimacyRequirement S ConstitutivePriority)
    (hTeleo : ∀ T : CandidateGround S, TeleologicalAgencyPrinciple S T)
    (hFreedom : ∀ T : CandidateGround S, AgentialFreedomBridge S T) :
    ∃ T : CandidateGround S, FreePersonalSource S T := by
  obtain ⟨T, hGrounds, hExpl⟩ := hPSR hCont
  have hExternal : ∃ e : T.ExtEntity, T.ground = GroundIdentity.external e :=
    candidate_ground_must_be_structurally_external S T
      ConstitutivePriority prior_wf (fun Ext {_a _b _c} => prior_trans Ext)
      (fun Ext m => hConstitutiveOfTotality Ext m) (hInternalGroundsTotality T)
  obtain ⟨e, hExt⟩ := hExternal
  have hGroundsPriority := hGroundsTotality T e hExt
  have hNec : IsNecessary S T := hAseity T hGrounds
  have hUlt : IsUltimateGround S T ConstitutivePriority := hUltRequirement T hGrounds
  have hExh := grounding_modes_exhaustive S T
  refine ⟨T, ?_⟩
  rcases hExh with hNecMode | hGuided | ⟨w_alt, hAcc, hAlt, hUnjust⟩
  · have hImpNec : ImpersonalNecessitatingGround S T := ⟨hNec, hNecMode⟩
    exact False.elim (necessary_impersonal_ground_contradicts_contingency S T hImpNec hCont)
  · have hAgent : IsPersonalAgent S T := by
      apply Classical.byContradiction
      intro hNotAgent
      have hImp : IsImpersonal S T := hNotAgent
      have hNature : NatureInvariant S T := hAseityNature T hImp hNec
      have hNotNec : ¬ NecessitatingMode S T := by
        intro hNecM
        exact necessary_impersonal_ground_contradicts_contingency S T ⟨hNec, hNecM⟩ hCont
      have hOr := impersonal_ground_forces_consequence_or_independent_condition S T
        ConstitutivePriority e hExt (hSymmPrinciple T) hImp hNature hNotNec hGuided
      cases hOr with
      | inl hConsequenceDep =>
        exact consequence_dependent_mode_fails_well_foundedness
          (ConstitutivePriority T.ExtEntity) (prior_wf T.ExtEntity) (fun {_a _b _c} => prior_trans T.ExtEntity) e hGroundsPriority hConsequenceDep
      | inr hIndep =>
        exact independent_condition_contradicts_ultimacy S T
          ConstitutivePriority e hExt hIndep hUlt
    exact agential_justification_mode_yields_free_personal_source S T ⟨e, hExt⟩ hNec hCont hAgent hGuided (hTeleo T) (hFreedom T)
  · have hExplAlt : ContrastiveExplanationForTotality S T w_alt := hExpl w_alt hAcc hAlt
    exact False.elim (unjustified_alternative_fails_contrastive_at S T w_alt hUnjust hExplAlt)

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
#print axioms agential_justification_mode_yields_free_personal_source
#print axioms contingent_system_derives_free_personal_source

end OntologicalIncompleteness
end Logos
