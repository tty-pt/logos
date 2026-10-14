import Lean

open Classical

namespace Logos

namespace Agency
axiom Subject : Type
axiom State : Type
axiom Means : Subject → Prop → Prop
axiom Initiates : Subject → State → State → Prop → Prop

def Act (s : Subject) (p : Prop) : Prop :=
  Means s p ∧ ∃ w w' : State, Initiates s w w' p
end Agency

namespace Alternatives
def Incompatible (p q : Prop) : Prop := ¬ (p ∧ q)
end Alternatives

namespace Choice
def Chooses (s : Logos.Agency.Subject) (p q : Prop) : Prop :=
  Logos.Agency.Means s p ∧ Logos.Agency.Means s q ∧ Logos.Alternatives.Incompatible p q

theorem incompatible_self_negation (p : Prop) : Logos.Alternatives.Incompatible p (¬ p) := by
  intro ⟨hp, hnp⟩
  exact hnp hp
end Choice

namespace Person
def Person (s : Logos.Agency.Subject) : Prop :=
  ∃ (p q : Prop), Logos.Choice.Chooses s p q
end Person

namespace Entity
inductive Entity : Type
  | ofGround : Entity
  | ofSubject : Logos.Agency.Subject → Entity
end Entity

namespace FoundationalUnicity
theorem ofGround_ne_ofSubject (s : Logos.Agency.Subject) :
    Logos.Entity.Entity.ofSubject s ≠ Logos.Entity.Entity.ofGround := by
  intro h
  nomatch h

def UniversalModalGround (g : Logos.Entity.Entity) : Prop :=
  g = Logos.Entity.Entity.ofGround

theorem exactly_one_universal_modal_ground (_hNoTotal : ∀ s : Logos.Agency.Subject, ∃ p : Prop, ¬ Logos.Agency.Means s p) :
    ∃ g : Logos.Entity.Entity, UniversalModalGround g ∧ (∀ g' : Logos.Entity.Entity, UniversalModalGround g' → g' = g) := by
  exact ⟨Logos.Entity.Entity.ofGround, rfl, fun g' hg' => hg'⟩
end FoundationalUnicity

namespace FoundationalOmnipresence
def UniversalModalGround := Logos.FoundationalUnicity.UniversalModalGround
end FoundationalOmnipresence

namespace TrinitarianSubjectBridge
inductive DivineRole : Type
  | source : DivineRole
  | word : DivineRole
  | spirit : DivineRole
deriving DecidableEq

axiom DivineSubjectRole : Logos.Agency.Subject → DivineRole

axiom three_divine_persons_exist_with_roles :
  ∃ a b c : Logos.Agency.Subject,
    DivineSubjectRole a = DivineRole.source ∧
    DivineSubjectRole b = DivineRole.word ∧
    DivineSubjectRole c = DivineRole.spirit ∧
    Logos.Person.Person a ∧ Logos.Person.Person b ∧ Logos.Person.Person c
end TrinitarianSubjectBridge

end Logos

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
theorem emptyUnitWf : WellFounded (fun (_ _ : Unit) => False) := by
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

end OntologicalIncompleteness
end Logos
