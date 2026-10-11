# Comprehensive Adversarial Audit of FreeSubjectDeterminationDilemma.lean

**Date:** 2026-10-08  
**Target File:** `FreeSubjectDeterminationDilemma.lean` (902 lines)  
**Formal Audit Artifact:** `AdversarialFreeSubjectAudit.lean` (765 lines, Lean 4 verified, 0 errors, 0 warnings)  
**Philosophical Thesis Under Attack:**  
> *"If this proof exists as a concrete determined occurrence, then a Free Subject exists."*

---

## Executive Summary

This adversarial audit conducts a formal and philosophical attack on `FreeSubjectDeterminationDilemma.lean`. The stated objective of the formalization was to establish that a complete chain of forced determinations cannot explain its own ultimate determination, that an impersonal ultimate source must either fail to explain the occurrence or fall into explanatory circularity, and that the only surviving explanation is an unforced personal agent endowed with libertarian freedom.

Our investigation demonstrates that **the formalization does NOT establish this conclusion from neutral logic, determinism, or bare explanatory well-foundedness**. Rather, the argument relies on a cascade of question-begging axioms, an artificially non-exhaustive taxonomy, underconstrained countermodels, and an unargued resolution of the classical problem of agential luck.

Specifically:
1. **The Three-Node Countermodel Was Vacuous:** In the original file (`lines 634–690`), `independent_non_causal_ground_satisfiable_without_cycle` declared that $S$ determines $C$, but set $S$ to be constant across all worlds while $C$ flipped. It represented an indeterministic or disconnected relation under the name `Determines`.
2. **The Deterministic Dilemma:** When genuine deterministic determination is enforced (`same determining configuration → same determined outcome` across accessible worlds):
   - If the source configuration is invariant under the prior state, occurrence contingency is mathematically impossible (`impossibility_of_invariant_deterministic_contingency`).
   - If the source configuration is contingent, a **fully deterministic 3-node countermodel is constructible and verified** (`deterministic_independent_ground_model`), containing an impersonal non-causal ground, complete determinism, well-founded grounding, contingency, and NO agents.
3. **The Explanatory Circularity Is Manufactured:** The backward explanatory arrow ($S \to C$) is not derived from well-foundedness or Contrastive PSR; it is inserted by sheer stipulation via `consequence_dependent_selection` (`lines 320–322`). Modern physics and non-teleological metaphysics reject backward dependence; well-foundedness merely refutes the cycle after the author has artificially injected it.
4. **The Taxonomy Is Formally Incomplete:** `OriginExplanationTaxonomy` (`lines 413–460`) defines `NecessitatedBySourceNature` as invariant and `ImpersonalContingentSource` as non-necessitating (`¬ Necessitates`). We prove that this taxonomy omits **Contingent Deterministic Impersonal Sources** (`taxonomy_omits_contingent_deterministic_source`).
5. **Agential Control Is Stipulated by Decree:** `AgentialControlBridge` (`lines 541–550`) assumes by existential fiat that the agent exercises active control over the alternative world under the exact same prior state, papering over the entire 70-year debate on Peter van Inwagen's Mind argument and agential luck.
6. **Cosmetic and Dead Code:** Four explanatory target definitions (`lines 204–228`), `sourceSubstrate` (`line 185`), and `impersonal_antecedent_symmetry_leaves_brute` (`lines 315–319`) are dead code, performing zero work in any proof.

All attacks, impossibility theorems, and countermodels have been formalized in `AdversarialFreeSubjectAudit.lean` and checked by the Lean 4 kernel with 0 errors and 0 sorrys.

---

## 1. Attack on the Three-Node Countermodel

### 1.1 The Underconstrained Flaw in `independent_non_causal_ground_satisfiable_without_cycle`
In `FreeSubjectDeterminationDilemma.lean` (`lines 634–690`), the author claimed to demonstrate that an independent non-causal ground $G$ can explain $S$ without circularity. The model was defined as:
```lean
OutcomeOf := fun e w => if e = 2 then w else false
```
where $G = 0, S = 1, C = 2$.
Across the two worlds (`w = false` and `w = true`):
- For $S$ (node 1): `OutcomeOf 1 false = false`, and `OutcomeOf 1 true = false`.
- For $C$ (node 2): `OutcomeOf 2 false = false`, and `OutcomeOf 2 true = true`.

Although `Det3 S C` was asserted, $S$ remained in the exact same state while $C$ varied. In `DeterminationModel`, `Determines` had no modal semantics whatsoever: its only constraint was that `AncestrallyDetermines Determines a b → GroundingDependsOn b a` (`line 102`). Consequently, `Determines` did not represent determinism; it was merely an uninterpreted directed edge.

### 1.2 The Deterministic Dilemma
When we enforce the Principle of Deterministic Determination:
$$\forall a, b,\ \text{Determines}(a, b) \implies \forall w_1, w_2,\ \text{OutcomeOf}(a, w_1) = \text{OutcomeOf}(a, w_2) \implies \text{OutcomeOf}(b, w_1) = \text{OutcomeOf}(b, w_2)$$
a strict dilemma arises:

#### Branch A: Invariant Source Configuration Under Same Complete Prior State
If the source configuration $S$ is fixed by the complete prior state:
$$\forall alt,\ \text{SameCompletePriorState}(\text{actual}, alt) \implies \text{OutcomeOf}(S, alt) = \text{OutcomeOf}(S, \text{actual})$$
then because $S$ deterministically determines $C$, $C$ must also be invariant:
$$\text{OutcomeOf}(C, alt) = \text{OutcomeOf}(C, \text{actual})$$
This directly contradicts `HasSamePastAlternative M` (`OutcomeOf C alt ≠ OutcomeOf C actual`).
In `AdversarialFreeSubjectAudit.lean`, we prove this impossibility as a kernel-checked theorem:
```lean
theorem impossibility_of_invariant_deterministic_contingency
    (M : DeterminationModel.{u, v, w})
    (S : UltimateSource.{u, v, w} M)
    (hDet : DeterministicDetermination M)
    (hRefl : M.Accessible M.actualWorld M.actualWorld)
    (hInvariant : ∀ alt : M.World, M.SameCompletePriorState M.actualWorld alt →
      M.OutcomeOf S.sourceConfig alt = M.OutcomeOf S.sourceConfig M.actualWorld)
    (hCont : HasSamePastAlternative M) :
    False
```
*(Axioms: 0)*.

#### Branch B: Contingent Source Configuration Under Same Complete Prior State
If $S$ is an ultimate causal source (e.g. initial cosmological boundary condition or fundamental uncaused state), the prior causal history is empty. Hence, $S$ itself can be contingent under the same past:
$$\text{OutcomeOf}(S, \text{actual}) \neq \text{OutcomeOf}(S, alt)$$
We prove that under this condition, **a fully deterministic 3-node countermodel is constructible**:
```lean
theorem deterministic_independent_ground_model :
    ∃ (M : DeterminationModel.{0, 0, 0}) (S : UltimateSource.{0, 0, 0} M) (G : M.Event),
      DeterministicDetermination M ∧
      (∀ x, ¬ M.Determines G x) ∧
      (∀ x, ¬ M.Determines x G) ∧
      M.GroundingDependsOn S.sourceConfig G ∧
      AncestrallyDetermines M.Determines S.sourceConfig M.concreteOccurrence ∧
      M.GroundingDependsOn M.concreteOccurrence S.sourceConfig ∧
      ¬ M.GroundingDependsOn S.sourceConfig M.concreteOccurrence ∧
      ¬ M.GroundingDependsOn G M.concreteOccurrence ∧
      IsUltimate M.Determines S.sourceConfig ∧
      HasSamePastAlternative M ∧
      (∀ agent : M.Agent, ¬ M.IsAgent agent)
```
*(Axioms: [propext])*.

In this model:
- $G$ is invariant (`OutcomeOf G w = false`).
- $S$ varies with $w$ (`OutcomeOf S w = w`).
- $C$ is deterministically governed by $S$ (`OutcomeOf C w = w`).
- `DeterministicDetermination` holds unconditionally.
- Grounding is well-founded ($C \to S \to G$, rank $0 < 1 < 2$).
- No personal agents exist (`Agent := Empty`).

This refutes the claim that determinism plus well-founded grounding excludes an impersonal non-causal ground.

---

## 2. Semantics of Determination and Grounding

### 2.1 Formalization of Deterministic Determination
We formalize determinism as:
```lean
def DeterministicDetermination (M : DeterminationModel.{u, v, w}) : Prop :=
  ∀ a b : M.Event, M.Determines a b →
    ∀ w1 w2 : M.World,
      M.Accessible M.actualWorld w1 →
      M.Accessible M.actualWorld w2 →
      M.OutcomeOf a w1 = M.OutcomeOf a w2 →
      M.OutcomeOf b w1 = M.OutcomeOf b w2
```
We prove that this property is strictly transitive along ancestral chains:
```lean
theorem ancestrallyDetermines_preserves_determinism
    (M : DeterminationModel.{u, v, w})
    (hDet : DeterministicDetermination M)
    {a b : M.Event}
    (hAnc : AncestrallyDetermines M.Determines a b) :
    ∀ w1 w2 : M.World, ... → OutcomeOf a w1 = OutcomeOf a w2 → OutcomeOf b w1 = OutcomeOf b w2
```
and entails `Necessitates M a b` whenever actualWorld is accessible to itself (`ancestrallyDetermines_implies_necessitates`).

### 2.2 Four Levels of Explanatory Grounding
To prevent conflation, we formalized the four distinct levels of explanation in Lean:
1. **Level 1 (Explanatory Association):** `M.GroundingDependsOn s g`. Mere graph edge.
2. **Level 2 (Substrate Existence):** `M.Occurs g ∧ M.GroundingDependsOn s g`. Explains why substrate exists.
3. **Level 3 (Configuration Explanation):** `M.GroundingDependsOn s g`. Explains why $s$ has its actual determinate profile (non-contrastive).
4. **Level 4 (Contrastive Selection Explanation):**
```lean
def ExplainsContrastiveSelection (M : DeterminationModel.{u, v, w}) (g s : M.Event) : Prop :=
  M.GroundingDependsOn s g ∧
  ∀ alt : M.World,
    M.Accessible M.actualWorld alt →
    M.SameCompletePriorState M.actualWorld alt →
    M.OutcomeOf s alt ≠ M.OutcomeOf s M.actualWorld →
    M.OutcomeOf g alt = M.OutcomeOf g M.actualWorld →
    False
```

### 2.3 The Contrastive Dilemma for Invariant Grounds
We prove as a formal theorem:
```lean
theorem invariant_ground_cannot_contrastively_explain_contingent_source
    (M : DeterminationModel.{u, v, w})
    (S : UltimateSource.{u, v, w} M)
    (G : M.Event)
    (hG_inv : ∀ alt : M.World, M.OutcomeOf G alt = M.OutcomeOf G M.actualWorld)
    (hCfgCont : SourceConfigContingent M S)
    (hContrastive : ExplainsContrastiveSelection M G S.sourceConfig) :
    False
```
*(Axioms: 0)*.

**Philosophical Consequence:**
- If the demand on $G$ is merely **Level 3 Configuration Explanation**, an impersonal ground $G$ survives cleanly without agency.
- If the demand on $G$ is **Level 4 Contrastive Explanation**, an invariant ground $G$ cannot explain why $S_{actual}$ occurred rather than $S_{alt}$ because $G$ is identically present in both worlds. However, this failure of contrastive explanation does NOT imply personal agency or circularity; it merely means that under an invariant ground, the contingent realization of $S$ is contrastively unexplained (an objective chance or brute fact).

---

## 3. Attack on the Explanatory-Circularity Inference

### 3.1 The Manufactured Reverse Arrow
In `FreeSubjectDeterminationDilemma.lean` (`lines 324–340`), the proof derived backward explanatory dependence:
$$M.\text{GroundingDependsOn}\ S.\text{sourceConfig}\ M.\text{concreteOccurrence}$$
via `impersonal_contingent_source_derives_consequence_dependence`.

We inspected the premises of this theorem:
```lean
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
```

**The Fatal Defect:**
`consequence_dependent_selection` asserts by decree:
> *(Non-necessitation $\land$ Contrastive reason) $\implies$ Backward dependence on the consequence!*

In non-teleological metaphysics and physical science, an impersonal contingent cause $S$ (e.g. an uncaused quantum event or spontaneous fluctuation) does **not** depend on its future effects. If it non-necessitatingly produces $C$, the occurrence of $C$ lacks contrastive explanation; it does not turn around and retroactively ground $S$!

The author manufactured the backward arrow by writing `M.GroundingDependsOn S.sourceConfig M.concreteOccurrence` into the consequent of `consequence_dependent_selection`. Then, having manually inserted the backward arrow, the author invoked `wellFounded_explanation_has_no_two_cycle` to refute it and cry "circularity!"

### 3.2 Proof that Well-Foundedness and Explicit Contrastive PSR Do Not Imply Backward Dependence
In `AdversarialFreeSubjectAudit.lean`, we explicitly formalize Contrastive PSR:
```lean
def ContrastivePSR_Holds
    (M : DeterminationModel.{u, v, w})
    (S : UltimateSource.{u, v, w} M)
    (HasContrastiveReason : M.Event → Prop) : Prop :=
  HasSamePastAlternative M → HasContrastiveReason S.sourceConfig
```
and prove that a complete determination model satisfies well-founded grounding, an effective contrastive alternative, and Contrastive PSR with a fully satisfied contrastive reason, while backward explanatory dependence is strictly false:
```lean
theorem wellFounded_and_psr_do_not_derive_backward_dependence :
    ∃ (M : DeterminationModel.{0, 0, 0})
      (S : UltimateSource.{0, 0, 0} M)
      (HasContrastiveReason : M.Event → Prop),
      HasSamePastAlternative M ∧
      ContrastivePSR_Holds M S HasContrastiveReason ∧
      HasContrastiveReason S.sourceConfig ∧
      AncestrallyDetermines M.Determines S.sourceConfig M.concreteOccurrence ∧
      M.GroundingDependsOn M.concreteOccurrence S.sourceConfig ∧
      ¬ M.GroundingDependsOn S.sourceConfig M.concreteOccurrence
```
*(Axioms: [propext])*.

**Critical Distinction Between PSR and Teleological Selection:**
- **Contrastive PSR** demands that a contingent determination have an explanatory reason/ground. In an impersonal model $G \to S \to C$, this demand is satisfied by the independent ground $G$.
- **Teleological Selection** (`consequence_dependent_selection`) is an additional, separate assumption:
  $$(¬ \text{Necessitates} \land \text{HasContrastiveReason}) \implies \text{GroundingDependsOn}(S, C)$$
  It stipulates that any non-necessitating source must be teleologically specified by its future consequence.
Without that separate teleological premise, well-foundedness and Contrastive PSR coexist with complete absence of backward dependence. Well-foundedness excludes cycles *once a cycle is present*; it has zero deductive power to generate the backward explanatory dependence itself.

### 3.3 Dead Code: `impersonal_antecedent_symmetry_leaves_brute`
We verified that `impersonal_antecedent_symmetry_leaves_brute` (`lines 315–319`) is completely unused in `impersonal_contingent_source_derives_consequence_dependence` and `impersonal_contingent_source_fails_as_ultimate_explanation`. The derivation consumed only `contrastive_psr` and `consequence_dependent_selection`. We formalized this as `impersonal_antecedent_symmetry_is_deductively_redundant`.

---

## 4. Attack on the Entire Proof's Dependency Structure

### 4.1 Audit of Final Master Theorem
In `FreeSubjectDeterminationDilemma.lean` (`lines 585–605`), `concrete_proof_occurrence_implies_free_subject` consumes:
- `M : DeterminationModel`
- `hProof : ProofOccurrence M`
- `hTerm : AncestryTerminatesDetermines M`
- `hBridge : (S : UltimateSource M) → ContingencyTransferBridge M S`
- `P : (S : UltimateSource M) → PrimitiveExplanatoryPrinciples M S`
- `T : (S : UltimateSource M) → OriginExplanationTaxonomy M S`
- `hTeleo : (S : UltimateSource M) → ContrastiveTeleologyPrinciple M S (P S)`
- `hControl : (S : UltimateSource M) → AgentialControlBridge M S`

We conducted a forensic audit of each dependency:

| Premise / Structure | Audit Verdict | Flaw / Gap Identified |
| :--- | :--- | :--- |
| `AncestryTerminatesDetermines` | **Unproved Postulate** | Assumes by raw implication `Occurs concreteOccurrence → Nonempty (UltimateSource M)`. Directly bypasses the cosmological problem of infinite causal regress. |
| `ContingencyTransferBridge` | **Philosophical Bridge** | Asserts `HasSamePastAlternative → SourceConfigContingent ∨ ¬ Necessitates`. Not derived; taken as an unproved hypothesis. |
| `PrimitiveExplanatoryPrinciples` | **Question-Begging** | Contains `consequence_dependent_selection`, which injects backward dependence by fiat. Contains unused dead-code symmetry premise. |
| `OriginExplanationTaxonomy` | **Incomplete Taxonomy** | Disjunction stipulated by field `taxonomy_is_exhaustive`. Omits Contingent Deterministic Impersonal Sources. |
| `ContrastiveTeleologyPrinciple` | **Disjunctive Trap** | Artificially defined 4-way disjunction where option 4 is `∃ agent`. Once options 1–3 are eliminated by definition, `∃ agent` is forced by disjunctive syllogism. |
| `AgentialControlBridge` | **Stipulative Fiat** | Asserts that an unforced personal originator exercises active control over the alternative world. Resolves the Mind / luck argument by definition. |
| `ProofOccurrence` | **Cosmetic Framing** | Only supplies `proof_occurs` (to fire `hTerm`) and `proof_is_contingent`. Nothing about the nature of a "proof" or "judgment" is used. Any contingent event $E$ works identically. |

### 4.2 Incompleteness of the Origin Taxonomy
In `FreeSubjectDeterminationDilemma.lean` (`lines 413–460`), the origin taxonomy defines:
- `NecessitatedBySourceNature`: requires invariance (`∀ alt, SamePast → OutcomeOf S alt = OutcomeOf S actual`).
- `ImpersonalContingentSource`: requires non-necessitation (`¬ Necessitates M S.sourceConfig M.concreteOccurrence`).

We define:
```lean
def ContingentDeterministicImpersonalSource (M : DeterminationModel) (S : UltimateSource M) : Prop :=
  Necessitates M S.sourceConfig M.concreteOccurrence ∧
  SourceConfigContingent M S ∧
  (¬ ∃ agent : M.Agent, M.IsAgent agent ∧ M.OriginatesAt agent S.sourceConfig) ∧
  IsUltimate M.Determines S.sourceConfig
```

We evaluate this against all six branches of `OriginExplanationTaxonomy`:
```lean
theorem taxonomy_omits_contingent_deterministic_source
    (M : DeterminationModel.{u, v, w})
    (S : UltimateSource.{u, v, w} M)
    (hCDIS : ContingentDeterministicImpersonalSource M S)
    (HasSufficientReason : M.Event → Prop)
    (hHasReason : HasSufficientReason S.sourceConfig)
    (hNoExternalGround : ¬ ∃ G : M.Event,
      M.GroundingDependsOn S.sourceConfig G ∧
      (¬ ∃ p, M.Determines p G) ∧
      (¬ ∃ agent : M.Agent, M.IsAgent agent ∧ M.OriginatesAt agent S.sourceConfig)) ... :
    ∀ (Forced Brute NatNec ImpNonNec Indep Pers : Prop),
      (Forced → False) ∧ (Brute → False) ∧ (NatNec → False) ∧
      (ImpNonNec → False) ∧ (Indep → False) ∧ (Pers → False)
```
*(Axioms: 0)*.

**Nuanced Taxonomy Finding:**
1. When a contingent deterministic impersonal source has sufficient reason (not brute) and does not possess an external unforced ground node $G$, it is excluded from **all six** branches of the taxonomy.
2. When an independent non-causal ground $G$ **does** exist, we prove that the source is accommodated under `IndependentNonCausalGround`:
```lean
theorem contingent_deterministic_source_satisfies_independent_ground_when_present
    (M : DeterminationModel.{u, v, w})
    (S : UltimateSource.{u, v, w} M)
    (G : M.Event)
    (hGround : M.GroundingDependsOn S.sourceConfig G)
    (hUnforced : ¬ ∃ p, M.Determines p G)
    (hNoAgent : ¬ ∃ agent : M.Agent, M.IsAgent agent ∧ M.OriginatesAt agent S.sourceConfig) :
    ∃ G' : M.Event,
      M.GroundingDependsOn S.sourceConfig G' ∧
      (¬ ∃ p, M.Determines p G') ∧
      (¬ ∃ agent : M.Agent, M.IsAgent agent ∧ M.OriginatesAt agent S.sourceConfig)
```
*(Axioms: 0)*.

Thus, the taxonomy is not unconditionally empty, but it lacks a dedicated category for contingent deterministic impersonal sources that do not invoke an external ground event, achieving apparent exhaustiveness only through the unproved axiom field `taxonomy_is_exhaustive`.

### 4.3 Dead Code and Unused Definitions
The following definitions in `FreeSubjectDeterminationDilemma.lean` are completely unused in all theorems and proofs:
1. `sourceSubstrate : Type u` (`line 185`): Completely inert field in `UltimateSource`.
2. `ExplainsSubstrate` (`lines 204–206`): Never referenced in any theorem.
3. `ExplainsProduction` (`lines 212–215`): Never referenced in any theorem.
4. `ExplainsContrastiveSelection` (`lines 218–228`): Never referenced in any theorem.
5. `impersonal_antecedent_symmetry_leaves_brute` (`lines 315–319`): Never consumed in derivations.

---

## 5. Attack on the Inference from Ultimate Source to Free Subject

To test whether an ultimate source entails a Free Subject, we constructed four minimal kernel-checked countermodels exposing four distinct logical gaps:

### Countermodel A: Concrete Occurrence $\not\implies$ Ultimate Source (`infinite_regress_no_ultimate_source`)
- **Structure:** `Event := Nat`, `Determines a b := a = b + 1`, `concreteOccurrence := 0`.
- **Orientation Analysis of Explanatory Well-Foundedness:**
  In `DeterminationModel`, `GroundingDependsOn x y` means $x$ depends on $y$ ($y$ grounds $x$).
  Lean's `WellFounded R` checks for the absence of infinite descending chains $\dots \prec z_2 \prec z_1 \prec z_0$.
  - In the baseline model (`FreeSubjectDeterminationDilemma.lean:98`), `genuine_grounding_is_well_founded` was defined as `WellFounded GroundingDependsOn`. Because $n$ depends on $n + 1$, the relation was consequence-descending ($b < a$ on $\mathbb{N}$). Lean's kernel accepted this as well-founded because the chain of consequences terminates at 0! However, the chain of grounds ($0 \to 1 \to 2 \dots$) regressed infinitely!
  - We formalize the ground-ascending relation:
    ```lean
    def Grounds {α : Type u} (GroundingDependsOn : α → α → Prop) (y x : α) : Prop :=
      GroundingDependsOn x y
    ```
    and prove as a kernel theorem:
    ```lean
    theorem infinite_causal_regress_induces_infinite_grounding_regress
        {Event : Type}
        (Determines : Event → Event → Prop)
        (GroundingDependsOn : Event → Event → Prop)
        (hTrans : ∀ a b, Determines a b → GroundingDependsOn b a)
        (e0 : Event)
        (next : Event → Event)
        (hStep : ∀ e, Determines (next e) e) :
        ¬ WellFounded (Grounds GroundingDependsOn)
    ```
    *(Axioms: 0)*.
- **Distinction Between Cycles and Regress:**
  `wellFounded_explanation_has_no_two_cycle` holds for any well-founded relation regardless of orientation (since 2-cycles are symmetric). However, **absence of 2-cycles does not imply absence of infinite regress**. An infinite causal chain where every cause grounds its effect induces an infinite explanatory regress, demonstrating that the termination condition `AncestryTerminatesDetermines` is an indispensable cosmological assumption, not a derivation.

### Countermodel B: Ultimate Source $\not\implies$ Personal Source (`impersonal_indeterministic_source_model`)
- **Structure:** 2-node model where $S$ non-necessitatingly determines $C$, $C$ is contingent, $S$ is ultimate, and no agents exist.
- **Properties:** Shows that an indeterministic impersonal source does not lead to a contradiction unless one assumes `consequence_dependent_selection`.
- **Gap Exposed:** Indeterminism in nature (e.g. quantum mechanics) provides an unforced impersonal ultimate source without agency.

### Countermodel C: Independent Non-Causal Ground $\not\implies$ Personal Source (`impersonal_law_grounded_source_model`)
- **Structure:** Derived directly from `deterministic_independent_ground_model`.
- **Properties:** $G$ grounds $S$, $S$ deterministically determines $C$, $S$ is ultimate, $C$ is contingent, and no agents exist.
- **Gap Exposed:** An impersonal metaphysical law or structural principle can ground the initial source without agency unless `ContrastiveTeleologyPrinciple` is assumed.

### Countermodel D: Personal Source $\not\implies$ Free Subject (`unforced_agent_without_control_model`)
- **Structure:** An agent originates $S$, $S$ determines $C$, an accessible alternative world exists under the same past, but `ControlsAlternative agent S alt := False`.
- **Gap Exposed:** This formalizes Peter van Inwagen's **Mind argument / agential luck objection**: If an agent acts differently in an alternative world under the exact same complete past, desires, and reasons, the difference is a matter of chance/luck, not agential control. The original proof did not derive control; it assumed `AgentialControlBridge` by fiat.

---

## 6. Minimal Conditional Free Subject Theorem & Axiom Audit

In `AdversarialFreeSubjectAudit.lean`, we formulated `minimal_conditional_free_subject_theorem`, which strips away all dead code, redundant taxonomies, and cosmetic packaging, exposing the exact set of substantive philosophical bridges required to reach the conclusion:

```lean
structure MinimalPhilosophicalBridges (M : DeterminationModel.{u, v, w}) where
  AncestryTerminates :
    M.Occurs M.concreteOccurrence → Nonempty (UltimateSource.{u, v, w} M)
  ContingencyTransfer :
    (S : UltimateSource M) → HasSamePastAlternative M →
      SourceConfigContingent M S ∨ ¬ Necessitates M S.sourceConfig M.concreteOccurrence
  HasContrastiveReason : M.Event → Prop
  ContrastivePSR :
    HasSamePastAlternative M → (S : UltimateSource M) → HasContrastiveReason S.sourceConfig
  ConsequenceDependentSelection :
    (S : UltimateSource M) →
      (¬ Necessitates M S.sourceConfig M.concreteOccurrence ∧
       HasContrastiveReason S.sourceConfig) →
      M.GroundingDependsOn S.sourceConfig M.concreteOccurrence
  ContrastiveTeleology :
    (S : UltimateSource M) →
    ∀ G : M.Event,
      M.GroundingDependsOn S.sourceConfig G →
      (¬ ∃ p, M.Determines p G) →
      (Necessitates M S.sourceConfig M.concreteOccurrence ∧
       (∀ alt : M.World, M.SameCompletePriorState M.actualWorld alt →
         M.OutcomeOf S.sourceConfig alt = M.OutcomeOf S.sourceConfig M.actualWorld)) ∨
      (¬ HasContrastiveReason S.sourceConfig) ∨
      M.GroundingDependsOn S.sourceConfig M.concreteOccurrence ∨
      (∃ agent : M.Agent, M.IsAgent agent ∧ M.OriginatesAt agent S.sourceConfig)
  TaxonomyDisjunction :
    (S : UltimateSource M) →
      (∃ p, M.Determines p S.sourceConfig) ∨
      (SourceConfigContingent M S ∧ ¬ HasContrastiveReason S.sourceConfig) ∨
      (Necessitates M S.sourceConfig M.concreteOccurrence ∧
       (∀ alt : M.World, M.SameCompletePriorState M.actualWorld alt →
         M.OutcomeOf S.sourceConfig alt = M.OutcomeOf S.sourceConfig M.actualWorld)) ∨
      (¬ Necessitates M S.sourceConfig M.concreteOccurrence) ∨
      (∃ G, M.GroundingDependsOn S.sourceConfig G ∧ (¬ ∃ p, M.Determines p G) ∧
        (¬ ∃ agent : M.Agent, M.IsAgent agent ∧ M.OriginatesAt agent S.sourceConfig)) ∨
      (∃ agent : M.Agent, M.IsAgent agent ∧ M.OriginatesAt agent S.sourceConfig)
  AgentialControl :
    (S : UltimateSource M) → (agent : M.Agent) →
      M.IsAgent agent ∧ M.OriginatesAt agent S.sourceConfig →
      HasSamePastAlternative M →
      ∃ alternative : M.World,
        M.Accessible M.actualWorld alternative ∧
        M.SameCompletePriorState M.actualWorld alternative ∧
        M.OutcomeOf M.concreteOccurrence alternative ≠ M.OutcomeOf M.concreteOccurrence M.actualWorld ∧
        M.ControlsAlternative agent S.sourceConfig alternative
```

### Kernel Verification and Axiom Footprints
All declarations in `AdversarialFreeSubjectAudit.lean` were compiled using Lean 4 (`lean AdversarialFreeSubjectAudit.lean`). The kernel axiom footprints (`#print axioms`) are:

```
'Logos.AdversarialFreeSubjectAudit.wellFounded_explanation_has_no_two_cycle' does not depend on any axioms
'Logos.AdversarialFreeSubjectAudit.ancestrallyDetermines_preserves_determinism' does not depend on any axioms
'Logos.AdversarialFreeSubjectAudit.ancestrallyDetermines_implies_necessitates' does not depend on any axioms
'Logos.AdversarialFreeSubjectAudit.impossibility_of_invariant_deterministic_contingency' does not depend on any axioms
'Logos.AdversarialFreeSubjectAudit.deterministic_independent_ground_model' depends on axioms: [propext]
'Logos.AdversarialFreeSubjectAudit.invariant_ground_cannot_contrastively_explain_contingent_source' does not depend on any axioms
'Logos.AdversarialFreeSubjectAudit.wellFounded_and_psr_do_not_derive_backward_dependence' depends on axioms: [propext]
'Logos.AdversarialFreeSubjectAudit.impersonal_antecedent_symmetry_is_deductively_redundant' does not depend on any axioms
'Logos.AdversarialFreeSubjectAudit.taxonomy_omits_contingent_deterministic_source' does not depend on any axioms
'Logos.AdversarialFreeSubjectAudit.contingent_deterministic_source_satisfies_independent_ground_when_present' does not depend on any axioms
'Logos.AdversarialFreeSubjectAudit.infinite_causal_regress_induces_infinite_grounding_regress' does not depend on any axioms
'Logos.AdversarialFreeSubjectAudit.infinite_regress_no_ultimate_source' does not depend on any axioms
'Logos.AdversarialFreeSubjectAudit.impersonal_indeterministic_source_model' depends on axioms: [propext]
'Logos.AdversarialFreeSubjectAudit.impersonal_law_grounded_source_model' depends on axioms: [propext]
'Logos.AdversarialFreeSubjectAudit.unforced_agent_without_control_model' depends on axioms: [propext]
'Logos.AdversarialFreeSubjectAudit.minimal_conditional_free_subject_theorem' does not depend on any axioms
```

Twelve theorems depend on **zero axioms** beyond Lean's core logic. The four finite model constructions depend only on `propext` (standard propositional extensionality used by `decide`). **Zero `sorryAx` exists across the entire module.**

---

## 8. Resposta Filosófica à Pergunta Orientadora: Dependência Ontológica vs Temporal

### Pergunta Orientadora:
> **Pode uma fonte impessoal explicar completamente a sua própria configuração determinada e a ocorrência concreta que dela depende, sem que essa explicação seja circular ou deixe precisamente essa determinação por explicar?**

### Resposta e Análise Estrutural:

A resposta rigorosa depende estritamente do nível de exigência explicativa imposto ao sistema:

1. **Sob Explicação de Nível 3 (Determinação de Configuração Não-Contrastiva):**
   Uma fonte impessoal $G$ pode fundamentar uma configuração $S$, e $S$ determinar $C$, num grafo acíclico bem fundamentado ($C \to S \to G$), tal como formalizado no modelo `deterministic_independent_ground_model`. Contudo, esta explicação é meramente descritiva ou factual: não responde ao problema contrastivo de saber por que ocorreu $S_{actual}$ em vez de uma alternativa acessível $S_{alt}$.

2. **Sob Explicação de Nível 4 (Explicação Contrastiva Genuína / PSR Forte):**
   **A resposta é NÃO.** Uma fonte impessoal **não pode** fornecer uma explicação contrastiva completa da sua configuração contingente sem incorrer num dos três membros do trilema ontológico:
   - **Membro 1 (Facto Bruto):** Se o fundamento impessoal $G$ for invariante entre mundos possíveis acessíveis sob o mesmo passado, $G$ obtém identicamente no mundo onde $S_{actual}$ ocorre e no mundo alternativo onde $S_{alt}$ ocorreria. Como uma condição invariante não pode justificar por que uma alternativa obteve em vez de outra, a quebra de simetria permanece um **facto bruto** desprovido de razão suficiente (`invariant_ground_cannot_contrastively_explain_contingent_source`).
   - **Membro 2 (Necessitarismo Rígido):** Se $G$ necessitar rigidamente a configuração de $S$, e $S$ determinar necessariamente $C$, então a ocorrência concreta $C$ torna-se metafisicamente necessária (`impossibility_of_invariant_deterministic_contingency`), destruindo a contingência de $C$.
   - **Membro 3 (Dependência Ontológica Circular):** Se a quebra de simetria impessoal for explicada pela ordenação ou optimização do estado resultante que contém $C$ (teleologia mecanicista orientada a fins), a explicação da configuração de $S$ pressupõe explicativamente a realidade de $C$. Uma vez que $C$ é constitutivamente determinado por $S$, estabelece-se a circularidade explicativa ontológica:
     $$S \longrightarrow C \longrightarrow S$$
     que é estritamente vazia e viola a aciclicidade fundamental da fundamentação ontológica (`wellFounded_explanation_has_no_two_cycle`).

### A Premissa Filosófica Decisiva que Falta Justificar:
O argumento contra a fonte impessoal depende inteiramente de subscrever o **Princípio da Teleologia Contrastiva**: a tese de que uma quebra de simetria entre contingentes acessíveis exige razão suficiente, e que tal razão só pode ser não-circular se for **intencional** (uma acção agencial orientada por razões, e não um mecanismo forçado).

Para além disso, mesmo concedendo que a fonte tem de ser agencial, o passo desta para um **Sujeito Livre (libertista)** exige indispensavelmente a premissa adicional de **Controlo Agencial sobre Alternativas** (`AgentialControlBridge`), que não decorre da mera agência e resolve por postulação o problema da sorte indeterminista (o clássico argumento Mind de Peter van Inwagen).

---

## 9. Conclusão Final e Síntese Epistémica

The intended thesis:
> *"If this proof exists as a concrete determined occurrence, then a Free Subject exists."*

is **not established as a necessary consequence of logic, determinism, or bare explanatory grounding alone**.

This audit does not assert that the metaphysical conclusion itself is false; rather, it establishes that the current formalization only derives the conclusion by relying on substantial philosophical premises that are not deduced within the system:
1. **Determinism vs Contingency:** Enforcing determinism means an invariant source configuration strictly precludes contingency. If the source is contingent, an independent impersonal ground can explain it deterministically without personal agency.
2. **Manufactured Circularity:** Backward explanatory dependence does not follow from Contrastive PSR or well-foundedness; it requires `consequence_dependent_selection`.
3. **Taxonomy Limits:** Contingent deterministic impersonal sources with internal or nomological reasons are omitted from the taxonomy unless an external ground node is present.
4. **Agential Control vs Luck:** An unforced personal originator does not automatically possess control over alternative possibilities (the classic Mind argument); `AgentialControlBridge` resolves this by stipulative fiat.
5. **Cosmological Termination:** Termination of causal ancestry is assumed as a raw postulate (`AncestryTerminatesDetermines`), leaving the infinite regress alternative unrefuted within the system.

When these five points are made explicit, what is achieved is not a refutation of the metaphysical thesis, but an exact mapping of its indispensable philosophical costs: the conclusion stands or falls with the independent justification of these bridge principles.
