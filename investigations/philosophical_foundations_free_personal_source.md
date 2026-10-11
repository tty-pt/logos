# The Philosophical Foundations of the Free Personal Source Argument
## A Critical and Systematic Investigation of the Three Underpinning Principles in Γ

**Author / Formalization Anchor:** Framework Γ (Logos Formalization)  
**Corpus Anchor:** `formal/Logos/*.lean`, `OntologicalIncompletenessTheorem.lean`  
**Epistemological Legend:**
- **[P]** Primary Source Citation (verified historical/philosophical text with exact original quotation)
- **[I]** Philosophical Interpretation (standard or defended hermeneutical reading in scholarly literature)
- **[R]** Analytical Inference (deductive or conceptual argument constructed in this investigation)
- **[T]** Lean Kernel Verified Theorem (formal declaration verified in Lean 4 with exact file:line anchor)

---

## 1. Executive Assessment of the Three Principles

### 1.0 The Governing Principle of the Elimination
The entire formal architecture of Γ is governed by a single decisive question:
> **Which kind of ultimate ground can explain why a contingent concrete reality obtains rather than an accessible alternative, without leaving the divergence brute, entering circularity or infinite regress, or necessitating the outcome so that contingency disappears?**

Framework Γ does not treat all metaphysically imaginable positions as equally viable answers to this question. Each explanatory candidate must satisfy the complete explanatory requirements simultaneously. The argument is cumulative: eliminating one failure mode is insufficient; a satisfactory candidate must survive all relevant constraints together:
1. It must provide an **ultimate ground** without circularity or internal infinite regress;
2. It must supply a **contrastive explanation** for why the actual configuration obtained rather than an accessible alternative, without treating modal divergence as brute;
3. It must preserve **genuine contingency**, ensuring that the outcome is not rigidly necessitated; and
4. It must ground action in **non-necessitated personal agency**, avoiding both deterministic intellectualism and brute indeterministic luck.

Under Γ's complete set of declared premises, the competing explanatory alternatives (contingent brute facts, internal circularity, infinite regress, rigid impersonal necessitation, brute indeterminism, and intellectualist necessitation) do not survive. The **Necessary Free Personal Source** is not merely one interesting hypothesis among several; it is the unique candidate that remains because the alternatives fail to satisfy the joint requirements.

### 1.1 The Three-Tier Theorem Architecture
The formal deduction of the **Free Personal Source** (`FreePersonalSource S T`) in Γ culminates in a three-tier architecture:
1. **Tier 1 (Cosmological Elimination):** `eliminative_existential_derives_unforced_personal_agent` (`OntologicalIncompletenessTheorem.lean:4187`). Deduces the existence of an ungrounded, necessary, transcendent, nature-invariant personal agent whose determination is unforced by antecedent reasons or mechanical prior states, **conditional on the complete set of structural and cosmological hypotheses**: system contingency (`ContingentSystem S`), well-foundedness, transitivity, and irreflexivity of constitutive priority (`ConstitutivePriority`), totality grounding conditions (`hInternalGroundsTotality`, `hGroundsTotality`), aseity termination (`GroundingTotalityTerminatesInAseity`), personal nature invariance, priority exclusion, teleological decoupling, and intellectualist evasion closure, alongside `GeneralContrastivePSR S`. **[T]** Footprint: `[propext, Classical.choice, Quot.sound]`, with 0 substantive axioms of Γ.
2. **Tier 2 (Metaphysical Integration):** `intermediate_existential_derives_unforced_personal_source` (`OntologicalIncompletenessTheorem.lean:4367`). Grounding identity mapped to `Entity.ofGround` via priority homomorphism, personal agency anchored in the Divine Person acting as `DivineRole.source`, while preserving categorical sort discipline (`EntityOf s ≠ Entity.ofGround`). **[T]**
3. **Tier 3 (Full Theistic Integration):** `eliminative_foundation_derives_free_personal_source_under_transmission` (`OntologicalIncompletenessTheorem.lean:4567`). Deduces the Free Personal Source endowed with all classical attributes, universal explanatory scope, and positive counterfactual freedom (`ActsFreely S T`), **conditional on its own explicit hypothesis signature**:
   - System contingency: `ContingentSystem S`;
   - Shared structural priority hypotheses: well-foundedness (`prior_wf`), transitivity (`prior_trans`), and totality ordering (`hConstitutiveOfTotality`, `hInternalGroundsTotality`, `hGroundsTotality`);
   - Aseity and nature invariance: `hAseity`, `hAseityNature`, and `hPersonalNature`;
   - Explanatory symmetry and ultimacy: `hSymmPrinciple` and `hUltRequirement`;
   - Ontic condition and causal determination: `hCond` and `hCausal`;
   - Five foundational metaphysical premises:
     1. `GeneralContrastivePSR S` (line 1049);
     2. `UniversalOutcomePSR S ConstitutivePriority` (line 1872);
     3. `MediatedExplanatoryScope S T ConstitutivePriority` (line 1940);
     4. `ExplanatoryTransmission S T ConstitutivePriority` (line 1960);
     5. `TranscendentAgentialActionCorrespondence S T` (line 2250). **[T]**

   **Architectural Precision Regarding Signatures:**
   The Tier 3 theorem directly establishes its existential result under its own signature via `eliminative_deduction_derives_free_personal_source_under_transmission`, rather than applying the Tier 2 theorem as an intermediate proof step. Tier 3 does **not** include `PriorityGroundingHomomorphism` or `TrinitarianPersonalBridge` as explicit signature parameters; those belong to Tier 2 (`intermediate_existential_derives_unforced_personal_source`, line 4367). In Tier 3, the acting divine subject and its hypostatic role `DivineRole.source` are packaged directly within `TranscendentAgentialActionCorrespondence`. Furthermore, `ActsFreely S T` is derived conditionally within Γ from `AgentialActionRealization`, `choice_reflection`, and `AgentialCounterfactualChoiceBridge` (`agential_freedom_derived`, line 810; `agential_determination_entails_choice_derived`, line 2200), rather than as an analytic consequence of mere non-necessitation. Alternative-choice power is thus a kernel-verified deduction *conditional on those action-theoretic bridges*, not an unconditioned discovery.

The formal independence investigations (witnessed by countermodels Model A and Model B in the Lean kernel) have definitively established that Tier 3 does not follow from the bare existential unicity of the universal ground nor from the unforced personal agent of Tier 1 alone. Rather, the master existential integration rests upon **three substantive foundational principles**:
- **Principle 1: `GeneralContrastivePSR S`** (`OntologicalIncompletenessTheorem.lean:1049`). The principle that a contingent concrete system $S$ possesses an explanatory ground providing a contrastive justification for why the actual configuration obtained rather than an accessible alternative.
- **Principle 2: `ExplanatoryTransmission S T ConstitutivePriority`** (`OntologicalIncompletenessTheorem.lean:1960`). The principle of concurrent causality (*concursus divinus*), whereby the explanatory efficacy of intermediate secondary causes in a complete grounding chain is transmitted to and grounded in the ultimate foundation.
- **Principle 3: `TranscendentAgentialActionCorrespondence S T`** (`OntologicalIncompletenessTheorem.lean:2250`). The principle of intentional creation (*creatio ex voluntate*), whereby the ground's factual determination of concrete actuality corresponds to an originating intentional act of the Divine Person acting as Source.

### Executive Verdict
| Principle | Canonical Status in Γ | Epistemic Justification | Prime Vulnerability | Kernel Model Test |
| :--- | :--- | :--- | :--- | :--- |
| **`GeneralContrastivePSR`** | Foundational Premise of Tier 1 | Rational Presupposition of Total Contrastive Explanation | Radical Brute Fact Assertion / Anti-Rationalism | `dualWorldS` (line 5195) |
| **`ExplanatoryTransmission`** | Substantive Bridge (`Tag: META`) | Thomistic Concurrentism (*Causa secunda non agit nisi in virtute primae*) | Durandus's Mere Conservationism / Causal Insulation | Model A (`rivalS`, line 5733) |
| **`TranscendentAgentialActionCorrespondence`** | Substantive Bridge (`Tag: META`) | Scotist-Thomistic Theory of Divine Volitional Act (*Creatio ex Voluntate*) | Spinozist/Leibnizian Intellectualist Necessity or Epicurean Randomness | Model B (`T_det`, line 5892) |

---

## 2. The Strongest Argument for GeneralContrastivePSR

### 2.1 The Narrowest Defensible Formulation
The target of Γ is **not** an unconstrained, rationalist PSR asserting that every proposition, truth, or metaphysical entity has an extrinsic sufficient reason. **[R]** Such unconstrained formulations notoriously trigger Van Inwagen's modal collapse. Instead, Γ isolates the **restricted contrastive principle on contingent concrete totalities**:

$$\text{GeneralContrastivePSR}(S) \iff \text{ContingentSystem}(S) \to \exists T : \text{CandidateGround}(S), T \text{ grounds } S \land \forall w_{\text{alt}} \in \text{Acc}(S), \text{ContrastiveExplanation}(S, T, w_{\text{alt}})$$

In Γ's ontology, this principle is structured across four distinct conceptual levels:
1. **Explanation of Entity Existence:** That an entity $e$ is placed into being rather than non-being. **[I]**
2. **Explanation of Determinate Configuration:** Why the state space assigns particular values $(n \mapsto \text{true/false})$ to nodes of $S$ at world $w$. **[I]**
3. **Contrastive Explanation:** Why configuration $\mathbf{C}_{\text{act}}$ obtained *rather than* accessible configuration $\mathbf{C}_{\text{alt}}$ ($w_{\text{act}} \text{ rather than } w_{\text{alt}}$). **[I]**
4. **Complete Ultimate Explanation of Totality:** An explanation whose explanatory chain does not terminate in an unexplained internal subsystem of $S$ but terminates in an ungrounded transcendent foundation. **[R]**

In the Lean theorem hierarchy:
- Step 1 (Cosmological Elimination, Tier 1) requires **Levels 3 and 4**: without contrastive explanation across accessible worlds, the 7 competing branches (internal loops, infinite regress, rigid impersonal necessitation, brute alternative, and intellectualist evasion) cannot be eliminated. **[T]**
- Levels 1 and 2 alone are insufficient, because an internal node could explain its own existence or configuration conditionally while leaving the contrastive shift to an alternative completely brute. **[T]** (`internal_candidate_cannot_ground_totality`, line 560).

### 2.2 Deductive and Transcendental Defense of Contrastive PSR

#### The Argument from the Presupposition of Complete Explanation
1. **Fact vs. Explanation Distinction [R]:** To describe a contingent concrete state of affairs $\mathbf{C}_{\text{act}}$ is merely to assert *that* it obtains. To explain it is to render intelligible *why* it obtains.
2. **The Intelligibility of Modal Contrast [P, I]:** As Leibniz observes in *Monadology* §32:
   > *"Aucun fait ne saurait se trouver vrai ou existant, aucune énonciation véritable, sans qu'il y ait une raison suffisante pourquoi il en soit ainsi et non pas autrement."* **[P]** (G. W. Leibniz, *Monadologie*, 1714, §32).
   When an alternative state $\mathbf{C}_{\text{alt}}$ is genuinely accessible ($\text{Accessible } w_{\text{act}} \ w_{\text{alt}}$), the actual state $\mathbf{C}_{\text{act}}$ represents an asymmetry in reality. A reason that is equally compatible with both $\mathbf{C}_{\text{act}}$ and $\mathbf{C}_{\text{alt}}$ fails to be an explanation of $\mathbf{C}_{\text{act}}$'s actualization *over* $\mathbf{C}_{\text{alt}}$. **[R]** (van Fraassen 1980, Lipton 1990).
3. **The Inadequacy of Disjoint Local Explanations [R, T]:** A collection of local causal explanations within $S$, where each node $n_i$ is explained by node $n_{i-1}$, leaves the totality $\bigcup n_i$ unexplained as to why this entire world-history obtained rather than an alternative counterfactual history $\mathbf{C}_{\text{alt}}$. This is formally proved in Lean: `concrete_system_cannot_be_fully_internally_determined` (`OntologicalIncompletenessTheorem.lean:471`). **[T]**
4. **The Rational Demand Against Inexplicable Selection [R]:** If a concrete system $S$ could actualize $\mathbf{C}_{\text{act}}$ rather than $\mathbf{C}_{\text{alt}}$ with zero ground, reality would contain a radical, unconditioned metaphysical rupture: an objective differential between two real possibilities with no ground for the divergence.
5. **Epistemic Parity and Explanatory Pressure [R, I]:** While an opponent may attempt to isolate bruteness strictly to the cosmic boundary while demanding reasons for local empirical and cognitive beliefs, this separation faces severe epistemic pressure: if contingent states of affairs can actualize with zero ground, one loses any non-arbitrary metaphysical guarantee against arbitrary brute occurrences elsewhere (Pruss 2006, Della Rocca 2010). However, this functions as a powerful parity and plausibility argument (an inference to the best explanation), not as a formal deductive refutation of the logically consistent local-empiricist stance.

### 2.3 Answers to the Strongest Objections

#### Objection 1: Brute Facts (Russell, Hume)
*Objection:* Why cannot the total contingent universe simply be an unexplained brute fact? As Bertrand Russell stated in the 1948 BBC debate with Copleston: *"The universe is just there, and that's all."*
*Response:* The response to global bruteness in Γ is **an Inference to the Best Explanation (IBE) and a parity argument against arbitrary explanatory boundaries, not a deductive refutation**. A naturalist who accepts local physical causation while taking the cosmic totality as brute is not guilty of a formal logical contradiction. However, that position introduces an ungrounded asymmetry: if uncaused, brute actuality is admitted at the cosmic boundary, there is no non-arbitrary metaphysical principle that restricts bruteness to that boundary while forbidding it within intermediate macroscopic physical systems (Pruss 2006). In Γ, bruteness is structurally excluded by the declared hypothesis `GeneralContrastivePSR S` and constitutive priority irreflexivity (`unjustified_alternative_fails_contrastive_at`, line 1116). **[T]**

#### Objection 2: Van Inwagen's Modal Collapse
*Objection:* If the PSR holds, let $p$ be the Big Conjunctive Contingent Fact (BCCF)—the conjunction of all true contingent propositions. Van Inwagen's argument operates via five explanatory premises: (0) Factivity of explanation: if $q$ explains $p$, then $q$ is true; (1) the BCCF $p$ exists and is a true contingent conjunction; (2) a necessary proposition cannot explain a contingent proposition; (3) no contingent proposition can explain itself; and (4) the Explanatory Distribution Principle (if $q$ explains conjunction $p$, then $q$ explains every conjunct of $p$). If $q$ explains $p$, then: if $q$ is necessary, it violates (2); if $q$ is contingent, then by factivity (0) $q$ is a true contingent proposition and therefore a conjunct of $p$ by (1), so by distribution (4) $q$ explains $q$, violating (3). Thus, the BCCF argument generates a strict contradiction between an unrestricted PSR and these explanatory premises.
*Response:* The libertarian agent-causal framework in Γ challenges the **Explanatory Distribution Principle (4)** and the propositional reduction of agency: an agent's free choice teleologically explains the obtained outcome without the choice itself functioning as a proposition that circularly explains itself. Crucially, however, **this response does not independently refute modal collapse from neutral logical premises**; it resists the collapse *conditional upon adopting libertarian agency as a substantive metaphysical commitment*. Without that prior commitment, Van Inwagen's argument remains an open, unresolved challenge against any unconstrained PSR.

#### Objection 3: The Stopping-Point / Regress Objection
*Objection:* Why must explanatory inquiry terminate in an ultimate transcendent ground rather than continue infinitely?
*Response:* In Γ, infinite regress is not rejected by aesthetic preference, but by the formal properties of constitutive priority (`ConstitutivePriority`). If an explanatory chain is infinite and internal to $S$, every node remains conditionally dependent on prior nodes, leaving the totality of conditionality ungrounded: `infinite_regress_cannot_self_ground` (`OntologicalIncompletenessTheorem.lean:182`). **[T]**

### 2.4 Epistemological Status of GeneralContrastivePSR
**Conclusion:** `GeneralContrastivePSR` is best defended as an **Inference to the Best Explanation (IBE) and Substantive Rational Presupposition of Total Explanation**. It is not an analytic tautology of propositional logic (hence its status as an unproved cosmological premise of Tier 1). While accepting brute global actuality alongside local empiricism is not formally self-contradictory in first-order logic, it introduces an arbitrary explanatory discontinuity and leaves modal divergence unexplained.

---

## 3. The Strongest Argument for ExplanatoryTransmission

### 3.1 The Thomistic Causal Argument: Concursus Divinus
The canonical Lean predicate:
```lean
def ExplanatoryTransmission (S : ConcreteSystem.{u}) (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop) : Prop :=
  ∀ (T' : CandidateGround S) (w_alt : S.World),
    ExplainsOutcomeAt S T' ConstitutivePriority w_alt (SystemOutcomeAt S w_alt) →
    CompleteExplanatoryChain S ConstitutivePriority T' T →
    ExplainsOutcomeAt S T ConstitutivePriority w_alt (SystemOutcomeAt S w_alt)
```
connects secondary causes ($T'$) to the primary ground ($T$).

#### Primary Textual Anchor: Thomas Aquinas, *Summa Theologiae* I, q. 105, a. 5
Thomas Aquinas explicitly addresses whether God operates in every operating secondary agent (*Utrum Deus operetur in omni operante*):
> *"Respondeo dicendum quod Deus operatur in omni operante quadrupliciter. Primo quidem, per modum finis... Secundo, per modum primi agentis: sicut enim secundum agens agit per virtutem primi agentis a quo movetur ad agendum... Tertio, quia Deus non solum dat virtutem agentibus creatis, sed etiam eam conservat in esse... Quarto, quia virtus a Deo collata creaturae non potest agere nisi per virtutem ipsius Dei... Patet etiam quod non sic idem effectus causatur a Deo et a causa naturali, quasi partim a Deo et partim a naturali agente fiat, sed totus ab utroque secundum alium modum: sicut idem effectus totus attribuitur instrumento, et totus etiam principali agenti."* **[P]** (Thomas Aquinas, *ST* I, q. 105, a. 5, corpus).

#### The Four Distinct Causal Levels in Concurrentism
To avoid confusion, the argument decomposes into four rigorous levels:
1. **Level 1 (Ontological Dependence):** Secondary cause $T'$ depends on the primary ground $T$ for its existence (*conservatio in esse*). **[P]**
2. **Level 2 (Dependence of Operative Power):** The causal power of $T'$ is not self-derived but participated and sustained by $T$. **[P]**
3. **Level 3 (Immediate Production):** $T'$ is the immediate, genuine cause of the particular outcome in $S$ (*causa secunda agit proprium effectum*). **[P]**
4. **Level 4 (Explanatory Transmission):** Because $T'$ acts exclusively in virtue of the primary cause sustaining and moving it, the ultimate explanation of the effect produced by $T'$ terminates in $T$ (*totus effectus attribuitur instrumento et totus principali agenti*). **[P, R]**

#### Demarcation: Concurrentism vs. Occasionalism vs. Mere Conservationism
- **Against Occasionalism (Malebranche):** Occasionalism denies Level 3, asserting that creatures have no real causal efficacy, making divine action universal but illusory. Aquinas refutes this: denying secondary causation insults divine wisdom, rendering creaturely powers redundant (*virtutes operativae frustra essent collatae*). **[P]**
- **Against Mere Conservationism (Durandus of Saint-Pourçain):** Durandus held that God creates and conserves secondary causes with active powers, but does not concur directly in their operations. If Durandus were right, Level 4 would fail: a secondary cause could produce an effect that is completely unexplained by the first cause.
- **The Thomistic Synthesis:** Primary causation and secondary causation are non-competitive. The primary ground is not an extrinsic rival to the secondary cause; rather, it is the foundational ground that enables the secondary cause to exercise its efficacy. Therefore, explanatory efficacy is transitively grounded across the constitutive chain. **[I, R]**

### 3.2 Testing the Canonical Lean Formulation
In Lean, `ExplanatoryTransmission` is formulated as:
$$\text{ExplainsOutcome}(T') \land \text{Chain}(T', T) \implies \text{ExplainsOutcome}(T)$$
Is this formulation justified in full generality?
- **Analysis [R]:** In the abstract setting of `CandidateGround`, without additional metaphysics, a local cause $T'$ could settle a configuration at world $w_{\text{alt}}$ through a mechanism completely detached from $T$.
- **Model A as Diagnostic [T]:** In `OntologicalIncompletenessTheorem.lean:5733`, Model A (`rivalS`, `T_main`, `T_rival`) constructs an explicit countermodel where:
  1. `T_main` is the unique necessary ground of all entities;
  2. `T_rival` is a secondary agent that explains the configuration at $w_1$;
  3. `T_main` does **not** explain $w_1$, because its causal access is restricted.
  Theorem `rival_ground_model_satisfies_neutral_psr_but_fails_scope` (line 5852) proves that bare modal grounding (`OneEssence g e`) does not analytically entail `ExplanatoryTransmission`. **[T]**
- **Metaphysical Commitment:** `ExplanatoryTransmission` is **not** an analytic tautology of grounding logic; it is a **substantive metaphysical commitment (`Tag: META`)** embodying Thomistic concurrentism.

---

## 4. The Strongest Argument for TranscendentAgentialActionCorrespondence

### 4.1 Defending Intentional Creation (*Creatio ex Voluntate*)
The principle `TranscendentAgentialActionCorrespondence S T` connects the candidate ground's cosmological determination of concrete actuality to the originating intentional act of the Divine Person occupying `DivineRole.source`.

#### Primary Textual Anchors: Aquinas and Scotus
1. **Thomas Aquinas on Creation via Will:**
   > *"Cum igitur Deus sit causa rerum per suum intellectum et voluntatem, sicut artifex rerum artificiatarum... necesse est quod voluntas Dei sit causa rerum."* **[P]** (Thomas Aquinas, *ST* I, q. 19, a. 4, corpus).
   > *"Cum bonitas Dei sit perfecta, et esse possit sine aliis, cum nihil ei perfectionis ex aliis accrescat; sequitur quod alia a se velle non sit ei necessarium absolute."* **[P]** (Thomas Aquinas, *ST* I, q. 19, a. 3, corpus).
2. **John Duns Scotus on Synchronic Contingency:**
   > *"Dico quod potentia ad opposita est duplex: una cum successione... Alia est potentia sine successione, ut in eodem instanti in quo voluntas vult A, habet potentiam ad non velle A pro eodem instanti... Ideo voluntas divina contingenter vult quidquid vult extra se."* **[P]** (John Duns Scotus, *Ordinatio* I, d. 39, q. un.).

#### Resolving the Core Antinomies of Divine Creation
1. **Invariant Necessary Nature vs. Contingent Effect [R]:**
   How can a Source whose essence is strictly necessary and immutable produce a contingent effect?
   - *Intellectualist Error (Spinoza):* An immutable, necessary nature can only produce necessary effects ($E = f(N) \implies \Box E$).
   - *Thomistic-Scotist Resolution:* The divine essence is necessary, but the relation of the divine will to finite external objects is non-necessary. God necessarily loves His own infinite goodness, but no finite creaturely system is necessary for the manifestation of that goodness (*nihil ei perfectionis ex aliis accrescat*). Therefore, the act of will regarding external creation is inherently free and contingent.
2. **Reasons Without Necessitation (Non-Deterministic Reasons Explanation) [R, I]:**
   God acts for supreme reasons (wisdom, goodness, beauty), yet these reasons do not necessitate a single unique world:
   - *No Best of All Possible Worlds:* For any created universe, a more perfect or differently configured universe is conceivable.
   - *Buridan's Ass Dissolution:* When multiple alternatives are equally good or incommensurable, a rational agent can choose without arbitrariness through **election** (Scotus's self-determining will, *voluntas est activa potentia respectu oppositorum*).
   - In Γ, this is formally proved: `agential_election_resolves_contrastive_psr_for_equal_goods` (`OntologicalIncompletenessTheorem.lean:2880`). **[T]**
3. **Freedom vs. Epicurean Randomness [R]:**
   An unforced choice is not random luck. An event is random when it is ungrounded in any subjective intention or reason. In Γ's action theory, `ActsFreely S T` requires that the choice is grounded in the agent's subjective apprehension of the alternatives (`Means s out_act ∧ Means s out_alt`) and initiated by the agent: `agential_freedom_derived` (line 810). **[T]**
   Crucially, `ActsFreely S T` is derived within Γ **conditional on** explicit action-theoretic bridge premises: `AgentialActionRealization`, `choice_reflection`, and `AgentialCounterfactualChoiceBridge`. Alternative-choice power is therefore supplied by these substantive structures, rather than emerging analytically from mere non-necessitation. A kernel-verified derivation conditional on those bridges must not be conflated with a philosophical proof of the bridges themselves.

### 4.2 Comparison of Leading Philosophical Positions
| Position | Core Thesis | Compatibility with Γ | Status in Lean Formalization |
| :--- | :--- | :--- | :--- |
| **Necessitarian Emanation** (Plotinus, Spinoza) | The universe flows by natural necessity from the First Principle. | **INTERNALLY ELIMINATED** | Contradicts `ContingentSystem S` (`necessary_ground_cannot_rigidly_necessitate_contingent_system`, line 1273). **[T]** |
| **Intellectualist Determinism** (Leibniz) | Divine reasons uniquely necessitate the choice of the best world. | **INTERNALLY ELIMINATED** | Contradicts contingency of priority chain (`deepened_intellectualist_evasion_closure`, line 3099). **[T]** |
| **Brute Indeterminism** (Epicurus) | Modal alternatives exist, but actualization occurs by uncaused swerve. | **INTERNALLY ELIMINATED** | Violates contrastive explanation (`unjustified_alternative_fails_contrastive_at`, line 1116). **[T]** |
| **Libertarian Agent Causation** (Scotus, Aquinas, Pruss, O'Connor) | The agent determines the contingent outcome for reasons without antecedent necessitation. | **SURVIVING CANDIDATE** | Formalized and derived in `CompleteLibertarianFreedomArgument.lean` and Tier 3 (`eliminative_foundation_derives_free_personal_source_under_transmission`, line 4567). **[T]** |

### 4.3 Coherence of the Formal Correspondence in Lean
In `OntologicalIncompletenessTheorem.lean:2250`, `TranscendentAgentialActionCorrespondence` is defined as:
```lean
inductive TranscendentAgentialActionCorrespondence (S : ConcreteSystem.{0}) (T : CandidateGround S) : Prop
  | mk : ∀ (agent : Logos.Agency.Subject),
      Logos.TrinitarianSubjectBridge.DivineSubjectRole agent = Logos.TrinitarianSubjectBridge.DivineRole.source →
      Logos.Person.Person agent →
      (∀ (w : S.World) (out : Option (S.Node → Bool)),
        T.DeterminesOutcomeAt T.ground w out ↔
          (out = SystemOutcomeAt S w ∧ Logos.Agency.Act agent (OutcomeAt S w out))) →
      AgentialActionRealization S T agent →
      (∀ (w_alt : S.World), S.Accessible S.actualWorld w_alt → T.ReasonsFavor T.ground S.actualWorld w_alt) →
      T.DeterminesOutcomeAt T.ground S.actualWorld (some (S.ConfigurationIn S.actualWorld)) →
      TranscendentAgentialActionCorrespondence S T
```
- **Strict Non-Circularity:** The constructor does **not** assume `ChoosesOutcomeAt` or `SelectsIntentionally`. These are derived via `agential_action_grounding_derives_actual_choice` (line 2315) and `agential_action_grounding_derives_selects_intentionally` (line 2355). **[T]**
- **Model B as Diagnostic [T]:** In `OntologicalIncompletenessTheorem.lean:5892`, Model B ($T_{\text{det}}$) proves that a candidate ground can causally determine the cosmos while lacking intentional action and alternative choice: `model_b_violates_transcendent_action_correspondence` (line 5986). This proves that `TranscendentAgentialActionCorrespondence` is a substantive bridge principle that cannot be eliminated by bare unicity. **[T]**

---

## 5. Comparative Objection-and-Response Table

| Principle | Strongest Philosophical Objection | Historical Source of Objection | Defense / Response in Framework Γ | Formal Lean Anchor |
| :--- | :--- | :--- | :--- | :--- |
| **`GeneralContrastivePSR`** | **Radical Bruteness:** The universe's total contingent state is an inexplicable brute terminus. | David Hume, Bertrand Russell (1948 Debate) | Internally eliminated under Γ: fails contrastive PSR (`unjustified_alternative_fails_contrastive_at`, line 1116). Externally contestable: a critic can reject PSR and accept cosmic bruteness. | `unjustified_alternative_fails_contrastive_at` (line 1116) **[T]** |
| **`GeneralContrastivePSR`** | **Modal Collapse:** Any sufficient explanation of the Big Contingent Fact renders it necessary. | Peter van Inwagen (1983) | Internally eliminated under Γ via agent causation; conditional on accepting libertarian agency as a substantive primitive, contrastive reasons explain outcomes without necessitation. | `contingent_determination_constructs_positive_libertarian_choice` (CLFA:2712) **[T]** |
| **`ExplanatoryTransmission`** | **Dilemma of Durandus (Mere Conservationism):** A secondary cause has real, autonomous efficacy; its specific effect is not explained by the primary ground. | Durandus of Saint-Pourçain (*In Sent.* II, d. 1, q. 5) | Creaturely powers are participated and dependent; secondary causes act only *in virtute causae primae*. Primary and secondary causes are concurrent, not competing partial causes. | `mediated_scope_to_ultimate_scope_under_transmission` (line 1975) **[T]** |
| **`ExplanatoryTransmission`** | **Ocasionalist Collapse:** If the primary ground explains all effects, secondary causes are superfluous. | Nicolas Malebranche (*De la recherche de la vérité*) | Refuted by Aquinas (*ST* I, q. 105, a. 5): God creates real operative causal powers in creatures; God acts through them as principal agent through instrument, preserving secondary efficacy. | `CompleteExplanatoryChain` (line 1930) **[T]** |
| **`TranscendentAgentialActionCorrespondence`** | **Spinozist Necessitarianism:** An immutable, necessary divine nature cannot have contingent volitions; God creates necessarily. | Baruch Spinoza (*Ethics* I, p. 16, 29, 33) | Internally eliminated under Γ: an immutable nature with necessitating determination destroys contingency (`necessary_ground_cannot_rigidly_necessitate_contingent_system`, line 1273). | `necessary_ground_cannot_rigidly_necessitate_contingent_system` (line 1273) **[T]** |
| **`TranscendentAgentialActionCorrespondence`** | **Rationalist Determinism:** God must create the best possible world, so divine reasons determine the outcome uniquely. | G. W. Leibniz (*Theodicy* §45) | Internally eliminated under Γ: if reasons exhaustively fix the outcome, contingency is lost (`deepened_intellectualist_evasion_closure`, line 3099). Election among equal goods is free. | `deepened_intellectualist_evasion_closure` (line 3099) **[T]** |
| **`TranscendentAgentialActionCorrespondence`** | **Arbitrariness / Luck Objection:** If reasons do not necessitate the choice, the choice is an arbitrary, lucky roll of the dice. | Robert Kane / Contemporary Critics of Incompatibilism | Internally eliminated under Γ: choice is teleological, motivated by the good of the configuration, derived via action bridges (`agential_freedom_derived`, line 810). | `agential_freedom_derived` (line 810) **[T]** |

---

## 6. Revised Dependency Argument Connecting the Three Principles

The three principles do not operate as isolated axioms; they form a mutually supportive, unified transcendental-metaphysical architecture:

```
                               [ ContingentSystem S ]
                                          │
                        (Demand for Contrastive Intelligibility)
                                          ▼
                             [ GeneralContrastivePSR S ]
                                          │
                     ┌────────────────────┴────────────────────┐
                     ▼                                         ▼
         [ Structural Impossibility ]              [ Eliminative Exhaustion ]
      - Internal Loops Violated (3E)              - 7 Competing Branches Cut
      - Infinite Regress Fails (3C)               - Impersonal Necessitation Fails
      - Circularity Refuted (3B)                  - Intellectualist Evasion Closed
                     │                                         │
                     └────────────────────┬────────────────────┘
                                          ▼
                      ┌────────────────────────────────────────┐
                      │ CANONICAL TIER 1:                      │
                      │ eliminative_existential_derives_       │
                      │ unforced_personal_agent (line 4187)    │
                      └────────────────────────────────────────┘
                           │                              │
          (+ PriorityGroundingHomomorphism)               │ (Direct Independent
          (+ Trinitarian Personal Ground)                 │  Existential Signature)
                           ▼                              │
      ┌────────────────────────────────────────┐          │
      │ CANONICAL TIER 2:                      │          │
      │ intermediate_existential_derives_      │          │
      │ unforced_personal_source (line 4367)   │          │
      └────────────────────────────────────────┘          │
                                                          ▼
                                ┌────────────────────────────────────────┐
                                │ Explicit Hypotheses of Tier 3:         │
                                │ - GeneralContrastivePSR S              │
                                │ - UniversalOutcomePSR S                │
                                │ - MediatedExplanatoryScope S T         │
                                │ - ExplanatoryTransmission S T          │
                                │ - TranscendentAgentialActionCorr S T   │
                                │ - Shared Structural / Aseity Premises  │
                                └────────────────────────────────────────┘
                                                          │
                                                          ▼
                                ┌────────────────────────────────────────┐
                                │ CANONICAL TIER 3:                      │
                                │ eliminative_foundation_derives_free_   │
                                │ personal_source_under_transmission     │
                                │ (line 4567)                            │
                                │ [FreePersonalSource S T ∧ ActsFreely]  │
                                └────────────────────────────────────────┘
```

### Analysis of the Interactions
1. **Does the PSR Require Necessitation? [R]** No. The contrastive PSR demands a distinction-making reason why $w_{\text{act}}$ rather than $w_{\text{alt}}$ obtained. `TranscendentAgentialActionCorrespondence` supplies this reason without necessitation via an **agent-causal election** motivated by divine goodness.
2. **Does Explanatory Transmission Add Genuine Explanatory Completeness? [R]** Yes. Without `ExplanatoryTransmission`, local secondary causes could explain localized subsystems without the ultimate source possessing universal explanatory scope (as shown by Model A). Transmission integrates secondary causation into primary grounding.
3. **Does Intentional Creation Avoid Circularity? [R, T]** Yes. The explanation of the choice does not appeal to a prior choice; it appeals to the agent's active power of will operating on contrastive reasons. Actual-world choice is derived from the originating act, not circularly presupposed.

---

## 7. Ranked Assessment by Philosophical Strength and Vulnerability

### Rank 1 (Most Robust): `GeneralContrastivePSR`
- **Strengths:**
  - Grounded in the demand for rational intelligibility and modal explanation.
  - Formulated strictly as a restricted contrastive principle on contingent totalities, avoiding standard paradoxes of unrestricted propositional PSR.
  - Supported by strong parity considerations: denying the PSR at the cosmic boundary while demanding reasons within science introduces an ungrounded, arbitrary explanatory discontinuity.
- **Vulnerabilities:**
  - An opponent committed to Russellian physicalism can consistently accept global brute reality while demanding local empirical justification, treating cosmic initial conditions as an unexplained stopping point.

### Rank 2 (Intermediate Strength): `TranscendentAgentialActionCorrespondence`
- **Strengths:**
  - Backed by the profound classical tradition of divine freedom (Aquinas, Scotus) and modern incompatibilist action theory (Pruss, O'Connor).
  - Resolves both Spinozist fatalism and Epicurean randomness through the notion of teleological election among compossible goods.
  - Rigorously formalized and non-circular in the Lean kernel.
- **Vulnerabilities:**
  - Highly demanding metaphysical machinery: requires bridging cosmic determination with the intentional semantics of a Divine Person acting as `DivineRole.source`.
  - Dependent on the sort distinction between `Entity.ofGround` and `EntityOf s`.

### Rank 3 (Most Vulnerable): `ExplanatoryTransmission`
- **Strengths:**
  - Essential to any classical theistic metaphysics of *concursus divinus* and conservation.
  - Successfully prevents deistic fragmentation or rival-ground pluralism.
- **Vulnerabilities:**
  - Susceptible to the historical challenge of Durandism (mere conservationism): an opponent can maintain that creaturely secondary causes possess autonomous causal efficacy that does not transmit its explanatory debt to the ultimate ground.
  - As Model A proves, this principle cannot be extracted purely from the meaning-containment semantics of `OneEssence`.

---

## 8. Precise Account of What Remains a Substantive Metaphysical Commitment

In the final, frozen architecture of Γ, the epistemic boundaries are sharply and honestly demarcated:

1. **What is Analytically / Deductively Established in the Kernel (Zero Substantive Axioms):**
   - The conditional deduction of Tier 1 (`eliminative_existential_derives_unforced_personal_agent`): IF $S$ is contingent, IF `GeneralContrastivePSR S` holds, and IF `ConstitutivePriority` is well-founded, THEN there exists an ungrounded, necessary, transcendent, personal agent unforced by antecedent states. **[T]**
   - The refutation of internal grounding, infinite regress, circularity, rigid necessitation, and rational intellectualist evasion. **[T]**
   - The non-circular derivation of actual-world choice and intentional selection from an originating agential act and contrastive alternatives. **[T]**
   - The independence of `ExplanatoryTransmission` (Model A) and `TranscendentAgentialActionCorrespondence` (Model B). **[T]**

2. **What Remains an Irreducible Metaphysical Commitment:**
   - **Commitment 1:** `GeneralContrastivePSR S` — The commitment to the rational intelligibility and contrastive explanation of the actual contingent concrete totality across accessible modal alternatives.
   - **Commitment 2:** `UniversalOutcomePSR S ConstitutivePriority` — The commitment that every concrete outcome in every accessible counterfactual world possesses an explanatory ground, preventing brute counterfactual actuality and enabling the derivation of counterfactual choice (`ActsFreely S T`).
   - **Commitment 3:** `MediatedExplanatoryScope S T ConstitutivePriority` — The structural commitment that local secondary explanations in accessible worlds connect to the ultimate ground via complete constitutive priority chains.
   - **Commitment 4:** `ExplanatoryTransmission S T ConstitutivePriority` (`Tag: META`) — The commitment to Thomistic concurrent causality (*concursus divinus*), asserting that secondary causes act only in virtue of the primary ground.
   - **Commitment 5:** `TranscendentAgentialActionCorrespondence S T` (`Tag: META`) — The commitment to *creatio ex voluntate*, asserting that the cosmic actualization of the universe is the originating voluntary act of a Divine Person.

None of Commitments 1–5 is a disguised tautology, and none can be derived from bare universal ground unicity without circularity. They are the explicit, noble, and historically grounded metaphysical bridges of classical theistic philosophy.

---

## 9. Comprehensive Bibliography with Verified Primary Citations

### 9.1 Primary Sources
1. **Thomas Aquinas**
   - *Summa Theologiae*, Pars Prima (ST I):
     - q. 19, a. 3: *Utrum quidquid Deus vult, ex necessitate velit.* (Verified: divine will is not absolutely necessitated regarding creatures).
     - q. 19, a. 4: *Utrum voluntas Dei sit causa rerum.* (Verified: divine intellect and will are the cause of things).
     - q. 19, a. 10: *Utrum Deus habeat liberum arbitrium.* (Verified: God has free choice regarding contingent creation).
     - q. 105, a. 5: *Utrum Deus operetur in omni operante.* (Verified: God operates in every operating agent by conferring power, conserving it, applying it, and as principal agent through instrument; total effect from both).
   - *Summa Contra Gentiles*, Liber Tertius (SCG III), c. 67: *Quod Deus est causa operandi omnibus operantibus.* (Verified).
   - *De Potentia Dei*, q. 3, a. 7: *Utrum Deus operetur in operatione naturae.*

2. **John Duns Scotus**
   - *Ordinatio* (Opera Omnia, ed. Vaticana):
     - I, d. 2, p. 1, qq. 1-2: *De existentia primi principii.* (The triple primacy of efficiency, finality, and eminence).
     - I, d. 8, p. 2, q. un.: *De simplicitate et immutabilitate divina.*
     - I, d. 39, qq. 1-5: *De scientia Dei et contingentia rerum.* (Formulation of synchronic contingency: *potentia ad opposita sine successione*).
   - *Lectura* I, d. 39, qq. 1-5.

3. **Gottfried Wilhelm Leibniz**
   - *Monadologie* (1714), §§ 32, 53, 54. (Principle of Sufficient Reason, choice of the best world, moral necessity).
   - *Essais de Théodicée sur la bonté de Dieu, la liberté de l'homme et l'origine du mal* (1710), §§ 44-45, 196. (*Inclinant sans nécessiter*).

4. **Durandus of Saint-Pourçain**
   - *In Sententias Theologicas Petri Lombardi Commentariorum Libri Quatuor*, Lib. II, dist. 1, q. 5. (Classical defense of mere conservationism / denial of immediate concurrentism).

### 9.2 Scholarly and Contemporary Literature
1. **Stanford Encyclopedia of Philosophy (SEP)**
   - Melamed, Yitzhak Y., and Martin Lin. "Principle of Sufficient Reason." *The Stanford Encyclopedia of Philosophy* (Fall 2021 Edition), Edward N. Zalta (ed.).
   - Koons, Robert. "Divine Freedom." *The Stanford Encyclopedia of Philosophy* (Winter 2020 Edition), Edward N. Zalta (ed.).
   - Pasnau, Robert. "Divine Concurrence." *The Stanford Encyclopedia of Philosophy* (Spring 2021 Edition).
2. **Monographs and Articles**
   - Della Rocca, Michael. "PSR." *Philosophical Review* 119.1 (2010): 1–41.
   - Freddoso, Alfred J. "God's General Concurrence with Secondary Causes: Why Conservation is Not Enough." *Philosophical Perspectives* 5 (1991): 553–585.
   - Freddoso, Alfred J. "God's General Concurrence with Secondary Causes: The Mechanist Challenge." *The Thomist* 58.1 (1994): 43–78.
   - Lipton, Peter. "Contrastive Explanation." *Knowledge and Explanation in Cultural Anthropology*, Cambridge UP, 1990.
   - O'Connor, Timothy. *Persons and Causes: The Metaphysics of Free Will*. Oxford University Press, 2000.
   - Pruss, Alexander R. *The Principle of Sufficient Reason: A Reassessment*. Cambridge Studies in Philosophy, Cambridge University Press, 2006.
   - van Fraassen, Bas C. *The Scientific Image*. Oxford University Press, 1980.
   - van Inwagen, Peter. *An Essay on Free Will*. Oxford University Press, 1983 (pp. 202–204).

---

## 10. Formal-Conceptual Harmony and Optional Lean Refinements

### Evaluation of Lean Predicates Against Philosophical Findings
1. **`GeneralContrastivePSR` (`OntologicalIncompletenessTheorem.lean:1049`):**
   - *Finding:* Accurately isolates contrastive justification across accessible divergent worlds without imposing global propositional necessitation, functioning as an IBE hypothesis rather than a logical tautology.
2. **`ExplanatoryTransmission` (`OntologicalIncompletenessTheorem.lean:1960`):**
   - *Finding:* Captures the core requirement of concurrent efficacy across constitutive chains, though its formal universal quantification over arbitrary `CandidateGround T'` has broader abstract scope than historical theological concursus (which applies specifically to God and creaturely substances).
3. **`TranscendentAgentialActionCorrespondence` (`OntologicalIncompletenessTheorem.lean:2250`):**
   - *Finding:* Rigorous action-theoretic realization structure (`AgentialActionRealization`) that avoids circularity in actual choice, though its link to `DivineRole.source` represents a substantive Trinitarian bridge rather than an analytic extraction from physical cosmology.

### Final Methodological Note
The formal investigation is **frozen**. No Lean modifications are required or permitted, as the philosophical strengthening demonstrates that the existing formal architecture of Γ accurately, elegantly, and non-circularly formalizes the deepest insights of the classical theistic tradition.

---

## 11. Adversarial Deepening and Inferential Gap Resolution

This section directly confronts the hardest philosophical objections and sharpens the inferential transitions underlying the three foundational principles, without relying on appeals to authority or confusing formalization with deductive demonstration.

### 11.1 GeneralContrastivePSR: Distinguishing Rationality from Metaphysical Intelligibility

#### 11.1.1 Reassessment of the Self-Defeat Argument
A standard apologetic move asserts that denying the PSR is self-defeating: *"To argue that reality is brute requires giving reasons, which presupposes the PSR."*
- **Rigorous Evaluation [R]:** This argument conflates **epistemic rationality** (the normative requirement that rational agents proportion belief to evidence and reasons) with **metaphysical intelligibility** (the ontic requirement that every contingent concrete state of affairs has an external sufficient reason).
- **The Coherence of Local Empiricism with Global Bruteness [I]:** A Humean or Russellian naturalist can consistently maintain:
  1. Epistemic norm: Beliefs about macroscopic facts, historical claims, and scientific laws require adequate evidence.
  2. Local causal intelligibility: Subsystems within spacetime are explained by antecedent physical states and natural regularities.
  3. Global bruteness: The totality of contingent concrete reality (the Big Bang, the cosmic initial condition, or the spacetime manifold as a whole) is an unexplained brute fact: *"The universe is just there, and that's all."* (Russell 1948).
  This position is **not self-contradictory in first-order logic**. Demanding evidence for beliefs does not formally entail that every objective contingent state of affairs in the cosmos must possess an ontic ground.

#### 11.1.2 The Strongest Independent Argument for Applying Restricted PSR to the Totality
If the self-defeat argument does not deductively refute the brute-fact thesis, why should `GeneralContrastivePSR` be accepted for the totality of $S$? The defense rests on two formidable arguments:

1. **The Argument from the Metaphysical Arbitrariness of Bounded Bruteness [R]:**
   If the total concrete system $S$ can actualize $\mathbf{C}_{\text{act}}$ rather than accessible alternative $\mathbf{C}_{\text{alt}}$ with zero ground, then uncaused, brute transitions are admitted into the ontology of being. But on what principled basis can bruteness be strictly quarantined to the cosmic boundary? If ungrounded modal divergence is real at the level of the totality, it becomes completely arbitrary to assert that ungrounded divergences cannot occur within intermediate nodes of $S$. Denying the PSR at the boundary while demanding strict causality inside reality is an *ad-hoc* boundary stipulation without metaphysical justification (Pruss 2006).

2. **The Argument from the Compositional Non-Self-Explanatoriness of Conditioned Systems (Leibniz) [P, R]:**
   In $S$, every node $n \in S.\text{Node}$ is contingent and conditionally dependent. A collection of conditionally dependent parts does not, by mere aggregation, generate an unconditioned explanation for the whole. As Leibniz argues in *On the Ultimate Origination of Things* (1697):
   > *"No matter how far back you go into earlier states, you will never find in them a full reason why there is any world rather than none, and why it is as it is... The reasons for the world therefore lie hidden in something extramundane."* **[P]**
   To claim that each part is conditionally explained while the whole collection of conditions is unexplained is to confuse an infinite deferral of explanatory debt with the satisfaction of that debt.

#### 11.1.3 Epistemological Classification
`GeneralContrastivePSR` is **not a demonstrable tautology** of logic, nor is its denial a formal contradiction. It is correctly classified as an **Inference to the Best Explanation (IBE) and a Substantive Rational Presupposition of Total Explanation**. It expresses the fundamental metaphysical wager of rational inquiry: that contingent actuality is objectively intelligible across modal alternatives.

---

### 11.2 PSR and Modal Collapse: Van Inwagen's Argument Reconstructed

#### 11.2.1 Canonical Five-Premise Reconstruction of the BCCF Argument
Peter van Inwagen (*An Essay on Free Will*, 1983, pp. 202–204) formulates the modal collapse argument against the unrestricted Principle of Sufficient Reason. The argument operates across five foundational premises:
1. **Premise 0 (Factivity of Explanation):** An explanation must be true; that is, if $q$ explains $p$, then $q$ is true. (A false proposition cannot serve as an explanation of any fact).
2. **Premise 1 (Existence of the BCCF):** The **Big Conjunctive Contingent Fact ($p$)** exists and is a true contingent proposition comprising the conjunction of all true contingent propositions.
3. **Premise 2 (Necessary-Contingent Explanatory Asymmetry):** A necessary proposition cannot explain a contingent proposition; that is, if $\Box q$, then $\neg(q \text{ explains } p)$. (An intrinsically necessary fact cannot account for why a contingent fact obtained rather than its contradictory).
4. **Premise 3 (Irreflexivity of Contingent Explanation):** No contingent proposition can serve as its own explanation; for any contingent $q$, $\neg(q \text{ explains } q)$. (Self-explanation of contingent facts is circularly empty).
5. **Premise 4 (Explanatory Distribution Principle):** If proposition $q$ explains a conjunction of propositions, then for every conjunct $r$ of that conjunction, $q$ explains $r$; that is:
   $$(q \text{ explains } (r \land s)) \implies (q \text{ explains } r)$$

Given these five premises, assume the universal PSR: every true contingent proposition (and specifically the BCCF $p$) has an explanation, say $q$.
- **The Dilemma on $q$:**
  - **Horn 1 ($q$ is necessary):** By Premise 2, a necessary proposition cannot explain contingent $p$. Contradiction.
  - **Horn 2 ($q$ is contingent):** If $q$ is contingent, then because $q$ explains $p$, by Premise 0 (Factivity) $q$ is true. Therefore, $q$ is a **true contingent proposition**. By Premise 1, the BCCF $p$ contains every true contingent proposition as a conjunct; hence $q$ is necessarily a conjunct of $p$. But by Premise 4 (Explanatory Distribution), because $q$ explains the conjunction $p$, $q$ must explain every conjunct of $p$. Since $q$ is a conjunct of $p$, it follows that $q$ explains $q$. But this directly contradicts Premise 3 (Irreflexivity).
- **Deductive Result:** The BCCF argument operates as a strict *reductio ad absurdum*: the conjunction of the unrestricted Principle of Sufficient Reason with the classical explanatory premises (P0–P4) produces a formal logical contradiction. It does not directly prove that no contingent proposition can have an explanation; rather, it proves that the unrestricted PSR is logically incompatible with the conjunction of factivity, asymmetry, irreflexivity, and distribution.

#### 11.2.2 Which Premise Agent-Causal Explanation Rejects
The agent-causal / personal theistic response in Γ does **not** rely solely on noting that reasons do not necessitate actions. Rather, it directly challenges **Premise 4 (The Explanatory Distribution Principle)** and the **Propositional Reduction of Agential Action**:
1. **Rejection of the Explanatory Distribution Principle [R, I]:**
   An explanation of a systemic whole does not distribute across every conjunct. In agent causation, an agent's intentional act $\text{Act}(A, \mathbf{C}_{\text{act}})$ teleologically explains why the contingent outcome $\mathbf{C}_{\text{act}}$ obtained, but it does **not** explain the conjunct asserting *that the agent chose $\mathbf{C}_{\text{act}}$* in the propositional sense of $q$ explaining $q$ (Pruss 2006).
2. **Category of the Explanans [R]:**
   In agent causation, the ultimate explainer is not an extrinsic proposition $q$, but a **personal substance acting for reasons** ($A \text{ acting for } R$). Subsuming free agency under propositional conjunctions treats the agent's act as just another passive event, creating an artificial self-referential trap.

#### 11.2.3 The Circularity / Substantive Commitment Limitation
Can agent-causal explanation resist the Explanatory Distribution Principle without circularly assuming the libertarian freedom that Tier 3 aims to establish?
- **Explicit Methodological Admission [R]:** **No.** Resisting Premise 4 requires taking the agent's act of choice as an unforced, self-determining primitive that cannot be decomposed into a further antecedent necessitating condition. If one does not already assume a libertarian agent-causal metaphysics, the distribution principle reasserts itself: the event of the agent choosing is itself a contingent fact in the world, and if the PSR applies to it, it demands an explanation, re-igniting the regress.
- **Philosophical Limitation:** Therefore, **agent causation cannot be claimed as an independent, neutral refutation of Van Inwagen's modal collapse**. Rather, it provides an internally coherent model of explanation that escapes modal collapse *if and only if libertarian agency is accepted as an irreducible, substantive metaphysical commitment*. Without that prior commitment, modal collapse remains an unresolved threat to any unconstrained PSR.

#### 11.2.4 The Internal Intelligibility of Choice and the Brute-Choice Challenge
Even if Premise 4 is rejected, an opponent will press: *If the agent's choice was not necessitated by antecedent reasons, why did the agent choose $\mathbf{C}_{\text{act}}$ rather than $\mathbf{C}_{\text{alt}}$? Does this not make the choice an unexplained brute stopping point?*
- **Teleological Intelligibility [R, I]:** The choice is not a random brute event (like an uncaused quantum fluctuation), because it is teleologically structured: the agent acts *for the sake of* good $G$. The reason $R$ teleologically explains the action, even though $R$ was compossible with choosing differently for reason $R'$.
- **Irreducible Primitive:** However, demanding a further contrastive reason that *guarantees* why reason $R$ was acted upon rather than $R'$ is equivalent to demanding a deterministic cause. The self-determining power of the will is an irreducible primitive of libertarian freedom. In Γ, this is formally acknowledged: `ActsFreely S T` is derived from explicit action-theoretic bridge structures (`agential_freedom_derived`, line 810), not from bare non-necessitation.

#### 11.2.5 Candidate F (Intellectualist Necessitation) Internally Eliminated Under Γ
A major historical alternative to libertarian divine creation is **Intellectualist Necessitation** (Leibniz, and in extreme form, Spinoza): the thesis that the source's supreme rationality, omniscient evaluation of perfections, or invariant nature uniquely and antecedently necessitates this particular universe.
- **Internal Elimination in the Kernel [T]:** In Γ, Intellectualist Necessitation is **deductively eliminated** by `deepened_intellectualist_evasion_closure` (`OntologicalIncompletenessTheorem.lean:3099`). If antecedent reasons uniquely fix the outcome in constitutive priority order, the contingent effect is rendered unconditionally inevitable, which directly contradicts the empirically given hypothesis `ContingentSystem S` (`intrinsic_rational_fixing_contradicts_contingency`, line 1445; `necessary_ground_cannot_rigidly_necessitate_contingent_system`, line 1273).
- **Distinction Between Internal Elimination and External Dispute [R]:** An external rationalist philosopher may dispute whether moral necessity truly destroys contingency, or may reject `ContingentSystem S` altogether in favor of Spinozist necessitarianism. That is an **external challenge to Γ's premises**. But **within the axiomatic framework of Γ**, Intellectualist Necessitation is strictly impossible: it cannot serve as a viable terminal solution because it destroys the contingency it was summoned to explain.

---

### 11.3 ExplanatoryTransmission: Establishing the Causal-to-Explanatory Inference

#### 11.3.1 Step-by-Step Causal Argument from *ST* I, q. 105, a. 5
Aquinas's doctrine of concurrent causation provides the classical foundation for transmitting efficacy from secondary causes to the First Cause:
1. **Step 1 (Conservation of Being and Power):** A created secondary cause $T'$ does not possess self-existent being (*esse per essentiam*); its being and operative powers are participated and continually conserved by the First Cause ($T$): *dat virtutem agendi et conservat eam in esse*. **[P]**
2. **Step 2 (Application to Action / Motio Divina):** An active power cannot move from potency to act on its own accord without being actualized and applied to operation by an actual agent: *applicat eam ad agendum*. **[P]**
3. **Step 3 (Immediate Concurrent Actuation of the Effect's Esse):** Being (*esse*) is the proper and universal effect of God. Since every creaturely action results in some new actualization of *esse* in reality, God must immediately concur not only in moving the agent, but in producing the very actuality of the effect: *Deus est causa omnis actionis prout eius virtute omnis alia virtus agit*. **[P]**
4. **Step 4 (Non-Competitive Co-Causation):** The secondary cause is the true, immediate cause of the specific effect according to its creaturely mode, while the First Cause is the primary, universal cause sustaining the entire event: *sicut idem effectus totus attribuitur instrumento, et totus etiam principali agenti*. **[P]**
5. **Step 5 (Explanatory Transmission):** Because the secondary cause's causal efficacy is completely dependent on and animated by the First Cause, any complete explanation of why an outcome obtained under secondary causality necessarily includes and terminates in the First Cause.

#### 11.3.2 Engaging the Durandist Challenge (Mere Conservationism)
Durando de Saint-Pourçain (*In Sent.* II, d. 1, q. 5) objected that God gives creatures powers and conserves those powers, but does **not** concur immediately in their actions (*concursus simultaneus*). On Durandus's view:
- God creates fire with the power to heat, and conserves the fire.
- When fire heats wood, the heating is caused exclusively by the fire; God does not directly act in the heating.
- Therefore, the explanation of the heating terminates in the fire; God's causality is merely remote and non-explanatory of the specific outcome.

**What the Thomistic Position Adds Against Durandus:**
Aquinas refutes mere conservationism by showing that it treats creatures as if they were independent demiurges once created. Creaturely powers are always in potency with respect to specific operations; no creature can reduce itself from potency to act without an already actualized mover. Furthermore, since *esse* is the primary reality of any effect, and no finite creature can produce *esse* *ex nihilo*, creaturely causation is strictly instrumental with respect to the universal ground of being. Thus, Durandus's insulation of creaturely causality is metaphysically impossible for participated beings.

#### 11.3.3 The Scope Parameter in Lean `def ExplanatoryTransmission`
Let us examine the exact Lean definition (`OntologicalIncompletenessTheorem.lean:1960`):
```lean
def ExplanatoryTransmission (S : ConcreteSystem.{u}) (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop) : Prop :=
  ∀ (T' : CandidateGround S) (w_alt : S.World),
    ExplainsOutcomeAt S T' ConstitutivePriority w_alt (SystemOutcomeAt S w_alt) →
    CompleteExplanatoryChain S ConstitutivePriority T' T →
    ExplainsOutcomeAt S T ConstitutivePriority w_alt (SystemOutcomeAt S w_alt)
```
- **Does this formulation overreach strict Thomistic concursus? [R]**  
  **Yes.** In Thomism, *concursus* is a specific ontological relation between God (as *Actus Purus* and *Ipsum Esse*) and created secondary substances. In Lean, `ExplanatoryTransmission` is formulated as an **unrestricted transitivity principle over any arbitrary `CandidateGround T'` and any arbitrary complete chain**.
- **Metaphysical Boundary:** This confirms that `ExplanatoryTransmission` in $\Gamma$ is **not a theorem of pure grounding logic**, but a **substantive metaphysical bridge parameter (`Tag: META`)**. It states as an explicit hypothesis that the grounding hierarchy of $S$ exhibits concurrent transmission rather than Durandist causal insulation.

---

### 11.4 TranscendentAgentialActionCorrespondence: Explaining the Actual Intentional Act

#### 11.4.1 Divine Nature and Contingent Actualization
How can a necessary divine essence be compatible with a genuinely contingent created system without collapsing into either necessitarian emanation (Spinoza) or brute indeterminism?
- **Thomas Aquinas (*ST* I, q. 19, aa. 3–4) [P]:**
  God's intellect and will are identical with His necessary essence. God necessarily wills His own infinite goodness. But finite creatures are not necessary to that goodness:
  > *"Cum bonitas Dei sit perfecta, et esse possit sine aliis, cum nihil ei perfectionis ex aliis accrescat; sequitur quod alia a se velle non sit ei necessarium absolute."*
  Because no creature adds anything to divine perfection, God wills creatures not by natural necessity, but by **free benevolence** (*ex libertate voluntatis*).
- **John Duns Scotus (*Ordinatio* I, d. 39) [P]:**
  Scotus introduces the formal logic of **synchronic contingency** (*potentia ad opposita sine successione*). At the timeless instant of divine willing, the divine will has the real, unactualized power to will non-$A$ at that very same instant. The contingency of creation is rooted in the sovereign active power of the divine will.

#### 11.4.2 The Decisive Inference: Why THIS Particular Concrete System $S$?
Here lies the most sensitive inferential transition in the theistic deduction:
*Why is this particular contingent configuration $S$ the content of an originating intentional act of the Divine Person acting as Source?*

We must rigorously separate three claims:
1. **Claim A (Generic Theistic Doctrine):** Classical theism asserts that the universe was created by divine will (*creatio ex voluntate*). This is historical-theological doctrine, not a cosmological derivation.
2. **Claim B (Eliminative Cosmological Derivation — Tier 1):** The cosmological argument in $\Gamma$ deductively proves that any ground capable of contrastively explaining contingent system $S$ without circularity, infinite regress, or rigid necessitation must be an **unforced personal agent** (`eliminative_existential_derives_unforced_personal_agent`, line 4187). **`[T]`**
3. **Claim C (The Integration Bridge — Tier 3):** The identification of the cosmological unforced agent's determination with the originating act of the Trinitarian Person acting as `DivineRole.source` via `TranscendentAgentialActionCorrespondence` (`line 2250`). **`[T]`**

**The Exact Demarcation:**
- Claim B is **deductively established** in the kernel under `GeneralContrastivePSR`.
- Claim C, however, is **not derived from bare cosmological necessity**. It represents the **theological integration** of the cosmological deduction with $\Gamma$'s Trinitarian ontology (`TrinitarianPersonalBridge`, `DivineTrinitarianAttributes.lean:270`).
- The assertion that the concrete system $S$ corresponds to the originating act of `DivineRole.source` requires two substantive commitments:
  a) That the transcendent agent identified in Tier 1 is identical in hypostatic role to the Source/Father in the Godhead;
  b) That the determination of concrete actuality is mediated by intentional action (`Logos.Agency.Act agent`).
- This transition is therefore an **explicit metaphysical integration**, not an analytic tautology.

#### 11.4.3 The Role of `UniversalOutcomePSR` vs. `GeneralContrastivePSR` in Tier 3
A critical formal distinction in the Lean kernel of Γ is that between `GeneralContrastivePSR` and `UniversalOutcomePSR`:
1. **`GeneralContrastivePSR S` (`OntologicalIncompletenessTheorem.lean:1049`):**
   Operates from the standpoint of the **actual world**: it asserts that for contingent concrete system $S$, there exists a candidate ground $T$ grounding actual concrete reality that supplies contrastive justification for the actual configuration against any divergent accessible alternative. This premise drives the eliminative exclusion of competing impersonal and internal branches in Tier 1.
2. **`UniversalOutcomePSR S ConstitutivePriority` (`OntologicalIncompletenessTheorem.lean:1872`):**
   ```lean
   def UniversalOutcomePSR (S : ConcreteSystem.{u}) (ConstitutivePriority : ...) : Prop :=
     ∀ w_alt : S.World, S.Accessible S.actualWorld w_alt →
       ∃ T' : CandidateGround S, ExplainsOutcomeAt S T' ConstitutivePriority w_alt (SystemOutcomeAt S w_alt)
   ```
   Operates across **all accessible counterfactual worlds**: it asserts that in every accessible world $w_{\text{alt}}$, the outcome obtained at $w_{\text{alt}}$ possesses *some* explanatory ground $T'$ in constitutive priority, without presupposing that it is the actual ground $T$.
3. **Independence and Necessary Role in Deriving `ActsFreely`:**
   Neither principle analytically entails the other:
   - `GeneralContrastivePSR` ensures that the actual world is contrastively grounded, but does not guarantee that counterfactual accessible worlds possess non-brute explanatory grounds.
   - If `UniversalOutcomePSR` were omitted, accessible counterfactual worlds could contain brute, ungrounded outcomes. Consequently, `MediatedExplanatoryScope` and `ExplanatoryTransmission` could not fire to establish that $T$ determines outcomes at counterfactual worlds ($T.\text{DeterminesOutcomeAt } T.\text{ground } w_{\text{alt}} \dots$).
   - Without determination at counterfactual worlds, the action-theoretic bridge `agential_determination_entails_choice_derived` (line 2200) cannot construct counterfactual choice (`T.ChoosesOutcomeAt`), collapsing the derivation of positive freedom (`ActsFreely S T`).
   - Therefore, `UniversalOutcomePSR` is an independently substantive cosmological hypothesis required by the explicit signature of Tier 3 (`eliminative_foundation_derives_free_personal_source_under_transmission`, line 4567).

---

### 11.5 Integrated Joint Coherence, Failure Modes, and Ranked Vulnerability Matrix

#### 11.5.1 The Joint Consistency of the Three Principles
Can the three principles jointly provide a coherent account of contingent actuality without falling into the five major philosophical traps? The answer requires applying the distinction between **internal elimination under Γ's premises** and **external contestability of those premises**:

1. **Does it treat the totality as a brute fact?**  
   - *Status within Γ:* **Internally Eliminated.** `GeneralContrastivePSR S` is an explicit declared hypothesis that guarantees that the contingent totality has an ungrounded transcendent ground that supplies contrastive explanation across accessible worlds. Bruteness is strictly excluded by `unjustified_alternative_fails_contrastive_at` (line 1116).
   - *External Contestability:* An external critic may reject `GeneralContrastivePSR S` at the cosmic boundary, accepting the universe as an ungrounded brute fact while maintaining local empirical science.
2. **Does it make the contingent outcome necessary?**  
   - *Status within Γ:* **Internally Eliminated.** The outcome is actualized through intentional agent causation (`TranscendentAgentialActionCorrespondence`), where divine reasons motivate without deductively necessitating the outcome, formally decoupling outcome determination from rigid necessity (`contingent_determination_constructs_positive_libertarian_choice`, CLFA:2712; `necessary_ground_cannot_rigidly_necessitate_contingent_system`, line 1273).
   - *External Contestability:* Philosophically, this resolution depends on resisting Van Inwagen's Explanatory Distribution Principle via agent causation. A necessitarian or determinist may contest whether unnecessitated choice is coherent.
3. **Does it make the act of choice itself an unexplained stopping point?**  
   - *Status within Γ:* **Internally Eliminated.** The choice is teleologically structured by reasons and apprehended goods (`AgentialActionRealization`, `ReasonsFavor`). It is not an unguided brute event.
   - *External Contestability:* Its self-determination is an irreducible primitive of libertarian agency. A determinist critic will continue to dispute whether an unnecessitated choice avoids being an unexplained stopping point.
4. **Does secondary causality collapse into occasionalism?**  
   - *Status within Γ:* **Internally Eliminated.** `ExplanatoryTransmission` and `CompleteExplanatoryChain` preserve secondary causes as real immediate operative agents producing real effects according to Thomistic concurrentism (*totus effectus ab utroque*), blocking occasionalism.
   - *External Contestability:* A follower of Malebranche may dispute creaturely efficacy, while a follower of Durandus may dispute simultaneous concurrence.
5. **Does it infer positive free choice merely from non-necessitation?**  
   - *Status within Γ:* **Internally Eliminated.** Freedom in Γ is not mere indeterminism; `ActsFreely S T` is derived in `agential_freedom_derived` (line 810) conditionally upon `AgentialActionRealization`, `choice_reflection`, and `AgentialCounterfactualChoiceBridge`. Alternative-choice power is supplied by these action-theoretic premises, not inferred from bare non-necessitation alone.

#### 11.5.2 Systematic Ledger of the Seven Explanatory Candidates
Under Γ's cumulative eliminative constraints, the seven exhaustive candidates are resolved as follows:
1. **Candidate A (Contingent Brute Fact):** *Status:* **INTERNALLY ELIMINATED** (fails `GeneralContrastivePSR S` and priority irreflexivity). Abandoning the demand for an explanation does not satisfy it.
2. **Candidate B (Circularity):** *Status:* **INTERNALLY ELIMINATED** (`consequence_dependent_mode_fails_well_foundedness`, line 1146). Circular dependence violates asymmetric well-foundedness.
3. **Candidate C (Infinite Regress):** *Status:* **INTERNALLY ELIMINATED** (`infinite_regress_cannot_self_ground`, line 182). Deferring dependency infinitely leaves conditionality ungrounded.
4. **Candidate D (Impersonal Rigid Necessitation):** *Status:* **INTERNALLY ELIMINATED** (`necessary_ground_cannot_rigidly_necessitate_contingent_system`, line 1273). Necessary ground plus rigid outcome determination destroys `ContingentSystem S`.
5. **Candidate E (Brute Randomness / Indeterminism):** *Status:* **INTERNALLY ELIMINATED** (`unjustified_alternative_fails_contrastive_at`, line 1116). Mere modal openness lacks contrastive explanation and positive agential control.
6. **Candidate F (Intellectualist Necessitation):** *Status:* **INTERNALLY ELIMINATED** (`deepened_intellectualist_evasion_closure`, line 3099). If antecedent reasons uniquely fix the outcome, contingency is extinguished.
7. **Candidate G (Necessary Free Personal Source):** *Status:* **THE UNIQUE SURVIVING CANDIDATE** (`eliminative_foundation_derives_free_personal_source_under_transmission`, line 4567). Structurally distinct from all competitors: necessary in existence (hence non-derivative), unforced in action (hence preserving contingency), and intentional in execution (providing contrastive explanation without brute chance).

#### 11.5.3 Ranked Vulnerability Matrix with Exact Residual Statements

| Principle | Rank | Primary Philosophical Strength | Primary Remaining Vulnerability | Smallest Defensible Propositional Statement of Remaining Metaphysical Gap |
| :--- | :--- | :--- | :--- | :--- |
| **`GeneralContrastivePSR`** | **1 (Most Robust)** | Deeply rooted in rational intelligibility; immune to standard modal collapse through agent-causal contrastive formulation. | An opponent can "bite the bullet" and assert that the cosmic totality is a brute fact while maintaining local empirical rationality. | **$\mathbf{Gap}_1$:** *The totality of contingent concrete reality requires an ontic contrastive explanation across accessible worlds, rather than being an ungrounded brute fact.* |
| **`TranscendentAgentialActionCorrespondence`** | **2 (Intermediate)** | Seamlessly unites classical divine freedom (*ST* I, q. 19; Scotus *Ordinatio* I, d. 39) with contemporary incompatibilist action theory. | Relies on the metaphysical coherence of libertarian agent causation and the Trinitarian identification of the cosmological agent with `DivineRole.source`. | **$\mathbf{Gap}_2$:** *The determination of concrete actuality by the ultimate ground is identical with the originating voluntary act of the Divine Person occupying `DivineRole.source` acting under libertarian freedom.* |
| **`ExplanatoryTransmission`** | **3 (Most Vulnerable)** | Coherent, historically venerable Thomistic concurrentism (*ST* I, q. 105, a. 5); prevents deistic fragmentation. | Susceptible to Durandist mere conservationism: a critic may argue that secondary causes possess autonomous efficacy that does not transmit its explanatory debt to the First Cause. | **$\mathbf{Gap}_3$:** *The explanatory efficacy of secondary causes in a complete constitutive priority chain is transitively grounded in and transmitted to the ultimate transcendent foundation.* |

---

### 11.6 Final Concluding Summary

#### 11.6.1 The Governing Question Resolved
At the close of this investigation, the governing question formulated in Section 1 receives its definitive resolution:
> **Which kind of ultimate ground can explain why a contingent concrete reality obtains rather than an accessible alternative, without leaving the divergence brute, entering circularity or infinite regress, or necessitating the outcome so that contingency disappears?**

#### 11.6.2 The Eliminative Necessity of the Free Personal Source
Γ's alternatives are not interchangeable answers to the problem of ultimate explanation. A brute contingent terminus abandons contrastive explanation; circularity and internal regress fail to provide an ultimate ground; rigid impersonal necessitation sacrifices genuine contingency; and brute indeterminism fails to explain the actualization contrastively. 

The **Necessary Free Personal Source** is the candidate that satisfies the joint requirements: necessary existence without necessary production of this particular contingent effect, ultimate grounding without an antecedent ground, and contrastive explanation through personal freedom. Its freedom is not an obstacle to the solution; it is the feature that makes the solution possible. 

The conclusion follows conditionally on Γ's declared premises, whose philosophical defence remains open to examination.

---

### 11.7 Change Log — Final Elimination Audit and Consistency Reconciliation

This change log documents the comprehensive revisions executed during the Final Elimination Audit, Precision Passes, and Consistency Audits:
- **Item 1 (Governing Elimination Principle):** Articulated the governing question (*"Which kind of ultimate ground can explain why a contingent concrete reality obtains rather than an accessible alternative, without leaving the divergence brute, entering circularity or infinite regress, or necessitating the outcome so that contingency disappears?"*) at the head of Section 1 (Executive Assessment, Section 1.0) and in the final conclusion (Section 11.6.1). Explicitly framed Γ's argument as a cumulative eliminative deduction where a satisfactory candidate must survive all constraints simultaneously.
- **Item 2 (Systematic Ledger of the Seven Explanatory Candidates):** In Sections 2, 4.2, 5, 7, 11.1, 11.2.5, and 11.5.2, presented Candidates A–F as internally eliminated failure modes, while establishing Candidate G (Necessary Free Personal Source) as the unique surviving candidate that reconciles necessary existence with non-necessitated contingent production.
- **Item 3 (Demarcation: External Rejection vs. Internal Elimination):** Systematically enforced throughout the document that while an external critic may reject one or more of Γ's premises (e.g. `GeneralContrastivePSR`, constitutive priority, or libertarian agency), such external dissent does not mean that the competing candidates satisfy Γ's requirements. Under Γ's premises, the alternatives fail deductively.
- **Item 4 (Van Inwagen / BCCF Factivity and Reductio Formulation):** Reconstructed Van Inwagen's Big Conjunctive Contingent Fact argument across all five canonical premises (P0: factivity; P1: existence of BCCF; P2: necessary-contingent explanatory asymmetry; P3: irreflexivity; P4: Explanatory Distribution Principle). Conceded that resisting distribution requires accepting libertarian agency as an independent metaphysical commitment.
- **Item 5 (Freedom Derivation vs. Action Bridges):** Clarified throughout Sections 1, 4.1, 11.2, and 11.5 that `ActsFreely` is conditionally derived in Γ from `AgentialActionRealization`, `choice_reflection`, and `AgentialCounterfactualChoiceBridge`, rather than being an analytic consequence of bare non-necessitation.
- **Item 6 (Tier 3 Signature Audit and UniversalOutcomePSR Analysis):** Corrected the Tier 3 signature in Sections 1, 6, 8, and 11.4 to match `eliminative_foundation_derives_free_personal_source_under_transmission` (line 4567), removing erroneous references to Tier 2 parameters (`PriorityGroundingHomomorphism`, `TrinitarianPersonalBridge`), and detailing the essential role of `UniversalOutcomePSR` (line 1872) in grounding counterfactual choice.
- **Item 7 (Line Citation Verification Across the Kernel):** Corrected all historical and formal line citations to match the active Lean codebase:
  - `infinite_regress_cannot_self_ground`: verified at **line 182** (corrected from stale 450);
  - `concrete_system_cannot_be_fully_internally_determined`: verified at **line 471** (corrected from stale 476);
  - `unjustified_alternative_fails_contrastive_at`: verified at **line 1116** (corrected from stale 605);
  - `consequence_dependent_mode_fails_well_foundedness`: verified at **line 1146** (corrected from stale 615);
  - `necessary_ground_cannot_rigidly_necessitate_contingent_system`: verified at **line 1273** (corrected from stale 675);
  - `deepened_intellectualist_evasion_closure`: verified at **line 3099** (corrected from stale 1665);
  - Master theorems: Tier 1 at **line 4187**, Tier 2 at **line 4367**, and Tier 3 at **line 4567**.
- **Strict Documentation-Only Guardrail:** This task was strictly documentation-only. No Lean files (`.lean`) were modified, no theorem statements or proofs were refactored, and no Lean kernel build or audit was rerun.

---

### 11.8 Inventory of Open Hypotheses and Unresolved Philosophical Objections

The following items record the exact external challenges to Γ's premises and the open hypotheses whose philosophical defense remains a matter of active debate:

#### 11.8.1 Open Formal Hypotheses in the Lean Signature
1. **`GeneralContrastivePSR S` (`line 1049`):** Assumes that the contingent concrete totality $S$ possesses an actual-world contrastive explanation across accessible worlds ($\mathbf{Gap}_1$).
2. **`UniversalOutcomePSR S ConstitutivePriority` (`line 1872`):** Assumes that every accessible counterfactual world possesses an explanatory ground, preventing brute counterfactual actuality and enabling the derivation of counterfactual choice (`ActsFreely S T`).
3. **`MediatedExplanatoryScope S T ConstitutivePriority` (`line 1940`):** Assumes that local secondary explanations in accessible worlds connect to the ultimate ground via complete constitutive priority chains.
4. **`ExplanatoryTransmission S T ConstitutivePriority` (`Tag: META`, `line 1960`):** Assumes that secondary-cause explanatory efficacy is transitively transmitted to the ultimate ground across complete priority chains ($\mathbf{Gap}_3$).
5. **`TranscendentAgentialActionCorrespondence S T` (`Tag: META`, `line 2250`):** Assumes that cosmological outcome determination corresponds to the originating voluntary act of the Divine Person occupying `DivineRole.source` via `AgentialActionRealization` ($\mathbf{Gap}_2$).

#### 11.8.2 External Philosophical Disputes Regarding Γ's Premises
1. **The Global Brute Fact Challenge (Hume, Russell):** An external naturalist may reject `GeneralContrastivePSR S` at the cosmic boundary, maintaining that while local physical events have antecedent causes, the totality of the physical universe is an ungrounded brute fact requiring no external explanation. (Internally, bruteness fails Γ's explanatory requirements).
2. **The Modal Collapse / Explanatory Distribution Challenge (Van Inwagen):** An external critic who rejects libertarian agent causation may argue that if the Explanatory Distribution Principle holds, or if an agent's choice is treated as an event in the world, the choice must either be determined by prior conditions or remain a brute, ungrounded event. (Internally, Γ's agent-causal semantics rejects distribution and affirms unforced teleological choice).
3. **The Mere Conservationism Challenge (Durando de Saint-Pourçain):** An external critic may reject `ExplanatoryTransmission`, asserting that God merely conserves creaturely substances and powers, but that the specific explanatory debt of secondary causal outcomes does not transmit to the First Cause. (Internally, Thomistic concurrentism is affirmed via the transmission bridge).
4. **The Hypostatic Role Identification Challenge:** A philosopher outside the Trinitarian tradition may accept the cosmological derivation of an unforced personal agent (Tier 1), but reject the bridge principle `TranscendentAgentialActionCorrespondence` identifying this agent with the Divine Person acting as `DivineRole.source`, viewing this identification as requiring revelation or distinct theological premises rather than cosmological argument. (Internally, Γ formalizes this as an explicit metaphysical integration bridge).

