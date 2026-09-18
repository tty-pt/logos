# Γ — The Deduction

**Generated document.** Produced by `scripts/build_deduction.py`; do not edit it by hand (sync rule in `AGENTS.md`). A philosopher can read Sections 1–4 and understand the argument, its inline obstructions and caveats, and its unresolved frontier; a logician can follow the appendices down to the kernel proof and the exact axiom footprint.

- **Lean source:** `formal/Logos/*.lean` — kernel-checked (`lake build` green, sorryAx 0)
- **Kernel footprints:** `formal/axiom_audit.json` (`#print axioms` per declaration — the exact transitive kernel axiom set, meta-logic included)
- **Axiom tags:** the `Tag:` line (`VOCAB`/`SEM`/`META`) on each axiom's Lean docstring
- **Dependency graph:** `formal/depgraph.json` (LeanDepViz, kernel)
- **Claim ledger:** [`formal/GAPMAP.md`](formal/GAPMAP.md) — statuses transcribed and *checked* against the kernel, never its source
- **Prose:** [`base.txt`](base.txt) (§0–§29) · [`poem.txt`](poem.txt) (P1–P10) · [`theorems/`](theorems/)

Regeneration: `python3 scripts/audit_footprints.py && python3 scripts/build_deduction.py`

---

## 1. What the argument tries to establish

Γ does not begin from an arbitrary propositional premise. It begins from a performatively given datum: an act of meaning is occurring. From that datum the argument extracts the maximum that is *un-deniable*, marking at every step whether a claim is **LOGICAL** (logic alone), **DEFINITIONAL** (follows from how Γ's concepts are constituted), **SEMANTIC** (a substantive semantic principle), or **METAPHYSICAL** (a substantive metaphysical bridge). No claim is called a deduction unless it is derived; no bridge is smuggled in unnamed. The conclusion layers of `base.txt` §0 are kept separate: the performatively undeniable, the logically undeniable, the transcendentally necessary, and the metaphysically necessary *if the corresponding bridge is shown*. God is not derived; the relevant steps are faith or deferred.

**Status vocabulary.** **LOGICAL** (logic alone) · **DEFINITIONAL** (follows from how Γ's concepts are constituted) · **SEMANTIC** (a substantive semantic principle) · **METAPHYSICAL** (a substantive metaphysical bridge) · **OPEN** (not currently derived) · **COUNTERMODEL** (a proposed inference fails in a hostile model). A `/ CONDITIONAL` qualifier marks a conclusion resting on a premise clause.

---

## 2. The argument at a glance

### 2.1 Classical and Logical Core

The logical core holds by classical propositional logic and semantic definition alone, independently of whether any agent is acting or meaning:

```text
classical core: truth / falsehood                          LOGICAL
classical core: right / wrong distinction                  LOGICAL
classical core: excluded middle & non-contradiction        LOGICAL
classical core: bivalence & strong truth                   LOGICAL
```

### 2.2 The Agency and Metaphysical Branch

From the performative meaning-bearing datum (`∃ s p, Act s p`), Γ reads off subjecthood, constitutive personhood, available alternatives, and semantic selection. Substantive metaphysical and relational bridges remain explicitly priced:

```text
performative meaning-act → subject                         DEFINITIONAL
performative meaning-act → Γ-person                        DEFINITIONAL
performative meaning-act → choice field (alternatives)     DEFINITIONAL
assertion → semantic selection                             DEFINITIONAL
deliberate choice → semantic selection                     DEFINITIONAL
deliberate choice → genuine choice                         DEFINITIONAL
genuine choice → free will                                 DEFINITIONAL
genuine choice (existence: F1b)                            SEMANTIC
performative meaning-act → Γ-necessary person / entity     DEFINITIONAL
necessary truth → necessary ground / reality (T7)          SEMANTIC
necessary reality → personal ground (T8)                   METAPHYSICAL
performative meaning-act → plurality                       METAPHYSICAL
plurality → love                                           METAPHYSICAL
performative meaning-act → God ?                           OPEN
```

### 2.3 The genuine-choice frontier

```text
PERFORMATIVE MEANING-ACT
        │
        └──→ Strong Act
              ├──→ ChoiceField              [DEFINITIONAL]
              │
              └──→ Genuine Choice           [A14 / SEM]
                         │
                         └──→ FreeWill / FreeSubject

A14 (AxIntentionalChoice):
    Act(s,p) → ∃ q, Chooses(s,p,q)

    ADOPTED as a substantive SEMANTIC constitutive principle
    Weakest sufficient bridge identified at the pointwise level

A13 (AxActPolarity):
    Act(s,p) → Means(s,¬p)

    Optional stronger contradictory-negation polarity principle
    Strictly entails A14 (act_polarity_implies_intentional_choice)
```

#### Adopted Constitutive Semantic Principle: AxIntentionalChoice (A14)

The hostile-model audit definitively proved that Strong Act is orthogonal to Genuine Choice under the pre-A14 primitives (`PreA14GammaTheory ⊬ genuine choice`, formalized by `act_orthogonal_to_genuine_choice_in_full_theory`). Genuine choice is not derivable from Strong Act in the pre-A14 theory. Γ now explicitly adopts the constitutive thesis as A14, a substantive semantic commitment:

> **Genuine choice is constitutive of intentional action.**

An event can be mechanical, involuntary, or merely causally produced (`act`); but an **intentional action** (`Act`), qua intentional action, is an action performed through the agent's apprehension and co-meaning of an incompatible alternative (`Chooses s p q`). Hence, genuine choice is constitutive of Strong Act, while remaining orthogonal to raw/weak performed events (`act`), preserving the separation proven in `CountermodelWeakActWithoutMeaning`.

This constitutive commitment is formalized as the substantive semantic axiom:

$$\text{AxIntentionalChoice} : \forall (s : \text{Subject}) (p : \text{Prop}),\; \text{Act}(s,p) \implies \exists q,\; \text{Chooses}(s,p,q)$$

Under AxIntentionalChoice:

$$\text{Act}(s,p) \longrightarrow \text{Chooses}(s,p,q) \longrightarrow \text{FreeWill}(s) \iff \text{FreeSubject}(s)$$

Thus F1b is closed under `{AxIntentionalChoice, Initiates, Means, State, Subject}` (`genuineChoice_exists_of_act_constitutive`, `freeWill_exists_of_act`, `freeSubject_exists_of_act`).

**Distinction between Derivation and Adoption:**
1. `Pre-A14 Γ ⊬ genuine choice` is **formally established** by the machine-checked hostile models `HostileSemantics.hostileAgencyInstance` and `HostileSemantics.fullTheoryHostileInstance` (`act_orthogonal_to_genuine_choice_in_full_theory`).
2. `Pre-A14 Γ + AxIntentionalChoice ⊢ genuine choice` is **formally established** by the kernel theorem `Choice.genuineChoice_exists_of_act_constitutive`.
The hostile countermodels remain valid against the pre-A14 theory, demonstrating why genuine choice is an authentic semantic commitment rather than a theorem of raw agency.

#### Four-Model Diagnostic Hierarchy (M0–M3)

| Level | Model Description | Act s p | ChoiceField s p q | Chooses s p q | FreeWill s | FreeSubject s | Verdict |
|---|---|---|---|---|---|---|---|
| M0 | Weak Act (`CountermodelWeakActWithoutMeaning`) | FALSE | FALSE | FALSE | FALSE | FALSE | Event occurs without meaning or strong Act |
| M1 | Factive Strong Act (`hostileAgencyInstance`) | TRUE | TRUE | FALSE | FALSE | FALSE | Strong Act & ChoiceField hold; Chooses fails by veridicality |
| M2 | Branching Initiation (`ModelM2BranchingInitiation`) | TRUE | TRUE | FALSE | FALSE | FALSE | Non-trivial state branching holds; Chooses still fails |
| M3 | Contrastive Agency (`ModelM3ContrastiveAgency`) | TRUE | TRUE | TRUE | TRUE | TRUE | Polar agency validated (AxActPolarity); FreeSubject valid |

#### Six-Attack Audit on Deriving Polarity from Strong Act

| Attack Vector | Candidate Principle | Outcome Classification | Hostile Witness / Model | Exact Separating Valuation & Analysis |
|---|---|---|---|---|
| **Attack 1 (Existential Act Polarity)** | `(∃ s p, Act s p) → ∃ s p, Act s p ∧ Means s (¬p)` | **C. REFUTED BY HOSTILE MODEL** | `fullTheoryHostileInstance` (`not_entails_existential_polarity_from_full_theory`) | Valuation: `s = false, p = True`. In veridical semantics (`Means s p := p`), `Act s p` forces $p$, while `Means s (¬p)` forces $\neg p$, making dual co-meaning an absolute contradiction ($p \land \neg p \equiv \bot$). |
| **Attack 2 (Semantics of Means)** | `Act s p → ∃ q, Means s q ∧ Incompatible p q` | **C. REFUTED BY HOSTILE MODEL** | `CountermodelVeridicalMeaning.Single` (`Single.no_genuine_choice`, `genuineChoice_requires_error_possibility`) | Valuation: `p = True`. If meaning is factive, any incompatible pair $p, q$ would require $p \land q \land \neg(p \land q) \equiv \bot$. Factive meaning mathematically excludes co-meaning incompatible alternatives. |
| **Attack 3 (Contrastive Initiation)** | `Branches (fun w w' => ∃ p, Initiates s w w' p) → ∃ q, Means s q ∧ Incompatible p q` | **C. REFUTED / D. REDUNDANT** | `ModelM2BranchingInitiation` (`m2_diagnostic_separation`) | For physical branching: **C. REFUTED** by Model M2 (`w = false ∧ w' ∈ {true, false}`); physical state transitions are extensional and do not force mental co-meaning. For intentional contrast: **D. REDUNDANT** (extensionally equivalent to A13). |
| **Attack 4 (DeliberateChoice Decomposition)** | `Act s p → ∃ q, DeliberateChoice s p q` | **C. REFUTED BY HOSTILE MODEL** | `hostileAgencyInstance` (`deliberateChoice_negation_decomposition`) | Valuation: `s = false, p = True, q = False`. Executive selection `Selects s p (¬p)` holds by assertion, but alternative awareness `Means s (¬p)` fails by veridicality. Deliberation fails strictly at the missing cognitive horn. |
| **Attack 5 (Performative Doubt & Retorsion)** | `(Asserts speaker NoAct → False) → ∃ s p, Doubts s p` | **C. REFUTED BY HOSTILE MODEL** | `TwoPersons.retorsion_does_not_imply_doubt` | Valuation: `NoAct := ¬ ∃ s p, Act s p`. Retorsion establishes that denying action is performatively self-refuting, but refutation of an assertion does not populate the agent's mind with dual contradictory contents. |
| **Attack 6 (C101 Normative Bivalence)** | `(Act s p ↔ Asserts s p ∨ Incorrect s p) → ∃ s p, Means s p ∧ Means s (¬p)` | **C. REFUTED BY HOSTILE MODEL** | `hostileAgencyInstance` (`hostile_c101`) | Valuation: `s = false, p = True`. Bivalent partition classifies the normative status of the posited content $p$ relative to reality; it tracks the world, not dual cognitive representations in the same subject $s$. |

**Philosophical resolution of intentional initiation:**
- **Case A (Already derivable from existing Strong Act in pre-A14 theory):** REFUTED by the all-scope hostile model `HostileSemantics.fullTheoryHostileInstance`.
- **Case B (Initiates vocabulary is under-specified):** EVALUATED & BOUNDED. Model M2 shows that even when `Initiates` branches dynamically across states (`Branches`), physical transitions do not force cognitive co-meaning of the unchosen alternative in `Means`.
- **Case C (Adoption of Constitutive Semantic Principle A14):** ESTABLISHED. Strong Choice is not an executive property of state transitions, but a cognitive property of contrastive agency. In the pre-A14 theory, Strong Act does not entail Genuine Choice; Γ therefore adopts `AxIntentionalChoice : Act s p → ∃ q, Chooses s p q` as an authentic, substantive **SEMANTIC constitutive principle** (`Tag: SEM`), with `AxActPolarity : Act s p → Means s (¬p)` remaining an optional stronger contradictory-negation principle.

**Free Subject vs. Personhood:**
- `FreeSubject s := ∃ p q, Chooses s p q` is definitionally equivalent to `FreeWill s` (`Choice.freeSubject_iff_freeWill`).
- Every free subject is an ontological person (`Choice.freeSubject_implies_person`: `FreeSubject s → Person s`, `{Means, Subject}`).
- But ontological personhood does NOT imply a free subject: in `TwoPersons`, two distinct persons exist while neither possesses free will (`HostileSemantics.TwoPersons.person_does_not_imply_freeSubject`).


#### A Fronteira de A14: O Que a Teoria Existente Já Fornece vs. O Abismo Cognitivo

Para qualquer ato intencional forte `Act s p`, as definições analíticas e a lógica de Γ já fornecem rigorosamente:
```text
Act s p
  ├─→ Means s p                  [Definição analítica de Act: corno intencional]
  ├─→ ∃ w w', Initiates s w w' p  [Definição analítica de Act: iniciação causal]
  └─→ ChoiceField s p (¬p)       [Lógica pura: Incompatible p (¬p)]
```

Contudo, a ação intencional `Act s p` isolada **não** acarreta por si mesma:
- `¬ Act s (¬p)` (necessário para a exclusão executiva em `Authors s p (¬p)`);
- `Asserts s p` (necessário para a seleção assertiva em `Selects s p (¬p)`);
- e, crucialmente, **não acarreta `Means s (¬p)` nem `Means s q` para nenhum `q` incompatível**.

A proposição não-resolvida que separa a ação da escolha genuína é unicamente:
$$\text{Act}(s, p) \implies \exists q : \text{Prop},\; \text{Means}(s, q) \land \text{Incompatible}(p, q)$$
Esta é a ponte em falta da **Representação Contrastiva** (o segundo corno cognitivo).

Como `Chooses s p q := Means s p ∧ Means s q ∧ Incompatible p q` e `Act s p` já fornece analiticamente `Means s p`, o axioma substantivo A14 (`AxIntentionalChoice : Act s p → ∃ q, Chooses s p q`) é **logicamente e definicionalmente equivalente à ponte de Representação Contrastiva** sobre a teoria existente.

Portanto, a fronteira epistemológica de A14 fica perfeitamente isolada:
$$\text{Definições} + \text{Lógica} \quad \vdash \quad \text{Act}(s, p) \implies \text{ChoiceField}(s, p, \neg p)$$
$$\text{Definições} + \text{Lógica} \quad \not\vdash \quad \text{Act}(s, p) \implies \exists q,\; \text{Means}(s, q) \land \text{Incompatible}(p, q)$$

```text
ALTERNATIVA OBJETIVA (ChoiceField)   ───X───>   ALTERNATIVA COGNITIVA (Chooses / Means q)
```
Nenhuma propriedade puramente lógica ou analítica da semântica atual de `Means` é estritamente mais fraca do que A14 e capaz de derivar esta ponte: a co-significação de alternativas é o compromisso semântico irredutível de A14.

### Primitive Boundary: Means and Incompatibility

Means is primitive and presently uninterpreted.

Incompatible is logical:
    Incompatible p q := ¬(p ∧ q)

Thus Γ currently contains:

    cognitive relation: Means(s,p)
    objective relation: Incompatible(p,q)

but no primitive relation connecting the two.

The unresolved A14 bridge is precisely that connection.

```text
The current formalization contains no primitive relation connecting
objective incompatibility with cognitive representation.

The unresolved bridge is therefore not recoverable from either:
  (a) the current semantics of Means, or
  (b) the current logic of Incompatible.
```

#### Audit: Semantics of Incompatible vs. Cognitive Representation

1. **Is `Incompatible` primitive?** NO. In `formal/Logos/Alternatives.lean:17`, `Incompatible p q := ¬ (p ∧ q)` is a pure definition of propositional logic (`sorryAx = 0`, axiom footprint `{}`).
2. **Seven Conceptual Dimensions of Incompatibility:**
   - *Logical Incompatibility:* $\neg(p \land q)$ (truth-functional non-conjunction; the formal definition in Γ).
   - *Truth Incompatibility:* $p$ and $q$ cannot co-obtain in reality.
   - *Action Incompatibility:* An agent cannot execute both acts simultaneously.
   - *Goal Incompatibility:* The realization of $p$ frustrates or precludes goal $q$.
   - *Practical Opposition:* Volitional commitment to $p$ versus active rejection of $q$.
   - *Counterfactual Exclusivity:* In any accessible counterfactual world realizing $p$, $q$ does not obtain.
   - *Cognitive Alternative:* Both incompatible propositions $p$ and $q$ are apprehended, entertained, or represented in consciousness (`Means s p ∧ Means s q ∧ Incompatible p q`).
3. **Sufficiency of Logical Relation:** Tested against hostile models (`CountermodelVeridicalMeaning.Single` and `ModelM2BranchingInitiation`), bare objective incompatibility $\neg(p \land q)$ does not imply that either proposition is represented (`Means s q`), considered, possible, actionable, chosen, rejected, or cognitively available.
4. **Search for Deeper Structure in Γ:** Neither modal possibility (`Logos.Modal`), dynamic physical state branching (`ModelM2BranchingInitiation`), normative bivalence (`Logos.Order` C101), nor teleological goals (`TeleologicalAct`) can derive `Means s q` for an incompatible $q$ without already presupposing cognitive representation.
5. **Candidate Principles & Relation to A14:**
   - `Incompatible p q → Means s q`: Strictly stronger than A14 ($P > \text{A14}$), cognitively explosive (forces representation of every incompatible proposition / contradiction), rejected.
   - `Initiates s w w' p ∧ Initiates s w w'' q`: Independent of A14 ($P \perp \text{A14}$); extensional state branching fails to force mental co-meaning (refuted by Model M2).
   - `Means s p → Means s (¬p)`: Equivalent to **A13** (`AxActPolarity`), NOT A14.

#### Strength Relation: A13 vs. A14

```text
A13 : Act s p → Means s (¬p)
             ↓
A14 : Act s p → ∃q, Chooses s p q
```

A13 is **strictly stronger** in general than A14 because A14 permits an arbitrary incompatible alternative $q$ (e.g. contrasting positive actions such as North vs. East, as formally separated in `ContrastiveSeparation.contrastive_strictly_weaker`), whereas A13 forces the alternative to be the formal contradictory negation $\neg p$.

### Universal vs. Existential Constitutive Principle

Universal A14:
    ∀s p, Act s p → ∃q, Chooses s p q

Existential weakening:
    (∃s p, Act s p) →
      ∃s p q, Chooses s p q

The latter is sufficient for F1b.

Its relation to A14 must be established formally.

#### Audit: A14 vs. A14∃ (Formal Results)

1. **Formalization:**
   - Universal A14 (`AxIntentionalChoice`): `∀ (s : Subject) (p : Prop), Act s p → ∃ q, Chooses s p q`
   - Existential A14 (`existential_intentional_choice`): `(∃ s : Subject, ∃ p : Prop, Act s p) → ∃ s : Subject, ∃ p q : Prop, Chooses s p q`
2. **Entailment `A14 → A14∃`:** PROVEN by pure logic (`intentional_choice_implies_existential_choice`).
3. **Converse `A14∃ → A14`:** REFUTED BY HOSTILE MODEL (`ExistentialChoiceSeparationModel.existential_not_entails_universal`). In a two-agent model where one agent chooses and another acts unilaterally without choice, `A14∃` holds while universal `A14` fails.
   - Therefore: **`A14∃ < A14` (strictly weaker).**
4. **Relation to Target F1b:** `existential_choice_iff_f1b` proves that `A14∃` is **DEFINITIONALLY EQUIVALENT** to target F1b (`(∃ s p, Act s p) → ∃ s, FreeWill s`) under `FreeWill s := ∃ p q, Chooses s p q` (`rfl`).
5. **Sufficiency for Free Will:** YES (`freeWill_exists_of_existential_choice`).
6. **Pre-A14 Derivability:** NO. `act_orthogonal_to_existential_contrastive_agency_in_full_theory` in `fullTheoryHostileInstance` proves that `A14∃` is independent of the pre-A14 theory.
7. **Transitivity with A13:**
```text
A13 : Act s p → Means s (¬p)
       ↓
A14 : ∀ s p, Act s p → ∃ q, Chooses s p q
       ↓
A14∃ : (∃ s p, Act s p) → ∃ s p q, Chooses s p q  (≡ F1b)
```
`act_polarity_implies_existential_choice` verifies direct entailment `A13 → A14∃`.

### Systematic Attack on F1b and the Mathematical Frontier

Target F1b: `(∃ s p, Act s p) → ∃ s, FreeWill s` (definitionally equivalent to `A14∃`).

We seek whether there is a genuinely more primitive semantic principle $B$ such that:
$$\text{Pre-A14 } \Gamma + B \vdash \text{F1b}$$
while $B$ is not definitionally or propositionally equivalent to F1b/A14∃, and not merely A14/A13 under another name.

#### The 11-Way Candidate Classification

| Candidate Direction | Formulation / Schema | Strict Classification | Hostile Witness / Model | Formal Mechanism & Status |
|---|---|---|---|---|
| **1. Doubt / Propositional Polarity** | `Doubts s p := Means s p ∧ Means s (¬p)` | **INCOMPARABLE** (datum) / **STRICTLY STRONGER THAN F1b** (act bridge); **REFUTED BY HOSTILE MODEL** | `fullTheoryHostileInstance` (`Means s p := p`) | As an unprompted datum (`DoubtingDatum : ∃ s p, Doubts s p`), it is incomparable with F1b (entails FreeWill without requiring an intentional act; not entailed by F1b). As an act bridge (`Act s p → ∃ q, Doubts s q`), it strictly entails F1b but forces contradictory negation $\neg p$. In pre-A14 Γ, doubt is identically False in veridical models (`p ∧ ¬p ↔ False`). |
| **2. Self-Reference / Retorsion** | `SelfDenialOfChoice s p := Act s p ∧ (p ↔ ∀ q, ¬ Chooses s p q)` | **REFUTED BY HOSTILE MODEL** | `DelusionalSelfChoiceModel` & `SelfDenialOfChoiceModel` | An agent can truthfully perform an act with content 'this act contains no genuine choice' (`p = True`), and in fact possess zero choice (`∀ q, ¬ Chooses s p q`). Performative retorsion fails to populate the cognitive field with alternative contents. |
| **3. Intentionality as such** | `Intentional s := ∃ p, Means s p` (or `Act s p`) | **REFUTED BY HOSTILE MODEL** | `fullTheoryHostileInstance` (`act_orthogonal_to_genuine_choice_in_full_theory`) | Present in pre-A14 Γ (`T5_personExists`, `act_implies_intentional`). Survives in hostile models where an agent acts intentionally with single/veridical content, completely decoupled from genuine choice. |
| **4. Rationality / Judgment** | `Judge s := Asserts s (¬ N_T ∧ ¬ N_F)` | **REFUTED BY HOSTILE MODEL** | `fullTheoryHostileInstance` (`JUDGE_HAS_CHOICE_FIELD`) | Judgment derives an *objective* alternative field `ChoiceField s p (¬p)` (`Means s p ∧ Incompatible p (¬p)`), but does NOT derive the second cognitive horn `Means s (¬p)`. The judge remains free of choice in factive models. |
| **5. Alternative-Generation** | `∃ q, Incompatible p q` | **REFUTED BY HOSTILE MODEL** | `CountermodelVeridicalMeaning.Single` | Pure logic: for any $p$, $q := \neg p$ satisfies `Incompatible p (¬p)`. Being a tautology, it holds in all models, including single-meaning deterministic models, and cannot force mental representation of $q$. |
| **6. Modal Openness / Branching** | `∃ w w' : State, Initiates s w w' p ∧ ∃ w'' : State, Initiates s w w'' q` | **REFUTED BY HOSTILE MODEL** | `ModelM2BranchingInitiation` (`counterfactual_branching_not_entails_means`) | Physical or modal non-determinacy in causal initiation branches the state space without forcing internal intentional representation `Means s q` of the non-actualized branch. |
| **7. Contrastive Explanation** | `ExplainsContrast s p q := Act s p ∧ Means s q ∧ Incompatible p q` | **REDUNDANT / RENAMED F1b** (if cognitive) / **REFUTED BY HOSTILE MODEL** (if objective) | `ModelM2BranchingInitiation` & `fullTheoryHostileInstance` | If defined with cognitive representation `Means s q`, existential contrastive agency is definitionally equivalent to F1b (`existential_contrastive_agency`). If defined purely objectively without `Means s q`, it is refuted by M2. |
| **8. Reasons-Responsive Agency** | `ReasonResponsiveAct s p r := Act s p ∧ Means s r ∧ (r → p)` | **REFUTED BY HOSTILE MODEL** | `hostileReasonResponsiveInstance` (`reason_responsiveness_not_entails_contrastive_agency`) | Acting for a sufficient reason in the actual world does not require occurrent representation of contrary reasons in thought. Counterfactual dispositions do not populate actual occurrent `Means`. |
| **9. Authorship / Settlement** | `Authors s p q := Act s p ∧ ¬ Act s q ∧ Incompatible p q` | **DERIVED** in pre-A14 Γ; **REFUTED BY HOSTILE MODEL** for F1b | `fullTheoryHostileInstance` (`authors_not_entails_rejected_horn_meaning`) | Raw authorship is derived in pre-A14 Γ (`act_implies_authors`), but fails to derive F1b because non-action on $\neg p$ does not imply meaning $\neg p$. 'Deliberate Authorship' (`Authors ∧ Means s q`) is **REDUNDANT / RENAMED F1b**. |
| **10. Deliberation** | `Deliberates s p q` vs `DeliberateChoice s p q` | **REDUNDANT / RENAMED F1b** (raw) / **STRICTLY STRONGER THAN F1b** (executive) | `hostileAgencyInstance` (`deliberateChoice_negation_decomposition`) | Raw deliberation (`deliberates_iff_chooses`) is definitionally identical to `Chooses`. Executive deliberation (`DeliberateChoice := Selects ∧ Means s q`) strictly entails F1b and is refuted by veridical models. |
| **11. Unrealized Possibilities** | `∃ s p, Means s p ∧ ¬p` (non-factive intentionality) | **REFUTED BY HOSTILE MODEL** | `UnrealizedPossibilityModel` (`unrealized_not_entails_freeWill`) | Representing a false or unrealized proposition allows error in thought, but does not force co-meaning mutually exclusive alternatives. An agent representing a falsehood does not thereby possess genuine choice among alternatives. |

#### The Exact Mathematical Frontier of Genuine Choice

In `formal/Logos/Choice.lean`, the exact mathematical structure required to close F1b is formally isolated:

```lean
def MissingCognitiveHorn (s : Subject) (p : Prop) : Prop :=
  ∃ q : Prop, Means s q ∧ Incompatible p q

theorem means_missing_horn_iff_chooses (s : Subject) (p : Prop) :
  Means s p ∧ MissingCognitiveHorn s p ↔ ∃ q, Chooses s p q

theorem freeWill_iff_means_missing_horn :
  (∃ s : Subject, FreeWill s) ↔ ∃ s : Subject, ∃ p : Prop, Means s p ∧ MissingCognitiveHorn s p

theorem act_missing_horn_implies_chooses (s : Subject) (p : Prop) :
  Act s p ∧ MissingCognitiveHorn s p → ∃ q, Chooses s p q

theorem act_missing_horn_iff_chooses (s : Subject) (p : Prop) (hAct : Act s p) :
  MissingCognitiveHorn s p ↔ ∃ q, Chooses s p q
```

The mathematical frontier is completely rigid:
1. **First Horn Provided by Act:** For any intentional act `Act s p`, pre-A14 Γ supplies the first cognitive horn: `Means s p` (via `act_decomposition`).
2. **Objective Incompatibility Provided by Logic:** For any proposition $p$, logic supplies an incompatible partner: $q := \neg p$ with `Incompatible p (¬p)` (`incompatible_self_negation`).
3. **The Irreducible Missing Ingredient:** The entire axiomatic gap of F1b is precisely `MissingCognitiveHorn s p`, i.e., `∃ q, Means s q ∧ Incompatible p q`.
4. **No Pre-A14 Structure Supplies This Horn:** Neither causal initiation (`Initiates`), nor logical negation (`¬`), nor assertion (`Asserts`), nor judgment (`Judge`), nor authorship (`Authors`), nor non-factivity (`Means s p ∧ ¬p`) supplies `Means s q` for an incompatible $q$.
5. **Conclusion:** Any principle $B$ that derives F1b without goal-containment either introduces a substantive cognitive commitment strictly stronger than F1b (such as A13 or DoubtingDatum), or is equivalent to F1b under definitional expansion (such as A14∃ or Deliberates). No weaker or decoupled existing structure in Γ can derive genuine choice.

### The Frontier Meta-Theorems (Relative Completeness, General Independence, and Contrastive Collapse)

The frontier separating pre-A14 agency from genuine choice is not merely an empirical collection of failed attempts. It is a **rigorous mathematical boundary** governing the formal language of Γ, established by three meta-theorems:

#### 1. Claim A — Exact Relative Completeness Theorem

Relative to the pre-A14 vocabulary and axioms, target F1b is provably equivalent to the conditional existence of the missing cognitive horn over the performative action datum:

```lean
theorem f1b_iff_missing_cognitive_horn :
  ((∃ s : Subject, ∃ p : Prop, Act s p) → ∃ s : Subject, FreeWill s) ↔
  ((∃ s : Subject, ∃ p : Prop, Act s p) → ∃ s : Subject, ∃ p : Prop, Means s p ∧ MissingCognitiveHorn s p)
```

- **Kernel Footprint:** `{Initiates, Means, State, Subject}` (VOCAB only; zero non-logical axioms).
- **Transparent Equivalence:** Because `FreeWill s ↔ ∃ p, Means s p ∧ MissingCognitiveHorn s p` holds by pure definition, F1b is transparently the requirement that intentional action be accompanied by the mental co-representation of an incompatible alternative. Closing F1b without supplying `MissingCognitiveHorn` is a logical impossibility.

#### 2. Claim B — Parameterized Hostile Model Family (General Independence)

In `formal/Logos/HostileSemantics.lean` (`ParameterizedHostileFamily`), the hostile countermodel is elevated from an isolated instance to a **reusable parameterized model family**:

$$\forall R : \text{Bool} \to \text{Prop} \to \text{Prop},\; \text{AdmissiblePreA14Meaning}(R) \land \text{HornFreeMeaning}(R) \implies \text{PreA13FullTheory}(\text{model}(R)) \land \neg \text{F1b}$$

- **Admissibility:** Any relation where subjects mean true performed contents (e.g. $R(\text{true}, \text{True})$).
- **Horn-Free Condition:** $\forall s\,p\,q,\; R(s,p) \land R(s,q) \implies \neg \text{Incompatible}(p,q)$ (i.e. the agent never simultaneously entertains mutually exclusive propositions).
- **Scope:** Captures veridical semantics ($R(s,p) := p$), single-content intentionality ($R(s,p) := (p = \text{True})$), and any conjunctive belief filter.
- **Result:** Pre-A14 $\Gamma \nvdash \text{F1b}$ across the entire family.

#### 3. Claim C — Model-Transformation Preservation & Blocker Analysis

In `formal/Logos/HostileSemantics.lean` (`ModelTransformationCollapse`), we define the generic semantic transformation:

$$\text{Collapse}(M) := M[\text{Means} \mapsto \lambda s\,p,\; M.\text{Means}(s,p) \land p]$$

1. **Universal Choice Destruction:** For EVERY model $M$, $\forall s\,p\,q,\; \neg \text{Chooses}(\text{Collapse}(M), s, p, q)$ (`collapse_destroys_all_choice`).
2. **Blocker Analysis for Unconditioned $T_0$:** Does `Collapse(M)` preserve the unconditioned 12-axiom theory $T_0$ for arbitrary models? **NO.**
   - *Axiom 1 Blocker (`nonfactive_act_blocks_collapse`):* If all intentional acts in $M$ are non-factive ($p = \text{False}$), `FullAct` collapses to false, refuting Axiom 1 (Act Datum).
   - *Axiom 2 Blocker (`nonfactive_plurality_blocks_collapse`):* If a person in $M$ only means non-factive contents, `FullPerson` collapses to false, refuting Axiom 2 (Plurality of Persons).
3. **Full Preservation Theorem on Factive Models:** On `FactivePreA14Theory` (where intentional acts and personhood meanings are realized factively), `ContrastiveCollapse` **provably preserves every one of the 12 pre-A14 axioms** (`collapse_preserves_preA14`).
4. **Canonical Witness:** `fullTheoryHostileInstance_is_factive` formally verifies that the canonical hostile instance is factive.

#### 4. Claim D — Structural Impossibility for Contrastive-Blind Extensions

Let $B$ be any extension of the theory satisfying the model-preserving blindness condition:
$$\text{PreA14ContrastiveBlind}(B) := \forall I,\; \text{FactivePreA14Theory}(I) \land B(I) \implies B(\text{ContrastiveCollapse } I)$$

The kernel formally proves the model-theoretic impossibility theorem (`blind_extension_cannot_derive_f1b`):

$$\text{PreA14ContrastiveBlind}(B) \land \text{PreA14Consistent}(B) \implies \exists M,\; \text{PreA13FullTheory}(M) \land B(M) \land (\exists s\,p,\; \text{FullAct } M\,s\,p) \land \neg (\exists s,\; \text{FullFreeWill } M\,s)$$

> **Exact Impossibility:** $\text{Pre-A14 }\Gamma + B \nvdash \text{F1b}$. Every consistent contrastive-blind extension admits a choice-free model satisfying the entire pre-A14 theory.

#### 5. Claim E — Expressivity Boundary & Non-Definability Theorem

In `formal/Logos/HostileSemantics.lean` (`ExpressivityBoundary`), we construct the inductive syntax `BlindFormula (Subject State Entity : Type)` decoupled from concrete model instances, with constructors for:
- Propositional truth connectives (`top`, `bot`, `not`, `and`, `or`, `imp`)
- Causal state transitions: `causal (s : Subject) (w w' : State) (p : Prop)` (`Initiates`)
- Truthmaker grounding: `ground (e : Entity) (p : Prop)` (`Ground`)
- Objective logical incompatibility: `incomp (p q : Prop)` (`Incompatible`)
- Factive intentional meaning: `factiveMeans (s : Subject) (p : Prop)` (`Means s p ∧ p`)

The kernel machine-checks two fundamental expressivity results:
1. **Invariance Theorem (`blind_formula_collapse_invariant`):** By structural induction on formulas, every $\varphi \in \text{BlindFormula}$ evaluates identically in any model and in its contrastive collapse:
$$\forall I\,\varphi,\; \text{eval } I\ \varphi \iff \text{eval } (\text{ContrastiveCollapse } I)\ \varphi$$
2. **Non-Definability of Genuine Choice (`no_blind_formula_defines_choice`):** In a model $I_{\text{choice}}$ where genuine choice occurs, any formula defining `Chooses` would evaluate to true in $I_{\text{choice}}$, hence true in $\text{Collapse}(I_{\text{choice}})$, contradicting `collapse_destroys_all_choice`. Thus:
$$\neg \exists \varphi \in \text{BlindFormula},\; \text{eval } I\ \varphi \iff \text{FullChooses } I\ s\ p\ q$$
3. **Non-Definability of Free Will (`no_blind_formula_defines_freeWill`):** No formula in `BlindFormula` can define `FreeWill` or target F1b across models.

#### 6. Adversarial Self-Attack & Loopholes Analysis

- **Loophole 1: Quantifier Permutation:** Can an existential action datum $\exists s\,p, Act(s,p)$ force choice through an external subject? Refuted: In single-agent models (`CountermodelVeridicalMeaning.Single`), no external subject exists.
- **Loophole 2: Non-Factivity without Choice:** Can allowing false beliefs force choice? Refuted: `UnrealizedPossibilityModel` demonstrates an agent meaning a falsehood (`Means () False`) with zero genuine choice.
- **Loophole 3: Disjunctive / Negated Actions:** Can an agent act on a disjunction $p \lor q$? Refuted: Acting on $p \lor q$ provides `Means s (p ∨ q)`, not `Means s p ∧ Means s q`.
- **Loophole 4: Performative Retorsion / Self-Denial:** Refuted: `SelfDenialOfChoiceModel` and `DelusionalSelfChoiceModel` prove that self-referential denial of choice is consistent with zero genuine choice.

#### 5. Architectural Synthesis: The Frontier Diagram

```text
=========================================================================================
                           THE FRONTIER THEOREM                                          
=========================================================================================
                                                                                         
    Performative Intentional Action (Act s p)                                            
            │                                                                            
            ├──► Intentional Meaning: Means s p                   (Layer 1 - PROVEN)     
            ├──► Causal Initiation: Initiates s w w' p            (Layer 0 - PROVEN)     
            ├──► Objective Incompatibility: Incompatible p (¬p)   (Layer 2 - PROVEN)     
            ├──► Selection / Settlement: Selects / Authors        (Layer 3 - PROVEN)     
            └──► Judgment / Truth / Normativity / Modality        (Layer 3+ - PROVEN)    
                           │                                                             
                           X  ◄─── CONTRASTIVE COLLAPSE BARRIER                          
                           │       (Destroyed by Collapse(M); Underdetermined by T₀)     
                           │                                                             
                Cognitive Representation of an Incompatible Alternative                   
                (MissingCognitiveHorn s p := ∃ q, Means s q ∧ Incompatible p q)          
                           │                                                             
                           ▼                                                             
                     Genuine Choice (Chooses s p q)               (Layer 4 - A14)        
                           │                                                             
                           ▼                                                             
                       Free Will (FreeWill s)                     (Target F1b)           
=========================================================================================
```

### Candidate Layer Beneath A14

Current status:

```text
  Objective incompatibility
          ↓
  [MISSING COGNITIVE RELATION]
          ↓
  Cognitive alternative representation
          ↓
  Chooses
          ↓
  FreeWill
```

The candidate cognitive relation is NOT yet part of Γ.

Its logical strength relative to A14 is currently OPEN.

---

## O Programa de Teologia Condicional (Γ + A14 ⊢ ?)

Adotando $A14$ (`AxIntentionalChoice`: $Act(s,p) \to \exists q, Chooses(s,p,q)$) como o único novo compromisso semântico substantivo, investigamos formalmente no módulo `formal/Logos/ConditionalTheology.lean` o que o sistema axiomático existente de $\Gamma$ é capaz de derivar em direção à teologia filosófica (fundamento último, personalidade, pluralidade, amor, trindade, encarnação, criação).

### 1. Fechamento de Agência e Limites de FreeWill

O fechamento dedutivo imediato de A14 estabelece:
$$Act(s,p) \implies Chooses(s,p,q) \implies FreeWill(s) \land FreeSubject(s) \land Person(s)$$

No entanto, o teste adversarial contra 8 dimensões de agência prova que $FreeWill$ **NÃO acarreta** nenhuma das seguintes propriedades (todas separadas por contramodelos máquina-verificados):
1. **Racionalidade:** $FreeWill \nvdash ReasonsFor$ (`freewill_not_entails_rationality`). Agentes livres podem escolher sem razões explicativas.
2. **Normatividade:** $FreeWill \nvdash ActsCorrectly$ (`freewill_not_entails_normativity`). A liberdade permite o erro e a infração normativa.
3. **Valor Interpessoal:** $FreeWill \nvdash AffectsValue$ (`freewill_not_entails_value`). Agência livre é consistente com estados proposicionais indiferentes.
4. **Teleologia:** $FreeWill \nvdash HasGoal$ (`freewill_not_entails_teleology`). Escolhas deliberadas podem ser pontuais e espontâneas sem meta final.
5. **Subjetividade Reflexiva:** $FreeWill \nvdash KnowsOwnAct$ (`freewill_not_entails_reflexive_subjectivity`). A escolha de primeira ordem não força auto-representação transcendental de ordem superior.
6. **Relacionalidade:** $FreeWill \nvdash \exists s_2, s_1 \neq s_2$ (`freewill_not_entails_relationality`). Um agente livre pode existir em isolamento solipsista absoluto.
7. **Persistência / Imortalidade:** $FreeWill \nvdash Persists$ (`freewill_not_entails_persistence`). Agentes livres podem ser puramente efêmeros (existir e escolher em um único instante temporal/causal).
8. **Necessidade:** $FreeWill \nvdash NecSubject$ (`freewill_not_entails_necessity`). A vontade livre é compatível com contingência ontológica total.

### 2. A Arquitetura de Fundamentação sob A14 (Obstrução da Cadeia Infinita)

Na cadeia de fundamentação de verdades necessárias:
$$T(p) \implies \exists e, Ground(e,p) \implies \exists e, Ground(e,p) \land Nec(e) \stackrel{?}{\implies} UltimateGround(u)$$
- A14 **não elimina** a regressão infinita de fundamentação (`a14_not_eliminates_infinite_ground_chain`). A agência livre de sujeitos contingentes não impõe boa-ordenação ou finitude na ordem explicativa ontológica.
- Logo, $FreeWill \nvdash UltimateGround$ (`free_agency_not_entails_ultimate_ground`).

### 3. Independência do Fundamento Último Pessoal

Mesmo que se postule a existência de um fundamento último ($UltimateGround(u)$), a adição de A14 **não força** que o fundamento último seja pessoal:
$$A14 + UltimateGround \nvdash Personal(u)$$
Demonstrado formalmente em `a14_plus_ultimate_ground_not_entails_personal_ultimate_ground`: um fundamento último impessoal (substrato cósmico) é plenamente compatível com a existência de criaturas contingentes dotadas de livre-arbítrio.

### 4. Independência de Pluralidade e Amor

1. **Pluralidade:** $A14 \nvdash Plurality$ (`a14_not_entails_plurality`). O contramodelo `SolitaryFreeAgentModel` prova que a agência livre não deriva um segundo sujeito sem o compromisso metafísico `AxTwoSubjects`.
2. **Amor:** $A14 + Plurality \nvdash Loves$ (`free_agency_and_plurality_not_entails_love`). Um universo com múltiplos agentes livres pode ser mutuamente hostil, maldoso ou estéril. O amor não decorre analiticamente da liberdade.

### 5. Estruturas Teológicas Neutras: Trindade, Encarnação e Criação

Definindo alvos estruturais neutros (sem contrabando dogmático por definição):
1. **Trindade (`TrinitarianStructure`):** Exige 3 centros pessoais distintos em 1 realidade divina comum com relações mútuas eternas. Separado pelo modelo binitariano (`preceding_theory_not_entails_trinity`): uma teologia com 2 pessoas divinas em mútuo amor satisfaz plenamente $\Gamma + A14$, tornando a Trindade estritamente indemonstrável sem axioma triádico.
2. **Encarnação (`IncarnationalStructure`):** Exige que um mesmo sujeito pessoal una uma natureza divina e uma natureza humana. Separado pelo modelo unincarnado (`preceding_theory_not_entails_incarnation`): a transcendência divina não acarreta ontologicamente a união hipostática.
3. **Criação Contingente (`CreationStructure`):** Separado pelo modelo divino acósmico (`necessary_ground_not_entails_contingent_creation`): um Deus necessário e autossuficiente pode existir sem criar qualquer universo ou sujeito contingente. A realidade necessária não força criação contingente.

### 6. O Grafo de Dependência Teológica Formal

```text
=========================================================================================
                 GRAFO DE DEPENDÊNCIA TEOLÓGICA (Γ + A14)                                 
=========================================================================================
                                                                                         
     [Act s p]                                                                           
         │                                                                               
         ▼  (A14: AxIntentionalChoice - SEMANTIC)                                        
     [Chooses s p q]                                                                     
         │                                                                               
         ▼  (DEFINITIONAL)                                                               
     [FreeWill s]                                                                        
         │                                                                               
         ├──X (COUNTERMODEL: freewill_not_entails_rationality)      ──► [Rationality]    
         ├──X (COUNTERMODEL: freewill_not_entails_normativity)      ──► [Normativity]    
         ├──X (COUNTERMODEL: freewill_not_entails_teleology)        ──► [Teleology]      
         ├──X (COUNTERMODEL: freewill_not_entails_relationality)    ──► [Relationality]  
         └──X (COUNTERMODEL: freewill_not_entails_necessity)        ──► [Necessity]      
                                                                                         
     [Necessary Truth (T p)]                                                             
         │                                                                               
         ▼  (A4/A6: AxGlobalGround - PROVEN)                                             
     [Some Ground (Ground e p)]                                                          
         │                                                                               
         ▼  (Modal: T7_necessaryReality - PROVEN)                                        
     [Necessary Ground (Ground e p ∧ Nec e)]                                             
         │                                                                               
         X  ◄─── (COUNTERMODEL: a14_not_eliminates_infinite_ground_chain)                  
         │                                                                               
     [Ultimate Ground]                                                                   
         │                                                                               
         X  ◄─── (COUNTERMODEL: a14_plus_ultimate_ground_not_entails_personal_ultimate)      
         │                                                                               
     [Personal Ultimate Ground]                                                          
         │                                                                               
         X  ◄─── (METAPHYSICAL: A10 AxTwoSubjects required; Solitary Model blocks)       
         │                                                                               
     [Plurality of Persons]                                                              
         │                                                                               
         X  ◄─── (METAPHYSICAL: AxPersonsAffect required; Malicious Model blocks)        
         │                                                                               
     [Mutual Divine Love]                                                                
         │                                                                               
         X  ◄─── (COUNTERMODEL: Binitarian Model blocks Trinity)                         
         │                                                                               
     [Trinitarian Structure (3 Persons)]                                                 
         │                                                                               
         ├──X (COUNTERMODEL: Acosmic Model blocks) ──► [Contingent Creation]             
         │                                                    │                          
         └────────────────────────────────────────────────────X (Unincarnate Model)     
                                                              │                          
                                                              ▼                          
                                                     [Incarnation]                       
=========================================================================================
```

### 7. Síntese do Balanço Axiomático (Single-Axiom Discipline)

- **O que A14 realmente compra:** A14 fecha formalmente o salto de agência performativa para livre-arbítrio (`Act → Chooses → FreeWill`), garantindo a existência de um sujeito livre (`FreeSubject`) e de uma pessoa moral (`Person`).
- **O que A14 NÃO compra:** A14 não compra fundamentação última bem-ordenada, não compra personalidade do absoluto, não força pluralidade, não força amor mútuo, não deriva a Trindade, não força a criação contingente e não deriva a Encarnação.
- **A Teologia de $\Gamma$:** É uma teologia rigorosamente condicional, estratificada e honesta. Cada passo além da liberdade requer explicitamente ou uma nova ponte metafísica (como `AxTwoSubjects` e `AxPersonsAffect`) ou permanece estritamente indecidível/independente da lógica interna da agência.

---

## O Passe de Endurecimento Ontológico de Γ (Ontology Hardening)

Executamos um passe agressivo de **endurecimento ontológico** sobre $\Gamma$, eliminando atalhos definicionais que carregavam conteúdo metafísico substantivo disfarçado de analiticidade, sob a regra mandatória:

> **Prefira perder um teorema a esconder uma premissa.**

### 1. Desconstrução dos Atalhos Eliminados

1. **`ExistsAt` (Existência Relativa a Mundos vs. Necessidade Degenerada):**
   - *Atalho anterior:* `ExistsAt w (Entity.ofSubject _) := True` tornava qualquer sujeito atuante trivialmente necessário em todos os mundos por pura definição analítica.
   - *Endurecimento:* Substituído por existência genuinamente sensível ao mundo (`SubjectExistsAt w s`, `EntityExistsAt w e`). Sujeitos atuantes na atualidade não existem automaticamente em mundos contrafatuais.
   - *Impacto:* Os teoremas C77 (`necessaryPersonExists`) e C92 (`necessary_entity_exists`) a partir do ato performativo foram **demovidos e refutados por contramodelo** (`ContingentAgencyModel`: `act_not_entails_necessary_subject` e `act_not_entails_necessary_entity`). A necessidade ontológica não nasce mais de um ato contingente.

2. **`Person` (Sujeito Intencional vs. Pessoalidade Substantiva):**
   - *Atalho anterior:* `Person s := Agent s ∧ Rational s ∧ Intentional s` com `Agent := True` e `Rational := True`, fazendo com que qualquer registro intencional fosse nominalmente uma 'pessoa'.
   - *Endurecimento:* Introduzida a distinção honesta entre `IntentionalSubject s := ∃ p, Means s p` (definição constitutiva do ato) e `Person s := IntentionalSubject s ∧ SubstantivePerson s` (predicado substantivo independente).
   - *Impacto:* O ato intencional deriva estritamente `IntentionalSubject` (`DEFINITIONAL`). O salto `Act → Person` e `FreeSubject → Person` permanece **OPEN / desacoplado**, e `Person → FreeSubject` é refutado por contramodelo (`PersonhoodAgencySeparation`).

3. **Relações Interpessoais (`Affects`, `Helps`, `Harms`, `Loves`):**
   - *Atalho anterior:* `Affects s t := s ≠ t`, `Helps := Affects`, `Harms := False`, o que tornava o amor uma consequência analítica imediata da mera distinção entre dois sujeitos ($s \neq t \implies Loves(s,t)$).
   - *Endurecimento:* As relações de afetação, ajuda e dano foram endurecidas em termos primitivos independentes (`BearingOf s t`), preservando a definição constitutiva de amor como benevolência direcionada (`Loves s t := Helps s t ∧ ¬ Harms s t`).
   - *Impacto:* A derivação automática de amor a partir da pluralidade foi **completamente destruída**. Dois sujeitos distintos não se afetam, não se ajudam e não se amam analiticamente (`DisconnectedPluralityModel`: `plurality_not_entails_affects`, `plurality_not_entails_helps`, `plurality_not_entails_love`, `freewill_and_plurality_not_entails_love`). T13 e T14 tornam-se estritamente condicionais a princípios relacionais explícitos.

4. **Ataque aos Quatro Grandes Axiomas (A3, A4, A6, A7):**
   - **A3 (Truthmaker):** A instanciação atômica (`groundPrinciple_atom`) não deriva a fundamentação existencial de fórmulas compostas sem indução estrutural (`AtomicVsFormulaTruthmakerModel`).
   - **A4 (Global Ground):** A fundamentação mundanal ordinária não acarreta um fundamento uniforme necessário comum a todos os mundos (`CountermodelWorldwiseTruthmaking`). A4 permanece estritamente irredutível como compromisso semântico.
   - **A6 (Pluralidade):** O cogito performativo, a bivalência e o livre-arbítrio (sob A14) são plenamente consistentes com um modelo solitário de agente único (`SolitaryChoiceModel`). A6 permanece estritamente irredutível como compromisso META.
   - **A7 (Personal Ground):** A fundamentação de uma propriedade pessoal não transfere o tipo ontológico para o fundamento (`CountermodelImpersonalUltimateGround`). A7 permanece estritamente irredutível como compromisso META.

### 2. Tabela de Auditoria Compacta (Ontology Hardening Ledger)

| Área Ontológica | Formulação Antiga (Degenerada) | Formulação Endurecida (Robusta) | Teorema Antigo Sobrevive? | Novo Axioma Adicionado? | Status Epistêmico / Contramodelo |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Person** | `Agent ∧ Rational ∧ Intentional` (`Agent, Rational := True`) | `IntentionalSubject s := ∃p, Means s p`; `Person` substantivo independente | **DEMOVIDO** (`Act → IntentionalSubject` sobrevive; `Act → Person` é OPEN) | **NÃO** (0 axiomas) | `DEFINITIONAL` (intencional) / `OPEN` (pessoal); `PersonhoodAgencySeparation` |
| **ExistsAt** | `ExistsAt w (Entity.ofSubject _) := True` (necessidade analítica) | `SubjectExistsAt w s` sensível a mundos (`w = actualWorld`) | **DEMOVIDO** (C77 e C92 refutados; necessidade do ato cai) | **NÃO** (0 axiomas) | `COUNTERMODEL` (`ContingentAgencyModel`: `act_not_entails_necessary_subject`) |
| **Ground (A3)** | Truthmaker existencial irrestrito para todas as fórmulas | Fundamentação atômica (`groundPrinciple_atom`) + semântica composicional | **AUDITADO / REDUZIDO** (átomos fundamentados; compostos livres) | **NÃO** (A3 auditado) | `SEMANTIC` / `AtomicVsFormulaTruthmakerModel` |
| **GlobalGround (A4)** | Troca de quantificadores $\forall w \exists e \to \exists e \forall w$ | Fundamentação mundanal vs. fundamento necessário uniforme | **IRREDUTÍVEL** (fundamento uniforme não dedutível de mundanal) | **NÃO** (A4 preservado) | `SEMANTIC` / `CountermodelWorldwiseTruthmaking` |
| **Plurality (A6)** | `AxTwoSubjects` decorrente de certo/errado | Pluralidade genuína irredutível do agente único | **IRREDUTÍVEL** (agência e escolha não forçam segundo sujeito) | **NÃO** (A6 mantido como META) | `METAPHYSICAL` / `SolitaryChoiceModel`, `CountermodelUnitPlurality` |
| **Love / Value** | `Affects := s ≠ t`, `Helps := Affects`, `Harms := False` | `BearingOf s t` independente; `Loves := Helps ∧ ¬Harms` | **DEMOVIDO** (Amor não decorre da pluralidade; T13/T14 condicionais) | **NÃO** (0 axiomas) | `COUNTERMODEL` (`DisconnectedPluralityModel`: `plurality_not_entails_love`) |

> **Conclusão:** O sistema $\Gamma$ agora repousa sobre uma base axiomática limpa, livre de atalhos definicionais ilícitos. A necessidade, a pessoalidade substantiva, a pluralidade e o amor mútuo são explicitamente reconhecidos pelo que são: exigências ontológicas de alto preço que jamais devem ser mascaradas sob definições analíticas triviais.

---

## O Programa de Expansão Retorsiva de Γ (Retorsion Expansion Pass)

Sob a diretriz metodológica central:
> **Para toda afirmação substantiva que Γ aceita, não basta testar se ela é derivável. Ataque também sua negação. Verifique se a negação é performativa, semântica, lógica ou metafisicamente auto-refutável.**
> **Prefira perder um teorema a esconder uma premissa. Uma retorsão tem êxito somente quando a negação genuinamente não pode ser coerentemente sustentada.**

### 1. Taxonomia e Estratégia Retorsiva de Primeira Classe

- **Reductio Ordinário:** Assume $\neg P$, deriva `False` num modelo arbitrário (`by_contra`).
- **Retorsão Performativa:** Assume $\neg P$ como uma posição cognitiva ou ato asserido real, analisa os compromissos ontológicos e semânticos indispensáveis para executar ou sustentar esse próprio ato, e demonstra que o próprio ato de negação pressupõe ou instancia $P$.

Fontes rastreadas da contradição retorsiva:
1. `RETORSION / LOGICAL`: O ato de asserção viola a coerência lógica bivalente ($T(\text{NoTruth}) \implies False$).
2. `RETORSION / DEFINITIONAL`: O ato de asserir a negação instancia analiticamente o conceito negado (asserir `NoAct` executa um `Act`).
3. `RETORSION / SEMANTIC`: A verdade pretendida pela negação exige uma ponte semântica que ela mesma rejeita (ou revela limitação expressiva).
4. `RETORSION / METAPHYSICAL`: A posição sustentada anula as condições ontológicas do sujeito que julga.

### 2. A Campanha Retorsiva Big-O / Big-S (Ontologia de Sujeito Intencional)

Reformulamos a campanha retorsiva em torno do conceito ontológico fundamental de **dependência de um Sujeito Intencional** (`IntentionalSubject`), desvinculando a definição de Subjetividade de Pessoa e Livre-Arbítrio:

```text
Subject
  └── IntentionalSubject

Subjective x  :=  x depende de um Sujeito Intencional (DependsOnIntentional x)
Objective x   :=  x não depende de um Sujeito Intencional (¬ DependsOnIntentional x)
```

- **Definição de Dependência Intencional:** `DependsOnIntentional x := ∃ s : Subject, IntentionalSubject s ∧ DependsOn x s`. Um item é subjetivo sse inere ontologicamente em um sujeito que significa conteúdos proposicionais.
- **Dependência Ontológica:** Primitivo intensional `DependsOn x s` (**A15**, `Tag: VOCAB`).
- **Disjunção Lógica Pura:** A disjunção entre Objetividade e Subjetividade (`objective_and_subjective_disjoint`) é um **teorema da lógica pura** ($\neg P \land P \implies False$).
- **Exaustão Clássica:** `Objective x ∨ Subjective x` decorre do Terceiro Excluído clássico.
- **Cadeia Construtiva:** A inferência `Subjective x → ∃ s, IntentionalSubject s` é puramente lógica e definicional.

Axiomas constitutivos da campanha retorsiva:
- **Axiom A15 · `DependsOn` (`VOCAB`):** Vocabulary: primitive ontological dependence relation between a domain item and a subject.
- **Axiom A16 · `universal_thesis_claims_objectivity` (`SEM`):** Semantic bridge: the universal thesis of subjectivity, as an asserted universal truth about all reality, does not depend on any particular intentional subject.
- **Axiom A17 · `transcendental_reflection_intentional` (`SEM`):** Semantic transcendental bridge: the transcendental reflection on universal objectivity depends on an IntentionalSubject who entertains it.

1. **Retorsão contra a Subjetividade Absoluta (Big-S):**
   - Seja $ES := \forall x, Subjective(x)$ ("Tudo depende de um Sujeito Intencional").
   - Reivindica validade objetiva como tese universal sobre a realidade (independência de sujeito intencional): `universal_thesis_claims_objectivity` (**A16** / `SEM`).
   - Pelo lema de auto-inclusão (`everything_subjective_self_applies`), $ES$ classifica a si mesma como dependente de sujeito intencional: $Subjective(ES)$.
   - Pela contradição definicional entre $Objective$ e $Subjective$, temos $\neg EverythingSubjective$ (`not_everything_subjective`, 0 premissas).
   - Consequência existencial positiva: **$\exists x, Objective(x)$** (`exists_objective_of_retorsion`, testemunhado pela própria tese universal).

2. **Retorsão contra a Objetividade Absoluta (Big-O):**
   - Seja $EO := \forall x, Objective(x)$ ("Nada depende de um Sujeito Intencional").
   - A reflexão transcendental sobre a objetividade universal depende de um sujeito intencional pensante: `transcendental_reflection_intentional` (**A17** / `SEM`).
   - Essa ponte semântica estabelece que a própria formulação de $EO$ depende de um sujeito intencional: $Subjective(EO)$.
   - Pelo lema de auto-inclusão (`everything_objective_self_applies`), $EO$ dita que ela mesma é objetiva: $Objective(EO)$.
   - Pela contradição definicional, temos $\neg EverythingObjective$ (`not_everything_objective`, 0 premissas).
   - Consequência existencial positiva: **$\exists x, Subjective(x)$** (`exists_subjective_of_retorsion`).

3. **Dedução do Teorema Central: Existência do Sujeito Intencional via Retorsão:**
   - Da testemunha positiva $\exists x, Subjective(x)$, decorre imediatamente:
     $$\exists s : Subject, \; IntentionalSubject(s) \quad (\text{`exists_intentional_subject_of_retorsion`})$$

```text
=========================================================================================
TEOREMA CENTRAL — EXISTÊNCIA DO SUJEITO INTENCIONAL VIA RETORSÃO BIG-O / BIG-S
=========================================================================================
A campanha retorsiva sob a ontologia de Dependência Intencional estabelece formalmente em Lean:

    exists_intentional_subject_of_retorsion : ∃ s : Subject, IntentionalSubject s

Cadeia Construtiva Transparente:
    Retorsão Big-O  ──→  ∃ x, Subjective x  ──→  ∃ s, IntentionalSubject s

Footprint Axiomático Auditado pelo Kernel:
    {Means, Subject, DependsOn, transcendental_reflection_intentional}

• RIGOROSAMENTE INDEPENDENTE de Person, FreeWill, Chooses, Act e A14.
• Não depende de Initiates, State, Cogito, ou escolha moral deliberada.
• A retorsão atinge legitimamente o Sujeito Intencional e estanca ANTES de Pessoa / Livre-Arbítrio.
=========================================================================================
```

> **Significado Conceitual Preciso:** A rota Big-O / Big-S estabelece a existência de um centro de perspectiva intencional (`IntentionalSubject`) independentemente de `Act`. Ela não assume Livre-Arbítrio nem Pessoalidade, mantendo estes como conceitos a jusante.

#### Fronteira Conceitual e Teoremas de Separação

A arquitetura torna a fronteira explícita:
```text
Retorsão Big-O / Big-S
   │
   ▼  [PROVADO - exists_intentional_subject_of_retorsion]
IntentionalSubject
   │
   X  [BLOQUEADO - DeterministicTranscendentalSubjectModel]
   ▼
Person (FreeWill)
```

#### Auditoria Adversarial: A Fraqueza Inerente e o Teste do "Porco Voador"

Submetemos a campanha retorsiva ao teste adversarial definitivo: **pode a retorsão descobrir o Livre-Arbítrio sem já assumi-lo na premissa retorsiva A17?**

1. **Variantes Enfraquecidas da Premissa Retorsiva:**
   - *Dependência de Sujeito Nu (`DependsOnBareSubject`):* Se a reflexão transcendental exige apenas que a tese dependa de algum sujeito (`∃ s, DependsOn EO s`), a retorsão deriva apenas a existência do sort `∃ s : Subject, True`, sem qualquer intencionalidade ou agência.
   - *Dependência de Sujeito Intencional (`DependsOnIntentional`):* Se a reflexão exige que a tese dependa de um sujeito intencional (`∃ s, IntentionalSubject s ∧ DependsOn EO s`), a retorsão deriva legitimamente `∃ s : Subject, IntentionalSubject s` (`weakened_retorsion_derives_intentional_subject`).

2. **O Modelo Hostil Permanente (`DeterministicTranscendentalSubjectModel`):**
   Construímos em Lean um modelo concreto com `0 axiomas` onde um sujeito puramente mecânico/determinista reflete intencionalmente sobre a tese transcendental, satisfazendo plenamente a teoria retorsiva enfraquecida, enquanto `FreeWill` e `Person` são uniformemente falsos:
   - Provamos `deterministic_transcendental_subject_refutes_freewill`: **a retorsão enfraquecida NÃO deriva Livre-Arbítrio**.
   - Provamos `deterministic_transcendental_subject_refutes_person`: **a retorsão enfraquecida NÃO deriva Pessoalidade**.

3. **O Teste de Estresse do "Porco Voador" (Arbitrary-Object Stress Test):**
   Para demonstrar o vício de petição de princípio de injetar `Person / FreeWill` na premissa transcendental A17, introduzimos o predicado arbitrário `WingedPig : Subject → Prop` e definimos `SubjectivePig x := ∃ s, WingedPig s ∧ DependsOn x s`.
   - Provamos `winged_pig_derived_of_pig_reflection`: se postulamos que a reflexão depende de um porco voador, a retorsão "prova" a existência de um porco voador!
   - Provamos `pig_retorsion_exposes_premise_smuggling` (`0 axiomas`): a reflexão transcendental não força predicados externos arbitrários.

4. **Decomposição Sistemática e Escada Dedutiva de A17:**
   Decompomos o axioma forte A17 em quatro alvos intermediários explícitos:
   - **(A17a) `∃ s, IntentionalSubject s`:** Existência de sujeito intencional (derivável via Rota B).
   - **(A17b) `∃ s, Means s EO ∧ DependsOn EO s`:** Mesma testemunha que significa e fundamenta a tese universal.
   - **(A17c) `∃ s, Person s`:** Existência de uma pessoa.
   - **(A17d) `∃ s, FreeWill s`:** Existência de livre-arbítrio.
   - **`A17_weak`:** `∃ s, IntentionalSubject s ∧ DependsOn EO s` (transcendental enfraquecido).
   - **`A17_strong`:** `∃ s, Person s ∧ DependsOn EO s` (o A17 original com livre-arbítrio).

   *Pontes Candidatas entre Significação e Dependência:*
   - *Ponte Universal (`Means s p → DependsOn (ofProp p) s`):* Rejeitada como absurda — faria qualquer pensamento sobre 2+2=4 ou sobre um Porco Voador tornar a entidade dependente da mente.
   - *Ponte Transcendental Restrita (`RestrictedTranscendentalBridge`):* Postula especificamente que a tese de objetividade universal, enquanto formulação conceitual, depende ontologicamente do sujeito que a pensa (`Tag: SEM`). Provamos que ela deriva `A17b` e `A17_weak`, mas **não** deriva `FreeWill`.

   *Rastreamento Estrito de Testemunha e Modelo de Deslizamento (Witness Slippage):*
   Provamos formalmente que ter separadamente um pensante de EO (`A17b`) e uma pessoa (`A17c`) **não implica** que o pensante seja uma pessoa (`witness_slippage_separation`, `0 axiomas`). No modelo com dois sujeitos `WitnessSubject` (`thinker` e `person`), o pensante opera sem livre-arbítrio, enquanto a pessoa não fundamenta a tese.

```text
=========================================================================================
A ESCADA DEDUTIVA DE A17 E O ESTATUTO DE CADA DEGRAU
=========================================================================================
Retorsão Big-O / Big-S
  │
  ▼  [PROVADO - Rota B]
∃ s : Subject, IntentionalSubject s  (A17a)
  │
  ▼? [EXIGE PREMISSA DE CONSIDERAÇÃO PERFORMATIVA (SEMÂNTICA)]
∃ s : Subject, Means s EverythingObjective
  │
  ▼? [EXIGE PONTE TRANSCENDENTAL DE DEPENDÊNCIA (SEMÂNTICA)]
∃ s : Subject, Means s EO ∧ DependsOn EO s  (A17b)
  │
  ▼  [PROVADO / DEFINICIONAL - a17b_implies_a17_weak]
A17_weak : ∃ s : Subject, IntentionalSubject s ∧ DependsOn EO s
  │
  ▼? [INDEPENDENTE / BLOQUEADO PELO MODELO DETERMINISTA E DESLIZAMENTO]
∃ s : Subject, Person s ∧ DependsOn EO s
  │
  ▼  [PROVADO / DEFINICIONAL]
A17_strong : ∃ s : Subject, FreeWill s ∧ DependsOn EO s
=========================================================================================
```

> **Veredito Filosófico e Formal (CASO C):**
> A reflexão transcendental força performativamente a existência de um **Sujeito Intencional** (`IntentionalSubject`), pois não se pode formular uma tese sem significá-la. Contudo, ela **NÃO força Livre-Arbítrio nem Pessoalidade**, pois um autômato determinista pode significar uma tese. Portanto, **A17_strong é uma ponte metafísica substantiva irredutível (`Tag: META`)**, e não uma decorrência neutra da lógica ou da retorsão pura.

Provamos formalmente 11 teoremas de separação sem axiomas (`0 axioms`) demonstrando essas fronteiras:
1. **`representation_not_depends_on_person`:** Representação intencional (`Means s p`) não implica dependência de pessoa.
2. **`subjective_not_depends_on_person`:** Em assinatura desvinculada, subjetividade não força dependência de pessoa.
3. **`intentional_subject_not_person`:** Sujeito intencional não implica Pessoa (Livre-Arbítrio).
4. **`person_not_freewill`:** Em assinatura desvinculada, pessoalidade não força livre-arbítrio.
5. **`exists_subjective_not_exists_person`:** A existência de algo subjetivo não força a existência de uma pessoa.
6. **`exists_subjective_not_exists_freewill`:** A existência de algo subjetivo não força livre-arbítrio.
7. **`deterministic_transcendental_subject_refutes_freewill`:** Retorsão enfraquecida não deriva livre-arbítrio.
8. **`deterministic_transcendental_subject_refutes_person`:** Retorsão enfraquecida não deriva pessoalidade.
9. **`pig_retorsion_exposes_premise_smuggling`:** Retorsão enfraquecida não deriva predicados arbitrários externos.
10. **`means_not_dependson` / `exists_means_not_exists_dependson`:** Significar EO não implica depender ontologicamente de s.
11. **`witness_slippage_separation`:** Conjunção de pensante de EO e pessoa não garante pensante pessoal (bloqueio de deslizamento).

### 3. Livro-Razão Adversarial de Retorsão (Adversarial Retorsion Ledger)

| Afirmação Alvo | Negação Exata | Ataque Retorsivo | O que a negação precisa executar/assumir | Resultado | Classificação | Modelo Hostil / Obstrução |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Ato Intencional** (`Act`) | `∀ s p, ¬ Act s p` (`NoAct`) | Performativo direto | Asserir que não há ato executa um ato intencional | **REFUTADO** | `PROVEN BY RETORSION` | Nenhum (impossibilidade analítica) |
| **Ato Fraco** (`act`) | `∀ s p, ¬ act s p` (`NoWeakAct`) | Performativo fraco | Enunciar a negação realiza um evento de prolação | **REFUTADO** | `PROVEN BY RETORSION` | Nenhum |
| **Verdade** (`T`) | `∀ p, ¬ T p` (`NoTruth`) | Lógico | Se é verdade que nada é verdade, algo é verdade | **REFUTADO** | `PROVEN BY RETORSION + LOGIC` | Nenhum |
| **Sujeito** (`SubjectExists`) | `∀ s, ¬ SubjectExists s` | Performativo direto | Negar o sujeito exige o centro de perspectiva que julga | **REFUTADO** | `PROVEN BY RETORSION` | Nenhum |
| **Campo de Escolha** (`ChoiceField`) | `∀ s p q, ¬ ChoiceField s p q` | Performativo alternativo | Asserir coloca o agente diante da alternativa da sua própria negação | **REFUTADO** | `PROVEN BY RETORSION` | Nenhum |
| **Subjetividade Absoluta** | `∀ x, Subjective x` | Auto-inclusão objetiva | A tese reivindica estatuto objetivo sobre o real | **REFUTADO** | `PROVEN BY RETORSION + LOGIC` | Nenhum (sob disjunção lógica O/S) |
| **Objetividade Absoluta** | `∀ x, Objective x` | Representação pessoal | O ato de formular a tese depende de um sujeito pessoal livre | **REFUTADO** | `PROVEN BY RETORSION + META` | Nenhum (sob A17) |
| **Retorsão Enfraquecida → FreeWill** | `∃ s, IntentionalSubject s ↛ FreeWill s` | Teste de enfraquecimento | Reflexão transcendental mecânica sem livre-arbítrio | **FALHOU** | `FAILED — HOSTILE MODEL` | `DeterministicTranscendentalSubjectModel` |
| **Retorsão Arbitrária (WingedPig)** | `Reflexão ↛ WingedPig` | Objeção de Gaunilo | Enxertar predicados contingentes na premissa | **FALHOU** | `FAILED — PREMISE SMUGGLING` | `pig_retorsion_exposes_premise_smuggling` |
| **A3 (Truthmaker)** | `∃ w φ, TrueAt w φ ∧ ∀ e, ¬(ExistsAt ∧ Ground)` | Performativo / Diagonal | Asserir que algo não tem grounder não fornece grounder ontológico | **FALHOU** | `FAILED — HOSTILE MODEL` / `EXPRESSIVITY GAP` | Satisfação sem grounder é coerente (`Form` carece de ponto fixo diagonal) |
| **A4 (Global Ground)** | `∃ φ, □φ ∧ ∀ e, ¬(∀ w, ExistsAt ∧ Ground)` | Universal contrafatual | Troca $\forall w \exists e \to \exists e \forall w$ não é forçada por asserir sua ausência | **FALHOU** | `FAILED — HOSTILE MODEL` | `CountermodelWorldwiseTruthmaking` |
| **A9 (GroundProp)** | `∃ f, T f ∧ ∀ e, ¬ GroundProp e f` | Performativo | Proposição verdadeira não carrega entidade grounder por mera auto-asserção | **FALHOU** | `FAILED — HOSTILE MODEL` | Impessoalismo semântico |
| **A13 (ActPolarity)** | `∃ s p, Act s p ∧ ¬ Means s (¬p)` | Asserção de contra-exemplo | Agente pode asserir sem conceber a negação contraditória | **FALHOU** | `FAILED — HOSTILE MODEL` | `CountermodelVeridicalMeaning` (`Means s p := p`) |
| **A14 (IntentionalChoice)** | `∃ s p, Act s p ∧ ∀ q, ¬ Chooses s p q` | Auto-negação de escolha | "Ajo sem escolher": ato determinado assere a negação sem ter alternativas co-significadas | **FALHOU** | `FAILED — HOSTILE MODEL` | `CountermodelNoFreeWill` (ato determinado sem livre-arbítrio) |
| **A6 (Pluralidade)** | `¬ ∃ s₁ s₂, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂` | Solipsismo asserido | Agente único assere "estou só"; ato não requer interlocutor | **FALHOU** | `FAILED — HOSTILE MODEL` | `SolitaryChoiceModel` (agente único cumpre toda a agência pré-A6) |
| **A7 (Personal Ground)** | `∃ f, IsPresentPersonalFeature f ∧ ∀ e, ¬Personal e` | Grounding de pessoa | Ato pessoal sustentado por fundamento impessoal | **FALHOU** | `FAILED — HOSTILE MODEL` | `CountermodelImpersonalUltimateGround` |
| **Fundamento Último** (`UltimateGround`) | `¬ ∃ u, UltimateGround u` | Regresso Infinito com Truthmakers | Asserir que não há fundamento último exige verdade fundamentada | **SOBREVIVE / DILEMA** | `DILEMMA — HOSTILE MODEL` | Sobrevive sob truthmaking permissivo (`PermissiveTruthGroundedInfiniteChain`); refutado sob truthmaking de totalidade substantiva (`TotalityGroundingSignature`) |
| **Act → Person** | `∃ s p, Act s p ∧ ¬ Person s` | Performativo substantivo | Agente mecânico intencional age sem deliberação moral | **FALHOU** | `FAILED — HOSTILE MODEL` | `CountermodelSubjectWithoutPerson` |
| **FreeSubject → Person** | `∃ s, FreeSubject s ∧ ¬ Person s` | Escolha sem pessoalidade | Escolha combinatória entre estados sem pessoalidade substantiva | **FALHOU** | `FAILED — HOSTILE MODEL` | `PersonhoodAgencySeparation` |
| **Plurality → Loves** | `Pluralidade ∧ ¬ Amor` | Indiferença interpessoal | Dois sujeitos interagem em total indiferença ou hostilidade | **FALHOU** | `FAILED — HOSTILE MODEL` | `DisconnectedPluralityModel` |

### 4. Mapa Sintético: O Espaço Negativo e Positivo de Γ

```text
                        [ DADO PERFORMATIVO ]                                            
                                  │                                                      
        ┌─────────────────────────┴─────────────────────────┐                            
        ▼                                                   ▼                            
[ Consequências Positivas ]                       [ Exclusões Retorsivas ]               
  • Act s p                                         • ¬(NoAct)                           
  • Means s p                                       • ¬(NoWeakAct)                       
  • IntentionalSubject s                            • ¬(NoTruth)                         
  • ChoiceField s p (¬p)                            • ¬(NoSubject)                       
  • Chooses / FreeWill (sob A14)                    • ¬(NoChoiceField)                   
                                                    • ¬(EverythingSubjective)            
                                                    • ¬(EverythingObjective)             
                                                            │                            
                                                            ▼                            
                                              [ Testemunhas Positivas ]                  
                                                • ∃ x, Objective x                       
                                                • ∃ x, Subjective x                      
                                                • ∃ s, IntentionalSubject s (Rota B)     
                                                                                         
=========================================================================================
                 FRONTEIRA DE IRREDUCIBILIDADE (Retorsão Falha)                          
=========================================================================================
  Axiomas Semânticos:                                                                    
    A3 (Truthmaker)      ◄─── Retorsão falha; modelo hostil sem grounder sobrevive       
    A4 (GlobalGround)    ◄─── Retorsão falha; modelo mundanal sem swap sobrevive         
    A9 (GroundProp)      ◄─── Retorsão falha; modelo impessoal sobrevive                 
    A13 (ActPolarity)    ◄─── Retorsão falha; modelo verídico sem ¬p sobrevive           
    A14 (Choice)         ◄─── Retorsão falha; ato determinado sem Chooses sobrevive      
                                                                                         
  Axiomas Metafísicos:                                                                   
    A6 (Pluralidade)     ◄─── Retorsão falha; modelo de agente solitário sobrevive       
    A7 (Personal Ground) ◄─── Retorsão falha; modelo de base impessoal sobrevive         
                                                                                         
  Fronteiras Abertas:                                                                    
    Act → Person         ◄─── Retorsão falha; sujeito sem pessoalidade substantiva       
    Pluralidade → Amor   ◄─── Retorsão falha; sujeitos indiferentes/hostis sobrevivem    
```

#### Audit of Candidate Cognitive Primitive R

- **Candidate primitive:** `AlternativeRepresentation : Subject → Prop → Prop → Prop`
- **Semantic elimination:** `elim_R : ∀ s p q, AlternativeRepresentation s p q → Means s q ∧ Incompatible p q`
- **Action bridge:** `B_R : ∀ s p, Act s p → ∃ q, AlternativeRepresentation s p q`
- **Does $B_R$ derive A14?** YES (via `elim_R` and `Act s p → Means s p`).
- **Does A14 derive $B_R$?** NOT in general (if $R$ requires intentional contrastive awareness beyond extensional co-meaning) / YES (if $R$ is extensionally defined as `Means s q ∧ Incompatible p q`).
- **Strictly weaker than A14?** NO. Any candidate weaker than `Means s q ∧ Incompatible p q` fails to derive A14, while any candidate requiring intentional contrast is strictly stronger ($B_R > \text{A14}$).
- **Outcome:** **Outcome C** (every candidate reduces either to A13, A14, or a renamed composite primitive; no genuinely weaker bridge has yet been discovered).
- **Hostile model:** In `CountermodelVeridicalMeaning.Single` (`Means s p := p`), $B_R$ fails identically to A14, because no incompatible proposition can be represented without contradiction.

Current formal status of `Means`:
```lean
Means : Subject → Prop → Prop
Tag: VOCAB (Primitive Vocabulary)
```

As currently formalized, `Means` has no internal structure beyond pairing a subject with a proposition. Therefore no closure, factivity, non-factivity, alternative-generation, or contrastive representation follows merely from the relation itself.

- **Independent decomposition found?** NO. Any decomposition into mental states/representations either renames the primitive (`Means := Represents`) or hard-codes contrastivity into the definition.
- **Smallest missing primitive beneath Means:** A structured intensional representation layer or cognitive polarity faculty (`Polarity : Means s p → Means s (¬p)`), which is equivalent to **A13** (`Tag: SEM`), not A14.
- **Status:** OPEN as a deeper reductive question; BOUNDED as a primitive semantic relation in the formal ledger.

#### Conceptual Hierarchy: The Multi-Stage Architecture of Agency

```text
Layer 0: Causal Production (Initiates s w w' p)
      ↓  [Refuted: initiates_does_not_imply_means (CountermodelWeakActWithoutMeaning)]
Layer 1: Intentional Action (Act s p := Means s p ∧ ∃ w w', Initiates s w w' p)
      ↓  [PROVEN: act_implies_choiceField / intentional_hasChoiceField]
Layer 2: Objective Alternative Field (ChoiceField s p q := Means s p ∧ Incompatible p q)
      ↓  [PROVEN for Asserts: asserts_implies_selects / asserts_selects]
Layer 3: Semantic Selection / Authorship (Selects s p q / Authors s p q)
      ↓  [Refuted: selection_not_entails_rejected_horn_meaning / authors_not_entails_rejected_horn_meaning]
Layer 4: Cognitive Alternative Representation (Means s q ∧ Incompatible p q / Contemplates)
      ↓  [PROVEN: deliberateAuthorship_implies_chooses / deliberateChoice_iff_selects_and_means]
Layer 5: Deliberate Authorship / Settlement (DeliberateAuthorship s p q := Authors s p q ∧ Means s q)
      ↓  [PROVEN: deliberateAuthorship_implies_chooses / chooses_implies_freeWill]
Layer 6: Genuine Choice & Free Will (Chooses s p q  →  FreeSubject s / FreeWill s)
```

This multi-stage hierarchy isolates the exact locus of non-derivability in the pre-A14 theory:
- **Transitions 1 → 2 and 2 → 3** are machine-verified theorems of logic and assertion.
- **Transition 3 → 4** is the sole unbridgeable cognitive boundary: selecting or authoring *against* $q$ does not force *thinking* or *co-meaning* $q$.
- **Transitions 4 → 5 → 6** are definitional identities.

#### Four Rigorously Separated Phenomena of Agency

1. **Causal Outcome (`CausalSettles`):** Physical execution bringing about $p$ and suppressing $q$ in state space; satisfied by deterministic systems (`ModelM2BranchingInitiation`). Does not entail mental representation.
2. **Contemplative Representation (`ContemplatesWithoutSettling`):** Co-meaning incompatible options without physical action; satisfied by `ContemplationWithoutActionModel` (`contemplation_without_action`). Shows that cognitive free will does not require overt physical action.
3. **Selection / Authorship (`Authors` / `Selects`):** Executive determination of $p$ over $q$ without representing $q$; satisfied by `Single` (`authors_not_entails_rejected_horn_meaning`).
4. **Deliberate Choice (`DeliberateAuthorship` / `DeliberateChoice` / `Chooses`):** Active commitment with dual cognitive representation of both incompatible options.

#### Three Epistemic Levels of Constitutivity in Γ

- **Constitutive by Definition (DEFINITIONAL):** `FreeWill` from `Chooses` (`FreeWill s := ∃ p q, Chooses s p q`); `Chooses` from `DeliberateAuthorship`.
- **Constitutive by Semantic Axiom (SEMANTIC):** `AxIntentionalChoice` (A14): substantive commitment that intentional initiation constitutively involves cognitive alternativity, proven independent of pre-A14 primitives by machine-checked full-theory countermodels.
- **Constitutive by Derivation (DERIVED):** `ChoiceField s p (¬p)` from `Act s p`; `Selects s p (¬p)` from `Asserts s p`.

#### O Contraste Definidor: A14 (Ato → Escolha) vs. Inverso de A14 (Escolha → Ato)

A relação entre ação intencional e escolha genuína é assimetricamente estruturada:

- **A14 (`Act s p → ∃ q, Chooses s p q`):** Princípio semântico constitutivo adotado (`Tag: SEM`). Postula que a ação intencional envolve constitutivamente a faculdade cognitiva de escolha entre alternativas.
- **Inverso de A14 (`(∃ q, Chooses s p q) → Act s p`):** **REFUTADO POR MODELO HOSTIL** (`ContemplationWithoutActionModel.universal_reverse_a14_refuted` e `existential_reverse_a14_refuted`). A escolha genuína e o livre-arbítrio são faculdades cognitivas/deliberativas (`Means s p ∧ Means s q ∧ Incompatible p q`) que não exigem execução ou iniciação causal física (`Initiates s w w' p`). Um sujeito pode escolher e deliberar em puro pensamento contemplativo sem agir no mundo físico.

Conclusão filosófica: **A escolha genuína não acarreta execução. Escolha cognitiva e ação intencional são fenômenos ontologicamente distintos.**

#### Auditoria da Negação Auto-Referencial da Escolha

Investigou-se se uma asserção auto-referencial que nega a existência de escolha em si mesma (`SelfDenialOfChoice s p := Act s p ∧ (p ↔ ∀ q, ¬ Chooses s p q)`) poderia forçar a escolha genuína por retorção performativa.

- **Resultado:** **REFUTADO POR MODELO HOSTIL** (`SelfDenialOfChoiceModel.self_denial_not_derives_choice` e `self_denial_without_choice_consistent`).
- **Mecanismo:** Em semântica verídica, a proposição $p := (\forall q, \neg \text{Chooses}(s, p, q))$ é estritamente verdadeira; o agente intencionalmente significa $p$, inicia o proferimento de $p$, e de facto não possui escolha alguma, sem qualquer contradição. Ao contrário da negação de atos (onde negar o ato destrói a própria execução), negar a escolha apenas exige agir, não escolher.
- **Conclusão:** A auto-referência não ultrapassa A14; refutar a negação da escolha pressupõe a própria bilateralidade cognitiva (A13/A14) em vez de a derivar.

#### Auditoria da Escolha Livre Auto-Referencial (Candidatas A, B, C, D)

Investigou-se se asserir positivamente a escolha livre de si mesmo ("Escolho livremente este próprio ato") poderia derivar a escolha genuína ou gerar contradição performativa sem assumir A14.

- **Candidata A (Escolha Genuína Auto-Asserida, `p ↔ ∃ q, Chooses s p q`):**
  - Sob asserção fáctica (`Asserts s p`), $p$ é verdadeiro, logo $\exists q, \text{Chooses}(s, p, q)$ segue por **pura lógica/desprendimento definicional** (`selfAssertedChoice_factive_implies_chooses`).
  - Sob ação intencional não-fáctica (`Act s p`), o agente pode proferir iludidamente $p$ num mundo determinista onde $p$ é falso e nenhuma escolha existe (**REFUTADO POR MODELO HOSTIL**, `DelusionalSelfChoiceModel.nonfactive_self_choice_not_derives_choice`).
- **Candidata B (Autoria Auto-Asserida, `p ↔ ∃ q, Authors s p q`):** A autoria executiva verdadeira não força a representação cognitiva do corno rejeitado (`Single.authors_not_entails_rejected_horn_meaning`).
- **Candidata C (Escolha Deliberada Auto-Asserida, `p ↔ ∃ q, DeliberateChoice s p q`):** Sob asserção fáctica, deriva escolha por desprendimento (`selfAssertedDeliberateChoice_factive_implies_chooses`); sob ação não-fáctica, falha por auto-atribuição falsa.
- **Candidata D (Paradoxo Auto-Referencial, `p ↔ (∃ q, Chooses s p q) ∧ (∀ q, ¬ Chooses s p q)`):** $p$ é logicamente falso (`selfAssertedParadox_is_false`). A asserção fáctica é auto-refutante (`selfAssertedParadox_not_assertable`), mas o proferimento de uma falsidade em ato não-fáctico não instancia escolha.

Conclusão: **A auto-referência positiva apenas deriva a escolha se a auto-atribuição for previamente admitida como verdadeira (fáctica), o que não pode ser generalizado a um ato genérico (`Act s p`) sem assumir A14.**

#### Reconstrução Ontológica da Escolha: Determinação Executiva vs. Deliberação

A auditoria formal revelou que a definição histórica de `Chooses s p q := Means s p ∧ Means s q ∧ Incompatible p q` media a faculdade cognitiva de **Deliberação / Representação Contrastiva** (co-significar simultaneamente ambos os cornos em pensamento), e não a **Escolha Executiva** (o ato de determinação/seleção semântica).

A ontologia reconstruída separa rigorosamente as camadas:
1. **Movimento/Evento Fraco (`act s`):** Comportamento causal/físico sem intencionalidade.
2. **Ato Intencional Forte (`Act s p`):** Significado intencional aliado à iniciação causal de transição de estado.
3. **Campo Objetivo de Alternativas (`ChoiceField s p q`):** Espaço lógico objetivo de alternativas (`Incompatible p q`).
4. **Determinação Executiva / Escolha (`Choice s p := Selects s p (¬p)` e `AuthorshipChoice s p := Authors s p (¬p)`):** O sujeito assere/determina $p$ e exclui $\neg p$.
5. **Deliberação Cognitiva (`Deliberates s p q := Means s p ∧ Means s q ∧ Incompatible p q`):** Contemplação de alternativas em pensamento (legado `Chooses`).
6. **Escolha Deliberada (`DeliberateChoice s p q := Selects s p q ∧ Means s q`):** Determinação executiva unida à consciência cognitiva do corno rejeitado.
7. **Livre Agência (`FreeAgency s := ∃ p, Choice s p`):** Capacidade de determinação executiva.

- **Teorema da Retorção Performativa da Escolha (`selfDenialOfExecutiveChoice_selfRefutes`):**
  A asserção auto-referencial "Esta minha asserção não possui Escolha" (`SelfDenialOfExecutiveChoice s p := Asserts s p ∧ (p ↔ ¬ Choice s p)`) é uma **CONTRADIÇÃO PERFORMATIVA GENUÍNA** (`SelfDenialOfExecutiveChoice s p → False`, derivado por pura lógica/definições). O próprio ato de asserir $p$ instancia a determinação executiva `Choice s p`, destruindo o conteúdo da negação!

This clarifies that genuine choice constitutively requires *alternativity* (`Incompatible p q` entertained in thought), but does not intrinsically require the formal operator of contradictory propositional negation (`¬p`). Model `ContrastiveSeparation` formally demonstrates that an agent can choose between incompatible positive courses of action (e.g. North vs. East) without entertaining `¬North`.

#### Six Foundational Candidate Families for Deriving A14 (Exhaustive Audit)

| Foundational Family | Candidate Formulation | Strict Classification | Hostile Witness / Model | Analysis & Mathematical Mechanism |
|---|---|---|---|---|
| **1. Goal / End-Directedness** | `Goal s g ∧ (p → g) → ∃ q, Means s q ∧ Incompatible g q` | **REFUTED BY HOSTILE MODEL** | `hostileTeleologicalInstance` (`teleology_not_entails_contrastive_agency`) | Valuation: `s = false, p = True, g = True`. In veridical semantics (`Means s p := p`), acting for a true goal does not force representation of an incompatible alternative; factive goal-directedness mathematically excludes co-meaning false $q$. Baking contrastivity into `Goal` is **DEFINITIONAL RECODING — REJECTED**. |
| **2. Reason-Guided Agency** | `ReasonFor s r p ∧ (r → p) → ∃ r' q, Means s r' ∧ Means s q ∧ Incompatible r q` | **REFUTED BY HOSTILE MODEL** | `hostileReasonResponsiveInstance` (`reason_responsiveness_not_entails_contrastive_agency`) | Valuation: `s = false, r = True, p = True`. Acting on a sufficient reason in the actual world does not require occurrent representation of contrary reasons in thought. Dispositions across hypothetical counterfactual worlds do not populate actual occurrent `Means`. |
| **3. Action Individuation under Description** | `Description s p → ∃ q, Means s q ∧ Incompatible p q` | **REFUTED BY HOSTILE MODEL** | `hostileActionIndividuationInstance` (`action_individuation_not_entails_contrastive_agency`) | Valuation: `s = false, p = True`. Individuating an action under description $p$ distinguishes it from non-intended descriptions $p'$ without the subject representing any incompatible alternative description $q$ in thought. |
| **4. Non-Factive Representation Layer** | `Entertains s p → ∃ q, Entertains s q ∧ Incompatible p q` | **REFUTED BY HOSTILE MODEL** | `hostileRepresentationLayerInstance` (`nonfactive_representation_not_entails_contrastive_agency`) | Valuation: `s = false, p = True`. Distinguishing `Means` from a non-factive representation faculty `Entertains` allows entertaining false contents in principle, but does not force the subject to entertain incompatible alternatives; single-content entertainment remains consistent. |
| **5. Counterfactual Agency (State Branching)** | `CouldAct s q ∧ Incompatible p q → Means s q` | **REFUTED BY HOSTILE MODEL** | `ModelM2BranchingInitiation` (`counterfactual_branching_not_entails_means`) | Valuation: Model M2 exhibits physical state-space branching (`w = false ∧ w' ∈ {true, false}`), so alternative initiation holds (`CouldAct () False`), but internal intentional representation `Means () False` remains strictly false. Physical branching does not force cognitive representation. |
| **6. Contrastive Intentionality** | `Act s p → ∃ q, Means s q ∧ Incompatible p q` | **REDUCED TO DEEPER SEMANTIC BRIDGE** · **REDUNDANT** | `fullTheoryHostileInstance` (`act_orthogonal_to_contrastive_agency_in_full_theory`) | Conceptually and logically equivalent to A14 (`contrastive_agency_equivalent_to_intentional_choice`). Strictly independent of pre-A14 primitives, forming the *weakest sufficient bridge identified at the pointwise level* within the audited candidate family. |

#### Machine-Checked Orthogonality Theorem: Act ⟂ Chooses (Pre-A14 Theory)

In `formal/Logos/HostileSemantics.lean`, the kernel formally verifies that under the ENTIRE pre-A14 axiomatic theory of Γ (12 axioms across Agency, Plurality, Truthmaker, Modal, GroundPerson, and Value):

$$\exists s\,p,\; \text{Act}(s,p) \quad \perp \quad \exists s\,p\,q,\; \text{Chooses}(s,p,q)$$

- `act_orthogonal_to_genuine_choice_in_full_theory`: Strong Act does NOT entail Genuine Choice in the pre-A14 theory.
- `act_orthogonal_to_freewill_in_full_theory`: Strong Act does NOT entail Free Will in the pre-A14 theory.
- `act_orthogonal_to_contrastive_agency_in_full_theory`: Strong Act does NOT entail Contrastive Agency in the pre-A14 theory.

Thus, genuine choice is not derivable from Strong Act in the pre-A14 theory; Γ adopts its constitutivity as A14, an authentic substantive semantic commitment (`Tag: SEM`).

Architectural note on the formal definition of `Chooses`: the attempted asymmetric definition `Chooses_asym(s, p, q) := Means(s, p) ∧ Means(s, ¬q) ∧ Incompatible(p, q)` fails by double-negation collapse: for `q := ¬p`, `Means(s, ¬¬p)` reduces to `Means(s, p)`, dissolving the requirement of entertaining the rejected alternative and collapsing genuine choice into mere `ChoiceField`. Genuine choice therefore constitutively requires co-meaning of both alternatives (`Means s p ∧ Means s q ∧ Incompatible p q`).

---

## 3. The deduction

### Stage I — The Performative Starting Point

The argument begins not from an arbitrary propositional premise but from a performative datum: an act of affirming, denying, doubting or judging is occurring. The starting point (`base.txt` §0) is the contrast between an arbitrary premise and a claim whose negation destroys the very act of negating it. The steps below attempt, oppose and refute the absolute theses that nothing — or everything — is true.

**Definition (Weak act vs. strong Act).** `act(s, p)` — *weak act: performed event* (utterance, assertion-event, performance) vs. `Act(s, p) := Means(s, p) ∧ ∃ w w', Initiates(s, w, w', p)` (abbreviated `A(s, p)`) — *strong act: meaningful initiation (its constitutive content is intentional meaning, and its evental character is initiation)*.

**Definition (Weak assertion vs. strong assertion).** `asserts(s, p) := act(s, p) ∧ p` (*weak assertion: performed assertion event*) vs. `Asserts(s, p) := Act(s, p) ∧ p` (*strong assertion: meaning-bearing assertion*).

**Bridge (Weak act to strong act).** `weak_act_implies_strong_act := ∀ s p, act(s, p) → Act(s, p)` (*unforced intentionality bridge*).

**Definition (Subject actuality).** SubjectExists(s) := ∃ p, Act(s, p).

**Definition (Personhood).** Person(s) := Agent(s) ∧ Rational(s) ∧ Intentional(s), where Agent(s) := True, Rational(s) := True, and Intentional(s) := ∃ p, Means(s, p).

**Audit of the Performative Datum.**

- **Current formal datum:** `∃ s p, Act s p`
- **Question:** Is this the complete formal expression of the performative evidence, or does the intended datum contain additional structure?
- **Status: AUDITED.** The intended datum in `base.txt` (§0–§1) encompasses thinking, asserting, judging, and doubting. Strong assertion (`Asserts`) and judgment (`Correct/Incorrect`) derive objective semantic selection (`Selects s p (¬p)`), but no generic candidate entails cognitive representation of the rejected horn (`Means s q`).
- **Constraint:** No strengthening is permitted merely because it helps derive A14. Any strengthening must be independently grounded in the actual performative datum.

**Axiom A2 · Subject (VOCAB).**
\[ Subject : Type \]
The pure sort of subjects — that which performs acts of reasoning.

**Axiom A10 · act (VOCAB).**
\[ act : Subject → Prop → Prop \]
Weak act / performed event — something is performed, uttered, asserted, or denied.

**Proposition C58 (Step 4 (weak retorsion)).**

Asserting that no performed event occurs refutes itself directly

\[ asserts(speaker, NoWeakAct) → False \]

**Proof.** Assume asserts(speaker, NoWeakAct). Follows under **A10**, **A2**. ∎

**Obstruction.** `CountermodelWeakActWithoutMeaning` — A performed event (utterance, keystroke, physical emission) does not entail an intentional meaning-act: `act s p` can occur without `Means s p`.

**Γ's answer.** the step is constitutive in Γ, not a logical consequence.

`Lean: Agency.lean#L182 · uses A2, A10 · DEFINITIONAL ✔`

**Axiom A5 · Means (VOCAB).**
\[ Means : Subject → Prop → Prop \]
The meaning-act relation — a subject means a proposition.

**Axiom A11 · State (VOCAB).**
\[ State : Type \]
Abstract state space for initiation of movement.

**Axiom A12 · Initiates (VOCAB).**
\[ Initiates : Subject → State → State → Prop → Prop \]
The initiation relation — a subject initiates a transition between states positing content.

**Proposition C68 (Cogito as a derived theorem (strong shortcut)).**

Any strong assertion entails that an intentional act occurs.

\[ Asserts(s, p) → ∃ s', p', Act(s', p') \]

**Proof.** Assume Asserts(s, p). Follows under **A2**. ∎

`Lean: Agency.lean#L261 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`

**Proposition C83 (The Cartesian Retortion (half 1)).**

No subject can ever correctly judge that no act occurs

\[ ¬Correct(s, NoAct) \]

**Proof.** Under **a2**, the assumption refutes itself. ∎

`Lean: Order.lean#L204 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`

**Proposition C84 (The Retorsive Cogito).**

Even the skeptic's denial that any act occurs strictly witnesses that an act occurs. The act cannot be denied without providing the witness that refutes the denial.

\[ (Correct(s, NoAct) ∨ Incorrect(s, NoAct)) → ∃ s', p', A(s', p') \]

**Proof.** Assume Correct(s, NoAct) ∨ Incorrect(s, NoAct). The required witness is constructed under **A2**. ∎

`Lean: Order.lean#L225 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`

**Lemma C63 (Initiation is not transfer).**

A relation with genuine alternatives is not the graph of any function.

\[ Branches(R) → ¬IsTransfer(R) \]

**Proof.** Assume Branches(R). By definition, the assumption refutes itself. ∎

`Lean: Initiation.lean#L27 · LOGICAL ✔`


### Stage II — Truth and Falsehood

Once an act of meaning is occurring, truth and falsehood cannot both be abolished. The performative absolutes refute themselves (C1–C9); the classical laws and the object-language distinction between truth and falsehood follow (C10–C12). The stage closes with the transcendental principles of semantics and the elementary truthmaker step.

**Definition (Truth and falsehood).** T(p) := p (truth is identity, E0) and IsFalse(p) := ¬T(p).

**Definition (The absolutes).** N_T := ∀ p, ¬T(p) (nothing is true) and N_F := ∀ p, T(p) (everything is true).

**Lemma C1 (It cannot be true that nothing is true).**

Asserting 'nothing is true' would itself be a true proposition.

\[ ¬T(N_T) \]

**Proof.** `T(N_T)` cannot hold: assuming it forces both `N_T` and `¬T(N_T)`. ∎

`Lean: Core.lean#L61 · LOGICAL ✔`

**Lemma C2 (It is false that nothing is true).**

Some proposition is true.

\[ ¬N_T \]

**Proof.** ¬(∀p ¬T(p)): it is not the case that nothing is true (classical step §4). ∎

`Lean: Core.lean#L69 · LOGICAL ✔`

**Lemma C3 (Some proposition is true).**

\[ ∃ p, T(p) \]

**Proof.** There is at least one true proposition. ∎

`Lean: Core.lean#L77 · LOGICAL ✔`

**Lemma C4 (The proposition True is itself true).**

\[ T(True) \]

**Proof.** Follows directly from the definitions. ∎

`Lean: Core.lean#L85 · LOGICAL ✔`

**Lemma C5 (It cannot be true that nothing is false).**

If it were, the falsehood False would be true.

\[ ¬T(N_F) \]

**Proof.** `T(N_F)` cannot hold: `∀p T(p)` applied to the proposition `False`. ∎

`Lean: Core.lean#L94 · LOGICAL ✔`

**Lemma C6 (It is false that everything is true).**

Some proposition is false.

\[ ¬N_F \]

**Proof.** ¬(∀p T(p)): it is not the case that everything is true. ∎

`Lean: Core.lean#L103 · LOGICAL ✔`

**Lemma C7 (Some proposition is false).**

\[ ∃ q, IsFalse(q) \]

**Proof.** There is at least one false proposition. ∎

`Lean: Core.lean#L111 · LOGICAL ✔`

**Lemma C8 (Truth and falsehood both obtain).**

Some proposition is true and some proposition is false.

\[ ∃ p, q, T(p) ∧ IsFalse(q) \]

**Proof.** T3 — truth and falsehood are both necessarily instantiated, hence `T ≠ F` as statuses: `∃p, T(p)` and `∃q, ¬T(q)`. ∎

`Lean: Core.lean#L156 · LOGICAL ✔`

**Lemma C9 (No proposition is both true and false).**

\[ ∀ p, ¬(T(p) ∧ IsFalse(p)) \]

**Proof.** No proposition is both true and false (non-contradiction for T). ∎

`Lean: Core.lean#L162 · LOGICAL ✔`

**Lemma C10 (For every proposition p, 'p or not-p' is true).**

\[ ∀ p, T((p ∨ ¬p)) \]

**Proof.** Follows directly from the definitions. ∎

`Lean: Core.lean#L174 · LOGICAL ✔`

**Lemma C11 (For every proposition p, 'not (p and not-p)' is true).**

\[ ∀ p, T((¬(p ∧ ¬p))) \]

**Proof.** Follows directly from the definitions. ∎

`Lean: Core.lean#L180 · LOGICAL ✔`

**Lemma C12 (Every proposition is either true or false).**

\[ ∀ p, T(p) ∨ IsFalse(p) \]

**Proof.** Bivalence, §10: each proposition is true or false (is false iff not true). ∎

`Lean: Core.lean#L186 · LOGICAL ✔`

**Lemma C13 (In every world, 'φ or not-φ' is true).**

\[ □(φ ∨ ¬φ) \]

**Proof.** Follows by classical logic (**CL**). ∎

`Lean: Semantics.lean#L76 · LOGICAL ✔`

**Lemma C14 (In every world, 'φ and not-φ' cannot be true).**

\[ ¬◇(φ ∧ ¬φ) \]

**Proof.** By classical logic (**cl**), the assumption refutes itself. ∎

`Lean: Semantics.lean#L85 · LOGICAL ✔`

**Lemma C16 (In every world, 'φ or not-φ' is true — composite truth is Tarskian-compositional).**

\[ □(φ ∨ ¬φ) \]

**Proof.** Follows directly from the definitions. ∎

`Lean: Truthmaker.lean#L140 · LOGICAL ✔`

**Lemma C17 (In every world, 'φ and not-φ' cannot be true).**

\[ ¬◇(φ ∧ ¬φ) \]

**Proof.** By definition, the assumption refutes itself. ∎

`Lean: Truthmaker.lean#L148 · LOGICAL ✔`

**Lemma C31 (Consequence preserves truth).**

Whatever two true premises jointly imply is true.

\[ (p₁ → p₂ → q) → T(p₁) → T(p₂) → T(q) \]

**Proof.** Assume p₁ → p₂ → q, and T(p₁), and T(p₂). Follows directly from the definitions. ∎

`Lean: Order.lean#L195 · LOGICAL ✔`

**Lemma C35 (It is neither the case that nothing is true, nor that nothing is false).**

\[ ¬(N_T ∨ N_F) \]

**Proof.** `¬(N_T ∨ N_F)`: it is not the case that (either nothing is true or nothing is false) — the poem's "p1 ∨ p2 is a contradiction"; classically from `notNothingTrue` (C2) and `notEverythingTrue` (C6). ∎

`Lean: Core.lean#L129 · LOGICAL ✔`

**Lemma C36 (Right and wrong both obtain).**

It is false that nothing is true, and false that everything is true.

\[ ¬N_T ∧ ¬N_F \]

**Proof.** Right AND wrong both obtain: `¬N_T ∧ ¬N_F`, classically from `¬(N_T ∨ N_F)` — the direct witness for the poem's P2 conclusion "há certo e há errado". ∎

`Lean: Core.lean#L145 · LOGICAL ✔`

**Proposition C101 (Bivalent partition of intentional meaning (Route B milestone)).**

Every intentional act is constitutively either a veridical assertion (correct stance) or an erroneous judgment (incorrect stance). An agent cannot mean a content without that meaning being either truth-affirming or truth-violating.

\[ A(s, p) ↔ Asserts(s, p) ∨ Incorrect(s, p) \]

**Proof.** Evaluating by disjunctive cases under **A2**. ∎

`Lean: Order.lean#L57 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`


### Stage III — The Subject of Thought

The act is always an act *of* a subject and *about* content. From the performative datum Γ reads off the existence of a subject of thought (C21), the subject's inseparability from its act, and the collapse of the subject into the person (*esse est agere*). The stage is definitional modulo the vocabulary of agency.

**Proposition C21 (At least one subject exists).**

Derived from the performative act-datum.

\[ (∃ s, p, Act(s, p)) → ∃ s, SubjectExists(s) \]

**Proof.** T1 (C21) — the subject of the present act exists: derived from the existence of an intentional act(C68, via) the constitutive rule `act_requires_subject` (Case B). Footprint: `{Initiates, Means, State, Subject}` (VOCAB only; decoupled from AxTwoSubjects). ∎

**Obstruction.** `CountermodelActWithoutSubject` — Without a constitutive rule, an act can occur in the void with no actualizing subject (Lichtenberg's objection).

**Γ's answer.** the step is DEFINITIONAL in Γ, not LOGICAL: it follows from `Act s p := Means s p ∧ ∃ w w', Initiates s w w' p`; `act_requires_subject : Act s p → SubjectExists s`.

`Lean: Plurality.lean#L67 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`

**Lemma C22 (At least one content exists).**

Every proposition is admissible content.

\[ ∃ p, Content(p) \]

**Proof.** T2 — there is propositional content. Now axiom-free: `Content` is the analytical definition `Content(_) := True`, so `True` itself witnesses content (cogito no longer needed). ∎

`Lean: Agency.lean#L320 · LOGICAL ✔`

**Proposition C23 (At least one agent exists).**

Someone who acts.

\[ (∃ s, p, Act(s, p)) → ∃ s, SubjectExists(s) ∧ Agent(s) \]

**Proof.** T4 (C23) — the subject is an agent (`Agent` is analytical `:= True`): derived from the existence of an intentional act (C68 → C21). Footprint: `{Initiates, Means, State, Subject}`. ∎

**Obstruction.** `CountermodelActWithoutSubject` — an act occurring with no actualizing subject (see Appendix C.1).

**Γ's answer.** the step is DEFINITIONAL in Γ, not LOGICAL: it follows from Act → Agent is constitutive in Γ.

`Lean: Plurality.lean#L75 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`

**Theorem C24 (At least one intentional subject exists).**

Someone who means content

\[ (∃ s, p, Act(s, p)) → ∃ s, IntentionalSubject(s) \]

**Proof.** Assume ∃ s, p, Act(s, p). Follows under **A2**. ∎

**Obstruction.** `CountermodelNoPerson` — The bare act-datum `∃ s p, A s p` does not force any `Person`.

**Γ's answer.** the step is DEFINITIONAL in Γ, not LOGICAL: it follows from §12 reduction `Person s := Agent s ∧ Rational s ∧ Intentional s` with `Agent, Rational := True` (`Person.person_intentional_iff`).

`Lean: Plurality.lean#L83 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`

**Proposition C25 (Every rational act carries a personal feature exactly when it carries a logical feature).**

Personhood and logic travel together.

\[ ∀ a, RationalAct(a) → (CarriesPersonalFeature(a) ↔ CarriesLogicalFeature(a)) \]

**Proof.** Evaluating by disjunctive cases under **A2**, **A5**. ∎

`Lean: Person.lean#L143 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`

**Proposition C49 (Meaning needs a subject).**

Whatever is meant is meant by someone.

\[ Means(s, p) → ∃ t, Means(t, p) \]

**Proof.** No meaning without a subject (analytic): the intentional relation `Means : Subject → Prop → Prop` only exists relata-subjected, so the subject of any meaning is itself the witness. ∎

`Lean: Choice.lean#L137 · uses A2, A5 · DEFINITIONAL ✔`

**Proposition C57 (Retorsion — asserting that no actual subject exists refutes itself).**

\[ Asserts(speaker, NoSubject) → False \]

**Proof.** Assume Asserts(speaker, NoSubject). Follows under **A2**. ∎

`Lean: Choice.lean#L398 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`

**Proposition C62 (Right and wrong need meaning).**

The normative predicates are properties of acts, so wherever right-or-wrong is realized, meaning (and thus a subject, C49) is realized.

\[ (∃ s, p, Correct(s, p)) ∨ (∃ s, p, Incorrect(s, p)) → ∃ p, Meaning_I(p) \]

**Proof.** "For right to be distinct from wrong, meaning must be a thing" (poem P3, line 18). Pure projection from the §8 definitions: `Correct(s, p)` unfolds to `A(s, p) ∧ T(p)` where `A(s, p) := Means(s, p) ∧ ∃ w, w', Initiates s w w' p`, so the witness content `p`, meant by `s`, is a `Meaning_I` (via `hc.1.1`). Footprint `{Initiates, Means, State, Subject}` (vocab-only — no substantive axiom): no model can assert `Correct`/`Incorrect` while denying meaning, because `A(s, p)` has `Means(s, p)` as its constitutive content. ∎

`Lean: Order.lean#L91 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`


### Stage IV — Agency and Choice

A subject that acts and judges is a person before a field of incompatible alternatives. C26/C27/C50 supply the alternatives; C39 and C51/C52 derive the choice field and its performative retorsion (C53); C54/C61 connect it to right-and-wrong; C28/C29 record fallibility. F1b (genuine choice and free will) is closed under the adopted constitutive semantic principle AxIntentionalChoice (A14, SEM). Strong Act and Genuine Choice are proven orthogonal in the pre-A14 theory (act_orthogonal_to_genuine_choice_in_full_theory), with AxIntentionalChoice adopted as the minimal constitutive bridge.

**Definition (Incompatibility, weak choice, and strong choice).** Incompatible(p, q) := ¬(p ∧ q), ChoiceField(s, p, q) := Means(s, p) ∧ Incompatible(p, q) (*weak choice: incompatible alternatives are present*), and Chooses(s, p, q) := Means(s, p) ∧ Means(s, q) ∧ Incompatible(p, q) (*strong choice: the subject co-means incompatible alternatives*).

**Architectural note (Asymmetric definition ruled out by double-negation collapse).** A tempting alternative definition of choice as asymmetric rejection, `Chooses_asym(s, p, q) := Means(s, p) ∧ Means(s, ¬q) ∧ Incompatible(p, q)` (meaning the selected alternative and meaning the negation of the rejected alternative), fails mathematically in the canonical contradictory case `q := ¬p`: because `¬(¬p) ↔ p`, `Means(s, ¬¬p)` collapses under classical logic (`Classical.propext`) to `Means(s, p)`. Hence `Chooses_asym(s, p, ¬p)` dissolves into `Means(s, p) ∧ Incompatible(p, ¬p)` — which is identically `ChoiceField(s, p, ¬p)` — requiring zero representation of the rejected alternative and destroying the hostile-model separation between field and choice. Therefore, genuine choice strictly requires symmetric co-meaning of the incompatible alternatives: `Chooses(s, p, q) := Means(s, p) ∧ Means(s, q) ∧ Incompatible(p, q)`.

**Definition (Free will).** FreeWill(s) := ∃ p, q (Chooses(s, p, q)) (*freedom: definitional from strong choice*).

**Frontier (Genuine choice).** deliberateGenuineChoiceResource := ∃ s p, Asserts(s, p) ∧ Means(s, ¬p) (*the minimal resource sufficient to prove genuineChoice_exists and deliberateChoice_exists; its existence remains open*).

**Definition (Judgment quality).** Correct(s, p) := A(s, p) ∧ T(p), Incorrect(s, p) := A(s, p) ∧ IsFalse(p), and Fallible(s, p) := IsFalse(p).

**Lemma C26 (There are two incompatible alternatives, one of them true and the other false).**

\[ ∃ p, q, Incompatible(p, q) ∧ T(p) ∧ IsFalse(q) \]

**Proof.** T9 — there are at least two incompatible contents, one true and one false: the minimal field of rational choice of §13 is non-empty, and it is present constructively (no choice axioms). ∎

`Lean: Alternatives.lean#L24 · LOGICAL ✔`

**Lemma C27 (Every true proposition is incompatible with its own negation).**

\[ T(p) → Incompatible(p, ¬p) ∧ T(p) ∧ IsFalse(¬p) \]

**Proof.** General form: any true content and its own negation are incompatible. ∎

`Lean: Alternatives.lean#L35 · LOGICAL ✔`

**Lemma C50 (Every proposition is incompatible with its own negation).**

\[ Incompatible(p, ¬p) \]

**Proof.** A(proposition, and) its own negation are always incompatible options (`¬(p ∧ ¬p)`, pure logic, footprint `{}`) — the field around any meaning-act(is, non)-empty. ∎

`Lean: Choice.lean#L113 · LOGICAL ✔`

**Proposition C39 (There is a field of choice).**

Some intentional subject with two incompatible alternatives.

\[ (∃ s, p, A(s, p)) → ∃ s, IntentionalSubject(s) ∧ ∃ p, q, Incompatible(p, q) \]

**Proof.** T11 (C39) — the minimal field of rational choice is non-empty for an intentional subject: derived from an intentional act(datum, (C68 → C21 → C39)). Footprint: `{Initiates, Means, State, Subject}` (VOCAB only; decoupled from AxTwoSubjects). ∎

**Obstruction.** `CountermodelNoPerson` — the bare act datum forcing `Person` (see Appendix C.1).

**Γ's answer.** the step is DEFINITIONAL in Γ, not LOGICAL: it follows from `ChoiceField s p q := Means s p ∧ Incompatible p q` (the second horn is supplied by logic, C27/C50).

`Lean: Choice.lean#L290 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`

**Lemma C51 (Any person has a choice field).**

A person is always before two incompatible alternatives.

\[ Person(s) → ∃ p, q, ChoiceField(s, p, q) \]

**Proof.** Audit notice (freedom/choice fix, 2026-09-18): this yields `ChoiceField`, NOT genuine `Chooses`. The agent is related only to the adopted content `p`; the rejected horn `¬p` is supplied by pure logic (`incompatible_self_negation`), not by the agent. The genuine form (both horns co-meant) is BLOCKED on `rejectedHornCoMeant`. Nominal wrapper of `intentional_hasChoiceField` (the §12 label adds nothing). ∎

`Lean: Choice.lean#L320 · uses A2, A5 · DEFINITIONAL ✔`

**Proposition C52 (The choice field exists).**

Some subject is before two incompatible alternatives.

\[ (∃ s, p, A(s, p)) → ∃ s, p, q, ChoiceField(s, p, q) \]

**Proof.** C52 (field form) — the field is real: derived from an intentional act(datum, (C68 → C52)) through the WEAKER predicate `Intentional` (via `act_implies_intentional`), not through the §12 person label: `SubjectExists`/`Intentional` suffices. Footprint: `{Initiates, Means, State, Subject}` (VOCAB only). ∎

`Lean: Choice.lean#L330 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`

**Proposition C53 (Performative retorsion — asserting that no choice field exists refutes itself).**

Footprint: `{Initiates, Means, State, Subject}` (VOCAB only; zero AxTwoSubjects).

\[ Asserts(speaker, NoChoiceField) → False \]

**Proof.** Assume Asserts(speaker, NoChoiceField). Follows under **A2**. ∎

`Lean: Choice.lean#L355 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`

**Axiom A6 · AxTwoSubjects (META).**
\[ (¬N_T ∧ ¬N_F) → ∃ s₁, s₂, Person(s₁) ∧ Person(s₂) ∧ s₁ ≠ s₂ \]
The *reality* of right-and-wrong demands that there be at least two distinct persons. Narrower than the former single bridge `AxValueInterpersonal` (plurality only…

*Philosophical cost:* A substantive interpersonal metaphysics. A lone judging subject, and the unit world of a single act, remain logically consistent with every earlier premise, so the demand for a second distinct person is posited, not deduced. Plural personal reality is bought with this declared bridge.

**Theorem C54 (Right-and-wrong commits a choice field).**

Where there is truth and error, someone is before an incompatible pair.

\[ (¬N_T ∧ ¬N_F) → ∃ s, p, q, ChoiceField(s, p, q) \]

**Proof.** C54 (field form): "No right and wrong without (a field of) choice" — whenever the distinction holds, some subject before a choice field exists via AxTwoSubjects(poem P5). The genuine `Chooses` conclusion is BLOCKED on `rejectedHornCoMeant`. ∎

`Lean: Choice.lean#L371 · uses A2, A5, A6 · METAPHYSICAL ⚠`

**Theorem C61 (Right-and-wrong implies someone who means).**

(poem P3, line 18 "há certo e há errado → há significado → há alguém para quem algo significar")

\[ (¬N_T ∧ ¬N_F) → ∃ s, p, Means(s, p) \]

**Proof.** C61: `JUDGE_HAS_CHOICE_FIELD` (C54) composes with `rightWrongDistinction` (C36) to yield a field; its first conjunct is a meaning-act, so some subject means some content. ∎

`Lean: Choice.lean#L391 · uses A2, A5, A6 · METAPHYSICAL ⚠`

**Theorem C28 (A fallible judgment need not be true).**

Fallibility is real.

\[ ¬(∀ s, p, Fallible(s, p) → T(p)) \]

**Proof.** T6 — truth is not created by asserting: assertion ⇒ truth fails (under **A2**). ∎

`Lean: Order.lean#L135 · uses A2, A5, A6 · METAPHYSICAL ⚠`

**Theorem C29 (Truth is not the same as being fallibly judged).**

What is true transcends the will to judge.

\[ ¬(∀ s, p, Fallible(s, p) ↔ T(p)) \]

**Proof.** T6, second form: `Truth ≠ WillOfAgent` — no equivalence can hold between willing-asserting and being true. ∎

`Lean: Order.lean#L144 · uses A2, A5, A6 · METAPHYSICAL ⚠`

**Proposition C97 (Deliberate choice strictly entails semantic selection).**

\[ DeliberateChoice(s, p, q) → Selects(s, p, q) \]

**Proof.** Assume DeliberateChoice(s, p, q). The required witness is constructed under **A2**, **A5**. ∎

`Lean: Choice.lean#L490 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`

**Proposition C98 (Deliberate choice entails genuine choice in the co-meaning sense).**

\[ DeliberateChoice(s, p, q) → Chooses(s, p, q) \]

**Proof.** Assume DeliberateChoice(s, p, q). The required witness is constructed under **A2**, **A5**. ∎

`Lean: Choice.lean#L496 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`

**Proposition C99 (Under the explicit Candidate C bridge, an intentional act yields semantic selection).**

\[ act_implies_asserts_bridge → (∃ s, p, Act(s, p)) → ∃ s, p, q, Selects(s, p, q) \]

**Proof.** Assume act_implies_asserts_bridge, and ∃ s, p, Act(s, p). The required witness is constructed under **A2**. ∎

`Lean: Choice.lean#L693 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`

**Proposition C100 (Exact decomposition of deliberate choice (Route C milestone)).**

Deliberate choice between `p` and `q` is definitionally equivalent to semantic selection of `p` against `q` plus awareness (intentional representation) of the alternative horn `q`.

\[ DeliberateChoice(s, p, q) ↔ Selects(s, p, q) ∧ Means(s, q) \]

**Proof.** The required witness is constructed under **A11**, **A12**, **A2**, **A5**. ∎

`Lean: Choice.lean#L504 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`

**Axiom A13 · AxActPolarity (SEM).**
\[ ∀ s, p, Act(s, p) → Means(s, ¬p) \]
Act polarity: initiating an intentional act constitutively endows the agent with the representation of its contradictory negation.

**Axiom A14 · AxIntentionalChoice (SEM).**
\[ ∀ s, p, Act(s, p) → ∃ q, Chooses(s, p, q) \]
Genuine choice is constitutive of intentional action: an intentional act is an initiation performed through the subject's apprehension of an incompatible alternative.

**Theorem F1b (Free will exists).**

Some subject genuinely chooses between incompatible alternatives.

\[ (∃ s, p, Act(s, p)) → ∃ s, FreeWill(s) \]

**Proof.** Primary target theorem closing F1b under the performative datum of intentional action and the adopted constitutive principle AxIntentionalChoice. Footprint: `{AxIntentionalChoice, Initiates, Means, State, Subject}`. ∎

**Obstruction.** `CountermodelVeridicalMeaning` — The act-datum does not force `genuineChoice_exists` even under the Logos definition of `Chooses`: veridical meaning makes co-meaning an incompatible pair impossible while the whole agency/choice/order fragment holds.

**Obstruction.** `CountermodelNoFreeWill` — Mere occurrence of an act does not entail genuine choice: an uninterpreted determined act with `Chooses := False` satisfies the datum while `Chooses` and `FreeWill` stay empty.

**Γ's answer.** the step rests on a substantive semantic principle, not logic alone.

`Lean: Choice.lean#L1118 · uses A2, A5, A11, A12, A14 · SEMANTIC ⚠`

**Corollary (Free will is definitional).**

\[ Chooses(s, p, q) → FreeWill(s) \]

**Proof.** Immediate from FreeWill(s) := ∃ p, q (Chooses(s, p, q)) (definitional unrolling). ∎

`Lean: Choice.lean#L151 · uses A5 · DEFINITIONAL ✔`


### Stage V — Necessity

From the semantic principles and the modal backbone Γ derives the necessary: excluded middle and non-contradiction, the necessary person, and the necessary reality (T7). The person/entity lifts are definitional; the necessary reality itself is the first place a substantive bridge — `AxGlobalGround` — is priced.

**Definition (World necessity).** NecessarilyTrue(φ) := ∀ w, TrueAt(w, φ) (written □ φ) and NecessarilyFalse(φ) := ∀ w, FalseAt(w, φ) (written ¬◇ φ).

**Definition (Necessary entities and persistence).** NecessaryEntity(e) := ∀ w, ExistsAt(w, e), Contingent(e) := ¬NecessaryEntity(e), and NecessarySubject(s) := ∀ w, ExistsAt(w, EntityOf(s)).

**Lemma C37 (In every world there is necessarily-true content and necessarily-false content).**

\[ (∃ τ, □ τ) ∧ (∃ ρ, ¬◇ ρ) \]

**Proof.** There is a necessarily-true content AND a necessarily-false one (the poem's "há certo E há errado" where "errado" is level-1 falsity), witnessed by the excluded-middle tautology and the non-contradiction anti-tautology, respectively. ∎

`Lean: Semantics.lean#L102 · LOGICAL ✔`

**Lemma C38 (The distinction between right and wrong under the identity-model alias).**

\[ □(¬N_T ∧ ¬N_F) \]

**Proof.** NOTE: `Necessity(p)` is an identity alias (`Necessity(p) ↔ p`), not genuine metaphysical necessity. The genuine world-level modal theorem is `Semantics.bothNecessarilyTrueAndFalse` (C37). ∎

`Lean: Necessity.lean#L116 · LOGICAL ✔`

**Lemma C59 (Strong truth exists).**

Some formula is true in every world — axiom-free, the performative "há certo E há errado" (§27, poem.txt), resident as the excluded-middle datum C37 (footprint {CL}).

\[ ∃ τ, □ τ \]

**Proof.** The required witness is constructed directly. ∎

`Lean: Semantics.lean#L113 · LOGICAL ✔`

**Lemma C93 (Denying strong truth refutes itself).**

It cannot be the case that no formula is necessarily true — the act of denying strong truth is destroyed by strong truth (performative retorsion of C59, footprint {CL}).

\[ ¬(¬∃ τ, □ τ) \]

**Proof.** By definition, the assumption refutes itself. ∎

`Lean: Semantics.lean#L121 · LOGICAL ✔`

**Proposition C94 (No one can assert "there is no strong truth").**

The act of denying the world-level datum is destroyed by the datum itself (assertive retorsion of C93, completing the retorsion family at the assertion level; footprint {Means, Subject, CL}).

\[ Asserts(speaker, ¬∃ τ, □ τ) → False \]

**Proof.** Under **a2**, the assumption refutes itself. ∎

`Lean: Choice.lean#L1227 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`

**Lemma C95 (The atoms are modally free).**

No atom is fixed in either modal direction.

\[ ∀ n, ¬□atom(n) ∧ ¬¬◇atom(n) \]

**Proof.** The atom-wall, combined form (footprint {}). ∎

`Lean: Semantics.lean#L146 · LOGICAL ✔`

**Lemma C96 (Contingent content exists — the counterweight of C59 (GAPMAP.md C96)).**

Some formula is neither necessary nor impossible, derived from the atom-wall (footprint {}).

\[ ∃ τ, ¬□ τ ∧ ¬¬◇ τ \]

**Proof.** Evaluating by disjunctive cases from premises. ∎

`Lean: Semantics.lean#L160 · LOGICAL ✔`

**Theorem C77 (Conditional C77).**

If person stability holds and intentional action confers personhood, an intentional act yields a necessary person.

\[ PersonStabilityPrinciple → (∀ s, p, Act(s, p) → Person(s)) → (∃ s, p, Act(s, p)) → ∃ s, Person(s) ∧ NecessarySubject(s) \]

**Proof.** Assume PersonStabilityPrinciple, and ∀ s, p, Act(s, p) → Person(s), and ∃ s, p, Act(s, p). The required witness is constructed under **A2**. ∎

**Obstruction.** `CountermodelPersonNotNecessary` — A person need not be a necessary subject: `Person → NecessarySubject` fails as a logical law (subject exists only in the `true` world).

**Γ's answer.** the step is DEFINITIONAL in Γ, not LOGICAL: it follows from `AxPersonStability : Person s → NecessarySubject s` (esse est agere).

`Lean: Love.lean#L98 · uses A2, A5, A11, A12 · DEFINITIONAL / CONDITIONAL ✔`

**Proposition C91 (A subject that is necessary has an entity-correlate that is a necessary entity).**

\[ NecessarySubject(s) → NecessaryEntity(EntityOf(s)) \]

**Proof.** Necessity(lift) (subject → entity, C91): if the subject `s` persists in every world (`NecessarySubject(s)`), its entity-correlate `EntityOf(s)` is an entity that exists in every world. The lift is *definitional*: `ExistsAt` is one shared relation and `EntityOf` is the Truthmaker(embedding), so both sides unfold to `∀ w, ExistsAt(w, EntityOf(s))`. It carries no SEM/META price; its force is exactly the definitions chosen in Plurality/Truthmaker. Hostile separation (not a logical law): `CountermodelSubjectNecessityNotEntityNecessity` in HostileSemantics. Footprint: `{Subject}`. ∎

**Obstruction.** `CountermodelSubjectNecessityNotEntity` — Subject-persistence does not entail entity-necessity by logic alone: the transfer fails with independent persistence/existence predicates.

**Γ's answer.** the step is DEFINITIONAL in Γ, not LOGICAL: it follows from `subject_nec_entity_nec : NecessarySubject s → NecessaryEntity (EntityOf s)`.

`Lean: Modal.lean#L103 · uses A2 · DEFINITIONAL ✔`

**Corollary C92 (Conditional C92).**

If person stability holds and intentional action confers personhood, an intentional act yields a necessary entity.

\[ PersonStabilityPrinciple → (∀ s, p, Act(s, p) → Person(s)) → (∃ s, p, Act(s, p)) → ∃ e, NecessaryEntity(e) \]

**Proof.** Assume PersonStabilityPrinciple, and ∀ s, p, Act(s, p) → Person(s), and ∃ s, p, Act(s, p). The required witness is constructed under **A2**. ∎

**Obstruction.** `CountermodelPersonNotNecessary` — `Person → NecessarySubject` as a logical law (see Appendix C.1).

**Γ's answer.** the step is DEFINITIONAL in Γ, not LOGICAL: it follows from `AxPersonStability` and `subject_nec_entity_nec`.

`Lean: Love.lean#L109 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`


### Stage VI — Grounding

Grounding turns truth into a relation to reality. The atomic truthmaker is definitional; its propositional and global reflections are the priced semantic bridge (`AxGlobalGround`), and the personal ground is the priced metaphysical bridge (`AxPersonalGround`). The withdrawn and blocked ground-theoretic steps are shown here as well.

**Axiom A1 · Ground (VOCAB).**
\[ Ground : Entity → Form → Prop \]
The truthmaker relation — an entity grounding a formula.

**Axiom A3 · Truthmaker (SEM).**
\[ ∀ w, φ, w ⊨ φ → ∃ e, ExistsAt(w, e) ∧ Ground(e, φ) \]
The truthmaker principle: truth is grounded in reality.

*Philosophical cost:* The price of a realist reading of correspondence — the bridge commits Γ to a non-vacuous grounding relation between satisfied formulas and existing entities, without deciding what kind of entities those must be. A coherence or deflationary account of truth is thereby excluded; the principle is posited, not derived.

**Theorem C15 (Every atomic truth is grounded).**

Where an atom is true, an entity exists there that grounds it.

\[ w ⊨ atom(n) → ∃ e, ExistsAt(w, e) ∧ Ground(e, atom(n)) \]

**Proof.** Follows under **A1**, **A3**. ∎

`Lean: Truthmaker.lean#L105 · uses A1, A2, A3 · SEMANTIC ⚠`

**Theorem C60 (The denial that atomic truth is grounded refutes itself under the Truthmaker bridge).**

\[ ¬(∃ w, n, w ⊨ atom(n) ∧ ¬(∃ e, ExistsAt(w, e) ∧ Ground(e, atom(n)))) \]

**Proof.** Under **a1**, **a3**, the assumption refutes itself. ∎

`Lean: Truthmaker.lean#L112 · uses A1, A2, A3 · SEMANTIC ⚠`

**Axiom A4 · AxGlobalGround (SEM).**
\[ ∀ φ, □ φ → ∃ e, ∀ w, ExistsAt(w, e) ∧ Ground(e, φ) \]
A formula true in every world is grounded by a single entity that exists in every world.

*Philosophical cost:* The declared modal price of the argument. The `∀w∃r … → ∃r∀w …` swap is not derivable from the atomic truthmaker (`groundPrinciple_atom`); it posits one necessary ground for every necessarily-true formula, which the worldwise-but-not-uniform model (`CountermodelWorldwiseTruthmaking`) shows is unforced by logic alone.

**Theorem C18 (T7 — necessary truth forces necessary reality (base.txt T7)).**

\[ □ τ → ∃ e, NecessaryEntity(e) ∧ Ground(e, τ) \]

**Proof.** Assume □ τ. The required witness is constructed under **A1**, **A4**. ∎

**Obstruction.** `CountermodelWorldwiseTruthmaking` — Worldwise truthmaking does not entail a uniform necessary ground: the `Bool` model has `∀ w ∃ e` with `ExistsAt w e := e = w` but no entity present in every world.

**Γ's answer.** Γ derives this only under AxGlobalGround; the countermodel shows that the stronger conclusion is not forced by worldwise truthmaking alone.

`Lean: Modal.lean#L74 · uses A1, A2, A4 · SEMANTIC ⚠`

**Corollary C19 (Grounding of the necessary excluded-middle reality under AxGlobalGround).**

\[ ∃ e, NecessaryEntity(e) ∧ Ground(e, (φ ∨ ¬φ)) \]

**Proof.** Follows under **A1**. ∎

**Obstruction.** `CountermodelWorldwiseTruthmaking` — worldwise truthmaking entailing a uniform necessary ground (see Appendix C.1).

**Γ's answer.** Γ derives this only under AxGlobalGround; the countermodel shows that the stronger conclusion is not forced by worldwise truthmaking alone.

`Lean: Modal.lean#L80 · uses A1, A2, A4 · SEMANTIC ⚠`

**Corollary C20 (The reductio shape of the prose).**

If every entity were contingent, no formula could be necessarily true.

\[ (∀ e, Contingent(e)) → ∀ φ, ¬□ φ \]

**Proof.** The required witness is constructed under **A1**. ∎

`Lean: Modal.lean#L86 · uses A1, A2, A4 · SEMANTIC / CONDITIONAL ⚠`

**Axiom A7 · AxPersonalGround (META).**
\[ ∀ f, IsPresentPersonalFeature(f) → ∃ e, NecessaryEntity(e) ∧ GroundProp(e, f) \]
The *necessary* reality grounds the personal features present in the rational act.

*Philosophical cost:* A metaphysical bridge. The necessary reality is asserted to carry the present rational (personal) features without this following from the performative datum: a world whose ultimate reality is impersonal is logically consistent with the premises (impersonal-ground countermodel). Γ names the bridge and pays for it explicitly.

**Axiom A8 · GroundProp (VOCAB).**
\[ GroundProp : Entity → Prop → Prop \]
The grounding relation between an entity and a proposition.

**Theorem C32 (T8 — the necessary reality is personal (PROVEN↑ under the two META bridges declared above)).**

\[ IsPresentPersonalFeature(f) → ∃ e, NecessaryEntity(e) ∧ Personal(e) \]

**Proof.** Assume IsPresentPersonalFeature(f). The required witness is constructed under **A7**, **A8**. ∎

**Obstruction.** `CountermodelImpersonalUltimateGround` — Existence of an ultimate ground does not entail that it is personal: `Personal := False` coexists with an ultimate element.

**Γ's answer.** the step rests on a substantive metaphysical bridge, not logic alone.

`Lean: GroundPerson.lean#L112 · uses A2, A5, A7, A8, A11, A12 · METAPHYSICAL ⚠`

**Axiom A9 · GroundPrincipleProp (SEM).**
\[ ∀ f, T(f) → ∃ e, GroundProp(e, f) \]
The §24a atom-grounding principle reflected at the level of propositions.

*Philosophical cost:* A separate positive existential commitment over the whole propositional level — every true proposition, not merely every atomic formula, is guaranteed a ground. Beyond the definitional atom cases this is a substantive semantic postulate, not a theorem the axioms force.

**Theorem C33 (Every present personal feature is grounded in reality).**

(the weak, necessity-free half of §24a that is provable without the META bridges, for completeness)

\[ T(f) → IsPresentPersonalFeature(f) → ∃ e, GroundProp(e, f) \]

**Proof.** Assume T(f), and IsPresentPersonalFeature(f). Follows under **A8**, **A9**. ∎

`Lean: GroundPerson.lean#L120 · uses A2, A5, A8, A9, A11, A12 · SEMANTIC ⚠`

**Corollary C34 (§24a applied to a necessary truth yields a grounder).**

(linking Prop-level and world-level principles: T7 supplies the necessary entity)

\[ □ τ → ∃ e, NecessaryEntity(e) \]

**Proof.** Assume □ τ. The required witness is constructed under **A1**. ∎

`Lean: GroundPerson.lean#L125 · uses A1, A2, A4 · SEMANTIC ⚠`

**Open problem Q7.2 (Simulated world-existence).**

The subject exists only in the `true` world.

**Status: OPEN.**

`Lean: HostileSemantics.lean#L720 · OPEN ANSWERED`


### Stage VII — Plurality and Relation

Right and wrong are interpersonal. The unit world satisfies a single act with no second subject, so plurality is not derived: it is bought with `AxTwoSubjects`. Plurality also exhibits the acting subject (C48) and reaches the distinctness of correct and incorrect judging (C30) and the judge's choice field (C55). From two distinct persons the directed-pair and interpersonal-value steps follow.

**Definition (Interpersonal relations).** Affects(s, t) := s ≠ t, Alone(s) := ∀ t, t = s, Helps(s, t) := Affects(s, t), and Harms(s, t) := False.

**Theorem C40 (There are at least two distinct persons).**

\[ ∃ s₁, s₂, Person(s₁) ∧ Person(s₂) ∧ s₁ ≠ s₂ \]

**Proof.** T12 — there is more than one person (poem P5/P7; PROVEN↑ under `AxTwoSubjects`): the reality of right-and-wrong demands plurality. A(single, act) does not entail plurality (settled by the Unit countermodel in HostileSemantics). Footprint: `{AxTwoSubjects}`. ∎

**Obstruction.** `CountermodelUnitPlurality` — A single act (one subject) cannot force a plurality of subjects: the unit model with `Person := True` satisfies act and personhood but has no second subject.

**Γ's answer.** the step rests on a substantive metaphysical bridge, not logic alone.

`Lean: Plurality.lean#L44 · uses A2, A5, A6 · METAPHYSICAL ⚠`

**Theorem C48 (The intentional subject is exhibited from plurality).**

Someone means something.

\[ ∃ s, p, Means(s, p) \]

**Proof.** cogito, RESTATED AS A(COROLLARY, OF) PLURALITY: from the demonstrated pair of persons, an intentional meaning occurs. ∎

`Lean: Plurality.lean#L57 · uses A2, A5, A6 · METAPHYSICAL ⚠`

**Proposition C30 (Correct and incorrect judging are distinct).**

Correctness is not incorrectness.

\[ (∃ s, p, A(s, p)) → ¬(∀ s, p, Correct(s, p) ↔ Incorrect(s, p)) \]

**Proof.** Assume ∃ s, p, A(s, p). Evaluating by disjunctive cases under **A2**. ∎

`Lean: Order.lean#L152 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`

**Proposition C55 (The judge is before a choice field).**

Whoever judges acts, correctly or incorrectly.

\[ (∃ s, p, A(s, p)) → ∃ s, p, q, A(s, p) ∧ (Correct(s, p) ∨ Incorrect(s, p)) ∧ ChoiceField(s, p, q) \]

**Proof.** "There is no right and wrong without (a field of) choice" (IM_STUPID.md §1–§2): the judgment act — a subject asserting a content that is correct-or-incorrect (§8) — IS set against the incompatible alternative `¬p`. Derived from an act datum + bivalence (p is right-or-wrong) + `Incompatible(p, ¬p)` (pure logic). ∎

`Lean: Order.lean#L172 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`

**Proposition C56 (A lone subject neither helps nor harms anyone else).**

\[ Alone(s) → (¬∃ t, t ≠ s ∧ Helps(s, t)) ∧ (¬∃ t, t ≠ s ∧ Harms(s, t)) \]

**Proof.** P6, whole — a lone subject helps no other AND harms no other (under **A2**). ∎

`Lean: Value.lean#L95 · uses A2 · DEFINITIONAL ✔`

**Theorem C46 (Right-and-wrong yields two distinct persons who bear on each other, conditional on the PersonsAffectPrinciple).**

\[ PersonsAffectPrinciple → (¬N_T ∧ ¬N_F) → ∃ s₁, s₂, Person(s₁) ∧ Person(s₂) ∧ s₁ ≠ s₂ ∧ (Affects(s₁, s₂) ∨ Affects(s₂, s₁)) \]

**Proof.** Assume PersonsAffectPrinciple, and ¬N_T ∧ ¬N_F. The required witness is constructed under **A2**, **A6**. ∎

`Lean: Value.lean#L139 · uses A2, A5, A6 · METAPHYSICAL / CONDITIONAL ⚠`

**Theorem C47 (T12, directed form (chain node C47)).**

The two-person pair can be oriented so that affectivity flows forward, conditional on PersonsAffectPrinciple.

\[ PersonsAffectPrinciple → ∃ s₁, s₂, Person(s₁) ∧ Person(s₂) ∧ s₁ ≠ s₂ ∧ Affects(s₁, s₂) \]

**Proof.** Assume PersonsAffectPrinciple. Evaluating by disjunctive cases under **A2**. ∎

`Lean: Plurality.lean#L124 · uses A2, A5, A6 · METAPHYSICAL ⚠`

**Theorem C74 (No person is alone).**

There is no personal lone subject under the plurality bridge.

\[ ¬∃ s, Person(s) ∧ Alone(s) \]

**Proof.** `aloneExcluded` — under `AxTwoSubjects`, a lone person is excluded: there exist distinct persons, so no single subject can encompass all subjects. Footprint: `{AxTwoSubjects}`. ∎

**Obstruction.** `CountermodelUnitPlurality` — one act forcing a plurality of subjects (see Appendix C.1).

**Γ's answer.** the step rests on a substantive metaphysical bridge, not logic alone.

`Lean: Value.lean#L124 · uses A2, A5, A6 · METAPHYSICAL ⚠`


### Stage VIII — Love

Given two distinct persons, love is defined as the mutual help that does not harm. C41–C45 derive an eternal love-relation between two persons; plurality alone still does not force love — that is the separate bridge content.

**Definition (Love).** Loves(s, t) := Helps(s, t) ∧ ¬Harms(s, t) and Lovable(t) := ∃ s, s ≠ t ∧ Person(s).

**Theorem C41 (There are two distinct persons, both lovable).**

\[ ∃ s, t, Person(s) ∧ Person(t) ∧ s ≠ t ∧ Lovable(s) ∧ Lovable(t) \]

**Proof.** T13 — there is someone able to be loved (poem P7; PROVEN from T12): each member of the two-person pair is lovable by the other. ∎

**Obstruction.** `CountermodelPluralityWithoutLove` — Plurality of distinct persons does not entail love: `Bool` with `Person := True` and `Loves := False`.

**Γ's answer.** the step rests on a substantive metaphysical bridge, not logic alone.

`Lean: Love.lean#L81 · uses A2, A5, A6 · METAPHYSICAL ⚠`

**Theorem C42 (Conditional T14).**

Under person stability and the plurality-love principle, two distinct persons stand in an eternal love relation.

\[ PersonStabilityPrinciple → PluralityLovePrinciple → ∃ s₁, s₂, Person(s₁) ∧ Person(s₂) ∧ s₁ ≠ s₂ ∧ Loves(s₁, s₂) ∧ NecessarySubject(s₁) ∧ NecessarySubject(s₂) \]

**Proof.** Assume PersonStabilityPrinciple, and PluralityLovePrinciple. The required witness is constructed under **A2**. ∎

**Obstruction.** `CountermodelPluralityWithoutLove` — plurality entailing love (see Appendix C.1).

**Γ's answer.** the step rests on a substantive metaphysical bridge, not logic alone.

`Lean: Love.lean#L119 · uses A2, A5, A6 · METAPHYSICAL ⚠`

**Theorem C43 (Two distinct persons stand in a love relation (conditional on the plurality-love principle)).**

\[ PluralityLovePrinciple → ∃ s₁, s₂, Person(s₁) ∧ Person(s₂) ∧ s₁ ≠ s₂ ∧ Loves(s₁, s₂) \]

**Proof.** Assume PluralityLovePrinciple. The required witness is constructed under **A2**. ∎

**Obstruction.** `CountermodelPluralityWithoutLove` — plurality entailing love (see Appendix C.1).

**Γ's answer.** the step rests on a substantive metaphysical bridge, not logic alone.

`Lean: Love.lean#L151 · uses A2, A5, A6 · METAPHYSICAL ⚠`

**Theorem C44 (In every world, two distinct persons stand in a love relation (conditional on stability and love)).**

\[ PersonStabilityPrinciple → PluralityLovePrinciple → ∀ w, ∃ s₁, s₂, Person(s₁) ∧ Person(s₂) ∧ s₁ ≠ s₂ ∧ Loves(s₁, s₂) ∧ ExistsAt(w, EntityOf(s₁)) ∧ ExistsAt(w, EntityOf(s₂)) \]

**Proof.** Assume PersonStabilityPrinciple, and PluralityLovePrinciple. The required witness is constructed under **A2**. ∎

**Obstruction.** `CountermodelPluralityWithoutLove` — plurality entailing love (see Appendix C.1).

**Γ's answer.** the step rests on a substantive metaphysical bridge, not logic alone.

`Lean: Love.lean#L129 · uses A2, A5, A6 · METAPHYSICAL ⚠`

**Corollary C45 (Necessarily, two distinct persons stand in a love relation (conditional on stability and love)).**

\[ PersonStabilityPrinciple → PluralityLovePrinciple → □(∃ s₁, s₂, Person(s₁) ∧ Person(s₂) ∧ s₁ ≠ s₂ ∧ Loves(s₁, s₂)) \]

**Proof.** Assume PersonStabilityPrinciple, and PluralityLovePrinciple. The required witness is constructed under **A2**. ∎

**Obstruction.** `CountermodelPluralityWithoutLove` — plurality entailing love (see Appendix C.1).

**Γ's answer.** the step rests on a substantive metaphysical bridge, not logic alone.

`Lean: Love.lean#L141 · uses A2, A5, A6 · METAPHYSICAL ⚠`

**Proposition C85 (Benevolence principle).**

In the foundational order, what helps does not harm.

\[ ∀ s, t, Helps(s, t) → ¬Harms(s, t) \]

**Proof.** Evaluating by disjunctive cases under **A2**. ∎

`Lean: Value.lean#L74 · uses A2 · DEFINITIONAL ✔`

**Proposition C86 (Love implies positive help).**

The lover benefits the beloved.

\[ ∀ s, t, Loves(s, t) → Helps(s, t) \]

**Proof.** Loving unfolds to benevolence: loving entails helping (under **A2**). ∎

`Lean: Love.lean#L47 · uses A2 · DEFINITIONAL ✔`


### Stage IX — The Remaining Metaphysical Frontier

The remaining frontier is explicit: teleology, the moral good, the Trinity, incarnation and creation are deferred or faith data; the initiation-theoretic and ground-chain constructions are withdrawn under hostile semantics. Nothing here is presented as derived.

**Open problem F2 (Deontic teleology is deferred).**

How norms point at goals is not yet derived.

**Status: OPEN.**

`Lean: n/a · OPEN ➖`

**Open problem F3 (Moral good from logical normativity is deferred).**

Not yet derived.

**Status: OPEN.**

`Lean: n/a · OPEN ➖`

**Open problem F6 (The Trinity is deferred).**

No argument exists yet.

**Status: OPEN.**

`Lean: n/a · OPEN ➖`

**Open problem F8 (The Trinity is not attempted).**

**Status: OPEN.**

`Lean: n/a · OPEN ➖`

**Open problem F9 (Incarnation and creation are faith data from the poem, deferred).**

**Status: OPEN.**

`Lean: n/a · OPEN ➖`


## 4. Where the deduction stops

The frontier is the set of claims that are not currently derived. An **OPEN** claim has no kernel node (blocked, deferred, answered, or a missing lemma) and is listed below. A **COUNTERMODEL** claim is a proposed inference that a hostile model refutes: the step is *withdrawn*, and what survives is recorded in Appendix C.2. The premier open frontiers are deontic teleology (F2) and moral good (F3).

- **F2** — Deontic teleology is deferred
- **F3** — Moral good from logical normativity is deferred
- **F6** — The Trinity is deferred
- **Q7.2** — Simulated world-existence
- **F8** — The Trinity is not attempted
- **F9** — Incarnation and creation are faith data from the poem, deferred

**§28 open bridges.** The prose corpus lists the still-missing named lemmas: #7 `NecessaryEntity e → ∃ τ, Ground e τ`; #8 the target opposite of #7; #9 `Ground(e, personal) → Personal(e)`; #10 its target. Each appears above in the open inventory; none is silently assumed.

---

## Appendix A — Formal notation

Each step is the real Lean declaration, rendered in logic symbols by the `humanise` pipeline; the English meaning lives in code (docstrings / String constants).

| Symbol | Lean | Meaning |
|---|---|---|
| `\[ … \]` · `\( … \)` | (display/inline math) | standard mathematical display convention for formal statements |
| `¬` · `∧` · `∨` · `→` | `Not` · `And` · `Or` · `Imp` | negation, conjunction, disjunction, implication |
| `φ ∨ ¬φ` | `Form.or φ (Form.not φ)` | object-language formula (not `Prop`) |
| `τ` · `φ` | `Form` | formula/content of the object language |
| `∃ s p q, …` | `∃ (s : Subject), …` | quantifier binder types stripped by `mathify` for concise presentation |
| `□ τ` | `NecessarilyTrue τ` | true in every world (`∀ w, TrueAt w τ`) |
| `¬◇ τ` | `NecessarilyFalse τ` | false in every world (impossible: `∀ w, FalseAt w τ`) |
| `□ p` | `Necessity p` | box at the `Prop` level (degenerate identity alias, `□p := p`) |
| `□ₚ P` · `∀ w, P(w)` | `NecessityPH P` | world-level box — the real modality |
| `◇ p` | `Dia p` | possibility: `¬□(¬p)` |
| `w ⊨ τ` | `TrueAt w τ` / `Satisfies w τ` | τ is true in world w |
| `w ⊭ τ` | `FalseAt w τ` | τ is false in world w |
| `atom n` | `Form.atom n` | atomic proposition n of the object language |
| `T p` | `T p` (`def T p := p`) | "p is true" — truth is identity (E0) |
| `IsFalse p` | `IsFalse p` | "p is false" (`:= ¬ T p`) |
| `N_T` ≡ `N_F` | `N_T` · `N_F` | absolutes: "nothing is true" · "everything is true" |
| `A s p` · `Means s p` | `A s p` (`:= Means s p ∧ ∃ w w', Initiates s w w' p`) · `Means s p` | an act is a meaningful initiation: its constitutive content is intentional meaning, and its evental character is initiation |
| `Agent s` · `SubjectExists s` | `Agent s` (`:= True`) · `SubjectExists s` (`:= ∃ p, Act s p`) | nominal agent predicate; subject-actuality is constitutive via `Act` |
| `Subject` · `Person s` | `Subject` · `Person s` | sort of subjects · "s is a person" |
| `Chooses s p q` | `Chooses s p q` | subject s chooses between alternatives p and q |
| `Ground e τ` · `ExistsAt w e` | `Ground e τ` · `ExistsAt w e` | entity e grounds τ · e exists in world w |
| `NecessaryEntity e` · `NecessarySubject s` | `NecessaryEntity e` · `NecessarySubject s` | e exists in every world · s persists in every world |
| `Correct s p` · `Incorrect s p` · `Fallible s p` | `Correct` · `Incorrect` · `Fallible` | correct · incorrect · fallible judgment of subject s about p |
| `Incompatible p q` · `Lovable s` · `Loves s₁ s₂` | `Incompatible` · `Lovable` · `Loves` | incompatible alternatives · s is lovable · s₁'s love of s₂ |

---

## Appendix B — Axiom ledger (17 declarations)

| Axiom | A# | Tag | Meaning (EN) | Depended on by |
|---|---|---|---|---|
| `Ground` | A1 | `VOCAB` | The truthmaker relation — an entity grounding a formula. | C15, C18, C19, C20, C34, C60 |
| `Subject` | A2 | `VOCAB` | Vocabulary: the pure sort of subjects — that which performs acts of reasoning. | C100, C101, C15, C18, C19, C20, C21, C23, C24, C25, C28, C29, C30, C32, C33, C34, C39, C40, C41, C42, C43, C44, C45, C46, C47, C48, C49, C51, C52, C53, C54, C55, C56, C57, C58, C60, C61, C62, C68, C74, C77, C83, C84, C85, C86, C91, C92, C94, C97, C98, C99, F1b, FAITH-2 |
| `Truthmaker` | A3 | `SEM` | The truthmaker principle: truth is grounded in reality. | C15, C60 |
| `AxGlobalGround` | A4 | `SEM` | AxGlobalGround (SEM): a formula true in every world is grounded by a single entity that exists in every world. | C18, C19, C20, C34 |
| `Means` | A5 | `VOCAB` | Vocabulary: the meaning-act relation — a subject means a proposition. | C100, C101, C21, C23, C24, C25, C28, C29, C30, C32, C33, C39, C40, C41, C42, C43, C44, C45, C46, C47, C48, C49, C51, C52, C53, C54, C55, C57, C61, C62, C68, C74, C77, C83, C84, C92, C94, C97, C98, C99, F1b, FAITH-2 |
| `AxTwoSubjects` | A6 | `META` | AxTwoSubjects (META; poem P5/P7, failure traces in DESIGN.md D14 and HostileSemantics): the *reality* of right-and-wrong demands that there be at least two distinct persons. Narrower than the former single bridge `AxValueInterpersonal` (plurality only… | C28, C29, C40, C41, C42, C43, C44, C45, C46, C47, C48, C54, C61, C74, FAITH-2 |
| `AxPersonalGround` | A7 | `META` | AxPersonalGround (META): the *necessary* reality grounds the personal features present in the rational act. | C32 |
| `GroundProp` | A8 | `VOCAB` | The grounding relation between an entity and a proposition. | C32, C33 |
| `GroundPrincipleProp` | A9 | `SEM` | The §24a atom-grounding principle reflected at the level of propositions. | C33 |
| `act` | A10 | `VOCAB` | Vocabulary: weak act / performed event — something is performed, uttered, asserted, or denied. | C58 |
| `State` | A11 | `VOCAB` | Vocabulary: abstract state space for initiation of movement. | C100, C101, C21, C23, C24, C25, C30, C32, C33, C39, C52, C53, C55, C57, C62, C68, C77, C83, C84, C92, C94, C97, C98, C99, F1b |
| `Initiates` | A12 | `VOCAB` | Vocabulary: the initiation relation — a subject initiates a transition between states positing content. | C100, C101, C21, C23, C24, C25, C30, C32, C33, C39, C52, C53, C55, C57, C62, C68, C77, C83, C84, C92, C94, C97, C98, C99, F1b |
| `AxActPolarity` | A13 | `SEM` | Act polarity: initiating an intentional act constitutively endows the agent with the representation of its contradictory negation. | — |
| `AxIntentionalChoice` | A14 | `SEM` | Genuine choice is constitutive of intentional action: an intentional act is an initiation performed through the subject's apprehension of an incompatible alternative. | F1b |
| `DependsOn` | A15 | `VOCAB` | Vocabulary: primitive ontological dependence relation between a domain item and a subject. | — |
| `universal_thesis_claims_objectivity` | A16 | `SEM` | Semantic bridge: the universal thesis of subjectivity, as an asserted universal truth about all reality, does not depend on any particular intentional subject. | — |
| `transcendental_reflection_intentional` | A17 | `SEM` | Semantic transcendental bridge: the transcendental reflection on universal objectivity depends on an IntentionalSubject who entertains it. | — |

### Kernel declarations

- `Logos.Agency.Initiates`
- `Logos.Agency.Means`
- `Logos.Agency.State`
- `Logos.Agency.Subject`
- `Logos.Agency.act`
- `Logos.Choice.AxActPolarity`
- `Logos.Choice.AxIntentionalChoice`
- `Logos.GroundPerson.AxPersonalGround`
- `Logos.GroundPerson.GroundPrincipleProp`
- `Logos.GroundPerson.GroundProp`
- `Logos.Modal.AxGlobalGround`
- `Logos.Retorsion.DependsOn`
- `Logos.Retorsion.transcendental_reflection_intentional`
- `Logos.Retorsion.universal_thesis_claims_objectivity`
- `Logos.Truthmaker.Ground`
- `Logos.Truthmaker.Truthmaker`
- `Logos.Value.AxTwoSubjects`

### Withdrawn / demoted axioms (history only)

Kept so a stale GAPMAP footprint referencing them is flagged; never used for status: `AxPersonStability`, `ExistsAt`.

---

## Appendix C — Obstructions & retired alternatives

A hostile model is a self-contained Lean structure in which the premises hold and the disputed inference fails. C.1 is the model reference; C.2 lists the proposed steps those models retire; C.3 lists the dissolved aliases. Each step's inline **Obstruction** line points back here.

### C.1 Countermodel reference

- **`CountermodelWeakActWithoutMeaning`** — The mechanical event: *attacks* a performed event entailing intentional meaning (`act → Act`). Refutes: A performed event (utterance, keystroke, physical emission) does not entail an intentional meaning-act: `act s p` can occur without `Means s p`. **What survives:** The weak retorsion proves directly only that an act-event occurs; the step from event to meaning requires the explicit intentionality bridge `weak_act_implies_strong_act`. · `Logos.HostileSemantics.CountermodelWeakActWithoutMeaning` · [HostileSemantics.lean#L390](formal/Logos/HostileSemantics.lean#L390)
- **`CountermodelActWithoutSubject`** — The void act (Lichtenberg): *attacks* an act occurring with no actualizing subject. Refutes: Without a constitutive rule, an act can occur in the void with no actualizing subject (Lichtenberg's objection). **What survives:** In Γ the Act relation is constitutive — `Act s p → Subject s` by definition — so the void-act is no countermodel to the formal implication. · `Logos.CountermodelActWithoutSubject` · [HostileSemantics.lean#L346](formal/Logos/HostileSemantics.lean#L346)
- **`CountermodelSubjectWithoutPerson`** — The unpredicated subject: *attacks* `Subject → Person` as a logical law. Refutes: A subject of an act need not be a person: if `Person` is an uninterpreted substantive predicate, `Subject → Person` fails as a logical law. **What survives:** Under §12 the identity `Person s ↔ ∃ p, Act s p` makes personhood definitional, so the implication holds in Γ by analysis, not by logic. · `Logos.HostileSemantics.CountermodelSubjectWithoutPerson` · [HostileSemantics.lean#L487](formal/Logos/HostileSemantics.lean#L487)
- **`CountermodelNoPerson`** — The personless act: *attacks* the bare act datum forcing `Person`. Refutes: The bare act-datum `∃ s p, A s p` does not force any `Person`. **What survives:** Personhood is introduced by the definition of Act (esse est agere), not by the raw datum. · `Logos.HostileSemantics.CountermodelNoPerson` · [HostileSemantics.lean#L513](formal/Logos/HostileSemantics.lean#L513)
- **`CountermodelNoFreeWill`** — The determined act: *attacks* `Act → Chooses` / `Act → FreeWill`. Refutes: Mere occurrence of an act does not entail genuine choice: an uninterpreted determined act with `Chooses := False` satisfies the datum while `Chooses` and `FreeWill` stay empty. **What survives:** `Chooses → FreeWill` holds in Γ by definition (`FreeWill s := ∃ p q, Chooses s p q`); the countermodel attacks the existence of genuine choice, not the implication. · `Logos.HostileSemantics.CountermodelNoFreeWill` · [HostileSemantics.lean#L532](formal/Logos/HostileSemantics.lean#L532)
- **`CountermodelUnitPlurality`** — The unit world: *attacks* one act forcing a plurality of subjects. Refutes: A single act (one subject) cannot force a plurality of subjects: the unit model with `Person := True` satisfies act and personhood but has no second subject. **What survives:** Plurality rests on `AxTwoSubjects` (the reality of right-and-wrong demands two subjects), not on the mere act. · `Logos.HostileSemantics.UnitPluralityCountermodel` · [HostileSemantics.lean#L549](formal/Logos/HostileSemantics.lean#L549)
- **`CountermodelContentWithoutPerson`** — Content without a person: *attacks* content existence entailing personhood. Refutes: Propositional existence plus meaning does not entail personhood: `S := Prop`, `Means s p := s = p`, `Person := False`. **What survives:** Content-existence is a distinct step from personhood; the definitional link `Person s ↔ ∃ p, Act s p` is what Γ uses, not a logical law. · `Logos.HostileSemantics.PropositionalPersonhood.CountermodelContentWithoutPerson` · [HostileSemantics.lean#L567](formal/Logos/HostileSemantics.lean#L567)
- **`CountermodelWorldwiseTruthmaking`** — Worldwise but not uniform: *attacks* worldwise truthmaking entailing a uniform necessary ground. Refutes: Worldwise truthmaking does not entail a uniform necessary ground: the `Bool` model has `∀ w ∃ e` with `ExistsAt w e := e = w` but no entity present in every world. **What survives:** For atoms the swap is a theorem without axioms; the compound/global instance is exactly what `AxGlobalGround` supplies. · `Logos.HostileSemantics.CountermodelWorldwiseTruthmaking` · [HostileSemantics.lean#L592](formal/Logos/HostileSemantics.lean#L592)
- **`CountermodelSubjectNecessityNotEntity`** — Persistence without entity: *attacks* subject-persistence entailing entity-necessity by logic alone. Refutes: Subject-persistence does not entail entity-necessity by logic alone: the transfer fails with independent persistence/existence predicates. **What survives:** In Γ `EntityOf` is the Truthmaker embedding and `ExistsAt` is one shared relation, so the lift (C91) is definitional, not a logical law. · `Logos.HostileSemantics.CountermodelSubjectNecessityNotEntityNecessity` · [HostileSemantics.lean#L631](formal/Logos/HostileSemantics.lean#L631)
- **`CountermodelPersonNotNecessary`** — The contingent person: *attacks* `Person → NecessarySubject` as a logical law. Refutes: A person need not be a necessary subject: `Person → NecessarySubject` fails as a logical law (subject exists only in the `true` world). **What survives:** Person-persistence is definitional (esse est agere, `AxPersonStability`), and `Love.no_contingent_person` shows the concrete refutation cannot exist in Γ. · `Logos.HostileSemantics.CountermodelPersonNotNecessary` · [HostileSemantics.lean#L714](formal/Logos/HostileSemantics.lean#L714)
- **`CountermodelVeridicalMeaning`** — Veridical meaning (one and two persons): *attacks* the act datum forcing genuine choice. Refutes: The act-datum does not force `genuineChoice_exists` even under the Logos definition of `Chooses`: veridical meaning makes co-meaning an incompatible pair impossible while the whole agency/choice/order fragment holds. **What survives:** The frontier is not the implication `Chooses → FreeWill` but whether any subject co-means an incompatible horn — the single irreducible resource is `rejectedHornCoMeant` (BLOCKED). · `Logos.HostileSemantics.CountermodelVeridicalMeaning` · [HostileSemantics.lean#L794](formal/Logos/HostileSemantics.lean#L794)
- **`CountermodelInfiniteGroundChain`** — The infinite descending chain: *attacks* grounding forcing an ultimate element. Refutes: A strict partial order need not have an ultimate element: descending infinite chains in `Int` have none. **What survives:** Γ never claimed order-theoretic well-foundedness; the missing assumption (if adopted) would be a further axiom, not a hidden theorem. · `Logos.HostileSemantics.CountermodelInfiniteGroundChain` · [HostileSemantics.lean#L2218](formal/Logos/HostileSemantics.lean#L2218)
- **`CountermodelImpersonalUltimateGround`** — The impersonal ultimate: *attacks* an ultimate ground entailing a personal one. Refutes: Existence of an ultimate ground does not entail that it is personal: `Personal := False` coexists with an ultimate element. **What survives:** Personal grounding is the content of `AxPersonalGround` (T8), a META bridge whose cost is explicit, not a consequence of grounding alone. · `Logos.HostileSemantics.CountermodelImpersonalUltimateGround` · [HostileSemantics.lean#L2363](formal/Logos/HostileSemantics.lean#L2363)
- **`CountermodelPluralityWithoutLove`** — Plurality without love: *attacks* plurality entailing love. Refutes: Plurality of distinct persons does not entail love: `Bool` with `Person := True` and `Loves := False`. **What survives:** Love follows in Γ from the definitions plus `AxTwoSubjects` — substantive relational bridges, not a logical consequence of plurality. · `Logos.HostileSemantics.CountermodelPluralityWithoutLove` · [HostileSemantics.lean#L2392](formal/Logos/HostileSemantics.lean#L2392)

### C.2 Retired and rejected alternatives

- **C78** — Contingent ground is retired · `CountermodelActWithoutSubject` · what survives: In Γ the Act relation is constitutive — `Act s p → Subject s` by definition — so the void-act is no countermodel to the formal implication.
- **C79** — Ultimate ground existence is blocked · `CountermodelInfiniteGroundChain` · what survives: Γ never claimed order-theoretic well-foundedness; the missing assumption (if adopted) would be a further axiom, not a hidden theorem.
- **C87** — Origin necessity is retired · `CountermodelActWithoutSubject` · what survives: In Γ the Act relation is constitutive — `Act s p → Subject s` by definition — so the void-act is no countermodel to the formal implication.
- **C88** — Transcendental quantifier swap is retired · `CountermodelWorldwiseTruthmaking` · what survives: For atoms the swap is a theorem without axioms; the compound/global instance is exactly what `AxGlobalGround` supplies.
- **C89** — Ultimate ground by initiation is blocked · `CountermodelInfiniteGroundChain` · what survives: Γ never claimed order-theoretic well-foundedness; the missing assumption (if adopted) would be a further axiom, not a hidden theorem.
- **C90** — Personal ultimate ground is blocked · `CountermodelImpersonalUltimateGround` · what survives: Personal grounding is the content of `AxPersonalGround` (T8), a META bridge whose cost is explicit, not a consequence of grounding alone.
- **C69** — Free will of origin is retired · `CountermodelNoFreeWill`, `CountermodelVeridicalMeaning` · what survives: `Chooses → FreeWill` holds in Γ by definition (`FreeWill s := ∃ p q, Chooses s p q`); the countermodel attacks the existence of genuine choice, not the implication. The frontier is not the implication `Chooses → FreeWill` but whether any subject co-means an incompatible horn — the single irreducible resource is `rejectedHornCoMeant` (BLOCKED).
- **C70** — Posited content non-freedom is retired · `CountermodelNoFreeWill`, `CountermodelVeridicalMeaning` · what survives: `Chooses → FreeWill` holds in Γ by definition (`FreeWill s := ∃ p q, Chooses s p q`); the countermodel attacks the existence of genuine choice, not the implication. The frontier is not the implication `Chooses → FreeWill` but whether any subject co-means an incompatible horn — the single irreducible resource is `rejectedHornCoMeant` (BLOCKED).
- **C71** — Origin freedom denial self-refuting is retired · `CountermodelNoFreeWill`, `CountermodelVeridicalMeaning` · what survives: `Chooses → FreeWill` holds in Γ by definition (`FreeWill s := ∃ p q, Chooses s p q`); the countermodel attacks the existence of genuine choice, not the implication. The frontier is not the implication `Chooses → FreeWill` but whether any subject co-means an incompatible horn — the single irreducible resource is `rejectedHornCoMeant` (BLOCKED).
- **C72** — Judge is free is retired · `CountermodelNoFreeWill`, `CountermodelVeridicalMeaning` · what survives: `Chooses → FreeWill` holds in Γ by definition (`FreeWill s := ∃ p q, Chooses s p q`); the countermodel attacks the existence of genuine choice, not the implication. The frontier is not the implication `Chooses → FreeWill` but whether any subject co-means an incompatible horn — the single irreducible resource is `rejectedHornCoMeant` (BLOCKED).
- **C73** — Plurality without bridges is blocked · `CountermodelUnitPlurality` · what survives: Plurality rests on `AxTwoSubjects` (the reality of right-and-wrong demands two subjects), not on the mere act.
- **C75** — Propositional personhood is blocked · `CountermodelContentWithoutPerson` · what survives: Content-existence is a distinct step from personhood; the definitional link `Person s ↔ ∃ p, Act s p` is what Γ uses, not a logical law.
- **C76** — Canonical rigid love is retired · `CountermodelPluralityWithoutLove` · what survives: Love follows in Γ from the definitions plus `AxTwoSubjects` — substantive relational bridges, not a logical consequence of plurality.
- **C64** — Movement not transfer is retired · `CountermodelActWithoutSubject` · what survives: In Γ the Act relation is constitutive — `Act s p → Subject s` by definition — so the void-act is no countermodel to the formal implication.
- **C65** — Person iff originates is retired · `CountermodelActWithoutSubject` · what survives: In Γ the Act relation is constitutive — `Act s p → Subject s` by definition — so the void-act is no countermodel to the formal implication.
- **C66** — Cogito as initiation is retired · `CountermodelActWithoutSubject` · what survives: In Γ the Act relation is constitutive — `Act s p → Subject s` by definition — so the void-act is no countermodel to the formal implication.
- **C67** — Denial of initiation self-refuting is retired · `CountermodelActWithoutSubject` · what survives: In Γ the Act relation is constitutive — `Act s p → Subject s` by definition — so the void-act is no countermodel to the formal implication.
- **C80** — Posited content deterministic transfer is retired · `CountermodelActWithoutSubject` · what survives: In Γ the Act relation is constitutive — `Act s p → Subject s` by definition — so the void-act is no countermodel to the formal implication.
- **C81** — Origin branching is retired · `CountermodelActWithoutSubject` · what survives: In Γ the Act relation is constitutive — `Act s p → Subject s` by definition — so the void-act is no countermodel to the formal implication.
- **C82** — Origin initiating person is retired · `CountermodelActWithoutSubject` · what survives: In Γ the Act relation is constitutive — `Act s p → Subject s` by definition — so the void-act is no countermodel to the formal implication.

### C.3 Dissolved aliases

- **F1a** → **C51** (shares `Logos.Choice.person_hasChoiceField`); see that block.
- **F4** → **C41** (shares `Logos.Love.T13_someoneLovable`); see that block.
- **F5** → **C42** (shares `Logos.Love.T14_eternalRelation_conditional`); see that block.
- **F7** → **F1b** (shares `Logos.Choice.freeWill_exists`); see that block.
- **FAITH-1** → **C38** (shares `Logos.Necessity.necDistinction`); see that block.
- **FAITH-2** → **C42** (shares `Logos.Love.T14_eternalRelation_conditional`); see that block.

---

## Appendix D — Lean / kernel audit

### D.1 Kernel-derived status (badges vs. philosophical statuses)

| Machine badge | GAPMAP status | Philosophical status |
|---|---|---|
| `✔` | PROVEN | LOGICAL or DEFINITIONAL |
| `⚠` | PROVEN↑ | SEMANTIC or METAPHYSICAL |
| `◆` | AXIOM | tag of the axiom (`VOCAB`/`SEM`/`META`) |
| `✖` | BLOCKED | OPEN or COUNTERMODEL |
| `➖` | DEFERRED | OPEN |
| `→` | dissolved | cross-reference |
| `CL` | — | classical meta-logic `{propext, Classical.choice, Quot.sound}` |

### D.2 Reconciliation report (kernel ↔ GAPMAP)

- GAPMAP claims with a kernel declaration located (FOUND): **87** / 114
- Steps with an **English meaning in code**: **114** / 114
- **Claims whose referenced theorem is missing (MISSING) (1):**
  - `F5` ref `Love.T14_eternalRelation` — §28 EternalRelation
- **Withdrawn / blocked claims (outside the active deduction) (26):**
  - `C78` (`BLOCKED`) ref `Modal.contingent_ground` — T7
  - `C79` (`BLOCKED`) ref `Modal.ultimateGround_exists` — T7
  - `C87` (`BLOCKED`) ref `Modal.origin_is_necessary` — T7
  - `C88` (`BLOCKED`) ref `Modal.transcendental_quantifier_swap` — T7
  - `C89` (`BLOCKED`) ref `Modal.ultimateGroundInit_exists` — T7
  - `C90` (`BLOCKED`) ref `GroundPerson.personal_ultimate_ground_exists` — T8
  - `F2` (`DEFERRED`) ref `—` — §21 teleology (`Ought → Goal`)
  - `F3` (`DEFERRED`) ref `—` — §28 Good (`§20 → bem`)
  - `F6` (`DEFERRED`) ref `—` — §28 Trinity
  - `C69` (`BLOCKED`) ref `—` — §15/F1b
  - `C70` (`BLOCKED`) ref `—` — §15/F1b
  - `C71` (`BLOCKED`) ref `—` — §15/F1b
  - `C72` (`BLOCKED`) ref `—` — §15/F1b
  - `C73` (`BLOCKED`) ref `Person.twoPersonsFromSubject` — P5/P7
  - `C75` (`BLOCKED`) ref `Person.everyContentIsAPerson` — P7
  - `C76` (`BLOCKED`) ref `Love.T14_canonicalRigid` — P8
  - `C64` (`BLOCKED`) ref `Initiation.originates_not_transfer` — §1
  - `C65` (`BLOCKED`) ref `Initiation.person_iff_originates` — §1/T5
  - `C66` (`BLOCKED`) ref `Initiation.Cogito_Init` — §1 fnd
  - `C67` (`BLOCKED`) ref `Initiation.noInitiation_selfRefutes` — §1 fnd
  - `C80` (`BLOCKED`) ref `Initiation.posited_not_branch` — §1
  - `C81` (`BLOCKED`) ref `Initiation.origin_branches` — §1
  - `C82` (`BLOCKED`) ref `Initiation.origin_is_initiating_person` — §1/§12
  - `F7` (`→`) ref `—` — §15 the bipolar half of freedom
  - `F8` (`DEFERRED`) ref `—` — Trinity
  - `F9` (`DEFERRED`) ref `—` — Incarnation / creation
- **Kernel theorems supporting the architecture (244 intentional unmapped helper/infrastructure theorems):**
  - *Hostile countermodel separations (10):* act_exists_of_act, not_entails_content_person, not_entails_decoupled_freewill, not_entails_person, not_entails_plurality, not_entails_substantive_autonomy, not_entails_substantive_intentionality, not_entails_substantive_person, not_entails_substantive_rationality, subject_exists_of_act
  - *Modal calculus S4/K4 machinery (12):* Modal.necessary_entity_exists_of_necessary_subject, Modal.subject_nec_entity_nec_iff, Necessity.dia_def, Necessity.nec4, Necessity.nec4PH, Necessity.necDistinction_content, Necessity.necK, Necessity.necKPH, Necessity.necMP, Necessity.necT, Necessity.necTPH, Necessity.nec_apply
  - *Semantic satisfaction & object-language lemmas (25):* Core.atomicWitnessFalsehood, Core.someTruthAndSomeFalsehood, Core.tschema, HostileSemantics.act_exists_of_act, HostileSemantics.not_entails_content_person, HostileSemantics.not_entails_decoupled_freewill, HostileSemantics.not_entails_person, HostileSemantics.not_entails_plurality, HostileSemantics.not_entails_substantive_autonomy, HostileSemantics.not_entails_substantive_intentionality, HostileSemantics.not_entails_substantive_person, HostileSemantics.not_entails_substantive_rationality, HostileSemantics.subject_exists_of_act, Semantics.atom_not_necessarily_false, Semantics.atom_not_necessarily_true, Semantics.sat_and, Semantics.sat_imp, Semantics.sat_not, Semantics.sat_or, Semantics.strongTruth_and_contingent_content, Semantics.strongTruth_is_not_atomic, Truthmaker.sat_ground_and, Truthmaker.sat_ground_imp, Truthmaker.sat_ground_not, Truthmaker.sat_ground_or
  - *Intermediate agency, order, and relation steps (207):* Agency.Cogito_of_bridge, Agency.T1_subjectExists_of_act, Agency.act_datum_implies_initiates, Agency.act_datum_implies_means, Agency.act_decomposition, Agency.act_exists_of_assert, Agency.act_implies_agent, Agency.act_implies_content, Agency.act_implies_initiates, Agency.act_implies_means, Agency.act_implies_rational, Agency.act_of_asserting_no_act, Agency.act_requires_subject, Agency.an_actual_subject_exists_of_act, Agency.assertion_is_act, Agency.assertion_is_weak_act, Agency.noAct_conditional_selfRefutes, Agency.noCogito_selfRefutes, Agency.noSubjectSort_selfRefutes, Agency.noSubject_performative_selfRefutes, Agency.noSubject_selfRefutes, Agency.strong_act_of_weak_act, Agency.subject_exists_of_act, Agency.subject_exists_of_assert, Agency.weak_Cogito, Agency.weak_act_exists_of_assert, Choice.T11_choiceField_from_plurality, Choice.act_decomposition, Choice.act_implies_authors, Choice.act_implies_causalTransition, Choice.act_implies_choiceField, Choice.act_missing_horn_iff_chooses, Choice.act_missing_horn_implies_chooses, Choice.act_polarity_implies_conditional, Choice.act_polarity_implies_contrastive, Choice.act_polarity_implies_existential, Choice.act_polarity_implies_existential_choice, Choice.act_polarity_implies_intentional_choice, Choice.act_produces_choice_iff_missing_horn, Choice.alternativeSensitivity_implies_genuineChoice, Choice.asserting_noChoiceField_is_choiceField, Choice.assertion_consistency, Choice.asserts_implies_choice, Choice.asserts_implies_freeAgency, Choice.asserts_implies_selects, Choice.asserts_selects, Choice.asserts_selects_all_incompatible, Choice.bilateral_implies_act_polarity, Choice.canChoose_unfold, Choice.choiceField_exists_from_plurality, Choice.chooses_implies_freeSubject, Choice.chooses_implies_freeWill, Choice.contemplatesWithoutSettling_implies_freeWill, Choice.contemplates_iff_chooses, Choice.contrastive_agency_implies_existential, Choice.contrastive_implies_intentional_choice, Choice.counterfactual_act_implies_genuineChoice, Choice.deliberateAuthorship_implies_chooses, Choice.deliberateAuthorship_implies_deliberateChoice, Choice.deliberateChoice_exists_of_assertion_and_negation_meaning, Choice.deliberateChoice_iff_selects_and_rejects, Choice.deliberateChoice_negation_decomposition, Choice.deliberateChoice_negation_iff, Choice.deliberateResource_of_act_polarity, Choice.deliberateResource_of_bilateral_intentionality, Choice.deliberate_resource_implies_genuine_choice, Choice.deliberates_iff_chooses, Choice.descriptive_act_implies_genuineChoice, Choice.existential_choice_iff_f1b, Choice.f1b_iff_missing_cognitive_horn, Choice.freeSubject_exists, Choice.freeSubject_exists_of_act, Choice.freeSubject_exists_of_contrastive_act, Choice.freeSubject_iff_freeWill, Choice.freeSubject_implies_intentional, Choice.freeSubject_implies_intentionalSubject, Choice.freeWillExists_of_chooses, Choice.freeWillExists_of_genuineChoice, Choice.freeWill_exists_of_act, Choice.freeWill_exists_of_act_polarity, Choice.freeWill_exists_of_contrastive_act, Choice.freeWill_exists_of_doubt_bridge, Choice.freeWill_exists_of_doubt_datum, Choice.freeWill_exists_of_existential_act_polarity, Choice.freeWill_exists_of_existential_choice, Choice.freeWill_iff_means_missing_horn, Choice.freeWill_of_doubt, Choice.genuineChoice_exists_of_act, Choice.genuineChoice_exists_of_act_constitutive, Choice.genuineChoice_exists_of_act_polarity, Choice.genuineChoice_exists_of_bilateral_intentionality, Choice.genuineChoice_exists_of_contrastive_act, Choice.genuineChoice_exists_of_doubt_bridge, Choice.genuineChoice_exists_of_doubt_datum, Choice.genuineChoice_exists_of_existential_act_polarity, Choice.genuineChoice_of_doubt, Choice.genuineChoice_requires_error_possibility, Choice.intentional_choice_implies_contrastive, Choice.intentional_choice_implies_existential_choice, Choice.intentional_hasChoiceField, Choice.judge_asserting_rightWrong_has_choiceField, Choice.meaning_I_needs_subject, Choice.means_missing_horn_iff_chooses, Choice.noChoiceField_contradicts_field, Choice.noSubject_contradicts_subject, Choice.no_one_asserts_incompatible_pair, Choice.no_selection_no_assertion, Choice.reasonResponsive_act_implies_genuineChoice, Choice.rejectedHornCoMeant_implies_genuineChoice, Choice.relationalIntentionality_implies_genuineChoice, Choice.selection_exists, Choice.selfAssertedChoice_factive_implies_chooses, Choice.selfAssertedDeliberateChoice_factive_implies_chooses, Choice.selfAssertedParadox_is_false, Choice.selfAssertedParadox_not_assertable, Choice.selfDenialOfExecutiveChoice_selfRefutes, Choice.selfDenial_implies_genuineChoice_of_a14, Choice.selfDenial_implies_genuineChoice_of_polarity, Choice.teleological_act_implies_genuineChoice, ConditionalTheology.agency_closure_act_to_chooses, ConditionalTheology.agency_closure_act_to_freeSubject, ConditionalTheology.agency_closure_act_to_freewill, ConditionalTheology.agency_closure_act_to_intentionalSubject, ConditionalTheology.freewill_not_entails_necessity, ConditionalTheology.freewill_not_entails_normativity, ConditionalTheology.freewill_not_entails_persistence, ConditionalTheology.freewill_not_entails_rationality, ConditionalTheology.freewill_not_entails_reflexive_subjectivity, ConditionalTheology.freewill_not_entails_relationality, ConditionalTheology.freewill_not_entails_teleology, ConditionalTheology.freewill_not_entails_value, GroundPerson.AxGroundBearing, Love.love_affects, Love.love_not_harms, Love.loves_of_helps, Order.act_iff_correct_or_incorrect, Order.correct_implies_selection, Order.correct_implies_selection_all_incompatible, Order.fallible_false, Order.judgment_implies_act, Order.judgment_implies_cogito, Order.judgment_of_no_act_is_incorrect, Order.rightDistinctWrong_implies_meaning, Order.rightWrongDistinction_implies_meaning, Person.act_implies_intentional, Person.act_implies_intentionalSubject, Person.intentionalSubject_exists_of_act, Person.intentionalSubject_exists_of_assert, Person.intentional_exists_of_act, Person.intentional_exists_of_assert, Person.intentional_implies_subjectExists_of_bridge, Person.person_is_intentional, Person.subjectExists_implies_intentional, Person.subjectExists_implies_intentionalSubject, Plurality.T1_of_assert, Plurality.T1_subjectExists_from_plurality, Plurality.T4_agentExists_from_plurality, Plurality.T4_of_assert, Plurality.T5_intentional_of_assert, Plurality.T5_personExists_from_plurality, Plurality.notAlone, Retorsion.a17_strong_implies_a17_weak, Retorsion.a17b_implies_a17_weak, Retorsion.bigO_bigS_intentional_synthesis, Retorsion.deterministic_transcendental_subject_refutes_freewill, Retorsion.deterministic_transcendental_subject_refutes_person, Retorsion.everything_objective_self_applies, Retorsion.everything_subjective_self_applies, Retorsion.exists_intentional_subject_of_retorsion, Retorsion.exists_intentional_subject_of_subjective, Retorsion.exists_means_not_exists_dependson, Retorsion.exists_non_objective_item, Retorsion.exists_non_subjective_item, Retorsion.exists_objective_of_retorsion, Retorsion.exists_subjective_not_exists_freewill, Retorsion.exists_subjective_not_exists_person, Retorsion.exists_subjective_of_retorsion, Retorsion.intentional_not_freewill, Retorsion.intentional_not_person, Retorsion.intentional_subject_not_person, Retorsion.means_not_dependson, Retorsion.not_everything_objective, Retorsion.not_everything_subjective, Retorsion.objective_and_subjective_disjoint, Retorsion.objective_or_subjective, Retorsion.person_not_freewill, Retorsion.pig_retorsion_exposes_premise_smuggling, Retorsion.representation_not_depends_on_person, Retorsion.restricted_bridge_derives_a17_weak, Retorsion.restricted_bridge_derives_a17b, Retorsion.retorsion_boundary_principle, Retorsion.retorsion_establishes_affirmation, Retorsion.retorsion_no_act, Retorsion.retorsion_no_choiceField, Retorsion.retorsion_no_subject, Retorsion.retorsion_no_truth, Retorsion.retorsion_no_weak_act, Retorsion.retorsion_refutes_denial, Retorsion.subjective_implies_intentional_subject, Retorsion.subjective_not_depends_on_person, Retorsion.universal_objectivity_subjective, Retorsion.weakened_retorsion_derives_intentional_subject, Retorsion.winged_pig_derived_of_pig_reflection, Retorsion.witness_slippage_separation, Value.alone_no_other_affects, Value.harm_affects, Value.help_affects
- **Kernel-derived status** (#print axioms + axiom `Tag:`): **59 ✔** · **23 ⚠** · **0 ◆** (unique steps detailed in the map)
- **Reconciled claim inventory (114 total):** 82 unique active steps (59 ✔ + 23 ⚠) · 5 repeated / dissolved (→) · 21 blocked / missing (✖) · 5 deferred (➖) · 1 other (ANSWERED)
- **Philosophical status histogram:** **COUNTERMODEL 20** · **DEFINITIONAL 29** · **DISSOLVED 6** · **LOGICAL 30** · **METAPHYSICAL 15** · **OPEN 6** · **SEMANTIC 8**
- GAPMAP × derived status: **no divergences** (transcription verified).
- **Steps ⚠ under a substantive axiom (SEM/META)** (24): C15, C18, C19, C20, C28, C29, C32, C33, C34, C40, C41, C42, C43, C44, C45, C46, C47, C48, C54, C60, C61, C74, F1b, F4
- **Displayed ✔ by vocabulary only (axiom-free modulo declared vocabulary)** (kernel footprint contains only the statement's own VOCAB axioms — no SEM/META/TRANS): C100, C101, C21, C23, C24, C25, C30, C39, C49, C51, C52, C53, C55, C56, C57, C58, C62, C68, C77, C83, C84, C85, C86, C91, C92, C94, C97, C98, C99, F1a
- **Kernel × GAPMAP footprint divergences** (2 — fix the GAPMAP ledger):
  - `C85` kernel `{Subject}` vs GAPMAP `{}`
  - `C86` kernel `{Subject}` vs GAPMAP `{}`
- **Graph (closure) × audit (#print axioms) diverge on 1 claims** (depviz transitive undercount — toolchain, not ledger; the audit decides):
  - `FAITH-2` audit `{AxTwoSubjects, Means, Subject}` vs graph `{}`
- Axioms declared in the kernel: **17** — **all carry a `Tag:` line on their Lean docstring**

### D.3 Blocked / deferred / faith inventory

| ID | Prose | Status | Missing lemma / meaning (EN) |
|---|---|---|---|
| F1a | §13–§15 choice-field existence (`∃s p q`, `ChoiceField s p q`) | DISSOLVED | Any person has a choice field: a person is always before two incompatible alternatives. |
| F1b | §15 genuine choice & freedom of the actor | SEMANTIC | Free will exists: some subject genuinely chooses between incompatible alternatives. |
| F2 | §21 teleology (`Ought → Goal`) | OPEN | Deontic teleology is deferred: how norms point at goals is not yet derived. |
| F3 | §28 Good (`§20 → bem`) | OPEN | Moral good from logical normativity is deferred: not yet derived. |
| F4 | §28 Love | DISSOLVED | There are two distinct persons, both lovable. |
| F5 | §28 EternalRelation | DISSOLVED | Eternal loveship is proven: two distinct persons stand in an eternal love-relation, under the bridges and person-stability. |
| F6 | §28 Trinity | OPEN | The Trinity is deferred: no argument exists yet. |
| Q7.2 | weaker `AxGlobalGround` | OPEN | Simulated world-existence: the subject exists only in the `true` world. |
| FAITH-1 | P2 necessity | DISSOLVED | The distinction between right and wrong under the identity-model alias. |
| FAITH-2 | P8 eternal love | DISSOLVED | AxTwoSubjects (META; poem P5/P7, failure traces in DESIGN.md D14 and HostileSemantics): the *reality* of right-and-wrong demands that there be at least two distinct persons. Narrower than the former single bridge… |
| F7 | §15 the bipolar half of freedom | DISSOLVED | F7 (free will under AxActPolarity) is DERIVED / DISSOLVED into F1b: A13 strictly implies A14 (act_polarity_implies_intentional_choice), closing free will via genuineChoice_exists_of_act_constitutive. AxActPolarity… |
| F8 | Trinity | OPEN | The Trinity is not attempted. |
| F9 | Incarnation / creation | OPEN | Incarnation and creation are faith data from the poem, deferred. |

### D.4 Per-claim code annex

<details>
<summary>Lean declaration, file:line, kernel footprint and code dependencies, per claim →</summary>

| ID | Lean declaration | File#L | Kernel axioms | Depends on (Lean) | Used by |
|---|---|---|---|---|---|
| C1 | `Logos.Core.nothingTrueRefutes` | [Core.lean#L61](formal/Logos/Core.lean#L61) | `{}` | `Core.N_T`, `Core.T`, `Core.tschema` | **C2** `notNothingTrue`, `Retorsion.retorsion_no_truth` |
| C2 | `Logos.Core.notNothingTrue` | [Core.lean#L69](formal/Logos/Core.lean#L69) | `{}` | `Core.N_T`, `Core.T`, **C1** `nothingTrueRefutes`, `Core.tschema` | **C35** `negatedAbsolutes`, **C36** `rightWrongDistinction`, **C3** `someTrue` |
| C3 | `Logos.Core.someTrue` | [Core.lean#L77](formal/Logos/Core.lean#L77) | `{CL}` | `Core.N_T`, `Core.T`, **C2** `notNothingTrue` | `Core.someTruthAndSomeFalsehood` |
| C4 | `Logos.Core.atomicTruthWitnessed` | [Core.lean#L85](formal/Logos/Core.lean#L85) | `{}` | `Core.T`, `Core.tschema` | **C26** `T9_incompatibleAlternatives`, **C8** `greatResult` |
| C5 | `Logos.Core.nothingFalseRefutes` | [Core.lean#L94](formal/Logos/Core.lean#L94) | `{}` | `Core.N_F`, `Core.T`, `Core.tschema` | **C6** `notEverythingTrue` |
| C6 | `Logos.Core.notEverythingTrue` | [Core.lean#L103](formal/Logos/Core.lean#L103) | `{}` | `Core.N_F`, `Core.T`, **C5** `nothingFalseRefutes`, `Core.tschema` | **C35** `negatedAbsolutes`, **C36** `rightWrongDistinction` |
| C7 | `Logos.Core.someFalse` | [Core.lean#L111](formal/Logos/Core.lean#L111) | `{}` | `Core.IsFalse`, `Core.T`, `Core.tschema` | `Core.someTruthAndSomeFalsehood`, `Order.fallible_false` |
| C8 | `Logos.Core.greatResult` | [Core.lean#L156](formal/Logos/Core.lean#L156) | `{}` | `Core.IsFalse`, `Core.T`, **C4** `atomicTruthWitnessed`, `Core.atomicWitnessFalsehood` | — |
| C9 | `Logos.Core.noBothTrueAndFalse` | [Core.lean#L162](formal/Logos/Core.lean#L162) | `{}` | `Core.IsFalse`, `Core.T` | — |
| C10 | `Logos.Core.excludedMiddle` | [Core.lean#L174](formal/Logos/Core.lean#L174) | `{CL}` | `Core.T`, `Core.tschema` | — |
| C11 | `Logos.Core.nonContradiction` | [Core.lean#L180](formal/Logos/Core.lean#L180) | `{}` | `Core.T`, `Core.tschema` | — |
| C12 | `Logos.Core.bivalence` | [Core.lean#L186](formal/Logos/Core.lean#L186) | `{CL}` | `Core.IsFalse`, `Core.T` | — |
| C13 | `Logos.Semantics.lawExcludedMiddle` | [Semantics.lean#L76](formal/Logos/Semantics.lean#L76) | `{CL}` | `Semantics.Form`, `Semantics.NecessarilyTrue`, `Semantics.Satisfies`, `Semantics.TrueAt`, `Semantics.World`, `Semantics.sat_not`, `Semantics.sat_or` | **C37** `bothNecessarilyTrueAndFalse`, `Semantics.strongTruth_is_not_atomic` |
| C14 | `Logos.Semantics.nonContradiction` | [Semantics.lean#L85](formal/Logos/Semantics.lean#L85) | `{CL}` | `Semantics.FalseAt`, `Semantics.Form`, `Semantics.NecessarilyFalse`, `Semantics.Satisfies`, `Semantics.World`, `Semantics.sat_and`, `Semantics.sat_not` | **C37** `bothNecessarilyTrueAndFalse` |
| C15 | `Logos.Truthmaker.groundPrinciple_atom` | [Truthmaker.lean#L105](formal/Logos/Truthmaker.lean#L105) | `{Truthmaker, Ground, Subject}` | `Semantics.World`, `Truthmaker.Entity`, `Truthmaker.ExistsAt`, axiom `Ground` (VOCAB), `Truthmaker.TrueAt`, axiom `Truthmaker` (SEM) | — |
| C60 | `Logos.Truthmaker.noGround_selfRefutes` | [Truthmaker.lean#L112](formal/Logos/Truthmaker.lean#L112) | `{Truthmaker, Ground, Subject}` | `Semantics.World`, `Truthmaker.Entity`, `Truthmaker.ExistsAt`, axiom `Ground` (VOCAB), `Truthmaker.TrueAt`, axiom `Truthmaker` (SEM) | — |
| C16 | `Logos.Truthmaker.lawExcludedMiddle` | [Truthmaker.lean#L140](formal/Logos/Truthmaker.lean#L140) | `{CL}` | `Semantics.Form`, `Semantics.World`, `Truthmaker.NecessarilyTrue`, `Truthmaker.TrueAt` | **C19** `T7_excludedMiddleInstance` |
| C17 | `Logos.Truthmaker.nonContradiction` | [Truthmaker.lean#L148](formal/Logos/Truthmaker.lean#L148) | `{}` | `Semantics.Form`, `Semantics.Satisfies`, `Semantics.World`, `Truthmaker.NecessarilyFalse`, `Truthmaker.TrueAt` | — |
| C18 | `Logos.Modal.T7_necessaryReality` | [Modal.lean#L74](formal/Logos/Modal.lean#L74) | `{AxGlobalGround, Ground, Subject}` | axiom `AxGlobalGround` (SEM), `Modal.NecessaryEntity`, `Modal.actualWorld`, `Semantics.Form`, `Semantics.World`, `Truthmaker.Entity`, `Truthmaker.ExistsAt`, axiom `Ground` (VOCAB), `Truthmaker.NecessarilyTrue` | **C34** `necessary_truth_has_necessary_grounder`, **C19** `T7_excludedMiddleInstance`, **C20** `noNecessaryTruthIfAllContingent` |
| C19 | `Logos.Modal.T7_excludedMiddleInstance` | [Modal.lean#L80](formal/Logos/Modal.lean#L80) | `{AxGlobalGround, Ground, Subject, CL}` | `Modal.NecessaryEntity`, **C18** `T7_necessaryReality`, `Semantics.Form`, `Truthmaker.Entity`, axiom `Ground` (VOCAB), **C16** `lawExcludedMiddle` | — |
| C20 | `Logos.Modal.noNecessaryTruthIfAllContingent` | [Modal.lean#L86](formal/Logos/Modal.lean#L86) | `{AxGlobalGround, Ground, Subject}` | `Modal.Contingent`, `Modal.NecessaryEntity`, **C18** `T7_necessaryReality`, `Semantics.Form`, `Truthmaker.Entity`, axiom `Ground` (VOCAB), `Truthmaker.NecessarilyTrue` | — |
| C91 | `Logos.Modal.subject_nec_entity_nec` | [Modal.lean#L103](formal/Logos/Modal.lean#L103) | `{Subject}` | axiom `Subject` (VOCAB), `Modal.NecessaryEntity`, `Plurality.EntityOf`, `Plurality.NecessarySubject` | **C92** `necessary_entity_exists_conditional`, `Modal.necessary_entity_exists_of_necessary_subject` |
| C78 | — | — | — | — | Modal.contingent_ground |
| C79 | — | — | — | — | Modal.ultimateGround_exists |
| C87 | — | — | — | — | Modal.origin_is_necessary |
| C88 | — | — | — | — | Modal.transcendental_quantifier_swap |
| C89 | — | — | — | — | Modal.ultimateGroundInit_exists |
| C58 | `Logos.Agency.noWeakAct_selfRefutes` | [Agency.lean#L182](formal/Logos/Agency.lean#L182) | `{Subject, act}` | `Agency.NoWeakAct`, axiom `Subject` (VOCAB), axiom `act` (VOCAB), `Agency.asserts`, `Agency.weak_act_exists_of_assert` | `Retorsion.retorsion_no_weak_act` |
| C68 | `Logos.Agency.Cogito` | [Agency.lean#L261](formal/Logos/Agency.lean#L261) | `{Initiates, Means, State, Subject}` | `Agency.Act`, `Agency.Asserts`, axiom `Subject` (VOCAB), `Agency.act_exists_of_assert` | — |
| C21 | `Logos.Plurality.T1_subjectExists` | [Plurality.lean#L67](formal/Logos/Plurality.lean#L67) | `{Initiates, Means, State, Subject}` | `Agency.Act`, axiom `Subject` (VOCAB), `Agency.SubjectExists`, `Agency.subject_exists_of_act` | **C23** `T4_agentExists` |
| C22 | `Logos.Agency.T2_contentExists` | [Agency.lean#L320](formal/Logos/Agency.lean#L320) | `{}` | `Agency.Content` | — |
| C23 | `Logos.Plurality.T4_agentExists` | [Plurality.lean#L75](formal/Logos/Plurality.lean#L75) | `{Initiates, Means, State, Subject}` | `Agency.Act`, `Agency.Agent`, axiom `Subject` (VOCAB), `Agency.SubjectExists`, **C21** `T1_subjectExists` | — |
| C24 | `Logos.Plurality.T5_intentionalSubjectExists` | [Plurality.lean#L83](formal/Logos/Plurality.lean#L83) | `{Initiates, Means, State, Subject}` | `Agency.Act`, axiom `Subject` (VOCAB), `Person.IntentionalSubject`, `Person.intentionalSubject_exists_of_act` | **C39** `T11_choiceField` |
| C25 | `Logos.Person.inseparability_24b` | [Person.lean#L143](formal/Logos/Person.lean#L143) | `{Initiates, Means, State, Subject, CL}` | `Agency.A`, axiom `Means` (VOCAB), axiom `Subject` (VOCAB), `Agency.act_implies_means`, `Core.IsFalse`, `Core.T`, `Person.CarriesLogicalFeature`, `Person.CarriesPersonalFeature`, `Person.HasFeature`, `Person.RationalAct` | — |
| C26 | `Logos.Alternatives.T9_incompatibleAlternatives` | [Alternatives.lean#L24](formal/Logos/Alternatives.lean#L24) | `{}` | `Alternatives.Incompatible`, `Core.IsFalse`, `Core.T`, **C4** `atomicTruthWitnessed`, `Core.atomicWitnessFalsehood` | **C39** `T11_choiceField`, `Choice.T11_choiceField_from_plurality` |
| C27 | `Logos.Alternatives.incompatible_with_negation` | [Alternatives.lean#L35](formal/Logos/Alternatives.lean#L35) | `{}` | `Alternatives.Incompatible`, `Core.IsFalse`, `Core.T`, `Core.tschema` | — |
| C28 | `Logos.Order.T6_fallibility` | [Order.lean#L135](formal/Logos/Order.lean#L135) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Core.IsFalse`, `Core.T`, `Order.Fallible`, `Order.fallible_false` | — |
| C29 | `Logos.Order.T6_truthTranscendsWill` | [Order.lean#L144](formal/Logos/Order.lean#L144) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Core.IsFalse`, `Core.T`, `Order.Fallible`, `Order.fallible_false` | — |
| C30 | `Logos.Order.correctness_distinct` | [Order.lean#L152](formal/Logos/Order.lean#L152) | `{Initiates, Means, State, Subject, CL}` | `Agency.A`, axiom `Subject` (VOCAB), `Core.IsFalse`, `Core.T`, `Order.Correct`, `Order.Incorrect` | — |
| C31 | `Logos.Order.consequence_preserves_truth` | [Order.lean#L195](formal/Logos/Order.lean#L195) | `{}` | `Core.T`, `Core.tschema` | — |
| C83 | `Logos.Order.no_correct_judgment_of_no_act` | [Order.lean#L204](formal/Logos/Order.lean#L204) | `{Initiates, Means, State, Subject}` | `Agency.A`, axiom `Subject` (VOCAB), `Core.T`, `Order.Correct`, `Order.NoAct` | `Order.judgment_of_no_act_is_incorrect` |
| C84 | `Logos.Order.judgment_of_no_act_proves_act` | [Order.lean#L225](formal/Logos/Order.lean#L225) | `{Initiates, Means, State, Subject}` | `Agency.A`, axiom `Subject` (VOCAB), `Order.Correct`, `Order.Incorrect`, `Order.NoAct`, `Order.judgment_implies_act` | — |
| C32 | `Logos.GroundPerson.T8_personalGround` | [GroundPerson.lean#L112](formal/Logos/GroundPerson.lean#L112) | `{AxPersonalGround, GroundProp, Initiates, Means, State, Subject}` | `GroundPerson.AxGroundBearing`, axiom `AxPersonalGround` (META), axiom `GroundProp` (VOCAB), `GroundPerson.IsPresentPersonalFeature`, `GroundPerson.Personal`, `GroundPerson.Realizes`, `Modal.NecessaryEntity`, `Truthmaker.Entity` | — |
| C33 | `Logos.GroundPerson.present_feature_is_grounded` | [GroundPerson.lean#L120](formal/Logos/GroundPerson.lean#L120) | `{GroundPrincipleProp, GroundProp, Initiates, Means, State, Subject}` | `Core.T`, axiom `GroundPrincipleProp` (SEM), axiom `GroundProp` (VOCAB), `GroundPerson.IsPresentPersonalFeature`, `Truthmaker.Entity` | — |
| C34 | `Logos.GroundPerson.necessary_truth_has_necessary_grounder` | [GroundPerson.lean#L125](formal/Logos/GroundPerson.lean#L125) | `{AxGlobalGround, Ground, Subject}` | `Modal.NecessaryEntity`, **C18** `T7_necessaryReality`, `Semantics.Form`, `Truthmaker.Entity`, axiom `Ground` (VOCAB), `Truthmaker.NecessarilyTrue` | — |
| C90 | — | — | — | — | GroundPerson.personal_ultimate_ground_exists |
| F1a | `Logos.Choice.person_hasChoiceField` | [Choice.lean#L320](formal/Logos/Choice.lean#L320) | `{Means, Subject}` | axiom `Subject` (VOCAB), `Choice.ChoiceField`, `Choice.intentional_hasChoiceField`, `Person.Person`, `Person.person_is_intentional` | **C54** `JUDGE_HAS_CHOICE_FIELD`, `Choice.choiceField_exists_from_plurality` |
| F1b | `Logos.Choice.freeWill_exists` | [Choice.lean#L1118](formal/Logos/Choice.lean#L1118) | `{AxIntentionalChoice, Initiates, Means, State, Subject}` | `Agency.Act`, axiom `Subject` (VOCAB), `Choice.FreeWill`, `Choice.freeWill_exists_of_act` | — |
| F2 | — | — | — | — | — |
| F3 | — | — | — | — | — |
| F4 | `Logos.Love.T13_someoneLovable` | [Love.lean#L81](formal/Logos/Love.lean#L81) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Love.Lovable`, `Person.Person`, **C40** `T12_twoPersons` | — |
| F5 | — | — | — | — | Love.T14_eternalRelation |
| F6 | — | — | — | — | — |
| Q7.2 | `CountermodelPersonNotNecessary.ExistsAt` | [HostileSemantics.lean#L720](formal/Logos/HostileSemantics.lean#L720) | `{}` | — | — |
| C35 | `Logos.Core.negatedAbsolutes` | [Core.lean#L129](formal/Logos/Core.lean#L129) | `{}` | `Core.N_F`, `Core.N_T`, **C6** `notEverythingTrue`, **C2** `notNothingTrue` | — |
| C36 | `Logos.Core.rightWrongDistinction` | [Core.lean#L145](formal/Logos/Core.lean#L145) | `{}` | `Core.N_F`, `Core.N_T`, **C6** `notEverythingTrue`, **C2** `notNothingTrue` | **FAITH-1** `necDistinction`, **C40** `T12_twoPersons`, **C74** `aloneExcluded` |
| C37 | `Logos.Semantics.bothNecessarilyTrueAndFalse` | [Semantics.lean#L102](formal/Logos/Semantics.lean#L102) | `{CL}` | `Semantics.Form`, `Semantics.NecessarilyFalse`, `Semantics.NecessarilyTrue`, **C13** `lawExcludedMiddle`, **C14** `nonContradiction` | **C59** `strongTruthExists`, `Semantics.strongTruth_and_contingent_content` |
| C59 | `Logos.Semantics.strongTruthExists` | [Semantics.lean#L113](formal/Logos/Semantics.lean#L113) | `{CL}` | `Semantics.Form`, `Semantics.NecessarilyFalse`, `Semantics.NecessarilyTrue`, **C37** `bothNecessarilyTrueAndFalse` | **C93** `noStrongTruth_selfRefutes` |
| C93 | `Logos.Semantics.noStrongTruth_selfRefutes` | [Semantics.lean#L121](formal/Logos/Semantics.lean#L121) | `{CL}` | `Semantics.Form`, `Semantics.NecessarilyTrue`, **C59** `strongTruthExists` | **C94** `noStrongTruth_assertable_refutes` |
| C94 | `Logos.Choice.noStrongTruth_assertable_refutes` | [Choice.lean#L1227](formal/Logos/Choice.lean#L1227) | `{Initiates, Means, State, Subject, CL}` | `Agency.Act`, `Agency.Asserts`, axiom `Subject` (VOCAB), `Semantics.Form`, `Semantics.NecessarilyTrue`, **C93** `noStrongTruth_selfRefutes` | — |
| C95 | `Logos.Semantics.atoms_are_modally_free` | [Semantics.lean#L146](formal/Logos/Semantics.lean#L146) | `{}` | `Semantics.NecessarilyFalse`, `Semantics.NecessarilyTrue`, `Semantics.atom_not_necessarily_false`, `Semantics.atom_not_necessarily_true` | **C96** `some_formula_contingent` |
| C96 | `Logos.Semantics.some_formula_contingent` | [Semantics.lean#L160](formal/Logos/Semantics.lean#L160) | `{}` | `Semantics.Form`, `Semantics.NecessarilyFalse`, `Semantics.NecessarilyTrue`, **C95** `atoms_are_modally_free` | `Semantics.strongTruth_and_contingent_content` |
| C38 | `Logos.Necessity.necDistinction` | [Necessity.lean#L116](formal/Logos/Necessity.lean#L116) | `{}` | `Core.N_F`, `Core.N_T`, **C36** `rightWrongDistinction`, `Necessity.Necessity`, `Semantics.World` | `Necessity.necDistinction_content` |
| C39 | `Logos.Choice.T11_choiceField` | [Choice.lean#L290](formal/Logos/Choice.lean#L290) | `{Initiates, Means, State, Subject}` | `Agency.A`, axiom `Subject` (VOCAB), `Alternatives.Incompatible`, **C26** `T9_incompatibleAlternatives`, `Core.IsFalse`, `Core.T`, `Person.IntentionalSubject`, **C24** `T5_intentionalSubjectExists` | — |
| C40 | `Logos.Plurality.T12_twoPersons` | [Plurality.lean#L44](formal/Logos/Plurality.lean#L44) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), **C36** `rightWrongDistinction`, `Person.Person`, **FAITH-2** `AxTwoSubjects` | `Choice.choiceField_exists_from_plurality`, **C41** `T13_someoneLovable`, **C43** `T14_content_conditional`, **C42** `T14_eternalRelation_conditional`, **C47** `T12_directedPair_conditional`, `Plurality.T1_subjectExists_from_plurality`, `Plurality.T5_personExists_from_plurality`, **C48** `cogito_from_T12`, `Plurality.notAlone` |
| C41 | `Logos.Love.T13_someoneLovable` | [Love.lean#L81](formal/Logos/Love.lean#L81) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Love.Lovable`, `Person.Person`, **C40** `T12_twoPersons` | — |
| C48 | `Logos.Plurality.cogito_from_T12` | [Plurality.lean#L57](formal/Logos/Plurality.lean#L57) | `{AxTwoSubjects, Means, Subject}` | axiom `Means` (VOCAB), axiom `Subject` (VOCAB), `Person.IntentionalSubject`, `Person.Person`, `Person.person_is_intentional`, **C40** `T12_twoPersons` | `Order.fallible_false` |
| C49 | `Logos.Choice.meaning_needs_subject` | [Choice.lean#L137](formal/Logos/Choice.lean#L137) | `{Means, Subject}` | axiom `Means` (VOCAB), axiom `Subject` (VOCAB) | — |
| C50 | `Logos.Choice.incompatible_self_negation` | [Choice.lean#L113](formal/Logos/Choice.lean#L113) | `{}` | `Alternatives.Incompatible` | `Choice.act_implies_authors`, `Choice.act_implies_choiceField`, `Choice.act_polarity_implies_contrastive`, `Choice.act_polarity_implies_intentional_choice`, `Choice.asserting_noChoiceField_is_choiceField`, `Choice.asserts_selects`, `Choice.deliberate_resource_implies_genuine_choice`, `Choice.genuineChoice_exists_of_act`, `Choice.genuineChoice_exists_of_existential_act_polarity`, `Choice.genuineChoice_of_doubt`, `Choice.intentional_hasChoiceField`, `Choice.judge_asserting_rightWrong_has_choiceField`, `Choice.rejectedHornCoMeant_implies_genuineChoice`, `Choice.selfDenial_implies_genuineChoice_of_polarity`, **C55** `judge_commits` |
| C51 | `Logos.Choice.person_hasChoiceField` | [Choice.lean#L320](formal/Logos/Choice.lean#L320) | `{Means, Subject}` | axiom `Subject` (VOCAB), `Choice.ChoiceField`, `Choice.intentional_hasChoiceField`, `Person.Person`, `Person.person_is_intentional` | **C54** `JUDGE_HAS_CHOICE_FIELD`, `Choice.choiceField_exists_from_plurality` |
| C52 | `Logos.Choice.choiceField_exists` | [Choice.lean#L330](formal/Logos/Choice.lean#L330) | `{Initiates, Means, State, Subject}` | `Agency.A`, axiom `Subject` (VOCAB), `Choice.ChoiceField`, `Choice.intentional_hasChoiceField`, `Person.act_implies_intentional` | — |
| C53 | `Logos.Choice.noChoiceField_selfRefutes` | [Choice.lean#L355](formal/Logos/Choice.lean#L355) | `{Initiates, Means, State, Subject}` | `Agency.Act`, `Agency.Asserts`, axiom `Subject` (VOCAB), `Choice.NoChoiceField`, `Choice.asserting_noChoiceField_is_choiceField` | `Retorsion.retorsion_no_choiceField` |
| C54 | `Logos.Choice.JUDGE_HAS_CHOICE_FIELD` | [Choice.lean#L371](formal/Logos/Choice.lean#L371) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Choice.ChoiceField`, **C51** `person_hasChoiceField`, `Core.N_F`, `Core.N_T`, `Person.Person`, **FAITH-2** `AxTwoSubjects` | **C61** `rightWrong_implies_someone_means` |
| C55 | `Logos.Order.judge_commits` | [Order.lean#L172](formal/Logos/Order.lean#L172) | `{Initiates, Means, State, Subject, CL}` | `Agency.A`, axiom `Initiates` (VOCAB), axiom `Means` (VOCAB), axiom `State` (VOCAB), axiom `Subject` (VOCAB), `Alternatives.Incompatible`, `Choice.ChoiceField`, **C50** `incompatible_self_negation`, `Core.IsFalse`, `Core.T`, `Order.Correct`, `Order.Incorrect` | `Order.rightWrongDistinction_implies_meaning` |
| C56 | `Logos.Value.alone_no_other_help_harm` | [Value.lean#L95](formal/Logos/Value.lean#L95) | `{Subject}` | axiom `Subject` (VOCAB), `Value.Alone`, `Value.Harms`, `Value.Helps` | — |
| C57 | `Logos.Choice.noSubject_selfRefutes` | [Choice.lean#L398](formal/Logos/Choice.lean#L398) | `{Initiates, Means, State, Subject}` | `Agency.Asserts`, `Agency.NoSubject`, axiom `Subject` (VOCAB), `Agency.noSubject_performative_selfRefutes` | `Retorsion.retorsion_no_subject` |
| C42 | `Logos.Love.T14_eternalRelation_conditional` | [Love.lean#L119](formal/Logos/Love.lean#L119) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Love.Loves`, `Love.PersonStabilityPrinciple`, `Love.PluralityLovePrinciple`, `Person.Person`, `Plurality.NecessarySubject`, **C40** `T12_twoPersons` | **C45** `T14_square_conditional`, **C44** `T14_world_conditional` |
| C43 | `Logos.Love.T14_content_conditional` | [Love.lean#L151](formal/Logos/Love.lean#L151) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Love.Loves`, `Love.PluralityLovePrinciple`, `Person.Person`, **C40** `T12_twoPersons` | — |
| C44 | `Logos.Love.T14_world_conditional` | [Love.lean#L129](formal/Logos/Love.lean#L129) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Love.Loves`, `Love.PersonStabilityPrinciple`, `Love.PluralityLovePrinciple`, **C42** `T14_eternalRelation_conditional`, `Necessity.NecessityPH`, `Person.Person`, `Plurality.EntityOf`, `Plurality.NecessarySubject`, `Semantics.World`, `Truthmaker.ExistsAt` | — |
| C45 | `Logos.Love.T14_square_conditional` | [Love.lean#L141](formal/Logos/Love.lean#L141) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Love.Loves`, `Love.PersonStabilityPrinciple`, `Love.PluralityLovePrinciple`, **C42** `T14_eternalRelation_conditional`, `Necessity.Necessity`, `Person.Person`, `Plurality.NecessarySubject`, `Semantics.World` | — |
| C46 | `Logos.Value.valueInterpersonal_of_split_conditional` | [Value.lean#L139](formal/Logos/Value.lean#L139) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Core.N_F`, `Core.N_T`, `Person.Person`, `Value.Affects`, **FAITH-2** `AxTwoSubjects`, `Value.PersonsAffectPrinciple` | — |
| C47 | `Logos.Plurality.T12_directedPair_conditional` | [Plurality.lean#L124](formal/Logos/Plurality.lean#L124) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Person.Person`, **C40** `T12_twoPersons`, `Value.Affects`, `Value.PersonsAffectPrinciple` | — |
| C61 | `Logos.Choice.rightWrong_implies_someone_means` | [Choice.lean#L391](formal/Logos/Choice.lean#L391) | `{AxTwoSubjects, Means, Subject}` | axiom `Means` (VOCAB), axiom `Subject` (VOCAB), `Alternatives.Incompatible`, `Choice.ChoiceField`, **C54** `JUDGE_HAS_CHOICE_FIELD`, `Core.N_F`, `Core.N_T` | — |
| C62 | `Logos.Order.rightWrong_implies_meaning` | [Order.lean#L91](formal/Logos/Order.lean#L91) | `{Initiates, Means, State, Subject}` | `Agency.A`, axiom `Initiates` (VOCAB), axiom `Means` (VOCAB), axiom `State` (VOCAB), axiom `Subject` (VOCAB), `Choice.Meaning_I`, `Core.IsFalse`, `Core.T`, `Order.Correct`, `Order.Incorrect` | `Order.rightDistinctWrong_implies_meaning`, `Order.rightWrongDistinction_implies_meaning` |
| C101 | `Logos.Order.act_iff_asserts_or_incorrect` | [Order.lean#L57](formal/Logos/Order.lean#L57) | `{Initiates, Means, State, Subject, CL}` | `Agency.A`, `Agency.Act`, `Agency.Asserts`, axiom `Subject` (VOCAB), `Core.IsFalse`, `Order.Incorrect` | — |
| C97 | `Logos.Choice.deliberateChoice_implies_selects` | [Choice.lean#L490](formal/Logos/Choice.lean#L490) | `{Initiates, Means, State, Subject}` | `Agency.Asserts`, axiom `Means` (VOCAB), axiom `Subject` (VOCAB), `Alternatives.Incompatible`, `Choice.DeliberateChoice`, `Choice.Selects` | **C100** `deliberateChoice_iff_selects_and_means`, `Choice.deliberateChoice_iff_selects_and_rejects` |
| C98 | `Logos.Choice.deliberateChoice_implies_chooses` | [Choice.lean#L496](formal/Logos/Choice.lean#L496) | `{Initiates, Means, State, Subject}` | `Agency.Asserts`, axiom `Means` (VOCAB), axiom `Subject` (VOCAB), `Alternatives.Incompatible`, `Choice.Chooses`, `Choice.DeliberateChoice` | `Choice.selfAssertedDeliberateChoice_factive_implies_chooses` |
| C99 | `Logos.Choice.selection_exists_of_act` | [Choice.lean#L693](formal/Logos/Choice.lean#L693) | `{Initiates, Means, State, Subject}` | `Agency.Act`, `Agency.Asserts`, axiom `Subject` (VOCAB), `Choice.Selects`, `Choice.act_implies_asserts_bridge`, `Choice.selection_exists` | — |
| C100 | `Logos.Choice.deliberateChoice_iff_selects_and_means` | [Choice.lean#L504](formal/Logos/Choice.lean#L504) | `{Initiates, Means, State, Subject}` | `Agency.Act`, `Agency.Asserts`, axiom `Initiates` (VOCAB), axiom `Means` (VOCAB), axiom `State` (VOCAB), axiom `Subject` (VOCAB), `Alternatives.Incompatible`, `Choice.DeliberateChoice`, `Choice.Selects`, **C97** `deliberateChoice_implies_selects` | `Choice.deliberateChoice_negation_decomposition`, `Choice.deliberateChoice_negation_iff` |
| C69 | — | — | — | — | — |
| C70 | — | — | — | — | — |
| C71 | — | — | — | — | — |
| C72 | — | — | — | — | — |
| C73 | — | — | — | — | Person.twoPersonsFromSubject |
| C74 | `Logos.Value.aloneExcluded` | [Value.lean#L124](formal/Logos/Value.lean#L124) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), **C36** `rightWrongDistinction`, `Person.Person`, `Value.Alone`, **FAITH-2** `AxTwoSubjects` | — |
| C75 | — | — | — | — | Person.everyContentIsAPerson |
| C76 | — | — | — | — | Love.T14_canonicalRigid |
| C77 | `Logos.Love.necessaryPersonExists_conditional` | [Love.lean#L98](formal/Logos/Love.lean#L98) | `{Initiates, Means, State, Subject}` | `Agency.Act`, axiom `Subject` (VOCAB), `Love.PersonStabilityPrinciple`, `Person.Person`, `Plurality.NecessarySubject` | **C92** `necessary_entity_exists_conditional` |
| C85 | `Logos.Value.help_not_harm` | [Value.lean#L74](formal/Logos/Value.lean#L74) | `{Subject}` | axiom `Subject` (VOCAB), `Value.BearingOf`, `Value.Harms`, `Value.Helps`, `Value.InterpersonalBearing` | `Love.loves_of_helps` |
| C86 | `Logos.Love.love_helps` | [Love.lean#L47](formal/Logos/Love.lean#L47) | `{Subject}` | axiom `Subject` (VOCAB), `Love.Loves`, `Value.Harms`, `Value.Helps` | — |
| C92 | `Logos.Love.necessary_entity_exists_conditional` | [Love.lean#L109](formal/Logos/Love.lean#L109) | `{Initiates, Means, State, Subject}` | `Agency.Act`, axiom `Subject` (VOCAB), `Love.PersonStabilityPrinciple`, **C77** `necessaryPersonExists_conditional`, `Modal.NecessaryEntity`, **C91** `subject_nec_entity_nec`, `Person.Person`, `Plurality.EntityOf`, `Plurality.NecessarySubject`, `Truthmaker.Entity` | — |
| C63 | `Logos.Initiation.branches_not_transfer` | [Initiation.lean#L27](formal/Logos/Initiation.lean#L27) | `{}` | `Initiation.Branches`, `Initiation.IsTransfer` | — |
| C64 | — | — | — | — | Initiation.originates_not_transfer |
| C65 | — | — | — | — | Initiation.person_iff_originates |
| C66 | — | — | — | — | Initiation.Cogito_Init |
| C67 | — | — | — | — | Initiation.noInitiation_selfRefutes |
| C80 | — | — | — | — | Initiation.posited_not_branch |
| C81 | — | — | — | — | Initiation.origin_branches |
| C82 | — | — | — | — | Initiation.origin_is_initiating_person |
| FAITH-1 | `Logos.Necessity.necDistinction` | [Necessity.lean#L116](formal/Logos/Necessity.lean#L116) | `{}` | `Core.N_F`, `Core.N_T`, **C36** `rightWrongDistinction`, `Necessity.Necessity`, `Semantics.World` | `Necessity.necDistinction_content` |
| FAITH-2 | `Logos.Value.AxTwoSubjects` | [Value.lean#L115](formal/Logos/Value.lean#L115) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Core.N_F`, `Core.N_T`, `Person.Person` | **C54** `JUDGE_HAS_CHOICE_FIELD`, **C40** `T12_twoPersons`, **C74** `aloneExcluded`, **C46** `valueInterpersonal_of_split_conditional` |
| F7 | — | — | — | — | — |
| F8 | — | — | — | — | — |
| F9 | — | — | — | — | — |

</details>

---
### D.5 Kernel declaration index

<details>
<summary>All user-authored theorems/defs, by module (line and kernel axioms) →</summary>

### `CountermodelActWithoutAssertion`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Act` | def | [L2009](formal/Logos/HostileSemantics.lean#L2009) | `def Act (s : S) (p : Prop) : Prop` | —  |
| `Asserts` | def | [L2010](formal/Logos/HostileSemantics.lean#L2010) | `def Asserts (s : S) (p : Prop) : Prop` | —  |
| `Means` | def | [L2008](formal/Logos/HostileSemantics.lean#L2008) | `def Means (_s : S) (p : Prop) : Prop` | —  |
| `S` | def | [L2007](formal/Logos/HostileSemantics.lean#L2007) | `def S : Type` | —  |
| `act_datum_holds` | theorem | [L2012](formal/Logos/HostileSemantics.lean#L2012) | `theorem act_datum_holds : ∃ s : S, ∃ p : Prop, Act s p` | —  |
| `act_does_not_imply_assertion` | theorem | [L2022](formal/Logos/HostileSemantics.lean#L2022) | `theorem act_does_not_imply_assertion : (∃ s : S, ∃ p : Prop, Act s p) ∧ ¬ (∃ s :` | —  |
| `no_assertion` | theorem | [L2015](formal/Logos/HostileSemantics.lean#L2015) | `theorem no_assertion : ¬ ∃ s : S, ∃ p : Prop, Asserts s p` | —  |

### `CountermodelActWithoutSubject`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Act` | def | [L348](formal/Logos/HostileSemantics.lean#L348) | `def Act : Entity → Prop → Prop` | —  |
| `ConstitutiveAct` | def | [L362](formal/Logos/HostileSemantics.lean#L362) | `def ConstitutiveAct (I : ActOntology) : Prop` | —  |
| `Entity` | def | [L347](formal/Logos/HostileSemantics.lean#L347) | `def Entity : Type` | —  |
| `Person` | def | [L350](formal/Logos/HostileSemantics.lean#L350) | `def Person : Entity → Prop` | —  |
| `Subject` | def | [L349](formal/Logos/HostileSemantics.lean#L349) | `def Subject : Entity → Prop` | —  |
| `act_occurs` | theorem | [L352](formal/Logos/HostileSemantics.lean#L352) | `theorem act_occurs : ∃ s : Entity, ∃ p : Prop, Act s p` | —  |
| `act_without_subject` | theorem | [L357](formal/Logos/HostileSemantics.lean#L357) | `theorem act_without_subject : (∃ s : Entity, ∃ p : Prop, Act s p) ∧ ¬ (∃ s : Ent` | —  |
| `countermodel_violates_constitutive_act` | theorem | [L373](formal/Logos/HostileSemantics.lean#L373) | `theorem countermodel_violates_constitutive_act : ¬ ConstitutiveAct { Entity` | —  |
| `no_person` | theorem | [L354](formal/Logos/HostileSemantics.lean#L354) | `theorem no_person : ¬ ∃ s : Entity, Person s` | —  |
| `no_subject` | theorem | [L353](formal/Logos/HostileSemantics.lean#L353) | `theorem no_subject : ¬ ∃ s : Entity, Subject s` | —  |
| `subject_of_constitutive_act` | theorem | [L366](formal/Logos/HostileSemantics.lean#L366) | `theorem subject_of_constitutive_act (I : ActOntology) (hConst : ConstitutiveAct ` | —  |

### `CountermodelImpersonalUltimateGround`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Entity` | abbrev | [L2365](formal/Logos/HostileSemantics.lean#L2365) | `abbrev Entity : Type` | —  |
| `GroundEntity` | def | [L2367](formal/Logos/HostileSemantics.lean#L2367) | `def GroundEntity (_x _y : Entity) : Prop` | —  |
| `Personal` | def | [L2369](formal/Logos/HostileSemantics.lean#L2369) | `def Personal (_e : Entity) : Prop` | —  |
| `UltimateGround` | def | [L2368](formal/Logos/HostileSemantics.lean#L2368) | `def UltimateGround (u : Entity) : Prop` | —  |
| `no_personal_ultimate` | theorem | [L2376](formal/Logos/HostileSemantics.lean#L2376) | `theorem no_personal_ultimate : ¬ ∃ u : Entity, UltimateGround u ∧ Personal u` | —  |
| `ultimate_exists` | theorem | [L2371](formal/Logos/HostileSemantics.lean#L2371) | `theorem ultimate_exists : ∃ u : Entity, UltimateGround u` | —  |
| `ultimate_not_entails_personal` | theorem | [L2381](formal/Logos/HostileSemantics.lean#L2381) | `theorem ultimate_not_entails_personal : (∃ u : Entity, UltimateGround u) ∧ ¬ (∃ ` | —  |

### `CountermodelInfiniteGroundChain`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Entity` | abbrev | [L2220](formal/Logos/HostileSemantics.lean#L2220) | `abbrev Entity : Type` | —  |
| `GroundEntity` | def | [L2223](formal/Logos/HostileSemantics.lean#L2223) | `def GroundEntity (x y : Entity) : Prop` | —  |
| `GroundProp` | def | [L2259](formal/Logos/HostileSemantics.lean#L2259) | `def GroundProp (_e : Entity) (p : Prop) : Prop` | —  |
| `PermissiveTruthGroundedInfiniteChain` | def | [L2285](formal/Logos/HostileSemantics.lean#L2285) | `def PermissiveTruthGroundedInfiniteChain : TruthGroundedRegressSignature where E` | —  |
| `TotalityGroundingSignature` | structure | [L2325](formal/Logos/HostileSemantics.lean#L2325) | `structure TotalityGroundingSignature where` | —  |
| `TruthGroundedRegressSignature` | structure | [L2273](formal/Logos/HostileSemantics.lean#L2273) | `structure TruthGroundedRegressSignature where` | —  |
| `UltimateGround` | def | [L2225](formal/Logos/HostileSemantics.lean#L2225) | `def UltimateGround (u : Entity) : Prop` | —  |
| `UltimateGroundExists` | def | [L2227](formal/Logos/HostileSemantics.lean#L2227) | `def UltimateGroundExists : Prop` | —  |
| `asymmetric` | theorem | [L2232](formal/Logos/HostileSemantics.lean#L2232) | `theorem asymmetric (x y : Entity) : GroundEntity x y → ¬ GroundEntity y x` | —  |
| `ground_principle_prop_satisfied` | theorem | [L2263](formal/Logos/HostileSemantics.lean#L2263) | `theorem ground_principle_prop_satisfied (p : Prop) (hp : p) : ∃ e : Entity, Grou` | —  |
| `infinite_chain_has_no_ultimate` | theorem | [L2242](formal/Logos/HostileSemantics.lean#L2242) | `theorem infinite_chain_has_no_ultimate : (∀ x, ¬ GroundEntity x x) ∧ (∀ x y, Gro` | —  |
| `irreflexive` | theorem | [L2229](formal/Logos/HostileSemantics.lean#L2229) | `theorem irreflexive (x : Entity) : ¬ GroundEntity x x` | —  |
| `no_ultimate` | theorem | [L2238](formal/Logos/HostileSemantics.lean#L2238) | `theorem no_ultimate : ¬ UltimateGroundExists` | —  |
| `retorsion_cannot_refute_infinite_regress` | theorem | [L2302](formal/Logos/HostileSemantics.lean#L2302) | `theorem retorsion_cannot_refute_infinite_regress : ¬ (∀ I : TruthGroundedRegress` | —  |
| `thesis_itself_grounded` | theorem | [L2268](formal/Logos/HostileSemantics.lean#L2268) | `theorem thesis_itself_grounded : ∃ e : Entity, GroundProp e (¬ UltimateGroundExi` | —  |
| `totality_grounding_forces_ultimate_ground` | theorem | [L2343](formal/Logos/HostileSemantics.lean#L2343) | `theorem totality_grounding_forces_ultimate_ground (I : TotalityGroundingSignatur` | —  |
| `transitive` | theorem | [L2235](formal/Logos/HostileSemantics.lean#L2235) | `theorem transitive (x y z : Entity) : GroundEntity x y → GroundEntity y z → Grou` | —  |
| `ultimate_ground_dilemma` | theorem | [L2352](formal/Logos/HostileSemantics.lean#L2352) | `theorem ultimate_ground_dilemma : (¬ (∀ I : TruthGroundedRegressSignature, I.Ult` | —  |

### `CountermodelMeaningWithoutInitiation`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Act` | def | [L457](formal/Logos/HostileSemantics.lean#L457) | `def Act (s : Entity) (p : Prop) : Prop` | —  |
| `Entity` | def | [L453](formal/Logos/HostileSemantics.lean#L453) | `def Entity : Type` | —  |
| `Initiates` | def | [L456](formal/Logos/HostileSemantics.lean#L456) | `def Initiates : Entity → State → State → Prop → Prop` | —  |
| `Means` | def | [L455](formal/Logos/HostileSemantics.lean#L455) | `def Means : Entity → Prop → Prop` | —  |
| `State` | def | [L454](formal/Logos/HostileSemantics.lean#L454) | `def State : Type` | —  |
| `meaning_occurs` | theorem | [L460](formal/Logos/HostileSemantics.lean#L460) | `theorem meaning_occurs : ∃ s : Entity, ∃ p : Prop, Means s p` | —  |
| `means_does_not_imply_act` | theorem | [L473](formal/Logos/HostileSemantics.lean#L473) | `theorem means_does_not_imply_act : (∃ s : Entity, ∃ p : Prop, Means s p) ∧ ¬ (∃ ` | —  |
| `means_does_not_imply_initiates` | theorem | [L467](formal/Logos/HostileSemantics.lean#L467) | `theorem means_does_not_imply_initiates : (∃ s : Entity, ∃ p : Prop, Means s p) ∧` | —  |
| `no_act` | theorem | [L463](formal/Logos/HostileSemantics.lean#L463) | `theorem no_act : ¬ ∃ s : Entity, ∃ p : Prop, Act s p` | —  |
| `no_initiation` | theorem | [L461](formal/Logos/HostileSemantics.lean#L461) | `theorem no_initiation : ¬ ∃ s : Entity, ∃ p : Prop, ∃ w w' : State, Initiates s ` | —  |

### `CountermodelNoFreeWill`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `A` | def | [L534](formal/Logos/HostileSemantics.lean#L534) | `def A : S → Prop → Prop` | —  |
| `Chooses` | def | [L535](formal/Logos/HostileSemantics.lean#L535) | `def Chooses : S → Prop → Prop → Prop` | —  |
| `FreeWill` | def | [L536](formal/Logos/HostileSemantics.lean#L536) | `def FreeWill : S → Prop` | —  |
| `S` | def | [L533](formal/Logos/HostileSemantics.lean#L533) | `def S : Type` | —  |
| `act_does_not_imply_choice` | theorem | [L541](formal/Logos/HostileSemantics.lean#L541) | `theorem act_does_not_imply_choice : (∃ s : S, ∃ p : Prop, A s p) ∧ ¬ (∃ s : S, ∃` | —  |
| `act_does_not_imply_freewill` | theorem | [L544](formal/Logos/HostileSemantics.lean#L544) | `theorem act_does_not_imply_freewill : (∃ s : S, ∃ p : Prop, A s p) ∧ ¬ (∃ s : S,` | —  |
| `act_occurs` | theorem | [L538](formal/Logos/HostileSemantics.lean#L538) | `theorem act_occurs : ∃ s : S, ∃ p : Prop, A s p` | —  |
| `no_choice` | theorem | [L539](formal/Logos/HostileSemantics.lean#L539) | `theorem no_choice : ¬ ∃ s : S, ∃ p q : Prop, Chooses s p q` | —  |
| `no_free_will` | theorem | [L540](formal/Logos/HostileSemantics.lean#L540) | `theorem no_free_will : ¬ ∃ s : S, FreeWill s` | —  |

### `CountermodelNoPerson`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `A` | def | [L515](formal/Logos/HostileSemantics.lean#L515) | `def A : S → Prop → Prop` | —  |
| `Person` | def | [L516](formal/Logos/HostileSemantics.lean#L516) | `def Person : S → Prop` | —  |
| `S` | def | [L514](formal/Logos/HostileSemantics.lean#L514) | `def S : Type` | —  |
| `act_does_not_imply_person` | theorem | [L520](formal/Logos/HostileSemantics.lean#L520) | `theorem act_does_not_imply_person : (∃ s : S, ∃ p : Prop, A s p) ∧ ¬ (∃ s : S, P` | —  |
| `act_occurs` | theorem | [L518](formal/Logos/HostileSemantics.lean#L518) | `theorem act_occurs : ∃ s : S, ∃ p : Prop, A s p` | —  |
| `no_person` | theorem | [L519](formal/Logos/HostileSemantics.lean#L519) | `theorem no_person : ¬ ∃ s : S, Person s` | —  |

### `CountermodelOmniMeaning`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Act` | def | [L1985](formal/Logos/HostileSemantics.lean#L1985) | `def Act (s : S) (p : Prop) : Prop` | —  |
| `Means` | def | [L1984](formal/Logos/HostileSemantics.lean#L1984) | `def Means (_s : S) (_p : Prop) : Prop` | —  |
| `MeansSelects` | def | [L1986](formal/Logos/HostileSemantics.lean#L1986) | `def MeansSelects (s : S) (p q : Prop) : Prop` | —  |
| `S` | def | [L1983](formal/Logos/HostileSemantics.lean#L1983) | `def S : Type` | —  |
| `act_datum_holds` | theorem | [L1989](formal/Logos/HostileSemantics.lean#L1989) | `theorem act_datum_holds : ∃ s : S, ∃ p : Prop, Act s p` | —  |
| `means_does_not_entail_means_selection` | theorem | [L1998](formal/Logos/HostileSemantics.lean#L1998) | `theorem means_does_not_entail_means_selection : (∃ s : S, ∃ p : Prop, Act s p) ∧` | —  |
| `no_means_selection` | theorem | [L1992](formal/Logos/HostileSemantics.lean#L1992) | `theorem no_means_selection : ¬ ∃ s : S, ∃ p q : Prop, MeansSelects s p q` | —  |

### `CountermodelPersonNotNecessary`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `ExistsAt` | def | [L720](formal/Logos/HostileSemantics.lean#L720) | `def ExistsAt (w : World) (_s : Subject) : Prop` | — → Q7.2 |
| `NecessarySubject` | def | [L724](formal/Logos/HostileSemantics.lean#L724) | `def NecessarySubject (s : Subject) : Prop` | —  |
| `NecessitySignature` | structure | [L740](formal/Logos/HostileSemantics.lean#L740) | `structure NecessitySignature where` | —  |
| `Person` | def | [L722](formal/Logos/HostileSemantics.lean#L722) | `def Person (_s : Subject) : Prop` | —  |
| `Subject` | abbrev | [L716](formal/Logos/HostileSemantics.lean#L716) | `abbrev Subject : Type` | —  |
| `World` | abbrev | [L717](formal/Logos/HostileSemantics.lean#L717) | `abbrev World : Type` | —  |
| `no_necessary_subject` | theorem | [L728](formal/Logos/HostileSemantics.lean#L728) | `theorem no_necessary_subject : ¬ ∃ s : Subject, NecessarySubject s` | —  |
| `not_entails_person_necessary` | theorem | [L748](formal/Logos/HostileSemantics.lean#L748) | `theorem not_entails_person_necessary : ¬ (∀ I : NecessitySignature, (∃ s : I.Sub` | —  |
| `person_exists` | theorem | [L726](formal/Logos/HostileSemantics.lean#L726) | `theorem person_exists : ∃ s : Subject, Person s` | —  |
| `person_not_entails_necessary` | theorem | [L734](formal/Logos/HostileSemantics.lean#L734) | `theorem person_not_entails_necessary : (∃ s : Subject, Person s) ∧ ¬ (∃ s : Subj` | —  |

### `CountermodelPluralityWithoutLove`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Loves` | def | [L2396](formal/Logos/HostileSemantics.lean#L2396) | `def Loves (_s _t : Subject) : Prop` | —  |
| `Person` | def | [L2395](formal/Logos/HostileSemantics.lean#L2395) | `def Person (_s : Subject) : Prop` | —  |
| `Subject` | abbrev | [L2394](formal/Logos/HostileSemantics.lean#L2394) | `abbrev Subject : Type` | —  |
| `no_love` | theorem | [L2402](formal/Logos/HostileSemantics.lean#L2402) | `theorem no_love : ¬ ∃ s₁ s₂ : Subject, Loves s₁ s₂` | —  |
| `plurality_not_entails_love` | theorem | [L2407](formal/Logos/HostileSemantics.lean#L2407) | `theorem plurality_not_entails_love : (∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧` | —  |
| `two_persons_exist` | theorem | [L2398](formal/Logos/HostileSemantics.lean#L2398) | `theorem two_persons_exist : ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂` | —  |

### `CountermodelSubjectNecessityNotEntityNecessity`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Entity` | abbrev | [L635](formal/Logos/HostileSemantics.lean#L635) | `abbrev Entity : Type` | —  |
| `EntityExistsAt` | def | [L647](formal/Logos/HostileSemantics.lean#L647) | `def EntityExistsAt (w : World) (_e : Entity) : Prop` | —  |
| `EntityOf` | def | [L639](formal/Logos/HostileSemantics.lean#L639) | `def EntityOf (_s : Subject) : Entity` | —  |
| `NecessaryEntity` | def | [L653](formal/Logos/HostileSemantics.lean#L653) | `def NecessaryEntity (e : Entity) : Prop` | —  |
| `NecessarySubject` | def | [L650](formal/Logos/HostileSemantics.lean#L650) | `def NecessarySubject (s : Subject) : Prop` | —  |
| `NecessityLift` | structure | [L674](formal/Logos/HostileSemantics.lean#L674) | `structure NecessityLift where` | —  |
| `Subject` | abbrev | [L634](formal/Logos/HostileSemantics.lean#L634) | `abbrev Subject : Type` | —  |
| `SubjectExistsAt` | def | [L643](formal/Logos/HostileSemantics.lean#L643) | `def SubjectExistsAt (_w : World) (_s : Subject) : Prop` | —  |
| `World` | abbrev | [L633](formal/Logos/HostileSemantics.lean#L633) | `abbrev World : Type` | —  |
| `necessary_subject_is_necessary` | theorem | [L656](formal/Logos/HostileSemantics.lean#L656) | `theorem necessary_subject_is_necessary : NecessarySubject ()` | —  |
| `no_necessary_entity` | theorem | [L661](formal/Logos/HostileSemantics.lean#L661) | `theorem no_necessary_entity : ¬ ∃ e : Entity, NecessaryEntity e` | —  |
| `not_holds_of_arbitrary_signature` | theorem | [L683](formal/Logos/HostileSemantics.lean#L683) | `theorem not_holds_of_arbitrary_signature : ¬ (∀ (I : NecessityLift), ∀ s : I.Sub` | —  |
| `subject_necessity_not_entails_entity_necessity` | theorem | [L668](formal/Logos/HostileSemantics.lean#L668) | `theorem subject_necessity_not_entails_entity_necessity : (∃ s : Subject, Necessa` | —  |

### `CountermodelSubjectWithoutPerson`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Act` | def | [L489](formal/Logos/HostileSemantics.lean#L489) | `def Act : Entity → Prop → Prop` | —  |
| `Entity` | def | [L488](formal/Logos/HostileSemantics.lean#L488) | `def Entity : Type` | —  |
| `Person` | def | [L491](formal/Logos/HostileSemantics.lean#L491) | `def Person : Entity → Prop` | —  |
| `Subject` | def | [L490](formal/Logos/HostileSemantics.lean#L490) | `def Subject : Entity → Prop` | —  |
| `act_and_subject_without_person` | theorem | [L507](formal/Logos/HostileSemantics.lean#L507) | `theorem act_and_subject_without_person : (∃ s : Entity, ∃ p : Prop, Act s p) ∧ (` | —  |
| `act_occurs` | theorem | [L497](formal/Logos/HostileSemantics.lean#L497) | `theorem act_occurs : ∃ s : Entity, ∃ p : Prop, Act s p` | —  |
| `constitutive_act_holds` | theorem | [L494](formal/Logos/HostileSemantics.lean#L494) | `theorem constitutive_act_holds : ∀ (s : Entity) (p : Prop), Act s p → Subject s` | —  |
| `no_person` | theorem | [L499](formal/Logos/HostileSemantics.lean#L499) | `theorem no_person : ¬ ∃ s : Entity, Person s` | —  |
| `subject_exists` | theorem | [L498](formal/Logos/HostileSemantics.lean#L498) | `theorem subject_exists : ∃ s : Entity, Subject s` | —  |
| `subject_without_person` | theorem | [L502](formal/Logos/HostileSemantics.lean#L502) | `theorem subject_without_person : (∃ s : Entity, Subject s) ∧ ¬ (∃ s : Entity, Pe` | —  |

### `CountermodelVeridicalMeaning`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `ActDatum` | def | [L1210](formal/Logos/HostileSemantics.lean#L1210) | `def ActDatum (I : ActSignature) : Prop` | —  |
| `ActOf` | def | [L1207](formal/Logos/HostileSemantics.lean#L1207) | `def ActOf (I : ActSignature) (s : I.Subject) (p : Prop) : Prop` | —  |
| `ActSignature` | structure | [L1201](formal/Logos/HostileSemantics.lean#L1201) | `structure ActSignature where` | —  |
| `ActTwoSubjects` | def | [L1213](formal/Logos/HostileSemantics.lean#L1213) | `def ActTwoSubjects (I : ActSignature) : Prop` | —  |
| `BoundaryDatum` | def | [L1918](formal/Logos/HostileSemantics.lean#L1918) | `def BoundaryDatum (I : BoundarySignature) : Prop` | —  |
| `BoundaryGenuineChoice` | def | [L1923](formal/Logos/HostileSemantics.lean#L1923) | `def BoundaryGenuineChoice (I : BoundarySignature) : Prop` | —  |
| `BoundarySignature` | structure | [L1905](formal/Logos/HostileSemantics.lean#L1905) | `structure BoundarySignature where` | —  |
| `BoundaryTwoSubjects` | def | [L1928](formal/Logos/HostileSemantics.lean#L1928) | `def BoundaryTwoSubjects (I : BoundarySignature) : Prop` | —  |
| `FullAct` | def | [L1480](formal/Logos/HostileSemantics.lean#L1480) | `def FullAct (I : PreA13FullTheorySignature) (s : I.Subject) (p : Prop) : Prop` | —  |
| `FullChooses` | def | [L1586](formal/Logos/HostileSemantics.lean#L1586) | `def FullChooses (I : PreA13FullTheorySignature) (s : I.Subject) (p q : Prop) : P` | —  |
| `FullContrastiveAgency` | def | [L1594](formal/Logos/HostileSemantics.lean#L1594) | `def FullContrastiveAgency (I : PreA13FullTheorySignature) (s : I.Subject) (p : P` | —  |
| `FullFreeWill` | def | [L1590](formal/Logos/HostileSemantics.lean#L1590) | `def FullFreeWill (I : PreA13FullTheorySignature) (s : I.Subject) : Prop` | —  |
| `FullPerson` | def | [L1483](formal/Logos/HostileSemantics.lean#L1483) | `def FullPerson (I : PreA13FullTheorySignature) (s : I.Subject) : Prop` | —  |
| `GCdatum` | def | [L1138](formal/Logos/HostileSemantics.lean#L1138) | `def GCdatum (I : GenuineChoiceSignature) : Prop` | —  |
| `GenuineChoice` | def | [L1143](formal/Logos/HostileSemantics.lean#L1143) | `def GenuineChoice (I : GenuineChoiceSignature) : Prop` | —  |
| `GenuineChoiceSignature` | structure | [L1134](formal/Logos/HostileSemantics.lean#L1134) | `structure GenuineChoiceSignature where` | —  |
| `ModalOpen` | def | [L1914](formal/Logos/HostileSemantics.lean#L1914) | `def ModalOpen (I : BoundarySignature) : Prop` | —  |
| `PreA13Act` | def | [L1283](formal/Logos/HostileSemantics.lean#L1283) | `def PreA13Act (I : PreA13AgencySignature) (s : I.Subject) (p : Prop) : Prop` | —  |
| `PreA13AgencySignature` | structure | [L1275](formal/Logos/HostileSemantics.lean#L1275) | `structure PreA13AgencySignature where` | —  |
| `PreA13AgencyTheory` | def | [L1303](formal/Logos/HostileSemantics.lean#L1303) | `def PreA13AgencyTheory (I : PreA13AgencySignature) : Prop` | —  |
| `PreA13ChoiceField` | def | [L1397](formal/Logos/HostileSemantics.lean#L1397) | `def PreA13ChoiceField (I : PreA13AgencySignature) (s : I.Subject) (p q : Prop) :` | —  |
| `PreA13Chooses` | def | [L1400](formal/Logos/HostileSemantics.lean#L1400) | `def PreA13Chooses (I : PreA13AgencySignature) (s : I.Subject) (p q : Prop) : Pro` | —  |
| `PreA13Correct` | def | [L1289](formal/Logos/HostileSemantics.lean#L1289) | `def PreA13Correct (I : PreA13AgencySignature) (s : I.Subject) (p : Prop) : Prop` | —  |
| `PreA13Fallible` | def | [L1295](formal/Logos/HostileSemantics.lean#L1295) | `def PreA13Fallible (I : PreA13AgencySignature) (_s : I.Subject) (p : Prop) : Pro` | —  |
| `PreA13FullTheory` | def | [L1498](formal/Logos/HostileSemantics.lean#L1498) | `def PreA13FullTheory (I : PreA13FullTheorySignature) : Prop` | —  |
| `PreA13FullTheorySignature` | structure | [L1466](formal/Logos/HostileSemantics.lean#L1466) | `structure PreA13FullTheorySignature where` | —  |
| `PreA13Incorrect` | def | [L1292](formal/Logos/HostileSemantics.lean#L1292) | `def PreA13Incorrect (I : PreA13AgencySignature) (s : I.Subject) (p : Prop) : Pro` | —  |
| `PreA13Person` | def | [L1286](formal/Logos/HostileSemantics.lean#L1286) | `def PreA13Person (I : PreA13AgencySignature) (s : I.Subject) : Prop` | —  |
| `act_orthogonal_to_contrastive_agency_in_full_theory` | theorem | [L1631](formal/Logos/HostileSemantics.lean#L1631) | `theorem act_orthogonal_to_contrastive_agency_in_full_theory : ¬ (∀ I : PreA13Ful` | —  |
| `act_orthogonal_to_existential_contrastive_agency_in_full_theory` | theorem | [L1641](formal/Logos/HostileSemantics.lean#L1641) | `theorem act_orthogonal_to_existential_contrastive_agency_in_full_theory : ¬ (∀ I` | —  |
| `act_orthogonal_to_freewill_in_full_theory` | theorem | [L1619](formal/Logos/HostileSemantics.lean#L1619) | `theorem act_orthogonal_to_freewill_in_full_theory : ¬ (∀ I : PreA13FullTheorySig` | —  |
| `act_orthogonal_to_genuine_choice_in_full_theory` | theorem | [L1607](formal/Logos/HostileSemantics.lean#L1607) | `theorem act_orthogonal_to_genuine_choice_in_full_theory : ¬ (∀ I : PreA13FullThe` | —  |
| `fullTheoryHostileInstance` | def | [L1521](formal/Logos/HostileSemantics.lean#L1521) | `def fullTheoryHostileInstance : PreA13FullTheorySignature` | —  |
| `fullTheory_holds` | theorem | [L1537](formal/Logos/HostileSemantics.lean#L1537) | `theorem fullTheory_holds : PreA13FullTheory fullTheoryHostileInstance` | —  |
| `hostileAgencyInstance` | def | [L1322](formal/Logos/HostileSemantics.lean#L1322) | `def hostileAgencyInstance : PreA13AgencySignature` | —  |
| `hostileAgencyTheory_holds` | theorem | [L1388](formal/Logos/HostileSemantics.lean#L1388) | `theorem hostileAgencyTheory_holds : PreA13AgencyTheory hostileAgencyInstance` | —  |
| `hostile_act_datum` | theorem | [L1331](formal/Logos/HostileSemantics.lean#L1331) | `theorem hostile_act_datum : ∃ s p, PreA13Act hostileAgencyInstance s p` | —  |
| `hostile_c101` | theorem | [L1373](formal/Logos/HostileSemantics.lean#L1373) | `theorem hostile_c101 : ∀ (s : hostileAgencyInstance.Subject) (p : Prop), PreA13A` | —  |
| `hostile_choice_field_holds` | theorem | [L1414](formal/Logos/HostileSemantics.lean#L1414) | `theorem hostile_choice_field_holds : PreA13ChoiceField hostileAgencyInstance fal` | —  |
| `hostile_choice_field_not_implies_chooses` | theorem | [L1423](formal/Logos/HostileSemantics.lean#L1423) | `theorem hostile_choice_field_not_implies_chooses : PreA13ChoiceField hostileAgen` | —  |
| `hostile_fallibility` | theorem | [L1361](formal/Logos/HostileSemantics.lean#L1361) | `theorem hostile_fallibility : ∃ (s : hostileAgencyInstance.Subject) (p : Prop), ` | —  |
| `hostile_judge_commits` | theorem | [L1351](formal/Logos/HostileSemantics.lean#L1351) | `theorem hostile_judge_commits : ∃ (s : hostileAgencyInstance.Subject) (p q : Pro` | —  |
| `hostile_no_chooses` | theorem | [L1418](formal/Logos/HostileSemantics.lean#L1418) | `theorem hostile_no_chooses : ¬ PreA13Chooses hostileAgencyInstance false True Fa` | —  |
| `hostile_retorsion` | theorem | [L1366](formal/Logos/HostileSemantics.lean#L1366) | `theorem hostile_retorsion : ∀ (speaker : hostileAgencyInstance.Subject), (PreA13` | —  |
| `hostile_right_wrong` | theorem | [L1342](formal/Logos/HostileSemantics.lean#L1342) | `theorem hostile_right_wrong : (¬ ∀ p : Prop, ¬ hostileAgencyInstance.T p) ∧ (¬ ∀` | —  |
| `hostile_semantic_assignment` | theorem | [L1405](formal/Logos/HostileSemantics.lean#L1405) | `theorem hostile_semantic_assignment : hostileAgencyInstance.Means false True ∧ ¬` | —  |
| `hostile_two_persons` | theorem | [L1334](formal/Logos/HostileSemantics.lean#L1334) | `theorem hostile_two_persons : ∃ s₁ s₂ : hostileAgencyInstance.Subject, PreA13Per` | —  |
| `modal_openness_and_plurality_do_not_entail_genuine_choice` | theorem | [L1954](formal/Logos/HostileSemantics.lean#L1954) | `theorem modal_openness_and_plurality_do_not_entail_genuine_choice : ¬ (∀ I : Bou` | —  |
| `modal_openness_does_not_entail_genuine_choice` | theorem | [L1935](formal/Logos/HostileSemantics.lean#L1935) | `theorem modal_openness_does_not_entail_genuine_choice : ¬ (∀ I : BoundarySignatu` | —  |
| `not_entails_act_polarity` | theorem | [L1217](formal/Logos/HostileSemantics.lean#L1217) | `theorem not_entails_act_polarity : ¬ (∀ I : ActSignature, ActDatum I → ∀ (s : I.` | —  |
| `not_entails_act_polarity_from_full_theory` | theorem | [L1563](formal/Logos/HostileSemantics.lean#L1563) | `theorem not_entails_act_polarity_from_full_theory : ¬ (∀ I : PreA13FullTheorySig` | —  |
| `not_entails_act_polarity_from_preA13` | theorem | [L1439](formal/Logos/HostileSemantics.lean#L1439) | `theorem not_entails_act_polarity_from_preA13 : ¬ (∀ I : PreA13AgencySignature, P` | —  |
| `not_entails_act_polarity_with_plurality` | theorem | [L1232](formal/Logos/HostileSemantics.lean#L1232) | `theorem not_entails_act_polarity_with_plurality : ¬ (∀ I : ActSignature, ActDatu` | —  |
| `not_entails_bilateral_intentionality` | theorem | [L1180](formal/Logos/HostileSemantics.lean#L1180) | `theorem not_entails_bilateral_intentionality : ¬ (∀ I : GenuineChoiceSignature, ` | —  |
| `not_entails_bilateral_intentionality_with_plurality` | theorem | [L1189](formal/Logos/HostileSemantics.lean#L1189) | `theorem not_entails_bilateral_intentionality_with_plurality : ¬ (∀ I : GenuineCh` | —  |
| `not_entails_existential_polarity_from_full_theory` | theorem | [L1576](formal/Logos/HostileSemantics.lean#L1576) | `theorem not_entails_existential_polarity_from_full_theory : ¬ (∀ I : PreA13FullT` | —  |
| `not_entails_existential_polarity_from_preA13` | theorem | [L1452](formal/Logos/HostileSemantics.lean#L1452) | `theorem not_entails_existential_polarity_from_preA13 : ¬ (∀ I : PreA13AgencySign` | —  |
| `not_entails_genuine_choice` | theorem | [L1152](formal/Logos/HostileSemantics.lean#L1152) | `theorem not_entails_genuine_choice : ¬ (∀ I : GenuineChoiceSignature, GCdatum I ` | —  |
| `not_entails_genuine_choice_with_plurality` | theorem | [L1164](formal/Logos/HostileSemantics.lean#L1164) | `theorem not_entails_genuine_choice_with_plurality : ¬ (∀ I : GenuineChoiceSignat` | —  |
| `Γ_twoGCSubjects` | def | [L1147](formal/Logos/HostileSemantics.lean#L1147) | `def Γ_twoGCSubjects (I : GenuineChoiceSignature) : Prop` | —  |

### `CountermodelVeridicalMeaning.ActPolaritySeparation`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Act` | def | [L1867](formal/Logos/HostileSemantics.lean#L1867) | `def Act : S → Prop → Prop | S.active, _ => True` | —  |
| `Means` | def | [L1871](formal/Logos/HostileSemantics.lean#L1871) | `def Means : S → Prop → Prop | S.active, _ => True -- active subject has polar me` | —  |
| `S` | inductive | [L1863](formal/Logos/HostileSemantics.lean#L1863) | `inductive S : Type` | —  |
| `act_polarity_holds` | theorem | [L1876](formal/Logos/HostileSemantics.lean#L1876) | `theorem act_polarity_holds : ∀ (s : S) (p : Prop), Act s p → Means s (¬ p)` | —  |
| `act_polarity_strictly_weaker` | theorem | [L1890](formal/Logos/HostileSemantics.lean#L1890) | `theorem act_polarity_strictly_weaker : (∀ (s : S) (p : Prop), Act s p → Means s ` | —  |
| `universal_bilateral_fails` | theorem | [L1883](formal/Logos/HostileSemantics.lean#L1883) | `theorem universal_bilateral_fails : ¬ (∀ (s : S) (p : Prop), Means s p → Means s` | —  |

### `CountermodelVeridicalMeaning.ModelHierarchy.ContrastiveSeparation`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Act` | def | [L1835](formal/Logos/HostileSemantics.lean#L1835) | `def Act (s : S) (p : Form3) : Prop` | —  |
| `Form3` | inductive | [L1809](formal/Logos/HostileSemantics.lean#L1809) | `inductive Form3 : Type` | —  |
| `Incompatible3` | def | [L1814](formal/Logos/HostileSemantics.lean#L1814) | `def Incompatible3 (p q : Form3) : Prop` | —  |
| `Initiates` | def | [L1831](formal/Logos/HostileSemantics.lean#L1831) | `def Initiates (_s : S) (_w _w' : State) : Form3 → Prop | Form3.North => True` | —  |
| `Means` | def | [L1826](formal/Logos/HostileSemantics.lean#L1826) | `def Means (_s : S) : Form3 → Prop | Form3.North => True` | —  |
| `S` | def | [L1822](formal/Logos/HostileSemantics.lean#L1822) | `def S : Type` | —  |
| `State` | def | [L1823](formal/Logos/HostileSemantics.lean#L1823) | `def State : Type` | —  |
| `contrastive_holds` | theorem | [L1838](formal/Logos/HostileSemantics.lean#L1838) | `theorem contrastive_holds : ∀ (s : S) (p : Form3), Act s p → ∃ q : Form3, Means ` | —  |
| `contrastive_strictly_weaker` | theorem | [L1850](formal/Logos/HostileSemantics.lean#L1850) | `theorem contrastive_strictly_weaker : (∀ (s : S) (p : Form3), Act s p → ∃ q : Fo` | —  |
| `negation_meaning_fails` | theorem | [L1848](formal/Logos/HostileSemantics.lean#L1848) | `theorem negation_meaning_fails : ¬ Means () Form3.NotNorth` | —  |

### `CountermodelVeridicalMeaning.ModelHierarchy.ModelM2BranchingInitiation`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Act` | def | [L1704](formal/Logos/HostileSemantics.lean#L1704) | `def Act (s : S) (p : Prop) : Prop` | —  |
| `ChoiceField` | def | [L1705](formal/Logos/HostileSemantics.lean#L1705) | `def ChoiceField (s : S) (p q : Prop) : Prop` | —  |
| `Chooses` | def | [L1706](formal/Logos/HostileSemantics.lean#L1706) | `def Chooses (s : S) (p q : Prop) : Prop` | —  |
| `FreeSubject` | def | [L1708](formal/Logos/HostileSemantics.lean#L1708) | `def FreeSubject (s : S) : Prop` | —  |
| `FreeWill` | def | [L1707](formal/Logos/HostileSemantics.lean#L1707) | `def FreeWill (s : S) : Prop` | —  |
| `Initiates` | def | [L1701](formal/Logos/HostileSemantics.lean#L1701) | `def Initiates (_s : S) (w w' : State) (p : Prop) : Prop` | —  |
| `Means` | def | [L1700](formal/Logos/HostileSemantics.lean#L1700) | `def Means (_s : S) (p : Prop) : Prop` | —  |
| `S` | def | [L1698](formal/Logos/HostileSemantics.lean#L1698) | `def S : Type` | —  |
| `State` | def | [L1699](formal/Logos/HostileSemantics.lean#L1699) | `def State : Type` | —  |
| `choice_field_holds` | theorem | [L1720](formal/Logos/HostileSemantics.lean#L1720) | `theorem choice_field_holds : ∃ s : S, ∃ p q : Prop, ChoiceField s p q` | —  |
| `initiation_branches` | theorem | [L1715](formal/Logos/HostileSemantics.lean#L1715) | `theorem initiation_branches : ∃ s : S, Logos.Initiation.Branches (fun w w' => ∃ ` | —  |
| `m2_diagnostic_separation` | theorem | [L1740](formal/Logos/HostileSemantics.lean#L1740) | `theorem m2_diagnostic_separation : (∃ s : S, ∃ p : Prop, Act s p) ∧ (∃ s : S, Lo` | —  |
| `no_chooses` | theorem | [L1724](formal/Logos/HostileSemantics.lean#L1724) | `theorem no_chooses : ¬ ∃ s : S, ∃ p q : Prop, Chooses s p q` | —  |
| `no_free_subject` | theorem | [L1734](formal/Logos/HostileSemantics.lean#L1734) | `theorem no_free_subject : ¬ ∃ s : S, FreeSubject s` | —  |
| `no_free_will` | theorem | [L1729](formal/Logos/HostileSemantics.lean#L1729) | `theorem no_free_will : ¬ ∃ s : S, FreeWill s` | —  |
| `strong_act_holds` | theorem | [L1711](formal/Logos/HostileSemantics.lean#L1711) | `theorem strong_act_holds : ∃ s : S, ∃ p : Prop, Act s p` | —  |

### `CountermodelVeridicalMeaning.ModelHierarchy.ModelM3ContrastiveAgency`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Act` | def | [L1764](formal/Logos/HostileSemantics.lean#L1764) | `def Act (s : S) (p : Prop) : Prop` | —  |
| `ChoiceField` | def | [L1765](formal/Logos/HostileSemantics.lean#L1765) | `def ChoiceField (s : S) (p q : Prop) : Prop` | —  |
| `Chooses` | def | [L1766](formal/Logos/HostileSemantics.lean#L1766) | `def Chooses (s : S) (p q : Prop) : Prop` | —  |
| `FreeSubject` | def | [L1768](formal/Logos/HostileSemantics.lean#L1768) | `def FreeSubject (s : S) : Prop` | —  |
| `FreeWill` | def | [L1767](formal/Logos/HostileSemantics.lean#L1767) | `def FreeWill (s : S) : Prop` | —  |
| `Initiates` | def | [L1762](formal/Logos/HostileSemantics.lean#L1762) | `def Initiates (_s : S) (_w _w' : State) (_p : Prop) : Prop` | —  |
| `Means` | def | [L1761](formal/Logos/HostileSemantics.lean#L1761) | `def Means (_s : S) (_p : Prop) : Prop` | —  |
| `S` | def | [L1759](formal/Logos/HostileSemantics.lean#L1759) | `def S : Type` | —  |
| `State` | def | [L1760](formal/Logos/HostileSemantics.lean#L1760) | `def State : Type` | —  |
| `act_holds` | theorem | [L1770](formal/Logos/HostileSemantics.lean#L1770) | `theorem act_holds : ∃ s : S, ∃ p : Prop, Act s p` | —  |
| `choice_field_holds` | theorem | [L1773](formal/Logos/HostileSemantics.lean#L1773) | `theorem choice_field_holds : ∃ s : S, ∃ p q : Prop, ChoiceField s p q` | —  |
| `chooses_holds` | theorem | [L1777](formal/Logos/HostileSemantics.lean#L1777) | `theorem chooses_holds : ∃ s : S, ∃ p q : Prop, Chooses s p q` | —  |
| `free_subject_holds` | theorem | [L1785](formal/Logos/HostileSemantics.lean#L1785) | `theorem free_subject_holds : ∃ s : S, FreeSubject s` | —  |
| `free_will_holds` | theorem | [L1781](formal/Logos/HostileSemantics.lean#L1781) | `theorem free_will_holds : ∃ s : S, FreeWill s` | —  |
| `m3_diagnostic_fulfillment` | theorem | [L1790](formal/Logos/HostileSemantics.lean#L1790) | `theorem m3_diagnostic_fulfillment : (∃ s : S, ∃ p : Prop, Act s p) ∧ (∃ s : S, ∃` | —  |

### `CountermodelVeridicalMeaning.Single`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `A` | def | [L803](formal/Logos/HostileSemantics.lean#L803) | `def A (s : S) (p : Prop) : Prop` | —  |
| `Asserts` | def | [L807](formal/Logos/HostileSemantics.lean#L807) | `def Asserts (s : S) (p : Prop) : Prop` | —  |
| `Chooses` | def | [L805](formal/Logos/HostileSemantics.lean#L805) | `def Chooses (s : S) (p q : Prop) : Prop` | —  |
| `DeliberateChoice` | def | [L810](formal/Logos/HostileSemantics.lean#L810) | `def DeliberateChoice (s : S) (p q : Prop) : Prop` | —  |
| `FreeWill` | def | [L806](formal/Logos/HostileSemantics.lean#L806) | `def FreeWill (s : S) : Prop` | —  |
| `Initiates` | def | [L802](formal/Logos/HostileSemantics.lean#L802) | `def Initiates (_s : S) (_w _w' : State) (p : Prop) : Prop` | —  |
| `M` | def | [L801](formal/Logos/HostileSemantics.lean#L801) | `def M (_s : S) (p : Prop) : Prop` | —  |
| `Person` | def | [L804](formal/Logos/HostileSemantics.lean#L804) | `def Person (s : S) : Prop` | —  |
| `S` | def | [L799](formal/Logos/HostileSemantics.lean#L799) | `def S : Type` | —  |
| `Selects` | def | [L808](formal/Logos/HostileSemantics.lean#L808) | `def Selects (s : S) (p q : Prop) : Prop` | —  |
| `State` | def | [L800](formal/Logos/HostileSemantics.lean#L800) | `def State : Type` | —  |
| `act_datum_holds` | theorem | [L813](formal/Logos/HostileSemantics.lean#L813) | `theorem act_datum_holds : ∃ s : S, ∃ p : Prop, A s p` | —  |
| `act_does_not_imply_genuine_choice` | theorem | [L842](formal/Logos/HostileSemantics.lean#L842) | `theorem act_does_not_imply_genuine_choice : (∃ s : S, ∃ p : Prop, A s p) ∧ ¬ (∃ ` | —  |
| `act_polarity_fails` | theorem | [L910](formal/Logos/HostileSemantics.lean#L910) | `theorem act_polarity_fails : ¬ (∀ (s : S) (p : Prop), A s p → M s (¬ p))` | —  |
| `assertion_does_not_imply_rejected_horn_meaning` | theorem | [L887](formal/Logos/HostileSemantics.lean#L887) | `theorem assertion_does_not_imply_rejected_horn_meaning : (∃ s : S, ∃ p : Prop, A` | —  |
| `bilateral_intentionality_fails` | theorem | [L900](formal/Logos/HostileSemantics.lean#L900) | `theorem bilateral_intentionality_fails : ¬ (∀ (s : S) (p : Prop), M s p → M s (¬` | —  |
| `field_holds` | theorem | [L816](formal/Logos/HostileSemantics.lean#L816) | `theorem field_holds : ∃ s : S, ∃ p q : Prop, M s p ∧ Logos.Alternatives.Incompat` | —  |
| `no_deliberate_choice` | theorem | [L828](formal/Logos/HostileSemantics.lean#L828) | `theorem no_deliberate_choice : ¬ ∃ s : S, ∃ p q : Prop, DeliberateChoice s p q` | —  |
| `no_freewill` | theorem | [L832](formal/Logos/HostileSemantics.lean#L832) | `theorem no_freewill : ¬ ∃ s : S, FreeWill s` | —  |
| `no_genuine_choice` | theorem | [L824](formal/Logos/HostileSemantics.lean#L824) | `theorem no_genuine_choice : ¬ ∃ s : S, ∃ p q : Prop, Chooses s p q` | —  |
| `no_rejected_horn` | theorem | [L836](formal/Logos/HostileSemantics.lean#L836) | `theorem no_rejected_horn : ¬ ∃ s : S, ∃ p : Prop, A s p ∧ A s (¬ p)` | —  |
| `selection_does_not_imply_deliberate_choice` | theorem | [L856](formal/Logos/HostileSemantics.lean#L856) | `theorem selection_does_not_imply_deliberate_choice : (∃ s : S, ∃ p q : Prop, Sel` | —  |
| `selection_does_not_imply_freewill` | theorem | [L863](formal/Logos/HostileSemantics.lean#L863) | `theorem selection_does_not_imply_freewill : (∃ s : S, ∃ p q : Prop, Selects s p ` | —  |
| `selection_does_not_imply_genuine_choice` | theorem | [L849](formal/Logos/HostileSemantics.lean#L849) | `theorem selection_does_not_imply_genuine_choice : (∃ s : S, ∃ p q : Prop, Select` | —  |
| `selection_holds` | theorem | [L819](formal/Logos/HostileSemantics.lean#L819) | `theorem selection_holds : ∃ s : S, ∃ p q : Prop, Selects s p q` | —  |
| `selects_does_not_imply_rejected_horn_meaning` | theorem | [L871](formal/Logos/HostileSemantics.lean#L871) | `theorem selects_does_not_imply_rejected_horn_meaning : (∃ s : S, ∃ p : Prop, Sel` | —  |
| `unilateral_act_witness` | theorem | [L906](formal/Logos/HostileSemantics.lean#L906) | `theorem unilateral_act_witness : ∃ s : S, ∃ p : Prop, A s p ∧ ¬ M s (¬ p)` | —  |
| `unilateral_meaning_witness` | theorem | [L896](formal/Logos/HostileSemantics.lean#L896) | `theorem unilateral_meaning_witness : ∃ s : S, ∃ p : Prop, M s p ∧ ¬ M s (¬ p)` | —  |

### `CountermodelVeridicalMeaning.TwoPersons`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `A` | def | [L925](formal/Logos/HostileSemantics.lean#L925) | `def A (s : S) (p : Prop) : Prop` | —  |
| `Asserts` | def | [L936](formal/Logos/HostileSemantics.lean#L936) | `def Asserts (s : S) (p : Prop) : Prop` | —  |
| `Chooses` | def | [L927](formal/Logos/HostileSemantics.lean#L927) | `def Chooses (s : S) (p q : Prop) : Prop` | —  |
| `Correct` | def | [L933](formal/Logos/HostileSemantics.lean#L933) | `def Correct (s : S) (p : Prop) : Prop` | —  |
| `DeliberateChoice` | def | [L939](formal/Logos/HostileSemantics.lean#L939) | `def DeliberateChoice (s : S) (p q : Prop) : Prop` | —  |
| `Doubts` | def | [L941](formal/Logos/HostileSemantics.lean#L941) | `def Doubts (s : S) (p : Prop) : Prop` | —  |
| `Fallible` | def | [L935](formal/Logos/HostileSemantics.lean#L935) | `def Fallible (_s : S) (p : Prop) : Prop` | —  |
| `FreeSubject` | def | [L1069](formal/Logos/HostileSemantics.lean#L1069) | `def FreeSubject (s : S) : Prop` | —  |
| `FreeWill` | def | [L928](formal/Logos/HostileSemantics.lean#L928) | `def FreeWill (s : S) : Prop` | —  |
| `Incorrect` | def | [L934](formal/Logos/HostileSemantics.lean#L934) | `def Incorrect (s : S) (p : Prop) : Prop` | —  |
| `Initiates` | def | [L924](formal/Logos/HostileSemantics.lean#L924) | `def Initiates (_s : S) (_w _w' : State) (p : Prop) : Prop` | —  |
| `IsFalse` | def | [L932](formal/Logos/HostileSemantics.lean#L932) | `def IsFalse (p : Prop) : Prop` | —  |
| `M` | def | [L923](formal/Logos/HostileSemantics.lean#L923) | `def M (_s : S) (p : Prop) : Prop` | —  |
| `NoAct` | def | [L1063](formal/Logos/HostileSemantics.lean#L1063) | `def NoAct : Prop` | —  |
| `Person` | def | [L926](formal/Logos/HostileSemantics.lean#L926) | `def Person (s : S) : Prop` | —  |
| `S` | def | [L921](formal/Logos/HostileSemantics.lean#L921) | `def S : Type` | —  |
| `Selects` | def | [L937](formal/Logos/HostileSemantics.lean#L937) | `def Selects (s : S) (p q : Prop) : Prop` | —  |
| `State` | def | [L922](formal/Logos/HostileSemantics.lean#L922) | `def State : Type` | —  |
| `T` | def | [L931](formal/Logos/HostileSemantics.lean#L931) | `def T (p : Prop) : Prop` | —  |
| `act_datum_holds` | theorem | [L943](formal/Logos/HostileSemantics.lean#L943) | `theorem act_datum_holds : ∃ s : S, ∃ p : Prop, A s p` | —  |
| `act_does_not_imply_doubt` | theorem | [L1033](formal/Logos/HostileSemantics.lean#L1033) | `theorem act_does_not_imply_doubt : (∃ s : S, ∃ p : Prop, A s p) ∧ ¬ (∃ s : S, ∃ ` | —  |
| `act_polarity_fails` | theorem | [L1110](formal/Logos/HostileSemantics.lean#L1110) | `theorem act_polarity_fails : ¬ (∀ (s : S) (p : Prop), A s p → M s (¬ p))` | —  |
| `assertion_does_not_imply_rejected_horn_meaning` | theorem | [L995](formal/Logos/HostileSemantics.lean#L995) | `theorem assertion_does_not_imply_rejected_horn_meaning : (∃ s : S, ∃ p : Prop, A` | —  |
| `assertion_holds` | theorem | [L946](formal/Logos/HostileSemantics.lean#L946) | `theorem assertion_holds : ∃ s : S, ∃ p : Prop, Asserts s p` | —  |
| `asserts_does_not_imply_doubt` | theorem | [L1039](formal/Logos/HostileSemantics.lean#L1039) | `theorem asserts_does_not_imply_doubt : (∃ s : S, ∃ p : Prop, Asserts s p) ∧ ¬ (∃` | —  |
| `bilateral_intentionality_fails` | theorem | [L1088](formal/Logos/HostileSemantics.lean#L1088) | `theorem bilateral_intentionality_fails : ¬ (∀ (s : S) (p : Prop), M s p → M s (¬` | —  |
| `fallibility_holds` | theorem | [L971](formal/Logos/HostileSemantics.lean#L971) | `theorem fallibility_holds : ∃ (s : S) (p : Prop), Fallible s p ∧ IsFalse p` | —  |
| `full_fragment_with_unilateral_act` | theorem | [L1118](formal/Logos/HostileSemantics.lean#L1118) | `theorem full_fragment_with_unilateral_act : (∃ s : S, ∃ p : Prop, A s p) ∧ (∃ s₁` | —  |
| `full_fragment_with_unilateral_meaning` | theorem | [L1095](formal/Logos/HostileSemantics.lean#L1095) | `theorem full_fragment_with_unilateral_meaning : (∃ s : S, ∃ p : Prop, A s p) ∧ (` | —  |
| `full_fragment_without_deliberate_resource` | theorem | [L1018](formal/Logos/HostileSemantics.lean#L1018) | `theorem full_fragment_without_deliberate_resource : (∃ s : S, ∃ p : Prop, Assert` | —  |
| `full_fragment_without_doubt` | theorem | [L1053](formal/Logos/HostileSemantics.lean#L1053) | `theorem full_fragment_without_doubt : (∃ s : S, ∃ p : Prop, Asserts s p) ∧ (∃ s₁` | —  |
| `full_fragment_without_genuine_choice` | theorem | [L1005](formal/Logos/HostileSemantics.lean#L1005) | `theorem full_fragment_without_genuine_choice : (∃ s : S, ∃ p : Prop, A s p) ∧ (∃` | —  |
| `judge_commits_holds` | theorem | [L963](formal/Logos/HostileSemantics.lean#L963) | `theorem judge_commits_holds : ∃ (s : S) (p q : Prop), A s p ∧ (Correct s p ∨ Inc` | —  |
| `judgment_does_not_imply_doubt` | theorem | [L1045](formal/Logos/HostileSemantics.lean#L1045) | `theorem judgment_does_not_imply_doubt : (∃ (s : S) (p q : Prop), A s p ∧ (Correc` | —  |
| `noAct_selfRefutes` | theorem | [L1065](formal/Logos/HostileSemantics.lean#L1065) | `theorem noAct_selfRefutes (speaker : S) : Asserts speaker NoAct → False` | —  |
| `no_deliberate_choice` | theorem | [L986](formal/Logos/HostileSemantics.lean#L986) | `theorem no_deliberate_choice : ¬ ∃ s : S, ∃ p q : Prop, DeliberateChoice s p q` | —  |
| `no_deliberate_resource` | theorem | [L990](formal/Logos/HostileSemantics.lean#L990) | `theorem no_deliberate_resource : ¬ ∃ s : S, ∃ p : Prop, Asserts s p ∧ M s (¬ p)` | —  |
| `no_doubt` | theorem | [L1028](formal/Logos/HostileSemantics.lean#L1028) | `theorem no_doubt : ¬ ∃ s : S, ∃ p : Prop, Doubts s p` | —  |
| `no_genuine_choice` | theorem | [L978](formal/Logos/HostileSemantics.lean#L978) | `theorem no_genuine_choice : ¬ ∃ s : S, ∃ p q : Prop, Chooses s p q` | —  |
| `no_rejected_horn` | theorem | [L982](formal/Logos/HostileSemantics.lean#L982) | `theorem no_rejected_horn : ¬ ∃ s : S, ∃ p : Prop, A s p ∧ A s (¬ p)` | —  |
| `person_does_not_imply_freeSubject` | theorem | [L1073](formal/Logos/HostileSemantics.lean#L1073) | `theorem person_does_not_imply_freeSubject : (∃ s : S, Person s) ∧ ¬ (∃ s : S, Fr` | —  |
| `retorsion_does_not_imply_doubt` | theorem | [L1078](formal/Logos/HostileSemantics.lean#L1078) | `theorem retorsion_does_not_imply_doubt : (∀ speaker : S, Asserts speaker NoAct →` | —  |
| `rightWrong_holds` | theorem | [L956](formal/Logos/HostileSemantics.lean#L956) | `theorem rightWrong_holds : (¬ (∀ p : Prop, ¬ T p)) ∧ (¬ (∀ p : Prop, T p))` | —  |
| `two_persons_exist` | theorem | [L949](formal/Logos/HostileSemantics.lean#L949) | `theorem two_persons_exist : ∃ s₁ s₂ : S, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂` | —  |
| `unilateral_act_witness` | theorem | [L1106](formal/Logos/HostileSemantics.lean#L1106) | `theorem unilateral_act_witness : ∃ s : S, ∃ p : Prop, A s p ∧ ¬ M s (¬ p)` | —  |
| `unilateral_meaning_witness` | theorem | [L1084](formal/Logos/HostileSemantics.lean#L1084) | `theorem unilateral_meaning_witness : ∃ s : S, ∃ p : Prop, M s p ∧ ¬ M s (¬ p)` | —  |

### `CountermodelWeakActWithoutMeaning`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Act` | def | [L397](formal/Logos/HostileSemantics.lean#L397) | `def Act (s : Entity) (p : Prop) : Prop` | —  |
| `Entity` | def | [L392](formal/Logos/HostileSemantics.lean#L392) | `def Entity : Type` | —  |
| `Initiates` | def | [L395](formal/Logos/HostileSemantics.lean#L395) | `def Initiates : Entity → State → State → Prop → Prop` | —  |
| `Means` | def | [L396](formal/Logos/HostileSemantics.lean#L396) | `def Means : Entity → Prop → Prop` | —  |
| `State` | def | [L393](formal/Logos/HostileSemantics.lean#L393) | `def State : Type` | —  |
| `act` | def | [L394](formal/Logos/HostileSemantics.lean#L394) | `def act : Entity → Prop → Prop` | —  |
| `initiates_does_not_imply_act` | theorem | [L413](formal/Logos/HostileSemantics.lean#L413) | `theorem initiates_does_not_imply_act : (∃ s : Entity, ∃ p : Prop, ∃ w w' : State` | —  |
| `initiates_does_not_imply_means` | theorem | [L407](formal/Logos/HostileSemantics.lean#L407) | `theorem initiates_does_not_imply_means : (∃ s : Entity, ∃ p : Prop, ∃ w w' : Sta` | —  |
| `initiates_does_not_imply_negation_meaning` | theorem | [L423](formal/Logos/HostileSemantics.lean#L423) | `theorem initiates_does_not_imply_negation_meaning : ∃ (S State : Type) (Init : S` | —  |
| `initiation_occurs` | theorem | [L401](formal/Logos/HostileSemantics.lean#L401) | `theorem initiation_occurs : ∃ s : Entity, ∃ p : Prop, ∃ w w' : State, Initiates ` | —  |
| `no_meaning` | theorem | [L403](formal/Logos/HostileSemantics.lean#L403) | `theorem no_meaning : ¬ ∃ s : Entity, ∃ p : Prop, Means s p` | —  |
| `no_strong_act` | theorem | [L404](formal/Logos/HostileSemantics.lean#L404) | `theorem no_strong_act : ¬ ∃ s : Entity, ∃ p : Prop, Act s p` | —  |
| `not_entails_strong_act` | theorem | [L440](formal/Logos/HostileSemantics.lean#L440) | `theorem not_entails_strong_act : ¬ (∀ (I_act : Entity → Prop → Prop) (I_Means : ` | —  |
| `weak_act_occurs` | theorem | [L400](formal/Logos/HostileSemantics.lean#L400) | `theorem weak_act_occurs : ∃ s : Entity, ∃ p : Prop, act s p` | —  |
| `weak_act_without_meaning` | theorem | [L434](formal/Logos/HostileSemantics.lean#L434) | `theorem weak_act_without_meaning : (∃ s : Entity, ∃ p : Prop, act s p) ∧ ¬ (∃ s ` | —  |

### `CountermodelWorldwiseTruthmaking`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Entity` | abbrev | [L595](formal/Logos/HostileSemantics.lean#L595) | `abbrev Entity : Type` | —  |
| `ExistsAt` | def | [L597](formal/Logos/HostileSemantics.lean#L597) | `def ExistsAt (w : World) (e : Entity) : Prop` | —  |
| `Ground` | def | [L598](formal/Logos/HostileSemantics.lean#L598) | `def Ground (_e : Entity) (_φ : Unit) : Prop` | —  |
| `World` | abbrev | [L594](formal/Logos/HostileSemantics.lean#L594) | `abbrev World : Type` | —  |
| `no_uniform_ground` | theorem | [L604](formal/Logos/HostileSemantics.lean#L604) | `theorem no_uniform_ground : ¬ ∃ e : Entity, ∀ w : World, ExistsAt w e ∧ Ground e` | —  |
| `worldwise_not_entails_uniform_ground` | theorem | [L612](formal/Logos/HostileSemantics.lean#L612) | `theorem worldwise_not_entails_uniform_ground : (∀ w : World, ∃ e : Entity, Exist` | —  |
| `worldwise_truthmaking` | theorem | [L600](formal/Logos/HostileSemantics.lean#L600) | `theorem worldwise_truthmaking : ∀ w : World, ∃ e : Entity, ExistsAt w e ∧ Ground` | —  |

### `DeeperSemanticRoutes`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `ActionIndividuationSignature` | structure | [L2502](formal/Logos/HostileSemantics.lean#L2502) | `structure ActionIndividuationSignature extends PreA13FullTheorySignature where` | —  |
| `FunctionalSelects` | def | [L2651](formal/Logos/HostileSemantics.lean#L2651) | `def FunctionalSelects (I : PreA13FullTheorySignature) (s : I.Subject) (p q : Pro` | —  |
| `ReasonResponsiveSignature` | structure | [L2469](formal/Logos/HostileSemantics.lean#L2469) | `structure ReasonResponsiveSignature extends PreA13FullTheorySignature where` | —  |
| `RelationalAct` | def | [L2626](formal/Logos/HostileSemantics.lean#L2626) | `def RelationalAct (I : PreA13FullTheorySignature) (s : I.Subject) (p q : Prop) :` | —  |
| `RepresentationLayerSignature` | structure | [L2534](formal/Logos/HostileSemantics.lean#L2534) | `structure RepresentationLayerSignature extends PreA13FullTheorySignature where` | —  |
| `TeleologicalSignature` | structure | [L2436](formal/Logos/HostileSemantics.lean#L2436) | `structure TeleologicalSignature extends PreA13FullTheorySignature where` | —  |
| `action_individuation_not_entails_contrastive_agency` | theorem | [L2514](formal/Logos/HostileSemantics.lean#L2514) | `theorem action_individuation_not_entails_contrastive_agency : ¬ (∀ I : ActionInd` | —  |
| `authors_not_entails_rejected_horn_meaning` | theorem | [L2681](formal/Logos/HostileSemantics.lean#L2681) | `theorem authors_not_entails_rejected_horn_meaning : ¬ (∀ (s : Single.S) (p q : P` | —  |
| `contrastive_agency_independent_in_full_theory` | theorem | [L2614](formal/Logos/HostileSemantics.lean#L2614) | `theorem contrastive_agency_independent_in_full_theory : ¬ (∀ I : PreA13FullTheor` | —  |
| `counterfactual_branching_not_entails_means` | theorem | [L2567](formal/Logos/HostileSemantics.lean#L2567) | `theorem counterfactual_branching_not_entails_means : ¬ (∀ (s : ModelHierarchy.Mo` | —  |
| `functional_selection_not_entails_deliberate_choice` | theorem | [L2658](formal/Logos/HostileSemantics.lean#L2658) | `theorem functional_selection_not_entails_deliberate_choice : ¬ (∀ (s : Countermo` | —  |
| `hostileActionIndividuationInstance` | def | [L2506](formal/Logos/HostileSemantics.lean#L2506) | `def hostileActionIndividuationInstance : ActionIndividuationSignature` | —  |
| `hostileReasonResponsiveInstance` | def | [L2473](formal/Logos/HostileSemantics.lean#L2473) | `def hostileReasonResponsiveInstance : ReasonResponsiveSignature` | —  |
| `hostileRepresentationLayerInstance` | def | [L2538](formal/Logos/HostileSemantics.lean#L2538) | `def hostileRepresentationLayerInstance : RepresentationLayerSignature` | —  |
| `hostileTeleologicalInstance` | def | [L2440](formal/Logos/HostileSemantics.lean#L2440) | `def hostileTeleologicalInstance : TeleologicalSignature` | —  |
| `nonfactive_representation_not_entails_contrastive_agency` | theorem | [L2546](formal/Logos/HostileSemantics.lean#L2546) | `theorem nonfactive_representation_not_entails_contrastive_agency : ¬ (∀ I : Repr` | —  |
| `reason_responsiveness_not_entails_contrastive_agency` | theorem | [L2481](formal/Logos/HostileSemantics.lean#L2481) | `theorem reason_responsiveness_not_entails_contrastive_agency : ¬ (∀ I : ReasonRe` | —  |
| `relational_act_not_entails_alternative_meaning` | theorem | [L2631](formal/Logos/HostileSemantics.lean#L2631) | `theorem relational_act_not_entails_alternative_meaning : ¬ (∀ I : PreA13FullTheo` | —  |
| `selection_not_entails_rejected_horn_meaning` | theorem | [L2594](formal/Logos/HostileSemantics.lean#L2594) | `theorem selection_not_entails_rejected_horn_meaning : ¬ (∀ (s : Single.S) (p q :` | —  |
| `teleology_not_entails_contrastive_agency` | theorem | [L2448](formal/Logos/HostileSemantics.lean#L2448) | `theorem teleology_not_entails_contrastive_agency : ¬ (∀ I : TeleologicalSignatur` | —  |

### `DeeperSemanticRoutes.ContemplationWithoutActionModel`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Act` | def | [L2706](formal/Logos/HostileSemantics.lean#L2706) | `def Act (s : Subject) (p : Prop) : Prop` | —  |
| `Chooses` | def | [L2707](formal/Logos/HostileSemantics.lean#L2707) | `def Chooses (s : Subject) (p q : Prop) : Prop` | —  |
| `Initiates` | def | [L2705](formal/Logos/HostileSemantics.lean#L2705) | `def Initiates (_s : Subject) (_w _w' : State) (_p : Prop) : Prop` | —  |
| `Means` | def | [L2704](formal/Logos/HostileSemantics.lean#L2704) | `def Means (_s : Subject) (_p : Prop) : Prop` | —  |
| `State` | def | [L2703](formal/Logos/HostileSemantics.lean#L2703) | `def State : Type` | —  |
| `Subject` | def | [L2702](formal/Logos/HostileSemantics.lean#L2702) | `def Subject : Type` | —  |
| `choice_witness_without_action` | theorem | [L2741](formal/Logos/HostileSemantics.lean#L2741) | `theorem choice_witness_without_action : ∃ s : Subject, ∃ p q : Prop, Chooses s p` | —  |
| `contemplation_holds` | theorem | [L2709](formal/Logos/HostileSemantics.lean#L2709) | `theorem contemplation_holds : ∃ s : Subject, ∃ p q : Prop, Chooses s p q` | —  |
| `contemplation_without_action` | theorem | [L2716](formal/Logos/HostileSemantics.lean#L2716) | `theorem contemplation_without_action : (∃ s : Subject, ∃ p q : Prop, Chooses s p` | —  |
| `existential_reverse_a14_refuted` | theorem | [L2733](formal/Logos/HostileSemantics.lean#L2733) | `theorem existential_reverse_a14_refuted : ¬ ((∃ s : Subject, ∃ p q : Prop, Choos` | —  |
| `no_action` | theorem | [L2712](formal/Logos/HostileSemantics.lean#L2712) | `theorem no_action : ¬ ∃ s : Subject, ∃ p : Prop, Act s p` | —  |
| `universal_reverse_a14_refuted` | theorem | [L2723](formal/Logos/HostileSemantics.lean#L2723) | `theorem universal_reverse_a14_refuted : ¬ (∀ (s : Subject) (p : Prop), (∃ q : Pr` | —  |

### `DeeperSemanticRoutes.DelusionalSelfChoiceModel`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Act` | def | [L2825](formal/Logos/HostileSemantics.lean#L2825) | `def Act (s : Subject) (p : Prop) : Prop` | —  |
| `Chooses` | def | [L2826](formal/Logos/HostileSemantics.lean#L2826) | `def Chooses (_s : Subject) (_p _q : Prop) : Prop` | —  |
| `Initiates` | def | [L2824](formal/Logos/HostileSemantics.lean#L2824) | `def Initiates (_s : Subject) (_w _w' : State) (_p : Prop) : Prop` | —  |
| `Means` | def | [L2823](formal/Logos/HostileSemantics.lean#L2823) | `def Means (_s : Subject) (_p : Prop) : Prop` | —  |
| `SelfAssertedChoice` | def | [L2828](formal/Logos/HostileSemantics.lean#L2828) | `def SelfAssertedChoice (s : Subject) (p : Prop) : Prop` | —  |
| `State` | def | [L2822](formal/Logos/HostileSemantics.lean#L2822) | `def State : Type` | —  |
| `Subject` | def | [L2821](formal/Logos/HostileSemantics.lean#L2821) | `def Subject : Type` | —  |
| `act_delusional_choice` | theorem | [L2845](formal/Logos/HostileSemantics.lean#L2845) | `theorem act_delusional_choice : Act () False` | —  |
| `delusional_choice_consistent` | theorem | [L2850](formal/Logos/HostileSemantics.lean#L2850) | `theorem delusional_choice_consistent : ∃ s : Subject, ∃ p : Prop, Act s p ∧ Self` | —  |
| `nonfactive_self_choice_not_derives_choice` | theorem | [L2856](formal/Logos/HostileSemantics.lean#L2856) | `theorem nonfactive_self_choice_not_derives_choice : ¬ (∀ (s : Subject) (p : Prop` | —  |
| `self_choice_equiv` | theorem | [L2836](formal/Logos/HostileSemantics.lean#L2836) | `theorem self_choice_equiv : SelfAssertedChoice () False` | —  |
| `self_choice_prop_false` | theorem | [L2832](formal/Logos/HostileSemantics.lean#L2832) | `theorem self_choice_prop_false : ¬ ∃ q : Prop, Chooses () False q` | —  |

### `DeeperSemanticRoutes.ExistentialChoiceSeparationModel`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Act` | def | [L2902](formal/Logos/HostileSemantics.lean#L2902) | `def Act (s : Subject) (p : Prop) : Prop` | —  |
| `Chooses` | def | [L2905](formal/Logos/HostileSemantics.lean#L2905) | `def Chooses (s : Subject) (p q : Prop) : Prop` | —  |
| `ExistentialA14` | def | [L2911](formal/Logos/HostileSemantics.lean#L2911) | `def ExistentialA14 : Prop` | —  |
| `Initiates` | def | [L2900](formal/Logos/HostileSemantics.lean#L2900) | `def Initiates (_s : Subject) (_w _w' : State) (_p : Prop) : Prop` | —  |
| `Means` | def | [L2896](formal/Logos/HostileSemantics.lean#L2896) | `def Means : Subject → Prop → Prop | Subject.choiceUser, _ => True` | —  |
| `State` | def | [L2894](formal/Logos/HostileSemantics.lean#L2894) | `def State : Type` | —  |
| `Subject` | inductive | [L2890](formal/Logos/HostileSemantics.lean#L2890) | `inductive Subject : Type` | —  |
| `UniversalA14` | def | [L2908](formal/Logos/HostileSemantics.lean#L2908) | `def UniversalA14 : Prop` | —  |
| `act_choiceUser` | theorem | [L2915](formal/Logos/HostileSemantics.lean#L2915) | `theorem act_choiceUser : Act Subject.choiceUser True` | —  |
| `act_unilateral` | theorem | [L2919](formal/Logos/HostileSemantics.lean#L2919) | `theorem act_unilateral : Act Subject.unilateral True` | —  |
| `chooses_choiceUser` | theorem | [L2923](formal/Logos/HostileSemantics.lean#L2923) | `theorem chooses_choiceUser : Chooses Subject.choiceUser True False` | —  |
| `existential_a14_holds` | theorem | [L2935](formal/Logos/HostileSemantics.lean#L2935) | `theorem existential_a14_holds : ExistentialA14` | —  |
| `existential_not_entails_universal` | theorem | [L2950](formal/Logos/HostileSemantics.lean#L2950) | `theorem existential_not_entails_universal : ¬ (ExistentialA14 → UniversalA14)` | —  |
| `some_act` | theorem | [L2927](formal/Logos/HostileSemantics.lean#L2927) | `theorem some_act : ∃ s : Subject, ∃ p : Prop, Act s p` | —  |
| `some_choice` | theorem | [L2931](formal/Logos/HostileSemantics.lean#L2931) | `theorem some_choice : ∃ s : Subject, ∃ p q : Prop, Chooses s p q` | —  |
| `universal_a14_fails` | theorem | [L2939](formal/Logos/HostileSemantics.lean#L2939) | `theorem universal_a14_fails : ¬ UniversalA14` | —  |

### `DeeperSemanticRoutes.ExpressivityBoundary`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `BlindFormula` | inductive | [L3280](formal/Logos/HostileSemantics.lean#L3280) | `inductive BlindFormula (Subject State Entity : Type) : Type` | —  |
| `blind_formula_collapse_invariant` | theorem | [L3309](formal/Logos/HostileSemantics.lean#L3309) | `theorem blind_formula_collapse_invariant (I : PreA13FullTheorySignature) (φ : Bl` | —  |
| `choiceWitnessModel` | def | [L3339](formal/Logos/HostileSemantics.lean#L3339) | `def choiceWitnessModel : PreA13FullTheorySignature` | —  |
| `choiceWitnessModel_has_choice` | theorem | [L3355](formal/Logos/HostileSemantics.lean#L3355) | `theorem choiceWitnessModel_has_choice : FullChooses choiceWitnessModel true True` | —  |
| `eval` | def | [L3293](formal/Logos/HostileSemantics.lean#L3293) | `def eval (I : PreA13FullTheorySignature) : BlindFormula I.Subject I.State I.Enti` | —  |
| `no_blind_formula_defines_choice` | theorem | [L3361](formal/Logos/HostileSemantics.lean#L3361) | `theorem no_blind_formula_defines_choice : ¬ ∃ (φ : BlindFormula Bool Unit Unit),` | —  |
| `no_blind_formula_defines_freeWill` | theorem | [L3376](formal/Logos/HostileSemantics.lean#L3376) | `theorem no_blind_formula_defines_freeWill : ¬ ∃ (φ : BlindFormula Bool Unit Unit` | —  |

### `DeeperSemanticRoutes.ExpressivityBoundary.OntologyHardeningCountermodels.AtomicVsFormulaTruthmakerModel`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Ent` | abbrev | [L3548](formal/Logos/HostileSemantics.lean#L3548) | `abbrev Ent : Type` | —  |
| `FormM` | inductive | [L3544](formal/Logos/HostileSemantics.lean#L3544) | `inductive FormM : Type` | —  |
| `Ground` | def | [L3550](formal/Logos/HostileSemantics.lean#L3550) | `def Ground (e : Ent) : FormM → Prop | FormM.atom n => e = n` | —  |
| `atomic_grounded` | theorem | [L3554](formal/Logos/HostileSemantics.lean#L3554) | `theorem atomic_grounded (n : Nat) : ∃ e : Ent, Ground e (FormM.atom n)` | —  |
| `compound_not_grounded` | theorem | [L3557](formal/Logos/HostileSemantics.lean#L3557) | `theorem compound_not_grounded (p q : FormM) : ¬ ∃ e : Ent, Ground e (FormM.disj ` | —  |

### `DeeperSemanticRoutes.ExpressivityBoundary.OntologyHardeningCountermodels.ContingentAgencyModel`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Act` | def | [L3416](formal/Logos/HostileSemantics.lean#L3416) | `def Act (_s : Subj) (_p : Prop) : Prop` | —  |
| `Ent` | abbrev | [L3414](formal/Logos/HostileSemantics.lean#L3414) | `abbrev Ent : Type` | —  |
| `EntityExistsAt` | def | [L3423](formal/Logos/HostileSemantics.lean#L3423) | `def EntityExistsAt (w : World2) (_e : Ent) : Prop` | —  |
| `NecessaryEntity` | def | [L3428](formal/Logos/HostileSemantics.lean#L3428) | `def NecessaryEntity (e : Ent) : Prop` | —  |
| `NecessarySubject` | def | [L3422](formal/Logos/HostileSemantics.lean#L3422) | `def NecessarySubject (s : Subj) : Prop` | —  |
| `Subj` | abbrev | [L3413](formal/Logos/HostileSemantics.lean#L3413) | `abbrev Subj : Type` | —  |
| `SubjectExistsAt` | def | [L3417](formal/Logos/HostileSemantics.lean#L3417) | `def SubjectExistsAt (w : World2) (_s : Subj) : Prop` | —  |
| `World2` | inductive | [L3409](formal/Logos/HostileSemantics.lean#L3409) | `inductive World2 : Type` | —  |
| `act_not_entails_necessary_entity` | theorem | [L3451](formal/Logos/HostileSemantics.lean#L3451) | `theorem act_not_entails_necessary_entity : (∃ s : Subj, ∃ p : Prop, Act s p) ∧ ¬` | —  |
| `act_not_entails_necessary_subject` | theorem | [L3440](formal/Logos/HostileSemantics.lean#L3440) | `theorem act_not_entails_necessary_subject : (∃ s : Subj, ∃ p : Prop, Act s p) ∧ ` | —  |
| `act_occurs` | theorem | [L3430](formal/Logos/HostileSemantics.lean#L3430) | `theorem act_occurs : ∃ s : Subj, ∃ p : Prop, Act s p` | —  |
| `entity_not_necessary` | theorem | [L3444](formal/Logos/HostileSemantics.lean#L3444) | `theorem entity_not_necessary : ¬ ∀ e : Ent, NecessaryEntity e` | —  |
| `subject_not_necessary` | theorem | [L3433](formal/Logos/HostileSemantics.lean#L3433) | `theorem subject_not_necessary : ¬ ∀ s : Subj, NecessarySubject s` | —  |

### `DeeperSemanticRoutes.ExpressivityBoundary.OntologyHardeningCountermodels.DisconnectedPluralityModel`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Affects` | def | [L3493](formal/Logos/HostileSemantics.lean#L3493) | `def Affects (_s _t : Subj) : Prop` | —  |
| `Chooses` | def | [L3497](formal/Logos/HostileSemantics.lean#L3497) | `def Chooses (_s : Subj) (_p _q : Prop) : Prop` | —  |
| `FreeWill` | def | [L3498](formal/Logos/HostileSemantics.lean#L3498) | `def FreeWill (_s : Subj) : Prop` | —  |
| `Harms` | def | [L3495](formal/Logos/HostileSemantics.lean#L3495) | `def Harms (_s _t : Subj) : Prop` | —  |
| `Helps` | def | [L3494](formal/Logos/HostileSemantics.lean#L3494) | `def Helps (_s _t : Subj) : Prop` | —  |
| `Loves` | def | [L3496](formal/Logos/HostileSemantics.lean#L3496) | `def Loves (s t : Subj) : Prop` | —  |
| `Person` | def | [L3492](formal/Logos/HostileSemantics.lean#L3492) | `def Person (_s : Subj) : Prop` | —  |
| `Subj` | abbrev | [L3490](formal/Logos/HostileSemantics.lean#L3490) | `abbrev Subj : Type` | —  |
| `freewill_and_plurality_not_entails_love` | theorem | [L3531](formal/Logos/HostileSemantics.lean#L3531) | `theorem freewill_and_plurality_not_entails_love : (∃ s₁ s₂ : Subj, Person s₁ ∧ P` | —  |
| `no_affects` | theorem | [L3503](formal/Logos/HostileSemantics.lean#L3503) | `theorem no_affects : ¬ ∃ s₁ s₂ : Subj, Affects s₁ s₂` | —  |
| `no_helps` | theorem | [L3506](formal/Logos/HostileSemantics.lean#L3506) | `theorem no_helps : ¬ ∃ s₁ s₂ : Subj, Helps s₁ s₂` | —  |
| `no_love` | theorem | [L3509](formal/Logos/HostileSemantics.lean#L3509) | `theorem no_love : ¬ ∃ s₁ s₂ : Subj, Loves s₁ s₂` | —  |
| `plurality_not_entails_affects` | theorem | [L3513](formal/Logos/HostileSemantics.lean#L3513) | `theorem plurality_not_entails_affects : (∃ s₁ s₂ : Subj, Person s₁ ∧ Person s₂ ∧` | —  |
| `plurality_not_entails_helps` | theorem | [L3519](formal/Logos/HostileSemantics.lean#L3519) | `theorem plurality_not_entails_helps : (∃ s₁ s₂ : Subj, Person s₁ ∧ Person s₂ ∧ s` | —  |
| `plurality_not_entails_love` | theorem | [L3525](formal/Logos/HostileSemantics.lean#L3525) | `theorem plurality_not_entails_love : (∃ s₁ s₂ : Subj, Person s₁ ∧ Person s₂ ∧ s₁` | —  |
| `two_persons_exist` | theorem | [L3500](formal/Logos/HostileSemantics.lean#L3500) | `theorem two_persons_exist : ∃ s₁ s₂ : Subj, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂` | —  |

### `DeeperSemanticRoutes.ExpressivityBoundary.OntologyHardeningCountermodels.PersonhoodAgencySeparation`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `FreeSubject` | def | [L3467](formal/Logos/HostileSemantics.lean#L3467) | `def FreeSubject (s : Subj) : Prop` | —  |
| `Person` | def | [L3465](formal/Logos/HostileSemantics.lean#L3465) | `def Person (s : Subj) : Prop` | —  |
| `Subj` | abbrev | [L3462](formal/Logos/HostileSemantics.lean#L3462) | `abbrev Subj : Type` | —  |
| `freeSubject_not_entails_person` | theorem | [L3476](formal/Logos/HostileSemantics.lean#L3476) | `theorem freeSubject_not_entails_person : (∃ s : Subj, FreeSubject s) ∧ ¬ (∀ s : ` | —  |
| `person_not_entails_freeSubject` | theorem | [L3469](formal/Logos/HostileSemantics.lean#L3469) | `theorem person_not_entails_freeSubject : (∃ s : Subj, Person s) ∧ ¬ (∀ s : Subj,` | —  |

### `DeeperSemanticRoutes.ModelTransformationCollapse`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `ContrastiveCollapse` | def | [L3120](formal/Logos/HostileSemantics.lean#L3120) | `def ContrastiveCollapse (I : PreA13FullTheorySignature) : PreA13FullTheorySignat` | —  |
| `FactivePreA14Theory` | structure | [L3182](formal/Logos/HostileSemantics.lean#L3182) | `structure FactivePreA14Theory (I : PreA13FullTheorySignature) : Prop where` | —  |
| `PreA14Consistent` | def | [L3242](formal/Logos/HostileSemantics.lean#L3242) | `def PreA14Consistent (B : PreA13FullTheorySignature → Prop) : Prop` | —  |
| `PreA14ContrastiveBlind` | def | [L3235](formal/Logos/HostileSemantics.lean#L3235) | `def PreA14ContrastiveBlind (B : PreA13FullTheorySignature → Prop) : Prop` | —  |
| `blind_extension_cannot_derive_f1b` | theorem | [L3248](formal/Logos/HostileSemantics.lean#L3248) | `theorem blind_extension_cannot_derive_f1b (B : PreA13FullTheorySignature → Prop)` | —  |
| `collapse_destroys_all_choice` | theorem | [L3125](formal/Logos/HostileSemantics.lean#L3125) | `theorem collapse_destroys_all_choice (I : PreA13FullTheorySignature) (s : I.Subj` | —  |
| `collapse_has_no_freeWill` | theorem | [L3146](formal/Logos/HostileSemantics.lean#L3146) | `theorem collapse_has_no_freeWill (I : PreA13FullTheorySignature) : ¬ ∃ s : (Cont` | —  |
| `collapse_preserves_choiceField` | theorem | [L3139](formal/Logos/HostileSemantics.lean#L3139) | `theorem collapse_preserves_choiceField (I : PreA13FullTheorySignature) (s : I.Su` | —  |
| `collapse_preserves_factive_act` | theorem | [L3132](formal/Logos/HostileSemantics.lean#L3132) | `theorem collapse_preserves_factive_act (I : PreA13FullTheorySignature) (s : I.Su` | —  |
| `collapse_preserves_preA14` | theorem | [L3189](formal/Logos/HostileSemantics.lean#L3189) | `theorem collapse_preserves_preA14 (I : PreA13FullTheorySignature) (h : FactivePr` | —  |
| `fullTheoryHostileInstance_is_factive` | theorem | [L3222](formal/Logos/HostileSemantics.lean#L3222) | `theorem fullTheoryHostileInstance_is_factive : FactivePreA14Theory fullTheoryHos` | —  |
| `nonfactive_act_blocks_collapse` | theorem | [L3159](formal/Logos/HostileSemantics.lean#L3159) | `theorem nonfactive_act_blocks_collapse (I : PreA13FullTheorySignature) (hNonFact` | —  |
| `nonfactive_plurality_blocks_collapse` | theorem | [L3169](formal/Logos/HostileSemantics.lean#L3169) | `theorem nonfactive_plurality_blocks_collapse (I : PreA13FullTheorySignature) (s ` | —  |

### `DeeperSemanticRoutes.ParameterizedHostileFamily`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `AdmissiblePreA14Meaning` | structure | [L3002](formal/Logos/HostileSemantics.lean#L3002) | `structure AdmissiblePreA14Meaning (R : Bool → Prop → Prop) : Prop where` | —  |
| `HornFreeMeaning` | def | [L3006](formal/Logos/HostileSemantics.lean#L3006) | `def HornFreeMeaning (R : Bool → Prop → Prop) : Prop` | —  |
| `parameterizedModel` | def | [L3009](formal/Logos/HostileSemantics.lean#L3009) | `def parameterizedModel (R : Bool → Prop → Prop) : PreA13FullTheorySignature` | —  |
| `parameterized_model_has_act` | theorem | [L3059](formal/Logos/HostileSemantics.lean#L3059) | `theorem parameterized_model_has_act (R : Bool → Prop → Prop) (hAdm : AdmissibleP` | —  |
| `parameterized_model_horn_free_has_no_choice` | theorem | [L3065](formal/Logos/HostileSemantics.lean#L3065) | `theorem parameterized_model_horn_free_has_no_choice (R : Bool → Prop → Prop) (hH` | —  |
| `parameterized_model_horn_free_refutes_f1b` | theorem | [L3072](formal/Logos/HostileSemantics.lean#L3072) | `theorem parameterized_model_horn_free_refutes_f1b (R : Bool → Prop → Prop) (hAdm` | —  |
| `parameterized_model_satisfies_preA14` | theorem | [L3025](formal/Logos/HostileSemantics.lean#L3025) | `theorem parameterized_model_satisfies_preA14 (R : Bool → Prop → Prop) (hAdm : Ad` | —  |
| `singleContentMeaning` | def | [L3095](formal/Logos/HostileSemantics.lean#L3095) | `def singleContentMeaning : Bool → Prop → Prop` | —  |
| `single_content_admissible` | theorem | [L3097](formal/Logos/HostileSemantics.lean#L3097) | `theorem single_content_admissible : AdmissiblePreA14Meaning singleContentMeaning` | —  |
| `single_content_horn_free` | theorem | [L3100](formal/Logos/HostileSemantics.lean#L3100) | `theorem single_content_horn_free : HornFreeMeaning singleContentMeaning` | —  |
| `veridicalMeaning` | def | [L3085](formal/Logos/HostileSemantics.lean#L3085) | `def veridicalMeaning : Bool → Prop → Prop` | —  |
| `veridical_admissible` | theorem | [L3087](formal/Logos/HostileSemantics.lean#L3087) | `theorem veridical_admissible : AdmissiblePreA14Meaning veridicalMeaning` | —  |
| `veridical_horn_free` | theorem | [L3090](formal/Logos/HostileSemantics.lean#L3090) | `theorem veridical_horn_free : HornFreeMeaning veridicalMeaning` | —  |

### `DeeperSemanticRoutes.SelfDenialOfChoiceModel`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Act` | def | [L2763](formal/Logos/HostileSemantics.lean#L2763) | `def Act (s : Subject) (p : Prop) : Prop` | —  |
| `Chooses` | def | [L2764](formal/Logos/HostileSemantics.lean#L2764) | `def Chooses (s : Subject) (p q : Prop) : Prop` | —  |
| `Initiates` | def | [L2762](formal/Logos/HostileSemantics.lean#L2762) | `def Initiates (_s : Subject) (_w _w' : State) (p : Prop) : Prop` | —  |
| `Means` | def | [L2761](formal/Logos/HostileSemantics.lean#L2761) | `def Means (_s : Subject) (p : Prop) : Prop` | —  |
| `SelfDenialProp` | def | [L2766](formal/Logos/HostileSemantics.lean#L2766) | `def SelfDenialProp (s : Subject) (p : Prop) : Prop` | —  |
| `State` | def | [L2760](formal/Logos/HostileSemantics.lean#L2760) | `def State : Type` | —  |
| `Subject` | def | [L2759](formal/Logos/HostileSemantics.lean#L2759) | `def Subject : Type` | —  |
| `act_self_denial` | theorem | [L2788](formal/Logos/HostileSemantics.lean#L2788) | `theorem act_self_denial : Act () True` | —  |
| `no_choice_all` | theorem | [L2770](formal/Logos/HostileSemantics.lean#L2770) | `theorem no_choice_all (s : Subject) (p q : Prop) : ¬ Chooses s p q` | —  |
| `self_denial_holds` | theorem | [L2779](formal/Logos/HostileSemantics.lean#L2779) | `theorem self_denial_holds : SelfDenialProp () True` | —  |
| `self_denial_not_derives_choice` | theorem | [L2799](formal/Logos/HostileSemantics.lean#L2799) | `theorem self_denial_not_derives_choice : ¬ (∀ (s : Subject) (p : Prop), Act s p ` | —  |
| `self_denial_true` | theorem | [L2775](formal/Logos/HostileSemantics.lean#L2775) | `theorem self_denial_true (s : Subject) : ∀ q : Prop, ¬ Chooses s True q` | —  |
| `self_denial_without_choice_consistent` | theorem | [L2793](formal/Logos/HostileSemantics.lean#L2793) | `theorem self_denial_without_choice_consistent : ∃ s : Subject, ∃ p : Prop, Act s` | —  |

### `DeeperSemanticRoutes.UnrealizedPossibilityModel`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Act` | def | [L2971](formal/Logos/HostileSemantics.lean#L2971) | `def Act (s : Subject) (p : Prop) : Prop` | —  |
| `Chooses` | def | [L2972](formal/Logos/HostileSemantics.lean#L2972) | `def Chooses (_s : Subject) (_p _q : Prop) : Prop` | —  |
| `FreeWill` | def | [L2973](formal/Logos/HostileSemantics.lean#L2973) | `def FreeWill (s : Subject) : Prop` | —  |
| `Initiates` | def | [L2970](formal/Logos/HostileSemantics.lean#L2970) | `def Initiates (_s : Subject) (_w _w' : State) (_p : Prop) : Prop` | —  |
| `Means` | def | [L2969](formal/Logos/HostileSemantics.lean#L2969) | `def Means (_s : Subject) (p : Prop) : Prop` | —  |
| `State` | def | [L2968](formal/Logos/HostileSemantics.lean#L2968) | `def State : Type` | —  |
| `Subject` | def | [L2967](formal/Logos/HostileSemantics.lean#L2967) | `def Subject : Type` | —  |
| `no_freeWill` | theorem | [L2980](formal/Logos/HostileSemantics.lean#L2980) | `theorem no_freeWill : ¬ ∃ (s : Subject), FreeWill s` | —  |
| `represents_unrealized` | theorem | [L2976](formal/Logos/HostileSemantics.lean#L2976) | `theorem represents_unrealized : ∃ (s : Subject) (p : Prop), Means s p ∧ ¬p` | —  |
| `unrealized_not_entails_freeWill` | theorem | [L2984](formal/Logos/HostileSemantics.lean#L2984) | `theorem unrealized_not_entails_freeWill : ¬ ((∃ (s : Subject) (p : Prop), Means ` | —  |

### `Logos.Agency`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `A` | abbrev | [L96](formal/Logos/Agency.lean#L96) | `abbrev A` | {Initiates, Means, State, Subject}  |
| `Act` | def | [L92](formal/Logos/Agency.lean#L92) | `def Act (s : Subject) (p : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `Agent` | def | [L54](formal/Logos/Agency.lean#L54) | `def Agent (_s : Subject) : Prop` | {Subject}  |
| `AnActualSubjectExists` | def | [L138](formal/Logos/Agency.lean#L138) | `def AnActualSubjectExists : Prop` | {Initiates, Means, State, Subject}  |
| `Asserts` | def | [L232](formal/Logos/Agency.lean#L232) | `def Asserts (s : Subject) (p : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `Cogito` | theorem | [L261](formal/Logos/Agency.lean#L261) | `theorem Cogito {s : Subject} {p : Prop} (h : Asserts s p) : ∃ s' : Subject, ∃ p'` | {Initiates, Means, State, Subject} → C68 |
| `Cogito_of_bridge` | theorem | [L211](formal/Logos/Agency.lean#L211) | `theorem Cogito_of_bridge (hBridge : weak_act_implies_strong_act) {s : Subject} {` | {Initiates, Means, State, Subject, act}  |
| `Content` | def | [L48](formal/Logos/Agency.lean#L48) | `def Content (_p : Prop) : Prop` | {}  |
| `Exists` | abbrev | [L135](formal/Logos/Agency.lean#L135) | `abbrev Exists : Subject → Prop` | {Initiates, Means, State, Subject}  |
| `Initiates` | axiom | [L87](formal/Logos/Agency.lean#L87) | `axiom Initiates : Subject → State → State → Prop → Prop` | {Initiates, State, Subject}  |
| `Means` | axiom | [L74](formal/Logos/Agency.lean#L74) | `axiom Means : Subject → Prop → Prop` | {Means, Subject}  |
| `NoAct` | def | [L218](formal/Logos/Agency.lean#L218) | `def NoAct : Prop` | {Initiates, Means, State, Subject}  |
| `NoSubject` | def | [L271](formal/Logos/Agency.lean#L271) | `def NoSubject : Prop` | {Initiates, Means, State, Subject}  |
| `NoSubjectSort` | def | [L286](formal/Logos/Agency.lean#L286) | `def NoSubjectSort : Prop` | {Subject}  |
| `NoWeakAct` | def | [L165](formal/Logos/Agency.lean#L165) | `def NoWeakAct : Prop` | {Subject, act}  |
| `Rational` | def | [L60](formal/Logos/Agency.lean#L60) | `def Rational (_s : Subject) : Prop` | {Subject}  |
| `State` | axiom | [L81](formal/Logos/Agency.lean#L81) | `axiom State : Type` | {State}  |
| `Subject` | axiom | [L43](formal/Logos/Agency.lean#L43) | `axiom Subject : Type` | {Subject}  |
| `SubjectExists` | def | [L132](formal/Logos/Agency.lean#L132) | `def SubjectExists (s : Subject) : Prop` | {Initiates, Means, State, Subject}  |
| `T1_subjectExists_of_act` | theorem | [L266](formal/Logos/Agency.lean#L266) | `theorem T1_subjectExists_of_act (h : ∃ s : Subject, ∃ p : Prop, Act s p) : ∃ s :` | {Initiates, Means, State, Subject}  |
| `T2_contentExists` | theorem | [L320](formal/Logos/Agency.lean#L320) | `theorem T2_contentExists : ∃ p : Prop, Content p` | {} → C22 |
| `act` | axiom | [L67](formal/Logos/Agency.lean#L67) | `axiom act : Subject → Prop → Prop` | {Subject, act}  |
| `act_datum_implies_initiates` | theorem | [L117](formal/Logos/Agency.lean#L117) | `theorem act_datum_implies_initiates (h : ∃ s : Subject, ∃ p : Prop, Act s p) : ∃` | {Initiates, Means, State, Subject}  |
| `act_datum_implies_means` | theorem | [L111](formal/Logos/Agency.lean#L111) | `theorem act_datum_implies_means (h : ∃ s : Subject, ∃ p : Prop, Act s p) : ∃ s :` | {Initiates, Means, State, Subject}  |
| `act_decomposition` | theorem | [L106](formal/Logos/Agency.lean#L106) | `theorem act_decomposition (s : Subject) (p : Prop) : Act s p ↔ Means s p ∧ ∃ w w` | {Initiates, Means, State, Subject}  |
| `act_exists_of_assert` | theorem | [L241](formal/Logos/Agency.lean#L241) | `theorem act_exists_of_assert {s : Subject} {p : Prop} (h : Asserts s p) : ∃ s' :` | {Initiates, Means, State, Subject}  |
| `act_implies_agent` | theorem | [L299](formal/Logos/Agency.lean#L299) | `theorem act_implies_agent : ∀ {s : Subject} {p : Prop}, A s p → Agent s` | {Initiates, Means, State, Subject}  |
| `act_implies_content` | theorem | [L294](formal/Logos/Agency.lean#L294) | `theorem act_implies_content : ∀ {s : Subject} {p : Prop}, A s p → Content p` | {Initiates, Means, State, Subject}  |
| `act_implies_exists` | abbrev | [L147](formal/Logos/Agency.lean#L147) | `abbrev act_implies_exists` | {Initiates, Means, State, Subject}  |
| `act_implies_initiates` | theorem | [L99](formal/Logos/Agency.lean#L99) | `theorem act_implies_initiates {s : Subject} {p : Prop} (h : Act s p) : ∃ w w' : ` | {Initiates, Means, State, Subject}  |
| `act_implies_means` | theorem | [L311](formal/Logos/Agency.lean#L311) | `theorem act_implies_means : ∀ {s : Subject} {p : Prop}, A s p → Means s p` | {Initiates, Means, State, Subject}  |
| `act_implies_rational` | theorem | [L305](formal/Logos/Agency.lean#L305) | `theorem act_implies_rational : ∀ {s : Subject} {p : Prop}, A s p → Rational s` | {Initiates, Means, State, Subject}  |
| `act_of_asserting_no_act` | theorem | [L246](formal/Logos/Agency.lean#L246) | `theorem act_of_asserting_no_act (speaker : Subject) (h : Asserts speaker NoAct) ` | {Initiates, Means, State, Subject}  |
| `act_requires_subject` | theorem | [L143](formal/Logos/Agency.lean#L143) | `theorem act_requires_subject (s : Subject) (p : Prop) (h : Act s p) : SubjectExi` | {Initiates, Means, State, Subject}  |
| `an_actual_subject_exists_of_act` | theorem | [L156](formal/Logos/Agency.lean#L156) | `theorem an_actual_subject_exists_of_act (h : ∃ s : Subject, ∃ p : Prop, Act s p)` | {Initiates, Means, State, Subject}  |
| `assertion_is_act` | theorem | [L237](formal/Logos/Agency.lean#L237) | `theorem assertion_is_act {s : Subject} {p : Prop} (h : Asserts s p) : Act s p` | {Initiates, Means, State, Subject}  |
| `assertion_is_weak_act` | theorem | [L172](formal/Logos/Agency.lean#L172) | `theorem assertion_is_weak_act {s : Subject} {p : Prop} (h : asserts s p) : act s` | {Subject, act}  |
| `asserts` | def | [L169](formal/Logos/Agency.lean#L169) | `def asserts (s : Subject) (p : Prop) : Prop` | {Subject, act}  |
| `noAct_conditional_selfRefutes` | theorem | [L221](formal/Logos/Agency.lean#L221) | `theorem noAct_conditional_selfRefutes (hBridge : weak_act_implies_strong_act) (s` | {Initiates, Means, State, Subject, act}  |
| `noCogito_selfRefutes` | theorem | [L257](formal/Logos/Agency.lean#L257) | `theorem noCogito_selfRefutes (speaker : Subject) (h : Asserts speaker NoAct) : F` | {Initiates, Means, State, Subject}  |
| `noSubjectSort_selfRefutes` | theorem | [L289](formal/Logos/Agency.lean#L289) | `theorem noSubjectSort_selfRefutes (speaker : Subject) (h : Asserts speaker NoSub` | {Initiates, Means, State, Subject}  |
| `noSubject_performative_selfRefutes` | theorem | [L276](formal/Logos/Agency.lean#L276) | `theorem noSubject_performative_selfRefutes (speaker : Subject) (h : Asserts spea` | {Initiates, Means, State, Subject}  |
| `noSubject_selfRefutes` | theorem | [L282](formal/Logos/Agency.lean#L282) | `theorem noSubject_selfRefutes (speaker : Subject) (h : Asserts speaker NoSubject` | {Initiates, Means, State, Subject}  |
| `noWeakAct_selfRefutes` | theorem | [L182](formal/Logos/Agency.lean#L182) | `theorem noWeakAct_selfRefutes (speaker : Subject) (h : asserts speaker NoWeakAct` | {Subject, act} → C58 |
| `strong_act_of_weak_act` | theorem | [L206](formal/Logos/Agency.lean#L206) | `theorem strong_act_of_weak_act (hBridge : weak_act_implies_strong_act) {s : Subj` | {Initiates, Means, State, Subject, act}  |
| `subject_exists_of_act` | theorem | [L150](formal/Logos/Agency.lean#L150) | `theorem subject_exists_of_act (h : ∃ s : Subject, ∃ p : Prop, Act s p) : ∃ s : S` | {Initiates, Means, State, Subject}  |
| `subject_exists_of_assert` | theorem | [L251](formal/Logos/Agency.lean#L251) | `theorem subject_exists_of_assert {s : Subject} {p : Prop} (h : Asserts s p) : ∃ ` | {Initiates, Means, State, Subject}  |
| `weak_Cogito` | theorem | [L186](formal/Logos/Agency.lean#L186) | `theorem weak_Cogito {s : Subject} {p : Prop} (h : asserts s p) : ∃ s' : Subject,` | {Subject, act}  |
| `weak_act_exists_implies_strong_act_exists` | def | [L202](formal/Logos/Agency.lean#L202) | `def weak_act_exists_implies_strong_act_exists : Prop` | {Initiates, Means, State, Subject, act}  |
| `weak_act_exists_of_assert` | theorem | [L176](formal/Logos/Agency.lean#L176) | `theorem weak_act_exists_of_assert {s : Subject} {p : Prop} (h : asserts s p) : ∃` | {Subject, act}  |
| `weak_act_implies_strong_act` | def | [L198](formal/Logos/Agency.lean#L198) | `def weak_act_implies_strong_act : Prop` | {Initiates, Means, State, Subject, act}  |

### `Logos.Alternatives`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Incompatible` | def | [L17](formal/Logos/Alternatives.lean#L17) | `def Incompatible (p q : Prop) : Prop` | {}  |
| `T9_incompatibleAlternatives` | theorem | [L24](formal/Logos/Alternatives.lean#L24) | `theorem T9_incompatibleAlternatives : ∃ p q : Prop, Incompatible p q ∧ T p ∧ IsF` | {} → C26 |
| `incompatible_with_negation` | theorem | [L35](formal/Logos/Alternatives.lean#L35) | `theorem incompatible_with_negation {p : Prop} (hp : T p) : Incompatible p (¬ p) ` | {} → C27 |

### `Logos.Choice`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `AlternativeSensitivity` | def | [L662](formal/Logos/Choice.lean#L662) | `def AlternativeSensitivity (s : Subject) (p : Prop) : Prop` | {Means, Subject}  |
| `Authors` | def | [L615](formal/Logos/Choice.lean#L615) | `def Authors (s : Subject) (p : Prop) (q : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `AuthorshipChoice` | def | [L1325](formal/Logos/Choice.lean#L1325) | `def AuthorshipChoice (s : Subject) (p : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `AxActPolarity` | axiom | [L833](formal/Logos/Choice.lean#L833) | `axiom AxActPolarity : ∀ (s : Subject) (p : Prop), Act s p → Means s (¬ p)` | {AxActPolarity, Initiates, Means, State, Subject}  |
| `AxIntentionalChoice` | axiom | [L822](formal/Logos/Choice.lean#L822) | `axiom AxIntentionalChoice : ∀ (s : Subject) (p : Prop), Act s p → ∃ q, Chooses s` | {AxIntentionalChoice, Initiates, Means, State, Subject}  |
| `CanChoose` | def | [L143](formal/Logos/Choice.lean#L143) | `def CanChoose (s : Subject) (p : Prop) : Prop` | {Means, Subject}  |
| `CausalSettles` | def | [L595](formal/Logos/Choice.lean#L595) | `def CausalSettles (s : Subject) (p : Prop) (q : Prop) : Prop` | {Initiates, State, Subject}  |
| `CausalTransition` | def | [L591](formal/Logos/Choice.lean#L591) | `def CausalTransition (s : Subject) (p : Prop) : Prop` | {Initiates, State, Subject}  |
| `Choice` | def | [L1312](formal/Logos/Choice.lean#L1312) | `def Choice (s : Subject) (p : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `ChoiceField` | def | [L98](formal/Logos/Choice.lean#L98) | `def ChoiceField (s : Subject) (p : Prop) (q : Prop) : Prop` | {Means, Subject}  |
| `ChoiceRel` | def | [L1321](formal/Logos/Choice.lean#L1321) | `def ChoiceRel (s : Subject) (p : Prop) (q : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `Chooses` | def | [L105](formal/Logos/Choice.lean#L105) | `def Chooses (s : Subject) (p : Prop) (q : Prop) : Prop` | {Means, Subject}  |
| `Contemplates` | def | [L626](formal/Logos/Choice.lean#L626) | `def Contemplates (s : Subject) (p : Prop) (q : Prop) : Prop` | {Means, Subject}  |
| `ContemplatesWithoutSettling` | def | [L635](formal/Logos/Choice.lean#L635) | `def ContemplatesWithoutSettling (s : Subject) (p : Prop) (q : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `CounterfactualAct` | def | [L1192](formal/Logos/Choice.lean#L1192) | `def CounterfactualAct (s : Subject) (p : Prop) (q : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `DeliberateAuthorship` | def | [L645](formal/Logos/Choice.lean#L645) | `def DeliberateAuthorship (s : Subject) (p : Prop) (q : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `DeliberateChoice` | def | [L485](formal/Logos/Choice.lean#L485) | `def DeliberateChoice (s : Subject) (p : Prop) (q : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `Deliberates` | def | [L1302](formal/Logos/Choice.lean#L1302) | `def Deliberates (s : Subject) (p : Prop) (q : Prop) : Prop` | {Means, Subject}  |
| `DescriptiveAct` | def | [L1214](formal/Logos/Choice.lean#L1214) | `def DescriptiveAct (s : Subject) (p : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `DoubtingDatum` | def | [L1136](formal/Logos/Choice.lean#L1136) | `def DoubtingDatum : Prop` | {Means, Subject}  |
| `Doubts` | def | [L1130](formal/Logos/Choice.lean#L1130) | `def Doubts (s : Subject) (p : Prop) : Prop` | {Means, Subject}  |
| `FreeAgency` | def | [L1329](formal/Logos/Choice.lean#L1329) | `def FreeAgency (s : Subject) : Prop` | {Initiates, Means, State, Subject}  |
| `FreeSubject` | def | [L171](formal/Logos/Choice.lean#L171) | `def FreeSubject (s : Subject) : Prop` | {Means, Subject}  |
| `FreeWill` | def | [L166](formal/Logos/Choice.lean#L166) | `def FreeWill (s : Subject) : Prop` | {Means, Subject}  |
| `JUDGE_HAS_CHOICE_FIELD` | theorem | [L371](formal/Logos/Choice.lean#L371) | `theorem JUDGE_HAS_CHOICE_FIELD (h : ¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) : ∃ s :` | {AxTwoSubjects, Means, Subject} → C54 |
| `Meaning_I` | def | [L120](formal/Logos/Choice.lean#L120) | `def Meaning_I (p : Prop) : Prop` | {Means, Subject}  |
| `MissingCognitiveHorn` | def | [L950](formal/Logos/Choice.lean#L950) | `def MissingCognitiveHorn (s : Subject) (p : Prop) : Prop` | {Means, Subject}  |
| `NoChoiceField` | def | [L344](formal/Logos/Choice.lean#L344) | `def NoChoiceField : Prop` | {Means, Subject}  |
| `ReasonResponsiveAct` | def | [L1188](formal/Logos/Choice.lean#L1188) | `def ReasonResponsiveAct (s : Subject) (p : Prop) (r : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `Rejects` | def | [L524](formal/Logos/Choice.lean#L524) | `def Rejects (s : Subject) (q : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `RelationalIntentionality` | def | [L666](formal/Logos/Choice.lean#L666) | `def RelationalIntentionality (s : Subject) (p : Prop) (q : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `Selects` | def | [L440](formal/Logos/Choice.lean#L440) | `def Selects (s : Subject) (p : Prop) (q : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `SelfAssertedAuthorship` | def | [L1261](formal/Logos/Choice.lean#L1261) | `def SelfAssertedAuthorship (s : Subject) (p : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `SelfAssertedChoice` | def | [L1256](formal/Logos/Choice.lean#L1256) | `def SelfAssertedChoice (s : Subject) (p : Prop) : Prop` | {Means, Subject}  |
| `SelfAssertedDeliberateChoice` | def | [L1266](formal/Logos/Choice.lean#L1266) | `def SelfAssertedDeliberateChoice (s : Subject) (p : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `SelfAssertedParadox` | def | [L1271](formal/Logos/Choice.lean#L1271) | `def SelfAssertedParadox (s : Subject) (p : Prop) : Prop` | {Means, Subject}  |
| `SelfDenialOfChoice` | def | [L1233](formal/Logos/Choice.lean#L1233) | `def SelfDenialOfChoice (s : Subject) (p : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `SelfDenialOfExecutiveChoice` | def | [L1338](formal/Logos/Choice.lean#L1338) | `def SelfDenialOfExecutiveChoice (s : Subject) (p : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `T11_choiceField` | theorem | [L290](formal/Logos/Choice.lean#L290) | `theorem T11_choiceField (h : ∃ s : Subject, ∃ p : Prop, A s p) : ∃ s : Subject, ` | {Initiates, Means, State, Subject} → C39 |
| `T11_choiceField_from_plurality` | theorem | [L297](formal/Logos/Choice.lean#L297) | `theorem T11_choiceField_from_plurality : ∃ s : Subject, Person s ∧ ∃ p q : Prop,` | {AxTwoSubjects, Means, Subject}  |
| `TeleologicalAct` | def | [L1184](formal/Logos/Choice.lean#L1184) | `def TeleologicalAct (s : Subject) (p : Prop) (g : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `act_decomposition` | theorem | [L785](formal/Logos/Choice.lean#L785) | `theorem act_decomposition (s : Subject) (p : Prop) : Act s p ↔ Means s p ∧ ∃ w w` | {Initiates, Means, State, Subject}  |
| `act_implies_asserts_bridge` | def | [L687](formal/Logos/Choice.lean#L687) | `def act_implies_asserts_bridge : Prop` | {Initiates, Means, State, Subject}  |
| `act_implies_authors` | theorem | [L619](formal/Logos/Choice.lean#L619) | `theorem act_implies_authors (s : Subject) (p : Prop) (h : Act s p) (hNoActNeg : ` | {Initiates, Means, State, Subject}  |
| `act_implies_causalTransition` | theorem | [L599](formal/Logos/Choice.lean#L599) | `theorem act_implies_causalTransition {s : Subject} {p : Prop} (h : Act s p) : Ca` | {Initiates, Means, State, Subject}  |
| `act_implies_choiceField` | theorem | [L604](formal/Logos/Choice.lean#L604) | `theorem act_implies_choiceField (s : Subject) (p : Prop) (h : Act s p) : ∃ q : P` | {Initiates, Means, State, Subject}  |
| `act_missing_horn_iff_chooses` | theorem | [L983](formal/Logos/Choice.lean#L983) | `theorem act_missing_horn_iff_chooses (s : Subject) (p : Prop) (hAct : Act s p) :` | {Initiates, Means, State, Subject}  |
| `act_missing_horn_implies_chooses` | theorem | [L976](formal/Logos/Choice.lean#L976) | `theorem act_missing_horn_implies_chooses (s : Subject) (p : Prop) : Act s p ∧ Mi` | {Initiates, Means, State, Subject}  |
| `act_polarity_implies_conditional` | theorem | [L846](formal/Logos/Choice.lean#L846) | `theorem act_polarity_implies_conditional (h : act_polarity_principle) : conditio` | {Initiates, Means, State, Subject}  |
| `act_polarity_implies_contrastive` | theorem | [L883](formal/Logos/Choice.lean#L883) | `theorem act_polarity_implies_contrastive (h : act_polarity_principle) : contrast` | {Initiates, Means, State, Subject}  |
| `act_polarity_implies_existential` | theorem | [L852](formal/Logos/Choice.lean#L852) | `theorem act_polarity_implies_existential (h : act_polarity_principle) (hAct : ∃ ` | {Initiates, Means, State, Subject}  |
| `act_polarity_implies_existential_choice` | theorem | [L944](formal/Logos/Choice.lean#L944) | `theorem act_polarity_implies_existential_choice (h : act_polarity_principle) : e` | {Initiates, Means, State, Subject}  |
| `act_polarity_implies_intentional_choice` | theorem | [L889](formal/Logos/Choice.lean#L889) | `theorem act_polarity_implies_intentional_choice (h : act_polarity_principle) : ∀` | {Initiates, Means, State, Subject}  |
| `act_polarity_principle` | def | [L716](formal/Logos/Choice.lean#L716) | `def act_polarity_principle : Prop` | {Initiates, Means, State, Subject}  |
| `act_produces_choice_iff_missing_horn` | theorem | [L1008](formal/Logos/Choice.lean#L1008) | `theorem act_produces_choice_iff_missing_horn (s : Subject) (p : Prop) (hAct : Ac` | {Initiates, Means, State, Subject}  |
| `alternativeSensitivity_implies_genuineChoice` | theorem | [L670](formal/Logos/Choice.lean#L670) | `theorem alternativeSensitivity_implies_genuineChoice {s : Subject} {p : Prop} (h` | {Initiates, Means, State, Subject}  |
| `asserting_noChoiceField_is_choiceField` | theorem | [L348](formal/Logos/Choice.lean#L348) | `theorem asserting_noChoiceField_is_choiceField (speaker : Subject) (h : Logos.Ag` | {Initiates, Means, State, Subject}  |
| `assertion_consistency` | theorem | [L414](formal/Logos/Choice.lean#L414) | `theorem assertion_consistency {s : Subject} {p : Prop} (h : Asserts s p) : ¬ Ass` | {Initiates, Means, State, Subject}  |
| `asserts_implies_choice` | theorem | [L1316](formal/Logos/Choice.lean#L1316) | `theorem asserts_implies_choice (s : Subject) (p : Prop) (hAss : Asserts s p) : C` | {Initiates, Means, State, Subject}  |
| `asserts_implies_freeAgency` | theorem | [L1333](formal/Logos/Choice.lean#L1333) | `theorem asserts_implies_freeAgency {s : Subject} {p : Prop} (hAss : Asserts s p)` | {Initiates, Means, State, Subject}  |
| `asserts_implies_selects` | theorem | [L609](formal/Logos/Choice.lean#L609) | `theorem asserts_implies_selects (s : Subject) (p : Prop) (h : Asserts s p) : ∃ q` | {Initiates, Means, State, Subject}  |
| `asserts_selects` | theorem | [L446](formal/Logos/Choice.lean#L446) | `theorem asserts_selects (s : Subject) (p : Prop) (h : Asserts s p) : Selects s p` | {Initiates, Means, State, Subject}  |
| `asserts_selects_all_incompatible` | theorem | [L453](formal/Logos/Choice.lean#L453) | `theorem asserts_selects_all_incompatible (s : Subject) (p q : Prop) (h : Asserts` | {Initiates, Means, State, Subject}  |
| `bilateral_implies_act_polarity` | theorem | [L721](formal/Logos/Choice.lean#L721) | `theorem bilateral_implies_act_polarity (h : bilateral_intentionality_principle) ` | {Initiates, Means, State, Subject}  |
| `bilateral_intentionality_principle` | def | [L710](formal/Logos/Choice.lean#L710) | `def bilateral_intentionality_principle : Prop` | {Means, Subject}  |
| `canChoose_unfold` | theorem | [L148](formal/Logos/Choice.lean#L148) | `theorem canChoose_unfold {s : Subject} {p : Prop} : CanChoose s p ↔ ∃ q : Prop, ` | {Means, Subject, CL}  |
| `choiceField_exists` | theorem | [L330](formal/Logos/Choice.lean#L330) | `theorem choiceField_exists (h : ∃ s : Subject, ∃ p : Prop, A s p) : ∃ s : Subjec` | {Initiates, Means, State, Subject} → C52 |
| `choiceField_exists_from_plurality` | theorem | [L338](formal/Logos/Choice.lean#L338) | `theorem choiceField_exists_from_plurality : ∃ s : Subject, ∃ p q : Prop, ChoiceF` | {AxTwoSubjects, Means, Subject}  |
| `chooses_implies_freeSubject` | theorem | [L188](formal/Logos/Choice.lean#L188) | `theorem chooses_implies_freeSubject {s : Subject} {p q : Prop} (h : Chooses s p ` | {Means, Subject}  |
| `chooses_implies_freeWill` | theorem | [L183](formal/Logos/Choice.lean#L183) | `theorem chooses_implies_freeWill {s : Subject} {p q : Prop} (h : Chooses s p q) ` | {Means, Subject}  |
| `conditional_act_polarity` | def | [L837](formal/Logos/Choice.lean#L837) | `def conditional_act_polarity : Prop` | {Initiates, Means, State, Subject}  |
| `contemplatesWithoutSettling_implies_freeWill` | theorem | [L639](formal/Logos/Choice.lean#L639) | `theorem contemplatesWithoutSettling_implies_freeWill {s : Subject} {p q : Prop} ` | {Initiates, Means, State, Subject}  |
| `contemplates_iff_chooses` | theorem | [L630](formal/Logos/Choice.lean#L630) | `theorem contemplates_iff_chooses (s : Subject) (p q : Prop) : Contemplates s p q` | {Means, Subject}  |
| `contrastive_agency_implies_existential` | theorem | [L911](formal/Logos/Choice.lean#L911) | `theorem contrastive_agency_implies_existential (h : contrastive_agency_principle` | {Initiates, Means, State, Subject}  |
| `contrastive_agency_principle` | def | [L873](formal/Logos/Choice.lean#L873) | `def contrastive_agency_principle : Prop` | {Initiates, Means, State, Subject}  |
| `contrastive_implies_intentional_choice` | theorem | [L904](formal/Logos/Choice.lean#L904) | `theorem contrastive_implies_intentional_choice : contrastive_agency_principle → ` | {Initiates, Means, State, Subject}  |
| `counterfactual_act_implies_genuineChoice` | theorem | [L1208](formal/Logos/Choice.lean#L1208) | `theorem counterfactual_act_implies_genuineChoice (s : Subject) (p q : Prop) (h :` | {AxIntentionalChoice, Initiates, Means, State, Subject}  |
| `deliberateAuthorship_implies_chooses` | theorem | [L649](formal/Logos/Choice.lean#L649) | `theorem deliberateAuthorship_implies_chooses {s : Subject} {p q : Prop} (h : Del` | {Initiates, Means, State, Subject}  |
| `deliberateAuthorship_implies_deliberateChoice` | theorem | [L655](formal/Logos/Choice.lean#L655) | `theorem deliberateAuthorship_implies_deliberateChoice {s : Subject} {p q : Prop}` | {Initiates, Means, State, Subject}  |
| `deliberateChoice_exists_of_assertion_and_negation_meaning` | theorem | [L560](formal/Logos/Choice.lean#L560) | `theorem deliberateChoice_exists_of_assertion_and_negation_meaning (h : deliberat` | {Initiates, Means, State, Subject}  |
| `deliberateChoice_iff_selects_and_means` | theorem | [L504](formal/Logos/Choice.lean#L504) | `theorem deliberateChoice_iff_selects_and_means (s : Subject) (p q : Prop) : Deli` | {Initiates, Means, State, Subject} → C100 |
| `deliberateChoice_iff_selects_and_rejects` | theorem | [L530](formal/Logos/Choice.lean#L530) | `theorem deliberateChoice_iff_selects_and_rejects (s : Subject) (p q : Prop) : De` | {Initiates, Means, State, Subject}  |
| `deliberateChoice_implies_chooses` | theorem | [L496](formal/Logos/Choice.lean#L496) | `theorem deliberateChoice_implies_chooses {s : Subject} {p q : Prop} (h : Deliber` | {Initiates, Means, State, Subject} → C98 |
| `deliberateChoice_implies_selects` | theorem | [L490](formal/Logos/Choice.lean#L490) | `theorem deliberateChoice_implies_selects {s : Subject} {p q : Prop} (h : Deliber` | {Initiates, Means, State, Subject} → C97 |
| `deliberateChoice_negation_decomposition` | theorem | [L516](formal/Logos/Choice.lean#L516) | `theorem deliberateChoice_negation_decomposition (s : Subject) (p : Prop) : Delib` | {Initiates, Means, State, Subject}  |
| `deliberateChoice_negation_iff` | theorem | [L540](formal/Logos/Choice.lean#L540) | `theorem deliberateChoice_negation_iff (s : Subject) (p : Prop) (hAss : Asserts s` | {Initiates, Means, State, Subject}  |
| `deliberateGenuineChoiceResource` | def | [L554](formal/Logos/Choice.lean#L554) | `def deliberateGenuineChoiceResource : Prop` | {Initiates, Means, State, Subject}  |
| `deliberateResource_of_act_polarity` | theorem | [L1038](formal/Logos/Choice.lean#L1038) | `theorem deliberateResource_of_act_polarity (hPolarity : act_polarity_principle) ` | {Initiates, Means, State, Subject}  |
| `deliberateResource_of_bilateral_intentionality` | theorem | [L1057](formal/Logos/Choice.lean#L1057) | `theorem deliberateResource_of_bilateral_intentionality (hBilateral : bilateral_i` | {Initiates, Means, State, Subject}  |
| `deliberate_resource_implies_genuine_choice` | theorem | [L573](formal/Logos/Choice.lean#L573) | `theorem deliberate_resource_implies_genuine_choice (h : deliberateGenuineChoiceR` | {Initiates, Means, State, Subject}  |
| `deliberates_iff_chooses` | theorem | [L1306](formal/Logos/Choice.lean#L1306) | `theorem deliberates_iff_chooses (s : Subject) (p q : Prop) : Deliberates s p q ↔` | {Means, Subject}  |
| `descriptive_act_implies_genuineChoice` | theorem | [L1218](formal/Logos/Choice.lean#L1218) | `theorem descriptive_act_implies_genuineChoice (s : Subject) (p : Prop) (h : Desc` | {AxIntentionalChoice, Initiates, Means, State, Subject}  |
| `doubt_existence_bridge` | def | [L1168](formal/Logos/Choice.lean#L1168) | `def doubt_existence_bridge : Prop` | {Initiates, Means, State, Subject}  |
| `existential_act_polarity` | def | [L842](formal/Logos/Choice.lean#L842) | `def existential_act_polarity : Prop` | {Initiates, Means, State, Subject}  |
| `existential_choice_iff_f1b` | theorem | [L939](formal/Logos/Choice.lean#L939) | `theorem existential_choice_iff_f1b : existential_intentional_choice ↔ ((∃ s : Su` | {Initiates, Means, State, Subject}  |
| `existential_contrastive_agency` | def | [L878](formal/Logos/Choice.lean#L878) | `def existential_contrastive_agency : Prop` | {Initiates, Means, State, Subject}  |
| `existential_intentional_choice` | def | [L919](formal/Logos/Choice.lean#L919) | `def existential_intentional_choice : Prop` | {Initiates, Means, State, Subject}  |
| `f1b_iff_missing_cognitive_horn` | theorem | [L995](formal/Logos/Choice.lean#L995) | `theorem f1b_iff_missing_cognitive_horn : ((∃ s : Subject, ∃ p : Prop, Act s p) →` | {Initiates, Means, State, Subject}  |
| `freeSubject_exists` | theorem | [L1124](formal/Logos/Choice.lean#L1124) | `theorem freeSubject_exists (h : ∃ s : Subject, ∃ p : Prop, Act s p) : ∃ s : Subj` | {AxIntentionalChoice, Initiates, Means, State, Subject}  |
| `freeSubject_exists_of_act` | theorem | [L1102](formal/Logos/Choice.lean#L1102) | `theorem freeSubject_exists_of_act (h : ∃ s : Subject, ∃ p : Prop, Act s p) : ∃ s` | {AxIntentionalChoice, Initiates, Means, State, Subject}  |
| `freeSubject_exists_of_contrastive_act` | theorem | [L1031](formal/Logos/Choice.lean#L1031) | `theorem freeSubject_exists_of_contrastive_act (h : contrastive_agency_principle)` | {Initiates, Means, State, Subject}  |
| `freeSubject_iff_freeWill` | theorem | [L174](formal/Logos/Choice.lean#L174) | `theorem freeSubject_iff_freeWill (s : Subject) : FreeSubject s ↔ FreeWill s` | {Means, Subject}  |
| `freeSubject_implies_intentional` | theorem | [L200](formal/Logos/Choice.lean#L200) | `theorem freeSubject_implies_intentional (s : Subject) (h : FreeSubject s) : Logo` | {Means, Subject}  |
| `freeSubject_implies_intentionalSubject` | theorem | [L194](formal/Logos/Choice.lean#L194) | `theorem freeSubject_implies_intentionalSubject (s : Subject) (h : FreeSubject s)` | {Means, Subject}  |
| `freeWillExists_of_chooses` | theorem | [L207](formal/Logos/Choice.lean#L207) | `theorem freeWillExists_of_chooses (h : ∃ s : Subject, ∃ p q : Prop, Chooses s p ` | {Means, Subject}  |
| `freeWillExists_of_genuineChoice` | theorem | [L255](formal/Logos/Choice.lean#L255) | `theorem freeWillExists_of_genuineChoice : genuineChoice_exists → ∃ s : Subject, ` | {Means, Subject}  |
| `freeWill_exists` | theorem | [L1118](formal/Logos/Choice.lean#L1118) | `theorem freeWill_exists (h : ∃ s : Subject, ∃ p : Prop, Act s p) : ∃ s : Subject` | {AxIntentionalChoice, Initiates, Means, State, Subject} → F1b |
| `freeWill_exists_of_act` | theorem | [L1095](formal/Logos/Choice.lean#L1095) | `theorem freeWill_exists_of_act (h : ∃ s : Subject, ∃ p : Prop, Act s p) : ∃ s : ` | {AxIntentionalChoice, Initiates, Means, State, Subject}  |
| `freeWill_exists_of_act_polarity` | theorem | [L1109](formal/Logos/Choice.lean#L1109) | `theorem freeWill_exists_of_act_polarity (h : ∃ s : Subject, ∃ p : Prop, Act s p)` | {AxActPolarity, Initiates, Means, State, Subject}  |
| `freeWill_exists_of_contrastive_act` | theorem | [L1024](formal/Logos/Choice.lean#L1024) | `theorem freeWill_exists_of_contrastive_act (h : contrastive_agency_principle) (h` | {Initiates, Means, State, Subject}  |
| `freeWill_exists_of_doubt_bridge` | theorem | [L1178](formal/Logos/Choice.lean#L1178) | `theorem freeWill_exists_of_doubt_bridge (hBridge : doubt_existence_bridge) (hAct` | {Initiates, Means, State, Subject}  |
| `freeWill_exists_of_doubt_datum` | theorem | [L1160](formal/Logos/Choice.lean#L1160) | `theorem freeWill_exists_of_doubt_datum (h : DoubtingDatum) : ∃ s : Subject, Free` | {Means, Subject}  |
| `freeWill_exists_of_existential_act_polarity` | theorem | [L865](formal/Logos/Choice.lean#L865) | `theorem freeWill_exists_of_existential_act_polarity (h : existential_act_polarit` | {Initiates, Means, State, Subject}  |
| `freeWill_exists_of_existential_choice` | theorem | [L931](formal/Logos/Choice.lean#L931) | `theorem freeWill_exists_of_existential_choice (h : existential_intentional_choic` | {Initiates, Means, State, Subject}  |
| `freeWill_iff_means_missing_horn` | theorem | [L967](formal/Logos/Choice.lean#L967) | `theorem freeWill_iff_means_missing_horn : (∃ s : Subject, FreeWill s) ↔ ∃ s : Su` | {Means, Subject}  |
| `freeWill_of_doubt` | theorem | [L1147](formal/Logos/Choice.lean#L1147) | `theorem freeWill_of_doubt {s : Subject} {p : Prop} (hDoubt : Doubts s p) : FreeW` | {Means, Subject}  |
| `genuineChoice_exists` | def | [L230](formal/Logos/Choice.lean#L230) | `def genuineChoice_exists : Prop` | {Means, Subject}  |
| `genuineChoice_exists_of_act` | theorem | [L1076](formal/Logos/Choice.lean#L1076) | `theorem genuineChoice_exists_of_act (h : ∃ s : Subject, ∃ p : Prop, Act s p) : g` | {AxActPolarity, Initiates, Means, State, Subject}  |
| `genuineChoice_exists_of_act_constitutive` | theorem | [L1085](formal/Logos/Choice.lean#L1085) | `theorem genuineChoice_exists_of_act_constitutive (h : ∃ s : Subject, ∃ p : Prop,` | {AxIntentionalChoice, Initiates, Means, State, Subject}  |
| `genuineChoice_exists_of_act_polarity` | theorem | [L1047](formal/Logos/Choice.lean#L1047) | `theorem genuineChoice_exists_of_act_polarity (hPolarity : act_polarity_principle` | {Initiates, Means, State, Subject}  |
| `genuineChoice_exists_of_assertion_and_negation_meaning` | abbrev | [L583](formal/Logos/Choice.lean#L583) | `abbrev genuineChoice_exists_of_assertion_and_negation_meaning` | {Initiates, Means, State, Subject}  |
| `genuineChoice_exists_of_bilateral_intentionality` | theorem | [L1066](formal/Logos/Choice.lean#L1066) | `theorem genuineChoice_exists_of_bilateral_intentionality (hBilateral : bilateral` | {Initiates, Means, State, Subject}  |
| `genuineChoice_exists_of_contrastive_act` | theorem | [L1015](formal/Logos/Choice.lean#L1015) | `theorem genuineChoice_exists_of_contrastive_act (h : contrastive_agency_principl` | {Initiates, Means, State, Subject}  |
| `genuineChoice_exists_of_doubt_bridge` | theorem | [L1172](formal/Logos/Choice.lean#L1172) | `theorem genuineChoice_exists_of_doubt_bridge (hBridge : doubt_existence_bridge) ` | {Initiates, Means, State, Subject}  |
| `genuineChoice_exists_of_doubt_datum` | theorem | [L1153](formal/Logos/Choice.lean#L1153) | `theorem genuineChoice_exists_of_doubt_datum (h : DoubtingDatum) : genuineChoice_` | {Means, Subject}  |
| `genuineChoice_exists_of_existential_act_polarity` | theorem | [L859](formal/Logos/Choice.lean#L859) | `theorem genuineChoice_exists_of_existential_act_polarity (h : existential_act_po` | {Initiates, Means, State, Subject}  |
| `genuineChoice_of_doubt` | theorem | [L1142](formal/Logos/Choice.lean#L1142) | `theorem genuineChoice_of_doubt {s : Subject} {p : Prop} (hDoubt : Doubts s p) : ` | {Means, Subject}  |
| `genuineChoice_requires_error_possibility` | theorem | [L279](formal/Logos/Choice.lean#L279) | `theorem genuineChoice_requires_error_possibility : genuineChoice_exists → ¬ (∀ s` | {Means, Subject}  |
| `incompatible_self_negation` | theorem | [L113](formal/Logos/Choice.lean#L113) | `theorem incompatible_self_negation (p : Prop) : Incompatible p (¬ p)` | {} → C50 |
| `intentional_choice_implies_contrastive` | theorem | [L896](formal/Logos/Choice.lean#L896) | `theorem intentional_choice_implies_contrastive : (∀ (s : Subject) (p : Prop), Ac` | {Initiates, Means, State, Subject}  |
| `intentional_choice_implies_existential_choice` | theorem | [L923](formal/Logos/Choice.lean#L923) | `theorem intentional_choice_implies_existential_choice (h : ∀ (s : Subject) (p : ` | {Initiates, Means, State, Subject}  |
| `intentional_hasChoiceField` | theorem | [L307](formal/Logos/Choice.lean#L307) | `theorem intentional_hasChoiceField {s : Subject} (hIn : Logos.Person.Intentional` | {Means, Subject}  |
| `judge_asserting_rightWrong_has_choiceField` | theorem | [L379](formal/Logos/Choice.lean#L379) | `theorem judge_asserting_rightWrong_has_choiceField (speaker : Subject) (h : Logo` | {Initiates, Means, State, Subject}  |
| `meaning_I_needs_subject` | theorem | [L128](formal/Logos/Choice.lean#L128) | `theorem meaning_I_needs_subject {p : Prop} (h : Meaning_I p) : ∃ s : Subject, Me` | {Means, Subject}  |
| `meaning_needs_subject` | theorem | [L137](formal/Logos/Choice.lean#L137) | `theorem meaning_needs_subject {s : Subject} {p : Prop} (hm : Means s p) : ∃ t : ` | {Means, Subject} → C49 |
| `means_missing_horn_iff_chooses` | theorem | [L956](formal/Logos/Choice.lean#L956) | `theorem means_missing_horn_iff_chooses (s : Subject) (p : Prop) : Means s p ∧ Mi` | {Means, Subject}  |
| `noChoiceField_contradicts_field` | theorem | [L360](formal/Logos/Choice.lean#L360) | `theorem noChoiceField_contradicts_field (hField : ∃ s : Subject, ∃ p q : Prop, C` | {Means, Subject}  |
| `noChoiceField_selfRefutes` | theorem | [L355](formal/Logos/Choice.lean#L355) | `theorem noChoiceField_selfRefutes (speaker : Subject) (h : Logos.Agency.Asserts ` | {Initiates, Means, State, Subject} → C53 |
| `noStrongTruth_assertable_refutes` | theorem | [L1227](formal/Logos/Choice.lean#L1227) | `theorem noStrongTruth_assertable_refutes (speaker : Subject) : Asserts speaker (` | {Initiates, Means, State, Subject, CL} → C94 |
| `noSubject_contradicts_subject` | theorem | [L403](formal/Logos/Choice.lean#L403) | `theorem noSubject_contradicts_subject (hSubj : ∃ s : Subject, Logos.Agency.Subje` | {Initiates, Means, State, Subject}  |
| `noSubject_selfRefutes` | theorem | [L398](formal/Logos/Choice.lean#L398) | `theorem noSubject_selfRefutes (speaker : Subject) (h : Logos.Agency.Asserts spea` | {Initiates, Means, State, Subject} → C57 |
| `no_one_asserts_incompatible_pair` | theorem | [L425](formal/Logos/Choice.lean#L425) | `theorem no_one_asserts_incompatible_pair : ¬ ∃ s : Subject, ∃ p q : Prop, Assert` | {Initiates, Means, State, Subject}  |
| `no_selection_no_assertion` | theorem | [L471](formal/Logos/Choice.lean#L471) | `theorem no_selection_no_assertion (s : Subject) (p : Prop) (hNo : ∀ q : Prop, ¬ ` | {Initiates, Means, State, Subject}  |
| `person_hasChoiceField` | theorem | [L320](formal/Logos/Choice.lean#L320) | `theorem person_hasChoiceField {s : Subject} (hs : Person s) : ∃ p q : Prop, Choi` | {Means, Subject} → C51 |
| `reasonResponsive_act_implies_genuineChoice` | theorem | [L1202](formal/Logos/Choice.lean#L1202) | `theorem reasonResponsive_act_implies_genuineChoice (s : Subject) (p r : Prop) (h` | {AxIntentionalChoice, Initiates, Means, State, Subject}  |
| `rejectedHornCoMeant` | def | [L247](formal/Logos/Choice.lean#L247) | `def rejectedHornCoMeant : Prop` | {Means, Subject}  |
| `rejectedHornCoMeant_implies_genuineChoice` | theorem | [L266](formal/Logos/Choice.lean#L266) | `theorem rejectedHornCoMeant_implies_genuineChoice : rejectedHornCoMeant → genuin` | {Means, Subject}  |
| `relationalIntentionality_implies_genuineChoice` | theorem | [L677](formal/Logos/Choice.lean#L677) | `theorem relationalIntentionality_implies_genuineChoice {s : Subject} {p q : Prop` | {Initiates, Means, State, Subject}  |
| `rightWrong_implies_someone_means` | theorem | [L391](formal/Logos/Choice.lean#L391) | `theorem rightWrong_implies_someone_means (h : ¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_` | {AxTwoSubjects, Means, Subject} → C61 |
| `selection_exists` | theorem | [L463](formal/Logos/Choice.lean#L463) | `theorem selection_exists (h : ∃ s : Subject, ∃ p : Prop, Asserts s p) : ∃ s : Su` | {Initiates, Means, State, Subject}  |
| `selection_exists_of_act` | theorem | [L693](formal/Logos/Choice.lean#L693) | `theorem selection_exists_of_act (hBridge : act_implies_asserts_bridge) (h : ∃ s ` | {Initiates, Means, State, Subject} → C99 |
| `selfAssertedChoice_factive_implies_chooses` | theorem | [L1275](formal/Logos/Choice.lean#L1275) | `theorem selfAssertedChoice_factive_implies_chooses {s : Subject} {p : Prop} (hAs` | {Initiates, Means, State, Subject}  |
| `selfAssertedDeliberateChoice_factive_implies_chooses` | theorem | [L1281](formal/Logos/Choice.lean#L1281) | `theorem selfAssertedDeliberateChoice_factive_implies_chooses {s : Subject} {p : ` | {Initiates, Means, State, Subject}  |
| `selfAssertedParadox_is_false` | theorem | [L1288](formal/Logos/Choice.lean#L1288) | `theorem selfAssertedParadox_is_false {s : Subject} {p : Prop} (hSelf : SelfAsser` | {Means, Subject}  |
| `selfAssertedParadox_not_assertable` | theorem | [L1354](formal/Logos/Choice.lean#L1354) | `theorem selfAssertedParadox_not_assertable {s : Subject} {p : Prop} (hSelf : Sel` | {Initiates, Means, State, Subject}  |
| `selfDenialOfExecutiveChoice_selfRefutes` | theorem | [L1345](formal/Logos/Choice.lean#L1345) | `theorem selfDenialOfExecutiveChoice_selfRefutes {s : Subject} {p : Prop} (hDenia` | {Initiates, Means, State, Subject}  |
| `selfDenial_implies_genuineChoice_of_a14` | theorem | [L1245](formal/Logos/Choice.lean#L1245) | `theorem selfDenial_implies_genuineChoice_of_a14 {s : Subject} {p : Prop} (hDenia` | {AxIntentionalChoice, Initiates, Means, State, Subject}  |
| `selfDenial_implies_genuineChoice_of_polarity` | theorem | [L1237](formal/Logos/Choice.lean#L1237) | `theorem selfDenial_implies_genuineChoice_of_polarity {s : Subject} {p : Prop} (h` | {AxActPolarity, Initiates, Means, State, Subject}  |
| `teleological_act_implies_genuineChoice` | theorem | [L1196](formal/Logos/Choice.lean#L1196) | `theorem teleological_act_implies_genuineChoice (s : Subject) (p g : Prop) (h : T` | {AxIntentionalChoice, Initiates, Means, State, Subject}  |

### `Logos.ClaimMeanings`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `C19` | def | [L32](formal/Logos/ClaimMeanings.lean#L32) | `def C19 : String` | —  |
| `C64` | def | [L62](formal/Logos/ClaimMeanings.lean#L62) | `def C64 : String` | —  |
| `C65` | def | [L64](formal/Logos/ClaimMeanings.lean#L64) | `def C65 : String` | —  |
| `C66` | def | [L66](formal/Logos/ClaimMeanings.lean#L66) | `def C66 : String` | —  |
| `C67` | def | [L68](formal/Logos/ClaimMeanings.lean#L68) | `def C67 : String` | —  |
| `C69` | def | [L48](formal/Logos/ClaimMeanings.lean#L48) | `def C69 : String` | —  |
| `C70` | def | [L50](formal/Logos/ClaimMeanings.lean#L50) | `def C70 : String` | —  |
| `C71` | def | [L52](formal/Logos/ClaimMeanings.lean#L52) | `def C71 : String` | —  |
| `C72` | def | [L54](formal/Logos/ClaimMeanings.lean#L54) | `def C72 : String` | —  |
| `C73` | def | [L56](formal/Logos/ClaimMeanings.lean#L56) | `def C73 : String` | —  |
| `C75` | def | [L58](formal/Logos/ClaimMeanings.lean#L58) | `def C75 : String` | —  |
| `C76` | def | [L60](formal/Logos/ClaimMeanings.lean#L60) | `def C76 : String` | —  |
| `C78` | def | [L36](formal/Logos/ClaimMeanings.lean#L36) | `def C78 : String` | —  |
| `C79` | def | [L38](formal/Logos/ClaimMeanings.lean#L38) | `def C79 : String` | —  |
| `C80` | def | [L70](formal/Logos/ClaimMeanings.lean#L70) | `def C80 : String` | —  |
| `C81` | def | [L72](formal/Logos/ClaimMeanings.lean#L72) | `def C81 : String` | —  |
| `C82` | def | [L74](formal/Logos/ClaimMeanings.lean#L74) | `def C82 : String` | —  |
| `C87` | def | [L40](formal/Logos/ClaimMeanings.lean#L40) | `def C87 : String` | —  |
| `C88` | def | [L42](formal/Logos/ClaimMeanings.lean#L42) | `def C88 : String` | —  |
| `C89` | def | [L44](formal/Logos/ClaimMeanings.lean#L44) | `def C89 : String` | —  |
| `C90` | def | [L46](formal/Logos/ClaimMeanings.lean#L46) | `def C90 : String` | —  |
| `F1b` | def | [L12](formal/Logos/ClaimMeanings.lean#L12) | `def F1b : String` | —  |
| `F2` | def | [L14](formal/Logos/ClaimMeanings.lean#L14) | `def F2 : String` | —  |
| `F3` | def | [L16](formal/Logos/ClaimMeanings.lean#L16) | `def F3 : String` | —  |
| `F4` | def | [L18](formal/Logos/ClaimMeanings.lean#L18) | `def F4 : String` | —  |
| `F5` | def | [L20](formal/Logos/ClaimMeanings.lean#L20) | `def F5 : String` | —  |
| `F6` | def | [L22](formal/Logos/ClaimMeanings.lean#L22) | `def F6 : String` | —  |
| `F7` | def | [L24](formal/Logos/ClaimMeanings.lean#L24) | `def F7 : String` | —  |
| `F8` | def | [L26](formal/Logos/ClaimMeanings.lean#L26) | `def F8 : String` | —  |
| `F9` | def | [L28](formal/Logos/ClaimMeanings.lean#L28) | `def F9 : String` | —  |
| `Q7_2` | def | [L30](formal/Logos/ClaimMeanings.lean#L30) | `def Q7_2 : String` | —  |

### `Logos.ConditionalTheology`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `CreationStructure` | structure | [L411](formal/Logos/ConditionalTheology.lean#L411) | `structure CreationStructure (Subj : Type) (Ent : Type) where` | —  |
| `IncarnationalStructure` | structure | [L368](formal/Logos/ConditionalTheology.lean#L368) | `structure IncarnationalStructure (Subj : Type) (Nature : Type) (HasNature : Subj` | —  |
| `InferenceStatus` | inductive | [L442](formal/Logos/ConditionalTheology.lean#L442) | `inductive InferenceStatus` | —  |
| `agency_closure_act_to_chooses` | theorem | [L55](formal/Logos/ConditionalTheology.lean#L55) | `theorem agency_closure_act_to_chooses (s : Subject) (p : Prop) (hAct : Act s p) ` | {AxIntentionalChoice, Initiates, Means, State, Subject}  |
| `agency_closure_act_to_freeSubject` | theorem | [L64](formal/Logos/ConditionalTheology.lean#L64) | `theorem agency_closure_act_to_freeSubject (s : Subject) (p : Prop) (hAct : Act s` | {AxIntentionalChoice, Initiates, Means, State, Subject}  |
| `agency_closure_act_to_freewill` | theorem | [L59](formal/Logos/ConditionalTheology.lean#L59) | `theorem agency_closure_act_to_freewill (s : Subject) (p : Prop) (hAct : Act s p)` | {AxIntentionalChoice, Initiates, Means, State, Subject}  |
| `agency_closure_act_to_intentionalSubject` | theorem | [L68](formal/Logos/ConditionalTheology.lean#L68) | `theorem agency_closure_act_to_intentionalSubject (s : Subject) (p : Prop) (hAct ` | {Initiates, Means, State, Subject}  |
| `freewill_not_entails_necessity` | theorem | [L153](formal/Logos/ConditionalTheology.lean#L153) | `theorem freewill_not_entails_necessity : ∃ (Subj : Type) (Chooses : Subj → Prop ` | {}  |
| `freewill_not_entails_normativity` | theorem | [L99](formal/Logos/ConditionalTheology.lean#L99) | `theorem freewill_not_entails_normativity : ∃ (Subj : Type) (Chooses : Subj → Pro` | {}  |
| `freewill_not_entails_persistence` | theorem | [L144](formal/Logos/ConditionalTheology.lean#L144) | `theorem freewill_not_entails_persistence : ∃ (Subj : Type) (Chooses : Subj → Pro` | {}  |
| `freewill_not_entails_rationality` | theorem | [L88](formal/Logos/ConditionalTheology.lean#L88) | `theorem freewill_not_entails_rationality : ∃ (Subj : Type) (Chooses : Subj → Pro` | {}  |
| `freewill_not_entails_reflexive_subjectivity` | theorem | [L126](formal/Logos/ConditionalTheology.lean#L126) | `theorem freewill_not_entails_reflexive_subjectivity : ∃ (Subj : Type) (Chooses :` | {}  |
| `freewill_not_entails_relationality` | theorem | [L135](formal/Logos/ConditionalTheology.lean#L135) | `theorem freewill_not_entails_relationality : ∃ (Subj : Type) (Chooses : Subj → P` | {}  |
| `freewill_not_entails_teleology` | theorem | [L117](formal/Logos/ConditionalTheology.lean#L117) | `theorem freewill_not_entails_teleology : ∃ (Subj : Type) (Chooses : Subj → Prop ` | {}  |
| `freewill_not_entails_value` | theorem | [L108](formal/Logos/ConditionalTheology.lean#L108) | `theorem freewill_not_entails_value : ∃ (Subj : Type) (Chooses : Subj → Prop → Pr` | {}  |
| `TrinitarianStructure` | structure | [L308](formal/Logos/ConditionalTheology.lean#L308) | `structure TrinitarianStructure (Subj : Type) (Ent : Type) where` | —  |
| `a14_not_eliminates_infinite_ground_chain` | theorem | [L183](formal/Logos/ConditionalTheology.lean#L183) | `theorem a14_not_eliminates_infinite_ground_chain : ∃ (Subj : Type) (Ent : Type) ` | —  |
| `a14_not_entails_plurality` | theorem | [L257](formal/Logos/ConditionalTheology.lean#L257) | `theorem a14_not_entails_plurality : ∃ (Subj : Type) (Chooses : Subj → Prop → Pro` | —  |
| `a14_plus_ultimate_ground_not_entails_personal_ultimate_ground` | theorem | [L229](formal/Logos/ConditionalTheology.lean#L229) | `theorem a14_plus_ultimate_ground_not_entails_personal_ultimate_ground : ∃ (Subj ` | —  |
| `edge_Act_to_Chooses` | def | [L451](formal/Logos/ConditionalTheology.lean#L451) | `def edge_Act_to_Chooses : InferenceStatus` | —  |
| `edge_Chooses_to_FreeWill` | def | [L452](formal/Logos/ConditionalTheology.lean#L452) | `def edge_Chooses_to_FreeWill : InferenceStatus` | —  |
| `edge_Creation_to_Incarnation` | def | [L462](formal/Logos/ConditionalTheology.lean#L462) | `def edge_Creation_to_Incarnation : InferenceStatus` | —  |
| `edge_DivineGround_to_Creation` | def | [L461](formal/Logos/ConditionalTheology.lean#L461) | `def edge_DivineGround_to_Creation : InferenceStatus` | —  |
| `edge_FreeWill_to_Rationality` | def | [L453](formal/Logos/ConditionalTheology.lean#L453) | `def edge_FreeWill_to_Rationality : InferenceStatus` | —  |
| `edge_Love_to_Trinity` | def | [L460](formal/Logos/ConditionalTheology.lean#L460) | `def edge_Love_to_Trinity : InferenceStatus` | —  |
| `edge_NecessaryGround_to_UltimateGround` | def | [L456](formal/Logos/ConditionalTheology.lean#L456) | `def edge_NecessaryGround_to_UltimateGround : InferenceStatus` | —  |
| `edge_NecessaryTruth_to_SomeGround` | def | [L454](formal/Logos/ConditionalTheology.lean#L454) | `def edge_NecessaryTruth_to_SomeGround : InferenceStatus` | —  |
| `edge_PersonalGround_to_Plurality` | def | [L458](formal/Logos/ConditionalTheology.lean#L458) | `def edge_PersonalGround_to_Plurality : InferenceStatus` | —  |
| `edge_Plurality_to_Love` | def | [L459](formal/Logos/ConditionalTheology.lean#L459) | `def edge_Plurality_to_Love : InferenceStatus` | —  |
| `edge_SomeGround_to_NecessaryGround` | def | [L455](formal/Logos/ConditionalTheology.lean#L455) | `def edge_SomeGround_to_NecessaryGround : InferenceStatus` | —  |
| `edge_UltimateGround_to_PersonalGround` | def | [L457](formal/Logos/ConditionalTheology.lean#L457) | `def edge_UltimateGround_to_PersonalGround : InferenceStatus` | —  |
| `free_agency_and_plurality_not_entails_love` | theorem | [L282](formal/Logos/ConditionalTheology.lean#L282) | `theorem free_agency_and_plurality_not_entails_love : ∃ (Subj : Type) (Chooses : ` | —  |
| `free_agency_not_entails_ultimate_ground` | theorem | [L201](formal/Logos/ConditionalTheology.lean#L201) | `theorem free_agency_not_entails_ultimate_ground : ∃ (Subj : Type) (Ent : Type) (` | —  |
| `necessary_ground_not_entails_contingent_creation` | theorem | [L420](formal/Logos/ConditionalTheology.lean#L420) | `theorem necessary_ground_not_entails_contingent_creation : ∃ (Subj : Type) (Ent ` | —  |
| `preceding_theory_not_entails_incarnation` | theorem | [L380](formal/Logos/ConditionalTheology.lean#L380) | `theorem preceding_theory_not_entails_incarnation : ∃ (Subj : Type) (Nature : Typ` | —  |
| `preceding_theory_not_entails_trinity` | theorem | [L329](formal/Logos/ConditionalTheology.lean#L329) | `theorem preceding_theory_not_entails_trinity : ∃ (Subj : Type) (Ent : Type) (Cho` | —  |
| `theological_dependency_ledger` | theorem | [L467](formal/Logos/ConditionalTheology.lean#L467) | `theorem theological_dependency_ledger : edge_Act_to_Chooses = InferenceStatus.PR` | —  |

### `Logos.Core`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `IsFalse` | def | [L52](formal/Logos/Core.lean#L52) | `def IsFalse (p : Prop) : Prop` | {}  |
| `N_F` | def | [L49](formal/Logos/Core.lean#L49) | `def N_F : Prop` | {}  |
| `N_T` | def | [L46](formal/Logos/Core.lean#L46) | `def N_T : Prop` | {}  |
| `T` | def | [L40](formal/Logos/Core.lean#L40) | `def T (p : Prop) : Prop` | {}  |
| `atomicTruthWitnessed` | theorem | [L85](formal/Logos/Core.lean#L85) | `theorem atomicTruthWitnessed : T True` | {} → C4 |
| `atomicWitnessFalsehood` | theorem | [L117](formal/Logos/Core.lean#L117) | `theorem atomicWitnessFalsehood : IsFalse False` | {}  |
| `bivalence` | theorem | [L186](formal/Logos/Core.lean#L186) | `theorem bivalence : ∀ p : Prop, T p ∨ IsFalse p` | {CL} → C12 |
| `excludedMiddle` | theorem | [L174](formal/Logos/Core.lean#L174) | `theorem excludedMiddle : ∀ p : Prop, T (p ∨ ¬ p)` | {CL} → C10 |
| `greatResult` | theorem | [L156](formal/Logos/Core.lean#L156) | `theorem greatResult : ∃ p q : Prop, T p ∧ IsFalse q` | {} → C8 |
| `negatedAbsolutes` | theorem | [L129](formal/Logos/Core.lean#L129) | `theorem negatedAbsolutes : ¬ (N_T ∨ N_F)` | {} → C35 |
| `noBothTrueAndFalse` | theorem | [L162](formal/Logos/Core.lean#L162) | `theorem noBothTrueAndFalse : ∀ p : Prop, ¬ (T p ∧ IsFalse p)` | {} → C9 |
| `nonContradiction` | theorem | [L180](formal/Logos/Core.lean#L180) | `theorem nonContradiction : ∀ p : Prop, T (¬ (p ∧ ¬ p))` | {} → C11 |
| `notEverythingTrue` | theorem | [L103](formal/Logos/Core.lean#L103) | `theorem notEverythingTrue : ¬ N_F` | {} → C6 |
| `notNothingTrue` | theorem | [L69](formal/Logos/Core.lean#L69) | `theorem notNothingTrue : ¬ N_T` | {} → C2 |
| `nothingFalseRefutes` | theorem | [L94](formal/Logos/Core.lean#L94) | `theorem nothingFalseRefutes : ¬ T N_F` | {} → C5 |
| `nothingTrueRefutes` | theorem | [L61](formal/Logos/Core.lean#L61) | `theorem nothingTrueRefutes : ¬ T N_T` | {} → C1 |
| `rightWrongDistinction` | theorem | [L145](formal/Logos/Core.lean#L145) | `theorem rightWrongDistinction : ¬ N_T ∧ ¬ N_F` | {} → C36 |
| `someFalse` | theorem | [L111](formal/Logos/Core.lean#L111) | `theorem someFalse : ∃ q : Prop, IsFalse q` | {} → C7 |
| `someTrue` | theorem | [L77](formal/Logos/Core.lean#L77) | `theorem someTrue : ∃ p : Prop, T p` | {CL} → C3 |
| `someTruthAndSomeFalsehood` | theorem | [L137](formal/Logos/Core.lean#L137) | `theorem someTruthAndSomeFalsehood : (∃ p : Prop, T p) ∧ (∃ q : Prop, IsFalse q)` | {CL}  |
| `tschema` | theorem | [L43](formal/Logos/Core.lean#L43) | `theorem tschema (p : Prop) : T p ↔ p` | {}  |

### `Logos.CountermodelMeanings`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `ActWithoutSubject_refutes` | def | [L16](formal/Logos/CountermodelMeanings.lean#L16) | `def ActWithoutSubject_refutes : String` | —  |
| `ActWithoutSubject_survives` | def | [L19](formal/Logos/CountermodelMeanings.lean#L19) | `def ActWithoutSubject_survives : String` | —  |
| `ContentWithoutPerson_refutes` | def | [L62](formal/Logos/CountermodelMeanings.lean#L62) | `def ContentWithoutPerson_refutes : String` | —  |
| `ContentWithoutPerson_survives` | def | [L65](formal/Logos/CountermodelMeanings.lean#L65) | `def ContentWithoutPerson_survives : String` | —  |
| `ImpersonalUltimateGround_refutes` | def | [L110](formal/Logos/CountermodelMeanings.lean#L110) | `def ImpersonalUltimateGround_refutes : String` | —  |
| `ImpersonalUltimateGround_survives` | def | [L113](formal/Logos/CountermodelMeanings.lean#L113) | `def ImpersonalUltimateGround_survives : String` | —  |
| `InfiniteGroundChain_refutes` | def | [L102](formal/Logos/CountermodelMeanings.lean#L102) | `def InfiniteGroundChain_refutes : String` | —  |
| `InfiniteGroundChain_survives` | def | [L105](formal/Logos/CountermodelMeanings.lean#L105) | `def InfiniteGroundChain_survives : String` | —  |
| `NoFreeWill_refutes` | def | [L46](formal/Logos/CountermodelMeanings.lean#L46) | `def NoFreeWill_refutes : String` | —  |
| `NoFreeWill_survives` | def | [L49](formal/Logos/CountermodelMeanings.lean#L49) | `def NoFreeWill_survives : String` | —  |
| `NoPerson_refutes` | def | [L38](formal/Logos/CountermodelMeanings.lean#L38) | `def NoPerson_refutes : String` | —  |
| `NoPerson_survives` | def | [L41](formal/Logos/CountermodelMeanings.lean#L41) | `def NoPerson_survives : String` | —  |
| `PersonNotNecessary_refutes` | def | [L86](formal/Logos/CountermodelMeanings.lean#L86) | `def PersonNotNecessary_refutes : String` | —  |
| `PersonNotNecessary_survives` | def | [L89](formal/Logos/CountermodelMeanings.lean#L89) | `def PersonNotNecessary_survives : String` | —  |
| `PluralityWithoutLove_refutes` | def | [L118](formal/Logos/CountermodelMeanings.lean#L118) | `def PluralityWithoutLove_refutes : String` | —  |
| `PluralityWithoutLove_survives` | def | [L121](formal/Logos/CountermodelMeanings.lean#L121) | `def PluralityWithoutLove_survives : String` | —  |
| `SubjectNecessityNotEntity_refutes` | def | [L78](formal/Logos/CountermodelMeanings.lean#L78) | `def SubjectNecessityNotEntity_refutes : String` | —  |
| `SubjectNecessityNotEntity_survives` | def | [L81](formal/Logos/CountermodelMeanings.lean#L81) | `def SubjectNecessityNotEntity_survives : String` | —  |
| `SubjectWithoutPerson_refutes` | def | [L32](formal/Logos/CountermodelMeanings.lean#L32) | `def SubjectWithoutPerson_refutes : String` | —  |
| `SubjectWithoutPerson_survives` | def | [L35](formal/Logos/CountermodelMeanings.lean#L35) | `def SubjectWithoutPerson_survives : String` | —  |
| `UnitPlurality_refutes` | def | [L54](formal/Logos/CountermodelMeanings.lean#L54) | `def UnitPlurality_refutes : String` | —  |
| `UnitPlurality_survives` | def | [L57](formal/Logos/CountermodelMeanings.lean#L57) | `def UnitPlurality_survives : String` | —  |
| `VeridicalMeaning_refutes` | def | [L94](formal/Logos/CountermodelMeanings.lean#L94) | `def VeridicalMeaning_refutes : String` | —  |
| `VeridicalMeaning_survives` | def | [L97](formal/Logos/CountermodelMeanings.lean#L97) | `def VeridicalMeaning_survives : String` | —  |
| `WeakActWithoutMeaning_refutes` | def | [L24](formal/Logos/CountermodelMeanings.lean#L24) | `def WeakActWithoutMeaning_refutes : String` | —  |
| `WeakActWithoutMeaning_survives` | def | [L27](formal/Logos/CountermodelMeanings.lean#L27) | `def WeakActWithoutMeaning_survives : String` | —  |
| `WorldwiseTruthmaking_refutes` | def | [L70](formal/Logos/CountermodelMeanings.lean#L70) | `def WorldwiseTruthmaking_refutes : String` | —  |
| `WorldwiseTruthmaking_survives` | def | [L73](formal/Logos/CountermodelMeanings.lean#L73) | `def WorldwiseTruthmaking_survives : String` | —  |

### `Logos.GroundPerson`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `AxGroundBearing` | theorem | [L84](formal/Logos/GroundPerson.lean#L84) | `theorem AxGroundBearing {e : Entity} {f : Prop} : GroundProp e f → Realizes e f` | {GroundProp, Subject}  |
| `AxPersonalGround` | axiom | [L107](formal/Logos/GroundPerson.lean#L107) | `axiom AxPersonalGround : ∀ {f : Prop}, IsPresentPersonalFeature f → ∃ e : Entity` | {AxPersonalGround, GroundProp, Initiates, Means, State, Subject}  |
| `GroundPrincipleProp` | axiom | [L79](formal/Logos/GroundPerson.lean#L79) | `axiom GroundPrincipleProp : ∀ {f : Prop}, T f → ∃ e : Entity, GroundProp e f` | {GroundPrincipleProp, GroundProp, Subject}  |
| `GroundProp` | axiom | [L60](formal/Logos/GroundPerson.lean#L60) | `axiom GroundProp : Entity → Prop → Prop` | {GroundProp, Subject}  |
| `IsPresentPersonalFeature` | def | [L89](formal/Logos/GroundPerson.lean#L89) | `def IsPresentPersonalFeature (f : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `Personal` | def | [L93](formal/Logos/GroundPerson.lean#L93) | `def Personal (e : Entity) : Prop` | {GroundProp, Initiates, Means, State, Subject}  |
| `Realizes` | def | [L66](formal/Logos/GroundPerson.lean#L66) | `def Realizes (e : Entity) (f : Prop) : Prop` | {GroundProp, Subject}  |
| `T8_personalGround` | theorem | [L112](formal/Logos/GroundPerson.lean#L112) | `theorem T8_personalGround {f : Prop} (hf : IsPresentPersonalFeature f) : ∃ e : E` | {AxPersonalGround, GroundProp, Initiates, Means, State, Subject} → C32 |
| `necessary_truth_has_necessary_grounder` | theorem | [L125](formal/Logos/GroundPerson.lean#L125) | `theorem necessary_truth_has_necessary_grounder {τ : Form} (hτ : Logos.Truthmaker` | {AxGlobalGround, Ground, Subject} → C34 |
| `present_feature_is_grounded` | theorem | [L120](formal/Logos/GroundPerson.lean#L120) | `theorem present_feature_is_grounded {f : Prop} (ht : T f) (_hf : IsPresentPerson` | {GroundPrincipleProp, GroundProp, Initiates, Means, State, Subject} → C33 |

### `Logos.HostileSemantics`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `ActDatum` | def | [L2047](formal/Logos/HostileSemantics.lean#L2047) | `def ActDatum (I : SelectionSignature) : Prop` | —  |
| `ActOntology` | structure | [L338](formal/Logos/HostileSemantics.lean#L338) | `structure ActOntology where` | —  |
| `AssertsDatum` | def | [L2050](formal/Logos/HostileSemantics.lean#L2050) | `def AssertsDatum (I : SelectionSignature) : Prop` | —  |
| `BareMeansDatum` | def | [L2193](formal/Logos/HostileSemantics.lean#L2193) | `def BareMeansDatum (I : MeansSelectionSignature) : Prop` | —  |
| `DeliberateChoiceDatum` | def | [L2056](formal/Logos/HostileSemantics.lean#L2056) | `def DeliberateChoiceDatum (I : SelectionSignature) : Prop` | —  |
| `FreeWillDatum` | def | [L2062](formal/Logos/HostileSemantics.lean#L2062) | `def FreeWillDatum (I : SelectionSignature) : Prop` | —  |
| `GenuineChoiceDatum` | def | [L2059](formal/Logos/HostileSemantics.lean#L2059) | `def GenuineChoiceDatum (I : SelectionSignature) : Prop` | —  |
| `CoreSignature` | structure | [L86](formal/Logos/HostileSemantics.lean#L86) | `structure CoreSignature where` | —  |
| `FreeWillExistence` | def | [L109](formal/Logos/HostileSemantics.lean#L109) | `def FreeWillExistence (I : CoreSignature) : Prop` | {}  |
| `PersonExistence` | def | [L103](formal/Logos/HostileSemantics.lean#L103) | `def PersonExistence (I : CoreSignature) : Prop` | {}  |
| `SubstantiveAuto` | def | [L234](formal/Logos/HostileSemantics.lean#L234) | `def SubstantiveAuto (I : SubstantivePersonhood) : Prop` | {}  |
| `SubstantiveDatum` | def | [L229](formal/Logos/HostileSemantics.lean#L229) | `def SubstantiveDatum (I : SubstantivePersonhood) : Prop` | {}  |
| `SubstantiveDegree` | def | [L235](formal/Logos/HostileSemantics.lean#L235) | `def SubstantiveDegree (I : SubstantivePersonhood) : Prop` | {}  |
| `SubstantiveMind` | def | [L232](formal/Logos/HostileSemantics.lean#L232) | `def SubstantiveMind (I : SubstantivePersonhood) : Prop` | {}  |
| `SubstantivePersonhood` | structure | [L221](formal/Logos/HostileSemantics.lean#L221) | `structure SubstantivePersonhood where` | —  |
| `SubstantiveRatio` | def | [L233](formal/Logos/HostileSemantics.lean#L233) | `def SubstantiveRatio (I : SubstantivePersonhood) : Prop` | {}  |
| `TwoPersons` | def | [L106](formal/Logos/HostileSemantics.lean#L106) | `def TwoPersons (I : CoreSignature) : Prop` | {}  |
| `act_exists_of_act` | theorem | [L332](formal/Logos/HostileSemantics.lean#L332) | `theorem act_exists_of_act (hAct : ∃ s : S, ∃ p : Prop, A s p) : ∃ s : S, ∃ p : P` | {}  |
| `not_entails_content_person` | theorem | [L184](formal/Logos/HostileSemantics.lean#L184) | `theorem not_entails_content_person : ¬ (∀ (S : Type) (Means : S → Prop → Prop) (` | {}  |
| `not_entails_decoupled_freewill` | theorem | [L167](formal/Logos/HostileSemantics.lean#L167) | `theorem not_entails_decoupled_freewill : ¬ (∀ I : CoreSignature, Γ_act I ∧ (∀ s ` | {}  |
| `not_entails_person` | theorem | [L122](formal/Logos/HostileSemantics.lean#L122) | `theorem not_entails_person : ¬ (∀ I : CoreSignature, Γ_person I → PersonExistenc` | {}  |
| `not_entails_plurality` | theorem | [L138](formal/Logos/HostileSemantics.lean#L138) | `theorem not_entails_plurality : ¬ (∀ I : CoreSignature, Γ_act I ∧ (∃ s : I.Subje` | {}  |
| `not_entails_substantive_autonomy` | theorem | [L280](formal/Logos/HostileSemantics.lean#L280) | `theorem not_entails_substantive_autonomy : ¬ (∀ I : SubstantivePersonhood, Subst` | {}  |
| `not_entails_substantive_intentionality` | theorem | [L242](formal/Logos/HostileSemantics.lean#L242) | `theorem not_entails_substantive_intentionality : ¬ (∀ I : SubstantivePersonhood,` | {}  |
| `not_entails_substantive_person` | theorem | [L302](formal/Logos/HostileSemantics.lean#L302) | `theorem not_entails_substantive_person : ¬ (∀ I : SubstantivePersonhood, Substan` | {}  |
| `not_entails_substantive_rationality` | theorem | [L261](formal/Logos/HostileSemantics.lean#L261) | `theorem not_entails_substantive_rationality : ¬ (∀ I : SubstantivePersonhood, Su` | {}  |
| `subject_exists_of_act` | theorem | [L327](formal/Logos/HostileSemantics.lean#L327) | `theorem subject_exists_of_act (hAct : ∃ s : S, ∃ p : Prop, A s p) : ∃ _s : S, Tr` | {}  |
| `Γ_act` | def | [L94](formal/Logos/HostileSemantics.lean#L94) | `def Γ_act (I : CoreSignature) : Prop` | {}  |
| `Γ_means` | def | [L97](formal/Logos/HostileSemantics.lean#L97) | `def Γ_means (I : CoreSignature) : Prop` | {}  |
| `Γ_person` | def | [L100](formal/Logos/HostileSemantics.lean#L100) | `def Γ_person (I : CoreSignature) : Prop` | {}  |
| `MeansSelectionDatum` | def | [L2196](formal/Logos/HostileSemantics.lean#L2196) | `def MeansSelectionDatum (I : MeansSelectionSignature) : Prop` | —  |
| `MeansSelectionSignature` | structure | [L2188](formal/Logos/HostileSemantics.lean#L2188) | `structure MeansSelectionSignature where` | —  |
| `SelectionDatum` | def | [L2053](formal/Logos/HostileSemantics.lean#L2053) | `def SelectionDatum (I : SelectionSignature) : Prop` | —  |
| `SelectionSignature` | structure | [L2038](formal/Logos/HostileSemantics.lean#L2038) | `structure SelectionSignature where` | —  |
| `act_not_entails_asserts` | theorem | [L2068](formal/Logos/HostileSemantics.lean#L2068) | `theorem act_not_entails_asserts : ¬ (∀ I : SelectionSignature, ActDatum I → Asse` | —  |
| `act_not_entails_selects` | theorem | [L2089](formal/Logos/HostileSemantics.lean#L2089) | `theorem act_not_entails_selects : ¬ (∀ I : SelectionSignature, ActDatum I → Sele` | —  |
| `chooses_not_entails_deliberateChoice` | theorem | [L2111](formal/Logos/HostileSemantics.lean#L2111) | `theorem chooses_not_entails_deliberateChoice : ¬ (∀ I : SelectionSignature, Genu` | —  |
| `not_entails_selection_of_bare_means` | theorem | [L2200](formal/Logos/HostileSemantics.lean#L2200) | `theorem not_entails_selection_of_bare_means : ¬ (∀ I : MeansSelectionSignature, ` | —  |
| `selection_not_entails_deliberate_choice` | theorem | [L2131](formal/Logos/HostileSemantics.lean#L2131) | `theorem selection_not_entails_deliberate_choice : ¬ (∀ I : SelectionSignature, S` | —  |
| `selection_not_entails_freewill` | theorem | [L2170](formal/Logos/HostileSemantics.lean#L2170) | `theorem selection_not_entails_freewill : ¬ (∀ I : SelectionSignature, SelectionD` | —  |
| `selection_not_entails_genuine_choice` | theorem | [L2151](formal/Logos/HostileSemantics.lean#L2151) | `theorem selection_not_entails_genuine_choice : ¬ (∀ I : SelectionSignature, Sele` | —  |

### `Logos.Initiation`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Branches` | def | [L23](formal/Logos/Initiation.lean#L23) | `def Branches {α β : Type} (R : α → β → Prop) : Prop` | {}  |
| `IsTransfer` | def | [L19](formal/Logos/Initiation.lean#L19) | `def IsTransfer {α β : Type} (R : α → β → Prop) : Prop` | {}  |
| `branches_not_transfer` | theorem | [L27](formal/Logos/Initiation.lean#L27) | `theorem branches_not_transfer {α β : Type} {R : α → β → Prop} (h : Branches R) :` | {} → C63 |

### `Logos.Love`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Lovable` | def | [L75](formal/Logos/Love.lean#L75) | `def Lovable (t : Subject) : Prop` | {Means, Subject}  |
| `Loves` | def | [L42](formal/Logos/Love.lean#L42) | `def Loves (s t : Subject) : Prop` | {Subject}  |
| `PersonStabilityPrinciple` | def | [L90](formal/Logos/Love.lean#L90) | `def PersonStabilityPrinciple : Prop` | {Means, Subject}  |
| `PluralityLovePrinciple` | def | [L94](formal/Logos/Love.lean#L94) | `def PluralityLovePrinciple : Prop` | {Means, Subject}  |
| `T13_someoneLovable` | theorem | [L81](formal/Logos/Love.lean#L81) | `theorem T13_someoneLovable : ∃ s t : Subject, Person s ∧ Person t ∧ s ≠ t ∧ Lova` | {AxTwoSubjects, Means, Subject} → C41 |
| `T14_content_conditional` | theorem | [L151](formal/Logos/Love.lean#L151) | `theorem T14_content_conditional (hLove : PluralityLovePrinciple) : ∃ s₁ s₂ : Sub` | {AxTwoSubjects, Means, Subject} → C43 |
| `T14_eternalRelation_conditional` | theorem | [L119](formal/Logos/Love.lean#L119) | `theorem T14_eternalRelation_conditional (hStab : PersonStabilityPrinciple) (hLov` | {AxTwoSubjects, Means, Subject} → C42 |
| `T14_square_conditional` | theorem | [L141](formal/Logos/Love.lean#L141) | `theorem T14_square_conditional (hStab : PersonStabilityPrinciple) (hLove : Plura` | {AxTwoSubjects, Means, Subject} → C45 |
| `T14_world_conditional` | theorem | [L129](formal/Logos/Love.lean#L129) | `theorem T14_world_conditional (hStab : PersonStabilityPrinciple) (hLove : Plural` | {AxTwoSubjects, Means, Subject} → C44 |
| `love_affects` | theorem | [L61](formal/Logos/Love.lean#L61) | `theorem love_affects : ∀ {s t : Subject}, Loves s t → Affects s t` | {Subject}  |
| `love_helps` | theorem | [L47](formal/Logos/Love.lean#L47) | `theorem love_helps : ∀ {s t : Subject}, Loves s t → Helps s t` | {Subject} → C86 |
| `love_not_harms` | theorem | [L54](formal/Logos/Love.lean#L54) | `theorem love_not_harms : ∀ {s t : Subject}, Loves s t → ¬ Harms s t` | {Subject}  |
| `loves_of_helps` | theorem | [L69](formal/Logos/Love.lean#L69) | `theorem loves_of_helps : ∀ {s t : Subject}, Helps s t → Loves s t` | {Subject}  |
| `necessaryPersonExists_conditional` | theorem | [L98](formal/Logos/Love.lean#L98) | `theorem necessaryPersonExists_conditional (hStab : PersonStabilityPrinciple) (hA` | {Initiates, Means, State, Subject} → C77 |
| `necessary_entity_exists_conditional` | theorem | [L109](formal/Logos/Love.lean#L109) | `theorem necessary_entity_exists_conditional (hStab : PersonStabilityPrinciple) (` | {Initiates, Means, State, Subject} → C92 |

### `Logos.Modal`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `AxGlobalGround` | axiom | [L67](formal/Logos/Modal.lean#L67) | `axiom AxGlobalGround : ∀ (φ : Form), □ φ → ∃ e : Entity, ∀ w : World, ExistsAt w` | {AxGlobalGround, Ground, Subject}  |
| `Contingent` | def | [L50](formal/Logos/Modal.lean#L50) | `def Contingent (e : Entity) : Prop` | {Subject}  |
| `NecessaryEntity` | def | [L47](formal/Logos/Modal.lean#L47) | `def NecessaryEntity (e : Entity) : Prop` | {Subject}  |
| `T7_excludedMiddleInstance` | theorem | [L80](formal/Logos/Modal.lean#L80) | `theorem T7_excludedMiddleInstance (φ : Form) : ∃ e : Entity, NecessaryEntity e ∧` | {AxGlobalGround, Ground, Subject, CL} → C19 |
| `T7_necessaryReality` | theorem | [L74](formal/Logos/Modal.lean#L74) | `theorem T7_necessaryReality {τ : Form} (hτ : □ τ) : ∃ e : Entity, NecessaryEntit` | {AxGlobalGround, Ground, Subject} → C18 |
| `actualWorld` | def | [L44](formal/Logos/Modal.lean#L44) | `def actualWorld : World` | {}  |
| `necessary_entity_exists_of_necessary_subject` | theorem | [L115](formal/Logos/Modal.lean#L115) | `theorem necessary_entity_exists_of_necessary_subject {s : Subject} (h : Necessar` | {Subject}  |
| `noNecessaryTruthIfAllContingent` | theorem | [L86](formal/Logos/Modal.lean#L86) | `theorem noNecessaryTruthIfAllContingent : (∀ e : Entity, Contingent e) → ∀ φ : F` | {AxGlobalGround, Ground, Subject} → C20 |
| `subject_nec_entity_nec` | theorem | [L103](formal/Logos/Modal.lean#L103) | `theorem subject_nec_entity_nec (s : Subject) : NecessarySubject s → NecessaryEnt` | {Subject} → C91 |
| `subject_nec_entity_nec_iff` | theorem | [L110](formal/Logos/Modal.lean#L110) | `theorem subject_nec_entity_nec_iff (s : Subject) : NecessarySubject s ↔ Necessar` | {Subject}  |

### `Logos.Necessity`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Dia` | def | [L69](formal/Logos/Necessity.lean#L69) | `def ◇(p : Prop) : Prop` | {}  |
| `Necessity` | def | [L51](formal/Logos/Necessity.lean#L51) | `def □(p : Prop) : Prop` | {}  |
| `NecessityPH` | def | [L94](formal/Logos/Necessity.lean#L94) | `def □ₚ(P : WProp) : Prop` | {}  |
| `WProp` | abbrev | [L86](formal/Logos/Necessity.lean#L86) | `abbrev WProp : Type` | {}  |
| `dia_def` | theorem | [L72](formal/Logos/Necessity.lean#L72) | `theorem dia_def {p : Prop} : ◇ p ↔ ¬ □(¬ p)` | {}  |
| `nec4` | theorem | [L64](formal/Logos/Necessity.lean#L64) | `theorem nec4 : ∀ {p : Prop}, □ p → □(□ p)` | {}  |
| `nec4PH` | theorem | [L108](formal/Logos/Necessity.lean#L108) | `theorem nec4PH {P : WProp} : □ₚ P → □ₚ(fun _ => □ₚ P)` | {}  |
| `necDistinction` | theorem | [L116](formal/Logos/Necessity.lean#L116) | `theorem necDistinction : □(¬ N_T ∧ ¬ N_F)` | {} → FAITH-1 |
| `necDistinction_content` | theorem | [L120](formal/Logos/Necessity.lean#L120) | `theorem necDistinction_content : ¬ N_T ∧ ¬ N_F` | {}  |
| `necK` | theorem | [L54](formal/Logos/Necessity.lean#L54) | `theorem necK : ∀ {p q : Prop}, □(p → q) → □ p → □ q` | {}  |
| `necKPH` | theorem | [L97](formal/Logos/Necessity.lean#L97) | `theorem necKPH {P Q : WProp} : □ₚ(fun w => P w → Q w) → □ₚ P → □ₚ Q` | {}  |
| `necMP` | theorem | [L78](formal/Logos/Necessity.lean#L78) | `theorem necMP {p q : Prop} (hpq : □(p → q)) (hp : □ p) : □ q` | {}  |
| `necT` | theorem | [L59](formal/Logos/Necessity.lean#L59) | `theorem necT : ∀ {p : Prop}, □ p → p` | {}  |
| `necTPH` | theorem | [L102](formal/Logos/Necessity.lean#L102) | `theorem necTPH {P : WProp} : □ₚ P → P someWorld` | {}  |
| `nec_apply` | theorem | [L75](formal/Logos/Necessity.lean#L75) | `theorem nec_apply {p : Prop} (hp : □ p) : p` | {}  |
| `someWorld` | def | [L45](formal/Logos/Necessity.lean#L45) | `def someWorld : World` | {}  |

### `Logos.Order`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Correct` | def | [L30](formal/Logos/Order.lean#L30) | `def Correct (s : Subject) (p : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `Fallible` | def | [L119](formal/Logos/Order.lean#L119) | `def Fallible (_s : Subject) (p : Prop) : Prop` | {Subject}  |
| `Incorrect` | def | [L51](formal/Logos/Order.lean#L51) | `def Incorrect (s : Subject) (p : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `NoAct` | def | [L200](formal/Logos/Order.lean#L200) | `def NoAct : Prop` | {Initiates, Means, State, Subject}  |
| `T6_fallibility` | theorem | [L135](formal/Logos/Order.lean#L135) | `theorem T6_fallibility : ¬ (∀ s : Subject, ∀ p : Prop, Fallible s p → T p)` | {AxTwoSubjects, Means, Subject} → C28 |
| `T6_truthTranscendsWill` | theorem | [L144](formal/Logos/Order.lean#L144) | `theorem T6_truthTranscendsWill : ¬ (∀ s : Subject, ∀ p : Prop, Fallible s p ↔ T ` | {AxTwoSubjects, Means, Subject} → C29 |
| `act_iff_asserts_or_incorrect` | theorem | [L57](formal/Logos/Order.lean#L57) | `theorem act_iff_asserts_or_incorrect (s : Subject) (p : Prop) : A s p ↔ Asserts ` | {Initiates, Means, State, Subject, CL} → C101 |
| `act_iff_correct_or_incorrect` | theorem | [L69](formal/Logos/Order.lean#L69) | `theorem act_iff_correct_or_incorrect (s : Subject) (p : Prop) : A s p ↔ Correct ` | {Initiates, Means, State, Subject, CL}  |
| `consequence_preserves_truth` | theorem | [L195](formal/Logos/Order.lean#L195) | `theorem consequence_preserves_truth {p₁ p₂ q : Prop} (himp : p₁ → p₂ → q) (h1 : ` | {} → C31 |
| `correct_implies_selection` | theorem | [L35](formal/Logos/Order.lean#L35) | `theorem correct_implies_selection {s : Subject} {p : Prop} (h : Correct s p) : S` | {Initiates, Means, State, Subject}  |
| `correct_implies_selection_all_incompatible` | theorem | [L42](formal/Logos/Order.lean#L42) | `theorem correct_implies_selection_all_incompatible {s : Subject} {p q : Prop} (h` | {Initiates, Means, State, Subject}  |
| `correctness_distinct` | theorem | [L152](formal/Logos/Order.lean#L152) | `theorem correctness_distinct (hAct : ∃ s : Subject, ∃ p : Prop, A s p) : ¬ (∀ s ` | {Initiates, Means, State, Subject, CL} → C30 |
| `fallible_false` | theorem | [L127](formal/Logos/Order.lean#L127) | `theorem fallible_false : ∃ s : Subject, ∃ p : Prop, Fallible s p ∧ IsFalse p` | {AxTwoSubjects, Means, Subject}  |
| `judge_commits` | theorem | [L172](formal/Logos/Order.lean#L172) | `theorem judge_commits (hAct : ∃ s : Subject, ∃ p : Prop, A s p) : ∃ s : Subject,` | {Initiates, Means, State, Subject, CL} → C55 |
| `judgment_implies_act` | theorem | [L218](formal/Logos/Order.lean#L218) | `theorem judgment_implies_act {s : Subject} {p : Prop} (h : Correct s p ∨ Incorre` | {Initiates, Means, State, Subject}  |
| `judgment_implies_cogito` | theorem | [L230](formal/Logos/Order.lean#L230) | `theorem judgment_implies_cogito (h : (∃ s : Subject, ∃ p : Prop, Correct s p) ∨ ` | {Initiates, Means, State, Subject}  |
| `judgment_of_no_act_is_incorrect` | theorem | [L211](formal/Logos/Order.lean#L211) | `theorem judgment_of_no_act_is_incorrect (s : Subject) (h : Correct s NoAct ∨ Inc` | {Initiates, Means, State, Subject}  |
| `judgment_of_no_act_proves_act` | theorem | [L225](formal/Logos/Order.lean#L225) | `theorem judgment_of_no_act_proves_act (s : Subject) (h : Correct s NoAct ∨ Incor` | {Initiates, Means, State, Subject} → C84 |
| `no_correct_judgment_of_no_act` | theorem | [L204](formal/Logos/Order.lean#L204) | `theorem no_correct_judgment_of_no_act (s : Subject) : ¬ Correct s NoAct` | {Initiates, Means, State, Subject} → C83 |
| `rightDistinctWrong_implies_meaning` | theorem | [L107](formal/Logos/Order.lean#L107) | `theorem rightDistinctWrong_implies_meaning (h : (∃ s : Subject, ∃ p : Prop, Corr` | {Initiates, Means, State, Subject}  |
| `rightWrongDistinction_implies_meaning` | theorem | [L182](formal/Logos/Order.lean#L182) | `theorem rightWrongDistinction_implies_meaning (hAct : ∃ s : Subject, ∃ p : Prop,` | {Initiates, Means, State, Subject, CL}  |
| `rightWrong_implies_meaning` | theorem | [L91](formal/Logos/Order.lean#L91) | `theorem rightWrong_implies_meaning (h : (∃ s : Subject, ∃ p : Prop, Correct s p)` | {Initiates, Means, State, Subject} → C62 |

### `Logos.Person`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `CarriesLogicalFeature` | def | [L137](formal/Logos/Person.lean#L137) | `def CarriesLogicalFeature (a : Prop) : Prop` | {}  |
| `CarriesPersonalFeature` | def | [L133](formal/Logos/Person.lean#L133) | `def CarriesPersonalFeature (a : Prop) : Prop` | {Means, Subject}  |
| `HasFeature` | def | [L130](formal/Logos/Person.lean#L130) | `def HasFeature (a f : Prop) : Prop` | {}  |
| `Intentional` | def | [L53](formal/Logos/Person.lean#L53) | `def Intentional (s : Subject) : Prop` | {Means, Subject}  |
| `IntentionalSubject` | def | [L50](formal/Logos/Person.lean#L50) | `def IntentionalSubject (s : Subject) : Prop` | {Means, Subject}  |
| `Person` | def | [L62](formal/Logos/Person.lean#L62) | `def Person (s : Subject) : Prop` | {Means, Subject}  |
| `RationalAct` | def | [L127](formal/Logos/Person.lean#L127) | `def RationalAct (a : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `SubstantivePerson` | opaque | [L57](formal/Logos/Person.lean#L57) | `opaque SubstantivePerson : Subject → Prop` | —  |
| `act_implies_intentional` | theorem | [L77](formal/Logos/Person.lean#L77) | `theorem act_implies_intentional {s : Subject} {p : Prop} (h : Logos.Agency.Act s` | {Initiates, Means, State, Subject}  |
| `act_implies_intentionalSubject` | theorem | [L73](formal/Logos/Person.lean#L73) | `theorem act_implies_intentionalSubject {s : Subject} {p : Prop} (h : Logos.Agenc` | {Initiates, Means, State, Subject}  |
| `inseparability_24b` | theorem | [L143](formal/Logos/Person.lean#L143) | `theorem inseparability_24b : ∀ a : Prop, RationalAct a → (CarriesPersonalFeature` | {Initiates, Means, State, Subject, CL} → C25 |
| `intentionalSubject_exists_of_act` | theorem | [L101](formal/Logos/Person.lean#L101) | `theorem intentionalSubject_exists_of_act (h : ∃ s : Subject, ∃ p : Prop, Logos.A` | {Initiates, Means, State, Subject}  |
| `intentionalSubject_exists_of_assert` | theorem | [L113](formal/Logos/Person.lean#L113) | `theorem intentionalSubject_exists_of_assert {s : Subject} {p : Prop} (h : Logos.` | {Initiates, Means, State, Subject}  |
| `intentional_exists_of_act` | theorem | [L107](formal/Logos/Person.lean#L107) | `theorem intentional_exists_of_act (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.A` | {Initiates, Means, State, Subject}  |
| `intentional_exists_of_assert` | theorem | [L118](formal/Logos/Person.lean#L118) | `theorem intentional_exists_of_assert {s : Subject} {p : Prop} (h : Logos.Agency.` | {Initiates, Means, State, Subject}  |
| `intentional_implies_subjectExists_of_bridge` | theorem | [L93](formal/Logos/Person.lean#L93) | `theorem intentional_implies_subjectExists_of_bridge (hBridge : ∀ (s : Subject) (` | {Initiates, Means, State, Subject}  |
| `person_is_intentional` | theorem | [L66](formal/Logos/Person.lean#L66) | `theorem person_is_intentional (s : Subject) (h : Person s) : IntentionalSubject ` | {Means, Subject}  |
| `subjectExists_implies_intentional` | theorem | [L88](formal/Logos/Person.lean#L88) | `theorem subjectExists_implies_intentional (h : Logos.Agency.SubjectExists s) : I` | {Initiates, Means, State, Subject}  |
| `subjectExists_implies_intentionalSubject` | theorem | [L83](formal/Logos/Person.lean#L83) | `theorem subjectExists_implies_intentionalSubject (h : Logos.Agency.SubjectExists` | {Initiates, Means, State, Subject}  |

### `Logos.Plurality`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `EntityOf` | def | [L34](formal/Logos/Plurality.lean#L34) | `def EntityOf : Subject → Entity` | {Subject}  |
| `NecessarySubject` | def | [L37](formal/Logos/Plurality.lean#L37) | `def NecessarySubject (s : Subject) : Prop` | {Subject}  |
| `T12_directedPair_conditional` | theorem | [L124](formal/Logos/Plurality.lean#L124) | `theorem T12_directedPair_conditional (hAffect : Logos.Value.PersonsAffectPrincip` | {AxTwoSubjects, Means, Subject} → C47 |
| `T12_twoPersons` | theorem | [L44](formal/Logos/Plurality.lean#L44) | `theorem T12_twoPersons : ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂` | {AxTwoSubjects, Means, Subject} → C40 |
| `T1_of_assert` | theorem | [L88](formal/Logos/Plurality.lean#L88) | `theorem T1_of_assert {s : Subject} {p : Prop} (h : Logos.Agency.Asserts s p) : ∃` | {Initiates, Means, State, Subject}  |
| `T1_subjectExists` | theorem | [L67](formal/Logos/Plurality.lean#L67) | `theorem T1_subjectExists (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Act s p) :` | {Initiates, Means, State, Subject} → C21 |
| `T1_subjectExists_from_plurality` | theorem | [L103](formal/Logos/Plurality.lean#L103) | `theorem T1_subjectExists_from_plurality (hBridge : ∀ (s : Subject) (p : Prop), L` | {AxTwoSubjects, Initiates, Means, State, Subject}  |
| `T4_agentExists` | theorem | [L75](formal/Logos/Plurality.lean#L75) | `theorem T4_agentExists (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Act s p) : ∃` | {Initiates, Means, State, Subject} → C23 |
| `T4_agentExists_from_plurality` | theorem | [L111](formal/Logos/Plurality.lean#L111) | `theorem T4_agentExists_from_plurality (hBridge : ∀ (s : Subject) (p : Prop), Log` | {AxTwoSubjects, Initiates, Means, State, Subject}  |
| `T4_of_assert` | theorem | [L93](formal/Logos/Plurality.lean#L93) | `theorem T4_of_assert {s : Subject} {p : Prop} (h : Logos.Agency.Asserts s p) : ∃` | {Initiates, Means, State, Subject}  |
| `T5_intentionalSubjectExists` | theorem | [L83](formal/Logos/Plurality.lean#L83) | `theorem T5_intentionalSubjectExists (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency` | {Initiates, Means, State, Subject} → C24 |
| `T5_intentional_of_assert` | theorem | [L98](formal/Logos/Plurality.lean#L98) | `theorem T5_intentional_of_assert {s : Subject} {p : Prop} (h : Logos.Agency.Asse` | {Initiates, Means, State, Subject}  |
| `T5_personExists_from_plurality` | theorem | [L118](formal/Logos/Plurality.lean#L118) | `theorem T5_personExists_from_plurality : ∃ s : Subject, Person s` | {AxTwoSubjects, Means, Subject}  |
| `cogito_from_T12` | theorem | [L57](formal/Logos/Plurality.lean#L57) | `theorem cogito_from_T12 : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Means s p` | {AxTwoSubjects, Means, Subject} → C48 |
| `notAlone` | theorem | [L50](formal/Logos/Plurality.lean#L50) | `theorem notAlone : ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂` | {AxTwoSubjects, Means, Subject}  |

### `Logos.Retorsion`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `A17AnalysisSignature` | structure | [L766](formal/Logos/Retorsion.lean#L766) | `structure A17AnalysisSignature where` | —  |
| `A17_strong` | def | [L709](formal/Logos/Retorsion.lean#L709) | `def A17_strong : Prop` | {DependsOn, Means, Subject}  |
| `A17_weak` | def | [L704](formal/Logos/Retorsion.lean#L704) | `def A17_weak : Prop` | {DependsOn, Means, Subject}  |
| `A17a` | def | [L690](formal/Logos/Retorsion.lean#L690) | `def A17a : Prop` | {Means, Subject}  |
| `A17b` | def | [L693](formal/Logos/Retorsion.lean#L693) | `def A17b : Prop` | {DependsOn, Means, Subject}  |
| `A17c` | def | [L697](formal/Logos/Retorsion.lean#L697) | `def A17c : Prop` | {Means, Subject}  |
| `A17d` | def | [L700](formal/Logos/Retorsion.lean#L700) | `def A17d : Prop` | {Means, Subject}  |
| `ArbitraryPigSignature` | structure | [L629](formal/Logos/Retorsion.lean#L629) | `structure ArbitraryPigSignature where` | —  |
| `DependsOn` | axiom | [L166](formal/Logos/Retorsion.lean#L166) | `axiom DependsOn : DomainItem → Subject → Prop` | {DependsOn, Subject}  |
| `DependsOnBareSubject` | def | [L514](formal/Logos/Retorsion.lean#L514) | `def DependsOnBareSubject (x : DomainItem) : Prop` | {DependsOn, Subject}  |
| `DependsOnIntentional` | def | [L171](formal/Logos/Retorsion.lean#L171) | `def DependsOnIntentional (x : DomainItem) : Prop` | {DependsOn, Means, Subject}  |
| `DependsOnWingedPig` | def | [L601](formal/Logos/Retorsion.lean#L601) | `def DependsOnWingedPig (x : DomainItem) : Prop` | {DependsOn, Subject}  |
| `DeterministicTranscendentalSubjectModel` | def | [L555](formal/Logos/Retorsion.lean#L555) | `def DeterministicTranscendentalSubjectModel : WeakenedRetorsionSignature where S` | {}  |
| `DomainItem` | inductive | [L157](formal/Logos/Retorsion.lean#L157) | `inductive DomainItem : Type` | —  |
| `EverythingObjective` | def | [L259](formal/Logos/Retorsion.lean#L259) | `def EverythingObjective : Prop` | {DependsOn, Means, Subject}  |
| `EverythingObjectivePig` | def | [L613](formal/Logos/Retorsion.lean#L613) | `def EverythingObjectivePig : Prop` | {DependsOn, Subject}  |
| `EverythingSubjective` | def | [L212](formal/Logos/Retorsion.lean#L212) | `def EverythingSubjective : Prop` | {DependsOn, Means, Subject}  |
| `NegA13_ActPolarity` | def | [L909](formal/Logos/Retorsion.lean#L909) | `def NegA13_ActPolarity : Prop` | {Initiates, Means, State, Subject}  |
| `NegA14_IntentionalChoice` | def | [L913](formal/Logos/Retorsion.lean#L913) | `def NegA14_IntentionalChoice : Prop` | {Initiates, Means, State, Subject}  |
| `NegA3_Truthmaker` | def | [L901](formal/Logos/Retorsion.lean#L901) | `def NegA3_Truthmaker : Prop` | {Ground, Subject}  |
| `NegA4_GlobalGround` | def | [L905](formal/Logos/Retorsion.lean#L905) | `def NegA4_GlobalGround : Prop` | {Ground, Subject}  |
| `NegA6_Plurality` | def | [L917](formal/Logos/Retorsion.lean#L917) | `def NegA6_Plurality : Prop` | {Means, Subject}  |
| `NegA7_PersonalGround` | def | [L921](formal/Logos/Retorsion.lean#L921) | `def NegA7_PersonalGround : Prop` | {GroundProp, Initiates, Means, State, Subject}  |
| `NegActToPerson` | def | [L926](formal/Logos/Retorsion.lean#L926) | `def NegActToPerson : Prop` | {Initiates, Means, State, Subject}  |
| `NegPluralityToLove` | def | [L930](formal/Logos/Retorsion.lean#L930) | `def NegPluralityToLove : Prop` | {Means, Subject}  |
| `NoTruth` | def | [L95](formal/Logos/Retorsion.lean#L95) | `def NoTruth : Prop` | {}  |
| `Objective` | def | [L181](formal/Logos/Retorsion.lean#L181) | `def Objective (x : DomainItem) : Prop` | {DependsOn, Means, Subject}  |
| `ObjectivePig` | def | [L609](formal/Logos/Retorsion.lean#L609) | `def ObjectivePig (x : DomainItem) : Prop` | {DependsOn, Subject}  |
| `PerformativeRetorsionWitness` | structure | [L70](formal/Logos/Retorsion.lean#L70) | `structure PerformativeRetorsionWitness (P : Prop) where` | —  |
| `Person` | def | [L153](formal/Logos/Retorsion.lean#L153) | `def Person (s : Subject) : Prop` | {Means, Subject}  |
| `PersonOSSignature` | structure | [L346](formal/Logos/Retorsion.lean#L346) | `structure PersonOSSignature where` | —  |
| `PigTranscendentalReflectionHypothesis` | def | [L617](formal/Logos/Retorsion.lean#L617) | `def PigTranscendentalReflectionHypothesis : Prop` | {DependsOn, Subject}  |
| `RestrictedTranscendentalBridge` | def | [L738](formal/Logos/Retorsion.lean#L738) | `def RestrictedTranscendentalBridge : Prop` | {DependsOn, Means, Subject}  |
| `RetorsionSource` | inductive | [L62](formal/Logos/Retorsion.lean#L62) | `inductive RetorsionSource : Type` | —  |
| `Subjective` | def | [L176](formal/Logos/Retorsion.lean#L176) | `def Subjective (x : DomainItem) : Prop` | {DependsOn, Means, Subject}  |
| `SubjectivePig` | def | [L605](formal/Logos/Retorsion.lean#L605) | `def SubjectivePig (x : DomainItem) : Prop` | {DependsOn, Subject}  |
| `UniversalMeansToDependsBridge` | def | [L732](formal/Logos/Retorsion.lean#L732) | `def UniversalMeansToDependsBridge : Prop` | {DependsOn, Means, Subject}  |
| `WeakenedEverythingObjective` | def | [L526](formal/Logos/Retorsion.lean#L526) | `def WeakenedEverythingObjective : Prop` | {DependsOn, Means, Subject}  |
| `WeakenedObjective` | def | [L522](formal/Logos/Retorsion.lean#L522) | `def WeakenedObjective (x : DomainItem) : Prop` | {DependsOn, Means, Subject}  |
| `WeakenedRetorsionSignature` | structure | [L542](formal/Logos/Retorsion.lean#L542) | `structure WeakenedRetorsionSignature where` | —  |
| `WeakenedSubjective` | def | [L518](formal/Logos/Retorsion.lean#L518) | `def WeakenedSubjective (x : DomainItem) : Prop` | {DependsOn, Means, Subject}  |
| `WeakenedTranscendentalReflectionHypothesis` | def | [L531](formal/Logos/Retorsion.lean#L531) | `def WeakenedTranscendentalReflectionHypothesis : Prop` | {DependsOn, Means, Subject}  |
| `WingedPig` | opaque | [L598](formal/Logos/Retorsion.lean#L598) | `opaque WingedPig : Subject → Prop` | —  |
| `WitnessSubject` | inductive | [L761](formal/Logos/Retorsion.lean#L761) | `inductive WitnessSubject : Type` | —  |
| `a17_strong_implies_a17_weak` | theorem | [L719](formal/Logos/Retorsion.lean#L719) | `theorem a17_strong_implies_a17_weak (h : A17_strong) : A17_weak` | {DependsOn, Means, Subject}  |
| `a17b_implies_a17_weak` | theorem | [L713](formal/Logos/Retorsion.lean#L713) | `theorem a17b_implies_a17_weak (h : A17b) : A17_weak` | {DependsOn, Means, Subject}  |
| `bigO_bigS_intentional_synthesis` | theorem | [L324](formal/Logos/Retorsion.lean#L324) | `theorem bigO_bigS_intentional_synthesis : (∃ x : DomainItem, Objective x) ∧ (∃ x` | {transcendental_reflection_intentional, universal_thesis_claims_objectivity, DependsOn, Means, Subject}  |
| `deterministic_transcendental_subject_refutes_freewill` | theorem | [L569](formal/Logos/Retorsion.lean#L569) | `theorem deterministic_transcendental_subject_refutes_freewill : ¬ (∀ I : Weakene` | {}  |
| `deterministic_transcendental_subject_refutes_person` | theorem | [L582](formal/Logos/Retorsion.lean#L582) | `theorem deterministic_transcendental_subject_refutes_person : ¬ (∀ I : WeakenedR` | {}  |
| `everything_objective_self_applies` | theorem | [L263](formal/Logos/Retorsion.lean#L263) | `theorem everything_objective_self_applies (hEO : EverythingObjective) : Objectiv` | {DependsOn, Means, Subject}  |
| `everything_subjective_self_applies` | theorem | [L216](formal/Logos/Retorsion.lean#L216) | `theorem everything_subjective_self_applies (hES : EverythingSubjective) : Subjec` | {DependsOn, Means, Subject}  |
| `exists_intentional_subject_of_retorsion` | theorem | [L317](formal/Logos/Retorsion.lean#L317) | `theorem exists_intentional_subject_of_retorsion : ∃ s : Subject, IntentionalSubj` | {transcendental_reflection_intentional, DependsOn, Means, Subject}  |
| `exists_intentional_subject_of_subjective` | theorem | [L206](formal/Logos/Retorsion.lean#L206) | `theorem exists_intentional_subject_of_subjective (h : ∃ x : DomainItem, Subjecti` | {DependsOn, Means, Subject}  |
| `exists_means_not_exists_dependson` | theorem | [L835](formal/Logos/Retorsion.lean#L835) | `theorem exists_means_not_exists_dependson : ¬ (∀ I : A17AnalysisSignature, (∃ s ` | {}  |
| `exists_non_objective_item` | theorem | [L302](formal/Logos/Retorsion.lean#L302) | `theorem exists_non_objective_item : ∃ x : DomainItem, ¬ Objective x` | {transcendental_reflection_intentional, DependsOn, Means, Subject, CL}  |
| `exists_non_subjective_item` | theorem | [L247](formal/Logos/Retorsion.lean#L247) | `theorem exists_non_subjective_item : ∃ x : DomainItem, ¬ Subjective x` | {universal_thesis_claims_objectivity, DependsOn, Means, Subject, CL}  |
| `exists_objective_of_retorsion` | theorem | [L241](formal/Logos/Retorsion.lean#L241) | `theorem exists_objective_of_retorsion : ∃ x : DomainItem, Objective x` | {universal_thesis_claims_objectivity, DependsOn, Means, Subject}  |
| `exists_subjective_not_exists_freewill` | theorem | [L472](formal/Logos/Retorsion.lean#L472) | `theorem exists_subjective_not_exists_freewill : ¬ (∀ I : PersonOSSignature, (∃ x` | {}  |
| `exists_subjective_not_exists_person` | theorem | [L449](formal/Logos/Retorsion.lean#L449) | `theorem exists_subjective_not_exists_person : ¬ (∀ I : PersonOSSignature, (∃ x :` | {}  |
| `exists_subjective_of_retorsion` | theorem | [L296](formal/Logos/Retorsion.lean#L296) | `theorem exists_subjective_of_retorsion : ∃ x : DomainItem, Subjective x` | {transcendental_reflection_intentional, DependsOn, Means, Subject}  |
| `intentional_not_freewill` | theorem | [L797](formal/Logos/Retorsion.lean#L797) | `theorem intentional_not_freewill : ¬ (∀ I : A17AnalysisSignature, ∀ s : I.Subjec` | {}  |
| `intentional_not_person` | theorem | [L778](formal/Logos/Retorsion.lean#L778) | `theorem intentional_not_person : ¬ (∀ I : A17AnalysisSignature, ∀ s : I.Subject,` | {}  |
| `intentional_subject_not_person` | theorem | [L405](formal/Logos/Retorsion.lean#L405) | `theorem intentional_subject_not_person : ¬ (∀ I : PersonOSSignature, ∀ s : I.Sub` | {}  |
| `means_not_dependson` | theorem | [L816](formal/Logos/Retorsion.lean#L816) | `theorem means_not_dependson : ¬ (∀ I : A17AnalysisSignature, ∀ s : I.Subject, I.` | {}  |
| `not_everything_objective` | theorem | [L286](formal/Logos/Retorsion.lean#L286) | `theorem not_everything_objective : ¬ EverythingObjective` | {transcendental_reflection_intentional, DependsOn, Means, Subject}  |
| `not_everything_subjective` | theorem | [L231](formal/Logos/Retorsion.lean#L231) | `theorem not_everything_subjective : ¬ EverythingSubjective` | {universal_thesis_claims_objectivity, DependsOn, Means, Subject}  |
| `objective_and_subjective_disjoint` | theorem | [L187](formal/Logos/Retorsion.lean#L187) | `theorem objective_and_subjective_disjoint (x : DomainItem) : Objective x → Subje` | {DependsOn, Means, Subject}  |
| `objective_or_subjective` | theorem | [L193](formal/Logos/Retorsion.lean#L193) | `theorem objective_or_subjective (x : DomainItem) : Objective x ∨ Subjective x` | {DependsOn, Means, Subject, CL}  |
| `person_not_freewill` | theorem | [L427](formal/Logos/Retorsion.lean#L427) | `theorem person_not_freewill : ¬ (∀ I : PersonOSSignature, ∀ s : I.Subject, I.Per` | {}  |
| `pig_retorsion_exposes_premise_smuggling` | theorem | [L642](formal/Logos/Retorsion.lean#L642) | `theorem pig_retorsion_exposes_premise_smuggling : ¬ (∀ I : ArbitraryPigSignature` | {}  |
| `representation_not_depends_on_person` | theorem | [L361](formal/Logos/Retorsion.lean#L361) | `theorem representation_not_depends_on_person : ¬ (∀ I : PersonOSSignature, ∀ (s ` | {}  |
| `restricted_bridge_derives_a17_weak` | theorem | [L750](formal/Logos/Retorsion.lean#L750) | `theorem restricted_bridge_derives_a17_weak (hEntertains : ∃ s : Subject, Means s` | {DependsOn, Means, Subject}  |
| `restricted_bridge_derives_a17b` | theorem | [L742](formal/Logos/Retorsion.lean#L742) | `theorem restricted_bridge_derives_a17b (hEntertains : ∃ s : Subject, Means s Eve` | {DependsOn, Means, Subject}  |
| `retorsion_boundary_principle` | theorem | [L939](formal/Logos/Retorsion.lean#L939) | `theorem retorsion_boundary_principle (P Q : Prop) (hModel : Q) (hConsistent : ¬ ` | {}  |
| `retorsion_establishes_affirmation` | theorem | [L79](formal/Logos/Retorsion.lean#L79) | `theorem retorsion_establishes_affirmation {P : Prop} (w : PerformativeRetorsionW` | {Initiates, Means, State, Subject}  |
| `retorsion_no_act` | theorem | [L99](formal/Logos/Retorsion.lean#L99) | `theorem retorsion_no_act (s : Subject) (h : Asserts s NoAct) : False` | {Initiates, Means, State, Subject}  |
| `retorsion_no_choiceField` | theorem | [L118](formal/Logos/Retorsion.lean#L118) | `theorem retorsion_no_choiceField (s : Subject) (h : Asserts s NoChoiceField) : F` | {Initiates, Means, State, Subject}  |
| `retorsion_no_subject` | theorem | [L113](formal/Logos/Retorsion.lean#L113) | `theorem retorsion_no_subject (s : Subject) (h : Asserts s Logos.Agency.NoSubject` | {Initiates, Means, State, Subject}  |
| `retorsion_no_truth` | theorem | [L108](formal/Logos/Retorsion.lean#L108) | `theorem retorsion_no_truth (h : T NoTruth) : False` | {}  |
| `retorsion_no_weak_act` | theorem | [L103](formal/Logos/Retorsion.lean#L103) | `theorem retorsion_no_weak_act (s : Subject) (h : asserts s NoWeakAct) : False` | {Subject, act}  |
| `retorsion_refutes_denial` | theorem | [L84](formal/Logos/Retorsion.lean#L84) | `theorem retorsion_refutes_denial {P : Prop} (w : PerformativeRetorsionWitness P)` | {Initiates, Means, State, Subject}  |
| `subjective_implies_intentional_subject` | theorem | [L200](formal/Logos/Retorsion.lean#L200) | `theorem subjective_implies_intentional_subject (x : DomainItem) (h : Subjective ` | {DependsOn, Means, Subject}  |
| `subjective_not_depends_on_person` | theorem | [L383](formal/Logos/Retorsion.lean#L383) | `theorem subjective_not_depends_on_person : ¬ (∀ I : PersonOSSignature, ∀ x : I.D` | {}  |
| `transcendental_reflection_intentional` | axiom | [L274](formal/Logos/Retorsion.lean#L274) | `axiom transcendental_reflection_intentional : ∃ s : Subject, IntentionalSubject ` | {transcendental_reflection_intentional, DependsOn, Means, Subject}  |
| `universal_objectivity_subjective` | theorem | [L278](formal/Logos/Retorsion.lean#L278) | `theorem universal_objectivity_subjective : Subjective (DomainItem.ofProp Everyth` | {transcendental_reflection_intentional, DependsOn, Means, Subject}  |
| `universal_thesis_claims_objectivity` | axiom | [L224](formal/Logos/Retorsion.lean#L224) | `axiom universal_thesis_claims_objectivity : Objective (DomainItem.ofProp Everyth` | {universal_thesis_claims_objectivity, DependsOn, Means, Subject}  |
| `weakened_retorsion_derives_intentional_subject` | theorem | [L535](formal/Logos/Retorsion.lean#L535) | `theorem weakened_retorsion_derives_intentional_subject (hRef : WeakenedTranscend` | {DependsOn, Means, Subject}  |
| `winged_pig_derived_of_pig_reflection` | theorem | [L622](formal/Logos/Retorsion.lean#L622) | `theorem winged_pig_derived_of_pig_reflection (hPigRef : PigTranscendentalReflect` | {DependsOn, Subject}  |
| `witness_slippage_separation` | theorem | [L859](formal/Logos/Retorsion.lean#L859) | `theorem witness_slippage_separation : ¬ (∀ I : A17AnalysisSignature, (∃ s : I.Su` | {}  |

### `Logos.Semantics`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `FalseAt` | def | [L55](formal/Logos/Semantics.lean#L55) | `def FalseAt (w : World) (φ : Form) : Prop` | {}  |
| `Form` | inductive | [L22](formal/Logos/Semantics.lean#L22) | `inductive Form : Type` | —  |
| `NecessarilyFalse` | def | [L61](formal/Logos/Semantics.lean#L61) | `def ¬◇(φ : Form) : Prop` | {}  |
| `NecessarilyTrue` | def | [L58](formal/Logos/Semantics.lean#L58) | `def □(φ : Form) : Prop` | {}  |
| `Satisfies` | def | [L44](formal/Logos/Semantics.lean#L44) | `def Satisfies : World → Form → Prop | w, atom n => w n = TV.t` | {}  |
| `TV` | inductive | [L33](formal/Logos/Semantics.lean#L33) | `inductive TV : Type` | —  |
| `TrueAt` | def | [L52](formal/Logos/Semantics.lean#L52) | `def TrueAt (w : World) (φ : Form) : Prop` | {}  |
| `World` | abbrev | [L41](formal/Logos/Semantics.lean#L41) | `abbrev World : Type` | {}  |
| `atom_not_necessarily_false` | theorem | [L139](formal/Logos/Semantics.lean#L139) | `theorem atom_not_necessarily_false (n : Nat) : ¬ ¬◇atom n` | {}  |
| `atom_not_necessarily_true` | theorem | [L131](formal/Logos/Semantics.lean#L131) | `theorem atom_not_necessarily_true (n : Nat) : ¬ □atom n` | {}  |
| `atoms_are_modally_free` | theorem | [L146](formal/Logos/Semantics.lean#L146) | `theorem atoms_are_modally_free : ∀ n : Nat, ¬ □atom n ∧ ¬ ¬◇atom n` | {} → C95 |
| `bothNecessarilyTrueAndFalse` | theorem | [L102](formal/Logos/Semantics.lean#L102) | `theorem bothNecessarilyTrueAndFalse : (∃ τ : Form, □ τ) ∧ (∃ ρ : Form, ¬◇ ρ)` | {CL} → C37 |
| `lawExcludedMiddle` | theorem | [L76](formal/Logos/Semantics.lean#L76) | `theorem lawExcludedMiddle (φ : Form) : □(φ ∨ ¬φ)` | {CL} → C13 |
| `noStrongTruth_selfRefutes` | theorem | [L121](formal/Logos/Semantics.lean#L121) | `theorem noStrongTruth_selfRefutes : ¬ (¬ ∃ τ : Form, □ τ)` | {CL} → C93 |
| `nonContradiction` | theorem | [L85](formal/Logos/Semantics.lean#L85) | `theorem nonContradiction (φ : Form) : ¬◇(φ ∧ ¬φ)` | {CL} → C14 |
| `sat_and` | theorem | [L67](formal/Logos/Semantics.lean#L67) | `theorem sat_and : w ⊨ (φ ∧ ψ) ↔ w ⊨ φ ∧ w ⊨ ψ` | {}  |
| `sat_imp` | theorem | [L71](formal/Logos/Semantics.lean#L71) | `theorem sat_imp : w ⊨ (φ → ψ) ↔ (w ⊨ φ → w ⊨ ψ)` | {}  |
| `sat_not` | theorem | [L65](formal/Logos/Semantics.lean#L65) | `theorem sat_not : w ⊨ ¬φ ↔ ¬ w ⊨ φ` | {}  |
| `sat_or` | theorem | [L69](formal/Logos/Semantics.lean#L69) | `theorem sat_or : w ⊨ (φ ∨ ψ) ↔ w ⊨ φ ∨ w ⊨ ψ` | {}  |
| `some_formula_contingent` | theorem | [L160](formal/Logos/Semantics.lean#L160) | `theorem some_formula_contingent : ∃ τ : Form, ¬ □ τ ∧ ¬ ¬◇ τ` | {} → C96 |
| `strongTruthExists` | theorem | [L113](formal/Logos/Semantics.lean#L113) | `theorem strongTruthExists : ∃ τ : Form, □ τ` | {CL} → C59 |
| `strongTruth_and_contingent_content` | theorem | [L168](formal/Logos/Semantics.lean#L168) | `theorem strongTruth_and_contingent_content : ∃ τ : Form, □ τ ∧ ∃ σ : Form, ¬ □ σ` | {CL}  |
| `strongTruth_is_not_atomic` | theorem | [L152](formal/Logos/Semantics.lean#L152) | `theorem strongTruth_is_not_atomic : ∃ τ : Form, □ τ ∧ ∀ n : Nat, ¬ □atom n` | {CL}  |

### `Logos.Truthmaker`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Entity` | inductive | [L41](formal/Logos/Truthmaker.lean#L41) | `inductive Entity : Type` | —  |
| `EntityExistsAt` | def | [L70](formal/Logos/Truthmaker.lean#L70) | `def EntityExistsAt (w : World) : Entity → Prop | Entity.ofSubject s => SubjectEx` | {Subject}  |
| `EntityOf` | def | [L46](formal/Logos/Truthmaker.lean#L46) | `def EntityOf (s : Subject) : Entity` | {Subject}  |
| `ExistsAt` | def | [L75](formal/Logos/Truthmaker.lean#L75) | `def ExistsAt (w : World) (e : Entity) : Prop` | {Subject}  |
| `Ground` | axiom | [L54](formal/Logos/Truthmaker.lean#L54) | `axiom Ground : Entity → Form → Prop` | {Ground, Subject}  |
| `NecessarilyFalse` | def | [L85](formal/Logos/Truthmaker.lean#L85) | `def ¬◇(φ : Form) : Prop` | {}  |
| `NecessarilyTrue` | def | [L82](formal/Logos/Truthmaker.lean#L82) | `def □(φ : Form) : Prop` | {}  |
| `SubjectExistsAt` | def | [L64](formal/Logos/Truthmaker.lean#L64) | `def SubjectExistsAt (w : World) (_s : Subject) : Prop` | {Subject}  |
| `TrueAt` | def | [L79](formal/Logos/Truthmaker.lean#L79) | `def TrueAt (w : World) (φ : Form) : Prop` | {}  |
| `Truthmaker` | axiom | [L98](formal/Logos/Truthmaker.lean#L98) | `axiom Truthmaker : ∀ (w : World) (φ : Form), w ⊨ φ → ∃ e : Entity, ExistsAt w e ` | {Truthmaker, Ground, Subject}  |
| `actualWorld` | def | [L57](formal/Logos/Truthmaker.lean#L57) | `def actualWorld : World` | {}  |
| `groundPrinciple_atom` | theorem | [L105](formal/Logos/Truthmaker.lean#L105) | `theorem groundPrinciple_atom (w : World) (n : Nat) : w ⊨ atom n → ∃ e : Entity, ` | {Truthmaker, Ground, Subject} → C15 |
| `lawExcludedMiddle` | theorem | [L140](formal/Logos/Truthmaker.lean#L140) | `theorem lawExcludedMiddle (φ : Form) : □(φ ∨ ¬φ)` | {CL} → C16 |
| `noGround_selfRefutes` | theorem | [L112](formal/Logos/Truthmaker.lean#L112) | `theorem noGround_selfRefutes : ¬ (∃ (w : World) (n : Nat), w ⊨ atom n ∧ ¬ (∃ e :` | {Truthmaker, Ground, Subject} → C60 |
| `nonContradiction` | theorem | [L148](formal/Logos/Truthmaker.lean#L148) | `theorem nonContradiction (φ : Form) : ¬◇(φ ∧ ¬φ)` | {} → C17 |
| `otherWorld` | def | [L60](formal/Logos/Truthmaker.lean#L60) | `def otherWorld : World` | {}  |
| `sat_ground_and` | theorem | [L125](formal/Logos/Truthmaker.lean#L125) | `theorem sat_ground_and {w : World} {φ ψ : Form} : w ⊨ (φ ∧ ψ) ↔ w ⊨ φ ∧ w ⊨ ψ` | {}  |
| `sat_ground_imp` | theorem | [L133](formal/Logos/Truthmaker.lean#L133) | `theorem sat_ground_imp {w : World} {φ ψ : Form} : w ⊨ (φ → ψ) ↔ (w ⊨ φ → w ⊨ ψ)` | {}  |
| `sat_ground_not` | theorem | [L129](formal/Logos/Truthmaker.lean#L129) | `theorem sat_ground_not {w : World} {φ : Form} : w ⊨ ¬φ ↔ ¬ w ⊨ φ` | {}  |
| `sat_ground_or` | theorem | [L121](formal/Logos/Truthmaker.lean#L121) | `theorem sat_ground_or {w : World} {φ ψ : Form} : w ⊨ (φ ∨ ψ) ↔ w ⊨ φ ∨ w ⊨ ψ` | {}  |

### `Logos.Value`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Affects` | def | [L48](formal/Logos/Value.lean#L48) | `def Affects (s t : Subject) : Prop` | {Subject}  |
| `Alone` | def | [L84](formal/Logos/Value.lean#L84) | `def Alone (s : Subject) : Prop` | {Subject}  |
| `AxTwoSubjects` | axiom | [L115](formal/Logos/Value.lean#L115) | `axiom AxTwoSubjects : (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) → ∃ s₁ s₂ : Subject,` | {AxTwoSubjects, Means, Subject} → FAITH-2 |
| `BearingOf` | def | [L43](formal/Logos/Value.lean#L43) | `def BearingOf (_s _t : Subject) : InterpersonalBearing` | {Subject}  |
| `Harms` | def | [L58](formal/Logos/Value.lean#L58) | `def Harms (s t : Subject) : Prop` | {Subject}  |
| `Helps` | def | [L54](formal/Logos/Value.lean#L54) | `def Helps (s t : Subject) : Prop` | {Subject}  |
| `InterpersonalBearing` | inductive | [L35](formal/Logos/Value.lean#L35) | `inductive InterpersonalBearing : Type` | —  |
| `OtherAffects` | def | [L81](formal/Logos/Value.lean#L81) | `def OtherAffects (s : Subject) : Prop` | {Subject}  |
| `PersonsAffectPrinciple` | def | [L134](formal/Logos/Value.lean#L134) | `def PersonsAffectPrinciple : Prop` | {Means, Subject}  |
| `aloneExcluded` | theorem | [L124](formal/Logos/Value.lean#L124) | `theorem aloneExcluded : ¬ ∃ s : Subject, Person s ∧ Alone s` | {AxTwoSubjects, Means, Subject} → C74 |
| `alone_no_other_affects` | theorem | [L87](formal/Logos/Value.lean#L87) | `theorem alone_no_other_affects {s : Subject} (ha : Alone s) : ¬ OtherAffects s` | {Subject}  |
| `alone_no_other_help_harm` | theorem | [L95](formal/Logos/Value.lean#L95) | `theorem alone_no_other_help_harm {s : Subject} (ha : Alone s) : (¬ ∃ t : Subject` | {Subject} → C56 |
| `harm_affects` | theorem | [L68](formal/Logos/Value.lean#L68) | `theorem harm_affects : ∀ {s t : Subject}, Harms s t → Affects s t` | {Subject}  |
| `help_affects` | theorem | [L62](formal/Logos/Value.lean#L62) | `theorem help_affects : ∀ {s t : Subject}, Helps s t → Affects s t` | {Subject}  |
| `help_not_harm` | theorem | [L74](formal/Logos/Value.lean#L74) | `theorem help_not_harm : ∀ {s t : Subject}, Helps s t → ¬ Harms s t` | {Subject} → C85 |
| `valueInterpersonal_of_split_conditional` | theorem | [L139](formal/Logos/Value.lean#L139) | `theorem valueInterpersonal_of_split_conditional (hAffect : PersonsAffectPrincipl` | {AxTwoSubjects, Means, Subject} → C46 |

### `PropositionalPersonhood`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `TripartiteVerdict` | def | [L581](formal/Logos/HostileSemantics.lean#L581) | `def TripartiteVerdict : String` | —  |

### `PropositionalPersonhood.CountermodelContentWithoutPerson`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Means` | def | [L569](formal/Logos/HostileSemantics.lean#L569) | `def Means : S → Prop → Prop` | —  |
| `Person` | def | [L570](formal/Logos/HostileSemantics.lean#L570) | `def Person : S → Prop` | —  |
| `S` | def | [L568](formal/Logos/HostileSemantics.lean#L568) | `def S : Type` | —  |
| `content_does_not_imply_personhood` | theorem | [L576](formal/Logos/HostileSemantics.lean#L576) | `theorem content_does_not_imply_personhood : (∃ _p : Prop, True) ∧ (∀ p : Prop, ∃` | —  |
| `content_exists` | theorem | [L572](formal/Logos/HostileSemantics.lean#L572) | `theorem content_exists : ∃ _p : Prop, True` | —  |
| `every_content_meant` | theorem | [L573](formal/Logos/HostileSemantics.lean#L573) | `theorem every_content_meant (p : Prop) : ∃ s : S, Means s p` | —  |
| `no_person` | theorem | [L574](formal/Logos/HostileSemantics.lean#L574) | `theorem no_person : ¬ ∃ s : S, Person s` | —  |

### `TruthmakingInvestigation`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `C_does_not_entail_D` | theorem | [L3717](formal/Logos/HostileSemantics.lean#L3717) | `theorem C_does_not_entail_D : ¬ (∀ S : GroundingModalitySignature, S.ClaimC → S.` | —  |
| `ClaimA` | def | [L3642](formal/Logos/HostileSemantics.lean#L3642) | `def ClaimA : Prop` | —  |
| `ClaimB_Prop` | def | [L3646](formal/Logos/HostileSemantics.lean#L3646) | `def ClaimB_Prop : Prop` | —  |
| `ClaimB_World` | def | [L3650](formal/Logos/HostileSemantics.lean#L3650) | `def ClaimB_World : Prop` | —  |
| `ClaimC` | def | [L3654](formal/Logos/HostileSemantics.lean#L3654) | `def ClaimC : Prop` | —  |
| `ClaimD` | def | [L3657](formal/Logos/HostileSemantics.lean#L3657) | `def ClaimD : Prop` | —  |
| `D_implies_C` | theorem | [L3661](formal/Logos/HostileSemantics.lean#L3661) | `theorem D_implies_C : ClaimD → ClaimC` | —  |
| `DeflationaryModel` | def | [L3617](formal/Logos/HostileSemantics.lean#L3617) | `def DeflationaryModel : TruthmakingIndependenceSignature where Entity` | —  |
| `G` | def | [L3588](formal/Logos/HostileSemantics.lean#L3588) | `def G : Prop` | —  |
| `G_ambient_derivable` | theorem | [L3598](formal/Logos/HostileSemantics.lean#L3598) | `theorem G_ambient_derivable : G` | —  |
| `G_yields_ClaimC` | theorem | [L3667](formal/Logos/HostileSemantics.lean#L3667) | `theorem G_yields_ClaimC (hG : G) : ClaimC` | —  |
| `GroundLevel1` | def | [L3788](formal/Logos/HostileSemantics.lean#L3788) | `def GroundLevel1 (e₀ : Entity) : Prop` | —  |
| `GroundLevel2` | def | [L3789](formal/Logos/HostileSemantics.lean#L3789) | `def GroundLevel2 (e₁ e₀ : Entity) : Prop` | —  |
| `GroundLevel3` | def | [L3790](formal/Logos/HostileSemantics.lean#L3790) | `def GroundLevel3 : Prop` | —  |
| `GroundingModalitySignature` | structure | [L3700](formal/Logos/HostileSemantics.lean#L3700) | `structure GroundingModalitySignature where` | —  |
| `NecessaryChainSignature` | structure | [L3854](formal/Logos/HostileSemantics.lean#L3854) | `structure NecessaryChainSignature where` | —  |
| `Neg_G` | def | [L3753](formal/Logos/HostileSemantics.lean#L3753) | `def Neg_G : Prop` | —  |
| `T_G_ambient_derivable` | theorem | [L3603](formal/Logos/HostileSemantics.lean#L3603) | `theorem T_G_ambient_derivable : T G` | —  |
| `T_G_iff_G` | theorem | [L3593](formal/Logos/HostileSemantics.lean#L3593) | `theorem T_G_iff_G : T G ↔ G` | —  |
| `TruthmakingIndependenceSignature` | structure | [L3608](formal/Logos/HostileSemantics.lean#L3608) | `structure TruthmakingIndependenceSignature where` | —  |
| `claimB_world_refuted` | theorem | [L3692](formal/Logos/HostileSemantics.lean#L3692) | `theorem claimB_world_refuted : ¬ ClaimB_World` | —  |
| `grounding_G_does_not_derive_ultimate_ground` | theorem | [L3862](formal/Logos/HostileSemantics.lean#L3862) | `theorem grounding_G_does_not_derive_ultimate_ground : ¬ (∀ S : NecessaryChainSig` | —  |
| `infinite_regress_generator` | theorem | [L3795](formal/Logos/HostileSemantics.lean#L3795) | `theorem infinite_regress_generator (hG : G) (e₀ : Entity) (h0 : GroundLevel1 e₀)` | —  |
| `neg_G_consistent_in_deflationary_model` | theorem | [L3760](formal/Logos/HostileSemantics.lean#L3760) | `theorem neg_G_consistent_in_deflationary_model : ∃ (M : TruthmakingIndependenceS` | —  |
| `no_entity_at_otherWorld` | theorem | [L3674](formal/Logos/HostileSemantics.lean#L3674) | `theorem no_entity_at_otherWorld (e : Entity) : ¬ ExistsAt otherWorld e` | —  |
| `permissive_regress_collapse` | theorem | [L3806](formal/Logos/HostileSemantics.lean#L3806) | `theorem permissive_regress_collapse (p : Prop) (hp : p) : let GP` | —  |
| `truthmaking_alone_insufficient_for_ultimate_ground` | theorem | [L3885](formal/Logos/HostileSemantics.lean#L3885) | `theorem truthmaking_alone_insufficient_for_ultimate_ground : (∃ (M : Countermode` | —  |
| `truthmaking_not_logically_forced` | theorem | [L3625](formal/Logos/HostileSemantics.lean#L3625) | `theorem truthmaking_not_logically_forced : ¬ (∀ I : TruthmakingIndependenceSigna` | —  |
| `truthmaking_retorsion_fails` | theorem | [L3771](formal/Logos/HostileSemantics.lean#L3771) | `theorem truthmaking_retorsion_fails (asserts_neg_G : Neg_G) (h_no_ground : ∀ e :` | —  |
| `z_chain_satisfies_grounded_truthmaking` | theorem | [L3824](formal/Logos/HostileSemantics.lean#L3824) | `theorem z_chain_satisfies_grounded_truthmaking : let Ent` | —  |

### `UnitPluralityCountermodel`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `A` | def | [L551](formal/Logos/HostileSemantics.lean#L551) | `def A : S → Prop → Prop` | —  |
| `Person` | def | [L552](formal/Logos/HostileSemantics.lean#L552) | `def Person : S → Prop` | —  |
| `S` | def | [L550](formal/Logos/HostileSemantics.lean#L550) | `def S : Type` | —  |
| `act_occurs` | theorem | [L554](formal/Logos/HostileSemantics.lean#L554) | `theorem act_occurs : ∃ s : S, ∃ p : Prop, A s p` | —  |
| `agency_does_not_imply_plurality` | theorem | [L561](formal/Logos/HostileSemantics.lean#L561) | `theorem agency_does_not_imply_plurality : (∃ s : S, ∃ p : Prop, A s p) ∧ (∃ s : ` | —  |
| `no_plurality` | theorem | [L556](formal/Logos/HostileSemantics.lean#L556) | `theorem no_plurality : ¬ ∃ s t : S, s ≠ t` | —  |
| `person_exists` | theorem | [L555](formal/Logos/HostileSemantics.lean#L555) | `theorem person_exists : ∃ s : S, Person s` | —  |

</details>

---
### D.6 Provenance and regeneration

Every statement, gloss and cost sentence consumed above lives in the Lean sources (docstrings, `String` constants, `Tag:` lines); the generated document transcribes nothing by hand.

- **Kernel:** `formal/Logos/*.lean` — `lake build` green, `sorryAx 0`.
- **Footprints:** `formal/axiom_audit.json` via `#print axioms` (transitive kernel axiom set, meta-logic `CL` included).
- **Dependency edges:** `formal/depgraph.json` (LeanDepViz).
- **Claim ledger (checked, not quoted):** `formal/GAPMAP.md`.
- **Regeneration order:**

```sh
export PATH="$HOME/.elan/bin:$PATH"
cd formal && lake build
lake exe depviz --roots Logos --json-out depgraph.json --dot-out depgraph.dot
cd .. && python3 scripts/audit_footprints.py && python3 scripts/build_deduction.py
```

---
