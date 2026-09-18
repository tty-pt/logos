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
performative meaning-act → intentional subject (C24) [substantive person OPEN] DEFINITIONAL
performative meaning-act → choice field (alternatives)     DEFINITIONAL
assertion → semantic selection                             DEFINITIONAL
deliberate choice → semantic selection                     DEFINITIONAL
deliberate choice → genuine choice                         DEFINITIONAL
genuine choice → free will                                 DEFINITIONAL
genuine choice (existence: F1b)                            SEMANTIC
performative meaning-act → necessary person / entity       CONDITIONAL
necessary subject → necessary entity                       DEFINITIONAL
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
$$Act(s,p) \implies Chooses(s,p,q) \implies FreeWill(s) \land FreeSubject(s) \land IntentionalSubject(s)$$
(Note-se que $Person(s)$ exige personalidade substantiva, $Person(s) := IntentionalSubject(s) \land SubstantivePerson(s)$, permanecendo em aberto: $FreeSubject \to Person$ é OPEN).

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

**Bridge (Weak act to strong act).** `weak_act_implies_strong_act := ∀ s p, act(s, p) → Act(s, p)` (*unforced open intentionality bridge; separated by CountermodelWeakActWithoutMeaning*).

**Definition (Subject actuality).** SubjectExists(s) := ∃ p, Act(s, p).

**Definition (Intentional Subject vs. Substantive Person).** IntentionalSubject(s) := ∃ p, Means(s, p) (*the subject who means content, derived from Act*). Person(s) := IntentionalSubject(s) ∧ SubstantivePerson(s), where SubstantivePerson(s) is an independent substantive personal center. (The performative datum strictly derives IntentionalSubject, but leaves SubstantivePerson model-theoretically independent; Act → Person is OPEN and substantive personhood requires AxTwoSubjects).

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

\[ asserts speaker NoWeakAct → False \]

**Proof.** Assume asserts speaker NoWeakAct. Follows under **A10**, **A2**. ∎

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

\[ Asserts s p → ∃ s', p', Act s' p' \]

**Proof.** Assume Asserts s p. Follows under **A2**. ∎

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

\[ A(s, p) ↔ Asserts s p ∨ Incorrect(s, p) \]

**Proof.** Evaluating by disjunctive cases under **A2**. ∎

`Lean: Order.lean#L57 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`


### Stage III — The Subject of Thought

The act is always an act *of* a subject and *about* content. From the performative datum Γ reads off the existence of a subject of thought (C21), the subject's inseparability from its act, and the collapse of the subject into the person (*esse est agere*). The stage is definitional modulo the vocabulary of agency.

**Proposition C21 (At least one subject exists).**

Derived from the performative act-datum.

\[ (∃ s, p, Act s p) → ∃ s, SubjectExists(s) \]

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

\[ (∃ s, p, Act s p) → ∃ s, SubjectExists(s) ∧ Agent(s) \]

**Proof.** T4 (C23) — the subject is an agent (`Agent` is analytical `:= True`): derived from the existence of an intentional act (C68 → C21). Footprint: `{Initiates, Means, State, Subject}`. ∎

**Obstruction.** `CountermodelActWithoutSubject` — an act occurring with no actualizing subject (see Appendix C.1).

**Γ's answer.** the step is DEFINITIONAL in Γ, not LOGICAL: it follows from Act → Agent: the subject of an intentional act is an agent.

`Lean: Plurality.lean#L75 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`

**Theorem C24 (At least one intentional subject exists).**

Someone who means content

\[ (∃ s, p, Act s p) → ∃ s, IntentionalSubject(s) \]

**Proof.** Assume ∃ s, p, Act s p. Follows under **A2**. ∎

**Obstruction.** `CountermodelNoPerson` — The bare act-datum `∃ s p, A s p` does not force any `Person`.

**Γ's answer.** the step is DEFINITIONAL in Γ, not LOGICAL: it follows from Act → IntentionalSubject: an act witnesses an intentional subject; substantive Personhood is model-theoretically independent.

`Lean: Plurality.lean#L83 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`

**Proposition C25 (Every rational act carries a personal feature exactly when it carries a logical feature).**

Personhood and logic travel together.

\[ ∀ a, RationalAct(a) → (CarriesPersonalFeature(a) ↔ CarriesLogicalFeature(a)) \]

**Proof.** Evaluating by disjunctive cases under **A2**, **A5**. ∎

`Lean: Person.lean#L138 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`

**Proposition C49 (Meaning needs a subject).**

Whatever is meant is meant by someone.

\[ Means(s, p) → ∃ t, Means(t, p) \]

**Proof.** No meaning without a subject (analytic): the intentional relation `Means : Subject → Prop → Prop` only exists relata-subjected, so the subject of any meaning is itself the witness. ∎

`Lean: Choice.lean#L137 · uses A2, A5 · DEFINITIONAL ✔`

**Proposition C57 (Retorsion — asserting that no actual subject exists refutes itself).**

\[ Asserts speaker NoSubject → False \]

**Proof.** Assume Asserts speaker NoSubject. Follows under **A2**. ∎

`Lean: Choice.lean#L400 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`

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

`Lean: Choice.lean#L292 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`

**Lemma C51 (Any person has a choice field).**

A person is always before two incompatible alternatives.

\[ Person(s) → ∃ p, q, ChoiceField(s, p, q) \]

**Proof.** Audit notice (freedom/choice fix, 2026-09-18): this yields `ChoiceField`, NOT genuine `Chooses`. The agent is related only to the adopted content `p`; the rejected horn `¬p` is supplied by pure logic (`incompatible_self_negation`), not by the agent. The genuine form (both horns co-meant) is BLOCKED on `rejectedHornCoMeant`. Nominal wrapper of `intentional_hasChoiceField` (the §12 label adds nothing). ∎

`Lean: Choice.lean#L322 · uses A2, A5 · DEFINITIONAL ✔`

**Proposition C52 (The choice field exists).**

Some subject is before two incompatible alternatives.

\[ (∃ s, p, A(s, p)) → ∃ s, p, q, ChoiceField(s, p, q) \]

**Proof.** C52 (field form) — the field is real: derived from an intentional act(datum, (C68 → C52)) through the WEAKER predicate `Intentional` (via `act_implies_intentional`), not through the §12 person label: `SubjectExists`/`Intentional` suffices. Footprint: `{Initiates, Means, State, Subject}` (VOCAB only). ∎

`Lean: Choice.lean#L332 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`

**Proposition C53 (Performative retorsion — asserting that no choice field exists refutes itself).**

Footprint: `{Initiates, Means, State, Subject}` (VOCAB only; zero AxTwoSubjects).

\[ Asserts speaker NoChoiceField → False \]

**Proof.** Assume Asserts speaker NoChoiceField. Follows under **A2**. ∎

`Lean: Choice.lean#L357 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`

**Axiom A6 · AxTwoSubjects (META).**
\[ (¬N_T ∧ ¬N_F) → ∃ s₁, s₂, Person(s₁) ∧ Person(s₂) ∧ s₁ ≠ s₂ \]
The *reality* of right-and-wrong demands that there be at least two distinct persons. Narrower than the former single bridge `AxValueInterpersonal` (plurality only…

*Philosophical cost:* A substantive interpersonal metaphysics. A lone judging subject, and the unit world of a single act, remain logically consistent with every earlier premise, so the demand for a second distinct person is posited, not deduced. Plural personal reality is bought with this declared bridge.

**Theorem C54 (Right-and-wrong commits a choice field).**

Where there is truth and error, someone is before an incompatible pair.

\[ (¬N_T ∧ ¬N_F) → ∃ s, p, q, ChoiceField(s, p, q) \]

**Proof.** C54 (field form): "No right and wrong without (a field of) choice" — whenever the distinction holds, some subject before a choice field exists via AxTwoSubjects(poem P5). The genuine `Chooses` conclusion is BLOCKED on `rejectedHornCoMeant`. ∎

`Lean: Choice.lean#L373 · uses A2, A5, A6 · METAPHYSICAL ⚠`

**Theorem C61 (Right-and-wrong implies someone who means).**

(poem P3, line 18 "há certo e há errado → há significado → há alguém para quem algo significar")

\[ (¬N_T ∧ ¬N_F) → ∃ s, p, Means(s, p) \]

**Proof.** C61: `JUDGE_HAS_CHOICE_FIELD` (C54) composes with `rightWrongDistinction` (C36) to yield a field; its first conjunct is a meaning-act, so some subject means some content. ∎

`Lean: Choice.lean#L393 · uses A2, A5, A6 · METAPHYSICAL ⚠`

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

`Lean: Choice.lean#L492 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`

**Proposition C98 (Deliberate choice entails genuine choice in the co-meaning sense).**

\[ DeliberateChoice(s, p, q) → Chooses s p q \]

**Proof.** Assume DeliberateChoice(s, p, q). The required witness is constructed under **A2**, **A5**. ∎

`Lean: Choice.lean#L498 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`

**Proposition C99 (Under the explicit Candidate C bridge, an intentional act yields semantic selection).**

\[ act_implies_asserts_bridge → (∃ s, p, Act s p) → ∃ s, p, q, Selects(s, p, q) \]

**Proof.** Assume act_implies_asserts_bridge, and ∃ s, p, Act s p. The required witness is constructed under **A2**. ∎

`Lean: Choice.lean#L695 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`

**Proposition C100 (Exact decomposition of deliberate choice (Route C milestone)).**

Deliberate choice between `p` and `q` is definitionally equivalent to semantic selection of `p` against `q` plus awareness (intentional representation) of the alternative horn `q`.

\[ DeliberateChoice(s, p, q) ↔ Selects(s, p, q) ∧ Means(s, q) \]

**Proof.** The required witness is constructed under **A11**, **A12**, **A2**, **A5**. ∎

`Lean: Choice.lean#L506 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`

**Axiom A13 · AxActPolarity (SEM).**
\[ ∀ s, p, Act s p → Means(s, ¬p) \]
Act polarity: initiating an intentional act constitutively endows the agent with the representation of its contradictory negation.

**Axiom A14 · AxIntentionalChoice (SEM).**
\[ ∀ s, p, Act s p → ∃ q, Chooses s p q \]
Genuine choice is constitutive of intentional action: an intentional act is an initiation performed through the subject's apprehension of an incompatible alternative.

**Theorem F1b (Free will exists).**

Some subject genuinely chooses between incompatible alternatives.

\[ (∃ s, p, Act s p) → ∃ s, FreeWill(s) \]

**Proof.** Primary target theorem closing F1b under the performative datum of intentional action and the adopted constitutive principle AxIntentionalChoice. Footprint: `{AxIntentionalChoice, Initiates, Means, State, Subject}`. ∎

**Obstruction.** `CountermodelVeridicalMeaning` — The act-datum does not force `genuineChoice_exists` even under the Logos definition of `Chooses`: veridical meaning makes co-meaning an incompatible pair impossible while the whole agency/choice/order fragment holds.

**Obstruction.** `CountermodelNoFreeWill` — Mere occurrence of an act does not entail genuine choice: an uninterpreted determined act with `Chooses := False` satisfies the datum while `Chooses` and `FreeWill` stay empty.

**Γ's answer.** the step rests on a substantive semantic principle, not logic alone.

`Lean: Choice.lean#L1120 · uses A2, A5, A11, A12, A14 · SEMANTIC ⚠`

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

\[ Asserts speaker (¬∃ τ, □ τ) → False \]

**Proof.** Under **a2**, the assumption refutes itself. ∎

`Lean: Choice.lean#L1229 · uses A2, A5, A11, A12 · DEFINITIONAL ✔`

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

\[ PersonStabilityPrinciple → (∀ s, p, Act s p → Person(s)) → (∃ s, p, Act s p) → ∃ s, Person(s) ∧ NecessarySubject(s) \]

**Proof.** Assume PersonStabilityPrinciple, and ∀ s, p, Act s p → Person(s), and ∃ s, p, Act s p. The required witness is constructed under **A2**. ∎

**Obstruction.** `CountermodelPersonNotNecessary` — A person need not be a necessary subject: `Person → NecessarySubject` fails as a logical law (subject exists only in the `true` world).

**Γ's answer.** Conditional upon PersonStabilityPrinciple; hostile countermodels show that performative agency does not logically force modal subject-necessity.

`Lean: Love.lean#L98 · uses A2, A5, A11, A12 · CONDITIONAL ✔`

**Proposition C91 (A subject that is necessary has an entity-correlate that is a necessary entity).**

\[ NecessarySubject(s) → NecessaryEntity(EntityOf(s)) \]

**Proof.** Necessity(lift) (subject → entity, C91): if the subject `s` persists in every world (`NecessarySubject(s)`), its entity-correlate `EntityOf(s)` is an entity that exists in every world. The lift is *definitional*: `ExistsAt` is one shared relation and `EntityOf` is the Truthmaker(embedding), so both sides unfold to `∀ w, ExistsAt(w, EntityOf(s))`. It carries no SEM/META price; its force is exactly the definitions chosen in Plurality/Truthmaker. Hostile separation (not a logical law): `CountermodelSubjectNecessityNotEntityNecessity` in HostileSemantics. Footprint: `{Subject}`. ∎

**Obstruction.** `CountermodelSubjectNecessityNotEntity` — Subject-persistence does not entail entity-necessity by logic alone: the transfer fails with independent persistence/existence predicates.

**Γ's answer.** the step is DEFINITIONAL in Γ, not LOGICAL: it follows from `subject_nec_entity_nec : NecessarySubject s → NecessaryEntity (EntityOf s)` (definitional lift).

`Lean: Modal.lean#L103 · uses A2 · DEFINITIONAL ✔`

**Corollary C92 (Conditional C92).**

If person stability holds and intentional action confers personhood, an intentional act yields a necessary entity.

\[ PersonStabilityPrinciple → (∀ s, p, Act s p → Person(s)) → (∃ s, p, Act s p) → ∃ e, NecessaryEntity(e) \]

**Proof.** Assume PersonStabilityPrinciple, and ∀ s, p, Act s p → Person(s), and ∃ s, p, Act s p. The required witness is constructed under **A2**. ∎

**Obstruction.** `CountermodelPersonNotNecessary` — `Person → NecessarySubject` as a logical law (see Appendix C.1).

**Γ's answer.** Conditional upon PersonStabilityPrinciple; hostile countermodels show that performative agency does not logically force modal entity-necessity.

`Lean: Love.lean#L109 · uses A2, A5, A11, A12 · CONDITIONAL ✔`


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

- GAPMAP claims with a kernel declaration located (FOUND): **88** / 114
- Steps with an **English meaning in code**: **114** / 114
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
- **Kernel theorems supporting the architecture (984 intentional unmapped helper/infrastructure theorems):**
  - *Hostile countermodel separations (10):* act_exists_of_act, not_entails_content_person, not_entails_decoupled_freewill, not_entails_person, not_entails_plurality, not_entails_substantive_autonomy, not_entails_substantive_intentionality, not_entails_substantive_person, not_entails_substantive_rationality, subject_exists_of_act
  - *Modal calculus S4/K4 machinery (112):* DeepModalFrontier.C0_not_entails_C1, DeepModalFrontier.C1_not_entails_C2, DeepModalFrontier.modal_volition_iff_primitive_decomposition, DeepModalFrontier.model_MC31_consistent, DeepModalFrontier.model_MC32_consistent, DeepModalFrontier.model_MC33_consistent, DeepModalFrontier.model_MC34_consistent, DeepModalFrontier.model_MC35_consistent, DeepModalFrontier.model_MC36_consistent, DeepModalFrontier.model_MC37_consistent, DeepModalFrontier.model_MC38_consistent, DeepModalFrontier.model_MC39_consistent, DeepModalFrontier.model_MC40_consistent, DeepModalFrontier.model_MC41_consistent, DeepModalFrontier.model_MC42_consistent, DeepModalFrontier.model_MC43_consistent, DeepModalFrontier.model_MC44_consistent, DeepModalFrontier.model_MC45_consistent, DeepModalFrontier.nondeterministic_not_entails_modal_freewill, DeepModalFrontier.s5_frame_is_equivalence, DeepModalFrontier.third_regime_consistent, DeepModalFrontier.unique_best_action_optimific_rationality_modal_collapse, Modal.necessary_entity_exists_of_necessary_subject, Modal.subject_nec_entity_nec_iff, ModalCreationAgency.freeWill_not_entails_modal_alternatives, ModalCreationAgency.free_voluntary_implies_voluntary, ModalCreationAgency.modal_freedom_implies_local_freedom, ModalCreationAgency.modal_freedom_yields_contingency_of_creation, ModalCreationAgency.model_MC1_necessary_impersonal_consistent, ModalCreationAgency.model_MC2_necessary_person_no_agency_consistent, ModalCreationAgency.model_MC3_fixed_choice_consistent, ModalCreationAgency.model_MC4_necessary_creation_consistent, ModalCreationAgency.model_MC5_contingent_creation_consistent, ModalCreationAgency.model_MC6_passive_no_creation_accessible, ModalCreationAgency.necessary_free_agent_not_entails_contingent_creation, ModalCreationAgency.passive_not_entails_voluntary, ModalCreationAgency.voluntary_implies_passive, ModalPossibilityFrontier.causal_determinism_modal_collapse, ModalPossibilityFrontier.determining_psr_iff_reason_determinism, ModalPossibilityFrontier.determining_psr_incompatible_with_modal_freedom, ModalPossibilityFrontier.immutable_will_incompatible_with_contingent_act, ModalPossibilityFrontier.model_MC13_consistent, ModalPossibilityFrontier.model_MC14_consistent, ModalPossibilityFrontier.model_MC15_consistent, ModalPossibilityFrontier.model_MC16_consistent, ModalPossibilityFrontier.model_MC17_consistent, ModalPossibilityFrontier.model_MC18_consistent, ModalPossibilityFrontier.model_MC19_consistent, ModalPossibilityFrontier.model_MC20_consistent, ModalPossibilityFrontier.model_MC21_consistent, ModalPossibilityFrontier.model_MC22_consistent, ModalPossibilityFrontier.model_MC23_consistent, ModalPossibilityFrontier.model_MC24_consistent, ModalPossibilityFrontier.model_MC25_consistent, ModalPossibilityFrontier.model_MC26_consistent, ModalPossibilityFrontier.model_MC27_consistent, ModalPossibilityFrontier.model_MC28_consistent, ModalPossibilityFrontier.model_MC29_consistent, ModalPossibilityFrontier.model_MC30_consistent, ModalPossibilityFrontier.necessary_knowledge_not_entails_necessary_will, ModalPossibilityFrontier.necessary_rationality_not_entails_necessary_act, ModalPossibilityFrontier.reason_determinism_modal_collapse, ModalPossibilityFrontier.target_contingent_creation_iff_missing_modal_settlement, Necessity.dia_def, Necessity.nec4, Necessity.nec4PH, Necessity.necDistinction_content, Necessity.necK, Necessity.necKPH, Necessity.necMP, Necessity.necT, Necessity.necTPH, Necessity.nec_apply, TheologicalModalHardening.accessible_worldwise_truthmaking_consistent, TheologicalModalHardening.axGlobalGround_refutes_empty_world, TheologicalModalHardening.boxR_universal_iff, TheologicalModalHardening.coexistence_without_creation_relation, TheologicalModalHardening.constant_domain_yields_necessary_entity, TheologicalModalHardening.divine_identification_theorem, TheologicalModalHardening.empty_world_excluded_by_non_emptiness_constraint, TheologicalModalHardening.frameE2_truthmaking_holds_at_actual, TheologicalModalHardening.g1_god_alone_properties, TheologicalModalHardening.g2_creation_properties, TheologicalModalHardening.g3_coexistence_no_creation_properties, TheologicalModalHardening.g4_creation_is_contingent, TheologicalModalHardening.god_alone_has_no_creation, TheologicalModalHardening.intentional_subject_not_entails_freewill, TheologicalModalHardening.logical_truth_in_empty_world, TheologicalModalHardening.model_E_absolute_empty_world, TheologicalModalHardening.model_G_consistent, TheologicalModalHardening.model_NA_consistent, TheologicalModalHardening.model_ND_consistent, TheologicalModalHardening.model_NP_consistent, TheologicalModalHardening.necessary_being_not_entails_divine, TheologicalModalHardening.necessary_entity_not_entails_subject, TheologicalModalHardening.necessary_entity_not_entails_ultimate_ground, TheologicalModalHardening.necessary_entity_not_forces_contingent_creation, TheologicalModalHardening.necessary_entity_rules_out_empty_world, TheologicalModalHardening.necessary_existence_not_entails_uniqueness, TheologicalModalHardening.necessary_ground_can_be_non_ultimate, TheologicalModalHardening.necessary_non_emptiness_not_entails_necessary_entity, TheologicalModalHardening.necessary_not_contingent, TheologicalModalHardening.neg_necessary_entity_holds_in_concrete_ontology, TheologicalModalHardening.non_contingent_not_entails_necessary, TheologicalModalHardening.plural_necessary_entities_consistent, TheologicalModalHardening.retorsion_fails_against_no_necessary_entity, TheologicalModalHardening.retorsion_not_forces_necessary_subject, TheologicalModalHardening.self_grounding_violates_irreflexivity, TheologicalModalHardening.subject_not_entails_agency, TheologicalModalHardening.u1_independence_exclusion_forces_uniqueness, TheologicalModalHardening.uniform_witness_yields_necessary_entity, TheologicalModalHardening.well_foundedness_forces_ultimate_ground
  - *Semantic satisfaction & object-language lemmas (25):* Core.atomicWitnessFalsehood, Core.someTruthAndSomeFalsehood, Core.tschema, HostileSemantics.act_exists_of_act, HostileSemantics.not_entails_content_person, HostileSemantics.not_entails_decoupled_freewill, HostileSemantics.not_entails_person, HostileSemantics.not_entails_plurality, HostileSemantics.not_entails_substantive_autonomy, HostileSemantics.not_entails_substantive_intentionality, HostileSemantics.not_entails_substantive_person, HostileSemantics.not_entails_substantive_rationality, HostileSemantics.subject_exists_of_act, Semantics.atom_not_necessarily_false, Semantics.atom_not_necessarily_true, Semantics.sat_and, Semantics.sat_imp, Semantics.sat_not, Semantics.sat_or, Semantics.strongTruth_and_contingent_content, Semantics.strongTruth_is_not_atomic, Truthmaker.sat_ground_and, Truthmaker.sat_ground_imp, Truthmaker.sat_ground_not, Truthmaker.sat_ground_or
  - *Intermediate agency, order, and relation steps (847):* A14DerivationAudit.NormativeSeparationModel.hostile_model_normativity_compatible_with_not_universal_a14, A14DerivationAudit.NormativeSeparationModel.moral_agent_acts, A14DerivationAudit.NormativeSeparationModel.moral_agent_chooses, A14DerivationAudit.NormativeSeparationModel.moral_agent_satisfies_normative_truth, A14DerivationAudit.NormativeSeparationModel.normativity_does_not_entail_universal_a14, A14DerivationAudit.NormativeSeparationModel.unilateral_agent_acts, A14DerivationAudit.NormativeSeparationModel.unilateral_agent_cannot_choose, A14DerivationAudit.normative_action_yields_choice, A14DerivationAudit.normative_route_derives_free_will, A14DerivationAudit.polarity_entails_universal_a14, A14SemanticAudit.a14_iff_missing_horn_principle, A14SemanticAudit.act_contrastive_trivializes_a14, A14SemanticAudit.candidate_principles_fail_to_derive_a14, A14SemanticAudit.contrastive_closure_of_means_fails, A14SemanticAudit.inferential_closure_of_means_fails, A14SemanticAudit.irreducible_semantic_boundary_of_a14, A14SemanticAudit.negation_closure_of_means_fails, A14SemanticAudit.performative_boundary_theorem, A14SemanticAudit.separation_aim_without_self_attr, A14SemanticAudit.separation_author_without_aim, A14SemanticAudit.separation_causal_without_reason, A14SemanticAudit.separation_reason_without_modal, A14SemanticAudit.separation_repr_without_eval, A14SemanticAudit.separation_self_attr_without_causal, A14SemanticAudit.separation_settle_without_authorship, ActionChoiceDefinitions.action_eq_act, ActionChoiceDefinitions.alternative_possibility_conflicts_with_choice_determinism, ActionChoiceDefinitions.anti_cheating_action_without_alternatives, ActionChoiceDefinitions.anti_cheating_determinism_not_compulsion, ActionChoiceDefinitions.genuine_choice_entails_asymmetric_settlement, ActionChoiceDefinitions.genuine_choice_entails_incompatible, ActionChoiceDefinitions.genuine_intentional_action_implies_action, ActionChoiceDefinitions.libertarian_freedom_entails_alternative_possibility, ActionChoiceDefinitions.libertarian_freedom_entails_sourcehood, ActionChoiceDefinitions.model_S1_selection_without_meaning, ActionChoiceDefinitions.model_S2_assertion_without_choice, ActionChoiceDefinitions.model_S3_choice_without_assertion, ActionChoiceDefinitions.model_S4_action_without_choice, ActionChoiceDefinitions.model_S5_deterministic_selection_verified, ActionChoiceDefinitions.model_S6_co_representation_without_leeway, ActionChoiceDefinitions.model_S7_decision_without_alternative, ActionChoiceDefinitions.model_S8_volition_without_action, ActionChoiceDefinitions.selection_not_implies_meaning, AdversarialReductioAudit.affirmation_to_act_derives_one_horn_only, AdversarialReductioAudit.model_M10_mechanical_execution_no_act, AdversarialReductioAudit.model_M11_considered_not_act, AdversarialReductioAudit.model_M12_contrast_without_chooses, AdversarialReductioAudit.model_M7_external_conclusion, AdversarialReductioAudit.model_M8_consideration_without_meaning, AdversarialReductioAudit.model_M9_affirmation_without_meaning, AdversarialReductioAudit.rational_subject_cannot_volitionally_aim_at_rejected_horn, AdversarialReductioAudit.state_A_is_refuted, AdversarialReductioAudit.state_D_is_refuted, AdversarialReductioAudit.uptake_is_renamed_co_meaning_premise, Agency.Cogito_of_bridge, Agency.T1_subjectExists_of_act, Agency.act_datum_implies_initiates, Agency.act_datum_implies_means, Agency.act_decomposition, Agency.act_exists_of_assert, Agency.act_implies_agent, Agency.act_implies_content, Agency.act_implies_initiates, Agency.act_implies_means, Agency.act_implies_rational, Agency.act_of_asserting_no_act, Agency.act_requires_subject, Agency.an_actual_subject_exists_of_act, Agency.assertion_is_act, Agency.assertion_is_weak_act, Agency.noAct_conditional_selfRefutes, Agency.noCogito_selfRefutes, Agency.noSubjectSort_selfRefutes, Agency.noSubject_performative_selfRefutes, Agency.noSubject_selfRefutes, Agency.strong_act_of_weak_act, Agency.subject_exists_of_act, Agency.subject_exists_of_assert, Agency.weak_Cogito, Agency.weak_act_exists_of_assert, AgencyDeterminismConsequences.consequence_A_reasoning_not_entails_libertarian, AgencyDeterminismConsequences.consequence_B_first_person_not_entails_libertarian, AgencyDeterminismConsequences.consequence_C_intentionality_not_entails_libertarian, AgencyDeterminismConsequences.consequence_D_normativity_not_entails_libertarian, AgencyDeterminismConsequences.consequence_E_gamma_freewill_compatible_with_determinism, AgencyDeterminismConsequences.consequence_F_libertarian_requires_new_primitive, AgencyDeterminismConsequences.determinism_compatible_with_gamma_freewill, AgencyDeterminismConsequences.deterministic_rational_realization, AgencyDeterminismConsequences.gamma_freewill_distinct_from_libertarian_freedom, AgencyDeterminismConsequences.master_agency_determinism_synthesis, AgencyDeterminismConsequences.test_M_D1_deterministic, AgencyDeterminismConsequences.test_M_D2_intentionality_compatible_with_determinism, AgencyDeterminismConsequences.test_M_D3_first_person_survives, AgencyDeterminismConsequences.test_M_D4_self_reference_survives, AgencyDeterminismConsequences.test_M_D5_error_and_correction_deterministic, AgencyDeterminismConsequences.test_M_D6_rational_because_survives_determinism, AgencyDeterminismConsequences.test_M_D7_deliberation_survives_determinism, AgencyDeterminismConsequences.test_M_D8_act_execution_deterministic, AgencyDeterminismConsequences.unary_representation_fails_missing_horn, AgencyFrontierAudit.agency_star_is_model_theoretically_independent, AgencyFrontierAudit.agency_without_modal_alternatives, AgencyFrontierAudit.agentCausalSettlement_star_is_model_theoretically_independent, AgencyFrontierAudit.choice_star_is_model_theoretically_independent, AgencyFrontierAudit.freeWill_settlement_is_nomenclatural, AgencyFrontierAudit.indeterminism_does_not_imply_choice, AgencyFrontierAudit.modalFreedom_star_is_model_theoretically_independent, AgencyFrontierAudit.modal_alternatives_without_agency, AgencyFrontierAudit.model_M27_pure_cognitive_resolver, AgencyFrontierAudit.model_M28_deterministic_evaluator, AgencyFrontierAudit.model_M29_passive_truth_tracker, AgencyFrontierAudit.model_M30_automatic_preference_mechanism, AgencyFrontierAudit.model_M31_indifferent_tie_breaker, AgencyFrontierAudit.model_M32_genuine_choice_candidate, AgencyFrontierAudit.old_chooses_compatible_with_determinism, AgencyFrontierAudit.settlementChoice_compatible_with_determinism, AgencyFrontierAudit.settlementChoice_does_not_derive_volition, AgencyFrontierAudit.settlementChoice_is_purely_cognitive, AgencyFrontierAudit.structural_choice_differentiator, AgencyFrontierAudit.volition_star_is_model_theoretically_independent, AxiomNegationAudit.core_compatible_with_neg_a13, AxiomNegationAudit.core_compatible_with_neg_a14, AxiomNegationAudit.core_compatible_with_neg_a4, AxiomNegationAudit.core_compatible_with_neg_a6, AxiomNegationAudit.core_compatible_with_neg_a7, AxiomNegationAudit.core_compatible_with_neg_ground_principle_prop, AxiomNegationAudit.core_compatible_with_neg_transcendental_reflection_intentional, AxiomNegationAudit.core_compatible_with_neg_truthmaker, AxiomNegationAudit.core_compatible_with_neg_universal_thesis_claims_objectivity, AxiomNegationAudit.no_hidden_necessity_synthesis, Choice.T11_choiceField_from_plurality, Choice.act_decomposition, Choice.act_implies_authors, Choice.act_implies_causalTransition, Choice.act_implies_choiceField, Choice.act_missing_horn_iff_chooses, Choice.act_missing_horn_implies_chooses, Choice.act_polarity_implies_conditional, Choice.act_polarity_implies_contrastive, Choice.act_polarity_implies_existential, Choice.act_polarity_implies_existential_choice, Choice.act_polarity_implies_intentional_choice, Choice.act_produces_choice_iff_missing_horn, Choice.alternativeSensitivity_implies_genuineChoice, Choice.asserting_noChoiceField_is_choiceField, Choice.assertion_consistency, Choice.asserts_implies_choice, Choice.asserts_implies_freeAgency, Choice.asserts_implies_selects, Choice.asserts_selects, Choice.asserts_selects_all_incompatible, Choice.bilateral_implies_act_polarity, Choice.canChoose_unfold, Choice.choiceField_exists_from_plurality, Choice.chooses_implies_freeSubject, Choice.chooses_implies_freeWill, Choice.contemplatesWithoutSettling_implies_freeWill, Choice.contemplates_iff_chooses, Choice.contrastive_agency_implies_existential, Choice.contrastive_implies_intentional_choice, Choice.counterfactual_act_implies_genuineChoice, Choice.deliberateAuthorship_implies_chooses, Choice.deliberateAuthorship_implies_deliberateChoice, Choice.deliberateChoice_exists_of_assertion_and_negation_meaning, Choice.deliberateChoice_iff_selects_and_rejects, Choice.deliberateChoice_negation_decomposition, Choice.deliberateChoice_negation_iff, Choice.deliberateResource_of_act_polarity, Choice.deliberateResource_of_bilateral_intentionality, Choice.deliberate_resource_implies_genuine_choice, Choice.deliberates_iff_chooses, Choice.descriptive_act_implies_genuineChoice, Choice.existential_choice_iff_f1b, Choice.f1b_iff_missing_cognitive_horn, Choice.freeSubject_exists, Choice.freeSubject_exists_of_act, Choice.freeSubject_exists_of_contrastive_act, Choice.freeSubject_iff_freeWill, Choice.freeSubject_implies_intentional, Choice.freeSubject_implies_intentionalSubject, Choice.freeWillExists_of_chooses, Choice.freeWillExists_of_genuineChoice, Choice.freeWill_exists_of_act, Choice.freeWill_exists_of_act_polarity, Choice.freeWill_exists_of_contrastive_act, Choice.freeWill_exists_of_doubt_bridge, Choice.freeWill_exists_of_doubt_datum, Choice.freeWill_exists_of_existential_act_polarity, Choice.freeWill_exists_of_existential_choice, Choice.freeWill_iff_means_missing_horn, Choice.freeWill_of_doubt, Choice.genuineChoice_exists_of_act, Choice.genuineChoice_exists_of_act_constitutive, Choice.genuineChoice_exists_of_act_polarity, Choice.genuineChoice_exists_of_bilateral_intentionality, Choice.genuineChoice_exists_of_contrastive_act, Choice.genuineChoice_exists_of_doubt_bridge, Choice.genuineChoice_exists_of_doubt_datum, Choice.genuineChoice_exists_of_existential_act_polarity, Choice.genuineChoice_of_doubt, Choice.genuineChoice_requires_error_possibility, Choice.intentional_choice_implies_contrastive, Choice.intentional_choice_implies_existential_choice, Choice.intentional_hasChoiceField, Choice.judge_asserting_rightWrong_has_choiceField, Choice.meaning_I_needs_subject, Choice.means_missing_horn_iff_chooses, Choice.noChoiceField_contradicts_field, Choice.noSubject_contradicts_subject, Choice.no_one_asserts_incompatible_pair, Choice.no_selection_no_assertion, Choice.reasonResponsive_act_implies_genuineChoice, Choice.rejectedHornCoMeant_implies_genuineChoice, Choice.relationalIntentionality_implies_genuineChoice, Choice.selection_exists, Choice.selfAssertedChoice_factive_implies_chooses, Choice.selfAssertedDeliberateChoice_factive_implies_chooses, Choice.selfAssertedParadox_is_false, Choice.selfAssertedParadox_not_assertable, Choice.selfDenialOfExecutiveChoice_selfRefutes, Choice.selfDenial_implies_genuineChoice_of_a14, Choice.selfDenial_implies_genuineChoice_of_polarity, Choice.teleological_act_implies_genuineChoice, ChoiceRepair.divergence_between_intentional_resolution_and_old_choice, ChoiceRepair.libertarian_freewill_is_model_theoretically_independent, ChoiceRepair.model_A_lib_with_libertarian_freewill, ChoiceRepair.model_B_lib_without_libertarian_freewill, ChoiceRepair.model_M19_cognitive_resolution_without_volition, ChoiceRepair.model_M20_volition_without_alternative_capacity, ChoiceRepair.model_M21_action_selection_without_libertarian_freedom, ChoiceRepair.model_M22_agent_causal_settlement, ChoiceRepair.model_M23_fully_deterministic_deliberator, ChoiceRepair.model_M24_automatic_rational_evaluator, ChoiceRepair.model_M25_passive_truth_tracker, ChoiceRepair.model_M26_choice_without_libertarianism, ChoiceRepair.reductio_derives_compatibilist_freeWill, ChoiceRepair.reductio_derives_settlementChoice, ChoiceRepair.settlementChoice_compatible_with_case_D, ChoiceRepair.settlementChoice_does_not_entail_modal_freedom, ChoiceRepair.settlementChoice_iff_settlement1, ChoiceRepair.settlementChoice_is_definitional_unfolding, ChoiceRepair.settlementChoice_orthogonal_to_old_chooses, CognitiveDiscrimination.AD_alone_insufficient_for_missing_horn, CognitiveDiscrimination.BR_alone_insufficient_for_missing_horn, CognitiveDiscrimination.D1_discrimination_not_entails_choice, CognitiveDiscrimination.D2_discrimination_not_entails_meaning, CognitiveDiscrimination.D3_discrimination_present_without_choice_or_freewill, CognitiveDiscrimination.D4_act_not_derives_discrimination, CognitiveDiscrimination.affirmation_not_implies_representation, CognitiveDiscrimination.discrimination_equiv_intentional_distinction, CognitiveDiscrimination.horn_local_decomposition_blind_to_second_horn, CognitiveDiscrimination.level1_not_implies_level2, CognitiveDiscrimination.level2_not_implies_level3, CognitiveDiscrimination.level3_not_implies_level4, CognitiveDiscrimination.level4_not_implies_level5, CognitiveDiscrimination.level5_local_choice_not_implies_global_freewill, CognitiveDiscrimination.level6_freewill_not_implies_libertarian_freedom, CognitiveDiscrimination.means_iff_aboutness, CognitiveDiscrimination.means_iff_awareness, CognitiveDiscrimination.means_iff_consideration, CognitiveDiscrimination.means_iff_entertainment, CognitiveDiscrimination.means_iff_representation, CognitiveDiscrimination.means_implies_identity, CognitiveDiscrimination.means_implies_individuation, CognitiveDiscrimination.means_not_implies_alternative_awareness, CognitiveDiscrimination.means_not_implies_counterfactual_availability, CognitiveDiscrimination.means_not_implies_discrimination, CognitiveDiscrimination.recognition_of_incompatibility_requires_alternative_awareness, CognitiveDiscrimination.representation_not_implies_affirmation, CognitiveDiscrimination.subprinciples_derive_missing_cognitive_horn, CognitiveDiscrimination.unary_intentional_collapse, CognitiveToAgencyFrontier.model_M13_dual_consideration_without_evaluation, CognitiveToAgencyFrontier.model_M14_evaluation_without_commitment, CognitiveToAgencyFrontier.model_M15_settlement_without_choice, CognitiveToAgencyFrontier.model_M16_deterministic_settlement, CognitiveToAgencyFrontier.model_M17_compatibilist_choice, CognitiveToAgencyFrontier.model_M18_agent_causal_settlement, CognitiveToAgencyFrontier.reductio_cannot_collapse_to_one_horn, CognitiveToAgencyFrontier.reductio_frontier_status, CognitiveToAgencyFrontier.reductio_induces_asymmetric_status_transition, CognitiveToAgencyFrontier.reductio_necessarily_asymmetric, CognitiveToAgencyFrontier.reductio_proves_settlement_1, CognitiveToAgencyFrontier.settlement_1_does_not_imply_settlement_3, ConditionalTheology.agency_closure_act_to_chooses, ConditionalTheology.agency_closure_act_to_freeSubject, ConditionalTheology.agency_closure_act_to_freewill, ConditionalTheology.agency_closure_act_to_intentionalSubject, ConditionalTheology.freewill_not_entails_necessity, ConditionalTheology.freewill_not_entails_normativity, ConditionalTheology.freewill_not_entails_persistence, ConditionalTheology.freewill_not_entails_rationality, ConditionalTheology.freewill_not_entails_reflexive_subjectivity, ConditionalTheology.freewill_not_entails_relationality, ConditionalTheology.freewill_not_entails_teleology, ConditionalTheology.freewill_not_entails_value, ConstitutiveNormativeFreeWill.T1_constitutive_normative_truth_implies_agency, ConstitutiveNormativeFreeWill.T2_constitutive_normative_truth_implies_alternative, ConstitutiveNormativeFreeWill.T3_constitutive_normative_truth_implies_chooses, ConstitutiveNormativeFreeWill.T4_constitutive_normative_truth_implies_free_will, ConstitutiveNormativeFreeWill.T5_necessary_constitutive_normativity_implies_necessary_free_will, ConstitutiveNormativeFreeWill.T6_necessary_deontic_truth_implies_necessary_genuine_free_subject, ConstitutiveNormativeFreeWill.T7_necessary_deontic_truth_implies_not_d3, ConstitutiveNormativeFreeWill.cm22_impersonal_world_strictly_fails_constitutive_normativity, ConstitutiveNormativeFreeWill.constitutive_deontic_truth_implies_genuine_chooses, ConstitutiveNormativeFreeWill.hostile_model_outcome_1_compatibilist_satisfies_core_freedom_under_d3, ConstitutiveNormativeFreeWill.hostile_model_outcome_2_d3_contradicts_constitutive_deontic_truth, ConstitutiveNormativeFreeWill.retorsion_establishes_normative_truth_exists, ConstitutiveNormativeFreeWill.retorsion_pragmatic_address_excludes_impersonal_model, ContextualDevelopment.cross_context_development_implies_core, ContextualDevelopment.development_not_entails_freewill, ContextualDevelopment.distinct_contexts_same_subject, ContextualDevelopment.model_M_D_consistent, ContextualDevelopment.model_M_F_consistent, ContextualDevelopment.model_M_N_consistent, ContextualDevelopment.model_M_S_consistent, ContextualDevelopment.performance_not_entails_freewill, ContextualDevelopment.presence_not_entails_free_selection, ContextualDevelopment.threshold_audit_correct, DeepContrastiveFrontier.F1b_is_relatively_minimal, DeepContrastiveFrontier.M_existential_only_refutes_universal, DeepContrastiveFrontier.M_existential_only_validates_existential, DeepContrastiveFrontier.collapse_destroys_all_deliberation, DeepContrastiveFrontier.collapse_preserves_assertions, DeepContrastiveFrontier.collapse_preserves_executive_choice, DeepContrastiveFrontier.contrastive_blind_invariance_refutes_freewill, DeepContrastiveFrontier.diagonal_freeAgency_without_freeWill_coherent, DeepContrastiveFrontier.diagonal_negative_choice_coherent, DeepContrastiveFrontier.diagonal_positive_choice_not_forces_choice, DeepContrastiveFrontier.discrimination_not_implies_incompatibility, DeepContrastiveFrontier.exclusion_not_implies_deliberation, DeepContrastiveFrontier.existential_a14_iff_F1b, DeepContrastiveFrontier.freewill_not_implies_necessity, DeepContrastiveFrontier.freewill_not_implies_person, DeepContrastiveFrontier.freewill_not_implies_ultimate_ground, DeepContrastiveFrontier.layer_L1_refl, DeepContrastiveFrontier.universal_a14_implies_existential, DefinitiveAgencyFrontier.agent_causation_does_not_imply_reason_responsiveness, DefinitiveAgencyFrontier.collapse_invariance_pre_commitment, DefinitiveAgencyFrontier.definitive_agency_frontier_synthesis, DefinitiveAgencyFrontier.delusion_of_agency_separation, DefinitiveAgencyFrontier.free_will_hierarchy_implications, DefinitiveAgencyFrontier.libertarian_freewill_fails_to_derive_substantive_person, DefinitiveAgencyFrontier.model_A1_puppet, DefinitiveAgencyFrontier.model_A2_external_optimizer, DefinitiveAgencyFrontier.model_A3_subpersonal_execution, DefinitiveAgencyFrontier.model_A4_authorless_execution, DefinitiveAgencyFrontier.model_A5_author_without_self_attribution, DefinitiveAgencyFrontier.model_AC1_deterministic_agent_causal, DefinitiveAgencyFrontier.model_AC2_indeterministic_chance, DefinitiveAgencyFrontier.model_AC3_externally_determined, DefinitiveAgencyFrontier.model_AC4_agent_causal_without_alternatives, DefinitiveAgencyFrontier.model_AC5_full_libertarian, DefinitiveAgencyFrontier.model_C1_passive_truth_tracker, DefinitiveAgencyFrontier.model_C2_formal_evaluator, DefinitiveAgencyFrontier.model_C3_suspended_judgment, DefinitiveAgencyFrontier.model_C4_assertion_without_commitment, DefinitiveAgencyFrontier.model_C5_commitment_without_assertion, DefinitiveAgencyFrontier.model_V1_pure_theoretician, DefinitiveAgencyFrontier.model_V2_aim_without_deliberative_settlement, DefinitiveAgencyFrontier.model_V3_commitment_to_unwanted_fact, DefinitiveAgencyFrontier.model_V4_external_objective, DefinitiveAgencyFrontier.model_V5_spontaneous_aim, DefinitiveAgencyFrontier.performative_datum_supplies_executive_initiation, DefinitiveAgencyFrontier.reason_responsiveness_compatible_with_determinism, DefinitiveAgencyFrontier.retorsion_denial_does_not_commit_to_content, DefinitiveAgencyFrontier.sincerity_is_independent, DefinitiveAgencyFrontier.standalone_volition_fails_to_derive_agency, DefinitiveAgencyFrontier.two_sided_independence_commitment, DefinitiveAgencyFrontier.two_sided_independence_volition, DeterministicReductioFrontier.M16_refutes_chooses, DeterministicReductioFrontier.M16_refutes_freewill, DeterministicReductioFrontier.choice_not_implies_chooses, DeterministicReductioFrontier.cognitive_agency_not_implies_choice, DeterministicReductioFrontier.factive_assertion_of_no_act_is_contradictory, DeterministicReductioFrontier.performative_datum_not_implies_reductio_progression, DeterministicReductioFrontier.performative_self_refutation_compatible_with_determinism, DeterministicReductioFrontier.positive_action_without_reductio, DeterministicReductioFrontier.reductio_asymmetry_non_affirmation, DeterministicReductioFrontier.reductio_forces_rational_settlement, DeterministicReductioFrontier.reductio_frontier_summary, DeterministicReductioFrontier.self_denial_of_reasoning_self_refutes, DeterministicReductioFrontier.test_A_first_person_survives_determinism, DeterministicReductioFrontier.test_B_intentionality_survives_determinism, DeterministicReductioFrontier.test_C_normative_rule_realized_deterministically, DeterministicReductioFrontier.test_D_truth_factivity_survives_determinism, DeterministicReductioFrontier.test_E_error_possibility_compatible_with_determinism, DeterministicReductioFrontier.test_F_self_reference_survives_determinism, DeterministicReductioFrontier.test_G_diachronic_identity_survives_determinism, DeterministicReductioFrontier.test_H_causal_closure_survives_determinism, DeterministicReductioFrontier.weak_act_not_implies_strong_act, DirectNormativeFreeWill.hostile_model_a_impersonal_normativity_cannot_generate_agency, DirectNormativeFreeWill.hostile_model_b_determinism_precludes_alternative_availability, DirectNormativeFreeWill.hostile_model_b_determinism_refutes_kantian_principle, DirectNormativeFreeWill.hostile_model_c_compatibilist_satisfies_core_freedom, DirectNormativeFreeWill.necessary_normativity_implies_necessary_free_subject, DirectNormativeFreeWill.necessary_normativity_implies_necessary_free_will, DirectNormativeFreeWill.necessary_normativity_implies_necessary_genuine_freedom, DirectNormativeFreeWill.normative_alternative_implies_chooses, DirectNormativeFreeWill.normative_alternative_implies_core_free_subject, DirectNormativeFreeWill.normative_alternative_implies_core_free_will, DirectNormativeFreeWill.normative_alternative_implies_genuine_chooses, DirectNormativeFreeWill.normative_alternative_implies_genuine_free_subject, DirectNormativeFreeWill.normative_deliberation_yields_strong_chooses, DirectNormativeFreeWill.normative_route_to_metaphysical_indeterminism, DirectNormativeFreeWill.normative_route_to_not_d3, EssenceActCollapse.agent_causal_implies_volitional_indifference, EssenceActCollapse.free_creation_anti_collapse, EssenceActCollapse.hardened_modal_freedom_forces_distinct_worlds, EssenceActCollapse.involuntary_act_consistent, EssenceActCollapse.modal_collapse_action_theorem, EssenceActCollapse.modal_collapse_theorem, EssenceActCollapse.model_MC10_consistent, EssenceActCollapse.model_MC11_consistent, EssenceActCollapse.model_MC12_consistent, EssenceActCollapse.model_MC7_consistent, EssenceActCollapse.model_MC8_consistent, EssenceActCollapse.model_MC9_consistent, EssenceActCollapse.necessary_nature_not_entails_necessary_act, EssenceActCollapse.statement2_implies_statement1, EssenceActCollapse.statement3_implies_statement2, EssenceActCollapse.sufficient_freedom_not_entails_volitional_indifference, EssenceActCollapse.unexecuted_volition_consistent, EssenceActCollapse.volitional_indifference_implies_nondeterministic, EssenceActCollapse.volitional_indifference_implies_sufficient_freedom, ExecutiveDeliberativeFrontier.M_det_refutes_chooses, ExecutiveDeliberativeFrontier.M_det_refutes_missing_cognitive_horn, ExecutiveDeliberativeFrontier.M_det_validates_executive_choice, ExecutiveDeliberativeFrontier.exclusion_not_implies_representation, ExecutiveDeliberativeFrontier.freeAgency_not_implies_necessary_subject, ExecutiveDeliberativeFrontier.freeAgency_not_implies_person, ExecutiveDeliberativeFrontier.freeAgency_not_implies_ultimate_ground, ExecutiveDeliberativeFrontier.mechanical_prover_lacks_deliberation, ExecutiveDeliberativeFrontier.modal_branching_not_induces_representation, ExecutiveDeliberativeFrontier.retorsion_NoChoice_self_refutes, ExecutiveDeliberativeFrontier.retorsion_NoDeliberation_consistent, ExecutiveDeliberativeFrontier.retorsion_NoFreeWill_consistent, ExecutiveDeliberativeFrontier.schema_S1_performative_contradiction, ExecutiveDeliberativeFrontier.schema_S2_coherent, ExecutiveDeliberativeFrontier.schema_S4_satisfiable_and_non_self_refuting, ExecutiveDeliberativeFrontier.schema_S5_executive_without_deliberation_coherent, ExecutiveDeliberativeFrontier.trackA_act_not_implies_deliberates, ExecutiveDeliberativeFrontier.trackA_asserts_implies_choice, ExecutiveDeliberativeFrontier.trackA_choice_implies_freeAgency, ExecutiveDeliberativeFrontier.trackA_choice_not_implies_chooses, ExecutiveDeliberativeFrontier.trackA_chooses_implies_freeWill, ExecutiveDeliberativeFrontier.trackA_chooses_not_implies_choice, ExecutiveDeliberativeFrontier.trackA_deliberates_iff_chooses, ExecutiveDeliberativeFrontier.trackA_freeAgency_not_implies_freeWill, ExecutiveDeliberativeFrontier.trackB_selfDenialOfExecutiveChoice_selfRefutes, FreeWillIndependence.bridge_B2_derives_choice, FreeWillIndependence.deterministic_status_transition_without_freewill, FreeWillIndependence.f1b_target_definitionally_unfolded, FreeWillIndependence.freewill_is_model_theoretically_independent, FreeWillIndependence.identical_deliberation_case_A, FreeWillIndependence.identical_deliberation_case_D, FreeWillIndependence.identical_deliberation_case_M, FreeWillIndependence.intentional_resolution_excludes_choice_of_same_horns, FreeWillIndependence.model_A_gamma_with_freewill, FreeWillIndependence.model_B_gamma_without_freewill, FreeWillIndependence.model_M14_plus_evaluation_without_commitment, FreeWillIndependence.model_deterministic_rationality_without_modal_freedom, FreeWillIndependence.model_libertarian_settlement_without_reasons, FreeWillIndependence.rationality_orthogonal_to_libertarian_freedom, FreeWillIndependence.settlement_1_compatible_with_no_chdo, FreeWillIndependence.settlement_1_is_assembled_package, FreeWillInvariance.causal_necessity_not_entails_logical_necessity, FreeWillInvariance.core_gamma_free_will_invariant, FreeWillInvariance.first_freewill_sensitive_layer_is_L10, FreeWillInvariance.model_FW0_consistent, FreeWillInvariance.model_FW10_consistent, FreeWillInvariance.model_FW1_consistent, FreeWillInvariance.model_FW2_consistent, FreeWillInvariance.model_FW3_consistent, FreeWillInvariance.model_FW4_consistent, FreeWillInvariance.model_FW5_consistent, FreeWillInvariance.model_FW6_consistent, FreeWillInvariance.model_FW7_consistent, FreeWillInvariance.model_FW8_consistent, FreeWillInvariance.model_FW9_consistent, FreeWillInvariance.performative_datum_not_entails_freewill, FreeWillInvariance.retorsion_under_determinism_valid, GroundPerson.AxGroundBearing, GroundingFrontier.a4_does_not_imply_single_common_ground, GroundingFrontier.a4_does_not_imply_unique_ground, GroundingFrontier.collapse_invariance_impersonal, GroundingFrontier.cyclic_grounding_has_no_ultimate_ground, GroundingFrontier.denial_of_necessary_ground_is_non_self_refuting, GroundingFrontier.grounding_frontier_synthesis, GroundingFrontier.implication_G2_implies_G1, GroundingFrontier.implication_G4_implies_G2, GroundingFrontier.infinite_descending_chain_has_no_ultimate_ground, GroundingFrontier.minimal_ultimate_ground_theorem, GroundingFrontier.model_G10_personal_ground_with_no_plurality, GroundingFrontier.model_G1_worldwise_grounding, GroundingFrontier.model_G2_uniform_necessary_ground, GroundingFrontier.model_G3_infinite_ground_chain, GroundingFrontier.model_G4_cyclic_grounding, GroundingFrontier.model_G5_multiple_ultimate_grounds, GroundingFrontier.model_G6_unique_impersonal_ultimate_ground, GroundingFrontier.model_G7_necessary_personal_ground, GroundingFrontier.model_G8_necessary_ground_without_ultimate, GroundingFrontier.model_G9_intentional_subject_with_impersonal_ground, GroundingFrontier.model_P1_impersonal_substrate, GroundingFrontier.model_P2_structural_realization, GroundingFrontier.model_P3_emergent_intentionality, GroundingFrontier.model_P4_multiple_impersonal_grounders, GroundingFrontier.model_P5_anonymous_ultimate_ground, GroundingFrontier.performative_subject_and_nec_truth_do_not_force_necessary_entity, GroundingFrontier.quantifier_exchange_under_uniqueness, GroundingFrontier.separation_G1_not_implies_G2, GroundingFrontier.ultimate_ground_does_not_imply_plurality, GroundingFrontier.ultimate_ground_does_not_imply_uniqueness, GroundingFrontier.uniform_ground_iff_worldwise_and_missing_horn, GroundingFrontier.worldwise_fails_to_derive_uniform_ground, HardenedInvariance.act_not_implies_person, HardenedInvariance.agent_invariant_iff_agent_neutral_core, HardenedInvariance.causal_determination_not_implies_logical_validity, HardenedInvariance.chooses_not_implies_agent_causal_settlement, HardenedInvariance.chooses_not_implies_modal_freedom, HardenedInvariance.chooses_not_implies_nondeterministic, HardenedInvariance.contextual_retorsion_datum, HardenedInvariance.cross_context_development_soundness, HardenedInvariance.first_agency_sensitive_layer_is_L1, HardenedInvariance.first_choice_sensitive_layer_is_L10, HardenedInvariance.first_compatibilist_freewill_sensitive_layer_is_L11, HardenedInvariance.first_intentionality_sensitive_layer_is_L2, HardenedInvariance.first_libertarian_sensitive_layer_is_L12, HardenedInvariance.first_substantive_personhood_sensitive_layer_is_L9, HardenedInvariance.freeSubject_equiv_freeWill, HardenedInvariance.freeSubject_not_implies_person, HardenedInvariance.freewill_entails_intentionalSubject, HardenedInvariance.freewill_invariant_iff_freewill_neutral_core, HardenedInvariance.freewill_not_implies_agent_causal_settlement, HardenedInvariance.freewill_not_implies_modal_freedom, HardenedInvariance.freewill_not_implies_nondeterministic, HardenedInvariance.libertarian_freedom_iff_agent_causal_settlement, HardenedInvariance.logical_validity_not_implies_metaphysical_necessity, HardenedInvariance.person_entails_intentionalSubject, HardenedInvariance.proof_correctness_not_implies_freewill, HardenedInvariance.proof_occurrence_not_implies_freewill, HardenedInvariance.proof_occurrence_not_implies_intentional_agency, HardenedInvariance.realizesAt_conclusion, HardenedInvariance.realizesAt_sound, HardenedInvariance.strict_core_inclusion, IndubitableNormativeFreeWill.dnf1_denial_of_existence_violates_core, IndubitableNormativeFreeWill.dnf2_descriptive_value_lacks_prescriptive_force, IndubitableNormativeFreeWill.dnf3_impersonal_ought_fails_address, IndubitableNormativeFreeWill.dnf4_monolithic_command_lacks_opposition, IndubitableNormativeFreeWill.dnf5_ungraspable_directive_is_not_agential_address, IndubitableNormativeFreeWill.dnf6_isolated_intelligibility_refutes_normativity, IndubitableNormativeFreeWill.dnf7_cannot_deny_choice_from_co_meaning, IndubitableNormativeFreeWill.dnf8_cannot_deny_freewill_from_choice, IndubitableNormativeFreeWill.impossibility_of_denying_chooses, IndubitableNormativeFreeWill.impossibility_of_denying_freewill, IndubitableNormativeFreeWill.indubitable_normative_free_will, IndubitableNormativeFreeWill.intelligibility_not_trivially_realization, IndubitableNormativeFreeWill.necessary_normativity_implies_necessary_free_will, IndubitableNormativeFreeWill.normative_agency_reduction, IndubitableNormativeFreeWill.normative_alternative_reduction, JointForcing.A1_not_implies_A2, JointForcing.A2_implies_A1, JointForcing.A6_A7_synergistic_forcing, JointForcing.A6_alone_insufficient, JointForcing.A7_alone_insufficient, JointForcing.agency_not_implies_global_ground, JointForcing.choice_and_global_ground_not_implies_necessary_subject, JointForcing.empty_inconsistency_basis, JointForcing.global_ground_and_personal_ground_not_implies_personal_ultimate, JointForcing.global_ground_and_personal_ground_not_implies_unique, JointForcing.joint_forcing_synthesis, JointForcing.joint_satisfiability_synthesis, JointForcing.plurality_and_global_ground_not_implies_personal_ground, JointForcing.plurality_and_personal_ground_not_implies_love, JointForcing.plurality_and_personal_ground_not_implies_plural_necessary_persons, JointForcing.retorsion_not_implies_choice, JointForcing.truthmaker_and_ground_prop_not_implies_global_ground, Love.love_affects, Love.love_not_harms, Love.loves_of_helps, NegativeRetorsionAudit.Level10.converse_step2_fails, NegativeRetorsionAudit.Level10.converse_step3_fails, NegativeRetorsionAudit.Level10.equiv_act, NegativeRetorsionAudit.Level10.equiv_asserts, NegativeRetorsionAudit.Level10.equiv_intentional, NegativeRetorsionAudit.Level10.equiv_means, NegativeRetorsionAudit.Level10.step1_noi_implies_all_not_means, NegativeRetorsionAudit.Level10.step2_not_means_implies_not_act, NegativeRetorsionAudit.Level10.step3_not_act_implies_not_asserts, NegativeRetorsionAudit.Level7.countermodel_neg_a17_compatible_with_asserting_eo, NegativeRetorsionAudit.Level7.countermodel_neg_a17_does_not_imply_noi, NegativeRetorsionAudit.Level7.countermodel_neg_no_thinker_eo_does_not_imply_noi, NegativeRetorsionAudit.Level7.neg_a17_implies_neg_no_dep_thinker_eo, NegativeRetorsionAudit.Level7.neg_no_act_implies_neg_no_assert, NegativeRetorsionAudit.Level7.neg_no_thinker_implies_neg_no_act, NegativeRetorsionAudit.Level7.noi_implies_neg_a17, NegativeRetorsionAudit.Level7.noi_implies_neg_no_thinker_eo, NegativeRetorsionAudit.NegativeRetorsionSignature.noi_iff_pointwise, NegativeRetorsionAudit.canonical_act_noi_proves_P, NegativeRetorsionAudit.canonical_act_noi_refutes_noi, NegativeRetorsionAudit.canonical_asserts_noi_selfRefutes, NegativeRetorsionAudit.canonical_exists_asserts_noi_selfRefutes, NegativeRetorsionAudit.canonical_means_noi_proves_P, NegativeRetorsionAudit.canonical_means_noi_refutes_noi, NegativeRetorsionAudit.canonical_noi_contradicts_a17, NegativeRetorsionAudit.canonical_noi_implies_not_act, NegativeRetorsionAudit.canonical_noi_implies_not_asserts, NegativeRetorsionAudit.canonical_noi_implies_not_exists_act, NegativeRetorsionAudit.canonical_noi_implies_not_exists_asserts, NegativeRetorsionAudit.canonical_noi_implies_not_exists_means, NegativeRetorsionAudit.canonical_noi_implies_not_means, NegativeRetorsionAudit.contrapositive_asserts_noi, NegativeRetorsionAudit.contrapositive_means_noi, NegativeRetorsionAudit.converse_trap_P_does_not_imply_means_noi, NegativeRetorsionAudit.converse_trap_unasserted_does_not_imply_noi, NegativeRetorsionAudit.converse_trap_unmeant_does_not_imply_noi, NegativeRetorsionAudit.level0_model_M0_empty_subject_satisfies_noi, NegativeRetorsionAudit.level0_model_M1_inanimate_universe_satisfies_noi, NegativeRetorsionAudit.level0_noi_incompatible_with_a17, NegativeRetorsionAudit.level1_signature_noi_not_meant, NegativeRetorsionAudit.level2_signature_asserts_noi_selfRefutes, NegativeRetorsionAudit.level3_act_noi_consistent_with_false_noi, NegativeRetorsionAudit.level4_intentional_understanding_forces_subject, NegativeRetorsionAudit.level4_mechanical_presentation_without_intentionality, NegativeRetorsionAudit.level4_proof_occurrence_without_subject, NegativeRetorsionAudit.level5_domain_item_versus_subject_sort, NegativeRetorsionAudit.level5_noi_cannot_self_apply, NegativeRetorsionAudit.level6_diagonal_meant_implies_false, NegativeRetorsionAudit.level6_diagonal_true_implies_unmeant, NegativeRetorsionAudit.level6_model_diagonal_false_consistent, NegativeRetorsionAudit.level6_model_diagonal_true_consistent, NegativeRetorsionAudit.model_M0_specs, NegativeRetorsionAudit.model_M1_specs, NegativeRetorsionAudit.model_M2_specs, NegativeRetorsionAudit.model_M3_specs, NegativeRetorsionAudit.model_M4_specs, NegativeRetorsionAudit.model_M6_specs, NegativeRetorsionAudit.model_M7_specs, NegativeRetorsionAudit.negative_retorsion_master_synthesis, NegativeRetorsionAudit.noi_canonical_iff_pointwise, NegativeRetorsionAudit.performed_denial_gradient, NegativeRetorsionAudit.regime_M5_is_provably_incoherent, NegativeRetorsionAudit.unassertability_does_not_imply_falsity, NonLibertarianCreation.contrastive_trilemma_theorem, NonLibertarianCreation.explanation_not_entails_determination, NonLibertarianCreation.model_NC10_consistent, NonLibertarianCreation.model_NC11_consistent, NonLibertarianCreation.model_NC12_consistent, NonLibertarianCreation.model_NC13_consistent, NonLibertarianCreation.model_NC14_consistent, NonLibertarianCreation.model_NC15_consistent, NonLibertarianCreation.model_NC16_consistent, NonLibertarianCreation.model_NC1_consistent, NonLibertarianCreation.model_NC2_consistent, NonLibertarianCreation.model_NC3_consistent, NonLibertarianCreation.model_NC4_consistent, NonLibertarianCreation.model_NC5_consistent, NonLibertarianCreation.model_NC6_consistent, NonLibertarianCreation.model_NC7_consistent, NonLibertarianCreation.model_NC8_consistent, NonLibertarianCreation.model_NC9_consistent, NonLibertarianCreation.nondetermined_not_entails_nonfree, NonLibertarianCreation.nondetermined_not_entails_random, NonLibertarianCreation.nonfree_not_entails_random, NormativeTruth.context_normative_truth_exists, NormativeTruth.established_free_subject_defeats_d3, NormativeTruth.impersonal_model_excludes_genuine_normative_truth, NormativeTruth.necessary_normative_truth_exists, NormativeTruth.no_normative_truth_is_self_refuting, NormativeTruth.normative_free_subject_grounds_agency, NormativeTruth.normative_free_subject_implies_indeterminism, NormativeTruth.normative_free_subject_implies_not_d3, NormativeTruth.normative_truth_exists, NormativeTruth.right_wrong_content_and_normativity, NormativeTruth.right_wrong_is_normative_truth, Order.act_iff_correct_or_incorrect, Order.correct_implies_selection, Order.correct_implies_selection_all_incompatible, Order.fallible_false, Order.judgment_implies_act, Order.judgment_implies_cogito, Order.judgment_of_no_act_is_incorrect, Order.rightDistinctWrong_implies_meaning, Order.rightWrongDistinction_implies_meaning, Person.act_implies_intentional, Person.act_implies_intentionalSubject, Person.intentionalSubject_exists_of_act, Person.intentionalSubject_exists_of_assert, Person.intentional_exists_of_act, Person.intentional_exists_of_assert, Person.intentional_implies_subjectExists_of_bridge, Person.person_is_intentional, Person.subjectExists_implies_intentional, Person.subjectExists_implies_intentionalSubject, Plurality.T1_of_assert, Plurality.T1_subjectExists_from_plurality, Plurality.T4_agentExists_from_plurality, Plurality.T4_of_assert, Plurality.T5_intentional_of_assert, Plurality.T5_personExists_from_plurality, Plurality.notAlone, PostA14Frontier.agency_ladder_frontier_synthesis, PostA14Frontier.archetype_deterministic_evaluator, PostA14Frontier.archetype_non_reflexive_chooser, PostA14Frontier.archetype_passive_truth_tracker, PostA14Frontier.archetype_puppet_unauthored_aims, PostA14Frontier.archetype_theoretical_deliberator, PostA14Frontier.post_a14_derives_old_chooses, PostA14Frontier.post_a14_fails_to_derive_commitment, PostA14Frontier.post_a14_fails_to_derive_discretionary_choice, PostA14Frontier.separation_commitment_without_volition, PostA14Frontier.separation_settlement_without_commitment, PostA14Frontier.separation_volition_without_agency, PostA14Frontier.settlement_plus_aim_horn_yields_volition, PostA14Frontier.settlement_plus_horn_yields_commitment, ProofSpecificContrast.a14_proof_performance_is_contrastive, ProofSpecificContrast.model_M0_trace_without_subject, ProofSpecificContrast.model_M2_not_implies_M3, ProofSpecificContrast.model_M3_not_implies_M4, ProofSpecificContrast.model_M4_not_implies_M5, ProofSpecificContrast.model_M5_not_implies_M6, ProofSpecificContrast.performative_proof_yields_freewill, ProofSpecificContrast.proof_specific_contrast_yields_freewill, ProofSpecificContrast.reductio_engages_incompatible_contents, ProofSpecificContrast.retorsion_proof_derives_F1b, ProofSpecificContrast.trace_occurrence_not_implies_cognitive_uptake, ProofSpecificContrast.universal_a14_false_for_arbitrary_acts, Retorsion.a17_strong_implies_a17_weak, Retorsion.a17b_implies_a17_weak, Retorsion.bigO_bigS_intentional_synthesis, Retorsion.deterministic_transcendental_subject_refutes_freewill, Retorsion.deterministic_transcendental_subject_refutes_person, Retorsion.everything_objective_self_applies, Retorsion.everything_subjective_self_applies, Retorsion.exists_intentional_subject_of_retorsion, Retorsion.exists_intentional_subject_of_subjective, Retorsion.exists_means_not_exists_dependson, Retorsion.exists_non_objective_item, Retorsion.exists_non_subjective_item, Retorsion.exists_objective_of_retorsion, Retorsion.exists_subjective_not_exists_freewill, Retorsion.exists_subjective_not_exists_person, Retorsion.exists_subjective_of_retorsion, Retorsion.intentional_not_freewill, Retorsion.intentional_not_person, Retorsion.intentional_subject_not_person, Retorsion.means_not_dependson, Retorsion.not_everything_objective, Retorsion.not_everything_subjective, Retorsion.objective_and_subjective_disjoint, Retorsion.objective_or_subjective, Retorsion.person_not_freewill, Retorsion.pig_retorsion_exposes_premise_smuggling, Retorsion.representation_not_depends_on_person, Retorsion.restricted_bridge_derives_a17_weak, Retorsion.restricted_bridge_derives_a17b, Retorsion.retorsion_boundary_principle, Retorsion.retorsion_establishes_affirmation, Retorsion.retorsion_no_act, Retorsion.retorsion_no_choiceField, Retorsion.retorsion_no_subject, Retorsion.retorsion_no_truth, Retorsion.retorsion_no_weak_act, Retorsion.retorsion_refutes_denial, Retorsion.subjective_implies_intentional_subject, Retorsion.subjective_not_depends_on_person, Retorsion.universal_objectivity_subjective, Retorsion.weakened_retorsion_derives_intentional_subject, Retorsion.winged_pig_derived_of_pig_reflection, Retorsion.witness_slippage_separation, StrongActionChoice.chooses_weak_eq_chooses, StrongActionChoice.countermodel_10_epistemically_uncertain_but_deterministic_future, StrongActionChoice.countermodel_11_stochastically_described_but_deterministic, StrongActionChoice.countermodel_12_indeterminism_without_agent, StrongActionChoice.countermodel_13_physical_indet_agent_det, StrongActionChoice.countermodel_14_deterministic_maximal_deliberator, StrongActionChoice.countermodel_15_deterministic_agent_causal_source, StrongActionChoice.countermodel_16_different_priors_not_identical_availability, StrongActionChoice.countermodel_17_counterfactual_without_availability, StrongActionChoice.countermodel_18_logical_possibility_without_availability, StrongActionChoice.countermodel_19_canonical_genuine_choice, StrongActionChoice.countermodel_19_witnesses_indeterminism, StrongActionChoice.countermodel_19_witnesses_neg_d3, StrongActionChoice.countermodel_1_single_path_intentional_action, StrongActionChoice.countermodel_20_d3_excludes_genuine_choice, StrongActionChoice.countermodel_21_deterministic_performed_denial, StrongActionChoice.countermodel_22_platonic_normative_realism, StrongActionChoice.countermodel_23_deterministic_subject_normativism, StrongActionChoice.countermodel_2_deterministic_pseudo_choice_verified, StrongActionChoice.countermodel_3_deterministic_co_representation, StrongActionChoice.countermodel_4_selection_without_choice, StrongActionChoice.countermodel_5_choice_without_assertion, StrongActionChoice.countermodel_6_authorship_without_alternative, StrongActionChoice.countermodel_7_alternative_representation_without_choice, StrongActionChoice.countermodel_8_deterministic_volition, StrongActionChoice.countermodel_9_agent_causal_but_deterministic_action, StrongActionChoice.denial_of_genuine_choice_is_self_refuting, StrongActionChoice.denial_of_no_metaphysical_alternative_is_self_refuting, StrongActionChoice.free_subject_conflicts_with_d3, StrongActionChoice.free_subject_implies_metaphysical_indeterminism, StrongActionChoice.genuine_act_implies_genuine_chooses, StrongActionChoice.genuine_chooses_conflicts_with_d3, StrongActionChoice.genuine_chooses_conflicts_with_d5, StrongActionChoice.genuine_chooses_implies_metaphysical_indeterminism, StrongActionChoice.libertarian_chooses_conflicts_with_d3, StrongActionChoice.libertarian_chooses_conflicts_with_d5, StrongActionChoice.metaphysical_indeterminism_neg_d3, StrongActionChoice.necessary_normative_grounding_derives_necessary_free_subject, StrongActionChoice.necessary_normative_grounding_implies_not_d3, StrongActionChoice.normative_fact_not_implies_free_subject, StrongActionChoice.normative_grounding_derives_free_subject, StrongActionChoice.performed_denial_consistent_with_d3, StrongActionChoice.performed_denial_implies_act, StrongActionChoice.performed_denial_implies_chooses, StrongActionChoice.performed_denial_implies_cognitive_contrast, StrongActionChoice.performed_denial_not_implies_genuine_chooses, StrongActionChoice.performed_denial_not_implies_metaphysical_availability, StrongActionChoice.strong_act_not_implies_genuine_chooses, StrongActionChoice.strong_act_not_implies_strong_chooses, StrongActionChoice.strong_chooses_compatible_with_d3, StrongActionChoice.strong_chooses_compatible_with_d5, StrongActionChoice.strong_chooses_not_implies_genuine_chooses, StrongActionChoice.strong_chooses_without_immediate_volition, StrongActionChoice.volition_without_action, SubContrastFoundations.act_not_implies_reasoning, SubContrastFoundations.consequence_cannot_be_incompatible, SubContrastFoundations.distinct_props_are_incompatible, SubContrastFoundations.first_unavoidable_cognitive_layer, SubContrastFoundations.generalized_expressivity_collapse, SubContrastFoundations.hierarchy_L1_not_implies_L3, SubContrastFoundations.hierarchy_L3_not_implies_L4, SubContrastFoundations.hierarchy_L4_not_implies_L7, SubContrastFoundations.hierarchy_L7_not_implies_L8, SubContrastFoundations.hierarchy_L8_not_implies_L10, SubContrastFoundations.intensional_object_diff_not_implies_alternative_diff, SubContrastFoundations.intentionality_not_intrinsically_contrastive, SubContrastFoundations.means_not_implies_cognitive_exclusion, SubContrastFoundations.negation_not_inferrable_from_truth, SubContrastFoundations.propositional_closure_cannot_generate_incompatible_horn, SubContrastFoundations.reasoning_not_implies_discrimination, SubContrastFoundations.reasoning_not_implies_distinct_contents, SubContrastFoundations.reasoning_not_implies_means_conclusion, SubContrastFoundations.reasoning_not_implies_means_premise, SubContrastFoundations.subprinciples_jointly_sufficient_for_choice, SubContrastFoundations.vertical_asymmetry_blind_to_horizontal_distinction, SubContrastFoundations.vertical_sort_separation, Value.alone_no_other_affects, Value.harm_affects, Value.help_affects
- **Kernel-derived status** (#print axioms + axiom `Tag:`): **59 ✔** · **22 ⚠** · **0 ◆** (unique steps detailed in the map)
- **Reconciled claim inventory (114 total):** 81 unique active steps (59 ✔ + 22 ⚠) · 7 repeated / dissolved (→) · 20 blocked / missing (✖) · 5 deferred (➖) · 1 other (ANSWERED)
- **Philosophical status histogram:** **CONDITIONAL 2** · **COUNTERMODEL 20** · **DEFINITIONAL 27** · **DISSOLVED 6** · **LOGICAL 30** · **METAPHYSICAL 15** · **OPEN 6** · **SEMANTIC 8**
- GAPMAP × derived status: **no divergences** (transcription verified).
- **Steps ⚠ under a substantive axiom (SEM/META)** (24): C15, C18, C19, C20, C28, C29, C32, C33, C34, C40, C41, C42, C43, C44, C45, C46, C47, C48, C54, C60, C61, C74, F1b, F4
- **Displayed ✔ by vocabulary only (axiom-free modulo declared vocabulary)** (kernel footprint contains only the statement's own VOCAB axioms — no SEM/META/TRANS): C100, C101, C21, C23, C24, C25, C30, C39, C49, C51, C52, C53, C55, C56, C57, C58, C62, C68, C77, C83, C84, C85, C86, C91, C92, C94, C97, C98, C99, F1a
- Kernel × GAPMAP footprint: **no divergences**.
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
| F5 | §28 EternalRelation | DISSOLVED | Conditional T14: Under person stability and the plurality-love principle, two distinct persons stand in an eternal love relation. |
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
| C16 | `Logos.Truthmaker.lawExcludedMiddle` | [Truthmaker.lean#L140](formal/Logos/Truthmaker.lean#L140) | `{CL}` | `Semantics.Form`, `Semantics.World`, `Truthmaker.NecessarilyTrue`, `Truthmaker.TrueAt` | **C19** `T7_excludedMiddleInstance`, `TheologicalModalHardening.axGlobalGround_refutes_empty_world`, `TheologicalModalHardening.logical_truth_in_empty_world` |
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
| C25 | `Logos.Person.inseparability_24b` | [Person.lean#L138](formal/Logos/Person.lean#L138) | `{Initiates, Means, State, Subject, CL}` | `Agency.A`, axiom `Means` (VOCAB), axiom `Subject` (VOCAB), `Agency.act_implies_means`, `Core.IsFalse`, `Core.T`, `Person.CarriesLogicalFeature`, `Person.CarriesPersonalFeature`, `Person.HasFeature`, `Person.RationalAct` | — |
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
| F1a | `Logos.Choice.person_hasChoiceField` | [Choice.lean#L322](formal/Logos/Choice.lean#L322) | `{Means, Subject}` | axiom `Subject` (VOCAB), `Choice.ChoiceField`, `Choice.intentional_hasChoiceField`, `Person.Person`, `Person.person_is_intentional` | **C54** `JUDGE_HAS_CHOICE_FIELD`, `Choice.choiceField_exists_from_plurality` |
| F1b | `Logos.Choice.freeWill_exists` | [Choice.lean#L1120](formal/Logos/Choice.lean#L1120) | `{AxIntentionalChoice, Initiates, Means, State, Subject}` | `Agency.Act`, axiom `Subject` (VOCAB), `Choice.FreeWill`, `Choice.freeWill_exists_of_act` | — |
| F2 | — | — | — | — | — |
| F3 | — | — | — | — | — |
| F4 | `Logos.Love.T13_someoneLovable` | [Love.lean#L81](formal/Logos/Love.lean#L81) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Love.Lovable`, `Person.Person`, **C40** `T12_twoPersons` | — |
| F5 | `Logos.Love.T14_eternalRelation_conditional` | [Love.lean#L119](formal/Logos/Love.lean#L119) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Love.Loves`, `Love.PersonStabilityPrinciple`, `Love.PluralityLovePrinciple`, `Person.Person`, `Plurality.NecessarySubject`, **C40** `T12_twoPersons` | **C45** `T14_square_conditional`, **C44** `T14_world_conditional` |
| F6 | — | — | — | — | — |
| Q7.2 | `CountermodelPersonNotNecessary.ExistsAt` | [HostileSemantics.lean#L720](formal/Logos/HostileSemantics.lean#L720) | `{}` | — | — |
| C35 | `Logos.Core.negatedAbsolutes` | [Core.lean#L129](formal/Logos/Core.lean#L129) | `{}` | `Core.N_F`, `Core.N_T`, **C6** `notEverythingTrue`, **C2** `notNothingTrue` | — |
| C36 | `Logos.Core.rightWrongDistinction` | [Core.lean#L145](formal/Logos/Core.lean#L145) | `{}` | `Core.N_F`, `Core.N_T`, **C6** `notEverythingTrue`, **C2** `notNothingTrue` | `IndubitableNormativeFreeWill.dnf1_denial_of_existence_violates_core`, **FAITH-1** `necDistinction`, `NormativeTruth.right_wrong_content_and_normativity`, **C40** `T12_twoPersons`, `StrongActionChoice.countermodel_22_platonic_normative_realism`, `StrongActionChoice.countermodel_23_deterministic_subject_normativism`, **C74** `aloneExcluded` |
| C37 | `Logos.Semantics.bothNecessarilyTrueAndFalse` | [Semantics.lean#L102](formal/Logos/Semantics.lean#L102) | `{CL}` | `Semantics.Form`, `Semantics.NecessarilyFalse`, `Semantics.NecessarilyTrue`, **C13** `lawExcludedMiddle`, **C14** `nonContradiction` | **C59** `strongTruthExists`, `Semantics.strongTruth_and_contingent_content` |
| C59 | `Logos.Semantics.strongTruthExists` | [Semantics.lean#L113](formal/Logos/Semantics.lean#L113) | `{CL}` | `Semantics.Form`, `Semantics.NecessarilyFalse`, `Semantics.NecessarilyTrue`, **C37** `bothNecessarilyTrueAndFalse` | **C93** `noStrongTruth_selfRefutes` |
| C93 | `Logos.Semantics.noStrongTruth_selfRefutes` | [Semantics.lean#L121](formal/Logos/Semantics.lean#L121) | `{CL}` | `Semantics.Form`, `Semantics.NecessarilyTrue`, **C59** `strongTruthExists` | **C94** `noStrongTruth_assertable_refutes` |
| C94 | `Logos.Choice.noStrongTruth_assertable_refutes` | [Choice.lean#L1229](formal/Logos/Choice.lean#L1229) | `{Initiates, Means, State, Subject, CL}` | `Agency.Act`, `Agency.Asserts`, axiom `Subject` (VOCAB), `Semantics.Form`, `Semantics.NecessarilyTrue`, **C93** `noStrongTruth_selfRefutes` | — |
| C95 | `Logos.Semantics.atoms_are_modally_free` | [Semantics.lean#L146](formal/Logos/Semantics.lean#L146) | `{}` | `Semantics.NecessarilyFalse`, `Semantics.NecessarilyTrue`, `Semantics.atom_not_necessarily_false`, `Semantics.atom_not_necessarily_true` | **C96** `some_formula_contingent` |
| C96 | `Logos.Semantics.some_formula_contingent` | [Semantics.lean#L160](formal/Logos/Semantics.lean#L160) | `{}` | `Semantics.Form`, `Semantics.NecessarilyFalse`, `Semantics.NecessarilyTrue`, **C95** `atoms_are_modally_free` | `Semantics.strongTruth_and_contingent_content` |
| C38 | `Logos.Necessity.necDistinction` | [Necessity.lean#L116](formal/Logos/Necessity.lean#L116) | `{}` | `Core.N_F`, `Core.N_T`, **C36** `rightWrongDistinction`, `Necessity.Necessity`, `Semantics.World` | `Necessity.necDistinction_content` |
| C39 | `Logos.Choice.T11_choiceField` | [Choice.lean#L292](formal/Logos/Choice.lean#L292) | `{Initiates, Means, State, Subject}` | `Agency.A`, axiom `Subject` (VOCAB), `Alternatives.Incompatible`, **C26** `T9_incompatibleAlternatives`, `Core.IsFalse`, `Core.T`, `Person.IntentionalSubject`, **C24** `T5_intentionalSubjectExists` | — |
| C40 | `Logos.Plurality.T12_twoPersons` | [Plurality.lean#L44](formal/Logos/Plurality.lean#L44) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), **C36** `rightWrongDistinction`, `Person.Person`, **FAITH-2** `AxTwoSubjects` | `Choice.choiceField_exists_from_plurality`, **C41** `T13_someoneLovable`, **C43** `T14_content_conditional`, **C42** `T14_eternalRelation_conditional`, **C47** `T12_directedPair_conditional`, `Plurality.T1_subjectExists_from_plurality`, `Plurality.T5_personExists_from_plurality`, **C48** `cogito_from_T12`, `Plurality.notAlone` |
| C41 | `Logos.Love.T13_someoneLovable` | [Love.lean#L81](formal/Logos/Love.lean#L81) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Love.Lovable`, `Person.Person`, **C40** `T12_twoPersons` | — |
| C48 | `Logos.Plurality.cogito_from_T12` | [Plurality.lean#L57](formal/Logos/Plurality.lean#L57) | `{AxTwoSubjects, Means, Subject}` | axiom `Means` (VOCAB), axiom `Subject` (VOCAB), `Person.IntentionalSubject`, `Person.Person`, `Person.person_is_intentional`, **C40** `T12_twoPersons` | `Order.fallible_false` |
| C49 | `Logos.Choice.meaning_needs_subject` | [Choice.lean#L137](formal/Logos/Choice.lean#L137) | `{Means, Subject}` | axiom `Means` (VOCAB), axiom `Subject` (VOCAB) | — |
| C50 | `Logos.Choice.incompatible_self_negation` | [Choice.lean#L113](formal/Logos/Choice.lean#L113) | `{}` | `Alternatives.Incompatible` | `Choice.act_implies_authors`, `Choice.act_implies_choiceField`, `Choice.act_polarity_implies_contrastive`, `Choice.act_polarity_implies_intentional_choice`, `Choice.asserting_noChoiceField_is_choiceField`, `Choice.asserts_selects`, `Choice.deliberate_resource_implies_genuine_choice`, `Choice.genuineChoice_exists_of_act`, `Choice.genuineChoice_exists_of_existential_act_polarity`, `Choice.genuineChoice_of_doubt`, `Choice.intentional_hasChoiceField`, `Choice.judge_asserting_rightWrong_has_choiceField`, `Choice.rejectedHornCoMeant_implies_genuineChoice`, `Choice.selfDenial_implies_genuineChoice_of_polarity`, **C55** `judge_commits` |
| C51 | `Logos.Choice.person_hasChoiceField` | [Choice.lean#L322](formal/Logos/Choice.lean#L322) | `{Means, Subject}` | axiom `Subject` (VOCAB), `Choice.ChoiceField`, `Choice.intentional_hasChoiceField`, `Person.Person`, `Person.person_is_intentional` | **C54** `JUDGE_HAS_CHOICE_FIELD`, `Choice.choiceField_exists_from_plurality` |
| C52 | `Logos.Choice.choiceField_exists` | [Choice.lean#L332](formal/Logos/Choice.lean#L332) | `{Initiates, Means, State, Subject}` | `Agency.A`, axiom `Subject` (VOCAB), `Choice.ChoiceField`, `Choice.intentional_hasChoiceField`, `Person.act_implies_intentional` | — |
| C53 | `Logos.Choice.noChoiceField_selfRefutes` | [Choice.lean#L357](formal/Logos/Choice.lean#L357) | `{Initiates, Means, State, Subject}` | `Agency.Act`, `Agency.Asserts`, axiom `Subject` (VOCAB), `Choice.NoChoiceField`, `Choice.asserting_noChoiceField_is_choiceField` | `Retorsion.retorsion_no_choiceField` |
| C54 | `Logos.Choice.JUDGE_HAS_CHOICE_FIELD` | [Choice.lean#L373](formal/Logos/Choice.lean#L373) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Choice.ChoiceField`, **C51** `person_hasChoiceField`, `Core.N_F`, `Core.N_T`, `Person.Person`, **FAITH-2** `AxTwoSubjects` | **C61** `rightWrong_implies_someone_means` |
| C55 | `Logos.Order.judge_commits` | [Order.lean#L172](formal/Logos/Order.lean#L172) | `{Initiates, Means, State, Subject, CL}` | `Agency.A`, axiom `Initiates` (VOCAB), axiom `Means` (VOCAB), axiom `State` (VOCAB), axiom `Subject` (VOCAB), `Alternatives.Incompatible`, `Choice.ChoiceField`, **C50** `incompatible_self_negation`, `Core.IsFalse`, `Core.T`, `Order.Correct`, `Order.Incorrect` | `Order.rightWrongDistinction_implies_meaning` |
| C56 | `Logos.Value.alone_no_other_help_harm` | [Value.lean#L95](formal/Logos/Value.lean#L95) | `{Subject}` | axiom `Subject` (VOCAB), `Value.Alone`, `Value.Harms`, `Value.Helps` | — |
| C57 | `Logos.Choice.noSubject_selfRefutes` | [Choice.lean#L400](formal/Logos/Choice.lean#L400) | `{Initiates, Means, State, Subject}` | `Agency.Asserts`, `Agency.NoSubject`, axiom `Subject` (VOCAB), `Agency.noSubject_performative_selfRefutes` | `Retorsion.retorsion_no_subject` |
| C42 | `Logos.Love.T14_eternalRelation_conditional` | [Love.lean#L119](formal/Logos/Love.lean#L119) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Love.Loves`, `Love.PersonStabilityPrinciple`, `Love.PluralityLovePrinciple`, `Person.Person`, `Plurality.NecessarySubject`, **C40** `T12_twoPersons` | **C45** `T14_square_conditional`, **C44** `T14_world_conditional` |
| C43 | `Logos.Love.T14_content_conditional` | [Love.lean#L151](formal/Logos/Love.lean#L151) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Love.Loves`, `Love.PluralityLovePrinciple`, `Person.Person`, **C40** `T12_twoPersons` | — |
| C44 | `Logos.Love.T14_world_conditional` | [Love.lean#L129](formal/Logos/Love.lean#L129) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Love.Loves`, `Love.PersonStabilityPrinciple`, `Love.PluralityLovePrinciple`, **C42** `T14_eternalRelation_conditional`, `Necessity.NecessityPH`, `Person.Person`, `Plurality.EntityOf`, `Plurality.NecessarySubject`, `Semantics.World`, `Truthmaker.ExistsAt` | — |
| C45 | `Logos.Love.T14_square_conditional` | [Love.lean#L141](formal/Logos/Love.lean#L141) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Love.Loves`, `Love.PersonStabilityPrinciple`, `Love.PluralityLovePrinciple`, **C42** `T14_eternalRelation_conditional`, `Necessity.Necessity`, `Person.Person`, `Plurality.NecessarySubject`, `Semantics.World` | — |
| C46 | `Logos.Value.valueInterpersonal_of_split_conditional` | [Value.lean#L139](formal/Logos/Value.lean#L139) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Core.N_F`, `Core.N_T`, `Person.Person`, `Value.Affects`, **FAITH-2** `AxTwoSubjects`, `Value.PersonsAffectPrinciple` | — |
| C47 | `Logos.Plurality.T12_directedPair_conditional` | [Plurality.lean#L124](formal/Logos/Plurality.lean#L124) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Person.Person`, **C40** `T12_twoPersons`, `Value.Affects`, `Value.PersonsAffectPrinciple` | — |
| C61 | `Logos.Choice.rightWrong_implies_someone_means` | [Choice.lean#L393](formal/Logos/Choice.lean#L393) | `{AxTwoSubjects, Means, Subject}` | axiom `Means` (VOCAB), axiom `Subject` (VOCAB), `Alternatives.Incompatible`, `Choice.ChoiceField`, **C54** `JUDGE_HAS_CHOICE_FIELD`, `Core.N_F`, `Core.N_T` | — |
| C62 | `Logos.Order.rightWrong_implies_meaning` | [Order.lean#L91](formal/Logos/Order.lean#L91) | `{Initiates, Means, State, Subject}` | `Agency.A`, axiom `Initiates` (VOCAB), axiom `Means` (VOCAB), axiom `State` (VOCAB), axiom `Subject` (VOCAB), `Choice.Meaning_I`, `Core.IsFalse`, `Core.T`, `Order.Correct`, `Order.Incorrect` | `Order.rightDistinctWrong_implies_meaning`, `Order.rightWrongDistinction_implies_meaning` |
| C101 | `Logos.Order.act_iff_asserts_or_incorrect` | [Order.lean#L57](formal/Logos/Order.lean#L57) | `{Initiates, Means, State, Subject, CL}` | `Agency.A`, `Agency.Act`, `Agency.Asserts`, axiom `Subject` (VOCAB), `Core.IsFalse`, `Order.Incorrect` | — |
| C97 | `Logos.Choice.deliberateChoice_implies_selects` | [Choice.lean#L492](formal/Logos/Choice.lean#L492) | `{Initiates, Means, State, Subject}` | `Agency.Asserts`, axiom `Means` (VOCAB), axiom `Subject` (VOCAB), `Alternatives.Incompatible`, `Choice.DeliberateChoice`, `Choice.Selects` | **C100** `deliberateChoice_iff_selects_and_means`, `Choice.deliberateChoice_iff_selects_and_rejects` |
| C98 | `Logos.Choice.deliberateChoice_implies_chooses` | [Choice.lean#L498](formal/Logos/Choice.lean#L498) | `{Initiates, Means, State, Subject}` | `Agency.Asserts`, axiom `Means` (VOCAB), axiom `Subject` (VOCAB), `Alternatives.Incompatible`, `Choice.Chooses`, `Choice.DeliberateChoice` | `Choice.selfAssertedDeliberateChoice_factive_implies_chooses` |
| C99 | `Logos.Choice.selection_exists_of_act` | [Choice.lean#L695](formal/Logos/Choice.lean#L695) | `{Initiates, Means, State, Subject}` | `Agency.Act`, `Agency.Asserts`, axiom `Subject` (VOCAB), `Choice.Selects`, `Choice.act_implies_asserts_bridge`, `Choice.selection_exists` | — |
| C100 | `Logos.Choice.deliberateChoice_iff_selects_and_means` | [Choice.lean#L506](formal/Logos/Choice.lean#L506) | `{Initiates, Means, State, Subject}` | `Agency.Act`, `Agency.Asserts`, axiom `Initiates` (VOCAB), axiom `Means` (VOCAB), axiom `State` (VOCAB), axiom `Subject` (VOCAB), `Alternatives.Incompatible`, `Choice.DeliberateChoice`, `Choice.Selects`, **C97** `deliberateChoice_implies_selects` | `Choice.deliberateChoice_negation_decomposition`, `Choice.deliberateChoice_negation_iff` |
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

### `Logos.A14DerivationAudit`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `NormativeActionChoice` | def | [L55](formal/Logos/A14DerivationAudit.lean#L55) | `def NormativeActionChoice {World : Type} (cnt : ConstitutiveNormativeTruth World` | {Means, Subject}  |
| `UniversalA14` | def | [L49](formal/Logos/A14DerivationAudit.lean#L49) | `def UniversalA14 (Subj : Type) (ActRel : Subj → Prop → Prop) (ChoosesRel : Subj ` | {}  |
| `UniversalActPolarity` | def | [L199](formal/Logos/A14DerivationAudit.lean#L199) | `def UniversalActPolarity (Subj : Type) (ActRel : Subj → Prop → Prop) (MeansRel :` | {}  |
| `normative_action_yields_choice` | theorem | [L68](formal/Logos/A14DerivationAudit.lean#L68) | `theorem normative_action_yields_choice {World : Type} (cnt : ConstitutiveNormati` | {Means, Subject}  |
| `normative_route_derives_free_will` | theorem | [L75](formal/Logos/A14DerivationAudit.lean#L75) | `theorem normative_route_derives_free_will {World : Type} (cnt : ConstitutiveNorm` | {Means, Subject}  |
| `polarity_entails_universal_a14` | theorem | [L205](formal/Logos/A14DerivationAudit.lean#L205) | `theorem polarity_entails_universal_a14 {Subj : Type} (ActRel : Subj → Prop → Pro` | {CL}  |

### `Logos.A14DerivationAudit.NormativeSeparationModel`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `ModelAct` | def | [L113](formal/Logos/A14DerivationAudit.lean#L113) | `def ModelAct (s : ModelSubject) (p : Prop) : Prop` | {}  |
| `ModelChooses` | def | [L116](formal/Logos/A14DerivationAudit.lean#L116) | `def ModelChooses (s : ModelSubject) (p q : Prop) : Prop` | {}  |
| `ModelInitiates` | def | [L111](formal/Logos/A14DerivationAudit.lean#L111) | `def ModelInitiates (_s : ModelSubject) (_w _w' : ModelState) (_p : Prop) : Prop` | {}  |
| `ModelMeans` | def | [L107](formal/Logos/A14DerivationAudit.lean#L107) | `def ModelMeans : ModelSubject → Prop → Prop | ModelSubject.moralAgent, _ => True` | {}  |
| `ModelState` | def | [L105](formal/Logos/A14DerivationAudit.lean#L105) | `def ModelState : Type` | {}  |
| `ModelSubject` | inductive | [L101](formal/Logos/A14DerivationAudit.lean#L101) | `inductive ModelSubject : Type` | —  |
| `ModelUniversalA14` | def | [L119](formal/Logos/A14DerivationAudit.lean#L119) | `def ModelUniversalA14 : Prop` | {}  |
| `MoralNormativeTruth` | def | [L123](formal/Logos/A14DerivationAudit.lean#L123) | `def MoralNormativeTruth : Prop` | {}  |
| `hostile_model_normativity_compatible_with_not_universal_a14` | theorem | [L160](formal/Logos/A14DerivationAudit.lean#L160) | `theorem hostile_model_normativity_compatible_with_not_universal_a14 : MoralNorma` | {}  |
| `moral_agent_acts` | theorem | [L142](formal/Logos/A14DerivationAudit.lean#L142) | `theorem moral_agent_acts : ModelAct ModelSubject.moralAgent True` | {}  |
| `moral_agent_chooses` | theorem | [L138](formal/Logos/A14DerivationAudit.lean#L138) | `theorem moral_agent_chooses : ModelChooses ModelSubject.moralAgent True False` | {}  |
| `moral_agent_satisfies_normative_truth` | theorem | [L130](formal/Logos/A14DerivationAudit.lean#L130) | `theorem moral_agent_satisfies_normative_truth : MoralNormativeTruth` | {}  |
| `normativity_does_not_entail_universal_a14` | theorem | [L170](formal/Logos/A14DerivationAudit.lean#L170) | `theorem normativity_does_not_entail_universal_a14 : ¬ (MoralNormativeTruth → Mod` | {}  |
| `unilateral_agent_acts` | theorem | [L146](formal/Logos/A14DerivationAudit.lean#L146) | `theorem unilateral_agent_acts : ModelAct ModelSubject.unilateralAgent True` | {}  |
| `unilateral_agent_cannot_choose` | theorem | [L150](formal/Logos/A14DerivationAudit.lean#L150) | `theorem unilateral_agent_cannot_choose : ¬ ∃ q : Prop, ModelChooses ModelSubject` | {}  |

### `Logos.A14SemanticAudit`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `A14_Statement` | def | [L56](formal/Logos/A14SemanticAudit.lean#L56) | `def A14_Statement (Subj : Type) (ActRel : Subj → Prop → Prop) (MeansRel : Subj →` | {}  |
| `Act_Authorial` | def | [L165](formal/Logos/A14SemanticAudit.lean#L165) | `def Act_Authorial {Subj : Type} (MeansRel : Subj → Prop → Prop) (InitiatesRel : ` | {}  |
| `Act_Contrastive` | def | [L152](formal/Logos/A14SemanticAudit.lean#L152) | `def Act_Contrastive {Subj : Type} (MeansRel : Subj → Prop → Prop) (InitiatesRel ` | {}  |
| `Act_Minimal` | def | [L146](formal/Logos/A14SemanticAudit.lean#L146) | `def Act_Minimal {Subj : Type} (MeansRel : Subj → Prop → Prop) (InitiatesRel : Su` | {}  |
| `Act_Purposeful` | def | [L158](formal/Logos/A14SemanticAudit.lean#L158) | `def Act_Purposeful {Subj : Type} (MeansRel : Subj → Prop → Prop) (InitiatesRel :` | {}  |
| `Act_Responsive` | def | [L172](formal/Logos/A14SemanticAudit.lean#L172) | `def Act_Responsive {Subj : Type} (MeansRel : Subj → Prop → Prop) (InitiatesRel :` | {}  |
| `AimStage` | def | [L295](formal/Logos/A14SemanticAudit.lean#L295) | `def AimStage {Subj : Type} (CS : FineCognitiveSubject Subj) (SourceOf : Subj → P` | {}  |
| `AuthorStage` | def | [L290](formal/Logos/A14SemanticAudit.lean#L290) | `def AuthorStage {Subj : Type} (CS : FineCognitiveSubject Subj) (SourceOf : Subj ` | {}  |
| `AuthorialAction` | def | [L92](formal/Logos/A14SemanticAudit.lean#L92) | `def AuthorialAction {Subj : Type} (ActRel : Subj → Prop → Prop) (SourceOf : Subj` | {}  |
| `CausalStage` | def | [L306](formal/Logos/A14SemanticAudit.lean#L306) | `def CausalStage {Subj : Type} (CS : FineCognitiveSubject Subj) (SourceOf : Subj ` | {}  |
| `EvalStage` | def | [L282](formal/Logos/A14SemanticAudit.lean#L282) | `def EvalStage {Subj : Type} (CS : FineCognitiveSubject Subj) (s : Subj) (p q : P` | {}  |
| `MissingHornPrinciple` | def | [L62](formal/Logos/A14SemanticAudit.lean#L62) | `def MissingHornPrinciple (Subj : Type) (ActRel : Subj → Prop → Prop) (MeansRel :` | {}  |
| `ModalStage` | def | [L319](formal/Logos/A14SemanticAudit.lean#L319) | `def ModalStage {Subj : Type} (CS : FineCognitiveSubject Subj) (SourceOf : Subj →` | {}  |
| `ReasonStage` | def | [L312](formal/Logos/A14SemanticAudit.lean#L312) | `def ReasonStage {Subj : Type} (CS : FineCognitiveSubject Subj) (SourceOf : Subj ` | {}  |
| `ReasonsResponsiveAction` | def | [L87](formal/Logos/A14SemanticAudit.lean#L87) | `def ReasonsResponsiveAction {Subj : Type} (ActRel : Subj → Prop → Prop) (Respons` | {}  |
| `ReprStage` | def | [L278](formal/Logos/A14SemanticAudit.lean#L278) | `def ReprStage {Subj : Type} (CS : FineCognitiveSubject Subj) (s : Subj) (p q : P` | {}  |
| `SelfAttrStage` | def | [L300](formal/Logos/A14SemanticAudit.lean#L300) | `def SelfAttrStage {Subj : Type} (CS : FineCognitiveSubject Subj) (SourceOf : Sub` | {}  |
| `SettleStage` | def | [L286](formal/Logos/A14SemanticAudit.lean#L286) | `def SettleStage {Subj : Type} (CS : FineCognitiveSubject Subj) (s : Subj) (p q :` | {}  |
| `SubstantivePerson` | def | [L228](formal/Logos/A14SemanticAudit.lean#L228) | `def SubstantivePerson (Subj : Type) (s : Subj) : Prop` | {}  |
| `TeleologicalAction` | def | [L82](formal/Logos/A14SemanticAudit.lean#L82) | `def TeleologicalAction {Subj : Type} (ActRel : Subj → Prop → Prop) (AimsAt : Sub` | {}  |
| `a14_iff_missing_horn_principle` | theorem | [L68](formal/Logos/A14SemanticAudit.lean#L68) | `theorem a14_iff_missing_horn_principle {Subj : Type} (ActRel : Subj → Prop → Pro` | {}  |
| `act_contrastive_trivializes_a14` | theorem | [L179](formal/Logos/A14SemanticAudit.lean#L179) | `theorem act_contrastive_trivializes_a14 {Subj : Type} (MeansRel : Subj → Prop → ` | {}  |
| `candidate_principles_fail_to_derive_a14` | theorem | [L100](formal/Logos/A14SemanticAudit.lean#L100) | `theorem candidate_principles_fail_to_derive_a14 : ∃ (Subj : Type) (ActRel : Subj` | {}  |
| `contrastive_closure_of_means_fails` | theorem | [L213](formal/Logos/A14SemanticAudit.lean#L213) | `theorem contrastive_closure_of_means_fails : ∃ (Subj : Type) (MeansRel : Subj → ` | {}  |
| `inferential_closure_of_means_fails` | theorem | [L201](formal/Logos/A14SemanticAudit.lean#L201) | `theorem inferential_closure_of_means_fails : ∃ (Subj : Type) (MeansRel : Subj → ` | {}  |
| `irreducible_semantic_boundary_of_a14` | theorem | [L131](formal/Logos/A14SemanticAudit.lean#L131) | `theorem irreducible_semantic_boundary_of_a14 {Subj : Type} (ActRel : Subj → Prop` | {CL}  |
| `negation_closure_of_means_fails` | theorem | [L190](formal/Logos/A14SemanticAudit.lean#L190) | `theorem negation_closure_of_means_fails : ∃ (Subj : Type) (MeansRel : Subj → Pro` | {}  |
| `performative_boundary_theorem` | theorem | [L236](formal/Logos/A14SemanticAudit.lean#L236) | `theorem performative_boundary_theorem : ∃ (Subj : Type) (CS : FineCognitiveSubje` | {}  |
| `separation_aim_without_self_attr` | theorem | [L416](formal/Logos/A14SemanticAudit.lean#L416) | `theorem separation_aim_without_self_attr : ∃ (Subj : Type) (CS : FineCognitiveSu` | {}  |
| `separation_author_without_aim` | theorem | [L385](formal/Logos/A14SemanticAudit.lean#L385) | `theorem separation_author_without_aim : ∃ (Subj : Type) (CS : FineCognitiveSubje` | {}  |
| `separation_causal_without_reason` | theorem | [L489](formal/Logos/A14SemanticAudit.lean#L489) | `theorem separation_causal_without_reason : ∃ (Subj : Type) (CS : FineCognitiveSu` | {}  |
| `separation_reason_without_modal` | theorem | [L532](formal/Logos/A14SemanticAudit.lean#L532) | `theorem separation_reason_without_modal : ∃ (Subj : Type) (CS : FineCognitiveSub` | {}  |
| `separation_repr_without_eval` | theorem | [L328](formal/Logos/A14SemanticAudit.lean#L328) | `theorem separation_repr_without_eval : ∃ (Subj : Type) (CS : FineCognitiveSubjec` | {}  |
| `separation_self_attr_without_causal` | theorem | [L452](formal/Logos/A14SemanticAudit.lean#L452) | `theorem separation_self_attr_without_causal : ∃ (Subj : Type) (CS : FineCognitiv` | {}  |
| `separation_settle_without_authorship` | theorem | [L354](formal/Logos/A14SemanticAudit.lean#L354) | `theorem separation_settle_without_authorship : ∃ (Subj : Type) (CS : FineCogniti` | {}  |

### `Logos.ActionChoiceDefinitions`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Action` | def | [L88](formal/Logos/ActionChoiceDefinitions.lean#L88) | `def Action (s : Subject) (p : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `AgentCausalSourcehood` | structure | [L282](formal/Logos/ActionChoiceDefinitions.lean#L282) | `structure AgentCausalSourcehood (Subject : Type) where` | —  |
| `AgentialExecution` | structure | [L100](formal/Logos/ActionChoiceDefinitions.lean#L100) | `structure AgentialExecution (Subject : Type) where` | —  |
| `AssertionWithoutChoiceModel` | structure | [L367](formal/Logos/ActionChoiceDefinitions.lean#L367) | `structure AssertionWithoutChoiceModel where` | —  |
| `CategoricalAlternativePossibility` | structure | [L266](formal/Logos/ActionChoiceDefinitions.lean#L266) | `structure CategoricalAlternativePossibility (Subject : Type) (State : Type) wher` | —  |
| `ChoiceWithoutAssertionModel` | structure | [L385](formal/Logos/ActionChoiceDefinitions.lean#L385) | `structure ChoiceWithoutAssertionModel where` | —  |
| `CompulsionDistinction` | structure | [L607](formal/Logos/ActionChoiceDefinitions.lean#L607) | `structure CompulsionDistinction where` | —  |
| `ContrastiveChoice` | def | [L154](formal/Logos/ActionChoiceDefinitions.lean#L154) | `def ContrastiveChoice (s : Subject) (p q : Prop) : Prop` | {Means, Subject}  |
| `Decision` | structure | [L196](formal/Logos/ActionChoiceDefinitions.lean#L196) | `structure Decision (Subject : Type) (ctx : DecisionContext Subject) (s : Subject` | —  |
| `DecisionContext` | structure | [L186](formal/Logos/ActionChoiceDefinitions.lean#L186) | `structure DecisionContext (Subject : Type) where` | —  |
| `DeliberativeContext` | structure | [L162](formal/Logos/ActionChoiceDefinitions.lean#L162) | `structure DeliberativeContext (Subject : Type) where` | —  |
| `DeliberatorWithoutLeeway` | structure | [L441](formal/Logos/ActionChoiceDefinitions.lean#L441) | `structure DeliberatorWithoutLeeway where` | —  |
| `Determinism_D1` | def | [L222](formal/Logos/ActionChoiceDefinitions.lean#L222) | `def Determinism_D1 {State : Type} (step : State → State) : Prop` | {}  |
| `Determinism_D2` | def | [L226](formal/Logos/ActionChoiceDefinitions.lean#L226) | `def Determinism_D2 {State : Type} (History : State → Nat → Prop) (NextEvent : St` | {}  |
| `Determinism_D3` | def | [L230](formal/Logos/ActionChoiceDefinitions.lean#L230) | `def Determinism_D3 {State : Type} (Laws : Prop) (StateAt : State → Nat → Prop) :` | {}  |
| `Determinism_D4` | def | [L234](formal/Logos/ActionChoiceDefinitions.lean#L234) | `def Determinism_D4 (MentalState : Subject → Nat → Prop) (NextMentalState : Subje` | {Subject}  |
| `Determinism_D5` | def | [L238](formal/Logos/ActionChoiceDefinitions.lean#L238) | `def Determinism_D5 (Subject : Type) (Antecedents : Subject → Prop → Prop) (Settl` | {}  |
| `DeterministicSelector` | structure | [L423](formal/Logos/ActionChoiceDefinitions.lean#L423) | `structure DeterministicSelector where` | —  |
| `ExtensionalChoice` | def | [L146](formal/Logos/ActionChoiceDefinitions.lean#L146) | `def ExtensionalChoice (s : Subject) (p q : Prop) : Prop` | {Means, Subject}  |
| `GenuineChoice` | structure | [L173](formal/Logos/ActionChoiceDefinitions.lean#L173) | `structure GenuineChoice (Subject : Type) (ctx : DeliberativeContext Subject)` | —  |
| `GenuineIntentionalAction` | structure | [L109](formal/Logos/ActionChoiceDefinitions.lean#L109) | `structure GenuineIntentionalAction (Subject : Type) (State : Type) (E : Agential` | —  |
| `InevitableDecisionModel` | structure | [L464](formal/Logos/ActionChoiceDefinitions.lean#L464) | `structure InevitableDecisionModel where` | —  |
| `Layer1_LogicalAlternative` | def | [L259](formal/Logos/ActionChoiceDefinitions.lean#L259) | `def Layer1_LogicalAlternative (p q : Prop) : Prop` | {}  |
| `Layer2_RepresentedAlternative` | def | [L262](formal/Logos/ActionChoiceDefinitions.lean#L262) | `def Layer2_RepresentedAlternative (s : Subject) (p q : Prop) : Prop` | {Means, Subject}  |
| `LibertarianFreedom` | structure | [L297](formal/Logos/ActionChoiceDefinitions.lean#L297) | `structure LibertarianFreedom (Subject : Type) (State : Type) (ctx : Deliberative` | —  |
| `M_S5_selector` | def | [L428](formal/Logos/ActionChoiceDefinitions.lean#L428) | `def M_S5_selector : DeterministicSelector where step` | {}  |
| `Selection` | def | [L134](formal/Logos/ActionChoiceDefinitions.lean#L134) | `def Selection {Item : Type} (ctx : SelectionContext Item) (x : Item) : Prop` | {}  |
| `SelectionContext` | structure | [L122](formal/Logos/ActionChoiceDefinitions.lean#L122) | `structure SelectionContext (Item : Type) where` | —  |
| `SelectionWithoutMeaningModel` | structure | [L324](formal/Logos/ActionChoiceDefinitions.lean#L324) | `structure SelectionWithoutMeaningModel where` | —  |
| `SinglePathActionModel` | structure | [L401](formal/Logos/ActionChoiceDefinitions.lean#L401) | `structure SinglePathActionModel where` | —  |
| `Volition` | def | [L214](formal/Logos/ActionChoiceDefinitions.lean#L214) | `def Volition {Subject : Type} (ctx : VolitionalContext Subject) (s : Subject) (p` | {}  |
| `VolitionWithoutActionModel` | structure | [L480](formal/Logos/ActionChoiceDefinitions.lean#L480) | `structure VolitionWithoutActionModel where` | —  |
| `VolitionalContext` | structure | [L206](formal/Logos/ActionChoiceDefinitions.lean#L206) | `structure VolitionalContext (Subject : Type) where` | —  |
| `WeakAct` | def | [L76](formal/Logos/ActionChoiceDefinitions.lean#L76) | `def WeakAct {Subject : Type} (ctx : WeakActContext Subject) (s : Subject) (p : P` | {}  |
| `WeakActContext` | structure | [L68](formal/Logos/ActionChoiceDefinitions.lean#L68) | `structure WeakActContext (Subject : Type) where` | —  |
| `action_eq_act` | theorem | [L92](formal/Logos/ActionChoiceDefinitions.lean#L92) | `theorem action_eq_act (s : Subject) (p : Prop) : Action s p ↔ Act s p` | {Initiates, Means, State, Subject}  |
| `alternative_possibility_conflicts_with_choice_determinism` | theorem | [L556](formal/Logos/ActionChoiceDefinitions.lean#L556) | `theorem alternative_possibility_conflicts_with_choice_determinism : ∀ (Subject :` | {}  |
| `anti_cheating_action_without_alternatives` | theorem | [L587](formal/Logos/ActionChoiceDefinitions.lean#L587) | `theorem anti_cheating_action_without_alternatives : ∃ (Subject : Type) (State : ` | {}  |
| `anti_cheating_determinism_not_compulsion` | theorem | [L612](formal/Logos/ActionChoiceDefinitions.lean#L612) | `theorem anti_cheating_determinism_not_compulsion : ∃ (C : CompulsionDistinction)` | {}  |
| `genuine_choice_entails_asymmetric_settlement` | theorem | [L525](formal/Logos/ActionChoiceDefinitions.lean#L525) | `theorem genuine_choice_entails_asymmetric_settlement {Subject : Type} {ctx : Del` | {}  |
| `genuine_choice_entails_incompatible` | theorem | [L516](formal/Logos/ActionChoiceDefinitions.lean#L516) | `theorem genuine_choice_entails_incompatible {Subject : Type} {ctx : Deliberative` | {}  |
| `genuine_intentional_action_implies_action` | theorem | [L506](formal/Logos/ActionChoiceDefinitions.lean#L506) | `theorem genuine_intentional_action_implies_action {Subject : Type} {State : Type` | {}  |
| `libertarian_freedom_entails_alternative_possibility` | theorem | [L534](formal/Logos/ActionChoiceDefinitions.lean#L534) | `theorem libertarian_freedom_entails_alternative_possibility {Subject : Type} {St` | {}  |
| `libertarian_freedom_entails_sourcehood` | theorem | [L544](formal/Logos/ActionChoiceDefinitions.lean#L544) | `theorem libertarian_freedom_entails_sourcehood {Subject : Type} {State : Type} {` | {}  |
| `model_S1_selection_without_meaning` | theorem | [L330](formal/Logos/ActionChoiceDefinitions.lean#L330) | `theorem model_S1_selection_without_meaning : ∃ (M : SelectionWithoutMeaningModel` | {}  |
| `model_S2_assertion_without_choice` | theorem | [L371](formal/Logos/ActionChoiceDefinitions.lean#L371) | `theorem model_S2_assertion_without_choice : ∃ (M : AssertionWithoutChoiceModel),` | {}  |
| `model_S3_choice_without_assertion` | theorem | [L389](formal/Logos/ActionChoiceDefinitions.lean#L389) | `theorem model_S3_choice_without_assertion : ∃ (M : ChoiceWithoutAssertionModel),` | {}  |
| `model_S4_action_without_choice` | theorem | [L406](formal/Logos/ActionChoiceDefinitions.lean#L406) | `theorem model_S4_action_without_choice : ∃ (M : SinglePathActionModel), (M.Means` | {}  |
| `model_S5_deterministic_selection_verified` | theorem | [L433](formal/Logos/ActionChoiceDefinitions.lean#L433) | `theorem model_S5_deterministic_selection_verified : M_S5_selector.hDet 0 0 rfl =` | {}  |
| `model_S6_co_representation_without_leeway` | theorem | [L448](formal/Logos/ActionChoiceDefinitions.lean#L448) | `theorem model_S6_co_representation_without_leeway : ∃ (M : DeliberatorWithoutLee` | {}  |
| `model_S7_decision_without_alternative` | theorem | [L468](formal/Logos/ActionChoiceDefinitions.lean#L468) | `theorem model_S7_decision_without_alternative : ∃ (M : InevitableDecisionModel),` | {}  |
| `model_S8_volition_without_action` | theorem | [L484](formal/Logos/ActionChoiceDefinitions.lean#L484) | `theorem model_S8_volition_without_action : ∃ (M : VolitionWithoutActionModel), M` | {}  |
| `selection_not_implies_meaning` | theorem | [L353](formal/Logos/ActionChoiceDefinitions.lean#L353) | `theorem selection_not_implies_meaning : ∃ (Item : Type) (ctx : SelectionContext ` | {}  |

### `Logos.AdversarialReductioAudit`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `ExactUptakeGap` | def | [L271](formal/Logos/AdversarialReductioAudit.lean#L271) | `def ExactUptakeGap (Subject : Type) (CS : CognitiveSubject Subject) (MeansAt : S` | {}  |
| `ExtendedTrace` | structure | [L110](formal/Logos/AdversarialReductioAudit.lean#L110) | `structure ExtendedTrace (Subject : Type) where` | —  |
| `RetorsionProgression` | structure | [L120](formal/Logos/AdversarialReductioAudit.lean#L120) | `structure RetorsionProgression (Subject : Type) (s : Subject) (P : Prop) where` | —  |
| `VolitionalAim` | def | [L80](formal/Logos/AdversarialReductioAudit.lean#L80) | `def VolitionalAim (Subject State : Type) (s : Subject) (p : Prop) (InitiatesAt :` | {}  |
| `affirmation_to_act_derives_one_horn_only` | theorem | [L132](formal/Logos/AdversarialReductioAudit.lean#L132) | `theorem affirmation_to_act_derives_one_horn_only : ∃ (Subject : Type) (s : Subje` | {}  |
| `model_M10_mechanical_execution_no_act` | theorem | [L224](formal/Logos/AdversarialReductioAudit.lean#L224) | `theorem model_M10_mechanical_execution_no_act : ∃ (Subject : Type) (s : Subject)` | {}  |
| `model_M11_considered_not_act` | theorem | [L233](formal/Logos/AdversarialReductioAudit.lean#L233) | `theorem model_M11_considered_not_act : ∃ (Subject : Type) (CS : CognitiveSubject` | {}  |
| `model_M12_contrast_without_chooses` | theorem | [L248](formal/Logos/AdversarialReductioAudit.lean#L248) | `theorem model_M12_contrast_without_chooses : ∃ (Subject : Type) (CS : CognitiveS` | {}  |
| `model_M7_external_conclusion` | theorem | [L166](formal/Logos/AdversarialReductioAudit.lean#L166) | `theorem model_M7_external_conclusion : ∃ (Subject : Type) (CS : CognitiveSubject` | {}  |
| `model_M8_consideration_without_meaning` | theorem | [L184](formal/Logos/AdversarialReductioAudit.lean#L184) | `theorem model_M8_consideration_without_meaning : ∃ (Subject : Type) (CS : Cognit` | {}  |
| `model_M9_affirmation_without_meaning` | theorem | [L201](formal/Logos/AdversarialReductioAudit.lean#L201) | `theorem model_M9_affirmation_without_meaning : ∃ (Subject : Type) (CS : Cognitiv` | {}  |
| `rational_subject_cannot_volitionally_aim_at_rejected_horn` | theorem | [L84](formal/Logos/AdversarialReductioAudit.lean#L84) | `theorem rational_subject_cannot_volitionally_aim_at_rejected_horn : ∃ (Subject S` | {}  |
| `state_A_is_refuted` | theorem | [L276](formal/Logos/AdversarialReductioAudit.lean#L276) | `theorem state_A_is_refuted : ∃ (Subject : Type) (CS : CognitiveSubject Subject) ` | {}  |
| `state_D_is_refuted` | theorem | [L286](formal/Logos/AdversarialReductioAudit.lean#L286) | `theorem state_D_is_refuted : ∃ (Subject : Type) (CS : CognitiveSubject Subject) ` | {}  |
| `uptake_is_renamed_co_meaning_premise` | theorem | [L53](formal/Logos/AdversarialReductioAudit.lean#L53) | `theorem uptake_is_renamed_co_meaning_premise (Subject : Type) (CS : CognitiveSub` | {}  |

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

### `Logos.AgencyDeterminismConsequences`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `AgencyPartialOrder` | structure | [L70](formal/Logos/AgencyDeterminismConsequences.lean#L70) | `structure AgencyPartialOrder (Subject : Type) where` | —  |
| `DeterministicDeliberator` | structure | [L137](formal/Logos/AgencyDeterminismConsequences.lean#L137) | `structure DeterministicDeliberator where` | —  |
| `ErrorCapableReasoner` | structure | [L261](formal/Logos/AgencyDeterminismConsequences.lean#L261) | `structure ErrorCapableReasoner where` | —  |
| `ExplanatoryNexus` | structure | [L334](formal/Logos/AgencyDeterminismConsequences.lean#L334) | `structure ExplanatoryNexus where` | —  |
| `FirstPersonState` | structure | [L230](formal/Logos/AgencyDeterminismConsequences.lean#L230) | `structure FirstPersonState where` | —  |
| `M_D1_state_machine` | def | [L217](formal/Logos/AgencyDeterminismConsequences.lean#L217) | `def M_D1_state_machine (n : Nat) : Nat` | {}  |
| `M_D5_error_system` | def | [L268](formal/Logos/AgencyDeterminismConsequences.lean#L268) | `def M_D5_error_system : ErrorCapableReasoner where Believes` | {}  |
| `M_D6_reasons_system` | def | [L294](formal/Logos/AgencyDeterminismConsequences.lean#L294) | `def M_D6_reasons_system : ReasonsResponsiveReasoner where ReasonFor` | {}  |
| `M_Deliberator` | def | [L152](formal/Logos/AgencyDeterminismConsequences.lean#L152) | `def M_Deliberator : DeterministicDeliberator where State` | {}  |
| `ReasonsResponsiveReasoner` | structure | [L288](formal/Logos/AgencyDeterminismConsequences.lean#L288) | `structure ReasonsResponsiveReasoner where` | —  |
| `SelfRefState` | structure | [L243](formal/Logos/AgencyDeterminismConsequences.lean#L243) | `structure SelfRefState where` | —  |
| `Tier1_IntentionalDirectedness` | def | [L85](formal/Logos/AgencyDeterminismConsequences.lean#L85) | `def Tier1_IntentionalDirectedness (Subject : Type) (A : AgencyPartialOrder Subje` | {}  |
| `Tier2_CognitiveAlternativity` | def | [L89](formal/Logos/AgencyDeterminismConsequences.lean#L89) | `def Tier2_CognitiveAlternativity (Subject : Type) (A : AgencyPartialOrder Subjec` | {}  |
| `Tier3_RationalSettlement` | def | [L93](formal/Logos/AgencyDeterminismConsequences.lean#L93) | `def Tier3_RationalSettlement (Subject : Type) (A : AgencyPartialOrder Subject) :` | {}  |
| `Tier4_ContrastiveChoice` | def | [L97](formal/Logos/AgencyDeterminismConsequences.lean#L97) | `def Tier4_ContrastiveChoice (Subject : Type) (A : AgencyPartialOrder Subject) : ` | {}  |
| `Tier5_ExecutiveChoice` | def | [L101](formal/Logos/AgencyDeterminismConsequences.lean#L101) | `def Tier5_ExecutiveChoice (Subject : Type) (A : AgencyPartialOrder Subject) : Pr` | {}  |
| `Tier6_GammaFreeWill` | def | [L105](formal/Logos/AgencyDeterminismConsequences.lean#L105) | `def Tier6_GammaFreeWill (Subject : Type) (A : AgencyPartialOrder Subject) : Prop` | {}  |
| `Tier7_AlternativePossibility` | def | [L109](formal/Logos/AgencyDeterminismConsequences.lean#L109) | `def Tier7_AlternativePossibility (Subject : Type) (A : AgencyPartialOrder Subjec` | {}  |
| `Tier8_AgentCausalSourcehood` | def | [L113](formal/Logos/AgencyDeterminismConsequences.lean#L113) | `def Tier8_AgentCausalSourcehood (Subject : Type) (A : AgencyPartialOrder Subject` | {}  |
| `Tier9_LibertarianFreedom` | def | [L117](formal/Logos/AgencyDeterminismConsequences.lean#L117) | `def Tier9_LibertarianFreedom (Subject : Type) (A : AgencyPartialOrder Subject) :` | {}  |
| `UnaryRepresentation` | structure | [L374](formal/Logos/AgencyDeterminismConsequences.lean#L374) | `structure UnaryRepresentation (Subject : Type) where` | —  |
| `consequence_A_reasoning_not_entails_libertarian` | theorem | [L405](formal/Logos/AgencyDeterminismConsequences.lean#L405) | `theorem consequence_A_reasoning_not_entails_libertarian : ∃ (Subject : Type) (A ` | {}  |
| `consequence_B_first_person_not_entails_libertarian` | theorem | [L430](formal/Logos/AgencyDeterminismConsequences.lean#L430) | `theorem consequence_B_first_person_not_entails_libertarian : ∃ (s : FirstPersonS` | {}  |
| `consequence_C_intentionality_not_entails_libertarian` | theorem | [L438](formal/Logos/AgencyDeterminismConsequences.lean#L438) | `theorem consequence_C_intentionality_not_entails_libertarian : ∃ (step : Nat → N` | {}  |
| `consequence_D_normativity_not_entails_libertarian` | theorem | [L446](formal/Logos/AgencyDeterminismConsequences.lean#L446) | `theorem consequence_D_normativity_not_entails_libertarian : let M` | {}  |
| `consequence_E_gamma_freewill_compatible_with_determinism` | theorem | [L454](formal/Logos/AgencyDeterminismConsequences.lean#L454) | `theorem consequence_E_gamma_freewill_compatible_with_determinism : let M` | {}  |
| `consequence_F_libertarian_requires_new_primitive` | theorem | [L466](formal/Logos/AgencyDeterminismConsequences.lean#L466) | `theorem consequence_F_libertarian_requires_new_primitive : -- Any theory entaili` | {}  |
| `determinism_compatible_with_gamma_freewill` | theorem | [L167](formal/Logos/AgencyDeterminismConsequences.lean#L167) | `theorem determinism_compatible_with_gamma_freewill : let M` | {}  |
| `deterministic_rational_realization` | theorem | [L343](formal/Logos/AgencyDeterminismConsequences.lean#L343) | `theorem deterministic_rational_realization : ∃ (N : ExplanatoryNexus) (s0 s1 : N` | {}  |
| `gamma_freewill_distinct_from_libertarian_freedom` | theorem | [L178](formal/Logos/AgencyDeterminismConsequences.lean#L178) | `theorem gamma_freewill_distinct_from_libertarian_freedom : ∃ (Subject : Type) (A` | {}  |
| `master_agency_determinism_synthesis` | theorem | [L490](formal/Logos/AgencyDeterminismConsequences.lean#L490) | `theorem master_agency_determinism_synthesis : -- 1. Rational settlement is force` | {}  |
| `step_M_D3` | def | [L235](formal/Logos/AgencyDeterminismConsequences.lean#L235) | `def step_M_D3 (s : FirstPersonState) : FirstPersonState` | {}  |
| `step_M_D4` | def | [L247](formal/Logos/AgencyDeterminismConsequences.lean#L247) | `def step_M_D4 (s : SelfRefState) : SelfRefState` | {}  |
| `test_M_D1_deterministic` | theorem | [L219](formal/Logos/AgencyDeterminismConsequences.lean#L219) | `theorem test_M_D1_deterministic : ∀ n1 n2 : Nat, n1 = n2 → M_D1_state_machine n1` | {}  |
| `test_M_D2_intentionality_compatible_with_determinism` | theorem | [L223](formal/Logos/AgencyDeterminismConsequences.lean#L223) | `theorem test_M_D2_intentionality_compatible_with_determinism : ∃ (step : Nat → N` | {}  |
| `test_M_D3_first_person_survives` | theorem | [L238](formal/Logos/AgencyDeterminismConsequences.lean#L238) | `theorem test_M_D3_first_person_survives : ∀ s1 s2 : FirstPersonState, s1 = s2 → ` | {}  |
| `test_M_D4_self_reference_survives` | theorem | [L250](formal/Logos/AgencyDeterminismConsequences.lean#L250) | `theorem test_M_D4_self_reference_survives : ∀ s1 s2 : SelfRefState, s1 = s2 → st` | {}  |
| `test_M_D5_error_and_correction_deterministic` | theorem | [L275](formal/Logos/AgencyDeterminismConsequences.lean#L275) | `theorem test_M_D5_error_and_correction_deterministic : let M` | {}  |
| `test_M_D6_rational_because_survives_determinism` | theorem | [L300](formal/Logos/AgencyDeterminismConsequences.lean#L300) | `theorem test_M_D6_rational_because_survives_determinism : let M` | {}  |
| `test_M_D7_deliberation_survives_determinism` | theorem | [L308](formal/Logos/AgencyDeterminismConsequences.lean#L308) | `theorem test_M_D7_deliberation_survives_determinism : ∃ (MeansAt : Unit → Prop →` | {}  |
| `test_M_D8_act_execution_deterministic` | theorem | [L315](formal/Logos/AgencyDeterminismConsequences.lean#L315) | `theorem test_M_D8_act_execution_deterministic : ∃ (MeansAt : Unit → Prop → Prop)` | {}  |
| `unary_representation_fails_missing_horn` | theorem | [L381](formal/Logos/AgencyDeterminismConsequences.lean#L381) | `theorem unary_representation_fails_missing_horn : ∃ (Subject : Type) (UR : Unary` | {}  |

### `Logos.AgencyFrontierAudit`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Agency_Star` | def | [L326](formal/Logos/AgencyFrontierAudit.lean#L326) | `def Agency_Star (Subj : Type) (CS : FineCognitiveSubject Subj) : Prop` | {}  |
| `AgentCausalSettlement_Star` | def | [L343](formal/Logos/AgencyFrontierAudit.lean#L343) | `def AgentCausalSettlement_Star (Subj : Type) (CS : FineCognitiveSubject Subj) (A` | {}  |
| `AgentDeterminesHorn` | def | [L108](formal/Logos/AgencyFrontierAudit.lean#L108) | `def AgentDeterminesHorn {Subj : Type} (AgentDet : Subj → Prop → Prop) (s : Subj)` | {}  |
| `AgentSource` | def | [L97](formal/Logos/AgencyFrontierAudit.lean#L97) | `def AgentSource {Subj : Type} (SourceOf : Subj → Prop → Prop) (s : Subj) (p : Pr` | {}  |
| `Choice_Star` | def | [L334](formal/Logos/AgencyFrontierAudit.lean#L334) | `def Choice_Star (Subj : Type) (CS : FineCognitiveSubject Subj) (AgentDet : Subj ` | {}  |
| `CouldHaveSettledOtherwise` | def | [L102](formal/Logos/AgencyFrontierAudit.lean#L102) | `def CouldHaveSettledOtherwise {Subj : Type} (CanSettle : Subj → Prop → Prop) (s ` | {}  |
| `DiscretionaryChoice` | structure | [L191](formal/Logos/AgencyFrontierAudit.lean#L191) | `structure DiscretionaryChoice {Subj : Type} (CS : FineCognitiveSubject Subj)` | —  |
| `EpistemicClassification` | inductive | [L50](formal/Logos/AgencyFrontierAudit.lean#L50) | `inductive EpistemicClassification where` | —  |
| `ModalFreedom_Star` | def | [L339](formal/Logos/AgencyFrontierAudit.lean#L339) | `def ModalFreedom_Star (M : ExtendedGammaModel) : Prop` | {}  |
| `SettlesForHorn` | def | [L92](formal/Logos/AgencyFrontierAudit.lean#L92) | `def SettlesForHorn {Subj : Type} (CS : FineCognitiveSubject Subj) (s : Subj) (p ` | {}  |
| `Volition_Star` | def | [L330](formal/Logos/AgencyFrontierAudit.lean#L330) | `def Volition_Star (Subj : Type) (CS : FineCognitiveSubject Subj) : Prop` | {}  |
| `agency_star_is_model_theoretically_independent` | theorem | [L350](formal/Logos/AgencyFrontierAudit.lean#L350) | `theorem agency_star_is_model_theoretically_independent : (∃ (Subj : Type) (CS : ` | {}  |
| `agency_without_modal_alternatives` | theorem | [L313](formal/Logos/AgencyFrontierAudit.lean#L313) | `theorem agency_without_modal_alternatives : ∃ (Subj : Type) (ActRel : Subj → Pro` | {}  |
| `agentCausalSettlement_star_is_model_theoretically_independent` | theorem | [L494](formal/Logos/AgencyFrontierAudit.lean#L494) | `theorem agentCausalSettlement_star_is_model_theoretically_independent : (∃ (Subj` | {}  |
| `choice_star_is_model_theoretically_independent` | theorem | [L419](formal/Logos/AgencyFrontierAudit.lean#L419) | `theorem choice_star_is_model_theoretically_independent : (∃ (Subj : Type) (CS : ` | {}  |
| `freeWill_settlement_is_nomenclatural` | theorem | [L70](formal/Logos/AgencyFrontierAudit.lean#L70) | `theorem freeWill_settlement_is_nomenclatural {Subj : Type} (CS : FineCognitiveSu` | {}  |
| `indeterminism_does_not_imply_choice` | theorem | [L298](formal/Logos/AgencyFrontierAudit.lean#L298) | `theorem indeterminism_does_not_imply_choice : ∃ (Event : Prop) (Undetermined : P` | {}  |
| `modalFreedom_star_is_model_theoretically_independent` | theorem | [L451](formal/Logos/AgencyFrontierAudit.lean#L451) | `theorem modalFreedom_star_is_model_theoretically_independent : (∃ (M : ExtendedG` | {}  |
| `modal_alternatives_without_agency` | theorem | [L304](formal/Logos/AgencyFrontierAudit.lean#L304) | `theorem modal_alternatives_without_agency : ∃ (Entity : Type) (CanOccur : Entity` | {}  |
| `model_M27_pure_cognitive_resolver` | theorem | [L118](formal/Logos/AgencyFrontierAudit.lean#L118) | `theorem model_M27_pure_cognitive_resolver : ∃ (Subj : Type) (CS : FineCognitiveS` | {}  |
| `model_M28_deterministic_evaluator` | theorem | [L147](formal/Logos/AgencyFrontierAudit.lean#L147) | `theorem model_M28_deterministic_evaluator : ∃ (StateSpace : Type) (Step : StateS` | {}  |
| `model_M29_passive_truth_tracker` | theorem | [L156](formal/Logos/AgencyFrontierAudit.lean#L156) | `theorem model_M29_passive_truth_tracker : ∃ (Tracker : Prop → Prop), (∀ p, p → T` | {CL}  |
| `model_M30_automatic_preference_mechanism` | theorem | [L170](formal/Logos/AgencyFrontierAudit.lean#L170) | `theorem model_M30_automatic_preference_mechanism : ∃ (Valuation : Prop → Nat) (S` | {CL}  |
| `model_M31_indifferent_tie_breaker` | theorem | [L181](formal/Logos/AgencyFrontierAudit.lean#L181) | `theorem model_M31_indifferent_tie_breaker : ∃ (TieBreaker : Prop → Prop → Prop),` | {}  |
| `model_M32_genuine_choice_candidate` | theorem | [L202](formal/Logos/AgencyFrontierAudit.lean#L202) | `theorem model_M32_genuine_choice_candidate : ∃ (Subj : Type) (CS : FineCognitive` | {}  |
| `old_chooses_compatible_with_determinism` | theorem | [L260](formal/Logos/AgencyFrontierAudit.lean#L260) | `theorem old_chooses_compatible_with_determinism : ∃ (Subj : Type) (MeansRel : Su` | {}  |
| `settlementChoice_compatible_with_determinism` | theorem | [L269](formal/Logos/AgencyFrontierAudit.lean#L269) | `theorem settlementChoice_compatible_with_determinism : ∃ (Subj : Type) (CS : Fin` | {}  |
| `settlementChoice_does_not_derive_volition` | theorem | [L77](formal/Logos/AgencyFrontierAudit.lean#L77) | `theorem settlementChoice_does_not_derive_volition : ∃ (Subj : Type) (CS : FineCo` | {}  |
| `settlementChoice_is_purely_cognitive` | theorem | [L62](formal/Logos/AgencyFrontierAudit.lean#L62) | `theorem settlementChoice_is_purely_cognitive {Subj : Type} (CS : FineCognitiveSu` | {}  |
| `structural_choice_differentiator` | theorem | [L247](formal/Logos/AgencyFrontierAudit.lean#L247) | `theorem structural_choice_differentiator {Subj : Type} (CS : FineCognitiveSubjec` | {}  |
| `volition_star_is_model_theoretically_independent` | theorem | [L392](formal/Logos/AgencyFrontierAudit.lean#L392) | `theorem volition_star_is_model_theoretically_independent : (∃ (Subj : Type) (CS ` | {}  |

### `Logos.Alternatives`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Incompatible` | def | [L17](formal/Logos/Alternatives.lean#L17) | `def Incompatible (p q : Prop) : Prop` | {}  |
| `T9_incompatibleAlternatives` | theorem | [L24](formal/Logos/Alternatives.lean#L24) | `theorem T9_incompatibleAlternatives : ∃ p q : Prop, Incompatible p q ∧ T p ∧ IsF` | {} → C26 |
| `incompatible_with_negation` | theorem | [L35](formal/Logos/Alternatives.lean#L35) | `theorem incompatible_with_negation {p : Prop} (hp : T p) : Incompatible p (¬ p) ` | {} → C27 |

### `Logos.AxiomNegationAudit`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `AxActPolarity_Statement` | def | [L142](formal/Logos/AxiomNegationAudit.lean#L142) | `def AxActPolarity_Statement (C : CoreAgencySignature) : Prop` | {}  |
| `AxGlobalGround_Statement` | def | [L174](formal/Logos/AxiomNegationAudit.lean#L174) | `def AxGlobalGround_Statement (M : CoreModalGroundingSignature) : Prop` | {}  |
| `AxIntentionalChoice_Statement` | def | [L107](formal/Logos/AxiomNegationAudit.lean#L107) | `def AxIntentionalChoice_Statement (C : CoreAgencySignature) : Prop` | {}  |
| `AxPersonalGround_Statement` | def | [L395](formal/Logos/AxiomNegationAudit.lean#L395) | `def AxPersonalGround_Statement (G : CorePersonalGroundSignature) : Prop` | {}  |
| `AxTwoSubjects_Statement` | def | [L355](formal/Logos/AxiomNegationAudit.lean#L355) | `def AxTwoSubjects_Statement (V : CoreValueSignature) : Prop` | {}  |
| `ContingentContentExists` | def | [L92](formal/Logos/AxiomNegationAudit.lean#L92) | `def ContingentContentExists (M : CoreModalGroundingSignature) : Prop` | {}  |
| `CoreAgencySignature` | structure | [L66](formal/Logos/AxiomNegationAudit.lean#L66) | `structure CoreAgencySignature where` | —  |
| `CoreDatumHolds` | def | [L75](formal/Logos/AxiomNegationAudit.lean#L75) | `def CoreDatumHolds (C : CoreAgencySignature) : Prop` | {}  |
| `CoreModalGroundingSignature` | structure | [L80](formal/Logos/AxiomNegationAudit.lean#L80) | `structure CoreModalGroundingSignature where` | —  |
| `CorePersonalGroundSignature` | structure | [L385](formal/Logos/AxiomNegationAudit.lean#L385) | `structure CorePersonalGroundSignature where` | —  |
| `CorePropositionalGroundSignature` | structure | [L249](formal/Logos/AxiomNegationAudit.lean#L249) | `structure CorePropositionalGroundSignature where` | —  |
| `CoreTranscendentalReflectionSignature` | structure | [L317](formal/Logos/AxiomNegationAudit.lean#L317) | `structure CoreTranscendentalReflectionSignature where` | —  |
| `CoreUniversalObjectivitySignature` | structure | [L285](formal/Logos/AxiomNegationAudit.lean#L285) | `structure CoreUniversalObjectivitySignature where` | —  |
| `CoreValueSignature` | structure | [L97](formal/Logos/AxiomNegationAudit.lean#L97) | `structure CoreValueSignature where` | —  |
| `FeatureIsGrounded` | def | [L391](formal/Logos/AxiomNegationAudit.lean#L391) | `def FeatureIsGrounded (G : CorePersonalGroundSignature) : Prop` | {}  |
| `GroundPrincipleProp_Statement` | def | [L257](formal/Logos/AxiomNegationAudit.lean#L257) | `def GroundPrincipleProp_Statement (G : CorePropositionalGroundSignature) : Prop` | {}  |
| `NecessaryTruthExists` | def | [L89](formal/Logos/AxiomNegationAudit.lean#L89) | `def NecessaryTruthExists (M : CoreModalGroundingSignature) : Prop` | {}  |
| `Neg_AxActPolarity` | def | [L147](formal/Logos/AxiomNegationAudit.lean#L147) | `def Neg_AxActPolarity (C : CoreAgencySignature) : Prop` | {}  |
| `Neg_AxGlobalGround` | def | [L179](formal/Logos/AxiomNegationAudit.lean#L179) | `def Neg_AxGlobalGround (M : CoreModalGroundingSignature) : Prop` | {}  |
| `Neg_AxIntentionalChoice` | def | [L112](formal/Logos/AxiomNegationAudit.lean#L112) | `def Neg_AxIntentionalChoice (C : CoreAgencySignature) : Prop` | {}  |
| `Neg_AxPersonalGround` | def | [L400](formal/Logos/AxiomNegationAudit.lean#L400) | `def Neg_AxPersonalGround (G : CorePersonalGroundSignature) : Prop` | {}  |
| `Neg_AxTwoSubjects` | def | [L360](formal/Logos/AxiomNegationAudit.lean#L360) | `def Neg_AxTwoSubjects (V : CoreValueSignature) : Prop` | {}  |
| `Neg_GroundPrincipleProp` | def | [L262](formal/Logos/AxiomNegationAudit.lean#L262) | `def Neg_GroundPrincipleProp (G : CorePropositionalGroundSignature) : Prop` | {}  |
| `Neg_TranscendentalReflectionIntentional` | def | [L331](formal/Logos/AxiomNegationAudit.lean#L331) | `def Neg_TranscendentalReflectionIntentional (R : CoreTranscendentalReflectionSig` | {}  |
| `Neg_Truthmaker` | def | [L218](formal/Logos/AxiomNegationAudit.lean#L218) | `def Neg_Truthmaker (M : CoreModalGroundingSignature) : Prop` | {}  |
| `Neg_UniversalThesisClaimsObjectivity` | def | [L297](formal/Logos/AxiomNegationAudit.lean#L297) | `def Neg_UniversalThesisClaimsObjectivity (R : CoreUniversalObjectivitySignature)` | {}  |
| `TranscendentalReflectionIntentional_Statement` | def | [L326](formal/Logos/AxiomNegationAudit.lean#L326) | `def TranscendentalReflectionIntentional_Statement (R : CoreTranscendentalReflect` | {}  |
| `TruePropExists` | def | [L253](formal/Logos/AxiomNegationAudit.lean#L253) | `def TruePropExists (_G : CorePropositionalGroundSignature) : Prop` | {}  |
| `Truthmaker_Statement` | def | [L213](formal/Logos/AxiomNegationAudit.lean#L213) | `def Truthmaker_Statement (M : CoreModalGroundingSignature) : Prop` | {}  |
| `UniversalThesisClaimsObjectivity_Statement` | def | [L292](formal/Logos/AxiomNegationAudit.lean#L292) | `def UniversalThesisClaimsObjectivity_Statement (R : CoreUniversalObjectivitySign` | {}  |
| `core_compatible_with_neg_a13` | theorem | [L153](formal/Logos/AxiomNegationAudit.lean#L153) | `theorem core_compatible_with_neg_a13 : ∃ (C : CoreAgencySignature), CoreDatumHol` | {}  |
| `core_compatible_with_neg_a14` | theorem | [L118](formal/Logos/AxiomNegationAudit.lean#L118) | `theorem core_compatible_with_neg_a14 : ∃ (C : CoreAgencySignature), CoreDatumHol` | {}  |
| `core_compatible_with_neg_a4` | theorem | [L185](formal/Logos/AxiomNegationAudit.lean#L185) | `theorem core_compatible_with_neg_a4 : ∃ (M : CoreModalGroundingSignature), Neces` | {}  |
| `core_compatible_with_neg_a6` | theorem | [L366](formal/Logos/AxiomNegationAudit.lean#L366) | `theorem core_compatible_with_neg_a6 : ∃ (V : CoreValueSignature), Neg_AxTwoSubje` | {}  |
| `core_compatible_with_neg_a7` | theorem | [L406](formal/Logos/AxiomNegationAudit.lean#L406) | `theorem core_compatible_with_neg_a7 : ∃ (G : CorePersonalGroundSignature), Featu` | {}  |
| `core_compatible_with_neg_ground_principle_prop` | theorem | [L267](formal/Logos/AxiomNegationAudit.lean#L267) | `theorem core_compatible_with_neg_ground_principle_prop : ∃ (G : CorePropositiona` | {}  |
| `core_compatible_with_neg_transcendental_reflection_intentional` | theorem | [L336](formal/Logos/AxiomNegationAudit.lean#L336) | `theorem core_compatible_with_neg_transcendental_reflection_intentional : ∃ (R : ` | {}  |
| `core_compatible_with_neg_truthmaker` | theorem | [L224](formal/Logos/AxiomNegationAudit.lean#L224) | `theorem core_compatible_with_neg_truthmaker : ∃ (M : CoreModalGroundingSignature` | {}  |
| `core_compatible_with_neg_universal_thesis_claims_objectivity` | theorem | [L302](formal/Logos/AxiomNegationAudit.lean#L302) | `theorem core_compatible_with_neg_universal_thesis_claims_objectivity : ∃ (R : Co` | {}  |
| `no_hidden_necessity_synthesis` | theorem | [L437](formal/Logos/AxiomNegationAudit.lean#L437) | `theorem no_hidden_necessity_synthesis : -- 1. A14: AxIntentionalChoice (SEM) is ` | {}  |

### `Logos.Choice`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `AlternativeSensitivity` | def | [L664](formal/Logos/Choice.lean#L664) | `def AlternativeSensitivity (s : Subject) (p : Prop) : Prop` | {Means, Subject}  |
| `Authors` | def | [L617](formal/Logos/Choice.lean#L617) | `def Authors (s : Subject) (p : Prop) (q : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `AuthorshipChoice` | def | [L1327](formal/Logos/Choice.lean#L1327) | `def AuthorshipChoice (s : Subject) (p : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `AxActPolarity` | axiom | [L835](formal/Logos/Choice.lean#L835) | `axiom AxActPolarity : ∀ (s : Subject) (p : Prop), Act s p → Means s (¬ p)` | {AxActPolarity, Initiates, Means, State, Subject}  |
| `AxIntentionalChoice` | axiom | [L824](formal/Logos/Choice.lean#L824) | `axiom AxIntentionalChoice : ∀ (s : Subject) (p : Prop), Act s p → ∃ q, Chooses s` | {AxIntentionalChoice, Initiates, Means, State, Subject}  |
| `CanChoose` | def | [L143](formal/Logos/Choice.lean#L143) | `def CanChoose (s : Subject) (p : Prop) : Prop` | {Means, Subject}  |
| `CausalSettles` | def | [L597](formal/Logos/Choice.lean#L597) | `def CausalSettles (s : Subject) (p : Prop) (q : Prop) : Prop` | {Initiates, State, Subject}  |
| `CausalTransition` | def | [L593](formal/Logos/Choice.lean#L593) | `def CausalTransition (s : Subject) (p : Prop) : Prop` | {Initiates, State, Subject}  |
| `Choice` | def | [L1314](formal/Logos/Choice.lean#L1314) | `def Choice (s : Subject) (p : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `ChoiceField` | def | [L98](formal/Logos/Choice.lean#L98) | `def ChoiceField (s : Subject) (p : Prop) (q : Prop) : Prop` | {Means, Subject}  |
| `ChoiceRel` | def | [L1323](formal/Logos/Choice.lean#L1323) | `def ChoiceRel (s : Subject) (p : Prop) (q : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `Chooses` | def | [L105](formal/Logos/Choice.lean#L105) | `def Chooses (s : Subject) (p : Prop) (q : Prop) : Prop` | {Means, Subject}  |
| `Contemplates` | def | [L628](formal/Logos/Choice.lean#L628) | `def Contemplates (s : Subject) (p : Prop) (q : Prop) : Prop` | {Means, Subject}  |
| `ContemplatesWithoutSettling` | def | [L637](formal/Logos/Choice.lean#L637) | `def ContemplatesWithoutSettling (s : Subject) (p : Prop) (q : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `CounterfactualAct` | def | [L1194](formal/Logos/Choice.lean#L1194) | `def CounterfactualAct (s : Subject) (p : Prop) (q : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `DeliberateAuthorship` | def | [L647](formal/Logos/Choice.lean#L647) | `def DeliberateAuthorship (s : Subject) (p : Prop) (q : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `DeliberateChoice` | def | [L487](formal/Logos/Choice.lean#L487) | `def DeliberateChoice (s : Subject) (p : Prop) (q : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `Deliberates` | def | [L1304](formal/Logos/Choice.lean#L1304) | `def Deliberates (s : Subject) (p : Prop) (q : Prop) : Prop` | {Means, Subject}  |
| `DescriptiveAct` | def | [L1216](formal/Logos/Choice.lean#L1216) | `def DescriptiveAct (s : Subject) (p : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `DoubtingDatum` | def | [L1138](formal/Logos/Choice.lean#L1138) | `def DoubtingDatum : Prop` | {Means, Subject}  |
| `Doubts` | def | [L1132](formal/Logos/Choice.lean#L1132) | `def Doubts (s : Subject) (p : Prop) : Prop` | {Means, Subject}  |
| `FreeAgency` | def | [L1331](formal/Logos/Choice.lean#L1331) | `def FreeAgency (s : Subject) : Prop` | {Initiates, Means, State, Subject}  |
| `FreeSubject` | def | [L173](formal/Logos/Choice.lean#L173) | `def FreeSubject (s : Subject) : Prop` | {Means, Subject}  |
| `FreeWill` | def | [L166](formal/Logos/Choice.lean#L166) | `def FreeWill (s : Subject) : Prop` | {Means, Subject}  |
| `JUDGE_HAS_CHOICE_FIELD` | theorem | [L373](formal/Logos/Choice.lean#L373) | `theorem JUDGE_HAS_CHOICE_FIELD (h : ¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) : ∃ s :` | {AxTwoSubjects, Means, Subject} → C54 |
| `Meaning_I` | def | [L120](formal/Logos/Choice.lean#L120) | `def Meaning_I (p : Prop) : Prop` | {Means, Subject}  |
| `MissingCognitiveHorn` | def | [L952](formal/Logos/Choice.lean#L952) | `def MissingCognitiveHorn (s : Subject) (p : Prop) : Prop` | {Means, Subject}  |
| `NoChoiceField` | def | [L346](formal/Logos/Choice.lean#L346) | `def NoChoiceField : Prop` | {Means, Subject}  |
| `ReasonResponsiveAct` | def | [L1190](formal/Logos/Choice.lean#L1190) | `def ReasonResponsiveAct (s : Subject) (p : Prop) (r : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `Rejects` | def | [L526](formal/Logos/Choice.lean#L526) | `def Rejects (s : Subject) (q : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `RelationalIntentionality` | def | [L668](formal/Logos/Choice.lean#L668) | `def RelationalIntentionality (s : Subject) (p : Prop) (q : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `Selects` | def | [L442](formal/Logos/Choice.lean#L442) | `def Selects (s : Subject) (p : Prop) (q : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `SelfAssertedAuthorship` | def | [L1263](formal/Logos/Choice.lean#L1263) | `def SelfAssertedAuthorship (s : Subject) (p : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `SelfAssertedChoice` | def | [L1258](formal/Logos/Choice.lean#L1258) | `def SelfAssertedChoice (s : Subject) (p : Prop) : Prop` | {Means, Subject}  |
| `SelfAssertedDeliberateChoice` | def | [L1268](formal/Logos/Choice.lean#L1268) | `def SelfAssertedDeliberateChoice (s : Subject) (p : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `SelfAssertedParadox` | def | [L1273](formal/Logos/Choice.lean#L1273) | `def SelfAssertedParadox (s : Subject) (p : Prop) : Prop` | {Means, Subject}  |
| `SelfDenialOfChoice` | def | [L1235](formal/Logos/Choice.lean#L1235) | `def SelfDenialOfChoice (s : Subject) (p : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `SelfDenialOfExecutiveChoice` | def | [L1340](formal/Logos/Choice.lean#L1340) | `def SelfDenialOfExecutiveChoice (s : Subject) (p : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `T11_choiceField` | theorem | [L292](formal/Logos/Choice.lean#L292) | `theorem T11_choiceField (h : ∃ s : Subject, ∃ p : Prop, A s p) : ∃ s : Subject, ` | {Initiates, Means, State, Subject} → C39 |
| `T11_choiceField_from_plurality` | theorem | [L299](formal/Logos/Choice.lean#L299) | `theorem T11_choiceField_from_plurality : ∃ s : Subject, Person s ∧ ∃ p q : Prop,` | {AxTwoSubjects, Means, Subject}  |
| `TeleologicalAct` | def | [L1186](formal/Logos/Choice.lean#L1186) | `def TeleologicalAct (s : Subject) (p : Prop) (g : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `act_decomposition` | theorem | [L787](formal/Logos/Choice.lean#L787) | `theorem act_decomposition (s : Subject) (p : Prop) : Act s p ↔ Means s p ∧ ∃ w w` | {Initiates, Means, State, Subject}  |
| `act_implies_asserts_bridge` | def | [L689](formal/Logos/Choice.lean#L689) | `def act_implies_asserts_bridge : Prop` | {Initiates, Means, State, Subject}  |
| `act_implies_authors` | theorem | [L621](formal/Logos/Choice.lean#L621) | `theorem act_implies_authors (s : Subject) (p : Prop) (h : Act s p) (hNoActNeg : ` | {Initiates, Means, State, Subject}  |
| `act_implies_causalTransition` | theorem | [L601](formal/Logos/Choice.lean#L601) | `theorem act_implies_causalTransition {s : Subject} {p : Prop} (h : Act s p) : Ca` | {Initiates, Means, State, Subject}  |
| `act_implies_choiceField` | theorem | [L606](formal/Logos/Choice.lean#L606) | `theorem act_implies_choiceField (s : Subject) (p : Prop) (h : Act s p) : ∃ q : P` | {Initiates, Means, State, Subject}  |
| `act_missing_horn_iff_chooses` | theorem | [L985](formal/Logos/Choice.lean#L985) | `theorem act_missing_horn_iff_chooses (s : Subject) (p : Prop) (hAct : Act s p) :` | {Initiates, Means, State, Subject}  |
| `act_missing_horn_implies_chooses` | theorem | [L978](formal/Logos/Choice.lean#L978) | `theorem act_missing_horn_implies_chooses (s : Subject) (p : Prop) : Act s p ∧ Mi` | {Initiates, Means, State, Subject}  |
| `act_polarity_implies_conditional` | theorem | [L848](formal/Logos/Choice.lean#L848) | `theorem act_polarity_implies_conditional (h : act_polarity_principle) : conditio` | {Initiates, Means, State, Subject}  |
| `act_polarity_implies_contrastive` | theorem | [L885](formal/Logos/Choice.lean#L885) | `theorem act_polarity_implies_contrastive (h : act_polarity_principle) : contrast` | {Initiates, Means, State, Subject}  |
| `act_polarity_implies_existential` | theorem | [L854](formal/Logos/Choice.lean#L854) | `theorem act_polarity_implies_existential (h : act_polarity_principle) (hAct : ∃ ` | {Initiates, Means, State, Subject}  |
| `act_polarity_implies_existential_choice` | theorem | [L946](formal/Logos/Choice.lean#L946) | `theorem act_polarity_implies_existential_choice (h : act_polarity_principle) : e` | {Initiates, Means, State, Subject}  |
| `act_polarity_implies_intentional_choice` | theorem | [L891](formal/Logos/Choice.lean#L891) | `theorem act_polarity_implies_intentional_choice (h : act_polarity_principle) : ∀` | {Initiates, Means, State, Subject}  |
| `act_polarity_principle` | def | [L718](formal/Logos/Choice.lean#L718) | `def act_polarity_principle : Prop` | {Initiates, Means, State, Subject}  |
| `act_produces_choice_iff_missing_horn` | theorem | [L1010](formal/Logos/Choice.lean#L1010) | `theorem act_produces_choice_iff_missing_horn (s : Subject) (p : Prop) (hAct : Ac` | {Initiates, Means, State, Subject}  |
| `alternativeSensitivity_implies_genuineChoice` | theorem | [L672](formal/Logos/Choice.lean#L672) | `theorem alternativeSensitivity_implies_genuineChoice {s : Subject} {p : Prop} (h` | {Initiates, Means, State, Subject}  |
| `asserting_noChoiceField_is_choiceField` | theorem | [L350](formal/Logos/Choice.lean#L350) | `theorem asserting_noChoiceField_is_choiceField (speaker : Subject) (h : Logos.Ag` | {Initiates, Means, State, Subject}  |
| `assertion_consistency` | theorem | [L416](formal/Logos/Choice.lean#L416) | `theorem assertion_consistency {s : Subject} {p : Prop} (h : Asserts s p) : ¬ Ass` | {Initiates, Means, State, Subject}  |
| `asserts_implies_choice` | theorem | [L1318](formal/Logos/Choice.lean#L1318) | `theorem asserts_implies_choice (s : Subject) (p : Prop) (hAss : Asserts s p) : C` | {Initiates, Means, State, Subject}  |
| `asserts_implies_freeAgency` | theorem | [L1335](formal/Logos/Choice.lean#L1335) | `theorem asserts_implies_freeAgency {s : Subject} {p : Prop} (hAss : Asserts s p)` | {Initiates, Means, State, Subject}  |
| `asserts_implies_selects` | theorem | [L611](formal/Logos/Choice.lean#L611) | `theorem asserts_implies_selects (s : Subject) (p : Prop) (h : Asserts s p) : ∃ q` | {Initiates, Means, State, Subject}  |
| `asserts_selects` | theorem | [L448](formal/Logos/Choice.lean#L448) | `theorem asserts_selects (s : Subject) (p : Prop) (h : Asserts s p) : Selects s p` | {Initiates, Means, State, Subject}  |
| `asserts_selects_all_incompatible` | theorem | [L455](formal/Logos/Choice.lean#L455) | `theorem asserts_selects_all_incompatible (s : Subject) (p q : Prop) (h : Asserts` | {Initiates, Means, State, Subject}  |
| `bilateral_implies_act_polarity` | theorem | [L723](formal/Logos/Choice.lean#L723) | `theorem bilateral_implies_act_polarity (h : bilateral_intentionality_principle) ` | {Initiates, Means, State, Subject}  |
| `bilateral_intentionality_principle` | def | [L712](formal/Logos/Choice.lean#L712) | `def bilateral_intentionality_principle : Prop` | {Means, Subject}  |
| `canChoose_unfold` | theorem | [L148](formal/Logos/Choice.lean#L148) | `theorem canChoose_unfold {s : Subject} {p : Prop} : CanChoose s p ↔ ∃ q : Prop, ` | {Means, Subject, CL}  |
| `choiceField_exists` | theorem | [L332](formal/Logos/Choice.lean#L332) | `theorem choiceField_exists (h : ∃ s : Subject, ∃ p : Prop, A s p) : ∃ s : Subjec` | {Initiates, Means, State, Subject} → C52 |
| `choiceField_exists_from_plurality` | theorem | [L340](formal/Logos/Choice.lean#L340) | `theorem choiceField_exists_from_plurality : ∃ s : Subject, ∃ p q : Prop, ChoiceF` | {AxTwoSubjects, Means, Subject}  |
| `chooses_implies_freeSubject` | theorem | [L190](formal/Logos/Choice.lean#L190) | `theorem chooses_implies_freeSubject {s : Subject} {p q : Prop} (h : Chooses s p ` | {Means, Subject}  |
| `chooses_implies_freeWill` | theorem | [L185](formal/Logos/Choice.lean#L185) | `theorem chooses_implies_freeWill {s : Subject} {p q : Prop} (h : Chooses s p q) ` | {Means, Subject}  |
| `conditional_act_polarity` | def | [L839](formal/Logos/Choice.lean#L839) | `def conditional_act_polarity : Prop` | {Initiates, Means, State, Subject}  |
| `contemplatesWithoutSettling_implies_freeWill` | theorem | [L641](formal/Logos/Choice.lean#L641) | `theorem contemplatesWithoutSettling_implies_freeWill {s : Subject} {p q : Prop} ` | {Initiates, Means, State, Subject}  |
| `contemplates_iff_chooses` | theorem | [L632](formal/Logos/Choice.lean#L632) | `theorem contemplates_iff_chooses (s : Subject) (p q : Prop) : Contemplates s p q` | {Means, Subject}  |
| `contrastive_agency_implies_existential` | theorem | [L913](formal/Logos/Choice.lean#L913) | `theorem contrastive_agency_implies_existential (h : contrastive_agency_principle` | {Initiates, Means, State, Subject}  |
| `contrastive_agency_principle` | def | [L875](formal/Logos/Choice.lean#L875) | `def contrastive_agency_principle : Prop` | {Initiates, Means, State, Subject}  |
| `contrastive_implies_intentional_choice` | theorem | [L906](formal/Logos/Choice.lean#L906) | `theorem contrastive_implies_intentional_choice : contrastive_agency_principle → ` | {Initiates, Means, State, Subject}  |
| `counterfactual_act_implies_genuineChoice` | theorem | [L1210](formal/Logos/Choice.lean#L1210) | `theorem counterfactual_act_implies_genuineChoice (s : Subject) (p q : Prop) (h :` | {AxIntentionalChoice, Initiates, Means, State, Subject}  |
| `deliberateAuthorship_implies_chooses` | theorem | [L651](formal/Logos/Choice.lean#L651) | `theorem deliberateAuthorship_implies_chooses {s : Subject} {p q : Prop} (h : Del` | {Initiates, Means, State, Subject}  |
| `deliberateAuthorship_implies_deliberateChoice` | theorem | [L657](formal/Logos/Choice.lean#L657) | `theorem deliberateAuthorship_implies_deliberateChoice {s : Subject} {p q : Prop}` | {Initiates, Means, State, Subject}  |
| `deliberateChoice_exists_of_assertion_and_negation_meaning` | theorem | [L562](formal/Logos/Choice.lean#L562) | `theorem deliberateChoice_exists_of_assertion_and_negation_meaning (h : deliberat` | {Initiates, Means, State, Subject}  |
| `deliberateChoice_iff_selects_and_means` | theorem | [L506](formal/Logos/Choice.lean#L506) | `theorem deliberateChoice_iff_selects_and_means (s : Subject) (p q : Prop) : Deli` | {Initiates, Means, State, Subject} → C100 |
| `deliberateChoice_iff_selects_and_rejects` | theorem | [L532](formal/Logos/Choice.lean#L532) | `theorem deliberateChoice_iff_selects_and_rejects (s : Subject) (p q : Prop) : De` | {Initiates, Means, State, Subject}  |
| `deliberateChoice_implies_chooses` | theorem | [L498](formal/Logos/Choice.lean#L498) | `theorem deliberateChoice_implies_chooses {s : Subject} {p q : Prop} (h : Deliber` | {Initiates, Means, State, Subject} → C98 |
| `deliberateChoice_implies_selects` | theorem | [L492](formal/Logos/Choice.lean#L492) | `theorem deliberateChoice_implies_selects {s : Subject} {p q : Prop} (h : Deliber` | {Initiates, Means, State, Subject} → C97 |
| `deliberateChoice_negation_decomposition` | theorem | [L518](formal/Logos/Choice.lean#L518) | `theorem deliberateChoice_negation_decomposition (s : Subject) (p : Prop) : Delib` | {Initiates, Means, State, Subject}  |
| `deliberateChoice_negation_iff` | theorem | [L542](formal/Logos/Choice.lean#L542) | `theorem deliberateChoice_negation_iff (s : Subject) (p : Prop) (hAss : Asserts s` | {Initiates, Means, State, Subject}  |
| `deliberateGenuineChoiceResource` | def | [L556](formal/Logos/Choice.lean#L556) | `def deliberateGenuineChoiceResource : Prop` | {Initiates, Means, State, Subject}  |
| `deliberateResource_of_act_polarity` | theorem | [L1040](formal/Logos/Choice.lean#L1040) | `theorem deliberateResource_of_act_polarity (hPolarity : act_polarity_principle) ` | {Initiates, Means, State, Subject}  |
| `deliberateResource_of_bilateral_intentionality` | theorem | [L1059](formal/Logos/Choice.lean#L1059) | `theorem deliberateResource_of_bilateral_intentionality (hBilateral : bilateral_i` | {Initiates, Means, State, Subject}  |
| `deliberate_resource_implies_genuine_choice` | theorem | [L575](formal/Logos/Choice.lean#L575) | `theorem deliberate_resource_implies_genuine_choice (h : deliberateGenuineChoiceR` | {Initiates, Means, State, Subject}  |
| `deliberates_iff_chooses` | theorem | [L1308](formal/Logos/Choice.lean#L1308) | `theorem deliberates_iff_chooses (s : Subject) (p q : Prop) : Deliberates s p q ↔` | {Means, Subject}  |
| `descriptive_act_implies_genuineChoice` | theorem | [L1220](formal/Logos/Choice.lean#L1220) | `theorem descriptive_act_implies_genuineChoice (s : Subject) (p : Prop) (h : Desc` | {AxIntentionalChoice, Initiates, Means, State, Subject}  |
| `doubt_existence_bridge` | def | [L1170](formal/Logos/Choice.lean#L1170) | `def doubt_existence_bridge : Prop` | {Initiates, Means, State, Subject}  |
| `existential_act_polarity` | def | [L844](formal/Logos/Choice.lean#L844) | `def existential_act_polarity : Prop` | {Initiates, Means, State, Subject}  |
| `existential_choice_iff_f1b` | theorem | [L941](formal/Logos/Choice.lean#L941) | `theorem existential_choice_iff_f1b : existential_intentional_choice ↔ ((∃ s : Su` | {Initiates, Means, State, Subject}  |
| `existential_contrastive_agency` | def | [L880](formal/Logos/Choice.lean#L880) | `def existential_contrastive_agency : Prop` | {Initiates, Means, State, Subject}  |
| `existential_intentional_choice` | def | [L921](formal/Logos/Choice.lean#L921) | `def existential_intentional_choice : Prop` | {Initiates, Means, State, Subject}  |
| `f1b_iff_missing_cognitive_horn` | theorem | [L997](formal/Logos/Choice.lean#L997) | `theorem f1b_iff_missing_cognitive_horn : ((∃ s : Subject, ∃ p : Prop, Act s p) →` | {Initiates, Means, State, Subject}  |
| `freeSubject_exists` | theorem | [L1126](formal/Logos/Choice.lean#L1126) | `theorem freeSubject_exists (h : ∃ s : Subject, ∃ p : Prop, Act s p) : ∃ s : Subj` | {AxIntentionalChoice, Initiates, Means, State, Subject}  |
| `freeSubject_exists_of_act` | theorem | [L1104](formal/Logos/Choice.lean#L1104) | `theorem freeSubject_exists_of_act (h : ∃ s : Subject, ∃ p : Prop, Act s p) : ∃ s` | {AxIntentionalChoice, Initiates, Means, State, Subject}  |
| `freeSubject_exists_of_contrastive_act` | theorem | [L1033](formal/Logos/Choice.lean#L1033) | `theorem freeSubject_exists_of_contrastive_act (h : contrastive_agency_principle)` | {Initiates, Means, State, Subject}  |
| `freeSubject_iff_freeWill` | theorem | [L176](formal/Logos/Choice.lean#L176) | `theorem freeSubject_iff_freeWill (s : Subject) : FreeSubject s ↔ FreeWill s` | {Means, Subject}  |
| `freeSubject_implies_intentional` | theorem | [L202](formal/Logos/Choice.lean#L202) | `theorem freeSubject_implies_intentional (s : Subject) (h : FreeSubject s) : Logo` | {Means, Subject}  |
| `freeSubject_implies_intentionalSubject` | theorem | [L196](formal/Logos/Choice.lean#L196) | `theorem freeSubject_implies_intentionalSubject (s : Subject) (h : FreeSubject s)` | {Means, Subject}  |
| `freeWillExists_of_chooses` | theorem | [L209](formal/Logos/Choice.lean#L209) | `theorem freeWillExists_of_chooses (h : ∃ s : Subject, ∃ p q : Prop, Chooses s p ` | {Means, Subject}  |
| `freeWillExists_of_genuineChoice` | theorem | [L257](formal/Logos/Choice.lean#L257) | `theorem freeWillExists_of_genuineChoice : genuineChoice_exists → ∃ s : Subject, ` | {Means, Subject}  |
| `freeWill_exists` | theorem | [L1120](formal/Logos/Choice.lean#L1120) | `theorem freeWill_exists (h : ∃ s : Subject, ∃ p : Prop, Act s p) : ∃ s : Subject` | {AxIntentionalChoice, Initiates, Means, State, Subject} → F1b |
| `freeWill_exists_of_act` | theorem | [L1097](formal/Logos/Choice.lean#L1097) | `theorem freeWill_exists_of_act (h : ∃ s : Subject, ∃ p : Prop, Act s p) : ∃ s : ` | {AxIntentionalChoice, Initiates, Means, State, Subject}  |
| `freeWill_exists_of_act_polarity` | theorem | [L1111](formal/Logos/Choice.lean#L1111) | `theorem freeWill_exists_of_act_polarity (h : ∃ s : Subject, ∃ p : Prop, Act s p)` | {AxActPolarity, Initiates, Means, State, Subject}  |
| `freeWill_exists_of_contrastive_act` | theorem | [L1026](formal/Logos/Choice.lean#L1026) | `theorem freeWill_exists_of_contrastive_act (h : contrastive_agency_principle) (h` | {Initiates, Means, State, Subject}  |
| `freeWill_exists_of_doubt_bridge` | theorem | [L1180](formal/Logos/Choice.lean#L1180) | `theorem freeWill_exists_of_doubt_bridge (hBridge : doubt_existence_bridge) (hAct` | {Initiates, Means, State, Subject}  |
| `freeWill_exists_of_doubt_datum` | theorem | [L1162](formal/Logos/Choice.lean#L1162) | `theorem freeWill_exists_of_doubt_datum (h : DoubtingDatum) : ∃ s : Subject, Free` | {Means, Subject}  |
| `freeWill_exists_of_existential_act_polarity` | theorem | [L867](formal/Logos/Choice.lean#L867) | `theorem freeWill_exists_of_existential_act_polarity (h : existential_act_polarit` | {Initiates, Means, State, Subject}  |
| `freeWill_exists_of_existential_choice` | theorem | [L933](formal/Logos/Choice.lean#L933) | `theorem freeWill_exists_of_existential_choice (h : existential_intentional_choic` | {Initiates, Means, State, Subject}  |
| `freeWill_iff_means_missing_horn` | theorem | [L969](formal/Logos/Choice.lean#L969) | `theorem freeWill_iff_means_missing_horn : (∃ s : Subject, FreeWill s) ↔ ∃ s : Su` | {Means, Subject}  |
| `freeWill_of_doubt` | theorem | [L1149](formal/Logos/Choice.lean#L1149) | `theorem freeWill_of_doubt {s : Subject} {p : Prop} (hDoubt : Doubts s p) : FreeW` | {Means, Subject}  |
| `genuineChoice_exists` | def | [L232](formal/Logos/Choice.lean#L232) | `def genuineChoice_exists : Prop` | {Means, Subject}  |
| `genuineChoice_exists_of_act` | theorem | [L1078](formal/Logos/Choice.lean#L1078) | `theorem genuineChoice_exists_of_act (h : ∃ s : Subject, ∃ p : Prop, Act s p) : g` | {AxActPolarity, Initiates, Means, State, Subject}  |
| `genuineChoice_exists_of_act_constitutive` | theorem | [L1087](formal/Logos/Choice.lean#L1087) | `theorem genuineChoice_exists_of_act_constitutive (h : ∃ s : Subject, ∃ p : Prop,` | {AxIntentionalChoice, Initiates, Means, State, Subject}  |
| `genuineChoice_exists_of_act_polarity` | theorem | [L1049](formal/Logos/Choice.lean#L1049) | `theorem genuineChoice_exists_of_act_polarity (hPolarity : act_polarity_principle` | {Initiates, Means, State, Subject}  |
| `genuineChoice_exists_of_assertion_and_negation_meaning` | abbrev | [L585](formal/Logos/Choice.lean#L585) | `abbrev genuineChoice_exists_of_assertion_and_negation_meaning` | {Initiates, Means, State, Subject}  |
| `genuineChoice_exists_of_bilateral_intentionality` | theorem | [L1068](formal/Logos/Choice.lean#L1068) | `theorem genuineChoice_exists_of_bilateral_intentionality (hBilateral : bilateral` | {Initiates, Means, State, Subject}  |
| `genuineChoice_exists_of_contrastive_act` | theorem | [L1017](formal/Logos/Choice.lean#L1017) | `theorem genuineChoice_exists_of_contrastive_act (h : contrastive_agency_principl` | {Initiates, Means, State, Subject}  |
| `genuineChoice_exists_of_doubt_bridge` | theorem | [L1174](formal/Logos/Choice.lean#L1174) | `theorem genuineChoice_exists_of_doubt_bridge (hBridge : doubt_existence_bridge) ` | {Initiates, Means, State, Subject}  |
| `genuineChoice_exists_of_doubt_datum` | theorem | [L1155](formal/Logos/Choice.lean#L1155) | `theorem genuineChoice_exists_of_doubt_datum (h : DoubtingDatum) : genuineChoice_` | {Means, Subject}  |
| `genuineChoice_exists_of_existential_act_polarity` | theorem | [L861](formal/Logos/Choice.lean#L861) | `theorem genuineChoice_exists_of_existential_act_polarity (h : existential_act_po` | {Initiates, Means, State, Subject}  |
| `genuineChoice_of_doubt` | theorem | [L1144](formal/Logos/Choice.lean#L1144) | `theorem genuineChoice_of_doubt {s : Subject} {p : Prop} (hDoubt : Doubts s p) : ` | {Means, Subject}  |
| `genuineChoice_requires_error_possibility` | theorem | [L281](formal/Logos/Choice.lean#L281) | `theorem genuineChoice_requires_error_possibility : genuineChoice_exists → ¬ (∀ s` | {Means, Subject}  |
| `incompatible_self_negation` | theorem | [L113](formal/Logos/Choice.lean#L113) | `theorem incompatible_self_negation (p : Prop) : Incompatible p (¬ p)` | {} → C50 |
| `intentional_choice_implies_contrastive` | theorem | [L898](formal/Logos/Choice.lean#L898) | `theorem intentional_choice_implies_contrastive : (∀ (s : Subject) (p : Prop), Ac` | {Initiates, Means, State, Subject}  |
| `intentional_choice_implies_existential_choice` | theorem | [L925](formal/Logos/Choice.lean#L925) | `theorem intentional_choice_implies_existential_choice (h : ∀ (s : Subject) (p : ` | {Initiates, Means, State, Subject}  |
| `intentional_hasChoiceField` | theorem | [L309](formal/Logos/Choice.lean#L309) | `theorem intentional_hasChoiceField {s : Subject} (hIn : Logos.Person.Intentional` | {Means, Subject}  |
| `judge_asserting_rightWrong_has_choiceField` | theorem | [L381](formal/Logos/Choice.lean#L381) | `theorem judge_asserting_rightWrong_has_choiceField (speaker : Subject) (h : Logo` | {Initiates, Means, State, Subject}  |
| `meaning_I_needs_subject` | theorem | [L128](formal/Logos/Choice.lean#L128) | `theorem meaning_I_needs_subject {p : Prop} (h : Meaning_I p) : ∃ s : Subject, Me` | {Means, Subject}  |
| `meaning_needs_subject` | theorem | [L137](formal/Logos/Choice.lean#L137) | `theorem meaning_needs_subject {s : Subject} {p : Prop} (hm : Means s p) : ∃ t : ` | {Means, Subject} → C49 |
| `means_missing_horn_iff_chooses` | theorem | [L958](formal/Logos/Choice.lean#L958) | `theorem means_missing_horn_iff_chooses (s : Subject) (p : Prop) : Means s p ∧ Mi` | {Means, Subject}  |
| `noChoiceField_contradicts_field` | theorem | [L362](formal/Logos/Choice.lean#L362) | `theorem noChoiceField_contradicts_field (hField : ∃ s : Subject, ∃ p q : Prop, C` | {Means, Subject}  |
| `noChoiceField_selfRefutes` | theorem | [L357](formal/Logos/Choice.lean#L357) | `theorem noChoiceField_selfRefutes (speaker : Subject) (h : Logos.Agency.Asserts ` | {Initiates, Means, State, Subject} → C53 |
| `noStrongTruth_assertable_refutes` | theorem | [L1229](formal/Logos/Choice.lean#L1229) | `theorem noStrongTruth_assertable_refutes (speaker : Subject) : Asserts speaker (` | {Initiates, Means, State, Subject, CL} → C94 |
| `noSubject_contradicts_subject` | theorem | [L405](formal/Logos/Choice.lean#L405) | `theorem noSubject_contradicts_subject (hSubj : ∃ s : Subject, Logos.Agency.Subje` | {Initiates, Means, State, Subject}  |
| `noSubject_selfRefutes` | theorem | [L400](formal/Logos/Choice.lean#L400) | `theorem noSubject_selfRefutes (speaker : Subject) (h : Logos.Agency.Asserts spea` | {Initiates, Means, State, Subject} → C57 |
| `no_one_asserts_incompatible_pair` | theorem | [L427](formal/Logos/Choice.lean#L427) | `theorem no_one_asserts_incompatible_pair : ¬ ∃ s : Subject, ∃ p q : Prop, Assert` | {Initiates, Means, State, Subject}  |
| `no_selection_no_assertion` | theorem | [L473](formal/Logos/Choice.lean#L473) | `theorem no_selection_no_assertion (s : Subject) (p : Prop) (hNo : ∀ q : Prop, ¬ ` | {Initiates, Means, State, Subject}  |
| `person_hasChoiceField` | theorem | [L322](formal/Logos/Choice.lean#L322) | `theorem person_hasChoiceField {s : Subject} (hs : Person s) : ∃ p q : Prop, Choi` | {Means, Subject} → C51 |
| `reasonResponsive_act_implies_genuineChoice` | theorem | [L1204](formal/Logos/Choice.lean#L1204) | `theorem reasonResponsive_act_implies_genuineChoice (s : Subject) (p r : Prop) (h` | {AxIntentionalChoice, Initiates, Means, State, Subject}  |
| `rejectedHornCoMeant` | def | [L249](formal/Logos/Choice.lean#L249) | `def rejectedHornCoMeant : Prop` | {Means, Subject}  |
| `rejectedHornCoMeant_implies_genuineChoice` | theorem | [L268](formal/Logos/Choice.lean#L268) | `theorem rejectedHornCoMeant_implies_genuineChoice : rejectedHornCoMeant → genuin` | {Means, Subject}  |
| `relationalIntentionality_implies_genuineChoice` | theorem | [L679](formal/Logos/Choice.lean#L679) | `theorem relationalIntentionality_implies_genuineChoice {s : Subject} {p q : Prop` | {Initiates, Means, State, Subject}  |
| `rightWrong_implies_someone_means` | theorem | [L393](formal/Logos/Choice.lean#L393) | `theorem rightWrong_implies_someone_means (h : ¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_` | {AxTwoSubjects, Means, Subject} → C61 |
| `selection_exists` | theorem | [L465](formal/Logos/Choice.lean#L465) | `theorem selection_exists (h : ∃ s : Subject, ∃ p : Prop, Asserts s p) : ∃ s : Su` | {Initiates, Means, State, Subject}  |
| `selection_exists_of_act` | theorem | [L695](formal/Logos/Choice.lean#L695) | `theorem selection_exists_of_act (hBridge : act_implies_asserts_bridge) (h : ∃ s ` | {Initiates, Means, State, Subject} → C99 |
| `selfAssertedChoice_factive_implies_chooses` | theorem | [L1277](formal/Logos/Choice.lean#L1277) | `theorem selfAssertedChoice_factive_implies_chooses {s : Subject} {p : Prop} (hAs` | {Initiates, Means, State, Subject}  |
| `selfAssertedDeliberateChoice_factive_implies_chooses` | theorem | [L1283](formal/Logos/Choice.lean#L1283) | `theorem selfAssertedDeliberateChoice_factive_implies_chooses {s : Subject} {p : ` | {Initiates, Means, State, Subject}  |
| `selfAssertedParadox_is_false` | theorem | [L1290](formal/Logos/Choice.lean#L1290) | `theorem selfAssertedParadox_is_false {s : Subject} {p : Prop} (hSelf : SelfAsser` | {Means, Subject}  |
| `selfAssertedParadox_not_assertable` | theorem | [L1356](formal/Logos/Choice.lean#L1356) | `theorem selfAssertedParadox_not_assertable {s : Subject} {p : Prop} (hSelf : Sel` | {Initiates, Means, State, Subject}  |
| `selfDenialOfExecutiveChoice_selfRefutes` | theorem | [L1347](formal/Logos/Choice.lean#L1347) | `theorem selfDenialOfExecutiveChoice_selfRefutes {s : Subject} {p : Prop} (hDenia` | {Initiates, Means, State, Subject}  |
| `selfDenial_implies_genuineChoice_of_a14` | theorem | [L1247](formal/Logos/Choice.lean#L1247) | `theorem selfDenial_implies_genuineChoice_of_a14 {s : Subject} {p : Prop} (hDenia` | {AxIntentionalChoice, Initiates, Means, State, Subject}  |
| `selfDenial_implies_genuineChoice_of_polarity` | theorem | [L1239](formal/Logos/Choice.lean#L1239) | `theorem selfDenial_implies_genuineChoice_of_polarity {s : Subject} {p : Prop} (h` | {AxActPolarity, Initiates, Means, State, Subject}  |
| `teleological_act_implies_genuineChoice` | theorem | [L1198](formal/Logos/Choice.lean#L1198) | `theorem teleological_act_implies_genuineChoice (s : Subject) (p g : Prop) (h : T` | {AxIntentionalChoice, Initiates, Means, State, Subject}  |

### `Logos.ChoiceRepair`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `ActionSelection` | def | [L118](formal/Logos/ChoiceRepair.lean#L118) | `def ActionSelection {Subj : Type} (CS : FineCognitiveSubject Subj) (ActRel : Sub` | {}  |
| `AgentCausalSettlement` | def | [L123](formal/Logos/ChoiceRepair.lean#L123) | `def AgentCausalSettlement {Subj : Type} (CS : FineCognitiveSubject Subj) (ActRel` | {}  |
| `CognitiveSettlement` | def | [L110](formal/Logos/ChoiceRepair.lean#L110) | `def CognitiveSettlement {Subj : Type} (CS : FineCognitiveSubject Subj) (s : Subj` | {}  |
| `ExtendedGammaModel` | structure | [L361](formal/Logos/ChoiceRepair.lean#L361) | `structure ExtendedGammaModel where` | —  |
| `FreeWill_Libertarian` | def | [L386](formal/Logos/ChoiceRepair.lean#L386) | `def FreeWill_Libertarian (M : ExtendedGammaModel) (s : M.Subj) : Prop` | {}  |
| `FreeWill_Settlement` | def | [L374](formal/Logos/ChoiceRepair.lean#L374) | `def FreeWill_Settlement (Subj : Type) (CS : FineCognitiveSubject Subj) (s : Subj` | {}  |
| `OldChooses` | def | [L56](formal/Logos/ChoiceRepair.lean#L56) | `def OldChooses (s : Subject) (p q : Prop) : Prop` | {Means, Subject}  |
| `OldFreeWill` | def | [L57](formal/Logos/ChoiceRepair.lean#L57) | `def OldFreeWill (s : Subject) : Prop` | {Means, Subject}  |
| `SettlementChoice` | def | [L77](formal/Logos/ChoiceRepair.lean#L77) | `def SettlementChoice {Subj : Type} (CS : FineCognitiveSubject Subj) (s : Subj) (` | {}  |
| `TransformToDeterministicAgency` | def | [L479](formal/Logos/ChoiceRepair.lean#L479) | `def TransformToDeterministicAgency (M : ExtendedGammaModel) : ExtendedGammaModel` | {}  |
| `VolitionalSettlement` | def | [L114](formal/Logos/ChoiceRepair.lean#L114) | `def VolitionalSettlement {Subj : Type} (CS : FineCognitiveSubject Subj) (s : Sub` | {}  |
| `divergence_between_intentional_resolution_and_old_choice` | theorem | [L63](formal/Logos/ChoiceRepair.lean#L63) | `theorem divergence_between_intentional_resolution_and_old_choice (s : Subject) (` | {Means, Subject}  |
| `libertarian_freewill_is_model_theoretically_independent` | theorem | [L472](formal/Logos/ChoiceRepair.lean#L472) | `theorem libertarian_freewill_is_model_theoretically_independent : (∃ (M : Extend` | {}  |
| `model_A_lib_with_libertarian_freewill` | theorem | [L391](formal/Logos/ChoiceRepair.lean#L391) | `theorem model_A_lib_with_libertarian_freewill : ∃ (M : ExtendedGammaModel), ∃ (s` | {}  |
| `model_B_lib_without_libertarian_freewill` | theorem | [L430](formal/Logos/ChoiceRepair.lean#L430) | `theorem model_B_lib_without_libertarian_freewill : ∃ (M : ExtendedGammaModel), ∀` | {}  |
| `model_M19_cognitive_resolution_without_volition` | theorem | [L134](formal/Logos/ChoiceRepair.lean#L134) | `theorem model_M19_cognitive_resolution_without_volition : ∃ (Subj : Type) (CS : ` | {}  |
| `model_M20_volition_without_alternative_capacity` | theorem | [L162](formal/Logos/ChoiceRepair.lean#L162) | `theorem model_M20_volition_without_alternative_capacity : ∃ (Subj : Type) (CS : ` | {}  |
| `model_M21_action_selection_without_libertarian_freedom` | theorem | [L197](formal/Logos/ChoiceRepair.lean#L197) | `theorem model_M21_action_selection_without_libertarian_freedom : ∃ (Subj : Type)` | {}  |
| `model_M22_agent_causal_settlement` | theorem | [L205](formal/Logos/ChoiceRepair.lean#L205) | `theorem model_M22_agent_causal_settlement : ∃ (Subj : Type) (AgentDetermines : S` | {}  |
| `model_M23_fully_deterministic_deliberator` | theorem | [L221](formal/Logos/ChoiceRepair.lean#L221) | `theorem model_M23_fully_deterministic_deliberator : ∃ (StateSpace : Type) (Step ` | {}  |
| `model_M24_automatic_rational_evaluator` | theorem | [L228](formal/Logos/ChoiceRepair.lean#L228) | `theorem model_M24_automatic_rational_evaluator : ∃ (StateSpace : Type) (Evaluate` | {}  |
| `model_M25_passive_truth_tracker` | theorem | [L235](formal/Logos/ChoiceRepair.lean#L235) | `theorem model_M25_passive_truth_tracker : ∃ (Tracker : Prop → Prop), (∀ p : Prop` | {CL}  |
| `model_M26_choice_without_libertarianism` | theorem | [L250](formal/Logos/ChoiceRepair.lean#L250) | `theorem model_M26_choice_without_libertarianism : ∃ (Subj : Type) (CS : FineCogn` | {}  |
| `reductio_derives_compatibilist_freeWill` | theorem | [L378](formal/Logos/ChoiceRepair.lean#L378) | `theorem reductio_derives_compatibilist_freeWill (Subj : Type) (CS : FineCognitiv` | {}  |
| `reductio_derives_settlementChoice` | theorem | [L89](formal/Logos/ChoiceRepair.lean#L89) | `theorem reductio_derives_settlementChoice {Subj : Type} (CS : FineCognitiveSubje` | {}  |
| `settlementChoice_compatible_with_case_D` | theorem | [L285](formal/Logos/ChoiceRepair.lean#L285) | `theorem settlementChoice_compatible_with_case_D : ∃ (D : Type) (Settlement : D →` | {}  |
| `settlementChoice_does_not_entail_modal_freedom` | theorem | [L290](formal/Logos/ChoiceRepair.lean#L290) | `theorem settlementChoice_does_not_entail_modal_freedom : ∃ (Subj : Type) (CS : F` | {}  |
| `settlementChoice_iff_settlement1` | theorem | [L82](formal/Logos/ChoiceRepair.lean#L82) | `theorem settlementChoice_iff_settlement1 {Subj : Type} (CS : FineCognitiveSubjec` | {}  |
| `settlementChoice_is_definitional_unfolding` | theorem | [L98](formal/Logos/ChoiceRepair.lean#L98) | `theorem settlementChoice_is_definitional_unfolding {Subj : Type} (CS : FineCogni` | {}  |
| `settlementChoice_orthogonal_to_old_chooses` | theorem | [L304](formal/Logos/ChoiceRepair.lean#L304) | `theorem settlementChoice_orthogonal_to_old_chooses : (∃ (Subj : Type) (CS : Fine` | {}  |

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

### `Logos.ClassicalTheism`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `ApprehendsGood` | axiom | [L145](formal/Logos/ClassicalTheism.lean#L145) | `axiom ApprehendsGood : Subject → Good → Prop` | —  |
| `AxCondilectus` | axiom | [L186](formal/Logos/ClassicalTheism.lean#L186) | `axiom AxCondilectus : ∀ s1 s2 : Subject, NecessarySubject s1 → NecessarySubject ` | —  |
| `AxContingentRequiresCreator` | axiom | [L121](formal/Logos/ClassicalTheism.lean#L121) | `axiom AxContingentRequiresCreator : ∀ e : Entity, ContingentEntity e → ∃ u : Ent` | —  |
| `AxDivineSimplicity` | axiom | [L181](formal/Logos/ClassicalTheism.lean#L181) | `axiom AxDivineSimplicity : ∀ u1 u2 : Entity, UltimateGround u1 → UltimateGround ` | —  |
| `AxExplanatoryTransfer` | axiom | [L92](formal/Logos/ClassicalTheism.lean#L92) | `axiom AxExplanatoryTransfer : ∀ (u : Entity) (p : Prop), UltimateGround u → Impe` | —  |
| `AxSummumBonum` | axiom | [L162](formal/Logos/ClassicalTheism.lean#L162) | `axiom AxSummumBonum : ∀ u : Entity, UltimateGround u → ∃ g : Good, SummumBonum u` | —  |
| `AxTeleologicalAim` | axiom | [L157](formal/Logos/ClassicalTheism.lean#L157) | `axiom AxTeleologicalAim : ∀ (s : Subject) (p : Prop), Act s p → ∃ g : Good, Tele` | —  |
| `AxTotalityGrounding` | axiom | [L71](formal/Logos/ClassicalTheism.lean#L71) | `axiom AxTotalityGrounding : (∃ e : Entity, ContingentEntity e) → ∃ u : Entity, U` | —  |
| `ContingentEntity` | def | [L47](formal/Logos/ClassicalTheism.lean#L47) | `def ContingentEntity (e : Entity) : Prop` | —  |
| `Creates` | axiom | [L117](formal/Logos/ClassicalTheism.lean#L117) | `axiom Creates : Entity → Entity → Prop` | —  |
| `Good` | axiom | [L141](formal/Logos/ClassicalTheism.lean#L141) | `axiom Good : Type` | —  |
| `GroundsEntity` | axiom | [L61](formal/Logos/ClassicalTheism.lean#L61) | `axiom GroundsEntity : Entity → Entity → Prop` | —  |
| `Impersonal` | axiom | [L86](formal/Logos/ClassicalTheism.lean#L86) | `axiom Impersonal : Entity → Prop` | —  |
| `NecessarilyTrue` | abbrev | [L51](formal/Logos/ClassicalTheism.lean#L51) | `abbrev □(p : Prop) : Prop` | —  |
| `SummumBonum` | axiom | [L153](formal/Logos/ClassicalTheism.lean#L153) | `axiom SummumBonum : Entity → Good → Prop` | —  |
| `TeleologicalAim` | axiom | [L149](formal/Logos/ClassicalTheism.lean#L149) | `axiom TeleologicalAim : Subject → Prop → Good → Prop` | —  |
| `UltimateGround` | def | [L64](formal/Logos/ClassicalTheism.lean#L64) | `def UltimateGround (u : Entity) : Prop` | —  |
| `divine_love_derives_trinity` | theorem | [L194](formal/Logos/ClassicalTheism.lean#L194) | `theorem divine_love_derives_trinity (u : Entity) (_hu : UltimateGround u) (s1 s2` | —  |
| `free_agency_points_to_supreme_good` | theorem | [L166](formal/Logos/ClassicalTheism.lean#L166) | `theorem free_agency_points_to_supreme_good : (∃ s : Subject, ∃ p : Prop, Act s p` | —  |
| `performative_datum_forces_creation` | theorem | [L125](formal/Logos/ClassicalTheism.lean#L125) | `theorem performative_datum_forces_creation (s : Subject) (p : Prop) (_hAct : Act` | —  |
| `totality_grounding_derives_ultimate_ground` | theorem | [L75](formal/Logos/ClassicalTheism.lean#L75) | `theorem totality_grounding_derives_ultimate_ground : (∃ e : Entity, ContingentEn` | —  |
| `ultimate_ground_is_free_subject` | theorem | [L96](formal/Logos/ClassicalTheism.lean#L96) | `theorem ultimate_ground_is_free_subject : (∃ p : Prop, p ∧ ¬ □ p) → ∀ u : Entity` | —  |

### `Logos.CognitiveDiscrimination`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `AD_alone_insufficient_for_missing_horn` | theorem | [L303](formal/Logos/CognitiveDiscrimination.lean#L303) | `theorem AD_alone_insufficient_for_missing_horn : ∃ (Subject : Type) (ActAt : Sub` | {}  |
| `Aboutness` | def | [L99](formal/Logos/CognitiveDiscrimination.lean#L99) | `def Aboutness (s : Subject) (p : Prop) : Prop` | {Means, Subject}  |
| `AlternativeAvailable` | def | [L187](formal/Logos/CognitiveDiscrimination.lean#L187) | `def AlternativeAvailable (Available : Subject → Prop → Prop → Prop) (s : Subject` | {Subject}  |
| `AlternativeAwareness` | def | [L149](formal/Logos/CognitiveDiscrimination.lean#L149) | `def AlternativeAwareness (Subject : Type) (MeansAt : Subject → Prop → Prop) (s :` | {}  |
| `BR_alone_insufficient_for_missing_horn` | theorem | [L324](formal/Logos/CognitiveDiscrimination.lean#L324) | `theorem BR_alone_insufficient_for_missing_horn : ∃ (Subject : Type) (ActAt : Sub` | {}  |
| `BareDiscrimination` | def | [L174](formal/Logos/CognitiveDiscrimination.lean#L174) | `def BareDiscrimination (Discriminates : Subject → Prop → Prop → Prop) (s : Subje` | {Subject}  |
| `CognitiveContrastPrinciple` | def | [L271](formal/Logos/CognitiveDiscrimination.lean#L271) | `def CognitiveContrastPrinciple (Subject : Type) (ActAt : Subject → Prop → Prop) ` | {}  |
| `CognitiveUptakePrinciple` | def | [L278](formal/Logos/CognitiveDiscrimination.lean#L278) | `def CognitiveUptakePrinciple (Subject : Type) (MeansAt : Subject → Prop → Prop) ` | {}  |
| `Consideration` | def | [L106](formal/Logos/CognitiveDiscrimination.lean#L106) | `def Consideration (s : Subject) (p : Prop) : Prop` | {Means, Subject}  |
| `ContentAwareness` | def | [L85](formal/Logos/CognitiveDiscrimination.lean#L85) | `def ContentAwareness (s : Subject) (p : Prop) : Prop` | {Means, Subject}  |
| `ContentDiscrimination` | def | [L121](formal/Logos/CognitiveDiscrimination.lean#L121) | `def ContentDiscrimination (Subject : Type) (Discriminates : Subject → Prop → Pro` | {}  |
| `ContentIndividuation` | def | [L74](formal/Logos/CognitiveDiscrimination.lean#L74) | `def ContentIndividuation (p : Prop) : Prop` | {}  |
| `ContentRepresentation` | def | [L353](formal/Logos/CognitiveDiscrimination.lean#L353) | `def ContentRepresentation (Subject : Type) (Represents : Subject → Prop → Prop) ` | {}  |
| `CounterfactualAvailability` | def | [L135](formal/Logos/CognitiveDiscrimination.lean#L135) | `def CounterfactualAvailability (Subject : Type) (CanEntertain : Subject → Prop →` | {}  |
| `CounterfactualConsideration` | def | [L192](formal/Logos/CognitiveDiscrimination.lean#L192) | `def CounterfactualConsideration (Considers : Subject → Prop → Prop) (s : Subject` | {Means, Subject}  |
| `D1_discrimination_not_entails_choice` | theorem | [L207](formal/Logos/CognitiveDiscrimination.lean#L207) | `theorem D1_discrimination_not_entails_choice : ∃ (Subject : Type) (s : Subject) ` | {}  |
| `D2_discrimination_not_entails_meaning` | theorem | [L216](formal/Logos/CognitiveDiscrimination.lean#L216) | `theorem D2_discrimination_not_entails_meaning : ∃ (Subject : Type) (s : Subject)` | {}  |
| `D3_discrimination_present_without_choice_or_freewill` | theorem | [L226](formal/Logos/CognitiveDiscrimination.lean#L226) | `theorem D3_discrimination_present_without_choice_or_freewill : ∃ (Subject : Type` | {}  |
| `D4_act_not_derives_discrimination` | theorem | [L246](formal/Logos/CognitiveDiscrimination.lean#L246) | `theorem D4_act_not_derives_discrimination : ∃ (Subject : Type) (s : Subject) (p ` | {}  |
| `DecomposedMeans` | def | [L361](formal/Logos/CognitiveDiscrimination.lean#L361) | `def DecomposedMeans (Subject : Type) (Represents Affirms : Subject → Prop → Prop` | {}  |
| `Entertainment` | def | [L113](formal/Logos/CognitiveDiscrimination.lean#L113) | `def Entertainment (s : Subject) (p : Prop) : Prop` | {Means, Subject}  |
| `IntentionalAffirmation` | def | [L357](formal/Logos/CognitiveDiscrimination.lean#L357) | `def IntentionalAffirmation (Subject : Type) (Affirms : Subject → Prop → Prop) (s` | {}  |
| `Level1_ObjectiveIncompatibility` | def | [L438](formal/Logos/CognitiveDiscrimination.lean#L438) | `def Level1_ObjectiveIncompatibility (p q : Prop) : Prop` | {}  |
| `Level2_CognitiveDistinction` | def | [L441](formal/Logos/CognitiveDiscrimination.lean#L441) | `def Level2_CognitiveDistinction (Subject : Type) (Discriminates : Subject → Prop` | {}  |
| `Level3_AlternativeRepresentation` | def | [L445](formal/Logos/CognitiveDiscrimination.lean#L445) | `def Level3_AlternativeRepresentation (Subject : Type) (Represents : Subject → Pr` | {}  |
| `Level4_CoMeaning` | def | [L449](formal/Logos/CognitiveDiscrimination.lean#L449) | `def Level4_CoMeaning (Subject : Type) (MeansAt : Subject → Prop → Prop) (s : Sub` | {}  |
| `Level5_Choice` | def | [L453](formal/Logos/CognitiveDiscrimination.lean#L453) | `def Level5_Choice (Subject : Type) (ChoosesAt : Subject → Prop → Prop → Prop) (s` | {}  |
| `Level6_FreeWill` | def | [L457](formal/Logos/CognitiveDiscrimination.lean#L457) | `def Level6_FreeWill (Subject : Type) (ChoosesAt : Subject → Prop → Prop → Prop) ` | {}  |
| `Level7_LibertarianFreedom` | def | [L461](formal/Logos/CognitiveDiscrimination.lean#L461) | `def Level7_LibertarianFreedom (Subject : Type) (CausesAt : Subject → Prop → Prop` | {}  |
| `MonadicIntentionalFrame` | structure | [L406](formal/Logos/CognitiveDiscrimination.lean#L406) | `structure MonadicIntentionalFrame where` | —  |
| `ObjectiveDistinction` | def | [L179](formal/Logos/CognitiveDiscrimination.lean#L179) | `def ObjectiveDistinction (p q : Prop) : Prop` | {}  |
| `PropIdentity` | def | [L67](formal/Logos/CognitiveDiscrimination.lean#L67) | `def PropIdentity (p : Prop) : Prop` | {}  |
| `RecognitionOfDifference` | def | [L182](formal/Logos/CognitiveDiscrimination.lean#L182) | `def RecognitionOfDifference (Discriminates : Subject → Prop → Prop → Prop) (s : ` | {Subject}  |
| `Representation` | def | [L92](formal/Logos/CognitiveDiscrimination.lean#L92) | `def Representation (s : Subject) (p : Prop) : Prop` | {Means, Subject}  |
| `RepresentationalSeparation` | def | [L197](formal/Logos/CognitiveDiscrimination.lean#L197) | `def RepresentationalSeparation (Represents : Subject → Prop → Prop) (s : Subject` | {Subject}  |
| `affirmation_not_implies_representation` | theorem | [L376](formal/Logos/CognitiveDiscrimination.lean#L376) | `theorem affirmation_not_implies_representation : ∃ (Subject : Type) (s : Subject` | {}  |
| `discrimination_equiv_intentional_distinction` | theorem | [L561](formal/Logos/CognitiveDiscrimination.lean#L561) | `theorem discrimination_equiv_intentional_distinction (D1 D2 : Subject → Prop → P` | {Subject}  |
| `horn_local_decomposition_blind_to_second_horn` | theorem | [L385](formal/Logos/CognitiveDiscrimination.lean#L385) | `theorem horn_local_decomposition_blind_to_second_horn : ∃ (Subject : Type) (s : ` | {}  |
| `level1_not_implies_level2` | theorem | [L476](formal/Logos/CognitiveDiscrimination.lean#L476) | `theorem level1_not_implies_level2 : ∃ (p q : Prop) (Subject : Type) (s : Subject` | {}  |
| `level2_not_implies_level3` | theorem | [L486](formal/Logos/CognitiveDiscrimination.lean#L486) | `theorem level2_not_implies_level3 : ∃ (Subject : Type) (s : Subject) (p q : Prop` | {}  |
| `level3_not_implies_level4` | theorem | [L500](formal/Logos/CognitiveDiscrimination.lean#L500) | `theorem level3_not_implies_level4 : ∃ (Subject : Type) (s : Subject) (p q : Prop` | {}  |
| `level4_not_implies_level5` | theorem | [L513](formal/Logos/CognitiveDiscrimination.lean#L513) | `theorem level4_not_implies_level5 : ∃ (Subject : Type) (s : Subject) (p q : Prop` | {}  |
| `level5_local_choice_not_implies_global_freewill` | theorem | [L525](formal/Logos/CognitiveDiscrimination.lean#L525) | `theorem level5_local_choice_not_implies_global_freewill : ∃ (Subject : Type) (s ` | {}  |
| `level6_freewill_not_implies_libertarian_freedom` | theorem | [L534](formal/Logos/CognitiveDiscrimination.lean#L534) | `theorem level6_freewill_not_implies_libertarian_freedom : ∃ (Subject : Type) (s ` | {}  |
| `means_iff_aboutness` | theorem | [L101](formal/Logos/CognitiveDiscrimination.lean#L101) | `theorem means_iff_aboutness (s : Subject) (p : Prop) : Means s p ↔ Aboutness s p` | {Means, Subject}  |
| `means_iff_awareness` | theorem | [L87](formal/Logos/CognitiveDiscrimination.lean#L87) | `theorem means_iff_awareness (s : Subject) (p : Prop) : Means s p ↔ ContentAwaren` | {Means, Subject}  |
| `means_iff_consideration` | theorem | [L108](formal/Logos/CognitiveDiscrimination.lean#L108) | `theorem means_iff_consideration (s : Subject) (p : Prop) : Means s p ↔ Considera` | {Means, Subject}  |
| `means_iff_entertainment` | theorem | [L115](formal/Logos/CognitiveDiscrimination.lean#L115) | `theorem means_iff_entertainment (s : Subject) (p : Prop) : Means s p ↔ Entertain` | {Means, Subject}  |
| `means_iff_representation` | theorem | [L94](formal/Logos/CognitiveDiscrimination.lean#L94) | `theorem means_iff_representation (s : Subject) (p : Prop) : Means s p ↔ Represen` | {Means, Subject}  |
| `means_implies_identity` | theorem | [L69](formal/Logos/CognitiveDiscrimination.lean#L69) | `theorem means_implies_identity (s : Subject) (p : Prop) (_h : Means s p) : PropI` | {Means, Subject}  |
| `means_implies_individuation` | theorem | [L77](formal/Logos/CognitiveDiscrimination.lean#L77) | `theorem means_implies_individuation (s : Subject) (p : Prop) (_h : Means s p) : ` | {Means, Subject, CL}  |
| `means_not_implies_alternative_awareness` | theorem | [L153](formal/Logos/CognitiveDiscrimination.lean#L153) | `theorem means_not_implies_alternative_awareness : ∃ (Subject : Type) (s : Subjec` | {}  |
| `means_not_implies_counterfactual_availability` | theorem | [L139](formal/Logos/CognitiveDiscrimination.lean#L139) | `theorem means_not_implies_counterfactual_availability : ∃ (Subject : Type) (s : ` | {}  |
| `means_not_implies_discrimination` | theorem | [L125](formal/Logos/CognitiveDiscrimination.lean#L125) | `theorem means_not_implies_discrimination : ∃ (Subject : Type) (s : Subject) (p :` | {}  |
| `recognition_of_incompatibility_requires_alternative_awareness` | theorem | [L568](formal/Logos/CognitiveDiscrimination.lean#L568) | `theorem recognition_of_incompatibility_requires_alternative_awareness (s : Subje` | {Means, Subject}  |
| `representation_not_implies_affirmation` | theorem | [L368](formal/Logos/CognitiveDiscrimination.lean#L368) | `theorem representation_not_implies_affirmation : ∃ (Subject : Type) (s : Subject` | {}  |
| `subprinciples_derive_missing_cognitive_horn` | theorem | [L285](formal/Logos/CognitiveDiscrimination.lean#L285) | `theorem subprinciples_derive_missing_cognitive_horn (Subject : Type) (ActAt : Su` | {}  |
| `unary_intentional_collapse` | theorem | [L414](formal/Logos/CognitiveDiscrimination.lean#L414) | `theorem unary_intentional_collapse (F : MonadicIntentionalFrame) (p : Prop) (hp ` | {}  |

### `Logos.CognitiveToAgencyFrontier`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `BilateralModalFreedom` | def | [L357](formal/Logos/CognitiveToAgencyFrontier.lean#L357) | `def BilateralModalFreedom (Subject : Type) (s : Subject) (p q : Prop) (CanAct : ` | {}  |
| `FineCognitiveSubject` | structure | [L44](formal/Logos/CognitiveToAgencyFrontier.lean#L44) | `structure FineCognitiveSubject (Subject : Type) where` | —  |
| `LibertarianFreedom` | def | [L362](formal/Logos/CognitiveToAgencyFrontier.lean#L362) | `def LibertarianFreedom (Subject : Type) (s : Subject) (p q : Prop) (CanAct : Sub` | {}  |
| `ReductioProgression` | structure | [L67](formal/Logos/CognitiveToAgencyFrontier.lean#L67) | `structure ReductioProgression (Subject : Type) (CS : FineCognitiveSubject Subjec` | —  |
| `Settlement1` | def | [L91](formal/Logos/CognitiveToAgencyFrontier.lean#L91) | `def Settlement1 (Subject : Type) (CS : FineCognitiveSubject Subject) (s : Subjec` | {}  |
| `Settlement2` | def | [L98](formal/Logos/CognitiveToAgencyFrontier.lean#L98) | `def Settlement2 (Subject : Type) (CS : FineCognitiveSubject Subject) (s : Subjec` | {}  |
| `Settlement3` | def | [L105](formal/Logos/CognitiveToAgencyFrontier.lean#L105) | `def Settlement3 (Subject : Type) (CS : FineCognitiveSubject Subject) (MeansAt : ` | {}  |
| `Settlement4` | def | [L112](formal/Logos/CognitiveToAgencyFrontier.lean#L112) | `def Settlement4 (Subject State : Type) (CS : FineCognitiveSubject Subject) (Mean` | {}  |
| `Settlement5` | def | [L122](formal/Logos/CognitiveToAgencyFrontier.lean#L122) | `def Settlement5 (Subject State : Type) (CS : FineCognitiveSubject Subject) (Mean` | {}  |
| `model_M13_dual_consideration_without_evaluation` | theorem | [L210](formal/Logos/CognitiveToAgencyFrontier.lean#L210) | `theorem model_M13_dual_consideration_without_evaluation : ∃ (Subject : Type) (CS` | {}  |
| `model_M14_evaluation_without_commitment` | theorem | [L234](formal/Logos/CognitiveToAgencyFrontier.lean#L234) | `theorem model_M14_evaluation_without_commitment : ∃ (Subject : Type) (CS : FineC` | {}  |
| `model_M15_settlement_without_choice` | theorem | [L260](formal/Logos/CognitiveToAgencyFrontier.lean#L260) | `theorem model_M15_settlement_without_choice : ∃ (Subject : Type) (CS : FineCogni` | {}  |
| `model_M16_deterministic_settlement` | theorem | [L288](formal/Logos/CognitiveToAgencyFrontier.lean#L288) | `theorem model_M16_deterministic_settlement : ∃ (DeliberativeState : Type) (Step ` | {}  |
| `model_M17_compatibilist_choice` | theorem | [L319](formal/Logos/CognitiveToAgencyFrontier.lean#L319) | `theorem model_M17_compatibilist_choice : ∃ (DeliberativeState : Type) (Step : De` | {}  |
| `model_M18_agent_causal_settlement` | theorem | [L337](formal/Logos/CognitiveToAgencyFrontier.lean#L337) | `theorem model_M18_agent_causal_settlement : ∃ (DeliberativeState : Type) (Subjec` | {}  |
| `reductio_cannot_collapse_to_one_horn` | theorem | [L146](formal/Logos/CognitiveToAgencyFrontier.lean#L146) | `theorem reductio_cannot_collapse_to_one_horn (Subject : Type) (CS : FineCognitiv` | {}  |
| `reductio_frontier_status` | theorem | [L369](formal/Logos/CognitiveToAgencyFrontier.lean#L369) | `theorem reductio_frontier_status (Subject : Type) (CS : FineCognitiveSubject Sub` | {}  |
| `reductio_induces_asymmetric_status_transition` | theorem | [L76](formal/Logos/CognitiveToAgencyFrontier.lean#L76) | `theorem reductio_induces_asymmetric_status_transition (Subject : Type) (CS : Fin` | {}  |
| `reductio_necessarily_asymmetric` | theorem | [L158](formal/Logos/CognitiveToAgencyFrontier.lean#L158) | `theorem reductio_necessarily_asymmetric (Subject : Type) (CS : FineCognitiveSubj` | {}  |
| `reductio_proves_settlement_1` | theorem | [L131](formal/Logos/CognitiveToAgencyFrontier.lean#L131) | `theorem reductio_proves_settlement_1 (Subject : Type) (CS : FineCognitiveSubject` | {}  |
| `settlement_1_does_not_imply_settlement_3` | theorem | [L166](formal/Logos/CognitiveToAgencyFrontier.lean#L166) | `theorem settlement_1_does_not_imply_settlement_3 : ∃ (Subject : Type) (CS : Fine` | {}  |

### `Logos.ConditionalTheology`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `CreationStructure` | structure | [L412](formal/Logos/ConditionalTheology.lean#L412) | `structure CreationStructure (Subj : Type) (Ent : Type) where` | —  |
| `IncarnationalStructure` | structure | [L369](formal/Logos/ConditionalTheology.lean#L369) | `structure IncarnationalStructure (Subj : Type) (Nature : Type) (HasNature : Subj` | —  |
| `InferenceStatus` | inductive | [L443](formal/Logos/ConditionalTheology.lean#L443) | `inductive InferenceStatus` | —  |
| `agency_closure_act_to_chooses` | theorem | [L56](formal/Logos/ConditionalTheology.lean#L56) | `theorem agency_closure_act_to_chooses (s : Subject) (p : Prop) (hAct : Act s p) ` | {AxIntentionalChoice, Initiates, Means, State, Subject}  |
| `agency_closure_act_to_freeSubject` | theorem | [L65](formal/Logos/ConditionalTheology.lean#L65) | `theorem agency_closure_act_to_freeSubject (s : Subject) (p : Prop) (hAct : Act s` | {AxIntentionalChoice, Initiates, Means, State, Subject}  |
| `agency_closure_act_to_freewill` | theorem | [L60](formal/Logos/ConditionalTheology.lean#L60) | `theorem agency_closure_act_to_freewill (s : Subject) (p : Prop) (hAct : Act s p)` | {AxIntentionalChoice, Initiates, Means, State, Subject}  |
| `agency_closure_act_to_intentionalSubject` | theorem | [L69](formal/Logos/ConditionalTheology.lean#L69) | `theorem agency_closure_act_to_intentionalSubject (s : Subject) (p : Prop) (hAct ` | {Initiates, Means, State, Subject}  |
| `freewill_not_entails_necessity` | theorem | [L154](formal/Logos/ConditionalTheology.lean#L154) | `theorem freewill_not_entails_necessity : ∃ (Subj : Type) (Chooses : Subj → Prop ` | {}  |
| `freewill_not_entails_normativity` | theorem | [L100](formal/Logos/ConditionalTheology.lean#L100) | `theorem freewill_not_entails_normativity : ∃ (Subj : Type) (Chooses : Subj → Pro` | {}  |
| `freewill_not_entails_persistence` | theorem | [L145](formal/Logos/ConditionalTheology.lean#L145) | `theorem freewill_not_entails_persistence : ∃ (Subj : Type) (Chooses : Subj → Pro` | {}  |
| `freewill_not_entails_rationality` | theorem | [L89](formal/Logos/ConditionalTheology.lean#L89) | `theorem freewill_not_entails_rationality : ∃ (Subj : Type) (Chooses : Subj → Pro` | {}  |
| `freewill_not_entails_reflexive_subjectivity` | theorem | [L127](formal/Logos/ConditionalTheology.lean#L127) | `theorem freewill_not_entails_reflexive_subjectivity : ∃ (Subj : Type) (Chooses :` | {}  |
| `freewill_not_entails_relationality` | theorem | [L136](formal/Logos/ConditionalTheology.lean#L136) | `theorem freewill_not_entails_relationality : ∃ (Subj : Type) (Chooses : Subj → P` | {}  |
| `freewill_not_entails_teleology` | theorem | [L118](formal/Logos/ConditionalTheology.lean#L118) | `theorem freewill_not_entails_teleology : ∃ (Subj : Type) (Chooses : Subj → Prop ` | {}  |
| `freewill_not_entails_value` | theorem | [L109](formal/Logos/ConditionalTheology.lean#L109) | `theorem freewill_not_entails_value : ∃ (Subj : Type) (Chooses : Subj → Prop → Pr` | {}  |
| `TrinitarianStructure` | structure | [L309](formal/Logos/ConditionalTheology.lean#L309) | `structure TrinitarianStructure (Subj : Type) (Ent : Type) where` | —  |
| `a14_not_eliminates_infinite_ground_chain` | theorem | [L184](formal/Logos/ConditionalTheology.lean#L184) | `theorem a14_not_eliminates_infinite_ground_chain : ∃ (Subj : Type) (Ent : Type) ` | —  |
| `a14_not_entails_plurality` | theorem | [L258](formal/Logos/ConditionalTheology.lean#L258) | `theorem a14_not_entails_plurality : ∃ (Subj : Type) (Chooses : Subj → Prop → Pro` | —  |
| `a14_plus_ultimate_ground_not_entails_personal_ultimate_ground` | theorem | [L230](formal/Logos/ConditionalTheology.lean#L230) | `theorem a14_plus_ultimate_ground_not_entails_personal_ultimate_ground : ∃ (Subj ` | —  |
| `edge_Act_to_Chooses` | def | [L452](formal/Logos/ConditionalTheology.lean#L452) | `def edge_Act_to_Chooses : InferenceStatus` | —  |
| `edge_Chooses_to_FreeWill` | def | [L453](formal/Logos/ConditionalTheology.lean#L453) | `def edge_Chooses_to_FreeWill : InferenceStatus` | —  |
| `edge_Creation_to_Incarnation` | def | [L463](formal/Logos/ConditionalTheology.lean#L463) | `def edge_Creation_to_Incarnation : InferenceStatus` | —  |
| `edge_DivineGround_to_Creation` | def | [L462](formal/Logos/ConditionalTheology.lean#L462) | `def edge_DivineGround_to_Creation : InferenceStatus` | —  |
| `edge_FreeWill_to_Rationality` | def | [L454](formal/Logos/ConditionalTheology.lean#L454) | `def edge_FreeWill_to_Rationality : InferenceStatus` | —  |
| `edge_Love_to_Trinity` | def | [L461](formal/Logos/ConditionalTheology.lean#L461) | `def edge_Love_to_Trinity : InferenceStatus` | —  |
| `edge_NecessaryGround_to_UltimateGround` | def | [L457](formal/Logos/ConditionalTheology.lean#L457) | `def edge_NecessaryGround_to_UltimateGround : InferenceStatus` | —  |
| `edge_NecessaryTruth_to_SomeGround` | def | [L455](formal/Logos/ConditionalTheology.lean#L455) | `def edge_NecessaryTruth_to_SomeGround : InferenceStatus` | —  |
| `edge_PersonalGround_to_Plurality` | def | [L459](formal/Logos/ConditionalTheology.lean#L459) | `def edge_PersonalGround_to_Plurality : InferenceStatus` | —  |
| `edge_Plurality_to_Love` | def | [L460](formal/Logos/ConditionalTheology.lean#L460) | `def edge_Plurality_to_Love : InferenceStatus` | —  |
| `edge_SomeGround_to_NecessaryGround` | def | [L456](formal/Logos/ConditionalTheology.lean#L456) | `def edge_SomeGround_to_NecessaryGround : InferenceStatus` | —  |
| `edge_UltimateGround_to_PersonalGround` | def | [L458](formal/Logos/ConditionalTheology.lean#L458) | `def edge_UltimateGround_to_PersonalGround : InferenceStatus` | —  |
| `free_agency_and_plurality_not_entails_love` | theorem | [L283](formal/Logos/ConditionalTheology.lean#L283) | `theorem free_agency_and_plurality_not_entails_love : ∃ (Subj : Type) (Chooses : ` | —  |
| `free_agency_not_entails_ultimate_ground` | theorem | [L202](formal/Logos/ConditionalTheology.lean#L202) | `theorem free_agency_not_entails_ultimate_ground : ∃ (Subj : Type) (Ent : Type) (` | —  |
| `necessary_ground_not_entails_contingent_creation` | theorem | [L421](formal/Logos/ConditionalTheology.lean#L421) | `theorem necessary_ground_not_entails_contingent_creation : ∃ (Subj : Type) (Ent ` | —  |
| `preceding_theory_not_entails_incarnation` | theorem | [L381](formal/Logos/ConditionalTheology.lean#L381) | `theorem preceding_theory_not_entails_incarnation : ∃ (Subj : Type) (Nature : Typ` | —  |
| `preceding_theory_not_entails_trinity` | theorem | [L330](formal/Logos/ConditionalTheology.lean#L330) | `theorem preceding_theory_not_entails_trinity : ∃ (Subj : Type) (Ent : Type) (Cho` | —  |
| `theological_dependency_ledger` | theorem | [L468](formal/Logos/ConditionalTheology.lean#L468) | `theorem theological_dependency_ledger : edge_Act_to_Chooses = InferenceStatus.PR` | —  |

### `Logos.ConstitutiveNormativeFreeWill`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `ConstitutiveDeonticTruth` | structure | [L181](formal/Logos/ConstitutiveNormativeFreeWill.lean#L181) | `structure ConstitutiveDeonticTruth` | —  |
| `ConstitutiveNormativeTruth` | structure | [L67](formal/Logos/ConstitutiveNormativeFreeWill.lean#L67) | `structure ConstitutiveNormativeTruth (World : Type) where` | —  |
| `DescriptiveTruth` | def | [L49](formal/Logos/ConstitutiveNormativeFreeWill.lean#L49) | `def DescriptiveTruth (p : Prop) : Prop` | {}  |
| `NecessaryConstitutiveNormativity` | def | [L152](formal/Logos/ConstitutiveNormativeFreeWill.lean#L152) | `def NecessaryConstitutiveNormativity (World : Type) : Prop` | {Means, Subject}  |
| `ObjectiveValue` | structure | [L54](formal/Logos/ConstitutiveNormativeFreeWill.lean#L54) | `structure ObjectiveValue (World : Type) (_w : World) where` | —  |
| `T1_constitutive_normative_truth_implies_agency` | theorem | [L114](formal/Logos/ConstitutiveNormativeFreeWill.lean#L114) | `theorem T1_constitutive_normative_truth_implies_agency {World : Type} (cnt : Con` | {Means, Subject}  |
| `T2_constitutive_normative_truth_implies_alternative` | theorem | [L125](formal/Logos/ConstitutiveNormativeFreeWill.lean#L125) | `theorem T2_constitutive_normative_truth_implies_alternative {World : Type} (cnt ` | {Means, Subject}  |
| `T3_constitutive_normative_truth_implies_chooses` | theorem | [L136](formal/Logos/ConstitutiveNormativeFreeWill.lean#L136) | `theorem T3_constitutive_normative_truth_implies_chooses {World : Type} (cnt : Co` | {Means, Subject}  |
| `T4_constitutive_normative_truth_implies_free_will` | theorem | [L144](formal/Logos/ConstitutiveNormativeFreeWill.lean#L144) | `theorem T4_constitutive_normative_truth_implies_free_will {World : Type} (cnt : ` | {Means, Subject}  |
| `T5_necessary_constitutive_normativity_implies_necessary_free_will` | theorem | [L158](formal/Logos/ConstitutiveNormativeFreeWill.lean#L158) | `theorem T5_necessary_constitutive_normativity_implies_necessary_free_will {World` | {Means, Subject}  |
| `T6_necessary_deontic_truth_implies_necessary_genuine_free_subject` | theorem | [L204](formal/Logos/ConstitutiveNormativeFreeWill.lean#L204) | `theorem T6_necessary_deontic_truth_implies_necessary_genuine_free_subject {World` | {Means, Subject}  |
| `T7_necessary_deontic_truth_implies_not_d3` | theorem | [L218](formal/Logos/ConstitutiveNormativeFreeWill.lean#L218) | `theorem T7_necessary_deontic_truth_implies_not_d3 {World PriorState FutureState ` | {Means, Subject}  |
| `cm22_impersonal_world_satisfies_objective_value` | def | [L91](formal/Logos/ConstitutiveNormativeFreeWill.lean#L91) | `def cm22_impersonal_world_satisfies_objective_value {World : Type} (w : World) :` | {}  |
| `cm22_impersonal_world_strictly_fails_constitutive_normativity` | theorem | [L95](formal/Logos/ConstitutiveNormativeFreeWill.lean#L95) | `theorem cm22_impersonal_world_strictly_fails_constitutive_normativity {World : T` | {Means, Subject}  |
| `constitutive_deontic_truth_implies_genuine_chooses` | theorem | [L193](formal/Logos/ConstitutiveNormativeFreeWill.lean#L193) | `theorem constitutive_deontic_truth_implies_genuine_chooses {World PriorState Fut` | {Means, Subject}  |
| `hostile_model_outcome_1_compatibilist_satisfies_core_freedom_under_d3` | theorem | [L245](formal/Logos/ConstitutiveNormativeFreeWill.lean#L245) | `theorem hostile_model_outcome_1_compatibilist_satisfies_core_freedom_under_d3 {W` | {Means, Subject}  |
| `hostile_model_outcome_2_d3_contradicts_constitutive_deontic_truth` | theorem | [L257](formal/Logos/ConstitutiveNormativeFreeWill.lean#L257) | `theorem hostile_model_outcome_2_d3_contradicts_constitutive_deontic_truth {World` | {Means, Subject}  |
| `retorsion_establishes_normative_truth_exists` | theorem | [L279](formal/Logos/ConstitutiveNormativeFreeWill.lean#L279) | `theorem retorsion_establishes_normative_truth_exists (ctx : Logos.NormativeTruth` | {CL}  |
| `retorsion_pragmatic_address_excludes_impersonal_model` | theorem | [L284](formal/Logos/ConstitutiveNormativeFreeWill.lean#L284) | `theorem retorsion_pragmatic_address_excludes_impersonal_model (dom : StrongNorma` | {Subject}  |

### `Logos.ContextualDevelopment`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `ConceptThreshold` | inductive | [L207](formal/Logos/ContextualDevelopment.lean#L207) | `inductive ConceptThreshold` | —  |
| `CrossContextDevelopment` | def | [L175](formal/Logos/ContextualDevelopment.lean#L175) | `def CrossContextDevelopment (c1 c2 : DeductiveContext) (GammaCore : Prop) (Devel` | {}  |
| `DeductiveContext` | inductive | [L54](formal/Logos/ContextualDevelopment.lean#L54) | `inductive DeductiveContext` | —  |
| `EntryLayerOf` | def | [L216](formal/Logos/ContextualDevelopment.lean#L216) | `def EntryLayerOf (th : ConceptThreshold) : DependencyLayer` | {}  |
| `ProofDevelopment` | def | [L65](formal/Logos/ContextualDevelopment.lean#L65) | `def ProofDevelopment (c : DeductiveContext) (GammaCore : Prop) (DevelopsAt : Ded` | {}  |
| `ProofPerformance` | def | [L61](formal/Logos/ContextualDevelopment.lean#L61) | `def ProofPerformance (Subject : Type) (s : Subject) (c : DeductiveContext) (Perf` | {}  |
| `cross_context_development_implies_core` | theorem | [L182](formal/Logos/ContextualDevelopment.lean#L182) | `theorem cross_context_development_implies_core (c1 c2 : DeductiveContext) (Gamma` | {}  |
| `development_not_entails_freewill` | theorem | [L82](formal/Logos/ContextualDevelopment.lean#L82) | `theorem development_not_entails_freewill : ∃ (Subject : Type) (s : Subject) (c :` | {}  |
| `distinct_contexts_same_subject` | theorem | [L100](formal/Logos/ContextualDevelopment.lean#L100) | `theorem distinct_contexts_same_subject : ∃ (Subject : Type) (s : Subject) (c1 c2` | {}  |
| `model_M_D_consistent` | theorem | [L122](formal/Logos/ContextualDevelopment.lean#L122) | `theorem model_M_D_consistent : ∃ (c : DeductiveContext) (Subject : Type) (s : Su` | {}  |
| `model_M_F_consistent` | theorem | [L144](formal/Logos/ContextualDevelopment.lean#L144) | `theorem model_M_F_consistent : ∃ (c : DeductiveContext) (Subject : Type) (s : Su` | {}  |
| `model_M_N_consistent` | theorem | [L133](formal/Logos/ContextualDevelopment.lean#L133) | `theorem model_M_N_consistent : ∃ (c : DeductiveContext) (Subject : Type) (s : Su` | {}  |
| `model_M_S_consistent` | theorem | [L155](formal/Logos/ContextualDevelopment.lean#L155) | `theorem model_M_S_consistent : ∃ (c : DeductiveContext) (Subject : Type) (HasAge` | {}  |
| `performance_not_entails_freewill` | theorem | [L74](formal/Logos/ContextualDevelopment.lean#L74) | `theorem performance_not_entails_freewill : ∃ (Subject : Type) (s : Subject) (c :` | {}  |
| `presence_not_entails_free_selection` | theorem | [L90](formal/Logos/ContextualDevelopment.lean#L90) | `theorem presence_not_entails_free_selection : ∃ (Subject : Type) (s : Subject) (` | {}  |
| `threshold_audit_correct` | theorem | [L228](formal/Logos/ContextualDevelopment.lean#L228) | `theorem threshold_audit_correct : CoreGammaLayer (EntryLayerOf ConceptThreshold.` | {}  |

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

### `Logos.DeepContrastiveFrontier`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Collapse` | def | [L136](formal/Logos/DeepContrastiveFrontier.lean#L136) | `def Collapse (M : ContrastiveModel) : ContrastiveModel where Subject` | {}  |
| `CompatibleIntensional` | def | [L73](formal/Logos/DeepContrastiveFrontier.lean#L73) | `def CompatibleIntensional (p q : WorldProp) : Prop` | {}  |
| `ContrastiveModel` | structure | [L126](formal/Logos/DeepContrastiveFrontier.lean#L126) | `structure ContrastiveModel where` | —  |
| `ExistentialA14` | def | [L197](formal/Logos/DeepContrastiveFrontier.lean#L197) | `def ExistentialA14 (Subject : Type) (ActAt : Subject → Prop → Prop) (ChoosesAt :` | {}  |
| `F1bStatement` | def | [L202](formal/Logos/DeepContrastiveFrontier.lean#L202) | `def F1bStatement (Subject : Type) (ActAt : Subject → Prop → Prop) (FreeWillAt : ` | {}  |
| `F1b_is_relatively_minimal` | theorem | [L235](formal/Logos/DeepContrastiveFrontier.lean#L235) | `theorem F1b_is_relatively_minimal {Subject : Type} {ActAt : Subject → Prop → Pro` | {}  |
| `IncompatibleIntensional` | def | [L76](formal/Logos/DeepContrastiveFrontier.lean#L76) | `def IncompatibleIntensional (p q : WorldProp) : Prop` | {}  |
| `IntentionalDecomposition` | structure | [L60](formal/Logos/DeepContrastiveFrontier.lean#L60) | `structure IntentionalDecomposition (Subject : Type) where` | —  |
| `M_existential_only` | def | [L263](formal/Logos/DeepContrastiveFrontier.lean#L263) | `def M_existential_only : TwoAgentUniverse where Subject` | {}  |
| `M_existential_only_refutes_universal` | theorem | [L278](formal/Logos/DeepContrastiveFrontier.lean#L278) | `theorem M_existential_only_refutes_universal : ¬ UniversalA14 M_existential_only` | {}  |
| `M_existential_only_validates_existential` | theorem | [L272](formal/Logos/DeepContrastiveFrontier.lean#L272) | `theorem M_existential_only_validates_existential : ExistentialA14 M_existential_` | {}  |
| `TwoAgentUniverse` | structure | [L254](formal/Logos/DeepContrastiveFrontier.lean#L254) | `structure TwoAgentUniverse where` | —  |
| `UniversalA14` | def | [L192](formal/Logos/DeepContrastiveFrontier.lean#L192) | `def UniversalA14 (Subject : Type) (ActAt : Subject → Prop → Prop) (ChoosesAt : S` | {}  |
| `WorldProp` | def | [L71](formal/Logos/DeepContrastiveFrontier.lean#L71) | `def WorldProp` | {}  |
| `collapse_destroys_all_deliberation` | theorem | [L163](formal/Logos/DeepContrastiveFrontier.lean#L163) | `theorem collapse_destroys_all_deliberation (M : ContrastiveModel) (s : (Collapse` | {}  |
| `collapse_preserves_assertions` | theorem | [L149](formal/Logos/DeepContrastiveFrontier.lean#L149) | `theorem collapse_preserves_assertions (M : ContrastiveModel) (s : M.Subject) (p ` | {}  |
| `collapse_preserves_executive_choice` | theorem | [L155](formal/Logos/DeepContrastiveFrontier.lean#L155) | `theorem collapse_preserves_executive_choice (M : ContrastiveModel) (s : M.Subjec` | {}  |
| `contrastive_blind_invariance_refutes_freewill` | theorem | [L172](formal/Logos/DeepContrastiveFrontier.lean#L172) | `theorem contrastive_blind_invariance_refutes_freewill (M : ContrastiveModel) : ¬` | {}  |
| `diagonal_freeAgency_without_freeWill_coherent` | theorem | [L333](formal/Logos/DeepContrastiveFrontier.lean#L333) | `theorem diagonal_freeAgency_without_freeWill_coherent : ∃ (Subject : Type) (s : ` | {}  |
| `diagonal_negative_choice_coherent` | theorem | [L318](formal/Logos/DeepContrastiveFrontier.lean#L318) | `theorem diagonal_negative_choice_coherent : ∃ (Subject : Type) (s : Subject) (p ` | {}  |
| `diagonal_positive_choice_not_forces_choice` | theorem | [L302](formal/Logos/DeepContrastiveFrontier.lean#L302) | `theorem diagonal_positive_choice_not_forces_choice : ∃ (Subject : Type) (s : Sub` | {}  |
| `discrimination_not_implies_incompatibility` | theorem | [L82](formal/Logos/DeepContrastiveFrontier.lean#L82) | `theorem discrimination_not_implies_incompatibility : ∃ (p q : WorldProp), p ≠ q ` | {}  |
| `exclusion_not_implies_deliberation` | theorem | [L97](formal/Logos/DeepContrastiveFrontier.lean#L97) | `theorem exclusion_not_implies_deliberation : ∃ (Subject : Type) (D : Intentional` | {CL}  |
| `existential_a14_iff_F1b` | theorem | [L217](formal/Logos/DeepContrastiveFrontier.lean#L217) | `theorem existential_a14_iff_F1b {Subject : Type} {ActAt : Subject → Prop → Prop}` | {}  |
| `freewill_not_implies_necessity` | theorem | [L374](formal/Logos/DeepContrastiveFrontier.lean#L374) | `theorem freewill_not_implies_necessity : ∃ (Subject : Type) (s : Subject) (FreeW` | {}  |
| `freewill_not_implies_person` | theorem | [L366](formal/Logos/DeepContrastiveFrontier.lean#L366) | `theorem freewill_not_implies_person : ∃ (Subject : Type) (s : Subject) (FreeWill` | {}  |
| `freewill_not_implies_ultimate_ground` | theorem | [L382](formal/Logos/DeepContrastiveFrontier.lean#L382) | `theorem freewill_not_implies_ultimate_ground : ∃ (Subject : Type) (s : Subject) ` | {}  |
| `layer_L1_refl` | theorem | [L67](formal/Logos/DeepContrastiveFrontier.lean#L67) | `theorem layer_L1_refl {Subject : Type} (D : IntentionalDecomposition Subject) (s` | {}  |
| `universal_a14_implies_existential` | theorem | [L207](formal/Logos/DeepContrastiveFrontier.lean#L207) | `theorem universal_a14_implies_existential {Subject : Type} {ActAt : Subject → Pr` | {}  |

### `Logos.DeepModalFrontier`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Alt1_Outcome` | def | [L104](formal/Logos/DeepModalFrontier.lean#L104) | `def Alt1_Outcome (World : Type) (OutcomeAt : World → Prop) (v u : World) : Prop` | {}  |
| `Alt2_Action` | def | [L107](formal/Logos/DeepModalFrontier.lean#L107) | `def Alt2_Action (World Subject : Type) (ActAt : World → Subject → Prop → Prop) (` | {}  |
| `Alt3_Volition` | def | [L111](formal/Logos/DeepModalFrontier.lean#L111) | `def Alt3_Volition (World Subject : Type) (WillsAt : World → Subject → Prop → Pro` | {}  |
| `Alt4_Counterfactual` | def | [L115](formal/Logos/DeepModalFrontier.lean#L115) | `def Alt4_Counterfactual (World Subject : Type) (ReasonsAt : World → Subject → Pr` | {}  |
| `Alt5_Agentive` | def | [L121](formal/Logos/DeepModalFrontier.lean#L121) | `def Alt5_Agentive (World Subject : Type) (IntentionalAt : World → Subject → Prop` | {}  |
| `Alt6_AgentCausal` | def | [L126](formal/Logos/DeepModalFrontier.lean#L126) | `def Alt6_AgentCausal (World Entity Subject : Type) (ExtCirc : World → Prop) (Rea` | {}  |
| `C0_not_entails_C1` | theorem | [L182](formal/Logos/DeepModalFrontier.lean#L182) | `theorem C0_not_entails_C1 : ∃ (World Subject : Type) (ReasonsAt : World → Subjec` | {CL}  |
| `C1_not_entails_C2` | theorem | [L202](formal/Logos/DeepModalFrontier.lean#L202) | `theorem C1_not_entails_C2 : ∃ (World Subject : Type) (ReasonsAt : World → Subjec` | {}  |
| `ExplainsChoiceNonDetermining` | def | [L349](formal/Logos/DeepModalFrontier.lean#L349) | `def ExplainsChoiceNonDetermining (World Subject : Type) (frame : KripkeFrame Wor` | {}  |
| `Level_C0_PrimitiveVariation` | def | [L149](formal/Logos/DeepModalFrontier.lean#L149) | `def Level_C0_PrimitiveVariation (World Subject : Type) (WillsAt : World → Subjec` | {}  |
| `Level_C1_NonDeterministic` | def | [L153](formal/Logos/DeepModalFrontier.lean#L153) | `def Level_C1_NonDeterministic (World Subject : Type) (ReasonsAt : World → Subjec` | {}  |
| `Level_C2_AgentAttributable` | def | [L158](formal/Logos/DeepModalFrontier.lean#L158) | `def Level_C2_AgentAttributable (World Subject : Type) (SettlesAt : World → Subje` | {}  |
| `Level_C3_AgentCausal` | def | [L163](formal/Logos/DeepModalFrontier.lean#L163) | `def Level_C3_AgentCausal (World Entity Subject : Type) (ExtCirc : World → Prop) ` | {}  |
| `Level_C4_ExplanatoryAgentCausal` | def | [L171](formal/Logos/DeepModalFrontier.lean#L171) | `def Level_C4_ExplanatoryAgentCausal (World Entity Subject : Type) (ExtCirc : Wor` | {}  |
| `ModalDifferencePrimitive` | structure | [L231](formal/Logos/DeepModalFrontier.lean#L231) | `structure ModalDifferencePrimitive (World Subject : Type)` | —  |
| `ModalFreeWillRigid` | def | [L62](formal/Logos/DeepModalFrontier.lean#L62) | `def ModalFreeWillRigid (World Subject : Type) (frame : KripkeFrame World) (actua` | {}  |
| `NonDeterministicVolition` | def | [L57](formal/Logos/DeepModalFrontier.lean#L57) | `def NonDeterministicVolition (World Subject : Type) (ReasonsAt : World → Subject` | {}  |
| `Omniscience_AllTruths` | def | [L313](formal/Logos/DeepModalFrontier.lean#L313) | `def Omniscience_AllTruths (World Subject : Type) (KnowsAt : World → Subject → Pr` | {}  |
| `Omniscience_Counterfactuals` | def | [L317](formal/Logos/DeepModalFrontier.lean#L317) | `def Omniscience_Counterfactuals (World Subject : Type) (KnowsCounterfactualAt : ` | {}  |
| `PSR_Level3_ActReason` | def | [L332](formal/Logos/DeepModalFrontier.lean#L332) | `def PSR_Level3_ActReason (World Subject : Type) (ReasonsAt : World → Subject → P` | {}  |
| `PSR_Level4_VolitionReason` | def | [L336](formal/Logos/DeepModalFrontier.lean#L336) | `def PSR_Level4_VolitionReason (World Subject : Type) (ReasonsAt : World → Subjec` | {}  |
| `PSR_Level6_DeterminingPSR` | def | [L340](formal/Logos/DeepModalFrontier.lean#L340) | `def PSR_Level6_DeterminingPSR (World Subject : Type) (ReasonsAt : World → Subjec` | {}  |
| `Rationality_R0` | def | [L272](formal/Logos/DeepModalFrontier.lean#L272) | `def Rationality_R0 (World Subject : Type) (ActAt : World → Subject → Prop → Prop` | {}  |
| `Rationality_R1` | def | [L275](formal/Logos/DeepModalFrontier.lean#L275) | `def Rationality_R1 (World Subject : Type) (ReasonsAt : World → Subject → Prop) (` | {}  |
| `Rationality_R4_Deliberative` | def | [L279](formal/Logos/DeepModalFrontier.lean#L279) | `def Rationality_R4_Deliberative (World Subject : Type) (ReasonsAt : World → Subj` | {}  |
| `Rationality_R5_OptimificCompulsion` | def | [L283](formal/Logos/DeepModalFrontier.lean#L283) | `def Rationality_R5_OptimificCompulsion (World Subject : Type) (BestReasonAt : Wo` | {}  |
| `S5UniversalFrame` | def | [L48](formal/Logos/DeepModalFrontier.lean#L48) | `def S5UniversalFrame (World : Type) : KripkeFrame World` | {}  |
| `UniqueBestAction` | def | [L292](formal/Logos/DeepModalFrontier.lean#L292) | `def UniqueBestAction (World Subject : Type) (BestReasonAt : World → Subject → Pr` | {}  |
| `modal_volition_iff_primitive_decomposition` | theorem | [L244](formal/Logos/DeepModalFrontier.lean#L244) | `theorem modal_volition_iff_primitive_decomposition (World Subject : Type) (frame` | {}  |
| `model_MC31_consistent` | theorem | [L386](formal/Logos/DeepModalFrontier.lean#L386) | `theorem model_MC31_consistent : ∃ (World Subject : Type) (frame : KripkeFrame Wo` | {}  |
| `model_MC32_consistent` | theorem | [L402](formal/Logos/DeepModalFrontier.lean#L402) | `theorem model_MC32_consistent : ∃ (World Subject : Type) (frame : KripkeFrame Wo` | {}  |
| `model_MC33_consistent` | theorem | [L418](formal/Logos/DeepModalFrontier.lean#L418) | `theorem model_MC33_consistent : ∃ (World Subject : Type) (frame : KripkeFrame Wo` | {}  |
| `model_MC34_consistent` | theorem | [L434](formal/Logos/DeepModalFrontier.lean#L434) | `theorem model_MC34_consistent : ∃ (World Subject : Type) (frame : KripkeFrame Wo` | {}  |
| `model_MC35_consistent` | theorem | [L447](formal/Logos/DeepModalFrontier.lean#L447) | `theorem model_MC35_consistent : ∃ (World Entity Subject : Type) (frame : KripkeF` | {}  |
| `model_MC36_consistent` | theorem | [L463](formal/Logos/DeepModalFrontier.lean#L463) | `theorem model_MC36_consistent : ∃ (World Entity Subject : Type) (frame : KripkeF` | {}  |
| `model_MC37_consistent` | theorem | [L481](formal/Logos/DeepModalFrontier.lean#L481) | `theorem model_MC37_consistent : ∃ (World Subject : Type) (frame : KripkeFrame Wo` | {CL}  |
| `model_MC38_consistent` | theorem | [L506](formal/Logos/DeepModalFrontier.lean#L506) | `theorem model_MC38_consistent : ∃ (World Subject : Type) (frame : KripkeFrame Wo` | {}  |
| `model_MC39_consistent` | theorem | [L518](formal/Logos/DeepModalFrontier.lean#L518) | `theorem model_MC39_consistent : ∃ (World Subject : Type) (WillsAt : World → Subj` | {}  |
| `model_MC40_consistent` | theorem | [L526](formal/Logos/DeepModalFrontier.lean#L526) | `theorem model_MC40_consistent : ∃ (World Entity Subject : Type) (ExtCirc : World` | {}  |
| `model_MC41_consistent` | theorem | [L545](formal/Logos/DeepModalFrontier.lean#L545) | `theorem model_MC41_consistent : ∃ (World Subject : Type) (QualStateAt : World → ` | {}  |
| `model_MC42_consistent` | theorem | [L557](formal/Logos/DeepModalFrontier.lean#L557) | `theorem model_MC42_consistent : ∃ (World Entity : Type) (RelToAllAt : World → En` | {}  |
| `model_MC43_consistent` | theorem | [L569](formal/Logos/DeepModalFrontier.lean#L569) | `theorem model_MC43_consistent : ∃ (World Subject : Type) (frame : KripkeFrame Wo` | {CL}  |
| `model_MC44_consistent` | theorem | [L595](formal/Logos/DeepModalFrontier.lean#L595) | `theorem model_MC44_consistent : ∃ (World Entity Subject : Type) (frame : KripkeF` | {}  |
| `model_MC45_consistent` | theorem | [L621](formal/Logos/DeepModalFrontier.lean#L621) | `theorem model_MC45_consistent : ∃ (World Entity Subject : Type) (frame : KripkeF` | {}  |
| `nondeterministic_not_entails_modal_freewill` | theorem | [L71](formal/Logos/DeepModalFrontier.lean#L71) | `theorem nondeterministic_not_entails_modal_freewill : ∃ (World Subject : Type) (` | {}  |
| `s5_frame_is_equivalence` | theorem | [L51](formal/Logos/DeepModalFrontier.lean#L51) | `theorem s5_frame_is_equivalence (World : Type) : (∀ w : World, (S5UniversalFrame` | {}  |
| `third_regime_consistent` | theorem | [L362](formal/Logos/DeepModalFrontier.lean#L362) | `theorem third_regime_consistent : ∃ (World Subject : Type) (frame : KripkeFrame ` | {}  |
| `unique_best_action_optimific_rationality_modal_collapse` | theorem | [L297](formal/Logos/DeepModalFrontier.lean#L297) | `theorem unique_best_action_optimific_rationality_modal_collapse (World Subject :` | {}  |

### `Logos.DefinitiveAgencyFrontier`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `AgentCausalFreeWill` | def | [L546](formal/Logos/DefinitiveAgencyFrontier.lean#L546) | `def AgentCausalFreeWill {Subj : Type} (CS : FineCognitiveSubject Subj) (ActRel :` | {}  |
| `AuthorialFreeWill` | def | [L541](formal/Logos/DefinitiveAgencyFrontier.lean#L541) | `def AuthorialFreeWill {Subj : Type} (CS : FineCognitiveSubject Subj) (SourceOf :` | {}  |
| `CognitiveFreeWill` | def | [L528](formal/Logos/DefinitiveAgencyFrontier.lean#L528) | `def CognitiveFreeWill {Subj : Type} (CS : FineCognitiveSubject Subj) (s : Subj) ` | {}  |
| `CompatibilistFreeWill` | def | [L536](formal/Logos/DefinitiveAgencyFrontier.lean#L536) | `def CompatibilistFreeWill {Subj : Type} (CS : FineCognitiveSubject Subj) (ActRel` | {}  |
| `LibertarianFreeWill` | def | [L551](formal/Logos/DefinitiveAgencyFrontier.lean#L551) | `def LibertarianFreeWill {Subj : Type} (CS : FineCognitiveSubject Subj) (ActRel :` | {}  |
| `ReasonResponsive` | def | [L428](formal/Logos/DefinitiveAgencyFrontier.lean#L428) | `def ReasonResponsive (Subj : Type) (ChoiceRel : Subj → Prop → Prop) (ReasonFor :` | {}  |
| `SincerityPrinciple` | def | [L195](formal/Logos/DefinitiveAgencyFrontier.lean#L195) | `def SincerityPrinciple (Subj : Type) (CS : FineCognitiveSubject Subj) (AssertsRe` | {}  |
| `T_uncommit` | def | [L647](formal/Logos/DefinitiveAgencyFrontier.lean#L647) | `def T_uncommit {Subj : Type} (CS : FineCognitiveSubject Subj) : FineCognitiveSub` | {}  |
| `VolitionalFreeWill` | def | [L532](formal/Logos/DefinitiveAgencyFrontier.lean#L532) | `def VolitionalFreeWill {Subj : Type} (CS : FineCognitiveSubject Subj) (s : Subj)` | {}  |
| `agent_causation_does_not_imply_reason_responsiveness` | theorem | [L447](formal/Logos/DefinitiveAgencyFrontier.lean#L447) | `theorem agent_causation_does_not_imply_reason_responsiveness : ∃ (Subj : Type) (` | {}  |
| `collapse_invariance_pre_commitment` | theorem | [L669](formal/Logos/DefinitiveAgencyFrontier.lean#L669) | `theorem collapse_invariance_pre_commitment {Subj : Type} (CS : FineCognitiveSubj` | {}  |
| `definitive_agency_frontier_synthesis` | theorem | [L753](formal/Logos/DefinitiveAgencyFrontier.lean#L753) | `theorem definitive_agency_frontier_synthesis {Subj : Type} (CS : FineCognitiveSu` | {}  |
| `delusion_of_agency_separation` | theorem | [L414](formal/Logos/DefinitiveAgencyFrontier.lean#L414) | `theorem delusion_of_agency_separation : ∃ (Subj : Type) (SelfAttr : Subj → Prop ` | {}  |
| `free_will_hierarchy_implications` | theorem | [L560](formal/Logos/DefinitiveAgencyFrontier.lean#L560) | `theorem free_will_hierarchy_implications {Subj : Type} (CS : FineCognitiveSubjec` | {}  |
| `libertarian_freewill_fails_to_derive_substantive_person` | theorem | [L683](formal/Logos/DefinitiveAgencyFrontier.lean#L683) | `theorem libertarian_freewill_fails_to_derive_substantive_person : ∃ (Subj : Type` | {}  |
| `model_A1_puppet` | theorem | [L326](formal/Logos/DefinitiveAgencyFrontier.lean#L326) | `theorem model_A1_puppet : ∃ (Subj : Type) (CS : FineCognitiveSubject Subj) (Sour` | {}  |
| `model_A2_external_optimizer` | theorem | [L334](formal/Logos/DefinitiveAgencyFrontier.lean#L334) | `theorem model_A2_external_optimizer : ∃ (Subj : Type) (CS : FineCognitiveSubject` | {}  |
| `model_A3_subpersonal_execution` | theorem | [L379](formal/Logos/DefinitiveAgencyFrontier.lean#L379) | `theorem model_A3_subpersonal_execution : ∃ (Subj : Type) (CS : FineCognitiveSubj` | {}  |
| `model_A4_authorless_execution` | theorem | [L392](formal/Logos/DefinitiveAgencyFrontier.lean#L392) | `theorem model_A4_authorless_execution : ∃ (Subj : Type) (InitiatesRel : Subj → U` | {}  |
| `model_A5_author_without_self_attribution` | theorem | [L404](formal/Logos/DefinitiveAgencyFrontier.lean#L404) | `theorem model_A5_author_without_self_attribution : ∃ (Subj : Type) (CS : FineCog` | {}  |
| `model_AC1_deterministic_agent_causal` | theorem | [L461](formal/Logos/DefinitiveAgencyFrontier.lean#L461) | `theorem model_AC1_deterministic_agent_causal : ∃ (Subj : Type) (AgentDet : Subj ` | {}  |
| `model_AC2_indeterministic_chance` | theorem | [L471](formal/Logos/DefinitiveAgencyFrontier.lean#L471) | `theorem model_AC2_indeterministic_chance : ∃ (Subj : Type) (AgentDet : Subj → Pr` | {}  |
| `model_AC3_externally_determined` | theorem | [L482](formal/Logos/DefinitiveAgencyFrontier.lean#L482) | `theorem model_AC3_externally_determined : ∃ (Subj : Type) (AgentDet : Subj → Pro` | {}  |
| `model_AC4_agent_causal_without_alternatives` | theorem | [L492](formal/Logos/DefinitiveAgencyFrontier.lean#L492) | `theorem model_AC4_agent_causal_without_alternatives : ∃ (Subj : Type) (AgentDet ` | {}  |
| `model_AC5_full_libertarian` | theorem | [L508](formal/Logos/DefinitiveAgencyFrontier.lean#L508) | `theorem model_AC5_full_libertarian : ∃ (Subj : Type) (AgentDet : Subj → Prop → P` | {}  |
| `model_C1_passive_truth_tracker` | theorem | [L69](formal/Logos/DefinitiveAgencyFrontier.lean#L69) | `theorem model_C1_passive_truth_tracker : ∃ (Subj : Type) (CS : FineCognitiveSubj` | {}  |
| `model_C2_formal_evaluator` | theorem | [L83](formal/Logos/DefinitiveAgencyFrontier.lean#L83) | `theorem model_C2_formal_evaluator : ∃ (Subj : Type) (CS : FineCognitiveSubject S` | {}  |
| `model_C3_suspended_judgment` | theorem | [L94](formal/Logos/DefinitiveAgencyFrontier.lean#L94) | `theorem model_C3_suspended_judgment : ∃ (Subj : Type) (CS : FineCognitiveSubject` | {}  |
| `model_C4_assertion_without_commitment` | theorem | [L106](formal/Logos/DefinitiveAgencyFrontier.lean#L106) | `theorem model_C4_assertion_without_commitment : ∃ (Subj : Type) (CS : FineCognit` | {}  |
| `model_C5_commitment_without_assertion` | theorem | [L132](formal/Logos/DefinitiveAgencyFrontier.lean#L132) | `theorem model_C5_commitment_without_assertion : ∃ (Subj : Type) (CS : FineCognit` | {}  |
| `model_V1_pure_theoretician` | theorem | [L215](formal/Logos/DefinitiveAgencyFrontier.lean#L215) | `theorem model_V1_pure_theoretician : ∃ (Subj : Type) (CS : FineCognitiveSubject ` | {}  |
| `model_V2_aim_without_deliberative_settlement` | theorem | [L224](formal/Logos/DefinitiveAgencyFrontier.lean#L224) | `theorem model_V2_aim_without_deliberative_settlement : ∃ (Subj : Type) (CS : Fin` | {}  |
| `model_V3_commitment_to_unwanted_fact` | theorem | [L250](formal/Logos/DefinitiveAgencyFrontier.lean#L250) | `theorem model_V3_commitment_to_unwanted_fact : ∃ (Subj : Type) (CS : FineCogniti` | {}  |
| `model_V4_external_objective` | theorem | [L259](formal/Logos/DefinitiveAgencyFrontier.lean#L259) | `theorem model_V4_external_objective : ∃ (Subj : Type) (CS : FineCognitiveSubject` | {}  |
| `model_V5_spontaneous_aim` | theorem | [L269](formal/Logos/DefinitiveAgencyFrontier.lean#L269) | `theorem model_V5_spontaneous_aim : ∃ (Subj : Type) (CS : FineCognitiveSubject Su` | {}  |
| `performative_datum_supplies_executive_initiation` | theorem | [L310](formal/Logos/DefinitiveAgencyFrontier.lean#L310) | `theorem performative_datum_supplies_executive_initiation {Subj : Type} (CS : Fin` | {}  |
| `reason_responsiveness_compatible_with_determinism` | theorem | [L434](formal/Logos/DefinitiveAgencyFrontier.lean#L434) | `theorem reason_responsiveness_compatible_with_determinism : ∃ (Subj : Type) (Cho` | {}  |
| `retorsion_denial_does_not_commit_to_content` | theorem | [L164](formal/Logos/DefinitiveAgencyFrontier.lean#L164) | `theorem retorsion_denial_does_not_commit_to_content : ∃ (Subj : Type) (CS : Fine` | {}  |
| `sincerity_is_independent` | theorem | [L201](formal/Logos/DefinitiveAgencyFrontier.lean#L201) | `theorem sincerity_is_independent : ∃ (Subj : Type) (CS : FineCognitiveSubject Su` | {}  |
| `standalone_volition_fails_to_derive_agency` | theorem | [L297](formal/Logos/DefinitiveAgencyFrontier.lean#L297) | `theorem standalone_volition_fails_to_derive_agency : ∃ (Subj : Type) (CS : FineC` | {}  |
| `two_sided_independence_commitment` | theorem | [L589](formal/Logos/DefinitiveAgencyFrontier.lean#L589) | `theorem two_sided_independence_commitment : (∃ (Subj : Type) (CS : FineCognitive` | {}  |
| `two_sided_independence_volition` | theorem | [L603](formal/Logos/DefinitiveAgencyFrontier.lean#L603) | `theorem two_sided_independence_volition : (∃ (Subj : Type) (CS : FineCognitiveSu` | {}  |

### `Logos.DeterministicReductioFrontier`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `AgencyLexicon` | structure | [L68](formal/Logos/DeterministicReductioFrontier.lean#L68) | `structure AgencyLexicon where` | —  |
| `CognitiveAgency` | structure | [L407](formal/Logos/DeterministicReductioFrontier.lean#L407) | `structure CognitiveAgency (Subject : Type) where` | —  |
| `HardenedDeterministicReasoner` | structure | [L238](formal/Logos/DeterministicReductioFrontier.lean#L238) | `structure HardenedDeterministicReasoner where` | —  |
| `M16_Hardened` | def | [L252](formal/Logos/DeterministicReductioFrontier.lean#L252) | `def M16_Hardened (q : Prop) (_hqFalse : q ↔ False) : HardenedDeterministicReason` | {CL}  |
| `M16_refutes_chooses` | theorem | [L440](formal/Logos/DeterministicReductioFrontier.lean#L440) | `theorem M16_refutes_chooses (q : Prop) (hq : q ↔ False) : ¬ ∃ (a b : Prop), (M16` | {CL}  |
| `M16_refutes_freewill` | theorem | [L455](formal/Logos/DeterministicReductioFrontier.lean#L455) | `theorem M16_refutes_freewill (q : Prop) (hq : q ↔ False) : ¬ ∃ (a b : Prop), (M1` | {CL}  |
| `RationalSettlement` | def | [L180](formal/Logos/DeterministicReductioFrontier.lean#L180) | `def RationalSettlement (Subject : Type) (R : ReductioProgression Subject) (s : S` | {}  |
| `ReductioPhase` | inductive | [L227](formal/Logos/DeterministicReductioFrontier.lean#L227) | `inductive ReductioPhase` | —  |
| `ReductioProgression` | structure | [L104](formal/Logos/DeterministicReductioFrontier.lean#L104) | `structure ReductioProgression (Subject : Type) where` | —  |
| `choice_not_implies_chooses` | theorem | [L86](formal/Logos/DeterministicReductioFrontier.lean#L86) | `theorem choice_not_implies_chooses : ∃ (Subject : Type) (Choice : Subject → Prop` | {}  |
| `cognitive_agency_not_implies_choice` | theorem | [L421](formal/Logos/DeterministicReductioFrontier.lean#L421) | `theorem cognitive_agency_not_implies_choice : ∃ (Subject : Type) (CA : Cognitive` | {}  |
| `factive_assertion_of_no_act_is_contradictory` | theorem | [L494](formal/Logos/DeterministicReductioFrontier.lean#L494) | `theorem factive_assertion_of_no_act_is_contradictory {Subject : Type} (AssertsAt` | {}  |
| `performative_datum_not_implies_reductio_progression` | theorem | [L120](formal/Logos/DeterministicReductioFrontier.lean#L120) | `theorem performative_datum_not_implies_reductio_progression : ∃ (Subject : Type)` | {}  |
| `performative_self_refutation_compatible_with_determinism` | theorem | [L510](formal/Logos/DeterministicReductioFrontier.lean#L510) | `theorem performative_self_refutation_compatible_with_determinism : ∃ (M : Harden` | {CL}  |
| `positive_action_without_reductio` | theorem | [L143](formal/Logos/DeterministicReductioFrontier.lean#L143) | `theorem positive_action_without_reductio : ∃ (Subject : Type) (ActAt : Subject →` | {}  |
| `reductio_asymmetry_non_affirmation` | theorem | [L204](formal/Logos/DeterministicReductioFrontier.lean#L204) | `theorem reductio_asymmetry_non_affirmation {Subject : Type} (R : ReductioProgres` | {}  |
| `reductio_forces_rational_settlement` | theorem | [L190](formal/Logos/DeterministicReductioFrontier.lean#L190) | `theorem reductio_forces_rational_settlement {Subject : Type} (R : ReductioProgre` | {}  |
| `reductio_frontier_summary` | theorem | [L533](formal/Logos/DeterministicReductioFrontier.lean#L533) | `theorem reductio_frontier_summary : -- 1. Reductio forces asymmetric rational se` | {CL}  |
| `self_denial_of_reasoning_self_refutes` | theorem | [L481](formal/Logos/DeterministicReductioFrontier.lean#L481) | `theorem self_denial_of_reasoning_self_refutes {Subject : Type} (AssertsAt : Subj` | {}  |
| `stepPhase` | def | [L233](formal/Logos/DeterministicReductioFrontier.lean#L233) | `def stepPhase : ReductioPhase → ReductioPhase | ReductioPhase.Phase0_Assume => R` | {}  |
| `test_A_first_person_survives_determinism` | theorem | [L305](formal/Logos/DeterministicReductioFrontier.lean#L305) | `theorem test_A_first_person_survives_determinism (q : Prop) (hq : q ↔ False) : l` | {CL}  |
| `test_B_intentionality_survives_determinism` | theorem | [L314](formal/Logos/DeterministicReductioFrontier.lean#L314) | `theorem test_B_intentionality_survives_determinism (q : Prop) (hq : q ↔ False) :` | {CL}  |
| `test_C_normative_rule_realized_deterministically` | theorem | [L324](formal/Logos/DeterministicReductioFrontier.lean#L324) | `theorem test_C_normative_rule_realized_deterministically (q : Prop) (hq : q ↔ Fa` | {CL}  |
| `test_D_truth_factivity_survives_determinism` | theorem | [L333](formal/Logos/DeterministicReductioFrontier.lean#L333) | `theorem test_D_truth_factivity_survives_determinism (q : Prop) (hq : q ↔ False) ` | {CL}  |
| `test_E_error_possibility_compatible_with_determinism` | theorem | [L345](formal/Logos/DeterministicReductioFrontier.lean#L345) | `theorem test_E_error_possibility_compatible_with_determinism : ∃ (M : HardenedDe` | {}  |
| `test_F_self_reference_survives_determinism` | theorem | [L368](formal/Logos/DeterministicReductioFrontier.lean#L368) | `theorem test_F_self_reference_survives_determinism : ∃ (M : HardenedDeterministi` | {CL}  |
| `test_G_diachronic_identity_survives_determinism` | theorem | [L378](formal/Logos/DeterministicReductioFrontier.lean#L378) | `theorem test_G_diachronic_identity_survives_determinism (q : Prop) (hq : q ↔ Fal` | {CL}  |
| `test_H_causal_closure_survives_determinism` | theorem | [L386](formal/Logos/DeterministicReductioFrontier.lean#L386) | `theorem test_H_causal_closure_survives_determinism (q : Prop) (hq : q ↔ False) :` | {CL}  |
| `weak_act_not_implies_strong_act` | theorem | [L79](formal/Logos/DeterministicReductioFrontier.lean#L79) | `theorem weak_act_not_implies_strong_act : ∃ (Subject : Type) (act : Subject → Pr` | {}  |

### `Logos.DirectNormativeFreeWill`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `NecessaryStrongNormativity` | def | [L273](formal/Logos/DirectNormativeFreeWill.lean#L273) | `def NecessaryStrongNormativity (dom : StrongNormativeDomain Subject World) : Pro` | {Subject}  |
| `NormativeAgency` | structure | [L61](formal/Logos/DirectNormativeFreeWill.lean#L61) | `structure NormativeAgency` | —  |
| `NormativeAlternative` | structure | [L72](formal/Logos/DirectNormativeFreeWill.lean#L72) | `structure NormativeAlternative` | —  |
| `NormativeDeliberationContext` | structure | [L154](formal/Logos/DirectNormativeFreeWill.lean#L154) | `structure NormativeDeliberationContext` | —  |
| `NormativeGraspPrinciple` | def | [L97](formal/Logos/DirectNormativeFreeWill.lean#L97) | `def NormativeGraspPrinciple (dom : StrongNormativeDomain Subject World) : Prop` | {Means, Subject}  |
| `OughtImpliesAlternativeAvailability` | def | [L188](formal/Logos/DirectNormativeFreeWill.lean#L188) | `def OughtImpliesAlternativeAvailability (dom : StrongNormativeDomain Subject Wor` | {Subject}  |
| `StrongNormativeDomain` | structure | [L49](formal/Logos/DirectNormativeFreeWill.lean#L49) | `structure StrongNormativeDomain (Subject : Type) (World : Type) where` | —  |
| `hostile_model_a_impersonal_normativity_cannot_generate_agency` | theorem | [L335](formal/Logos/DirectNormativeFreeWill.lean#L335) | `theorem hostile_model_a_impersonal_normativity_cannot_generate_agency (dom : Str` | {Subject}  |
| `hostile_model_b_determinism_precludes_alternative_availability` | theorem | [L356](formal/Logos/DirectNormativeFreeWill.lean#L356) | `theorem hostile_model_b_determinism_precludes_alternative_availability {World Pr` | {Subject}  |
| `hostile_model_b_determinism_refutes_kantian_principle` | theorem | [L366](formal/Logos/DirectNormativeFreeWill.lean#L366) | `theorem hostile_model_b_determinism_refutes_kantian_principle (dom : StrongNorma` | {Subject}  |
| `hostile_model_c_compatibilist_satisfies_core_freedom` | theorem | [L389](formal/Logos/DirectNormativeFreeWill.lean#L389) | `theorem hostile_model_c_compatibilist_satisfies_core_freedom (dom : StrongNormat` | {Means, Subject}  |
| `necessary_normativity_implies_necessary_free_subject` | theorem | [L280](formal/Logos/DirectNormativeFreeWill.lean#L280) | `theorem necessary_normativity_implies_necessary_free_subject (dom : StrongNormat` | {Means, Subject}  |
| `necessary_normativity_implies_necessary_free_will` | theorem | [L292](formal/Logos/DirectNormativeFreeWill.lean#L292) | `theorem necessary_normativity_implies_necessary_free_will (dom : StrongNormative` | {Means, Subject}  |
| `necessary_normativity_implies_necessary_genuine_freedom` | theorem | [L304](formal/Logos/DirectNormativeFreeWill.lean#L304) | `theorem necessary_normativity_implies_necessary_genuine_freedom (dom : StrongNor` | {Subject}  |
| `normative_alternative_implies_chooses` | theorem | [L105](formal/Logos/DirectNormativeFreeWill.lean#L105) | `theorem normative_alternative_implies_chooses (dom : StrongNormativeDomain Subje` | {Means, Subject}  |
| `normative_alternative_implies_core_free_subject` | theorem | [L128](formal/Logos/DirectNormativeFreeWill.lean#L128) | `theorem normative_alternative_implies_core_free_subject (dom : StrongNormativeDo` | {Means, Subject}  |
| `normative_alternative_implies_core_free_will` | theorem | [L117](formal/Logos/DirectNormativeFreeWill.lean#L117) | `theorem normative_alternative_implies_core_free_will (dom : StrongNormativeDomai` | {Means, Subject}  |
| `normative_alternative_implies_genuine_chooses` | theorem | [L198](formal/Logos/DirectNormativeFreeWill.lean#L198) | `theorem normative_alternative_implies_genuine_chooses (dom : StrongNormativeDoma` | {Subject}  |
| `normative_alternative_implies_genuine_free_subject` | theorem | [L214](formal/Logos/DirectNormativeFreeWill.lean#L214) | `theorem normative_alternative_implies_genuine_free_subject (dom : StrongNormativ` | {Subject}  |
| `normative_deliberation_yields_strong_chooses` | theorem | [L168](formal/Logos/DirectNormativeFreeWill.lean#L168) | `theorem normative_deliberation_yields_strong_chooses (dom : StrongNormativeDomai` | {Subject}  |
| `normative_route_to_metaphysical_indeterminism` | theorem | [L230](formal/Logos/DirectNormativeFreeWill.lean#L230) | `theorem normative_route_to_metaphysical_indeterminism (dom : StrongNormativeDoma` | {Subject}  |
| `normative_route_to_not_d3` | theorem | [L246](formal/Logos/DirectNormativeFreeWill.lean#L246) | `theorem normative_route_to_not_d3 (dom : StrongNormativeDomain Subject World) {P` | {Subject}  |

### `Logos.EssenceActCollapse`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `ActToCreationBridge` | def | [L137](formal/Logos/EssenceActCollapse.lean#L137) | `def ActToCreationBridge (World Entity Subject : Type) (EntityOf : Subject → Enti` | {}  |
| `ActToVolitionBridge` | def | [L132](formal/Logos/EssenceActCollapse.lean#L132) | `def ActToVolitionBridge (World Subject : Type) (WillsAt : World → Subject → Prop` | {}  |
| `CandidateA_VolitionalIndifference` | def | [L290](formal/Logos/EssenceActCollapse.lean#L290) | `def CandidateA_VolitionalIndifference (World Subject : Type) (frame : KripkeFram` | {}  |
| `CandidateB_NonDeterministicVolition` | def | [L300](formal/Logos/EssenceActCollapse.lean#L300) | `def CandidateB_NonDeterministicVolition (World Subject : Type) (Circumstance : W` | {}  |
| `CandidateC_AgentCausalSettlement` | def | [L305](formal/Logos/EssenceActCollapse.lean#L305) | `def CandidateC_AgentCausalSettlement (World Subject : Type) (frame : KripkeFrame` | {}  |
| `CandidateD_SufficientFreedom` | def | [L317](formal/Logos/EssenceActCollapse.lean#L317) | `def CandidateD_SufficientFreedom (World Subject : Type) (frame : KripkeFrame Wor` | {}  |
| `ContingentAct` | def | [L91](formal/Logos/EssenceActCollapse.lean#L91) | `def ContingentAct (World Subject : Type) (ActAt : World → Subject → Prop → Prop)` | {}  |
| `DeterministicVolitionPrinciple` | def | [L232](formal/Logos/EssenceActCollapse.lean#L232) | `def DeterministicVolitionPrinciple (World Subject : Type) (Circumstance : World ` | {}  |
| `HardenedModalFreeWill` | structure | [L44](formal/Logos/EssenceActCollapse.lean#L44) | `structure HardenedModalFreeWill (World Subject : Type)` | —  |
| `MC10_Signature` | structure | [L571](formal/Logos/EssenceActCollapse.lean#L571) | `structure MC10_Signature where` | —  |
| `MC12_Signature` | structure | [L628](formal/Logos/EssenceActCollapse.lean#L628) | `structure MC12_Signature where` | —  |
| `MC7_Signature` | structure | [L424](formal/Logos/EssenceActCollapse.lean#L424) | `structure MC7_Signature where` | —  |
| `MC8_Signature` | structure | [L481](formal/Logos/EssenceActCollapse.lean#L481) | `structure MC8_Signature where` | —  |
| `MC9_Signature` | structure | [L519](formal/Logos/EssenceActCollapse.lean#L519) | `structure MC9_Signature where` | —  |
| `NecessaryAct` | def | [L88](formal/Logos/EssenceActCollapse.lean#L88) | `def NecessaryAct (World Subject : Type) (ActAt : World → Subject → Prop → Prop) ` | {}  |
| `NecessaryEntity` | def | [L82](formal/Logos/EssenceActCollapse.lean#L82) | `def NecessaryEntity (World Entity : Type) (ExistsAt : World → Entity → Prop) (g ` | {}  |
| `NecessaryNature` | def | [L85](formal/Logos/EssenceActCollapse.lean#L85) | `def NecessaryNature (World Entity : Type) (NatureAt : World → Entity → Prop) (g ` | {}  |
| `SameCircumstances` | def | [L226](formal/Logos/EssenceActCollapse.lean#L226) | `def SameCircumstances (World : Type) (Circumstance : World → Prop) (w u : World)` | {}  |
| `SameNature` | def | [L229](formal/Logos/EssenceActCollapse.lean#L229) | `def SameNature (World Entity : Type) (NatureAt : World → Entity → Prop) (g : Ent` | {}  |
| `Statement1_PassiveNoCreation` | def | [L175](formal/Logos/EssenceActCollapse.lean#L175) | `def Statement1_PassiveNoCreation (World Entity : Type) (frame : KripkeFrame Worl` | {}  |
| `Statement2_WillsNotToCreate` | def | [L180](formal/Logos/EssenceActCollapse.lean#L180) | `def Statement2_WillsNotToCreate (World Subject : Type) (frame : KripkeFrame Worl` | {}  |
| `Statement3_FreelyWillsNotToCreate` | def | [L185](formal/Logos/EssenceActCollapse.lean#L185) | `def Statement3_FreelyWillsNotToCreate (World Subject : Type) (frame : KripkeFram` | {}  |
| `Statement4_BilateralFreeWillCreation` | def | [L191](formal/Logos/EssenceActCollapse.lean#L191) | `def Statement4_BilateralFreeWillCreation (World Subject : Type) (frame : KripkeF` | {}  |
| `VolitionToActBridge` | def | [L127](formal/Logos/EssenceActCollapse.lean#L127) | `def VolitionToActBridge (World Subject : Type) (WillsAt : World → Subject → Prop` | {}  |
| `VolitionToCreationBridge` | def | [L144](formal/Logos/EssenceActCollapse.lean#L144) | `def VolitionToCreationBridge (World Entity Subject : Type) (EntityOf : Subject →` | {}  |
| `agent_causal_implies_volitional_indifference` | theorem | [L327](formal/Logos/EssenceActCollapse.lean#L327) | `theorem agent_causal_implies_volitional_indifference (World Subject : Type) (fra` | {}  |
| `free_creation_anti_collapse` | theorem | [L403](formal/Logos/EssenceActCollapse.lean#L403) | `theorem free_creation_anti_collapse (World Subject : Type) (frame : KripkeFrame ` | {}  |
| `hardened_modal_freedom_forces_distinct_worlds` | theorem | [L61](formal/Logos/EssenceActCollapse.lean#L61) | `theorem hardened_modal_freedom_forces_distinct_worlds (World Subject : Type) (fr` | {}  |
| `involuntary_act_consistent` | theorem | [L153](formal/Logos/EssenceActCollapse.lean#L153) | `theorem involuntary_act_consistent : ∃ (World Subject : Type) (WillsAt : World →` | {}  |
| `modal_collapse_action_theorem` | theorem | [L261](formal/Logos/EssenceActCollapse.lean#L261) | `theorem modal_collapse_action_theorem (World Entity Subject : Type) (frame : Kri` | {}  |
| `modal_collapse_theorem` | theorem | [L241](formal/Logos/EssenceActCollapse.lean#L241) | `theorem modal_collapse_theorem (World Subject : Type) (frame : KripkeFrame World` | {}  |
| `model_MC10_consistent` | theorem | [L587](formal/Logos/EssenceActCollapse.lean#L587) | `theorem model_MC10_consistent : ∃ _M : MC10_Signature, True` | {}  |
| `model_MC11_consistent` | theorem | [L612](formal/Logos/EssenceActCollapse.lean#L612) | `theorem model_MC11_consistent : ∃ (World Entity Subject : Type) (frame : KripkeF` | {}  |
| `model_MC12_consistent` | theorem | [L644](formal/Logos/EssenceActCollapse.lean#L644) | `theorem model_MC12_consistent : ∃ _M : MC12_Signature, True` | {}  |
| `model_MC7_consistent` | theorem | [L449](formal/Logos/EssenceActCollapse.lean#L449) | `theorem model_MC7_consistent : ∃ _M : MC7_Signature, True` | {}  |
| `model_MC8_consistent` | theorem | [L497](formal/Logos/EssenceActCollapse.lean#L497) | `theorem model_MC8_consistent : ∃ _M : MC8_Signature, True` | {}  |
| `model_MC9_consistent` | theorem | [L542](formal/Logos/EssenceActCollapse.lean#L542) | `theorem model_MC9_consistent : ∃ _M : MC9_Signature, True` | {}  |
| `necessary_nature_not_entails_necessary_act` | theorem | [L97](formal/Logos/EssenceActCollapse.lean#L97) | `theorem necessary_nature_not_entails_necessary_act : ∃ (World Entity Subject : T` | {}  |
| `statement2_implies_statement1` | theorem | [L205](formal/Logos/EssenceActCollapse.lean#L205) | `theorem statement2_implies_statement1 (World Entity Subject : Type) (frame : Kri` | {}  |
| `statement3_implies_statement2` | theorem | [L197](formal/Logos/EssenceActCollapse.lean#L197) | `theorem statement3_implies_statement2 (World Subject : Type) (frame : KripkeFram` | {}  |
| `sufficient_freedom_not_entails_volitional_indifference` | theorem | [L369](formal/Logos/EssenceActCollapse.lean#L369) | `theorem sufficient_freedom_not_entails_volitional_indifference : ∃ (World Subjec` | {CL}  |
| `unexecuted_volition_consistent` | theorem | [L163](formal/Logos/EssenceActCollapse.lean#L163) | `theorem unexecuted_volition_consistent : ∃ (World Subject : Type) (WillsAt : Wor` | {}  |
| `volitional_indifference_implies_nondeterministic` | theorem | [L352](formal/Logos/EssenceActCollapse.lean#L352) | `theorem volitional_indifference_implies_nondeterministic (World Subject : Type) ` | {}  |
| `volitional_indifference_implies_sufficient_freedom` | theorem | [L340](formal/Logos/EssenceActCollapse.lean#L340) | `theorem volitional_indifference_implies_sufficient_freedom (World Subject : Type` | {}  |

### `Logos.ExecutiveDeliberativeFrontier`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `AuditVerdict` | structure | [L300](formal/Logos/ExecutiveDeliberativeFrontier.lean#L300) | `structure AuditVerdict where` | —  |
| `BranchingWorldSignature` | structure | [L416](formal/Logos/ExecutiveDeliberativeFrontier.lean#L416) | `structure BranchingWorldSignature where` | —  |
| `CognitiveLadder` | structure | [L386](formal/Logos/ExecutiveDeliberativeFrontier.lean#L386) | `structure CognitiveLadder (Subject : Type) where` | —  |
| `DeterministicModel` | structure | [L165](formal/Logos/ExecutiveDeliberativeFrontier.lean#L165) | `structure DeterministicModel where` | —  |
| `DownstreamOntology` | structure | [L518](formal/Logos/ExecutiveDeliberativeFrontier.lean#L518) | `structure DownstreamOntology where` | —  |
| `M_det` | def | [L181](formal/Logos/ExecutiveDeliberativeFrontier.lean#L181) | `def M_det : DeterministicModel where Subject` | {}  |
| `M_det_refutes_chooses` | theorem | [L210](formal/Logos/ExecutiveDeliberativeFrontier.lean#L210) | `theorem M_det_refutes_chooses (M : DeterministicModel) : ¬ ∃ p q, M.Means M.s p ` | {}  |
| `M_det_refutes_missing_cognitive_horn` | theorem | [L202](formal/Logos/ExecutiveDeliberativeFrontier.lean#L202) | `theorem M_det_refutes_missing_cognitive_horn (M : DeterministicModel) : ¬ ∃ q, M` | {}  |
| `M_det_validates_executive_choice` | theorem | [L197](formal/Logos/ExecutiveDeliberativeFrontier.lean#L197) | `theorem M_det_validates_executive_choice (M : DeterministicModel) : M.Asserts M.` | {}  |
| `MechanicalProver` | structure | [L349](formal/Logos/ExecutiveDeliberativeFrontier.lean#L349) | `structure MechanicalProver where` | —  |
| `ProofTraceSignature` | structure | [L343](formal/Logos/ExecutiveDeliberativeFrontier.lean#L343) | `structure ProofTraceSignature where` | —  |
| `SelfDenialOfDeliberation` | def | [L249](formal/Logos/ExecutiveDeliberativeFrontier.lean#L249) | `def SelfDenialOfDeliberation (s : Subject) (p : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `audit_Act_to_Choice` | def | [L306](formal/Logos/ExecutiveDeliberativeFrontier.lean#L306) | `def audit_Act_to_Choice : AuditVerdict where candidateName` | {}  |
| `audit_Act_to_Chooses` | def | [L318](formal/Logos/ExecutiveDeliberativeFrontier.lean#L318) | `def audit_Act_to_Chooses : AuditVerdict where candidateName` | {}  |
| `audit_Choice_to_Chooses` | def | [L312](formal/Logos/ExecutiveDeliberativeFrontier.lean#L312) | `def audit_Choice_to_Chooses : AuditVerdict where candidateName` | {}  |
| `audit_ExistentialAct_to_FreeWill` | def | [L324](formal/Logos/ExecutiveDeliberativeFrontier.lean#L324) | `def audit_ExistentialAct_to_FreeWill : AuditVerdict where candidateName` | {}  |
| `exclusion_not_implies_representation` | theorem | [L393](formal/Logos/ExecutiveDeliberativeFrontier.lean#L393) | `theorem exclusion_not_implies_representation : ∃ (Subject : Type) (CL : Cognitiv` | {CL}  |
| `freeAgency_not_implies_necessary_subject` | theorem | [L539](formal/Logos/ExecutiveDeliberativeFrontier.lean#L539) | `theorem freeAgency_not_implies_necessary_subject : ∃ (DO : DownstreamOntology) (` | {}  |
| `freeAgency_not_implies_person` | theorem | [L526](formal/Logos/ExecutiveDeliberativeFrontier.lean#L526) | `theorem freeAgency_not_implies_person : ∃ (DO : DownstreamOntology) (s : DO.Subj` | {}  |
| `freeAgency_not_implies_ultimate_ground` | theorem | [L552](formal/Logos/ExecutiveDeliberativeFrontier.lean#L552) | `theorem freeAgency_not_implies_ultimate_ground : ∃ (DO : DownstreamOntology) (s ` | {}  |
| `mechanical_prover_lacks_deliberation` | theorem | [L355](formal/Logos/ExecutiveDeliberativeFrontier.lean#L355) | `theorem mechanical_prover_lacks_deliberation : ∃ (M : MechanicalProver), (∃ step` | {}  |
| `modal_branching_not_induces_representation` | theorem | [L427](formal/Logos/ExecutiveDeliberativeFrontier.lean#L427) | `theorem modal_branching_not_induces_representation : ∃ (BW : BranchingWorldSigna` | {}  |
| `retorsion_NoChoice_self_refutes` | theorem | [L472](formal/Logos/ExecutiveDeliberativeFrontier.lean#L472) | `theorem retorsion_NoChoice_self_refutes (s : Subject) (p : Prop) (hAss : Asserts` | {Initiates, Means, State, Subject}  |
| `retorsion_NoDeliberation_consistent` | theorem | [L482](formal/Logos/ExecutiveDeliberativeFrontier.lean#L482) | `theorem retorsion_NoDeliberation_consistent : ∃ (Subject : Type) (s : Subject) (` | {}  |
| `retorsion_NoFreeWill_consistent` | theorem | [L495](formal/Logos/ExecutiveDeliberativeFrontier.lean#L495) | `theorem retorsion_NoFreeWill_consistent : ∃ (Subject : Type) (s : Subject) (p : ` | {}  |
| `schema_S1_performative_contradiction` | theorem | [L235](formal/Logos/ExecutiveDeliberativeFrontier.lean#L235) | `theorem schema_S1_performative_contradiction (s : Subject) (p : Prop) (hAss : As` | {Initiates, Means, State, Subject}  |
| `schema_S2_coherent` | theorem | [L243](formal/Logos/ExecutiveDeliberativeFrontier.lean#L243) | `theorem schema_S2_coherent (s : Subject) (p : Prop) (hAss : Asserts s p) (_hSelf` | {Initiates, Means, State, Subject}  |
| `schema_S4_satisfiable_and_non_self_refuting` | theorem | [L254](formal/Logos/ExecutiveDeliberativeFrontier.lean#L254) | `theorem schema_S4_satisfiable_and_non_self_refuting : ∃ (Subject : Type) (s : Su` | {}  |
| `schema_S5_executive_without_deliberation_coherent` | theorem | [L266](formal/Logos/ExecutiveDeliberativeFrontier.lean#L266) | `theorem schema_S5_executive_without_deliberation_coherent : ∃ (Subject : Type) (` | {}  |
| `trackA_act_not_implies_deliberates` | theorem | [L117](formal/Logos/ExecutiveDeliberativeFrontier.lean#L117) | `theorem trackA_act_not_implies_deliberates : ∃ (Subject : Type) (s : Subject) (p` | {}  |
| `trackA_asserts_implies_choice` | theorem | [L61](formal/Logos/ExecutiveDeliberativeFrontier.lean#L61) | `theorem trackA_asserts_implies_choice (s : Subject) (p : Prop) (hAss : Asserts s` | {Initiates, Means, State, Subject}  |
| `trackA_choice_implies_freeAgency` | theorem | [L66](formal/Logos/ExecutiveDeliberativeFrontier.lean#L66) | `theorem trackA_choice_implies_freeAgency (s : Subject) (p : Prop) (hChoice : Cho` | {Initiates, Means, State, Subject}  |
| `trackA_choice_not_implies_chooses` | theorem | [L82](formal/Logos/ExecutiveDeliberativeFrontier.lean#L82) | `theorem trackA_choice_not_implies_chooses : ∃ (Subject : Type) (s : Subject) (p ` | {}  |
| `trackA_chooses_implies_freeWill` | theorem | [L71](formal/Logos/ExecutiveDeliberativeFrontier.lean#L71) | `theorem trackA_chooses_implies_freeWill (s : Subject) (p q : Prop) (hChooses : C` | {Means, Subject}  |
| `trackA_chooses_not_implies_choice` | theorem | [L102](formal/Logos/ExecutiveDeliberativeFrontier.lean#L102) | `theorem trackA_chooses_not_implies_choice : ∃ (Subject : Type) (s : Subject) (p ` | {}  |
| `trackA_deliberates_iff_chooses` | theorem | [L76](formal/Logos/ExecutiveDeliberativeFrontier.lean#L76) | `theorem trackA_deliberates_iff_chooses (s : Subject) (p q : Prop) : Deliberates ` | {Means, Subject}  |
| `trackA_freeAgency_not_implies_freeWill` | theorem | [L134](formal/Logos/ExecutiveDeliberativeFrontier.lean#L134) | `theorem trackA_freeAgency_not_implies_freeWill : ∃ (Subject : Type) (s : Subject` | {}  |
| `trackB_selfDenialOfExecutiveChoice_selfRefutes` | theorem | [L157](formal/Logos/ExecutiveDeliberativeFrontier.lean#L157) | `theorem trackB_selfDenialOfExecutiveChoice_selfRefutes {s : Subject} {p : Prop} ` | {Initiates, Means, State, Subject}  |

### `Logos.FreeWillIndependence`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `BridgeB1` | def | [L390](formal/Logos/FreeWillIndependence.lean#L390) | `def BridgeB1 (CS : FineCognitiveSubject Subject) : Prop` | {Subject}  |
| `BridgeB2` | def | [L394](formal/Logos/FreeWillIndependence.lean#L394) | `def BridgeB2 (CS : FineCognitiveSubject Subject) (MeansAt : Subject → Prop → Pro` | {Subject}  |
| `BridgeB3` | def | [L398](formal/Logos/FreeWillIndependence.lean#L398) | `def BridgeB3 (MeansAt : Subject → Prop → Prop) (CanAct : Subject → Prop → Prop) ` | {Subject}  |
| `BridgeB4` | def | [L402](formal/Logos/FreeWillIndependence.lean#L402) | `def BridgeB4 (CanAct : Subject → Prop → Prop) (AgentDetermines : Subject → Prop ` | {Subject}  |
| `CognitiveStatus` | inductive | [L116](formal/Logos/FreeWillIndependence.lean#L116) | `inductive CognitiveStatus | Assumed | Examined | Rejected | Affirmed` | —  |
| `DeliberativeState` | structure | [L267](formal/Logos/FreeWillIndependence.lean#L267) | `structure DeliberativeState where` | —  |
| `F1b_Target` | def | [L50](formal/Logos/FreeWillIndependence.lean#L50) | `def F1b_Target : Prop` | {Initiates, Means, State, Subject}  |
| `GammaCoreModel` | structure | [L138](formal/Logos/FreeWillIndependence.lean#L138) | `structure GammaCoreModel where` | —  |
| `HasCommitment` | def | [L74](formal/Logos/FreeWillIndependence.lean#L74) | `def HasCommitment (CS : FineCognitiveSubject Subject) (s : Subject) (p : Prop) :` | {Subject}  |
| `RationalDeliberator` | structure | [L336](formal/Logos/FreeWillIndependence.lean#L336) | `structure RationalDeliberator (Subject : Type) where` | —  |
| `TransformToUnipolar` | def | [L247](formal/Logos/FreeWillIndependence.lean#L247) | `def TransformToUnipolar (M : GammaCoreModel) (s_witness : M.Subj) (p_witness : P` | {}  |
| `bridge_B2_derives_choice` | theorem | [L407](formal/Logos/FreeWillIndependence.lean#L407) | `theorem bridge_B2_derives_choice (CS : FineCognitiveSubject Subject) (MeansAt : ` | {Subject}  |
| `deterministic_status_transition_without_freewill` | theorem | [L120](formal/Logos/FreeWillIndependence.lean#L120) | `theorem deterministic_status_transition_without_freewill : ∃ (Transition : Cogni` | {}  |
| `f1b_target_definitionally_unfolded` | theorem | [L54](formal/Logos/FreeWillIndependence.lean#L54) | `theorem f1b_target_definitionally_unfolded : F1b_Target ↔ ((∃ s : Subject, ∃ p :` | {Initiates, Means, State, Subject}  |
| `freewill_is_model_theoretically_independent` | theorem | [L239](formal/Logos/FreeWillIndependence.lean#L239) | `theorem freewill_is_model_theoretically_independent : (∃ M : GammaCoreModel, ∃ s` | {}  |
| `identical_deliberation_case_A` | theorem | [L290](formal/Logos/FreeWillIndependence.lean#L290) | `theorem identical_deliberation_case_A : ∃ (AgentSettles : DeliberativeState → Pr` | {}  |
| `identical_deliberation_case_D` | theorem | [L274](formal/Logos/FreeWillIndependence.lean#L274) | `theorem identical_deliberation_case_D : ∃ (Transition : DeliberativeState → Prop` | {}  |
| `identical_deliberation_case_M` | theorem | [L281](formal/Logos/FreeWillIndependence.lean#L281) | `theorem identical_deliberation_case_M : ∃ (Accessible : DeliberativeState → Prop` | {}  |
| `intentional_resolution_excludes_choice_of_same_horns` | theorem | [L108](formal/Logos/FreeWillIndependence.lean#L108) | `theorem intentional_resolution_excludes_choice_of_same_horns (MeansAt : Subject ` | {Subject}  |
| `model_A_gamma_with_freewill` | theorem | [L152](formal/Logos/FreeWillIndependence.lean#L152) | `theorem model_A_gamma_with_freewill : ∃ (M : GammaCoreModel), ∃ (s : M.Subj) (p ` | {}  |
| `model_B_gamma_without_freewill` | theorem | [L192](formal/Logos/FreeWillIndependence.lean#L192) | `theorem model_B_gamma_without_freewill : ∃ (M : GammaCoreModel), (∀ (s : M.Subj)` | {}  |
| `model_M14_plus_evaluation_without_commitment` | theorem | [L79](formal/Logos/FreeWillIndependence.lean#L79) | `theorem model_M14_plus_evaluation_without_commitment : ∃ (Subj : Type) (CS : Fin` | {}  |
| `model_deterministic_rationality_without_modal_freedom` | theorem | [L345](formal/Logos/FreeWillIndependence.lean#L345) | `theorem model_deterministic_rationality_without_modal_freedom : ∃ (Subject : Typ` | {}  |
| `model_libertarian_settlement_without_reasons` | theorem | [L359](formal/Logos/FreeWillIndependence.lean#L359) | `theorem model_libertarian_settlement_without_reasons : ∃ (Subject : Type) (RD : ` | {}  |
| `rationality_orthogonal_to_libertarian_freedom` | theorem | [L373](formal/Logos/FreeWillIndependence.lean#L373) | `theorem rationality_orthogonal_to_libertarian_freedom : (∃ (Subj : Type) (RD : R` | {}  |
| `settlement_1_compatible_with_no_chdo` | theorem | [L303](formal/Logos/FreeWillIndependence.lean#L303) | `theorem settlement_1_compatible_with_no_chdo : ∃ (Subject : Type) (CS : FineCogn` | {}  |
| `settlement_1_is_assembled_package` | theorem | [L63](formal/Logos/FreeWillIndependence.lean#L63) | `theorem settlement_1_is_assembled_package (CS : FineCognitiveSubject Subject) (s` | {Subject}  |

### `Logos.FreeWillInvariance`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `CoreGammaLayer` | def | [L184](formal/Logos/FreeWillInvariance.lean#L184) | `def CoreGammaLayer (l : DependencyLayer) : Prop` | {}  |
| `DatumRequiresFreeWill` | def | [L116](formal/Logos/FreeWillInvariance.lean#L116) | `def DatumRequiresFreeWill (Subject : Type) (p : Prop) (_datum : PerformativeDatu` | {}  |
| `DependencyLayer` | inductive | [L82](formal/Logos/FreeWillInvariance.lean#L82) | `inductive DependencyLayer` | —  |
| `FirstFreeWillSensitiveLayer` | def | [L217](formal/Logos/FreeWillInvariance.lean#L217) | `def FirstFreeWillSensitiveLayer : DependencyLayer` | {}  |
| `LayerRequiresFreeWill` | def | [L196](formal/Logos/FreeWillInvariance.lean#L196) | `def LayerRequiresFreeWill (l : DependencyLayer) : Prop` | {}  |
| `PerformativeDatum` | structure | [L111](formal/Logos/FreeWillInvariance.lean#L111) | `structure PerformativeDatum (Subject : Type) (p : Prop) where` | —  |
| `PerformerRegime` | inductive | [L58](formal/Logos/FreeWillInvariance.lean#L58) | `inductive PerformerRegime` | —  |
| `ProofDimensions` | structure | [L73](formal/Logos/FreeWillInvariance.lean#L73) | `structure ProofDimensions (World Subject : Type) where` | —  |
| `causal_necessity_not_entails_logical_necessity` | theorem | [L151](formal/Logos/FreeWillInvariance.lean#L151) | `theorem causal_necessity_not_entails_logical_necessity : ∃ (World : Type) (frame` | {}  |
| `core_gamma_free_will_invariant` | theorem | [L202](formal/Logos/FreeWillInvariance.lean#L202) | `theorem core_gamma_free_will_invariant (l : DependencyLayer) (hCore : CoreGammaL` | {}  |
| `first_freewill_sensitive_layer_is_L10` | theorem | [L220](formal/Logos/FreeWillInvariance.lean#L220) | `theorem first_freewill_sensitive_layer_is_L10 : FirstFreeWillSensitiveLayer = De` | {}  |
| `model_FW0_consistent` | theorem | [L234](formal/Logos/FreeWillInvariance.lean#L234) | `theorem model_FW0_consistent : ∃ (World Subject : Type) (frame : KripkeFrame Wor` | {}  |
| `model_FW10_consistent` | theorem | [L364](formal/Logos/FreeWillInvariance.lean#L364) | `theorem model_FW10_consistent : ∃ (World : Type) (frame : KripkeFrame World) (ac` | {}  |
| `model_FW1_consistent` | theorem | [L247](formal/Logos/FreeWillInvariance.lean#L247) | `theorem model_FW1_consistent : ∃ (World Subject : Type) (frame : KripkeFrame Wor` | {}  |
| `model_FW2_consistent` | theorem | [L262](formal/Logos/FreeWillInvariance.lean#L262) | `theorem model_FW2_consistent : ∃ (World Subject : Type) (frame : KripkeFrame Wor` | {}  |
| `model_FW3_consistent` | theorem | [L280](formal/Logos/FreeWillInvariance.lean#L280) | `theorem model_FW3_consistent : ∃ (World Subject : Type) (frame : KripkeFrame Wor` | {}  |
| `model_FW4_consistent` | theorem | [L292](formal/Logos/FreeWillInvariance.lean#L292) | `theorem model_FW4_consistent : ∃ (World Subject : Type) (frame : KripkeFrame Wor` | {}  |
| `model_FW5_consistent` | theorem | [L308](formal/Logos/FreeWillInvariance.lean#L308) | `theorem model_FW5_consistent : ∃ (World : Type) (frame : KripkeFrame World) (act` | {}  |
| `model_FW6_consistent` | theorem | [L316](formal/Logos/FreeWillInvariance.lean#L316) | `theorem model_FW6_consistent : ∃ (World Subject : Type) (frame : KripkeFrame Wor` | {}  |
| `model_FW7_consistent` | theorem | [L331](formal/Logos/FreeWillInvariance.lean#L331) | `theorem model_FW7_consistent : ∃ (World Subject : Type) (frame : KripkeFrame Wor` | {}  |
| `model_FW8_consistent` | theorem | [L339](formal/Logos/FreeWillInvariance.lean#L339) | `theorem model_FW8_consistent : ∃ (World Subject : Type) (frame : KripkeFrame Wor` | {}  |
| `model_FW9_consistent` | theorem | [L351](formal/Logos/FreeWillInvariance.lean#L351) | `theorem model_FW9_consistent : ∃ (World Subject : Type) (frame : KripkeFrame Wor` | {}  |
| `performative_datum_not_entails_freewill` | theorem | [L121](formal/Logos/FreeWillInvariance.lean#L121) | `theorem performative_datum_not_entails_freewill : ∃ (Subject : Type) (p : Prop) ` | {}  |
| `retorsion_under_determinism_valid` | theorem | [L134](formal/Logos/FreeWillInvariance.lean#L134) | `theorem retorsion_under_determinism_valid : ∃ (World Subject : Type) (Antecedent` | {}  |

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

### `Logos.GroundingFrontier`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Candidate_G1` | def | [L83](formal/Logos/GroundingFrontier.lean#L83) | `def Candidate_G1 (M : ModalGroundingSignature) (φ : M.Form) : Prop` | {}  |
| `Candidate_G2` | def | [L88](formal/Logos/GroundingFrontier.lean#L88) | `def Candidate_G2 (M : ModalGroundingSignature) (φ : M.Form) : Prop` | {}  |
| `Candidate_G3` | def | [L93](formal/Logos/GroundingFrontier.lean#L93) | `def Candidate_G3 (M : ModalGroundingSignature) (φ : M.Form) : Prop` | {}  |
| `Candidate_G4` | def | [L98](formal/Logos/GroundingFrontier.lean#L98) | `def Candidate_G4 (M : ModalGroundingSignature) (φ : M.Form) : Prop` | {}  |
| `ExtendedGroundingSignature` | structure | [L355](formal/Logos/GroundingFrontier.lean#L355) | `structure ExtendedGroundingSignature where` | —  |
| `GroundingOrderSignature` | structure | [L284](formal/Logos/GroundingFrontier.lean#L284) | `structure GroundingOrderSignature where` | —  |
| `HasBoundedAncestry` | def | [L337](formal/Logos/GroundingFrontier.lean#L337) | `def HasBoundedAncestry (S : GroundingOrderSignature) (e : S.Entity) (n : Nat) : ` | {}  |
| `MissingRigidGroundHorn` | def | [L163](formal/Logos/GroundingFrontier.lean#L163) | `def MissingRigidGroundHorn (M : ModalGroundingSignature) (φ : M.Form) : Prop` | {}  |
| `ModalGroundingSignature` | structure | [L67](formal/Logos/GroundingFrontier.lean#L67) | `structure ModalGroundingSignature where` | —  |
| `NecessaryEntity` | def | [L78](formal/Logos/GroundingFrontier.lean#L78) | `def NecessaryEntity (M : ModalGroundingSignature) (e : M.Entity) : Prop` | {}  |
| `T_impersonal` | def | [L687](formal/Logos/GroundingFrontier.lean#L687) | `def T_impersonal (M : ExtendedGroundingSignature) : ExtendedGroundingSignature` | {}  |
| `U1_NoInfiniteDescendingChains` | def | [L294](formal/Logos/GroundingFrontier.lean#L294) | `def U1_NoInfiniteDescendingChains (S : GroundingOrderSignature) : Prop` | {}  |
| `UltimateGround` | def | [L289](formal/Logos/GroundingFrontier.lean#L289) | `def UltimateGround (S : GroundingOrderSignature) (u : S.Entity) : Prop` | {}  |
| `UniformNecessaryGround` | def | [L158](formal/Logos/GroundingFrontier.lean#L158) | `def UniformNecessaryGround (M : ModalGroundingSignature) (φ : M.Form) : Prop` | {}  |
| `WorldwiseTruthmaking` | def | [L153](formal/Logos/GroundingFrontier.lean#L153) | `def WorldwiseTruthmaking (M : ModalGroundingSignature) (φ : M.Form) : Prop` | {}  |
| `a4_does_not_imply_single_common_ground` | theorem | [L253](formal/Logos/GroundingFrontier.lean#L253) | `theorem a4_does_not_imply_single_common_ground : ∃ (M : ModalGroundingSignature)` | {}  |
| `a4_does_not_imply_unique_ground` | theorem | [L229](formal/Logos/GroundingFrontier.lean#L229) | `theorem a4_does_not_imply_unique_ground : ∃ (M : ModalGroundingSignature) (φ : M` | {}  |
| `collapse_invariance_impersonal` | theorem | [L703](formal/Logos/GroundingFrontier.lean#L703) | `theorem collapse_invariance_impersonal (M : ExtendedGroundingSignature) (u : M.E` | {}  |
| `cyclic_grounding_has_no_ultimate_ground` | theorem | [L317](formal/Logos/GroundingFrontier.lean#L317) | `theorem cyclic_grounding_has_no_ultimate_ground : ∃ (S : GroundingOrderSignature` | {}  |
| `denial_of_necessary_ground_is_non_self_refuting` | theorem | [L514](formal/Logos/GroundingFrontier.lean#L514) | `theorem denial_of_necessary_ground_is_non_self_refuting : ∃ (M : ModalGroundingS` | {}  |
| `grounding_frontier_synthesis` | theorem | [L729](formal/Logos/GroundingFrontier.lean#L729) | `theorem grounding_frontier_synthesis : -- 1. Quantifier non-equivalence (∃ (M : ` | {}  |
| `implication_G2_implies_G1` | theorem | [L113](formal/Logos/GroundingFrontier.lean#L113) | `theorem implication_G2_implies_G1 (M : ModalGroundingSignature) (φ : M.Form) (hG` | {}  |
| `implication_G4_implies_G2` | theorem | [L103](formal/Logos/GroundingFrontier.lean#L103) | `theorem implication_G4_implies_G2 (M : ModalGroundingSignature) (φ : M.Form) (w0` | {}  |
| `infinite_descending_chain_has_no_ultimate_ground` | theorem | [L300](formal/Logos/GroundingFrontier.lean#L300) | `theorem infinite_descending_chain_has_no_ultimate_ground : ∃ (S : GroundingOrder` | {}  |
| `minimal_ultimate_ground_theorem` | theorem | [L344](formal/Logos/GroundingFrontier.lean#L344) | `theorem minimal_ultimate_ground_theorem (S : GroundingOrderSignature) (e : S.Ent` | {}  |
| `model_G10_personal_ground_with_no_plurality` | theorem | [L664](formal/Logos/GroundingFrontier.lean#L664) | `theorem model_G10_personal_ground_with_no_plurality : ∃ (M : ExtendedGroundingSi` | {}  |
| `model_G1_worldwise_grounding` | theorem | [L572](formal/Logos/GroundingFrontier.lean#L572) | `theorem model_G1_worldwise_grounding : ∃ (M : ModalGroundingSignature) (φ : M.Fo` | {}  |
| `model_G2_uniform_necessary_ground` | theorem | [L578](formal/Logos/GroundingFrontier.lean#L578) | `theorem model_G2_uniform_necessary_ground : ∃ (M : ModalGroundingSignature) (φ :` | {}  |
| `model_G3_infinite_ground_chain` | theorem | [L594](formal/Logos/GroundingFrontier.lean#L594) | `theorem model_G3_infinite_ground_chain : ∃ (S : GroundingOrderSignature), (∀ y, ` | {}  |
| `model_G4_cyclic_grounding` | theorem | [L600](formal/Logos/GroundingFrontier.lean#L600) | `theorem model_G4_cyclic_grounding : ∃ (S : GroundingOrderSignature) (x y : S.Ent` | {}  |
| `model_G5_multiple_ultimate_grounds` | theorem | [L606](formal/Logos/GroundingFrontier.lean#L606) | `theorem model_G5_multiple_ultimate_grounds : ∃ (S : GroundingOrderSignature) (u₁` | {}  |
| `model_G6_unique_impersonal_ultimate_ground` | theorem | [L612](formal/Logos/GroundingFrontier.lean#L612) | `theorem model_G6_unique_impersonal_ultimate_ground : ∃ (M : ExtendedGroundingSig` | {}  |
| `model_G7_necessary_personal_ground` | theorem | [L618](formal/Logos/GroundingFrontier.lean#L618) | `theorem model_G7_necessary_personal_ground : ∃ (M : ExtendedGroundingSignature) ` | {}  |
| `model_G8_necessary_ground_without_ultimate` | theorem | [L636](formal/Logos/GroundingFrontier.lean#L636) | `theorem model_G8_necessary_ground_without_ultimate : ∃ (M : ModalGroundingSignat` | {}  |
| `model_G9_intentional_subject_with_impersonal_ground` | theorem | [L657](formal/Logos/GroundingFrontier.lean#L657) | `theorem model_G9_intentional_subject_with_impersonal_ground : ∃ (M : ExtendedGro` | {}  |
| `model_P1_impersonal_substrate` | theorem | [L368](formal/Logos/GroundingFrontier.lean#L368) | `theorem model_P1_impersonal_substrate : ∃ (M : ExtendedGroundingSignature) (u : ` | {}  |
| `model_P2_structural_realization` | theorem | [L389](formal/Logos/GroundingFrontier.lean#L389) | `theorem model_P2_structural_realization : ∃ (M : ExtendedGroundingSignature) (u ` | {}  |
| `model_P3_emergent_intentionality` | theorem | [L415](formal/Logos/GroundingFrontier.lean#L415) | `theorem model_P3_emergent_intentionality : ∃ (M : ExtendedGroundingSignature) (u` | {}  |
| `model_P4_multiple_impersonal_grounders` | theorem | [L438](formal/Logos/GroundingFrontier.lean#L438) | `theorem model_P4_multiple_impersonal_grounders : ∃ (M : ExtendedGroundingSignatu` | {}  |
| `model_P5_anonymous_ultimate_ground` | theorem | [L459](formal/Logos/GroundingFrontier.lean#L459) | `theorem model_P5_anonymous_ultimate_ground : ∃ (M : ExtendedGroundingSignature) ` | {}  |
| `performative_subject_and_nec_truth_do_not_force_necessary_entity` | theorem | [L484](formal/Logos/GroundingFrontier.lean#L484) | `theorem performative_subject_and_nec_truth_do_not_force_necessary_entity : ∃ (M ` | {}  |
| `quantifier_exchange_under_uniqueness` | theorem | [L207](formal/Logos/GroundingFrontier.lean#L207) | `theorem quantifier_exchange_under_uniqueness (M : ModalGroundingSignature) (φ : ` | {}  |
| `separation_G1_not_implies_G2` | theorem | [L124](formal/Logos/GroundingFrontier.lean#L124) | `theorem separation_G1_not_implies_G2 : ∃ (M : ModalGroundingSignature) (φ : M.Fo` | {}  |
| `ultimate_ground_does_not_imply_plurality` | theorem | [L557](formal/Logos/GroundingFrontier.lean#L557) | `theorem ultimate_ground_does_not_imply_plurality : ∃ (S : GroundingOrderSignatur` | {}  |
| `ultimate_ground_does_not_imply_uniqueness` | theorem | [L543](formal/Logos/GroundingFrontier.lean#L543) | `theorem ultimate_ground_does_not_imply_uniqueness : ∃ (S : GroundingOrderSignatu` | {}  |
| `uniform_ground_iff_worldwise_and_missing_horn` | theorem | [L195](formal/Logos/GroundingFrontier.lean#L195) | `theorem uniform_ground_iff_worldwise_and_missing_horn (M : ModalGroundingSignatu` | {}  |
| `worldwise_fails_to_derive_uniform_ground` | theorem | [L169](formal/Logos/GroundingFrontier.lean#L169) | `theorem worldwise_fails_to_derive_uniform_ground : ∃ (M : ModalGroundingSignatur` | {}  |

### `Logos.HardenedInvariance`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `AgentCausalSettlement` | def | [L345](formal/Logos/HardenedInvariance.lean#L345) | `def AgentCausalSettlement (Subject : Type) (s : Subject) (CausesAt : Subject → P` | {}  |
| `AgentInvariant` | def | [L102](formal/Logos/HardenedInvariance.lean#L102) | `def AgentInvariant (l : DependencyLayer) : Prop` | {}  |
| `AgentNeutralCore` | def | [L110](formal/Logos/HardenedInvariance.lean#L110) | `def AgentNeutralCore (l : DependencyLayer) : Prop` | {}  |
| `Checks` | inductive | [L373](formal/Logos/HardenedInvariance.lean#L373) | `inductive Checks : DeductiveContext → ProofTrace → Prop` | —  |
| `Develops` | def | [L403](formal/Logos/HardenedInvariance.lean#L403) | `def Develops (c : DeductiveContext) (t : ProofTrace) : Prop` | {}  |
| `FreeWillInvariant` | def | [L106](formal/Logos/HardenedInvariance.lean#L106) | `def FreeWillInvariant (l : DependencyLayer) : Prop` | {}  |
| `FreeWillNeutralCore` | def | [L114](formal/Logos/HardenedInvariance.lean#L114) | `def FreeWillNeutralCore (l : DependencyLayer) : Prop` | {}  |
| `HasAgent` | def | [L59](formal/Logos/HardenedInvariance.lean#L59) | `def HasAgent (r : ProofRegime) : Prop` | {}  |
| `HasFreeWill` | def | [L68](formal/Logos/HardenedInvariance.lean#L68) | `def HasFreeWill (r : ProofRegime) : Prop` | {}  |
| `HasIntentionality` | def | [L62](formal/Logos/HardenedInvariance.lean#L62) | `def HasIntentionality (r : ProofRegime) : Prop` | {}  |
| `HasLibertarianAgency` | def | [L71](formal/Logos/HardenedInvariance.lean#L71) | `def HasLibertarianAgency (r : ProofRegime) : Prop` | {}  |
| `IsDeterministic` | def | [L65](formal/Logos/HardenedInvariance.lean#L65) | `def IsDeterministic (r : ProofRegime) : Prop` | {}  |
| `LibertarianFreedom` | def | [L348](formal/Logos/HardenedInvariance.lean#L348) | `def LibertarianFreedom (Subject : Type) (s : Subject) (CausesAt : Subject → Prop` | {}  |
| `ProofConclusionIsLogicallyEntailed` | def | [L437](formal/Logos/HardenedInvariance.lean#L437) | `def ProofConclusionIsLogicallyEntailed (P : Prop) : Prop` | {}  |
| `ProofConclusionIsMetaphysicallyNecessary` | def | [L439](formal/Logos/HardenedInvariance.lean#L439) | `def ProofConclusionIsMetaphysicallyNecessary (_P : Prop) : Prop` | {}  |
| `ProofExists` | def | [L427](formal/Logos/HardenedInvariance.lean#L427) | `def ProofExists (P : Prop) : Prop` | {}  |
| `ProofIsCausallyDetermined` | def | [L435](formal/Logos/HardenedInvariance.lean#L435) | `def ProofIsCausallyDetermined (_t : ProofTrace) : Prop` | {}  |
| `ProofIsCorrect` | def | [L430](formal/Logos/HardenedInvariance.lean#L430) | `def ProofIsCorrect (P : Prop) : Prop` | {}  |
| `ProofIsValid` | def | [L432](formal/Logos/HardenedInvariance.lean#L432) | `def ProofIsValid (t : ProofTrace) (P : Prop) : Prop` | {}  |
| `ProofOccursInContext` | def | [L409](formal/Logos/HardenedInvariance.lean#L409) | `def ProofOccursInContext (c : DeductiveContext) (P : Prop) : Prop` | {}  |
| `ProofRegime` | inductive | [L51](formal/Logos/HardenedInvariance.lean#L51) | `inductive ProofRegime` | —  |
| `ProofTrace` | inductive | [L360](formal/Logos/HardenedInvariance.lean#L360) | `inductive ProofTrace` | —  |
| `RealizesAt` | inductive | [L380](formal/Logos/HardenedInvariance.lean#L380) | `inductive RealizesAt : DeductiveContext → ProofTrace → Prop → Prop` | —  |
| `RegimeAdmissible` | def | [L95](formal/Logos/HardenedInvariance.lean#L95) | `def RegimeAdmissible (r : ProofRegime) (l : DependencyLayer) : Prop` | {}  |
| `RequiresAgent` | def | [L75](formal/Logos/HardenedInvariance.lean#L75) | `def RequiresAgent (l : DependencyLayer) : Prop` | {}  |
| `RequiresFreeWill` | def | [L85](formal/Logos/HardenedInvariance.lean#L85) | `def RequiresFreeWill (l : DependencyLayer) : Prop` | {}  |
| `RequiresIntentionality` | def | [L80](formal/Logos/HardenedInvariance.lean#L80) | `def RequiresIntentionality (l : DependencyLayer) : Prop` | {}  |
| `RequiresLibertarianAgency` | def | [L90](formal/Logos/HardenedInvariance.lean#L90) | `def RequiresLibertarianAgency (l : DependencyLayer) : Prop` | {}  |
| `TraceConclusion` | def | [L366](formal/Logos/HardenedInvariance.lean#L366) | `def TraceConclusion (t : ProofTrace) : Prop` | {}  |
| `act_not_implies_person` | theorem | [L268](formal/Logos/HardenedInvariance.lean#L268) | `theorem act_not_implies_person : ∃ (Subject : Type) (s : Subject) (p : Prop) (Ac` | {}  |
| `agent_invariant_iff_agent_neutral_core` | theorem | [L118](formal/Logos/HardenedInvariance.lean#L118) | `theorem agent_invariant_iff_agent_neutral_core (l : DependencyLayer) : AgentInva` | {}  |
| `causal_determination_not_implies_logical_validity` | theorem | [L442](formal/Logos/HardenedInvariance.lean#L442) | `theorem causal_determination_not_implies_logical_validity : ∃ (t : ProofTrace) (` | {}  |
| `chooses_not_implies_agent_causal_settlement` | theorem | [L309](formal/Logos/HardenedInvariance.lean#L309) | `theorem chooses_not_implies_agent_causal_settlement : ∃ (Subject : Type) (s : Su` | {}  |
| `chooses_not_implies_modal_freedom` | theorem | [L300](formal/Logos/HardenedInvariance.lean#L300) | `theorem chooses_not_implies_modal_freedom : ∃ (Subject : Type) (s : Subject) (p ` | {}  |
| `chooses_not_implies_nondeterministic` | theorem | [L291](formal/Logos/HardenedInvariance.lean#L291) | `theorem chooses_not_implies_nondeterministic : ∃ (Subject : Type) (s : Subject) ` | {}  |
| `contextual_retorsion_datum` | theorem | [L527](formal/Logos/HardenedInvariance.lean#L527) | `theorem contextual_retorsion_datum : ¬ (∀ c : DeductiveContext, ¬ ProofOccursInC` | {}  |
| `cross_context_development_soundness` | theorem | [L415](formal/Logos/HardenedInvariance.lean#L415) | `theorem cross_context_development_soundness (c1 c2 : DeductiveContext) (t : Proo` | {}  |
| `first_agency_sensitive_layer_is_L1` | theorem | [L482](formal/Logos/HardenedInvariance.lean#L482) | `theorem first_agency_sensitive_layer_is_L1 : RequiresAgent DependencyLayer.L1_Pe` | {}  |
| `first_choice_sensitive_layer_is_L10` | theorem | [L501](formal/Logos/HardenedInvariance.lean#L501) | `theorem first_choice_sensitive_layer_is_L10 : RequiresFreeWill DependencyLayer.L` | {}  |
| `first_compatibilist_freewill_sensitive_layer_is_L11` | theorem | [L508](formal/Logos/HardenedInvariance.lean#L508) | `theorem first_compatibilist_freewill_sensitive_layer_is_L11 : RequiresFreeWill D` | {}  |
| `first_intentionality_sensitive_layer_is_L2` | theorem | [L488](formal/Logos/HardenedInvariance.lean#L488) | `theorem first_intentionality_sensitive_layer_is_L2 : RequiresIntentionality Depe` | {}  |
| `first_libertarian_sensitive_layer_is_L12` | theorem | [L515](formal/Logos/HardenedInvariance.lean#L515) | `theorem first_libertarian_sensitive_layer_is_L12 : RequiresLibertarianAgency Dep` | {}  |
| `first_substantive_personhood_sensitive_layer_is_L9` | theorem | [L494](formal/Logos/HardenedInvariance.lean#L494) | `theorem first_substantive_personhood_sensitive_layer_is_L9 : DependencyLayer.L9_` | {}  |
| `freeSubject_equiv_freeWill` | theorem | [L242](formal/Logos/HardenedInvariance.lean#L242) | `theorem freeSubject_equiv_freeWill (s : Logos.Agency.Subject) : Logos.Choice.Fre` | {Means, Subject}  |
| `freeSubject_not_implies_person` | theorem | [L255](formal/Logos/HardenedInvariance.lean#L255) | `theorem freeSubject_not_implies_person : ∃ (Subject : Type) (s : Subject) (Means` | {}  |
| `freewill_entails_intentionalSubject` | theorem | [L247](formal/Logos/HardenedInvariance.lean#L247) | `theorem freewill_entails_intentionalSubject (s : Logos.Agency.Subject) (h : Logo` | {Means, Subject}  |
| `freewill_invariant_iff_freewill_neutral_core` | theorem | [L153](formal/Logos/HardenedInvariance.lean#L153) | `theorem freewill_invariant_iff_freewill_neutral_core (l : DependencyLayer) : Fre` | {}  |
| `freewill_not_implies_agent_causal_settlement` | theorem | [L336](formal/Logos/HardenedInvariance.lean#L336) | `theorem freewill_not_implies_agent_causal_settlement : ∃ (Subject : Type) (s : S` | {}  |
| `freewill_not_implies_modal_freedom` | theorem | [L327](formal/Logos/HardenedInvariance.lean#L327) | `theorem freewill_not_implies_modal_freedom : ∃ (Subject : Type) (s : Subject) (H` | {}  |
| `freewill_not_implies_nondeterministic` | theorem | [L318](formal/Logos/HardenedInvariance.lean#L318) | `theorem freewill_not_implies_nondeterministic : ∃ (Subject : Type) (s : Subject)` | {}  |
| `libertarian_freedom_iff_agent_causal_settlement` | theorem | [L351](formal/Logos/HardenedInvariance.lean#L351) | `theorem libertarian_freedom_iff_agent_causal_settlement (Subject : Type) (s : Su` | {}  |
| `logical_validity_not_implies_metaphysical_necessity` | theorem | [L451](formal/Logos/HardenedInvariance.lean#L451) | `theorem logical_validity_not_implies_metaphysical_necessity : ∃ (t : ProofTrace)` | {}  |
| `person_entails_intentionalSubject` | theorem | [L237](formal/Logos/HardenedInvariance.lean#L237) | `theorem person_entails_intentionalSubject (s : Logos.Agency.Subject) (h : Logos.` | {Means, Subject}  |
| `proof_correctness_not_implies_freewill` | theorem | [L474](formal/Logos/HardenedInvariance.lean#L474) | `theorem proof_correctness_not_implies_freewill : ∃ (P : Prop), ProofIsCorrect P ` | {}  |
| `proof_occurrence_not_implies_freewill` | theorem | [L467](formal/Logos/HardenedInvariance.lean#L467) | `theorem proof_occurrence_not_implies_freewill : ∃ (c : DeductiveContext) (t : Pr` | {}  |
| `proof_occurrence_not_implies_intentional_agency` | theorem | [L460](formal/Logos/HardenedInvariance.lean#L460) | `theorem proof_occurrence_not_implies_intentional_agency : ∃ (c : DeductiveContex` | {}  |
| `realizesAt_conclusion` | theorem | [L396](formal/Logos/HardenedInvariance.lean#L396) | `theorem realizesAt_conclusion (c : DeductiveContext) (t : ProofTrace) (P : Prop)` | {}  |
| `realizesAt_sound` | theorem | [L389](formal/Logos/HardenedInvariance.lean#L389) | `theorem realizesAt_sound (c : DeductiveContext) (t : ProofTrace) (P : Prop) (h :` | {}  |
| `strict_core_inclusion` | theorem | [L173](formal/Logos/HardenedInvariance.lean#L173) | `theorem strict_core_inclusion : (∀ l, AgentNeutralCore l → FreeWillNeutralCore l` | {}  |

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

### `Logos.IndubitableNormativeFreeWill`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `AgentialDeonticAddress` | def | [L78](formal/Logos/IndubitableNormativeFreeWill.lean#L78) | `def AgentialDeonticAddress (s : Subject) (p q : Prop) : Prop` | {Means, Subject}  |
| `DeonticOpposition` | def | [L72](formal/Logos/IndubitableNormativeFreeWill.lean#L72) | `def DeonticOpposition (p q : Prop) : Prop` | {}  |
| `EstablishedRightWrong` | def | [L53](formal/Logos/IndubitableNormativeFreeWill.lean#L53) | `def EstablishedRightWrong : Prop` | {}  |
| `GenuineNormativity` | structure | [L84](formal/Logos/IndubitableNormativeFreeWill.lean#L84) | `structure GenuineNormativity (s : Subject) (p q : Prop) : Prop where` | —  |
| `IntelligibleRight` | def | [L42](formal/Logos/IndubitableNormativeFreeWill.lean#L42) | `def IntelligibleRight (s : Subject) (p : Prop) : Prop` | {Means, Subject}  |
| `NecessaryGenuineNormativity` | def | [L126](formal/Logos/IndubitableNormativeFreeWill.lean#L126) | `def NecessaryGenuineNormativity (World : Type) : Prop` | {Subject}  |
| `NormativeAgency` | def | [L91](formal/Logos/IndubitableNormativeFreeWill.lean#L91) | `def NormativeAgency (s : Subject) : Prop` | {Subject}  |
| `NormativeAlternative` | def | [L101](formal/Logos/IndubitableNormativeFreeWill.lean#L101) | `def NormativeAlternative (p q : Prop) : Prop` | {}  |
| `RealizedRight` | def | [L48](formal/Logos/IndubitableNormativeFreeWill.lean#L48) | `def RealizedRight (p : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `dnf1_denial_of_existence_violates_core` | theorem | [L154](formal/Logos/IndubitableNormativeFreeWill.lean#L154) | `theorem dnf1_denial_of_existence_violates_core (hDenial : ¬ EstablishedRightWron` | {}  |
| `dnf2_descriptive_value_lacks_prescriptive_force` | theorem | [L160](formal/Logos/IndubitableNormativeFreeWill.lean#L160) | `theorem dnf2_descriptive_value_lacks_prescriptive_force (is_evaluative_only : Pr` | {Means, Subject}  |
| `dnf3_impersonal_ought_fails_address` | theorem | [L172](formal/Logos/IndubitableNormativeFreeWill.lean#L172) | `theorem dnf3_impersonal_ought_fails_address (p q : Prop) (hNoAddress : ∀ s : Sub` | {Means, Subject}  |
| `dnf4_monolithic_command_lacks_opposition` | theorem | [L180](formal/Logos/IndubitableNormativeFreeWill.lean#L180) | `theorem dnf4_monolithic_command_lacks_opposition (p : Prop) (hNoAlternative : ∀ ` | {Subject}  |
| `dnf5_ungraspable_directive_is_not_agential_address` | theorem | [L189](formal/Logos/IndubitableNormativeFreeWill.lean#L189) | `theorem dnf5_ungraspable_directive_is_not_agential_address (s : Subject) (p q : ` | {Means, Subject}  |
| `dnf6_isolated_intelligibility_refutes_normativity` | theorem | [L197](formal/Logos/IndubitableNormativeFreeWill.lean#L197) | `theorem dnf6_isolated_intelligibility_refutes_normativity (s : Subject) (p q : P` | {Means, Subject}  |
| `dnf7_cannot_deny_choice_from_co_meaning` | theorem | [L206](formal/Logos/IndubitableNormativeFreeWill.lean#L206) | `theorem dnf7_cannot_deny_choice_from_co_meaning (s : Subject) (p q : Prop) (hMea` | {Means, Subject}  |
| `dnf8_cannot_deny_freewill_from_choice` | theorem | [L214](formal/Logos/IndubitableNormativeFreeWill.lean#L214) | `theorem dnf8_cannot_deny_freewill_from_choice (s : Subject) (p q : Prop) (hChoic` | {Means, Subject}  |
| `impossibility_of_denying_chooses` | theorem | [L226](formal/Logos/IndubitableNormativeFreeWill.lean#L226) | `theorem impossibility_of_denying_chooses : ¬ ∃ (Subj : Type) (MeansRel : Subj → ` | {}  |
| `impossibility_of_denying_freewill` | theorem | [L235](formal/Logos/IndubitableNormativeFreeWill.lean#L235) | `theorem impossibility_of_denying_freewill : ¬ ∃ (Subj : Type) (ChoosesRel : Subj` | {}  |
| `indubitable_normative_free_will` | theorem | [L115](formal/Logos/IndubitableNormativeFreeWill.lean#L115) | `theorem indubitable_normative_free_will {s : Subject} {p q : Prop} (h : GenuineN` | {Means, Subject}  |
| `intelligibility_not_trivially_realization` | theorem | [L58](formal/Logos/IndubitableNormativeFreeWill.lean#L58) | `theorem intelligibility_not_trivially_realization : ∃ (Subj : Type) (MeansRel : ` | {}  |
| `necessary_normativity_implies_necessary_free_will` | theorem | [L131](formal/Logos/IndubitableNormativeFreeWill.lean#L131) | `theorem necessary_normativity_implies_necessary_free_will {World : Type} (hNec :` | {Means, Subject}  |
| `normative_agency_reduction` | theorem | [L94](formal/Logos/IndubitableNormativeFreeWill.lean#L94) | `theorem normative_agency_reduction (s : Subject) (p q : Prop) (h : GenuineNormat` | {Subject}  |
| `normative_alternative_reduction` | theorem | [L104](formal/Logos/IndubitableNormativeFreeWill.lean#L104) | `theorem normative_alternative_reduction (s : Subject) (p q : Prop) (h : GenuineN` | {Subject}  |

### `Logos.Initiation`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Branches` | def | [L23](formal/Logos/Initiation.lean#L23) | `def Branches {α β : Type} (R : α → β → Prop) : Prop` | {}  |
| `IsTransfer` | def | [L19](formal/Logos/Initiation.lean#L19) | `def IsTransfer {α β : Type} (R : α → β → Prop) : Prop` | {}  |
| `branches_not_transfer` | theorem | [L27](formal/Logos/Initiation.lean#L27) | `theorem branches_not_transfer {α β : Type} {R : α → β → Prop} (h : Branches R) :` | {} → C63 |

### `Logos.JointForcing`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `A1_AxIntentionalChoice` | def | [L163](formal/Logos/JointForcing.lean#L163) | `def A1_AxIntentionalChoice (J : JointSignature) : Prop` | {}  |
| `A1_not_implies_A2` | theorem | [L230](formal/Logos/JointForcing.lean#L230) | `theorem A1_not_implies_A2 : ∃ (J : JointSignature), GammaCore J ∧ A1_AxIntention` | {CL}  |
| `A2_AxActPolarity` | def | [L167](formal/Logos/JointForcing.lean#L167) | `def A2_AxActPolarity (J : JointSignature) : Prop` | {}  |
| `A2_implies_A1` | theorem | [L217](formal/Logos/JointForcing.lean#L217) | `theorem A2_implies_A1 (J : JointSignature) (hA2 : A2_AxActPolarity J) : A1_AxInt` | {}  |
| `A3_AxGlobalGround` | def | [L171](formal/Logos/JointForcing.lean#L171) | `def A3_AxGlobalGround (J : JointSignature) : Prop` | {}  |
| `A4_Truthmaker` | def | [L175](formal/Logos/JointForcing.lean#L175) | `def A4_Truthmaker (J : JointSignature) : Prop` | {}  |
| `A5_GroundPrincipleProp` | def | [L179](formal/Logos/JointForcing.lean#L179) | `def A5_GroundPrincipleProp (J : JointSignature) : Prop` | {}  |
| `A6_A7_synergistic_forcing` | theorem | [L296](formal/Logos/JointForcing.lean#L296) | `theorem A6_A7_synergistic_forcing (J : JointSignature) (hRetBridgeObj : J.Claims` | {}  |
| `A6_alone_insufficient` | theorem | [L313](formal/Logos/JointForcing.lean#L313) | `theorem A6_alone_insufficient : ∃ (J : JointSignature), GammaCore J ∧ A6_univers` | {}  |
| `A6_universal_thesis_claims_objectivity` | def | [L183](formal/Logos/JointForcing.lean#L183) | `def A6_universal_thesis_claims_objectivity (J : JointSignature) : Prop` | {}  |
| `A7_alone_insufficient` | theorem | [L356](formal/Logos/JointForcing.lean#L356) | `theorem A7_alone_insufficient : ∃ (J : JointSignature), GammaCore J ∧ A7_transce` | {}  |
| `A7_transcendental_reflection_intentional` | def | [L187](formal/Logos/JointForcing.lean#L187) | `def A7_transcendental_reflection_intentional (J : JointSignature) : Prop` | {}  |
| `A8_AxTwoSubjects` | def | [L191](formal/Logos/JointForcing.lean#L191) | `def A8_AxTwoSubjects (J : JointSignature) : Prop` | {}  |
| `A9_AxPersonalGround` | def | [L195](formal/Logos/JointForcing.lean#L195) | `def A9_AxPersonalGround (J : JointSignature) : Prop` | {}  |
| `Act` | def | [L110](formal/Logos/JointForcing.lean#L110) | `def Act (J : JointSignature) (s : J.Subject) (p : Prop) : Prop` | {}  |
| `Chooses` | def | [L113](formal/Logos/JointForcing.lean#L113) | `def Chooses (J : JointSignature) (s : J.Subject) (p q : Prop) : Prop` | {}  |
| `ContingentContentExists` | def | [L141](formal/Logos/JointForcing.lean#L141) | `def ContingentContentExists (J : JointSignature) : Prop` | {}  |
| `CoreDatumHolds` | def | [L135](formal/Logos/JointForcing.lean#L135) | `def CoreDatumHolds (J : JointSignature) : Prop` | {}  |
| `GammaCore` | def | [L151](formal/Logos/JointForcing.lean#L151) | `def GammaCore (J : JointSignature) : Prop` | {}  |
| `J_standard` | def | [L882](formal/Logos/JointForcing.lean#L882) | `def J_standard : JointSignature` | {}  |
| `JointSignature` | structure | [L70](formal/Logos/JointForcing.lean#L70) | `structure JointSignature where` | —  |
| `Love` | def | [L128](formal/Logos/JointForcing.lean#L128) | `def Love (J : JointSignature) (s₁ s₂ : J.Subject) : Prop` | {}  |
| `MoralDistinctionHolds` | def | [L144](formal/Logos/JointForcing.lean#L144) | `def MoralDistinctionHolds (J : JointSignature) : Prop` | {}  |
| `NecessaryEntity` | def | [L116](formal/Logos/JointForcing.lean#L116) | `def NecessaryEntity (J : JointSignature) (e : J.Entity) : Prop` | {}  |
| `NecessarySubject` | def | [L119](formal/Logos/JointForcing.lean#L119) | `def NecessarySubject (J : JointSignature) (s : J.Subject) : Prop` | {}  |
| `NecessaryTruthExists` | def | [L138](formal/Logos/JointForcing.lean#L138) | `def NecessaryTruthExists (J : JointSignature) : Prop` | {}  |
| `Neg_A1` | def | [L199](formal/Logos/JointForcing.lean#L199) | `def Neg_A1 (J : JointSignature) : Prop` | {}  |
| `Neg_A2` | def | [L200](formal/Logos/JointForcing.lean#L200) | `def Neg_A2 (J : JointSignature) : Prop` | {}  |
| `Neg_A3` | def | [L201](formal/Logos/JointForcing.lean#L201) | `def Neg_A3 (J : JointSignature) : Prop` | {}  |
| `Neg_A4` | def | [L202](formal/Logos/JointForcing.lean#L202) | `def Neg_A4 (J : JointSignature) : Prop` | {}  |
| `Neg_A5` | def | [L203](formal/Logos/JointForcing.lean#L203) | `def Neg_A5 (J : JointSignature) : Prop` | {}  |
| `Neg_A6` | def | [L204](formal/Logos/JointForcing.lean#L204) | `def Neg_A6 (J : JointSignature) : Prop` | {}  |
| `Neg_A7` | def | [L205](formal/Logos/JointForcing.lean#L205) | `def Neg_A7 (J : JointSignature) : Prop` | {}  |
| `Neg_A8` | def | [L206](formal/Logos/JointForcing.lean#L206) | `def Neg_A8 (J : JointSignature) : Prop` | {}  |
| `Neg_A9` | def | [L207](formal/Logos/JointForcing.lean#L207) | `def Neg_A9 (J : JointSignature) : Prop` | {}  |
| `NonTrivialOntology` | def | [L289](formal/Logos/JointForcing.lean#L289) | `def NonTrivialOntology (J : JointSignature) : Prop` | {}  |
| `PersonalFeatureExists` | def | [L147](formal/Logos/JointForcing.lean#L147) | `def PersonalFeatureExists (J : JointSignature) : Prop` | {}  |
| `UltimateGround` | def | [L125](formal/Logos/JointForcing.lean#L125) | `def UltimateGround (J : JointSignature) (e : J.Entity) : Prop` | {}  |
| `UniqueNecessaryEntity` | def | [L122](formal/Logos/JointForcing.lean#L122) | `def UniqueNecessaryEntity (J : JointSignature) : Prop` | {}  |
| `agency_not_implies_global_ground` | theorem | [L564](formal/Logos/JointForcing.lean#L564) | `theorem agency_not_implies_global_ground : ∃ (J : JointSignature), GammaCore J ∧` | {}  |
| `choice_and_global_ground_not_implies_necessary_subject` | theorem | [L771](formal/Logos/JointForcing.lean#L771) | `theorem choice_and_global_ground_not_implies_necessary_subject : ∃ (J : JointSig` | {}  |
| `empty_inconsistency_basis` | theorem | [L946](formal/Logos/JointForcing.lean#L946) | `theorem empty_inconsistency_basis : ¬ ∃ (Δ : List Prop), (∀ p ∈ Δ, p = True) ∧ (` | {CL}  |
| `global_ground_and_personal_ground_not_implies_personal_ultimate` | theorem | [L510](formal/Logos/JointForcing.lean#L510) | `theorem global_ground_and_personal_ground_not_implies_personal_ultimate : ∃ (J :` | {}  |
| `global_ground_and_personal_ground_not_implies_unique` | theorem | [L458](formal/Logos/JointForcing.lean#L458) | `theorem global_ground_and_personal_ground_not_implies_unique : ∃ (J : JointSigna` | {}  |
| `joint_forcing_synthesis` | theorem | [L970](formal/Logos/JointForcing.lean#L970) | `theorem joint_forcing_synthesis : -- 1. Contextual Redundancy (∀ J, A2_AxActPola` | {CL}  |
| `joint_satisfiability_synthesis` | theorem | [L917](formal/Logos/JointForcing.lean#L917) | `theorem joint_satisfiability_synthesis : GammaCore J_standard ∧ A1_AxIntentional` | {}  |
| `plurality_and_global_ground_not_implies_personal_ground` | theorem | [L613](formal/Logos/JointForcing.lean#L613) | `theorem plurality_and_global_ground_not_implies_personal_ground : ∃ (J : JointSi` | {}  |
| `plurality_and_personal_ground_not_implies_love` | theorem | [L721](formal/Logos/JointForcing.lean#L721) | `theorem plurality_and_personal_ground_not_implies_love : ∃ (J : JointSignature),` | {}  |
| `plurality_and_personal_ground_not_implies_plural_necessary_persons` | theorem | [L663](formal/Logos/JointForcing.lean#L663) | `theorem plurality_and_personal_ground_not_implies_plural_necessary_persons : ∃ (` | {}  |
| `retorsion_not_implies_choice` | theorem | [L827](formal/Logos/JointForcing.lean#L827) | `theorem retorsion_not_implies_choice : ∃ (J : JointSignature), GammaCore J ∧ A6_` | {}  |
| `truthmaker_and_ground_prop_not_implies_global_ground` | theorem | [L405](formal/Logos/JointForcing.lean#L405) | `theorem truthmaker_and_ground_prop_not_implies_global_ground : ∃ (J : JointSigna` | {}  |

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

### `Logos.ModalCreationAgency`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `ChoosesAt` | def | [L74](formal/Logos/ModalCreationAgency.lean#L74) | `def ChoosesAt (World Subject : Type) (MeansAt : World → Subject → Prop → Prop) (` | {}  |
| `ClaimC1_ActualNoCreation` | def | [L207](formal/Logos/ModalCreationAgency.lean#L207) | `def ClaimC1_ActualNoCreation (World Entity : Type) (actualWorld : World) (Create` | {}  |
| `ClaimC2_ModalNoCreation` | def | [L212](formal/Logos/ModalCreationAgency.lean#L212) | `def ClaimC2_ModalNoCreation (World Entity : Type) (frame : KripkeFrame World) (a` | {}  |
| `ClaimC3_NoContingentEntitiesPossible` | def | [L218](formal/Logos/ModalCreationAgency.lean#L218) | `def ClaimC3_NoContingentEntitiesPossible (World Entity : Type) (frame : KripkeFr` | {}  |
| `DeterministicModalModel` | structure | [L134](formal/Logos/ModalCreationAgency.lean#L134) | `structure DeterministicModalModel where` | —  |
| `FreeVoluntaryNoCreation` | def | [L243](formal/Logos/ModalCreationAgency.lean#L243) | `def FreeVoluntaryNoCreation (World Entity Subject : Type) (frame : KripkeFrame W` | {}  |
| `FreeWillAt` | def | [L81](formal/Logos/ModalCreationAgency.lean#L81) | `def FreeWillAt (World Subject : Type) (MeansAt : World → Subject → Prop → Prop) ` | {}  |
| `Incompatible` | def | [L70](formal/Logos/ModalCreationAgency.lean#L70) | `def Incompatible (p q : Prop) : Prop` | {}  |
| `MC4_Signature` | structure | [L338](formal/Logos/ModalCreationAgency.lean#L338) | `structure MC4_Signature where` | —  |
| `MC5_Signature` | structure | [L389](formal/Logos/ModalCreationAgency.lean#L389) | `structure MC5_Signature where` | —  |
| `ModalFreeWill` | structure | [L102](formal/Logos/ModalCreationAgency.lean#L102) | `structure ModalFreeWill (World Subject : Type)` | —  |
| `ModelDeterministicChoice` | def | [L158](formal/Logos/ModalCreationAgency.lean#L158) | `def ModelDeterministicChoice : DeterministicModalModel where World` | {}  |
| `ModelMC5` | def | [L414](formal/Logos/ModalCreationAgency.lean#L414) | `def ModelMC5 : MC5_Signature where World` | {}  |
| `PassiveNoCreationAt` | def | [L230](formal/Logos/ModalCreationAgency.lean#L230) | `def PassiveNoCreationAt (World Entity : Type) (CreatesAt : World → Entity → Enti` | {}  |
| `TargetA_NecessaryBeing` | def | [L42](formal/Logos/ModalCreationAgency.lean#L42) | `def TargetA_NecessaryBeing (World Entity : Type) (ExistsAt : World → Entity → Pr` | {}  |
| `TargetB_NecessaryPerson` | structure | [L48](formal/Logos/ModalCreationAgency.lean#L48) | `structure TargetB_NecessaryPerson (World Entity Subject : Type)` | —  |
| `TargetC_NecessaryFreeAgent` | structure | [L88](formal/Logos/ModalCreationAgency.lean#L88) | `structure TargetC_NecessaryFreeAgent (World Entity Subject : Type)` | —  |
| `VoluntaryNoCreationAt` | def | [L235](formal/Logos/ModalCreationAgency.lean#L235) | `def VoluntaryNoCreationAt (World Entity Subject : Type) (CreatesAt : World → Ent` | {}  |
| `freeWill_not_entails_modal_alternatives` | theorem | [L185](formal/Logos/ModalCreationAgency.lean#L185) | `theorem freeWill_not_entails_modal_alternatives : ∃ M : DeterministicModalModel,` | {}  |
| `free_voluntary_implies_voluntary` | theorem | [L252](formal/Logos/ModalCreationAgency.lean#L252) | `theorem free_voluntary_implies_voluntary (World Entity Subject : Type) (frame : ` | {}  |
| `modal_freedom_implies_local_freedom` | theorem | [L114](formal/Logos/ModalCreationAgency.lean#L114) | `theorem modal_freedom_implies_local_freedom (World Subject : Type) (frame : Krip` | {}  |
| `modal_freedom_yields_contingency_of_creation` | theorem | [L482](formal/Logos/ModalCreationAgency.lean#L482) | `theorem modal_freedom_yields_contingency_of_creation (World Entity Subject : Typ` | {}  |
| `model_MC1_necessary_impersonal_consistent` | theorem | [L292](formal/Logos/ModalCreationAgency.lean#L292) | `theorem model_MC1_necessary_impersonal_consistent : ∃ (World Entity Subject : Ty` | {}  |
| `model_MC2_necessary_person_no_agency_consistent` | theorem | [L304](formal/Logos/ModalCreationAgency.lean#L304) | `theorem model_MC2_necessary_person_no_agency_consistent : ∃ (World Entity Subjec` | {}  |
| `model_MC3_fixed_choice_consistent` | theorem | [L321](formal/Logos/ModalCreationAgency.lean#L321) | `theorem model_MC3_fixed_choice_consistent : ∃ M : DeterministicModalModel, (∀ w,` | {}  |
| `model_MC4_necessary_creation_consistent` | theorem | [L360](formal/Logos/ModalCreationAgency.lean#L360) | `theorem model_MC4_necessary_creation_consistent : ∃ _M : MC4_Signature, True` | {}  |
| `model_MC5_contingent_creation_consistent` | theorem | [L439](formal/Logos/ModalCreationAgency.lean#L439) | `theorem model_MC5_contingent_creation_consistent : ∃ _M : MC5_Signature, True` | {}  |
| `model_MC6_passive_no_creation_accessible` | theorem | [L446](formal/Logos/ModalCreationAgency.lean#L446) | `theorem model_MC6_passive_no_creation_accessible : ∃ (World Entity Subject : Typ` | {}  |
| `necessary_free_agent_not_entails_contingent_creation` | theorem | [L470](formal/Logos/ModalCreationAgency.lean#L470) | `theorem necessary_free_agent_not_entails_contingent_creation : ¬ (∀ (S : MC4_Sig` | {}  |
| `passive_not_entails_voluntary` | theorem | [L270](formal/Logos/ModalCreationAgency.lean#L270) | `theorem passive_not_entails_voluntary : ∃ (World Entity Subject : Type) (Creates` | {}  |
| `voluntary_implies_passive` | theorem | [L261](formal/Logos/ModalCreationAgency.lean#L261) | `theorem voluntary_implies_passive (World Entity Subject : Type) (CreatesAt : Wor` | {}  |

### `Logos.ModalPossibilityFrontier`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Aseity` | def | [L122](formal/Logos/ModalPossibilityFrontier.lean#L122) | `def Aseity (World Entity : Type) (ExtDepAt : World → Entity → Prop) (g : Entity)` | {}  |
| `CausalDeterminism` | def | [L169](formal/Logos/ModalPossibilityFrontier.lean#L169) | `def CausalDeterminism (World Subject : Type) (HistoryAt : World → Prop) (WillsAt` | {}  |
| `CompleteStateDeterminism` | def | [L196](formal/Logos/ModalPossibilityFrontier.lean#L196) | `def CompleteStateDeterminism (World Entity Subject : Type) (ExtCirc : World → Pr` | {}  |
| `DeterminingPSR` | def | [L181](formal/Logos/ModalPossibilityFrontier.lean#L181) | `def DeterminingPSR (World Subject : Type) (ReasonsAt : World → Subject → Prop) (` | {}  |
| `ImmutableNature` | def | [L114](formal/Logos/ModalPossibilityFrontier.lean#L114) | `def ImmutableNature (World Entity : Type) (NatureAt : World → Entity → Prop) (g ` | {}  |
| `ImmutableWill` | def | [L118](formal/Logos/ModalPossibilityFrontier.lean#L118) | `def ImmutableWill (World Subject : Type) (WillsAt : World → Subject → Prop → Pro` | {}  |
| `Level1_OutcomeAlternative` | def | [L295](formal/Logos/ModalPossibilityFrontier.lean#L295) | `def Level1_OutcomeAlternative (World : Type) (OutcomeAt : World → Prop) (v u : W` | {}  |
| `Level2_ActAlternative` | def | [L298](formal/Logos/ModalPossibilityFrontier.lean#L298) | `def Level2_ActAlternative (World Subject : Type) (ActAt : World → Subject → Prop` | {}  |
| `Level3_VolitionAlternative` | def | [L302](formal/Logos/ModalPossibilityFrontier.lean#L302) | `def Level3_VolitionAlternative (World Subject : Type) (WillsAt : World → Subject` | {}  |
| `Level4_AgentCausalAlternative` | def | [L306](formal/Logos/ModalPossibilityFrontier.lean#L306) | `def Level4_AgentCausalAlternative (World Entity Subject : Type) (ExtCirc : World` | {}  |
| `MissingModalSettlement` | def | [L321](formal/Logos/ModalPossibilityFrontier.lean#L321) | `def MissingModalSettlement (World Subject : Type) (frame : KripkeFrame World) (a` | {}  |
| `NecessaryKnowledge` | def | [L106](formal/Logos/ModalPossibilityFrontier.lean#L106) | `def NecessaryKnowledge (World Subject : Type) (KnowsAt : World → Subject → Prop ` | {}  |
| `NecessaryRationality` | def | [L102](formal/Logos/ModalPossibilityFrontier.lean#L102) | `def NecessaryRationality (World Subject : Type) (IsRationalAt : World → Subject ` | {}  |
| `PerfectGoodness` | def | [L110](formal/Logos/ModalPossibilityFrontier.lean#L110) | `def PerfectGoodness (World Subject : Type) (IsGoodAt : World → Subject → Prop) (` | {}  |
| `ReasonDeterminism` | def | [L175](formal/Logos/ModalPossibilityFrontier.lean#L175) | `def ReasonDeterminism (World Subject : Type) (ReasonsAt : World → Subject → Prop` | {}  |
| `RigidAgent` | structure | [L45](formal/Logos/ModalPossibilityFrontier.lean#L45) | `structure RigidAgent (World Entity Subject : Type)` | —  |
| `SameExternalCircumstances` | def | [L65](formal/Logos/ModalPossibilityFrontier.lean#L65) | `def SameExternalCircumstances (World : Type) (ExtCirc : World → Prop) (w u : Wor` | {}  |
| `SameHistory` | def | [L71](formal/Logos/ModalPossibilityFrontier.lean#L71) | `def SameHistory (World : Type) (HistoryAt : World → Prop) (w u : World) : Prop` | {}  |
| `SameInternalState` | def | [L77](formal/Logos/ModalPossibilityFrontier.lean#L77) | `def SameInternalState (World Subject : Type) (InternalStateAt : World → Subject ` | {}  |
| `SameIntrinsicNature` | def | [L74](formal/Logos/ModalPossibilityFrontier.lean#L74) | `def SameIntrinsicNature (World Entity : Type) (NatureAt : World → Entity → Prop)` | {}  |
| `SameReasons` | def | [L68](formal/Logos/ModalPossibilityFrontier.lean#L68) | `def SameReasons (World Subject : Type) (ReasonsAt : World → Subject → Prop) (s :` | {}  |
| `SameTotalDeliberativeState` | structure | [L80](formal/Logos/ModalPossibilityFrontier.lean#L80) | `structure SameTotalDeliberativeState (World Entity Subject : Type)` | —  |
| `StrictDeterminism` | def | [L166](formal/Logos/ModalPossibilityFrontier.lean#L166) | `def StrictDeterminism (World : Type) (frame : KripkeFrame World) (actualWorld : ` | {}  |
| `causal_determinism_modal_collapse` | theorem | [L207](formal/Logos/ModalPossibilityFrontier.lean#L207) | `theorem causal_determinism_modal_collapse (World Subject : Type) (frame : Kripke` | {}  |
| `determining_psr_iff_reason_determinism` | theorem | [L188](formal/Logos/ModalPossibilityFrontier.lean#L188) | `theorem determining_psr_iff_reason_determinism (World Subject : Type) (ReasonsAt` | {}  |
| `determining_psr_incompatible_with_modal_freedom` | theorem | [L241](formal/Logos/ModalPossibilityFrontier.lean#L241) | `theorem determining_psr_incompatible_with_modal_freedom (World Subject : Type) (` | {}  |
| `immutable_will_incompatible_with_contingent_act` | theorem | [L264](formal/Logos/ModalPossibilityFrontier.lean#L264) | `theorem immutable_will_incompatible_with_contingent_act (World Subject : Type) (` | {}  |
| `model_MC13_consistent` | theorem | [L351](formal/Logos/ModalPossibilityFrontier.lean#L351) | `theorem model_MC13_consistent : ∃ (World Subject : Type) (ExtCirc : World → Prop` | {}  |
| `model_MC14_consistent` | theorem | [L360](formal/Logos/ModalPossibilityFrontier.lean#L360) | `theorem model_MC14_consistent : ∃ (World Subject : Type) (ExtCirc : World → Prop` | {}  |
| `model_MC15_consistent` | theorem | [L370](formal/Logos/ModalPossibilityFrontier.lean#L370) | `theorem model_MC15_consistent : ∃ (World Subject : Type) (ExtCirc : World → Prop` | {}  |
| `model_MC16_consistent` | theorem | [L383](formal/Logos/ModalPossibilityFrontier.lean#L383) | `theorem model_MC16_consistent : ∃ (World Entity Subject : Type) (ExtCirc : World` | {}  |
| `model_MC17_consistent` | theorem | [L398](formal/Logos/ModalPossibilityFrontier.lean#L398) | `theorem model_MC17_consistent : ∃ (World Entity Subject : Type) (ExistsAt : Worl` | {}  |
| `model_MC18_consistent` | theorem | [L420](formal/Logos/ModalPossibilityFrontier.lean#L420) | `theorem model_MC18_consistent : ∃ (World Subject : Type) (InfoAt : World → Subje` | {}  |
| `model_MC19_consistent` | theorem | [L431](formal/Logos/ModalPossibilityFrontier.lean#L431) | `theorem model_MC19_consistent : ∃ (World Subject : Type) (IsGoodAt : World → Sub` | {}  |
| `model_MC20_consistent` | theorem | [L440](formal/Logos/ModalPossibilityFrontier.lean#L440) | `theorem model_MC20_consistent : ∃ (World Entity Subject : Type) (NatureAt : Worl` | {}  |
| `model_MC21_consistent` | theorem | [L449](formal/Logos/ModalPossibilityFrontier.lean#L449) | `theorem model_MC21_consistent : ∃ (World Entity Subject : Type) (ExtDepAt : Worl` | {}  |
| `model_MC22_consistent` | theorem | [L458](formal/Logos/ModalPossibilityFrontier.lean#L458) | `theorem model_MC22_consistent : ∃ (World Entity Subject : Type) (ExtCirc : World` | {}  |
| `model_MC23_consistent` | theorem | [L473](formal/Logos/ModalPossibilityFrontier.lean#L473) | `theorem model_MC23_consistent : ∃ (World Subject : Type) (Circumstance : World →` | {}  |
| `model_MC24_consistent` | theorem | [L486](formal/Logos/ModalPossibilityFrontier.lean#L486) | `theorem model_MC24_consistent : ∃ (World Subject : Type) (frame : KripkeFrame Wo` | {CL}  |
| `model_MC25_consistent` | theorem | [L504](formal/Logos/ModalPossibilityFrontier.lean#L504) | `theorem model_MC25_consistent : ∃ (World Subject : Type) (frame : KripkeFrame Wo` | {}  |
| `model_MC26_consistent` | theorem | [L520](formal/Logos/ModalPossibilityFrontier.lean#L520) | `theorem model_MC26_consistent : ∃ (World Subject : Type) (frame : KripkeFrame Wo` | {}  |
| `model_MC27_consistent` | theorem | [L532](formal/Logos/ModalPossibilityFrontier.lean#L532) | `theorem model_MC27_consistent : ∃ (World Entity : Type) (frame : KripkeFrame Wor` | {}  |
| `model_MC28_consistent` | theorem | [L544](formal/Logos/ModalPossibilityFrontier.lean#L544) | `theorem model_MC28_consistent : ∃ (World Entity : Type) (frame : KripkeFrame Wor` | {}  |
| `model_MC29_consistent` | theorem | [L554](formal/Logos/ModalPossibilityFrontier.lean#L554) | `theorem model_MC29_consistent : ∃ (World Entity Subject : Type) (frame : KripkeF` | {}  |
| `model_MC30_consistent` | theorem | [L566](formal/Logos/ModalPossibilityFrontier.lean#L566) | `theorem model_MC30_consistent : ∃ (World Entity Subject : Type) (frame : KripkeF` | {}  |
| `necessary_knowledge_not_entails_necessary_will` | theorem | [L127](formal/Logos/ModalPossibilityFrontier.lean#L127) | `theorem necessary_knowledge_not_entails_necessary_will : ∃ (World Subject : Type` | {CL}  |
| `necessary_rationality_not_entails_necessary_act` | theorem | [L142](formal/Logos/ModalPossibilityFrontier.lean#L142) | `theorem necessary_rationality_not_entails_necessary_act : ∃ (World Subject : Typ` | {}  |
| `reason_determinism_modal_collapse` | theorem | [L221](formal/Logos/ModalPossibilityFrontier.lean#L221) | `theorem reason_determinism_modal_collapse (World Subject : Type) (frame : Kripke` | {}  |
| `target_contingent_creation_iff_missing_modal_settlement` | theorem | [L332](formal/Logos/ModalPossibilityFrontier.lean#L332) | `theorem target_contingent_creation_iff_missing_modal_settlement (World Subject :` | {}  |

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

### `Logos.NegativeRetorsionAudit`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `CertConclusion` | def | [L401](formal/Logos/NegativeRetorsionAudit.lean#L401) | `def CertConclusion : FormalProofCert → Prop | FormalProofCert.axiomStep c => c` | {}  |
| `DiagonalSpec` | structure | [L516](formal/Logos/NegativeRetorsionAudit.lean#L516) | `structure DiagonalSpec (Subject : Type) (Means : Subject → Prop → Prop) where` | —  |
| `FormalProofCert` | inductive | [L395](formal/Logos/NegativeRetorsionAudit.lean#L395) | `inductive FormalProofCert : Type` | —  |
| `NegativeRetorsionSignature` | structure | [L66](formal/Logos/NegativeRetorsionAudit.lean#L66) | `structure NegativeRetorsionSignature where` | —  |
| `NoI_canonical` | def | [L47](formal/Logos/NegativeRetorsionAudit.lean#L47) | `def NoI_canonical : Prop` | {Means, Subject}  |
| `NoI_pointwise_canonical` | def | [L50](formal/Logos/NegativeRetorsionAudit.lean#L50) | `def NoI_pointwise_canonical : Prop` | {Means, Subject}  |
| `P_canonical` | def | [L44](formal/Logos/NegativeRetorsionAudit.lean#L44) | `def P_canonical : Prop` | {Means, Subject}  |
| `canonical_act_noi_proves_P` | theorem | [L345](formal/Logos/NegativeRetorsionAudit.lean#L345) | `theorem canonical_act_noi_proves_P (s : Subject) : Act s NoI_canonical → P_canon` | {Initiates, Means, State, Subject}  |
| `canonical_act_noi_refutes_noi` | theorem | [L352](formal/Logos/NegativeRetorsionAudit.lean#L352) | `theorem canonical_act_noi_refutes_noi (s : Subject) : Act s NoI_canonical → ¬ No` | {Initiates, Means, State, Subject}  |
| `canonical_asserts_noi_selfRefutes` | theorem | [L269](formal/Logos/NegativeRetorsionAudit.lean#L269) | `theorem canonical_asserts_noi_selfRefutes (s : Subject) : Asserts s NoI_canonica` | {Initiates, Means, State, Subject}  |
| `canonical_exists_asserts_noi_selfRefutes` | theorem | [L280](formal/Logos/NegativeRetorsionAudit.lean#L280) | `theorem canonical_exists_asserts_noi_selfRefutes : (∃ s : Subject, Asserts s NoI` | {Initiates, Means, State, Subject}  |
| `canonical_means_noi_proves_P` | theorem | [L220](formal/Logos/NegativeRetorsionAudit.lean#L220) | `theorem canonical_means_noi_proves_P (s : Subject) : Means s NoI_canonical → P_c` | {Means, Subject}  |
| `canonical_means_noi_refutes_noi` | theorem | [L227](formal/Logos/NegativeRetorsionAudit.lean#L227) | `theorem canonical_means_noi_refutes_noi (s : Subject) : Means s NoI_canonical → ` | {Means, Subject}  |
| `canonical_noi_contradicts_a17` | theorem | [L186](formal/Logos/NegativeRetorsionAudit.lean#L186) | `theorem canonical_noi_contradicts_a17 : NoI_canonical → False` | {transcendental_reflection_intentional, DependsOn, Means, Subject}  |
| `canonical_noi_implies_not_act` | theorem | [L331](formal/Logos/NegativeRetorsionAudit.lean#L331) | `theorem canonical_noi_implies_not_act (s : Subject) : NoI_canonical → ¬ Act s No` | {Initiates, Means, State, Subject}  |
| `canonical_noi_implies_not_asserts` | theorem | [L252](formal/Logos/NegativeRetorsionAudit.lean#L252) | `theorem canonical_noi_implies_not_asserts (s : Subject) : NoI_canonical → ¬ Asse` | {Initiates, Means, State, Subject}  |
| `canonical_noi_implies_not_exists_act` | theorem | [L338](formal/Logos/NegativeRetorsionAudit.lean#L338) | `theorem canonical_noi_implies_not_exists_act : NoI_canonical → ¬ ∃ s : Subject, ` | {Initiates, Means, State, Subject}  |
| `canonical_noi_implies_not_exists_asserts` | theorem | [L261](formal/Logos/NegativeRetorsionAudit.lean#L261) | `theorem canonical_noi_implies_not_exists_asserts : NoI_canonical → ¬ ∃ s : Subje` | {Initiates, Means, State, Subject}  |
| `canonical_noi_implies_not_exists_means` | theorem | [L213](formal/Logos/NegativeRetorsionAudit.lean#L213) | `theorem canonical_noi_implies_not_exists_means : NoI_canonical → ¬ ∃ s : Subject` | {Means, Subject}  |
| `canonical_noi_implies_not_means` | theorem | [L205](formal/Logos/NegativeRetorsionAudit.lean#L205) | `theorem canonical_noi_implies_not_means (s : Subject) : NoI_canonical → ¬ Means ` | {Means, Subject}  |
| `contrapositive_asserts_noi` | theorem | [L767](formal/Logos/NegativeRetorsionAudit.lean#L767) | `theorem contrapositive_asserts_noi (S : NegativeRetorsionSignature) : (∃ s : S.S` | {}  |
| `contrapositive_means_noi` | theorem | [L761](formal/Logos/NegativeRetorsionAudit.lean#L761) | `theorem contrapositive_means_noi (S : NegativeRetorsionSignature) : (∃ s : S.Sub` | {}  |
| `converse_trap_P_does_not_imply_means_noi` | theorem | [L818](formal/Logos/NegativeRetorsionAudit.lean#L818) | `theorem converse_trap_P_does_not_imply_means_noi : ∃ (S : NegativeRetorsionSigna` | {}  |
| `converse_trap_unasserted_does_not_imply_noi` | theorem | [L805](formal/Logos/NegativeRetorsionAudit.lean#L805) | `theorem converse_trap_unasserted_does_not_imply_noi : ∃ (S : NegativeRetorsionSi` | {}  |
| `converse_trap_unmeant_does_not_imply_noi` | theorem | [L776](formal/Logos/NegativeRetorsionAudit.lean#L776) | `theorem converse_trap_unmeant_does_not_imply_noi : ∃ (S : NegativeRetorsionSigna` | {}  |
| `level0_model_M0_empty_subject_satisfies_noi` | theorem | [L136](formal/Logos/NegativeRetorsionAudit.lean#L136) | `theorem level0_model_M0_empty_subject_satisfies_noi : ∃ (S : NegativeRetorsionSi` | {}  |
| `level0_model_M1_inanimate_universe_satisfies_noi` | theorem | [L158](formal/Logos/NegativeRetorsionAudit.lean#L158) | `theorem level0_model_M1_inanimate_universe_satisfies_noi : ∃ (S : NegativeRetors` | {}  |
| `level0_noi_incompatible_with_a17` | theorem | [L179](formal/Logos/NegativeRetorsionAudit.lean#L179) | `theorem level0_noi_incompatible_with_a17 (S : NegativeRetorsionSignature) : S.A1` | {}  |
| `level1_signature_noi_not_meant` | theorem | [L234](formal/Logos/NegativeRetorsionAudit.lean#L234) | `theorem level1_signature_noi_not_meant (S : NegativeRetorsionSignature) (s : S.S` | {}  |
| `level2_signature_asserts_noi_selfRefutes` | theorem | [L287](formal/Logos/NegativeRetorsionAudit.lean#L287) | `theorem level2_signature_asserts_noi_selfRefutes (S : NegativeRetorsionSignature` | {}  |
| `level3_act_noi_consistent_with_false_noi` | theorem | [L360](formal/Logos/NegativeRetorsionAudit.lean#L360) | `theorem level3_act_noi_consistent_with_false_noi : ∃ (S : NegativeRetorsionSigna` | {}  |
| `level4_intentional_understanding_forces_subject` | theorem | [L455](formal/Logos/NegativeRetorsionAudit.lean#L455) | `theorem level4_intentional_understanding_forces_subject (S : NegativeRetorsionSi` | {}  |
| `level4_mechanical_presentation_without_intentionality` | theorem | [L433](formal/Logos/NegativeRetorsionAudit.lean#L433) | `theorem level4_mechanical_presentation_without_intentionality : ∃ (S : NegativeR` | {}  |
| `level4_proof_occurrence_without_subject` | theorem | [L409](formal/Logos/NegativeRetorsionAudit.lean#L409) | `theorem level4_proof_occurrence_without_subject : ∃ (cert : FormalProofCert) (S ` | {}  |
| `level5_domain_item_versus_subject_sort` | theorem | [L492](formal/Logos/NegativeRetorsionAudit.lean#L492) | `theorem level5_domain_item_versus_subject_sort : (∃ (wrap : Prop → DomainItem), ` | {DependsOn, Means, Subject}  |
| `level5_noi_cannot_self_apply` | theorem | [L484](formal/Logos/NegativeRetorsionAudit.lean#L484) | `theorem level5_noi_cannot_self_apply : ∀ s : Subject, IntentionalSubject s → ∃ p` | {Means, Subject}  |
| `level6_diagonal_meant_implies_false` | theorem | [L522](formal/Logos/NegativeRetorsionAudit.lean#L522) | `theorem level6_diagonal_meant_implies_false {Subj : Type} {Means : Subj → Prop →` | {}  |
| `level6_diagonal_true_implies_unmeant` | theorem | [L531](formal/Logos/NegativeRetorsionAudit.lean#L531) | `theorem level6_diagonal_true_implies_unmeant {Subj : Type} {Means : Subj → Prop ` | {}  |
| `level6_model_diagonal_false_consistent` | theorem | [L561](formal/Logos/NegativeRetorsionAudit.lean#L561) | `theorem level6_model_diagonal_false_consistent : ∃ (Subj : Type) (Means : Subj →` | {}  |
| `level6_model_diagonal_true_consistent` | theorem | [L539](formal/Logos/NegativeRetorsionAudit.lean#L539) | `theorem level6_model_diagonal_true_consistent : ∃ (Subj : Type) (Means : Subj → ` | {}  |
| `model_M0_specs` | theorem | [L988](formal/Logos/NegativeRetorsionAudit.lean#L988) | `theorem model_M0_specs : ∃ (S : NegativeRetorsionSignature), S.NoI ∧ (¬ ∃ _s : S` | {}  |
| `model_M1_specs` | theorem | [L1015](formal/Logos/NegativeRetorsionAudit.lean#L1015) | `theorem model_M1_specs : ∃ (S : NegativeRetorsionSignature), (∃ _s : S.Subject, ` | {}  |
| `model_M2_specs` | theorem | [L1041](formal/Logos/NegativeRetorsionAudit.lean#L1041) | `theorem model_M2_specs : ∃ (S : NegativeRetorsionSignature), ¬ S.NoI ∧ (∃ s : S.` | {}  |
| `model_M3_specs` | theorem | [L1075](formal/Logos/NegativeRetorsionAudit.lean#L1075) | `theorem model_M3_specs : ∃ (S : NegativeRetorsionSignature), S.NoI ∧ (∀ s : S.Su` | {}  |
| `model_M4_specs` | theorem | [L1083](formal/Logos/NegativeRetorsionAudit.lean#L1083) | `theorem model_M4_specs : ∃ (S : NegativeRetorsionSignature), ¬ S.NoI ∧ (∃ s : S.` | {}  |
| `model_M6_specs` | theorem | [L1101](formal/Logos/NegativeRetorsionAudit.lean#L1101) | `theorem model_M6_specs : ∃ (cert : FormalProofCert) (S : NegativeRetorsionSignat` | {}  |
| `model_M7_specs` | theorem | [L1134](formal/Logos/NegativeRetorsionAudit.lean#L1134) | `theorem model_M7_specs : ∃ (cert : FormalProofCert) (S : NegativeRetorsionSignat` | {}  |
| `negative_retorsion_master_synthesis` | theorem | [L1177](formal/Logos/NegativeRetorsionAudit.lean#L1177) | `theorem negative_retorsion_master_synthesis : -- 1. Satisfiable in isolation (∃ ` | {}  |
| `noi_canonical_iff_pointwise` | theorem | [L54](formal/Logos/NegativeRetorsionAudit.lean#L54) | `theorem noi_canonical_iff_pointwise : NoI_canonical ↔ NoI_pointwise_canonical` | {Means, Subject}  |
| `performed_denial_gradient` | theorem | [L735](formal/Logos/NegativeRetorsionAudit.lean#L735) | `theorem performed_denial_gradient (S : NegativeRetorsionSignature) (s : S.Subjec` | {}  |
| `regime_M5_is_provably_incoherent` | theorem | [L1093](formal/Logos/NegativeRetorsionAudit.lean#L1093) | `theorem regime_M5_is_provably_incoherent (S : NegativeRetorsionSignature) : S.No` | {}  |
| `unassertability_does_not_imply_falsity` | theorem | [L297](formal/Logos/NegativeRetorsionAudit.lean#L297) | `theorem unassertability_does_not_imply_falsity : ∃ (S : NegativeRetorsionSignatu` | {}  |

### `Logos.NegativeRetorsionAudit.Level10`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `converse_step2_fails` | theorem | [L915](formal/Logos/NegativeRetorsionAudit.lean#L915) | `theorem converse_step2_fails : ∃ (S : NegativeRetorsionSignature), (∀ s : S.Subj` | {}  |
| `converse_step3_fails` | theorem | [L941](formal/Logos/NegativeRetorsionAudit.lean#L941) | `theorem converse_step3_fails : ∃ (S : NegativeRetorsionSignature), (∀ s : S.Subj` | {}  |
| `equiv_act` | theorem | [L880](formal/Logos/NegativeRetorsionAudit.lean#L880) | `theorem equiv_act (S : NegativeRetorsionSignature) : (¬ ∃ s : S.Subject, S.Act s` | {}  |
| `equiv_asserts` | theorem | [L887](formal/Logos/NegativeRetorsionAudit.lean#L887) | `theorem equiv_asserts (S : NegativeRetorsionSignature) : (¬ ∃ s : S.Subject, S.A` | {}  |
| `equiv_intentional` | theorem | [L866](formal/Logos/NegativeRetorsionAudit.lean#L866) | `theorem equiv_intentional (S : NegativeRetorsionSignature) : (¬ ∃ s : S.Subject,` | {}  |
| `equiv_means` | theorem | [L873](formal/Logos/NegativeRetorsionAudit.lean#L873) | `theorem equiv_means (S : NegativeRetorsionSignature) : (¬ ∃ s : S.Subject, S.Mea` | {}  |
| `step1_noi_implies_all_not_means` | theorem | [L894](formal/Logos/NegativeRetorsionAudit.lean#L894) | `theorem step1_noi_implies_all_not_means (S : NegativeRetorsionSignature) : S.NoI` | {}  |
| `step2_not_means_implies_not_act` | theorem | [L900](formal/Logos/NegativeRetorsionAudit.lean#L900) | `theorem step2_not_means_implies_not_act (S : NegativeRetorsionSignature) : (∀ s ` | {}  |
| `step3_not_act_implies_not_asserts` | theorem | [L906](formal/Logos/NegativeRetorsionAudit.lean#L906) | `theorem step3_not_act_implies_not_asserts (S : NegativeRetorsionSignature) : (∀ ` | {}  |

### `Logos.NegativeRetorsionAudit.Level7`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Neg_A17` | def | [L609](formal/Logos/NegativeRetorsionAudit.lean#L609) | `def Neg_A17 (S : NegativeRetorsionSignature) : Prop` | {}  |
| `Neg_NoActEO` | def | [L607](formal/Logos/NegativeRetorsionAudit.lean#L607) | `def Neg_NoActEO (S : NegativeRetorsionSignature) : Prop` | {}  |
| `Neg_NoAssertEO` | def | [L608](formal/Logos/NegativeRetorsionAudit.lean#L608) | `def Neg_NoAssertEO (S : NegativeRetorsionSignature) : Prop` | {}  |
| `Neg_NoDepThinkerEO` | def | [L606](formal/Logos/NegativeRetorsionAudit.lean#L606) | `def Neg_NoDepThinkerEO (S : NegativeRetorsionSignature) : Prop` | {}  |
| `Neg_NoIntentionalSubject` | def | [L604](formal/Logos/NegativeRetorsionAudit.lean#L604) | `def Neg_NoIntentionalSubject (S : NegativeRetorsionSignature) : Prop` | {}  |
| `Neg_NoThinkerEO` | def | [L605](formal/Logos/NegativeRetorsionAudit.lean#L605) | `def Neg_NoThinkerEO (S : NegativeRetorsionSignature) : Prop` | {}  |
| `countermodel_neg_a17_compatible_with_asserting_eo` | theorem | [L697](formal/Logos/NegativeRetorsionAudit.lean#L697) | `theorem countermodel_neg_a17_compatible_with_asserting_eo : ∃ (S : NegativeRetor` | {}  |
| `countermodel_neg_a17_does_not_imply_noi` | theorem | [L649](formal/Logos/NegativeRetorsionAudit.lean#L649) | `theorem countermodel_neg_a17_does_not_imply_noi : ∃ (S : NegativeRetorsionSignat` | {}  |
| `countermodel_neg_no_thinker_eo_does_not_imply_noi` | theorem | [L673](formal/Logos/NegativeRetorsionAudit.lean#L673) | `theorem countermodel_neg_no_thinker_eo_does_not_imply_noi : ∃ (S : NegativeRetor` | {}  |
| `neg_a17_implies_neg_no_dep_thinker_eo` | theorem | [L627](formal/Logos/NegativeRetorsionAudit.lean#L627) | `theorem neg_a17_implies_neg_no_dep_thinker_eo (S : NegativeRetorsionSignature) :` | {}  |
| `neg_no_act_implies_neg_no_assert` | theorem | [L641](formal/Logos/NegativeRetorsionAudit.lean#L641) | `theorem neg_no_act_implies_neg_no_assert (S : NegativeRetorsionSignature) : Neg_` | {}  |
| `neg_no_thinker_implies_neg_no_act` | theorem | [L634](formal/Logos/NegativeRetorsionAudit.lean#L634) | `theorem neg_no_thinker_implies_neg_no_act (S : NegativeRetorsionSignature) : Neg` | {}  |
| `noi_implies_neg_a17` | theorem | [L613](formal/Logos/NegativeRetorsionAudit.lean#L613) | `theorem noi_implies_neg_a17 (S : NegativeRetorsionSignature) : S.NoI → Neg_A17 S` | {}  |
| `noi_implies_neg_no_thinker_eo` | theorem | [L620](formal/Logos/NegativeRetorsionAudit.lean#L620) | `theorem noi_implies_neg_no_thinker_eo (S : NegativeRetorsionSignature) : S.NoI →` | {}  |

### `Logos.NegativeRetorsionAudit.NegativeRetorsionSignature`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `A17` | def | [L109](formal/Logos/NegativeRetorsionAudit.lean#L109) | `def A17 (S : NegativeRetorsionSignature) : Prop` | {}  |
| `Act` | def | [L84](formal/Logos/NegativeRetorsionAudit.lean#L84) | `def Act (S : NegativeRetorsionSignature) (s : S.Subject) (p : Prop) : Prop` | {}  |
| `Asserts` | def | [L88](formal/Logos/NegativeRetorsionAudit.lean#L88) | `def Asserts (S : NegativeRetorsionSignature) (s : S.Subject) (p : Prop) : Prop` | {}  |
| `IntentionalSubject` | def | [L80](formal/Logos/NegativeRetorsionAudit.lean#L80) | `def IntentionalSubject (S : NegativeRetorsionSignature) (s : S.Subject) : Prop` | {}  |
| `NoI` | def | [L100](formal/Logos/NegativeRetorsionAudit.lean#L100) | `def NoI (S : NegativeRetorsionSignature) : Prop` | {}  |
| `NoI_pointwise` | def | [L104](formal/Logos/NegativeRetorsionAudit.lean#L104) | `def NoI_pointwise (S : NegativeRetorsionSignature) : Prop` | {}  |
| `P` | def | [L96](formal/Logos/NegativeRetorsionAudit.lean#L96) | `def P (S : NegativeRetorsionSignature) : Prop` | {}  |
| `asserts` | def | [L92](formal/Logos/NegativeRetorsionAudit.lean#L92) | `def asserts (S : NegativeRetorsionSignature) (s : S.Subject) (p : Prop) : Prop` | {}  |
| `noi_iff_pointwise` | theorem | [L113](formal/Logos/NegativeRetorsionAudit.lean#L113) | `theorem noi_iff_pointwise (S : NegativeRetorsionSignature) : S.NoI ↔ S.NoI_point` | {}  |

### `Logos.NonLibertarianCreation`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `ActionContingency` | def | [L136](formal/Logos/NonLibertarianCreation.lean#L136) | `def ActionContingency (World Subject : Type) (ActAt : World → Subject → Prop → P` | {}  |
| `AdmissibleByReason` | def | [L154](formal/Logos/NonLibertarianCreation.lean#L154) | `def AdmissibleByReason (Reason : Prop) (p q : Prop) : Prop` | {}  |
| `AgentCausalSettlement` | def | [L58](formal/Logos/NonLibertarianCreation.lean#L58) | `def AgentCausalSettlement (World Subject : Type) (SettlesAt : World → Subject → ` | {}  |
| `BruteEvent` | def | [L73](formal/Logos/NonLibertarianCreation.lean#L73) | `def BruteEvent (World : Type) (AntecedentAt : World → Prop) (ReasonAt : World → ` | {}  |
| `ContrastiveExplanation` | def | [L209](formal/Logos/NonLibertarianCreation.lean#L209) | `def ContrastiveExplanation (World : Type) (AntecedentAt : World → Prop) (_EventA` | {}  |
| `DeterminedEvent` | def | [L47](formal/Logos/NonLibertarianCreation.lean#L47) | `def DeterminedEvent (World : Type) (AntecedentAt : World → Prop) (EventAt : Worl` | {}  |
| `ExplainedEvent` | def | [L63](formal/Logos/NonLibertarianCreation.lean#L63) | `def ExplainedEvent (World : Type) (ReasonAt : World → Prop) (EventAt : World → P` | {}  |
| `ExplainsCreationSet` | def | [L157](formal/Logos/NonLibertarianCreation.lean#L157) | `def ExplainsCreationSet (World : Type) (ReasonAt : World → Prop) (CreateAt : Wor` | {}  |
| `GroundedEvent` | def | [L66](formal/Logos/NonLibertarianCreation.lean#L66) | `def GroundedEvent (World Entity : Type) (GroundsAt : World → Entity → Prop → Pro` | {}  |
| `NonDeterminedEvent` | def | [L50](formal/Logos/NonLibertarianCreation.lean#L50) | `def NonDeterminedEvent (World : Type) (AntecedentAt : World → Prop) (EventAt : W` | {}  |
| `NonDeterminingGround` | def | [L190](formal/Logos/NonLibertarianCreation.lean#L190) | `def NonDeterminingGround (World Entity : Type) (frame : KripkeFrame World) (actu` | {}  |
| `PossibilityExplanation` | def | [L206](formal/Logos/NonLibertarianCreation.lean#L206) | `def PossibilityExplanation (Reason : Prop) (Create NoCreate : Prop) : Prop` | {}  |
| `RandomEvent` | def | [L70](formal/Logos/NonLibertarianCreation.lean#L70) | `def RandomEvent (World : Type) (EventAt : World → Prop) (ReasonAt : World → Prop` | {}  |
| `VolitionalContingency` | def | [L140](formal/Logos/NonLibertarianCreation.lean#L140) | `def VolitionalContingency (World Subject : Type) (WillsAt : World → Subject → Pr` | {}  |
| `VolitionallyFree` | def | [L53](formal/Logos/NonLibertarianCreation.lean#L53) | `def VolitionallyFree (World Subject : Type) (ChoosesAt : World → Subject → Prop ` | {}  |
| `WorldContingency` | def | [L132](formal/Logos/NonLibertarianCreation.lean#L132) | `def WorldContingency (World Entity : Type) (CreatesAt : World → Entity → Entity ` | {}  |
| `contrastive_trilemma_theorem` | theorem | [L219](formal/Logos/NonLibertarianCreation.lean#L219) | `theorem contrastive_trilemma_theorem (World Subject : Type) (AntecedentAt : Worl` | {}  |
| `explanation_not_entails_determination` | theorem | [L163](formal/Logos/NonLibertarianCreation.lean#L163) | `theorem explanation_not_entails_determination : ∃ (World : Type) (ReasonAt : Wor` | {}  |
| `model_NC10_consistent` | theorem | [L354](formal/Logos/NonLibertarianCreation.lean#L354) | `theorem model_NC10_consistent : ∃ (World Entity : Type) (frame : KripkeFrame Wor` | {}  |
| `model_NC11_consistent` | theorem | [L367](formal/Logos/NonLibertarianCreation.lean#L367) | `theorem model_NC11_consistent : ∃ (World Entity : Type) (frame : KripkeFrame Wor` | {}  |
| `model_NC12_consistent` | theorem | [L380](formal/Logos/NonLibertarianCreation.lean#L380) | `theorem model_NC12_consistent : ∃ (World Entity Subject : Type) (frame : KripkeF` | {}  |
| `model_NC13_consistent` | theorem | [L397](formal/Logos/NonLibertarianCreation.lean#L397) | `theorem model_NC13_consistent : ∃ (World Entity Subject : Type) (frame : KripkeF` | {}  |
| `model_NC14_consistent` | theorem | [L417](formal/Logos/NonLibertarianCreation.lean#L417) | `theorem model_NC14_consistent : ∃ (World Entity Subject : Type) (frame : KripkeF` | {}  |
| `model_NC15_consistent` | theorem | [L434](formal/Logos/NonLibertarianCreation.lean#L434) | `theorem model_NC15_consistent : ∃ (World Entity Subject : Type) (frame : KripkeF` | {}  |
| `model_NC16_consistent` | theorem | [L452](formal/Logos/NonLibertarianCreation.lean#L452) | `theorem model_NC16_consistent : ∃ (World Entity Subject : Type) (frame : KripkeF` | {}  |
| `model_NC1_consistent` | theorem | [L241](formal/Logos/NonLibertarianCreation.lean#L241) | `theorem model_NC1_consistent : ∃ (World Entity : Type) (frame : KripkeFrame Worl` | {}  |
| `model_NC2_consistent` | theorem | [L251](formal/Logos/NonLibertarianCreation.lean#L251) | `theorem model_NC2_consistent : ∃ (World Entity : Type) (frame : KripkeFrame Worl` | {}  |
| `model_NC3_consistent` | theorem | [L264](formal/Logos/NonLibertarianCreation.lean#L264) | `theorem model_NC3_consistent : ∃ (World Entity : Type) (frame : KripkeFrame Worl` | {}  |
| `model_NC4_consistent` | theorem | [L282](formal/Logos/NonLibertarianCreation.lean#L282) | `theorem model_NC4_consistent : ∃ (World Entity Subject : Type) (frame : KripkeFr` | {}  |
| `model_NC5_consistent` | theorem | [L296](formal/Logos/NonLibertarianCreation.lean#L296) | `theorem model_NC5_consistent : ∃ (World Entity : Type) (frame : KripkeFrame Worl` | {}  |
| `model_NC6_consistent` | theorem | [L309](formal/Logos/NonLibertarianCreation.lean#L309) | `theorem model_NC6_consistent : ∃ (World Entity : Type) (frame : KripkeFrame Worl` | {}  |
| `model_NC7_consistent` | theorem | [L319](formal/Logos/NonLibertarianCreation.lean#L319) | `theorem model_NC7_consistent : ∃ (World Entity : Type) (frame : KripkeFrame Worl` | {}  |
| `model_NC8_consistent` | theorem | [L327](formal/Logos/NonLibertarianCreation.lean#L327) | `theorem model_NC8_consistent : ∃ (World Entity : Type) (frame : KripkeFrame Worl` | {}  |
| `model_NC9_consistent` | theorem | [L340](formal/Logos/NonLibertarianCreation.lean#L340) | `theorem model_NC9_consistent : ∃ (World Entity : Type) (frame : KripkeFrame Worl` | {}  |
| `nondetermined_not_entails_nonfree` | theorem | [L97](formal/Logos/NonLibertarianCreation.lean#L97) | `theorem nondetermined_not_entails_nonfree : ∃ (World Subject : Type) (Antecedent` | {}  |
| `nondetermined_not_entails_random` | theorem | [L83](formal/Logos/NonLibertarianCreation.lean#L83) | `theorem nondetermined_not_entails_random : ∃ (World : Type) (AntecedentAt : Worl` | {}  |
| `nonfree_not_entails_random` | theorem | [L113](formal/Logos/NonLibertarianCreation.lean#L113) | `theorem nonfree_not_entails_random : ∃ (World Subject : Type) (EventAt : World →` | {}  |

### `Logos.NormativeTruth`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `GenuineNormativeDomain` | structure | [L137](formal/Logos/NormativeTruth.lean#L137) | `structure GenuineNormativeDomain (Subject : Type) where` | —  |
| `NoNormativeTruth` | def | [L35](formal/Logos/NormativeTruth.lean#L35) | `def NoNormativeTruth (NormativeTruth : Prop → Prop) : Prop` | {}  |
| `NoNormativeTruthAt` | def | [L82](formal/Logos/NormativeTruth.lean#L82) | `def NoNormativeTruthAt (World : Type) (NormAt : World → Prop → Prop) (w : World)` | {}  |
| `NormativeFreeGroundContext` | structure | [L167](formal/Logos/NormativeTruth.lean#L167) | `structure NormativeFreeGroundContext` | —  |
| `NormativeTruthContext` | structure | [L41](formal/Logos/NormativeTruth.lean#L41) | `structure NormativeTruthContext where` | —  |
| `RightWrongNormativeContext` | structure | [L106](formal/Logos/NormativeTruth.lean#L106) | `structure RightWrongNormativeContext where` | —  |
| `context_normative_truth_exists` | theorem | [L72](formal/Logos/NormativeTruth.lean#L72) | `theorem context_normative_truth_exists (ctx : NormativeTruthContext) : ∃ p : Pro` | {CL}  |
| `established_free_subject_defeats_d3` | theorem | [L211](formal/Logos/NormativeTruth.lean#L211) | `theorem established_free_subject_defeats_d3 {World PriorState FutureState : Type` | {Means, Subject}  |
| `impersonal_model_excludes_genuine_normative_truth` | theorem | [L144](formal/Logos/NormativeTruth.lean#L144) | `theorem impersonal_model_excludes_genuine_normative_truth {Subject : Type} (dom ` | {}  |
| `necessary_normative_truth_exists` | theorem | [L88](formal/Logos/NormativeTruth.lean#L88) | `theorem necessary_normative_truth_exists {World : Type} (NormAt : World → Prop →` | {CL}  |
| `no_normative_truth_is_self_refuting` | theorem | [L51](formal/Logos/NormativeTruth.lean#L51) | `theorem no_normative_truth_is_self_refuting (NormativeTruth : Prop → Prop) (hSel` | {}  |
| `normative_free_subject_grounds_agency` | theorem | [L175](formal/Logos/NormativeTruth.lean#L175) | `theorem normative_free_subject_grounds_agency {World PriorState FutureState : Ty` | {Means, Subject}  |
| `normative_free_subject_implies_indeterminism` | theorem | [L186](formal/Logos/NormativeTruth.lean#L186) | `theorem normative_free_subject_implies_indeterminism {World PriorState FutureSta` | {Means, Subject}  |
| `normative_free_subject_implies_not_d3` | theorem | [L198](formal/Logos/NormativeTruth.lean#L198) | `theorem normative_free_subject_implies_not_d3 {World PriorState FutureState : Ty` | {Means, Subject}  |
| `normative_truth_exists` | theorem | [L62](formal/Logos/NormativeTruth.lean#L62) | `theorem normative_truth_exists (NormativeTruth : Prop → Prop) (hSelf : NoNormati` | {CL}  |
| `right_wrong_content_and_normativity` | theorem | [L118](formal/Logos/NormativeTruth.lean#L118) | `theorem right_wrong_content_and_normativity (ctx : RightWrongNormativeContext) :` | {}  |
| `right_wrong_is_normative_truth` | theorem | [L112](formal/Logos/NormativeTruth.lean#L112) | `theorem right_wrong_is_normative_truth (ctx : RightWrongNormativeContext) : ∃ p ` | {}  |

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
| `CarriesLogicalFeature` | def | [L132](formal/Logos/Person.lean#L132) | `def CarriesLogicalFeature (a : Prop) : Prop` | {}  |
| `CarriesPersonalFeature` | def | [L128](formal/Logos/Person.lean#L128) | `def CarriesPersonalFeature (a : Prop) : Prop` | {Means, Subject}  |
| `HasFeature` | def | [L125](formal/Logos/Person.lean#L125) | `def HasFeature (a f : Prop) : Prop` | {}  |
| `Intentional` | def | [L48](formal/Logos/Person.lean#L48) | `def Intentional (s : Subject) : Prop` | {Means, Subject}  |
| `IntentionalSubject` | def | [L45](formal/Logos/Person.lean#L45) | `def IntentionalSubject (s : Subject) : Prop` | {Means, Subject}  |
| `Person` | def | [L57](formal/Logos/Person.lean#L57) | `def Person (s : Subject) : Prop` | {Means, Subject}  |
| `RationalAct` | def | [L122](formal/Logos/Person.lean#L122) | `def RationalAct (a : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `SubstantivePerson` | opaque | [L52](formal/Logos/Person.lean#L52) | `opaque SubstantivePerson : Subject → Prop` | —  |
| `act_implies_intentional` | theorem | [L72](formal/Logos/Person.lean#L72) | `theorem act_implies_intentional {s : Subject} {p : Prop} (h : Logos.Agency.Act s` | {Initiates, Means, State, Subject}  |
| `act_implies_intentionalSubject` | theorem | [L68](formal/Logos/Person.lean#L68) | `theorem act_implies_intentionalSubject {s : Subject} {p : Prop} (h : Logos.Agenc` | {Initiates, Means, State, Subject}  |
| `inseparability_24b` | theorem | [L138](formal/Logos/Person.lean#L138) | `theorem inseparability_24b : ∀ a : Prop, RationalAct a → (CarriesPersonalFeature` | {Initiates, Means, State, Subject, CL} → C25 |
| `intentionalSubject_exists_of_act` | theorem | [L96](formal/Logos/Person.lean#L96) | `theorem intentionalSubject_exists_of_act (h : ∃ s : Subject, ∃ p : Prop, Logos.A` | {Initiates, Means, State, Subject}  |
| `intentionalSubject_exists_of_assert` | theorem | [L108](formal/Logos/Person.lean#L108) | `theorem intentionalSubject_exists_of_assert {s : Subject} {p : Prop} (h : Logos.` | {Initiates, Means, State, Subject}  |
| `intentional_exists_of_act` | theorem | [L102](formal/Logos/Person.lean#L102) | `theorem intentional_exists_of_act (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.A` | {Initiates, Means, State, Subject}  |
| `intentional_exists_of_assert` | theorem | [L113](formal/Logos/Person.lean#L113) | `theorem intentional_exists_of_assert {s : Subject} {p : Prop} (h : Logos.Agency.` | {Initiates, Means, State, Subject}  |
| `intentional_implies_subjectExists_of_bridge` | theorem | [L88](formal/Logos/Person.lean#L88) | `theorem intentional_implies_subjectExists_of_bridge (hBridge : ∀ (s : Subject) (` | {Initiates, Means, State, Subject}  |
| `person_is_intentional` | theorem | [L61](formal/Logos/Person.lean#L61) | `theorem person_is_intentional (s : Subject) (h : Person s) : IntentionalSubject ` | {Means, Subject}  |
| `subjectExists_implies_intentional` | theorem | [L83](formal/Logos/Person.lean#L83) | `theorem subjectExists_implies_intentional (h : Logos.Agency.SubjectExists s) : I` | {Initiates, Means, State, Subject}  |
| `subjectExists_implies_intentionalSubject` | theorem | [L78](formal/Logos/Person.lean#L78) | `theorem subjectExists_implies_intentionalSubject (h : Logos.Agency.SubjectExists` | {Initiates, Means, State, Subject}  |

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

### `Logos.PostA14Frontier`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `DoxasticCommitmentHorn` | def | [L64](formal/Logos/PostA14Frontier.lean#L64) | `def DoxasticCommitmentHorn {Subj : Type} (CS : FineCognitiveSubject Subj) (s : S` | {}  |
| `ExecutiveInitiationHorn` | def | [L74](formal/Logos/PostA14Frontier.lean#L74) | `def ExecutiveInitiationHorn {Subj : Type} (InitiatesRel : Subj → Unit → Unit → P` | {}  |
| `TeleologicalAimHorn` | def | [L69](formal/Logos/PostA14Frontier.lean#L69) | `def TeleologicalAimHorn {Subj : Type} (CS : FineCognitiveSubject Subj) (s : Subj` | {}  |
| `agency_ladder_frontier_synthesis` | theorem | [L471](formal/Logos/PostA14Frontier.lean#L471) | `theorem agency_ladder_frontier_synthesis {Subj : Type} (CS : FineCognitiveSubjec` | {}  |
| `archetype_deterministic_evaluator` | theorem | [L313](formal/Logos/PostA14Frontier.lean#L313) | `theorem archetype_deterministic_evaluator : ∃ (Subj : Type) (CS : FineCognitiveS` | {}  |
| `archetype_non_reflexive_chooser` | theorem | [L418](formal/Logos/PostA14Frontier.lean#L418) | `theorem archetype_non_reflexive_chooser : ∃ (Subj : Type) (CS : FineCognitiveSub` | {}  |
| `archetype_passive_truth_tracker` | theorem | [L276](formal/Logos/PostA14Frontier.lean#L276) | `theorem archetype_passive_truth_tracker : ∃ (Subj : Type) (CS : FineCognitiveSub` | {}  |
| `archetype_puppet_unauthored_aims` | theorem | [L379](formal/Logos/PostA14Frontier.lean#L379) | `theorem archetype_puppet_unauthored_aims : ∃ (Subj : Type) (CS : FineCognitiveSu` | {}  |
| `archetype_theoretical_deliberator` | theorem | [L348](formal/Logos/PostA14Frontier.lean#L348) | `theorem archetype_theoretical_deliberator : ∃ (Subj : Type) (CS : FineCognitiveS` | {}  |
| `post_a14_derives_old_chooses` | theorem | [L204](formal/Logos/PostA14Frontier.lean#L204) | `theorem post_a14_derives_old_chooses {Subj : Type} (ActRel : Subj → Prop → Prop)` | {}  |
| `post_a14_fails_to_derive_commitment` | theorem | [L213](formal/Logos/PostA14Frontier.lean#L213) | `theorem post_a14_fails_to_derive_commitment : ∃ (Subj : Type) (CS : FineCognitiv` | {}  |
| `post_a14_fails_to_derive_discretionary_choice` | theorem | [L228](formal/Logos/PostA14Frontier.lean#L228) | `theorem post_a14_fails_to_derive_discretionary_choice : ∃ (Subj : Type) (CS : Fi` | {}  |
| `separation_commitment_without_volition` | theorem | [L120](formal/Logos/PostA14Frontier.lean#L120) | `theorem separation_commitment_without_volition : ∃ (Subj : Type) (CS : FineCogni` | {}  |
| `separation_settlement_without_commitment` | theorem | [L81](formal/Logos/PostA14Frontier.lean#L81) | `theorem separation_settlement_without_commitment : ∃ (Subj : Type) (CS : FineCog` | {}  |
| `separation_volition_without_agency` | theorem | [L161](formal/Logos/PostA14Frontier.lean#L161) | `theorem separation_volition_without_agency : ∃ (Subj : Type) (CS : FineCognitive` | {}  |
| `settlement_plus_aim_horn_yields_volition` | theorem | [L151](formal/Logos/PostA14Frontier.lean#L151) | `theorem settlement_plus_aim_horn_yields_volition {Subj : Type} (CS : FineCogniti` | {}  |
| `settlement_plus_horn_yields_commitment` | theorem | [L111](formal/Logos/PostA14Frontier.lean#L111) | `theorem settlement_plus_horn_yields_commitment {Subj : Type} (CS : FineCognitive` | {}  |

### `Logos.ProofSpecificContrast`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `A14_Existential` | def | [L60](formal/Logos/ProofSpecificContrast.lean#L60) | `def A14_Existential (Subject : Type) (ActAt : Subject → Prop → Prop) (FreeWillAt` | {}  |
| `A14_Universal` | def | [L56](formal/Logos/ProofSpecificContrast.lean#L56) | `def A14_Universal (Subject : Type) (ActAt : Subject → Prop → Prop) (ChoosesAt : ` | {}  |
| `CognitiveSubject` | structure | [L89](formal/Logos/ProofSpecificContrast.lean#L89) | `structure CognitiveSubject (Subject : Type) where` | —  |
| `PerformsRefutation` | def | [L144](formal/Logos/ProofSpecificContrast.lean#L144) | `def PerformsRefutation (Subject : Type) (CS : CognitiveSubject Subject) (s : Sub` | {}  |
| `ProofSpecificContrast` | def | [L64](formal/Logos/ProofSpecificContrast.lean#L64) | `def ProofSpecificContrast (Subject : Type) (s : Subject) (p q : Prop) (MeansAt :` | {}  |
| `RefutationalCognitiveUptake` | def | [L280](formal/Logos/ProofSpecificContrast.lean#L280) | `def RefutationalCognitiveUptake (Subject : Type) (CS : CognitiveSubject Subject)` | {}  |
| `RefutationalPerformance` | def | [L105](formal/Logos/ProofSpecificContrast.lean#L105) | `def RefutationalPerformance (Subject : Type) (CS : CognitiveSubject Subject) (s ` | {}  |
| `RefutationalTrace` | abbrev | [L135](formal/Logos/ProofSpecificContrast.lean#L135) | `abbrev RefutationalTrace : Type` | {}  |
| `TraceContainsAssumption` | def | [L137](formal/Logos/ProofSpecificContrast.lean#L137) | `def TraceContainsAssumption (t : RefutationalTrace) (q : Prop) : Prop` | {}  |
| `TraceContainsDischarge` | def | [L140](formal/Logos/ProofSpecificContrast.lean#L140) | `def TraceContainsDischarge (t : RefutationalTrace) (q : Prop) : Prop` | {}  |
| `TraceStep` | inductive | [L129](formal/Logos/ProofSpecificContrast.lean#L129) | `inductive TraceStep where` | —  |
| `a14_proof_performance_is_contrastive` | theorem | [L181](formal/Logos/ProofSpecificContrast.lean#L181) | `theorem a14_proof_performance_is_contrastive (Subject : Type) (CS : CognitiveSub` | {}  |
| `model_M0_trace_without_subject` | theorem | [L207](formal/Logos/ProofSpecificContrast.lean#L207) | `theorem model_M0_trace_without_subject : ∃ (t : RefutationalTrace), TraceContain` | {}  |
| `model_M2_not_implies_M3` | theorem | [L215](formal/Logos/ProofSpecificContrast.lean#L215) | `theorem model_M2_not_implies_M3 : ∃ (Subject : Type) (CS : CognitiveSubject Subj` | {}  |
| `model_M3_not_implies_M4` | theorem | [L229](formal/Logos/ProofSpecificContrast.lean#L229) | `theorem model_M3_not_implies_M4 : ∃ (Subject : Type) (s : Subject) (q : Prop) (C` | {}  |
| `model_M4_not_implies_M5` | theorem | [L239](formal/Logos/ProofSpecificContrast.lean#L239) | `theorem model_M4_not_implies_M5 : ∃ (Subject : Type) (s : Subject) (q : Prop) (C` | {}  |
| `model_M5_not_implies_M6` | theorem | [L252](formal/Logos/ProofSpecificContrast.lean#L252) | `theorem model_M5_not_implies_M6 : ∃ (Subject : Type) (s : Subject) (q : Prop) (M` | {}  |
| `performative_proof_yields_freewill` | theorem | [L286](formal/Logos/ProofSpecificContrast.lean#L286) | `theorem performative_proof_yields_freewill (Subject : Type) (CS : CognitiveSubje` | {}  |
| `proof_specific_contrast_yields_freewill` | theorem | [L69](formal/Logos/ProofSpecificContrast.lean#L69) | `theorem proof_specific_contrast_yields_freewill (Subject : Type) (s : Subject) (` | {}  |
| `reductio_engages_incompatible_contents` | theorem | [L111](formal/Logos/ProofSpecificContrast.lean#L111) | `theorem reductio_engages_incompatible_contents (Subject : Type) (CS : CognitiveS` | {}  |
| `retorsion_proof_derives_F1b` | theorem | [L304](formal/Logos/ProofSpecificContrast.lean#L304) | `theorem retorsion_proof_derives_F1b (Subject : Type) (CS : CognitiveSubject Subj` | {}  |
| `trace_occurrence_not_implies_cognitive_uptake` | theorem | [L152](formal/Logos/ProofSpecificContrast.lean#L152) | `theorem trace_occurrence_not_implies_cognitive_uptake : ∃ (t : RefutationalTrace` | {}  |
| `universal_a14_false_for_arbitrary_acts` | theorem | [L168](formal/Logos/ProofSpecificContrast.lean#L168) | `theorem universal_a14_false_for_arbitrary_acts : ∃ (Subject : Type) (ActAt : Sub` | {}  |

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

### `Logos.StrongActionChoice`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `ActLegacy` | def | [L61](formal/Logos/StrongActionChoice.lean#L61) | `def ActLegacy (s : Subject) (p : Prop) : Prop` | {Initiates, Means, State, Subject}  |
| `AgentCausalDeterministicModel` | structure | [L702](formal/Logos/StrongActionChoice.lean#L702) | `structure AgentCausalDeterministicModel where` | —  |
| `AgentialComponents` | structure | [L174](formal/Logos/StrongActionChoice.lean#L174) | `structure AgentialComponents (Subject : Type) (State : Type) where` | —  |
| `AuthorshipWithoutAlternativeModel` | structure | [L455](formal/Logos/StrongActionChoice.lean#L455) | `structure AuthorshipWithoutAlternativeModel where` | —  |
| `Available` | def | [L848](formal/Logos/StrongActionChoice.lean#L848) | `def Available {World PriorState Subject FutureState : Type} (mctx : Metaphysical` | {}  |
| `CandidateStatus` | inductive | [L223](formal/Logos/StrongActionChoice.lean#L223) | `inductive CandidateStatus` | —  |
| `CategoricalLeewayContext` | structure | [L143](formal/Logos/StrongActionChoice.lean#L143) | `structure CategoricalLeewayContext (Subject : Type) (State : Type) where` | —  |
| `ChoiceTaxonomy` | structure | [L288](formal/Logos/StrongActionChoice.lean#L288) | `structure ChoiceTaxonomy (Subject : Type) where` | —  |
| `ChoiceWithoutAssertionModel` | structure | [L428](formal/Logos/StrongActionChoice.lean#L428) | `structure ChoiceWithoutAssertionModel where` | —  |
| `ChoosesWeak` | def | [L64](formal/Logos/StrongActionChoice.lean#L64) | `def ChoosesWeak (s : Subject) (p q : Prop) : Prop` | {Means, Subject}  |
| `CoRepWithoutChoiceModel` | structure | [L384](formal/Logos/StrongActionChoice.lean#L384) | `structure CoRepWithoutChoiceModel where` | —  |
| `ContrastiveCandidateContext` | structure | [L233](formal/Logos/StrongActionChoice.lean#L233) | `structure ContrastiveCandidateContext (Subject : Type) where` | —  |
| `CounterfactualCompatibilistModel` | structure | [L984](formal/Logos/StrongActionChoice.lean#L984) | `structure CounterfactualCompatibilistModel where` | —  |
| `DeterministicVolitionModel` | structure | [L676](formal/Logos/StrongActionChoice.lean#L676) | `structure DeterministicVolitionModel where` | —  |
| `DiachronicDeliberation` | structure | [L257](formal/Logos/StrongActionChoice.lean#L257) | `structure DiachronicDeliberation (Subject : Type) (State : Type) where` | —  |
| `EpistemicObservation` | structure | [L652](formal/Logos/StrongActionChoice.lean#L652) | `structure EpistemicObservation (World : Type) (ObsState : Type) where` | —  |
| `EpistemicUncertainty` | def | [L656](formal/Logos/StrongActionChoice.lean#L656) | `def EpistemicUncertainty {World ObsState PriorState FutureState : Type} (W : Wor` | {}  |
| `FullDeliberativeProcess` | def | [L264](formal/Logos/StrongActionChoice.lean#L264) | `def FullDeliberativeProcess (Subject : Type) (State : Type) (D : DiachronicDelib` | {}  |
| `FunctionalSelectionModel` | structure | [L407](formal/Logos/StrongActionChoice.lean#L407) | `structure FunctionalSelectionModel where` | —  |
| `GenuineAct` | structure | [L869](formal/Logos/StrongActionChoice.lean#L869) | `structure GenuineAct` | —  |
| `GenuineChooses` | structure | [L855](formal/Logos/StrongActionChoice.lean#L855) | `structure GenuineChooses` | —  |
| `GenuineFreeSubject` | def | [L1493](formal/Logos/StrongActionChoice.lean#L1493) | `def GenuineFreeSubject {Subject World PriorState FutureState : Type} (cctx : Str` | {}  |
| `LibertarianChooses` | structure | [L153](formal/Logos/StrongActionChoice.lean#L153) | `structure LibertarianChooses (Subject : Type) (State : Type)` | —  |
| `MetaphysicalAvailabilityContext` | structure | [L839](formal/Logos/StrongActionChoice.lean#L839) | `structure MetaphysicalAvailabilityContext (World : Type) (PriorState : Type) (Su` | —  |
| `MetaphysicalIndeterminism` | def | [L640](formal/Logos/StrongActionChoice.lean#L640) | `def MetaphysicalIndeterminism {World PriorState FutureState : Type} (W : WorldMo` | {}  |
| `Model_M_SD` | structure | [L345](formal/Logos/StrongActionChoice.lean#L345) | `structure Model_M_SD where` | —  |
| `NecessaryNormativeFreeGroundingPrinciple` | def | [L1535](formal/Logos/StrongActionChoice.lean#L1535) | `def NecessaryNormativeFreeGroundingPrinciple {Subject World PriorState FutureSta` | {}  |
| `NoAlternativeAvailable` | def | [L1277](formal/Logos/StrongActionChoice.lean#L1277) | `def NoAlternativeAvailable {World PriorState Subject FutureState : Type} (mctx :` | {}  |
| `NoGenuineChoice` | def | [L1268](formal/Logos/StrongActionChoice.lean#L1268) | `def NoGenuineChoice {World PriorState Subject FutureState : Type} (cctx : Strong` | {}  |
| `NomologicalDeterminism_D3` | def | [L632](formal/Logos/StrongActionChoice.lean#L632) | `def NomologicalDeterminism_D3 {World PriorState FutureState : Type} (W : WorldMo` | {}  |
| `NormativeFreeGroundingPrinciple` | def | [L1523](formal/Logos/StrongActionChoice.lean#L1523) | `def NormativeFreeGroundingPrinciple {Subject World PriorState FutureState : Type` | {}  |
| `NormativeGroundingContext` | structure | [L1517](formal/Logos/StrongActionChoice.lean#L1517) | `structure NormativeGroundingContext (Subject : Type) (World : Type) where` | —  |
| `PerformedDenial` | structure | [L1285](formal/Logos/StrongActionChoice.lean#L1285) | `structure PerformedDenial` | —  |
| `PhysicalIndetAgentDetWorld` | structure | [L916](formal/Logos/StrongActionChoice.lean#L916) | `structure PhysicalIndetAgentDetWorld where` | —  |
| `RetorsiveAvailability` | def | [L1427](formal/Logos/StrongActionChoice.lean#L1427) | `def RetorsiveAvailability {World PriorState Subject State FutureState : Type} (a` | {}  |
| `SelectsOver` | def | [L238](formal/Logos/StrongActionChoice.lean#L238) | `def SelectsOver (Subject : Type) (ctx : ContrastiveCandidateContext Subject) (st` | {}  |
| `SinglePathModel` | structure | [L315](formal/Logos/StrongActionChoice.lean#L315) | `structure SinglePathModel where` | —  |
| `StatMechWorld` | structure | [L755](formal/Logos/StrongActionChoice.lean#L755) | `structure StatMechWorld where` | —  |
| `StrongAct` | structure | [L93](formal/Logos/StrongActionChoice.lean#L93) | `structure StrongAct (Subject : Type) (State : Type) (ctx : StrongActContext Subj` | —  |
| `StrongActContext` | structure | [L83](formal/Logos/StrongActionChoice.lean#L83) | `structure StrongActContext (Subject : Type) (State : Type) where` | —  |
| `StrongChooses` | structure | [L122](formal/Logos/StrongActionChoice.lean#L122) | `structure StrongChooses (Subject : Type) (ctx : StrongChoosesContext Subject)` | —  |
| `StrongChoosesContext` | structure | [L113](formal/Logos/StrongActionChoice.lean#L113) | `structure StrongChoosesContext (Subject : Type) where` | —  |
| `StrongNormativeFact` | structure | [L1503](formal/Logos/StrongActionChoice.lean#L1503) | `structure StrongNormativeFact where` | —  |
| `StrongNormativeFactAt` | structure | [L1510](formal/Logos/StrongActionChoice.lean#L1510) | `structure StrongNormativeFactAt (World : Type) (_w : World) where` | —  |
| `SuspendedDeliberationModel` | structure | [L471](formal/Logos/StrongActionChoice.lean#L471) | `structure SuspendedDeliberationModel where` | —  |
| `Volition` | def | [L203](formal/Logos/StrongActionChoice.lean#L203) | `def Volition {Subject : Type} (arch : VolitionalArchitecture Subject) (s : Subje` | {}  |
| `VolitionalArchitecture` | structure | [L196](formal/Logos/StrongActionChoice.lean#L196) | `structure VolitionalArchitecture (Subject : Type) where` | —  |
| `WeakActLegacy` | def | [L58](formal/Logos/StrongActionChoice.lean#L58) | `def WeakActLegacy (s : Subject) (p : Prop) : Prop` | {Subject, act}  |
| `WorldModel` | structure | [L623](formal/Logos/StrongActionChoice.lean#L623) | `structure WorldModel (World : Type) (PriorState : Type) (FutureState : Type) whe` | —  |
| `chooses_weak_eq_chooses` | theorem | [L67](formal/Logos/StrongActionChoice.lean#L67) | `theorem chooses_weak_eq_chooses (s : Subject) (p q : Prop) : ChoosesWeak s p q ↔` | {Means, Subject}  |
| `coarse_obs` | def | [L735](formal/Logos/StrongActionChoice.lean#L735) | `def coarse_obs : EpistemicObservation (Nat × Bool) Unit where obs` | {}  |
| `countermodel_10_epistemically_uncertain_but_deterministic_future` | theorem | [L738](formal/Logos/StrongActionChoice.lean#L738) | `theorem countermodel_10_epistemically_uncertain_but_deterministic_future : Nomol` | {}  |
| `countermodel_11_stochastically_described_but_deterministic` | theorem | [L767](formal/Logos/StrongActionChoice.lean#L767) | `theorem countermodel_11_stochastically_described_but_deterministic : Nomological` | {}  |
| `countermodel_12_indeterminism_without_agent` | theorem | [L898](formal/Logos/StrongActionChoice.lean#L898) | `theorem countermodel_12_indeterminism_without_agent : ∃ (W : WorldModel Bool Uni` | {}  |
| `countermodel_13_physical_indet_agent_det` | theorem | [L925](formal/Logos/StrongActionChoice.lean#L925) | `theorem countermodel_13_physical_indet_agent_det : MetaphysicalIndeterminism phy` | {}  |
| `countermodel_14_deterministic_maximal_deliberator` | theorem | [L941](formal/Logos/StrongActionChoice.lean#L941) | `theorem countermodel_14_deterministic_maximal_deliberator : ∃ (Subject : Type) (` | {}  |
| `countermodel_15_deterministic_agent_causal_source` | theorem | [L952](formal/Logos/StrongActionChoice.lean#L952) | `theorem countermodel_15_deterministic_agent_causal_source : ∃ (M : AgentCausalDe` | {CL}  |
| `countermodel_16_different_priors_not_identical_availability` | theorem | [L966](formal/Logos/StrongActionChoice.lean#L966) | `theorem countermodel_16_different_priors_not_identical_availability : ∃ (W : Wor` | {}  |
| `countermodel_17_counterfactual_without_availability` | theorem | [L991](formal/Logos/StrongActionChoice.lean#L991) | `theorem countermodel_17_counterfactual_without_availability : ∃ (M : Counterfact` | {}  |
| `countermodel_18_logical_possibility_without_availability` | theorem | [L1007](formal/Logos/StrongActionChoice.lean#L1007) | `theorem countermodel_18_logical_possibility_without_availability : ∃ (p q : Bool` | {}  |
| `countermodel_19_canonical_genuine_choice` | theorem | [L1046](formal/Logos/StrongActionChoice.lean#L1046) | `theorem countermodel_19_canonical_genuine_choice : ∃ (cctx : StrongChoosesContex` | {CL}  |
| `countermodel_19_witnesses_indeterminism` | theorem | [L1156](formal/Logos/StrongActionChoice.lean#L1156) | `theorem countermodel_19_witnesses_indeterminism : MetaphysicalIndeterminism genu` | {CL}  |
| `countermodel_19_witnesses_neg_d3` | theorem | [L1163](formal/Logos/StrongActionChoice.lean#L1163) | `theorem countermodel_19_witnesses_neg_d3 : ¬ NomologicalDeterminism_D3 genuine_c` | {CL}  |
| `countermodel_1_single_path_intentional_action` | theorem | [L319](formal/Logos/StrongActionChoice.lean#L319) | `theorem countermodel_1_single_path_intentional_action : ∃ (M : SinglePathModel),` | {}  |
| `countermodel_20_d3_excludes_genuine_choice` | theorem | [L1067](formal/Logos/StrongActionChoice.lean#L1067) | `theorem countermodel_20_d3_excludes_genuine_choice {World PriorState Subject Fut` | {}  |
| `countermodel_21_deterministic_performed_denial` | theorem | [L1330](formal/Logos/StrongActionChoice.lean#L1330) | `theorem countermodel_21_deterministic_performed_denial : ∃ (World : Type) (Prior` | {}  |
| `countermodel_22_platonic_normative_realism` | theorem | [L1548](formal/Logos/StrongActionChoice.lean#L1548) | `theorem countermodel_22_platonic_normative_realism : ∃ (Subject : Type) (World :` | {}  |
| `countermodel_23_deterministic_subject_normativism` | theorem | [L1595](formal/Logos/StrongActionChoice.lean#L1595) | `theorem countermodel_23_deterministic_subject_normativism : ∃ (Subject : Type) (` | {}  |
| `countermodel_2_deterministic_pseudo_choice_verified` | theorem | [L375](formal/Logos/StrongActionChoice.lean#L375) | `theorem countermodel_2_deterministic_pseudo_choice_verified : m_sd_instance.hD1 ` | {}  |
| `countermodel_3_deterministic_co_representation` | theorem | [L391](formal/Logos/StrongActionChoice.lean#L391) | `theorem countermodel_3_deterministic_co_representation : ∃ (M : CoRepWithoutChoi` | {}  |
| `countermodel_4_selection_without_choice` | theorem | [L412](formal/Logos/StrongActionChoice.lean#L412) | `theorem countermodel_4_selection_without_choice : ∃ (M : FunctionalSelectionMode` | {}  |
| `countermodel_5_choice_without_assertion` | theorem | [L434](formal/Logos/StrongActionChoice.lean#L434) | `theorem countermodel_5_choice_without_assertion : ∃ (M : ChoiceWithoutAssertionM` | {}  |
| `countermodel_6_authorship_without_alternative` | theorem | [L459](formal/Logos/StrongActionChoice.lean#L459) | `theorem countermodel_6_authorship_without_alternative : ∃ (M : AuthorshipWithout` | {}  |
| `countermodel_7_alternative_representation_without_choice` | theorem | [L478](formal/Logos/StrongActionChoice.lean#L478) | `theorem countermodel_7_alternative_representation_without_choice : ∃ (M : Suspen` | {}  |
| `countermodel_8_deterministic_volition` | theorem | [L681](formal/Logos/StrongActionChoice.lean#L681) | `theorem countermodel_8_deterministic_volition : ∃ (M : DeterministicVolitionMode` | {}  |
| `countermodel_9_agent_causal_but_deterministic_action` | theorem | [L707](formal/Logos/StrongActionChoice.lean#L707) | `theorem countermodel_9_agent_causal_but_deterministic_action : ∃ (M : AgentCausa` | {}  |
| `denial_of_genuine_choice_is_self_refuting` | theorem | [L1457](formal/Logos/StrongActionChoice.lean#L1457) | `theorem denial_of_genuine_choice_is_self_refuting {World PriorState Subject Stat` | {}  |
| `denial_of_no_metaphysical_alternative_is_self_refuting` | theorem | [L1439](formal/Logos/StrongActionChoice.lean#L1439) | `theorem denial_of_no_metaphysical_alternative_is_self_refuting {World PriorState` | {}  |
| `deterministic_seed_world_model` | def | [L730](formal/Logos/StrongActionChoice.lean#L730) | `def deterministic_seed_world_model : WorldModel (Nat × Bool) Nat Bool where prio` | {}  |
| `free_subject_conflicts_with_d3` | theorem | [L1686](formal/Logos/StrongActionChoice.lean#L1686) | `theorem free_subject_conflicts_with_d3 {Subject World PriorState FutureState : T` | {}  |
| `free_subject_implies_metaphysical_indeterminism` | theorem | [L1674](formal/Logos/StrongActionChoice.lean#L1674) | `theorem free_subject_implies_metaphysical_indeterminism {Subject World PriorStat` | {}  |
| `genuine_act_implies_genuine_chooses` | theorem | [L1170](formal/Logos/StrongActionChoice.lean#L1170) | `theorem genuine_act_implies_genuine_chooses {World PriorState Subject State Futu` | {}  |
| `genuine_choice_avail_ctx` | def | [L1032](formal/Logos/StrongActionChoice.lean#L1032) | `def genuine_choice_avail_ctx : MetaphysicalAvailabilityContext Bool Unit Unit Bo` | {}  |
| `genuine_choice_world_model` | def | [L1027](formal/Logos/StrongActionChoice.lean#L1027) | `def genuine_choice_world_model : WorldModel Bool Unit Bool where prior` | {}  |
| `genuine_chooses_conflicts_with_d3` | theorem | [L1125](formal/Logos/StrongActionChoice.lean#L1125) | `theorem genuine_chooses_conflicts_with_d3 {World PriorState Subject FutureState ` | {}  |
| `genuine_chooses_conflicts_with_d5` | theorem | [L1137](formal/Logos/StrongActionChoice.lean#L1137) | `theorem genuine_chooses_conflicts_with_d5 {World PriorState Subject FutureState ` | {}  |
| `genuine_chooses_implies_metaphysical_indeterminism` | theorem | [L1109](formal/Logos/StrongActionChoice.lean#L1109) | `theorem genuine_chooses_implies_metaphysical_indeterminism {World PriorState Sub` | {}  |
| `libertarian_chooses_conflicts_with_d3` | theorem | [L811](formal/Logos/StrongActionChoice.lean#L811) | `theorem libertarian_chooses_conflicts_with_d3 {World PriorState : Type} (W : Wor` | {}  |
| `libertarian_chooses_conflicts_with_d5` | theorem | [L542](formal/Logos/StrongActionChoice.lean#L542) | `theorem libertarian_chooses_conflicts_with_d5 {Subject : Type} {State : Type} {c` | {}  |
| `m_sd_instance` | def | [L354](formal/Logos/StrongActionChoice.lean#L354) | `def m_sd_instance : Model_M_SD where step` | {}  |
| `macro_obs` | def | [L764](formal/Logos/StrongActionChoice.lean#L764) | `def macro_obs : EpistemicObservation StatMechWorld Nat where obs` | {}  |
| `metaphysical_indeterminism_neg_d3` | theorem | [L644](formal/Logos/StrongActionChoice.lean#L644) | `theorem metaphysical_indeterminism_neg_d3 {World PriorState FutureState : Type} ` | {}  |
| `necessary_normative_grounding_derives_necessary_free_subject` | theorem | [L1699](formal/Logos/StrongActionChoice.lean#L1699) | `theorem necessary_normative_grounding_derives_necessary_free_subject {Subject Wo` | {}  |
| `necessary_normative_grounding_implies_not_d3` | theorem | [L1715](formal/Logos/StrongActionChoice.lean#L1715) | `theorem necessary_normative_grounding_implies_not_d3 {Subject World PriorState F` | {}  |
| `normative_fact_not_implies_free_subject` | theorem | [L1646](formal/Logos/StrongActionChoice.lean#L1646) | `theorem normative_fact_not_implies_free_subject : ∃ (Subject : Type) (World : Ty` | {}  |
| `normative_grounding_derives_free_subject` | theorem | [L1660](formal/Logos/StrongActionChoice.lean#L1660) | `theorem normative_grounding_derives_free_subject {Subject World PriorState Futur` | {}  |
| `performed_denial_consistent_with_d3` | theorem | [L1411](formal/Logos/StrongActionChoice.lean#L1411) | `theorem performed_denial_consistent_with_d3 : ∃ (World : Type) (PriorState : Typ` | {}  |
| `performed_denial_implies_act` | theorem | [L1293](formal/Logos/StrongActionChoice.lean#L1293) | `theorem performed_denial_implies_act {Subject State : Type} {actCtx : StrongActC` | {}  |
| `performed_denial_implies_chooses` | theorem | [L1303](formal/Logos/StrongActionChoice.lean#L1303) | `theorem performed_denial_implies_chooses {Subject State : Type} {actCtx : Strong` | {}  |
| `performed_denial_implies_cognitive_contrast` | theorem | [L1316](formal/Logos/StrongActionChoice.lean#L1316) | `theorem performed_denial_implies_cognitive_contrast {Subject State : Type} {actC` | {}  |
| `performed_denial_not_implies_genuine_chooses` | theorem | [L1387](formal/Logos/StrongActionChoice.lean#L1387) | `theorem performed_denial_not_implies_genuine_chooses : ∃ (World : Type) (PriorSt` | {}  |
| `performed_denial_not_implies_metaphysical_availability` | theorem | [L1374](formal/Logos/StrongActionChoice.lean#L1374) | `theorem performed_denial_not_implies_metaphysical_availability : ∃ (World : Type` | {}  |
| `phys_indet_agent_det_model` | def | [L920](formal/Logos/StrongActionChoice.lean#L920) | `def phys_indet_agent_det_model : WorldModel PhysicalIndetAgentDetWorld Unit (Boo` | {}  |
| `stat_mech_model` | def | [L759](formal/Logos/StrongActionChoice.lean#L759) | `def stat_mech_model : WorldModel StatMechWorld (Nat × Nat) (Nat × Nat) where pri` | {}  |
| `strong_act_not_implies_genuine_chooses` | theorem | [L1183](formal/Logos/StrongActionChoice.lean#L1183) | `theorem strong_act_not_implies_genuine_chooses : ∃ (Subject : Type) (State : Typ` | {}  |
| `strong_act_not_implies_strong_chooses` | theorem | [L510](formal/Logos/StrongActionChoice.lean#L510) | `theorem strong_act_not_implies_strong_chooses : ∃ (Subject : Type) (State : Type` | {}  |
| `strong_chooses_compatible_with_d3` | theorem | [L798](formal/Logos/StrongActionChoice.lean#L798) | `theorem strong_chooses_compatible_with_d3 : ∃ (World PriorState FutureState : Ty` | {}  |
| `strong_chooses_compatible_with_d5` | theorem | [L532](formal/Logos/StrongActionChoice.lean#L532) | `theorem strong_chooses_compatible_with_d5 : ∃ (Subject : Type) (cctx : StrongCho` | {}  |
| `strong_chooses_not_implies_genuine_chooses` | theorem | [L1212](formal/Logos/StrongActionChoice.lean#L1212) | `theorem strong_chooses_not_implies_genuine_chooses : ∃ (Subject : Type) (cctx : ` | {CL}  |
| `strong_chooses_without_immediate_volition` | theorem | [L589](formal/Logos/StrongActionChoice.lean#L589) | `theorem strong_chooses_without_immediate_volition : ∃ (cctx : StrongChoosesConte` | {}  |
| `volition_without_action` | theorem | [L565](formal/Logos/StrongActionChoice.lean#L565) | `theorem volition_without_action : ∃ (vArch : VolitionalArchitecture Unit) (actCt` | {}  |

### `Logos.SubContrastFoundations`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `AxCognitiveContrast` | def | [L466](formal/Logos/SubContrastFoundations.lean#L466) | `def AxCognitiveContrast (Subject : Type) (ActAt : Subject → Prop → Prop) (Discri` | {}  |
| `AxCognitiveUptake` | def | [L470](formal/Logos/SubContrastFoundations.lean#L470) | `def AxCognitiveUptake (Subject : Type) (MeansAt : Subject → Prop → Prop) (Discri` | {}  |
| `CognitiveExclusion` | def | [L250](formal/Logos/SubContrastFoundations.lean#L250) | `def CognitiveExclusion (Subject : Type) (Excludes : Subject → Prop → Prop → Prop` | {}  |
| `CompatibleIntensional` | def | [L219](formal/Logos/SubContrastFoundations.lean#L219) | `def CompatibleIntensional (p q : WorldProp) : Prop` | {}  |
| `IncompatibleIntensional` | def | [L222](formal/Logos/SubContrastFoundations.lean#L222) | `def IncompatibleIntensional (p q : WorldProp) : Prop` | {}  |
| `L10_Choice` | def | [L336](formal/Logos/SubContrastFoundations.lean#L336) | `def L10_Choice (Subject : Type) (ChoosesAt : Subject → Prop → Prop → Prop) (s : ` | {}  |
| `L11_FreeWill` | def | [L340](formal/Logos/SubContrastFoundations.lean#L340) | `def L11_FreeWill (Subject : Type) (ChoosesAt : Subject → Prop → Prop → Prop) (s ` | {}  |
| `L12_LibertarianFreedom` | def | [L344](formal/Logos/SubContrastFoundations.lean#L344) | `def L12_LibertarianFreedom (Subject : Type) (CausesAt : Subject → Prop → Prop) (` | {}  |
| `L1_IntentionalDirectedness` | def | [L301](formal/Logos/SubContrastFoundations.lean#L301) | `def L1_IntentionalDirectedness (Subject : Type) (MeansAt : Subject → Prop → Prop` | {}  |
| `L2_ObjectIndividuation` | def | [L305](formal/Logos/SubContrastFoundations.lean#L305) | `def L2_ObjectIndividuation (p : Prop) : Prop` | {}  |
| `L3_ObjectDifferentiation` | def | [L308](formal/Logos/SubContrastFoundations.lean#L308) | `def L3_ObjectDifferentiation (Subject : Type) (Distinguishes : Subject → Prop → ` | {}  |
| `L4_CognitiveExclusion` | def | [L312](formal/Logos/SubContrastFoundations.lean#L312) | `def L4_CognitiveExclusion (Subject : Type) (Excludes : Subject → Prop → Prop → P` | {}  |
| `L5_AlternativeDifferentiation` | def | [L316](formal/Logos/SubContrastFoundations.lean#L316) | `def L5_AlternativeDifferentiation (Subject : Type) (Discriminates : Subject → Pr` | {}  |
| `L6_AlternativeAvailability` | def | [L320](formal/Logos/SubContrastFoundations.lean#L320) | `def L6_AlternativeAvailability (Subject : Type) (Available : Subject → Prop → Pr` | {}  |
| `L7_AlternativeRepresentation` | def | [L324](formal/Logos/SubContrastFoundations.lean#L324) | `def L7_AlternativeRepresentation (Subject : Type) (Represents : Subject → Prop →` | {}  |
| `L8_CoMeaning` | def | [L328](formal/Logos/SubContrastFoundations.lean#L328) | `def L8_CoMeaning (Subject : Type) (MeansAt : Subject → Prop → Prop) (s : Subject` | {}  |
| `L9_Deliberation` | def | [L332](formal/Logos/SubContrastFoundations.lean#L332) | `def L9_Deliberation (Subject : Type) (Weighs : Subject → Prop → Prop → Prop) (s ` | {}  |
| `MonadicSimulationFrame` | structure | [L424](formal/Logos/SubContrastFoundations.lean#L424) | `structure MonadicSimulationFrame where` | —  |
| `ReasoningRelation` | def | [L73](formal/Logos/SubContrastFoundations.lean#L73) | `def ReasoningRelation (Subject : Type) (Infers : Subject → Prop → Prop → Prop) (` | {}  |
| `WorldProp` | def | [L217](formal/Logos/SubContrastFoundations.lean#L217) | `def WorldProp` | {}  |
| `act_not_implies_reasoning` | theorem | [L117](formal/Logos/SubContrastFoundations.lean#L117) | `theorem act_not_implies_reasoning : ∃ (Subject : Type) (s : Subject) (p : Prop) ` | {}  |
| `consequence_cannot_be_incompatible` | theorem | [L167](formal/Logos/SubContrastFoundations.lean#L167) | `theorem consequence_cannot_be_incompatible (p q : Prop) (hConsist : p) (hEntails` | {}  |
| `distinct_props_are_incompatible` | theorem | [L207](formal/Logos/SubContrastFoundations.lean#L207) | `theorem distinct_props_are_incompatible (p q : Prop) (h : p ≠ q) : Incompatible ` | {CL}  |
| `first_unavoidable_cognitive_layer` | theorem | [L415](formal/Logos/SubContrastFoundations.lean#L415) | `theorem first_unavoidable_cognitive_layer (s : Logos.Agency.Subject) (p : Prop) ` | {Initiates, Means, State, Subject}  |
| `generalized_expressivity_collapse` | theorem | [L438](formal/Logos/SubContrastFoundations.lean#L438) | `theorem generalized_expressivity_collapse (F : MonadicSimulationFrame) (p : Prop` | {}  |
| `hierarchy_L1_not_implies_L3` | theorem | [L349](formal/Logos/SubContrastFoundations.lean#L349) | `theorem hierarchy_L1_not_implies_L3 : ∃ (Subject : Type) (s : Subject) (p : Prop` | {}  |
| `hierarchy_L3_not_implies_L4` | theorem | [L360](formal/Logos/SubContrastFoundations.lean#L360) | `theorem hierarchy_L3_not_implies_L4 : ∃ (Subject : Type) (s : Subject) (p q : Pr` | {}  |
| `hierarchy_L4_not_implies_L7` | theorem | [L373](formal/Logos/SubContrastFoundations.lean#L373) | `theorem hierarchy_L4_not_implies_L7 : ∃ (Subject : Type) (s : Subject) (p q : Pr` | {}  |
| `hierarchy_L7_not_implies_L8` | theorem | [L385](formal/Logos/SubContrastFoundations.lean#L385) | `theorem hierarchy_L7_not_implies_L8 : ∃ (Subject : Type) (s : Subject) (p q : Pr` | {}  |
| `hierarchy_L8_not_implies_L10` | theorem | [L396](formal/Logos/SubContrastFoundations.lean#L396) | `theorem hierarchy_L8_not_implies_L10 : ∃ (Subject : Type) (s : Subject) (p q : P` | {}  |
| `intensional_object_diff_not_implies_alternative_diff` | theorem | [L227](formal/Logos/SubContrastFoundations.lean#L227) | `theorem intensional_object_diff_not_implies_alternative_diff : ∃ (p q : WorldPro` | {}  |
| `intentionality_not_intrinsically_contrastive` | theorem | [L268](formal/Logos/SubContrastFoundations.lean#L268) | `theorem intentionality_not_intrinsically_contrastive : ∃ (Subject : Type) (s : S` | {}  |
| `means_not_implies_cognitive_exclusion` | theorem | [L256](formal/Logos/SubContrastFoundations.lean#L256) | `theorem means_not_implies_cognitive_exclusion : ∃ (Subject : Type) (s : Subject)` | {}  |
| `negation_not_inferrable_from_truth` | theorem | [L184](formal/Logos/SubContrastFoundations.lean#L184) | `theorem negation_not_inferrable_from_truth (p : Prop) (hp : p) : ¬ (p → ¬ p)` | {}  |
| `propositional_closure_cannot_generate_incompatible_horn` | theorem | [L175](formal/Logos/SubContrastFoundations.lean#L175) | `theorem propositional_closure_cannot_generate_incompatible_horn : ∀ (p : Prop), ` | {}  |
| `reasoning_not_implies_discrimination` | theorem | [L80](formal/Logos/SubContrastFoundations.lean#L80) | `theorem reasoning_not_implies_discrimination : ∃ (Subject : Type) (s : Subject) ` | {}  |
| `reasoning_not_implies_distinct_contents` | theorem | [L89](formal/Logos/SubContrastFoundations.lean#L89) | `theorem reasoning_not_implies_distinct_contents : ∃ (Subject : Type) (s : Subjec` | {}  |
| `reasoning_not_implies_means_conclusion` | theorem | [L108](formal/Logos/SubContrastFoundations.lean#L108) | `theorem reasoning_not_implies_means_conclusion : ∃ (Subject : Type) (s : Subject` | {}  |
| `reasoning_not_implies_means_premise` | theorem | [L99](formal/Logos/SubContrastFoundations.lean#L99) | `theorem reasoning_not_implies_means_premise : ∃ (Subject : Type) (s : Subject) (` | {}  |
| `subprinciples_jointly_sufficient_for_choice` | theorem | [L474](formal/Logos/SubContrastFoundations.lean#L474) | `theorem subprinciples_jointly_sufficient_for_choice (Subject : Type) (ActAt : Su` | {}  |
| `vertical_asymmetry_blind_to_horizontal_distinction` | theorem | [L144](formal/Logos/SubContrastFoundations.lean#L144) | `theorem vertical_asymmetry_blind_to_horizontal_distinction : ∃ (Subject : Type) ` | {}  |
| `vertical_sort_separation` | theorem | [L138](formal/Logos/SubContrastFoundations.lean#L138) | `theorem vertical_sort_separation (_s : Subject) (_p : Prop) : True` | {Subject}  |

### `Logos.TheologicalModalHardening`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `ActualEntity` | def | [L54](formal/Logos/TheologicalModalHardening.lean#L54) | `def ActualEntity (e : Entity) : Prop` | {Subject}  |
| `BoxR` | def | [L177](formal/Logos/TheologicalModalHardening.lean#L177) | `def BoxR {W : Type} (frame : KripkeFrame W) (P : W → Prop) (w : W) : Prop` | {}  |
| `CoexistenceWithoutCreationModel` | def | [L471](formal/Logos/TheologicalModalHardening.lean#L471) | `def CoexistenceWithoutCreationModel : CreationSignature where Entity` | {}  |
| `ConcreteInfiniteNecessaryChain` | def | [L264](formal/Logos/TheologicalModalHardening.lean#L264) | `def ConcreteInfiniteNecessaryChain : InfiniteNecessaryChainSignature where Entit` | {CL}  |
| `ConcreteModelG` | def | [L144](formal/Logos/TheologicalModalHardening.lean#L144) | `def ConcreteModelG : ModelG_Signature where Entity` | {}  |
| `ConstantDomainPrinciple` | def | [L629](formal/Logos/TheologicalModalHardening.lean#L629) | `def ConstantDomainPrinciple (S : RegimeG_Signature) : Prop` | {}  |
| `ContingentEntity` | def | [L65](formal/Logos/TheologicalModalHardening.lean#L65) | `def ContingentEntity (e : Entity) : Prop` | {Subject}  |
| `ContingentSubjectRetorsionModel` | structure | [L684](formal/Logos/TheologicalModalHardening.lean#L684) | `structure ContingentSubjectRetorsionModel where` | —  |
| `CreationSignature` | structure | [L442](formal/Logos/TheologicalModalHardening.lean#L442) | `structure CreationSignature where` | —  |
| `DeepCreationSignature` | structure | [L775](formal/Logos/TheologicalModalHardening.lean#L775) | `structure DeepCreationSignature where` | —  |
| `DivineSpecification` | structure | [L731](formal/Logos/TheologicalModalHardening.lean#L731) | `structure DivineSpecification (Entity : Type) where` | —  |
| `DivineSpecification.Divine` | def | [L738](formal/Logos/TheologicalModalHardening.lean#L738) | `def DivineSpecification.Divine {Entity : Type} (spec : DivineSpecification Entit` | {}  |
| `FrameE1` | def | [L647](formal/Logos/TheologicalModalHardening.lean#L647) | `def FrameE1 (W : Type) : KripkeFrame W where R` | {}  |
| `FrameE2` | def | [L653](formal/Logos/TheologicalModalHardening.lean#L653) | `def FrameE2 : KripkeFrame Bool where R` | {}  |
| `FrameE3_Signature` | structure | [L667](formal/Logos/TheologicalModalHardening.lean#L667) | `structure FrameE3_Signature where` | —  |
| `GodAloneModel` | def | [L455](formal/Logos/TheologicalModalHardening.lean#L455) | `def GodAloneModel : CreationSignature where Entity` | {}  |
| `InfiniteNecessaryChainSignature` | structure | [L246](formal/Logos/TheologicalModalHardening.lean#L246) | `structure InfiniteNecessaryChainSignature where` | —  |
| `KripkeFrame` | structure | [L172](formal/Logos/TheologicalModalHardening.lean#L172) | `structure KripkeFrame (W : Type) where` | —  |
| `ModalOntologySignature` | structure | [L75](formal/Logos/TheologicalModalHardening.lean#L75) | `structure ModalOntologySignature where` | —  |
| `ModalWorldModel` | structure | [L887](formal/Logos/TheologicalModalHardening.lean#L887) | `structure ModalWorldModel (World : Type) where` | —  |
| `ModalWorldModel.PossibleWorld` | def | [L891](formal/Logos/TheologicalModalHardening.lean#L891) | `def ModalWorldModel.PossibleWorld {World : Type} (M : ModalWorldModel World) (w ` | {}  |
| `ModelG_Signature` | structure | [L128](formal/Logos/TheologicalModalHardening.lean#L128) | `structure ModelG_Signature where` | —  |
| `ModelNA_Signature` | structure | [L379](formal/Logos/TheologicalModalHardening.lean#L379) | `structure ModelNA_Signature where` | —  |
| `ModelND_Signature` | structure | [L400](formal/Logos/TheologicalModalHardening.lean#L400) | `structure ModelND_Signature where` | —  |
| `ModelNP_Signature` | structure | [L345](formal/Logos/TheologicalModalHardening.lean#L345) | `structure ModelNP_Signature where` | —  |
| `NecessaryEntity` | def | [L57](formal/Logos/TheologicalModalHardening.lean#L57) | `def NecessaryEntity (e : Entity) : Prop` | {Subject}  |
| `Neg_NecessaryEntityExists` | def | [L214](formal/Logos/TheologicalModalHardening.lean#L214) | `def Neg_NecessaryEntityExists : Prop` | {Subject}  |
| `PluralNecessaryEntitiesSignature` | structure | [L502](formal/Logos/TheologicalModalHardening.lean#L502) | `structure PluralNecessaryEntitiesSignature where` | —  |
| `RegimeE_Signature` | structure | [L569](formal/Logos/TheologicalModalHardening.lean#L569) | `structure RegimeE_Signature where` | —  |
| `RegimeG1_GodAlone` | def | [L787](formal/Logos/TheologicalModalHardening.lean#L787) | `def RegimeG1_GodAlone : DeepCreationSignature where Entity` | {}  |
| `RegimeG2_Creation` | def | [L805](formal/Logos/TheologicalModalHardening.lean#L805) | `def RegimeG2_Creation : DeepCreationSignature where Entity` | {}  |
| `RegimeG3_CoexistenceNoCreation` | def | [L825](formal/Logos/TheologicalModalHardening.lean#L825) | `def RegimeG3_CoexistenceNoCreation : DeepCreationSignature where Entity` | {}  |
| `RegimeG_Signature` | structure | [L577](formal/Logos/TheologicalModalHardening.lean#L577) | `structure RegimeG_Signature where` | —  |
| `RegimeG_Signature.NecessaryEntity` | def | [L583](formal/Logos/TheologicalModalHardening.lean#L583) | `def RegimeG_Signature.NecessaryEntity (S : RegimeG_Signature) (e : S.Entity) : P` | {}  |
| `ShiftingEntityModel` | def | [L594](formal/Logos/TheologicalModalHardening.lean#L594) | `def ShiftingEntityModel : RegimeG_Signature where World` | {}  |
| `UniformWitnessPrinciple` | def | [L618](formal/Logos/TheologicalModalHardening.lean#L618) | `def UniformWitnessPrinciple (S : RegimeG_Signature) : Prop` | {}  |
| `UniqueExists` | def | [L497](formal/Logos/TheologicalModalHardening.lean#L497) | `def UniqueExists {α : Type} (P : α → Prop) : Prop` | {}  |
| `UniversalFrame` | def | [L182](formal/Logos/TheologicalModalHardening.lean#L182) | `def UniversalFrame (W : Type) : KripkeFrame W where R` | {}  |
| `accessible_worldwise_truthmaking_consistent` | theorem | [L197](formal/Logos/TheologicalModalHardening.lean#L197) | `theorem accessible_worldwise_truthmaking_consistent : let W` | {}  |
| `axGlobalGround_refutes_empty_world` | theorem | [L551](formal/Logos/TheologicalModalHardening.lean#L551) | `theorem axGlobalGround_refutes_empty_world (hGlobal : ∀ (φ : Form), Logos.Truthm` | {Ground, Subject, CL}  |
| `boxR_universal_iff` | theorem | [L185](formal/Logos/TheologicalModalHardening.lean#L185) | `theorem boxR_universal_iff {W : Type} (P : W → Prop) (w : W) : BoxR (UniversalFr` | {}  |
| `coexistence_without_creation_relation` | theorem | [L480](formal/Logos/TheologicalModalHardening.lean#L480) | `theorem coexistence_without_creation_relation : (∃ x : CoexistenceWithoutCreatio` | {}  |
| `constant_domain_yields_necessary_entity` | theorem | [L632](formal/Logos/TheologicalModalHardening.lean#L632) | `theorem constant_domain_yields_necessary_entity (S : RegimeG_Signature) [Inhabit` | {}  |
| `divine_identification_theorem` | theorem | [L760](formal/Logos/TheologicalModalHardening.lean#L760) | `theorem divine_identification_theorem (Entity : Type) (spec : DivineSpecificatio` | {}  |
| `empty_world_excluded_by_non_emptiness_constraint` | theorem | [L897](formal/Logos/TheologicalModalHardening.lean#L897) | `theorem empty_world_excluded_by_non_emptiness_constraint (World : Type) (M : Mod` | {}  |
| `frameE2_truthmaking_holds_at_actual` | theorem | [L656](formal/Logos/TheologicalModalHardening.lean#L656) | `theorem frameE2_truthmaking_holds_at_actual : let ExistsAt` | {}  |
| `g1_god_alone_properties` | theorem | [L796](formal/Logos/TheologicalModalHardening.lean#L796) | `theorem g1_god_alone_properties : (¬ ∃ x : RegimeG1_GodAlone.Entity, RegimeG1_Go` | {}  |
| `g2_creation_properties` | theorem | [L814](formal/Logos/TheologicalModalHardening.lean#L814) | `theorem g2_creation_properties : (∃ x : RegimeG2_Creation.Entity, RegimeG2_Creat` | {}  |
| `g3_coexistence_no_creation_properties` | theorem | [L834](formal/Logos/TheologicalModalHardening.lean#L834) | `theorem g3_coexistence_no_creation_properties : (∃ x : RegimeG3_CoexistenceNoCre` | {}  |
| `g4_creation_is_contingent` | theorem | [L845](formal/Logos/TheologicalModalHardening.lean#L845) | `theorem g4_creation_is_contingent : ∃ w : RegimeG2_Creation.World, ¬ RegimeG2_Cr` | {}  |
| `god_alone_has_no_creation` | theorem | [L464](formal/Logos/TheologicalModalHardening.lean#L464) | `theorem god_alone_has_no_creation : ¬ ∃ x : GodAloneModel.Entity, GodAloneModel.` | {}  |
| `intentional_subject_not_entails_freewill` | theorem | [L430](formal/Logos/TheologicalModalHardening.lean#L430) | `theorem intentional_subject_not_entails_freewill : ¬ (∀ S : ModelND_Signature, S` | {}  |
| `logical_truth_in_empty_world` | theorem | [L118](formal/Logos/TheologicalModalHardening.lean#L118) | `theorem logical_truth_in_empty_world (φ : Form) : otherWorld ⊨ (φ ∨ ¬φ) ∧ (∀ e :` | {Subject, CL}  |
| `model_E_absolute_empty_world` | theorem | [L111](formal/Logos/TheologicalModalHardening.lean#L111) | `theorem model_E_absolute_empty_world : ∃ w : World, ∀ e : Entity, ¬ ExistsAt w e` | {Subject}  |
| `model_G_consistent` | theorem | [L164](formal/Logos/TheologicalModalHardening.lean#L164) | `theorem model_G_consistent : ∃ _M : ModelG_Signature, True` | {}  |
| `model_NA_consistent` | theorem | [L386](formal/Logos/TheologicalModalHardening.lean#L386) | `theorem model_NA_consistent : ∃ _M : ModelNA_Signature, True` | {}  |
| `model_ND_consistent` | theorem | [L413](formal/Logos/TheologicalModalHardening.lean#L413) | `theorem model_ND_consistent : ∃ _M : ModelND_Signature, True` | {}  |
| `model_NP_consistent` | theorem | [L356](formal/Logos/TheologicalModalHardening.lean#L356) | `theorem model_NP_consistent : ∃ _M : ModelNP_Signature, True` | {}  |
| `necessary_being_not_entails_divine` | theorem | [L743](formal/Logos/TheologicalModalHardening.lean#L743) | `theorem necessary_being_not_entails_divine : ¬ (∀ (Entity : Type) (spec : Divine` | {}  |
| `necessary_entity_not_entails_subject` | theorem | [L370](formal/Logos/TheologicalModalHardening.lean#L370) | `theorem necessary_entity_not_entails_subject : ¬ (∀ S : ModelNP_Signature, ∃ s :` | {}  |
| `necessary_entity_not_entails_ultimate_ground` | theorem | [L278](formal/Logos/TheologicalModalHardening.lean#L278) | `theorem necessary_entity_not_entails_ultimate_ground : ¬ (∀ S : InfiniteNecessar` | {CL}  |
| `necessary_entity_not_forces_contingent_creation` | theorem | [L330](formal/Logos/TheologicalModalHardening.lean#L330) | `theorem necessary_entity_not_forces_contingent_creation : ∃ S : ModelG_Signature` | {}  |
| `necessary_entity_rules_out_empty_world` | theorem | [L319](formal/Logos/TheologicalModalHardening.lean#L319) | `theorem necessary_entity_rules_out_empty_world (Entity World : Type) (ExistsAt :` | {}  |
| `necessary_existence_not_entails_uniqueness` | theorem | [L528](formal/Logos/TheologicalModalHardening.lean#L528) | `theorem necessary_existence_not_entails_uniqueness : ¬ (∀ S : PluralNecessaryEnt` | {}  |
| `necessary_ground_can_be_non_ultimate` | theorem | [L872](formal/Logos/TheologicalModalHardening.lean#L872) | `theorem necessary_ground_can_be_non_ultimate : let GroundEntity` | {}  |
| `necessary_non_emptiness_not_entails_necessary_entity` | theorem | [L600](formal/Logos/TheologicalModalHardening.lean#L600) | `theorem necessary_non_emptiness_not_entails_necessary_entity : ¬ (∀ S : RegimeG_` | {}  |
| `necessary_not_contingent` | theorem | [L69](formal/Logos/TheologicalModalHardening.lean#L69) | `theorem necessary_not_contingent (e : Entity) : NecessaryEntity e → ¬ Contingent` | {Subject}  |
| `neg_necessary_entity_holds_in_concrete_ontology` | theorem | [L219](formal/Logos/TheologicalModalHardening.lean#L219) | `theorem neg_necessary_entity_holds_in_concrete_ontology : Neg_NecessaryEntityExi` | {Subject}  |
| `non_contingent_not_entails_necessary` | theorem | [L87](formal/Logos/TheologicalModalHardening.lean#L87) | `theorem non_contingent_not_entails_necessary : ¬ (∀ S : ModalOntologySignature, ` | {}  |
| `plural_necessary_entities_consistent` | theorem | [L513](formal/Logos/TheologicalModalHardening.lean#L513) | `theorem plural_necessary_entities_consistent : ∃ _M : PluralNecessaryEntitiesSig` | {}  |
| `retorsion_fails_against_no_necessary_entity` | theorem | [L228](formal/Logos/TheologicalModalHardening.lean#L228) | `theorem retorsion_fails_against_no_necessary_entity : (∃ w : World, ∀ e : Entity` | {Subject}  |
| `retorsion_not_forces_necessary_subject` | theorem | [L699](formal/Logos/TheologicalModalHardening.lean#L699) | `theorem retorsion_not_forces_necessary_subject : ∃ _M : ContingentSubjectRetorsi` | {}  |
| `self_grounding_violates_irreflexivity` | theorem | [L301](formal/Logos/TheologicalModalHardening.lean#L301) | `theorem self_grounding_violates_irreflexivity (Entity : Type) (GroundEntity : En` | {}  |
| `subject_not_entails_agency` | theorem | [L390](formal/Logos/TheologicalModalHardening.lean#L390) | `theorem subject_not_entails_agency : ¬ (∀ S : ModelNA_Signature, ∃ p : S.PropTyp` | {}  |
| `u1_independence_exclusion_forces_uniqueness` | theorem | [L859](formal/Logos/TheologicalModalHardening.lean#L859) | `theorem u1_independence_exclusion_forces_uniqueness (_Entity : Type) (Nec : _Ent` | {}  |
| `uniform_witness_yields_necessary_entity` | theorem | [L621](formal/Logos/TheologicalModalHardening.lean#L621) | `theorem uniform_witness_yields_necessary_entity (S : RegimeG_Signature) (hWit : ` | {}  |
| `well_foundedness_forces_ultimate_ground` | theorem | [L290](formal/Logos/TheologicalModalHardening.lean#L290) | `theorem well_foundedness_forces_ultimate_ground (Entity : Type) (GroundEntity : ` | {}  |

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
