# Investigation: Contrastive Choice, Action, and Axiom A14

**Repository:** Γ (Logos)  
**Primary Formal Source:** `formal/Logos/Agency.lean`, `formal/Logos/Choice.lean`, `formal/Logos/A14SemanticAudit.lean`, `formal/Logos/BipolarityRetorsion.lean`  
**Kernel Status:** SEMANTIC BRIDGE A14 (`AxIntentionalChoice`, Tag: SEM) / INDEPENDENCE THEOREMS (`{}`)  

---

## 1. The Problem: From Action to Deliberative Choice

Can Free Will be derived from bare action without a normative bridge?
In Γ's foundational vocabulary:
- **Weak Act (`act`):** An arbitrary physical or causal event performed by a subject (`formal/Logos/Agency.lean:50`).
- **Strong Act (`Act`):** An intentional event where the agent means the performed content:
  $$\text{Act}(s, p) \equiv \text{Means}(s, p) \land \exists w w',\; \text{Initiates}(s, w, w', p) \quad (\text{Agency.lean:75}).$$
- **Choice Field (`ChoiceField`):** The logical availability of contrary possibilities:
  $$\text{ChoiceField}(s, p, \neg p) \equiv \text{Means}(s, p) \land \text{Incompatible}(p, \neg p) \quad (\text{Choice.lean:80}).$$
- **Genuine Choice (`Chooses`):** The deliberate co-apprehension of both incompatible alternatives:
  $$\text{Chooses}(s, p, q) \equiv \text{Means}(s, p) \land \text{Means}(s, q) \land \text{Incompatible}(p, q) \quad (\text{Choice.lean:105}).$$

---

## 2. The Orthogonality Proof: Why Logic Alone Fails

In `formal/Logos/A14SemanticAudit.lean:120-160`, Γ machine-checked the independence theorem:
$$\text{PreA14Theory} \not\vdash \exists s\, p\, q,\; \text{Chooses}(s, p, q).$$
* **The Countermodel (`act_orthogonal_to_genuine_choice_in_full_theory`):**  
  An agent can initiate an intentional act (`Act s p`) by focusing entirely on $p$, while their intentional state (`Means`) never represents $\neg p$.
* **Model $M_{\text{opaque}}$ (`formal/Logos/BipolarityRetorsion.lean:110`):**  
  Proves that in uninterpreted semantics, meaning $p$ does not logically entail meaning $\neg p$.

---

## 3. The Constitutive Semantic Principle A14 (`AxIntentionalChoice`)

To close the bridge between Strong Act and Genuine Choice, Γ explicitly introduced **A14** as a declared semantic axiom (`Tag: SEM`):

```lean
/-- Tag: SEM
    AxIntentionalChoice (A14): Genuine choice is constitutive of intentional action. -/
axiom AxIntentionalChoice :
  ∀ (s : Subject) (p : Prop), Act s p → ∃ q : Prop, Chooses s p q
```
(`formal/Logos/Choice.lean:1408`).

Under A14:
$$\text{Act}(s, p) \implies \exists q,\; \text{Chooses}(s, p, q) \implies \text{FreeWill}(s).$$

---

## 4. Comparison: A13 vs A14 vs The Direct Normative Route

1. **A13 (`AxActPolarity`):** Assumes the agent specifically grasps the contradictory negation: $\text{Act}(s, p) \implies \text{Means}(s, \neg p)$. Strictly entails A14 (`act_polarity_implies_intentional_choice`).
2. **A14 (`AxIntentionalChoice`):** The minimal pointwise semantic bridge: an intentional act constitutively selects against some co-grasped incompatible alternative $q$.
3. **The Direct Normative Route (`IndubitableNormativeFreeWill`):** Bypasses A13 and A14 entirely by extracting `Chooses` directly from the constitutive definition of `GenuineNormativity` with **zero substantive axioms**.

---

## 5. Architectural Role

A14 is an alternative, action-based route to Free Will. The primary route in Γ remains the **Normative Route** (`Right/Wrong → GenuineNormativity → FreeWill`), while A14 serves as an explicit, honest semantic bridge for the action-theoretic branch.
