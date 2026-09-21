# Investigation: The Normative Route to Free Will

**Repository:** Γ (Logos)  
**Primary Formal Source:** `formal/Logos/IndubitableNormativeFreeWill.lean`, `formal/Logos/UndeniableNormativeDerivation.lean`  
**Kernel Status:** LOGICAL derivation from CONSTITUTIVE SEMANTICS (`{Means, Subject}`, 0 substantive axioms)  

---

## 1. Overview of the Normative Chain

The primary deduction of Free Will in Γ does not rely on Cartesian introspection, physical indeterminism, or unanalyzed voluntarism. It proceeds along an explicit normative chain:

$$\text{Right / Wrong} \longrightarrow \text{Ought / OughtNot} \longrightarrow \text{Incompatible Alternatives} \longrightarrow \text{Agential Address} \longrightarrow \text{Co-Apprehension} \longrightarrow \text{Choice} \longrightarrow \boxed{\text{Free Will}}$$

---

## 2. Formal Deconstruction of the Spine

### Step 1: Deontic Opposition (The Two Normative Poles)
Normative authority commands the Right ($p$) and forbids the Wrong ($q$). The two terms are distinct and logically incompatible:
```lean
def DeonticOpposition (p q : Prop) : Prop :=
  Incompatible p q ∧ (p ≠ q)
```
(`formal/Logos/IndubitableNormativeFreeWill.lean:66`).

### Step 2: Agential Deontic Address (Normativity is Directed)
An impersonal directive commands nobody. A genuine normative law is addressed to an agent $s$ who is cognitively capable of grasping both what is commanded and what is prohibited:
```lean
def AgentialDeonticAddress (s : Subject) (p q : Prop) : Prop :=
  Means s p ∧ Means s q
```
(`formal/Logos/IndubitableNormativeFreeWill.lean:78`).

### Step 3: Genuine Normativity
Combining deontic opposition with agential address defines genuine prescriptive normativity:
```lean
structure GenuineNormativity (s : Subject) (p q : Prop) : Prop where
  opposition : DeonticOpposition p q
  address    : AgentialDeonticAddress s p q
```
(`formal/Logos/IndubitableNormativeFreeWill.lean:84`).

---

## 3. The Master Kernel Proof of Free Will

In `formal/Logos/IndubitableNormativeFreeWill.lean:115`, the complete derivation is checked with zero substantive axioms:

```lean
theorem indubitable_normative_free_will
    {s : Subject} {p q : Prop} (h : GenuineNormativity s p q) :
    Chooses s p q ∧ FreeWill s := by
  have hMeansP : Means s p := h.address.1
  have hMeansQ : Means s q := h.address.2
  have hIncomp : Incompatible p q := h.opposition.1
  have hChooses : Chooses s p q := ⟨hMeansP, hMeansQ, hIncomp⟩
  have hFreeWill : FreeWill s := ⟨p, q, hChooses⟩
  exact ⟨hChooses, hFreeWill⟩
```

* **Footprint:** `{Means, Subject}` (pure vocabulary, zero substantive axioms).
* **Non-Circularity:** `Chooses` is extracted purely by projection from the components of `GenuineNormativity` (`normativity_projects_to_chooses`, `formal/Logos/UndeniableNormativeDerivation.lean:175`).

---

## 4. Modal Extension: Necessary Free Will

If genuine normativity is a modally necessary feature of reality, then Free Will is modally necessary across all worlds:
```lean
theorem necessary_normativity_implies_necessary_free_will
    {World : Type} (hNec : NecessaryGenuineNormativity World) :
    ∀ w : World, ∃ (s : Subject), FreeWill s
```
(`formal/Logos/IndubitableNormativeFreeWill.lean:133`).

---

## 5. Epistemic Assessment

- **Logical:** The step from `GenuineNormativity s p q` to `Chooses s p q ∧ FreeWill s` is **100% deductive logic**.
- **Constitutive Semantic:** The premise that Right and Wrong constitute an agential directive addressed to a subject between incompatible alternatives is a **substantive semantic commitment**.
