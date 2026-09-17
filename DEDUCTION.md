# Γ — Deduction Map (mapa da dedução)

Versão derivada do estado formal atual. Este documento é **gerado** por `scripts/build_deduction.py` — não o edite à mão (regra de sincronização em `AGENTS.md`).

- **Fonte Lean:** `formal/Logos/*.lean` (kernel-checked, `lake build` verde, sorryAx 0)
- **Pegadas do kernel:** `formal/axiom_audit.json` (`#print axioms` por declaração — a pegada axiomática transitiva exata, meta-lógica incluída)
- **Tipos de axioma:** a linha `Tag:` (`VOCAB`/`SEM`/`META`) na docstring Lean de cada axioma
- **Grafo de dependências:** `formal/depgraph.json` (LeanDepViz, kernel)
- **Ledger GAPMAP:** [`formal/GAPMAP.md`](formal/GAPMAP.md) (IDs, refs de prosa, transcrição de estatuto/pegada — *verificada*, nunca usada como fonte)
- **Prosa:** [`base.txt`](base.txt) (argumento §0–§29) · [`poem.txt`](poem.txt) (P1–P10) · [`theorems/`](theorems/)

Regeneração: `python3 scripts/audit_footprints.py && python3 scripts/build_deduction.py`

---

## Legenda

| Token | Significado |
|---|---|
| `✔` | teorema verificado pelo kernel, pegada sem axioma substantivo (vazia, `CL` ou só vocabulário) |
| `⚠` | teorema verificado sob axiomas substantivos — quais, no próprio passo (`Segue de: … e do axioma …`) |
| `◆` | declaração (`axiom`) — não derivada |
| `✖` | em falta um lema nomeado (ver **Deferred / blocked**) |
| `➖` | fora do âmbito deste marco |
| `→` | dissolvido numa entrada já apresentada (`Vide …`) |
| `CL` | meta-lógica clássica `{propext, Classical.choice, Quot.sound}` (D1, reportada pelo kernel) |
| `✔` (só vocabulário) | teorema **axiom-free módulo vocabulário**: a pegada do kernel só contém vocábulos que o próprio enunciado menciona (`Ground`, `ExistsAt`, `GroundProp`), sem axioma substantivo (SEM/META). Ex.: C15/C60 (a negação refuta-se por definição — RAA), C25/C49/C51/C56/C62 (analíticos), C16/C17. Inventário e justificação em [`VOCAB.md`](VOCAB.md); ver **Relatório de consistência** |
| `An` | axioma exibido em bloco próprio (`### A1 ◆ …`) no 1.º passo que o usa; as linhas `Segue …` referenciam-no por `A#` |

O estatuto de cada passo é **derivado** — função de (tipo do nó no kernel, pegada `#print axioms`, `Tag:` declarada dos axiomas) — e não transcrito do ledger. A transcrição GAPMAP é auto-verificada contra o derivado; o que diverge aparece como **erro de ledger** no **Relatório de consistência**.

Etiquetas de axioma (o `Tag:` declarado na docstring Lean de cada axioma):

| Tag | Significado |
|---|---|
| `SEM` | escolha semântica, com modelo de consistência registado |
| `META` | ponte metafísica, com o preço tornado explícito |
| `VOCAB` | vocabulário primitivo (relação que o próprio enunciado menciona) |

Notação formal: cada passo mostra o *enunciado* em símbolos lógicos (traduzido do Lean), uma frase em inglês com o significado e a linha `Segue de:` — os teoremas-passo a partir dos quais decorre e o(s) axioma(s) do seu pé de kernel (`… e do axioma **A1** / … e dos axiomas **A1**, **A2**`, com `A#` definido no bloco do próprio axioma). As referências de código (ficheiro:linha, pegadas `#print axioms`, dependências e usos no grafo) ficam todas no **Anexo: código por passo**.

---

<details>
<summary>Leitura da notação (símbolos ↔ Lean) →</summary>

Cada passo é o teorema Lean real, escrito em símbolos. Os símbolos e os predicados-tipo usados:

| Símbolo | Lean | Significado |
|---|---|---|
| `¬` · `∧` · `∨` · `→` | `Not` · `And` · `Or` · `Imp` | negação, conjunção, disjunção, implicação |
| `φ ∨ ¬φ` | `Form.or φ (Form.not φ)` | fórmula da linguagem-objecto (não `Prop`) |
| `□ τ` | `NecessarilyTrue τ` | verdade em todo o mundo (`∀ w, TrueAt w τ`) |
| `¬◇ τ` | `NecessarilyFalse τ` | falso em todo o mundo (impossível: `∀ w, FalseAt w τ`) |
| `□ p` | `Necessity p` | caixa ao nível de `Prop` (alias degenerado da identidade, `□p := p`) |
| `□ₚ P` · `∀ w, P(w)` | `NecessityPH P` | caixa ao nível do mundo — a modalidade real |
| `◇ p` | `Dia p` | possibilidade: `¬□(¬p)` |
| `w ⊨ τ` | `TrueAt w τ` / `Satisfies w τ` | a fórmula τ é verdadeira no mundo w |
| `w ⊭ τ` | `FalseAt w τ` | a fórmula τ é falsa no mundo w |
| `atom n` | `Form.atom n` | proposição atómica n da linguagem-objecto |
| `T p` | `T p` (`def T p := p`) | "p é verdadeiro" — a verdade é a identidade (E0) |
| `IsFalse p` | `IsFalse p` | "p é falso" (`:= ¬ T p`) |
| `N_T` ≡ `N_F` | `N_T` · `N_F` | absolutos: "nada é verdadeiro" · "tudo é verdadeiro" |
| `A s p` · `Means s p` | `A s p` (`:= Means s p`) · `Means s p` (`:= ∃ w w', Initiates s w w' p`) | o acto de um sujeito s sobre um conteúdo p — a iniciação de um movimento |
| `Subject` · `Person s` | `Subject` · `Person s` | sort de sujeitos · "s é pessoa" |
| `Chooses s p q` | `Chooses s p q` | o sujeito s escolhe entre as alternativas p e q |
| `Ground e τ` · `ExistsAt w e` | `Ground e τ` · `ExistsAt w e` | a entidade e fundamenta τ · e existe no mundo w |
| `NecessaryEntity e` · `NecessarySubject s` | `NecessaryEntity e` · `NecessarySubject s` | e existe em todo o mundo · s persiste em todo o mundo |
| `Correct s p` · `Incorrect s p` · `Fallible s p` | `Correct` · `Incorrect` · `Fallible` | juízo correto · incorreto · falível do sujeito s sobre p |
| `Incompatible p q` · `Lovable s` · `Loves s₁ s₂` | `Incompatible` · `Lovable` · `Loves` | alternativas incompatíveis · s é amável · o amor de s₁ por s₂ |

O **significado** de cada passo é dado em inglês a seguir ao seu enunciado (o original Lean está numa hiperligação).

</details>

---

## Visão global do argumento

```text
§0  premissa arbitrária ≠ condição cuja negação destrói o ato de a negar
      │
§1  A(s,p)  (ato presente, EXIBIDO — teorema `Cogito`, sem axiomas)
      │  T1 sujeito · T2 conteúdo · §4–§5 absolutos N_T/N_F refutam-se
      │  T3 verdade-e-erro §6 · §7–§21 verdade/vontade/correção/consequência
      ├──→ §22–§23 necessidade (excluded middle / não-contradição)
      ├──→ §24a truthmaker atómico · T7 realidade necessária (AxGlobalGround)
      ├──→ §24b pessoa · T8 fundamento pessoal (AxPersonalGround, META)
      ├──→ §13–§15 escolha · T11 campo de escolha · T9 alternativas
      └──→ P5/P7 pluralidade (derivada — par canónico C73, `{}`) · P7/P8 amor (T13·T14)
                AxPersonStability (SEM) — 'de alguma forma'
```

Camadas de conclusão (base.txt §0): performativamente inegável → logicamente inegável → transcendentalmente necessário → metafisicamente necessário **se a ponte for demonstrada**.

---
## Level 0 — performative core (`Logos.Core`)

### C1 · ✔
`¬ T N_T` — _It cannot be true that nothing is true: asserting 'nothing is true' would itself be a true proposition._
[§4](base.txt)

### C2 · ✔
`¬ N_T` — _It is false that nothing is true: some proposition is true._
Segue de: **C1** — [§4](base.txt)

### C3 · ✔
`∃ p : Prop, T p` — _Some proposition is true._
Segue de: **C2** — [§4](base.txt)

### C4 · ✔
`T True` — _The proposition True is itself true._
[§4](base.txt)

### C5 · ✔
`¬ T N_F` — _It cannot be true that nothing is false: if it were, the falsehood False would be true._
[§5](base.txt)

### C6 · ✔
`¬ N_F` — _It is false that everything is true: some proposition is false._
Segue de: **C5** — [§5](base.txt)

### C7 · ✔
`∃ q : Prop, IsFalse q` — _Some proposition is false._
[§5](base.txt)

### C8 · ✔
`∃ p q : Prop, T p ∧ IsFalse q` — _Truth and falsehood both obtain: some proposition is true and some proposition is false._
Segue de: **C4** — [T3 §6](base.txt) · [T3](theorems/T3.txt)

### C9 · ✔
`∀ p : Prop, ¬ (T p ∧ IsFalse p)` — _No proposition is both true and false._
[§T3](base.txt) · [T3](theorems/T3.txt)

### C10 · ✔
`∀ p : Prop, T (p ∨ ¬ p)` — _For every proposition p, 'p or not-p' is true._
[§22](base.txt)

### C11 · ✔
`∀ p : Prop, T (¬ (p ∧ ¬ p))` — _For every proposition p, 'not (p and not-p)' is true._
[§23](base.txt)

### C12 · ✔
`∀ p : Prop, T p ∨ IsFalse p` — _Every proposition is either true or false._
[§10](base.txt)


---

## Level 1 — semantics (`Logos.Semantics`, `Logos.Truthmaker`, `Logos.Modal`)

### C13 · ✔
`□(φ ∨ ¬φ)` — _In every world, 'φ or not-φ' is true._
[§22](base.txt)

### C14 · ✔
`¬◇(φ ∧ ¬φ)` — _In every world, 'φ and not-φ' cannot be true._
[§23](base.txt)

### A1 ◆ The truthmaker relation — an entity grounding a formula · `VOCAB`
`Ground : Subject → Form → Prop` — _The truthmaker relation — an entity grounding a formula._

### C15 · ✔
`w ⊨ atom n → ∃ e : Entity, ExistsAt w e ∧ Ground e atom n` — _Every atomic truth is grounded: where an atom is true, an entity exists there that grounds it._
Segue do axioma **A1** (vocabulário do enunciado) — [§24a](base.txt)

### C60 · ✔
`¬ (∃ (w : World) (n : Nat), w ⊨ atom n ∧ ¬ (∃ e : Entity, ExistsAt w e ∧ Ground e atom n))` — _The denial that atomic truth is grounded refutes itself: where an atom is true, no world lacks a grounder for it._
Segue do axioma **A1** (vocabulário do enunciado) — [§24a (RAA)](base.txt)

### C16 · ✔
`□(φ ∨ ¬φ)` — _In every world, 'φ or not-φ' is true — composite truth is Tarskian-compositional._
Segue do axioma **A1** (vocabulário do enunciado) — [§22](base.txt)

### C17 · ✔
`¬◇(φ ∧ ¬φ)` — _In every world, 'φ and not-φ' cannot be true._
Segue do axioma **A1** (vocabulário do enunciado) — [§23](base.txt)

### C18 · ✔
`∃ e : Entity, NecessaryEntity e ∧ Ground e atom n` — _Atomic necessary truth forces necessary reality: whatever atom is true in every world is grounded by an entity existing in every world._
Segue do axioma **A1** (vocabulário do enunciado) — [§T7](base.txt) · [T7](theorems/T7.txt)

### C19 · ✖
_There is a necessary reality grounded on the indubitable: some entity existing in every world grounds 'φ or not-φ' (blocked: no existential compound ground is forced)._

### C20 · ✔
`(∀ e : Entity, Contingent e) → ∀ n : Nat, ¬ □atom n` — _If every entity were contingent, no atom could be true in every world._
Segue de: **C18** e do axioma **A1** (vocabulário do enunciado) — [§T7](base.txt) · [T7](theorems/T7.txt)


---

## Level 2 — agency and person (`Logos.Agency`, `Person`, `Alternatives`, `Order`, `GroundPerson`)

### C58 · ✔
`(¬ ∃ s : Subject, ∃ p : Prop, A s p) → False` — _Denying 'some subject acts on some content' refutes itself — the silent origin is exhibited, no axiom cited._
[§1 fnd](base.txt)

### C68 · ✔
`∃ s : Subject, ∃ p : Prop, A s p` — _Some subject acts on some content: the choosing subject exists. Proven, not postulated — exhibited by the silent origin._
[§1 fnd](base.txt)

### C59 · ✔
_Strong truth exists: some formula is true in every world (spike-level, axiom-free)._

### C21 · ✔
`∃ s : Subject, Logos.Agency.Exists s` — _At least one subject exists._
Segue de: **C68** — [§1/T1](base.txt) · [T1](theorems/T1.txt)

### C22 · ✔
`∃ p : Prop, Content p` — _At least one content exists: every proposition is admissible content._
[§T2](base.txt) · [T2](theorems/T2.txt)

### C23 · ✔
`∃ s : Subject, Logos.Agency.Exists s ∧ Logos.Agency.Agent s` — _At least one agent exists: someone who acts._
Segue de: **C68** — [§T4](base.txt) · [T4](theorems/T4.txt)

### C24 · ✔
`∃ s : Subject, Person s` — _At least one person exists._
Segue de: **C68** — [§T5](base.txt) · [T5](theorems/T5.txt)

### C25 · ✔
`∀ a : Prop, RationalAct a → (CarriesPersonalFeature a ↔ CarriesLogicalFeature a)` — _Every rational act carries a personal feature exactly when it carries a logical feature: personhood and logic travel together._
[§24b](base.txt)

### C26 · ✔
`∃ p q : Prop, Incompatible p q ∧ T p ∧ IsFalse q` — _There are two incompatible alternatives, one of them true and the other false._
Segue de: **C4** — [**T9 (new)**](base.txt) · [T9](theorems/T9.txt)

### C27 · ✔
`Incompatible p (¬ p) ∧ T p ∧ IsFalse (¬ p)` — _Every true proposition is incompatible with its own negation._
[§13](base.txt)

### C28 · ✔
`¬ (∀ s : Subject, ∀ p : Prop, Fallible s p → T p)` — _A fallible judgment need not be true: fallibility is real._
[§T6](base.txt) · [T6](theorems/T6.txt)

### C29 · ✔
`¬ (∀ s : Subject, ∀ p : Prop, Fallible s p ↔ T p)` — _Truth is not the same as being fallibly judged: what is true transcends the will to judge._
[§T6](base.txt) · [T6](theorems/T6.txt)

### C30 · ✔
`¬ (∀ s : Subject, ∀ p : Prop, Correct s p ↔ Incorrect s p)` — _Correct and incorrect judging are distinct: correctness is not incorrectness._
Segue de: **C48** — [§8](base.txt)

### C31 · ✔
`T q` — _Consequence preserves truth: whatever two true premises jointly imply is true._
[§9](base.txt)

### A2 ◆ The personal price of T8: what is grounded about a person is grounded in a personal way · `META`
`AxPersonalGround : ∀ {f : Prop}, IsPresentPersonalFeature f → ∃ e : Entity, NecessaryEntity e ∧ GroundProp e f` — _The personal price of T8: what is grounded about a person is grounded in a personal way._

### A3 ◆ The grounding relation between an entity and a proposition · `VOCAB`
`GroundProp : Entity → Prop → Prop` — _The grounding relation between an entity and a proposition._

### C32 · ⚠
`∃ e : Entity, NecessaryEntity e ∧ Personal e` — _Every present personal feature is grounded by a necessary, personal entity._
Segue dos axiomas **A2**, **A3** — [§T8](base.txt) · [T8](theorems/T8.txt)

### A4 ◆ The §24a atom-grounding principle reflected at the level of propositions · `SEM`
`GroundPrincipleProp : ∀ {f : Prop}, T f → ∃ e : Entity, GroundProp e f` — _The §24a atom-grounding principle reflected at the level of propositions._

### C33 · ⚠
`∃ e : Entity, GroundProp e f` — _Every true present personal feature has a ground._
Segue dos axiomas **A3**, **A4** — [§T8](base.txt) · [T8](theorems/T8.txt)

### C34 · ✔
`∃ e : Entity, NecessaryEntity e` — _Every necessary atomic truth has a necessary grounder._
Segue de: **C18** e do axioma **A1** (vocabulário do enunciado) — [§T8](base.txt) · [T8](theorems/T8.txt)


---

## Level 3 — modal, choice, interpersonal value (new: poem chain)

### C35 · ✔
`¬ (N_T ∨ N_F)` — _It is neither the case that nothing is true, nor that nothing is false._
Segue de: **C2**, **C6** — [P2](poem.txt)

### C36 · ✔
`¬ N_T ∧ ¬ N_F` — _Right and wrong both obtain: it is false that nothing is true, and false that everything is true._
Segue de: **C2**, **C6** — [P2](poem.txt)

### C37 · ✔
`(∃ τ : Form, □ τ) ∧ (∃ ρ : Form, ¬◇ ρ)` — _In every world there is necessarily-true content and necessarily-false content._
Segue de: **C13**, **C14** — [P2](poem.txt)

### C38 · ✔
`□(¬ N_T ∧ ¬ N_F)` — _The distinction between right and wrong is necessary: it is false that nothing is true, and false that everything is true._
Segue de: **C36** — [P2](poem.txt)

### C39 · ✔
`∃ s : Subject, Person s ∧ ∃ p q : Prop, Incompatible p q` — _There is a field of choice: some person with two incompatible alternatives._
Segue de: **C24**, **C26** — [P4](poem.txt)

### C40 · ✔
`∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂` — _There are at least two distinct persons._
Segue de: **C73** — [P5/P7](poem.txt)

### C41 · ✔
`∃ s t : Subject, Person s ∧ Person t ∧ s ≠ t ∧ Lovable s ∧ Lovable t` — _There is someone lovable and someone who loves: both are persons and distinct._
Segue de: **C40** — [P7](poem.txt)

### C48 · ✔
`∃ s : Subject, ∃ p : Prop, Logos.Agency.A s p` — _The acting subject is exhibited: someone acts on something._
Segue de: **C68** — [P1/§1](poem.txt)

### C49 · ✔
`∃ t : Subject, Means t p` — _Meaning needs a subject: whatever is meant is meant by someone._
[§13/IM_STUPID](base.txt)

### C50 · ✔
`Incompatible p (¬ p)` — _Every proposition is incompatible with its own negation._
[§14](base.txt)

### C51 · ✔
`∃ p q : Prop, Chooses s p q` — _Any person chooses: a person always has two incompatible alternatives to choose between._
Segue de: **C50** — [§14/IM_STUPID](base.txt)

### C52 · ✔
`∃ s : Subject, ∃ p q : Prop, Chooses s p q` — _Choice exists: some subject chooses between two incompatible alternatives._
Segue de: **C24**, **C51**, **F1a** — [§14](base.txt)

### C53 · ✔
`(¬ ∃ s : Subject, ∃ p q : Prop, Chooses s p q) → False` — _Denying choice refutes itself: the denial is itself a choice._
Segue de: **C52** — [§14](base.txt)

### C54 · ✔
`(¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) → ∃ s : Subject, ∃ p q : Prop, Chooses s p q` — _Right-and-wrong commits a chooser: where there is truth and error, someone has chosen._
Segue de: **C52** — [IM_STUPID §2](base.txt)

### C55 · ✔
`∃ s : Subject, ∃ p q : Prop, A s p ∧ (Correct s p ∨ Incorrect s p) ∧ Chooses s p q` — _The judge is a chooser: whoever judges acts and chooses, correctly or incorrectly._
Segue de: **C48**, **C50** — [§8/§14](base.txt)

### C56 · ✔
`(¬ ∃ t : Subject, t ≠ s ∧ Helps s t) ∧ (¬ ∃ t : Subject, t ≠ s ∧ Harms s t)` — _A lone subject neither helps nor harms anyone else._
[P6](poem.txt)

### C57 · ✔
`(¬ ∃ _s : Subject, True) → False` — _Denying 'a subject exists' refutes itself: the denial is itself an act._
Segue de: **C52** — [§26](base.txt)

### C42 · ✔
`∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ Loves s₁ s₂ ∧ NecessarySubject s₁ ∧ NecessarySubject s₂` — _Two distinct persons stand in an eternal love-relation, and both persist in every world._
Segue de: **C47** — [P8](poem.txt)

### C43 · ✔
`∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ Loves s₁ s₂` — _Two distinct persons stand in a love-relation._
Segue de: **C42** — [P8](poem.txt)

### C44 · ✔
`∀ w, ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ Loves s₁ s₂ ∧ ExistsAt _w (EntityOf s₁) ∧ ExistsAt _w (EntityOf s₂)` — _In every world, two distinct persons stand in a love-relation._
Segue de: **C42** — [P8](poem.txt)

### C45 · ✔
`□(∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ Loves s₁ s₂)` — _Necessarily, two distinct persons stand in a love-relation._
Segue de: **C42** — [P8](poem.txt)

### C46 · ✔
`(¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) → ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ (Affects s₁ s₂ ∨ Affects s₂ s₁)` — _Right-and-wrong yields two distinct persons who bear on each other._
Segue de: **C73** — [P5](poem.txt)

### C47 · ✔
`∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ Affects s₁ s₂` — _There are two distinct persons where one bears on the other._
Segue de: **C40** — [P5/P7](poem.txt)

### C61 · ✔
`(¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) → ∃ s : Subject, ∃ p : Prop, Means s p` — _Right-and-wrong implies someone who means (poem P3, line 18 "há certo e há errado → há significado → há alguém para quem algo significar")._
Segue de: **C54** — [P3](poem.txt)

### C62 · ✔
`∃ p : Prop, Logos.Choice.Meaning_I p` — _Right and wrong need meaning: the normative predicates are properties of meaning-acts, so wherever right-or-wrong is realized, a meaning (and thus a subject, C49) is realized._
[P3](poem.txt)

### C69 · ✔
`FreeWill (Sum.inl ()) p` — _The silent origin always could have chosen otherwise: it can choose p and can choose ¬p._
[§15/F1b](base.txt)

### C70 · ✔
`¬ FreeWill (Sum.inr q) p` — _A posited content cannot choose otherwise: `¬ FreeWill (Sum.inr q) p` for every `p`._
[§15/F1b](base.txt)

### C71 · ✔
`(¬ FreeWill (Sum.inl ()) p) → False` — _Denying that you could have chosen otherwise refutes itself: the denial is an act of the free origin._
Segue de: **C69**, **F7** — [§15/F1b](base.txt)

### C72 · ✔
`∃ s : Subject, Person s ∧ ∃ p : Prop, FreeWill s p` — _The chooser that right-and-wrong commits is free: some person can choose both ways._
Segue de: **C69**, **F7** — [§15/F1b](base.txt)

### C73 · ✔
`∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂` — _The canonical pair: the origin and the addressee are two distinct persons._
[P5/P7](poem.txt)

### C74 · ✔
`¬ ∃ s : Subject, Person s ∧ Alone s` — _No person is alone: there is no personal lone subject._
[P5](poem.txt)

### C75 · ✔
`∀ p : Prop, Person (Sum.inr p)` — _Every content, raised to a subject, is a person._
[P7](poem.txt)

### C76 · ✔
`Person (Sum.inl ()) ∧ Person (Sum.inr True) ∧ Loves (Sum.inl ()) (Sum.inr True) ∧ (∀ w : World, ExistsAt w (EntityOf (Sum.inl ())) ∧ ExistsAt w (EntityOf (Sum.inr True)))` — _The canonical eternal relation: the origin and the addressee love each other, and persist, in every world._
[P8](poem.txt)

### C77 · ✔
`∃ s : Subject, Person s ∧ NecessarySubject s` — _There exists a necessary person: someone who is a person and persists in every world._
Segue de: **C24** — [P5/P8](poem.txt)


---

## Level 2c — the act as initiation (`Logos.Initiation`, 2026-09-17)

### C63 · ✔
`¬ IsTransfer R` — _Initiation is not transfer: a relation with genuine alternatives is not the graph of any function._
[§1](base.txt)

### C64 · ✔
`¬ IsTransfer (Moves s)` — _A subject whose movement branches does not transfer movement: its outcome is not a function of its prior state._
Segue de: **C63** — [§1](base.txt)

### C65 · ✔
`Person s ↔ Originates s` — _A person is exactly a subject that originates an act._
[§1/T5](base.txt) · [T5](theorems/T5.txt)

### C66 · ✔
`∃ s : Subject, Originates s` — _The exhibited act, restated: the present subject originates an act._
Segue de: **C68** — [§1 fnd](base.txt)

### C67 · ✔
`(¬ ∃ s : Subject, Originates s) → False` — _Denying that any subject originates an act refutes itself: the origin is exhibited, no axiom cited._
Segue de: **C66** — [§1 fnd](base.txt)


---

## Deferred / blocked

| ID | Prosa | Status | Nota / lema em falta |
|---|---|---|---|
| F1a | §13–§15 choice-existence (`∃s p q`, `Chooses s p q`) | ✔ | person_chooses/choiceExists {} + judge_commits CL (choice-realism batch, C51–C52/C55) |
| F2 | §21 teleology (`Ought → Goal`) | ➖ | deontic layer (normativity → telos) |
| F3 | §28 Good (`§20 → bem`) | ➖ | moral good from logical normativity not yet derived |
| F4 | §28 Love | ✔ | Love.T13_someoneLovable (C41) under the derived plurality — no bridge (definitional subject, 2026-09-17; old bridge AxTwoSubjects retired) |
| F5 | §28 EternalRelation | ✔ | T14 under the derived plurality + esse est agere (AxPersonStability theorem); T14_canonicalRigid strengthens it to a world-rigid canonical pair |
| F6 | §28 Trinity | ➖ | no argument exists yet (§28/§29) |
| Q7.2 | weaker `AxGlobalGround` | ANSWERED | answered by batch A2-swap-theorem: for atoms the swap needs no premise at all (definitional via world-vacuous ExistsAt); the compound instance is unforced, not weaken-able (DESIGN.md) |

### F1a · →
*Vide **C51** (passo já apresentado).*

### F2 · ➖
_Deontic teleology is deferred: how norms point at goals is not yet derived._

### F3 · ➖
_Moral good from logical normativity is deferred: not yet derived._

### F4 · →
*Vide **C41** (passo já apresentado).*

### F5 · →
*Vide **C76** (passo já apresentado).*

### F6 · ➖
_The Trinity is deferred: no argument exists yet._

### Q7.2 · ANSWERED
`ExistsAt (_w : World) (s : Subject) : Prop` — _Existence as agency (esse est agere): an entity exists in a world iff it acts._
[weaker `AxGlobalGround`](base.txt)


---
## Faith / DEFERRED

| ID | Prosa | Status | Nota / lema em falta |
|---|---|---|---|
| FAITH-1 | P2 necessity | → | dissolved in C1: necDistinction is now a theorem (C38); world content = C37 |
| FAITH-2 | P8 eternal love | → | dissolved in C4: replaced by AxPersonStability (theorem, esse-est-agere) + the derived plurality (plurality-discharge: retired AxTwoSubjects); T14 is a theorem {} (C42–C45, C76) |
| F7 | §15 the bipolar half of freedom | ✔ | = F1b split (2026-09-17): the origin's both-ways capacity is proven (freeWillOrigin {}); world-level alternativity blocked on missing world-varying vocabulary (ChoiceAt) |
| F8 | Trinity | ➖ | not attempted (§28/§29) |
| F9 | Incarnation / creation | ➖ | poem P10, faith datum |

### FAITH-1 · →
*Vide **C38** (passo já apresentado).*

### FAITH-2 · →
`∀ s : Subject, Person s → NecessarySubject s` — _Persons persist across worlds: whoever is a person exists in every world — the poem's 'somehow'._
[P8 eternal love](poem.txt)

### F7 · →
*Vide **C69** (passo já apresentado).*

### F8 · ➖
_The Trinity is not attempted._

### F9 · ➖
_Incarnation and creation are faith data from the poem, deferred._


---
## Inventário de axiomas (4 declarações)

| Axioma | Nº | Tag | Significado (EN) / preço | Depende dele (claims) |
|---|---|---|---|---|
| `AxPersonalGround` | A2 | `META` | The personal price of T8: what is grounded about a person is grounded in a personal way. | C32 |
| `GroundPrincipleProp` | A4 | `SEM` | The §24a atom-grounding principle reflected at the level of propositions. | C33 |
| `GroundProp` | A3 | `VOCAB` | The grounding relation between an entity and a proposition. | C32, C33 |
| `Ground` | A1 | `VOCAB` | The truthmaker relation — an entity grounding a formula. | C15, C16, C17, C18, C20, C34, C60 |

Detalhe do kernel:

- `Logos.GroundPerson.AxPersonalGround`
- `Logos.GroundPerson.GroundPrincipleProp`
- `Logos.GroundPerson.GroundProp`
- `Logos.Truthmaker.Ground`

---
## Relatório de consistência (kernel ↔ GAPMAP)

- Claims do GAPMAP com teorema localizado no kernel: **82** / 89
- Steps com **significado em inglês**: **89** / 89
- **Claims sem teorema localizado** (sem dedução no kernel do mapa):
  - `C19` ref `Modal.T7_excludedMiddleInstance` — T7
  - `C59` ref `Spike_M5.strongTruthExists` — §27
- Teoremas no kernel **sem claim** no GAPMAP (42): Agency.act_implies_agent, Agency.act_implies_content, Agency.act_implies_exists, Agency.act_implies_means, Agency.act_implies_rational, Choice.canChoose_unfold, Choice.meaning_I_needs_subject, Core.atomicWitnessFalsehood, Core.someTruthAndSomeFalsehood, Core.tschema, GroundPerson.AxGroundBearing, Love.canonicalNecessaryPerson, Modal.AxGlobalGround, Necessity.dia_def, Necessity.nec4, Necessity.nec4PH, Necessity.necDistinction_content, Necessity.necK, Necessity.necKPH, Necessity.necMP, Necessity.necT, Necessity.necTPH, Necessity.nec_apply, Order.fallible_false, Order.rightDistinctWrong_implies_meaning, Order.rightWrongDistinction_implies_meaning, Person.positedDistinct, Plurality.notAlone, Semantics.sat_and, Semantics.sat_imp, Semantics.sat_not, Semantics.sat_or, Truthmaker.sat_ground_and, Truthmaker.sat_ground_imp, Truthmaker.sat_ground_not, Truthmaker.sat_ground_or, Value.AxPersonsAffect, Value.alone_no_other_affects, Value.harm_affects, Value.help_affects, Value.neverAlone, Value.otherSubject_ne
- **Estatuto derivado do kernel** (#print axioms + `Tag:` dos axiomas): **77 ✔** · **2 ⚠** · **0 ◆**
- Estatuto GAPMAP × derivado: **sem divergências** (transcrição verificada).
- **Steps ⚠ sob axioma substantivo (SEM/META)** (2): C32, C33
- **Exibidos ✔ por só-vocabulário** (pegada do kernel só com os vocábulos do próprio enunciado — SEM/META nenhum; em C15/C60 a negação refuta-se por definição, RAA): C15, C16, C17, C18, C20, C34, C60
- Pegada kernel × GAPMAP: **sem divergências**.
- **Grafo (closure) × audição (#print axioms) divergem em 2 claims** (subconta transitiva do depviz — toolchain, não ledger; a audição manda):
  - `C16` audição `{Ground}` vs grafo `{}`
  - `C17` audição `{Ground}` vs grafo `{}`
- Axiomas declarados no kernel: **4** — **todos com `Tag:` na docstring Lean**
## Anexo: código por passo

<details>
<summary>Declaração Lean, ficheiro:linha, pegadas e dependências de código, por passo →</summary>

| ID | Declaração Lean | Ficheiro#L | Axiomas (kernel) | Pegada GAPMAP | Depende (Lean) | Usado por |
|---|---|---|---|---|---|---|
| C1 | `Logos.Core.nothingTrueRefutes` | [Core.lean#L61](formal/Logos/Core.lean#L61) | `{}` | {} (E0: T := id) | `Core.N_T`, `Core.T`, `Core.tschema` | **C2** `notNothingTrue` |
| C2 | `Logos.Core.notNothingTrue` | [Core.lean#L69](formal/Logos/Core.lean#L69) | `{}` | {} (E0) | `Core.N_T`, `Core.T`, **C1** `nothingTrueRefutes`, `Core.tschema` | **C35** `negatedAbsolutes`, **C36** `rightWrongDistinction`, **C3** `someTrue` |
| C3 | `Logos.Core.someTrue` | [Core.lean#L77](formal/Logos/Core.lean#L77) | `{CL}` | CL | `Core.N_T`, `Core.T`, **C2** `notNothingTrue` | `Core.someTruthAndSomeFalsehood` |
| C4 | `Logos.Core.atomicTruthWitnessed` | [Core.lean#L85](formal/Logos/Core.lean#L85) | `{}` | {} (E0) | `Core.T`, `Core.tschema` | **C26** `T9_incompatibleAlternatives`, **C8** `greatResult` |
| C5 | `Logos.Core.nothingFalseRefutes` | [Core.lean#L94](formal/Logos/Core.lean#L94) | `{}` | {} (E0) | `Core.N_F`, `Core.T`, `Core.tschema` | **C6** `notEverythingTrue` |
| C6 | `Logos.Core.notEverythingTrue` | [Core.lean#L103](formal/Logos/Core.lean#L103) | `{}` | {} (E0) | `Core.N_F`, `Core.T`, **C5** `nothingFalseRefutes`, `Core.tschema` | **C35** `negatedAbsolutes`, **C36** `rightWrongDistinction` |
| C7 | `Logos.Core.someFalse` | [Core.lean#L111](formal/Logos/Core.lean#L111) | `{}` | {} (E0) | `Core.IsFalse`, `Core.T`, `Core.tschema` | `Core.someTruthAndSomeFalsehood`, `Order.fallible_false` |
| C8 | `Logos.Core.greatResult` | [Core.lean#L156](formal/Logos/Core.lean#L156) | `{}` | {} (E0) | `Core.IsFalse`, `Core.T`, **C4** `atomicTruthWitnessed`, `Core.atomicWitnessFalsehood` | — |
| C9 | `Logos.Core.noBothTrueAndFalse` | [Core.lean#L162](formal/Logos/Core.lean#L162) | `{}` | {} (pure logic) | `Core.IsFalse`, `Core.T` | — |
| C10 | `Logos.Core.excludedMiddle` | [Core.lean#L174](formal/Logos/Core.lean#L174) | `{CL}` | CL | `Core.T`, `Core.tschema` | — |
| C11 | `Logos.Core.nonContradiction` | [Core.lean#L180](formal/Logos/Core.lean#L180) | `{}` | {} (E0) | `Core.T`, `Core.tschema` | — |
| C12 | `Logos.Core.bivalence` | [Core.lean#L186](formal/Logos/Core.lean#L186) | `{CL}` | CL | `Core.IsFalse`, `Core.T` | — |
| C13 | `Logos.Semantics.lawExcludedMiddle` | [Semantics.lean#L76](formal/Logos/Semantics.lean#L76) | `{CL}` | CL | `Semantics.Form`, `Semantics.NecessarilyTrue`, `Semantics.Satisfies`, `Semantics.TrueAt`, `Semantics.World`, `Semantics.sat_not`, `Semantics.sat_or` | **C37** `bothNecessarilyTrueAndFalse` |
| C14 | `Logos.Semantics.nonContradiction` | [Semantics.lean#L85](formal/Logos/Semantics.lean#L85) | `{CL}` | {propext} | `Semantics.FalseAt`, `Semantics.Form`, `Semantics.NecessarilyFalse`, `Semantics.Satisfies`, `Semantics.World`, `Semantics.sat_and`, `Semantics.sat_not` | **C37** `bothNecessarilyTrueAndFalse` |
| C15 | `Logos.Truthmaker.groundPrinciple_atom` | [Truthmaker.lean#L86](formal/Logos/Truthmaker.lean#L86) | `{Ground}` | {Ground} (VOCAB — footprint is the statement's own vocabulary; proof is a definitional collapse, P → P; see C60; esse-est-agere batch drops ExistsAt, now a def) | `Semantics.World`, `Truthmaker.Entity`, **Q7.2** `ExistsAt`, axiom `Ground` (VOCAB), `Truthmaker.TrueAt` | `Modal.AxGlobalGround` |
| C60 | `Logos.Truthmaker.noGround_selfRefutes` | [Truthmaker.lean#L99](formal/Logos/Truthmaker.lean#L99) | `{Ground}` | {Ground} (VOCAB — denial refutes itself by definition: TrueAt w (atom n) unfolds to ∃e, ExistsAt w e ∧ Ground e (atom n) with ExistsAt now agency itself, so the denial is ∃e… ∧ ¬∃e…; companion of C15) | `Semantics.World`, `Truthmaker.Entity`, **Q7.2** `ExistsAt`, axiom `Ground` (VOCAB), `Truthmaker.TrueAt` | — |
| C16 | `Logos.Truthmaker.lawExcludedMiddle` | [Truthmaker.lean#L128](formal/Logos/Truthmaker.lean#L128) | `{Ground, CL}` | CL + {Ground} (A2: AxOr/AxNot dropped; esse-est-agere drops ExistsAt) | `Semantics.Form`, `Semantics.World`, `Truthmaker.NecessarilyTrue`, `Truthmaker.TrueAt` | — |
| C17 | `Logos.Truthmaker.nonContradiction` | [Truthmaker.lean#L136](formal/Logos/Truthmaker.lean#L136) | `{Ground}` | {Ground} (A2: AxAnd/AxNot dropped; no propext; esse-est-agere drops ExistsAt) | `Semantics.Form`, `Semantics.World`, `Truthmaker.NecessarilyFalse`, `Truthmaker.TrueAt` | — |
| C18 | `Logos.Modal.T7_necessaryReality` | [Modal.lean#L69](formal/Logos/Modal.lean#L69) | `{Ground}` | {Ground} (VOCAB — batch A2-swap-theorem: AxGlobalGround axiom → theorem) | `Modal.AxGlobalGround`, `Modal.NecessaryEntity`, `Modal.actualWorld`, `Semantics.World`, `Truthmaker.Entity`, **Q7.2** `ExistsAt`, axiom `Ground` (VOCAB), `Truthmaker.NecessarilyTrue` | **C34** `necessary_truth_has_necessary_grounder`, **C20** `noNecessaryTruthIfAllContingent` |
| C19 | — | — | — | missing lemma ∃ e, Ground e (or θ (not θ)) given EM-necessity — no existential compound ground is forced by structural TrueAt (transcript: formal/Spikes/Spike_A6_probe.lean) | Modal.T7_excludedMiddleInstance | — |
| C20 | `Logos.Modal.noNecessaryTruthIfAllContingent` | [Modal.lean#L78](formal/Logos/Modal.lean#L78) | `{Ground}` | {Ground} (VOCAB — as C18) | `Modal.Contingent`, `Modal.NecessaryEntity`, **C18** `T7_necessaryReality`, `Truthmaker.Entity`, axiom `Ground` (VOCAB), `Truthmaker.NecessarilyTrue` | — |
| C58 | `Logos.Agency.noCogito_selfRefutes` | [Agency.lean#L137](formal/Logos/Agency.lean#L137) | `{}` | {} (the silent origin is exhibited definitionally; no axiom cited) | `Agency.A`, `Agency.Initiates`, `Agency.State`, `Agency.Subject` | — |
| C68 | `Logos.Agency.Cogito` | [Agency.lean#L129](formal/Logos/Agency.lean#L129) | `{}` | {} (witness Sum.inl (): the silent origin sustains every posit; definitional subject, 2026-09-17) | `Agency.A`, `Agency.Initiates`, `Agency.State`, `Agency.Subject` | **C66** `Cogito_Init`, **C21** `T1_subjectExists`, **C23** `T4_agentExists`, **C24** `T5_personExists`, **C48** `cogito_from_T12` |
| C59 | — | — | — | **{CL}** (C37 lever) | Spike_M5.strongTruthExists | — |
| C21 | `Logos.Plurality.T1_subjectExists` | [Plurality.lean#L79](formal/Logos/Plurality.lean#L79) | `{}` | {} (kind-preds Agent/Rational are defs; datum now the exhibited theorem Cogito) | `Agency.A`, **C68** `Cogito`, `Agency.Exists`, `Agency.Subject` | — |
| C22 | `Logos.Agency.T2_contentExists` | [Agency.lean#L175](formal/Logos/Agency.lean#L175) | `{}` | **{}** — Content _ := True (def), True witnesses content; cogito not needed (was {cogito} + 6 kind-preds) | `Agency.Content` | — |
| C23 | `Logos.Plurality.T4_agentExists` | [Plurality.lean#L87](formal/Logos/Plurality.lean#L87) | `{}` | {} (as C21; Agent is := True, def — agent existence is analytic) | `Agency.A`, `Agency.Agent`, **C68** `Cogito`, `Agency.Exists`, `Agency.Subject` | — |
| C24 | `Logos.Plurality.T5_personExists` | [Plurality.lean#L97](formal/Logos/Plurality.lean#L97) | `{}` | {} (as C21) | `Agency.A`, `Agency.Agent`, **C68** `Cogito`, `Agency.Means`, `Agency.Rational`, `Agency.Subject`, `Person.Intentional`, `Person.Person` | **C39** `T11_choiceField`, **C52** `choiceExists`, **C77** `necessaryPersonExists` |
| C25 | `Logos.Person.inseparability_24b` | [Person.lean#L56](formal/Logos/Person.lean#L56) | `{CL}` | CL (vocab-only — no substantive axiom; see VOCAB.md) | `Agency.A`, `Agency.Means`, `Agency.Subject`, `Agency.act_implies_means`, `Core.IsFalse`, `Core.T`, `Person.CarriesLogicalFeature`, `Person.CarriesPersonalFeature`, `Person.HasFeature`, `Person.RationalAct` | — |
| C26 | `Logos.Alternatives.T9_incompatibleAlternatives` | [Alternatives.lean#L24](formal/Logos/Alternatives.lean#L24) | `{}` | {} (E0) | `Alternatives.Incompatible`, `Core.IsFalse`, `Core.T`, **C4** `atomicTruthWitnessed`, `Core.atomicWitnessFalsehood` | **C39** `T11_choiceField` |
| C27 | `Logos.Alternatives.incompatible_with_negation` | [Alternatives.lean#L35](formal/Logos/Alternatives.lean#L35) | `{}` | {} (E0) | `Alternatives.Incompatible`, `Core.IsFalse`, `Core.T`, `Core.tschema` | — |
| C28 | `Logos.Order.T6_fallibility` | [Order.lean#L90](formal/Logos/Order.lean#L90) | `{}` | {} (from the exhibited act + Core.someFalse) | `Agency.Subject`, `Core.IsFalse`, `Core.T`, `Order.Fallible`, `Order.fallible_false` | — |
| C29 | `Logos.Order.T6_truthTranscendsWill` | [Order.lean#L99](formal/Logos/Order.lean#L99) | `{}` | as C28 | `Agency.Subject`, `Core.IsFalse`, `Core.T`, `Order.Fallible`, `Order.fallible_false` | — |
| C30 | `Logos.Order.correctness_distinct` | [Order.lean#L107](formal/Logos/Order.lean#L107) | `{CL}` | CL (defs act-relative §8 Correct s p := A s p ∧ T p) | `Agency.A`, `Agency.Subject`, `Core.IsFalse`, `Core.T`, `Order.Correct`, `Order.Incorrect`, **C48** `cogito_from_T12` | — |
| C31 | `Logos.Order.consequence_preserves_truth` | [Order.lean#L146](formal/Logos/Order.lean#L146) | `{}` | {} (E0) | `Core.T`, `Core.tschema` | — |
| C32 | `Logos.GroundPerson.T8_personalGround` | [GroundPerson.lean#L108](formal/Logos/GroundPerson.lean#L108) | `{AxPersonalGround, GroundProp}` | {AxPersonalGround, GroundProp} (esse-est-agere drops ExistsAt) | `GroundPerson.AxGroundBearing`, axiom `AxPersonalGround` (META), axiom `GroundProp` (VOCAB), `GroundPerson.IsPresentPersonalFeature`, `GroundPerson.Personal`, `GroundPerson.Realizes`, `Modal.NecessaryEntity`, `Truthmaker.Entity` | — |
| C33 | `Logos.GroundPerson.present_feature_is_grounded` | [GroundPerson.lean#L118](formal/Logos/GroundPerson.lean#L118) | `{GroundPrincipleProp, GroundProp}` | {GroundProp, GroundPrincipleProp} | `Core.T`, axiom `GroundPrincipleProp` (SEM), axiom `GroundProp` (VOCAB), `GroundPerson.IsPresentPersonalFeature`, `Truthmaker.Entity` | — |
| C34 | `Logos.GroundPerson.necessary_truth_has_necessary_grounder` | [GroundPerson.lean#L126](formal/Logos/GroundPerson.lean#L126) | `{Ground}` | {Ground} (VOCAB — as C18) | `Modal.NecessaryEntity`, **C18** `T7_necessaryReality`, `Truthmaker.Entity`, axiom `Ground` (VOCAB), `Truthmaker.NecessarilyTrue` | — |
| F1a | `Logos.Choice.person_chooses` | [Choice.lean#L151](formal/Logos/Choice.lean#L151) | `{}` | — | `Agency.A`, `Agency.Agent`, `Agency.Means`, `Agency.Rational`, `Agency.Subject`, `Alternatives.Incompatible`, `Choice.Chooses`, **C50** `incompatible_self_negation`, `Person.Intentional`, `Person.Person` | **C52** `choiceExists` |
| F2 | — | — | — | — | — | — |
| F3 | — | — | — | — | — | — |
| F4 | `Logos.Love.T13_someoneLovable` | [Love.lean#L50](formal/Logos/Love.lean#L50) | `{}` | — | `Agency.Subject`, `Love.Lovable`, `Person.Person`, **C40** `T12_twoPersons` | — |
| F5 | `Logos.Love.T14_canonicalRigid` | [Love.lean#L114](formal/Logos/Love.lean#L114) | `{}` | — | `Agency.A`, `Agency.Agent`, `Agency.Initiates`, `Agency.Means`, `Agency.Rational`, `Agency.State`, `Agency.Subject`, `Love.Loves`, `Person.Intentional`, `Person.Person`, `Plurality.EntityOf`, `Semantics.World`, **Q7.2** `ExistsAt` | — |
| F6 | — | — | — | — | — | — |
| Q7.2 | `Logos.Truthmaker.ExistsAt` | [Truthmaker.lean#L57](formal/Logos/Truthmaker.lean#L57) | `{}` | — | `Agency.A`, `Agency.Subject`, `Semantics.World` | **FAITH-2** `AxPersonStability`, **C76** `T14_canonicalRigid`, **C44** `T14_world`, `Modal.AxGlobalGround`, `Modal.NecessaryEntity`, **C18** `T7_necessaryReality`, `Plurality.NecessarySubject`, **C15** `groundPrinciple_atom`, **C60** `noGround_selfRefutes` |
| C35 | `Logos.Core.negatedAbsolutes` | [Core.lean#L129](formal/Logos/Core.lean#L129) | `{}` | {} (E0) | `Core.N_F`, `Core.N_T`, **C6** `notEverythingTrue`, **C2** `notNothingTrue` | — |
| C36 | `Logos.Core.rightWrongDistinction` | [Core.lean#L145](formal/Logos/Core.lean#L145) | `{}` | {} (E0) | `Core.N_F`, `Core.N_T`, **C6** `notEverythingTrue`, **C2** `notNothingTrue` | **FAITH-1** `necDistinction` |
| C37 | `Logos.Semantics.bothNecessarilyTrueAndFalse` | [Semantics.lean#L102](formal/Logos/Semantics.lean#L102) | `{CL}` | CL | `Semantics.Form`, `Semantics.NecessarilyFalse`, `Semantics.NecessarilyTrue`, **C13** `lawExcludedMiddle`, **C14** `nonContradiction` | — |
| C38 | `Logos.Necessity.necDistinction` | [Necessity.lean#L118](formal/Logos/Necessity.lean#L118) | `{}` | {} (E0; C1: identity-model alias; world content = C37) | `Core.N_F`, `Core.N_T`, **C36** `rightWrongDistinction`, `Necessity.Necessity`, `Semantics.World` | `Necessity.necDistinction_content` |
| C39 | `Logos.Choice.T11_choiceField` | [Choice.lean#L140](formal/Logos/Choice.lean#L140) | `{}` | {} (choice field exhibited with the act) | `Agency.Subject`, `Alternatives.Incompatible`, **C26** `T9_incompatibleAlternatives`, `Core.IsFalse`, `Core.T`, `Person.Person`, **C24** `T5_personExists` | — |
| C40 | `Logos.Plurality.T12_twoPersons` | [Plurality.lean#L54](formal/Logos/Plurality.lean#L54) | `{}` | {} (definitional subject, 2026-09-17: canonical pair of Person.twoPersonsFromSubject — origin + addressee; no right/wrong premise, no bridge) | `Agency.Subject`, `Person.Person`, **C73** `twoPersonsFromSubject` | **C41** `T13_someoneLovable`, **C47** `T12_directedPair`, `Plurality.notAlone` |
| C41 | `Logos.Love.T13_someoneLovable` | [Love.lean#L50](formal/Logos/Love.lean#L50) | `{}` | {} (via C40) | `Agency.Subject`, `Love.Lovable`, `Person.Person`, **C40** `T12_twoPersons` | — |
| C48 | `Logos.Plurality.cogito_from_T12` | [Plurality.lean#L72](formal/Logos/Plurality.lean#L72) | `{}` | {} (cogito as corollary of the exhibited Cogito; plurality also forces the datum, the datum is not *grounded* on plurality) | `Agency.A`, **C68** `Cogito`, `Agency.Subject` | **C30** `correctness_distinct`, `Order.fallible_false`, **C55** `judge_commits` |
| C49 | `Logos.Choice.meaning_needs_subject` | [Choice.lean#L100](formal/Logos/Choice.lean#L100) | `{}` | {} (analytic; vocab-only — no substantive axiom; see VOCAB.md) | `Agency.Means`, `Agency.Subject` | — |
| C50 | `Logos.Choice.incompatible_self_negation` | [Choice.lean#L76](formal/Logos/Choice.lean#L76) | `{}` | **{}** (pure logic — the field around any meaning-act) | `Alternatives.Incompatible` | **C51** `person_chooses`, **C55** `judge_commits` |
| C51 | `Logos.Choice.person_chooses` | [Choice.lean#L151](formal/Logos/Choice.lean#L151) | `{}` | {} (vocab-only — no substantive axiom; see VOCAB.md) | `Agency.A`, `Agency.Agent`, `Agency.Means`, `Agency.Rational`, `Agency.Subject`, `Alternatives.Incompatible`, `Choice.Chooses`, **C50** `incompatible_self_negation`, `Person.Intentional`, `Person.Person` | **C52** `choiceExists` |
| C52 | `Logos.Choice.choiceExists` | [Choice.lean#L160](formal/Logos/Choice.lean#L160) | `{}` | {} (choice is real, from T5 — now Plurality.T5_personExists) | `Agency.Subject`, `Choice.Chooses`, **C51** `person_chooses`, `Person.Person`, **C24** `T5_personExists` | **C54** `JUDGE_COMMITTED`, **C53** `noChoice_selfRefutes`, **C57** `noSubject_selfRefutes` |
| C53 | `Logos.Choice.noChoice_selfRefutes` | [Choice.lean#L170](formal/Logos/Choice.lean#L170) | `{}` | {} — denying choice is itself an act = a choice | `Agency.Subject`, `Choice.Chooses`, **C52** `choiceExists` | — |
| C54 | `Logos.Choice.JUDGE_COMMITTED` | [Choice.lean#L179](formal/Logos/Choice.lean#L179) | `{}` | {} (premise unused: choice already holds via C52) | `Agency.Subject`, `Choice.Chooses`, **C52** `choiceExists`, `Core.N_F`, `Core.N_T` | **C61** `rightWrong_implies_someone_means` |
| C55 | `Logos.Order.judge_commits` | [Order.lean#L123](formal/Logos/Order.lean#L123) | `{CL}` | CL (defs act-relative §8) | `Agency.A`, `Agency.Subject`, `Alternatives.Incompatible`, `Choice.Chooses`, **C50** `incompatible_self_negation`, `Core.IsFalse`, `Core.T`, `Order.Correct`, `Order.Incorrect`, **C48** `cogito_from_T12` | `Order.rightWrongDistinction_implies_meaning` |
| C56 | `Logos.Value.alone_no_other_help_harm` | [Value.lean#L88](formal/Logos/Value.lean#L88) | `{}` | {} (M1: Affects is now the A3 definition s ≠ t, so the P6 lemma loses its axiom — measured; see VOCAB.md) | `Agency.Subject`, `Value.Alone`, `Value.Harms`, `Value.Helps` | — |
| C57 | `Logos.Choice.noSubject_selfRefutes` | [Choice.lean#L211](formal/Logos/Choice.lean#L211) | `{}` | {} — formal record of §26 "não existe sujeito do ato presente"; the act-datum is the exhibited theorem Cogito, never a consequence of the plurality bridge | `Agency.Subject`, `Choice.Chooses`, **C52** `choiceExists` | — |
| C42 | `Logos.Love.T14_eternalRelation` | [Love.lean#L98](formal/Logos/Love.lean#L98) | `{}` | {} (M1: Affects := s ≠ t def + AxPersonsAffect theorem vanish; esse-est-agere: AxPersonStability is a theorem and ExistsAt a def; plurality-discharge: AxTwoSubjects retired — canonical pair of Person.twoPersonsFromSubject) | `Agency.Subject`, **FAITH-2** `AxPersonStability`, `Love.Loves`, `Person.Person`, `Plurality.NecessarySubject`, **C47** `T12_directedPair`, `Value.Affects` | **C43** `T14_content`, **C45** `T14_square`, **C44** `T14_world` |
| C43 | `Logos.Love.T14_content` | [Love.lean#L155](formal/Logos/Love.lean#L155) | `{}` | as C42 | `Agency.Subject`, `Love.Loves`, **C42** `T14_eternalRelation`, `Person.Person`, `Plurality.NecessarySubject` | — |
| C44 | `Logos.Love.T14_world` | [Love.lean#L133](formal/Logos/Love.lean#L133) | `{}` | as C42 (world-anchored honest □) | `Agency.Subject`, `Love.Loves`, **C42** `T14_eternalRelation`, `Necessity.NecessityPH`, `Person.Person`, `Plurality.EntityOf`, `Plurality.NecessarySubject`, `Semantics.World`, **Q7.2** `ExistsAt` | — |
| C45 | `Logos.Love.T14_square` | [Love.lean#L145](formal/Logos/Love.lean#L145) | `{}` | as C42 (image of the old statement shape) | `Agency.Subject`, `Love.Loves`, **C42** `T14_eternalRelation`, `Necessity.Necessity`, `Person.Person`, `Plurality.NecessarySubject`, `Semantics.World` | — |
| C46 | `Logos.Value.valueInterpersonal_of_split` | [Value.lean#L156](formal/Logos/Value.lean#L156) | `{}` | {} (recovery theorem: exact old statement; M1: Affects/AxPersonsAffect gone; derived outright from Person.twoPersonsFromSubject) | `Agency.Subject`, `Core.N_F`, `Core.N_T`, `Person.Person`, **C73** `twoPersonsFromSubject`, `Value.Affects`, `Value.AxPersonsAffect` | — |
| C47 | `Logos.Plurality.T12_directedPair` | [Plurality.lean#L109](formal/Logos/Plurality.lean#L109) | `{}` | {} (chain node — M1: distinctness is already the forward direction under A3, so the pair wears its own inequality; T14 built on this node) | `Agency.Subject`, `Person.Person`, **C40** `T12_twoPersons`, `Value.Affects` | **C42** `T14_eternalRelation` |
| C61 | `Logos.Choice.rightWrong_implies_someone_means` | [Choice.lean#L194](formal/Logos/Choice.lean#L194) | `{}` | {} (JUDGE_COMMITTED C54 ∘ rightWrongDistinction C36; the analytic half "significado → sujeito" is C49) | `Agency.A`, `Agency.Means`, `Agency.Subject`, `Alternatives.Incompatible`, `Choice.Chooses`, **C54** `JUDGE_COMMITTED`, `Core.N_F`, `Core.N_T` | — |
| C62 | `Logos.Order.rightWrong_implies_meaning` | [Order.lean#L46](formal/Logos/Order.lean#L46) | `{}` | {} (pure bridges; full conditional CL; **sem axioma substantivo**; o modelo vazio já não satisfaz o antecedente; ver VOCAB.md/BRIDGE.md) | `Agency.A`, `Agency.Means`, `Agency.Subject`, `Choice.Meaning_I`, `Core.IsFalse`, `Core.T`, `Order.Correct`, `Order.Incorrect` | `Order.rightDistinctWrong_implies_meaning`, `Order.rightWrongDistinction_implies_meaning` |
| C69 | `Logos.Choice.freeWillOrigin` | [Choice.lean#L249](formal/Logos/Choice.lean#L249) | `{}` | {} (constructive — the origin means every content; instantiation at someWorld, deliberately not canChoose_unfold) | `Choice.CanChoose`, `Choice.FreeWill` | **C72** `judgeIsFree`, **C71** `originFreedomSelfRefutes` |
| C70 | `Logos.Choice.noFreeWillPosited` | [Choice.lean#L273](formal/Logos/Choice.lean#L273) | `{CL}` | CL (double negation on the CanChoose → q = p extraction) — no paradox: such subjects are never the judge right/wrong commits (that witness is the free origin) | `Choice.CanChoose`, `Choice.FreeWill` | — |
| C71 | `Logos.Choice.originFreedomSelfRefutes` | [Choice.lean#L296](formal/Logos/Choice.lean#L296) | `{}` | {} — the freedom paradox dissolves: the determinist alternative cannot be asserted performatively | `Choice.FreeWill`, **F7** `freeWillOrigin` | — |
| C72 | `Logos.Choice.judgeIsFree` | [Choice.lean#L306](formal/Logos/Choice.lean#L306) | `{}` | {} (judge = origin via T5_personExists; choice-in-the-freedom-sense exists for the act's subject) | `Agency.Agent`, `Agency.Means`, `Agency.Rational`, `Agency.Subject`, `Choice.FreeWill`, **F7** `freeWillOrigin`, `Person.Intentional`, `Person.Person` | — |
| C73 | `Logos.Person.twoPersonsFromSubject` | [Person.lean#L90](formal/Logos/Person.lean#L90) | `{}` | {} (plurality-discharge, 2026-09-17: no plurality axiom — AxTwoSubjects retired; Person (Sum.inr True) via Means (Sum.inr True) True; distinctness by constructors) | `Agency.Agent`, `Agency.Initiates`, `Agency.Means`, `Agency.Rational`, `Agency.State`, `Agency.Subject`, `Person.Intentional`, `Person.Person` | **C40** `T12_twoPersons`, **C46** `valueInterpersonal_of_split` |
| C74 | `Logos.Value.aloneExcluded` | [Value.lean#L135](formal/Logos/Value.lean#L135) | `{}` | {} (kills the M2 lone-subject countermodel; the named missing lemma that justified AxTwoSubjects no longer exists) | `Agency.Subject`, `Person.Person`, `Value.Alone`, `Value.neverAlone` | — |
| C75 | `Logos.Person.everyContentIsAPerson` | [Person.lean#L105](formal/Logos/Person.lean#L105) | `{}` | {} (honest limit: distinctness of such persons is kernel-visible only for incompatible contents — proposition equality is propext-collapsed) | `Agency.Agent`, `Agency.Initiates`, `Agency.Means`, `Agency.Rational`, `Agency.State`, `Person.Intentional`, `Person.Person` | — |
| C76 | `Logos.Love.T14_canonicalRigid` | [Love.lean#L114](formal/Logos/Love.lean#L114) | `{}` | {} (stronger than C42: "Amar é … necessário (de alguma forma)" made literal; no stability bridge needed — esse est agere) | `Agency.A`, `Agency.Agent`, `Agency.Initiates`, `Agency.Means`, `Agency.Rational`, `Agency.State`, `Agency.Subject`, `Love.Loves`, `Person.Intentional`, `Person.Person`, `Plurality.EntityOf`, `Semantics.World`, **Q7.2** `ExistsAt` | — |
| C77 | `Logos.Love.necessaryPersonExists` | [Love.lean#L77](formal/Logos/Love.lean#L77) | `{}` | {} (witnessed by the silent origin Sum.inl (), canonical pair relatum) | `Agency.Subject`, **FAITH-2** `AxPersonStability`, `Person.Person`, `Plurality.NecessarySubject`, **C24** `T5_personExists` | — |
| C63 | `Logos.Initiation.branches_not_transfer` | [Initiation.lean#L32](formal/Logos/Initiation.lean#L32) | `{}` | **{}** (lógica pura — sem axioma, sem vocabulário) | `Initiation.Branches`, `Initiation.IsTransfer` | **C64** `originates_not_transfer` |
| C64 | `Logos.Initiation.originates_not_transfer` | [Initiation.lean#L47](formal/Logos/Initiation.lean#L47) | `{}` | {} | `Agency.State`, `Agency.Subject`, `Initiation.Branches`, `Initiation.IsTransfer`, `Initiation.Moves`, **C63** `branches_not_transfer` | — |
| C65 | `Logos.Initiation.person_iff_originates` | [Initiation.lean#L52](formal/Logos/Initiation.lean#L52) | `{}` | {} | `Agency.Agent`, `Agency.Initiates`, `Agency.Means`, `Agency.Rational`, `Agency.State`, `Agency.Subject`, `Initiation.Originates`, `Person.Intentional`, `Person.Person` | — |
| C66 | `Logos.Initiation.Cogito_Init` | [Initiation.lean#L63](formal/Logos/Initiation.lean#L63) | `{}` | {} (relabel of the exhibited Cogito) | `Agency.A`, **C68** `Cogito`, `Agency.Initiates`, `Agency.State`, `Agency.Subject`, `Initiation.Originates` | **C67** `noInitiation_selfRefutes` |
| C67 | `Logos.Initiation.noInitiation_selfRefutes` | [Initiation.lean#L70](formal/Logos/Initiation.lean#L70) | `{}` | {} (mirror of C58) | `Agency.Subject`, **C66** `Cogito_Init`, `Initiation.Originates` | — |
| FAITH-1 | `Logos.Necessity.necDistinction` | [Necessity.lean#L118](formal/Logos/Necessity.lean#L118) | `{}` | — | `Core.N_F`, `Core.N_T`, **C36** `rightWrongDistinction`, `Necessity.Necessity`, `Semantics.World` | `Necessity.necDistinction_content` |
| FAITH-2 | `Logos.Love.AxPersonStability` | [Love.lean#L65](formal/Logos/Love.lean#L65) | `{}` | — | `Agency.A`, `Agency.Agent`, `Agency.Means`, `Agency.Rational`, `Agency.Subject`, `Person.Intentional`, `Person.Person`, `Plurality.EntityOf`, `Plurality.NecessarySubject`, `Semantics.World`, **Q7.2** `ExistsAt` | **C42** `T14_eternalRelation`, `Love.canonicalNecessaryPerson`, **C77** `necessaryPersonExists` |
| F7 | `Logos.Choice.freeWillOrigin` | [Choice.lean#L249](formal/Logos/Choice.lean#L249) | `{}` | — | `Choice.CanChoose`, `Choice.FreeWill` | **C72** `judgeIsFree`, **C71** `originFreedomSelfRefutes` |
| F8 | — | — | — | — | — | — |
| F9 | — | — | — | — | — | — |

</details>

---
## Índice de declarações do kernel

<details>
<summary>Todos os teoremas/defs user-authored, por módulo (linha e axiomas de kernel) →</summary>

### `Logos.Agency`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `A` | def | [L120](formal/Logos/Agency.lean#L120) | `def A (s : Subject) (p : Prop) : Prop` | {}  |
| `Agent` | def | [L83](formal/Logos/Agency.lean#L83) | `def Agent (_s : Subject) : Prop` | {}  |
| `Cogito` | theorem | [L129](formal/Logos/Agency.lean#L129) | `theorem Cogito : ∃ s : Subject, ∃ p : Prop, A s p` | {} → C68 |
| `Content` | def | [L77](formal/Logos/Agency.lean#L77) | `def Content (_p : Prop) : Prop` | {}  |
| `Exists` | def | [L72](formal/Logos/Agency.lean#L72) | `def Exists (_s : Subject) : Prop` | {}  |
| `Initiates` | def | [L105](formal/Logos/Agency.lean#L105) | `def Initiates (s : Subject) (_w w' : State) (p : Prop) : Prop` | {}  |
| `Means` | def | [L114](formal/Logos/Agency.lean#L114) | `def Means (s : Subject) (p : Prop) : Prop` | {}  |
| `Rational` | def | [L89](formal/Logos/Agency.lean#L89) | `def Rational (_s : Subject) : Prop` | {}  |
| `State` | def | [L97](formal/Logos/Agency.lean#L97) | `def State` | {}  |
| `Subject` | def | [L66](formal/Logos/Agency.lean#L66) | `def Subject` | {}  |
| `T2_contentExists` | theorem | [L175](formal/Logos/Agency.lean#L175) | `theorem T2_contentExists : ∃ p : Prop, Content p` | {} → C22 |
| `act_implies_agent` | theorem | [L154](formal/Logos/Agency.lean#L154) | `theorem act_implies_agent : ∀ {s : Subject} {p : Prop}, A s p → Agent s` | {}  |
| `act_implies_content` | theorem | [L149](formal/Logos/Agency.lean#L149) | `theorem act_implies_content : ∀ {s : Subject} {p : Prop}, A s p → Content p` | {}  |
| `act_implies_exists` | theorem | [L143](formal/Logos/Agency.lean#L143) | `theorem act_implies_exists : ∀ {s : Subject} {p : Prop}, A s p → Exists s` | {}  |
| `act_implies_means` | theorem | [L166](formal/Logos/Agency.lean#L166) | `theorem act_implies_means : ∀ {s : Subject} {p : Prop}, A s p → Means s p` | {}  |
| `act_implies_rational` | theorem | [L160](formal/Logos/Agency.lean#L160) | `theorem act_implies_rational : ∀ {s : Subject} {p : Prop}, A s p → Rational s` | {}  |
| `noCogito_selfRefutes` | theorem | [L137](formal/Logos/Agency.lean#L137) | `theorem noCogito_selfRefutes : (¬ ∃ s : Subject, ∃ p : Prop, A s p) → False` | {} → C58 |

### `Logos.Alternatives`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `Incompatible` | def | [L17](formal/Logos/Alternatives.lean#L17) | `def Incompatible (p q : Prop) : Prop` | {}  |
| `T9_incompatibleAlternatives` | theorem | [L24](formal/Logos/Alternatives.lean#L24) | `theorem T9_incompatibleAlternatives : ∃ p q : Prop, Incompatible p q ∧ T p ∧ IsF` | {} → C26 |
| `incompatible_with_negation` | theorem | [L35](formal/Logos/Alternatives.lean#L35) | `theorem incompatible_with_negation {p : Prop} (hp : T p) : Incompatible p (¬ p) ` | {} → C27 |

### `Logos.Choice`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `CanChoose` | def | [L105](formal/Logos/Choice.lean#L105) | `def CanChoose (s : Subject) (p : Prop) : Prop` | {}  |
| `Chooses` | def | [L69](formal/Logos/Choice.lean#L69) | `def Chooses (s : Subject) (p : Prop) (q : Prop) : Prop` | {}  |
| `FreeWill` | def | [L131](formal/Logos/Choice.lean#L131) | `def FreeWill (s : Subject) (p : Prop) : Prop` | {}  |
| `JUDGE_COMMITTED` | theorem | [L179](formal/Logos/Choice.lean#L179) | `theorem JUDGE_COMMITTED : (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) → ∃ s : Subject,` | {} → C54 |
| `Meaning_I` | def | [L83](formal/Logos/Choice.lean#L83) | `def Meaning_I (p : Prop) : Prop` | {}  |
| `T11_choiceField` | theorem | [L140](formal/Logos/Choice.lean#L140) | `theorem T11_choiceField : ∃ s : Subject, Person s ∧ ∃ p q : Prop, Incompatible p` | {} → C39 |
| `canChoose_unfold` | theorem | [L111](formal/Logos/Choice.lean#L111) | `theorem canChoose_unfold {s : Subject} {p : Prop} : CanChoose s p ↔ ∃ q : Prop, ` | {CL}  |
| `choiceExists` | theorem | [L160](formal/Logos/Choice.lean#L160) | `theorem choiceExists : ∃ s : Subject, ∃ p q : Prop, Chooses s p q` | {} → C52 |
| `freeWillOrigin` | theorem | [L249](formal/Logos/Choice.lean#L249) | `theorem freeWillOrigin (p : Prop) : FreeWill (Sum.inl ()) p` | {} → F7 |
| `incompatible_self_negation` | theorem | [L76](formal/Logos/Choice.lean#L76) | `theorem incompatible_self_negation (p : Prop) : Incompatible p (¬ p)` | {} → C50 |
| `judgeIsFree` | theorem | [L306](formal/Logos/Choice.lean#L306) | `theorem judgeIsFree : ∃ s : Subject, Person s ∧ ∃ p : Prop, FreeWill s p` | {} → C72 |
| `meaning_I_needs_subject` | theorem | [L91](formal/Logos/Choice.lean#L91) | `theorem meaning_I_needs_subject {p : Prop} (h : Meaning_I p) : ∃ s : Subject, Me` | {}  |
| `meaning_needs_subject` | theorem | [L100](formal/Logos/Choice.lean#L100) | `theorem meaning_needs_subject {s : Subject} {p : Prop} (hm : Means s p) : ∃ t : ` | {} → C49 |
| `noChoice_selfRefutes` | theorem | [L170](formal/Logos/Choice.lean#L170) | `theorem noChoice_selfRefutes : (¬ ∃ s : Subject, ∃ p q : Prop, Chooses s p q) → ` | {} → C53 |
| `noFreeWillPosited` | theorem | [L273](formal/Logos/Choice.lean#L273) | `theorem noFreeWillPosited (q p : Prop) : ¬ FreeWill (Sum.inr q) p` | {CL} → C70 |
| `noSubject_selfRefutes` | theorem | [L211](formal/Logos/Choice.lean#L211) | `theorem noSubject_selfRefutes : (¬ ∃ _s : Subject, True) → False` | {} → C57 |
| `originFreedomSelfRefutes` | theorem | [L296](formal/Logos/Choice.lean#L296) | `theorem originFreedomSelfRefutes (p : Prop) : (¬ FreeWill (Sum.inl ()) p) → Fals` | {} → C71 |
| `person_chooses` | theorem | [L151](formal/Logos/Choice.lean#L151) | `theorem person_chooses {s : Subject} (hs : Person s) : ∃ p q : Prop, Chooses s p` | {} → C51 |
| `rightWrong_implies_someone_means` | theorem | [L194](formal/Logos/Choice.lean#L194) | `theorem rightWrong_implies_someone_means : (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F)` | {} → C61 |

### `Logos.ClaimMeanings`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `C19` | def | [L29](formal/Logos/ClaimMeanings.lean#L29) | `def C19 : String` | —  |
| `C59` | def | [L11](formal/Logos/ClaimMeanings.lean#L11) | `def C59 : String` | —  |
| `F2` | def | [L13](formal/Logos/ClaimMeanings.lean#L13) | `def F2 : String` | —  |
| `F3` | def | [L15](formal/Logos/ClaimMeanings.lean#L15) | `def F3 : String` | —  |
| `F4` | def | [L17](formal/Logos/ClaimMeanings.lean#L17) | `def F4 : String` | —  |
| `F5` | def | [L19](formal/Logos/ClaimMeanings.lean#L19) | `def F5 : String` | —  |
| `F6` | def | [L21](formal/Logos/ClaimMeanings.lean#L21) | `def F6 : String` | —  |
| `F8` | def | [L23](formal/Logos/ClaimMeanings.lean#L23) | `def F8 : String` | —  |
| `F9` | def | [L25](formal/Logos/ClaimMeanings.lean#L25) | `def F9 : String` | —  |
| `Q7_2` | def | [L27](formal/Logos/ClaimMeanings.lean#L27) | `def Q7_2 : String` | —  |

### `Logos.Core`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
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

### `Logos.GroundPerson`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `AxGroundBearing` | theorem | [L82](formal/Logos/GroundPerson.lean#L82) | `theorem AxGroundBearing {e : Entity} {f : Prop} : GroundProp e f → Realizes e f` | {GroundProp}  |
| `AxPersonalGround` | axiom | [L101](formal/Logos/GroundPerson.lean#L101) | `axiom AxPersonalGround : ∀ {f : Prop}, IsPresentPersonalFeature f → ∃ e : Entity` | {AxPersonalGround, GroundProp}  |
| `GroundPrincipleProp` | axiom | [L77](formal/Logos/GroundPerson.lean#L77) | `axiom GroundPrincipleProp : ∀ {f : Prop}, T f → ∃ e : Entity, GroundProp e f` | {GroundPrincipleProp, GroundProp}  |
| `GroundProp` | axiom | [L62](formal/Logos/GroundPerson.lean#L62) | `axiom GroundProp : Entity → Prop → Prop` | {GroundProp}  |
| `IsPresentPersonalFeature` | def | [L87](formal/Logos/GroundPerson.lean#L87) | `def IsPresentPersonalFeature (f : Prop) : Prop` | {}  |
| `Personal` | def | [L91](formal/Logos/GroundPerson.lean#L91) | `def Personal (e : Entity) : Prop` | {GroundProp}  |
| `Realizes` | def | [L68](formal/Logos/GroundPerson.lean#L68) | `def Realizes (e : Entity) (f : Prop) : Prop` | {GroundProp}  |
| `T8_personalGround` | theorem | [L108](formal/Logos/GroundPerson.lean#L108) | `theorem T8_personalGround {f : Prop} (hf : IsPresentPersonalFeature f) : ∃ e : E` | {AxPersonalGround, GroundProp} → C32 |
| `necessary_truth_has_necessary_grounder` | theorem | [L126](formal/Logos/GroundPerson.lean#L126) | `theorem necessary_truth_has_necessary_grounder (n : Nat) (hτ : Logos.Truthmaker.` | {Ground} → C34 |
| `present_feature_is_grounded` | theorem | [L118](formal/Logos/GroundPerson.lean#L118) | `theorem present_feature_is_grounded {f : Prop} (ht : T f) (_hf : IsPresentPerson` | {GroundPrincipleProp, GroundProp} → C33 |

### `Logos.Initiation`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `Branches` | def | [L28](formal/Logos/Initiation.lean#L28) | `def Branches {α β : Type} (R : α → β → Prop) : Prop` | {}  |
| `Cogito_Init` | theorem | [L63](formal/Logos/Initiation.lean#L63) | `theorem Cogito_Init : ∃ s : Subject, Originates s` | {} → C66 |
| `IsTransfer` | def | [L24](formal/Logos/Initiation.lean#L24) | `def IsTransfer {α β : Type} (R : α → β → Prop) : Prop` | {}  |
| `Moves` | def | [L41](formal/Logos/Initiation.lean#L41) | `def Moves (s : Subject) (w w' : State) : Prop` | {}  |
| `Originates` | def | [L44](formal/Logos/Initiation.lean#L44) | `def Originates (s : Subject) : Prop` | {}  |
| `branches_not_transfer` | theorem | [L32](formal/Logos/Initiation.lean#L32) | `theorem branches_not_transfer {α β : Type} {R : α → β → Prop} (h : Branches R) :` | {} → C63 |
| `noInitiation_selfRefutes` | theorem | [L70](formal/Logos/Initiation.lean#L70) | `theorem noInitiation_selfRefutes : (¬ ∃ s : Subject, Originates s) → False` | {} → C67 |
| `originates_not_transfer` | theorem | [L47](formal/Logos/Initiation.lean#L47) | `theorem originates_not_transfer {s : Subject} (h : Branches (Moves s)) : ¬ IsTra` | {} → C64 |
| `person_iff_originates` | theorem | [L52](formal/Logos/Initiation.lean#L52) | `theorem person_iff_originates (s : Subject) : Person s ↔ Originates s` | {} → C65 |

### `Logos.Love`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `AxPersonStability` | theorem | [L65](formal/Logos/Love.lean#L65) | `theorem AxPersonStability : ∀ s : Subject, Person s → NecessarySubject s` | {} → FAITH-2 |
| `Lovable` | def | [L44](formal/Logos/Love.lean#L44) | `def Lovable (t : Subject) : Prop` | {}  |
| `Loves` | def | [L40](formal/Logos/Love.lean#L40) | `def Loves (s t : Subject) : Prop` | {}  |
| `T13_someoneLovable` | theorem | [L50](formal/Logos/Love.lean#L50) | `theorem T13_someoneLovable : ∃ s t : Subject, Person s ∧ Person t ∧ s ≠ t ∧ Lova` | {} → C41 |
| `T14_canonicalRigid` | theorem | [L114](formal/Logos/Love.lean#L114) | `theorem T14_canonicalRigid : Person (Sum.inl ()) ∧ Person (Sum.inr True) ∧ Loves` | {} → C76 |
| `T14_content` | theorem | [L155](formal/Logos/Love.lean#L155) | `theorem T14_content : ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ Loves` | {} → C43 |
| `T14_eternalRelation` | theorem | [L98](formal/Logos/Love.lean#L98) | `theorem T14_eternalRelation : ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂` | {} → C42 |
| `T14_square` | theorem | [L145](formal/Logos/Love.lean#L145) | `theorem T14_square : □(∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ Love` | {} → C45 |
| `T14_world` | theorem | [L133](formal/Logos/Love.lean#L133) | `theorem T14_world : ∀ w, ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ Lo` | {} → C44 |
| `canonicalNecessaryPerson` | theorem | [L84](formal/Logos/Love.lean#L84) | `theorem canonicalNecessaryPerson : Person (Sum.inl ()) ∧ NecessarySubject (Sum.i` | {}  |
| `necessaryPersonExists` | theorem | [L77](formal/Logos/Love.lean#L77) | `theorem necessaryPersonExists : ∃ s : Subject, Person s ∧ NecessarySubject s` | {} → C77 |

### `Logos.Modal`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `AxGlobalGround` | theorem | [L56](formal/Logos/Modal.lean#L56) | `theorem AxGlobalGround (n : Nat) (hnec : □atom n) : ∃ e : Entity, ∀ w : World, E` | {Ground}  |
| `Contingent` | def | [L40](formal/Logos/Modal.lean#L40) | `def Contingent (e : Entity) : Prop` | {}  |
| `NecessaryEntity` | def | [L37](formal/Logos/Modal.lean#L37) | `def NecessaryEntity (e : Entity) : Prop` | {}  |
| `T7_necessaryReality` | theorem | [L69](formal/Logos/Modal.lean#L69) | `theorem T7_necessaryReality (n : Nat) (hnec : □atom n) : ∃ e : Entity, Necessary` | {Ground} → C18 |
| `actualWorld` | def | [L34](formal/Logos/Modal.lean#L34) | `def actualWorld : World` | {}  |
| `noNecessaryTruthIfAllContingent` | theorem | [L78](formal/Logos/Modal.lean#L78) | `theorem noNecessaryTruthIfAllContingent : (∀ e : Entity, Contingent e) → ∀ n : N` | {Ground} → C20 |

### `Logos.Necessity`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `Dia` | def | [L69](formal/Logos/Necessity.lean#L69) | `def ◇(p : Prop) : Prop` | {}  |
| `Necessity` | def | [L51](formal/Logos/Necessity.lean#L51) | `def □(p : Prop) : Prop` | {}  |
| `NecessityPH` | def | [L94](formal/Logos/Necessity.lean#L94) | `def □ₚ(P : WProp) : Prop` | {}  |
| `WProp` | abbrev | [L86](formal/Logos/Necessity.lean#L86) | `abbrev WProp : Type` | {}  |
| `dia_def` | theorem | [L72](formal/Logos/Necessity.lean#L72) | `theorem dia_def {p : Prop} : ◇ p ↔ ¬ □(¬ p)` | {}  |
| `nec4` | theorem | [L64](formal/Logos/Necessity.lean#L64) | `theorem nec4 : ∀ {p : Prop}, □ p → □(□ p)` | {}  |
| `nec4PH` | theorem | [L108](formal/Logos/Necessity.lean#L108) | `theorem nec4PH {P : WProp} : □ₚ P → □ₚ(fun _ => □ₚ P)` | {}  |
| `necDistinction` | theorem | [L118](formal/Logos/Necessity.lean#L118) | `theorem necDistinction : □(¬ N_T ∧ ¬ N_F)` | {} → FAITH-1 |
| `necDistinction_content` | theorem | [L122](formal/Logos/Necessity.lean#L122) | `theorem necDistinction_content : ¬ N_T ∧ ¬ N_F` | {}  |
| `necK` | theorem | [L54](formal/Logos/Necessity.lean#L54) | `theorem necK : ∀ {p q : Prop}, □(p → q) → □ p → □ q` | {}  |
| `necKPH` | theorem | [L97](formal/Logos/Necessity.lean#L97) | `theorem necKPH {P Q : WProp} : □ₚ(fun w => P w → Q w) → □ₚ P → □ₚ Q` | {}  |
| `necMP` | theorem | [L78](formal/Logos/Necessity.lean#L78) | `theorem necMP {p q : Prop} (hpq : □(p → q)) (hp : □ p) : □ q` | {}  |
| `necT` | theorem | [L59](formal/Logos/Necessity.lean#L59) | `theorem necT : ∀ {p : Prop}, □ p → p` | {}  |
| `necTPH` | theorem | [L102](formal/Logos/Necessity.lean#L102) | `theorem necTPH {P : WProp} : □ₚ P → P someWorld` | {}  |
| `nec_apply` | theorem | [L75](formal/Logos/Necessity.lean#L75) | `theorem nec_apply {p : Prop} (hp : □ p) : p` | {}  |
| `someWorld` | def | [L45](formal/Logos/Necessity.lean#L45) | `def someWorld : World` | {}  |

### `Logos.Order`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `Correct` | def | [L29](formal/Logos/Order.lean#L29) | `def Correct (s : Subject) (p : Prop) : Prop` | {}  |
| `Fallible` | def | [L74](formal/Logos/Order.lean#L74) | `def Fallible (_s : Subject) (p : Prop) : Prop` | {}  |
| `Incorrect` | def | [L34](formal/Logos/Order.lean#L34) | `def Incorrect (s : Subject) (p : Prop) : Prop` | {}  |
| `T6_fallibility` | theorem | [L90](formal/Logos/Order.lean#L90) | `theorem T6_fallibility : ¬ (∀ s : Subject, ∀ p : Prop, Fallible s p → T p)` | {} → C28 |
| `T6_truthTranscendsWill` | theorem | [L99](formal/Logos/Order.lean#L99) | `theorem T6_truthTranscendsWill : ¬ (∀ s : Subject, ∀ p : Prop, Fallible s p ↔ T ` | {} → C29 |
| `consequence_preserves_truth` | theorem | [L146](formal/Logos/Order.lean#L146) | `theorem consequence_preserves_truth {p₁ p₂ q : Prop} (himp : p₁ → p₂ → q) (h1 : ` | {} → C31 |
| `correctness_distinct` | theorem | [L107](formal/Logos/Order.lean#L107) | `theorem correctness_distinct : ¬ (∀ s : Subject, ∀ p : Prop, Correct s p ↔ Incor` | {CL} → C30 |
| `fallible_false` | theorem | [L82](formal/Logos/Order.lean#L82) | `theorem fallible_false : ∃ s : Subject, ∃ p : Prop, Fallible s p ∧ IsFalse p` | {}  |
| `judge_commits` | theorem | [L123](formal/Logos/Order.lean#L123) | `theorem judge_commits : ∃ s : Subject, ∃ p q : Prop, A s p ∧ (Correct s p ∨ Inco` | {CL} → C55 |
| `rightDistinctWrong_implies_meaning` | theorem | [L62](formal/Logos/Order.lean#L62) | `theorem rightDistinctWrong_implies_meaning (h : (∃ s : Subject, ∃ p : Prop, Corr` | {}  |
| `rightWrongDistinction_implies_meaning` | theorem | [L134](formal/Logos/Order.lean#L134) | `theorem rightWrongDistinction_implies_meaning (_h : ¬ Logos.Core.N_T ∧ ¬ Logos.C` | {CL}  |
| `rightWrong_implies_meaning` | theorem | [L46](formal/Logos/Order.lean#L46) | `theorem rightWrong_implies_meaning (h : (∃ s : Subject, ∃ p : Prop, Correct s p)` | {} → C62 |

### `Logos.Person`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `CarriesLogicalFeature` | def | [L50](formal/Logos/Person.lean#L50) | `def CarriesLogicalFeature (a : Prop) : Prop` | {}  |
| `CarriesPersonalFeature` | def | [L46](formal/Logos/Person.lean#L46) | `def CarriesPersonalFeature (a : Prop) : Prop` | {}  |
| `HasFeature` | def | [L43](formal/Logos/Person.lean#L43) | `def HasFeature (a f : Prop) : Prop` | {}  |
| `Intentional` | def | [L30](formal/Logos/Person.lean#L30) | `def Intentional (s : Subject) : Prop` | {}  |
| `Person` | def | [L33](formal/Logos/Person.lean#L33) | `def Person (s : Subject) : Prop` | {}  |
| `RationalAct` | def | [L40](formal/Logos/Person.lean#L40) | `def RationalAct (a : Prop) : Prop` | {}  |
| `contentOf` | def | [L77](formal/Logos/Person.lean#L77) | `def contentOf : Subject → Prop | Sum.inl _ => True` | {}  |
| `everyContentIsAPerson` | theorem | [L105](formal/Logos/Person.lean#L105) | `theorem everyContentIsAPerson : ∀ p : Prop, Person (Sum.inr p)` | {} → C75 |
| `inseparability_24b` | theorem | [L56](formal/Logos/Person.lean#L56) | `theorem inseparability_24b : ∀ a : Prop, RationalAct a → (CarriesPersonalFeature` | {CL} → C25 |
| `positedDistinct` | theorem | [L114](formal/Logos/Person.lean#L114) | `theorem positedDistinct : (Sum.inr True : Subject) ≠ Sum.inr False` | {}  |
| `twoPersonsFromSubject` | theorem | [L90](formal/Logos/Person.lean#L90) | `theorem twoPersonsFromSubject : ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ ` | {} → C73 |

### `Logos.Plurality`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `EntityOf` | def | [L43](formal/Logos/Plurality.lean#L43) | `def EntityOf : Subject → Entity` | {}  |
| `NecessarySubject` | def | [L46](formal/Logos/Plurality.lean#L46) | `def NecessarySubject (s : Subject) : Prop` | {}  |
| `T12_directedPair` | theorem | [L109](formal/Logos/Plurality.lean#L109) | `theorem T12_directedPair : ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ ` | {} → C47 |
| `T12_twoPersons` | theorem | [L54](formal/Logos/Plurality.lean#L54) | `theorem T12_twoPersons : ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂` | {} → C40 |
| `T1_subjectExists` | theorem | [L79](formal/Logos/Plurality.lean#L79) | `theorem T1_subjectExists : ∃ s : Subject, Logos.Agency.Exists s` | {} → C21 |
| `T4_agentExists` | theorem | [L87](formal/Logos/Plurality.lean#L87) | `theorem T4_agentExists : ∃ s : Subject, Logos.Agency.Exists s ∧ Logos.Agency.Age` | {} → C23 |
| `T5_personExists` | theorem | [L97](formal/Logos/Plurality.lean#L97) | `theorem T5_personExists : ∃ s : Subject, Person s` | {} → C24 |
| `cogito_from_T12` | theorem | [L72](formal/Logos/Plurality.lean#L72) | `theorem cogito_from_T12 : ∃ s : Subject, ∃ p : Prop, Logos.Agency.A s p` | {} → C48 |
| `notAlone` | theorem | [L60](formal/Logos/Plurality.lean#L60) | `theorem notAlone : ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂` | {}  |

### `Logos.Semantics`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `FalseAt` | def | [L55](formal/Logos/Semantics.lean#L55) | `def FalseAt (w : World) (φ : Form) : Prop` | {}  |
| `Form` | inductive | [L22](formal/Logos/Semantics.lean#L22) | `inductive Form : Type` | —  |
| `NecessarilyFalse` | def | [L61](formal/Logos/Semantics.lean#L61) | `def ¬◇(φ : Form) : Prop` | {}  |
| `NecessarilyTrue` | def | [L58](formal/Logos/Semantics.lean#L58) | `def □(φ : Form) : Prop` | {}  |
| `Satisfies` | def | [L44](formal/Logos/Semantics.lean#L44) | `def Satisfies : World → Form → Prop | w, atom n => w n = TV.t` | {}  |
| `TV` | inductive | [L33](formal/Logos/Semantics.lean#L33) | `inductive TV : Type` | —  |
| `TrueAt` | def | [L52](formal/Logos/Semantics.lean#L52) | `def TrueAt (w : World) (φ : Form) : Prop` | {}  |
| `World` | abbrev | [L41](formal/Logos/Semantics.lean#L41) | `abbrev World : Type` | {}  |
| `bothNecessarilyTrueAndFalse` | theorem | [L102](formal/Logos/Semantics.lean#L102) | `theorem bothNecessarilyTrueAndFalse : (∃ τ : Form, □ τ) ∧ (∃ ρ : Form, ¬◇ ρ)` | {CL} → C37 |
| `lawExcludedMiddle` | theorem | [L76](formal/Logos/Semantics.lean#L76) | `theorem lawExcludedMiddle (φ : Form) : □(φ ∨ ¬φ)` | {CL} → C13 |
| `nonContradiction` | theorem | [L85](formal/Logos/Semantics.lean#L85) | `theorem nonContradiction (φ : Form) : ¬◇(φ ∧ ¬φ)` | {CL} → C14 |
| `sat_and` | theorem | [L67](formal/Logos/Semantics.lean#L67) | `theorem sat_and : w ⊨ (φ ∧ ψ) ↔ w ⊨ φ ∧ w ⊨ ψ` | {}  |
| `sat_imp` | theorem | [L71](formal/Logos/Semantics.lean#L71) | `theorem sat_imp : w ⊨ (φ → ψ) ↔ (w ⊨ φ → w ⊨ ψ)` | {}  |
| `sat_not` | theorem | [L65](formal/Logos/Semantics.lean#L65) | `theorem sat_not : w ⊨ ¬φ ↔ ¬ w ⊨ φ` | {}  |
| `sat_or` | theorem | [L69](formal/Logos/Semantics.lean#L69) | `theorem sat_or : w ⊨ (φ ∨ ψ) ↔ w ⊨ φ ∨ w ⊨ ψ` | {}  |

### `Logos.Truthmaker`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `Entity` | def | [L40](formal/Logos/Truthmaker.lean#L40) | `def Entity : Type` | {}  |
| `ExistsAt` | def | [L57](formal/Logos/Truthmaker.lean#L57) | `def ExistsAt (_w : World) (s : Subject) : Prop` | {} → Q7.2 |
| `Ground` | axiom | [L47](formal/Logos/Truthmaker.lean#L47) | `axiom Ground : Subject → Form → Prop` | {Ground}  |
| `NecessarilyFalse` | def | [L74](formal/Logos/Truthmaker.lean#L74) | `def ¬◇(φ : Form) : Prop` | {Ground}  |
| `NecessarilyTrue` | def | [L71](formal/Logos/Truthmaker.lean#L71) | `def □(φ : Form) : Prop` | {Ground}  |
| `TrueAt` | def | [L63](formal/Logos/Truthmaker.lean#L63) | `def TrueAt (w : World) : Form → Prop | atom n => ∃ e : Entity, ExistsAt w e ∧ Gr` | {Ground}  |
| `groundPrinciple_atom` | theorem | [L86](formal/Logos/Truthmaker.lean#L86) | `theorem groundPrinciple_atom (w : World) (n : Nat) : w ⊨ atom n → ∃ e : Entity, ` | {Ground} → C15 |
| `lawExcludedMiddle` | theorem | [L128](formal/Logos/Truthmaker.lean#L128) | `theorem lawExcludedMiddle (φ : Form) : □(φ ∨ ¬φ)` | {Ground, CL} → C16 |
| `noGround_selfRefutes` | theorem | [L99](formal/Logos/Truthmaker.lean#L99) | `theorem noGround_selfRefutes : ¬ (∃ (w : World) (n : Nat), w ⊨ atom n ∧ ¬ (∃ e :` | {Ground} → C60 |
| `nonContradiction` | theorem | [L136](formal/Logos/Truthmaker.lean#L136) | `theorem nonContradiction (φ : Form) : ¬◇(φ ∧ ¬φ)` | {Ground} → C17 |
| `sat_ground_and` | theorem | [L113](formal/Logos/Truthmaker.lean#L113) | `theorem sat_ground_and {w : World} {φ ψ : Form} : w ⊨ (φ ∧ ψ) ↔ w ⊨ φ ∧ w ⊨ ψ` | {Ground}  |
| `sat_ground_imp` | theorem | [L121](formal/Logos/Truthmaker.lean#L121) | `theorem sat_ground_imp {w : World} {φ ψ : Form} : w ⊨ (φ → ψ) ↔ (w ⊨ φ → w ⊨ ψ)` | {Ground}  |
| `sat_ground_not` | theorem | [L117](formal/Logos/Truthmaker.lean#L117) | `theorem sat_ground_not {w : World} {φ : Form} : w ⊨ ¬φ ↔ ¬ w ⊨ φ` | {Ground}  |
| `sat_ground_or` | theorem | [L109](formal/Logos/Truthmaker.lean#L109) | `theorem sat_ground_or {w : World} {φ ψ : Form} : w ⊨ (φ ∨ ψ) ↔ w ⊨ φ ∨ w ⊨ ψ` | {Ground}  |

### `Logos.Value`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `Affects` | def | [L53](formal/Logos/Value.lean#L53) | `def Affects (s t : Subject) : Prop` | {}  |
| `Alone` | def | [L77](formal/Logos/Value.lean#L77) | `def Alone (s : Subject) : Prop` | {}  |
| `AxPersonsAffect` | theorem | [L146](formal/Logos/Value.lean#L146) | `theorem AxPersonsAffect (s₁ s₂ : Subject) (_hs₁ : Person s₁) (_hs₂ : Person s₂) ` | {}  |
| `Harms` | def | [L61](formal/Logos/Value.lean#L61) | `def Harms (s t : Subject) : Prop` | {}  |
| `Helps` | def | [L57](formal/Logos/Value.lean#L57) | `def Helps (s t : Subject) : Prop` | {}  |
| `OtherAffects` | def | [L74](formal/Logos/Value.lean#L74) | `def OtherAffects (s : Subject) : Prop` | {}  |
| `aloneExcluded` | theorem | [L135](formal/Logos/Value.lean#L135) | `theorem aloneExcluded : ¬ ∃ s : Subject, Person s ∧ Alone s` | {} → C74 |
| `alone_no_other_affects` | theorem | [L80](formal/Logos/Value.lean#L80) | `theorem alone_no_other_affects {s : Subject} (ha : Alone s) : ¬ OtherAffects s` | {}  |
| `alone_no_other_help_harm` | theorem | [L88](formal/Logos/Value.lean#L88) | `theorem alone_no_other_help_harm {s : Subject} (ha : Alone s) : (¬ ∃ t : Subject` | {} → C56 |
| `harm_affects` | theorem | [L69](formal/Logos/Value.lean#L69) | `theorem harm_affects : ∀ {s t : Subject}, Harms s t → Affects s t` | {}  |
| `help_affects` | theorem | [L64](formal/Logos/Value.lean#L64) | `theorem help_affects : ∀ {s t : Subject}, Helps s t → Affects s t` | {}  |
| `neverAlone` | theorem | [L125](formal/Logos/Value.lean#L125) | `theorem neverAlone (s : Subject) : ¬ Alone s` | {}  |
| `otherSubject` | def | [L104](formal/Logos/Value.lean#L104) | `def otherSubject (s : Subject) : Subject` | {}  |
| `otherSubject_ne` | theorem | [L113](formal/Logos/Value.lean#L113) | `theorem otherSubject_ne (s : Subject) : otherSubject s ≠ s` | {}  |
| `valueInterpersonal_of_split` | theorem | [L156](formal/Logos/Value.lean#L156) | `theorem valueInterpersonal_of_split : (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) → ∃ ` | {} → C46 |

</details>

---
