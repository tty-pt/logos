# Γ — Deduction Map (mapa da dedução)

Versão derivada do estado formal atual. Este documento é **gerado** por `scripts/build_deduction.py` — não o edite à mão (regra de sincronização em `AGENTS.md`).

- **Fonte Lean:** `formal/Logos/*.lean` (kernel-checked, `lake build` verde, sorryAx 0)
- **Pegadas do kernel:** `formal/axiom_audit.json` (`#print axioms` por declaração — a pegada axiomática transitiva exata no kernel, meta-lógica incluída. Nota metodológica: a auditoria do kernel reporta dependências formais estritas; não certifica independentemente que as definições constitutivas não codifiquem compromissos substantivos)
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
| `✔` (só vocabulário) | teorema **axiom-free módulo o vocabulário primitivo declarado**: a pegada do kernel só contém vocábulos (`VOCAB`) que o próprio enunciado menciona, sem axioma substantivo (`SEM`/`META`/`TRANS`). Nota: `#print axioms` reporta apenas dependências formais do kernel; não certifica por si só que as definições não codifiquem compromissos constitutivos substantivos. Ex.: C25, C49, C51, C56, C62 (passos analíticos módulo vocabulário primitivo de agência/escolha). Inventário e justificação em [`VOCAB.md`](VOCAB.md); ver **Relatório de consistência** |
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
`Ground : Entity → Form → Prop` — _The truthmaker relation — an entity grounding a formula._

### A2 ◆ Vocabulary: the pure sort of subjects — that which performs acts of reasoning · `VOCAB`
`Subject : Type` — _Vocabulary: the pure sort of subjects — that which performs acts of reasoning._

### A3 ◆ The truthmaker principle: truth is grounded in reality · `SEM`
`Truthmaker : ∀ (w : World) (φ : Form), w ⊨ φ → ∃ e : Entity, ExistsAt w e ∧ Ground e φ` — _The truthmaker principle: truth is grounded in reality._

### C15 · ⚠
`w ⊨ atom n → ∃ e : Entity, ExistsAt w e ∧ Ground e atom n` — _Every atomic truth is grounded: where an atom is true, an entity exists there that grounds it._
Segue dos axiomas **A1**, **A2**, **A3** — [§24a](base.txt)

### C60 · ⚠
`¬ (∃ (w : World) (n : Nat), w ⊨ atom n ∧ ¬ (∃ e : Entity, ExistsAt w e ∧ Ground e atom n))` — _The denial that atomic truth is grounded refutes itself under the Truthmaker bridge._
Segue dos axiomas **A1**, **A2**, **A3** — [§24a (RAA)](base.txt)

### C16 · ✔
`□(φ ∨ ¬φ)` — _In every world, 'φ or not-φ' is true — composite truth is Tarskian-compositional._
[§22](base.txt)

### C17 · ✔
`¬◇(φ ∧ ¬φ)` — _In every world, 'φ and not-φ' cannot be true._
[§23](base.txt)

### A4 ◆ AxGlobalGround (SEM): a formula true in every world is grounded by a single entity that exists in every world · `SEM`
`AxGlobalGround : ∀ (φ : Form), □ φ → ∃ e : Entity, ∀ w : World, ExistsAt w e ∧ Ground e φ` — _AxGlobalGround (SEM): a formula true in every world is grounded by a single entity that exists in every world._

### C18 · ⚠
`∃ e : Entity, NecessaryEntity e ∧ Ground e τ` — _T7 — necessary truth forces necessary reality (base.txt T7)._
Segue dos axiomas **A1**, **A2**, **A4** — [§T7](base.txt) · [T7](theorems/T7.txt)

### C19 · ⚠
`∃ e : Entity, NecessaryEntity e ∧ Ground e (φ ∨ ¬φ)` — _C19 (closed): Grounding of the necessary excluded-middle reality under AxGlobalGround._
Segue de: **C16**, **C18** e dos axiomas **A1**, **A2**, **A4** — [§T7](base.txt) · [T7](theorems/T7.txt)

### C20 · ⚠
`(∀ e : Entity, Contingent e) → ∀ φ : Form, ¬ □ φ` — _The reductio shape of the prose: if every entity were contingent, no formula could be necessarily true._
Segue de: **C18** e dos axiomas **A1**, **A2**, **A4** — [§T7](base.txt) · [T7](theorems/T7.txt)

### C91 · ✔
`NecessarySubject s → NecessaryEntity (EntityOf s)` — _A subject that is necessary has an entity-correlate that is a necessary entity._
Segue do axioma **A2** (vocabulário do enunciado) — [§25/§27/T7 Passo A](base.txt) · [T7](theorems/T7.txt)

### C78 · ✖

### C79 · ✖

### C87 · ✖

### C88 · ✖

### C89 · ✖


---

## Level 2 — agency and person (`Logos.Agency`, `Person`, `Alternatives`, `Order`, `GroundPerson`)

### A5 ◆ Vocabulary: the meaning-act relation — a subject means a proposition · `VOCAB`
`Means : Subject → Prop → Prop` — _Vocabulary: the meaning-act relation — a subject means a proposition._

### C58 · ✔
`False` — _Step 4 (C58): Retorsion — asserting that no act occurs refutes itself_
Segue dos axiomas **A2**, **A5** (vocabulário do enunciado) — [§1 fnd](base.txt)

### C68 · ✔
`∃ s' : Subject, ∃ p' : Prop, Act s' p'` — _Cogito as a derived theorem: any performative assertion entails that an act occurs._
Segue dos axiomas **A2**, **A5** (vocabulário do enunciado) — [§1 fnd](base.txt)

### C59 · ✖
_Strong truth exists: some formula is true in every world (spike-level, axiom-free)._

### C21 · ✔
`∃ s : Subject, Logos.Agency.SubjectExists s` — _At least one subject exists: derived from the performative act-datum._
Segue dos axiomas **A2**, **A5** (vocabulário do enunciado) — [§1/T1](base.txt) · [T1](theorems/T1.txt)

### C22 · ✔
`∃ p : Prop, Content p` — _At least one content exists: every proposition is admissible content._
[§T2](base.txt) · [T2](theorems/T2.txt)

### C23 · ✔
`∃ s : Subject, Logos.Agency.SubjectExists s ∧ Logos.Agency.Agent s` — _At least one agent exists: someone who acts._
Segue de: **C21** e dos axiomas **A2**, **A5** (vocabulário do enunciado) — [§T4](base.txt) · [T4](theorems/T4.txt)

### C24 · ✔
`∃ s : Subject, Person s` — _At least one person exists: derived from the performative act-datum._
Segue dos axiomas **A2**, **A5** (vocabulário do enunciado) — [§T5](base.txt) · [T5](theorems/T5.txt)

### C25 · ✔
`∀ a : Prop, RationalAct a → (CarriesPersonalFeature a ↔ CarriesLogicalFeature a)` — _Every rational act carries a personal feature exactly when it carries a logical feature: personhood and logic travel together._
Segue dos axiomas **A2**, **A5** (vocabulário do enunciado) — [§24b](base.txt)

### C26 · ✔
`∃ p q : Prop, Incompatible p q ∧ T p ∧ IsFalse q` — _There are two incompatible alternatives, one of them true and the other false._
Segue de: **C4** — [**T9 (new)**](base.txt) · [T9](theorems/T9.txt)

### C27 · ✔
`Incompatible p (¬ p) ∧ T p ∧ IsFalse (¬ p)` — _Every true proposition is incompatible with its own negation._
[§13](base.txt)

### A6 ◆ AxTwoSubjects (META; poem P5/P7, failure traces in DESIGN · `META`
`AxTwoSubjects : (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) → ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂` — _AxTwoSubjects (META; poem P5/P7, failure traces in DESIGN.md D14 and HostileSemantics): the *reality* of right-and-wrong demands that there be at least two distinct persons. Narrower than the former single bridge `AxValueInterpersonal` (plurality only; affecti_

### C28 · ⚠
`¬ (∀ s : Subject, ∀ p : Prop, Fallible s p → T p)` — _A fallible judgment need not be true: fallibility is real._
Segue dos axiomas **A2**, **A5**, **A6** — [§T6](base.txt) · [T6](theorems/T6.txt)

### C29 · ⚠
`¬ (∀ s : Subject, ∀ p : Prop, Fallible s p ↔ T p)` — _Truth is not the same as being fallibly judged: what is true transcends the will to judge._
Segue dos axiomas **A2**, **A5**, **A6** — [§T6](base.txt) · [T6](theorems/T6.txt)

### C30 · ⚠
`¬ (∀ s : Subject, ∀ p : Prop, Correct s p ↔ Incorrect s p)` — _Correct and incorrect judging are distinct: correctness is not incorrectness._
Segue de: **C48** e dos axiomas **A2**, **A5**, **A6** — [§8](base.txt)

### C31 · ✔
`T q` — _Consequence preserves truth: whatever two true premises jointly imply is true._
[§9](base.txt)

### C83 · ✔
`¬ Correct s NoAct` — _The Cartesian Retortion (half 1): no subject can ever correctly judge that no act occurs_
Segue dos axiomas **A2**, **A5** (vocabulário do enunciado) — [§8](base.txt)

### C84 · ✔
`∃ s' : Subject, ∃ p' : Prop, A s' p'` — _The Retorsive Cogito: even the skeptic's denial that any act occurs strictly witnesses that an act occurs. The act cannot be denied without providing the witness that refutes the denial._
Segue dos axiomas **A2**, **A5** (vocabulário do enunciado) — [§1/§8](base.txt)

### A7 ◆ AxPersonalGround (META): the *necessary* reality grounds the personal features present in the rational act · `META`
`AxPersonalGround : ∀ {f : Prop}, IsPresentPersonalFeature f → ∃ e : Entity, NecessaryEntity e ∧ GroundProp e f` — _AxPersonalGround (META): the *necessary* reality grounds the personal features present in the rational act._

### A8 ◆ The grounding relation between an entity and a proposition · `VOCAB`
`GroundProp : Entity → Prop → Prop` — _The grounding relation between an entity and a proposition._

### C32 · ⚠
`∃ e : Entity, NecessaryEntity e ∧ Personal e` — _T8 — the necessary reality is personal (PROVEN↑ under the two META bridges declared above)._
Segue dos axiomas **A2**, **A5**, **A7**, **A8** — [§T8](base.txt) · [T8](theorems/T8.txt)

### A9 ◆ The §24a atom-grounding principle reflected at the level of propositions · `SEM`
`GroundPrincipleProp : ∀ {f : Prop}, T f → ∃ e : Entity, GroundProp e f` — _The §24a atom-grounding principle reflected at the level of propositions._

### C33 · ⚠
`∃ e : Entity, GroundProp e f` — _Every present personal feature is grounded in reality (the weak, necessity-free half of §24a that is provable without the META bridges, for completeness)._
Segue dos axiomas **A2**, **A5**, **A8**, **A9** — [§T8](base.txt) · [T8](theorems/T8.txt)

### C34 · ⚠
`∃ e : Entity, NecessaryEntity e` — _§24a applied to a necessary truth yields a grounder (linking Prop-level and world-level principles: T7 supplies the necessary entity)._
Segue de: **C18** e dos axiomas **A1**, **A2**, **A4** — [§T8](base.txt) · [T8](theorems/T8.txt)

### C90 · ✖


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
`□(¬ N_T ∧ ¬ N_F)` — _The distinction between right and wrong under the identity-model alias._
Segue de: **C36** — [P2](poem.txt)

### C39 · ✔
`∃ s : Subject, Person s ∧ ∃ p q : Prop, Incompatible p q` — _There is a field of choice: some person with two incompatible alternatives._
Segue de: **C24**, **C26** e dos axiomas **A2**, **A5** (vocabulário do enunciado) — [P4](poem.txt)

### C40 · ⚠
`∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂` — _There are at least two distinct persons._
Segue de: **C36** e dos axiomas **A2**, **A5**, **A6** — [P5/P7](poem.txt)

### C41 · ⚠
`∃ s t : Subject, Person s ∧ Person t ∧ s ≠ t ∧ Lovable s ∧ Lovable t` — _There are two distinct persons, both lovable._
Segue de: **C40** e dos axiomas **A2**, **A5**, **A6** — [P7](poem.txt)

### C48 · ⚠
`∃ s : Subject, ∃ p : Prop, Logos.Agency.A s p` — _The acting subject is exhibited from plurality: someone acts on something._
Segue de: **C40** e dos axiomas **A2**, **A5**, **A6** — [P1/§1](poem.txt)

### C49 · ✔
`∃ t : Subject, Means t p` — _Meaning needs a subject: whatever is meant is meant by someone._
Segue dos axiomas **A2**, **A5** (vocabulário do enunciado) — [§13/IM_STUPID](base.txt)

### C50 · ✔
`Incompatible p (¬ p)` — _Every proposition is incompatible with its own negation._
[§14](base.txt)

### C51 · ✔
`∃ p q : Prop, ChoiceField s p q` — _Any person has a choice field: a person is always before two incompatible alternatives._
Segue de: **C50** e dos axiomas **A2**, **A5** (vocabulário do enunciado) — [§14/IM_STUPID](base.txt)

### C52 · ✔
`∃ s : Subject, ∃ p q : Prop, ChoiceField s p q` — _The choice field exists: some subject is before two incompatible alternatives._
Segue de: **C24**, **C51**, **F1a** e dos axiomas **A2**, **A5** (vocabulário do enunciado) — [§14](base.txt)

### C53 · ✔
`False` — _C53 (field form): performative retorsion — asserting that no choice field exists refutes itself. Footprint: `{Means, Subject}` (VOCAB only; zero AxTwoSubjects)._
Segue dos axiomas **A2**, **A5** (vocabulário do enunciado) — [§14](base.txt)

### C54 · ⚠
`∃ s : Subject, ∃ p q : Prop, ChoiceField s p q` — _Right-and-wrong commits a choice field: where there is truth and error, someone is before an incompatible pair._
Segue de: **C51**, **F1a** e dos axiomas **A2**, **A5**, **A6** — [IM_STUPID §2](base.txt)

### C55 · ⚠
`∃ s : Subject, ∃ p q : Prop, A s p ∧ (Correct s p ∨ Incorrect s p) ∧ ChoiceField s p q` — _The judge is before a choice field: whoever judges acts, correctly or incorrectly._
Segue de: **C48**, **C50** e dos axiomas **A2**, **A5**, **A6** — [§8/§14](base.txt)

### C56 · ✔
`(¬ ∃ t : Subject, t ≠ s ∧ Helps s t) ∧ (¬ ∃ t : Subject, t ≠ s ∧ Harms s t)` — _A lone subject neither helps nor harms anyone else._
Segue do axioma **A2** (vocabulário do enunciado) — [P6](poem.txt)

### C57 · ✔
`False` — _C57: Retorsion — asserting that no actual subject exists refutes itself_
Segue dos axiomas **A2**, **A5** (vocabulário do enunciado) — [§26](base.txt)

### C42 · ⚠
`∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ Loves s₁ s₂ ∧ NecessarySubject s₁ ∧ NecessarySubject s₂` — _Two distinct persons stand in an eternal love-relation, and both persist in every world._
Segue de: **C47** e dos axiomas **A2**, **A5**, **A6** — [P8](poem.txt)

### C43 · ⚠
`∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ Loves s₁ s₂` — _Two distinct persons stand in a love-relation._
Segue de: **C42**, **F5** e dos axiomas **A2**, **A5**, **A6** — [P8](poem.txt)

### C44 · ⚠
`∀ w, ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ Loves s₁ s₂ ∧ ExistsAt _w (EntityOf s₁) ∧ ExistsAt _w (EntityOf s₂)` — _In every world, two distinct persons stand in a love-relation._
Segue de: **C42**, **F5** e dos axiomas **A2**, **A5**, **A6** — [P8](poem.txt)

### C45 · ⚠
`□(∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ Loves s₁ s₂)` — _Necessarily, two distinct persons stand in a love-relation._
Segue de: **C42**, **F5** e dos axiomas **A2**, **A5**, **A6** — [P8](poem.txt)

### C46 · ⚠
`(¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) → ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ (Affects s₁ s₂ ∨ Affects s₂ s₁)` — _Right-and-wrong yields two distinct persons who bear on each other._
Segue dos axiomas **A2**, **A5**, **A6** — [P5](poem.txt)

### C47 · ⚠
`∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ Affects s₁ s₂` — _There are two distinct persons where one bears on the other._
Segue de: **C40** e dos axiomas **A2**, **A5**, **A6** — [P5/P7](poem.txt)

### C61 · ⚠
`∃ s : Subject, ∃ p : Prop, Means s p` — _Right-and-wrong implies someone who means (poem P3, line 18 "há certo e há errado → há significado → há alguém para quem algo significar")._
Segue de: **C54** e dos axiomas **A2**, **A5**, **A6** — [P3](poem.txt)

### C62 · ✔
`∃ p : Prop, Logos.Choice.Meaning_I p` — _Right and wrong need meaning: the normative predicates are properties of meaning-acts, so wherever right-or-wrong is realized, a meaning (and thus a subject, C49) is realized._
Segue dos axiomas **A2**, **A5** (vocabulário do enunciado) — [P3](poem.txt)

### C69 · ✖
_Free will of origin is retired: manufactured constructor split destroyed._

### C70 · ✖
_Posited content non-freedom is retired: manufactured witness destroyed._

### C71 · ✖
_Origin freedom denial self-refuting is retired: manufactured witness destroyed._

### C72 · ✖
_Judge is free is retired: act does not entail free will; `judge_commits` yields only the choice field._

### C73 · ✖

### C74 · ⚠
`¬ ∃ s : Subject, Person s ∧ Alone s` — _No person is alone: there is no personal lone subject under the plurality bridge._
Segue de: **C36** e dos axiomas **A2**, **A5**, **A6** — [P5](poem.txt)

### C75 · ✖

### C76 · ✖

### C77 · ✔
`∃ s : Subject, Person s ∧ NecessarySubject s` — _There exists a necessary person: someone who is a person and persists in every world._
Segue de: **C24** e dos axiomas **A2**, **A5** (vocabulário do enunciado) — [P5/P8](poem.txt)

### C85 · ✔
`∀ {s t : Subject}, Helps s t → ¬ Harms s t` — _Helping excludes harming: benevolence is incompatible with malice._
Segue do axioma **A2** (vocabulário do enunciado) — [P6](poem.txt)

### C86 · ✔
`∀ {s t : Subject}, Loves s t → Helps s t` — _Love implies positive help: the lover benefits the beloved._
Segue do axioma **A2** (vocabulário do enunciado) — [P6/P8](poem.txt)

### C92 · ✔
`∃ e : Entity, NecessaryEntity e` — _There exists a necessary entity: the entity-correlate of the performing person exists in every world._
Segue de: **C24**, **C91** e dos axiomas **A2**, **A5** (vocabulário do enunciado) — [P8/§27](poem.txt)


---

## Level 2c — the act as initiation (`Logos.Initiation`, 2026-09-17)

### C63 · ✔
`¬ IsTransfer R` — _Initiation is not transfer: a relation with genuine alternatives is not the graph of any function._
[§1](base.txt)

### C64 · ✖

### C65 · ✖

### C66 · ✖

### C67 · ✖

### C80 · ✖

### C81 · ✖

### C82 · ✖


---

## Deferred / blocked

| ID | Prosa | Status | Nota / lema em falta |
|---|---|---|---|
| F1a | §13–§15 choice-field existence (`∃s p q`, `ChoiceField s p q`) | ✔ | person_hasChoiceField/choiceField_exists {Means, Subject} + judge_commits CL (choice-realism batch, C51–C52/C55; renamed 2026-09-18 — field form, not genuine choice) |
| F1b | §15 genuine choice & freedom of the actor | ✖ | alvo explícito Choice.genuineChoice_exists := ∃ s, ∃ p q, Chooses s p q (def-proposição; **não** axioma/sorry); recurso único formalizado como def **Choice.rejectedHornCoMeant := ∃ s p, A s p ∧ A s (¬ p)** — nada força um ato de significação a vir com a significação da sua negação; fronteira rejectedHornCoMeant → genuineChoice_exists ({Means, Subject}) e genuineChoice_exists → freeWillExists (freeWillExists_of_genuineChoice, {Means, Subject} — Chooses → FreeWill é definicional, ninguém usa freeWillExists como premissa). **Veredito hostil 2026-09-18 (opção 3 — bloqueio irreducível)**: genuineChoice_requires_error_possibility ({Means, Subject}, veridicalidade mata co-significação), assertion_consistency/no_one_asserts_incompatible_pair ({Means, Subject}, a via assertiva é impossível) e CountermodelVeridicalMeaning/not_entails_genuine_choice(_with_plurality) ({}, fragmento inteiro satisfeito com escolha vazia). Premissas substantivas candidatas registadas, NÃO introduzidas: AxCoMeaningNegation, co-sujeito Incorrect∧Denies, auto-representação. |
| F2 | §21 teleology (`Ought → Goal`) | ➖ | deontic layer (normativity → telos) |
| F3 | §28 Good (`§20 → bem`) | ➖ | moral good from logical normativity not yet derived |
| F4 | §28 Love | ⚠ | Love.T13_someoneLovable (C41) under {AxTwoSubjects, Means, Subject} |
| F5 | §28 EternalRelation | ⚠ | Love.T14_eternalRelation (C42) under {AxTwoSubjects, Means, Subject} |
| F6 | §28 Trinity | ➖ | no argument exists yet (§28/§29) |
| Q7.2 | weaker `AxGlobalGround` | ANSWERED | answered by batch A2-swap-theorem: for atoms the swap needs no premise at all (definitional via world-vacuous ExistsAt); the compound instance is unforced, not weaken-able (DESIGN.md) |

### F1a · →
*Vide **C51** (passo já apresentado).*

### F1b · ✖
`genuineChoice_exists : Prop` — _The precise missing lemma of the freedom frontier (F1b, BLOCKED): a genuine chooser exists — some subject co-meaning two incompatible contents._
Segue dos axiomas **A2**, **A5** (vocabulário do enunciado) — [§15 genuine choice & freedom of the actor](base.txt)

### F2 · ➖
_Deontic teleology is deferred: how norms point at goals is not yet derived._

### F3 · ➖
_Moral good from logical normativity is deferred: not yet derived._

### F4 · →
*Vide **C41** (passo já apresentado).*

### F5 · →
*Vide **C42** (passo já apresentado).*

### F6 · ➖
_The Trinity is deferred: no argument exists yet._

### Q7.2 · ANSWERED
`ExistsAt (w : World) (_s : Subject) : Prop` — _Simulated world-existence: the subject exists only in the `true` world._
[weaker `AxGlobalGround`](base.txt)


---
## Faith / DEFERRED

| ID | Prosa | Status | Nota / lema em falta |
|---|---|---|---|
| FAITH-1 | P2 necessity | → | dissolved in C1: necDistinction is now a theorem (C38); world content = C37 |
| FAITH-2 | P8 eternal love | → | rests on AxTwoSubjects (META bridge restored after Unit countermodel) + AxPersonStability (theorem); T14 is proven under {AxTwoSubjects} (C42–C45) |
| F7 | §15 the bipolar half of freedom | ✖ | (the bipolar half is subsumed by unary FreeWill; the remaining gap is NOT "freedom impossible to derive" — it is **existence of *genuine choice* not yet derived from the performative datum**: genuineChoice_exists BLOCKED on rejectedHornCoMeant; Chooses → FreeWill is definitional, freeWillExists_of_genuineChoice {Means, Subject}; world-level ChoiceAt remains a future SEM vocabulary) |
| F8 | Trinity | ➖ | not attempted (§28/§29) |
| F9 | Incarnation / creation | ➖ | poem P10, faith datum |

### FAITH-1 · →
*Vide **C38** (passo já apresentado).*

### FAITH-2 · →
`AxTwoSubjects : (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) → ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂` — _AxTwoSubjects (META; poem P5/P7, failure traces in DESIGN.md D14 and HostileSemantics): the *reality* of right-and-wrong demands that there be at least two distinct persons. Narrower than the former single bridge `AxValueInterpersonal` (plurality only; affecti_
[P8 eternal love](poem.txt)

### F7 · ✖
`FreeWill : S → Prop` — _The bipolar half of freedom is subsumed by unary `FreeWill`; the open gap is not 'freedom impossible to derive' but *existence of genuine choice* not yet derived from the performative datum (F1b, `genuineChoice_exists`). World-level `ChoiceAt : World → Subject → Prop → Prop` remains a future, priced SEM vocabulary._
[§15 the bipolar half of freedom](base.txt)

### F8 · ➖
_The Trinity is not attempted._

### F9 · ➖
_Incarnation and creation are faith data from the poem, deferred._


---
## Inventário de axiomas (9 declarações)

| Axioma | Nº | Tag | Significado (EN) / preço | Depende dele (claims) |
|---|---|---|---|---|
| `Means` | A5 | `VOCAB` | Vocabulary: the meaning-act relation — a subject means a proposition. | C21, C23, C24, C25, C28, C29, C30, C32, C33, C39, C40, C41, C42, C43, C44, C45, C46, C47, C48, C49, C51, C52, C53, C54, C55, C57, C58, C61, C62, C68, C74, C77, C83, C84, C92, F1b, FAITH-2 |
| `Subject` | A2 | `VOCAB` | Vocabulary: the pure sort of subjects — that which performs acts of reasoning. | C15, C18, C19, C20, C21, C23, C24, C25, C28, C29, C30, C32, C33, C34, C39, C40, C41, C42, C43, C44, C45, C46, C47, C48, C49, C51, C52, C53, C54, C55, C56, C57, C58, C60, C61, C62, C68, C74, C77, C83, C84, C85, C86, C91, C92, F1b, FAITH-2 |
| `AxPersonalGround` | A7 | `META` | AxPersonalGround (META): the *necessary* reality grounds the personal features present in the rational act. | C32 |
| `GroundPrincipleProp` | A9 | `SEM` | The §24a atom-grounding principle reflected at the level of propositions. | C33 |
| `GroundProp` | A8 | `VOCAB` | The grounding relation between an entity and a proposition. | C32, C33 |
| `AxGlobalGround` | A4 | `SEM` | AxGlobalGround (SEM): a formula true in every world is grounded by a single entity that exists in every world. | C18, C19, C20, C34 |
| `Ground` | A1 | `VOCAB` | The truthmaker relation — an entity grounding a formula. | C15, C18, C19, C20, C34, C60 |
| `Truthmaker` | A3 | `SEM` | The truthmaker principle: truth is grounded in reality. | C15, C60 |
| `AxTwoSubjects` | A6 | `META` | AxTwoSubjects (META; poem P5/P7, failure traces in DESIGN.md D14 and HostileSemantics): the *reality* of right-and-wrong demands that there be at least two distinct persons. Narrower than the former single bridge `AxValueInterpersonal` (plurality only; affecti | C28, C29, C30, C40, C41, C42, C43, C44, C45, C46, C47, C48, C54, C55, C61, C74, FAITH-2 |

Detalhe do kernel:

- `Logos.Agency.Means`
- `Logos.Agency.Subject`
- `Logos.GroundPerson.AxPersonalGround`
- `Logos.GroundPerson.GroundPrincipleProp`
- `Logos.GroundPerson.GroundProp`
- `Logos.Modal.AxGlobalGround`
- `Logos.Truthmaker.Ground`
- `Logos.Truthmaker.Truthmaker`
- `Logos.Value.AxTwoSubjects`

---
## Relatório de consistência (kernel ↔ GAPMAP)

- Claims do GAPMAP com teorema localizado no kernel (FOUND): **79** / 105
- Steps com **significado em inglês**: **89** / 105 · **sem gloss:** C78, C79, C87, C88, C89, C90, C73, C75, C76, C64, C65, C66, C67, C80, C81, C82
- **Claims com teorema em falta (MISSING — teorema referenciado não localizado no kernel) (1):**
  - `C59` ref `Spike_M5.strongTruthExists` — §27
- **Claims retirados / bloqueados (RETIRED/BLOCKED — fora da dedução ativa) (25):**
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
  - `F8` (`DEFERRED`) ref `—` — Trinity
  - `F9` (`DEFERRED`) ref `—` — Incarnation / creation
- Teoremas no kernel **sem claim** no GAPMAP (86): Agency.T1_subjectExists_of_act, Agency.act_exists_of_assert, Agency.act_implies_agent, Agency.act_implies_content, Agency.act_implies_means, Agency.act_implies_rational, Agency.act_of_asserting_no_act, Agency.act_requires_subject, Agency.an_actual_subject_exists_of_act, Agency.assertion_is_act, Agency.noSubjectSort_selfRefutes, Agency.noSubject_performative_selfRefutes, Agency.noSubject_selfRefutes, Agency.subject_exists_of_act, Agency.subject_exists_of_assert, Choice.T11_choiceField_from_plurality, Choice.asserting_noChoiceField_is_choiceField, Choice.assertion_consistency, Choice.canChoose_unfold, Choice.choiceField_exists_from_plurality, Choice.chooses_implies_freeWill, Choice.freeWillExists_of_chooses, Choice.freeWillExists_of_genuineChoice, Choice.genuineChoice_requires_error_possibility, Choice.judge_asserting_rightWrong_has_choiceField, Choice.meaning_I_needs_subject, Choice.noChoiceField_contradicts_field, Choice.noSubject_contradicts_subject, Choice.no_one_asserts_incompatible_pair, Choice.rejectedHornCoMeant_implies_genuineChoice, Core.atomicWitnessFalsehood, Core.someTruthAndSomeFalsehood, Core.tschema, GroundPerson.AxGroundBearing, HostileSemantics.act_exists_of_act, HostileSemantics.not_entails_content_person, HostileSemantics.not_entails_decoupled_freewill, HostileSemantics.not_entails_person, HostileSemantics.not_entails_plurality, HostileSemantics.subject_exists_of_act, Love.AxPersonStability, Love.love_affects, Love.love_not_harms, Love.loves_of_helps, Love.no_contingent_person, Modal.necessary_entity_exists_of_necessary_subject, Modal.subject_nec_entity_nec_iff, Necessity.dia_def, Necessity.nec4, Necessity.nec4PH, Necessity.necDistinction_content, Necessity.necK, Necessity.necKPH, Necessity.necMP, Necessity.necT, Necessity.necTPH, Necessity.nec_apply, Order.fallible_false, Order.judgment_implies_act, Order.judgment_implies_cogito, Order.judgment_of_no_act_is_incorrect, Order.rightDistinctWrong_implies_meaning, Order.rightWrongDistinction_implies_meaning, Person.person_exists_of_act, Person.person_exists_of_assert, Person.person_of_act, Person.person_of_subject, Plurality.T1_of_assert, Plurality.T1_subjectExists_from_plurality, Plurality.T4_agentExists_from_plurality, Plurality.T4_of_assert, Plurality.T5_of_assert, Plurality.T5_personExists_from_plurality, Plurality.notAlone, Semantics.sat_and, Semantics.sat_imp, Semantics.sat_not, Semantics.sat_or, Truthmaker.sat_ground_and, Truthmaker.sat_ground_imp, Truthmaker.sat_ground_not, Truthmaker.sat_ground_or, Value.AxPersonsAffect, Value.alone_no_other_affects, Value.harm_affects, Value.help_affects
- **Estatuto derivado do kernel** (#print axioms + `Tag:` dos axiomas): **47 ✔** · **24 ⚠** · **0 ◆** (passos únicos detalhados no mapa)
- **Inventário reconciliado de claims (105 no total):** 71 passos únicos ativos (47 ✔ + 24 ⚠) · 5 repetidos / dissolvidos (→) · 23 bloqueados / em falta (✖) · 5 diferidos (➖) · 1 outros (ANSWERED)
- Estatuto GAPMAP × derivado: **sem divergências** (transcrição verificada).
- **Steps ⚠ sob axioma substantivo (SEM/META)** (26): C15, C18, C19, C20, C28, C29, C30, C32, C33, C34, C40, C41, C42, C43, C44, C45, C46, C47, C48, C54, C55, C60, C61, C74, F4, F5
- **Exibidos ✔ por só-vocabulário (axiom-free módulo vocabulário declarado)** (pegada do kernel só com vocábulos VOCAB do próprio enunciado — SEM/META/TRANS nenhum): C21, C23, C24, C25, C39, C49, C51, C52, C53, C56, C57, C58, C62, C68, C77, C83, C84, C85, C86, C91, C92, F1a
- Pegada kernel × GAPMAP: **sem divergências**.
- **Grafo (closure) × audição (#print axioms) divergem em 1 claims** (subconta transitiva do depviz — toolchain, não ledger; a audição manda):
  - `FAITH-2` audição `{AxTwoSubjects, Means, Subject}` vs grafo `{}`
- Axiomas declarados no kernel: **9** — **todos com `Tag:` na docstring Lean**
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
| C14 | `Logos.Semantics.nonContradiction` | [Semantics.lean#L85](formal/Logos/Semantics.lean#L85) | `{CL}` | CL | `Semantics.FalseAt`, `Semantics.Form`, `Semantics.NecessarilyFalse`, `Semantics.Satisfies`, `Semantics.World`, `Semantics.sat_and`, `Semantics.sat_not` | **C37** `bothNecessarilyTrueAndFalse` |
| C15 | `Logos.Truthmaker.groundPrinciple_atom` | [Truthmaker.lean#L88](formal/Logos/Truthmaker.lean#L88) | `{Truthmaker, Ground, Subject}` | {Truthmaker, Ground, Subject} (SEM bridge Truthmaker) | `Semantics.World`, `Truthmaker.Entity`, `Truthmaker.ExistsAt`, axiom `Ground` (VOCAB), `Truthmaker.TrueAt`, axiom `Truthmaker` (SEM) | — |
| C60 | `Logos.Truthmaker.noGround_selfRefutes` | [Truthmaker.lean#L95](formal/Logos/Truthmaker.lean#L95) | `{Truthmaker, Ground, Subject}` | {Truthmaker, Ground, Subject} (companion of C15) | `Semantics.World`, `Truthmaker.Entity`, `Truthmaker.ExistsAt`, axiom `Ground` (VOCAB), `Truthmaker.TrueAt`, axiom `Truthmaker` (SEM) | — |
| C16 | `Logos.Truthmaker.lawExcludedMiddle` | [Truthmaker.lean#L123](formal/Logos/Truthmaker.lean#L123) | `{CL}` | {CL} | `Semantics.Form`, `Semantics.World`, `Truthmaker.NecessarilyTrue`, `Truthmaker.TrueAt` | **C19** `T7_excludedMiddleInstance` |
| C17 | `Logos.Truthmaker.nonContradiction` | [Truthmaker.lean#L131](formal/Logos/Truthmaker.lean#L131) | `{}` | {} | `Semantics.Form`, `Semantics.Satisfies`, `Semantics.World`, `Truthmaker.NecessarilyFalse`, `Truthmaker.TrueAt` | — |
| C18 | `Logos.Modal.T7_necessaryReality` | [Modal.lean#L68](formal/Logos/Modal.lean#L68) | `{AxGlobalGround, Ground, Subject}` | {AxGlobalGround, Ground, Subject} (SEM bridge AxGlobalGround) | axiom `AxGlobalGround` (SEM), `Modal.NecessaryEntity`, `Modal.actualWorld`, `Semantics.Form`, `Semantics.World`, `Truthmaker.Entity`, `Truthmaker.ExistsAt`, axiom `Ground` (VOCAB), `Truthmaker.NecessarilyTrue` | **C34** `necessary_truth_has_necessary_grounder`, **C19** `T7_excludedMiddleInstance`, **C20** `noNecessaryTruthIfAllContingent` |
| C19 | `Logos.Modal.T7_excludedMiddleInstance` | [Modal.lean#L74](formal/Logos/Modal.lean#L74) | `{AxGlobalGround, Ground, Subject, CL}` | {AxGlobalGround, Ground, Subject, CL} (derived from C18 and C16 under AxGlobalGround) | `Modal.NecessaryEntity`, **C18** `T7_necessaryReality`, `Semantics.Form`, `Truthmaker.Entity`, axiom `Ground` (VOCAB), **C16** `lawExcludedMiddle` | — |
| C20 | `Logos.Modal.noNecessaryTruthIfAllContingent` | [Modal.lean#L80](formal/Logos/Modal.lean#L80) | `{AxGlobalGround, Ground, Subject}` | {AxGlobalGround, Ground, Subject} (as C18) | `Modal.Contingent`, `Modal.NecessaryEntity`, **C18** `T7_necessaryReality`, `Semantics.Form`, `Truthmaker.Entity`, axiom `Ground` (VOCAB), `Truthmaker.NecessarilyTrue` | — |
| C91 | `Logos.Modal.subject_nec_entity_nec` | [Modal.lean#L97](formal/Logos/Modal.lean#L97) | `{Subject}` | {Subject} (VOCAB; ExistsAt/EntityOf partilhados — contramodelo hostil {} mostra que não é lei lógica) | axiom `Subject` (VOCAB), `Modal.NecessaryEntity`, `Plurality.EntityOf`, `Plurality.NecessarySubject` | **C92** `necessary_entity_exists`, `Modal.necessary_entity_exists_of_necessary_subject` |
| C78 | — | — | — | (retired: manufactured Sum.inl origin grounding destroyed under hostile semantics) | Modal.contingent_ground | — |
| C79 | — | — | — | (retired: manufactured ultimate ground destroyed under hostile semantics) | Modal.ultimateGround_exists | — |
| C87 | — | — | — | (retired: manufactured Sum.inl origin necessity destroyed) | Modal.origin_is_necessary | — |
| C88 | — | — | — | (retired: manufactured origin quantifier swap destroyed) | Modal.transcendental_quantifier_swap | — |
| C89 | — | — | — | (retired: manufactured ultimate ground by initiation destroyed) | Modal.ultimateGroundInit_exists | — |
| C58 | `Logos.Agency.noCogito_selfRefutes` | [Agency.lean#L143](formal/Logos/Agency.lean#L143) | `{Means, Subject}` | {Means, Subject} (sequência de 4 passos: asserção é ato → ato existe → sujeito existe → refutação de NoAct) | `Agency.Act`, `Agency.Asserts`, `Agency.NoAct`, axiom `Subject` (VOCAB), `Agency.act_exists_of_assert` | — |
| C68 | `Logos.Agency.Cogito` | [Agency.lean#L147](formal/Logos/Agency.lean#L147) | `{Means, Subject}` | {Means, Subject} (teorema derivado de qualquer asserção; deriva ato e sujeito via regra constitutiva) | `Agency.Act`, `Agency.Asserts`, axiom `Subject` (VOCAB), `Agency.act_exists_of_assert` | — |
| C59 | — | — | — | **{CL}** (C37 lever) | Spike_M5.strongTruthExists | — |
| C21 | `Logos.Plurality.T1_subjectExists` | [Plurality.lean#L66](formal/Logos/Plurality.lean#L66) | `{Means, Subject}` | {Means, Subject} (derivado do ato intencional C68 via regra constitutiva act_requires_subject; desacoplado de AxTwoSubjects) | `Agency.Act`, axiom `Subject` (VOCAB), `Agency.SubjectExists`, `Agency.subject_exists_of_act` | **C23** `T4_agentExists` |
| C22 | `Logos.Agency.T2_contentExists` | [Agency.lean#L206](formal/Logos/Agency.lean#L206) | `{}` | **{}** — Content _ := True (def), True witnesses content | `Agency.Content` | — |
| C23 | `Logos.Plurality.T4_agentExists` | [Plurality.lean#L74](formal/Logos/Plurality.lean#L74) | `{Means, Subject}` | {Means, Subject} (derivado do ato intencional C68 → C21; Agent é := True, def) | `Agency.Act`, `Agency.Agent`, axiom `Subject` (VOCAB), `Agency.SubjectExists`, **C21** `T1_subjectExists` | — |
| C24 | `Logos.Plurality.T5_personExists` | [Plurality.lean#L84](formal/Logos/Plurality.lean#L84) | `{Means, Subject}` | {Means, Subject} (derivado do ato intencional C68 → C21 → C24 via colapso definicional §12) | `Agency.Act`, axiom `Subject` (VOCAB), `Person.Person`, `Person.person_exists_of_act` | **C39** `T11_choiceField`, **C52** `choiceField_exists`, **C77** `necessaryPersonExists`, **C92** `necessary_entity_exists` |
| C25 | `Logos.Person.inseparability_24b` | [Person.lean#L92](formal/Logos/Person.lean#L92) | `{Means, Subject, CL}` | {Means, Subject, CL} | `Agency.A`, axiom `Means` (VOCAB), axiom `Subject` (VOCAB), `Agency.act_implies_means`, `Core.IsFalse`, `Core.T`, `Person.CarriesLogicalFeature`, `Person.CarriesPersonalFeature`, `Person.HasFeature`, `Person.RationalAct` | — |
| C26 | `Logos.Alternatives.T9_incompatibleAlternatives` | [Alternatives.lean#L24](formal/Logos/Alternatives.lean#L24) | `{}` | {} (E0) | `Alternatives.Incompatible`, `Core.IsFalse`, `Core.T`, **C4** `atomicTruthWitnessed`, `Core.atomicWitnessFalsehood` | **C39** `T11_choiceField`, `Choice.T11_choiceField_from_plurality` |
| C27 | `Logos.Alternatives.incompatible_with_negation` | [Alternatives.lean#L35](formal/Logos/Alternatives.lean#L35) | `{}` | {} (E0) | `Alternatives.Incompatible`, `Core.IsFalse`, `Core.T`, `Core.tschema` | — |
| C28 | `Logos.Order.T6_fallibility` | [Order.lean#L90](formal/Logos/Order.lean#L90) | `{AxTwoSubjects, Means, Subject}` | {AxTwoSubjects, Means, Subject} (via T12 + Core.someFalse) | axiom `Subject` (VOCAB), `Core.IsFalse`, `Core.T`, `Order.Fallible`, `Order.fallible_false` | — |
| C29 | `Logos.Order.T6_truthTranscendsWill` | [Order.lean#L99](formal/Logos/Order.lean#L99) | `{AxTwoSubjects, Means, Subject}` | {AxTwoSubjects, Means, Subject} (as C28) | axiom `Subject` (VOCAB), `Core.IsFalse`, `Core.T`, `Order.Fallible`, `Order.fallible_false` | — |
| C30 | `Logos.Order.correctness_distinct` | [Order.lean#L107](formal/Logos/Order.lean#L107) | `{AxTwoSubjects, Means, Subject, CL}` | {AxTwoSubjects, Means, Subject, CL} (defs act-relative §8) | `Agency.A`, axiom `Subject` (VOCAB), `Core.IsFalse`, `Core.T`, `Order.Correct`, `Order.Incorrect`, **C48** `cogito_from_T12` | — |
| C31 | `Logos.Order.consequence_preserves_truth` | [Order.lean#L150](formal/Logos/Order.lean#L150) | `{}` | {} (E0) | `Core.T`, `Core.tschema` | — |
| C83 | `Logos.Order.no_correct_judgment_of_no_act` | [Order.lean#L159](formal/Logos/Order.lean#L159) | `{Means, Subject}` | {Means, Subject} | `Agency.A`, axiom `Subject` (VOCAB), `Core.T`, `Order.Correct`, `Order.NoAct` | `Order.judgment_of_no_act_is_incorrect` |
| C84 | `Logos.Order.judgment_of_no_act_proves_act` | [Order.lean#L180](formal/Logos/Order.lean#L180) | `{Means, Subject}` | {Means, Subject} | `Agency.A`, axiom `Subject` (VOCAB), `Order.Correct`, `Order.Incorrect`, `Order.NoAct`, `Order.judgment_implies_act` | — |
| C32 | `Logos.GroundPerson.T8_personalGround` | [GroundPerson.lean#L101](formal/Logos/GroundPerson.lean#L101) | `{AxPersonalGround, GroundProp, Means, Subject}` | {AxPersonalGround, GroundProp, Means, Subject} | `GroundPerson.AxGroundBearing`, axiom `AxPersonalGround` (META), axiom `GroundProp` (VOCAB), `GroundPerson.IsPresentPersonalFeature`, `GroundPerson.Personal`, `GroundPerson.Realizes`, `Modal.NecessaryEntity`, `Truthmaker.Entity` | — |
| C33 | `Logos.GroundPerson.present_feature_is_grounded` | [GroundPerson.lean#L109](formal/Logos/GroundPerson.lean#L109) | `{GroundPrincipleProp, GroundProp, Means, Subject}` | {GroundPrincipleProp, GroundProp, Means, Subject} | `Core.T`, axiom `GroundPrincipleProp` (SEM), axiom `GroundProp` (VOCAB), `GroundPerson.IsPresentPersonalFeature`, `Truthmaker.Entity` | — |
| C34 | `Logos.GroundPerson.necessary_truth_has_necessary_grounder` | [GroundPerson.lean#L114](formal/Logos/GroundPerson.lean#L114) | `{AxGlobalGround, Ground, Subject}` | {AxGlobalGround, Ground, Subject} (via C18) | `Modal.NecessaryEntity`, **C18** `T7_necessaryReality`, `Semantics.Form`, `Truthmaker.Entity`, axiom `Ground` (VOCAB), `Truthmaker.NecessarilyTrue` | — |
| C90 | — | — | — | (retired: manufactured ultimate ground destroyed under hostile semantics) | GroundPerson.personal_ultimate_ground_exists | — |
| F1a | `Logos.Choice.person_hasChoiceField` | [Choice.lean#L250](formal/Logos/Choice.lean#L250) | `{Means, Subject}` | — | `Agency.A`, `Agency.Agent`, axiom `Means` (VOCAB), `Agency.Rational`, axiom `Subject` (VOCAB), `Alternatives.Incompatible`, `Choice.ChoiceField`, **C50** `incompatible_self_negation`, `Person.Intentional`, `Person.Person` | **C54** `JUDGE_HAS_CHOICE_FIELD`, **C52** `choiceField_exists`, `Choice.choiceField_exists_from_plurality` |
| F1b | `Logos.Choice.genuineChoice_exists` | [Choice.lean#L170](formal/Logos/Choice.lean#L170) | `{Means, Subject}` | — | axiom `Subject` (VOCAB), `Choice.Chooses` | `Choice.freeWillExists_of_genuineChoice`, `Choice.genuineChoice_requires_error_possibility`, `Choice.rejectedHornCoMeant_implies_genuineChoice` |
| F2 | — | — | — | — | — | — |
| F3 | — | — | — | — | — | — |
| F4 | `Logos.Love.T13_someoneLovable` | [Love.lean#L81](formal/Logos/Love.lean#L81) | `{AxTwoSubjects, Means, Subject}` | — | axiom `Subject` (VOCAB), `Love.Lovable`, `Person.Person`, **C40** `T12_twoPersons` | — |
| F5 | `Logos.Love.T14_eternalRelation` | [Love.lean#L150](formal/Logos/Love.lean#L150) | `{AxTwoSubjects, Means, Subject}` | — | axiom `Subject` (VOCAB), `Love.AxPersonStability`, `Love.Loves`, `Love.loves_of_helps`, `Person.Person`, `Plurality.NecessarySubject`, **C47** `T12_directedPair`, `Value.Affects` | **C43** `T14_content`, **C45** `T14_square`, **C44** `T14_world` |
| F6 | — | — | — | — | — | — |
| Q7.2 | `CountermodelPersonNotNecessary.ExistsAt` | [HostileSemantics.lean#L468](formal/Logos/HostileSemantics.lean#L468) | `{}` | — | — | — |
| C35 | `Logos.Core.negatedAbsolutes` | [Core.lean#L129](formal/Logos/Core.lean#L129) | `{}` | {} (E0) | `Core.N_F`, `Core.N_T`, **C6** `notEverythingTrue`, **C2** `notNothingTrue` | — |
| C36 | `Logos.Core.rightWrongDistinction` | [Core.lean#L145](formal/Logos/Core.lean#L145) | `{}` | {} (E0) | `Core.N_F`, `Core.N_T`, **C6** `notEverythingTrue`, **C2** `notNothingTrue` | **FAITH-1** `necDistinction`, **C40** `T12_twoPersons`, **C74** `aloneExcluded` |
| C37 | `Logos.Semantics.bothNecessarilyTrueAndFalse` | [Semantics.lean#L102](formal/Logos/Semantics.lean#L102) | `{CL}` | CL | `Semantics.Form`, `Semantics.NecessarilyFalse`, `Semantics.NecessarilyTrue`, **C13** `lawExcludedMiddle`, **C14** `nonContradiction` | — |
| C38 | `Logos.Necessity.necDistinction` | [Necessity.lean#L116](formal/Logos/Necessity.lean#L116) | `{}` | {} (E0; C1: identity-model alias; world content = C37) | `Core.N_F`, `Core.N_T`, **C36** `rightWrongDistinction`, `Necessity.Necessity`, `Semantics.World` | `Necessity.necDistinction_content` |
| C39 | `Logos.Choice.T11_choiceField` | [Choice.lean#L230](formal/Logos/Choice.lean#L230) | `{Means, Subject}` | {Means, Subject} (campo de escolha — não escolha genuína — derivado do ato intencional C68 → C24 → C39; renomeação/split 2026-09-18) | `Agency.A`, axiom `Subject` (VOCAB), `Alternatives.Incompatible`, **C26** `T9_incompatibleAlternatives`, `Core.IsFalse`, `Core.T`, `Person.Person`, **C24** `T5_personExists` | — |
| C40 | `Logos.Plurality.T12_twoPersons` | [Plurality.lean#L44](formal/Logos/Plurality.lean#L44) | `{AxTwoSubjects, Means, Subject}` | {AxTwoSubjects, Means, Subject} (settled by Unit countermodel that 1 act does not entail plurality; requires META bridge AxTwoSubjects) | axiom `Subject` (VOCAB), **C36** `rightWrongDistinction`, `Person.Person`, **FAITH-2** `AxTwoSubjects` | `Choice.choiceField_exists_from_plurality`, **C41** `T13_someoneLovable`, **C47** `T12_directedPair`, `Plurality.T1_subjectExists_from_plurality`, `Plurality.T4_agentExists_from_plurality`, `Plurality.T5_personExists_from_plurality`, **C48** `cogito_from_T12`, `Plurality.notAlone` |
| C41 | `Logos.Love.T13_someoneLovable` | [Love.lean#L81](formal/Logos/Love.lean#L81) | `{AxTwoSubjects, Means, Subject}` | {AxTwoSubjects, Means, Subject} (via C40) | axiom `Subject` (VOCAB), `Love.Lovable`, `Person.Person`, **C40** `T12_twoPersons` | — |
| C48 | `Logos.Plurality.cogito_from_T12` | [Plurality.lean#L57](formal/Logos/Plurality.lean#L57) | `{AxTwoSubjects, Means, Subject}` | {AxTwoSubjects, Means, Subject} | `Agency.A`, `Agency.Agent`, axiom `Means` (VOCAB), `Agency.Rational`, axiom `Subject` (VOCAB), `Person.Intentional`, `Person.Person`, **C40** `T12_twoPersons` | **C30** `correctness_distinct`, `Order.fallible_false`, **C55** `judge_commits` |
| C49 | `Logos.Choice.meaning_needs_subject` | [Choice.lean#L111](formal/Logos/Choice.lean#L111) | `{Means, Subject}` | {Means, Subject} | axiom `Means` (VOCAB), axiom `Subject` (VOCAB) | — |
| C50 | `Logos.Choice.incompatible_self_negation` | [Choice.lean#L87](formal/Logos/Choice.lean#L87) | `{}` | **{}** (pure logic — the field around any meaning-act) | `Alternatives.Incompatible` | `Choice.asserting_noChoiceField_is_choiceField`, `Choice.judge_asserting_rightWrong_has_choiceField`, **C51** `person_hasChoiceField`, `Choice.rejectedHornCoMeant_implies_genuineChoice`, **C55** `judge_commits` |
| C51 | `Logos.Choice.person_hasChoiceField` | [Choice.lean#L250](formal/Logos/Choice.lean#L250) | `{Means, Subject}` | {Means, Subject} | `Agency.A`, `Agency.Agent`, axiom `Means` (VOCAB), `Agency.Rational`, axiom `Subject` (VOCAB), `Alternatives.Incompatible`, `Choice.ChoiceField`, **C50** `incompatible_self_negation`, `Person.Intentional`, `Person.Person` | **C54** `JUDGE_HAS_CHOICE_FIELD`, **C52** `choiceField_exists`, `Choice.choiceField_exists_from_plurality` |
| C52 | `Logos.Choice.choiceField_exists` | [Choice.lean#L259](formal/Logos/Choice.lean#L259) | `{Means, Subject}` | {Means, Subject} (o campo é real, derivado do ato intencional C68 → C52; renomeado 2026-09-18) | `Agency.A`, axiom `Subject` (VOCAB), `Choice.ChoiceField`, **C51** `person_hasChoiceField`, `Person.Person`, **C24** `T5_personExists` | — |
| C53 | `Logos.Choice.noChoiceField_selfRefutes` | [Choice.lean#L283](formal/Logos/Choice.lean#L283) | `{Means, Subject}` | {Means, Subject} (retorsão performativa do campo: negar o campo é ele próprio um ato de campo contra a sua negação) | `Agency.Act`, `Agency.Asserts`, axiom `Subject` (VOCAB), `Choice.NoChoiceField`, `Choice.asserting_noChoiceField_is_choiceField` | — |
| C54 | `Logos.Choice.JUDGE_HAS_CHOICE_FIELD` | [Choice.lean#L299](formal/Logos/Choice.lean#L299) | `{AxTwoSubjects, Means, Subject}` | {AxTwoSubjects, Means, Subject} (derivação operativa via AxTwoSubjects h e person_hasChoiceField; renomeado 2026-09-18) | axiom `Subject` (VOCAB), `Choice.ChoiceField`, **C51** `person_hasChoiceField`, `Core.N_F`, `Core.N_T`, `Person.Person`, **FAITH-2** `AxTwoSubjects` | **C61** `rightWrong_implies_someone_means` |
| C55 | `Logos.Order.judge_commits` | [Order.lean#L127](formal/Logos/Order.lean#L127) | `{AxTwoSubjects, Means, Subject, CL}` | {AxTwoSubjects, Means, Subject, CL} (defs act-relative §8) | `Agency.A`, axiom `Subject` (VOCAB), `Alternatives.Incompatible`, `Choice.ChoiceField`, **C50** `incompatible_self_negation`, `Core.IsFalse`, `Core.T`, `Order.Correct`, `Order.Incorrect`, **C48** `cogito_from_T12` | `Order.rightWrongDistinction_implies_meaning` |
| C56 | `Logos.Value.alone_no_other_help_harm` | [Value.lean#L97](formal/Logos/Value.lean#L97) | `{Subject}` | {Subject} | axiom `Subject` (VOCAB), `Value.Alone`, `Value.Harms`, `Value.Helps` | — |
| C57 | `Logos.Choice.noSubject_selfRefutes` | [Choice.lean#L326](formal/Logos/Choice.lean#L326) | `{Means, Subject}` | {Means, Subject} (retorsão performativa genuína: negar o sujeito é um ato que testemunha o sujeito) | `Agency.Asserts`, `Agency.NoSubject`, axiom `Subject` (VOCAB), `Agency.noSubject_performative_selfRefutes` | — |
| C42 | `Logos.Love.T14_eternalRelation` | [Love.lean#L150](formal/Logos/Love.lean#L150) | `{AxTwoSubjects, Means, Subject}` | {AxTwoSubjects, Means, Subject} (built on directed pair C47 under AxTwoSubjects) | axiom `Subject` (VOCAB), `Love.AxPersonStability`, `Love.Loves`, `Love.loves_of_helps`, `Person.Person`, `Plurality.NecessarySubject`, **C47** `T12_directedPair`, `Value.Affects` | **C43** `T14_content`, **C45** `T14_square`, **C44** `T14_world` |
| C43 | `Logos.Love.T14_content` | [Love.lean#L185](formal/Logos/Love.lean#L185) | `{AxTwoSubjects, Means, Subject}` | {AxTwoSubjects, Means, Subject} | axiom `Subject` (VOCAB), `Love.Loves`, **C42** `T14_eternalRelation`, `Person.Person`, `Plurality.NecessarySubject` | — |
| C44 | `Logos.Love.T14_world` | [Love.lean#L163](formal/Logos/Love.lean#L163) | `{AxTwoSubjects, Means, Subject}` | {AxTwoSubjects, Means, Subject} (world-anchored honest □) | axiom `Subject` (VOCAB), `Love.Loves`, **C42** `T14_eternalRelation`, `Necessity.NecessityPH`, `Person.Person`, `Plurality.EntityOf`, `Plurality.NecessarySubject`, `Semantics.World`, `Truthmaker.ExistsAt` | — |
| C45 | `Logos.Love.T14_square` | [Love.lean#L175](formal/Logos/Love.lean#L175) | `{AxTwoSubjects, Means, Subject}` | {AxTwoSubjects, Means, Subject} (image of the old statement shape) | axiom `Subject` (VOCAB), `Love.Loves`, **C42** `T14_eternalRelation`, `Necessity.Necessity`, `Person.Person`, `Plurality.NecessarySubject`, `Semantics.World` | — |
| C46 | `Logos.Value.valueInterpersonal_of_split` | [Value.lean#L145](formal/Logos/Value.lean#L145) | `{AxTwoSubjects, Means, Subject}` | {AxTwoSubjects, Means, Subject} (recovery theorem under AxTwoSubjects) | axiom `Subject` (VOCAB), `Core.N_F`, `Core.N_T`, `Person.Person`, `Value.Affects`, `Value.AxPersonsAffect`, **FAITH-2** `AxTwoSubjects` | — |
| C47 | `Logos.Plurality.T12_directedPair` | [Plurality.lean#L124](formal/Logos/Plurality.lean#L124) | `{AxTwoSubjects, Means, Subject}` | {AxTwoSubjects, Means, Subject} (chain node — distinctness is forward direction; T14 built on this node) | axiom `Subject` (VOCAB), `Person.Person`, **C40** `T12_twoPersons`, `Value.Affects` | **C42** `T14_eternalRelation` |
| C61 | `Logos.Choice.rightWrong_implies_someone_means` | [Choice.lean#L319](formal/Logos/Choice.lean#L319) | `{AxTwoSubjects, Means, Subject}` | {AxTwoSubjects, Means, Subject} (JUDGE_HAS_CHOICE_FIELD C54 ∘ rightWrongDistinction C36) | `Agency.A`, axiom `Means` (VOCAB), axiom `Subject` (VOCAB), `Alternatives.Incompatible`, `Choice.ChoiceField`, **C54** `JUDGE_HAS_CHOICE_FIELD`, `Core.N_F`, `Core.N_T` | — |
| C62 | `Logos.Order.rightWrong_implies_meaning` | [Order.lean#L46](formal/Logos/Order.lean#L46) | `{Means, Subject}` | {Means, Subject} | `Agency.A`, axiom `Means` (VOCAB), axiom `Subject` (VOCAB), `Choice.Meaning_I`, `Core.IsFalse`, `Core.T`, `Order.Correct`, `Order.Incorrect` | `Order.rightDistinctWrong_implies_meaning`, `Order.rightWrongDistinction_implies_meaning` |
| C69 | — | — | — | (retired: manufactured freedom via Sum.inl destroyed under hostile semantics; genuine-choice replacement is Choice.Chooses/rejectedHornCoMeant) | — | — |
| C70 | — | — | — | (retired: manufactured free will destroyed under hostile semantics) | — | — |
| C71 | — | — | — | (retired: manufactured freedom destroyed under hostile semantics) | — | — |
| C72 | — | — | — | (retired: act does not entail free will; Order.judge_commits yields only the choice field; Chooses → FreeWill is definitional but its existence needs rejectedHornCoMeant) | — | — |
| C73 | — | — | — | (demoted: Unit countermodel settles that 1 act does not entail plurality; manufactured Sum.inl/inr witness destroyed) | Person.twoPersonsFromSubject | — |
| C74 | `Logos.Value.aloneExcluded` | [Value.lean#L122](formal/Logos/Value.lean#L122) | `{AxTwoSubjects, Means, Subject}` | {AxTwoSubjects, Means, Subject} (under the plurality bridge AxTwoSubjects, a lone person is excluded) | axiom `Subject` (VOCAB), **C36** `rightWrongDistinction`, `Person.Person`, `Value.Alone`, **FAITH-2** `AxTwoSubjects` | — |
| C75 | — | — | — | (killed under hostile semantics: content existence does not imply personhood; tripartite report) | Person.everyContentIsAPerson | — |
| C76 | — | — | — | (excised: manufactured witness destroyed) | Love.T14_canonicalRigid | — |
| C77 | `Logos.Love.necessaryPersonExists` | [Love.lean#L124](formal/Logos/Love.lean#L124) | `{Means, Subject}` | {Means, Subject} (VOCAB; **re-anchored 2026-09-18** ao dado performativo, sem AxTwoSubjects — a necessidade da pessoa é *definicional*, ExistsAt (Subject) := True; complementar ao concreto Love.no_contingent_person) | `Agency.Act`, axiom `Subject` (VOCAB), `Love.AxPersonStability`, `Person.Person`, `Plurality.NecessarySubject`, **C24** `T5_personExists` | — |
| C85 | `Logos.Value.help_not_harm` | [Value.lean#L78](formal/Logos/Value.lean#L78) | `{Subject}` | {Subject} | axiom `Subject` (VOCAB), `Value.Harms`, `Value.Helps` | `Love.loves_of_helps` |
| C86 | `Logos.Love.love_helps` | [Love.lean#L47](formal/Logos/Love.lean#L47) | `{Subject}` | {Subject} | axiom `Subject` (VOCAB), `Love.Loves`, `Value.Harms`, `Value.Helps` | — |
| C92 | `Logos.Love.necessary_entity_exists` | [Love.lean#L138](formal/Logos/Love.lean#L138) | `{Means, Subject}` | {Means, Subject} (sem AxTwoSubjects; distinto de T7/C18) | `Agency.Act`, axiom `Subject` (VOCAB), `Love.AxPersonStability`, `Modal.NecessaryEntity`, **C91** `subject_nec_entity_nec`, `Person.Person`, `Plurality.EntityOf`, **C24** `T5_personExists`, `Truthmaker.Entity` | — |
| C63 | `Logos.Initiation.branches_not_transfer` | [Initiation.lean#L27](formal/Logos/Initiation.lean#L27) | `{}` | **{}** (lógica pura — sem axioma, sem vocabulário) | `Initiation.Branches`, `Initiation.IsTransfer` | — |
| C64 | — | — | — | (retired: manufactured Sum.inl origin destroyed under hostile semantics) | Initiation.originates_not_transfer | — |
| C65 | — | — | — | (retired: manufactured personhood by initiation destroyed under hostile semantics) | Initiation.person_iff_originates | — |
| C66 | — | — | — | (retired: manufactured witness destroyed under hostile semantics) | Initiation.Cogito_Init | — |
| C67 | — | — | — | (retired: manufactured witness destroyed under hostile semantics) | Initiation.noInitiation_selfRefutes | — |
| C80 | — | — | — | (retired: manufactured posited content branch evaluation destroyed) | Initiation.posited_not_branch | — |
| C81 | — | — | — | (retired: manufactured origin branch evaluation destroyed) | Initiation.origin_branches | — |
| C82 | — | — | — | (retired: manufactured initiating person destroyed) | Initiation.origin_is_initiating_person | — |
| FAITH-1 | `Logos.Necessity.necDistinction` | [Necessity.lean#L116](formal/Logos/Necessity.lean#L116) | `{}` | — | `Core.N_F`, `Core.N_T`, **C36** `rightWrongDistinction`, `Necessity.Necessity`, `Semantics.World` | `Necessity.necDistinction_content` |
| FAITH-2 | `Logos.Value.AxTwoSubjects` | [Value.lean#L113](formal/Logos/Value.lean#L113) | `{AxTwoSubjects, Means, Subject}` | — | axiom `Subject` (VOCAB), `Core.N_F`, `Core.N_T`, `Person.Person` | **C54** `JUDGE_HAS_CHOICE_FIELD`, **C40** `T12_twoPersons`, **C74** `aloneExcluded`, **C46** `valueInterpersonal_of_split` |
| F7 | `CountermodelNoFreeWill.FreeWill` | [HostileSemantics.lean#L284](formal/Logos/HostileSemantics.lean#L284) | `{}` | — | — | — |
| F8 | — | — | — | — | — | — |
| F9 | — | — | — | — | — | — |

</details>

---
## Índice de declarações do kernel

<details>
<summary>Todos os teoremas/defs user-authored, por módulo (linha e axiomas de kernel) →</summary>

### ``

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `ActOntology` | structure | [L185](formal/Logos/HostileSemantics.lean#L185) | `structure ActOntology where` | —  |

### `CountermodelActWithoutSubject`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `Act` | def | [L195](formal/Logos/HostileSemantics.lean#L195) | `def Act : Entity → Prop → Prop` | —  |
| `ConstitutiveAct` | def | [L209](formal/Logos/HostileSemantics.lean#L209) | `def ConstitutiveAct (I : ActOntology) : Prop` | —  |
| `Entity` | def | [L194](formal/Logos/HostileSemantics.lean#L194) | `def Entity : Type` | —  |
| `Person` | def | [L197](formal/Logos/HostileSemantics.lean#L197) | `def Person : Entity → Prop` | —  |
| `Subject` | def | [L196](formal/Logos/HostileSemantics.lean#L196) | `def Subject : Entity → Prop` | —  |
| `act_occurs` | theorem | [L199](formal/Logos/HostileSemantics.lean#L199) | `theorem act_occurs : ∃ s : Entity, ∃ p : Prop, Act s p` | —  |
| `act_without_subject` | theorem | [L204](formal/Logos/HostileSemantics.lean#L204) | `theorem act_without_subject : (∃ s : Entity, ∃ p : Prop, Act s p) ∧ ¬ (∃ s : Ent` | —  |
| `countermodel_violates_constitutive_act` | theorem | [L220](formal/Logos/HostileSemantics.lean#L220) | `theorem countermodel_violates_constitutive_act : ¬ ConstitutiveAct { Entity` | —  |
| `no_person` | theorem | [L201](formal/Logos/HostileSemantics.lean#L201) | `theorem no_person : ¬ ∃ s : Entity, Person s` | —  |
| `no_subject` | theorem | [L200](formal/Logos/HostileSemantics.lean#L200) | `theorem no_subject : ¬ ∃ s : Entity, Subject s` | —  |
| `subject_of_constitutive_act` | theorem | [L213](formal/Logos/HostileSemantics.lean#L213) | `theorem subject_of_constitutive_act (I : ActOntology) (hConst : ConstitutiveAct ` | —  |

### `CountermodelImpersonalUltimateGround`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `Entity` | abbrev | [L730](formal/Logos/HostileSemantics.lean#L730) | `abbrev Entity : Type` | —  |
| `GroundEntity` | def | [L732](formal/Logos/HostileSemantics.lean#L732) | `def GroundEntity (_x _y : Entity) : Prop` | —  |
| `Personal` | def | [L734](formal/Logos/HostileSemantics.lean#L734) | `def Personal (_e : Entity) : Prop` | —  |
| `UltimateGround` | def | [L733](formal/Logos/HostileSemantics.lean#L733) | `def UltimateGround (u : Entity) : Prop` | —  |
| `no_personal_ultimate` | theorem | [L741](formal/Logos/HostileSemantics.lean#L741) | `theorem no_personal_ultimate : ¬ ∃ u : Entity, UltimateGround u ∧ Personal u` | —  |
| `ultimate_exists` | theorem | [L736](formal/Logos/HostileSemantics.lean#L736) | `theorem ultimate_exists : ∃ u : Entity, UltimateGround u` | —  |
| `ultimate_not_entails_personal` | theorem | [L746](formal/Logos/HostileSemantics.lean#L746) | `theorem ultimate_not_entails_personal : (∃ u : Entity, UltimateGround u) ∧ ¬ (∃ ` | —  |

### `CountermodelInfiniteGroundChain`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `Entity` | abbrev | [L695](formal/Logos/HostileSemantics.lean#L695) | `abbrev Entity : Type` | —  |
| `GroundEntity` | def | [L698](formal/Logos/HostileSemantics.lean#L698) | `def GroundEntity (x y : Entity) : Prop` | —  |
| `UltimateGround` | def | [L700](formal/Logos/HostileSemantics.lean#L700) | `def UltimateGround (u : Entity) : Prop` | —  |
| `asymmetric` | theorem | [L705](formal/Logos/HostileSemantics.lean#L705) | `theorem asymmetric (x y : Entity) : GroundEntity x y → ¬ GroundEntity y x` | —  |
| `infinite_chain_has_no_ultimate` | theorem | [L715](formal/Logos/HostileSemantics.lean#L715) | `theorem infinite_chain_has_no_ultimate : (∀ x, ¬ GroundEntity x x) ∧ (∀ x y, Gro` | —  |
| `irreflexive` | theorem | [L702](formal/Logos/HostileSemantics.lean#L702) | `theorem irreflexive (x : Entity) : ¬ GroundEntity x x` | —  |
| `no_ultimate` | theorem | [L711](formal/Logos/HostileSemantics.lean#L711) | `theorem no_ultimate : ¬ ∃ u : Entity, UltimateGround u` | —  |
| `transitive` | theorem | [L708](formal/Logos/HostileSemantics.lean#L708) | `theorem transitive (x y z : Entity) : GroundEntity x y → GroundEntity y z → Grou` | —  |

### `CountermodelNoFreeWill`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `A` | def | [L282](formal/Logos/HostileSemantics.lean#L282) | `def A : S → Prop → Prop` | —  |
| `Chooses` | def | [L283](formal/Logos/HostileSemantics.lean#L283) | `def Chooses : S → Prop → Prop → Prop` | —  |
| `FreeWill` | def | [L284](formal/Logos/HostileSemantics.lean#L284) | `def FreeWill : S → Prop` | — → F7 |
| `S` | def | [L281](formal/Logos/HostileSemantics.lean#L281) | `def S : Type` | —  |
| `act_does_not_imply_choice` | theorem | [L289](formal/Logos/HostileSemantics.lean#L289) | `theorem act_does_not_imply_choice : (∃ s : S, ∃ p : Prop, A s p) ∧ ¬ (∃ s : S, ∃` | —  |
| `act_does_not_imply_freewill` | theorem | [L292](formal/Logos/HostileSemantics.lean#L292) | `theorem act_does_not_imply_freewill : (∃ s : S, ∃ p : Prop, A s p) ∧ ¬ (∃ s : S,` | —  |
| `act_occurs` | theorem | [L286](formal/Logos/HostileSemantics.lean#L286) | `theorem act_occurs : ∃ s : S, ∃ p : Prop, A s p` | —  |
| `no_choice` | theorem | [L287](formal/Logos/HostileSemantics.lean#L287) | `theorem no_choice : ¬ ∃ s : S, ∃ p q : Prop, Chooses s p q` | —  |
| `no_free_will` | theorem | [L288](formal/Logos/HostileSemantics.lean#L288) | `theorem no_free_will : ¬ ∃ s : S, FreeWill s` | —  |

### `CountermodelNoPerson`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `A` | def | [L263](formal/Logos/HostileSemantics.lean#L263) | `def A : S → Prop → Prop` | —  |
| `Person` | def | [L264](formal/Logos/HostileSemantics.lean#L264) | `def Person : S → Prop` | —  |
| `S` | def | [L262](formal/Logos/HostileSemantics.lean#L262) | `def S : Type` | —  |
| `act_does_not_imply_person` | theorem | [L268](formal/Logos/HostileSemantics.lean#L268) | `theorem act_does_not_imply_person : (∃ s : S, ∃ p : Prop, A s p) ∧ ¬ (∃ s : S, P` | —  |
| `act_occurs` | theorem | [L266](formal/Logos/HostileSemantics.lean#L266) | `theorem act_occurs : ∃ s : S, ∃ p : Prop, A s p` | —  |
| `no_person` | theorem | [L267](formal/Logos/HostileSemantics.lean#L267) | `theorem no_person : ¬ ∃ s : S, Person s` | —  |

### `CountermodelPersonNotNecessary`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `ExistsAt` | def | [L468](formal/Logos/HostileSemantics.lean#L468) | `def ExistsAt (w : World) (_s : Subject) : Prop` | — → Q7.2 |
| `NecessarySubject` | def | [L472](formal/Logos/HostileSemantics.lean#L472) | `def NecessarySubject (s : Subject) : Prop` | —  |
| `NecessitySignature` | structure | [L488](formal/Logos/HostileSemantics.lean#L488) | `structure NecessitySignature where` | —  |
| `Person` | def | [L470](formal/Logos/HostileSemantics.lean#L470) | `def Person (_s : Subject) : Prop` | —  |
| `Subject` | abbrev | [L464](formal/Logos/HostileSemantics.lean#L464) | `abbrev Subject : Type` | —  |
| `World` | abbrev | [L465](formal/Logos/HostileSemantics.lean#L465) | `abbrev World : Type` | —  |
| `no_necessary_subject` | theorem | [L476](formal/Logos/HostileSemantics.lean#L476) | `theorem no_necessary_subject : ¬ ∃ s : Subject, NecessarySubject s` | —  |
| `not_entails_person_necessary` | theorem | [L496](formal/Logos/HostileSemantics.lean#L496) | `theorem not_entails_person_necessary : ¬ (∀ I : NecessitySignature, (∃ s : I.Sub` | —  |
| `person_exists` | theorem | [L474](formal/Logos/HostileSemantics.lean#L474) | `theorem person_exists : ∃ s : Subject, Person s` | —  |
| `person_not_entails_necessary` | theorem | [L482](formal/Logos/HostileSemantics.lean#L482) | `theorem person_not_entails_necessary : (∃ s : Subject, Person s) ∧ ¬ (∃ s : Subj` | —  |

### `CountermodelPluralityWithoutLove`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `Loves` | def | [L761](formal/Logos/HostileSemantics.lean#L761) | `def Loves (_s _t : Subject) : Prop` | —  |
| `Person` | def | [L760](formal/Logos/HostileSemantics.lean#L760) | `def Person (_s : Subject) : Prop` | —  |
| `Subject` | abbrev | [L759](formal/Logos/HostileSemantics.lean#L759) | `abbrev Subject : Type` | —  |
| `no_love` | theorem | [L767](formal/Logos/HostileSemantics.lean#L767) | `theorem no_love : ¬ ∃ s₁ s₂ : Subject, Loves s₁ s₂` | —  |
| `plurality_not_entails_love` | theorem | [L772](formal/Logos/HostileSemantics.lean#L772) | `theorem plurality_not_entails_love : (∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧` | —  |
| `two_persons_exist` | theorem | [L763](formal/Logos/HostileSemantics.lean#L763) | `theorem two_persons_exist : ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂` | —  |

### `CountermodelSubjectNecessityNotEntityNecessity`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `Entity` | abbrev | [L383](formal/Logos/HostileSemantics.lean#L383) | `abbrev Entity : Type` | —  |
| `EntityExistsAt` | def | [L395](formal/Logos/HostileSemantics.lean#L395) | `def EntityExistsAt (w : World) (_e : Entity) : Prop` | —  |
| `EntityOf` | def | [L387](formal/Logos/HostileSemantics.lean#L387) | `def EntityOf (_s : Subject) : Entity` | —  |
| `NecessaryEntity` | def | [L401](formal/Logos/HostileSemantics.lean#L401) | `def NecessaryEntity (e : Entity) : Prop` | —  |
| `NecessarySubject` | def | [L398](formal/Logos/HostileSemantics.lean#L398) | `def NecessarySubject (s : Subject) : Prop` | —  |
| `NecessityLift` | structure | [L422](formal/Logos/HostileSemantics.lean#L422) | `structure NecessityLift where` | —  |
| `Subject` | abbrev | [L382](formal/Logos/HostileSemantics.lean#L382) | `abbrev Subject : Type` | —  |
| `SubjectExistsAt` | def | [L391](formal/Logos/HostileSemantics.lean#L391) | `def SubjectExistsAt (_w : World) (_s : Subject) : Prop` | —  |
| `World` | abbrev | [L381](formal/Logos/HostileSemantics.lean#L381) | `abbrev World : Type` | —  |
| `necessary_subject_is_necessary` | theorem | [L404](formal/Logos/HostileSemantics.lean#L404) | `theorem necessary_subject_is_necessary : NecessarySubject ()` | —  |
| `no_necessary_entity` | theorem | [L409](formal/Logos/HostileSemantics.lean#L409) | `theorem no_necessary_entity : ¬ ∃ e : Entity, NecessaryEntity e` | —  |
| `not_holds_of_arbitrary_signature` | theorem | [L431](formal/Logos/HostileSemantics.lean#L431) | `theorem not_holds_of_arbitrary_signature : ¬ (∀ (I : NecessityLift), ∀ s : I.Sub` | —  |
| `subject_necessity_not_entails_entity_necessity` | theorem | [L416](formal/Logos/HostileSemantics.lean#L416) | `theorem subject_necessity_not_entails_entity_necessity : (∃ s : Subject, Necessa` | —  |

### `CountermodelSubjectWithoutPerson`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `Act` | def | [L237](formal/Logos/HostileSemantics.lean#L237) | `def Act : Entity → Prop → Prop` | —  |
| `Entity` | def | [L236](formal/Logos/HostileSemantics.lean#L236) | `def Entity : Type` | —  |
| `Person` | def | [L239](formal/Logos/HostileSemantics.lean#L239) | `def Person : Entity → Prop` | —  |
| `Subject` | def | [L238](formal/Logos/HostileSemantics.lean#L238) | `def Subject : Entity → Prop` | —  |
| `act_and_subject_without_person` | theorem | [L255](formal/Logos/HostileSemantics.lean#L255) | `theorem act_and_subject_without_person : (∃ s : Entity, ∃ p : Prop, Act s p) ∧ (` | —  |
| `act_occurs` | theorem | [L245](formal/Logos/HostileSemantics.lean#L245) | `theorem act_occurs : ∃ s : Entity, ∃ p : Prop, Act s p` | —  |
| `constitutive_act_holds` | theorem | [L242](formal/Logos/HostileSemantics.lean#L242) | `theorem constitutive_act_holds : ∀ (s : Entity) (p : Prop), Act s p → Subject s` | —  |
| `no_person` | theorem | [L247](formal/Logos/HostileSemantics.lean#L247) | `theorem no_person : ¬ ∃ s : Entity, Person s` | —  |
| `subject_exists` | theorem | [L246](formal/Logos/HostileSemantics.lean#L246) | `theorem subject_exists : ∃ s : Entity, Subject s` | —  |
| `subject_without_person` | theorem | [L250](formal/Logos/HostileSemantics.lean#L250) | `theorem subject_without_person : (∃ s : Entity, Subject s) ∧ ¬ (∃ s : Entity, Pe` | —  |

### `CountermodelVeridicalMeaning`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `GCdatum` | def | [L646](formal/Logos/HostileSemantics.lean#L646) | `def GCdatum (I : GenuineChoiceSignature) : Prop` | —  |
| `GenuineChoice` | def | [L651](formal/Logos/HostileSemantics.lean#L651) | `def GenuineChoice (I : GenuineChoiceSignature) : Prop` | —  |
| `GenuineChoiceSignature` | structure | [L642](formal/Logos/HostileSemantics.lean#L642) | `structure GenuineChoiceSignature where` | —  |
| `not_entails_genuine_choice` | theorem | [L660](formal/Logos/HostileSemantics.lean#L660) | `theorem not_entails_genuine_choice : ¬ (∀ I : GenuineChoiceSignature, GCdatum I ` | —  |
| `not_entails_genuine_choice_with_plurality` | theorem | [L672](formal/Logos/HostileSemantics.lean#L672) | `theorem not_entails_genuine_choice_with_plurality : ¬ (∀ I : GenuineChoiceSignat` | —  |
| `Γ_twoGCSubjects` | def | [L655](formal/Logos/HostileSemantics.lean#L655) | `def Γ_twoGCSubjects (I : GenuineChoiceSignature) : Prop` | —  |

### `CountermodelVeridicalMeaning.Single`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `A` | def | [L534](formal/Logos/HostileSemantics.lean#L534) | `def A (s : S) (p : Prop) : Prop` | —  |
| `Chooses` | def | [L536](formal/Logos/HostileSemantics.lean#L536) | `def Chooses (s : S) (p q : Prop) : Prop` | —  |
| `FreeWill` | def | [L537](formal/Logos/HostileSemantics.lean#L537) | `def FreeWill (s : S) : Prop` | —  |
| `M` | def | [L533](formal/Logos/HostileSemantics.lean#L533) | `def M (_s : S) (p : Prop) : Prop` | —  |
| `Person` | def | [L535](formal/Logos/HostileSemantics.lean#L535) | `def Person (s : S) : Prop` | —  |
| `S` | def | [L532](formal/Logos/HostileSemantics.lean#L532) | `def S : Type` | —  |
| `act_datum_holds` | theorem | [L539](formal/Logos/HostileSemantics.lean#L539) | `theorem act_datum_holds : ∃ s : S, ∃ p : Prop, A s p` | —  |
| `act_does_not_imply_genuine_choice` | theorem | [L555](formal/Logos/HostileSemantics.lean#L555) | `theorem act_does_not_imply_genuine_choice : (∃ s : S, ∃ p : Prop, A s p) ∧ ¬ (∃ ` | —  |
| `field_holds` | theorem | [L542](formal/Logos/HostileSemantics.lean#L542) | `theorem field_holds : ∃ s : S, ∃ p q : Prop, A s p ∧ Logos.Alternatives.Incompat` | —  |
| `no_genuine_choice` | theorem | [L545](formal/Logos/HostileSemantics.lean#L545) | `theorem no_genuine_choice : ¬ ∃ s : S, ∃ p q : Prop, Chooses s p q` | —  |
| `no_rejected_horn` | theorem | [L549](formal/Logos/HostileSemantics.lean#L549) | `theorem no_rejected_horn : ¬ ∃ s : S, ∃ p : Prop, A s p ∧ A s (¬ p)` | —  |

### `CountermodelVeridicalMeaning.TwoPersons`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `A` | def | [L568](formal/Logos/HostileSemantics.lean#L568) | `def A (s : S) (p : Prop) : Prop` | —  |
| `Chooses` | def | [L570](formal/Logos/HostileSemantics.lean#L570) | `def Chooses (s : S) (p q : Prop) : Prop` | —  |
| `Correct` | def | [L576](formal/Logos/HostileSemantics.lean#L576) | `def Correct (s : S) (p : Prop) : Prop` | —  |
| `Fallible` | def | [L578](formal/Logos/HostileSemantics.lean#L578) | `def Fallible (_s : S) (p : Prop) : Prop` | —  |
| `FreeWill` | def | [L571](formal/Logos/HostileSemantics.lean#L571) | `def FreeWill (s : S) : Prop` | —  |
| `Incorrect` | def | [L577](formal/Logos/HostileSemantics.lean#L577) | `def Incorrect (s : S) (p : Prop) : Prop` | —  |
| `IsFalse` | def | [L575](formal/Logos/HostileSemantics.lean#L575) | `def IsFalse (p : Prop) : Prop` | —  |
| `M` | def | [L567](formal/Logos/HostileSemantics.lean#L567) | `def M (_s : S) (p : Prop) : Prop` | —  |
| `Person` | def | [L569](formal/Logos/HostileSemantics.lean#L569) | `def Person (s : S) : Prop` | —  |
| `S` | def | [L566](formal/Logos/HostileSemantics.lean#L566) | `def S : Type` | —  |
| `T` | def | [L574](formal/Logos/HostileSemantics.lean#L574) | `def T (p : Prop) : Prop` | —  |
| `act_datum_holds` | theorem | [L580](formal/Logos/HostileSemantics.lean#L580) | `theorem act_datum_holds : ∃ s : S, ∃ p : Prop, A s p` | —  |
| `fallibility_holds` | theorem | [L606](formal/Logos/HostileSemantics.lean#L606) | `theorem fallibility_holds : ∃ (s : S) (p : Prop), Fallible s p ∧ IsFalse p` | —  |
| `full_fragment_without_genuine_choice` | theorem | [L626](formal/Logos/HostileSemantics.lean#L626) | `theorem full_fragment_without_genuine_choice : (∃ s : S, ∃ p : Prop, A s p) ∧ (∃` | —  |
| `judge_commits_holds` | theorem | [L597](formal/Logos/HostileSemantics.lean#L597) | `theorem judge_commits_holds : ∃ (s : S) (p q : Prop), A s p ∧ (Correct s p ∨ Inc` | —  |
| `no_genuine_choice` | theorem | [L613](formal/Logos/HostileSemantics.lean#L613) | `theorem no_genuine_choice : ¬ ∃ s : S, ∃ p q : Prop, Chooses s p q` | —  |
| `no_rejected_horn` | theorem | [L617](formal/Logos/HostileSemantics.lean#L617) | `theorem no_rejected_horn : ¬ ∃ s : S, ∃ p : Prop, A s p ∧ A s (¬ p)` | —  |
| `rightWrong_holds` | theorem | [L590](formal/Logos/HostileSemantics.lean#L590) | `theorem rightWrong_holds : (¬ (∀ p : Prop, ¬ T p)) ∧ (¬ (∀ p : Prop, T p))` | —  |
| `two_persons_exist` | theorem | [L583](formal/Logos/HostileSemantics.lean#L583) | `theorem two_persons_exist : ∃ s₁ s₂ : S, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂` | —  |

### `CountermodelWorldwiseTruthmaking`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `Entity` | abbrev | [L343](formal/Logos/HostileSemantics.lean#L343) | `abbrev Entity : Type` | —  |
| `ExistsAt` | def | [L345](formal/Logos/HostileSemantics.lean#L345) | `def ExistsAt (w : World) (e : Entity) : Prop` | —  |
| `Ground` | def | [L346](formal/Logos/HostileSemantics.lean#L346) | `def Ground (_e : Entity) (_φ : Unit) : Prop` | —  |
| `World` | abbrev | [L342](formal/Logos/HostileSemantics.lean#L342) | `abbrev World : Type` | —  |
| `no_uniform_ground` | theorem | [L352](formal/Logos/HostileSemantics.lean#L352) | `theorem no_uniform_ground : ¬ ∃ e : Entity, ∀ w : World, ExistsAt w e ∧ Ground e` | —  |
| `worldwise_not_entails_uniform_ground` | theorem | [L360](formal/Logos/HostileSemantics.lean#L360) | `theorem worldwise_not_entails_uniform_ground : (∀ w : World, ∃ e : Entity, Exist` | —  |
| `worldwise_truthmaking` | theorem | [L348](formal/Logos/HostileSemantics.lean#L348) | `theorem worldwise_truthmaking : ∀ w : World, ∃ e : Entity, ExistsAt w e ∧ Ground` | —  |

### `Logos.Agency`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `A` | abbrev | [L73](formal/Logos/Agency.lean#L73) | `abbrev A` | {Means, Subject}  |
| `Act` | def | [L70](formal/Logos/Agency.lean#L70) | `def Act (s : Subject) (p : Prop) : Prop` | {Means, Subject}  |
| `Agent` | def | [L53](formal/Logos/Agency.lean#L53) | `def Agent (_s : Subject) : Prop` | {Subject}  |
| `AnActualSubjectExists` | def | [L91](formal/Logos/Agency.lean#L91) | `def AnActualSubjectExists : Prop` | {Means, Subject}  |
| `Asserts` | def | [L118](formal/Logos/Agency.lean#L118) | `def Asserts (s : Subject) (p : Prop) : Prop` | {Means, Subject}  |
| `Cogito` | theorem | [L147](formal/Logos/Agency.lean#L147) | `theorem Cogito {s : Subject} {p : Prop} (h : Asserts s p) : ∃ s' : Subject, ∃ p'` | {Means, Subject} → C68 |
| `Content` | def | [L47](formal/Logos/Agency.lean#L47) | `def Content (_p : Prop) : Prop` | {}  |
| `Exists` | abbrev | [L88](formal/Logos/Agency.lean#L88) | `abbrev Exists : Subject → Prop` | {Means, Subject}  |
| `Means` | axiom | [L66](formal/Logos/Agency.lean#L66) | `axiom Means : Subject → Prop → Prop` | {Means, Subject}  |
| `NoAct` | def | [L114](formal/Logos/Agency.lean#L114) | `def NoAct : Prop` | {Means, Subject}  |
| `NoSubject` | def | [L157](formal/Logos/Agency.lean#L157) | `def NoSubject : Prop` | {Means, Subject}  |
| `NoSubjectSort` | def | [L172](formal/Logos/Agency.lean#L172) | `def NoSubjectSort : Prop` | {Subject}  |
| `Rational` | def | [L59](formal/Logos/Agency.lean#L59) | `def Rational (_s : Subject) : Prop` | {Subject}  |
| `Subject` | axiom | [L42](formal/Logos/Agency.lean#L42) | `axiom Subject : Type` | {Subject}  |
| `SubjectExists` | def | [L85](formal/Logos/Agency.lean#L85) | `def SubjectExists (s : Subject) : Prop` | {Means, Subject}  |
| `T1_subjectExists_of_act` | theorem | [L152](formal/Logos/Agency.lean#L152) | `theorem T1_subjectExists_of_act (h : ∃ s : Subject, ∃ p : Prop, Act s p) : ∃ s :` | {Means, Subject}  |
| `T2_contentExists` | theorem | [L206](formal/Logos/Agency.lean#L206) | `theorem T2_contentExists : ∃ p : Prop, Content p` | {} → C22 |
| `act_exists_of_assert` | theorem | [L127](formal/Logos/Agency.lean#L127) | `theorem act_exists_of_assert {s : Subject} {p : Prop} (h : Asserts s p) : ∃ s' :` | {Means, Subject}  |
| `act_implies_agent` | theorem | [L185](formal/Logos/Agency.lean#L185) | `theorem act_implies_agent : ∀ {s : Subject} {p : Prop}, A s p → Agent s` | {Means, Subject}  |
| `act_implies_content` | theorem | [L180](formal/Logos/Agency.lean#L180) | `theorem act_implies_content : ∀ {s : Subject} {p : Prop}, A s p → Content p` | {Means, Subject}  |
| `act_implies_exists` | abbrev | [L100](formal/Logos/Agency.lean#L100) | `abbrev act_implies_exists` | {Means, Subject}  |
| `act_implies_means` | theorem | [L197](formal/Logos/Agency.lean#L197) | `theorem act_implies_means : ∀ {s : Subject} {p : Prop}, A s p → Means s p` | {Means, Subject}  |
| `act_implies_rational` | theorem | [L191](formal/Logos/Agency.lean#L191) | `theorem act_implies_rational : ∀ {s : Subject} {p : Prop}, A s p → Rational s` | {Means, Subject}  |
| `act_of_asserting_no_act` | theorem | [L132](formal/Logos/Agency.lean#L132) | `theorem act_of_asserting_no_act (speaker : Subject) (h : Asserts speaker NoAct) ` | {Means, Subject}  |
| `act_requires_subject` | theorem | [L96](formal/Logos/Agency.lean#L96) | `theorem act_requires_subject (s : Subject) (p : Prop) (h : Act s p) : SubjectExi` | {Means, Subject}  |
| `an_actual_subject_exists_of_act` | theorem | [L109](formal/Logos/Agency.lean#L109) | `theorem an_actual_subject_exists_of_act (h : ∃ s : Subject, ∃ p : Prop, Act s p)` | {Means, Subject}  |
| `assertion_is_act` | theorem | [L123](formal/Logos/Agency.lean#L123) | `theorem assertion_is_act {s : Subject} {p : Prop} (h : Asserts s p) : Act s p` | {Means, Subject}  |
| `noCogito_selfRefutes` | theorem | [L143](formal/Logos/Agency.lean#L143) | `theorem noCogito_selfRefutes (speaker : Subject) (h : Asserts speaker NoAct) : F` | {Means, Subject} → C58 |
| `noSubjectSort_selfRefutes` | theorem | [L175](formal/Logos/Agency.lean#L175) | `theorem noSubjectSort_selfRefutes (speaker : Subject) (h : Asserts speaker NoSub` | {Means, Subject}  |
| `noSubject_performative_selfRefutes` | theorem | [L162](formal/Logos/Agency.lean#L162) | `theorem noSubject_performative_selfRefutes (speaker : Subject) (h : Asserts spea` | {Means, Subject}  |
| `noSubject_selfRefutes` | theorem | [L168](formal/Logos/Agency.lean#L168) | `theorem noSubject_selfRefutes (speaker : Subject) (h : Asserts speaker NoSubject` | {Means, Subject}  |
| `subject_exists_of_act` | theorem | [L103](formal/Logos/Agency.lean#L103) | `theorem subject_exists_of_act (h : ∃ s : Subject, ∃ p : Prop, Act s p) : ∃ s : S` | {Means, Subject}  |
| `subject_exists_of_assert` | theorem | [L137](formal/Logos/Agency.lean#L137) | `theorem subject_exists_of_assert {s : Subject} {p : Prop} (h : Asserts s p) : ∃ ` | {Means, Subject}  |

### `Logos.Alternatives`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `Incompatible` | def | [L17](formal/Logos/Alternatives.lean#L17) | `def Incompatible (p q : Prop) : Prop` | {}  |
| `T9_incompatibleAlternatives` | theorem | [L24](formal/Logos/Alternatives.lean#L24) | `theorem T9_incompatibleAlternatives : ∃ p q : Prop, Incompatible p q ∧ T p ∧ IsF` | {} → C26 |
| `incompatible_with_negation` | theorem | [L35](formal/Logos/Alternatives.lean#L35) | `theorem incompatible_with_negation {p : Prop} (hp : T p) : Incompatible p (¬ p) ` | {} → C27 |

### `Logos.Choice`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `CanChoose` | def | [L117](formal/Logos/Choice.lean#L117) | `def CanChoose (s : Subject) (p : Prop) : Prop` | {Means, Subject}  |
| `ChoiceField` | def | [L71](formal/Logos/Choice.lean#L71) | `def ChoiceField (s : Subject) (p : Prop) (q : Prop) : Prop` | {Means, Subject}  |
| `Chooses` | def | [L79](formal/Logos/Choice.lean#L79) | `def Chooses (s : Subject) (p : Prop) (q : Prop) : Prop` | {Means, Subject}  |
| `FreeWill` | def | [L140](formal/Logos/Choice.lean#L140) | `def FreeWill (s : Subject) : Prop` | {Means, Subject}  |
| `JUDGE_HAS_CHOICE_FIELD` | theorem | [L299](formal/Logos/Choice.lean#L299) | `theorem JUDGE_HAS_CHOICE_FIELD (h : ¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) : ∃ s :` | {AxTwoSubjects, Means, Subject} → C54 |
| `Meaning_I` | def | [L94](formal/Logos/Choice.lean#L94) | `def Meaning_I (p : Prop) : Prop` | {Means, Subject}  |
| `NoChoiceField` | def | [L272](formal/Logos/Choice.lean#L272) | `def NoChoiceField : Prop` | {Means, Subject}  |
| `T11_choiceField` | theorem | [L230](formal/Logos/Choice.lean#L230) | `theorem T11_choiceField (h : ∃ s : Subject, ∃ p : Prop, A s p) : ∃ s : Subject, ` | {Means, Subject} → C39 |
| `T11_choiceField_from_plurality` | theorem | [L237](formal/Logos/Choice.lean#L237) | `theorem T11_choiceField_from_plurality : ∃ s : Subject, Person s ∧ ∃ p q : Prop,` | {AxTwoSubjects, Means, Subject}  |
| `asserting_noChoiceField_is_choiceField` | theorem | [L276](formal/Logos/Choice.lean#L276) | `theorem asserting_noChoiceField_is_choiceField (speaker : Subject) (h : Logos.Ag` | {Means, Subject}  |
| `assertion_consistency` | theorem | [L342](formal/Logos/Choice.lean#L342) | `theorem assertion_consistency {s : Subject} {p : Prop} (h : Asserts s p) : ¬ Ass` | {Means, Subject}  |
| `canChoose_unfold` | theorem | [L122](formal/Logos/Choice.lean#L122) | `theorem canChoose_unfold {s : Subject} {p : Prop} : CanChoose s p ↔ ∃ q : Prop, ` | {Means, Subject, CL}  |
| `choiceField_exists` | theorem | [L259](formal/Logos/Choice.lean#L259) | `theorem choiceField_exists (h : ∃ s : Subject, ∃ p : Prop, A s p) : ∃ s : Subjec` | {Means, Subject} → C52 |
| `choiceField_exists_from_plurality` | theorem | [L266](formal/Logos/Choice.lean#L266) | `theorem choiceField_exists_from_plurality : ∃ s : Subject, ∃ p q : Prop, ChoiceF` | {AxTwoSubjects, Means, Subject}  |
| `chooses_implies_freeWill` | theorem | [L148](formal/Logos/Choice.lean#L148) | `theorem chooses_implies_freeWill {s : Subject} {p q : Prop} (h : Chooses s p q) ` | {Means, Subject}  |
| `freeWillExists_of_chooses` | theorem | [L155](formal/Logos/Choice.lean#L155) | `theorem freeWillExists_of_chooses (h : ∃ s : Subject, ∃ p q : Prop, Chooses s p ` | {Means, Subject}  |
| `freeWillExists_of_genuineChoice` | theorem | [L195](formal/Logos/Choice.lean#L195) | `theorem freeWillExists_of_genuineChoice : genuineChoice_exists → ∃ s : Subject, ` | {Means, Subject}  |
| `genuineChoice_exists` | def | [L170](formal/Logos/Choice.lean#L170) | `def genuineChoice_exists : Prop` | {Means, Subject} → F1b |
| `genuineChoice_requires_error_possibility` | theorem | [L219](formal/Logos/Choice.lean#L219) | `theorem genuineChoice_requires_error_possibility : genuineChoice_exists → ¬ (∀ s` | {Means, Subject}  |
| `incompatible_self_negation` | theorem | [L87](formal/Logos/Choice.lean#L87) | `theorem incompatible_self_negation (p : Prop) : Incompatible p (¬ p)` | {} → C50 |
| `judge_asserting_rightWrong_has_choiceField` | theorem | [L307](formal/Logos/Choice.lean#L307) | `theorem judge_asserting_rightWrong_has_choiceField (speaker : Subject) (h : Logo` | {Means, Subject}  |
| `meaning_I_needs_subject` | theorem | [L102](formal/Logos/Choice.lean#L102) | `theorem meaning_I_needs_subject {p : Prop} (h : Meaning_I p) : ∃ s : Subject, Me` | {Means, Subject}  |
| `meaning_needs_subject` | theorem | [L111](formal/Logos/Choice.lean#L111) | `theorem meaning_needs_subject {s : Subject} {p : Prop} (hm : Means s p) : ∃ t : ` | {Means, Subject} → C49 |
| `noChoiceField_contradicts_field` | theorem | [L288](formal/Logos/Choice.lean#L288) | `theorem noChoiceField_contradicts_field (hField : ∃ s : Subject, ∃ p q : Prop, C` | {Means, Subject}  |
| `noChoiceField_selfRefutes` | theorem | [L283](formal/Logos/Choice.lean#L283) | `theorem noChoiceField_selfRefutes (speaker : Subject) (h : Logos.Agency.Asserts ` | {Means, Subject} → C53 |
| `noSubject_contradicts_subject` | theorem | [L331](formal/Logos/Choice.lean#L331) | `theorem noSubject_contradicts_subject (hSubj : ∃ s : Subject, Logos.Agency.Subje` | {Means, Subject}  |
| `noSubject_selfRefutes` | theorem | [L326](formal/Logos/Choice.lean#L326) | `theorem noSubject_selfRefutes (speaker : Subject) (h : Logos.Agency.Asserts spea` | {Means, Subject} → C57 |
| `no_one_asserts_incompatible_pair` | theorem | [L353](formal/Logos/Choice.lean#L353) | `theorem no_one_asserts_incompatible_pair : ¬ ∃ s : Subject, ∃ p q : Prop, Assert` | {Means, Subject}  |
| `person_hasChoiceField` | theorem | [L250](formal/Logos/Choice.lean#L250) | `theorem person_hasChoiceField {s : Subject} (hs : Person s) : ∃ p q : Prop, Choi` | {Means, Subject} → C51 |
| `rejectedHornCoMeant` | def | [L187](formal/Logos/Choice.lean#L187) | `def rejectedHornCoMeant : Prop` | {Means, Subject}  |
| `rejectedHornCoMeant_implies_genuineChoice` | theorem | [L206](formal/Logos/Choice.lean#L206) | `theorem rejectedHornCoMeant_implies_genuineChoice : rejectedHornCoMeant → genuin` | {Means, Subject}  |
| `rightWrong_implies_someone_means` | theorem | [L319](formal/Logos/Choice.lean#L319) | `theorem rightWrong_implies_someone_means (h : ¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_` | {AxTwoSubjects, Means, Subject} → C61 |

### `Logos.ClaimMeanings`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `C19` | def | [L34](formal/Logos/ClaimMeanings.lean#L34) | `def C19 : String` | —  |
| `C59` | def | [L12](formal/Logos/ClaimMeanings.lean#L12) | `def C59 : String` | —  |
| `C64` | def | [L64](formal/Logos/ClaimMeanings.lean#L64) | `def C64 : String` | —  |
| `C65` | def | [L66](formal/Logos/ClaimMeanings.lean#L66) | `def C65 : String` | —  |
| `C66` | def | [L68](formal/Logos/ClaimMeanings.lean#L68) | `def C66 : String` | —  |
| `C67` | def | [L70](formal/Logos/ClaimMeanings.lean#L70) | `def C67 : String` | —  |
| `C69` | def | [L50](formal/Logos/ClaimMeanings.lean#L50) | `def C69 : String` | —  |
| `C70` | def | [L52](formal/Logos/ClaimMeanings.lean#L52) | `def C70 : String` | —  |
| `C71` | def | [L54](formal/Logos/ClaimMeanings.lean#L54) | `def C71 : String` | —  |
| `C72` | def | [L56](formal/Logos/ClaimMeanings.lean#L56) | `def C72 : String` | —  |
| `C73` | def | [L58](formal/Logos/ClaimMeanings.lean#L58) | `def C73 : String` | —  |
| `C75` | def | [L60](formal/Logos/ClaimMeanings.lean#L60) | `def C75 : String` | —  |
| `C76` | def | [L62](formal/Logos/ClaimMeanings.lean#L62) | `def C76 : String` | —  |
| `C78` | def | [L38](formal/Logos/ClaimMeanings.lean#L38) | `def C78 : String` | —  |
| `C79` | def | [L40](formal/Logos/ClaimMeanings.lean#L40) | `def C79 : String` | —  |
| `C80` | def | [L72](formal/Logos/ClaimMeanings.lean#L72) | `def C80 : String` | —  |
| `C81` | def | [L74](formal/Logos/ClaimMeanings.lean#L74) | `def C81 : String` | —  |
| `C82` | def | [L76](formal/Logos/ClaimMeanings.lean#L76) | `def C82 : String` | —  |
| `C87` | def | [L42](formal/Logos/ClaimMeanings.lean#L42) | `def C87 : String` | —  |
| `C88` | def | [L44](formal/Logos/ClaimMeanings.lean#L44) | `def C88 : String` | —  |
| `C89` | def | [L46](formal/Logos/ClaimMeanings.lean#L46) | `def C89 : String` | —  |
| `C90` | def | [L48](formal/Logos/ClaimMeanings.lean#L48) | `def C90 : String` | —  |
| `F1b` | def | [L14](formal/Logos/ClaimMeanings.lean#L14) | `def F1b : String` | —  |
| `F2` | def | [L16](formal/Logos/ClaimMeanings.lean#L16) | `def F2 : String` | —  |
| `F3` | def | [L18](formal/Logos/ClaimMeanings.lean#L18) | `def F3 : String` | —  |
| `F4` | def | [L20](formal/Logos/ClaimMeanings.lean#L20) | `def F4 : String` | —  |
| `F5` | def | [L22](formal/Logos/ClaimMeanings.lean#L22) | `def F5 : String` | —  |
| `F6` | def | [L24](formal/Logos/ClaimMeanings.lean#L24) | `def F6 : String` | —  |
| `F7` | def | [L26](formal/Logos/ClaimMeanings.lean#L26) | `def F7 : String` | —  |
| `F8` | def | [L28](formal/Logos/ClaimMeanings.lean#L28) | `def F8 : String` | —  |
| `F9` | def | [L30](formal/Logos/ClaimMeanings.lean#L30) | `def F9 : String` | —  |
| `Q7_2` | def | [L32](formal/Logos/ClaimMeanings.lean#L32) | `def Q7_2 : String` | —  |

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
| `AxGroundBearing` | theorem | [L79](formal/Logos/GroundPerson.lean#L79) | `theorem AxGroundBearing {e : Entity} {f : Prop} : GroundProp e f → Realizes e f` | {GroundProp, Subject}  |
| `AxPersonalGround` | axiom | [L96](formal/Logos/GroundPerson.lean#L96) | `axiom AxPersonalGround : ∀ {f : Prop}, IsPresentPersonalFeature f → ∃ e : Entity` | {AxPersonalGround, GroundProp, Means, Subject}  |
| `GroundPrincipleProp` | axiom | [L74](formal/Logos/GroundPerson.lean#L74) | `axiom GroundPrincipleProp : ∀ {f : Prop}, T f → ∃ e : Entity, GroundProp e f` | {GroundPrincipleProp, GroundProp, Subject}  |
| `GroundProp` | axiom | [L60](formal/Logos/GroundPerson.lean#L60) | `axiom GroundProp : Entity → Prop → Prop` | {GroundProp, Subject}  |
| `IsPresentPersonalFeature` | def | [L84](formal/Logos/GroundPerson.lean#L84) | `def IsPresentPersonalFeature (f : Prop) : Prop` | {Means, Subject}  |
| `Personal` | def | [L88](formal/Logos/GroundPerson.lean#L88) | `def Personal (e : Entity) : Prop` | {GroundProp, Means, Subject}  |
| `Realizes` | def | [L66](formal/Logos/GroundPerson.lean#L66) | `def Realizes (e : Entity) (f : Prop) : Prop` | {GroundProp, Subject}  |
| `T8_personalGround` | theorem | [L101](formal/Logos/GroundPerson.lean#L101) | `theorem T8_personalGround {f : Prop} (hf : IsPresentPersonalFeature f) : ∃ e : E` | {AxPersonalGround, GroundProp, Means, Subject} → C32 |
| `necessary_truth_has_necessary_grounder` | theorem | [L114](formal/Logos/GroundPerson.lean#L114) | `theorem necessary_truth_has_necessary_grounder {τ : Form} (hτ : Logos.Truthmaker` | {AxGlobalGround, Ground, Subject} → C34 |
| `present_feature_is_grounded` | theorem | [L109](formal/Logos/GroundPerson.lean#L109) | `theorem present_feature_is_grounded {f : Prop} (ht : T f) (_hf : IsPresentPerson` | {GroundPrincipleProp, GroundProp, Means, Subject} → C33 |

### `Logos.HostileSemantics`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `CoreSignature` | structure | [L63](formal/Logos/HostileSemantics.lean#L63) | `structure CoreSignature where` | —  |
| `FreeWillExistence` | def | [L86](formal/Logos/HostileSemantics.lean#L86) | `def FreeWillExistence (I : CoreSignature) : Prop` | {}  |
| `PersonExistence` | def | [L80](formal/Logos/HostileSemantics.lean#L80) | `def PersonExistence (I : CoreSignature) : Prop` | {}  |
| `TwoPersons` | def | [L83](formal/Logos/HostileSemantics.lean#L83) | `def TwoPersons (I : CoreSignature) : Prop` | {}  |
| `act_exists_of_act` | theorem | [L179](formal/Logos/HostileSemantics.lean#L179) | `theorem act_exists_of_act (hAct : ∃ s : S, ∃ p : Prop, A s p) : ∃ s : S, ∃ p : P` | {}  |
| `not_entails_content_person` | theorem | [L152](formal/Logos/HostileSemantics.lean#L152) | `theorem not_entails_content_person : ¬ (∀ (S : Type) (Means : S → Prop → Prop) (` | {}  |
| `not_entails_decoupled_freewill` | theorem | [L135](formal/Logos/HostileSemantics.lean#L135) | `theorem not_entails_decoupled_freewill : ¬ (∀ I : CoreSignature, Γ_act I ∧ (∀ s ` | {}  |
| `not_entails_person` | theorem | [L90](formal/Logos/HostileSemantics.lean#L90) | `theorem not_entails_person : ¬ (∀ I : CoreSignature, Γ_person I → PersonExistenc` | {}  |
| `not_entails_plurality` | theorem | [L106](formal/Logos/HostileSemantics.lean#L106) | `theorem not_entails_plurality : ¬ (∀ I : CoreSignature, Γ_act I ∧ (∃ s : I.Subje` | {}  |
| `subject_exists_of_act` | theorem | [L174](formal/Logos/HostileSemantics.lean#L174) | `theorem subject_exists_of_act (hAct : ∃ s : S, ∃ p : Prop, A s p) : ∃ _s : S, Tr` | {}  |
| `Γ_act` | def | [L71](formal/Logos/HostileSemantics.lean#L71) | `def Γ_act (I : CoreSignature) : Prop` | {}  |
| `Γ_means` | def | [L74](formal/Logos/HostileSemantics.lean#L74) | `def Γ_means (I : CoreSignature) : Prop` | {}  |
| `Γ_person` | def | [L77](formal/Logos/HostileSemantics.lean#L77) | `def Γ_person (I : CoreSignature) : Prop` | {}  |

### `Logos.Initiation`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `Branches` | def | [L23](formal/Logos/Initiation.lean#L23) | `def Branches {α β : Type} (R : α → β → Prop) : Prop` | {}  |
| `IsTransfer` | def | [L19](formal/Logos/Initiation.lean#L19) | `def IsTransfer {α β : Type} (R : α → β → Prop) : Prop` | {}  |
| `branches_not_transfer` | theorem | [L27](formal/Logos/Initiation.lean#L27) | `theorem branches_not_transfer {α β : Type} {R : α → β → Prop} (h : Branches R) :` | {} → C63 |

### `Logos.Love`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `AxPersonStability` | theorem | [L96](formal/Logos/Love.lean#L96) | `theorem AxPersonStability : ∀ s : Subject, Person s → NecessarySubject s` | {Means, Subject}  |
| `Lovable` | def | [L75](formal/Logos/Love.lean#L75) | `def Lovable (t : Subject) : Prop` | {Means, Subject}  |
| `Loves` | def | [L42](formal/Logos/Love.lean#L42) | `def Loves (s t : Subject) : Prop` | {Subject}  |
| `T13_someoneLovable` | theorem | [L81](formal/Logos/Love.lean#L81) | `theorem T13_someoneLovable : ∃ s t : Subject, Person s ∧ Person t ∧ s ≠ t ∧ Lova` | {AxTwoSubjects, Means, Subject} → C41 |
| `T14_content` | theorem | [L185](formal/Logos/Love.lean#L185) | `theorem T14_content : ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ Loves` | {AxTwoSubjects, Means, Subject} → C43 |
| `T14_eternalRelation` | theorem | [L150](formal/Logos/Love.lean#L150) | `theorem T14_eternalRelation : ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂` | {AxTwoSubjects, Means, Subject} → C42 |
| `T14_square` | theorem | [L175](formal/Logos/Love.lean#L175) | `theorem T14_square : □(∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ Love` | {AxTwoSubjects, Means, Subject} → C45 |
| `T14_world` | theorem | [L163](formal/Logos/Love.lean#L163) | `theorem T14_world : ∀ w, ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ Lo` | {AxTwoSubjects, Means, Subject} → C44 |
| `love_affects` | theorem | [L61](formal/Logos/Love.lean#L61) | `theorem love_affects : ∀ {s t : Subject}, Loves s t → Affects s t` | {Subject}  |
| `love_helps` | theorem | [L47](formal/Logos/Love.lean#L47) | `theorem love_helps : ∀ {s t : Subject}, Loves s t → Helps s t` | {Subject} → C86 |
| `love_not_harms` | theorem | [L54](formal/Logos/Love.lean#L54) | `theorem love_not_harms : ∀ {s t : Subject}, Loves s t → ¬ Harms s t` | {Subject}  |
| `loves_of_helps` | theorem | [L69](formal/Logos/Love.lean#L69) | `theorem loves_of_helps : ∀ {s t : Subject}, Helps s t → Loves s t` | {Subject}  |
| `necessaryPersonExists` | theorem | [L124](formal/Logos/Love.lean#L124) | `theorem necessaryPersonExists (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Act s` | {Means, Subject} → C77 |
| `necessary_entity_exists` | theorem | [L138](formal/Logos/Love.lean#L138) | `theorem necessary_entity_exists (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Act` | {Means, Subject} → C92 |
| `no_contingent_person` | theorem | [L110](formal/Logos/Love.lean#L110) | `theorem no_contingent_person : ¬ (∃ s : Subject, Person s ∧ ¬ NecessarySubject s` | {Means, Subject}  |

### `Logos.Modal`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `AxGlobalGround` | axiom | [L61](formal/Logos/Modal.lean#L61) | `axiom AxGlobalGround : ∀ (φ : Form), □ φ → ∃ e : Entity, ∀ w : World, ExistsAt w` | {AxGlobalGround, Ground, Subject}  |
| `Contingent` | def | [L50](formal/Logos/Modal.lean#L50) | `def Contingent (e : Entity) : Prop` | {Subject}  |
| `NecessaryEntity` | def | [L47](formal/Logos/Modal.lean#L47) | `def NecessaryEntity (e : Entity) : Prop` | {Subject}  |
| `T7_excludedMiddleInstance` | theorem | [L74](formal/Logos/Modal.lean#L74) | `theorem T7_excludedMiddleInstance (φ : Form) : ∃ e : Entity, NecessaryEntity e ∧` | {AxGlobalGround, Ground, Subject, CL} → C19 |
| `T7_necessaryReality` | theorem | [L68](formal/Logos/Modal.lean#L68) | `theorem T7_necessaryReality {τ : Form} (hτ : □ τ) : ∃ e : Entity, NecessaryEntit` | {AxGlobalGround, Ground, Subject} → C18 |
| `actualWorld` | def | [L44](formal/Logos/Modal.lean#L44) | `def actualWorld : World` | {}  |
| `necessary_entity_exists_of_necessary_subject` | theorem | [L109](formal/Logos/Modal.lean#L109) | `theorem necessary_entity_exists_of_necessary_subject {s : Subject} (h : Necessar` | {Subject}  |
| `noNecessaryTruthIfAllContingent` | theorem | [L80](formal/Logos/Modal.lean#L80) | `theorem noNecessaryTruthIfAllContingent : (∀ e : Entity, Contingent e) → ∀ φ : F` | {AxGlobalGround, Ground, Subject} → C20 |
| `subject_nec_entity_nec` | theorem | [L97](formal/Logos/Modal.lean#L97) | `theorem subject_nec_entity_nec (s : Subject) : NecessarySubject s → NecessaryEnt` | {Subject} → C91 |
| `subject_nec_entity_nec_iff` | theorem | [L104](formal/Logos/Modal.lean#L104) | `theorem subject_nec_entity_nec_iff (s : Subject) : NecessarySubject s ↔ Necessar` | {Subject}  |

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

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `Correct` | def | [L29](formal/Logos/Order.lean#L29) | `def Correct (s : Subject) (p : Prop) : Prop` | {Means, Subject}  |
| `Fallible` | def | [L74](formal/Logos/Order.lean#L74) | `def Fallible (_s : Subject) (p : Prop) : Prop` | {Subject}  |
| `Incorrect` | def | [L34](formal/Logos/Order.lean#L34) | `def Incorrect (s : Subject) (p : Prop) : Prop` | {Means, Subject}  |
| `NoAct` | def | [L155](formal/Logos/Order.lean#L155) | `def NoAct : Prop` | {Means, Subject}  |
| `T6_fallibility` | theorem | [L90](formal/Logos/Order.lean#L90) | `theorem T6_fallibility : ¬ (∀ s : Subject, ∀ p : Prop, Fallible s p → T p)` | {AxTwoSubjects, Means, Subject} → C28 |
| `T6_truthTranscendsWill` | theorem | [L99](formal/Logos/Order.lean#L99) | `theorem T6_truthTranscendsWill : ¬ (∀ s : Subject, ∀ p : Prop, Fallible s p ↔ T ` | {AxTwoSubjects, Means, Subject} → C29 |
| `consequence_preserves_truth` | theorem | [L150](formal/Logos/Order.lean#L150) | `theorem consequence_preserves_truth {p₁ p₂ q : Prop} (himp : p₁ → p₂ → q) (h1 : ` | {} → C31 |
| `correctness_distinct` | theorem | [L107](formal/Logos/Order.lean#L107) | `theorem correctness_distinct : ¬ (∀ s : Subject, ∀ p : Prop, Correct s p ↔ Incor` | {AxTwoSubjects, Means, Subject, CL} → C30 |
| `fallible_false` | theorem | [L82](formal/Logos/Order.lean#L82) | `theorem fallible_false : ∃ s : Subject, ∃ p : Prop, Fallible s p ∧ IsFalse p` | {AxTwoSubjects, Means, Subject}  |
| `judge_commits` | theorem | [L127](formal/Logos/Order.lean#L127) | `theorem judge_commits : ∃ s : Subject, ∃ p q : Prop, A s p ∧ (Correct s p ∨ Inco` | {AxTwoSubjects, Means, Subject, CL} → C55 |
| `judgment_implies_act` | theorem | [L173](formal/Logos/Order.lean#L173) | `theorem judgment_implies_act {s : Subject} {p : Prop} (h : Correct s p ∨ Incorre` | {Means, Subject}  |
| `judgment_implies_cogito` | theorem | [L185](formal/Logos/Order.lean#L185) | `theorem judgment_implies_cogito (h : (∃ s : Subject, ∃ p : Prop, Correct s p) ∨ ` | {Means, Subject}  |
| `judgment_of_no_act_is_incorrect` | theorem | [L166](formal/Logos/Order.lean#L166) | `theorem judgment_of_no_act_is_incorrect (s : Subject) (h : Correct s NoAct ∨ Inc` | {Means, Subject}  |
| `judgment_of_no_act_proves_act` | theorem | [L180](formal/Logos/Order.lean#L180) | `theorem judgment_of_no_act_proves_act (s : Subject) (h : Correct s NoAct ∨ Incor` | {Means, Subject} → C84 |
| `no_correct_judgment_of_no_act` | theorem | [L159](formal/Logos/Order.lean#L159) | `theorem no_correct_judgment_of_no_act (s : Subject) : ¬ Correct s NoAct` | {Means, Subject} → C83 |
| `rightDistinctWrong_implies_meaning` | theorem | [L62](formal/Logos/Order.lean#L62) | `theorem rightDistinctWrong_implies_meaning (h : (∃ s : Subject, ∃ p : Prop, Corr` | {Means, Subject}  |
| `rightWrongDistinction_implies_meaning` | theorem | [L138](formal/Logos/Order.lean#L138) | `theorem rightWrongDistinction_implies_meaning (_h : ¬ Logos.Core.N_T ∧ ¬ Logos.C` | {AxTwoSubjects, Means, Subject, CL}  |
| `rightWrong_implies_meaning` | theorem | [L46](formal/Logos/Order.lean#L46) | `theorem rightWrong_implies_meaning (h : (∃ s : Subject, ∃ p : Prop, Correct s p)` | {Means, Subject} → C62 |

### `Logos.Person`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `CarriesLogicalFeature` | def | [L86](formal/Logos/Person.lean#L86) | `def CarriesLogicalFeature (a : Prop) : Prop` | {}  |
| `CarriesPersonalFeature` | def | [L82](formal/Logos/Person.lean#L82) | `def CarriesPersonalFeature (a : Prop) : Prop` | {Means, Subject}  |
| `HasFeature` | def | [L79](formal/Logos/Person.lean#L79) | `def HasFeature (a f : Prop) : Prop` | {}  |
| `Intentional` | def | [L35](formal/Logos/Person.lean#L35) | `def Intentional (s : Subject) : Prop` | {Means, Subject}  |
| `Person` | def | [L38](formal/Logos/Person.lean#L38) | `def Person (s : Subject) : Prop` | {Means, Subject}  |
| `RationalAct` | def | [L76](formal/Logos/Person.lean#L76) | `def RationalAct (a : Prop) : Prop` | {Means, Subject}  |
| `inseparability_24b` | theorem | [L92](formal/Logos/Person.lean#L92) | `theorem inseparability_24b : ∀ a : Prop, RationalAct a → (CarriesPersonalFeature` | {Means, Subject, CL} → C25 |
| `person_exists_of_act` | theorem | [L61](formal/Logos/Person.lean#L61) | `theorem person_exists_of_act (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Act s ` | {Means, Subject}  |
| `person_exists_of_assert` | theorem | [L67](formal/Logos/Person.lean#L67) | `theorem person_exists_of_assert {s : Subject} {p : Prop} (h : Logos.Agency.Asser` | {Means, Subject}  |
| `person_of_act` | theorem | [L57](formal/Logos/Person.lean#L57) | `theorem person_of_act {s : Subject} {p : Prop} (h : Logos.Agency.Act s p) : Pers` | {Means, Subject}  |
| `person_of_subject` | theorem | [L53](formal/Logos/Person.lean#L53) | `theorem person_of_subject {s : Subject} (h : Logos.Agency.SubjectExists s) : Per` | {Means, Subject}  |

### `Logos.Plurality`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `EntityOf` | def | [L34](formal/Logos/Plurality.lean#L34) | `def EntityOf : Subject → Entity` | {Subject}  |
| `NecessarySubject` | def | [L37](formal/Logos/Plurality.lean#L37) | `def NecessarySubject (s : Subject) : Prop` | {Subject}  |
| `T12_directedPair` | theorem | [L124](formal/Logos/Plurality.lean#L124) | `theorem T12_directedPair : ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ ` | {AxTwoSubjects, Means, Subject} → C47 |
| `T12_twoPersons` | theorem | [L44](formal/Logos/Plurality.lean#L44) | `theorem T12_twoPersons : ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂` | {AxTwoSubjects, Means, Subject} → C40 |
| `T1_of_assert` | theorem | [L89](formal/Logos/Plurality.lean#L89) | `theorem T1_of_assert {s : Subject} {p : Prop} (h : Logos.Agency.Asserts s p) : ∃` | {Means, Subject}  |
| `T1_subjectExists` | theorem | [L66](formal/Logos/Plurality.lean#L66) | `theorem T1_subjectExists (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Act s p) :` | {Means, Subject} → C21 |
| `T1_subjectExists_from_plurality` | theorem | [L104](formal/Logos/Plurality.lean#L104) | `theorem T1_subjectExists_from_plurality : ∃ s : Subject, Logos.Agency.SubjectExi` | {AxTwoSubjects, Means, Subject}  |
| `T4_agentExists` | theorem | [L74](formal/Logos/Plurality.lean#L74) | `theorem T4_agentExists (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Act s p) : ∃` | {Means, Subject} → C23 |
| `T4_agentExists_from_plurality` | theorem | [L109](formal/Logos/Plurality.lean#L109) | `theorem T4_agentExists_from_plurality : ∃ s : Subject, Logos.Agency.SubjectExist` | {AxTwoSubjects, Means, Subject}  |
| `T4_of_assert` | theorem | [L94](formal/Logos/Plurality.lean#L94) | `theorem T4_of_assert {s : Subject} {p : Prop} (h : Logos.Agency.Asserts s p) : ∃` | {Means, Subject}  |
| `T5_of_assert` | theorem | [L99](formal/Logos/Plurality.lean#L99) | `theorem T5_of_assert {s : Subject} {p : Prop} (h : Logos.Agency.Asserts s p) : ∃` | {Means, Subject}  |
| `T5_personExists` | theorem | [L84](formal/Logos/Plurality.lean#L84) | `theorem T5_personExists (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Act s p) : ` | {Means, Subject} → C24 |
| `T5_personExists_from_plurality` | theorem | [L115](formal/Logos/Plurality.lean#L115) | `theorem T5_personExists_from_plurality : ∃ s : Subject, Person s` | {AxTwoSubjects, Means, Subject}  |
| `cogito_from_T12` | theorem | [L57](formal/Logos/Plurality.lean#L57) | `theorem cogito_from_T12 : ∃ s : Subject, ∃ p : Prop, Logos.Agency.A s p` | {AxTwoSubjects, Means, Subject} → C48 |
| `notAlone` | theorem | [L50](formal/Logos/Plurality.lean#L50) | `theorem notAlone : ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂` | {AxTwoSubjects, Means, Subject}  |

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
| `Entity` | inductive | [L41](formal/Logos/Truthmaker.lean#L41) | `inductive Entity : Type` | —  |
| `EntityOf` | def | [L46](formal/Logos/Truthmaker.lean#L46) | `def EntityOf (s : Subject) : Entity` | {Subject}  |
| `ExistsAt` | def | [L62](formal/Logos/Truthmaker.lean#L62) | `def ExistsAt (w : World) : Entity → Prop | Entity.ofSubject _ => True` | {Subject}  |
| `Ground` | axiom | [L55](formal/Logos/Truthmaker.lean#L55) | `axiom Ground : Entity → Form → Prop` | {Ground, Subject}  |
| `NecessarilyFalse` | def | [L74](formal/Logos/Truthmaker.lean#L74) | `def ¬◇(φ : Form) : Prop` | {}  |
| `NecessarilyTrue` | def | [L71](formal/Logos/Truthmaker.lean#L71) | `def □(φ : Form) : Prop` | {}  |
| `TrueAt` | def | [L68](formal/Logos/Truthmaker.lean#L68) | `def TrueAt (w : World) (φ : Form) : Prop` | {}  |
| `Truthmaker` | axiom | [L81](formal/Logos/Truthmaker.lean#L81) | `axiom Truthmaker : ∀ (w : World) (φ : Form), w ⊨ φ → ∃ e : Entity, ExistsAt w e ` | {Truthmaker, Ground, Subject}  |
| `groundPrinciple_atom` | theorem | [L88](formal/Logos/Truthmaker.lean#L88) | `theorem groundPrinciple_atom (w : World) (n : Nat) : w ⊨ atom n → ∃ e : Entity, ` | {Truthmaker, Ground, Subject} → C15 |
| `lawExcludedMiddle` | theorem | [L123](formal/Logos/Truthmaker.lean#L123) | `theorem lawExcludedMiddle (φ : Form) : □(φ ∨ ¬φ)` | {CL} → C16 |
| `noGround_selfRefutes` | theorem | [L95](formal/Logos/Truthmaker.lean#L95) | `theorem noGround_selfRefutes : ¬ (∃ (w : World) (n : Nat), w ⊨ atom n ∧ ¬ (∃ e :` | {Truthmaker, Ground, Subject} → C60 |
| `nonContradiction` | theorem | [L131](formal/Logos/Truthmaker.lean#L131) | `theorem nonContradiction (φ : Form) : ¬◇(φ ∧ ¬φ)` | {} → C17 |
| `sat_ground_and` | theorem | [L108](formal/Logos/Truthmaker.lean#L108) | `theorem sat_ground_and {w : World} {φ ψ : Form} : w ⊨ (φ ∧ ψ) ↔ w ⊨ φ ∧ w ⊨ ψ` | {}  |
| `sat_ground_imp` | theorem | [L116](formal/Logos/Truthmaker.lean#L116) | `theorem sat_ground_imp {w : World} {φ ψ : Form} : w ⊨ (φ → ψ) ↔ (w ⊨ φ → w ⊨ ψ)` | {}  |
| `sat_ground_not` | theorem | [L112](formal/Logos/Truthmaker.lean#L112) | `theorem sat_ground_not {w : World} {φ : Form} : w ⊨ ¬φ ↔ ¬ w ⊨ φ` | {}  |
| `sat_ground_or` | theorem | [L104](formal/Logos/Truthmaker.lean#L104) | `theorem sat_ground_or {w : World} {φ ψ : Form} : w ⊨ (φ ∨ ψ) ↔ w ⊨ φ ∨ w ⊨ ψ` | {}  |

### `Logos.Value`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `Affects` | def | [L51](formal/Logos/Value.lean#L51) | `def Affects (s t : Subject) : Prop` | {Subject}  |
| `Alone` | def | [L86](formal/Logos/Value.lean#L86) | `def Alone (s : Subject) : Prop` | {Subject}  |
| `AxPersonsAffect` | theorem | [L137](formal/Logos/Value.lean#L137) | `theorem AxPersonsAffect (s₁ s₂ : Subject) (_hs₁ : Person s₁) (_hs₂ : Person s₂) ` | {Means, Subject}  |
| `AxTwoSubjects` | axiom | [L113](formal/Logos/Value.lean#L113) | `axiom AxTwoSubjects : (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) → ∃ s₁ s₂ : Subject,` | {AxTwoSubjects, Means, Subject} → FAITH-2 |
| `Harms` | def | [L63](formal/Logos/Value.lean#L63) | `def Harms (_s _t : Subject) : Prop` | {Subject}  |
| `Helps` | def | [L57](formal/Logos/Value.lean#L57) | `def Helps (s t : Subject) : Prop` | {Subject}  |
| `OtherAffects` | def | [L83](formal/Logos/Value.lean#L83) | `def OtherAffects (s : Subject) : Prop` | {Subject}  |
| `aloneExcluded` | theorem | [L122](formal/Logos/Value.lean#L122) | `theorem aloneExcluded : ¬ ∃ s : Subject, Person s ∧ Alone s` | {AxTwoSubjects, Means, Subject} → C74 |
| `alone_no_other_affects` | theorem | [L89](formal/Logos/Value.lean#L89) | `theorem alone_no_other_affects {s : Subject} (ha : Alone s) : ¬ OtherAffects s` | {Subject}  |
| `alone_no_other_help_harm` | theorem | [L97](formal/Logos/Value.lean#L97) | `theorem alone_no_other_help_harm {s : Subject} (ha : Alone s) : (¬ ∃ t : Subject` | {Subject} → C56 |
| `harm_affects` | theorem | [L71](formal/Logos/Value.lean#L71) | `theorem harm_affects : ∀ {s t : Subject}, Harms s t → Affects s t` | {Subject}  |
| `help_affects` | theorem | [L66](formal/Logos/Value.lean#L66) | `theorem help_affects : ∀ {s t : Subject}, Helps s t → Affects s t` | {Subject}  |
| `help_not_harm` | theorem | [L78](formal/Logos/Value.lean#L78) | `theorem help_not_harm : ∀ {s t : Subject}, Helps s t → ¬ Harms s t` | {Subject} → C85 |
| `valueInterpersonal_of_split` | theorem | [L145](formal/Logos/Value.lean#L145) | `theorem valueInterpersonal_of_split : (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) → ∃ ` | {AxTwoSubjects, Means, Subject} → C46 |

### `PropositionalPersonhood`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `TripartiteVerdict` | def | [L329](formal/Logos/HostileSemantics.lean#L329) | `def TripartiteVerdict : String` | —  |

### `PropositionalPersonhood.CountermodelContentWithoutPerson`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `Means` | def | [L317](formal/Logos/HostileSemantics.lean#L317) | `def Means : S → Prop → Prop` | —  |
| `Person` | def | [L318](formal/Logos/HostileSemantics.lean#L318) | `def Person : S → Prop` | —  |
| `S` | def | [L316](formal/Logos/HostileSemantics.lean#L316) | `def S : Type` | —  |
| `content_does_not_imply_personhood` | theorem | [L324](formal/Logos/HostileSemantics.lean#L324) | `theorem content_does_not_imply_personhood : (∃ _p : Prop, True) ∧ (∀ p : Prop, ∃` | —  |
| `content_exists` | theorem | [L320](formal/Logos/HostileSemantics.lean#L320) | `theorem content_exists : ∃ _p : Prop, True` | —  |
| `every_content_meant` | theorem | [L321](formal/Logos/HostileSemantics.lean#L321) | `theorem every_content_meant (p : Prop) : ∃ s : S, Means s p` | —  |
| `no_person` | theorem | [L322](formal/Logos/HostileSemantics.lean#L322) | `theorem no_person : ¬ ∃ s : S, Person s` | —  |

### `UnitPluralityCountermodel`

| Nome | Tipo | Linha | Statement (Lógica) | Axis |
|---|---|---|---|---|
| `A` | def | [L299](formal/Logos/HostileSemantics.lean#L299) | `def A : S → Prop → Prop` | —  |
| `Person` | def | [L300](formal/Logos/HostileSemantics.lean#L300) | `def Person : S → Prop` | —  |
| `S` | def | [L298](formal/Logos/HostileSemantics.lean#L298) | `def S : Type` | —  |
| `act_occurs` | theorem | [L302](formal/Logos/HostileSemantics.lean#L302) | `theorem act_occurs : ∃ s : S, ∃ p : Prop, A s p` | —  |
| `agency_does_not_imply_plurality` | theorem | [L309](formal/Logos/HostileSemantics.lean#L309) | `theorem agency_does_not_imply_plurality : (∃ s : S, ∃ p : Prop, A s p) ∧ (∃ s : ` | —  |
| `no_plurality` | theorem | [L304](formal/Logos/HostileSemantics.lean#L304) | `theorem no_plurality : ¬ ∃ s t : S, s ≠ t` | —  |
| `person_exists` | theorem | [L303](formal/Logos/HostileSemantics.lean#L303) | `theorem person_exists : ∃ s : S, Person s` | —  |

</details>

---
