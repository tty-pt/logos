# Tratado de Auditoria Ontológica: Incompletude Explicativa da Totalidade e a Necessidade da Fonte Pessoal Livre

**Autor:** Auditor de Lógica Formal & Arquitecto Ontológico  
**Data:** 2026-10-08  
**Contexto Metateórico:** Análise atemporal de sistemas fechados de determinação e convergência com os dados formais de `best.lean` e `OntologicalIncompletenessTheorem.lean`.

---

## Introdução: O Modelo Atemporal de Determinação

Consideramos um sistema fechado de determinações $S$. Neste enquadramento, **o tempo não existe**:
- As relações não são sucessões cronológicas entre um "antes" e um "depois".
- A dependência explicativa é puramente **estrutural, ontológica e constitutiva**.
- A necessidade e a contingência distribuem-se de forma simétrica por toda a rede relacional.
- As regras de $S$ governam exaustivamente a relação entre os seus nós internos.

Assume-se o **Axioma da Falha Explicativa**:
> *Uma cadeia ou rede de determinações (finita, infinita ou circular) não pode explicar a sua própria determinação global. A mecânica interna do sistema não contém a razão suficiente para a instanciação da totalidade do sistema.*

A partir deste modelo, executamos as três tarefas analíticas requeridas.

---

## 1. Deconstrução da Totalidade: O Colapso do Princípio de Hume-Edwards

### 1.1 A Falácia da Composição Explicativa
David Hume (Diálogos sobre a Religião Natural, Parte IX) e Paul Edwards propuseram o célebre princípio segundo o qual, se explicarmos cada elemento individual de uma colecção por referência a outro elemento, a totalidade da colecção está ipso facto explicada.

**Por que razão esta tese é formalmente inválida?**
Seja o sistema $S = \{x_i\}_{i \in I}$. Para cada nó $x_i \in S$, a regra interna do sistema fornece uma justificação estritamente **condicional**:
$$E(x_i \mid \text{Determiners}(x_i)) = \text{"Dado que os nós determinantes de } x_i \text{ obtêm com determinada configuração, } x_i \text{ obtém."}$$

Se considerarmos uma cadeia circular fechada (um anel de dependência mútua):
$$x_1 \longrightarrow x_2 \longrightarrow \dots \longrightarrow x_n \longrightarrow x_1$$
a conjunção das regras internas estabelece uma equivalência lógica entre as condições de instanciação:
$$P(x_1) \iff P(x_2) \iff \dots \iff P(x_n)$$

Esta estrutura prova a **coerência interna relacional** dos nós, mas **nada diz sobre a sua instanciação factual**:
- O conjunto de fórmulas $\{P(x_i) \to P(x_{i+1})\}$ é identicamente satisfeito se **todos os $P(x_i)$ forem FALSOS** (isto é, se nada existir em absoluto).
- É igualmente satisfeito por um número indefinido de sistemas alternativos incompatíveis $S', S'', \dots$.

Explicar por que a parte $A$ se segue da parte $B$ é apenas explicar a **transição interna**, pressupondo a existência do sistema. A questão ontológica fundamental não é *"como se articulam as partes de $S$ entre si?"*, mas:
$$\text{Por que razão existe o sistema } S \text{ (com todos os seus nós e a sua regra) em vez do nada ou de outro sistema } S'?$$
A resposta a esta questão de segunda ordem não pode ser fornecida pela soma das relações de primeira ordem.

### 1.2 O Bloqueio Teórico-Conjuntista e a Irreflexividade Ontológica
Pode o fundamento da existência de $S$ ser um elemento $g \in S$?

Na teoria axiomática de conjuntos (ZFC), o **Axioma da Fundação (Regularidade)**:
$$\forall X (X \neq \emptyset \implies \exists Y \in X (Y \cap X = \emptyset))$$
exclui que um conjunto pertença a si mesmo ($X \notin X$) e interdita ciclos de pertença ($x_1 \in x_2 \in \dots \in x_1$).

No domínio da fundamentação ontológica estrita (*metaphysical grounding*), a prioridade constitutiva $\prec$ é estritamente **irreflexiva** ($x \not\prec x$) e **assimétrica** ($x \prec y \implies y \not\prec x$).
Ora:
1. Sendo $g \in S$, $g$ é um constituinte de $S$. A existência ontológica do todo $S$ pressupõe constitutivamente a existência de cada uma das suas partes:
   $$g \prec S$$
2. Se $g$ fosse a razão suficiente da instanciação global de $S$, a existência de $S$ dependeria explicativamente de $g$:
   $$S \prec g$$
3. Por transitividade da prioridade ontológica:
   $$g \prec g$$
O que constitui uma **petição de princípio ontológica** directa e viola a irreflexividade da determinação.

### 1.3 As Três Topologias Internas e a Falha de Suficiência Contrastiva
No módulo `OntologicalIncompletenessTheorem.lean`, demonstramos no kernel de Lean que a determinação interna falha categoricamente em qualquer das três topologias possíveis:

1. **Caso 1 (Ciclos Fechados):**
   Um ciclo de dependências mútuas ($a \prec \dots \prec a$) exige que um elemento seja anterior a si mesmo, violando a irreflexividade da prioridade ontológica estrita:
   ```lean
   theorem closed_cycle_violates_ontological_priority
       (D : DeterminationSystem.{u}) (a : D.Node)
       (hCycle : DeterminesAncestrally D.Determines a a) : False
   ```
2. **Caso 2 (Regressão Infinita sem Ponto de Paragem):**
   Num regresso infinito onde todo o nó tem um determinante interno prévio, as regras condicionais são satisfeitas pela vacuidade universal (`fun _ => False`), e a cadeia falha a boa fundamentação no sentido do fundamento:
   ```lean
   theorem infinite_regress_conditional_rules_satisfied_by_vacuity
       (S : InfiniteRegressSystem.{u}) :
       ConditionalDeterminationTransfer S (fun _ => False)

   theorem infinite_regress_cannot_self_ground
       (S : InfiniteRegressSystem.{u}) :
       ¬ WellFounded (fun a b => S.Determines a b)
   ```
   *Distinção Epistemológica:* O teorema `infinite_regress_cannot_self_ground` demonstra estritamente a propriedade formal de que uma relação com determinadores prévios em todos os nós não é bem-fundada (`¬ WellFounded`). A conclusão de que tal regresso não constitui uma explicação última da instanciação concreta global é uma conclusão filosófica substantiva: apoia-se no Teorema 2A (falácia de Hume-Edwards / vacuidade) e no PSR cosmológico, e não decorre apenas da não-boa-fundamentação formal. Analogamente, o Teorema Mestre assume `prior_wf : ∀ Ext, WellFounded (ConstitutivePriority Ext)` como hipótese estrutural necessária da ordem ontológica para derivar a irreflexividade das dependências.

3. **Caso 3 (Cadeia com Limite Interno — Teorema da Raiz Ancestral):**
   Para qualquer nó $x$ de um sistema bem fundado, existe uma fonte interna terminal $a$ (`IsInternalBruteFact D a` / `UltimateInternalSource D a`) que determina ancestralmente $x$ (ou coincide com $x$):
   ```lean
   theorem node_has_ancestral_ultimate_source
       (D : DeterminationSystem.{u}) (x : D.Node) :
       ∃ a : D.Node, IsInternalBruteFact D a ∧ (a = x ∨ DeterminesAncestrally D.Determines a x)
   ```
   Em todo o sistema bem fundado não-vazio, existe necessariamente pelo menos uma fronteira interna não determinada internamente (derivado directamente como corolário):
   ```lean
   theorem closed_system_has_unexplained_boundary
       (D : DeterminationSystem.{u}) (hNonempty : Nonempty D.Node) :
       ∃ a : D.Node, IsInternalBruteFact D a
   ```
4. **Compossibilidade das Regras Internas com Configurações Divergentes (`internal_rules_fail_contrastive_distinction` / `internal_rules_compossible_with_divergent_configurations`):**
   Num sistema concreto unificado (`ConcreteSystem`), a satisfação das regras relacionais internas de determinação (`InternalRulesPreserved S`) é formalmente compossível em mundos acessíveis com configurações globais divergentes. O teorema demonstra que existe um predicado relacional interno satisfeito identicamente em ambos os mundos apesar da divergência de configuração:
   ```lean
   theorem internal_rules_fail_contrastive_distinction
       (S : ConcreteSystem.{u}) (w_alt : S.World)
       (hActualRules : InternalRulesPreserved S S.actualWorld)
       (hAltRules : InternalRulesPreserved S w_alt)
       (hDiffCfg : S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) :
       ∃ R : S.World → Prop, R S.actualWorld ∧ R w_alt ∧
         (S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld)
   ```
   Isto atesta que a mera conformidade a regras relacionais internas é compatível com múltiplos estados globais divergentes e não serve, por si só, de diferenciador contrastivo isolado. A transcendência do fundamento ($T \notin S$) é deduzida separadamente pela refutação da circularidade constitutiva (`candidate_ground_must_be_structurally_external`, Teorema 3F).

---

## 2. O Impasse Binário: Facto Bruto vs Fundamento Transcendente

Dado que as regras internas de $S$ não contêm nem podem conter a razão suficiente da sua instanciação global, abrem-se analiticamente apenas duas saídas:

```
                      [ Instanciação Global de S ]
                                   │
                 ┌─────────────────┴─────────────────┐
                 ▼                                   ▼
        [ Saída 1: Facto Bruto ]           [ Saída 2: Fundamento Transcendente T ]
     (Abandono do PSR / Absurdo)           (Aseidade Necessária + Liberdade Agencial)
```

### 2.1 Saída 1: O Facto Bruto (Arbitrariedade e Colapso Epistémico)
A primeira opção consiste em declarar que a totalidade de $S$ simplesmente existe, sem qualquer razão, fundamento ou explicação.

**Consequências Analíticas:**
1. **Ruptura do Princípio de Razão Suficiente (PSR):**
   O PSR postula que para todo o facto contingente existe uma razão suficiente pela qual ele é assim e não de outro modo. Aceitar um Facto Bruto na totalidade é admitir que o fundamento último do real é a **ausência de razão**.
2. **A Falácia do Táxi Epistémico:**
   Se uma totalidade incomensuravelmente vasta e estruturada como $S$ pode existir como um facto bruto e arbitrário, a exigência de explicação racional a nível local perde toda a justificação normativa. Se o universo enquanto um todo pode surgir ou obter sem qualquer razão, torna-se arbitrário e incoerente exigir que fenómenos internos tenham razões suficientes. A racionalidade científica e lógica desmorona-se.

### 2.2 Saída 2: O Fundamento Transcendente $T \notin S$
Para fundamentar $S$ sem violar a irreflexividade da determinação, o explicador tem de pertencer a uma categoria ontológica exterior ao sistema:
$$T \notin S, \quad T \longrightarrow S$$

Para que $T$ estanque definitivamente a regressão explicativa (evitando que se pergunte *"por que existe $T$?"* e se gere um sistema mais vasto $S \cup \{T\}$), $T$ tem de possuir duas propriedades indispensáveis:

#### Propriedade A: Aseidade (Existência Necessária)
$T$ não pode ser contingente. Se fosse contingente, exigiria um fundamento anterior $T'$, reproduzindo o problema ad infinitum. Logo, $T$ tem de existir necessariamente em todos os mundos possíveis: a sua essência implica a sua existência (*ens a se*).

#### Propriedade B: Vontade Livre e Pessoal (A Conexão com `best.lean`)
Aqui reside o ponto mais profundo da ontologia formal:
**Como pode um fundamento necessário $T$ originar um sistema $S$ que é contingente?**

- **Se $T$ for um princípio impessoal e mecanicista:**
  Um princípio impessoal actua necessariamente de acordo com a sua natureza fixa. Não possui faculdade judicativa, desejo ou capacidade de escolha. Logo, a sua emanação causal/ontológica é necessária:
  $$\square T \land \square(T \to S) \implies \square S$$
  Isto implicaria que o sistema $S$ e todos os seus nós seriam **metafisicamente necessários**!
- **Mas os dados formais de `best.lean` refutam categoricamente a necessidade de $S$:**
  Em `best.lean`, a existência concreta desta demonstração matemática instancia a estrutura `JudgmentDeterminationChain C s w p`. Demonstra-se que o acto de juízo é sensível a alternativas polares sob o mesmo passado completo (`NormativelySensitive C s w p`), e que existe um mundo acessível onde o sujeito suspende o juízo em vez de assentir (`LibertarianFreeChoiceAt C s w p`), culminando no teorema mestre:
  ```lean
  theorem proof_exists_implies_existence_of_free_subject (h : ProofExists C) :
    ∃ s : Subject, FreeSubject C s
  ```
  Logo, $S$ **é irredutivelmente contingente**.
- **Se $T$ for impessoal e indeterminista (aleatório):**
  Uma emanação não-necessitante puramente impessoal é cega e desprovida de razão; a selecção de $S$ sobre $S'$ seria um puro acaso, colapsando de imediato na **Saída 1 (Facto Bruto)**.

**Conclusão Dedutiva Inescapável:**
A única forma ontológica de compatibilizar a necessidade de $T$ com a contingência de $S$ sem cair em fatalismo necessitarista nem em facto bruto é conceber $T$ como um **Agente Pessoal Dotado de Liberdade**:
1. Dotado de **Intelecto** para conceber a pluralidade de mundos/sistemas contingentes possíveis.
2. Dotado de **Vontade / Liberdade** para actualizar $S$ por razões intencionais/teleológicas, sem ser forçado mecanicistamente por uma causa antecedente.

> **O Fundamento Transcendente $T$ é necessariamente uma Fonte Pessoal Necessária e Livre.**

---

## 3. Síntese ou Falsificação: A Lei da Incompletude Explicativa Absoluta

Pode um sistema atemporal ser autocriado ou auto-justificado sem petição de princípio nem transcendência?

### 3.1 Exame de Modelos Matemáticos Candidatos
1. **Semântica de Pontos Fixos ($S = f(S)$):**
   Na teoria de domínios de Scott ou no Teorema de Ponto Fixo de Banach, equações recursivas admitem soluções formais $x = f(x)$.
   *Objecção:* A existência de uma solução matemática no interior de uma teoria prova apenas a auto-consistência estrutural de uma definição abstracta. **Não explica por que razão o universo físico ou concreto instancia essa solução.** A existência de um modelo formal não se confunde com a razão suficiente da sua instanciação ôntica factual.
2. **Teoria de Conjuntos Não-Bem-Fundados (Axioma Anti-Fundação de Aczel - AFA):**
   Em AFA, admitem-se conjuntos que contêm a si mesmos: $\Omega = \{\Omega\}$.
   *Objecção:* Um átomo de Quine $\Omega = \{\Omega\}$ apenas formaliza um ciclo puro de inclusão. Em termos de razão suficiente, $\Omega$ existe porque $\Omega$ existe. Trata-se da formalização matemática da **tautologia ontológica** (petição de princípio explícita). Não fornece explicação de por que $\Omega$ é actual.
3. **Universos de Deutsch-Politzer (Curvas Temporais Fechadas):**
   Modelos de relatividade geral com curvas temporais fechadas tipo-tempo (CTCs) modelam circuitos causais fechados.
   *Objecção:* Toda a curva fechada forma um bloco quadridimensional global cuja presença no espaço de soluções cosmológicas é, ela própria, contingente e sem explicação interna.

### 3.1.1 Auditoria das 9 Definições e Análise do Contra-Modelo

Em conformidade com a auditoria obrigatória requerida para o fecho formal do argumento ontológico, analisaram-se as 9 definições estruturais do modelo:

1. **`ImpersonalIntrinsicInvariancePrinciple` $\to$ `ExplanatorySymmetryPrinciple`:**
   - *Assinatura:* `∀ e, T.ground = external e → IsImpersonal S T → NatureInvariant S T → ¬ NecessitatingMode S T → GuidedByJustificationMode S T → ConstitutivePriority T.ExtEntity CandidateOnticItem.condition (CandidateOnticItem.candidate e)`
   - *Estatuto:* Axioma de ponte metafísica explícito (`Tag: META`). Na versão 8, esta asserção era postulada sem fundamentação leibniziana transparente. Foi reformulada com o seu fundamento ontológico rigoroso: características intrínsecas estritamente idênticas entre mundos contingentes acessíveis não podem contrastivamente quebrar a indiferença explicativa sem necessitar rigidamente o resultado; logo, qualquer justificação contrastiva requer uma condição explicativa extrínseca no domínio ôntico.
2. **`IndependentConditionTransfersUltimateGround` $\to$ `ExplanatoryUltimacyRequirement`:**
   - *Assinatura:* `∀ T, T.GroundsConcreteActuality T.ground S.actualWorld → IsUltimateGround S T ConstitutivePriority`
   - *Estatuto:* Princípio de ultimidade explicativa do PSR (`Tag: META`). Substitui o axioma bruto que forçava a contradição por estipulação.
3. **`IsUltimateGround`:**
   - *Assinatura:* `T.GroundsConcreteActuality T.ground S.actualWorld ∧ ∀ e, T.ground = external e → ¬ IndependentConditionMode (ConstitutivePriority T.ExtEntity) e`
   - *Estatuto:* Definição substantiva que desacopla a mera instanciação factual (`GroundsConcreteActuality`) da suficiência explicativa última (ausência de condicionamento exterior independente). Permite a demonstração de `independent_condition_contradicts_ultimacy` com **0 axiomas**.
4. **`NatureInvariant`:**
   - *Assinatura:* `∀ w, S.Accessible S.actualWorld w → T.EssenceOf T.ground w = T.EssenceOf T.ground S.actualWorld`
   - *Estatuto:* Definição rigorosa de invariância modal da essência e faculdades do fundamento entre mundos acessíveis.
5. **`GuidedByJustificationMode`:**
   - *Assinatura:* `∀ w_alt, S.Accessible S.actualWorld w_alt → (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) → T.ProvidesContrastiveJustification T.ground S.actualWorld w_alt`
   - *Estatuto:* Modo substantivo onde o fundamento fornece justificação contrastiva para todas as alternativas divergentes acessíveis.
6. **`ProvidesContrastiveJustification`:**
   - *Assinatura:* `GroundIdentity S.Node ExtEntity → S.World → S.World → Prop`
   - *Análise do Contra-Modelo:* Sob a assinatura não-constrangida de `CandidateGround`, este predicado é um campo livre. Sem o princípio de simetria explicativa, é possível construir um **contra-modelo minimal** onde:
     - $T$ existe em todos os mundos e tem essência invariante $\langle 1, 0 \rangle$;
     - $T$ é impessoal (`ApprehendsAlternative` é falso para todo o $w$);
     - $S$ é contingente (configuração de $w_{alt}$ diverge da actual);
     - $T$ não necessita rigidamente $S$;
     - **E $T.\text{ProvidesContrastiveJustification}$ é atribuído como `True` por mera estipulação gratuita**, sem qualquer condição extrínseca $C$ e sem circularidade!
     Este contra-modelo demonstra com rigor por que razão `ProvidesContrastiveJustification` não pode ser tomado no vácuo: a justificação contrastiva requer uma base explicativa real, exigindo o Princípio da Simetria Explicativa (`ExplanatorySymmetryPrinciple`, `Tag: META`) para afastar o contra-modelo e deduzir a necessidade de uma condição extrínseca.
7. **`ReasonsFavor`:**
   - *Assinatura:* `GroundIdentity S.Node ExtEntity → S.World → S.World → Prop`
   - *Estatuto:* Relação de teleologia agencial onde razões favorecem um mundo sobre outro.
8. **`ApprehendsAlternative`:**
   - *Assinatura:* `GroundIdentity S.Node ExtEntity → S.World → Prop`
   - *Alinhamento de Quantificadores:* O predicado `IsPersonalAgent` foi rigorosamente ajustado para quantificar sobre as alternativas acessíveis divergentes (`¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld`), garantindo correspondência estrita com a premissa de `GuidedByJustificationMode`.
9. **`ChoosesOutcomeAt`:**
   - *Assinatura:* `GroundIdentity S.Node ExtEntity → S.World → Option (S.Node → Bool) → Prop`
   - *Estatuto:* Acto volitivo positivo de selecção de uma configuração específica de mundos.

### 3.1.2 A Semântica da Explicação Contrastiva e o Fundamento Independente do ExplanatorySymmetryPrinciple

Para além da mecânica dedutiva do kernel, o fecho filosófico do argumento exige fundamentar por que razão o `ExplanatorySymmetryPrinciple` (`Tag: META`) é uma premissa metafísica inescapável sob o Princípio da Razão Suficiente.

#### 1. A Estrutura Lógica da Pergunta Contrastiva
Na teoria da explicação (van Fraassen 1980, Peter Lipton 2004), uma explicação não responde apenas à pergunta conjuntural *"Por que razão o facto $P$ obteve?"*, mas à pergunta contrastiva profunda:
$$\text{Por que razão } P \text{ obteve em vez de } Q? \quad (P \text{ rather than } Q)$$
onde $Q$ é uma alternativa contrafactual genuinamente acessível (*foil*).

A **Condição de Diferença de Lipton** (*Difference Condition*) estabelece que:
> *Para explicar contrastivamente por que $P$ obteve em vez de $Q$, é necessário apontar um factor explicativo que diferencie $P$ de $Q$ — isto é, um factor presente/activo nas condições de $P$ que não esteja identicamente presente/activo nas condições de $Q$.*

#### 2. A Indiscernibilidade Intrínseca do Fundamento Impessoal
Consideremos o candidato a fundamento $T$ sob a hipótese impessoal:
1. $T$ existe necessariamente no mundo actual $w_{act}$ (onde a configuração concreta contingente é $P$) e no mundo contrafactual acessível $w_{alt}$ (onde a configuração é $Q \neq P$).
2. A sua essência, faculdades e leis internas são estritamente invariantes entre mundos (`NatureInvariant`):
   $$\text{EssenceOf } T \ w_{act} = \text{EssenceOf } T \ w_{alt}$$
3. Sendo impessoal (`IsImpersonal`), $T$ carece de intelecto para conceber $Q$ contrafactualmente (`¬ ApprehendsAlternative`) e de vontade com razões para preferir $P$ a $Q$ (`¬ ReasonsFavor`).

Desta caracterização decorre que **o conjunto de todos os factos intrínsecos sobre $T$ em $w_{act}$ é estritamente indiscernível do conjunto de factos intrínsecos sobre $T$ em $w_{alt}$**.

#### 3. A Quebra de Simetria e o Princípio Independente
Se se afirmasse que a essência intrínseca de $T$ explica por que razão $P$ ocorreu em vez de $Q$, colidir-se-ia com o **Princípio da Simetria de Leibniz** (o Princípio da Identidade dos Indiscerníveis aplicado à Razão Suficiente):
- Sendo o estado intrínseco de $T$ perfeitamente simétrico e compatível tanto com $P$ como com $Q$, se ele fosse suficiente para justificar $P$ em vez de $Q$, explicaria com igual força e razão por que razão $Q$ ocorreria em vez de $P$.
- Como a justificação contrastiva é uma relação estritamente assimétrica (a razão que explica $P$ em vez de $Q$ não pode ser identicamente a razão que explica $Q$ em vez de $P$), invocar condições perfeitamente simétricas para justificar um resultado assimétrico é postular um **efeito sem causa diferenciadora**.

**Identificação Honesta do Compromisso Metafísico:**
O `ExplanatorySymmetryPrinciple` assenta no **Princípio da Razão Suficiente Contrastivo (PSR Contrastivo)**:
> *Uma pura simetria de condições intrínsecas não pode ser a razão suficiente de uma assimetria factual de resultados sem os necessitar rigidamente.*

Se o PSR for abandonado, a ocorrência de $P$ sobre $Q$ sob um $T$ neutro é um **puro facto bruto irracional** (acaso absoluto). Mas se o PSR for afirmado (como estipulado no ponto de partida do argumento, `GeneralContrastivePSR`), **uma explicação contrastiva puramente intrínseca é uma impossibilidade ontológica**. Logo, qualquer justificação contrastiva fornecida por $T$ tem necessariamente de apelar a uma condição extrínseca no domínio ôntico ($C \prec T$ ou $S \prec T$).

---

### 3.1.3 A Distinção Ontológica entre a Inexistência de Explicação Independente e a Mera Ausência de Relação de Prioridade

Um dos pontos mais críticos para a maturidade filosófica do argumento é distinguir com clareza analítica dois conceitos frequentemente confundidos na modelação relacional:

#### 1. A Mera Ausência de uma Relação de Prioridade ($\neg(C \prec T)$)
Na teoria formal de ordens bem-fundadas, a asserção:
$$\neg \exists C, \ C \prec T$$
é uma **propriedade puramente negativa**. Ela assevera apenas que não existe nenhum nó anterior a $T$ na ordem constitutiva.

Contudo, a ausência de uma aresta de prioridade **não confere auto-suficiência inteligível**:
- Um **facto bruto arbitrário** (um evento que surge do nada sem causa) satisfaz $\neg \exists C, C \prec T$;
- Uma **flutuação quântica ontologicamente indeterminista** num vazio metafísico satisfaz $\neg \exists C, C \prec T$;
- O **primeiro elemento cego** de uma cadeia mecânica satisfaz $\neg \exists C, C \prec T$.

Dizer que um fundamento impessoal não tem antecedentes exteriores demonstra apenas que ele não é causado por terceiros; **não demonstra que a sua determinação concreta possui razão de ser interna**. Se a sua natureza intrínseca é neutra e invariante face a $P$ e $Q$, a ausência de condicionamento exterior não o torna auto-explicativo — transforma a selecção de $P$ sobre $Q$ num **facto bruto contingente inexplicado**.

Portanto: **a mera ausência de uma relação formal de prioridade não equivale a auto-suficiência explicativa contrastiva.**

#### 2. A Inexistência de uma Explicação Independente (A Auto-Suficiência Positiva)
A verdadeira "inexistência de uma explicação independente" requerida pelo PSR é a **Suficiência Explicativa Positiva**:
> $T$ contém em si mesmo a razão positiva e suficiente da actualização de $P$ em vez de $Q$, de modo que a explicação da contingência cósmica termina verdadeiramente em $T$ sem deferir a dívida explicativa para fatores externos.

Como pode um fundamento ser internamente auto-suficiente na selecção de um contingente sem o necessitar rigidamente e sem depender de condições externas?

- **Num fundamento Impessoal:** É **impossível**.
  Se for necessitante, destrói a contingência (necessitarismo). Se for não-necessitante, a ausência de condições externas deixa a quebra de simetria desprovida de razão (facto bruto).
- **Num fundamento Pessoal (Agente Livre):** É **ontologicamente inteligível e positivo**.
  Um agente pessoal possui **Intelecto** (a faculdade de conceber internamente a representação mental contrafactual de $Q$ antes e independentemente da sua instanciação física) e **Vontade Teleológica** (a faculdade de agir por motivos, valores e razões que favorecem $P$ sobre $Q$).
  A razão pela qual $P$ obteve em vez de $Q$ é a **intenção do agente**. Esta razão é interna, teleológica e inteligível, sem necessitar mecanicamente o agente e sem exigir um determinante exterior prévio ($C \prec T$).

---

### 3.1.4 Quadro Sinóptico Comparativo das Opções Ontológicas

| Hipótese Ontológica | Relação de Prioridade Externa | Estatuto Explicativo da Contingência ($P$ em vez de $Q$) | Veredicto Lógico-Metafísico |
| :--- | :--- | :--- | :--- |
| **1. Necessitarismo Spinoziano** | Ausente ($\neg(C \prec T)$) | $Q$ é impossível; $P$ é metafisicamente necessário | **FALHA:** Destrói a contingência genuína da realidade (`necessary_impersonal_ground_contradicts_contingency`). |
| **2. Impessoal sem Condição Exterior** | Ausente ($\neg(C \prec T)$) | Não há razão; $P$ ocorre por mero acaso arbitrário | **FALHA:** A mera ausência de prioridade não é explicação; colide com o PSR Contrastivo (`unjustified_alternative_fails_contrastive_at`). |
| **3. Impessoal Consequente-Dependente** | Círculo ontológico: $T \prec S \prec C \prec T$ | $T$ determina $S$ porque $S$ já determinou a condição de $T$ | **FALHA:** Viciosa circularidade explicativa que viola a irreflexividade da prioridade bem-fundada (`candidate_consequence_circularity_refutation`, **0 axiomas**). |
| **4. Impessoal com Condição Independente** | Intermediário: $C \prec T \prec S$ ($\neg(S \prec C)$) | A determinação de $T$ é explicada por um terceiro factor $C$ | **FALHA:** $T$ é mero elo intermediário e não o fundamento último; a dívida do PSR transfere-se para $C$. |
| **5. Fonte Pessoal Livre (Logos / Teísmo Clássico)** | Ausente de forçamento mecanicista | $T$ escolhe $P$ intencionalmente por razões, apreendendo $Q$ | **VÁLIDO:** A razão é interna, positiva e teleológica, satisfazendo o PSR sem necessitação mecânica e sem circularidade. |

### 3.2 Enunciado e Demonstração da Lei de Incompletude Ontológica e o Fecho da Circularidade
Formalizado em `OntologicalIncompletenessTheorem.lean` e verificado pelo kernel de Lean 4 sem qualquer hipótese artificial ou axioma substantivo:

```lean
/-- TEOREMA 1 (Ciclos Fechados Violam a Prioridade Ontológica):
Um ciclo fechado de qualquer comprimento finito (a ≺ ... ≺ a) exige que um nó seja
anterior a si mesmo, violando a irreflexividade da prioridade ontológica estrita.
(0 axiomas). -/
theorem closed_cycle_violates_ontological_priority
    (D : DeterminationSystem.{u})
    (a : D.Node)
    (hCycle : DeterminesAncestrally D.Determines a a) :
    False

/-- TEOREMA 1B (Impossibilidade de Auto-Determinação de Nós Internos):
Um nó interno não pode determinar-se a si mesmo sem violar a irreflexividade da prioridade.
(0 axiomas). -/
theorem internal_node_cannot_self_determine
    (D : DeterminationSystem.{u})
    (n : D.Node)
    (hSelfDet : D.Determines n n) :
    False

/-- TEOREMA 2A (Falácia de Hume-Edwards — Regras Condicionais Satisfeitas pelo Nada):
As regras internas condicionais de determinação num regresso infinito são identicamente
satisfeitas pelo vazio universal (fun _ => False). Não explicam a instanciação global.
(0 axiomas). -/
theorem infinite_regress_conditional_rules_satisfied_by_vacuity
    (S : InfiniteRegressSystem.{u}) :
    ConditionalDeterminationTransfer S (fun _ => False)

/-- TEOREMA 2B (Regresso Infinito Falha a Boa Fundamentação):
Um regresso infinito de determinantes internos não é bem fundado na direcção do fundamento.
(0 axiomas). -/
theorem infinite_regress_cannot_self_ground
    (S : InfiniteRegressSystem.{u}) :
    ¬ WellFounded (fun a b => S.Determines a b)

/-- TEOREMA 3B (Existência de Limite Interno Inexplicado):
Todo o sistema bem fundado não-vazio contém pelo menos um elemento sem determinante interno.
Ausência de fundamento interno NÃO é ausência absoluta de fundamento: impõe um fundamento exterior.
(Axiomas: [propext, Classical.choice, Quot.sound]). -/
theorem closed_system_has_unexplained_boundary
    (D : DeterminationSystem.{u})
    (hNonempty : Nonempty D.Node) :
    ∃ a : D.Node, IsInternalBruteFact D a

/-- TEOREMA 3D (Compossibilidade de Regras Internas com Configurações Divergentes):
Demonstra formalmente que a satisfação de regras internas relacionais é compossível
em mundos com configurações globais divergentes. Não demonstra, por si só, a impossibilidade
de qualquer explicação contrastiva interna, mas exibe que a mera conformidade relacional é invariante
entre os mundos e não funciona como diferenciador isolado.
(0 axiomas). -/
theorem internal_rules_fail_contrastive_distinction
    (S : ConcreteSystem.{u})
    (w_alt : S.World)
    (hActualRules : InternalRulesPreserved S S.actualWorld)
    (hAltRules : InternalRulesPreserved S w_alt)
    (hDiffCfg : S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) :
    ∃ R : S.World → Prop, R S.actualWorld ∧ R w_alt ∧ (S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld)

/-- TEOREMA 3C (Refutação da Circularidade Constitutiva de Nó Interno):
Se um nó interno n constitui a totalidade (ConstitutivePriority (OnticDomain.node n) OnticDomain.totality)
e a totalidade dependesse de n (ConstitutivePriority OnticDomain.totality (OnticDomain.node n)),
então sob prioridade transitiva bem-fundada, n seria constitutivamente anterior a si mesmo,
violando a irreflexividade e derivando False.
(0 axiomas). -/
theorem internal_node_cannot_ground_totality_circularity
    {Node : Type u}
    (ConstitutivePriority : OnticDomain Node → OnticDomain Node → Prop)
    (prior_wf : WellFounded ConstitutivePriority)
    (prior_trans : ∀ {a b c}, ConstitutivePriority a b → ConstitutivePriority b c → ConstitutivePriority a c)
    (n : Node)
    (hConstitutive : ConstitutivePriority (OnticDomain.node n) OnticDomain.totality)
    (hPurportedGround : ConstitutivePriority OnticDomain.totality (OnticDomain.node n)) :
    False

/-- TEOREMA 3C₂ (Refutação do Círculo Explicativo Ontológico Relativo ao Candidato e - 3-Ciclo):
Se a entidade exterior e do candidato T fundamenta a Totalidade concreta (e ≺ S),
a Totalidade explica a Condição explicativa (S ≺ c), e essa Condição explica a determinação
concreta de e (c ≺ e), então sob prioridade transitiva bem-fundada, e explica-se a si mesma (e ≺ e),
violando a irreflexividade e derivando False.
(0 axiomas). -/
theorem candidate_consequence_circularity_refutation
    {Node : Type u} {Ext : Type u}
    (ConstitutivePriority : CandidateOnticItem Node Ext → CandidateOnticItem Node Ext → Prop)
    (prior_wf : WellFounded ConstitutivePriority)
    (prior_trans : ∀ {a b c}, ConstitutivePriority a b → ConstitutivePriority b c → ConstitutivePriority a c)
    (e : Ext)
    (hGroundsTotality : ConstitutivePriority (CandidateOnticItem.candidate e) CandidateOnticItem.totality)
    (hTotalityExplainsCondition : ConstitutivePriority CandidateOnticItem.totality CandidateOnticItem.condition)
    (hConditionDeterminesGround : ConstitutivePriority CandidateOnticItem.condition (CandidateOnticItem.candidate e)) :
    False

/-- TEOREMA 3C₃ (Refutação da Circularidade Consequente Directa Relativa a e - 2-Ciclo):
Se a entidade exterior e do candidato T fundamenta a Totalidade concreta (e ≺ S) e a determinação
de e apela directamente à Totalidade fundamentada (S ≺ e), induz-se e ≺ e, derivando False.
(0 axiomas). -/
theorem candidate_direct_consequence_cycle_refutation
    {Node : Type u} {Ext : Type u}
    (ConstitutivePriority : CandidateOnticItem Node Ext → CandidateOnticItem Node Ext → Prop)
    (prior_wf : WellFounded ConstitutivePriority)
    (prior_trans : ∀ {a b c}, ConstitutivePriority a b → ConstitutivePriority b c → ConstitutivePriority a c)
    (e : Ext)
    (hGroundsTotality : ConstitutivePriority (CandidateOnticItem.candidate e) CandidateOnticItem.totality)
    (hTotalityExplainsGround : ConstitutivePriority CandidateOnticItem.totality (CandidateOnticItem.candidate e)) :
    False

/-- TEOREMA 3E (Refutação da Circularidade Constitutiva de Candidato Interno):
Se um candidato a fundamento tem a identidade de um nó interno e é postulado para fundamentar a totalidade,
induz-se n ≺ n, derivando False por irreflexividade da prioridade constitutiva bem-fundada.
(0 axiomas). -/
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
    False

/-- TEOREMA 3F (Dedução de Transcendência Estrutural Positiva):
Nenhum candidato interno pode fundamentar a totalidade concreta sem circularidade constitutiva.
Sob prioridade constitutiva transitiva bem-fundada, qualquer candidato a fundamento da totalidade
TEM DE SER ESTRUTURALMENTE EXTERIOR: ∃ e : T.ExtEntity, T.ground = GroundIdentity.external e.
Transcendência é DERIVADA como identidade positiva estrutural, não apenas pressuposta.
(0 axiomas). -/
theorem candidate_ground_must_be_structurally_external
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop)
    (prior_wf : ∀ Ext, WellFounded (ConstitutivePriority Ext))
    (prior_trans : ∀ Ext {a b c : CandidateOnticItem S.Node Ext}, ConstitutivePriority Ext a b → ConstitutivePriority Ext b c → ConstitutivePriority Ext a c)
    (hConstitutiveOfTotality : ∀ Ext (m : S.Node), ConstitutivePriority Ext (CandidateOnticItem.node m) CandidateOnticItem.totality)
    (hInternalGroundsTotality : ∀ n : S.Node, T.ground = GroundIdentity.internal n →
      ∀ Ext, ConstitutivePriority Ext CandidateOnticItem.totality (CandidateOnticItem.node n)) :
    ∃ e : T.ExtEntity, T.ground = GroundIdentity.external e

/-- TEOREMA 4 (Necessitação Impessoal Destrói a Contingência):
Uma causa impessoal necessária que determina rigidamente o sistema torna-o invariante,
contradizendo a contingência genuína de S.
(0 axiomas). -/
theorem necessary_impersonal_ground_contradicts_contingency
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (hImpNec : ImpersonalNecessitatingGround S T)
    (hCont : ContingentSystem S) :
    False

/-- TEOREMA 5 (Fundamento Impessoal Não-Necessitante Falha a Explicação Contrastiva em w_alt):
Um fundamento impessoal não-necessitante que falhe a justificação contrastiva contradiz
a exigência de ContrastiveExplanationForTotality.
(0 axiomas). -/
theorem unjustified_alternative_fails_contrastive_at
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (w_alt : S.World)
    (hUnjustified : UnjustifiedContrastiveAlternativeAt S T w_alt)
    (hExpl : ContrastiveExplanationForTotality S T w_alt) :
    False

/-- TEOREMA 5C (Determinação Consequente-Dependente Falha a Bem-Fundação para o Candidato e):
Se o candidato a fundamento com entidade e fundamenta a totalidade S, e a condição que explica
a determinação de e depende da totalidade S, então e depende constitutivamente de si mesmo, derivando False.
(0 axiomas). -/
theorem consequence_dependent_mode_fails_well_foundedness
    {Node : Type u} {Ext : Type u}
    (ConstitutivePriority : CandidateOnticItem Node Ext → CandidateOnticItem Node Ext → Prop)
    (prior_wf : WellFounded ConstitutivePriority)
    (prior_trans : ∀ {a b c}, ConstitutivePriority a b → ConstitutivePriority b c → ConstitutivePriority a c)
    (e : Ext)
    (hGroundsTotality : ConstitutivePriority (CandidateOnticItem.candidate e) CandidateOnticItem.totality)
    (hConsequenceDep : ConsequenceDependentDetermination ConstitutivePriority e) :
    False

/-- TEOREMA 5D (Dependência Consequente Directa Falha a Bem-Fundação para o Candidato e):
A dependência directa da determinação de e na totalidade que e fundamenta viola a irreflexividade.
(0 axiomas). -/
theorem direct_consequence_mode_fails_well_foundedness
    {Node : Type u} {Ext : Type u}
    (ConstitutivePriority : CandidateOnticItem Node Ext → CandidateOnticItem Node Ext → Prop)
    (prior_wf : WellFounded ConstitutivePriority)
    (prior_trans : ∀ {a b c}, ConstitutivePriority a b → ConstitutivePriority b c → ConstitutivePriority a c)
    (e : Ext)
    (hGroundsTotality : ConstitutivePriority (CandidateOnticItem.candidate e) CandidateOnticItem.totality)
    (hDirectDep : DirectConsequenceDependence ConstitutivePriority e) :
    False

/-- TEOREMA 5E (Condição Prévia Independente Contradiz a Ultimidade):
Se uma condição exterior independente C determina a entidade e (C ≺ e),
então T é um fundamento intermediário em vez de uma explicação última auto-suficiente de S.
Derivado directamente da definição de suficiência explicativa última!
(0 axiomas). -/
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

/-- TEOREMA 5D₂ (O Teorema da Ponte Impessoal — Trifurcação Deduzida):
Sob o Princípio da Simetria Explicativa e Diferenciação Extrínseca (Tag: META), se um fundamento impessoal
necessário com essência invariante não necessita rigidamente o sistema contingente, mas fornece
justificação contrastiva entre mundos divergentes, a sua determinação TEM de ser ou
consequente-dependente ou dependente de uma condição independente.
DEDUZIDO como teorema no kernel a partir da partição clássica das condições extrínsecas no domínio ôntico!
(Axiomas: [propext, choice, Quot.sound]). -/
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
    IndependentConditionMode (ConstitutivePriority T.ExtEntity) e

/-- TEOREMA 5B (Dedução Clássica da Exaustividade dos Modos):
Demonstra que todo o candidato a fundamento ou necessita rigidamente o sistema,
ou fornece justificação contrastiva para todas as alternativas divergentes,
ou contém uma alternativa onde falha em fornecer justificação.
(Axiomas: [propext, choice, Quot.sound]). -/
theorem grounding_modes_exhaustive
    (S : ConcreteSystem.{u})
    (T : CandidateGround S) :
    NecessitatingMode S T ∨
    GuidedByJustificationMode S T ∨
    (∃ w_alt : S.World, S.Accessible S.actualWorld w_alt ∧
      (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) ∧
      UnjustifiedContrastiveAlternativeAt S T w_alt)

/-- TEOREMA 6 (Modo de Justificação Agencial Instancia a Fonte Pessoal Livre):
Demonstra que a capacidade agencial de apreender alternativas, avaliar razões e
escolher livremente instancia substantivamente todos os seis atributos de FreePersonalSource
mediante as pontes metafísicas TeleologicalAgencyPrinciple e AgentialFreedomBridge.
(Axiomas: [propext, choice, Quot.sound]). -/
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
    FreePersonalSource S T

/-- TEOREMA MESTRE (Dedução Conclusiva da Fonte Pessoal Necessária e Livre):
Sob a contingência do sistema, o PSR Contrastivo Geral, o Princípio de Aseidade,
a Preservação da Natureza sob Aseidade Impessoal, o Princípio da Simetria Explicativa,
o Princípio da Exigência de Ultimidade Explicativa, o Princípio de Agência Teleológica
e a Ponte de Liberdade Agencial:
O Fundamento Transcendente T NÃO PODE ser interno (refutado por circularidade constitutiva),
NÃO PODE ser impessoal (pois se for impessoal, pela ponte deduzida teria de ser consequente-dependente —
refutado por circularidade relativa a e — ou independente — refutado por ultimidade — ou necessitante —
refutado por contingência — ou injustificado — refutado pelo PSR),
pelo que é DEDUZIDO por contradição que T tem de ser um Agente Pessoal,
culminando num Agente Pessoal Estruturalmente Transcendente, Necessário, Intencional e Livre.
(Axiomas: [propext, choice, Quot.sound]). -/
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
    ∃ T : CandidateGround S, FreePersonalSource S T

### 3.3 Auditoria Completa de Axiomas no Kernel de Lean 4
Executado via `lake env lean OntologicalIncompletenessTheorem.lean`:
```
'Logos.OntologicalIncompleteness.prior_irrefl' does not depend on any axioms
'Logos.OntologicalIncompleteness.closed_cycle_violates_ontological_priority' does not depend on any axioms
'Logos.OntologicalIncompleteness.internal_node_cannot_self_determine' does not depend on any axioms
'Logos.OntologicalIncompleteness.infinite_regress_conditional_rules_satisfied_by_vacuity' does not depend on any axioms
'Logos.OntologicalIncompleteness.infinite_regress_cannot_self_ground' does not depend on any axioms
'Logos.OntologicalIncompleteness.fully_internally_determined_is_impossible' does not depend on any axioms
'Logos.OntologicalIncompleteness.closed_system_has_unexplained_boundary' depends on axioms: [propext, choice, Quot.sound]
'Logos.OntologicalIncompleteness.internal_node_cannot_ground_totality_circularity' does not depend on any axioms
'Logos.OntologicalIncompleteness.candidate_consequence_circularity_refutation' does not depend on any axioms
'Logos.OntologicalIncompleteness.candidate_direct_consequence_cycle_refutation' does not depend on any axioms
'Logos.OntologicalIncompleteness.internal_rules_fail_contrastive_distinction' does not depend on any axioms
'Logos.OntologicalIncompleteness.internal_candidate_cannot_ground_totality' does not depend on any axioms
'Logos.OntologicalIncompleteness.candidate_ground_must_be_structurally_external' does not depend on any axioms
'Logos.OntologicalIncompleteness.necessary_impersonal_ground_contradicts_contingency' does not depend on any axioms
'Logos.OntologicalIncompleteness.unjustified_alternative_fails_contrastive_at' does not depend on any axioms
'Logos.OntologicalIncompleteness.consequence_dependent_mode_fails_well_foundedness' does not depend on any axioms
'Logos.OntologicalIncompleteness.direct_consequence_mode_fails_well_foundedness' does not depend on any axioms
'Logos.OntologicalIncompleteness.independent_condition_contradicts_ultimacy' does not depend on any axioms
'Logos.OntologicalIncompleteness.grounding_modes_exhaustive' depends on axioms: [propext, choice, Quot.sound]
'Logos.OntologicalIncompleteness.impersonal_ground_forces_consequence_or_independent_condition' depends on axioms: [propext, choice, Quot.sound]
'Logos.OntologicalIncompleteness.agential_justification_mode_yields_free_personal_source' depends on axioms: [propext, choice, Quot.sound]
'Logos.OntologicalIncompleteness.contingent_system_derives_free_personal_source' depends on axioms: [propext, choice, Quot.sound]
```
Dezassete dos vinte e dois teoremas dependem de **0 axiomas**. Os restantes cinco teoremas consomem unicamente a lógica clássica standard (`Classical.choice`, `propext`, `Quot.sound`). A refutação da circularidade é agora rigorosamente relativa à entidade exterior concreta do candidato $T$ (`candidate_consequence_circularity_refutation`). A ponte para a refutação de fontes impessoais é **deduzida formalmente como teorema** (`impersonal_ground_forces_consequence_or_independent_condition`) a partir do princípio primitivo de simetria explicativa (`ExplanatorySymmetryPrinciple`, Tag: META). Todos os seis atributos da Fonte Pessoal Livre foram deduzidos no kernel.

A análise lógico-ontológica conduz a um resultado definitivo:

1. **A auto-determinação interna de uma totalidade é uma impossibilidade formal:** a topologia relacional (circular ou linear) apenas redistribui dependências condicionais, sendo incapaz de fundamentar a sua própria instanciação.
2. **O Facto Bruto é o suicídio da razão ontológica:** aceitar que o sistema existe "porque sim" destrói a base de toda a inferência inteligível.
3. **A exigência analítica de transcendência impõe a agência:** para que o fundamento transcenda o sistema e explique a contingência sem necessitação mecânica rígida, tem de ser capaz de selecção intencional teleológica.

A **Fonte Pessoal Necessária e Livre** não é uma hipótese teológica arbitrária ou mística; é o **único atractor lógico e ontológico coerente** que resolve o impasse da determinação contingente sem recorrer à petição de princípio nem à capitulação no absurdo.

---

## 4. Reconstrução Unificada do Argumento em Ordem de Dependência e Auditoria das Pontes Metafísicas

Para garantir a transparência analítica integral, prevenir leituras equívocas e tornar o argumento imediatamente auditável em um único local, esta secção sintetiza:
1. A reconstrução passo a passo dos 8 passos lógicos em ordem estrita de dependência dedutiva;
2. A auditoria detalhada das 5 pontes metafísicas;
3. A disciplina epistemológica entre derivações no kernel, premissas explícitas e justificação filosófica;
4. A clarificação notacional e direcional da prioridade ontológica atemporal.

### 4.1 Reconstrução Passo a Passo em Ordem Estrita de Dependência

A derivação do Teorema Mestre (`contingent_system_derives_free_personal_source`) articula 8 passos dedutivos encadeados:

```
[Passo 1: PSR Contrastivo]
          │
          ▼
[Passo 2: Exclusão do Necessitarismo Rígido]
          │
          ▼
[Passo 3: Simetria de Essência Invariante (Leibniz / Lipton)]
          │
          ▼
[Passo 4: Trifurcação Ôntica de Condições Extrínsecas]
          ├──> [Passo 5: Consequente-Dependente -> Círculo Ontológico -> REFUTADO (0 axiomas)]
          ├──> [Passo 6: Condição Independente -> Falha de Ultimidade -> REFUTADO (0 axiomas)]
          └──> [Passo 7: Ausência de Justificação -> Violação do PSR -> REFUTADO (0 axiomas)]
          │
          ▼
[Passo 8: Modo de Justificação Agencial -> Fonte Pessoal Livre]
```

#### Passo 1: A realidade concreta contingente exige uma explicação contrastiva sob o PSR
- **Declaração Lean:** `GeneralContrastivePSR S` (consumido na inferência inicial: `obtain ⟨T, hGrounds, hExpl⟩ := hPSR hCont`).
- **Fundamentação no Tratado:** §3.1.2 e §3.1.3. A contingência da realidade implica a existência de alternativas acessíveis contrafactuais onde o sistema diverge ou não existe. O PSR Geral Contrastivo afirma que a instanciação e configuração de $S$ no mundo actual não pode ser um facto bruto; tem de existir um fundamento $T$ cuja determinação justifique $w_{act}$ em vez de $w_{alt}$.
- **Nexo Inferencial:** Estabelece a existência de um candidato a fundamento $T$ dotado de instanciação factual (`GroundsConcreteActuality`) e capacidade explicativa contrastiva (`ContrastiveExplanationForTotality`).

#### Passo 2: A necessitação rígida por um fundamento necessário exclui a contingência genuína
- **Declaração Lean:** `necessary_impersonal_ground_contradicts_contingency` (Teorema derivado no kernel com 0 axiomas).
- **Fundamentação no Tratado:** §3.1.4 (Hipótese 1 - Necessitarismo Spinoziano). Se $T$ existe necessariamente e a sua determinação necessita rigidamente $S$, então $S$ tem a mesma configuração em todos os mundos acessíveis, o que contradiz a premissa de contingência genuína (`ContingentSystem S`).
- **Nexo Inferencial:** Elimina o primeiro ramo da exaustividade clássica dos modos (`NecessitatingMode S T`), forçando o fundamento a operar de modo não-necessitante se a contingência for real.

#### Passo 3: Uma natureza intrínseca invariante não distingue alternativas contingentes (Simetria Explicativa)
- **Declaração Lean:** `ExplanatorySymmetryPrinciple S T ConstitutivePriority` (Tag: META) e `ImpersonalAseityPreservesNature S T` (Tag: META).
- **Fundamentação no Tratado:** §3.1.2 (Condição de Diferença de Lipton e Princípio de Simetria de Leibniz). Se $T$ é impessoal (`IsImpersonal`) e a sua essência é invariante entre mundos acessíveis (`NatureInvariant`), o conjunto de propriedades e factos intrínsecos de $T$ é rigorosamente indiscernível entre $w_{act}$ e $w_{alt}$. Pela Condição de Diferença de Lipton, um factor explicativo tem de diferenciar os termos do contraste; por Leibniz, condições perfeitamente simétricas não podem justificar um resultado assimétrico sem necessitação rígida.
- **Nexo Inferencial:** Demonstra que um fundamento impessoal não pode fornecer justificação contrastiva a partir de características puramente intrínsecas; se fornecer justificação, esta tem necessariamente de apelar a uma condição diferenciadora extrínseca no domínio ôntico (`ConstitutivePriority condition (candidate e)`).

#### Passo 4: Bifurcação Estrutural da Condição Extrínseca face à Totalidade
- **Declaração Lean:** `impersonal_ground_forces_consequence_or_independent_condition` (Teorema derivado no kernel a partir da lógica clássica e do princípio de simetria).
- **Fundamentação no Tratado:** §3.1.1 e §3.1.2. A condição extrínseca $C$ que determina a entidade exterior $e$ de $T$ ou depende ontologicamente da totalidade $S$ que $e$ fundamenta ($S \prec C$), ou é ontologicamente independente dela ($\neg(S \prec C)$).
- **Nexo Inferencial:** Reduz exaustivamente a hipótese do fundamento impessoal a dois ramos disjuntivos: `ConsequenceDependentDetermination` ou `IndependentConditionMode`.

#### Passo 5: Refutação da Determinação Consequente-Dependente por Circularidade Ontológica
- **Declaração Lean:** `consequence_dependent_mode_fails_well_foundedness` e `candidate_consequence_circularity_refutation` (Teoremas derivados no kernel com 0 axiomas).
- **Fundamentação no Tratado:** §2.2, §3.1.4 (Hipótese 3) e Teorema 3C₂. Se $e$ fundamenta a totalidade concreta ($e \prec S$), a totalidade condiciona a condição explicativa ($S \prec C$), e essa condição determina a actuação de $e$ ($C \prec e$), induz-se um ciclo atemporal de prioridade $e \prec S \prec C \prec e$. Sob prioridade transitiva bem-fundada, isto impõe $e \prec e$, violando a irreflexividade ontológica fundamental (`well_founded_irrefl`).
- **Nexo Inferencial:** Elimina cabalmente o ramo consequente-dependente com 0 axiomas de cálculo, demonstrando que o fundamento não pode apelar ao próprio sistema que fundamenta para justificar a sua actuação.

#### Passo 6: Refutação da Condição Independente por Falta de Ultimidade Auto-Suficiente
- **Declaração Lean:** `independent_condition_contradicts_ultimacy` (Teorema derivado no kernel com 0 axiomas) e `ExplanatoryUltimacyRequirement` (Tag: META).
- **Fundamentação no Tratado:** §3.1.3 e §3.1.4 (Hipótese 4). Se a determinação de $T$ depende de uma condição independente $C$ ($C \prec e \land \neg(S \prec C)$), $T$ não é a explicação última auto-suficiente de $S$: torna-se um fundamento intermediário ($C \prec T \prec S$) que transfere a dívida de suficiência explicativa para $C$. O PSR cosmológico exige que o fundamento da totalidade seja último e termine a cadeia explicativa.
- **Nexo Inferencial:** Elimina o ramo da condição independente com 0 axiomas, fechando a refutação da alternativa impessoal.

#### Passo 7: Aplicação do PSR contra a Ausência de Justificação Contrastiva
- **Declaração Lean:** `unjustified_alternative_fails_contrastive_at` (Teorema derivado no kernel com 0 axiomas).
- **Fundamentação no Tratado:** §3.1.2 e Teorema 5. Se um candidato a fundamento não necessita rigidamente nem fornece justificação contrastiva para uma alternativa acessível divergente, a contingência permanece injustificada, colidindo com a garantia contrastiva de `GeneralContrastivePSR`.
- **Nexo Inferencial:** Elimina o terceiro ramo da exaustividade clássica (`UnjustifiedContrastiveAlternativeAt`), provando por contradição que o candidato tem de operar no modo guiado por justificação agencial.

#### Passo 8: Agência Pessoal Intencional e Decomposição da Liberdade Libertária
- **Declaração Lean:** `agential_justification_mode_yields_free_personal_source` e a derivação por estágios `agential_freedom_derived`, articulada com `TeleologicalAgencyPrinciple` e a ponte de estágio 4 `AgentialCounterfactualChoiceBridge`.
- **Fundamentação no Tratado:** §3.1.3 e §3.1.4 (Hipótese 5). Sob a exclusão demonstrativa de todos os modos impessoais e do vazio explicativo, o fundamento tem de possuir intelecto para apreender alternativas contrafactuais (`IsPersonalAgent`). A atribuição de liberdade positiva decompõe-se de forma estritamente auditável em quatro estágios atemporais:
  1. *Invariância da Base Essencial:* A essência do agente é necessária e invariante entre mundos acessíveis (`NatureInvariant S T`).
  2. *Disponibilidade Modal de Alternativas:* Demonstra-se no Lean (`contingent_system_yields_divergent_accessible_world_under_invariant_nature`) que, da contingência de $S$ e da invariância de $T$, decorre a existência de um mundo acessível alternativo com natureza idêntica e resultado divergente (`SystemOutcomeAt S w_alt ≠ SystemOutcomeAt S actualWorld`).
  3. *Selecção Intencional Actual:* O agente escolhe o resultado actual em virtude de razões teleológicas (`SelectsIntentionally S T`).
  4. *Poder Contrafactual de Escolha Agencial:* Pela ponte `AgentialCounterfactualChoiceBridge`, o agente intencional detém o poder de ter escolhido o resultado alternativo em $w_{alt}$ (`T.ChoosesOutcomeAt w_alt altOutcome`), formalizando que a alternativa é uma escolha agencial do mesmo sujeito e não um mero desvio acidental.
- **Nexo Inferencial:** Conclui a prova do Teorema Mestre, demonstrando a existência necessária de uma Fonte Transcendente, Pessoal, Intencional e Livre (`FreePersonalSource S T`).

---

### 4.2 Matriz de Auditoria das Cinco Pontes Metafísicas

| Ponte Metafísica | Tag Lean | Estatuto Formal no Lean | Justificação Filosófica no Tratado | Papel Exato no Teorema Mestre |
| :--- | :--- | :--- | :--- | :--- |
| **`ExplanatorySymmetryPrinciple`** | `META` | Parâmetro explícito | §3.1.1, §3.1.2, §4 (Passo 3): Princípio da Simetria de Leibniz e Condição de Diferença de Lipton | Força o fundamento impessoal não-necessitante a depender de uma condição extrínseca ($C \prec e$), disparando a bifurcação de `impersonal_ground_forces_consequence_or_independent_condition`. |
| **`ExplanatoryUltimacyRequirement`** | `META` | Parâmetro explícito | §3.1.1, §3.1.3, §4 (Passo 6): Auto-suficiência explicativa do PSR cosmológico | Estabelece que o fundamento factual da totalidade tem de ser auto-suficiente, permitindo a `independent_condition_contradicts_ultimacy` derivar contradição do ramo $C \prec e$. |
| **`ImpersonalAseityPreservesNature`** | `META` | Parâmetro explícito | §3.1.1, §4 (Passo 3): Aseidade ontológica de entidades necessárias não-agenciais | Fornece `NatureInvariant S T` para o candidato impessoal na redução ao absurdo do Teorema Mestre. |
| **`TeleologicalAgencyPrinciple`** | `META` | Parâmetro explícito | §3.1.1, §3.1.3, §4 (Passo 8): Natureza teleológica da agência intencional racional | Deriva `SelectsIntentionally S T` a partir de `IsPersonalAgent` e `GuidedByJustificationMode`. |
| **`AgentialFreedomBridge`** | `META` | Parâmetro explícito | §3.1.1, §3.1.3, §4 (Passo 8): Concepção libertária da escolha intencional contrafactual | Deriva `ActsFreely S T` e `NatureInvariant S T` a partir da selecção intencional sob essência necessária. |

#### Análise Específica do `ExplanatorySymmetryPrinciple`
É fundamental esclarecer que o `ExplanatorySymmetryPrinciple` **não é um dispositivo arbitrário ou ad hoc introduzido para forçar artificialmente uma condição externa**. Pelo contrário:
1. Ele expressa o **núcleo semântico da explicação contrastiva**: condições puramente intrínsecas e simétricas que sejam rigorosamente idênticas entre dois mundos possíveis não contêm em si a razão de ser da diferença entre esses mundos (Lipton 2004).
2. Sem esta restrição semântica, o modelo formal admitiria um **contra-modelo estipulativo minimal** onde `ProvidesContrastiveJustification` seria assinalado como `True` no vácuo para uma entidade impessoal invariante, sem qualquer base inteligível.
3. O princípio fecha esse contra-modelo abusivo, exigindo honestamente que qualquer diferenciação que não decorra de agência intencional tenha de provir de um factor extrínseco real no domínio ontológico.

---

### 4.3 Disciplina Epistemológica: Teoremas do Kernel vs. Premissas Metafísicas

Para evitar confusões categorialmente graves na leitura da formalização, adota-se uma disciplina rigorosa:

1. **Teorema Derivado pelo Kernel (`kernel-derived theorem`):**
   - É uma proposição demonstrada formalmente no Lean a partir das hipóteses estipuladas na sua assinatura, sem recorrer a axiomas não-declarados.
   - Exemplos: `closed_cycle_violates_ontological_priority`, `candidate_consequence_circularity_refutation`, `independent_condition_contradicts_ultimacy`, `impersonal_ground_forces_consequence_or_independent_condition`.
2. **Premissa Metafísica Explícita (`explicit metaphysical premise`):**
   - É uma premissa substantiva passada explicitamente como parâmetro formal ao teorema no Lean (como as cinco pontes catalogadas em §4.2).
   - O compilador Lean **não deriva** estas premissas a partir do vazio lógico; o compilador demonstra a relação condicional estrita:
     $$\big(\text{Premissas Metafísicas} \wedge \text{Estrutura do Sistema}\big) \implies \text{Fonte Pessoal Livre}$$
3. **Premissa Filosoficamente Justificada (`philosophically justified premise`):**
   - É uma premissa cujo fundamento racional, semântico e ontológico foi argumentado de forma substantiva no tratado filosófico (e.g. Leibniz, Lipton, PSR).
   - O facto de uma premissa ser recebida pelo Lean como parâmetro não atesta que ela é um hiato injustificado: a sua justificação reside no tratado, que constitui o corpo de demonstração ontológica.
4. **Interpretação do Footprint de `#print axioms`:**
   - Quando o comando `#print axioms` devolve `[propext, Classical.choice, Quot.sound]`, isto atesta unicamente que a dedução lógica do teorema utiliza os axiomas fundacionais padrão do Lean 4 e não consome nenhum axioma lógico espúrio (`sorryAx`, axiomas não-standard).
   - Este footprint **não significa** que o Teorema Mestre não tenha premissas ontológicas; significa apenas que todas as suas premissas ontológicas foram formalizadas de modo limpo e transparente como hipóteses no tipo do teorema, sem qualquer introdução sub-reptícia no kernel.

#### Distinção entre o Teorema da Circularidade e a Dependência do Consequente
Deve distinguir-se com precisão:
- O **Teorema Estrutural da Circularidade** (`candidate_consequence_circularity_refutation`): demonstra com 0 axiomas que qualquer ciclo finito de dependência prioritária $e \prec S \prec C \prec e$ viola a irreflexividade da bem-fundamentação. Esta é uma verdade dedutiva pura.
- O **Argumento Substantivo da Consequência**: estabelece quando e por que razão um fundamento impessoal cai nessa circularidade. A determinação de um fundamento impessoal apela ao consequente sempre que a única justificação da sua concretização actual repousa sobre a própria configuração do universo concreto cuja existência ele teria de explicar originariamente.

---

### 4.4 Clarificação Notacional e Direcional da Prioridade Ontológica Atemporal

#### 1. A Convenção Direcional Formal
No domínio ontológico `CandidateOnticItem Node Ext`, a relação `ConstitutivePriority a b` formaliza a ordem ontológica fundamental:
$$\text{ConstitutivePriority } a \ b \iff a \prec b \quad (a \text{ é ontologicamente anterior a } b)$$
- `CandidateOnticItem.node n ≺ CandidateOnticItem.totality`: o nó interno $n$ constitui a totalidade $S$.
- `CandidateOnticItem.candidate e ≺ CandidateOnticItem.totality`: a entidade exterior $e$ fundamenta a totalidade $S$.
- `CandidateOnticItem.condition ≺ CandidateOnticItem.candidate e`: a condição $C$ determina a entidade exterior $e$.
- `CandidateOnticItem.totality ≺ CandidateOnticItem.condition`: a totalidade $S$ explica/condiciona a condição $C$.

#### 2. A Leitura Estrita de `IndependentConditionMode`
A definição formal:
```lean
def IndependentConditionMode
    {Node : Type u} {Ext : Type u}
    (ConstitutivePriority : CandidateOnticItem Node Ext → CandidateOnticItem Node Ext → Prop)
    (e : Ext) : Prop :=
  ConstitutivePriority CandidateOnticItem.condition (CandidateOnticItem.candidate e) ∧
  ¬ ConstitutivePriority CandidateOnticItem.totality CandidateOnticItem.condition
```
deve ser lida com rigor:
1. `ConstitutivePriority condition (candidate e)` formaliza $C \prec e$: a condição $C$ é anterior a $e$ e determina a sua actuação;
2. `¬ ConstitutivePriority totality condition` formaliza $\neg(S \prec C)$: a totalidade fundamentada $S$ **não é anterior a $C$** (isto é, $C$ não depende da totalidade $S$ gerada por $e$).

**Prevenção de Má Leitura:**  
A cláusula $\neg(S \prec C)$ significa unicamente que a condição $C$ não depende do consequente que ela própria contribui para fundamentar. Ela **não afirma** que $C$ não tem nenhuma relação com o universo do ser; isola especificamente o ramo onde $C$ é uma condição prévia não-circular (independente de $S$). É precisamente esta independência face a $S$ que faz de $T$ um fundamento intermediário ($C \prec T \prec S$) e transfere a dívida de suficiência explicativa para $C$, colidindo com a exigência de ultimidade (`independent_condition_contradicts_ultimacy`).

#### 3. Atemporalidade da Prioridade Ontológica
A relação `ConstitutivePriority` é estritamente **atemporal e explicativa**:
- Não se trata de uma anterioridade cronológica no tempo físico ($t_1 < t_2$), nem de uma cadeia causal temporal que pudesse admitir soluções relativistas ou laços causais de tipo fechado (CTCs).
- Trata-se da **ordem ontológica de fundamentação do ser**: a realidade $A$ constitui a razão ontológica da realidade $B$.
- Em qualquer ordem de fundamentação bem-fundada, a auto-fundamentação viciosa ($A \prec \dots \prec A$) destruiria a inteligibilidade da existência, pois exigiria que $A$ fornecesse a base do seu próprio ser antes de a possuir.

#### 4. Conexão entre as Relações de Determinação Intra-Sistémica e Constitutiva Inter-Nível
O modelo ontológico distingue estritamente dois níveis de dependência:
1. `S.Determines` e `S.Prior`: governam a estrutura relacional interna intra-sistémica entre os nós de $S$ (`S.Node → S.Node → Prop`);
2. `ConstitutivePriority`: governa a ordem ontológica inter-nível abrangendo nós internos, a totalidade cósmica, a entidade exterior do candidato a fundamento e as condições explicativas extrínsecas (`CandidateOnticItem S.Node Ext`).

A ponte canónica de inclusão é expressa por:
```lean
def InternalPriorityEmbedsInConstitutive
    (S : ConcreteSystem.{u})
    (ConstitutivePriority : (Ext : Type u) → CandidateOnticItem S.Node Ext → CandidateOnticItem S.Node Ext → Prop) : Prop :=
  ∀ (Ext : Type u) (a b : S.Node),
    S.Prior a b → ConstitutivePriority Ext (CandidateOnticItem.node a) (CandidateOnticItem.node b)
```
Demonstra-se formalmente com **0 axiomas** (`internal_priority_irrefl_from_constitutive`) que sob esta inclusão, a bem-fundamentação de `ConstitutivePriority` refuta directamente qualquer ciclo de prioridade interna entre nós, conectando harmoniosamente as duas relações sem refatorações redundantes.

---

### 4.5 Aprofundamento das Premissas Fundamentais: Derivação de ExplanatoryDeterminationRule e AgentialSovereigntyOverAlternatives a partir de Princípios Primitivos

Em resposta à exigência de fundamentar mais profundamente a necessidade da Fonte Pessoal Livre e demonstrar que as premissas de alto nível não são estipulações ad hoc nem circulares, formalizou-se no kernel do Lean 4 a derivação dedutiva rigorosa tanto de `ExplanatoryDeterminationRule` como de `AgentialSovereigntyOverAlternatives` a partir de princípios ontológicos e modais primitivos.

#### 1. Resolução da Vulnerabilidade de Vacuidade do PSR e Semântica de Fundamentação Ontológica Genuína
A passagem da ausência de necessitação rígida para a escolha agencial positiva contrafactual (`T.ChoosesOutcomeAt w_alt`) foi rigorosamente examinada para evitar qualquer pressuposição velada e para impedir que qualquer registo sintético satisfaça o PSR vacuamente:

- **Demonstração Formal da Vulnerabilidade Pré-Correcção:**  
  No teorema `pre_correction_psr_vacuously_provable_by_synthetic_candidate` (0 axiomas), demonstrou-se formalmente que, sob a definição anterior onde a explicação requeria apenas `ExistsAt ∧ out = SystemOutcomeAt ∧ DeterminesOutcomeAt` com `DeterminesOutcomeAt` unconstrained, um candidato sintético artificial com `GroundsConcreteActuality := fun _ _ => False` e `DeterminesOutcomeAt := fun _ _ _ => True` satisfazia vacuamente `UniversalOutcomePSR S` para **qualquer sistema concreto $S$**, provando a necessidade inadiável de endurecer a semântica explicativa.
- **Semântica Endurecida de Explicação Ontológica (`ExplainsOutcomeAt`, Linha 1710):**  
  A explicação de um resultado alternativo não pode ser satisfeita por meras declarações booleanas desacopladas. Em `ExplainsOutcomeAt`, exige-se agora cumulativamente:
  (1) Existência do fundamento no mundo $w$ (`T.ExistsAt T.ground w`);
  (2) Coincidência com o resultado fáctico do sistema no mundo $w$ (`SystemOutcomeAt S w = out`);
  (3) Determinação do resultado pelo fundamento (`T.DeterminesOutcomeAt T.ground w out`);
  (4) Ancoragem na Ordem de Prioridade Constitutiva (`∃ e, T.ground = external e ∧ ConstitutivePriority ... (candidate e) totality`);
  (5) Fundamentação Ontológica do Resultado (`T.GroundsOutcomeAt S ConstitutivePriority w out`).
- **Fundamentação Efectiva da Não-Instanciação (`GroundsNonInstantiationAt`, Linha 1685):**  
  Para impedir a vacuidade explicativa em que qualquer entidade coexistente num mundo onde $S$ não existe fosse considerada explicação da sua ausência, a não-instanciação (`out = none`) exige cumulativamente:
  (1) Existência do fundamento no mundo $w$ (`T.ExistsAt T.ground w`);
  (2) Não-instanciação de $S$ no mundo $w$ (`¬ S.InstantiatedIn w`);
  (3) Prioridade constitutiva sobre a totalidade de $S$ (`ConstitutivePriority ... (candidate e) totality`);
  (4) Justificação contrastiva positiva para a não-actualização de $S$ em relação ao mundo actual (`T.ProvidesContrastiveJustification T.ground S.actualWorld w`).
- **Contra-Modelo de Ausência Inexplicada (`T_unexplained_absence`, Linha 4460):**  
  Demonstrou-se formalmente no kernel com 0 axiomas (`unexplained_absence_fails_explanation` e `unexplained_absence_fails_psr`):
  Um candidato artificial que existe em todos os mundos e declara a determinação, mas omite a justificação explicativa da não-instanciação (`ProvidesContrastiveJustification := fun _ _ _ => False`), **falha estritamente `ExplainsOutcomeAt` e é rejeitado pelo PSR universal**.
- **Coerência Onto-Causal da Determinação (`CausalDeterminationCoherence`, Linha 1715):**  
  Integrada como condição indispensável em `ExplainsOutcomeAt`, `UniversalOutcomePSR`, `UniversalGroundGovernanceBridge` e `DeepenedMetaphysicallyGroundedWitness`. Determinar um resultado exige ontologicamente produzir a configuração concreta com acesso aos nós em mundos instanciados, ou fundamentar a não-instanciação em mundos não-instanciados. Provou-se no kernel com 0 axiomas (`causal_determination_fidelity_implies_grounds_outcome`) que a fidelidade causal da determinação implica estritamente a fundamentação ontológica do resultado (`GroundsOutcomeAt`).
- **Neutralidade Ontológica Estrita:**  
  Eliminou-se qualquer inclusão circular de `ChoosesOutcomeAt` na definição de `ExplainsOutcomeAt` e de `DeterminesOutcomeAt`. A explicação permanece ontologicamente neutra entre modos agenciais e impessoais, assegurando que `AgentialDeterminationEntailsChoice` funcione como uma ponte substantiva genuína e não como uma tautologia analítica.
- **Teoremas de Não-Vacuidade e Falha por Falta de Acesso Causal:**  
  Demonstrou-se formalmente com 0 axiomas no kernel:
  - `candidate_without_causal_access_fails_explanation`: qualquer candidato sem acesso causal fundacional aos nós de um sistema instanciado falha estritamente `ExplainsOutcomeAt`;
  - `synthetic_candidate_without_constitutive_priority_fails_psr`: qualquer registo artificial fora da prioridade constitutiva não pode satisfazer o PSR neutro.

#### 2. Reconstrução do Contra-Modelo Rival e Auditoria das Premissas (Secção III-G)
Em resposta à exigência metodológica de auditar contra-modelos que não fossem factos brutos e não pressupusessem a escolha contrafactual:
1. **Modelo A (Modelo de Fundamento Rival com Acesso Causal Nodal e Totalidade):**  
   Construiu-se o sistema contingente `rivalS` com duas identidades externas efectivamente distintas (`true ≠ false` via `ExtEntity := Bool`).  
   - A ordem `rivalPriority` confere a ambos os candidatos (`candidate true` e `candidate false`) prioridade constitutiva sobre o nó terminal `()` (`candidate_node`) e sobre a totalidade (`candidate_totality`), bem como a prioridade constitutiva dos nós sobre a totalidade (`node_totality`), satisfazendo `hConstitutiveOfTotality` com `rivalPriority_wf` provado;  
   - $T_{\text{main}}$ (`external true`) fundamenta o mundo actual `true` com acesso causal fundacional provado (`T_main_causal_access`);  
   - $T_{\text{rival}}$ (`external false`) fundamenta o mundo alternativo `false` com acesso causal fundacional provado (`T_rival_causal_access`).  
   *Resultado no Kernel (0 axiomas — `rival_ground_model_satisfies_neutral_psr_but_fails_scope`):* O PSR neutro (`UniversalOutcomePSR rivalS rivalPriority`) é satisfeito de forma substancial e não-vácua (ambos os mundos possuem fundamentos ontológicos explicativos com pleno acesso causal), mas $T_{\text{main}}$ **falha estritamente o âmbito explicativo universal** (`¬ UltimateGroundExplanatoryScope rivalS T_main rivalPriority`) porque o mundo alternativo é explicado pela entidade rival distinta `false ≠ true`. Isso isola e fundamenta a necessidade da premissa cosmológica de unicidade do fundamento cósmico (`formal/Logos/DivineClassicalAttributes.lean:2198` `exactly_one_universal_modal_ground`).
2. **Modelo B (Modelo de Determinação Pessoal Sem Escolha com Acesso Causal Pleno):**  
   O agente pessoal $T_{\text{det}}$ fundamenta ontologicamente o resultado contrafactual em $w = \text{false}$ sob `dualPriority` (com `candidate_node`, `candidate_totality` e `node_totality`) com acesso causal provado (`T_det_causal_access`), mas recusa a escolha intencional (`ChoosesOutcomeAt` é falso).  
   *Resultado no Kernel (0 axiomas — `non_choosing_personal_model_violates_agential_determination_bridge`):* O modelo fornece uma explicação causal completa e não-bruta para o resultado divergente, mas **viola estritamente a ponte de determinação agencial** (`¬ AgentialDeterminationIsChoice`), provando que, sem a tese da agência racional não-alienada (fundamentada em `Choice.lean:779` `AxIntentionalChoice`), a determinação pessoal sem escolha seria formalmente consistente.
3. **Modelo C (Modelo de Fronteira Não-Fundamentada — `unfounded_boundary_model_fails_causal_determination`):**  
   Demonstrou no kernel com 0 axiomas que quando um candidato omite a fundamentação dos nós terminais internos de fronteira, `FoundationalCausalDetermination` falha estritamente, provando a necessidade de `hCausal`.
4. **Testemunho Formal de Satisfazibilidade Conjunta (`deepened_neutral_principles_jointly_satisfiable`):**  
   Demonstrou-se no kernel com **0 axiomas** que `ContingentSystem`, `UniversalOutcomePSR`, `UltimateGroundExplanatoryScope`, `AgentialDeterminationIsChoice` e `ActsFreely` são simultaneamente e não-vacuamente verdadeiros no modelo canónico `dualWorldS, dualWorldT, dualPriority`.

#### 3. Auditoria da Cadeia Existencial e Teorema de Integração com o Corpus
Auditou-se rigorosamente a proveniência da testemunha da Fonte Última e a articulação entre os diferentes módulos do Logos:
- **Investigação de `EpistemicNecessity.lean:160`:**  
  O teorema `epistemic_normativity_somewhere_yields_a_free_being` demonstra condicionalmente a existência de um sujeito livre `s : Subject` sob a premissa de um juízo normativo fáctico (`ClaimsNormativeCorrectness s p`). Esse sujeito é um agente cognoscente no mundo; não fundamenta a totalidade concreta $S$. Confundir esse sujeito com o fundamento cósmico seria um erro de categoria ontológica.
- **Investigação de `DivineClassicalAttributes.lean:2198`:**  
  O teorema `exactly_one_universal_modal_ground` demonstra a unicidade e existência de um fundamento modal universal $g : \text{Entity}$ de toda a realidade sob a premissa de finitude semântica criatural (`hNoTotal : ∀ s : Subject, ∃ p, ¬ Means s p`).
- **Correspondência Formal e Mapeamento de Tipos:**  
  Em `OntologicalIncompletenessTheorem.lean`, importou-se `Logos.DivineClassicalAttributes` e definiu-se a função formal de correspondência `universalGroundToCandidate`, que mapeia o fundamento universal $g : \text{Entity}$ para um candidato `CandidateGround S` em universo 0 com `ExtEntity := Entity` e `ground := GroundIdentity.external g`, preservando os tipos estritos.
- **Decomposição Analítica da Ponte de Governança Universal:**  
  Distinguiu-se formalmente:  
  (1) **O que decorre da metafísica universal de $\Gamma$ (`UniversalGroundModalProfile`, `universal_ground_modal_profile_holds`):** a unicidade e existência necessária do fundamento modal universal $g : \text{Entity}$ via `Logos.FoundationalUnicity.exactly_one_universal_modal_ground`, a sua necessidade e asseidade ontológica, e a sua exterioridade categorial em relação às criaturas (`ofGround_ne_ofSubject`);  
  (2) **O que constitui compromisso metafísico relacional específico sobre o sistema $S$ (`UniversalGroundGovernanceBridge`):** a actualização concreta de $S$, as razões contrastivas sobre as alternativas de $S$, a teleologia agencial e a invariância pessoal sobre $S$, o âmbito explicativo universal sobre $S$ (`UltimateGroundExplanatoryScope`) e a ponte de escolha (`AgentialDeterminationIsChoice`).  
  Não se confunde a demonstração da existência do fundamento cósmico universal com a prova automática de que ele governa o sistema como agente pessoal livre: essa vinculação permanece governada com total honestidade intelectual pela ponte explícita.
- **Ponte de Governança Explicativa e Teorema de Integração:**  
  Formalizou-se a estrutura substantiva de ponte `UniversalGroundGovernanceBridge S g ConstitutivePriority` (Tag: META), com a demarcação explícita e honesta das premissas:
  (1) O escopo explicativo (`UltimateGroundExplanatoryScope`) é preservado explicitamente como ponte metafísica cosmológica (Tag: META), reconhecendo-se com rigor matemático que a unicidade modal abstrata de $g$ (`UniversalModalGround`) não deduz directamente o acesso causal nodal nem a determinação fáctica de resultados num sistema genérico $S$ sem uma assunção de governança;
  (2) A escolha agencial contrafactual é refinada da forma bicondicional para a implicação directa estritamente suficiente `AgentialDeterminationEntailsChoice`, demonstrando-se no kernel através de `agential_determination_entails_choice_derived` que, sob realização acção-teórica (`AgentialActionRealization`), a determinação intencional acarreta a escolha intencional contrafactual (`Chooses s P Q`) via `AxIntentionalChoice` e `AxActPolarity`.
  Em `governance_bridge_to_witness`, a testemunha aprofundada `DeepenedMetaphysicallyGroundedWitness` é construída directamente, consumindo o escopo cosmológico e a implicação de escolha agencial.  
  Provou-se o Teorema Mestre de Integração:
  `universal_ground_governance_yields_free_personal_source` (0 axiomas além da lógica clássica fundamental e dos axiomas auditados de $\Gamma$),
  que deduz formalmente `∃ T : CandidateGround S, FreePersonalSource S T` e a liberdade agencial da Fonte (`ActsFreely S T`).

#### 3.5 Formalização do Escopo Explicativo Mediado e Derivação da Escolha Agencial Específica de Resultado

Em resposta à auditoria rigorosa das duas pontes fundamentais, implementaram-se no kernel do Lean 4 os seguintes avanços estruturais:

1. **Investigação do Escopo Explicativo e Distinção Genuína entre Escopo Mediado e Directo:**
   - **Auditoria de `UniversalModalGround` e Limites da Unicidade Modal:** Investigou-se formalmente `DivineClassicalAttributes.UniversalModalGround g` (linha 1725). Documentou-se que esta propriedade estabelece a unicidade de $g$ no espaço modal de entidades de $\Gamma$ (`exactly_one_universal_modal_ground`), refutando contra-modelos politeístas rivais (como o Modelo A `rivalS`, onde operavam dois fundamentos ontológicos independentes), mas não contém termos específicos de nós nodais (`HasFoundationalCausalAccess`) ou determinação causal directa de resultados para um sistema concreto genérico $S$.
   - **Caminho Explicativo Multi-Passo em Prioridade Constitutiva (`PriorityPath`, Linha 1905):** Formalizou-se o caminho indutivo de passos intermediários de prioridade (`PriorityPath ConstitutivePriority Ext`), representando a cadeia reflexiva-transitiva através da qual entidades intermediárias dependem constitutivamente do fundamento anterior.
   - **Cadeia Explicativa Completa com Conexão de Extremidades (`CompleteExplanatoryChain`, Linha 1920):** Redefiniu-se `CompleteExplanatoryChain S ConstitutivePriority T' T` ligando ontologicamente o candidato explicativo local $T'$ directamente ao fundamento último $T$:
     (1) $T'$ possui uma entidade externa $e'$ que fundamenta a totalidade concreta de $S$;
     (2) $T$ possui uma entidade externa $e_{\text{ult}}$ que é não-fundamentada em prioridade (`IsUngroundedInPriority ConstitutivePriority e_ult`);
     (3) Sob alinhamento de domínios $T'.\text{ExtEntity} = T.\text{ExtEntity}$, existe um caminho explicativo real de prioridade (`PriorityPath`) conectando $e_{\text{ult}}$ a $e'$, ou $e' = e_{\text{ult}}$ (fundamentação directa).
   - **Escopo Explicativo Mediado Genuinamente Distinto (`MediatedExplanatoryScope`, Linha 1935):** Quantifica universalmente sobre todas as explicações locais em mundos alternativos acessíveis: se qualquer candidato $T'$ explica ontologicamente o resultado de $S$ em $w_{\text{alt}}$ (`ExplainsOutcomeAt S T' ...`), então existe uma cadeia explicativa completa conectando $T'$ a $T$ (`CompleteExplanatoryChain S ConstitutivePriority T' T`). Esta definição é genuinamente distinta de `UltimateGroundExplanatoryScope`, pois acomoda plenamente causas secundárias intermediárias e não alega que $T$ determina directamente cada resultado local.
   - **Ponte de Transmissão Explicativa (`ExplanatoryTransmission`, Linha 1950) e Teorema de Dedução (0 axiomas — `mediated_scope_to_ultimate_scope_under_transmission`, Linha 1965):** Demonstrou-se formalmente no kernel que, sob a ponte metafísica explícita de que um fundamento último que encerra a cadeia explicativa de uma causa secundária herda a eficácia explicativa do resultado (`ExplanatoryTransmission`), o escopo mediado deduz rigorosamente o escopo directo (`UltimateGroundExplanatoryScope`).
   - **Homomorfismo Limpo e Terminação Única no Fundamento Modal (0 axiomas — `universal_ground_chain_terminus_unicity`, Linha 2015):** Removeu-se o campo circular de subsunção explicativa de `PriorityGroundingHomomorphism`. Demonstrou-se no kernel que o término não-fundamentado de qualquer cadeia completa de prioridade é mapeado com unicidade estrita para o fundamento modal universal $g = \text{Entity.ofGround}$.
   - **Demarcação Honesta do Escopo Directo:** Em estrito cumprimento das regras metodológicas do projecto ("If universal grounding does not guarantee that complete explanations of this concrete system are subsumed by the same ground, retain UltimateGroundExplanatoryScope as an explicit META premise. Do not call it derived"), reconheceu-se que a assunção de que o fundamento universal subsume directamente a determinação de todos os resultados contingentes de $S$ constitui uma premissa cosmológica irredutível da governança universal, preservando `UltimateGroundExplanatoryScope` como parâmetro explícito em `UniversalGroundGovernanceBridge` (Tag: META) e nos testemunhos mestres, sem pretensões de derivação incondicional.

2. **Representação Específica de Resultado e Derivação da Escolha Agencial:**
   - **Representação Proposicional de Estados (`OutcomeAt`, Linha 2055):** Definiu-se `OutcomeAt S (w : S.World) (out : Option (S.Node → Bool)) : Prop := SystemOutcomeAt S w = out`.
   - **Teorema de Incompatibilidade de Resultados no Mesmo Mundo (0 axiomas — `incompatible_outcomes_at_world`, Linha 2065):** Provou-se que para dois resultados distintos $out_1 \neq out_2$ avaliados no mesmo mundo $w$, `Incompatible (OutcomeAt S w out1) (OutcomeAt S w out2)` decorre da lógica pura de primeira ordem, garantindo que a divergência fáctica entre configurações constitui incompatibilidade lógica estrita.
   - **Representação Específica do Resultado Alternativo (`RepresentsAlternativeOutcome`, Linha 2075):** Definiu-se formalmente `RepresentsAlternativeOutcome S w out' q : Prop := (q → OutcomeAt S w out')`, estabelecendo uma relação formal que vincula o conteúdo proposicional da alternativa $q$ ao resultado alternativo concreto acessível do sistema.
   - **Espaços de Contraste Binário e Derivação por Polaridade (0 axiomas — `binary_contrast_space_entails_polarity_alternative`, Linha 2090):** Provou-se que em sistemas onde os resultados acessíveis formam uma partição binária (`BinaryContrastSpace S w_alt out_alt out_act := ∀ out, out ≠ out_alt → out = out_act`), a negação contraditória $\neg \text{OutcomeAt } S \ w_{\text{alt}} \ out_{\text{alt}}$ acarreta e representa univocamente o resultado fáctico do mundo actual $out_{\text{act}} = \text{SystemOutcomeAt } S \ S.\text{actualWorld}$.
   - **Estrutura de Realização Ação-Teórica Fortalecida (`AgentialActionRealization`, Linha 2105):** Articula a determinação causal do candidato à acção intencional originária de um sujeito pessoal $s : \text{Subject}$ (`originating_act : Act s (OutcomeAt S w out)`), incorpora como compromisso metafísico explícito que o agente co-significa o resultado actual saliente face ao qual diverge (`contrastive_alternative : Means s (OutcomeAt S w_alt out_act)`), e exige que a reflexão de escolha consuma especificamente proposições que representem a alternativa fáctica (`choice_reflection`).
   - **Derivação Rigorosa da Escolha com Uso Substantivo de `hAcc` e `hDiff` (0 axiomas — `agential_determination_entails_choice_derived`, Linha 2125):** Provou-se no kernel que para qualquer candidato com realização acção-teórica, a determinação de um resultado divergente $out_{\text{alt}}$ em mundo acessível ($hAcc$) com $hDiff : out_{\text{alt}} \neq out_{\text{act}}$ acarreta estritamente escolher esse resultado contra a alternativa concreta do mundo actual. Todas as hipóteses (`hAcc`, `hDiff`, `hDet`, `hReal`) são activamente consumidas, com código morto rigorosamente zero.
   - **Derivação Independente via AxActPolarity em Espaços Binários (0 axiomas — `agential_determination_entails_choice_in_binary_contrast_space`, Linha 2145):** Provou-se no kernel que sob `BinaryContrastSpace`, `AxActPolarity` (`Choice.lean:790`) fornece construtivamente a representação da alternativa real a partir da negação contraditória, derivando a escolha agencial contrafactual sem premissas adicionais.
   - **Refutação Estrita no Modelo B (`non_choosing_personal_model_violates_agential_determination_entailment`, Linha 5075):** Demonstrou-se com 0 axiomas que o agente dissociado $T_{\text{det}}$ (que determina o resultado em $w = \text{false}$ sem o escolher) viola estritamente a implicação directa `AgentialDeterminationEntailsChoice`, comprovando a não-vacuidade e a força substantiva da ponte agencial.
- **Transparência Epistemológica da Cadeia:**  
  Distingue-se com total clareza:  
  (a) A **validade dedutiva matemática** dos teoremas no kernel do Lean 4;  
  (b) A **justificação filosófica** das premissas e pontes cosmológicas explicitadas nos tratados;  
  (c) O **estatuto condicional** da existência da testemunha para um sistema específico $S$, evitando qualquer reivindicação indevida de fecho incondicional absoluto.

#### 4. Verificação de Casos-Limite e Satisfabilidade Conjunta Tri-Modal (Secção III-F.2)
Para responder cabalmente à auditoria de casos-limite, construiu-se o sistema `triModalS` com três mundos acessíveis exaustivos:
1. $w_{\text{Actual}}$: mundo actual instanciado, com configuração $c_0$ (`true`);
2. $w_{\text{Divergent}}$: mundo alternativo instanciado, com configuração divergente $c_1 \neq c_0$ (`false`);
3. $w_{\text{Uninstantiated}}$: mundo alternativo **não-instanciado**, com resultado `none`.

Demonstrou-se no kernel do Lean 4 com **0 axiomas além das fundações padrão** (`tri_modal_principles_jointly_satisfiable`):
- `ContingentSystem triModalS` (abrangendo simultaneamente a contingência por não-instanciação e por configuração divergente);
- `UniversalOutcomePSR triModalS triModalPriority` (explicando tanto $c_0$, como $c_1$, como a não-instanciação `none`);
- `UltimateGroundExplanatoryScope triModalS triModalT triModalPriority`;
- `AgentialDeterminationIsChoice triModalS triModalT`;
- `ActsFreely triModalS triModalT`.

Isto comprova definitivamente que a admissão de mundos não-instanciados é plenamente compatível com a contingência, com o PSR ontológico e com a dedução da liberdade agencial da Fonte.

#### 4. Demarcação Metafísica de `DeterminationAsOnticCondition`
A evasão leibniziana/intelectualista pretende que a escolha do fundamento é integral e univocamente determinada pelo perfil das melhores razões, mas que essas razões "não contam" como condição ontológica prévia na ordem de prioridade.
- **Estatuto Epistemológico:** `DeterminationAsOnticCondition` (com o alias canónico `ExplanatorySubsumptionOfDetermination`) é demarcada explicitamente como uma ponte metafísica substantiva (`Tag: META`). Reconhece-se com rigor que ela não decorre da pura lógica de primeira ordem nem de uma definição analítica trivial, pois liga predicados modais avaliativos (`ReasonsFavor`, `ChoosesOutcomeAt`) à relação de ordem constitutiva (`ConstitutivePriority`).
- **Justificação Filosófica:** Expressa o princípio anti-evasão segundo o qual qualquer perfil de condições que determine de forma unívoca e suficiente a acção de um fundamento constitui forçosamente uma dependência ontológica determinante na ordem de fundamentação (`condition ≺ candidate e`).
- **Dilema Resultante:**
  - Se for integrada no grafo, a determinação por razões conduz à necessitação rígida (se for intrínseca à essência) ou à perda de ultimidade/circularidade (se for extrínseca), fechando a evasão leibniziana (`deepened_intellectualist_evasion_closure`, `intellectualist_control_model_violates_ontic_conditioning`);
  - Se for rejeitada pelo determinista, este é forçado a assumir a tese insustentável de que uma determinação factual completa não desempenha papel explicativo na ordem ontológica do ser.
- **Visibilidade de Hipóteses:** O princípio permanece mantido como parâmetro formal explícito e transparente (`hCond`) no Teorema Mestre.

#### 5. Os Teoremas Mestres Consolidados Aprofundados
Estes princípios culminam nos teoremas mestres de fecho ontológico:
- `deepened_contingent_system_derives_free_personal_source_of_entails`: deduz `FreePersonalSource S T` a partir da implicação estrita `AgentialDeterminationEntailsChoice`;
- `deepened_contingent_system_derives_free_personal_source`: sobrecarga canónica consumindo o bicondicional `AgentialDeterminationIsChoice`;
- `deepened_contingent_system_with_psr_derives_free_personal_source`: corolário existencial sob testemunho fundado aprofundado (`DeepenedMetaphysicallyGroundedWitness`);
- `deepened_consolidated_free_personal_source_of_entails` e `deepened_consolidated_free_personal_source`: consolidam a dedução simultânea da existência necessária de uma Fonte Transcendente, Necessária, Pessoal e Livre (`FreePersonalSource S T`) e a exclusão formal irrevogável de todo e qualquer determinismo racional/mecanicista:
  $$\neg (\text{CompleteRationalDetermination } S \ T \lor \text{UnifiedRationalActualization } S \ T)$$
com **0 axiomas além da lógica clássica fundamental** (`propext`, `Classical.choice`, `Quot.sound`).

Deste modo, tanto na dimensão matemática do kernel como no tratado filosófico, o argumento fecha de modo transparente, rigoroso e auditável.

---

## 5. Relatório de Auditoria dos 6 Pontos: Dedução Eliminativa e Fronteira Formal da Escolha Agencial

Em estrito cumprimento do método eliminativo de Sherlock Holmes e das directrizes metodológicas do projecto (Seção 6), este relatório documenta com transparência matemática e filosófica total a dedução eliminativa pura, as alternativas excluídas e a fronteira formal exata onde a eliminação causal encontra a teoria da acção.

### 5.1 Premissas Substantivas e Suas Justificações Independentes
A dedução eliminativa existencial (`eliminative_existential_derives_unforced_personal_agent`) repousa unicamente sobre premissas cosmológicas e estruturais estabelecidas e justificadas no tratado:
1. `ContingentSystem S`: O facto modal da contingência cósmica (a realidade concreta admite alternativas acessíveis onde diverge ou não é instanciada).
2. `GeneralContrastivePSR S`: O Princípio da Razão Suficiente Contrastivo Geral que rejeita factos brutos contingentes, assegurando a existência de um fundamento factual que fornece justificação contrastiva.
3. `prior_wf` e `prior_trans`: A bem-fundação e transitividade da ordem ontológica de prioridade constitutiva, excluindo regresso infinito e ciclos de fundamentação (`well_founded_irrefl`).
4. `hConstitutiveOfTotality` e `hInternalGroundsTotality`: A fundamentação ontológica da totalidade exige prioridade estrutural sobre ela; nós internos são constitutivos da totalidade e não podem auto-fundamentá-la sem circularidade.
5. `GroundingTotalityTerminatesInAseity S T`: O princípio metafísico de que o fundamento explicativo último da totalidade contingente possui existência necessária (Aseidade).
6. `ImpersonalAseityPreservesNature S T`: A invariância da essência necessária de um candidato impessoal entre mundos acessíveis.
7. `ExplanatorySymmetryPrinciple S T ConstitutivePriority`: A condição de diferença de Lipton e o princípio de simetria de Leibniz — um fundamento impessoal de essência estritamente invariante não pode explicar resultados contingentes divergentes sem uma condição extrínseca diferenciadora.
8. `ExplanatoryUltimacyRequirement S ConstitutivePriority`: A auto-suficiência do fundamento cósmico último — não pode ser condicionado por uma entidade independente prévia.
9. `PersonalAseityPreservesNature S T`: A preservação da essência necessária pessoal através de mundos acessíveis.
10. `DeterminationAsOnticCondition S T ConstitutivePriority`: Qualquer perfil de condições ou razões que determine univocamente a actuação do fundamento funciona como condição ontológica na ordem de prioridade.
11. `FoundationalCausalDetermination S T ConstitutivePriority`: A determinação factual opera com acesso causal aos nós terminais do sistema.

### 5.2 Alternativas Excluídas e Teoremas de Refutação
O espaço modal de explicações para o sistema contingente é particionado em 5 níveis exaustivos e não-circulares, sendo cada ramo não-livre formalmente refutado no kernel por um teorema do projecto:
- **Modo 1 (Terminação Interna):** O fundamento é um nó interno $n \in S.\text{Node}$.  
  *Refutação:* `candidate_ground_must_be_structurally_external` (linha 571, 0 axiomas) demonstra que qualquer nó interno que fundamentasse a totalidade geraria o ciclo $n \prec S \prec n$, violando a irreflexividade da bem-fundação.
- **Modo 2 (Determinação Consequente-Dependente):** O fundamento depende de uma condição ontológica condicionada pelo próprio sistema que ele fundamenta ($e \prec S \prec C \prec e$).  
  *Refutação:* `candidate_consequence_circularity_refutation` (linha 340, 0 axiomas) demonstra que tal dependência induz auto-fundamentação $e \prec e$, contradizendo `well_founded_irrefl`.
- **Modo 3 (Condição Independente):** A actuação do candidato depende de uma condição extrínseca independente ($C \prec e \land \neg(S \prec C)$).  
  *Refutação:* `independent_condition_contradicts_ultimacy` (linha 1217, 0 axiomas) demonstra que isto destrói a ultimidade auto-suficiente do fundamento, reduzindo-o a uma causa intermediária.
- **Modo 4 (Necessitação Rígida):** O fundamento necessita rigidamente o universo em todos os mundos acessíveis (`NecessitatingMode S T`).  
  *Refutação:* `necessary_impersonal_ground_contradicts_contingency` (linha 1092, 0 axiomas) demonstra que a necessitação rígida por um fundamento necessário anula a contingência genuína de $S$.
- **Modo 5 (Determinação Impessoal Contingente):** O fundamento é impessoal e tenta explicar a contingência sem necessitação rígida.  
  *Refutação:* `impersonal_ground_forces_consequence_or_independent_condition` (linha 1503, 0 axiomas além de simetria) demonstra que a simetria de essência impessoal força o candidato a apelar a uma condição extrínseca, colapsando obrigatoriamente no Modo 2 (circularidade) ou no Modo 3 (perda de ultimidade).
- **Modo 6 (Facto Bruto / Alternativa Injustificada):** A alternativa contingente não possui justificação explicativa.  
  *Refutação:* `unjustified_alternative_fails_contrastive_at` (linha 1115, 0 axiomas) demonstra contradição directa com a garantia contrastiva do PSR.
- **Modo 7 (Forçagem por Antecedentes / Determinismo Racional):** O fundamento é um agente pessoal, mas a sua escolha é univocamente determinada por razões antecedentes ou pelo estado prévio completo.  
  *Refutação:* `deepened_intellectualist_evasion_closure` (linha 2969, 0 axiomas além de condicionamento ôntico) demonstra que sob `DeterminationAsOnticCondition`, as razões antecedentes funcionam como condição ôntica ($C \prec e$), recaindo no dilema entre circularidade e perda de ultimidade.

### 5.3 O Sobrevivente Demonstrado e a Fronteira Formal da Escolha Agencial
- **O Teorema Eliminativo Puro (`eliminative_deduction_of_unforced_personal_agent` e `eliminative_existential_derives_unforced_personal_agent`):**  
  Demonstra conclusivamente com **0 premissas de ponte e 0 axiomas espúrios** que o fundamento cósmico de qualquer sistema concreto contingente tem de ser um **Agente Pessoal Transcendente, Necessário, de Natureza Invariante, Último e Não-Forçado por Antecedentes**.
- **A Fronteira Formal com `FreePersonalSource`:**  
  A estrutura `FreePersonalSource S T` (linha 3256) exige cumulativamente dois predicados positivos de escolha: `SelectsIntentionally S T` (escolha intencional no mundo actual) e `ActsFreely S T` (escolha contrafactual no mundo alternativo divergente). Na sintaxe da estrutura `CandidateGround S` (linha 528), o campo `ChoosesOutcomeAt` foi formulado como um predicado desacoplado e independente de `DeterminesOutcomeAt`.
  Como comprovado no kernel pelo Modelo B (`T_det`, linha 5009) e pelo modelo fortificado (`fortified_rational_intellectualist_control_model`, linha 2396), essa independência sintática permite definir formalmente registros onde a determinação causal é verdadeira mas a escolha é assinalada como falsa por estipulação livre (`ChoosesOutcomeAt := fun _ w out => w = true ...`).
  Portanto, **a passagem da determinação agencial não-forçada para os predicados de escolha `ChoosesOutcomeAt` marca a fronteira exata entre a eliminação causal-cosmológica e a teoria da acção intencional**.

### 5.4 Não-Circularidade das Partições
As 5 partições utilizadas são rigorosamente estruturais e lógicas:
1. `T.ground = internal n ∨ (∃ e, T.ground = external e)` (casos de `GroundIdentity`);
2. `ConsequenceDependentDetermination ∨ IndependentConditionMode ∨ IsUltimateGround` (tricotomia ontológica);
3. `NecessitatingMode ∨ UnjustifiedContrastiveAlternativeAt ∨ GuidedByJustificationMode` (provado em `grounding_modes_exhaustive`);
4. `IsImpersonal S T ∨ IsPersonalAgent S T` (lei do terceiro excluído via `IsImpersonal := ¬ IsPersonalAgent`);
5. `(CompleteRationalDetermination ∨ UnifiedRationalActualization) ∨ ¬ (CompleteRationalDetermination ∨ UnifiedRationalActualization)` (lei do terceiro excluído).
Nenhuma destas partições insere o predicado de escolha (`ChoosesOutcomeAt`) nem a conclusão desejada (`FreePersonalSource`) no conjunto inicial de alternativas.

### 5.5 Auditoria dos Contra-Modelos do Repositório
- **Modelo A (`rivalS`, linha 4580):** Confirma a necessidade da unicidade cosmológica do fundamento, provando que múltiplos fundamentos independentes satisfazem o PSR neutro mas quebram o escopo universal sem a unicidade modal de $\Gamma$.
- **Modelo B (`T_det`, linha 5009):** Testemunha com 0 axiomas (`non_choosing_personal_model_violates_agential_determination_entailment`, linha 5075) o desacoplamento sintático entre determinação e escolha em `CandidateGround`, justificando por que a teoria da acção (`AxIntentionalChoice`) é a ponte conceitual necessária para unificar causalidade e escolha.
- **Modelo C (`boundaryS`, linha 5100):** Confirma com 0 axiomas (`unfounded_boundary_model_fails_causal_determination`) que a omissão de fundamentação sobre nós terminais de fronteira destrói a determinação causal fundacional.
- **Modelo de Controlo Intelectualista (`countermodelT`, linha 2396):** Demonstra formalmente que o determinismo racional não pode sobreviver uma vez integrada a integridade da determinação ôntica (`DeterminationAsOnticCondition`).

### 5.6 Footprint de Axiomas e Integridade do Repositório
- **Axiomas Auditados:** Os teoremas eliminativos puros dependem unicamente de `[propext, Classical.choice, Quot.sound]`.
- **Censo de Axiomas:** Exactamente 40 axiomas declarados (18 VOCAB, 6 SEM, 13 META, 3 TRANS), aprovados pelo script `test_axiom_census.py`.
- **Portão de Consistência:** Aprovado em todos os 4 portões (`check_consistency.py`).
- **Lake Build:** 110 módulos compilados com 0 erros e 0 avisos.

---

## 6. Auditoria Rigorosa de Fecho: Reparação de Prioridade, Teoria da Acção e Liberdade Positiva (Parte E)

Esta secção formaliza o relatório transparente e honesto dos cinco pontos fundamentais exigidos pelo mandato do projecto, detalhando o estado exato da dedução eliminativa, a reparação das hipóteses de prioridade, a teoria da acção de $\Gamma$, a derivação da liberdade contrafactual positiva e o estatuto do Modelo B (`T_det`).

### 6.1 Ponto 1: Premissas Cosmológicas Explícitas do Teorema Eliminativo Puro
O teorema eliminativo existencial puro (`eliminative_existential_derives_unforced_personal_agent`) deduz no kernel do Lean 4 a existência necessária de um Agente Pessoal Incauasado, Transcendente e Não-Forçado a partir exclusivamente de fundações cosmológicas e estruturais, com **zero premissas acção-teóricas ou pontes de escolha**:
1. `ContingentSystem S`: O facto ontológico fundamental da contingência da realidade concreta (admissibilidade de mundos acessíveis divergentes ou não-instanciados).
2. `prior_wf` e `prior_trans`: A bem-fundação estrita (exclusão de ciclos e regressos infinitos) e a transitividade da prioridade constitutiva ontológica.
3. `hConstitutiveOfTotality`: A prioridade ontológica intrínseca dos nós constitutivos sobre a totalidade do sistema ($n \prec S$).
4. `hInternalGroundsTotality` (condicionada): Se um candidato a fundamento for interno a um nó $n$, a fundamentação da totalidade impõe que a totalidade dependa desse nó ($S \prec n$).
5. `hGroundsTotality` (escopada): O fundamento externo da totalidade do sistema é ontologicamente prévio à totalidade ($e \prec S$).
6. `GeneralContrastivePSR S`: O Princípio da Razão Suficiente Contrastivo Geral que garante que a totalidade concreta de $S$ possui um fundamento ontológico explicativo.
7. `hAseity` (escopada): O fundamento que termina a cadeia explicativa de uma totalidade contingente existe necessariamente em todos os mundos acessíveis.
8. `hAseityNature` (escopada): A essência necessária de um candidato impessoal é invariante através do espaço modal acessível.
9. `hSymmPrinciple` (escopada): Princípio de Simetria Explicativa de Leibniz — fundamentos impessoais invariantes não podem produzir resultados contingentes assimétricos sem diferenciação extrínseca.
10. `hUltRequirement` (escopada): A ultimidade auto-suficiente do fundamento cósmico — um fundamento último não pode depender de uma condição independente prévia.
11. `hPersonalNature` (escopada): A preservação da essência necessária pessoal através dos mundos acessíveis.
12. `hCond` (escopada): Princípio de Subsumpção Ôntica — qualquer fixação univocamente determinada por razões antecedentes funciona como condição prioritária no domínio constitutivo.
13. `hCausal` (escopada): Determinação Causal Fundacional — o fundamento possui acesso causal aos nós terminais de fronteira do sistema.

### 6.2 Ponto 2: Dependências Exatas e Reparação Não-Contraditória (Parte A)
A auditoria estrutural do teorema eliminativo existencial corrigiu deficiências críticas de escopo que tornavam o conjunto de premissas contraditório em sistemas habitados:
1. **Reparação da Hipótese de Prioridade Interna (`hInternalGroundsTotality`):**
   - Na formulação anterior, `hInternalGroundsTotality` afirmava incondicionalmente `∀ n, totality ≺ node n`. Em conjunção com `hConstitutiveOfTotality` (`node n ≺ totality`), isto criava um 2-ciclo imediato sob bem-fundação sempre que $S.\text{Node}$ fosse habitado.
   - A formulação reparada condiciona estritamente a relação à identidade interna do candidato obtido pelo PSR:
     ```lean
     hInternalGroundsTotality : ∀ (T : CandidateGround S),
       T.GroundsConcreteActuality T.ground S.actualWorld →
       (∀ w_alt : S.World, S.Accessible S.actualWorld w_alt → ...) →
       ∀ (n : S.Node), T.ground = GroundIdentity.internal n →
       ∀ Ext, ConstitutivePriority Ext CandidateOnticItem.totality (CandidateOnticItem.node n)
     ```
   - No corpo da demonstração, a especialização a `T` preserva a igualdade de hipótese `T.ground = internal n`, de modo que quando $T$ é provado externo (`T.ground = external e`), o ramo interno é eliminado por contradição sem criar ciclos no ramo externo sobrevivente.
2. **Generalização de `dualPriority` e Inclusão de Relatores:**
   - `dualPriority` foi generalizado para ser polimórfico através de todos os tipos de extensão de candidatos `Ext : Type 0`, contendo os construtores `candidate_node`, `candidate_totality`, e `node_totality`.
   - Provou-se no kernel a bem-fundação (`dualPriority_wf`) e a transitividade (`dualPriority_trans`).
3. **Escopo de Hipóteses Universais sobre Candidatos:**
   - Todas as hipóteses sobre candidatos (`hAseity`, `hAseityNature`, `hSymmPrinciple`, `hPersonalNature`, `hCond`, `hCausal`) foram condicionadas a `T.GroundsConcreteActuality T.ground S.actualWorld`, evitando quantificação universal sobre registros arbitrários ou adversariais.
4. **Verificação de Regressão Não-Vácua (`dualWorldS_satisfies_existential_premises`):**
   - Demonstrou-se formalmente no kernel com 0 axiomas espúrios que `dualWorldS` (onde `Node := Unit` é habitado), `dualWorldT`, e `dualPriority` satisfazem a totalidade das premissas de `eliminative_existential_derives_unforced_personal_agent` construtivamente e sem recorrer a *ex falso*.

### 6.3 Ponto 3: A Teoria da Acção Fundacional de $\Gamma$ e a Agência Cósmica (Parte B)
A dedução da escolha e da liberdade intencional a partir da acção assenta na teoria geral da agência desenvolvida em `formal/Logos/Agency.lean` e `formal/Logos/Choice.lean`:
1. **Disciplina Categorial e Agência Divina:**
   - Em $\Gamma$, o fundamento último do ser é `Entity.ofGround` (`divineReality`). Pelo teorema `ofGround_ne_ofSubject` (`FoundationalUnicity.lean:134`, `NecessityEternity.lean:160`, `DivineClassicalAttributes.lean:190`; note-se que `Entity.lean:28-35` introduz `EntityOf` e a disjunção de construtores `ofGround_ne_ofAtom`), `EntityOf s ≠ Entity.ofGround` para qualquer Sujeito $s$. O fundamento não é um quarto sujeito finito (`ground_is_not_a_fourth_chooser : ¬ Asiety Entity.ofGround`, `DivineTrinitarianAttributes.lean:2759`).
   - A agência pessoal do fundamento é instanciada pelas Pessoas divinas que são Sujeitos necessários (`TrinitarianPersonalBridge`, `DivineTrinitarianAttributes.lean:270`), cuja relação essencial com o fundamento é expressa por `PersonalGround Entity.ofGround` (linha 2940).
2. **Definição Constitutiva da Acção e Escolha:**
   - Toda a acção intencional é um acto de iniciação por um sujeito: `Act s p := Means s p ∧ ∃ w w' : State, Initiates s w w' p`.
   - Pelo axioma semântico constitutivo `AxIntentionalChoice` (`Choice.lean:779`, Tag: SEM), todo o acto intencional envolve constitutivamente a apreensão e co-significação de uma alternativa incompatível: `Act s p → ∃ q, Chooses s p q`.
   - Pelo axioma semântico `AxActPolarity` (`Choice.lean:790`, Tag: SEM), iniciar um acto significa constitutivamente a negação contraditória do estado: `Act s p → Means s (¬ p)`, o que produz a escolha polar imediata `Chooses s p (¬ p)` e conclui o Sujeito Livre (`FreeSubject s`).
3. **Insuficiência da Mera Não-Mecanicidade:**
   - O teorema central `freedom_is_not_merely_unforced` (`CompleteLibertarianFreedomArgument.lean:892`) prova no kernel que a mera ausência de determinação mecânica ou determinismo racional (`¬ MechanicallyForced`) **não acarreta por si só a liberdade positiva (`¬ FreeSubject`)**.
   - A liberdade libertária positiva exige constitutivamente a presença positiva do acto de escolha intencional entre alternativas incompatíveis.

### 6.4 Ponto 4: Derivação da Liberdade Contrafactual Positiva e Relação de Produção Limpa (Parte C)
A integração entre o fundamento cósmico unificado e a teoria da acção é formalizada pelos teoremas mestres, expurgados de atalhos e rigorosamente ancorados em actos intencionais:
1. `TranscendentAgentialActionCorrespondence S T`: Estrutura de correspondência ontológica estrita onde a determinação do resultado cósmico `T.DeterminesOutcomeAt` é a realização de um acto originante `Act agent (OutcomeAt S w out)` da Pessoa divina fonte (`DivineRole.source`), e `T.ChoosesOutcomeAt` reflecte a escolha intencional `Chooses agent`.
   - **Remoção de Atalhos (`toy_model`):** O construtor `toy_model` foi **completamente eliminado da relação de produção**, impedindo que qualquer demonstração mestre assuma que determinação e escolha simplesmente coincidem por estipulação booleana.
   - **Especificidade de Resultado e `AxActPolarity`:** Em espaços de contraste binários, o teorema `binary_contrast_space_entails_polarity_alternative` prova que a negação polar `¬ OutcomeAt S w_alt altOutcome` fornecida por `AxActPolarity` representa estritamente o resultado alternativo concreto `actualOutcome`. Isto assegura que a escolha contrafactual não apela a uma proposição incompatível arbitrária, mas selecciona especificamente a configuração contrafactual exigida por `ActsFreely`.
2. `agential_determination_entails_choice_derived_from_action_theory`: Deduz no kernel de Lean 4 que qualquer candidato que instancie a correspondência agencial transcendente satisfaz `AgentialDeterminationEntailsChoice S T` directamente a partir de `AgentialActionRealization` e `AxIntentionalChoice`, com 0 axiomas adicionais.
3. `eliminative_deduction_derives_free_personal_source`:
   - Constrói `SelectsIntentionally S T` a partir da determinação originante do mundo actual e da justificação contrastiva via `agential_action_grounding_derives_selects_intentionally`.
   - Constrói `ActsFreely S T` provando a soberania agencial sobre alternativas acessíveis divergentes através do PSR neutro (`UniversalOutcomePSR`) e do escopo explicativo (`UltimateGroundExplanatoryScope`).
   - Reúne conclusivamente os 6 atributos da Fonte Pessoal Livre: externalidade estrutural, necessidade, invariância de essência, agência pessoal, selecção intencional e liberdade contrafactual positiva, formalmente excluindo a evasão intelectualista (`¬ (CompleteRationalDetermination ∨ UnifiedRationalActualization)`).
4. `eliminative_foundation_derives_free_personal_source`:
   - Formula o teorema de integração mestre existencial desmembrando integralmente as suas premissas: consome o PSR puramente cosmológico (`GeneralContrastivePSR S`), o escopo explicativo (`UltimateGroundExplanatoryScope`) e a correspondência agencial (`TranscendentAgentialActionCorrespondence`) como premissas separadas e transparentes, **sem recorrer ao empacotamento artificial de um pseudo-PSR agencial (`hAgentialPSR`)**.
   - O teste de regressão `dualWorldS_satisfies_free_personal_source_premises` certifica com 0 axiomas que o conjunto de premissas instancia directamente todos os seis atributos de `FreePersonalSource` no sistema habitado `dualWorldS` via `dualWorldT`, sem depender de qualquer atalho de correspondência sintética.

### 6.5 Ponto 5: O Estatuto Formal Irredutível e a Exclusão do Modelo B (`T_det`) (Partes D e E)
1. **O Testemunho Formal de Independência do Modelo B (`T_det`):**
   - O Modelo B (`T_det`, linha 5576; provado em `non_choosing_personal_model_violates_agential_determination_entailment`, linha 5640) é um habitante concreto e matematicamente válido de `CandidateGround dualWorldS`.
   - `T_det` satisfaz todas as premissas puramente cosmológicas do teorema eliminativo (é externo, necessário, pessoal, invariante, último, guiado por justificação contrastiva e determina o resultado em todos os mundos). Contudo, estipula arbitrariamente `ChoosesOutcomeAt () false out := False`, negando a liberdade contrafactual (`¬ ActsFreely`).
   - Isto constitui uma **demonstração matemática rigorosa no kernel de que, na estrutura abstrata e desinterpretada de `CandidateGround`, a escolha intencional é formalmente independente da determinação causal**.
2. **A Exclusão Formal do Modelo B pela Teoria da Acção (`model_b_violates_transcendent_action_correspondence` e `model_b_violates_action_theory_of_agency`):**
   - O teorema `model_b_violates_transcendent_action_correspondence` prova formalmente que `T_det` **não pode instanciar a correspondência agencial transcendente de $\Gamma$**: se a determinação causal em `false` fosse um acto originante de um agente (`Act s p`), o axioma constitutivo `AxIntentionalChoice` exigiria a presença de escolha (`Chooses s p q`), entrando em contradição imediata (`false = true`) com a estipulação `ChoosesOutcomeAt = False`.
   - O teorema reforçado `model_b_violates_action_theory_of_agency` generaliza esta refutação, demonstrando que **nenhum sujeito racional $s$ pode instanciar uma realização de acção para `T_det`**: `∀ s : Subject, ¬ AgentialActionRealization dualWorldS T_det s`.
   - O Modelo B é assim desmascarado como um **artefacto sintático livre desprovido de coerência semântica**, análogo aos modelos mutilados excluídos em `AGENTS.md` (2026-09-29): ele postula agência pessoal e determinação causal enquanto recusa a lei semântica que define constitutivamente o conceito de acção.

### 6.6 Ponto 6: Demarcação e Derivação do Escopo Explicativo do Fundamento Último
1. **Fundamentação Universal da Realidade vs. Escopo Explicativo Específico do Sistema:**
   - Em `formal/Logos/DivineClassicalAttributes.lean:1725`, o teorema `universal_ground_unicity` e `UniversalModalGround g` provam que toda a entidade existente na realidade ontológica é fundamentada pelo fundamento universal único $g = \text{Entity.ofGround}$.
   - Contudo, num sistema concreto arbitrário $S$, o princípio `UltimateGroundExplanatoryScope S T ConstitutivePriority` exige uma propriedade relacional explicativa adicional: que se qualquer candidato $T'$ explica um resultado de $S$ num mundo alternativo acessível $w_{\text{alt}}$, o próprio fundamento $T$ explica esse resultado.
   - O Modelo A (`rivalS`, linha 5040; provado em `rival_ground_model_satisfies_neutral_psr_but_fails_scope`, linha 5170) demonstra no kernel que a fundamentação universal da realidade **não acarreta analiticamente o escopo explicativo específico de $S$**: um sistema contingente pode ter todos os seus mundos explicados por candidatos distintos ($T_{\text{main}}$ no mundo actual e $T_{\text{rival}}$ no mundo alternativo) sem que o candidato actual explique as alternativas.
2. **As Duas Vias Legítimas para o Escopo:**
   - **Via A (Dedução via Transmissão Explicativa):** No teorema `universal_ground_chain_terminus_unicity` (linha 2010), prova-se sob um homomorfismo de prioridade (`PriorityGroundingHomomorphism`) que o término de qualquer cadeia explicativa é o fundamento universal único $g$. Para passar da unicidade do término para a explicação do resultado concreto, o teorema `mediated_scope_to_ultimate_scope_under_transmission` (linha 1975) deduz `UltimateGroundExplanatoryScope` a partir do **Princípio de Transmissão Explicativa** (`ExplanatoryTransmission S T ConstitutivePriority`), segundo o qual a eficácia explicativa de causas secundárias intermediárias se transmite à causa primeira.
   - **Via B (Ponte Metafísica Explícita):** O princípio pode ser mantido de forma transparente como uma premissa metafísica declarada (`UltimateGroundExplanatoryScope`), tornando explícito o compromisso cosmológico de que a explicação última de qualquer estado contingente do cosmos é subsumida pela mesma Fonte foundational.
3. **Conclusão Metodológica Honesta:**
   - O escopo explicativo não é iludido nem disfarçado como um corolário analítico trivial da unicidade do fundamento universal. A distinção entre fundamentação de entidades e escopo explicativo de configurações de sistemas é explicitamente demarcada, preservando a disciplina epistemológica integral do projecto $\Gamma$.

---

## 7. Resposta Definitiva aos Cinco Critérios Finais de Aceitação (Quest 1xGYNs)

Em estrito cumprimento das directrizes de integridade e auditoria formal, este relatório final sintetiza as conclusões ontológicas, formais e acção-teóricas relativas às duas conexões remanescentes:

### 7.1 Critério 1: O Que o Teorema Eliminativo Puro Estabelece (Tier 1 — Cosmológico Puro)
O teorema `eliminative_existential_derives_unforced_personal_agent` (`OntologicalIncompletenessTheorem.lean:4187`) constitui o cume eliminativo cosmológico rigorosamente estabelecido:
- **Enunciado Formal:** $\exists T : \text{CandidateGround } S$, $T$ é estruturalmente externo, necessário, de essência invariante, um agente pessoal, fundamento último em prioridade constitutiva, guiado por justificação contrastiva e formalmente não-forçado por determinismo racional ($\neg(\text{CRD} \lor \text{URA})$).
- **Pegada no Kernel:** `[propext, Classical.choice, Quot.sound]`.
- **Pureza Fundacional:** **Zero axiomas substantivos** de $\Gamma$, zero dependência de teoria da acção (`Agency.Subject`, `Means`, `Initiates`), zero premissas de escolha (`Choice`).
- **Satisfabilidade Construtiva Não-Vácua:** Provada no sistema habitado `dualWorldS` (com nós reais habitados `Node := Unit`) através de `dualWorldS_satisfies_existential_premises` (linha 5195) com 0 axiomas e sem apelo a *ex falso*.

### 7.2 Critério 2: Derivação do Escopo Explicativo, Limites da Unicidade Modal e Concursus Divinus
- **Derivação Rigorosa via Transmissão:** O teorema `eliminative_deduction_derives_free_personal_source_under_transmission` (linha 4330) deduz com sucesso a Fonte Pessoal Livre substituindo a hipótese primitiva de escopo direto por duas premissas estruturais:
  1. `MediatedExplanatoryScope S T ConstitutivePriority`: toda a explicação local por causas secundárias $T'$ liga-se a $T$ por uma cadeia prioritária completa;
  2. `ExplanatoryTransmission S T ConstitutivePriority` (Tag: META): a eficácia explicativa de causas secundárias intermediárias numa cadeia completa transmite-se ao fundamento terminal $T$.
  O lema `mediated_scope_to_ultimate_scope_under_transmission` (linha 1975) fecha a dedução de `UltimateGroundExplanatoryScope` no kernel com 0 axiomas adicionais.
- **Limites da Unicidade Modal Nua e Teste de Independência do Modelo A:**  
  Demonstrou-se formalmente através do contra-modelo Modelo A (`rivalS`, `T_main`, `T_rival`, linha 5733; teorema `rival_ground_model_satisfies_neutral_psr_but_fails_scope`, linha 5852) que a unicidade modal de $Entity.ofGround$ no domínio ontológico de entidades (`UniversalModalGround`) **não acarreta analiticamente o escopo explicativo específico de $S$**. Em `formal/Logos/RecoveredOntologicalGround.lean:85`, `OneEssence g e` é estritamente definida como contenção intencional de significados (`∀ p, EntityMeans e p → EntityMeans g p`). A fundamentação ontológica do ser de uma causa secundária não impõe que o primeiro fundamento determine directamente as configurações contrafactuais operadas por essa causa secundária.
- **Justificação Filosófica Minimal e Conclusiva (Concursus Divinus):**
  - *Princípio:* *Causa secunda non agit nisi virtute causae primae* (Tomás de Aquino, *ST* I, q. 105, a. 5; *SCG* III, c. 67). Nenhuma entidade dependente possui poder causal auto-originado ou desvinculado do fundamento do ser.
  - *Objeção (Dilema de Durando / Colapso no Ocasionalismo):* Se a causa primeira transmite e explica todo o efeito, a causa secundária é supérflua (ocasionalismo de Malebranche) ou possui eficácia independente (Durando de Saint-Pourçain).
  - *Resposta:* A transmissão explicativa em $\Gamma$ é concorrência genuína (*concursus*): a causa secundária $T'$ é a causa imediata real da configuração, enquanto o fundamento primeiro $T$ é a condição ontológica e causal primária que sustenta a própria eficácia de $T'$.

### 7.3 Critério 3: Conexão entre Determinação Cósmica, Criação Originante e Teste de Independência do Modelo B
- **Eliminação Definitiva da Circularidade em `SelectsIntentionally`:**  
  O construtor de `TranscendentAgentialActionCorrespondence` não assume a escolha no mundo actual (`T.ChoosesOutcomeAt T.ground S.actualWorld out_act`). A escolha no mundo actual é **activamente deduzida** no teorema `agential_action_grounding_derives_actual_choice` (linha 2315):
  1. A determinação factual da actualidade pelo candidato (`actual_determination`) mapeia para o acto originante da Pessoa divina (`act_iff : Act agent out_act`), implicando `Means agent out_act`;
  2. A contingência de $S$ (`ContingentSystem S`) e a invariância da essência do fundamento (`NatureInvariant S T`) garantem a existência de uma alternativa divergente acessível $w_{\text{alt}}$ com $out_{\text{alt}} \neq out_{\text{act}}$;
  3. A condição de significado contrastivo na realização de acção (`actual_contrastive_alternative`, linha 2170) assegura `Means agent out_alt`;
  4. Pela constitutividade da escolha em $\Gamma$ (`Chooses agent out_act out_alt := Means out_act ∧ Means out_alt ∧ Incompatible`), deduz-se `Chooses agent out_act out_alt`;
  5. A reflexão de escolha generalizada e simétrica em `AgentialActionRealization` (`choice_reflection`, linha 2175) reflecte esta escolha intencional para a relação do fundamento: `T.ChoosesOutcomeAt T.ground S.actualWorld out_act`.
  O teorema `agential_action_grounding_derives_selects_intentionally` (linha 2355) deduz `SelectsIntentionally S T` com **zero circularidade**.
- **Limites da Teoria da Acção Central e Teste de Independência do Modelo B:**  
  Em `formal/Logos/DivineThomisticProduction.lean:117,173`, `Produces` opera sobre fórmulas proposicionais abstratas em semântica modal, e registra-se explicitamente que "a fundamentação universal não acarreta externalidade causal, e produção não é criação".
  O Modelo B ($T_{\text{det}}$, linha 5892; teoremas `model_b_violates_transcendent_action_correspondence`, linha 5986, e `model_b_violates_action_theory_of_agency`, linha 6008) funciona como um **teste real de independência ontológica**:
  - Demonstra que, no formalismo de `CandidateGround`, um fundamento pode determinar causalmente o cosmos sem exercer escolha intencional contrafactual (`¬ ActsFreely`);
  - Prova que `TranscendentAgentialActionCorrespondence S T` é uma ponte de acção genuína, substantiva e **não-redundante**, que conecta a causalidade cósmica ao acto criador da Pessoa divina.
- **Justificação Filosófica Minimal e Conclusiva (Creatio ex Voluntate):**
  - *Princípio:* A criação contingente é um acto livre da vontade divina (*ST* I, q. 19, a. 4; Duns Scotus, *Ordinatio* I, d. 8), não uma emanação logicamente forçada.
  - *Objeção (Evasão Intelectualista / Emanacionismo Espinozista):* Poderia o fundamento pessoal emanar o universo por necessidade natural da sua suprema perfeição intelectual sem eleição livre?
  - *Resposta:* A Secção 6 de `OntologicalIncompletenessTheorem.lean` refuta a necessidade natural (`necessary_ground_cannot_rigidly_necessitate_contingent_system`, linha 675; `intrinsic_rational_fixing_contradicts_contingency`, linha 1445): um princípio necessário que opere por necessidade de natureza torna o efeito estritamente necessário, refutando a premissa empiricamente dada `ContingentSystem S`. Logo, a actualização contingente de $S$ por um fundamento pessoal é constitutivamente uma eleição intencional livre.

### 7.4 Critério 4: A Hierarquia Formal de Teoremas em 3 Níveis
Estabeleceu-se uma hierarquia deductiva transparente e honesta em três patamares ontológicos:
1. **Tier 1 (Cume Eliminativo Cosmológico Puro):**  
   `eliminative_existential_derives_unforced_personal_agent` (linha 4187).  
   Deduz a existência necessária de um Agente Pessoal Transcendente Não-Forçado a partir exclusivamente do `GeneralContrastivePSR S` e de propriedades estruturais da prioridade constitutiva. Pegada no kernel: `[propext, Classical.choice, Quot.sound]`. Zero axiomas de $\Gamma$, zero premissas de acção.
2. **Tier 2 (Integração Intermédia sem Pontes de Transmissão ou Criação):**  
   `intermediate_existential_derives_unforced_personal_source` (linha 4367).  
   Conecta o agente cosmológico não-forçado ao fundamento modal universal $Entity.ofGround$ através de um homomorfismo de prioridade (`PriorityGroundingHomomorphism`) e às Pessoas divinas via `TrinitarianPersonalBridge`, garantindo estrita disciplina categorial (`EntityOf agent ≠ Entity.ofGround`, provado por `ofGround_ne_ofSubject`). Demarca formalmente que o escopo explicativo terminal e a liberdade contrafactual plena permanecem independentes deste patamar (testemunhados pelos Modelos A e B).
3. **Tier 3 (Teorema Pleno da Fonte Pessoal Livre):**  
   `eliminative_foundation_derives_free_personal_source_under_transmission` (linha 4567).  
   Deduz a existência de uma verdadeira Fonte Pessoal Livre (`FreePersonalSource S T`), dotada de todos os seis atributos divinos e liberdade contrafactual positiva (`ActsFreely S T`), quando as pontes independentes de Concursus Divinus (`ExplanatoryTransmission`) e Criação Intencional Originante (`TranscendentAgentialActionCorrespondence`) são fornecidas.

### 7.5 Critério 5: Grafo de Dependências Exato do Teorema Existencial Mestre
O fluxo dedutivo completo e auditado de $\Gamma$ estrutura-se rigorosamente:
$$\begin{aligned}
\text{ContingentSystem } S + \text{GeneralContrastivePSR } S &\implies \text{Eliminação dos 7 Ramos Concorrentes} \\
&\implies \text{Tier 1: Agente Pessoal Não-Forçado Necessário} \\
&\quad\quad \downarrow \ (+ \text{Homomorfismo de Prioridade} + \text{TrinitarianPersonalBridge}) \\
&\implies \text{Tier 2: Fundamento Pessoal Trinitário Transcendente} \\
&\quad\quad \downarrow \ (+ \text{ExplanatoryTransmission} + \text{TranscendentAgentialActionCorrespondence}) \\
&\implies \text{Tier 3: FreePersonalSource } S \ T \ (\text{Fonte Pessoal Positivamente Livre})
\end{aligned}$$

As únicas premissas que permanecem na interface mestre de integração existencial são:
1. `GeneralContrastivePSR S`: A premissa cosmológica que assegura que a totalidade contingente possui um fundamento explicativo;
2. `ExplanatoryTransmission S T ConstitutivePriority` (Tag: META): O princípio ontológico de causalidade concorrente pelo qual as causas secundárias transmitem a sua dívida explicativa ao fundamento terminal;
3. `TranscendentAgentialActionCorrespondence S T` (Tag: META): O princípio de criação intencional originante pelo qual a determinação factual do cosmos é o acto voluntário e intencional da Pessoa divina Fonte.

---

### 7.6 Tratado Filosófico Dedicado e Justificação Metafísica Exaustiva
A fundamentação filosófica rigorosa, análise histórica de fontes primárias (Tomás de Aquino, João Duns Scotus, G. W. Leibniz), refutação de objeções clássicas (Van Inwagen, Durando, Malebranche, Espinoza) e bibliografia detalhada das três premissas substantivas encontram-se exaustivamente desenvolvidas no tratado dedicado:
- **`investigations/philosophical_foundations_free_personal_source.md`**

