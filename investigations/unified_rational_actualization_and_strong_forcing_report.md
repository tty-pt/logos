# Relatório Metodológico e Ontológico: Actualização Ontológica Efectiva, o Dilema da Forçagem Forte e a Separação dos Cinco Níveis de Conclusão

**Data:** 11 de Outubro de 2026  
**Ficheiro Formal Auditado:** `OntologicalIncompletenessTheorem.lean` (raiz do repositório)  
**Teoremas Relevantes e Linhas de Código no Kernel:**
- `def ActualizesOutcomeAt`: Linha **1892**
- `structure EffectiveOntologicalActualization`: Linha **1914**
- `theorem countermodelT_effective_actualization`: Linha **1931**
- `theorem modal_necessitation_distinct_from_effective_actualization`: Linha **1978**
- `theorem effective_actualization_distinct_from_outcome_fixed`: Linha **1987**
- `theorem effective_actualization_compossible_with_non_forcing`: Linha **1999**
- `theorem effective_actualization_refutes_libertarian_freedom`: Linha **2028**
- `theorem five_levels_of_conclusion_separation`: Linha **2049**
- `theorem strong_forcing_dilemma_and_role_of_sovereignty`: Linha **2075**
- `theorem substantive_rational_intellectualist_control_model`: Linha **2112**
- Bloco `#print axioms` da Secção IV: Linhas **2520–2535**

---

## 1. Contexto e Enunciado do Problema

O teorema central da incompletude ontológica no tratado Γ estabelece que:
$$\text{chain\_cannot\_be\_exhaustively\_forced} : (\neg \text{SystemFullyInternallyDetermined } S) \land (\neg \text{NecessitatingMode } S \ T)$$
Ou seja, a cadeia de determinações não pode ser auto-explicada internamente sem circularidade constitutiva, nem pode a totalidade contingente ser rigidamente necessitada em todo o espaço modal por um fundamento necessário.

A questão crítica investigada é:
> **A modelação formal representa adequadamente a impossibilidade de a cadeia concreta ser forçada integralmente? A determinação dos nós terminais decorre verdadeiramente da escolha do fundamento ou resulta apenas da definição rígida de `GroundsConcreteActuality`? E pode o argumento ontológico excluir a determinação racional leibniziana sem já pressupor a liberdade libertária?**

---

## 2. Relação Geral de Actualização e Determinação Efectiva dos Nós Terminais

### 2.1. Desacoplamento da Fixação em `actualWorld` (`ActualizesOutcomeAt`, Linha 1892)
Anteriormente, `GroundsConcreteActuality ground w` continha a exigência estrita `ConfigurationIn w = ConfigurationIn actualWorld`, impedindo a modelação de actualizações contrafactuais divergentes.  
Definiu-se a relação geral:
```lean
def ActualizesOutcomeAt
    (S : ConcreteSystem.{u})
    (T : CandidateGround S)
    (w : S.World)
    (out : Option (S.Node → Bool)) : Prop :=
  T.ExistsAt T.ground w ∧ SystemOutcomeAt S w = out
```
Esta relação opera sobre qualquer mundo $w$ e qualquer resultado hipotético `out`, permitindo modelar resultados contrafactuais sem pressupor a actualidade.

### 2.2. A Estrutura de Actualização Efectiva (`EffectiveOntologicalActualization`, Linha 1914)
Para ligar organicamente a escolha (`ChoosesOutcomeAt`) à configuração global e demonstrar a determinação fáctica dos nós terminais:
```lean
structure EffectiveOntologicalActualization
    (S : ConcreteSystem.{u})
    (T : CandidateGround S) : Prop where
  choice_actualizes :
    ∀ (w : S.World) (out : Option (S.Node → Bool)),
      T.ChoosesOutcomeAt T.ground w out →
      ActualizesOutcomeAt S T w out
  terminal_determination :
    ∀ (w : S.World) (cfg : S.Node → Bool),
      T.ChoosesOutcomeAt T.ground w (some cfg) →
      ∀ b : S.Node, IsInternalTerminalNode S b →
        S.ConfigurationIn w b = cfg b
  actual_grounding :
    T.ChoosesOutcomeAt T.ground S.actualWorld (some (S.ConfigurationIn S.actualWorld)) ∧
    T.GroundsConcreteActuality T.ground S.actualWorld
  rational_governance :
    CompleteRationalDetermination S T
```

### Eficácia da Determinação Nodal:
- **Não-vácua e Geral:** `terminal_determination` estabelece uma lei universal: em qualquer mundo $w$ onde o fundamento escolhe a configuração `cfg`, todo o nó terminal interno $b$ (`IsInternalTerminalNode S b`, isto é, sem determinação interna) toma necessariamente o valor `cfg b`.
- **Sensibilidade a Contrafactuais:** Se o fundamento tivesse escolhido uma configuração alternativa $cfg_{\text{alt}}$ em $w_{\text{alt}}$, o nó $b$ teria tomado o valor $cfg_{\text{alt}} b$. No mundo actual, o fundamento escolheu $cfg_{\text{act}}$, pelo que $b$ tomou $cfg_{\text{act}} b$. A dependência é causal e explicativa, não uma mera consequência analítica da definição de actualidade.

---

## 3. Auditoria do Contra-Modelo Intelectualista Substantivo (`substantive_rational_intellectualist_control_model`, Linha 2112)

O contra-modelo substantivo `(countermodelS, countermodelT, toyPriority)` foi submetido à prova da nova relação de actualização efectiva e **provou-se no kernel que satisfaz simultaneamente 13 premissas estruturais e cosmológicas**:
1. `ContingentSystem countermodelS` (modalidade contingente genuína)
2. `GeneralContrastivePSR countermodelS` (explicação contrastiva avaliativa)
3. `CompleteRationalDetermination countermodelS countermodelT` (escolha unívoca por razões)
4. `CompleteRationalGlobalDetermination countermodelS countermodelT` (determinação global da configuração)
5. `UnifiedRationalActualization countermodelS countermodelT` (fecho de fronteira e actualização unificada)
6. `EffectiveOntologicalActualization countermodelS countermodelT` (determinação efectiva dos nós terminais pela escolha)
7. `IsNecessary countermodelS countermodelT` (Aseidade do fundamento)
8. `NatureInvariant countermodelS countermodelT` (essência invariante entre mundos)
9. `IsPersonalAgent countermodelS countermodelT` (apreensão teleológica de alternativas)
10. `SelectsIntentionally countermodelS countermodelT` (selecção intencional guiada por razões)
11. `GuidedByJustificationMode countermodelS countermodelT` (justificação contrastiva objectiva)
12. `IsUltimateGround countermodelS countermodelT toyPriority` (ultimidade livre de condições exteriores não-fundadas)
13. `¬ NecessitatingMode countermodelS countermodelT` (ausência de necessitação modal rígida)

Ao mesmo tempo, o modelo **refuta e nega formalmente**:
- `¬ AgentialSovereigntyOverAlternatives countermodelS countermodelT toyPriority` (o agente não tem o poder contrafactual de escolher a alternativa sub-óptima)
- `¬ ActsFreely countermodelS countermodelT` (a liberdade libertária é estritamente falsa sob determinismo moral)

---

## 4. Separação Rigorosa dos Cinco Níveis de Conclusão (`five_levels_of_conclusion_separation`, Linha 2049)

O teorema `five_levels_of_conclusion_separation` demonstra no kernel que os cinco níveis conceituais são **rigorosamente independentes e não-conflacionados**:

```lean
theorem five_levels_of_conclusion_separation :
    (¬ SystemFullyInternallyDetermined countermodelS) ∧
    (¬ NecessitatingMode countermodelS countermodelT) ∧
    (¬ OutcomeFixedByGroundBasis countermodelS countermodelT) ∧
    CompleteRationalDetermination countermodelS countermodelT ∧
    EffectiveOntologicalActualization countermodelS countermodelT ∧
    (¬ ActsFreely countermodelS countermodelT)
```

### Análise Epistemológica dos Níveis:
1. **Nível 1 (Impossibilidade de Determinação Inteiramente Interna):**  
   $\neg \text{SystemFullyInternallyDetermined } S$ decorre da irreflexividade e aciclicidade da prioridade ontológica bem-fundada. A cadeia não é auto-suficiente.
2. **Nível 2 (Impossibilidade de Necessitação Modal Rígida da Totalidade):**  
   $\neg \text{NecessitatingMode } S \ T$ e $\neg \text{OutcomeFixedByGroundBasis } S \ T$ decorrem estritamente da contingência modal da totalidade fundado sob fundamento necessário.
3. **Nível 3 (Determinação da Escolha por Razões):**  
   $\text{CompleteRationalDetermination } S \ T$ (intelectualismo leibniziano) é perfeitamente compossível com os Níveis 1 e 2. O fundamento escolhe guiado univocamente pelas melhores razões.
4. **Nível 4 (Determinação Causal/Ontológica Efectiva do Resultado Global):**  
   $\text{EffectiveOntologicalActualization } S \ T$ prova que todo o resultado e todos os nós de fronteira dependem efectivamente da escolha do fundamento, sendo compossível com os Níveis 1, 2 e 3.
5. **Nível 5 (Liberdade Libertária Positiva):**  
   $\text{ActsFreely } S \ T$ exige o poder de escolher de outro modo sob as mesmas condições antecedentes (*potestas ad utrumque*). **Os Níveis 1 a 4 NÃO implicam o Nível 5.** Pelo contrário, o Nível 4 refuta formalmente o Nível 5 sob razões favoráveis (`effective_actualization_refutes_libertarian_freedom`, Linha 2028).

---

## 5. Conclusão Metodológica: O Dilema da Forçagem Forte e a Soberania Agencial

### A. O que está demonstrado no Kernel Lean 4:
- A impossibilidade ontológica da forçagem integral da cadeia (`chain_cannot_be_exhaustively_forced`) **não exclui a determinação racional completa do resultado pelas condições antecedentes**.
- O argumento cosmológico/ontológico e o PSR contrastivo conduzem necessariamente a um Fundamento Pessoal Último e Aseítico, **mas são neutros entre o Determinismo Racional/Moral (Leibniz) e a Liberdade Libertária (Escoto/Molina)**.
- Para excluir a determinação racional e deduzir a liberdade libertária positiva (`ActsFreely`), é **estrita e filosoficamente indispensável a premissa de Soberania Agencial** (`AgentialSovereigntyOverAlternatives`). Ela não é um corolário da cosmologia, mas uma premissa independente sobre a natureza da agência pessoal.

### B. Adequação Filosófica da Definição de Forçagem:
- Se se pretender estender a definição de "forçagem integral" para abranger a determinação da vontade pelas razões do bem, a exclusão dessa determinação **não é uma vitória dedutiva do argumento ontológico**, mas uma **petição de princípio definicional** (consistiria em definir "não-forçado" como significando "libertário").
- A formulação rigorosa de Γ ganha em honestidade intelectual e força filosófica ao explicitar que a defesa da liberdade libertária repousa sobre a retorsão transcendental da justificação racional no sujeito do juízo, e não sobre um suposto fechamento analítico da cosmologia pura.
