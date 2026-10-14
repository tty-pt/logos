---
description: "Master prompt to execute the complete polish, testing, and automation suite in logos4"
argument-hint: "[target]"
---

# Master Prompt: Suite de Polimento, Testes e Automação para Logos 4

Execute a implementação completa do pacote de melhorias em `/home/quirinpa/logos4`, mantendo a integridade matemática e a rastreabilidade do kernel do Lean 4:

## 1. Atualização do Diagrama Mermaid e Visão Geral (`README.md`)
- Em `scripts/build_deduction.py` (e no `README.md` resultante):
  * Atualizar o diagrama nativo Mermaid no topo do `README.md` para incluir a 11ª Cremação (`C11: Occasionalism / Pure Divine Monocausality` com terminador `COLLAPSE`).
  * Expandir o nó de `Divine Reality` (`DR`) para refletir a totalidade das **15 Características Divinas** deduzidas.
  * Destacar na narrativa inicial os 4 novos teoremas de ponta verificados no kernel:
    1. *Resolução do Paradoxo da Onipotência* (`omnipotence_excludes_logical_contradiction`);
    2. *Ex Nihilo Nihil Fit* (`absolute_nothingness_cannot_self_actualize`);
    3. *Argumento da Razão* (`rational_agency_incompatible_with_blind_physicalism`);
    4. *Creatio Continua* (`cessation_of_grounding_entails_system_annihilation`).

## 2. Criação da Suíte de Testes Automatizada (`scripts/test_pipeline.py`)
- Criar o script de testes automatizado em Python `/home/quirinpa/logos4/scripts/test_pipeline.py`.
- O script deve validar programmaticamente:
  * Ausência total de `sorryAx` (0 sorrys) em todos os 4 módulos em `formal/Logos/`;
  * Censo exato dos 6 axiomas declarados (impedindo axiomas não declarados ou fantasmas);
  * Integridade dos 10 passos dedutivos da Parte I e resolução de todas as âncoras Lean;
  * Integridade das 15 características divinas da Parte II em `DivineReality`;
  * Integridade das 11 cremações da Parte III com terminadores válidos (`⊥`, `⊘`, `COLLAPSE`, `🧱`);
  * Compilação com retorno 0 do metateorema raiz `OntologicalIncompletenessTheorem.lean`.
- Amarrar a execução de `test_pipeline.py` ao alvo `make test` no `Makefile`.

## 3. CLI Interativo com Suporte a Flags (`formal/Main.lean`)
- No executável Lean 4 (`formal/Main.lean`), implementar o tratamento de argumentos de linha de comando:
  * `lake exe logos --steps`: exibe apenas os 10 passos dedutivos da Parte I;
  * `lake exe logos --attributes`: exibe as 15 características divinas da Parte II;
  * `lake exe logos --cremations`: exibe as 11 cremações filosóficas da Parte III;
  * `lake exe logos --check`: executa uma verificação rápida e silenciosa retornando código 0;
  * `lake exe logos --help`: exibe o manual de uso e flags disponíveis;
  * Sem argumentos: executa a apresentação completa e detalhada padrão.

## 4. Alinhamento do CI do GitHub Actions (`.github/workflows/ci.yml`)
- Simplificar e padronizar o workflow `.github/workflows/ci.yml` para invocar os alvos do Makefile:
  ```bash
  make all
  make test
  make run
  ```
  Garantindo paridade estrita e reprodutibilidade entre o ambiente local e a integração contínua do GitHub.

## 5. Guia de Navegação Acadêmica (`READINGPATH.md`)
- Criar na raiz de `logos4` o guia `READINGPATH.md`, estruturando o roteiro de leitura para acadêmicos (matemáticos, filósofos e teólogos), orientando a exploração dos arquivos na ordem ideal:
  1. `README.md` (argumento dedutivo executivo);
  2. `Main.lean` (auditor interativo CLI);
  3. `OntologicalIncompletenessTheorem.lean` (metateorema unificado);
  4. Módulos formais em `formal/Logos/` (`System.lean`, `Elimination.lean`, `Agency.lean`, `Source.lean`);
  5. Tratados de aprofundamento em `investigations/`.

## 6. Verificação de Encerramento e Regras de Segurança
- Executar `make clean && make all && make test && make run` garantindo 0 erros e 100% de sucesso.
- O repositório base `~/logos` deve permanecer 100% intocado.
- Não executar `git commit` ou `git push` sem autorização prévia explícita.
