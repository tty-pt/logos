# GAPMAP.md — theorem ledger of Γ (generated from `#print axioms`, 2026-09-17, post A2-swap-theorem)

Statuses: `PROVEN` (theorem, kernel-checked) · `PROVEN↑` (theorem under
flagged axioms) · `AXIOM` (declared) · `BLOCKED` (missing lemma named) ·
`DEFERRED` (out of scope of this milestone).

`CL` = `{propext, Classical.choice, Quot.sound}` (classical meta-logic, D1).

## Batch lift-necessário (2026-09-18) — ∃e □Exists(e) via esse est agere

The roadmap step #4/#5 (subject necessity → entity necessity) is executed:

- **C91** `Modal.subject_nec_entity_nec` (plus `_iff` and
  `necessary_entity_exists_of_necessary_subject`): `NecessarySubject s →
  NecessaryEntity (EntityOf s)` is **definitional** — `ExistsAt` is one shared
  relation and `Plurality.EntityOf` is the Truthmaker embedding, so both sides
  unfold to `∀ w, ExistsAt w (EntityOf s)`. Footprint `{Subject}` (VOCAB only,
  no SEM/META). The transfer is NOT a logical law: `not_holds_of_arbitrary_signature`
  and `subject_necessity_not_entails_entity_necessity`
  (HostileSemantics, `{}`) show a subject can persist in every world while its
  entity-correlate exists in only one.
- **C92** `Love.necessary_entity_exists : ∃ e, NecessaryEntity e` — from the
  demonstrated person (`T5_personExists`, C24) and persistence
  (`AxPersonStability`, esse est agere) with the C91 lift. Footprint
  `{Means, Subject}` (no AxTwoSubjects). This gives the *performing person's
  entity-correlate*; it does **NOT** close T7 — the uniform ground of a
  necessary truth stays `AxGlobalGround`-priced (C18). Prose base.txt
  §26/§27/§28/§29 and theorems/T7.txt (Passo A) updated accordingly.
- Still requires proof (recorded in base.txt §28): an independent bridge
  `NecessaryEntity e → ∃τ, Ground e τ` (step #7, without AxGlobalGround) and
  `Ground(e, personal) → Personal(e)` (step #9, without AxPersonalGround).

## Batch freedom/choice fix (2026-09-18) — `Chooses` is genuine choice, `FreeWill` is definitional

Driven by the user: the hostile countermodel only showed `Act(s,p) ↛ FreeWill(s)`,
which is not the needed claim; `Chooses` was a *determined occurrence*, not a
choice; freedom must not be derived from `Act`; and no new metaphysical axiom
may be added.

- **Root finding**: with the old `Chooses s p q := A s p ∧ Incompatible p q` and
  `Incompatible p (¬p)` pure logic, `∃ q, Chooses s p q` collapses to `A s p`
  (`= SubjectExists s`). The agent was never related to the rejected horn.
- **Repair (definitions)**: vocabulary split into
  `ChoiceField s p q := A s p ∧ Incompatible p q` (representability; the OLD
  relation, no longer called choice), `Chooses s p q := A s p ∧ A s q ∧
  Incompatible p q` (genuine choice: the agent co-means both horns), and
  `FreeWill s := ∃ p q, Chooses s p q` (unary; freedom is DEFINITIONAL).
  `chooses_implies_freeWill` has footprint **`{Means, Subject}`** (VOCAB only:
  the statement's own vocabulary; the logical content is free); the old bipolar
  `FreeWill s p := CanChoose s p ∧ CanChoose s (¬p)` is subsumed.
- **Renamed (field form preserved)**: `person_chooses` → `person_hasChoiceField`,
  `choiceExists` → `choiceField_exists` (+`_from_plurality`),
  `noChoice_selfRefutes` → `noChoiceField_selfRefutes`,
  `JUDGE_COMMITTED` → `JUDGE_HAS_CHOICE_FIELD`, `NoChoice` → `NoChoiceField`;
  `Order.judge_commits` now concludes `ChoiceField`. Footprints unchanged
  (`{Means, Subject}`, `{AxTwoSubjects, Means, Subject}`, `CL` where applicable);
  only the conclusion is weakened from the (never valid) genuine choice to the
  honest field.
- **Hostile model**: `CountermodelNoFreeWill` now has `Chooses := fun _ _ _ => False`
  and `FreeWill := fun s => ∃ p q, Chooses s p q`; it proves `Act ↛ Chooses` and
  `Act ↛ FreeWill` (`{}`). It is **no longer** presented as a countermodel to
  `Chooses ↛ FreeWill`, which is definitional. `not_entails_freewill` →
  `not_entails_decoupled_freewill` (the decoupled predicate, not Logos's
  definitional `FreeWill`).
- **Missing lemma F1b resolved (PROVEN↑)**:

  Fechado sob a ponte semântica estritamente mais fraca `AxActPolarity : ∀ s p, Act s p → Means s (¬ p)`
  (`Tag: SEM`, polaridade da agência / início de movimento). A intencionalidade bilateral universal
  (`∀ s p, Means s p → Means s (¬p)`) foi demonstrada independente por `CountermodelVeridicalMeaning`
  (`unilateral_meaning_witness`, `bilateral_intentionality_fails`); `AxActPolarity` restringe a
  exigência de polaridade estritamente à iniciação de movimento (`Act s p`), derivando
  `Choice.genuineChoice_exists_of_act` e `Choice.freeWill_exists` sob
  `{AxActPolarity, Initiates, Means, State, Subject}`.
- **Footprint report**: no footprint grows, no axiom added. `chooses_implies_freeWill`
  `{Means, Subject}` (VOCAB only); field theorems same as before (`person_hasChoiceField`/`choiceField_exists`
  `{Means, Subject}`; `JUDGE_HAS_CHOICE_FIELD` `{AxTwoSubjects, Means, Subject}`;
  `judge_commits` `{AxTwoSubjects, Means, Subject, CL}`); hostile separations `{}`;
  unconditional `freeWillExists` BLOCKED (no footprint).
- **Fronteira negativa completada (2026-09-18)**: o lado modal da abertura está
  provado no kernel — átomos modicamente livres (`atoms_are_modally_free`,
  C95, `{}`) e conteúdo contingente existe (`some_formula_contingent`, C96,
  `{}`) — e é **inerte** para a fronteira: sob o datum de abertura modal, a
  co-significação continua não-derivável
  (`modal_openness_does_not_entail_genuine_choice(_and_plurality)`, `{}`,
  HostileSemantics). O bloqueio de F1b é exclusivamente
  `rejectedHornCoMeant` (o lado da agência), não qualquer determinação modal.

## Batch fronteira escolha-genuína (2026-09-18) — veredito opção 3 (bloqueio irreducível)

Hostile, proof-oriented attack on `genuineChoice_exists` (F1b). No axiom added;
each step is either a theorem, a countermodel, or a documented gap.

- **Recurso único formalizado**: `Choice.rejectedHornCoMeant : Prop :=
  ∃ s p, A s p ∧ A s (¬ p)` — nó BLOCKED (`{Means, Subject}`); a fronteira mínima
  `rejectedHornCoMeant → genuineChoice_exists` (`{Means, Subject}`) mostra que
  co-significar a negação basta (`q := ¬p`, `incompatible_self_negation`).
- **Factos negativos novos** (`{Means, Subject}`):
  - `genuineChoice_requires_error_possibility : genuineChoice_exists →
    ¬ (∀ s p, Means s p → p)` — escolha genuína força a não-veridicalidade de
    `Means` (co-significar incompatíveis com significação veridical daria
    `p ∧ q ∧ ¬(p∧q)`); a fronteira É a possibilidade de erro, que nenhum axioma
    fornece.
  - `assertion_consistency` / `no_one_asserts_incompatible_pair` — `Asserts s p
    := Act s p ∧ p` é verídico pelo conjunção; o performativo enquanto
    *asserção* é de um-corno-só por definição; a rota "assertir/denegar é
    escolher" é impossível como teorema (não como lacuna).
- **Contramodelos decisivos** (`{}`), `CountermodelVeridicalMeaning` em
  HostileSemantics (Part C2c): instâncias `Single` (Unit) e `TwoPersons`
  (Bool) usando as definições Logos **exatamente** (`A := Means`, `Person :=
  ∃p, Means s p`, `Chooses := co-significação`, `FreeWill := ∃p q, Chooses`) com
  `Means _ p := p` (veridical). Em `TwoPersons`, TODO o fragmento
  agency/choice/order vale — datum do ato, dois sujeitos distintos
  (AxTwoSubjects), certo/errado, `judge_commits`, falibilidade — com escolha
  genuína **vazia** (`full_fragment_without_genuine_choice`).
- **Não-derivação formal**: `not_entails_genuine_choice` e
  `not_entails_genuine_choice_with_plurality` sobre
  `GenuineChoiceSignature {Subject, Means}` (`{}`): nem o datum do ato, nem o
  datum + pluralidade, forçam `GenuineChoice`; novos, com o datum modal:
  `modal_openness_does_not_entail_genuine_choice` e `_and_plurality_...` sobre
  `BoundarySignature {Subject, World, Value, Means}` (`{}`) — mesmo alimentando
  a abertura modal (espelho de C95/C96) como premissa extra, a co-significação
  não é forçada.
- **Veredito**: opção 3 — `genuineChoice_exists` é genuinamente bloqueado sob
  os primitivos presentes (`{Means, Subject}`); nenhuma refundição definicional
  o fecha sem regressão (colapso campo-escolha, 2026-09-18) ou sem relação nova.
  Fronteira negativa completada: o lado modal está assentado (C95/C96, `{}`) e
  é inerte; o bloqueio é exclusivamente agency-side (`rejectedHornCoMeant`).
- **Premissas substantivas candidatas — registadas, NÃO introduzidas**:
  `AxCoMeaningNegation : ∃ s p, Means s p ∧ Means s (¬ p)` (SEM/META); co-sujeito
  dos cornos `∃ s p, Incorrect s p ∧ Denies s p` (composição `judge_commits` +
  negação); auto-representação do ato (META). Qualquer uma faria F1b →
  PROVEN↑ com pegada nova (próxima fase, fora deste milestone).
- **Footprint report**: nenhuma pegada cresce; `rejectedHornCoMeant` e os 4
  teoremas `{Means, Subject}` (VOCAB); modelos e não-entailments `{}`; novos
  não-entailments com datum modal `{}`. README.md: F1b ✖ BLOCKED (nó
  `rejectedHornCoMeant` + factos negativos).

## Batch fronteira seleção-semântica (2026-09-18) — Reabertura de F1b (Cenário B: fronteira refinada)

Reabertura da fronteira **F1b** sob uma nova interrogação: *A agência com significado envolve necessariamente seleção/compromisso entre alternativas incompatíveis?*
Intuição fundante: se uma ação possui significado assertivo, tem de ser direcionada a um conteúdo contra as suas alternativas incompatíveis. Isto é estritamente mais fraco que livre-arbítrio libertário e mais fraco que co-significar ambos os cornos.

- **Hierarquia de quatro níveis rigorosamente separada**:
  1. *Nível 1 — Alternativas / Campo de Escolha* (`ChoiceField s p q := A s p ∧ Incompatible p q`): presença do contraste lógico incompatível (derivado de qualquer ato).
  2. *Nível 2 — Seleção Semântica* (`Selects s p q := Asserts s p ∧ Incompatible p q ∧ ¬ Asserts s q`): compromisso direcionado com um corno e exclusão constitutiva do corno incompatível (derivado de qualquer asserção).
  3. *Nível 3 — Possibilidade Contrafactual de Selecionar de Outro Modo* (`CouldHaveSelectedOtherwise`): abertura modal contrafactual ($\Diamond \text{Selects}(s, q, p)$). Não forçada por agência determinista.
  4. *Nível 4 — Escolha Livre / Livre-arbítrio Libertário* (`FreeWill s` / `Chooses`): determinação originária sem necessidade causal determinista.
- **Teoremas provados sem axiomas substantivos (`{Means, Subject}` = VOCAB apenas)**:
  - `Choice.Selects`: definição de seleção semântica.
  - `Choice.asserts_selects : Asserts s p → Selects s p (¬p)` — qualquer asserção seleciona contra a sua negação.
  - `Choice.asserts_selects_all_incompatible : Asserts s p ∧ Incompatible p q → Selects s p q` — asserção seleciona contra qualquer alternativa incompatível.
  - `Choice.selection_exists : (∃ s p, Asserts s p) → ∃ s p q, Selects s p q` — o datum assertivo fornece existência de seleção semântica.
  - `Choice.no_selection_no_assertion : (∀ q, ¬ Selects s p q) → ¬ Asserts s p` — contrapositivo: quem não seleciona contra nenhuma alternativa não assere; compromisso assertivo envolve constitutivamente seleção.
  - `Choice.DeliberateChoice`: `Means s p ∧ Means s q ∧ Incompatible p q ∧ Asserts s p ∧ ¬ Asserts s q` — escolha deliberativa (o agente concebe ambos os cornos em pensamento, mas assere apenas um). Entende formalmente a escolha sem asserções contraditórias; acarreta `Selects` (`deliberateChoice_implies_selects`) e `Chooses` (`deliberateChoice_implies_chooses`).
  - `Order.correct_implies_selection` / `_all_incompatible`: juízo correto (`Correct s p := A s p ∧ T p`) reduz-se definicionalmente (`rfl`) a `Asserts s p` e acarreta seleção semântica (Candidato B assentado no kernel de `Order.lean`, sem ciclo de importação).
- **Análise das pontes para `Means → Selection`**:
  - *Candidato A (significado arbitrário)*: falha estritamente (`CountermodelOmniMeaning`, `{}`). Uma mente omni-contemplativa representa tudo (`Means () _ := True`) sem rejeitar nada; `Means` arbitrário não força asserção nem verdade.
  - *Candidato B (significado + direcionalidade à verdade)*: juízo correto `Correct s p` colapsa definicionalmente em `Asserts s p`, rendendo seleção imediatamente (`Order.correct_implies_selection`).
  - *Candidato C (datum performativo restrito)*: a retorsão genuína fornece uma asserção (`Asserts speaker NoAct`), de onde a seleção é gratuita. Para o datum genérico do ato `∃ s p, Act s p`, a passagem a asserção exige uma ponte semântica explícita e precificada: `Choice.act_implies_asserts_bridge : (∃ s p, Act s p) → ∃ s p, Asserts s p` (`Choice.selection_exists_of_act`, SEM).
- **Fronteira e contramodelos hostis (`{}`)**:
  - `Means ↛ Selects`: significado bruto não acarreta seleção (`CountermodelOmniMeaning`, `not_entails_selection_of_bare_means`, `{}`).
  - `Asserts ↛ Selects`: **impossível** de refutar por contramodelo — `asserts_selects` é teorema no kernel; `Asserts s p := Act s p ∧ p` exige que p seja verdadeiro, o que exclui constitutivamente asserir qualquer q incompatível via consistência lógica.
  - `Selects ↛ DeliberateChoice`: seleção não acarreta escolha deliberativa (`CountermodelVeridicalMeaning.Single.no_deliberate_choice`, `selection_not_entails_deliberate_choice`, `{}`) — o agente verídico seleciona `True` sobre `False`, mas não concebe `False` em pensamento (`no_rejected_horn`).
  - `Selects ↛ Chooses(antigo)`: seleção semântica não exige co-significar o corno rejeitado (`CountermodelVeridicalMeaning.Single`, `selection_does_not_imply_genuine_choice`, `{}`).
  - `Selects ↛ FreeWill`: agência determinista possui seleção semântica plena e dirigida, mas não possui liberdade libertária (`CountermodelVeridicalMeaning.Single`, `selection_does_not_imply_freewill`, `{}`).
- **Veredito F1b (Cenário B — fronteira refinada)**:
  A relação entre significado assertivo e seleção semântica está estabelecida dedutivamente sem axiomas. A questão do livre-arbítrio libertário fica desacoplada da seleção semântica e preservada como fronteira aberta separada.

## Batch fronteira pessoal (2026-09-18) — C24 nominal, pessoa substantiva não forçada

Refactor mínimo B + endurecimento hostil da ponte C24. **Conteúdo kernel
inalterado**: definições de `Act`/`SubjectExists`/`Intentional`/`Agent`/
`Rational`/`Person`/`Means` intactas; −0 axiomas, −0 `sorry`. O que muda é a
*precisão formal* da fronteira:

- **Lemas-ponte explícitos** (Person.lean, todos `{Means, Subject}`, provas
  mais fracas possíveis): `act_implies_intentional` (`⟨p, h⟩`),
  `subjectExists_implies_intentional` / `intentional_implies_subjectExists`
  (identidade), `person_intentional_iff` (a ponte §12 dita explicitamente:
  `Person ↔ Intentional`, pois `Agent`/`Rational` são analiticamente `True`).
  `person_of_subject`/`person_of_act`/`person_exists_of_act` ficam
  documentados como consequências **nominais/constitutivas** das definições
  correntes — NÃO como descobertas semânticas independentes.
- **Separação obrigatória**: *derivabilidade formal ≠ neutralidade semântica
  da definição*. C24 é teorema-válido na ontologia corrente, mas o §12 é
  compromisso constitutivo (rótulo "person" sobre o sujeito significador
  atualizado); a noção substantiva (deliberação, responsabilidade,
  auto-reflexão, agência autónoma, escolha racional, agência moral) NÃO é
  estabelecida pelo datum.
- **Matriz hostil substantiva** (HostileSemantics, Parte A2, `{}`): NENHUM
  modelo ataca a identidade §12 (é facto das definições); os quatro
  `not_entails_substantive_intentionality` (`Mind` vazio, resto cheio),
  `not_entails_substantive_rationality` (`Ratio` vazio),
  `not_entails_substantive_autonomy` (`Auto` vazio),
  `not_entails_substantive_person` (`Mind`/`Ratio`/`Auto` cheios, `Degree`
  vazio — mesmo com tudo o resto presente) atacam as leituras mais fortes
  que o rótulo não pode contrabandear, cada um com modelo DISTINTO que
  preserva os demais predicados (matriz ortogonal). Docstrings de
  `not_entails_person` e
  `CountermodelSubjectWithoutPerson` emendadas com o aviso "atinge só a
  leitura substantiva; NÃO é contramodelo de `person_intentional_iff`".
- **C24 reclassificado**: enunciado e gloss do README passam a dizer que a
  prova estabelece o sujeito significador atualizado sob §12 e que a
  pessoalidade substantiva não é independentemente estabelecida. PROVEN
  mantido; downstream intacto (C39/C77/C92 usam C24 só no sentido fraco —
  forma mais forte válida = reancoragem em `SubjectExists`/`Intentional`;
  C52 foi reancorado EM CÓDIGO: `choiceField_exists` deriva o campo via
  `intentional_hasChoiceField` a partir de `act_implies_intentional`, sem
  passar por `Person`).

## Batch A2-swap-theorem (2026-09-17) — `AxGlobalGround` becomes a theorem (atom-restricted)

The quantifier swap `∀w∃e … ⇒ ∃e∀w …` (D7, SEM) is answered by the
esse-est-agere deflation: `ExistsAt` is world-vacuous by definition, so the
witness from any one world works for all worlds definitionally —
`axiom AxGlobalGround` → **theorem** `AxGlobalGround (n : Nat)
(hnec : NecessarilyTrue (atom n))` (name kept per M1 precedent; proof:
`groundPrinciple_atom` at `actualWorld`, same entity reused at every `w`).
Measured (`#print axioms`): A2-atom, C18, C20, C34 → `{Ground}`
(vocab-only — the statement's own vocabulary, no SEM/META).
**Axiom inventory 6 → 5 declarations** (−`AxGlobalGround`); substantive
axioms unchanged in kind (SEM/META only).
Restricted to atoms by the M4 wall (structural `TrueAt` carries no
existential ground for compounds): the excluded-middle instance C19
(`T7_excludedMiddleInstance`, deleted from the barrel) is recorded
BLOCKED with its exact missing lemma `∃ e, Ground e (or θ (not θ))`
given EM-necessity (transcript: `formal/Spikes/Spike_A6_probe.lean` — the
M4 "stays priced (smaller)" verdict is superseded: nothing stays priced;
the atom swap needs no axiom at all). T7 (C18), its reductio (C20) and
the GroundPerson link (C34) are re-scoped to atoms, same proofs. Honestly
recorded cost: T7's "necessary reality grounded on the indubitable"
(compound) is no longer derived — the atom ground is. Q7.2 answered: for
atoms the swap needs no weaker premise (it is definitional); the compound
instance is a different, unforced claim.

## Batch definitional-subject (2026-09-17) — `Cogito` becomes a theorem

The user correction ("cogito must be a theorem; subject definitional, in the
traditional sense") retires M0's TRANS axiom. `axiom Subject : Type` → **def**
`Subject := Unit ⊕ Prop` (ὑποκείμενον: the silent origin sustaining every
posit + posited contents positing themselves; origin-only, never evaluated);
`axiom State : Type` → **def** `State := Prop` (truth-bearers);
`axiom Initiates` → **def** (field-toward-posit, by cases on the subject);
`axiom Cogito` → **theorem** `Cogito : ∃ s p, A s p` (**`{}`**, witness
`Sum.inl ()`); `noCogito_selfRefutes` re-proved by exhibition (**`{}`**,
no axiom cited — the degenerate `fun h => h Cogito` is retired). The M0
FORCED class is dissolved: there is no foundation axiom left to force. The
foundation is re-anchored on the original chain — undeniable right-and-wrong
(C36, `{}`) ⇒ meaning (analytic, §8) ⇒ choosing subject (definitional
witness). **Axiom inventory 12 → 8 declarations** (−`Cogito`, −`Subject`,
−`State`, −`Initiates`); substantive axioms unchanged (SEM/META only).
Former `{Cogito, Initiates, State, Subject}` footprints below are now `{}`
(measured, §Annex), `CL` where `by_cases` is used. (Prior batch, same day:
act-as-initiation rebase — `axiom Means` → def `Means s p := ∃ w w',
Initiates s w w' p`; `A s p := Means s p` unchanged.)

## Batch esse-est-agere (2026-09-17) — existence as agency; `AxPersonStability` becomes a theorem

The M3 wall (`PERSON_PERSISTS`: no rule from `Person`/`Means` to `ExistsAt`)
is answered by supplying the rule as a definition: `axiom ExistsAt` → **def**
`ExistsAt _w s := ∃ p, A s p` (to be is to act; the world-index is vacuous by
principle — `Means` takes no `World` parameter, so agency is not
world-located — while the existential does the real work: only actors exist).
`Person s` unfolds definitionally to `∃ p, Means s p` (via `Intentional`;
kind-preds `:= True`; `A := Means`), so `AxPersonStability : ∀ s, Person s →
NecessarySubject s` is now a **theorem** (**`{}`**, name kept per M1
precedent). Measured (`#print axioms`): T14 family (C42–C45) → `{}`
  after the plurality-discharge (2026-09-17); C18/C34 → `{AxGlobalGround, Ground}`;
  C15/C16/C17/C60 → `{Ground}`;
  C32 → `{AxPersonalGround, GroundProp}`; `Cogito` still `{}`.
**Axiom inventory 8 → 6 declarations** (−`ExistsAt`, −`AxPersonStability`);
substantive axioms unchanged in kind (SEM/META only). M2 (`ALONE_EXCLUDED`)
was untouched by this batch: `Alone` never mentions `ExistsAt` — this batch
proved *persistence*, not plurality; M2 was later closed by the
plurality-discharge (2026-09-17, `neverAlone`/`aloneExcluded`, C74).
Honestly recorded costs: the world-index is vacuous (declared, not hidden);
`T14_world` is trivially witnessed (same act in all worlds); T7/T8
"necessary" turns agent-flavored (grounded by an acting subject).

## Level 0 — performative core (`Logos.Core`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C1 | §4 | `nothingTrueRefutes : ¬ T N_T` | PROVEN | `{}` (E0: `T := id`) |
| C2 | §4 | `notNothingTrue : ¬ N_T` | PROVEN | `{}` (E0) |
| C3 | §4 | `someTrue : ∃ p, T p` | PROVEN | `CL` |
| C4 | §4 | `atomicTruthWitnessed : T True` | PROVEN | `{}` (E0) |
| C5 | §5 | `nothingFalseRefutes : ¬ T N_F` | PROVEN | `{}` (E0) |
| C6 | §5 | `notEverythingTrue : ¬ N_F` | PROVEN | `{}` (E0) |
| C7 | §5 | `someFalse : ∃ q, IsFalse q` | PROVEN | `{}` (E0) |
| C8 | T3 §6 | `greatResult : ∃ p q, T p ∧ IsFalse q` | PROVEN | `{}` (E0) |
| C9 | T3 | `noBothTrueAndFalse` | PROVEN | `{}` (pure logic) |
| C10 | §22 | `excludedMiddle : ∀ p, T (p ∨ ¬ p)` | PROVEN | `CL` |
| C11 | §23 | `nonContradiction : ∀ p, T (¬ (p ∧ ¬ p))` | PROVEN | `{}` (E0) |
| C12 | §10 | `bivalence : ∀ p, T p ∨ IsFalse p` | PROVEN | `CL` |
| C102 | §1/§4 | `DirectNormativeRetorsion.NoRight : Prop` — universal skeptical thesis that no genuine normative correctness judgment exists | PROVEN | `{}` |
| C103 | §1/§4 | `DirectNormativeRetorsion.claims_correct_no_right_self_refuting : ClaimsCorrect s NoRight → NoRight → False` — claiming NoRight as correct while true yields a contradiction | PROVEN | `{}` |
| C104 | §1/§4 | `DirectNormativeRetorsion.cannot_claim_correct_no_right_and_true : ¬ ∃ s, ClaimsCorrect s NoRight ∧ NoRight` — unassertability of the skeptical thesis | PROVEN | `{}` |
| C105 | §1/§4 | `DirectNormativeRetorsion.performative_normative_denial_establishes_normative_right : (∃ s, ClaimsCorrect s NoRight) → ¬ NoRight` — performative denial establishes normative right | PROVEN | `{}` |

Founding definitions of Level 0 (E0, 2026-09-15): `def T (p : Prop) : Prop := p`
(the D2 consistency model made definitional); `tschema` is a theorem
(`Iff.rfl`), no longer an axiom. The §4–§6 self-refutation core is
axiom-free: its negation-free content rests on classical logic only.

## Level 1 — semantics (`Logos.Semantics`, `Logos.Truthmaker`, `Logos.Modal`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C13 | §22 | `Semantics.lawExcludedMiddle` | PROVEN | `CL` |
| C14 | §23 | `Semantics.nonContradiction` | PROVEN | `CL` |
| C15 | §24a | `Truthmaker.groundPrinciple_atom` | PROVEN↑ | `{Truthmaker, Ground, Subject}` (SEM bridge `Truthmaker`) |
| C60 | §24a (RAA) | `Truthmaker.noGround_selfRefutes` | PROVEN↑ | `{Truthmaker, Ground, Subject}` (companion of C15) |
| C16 | §22 | `Truthmaker.lawExcludedMiddle` | PROVEN | `{CL}` |
| C17 | §23 | `Truthmaker.nonContradiction` | PROVEN | `{}` |
| C18 | T7 | `Modal.T7_necessaryReality` | PROVEN↑ | `{AxGlobalGround, Ground, Subject}` (SEM bridge `AxGlobalGround`) |
| C19 | T7 | `Modal.T7_excludedMiddleInstance` | PROVEN↑ | `{AxGlobalGround, Ground, Subject, CL}` (derived from C18 and C16 under `AxGlobalGround`) |
| C20 | T7 | `Modal.noNecessaryTruthIfAllContingent` | PROVEN↑ | `{AxGlobalGround, Ground, Subject}` (as C18) |
| C91 | §25/§27/T7 Passo A | `Modal.subject_nec_entity_nec : NecessarySubject s → NecessaryEntity (EntityOf s)` (+ `_iff`, `necessary_entity_exists_of_necessary_subject`) — **lift definicional sujeito → entidade** | PROVEN | `{Subject}` (VOCAB; `ExistsAt`/`EntityOf` partilhados — contramodelo hostil `{}` mostra que não é lei lógica) |
| C78 | T7 | `Modal.contingent_ground` | BLOCKED | (retired: manufactured `Sum.inl` origin grounding destroyed under hostile semantics) |
| C79 | T7 | `Modal.ultimateGround_exists` | BLOCKED | (retired: manufactured ultimate ground destroyed under hostile semantics) |
| C87 | T7 | `Modal.origin_is_necessary` | BLOCKED | (retired: manufactured `Sum.inl` origin necessity destroyed) |
| C88 | T7 | `Modal.transcendental_quantifier_swap` | BLOCKED | (retired: manufactured origin quantifier swap destroyed) |
| C89 | T7 | `Modal.ultimateGroundInit_exists` | BLOCKED | (retired: manufactured ultimate ground by initiation destroyed) |

Declared (Level 1): `Ground` (world-rigid, D6; over `Entity`) is the vocabulary axiom (`Tag: VOCAB`);
`Truthmaker` is the semantic bridge (`Tag: SEM`, 2026-09-17) decoupling satisfaction from grounding;
`ExistsAt` is the agency-independent *definition* (2026-09-17); `actualWorld` (def, SEM);
`AxGlobalGround` is the explicit uniform-grounding bridge (`Tag: SEM`).
C19 is derived under `AxGlobalGround` (`PROVEN↑`).

## Level 2 — agency and person (`Logos.Agency`, `Person`, `Alternatives`, `Order`, `GroundPerson`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C58 | §1 fnd | `Agency.noWeakAct_selfRefutes : asserts speaker NoWeakAct → False` — **retorsão performativa direta (ato fraco)** | PROVEN | `{Subject, act}` (retorsão performativa direta: asserção é evento realizado → evento existe → refutação direta de NoWeakAct; estabelece diretamente apenas o ato fraco) |
| C68 | T1 | `Agency.Cogito : Asserts s p → ∃ s' p', Act s' p'` — **cogito derivado da asserção performativa** | PROVEN | `{Initiates, Means, State, Subject}` (teorema derivado de qualquer asserção; deriva ato e sujeito via regra constitutiva) |
| C21 | T1 | `Plurality.T1_subjectExists` | PROVEN | `{Initiates, Means, State, Subject}` (derivado do ato intencional C68 via regra constitutiva act_requires_subject; desacoplado de AxTwoSubjects) |
| C22 | T2 | `Agency.T2_contentExists` | PROVEN | **`{}`** — `Content _ := True` (def), `True` witnesses content |
| C23 | T4 | `Plurality.T4_agentExists` | PROVEN | `{Initiates, Means, State, Subject}` (derivado do ato intencional C68 → C21; `Agent` é `:= True`, def) |
| C24 | T5 | `Plurality.T5_intentionalSubjectExists` | PROVEN | `{Initiates, Means, State, Subject}` (derivado do ato intencional C68 → C21 → C24; estabelece o sujeito intencional como conclusão necessária da agência; pessoalidade substantiva permanece desacoplada) |
| C25 | §24b | `Person.inseparability_24b` | PROVEN | `{Initiates, Means, State, Subject, CL}` |
| C26 | **T9 (new)** | `Alternatives.T9_incompatibleAlternatives` | PROVEN | `{}` (E0) |
| C27 | §13 | `Alternatives.incompatible_with_negation` | PROVEN | `{}` (E0) |
| C28 | T6 | `Order.T6_fallibility` | PROVEN↑ | `{AxTwoSubjects, Means, Subject}` (via T12 + `Core.someFalse`) |
| C29 | T6 | `Order.T6_truthTranscendsWill` | PROVEN↑ | `{AxTwoSubjects, Means, Subject}` (as C28) |
| C30 | §8 | `Order.correctness_distinct` | PROVEN | `{Initiates, Means, State, Subject, CL}` (defs act-relative §8; usa o dado performativo do ato) |
| C31 | §9 | `Order.consequence_preserves_truth` | PROVEN | `{}` (E0) |
| C83 | §8 | `Order.no_correct_judgment_of_no_act` — **retorsão cartesiana**: nenhuma negação do ato pode ser correta (`judgment_of_no_act_is_incorrect`) | PROVEN | `{Initiates, Means, State, Subject}` |
| C84 | §1/§8 | `Order.judgment_of_no_act_proves_act` — **cogito retorsivo**: o ato de julgar que não há ato testemunha que o ato ocorre (`judgment_implies_cogito`) | PROVEN | `{Initiates, Means, State, Subject}` |
| C106 | §12 | `RetorsiveNormativity.claims_correct_presupposes_normativity : ClaimsCorrect s p → GenuineNormativity s p (¬p)` — assertion presupposes genuine normativity under bipolarity | PROVEN↑ | `{AxJudicativeBipolarity, Means, Subject}` |
| C107 | §15 | `IndubitableNormativeFreeWill.indubitable_normative_free_will : GenuineNormativity s p q → Chooses s p q ∧ FreeWill s` — genuine normativity derives choice and free will | PROVEN | `{Means, Subject}` |
| C32 | T8 | `GroundPerson.T8_personalGround` | PROVEN↑ | `{AxPersonalGround, GroundProp, Initiates, Means, State, Subject}` |
| C33 | T8 | `GroundPerson.present_feature_is_grounded` | PROVEN↑ | `{GroundPrincipleProp, GroundProp, Initiates, Means, State, Subject}` |
| C34 | T8 | `GroundPerson.necessary_truth_has_necessary_grounder` | PROVEN↑ | `{AxGlobalGround, Ground, Subject}` (via C18) |
| C90 | T8 | `GroundPerson.personal_ultimate_ground_exists` | BLOCKED | (retired: manufactured ultimate ground destroyed under hostile semantics) |

### Auditoria Ontológica da Cadeia de Agência (`asserts → act → Act → Subject → Person → ChoiceField → Chooses → FreeWill`)

| Passo / Implicação | Formalização Lean | Classificação | Estatuto Epistemológico e Semântica Hostil |
| :--- | :--- | :--- | :--- |
| **asserts → act** | `Agency.assertion_is_weak_act` | **Caso A (Definicional / Fraco)** | A ocorrência de uma asserção é um evento realizado (`act s p` — *ato fraco: evento realizado*), projecção imediata de `asserts s p := act s p ∧ p`. A retorsão `noWeakAct_selfRefutes` estabelece puramente `∃ s p, act s p` sob `{Subject, act}` sem assumir significado intencional. |
| **act ↛ Act** | `Agency.weak_act_implies_strong_act` | **Caso D (Ponte / Bloqueio Aberto)** | O evento realizado (emissão, som, toque, evento físico/mecânico) **não acarreta logicamente** o ato intencional de iniciação com significado (`Act s p := Means s p ∧ ∃ w w', Initiates s w w' p` — *ato forte: ato com significado intencional e caráter de iniciação*). Demonstrado formalmente sob semântica hostil por `CountermodelWeakActWithoutMeaning` / `not_entails_strong_act` (`{}`). A passagem `act → Act` é uma ponte filosófica explícita (`weak_act_implies_strong_act`), não uma identidade definicional oculta. O atalho forte Logos é a asserção intencional `Asserts s p := Act s p ∧ p` (`assertion_is_act`). |
| **Act → SubjectExists** | `Agency.act_requires_subject`<br>`Agency.subject_exists_of_act` | **Caso B/A (regra constitutiva = identidade)** | Em Logos `Act s p := Means s p ∧ ∃ w w', Initiates s w w' p` e `SubjectExists s := ∃ p, Act s p`: ser sujeito *do* ato é a própria definição de sujeito atualizado. O contramodelo abstrato `CountermodelActWithoutSubject` (ato não-indexado, `Subject` predicado substantivo à parte) falha unicamente esta regra constitutiva; não atinge a identidade definicional Logos. |
| **Act → Intentional** | `Person.act_implies_intentional` | **Caso A (identidade)** | O conteúdo do próprio ato testemunha `Intentional s := ∃ p, Means s p` (`⟨p, h.1⟩`, `{Initiates, Means, State, Subject}`). Identidade definicional: NÃO é atacável por modelo hostil. A leitura substantiva de intencionalidade (consciência/awareness interna) NÃO é forçada — `not_entails_substantive_intentionality` (Part A2, `{}`). |
| **SubjectExists → Intentional** | `Person.subjectExists_implies_intentional`<br>`Person.intentional_implies_subjectExists` | **Caso A (identidade)** | Ambas as noções desdobram para `∃ p, Means s p` (`{Means, Subject}`); equivalência por desdobramento direto. Nenhuma premissa. |
| **Subject → Person** | `Person.person_of_subject` | **Caso A (nominal §12)** | Sob a redução estrutural de §12 (`Person s := Agent s ∧ Rational s ∧ Intentional s` com `Agent := True` e `Rational := True`), `Person` colapsa em `∃ p, Means s p`, IDÊNTICO a `SubjectExists`/`Intentional` (`Person.person_intentional_iff`, `{Means, Subject}`). O §12 é compromisso constitutivo (rótulo nominal), não descoberta metafísica. **Separação 2026-09-18**: derivabilidade formal ≠ neutralidade semântica da definição; sobsemântica hostil com predicado substantivo, a implicação NÃO se segue (`CountermodelSubjectWithoutPerson`, `not_entails_person`), mas isso NÃO é contramodelo da identidade §12. |
| **Person (unificada) ← FreeSubject** | `Person.free_subject_is_person` | **Caso A (Teorema Constitutivo Pleno)** | Na ontologia unificada de $\Gamma$, a Pessoa é definida constitutivamente como o sujeito dotado de livre-arbítrio numericamente distinto (`Person s := FreeSubject s ↔ FreeWill s`). Uma vez derivado o Livre-Arbítrio a partir da normatividade genuína (`indubitable_normative_free_will`), a pessoalidade segue por pura dedução lógica com 0 axiomas substantivos (`free_subject_is_person`, `{Means, Subject}`). A antiga noção opaca `SubstantivePerson` foi revogada como um artefato de lacuna sintética. |
| **Person → ChoiceField** | `Choice.person_hasChoiceField` | **Caso A/C (Campo de escolha fraco)** | O campo de escolha — `ChoiceField(s,p,q)` (*escolha fraca: alternativas incompatíveis estão presentes*) — é DEFINICIONAL a partir do ato intencional (`Person s → ∃p q, ChoiceField s p q`), footprint `{Means, Subject}`. Aviso de auditoria (freedom/choice fix, 2026-09-18): o agente relaciona-se apenas com o conteúdo adotado `p`; o outro corno `¬p` é fornecido pela lógica pura (`incompatible_self_negation`), NÃO pelo agente. Isto **não** é escolha genuína. |
| **Asserts → Selects** | `Choice.asserts_selects`<br>`Choice.asserts_selects_all_incompatible`<br>`Choice.selection_exists`<br>`Choice.no_selection_no_assertion` | **Caso B (Seleção Semântica Provada)** | **F1b reaberto e resolvido no nível semântico**: qualquer ato assertivo constitui seleção semântica direcionada (`Selects s p q := Asserts s p ∧ Incompatible p q ∧ ¬ Asserts s q`). Provado por consistência lógica (`assertion_consistency`, `incompatible_self_negation`, `no_one_asserts_incompatible_pair`), footprint `{Means, Subject}` (VOCAB apenas). O contrapositivo `no_selection_no_assertion` prova que sem seleção não há asserção. |
| **Correct → Selects** | `Order.correct_implies_selection`<br>`Order.correct_implies_selection_all_incompatible` | **Caso B (Candidato B assentado)** | O juízo correto (`Correct s p := A s p ∧ T p`) reduz-se definicionalmente (`rfl`) a `Asserts s p := Act s p ∧ p` e acarreta seleção semântica contra alternativas incompatíveis sem axiomas (`{Means, Subject}`). |
| **Act → Asserts (Ponte C)** | `Choice.act_implies_asserts_bridge`<br>`Choice.selection_exists_of_act` | **Caso D (Ponte SEM precificada)** | Passar do datum bruto do ato intencional (`∃ s p, Act s p`) para asserção exige uma premissa semântica explícita (`act_implies_asserts_bridge`, SEM). Sob a retorsão, a asserção é dada; sob o datum genérico, a ponte é necessária. |
| **DeliberateChoice** | `Choice.DeliberateChoice`<br>`Choice.deliberateChoice_implies_selects`<br>`Choice.deliberateChoice_implies_chooses` | **Caso A (Definição de Escolha Deliberativa)** | `DeliberateChoice s p q := Means s p ∧ Means s q ∧ Incompatible p q ∧ Asserts s p ∧ ¬ Asserts s q` — o sujeito concebe ambos os cornos, mas assere apenas um (`{Means, Subject}`). Acarreta seleção e escolha co-significada. |
| **Selects ↛ DeliberateChoice** | `HostileSemantics.selection_not_entails_deliberate_choice` | **Caso D (Separação Hostil)** | A seleção semântica não acarreta escolha deliberativa: `CountermodelVeridicalMeaning.Single` satisfaz `Selects () True False`, mas `DeliberateChoice` é impossível por não co-significar o corno rejeitado (`{}`). |
| **Selects ↛ Chooses** | `HostileSemantics.selection_does_not_imply_genuine_choice` | **Caso D (Separação Hostil)** | A seleção semântica NÃO força a co-significação de ambos os cornos incompatíveis exigida pelo antigo `Chooses`: `CountermodelVeridicalMeaning.Single` satisfaz `Selects () True False` enquanto `Chooses` é impossível (`{}`). |
| **Selects ↛ FreeWill** | `HostileSemantics.selection_does_not_imply_freewill` | **Caso D (Separação Hostil)** | A seleção semântica NÃO força liberdade libertária: um agente determinista representa, seleciona e exclui o corno incompatível sem contingência modal (`{}`). |
| **Asserts ↛ Asserts ∧ Means ¬p** | `HostileSemantics.CountermodelVeridicalMeaning.TwoPersons.assertion_does_not_imply_rejected_horn_meaning`<br>`HostileSemantics.CountermodelVeridicalMeaning.TwoPersons.full_fragment_without_deliberate_resource` | **Caso D (Separação Hostil)** | A asserção fáctica em dois sujeitos NÃO força a representação da negação contraditória: sob significação verídica, `Asserts` é satisfeito enquanto `deliberateGenuineChoiceResource` é provadamente falso (`{}`). |
| **AxIntentionalChoice / AxActPolarity → GenuineChoice** | `Choice.AxIntentionalChoice`<br>`Choice.AxActPolarity`<br>`Choice.genuineChoice_exists_of_act_constitutive`<br>`Choice.freeWill_exists` | **Caso B (Ponte Semântica Adotada)** | Sob o princípio constitutivo semântico adotado (`AxIntentionalChoice : Act s p → ∃ q, Chooses s p q`, SEM / A14), o ato intencional fecha a escolha genuína (`genuineChoice_exists_of_act_constitutive`) e o livre-arbítrio (`freeWill_exists`) sob `{AxIntentionalChoice, Initiates, Means, State, Subject}`. A tese de polaridade contraditória mais forte `AxActPolarity : Act s p → Means s (¬p)` (SEM / A13) acarreta estritamente `AxIntentionalChoice` via `act_polarity_implies_intentional_choice`. |
| **Doubt → GenuineChoice** | `Choice.Doubts`<br>`Choice.genuineChoice_of_doubt`<br>`Choice.freeWill_of_doubt` | **Caso B (Capacidade Cartesiana Candidata)** | Se o ato performativo for concebido como dúvida cartesiana (`Doubts s p := Means s p ∧ Means s (¬p)`), a escolha genuína e a liberdade do sujeito são imediatas (`{Means, Subject}`). |
| **ChoiceField ↛ Chooses** | `Choice.Chooses` / `rejectedHornCoMeant` (`F1b`) | **Caso D (Bloqueado)** | Não se segue logicamente da presença de alternativas que o sujeito escolha genuinamente (`Chooses(s,p,q)`: *escolha forte: o sujeito co-significa alternativas incompatíveis*). A escolha genuína exige que o sujeito co-signifique os DOIS cornos incompatíveis (`Means s p ∧ Means s (¬p)`); `Means` é uma relação opaca e `AxTwoSubjects` dá dois sujeitos DIFERENTES, cada um com um só conteúdo. Falta exatamente `rejectedHornCoMeant : (∃s p, Means s p) → ∃s p, Means s p ∧ Means s (¬p)`. `CountermodelNoFreeWill` mostra `Act ↛ Chooses` e `Act ↛ FreeWill` (`{}`); NÃO é contramodelo da definição `Chooses → FreeWill` (que é livre). **Milestone hostil 2026-09-18** (Batch fronteira escolha-genuína): o bloqueio é *irreducível* — o modelo veridical `CountermodelVeridicalMeaning` (significação veridical, `Means s p → p`) satisfaz TODO o fragmento agency/choice/order (datum do ato, pluralidade, certo/errado, `judge_commits`, falibilidade) com escolha genuína **vazia**, sob a própria definição Logos de `Chooses`; `not_entails_genuine_choice(_with_plurality)` (`{}`) formaliza a não-derivação; a via performativa assertiva é *impossível* por `assertion_consistency`/`no_one_asserts_incompatible_pair`, e a veridicalidade é refutada apenas por `genuineChoice_requires_error_possibility`. F1b permanece BLOCKED (**opção 3**: premissa substantiva nova seria necessária). |
| **Chooses → FreeWill** | `Choice.chooses_implies_freeWill` | **Caso A (Definicional)** | `FreeWill s := ∃p q, Chooses s p q` — por DEFINIÇÃO. A liberdade não é um passo metafísico adicional a partir do ato bruto; é a própria existência de uma escolha genuína entre alternativas incompatíveis. Footprint **`{Means, Subject}`** (VOCAB apenas — o conteúdo lógico é gratuito). A existência incondicional (`freeWillExists`) é que fica bloqueada, por depender de `rejectedHornCoMeant`. |

Declared (Level 2): `Subject` is an uninterpreted pure sort (`axiom Subject : Type`,
Tag: VOCAB); `State` is an uninterpreted state sort (`axiom State : Type`,
Tag: VOCAB); `act` is the uninterpreted weak performed event (`axiom act : Subject → Prop → Prop`,
Tag: VOCAB); `Means` is an uninterpreted intentional relation (`axiom Means : Subject → Prop → Prop`,
Tag: VOCAB); `Initiates` is the initiation of movement relation (`axiom Initiates : Subject → State → State → Prop → Prop`,
Tag: VOCAB); an act is a meaningful initiation: its constitutive content is intentional meaning, and its evental character is initiation (`Act s p := Means s p ∧ ∃ w w', Initiates s w w' p`);
`SubjectExists s := ∃ p, Act s p` is the constitutive rule of subjecthood (`act_requires_subject`);
`axiom Cogito` is **REMOVED ENTIRELY**; `Cogito` is a derived theorem from performative
assertion (`Asserts s p → ∃ s' p', Act s' p'`). Retorsion directly establishes the weak act via
`noWeakAct_selfRefutes : asserts speaker NoWeakAct → False` (`{Subject, act}`).
The strong retorsion shortcut is `noCogito_selfRefutes : Asserts speaker NoAct → False` (`{Initiates, Means, State, Subject}`)
under the intentional assertion `Asserts s p := Act s p ∧ p`.
`GroundProp`, `GroundPrincipleProp` (SEM); `AxPersonalGround` (META, D9).

### 14-Row Candidate Derivation Route Audit Table (`Act s p` to `Means s (¬p)`):

| Route | Intermediate Step | Classification | Exact Mathematical Obstruction |
|---|---|---|---|
| 1. Act → Means p | Analytic unrolling | DERIVES | `Act s p := Means s p ∧ ...`; only yields positive horn `Means s p`. |
| 2. Act → Asserts | Factive commitment | REQUIRES A NEW BRIDGE | Requires `act_implies_asserts_bridge` (factual truth of `p`). |
| 3. Act → Correct ∨ Incorrect | Bivalent partition | DERIVES | Proved via `act_iff_correct_or_incorrect` (C101). |
| 4. Correct/Incorrect → Means ¬p | Normative truth-value | DOES NOT DERIVE | Concerns truth-value of `p`, not mental representation of `¬p`. |
| 5. ChoiceField → Means ¬p | Incompatible availability | DOES NOT DERIVE | `¬p` occurs only in `Incompatible p (¬p) := ¬(p ∧ ¬p)`, not in `Means s _`. |
| 6. DeliberateChoice → Means ¬p | Deliberative co-meaning | REQUIRES A NEW BRIDGE | `DeliberateChoice` defines co-meaning, but `Act → DeliberateChoice` does not derive. |
| 7. Bivalence / LEM → Means ¬p | Propositional excluded middle | DOES NOT DERIVE | Intensional barrier: `p ∨ ¬p` in `Prop` does not force `Means s (¬p)`. |
| 8. Truth / Falsehood → Means ¬p | Semantic status | DOES NOT DERIVE | External truth-values do not populate intentional relations. |
| 9. Retorsion → Means ¬p | Performative contradiction | DOES NOT DERIVE | Refutes `NoAct`; does not force every act to co-mean contradictory negations. |
| 10. Intentional → Means ¬p | Representation faculty | DOES NOT DERIVE | `Intentional s := ∃ p, Means s p` provides only a single content. |
| 11. Person → Means ¬p | Rational personhood | DOES NOT DERIVE | Inherits only single intentional content of `Intentional s`. |
| 12. Plurality → Means ¬p | Distinct subjects | DOES NOT DERIVE | `AxTwoSubjects` gives two distinct subjects with single contents, not dual co-meaning. |
| 13. Modal Principles → Means ¬p | Propositional necessity | DOES NOT DERIVE | Modal backbone governs world-satisfaction, not internal cognitive representation. |
| 14. Grounding Principles → Means ¬p | Truthmaker grounding | DOES NOT DERIVE | `Ground e p` relates entities to propositions, entirely outside `Means`. |

### 6-Family Deeper Semantic Foundations Audit Table (Deriving A14 from Deeper Primitives):

| Foundational Family | Candidate Formulation | Strict Classification | Hostile Witness / Model | Analysis & Mathematical Obstruction |
|---|---|---|---|---|
| 1. Goal / End-Directedness | `Goal s g ∧ (p → g) → ∃ q, Means s q ∧ Incompatible g q` | **REFUTED BY HOSTILE MODEL** | `DeeperSemanticRoutes.hostileTeleologicalInstance` (`teleology_not_entails_contrastive_agency`) | In veridical semantics (`Means s p := p`), an agent acts for a genuine true goal `Goal s True`, but co-meaning an incompatible alternative $q$ requires $q \land \neg(\text{True} \land q) \equiv \bot$. Factive goal-directedness mathematically excludes entertaining incompatible alternatives. Defining `Goal` to include alternatives is **DEFINITIONAL RECODING — REJECTED**. |
| 2. Reason-Guided Agency | `ReasonFor s r p ∧ (r → p) → ∃ r' q, Means s r' ∧ Means s q ∧ Incompatible r q` | **REFUTED BY HOSTILE MODEL** | `DeeperSemanticRoutes.hostileReasonResponsiveInstance` (`reason_responsiveness_not_entails_contrastive_agency`) | Acting on a sufficient reason in the actual world does not require occurrent representation of contrary reasons in thought. Dispositions across hypothetical counterfactual worlds do not populate actual occurrent `Means`. |
| 3. Action Individuation under Description | `Description s p → ∃ q, Means s q ∧ Incompatible p q` | **REFUTED BY HOSTILE MODEL** | `DeeperSemanticRoutes.hostileActionIndividuationInstance` (`action_individuation_not_entails_contrastive_agency`) | Individuating an action under description $p = \text{True}$ distinguishes it from non-intended descriptions $p'$ without the subject representing any incompatible alternative description $q$ in thought. |
| 4. Non-Factive Representation Layer | `Entertains s p → ∃ q, Entertains s q ∧ Incompatible p q` | **REFUTED BY HOSTILE MODEL** | `DeeperSemanticRoutes.hostileRepresentationLayerInstance` (`nonfactive_representation_not_entails_contrastive_agency`) | Distinguishing `Means` from a non-factive representation faculty `Entertains` allows entertaining false contents in principle, but does not force the subject to entertain incompatible alternatives; single-content entertainment remains consistent. |
| 5. Counterfactual Agency (State Branching) | `CouldAct s q ∧ Incompatible p q → Means s q` | **REFUTED BY HOSTILE MODEL** | `ModelHierarchy.ModelM2BranchingInitiation` (`counterfactual_branching_not_entails_means`) | Model M2 exhibits physical state-space branching (`w = false ∧ w' ∈ {true, false}`), so alternative initiation holds (`CouldAct () False`), but internal intentional representation `Means () False` remains strictly false. Physical branching does not force cognitive representation. |
| 6. Contrastive Intentionality | `Act s p → ∃ q, Means s q ∧ Incompatible p q` | **REDUCED TO DEEPER SEMANTIC BRIDGE** · **REDUNDANT** | `fullTheoryHostileInstance` (`act_orthogonal_to_contrastive_agency_in_full_theory`) | Conceptually and logically equivalent to A14 (`contrastive_agency_equivalent_to_intentional_choice`). Strictly independent of pre-A14 primitives, forming the *weakest sufficient bridge identified so far* within the audited candidate family. |

### Auditoria de Circularidade Definicional dos Novos Predicados:

| Predicado | Definição Lean | Contém Conteúdo-Alvo? | Estado Extensional | Classificação Estrita |
|---|---|---|---|---|
| `RelationalIntentionality s p q` | `Act s p ∧ Incompatible p q ∧ Means s q` | Sim: contém `Means s q ∧ Incompatible p q` e `Means s p` via `Act`. | Equivalente a `Chooses s p q ∧ ∃ w w', Initiates s w w' p`. | **DEFINITIONAL RECODING — REJECTED** |
| `AlternativeSensitivity s p` | `∃ q, Means s q ∧ Incompatible p q` | Sim: contém o corno cognitivo contrastivo. | Idêntico a `ContrastiveAgency s p`. | **EQUIVALENT TO EXISTING TARGET** |
| `SettlesOn s p q` | `DeliberateChoice s p q` | Sim: contém `Chooses` e `Selects`. | Idêntico a `DeliberateChoice s p q`. | **DEFINITIONAL RECODING — REJECTED** |
| `Authors s p q` | `Act s p ∧ Incompatible p q ∧ ¬ Act s q` | Não: não contém `Means s q`. | Autoria executiva autônoma de `p` contra `q`. | **GENUINELY PRIMITIVE** |
| `DeliberateAuthorship s p q` | `Authors s p q ∧ Means s q` | Sim: conjunção explícita de autoria e representação do corno rejeitado. | Fatoração em dois fatores independentes. | **SEMANTIC BRIDGE COMPOSITION** |
| `TeleologicalAct s p g` | `Act s p ∧ Means s g ∧ (p → g)` | Não: não contém alternativa $q$. | Ação teleológica orientada a fins. | **GENUINELY PRIMITIVE** (depende de A14 para `Chooses`) |
| `ReasonResponsiveAct s p r` | `Act s p ∧ Means s r ∧ (r → p)` | Não: não contém alternativa $q$. | Ação sensível a razões. | **GENUINELY PRIMITIVE** (depende de A14 para `Chooses`) |
| `CounterfactualAct s p q` | `Act s p ∧ Incompatible p q ∧ ∃ w w', Initiates s w w' q` | Não: contém ramificação física, não mental. | Ação contrafactual no espaço de estados. | **GENUINELY PRIMITIVE** (separada por Model M2) |
| `DescriptiveAct s p` | `Act s p ∧ Means s p` | Não: conteúdo único. | Ação sob descrição. | **EQUIVALENT TO EXISTING TARGET** (`Act` já inclui `Means`) |

### Os Três Níveis de Constitutividade em Γ:
1. **Constitutivo por Definição (DEFINITIONAL):** `FreeWill` a partir de `Chooses` (`FreeWill s := ∃ p q, Chooses s p q`); `Chooses` a partir de `DeliberateAuthorship`.
2. **Constitutivo por Axioma Semântico (SEMANTIC):** `AxIntentionalChoice` (A14): compromisso substantivo de que o ato intencional envolve cognitivamente alternatividade, formalmente ortogonal aos primitivos pré-A14 (demonstrado por contramodelos no kernel).
3. **Constitutivo por Derivação (DERIVED):** `ChoiceField s p (¬p)` a partir de `Act s p`; `Selects s p (¬p)` a partir de `Asserts s p`.

### Decomposição Sub-A14 e Confirmação do Desfecho B (2026-09-20):
A investigação formal aprofundada nos módulos `Logos.CognitiveDiscrimination` e `Logos.SubContrastFoundations` estabelece:
1. **Decomposição Mínima de A14:** $A_{14}$ (`AxIntentionalChoice`) decompõe-se em dois sub-princípios estritamente mais fracos e filosoficamente independentes:
   - $A_D$ (`AxCognitiveContrast : Act s p → ∃ q, Discriminates s p q ∧ Incompatible p q`): polaridade / delimitação de fronteira.
   - $B_R$ (`AxCognitiveUptake : Means s p ∧ Discriminates s p q ∧ Incompatible p q → Means s q`): apreensão cognitiva do corno excluído.
   - Juntos, $A_D + B_R \vdash F_{1b}$; isoladamente, nenhum dos dois acarreta $F_{1b}$ (separados pelos contramodelos M1 e M3).
2. **Confirmação do Desfecho B (Contraste Não é Analítico):** O teorema de colapso intencional unário (`unary_intentional_collapse` e `generalized_expressivity_collapse`) prova que a intencionalidade não é intrinsecamente contrastiva. Qualquer conjectura de que a direcionalidade intencional `Means(s, p)` acarreta analiticamente a distinção de um segundo conteúdo $q$ está **definitivamente refutada** no kernel. O contraste cognitivo exige um compromisso semântico irredutível ($A_D$).
3. **Hierarquia de 12 Níveis:** Formalizada e máquina-verificada sem colapso entre níveis adjacentes:
   Direcionalidade Intencional ($L_1$) $\to$ Individuação de Objeto ($L_2$) $\to$ Diferenciação de Objeto ($L_3$) $\to$ Exclusão Cognitiva ($L_4$) $\to$ Diferenciação de Alternativa ($L_5$) $\to$ Disponibilidade de Alternativa ($L_6$) $\to$ Representação de Alternativa ($L_7$) $\to$ Co-Significação ($L_8$) $\to$ Deliberação ($L_9$) $\to$ Escolha ($L_{10}$) $\to$ Livre-Arbítrio ($L_{11}$) $\to$ Liberdade Libertista ($L_{12}$).
   O Teorema da Primeira Camada Inevitável prova que $L_1$ é a única camada cognitiva derivável do dado performativo isolado.

### Contraste Específico da Prova e Redução de A14 a Teorema Restrito (2026-09-20):
A investigação em `Logos.ProofSpecificContrast` reorienta a dedução de $F_{1b}$ do ato genérico para o ato performativo da prova efetiva de $\Gamma$:
1. **Desentrelaçamento dos Três Alvos:**
   - $A_{14}\text{-Universal}$: $\forall s\ p, \text{Act}(s, p) \to \exists q, \text{Chooses}(s, p, q)$ (FALSO para atos arbitrários no modelo $M_1$; excessivamente generalizado).
   - $A_{14}\text{-Existencial} / F_{1b}$: $(\exists s\ p, \text{Act}(s, p)) \to \exists s, \text{FreeWill}(s)$.
   - $\text{ProofSpecificContrast}$: o sujeito particular que executa a prova por retorção/reductio engaja intencionalmente conteúdos incompatíveis ($q$ e $\neg q$).
2. **Decomposição Fina de `Means`:** Decomposto em `Considers(s, p)` (presença cognitiva / entretenimento hipotético), `Affirms(s, p)` (asserção) e `Rejects(s, p)` (refutação).
3. **Semântica da Retorção / Reductio:** O teorema `reductio_engages_incompatible_contents` prova matematicamente (`{}`) que refutar $q$ exige considerar $q$ e afirmar $\neg q$ com $\text{Incompatible}(q, \neg q)$.
4. **Derivação Direta de $F_{1b}$:** O teorema `retorsion_proof_derives_F1b` prova que a execução performativa da prova de retorção com assimilação cognitiva acarreta $\exists s, \text{FreeWill}(s)$ diretamente, contornando completamente o axioma universal $A_{14}$.
5. **Escada de Contramodelos M0–M6:** Máquina-verificada sem colapso entre níveis adjacentes, de traço formal desprovido de sujeito (M0) até escolha genuína (M6).

### Auditoria Adversarial da Redução Redutiva e Fronteira Final (2026-09-20):
A investigação em `Logos.AdversarialReductioAudit` submete a estratégia redutiva ao escrutínio implacável da regra: *"Preferir perder o teorema a esconder a premissa"*:
1. **Auditoria de Circularidade de `RefutationalCognitiveUptake`:** O teorema `uptake_is_renamed_co_meaning_premise` prova (`{}`) que `RefutationalCognitiveUptake` é uma premissa renomeada equivalente à conjunção de co-significação (`Means s q ∧ Means s ¬q`), não sendo derivada dos primitivos pré-existentes de $\Gamma$.
2. **Equivocação Intencional (`MeansVolitional` vs `MeansRepresentational`):**
   - No ato forte `Act(s, p)`, `Means` opera como direcionamento volitivo / telos prático do agente.
   - Na consideração da hipótese adversária $q$ para reductio, $q$ é mantida sob escrutínio crítico para ser refutada.
   - O teorema `rational_subject_cannot_volitionally_aim_at_rejected_horn` prova (`{}`) que um sujeito que refuta e rejeita $q$ não pode ter $q$ como telos volitivo. Logo, `Means` em `Chooses` não pode ser unificado com a presença cognitiva de $q$ sem equivocar volição e representação.
3. **A Barreira de Um Corno Único (`affirmation_to_act_derives_one_horn_only`):** Mesmo admitindo a ponte mais forte entre asserção e ato (`Affirms s ¬q → Act s ¬q`), obtém-se no máximo `Means s ¬q`. O corno rejeitado $q$ permanece estritamente não derivado como conteúdo significado.
4. **Suíte Hostil M7–M12 e Classificação Quádrupla de $F_{1b}$:**
   - Contramodelos M7 a M12 máquina-verificados no kernel (`{}`).
   - O Estado A ($F_{1b}$ provado sem premissa semântica) é REFUTADO (`state_A_is_refuted`).
   - O Estado D ($F_{1b}$ bloqueado por contradição) é REFUTADO (`state_D_is_refuted`).
   - $F_{1b}$ classifica-se rigorosamente como **Estado C (ABERTO, com o hiato semântico reduzido ao princípio exato `ExactUptakeGap`)** ou condicionalmente como **Estado B (PROVADO sob `RefutationalCognitiveUptake` explícito)**.

### A Fronteira Cognitiva-Agencial e o Estabelecimento de Settlement-1 (2026-09-20):
A investigação em `Logos.CognitiveToAgencyFrontier` penetra na assimetria dinâmica da redução:
1. **Desambiguação Vocabular e Estrutura Dinâmica:** Formalização das operações finas (`Considers`, `Affirms`, `Rejects`, `CommitsTo`, `AimsAt`, `SettlesFor`, `Assumes`, `Derives`). A redução performativa é um processo assimétrico de transição de status (`ReductioProgression`): $q$ passa de assumida para rejeitada, enquanto $\neg q$ é afirmada (`reductio_induces_asymmetric_status_transition`, `{}`).
2. **Hierarquia de Liquidação Cognitiva (Settlement-1 a Settlement-5):**
   - **Settlement-1 (Resolução Cognitiva):** Provado categoricamente a partir da redução performativa (`reductio_proves_settlement_1`, `{}`). O sujeito adota postura avaliativa assimétrica entre conteúdos incompatíveis.
   - **Settlement-2 a Settlement-5:** Provado que Settlement-1 não acarreta significação intencional (`Means`), volição, escolha ou causalidade agencial (`settlement_1_does_not_imply_settlement_3`, `{}`).
3. **Teoremas Negativos Fortes:** Provado no kernel (`{}`) que a redução genuína é não-mecânica, não-passiva, não pode colapsar para um estado unipolar de um só corno (`reductio_cannot_collapse_to_one_horn`), e envolve necessariamente avaliação assimétrica (`reductio_necessarily_asymmetric`).
4. **Suíte Hostil M13–M18:** Separação estrita entre consideração dual (M13), avaliação sem compromisso (M14), liquidação sem escolha (M15), liquidação determinista (M16), escolha compatibilista (M17) e liquidação causal-agencial (M18).
5. **Proposição Cume da Fronteira:** A proposição mais forte demonstrável puramente a partir da redução performativa é que o sujeito executa necessariamente uma **liquidação cognitiva assimétrica (Settlement-1)** entre conteúdos incompatíveis, permanecendo a passagem para Escolha e Liberdade Libertária condicionada a princípios semânticos adicionais.

### Independência Modelo-Teórica do Livre-Arbítrio (2026-09-20):
A investigação em `Logos.FreeWillIndependence` resolve definitivamente o status do livre-arbítrio frente à base pré-A14 de $\Gamma$:
1. **Teorema de Independência Modelo-Teórica (`freewill_is_model_theoretically_independent`, `{}`):**
   - **Modelo A (`model_A_gamma_with_freewill`, `{}`):** Modelo completo da base ativa de $\Gamma$ (Cogito, Act, Sujeito Intencional, ReductioProgression, Settlement-1) onde o livre-arbítrio e a escolha genuína existem ($\Gamma \not\vdash \neg \text{FreeWill}$).
   - **Modelo B (`model_B_gamma_without_freewill`, `{}`):** Modelo completo da base ativa de $\Gamma$ onde nenhum sujeito possui livre-arbítrio e toda significação é estritamente unipolar ($\Gamma \not\vdash \text{FreeWill}$).
   - **Conclusão:** O Livre-Arbítrio é **estritamente independente** da base de $\Gamma$ sem $A_{14}$.
2. **Dilema Fundamental da Assimetria:** A liquidação intencional exige assimetria (`Means s ¬q ∧ ¬ Means s q`), enquanto `Chooses` exige co-significação de ambos os cornos (`Means s ¬q ∧ Means s q`). Logo, a liquidação prática bem-sucedida é formalmente incompatível com a escolha entre os mesmos cornos (`intentional_resolution_excludes_choice_of_same_horns`).
3. **Teste de Deliberação Idêntica e Ortogonalidade da Racionalidade:**
   - Formalização de Caso D (determinismo), Caso M (liberdade modal) e Caso A (causalidade agencial).
   - Demonstração de que a deliberação racional completa pode coexistir com determinismo estrito, e a escolha libertária pode ocorrer sem razões racionais (`rationality_orthogonal_to_libertarian_freedom`, `{}`).
4. **Pontes Mínimas $B_1$ a $B_4$:** Identificação dos princípios exatos para cruzar cada fronteira: $B_1$ (Compromisso Doxástico, SEM), $B_2$ (Co-Significação / Uptake Bilateral, SEM), $B_3$ (Pluralidade Modal, META), $B_4$ (Causalidade Agencial, META).

### Reconstrução da Escolha e Teste da Definição Reparada (2026-09-20):
A investigação em `Logos.ChoiceRepair` audita a possibilidade de reparar o conceito de escolha e livre-arbítrio com base na liquidação cognitiva assimétrica:
1. **Preservação Histórica:** As definições históricas `Chooses` e `FreeWill` foram congeladas intactas.
2. **Ortogonalidade Mútua entre Velha e Nova Escolha (`settlementChoice_orthogonal_to_old_chooses`, `{}`):**
   - `SettlementChoice(s, p, q)` (resolução avaliativa assimétrica) e `OldChooses(s, p, q)` (co-significação simétrica de ambos os cornos) são **estritamente ortogonais**: existem modelos com `SettlementChoice` sem `OldChooses` (modelos unipolares) e modelos com `OldChooses` sem `SettlementChoice` (sem rejeição).
3. **Hierarquia Agencial de 4 Níveis:** Separação estrita entre `CognitiveSettlement` (Nível 1), `VolitionalSettlement` (Nível 2), `ActionSelection` (Nível 3) e `AgentCausalSettlement` (Nível 4).
4. **Suíte Hostil M19–M26:**
   - M19–M22: Resolução sem volição (M19), volição sem capacidade alternativa (M20), seleção de ação sem indeterminização (M21), causalidade agencial (M22).
   - M23–M26: Deliberador totalmente determinista (M23), avaliador racional automático (M24), rastreador passivo de verdade (M25), escolha compatibilista sem liberdade modal bilateral (M26).
5. **Avaliação Frente à Deliberação Idêntica:** `SettlementChoice` é compatível com determinismo estrito (Caso D) e não acarreta liberdade modal (Caso M) nem determinação agencial (Caso A).
6. **Livre-Arbítrio Compatibilista vs Libertário:**
   - `FreeWill_Settlement` (compatibilista) é **derivável** da redução performativa (`reductio_derives_compatibilist_freeWill`, `{}`).
   - `FreeWill_Libertarian` (liberdade modal bilateral de ação) permanece **estritamente modelo-teoricamente independente** da base de $\Gamma$ (`libertarian_freewill_is_model_theoretically_independent`, `{}`).

### Auditoria Adversarial da Fronteira Agencial e Independência Exata (2026-09-20):
A investigação em `Logos.AgencyFrontierAudit` aprofunda o escrutínio conceitual sobre a transição da cognição à agência:
1. **Auditoria Nomenclatural:** `SettlementChoice` é puramente cognitivo (`settlementChoice_is_purely_cognitive`, `{}`). O teorema `reductio → SettlementChoice` comprova resolução cognitiva de conteúdos opostos, sem qualquer conteúdo volitivo ou discricionário; denominá-lo "Livre-Arbítrio" (`FreeWill_Settlement`) é estritamente uma convenção de nomenclatura (`freeWill_settlement_is_nomenclatural`, `{}`).
2. **Ingredientes Faltantes da Escolha Genuína:** Identificação de quatro dimensões irredutíveis: adoção executiva (`SettlesForHorn`), fonte autoral do sujeito (`AgentSource`), capacidade modal alternativa (`CouldHaveSettledOtherwise`) e determinação pela substância agencial (`AgentDeterminesHorn`).
3. **Suíte Hostil M27–M32 e Diferenciador Estrutural:**
   - M27: resolvedor cognitivo puro (sem volição).
   - M28: avaliador determinista estrito.
   - M29: rastreador passivo de verdade.
   - M30: mecanismo automático de preferência.
   - M31: desempate não-agencial indiferente.
   - M32: candidato a escolha genuína (`DiscretionaryChoice`).
   - O diferenciador estrutural exato (`structural_choice_differentiator`, `{}`) estabelece que a agência genuína exige a conjunção de mira executiva (`AimsAt`), adoção prática pessoal (`SettlesFor`) e determinação pela substância agencial (`AgentDetermines`).
4. **Desacoplamento de Determinismo, Indeterminismo e Agência:** Prova formal de que `Chooses` e `SettlementChoice` são compatíveis com determinismo estrito; o indeterminismo físico/bruto não acarreta escolha (`indeterminism_does_not_imply_choice`, `{}`); alternativas modais sem agência (`modal_alternatives_without_agency`, `{}`); agência sem alternativas modais (`agency_without_modal_alternatives`, `{}`).
5. **Fronteira Exata de Independência Modelo-Teórica:**
   Provas de independência de dois lados ($\Gamma_{\text{pre-}A_{14}} \not\vdash P^*$ e $\Gamma_{\text{pre-}A_{14}} \not\vdash \neg P^*$) no kernel para:
   - `Agency*` (`agency_star_is_model_theoretically_independent`, `{}`).
   - `Volition*` (`volition_star_is_model_theoretically_independent`, `{}`).
   - `Choice*` (`choice_star_is_model_theoretically_independent`, `{}`).
   - `ModalFreedom*` (`modalFreedom_star_is_model_theoretically_independent`, `{}`).
   - `AgentCausalSettlement*` (`agentCausalSettlement_star_is_model_theoretically_independent`, `{}`).

### Auditoria Filosófica de A14 e Fronteira Semântica Irredutível (2026-09-20):
A investigação em `Logos.A14SemanticAudit` fecha o escrutínio formal sobre o axioma A14 (`AxIntentionalChoice`):
1. **Teorema da Fronteira Semântica Irredutível (`irreducible_semantic_boundary_of_a14`, `{propext}`):**
   - Demonstra que A14 é exatamente equivalente à atribuição ao sujeito do corno cognitivo ausente (`MissingHornPrinciple`, `{}`).
   - Nenhum princípio independente de ação teleológica ($B_1$), responsividade a razões ($B_2$) ou autoria ($B_3$) deduz A14 (`candidate_principles_fail_to_derive_a14`, `{}`); qualquer princípio $B$ que acarrete A14 na base de $\Gamma$ acarreta necessariamente o princípio do corno ausente. Logo, A14 é a **fronteira semântica irredutível** da transição de ação intencional a escolha.
2. **Auditoria de Semânticas Concorrentes de Ação:**
   - Formalização de 5 noções de `Act`: Minimal, Contrastiva, Teleológica, Autoral, Responsiva.
   - Redefinir `Act` como contrastivo satisfaz A14 de forma puramente tautológica (`act_contrastive_trivializes_a14`, `{}`), demonstrando que isso não deduz a escolha, apenas transfere a premissa para a definição de ação (contrabando conceitual).
3. **Ataque às Leis Semânticas de `Means`:**
   - Fecho sob negação (`negation_closure_of_means_fails`, `{}`), fecho inferencial (`inferential_closure_of_means_fails`, `{}`) e relevância contrastiva (`contrastive_closure_of_means_fails`, `{}`) são refutados por contramodelos unipolares.
4. **Teorema da Fronteira Performativa (`performative_boundary_theorem`, `{}`):**
   - A retorsão transcendental estabelece um sujeito intencional e resolução cognitiva assimétrica, parando antes de volição (`AimsAt`) e execução externa de ação (`Act`). A pessoalidade é unificada constitutivamente com o Livre-Arbítrio derivado da normatividade (`Person s := FreeSubject s`).
5. **Cadeia Incremental de Escolha em 9 Níveis:**
   - Modelos formais de separação ({}) provam que representação, avaliação, assentamento, autoria, mira prática, autoatribuição, causação substancial, sensibilidade a razões e disponibilidade modal bilateral são conceitos estritamente distintos e não-colapsáveis.

### Auditoria da Fronteira Pós-A14: Limites de Assentamento, Compromisso, Volição e Agência (2026-09-20):
A campanha em `Logos.PostA14Frontier` estabelece os limites exatos da teoria com e sem A14:
1. **Fronteira Teorema a Teorema na Escada Agencial (`agency_ladder_frontier_synthesis`, `{}`):**
   - $\text{SettlementChoice} \land \text{DoxasticCommitmentHorn} \iff \text{SettlementChoice} \land \text{CommitsTo}$.
   - $\text{SettlementChoice} \land \text{TeleologicalAimHorn} \iff \text{VolitionalSettlement}$.
   - $\text{VolitionalSettlement} \land \text{ExecutiveInitiationHorn} \iff \text{VolitionalSettlement} \land \text{Initiates}$.
   Cada transição exige seu corno semântico exato e falha estritamente sem ele.
2. **Modelos Hostis de Separação na Escada:**
   - `separation_settlement_without_commitment` (`{}`): Resolução cognitiva pura sem tomada de postura doxástica/normativa.
   - `separation_commitment_without_volition` (`{}`): Crença/compromisso teórico sem qualquer mira prática ou telos.
   - `separation_volition_without_agency` (`{}`): Vontade paralisada — volição interna plena sem instanciação no mundo.
3. **Escopo e Limites da Teoria Pós-A14:**
   - $\Gamma + A14$ prova a escolha histórica a partir do ato (`post_a14_derives_old_chooses`, `{}`), mas falha estritamente em derivar compromisso doxástico (`post_a14_fails_to_derive_commitment`, `{}`) ou escolha discricionária substantiva (`post_a14_fails_to_derive_discretionary_choice`, `{}`).
4. **Cinco Arquétipos Hostis Canônicos ({})**:
   - `archetype_passive_truth_tracker`: Rastreador passivo de verdade (calcula verdades sem compromisso).
   - `archetype_deterministic_evaluator`: Avaliador determinístico (computa regras dedutivas sem determinação pelo agente).
   - `archetype_theoretical_deliberator`: Deliberador puramente teórico (comprometido com a verdade, mas desprovido de fins práticos).
   - `archetype_puppet_unauthored_aims`: Marionete com metas não-autorais (metas sub-pessoais ou impostas externamente).
   - `archetype_non_reflexive_chooser`: Escolhedor autoral não-reflexivo (escolhedor de primeira ordem sem autoatribuição reflexiva).

### Auditoria da Fronteira Agencial Definitiva (2026-09-20):
A campanha em `Logos.DefinitiveAgencyFrontier` estabelece os limites matemáticos finais sobre a hierarquia agencial pós-A14:
1. **Modelos C1–C5 (Assentamento, Avaliação e Compromisso):**
   - `model_C1_passive_truth_tracker`, `model_C2_formal_evaluator`, `model_C3_suspended_judgment`, `model_C4_assertion_without_commitment`, `model_C5_commitment_without_assertion` ({}) separam formalmente assentamento, avaliação algorítmica, compromisso privado e asserção pública.
2. **Fracasso da Retorsão do Compromisso (`retorsion_denial_does_not_commit_to_content`, `{}`):**
   - Asserir "não me comprometo com p" reflete o ato da asserção, mas NÃO acarreta compromisso performativo com p. O ceticismo ou desprendimento doxástico de primeira ordem é performativamente não-autodestrutivo.
3. **Ponte Semântica de Sinceridade (`sincerity_is_independent`, `{}`):**
   - O princípio de sinceridade (`Asserts s p → CommitsTo s p`) é uma ponte semântica independente (Tag: SEM), não um teorema lógico.
4. **Modelos V1–V5 (Compromisso vs Volição):**
   - `model_V1_pure_theoretician`, `model_V2_aim_without_deliberative_settlement`, `model_V3_commitment_to_unwanted_fact`, `model_V4_external_objective`, `model_V5_spontaneous_aim` ({}) provam a irredutibilidade mútua entre crença teórica e mira prática.
5. **Agência Isolada vs Agência no Datum Performativo:**
   - A volição isolada não acarreta iniciação externa (`standalone_volition_fails_to_derive_agency`, `{}`), mas dentro do datum performativo `Act(s, p)`, a iniciação já é fornecida pelo próprio ato (`performative_datum_supplies_executive_initiation`, `{}`).
6. **Modelos A1–A5 e Autoatribuição:**
   - Marionete (`model_A1_puppet`), otimizador externo (`model_A2_external_optimizer`), execução subpessoal (`model_A3_subpersonal_execution`), execução sem autor (`model_A4_authorless_execution`) e autor sem autoatribuição reflexiva (`model_A5_author_without_self_attribution`, `{}`).
7. **Causalidade Agencial e Compatibilismo (AC1–AC5):**
   - Compatibilidade de sensibilidade a razões com determinismo (`reason_responsiveness_compatible_with_determinism`, `{}`).
   - AC1–AC5: Causalidade do agente determinística (`model_AC1_deterministic_agent_causal`), acaso indeterminístico sem agência (`model_AC2_indeterministic_chance`), determinação externa (`model_AC3_externally_determined`), determinação agencial sem alternativas modais (`model_AC4_agent_causal_without_alternatives`) e modelo libertista pleno (`model_AC5_full_libertarian`, `{}`).
8. **As Seis Noções de Livre-Arbítrio e a Desambiguação de Vocabulário (`free_will_hierarchy_implications`, `{}`):**
   - `LibertarianFreeWill → AgentCausalFreeWill → CompatibilistFreeWill → VolitionalFreeWill → CognitiveFreeWill`.
9. **Independência Bilateral e Invariância por Colapso:**
   - Independência bilateral de compromisso e volição (`two_sided_independence_commitment`, `two_sided_independence_volition`, `{}`).
   - Teorema de invariância por colapso sob $T_{\text{uncommit}}$ (`collapse_invariance_pre_commitment`, `{}`): nenhuma fórmula da linguagem cognitiva pode definir compromisso.
10. **Descomissionamento de SubstantivePerson e Unificação de Pessoa:**
   - O antigo predicado opaco `SubstantivePerson` foi auditado e reconhecido como uma lacuna meramente sintética (Categoria 3). Na ontologia unificada de $\Gamma$, a Pessoa é definida constitutivamente pelo Livre-Arbítrio (`Person s := FreeSubject s ↔ FreeWill s`), derivando a pessoalidade com 0 axiomas substantivos.
11. **Síntese Mestra da Fronteira Agencial (`definitive_agency_frontier_synthesis`, `{}`).**

### Auditoria da Fronteira Modal e do Fundamento (2026-09-20):
A campanha em `Logos.GroundingFrontier` estabelece os limites matemáticos e ontológicos da passagem da verdade necessária à realidade necessária e ao fundamento último:
1. **Hierarquia de Pontes Candidatas (G1–G4):**
   - G4 (`Candidate_G4`, persistência forte) $\implies$ G2 (`Candidate_G2`) $\implies$ G1 (`Candidate_G1`, existência modal fraca) (`implication_G4_implies_G2`, `implication_G2_implies_G1`, `{}`).
   - Separação estrita G1 $\not\implies$ G2 (`separation_G1_not_implies_G2`, `{}`): a verdade necessária com testemunhas mundiais contingentes não força a existência de entidade necessária.
2. **Análise de Quantificadores ($\forall w \exists e$ vs $\exists e \forall w$) e o Corno Faltante do Fundamento:**
   - O truthmaking mundano ($\forall w \exists e$) não acarreta fundamento necessário uniforme ($\exists e \forall w$) (`worldwise_fails_to_derive_uniform_ground`, `{}`).
   - Isolamento do Corno Rígido Faltante (`MissingRigidGroundHorn`): o fundamento uniforme equivale estritamente ao truthmaking mundano conjugado ao corno rígido (`uniform_ground_iff_worldwise_and_missing_horn`, `{}`).
   - Sob domínio constante e unicidade modal, a troca quantificacional é teorema lógico (`quantifier_exchange_under_uniqueness`, `{}`).
3. **Auditoria Crítica de A4 (`AxGlobalGround`):**
   - A4 não acarreta unicidade de fundamentadores (`a4_does_not_imply_unique_ground`, `{}`): múltiplas entidades necessárias podem fundamentar a mesma verdade.
   - A4 não acarreta fundamento comum para verdades distintas (`a4_does_not_imply_single_common_ground`, `{}`).
   - A4 não acarreta boa-fundação nem fundamento último.
4. **Hierarquia de Boa-Fundação (U1–U6) e Teorema do Fundamento Último Mínimo:**
   - Cadeias infinitas descendentes (`infinite_descending_chain_has_no_ultimate_ground`, `{}`) e ciclos finitos (`cyclic_grounding_has_no_ultimate_ground`, `{}`) eliminam o fundamento último.
   - Teorema do Fundamento Último Mínimo (`minimal_ultimate_ground_theorem`, `{}`): ancestralidade finita/limitada força a existência de elemento terminal incausado.
5. **Auditoria de Pontes de Pessoalidade (P1–P6) e Modelos Hostis P1–P5 ({})**:
   - Substrato impessoal (`model_P1_impersonal_substrate`), realização estrutural (`model_P2_structural_realization`), intencionalidade emergente (`model_P3_emergent_intentionality`), múltiplos fundamentadores impessoais (`model_P4_multiple_impersonal_grounders`) e fundamento último anônimo (`model_P5_anonymous_ultimate_ground`).
   - Sujeito intencional + verdade necessária não forçam realidade necessária (`performative_subject_and_nec_truth_do_not_force_necessary_entity`, `{}`).
   - A negação de fundamento necessário é performativamente coerente e não-autodestrutiva (`denial_of_necessary_ground_is_non_self_refuting`, `{}`).
6. **Unicidade e Pluralidade:**
   - Fundamento último não acarreta unicidade (`ultimate_ground_does_not_imply_uniqueness`, `{}`).
   - Fundamento último não acarreta pluralidade (`ultimate_ground_does_not_imply_plurality`, `{}`).
7. **Dez Modelos Hostis Canônicos de Fundamento (G1–G10) e Invariância por Colapso:**
   - Família completa G1–G10 formalizada e verificada ({}); teorema de colapso impessoal (`collapse_invariance_impersonal`, `{}`) prova que a linguagem de truthmaking não pode definir pessoalidade.
8. **Síntese Mestra da Fronteira do Fundamento (`grounding_frontier_synthesis`, `{}`).**

### Auditoria de Negação dos Axiomas Substantivos (2026-09-20):
A campanha em `Logos.AxiomNegationAudit` executou a busca sistemática por necessidade oculta em $\Gamma$, testando a negação de cada um dos 9 axiomas substantivos (SEM e META) contra o núcleo matemático inevitável $\Gamma_{\text{core}}$:
1. **Nenhum Axioma Substantivo é Forçado pelo Núcleo ($\Gamma_{\text{core}} \not\vdash A$):**
   - $\neg \text{AxIntentionalChoice}$ (A14): consistente com o núcleo performativo (`core_compatible_with_neg_a14`, `{}`); refuta necessidade oculta de A14.
   - $\neg \text{AxActPolarity}$ (A13): consistente com o núcleo performativo (`core_compatible_with_neg_a13`, `{}`).
   - $\neg \text{AxGlobalGround}$ (A4): consistente com a lógica modal e conteúdo contingente (`core_compatible_with_neg_a4`, `{}`).
   - $\neg \text{Truthmaker}$ (A3) / $\neg \text{GroundPrincipleProp}$: consistente sob verdade deflacionária (`core_compatible_with_neg_truthmaker`, `{}`).
   - $\neg \text{universal\_thesis\_claims\_objectivity}$ / $\neg \text{transcendental\_reflection\_intentional}$: consistente sob assertor não-objetivista (`core_compatible_with_neg_retorsion_obj`, `{}`).
   - $\neg \text{AxTwoSubjects}$ (A6): consistente com o universo solitário (`core_compatible_with_neg_a6`, `{}`).
   - $\neg \text{AxPersonalGround}$ (A7): consistente sob substrato impessoal (`core_compatible_with_neg_a7`, `{}`).
2. **Teorema Mestre de Ausência de Necessidade Oculta (`no_hidden_necessity_synthesis`, `{}`):**
   - Prova formal no kernel de que todos os axiomas substantivos permanecem genuinamente adicionais e independentes de $\Gamma_{\text{core}}$.
   - Nenhum teorema com pegada vazia `{}` contradiz qualquer negação de axioma. Todos os 9 axiomas são compromissos semânticos ou metafísicos genuínos.

## Deferred / blocked

| ID | Prose | Status | Missing |
|----|-------|--------|---------|
| F1a | §13–§15 choice-field existence (`∃s p q`, `ChoiceField s p q`) | PROVEN | `person_hasChoiceField`/`choiceField_exists` `{Means, Subject}` + `judge_commits` `CL` (choice-realism batch, C51–C52/C55; renamed 2026-09-18 — field form, not genuine choice) |
| F1b | §15 genuine choice & freedom of the actor | PROVEN↑ | `Choice.freeWill_exists` / `Choice.freeSubject_exists` / `Choice.genuineChoice_exists_of_act_constitutive` sob `{AxIntentionalChoice, Initiates, Means, State, Subject}` (rota do Cogito / A14). Alternativamente, sob a **rota de retorsão normativa** (`Logos.RetorsiveNormativity.retorsion_derives_free_will`), demonstrado sob `{AxJudicativeBipolarity, Initiates, Means, State, Subject}` (`Tag: SEM`, bipolaridade judicativa), onde a negação de normatividade genuína refuta-se performativamente ao ser assertida como juízo correto, instanciando `GenuineNormativity` e derivando `Chooses` e `FreeWill` sem depender de `AxIntentionalChoice`. |
| F2 | §21 teleology (`Ought → Goal`) | DEFERRED | deontic layer (normativity → telos; ver C113–C121 para a retorsão do dever prático) |
| F3 | §28 Good (`§20 → bem`) | DEFERRED | moral good from logical normativity not yet derived |
| F4 | §28 Love | PROVEN↑ | `Love.T13_someoneLovable` (C41) under `{AxTwoSubjects, Means, Subject}` |
| F5 | §28 EternalRelation | → PROVEN↑ | dissolved in C42: `Love.T14_eternalRelation_conditional` under `{AxTwoSubjects, Means, Subject}` |
| F6 | §28 Trinity | DEFERRED | no argument exists yet (§28/§29) |
| Q7.2 | weaker `AxGlobalGround` | ANSWERED | answered by batch A2-swap-theorem: for atoms the swap needs no premise at all (definitional via world-vacuous `ExistsAt`); the compound instance is unforced, not weaken-able (DESIGN.md) |

## Level 3 — modal, choice, interpersonal value (new: poem chain)

| ID | Poem | Lean theorem | Status | Axiom footprint |
|----|------|--------------|--------|-----------------|
| C35 | P2 | `Core.negatedAbsolutes : ¬ (N_T ∨ N_F)` | PROVEN | `{}` (E0) |
| C36 | P2 | `Core.rightWrongDistinction : ¬ N_T ∧ ¬ N_F` | PROVEN | `{}` (E0) |
| C37 | P2 | `Semantics.bothNecessarilyTrueAndFalse` | PROVEN | `CL` |
| C59 | §27 | `Semantics.strongTruthExists : ∃ τ : Semantics.Form, Semantics.NecessarilyTrue τ` — "Strong Truth Exists" resident axiom-free ("há certo E há errado"; corolário nomeado de C37, residente no barrel 2026-09-18) | PROVEN | **`{CL}`** (C37 lever) |
| C93 | §27 | `Semantics.noStrongTruth_selfRefutes : ¬ (¬ ∃ τ : Semantics.Form, Semantics.NecessarilyTrue τ)` — retorsão performativa: negar a verdade forte refuta-se a si mesma (o ato de negar é destruído por ela) | PROVEN | **`{CL}`** (via C59) |
| C94 | §27 | `Choice.noStrongTruth_assertable_refutes : Asserts speaker (¬ ∃ τ : Semantics.Form, Semantics.NecessarilyTrue τ) → False` — retorsão assertiva do dado mundial: ninguém pode asserir que não existe verdade forte (o ato de negar o dado é destruído por ele) | PROVEN | **`{Initiates, Means, State, Subject, CL}`** (via C93 + Asserts) |
| C95 | §27 | `Semantics.atoms_are_modally_free : ∀ n : Nat, ¬ NecessarilyTrue (Form.atom n) ∧ ¬ NecessarilyFalse (Form.atom n)` — a parede dos átomos (fronteira de C59): nenhum átomo é fixado no percurso modal — a verdade forte fixa leis, não conteúdos | PROVEN | **`{}`** (Vocab puro, sem axiomas; `strongTruth_is_not_atomic` leva `{CL}`) |
| C96 | §27 | `Semantics.some_formula_contingent : ∃ τ : Semantics.Form, ¬ NecessarilyTrue τ ∧ ¬ NecessarilyFalse τ` — conteúdo contingente existe (contrapeso de C59): há fórmula nem necessariamente-verdadeira nem necessariamente-falsa — o percurso modal não é degenerado | PROVEN | **`{}`** (via C95; `strongTruth_and_contingent_content` leva `{CL}`) |
| C38 | P2 | `Necessity.necDistinction : Necessity (¬ N_T ∧ ¬ N_F)` | PROVEN (was AXIOM) | `{}` (E0; C1: identity-model alias; world content = C37) |
| C39 | P4 | `Choice.T11_choiceField` | PROVEN | `{Initiates, Means, State, Subject}` (campo de escolha — não escolha genuína — derivado do ato intencional C68 → C24 → C39; renomeação/split 2026-09-18; **usa C24 só no sentido fraco** `∃p, Means s p` — forma mais forte válida = reancoragem em `SubjectExists`/`Intentional`) |
| C40 | P5/P7 | `Plurality.T12_twoPersons` | PROVEN↑ | `{AxTwoSubjects, Means, Subject}` (settled by Unit countermodel that 1 act does not entail plurality; requires META bridge `AxTwoSubjects`) |
| C41 | P7 | `Love.T13_someoneLovable` | PROVEN↑ | `{AxTwoSubjects, Means, Subject}` (via C40) |
| C48 | §25/P1 | `Plurality.cogito_from_T12` | PROVEN↑ | `{AxTwoSubjects, Means, Subject}` |
| C49 | §13/IM_STUPID | `Choice.meaning_needs_subject` + `Choice.meaning_I_needs_subject` (definitional form: `Meaning_I p → ∃s, Means s p`) | PROVEN | `{Means, Subject}` |
| C50 | §14 | `Choice.incompatible_self_negation` | PROVEN | **`{}`** (pure logic — the field around any meaning-act) |
| C51 | §14/IM_STUPID | `Choice.person_hasChoiceField : Person s → ∃p q, ChoiceField s p q` — **subject ⇒ campo de escolha** (renomeado 2026-09-18; NÃO é escolha genuína) | PROVEN | `{Means, Subject}` |
| C52 | §14 | `Choice.choiceField_exists` | PROVEN | `{Initiates, Means, State, Subject}` (o campo é real, derivado do ato intencional C68 → C52 via `intentional_hasChoiceField` a partir de `act_implies_intentional` — reancorado em código 2026-09-18, sem passar por `Person`; renomeado 2026-09-18) |
| C53 | §14 | `Choice.noChoiceField_selfRefutes : Asserts speaker NoChoiceField → False` | PROVEN | `{Initiates, Means, State, Subject}` (retorsão performativa do campo: negar o campo é ele próprio um ato de campo contra a sua negação) |
| C54 | IM_STUPID §2 | `Plurality.JUDGE_HAS_CHOICE_FIELD : (¬N_T ∧ ¬N_F) → ∃s p q, ChoiceField s p q` — **right/wrong ⇒ campo de escolha** | PROVEN↑ | `{AxTwoSubjects, Means, Subject}` (derivação operativa via AxTwoSubjects h e person_hasChoiceField) |
| C55 | §8/§14 | `Order.judge_commits : ∃s p q, A s p ∧ (Correct s p ∨ Incorrect s p) ∧ ChoiceField s p q` — the judge HAS a choice-field (não escolha genuína) | PROVEN | `{Initiates, Means, State, Subject, CL}` (defs act-relative §8; usa o dado performativo do ato) |
| C56 | P6 | `Value.alone_no_other_help_harm` | PROVEN | `{Subject}` |
| C57 | §26 | `Choice.noSubject_selfRefutes : Asserts speaker NoSubject → False` | PROVEN | `{Initiates, Means, State, Subject}` (retorsão performativa genuína: negar o sujeito é um ato que testemunha o sujeito) |
| C42 | P8 | `Love.T14_eternalRelation_conditional` | PROVEN↑ | `{AxTwoSubjects, Means, Subject}` (sob o princípio de estabilidade pessoal e princípio relacional de amor) |
| C43 | P8 | `Love.T14_content_conditional` | PROVEN↑ | `{AxTwoSubjects, Means, Subject}` |
| C44 | P8 | `Love.T14_world_conditional` (`NecessityPH`) | PROVEN↑ | `{AxTwoSubjects, Means, Subject}` (world-anchored conditional □) |
| C45 | P8 | `Love.T14_square_conditional` (alias `Necessity`) | PROVEN↑ | `{AxTwoSubjects, Means, Subject}` (conditional) |
| C46 | P5 | `Value.valueInterpersonal_of_split_conditional` | PROVEN↑ | `{AxTwoSubjects, Means, Subject}` (sob o princípio PersonsAffectPrinciple) |
| C47 | P5/P7 | `Plurality.T12_directedPair_conditional` | PROVEN↑ | `{AxTwoSubjects, Means, Subject}` (sob o princípio PersonsAffectPrinciple) |
| C61 | P3 | `Plurality.rightWrong_implies_someone_means` — "há certo e há errado → há alguém para quem algo significar" | PROVEN↑ | `{AxTwoSubjects, Means, Subject}` (`JUDGE_HAS_CHOICE_FIELD` C54 ∘ `rightWrongDistinction` C36) |
| C62 | P3 | `Order.rightWrong_implies_meaning` (+ `Order.rightDistinctWrong_implies_meaning`) | PROVEN | `{Initiates, Means, State, Subject}` (o juízo desdobra-se num ato com significado, `A s p := Means s p ∧ ∃ w w', Initiates s w w' p`) |
| C101 | §8 | `Order.act_iff_asserts_or_incorrect : A s p ↔ Asserts s p ∨ Incorrect s p` — **partição bivalente do ato intencional**: todo ato intencional é asserção verídica ou juízo incorreto | PROVEN | `{Initiates, Means, State, Subject, CL}` |
| C97 | §15 | `Choice.deliberateChoice_implies_selects : DeliberateChoice s p q → Selects s p q` — **escolha deliberativa acarreta seleção**: quem delibera seleciona a favor de p e contra q | PROVEN | `{Initiates, Means, State, Subject}` |
| C98 | §15 | `Choice.deliberateChoice_implies_chooses : DeliberateChoice s p q → Chooses s p q` — **escolha deliberativa acarreta escolha co-significada**: quem delibera concebe ambos os cornos | PROVEN | `{Initiates, Means, State, Subject}` |
| C99 | §15 | `Choice.selection_exists_of_act (hBridge : act_implies_asserts_bridge) (h : ∃ s p, Act s p) : ∃ s p q, Selects s p q` — **existência de seleção a partir do ato sob a ponte**: o ato rende seleção sob a ponte semântica | PROVEN | `{Initiates, Means, State, Subject}` |
| C100 | §15 | `Choice.deliberateChoice_iff_selects_and_means : DeliberateChoice s p q ↔ Selects s p q ∧ Means s q` — **decomposição exata da escolha deliberativa**: deliberação é seleção semântica mais representação da alternativa rejeitada | PROVEN | `{Initiates, Means, State, Subject}` |
| C69 | §15/F1b | origin freedom (retired) | BLOCKED | (retired: manufactured freedom via `Sum.inl` destroyed under hostile semantics; genuine-choice replacement is `Choice.Chooses`/`rejectedHornCoMeant`) |
| C70 | §15/F1b | posited content non-freedom (retired) | BLOCKED | (retired: manufactured free will destroyed under hostile semantics) |
| C71 | §15/F1b | origin-freedom denial self-refutation (retired) | BLOCKED | (retired: manufactured freedom destroyed under hostile semantics) |
| C72 | §15/F1b | judge is free (retired) | BLOCKED | (retired: act does not entail free will; `Order.judge_commits` yields only the choice field; `Chooses → FreeWill` is definitional but its existence needs `rejectedHornCoMeant`) |
| C73 | P5/P7 | `Person.twoPersonsFromSubject` | BLOCKED | (demoted: Unit countermodel settles that 1 act does not entail plurality; manufactured `Sum.inl`/`inr` witness destroyed) |
| C74 | P5 | `Value.aloneExcluded : ¬ ∃ s, Person s ∧ Alone s` | PROVEN↑ | `{AxTwoSubjects, Means, Subject}` (under the plurality bridge `AxTwoSubjects`, a lone person is excluded) |
| C75 | P7 | `Person.everyContentIsAPerson` | BLOCKED | (killed under hostile semantics: content existence does not imply personhood; tripartite report) |
| C76 | P8 | `Love.T14_canonicalRigid` | BLOCKED | (excised: manufactured witness destroyed) |
| C77 | P5/P8 | `Love.necessaryPersonExists_conditional` | PROVEN | `{Initiates, Means, State, Subject}` (condicional; a necessidade do sujeito não se segue do ato contingente, como provado pelo contramodelo de agência contingente) |
| C85 | P6 | `Value.help_not_harm` — **princípio de benevolência**: no plano fundante, ajudar exclui prejudicar (`Helps s t → ¬ Harms s t`) | PROVEN | `{Subject}` |
| C86 | P6/P8 | `Love.love_helps` (+ `Love.love_not_harms`, `Love.loves_of_helps`) — **amor como benevolência direcionada**: amar é ajudar e não prejudicar (`Loves s t := Helps s t ∧ ¬ Harms s t`) | PROVEN | `{Subject}` |
| C92 | P8/§27 | `Love.necessary_entity_exists_conditional` | PROVEN | `{Initiates, Means, State, Subject}` (condicional; entidade necessária não é acarretada pelo ato performativo) |

Declared (Level 3): **M1 (A3, 2026-09-16): `Affects` is a structural
DEFINITION (`Affects s t := s ≠ t`), and `AxPersonsAffect` is a THEOREM** (distinct persons are
distinct — `Or.inl hne`). `Helps` is its positive projection (`:= Affects`),
`Harms` has no reality in the foundational order (`:= False`), and
`help_not_harm` is a THEOREM (`{}`).
`Loves` is **benevolent love** (`Loves s t := Helps s t ∧ ¬ Harms s t`, C86).
The plurality bridge `AxTwoSubjects` (Tag: META) is **RESTORED** as the honest metaphysical price of plurality,
following the mathematical proof of the Unit countermodel in `HostileSemantics`.
(C74) make solipsism structurally impossible.
`PersonStabilityPrinciple` is the explicit modal hypothesis for world-persistence of persons (`Person s → NecessarySubject s`).
It is NOT a theorem of pure performative logic: the countermodels `CountermodelPersonNotNecessary` and `ContingentAgencyModel`
in `HostileSemantics` formally prove that an intentional act at `actualWorld` does not entail modal necessity across all worlds.
C77 and C92 are explicitly CONDITIONAL on this hypothesis.
T14 stands on the pair under `AxTwoSubjects` and `PersonStabilityPrinciple`.
Modal layer is derived (C1): `Necessity: Prop → Prop` is a *definition*
(identity-model alias) and `NecessityPH : (World → Prop) → Prop` the
semantics-grounded operator; `necK/necT/nec4` (alias) and `necKPH/necTPH/nec4PH`
are theorem; `necDistinction` is a theorem. No modal axiom remains.

## Level 2c — the act as initiation (`Logos.Initiation`, 2026-09-17)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C63 | Detailed | `Initiation.branches_not_transfer : Branches R → ¬ IsTransfer R` — **iniciação ≠ transferência**: uma relação com alternativas genuínas não é o gráfico de função nenhuma | PROVEN | **`{}`** (lógica pura — sem axioma, sem vocabulário) |
| C64 | §1 | `Initiation.originates_not_transfer` | BLOCKED | (retired: manufactured `Sum.inl` origin destroyed under hostile semantics) |
| C65 | §1/T5 | `Initiation.person_iff_originates` | BLOCKED | (retired: manufactured personhood by initiation destroyed under hostile semantics) |
| C66 | §1 fnd | `Initiation.Cogito_Init` | BLOCKED | (retired: manufactured witness destroyed under hostile semantics) |
| C67 | §1 fnd | `Initiation.noInitiation_selfRefutes` | BLOCKED | (retired: manufactured witness destroyed under hostile semantics) |
| C80 | §1 | `Initiation.posited_not_branch` | BLOCKED | (retired: manufactured posited content branch evaluation destroyed) |
| C81 | §1 | `Initiation.origin_branches` | BLOCKED | (retired: manufactured origin branch evaluation destroyed) |
| C82 | §1/§12 | `Initiation.origin_is_initiating_person` | BLOCKED | (retired: manufactured initiating person destroyed) |

## Faith / DEFERRED

| ID | Poem | Status | Note |
|----|------|--------|------|
| FAITH-1 | P2 necessity | → PROVEN | dissolved in C1: `necDistinction` is now a theorem (C38); world content = C37 |
| FAITH-2 | P8 eternal love | → PROVEN↑ | rests on `AxTwoSubjects` (META bridge restored after Unit countermodel) + `AxPersonStability` (theorem); T14 is proven under `{AxTwoSubjects}` (C42–C45) |
| F7 | §15 the bipolar half of freedom | → PROVEN↑ | dissolved in F1b: free will under AxActPolarity is derived via A13 → A14 → FreeWill (Choice.freeWill_exists_of_act_polarity / Choice.act_polarity_implies_intentional_choice); AxActPolarity remains an optional stronger SEMANTIC principle |
| F8 | Trinity | DEFERRED | not attempted (§28/§29) |
| F9 | Incarnation / creation | DEFERRED | poem P10, faith datum |

## Hardening batch B1/A1/B2/C1 (2026-09-15)

- **B1** (act bundle): `A` redefined as a bundled predicate; the six
  `act_implies_*` meaning postulates became `rfl`-theorems. `cogito` is the
  single performative datum. Saves 6 axiom declarations; C21–C25, C39
  footprints shrink to `{cogito}` + kind-predicates.
- **A1** (fallibility): `Fallible := IsFalse` (the former consistency model,
  lifted to bivalence); `fallible_false` is a theorem. `Fallible` and
  `fallible_false` dissolved; C28–C30 lose them from their footprints.
- **B2** (`Realizes`): `Realizes := GroundProp` (rename); `AxGroundBearing`
  dissolved (was META); T8 (C32) now loads on `AxPersonalGround` only.
- **C1** (necessity): `Necessity p := ∀ w, p` (identity-model alias, D12) is a
  definition; `necK/necT/nec4` are theorems. Added `NecessityPH` — the
  semantics-grounded world-level operator with `necKPH/necTPH/nec4PH` theorems
  (no axioms). `necDistinction` is a theorem (was axiom, C38/FAITH-1). Saves 4
  axiom declarations.

## Batch C3-I/C4 — Interpersonal bridge split + structural love (2026-09-15)

- **C3-I** (split of `AxValueInterpersonal`): the monolithic META bridge
  `AxValueInterpersonal` is split into two narrower bridges:
  * `AxTwoSubjects` (META, plurality only: right-and-wrong demands two persons);
  * `AxPersonsAffect` (SEM meaning-postulate: distinct persons bear on each other).
  Recovery theorem `valueInterpersonal_of_split` proves the old statement. No
  strength lost; axiom content redistributed (lines 70–91 of `Value.lean`).
  Exclusion spikes (x2_spikeA, x2_spikeB) both stuck as designed: named missing
  lemma `ALONE_EXCLUDED : ¬ (∃ s, Person s ∧ Alone s)` — the transcript of the
  spike kernel context is in `/tmp/opencode/x2_spike{A,B}.lean`.
  (Superseded 2026-09-17 by the plurality-discharge: `ALONE_EXCLUDED` is now
  the theorem `Value.aloneExcluded` C74, and `AxTwoSubjects` was retired.)
- **C3-II** (single exclusion attempt, one-shot): tried to derive a second
  subject directly from the denial of `Alone` via `cogito + T6 + P6 + defs`.
  Stuck (x2_spikeC): the one-person scenario is consistent with every theorem;
  the interpersonal bridge is genuinely separate. Record in DESIGN.md D14b.
  (Superseded 2026-09-17: the one-person scenario is NO LONGER consistent —
  `neverAlone` (C74) refutes `Alone s` outright.)
- **C4** (`Loves := Affects`, structural love): `Loves` is redefined as a
  *definition* (`Affects`); `AxEternalLove` (FAITH/META, D14b) is dissolved.
  A new bridge `AxPersonStability : ∀ s, Person s → NecessarySubject s`
  (SEM, poem's "de alguma forma") carries the *eternal* half of T14, attached to
  the relata. T14 is restated as four theorems (`T14_eternalRelation` with
  `NecessarySubject` relata; `T14_world` with `NecessityPH`; `T14_square` the
  alias-□ image; `T14_content`). FAITH-2 dissolves. Loves is no longer an axiom.
  Exclusion spike x2_spikeD stuck: `Person` structure (T5) gives no fact about
  world-persistence of the entity-correlate. (Superseded 2026-09-17 by
  esse-est-agere: `AxPersonStability` is now a theorem, `ExistsAt` a def.)

## Batch E0/C2/A3 + transcendental spikes (2026-09-15) — honest info-line cut

Mechanism is **axiom→theorem/definition only** (no audit suppression, no lake
silencing — the 38 `#print axioms` statements stay). Measured on `lake build`
output: **220 → 180 printed axiom-entries (−18 %)**; 222 → 198 output lines;
6 theorems now print `does not depend on any axioms`.

- **E0** (`T := id`, `Core.lean`): the D2 consistency model made definitional.
  `axiom T` + `axiom tschema` are dissolved; `theorem tschema := Iff.rfl`.
  All §4–§6 self-refutation proofs re-verified (unchanged bodies — they were
  already logic, now openly so): `rightWrongDistinction` ("há certo e há
  errado") is axiom-free. `{T, tschema}` vanishes from ~16 non-empty blocks.
  Reversible by definition-restore; D4's gap concern re-recorded in D-E0.
- **C2** (amended 2026-09-17): `Entity` and `Subject` are genuinely distinct
  types (`Truthmaker.lean`, `Plurality.lean`). `Entity` is the general
  ontological sort (inductive: `ofSubject` and `ofAtom`), `EntityOf : Subject → Entity`
  embeds subjects into entities, and `ExistsAt` is defined independently of agency.
  `Ground` is the sole semantics axiom, over `Entity`. Contingency is genuine.
- **A3** (`Affects := Helps ∨ Harms`, `Value.lean`): faithful to P6; bundle
  mirrors B1. `help_affects`/`harm_affects` become projection theorems.
  `AxPersonsAffect` restated over the bundle; its footprint now shows
  `Helps`/`Harms` (unfold) instead of `Affects`.
- **B-spikes 2.0** (transcendental retries, `/tmp/opencode/x3_spikeB{1,2,3}.lean`,
  stuck by design): `ALONE_EXCLUDED` re-attacked post-E0/C2/A3 (strawmen: T6
  fallibility is one-subject; `rightWrongDistinction` is axiom-free but
  quantification-agnostic); `PERSONS_BEAR` (no intro rule for `Helps`/`Harms`
  from act-structure); `PERSON_PERSISTS` (no rule from `Person` to `ExistsAt`).
  Named missing lemmas `ALONE_EXCLUDED`, `PERSONS_BEAR`, `PERSON_PERSISTS`;
  the three bridges stay priced (META/SEM/SEM) — no fabricated promotion.
  (All three superseded 2026-09-17: `ALONE_EXCLUDED` → C74 theorem;
  `PERSONS_BEAR` → `AxPersonsAffect` theorem of A3; `PERSON_PERSISTS` →
  esse-est-agere, `AxPersonStability` theorem.)

## Batch actualWorld-def + T12_directedPair (2026-09-15) — free fortifications

Two honest cuts with no price, per the reducibility audit (§3 of the plan):
the previous agent's vetoed `someTrue` classical proof is **untouched** — it
remains the explicit reductio that exhibits the transcendental content, and
its footprint stays `CL`.

- **actualWorld → def** (`Modal.lean`): `def actualWorld : World :=
  fun _ => Logos.Semantics.TV.t` (precedent: `Necessity.someWorld`). T7
  invokes `Ground e τ` at *some* fixed world; nothing depends on which, so the
  "present world" is a modeled choice, not a datum. Axiom count 23 → 22;
  C18–C20 lose `actualWorld` (now `{AxGlobalGround, Subject, ExistsAt, Ground}` —
  at batch time; esse-est-agere drops `Subject` (def) and `ExistsAt` (def)).
  No proof-body changes.
- **T12_directedPair** (`Plurality.lean`, **C47**): the T12 pair oriented so
  affectivity flows named-forward — `AxPersonsAffect` decides direction by
  cases. `T14_eternalRelation` (`Love.lean`) is rebuilt on this node instead
  of the inline T12+cases, so direction and stability hold of the *same* pair.
  Same footprint as before (`{AxTwoSubjects, AxPersonsAffect, AxPersonStability}`
  + vocabulary + `{ExistsAt, Helps, Harms}`); one more named step in the chain.
  A lone stability-only node was rejected: direction and stability would then
  be unconnected (see DESIGN.md D-C47).
- Measured: `#print axioms` statements total 38 (statement-level audit set;
  the earlier "39" figure counted two in-doc mentions in `Core.lean`);
  theorems printing `does not depend on any axioms` now 8 (adds
  `necDistinction_content`, `necKPH`, `nec4PH`); `sorryAx: 0`; `lake build`
  green, zero warnings.

## Batch Chooses-def + A3-refactor (2026-09-15) — Value & Choice hardening

Two more honest cuts from the reducibility audit; the `someTrue` classical
proof remains **untouched**.

- **Chooses → def** (`Choice.lean`): `axiom Chooses` was dead code — used only
  by `def CanChoose` → `def FreeWill`; not a single theorem carries it in its
  footprint (F1/DEFERRED interface built on the placeholder `def Chooses :=
  False`). Axiom count 22 → 21; `T11_choiceField` footprint unchanged
  (`{cogito}` + kind-predicates); no proof bodies touched.
- **A3-refactor / Affects-primitive** (`Value.lean`): `Affects` promoted from
  bundle-definition to the *single primitive* value relation
  (`axiom Affects : Subject → Subject → Prop`); `Helps`/`Harms` demoted to
  projections `def Helps := Affects`, `def Harms := Affects`;
  `help_affects`/`harm_affects` become `rfl`-theorems. Axiom count 21 → 20.
  Footprints across the love chain drop `{Helps, Harms}` and read
  `{Affects}` instead — measured: `alone_no_other_help_harm`
  `{Subject, Affects}`; `valueInterpersonal_of_split` / `T12_directedPair`
  / `T14_*` all `{…, Affects, AxPersonsAffect, AxTwoSubjects, …}`.
  Honesty note: the HELP/HARM distinction is no longer formal (both unfold to
  `Affects`); it survives only on the prose/conceptual side (P6's "não ajuda
  nem prejudica ninguém" still holds, both halves literally).
- Measured: axiom inventory **20 declarations + CL** (now **18** after
  cogito-rethinking batch); `#print axioms` statements **39** (was 38, adds
  `cogito_from_T12`); `sorryAx: 0`; `lake build` green, zero warnings. The
  `PERSONS_BEAR` spike conclusion is unchanged: `Affects` (and hence its
  projections `Helps`/`Harms`) still has no *introduction rule* forcing it
  between persons — `AxPersonsAffect` stays a priced SEM bridge.

## Batch cogito-rethinking (2026-09-15) — Exists/Content defs + cogito as theorem

The user's observation drives this batch: **non-cogito refutes itself**.
Structurally this mirrors N_T ("there is no wrong") — the absolute negation
contradicts itself. RETHINKING-COGITO.md records the parallel in full.

- **Exists → def, Content → def** (`Agency.lean`): `def Exists (_s) := True`,
  `def Content (_p) := True` — analytical: every subject we meet exists; every
  proposition is a valid content. These two opaque axioms were meaning-intended
  as definitional; now made so. **Axiom count 20 → 18**.
- **cogito → derivable theorem** (`Plurality.lean`, C48): `cogito_from_T12` —
  from `T12_twoPersons` take a Person (`Agent ∧ Rational ∧ Intentional`),
  `Intentional` supplies the meant content, and the defs fill Exists/Content.
  Footprint `{AxTwoSubjects}` + kind-predicates — **no cogito, no Exists, no
  Content**. T2 became axiom-free (`{}`, witnessed by `True`). The denial of
  cogito is now refuted by a *theorem*, exactly as N_T is refuted by
  `notNothingTrue`.
- **`axiom cogito` retained in `Agency.lean`** for import-order only (Agency
  cannot import Plurality — cycle). Marked formally redundant.
- Measured: `#print axioms` statements total **39** (adds `cogito_from_T12`;
  the audit set never shrinks); `Exists`/`Content` leave *every* footprint;
  theorems printing `does not depend on any axioms` now **10** (adds
  `T2_contentExists`); `sorryAx: 0`; `lake build`
  green, zero warnings.
- Honest trade-off: footprints that read `{cogito}` still read `{cogito}`
  (T1/T4/T5/T6/T11/correctness_distinct — the axiom is still declared). But
  the *derivability* is now proven, so cogito's status is "axiom, proved
  redundant" rather than "irreducible datum" — a strict strengthening.

Summary counts (lift-necessário, measured 2026-09-18; supersedes the A2-swap-theorem figures below):

- **PROVEN** (no axioms beyond `CL` where marked) — **45 axiom-free** (`{}`):
  C1, C2, C4–C9, C11, C21–C24, C26–C29, C31, C35, C36, C38, C39,
  C48–C54, C56–C58, C61–C68 (C62: pure bridges `{}`; full conditional `CL`),
  C73–C79
  (definitional plurality, plenum seed, canonical rigid love, necessary person, contingent ground, substantive ultimate ground), F1a
  (choice-**field** existence resolves to a kernel step; renamed 2026-09-18, the genuine-choice form is BLOCKED on `rejectedHornCoMeant`).
  `CL`-only: C3, C10, C12–C14, C25, C30, C37, C55, C59, C93.
  Vocab-only (`{Ground}` — the statement's own vocabulary): C15, C16, C17,
  C18, C20, C34, C60 (denial refutes itself by definition — RAA;
  esse-est-agere drops `ExistsAt`, now a def; A2-swap-theorem drops
  `AxGlobalGround`, now a theorem).
  New (lift-necessário, 2026-09-18): **C91**, **C92** — vocab-only
  (`{Subject}` and `{Means, Subject}` respectively); hostile separations `{}`.
  C62 (`rightWrong_implies_meaning`) is the pure bridge: with the §8
  act-relative `Correct`/`Incorrect`, right/wrong unfold to a `Means`-act;
  the bare-distinction form `rightWrongDistinction_implies_meaning` is `CL`.
- **PROVEN↑** (under flagged SEM/META only — no foundation axiom remains):
  C32, C33, C40–C47, F4, F5.
  (`Cogito` is proven — the M0 forced-foundation axiom is retired, its
  degenerate `fun h => h Cogito` with it. `AxPersonalGround` (META, T8)
  is the remaining Level-2 price alongside `GroundPrincipleProp` (SEM);
  `AxTwoSubjects` was **retired** by the plurality-discharge (2026-09-17 —
  canonical pair C73, `ALONE_EXCLUDED` C74);
  `actualWorld` is a def;
  `Exists`/`Content`/`Agent`/`Rational` are analytical defs; `Affects` is the A3
  definition `s ≠ t`; `AxPersonsAffect`, `AxPersonStability` and now
  `AxGlobalGround` (atom-restricted) are theorems.)
- **BLOCKED**: C19 (T7 excluded-middle instance — missing lemma `∃ e,
  Ground e (or θ (not θ))`; transcript in `formal/Spikes/Spike_A6_probe.lean`);
  C69–C72 (retired origin-freedom witnesses) and F1b (genuine choice —
  missing `rejectedHornCoMeant : ∃s p, A s p ∧ A s (¬p)`, formalizado como nó
  def BLOCKED; **veredito 2026-09-18 opção 3** — irreducível sob os primitivos
  presentes: veridicalidade mata co-significação, asserção é de um-corno-só,
  `CountermodelVeridicalMeaning` satisfaz o fragmento com escolha vazia;
  freedom itself is definitional, `Chooses → FreeWill` `{Means, Subject}` (vocab-only));
  F7 (world-level alternativity — **vocabulary gap**, not a proof gap:
  no world-varying choice predicate exists; missing
  `ChoiceAt : World → Subject → Prop → Prop`, a new SEM/META bridge,
  deliberately deferred).
- FAITH layer: **empty** (FAITH-1 → C38, FAITH-2 → C4); no claims live at the faith boundary.
- Axioms dissolved (all batches): `T`, `tschema`, `Entity`,
  `EntityOf`, `help_affects`, `harm_affects`; `Affects` (axiom → def, M1);
  `actualWorld` (axiom → def); `Chooses` (axiom → def);
  `Exists`/`Content`/`Agent`/`Rational` (axioms → defs);
  `AxOr`/`AxAnd`/`AxNot` (axioms → theorems via A2);
  `AxPersonsAffect` (axiom → theorem, M1 via A3);
  `Subject`/`State`/`Initiates` (axioms → defs, definitional subject);
  `Cogito` (axiom → theorem, definitional subject);
  `ExistsAt` (axiom → def, esse est agere);
  `AxPersonStability` (axiom → theorem, esse est agere);
  `AxGlobalGround` (axiom → theorem, atom-restricted, A2-swap-theorem);
  `AxTwoSubjects` (axiom → **retired**, plurality-discharge 2026-09-17 — its
  content moved into the definition of a subject: the canonical pair C73 is
  a theorem `{}` and `ALONE_EXCLUDED` is C74; the M2 lone-subject model is
  superseded).
  A1 removed `cogito`; M0 restored it as the FORCED foundation (+1);
  the definitional-subject batch proves it (−1).
  Net inventory: **4 declarations** + `CL`:
  `Ground`,
  `GroundProp`, `GroundPrincipleProp`, `AxPersonalGround`.
- `sorryAx` count across all modules: **0**.
- Verification: `lake build` green (36 jobs, seconds, Lean core only); zero
  errors, zero warnings.

## Batch Tier1 + choice-realism (2026-09-16) — act = meaning, choice as theorem

Driven by the user: "There is no right and wrong without choice! OBVIOUSLY"
and "fix the argument, some gaps are obviously not so". Fine-text in
`Choice.lean` + `Order.lean`; full narrative in `IM_STUPID.md` (kept in sync).

- **Tier1 (act = meaning)** (`Agency.lean`, `Person.lean`): `axiom Agent`,
  `axiom Rational` were the *same analytical class* as `Exists`/`Content`
  (intended-definitional); both now `def _ := True`. `A` is redefined as
  `def A s p := Means s p` — the bundled act of B1 IS the meaning-act.
  `act_implies_*` remain `rfl`-level. **Axiom count 18 → 16.**
  Kind-predicates `{Agent, Rational}` vanish from every footprint.
  `Subject` stays an axiom as a *pure-sort postulate* (at Tier1 time): an empty `inductive`
  `Subject` refutes `∃ s` (breaks `Cogito`/T12 → `False`); `Subject :=
  Bool`/`fin 2` would smuggle "exactly two"; `ℕ` asserts infinity; `Unit`
  kills `s₁ ≠ s₂`. Recorded in the file and in DESIGN.md D-Tier1.
  (Superseded 2026-09-17 by the definitional-subject batch:
  `Subject := Unit ⊕ Prop` — the neutral witness `Sum.inl ()` smuggles
  nothing beyond the datum itself.)
- **(Superseded 2026-09-18 by the freedom/choice fix — see the batch at the top:
  the old body `A s p ∧ Incompatible p q` was a determined occurrence, not a
  choice; it is now `ChoiceField`, and genuine `Chooses` additionally requires
  `A s q`. Names below are the at-batch names.)**
  **Choice-realism** (`Choice.lean`, `Order.lean`): the old `def Chooses :=
  False` placeholder made choice unrepresentable — the mislabeled "subject ⇒
  choice" gap. New real definition `Chooses s p q := A s p ∧ Incompatible
  p q`, plus theorems: `incompatible_self_negation` (pure logic `{}` —
  the field around any meaning-act is non-empty), `meaning_needs_subject`,
  `person_chooses` (**subject ⇒ choice**, was OPEN; `{Initiates, State, Subject}`, no
  cogito — at batch time; now `{}`), `choiceExists`, `noChoice_selfRefutes` (denying choice is itself a
  choice), `JUDGE_COMMITTED` (**right/wrong ⇒ choice**), `judge_commits`
  (the §8 judge IS a chooser, `CL + {Cogito, Initiates, State, Subject}` post-M0 — now `CL`),
  `canChoose_unfold` (the aliased-◇ choice collapses to real choice),
  `noSubject_selfRefutes` (a subject exists is un-denyable: the denial is itself
  an act; `{Cogito, Initiates, State, Subject}` post-M0 — now `{}` — formal record of §26).
  `Order.lean` now imports `Logos.Choice` (no cycle).
- **F1 split**: F1a (choice-existence, transcendental) is PROVEN↑ (at batch
  time; now PROVEN); F1b
  (bipolar `◇Choose ∧ ◇Choose¬`, world-level on `NecessityPH`) stays
  DEFERRED — a subject may mean `p` without being able to mean `¬p`.
- Measured (at batch time): `#print axioms` statements **47** (was 39; +7 Choice, +1 Order);
  axiom-free theorems **11** (adds `incompatible_self_negation`); `sorryAx:
  0`; `lake build` green, zero warnings. (Now: 40 axiom-free; see summary.)

## Batch A1-cogito-removal (2026-09-16, superseded by M0) — axiom deleted, content re-homed

A1 was genuine but mechanical: it relocated the datum, not restructured it.
**M0 (2026-09-16, `FORCED_SUBJECT.md`) recognizes the A1 move as the bug the
forced-foundation batch fixes**: deleting cogito and anchoring on T12/AxTwoSubjects
made choosing-subject existence a *consequence* of plurality — the very datum
it must precede. M0 restores cogito as `Agency.Cogito` (FORCED foundation),
T1/T4/T5/cogito_from_T12 re-anchor there, and the A1-derived footprints
`{AxTwoSubjects, Initiates, State, Subject}` become `{Cogito, Initiates, State, Subject}` (measured).
The A1 mechanics (re-homing T1/T4/T5, Plurality audit lines, Choice/Order
switches) are retained as implementation but their anchor flips.

- **A1 (historical): `axiom cogito` was DELETED** (`Agency.lean`). The act-datum became
  `Plurality.cogito_from_T12` (C48), anchored on `AxTwoSubjects`. **M0
  recognized this as the bug and re-posted the datum** (see M0 batch below).
- **T1/T4/T5 re-homed** to `Plurality` as corollaries of the *foundation*
  (M0) — not as T12 projections: `Plurality.T1_subjectExists`,
  `Plurality.T4_agentExists`, `Plurality.T5_personExists`. `Person.lean`
  drops the deleted-axiom use; Choice/Order switch to the Plurality nodes.
- **A1 footprint flip (historical, superseded):** `{cogito,...}` → `{AxTwoSubjects,...}`
  was the A1-era state; M0 flips it again to `{Cogito,...}`.
- A4 circularity guard is now **live unconditionally** (M0): `choiceExists`,
  `cogito_from_T12`, `judge_commits`, `noChoice_selfRefutes`,
  `noSubject_selfRefutes`, `person_chooses` all depend on `Cogito` — not on
  `AxTwoSubjects` — so they are now permitted in any spike whose goal is
  `AxTwoSubjects` (no plurality assumption enters their footprints).
  (2026-09-17: all `{}` — the guard holds trivially.)

## Batch A2-structural-TrueAt (2026-09-16) — connectives as THEOREMS via structural `TrueAt`

The user's ruling: record A2 in its strongest form — *theorem, not thesis*.
Executed in `Truthmaker.lean`:

- **`def TrueAt` is now structural** (atom-grounding + Tarskian recursion over
  `Form`, mirroring `Semantics.Satisfies`): an atom is true in `w` iff some
  entity grounding it exists there; `not`/`and`/`or`/`imp` are
  Tarskian-compositional **by definition**.
- **`axiom AxOr`/`AxAnd`/`AxNot` DELETED** (−3 declarations). Their content is
  now **proved**: `sat_ground_or/and/not/imp : … := Iff.rfl` (C15–C17), and
  `lawExcludedMiddle`/`nonContradiction` are re-proved by definitional
  reduction (classical only for the `or`).
- **`groundPrinciple` → `groundPrinciple_atom`** (C15): the old formula-level
  version is deliberately dropped — for compounds it is underivable (not
  false): `Ground e (or …)` is a free relation with no introduction rule, so
  composite truth carries no existential grounding claim. Prose §24a/§27:
  "toda verdade **ATÓMICA** tem fundamento; a verdade composta é
  composicional (Tarskiana)". The atom-clause is not a new belief: it is the
  face-value model already in DESIGN D4-D5 and `Semantics.Satisfies`.
  Honesty limits: no `TrueAt = Satisfies` ∈-theorem (Ground/ExistsAt remain
  free VOCAB); `Ground e (or …)` neither asserted nor denied. (Superseded
  2026-09-17 by esse-est-agere for the `ExistsAt` half: existence is now
  agency itself; `Ground` alone stays free VOCAB.)
- Measured footprints (`#print axioms`, scratch `/tmp/opencode/aud.lean`;
  at batch time — `Subject` since demoted to a definition):
  `groundPrinciple_atom` = `{Subject, ExistsAt, Ground}`;
  `noGround_selfRefutes` = `{Subject, ExistsAt, Ground}` (C60 — the denial
  of atom-grounding refutes itself by definition: `TrueAt w (atom n)` unfolds
  to the existential clause, so the denial is `∃e… ∧ ¬∃e…`; RAA, no
  substantive axiom — this is also the justification for C15 being PROVEN,
  not a price);
  `lawExcludedMiddle` = `CL + {Subject, ExistsAt, Ground}`;
  `nonContradiction` = `{Subject, ExistsAt, Ground}` (**no propext** — the
  re-proof avoids `rw` on `Iff`); `T7_necessaryReality`/`T7_excludedMiddleInstance`/
  `noNecessaryTruthIfAllContingent` unchanged from before.
  (2026-09-17: `Subject` demoted — drop it from all four; esse-est-agere
  also drops `ExistsAt` — now `{Ground}`, `CL + {Ground}`, `{Ground}`.)
- Measured totals: axiom declarations **15 → 12**; `#print axioms` statements
  stay **47** (Truthmaker audit still 3); `sorryAx: 0`; `lake build` green,
  zero warnings.

## Batch M0+M1 (2026-09-16) — SUBJECT IS FORCED + definitional affectivity (`FORCED_SUBJECT.md`)

(Historical: M0's FORCED axiom is retired by the definitional-subject batch,
2026-09-17 — `Cogito` is now a theorem, `{}`. What follows is the record
as it stood.)

- **M0 — M0 forced foundation `Cogito` (`Agency.lean`).** The bug (measured):
  choosing-subject existence `∃ s p, A s p` was *optional-conditional* — the
  entire transcendental chain (T1/T4/T5, T6*, T11, choice/reason side, cogito)
  paid `{AxTwoSubjects}` merely to obtain a single witness. **Fix:**
  `axiom Cogito : ∃ s : Subject, ∃ p : Prop, A s p` (FORCED/TRANS) +
  `noCogito_selfRefutes` (C58). Walls that forbid a derivation recorded in
  `FORCED_SUBJECT.md` §1 (empty model satisfies the vocabulary; every non-empty
  carrier smuggles a count). Downstream witnesses re-anchor on `Cogito` —
  measured (`#print axioms`, scratch `/tmp/opencode/audit_forced.lean`):
  C21/C23/C24/C39/C48/C52/C53/C54/C57, C28/C29/`fallible_false` and
  C30/C55 at `CL +` — all `{Cogito, Initiates, State, Subject}`.
- **M1 — A3 definitional affectivity (`Value.lean`).** `def Affects s t :=
  s ≠ t` (bearing = distinctness; the lone subject affects nothing, P6);
  `def Helps`/`Harms := Affects`; **`AxPersonsAffect` → THEOREM**
  (`Or.inl hne`). Measured: `alone_no_other_help_harm` → `{Subject}` (C56);
  `T12_directedPair`/`valueInterpersonal_of_split` → `{AxTwoSubjects, Initiates, State,
  Subject}` (C46/C47); `T14_*` (C42–C45) → `{AxTwoSubjects, AxPersonStability,
  ExistsAt, Initiates, State, Subject}` (no `Affects`, no `AxPersonsAffect`).
- **Axiom inventory 12 → 11:** +`Cogito` (FORCED) −`Affects` (→ def)
  −`AxPersonsAffect` (→ theorem). `#print axioms` statements 47 → 50
  (adds M0 audit lines). `sorryAx: 0`; `lake build` green, zero warnings.
- **Spike verdicts (all BLOCKED, transcripts in `formal/Spikes/`):**
  * M2 `Spike_A4_2.lean`: `ALONE_EXCLUDED` — the lone-subject consistency
    witness is kernel-checked in-file (single inhabitant refutes the target
    over the whole allowed surface); `AxTwoSubjects` stands as a **price
    justified by a model**. (Superseded 2026-09-17 by the plurality-discharge:
    the witness is built on the OLD axiomatic `Subject`; the definitional
    `Subject := Unit ⊕ Prop` has ≥2 inhabitants, both persons — C73 — so the
    lone-subject model is void and `AxTwoSubjects` is retired; `ALONE_EXCLUDED`
    is now the theorem C74.)
  * M3 `Spike_PersonStability.lean`: `PERSON_PERSISTS` — a necessary relata
    `e₀` exists (T8 content) but `Realizes e₀ f` does not identify it with the
    act's subject; `NecessarySubject s` needs `ExistsAt w s` and no rule links
    `Means` to `ExistsAt`; `AxPersonStability` stays priced (SEM). (Superseded
    2026-09-17 by esse-est-agere: the rule is supplied by definition —
    `AxPersonStability` is now a theorem, `ExistsAt` a def.)
  * M4 `Spike_A6_probe.lean`: weaker `AxGlobalMirror` derives T7-**atom**
    (kernel-checked, no `AxGlobalGround`) but cannot cover the compound
    excluded-middle instance (A2 structural TrueAt has no existential ground
    for compounds) — `AxGlobalGround` **stays priced (smaller)**; recording
    only, not adopted. (Superseded 2026-09-17 by batch A2-swap-theorem:
    esse-est-agere's world-vacuous `ExistsAt` makes the atom swap itself a
    theorem — no axiom at all, weaker or otherwise; the compound instance
    C19 is recorded BLOCKED with its exact missing lemma.)
- **A4 guard relaxes justifiably:** the six enumerated theorems now bottom out
  at `Cogito` (no plurality), so they are plurality-free surface for future
  plurality spikes; the ban on plurality-from-plurality is preserved (nothing
  derives `AxTwoSubjects` from itself).
- **M5 — "Strong Truth Exists" resident; choosing subject stays FORCED (spike
  verdict BLOCKED, presumably permanent).** `strongTruthExists` was promoted
  into the barrel as `Semantics.strongTruthExists` (2026-09-18), on the
  axiom-free `{Core, Semantics}` surface — **C59, footprint `{CL}`, no Cogito**,
  the "há certo E há errado" datum of en.md §27/poem.txt, from C37. Axiom-free
  theorems: 13 → 14. `noStrongTruth_selfRefutes` (retorsão performativa)
  added as C93. `Spike_M5_StrongTruth.lean` retained as historical record.
  `Spike_M5_ChoosingSubject.lean` is the honest probe at
  `∃ s p q, Chooses s p q` WITHOUT Cogito: stopped at the **atom-wall**
  (`groundPrinciple_atom` is atom-only; the {CL}-forced strong truth is the
  necessitated disjunction `Form.or (atom 0) (Form.not (atom 0))`, never a true
  atom; exact missing lemma `∀ w, TrueAt w (Form.atom 0)` is not provable on
  {CL}worlds). `Cogito` **stays FORCED, ladder 11**; NOT demoted. M5 verdict:
  the transcendental datum is axiom-free, the choosing subject is not.
  (M5 verdict superseded 2026-09-17: the choosing subject IS proven —
  `Agency.Cogito`, `{}`, by definitional exhibition of the underlier.)

## Batch freedom-split (2026-09-17) — the "could not have chosen otherwise" paradox dissolved

**(Superseded 2026-09-18 by the freedom/choice fix — see the batch at the top:
the witnesses `freeWillOrigin`, `noFreeWillPosited`, `originFreedomSelfRefutes`,
`judgeIsFree` below were manufactured `Sum.inl`/`Sum.inr` constructions
destroyed under hostile semantics; C69–C72 are now BLOCKED/retired. The
genuine replacement is `Chooses`/`FreeWill`/`rejectedHornCoMeant`.)**

Driven by the user: "if you could not have chosen otherwise, then choice does
not exist in the freedom sense. Which means right and wrong would not exist.
This is paradoxical. We need to make it clear that it can't be the case."

- **F1b splits in two.** F1b-weak (the performer's both-ways capacity) is
  PROVEN; F1b-strong (world-level alternativity) is BLOCKED at the **vocabulary**
  level — not a proof gap like C19.
- **`freeWillOrigin : FreeWill (Sum.inl ()) p`** (`{}`): the act's own subject —
  the origin, the witness of `Agency.Cogito`/`Plurality.T5_personExists` that
  `JUDGE_COMMITTED` commits to right-and-wrong — can choose `p` AND can choose
  `¬p`. From `Initiates (inl _) _ w' p := w' = p`: the origin means every
  content, so both choices are real; `CanChoose` reached constructively
  (instantiation at `someWorld`), deliberately not via the classical
  `canChoose_unfold`. **C69**.
- **`noFreeWillPosited : ¬ FreeWill (Sum.inr q) p`** (`CL`): the self-posited
  contents provably CANNOT choose otherwise — `inr q` can only mean `q`
  (`Means (inr q) p` iff `q = p`), so both-ways capacity would force
  `q = p ∧ q = ¬p`, impossible. **No paradox**: these subjects are never the
  judge right/wrong commits (that witness is the free origin). **C70**.
- **`originFreedomSelfRefutes : (¬ FreeWill (Sum.inl ()) p) → False`** (`{}`):
  "I could not have chosen otherwise" — asserted by the origin of the present
  act — is itself a both-ways act and refutes itself. The determinist
  alternative cannot be asserted performatively. **C71** — this is the
  kernel-checked dissolving of the user's paradox.
- **`judgeIsFree : ∃ s, Person s ∧ ∃ p, FreeWill s p`** (`{}`): the chooser
  that right/wrong commits is free — choice *does* exist in the freedom sense
  for the subject the undeniable right/wrong demands. **C72**.
- Measured (`#print axioms`, in-file audit lines): `freeWillOrigin` `{}`,
  `noFreeWillPosited` `{propext, Classical.choice, Quot.sound}` = `CL`,
  `originFreedomSelfRefutes` `{}`, `judgeIsFree` `{}`. `lake build` green
  (36 jobs), zero warnings. Axiom inventory unchanged: **5 declarations**.
- **Recorded limitation (F1b-strong, BLOCKED):** a genuine *world-level*
  alternativity `◇PH Choose ∧ ◇PH Choose¬` requires a world-varying choice
  predicate; every predicate below `Semantics` is world-invariant, so
  `NecessityPH` over any of them collapses to identity (`∀ w, P ⟷ P`, world
  inhabited). The missing vocabulary —
  `ChoiceAt : World → Subject → Prop → Prop` — is deliberately NOT added
  (a new SEM/META bridge; not forced by the current chain). This is a
  *vocabulary* gap, unlike C19's formulable-but-unproven lemma.

## Batch plurality-discharge (2026-09-17) — `AxTwoSubjects` retired; the other is the addressee

Driven by the project's own discovery: under the definitional subject
(`Subject := Unit ⊕ Prop`, 2026-09-17) two distinct persons are **derivable** —
the former META price is redundant and is discharged as a demotion, the poem's
interpersonal step is re-found on the *addressee*, and the eternal relation
becomes world-rigid.

- **The fact:** `Person (Sum.inr True)` holds (`Means (Sum.inr True) True`),
  `Sum.inl () ≠ Sum.inr True` by constructors — so
  `∃ s₁ s₂, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂` unconditionally, `{}`. The
  second person is the *addressee*: a content positing itself — precisely the
  "alguém para quem significar" of the poem (P5/P7), not a second silent
  origin (one is all `Unit` can carry; any `Index ⊕ Prop` re-reading is
  behaviorally identical in `Means` — Track-B verdict: an equal-origin other is
  not a Λ-relatum, the other is inherently an addressee-content).
- **`Person.twoPersonsFromSubject`** (canonical pair, **C73**, `{}`): the
  origin `Sum.inl ()` and the addressee `Sum.inr True`.
- **`Value.neverAlone`/`Value.aloneExcluded`** (**C74**, `{}`): `∀ s, ¬ Alone s`
  (`otherSubject s ≠ s`) — so the named missing lemma `ALONE_EXCLUDED`,
  the *justification* of the bridge, is now a theorem and the M2 lone-subject
  consistency model (built on the pre-definition `Subject`) is void. The price
  was always, already, the definition.
- **Plenum seed (C75, `{}`)**: `everyContentIsAPerson : ∀ p, Person (Sum.inr p)` —
  every content raised to a subject is a person; `positedDistinct` for the
  extremes. Honest limit: distinctness is kernel-visible only for *incompatible*
  contents (proposition equality is `propext`-collapsed) — the plenum is
  unbounded in content, not in kernel-distinguishable members.
- **`Love.T14_canonicalRigid`** (**C76**, `{}`): the *same* pair (origin +
  addressee) loves in every world and both relata exist in every world —
  "Amar é … necessário (de alguma forma)" literal, strictly stronger than the
  old existential `{AxTwoSubjects}` form.
- **Cascade:** `valueInterpersonal_of_split` (C46) no longer needs the
  right-and-wrong premise; `T12_directedPair` (C47), `T13` (C41), `T14_*`
  (C42–C45), F4, F5 all → **PROVEN `{}`**.
- Measured (`#print axioms`, in-file audit lines): every touched node `{}`
  (no `CL` added). `lake build` green (36 jobs), zero warnings, `sorryAx: 0`.
- **Axiom inventory 5 → 4 declarations** (+`CL`): `Ground`, `GroundProp`,
  `GroundPrincipleProp`, `AxPersonalGround`;
  `AxTwoSubjects` → `RETIRED_AXIOMS` in `scripts/build_deduction.py` and the
  dissolved list; GAPMAP rows C40–C47/F4/F5 re-transcribed to the derived
  status (statuses are pure functions of the kernel; these cells now agree).
- **Philosophical record:** the "leap" was not lost and not faked — it was
  *located*: the interpersonal step lived in the 2026-09-17 decision that a
  subject is a self-positing content, and the addressee IS the other the poem
  needs. The prose registers (base.txt §28, T12–T14) adopt the addressee
  reading: "o outro é o conteúdo tornado sujeito".

## Conditional Theology Program (2026-09-19) — Downstream Consequences of A14 (`AxIntentionalChoice`)

Formal exploration in `formal/Logos/ConditionalTheology.lean` of the reach and exact independence boundaries
of $\Gamma + A14$:

- **Agency Closure:** $Act(s,p) \implies Chooses(s,p,q) \implies FreeWill(s) \land FreeSubject(s) \land IntentionalSubject(s)$ (`agency_closure_act_to_chooses`, `agency_closure_act_to_freewill`, `agency_closure_act_to_freeSubject`, `agency_closure_act_to_intentionalSubject`).
- **8 Agency Limits (Hostile Separation Models):** $FreeWill$ does NOT entail:
  1. Rationality (`freewill_not_entails_rationality`)
  2. Normativity (`freewill_not_entails_normativity`)
  3. Value (`freewill_not_entails_value`)
  4. Teleology (`freewill_not_entails_teleology`)
  5. Reflexive Subjectivity (`freewill_not_entails_reflexive_subjectivity`)
  6. Relationality (`freewill_not_entails_relationality`)
  7. Persistence (`freewill_not_entails_persistence`)
  8. Necessity (`freewill_not_entails_necessity`)
- **Grounding Architecture & Infinite Regress:** A14 cannot eliminate infinite ground chains (`a14_not_eliminates_infinite_ground_chain`); $FreeWill \nvdash UltimateGround$ (`free_agency_not_entails_ultimate_ground`).
- **Personal Ultimate Ground:** $A14 + UltimateGround \nvdash Personal(u)$ (`a14_plus_ultimate_ground_not_entails_personal_ultimate_ground`).
- **Plurality & Love:** $A14 \nvdash Plurality$ (`a14_not_entails_plurality`, separated by solitary free agent); $A14 + Plurality \nvdash Love$ (`free_agency_and_plurality_not_entails_love`, separated by loveless/malicious plurality).
- **Neutral Theological Targets:**
  - Trinity (`TrinitarianStructure`): independent; separated by Binitarian model (`preceding_theory_not_entails_trinity`).
  - Incarnation (`IncarnationalStructure`): independent; separated by Unincarnate model (`preceding_theory_not_entails_incarnation`).
  - Creation (`CreationStructure`): independent; separated by Acosmic divine model (`necessary_ground_not_entails_contingent_creation`).
- **Theological Dependency Ledger:** Machine-checked theorem `theological_dependency_ledger` proves the formal classification of all 10 transitions (PROVEN, DEFINITIONAL, SEMANTIC, METAPHYSICAL, COUNTERMODEL).
- **Single-Axiom Discipline:** A14 is the only new axiom. `lake build` green (40 jobs, 0 sorries).

## Level 4 — downstream metaphysical frontiers (`Logos.ConditionalTheology`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C108 | §28 | `ConditionalTheology.TrinitarianStructure` | PROVEN | `{}` |
| C109 | §28 | `ConditionalTheology.preceding_theory_not_entails_trinity` | DEMOTED | `{}` (demoted: 2-element Boolean cardinality artifact superseded by `monotheism_compatible_with_trinity`) |
| C110 | §28 | `ConditionalTheology.necessary_ground_not_entails_contingent_creation` | COUNTERMODEL | `{}` |
| C111 | §28 | `ConditionalTheology.IncarnationalStructure` | PROVEN | `{}` |
| C112 | §28 | `ConditionalTheology.preceding_theory_not_entails_incarnation` | COUNTERMODEL | `{}` |

## Level 5 — Practical Ought and Personhood Retorsion (`Logos.OughtRetorsion`, `Logos.PersonhoodOntologyAudit`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C113 | §21 | `OughtRetorsion.self_grounded_ought_collapses` | PROVEN | `{Ought, Subject, Wills}` |
| C114 | §21 | `OughtRetorsion.self_grounded_assertion_incoherent` | PROVEN | `{Ought, Subject, Wills}` |
| C115 | §21 | `OughtRetorsion.HostileImpersonalModel.impersonal_model_satisfies_ought_without_person` | COUNTERMODEL | `{}` |
| C116 | §21 | `OughtRetorsion.asserting_no_personal_source_instantiates_only_judging_subject` | PROVEN | `{Means, Subject}` |
| C117 | §21 | `OughtRetorsion.AxSecondPersonalAddress` | AXIOM | `AxSecondPersonalAddress` |
| C118 | §21 | `OughtRetorsion.second_personal_ought_derives_plurality` | PROVEN↑ | `{AxSecondPersonalAddress, Means, Ought, Subject}` |
| C119 | §21 | `OughtRetorsion.lone_subject_excludes_second_personal_ought` | PROVEN↑ | `{AxSecondPersonalAddress, Means, Ought, Subject}` |
| C120 | §12 | `Person.free_subject_is_person` | PROVEN | `{Means, Subject}` |
| C121 | §12 | `Person.person_iff_freeSubject` | PROVEN | `{Means, Subject}` |
| C122 | §12 | `PersonhoodOntologyAudit.opaque_person_failure_isolated_to_substantive_conjunct` | PROVEN | `{Means, Subject}` |
| C123 | §12 | `OughtRetorsion.faithful_contingent_person_fails_necessary_subject` | COUNTERMODEL | `{}` |

## Level 6 — Necessary Personal Ground and Monotheism (`Logos.NecessaryPersonalGround`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C124 | §23 | `NecessaryPersonalGround.claim_c_implies_claim_b` | PROVEN | `{GroundProp, Initiates, Means, State, Subject}` |
| C125 | §23 | `NecessaryPersonalGround.claim_d_implies_claim_b` | PROVEN | `{Means, Subject}` |
| C126 | §23 | `NecessaryPersonalGround.claim_e_implies_claim_b` | PROVEN | `{GroundProp, Means, Subject}` |
| C127 | §23 | `NecessaryPersonalGround.claim_e_implies_claim_d` | PROVEN↑ | `{divine_person_is_necessary, divine_nature_is_personal, personal_nature_iff_person, GroundsEntity, Subject, Will}` |
| C128 | §23 | `NecessaryPersonalGround.ofAtom_ne_ofSubject` | PROVEN | `{Subject}` |
| C129 | §23 | `NecessaryPersonalGround.ofAtom_not_necessary_personal_ground` | PROVEN | `{GroundsEntity, Subject, Will}` |
| C130 | §23 | `NecessaryPersonalGround.AxRealityGrounding` | AXIOM | `{AxRealityGrounding, Ground, GroundsEntity, Subject}` |
| C131 | §23 | `NecessaryPersonalGround.de_dicto_not_implies_de_re` | COUNTERMODEL | `{}` |
| C132 | §23 | `NecessaryPersonalGround.divine_subject_is_person` | PROVEN↑ | `{divine_nature_is_personal, personal_nature_iff_person, Means, Subject}` |
| C133 | §23 | `NecessaryPersonalGround.necessary_personal_ground_derived` | PROVEN↑ | `{AxGlobalGround, AxIntentionalChoice, AxRealityGrounding, explanatory_adequacy, Ground, GroundsEntity, Initiates, Means, State, Subject, Will, subjectWill, CL}` |
| C134 | §23 | `NecessaryPersonalGround.necessary_person_derived` | PROVEN↑ | `{divine_person_is_necessary, divine_nature_is_personal, personal_nature_iff_person, GroundsEntity, Subject, Will}` |
| C135 | §23 | `NecessaryPersonalGround.monotheism_derived` | PROVEN↑ | `{AxGlobalGround, AxIntentionalChoice, AxRealityGrounding, explanatory_adequacy, Ground, GroundsEntity, Initiates, Means, State, Subject, Will, subjectWill, universal_ground_unique, CL}` |
| C136 | §23 | `NecessaryPersonalGround.monotheism_compatible_with_trinity` | PROVEN | `{propext}` |

## Level 6 — Normative Order and Correctness (`Logos.NormativeOrder`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C137 | §8/§12 | `NormativeOrder.correct_implies_ought : Correct s p → Ought TruthNorm ⟨s, p⟩` — correctness generates agential deontic requirement under truth norm | PROVEN | `{Initiates, Means, State, Subject}` |
| C138 | §8/§12 | `NormativeOrder.incorrect_implies_oughtNot : Incorrect s p → OughtNot TruthNorm ⟨s, p⟩` — incorrectness generates agential deontic prohibition under truth norm | PROVEN | `{Initiates, Means, State, Subject}` |
| C139 | §8/§12 | `NormativeOrder.correctness_deontic_opposition : Act s p → DeonticOpposition (Correct s p) (Incorrect s p)` — deontic opposition between correctness and incorrectness derived via Ought/OughtNot | PROVEN | `{Initiates, Means, State, Subject, CL}` |
| C140 | §12/§15 | `NormativeOrder.claims_normative_correctness_derives_free_will : ClaimsNormativeCorrectness s p → Chooses s (Correct s p) (Incorrect s p) ∧ FreeWill s` — normative judicative stance derives choice and free will without AxJudicativeBipolarity | PROVEN | `{Initiates, Means, State, Subject, CL}` |
| C141 | §12/§15 | `RetorsiveNormativity.normative_retorsion_derives_free_will : (∃ s, ClaimsNormativeCorrectness s NoGN) → ∃ s, FreeWill s` — performative retorsion of skeptical denial without AxJudicativeBipolarity | PROVEN | `{Initiates, Means, State, Subject, CL}` |

## Level 7 — Ontological Grounding of Normative Polarity (`Logos.PersonalNormativeGround`, `Logos.Person`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C142 | §12 | `Person.person_iff_freeIndependentWill` | PROVEN | `{Means, Subject, Will, subjectWill, will_individuation}` |
| C143 | §8/§12 | `PersonalNormativeGround.AxPersonalNormativeGround` | AXIOM | `{AxPersonalNormativeGround, GroundProp, Initiates, Means, State, Subject, Will, subjectWill}` |
| C144 | §8/§12 | `PersonalNormativeGround.person_grounds_normative_polarity` | PROVEN↑ | `{AxPersonalNormativeGround, GroundProp, Initiates, Means, State, Subject, Will, subjectWill, will_individuation}` |
| C145 | §14/§15 | `PersonalNormativeGround.discovery_independent_of_grounding` | PROVEN | `{Means, Subject}` |
| C146 | §8/§12 | `PersonalNormativeGround.HostileModels.model_b_separation` | COUNTERMODEL | `{}` |



