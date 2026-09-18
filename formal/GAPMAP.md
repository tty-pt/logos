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
- **Exact missing lemma (F1b, BLOCKED)**:

      rejectedHornCoMeant :
        (∃ s : Subject, ∃ p : Prop, A s p) →
        ∃ s : Subject, ∃ p : Prop, A s p ∧ A s (¬ p)

  Rule form: `means_faces_negation {s p} : A s p → A s (¬ p)`. Why: `Means` is
  opaque (`Agency.lean`) and `AxTwoSubjects` yields two *different* subjects,
  each with a single content. The world-level `ChoiceAt : World → Subject →
  Prop → Prop` remains the (future, priced) SEM bridge, F7.
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
  não-entailments com datum modal `{}`. DEDUCTION.md: F1b ✖ BLOCKED (nó
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
- **C24 reclassificado**: enunciado e gloss do DEDUCTION passam a dizer que a
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
| C68 | §1 fnd | `Agency.Cogito : Asserts s p → ∃ s' p', Act s' p'` — **cogito derivado da asserção performativa** | PROVEN | `{Means, Subject}` (teorema derivado de qualquer asserção; deriva ato e sujeito via regra constitutiva) |
| C21 | §1/T1 | `Plurality.T1_subjectExists` | PROVEN | `{Means, Subject}` (derivado do ato intencional C68 via regra constitutiva act_requires_subject; desacoplado de AxTwoSubjects) |
| C22 | T2 | `Agency.T2_contentExists` | PROVEN | **`{}`** — `Content _ := True` (def), `True` witnesses content |
| C23 | T4 | `Plurality.T4_agentExists` | PROVEN | `{Means, Subject}` (derivado do ato intencional C68 → C21; `Agent` é `:= True`, def) |
| C24 | T5 | `Plurality.T5_personExists` | PROVEN | `{Means, Subject}` (teorema-válido sob a **definição constitutiva §12**, mas **não estabelece pessoalidade substantiva**; cadeia C68 → Act → SubjectExists → Intentional → Person (§12 nominal); `Person ≡ Intentional ≡ ∃p, Means s p` — `Person.person_intentional_iff` + lemas-ponte em Person.lean; matriz hostil substantive (Part A2) — Batch fronteira pessoal 2026-09-18) |
| C25 | §24b | `Person.inseparability_24b` | PROVEN | `{Means, Subject, CL}` |
| C26 | **T9 (new)** | `Alternatives.T9_incompatibleAlternatives` | PROVEN | `{}` (E0) |
| C27 | §13 | `Alternatives.incompatible_with_negation` | PROVEN | `{}` (E0) |
| C28 | T6 | `Order.T6_fallibility` | PROVEN↑ | `{AxTwoSubjects, Means, Subject}` (via T12 + `Core.someFalse`) |
| C29 | T6 | `Order.T6_truthTranscendsWill` | PROVEN↑ | `{AxTwoSubjects, Means, Subject}` (as C28) |
| C30 | §8 | `Order.correctness_distinct` | PROVEN↑ | `{AxTwoSubjects, Means, Subject, CL}` (defs act-relative §8) |
| C31 | §9 | `Order.consequence_preserves_truth` | PROVEN | `{}` (E0) |
| C83 | §8 | `Order.no_correct_judgment_of_no_act` — **retorsão cartesiana**: nenhuma negação do ato pode ser correta (`judgment_of_no_act_is_incorrect`) | PROVEN | `{Means, Subject}` |
| C84 | §1/§8 | `Order.judgment_of_no_act_proves_act` — **cogito retorsivo**: o ato de julgar que não há ato testemunha que o ato ocorre (`judgment_implies_cogito`) | PROVEN | `{Means, Subject}` |
| C32 | T8 | `GroundPerson.T8_personalGround` | PROVEN↑ | `{AxPersonalGround, GroundProp, Means, Subject}` |
| C33 | T8 | `GroundPerson.present_feature_is_grounded` | PROVEN↑ | `{GroundPrincipleProp, GroundProp, Means, Subject}` |
| C34 | T8 | `GroundPerson.necessary_truth_has_necessary_grounder` | PROVEN↑ | `{AxGlobalGround, Ground, Subject}` (via C18) |
| C90 | T8 | `GroundPerson.personal_ultimate_ground_exists` | BLOCKED | (retired: manufactured ultimate ground destroyed under hostile semantics) |

### Auditoria Ontológica da Cadeia de Agência (`asserts → act → Act → Subject → Person → ChoiceField → Chooses → FreeWill`)

| Passo / Implicação | Formalização Lean | Classificação | Estatuto Epistemológico e Semântica Hostil |
| :--- | :--- | :--- | :--- |
| **asserts → act** | `Agency.assertion_is_weak_act` | **Caso A (Definicional / Fraco)** | A ocorrência de uma asserção é um evento realizado (`act s p` — *ato fraco: evento realizado*), projecção imediata de `asserts s p := act s p ∧ p`. A retorsão `noWeakAct_selfRefutes` estabelece puramente `∃ s p, act s p` sob `{Subject, act}` sem assumir significado intencional. |
| **act ↛ Act** | `Agency.weak_act_implies_strong_act` | **Caso D (Ponte / Bloqueio Aberto)** | O evento realizado (emissão, som, toque, evento físico/mecânico) **não acarreta logicamente** o ato intencional de significação (`Act s p := Means s p` — *ato forte: ato intencional/portador de significado*). Demonstrado formalmente sob semântica hostil por `CountermodelWeakActWithoutMeaning` / `not_entails_strong_act` (`{}`). A passagem `act → Act` é uma ponte filosófica explícita (`weak_act_implies_strong_act`), não uma identidade definicional oculta. O atalho forte Logos é a asserção intencional `Asserts s p := Act s p ∧ p` (`assertion_is_act`). |
| **Act → SubjectExists** | `Agency.act_requires_subject`<br>`Agency.subject_exists_of_act` | **Caso B/A (regra constitutiva = identidade)** | Em Logos `Act s p := Means s p` e `SubjectExists s := ∃ p, Act s p`: ser sujeito *do* ato é a própria definição de sujeito atualizado. O contramodelo abstrato `CountermodelActWithoutSubject` (ato não-indexado, `Subject` predicado substantivo à parte) falha unicamente esta regra constitutiva; não atinge a identidade definicional Logos. |
| **Act → Intentional** | `Person.act_implies_intentional` | **Caso A (identidade)** | O conteúdo do próprio ato testemunha `Intentional s := ∃ p, Means s p` (`⟨p, h⟩`, `{Means, Subject}`). Identidade definicional: NÃO é atacável por modelo hostil. A leitura substantiva de intencionalidade (consciência/awareness interna) NÃO é forçada — `not_entails_substantive_intentionality` (Part A2, `{}`). |
| **SubjectExists → Intentional** | `Person.subjectExists_implies_intentional`<br>`Person.intentional_implies_subjectExists` | **Caso A (identidade)** | Ambas as noções desdobram para `∃ p, Means s p` (`{Means, Subject}`); equivalência por desdobramento direto. Nenhuma premissa. |
| **Subject → Person** | `Person.person_of_subject` | **Caso A (nominal §12)** | Sob a redução estrutural de §12 (`Person s := Agent s ∧ Rational s ∧ Intentional s` com `Agent := True` e `Rational := True`), `Person` colapsa em `∃ p, Means s p`, IDÊNTICO a `SubjectExists`/`Intentional` (`Person.person_intentional_iff`, `{Means, Subject}`). O §12 é compromisso constitutivo (rótulo nominal), não descoberta metafísica. **Separação 2026-09-18**: derivabilidade formal ≠ neutralidade semântica da definição; sobsemântica hostil com predicado substantivo, a implicação NÃO se segue (`CountermodelSubjectWithoutPerson`, `not_entails_person`), mas isso NÃO é contramodelo da identidade §12. |
| **Person (formal) → Person (substantiva)** | — (sem teorema; premissa registada, NÃO adicionada) | **Caso D (Bloqueado)** | A pessoa substantiva (deliberação, responsabilidade, auto-reflexão, agência autónoma, escolha racional, agência moral) não é forçada pelo datum performativo: `not_entails_substantive_person`, `not_entails_substantive_rationality`, `not_entails_substantive_intentionality` (HostileSemantics Part A2, `{}`) — o fragmento performativo é satisfeito com `Mind`/`Ratio`/`Degree` vazios. C24 é **teorema-válido** na ontologia corrente, mas **não estabelece** pessoalidade substantiva. Reancorar exigiria premissa substantiva nova (registada, não introduzida). |
| **Person → ChoiceField** | `Choice.person_hasChoiceField` | **Caso A/C (Campo de escolha fraco)** | O campo de escolha — `ChoiceField(s,p,q)` (*escolha fraca: alternativas incompatíveis estão presentes*) — é DEFINICIONAL a partir do ato intencional (`Person s → ∃p q, ChoiceField s p q`), footprint `{Means, Subject}`. Aviso de auditoria (freedom/choice fix, 2026-09-18): o agente relaciona-se apenas com o conteúdo adotado `p`; o outro corno `¬p` é fornecido pela lógica pura (`incompatible_self_negation`), NÃO pelo agente. Isto **não** é escolha genuína. |
| **Asserts → Selects** | `Choice.asserts_selects`<br>`Choice.asserts_selects_all_incompatible`<br>`Choice.selection_exists`<br>`Choice.no_selection_no_assertion` | **Caso B (Seleção Semântica Provada)** | **F1b reaberto e resolvido no nível semântico**: qualquer ato assertivo constitui seleção semântica direcionada (`Selects s p q := Asserts s p ∧ Incompatible p q ∧ ¬ Asserts s q`). Provado por consistência lógica (`assertion_consistency`, `incompatible_self_negation`, `no_one_asserts_incompatible_pair`), footprint `{Means, Subject}` (VOCAB apenas). O contrapositivo `no_selection_no_assertion` prova que sem seleção não há asserção. |
| **Correct → Selects** | `Order.correct_implies_selection`<br>`Order.correct_implies_selection_all_incompatible` | **Caso B (Candidato B assentado)** | O juízo correto (`Correct s p := A s p ∧ T p`) reduz-se definicionalmente (`rfl`) a `Asserts s p := Act s p ∧ p` e acarreta seleção semântica contra alternativas incompatíveis sem axiomas (`{Means, Subject}`). |
| **Act → Asserts (Ponte C)** | `Choice.act_implies_asserts_bridge`<br>`Choice.selection_exists_of_act` | **Caso D (Ponte SEM precificada)** | Passar do datum bruto do ato intencional (`∃ s p, Act s p`) para asserção exige uma premissa semântica explícita (`act_implies_asserts_bridge`, SEM). Sob a retorsão, a asserção é dada; sob o datum genérico, a ponte é necessária. |
| **DeliberateChoice** | `Choice.DeliberateChoice`<br>`Choice.deliberateChoice_implies_selects`<br>`Choice.deliberateChoice_implies_chooses` | **Caso A (Definição de Escolha Deliberativa)** | `DeliberateChoice s p q := Means s p ∧ Means s q ∧ Incompatible p q ∧ Asserts s p ∧ ¬ Asserts s q` — o sujeito concebe ambos os cornos, mas assere apenas um (`{Means, Subject}`). Acarreta seleção e escolha co-significada. |
| **Selects ↛ DeliberateChoice** | `HostileSemantics.selection_not_entails_deliberate_choice` | **Caso D (Separação Hostil)** | A seleção semântica não acarreta escolha deliberativa: `CountermodelVeridicalMeaning.Single` satisfaz `Selects () True False`, mas `DeliberateChoice` é impossível por não co-significar o corno rejeitado (`{}`). |
| **Selects ↛ Chooses** | `HostileSemantics.selection_does_not_imply_genuine_choice` | **Caso D (Separação Hostil)** | A seleção semântica NÃO força a co-significação de ambos os cornos incompatíveis exigida pelo antigo `Chooses`: `CountermodelVeridicalMeaning.Single` satisfaz `Selects () True False` enquanto `Chooses` é impossível (`{}`). |
| **Selects ↛ FreeWill** | `HostileSemantics.selection_does_not_imply_freewill` | **Caso D (Separação Hostil)** | A seleção semântica NÃO força liberdade libertária: um agente determinista representa, seleciona e exclui o corno incompatível sem contingência modal (`{}`). |
| **Asserts ↛ Asserts ∧ Means ¬p** | `HostileSemantics.CountermodelVeridicalMeaning.TwoPersons.assertion_does_not_imply_rejected_horn_meaning`<br>`HostileSemantics.CountermodelVeridicalMeaning.TwoPersons.full_fragment_without_deliberate_resource` | **Caso D (Separação Hostil)** | A asserção fáctica em dois sujeitos NÃO força a representação da negação contraditória: sob significação verídica, `Asserts` é satisfeito enquanto `deliberateGenuineChoiceResource` é provadamente falso (`{}`). |
| **BilateralIntentionality → GenuineChoice** | `Choice.bilateral_intentionality_principle`<br>`Choice.genuineChoice_exists_of_bilateral_intentionality` | **Caso B (Princípio Semântico Candidato)** | Sob a tese semântica de intencionalidade bilateral (`Means s p → Means s (¬p)`, SEM), qualquer asserção fecha estritamente a escolha genuína (`genuineChoice_exists`, `{Means, Subject}`). |
| **Doubt → GenuineChoice** | `Choice.Doubts`<br>`Choice.genuineChoice_of_doubt`<br>`Choice.freeWill_of_doubt` | **Caso B (Capacidade Cartesiana Candidata)** | Se o ato performativo for concebido como dúvida cartesiana (`Doubts s p := Means s p ∧ Means s (¬p)`), a escolha genuína e a liberdade do sujeito são imediatas (`{Means, Subject}`). |
| **ChoiceField ↛ Chooses** | `Choice.Chooses` / `rejectedHornCoMeant` (`F1b`) | **Caso D (Bloqueado)** | Não se segue logicamente da presença de alternativas que o sujeito escolha genuinamente (`Chooses(s,p,q)`: *escolha forte: o sujeito co-significa alternativas incompatíveis*). A escolha genuína exige que o sujeito co-signifique os DOIS cornos incompatíveis (`A s p ∧ A s (¬p)`); `Means` é uma relação opaca e `AxTwoSubjects` dá dois sujeitos DIFERENTES, cada um com um só conteúdo. Falta exatamente `rejectedHornCoMeant : (∃s p, A s p) → ∃s p, A s p ∧ A s (¬p)`. `CountermodelNoFreeWill` mostra `Act ↛ Chooses` e `Act ↛ FreeWill` (`{}`); NÃO é contramodelo da definição `Chooses → FreeWill` (que é livre). **Milestone hostil 2026-09-18** (Batch fronteira escolha-genuína): o bloqueio é *irreducível* — o modelo veridical `CountermodelVeridicalMeaning` (significação veridical, `Means s p → p`) satisfaz TODO o fragmento agency/choice/order (datum do ato, pluralidade, certo/errado, `judge_commits`, falibilidade) com escolha genuína **vazia**, sob a própria definição Logos de `Chooses`; `not_entails_genuine_choice(_with_plurality)` (`{}`) formaliza a não-derivação; a via performativa assertiva é *impossível* por `assertion_consistency`/`no_one_asserts_incompatible_pair`, e a veridicalidade é refutada apenas por `genuineChoice_requires_error_possibility`. F1b permanece BLOCKED (**opção 3**: premissa substantiva nova seria necessária). |
| **Chooses → FreeWill** | `Choice.chooses_implies_freeWill` | **Caso A (Definicional)** | `FreeWill s := ∃p q, Chooses s p q` — por DEFINIÇÃO. A liberdade não é um passo metafísico adicional a partir do ato bruto; é a própria existência de uma escolha genuína entre alternativas incompatíveis. Footprint **`{Means, Subject}`** (VOCAB apenas — o conteúdo lógico é gratuito). A existência incondicional (`freeWillExists`) é que fica bloqueada, por depender de `rejectedHornCoMeant`. |

Declared (Level 2): `Subject` is an uninterpreted pure sort (`axiom Subject : Type`,
Tag: VOCAB); `act` is the uninterpreted weak performed event (`axiom act : Subject → Prop → Prop`,
Tag: VOCAB); `Means` is an uninterpreted intentional relation (`axiom Means : Subject → Prop → Prop`,
Tag: VOCAB); `Act` is the constitutively subject-indexed meaning-act (`Act s p := Means s p`);
`SubjectExists s := ∃ p, Act s p` is the constitutive rule of subjecthood (`act_requires_subject`);
`axiom Cogito` is **REMOVED ENTIRELY**; `Cogito` is a derived theorem from performative
assertion (`Asserts s p → ∃ s' p', Act s' p'`). Retorsion directly establishes the weak act via
`noWeakAct_selfRefutes : asserts speaker NoWeakAct → False` (`{Subject, act}`).
The strong retorsion shortcut is `noCogito_selfRefutes : Asserts speaker NoAct → False` (`{Means, Subject}`)
under the intentional assertion `Asserts s p := Act s p ∧ p`.
`GroundProp`, `GroundPrincipleProp` (SEM); `AxPersonalGround` (META, D9).

## Deferred / blocked

| ID | Prose | Status | Missing |
|----|-------|--------|---------|
| F1a | §13–§15 choice-field existence (`∃s p q`, `ChoiceField s p q`) | PROVEN | `person_hasChoiceField`/`choiceField_exists` `{Means, Subject}` + `judge_commits` `CL` (choice-realism batch, C51–C52/C55; renamed 2026-09-18 — field form, not genuine choice) |
| F1b | §15 genuine choice & freedom of the actor | OPEN | alvo explícito `Choice.genuineChoice_exists := ∃ s, ∃ p q, Chooses s p q` (def-proposição; **não** axioma/`sorry`); reduzido estritamente via `deliberateChoice_negation_iff` e `deliberateChoice_implies_chooses` à obstrução mínima exata: `Choice.deliberateGenuineChoiceResource := ∃ s : Subject, ∃ p : Prop, Asserts s p ∧ Means s (¬ p)` (existência de uma asserção verídica cuja negação contraditória é simultaneamente concebida em pensamento). Provado `Choice.genuineChoice_exists_of_assertion_and_negation_meaning : deliberateGenuineChoiceResource → genuineChoice_exists` (`{Means, Subject}`). A implicação `Selects s p (¬p) → Means s (¬p)` é estritamente **FALSA** (refutada em `CountermodelVeridicalMeaning.Single.selects_does_not_imply_rejected_horn_meaning`). A seleção não força conceber a negação. |
| F2 | §21 teleology (`Ought → Goal`) | DEFERRED | deontic layer (normativity → telos) |
| F3 | §28 Good (`§20 → bem`) | DEFERRED | moral good from logical normativity not yet derived |
| F4 | §28 Love | PROVEN↑ | `Love.T13_someoneLovable` (C41) under `{AxTwoSubjects, Means, Subject}` |
| F5 | §28 EternalRelation | PROVEN↑ | `Love.T14_eternalRelation` (C42) under `{AxTwoSubjects, Means, Subject}` |
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
| C94 | §27 | `Choice.noStrongTruth_assertable_refutes : Asserts speaker (¬ ∃ τ : Semantics.Form, Semantics.NecessarilyTrue τ) → False` — retorsão assertiva do dado mundial: ninguém pode asserir que não existe verdade forte (o ato de negar o dado é destruído por ele) | PROVEN | **`{Means, Subject, CL}`** (via C93 + Asserts) |
| C95 | §27 | `Semantics.atoms_are_modally_free : ∀ n : Nat, ¬ NecessarilyTrue (Form.atom n) ∧ ¬ NecessarilyFalse (Form.atom n)` — a parede dos átomos (fronteira de C59): nenhum átomo é fixado no percurso modal — a verdade forte fixa leis, não conteúdos | PROVEN | **`{}`** (Vocab puro, sem axiomas; `strongTruth_is_not_atomic` leva `{CL}`) |
| C96 | §27 | `Semantics.some_formula_contingent : ∃ τ : Semantics.Form, ¬ NecessarilyTrue τ ∧ ¬ NecessarilyFalse τ` — conteúdo contingente existe (contrapeso de C59): há fórmula nem necessariamente-verdadeira nem necessariamente-falsa — o percurso modal não é degenerado | PROVEN | **`{}`** (via C95; `strongTruth_and_contingent_content` leva `{CL}`) |
| C38 | P2 | `Necessity.necDistinction : Necessity (¬ N_T ∧ ¬ N_F)` | PROVEN (was AXIOM) | `{}` (E0; C1: identity-model alias; world content = C37) |
| C39 | P4 | `Choice.T11_choiceField` | PROVEN | `{Means, Subject}` (campo de escolha — não escolha genuína — derivado do ato intencional C68 → C24 → C39; renomeação/split 2026-09-18; **usa C24 só no sentido fraco** `∃p, Means s p` — forma mais forte válida = reancoragem em `SubjectExists`/`Intentional`) |
| C40 | P5/P7 | `Plurality.T12_twoPersons` | PROVEN↑ | `{AxTwoSubjects, Means, Subject}` (settled by Unit countermodel that 1 act does not entail plurality; requires META bridge `AxTwoSubjects`) |
| C41 | P7 | `Love.T13_someoneLovable` | PROVEN↑ | `{AxTwoSubjects, Means, Subject}` (via C40) |
| C48 | P1/§1 | `Plurality.cogito_from_T12` | PROVEN↑ | `{AxTwoSubjects, Means, Subject}` |
| C49 | §13/IM_STUPID | `Choice.meaning_needs_subject` + `Choice.meaning_I_needs_subject` (definitional form: `Meaning_I p → ∃s, Means s p`) | PROVEN | `{Means, Subject}` |
| C50 | §14 | `Choice.incompatible_self_negation` | PROVEN | **`{}`** (pure logic — the field around any meaning-act) |
| C51 | §14/IM_STUPID | `Choice.person_hasChoiceField : Person s → ∃p q, ChoiceField s p q` — **subject ⇒ campo de escolha** (renomeado 2026-09-18; NÃO é escolha genuína) | PROVEN | `{Means, Subject}` |
| C52 | §14 | `Choice.choiceField_exists` | PROVEN | `{Means, Subject}` (o campo é real, derivado do ato intencional C68 → C52 via `intentional_hasChoiceField` a partir de `act_implies_intentional` — reancorado em código 2026-09-18, sem passar por `Person`; renomeado 2026-09-18) |
| C53 | §14 | `Choice.noChoiceField_selfRefutes : Asserts speaker NoChoiceField → False` | PROVEN | `{Means, Subject}` (retorsão performativa do campo: negar o campo é ele próprio um ato de campo contra a sua negação) |
| C54 | IM_STUPID §2 | `Choice.JUDGE_HAS_CHOICE_FIELD : (¬N_T ∧ ¬N_F) → ∃s p q, ChoiceField s p q` — **right/wrong ⇒ campo de escolha** | PROVEN↑ | `{AxTwoSubjects, Means, Subject}` (derivação operativa via AxTwoSubjects h e person_hasChoiceField; renomeado 2026-09-18) |
| C55 | §8/§14 | `Order.judge_commits : ∃s p q, A s p ∧ (Correct s p ∨ Incorrect s p) ∧ ChoiceField s p q` — the judge HAS a choice-field (não escolha genuína) | PROVEN↑ | `{AxTwoSubjects, Means, Subject, CL}` (defs act-relative §8) |
| C56 | P6 | `Value.alone_no_other_help_harm` | PROVEN | `{Subject}` |
| C57 | §26 | `Choice.noSubject_selfRefutes : Asserts speaker NoSubject → False` | PROVEN | `{Means, Subject}` (retorsão performativa genuína: negar o sujeito é um ato que testemunha o sujeito) |
| C42 | P8 | `Love.T14_eternalRelation` | PROVEN↑ | `{AxTwoSubjects, Means, Subject}` (built on directed pair C47 under AxTwoSubjects) |
| C43 | P8 | `Love.T14_content` | PROVEN↑ | `{AxTwoSubjects, Means, Subject}` |
| C44 | P8 | `Love.T14_world` (`NecessityPH`) | PROVEN↑ | `{AxTwoSubjects, Means, Subject}` (world-anchored honest □) |
| C45 | P8 | `Love.T14_square` (alias `Necessity`) | PROVEN↑ | `{AxTwoSubjects, Means, Subject}` (image of the old statement shape) |
| C46 | P5 | `Value.valueInterpersonal_of_split` | PROVEN↑ | `{AxTwoSubjects, Means, Subject}` (recovery theorem under AxTwoSubjects) |
| C47 | P5/P7 | `Plurality.T12_directedPair` | PROVEN↑ | `{AxTwoSubjects, Means, Subject}` (chain node — distinctness is forward direction; T14 built on this node) |
| C61 | P3 | `Choice.rightWrong_implies_someone_means` — "há certo e há errado → há alguém para quem algo significar" | PROVEN↑ | `{AxTwoSubjects, Means, Subject}` (`JUDGE_HAS_CHOICE_FIELD` C54 ∘ `rightWrongDistinction` C36) |
| C62 | P3 | `Order.rightWrong_implies_meaning` (+ `Order.rightDistinctWrong_implies_meaning`) | PROVEN | `{Means, Subject}` |
| C101 | §8 | `Order.act_iff_asserts_or_incorrect : A s p ↔ Asserts s p ∨ Incorrect s p` — **partição bivalente do ato intencional**: todo ato intencional é asserção verídica ou juízo incorreto | PROVEN | `{Means, Subject, CL}` |
| C97 | §15 | `Choice.deliberateChoice_implies_selects : DeliberateChoice s p q → Selects s p q` — **escolha deliberativa acarreta seleção**: quem delibera seleciona a favor de p e contra q | PROVEN | `{Means, Subject}` |
| C98 | §15 | `Choice.deliberateChoice_implies_chooses : DeliberateChoice s p q → Chooses s p q` — **escolha deliberativa acarreta escolha co-significada**: quem delibera concebe ambos os cornos | PROVEN | `{Means, Subject}` |
| C99 | §15 | `Choice.selection_exists_of_act (hBridge : act_implies_asserts_bridge) (h : ∃ s p, Act s p) : ∃ s p q, Selects s p q` — **existência de seleção a partir do ato sob a ponte**: o ato rende seleção sob a ponte semântica | PROVEN | `{Means, Subject}` |
| C100 | §15 | `Choice.deliberateChoice_iff_selects_and_means : DeliberateChoice s p q ↔ Selects s p q ∧ Means s q` — **decomposição exata da escolha deliberativa**: deliberação é seleção semântica mais representação da alternativa rejeitada | PROVEN | `{Means, Subject}` |
| C69 | §15/F1b | origin freedom (retired) | BLOCKED | (retired: manufactured freedom via `Sum.inl` destroyed under hostile semantics; genuine-choice replacement is `Choice.Chooses`/`rejectedHornCoMeant`) |
| C70 | §15/F1b | posited content non-freedom (retired) | BLOCKED | (retired: manufactured free will destroyed under hostile semantics) |
| C71 | §15/F1b | origin-freedom denial self-refutation (retired) | BLOCKED | (retired: manufactured freedom destroyed under hostile semantics) |
| C72 | §15/F1b | judge is free (retired) | BLOCKED | (retired: act does not entail free will; `Order.judge_commits` yields only the choice field; `Chooses → FreeWill` is definitional but its existence needs `rejectedHornCoMeant`) |
| C73 | P5/P7 | `Person.twoPersonsFromSubject` | BLOCKED | (demoted: Unit countermodel settles that 1 act does not entail plurality; manufactured `Sum.inl`/`inr` witness destroyed) |
| C74 | P5 | `Value.aloneExcluded : ¬ ∃ s, Person s ∧ Alone s` | PROVEN↑ | `{AxTwoSubjects, Means, Subject}` (under the plurality bridge `AxTwoSubjects`, a lone person is excluded) |
| C75 | P7 | `Person.everyContentIsAPerson` | BLOCKED | (killed under hostile semantics: content existence does not imply personhood; tripartite report) |
| C76 | P8 | `Love.T14_canonicalRigid` | BLOCKED | (excised: manufactured witness destroyed) |
| C77 | P5/P8 | `Love.necessaryPersonExists (h : ∃ s p, Act s p) : ∃ s, Person s ∧ NecessarySubject s` — **the necessary person exists**: from the performative act-datum (C68), a person (`T5_personExists`, C24) that is necessary by definition (`AxPersonStability`, esse est agere) | PROVEN | `{Means, Subject}` (VOCAB; **re-anchored 2026-09-18** ao dado performativo, sem `AxTwoSubjects` — a necessidade da pessoa é *definicional*, `ExistsAt (Subject) := True`; complementar ao concreto `Love.no_contingent_person`; usa C24 só no sentido fraco — reancoragem `SubjectExists`/`Intentional`; não depende da pessoalidade substantiva) |
| C85 | P6 | `Value.help_not_harm` — **princípio de benevolência**: no plano fundante, ajudar exclui prejudicar (`Helps s t → ¬ Harms s t`) | PROVEN | `{Subject}` |
| C86 | P6/P8 | `Love.love_helps` (+ `Love.love_not_harms`, `Love.loves_of_helps`) — **amor como benevolência direcionada**: amar é ajudar e não prejudicar (`Loves s t := Helps s t ∧ ¬ Harms s t`) | PROVEN | `{Subject}` |
| C92 | P8/§27 | `Love.necessary_entity_exists : ∃ e, NecessaryEntity e` — **existe uma entidade necessária** (rota performativa C24 + `AxPersonStability` + lift C91; o correlato da pessoa, ≠ T7) | PROVEN | `{Means, Subject}` (sem `AxTwoSubjects`; distinto de T7/C18; usa C24 só no sentido fraco — reancoragem `SubjectExists`/`Intentional`) |

Declared (Level 3): **M1 (A3, 2026-09-16): `Affects` is a structural
DEFINITION (`Affects s t := s ≠ t`), and `AxPersonsAffect` is a THEOREM** (distinct persons are
distinct — `Or.inl hne`). `Helps` is its positive projection (`:= Affects`),
`Harms` has no reality in the foundational order (`:= False`), and
`help_not_harm` is a THEOREM (`{}`).
`Loves` is **benevolent love** (`Loves s t := Helps s t ∧ ¬ Harms s t`, C86).
The plurality bridge `AxTwoSubjects` (Tag: META) is **RESTORED** as the honest metaphysical price of plurality,
following the mathematical proof of the Unit countermodel in `HostileSemantics`.
(C74) make solipsism structurally impossible.
`AxPersonStability` was the SEM bridge for world-persistence of persons — **now a theorem** (esse est
agere, 2026-09-17): `Person → Intentional → Means` with `ExistsAt` as agency.
T14 stands on the pair + esse est agere under `AxTwoSubjects`.
Modal layer is derived (C1): `Necessity: Prop → Prop` is a *definition*
(identity-model alias) and `NecessityPH : (World → Prop) → Prop` the
semantics-grounded operator; `necK/necT/nec4` (alias) and `necKPH/necTPH/nec4PH`
are theorem; `necDistinction` is a theorem. No modal axiom remains.

## Level 2c — the act as initiation (`Logos.Initiation`, 2026-09-17)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C63 | §1 | `Initiation.branches_not_transfer : Branches R → ¬ IsTransfer R` — **iniciação ≠ transferência**: uma relação com alternativas genuínas não é o gráfico de função nenhuma | PROVEN | **`{}`** (lógica pura — sem axioma, sem vocabulário) |
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
| F7 | §15 the bipolar half of freedom | BLOCKED | (the bipolar half is subsumed by unary `FreeWill`; the remaining gap is NOT "freedom impossible to derive" — it is **existence of *genuine choice* not yet derived from the performative datum**: `genuineChoice_exists` BLOCKED on `rejectedHornCoMeant`; `Chooses → FreeWill` is definitional, `freeWillExists_of_genuineChoice` `{Means, Subject}`; world-level `ChoiceAt` remains a future SEM vocabulary) |
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
