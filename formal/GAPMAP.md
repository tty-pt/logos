# GAPMAP.md — theorem ledger of Γ (generated from `#print axioms`, 2026-09-17, post A2-swap-theorem)

Statuses: `PROVEN` (theorem, kernel-checked) · `PROVEN↑` (theorem under
flagged axioms) · `AXIOM` (declared) · `BLOCKED` (missing lemma named) ·
`DEFERRED` (out of scope of this milestone).

`CL` = `{propext, Classical.choice, Quot.sound}` (classical meta-logic, D1).

## Batch two-kinds (2026-09-28) — os sujeitos vêm em dois géneros; o contingente é de outro género

O `SubjectExistsAt w s := w = actualWorld` incondicional escondia uma premissa: tratava
todo o sujeito como contingente. A doutrina dos dois géneros exibe-a. `Agency.NecessarySubjectKind`
é o predicado do género necessário (o fundamento em Tipo Pessoal — Pessoa, logo Sujeito);
`ContingentSubjectKind` é a sua negação, o outro género (a pessoa individual, relativa ao
mundo actual, que poderia não ter existido). `SubjectExistsAt` lê o género:
`NecessarySubjectKind s ∨ w = actualWorld`. Se o género necessário é habitado é a ponte
metafísica preçada C404, nunca parte do vocabulário.

**Duas adições ao inventário, ambas ledgerizadas:** `NecessarySubjectKind` (`Tag: VOCAB`,
o classificador) e `necessaryPersonalSubjectExists` (`Tag: META`, a habitação por uma
Pessoa). Total **24 → 26**; VOCAB 14 → 15; META 4 → 5.

| Claim | Secao | Declaracao | Status | Pegada |
|---|---|---|---|---|
| C403 | géneros | `Agency.NecessarySubjectKind : Subject → Prop` (`Agency.lean:62`, `Tag: VOCAB`) — **o vocabulário dos dois géneros**: o predicado do género necessário. A sua negação é `ContingentSubjectKind`. Se o género necessário é habitado é a ponte C404, nunca parte desta linha | AXIOM | `{Subject}` |
| C404 | géneros | `Plurality.necessaryPersonalSubjectExists : ∃ s : Subject, NecessarySubjectKind s ∧ Person s` (`Plurality.lean`, `Tag: META`) — **a ponte**: o género necessário é habitado por uma Pessoa — o fundamento em Tipo Pessoal, lido como Sujeito. Pessoa é Sujeito por definição; o Tipo Pessoal do fundamento está provado (T8, `normative_ground_is_personal`); o passo modal é esta ponte, e é todo o preço de "uma pessoa que significa tem de ser necessária". Não identifica o construtor-fundamento com correlato algum (`ofGround ≠ EntityOf s` continua); não diz que o Criador habita o mundo (nenhum elo ao habitante é afirmado); não torna necessário nenhum outro sujeito (a pertença ao género é por sujeito) | AXIOM | `{Means, NecessarySubjectKind, Subject, Will, subjectWill}` |
| C405 | géneros | `Plurality.necessaryKindSubject_is_necessary (s : Subject) (h : NecessarySubjectKind s) : NecessarySubject s` — um sujeito do género necessário é necessário: o correlato existe em todo o mundo pelo disjunto esquerdo de `SubjectExistsAt`. A forma relativa-ao-género da persistência | PROVEN | `{NecessarySubjectKind, Subject}` |
| C406 | géneros | `Plurality.contingentKindSubject_not_necessary (s : Subject) (h : ContingentSubjectKind s) : ¬ NecessarySubject s` — um sujeito do género contingente não é necessário: no mundo todo-`TV.f` o correlato falha. É onde vivem agora todos os achados de contingência antes incondicionais | PROVEN | `{NecessarySubjectKind, Subject}` |
| C407 | géneros | `Plurality.necessarySubject_exists : ∃ s : Subject, NecessarySubject s` — um sujeito necessário existe, pela ponte. Pegada só VOCAB mais a ponte | PROVEN↑ | `{Means, NecessarySubjectKind, Subject, Will, necessaryPersonalSubjectExists, subjectWill}` |
| C408 | géneros | `Plurality.necessaryPersonalSubject_derived : ∃ s : Subject, NecessarySubject s ∧ Person s` — uma pessoa necessária existe, pela ponte: a pessoa que significa é do género necessário; a pessoa contingente é do outro género | PROVEN↑ | `{Means, NecessarySubjectKind, Subject, Will, necessaryPersonalSubjectExists, subjectWill}` |
| C409 | géneros | `NecessaryPersonalGround.necessary_person_derived_from_bridge : ClaimD_NecessaryPerson` — **Claim D derivada em vez de anotada**: a pessoa necessária existe. Reforma a nota "annotated only": o existencial necessário deixou de estar vazio. O preço é exactamente a ponte — rejeite-a e isto cai com ela; a pessoa contingente, o habitante do mundo e todos os contramodelos ficam intocados por ela | PROVEN↑ | `{Means, NecessarySubjectKind, Subject, Will, necessaryPersonalSubjectExists, subjectWill}` |

### Lote B — a leitura dos dois géneros (2026-09-28) — `SUBJECTS.md`

C403 introduced the kind vocabulary as a free predicate. This batch reads it. **Zero
axioms added, zero existing footprints moved**: six theorems, all on
`{NecessarySubjectKind, Subject}`, plus one `def`. The plan of record, including the
gap this batch does *not* close, is `SUBJECTS.md` (English, repo root).

| Claim | Secao | Declaracao | Status | Pegada |
|---|---|---|---|---|
| C410 | géneros | `Plurality.kinds_are_the_modal_partition (s : Subject) : NecessarySubjectKind s ↔ NecessarySubject s` — **a manchete**: os dois géneros são exactamente os dois perfis modais. Um sujeito é do género necessário sse o seu correlato existe em todo o mundo. A directa é C405; a inversa instanciando no mundo da falsidade e usando `TV.noConfusion` — as mesmas duas linhas que C406 já usava. `NecessarySubjectKind` deixa de ser um rótulo solto: a sua interpretação é o perfil de mundo, e a partição é exaustiva e disjunta por C411. C403 **mantém** a sua etiqueta `Tag: VOCAB` — este teorema interpreta a etiqueta, não a degrada | PROVEN | `{NecessarySubjectKind, Subject}` |
| C411 | géneros | `Plurality.contingentKind_iff_not_necessary (s : Subject) : ContingentSubjectKind s ↔ ¬ NecessarySubject s` — o género contingente é a complemento do género necessário por definição, e por C410 é a complementaridade da rigidez-mundo ela mesma. Os dois géneros e os dois perfis modais são uma partição, não duas | PROVEN | `{NecessarySubjectKind, Subject}` |
| C412 | géneros | `Plurality.necessaryKind_existsAt_every_world {s : Subject} (h : NecessarySubjectKind s) (w : World) : Logos.Entity.SubjectExistsAt w s` — o perfil do género necessário: **todos** os mundos. Disjunto esquerdo, e nada mais | PROVEN | `{NecessarySubjectKind, Subject}` |
| C413 | géneros | `Plurality.contingentKind_existsAt_actualWorld_only {s : Subject} (h : ContingentSubjectKind s) (w : World) : Logos.Entity.SubjectExistsAt w s ↔ w = Entity.actualWorld` — o perfil do género contingente: **o mundo actual e nenhum outro**. Com C412, a **assimetria de habitação** em forma formal — perfis disjuntos e complementares. Nada disto diz que qualquer género seja habitado: o necessário é pago por C404, o contingente é a lacuna registada abaixo | PROVEN | `{NecessarySubjectKind, Subject}` |
| C414 | géneros | `Plurality.falsityWorld_holds_no_contingent_subject : ¬ ∃ s : Subject, ContingentSubjectKind s ∧ Logos.Entity.SubjectExistsAt Entity.falsityWorld s` — o mundo da falsidade não hospeda nenhum sujeito do género contingente. **O que isto não diz**: não diz que o mundo da falsidade seja vazio. Um sujeito do género necessário existe lá também (C405/C412), e o construtor do fundamento também, enquanto nenhum átomo existe (`EntityExistsAt w (ofAtom n) := w n = TV.t`). Sob a semântica de Γ o mundo todo-`TV.f` é o mundo **só-do-género-necessário**, e é o nosso mundo que fica excluído dele — de graça, porque o mundo actual tem conteúdo contingente (C350 `contingent_realm_obtains`) | PROVEN | `{NecessarySubjectKind, Subject}` |
| C415 | géneros | `Plurality.contingentSubject_might_not_have_existed {s : Subject} (h : ContingentSubjectKind s) : ∃ w : World, ¬ Logos.Entity.SubjectExistsAt w s` — um sujeito do género contingente podia não ter existido: falha no mundo da falsidade. C406 em forma relativa a mundos — o conteúdo formal de "o outro podia não ser (os humanos)" | PROVEN | `{NecessarySubjectKind, Subject}` |

Também neste lote: `Entity.falsityWorld` (`def`, pegada `{}`) dá nome ao que
`LovesAsGround.falsityWorld_ne_actualWorld:159` e os teoremas dos géneros já usavam
como lambda inline, para que "o mundo vazio" seja um ponto do espaço-de-mundos que o
livro-razão possa apontar.

#### A lacuna que este lote **não** fecha (BLOCKED)

O Mirror necessary kind é habitado e provado (C404 → C407/C408/C409). O Mirror
género contingente não é nem provado nem pago, pelo que todo o achado contingente
— C329, C330, C246/C247, `subject_not_everlasting`, C346–C348, C351/C352, C367,
C386/C387, C42/C44/C45 de T14 — carrega uma hipótese `ContingentSubjectKind s` que
`#print axioms` **não vê**. Decisão do autor (2026-09-28): *"Well, we really haven't
proved it yet so truly it's a gap for now."* Logo, sem axioma novo, e registado aqui
como nota (não como linha de tabela, porque não há declaração):

> **Lema em falta (BLOCKED).** `∀ w : World, ∀ s : Subject, Creates s w → ∃ t : Subject,
> ContingentSubjectKind t ∧ Person t` — *a criação implica uma pessoa contingente.*
>
> **Bloqueado no primeiro conjuncto.** `Creates` não está no vocabulário: o resultado
> permanente de C110 é que o fundamento não_entra um registo de criação,
> `Entity.ofGround` não tem cláusula de produção, e a via da criação não está aberta.
> Mesmo concedido `Creates`, nada liga o género do criador à contingência do mundo.
>
> **O argumento do autor, registado como via pretendida (2026-09-28):** *"why the
> necessary subject would create a world without contingent persons if He didn't need
> the world anyway"* — o argumento torna plausível o **segundo** conjuncto (um mundo
> que não precisava ter existido, trazido à existência por um sujeito que dele não
> precisa, tem conteúdos não-necessários), e é a forma "não há criação sem uma
> pessoa" do mesmo. É um argumento *sobre* a produção, logo não pode ser discharged
> antes de a via da criação ser aberta.

O que Γ **pode** dizer hoje, e o que o livro-razão tem de mostrar: (a) há um sujeito
do género necessário (C407/C408, pago META); (b) o mundo actual tem conteúdo
contingente (C350, `{NecessarySubjectKind, Subject}`, de graça, por um átomo); mas
**não** (c) o mundo actual tem um sujeito do género contingente.

O que este lote **não** faz: não toca na cláusula contingente (`w = actualWorld`
permanece o disjunto direito); não retira nenhum achado — `PersonNotNecessary`,
`no_necessary_subject`, a independência Tipo 1/4 de `PersonhoodOntologyAudit`,
`subject_not_everlasting`, C329, C344, C346–C348, C246 sobrevivem, os universais
como condicionais ao género; não liga a ponte ao habitante do mundo; não toca em
`AxTwoSubjects` (que sai de C367/C351/C352/C42/C44/C45 por um motivo independente
e registado na 5.ª correcção: exibir o género subsume a testemunha).

## Batch precedence (§9) e §18 (2026-09-28) — a precedência à distinção, e o panteísmo por identidade

Duas características abrem hoje sem uma única linha no livro-razão. **§9** (a
precedência do Fundamento à distinção entre certo e errado) era a única das dezenove
características com **zero** teoremas, zero claim, e **zero linha** na tabela gerada
`CLASSICAL_ATTRIBUTES` (`scripts/build_deduction.py:5268`) — por isso era invisível
para quem lê. **§18** (exclusão do panteísmo) era ❌ não estabelecida, por não haver
predicado `Universe` nenhum.

O lote traz **15 linhas novas, 0 axiomas novos, 0 primitivas novas, 0 estipulações
novas, 0 registos ◈ novos**. O total declarado fica em **27**.

**Uma correcção, e ela é o achado mais honesto do lote.** A via de `base.txt` §9 passa
por um "mundo vazio" — um mundo onde a distinção não está instanciada em lado nenhum,
que o fundamento teria de preceder. O plano (`AUDIT.md` §4, Stage 0) propunha como
primeiro lema `{}` a linha

    no_form_satisfied_at_falsity_world (φ : Form) : ¬ Satisfies falsityWorld φ

**Essa linha é falsa e não foi provada**, porque `Satisfies` é fechada sob negação: no
mundo todo-`TV.f` vale `Satisfies (Form.not (Form.atom 0))`. Não há mundo nenhum que não
satisfaça nenhuma forma, e **C418 é a refutação machine-checked disso**. O livro-razão
passa por isso a levar a forma **verdadeira e mais fraca** — um mundo onde **nenhum
átomo** é verdadeiro — e a levar a refutação da leitura forte como linha própria
(C418). O argumento de §9 não fica enfraquecido: fica enunciado com precisão pela
primeira vez. O que muda é que a "ausência" passa a ser um teorema, não um adjectivo.

`base.txt` §9 nunca foi reescrito por esta via: a characteristic continua sendo a do
autor; o que muda é o que Γ pode dizer dela.

| Claim | Secao | Declaracao | Status | Pegada |
|---|---|---|---|---|
| C417 | §9 | `Precedence.no_atom_is_true_at_falsityWorld (n : Nat) : ¬ Satisfies Entity.falsityWorld (Form.atom n)` — nenhum átomo é verdadeiro no mundo da falsidade: a valuation todo-`TV.f` é o ponto do espaço-mundos onde a distinção não está instanciada em nenhum conteúdo **atómico**. Esta é a forma honesta de "um mundo onde nada se dá" | PROVEN | `{}` |
| C418 | §9 | `Precedence.every_world_satisfies_some_form (w : World) : ∃ φ : Form, Satisfies w φ` — **a refutação da leitura "mundo vazio"**: para todo o mundo há uma forma satisfeita (o átomo `0` se o mundo o põe verdadeiro, a sua negação caso contrário). Construtiva — o ramo é sobre `w 0 = TV.t` e `TV` deriva `DecidableEq` — logo **sem `Classical.choice`**. É a linha que substitui o lema falso que o plano propunha, e a razão de a precedência se enunciar sobre conteúdo **atómico** e não sobre formas satisfeitas | PROVEN | `{}` |
| C419 | §9 | `Precedence.ofGround_obtains_where_no_atom_is_true : ∃ w : World, (∀ n : Nat, ¬ Satisfies w (Form.atom n)) ∧ ExistsAt w Entity.ofGround` — **precedência no sentido positivo**: o fundamento obtém onde nenhum átomo é verdadeiro. O mundo é `Entity.falsityWorld` e a obtensão é o braço `ofGround` de `EntityExistsAt` (`Entity.lean:66`), logo `True.intro`; o resto é C417. O preço vocabulary-only é o artefacto de `ExistsAt` desenrolar para `EntityExistsAt` — a prova nunca lê o predicado de género | PROVEN | `{NecessarySubjectKind, Subject}` |
| C420 | §9 | `Precedence.ground_existence_does_not_entail_any_truth : ¬ (∀ w : World, ∀ φ : Form, ExistsAt w Entity.ofGround → Satisfies w φ)` — a obtensão do fundamento **não_entra** nenhuma verdade: a distinção não é um filtro sobre o fundamento nem uma condição dele. Testemunha `falsityWorld` e o átomo `0`. É a **conversa** do que uma leitura de "precedência" precisaria, e é a razão de §9 ser uma separação e não um filtro | PROVEN | `{NecessarySubjectKind, Subject}` |
| C421 | §9 | `Precedence.ground_existence_is_invariant_while_content_varies` — a forma conjoined de C419 e C420 numa linha, para que o leitor veja as duas metades juntas: o que é verdadeiro varia de mundo para mundo (a invariância do agente, `HardenedInvariance` C180), a obtensão do fundamento não | PROVEN | `{NecessarySubjectKind, Subject}` |
| C422 | §9 | `Precedence.ground_scope_is_not_the_truth_set : ¬ (∀ p : Prop, EntityMeans Entity.ofGround p ↔ T p)` — o âmbito do fundamento **não** é o conjunto das verdadeiras: a distinção não se levanta sobre ele. Refuta-se com uma instância, `p := False` (`EntityMeans ofGround p` reduz a `True`, `T p := p`). É C236 lido ao contrário — a linha anterior excluía o fundamento do truth-tracking por um argumento de conteúdo, esta exclui-o pela definição do lado do significado | PROVEN | `{Means, Subject}` |
| C423 | §9 | `Precedence.ground_conditions_every_content_bearer (w : World) (e : Entity) : ExistsAt w e → (∃ p : Prop, EntityMeans e p) → GroundsEntity Entity.ofGround e` — a metade positiva de §9: o fundamento **condiciona** todo portador de conteúdo, na relação `GroundsEntity` que Γ já tem. **A hipótese de significado não é necessária** — `GroundsEntity Entity.ofGround e` é `∀ p, EntityMeans e p → True`, que vale para toda a entidade; a hipótese é carregada porque §9 diz "todo o que se levanta sob a distinção". O facto mais forte que isso implica é o relatório: sob as definições de Γ o fundamento condiciona **tudo**, com ou sem significado. É o mesmo facto que C328 regista para os sem-significado, citado e não re-provado | PROVEN | `{Means, NecessarySubjectKind, Subject}` |
| C424 | §9 | `Precedence.atom_fails_precedence : ¬ ∃ w : World, (∀ n : Nat, ¬ Satisfies w (Form.atom n)) ∧ ExistsAt w (Entity.ofAtom 0)` — a metade **discriminante**, no idioma das separações do corpus: o predicado vale do fundamento e falha de um átomo mundano, com as duas metades provadas. `EntityExistsAt w (ofAtom 0)` *é* `w 0 = TV.t`, que *é* `Satisfies w (Form.atom 0)`: a existência de um átomo é a sua própria verdade, e nenhum mundo pode satisfazer e negar ao mesmo tempo | PROVEN | `{NecessarySubjectKind, Subject}` |
| C425 | §9 | `Precedence.ofGround_precedes_the_right_wrong_distinction : PrecedesRightWrong Entity.ofGround` — **a manchete de §9**: os quatro sentidos num `structure`, para que nenhum predicado-guarda-chuva tenha de carregar a claim inteira. Os três campos juntos são a lacuna-2 de §9 num objecto: o fundamento precede a distinção *e* discrimina-a *e* não é discriminado por ela. "Precede" é deliberadamente `GroundsEntity` — uma condição — e nunca uma derivação | PROVEN | `{Means, NecessarySubjectKind, Subject}` |
| C426 | §9 | `Precedence.rightWrongDistinction_is_world_invariant (_w : World) : ¬ N_T ∧ ¬ N_F` — **o limite, e a razão de §9 não ser um PROVEN simples**: `Core.T p := p` é a identidade em `Prop`, logo `N_T` e `N_F` são afirmações sem índice de mundo. O argumento-mundo na Cottage é **inerte de propósito**: exibe que uma precedência relativa-a-mundo à distinção ao nível de `Prop` não é bem-formada sob o vocabulário actual. §9 está estabelecida na camada semântica (`Satisfies`, C419–C425) e **não** na camada do predicado de verdade; levantar a linha para PROVEN simples exigiria um `T` indexado por mundo, que é vocabulário novo a `Tag: SEM` no mínimo e é decisão do autor | PROVEN | `{}` |
| C427 | §16 item 3 | `DivineImmutability.no_world_indexed_extension_of_meaning_can_vary : ¬ ∃ (R : Entity → World → Prop → Prop), (∀ e w p, R e w p ↔ EntityMeans e p) ∧ (∃ e w₁ w₂ p, R e w₁ p ∧ ¬ R e w₂ p)` — **F16 pelo preço, não pela prova**: nenhuma relação que concorde com `EntityMeans` em todo o mundo pode exibir capacidade variável. Isto torna a razão declarada de F16 um teorema em vez de uma frase numa célula do livro-razão. **F16 continua BLOCKED** — o que se prova aqui é que o bloqueio é forçado: a variação, se existir, tem de vir de **vocabulário novo**, e isso é decisão do autor | PROVEN | `{Means, Subject}` |
| C428 | §16 item 3 | `DivineImmutability.world_indexed_extension_of_meaning_is_world_constant (R) (hExt) (e w₁ w₂ p) : R e w₁ p ↔ R e w₂ p` — a metade **construtiva** de C427, para que o livro-razão possa apontar para a invariância e não só para a sua impossibilidade. C321 (`capacity_invariance_holds_for_every_entity`) é o mesmo facto sobre `CapacityInvariance`; esta é a forma condicional. **Não** é uma afirmação de que o significado do fundamento não muda: não há significado indexado por mundo em Γ que pudesse mudar | PROVEN | `{Means, Subject}` |
| C429 | §18 | `CosmicExistence.no_entity_is_identical_to_the_whole (e : Entity) : ∃ (w : World) (x : Entity), ExistsAt w x ∧ x ≠ e` — a forma de **identidade** do panteísmo falha para os três construtores de `Entity` de uma vez. A prova é a exaustão dos três construtores e é **barata, e deve ser lida como barata**: diz que o `Entity` de Γ é um indutivo com construtores distinguíveis, não que uma ontologia do universo foi adjudicada filosoficamente. Não é um artefacto de mundo vazio: a testemunha é a mesma de C323 | PROVEN | `{NecessarySubjectKind, Subject}` |
| C430 | §18 | `CosmicExistence.the_ground_is_not_the_universe : ¬ Universe Entity.ofGround` — a manchete da forma de identidade de §18, lida de C429 em `e := Entity.ofGround`. `Universe e := ∀ w x, ExistsAt w x → e = x` ("o que obtém **é** e") é a única leitura de identidade bem-formada sobre o tipo de entidade de Γ; a leitura **agregada** ("o universo não é uma entidade") não é uma proposição sobre `Entity` e fica por isso **não-enunciável**, não refutada | PROVEN | `{NecessarySubjectKind, Subject}` |
| C431 | §18 | `CosmicExistence.grounding_never_yields_identity_of_the_totality (e : Entity) : GroundsEntity Entity.ofGround e → ¬ Universe e` — **fundar e identificar não são alternativas compatíveis**: a segunda lacuna declarada de §18 ("não especifica se fundado e idêntico são compatíveis") fica machine-checked como **incompatíveis**. O antecedente é o todo de `GroundsEntity`, que sob as definições de Γ vale para toda a entidade (C328), logo o conteúdo da linha está inteiramente na metade `¬ Universe e` | PROVEN | `{Means, NecessarySubjectKind, Subject}` |

Também neste lote, sem C-id por serem `def`s e não claims: `Precedence.PrecedesRightWrong`
(a `structure` de C425) e `CosmicExistence.Universe` (o `def` de C430/C431). `Universe`
aparece **só em conclusões** — é definido aqui e consumido pelas três linhas acima —
pelo que não precisa de registo ◈ nem de `Tag:`. Este é o ponto de `AUDIT.md` §3.3:
o plano original definia `Universe e := NecessaryEntity e` e thereby re-provava C330
sob um nome novo, o que o corpus proíbe.

#### O que este lote **não** fecha

* **A contingência do realm.** C429–C431 não a tocam. `SUBJECTS.md` §4
  (`∀ w ∀ s, Creates s w → ∃ t, ContingentSubjectKind t ∧ Person t`) continua BLOCKED
  e é citada aí, não re-provada aqui.
* **F16.** Continua BLOCKED. A instrução formal que falta continua a ser, por extenso,
  `EntityMeansAt : Entity → World → Prop → Prop` **mais** uma capacidade exibida que
  varie — e C427 é a prova de que essa variação não pode vir de re-ler a relação actual.
* **§9 ao nível de `Prop`.** Ver C426. O estado de §9 é o **split**: PROVEN na camada
  semântica, não estabelecida na camada do predicado de verdade.
* **A leitura agregada de §18.** Não enunciável sobre `Entity` (ver C430). Se o autor
  a quiser formalizada, é uma linha diferente e mais fraca, e deve ser adicionada
  explicitamente em vez de ser enfiada no `def`.

## Batch precedence-unicity & temporal-separation (2026-09-28) — a articulação que faltava entre §9 e §8, e os dois sentidos da eternidade

Sete linhas novas, **C432–C438**, em dois módulos já existentes, mais a reparação de duas
frases obsoletas (F15 e a nota de Level 14). Invariante do lote: **0 axiomas novos, 0
`Tag:` novos, 0 ◈ novos, 0 sorts novos**. O registo fica em **27 declarados (VOCAB 16 /
SEM 6 / META 5)**.

O lote nasce de duas afirmações que o documento para o leitor ainda escrevia no
**presente** como abertas, e que este corpus consegue fechar sem vocabulário novo:

* `CHARACTERISTICS.md:353` — *"a relação entre precedência sobre a avaliação e
  precedência sobre o tempo não está articulada"*.
* `CHARACTERISTICS.md:313` — *"o texto não distingue atemporalidade de perenidade"*.

| Claim | Secao | Declaracao | Status | Pegada |
|---|---|---|---|---|
| C432 | §9/§8 | `Precedence.stage_invariance_iff_atemporal (e) : StageInvariance e ↔ Atemporal e` — **dois nomes para um predicado**: `StageInvariance` e `Atemporal` desenrolam para a mesma proposição. Achado, não contribuição; importa para ler §8, porque a "atemporalidade" e o segundo campo do mestre da imutabilidade não são dois passos | PROVEN | `{NecessarySubjectKind, Subject}` |
| C433 | §9 | `Precedence.ofGround_sole_precedes_right_wrong : ∀ e, PrecedesRightWrong e → e = Entity.ofGround` — **a unicidade de §9**: o fundamento é a única entidade que precede a distinção. O braço `ofAtom n` é C424 verbatim (`{}`); o braço `ofSubject s` é onde está o preço, e o preço **é F15** | PROVEN | `{Means, NecessarySubjectKind, SemanticFinitude, Subject}` |
| C434 | §9/§8 | `Precedence.stage_invariance_does_not_uniquely_identify_the_ground : StageInvariance Entity.ofGround ∧ ¬ (∀ e, StageInvariance e → e = Entity.ofGround)` — **o contraexemplo**: `Entity.ofAtom 0` é stage-invariant (`0 ≤ t` em todos os estágios) e não é o fundamento, logo as duas precedências diferem em poder discriminante | PROVEN | `{propext, NecessarySubjectKind, Subject}` |
| C435 | §9/§8 | `Precedence.precedence_identifies_the_ground_where_stage_invariance_does_not` — a **articulação** que `CHARACTERISTICS.md:353` dava por aberta, enunciada como **separação de poder discriminante**, não como identificação: os predicados têm extensões diferentes e só `PrecedesRightWrong` singulariza o fundamento | PROVEN | `{propext, Means, NecessarySubjectKind, SemanticFinitude, Subject}` |
| C436 | §8 | `NecessityEternity.everlasting_implies_atemporal (e) : Everlasting e → Atemporal e` — **o passo genérico**, que faltava porque o módulo só tinha as instâncias ao nível do fundamento (`the_ground_everlasting`, `the_ground_atemporal`), ambas por `ofGround_necessary` | PROVEN | `{NecessarySubjectKind, Subject}` |
| C437 | §8 | `NecessityEternity.contingent_subject_is_timeless_but_not_everlasting (s) (hKind) : Atemporal (EntityOf s) ∧ ¬ Everlasting (EntityOf s)` — **o contraexemplo discriminante**. A segunda conjunção é `subject_not_everlasting`; a primeira é nova e **vácua**: sob `ContingentSubjectKind s` a cláusula de existência reduz a `stageOf t = actualWorld`, falsa em todo `t` | PROVEN | `{NecessarySubjectKind, Subject}` |
| C438 | §8 | `NecessityEternity.everlastingness_and_timelessness_are_distinct` — o fecho de C436∧C437, discharging `CHARACTERISTICS.md:313` e a fronteira `NÃO reivindicada` de `base.txt:1521-1524`. **Limite declarado**: Γ não tem teorema que habite `ContingentSubjectKind`, logo a região separadora está habitada nos modelos e não no kernel | PROVEN | `{NecessarySubjectKind, Subject}` |

**C432 — um achado, não uma contribuição.** `StageInvariance`
(`DivineImmutability.lean:86`) e `Atemporal` (`NecessityEternity.lean:92`) desenrolam
para a **mesma** proposição, `∀ t₁ t₂, ExistsAtTime t₁ e ↔ ExistsAtTime t₂ e`. O corpus
tem, portanto, dois nomes para o segundo campo do mestre da imutabilidade. Isto importa
para ler §8: a "atemporalidade" e esse campo **não são dois passos, são um**. O que
realmente funciona é o contraste **unidimensional**, porque
`Everlasting e := ∀ t, ExistsAtTime t e` tem outra forma — é C436. A linha é `{}` quanto
ao teorema, mas a pegada auditada é `{NecessarySubjectKind, Subject}`: os predicados que
desenrolam não sãolivres de axiomas.

**C433 — a unicidade de §9 é corolário do mesmo lema que fechou F15.** Os três
construtores de `Entity` esgotam o caso:

* `ofAtom n` é C424 verbatim e não custa nada (`{}`): o primeiro campo entrega um mundo
  `w` onde `ExistsAt w (ofAtom n)`, que *é* `Satisfies w (Form.atom n)`
  definitionualmente, e entrega também a sua negação.
* `ofSubject s` é onde está o preço, e o preço **é F15**. O segundo campo
  `conditions_every_bearer` é universal na entidade condicionada, logo instanciá-lo em
  `ofGround` — que obtém em todo o lado e significa tudo — força
  `GroundsEntity (EntityOf s) ofGround`, isto é `∀ p, Means s p`.
  `SemanticFinitude` (`SemanticFinitude.lean:151`, o limite declarado `Tag: VOCAB`
  `∀ s, ∃ p, ¬ Means s p`) é exactamente a negação disso. **Uma ограниченная, duas
  características**: o mesmo limite que fechou a unicidade fundacional de F15 fecha
  agora a unicidade da precedência de §9.
* `ofGround` é o objectivo.

A ponte #9 da pessoa (`base.txt:1526`, `Ground(e, personal) → Personal(e)`, ledgerada
BLOCKED em C228) **não é usada e não é precisa**: a pessoahood é irrelevante para a
precedência aqui, e a linha foi deliberadamente escrita para ser provável sem ela.

**C434/C435 — a articulação, como separação e não como conjunção.** `Entity.ofAtom 0` é
stage-invariant (`EntityExistsAt (stageOf t) (ofAtom 0)` reduz a `(stageOf t) 0 = TV.t`,
isto é `0 ≤ t`, que se verifica em todos os estágios) e não é o fundamento. Logo as duas
precedências **diferem em poder discriminante**, e é isso que C435 enuncia: só
`PrecedesRightWrong` singulariza o fundamento; `StageInvariance` tem pelo menos duas
instâncias. `propext` entra por `simp` a reduzir `stageOf t 0` e é o próprio axiom
fundacional de Lean, não uma premissa.

**A confusão que estas duas linhas existem para impedir.** A maneira óbvia de
"articular" §9 contra §8 é conjuntar `PrecedesRightWrong Entity.ofGround` com
`StageInvariance Entity.ofGround`. Essa conjunção é uma re-instanciação de dois factos
já provados (C425 e `ofGround_stage_invariance`) e **não discrimina nada** — é
exactamente o defeito que `CapacityInvariance` carrega e que C321 já reporta como
vácuo. A separação é a forma honesta.

**C436–C438 — os dois sentidos da eternidade, e a vacacidade que é o ponto.** C436 é o
passo genérico (uma linha: o `↔` desfaz-se nas duas instâncias unidireccionais), e
estava ausente porque o módulo só tinha as instâncias ao nível do fundamento
(`the_ground_everlasting`, `the_ground_atemporal`), ambas por `ofGround_necessary`.
C437 é o contraexemplo discriminante; a segunda conjunção é `subject_not_everlasting` (o
mesmo módulo) e a primeira é nova, com uma razão que tem de ser declarada e não
suavizada: sob `ContingentSubjectKind s` a cláusula de existência reduz a
`stageOf t = actualWorld`, que é **falsa em todo** `t` (no índice `t+1` tem-se
`stageOf t (t+1) = TV.f` contra `actualWorld (t+1) = TV.t`). Ambos os lados do `↔` de
`Atemporal` são falsos, e `Atemporal` é satisfeita **vacuamente**. Essa vacacidade é o
ponto da linha, não um defeito: é exactamente assim que uma entidade pode ser
"atemporal" sem existir em todo o lado.

**O limite que C438 tem de declarar, e que o enunciado não pode deixar ler-se:** Γ
**não tem** nenhum teorema que habite `ContingentSubjectKind`. Todas as ocorrências no
corpo são hipóteses — `LovesAsGround.lean:196`, `CosmicExistence.lean:299` e seguintes,
com a linha do `Creates` em `CosmicExistence.lean:695` ainda BLOCKED numa relação
`Creates` que Γ não tem. A região separadora está habitada nos **modelos**, não no
**kernel**: o fecho prova que o vocabulário *distingue* as duas noções, **não** que
algum sujeito de Γ caia na diferença. O esquema incondicional
`¬ (Atemporal e → Everlasting e)` **não é derivável** e não é enunciado de propósito — o
fundamento é atemporal e perene, e `Entity.ofAtom 0` também.

#### O que este lote **não** fecha

* **Nada no `F10`–`F16`.** Cada uma dessas linhas está ou bloqueada por vocabulário novo
  (`Produces`, `EntityMeansAt`, `Code`/`Subst`/`Diag`/`Truth`) ou já **machine-refutada**
  como não-derivável (F11 C273/C274, F12 C299, F13 C294). Este lote não as toca, e
  re-provar o bloqueio delas seria mais fraco do que os contra-modelos que já existem.
* **As duas linhas sem gloss.** `DivineImmutability.necessity_and_atemporality_yield_immutability`
  e `FoundationalOmnipresence.omnipresence_from_universal_ground_and_aseity` continuam
  **provadas sem linha no ledger**, logo invisíveis ao leitor. Fora do âmbito aprovado
  deste lote; registado em `PLAN.md` como achado não acted on.
* **F15 por provação.** Continua `AXIOM` (C388). C433 *consome* o limite, não o
  substitui.

## Batch meaning-retorsion (2026-09-27) — a tese do "não há significado" refutada como resposta

O novo módulo `Logos/MeaningRetorsion.lean` (lote B de 2026-09-27) enuncia a tese do
§26 item 3 ("Não existe conteúdo") e do poema P3 ("há significado") no vocabulário
significativo da própria Γ (`Choice.Meaning_I`), escala-a em quatro degraus até a
retorsão incondicional, e refuta a família de contramodelos M1/C294 **como respostas**.
**Zero axiomas novos declarados**: tudo são teoremas sobre `def`s e linhas já existentes.

A distinção que o lote inteiro assenta é a que `NegativeRetorsionAudit.lean:292-295`
já registava — *"`NoI is false` NÃO é equivalente a `NoI is unassertable`"*:

| Claim | Secao | Declaracao | Status | Pegada |
|---|---|---|---|---|
| C368 | §26 item 3, `poem.txt` P3 | `MeaningRetorsion.NoMeaning : Prop` — a tese do "não há conteúdo" enunciada no vocabulário significativo da própria Γ, `¬ ∃ p, Meaning_I p`. **DEF, não axioma**: o que se ledgeriza é a *identificação* da tese com esta fórmula, não uma prova | PROVEN | `{Means, Subject}` |
| C369 | §26 item 3 | `MeaningRetorsion.noMeaning_iff_noIntentionalSubject : NoMeaning ↔ NoI_canonical` — a tese **é** a negação auditada, re-indexada: só trocam a ordem de dois quantificadores existenciais. Sem `propext` — e a ausência dele na pegada é a confirmação machine-checked de que a re-indexação não precisa de cast | PROVEN | `{Means, Subject}` |
| C370 | §26 item 3 | `MeaningRetorsion.noMeaning_iff_pointwise : NoMeaning ↔ ∀ s : Subject, ¬ ∃ p : Prop, Means s p` — a forma pontual: nenhum sujeito significa seja o que for | PROVEN | `{Means, Subject}` |
| C371 | §26 item 3 | `MeaningRetorsion.noMeaning_is_unmeaned (s : Subject) : NoMeaning → ¬ Means s NoMeaning` — **degrau 1/4**: a tese não pode ser *significada*. Consistente, não paradoxal: uma negativo universal não é um mentiroso | PROVEN | `{Means, Subject}` |
| C372 | §26 item 3 | `MeaningRetorsion.noMeaning_is_unperformed (s : Subject) : NoMeaning → ¬ Act s NoMeaning` — **degrau 2/4**: a tese não pode ser *actuada* | PROVEN | `{Initiates, Means, State, Subject}` |
| C373 | §26 item 3 | `MeaningRetorsion.no_correct_judgment_of_noMeaning (s : Subject) : ¬ Correct s NoMeaning` — **degrau 3/4 — NOVO**: não havia rung `Correct` para nenhuma tese de insignificância | PROVEN | `{Initiates, Means, State, Subject}` |
| C374 | §26 item 3 | `MeaningRetorsion.judgment_of_noMeaning_is_incorrect (s : Subject) (h : Correct s NoMeaning ∨ Incorrect s NoMeaning) : Incorrect s NoMeaning` — **3'/4, forma exaustiva**: quem julga a tese, julga-a incorretamente | PROVEN | `{Initiates, Means, State, Subject}` |
| C375 | §26 item 3 | `MeaningRetorsion.noMeaning_is_unassertable : ¬ ∃ s : Subject, Asserts s NoMeaning` — **degrau 4/4, A RETORSÃO, incondicional**: sem hipótese, sem sujeito, sem ponte, sem axiom novo. **Não é uma proibição de tipo**: a frase é bem-formada e o autor enuncia-a; o que fica excluído é uma afirmação *que resulte*. Ver o bullet "a afirmação é a ENTRADA" | PROVEN | `{Initiates, Means, State, Subject}` |
| C376 | §26 item 3 | `MeaningRetorsion.noMeaning_ladder` — os quatro degraus numa conjunção, o último incondicional | PROVEN | `{Initiates, Means, State, Subject}` |
| C377 | §26 item 3 | `MeaningRetorsion.affirms_noMeaning_yields_meaning : (∃ s, Act s NoMeaning) → ∃ p, Meaning_I p` — a frase do autor como **teorema positiva de existência**: a afirmação é a entrada que produz o significado. *Delta 2026-09-27:* a hipótese foi **generalizada** de `Asserts` para `Act` (`Asserts s p` é `Act s p ∧ p`, logo a forma antiga é o caso particular e esta subsume-a; o C-id não muda porque a proposição cresceu). *O preço, inalterado:* a hipótese continua indisponível por antecedência — C372 exclui `Act s NoMeaning` onde `NoMeaning` vale — logo a leitura é a do autor: quem performua a tese com significado refuta-a | PROVEN | `{Initiates, Means, State, Subject}` |
| C378 | `poem.txt` P3 | `MeaningRetorsion.judges_noMeaning_yields_meaning : (∃ s, Correct s NoMeaning) → ∃ p, Meaning_I p` — a forma que o P3 usa: "há certo e há errado → há significado" | PROVEN | `{Initiates, Means, State, Subject}` |
| C379 | §35 item 3 | `MeaningRetorsion.no_countermodel_can_affirm_the_thesis : ∀ S, S.NoI → ¬ ∃ s, S.Asserts s NoI` — **corolário** de `level2_signature_asserts_noi_selfRefutes` (`NegativeRetorsionAudit.lean:286`), generalizado de uma assinatura a todas; **não reivindica novidade**. O peso independente da refutação está em C381 (que usa `NoWeakActIn` e não é instanciação) e em C382 | PROVEN | `{}` |
| C380 | §35 item 3 | `MeaningRetorsion.signature_weak_retorsion (S) (s) : S.asserts s (NoWeakActIn S) → False` — **NOVO**: `Agency.noWeakAct_selfRefutes` (`:245`) é só canónico; aqui é a negação do dado-do-acto em assinatura arbitrária. `NoWeakActIn` (def, sem claim) é o que separa M1 de um `Means`-vocabulário qualquer, e a sua negação é o que M1 satisfaz | PROVEN | `{}` |
| C381 | §35 item 3 | `MeaningRetorsion.the_two_denials_cannot_both_be_affirmed : ∀ S, S.NoI → NoWeakActIn S → ¬ ∃ s, S.asserts s NoWeakActIn S` — **a refutação conjunta, numa frase**: a tese e a negação do dado-do-acto não podem ser ambas afirmadas | PROVEN | `{}` |
| C382 | §35 item 3 | `MeaningRetorsion.the_meaningless_world_remains_a_model : ∃ S, (∃ _s, True) ∧ S.NoI ∧ (∀ s, ¬ S.Asserts s NoI)` — **o complemento populado**: mundo com sujeito (`Unit`, contra o sort vazio de M0 em `NegativeRetorsionAudit.lean:296`) onde a tese é verdadeira e nenhuma afirmação dela tem êxito. **É a razão machine-checked de que `¬ NoMeaning` NÃO é derivável *do vocabulário nu*** — de uma assinatura livre, sem as pontes de Γ. *Em Γ*, a tese **é** refutada: C401 (na ponte da pluralidade, incondicional) e C402 (no dado-do-acto, condicional). O que sobrevive de C382 é a consistência-da-forma, não a possibilidade-para-a-teoria | COUNTERMODEL | `{}` |
| C383 | §35 item 3 | `MeaningRetorsion.countermodel_is_a_world_where_the_thesis_is_unutterable` — as duas metades em conjunto: o complemento populado (C382) e a retorsão assinatura-a-assinatura (C379). *Sobre o nome:* "unutterable" **não** é proibição de tipo — a frase é bem-formada e o autor enuncia-a; o excluído é o **sucesso** da afirmação. C385 é a meia-positiva que o torna mau nome, e não má leitura | PROVEN | `{}` |
| C384 | §26 item 3 | `MeaningRetorsion.Voices (s : Subject) (p : Prop) : Prop := act s p` — **a performance sem a condição de sucesso**: o "pode ser dito, pode ser afirmado" do autor, e o predicado que Γ não tinha, porque todos os `asserts` do corpus trazem `∧ p` (`asserts s p := act s p ∧ p`, `Asserts s p := Act s p ∧ p`, `Correct s p := A s p ∧ T p`) — logo a palavra *afirmar* passara a significar *afirmar correctamente*. Construída sobre o `act` fraco, não sobre `Act`: `Act` exige `Means` e C372 já exclui `Act s NoMeaning` onde `NoMeaning` vale, portanto uma afirmação construída sobre `Act` nunca poderia testemunhar a tese a ser dita | PROVEN | `{Subject, act}` |
| C385 | §26 item 3 | `MeaningRetorsion.the_thesis_is_utterable_though_not_assertable : ∃ S, (∃ _s, True) ∧ S.NoI ∧ (∃ s, S.act s S.NoI) ∧ (∀ s, ¬ S.Asserts s S.NoI)` — **o mundo em que a tese é dita**: o mundo de C382 com `act := True` em vez de `False`; a terceira conjuncta é C379 aplicada a ele. É o que torna "unutterable" (C383) mau nome e não má leitura: a frase é bem-formada, o autor enuncia-a, e o act performado é fraco — `Act` exigiria `Means`, e num mundo onde a tese é verdadeira o único acto disponível dela é o fraco. A mesma instância desfaz o contramodelo de C294 como RESPOSTA (lifting trivial: `Means := M`, `act := True`). *Nota (2026-09-27, corrigida):* este ficheiro registava antes a impossibilidade de identificar um orador com um `Subject` como *limite registado* à espera de um 27.º axiom. **Essa moldura estava errada e é retirada.** `Voices` e `Act` quantificam sobre todos os sujeitos, portanto **quem quer que faça a performance da tese refuta-a ao fazê-la** — a contradição performativa é independente de quem fala, e nenhum axiom precisa de dizer que um orador em linguagem natural é um `Subject` para a retorsão correr. `Subject` continua a ser um sort não interpretado, e `()` a testemunha, pelo que Γ também não consegue *nomear* qual é o sujeito do modelo; nada na retorsão precisa que o nomeie | COUNTERMODEL | `{}` |
| C401 | §26 item 3 | `MeaningRetorsion.noMeaning_is_refuted_from_plurality : ¬ NoMeaning` — **a REFUTAÇÃO: o mundo-sem-significado não é possível em Γ**. `Meaning_I p` é por definição `∃ s, Means s p`, logo um sujeito que significa algo já é um contra-exemplo à tese, e `cogito_from_T12` exibe um sem hipótese. Três linhas, nunca escritas até agora. **Isto não é axiom-free** — nada no vocabulário nu refuta a tese, e C382 *é* a prova machine-checked disso. O que C382 exibe é uma assinatura livre satisfazendo o seu próprio `NoI`, proposição diferente sobre sort diferente; é consistente *como assinatura* e continua a sê-lo, estatuto COUNTERMODEL e gate B4 intactos. O que esta linha mostra é que a tese não sobrevive *à teoria*: dada a ponte da pluralidade, Γ refuta-a directamente. Companheira, não substituta, das Secções 1–3d | PROVEN↑ | `{AxTwoSubjects, Means, Subject, Will, subjectWill}` |
| C402 | §26 item 3 | `MeaningRetorsion.noMeaning_is_refuted_from_the_act_datum (h : ∃ s, ∃ p, Act s p) : ¬ NoMeaning` — **a mesma refutação no dado-do-acto, sem ponte META**: `act_datum_implies_means` converte "alguém agiu" directamente em testemunha de significado, porque `Act` já traz `Means`. O gémeo God-lane de C401 — C401 é incondicional na ponte da pluralidade, esta linha é condicional no dado performativo e livre de pontes, preço relocado para ◈ `performativeActDatum` (`Tag: TRANS`): livre em axiomas, não livre em performance. A hipótese é anónima, pelo que o registo ◈ é o *único* sinal da dependência | PROVEN | `{Initiates, Means, State, Subject}` |
| C386 | §35 | `CosmicExistence.cosmos_presence_model_of_the_act_datum (h : ∃ s : Subject, ContingentSubjectKind s ∧ ∃ p : Prop, Logos.Agency.Act s p) : CreatedRealm` — **a GOD-LANE, primeira metade**: o mesmo inhabitation de C367 com o preço movido do `Tag: META` `AxTwoSubjects` para o dado performativo do acto ◈ `performativeActDatum` (`Tag: TRANS`, registado 2026-09-27, registry 6 → 7). `Logos.Agency.act_datum_implies_means` dá a testemunha sem ponte nenhuma, porque `Act` já traz `Means` como conjuncta. **Não é uma reancoragem de C367** e não a substitui: um teorema *descobre*, não fabrica, e Γ não fornece um sujeito do nada — o dado é *dado*, como `Agency.lean:4` diz ("*given*, not inferred"). Reancorar `cosmos_obtains` seria repetir exactamente o bug de A1 ("consequência da pluralidade — o datum que deve preceder-la"), que foi apanhado e revertido. **O que a linha afirma é falsificável nos dois sentidos:** rejeite a ponte e C367 cai, esta linha fica | PROVEN | `{Initiates, Means, NecessarySubjectKind, State, Subject, propext}` |
| C387 | §35 | `CosmicExistence.the_ground_loves_the_cosmos_from_the_act_datum (h : ∃ s : Subject, ContingentSubjectKind s ∧ ∃ p : Prop, Logos.Agency.Act s p) : ∃ t, ContingentEntity t ∧ (∃ q, EntityMeans t q) ∧ ∃ p, GroundBearsGood Entity.ofGround t p` — **a GOD-LANE, o pagamento**: a conclusão de C351 com enunciado *byte-idêntico* e sem a rota da pluralidade. Medido: C351 é `{AxGroundLovesContingentRealm, AxTwoSubjects, GroundBearsGood, Means, Subject, Will, propext, subjectWill}` e esta linha é `{AxGroundLovesContingentRealm, GroundBearsGood, Initiates, Means, State, Subject, propext}` — **três axiomas e um sort a menos** (`AxTwoSubjects`, e com ele o `Will`/`subjectWill` que só entravam por aí). Restam a ponte do amor e a relação `GroundBearsGood`, e têm de restar: um bem direccional detido pelo fundamento não é exprimível no vocabulário de fundamentação de Γ, que só chega à suficiência não dirigida. **A metafísica interpessoal deixa de ser premissa do amor do fundamento** — e as duas premissas restantes são independentes dela, pelo que a remoção é *visível* e não absorvida. Preço relocado para ◈ `performativeActDatum`: livre em axiomas, não livre em performance | PROVEN↑ | `{AxGroundLovesContingentRealm, GroundBearsGood, Initiates, Means, NecessarySubjectKind, State, Subject, propext}` |

- **O contramodelo não é refutado como modelo; é refutado como RESPOSTA.** M1 e C294 são
  instâncias de uma só família — *um vocabulário significativo em que nada é significado*
  — e ambos Recusam também o dado-do-acto (`act := fun _ _ => False`). Uma resposta é um
  movimento feito dentro do discurso; um mundo sem movimentos não tem respostas, logo não
  pode conter a afirmação do seu próprio silêncio. As duas classes de modèle não se
  confundem: `NoWeakActIn` é precisamente o que separa M1 de um `Means`-vocabulário
  qualquer, e é a sua negação que M1 satisfaz.
- **A afirmação é a ENTRADA da refutação, não a sua saída.** `noMeaning_is_unassertable`
  (C375) é incondicional e não custa axiom nenhum, mas a contradição só se produz quando
  a afirmação é fornecida. A retorsão é **livre em axiomas e não livre em performance** —
  é essa a forma honesta da frase do autor, e é o preço que o gate B5 manda escrever.
- **O que este lote NÃO entrega:** `¬ NoMeaning`. `the_meaningless_world_remains_a_model`
  (C382) é a razão machine-checked: um mundo **populado** (sujeito `Unit`, ao contrário
  de M0, o sort vazio de `unassertability_does_not_imply_falsity` `:296`) onde a tese é
  verdadeira e ninguém pode afirmá-la. A afirmação só se paga quando é dado de entrada; um
  mundo onde ninguém afirma nada não tem o que a refute. O conteúdo fica vivo; a
  afirmação não sobrevive.
- **O preço é zero e é verificado, não afirmado** (gate B2): nenhuma das 17 declarações
  carrega `AxTwoSubjects` nem `transcendental_reflection_intentional`. Por isso o
  `AxTwoSubjects` (C367) continua a ser o preço da **existência** positiva de significado;
  o que este lote mostra é que ele é desnecessário sempre que a afirmação é dada.
- **Leitura para o leitor, verbatim:** a tese do "não há significado" não é um erro
  *lógico* (é consistente); é um erro *performativo* — um conteúdo que ninguém pode
  ter por correto não é uma posição, é a descrição de um mundo em que nada é nunca
  tenido.

## Batch semantic-finitude (2026-09-27) — F15 consolidated, the bound now ◈-stipulated

The per-subject meaning bound `∀ s, ∃ p, ¬ Means s p` (F15) is now a **stipulated**
sentence, registered in `Stipulations.lean` as ◈ `semanticFinitude` (`Tag: VOCAB`),
and the ten headline theorems that were conditional on an anonymous copy of it are keyed
to the named bound in the new module `Logos/SemanticFinitude.lean`. On 2026-09-28 (lote SEMANTIC-FINITUDE-PROMOTION) the bound was **promoted from
`def` to a declared `axiom`, `Tag: VOCAB`** — it is the 27th declared axiom. This is a
change of *provenance*, not of status: the ten results below were `PROVEN` before and are
`PROVEN` after, and no claim was added, demoted or withdrawn. The reason for the promotion
is stated in `SemanticFinitude.lean`: as a `def` of a `Prop` taken as a premise, the bound
was **invisible to every footprint tool** — `#print axioms` reported the same footprint as
the pre-existing conditional theorem and the declared-axiom count was unmoved, so a ◈ badge
was the only signal that anything had been paid. As a declared axiom the price appears in
every dependent footprint and the count moved 26 → 27. The ten theorems are now
**unconditional theorems of Γ** rather than corollaries of a hypothesis; their
`_stipulated` suffix is historical and kept because the ledger and the prose corpus cite
these names.

| C-id | Decl (`Logos.SemanticFinitude`) | Pegada (auditada) | Classe |
|---|---|---|---|
| C388 | `SemanticFinitude` (axiom, `Tag: VOCAB`) | `{Means, SemanticFinitude, Subject}` | AXIOM (27th axiom, VOCAB — the declared bound) |
| C389 | `exactly_one_universal_modal_ground_stipulated` | `{Means, NecessarySubjectKind, SemanticFinitude, Subject}` | PROVEN (unicity of the ground; unconditional) |
| C390 | `ofGround_sole_universal_grounding_stipulated` | `{Means, NecessarySubjectKind, SemanticFinitude, Subject}` | PROVEN |
| C391 | `conditional_canonical_aseity_stipulated` | `{Means, SemanticFinitude, Subject}` | PROVEN |
| C392 | `ofGround_modal_aseity_conditional_stipulated` | `{Means, NecessarySubjectKind, SemanticFinitude, Subject}` | PROVEN |
| C393 | `ofGround_divine_pure_actuality_stipulated` | `{Initiates, Means, NecessarySubjectKind, SemanticFinitude, State, Subject}` | PROVEN |
| C394 | `ofGround_no_grounding_potency_stipulated` | `{Means, SemanticFinitude, Subject}` | PROVEN |
| C395 | `ofGround_divine_simplicity_stipulated` | `{Means, SemanticFinitude, Subject, propext}` | PROVEN |
| C396 | `ofGround_non_composite_stipulated` | `{Means, SemanticFinitude, Subject, propext}` | PROVEN |
| C397 | `ofGround_simplicity_and_transcendence_stipulated` | `{Means, SemanticFinitude, Subject, propext}` | PROVEN |
| C398 | `ground_is_canonically_aseitous_but_not_asietic_stipulated` | `{Means, SemanticFinitude, Subject}` | PROVEN |
| C399 | `semantic_omnipotence_is_consistent` | `{}` | COUNTERMODEL (the bound is falsifiable) |
| C400 | `semanticFinitude_excludes_ground_from_subjects` | `{Means, SemanticFinitude, Subject}` | PROVEN (the bound is load-bearing) |

**C-ids atribuídos 2026-09-27 (C388–C400), por instrução do autor.** As pegadas `{CL}`
das linhas de simplicidade foram corrigidas para `{propext}` na mesma passagem — o
auditado é `propext` (lógica clássica de Lean, não um axiom substantivo), e pegadas são
derivadas, nunca transcritas. **Pegadas atualizadas 2026-09-28** na promoção: todas as
linhas acima passam a listar `SemanticFinitude`, e cinco delas passam a listar
`NecessarySubjectKind` — a unicity route usa a kind-modal bridge do lote
TWO-KINDS, não a premissa anónima. `NecessarySubjectKind` é ela própria um axioma
declarado `VOCAB`; ver C403. O registo `◈ semanticFinitude` foi **removido** de
`Stipulations.lean` (8 → 7), porque uma premissa com carga suficiente para precisar de
distintivo deve ser um `axiom`, não um `def`.

- **F15 retira** (o registo do lema-em-falta é substituído por este ponteiro ◈). A contagem
  de chamadores do próprio F15 ("20 vezes, 5 ficheiros, `DivinePureActuality` 5") fica
  superada por um censo fresco: 17 premissas + 2 campos de estrutura = 19 ocorrências em
  5 ficheiros, `DivinePureActuality` 4 (não 5).
- **O preço é invisível a `#print axioms`** (a premissa não é um axioma); o ◈ no registo
  (agora **6** stipulações) e a cadeia do gerador `SEMANTIC_FINITUDE_STEPS` são os
  únicos sinais. "A contagem de axiomas não se mexeu" **não** é um teste para este lote.
- **O limite é falsificável, não vácuo**: `semantic_omnipotence_is_consistent` (`{}`)
  é um modelo da sua negação (um portador semanticamente omnipotente), e
  `semanticFinitude_excludes_ground_from_subjects` mostra o limite a fazer trabalho real
  (`ofGround_meansAll` dá ao fundamento *toda* proposição, logo o limite é o que o mantém
  fora do sort `Subject`).
- **Os dez teoremas condicionais pré-existentes NÃO são editados** (mantêm a premissa
  anónima); os corolários `_stipulated` são aditivos. A existência de um fundamento já era
  `PROVEN` incondicionalmente (C319); o que é ◈ aqui é a sua *unicidade*. Pessoalidade
  (C228), Trindade (F6/F8) e fundamentação *explicativa* (C326/C328) ficam intocados.
- Decisões em aberto (autor): **resolvido 2026-09-27 para o bloco de C-ids — C388–C400
  abaixo**; o Ledger desta nota lê os C-ids. O `Tag:` fica (VOCAB justificado;
  alternativa SEM documentada; o autor mandou calar, não re-mexer).

| C388 | §28 Unicity | `SemanticFinitude.SemanticFinitude : Prop := ∀ s : Subject, ∃ p : Prop, ¬ Means s p` — **o limite F15, nomeado e declarado**: nenhum sujeito significa toda a proposição; nenhuma criatura é semanticamente omnipotente. Uma frase sobre o vocabulário existente, já paga 17 vezes como premissa anónima, **promovida a axioma declarado `Tag: VOCAB` em 2026-09-28** (o 27º). Não é ponte META e não declara conexão entre entidades — é o mesmo estatuto que `ofGround_existsAt`; a promoção torna o preço visível, não maior | AXIOM | `{Means, SemanticFinitude, Subject}` |
| C389 | §28 Unicity | `SemanticFinitude.exactly_one_universal_modal_ground_stipulated` — **a unicidade do fundamento de toda a realidade**, assente no limite nomeado em vez da premissa anónima. A existência já era `PROVEN` (C319); o que assenta no limite é a *unicidade*. Teorema **incondicional** desde a promoção: já não carrega `hf` | PROVEN | `{Means, NecessarySubjectKind, SemanticFinitude, Subject}` |
| C390 | §28 Unicity | `SemanticFinitude.ofGround_sole_universal_grounding_stipulated` — a fundamentação universal exclusiva do fundamento, no limite nomeado (incondicional) | PROVEN | `{Means, NecessarySubjectKind, SemanticFinitude, Subject}` |
| C391 | §28 Unicity | `SemanticFinitude.conditional_canonical_aseity_stipulated` — a asseidade canónica condicional do fundamento, no limite nomeado (incondicional) | PROVEN | `{Means, SemanticFinitude, Subject}` |
| C392 | §28 Unicity | `SemanticFinitude.ofGround_modal_aseity_conditional_stipulated` — a asseidade modal do fundamento quanto a `CanonicalExtDepAt`, no limite nomeado (incondicional) | PROVEN | `{Means, NecessarySubjectKind, SemanticFinitude, Subject}` |
| C393 | §28 Unicity | `SemanticFinitude.ofGround_divine_pure_actuality_stipulated` — **a actualidade pura divina** (actus purus) do fundamento, no limite nomeado (incondicional) | PROVEN | `{Initiates, Means, NecessarySubjectKind, SemanticFinitude, State, Subject}` |
| C394 | §28 Unicity | `SemanticFinitude.ofGround_no_grounding_potency_stipulated` — zero potência passiva de fundamentação no fundamento, no limite nomeado (incondicional) | PROVEN | `{Means, SemanticFinitude, Subject}` |
| C395 | §28 Unicity | `SemanticFinitude.ofGround_divine_simplicity_stipulated` — **a simplicidade divina** do fundamento, no limite nomeado (incondicional) | PROVEN | `{Means, SemanticFinitude, Subject, propext}` |
| C396 | §28 Unicity | `SemanticFinitude.ofGround_non_composite_stipulated` — a não-composição mereológica do fundamento, no limite nomeado (incondicional) | PROVEN | `{Means, SemanticFinitude, Subject, propext}` |
| C397 | §28 Unicity | `SemanticFinitude.ofGround_simplicity_and_transcendence_stipulated` — simplicidade divina **e** transcendência ontológica do fundamento, no limite nomeado (incondicional) | PROVEN | `{Means, SemanticFinitude, Subject, propext}` |
| C398 | §28 Unicity | `SemanticFinitude.ground_is_canonically_aseitous_but_not_asietic_stipulated` — canonicamente asseitício mas não ele próprio assiético: a asseidade canónica vale do fundamento, a assiidade não | PROVEN | `{Means, SemanticFinitude, Subject}` |
| C399 | §28 Unicity | `SemanticFinitude.semantic_omnipotence_is_consistent` — **o limite é falsificável, não vácuo**: um portador semanticamente omnipotente (`S := Unit`, `M := True`) é modelo da sua negação, pelo que a unicidade assenta mesmo nele e tem de ser declarado axiom, não assumido | COUNTERMODEL | `{}` |
| C400 | §28 Unicity | `SemanticFinitude.semanticFinitude_excludes_ground_from_subjects` — **o limite a fazer trabalho real**: `ofGround_meansAll` dá ao fundamento *toda* a proposição, logo é o limite que o mantém fora do sort `Subject` — encadeado *através* do limite de propósito, para a dependência ficar visível em vez de escondida atrás de C315. Nota de construção: `hf` foi removido desta linha em 2026-09-28; a dependência passou a ser direta e o auditado passou a listar `SemanticFinitude` | PROVEN | `{Means, SemanticFinitude, Subject}` |

## Batch committed-choice (2026-09-24) — Escolha Comprometida / "committing to one"

O glossado "apreender alternativas incompatíveis **e comprometer-se com uma**" ganhou
denotado formal. `Chooses` é só o núcleo cognitivo (co-significação); o comprometimento
é carregado pela postura judicativa `ClaimsNormativeCorrectness`, cujo feixe é definido
como `CommittedChoice s p q r := Act s p ∧ Chooses s q r` (novo §5b de
`formal/Logos/NormativeOrder.lean`). Nada muda em cadeia: `CommittedChoice` ⇒ `Chooses`
⇒ `FreeWill` ⇒ `Person`; a estrutura `GroundsRightWrong.agential_foundation` permanece
`∃ p q, Chooses s p q`. Ver `CHOICE.md`.

Pegadas `#print axioms` verificadas no build:

| Decl (Logos.NormativeOrder §5b) | Pegada | Classe |
|---|---|---|
| `committedChoice_implies_chooses`/`_act`/`_freeWill`/`_freeSubject` | `{Initiates, Means, State, Subject}` | PROVEN (VOCAB) |
| `claims_normative_correctness_implies_committed_choice` | `{Initiates, Means, State, Subject, CL}` | PROVEN |
| `claims_normative_correctness_derives_committed_free_will` | `{Initiates, Means, State, Subject, CL}` | PROVEN |
| `committed_choice_exists_of_stance` | `{Initiates, Means, State, Subject, CL}` | PROVEN |

- `CommittedChoice` é DEFINITIONAL; as pegadas `{Initiates, Means, State, Subject}` das
  deduções são o custo VOCAB de mencionar `Act`/`Chooses`/`FreeWill`.
- O teorema-mestre da postura mantém ZERO axiomas substantivos — mesmo `CL` do resto do
  §4/§5 de `NormativeOrder`. Apresentação sincronizada: nó `choice` do spine +
  supporting-defense "Committed Choice — the stance carries settlement (2026-09-24)";
  prosa em base.txt §15/"Aprofundamento"; docs em `CHOICE.md` e GOAL.md §"choice audit".

## Batch fundamento-necessário (2026-09-24) — Necessidade e Eternidade do Fundamento

Extensão do sort canónico `Logos.Entity.Entity` com o construtor **`Entity.ofGround`**
(entidade mundo-rígida: `EntityExistsAt w .ofGround := True`; as duas correspondências
`EntityMeans .ofGround p := True` em `RecoveredOntologicalGround` (~L45) e
`NecessaryPersonalGround` (~L150) + docstrings). Novo módulo
`formal/Logos/NecessityEternity.lean` (namespace `Logos.NecessityEternity`; importado
no barrel 2026-09-24) com a camada temporal de estágios Nat (`Time := Nat`,
`stageOf t m := if m ≤ t then TV.t else TV.f`, `ExistsAtTime`, `Everlasting`,
`Atemporal e := ∀ t₁ t₂, ExistsAtTime t₁ e ↔ ExistsAtTime t₂ e`,
`HasTemporalMode e := ¬ Atemporal e`, `NotInSuccession`)
e os teoremas abaixo. C181 acrescenta um transporte modal genérico: existência
necessária implica presença e equivalência em todos os estágios, mas não instancia
o sort canónico `Entity` nem prova eternidade metafísica.

Pegadas `#print axioms` verificadas no build (0 axiomas substantivos; `CL` ausente):

| Decl (Logos.NecessityEternity) | Pegada | Classe |
|---|---|---|
| `ofGround_necessary` | `{Subject}` | PROVEN (VOCAB) |
| `ofGround_ground_of_reality` | `{Means, Subject}` | PROVEN (VOCAB) |
| `ofGround_necessary_ground_of_reality` | `{Means, Subject}` | PROVEN (VOCAB) |
| `ofGround_ne_ofSubject` | `{Subject}` | PROVEN (VOCAB) |
| `necessary_implies_everlasting` | `{Subject}` | PROVEN (VOCAB) |
| `necessary_implies_atemporal` | `{Subject}` | PROVEN (VOCAB) |
| `the_ground_everlasting` | `{Subject}` | PROVEN (VOCAB) |
| `the_ground_atemporal` | `{Subject}` | PROVEN (VOCAB) |
| `the_ground_not_in_succession` | `{Initiates, State, Subject}` | PROVEN (VOCAB) |
| `everlasting_and_atemporal_ground` | `{Subject}` | PROVEN (VOCAB) |
| `atom_has_temporal_mode` | `{Subject}` | PROVEN (VOCAB) |
| `atom_not_everlasting` | `{Subject}` | PROVEN (VOCAB) |
| `atom_not_atemporal` | `{Subject}` | PROVEN (VOCAB) |
| `necessary_existence_is_stage_uniform` | `{}` | PROVEN (lógica modal genérica) |
| `subject_not_everlasting` | `{Subject}` | PROVEN (VOCAB) |
| `everlasting_but_contingent` | `{Subject}` | PROVEN (VOCAB) |
| `the_personal_type_grounding` | `{AxTwoSubjects, Means, Subject, Will, subjectWill}` | PROVEN↑ (META) |
| `claimE` | `{AxTwoSubjects, Means, Subject, Will, subjectWill}` | PROVEN↑ (META) |

Notas:
- O `{Subject}` Vocab nos teoremas "{}"-esperados é o custo de *mencionar* o tipo
  `Entity` (o construtor `ofSubject` referencia a sort-axioma `Agency.Subject`) —
  mesma convenção de `Modal.subject_nec_entity_nec` (C91). Zero axiomas substantivos.
- C181 (`necessary_existence_is_stage_uniform`) é uma codificação independente do
  tipo: recebe `ExistsAt`, `At` e `stage` como parâmetros, tem pegada `{}` e só
  transporta a necessidade mundial para estágios. Não elimina a pegada `{Subject}`
  dos corolários canónicos de `Entity.ofGround`, nem transforma esse transporte em
  uma prova de eternidade metafísica.
- A obstrução pré-extension `¬ ∃ e, NecessaryEntity e` (C-set "no necessary entity",
  GOAL.md §2.2) **deixa de ser teorema** do sort estendido: `NecessaryEntity
  Entity.ofGround` é uma estipulação semântica definicional (VOCAB), não um axioma.
- Estipulação mundial do construtor rígido (§4.2): `EntityExistsAt w Entity.ofGround := True`
  (`Entity.lean:53-56`) e `EntityMeans .ofGround p := True`
  (`RecoveredOntologicalGround.lean:46`) são ESTIPULAÇÕES definicionais do construtor
  de mundo-rígido (`Entity.lean:23-26`) — distinguem *o modelo tem um fundamento
  necessário* de *o argumento acarreta um fundamento ontológico necessário*.
- A Proposição E (nível-ente) passou de "anotada, nunca teorema" a teorema vivo como
  **par não-hipostático** (`∃ g s, NecessaryEntity g ∧ NecessaryGroundOfReality g ∧
  Person s ∧ GroundsRightWrong s`); o conjuncto pessoal carrega honestamente a ponte
  META `AxTwoSubjects` (via `T5_personExists_from_plurality`) mais o vocabulário da
  vontade e a lei `will_individuation` (via `Person := ThomisticPersonCore`, emenda
  2026-09-25: a redução a livre-arbítrio é o teorema com preço `freeWill_implies_person`) → `PROVEN↑`. A âncora
  da linha README é `ofGround_necessary_ground_of_reality` (`{Means, Subject}`, PROVEN).
- Identidade hipostática bloqueada: `ofGround_ne_ofSubject` (`Entity.noConfusion`).
- Guarda de nomes honrada: nenhuma declaração nova contém o fragmento `eternal`
  (`everlasting`/`atemporal`; `Love.T14_eternalRelation_conditional` permanece a única
  exceção permitida).
- Fronteiras honestas registadas em base.txt §28: Claim D ("sujeito necessário")
  continua refutado (`CountermodelPersonNotNecessary`); teologia forte da eternidade
  divina além da rigidez de estágios não é reivindicada.

## Batch retire-ConstitutiveNormativeBridge (2026-09-23) — Opção A: remoção de código morto

`Logos.DirectNormativeRetorsion.ConstitutiveNormativeBridge` (estrutura) e os seus
dois teoremas-consumidores — `normative_right_to_free_will`,
`master_retorsion_to_free_will` — foram **retirados**.

Justificação (medida, não estética): a ponte nunca foi instanciada em lado algum
(não existe `ConstitutiveNormativeBridge.mk`), nenhum outro módulo a referenciava,
o corpus em prosa tinha zero referências, e nenhuma rota do ledger dependia dela.
A rota que ela foi escrita para fornecer (`NormativeRightExists → GenuineNormativity
→ Chooses → FreeWill`) já é carregada pela cadeia **C140/C141**:
`Logos.NormativeOrder.claims_normative_correctness_derives_free_will` (pegada
`{Initiates, Means, State, Subject, CL}`, zero axiomas substantivos) e
`Logos.RetorsiveNormativity.normative_retorsion_derives_free_will`. O único
consumidor a jusante do módulo, `PersonalGroundOfReality` (C149
`the_person_supports_the_reality_of_right`), compõe apenas a retorsão diagonal da
Secção 1 (`NoRight` + `cannot_claim_correct_no_right_and_true`, C102–C105) — não a ponte.

Mudanças: docstring do módulo reescrita (item 3); a `structure` foi apagada; os
dois teoremas-consumidores e as suas linhas `#print axioms` foram apagados;
imports/«opens» órfãos podados (o módulo deixou de importar `Logos.Choice`,
`Logos.Alternatives`, `Logos.IndubitableNormativeFreeWill`, `Logos.Core`,
`Logos.Necessity`, `Logos.Semantics`). C102–C105 intactos; inventário de axiomas
inalterado (a ponte era uma `structure`, nunca um axioma). README regenerado.

## Batch lift-necessário (2026-09-18) — ∃e □Exists(e) via esse est agere

The roadmap step #4/#5 (subject necessity → entity necessity) is executed:

- **C91** `Modal.subject_nec_entity_nec` (plus `_iff` and
  `necessary_entity_exists_of_necessary_subject`): `NecessarySubject s →
  NecessaryEntity (EntityOf s)` is **definitional** — `ExistsAt` is one shared
  relation and `Plurality.EntityOf` is the entity embedding, so both sides
  unfold to `∀ w, ExistsAt w (EntityOf s)`. Footprint `{Subject}` (VOCAB only,
  no SEM/META). The transfer is NOT a logical law: `not_holds_of_arbitrary_signature`
  and `subject_necessity_not_entails_entity_necessity`
  (HostileSemantics, `{}`) show a subject can persist in every world while its
  entity-correlate exists in only one.
- **C92** `Love.necessary_entity_exists_conditional : ∃ e, NecessaryEntity e` — **DEFERRED**
  (theorem removed from kernel, commit ae7f4bd "remove a lot of garbage"
  2026-09-23; the former `Love.necessary_entity_exists` declaration exists
  nowhere in the live kernel). Retained as annotated conditional surface only:
  from the demonstrated person (`T5_personExists`, C24) and persistence
  (`AxPersonStability`, esse est agere) with the C91 lift. It does **NOT**
  close T7 — the uniform ground of a necessary truth stays
  `AxGlobalGround`-priced (C18). Prose base.txt
  §26/§27/§28/§29 and theorems/T7.txt (Passo A) updated accordingly.
- Still requires proof (recorded literally in base.txt §28 and rendered in the
  generated README "## Formal Frontiers" appendix + OPEN_BRIDGES): an independent
  bridge `NecessaryEntity e → ∃τ, Ground e τ` (step #7, without AxGlobalGround)
  and `Ground(e, personal) → Personal(e)` (step #9, without AxPersonalGround).
  **#9 is now a numbered ledger row**: C228
  (`PersonalNormativeGround.normative_ground_is_personal`) is BLOCKED, with the
  missing lemma named verbatim and the two sealing fields `explanatory` and
  `asymmetric` named as the blockers (decision D1′, deferred, not executed).

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
  C77/C92: teoremas removidos do kernel (ae7f4bd), demovidos para DEFERRED;
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
`Person s` yields `∃ p, Means s p` (via the rational conjunct `RationalNature.1`,
i.e. `Intentional`; kind-preds `:= True`; `A := Means`) — historically an
unfolding, but since the 2026-09-25 cut it is an **entailment** out of the second
conjunct of `ThomisticPersonCore`, not a definition (`Person` is now the
three-conjunct criterion, C163) — so `AxPersonStability : ∀ s, Person s →
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
| C183 | T3/§28 | `Core.rightWrong_nonempty_and_nonconflating` — bundles the explicit truth/falsity witnesses and nonconflation result | PROVEN | `{}` (E0; bundles C8/C9) |
| C10 | §22 | `excludedMiddle : ∀ p, T (p ∨ ¬ p)` | PROVEN | `CL` |
| C11 | §23 | `nonContradiction : ∀ p, T (¬ (p ∧ ¬ p))` | PROVEN | `{}` (E0) |
| C12 | §10 | `bivalence : ∀ p, T p ∨ IsFalse p` | PROVEN | `CL` |
| C102 | §1/§4 | `DirectNormativeRetorsion.NoRight : Prop` — universal skeptical thesis that no genuine normative correctness judgment exists | PROVEN | `{Initiates, Means, State, Subject}` |
| C103 | §1/§4 | `DirectNormativeRetorsion.claims_correct_no_right_self_refuting : ClaimsCorrect s NoRight → NoRight → False` — claiming NoRight as correct while true yields a contradiction | PROVEN | `{Initiates, Means, State, Subject}` |
| C104 | §1/§4 | `DirectNormativeRetorsion.cannot_claim_correct_no_right_and_true : ¬ ∃ s, ClaimsCorrect s NoRight ∧ NoRight` — unassertability of the skeptical thesis | PROVEN | `{Initiates, Means, State, Subject}` |
| C105 | §1/§4 | `DirectNormativeRetorsion.performative_normative_denial_establishes_normative_right : (∃ s, ClaimsCorrect s NoRight) → ¬ NoRight` — performative denial establishes normative right | PROVEN | `{Initiates, Means, State, Subject}` |
| C179 | §1/§4 | `DirectNormativeRetorsion.no_correct_claim_of_no_right_can_be_true : SigClaimsCorrect sig s (SigNoRight sig) → ¬ SigNoRight sig` — local interpreted-signature corollary: a normative denial cannot be both claimed correct and true | PROVEN | `{}` (pure logic; local retorsion) |

Founding definitions of Level 0 (E0, 2026-09-15): `def T (p : Prop) : Prop := p`
(the D2 consistency model made definitional); `tschema` is a theorem
(`Iff.rfl`), no longer an axiom. The §4–§6 self-refutation core is
axiom-free: its negation-free content rests on classical logic only.

## Level 1 — semantics (`Logos.Semantics`, `Logos.Entity`, `Logos.Modal`, `Logos.NecessityEternity`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C13 | §22 | `Semantics.lawExcludedMiddle` | PROVEN | `CL` |
| C14 | §23 | `Semantics.nonContradiction` | PROVEN | `CL` |
| C16 | §22 | `Entity.lawExcludedMiddle` | PROVEN | `{CL}` |
| C17 | §23 | `Entity.nonContradiction` | PROVEN | `{}` |
| C91 | §25/§27/T7 Passo A | `Modal.subject_nec_entity_nec : NecessarySubject s → NecessaryEntity (EntityOf s)` (+ `_iff`, `necessary_entity_exists_of_necessary_subject`) — **lift definicional sujeito → entidade** | PROVEN | `{NecessarySubjectKind, Subject}` (VOCAB; `ExistsAt`/`EntityOf` partilhados — contramodelo hostil `{}` mostra que não é lei lógica) |
| C181 | §28/T15 | `NecessityEternity.necessary_existence_is_stage_uniform` — transporte condicional de necessidade mundial para presença e equivalência em todos os estágios | PROVEN | `{}` (lógica modal genérica; sem instanciação do sort canónico `Entity`) |
| C78 | T7 | `Modal.contingent_ground` | BLOCKED | (retired: manufactured `Sum.inl` origin grounding destroyed under hostile semantics) |
| C79 | T7 | `Modal.ultimateGround_exists` | BLOCKED | (retired: manufactured ultimate ground destroyed under hostile semantics) |
| C87 | T7 | `Modal.origin_is_necessary` | BLOCKED | (retired: manufactured `Sum.inl` origin necessity destroyed) |
| C88 | T7 | `Modal.transcendental_quantifier_swap` | BLOCKED | (retired: manufactured origin quantifier swap destroyed) |
| C89 | T7 | `Modal.ultimateGroundInit_exists` | BLOCKED | (retired: manufactured ultimate ground by initiation destroyed) |

Declared (Level 1): `ExistsAt` is the definition (2026-09-17); `actualWorld` (def, SEM).

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
| C28 | T6 | `Order.T6_fallibility` | PROVEN↑ | `{AxTwoSubjects, Means, Subject, Will, subjectWill}` (via T12 + `Core.someFalse`) |
| C29 | T6 | `Order.T6_truthTranscendsWill` | PROVEN↑ | `{AxTwoSubjects, Means, Subject, Will, subjectWill}` (as C28) |
| C30 | §8 | `Order.correctness_distinct` | PROVEN | `{Initiates, Means, State, Subject, CL}` (defs act-relative §8; usa o dado performativo do ato) |
| C31 | §9 | `Order.consequence_preserves_truth` | PROVEN | `{}` (E0) |
| C83 | §8 | `Order.no_correct_judgment_of_no_act` — **retorsão cartesiana**: nenhuma negação do ato pode ser correta (`judgment_of_no_act_is_incorrect`) | PROVEN | `{Initiates, Means, State, Subject}` |
| C84 | §1/§8 | `Order.judgment_of_no_act_proves_act` — **cogito retorsivo**: o ato de julgar que não há ato testemunha que o ato ocorre (`judgment_implies_cogito`) | PROVEN | `{Initiates, Means, State, Subject}` |
| C106 | §12 | `RetorsiveNormativity.claims_correct_presupposes_normativity : ClaimsCorrect s p → GenuineNormativity s p (¬p)` — assertion presupposes genuine normativity under bipolarity. **Mesmo nível semântico:** a conclusão é um termo da própria estrutura `GenuineNormativity` consumida por C107 — endereço só via `Means` primitivo, oposição lógica pura; o preço SEM `AxJudicativeBipolarity` é independente em Γ primitivo (modelo `M_opaque`), porém dispensa-se sob a postura normativo-judicativa (C164/C165, zero axiomas substantivos) | PROVEN↑ | `{AxJudicativeBipolarity, Initiates, Means, State, Subject}` |
| C107 | §15 | `IndubitableNormativeFreeWill.indubitable_normative_free_will : GenuineNormativity s p q → Chooses s p q ∧ FreeWill s` — genuine normativity derives choice and free will | PROVEN | `{Means, Subject}` |
| C157 | §12/§15 | `RetorsiveNormativity.retorsion_conclusion_is_the_very_genuine_normativity_structure : ClaimsCorrect s NoGN → GenuineNormativity s NoGN (¬NoGN)` — testemunha canônica: a negação realizada instancia a própria estrutura `GenuineNormativity` (mesma definição, mesmo endereço `Means`, oposição por lógica pura; nenhuma normatividade mais forte é importada) | PROVEN↑ | `{AxJudicativeBipolarity, Initiates, Means, State, Subject}` |
| C158 | §12/§15 | `RetorsiveNormativity.retorsion_address_uses_only_means : (claiming_denial_presupposes_genuine_normativity s h).address = ⟨Means s NoGN, Means s (¬NoGN)⟩` — o componente de endereço é construído somente pela relação primitiva `Means`; nenhum primitivo deôntico (`Correct`/`Incorrect`/`Ought`) ocorre na conclusão | PROVEN↑ | `{AxJudicativeBipolarity, Initiates, Means, State, Subject}` |
| C159 | §12/§15 | `RetorsiveNormativity.retorsion_opposition_is_pure_logic : (claiming_denial_presupposes_genuine_normativity s h).opposition = ⟨Incompatible NoGN (¬NoGN), prop_neq_neg NoGN⟩` — o componente de oposição é pura lógica (incompatibilidade com a própria negação + não-trivialidade proposicional); o footprint do teorema herda a rota por projetar do termo estrutural | PROVEN↑ | `{AxJudicativeBipolarity, Initiates, Means, State, Subject}` |
| C160 | §12/§15 | `RetorsiveNormativity.denial_requires_meaning_genuine_normativity : ClaimsCorrect s NoGN → Means s NoGN` — negar a normatividade genuína como correta exige significar a própria negação (cf. Ataque A) | PROVEN | `{Initiates, Means, State, Subject}` |
| C161 | §12/§15 | `RetorsiveNormativity.normative_retorsion_same_structure_type : ClaimsNormativeCorrectness s NoGN → GenuineNormativity s (Correct s NoGN) (Incorrect s NoGN)` — a rota axiomática (sem `AxJudicativeBipolarity`) também termina no MESMO tipo `GenuineNormativity` (cornos = polos normativos judicativos); a cadeia GN → Chooses → FreeWill é independente da rota | PROVEN | `{Initiates, Means, State, Subject, CL}` |
| C90 | T8 | `GroundPerson.personal_ultimate_ground_exists` | BLOCKED | (retired: manufactured ultimate ground destroyed under hostile semantics) |

### Auditoria Ontológica da Cadeia de Agência (`asserts → act → Act → Subject → Person → ChoiceField → Chooses → FreeWill`)

| Passo / Implicação | Formalização Lean | Classificação | Estatuto Epistemológico e Semântica Hostil |
| :--- | :--- | :--- | :--- |
| **asserts → act** | `Agency.assertion_is_weak_act` | **Caso A (Definicional / Fraco)** | A ocorrência de uma asserção é um evento realizado (`act s p` — *ato fraco: evento realizado*), projecção imediata de `asserts s p := act s p ∧ p`. A retorsão `noWeakAct_selfRefutes` estabelece puramente `∃ s p, act s p` sob `{Subject, act}` sem assumir significado intencional. |
| **act ↛ Act** | `Agency.weak_act_implies_strong_act` | **Caso D (Ponte / Bloqueio Aberto)** | O evento realizado (emissão, som, toque, evento físico/mecânico) **não acarreta logicamente** o ato intencional de iniciação com significado (`Act s p := Means s p ∧ ∃ w w', Initiates s w w' p` — *ato forte: ato com significado intencional e caráter de iniciação*). A passagem `act → Act` é uma ponte filosófica explícita (`weak_act_implies_strong_act`), não uma identidade definicional oculta. O atalho forte Logos é a asserção intencional `Asserts s p := Act s p ∧ p` (`assertion_is_act`). |
| **Act → SubjectExists** | `Agency.act_requires_subject`<br>`Agency.subject_exists_of_act` | **Caso B/A (regra constitutiva = identidade)** | Em Logos `Act s p := Means s p ∧ ∃ w w', Initiates s w w' p` e `SubjectExists s := ∃ p, Act s p`: ser sujeito *do* ato é a própria definição de sujeito atualizado. |
| **Act → Intentional** | `Person.act_implies_intentional` | **Caso A (identidade)** | O conteúdo do próprio ato testemunha `Intentional s := ∃ p, Means s p` (`⟨p, h.1⟩`, `{Initiates, Means, State, Subject}`). Identidade definicional: NÃO é atacável por modelo hostil. A leitura substantiva de intencionalidade (consciência/awareness interna) NÃO é forçada — `not_entails_substantive_intentionality` (Part A2, `{}`). |
| **SubjectExists → Intentional** | `Person.subjectExists_implies_intentional`<br>`Person.intentional_implies_subjectExists` | **Caso A (identidade)** | Ambas as noções desdobram para `∃ p, Means s p` (`{Means, Subject}`); equivalência por desdobramento direto. Nenhuma premissa. |
| **Subject → Person** | `Person.person_of_subject` | **Caso A (nominal §12)** | Sob a redução estrutural de §12 (`Person s := Agent s ∧ Rational s ∧ Intentional s` com `Agent := True` e `Rational := ∃ p, Means s p` — piso derivado, PERSON.md 2026-09-23), `Person` colapsa em `∃ p, Means s p`, IDÊNTICO a `SubjectExists`/`Intentional` (`Person.person_intentional_iff`, `{Means, Subject}`). O §12 é compromisso constitutivo (rótulo nominal), não descoberta metafísica. **Separação 2026-09-18**: derivabilidade formal ≠ neutralidade semântica da definição; sobsemântica hostil com predicado substantivo, a implicação NÃO se segue (`CountermodelSubjectWithoutPerson`, `not_entails_person`), mas isso NÃO é contramodelo da identidade §12. |
| **Person (unificada) ← FreeSubject** | `Person.free_subject_is_person` | **Caso A (Teorema com Preço Nomeado)** | Na ontologia unificada de $\Gamma$, a Pessoa é o critério boécio-aquiniano (`Person s := ThomisticPersonCore s`): substância individual de natureza racional, dotada de domínio dos próprios atos. Uma vez derivado o Livre-Arbítrio a partir da normatividade genuína (`indubitable_normative_free_will`), a pessoalidade segue como teorema com preço nomeado — o único conteúdo não-definicional é a lei VOCAB `will_individuation` (`free_subject_is_person`/`freeWill_implies_person`, `{Means, Subject, Will, subjectWill, will_individuation}`, 0 axiomas substantivos; emenda 2026-09-25: a definição antiga `Person s := FreeSubject s` foi substituída). A antiga noção opaca `SubstantivePerson` foi revogada como um artefato de lacuna sintética. |
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
Will layer (all VOCAB, `Logos.Agency` A16–A20): `Will` (Type of volitional
faculties), `subjectWill : Subject → Will` (A17), `will_individuation` (A18 —
constitutive MEANING-POSTULATE, injectivity of `subjectWill`, **declared not
derived**), `Wills` (A19), `Ought` (A20).
Independence machine-witnessed — a **kernel fact** (2026-09-24), not a derivation gap:
the hostile model `Subject := Bool`, `Will := Unit`, `subjectWill := fun _ => ()` satisfies the
pre-will spine with its performative datum (`WillIndividuationAudit.hostile_model_satisfies_prewill_spine`,
`{}`), and there the law **arrives at a contradiction**: forcing `will_individuation` on this
model demands `subjectWill true ≠ subjectWill false` while both sides are `()`
(`hostile_model_refutes_will_individuation`, `{}`). Spine + law is inconsistent, spine alone
satisfiable ⇒ the law is not a consequence of the spine
(`will_individuation_not_forced_by_prewill_spine`, `{}`) — A18's VOCAB status is kernel-verified (§5.1).

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
| 14. Grounding Principles → Means ¬p | Entity grounding | DOES NOT DERIVE | `Ground e p` relates entities to propositions, entirely outside `Means`. |

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
   - A retorsão transcendental estabelece um sujeito intencional e resolução cognitiva assimétrica, parando antes de volição (`AimsAt`) e execução externa de ação (`Act`). A pessoalidade é o critério boécio-aquiniano alcançado a partir do Livre-Arbítrio derivado da normatividade via teorema com preço (`Person s := ThomisticPersonCore s`; emenda 2026-09-25 substitui a formulação antiga `Person s := FreeSubject s`).
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
   - O antigo predicado opaco `SubstantivePerson` foi auditado e reconhecido como uma lacuna meramente sintética (Categoria 3). Na ontologia unificada de $\Gamma$, a Pessoa é o critério boécio-aquiniano (`Person s := ThomisticPersonCore s`), alcançado a partir do Livre-Arbítrio via teorema com preço nomeado (`will_individuation`), com 0 axiomas substantivos (emenda 2026-09-25 substitui a formulação antiga `Person s := FreeSubject s ↔ FreeWill s`).
11. **Síntese Mestra da Fronteira Agencial (`definitive_agency_frontier_synthesis`, `{}`).**

### Auditoria da Fronteira Modal e do Fundamento (2026-09-20):
A campanha em `Logos.GroundingFrontier` estabelece os limites matemáticos e ontológicos da passagem da verdade necessária à realidade necessária e ao fundamento último:
1. **Hierarquia de Pontes Candidatas (G1–G4):**
   - G4 (`Candidate_G4`, persistência forte) $\implies$ G2 (`Candidate_G2`) $\implies$ G1 (`Candidate_G1`, existência modal fraca) (`implication_G4_implies_G2`, `implication_G2_implies_G1`, `{}`).
   - Separação estrita G1 $\not\implies$ G2 (`separation_G1_not_implies_G2`, `{}`): a verdade necessária com testemunhas mundiais contingentes não força a existência de entidade necessária.
2. **Análise de Quantificadores ($\forall w \exists e$ vs $\exists e \forall w$) e o Corno Faltante do Fundamento:**
   - O grounding mundano ($\forall w \exists e$) não acarreta fundamento necessário uniforme ($\exists e \forall w$) (`worldwise_fails_to_derive_uniform_ground`, `{}`).
   - Isolamento do Corno Rígido Faltante (`MissingRigidGroundHorn`): o fundamento uniforme equivale estritamente ao grounding mundano conjugado ao corno rígido (`uniform_ground_iff_worldwise_and_missing_horn`, `{}`).
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
   - Família completa G1–G10 formalizada e verificada ({}); teorema de colapso impessoal (`collapse_invariance_impersonal`, `{}`) prova que a linguagem de grounding não pode definir pessoalidade.
8. **Síntese Mestra da Fronteira do Fundamento (`grounding_frontier_synthesis`, `{}`).**

### Auditoria de Negação dos Axiomas Substantivos (2026-09-20):
A campanha em `Logos.AxiomNegationAudit` executou a busca sistemática por necessidade oculta em $\Gamma$, testando a negação de cada um dos 9 axiomas substantivos (SEM e META) contra o núcleo matemático inevitável $\Gamma_{\text{core}}$:
1. **Nenhum Axioma Substantivo é Forçado pelo Núcleo ($\Gamma_{\text{core}} \not\vdash A$):**
   - $\neg \text{AxIntentionalChoice}$ (A14): consistente com o núcleo performativo (`core_compatible_with_neg_a14`, `{}`); refuta necessidade oculta de A14.
   - $\neg \text{AxActPolarity}$ (A13): consistente com o núcleo performativo (`core_compatible_with_neg_a13`, `{}`).
   - $\neg \text{universal\_thesis\_claims\_objectivity}$ / $\neg \text{transcendental\_reflection\_intentional}$: consistente sob assertor não-objetivista (`core_compatible_with_neg_retorsion_obj`, `{}`).
   - $\neg \text{AxTwoSubjects}$ (A6): consistente com o universo solitário (`core_compatible_with_neg_a6`, `{}`).
2. **Teorema Mestre de Ausência de Necessidade Oculta (`no_hidden_necessity_synthesis`, `{}`):**
   - Prova formal no kernel de que todos os axiomas substantivos permanecem genuinamente adicionais e independentes de $\Gamma_{\text{core}}$.
   - Nenhum teorema com pegada vazia `{}` contradiz qualquer negação de axioma. Todos os 9 axiomas são compromissos semânticos ou metafísicos genuínos.

## Deferred / blocked

| ID | Prose | Status | Missing |
|----|-------|--------|---------|
| F1a | §13–§15 choice-field existence (`∃s p q`, `ChoiceField s p q`) | PROVEN | `person_hasChoiceField`/`choiceField_exists` `{Means, Subject}` + `judge_commits` `CL` (choice-realism batch, C51–C52/C55; renamed 2026-09-18 — field form, not genuine choice) |
| F1b | §15 genuine choice & freedom of the actor | PROVEN↑ | `Choice.freeWill_exists` / `Choice.freeSubject_exists` / `Choice.genuineChoice_exists_of_act_constitutive` sob `{AxIntentionalChoice, Initiates, Means, State, Subject}` (rota do Cogito / A14). Alternativamente, sob a **rota de retorsão normativa** (`Logos.RetorsiveNormativity.retorsion_derives_free_will`), demonstrado sob `{AxJudicativeBipolarity, Initiates, Means, State, Subject}` (`Tag: SEM`, bipolaridade judicativa), onde a negação de normatividade genuína refuta-se performativamente ao ser assertida como juízo correto, instanciando `GenuineNormativity` e derivando `Chooses` e `FreeWill` sem depender de `AxIntentionalChoice`. Resíduos registrados: (a) o preço SEM `AxJudicativeBipolarity` é **independente** em Γ primitivo (contramodelo `M_opaque`, `BipolarityRetorsion`) — porém é *dispensável* para a refutação do ataque, que é axiomática sob a postura normativo-judicativa (C164/C165); (b) o livre-arbítrio assim obtido tem cornos meta-nível (`NoGN`, `¬NoGN`) — deliberação sobre conteúdo de objeto/ação requer a rota separada `DeliberateChoice`/`ClaimsNormativeCorrectness` (C140/C141) |
| F2 | §21 teleology (`Ought → Goal`) | DEFERRED | deontic layer (normativity → telos; ver C113–C121 para a retorsão do dever prático) |
| F3 | §28 Good (`§20 → bem`) | COUNTERMODEL (positive close C178) | moral good **separated** from logical normativity: `MoralFrontierAudit.epistemic_normativity_without_practical_obligation` (`M_amoral`, `{}` — row C175) — epistemic agential normativity carries no practical obligation. **The separation itself is permanent (`{}`)**; the *positive close* is now earned honestly (2026-09-24, C176–C178): `Good` is a **fair definition** (helpfulness toward the other — `∃ t ≠ s, Person t ∧ Helps s t ∧ ¬ Harms s t`) and **obtains** (`moral_good_obtains`, C178) under the single disclosed META bridge `AxBenevolentBearingObtains` (C177, `Tag: META`). The bare value layer is machine-proven empty (C176), so the bridge is a genuine paid commitment, not a hidden derivation. The negative pole `Evil` remains a declared SEM datum (its fair reading is uninhabited without a parallel "some harm occurs" bridge — not yet declared). The relying structure alone still never forces any pole (`moral_pole_postulate_is_not_a_consequence`, `{Initiates, Means, State, Subject}`) |
| F4 | §28 Love | PROVEN↑ | `Love.T13_someoneLovable` (C41) under `{AxTwoSubjects, Means, Subject}` |
| F5 | §28 EternalRelation | → PROVEN↑ | dissolved in C42: `Love.T14_eternalRelation_conditional` under `{AxTwoSubjects, Means, Subject}` |
| F6 | §28 Trinity | DEFERRED | no argument exists yet (§28/§29) |
| F1bUncond | §15 unconditional `∃ s, FreeWill s` | BLOCKED | companion row to F1b (which is the conditional/PROVEN↑ front): the unconditional existence claim stays BLOCKED — missing lemma `rejectedHornCoMeant : ∃ s p, A s p ∧ A s (¬p)` |
| EvalSettlement | §3 executive settlement (executive `Choice` vs deliberative `Chooses`) | PROVEN | `ExecutiveDeliberativeFrontier.M_det` / `M_det_validates_executive_choice`: separation — executive `Selects`/`Choice`/`FreeAgency` is independent of deliberative `Chooses` with NO bridge axioms (`M_det`, `ExecutiveDeliberativeFrontier` Track A–H); `CommittedChoice` bundles settlement via the `Act` conjunct but derives no executive causation/sourcehood; `ContemplatesWithoutSettling` still implies `FreeWill` |
| OpenBridgeNormativity | §0.10 positive bridge bivalence → `GenuineNormativity` (`∀ s p, Judge s p → GenuineNormativity s p (¬p)` or stance-antecedent variant) | BLOCKED | bivalence alone is insufficient — `M_inanimate` (C167, `{}`); the weak-voice route C106 closes it at SEM cost `AxJudicativeBipolarity` (independent via `M_opaque`, dispensable); the axiom-free full-stance route C164/C165 requires the stance datum; unconditional `¬NoGN` is not derivable |
| Q7.2 | weaker `AxGlobalGround` | ANSWERED | answered by batch A2-swap-theorem: for atoms the swap needs no premise at all (definitional via world-vacuous `ExistsAt`); the compound instance is unforced, not weaken-able (DESIGN.md) |

## Level 3 — modal, choice, interpersonal value (new: poem chain)

> **Modal continuation — do NOT conflate (C59 note):** the *logical*
> continuation is `Semantics.strongTruthExists` (C59, `{CL}`) — `∃ τ,
> NecessarilyTrue τ`, resident in Core/Semantics (LEM), **not** derived from the
> normative chain; the *normative world-level* continuation is
> `NecessaryNormativeOrder : ∀ w, NormativeOrderAt w`
> (`NecessaryPersonalGround.lean:110-111`, anchored in C36 +
> incompatibilities). C95/C96 surround C59: the atom wall (no atom is fixed
> modally) and contingent content.

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
| C182 | §28/CHARACTERISTICS | `ModalPossibilityFrontier.aseity_does_not_force_any_volition_alternatives` — generic `Aseity` is compatible with the absence of every Level-3 volitional alternative | PROVEN | `{}` (pure logic; generic Unit/False countermodel) |
| C184 | §28/CHARACTERISTICS | `ModalPossibilityFrontier.volitional_alternative_does_not_force_aseity` — a Level-3 volitional alternative is compatible with failure of generic `Aseity` | PROVEN | `{}` (pure logic; generic Bool/True countermodel) |
| C185 | §28/CHARACTERISTICS | `CanonicalAseity.false_meaning_cannot_ground_true_meaning` — generic model-theoretic exclusion: an entity with false meaning capacity cannot ground true meaning | PROVEN | `{}` (pure logic) |
| C186 | §28/CHARACTERISTICS | `CanonicalAseity.conditional_canonical_aseity` — `Entity.ofGround` has Canonical Aseity (no external grounding entity) if all subjects are discriminating | PROVEN | `{Means, Subject}` (vocabulary-only) |
| C38 | P2 | `Necessity.necDistinction : Necessity (¬ N_T ∧ ¬ N_F)` | PROVEN (was AXIOM) | `{}` (E0; C1: identity-model alias; world content = C37) |
| C39 | P4 | `Choice.T11_choiceField` | PROVEN | `{Initiates, Means, State, Subject}` (campo de escolha — não escolha genuína — derivado do ato intencional C68 → C24 → C39; renomeação/split 2026-09-18; **usa C24 só no sentido fraco** `∃p, Means s p` — forma mais forte válida = reancoragem em `SubjectExists`/`Intentional`) |
| C40 | P5/P7 | `Plurality.T12_twoPersons` | PROVEN↑ | `{AxTwoSubjects, Means, Subject, Will, subjectWill}` (settled by Unit countermodel that 1 act does not entail plurality; requires META bridge `AxTwoSubjects`) |
| C41 | P7 | `Love.T13_someoneLovable` | PROVEN↑ | `{AxTwoSubjects, Means, Subject, Will, subjectWill}` (via C40) |
| C48 | §25/P1 | `Plurality.cogito_from_T12` | PROVEN↑ | `{AxTwoSubjects, Means, Subject, Will, subjectWill}` |
| C49 | §13/IM_STUPID | `Choice.meaning_needs_subject` + `Choice.meaning_I_needs_subject` (definitional form: `Meaning_I p → ∃s, Means s p`) | PROVEN | `{Means, Subject}` |
| C50 | §14 | `Choice.incompatible_self_negation` | PROVEN | **`{}`** (pure logic — the field around any meaning-act) |
| C51 | §14/IM_STUPID | `Person.person_hasChoiceField : Person s → ∃p q, ChoiceField s p q` — **subject ⇒ campo de escolha** (via o conjunto do domínio, emenda 2026-09-25; NÃO é escolha genuína) | PROVEN | `{Means, Subject, Will, subjectWill}` |
| C52 | §14 | `Choice.choiceField_exists` | PROVEN | `{Initiates, Means, State, Subject}` (o campo é real, derivado do ato intencional C68 → C52 via `intentional_hasChoiceField` a partir de `act_implies_intentional` — reancorado em código 2026-09-18, sem passar por `Person`; renomeado 2026-09-18) |
| C53 | §14 | `Choice.noChoiceField_selfRefutes : Asserts speaker NoChoiceField → False` | PROVEN | `{Initiates, Means, State, Subject}` (retorsão performativa do campo: negar o campo é ele próprio um ato de campo contra a sua negação) |
| C54 | IM_STUPID §2 | `Plurality.JUDGE_HAS_CHOICE_FIELD : (¬N_T ∧ ¬N_F) → ∃s p q, ChoiceField s p q` — **right/wrong ⇒ campo de escolha** | PROVEN↑ | `{AxTwoSubjects, Means, Subject, Will, subjectWill}` (derivação operativa via AxTwoSubjects h e person_hasChoiceField) |
| C55 | §8/§14 | `Order.judge_commits : ∃s p q, A s p ∧ (Correct s p ∨ Incorrect s p) ∧ ChoiceField s p q` — the judge HAS a choice-field (não escolha genuína) | PROVEN | `{Initiates, Means, State, Subject, CL}` (defs act-relative §8; usa o dado performativo do ato) |
| C56 | P6 | `Value.alone_no_other_help_harm` | PROVEN | `{Subject}` |
| C57 | §26 | `Choice.noSubject_selfRefutes : Asserts speaker NoSubject → False` | PROVEN | `{Initiates, Means, State, Subject}` (retorsão performativa genuína: negar o sujeito é um ato que testemunha o sujeito) |
| C42 | P8 | `Love.T14_eternalRelation_conditional` | PROVEN | `{Means, NecessarySubjectKind, Subject, Will, subjectWill}` (sob o princípio de estabilidade pessoal relativo-à-espécie, princípio relacional de amor e um par de espécie-necessária exibido; `AxTwoSubjects` saiu a 2026-09-28 — o par tem de ser exibido, não herdado de T12) |
| C43 | P8 | `Love.T14_content_conditional` | PROVEN↑ | `{AxTwoSubjects, Means, Subject, Will, subjectWill}` |
| C44 | P8 | `Love.T14_world_conditional` (`NecessityPH`) | PROVEN | `{Means, NecessarySubjectKind, Subject, Will, subjectWill}` (world-anchored conditional □; como C42) |
| C45 | P8 | `Love.T14_square_conditional` (alias `Necessity`) | PROVEN | `{Means, NecessarySubjectKind, Subject, Will, subjectWill}` (conditional; como C42) |
| C46 | P5 | `Value.valueInterpersonal_of_split_conditional` | PROVEN↑ | `{AxTwoSubjects, Means, Subject, Will, subjectWill}` (sob o princípio PersonsAffectPrinciple) |
| C47 | P5/P7 | `Plurality.T12_directedPair_conditional` | PROVEN↑ | `{AxTwoSubjects, Means, Subject, Will, subjectWill}` (sob o princípio PersonsAffectPrinciple) |
| C61 | P3 | `Plurality.rightWrong_implies_someone_means` — "há certo e há errado → há alguém para quem algo significar" | PROVEN↑ | `{AxTwoSubjects, Means, Subject, Will, subjectWill}` (`JUDGE_HAS_CHOICE_FIELD` C54 ∘ `rightWrongDistinction` C36) |
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
| C77 | P5/P8 | `Love.necessaryPersonExists_conditional` | DEFERRED | `{Initiates, Means, State, Subject}` (theorem removed from kernel, commit ae7f4bd "remove a lot of garbage" 2026-09-23; conditional claim retained as annotated surface only — a necessidade do sujeito não se segue do ato contingente, como provado pelo contramodelo de agência contingente) |
| C85 | P6 | `Value.help_not_harm` — **princípio de benevolência**: no plano fundante, ajudar exclui prejudicar (`Helps s t → ¬ Harms s t`) | PROVEN | `{Subject}` |
| C86 | P6/P8 | `Love.love_helps` (+ `Love.love_not_harms`, `Love.loves_of_helps`) — **amor como benevolência direcionada**: amar é ajudar e não prejudicar (`Loves s t := Helps s t ∧ ¬ Harms s t`) | PROVEN | `{Subject}` |
| C92 | P8/§27 | `Love.necessary_entity_exists_conditional` | DEFERRED | `{Initiates, Means, State, Subject}` (theorem removed from kernel, commit ae7f4bd "remove a lot of garbage" 2026-09-23; conditional claim retained as annotated surface only — entidade necessária não é acarretada pelo ato performativo) |

> Batch MODAL-FRONTIER-SEPARATIONS (2026-09-25): C182 and C184 are generic
> non-entailment countermodels over independently chosen predicates. Together
> they show two-way logical independence between `Aseity` and the existence of a
> `Level3_VolitionAlternative`; they do not establish aseity of `Entity.ofGround`
> or add modal accessibility, incompatibility, or distinct-world conditions.
> C185 and C186 formalize canonical external grounding and aseity for `Entity.ofGround`:
> C185 establishes the generic meaning-exclusion principle (`{}`), while C186
> proves Canonical Aseity for `Entity.ofGround` conditional on discriminating subjects (`{Means, Subject}`).

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
C77 and C92 are demoted to DEFERRED (theorems removed from the kernel, commit ae7f4bd); while they existed they were explicitly CONDITIONAL on this hypothesis.
T14 stands on the pair under `AxTwoSubjects` and `PersonStabilityPrinciple`.
Modal layer is derived (C1): `Necessity: Prop → Prop` is a *definition*
(identity-model alias) and `NecessityPH : (World → Prop) → Prop` the
semantics-grounded operator; `necK/necT/nec4` (alias) and `necKPH/necTPH/nec4PH`
are theorem; `necDistinction` is a theorem. No modal axiom remains.

## Level 2d — proof-performer invariance architecture (`Logos.HardenedInvariance`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C180 | §10/§24c | `HardenedInvariance.agent_invariant_core_is_strictly_inside_freewill_invariant_core` — the agent-invariant dependency-layer core is a proper subset of the free-will-invariant core; architectural non-relativity only, not metaphysical invariance of the ultimate foundation | PROVEN | `{}` (pure logic; no `CL`) |

> Batch INVARIANCE (2026-09-25): `AgentInvariant` and `FreeWillInvariant` are formalized
> as admissibility across proof-performer regimes. C180 proves strict inclusion by
> transporting the existing neutral-core equivalences and the strict witness from
> `strict_core_inclusion`. The result is architectural: it does not instantiate an
> absolute/non-relative predicate for the canonical foundation.

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
| FAITH-2 | P8 eternal love | → PROVEN↑ | rests on `AxTwoSubjects` (META bridge restored after Unit countermodel) + kind-relative `PersonStabilityPrinciple` + an exhibited necessary-kind pair; T14 (C42–C45) is proven under `{Means, NecessarySubjectKind, Subject, Will, subjectWill}` with the pair exhibited, no longer under `{AxTwoSubjects}` (2026-09-28, two-kinds: exhibiting the kind subsumes the T12 witness). C43 (`T14_content_conditional`) still pays the bridge |
| F7 | §15 the bipolar half of freedom | → PROVEN↑ | dissolved in F1b: free will under AxActPolarity is derived via A13 → A14 → FreeWill (Choice.freeWill_exists_of_act_polarity / Choice.act_polarity_implies_intentional_choice); AxActPolarity remains an optional stronger SEMANTIC principle |
| F8 | Trinity | DEFERRED | not attempted (§28/§29) |
| F9 | Incarnation / creation | **SPLIT 2026-09-27** | **Four lanes, no longer one undifferentiated word.** *L1 existence* → **PROVEN** (C350, `{propext, Subject}`): contingent reality obtains, derived outright — out of the faith zone. *L2 relation* → existence free (C350), *meaning* `PROVEN` (C367, exhibited contingent person — `AxTwoSubjects` left this row 2026-09-28, two-kinds), the ground's love `PROVEN↑` (C351–C352, + `AxGroundLovesContingentRealm`) — priced, correctly. *L3 production* → **DEFERRED, unclaimed**: no `Creates` relation in Γ, and C110 still refutes that grounding entails a creation record. *L4 purpose* → **faith** (poem P10). *Incarnation* → **DEFERRED** (F8). **Do not let the L1 result migrate into the others:** "the cosmos exists" is proved; "something made it" and "it exists for an end" are not |

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
  types (`Entity.lean`, `Plurality.lean`). `Entity` is the general
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

Summary counts (lift-necessário, measured 2026-09-18; supersedes the A2-swap-theorem figures below; **re-derived 2026-09-25 by `scripts/gapmap_taxonomy.py --check` from `formal/axiom_audit.json`** — the four tallies and the per-axiom PROVEN↑ counts are machine-derived, not transcribed):

- **PROVEN** (status PROVEN/PROVEN↑ whose audit footprint carries **no SEM/META
  axiom** — machine re-derived from `formal/axiom_audit.json`, 2026-09-25):
  - **55 truly axiom-free** (`{}`): C379, C380, C381, C383, C1, C2, C4, C5, C6, C7, C8, C9,
    C183, C11, C179,
    C17, C181, C22, C26, C27, C31, C35, C36, C95, C96, C182, C184, C185, C38, C50,
    C180, C63, C108, C111, C166, C167, C226, C227, C231, C259, C260, C272, C309,
    C310, C353, C355, C356, C361, C364, C365, C366,
    **C417, C418, C426** (the 2026-09-28 precedence batch: no atom is true at the
    falsity world, no world satisfies no form, and the world-invariance of the
    Prop-level right/wrong distinction. C418 is the refutation of the batch's own
    first draft lemma, which was **false** — see the batch section above),
    `EvalSettlement` (`ExecutiveDeliberativeFrontier.M_det`, added 2026-09-28 — this
    row was in the ledger but silently dropped by the generator's claim-id regex,
    see the correction below). (C175 is also `{}`, but its
    ledger status is COUNTERMODEL — the separation, not a PROVEN step — so it is
    not counted in this bucket; **C382 is the same case** — the 2026-09-27
    meaning-retorsion batch's populated complement is `{}` with COUNTERMODEL
    status, and it is the machine-checked reason `¬ NoMeaning` is not derivable,
    so counting it as a PROVEN step would overstate the batch. **C385 is the same
    case** — the utterance model is `{}` with COUNTERMODEL status, and it is a
    separation (utterable, not assertable) rather than a PROVEN step. C379, C380, C381
    and C383 are its four `{}` PROVEN siblings. C226/C227 are the two `{}`-footprint
    personhood-separation results of the 2026-09-25 refactor; C231 is the
    `{}`-footprint *irreducibility* result that closes that batch. C233 and C240
    are likewise `{}` with COUNTERMODEL status — the scope/infallibility and
    scope/counterfactual-knowledge separations of the 2026-09-26
    foundational-omniscience batch — so they stay out of this bucket too. C241,
    C249 and C250 are the three `{}`-footprint separations of the same day's
    foundational-omnipotence batch (presence-without-operation,
    gapless-without-conjunctive-power, scope-without-operation), likewise out.
    C309/C310 are the two `{}` diagonal theorems of the SYSTEM-EXTERNALITY batch, and
    C353 is the 2026-09-27 loves-catch-up batch's only `{}` row — a genuine countermodel of
    the SEM datum's contingency *shape* in a world-rigid universe, which is a PROVEN step
    and so **is** counted here; its companion `perfect_universe_actual_is_necessary` is
    `{}` too but is consumed inside C353 and carries no row.)
    **C355/C356/C361/C364/C365/C366** are the six `{}` **PROVEN** rows of the
    2026-09-27 empty-world ledgering pass (Level 22): C355 refutes an absolutely
    empty world once a necessary entity exists, C356 excludes it by stipulation,
    and C361/C364/C365/C366 are the positive existence/regime results of the
    G1–G4 atlas. They are counted here as PROVEN steps because each is a
    machine-checked theorem. The *separations* around them (C357, C358, C360,
    C362, C363) keep COUNTERMODEL status and stay out of this bucket, as does
    the rebuilt C110.
  - **11 `CL`-only**: C3, C10, C12, C13, C14, C16, C37, C59, C93, C251, C322. (C251 is the
    non-emptiness + contradiction-freedom of the satisfiable scope domain; its `propext`
    cost is inherited from C14, deliberately, so the graph shows the C251 → C14 edge.)
  - **230 vocabulary-only** (footprint ⊆ the statement's own declared `VOCAB`):
    C419, C420, C421, C422, C423, C424, C425, C427, C428, C429, C430, C431
    (the 2026-09-28 precedence / §18 batch — twelve rows, 0 substantive axioms;
    the `NecessarySubjectKind` in C419–C421/C424/C429/C430 is the `ExistsAt` artifact
    and the `Means` in C422/C423/C425/C428/C431 is `EntityMeans`/`GroundsEntity`),
    C432, C433, C434, C435, C436, C437, C438
    (**the 2026-09-28 precedence-unicity / temporal-separation batch — seven rows,
    0 substantive axioms, 0 new `Tag:`, 0 new ◈.** `propext` in C434/C435 is Lean's
    own foundational axiom, not a premise; `NecessarySubjectKind` in C432/C436–C438 is
    the `ExistsAtTime → ExistsAt → SubjectExistsAt` unfolding. C433/C435 are the first
    §9 rows to price `SemanticFinitude`, still `Tag: VOCAB`, so the badge is `PROVEN`),
    C368, C369, C370, C371, C372, C373, C374, C375, C376, C377, C378, C384, C386,
    C389, C390, C391, C392, C393, C394, C395, C396, C397, C398, C400, C402,
    C410, C411, C412, C413, C414, C415, C405, C406,
    C102, C103, C104, C105, C91, C58, C68, C21, C23, C24, C25, C30, C83, C84,
    C107, C160, C161, F1a, C94, C186, C39, C49, C51, C52, C53, C55, C56, C57, C42,
    C44, C45, C62,
    C101, C97, C98, C99, C100, C85, C86, C113, C114, C116, C120, C121, C122, C137,
    C138, C139, C140, C141, C164, C165, C142, C144, C145, C154, C155, C156, C162,
    C163, C168, C169, C170, C171, C221, C222, C223, C224, C225, C229, C230, C232,
    C147, C148, C149, C150, C151, C152, C153, C172, C173, C174, C176, C189, C190,
    C191, C193, C194, C195, C196, C198, C199, C200, C201, C203, C204, C205, C206,
    C207, C208, C209, C210, C211, C213, C215, C216, C217, C218, C219, C220, C234,
    C235, C236, C237, C238, C239, C242, C243, C244, C245, C246, C247, C248, C261, C262, C263, C264, C265,
    C275, C276, C280, C281, C282, C283, C284, C285,
    C287, C288, C289, C290, C291, C295, C296,
    C323, C324, C325, C326, C327, C328, C329, C330, C331, C332, C333, C334, C335,
    C336, C337, C338, C344, C345, C346, C347, C348, C350, C367,
    C354.
    **C388 saiu deste bucket em 2026-09-28** (212 → 211) quando `SemanticFinitude` foi
    promovida de `def` a axioma declarado: a linha passou de `PROVEN` a `AXIOM`, e o
    vocabulário-only é um predicado sobre *linhas `PROVEN`/`PROVEN↑`*, não sobre
    declarações. C389–C398 e C400 **continuam** vocabulary-only, porque
    `SemanticFinitude` é ela própria `Tag: VOCAB` — a promoção pagou um preço visível
    sem mover nenhum destes footprints para o lado substantivo. É a diferença entre
    *preço declarado* e *preço substantivo*.
    C323–C338, C344–C348 and C354 are the 2026-09-27 loves-catch-up batch (Level 21): the
    22 rows of the ground-love region that rest on **declared vocabulary alone** — the
    contingency and meaning setup (C323–C325), the undiscriminating grounding half and its
    refutation (C326–C328), the ontological pole (C329/C330), the six `GroundLoves`
    projections (C331–C336), the refuted unrestricted bridge (C337/C338), the interpersonal
    separations (C344–C348), and the datum's conditional satisfiability (C354). **This is a
    fact about the kernel's reach, not a warrant for the love thesis**: the substantive
    content of the module is exactly C339 (META) plus C349 (VOCAB), and the six `PROVEN↑`
    rows below are where the price is. C330 in particular is ontology-forced by the
    three-constructor `Entity` and carries **no** love content.
    C287–C291 and C295–C296 are the 2026-09-26 asiety-freedom batch (Level 19): the
    axiom-free Act-free weak→asiety step (C287/C288), the three ◈ META transfers whose
    stipulation is a `def` and therefore invisible to `#print axioms` (C289/C290/C291),
    the ground's exclusion from the chooser inventory (C295), and the master synthesis
    (C296). Their vocabulary-only footprint is a *fact about the kernel's reach*, not a
    warrant: the price of C289–C291 lives in the ◈ registry, not in the footprint.
    C242–C248 are the seven vocabulary-footprint results of the 2026-09-26
    foundational-omnipotence batch (gapless operative scope, the two
    non-contradictory horns, the atom/subject exclusions, the sole-operator
    theorem, and the master synthesis); each carries `propext` from C14 where it
    touches `nonContradiction`, and the companion
    `necessity_and_presence_yield_foundational_omnipotence` (no claim ID) is
    `{Subject, Means, propext}` on the same footing.
    C221–C225 are the five new priced personhood/grounding theorems of the
    2026-09-25 refactor (C223 is the definitional free-will route; C221/C222/
    C224/C225 carry the declared VOCAB law `will_individuation`). C229/C230/C232
    are the 2026-09-26 price-localization batch: C229 and C232's free half cost
    nothing, C230 *characterizes* the individuation price without paying it.
    C234–C239 are the 2026-09-26 foundational-omniscience batch (truth-exhaustive
    and world-indexed exhaustive scope, the *refutation* of infallibility for the
    ground, the exclusion of atoms and discriminating subjects, and the master
    synthesis) — all `{Means, Subject}`, i.e. vocabulary only; the cost of the
    scope is the declared VOCAB `Means` and the pure-sort `Subject`, exactly as
    for `ofGround_maximal_capacity`.
    F1a is the choice-**field** existence form (resolves to a kernel step;
    renamed 2026-09-18 — the genuine-choice form is BLOCKED on `rejectedHornCoMeant`).
  - **C91** — vocab-only (`{Subject}`); hostile separations `{}`. C92 (the
    vocab-only lift `{Means, Subject}`) became `Love.necessary_entity_exists_conditional`,
    removed from the kernel (ae7f4bd) — DEMOVIDO para DEFERRED.
  - **C62** (`rightWrong_implies_meaning`) is the pure bridge: with the §8
    act-relative `Correct`/`Incorrect`, right/wrong unfold to a `Means`-act;
    the bare-distinction form `rightWrongDistinction_implies_meaning` is `CL`.
  - Former "axiom-free" range **C73–C79 split out**: C73 (two-persons) and C75
    (propositional necessity) are BLOCKED under hostile semantics; C76 retired
    (canonical rigid love); C77 DEMOTED → DEFERRED (ae7f4bd); C78/C79 BLOCKED —
    see the BLOCKED/retired blocks and the `## Formal Frontiers` inventory.
    Of that range only C74 (`aloneExcluded`) survives, as PROVEN↑ (below).
- **PROVEN↑** (fully machine-verified under the flagged SEM/META axiom shown —
  no foundation axiom remains): **41 claims** —
  `AxTwoSubjects` (17): C28, C29, C40, C41, C43, C46, C47, C48, C54, C61, C74, C277, C278, C279, C286, F4,
  **C401**;
  `necessaryPersonalSubjectExists` (3): C407, C408, C409 (the necessary-kind inhabitant and its two readings, Batch two-kinds 2026-09-28)
   (F4 shares the C41 decl, `T13_someoneLovable`; C351–C352 entered this list on
   2026-09-27 when the SEM datum `AxContingentCreationObtains` was deleted; **C350 left it
   the same day and C367 entered**, when existence and meaning were split. **The
   `AxTwoSubjects` count is unchanged at 22 — C350 out, C367 in, net zero** — and that is the
   **(C387, 2026-09-27, God-lane)** the 41st entry, which is the *first* claim to enter this
   list on `AxGroundLovesContingentRealm` alone: it is the ground's-love conclusion reached
   without the plurality route, so it is not behind `AxTwoSubjects` at all, and its footprint
   also drops the `Will`/`subjectWill` that entered only through that bridge. It does not
   reduce the 22: C351, C352 and C367 are untouched and still pay the bridge. The row is
   `PROVEN↑` rather than `PROVEN` because the love bridge and `GroundBearsGood` are real
   axioms, META and VOCAB respectively, and the ◈ marks the *stipulated* act-datum that
   its hypothesis carries.
   **CORRECÇÃO (2026-09-28, 5.ª — dois géneros):** o parágrafo anterior dizia que C351,
   C352 e C367 "permanecem" sob `AxTwoSubjects`. Isso era verdade na semântica sem
   géneros, onde todo o sujeito era contingente e a testemunha de T12 trazia a
   contingência de graça. A doutrina dos dois géneros exibe a premissa oculta: um
   reino contingente precisa de uma testemunha *contingente*, e a contingência da
   testemunha é o seu género. C367, C351 e C352 passam a exibir uma pessoa
   contingente como premissa explícita; exibi-la subsume a testemunha, pelo que
   `AxTwoSubjects` **sai** das três linhas (tal como de C42/C44/C45, onde o par de
   T12 passou a par exibido de género-necessário). **O total `PROVEN↑` passa a 38**
   (C367, C42, C44, C45 saem para *vocabulary-only*; C351/C352 ficam, pelo amor);
   **`AxTwoSubjects` passa a 17**; *vocabulary-only* sobe **200 → 202** (C42, C44,
   C45, C367 entram; C247/C330 ficam, com os nomes novos). Nada disto é promoção
   gratuita: cada linha que sai de `PROVEN↑` ganha uma premissa exibida mais forte.
  right result, because the six existence-only claims this batch also freed
  (`a_created_realm_obtains`, `a_contingent_reality_obtains`,
  `reality_is_not_exhausted_by_the_ground`,
  `the_ground_is_necessary_and_the_realm_is_contingent`,
  `realm_existence_does_not_imply_realm_necessity`,
  `the_cosmos_existence_is_not_refutable`) are ledgered as display or unnamed rows and were
  never entries in this list. So the bridge's reach over *claims* is unaltered while its
  reach over *existence* is gone: it now pays for the realm's meaning-bearingness, not for
  the realm's existence). **The total is likewise unchanged at 40** (C350 out, C367 in),
  so the only bucket that moved is *vocabulary-only*: 173 → **174**, gaining C350);
  `AxJudicativeBipolarity` (11): C106, C157–C159, C266, C267, C268, C269, C270,
  C271, C286;
  `AxSecondPersonalAddress` (2): C118, C119;
  `AxIntentionalChoice` (1): F1b (`freeWill_exists`);
  `AxBenevolentBearingObtains` (1): C178 (`moral_good_obtains` — the positive
  moral close; C176 is the bridge's own countermodel);
  `AxGroundLovesContingentRealm` (7): C340, C341, C342, C343, C351, C352, C387 (the
  ground-love inhabitants and the two cosmic conclusions, plus the God-lane's re-routed
  twin of C351, which reaches the love bridge without `AxTwoSubjects`; the primitive that
  makes the bridge non-derivable, `GroundBearsGood`, is `Tag: VOCAB` and so is **not**
  counted here — the whole price of these seven rows is the single META axiom C339);
  `AxContingentCreationObtains` — **RETIRED 2026-09-27, 0 rows.** It was a `Tag: SEM`
  datum entering C351, C352 through the target's contingency and content. It is deleted:
  `Plurality.cogito_from_T12` already exhibits the inhabitant of `Means` unconditionally,
  so C350 `cosmos_obtains` derives what the datum used to stipulate. C351, C352 now carry
  the plurality bridge `AxTwoSubjects` (META) in its place, and are the **only** place in
  the corpus where a META bridge and a META bridge are consumed together. The two rows'
  price cells are updated accordingly.
  (`Cogito` is proven — the M0 forced-foundation axiom is retired, its
  degenerate `fun h => h Cogito` with it. `actualWorld` is a def;
  `Exists`/`Content`/`Agent`/`Rational` are analytical defs; `Affects` is the A3
  definition `s ≠ t`; `AxPersonsAffect`, `AxPersonStability` and now
  `AxGlobalGround` (atom-restricted) are theorems — see "Axioms dissolved" below.)
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
  `AxTwoSubjects` is **NOT retired** (the earlier "plurality-discharge
  2026-09-17" claim was refuted by the 2026-09-24 audit): it remains a live
  `Tag: META` bridge behind 15 PROVEN↑ claims (C28, C29, C40–C48, C54, C61,
  C74, F4), and the canonical-pair claim it was said to discharge is **C73 =
  BLOCKED** (`Person.twoPersonsFromSubject`), not a theorem `{}`. The lone-
  subject model M2 stands as the Unit countermodel instead, and every T14
  theorem is additionally conditional on the unproven
  `PluralityLovePrinciple`.
  A1 removed `cogito`; M0 restored it as the FORCED foundation (+1);
  the definitional-subject batch proves it (−1).
  **CORRECÇÃO (2026-09-27, 3.ª):** a linha seguinte dizia **25**. O axioma
  `AxContingentCreationObtains` (SEM) foi **eliminado** — o que era uma declaração
  `Tag: SEM` passou a ser o teorema C350 `cosmos_obtains`, derivado de
  `Plurality.cogito_from_T12` sob a ponte pluralista `AxTwoSubjects`. Total **25 → 24**;
  `Tag: SEM` **7 → 6**; VOCAB 14 e META 4 inalterados. As notas de lote mais acima que
  registam "25 declared (VOCAB 14 / SEM 7 / META 4)" **permanecem como registo histórico**
  das respectivas datas — estão correctas para o que era verdade então, e não são reescritas.
   Net inventory (machine-derived 2026-09-27, re-derived 2026-09-28 by
   `python3 scripts/gapmap_taxonomy.py`): **27 declared axioms**, all tagged —
   `Tag: VOCAB` (16): `HasNature`, `Initiates`, `Means`, `Nature`,
   `NecessarySubjectKind`, `State`,
   `Subject`, `Will`, `Wills`, `act`, `subjectWill`, `will_individuation`,
   `GroundBearsGood`, `Ought`, `DependsOn`,
   **`SemanticFinitude`** (promoted 2026-09-28 from a `def`-bridge); `Tag: SEM` (6): `AxActPolarity`,
   `AxIntentionalChoice`, `Evil`,
   `transcendental_reflection_intentional`, `universal_thesis_claims_objectivity`,
   `AxJudicativeBipolarity` — `AxContingentCreationObtains` **left this list
   2026-09-27**, promoted to the theorem C350 `cosmos_obtains`;
   `Tag: META` (5): `AxGroundLovesContingentRealm`,
   `AxSecondPersonalAddress`, `AxBenevolentBearingObtains`, `AxTwoSubjects`,
   `necessaryPersonalSubjectExists` —
   plus Lean's own `Classical.choice`, `Quot.sound`, `propext`. The former
   "4 declarations + CL" figure (`Ground`, `GroundProp`, `GroundPrincipleProp`,
   `AxPersonalGround`) is dead: none of those four is an axiom any more.
   **CORRECÇÃO (2026-09-28, dois géneros):** total **24 → 26**; VOCAB **14 → 15**
   (`NecessarySubjectKind`, a distinção de géneros no vocabulário); META
   **4 → 5** (`necessaryPersonalSubjectExists`, a ponte que habita o género
   necessário com uma Pessoa). SEM 6 inalterado.
   **CORRECÇÃO (2026-09-28, promoção do limite F15):** total **26 → 27**; VOCAB
   **15 → 16** (`SemanticFinitude`, o limite semântico do sujeito, promovido de
   `def`-ponte a axioma declarado). SEM 6 e META 5 inalterados. É a **única** das
   correcções deste inventário em que o total sobe por *rigor* e não por conteúdo
   novo: nenhuma linha mudou de estado, e as dez linhas F15 passaram de
   *condicionais* a **incondicionais** sem perderem o distintivo `PROVEN` — porque
   `SemanticFinitude` é `VOCAB`, que o gerador trata como não-substantivo. A
   distinção que isto fixa: *preço declarado* ≠ *preço substantivo*, e o registo
   tem de mostrar as duas.
  **CORRECÇÃO (2026-09-27):** esta lista dizia 22 / 13 / 6 / 3, com data
  "2026-09-24" — desatualizada em todos os três totais. Faltavam-na
  `GroundBearsGood` (VOCAB), `AxContingentCreationObtains` (SEM) e
  `AxGroundLovesContingentRealm` (META).
  **CORRECÇÃO (2026-09-27, 2.ª):** `AxContingentCreationObtains` **deixou de ser
  axioma** — foi promovido a teorema (C350 `cosmos_obtains`, derivado de
  `Plurality.cogito_from_T12` sob a ponte pluralista `AxTwoSubjects`). Total
  **25 → 24**; `Tag: SEM` **7 → 6**. VOCAB 14 e META 4 inalterados. A CORRECÇÃO
  anterior, que o_added este axioma a esta lista, fica historicamente correcta
  quanto ao que era verdade em 2026-09-24, e datada.
  **CORRECÇÃO (2026-09-27, 4.ª):** a **existência** do cosmos deixou de custar
  qualquer axioma substantivo. A 2.ª CORRECÇÃO promoteu o datum a teorema mas
  deixou-o `PROVEN↑` sob `AxTwoSubjects`; a 4.ª divide a afirmação em duas.
  **C350** passou a `CosmicExistence.contingent_realm_obtains : ContingentRealmObtains`
  — `PROVEN`, `{propext, Subject}` — e **C367** é a linha nova para
  `CosmicExistence.cosmos_obtains : CreatedRealm` (`PROVEN↑`, preço pluralista).
  *O inventário de axiomas não se mexe:* `ContingentRealm` é `Realm` sem
  `bears_meaning`, e uma mudança de `structure` **não acrescenta axioma** — o
  registo continua em **24 declarados / 23 etiquetados**, `Tag: SEM` **6**,
  VOCAB 14, META 4. *O que muda é alcance, não número:* `PROVEN↑` continua em
  **40** (C350 sai, C367 entra) e `AxTwoSubjects` continua em **22** (idem), ao passo
  que *vocabulary-only* sobe **173 → 174**. O seis derivados — `a_created_realm_obtains`,
  `a_contingent_reality_obtains`, `reality_is_not_exhausted_by_the_ground`,
  `the_ground_is_necessary_and_the_realm_is_contingent`,
  `realm_existence_does_not_imply_realm_necessity`,
  `the_cosmos_existence_is_not_refutable` — passam todos a `{propext, Subject}`.
  **Não são linhas de exibição, e continuam por ledgerizar:** são afirmações com
  enunciado próprio, pelo que por convenção do corpus deveriam ter linha (C-id ou `—`), e
  não a têm. É por isso que não entram nas contagens acima — e é a dívida que
  `IMPROVE.md` mantém na lista de *catch-up* (12 afirmações de `CosmicExistence` por
  ledgerizar), agora com seis delas **livres**, o que as torna as melhores candidatas que
  essa lista já teve. Ver §0 critério 2 de `IMPROVE.md`.
  *Preço bem atribuído:* a ponte pluralista passa a pagar pela
  **significantidade** do reino (C367, C351, C352), não pela sua **existência**
  (C350). Rejeitar `AxTwoSubjects` leva a significantidade; **não** leva o reino.
  *O que continua por reclamar:* a produção (L3) — nenhuma relação `Creates` em Γ, e
  C110 continua a refutar que o fundamentamento implique um registo de criação.
  `Tag: TRANS` está declarado em
  `AGENTS.md` mas **não tem membros** (0). Nota: existia ainda um **quinto
  compromisso `Tag: META`** que nenhuma varredura de axiomas encontra, porque é
  um `def` e não um `axiom`: ◈ `AsietyFreedom.asietyFreedom_ofGroundFreedom`
  (`AsietyFreedom.lean:119`). *Contagens desta entrada: 24 declarados, 25 com o
  `AsietyFreedom`; superadas pelas entradas de 2026-09-28 abaixo.*
  **CORRECÇÃO (2026-09-28, promoção do limite F15):** `SemanticFinitude` deixou de ser
  um `def`-ponte e passou a axioma declarado `Tag: VOCAB` — o **27º** declarado
  (**26 → 27**; VOCAB **15 → 16**; SEM **6** e META **5** inalterados). É a primeira
  aplicação ao corpus da regra que o próprio corpus já enunciava — *o corpus não pode
  provar o que não vê* — a uma premissa com carga suficiente para precisar de distintivo:
  passa a ser um `axiom`, não um `def`. É também a primeira vez que o total de axiomas
  **sobe** por uma razão de *rigor* e não de *conteúdo novo* — nenhum enunciado foi
  acrescentado, nenhum status mudou, e as dez linhas C389–C398 e C400 mantêm
  `PROVEN` e o seu badge.
- `sorryAx` count across all modules: **0**.
- Verification: `lake build` green (36 jobs, seconds, Lean core only); zero
  errors, zero warnings.

### CORRECÇÃO (2026-09-28, três linhas do ledger eram invisíveis ao gerador)

`build_deduction.parse_gapmap` filtrava a primeira coluna das tabelas por
`^(C\d+|F\d+[ab]?|FAITH-\d+|Q7\.\d)$`. Três linhas reais da tabela *Deferred /
blocked* (§978) — `F1bUncond`, `EvalSettlement` e `OpenBridgeNormativity` — não
casavam com esse padrão e eram **descartadas em silêncio**: nunca chegavam ao
README, ao `kernel-audit.md`, ao inventário nem à contagem. Duas delas são
`BLOCKED`; uma BLOCKED que não aparece é indistinguível de uma BLOCKED que não
existe, e é o pior modo de falha possível num documento cuja força é a de não
esconder as suas próprias lacunas.

Isto foi encontrado ao construir o bloco de score da Fase 4, não por leitura: o
`scripts/gapmap_taxonomy.py --check` acusou `DRIFT count: GAPMAP states 51,
derived 52` sobre o bucket axiom-free. O desvio era real e a linha extra era
`EvalSettlement` (`ExecutiveDeliberativeFrontier.M_det`, pegada `[]` — verificada
no `formal/axiom_audit.json`, não transcrita).

Correção: o padrão passou a aceitar os três, e o ramo de 4 células deixou de
exigir prefixo `F`/`Q` (a forma da linha é a mesma para as três). Ao hacerlo
apareceram 13 duplicatas de C388–C400, porque a tabela de proveniência
`C-id | Decl | Pegada | Classe` sob o lote *semantic-finitude* repete os mesmos
identificadores noutra forma de coluna. Tabelas derivadas (cabeçalho com `C-id` ou
`Decl (…)` **e** uma coluna de pegada) são agora saltadas, e o inventário
subiu de **406 → 409** claims, sem perder nenhuma linha e sem duplicar nenhuma.
`make all` verde; `gapmap_taxonomy.py --check` volta a bater.

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
Executed in `Entity.lean`:

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
  stay **47** (Entity audit still 3); `sorryAx: 0`; `lake build` green,
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

> **⚠️ REFUTED 2026-09-24 (auditoria de axiomas + contramodelo Unit).** This batch record
> is kept as history, but its central claim is **false**: `AxTwoSubjects` was **not**
> retired — it is a live `Tag: META` axiom behind 15 PROVEN↑ claims (C28, C29, C40–C48,
> C54, C61, C74, F4) — and **`Person.twoPersonsFromSubject` (C73) is `BLOCKED`**, not a
> `{}` theorem: the Unit countermodel (`Subject := Unit`) settles that one act does not
> entail plurality, and the manufactured `Sum.inl`/`Sum.inr` witness was destroyed. The
> `Value.neverAlone`/`aloneExcluded` (C74) step likewise carries the plurality bridge
> (`{AxTwoSubjects, Means, Subject}`), not `{}`. Every T14 theorem is additionally
> *conditional* on the unproven `PluralityLovePrinciple`. Corrected statements are in the
> "Summary counts" block and at C73/C74; see `theorems/T14.txt` and MORAL.md §8c/§8f.

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
  - Creation (`CreationStructure`): independent; separated by the Separation Model (`necessary_ground_not_entails_contingent_creation`, rebuilt 2026-09-27 on a **populated** world — see C110 and Level 22).
- **Theological Dependency Ledger:** Machine-checked theorem `theological_dependency_ledger` proves the formal classification of all 10 transitions (PROVEN, DEFINITIONAL, SEMANTIC, METAPHYSICAL, COUNTERMODEL).
- **Single-Axiom Discipline:** A14 is the only new axiom. `lake build` green (40 jobs, 0 sorries).

## Level 4 — downstream metaphysical frontiers (`Logos.ConditionalTheology`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C108 | §28 | `ConditionalTheology.TrinitarianStructure` | PROVEN | `{}` |
| C109 | §28 | `ConditionalTheology.preceding_theory_not_entails_trinity` | DEMOTED | `{}` (demoted: 2-element Boolean cardinality artifact superseded by `monotheism_compatible_with_trinity`) |
| C110 | §28 | `ConditionalTheology.necessary_ground_not_entails_contingent_creation : ¬ (∀ Subj Ent World, GroundEntailsCreation Subj Ent World)` — **rebuilt 2026-09-27 on a populated world.** The predecessor instantiated the subject sort as `Empty` and discharged the negated conclusion by `nomatch` on the data field `created_subject`: it stated no contingency, never used the ground's `∀ p, p → Ground e p` premise, and had no creation relation to deny. The countermodel is now `ConditionalTheology.CreationWorld` — a necessary ground grounding *every* content, a subject that is contingent in the model's own modality, and a `Creates` relation kept **distinct from** `Ground` so that "grounds everything, creates nothing" is statable. `the_creation_countermodel_is_a_populated_contingent_world` machine-checks that the separating world contains a contingent subject, and `a_populated_contingent_world_can_also_carry_creation` is its positive counterpart, so this row reads as *undetermined*, never as "creation is impossible". **Not a model of Γ and not a candidate for reality**; the contingent realm's *existence* is C350 | COUNTERMODEL | `{}` |
| C111 | §28 | `ConditionalTheology.IncarnationalStructure` | PROVEN | `{}` |
| C112 | §28 | `ConditionalTheology.preceding_theory_not_entails_incarnation` | COUNTERMODEL | `{}` |

## Level 5 — Practical Ought and Personhood Retorsion (`Logos.OughtRetorsion`, `Logos.PersonhoodOntologyAudit`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C113 | §21 | `OughtRetorsion.self_grounded_ought_collapses` | PROVEN | `{Ought, Subject, Wills}` |
| C114 | §21 | `OughtRetorsion.self_grounded_assertion_incoherent` | PROVEN | `{Ought, Subject, Wills}` |
| C115 | §21 | `OughtRetorsion.HostileImpersonalModel.impersonal_model_satisfies_ought_without_person` | COUNTERMODEL | `{}` |
| C116 | §21 | `OughtRetorsion.asserting_no_personal_source_instantiates_only_judging_subject` | PROVEN | `{Means, Subject, Will, subjectWill}` |
| C117 | §21 | `OughtRetorsion.AxSecondPersonalAddress` | AXIOM | `{AxSecondPersonalAddress, Means, Ought, Subject, Will, subjectWill}` |
| C118 | §21 | `OughtRetorsion.second_personal_ought_derives_plurality` | PROVEN↑ | `{AxSecondPersonalAddress, Means, Ought, Subject, Will, subjectWill}` |
| C119 | §21 | `OughtRetorsion.lone_subject_excludes_second_personal_ought` | PROVEN↑ | `{AxSecondPersonalAddress, Means, Ought, Subject, Will, subjectWill}` |
| C120 | §12 | `Person.free_subject_is_person` — free subjecthood yields Personhood via the priced theorem (the only non-definitional content is the VOCAB law `will_individuation`) | PROVEN | `{Means, Subject, Will, subjectWill, will_individuation}` |
| C121 | §12 | `Person.person_iff_freeSubject` — as a priced theorem, never `Iff.rfl` | PROVEN | `{Means, Subject, Will, subjectWill, will_individuation}` |
| C122 | §12 | `PersonhoodOntologyAudit.opaque_person_failure_isolated_to_substantive_conjunct` | PROVEN | `{Means, Subject}` |
| C123 | §12 | `OughtRetorsion.faithful_contingent_person_fails_necessary_subject` | COUNTERMODEL | `{}` |

## Level 6 — Normative Order and Correctness (`Logos.NormativeOrder`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C137 | §8/§12 | `NormativeOrder.correct_implies_ought : Correct s p → Ought TruthNorm ⟨s, p⟩` — correctness generates agential deontic requirement under truth norm | PROVEN | `{Initiates, Means, State, Subject}` |
| C138 | §8/§12 | `NormativeOrder.incorrect_implies_oughtNot : Incorrect s p → OughtNot TruthNorm ⟨s, p⟩` — incorrectness generates agential deontic prohibition under truth norm | PROVEN | `{Initiates, Means, State, Subject}` |
| C139 | §8/§12 | `NormativeOrder.correctness_deontic_opposition : Act s p → DeonticOpposition (Correct s p) (Incorrect s p)` — deontic opposition between correctness and incorrectness derived via Ought/OughtNot | PROVEN | `{Initiates, Means, State, Subject, CL}` |
| C140 | §12/§15 | `NormativeOrder.claims_normative_correctness_derives_free_will : ClaimsNormativeCorrectness s p → Chooses s (Correct s p) (Incorrect s p) ∧ FreeWill s` — normative judicative stance derives choice and free will without AxJudicativeBipolarity; termina no mesmo tipo `GenuineNormativity` (C161) | PROVEN | `{Initiates, Means, State, Subject, CL}` |
| C141 | §12/§15 | `RetorsiveNormativity.normative_retorsion_derives_free_will : (∃ s, ClaimsNormativeCorrectness s NoGN) → ∃ s, FreeWill s` — performative retorsion of skeptical denial without AxJudicativeBipolarity; mesma estrutura `GenuineNormativity` (C161), rota-agnóstica para GN → Chooses → FreeWill | PROVEN | `{Initiates, Means, State, Subject, CL}` |
| C164 | §12/§15 | `RetorsiveNormativity.normative_stance_refutes_attack_without_axioms : (∃ s, ∃ p, ClaimsNormativeCorrectness s p) → ¬ NoGN` — o ataque estipulacionista ("GN é uma definição estipulada") é **inviável por lógica pura**: qualquer postura normativo-judicativa (um juízo real de correção sobre algum conteúdo) deriva `GenuineNormativity` sobre os polos judicativos Correct/Incorrect e refuta NoGN com **ZERO axiomas substantivos** — sem `AxJudicativeBipolarity`, sem novo SEM (INVIABLE.md) | PROVEN | `{Initiates, Means, State, Subject, CL}` |
| C165 | §12/§15 | `RetorsiveNormativity.attack_inviable_without_axioms : (∃ s, ∃ p, ClaimsNormativeCorrectness s p) → ¬ NoGN ∧ ∃ s, FreeWill s` — o ataque é **inviável com zero axiomas substantivos** nas três asas decisivas: (1) a tese é falsa — a postura refuta NoGN com zero axiomas substantivos; (2) um ataque proferido **na postura normativo-judicativa** não pode ser verdadeiro — nenhum sujeito afirma e crê NoGN simultaneamente (`cannot_claim_normative_denial_and_truth`, axiom-free); o gêmeo de voz fraca `cannot_coherently_claim_denial_and_truth` ainda custa `AxJudicativeBipolarity` (C106); (3) a cadeia não é vazia — co-apreensão é definicionalmente escolha (D7) e escolha é definicionalmente livre-arbítrio (D8), ambas `{Means, Subject}` pura lógica; o ataque é refutado exatamente ao custo de ser proferido como juízo — instanciar a postura é o dado do campo não vazio (INVIABLE.md §3), não teorema da voz nua (C166) | PROVEN | `{Initiates, Means, State, Subject, CL}` |
| C166 | §12/§15/§28 | `BipolarityRetorsion.voice_without_normative_stance : ∃ sig, ∃ s, ∃ p, VoiceSig sig s p ∧ ¬ sig.Means s (JudSigIncorrect sig s p)` — vox (ato + polo positivo) **não** força a postura normativo-judicativa em Γ primitivo: `M_oneway` profere `True` como correto sem significar `Incorrect () True` — testemunha máquina da lacuna pólo-dual (INVIABLE.md §1, nível 1⇄2): a postura é um dado (INVIABLE.md §3), não um teorema da voz; companheiro `voice_to_stance_not_forced_by_primitive_judicative_gamma` | PROVEN | `{}` |
| C167 | §28/§15 | `UndeniableNormativeDerivation.inanimate_universe_satisfies_bivalence_and_no_genuine_normativity : ∃ U, ∃ M, (¬N_T ∧ ¬N_F) ∧ ¬ ∃ s p q, Incompatible p q ∧ p ≠ q ∧ M s p ∧ M s q` — `M_inanimate` agora testemunha **diretamente** o nível 3 (INVIABLE.md §1): bivalência extensional consistente com a ausência da forma GN — `¬NoGN` incondicional (sem postura) não é derivável, veredito máquina direto; companheiro `extensional_bivalence_insufficient_for_genuine_normativity` | PROVEN | `{}` |

> Batch INVIABLE.md (2026-09-23) — prova formal de que o ataque estipulacionista contra `GenuineNormativity` é **inviável sob a postura normativo-judicativa** SEM axiomas: `normative_stance_refutes_attack_without_axioms` (C164) e `attack_inviable_without_axioms` (C165), pegada `{Initiates, Means, State, Subject, CL}` = zero axiomas substantivos. A retorsão é *guiada pela postura*: um ataque proferido **como juízo avaliativo** instancia a postura, e ser proferido = ser refutado — o campo não está vazio porque se tenta a prova já de dentro dele (objetar já é julgar; INVIABLE.md §3). Fronteiras honestas do trade-off de 4 níveis (INVIABLE.md §1): voz fraca → custa SEM `AxJudicativeBipolarity` (C106); postura completa → zero axiomas substantivos (C164/C165); voz sem postura → `M_oneway` (C166 − a postura é dado, não teorema da voz); `¬NoGN` incondicional (sem postura) não é derivável — testemunha direta `M_inanimate` agora (C167).

## Level 7 — Ontological Grounding of Normative Polarity (`Logos.PersonalNormativeGround`, `Logos.Person`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C142 | §12 | `Person.person_iff_freeIndependentWill` — by projections plus the definitional rational conjunct (no individuation law needed) | PROVEN | `{Means, Subject, Will, subjectWill}` |
| C144 | §8/§12 | `PersonalNormativeGround.person_grounds_normative_polarity : Person s → GroundsRightWrong s` — Personhood supplies the ontological ground-type required by Right/Wrong via its free will (freeWill route), without Act; s is the formal witness | PROVEN | `{Means, Subject, Will, subjectWill}` |
| C145 | §14/§15 | `PersonalNormativeGround.discovery_independent_of_grounding` | PROVEN | `{Means, Subject}` |
| C146 | §8/§12 | `PersonalNormativeGround.HostileModels.model_b_separation` | COUNTERMODEL | `{}` |
| C416 | §8/§12 | `PersonalNormativeGround.HostileModels.model_d_asymmetric_leaves_ofGround_standing` — **RESULTADO NEGATIVO DA FASE 6 (D1′ confirmado como decisão semântica, não como refactor pendente).** O `asymmetric` de `GenericGroundingRelation` proíbe todo `Entity.ofAtom n`, mas `Entity` tem **três** construtores (`Entity.lean:23-26`) e `ofGround` sobrevive a `asymmetric`; e `ofGround` não é `EntityOf s` para nenhum `s`, logo não é `PersonalEntity`. O terceiro conjuncto mostra que `personal_ground` também não o salva: a sua hipótese `g = EntityOf s` é insatisfazível aí. Os dois campos selantes **não são redundantes**. Isto **não** promove C228, que continua `BLOCKED`; confirma que a remoção de `explanatory` seria insegura, e por isso D1′ fica. | COUNTERMODEL | `{Means, Subject, Will, subjectWill}` |
| C154 | §28/§29 | `PersonalNormativeGround.forward_modus_ponens_derivation : RightWrongAt s p q → Person s ∧ GroundsRightWrong s` — strictly forward constructive deduction chain via modus ponens (A₀ ⇒ ... ⇒ P ⇒ G); the P-step is the priced theorem (via `will_individuation`), the G-step the definitional free-will route | PROVEN | `{Means, Subject, Will, subjectWill, will_individuation}` |
| C155 | §28/§29 | `PersonalNormativeGround.person_grounds_original_normative_datum : RightWrongAt s p q → Person s ∧ GroundsRightWrong s` — the derived subject s instantiates the personal ontological ground of datum A₀(s, p, q) | PROVEN | `{Means, Subject, Will, subjectWill, will_individuation}` |
| C156 | §28/§29 | `PersonalNormativeGround.non_reversal_discovery_and_grounding` — discovery runs forward (A₀ ⇒ P ⇒ G) while personal ground-type is the derived conclusion | PROVEN | `{Means, Subject, Will, subjectWill, will_individuation}` |
| C162 | §12 | `Person.freeIndependentWill_iff_thomisticCore : FreeIndependentWill s ↔ ThomisticPersonCore s` — free, independent will is equivalent to the explicit Thomistic person core (`IndividualSubstance ∧ RationalNature ∧ DominionOverActs`; Boethius: individual substance of a rational nature; Aquinas ST I q.29 a.3, q.83: dominion over own acts); the formal correspondence that defeats the arbitrary-redefinition charge; zero new axioms | PROVEN | `{Means, Subject, Will, subjectWill}` |
| C163 | §12 | `Person.person_iff_thomisticCore : Person s ↔ ThomisticPersonCore s` — personhood IS the Boethius–Aquinas person core, honestly `rfl` since that is the definition (emenda 2026-09-25) | PROVEN | `{Means, Subject, Will, subjectWill}` |
| C168 | §24a/§28/§29 | `PersonalNormativeGround.groundsRightWrong_iff_forced_content : GroundsRightWrong s ↔ ForcedGroundContent s` — transparência: o predicado de fundamentação (registo de campo único, sem `person`, sem `dependence`) é abreviação definicional do facto agencial `ForcedGroundContent s := ∃ p q, Chooses s p q` escrito inteiramente no vocabulário ANTERIOR (sem o símbolo `GroundsRightWrong`); sem campo oculto, sem átomo opaco — o predicado é determinado, não estipulado | PROVEN | `{Means, Subject}` |
| C169 | §24a/§28/§29 | `PersonalNormativeGround.forced_content_of_person : Person s → ForcedGroundContent s` — projecção do conjunto do domínio (`Person s → FreeWill s := ∃ p q, Chooses s p q`); a pessoalidade do fundamento é o teorema com preço `grounding_right_wrong_entails_person` (via `will_individuation`), nunca um campo | PROVEN | `{Means, Subject, Will, subjectWill}` |
| C170 | §24a/§28/§29 | `PersonalNormativeGround.grounding_forced_by_preceding_facts : RightWrongAt s p q → GroundsRightWrong s` — o predicado é forçado pelo DADO A₀ sozinho, antes de a Pessoa ser atingida: sem hipótese `Person` no instante da fundamentação (a rota via Pessoa, pelo teorema de descoberta, carrega `will_individuation`) | PROVEN | `{Means, Subject, Will, subjectWill, will_individuation}` |
| C171 | §24a/§28/§29 | `PersonalNormativeGround.grounding_forced_at_datum : RightWrongAt s p q → GroundsRightWrongAt s p q` — alinhamento indexado: o fundamento no próprio par ⟨p, q⟩ do dado (normatividade = o dado, substrato = o mesmo par) — nenhuma testemunha pessoal é fabricada | PROVEN | `{Means, Subject}` |
| C221 | §12 | `Person.freeWill_implies_person : FreeWill s → Person s` — HEADLINE (AC2): o livre-arbítrio implica a pessoalidade **como teorema**, nunca `Iff.rfl`; a prova assembla os três conjunctos boécio-aquinianos, e todo o seu conteúdo não-definicional é a lei VOCAB declarada `will_individuation` (a substância individual vem dessa lei; a natureza racional e o domínio dos próprios atos são definitionais a partir do livre-arbítrio) | PROVEN | `{Means, Subject, Will, subjectWill, will_individuation}` |
| C222 | §8/§12 | `PersonalNormativeGround.genuineNormativity_implies_person : GenuineNormativity s p q → Person s` — HEADLINE (AC3): a cadeia exacta do crítico como teorema; compõe `indubitable_normative_free_will` (normatividade genuína → livre-arbítrio, `{Means, Subject}`) com o teorema com preço `free_subject_is_person` (via `will_individuation`). Nenhum passo é um desdobramento | PROVEN | `{Means, Subject, Will, subjectWill, will_individuation}` |
| C223 | §24a/§28/§29 | `PersonalNormativeGround.freeWill_grounds_right_wrong : FreeWill s → GroundsRightWrong s` — E2: o livre-arbítrio satisfaz a especificação ontológica do fundamento; o registo tem campo único e `FreeWill s` É `∃ p q, Chooses s p q`, portanto o passo é definitionally — e **nenhuma hipótese `Person` é tomada ou necessária** | PROVEN | `{Means, Subject}` |
| C224 | §24a/§28/§29 | `PersonalNormativeGround.grounding_right_wrong_entails_person : GroundsRightWrong s → Person s` — E2: a pessoalidade do fundamento é um **teorema com preço**, não um campo do registo; compõe o passo definitionally `agential_foundation → FreeWill` com `freeWill_implies_person` (custo: a lei nomeada `will_individuation`, divulgada) | PROVEN | `{Means, Subject, Will, subjectWill, will_individuation}` |
| C225 | §24a/§28/§29 | `PersonalNormativeGround.groundsRightWrongAt_entails_person : GroundsRightWrongAt s p q → Person s` — E1b: o gémeo indexado do anterior; a forma indexada também tem a pessoalidade **só por teorema**, nunca por campo | PROVEN | `{Means, Subject, Will, subjectWill, will_individuation}` |
| C226 | §12 | `PersonhoodOntologyAudit.freeWill_without_person : Vocab.FreeWill SharedWillModel true ∧ ¬ Vocab.Person SharedWillModel true` — AC9′: a separação é **machine-checked**, não afirmada; um sujeito com livre-arbítrio genuíno cujo domínio de vontade é partilhado (`WillOf := fun _ => ()`, `Subj := Bool`) **não** é pessoa. Computado, não estipulado, e a pegada é `{}` porque o modelo apenas interpreta o vocabulário de quatro campos `{Subject, Means, Will, subjectWill}` e **withholds** a lei `will_individuation` (é exactamente esse withholding que torna o contramodelo admissível) | PROVEN | `{}` |
| C227 | §12 | `PersonhoodOntologyAudit.freeWill_person_iff_individuation (M) (s) : Vocab.FreeWill M s → (Vocab.Person M s ↔ ∀ s', M.WillOf s' ≠ M.WillOf s)` — a precisão: dada a liberdade, ser pessoa **equivale** à individuação numérica desta vontade. Diz no kernel, sem desdobramento definicional, que a redução `Person ↔ FreeWill` não é uma identidade de significado mas um teorema cujo conteúdo não-definicional é exactamente `will_individuation` — e `SharedWillModel` (C226) é o contramodelo machine-checked dessa redução | PROVEN | `{}` |
| C228 | §24a/§29 | `PersonalNormativeGround.normative_ground_is_personal (g) (hGr : GenericGroundsRightWrong g) : PersonalEntity g` — **BLOCKED**: a pessoalidade do fundamento NÃO vem de um campo, mas continua a ser uma **projecção de campo em três passos** (1. `grounds_normativity` dá a `GenericGroundingRelation`; 2. `explanatory` força `g = EntityOf s`; 3. `personal_ground` dá `Person s`). Os dois campos que selam a Pierce-negociação são nomeados como bloqueadores (decisão D1′, adiada): `explanatory` impede qualquer contramodelo ao forçar todo fundamento a ser `EntityOf s`, e `asymmetric` proíbe por definição o contramodelo do átomo. Falta a lemma nomeada, verbatim de `base.txt:1345-1346`: `#9 Ground(e, personal) → Personal(e)` e o seu alvo #10. BLOCKED, não deferido em silêncio | BLOCKED | `{Means, Subject, Will, subjectWill}` |
| C229 | §12 | `PersonalNormativeGround.rightwrong_gives_rational_domination (s) (h : RightWrong s) : RationalNature s ∧ DominionOverActs s` — **dois terços da pessoa sem nenhum axiom**: o endereço normativo genuíno já traz `RationalNature` (sujeito intencional + capacidade discursiva, ambos projeções de `Means`) e `DominionOverActs` (definitionally `FreeWill`). Desvela, a preço zero, que dois dos três conjunctos de `ThomisticPersonCore` não precisam da lei de individuação | PROVEN | `{Means, Subject}` |
| C230 | §12 | `PersonalNormativeGround.person_from_rightwrong_iff_individuation (s) (h : RightWrong s) : Person s ↔ IndependentWill s` — o **preço localizado e exacto**: dada o datum normativo, ser Pessoa **equivale** a esta vontade ser individualmente numerada, porque C229 já fornece os outros dois conjunctos de graça. Analogue exacto de C227 para o ponto de entrada `RightWrong`. Sendo um `Iff` e não uma derivação, esta theorem **não** depende de `will_individuation`: ela **caracteriza** o preço em vez de o pagar | PROVEN | `{Means, Subject, Will, subjectWill}` |
| C231 | §12 | `PersonhoodOntologyAudit.rational_domination_without_person : Vocab.RationalNature SharedWillModel true ∧ Vocab.DominionOverActs SharedWillModel true ∧ ¬ Vocab.Person SharedWillModel true` — **necessidade**: um sujeito pode satisfazer *ambos* os conjunctos baratos (natureza racional + domínio sobre os seus actos) e ainda assim **não** ser Pessoa. Prova machine-checked que os dois terços **não** alcançam a pessoalidade: `will_individuation` não é despesa evitável, é o preço exacto e mínimo de `RightWrong ⇒ Person` | PROVEN | `{}` |
| C232 | §24a/§29 | `PersonalNormativeGround.grounding_carries_dependence_free (s) (hGround : GroundsRightWrong s) : ∀ s', RightWrong s' → RationalNature s' ∧ DominionOverActs s'` e `PersonalNormativeGround.grounding_carries_dependence (s) (hGround : GroundsRightWrong s) : ∀ s', RightWrong s' → Person s'` — o **conteúdo de dependência restaurado como teorema**, não como campo: o campo `dependence : ∀ s', RightWrong s' → Person s'` removido em 2026-09-25 é agora *derivado*. A metade livre (preço zero) devolve a `GroundsRightWrong` conteúdo implicado não-vacuoso, que é exactamente o que a redução a `FreeWill` tinha perdido; a metade paga completa a derivação com o preço declarado. O preço é provadamente mínimo por C230+C231 | PROVEN | `{Means, Subject}` / `{Means, Subject, Will, subjectWill, will_individuation}` |

> Batch SEMANTIC-INDEPENDENCE (2026-09-25) — a refactor de independência semântica fecha as três objecções C1/C2/C3 sem acrescentar um único axioma (conjunto declarado 22 = 22, AC10′). (i) **P1 — personhood vs. livre-arbítrio:** `Person` passou a ser o critério boécio-aquiniano completo (`Person s := ThomisticPersonCore s`), e a redução a livre-arbítrio é o teorema com preço C221/C222 (via `will_individuation`), não uma definição. A separação é machine-checked e exacta: C226 computa `FreeWill ∧ ¬Person` **com vontade não individuada**, e C227 declara o limite — pessoa **mais** vontade individuada **mais** racionalidade discursiva. Um modelo que importasse `Will`/`subjectWill` de Γ não pode exprimir esse contra-exemplo, porque `will_individuation` é justamente a lei em disputa; é por isso que o contramodelo tem **quatro campos** e nunca é descrito como "um modelo de Γ". (ii) **P2 — grounding-baking:** C223 é o único construtor de `GroundsRightWrong` a partir do livre-arbítrio e **não toma `Person`**; o registo de campo único eliminou `person`/`dependence`, e a pessoalidade é só por teorema (C224, e o gémeo indexado C225). O contraste honesto: `GroundsRightWrong` é agora *definitionally* `FreeWill` (C168), pelo que todo o conteúdo de fundamentação substantivo reside na relação genérica — que permanece **BLOCKED** em C228 com a lemma nomeada verbatim. (iii) **P3 — nomeado na ontologia:** `Entity.ofGround` fica (decisão §47.2) mas tagged, priced e badged ◈ no registo de `formal/Logos/Stipulations.lean` (3 stipulações, 9 dependentes verificados por `scripts/audit_stipulations.py`). Nada se perde no ledger de estados: 43 BLOCKED / 15 DEFERRED / 18 PROVEN / 41 PROVEN↑ / 5 AXIOM inalterados; 0 axiomas substantivos em todos os 115 footprints que cresceram.

> Batch PRICE-LOCALIZATION (2026-09-26) — fecha a segunda objecção de P2: a redução de `GroundsRightWrong` a `FreeWill` tornara o vocabulário de fundamentação *vacuoso*, e o preço de `will_individuation` aparecia como linha de custo sem ever ser caracterizado. Quatro teoremas aditivos, zero axiomas novos (22 = 22, AC10′). (i) **Dependência restaurada como teorema, não como campo:** o campo `dependence : ∀ s', RightWrong s' → Person s'` removido em 2026-09-25 é agora derivado em duas metades — `grounding_carries_dependence_free` (`{Means, Subject}`, **zero axiomas**) devolve a `GroundsRightWrong` um conteúdo *implicado* não-vacuoso, e `grounding_carries_dependence` completa a derivação com o preço declarado (C232). (ii) **Dois terços de graça:** `rightwrong_gives_rational_domination` (C229, `{Means, Subject}`) mostra que o endereço normativo genuíno já fornece `RationalNature` *e* `DominionOverActs` — dois dos três conjunctos de `ThomisticPersonCore` sem a lei de individuação. (iii) **O preço é exacto:** `person_from_rightwrong_iff_individuation` (C230, `{Means, Subject, Will, subjectWill}`) dá `Person s ↔ IndependentWill s` sob `RightWrong s`; sendo um `Iff`, **caracteriza** o preço em vez de o pagar — a lei `will_individuation` não consta da sua pegada. (iv) **O preço é necessário:** `rational_domination_without_person` (C231, `{}`) prova em `SharedWillModel` que um sujeito com natureza racional *e* domínio sobre os seus actos **não** é Pessoa. Conclusão: `will_individuation` é o preço **exacto e mínimo** de `RightWrong ⇒ Person`, e nenhuma técnica de prova o remove sem repor a deflação de `Person` (a `Person := FreeSubject` de HEAD^, tipo "stronger"). Nenhuma afirmação existente foi enfraquecida; o batch é puramente aditivo.
> Batch FORCING (2026-09-23; emenda 2026-09-25) — demonstração formal de que `GroundsRightWrong` NÃO é um predicado formal ad hoc construível uma vez obtida a Pessoa:
 (i) transparência (`groundsRightWrong_iff_forced_content`, C168) — o registo de campo único é definicionalmente idêntico ao facto agencial `∃ p q, Chooses s p q` no vocabulário anterior à fundamentação; (ii) toda a Pessoa satisfaz o conteúdo forçado (`forced_content_of_person`, C169) por projecção do domínio, e a pessoalidade do fundamento é o teorema com preço `grounding_right_wrong_entails_person` (via `will_individuation`); (iii) forçamento pelo dado (`grounding_forced_by_preceding_facts`, C170) com alinhamento indexado ao par ⟨p, q⟩ do próprio dado (`grounding_forced_at_datum`, C171), sem hipótese `Person`. Zero axiomas substantivos; núcleo agencial pegada `{Means, Subject}`, rotas via Pessoa com `Will, subjectWill, will_individuation`; contraste honesto: a leitura de relação externa (`GroundProp`, `AxPersonalNormativeGround`) foi retirada e o registo (record) é transparente — nada é estipulado no instante P⇒G.

> Batch PERSON.md (2026-09-23) — correspondência Boécio–Aquinas explícita + piso racional derivado: `Rational` deixou de ser o kind-pred analítico `:= True` e passou a piso DERIVADO `Rational s := ∃ p, Means s p` (`{Means, Subject}`, valor efetivo da definição = `Intentional`); a natureza racional operativa da pessoa é `RationalNature := Intentional ∧ FreeWill` (Person.lean), nunca o piso truncado. `ThomisticPersonCore` = substância individual (vontade numericamente individuada) + natureza racional (apreensão + deliberação) + domínio dos próprios atos (livre-arbítrio genuíno) — equivalência total `Person ↔ FreeIndependentWill ↔ ThomisticPersonCore` (C162/C163), pegada zero axiomas novos, idêntica ao feixe de C142. Contramodelos hostis intactos: `SubstantivePersonhood`` (Ratio próprio) e `freewill_not_entails_rationality` (RazõesFor local) não importam `Logos.Agency.Rational`.

## Level 8 — Personal Grounding of All Reality (`Logos.PersonalGroundOfReality`)

The headline of the deduction: **the Person already supports the reality of Right.**
Unconditional, no free premise, zero substantive axioms; the performative datum is
internalized as an implication. "Necessary" = the order is necessary and its basis is of a
free personal nature (retorsive-transcendental necessity of the personal ground-type), NOT
an entity-level modal claim that a contingent individual exists in every possible world
(Claim E stays annotated, THIS_IS_PERSONAL.md §12.1).

Γ-reality is the domain of what exists / is the case; the objective normative/truth order
governs only the objective correctness of propositions about that domain. "The Person
supports the reality of Right" therefore means the objective correctness/normativity
structure (RightWrong-reality) has a personal ontological ground-type — it is NOT a claim
that the ground creates existents, makes evil exist, or morally legitimizes what exists
(no causal principle `∀ x, Exists x → CausedByGround x` is introduced).

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C147 | §28/§29 | `PersonalGroundOfReality.deny_right_self_contradicts : ¬ ∃ s, ClaimsCorrect s NoRight ∧ NoRight` — denying Right is performatively self-contradictory (retorsion boundary) | PROVEN | `{Initiates, Means, State, Subject}` |
| C148 | §28/§29 | `PersonalGroundOfReality.reality_of_right : EstablishedRightWrong ∧ (∀ p, T p ∨ IsFalse p) ∧ NecessaryNormativeOrder` — Right/Wrong is real, bivalence holds, and the order is necessary | PROVEN | `{Initiates, Means, State, Subject, CL}` |
| C149 | §28/§29 | `PersonalGroundOfReality.judicative_stance_forces_person : ∀ s p, ClaimsNormativeCorrectness s p → Person s` — the judicative stance forces the Person (via the priced discovery theorem) | PROVEN | `{Initiates, Means, State, Subject, Will, subjectWill, will_individuation, CL}` |
| C150 | §28/§29 | `PersonalGroundOfReality.person_grounds_normative_order : ∀ s, Person s → GroundsRightWrong s` — Personhood supplies the ontological ground-type for all subjects without Act, via its free will | PROVEN | `{Means, Subject, Will, subjectWill}` |
| C151 | §28/§29 | `PersonalGroundOfReality.the_person_supports_the_reality_of_right` — HEADLINE: deny-Right is contradictory; Right/Wrong is real and necessary; the normative datum forces the Person (priced step); the ground is personal in kind via the priced personalness theorem. Unconditional, closed Prop. | PROVEN | `{Initiates, Means, State, Subject, Will, subjectWill, will_individuation, CL}` |
| C152 | §28/§29 | `PersonalGroundOfReality.personal_ground_of_right_exists (hDatum : ∃ s, RightWrong s) : ∃ s, Person s ∧ NecessaryNormativeOrder ∧ GroundsRightWrong s` — existential corollary, datum-guarded: a personal ground exists | PROVEN | `{Initiates, Means, State, Subject, Will, subjectWill, will_individuation}` |
| C153 | §28/§29 | `PersonalGroundOfReality.person_yields_personal_grounding_of_reality` — instance form (datum-guarded): the derived Person witnesses the personal ground of the objective normative/truth order governing judgments about reality (grounding correctness about reality; not creation of existents) (historical compatibility alias: `present_act_yields_personal_grounding_of_reality`) | PROVEN | `{Initiates, Means, State, Subject, Will, subjectWill}` |
| C172 | §28/§29 | `PersonalGroundOfReality.personal_ground_of_right_wrong : ∀ s, RightWrong s → Person s` — the 'simple thing' in one universal: wherever Right/Wrong is real, its ground-type is personal; via the priced discovery theorem (`normative_datum_forces_person`) | PROVEN | `{Means, Subject, Will, subjectWill, will_individuation}` |

> **GroundsRightWrong package (§4.3; emenda 2026-09-25):** `GroundsRightWrong` is a single-field RECORD —
> `agential_foundation := ∃p q, Chooses s p q` (transparent, C168; NO `person`,
> NO `dependence` fields — personalness is the priced theorem
> `grounding_right_wrong_entails_person`, C169/E2). `model_b_separation`
> (`PersonalNormativeGround.lean:673-675`) shows a concrete witness where an
> *arbitrary external* `GroundProp` is NOT forced: `Entity := Bool`,
> `GroundProp := fun e _ => e = false` — an impersonal atom satisfies it while the
> free person's entity fails. The kernel proves the package INSTANCE, not a
> general reduction of ontological grounding.

### Claim E status (annotated, not a theorem)

`∃ g, NecessaryEntity g ∧ Personal g ∧ GroundOfReality g` — beliefs that a
**necessary, personal ground of all reality** exists. **NOT derivable** from the
VOCAB-only spine: entity-level modal necessity needs `AxGlobalGround` (SEM) and
entity-level personal grounding needs `AxPersonalGround` (META). Counter-theorems:
`deterministic_transcendental_subject_*`, `retorsion_fails_against_no_necessary_entity`,
`necessary_normative_truth_not_implies_ground`, `normative_ground_independence_model_satisfiable`.
Record only; never re-axiomatize.

### Uniqueness / monotheism (nota §4.7) — ESTABLECIDO (com uma hipótese nomeada)

**CORRECÇÃO (2026-09-27, batch FOUNDATIONAL-UNICITY-REPAIR).** Este bloco afirmava antes
*"Nenhuma afirmação de unicidade/monoteísmo é provada no kernel"*. Isso era **falso** a partir de
C320, e a frase foi removida. O que o kernel estabelece hoje:

- **Existência — incondicional.** `FoundationalUnicity.ofGround_universal_modal_ground` (C319)
  prova que `Entity.ofGround` é um `UniversalModalGround`.
- **Unicidade — sob uma única hipótese nomeada.** `FoundationalUnicity.exactly_one_universal_modal_ground`
  (C320) prova `∃ g, UniversalModalGround g ∧ (∀ g', UniversalModalGround g' → g' = g)`, com todo o
  preço numa linha: `hNoTotal : ∀ s : Subject, ∃ p, ¬ Means s p` (= **F15**).

Isto **não** contradiz o countermodel que este bloco registava. Os dois falam de **predicados
diferentes**, e ambos são verdadeiros ao mesmo tempo:

| Predicado de unicidade | Onde | Estado |
|---|---|---|
| `UniversalModalGround` — *o único solo de fundamentação modal* | `FoundationalUnicity.lean` | **PROVEN** sob F15 (C320) |
| `UniqueExists S.NecessaryEntity` sobre `PluralNecessaryEntitiesSignature` | `TheologicalModalHardening.lean:406-414` | **COUNTERMODEL** (testemunha `plural_necessary_entities_consistent` L391-403) |
| `universal_ground_unique` | `NecessaryPersonalGround.lean:24` | difere de ambos |

E o monoteísmo **ao nível da Pessoa** continua **não** estabelecido: C212
(`FoundationalUnicity.unicity_does_not_force_unitarian_monad`, `{}`) prova que a unicidade do solo
*não* força um mônada unitário, e a Trindade (F6) continua bloqueada por C228. Monoteísmo é, com
precisão: **solo de fundamentação modal único, provado condicionalmente; unicidade de pessoa, em
aberto.**

---

## Level 9 — Reality-Hook & Moral Frontier (`RealityHookAudit`, `MoralFrontierAudit`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C173 | §28/§4 | `RealityHookAudit.content_reality_hook : ∀ p, (∃ s, Correct s p) → p` — wherever a judgment is correct, its content is the case (reality-hook, vocabulary-only, zero substantive axioms) | PROVEN | `{Initiates, Means, State, Subject}` |
| C174 | §28/§4 | `RealityHookAudit.disconnection_thesis_unjudgeable_as_correct : ¬ ∃ s, Correct s D` (+ `def D`, `D : Prop := ¬ ∀ s p, Correct s p → p`) — "propositional right/wrong has nothing to do with reality" is never correctly judged | PROVEN | `{Initiates, Means, State, Subject}` |
| C175 | §28/§5 | `MoralFrontierAudit.epistemic_normativity_without_practical_obligation : (∃ s, RightWrongStar s) ∧ (¬ ∃ r s a, OughtStar r s a)` — the `M_amoral` faithful model satisfies the epistemic agential reality-hook with zero practical binding; moral meaning is machine-separated (F3's countermodel row-of-record) | COUNTERMODEL | `{}` |
| C176 | §28/§5 | `Value.no_help_obtains : ¬ ∃ s t, s ≠ t ∧ Helps s t` — **the bare value layer is empty**: `BearingOf` is a closed def returning `unbearing`, so `Affects`/`Helps`/`Harms` are refutable for *every* pair (`helps_unobtainable`, `harms_unobtainable`, `affects_unobtainable`). The machine proof that benevolence does **not** obtain in the pure theory — and hence that any inhabited moral pole must pay a disclosed bridge | PROVEN | `{Subject}` |
| C177 | §28/§5 | `Value.AxBenevolentBearingObtains : ∃ s t, s ≠ t ∧ Person t ∧ Helps s t` — **META bridge** (poem P6 "ajuda" as world-fact, not only definition): some person is *actually* helped. Declared, tagged `META`, priced in the footprint; not forced (C176 is its countermodel). The one honest price of the positive moral close | AXIOM | `{Means, Subject, AxBenevolentBearingObtains}` |
| C178 | §28/§5 | `MoralFrontierAudit.moral_good_obtains : ∃ s a, Good s a` — **the positive close of F3**: the moral pole is a *fair definition* (`Good s a := ∃ t ≠ s, Person t ∧ Helps s t ∧ ¬ Harms s t` — helpfulness toward the other, per the declared content) and it **obtains** under C177. `Good` itself is vocabulary-only (`{Means, Subject, Will, subjectWill}` — `Person` in the definiens); the inhabitation carries the bridge openly | PROVEN↑ | `{Means, Subject, Will, subjectWill, AxBenevolentBearingObtains}` |

> Batch REALITY-HOOK & MORAL-FRONTIER (2026-09-24): a tese cética "certo/errado
> proposicional nada tem a ver com realidade" é **refutada no kernel** —
> `correct_tracks_reality` (`Correct s p → p`, vocab-only `{Initiates, Means, State,
> Subject}`, zero axiomas substantivos) torna `D` incorretamente-julgável
> (`disconnection_thesis_unjudgeable_as_correct`, C174). O mesmo método transferido
> para o domínio moral **inverte o veredito**: o polo prático `Ought`
> (`OughtRetorsion.lean:72`) é um postulado declarado, não uma definição, e o modelo
> `M_amoral` instancia toda a normatividade agencial epistémica sem nenhuma obrigação
> prática (`epistemic_normativity_without_practical_obligation`, C175, `{}`) — F3 vira
> **fronteira de contramodelo** 🧱, separada, não lacuna. *(A frase original deste
> bloco — "o fecho positivo custa o datum SEM §5.4 (`Good`/`Evil`)" — foi
> **superada** pelo fecho efetivamente implementado: ver a nota "Positive close of
> the moral frontier" abaixo, C176–C178.)* A separação é provada nunca-forçada por
> `moral_pole_postulate_is_not_a_consequence` (`{Initiates, Means, State, Subject}`).

> Machine-witness note (kernel fact, 2026-09-24 — not a derivation gap): the local model
> `M_amoral` (`S := Unit`, `OughtStar := False` everywhere, `CorrectStar` identity hook)
> satisfies `CorrectStar s p → p` plus an instantiated `<Subject, Means, State,
> Initiates>` vocabulary, so `epistemic_normativity_without_practical_obligation` holds
> with **zero axioms** (`{}`); `amoral_disconnection_is_judgeable_as_correct : ∃ s,
> CorrectStar s AmoralistThesis` is the formal flip — in contrast with epistemic `D`, the
> amoralist thesis is true-in-the-model, hence correctly judgeable.

> **Positive close of the moral frontier (batch OTHER-FIRST, 2026-09-24; C176–C178).**
> The separation C175 stays `{}` forever — normativity alone never forces a moral pole.
> But the positive pole no longer has to be *postulated*. Axiom-audit first settled two
> facts: (i) the bare value layer is **empty** — `BearingOf` is a closed def returning
> `unbearing`, so `Affects`/`Helps`/`Harms` are refutable for every pair (`C176`
> `no_help_obtains`), which is exactly why the fair `Good` could not obtain without a
> bridge; and (ii) the `Love.lean` "plurality-discharge" header was **false** (T14 still
> rests on `AxTwoSubjects` + an unproven `PluralityLovePrinciple` — the header is now
> corrected in place). The honest close (MORAL.md §8b fairness law — a consequence of a
> *fair* definition is declared, not smuggled): `Good` becomes a **fair definition**
> (helpfulness toward the other) and **obtains** (`moral_good_obtains`, `C178`,
> `PROVEN↑`) under ONE disclosed, tagged, priced META bridge `AxBenevolentBearingObtains`
> (`C177`, "some person is actually helped"). `Good` the *definition* is vocabulary-only
> (`{Means, Subject}`) — the definition smuggles nothing; only its *inhabitation* pays the
> declared bridge, openly. The negative pole `Evil` is deliberately **left** as a declared
> SEM datum (its fair reading is uninhabited without a parallel "some harm occurs" bridge,
> which was not commissioned) — asymmetry recorded, not hidden.

---

## Level 10 — Proof-Presentation Retorsion & Syntactic Checker Audit (`Logos.ProofPresentationRetorsion`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C187 | §28/§1 | `ProofPresentationRetorsion.syntactic_validity_without_subject_or_normativity : ∃ Universe MeansRel d, Checker d = true ∧ (∀ s p, ¬ MeansRel s p) ∧ ¬ ∃ _s, True` — mechanical syntax checking succeeds in an uninhabited universe (`Subject = Empty`), proving syntactic proof validity alone never entails subjects or normative judgments | COUNTERMODEL | `{}` |
| C188 | §28/§1 | `ProofPresentationRetorsion.checker_validity_does_not_force_normative_stance : ∃ sig s d, Checker d = true ∧ VoiceSig sig s (conclusion d) ∧ ¬ sig.Means s (JudSigIncorrect sig s (conclusion d))` — in `JudicativeSig` with `M_oneway`, a derivation is mechanically checked and voiced as correct yet grasp of the negative pole fails | COUNTERMODEL | `{}` |
| C189 | §28/§1 | `ProofPresentationRetorsion.presents_as_sound_implies_claims_normative_correctness : PresentsAsSound s d → ClaimsNormativeCorrectness s (DerivationSound d)` — presenting a derivation as sound constitutively instantiates the normative-judicative stance | PROVEN | `{Initiates, Means, State, Subject}` |
| C190 | §28/§1 | `ProofPresentationRetorsion.presents_as_sound_derives_personhood : PresentsAsSound s d → CommittedChoice s (DerivationSound d) (Correct s (DerivationSound d)) (Incorrect s (DerivationSound d)) ∧ Chooses s (Correct s (DerivationSound d)) (Incorrect s (DerivationSound d)) ∧ FreeWill s ∧ FreeSubject s ∧ Person s` — an agent presenting a derivation as sound instantiates committed choice, free will, free subjectivity, and personhood | PROVEN | `{Initiates, Means, State, Subject, CL}` |
| C191 | §28/§1 | `ProofPresentationRetorsion.proof_criticism_nihilism_self_refuting : ClaimsCorrect s NoRight → NoRight → False` — any skeptic attempting to deny objective correctness in formal derivations by claiming normative nihilism refutes itself constructively | PROVEN | `{Initiates, Means, State, Subject}` |

> Batch PROOF-PRESENTATION-RETORSION (2026-09-25): C187 and C188 are machine-checked
> countermodels establishing that mechanical proof verification (`Checker d = true`)
> does NOT mathematically force an agential normative stance. C187 proves this in an
> uninhabited universe (`Subject := Empty`, `{}`), while C188 proves it via `M_oneway`
> where a derivation is voiced as correct without grasping the negative error-alternative.
> C189 and C190 prove that the *argumentative presentation* of a derivation as sound
> (`PresentsAsSound s d`) instantiates the full normative-judicative stance
> (`ClaimsNormativeCorrectness`), committed choice, free will, and personhood with
> zero substantive axioms (`{Initiates, Means, State, Subject, CL}`). C191 formalizes
> dialectical retorsion against skeptical dismissal of formal correctness.

---

## Level 11 — Classical Divine Simplicity & Ontological Transcendence (`Logos.DivineSimplicity`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C192 | §28/CHARACTERISTICS | `DivineSimplicity.composite_entity_fails_simplicity : ∃ Ent HasComp Simp, (∀ e, Simp e → ¬ HasComp e) ∧ (∃ e, HasComp e ∧ ¬ Simp e)` — a composite entity with internal components fails Divine Simplicity | COUNTERMODEL | `{}` |
| C193 | §28/CHARACTERISTICS | `DivineSimplicity.ofGround_has_no_internal_components : ¬ HasInternalComponent Entity.ofGround` — Entity.ofGround has zero internal component decomposition (is an atomic, nullary ontological constructor) | PROVEN | `{Subject}` |
| C194 | §28/CHARACTERISTICS | `DivineSimplicity.ofGround_undivided_meaning : UndividedMeaning Entity.ofGround` — Entity.ofGround possesses undivided, uniform intentional capacity across reality | PROVEN | `{Means, Subject}` |
| C195 | §28/CHARACTERISTICS | `DivineSimplicity.ofGround_transcendent : TranscendentGround Entity.ofGround` — Entity.ofGround is transcendent to all atomic worldly entities and finite subjective agents | PROVEN | `{Subject}` |
| C196 | §28/CHARACTERISTICS | `DivineSimplicity.ofGround_divine_simplicity : (∀ s, ∃ p, ¬ Means s p) → DivineSimplicity Entity.ofGround` — under finite subjectivity, Entity.ofGround satisfies Classical Divine Simplicity (mereological non-compositeness, structural inextension, and undivided meaning) | PROVEN | `{Means, Subject, CL}` |

> Batch DIVINE-SIMPLICITY-TRANSCENDENCE (2026-09-25): C192 is a machine-checked
> independence countermodel refuting the conflation of composite entities with simplicity.
> C193 proves structural inextension (`ofGround_has_no_internal_components`, `{Subject}`),
> establishing that `Entity.ofGround` is an atomic, nullary constructor without internal parts.
> C194 establishes intentional undividedness (`ofGround_undivided_meaning`, `{Means, Subject}`).
> C195 establishes ontological transcendence (`ofGround_transcendent`, `{Subject}`).
> C196 provides the master synthesis (`ofGround_divine_simplicity`, `{Means, Subject, CL}`),
> proving that `Entity.ofGround` satisfies classical Divine Simplicity (mereological, structural,
> and intentional) with zero substantive axioms.

---

## Level 12 — Classical Divine Immutability & Ontological Invariance (`Logos.DivineImmutability`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C197 | §28/CHARACTERISTICS | `DivineImmutability.contingent_entity_fails_immutability : ∃ Ent World ExistsAtRel e, ¬ (∀ w₁ w₂, ExistsAtRel w₁ e ↔ ExistsAtRel w₂ e)` — contingent entities are mutable across worlds, confirming that immutability is non-trivial | COUNTERMODEL | `{}` |
| C198 | §28/CHARACTERISTICS | `DivineImmutability.ofGround_modal_invariance : ModalInvariance Entity.ofGround` — Entity.ofGround has invariant existence across all possible worlds | PROVEN | `{Subject}` |
| C199 | §28/CHARACTERISTICS | `DivineImmutability.ofGround_stage_invariance : StageInvariance Entity.ofGround` — Entity.ofGround has invariant existence across all temporal stages | PROVEN | `{Subject}` |
| C200 | §28/CHARACTERISTICS | `DivineImmutability.ofGround_transition_invariance : TransitionInvariance Entity.ofGround` — Entity.ofGround is outside all initiation-becoming and state transitions | PROVEN | `{Initiates, State, Subject}` |
| C201 | §28/CHARACTERISTICS | `DivineImmutability.ofGround_divine_immutability : DivineImmutability Entity.ofGround` — Entity.ofGround satisfies Classical Divine Immutability across worlds, time, state transitions, and meaning capacity | PROVEN | `{Initiates, Means, State, Subject}` |

> Batch DIVINE-IMMUTABILITY (2026-09-25): C197 is a machine-checked countermodel
> showing that contingent entities fail immutability. C198 proves modal invariance
> (`ofGround_modal_invariance`, `{Subject}`). C199 proves stage invariance
> (`ofGround_stage_invariance`, `{Subject}`). C200 establishes process invariance
> (`ofGround_transition_invariance`, `{Initiates, State, Subject}`). C201 provides the
> master synthesis (`ofGround_divine_immutability`, `{Initiates, Means, State, Subject}`),
> establishing that the ground satisfies Classical Divine Immutability with zero substantive axioms.

---

## Level 13 — Classical Foundational Omnipresence & Universal Sustaining Ground (`Logos.FoundationalOmnipresence`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C202 | §28/CHARACTERISTICS | `FoundationalOmnipresence.finite_entity_fails_omnipresence : ∃ Ent World ExistsAtRel GroundsRel e, ¬ (∀ w x, ExistsAtRel w x → x = e ∨ GroundsRel e x)` — finite/localized entities fail universal modal grounding, confirming that omnipresence is non-trivial | COUNTERMODEL | `{}` |
| C203 | §28/CHARACTERISTICS | `FoundationalOmnipresence.ofGround_world_rigid_presence : WorldRigidPresence Entity.ofGround` — Entity.ofGround is present across all possible worlds | PROVEN | `{Subject}` |
| C204 | §28/CHARACTERISTICS | `FoundationalOmnipresence.ofGround_universal_modal_ground : UniversalModalGround Entity.ofGround` — Entity.ofGround grounds every entity that exists in any possible world | PROVEN | `{Means, Subject}` |
| C205 | §28/CHARACTERISTICS | `FoundationalOmnipresence.ofGround_non_reciprocal_ground : NonReciprocalGround Entity.ofGround` — Entity.ofGround operates as asymmetric ground; no worldly atom or discriminating subject grounds it | PROVEN | `{Means, Subject}` |
| C206 | §28/CHARACTERISTICS | `FoundationalOmnipresence.ofGround_foundational_omnipresence : FoundationalOmnipresence Entity.ofGround` — Entity.ofGround satisfies Classical Foundational Omnipresence across all worlds, entities, and contents | PROVEN | `{Means, Subject}` |

> Batch FOUNDATIONAL-OMNIPRESENCE (2026-09-25): C202 is a machine-checked countermodel
> showing that finite localized entities fail universal modal grounding. C203 proves
> world-rigid presence across modal space (`ofGround_world_rigid_presence`, `{Subject}`).
> C204 establishes universal modal grounding across all worlds (`ofGround_universal_modal_ground`, `{Means, Subject}`).
> C205 proves non-reciprocal grounding (`ofGround_non_reciprocal_ground`, `{Means, Subject}`).
> C206 provides the master synthesis (`ofGround_foundational_omnipresence`, `{Means, Subject}`),
> establishing that the ground satisfies Classical Foundational Omnipresence (Aquinas ST I q. 8)
> with zero substantive axioms.

---

## Level 14 — Classical Foundational Unicity & Structural Monotheism (`Logos.FoundationalUnicity`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C207 | §28/CHARACTERISTICS | `FoundationalUnicity.universal_ground_unicity : ∀ g1 g2, UniversalModalGround g1 → UniversalModalGround g2 → AsymmetricGrounding → ∀ w, ExistsAt w g1 → ExistsAt w g2 → g1 = g2` — two distinct entities cannot both be universal modal grounds under asymmetric grounding | PROVEN | `{CL, Means, Subject}` |
| C208 | §28/CHARACTERISTICS | `FoundationalUnicity.no_atom_is_universal_modal_ground : ∀ n w, ¬ UniversalModalGround (Entity.ofAtom n)` — an atomic factual state cannot ground Entity.ofGround, hence cannot ground all beings | PROVEN | `{Means, Subject}` |
| C209 | §28/CHARACTERISTICS | `FoundationalUnicity.no_discriminating_subject_is_universal_modal_ground : ∀ s, (∃ p, ¬ Means s p) → ∀ w, ¬ UniversalModalGround (EntityOf s)` — a discriminating subject cannot ground Entity.ofGround, hence cannot ground all beings across modal space | PROVEN | `{Means, Subject}` |
| C210 | §28/CHARACTERISTICS | `FoundationalUnicity.ofGround_sole_universal_ground : ∀ e w, UniversalModalGround e → (∀ n, e ≠ Entity.ofAtom n) ∧ (∀ s, (∃ p, ¬ Means s p) → e ≠ EntityOf s)` — any universal modal ground in world w cannot be an atom, nor a discriminating subject | PROVEN | `{Means, Subject}` |
| C211 | §28/CHARACTERISTICS | `FoundationalUnicity.ofGround_foundational_unicity : FoundationalUnicity Entity.ofGround` — Entity.ofGround satisfies Classical Divine Unicity (Monotheism), grounding all beings and being structurally unique under asymmetry | PROVEN | `{CL, Means, Subject}` |
| C212 | §28/CHARACTERISTICS | `FoundationalUnicity.unicity_does_not_force_unitarian_monad : ∃ Ground Persons, (∃ g : Ground, ∀ g', g' = g) ∧ (∀ g, ∃ p1 p2 : Persons g, p1 ≠ p2)` — foundational unicity of universal grounding does not force a solitary, relationless monad; the Trinitarian frontier remains open | COUNTERMODEL | `{}` |
| C213 | §28/CHARACTERISTICS | `FoundationalUnicity.unicity_strictly_transcends_world : TranscendentGround Entity.ofGround` — foundational unicity does not collapse the ground into the world, strictly preserving ontological transcendence | PROVEN | `{Subject}` |
| C313 | §28/CHARACTERISTICS | `FoundationalUnicity.groundsEntity_reflexive : ∀ e, GroundsEntity e e` — grounding is meaning-containment, hence reflexive at every entity; no relation of this form can be irreflexive | PROVEN | `{Means, Subject}` |
| C314 | §28/CHARACTERISTICS | `FoundationalUnicity.grounds_ground_iff_maximal : ∀ e, GroundsEntity e Entity.ofGround ↔ MaximalCapacity e` — since the ground means every proposition, grounding the ground is exactly total meaning-capacity; this identifies `MaximalCapacity` (`FoundationalOmnipresence.lean:119`) as the precise maximality notion the unicity argument needs | PROVEN | `{Means, Subject}` |
| C315 | §28/CHARACTERISTICS | `FoundationalUnicity.ofGround_ne_ofSubject : ∀ s, EntityOf s ≠ Entity.ofGround` — no subject-entity is identical with the ground of reality | PROVEN | `{Subject}` |
| C316 | §28/CHARACTERISTICS | `FoundationalUnicity.not_asymmetric_grounding : ¬ AsymmetricGrounding` — **the asymmetry premise of C207 is unsatisfiable**: `AsymmetricGrounding` omits a `g1 ≠ g2` guard while `GroundsEntity` is reflexive (C313), so `g1 = g2 = ofGround` refutes it. C207's route to unicity is therefore **void**, and no unpayable premise may stand as a proven attribute | COUNTERMODEL | `{Means, Subject}` |
| C317 | §28/CHARACTERISTICS | `FoundationalUnicity.ofGround_unicity_from_no_discriminating_subject : ∀ s, (∃ p, ¬ Means s p) → ∀ e w, UniversalModalGround e → e = Entity.ofGround` — **Foundational Unicity from one named, satisfiable hypothesis**: no subject has total meaning-capacity, so the total-capacity subject left open by C210 is ruled out, and the ground is the only universal modal ground | PROVEN | `{Means, Subject}` |
| C318 | §28/CHARACTERISTICS | `FoundationalUnicity.no_discriminating_subject_iff_no_maximal_non_ground : (∀ s, ∃ p, ¬ Means s p) ↔ (∀ e, e ≠ Entity.ofGround → ¬ MaximalCapacity e)` — the premise of C317 **is** the exclusion of maximal capacity among non-ground entities, so the whole price of Foundational Unicity is one already-named predicate | PROVEN | `{CL, Means, Subject}` |
| C319 | §28/CHARACTERISTICS | `FoundationalUnicity.ofGround_sole_universal_grounding : ∀ s, (∃ p, ¬ Means s p) → SoleUniversalGrounding Entity.ofGround` — repaired master synthesis: identical in content to C211 but its unicity field is a plain identity discharged by the named hypothesis, with no unpayable premise | PROVEN | `{Means, Subject}` |
| C320 | §28/CHARACTERISTICS | `FoundationalUnicity.exactly_one_universal_modal_ground : ∀ s, (∃ p, ¬ Means s p) → ∃ g, UniversalModalGround g ∧ (∀ g', UniversalModalGround g' → g' = g)` — **Classical Monotheism with the entire price on one line**: existence is unconditional (`ofGround_universal_modal_ground`), uniqueness rests on the single named maximality hypothesis | PROVEN | `{Means, Subject}` |
| C321 | §28/CHARACTERISTICS | `DivineImmutability.capacity_invariance_holds_for_every_entity : ∀ e, CapacityInvariance e` — **the fourth field of `DivineImmutability` is a tautology and discriminates nothing.** *What is machine-checked:* `CapacityInvariance e := ∀ p, ∀ _w₁ _w₂ : World, EntityMeans e p ↔ EntityMeans e p` (`DivineImmutability.lean:120`), but `EntityMeans` is `EntityMeans (e : Entity) (p : Prop) : Prop` (`RecoveredOntologicalGround.lean:46`) and **takes no world argument at all** — so `w₁`/`w₂` are bound and never mentioned, the body reduces to `P ↔ P`, and the existing `ofGround_capacity_invariance` (`:130-133`) is discharged by `exact Iff.rfl`. Hence the property holds for **every** entity, subject and atom included. *Why the asymmetry is the finding:* all three siblings genuinely quantify and do discriminate — `ModalInvariance` over `w₁ w₂ : World` via `ExistsAt` (`:65`), `StageInvariance` over `t₁ t₂ : Time` via `ExistsAtTime` (`:84`), `TransitionInvariance` as the real predicate `NotInSuccession e` (`:101`) — and each has a `{}` non-triviality countermodel on record (C197 modal/stage, with C192, C202, C214 for the other three attribute masters). This field has **none, because there is nothing in it to refute.** *Disclosure, NOT a demotion:* `ofGround_divine_immutability` remains `PROVEN` and is untouched; what changes is that the ledger previously stated the property only where it could not fail, which read as if it carried weight | COUNTERMODEL | `{Means, Subject}` |

> Batch FOUNDATIONAL-UNICITY (2026-09-25): C207 proves the master metaphysical theorem
> that two distinct entities cannot both be universal modal grounds under asymmetric grounding
> (`universal_ground_unicity`, `{CL, Means, Subject}`). C208 and C209 systematically exclude
> worldly atoms and discriminating subjects from universal grounding (`{Means, Subject}`).
> C210 shows that `Entity.ofGround` is the sole candidate in the Γ inventory (`{Means, Subject}`).
> C211 provides the master synthesis (`ofGround_foundational_unicity`, `{CL, Means, Subject}`),
> establishing Classical Divine Unicity (Aquinas ST I q. 11 a. 3) with zero substantive axioms.
> C212 is a machine-checked separation model showing that foundational unicity does not collapse
> into numerical unitarianism, keeping the Trinitarian frontier open (`{}`).
> C213 confirms ontological transcendence over pantheistic conflation (`{Subject}`).

> **CORRECTION (2026-09-27, C316):** this batch note overstated C207/C211. Both rest on
> `AsymmetricGrounding`, which **C316 proves unsatisfiable** — the relation is reflexive
> (`GroundsEntity e e`, C313) and the definition omits the `g1 ≠ g2` guard. So the
> "zero substantive axioms" framing was true only in the vacuous sense that an
> *unpayable* premise was being consumed. C207 and C211 remain **PROVEN** as conditional
> theorems (they are valid inferences), but the *attribute* they were credited with
> establishing was not established. The replacement route is C317–C320 below.

> Batch FOUNDATIONAL-UNICITY-REPAIR (2026-09-27): the unicity attribute is re-derived on a
> sound basis. Diagnosis first (C313–C316): grounding is meaning-containment and therefore
> reflexive, so `AsymmetricGrounding` is refutable and the C207 route is void (C316). C314
> then supplies the key identification: because the ground means every proposition, "grounds
> the ground" is *exactly* `MaximalCapacity` — so the notion the argument needs already
> exists in the project (`FoundationalOmnipresence.lean:119`) and no new axiom is required.
> Repair (C317–C320): C210 leaves exactly one case open — a subject that means *everything* —
> and the single hypothesis `∀ s, ∃ p, ¬ Means s p` closes it, giving full unicity (C317).
> C318 proves that hypothesis *is* the exclusion of maximal capacity among non-ground entities,
> so the price is one named predicate, not a new bridge. C319 re-synthesises the attribute with
> a plain-identity unicity field, and **C320 states Classical Monotheism outright** (existence
> unconditional, uniqueness under the one named hypothesis). ~~The hypothesis is **not yet
> asserted in Γ** — it is tracked as frontier row **F15** and is the single open decision.~~
> **CORRECTION 2026-09-28 (lote SEMANTIC-FINITUDE-PROMOTION):** a hipótese **é** agora
> asserta em Γ, como o axioma declarado `SemanticFinitude.SemanticFinitude`
> (`SemanticFinitude.lean:151`, `Tag: VOCAB`, C388), e C389
> (`exactly_one_universal_modal_ground_stipulated`) é o teorema de unicidade
> **incondicional** — sem parâmetro de hipótese. F15 é `AXIOM`, não uma decisão em
> aberto. O que continua genuinamente em aberto é a monoteia *ao nível da pessoa* e a
> ponte #9 (`C228`), e nenhuma das duas é esta frase.

---

## Level 15 — Classical Divine Pure Actuality & Perfection (`Logos.DivinePureActuality`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C214 | §28/CHARACTERISTICS | `DivinePureActuality.entity_with_potency_fails_pure_actuality : ∃ Ent HasPotency PureAct, (∀ e, PureAct e → ¬ HasPotency e) ∧ (∃ e, HasPotency e ∧ ¬ PureAct e)` — an entity with passive potency fails pure actuality, confirming that pure actuality is non-trivial | COUNTERMODEL | `{}` |
| C215 | §28/CHARACTERISTICS | `DivinePureActuality.ofGround_no_existential_potency : ¬ PassiveExistentialPotency Entity.ofGround` — Entity.ofGround has zero passive existential potency, existing necessarily across all possible worlds | PROVEN | `{Subject}` |
| C216 | §28/CHARACTERISTICS | `DivinePureActuality.ofGround_no_grounding_potency : (∀ s, ∃ p, ¬ Means s p) → ¬ PassiveGroundingPotency Entity.ofGround` — under finite subjectivity, Entity.ofGround has zero passive grounding potency, depending on no external ground | PROVEN | `{Means, Subject}` |
| C217 | §28/CHARACTERISTICS | `DivinePureActuality.ofGround_no_transition_potency : ¬ PassiveTransitionPotency Entity.ofGround` — Entity.ofGround has zero passive transition potency, immune to agential succession and temporal becoming | PROVEN | `{Initiates, State, Subject}` |
| C218 | §28/CHARACTERISTICS | `DivinePureActuality.ofGround_no_intentional_potency : ¬ PassiveIntentionalPotency Entity.ofGround` — Entity.ofGround has zero passive intentional potency, possessing complete propositional meaning grasp | PROVEN | `{Means, Subject}` |
| C219 | §28/CHARACTERISTICS | `DivinePureActuality.ofGround_divine_pure_actuality : (∀ s, ∃ p, ¬ Means s p) → DivinePureActuality Entity.ofGround` — Entity.ofGround satisfies Classical Divine Pure Actuality (Actus Purus, Aquinas ST I q. 3-4), with zero passive potency and universal modal grounding | PROVEN | `{Initiates, Means, State, Subject}` |
| C220 | §28/CHARACTERISTICS | `DivinePureActuality.ofGround_incorporeal : ∀ n, Entity.ofGround ≠ Entity.ofAtom n` — as pure act without material/passive potency, Entity.ofGround is strictly non-corporeal and transcends all worldly atomic states | PROVEN | `{Subject}` |

> Batch DIVINE-PURE-ACTUALITY (2026-09-25): C214 is a machine-checked separation model
> showing that entities with passive potency fail Pure Actuality (`entity_with_potency_fails_pure_actuality`, `{}`).
> C215 proves that `Entity.ofGround` has zero passive existential potency across all worlds (`ofGround_no_existential_potency`, `{Subject}`).
> C216 proves zero passive grounding potency under finite subjectivity (`ofGround_no_grounding_potency`, `{Means, Subject}`).
> C217 proves zero passive transition potency (`ofGround_no_transition_potency`, `{Initiates, State, Subject}`).
> C218 proves zero passive intentional potency (`ofGround_no_intentional_potency`, `{Means, Subject}`).
> C219 provides the master synthesis (`ofGround_divine_pure_actuality`, `{Initiates, Means, State, Subject}`),
> establishing Classical Divine Pure Actuality (Actus Purus, Aquinas ST I q. 4 a. 1) with zero substantive axioms.
> C220 derives Divine Incorporeality and Immateriality (`ofGround_incorporeal`, `{Subject}`),
> proving that the ground cannot be an atom or physical body (Aquinas ST I q. 3 a. 1–2).





## Level 16 — Classical Foundational Omniscience & Truth-Exhaustiveness (`Logos.DivineOmniscience`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C233 | §28/CHARACTERISTICS | `DivineOmniscience.entity_scope_exhaustiveness_is_not_infallibility : ∃ (Ent : Type) (Scope Fails : Ent → Prop), (∀ e, Scope e) ∧ (∃ e, Scope e ∧ Fails e)` — a scope can be exhaustive over every true proposition and yet fail to track truth exactly: exhaustiveness and infallibility are independent | COUNTERMODEL | `{}` |
| C234 | §28/CHARACTERISTICS | `DivineOmniscience.ofGround_truth_exhaustive : TruthExhaustive Entity.ofGround` — no true proposition is closed to the ground's scope (`∀ p, T p → EntityMeans .ofGround p`); the ground is the condition of all truth (Aquinas ST I q. 14 a. 1) | PROVEN | `{Means, Subject}` |
| C235 | §28/CHARACTERISTICS | `DivineOmniscience.ofGround_world_truth_exhaustive : WorldTruthExhaustive Entity.ofGround` — the same exhaustiveness world-indexed: no state of affairs true in any possible world is closed to the ground's scope | PROVEN | `{Means, Subject}` |
| C236 | §28/CHARACTERISTICS | `DivineOmniscience.ofGround_not_truth_tracking : ¬ TruthTracking Entity.ofGround` — **the strong (infallible) sense is refuted for the canonical ground**: its scope bears every proposition (`p := False` witness), so `EntityMeans e p → T p` is false of `Entity.ofGround`; the scope is exhaustive and provably not error-free | PROVEN | `{Means, Subject}` |
| C237 | §28/CHARACTERISTICS | `DivineOmniscience.atom_not_truth_exhaustive : (n : Nat) → ¬ TruthExhaustive (Entity.ofAtom n)` — no worldly atom bears even one true proposition (`p := True` witness), so no atom is truth-exhaustive | PROVEN | `{Means, Subject}` |
| C238 | §28/CHARACTERISTICS | `DivineOmniscience.discriminating_subject_not_truth_exhaustive : (s : Subject) → (∃ p, T p ∧ ¬ Means s p) → ¬ TruthExhaustive (EntityOf s)` — any subject failing to mean a *true* proposition is not truth-exhaustive, that true proposition being the witness | PROVEN | `{Means, Subject}` |
| C239 | §28/CHARACTERISTICS | `DivineOmniscience.ofGround_foundational_omniscience : FoundationalOmniscience Entity.ofGround` — **master synthesis**: truth-exhaustive scope, world-indexed exhaustiveness, undivided scope (`DivineSimplicity`), the *refutation* of infallibility as a carried field, and universal modal grounding (`FoundationalOmnipresence`) | PROVEN | `{Means, Subject}` |
| C240 | §28/CHARACTERISTICS | `DivineOmniscience.exhaustive_scope_without_counterfactual_knowledge : ∃ (W S : Type) (Scope : S → Prop) (K : W → S → (W → Prop) → Prop) (s : S), Scope s ∧ ¬ Omniscience_Counterfactuals W S K s` — countermodel: exhaustive scope does not force the frontier's counterfactual-knowledge predicate, so the counterfactual sense of omniscience is independent of the foundational sense | COUNTERMODEL | `{}` |

> Batch FOUNDATIONAL-OMNISCIENCE (2026-09-26): C233 is a machine-checked separation model showing that
> scope-exhaustiveness and infallibility are independent (`entity_scope_exhaustiveness_is_not_infallibility`, `{}`).
> C234 proves the foundational sense itself for `Entity.ofGround` (`ofGround_truth_exhaustive`, `{Means, Subject}`:
> no true proposition is closed to the ground's scope) and C235 proves it world-indexed
> (`ofGround_world_truth_exhaustive`, `{Means, Subject}`). C236 **refutes the strong classical sense for the canonical
> ground** (`ofGround_not_truth_tracking`, `{Means, Subject}`): since `EntityMeans .ofGround p` reduces to `True`,
> the exclusive half `EntityMeans e p → T p` is false of the ground — the classical "all and only truths" reading is
> not merely unproven in Γ but refuted. C237/C238 exclude worldly atoms and discriminating subjects from
> truth-exhaustive scope (`{Means, Subject}`), so `Entity.ofGround` is the sole candidate in the Γ inventory.
> C239 provides the master synthesis (`ofGround_foundational_omniscience`, `{Means, Subject}`) — 0 substantive axioms,
> with the refutation of infallibility carried as a **field** of the record rather than a remark. C240 shows the
> counterfactual sense is not forced by the foundational one (`{}`), against `DeepModalFrontier`'s
> `Omniscience_Counterfactuals`. Companion principle: `necessity_and_scope_yield_foundational_omniscience`
> (`{Means, Subject}`) — necessary existence, exhaustive scope, undivided scope and universal grounding concede
> Foundational Omniscience, and generically concede non-infallibility. **Ordinary/classical omniscience remains
> disclaimed** (`README-OLD.md:263`; `CHARS.md` §14): Γ has no `Knows` predicate, the frontier's knowledge relations
> are vocabulary definitions, and `Entity.ofGround` is not a subject correlate
> (`ofGround_ne_ofSubject`, `NecessityEternity.lean:160`), so no divine knowledge bridge is manufactured.

## Level 17 — Classical Foundational Omnipotence & the Non-Contradictory Restriction (`Logos.DivineOmnipotence`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C241 | §15/CHARACTERISTICS | `DivineOmnipotence.existence_everywhere_does_not_entail_operation : ∃ (Ent : Type) (ExistsAtRel : World → Ent → Prop) (Operates : World → Ent → WProp → Prop) (e : Ent), (∀ w, ExistsAtRel w e) ∧ ¬ GaplessOperate (UniversalFrame World) Operates e` — **the price of the identification, machine-checked**: an entity present in *every* world can still operate nothing, so presence is not production. This is what keeps the causal disclaimer honest | COUNTERMODEL | `{}` |
| C242 | §15/CHARACTERISTICS | `DivineOmnipotence.ofGround_gapless_operative_scope : GaplessOperate (UniversalFrame World) OperatesAt Entity.ofGround` — **the doctrine**: no state of affairs satisfiable in any accessible world is closed to the ground's operative scope, i.e. power over whatever does not involve a contradiction (Aquinas *ST* I, q. 25, a. 5, ad 1, *semper et ubique operans*). Proved from the two clauses of `OperatesAt` (stipulation ◈ `operatesAt_presencePlusObtaining`) | PROVEN | `{Subject}` |
| C243 | §15/CHARACTERISTICS | `DivineOmnipotence.ofGround_operates_only_what_obtains : ∀ (v : World) (P : WProp), OperatesAt v Entity.ofGround P → P v` — the non-contradictory restriction, first horn: nothing unobtained — hence nothing unsatisfiable — is in the ground's operative scope. Holds of *every* entity under `OperatesAt` with no premise at all | PROVEN | `{Subject}` |
| C244 | §15/CHARACTERISTICS | `DivineOmnipotence.ofGround_does_not_operate_contradictions : ∀ (v : World) (φ : Form), ¬ OperatesAt v Entity.ofGround (fun u => Satisfies u (Form.and φ (Form.not φ)))` — second horn: no contradiction is ever operated, at no world, by `Semantics.nonContradiction` (C14). **The only sense of omnipotence refuted here is the contradiction-omni reading** ("everything conceivable, including contradictions"), and it is refuted *by* the orthodox restriction, not against it | PROVEN | `{Subject, propext}` |
| C245 | §15/CHARACTERISTICS | `DivineOmnipotence.atom_not_gapless_operate : ∀ (n : Nat), ¬ GaplessOperate (UniversalFrame World) OperatesAt (Entity.ofAtom n)` — no worldly atom is a gapless operator; witness the content `¬ atom n`, satisfiable in the all-`f` world and yet unobtained wherever the atom exists | PROVEN | `{Subject}` |
| C246 | §15/CHARACTERISTICS | `DivineOmnipotence.discriminating_subject_not_gapless_operate (s : Subject) (hKind : ContingentSubjectKind s) : ¬ GaplessOperate (UniversalFrame World) OperatesAt (EntityOf s)` — no *contingent-kind* subject is a gapless operator; such a subject exists only at `actualWorld`, which denies `atom 0` while `¬ atom 0` is satisfiable in the all-`f` world. A necessary-kind subject is present everywhere, so the exclusion is kind-relative by hypothesis | PROVEN | `{NecessarySubjectKind, Subject}` |
| C247 | §15/CHARACTERISTICS | `DivineOmnipotence.gapless_operators_are_ground_or_necessary_kind : ∀ (e : Entity), GaplessOperate (UniversalFrame World) OperatesAt e → e = Entity.ofGround ∨ ∃ s : Subject, NecessarySubjectKind s ∧ e = EntityOf s` — **gapless operators are the ground and the necessary-kind subjects** (renamed 2026-09-28; was `ofGround_sole_gapless_operator`): with C245/C246 this closes the characteristic — atoms and contingent-kind subjects are excluded, the ground and the necessary kind remain | PROVEN | `{NecessarySubjectKind, Subject}` |
| C248 | §15/CHARACTERISTICS | `DivineOmnipotence.ofGround_foundational_omnipotence : FoundationalOmnipotence Entity.ofGround` — **master synthesis**: gapless operative scope (C242), operates-only-what-obtains (C243), operates-no-contradiction (C244) and universal modal grounding (reused `ofGround_universal_modal_ground`), at 0 substantive axioms | PROVEN | `{Subject, Means, propext}` |
| C249 | §15/CHARACTERISTICS | `DivineOmnipotence.gapless_operative_scope_without_conjunctive_power : ∃ (Ent : Type) (Operates : World → Ent → WProp → Prop) (e : Ent), GaplessOperate (UniversalFrame World) Operates e ∧ ¬ ConjunctivePower (UniversalFrame World) Operates e` — countermodel: gapless scope does **not** entail conjunctive power, because Γ's Kripke accessibility is not conjunctive (`atom 0` and `¬ atom 0` are each possible; no world operates both). Bounds this batch's own claim: the non-contradictory restriction is machine-checked, but "jointly possible pairs" is strictly more than modal accessibility delivers | COUNTERMODEL | `{}` |
| C250 | §15/CHARACTERISTICS | `DivineOmnipotence.exhaustive_scope_without_operative_scope : ∃ (Ent : Type) (Scope : Ent → WProp → Prop) (Operates : World → Ent → WProp → Prop) (e : Ent), (∀ P : WProp, Scope e P) ∧ ¬ GaplessOperate (UniversalFrame World) Operates e` — countermodel: an exhaustive meaning scope does **not** entail operative scope; the operational analogue of `means_does_not_imply_means_selection` (`HostileSemantics.lean:1861`). This is why C242 is proved from world-rigid presence (◈ `ofGround_existsAt`) and never read off the meaning-exhaustive scope of `FoundationalOmniscience` | COUNTERMODEL | `{}` |
| C251 | §15/CHARACTERISTICS | `DivineOmnipotence.satisfiable_scope_is_nonempty_and_contradiction_free : (∃ v : World, ∃ φ : Form, Satisfies v φ) ∧ (∀ (φ : Form) (v : World), ¬ Satisfies v (Form.and φ (Form.not φ)))` — **the scope domain is non-empty and contradiction-free**: non-emptiness witnessed by `atom 0` at `actualWorld`, contradiction-freedom by C14. This is the machine-checked licence for reading C242 as "power over whatever does not involve a contradiction" — the reading is substantive, not vacuous | PROVEN | `{propext}` |
| F10 | §15 causal/creative omnipotence ("can bring X about", not "is present where X obtains") | BLOCKED | exactly two missing statements, in this order. **(1) MISSING VOCABULARY:** a production relation for entities, `Produces : Entity → World → Form → Prop` — Γ declares none; the only initiation relation is `Agency.Initiates : Subject → State → State → Prop → Prop` (`Agency.lean:168`, VOCAB), which is **subject**-indexed, and `Entity.ofGround` is provably not a subject correlate (`ofGround_ne_ofSubject`, `NecessityEternity.lean:160`), so it cannot even be instantiated by the ground. **(2) MISSING DERIVATION:** `∀ (φ : Form), (∃ w, Satisfies w φ) → ∃ v, Produces Entity.ofGround v φ` — which (1) alone would not give. The closest relation Γ has is explanatory containment `GroundsEntity` (`RecoveredOntologicalGround.lean:57`, *esse est agere*), and C250 plus `means_does_not_imply_means_selection` already machine-check that omni-scope does not entail selection power, so (1) must not be weakened to it. **Consequence for the prose:** the `README-OLD.md:263` / `CHARS.md` §15 disclaimer is **retained and narrowed to the causal sense only** — the non-contradictory sense is now PROVEN, not disclaimed |
| — | §15/CHARACTERISTICS | `DivineOmnipotence.necessity_and_presence_yield_foundational_omnipotence : ∀ (e : Entity), NecessaryEntity e → WorldRigidPresence e → UniversalModalGround e → FoundationalOmnipotence e` — companion principle (Aquinas *ST* I q. 25 a. 5: *semper*): necessary existence, world-rigid presence and universal grounding concede Foundational Omnipotence; the two non-contradictory horns are free, so only the presence premise does work | PROVEN | `{Subject, Means, propext}` |

> Batch FOUNDATIONAL-OMNIPOTENCE (2026-09-26): this batch **reverses the theological framing** of its own
> first draft, which had proposed to "refute the strong sense of omnipotence" by naming the
> contradiction-omni reading (power over everything conceivable, *including contradictions*) as *the*
> classical sense. That was wrong: the orthodox reading is Aquinas' own (*ST* I, q. 25, a. 5, ad 1) —
> power over whatever does not involve a contradiction — and Γ's own corpus already sides with it
> (`theorems/T25.txt:111` marks the passive-potentia scope; `README-OLD.md:263` disclaims the *causal*
> claim, not the non-contradictory one). So the restriction is **affirmed, not refuted**: C242 proves the
> orthodox sense for `Entity.ofGround` (`{Subject}`), C243/C244 give its two horns (`{Subject}` /
> `{Subject, propext}`), and C251 (`{propext}`) machine-checks that the scope domain is **non-empty and
> contradiction-free** — so the reading is substantive, not vacuous. C241 (`{}`) is the machine-checked
> **price** of the batch's founding definitional choice, now registered as a 4th stipulation
> ◈ `operatesAt_presencePlusObtaining` (`Tag: SEM`): Γ has no causal production relation, so
> `OperatesAt v e P := ExistsAt v e ∧ P v` reads "operates" as *presence plus obtaining*. Foundational
> omnipotence is therefore proved over that weakened reading, and the causal sense is **BLOCKED**, not
> discharged (F10, with both exact missing statements). C245/C246/C247 (`{NecessarySubjectKind, Subject}`) exclude worldly atoms
> and contingent-kind subjects; C247 (renamed 2026-09-28, two-kinds) closes the characteristic as a disjunction —
> gapless operators are the ground **and the necessary-kind subjects** — so the characteristic is
> closed against Γ's whole `Entity` inventory, with the necessary kind admitted rather than excluded. C249 (`{}`) and C250 (`{}`) bracket the claim from both
> sides: modal accessibility is not conjunctive (so gapless scope ⇏ conjunctive power), and exhaustive
> meaning scope ⇏ operative scope (so C242 rests on presence, not on `ofGround_meansAll`).
> C248 (`{Subject, Means, propext}`) is the master synthesis and
> `necessity_and_presence_yield_foundational_omnipotence` the companion. 0 new axioms, 0 new `Tag:`
> axioms; the `propext` cost is inherited from C14 by design, so the graph shows the C241–C251 → C14 edge.


## Level 18 — Asietic Indeterminacy, True Choice, and the Refuted Bare Horn (`Logos.AsieticChoice`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C259 | §30 | `AsieticChoice.contested_content : ContestedContent` — the frame does contest its own content: some formula is neither necessarily true nor necessarily false (C96 reused). Axiom-free, and it is the sole source of the contingency conjunct of `OpenAlternative` | PROVEN | `{}` |
| C260 | §30 | `AsieticChoice.open_alternative_is_incompatible {p q : Prop} (h : OpenAlternative p q) : Incompatible p q` — openness really excludes: the two alternatives of an `OpenAlternative` are incompatible, by `incompatible_self_negation` (C15). Pure logic, no axiom | PROVEN | `{}` |
| C261 | §30 | `AsieticChoice.chooses_implies_trueChoice {s : Subject} {p q : Prop} (h : Chooses s p q) : TrueChoice s p q` — the substantive direction, one way: a subject who means a content and its negation is genuinely choosing between them | PROVEN | `{Means, Subject}` |
| C262 | §30 | `AsieticChoice.trueChoice_implies_chooses {s : Subject} {p q : Prop} (h : TrueChoice s p q) : Chooses s p q` — the converse is definitional — `Chooses` is the second conjunct of `TrueChoice` | PROVEN | `{Means, Subject}` |
| C263 | §30 | `AsieticChoice.trueChoice_implies_choiceField {s : Subject} {p q : Prop} (h : TrueChoice s p q) : ChoiceField s p q` — true choice delivers the choice-field: meaning both horns exhibits the incompatibility the field records. No silent `ChoiceField → Chooses` conversion anywhere | PROVEN | `{Means, Subject}` |
| C264 | §30 | `AsieticChoice.trueChoice_implies_freeWill {s : Subject} {p q : Prop} (h : TrueChoice s p q) : FreeWill s` — true choice delivers free will, by `FreeWill s := ∃ p q, Chooses s p q` | PROVEN | `{Means, Subject}` |
| C265 | §30 | `AsieticChoice.strongChoice_iff_trueChoice {s : Subject} {p q : Prop} : Chooses s p q ↔ TrueChoice s p q` — **the disclosed weakness of this batch**: `TrueChoice ≡ Chooses`, because the openness conjunct is a *global frame fact*, not a per-pair modality. So "true choice" adds nothing over "strong choice"; the two substantive steps are `Chooses → TrueChoice` and the existential below | PROVEN | `{Means, Subject}` |
| C266 | §30 | `AsieticChoice.weakChoice_implies_chooses {s : Subject} {p q : Prop} (hField : ChoiceField s p q) (hJudge : ClaimsCorrect s p) : Chooses s p (¬ p)` — **the `?` of `base.txt:460`, discharged with its premise named**: alternatives in the field plus a correctness-judgment give the co-signification of the rejected horn. The premise is load-bearing and is *not* `ChoiceField` alone | PROVEN↑ | `{AxJudicativeBipolarity, Initiates, Means, State, Subject}` |
| C267 | §30 | `AsieticChoice.weakChoice_implies_trueChoice {s : Subject} {p q : Prop} (hField : ChoiceField s p q) (hJudge : ClaimsCorrect s p) : TrueChoice s p (¬ p)` — the same implication at the pair level, for the chain's `strong Chooses` step | PROVEN↑ | `{AxJudicativeBipolarity, Initiates, Means, State, Subject}` |
| C268 | §30 | `AsieticChoice.derives_rejectedHornCoMeant : (∃ s : Subject, ∃ p : Prop, Means s p ∧ ClaimsCorrect s p) → rejectedHornCoMeant` — the **conditional** form of the rejected horn: a subject claiming a content as correct also means its negation. This is the "co-significação do corno rejeitado" of `base.txt:460`. Note the antecedent is a *correctness-judgment*, strictly more than the bare antecedent of F11 | PROVEN↑ | `{AxJudicativeBipolarity, Initiates, Means, State, Subject}` |
| C269 | §30 | `AsieticChoice.weakChoice_carries_the_judicative_premise_explicitly : ∀ (s : Subject) (p : Prop), ChoiceField s p (¬ p) → ClaimsCorrect s p → TrueChoice s p (¬ p)` — the price of the premise, made visible in the footprint rather than in a claim about the world: the bare `ChoiceField → Chooses` would need horn-saturation, which no axiom of Γ supplies, so the entailment is stated *with* its premise and never silently converted | PROVEN↑ | `{AxJudicativeBipolarity, Initiates, Means, State, Subject}` |
| C270 | §30 | `AsieticChoice.retorsion_yields_genuine_normativity_on_its_own_content (hEvent : ∃ s : Subject, ClaimsCorrect s NoGN) : ∃ s : Subject, GenuineNormativity s NoGN (¬ NoGN)` — **answers the meta-level-horn residue of F1b (`GAPMAP.md:758`)**: a subject claiming "there is no genuine normativity" as correct thereby means both `NoGN` and `¬ NoGN` — genuine normativity **on its own content**. Proved from `claiming_denial_presupposes_genuine_normativity`, not by re-exporting `retorsion_derives_genuine_normativity` (whose `∃ s p q` conclusion hides the pinned witnesses). What it does *not* answer: object/action content, which still needs the `DeliberateChoice` / `ClaimsNormativeCorrectness` route (C140/C141) | PROVEN↑ | `{AxJudicativeBipolarity, Initiates, Means, State, Subject}` |
| C271 | §30 | `AsieticChoice.retorsion_implies_rejectedHornCoMeant (hEvent : ∃ s : Subject, ClaimsCorrect s NoGN) : rejectedHornCoMeant` — the **second, performative** discharge of the rejected horn: from the retorsion event the consequent follows at pinned content. Distinct from the row above — this one concludes the horn's consequent, that one the pinned normativity. Both state their premise (`∃ s, ClaimsCorrect s NoGN`), which is `Act`-gated and therefore not derivable in Γ | PROVEN↑ | `{AxJudicativeBipolarity, Initiates, Means, State, Subject}` |
| C272 | §30 | `AsieticChoice.SingleContentSignature.antecedentHolds_in_canonicalModel : singleContentModel.antecedentHolds` — the countermodel's antecedent really holds — something is meant — so C273 is a counterexample, not a trick about an unsatisfiable antecedent | PROVEN | `{}` |
| C273 | §30 | `AsieticChoice.singleContentModelRefutesBareRejectedHorn (S : SingleContentSignature) (hFaith : S.Faithful) (hAntec : S.antecedentHolds) : ¬ S.bareHorn` — **the bare horn is refuted, not merely unproved**: in a faithful single-content model the antecedent holds while `means t p ∧ means t (¬ p)` is unsatisfiable. This is the formal content of `Choice.lean:36-40` ("`Means` is an opaque relation, and `AxTwoSubjects` yields two *different* subjects, each with a single content") | COUNTERMODEL | `{}` |
| C274 | §30 | `AsieticChoice.bareRejectedHornCoMeant_is_not_derivable : ¬ SingleContentSignature.singleContentModel.bareHorn` — the refutation, concretely, in the canonical model — so the F11 frontier is machine-backed: the blocker is a sentence false in a model of the meaning vocabulary, not an artefact of an unsuccessful search | COUNTERMODEL | `{}` |
| C275 | §30 | `AsieticChoice.doubt_implies_trueChoice {s : Subject} {p : Prop} (h : Doubts s p) : TrueChoice s p (¬ p)` — Cartesian doubt suffices, with no axiom at all: meaning `p` and `¬ p` simultaneously *is* a genuine strong choice between them | PROVEN | `{Means, Subject}` |
| C276 | §30 | `AsieticChoice.genuineNormativity_implies_trueChoice {s : Subject} {p q : Prop} (h : GenuineNormativity s p q) : TrueChoice s p q` — genuine normativity yields true choice, by `indubitable_normative_free_will` and pure logic | PROVEN | `{Means, Subject}` |
| C277 | §30 | `AsieticChoice.trueChoice_exists : ∃ s : Subject, ∃ p q : Prop, TrueChoice s p q` — **existence of true choice, unconditional**: a person exists (C14, `T5_personExists_from_plurality`), `Person` bundles `FreeWill` (`DominionOverActs s := FreeWill s`, `Person.lean:56`), so a `Chooses` witness exists and Section 2 promotes it. A second route to an already-`PROVEN↑` result (F1b), and a genuinely derivational one — presented as both | PROVEN↑ | `{AxTwoSubjects, Means, Subject, Will, subjectWill}` |
| C278 | §30 | `AsieticChoice.freeWill_exists : ∃ s : Subject, FreeWill s` — existence of free will, same route one step earlier | PROVEN↑ | `{AxTwoSubjects, Means, Subject, Will, subjectWill}` |
| C279 | §30 | `AsieticChoice.an_asietic_entity_exists : ∃ e : Entity, Asiety e` — existence of an asietic entity: `Asiety e := ∃ s p q, e = EntityOf s ∧ TrueChoice s p q`, and the above supplies the witness at `EntityOf s` | PROVEN↑ | `{AxTwoSubjects, Means, Subject, Will, subjectWill}` |
| C280 | §30 | `AsieticChoice.asietic_is_true_freedom {s : Subject} {p q : Prop} (h : TrueChoice s p q) : FreeWill s` — **the thesis**: asiety is true freedom. Vocabulary-only, so this row carries no substantive price — the price is in the existential rows, which is where it belongs | PROVEN | `{Means, Subject}` |
| C281 | §30 | `AsieticChoice.the_ground_grounds_a_contingent_true_chooser {s : Subject} {p q : Prop} (_h : TrueChoice s p q) (hCont : ContingentEntity (EntityOf s)) : GroundsEntity Entity.ofGround (EntityOf s)` — the contingent true chooser is externally grounded: a real chooser is not ungrounded, by `ExternalGrounding` | PROVEN | `{Means, Subject}` |
| C282 | §30 | `AsieticChoice.contingent_true_chooser_is_externally_grounded {s : Subject} {p q : Prop} (h : TrueChoice s p q) (hCont : ContingentEntity (EntityOf s)) : ExternalGrounding Entity.ofGround (EntityOf s)` — and the ground really does ground it — the converse direction, machine-checked | PROVEN | `{Means, Subject}` |
| C283 | §30 | `AsieticChoice.contingent_asietic_is_not_canonically_aseitous {s : Subject} {p q : Prop} (h : TrueChoice s p q) (hCont : ContingentEntity (EntityOf s)) : ¬ CanonicalAseity (EntityOf s)` — **refuted, not open**: `CanonicalAseity → TrueChoice` fails at a contingent stage. A later pass that "helpfully" adds this bridge breaks Γ, which is why it is recorded as a countermodel-grade separation rather than a frontier | PROVEN | `{Means, Subject}` |
| C284 | §30 | `AsieticChoice.ground_is_canonically_aseitous_but_not_asietic (hFinite : ∀ s : Subject, ∃ p : Prop, ¬ Means s p) : CanonicalAseity Entity.ofGround ∧ ¬ Asiety Entity.ofGround` — the honest conditional form: canonical aseity holds of the ground, asiety does not. The ground must stay out of the chooser inventory | PROVEN | `{Means, Subject}` |
| C285 | §30 | `AsieticChoice.ground_is_not_a_true_chooser : ¬ ∃ s : Subject, EntityOf s = Entity.ofGround` — the ground is **not** a true chooser, and cannot be: `ofGround_ne_ofSubject` (`NecessityEternity.lean:160`) blocks it definitionally, since `Means` is subject-indexed | PROVEN | `{Subject}` |
| C286 | §30 | `AsieticChoice.asietic_summary : (∀ (s : Subject) (p : Prop), ChoiceField s p (¬ p) → ClaimsCorrect s p → Chooses s p (¬ p)) ∧ (∀ (s : Subject) {p q : Prop}, Chooses s p q → TrueChoice s p q) ∧ (∃ s : Subject, ∃ p q : Prop, TrueChoice s p q)` — **master synthesis** of the batch, conflating: the definitional identification (vocabulary-only rows), the weak→strong step under its named premise, the unconditional existence of true choice, and the ground's exclusion from the chooser inventory | PROVEN↑ | `{AxJudicativeBipolarity, AxTwoSubjects, Initiates, Means, State, Subject, Will, subjectWill}` |
| F11 | §30 bare rejected horn: the co-signification of the rejected implication follows from the existence of a meaning-act alone | BLOCKED | **now nameable**: the blocked implication is `Logos.AsieticChoice.bareRejectedHornCoMeant : (∃ s : Subject, ∃ p : Prop, Means s p) → ∃ s : Subject, ∃ p : Prop, Means s p ∧ Means s (¬ p)`, and this row is `refuted, not merely open` — C273/C274 exhibit a model of the meaning vocabulary in which the antecedent holds and the consequent does not. **(1) The complete inventory of Γ's routes to `Means s (¬ p)`, and all four are `Act`-gated:** `AxJudicativeBipolarity` (`RetorsiveNormativity.lean:91`, premise `ClaimsCorrect s p`), `AxActPolarity` (`Choice.lean:782`, premise `Act s p`), `AxIntentionalChoice` (`Choice.lean:771`, premise `Act s p`, and its `q` is arbitrary, never `¬ p`), `ClaimsNormativeCorrectness` (`NormativeOrder.lean:168`, premise `Act s p ∧ …`); `Doubts` (`Choice.lean:1079`) is *itself* `Means s p ∧ Means s (¬ p)`, so it is circular. **(2) The single upstream gap is the `Initiates`-existence gap, `∃ s p, Act s p`, NOT horn-saturation:** `Act s p := Means s p ∧ ∃ w w', Initiates s w w' p` (`Agency.lean`) and no axiom of Γ supplies an `Initiates` witness — the corpus records as much at `ProofPresentationRetorsion.lean:95` ("CANNOT deduce `∃ s p, ClaimsNormativeCorrectness s p`"), with countermodel `syntactic_validity_without_subject_or_normativity` (`:100`, `{}`). **(3) The two discharges that do work, with premises named:** `derives_rejectedHornCoMeant` (C268) from a correctness-judgment, and `retorsion_implies_rejectedHornCoMeant` (C271) from the retorsion event. **(4) Consequence for the prose:** `base.txt:451`'s prohibition on the *silent* `ChoiceField → Chooses` conversion stands unchanged, and `base.txt:460`'s `?` is closed *with its premise*, never from `ChoiceField` alone |
| — | §30 | `AsieticChoice.TrueChoice : Subject → Prop → Prop → Prop := fun s p q => Chooses s p q ∧ OpenAlternative p q` — and, expanding the two (`Choice.lean:116`, `AsieticChoice.lean:132`), `fun s p q => Means s p ∧ Means s q ∧ Incompatible p q ∧ ContestedContent`. The *horn* form the C-rows use is the instantiation `TrueChoice s p (¬ p)`. And `AsieticChoice.Asiety : Entity → Prop := fun e => ∃ s p q, e = EntityOf s ∧ TrueChoice s p q` — **a `def` is not a claim.** `ASIETY_FREE.md` §0's literal reading "`Asiety := TrueChoice`" is false against the code: `Asiety` is Entity-indexed, and the identification is true by construction. The C-rows carry the theorems | — | `{}` |
| — | §30 | `AsieticChoice.ContestedContent` / `.OpenAlternative` — the frame-level definitions the chain rests on; `contested_content` (C259) and `open_alternative_is_incompatible` (C260) are their theorems | — | `{}` |
| — | §30 | `AsieticChoice.bareRejectedHornCoMeant : (∃ s : Subject, ∃ p : Prop, Means s p) → ∃ s : Subject, ∃ p : Prop, Means s p ∧ Means s (¬ p)` — **the named blocker** (D2). Before this batch the blocked implication existed only as prose at `Choice.lean:33-35`, under a label that collided with the `def rejectedHornCoMeant` at `Choice.lean:247` (which is the *consequent*); it is now a `def` in its own right, so F11 can cite it instead of quoting prose. Footprint and status are orthogonal: `{Means, Subject}` is what the definition *depends on*; `BLOCKED` is that it is not discharged | — | `{Means, Subject}` |
| — | §30 | `AsieticChoice.SingleContentSignature` (structure) and its members `Faithful`, `bareHorn`, `antecedentHolds`, `singleContentModel`, plus `antecedentHolds_in_canonicalModel` (C272) — the countermodel apparatus, all `{}`. The load-bearing field is **`faithful`** (`means s p → p`), not single-valuedness: from `p = ¬ p` no contradiction follows, because `p` need not be provable. Faithfulness turns `means t p ∧ means t (¬ p)` into `p ∧ ¬ p`, which `incompatible_self_negation` forbids | — | `{}` |

> Batch ASIETIC-CHOICE (2026-09-26): this batch closes the `?` of `base.txt:460` — *weak choice → strong
> choice* — **with its premise named and with zero new axioms**, and it is the first batch whose frontier row is
> *refuted* rather than merely open. 0 new axioms, 0 new `Tag:` axioms; the tally is unmoved at **25 declared
> (VOCAB 14 / SEM 7 / META 4)**, and that not moving is the test: every footprint above is drawn from
> `formal/axiom_audit.json`, so a new axiom would have shown up here. The batch has four parts.
> **(1) The definitional spine, free.** `TrueChoice`, `Asiety`, `ContestedContent`, `OpenAlternative` and the
> twelve vocabulary-only rows cost nothing: axiomatic modulo Γ's own declared vocabulary, and four of them
> (`{}`) not even that. **(2) The `?`, discharged under a named premise.** C266/C267/C268 give the co-signification
> of the rejected horn from a correctness-judgment (`AxJudicativeBipolarity`, `Tag: SEM`), and C269 makes the
> price of that premise visible in the footprint instead of in a claim about the world. The silent conversion
> `ChoiceField → Chooses` that `base.txt:451` forbids is **still forbidden**: what is new is a *priced,
> premise-named* conversion, and the difference is the whole content of C266. **(3) The performative route, and
> the answer to F1b's residue.** C270 discharges the meta-level horn at pinned content — a subject claiming
> "there is no genuine normativity" as correct thereby means both `NoGN` and `¬ NoGN` — which is the direct
> answer to residue (b) at `GAPMAP.md:758`; C271 gives the horn's consequent from the same event. Both state
> their premise `∃ s, ClaimsCorrect s NoGN`, which is `Act`-gated and therefore *not* derivable in Γ; that is
> disclosed, not hidden. What this does **not** answer is object/action content, which still needs the separate
> `DeliberateChoice` / `ClaimsNormativeCorrectness` route (C140/C141).
> **(4) The frontier, refuted.** F11 records the bare implication as `BLOCKED` **and** machine-backed: C273/C274
> build a model of the meaning vocabulary in which the antecedent holds and the consequent does not, so the
> blocker is a sentence false in a model rather than an artefact of an unsuccessful search. This is what makes
> the positive results above credible — the one form that does *not* follow is refuted outright, so nothing
> positive here rests on a hidden assumption. Three demarcations are recorded so a later pass cannot quietly
> upgrade them: C282 **refutes** `CanonicalAseity → TrueChoice` (adding that bridge would break Γ), C283 keeps
> the ground out of the chooser inventory under the honest conditional, and C284 is the definitional block
> (`ofGround_ne_ofSubject`). And one weakness is disclosed rather than papered over: C261 proves
> `TrueChoice ≡ Chooses`, because the openness conjunct is a **global frame fact** and not a per-pair
> modality — so "true choice" adds nothing over "strong choice", and the batch's real content is the two
> substantive steps plus the unconditional existence of C279–C281.

## Level 19 — Asiety from Act-free Weak Choice, and the Ground's Sharing of It (`Logos.AsietyFreedom`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C287 | §31 | `AsietyFreedom.weakChoice_implies_asiety {s : Subject} {p q : Prop} (h : GenuineNormativity s p q) : Asiety (EntityOf s)` — **L1, the axiom-free step the corpus asked for**: a subject addressed by *genuine normativity* is an asietic subject, so **asiety follows from the Act-free weak choice**. `GenuineNormativity` (`IndubitableNormativeFreeWill.lean:84`) carries both horns in its `address` field (`Means s p ∧ Means s q`, `:78`) and the incompatibility in `opposition.1` (`:72`); the sole content beyond them is the frame's `ContestedContent` (C259, `{}`). **No `Act`, no `Initiates`, no `ClaimsCorrect`, no `AxJudicativeBipolarity`, no `AxTwoSubjects`, no stipulation** — the footprint is Γ's own vocabulary and nothing else | PROVEN | `{Means, Subject}` |
| C288 | §31 | `AsietyFreedom.weakChoice_implies_freeWill {s : Subject} {p q : Prop} (h : GenuineNormativity s p q) : FreeWill s` — the same step read in the `FreeWill` direction, kept as a separate row so it is not confused with C287: neither closes the `?` of `base.txt:460`, which stays discharged only under the `ClaimsCorrect` premise and whose bare form stays refuted (C273/C274). L1 routes *around* that `?` by starting from a premise that already contains both horns | PROVEN | `{Means, Subject}` |
| C289 | §31 | `AsietyFreedom.asietyFreedom_yields_trueChoice (h : AsietyFreedomOfGround) {s : Subject} {p q : Prop} (hG : GroundsEntity Entity.ofGround (EntityOf s)) (hA : Asiety (EntityOf s)) : TrueChoice s p q` — **L2, and it carries the stipulation ◈ `asietyFreedom_ofGroundFreedom` (`Tag: META`)**: the ground's freedom reaches the subjects it grounds, so an asietic subject makes a true choice at **every** incompatible pair, not only at the pair witnessing its asiety. The `GroundsEntity` premise is **vacuous** (`EntityMeans .ofGround p := True`), so all the weight sits in the leading universal quantifier, and C292 prices it. Status is `PROVEN` because the *inference* is machine-checked and axiom-free; the ◈ badge, not the footprint, is where the price is visible | PROVEN | `{Means, Subject}` |
| C290 | §31 | `AsietyFreedom.asietyFreedom_yields_asietyFreeWill (h : AsietyFreedomOfGround) {s : Subject} (_hG : GroundsEntity Entity.ofGround (EntityOf s)) (hA : Asiety (EntityOf s)) : AsietyFreeWill s` — **"which is shared with us by the creator"**: the ground's freedom, shared. One row, not two: the ledger's name (the mechanism) and the corpus's name (the Creator's sharing) are the *same inference*, and two declarations would be one proposition wearing two C-ids. The vacuous premise is named `_hG` and named *vacuous* in the docstring rather than dropped, so the `{}`-looking footprint cannot be mistaken for depth | PROVEN | `{Means, Subject}` |
| C291 | §31 | `AsietyFreedom.asietyFreeWill_yields_trueChoice {s : Subject} {p q : Prop} (h : AsietyFreeWill s) (hG : GroundsEntity Entity.ofGround (EntityOf s)) : TrueChoice s p q` — the other direction of the author's sentence, "`AsietyFreedom` gives rise to true choice *and* `AsietyFreeWill`": here `AsietyFreeWill` gives rise to true choice. Rests entirely on the stipulated first conjunct of `AsietyFreeWill`; the second supplies the witness | PROVEN | `{Means, Subject}` |
| C292 | §31 | `AsietyFreedom.asietyAloneDoesNotYieldTrueChoice : ∃ (S : Type) (M : S → Prop → Prop) (I : Prop → Prop → Prop) (C : Prop) (s₀ s₁ : S) (p q : Prop), I p q ∧ M s₀ p ∧ M s₀ q ∧ C ∧ ¬ (M s₁ p ∧ M s₁ q ∧ I p q ∧ C)` — **the price of the stipulation, machine-checked**: a subject can have asiety (it means both horns of an incompatible pair, and the frame's contested-content conjunct holds) while a second subject lacks true choice at the *very same* pair. So the universal quantifier over subjects in `AsietyFreedomOfGround` is doing real work, and the weaker **existential** reading — "the ground's freedom is shared with *some* one" — is a strictly cheaper stipulation that would still deliver C290. Recorded as the counterpart of that weaker reading so the strong one's price is visible rather than assumed | COUNTERMODEL | `{}` |
| C293 | §31 | `AsietyFreedom.frameContingencyDoesNotBindAPair : ∃ (C : Prop) (PairContested : Prop → Prop) (p : Prop), C ∧ ¬ PairContested p` — **why `TrueChoice ≡ Chooses` (C265) is forced rather than lazy**: the global contested-content fact holds while the per-pair contestedness of a given `p` fails. The countermodel carries a **withheld** per-pair predicate `PairContested`, holding nowhere — a model importing Γ's own vocabulary cannot express this, because the per-pair binding is precisely what is in dispute (`Incompatible` is `Prop`-level, `NecessarilyTrue` is `Form`-level, and Γ has no `Prop ↔ Form` bridge) | COUNTERMODEL | `{}` |
| C294 | §31 | `AsietyFreedom.rightWrongFactYieldsNoChooser : (¬ N_T ∧ ¬ N_F) ∧ ∃ (S : Type) (M : S → Prop → Prop), ¬ (∃ s : S, ∃ p q : Prop, M s p ∧ M s q)` — **the existence limit**: the author's own fact, `Core.rightWrongDistinction : ¬ N_T ∧ ¬ N_F` (`Core.lean:145`, `{}`), is a fact about **contents** — it quantifies over no `Subject`. So it is compatible with a meaning-vocabulary in which no subject means anything (`S := Unit`, `M := fun _ _ => False`), and therefore **no axiom-free existence of a chooser**. The Creator-sharing step is consequently stated *conditionally*, and its existence half is recorded as not derivable rather than asserted; the unconditional existence half still costs `AxTwoSubjects` (META), as C277–C279 already disclose. Note the `∃`, not `∀`, over vocabularies: no `False` follows from `M s p` for an arbitrary `M`, so a universally quantified form would have been unsound rather than strong | COUNTERMODEL | `{}` |
| C295 | §31 | `AsietyFreedom.groundIsNotASharerOfAsietyFreeWill : ¬ ∃ s : Subject, EntityOf s = Entity.ofGround ∧ AsietyFreeWill s` — **coherence with C285**: `AsietyFreedomOfGround` quantifies over *subjects* and says the ground's freedom reaches them, so it does **not** put the ground inside the chooser inventory. `AsietyFreedom` is a characteristic of the ground *as ground*; the ground remains canonically aseitous-but-not-asietic under C284's honest conditional, and participation is not identity. Proof is C285's `ofGround_ne_ofSubject` and nothing more — stated so a later pass cannot read the new chain as contradicting the old | PROVEN | `{Means, Subject}` |
| C296 | §31 | `AsietyFreedom.asietyFreedom_summary : (∀ (s : Subject) (p q : Prop), GenuineNormativity s p q → Asiety (EntityOf s)) ∧ ((h : AsietyFreedomOfGround) → ∀ (s : Subject) (p q : Prop), GroundsEntity Entity.ofGround (EntityOf s) → Asiety (EntityOf s) → TrueChoice s p q) ∧ (∀ (s : Subject) (p q : Prop), AsietyFreeWill s → GroundsEntity Entity.ofGround (EntityOf s) → TrueChoice s p q) ∧ (¬ N_T ∧ ¬ N_F) ∧ (¬ ∃ s : Subject, EntityOf s = Entity.ofGround ∧ AsietyFreeWill s)` — **master synthesis** of the batch, conflating the axiom-free L1, both ◈-bearing transfers, the author's right/wrong fact, and the ground's exclusion from the chooser inventory, so the whole chain and both of its prices are readable in one row | PROVEN | `{Means, Subject}` |
| — | §31 | `AsietyFreedom.AsietyFreedomOfGround : Prop := ∀ (s : Subject) (p q : Prop), GroundsEntity Entity.ofGround (EntityOf s) → Asiety (EntityOf s) → TrueChoice s p q` — the **stipulated** predicate, ◈ `asietyFreedom_ofGroundFreedom` (`Tag: META`, `Stipulations.lean`). **A `def` is not a claim, and a stipulation is not an axiom**: being a `def`, it is *invisible to `#print axioms`*, so no axiom-counting tool will ever flag it. That is exactly why it is registered in the stipulation registry and badged in the README — the badge is the only place the price is visible. Not derivable, for three independent blocks: `GroundsEntity` is vacuous (`LovesAsGround.lean:194`: `intro p _; exact True.intro`), the only non-vacuous grounding predicate `GroundsRightWrong` is definitionally `∃ p q, Chooses s p q` (C168), and the substantive grounding relation is `BLOCKED` (C228) | — | `{Means, Subject}` |
| — | §31 | `AsietyFreedom.AsietyFreeWill (s : Subject) : Prop := AsietyFreedomOfGround ∧ Asiety (EntityOf s)` — the shared-freedom predicate. Checked against the corpus's own anti-dishonesty rule: `TrueChoice` is **not** a conjunct, so this is not a projection of the conclusion it is used to derive; ground-participation and subject-asiety are two different things, conjoined | — | `{Means, Subject}` |
| C300 | §32 | `AsietyFreedom.weakChoice_yields_trueChoice {s : Subject} {p q : Prop} (h : GenuineNormativity s p q) : TrueChoice s p q` — **the derived side at its actual maximum, axiom-free and without ◈: true choice at the *specified* pair.** This is the strongest statement reachable from the batch's own starting hypothesis, and it strictly dominates C297. **How little work it is:** `Chooses s p q := Means s p ∧ Means s q ∧ Incompatible p q` (`Choice.lean:116`) and `OpenAlternative p q := Incompatible p q ∧ ContestedContent` (`AsieticChoice.lean:132`), so the two fields of `GenuineNormativity` — `opposition : Incompatible p q ∧ (p ≠ q)` and `address : Means s p ∧ Means s q` (`IndubitableNormativeFreeWill.lean:72,78`) — are *literally* the two conjuncts of `Chooses`; the sole input not already in `h` is the `{}` frame fact `ContestedContent`. The `p ≠ q` field is not even used. **This sharpens §0.2 rather than rescuing L1:** the axiom-free content of L1 is that the hypothesis already contains the choice and the world is contingent. **The bound is part of the row:** the *given* pair only. What ◈ therefore buys is *extension from the given pair to every incompatible pair* — **not** the existence of a pair, which was already free. The stipulation is paying for less than the C297 framing advertised | PROVEN | `{Means, Subject}` |
| C297 | §32 | `AsietyFreedom.asiety_yields_witnessed_trueChoice {s : Subject} (h : Asiety (EntityOf s)) : ∃ p q : Prop, TrueChoice s p q` — axieticity *already* carries a witnessed true choice, axiom-free and without ◈. **Not the derived side "at full strength": that claim was made here and withdrawn on 2026-09-26 (see `AsietyFreedom.md` §0.6.8). This row is strictly weaker than C300**, which delivers `TrueChoice` at the *specified* pair; this one existentially closes it. Retained, not deleted — the form the `Asiety` route needs. The content is `Asiety`'s own unfolding (`Asiety e := ∃ s, ∃ p q, e = EntityOf s ∧ TrueChoice s p q`, `AsieticChoice.lean:147`); the only work is the injectivity of `EntityOf`, i.e. constructor injectivity. **The bound is part of the row, not a caveat:** a *witnessed* pair only. The author's claim needs `TrueChoice s p q` at **every** incompatible pair, and that extension is exactly what ◈ asserts and exactly what C292/C299 price — so this row fixes the width of the gap and neither discharges nor softens the stipulation | PROVEN | `{Means, Subject}` |
| C298 | §32 | `AsietyFreedom.asiety_yields_freeWill {s : Subject} (h : Asiety (EntityOf s)) : FreeWill s` — the same derived side in the `FreeWill` direction, which is the form the sentence "the ground's freedom, shared" actually needs. Axiom-free, no ◈, and equally bounded: `FreeWill s` is `∃ p q, Chooses s p q`, so it too is a witnessed pair rather than every pair. Recorded as its own row so the corpus is not left claiming that the *only* free-will fact available from asiety is C288's, which starts from `GenuineNormativity` | PROVEN | `{Means, Subject}` |
| C299 | §32 | `AsietyFreedom.groundingCannotDeliverTrueChoice : ∃ (E : Type) (M : E → Prop → Prop) (I : Prop → Prop → Prop) (C : Prop) (g s₀ s₁ : E) (p q : Prop), (∀ v, M g v) ∧ (∀ e, ∀ v, M e v → M g v) ∧ I p q ∧ C ∧ M s₀ p ∧ M s₀ q ∧ ¬ (I p q ∧ M s₁ p ∧ M s₁ q ∧ C)` — **the price of ◈ in its strongest available form, and the machine-checked reason the stipulation is `BLOCKED` rather than merely unasserted.** Stated over *any* relation of **containment shape** (`∀ v, M e v → M g v`), so it is not an artefact of the vacuity at `LovesAsGround.lean:194`. **Scope limit (2026-09-26 correction):** this does *not* rule out a relation of some *other* shape — that is precisely the missing vocabulary of F12(1), which stays open. The block is serious, not permanent. The countermodel grants the premise **in full** — a ground of total meaning-capacity (`∀ v, M g v`, exactly what ◈ `ofGround_meansAll` buys for `Entity.ofGround`) and the containment premise **at every entity** (`∀ e v, M e v → M g v`, `GroundsEntity` verbatim, hence holding at `s₁` too) — and still denies the conclusion at the *same* pair. **Consequence for the corpus, and it corrects the earlier framing:** the disease is not that the premise is weak, it is that a *content-transfer* relation has no route to a *choice of contents*. Making the ground's meaning-capacity non-trivial would not repair the transfer; it would only make an irrelevant premise less obviously irrelevant. `base.txt` §31's "still requires proof" list is written accordingly | COUNTERMODEL | `{}` |
| — | §32 | `AsietyFreedom.groundFreedomSharedWithSomeone : Prop := ∃ (s : Subject), AsietyFreeWill s` — **the Creator-sharing obligation, named**, so frontier row F13 cites a declaration instead of quoting prose (the `F11` / `bareRejectedHornCoMeant` precedent). "…shared with **us** by the creator" is an *existence* claim, and this is the statement of it. Naming it does not advance it: it is `BLOCKED` and its derivation is **refuted, not merely open** (F13, via C294). Like the other two `def`s here it is invisible to `#print axioms`, so its price is the frontier row's, not the footprint's | — | `{Means, Subject}` |

| F12 | §32 the missing justification for ◈ `asietyFreedom_ofGroundFreedom`: the ground's being the ground of *freedom* follows from Γ's grounding vocabulary | BLOCKED | **now nameable in both halves, and the second is machine-refuted rather than open.** **(1) MISSING VOCABULARY:** a *substantive* grounding relation relating `Entity.ofGround` to the normative content of a subject. Γ declares none: the only entity-level relation is `GroundsEntity` (`RecoveredOntologicalGround.lean:57`), whose subject-side transfer is vacuous because `EntityMeans Entity.ofGround p := True` (LovesAsGround.lean:194, ◈ `ofGround_meansAll`), and the only non-vacuous grounding predicate, `GroundsRightWrong`, is definitionally `∃ p q, Chooses s p q` (C168) — i.e. already free will, so using it as the antecedent would be circular. The substantive relation stays `BLOCKED` at C228, with its named lemma verbatim. **(2) MISSING DERIVATION:** from such a relation plus `Asiety (EntityOf s)`, derive `TrueChoice s p q` at **every** incompatible pair. C299 (`{}`) is the machine-checked reason this cannot be discharged from a premise of `GroundsEntity`'s shape: it grants the containment premise in full — total ground meaning-capacity, and the premise at *every* entity — and still finds a first subject with genuine asiety and a second, equally grounded subject with no true choice at the same pair. **So the obstruction is structural, not a matter of strengthening the premise:** a content-transfer relation has no route to a choice of contents, and only the witnessed-pair form is derivable (C297/C298). **Consequence for the prose:** ◈ (we chose to assert it) and `BLOCKED` (we cannot justify it) are now both on the record, which is the state `AsietyFreedom.md` §0 argued the ledger was missing |
| F13 | §32 the Creator-sharing existence claim: the ground's shared freedom reaches **someone** | BLOCKED | **nameable, and refuted as derivable rather than open.** The obligation is `Logos.AsietyFreedom.groundFreedomSharedWithSomeone : Prop := ∃ (s : Subject), AsietyFreeWill s` (F13's named `def`). C294 (`{}`) is the refutation: `Core.rightWrongDistinction : ¬ N_T ∧ ¬ N_F` is a fact about **contents** — it quantifies over no `Subject` — and is compatible with a meaning-vocabulary in which no subject means anything (`S := Unit`, `M := fun _ _ => False`), so it delivers no sharer. The unconditional existence half remains the pre-existing `AxTwoSubjects` (META) route of C277–C279, and nothing in this batch prices it away. **Consequence for the prose:** the batch's strongest negative result was previously a footnote inside a module; it is now a citable frontier row and an entry in `base.txt` §31's "still requires proof" list |

> Batch ASIETY-FREEDOM (2026-09-26): this batch does what `Level 18` left open, and it does it in two
> steps of deliberately unequal price. **0 new axioms, 0 new `Tag:` axioms**; the tally is unmoved at
> **25 declared (VOCAB 14 / SEM 7 / META 4)** — and the *mechanism* of that invariance is the point:
> because `AsietyFreedomOfGround` is a `def` and not an `axiom`, `#print axioms` cannot see it, so the
> invariant "the count did not move" is **not by itself evidence that nothing was assumed**. The ◈
> registry entry and the README badge are what make the L2 price visible, and they are load-bearing rather
> than decorative.
> **(1) L1 is genuinely axiom-free (C287, C288).** Asiety follows from the *Act-free* weak choice:
> `GenuineNormativity` contains no `Act`, no `Initiates` and no `ClaimsCorrect`, and the only content
> beyond its two `Means` conjuncts is the `{}` frame fact `ContestedContent` (C259). This closes the gap
> `Level 18` could not: C266/C267 needed `AxJudicativeBipolarity` (SEM) *and* the `ClaimsCorrect`
> premise, whereas C287 needs neither. **Honest caveat, stated in the docstring and not buried:** C287 is
> close to a projection, because `AgentialDeonticAddress` already *is* `Means s p ∧ Means s q`; what it
> adds over `indubitable_normative_free_will` (C276) is the openness conjunct and nothing else. That
> theorem is itself disclosed as a sub-formula extraction, not a derivation: it discards the `p ≠ q`
> field and reorders three of the four conjuncts, so its `{Means, Subject}` footprint records the
> *structure's* fields, not an inference from independent premises.
> **(2) L2 is a declared bridge, not a derivation (C289, C290, C291).** Because the ground's being the
> ground of *freedom* cannot be derived from Γ's grounding vocabulary (three independent blocks, above),
> it is registered as ◈ `Tag: META` following the `operatesAt_presencePlusObtaining` precedent, and its
> price is machine-checked rather than asserted: C292 shows the universal reading is strictly stronger
> than the existential one, C293 shows why `TrueChoice ≡ Chooses` (C265) is forced, and C294 shows the
> right/wrong fact is silent on choosers. **The corpus's "no axioms in the chain" is therefore honoured in
> the only sense it can be**: L1 has none, and L2 is a *disclosed, priced* stipulation that does not
> touch the axiom ledger. Claiming more than that would be the dishonest move, and it is not made.
> **(3) What is refuted, not merely open.** No axiom-free **existence** of a chooser (C294): the
> Creator-sharing step is therefore conditional, and the unconditional existence half is still the
> pre-existing `AxTwoSubjects` route of C277–C279. The bare rejected horn stays refuted (C273/C274) and
> `base.txt:460`'s `?` stays discharged only under its `ClaimsCorrect` premise — L1 goes around that `?`,
> it does not close it. And the ground is still not a chooser (C295, preserving C284/C285): the new chain
> cannot be read as putting the ground inside the chooser inventory, because `AsietyFreedomOfGround`
> quantifies over subjects and asserts *participation*, not identity.

## Level 20 — The Four Senses of Externality, and the Boundary of the Diagonal Route (`Logos.DivineTranscendence`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C301 | §33 | `DivineTranscendence.per_system_outside_points_need_not_coalesce : ∃ (S : Type) (In : S → Entity → Prop), EachSystemHasAnOutside S In ∧ ¬ (∃ e : Entity, OutsideEverySystem S In e)` — **the load-bearing refutation**: the quantifier swap of `CHARACTERISTICS.md:64` is machine-checked false. Two complementary systems (`true` holds everything but the ground, `false` holds only the ground); each system has an outside, yet no point is outside them all. The machine-checked justification for the retirement of C88 `transcendental_quantifier_swap` | COUNTERMODEL | `{Subject}` |
| C302 | §33 | `DivineTranscendence.externality_to_every_system_is_consistent : ∃ (S : Type) (In : S → Entity → Prop) (e : Entity), OutsideEverySystem S In e` — **the conclusion is consistent, not destroyed.** Witness: a one-system family containing nothing. C301 refutes an *inference*; C302 shows the *conclusion* is satisfiable, so the batch bounds a real claim rather than refuting a fiction | COUNTERMODEL | `{Subject}` |
| C303 | §33 | `DivineTranscendence.universal_grounding_places_the_ground_inside_a_system : ∃ (S : Type) (In : S → Entity → Prop), (∀ e : Entity, ActualEntity e → e = Entity.ofGround ∨ GroundsEntity Entity.ofGround e) ∧ ¬ OutsideEverySystem S In Entity.ofGround` — the swap fails concretely at the canonical ground, using `ofGround_ground_of_reality` (`NecessityEternity.lean:140`) **verbatim**: the ground really does ground all actual reality and is nonetheless inside an ordinary membership class. Grounding is not externality | COUNTERMODEL | `{Means, Subject}` |
| C304 | §33 | `DivineTranscendence.membership_exclusion_does_not_entail_grounding_exclusion : ∃ (S : Type) (In : S → Entity → Prop) (Gr : S → Entity → Entity → Prop) (e : Entity), OutsideEverySystem S In e ∧ GroundedInSystem S In Gr e` — the **hierarchical** sense separates: nonmembership of every class does not deliver being ungrounded. Witness: an atom of the singleton ground-class lies outside every class yet is grounded by a member of the class | COUNTERMODEL | `{Subject}` |
| C305 | §33 | `DivineTranscendence.ofGround_external_to_every_class_may_still_be_ordered : ∃ (S : Type) (In : S → Entity → Prop) (Gr : S → Entity → Entity → Prop), OutsideEverySystem S In Entity.ofGround ∧ GroundedInSystem S In Gr Entity.ofGround` — the same separation instantiated at the ground. The order relation is abstract on purpose: the ground is *provably* ungrounded by every atom (`CanonicalAseity.lean:96`, `atom_cannot_ground_the_ground`), so Γ's own `ExternalGrounding` cannot exhibit the ordering. That impossibility is part of the finding | COUNTERMODEL | `{Subject}` |
| C306 | §33 | `DivineTranscendence.universal_grounding_does_not_entail_causal_externality : ∃ (S : Type) (Caus : S → Entity → Entity → Prop), (∀ e : Entity, ActualEntity e → e = Entity.ofGround ∨ GroundsEntity Entity.ofGround e) ∧ ¬ CausalExternality S Caus Entity.ofGround` — the **causal** sense separates: grounding all reality delivers no causal externality under *any* production relation. Γ declares none, the only initiation relation being `Agency.Initiates` (VOCAB, subject-indexed) | COUNTERMODEL | `{Means, Subject}` |
| C307 | §33 | `DivineTranscendence.ofGround_sole_transcendent_ground : ∀ (e : Entity), TranscendentGround e → e = Entity.ofGround` — **sole candidacy**, the one new PROVEN result. C195 establishes that the ground *is* transcendent and C213 only restates it; **no row said it is *uniquely* transcendent**. Both eliminations are `TranscendentGround`'s own non-identity clauses and the three constructors of `Entity` exhaust the inventory | PROVEN | `{Subject}` |
| C308 | §33 | `DivineTranscendence.diagonal_does_not_deliver_system_externality : ∀ (Subj : Type) (Means : Subj → Prop → Prop) (_diag : NegativeRetorsionAudit.DiagonalSpec Subj Means), ∃ (S : Type) (In : S → Entity → Prop), ¬ (∃ e : Entity, OutsideEverySystem S In e)` — **the price of the diagonal.** The *whole* `DiagonalSpec` is granted, and no entity need be outside every system: the diagonal's externality is externality from *entertainment* (`Means`), `OutsideEverySystem` is externality from *membership* (`In`), and Γ identifies them nowhere. **The premise `_diag` is inert, and that is the result, not an encoding defect** — the statement holds for *every* `DiagonalSpec` | COUNTERMODEL | `{Subject}` |
| C309 | §33 | `NegativeRetorsionAudit.level6_diagonal_meant_implies_false : ∀ {Subj : Type} {Means : Subj → Prop → Prop} (diag : DiagonalSpec Subj Means), (∃ s : Subj, Means s diag.D) → ¬ diag.D` — **ledgered, pre-existing** (`NegativeRetorsionAudit.lean:521`). Entering the diagonal refutes it | PROVEN | `{}` |
| C310 | §33 | `NegativeRetorsionAudit.level6_diagonal_true_implies_unmeant : ∀ {Subj : Type} {Means : Subj → Prop → Prop} (diag : DiagonalSpec Subj Means), diag.D → ¬ ∃ s : Subj, Means s diag.D` — **ledgered, pre-existing** (`:530`). The diagonal's specification, one direction at a time | PROVEN | `{}` |
| C311 | §33 | `NegativeRetorsionAudit.level6_model_diagonal_true_consistent : ∃ (Subj : Type) (Means : Subj → Prop → Prop) (diag : DiagonalSpec Subj Means), diag.D ∧ ¬ ∃ s : Subj, Means s diag.D` — **ledgered, pre-existing** (`:538`). The diagonal is consistent as *true-and-unmeant* | COUNTERMODEL | `{}` |
| C312 | §33 | `NegativeRetorsionAudit.level6_model_diagonal_false_consistent : ∃ (Subj : Type) (Means : Subj → Prop → Prop) (diag : DiagonalSpec Subj Means), ¬ diag.D ∧ ∃ s : Subj, Means s diag.D` — **ledgered, pre-existing** (`:560`). The diagonal is consistent as *false-and-meant* | COUNTERMODEL | `{}` |
| — | §33 | `DivineTranscendence.OutsideEverySystem (S : Type) (In : S → Entity → Prop) (e : Entity) : Prop := ∀ σ, ¬ In σ e` — **the logical sense**, four names and no umbrella, as `CHARS.md:144` requires | VOCABULARY | `{Subject}` |
| — | §33 | `DivineTranscendence.EachSystemHasAnOutside (S : Type) (In : S → Entity → Prop) : Prop := ∀ σ, ∃ e, ¬ In σ e` — the prose's step-1 premise in its weakest form: says nothing about whether the outsides coincide | VOCABULARY | `{Subject}` |
| — | §33 | `DivineTranscendence.GroundedInSystem (S : Type) (In : S → Entity → Prop) (Gr : S → Entity → Entity → Prop) (e : Entity) : Prop := ∃ σ, ∃ g, In σ g ∧ Gr σ g e` — **the hierarchical sense**'s inner clause. The grounding relation is a parameter because Γ's own `GroundsEntity` is vacuous at the ground (`EntityMeans Entity.ofGround p := True`, `NecessaryPersonalGround.lean:151-155`) | VOCABULARY | `{Subject}` |
| — | §33 | `DivineTranscendence.HierarchicalExternality (S : Type) (In : S → Entity → Prop) (Gr : S → Entity → Entity → Prop) (e : Entity) : Prop := (∀ σ, ¬ In σ e) ∧ ¬ GroundedInSystem S In Gr e` — outside every system **and** grounded in none: strictly stronger than `OutsideEverySystem`, and C304 machine-checks that the two come apart | VOCABULARY | `{Subject}` |
| — | §33 | `DivineTranscendence.CausalExternality (S : Type) (Caus : S → Entity → Entity → Prop) (e : Entity) : Prop := ∀ σ, ∀ g, ¬ Caus σ g e` — **the causal sense**, stated over an abstract relation because Γ declares no production relation | VOCABULARY | `{Subject}` |

| F14 | §33 the Gödel/Tarski/Turing route as a *transcendental* argument: a system cannot supply its own evaluative foundation, therefore the foundation lies external to every system | BLOCKED | **now nameable, bounded, and its in-Γ evidence points the other way.** *What is machine-checked:* (i) the self-referential **shape** is already formalized in Γ — `NegativeRetorsionAudit.DiagonalSpec` (`NegativeRetorsionAudit.lean:515`), `D ↔ ¬ ∃ s, Means s D`, with four `{}` consequences now ledgered at C309–C312; (ii) **the diagonal is never paradoxical** in either direction (C311 true-and-unmeant, C312 false-and-meant), so it yields no contradiction and therefore no forced foundation; (iii) granting the *whole* diagonal still does not deliver an entity external to every system (C308), because the diagonal's externality is from *entertainment* and `OutsideEverySystem` is from *membership*. *The missing lemma, verbatim:* a fixed-point coding — `Code : Nat → Form`, `Subst : Form → Code → Form`, `Diag : Form → Code`, and an internal truth predicate `Truth : Form → Prop` with `Truth (quote φ) ↔ φ` and `∀ φ, ¬ Truth (Diag φ)` — of which Γ declares **none**; `Form`, `Satisfies` and `NecessarilyTrue` (`Semantics.lean:22,44,58`) are meta-level and no `Form → Prop` truth predicate exists anywhere in `Logos/`. *Correction to the record:* the module header of `Logos.DivineTranscendence` previously dismissed the diagonal by claiming self-application "is not expressible in Lean 4's `Prop`". **That was wrong and is retracted in place** — self-application is expressible; the real obstacle is the absent coding vocabulary. *Scope limit:* this does **not** show the route is hopeless, only that it is a **missing-vocabulary** problem whose available in-Γ evidence does not favour it, and that the liar remains blocked for the independent reason recorded at `base.txt:219` (no self-referential proposition is assumed) |
| F15 | §28 Foundational Unicity: the ground of reality is the **sole** universal ground — no subject of total meaning-capacity competes with it | AXIOM | **DECLARED 2026-09-28 — no longer `BLOCKED`.** The missing lemma is now the declared axiom `SemanticFinitude` (C388, `Tag: VOCAB`), the 27th axiom; the ten unicity/attribute lines C389–C398 are unconditional theorems of Γ. Status changed `BLOCKED` → `AXIOM` by author decision: the sentence is *not derivable* and is not claimed to be — it is a priced, declared, machine-audited restriction of the meaning vocabulary. The price is now visible in every dependent footprint, where before (as a `def`-stipulation) it was invisible to `#print axioms`. *Original assessment, retained:* **now nameable, and no new axiom is needed.** *What is machine-checked:* (i) C210 (`Logos.FoundationalUnicity.ofGround_sole_universal_ground`) already excludes every entity **except** one case it cannot touch — a subject meaning *every* proposition, which no uninterpreted `Logos.Agency.Means` can be shown not to be; (ii) C314 (`Logos.FoundationalUnicity.grounds_ground_iff_maximal`) proves that "grounds the ground" **is** `Logos.FoundationalOmnipresence.MaximalCapacity` (`FoundationalOmnipresence.lean:119`), so the needed notion was already in the corpus and `GroundMaximal` is withdrawn as an invention; (iii) C317 (`Logos.FoundationalUnicity.ofGround_unicity_from_no_discriminating_subject`) closes the last case from the single hypothesis `∀ s, ∃ p, ¬ Means s p`, and **C320 (`Logos.FoundationalUnicity.exactly_one_universal_modal_ground`) states Classical Monotheism outright** (existence unconditional, uniqueness under that one hypothesis). *The missing lemma, verbatim:* `∀ s : Subject, ∃ p : Prop, ¬ Means s p` — i.e. **every subject is meaning-restricted**. *Why it is not derivable:* `Logos.Agency.Means` is VOCAB (`Agency.lean:49` declares `Logos.Agency.Subject` as a nullary uninterpreted sort) and is unconstrained above; nothing in Γ bounds a subject's propositional reach, and the `Existential`-style universality results elsewhere do not apply because the needed bound is per-subject, not global. *The price, stated honestly — and it is NOT a new payment:* this is a **restriction on the meaning vocabulary**, i.e. it says no creature is semantically omnipotent. It is *not* a META bridge and *not* a new definition — it is one quantified sentence over existing vocabulary, and C318 proves it equivalent to the exclusion of maximal capacity among non-ground entities. **Correction (2026-09-27, found while landing C320): the identical hypothesis is ALREADY the standing premise of the corpus.** `DivineSimplicity.canonical_aseity_conditional` (`DivineSimplicity.lean:79`), `DivineSimplicity.ofGround_divine_simplicity` (`:180`) and `DivineSimplicity.ofGround_divine_simplicity_and_transcendence` (`:191`) all take `hFinite : ∀ s : Subject, ∃ p : Prop, ¬ Means s p` — the *same sentence, character for character* — and C195/C196 are ledgered on it. **Second correction (2026-09-27, same day): "three call sites" was a file-local count and badly understated the case.** The hypothesis shape `∀ s : Subject, ∃ p : Prop, ¬ Means s p` occurs **20 times across 5 files** — `DivinePureActuality` 5, `FoundationalUnicity` 7, `CanonicalAseity` 4, `AsieticChoice` 1, `DivineSimplicity` 3. So the corpus pays this exact price for **five** attribute arguments (aseity, simplicity, pure actuality, choice/freedom, unicity), not two, and the already-paid case is *stronger* than the first correction claimed. Γ is no richer for it. F15 was therefore **not a new act of faith**: before the declaration it was an *unnamed* commitment, passed ad hoc wherever a bounded meaning capacity was needed — which is why declaring it once is a consolidation rather than an addition.  *What the batch explicitly did **not** do:* it did not weaken C207 or C211 (both remain PROVEN as conditional theorems) and did not delete them; C316 records that their shared premise is unsatisfiable, and C317–C320 supersede the route rather than the rows. ~~**What remains is bookkeeping, not belief:** because no *axiom* asserts it — it is passed as an explicit argument at each of the 20 ad-hoc call sites — C320 cannot consume it unconditionally, so F15 stays a frontier row. The fix is to consolidate the ad-hoc premises into **one named ◈ stipulation** (`Tag: VOCAB`) and re-point C320 at it (the other 19 users incrementally), which would make C320 an unconditional corollary and retire this row. That is a single, already-paid sentence rather than a new bridge, but it does move the registry from 25 declared axioms, so it is put to the author rather than done silently.~~ **SUPERSEDED 2026-09-28, on all four counts** (this paragraph was still printed inside the row it contradicts): the sentence is now a **declared `axiom`** (C388), the unicity is **unconditional** (C389, no hypothesis parameter), the ◈ `semanticFinitude` was registered and then **retired** (`Stipulations.lean:20`, 8 → 7), and the registry is **27**, not 25. The only residue that is still real is incremental: 19 ad-hoc call sites still pass the bound as an explicit argument instead of reading the axiom, which `scripts/census_semantic_finitude.py --check` counts (`any = 19`, `forall = 14`) and which is cosmetic, not a gap. |
| F16 | §28 Immutability: meaning capacity is constant *across worlds* (the substantive reading of the capacity-invariance predicate) | BLOCKED | **missing vocabulary, not a missing proof.** The substantive claim cannot be *stated*, because the meaning relation is `Logos.RecoveredOntologicalGround.EntityMeans (e : Entity) (p : Prop) : Prop` (`RecoveredOntologicalGround.lean:46`) — world-independent by construction. There is no `Entity → World → Prop → Prop` relation anywhere in the library, so "capacity varies / invariance across worlds" has no denotation. C321 proves the world-free reading is a tautology; F16 is the reading the classical text actually wants (Aquino *ST* I q. 9 a. 3, *idem actus semper et similiter est*), and it stays open. **O preço de F16 passou a ser teorema (2026-09-28, C427/C428):** `DivineImmutability.no_world_indexed_extension_of_meaning_can_vary` (C427, `{Means, Subject}`) prova que **nenhuma** relação que concorde com `EntityMeans` em todo o mundo pode exibir capacidade variável, e `world_indexed_extension_of_meaning_is_world_constant` (C428, mesma pegada) dá a invariância em forma construtiva. O que muda não é o estado de F16 — continua BLOCKED, e `EntityMeansAt` continua por adicionar — mas a **certeza de que o bloqueio é forçado**: a variação, se existir, tem de vir de vocabulário novo, e não de uma re-leitura do existente. A linha que falta é a mesma, por extenso, e a justificativa passou de frase a proposição verificada. *The missing statement, verbatim:* a relation indexed by world, `EntityMeansAt : Entity → World → Prop → Prop`, together with a proof that some entity's meaning capacity genuinely *fails* to be world-constant — so that the invariance is a discriminator. *Why it is not derivable:* adding the world index is a new primitive, so the price is new vocabulary, and tagging it honestly would cost `SEM` at minimum. **Not added — author decision.** The same wall as F10's missing `Produces` relation. |

> Batch SYSTEM-EXTERNALITY (2026-09-27): this batch is about **what the word "external" was doing**, and it is deliberately mostly negative. **0 new axioms, 0 new `Tag:` axioms**; the tally is unmoved at **25 declared (VOCAB 14 / SEM 7 / META 4)** — and unlike ASIETY-FREEDOM this invariance **is** a genuine test here, because no `def` is used as a premise: the ◈ caveat of the previous batch has no purchase on any row below.
> **(1) The refutation is of an inference, never of the thesis.** C301 machine-refutes the passage `∀ σ, ∃ e, ¬ In σ e ⟹ ∃ e, ∀ σ, ¬ In σ e` that `CHARACTERISTICS.md:64` itself names as "asserted rather than demonstrated". C302 then exhibits a model in which the **conclusion** is true, so the batch bounds a real claim. A reader must not take C301 as having refuted system-externality itself, and `base.txt` §33 says so in the same breath.
> **(2) The ontological sense is untouched and cited, never re-proved.** C195 (`DivineSimplicity.lean:151`) and C213 (`FoundationalUnicity.lean:200`) already deliver it; C213's proof *is* C195. What was missing was the word **system** — no row spoke of systems, only of non-identity. C307 is the one genuinely new **PROVEN** step: **uniqueness** of the transcendent ground, which neither C195 nor C213 asserted. The characteristic's own statement (`CHARACTERISTICS.md:59`) is therefore **not** softened by this batch; the batch is about its route surviving and its wording being priced.
> **(3) The four senses are separated, deliberately and without an umbrella.** `CHARS.md:144` forbids encoding logical, ontological, hierarchical and causal externality under one name, so there are five predicates and no master structure. A second master was **refused on content grounds**, not on style: `DivinePureActuality.lean:115-117,183-186` already carries the same `hFinite` premise, so it would have added a duplicate assumption and no content. Aseity is excluded for the recorded reason that `TranscendentGround` is a pair of non-identity clauses saying nothing about grounding, and `CanonicalAseity.lean:163` is an explicit countermodel against unconditional aseity.
> **(4) C309–C312 are ledgered, not earned here — and the corpus had been hiding them.** They were written in `NegativeRetorsionAudit.lean` (`:521`, `:530`, `:538`, `:560`) and had **no GAPMAP row at all**; the module is entirely unledgered. They are the two `{}` theorems that carry this batch's `af 38 → 40` movement, and they were machine-checked before anyone put them on the record. The honest description of the GTT situation is therefore *not* "not formalized" (as `CHARACTERISTICS.md:36` had it): the **shape** is formalized and consistent both ways, and the **fixed-point theorem** is absent for want of vocabulary (F14). `:36` and `:65` are corrected to say precisely that.
> **(5) One construction note that cost a build cycle, recorded because it is easy to repeat.** In C301 the negation is closed with `Entity.noConfusion`, **not** `rfl`: `rfl` does not unify across distinct constructors, and the obvious `fun h => h rfl` does not typecheck against `Entity.noConfusion`'s argument order.

---

## Level 21 — Ground-level love as a distinct relation, and the two prices it pays (`Logos.LovesAsGround`, `Logos.CosmicExistence`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C322 | §35 | `LovesAsGround.falsityWorld_ne_actualWorld : (fun _ => TV.f) ≠ actualWorld` — the single witness of modal fragility used by the whole module: the all-`TV.f` valuation is not the actual world, which is all-`TV.t` (`Entity.lean:33`). Cheapest row in the batch, and the only `CL`-only one | PROVEN | `CL` |
| C323 | §35 | `LovesAsGround.an_atom_is_contingent (n : Nat) : ContingentEntity (Entity.ofAtom n)` — an atom is actual at the actual world and refuted at the all-`TV.f` world, because `EntityExistsAt w (ofAtom n) := w n = TV.t` (`Entity.lean:53-56`). This is what makes C338 bite: an atom is *provably* contingent | PROVEN | `{Subject, propext}` |
| C324 | §35 | `LovesAsGround.a_contingent_entity_exists : ∃ t : Entity, ContingentEntity t` — the bare *contingency* half, witnessed by an atom. **Not** the identification of an atom with the cosmos, which the ledger forbids, and **not** an object of love either, since atoms bear no meaning (C335) | PROVEN | `{Subject, propext}` |
| C325 | §35 | `LovesAsGround.a_meaningful_contingent_entity_exists (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Means s p) : ∃ t : Entity, ContingentEntity t ∧ ∃ p, EntityMeans t p` — **a contingent entity bearing content exists.** The hypothesis is load-bearing and honestly stated: `Means` is a primitive `Tag: VOCAB` **axiom** (`Agency.lean:74`) with no derivable instance in Γ, so this theorem *consumes* a `Means` inhabitant rather than producing one. Supplies only the shape the love inhabitation needs; identifies nothing with the cosmos | PROVEN | `{Means, Subject, propext}` |
| C326 | §35 | `LovesAsGround.ground_grounds_every_entity (t : Entity) : GroundsEntity Entity.ofGround t` — the ground of reality grounds every entity whatsoever; the proof is `intro p _; exact True.intro`. **The transfer is vacuous, and that is the point of the next two rows** | PROVEN | `{Means, Subject}` |
| C327 | §35 | `LovesAsGround.atoms_bear_no_meaning (p : Prop) : ¬ EntityMeans (Entity.ofAtom 0) p` — an atom bears no meaning at all: the match arm alone reduces to `False` | PROVEN | `{Means, Subject}` |
| C328 | §35 | `LovesAsGround.ground_grounds_the_meaningless : GroundsEntity Entity.ofGround (Entity.ofAtom 0)` — the ground grounds even an entity that means nothing whatever. The sharpest machine-checked sense of "merely a mathematical ground": the relation is *undiscriminating*, holding uniformly **including where there is nothing to bear** | PROVEN | `{Means, Subject}` |
| — | §35 | `LovesAsGround.the_ground_is_a_universal_modal_ground : UniversalModalGround Entity.ofGround` — **restates C204** (`ofGround_universal_modal_ground`); its body is literally that declaration. Retained and displayed so the contrast with `GroundLoves` can be read off a single pair of definitions, and given **no second C-id** per the corpus rule that two names for one proposition are one proposition | — | `{Means, Subject}` |
| C329 | §35 | `LovesAsGround.no_subject_is_a_necessary_entity (s : Subject) (hKind : ContingentSubjectKind s) : ¬ NecessaryEntity (EntityOf s)` — subjects of the contingent kind exist only at the actual world, so such a subject fails to exist in every other world. **This is why no *contingent* person can occupy the necessary pole** of ground-level love, and it is the row that discharges the "necessary" half without any love axiom. The necessary kind is excluded by hypothesis (2026-09-28, two-kinds) | PROVEN | `{NecessarySubjectKind, Subject, propext}` |
| C330 | §35 | `LovesAsGround.necessary_entities_are_ground_or_necessary_kind : ∀ e : Entity, NecessaryEntity e → e = Entity.ofGround ∨ ∃ s : Subject, NecessarySubjectKind s ∧ e = EntityOf s` — the necessary entities are the ground **and the necessary-kind subjects** (renamed 2026-09-28; was `only_the_ground_is_necessary`). **Read this for what it is:** the ground disjunct is *forced by the three-constructor ontology* — `EntityExistsAt w .ofGround := True` is a definitional stipulation — and the subject disjunct is the priced bridge `Plurality.necessaryPersonalSubjectExists` (`Tag: META`). Its legitimate content is now positive: the "necessary ∧ chosen" cell of `poem.txt:24` is occupied. The "necessary" pole of interpersonal love is discharged here and, conditionally, by T14 / C42–C45 | PROVEN | `{NecessarySubjectKind, Subject, propext}` |
| — | §35 | `LovesAsGround.GroundLoves (g t : Entity) (a : Prop) : Prop := NecessaryEntity g ∧ ActualEntity t ∧ t ≠ g ∧ (∃ p, GroundBearsGood g t p) ∧ (∃ q, EntityMeans t q) ∧ a` — **the relation the module adds**, displayed like `AsietyFreedomOfGround` at §31. Read the six conjuncts, because each is load-bearing: *necessary* lover (C331), *actual other* target (C332), the **directed good** (C333, the one with no first-order substitute), the target's own content (C334), and the context-of-evaluation `a : Prop` mirroring `Good s (_a : Prop)` (`MoralFrontierAudit.lean:203-204`). **Why it is added rather than reused:** `Loves` is `Subject`-indexed (`Love.lean:49`) and the ground is provably not a `Subject` (C344), so "the ground loves" is **not well-formed** in the existing relational vocabulary. The design decision was to keep `GroundLoves` and `Loves` **distinct** rather than merge them, since merging would silently reinterpret `T14` and `PersonStabilityPrinciple` (`Love.lean:101`) | — | `{GroundBearsGood, Means, Subject}` |
| C331 | §35 | `LovesAsGround.ground_love_requires_a_necessary_lover {g t : Entity} {a : Prop} (h : GroundLoves g t a) : NecessaryEntity g` — ground-level love is eternal *in the lover*. This is one half of the formal content of `poem.txt:24`'s "também é necessário"; the other half, that love is *chosen*, is the bridge of C339, **not** this conjunct | PROVEN | `{GroundBearsGood, Means, Subject}` |
| C332 | §35 | `LovesAsGround.ground_love_is_directed_at_another {g t : Entity} {a : Prop} (h : GroundLoves g t a) : ActualEntity t ∧ t ≠ g` — love is not self-regarding: it is directed at an actual target other than the lover | PROVEN | `{GroundBearsGood, Means, Subject}` |
| C333 | §35 | `LovesAsGround.ground_love_bears_a_directional_good {g t : Entity} {a : Prop} (h : GroundLoves g t a) : ∃ p, GroundBearsGood g t p` — ground-level love is content-bearing in the strong sense: the ground holds some directional good *toward* the target. **The conjunct with no first-order substitute, and the one the inhabitation axiom pays for** | PROVEN | `{GroundBearsGood, Means, Subject}` |
| C334 | §35 | `LovesAsGround.ground_love_requires_a_meaningful_target {g t : Entity} {a : Prop} (h : GroundLoves g t a) : ∃ q, EntityMeans t q` — the target must bear content **of its own**. Since `EntityMeans (ofAtom _) = False` and `EntityMeans Entity.ofGround _ = True`, this is exactly what separates love from the ground's undiscriminated meaning-capacity | PROVEN | `{GroundBearsGood, Means, Subject}` |
| C335 | §35 | `LovesAsGround.meaningless_entities_cannot_be_loved : ¬ ∃ a : Prop, GroundLoves Entity.ofGround (Entity.ofAtom 0) a` — **love cannot reach the meaningless**, in any context. The discriminating counterpart of C328: grounding holds at an atom, love does not | PROVEN | `{GroundBearsGood, Means, Subject}` |
| C336 | §35 | `LovesAsGround.grounding_reaches_what_love_cannot : GroundsEntity Entity.ofGround (Entity.ofAtom 0) ∧ ¬ ∃ a : Prop, GroundLoves Entity.ofGround (Entity.ofAtom 0) a` — **the separation, in one statement.** The machine-checked content of "not *merely* a mathematical ground": the two relations differ, and they differ on an entity bearing no meaning | PROVEN | `{GroundBearsGood, Means, Subject}` |
| C337 | §35 | `LovesAsGround.grounding_is_total_but_love_is_not : (∀ t : Entity, GroundsEntity Entity.ofGround t) ∧ ¬ (∀ t : Entity, ContingentEntity t → ∃ a : Prop, GroundLoves Entity.ofGround t a)` — the totals separate: every entity is grounded, and **not** every contingent entity is loved. Read together with C338 this is a pair, not a single step | PROVEN | `{GroundBearsGood, Means, Subject, propext}` |
| C338 | §35 | `LovesAsGround.meaningful_love_bridge_is_refuted : ¬ (∀ t : Entity, ContingentEntity t → ∃ a : Prop, GroundLoves Entity.ofGround t a)` — **the machine-checked reason the bridge carries a meaning hypothesis.** The unrestricted, more attractive form is *false in Γ*: an atom is provably contingent (C323) and provably meaningless (C327), so it would force an atom to bear meaning. This is why the module does not claim the stronger statement, and it is a refutation of a *form*, not of the thesis | PROVEN | `{GroundBearsGood, Means, Subject, propext}` |
| C339 | §35 | `LovesAsGround.AxGroundLovesContingentRealm : ∀ t : Entity, ContingentEntity t → (∃ q, EntityMeans t q) → ∃ a : Prop, GroundLoves Entity.ofGround t a` (`LovesAsGround.lean:449`, `Tag: META`) — **the substance of the batch**: the ground bears a directional good toward every contingent realm that bears content of its own. **Not derivable**, and the `Tag: VOCAB` primitive `GroundBearsGood` (C349) is what makes that true, since a predicate that constrains nothing cannot establish that any bearer holds any good. Nor can the content be read off existing relations: universal grounding is satisfied *vacuously* by the ground for every entity, including meaningless ones (C328), so grounding carries **no directed content** from which love could follow. *Consistency model* (`LovesAsGround.lean:115`): interpret `GroundBearsGood` as `False` everywhere — that satisfies the whole vocabulary, the epistemic reality-hook and every per-constructor theorem of the `Divine*` modules, while every inhabitant theorem of §3 fails. *And it is not a triviality either:* not satisfied by `True`, since the target must be actual, distinct from the lover, and meaningful, and the good directional. *Price, stated:* Γ acquires a directed relation at the ground **not reducible to its stipulated meaning-capacity**; `ofGround_meansAll` (`Stipulations.lean:60-61`) fixes the ground's `EntityMeans` at `True`, and `GroundBearsGood` is a relation over a *pair* with a content argument, so `ofGround_truth_exhaustive` stays consistent precisely because it is not a `Means` judgment. A reader who rejects the price must reject this axiom, **and with it `the_ground_is_a_liver` (C342)** | AXIOM | `{AxGroundLovesContingentRealm, GroundBearsGood, Means, Subject}` |
| C340 | §35 | `LovesAsGround.the_ground_loves_every_meaningful_contingent_reality {t : Entity} (h : ContingentEntity t) (hm : ∃ q, EntityMeans t q) : ∃ a : Prop, GroundLoves Entity.ofGround t a` — the bridge, applied. The first `PROVEN↑` of the batch and the first row in the corpus where the ground's love is a *conclusion* rather than a definition | PROVEN↑ | `{AxGroundLovesContingentRealm, GroundBearsGood, Means, Subject}` |
| C341 | §35 | `LovesAsGround.the_ground_bears_a_directional_good_toward_the_cosmos {t : Entity} (h : ContingentEntity t) (hm : ∃ q, EntityMeans t q) : ∃ p, GroundBearsGood Entity.ofGround t p` — **the content of the claim, unwrapped.** This is the least an inhabitant theorem can say, and it is where the whole price sits: a `{}` reading of "the ground loves" would be a *different and much weaker* claim about meaning-capacity | PROVEN↑ | `{AxGroundLovesContingentRealm, GroundBearsGood, Means, Subject}` |
| C342 | §35 | `LovesAsGround.the_ground_is_a_liver (h : ∃ s : Subject, ContingentSubjectKind s ∧ ∃ p : Prop, Logos.Agency.Means s p) : ∃ t : Entity, ContingentEntity t ∧ (∃ q, EntityMeans t q) ∧ ∃ p, GroundBearsGood Entity.ofGround t p` — **the inhabitants, with the price visible.** The `Means` hypothesis is Γ's primitive content vocabulary being inhabited by a *contingent-kind* subject, which the caller obtains from its own datum (`CosmicExistence.CreatedRealm.bears_meaning` under the kind premise); nothing here identifies that subject with the cosmos | PROVEN↑ | `{AxGroundLovesContingentRealm, GroundBearsGood, Means, NecessarySubjectKind, Subject, propext}` |
| C343 | §35 | `LovesAsGround.the_ground_is_a_necessary_and_chosen_lover (h : ∃ s : Subject, ContingentSubjectKind s ∧ ∃ p : Prop, Logos.Agency.Means s p) : NecessaryEntity Entity.ofGround ∧ ∃ t : Entity, ContingentEntity t ∧ (∃ q, EntityMeans t q) ∧ ∃ p, GroundBearsGood Entity.ofGround t p` — **the "necessary ∧ chosen" cell, occupied**: the machine form of `poem.txt:24`'s "Amar é escolhido e também é necessário", with the necessity in the lover and the choice in the bridge. **This row is the one the reader-facing attribute anchors on, and its footprint names the whole price.** And note the asymmetry, which is the honest content of the row: the *necessary* half is `ofGround_necessary` (`trivial`) and ontology-forced; **the *chosen* half is exactly `AxGroundLovesContingentRealm` and nothing else** — no axiom of free choice is hidden here | PROVEN↑ | `{AxGroundLovesContingentRealm, GroundBearsGood, Means, NecessarySubjectKind, Subject, propext}` |
| C344 | §35 | `LovesAsGround.the_ground_is_not_a_person : ∀ s : Subject, Entity.ofGround ≠ EntityOf s` — the ground-*constructor* is not a subject-correlate (re-scoped 2026-09-28; was read as "the ground is not a personal entity"). So the conclusion attributes love to the ground **as a kind** and smuggles in no hypostatic identification; the open ledger bridge #9 (`Ground(e, personal) → Personal(e)`, C228) is untouched by it. The personal ground of the necessary kind is a *subject* (`Plurality.necessaryPersonalSubjectExists`), hence a different entity from the ground-constructor — Claim E's two conjuncts with no identity line are exactly that shape | PROVEN | `{Subject}` |
| C345 | §35 | `LovesAsGround.ground_love_does_not_identify_a_person : ¬ ∃ s : Subject, Entity.ofGround = EntityOf s` — **the separation, in one statement:** the inhabitation cannot be read as a claim about a person. If someone were to identify the ground with a subject, the identification itself fails, so no route from the ground's love to a created person exists here | PROVEN | `{Subject}` |
| C346 | §35 | `LovesAsGround.subject_love_is_not_ground_love (s t : Subject) (a : Prop) (hKind : ContingentSubjectKind s) (_h : Loves s t) : ¬ GroundLoves (EntityOf s) (EntityOf t) a` — **contingent interpersonal love never yields ground-level love.** `GroundLoves` demands a *necessary* lover and no contingent-kind subject is necessary (C329), so the two relations are provably disjoint on the contingent side. The `_h : Loves s t` hypothesis is deliberately unused: the separation is **stronger** than its motive | PROVEN | `{GroundBearsGood, Means, NecessarySubjectKind, Subject, propext}` |
| C347 | §35 | `LovesAsGround.interpersonal_love_never_reaches_the_necessary_quadrant : ¬ ∃ s t : Subject, ContingentSubjectKind s ∧ Loves s t ∧ NecessaryEntity (EntityOf s)` — the failure holds for *every contingent-kind* subject and *every* love relation, so no amount of contingent interpersonal love can populate the necessary quadrant. The necessary kind can — that is the reversal this batch records. This is the negative half of the transfer the original module design asked for, now correctly scoped | PROVEN | `{NecessarySubjectKind, Subject, propext}` |
| C348 | §35 | `LovesAsGround.ground_love_cannot_be_read_as_person_love : ¬ (∃ s : Subject, Entity.ofGround = EntityOf s) ∧ ∀ s t : Subject, ContingentSubjectKind s → Loves s t → ¬ GroundLoves (EntityOf s) (EntityOf t) True` — **the transfer to contingent interpersonal love is unstatable, not merely blocked.** The design originally asked for `GroundLoves → Loves` on the subject side; there is no such statement for the contingent kind, because `Loves` is `Subject`-indexed, the ground is provably no subject-correlate, and the target of a `GroundLoves` claim is an arbitrary `Entity` rather than a `Subject`. The only route would be a hypostatic identification, which C344/C345 refute for the contingent kind | PROVEN | `{GroundBearsGood, Means, NecessarySubjectKind, Subject, propext}` |
| — | §35 | `LovesAsGround.ground_love_preserves_pure_actuality {t : Entity} {a : Prop} (_h : GroundLoves Entity.ofGround t a) : ¬ PassiveTransitionPotency Entity.ofGround` — **restates C217** (`ofGround_no_transition_potency`); its body is literally that declaration. The substantive content is the compatibility note in the module header and not a separate proposition: attributing an *act* of love to the ground **adds to** `ofGround_divine_pure_actuality` rather than contradicting it, since pure actuality excludes passive potency, not act (Aquinas, *ST* I q.20 a.3). No second C-id, per the corpus rule | — | `{GroundBearsGood, Initiates, Means, State, Subject}` |
| C349 | §35 | `LovesAsGround.GroundBearsGood : Entity → Entity → Prop → Prop` (`LovesAsGround.lean:284`, `Tag: VOCAB`) — **the price of vocabulary**: a necessary bearer holds a directional good toward a target, with content `p`. *Why a primitive and not a fair definition:* the library's grounding vocabulary expresses only undirected sufficiency (`GroundsEntity g e := ∀ p, EntityMeans e p → EntityMeans g p`), which the ground satisfies **vacuously** (C328); the one content predicate available, `EntityMeans`, is a *capacity of the target*, not an *attitude of the bearer*, so it cannot distinguish a bearer that loves from one that merely contains; and `Good s (_a : Prop)` (`MoralFrontierAudit.lean:203-204`) is the right shape but is `Subject`-indexed, while the ground is provably not a `Subject` (C344). *Any* first-order definition over `NecessaryEntity`/`ActualEntity`/`EntityMeans` is a function of the target's own properties and collapses to a provable conjunction — the concrete instance of that collapse this module **previously shipped by mistake** is corrected in the module header. *Consistency model:* the predicate constrains nothing, so it is satisfiable by any interpretation including constant-`False`, under which every inhabitant theorem fails. **Rejecting it means rejecting the relation's content, not the theory** | AXIOM | `{GroundBearsGood, Subject}` |
| C350 | §35 | `CosmicExistence.contingent_realm_obtains : ContingentRealmObtains` (`CosmicExistence.lean:~220`) — **contingency-overflow, at no substantive price**: something obtains, is modal-fragile, and is not the necessary ground, and Γ derives it outright. **PROMOTED FROM `PROVEN↑` TO `PROVEN` 2026-09-27** — the status *drops*, and that is an improvement: Batch 1 had left existence priced on `AxTwoSubjects` (`Tag: META`), which the user rejected — *"Cosmos existence MUST be axiom free. Otherwise the proof itself wouldn't exist."* *Why the price was never intrinsic:* it came from **one field** of the `Realm` record, `bears_meaning`. `EntityMeans` is `False` on `ofAtom` and `True` on `ofGround` (`RecoveredOntologicalGround.lean:48-50`), and `not_the_ground` excludes the latter, so `bears_meaning` **forces the witness to be a `Subject`** — and `Subject` is an opaque sort (`Agency.lean:43-49`). An `∃ s : Subject, p` is therefore unprovable without an axiom mentioning `Subject`. **Existence never needed that field.** `ContingentRealm` is `Realm` minus `bears_meaning`: a `structure` change, so it adds **no axiom** and the registry does not move. *The witness:* `LovesAsGround.an_atom_is_contingent 0` (`LovesAsGround.lean:171`), reused verbatim — the construction C324 already uses, so the footprint is `{propext, Subject}`. *Not vacuous:* `EntityExistsAt w (ofAtom n) := w n = TV.t` (`Entity.lean:53-56`) discriminates on the index, so `actualWorld 0 = TV.t` while `fun _ => TV.f` falsifies it — a real contingency claim, not an artifact of a coarse world sort. *On the word "created":* it labels the **region** of reality the record describes, and does **not** assert production. No `Creates` relation, no agent, no first moment appears here or is derivable from it. **Do not read this row as saying something made the realm** — that is lane L3, unclaimed, and C110 still refutes that grounding entails a creation record. *Nor as saying this is our cosmos:* C324's prohibition stands, an atom is **not** the cosmos. What is proved is that the *shape* has an instance; the **identification** is C367. Not a duplicate claim id: C324 remains `PROVEN` with its caveat unchanged, and C350 carries the explicit `not_the_ground` conjunct C324 lacks. The existence half of F9 leaves the faith zone for the second time and now for a stronger reason; **purpose and the incarnation do not** | PROVEN | `{propext, Subject}` |
| C351 | §35 | `CosmicExistence.the_ground_loves_the_cosmos (h : ∃ s : Subject, ContingentSubjectKind s ∧ Logos.Person.Person s) : ∃ t : Entity, ContingentEntity t ∧ (∃ q, EntityMeans t q) ∧ ∃ p, GroundBearsGood Entity.ofGround t p` — **the conclusion, with both prices visible.** The realm's contingency and content plus the declared bridge yield a directional good the ground holds toward the cosmos: "He is not merely a mathematical ground, but loves". The footprint names the **whole** price — the exhibited contingent person, the metaphysical bridge, the content vocabulary and the world structure. The claim is about the ground **as a kind**; no hypostatic identification is made (C344) | PROVEN↑ | `{AxGroundLovesContingentRealm, GroundBearsGood, Means, NecessarySubjectKind, Subject, Will, propext, subjectWill}` |
| C352 | §35 | `CosmicExistence.the_ground_loves_the_cosmos_in_a_context (h : ∃ s : Subject, ContingentSubjectKind s ∧ Logos.Person.Person s) : ∃ t : Entity, ContingentEntity t ∧ ∃ a : Prop, GroundLoves Entity.ofGround t a` — the same conclusion in the library's *relational* vocabulary: there is a context in which the ground's love of the realm holds. Note this is the relation `GroundLoves`, **not** interpersonal `Loves` — the two are provably disjoint on the contingent side (C346) and the transfer is unstatable rather than merely unproved (C348) | PROVEN↑ | `{AxGroundLovesContingentRealm, GroundBearsGood, Means, NecessarySubjectKind, Subject, Will, propext, subjectWill}` |
| C367 | §35 | `CosmicExistence.cosmos_obtains (h : ∃ s : Subject, ContingentSubjectKind s ∧ Logos.Person.Person s) : CreatedRealm` (`CosmicExistence.lean:410`) — **and it bears content of its own.** The meaning-bearing half, split off from C350 on 2026-09-27: a contingent created realm, not the necessary ground, obtains **and** bears content, and the witness is a `Subject`. *This is the row that identifies the derived realm as the cosmos.* *Price, now correctly attributed:* **existence is not what this row pays for** — C350 has it at `{propext, Subject}`. What costs here is the `bears_meaning` conjunct, and only that, given an exhibited *contingent person* (2026-09-28, two-kinds: a contingent realm needs a contingent witness, and the witness\u2019s contingency is its kind — under kind-blind semantics the T12 witness\u2019s contingency was free, now it is exhibited). `AxTwoSubjects` no longer appears: it supplied personhood and meaning, but exhibiting the kind subsumes the witness. **Reject the contingent-person datum and the realm\u2019s *meaning-bearing inhabitation* goes; its existence (C350) does not.** Both shortcuts that would have made this row free were considered and **rejected**: rescoping the love claims onto an atom, and relaxing `EntityMeans` so atoms bear content — which would also have destroyed C335 `meaningless_entities_cannot_be_loved` and C338. *Inherited from the retired row:* C324's "an atom is **not** the cosmos" limit, restated here because this is where the identification lives, and the C353 non-triviality note (`perfect_universe_has_no_contingent_realm` refutes the `Realm` shape in a world-rigid universe). *Unchanged by the split:* the deleted `AxContingentCreationObtains` was `AXIOM` (`Tag: SEM`) and its retirement (registry 25 → 24, SEM 7 → 6) stands, as does the finding that its stated reason — that `∃ s : Subject, ∃ p : Prop, Means s p` had no producer — was **false**, `Plurality.cogito_from_T12` being that producer *unconditionally* from the axiom-free `Logos.Core.rightWrongDistinction`. **Not claimed:** that the negation is consistent with all of Γ (model-theoretic over the whole theory, not built), nor that anything made the realm. **The price is not forced (2026-09-27, GOD-LANE):** `AxTwoSubjects` is one route to a meaning-bearing realm, not the only one. C386 inhabits `CreatedRealm` from the performative act-datum ◈ `performativeActDatum` (`Tag: TRANS`, registry 6 → 7) with no bridge, and C387 carries the same substitution all the way to the ground's love. **This row is untouched and still pays the bridge** — the substitution is a *companion*, not a re-anchoring, and the reason is the A1 bug: anchoring subject-existence on plurality made it a consequence of the datum it must precede. A theorem discovers; it does not manufacture. **Existence is not entailment** — C110 stands | PROVEN | `{Means, NecessarySubjectKind, Subject, Will, propext, subjectWill}` |
| — | §35 | `CosmicExistence.ContingentRealm : Type` — **the realm without the meaning condition**: `witness`, `actual`, `contingent`, `not_the_ground`. It is `Realm` minus `bears_meaning`, and dropping that one field is what frees existence from `AxTwoSubjects`. A `structure` change, so **no axiom is added**. Displayed like `AsietyFreedomOfGround`; the claim that inhabits it is `contingent_realm_obtains` |
| — | §35 | `CosmicExistence.ContingentRealmObtains : Prop := Nonempty ContingentRealm` — the `Prop` form, so the ledger can name the inhabitation as a claim while the record keeps a single witness (the same device as `CreatedRealm`) |
| — | §35 | `CosmicExistence.CreatedRealm : Prop := Nonempty Realm` — the **meaning-bearing** realm's structure, displayed like `AsietyFreedomOfGround` at §31: a `Type`-valued, displayed like `AsietyFreedomOfGround` at §31: a `Type`-valued record, because a `Prop`-valued structure may not carry a data field, so the single witness is only expressible this way. **Corrected 2026-09-27:** this row previously read `CreatedRealm (R : Type) : Prop := Nonempty Realm`, inventing a parameter; the audited `def` (`CosmicExistence.lean:137`) is a closed `Prop` and `R` is the *structure* name being inhabited, not a binder. The `Type`-valued thing is `structure Realm : Type` (`:119`), displayed by the same row's prose. `Realm` carries `witness`, `actual`, `contingent`, `not_the_ground` and `bears_meaning` — every field a predicate over the *existing* vocabulary about **one** entity, so the record really does describe a single realm | — | `{Means, Subject}` |
| C353 | §35 | `CosmicExistence.perfect_universe_has_no_contingent_realm (U : PerfectUniverse) : ¬ (∃ t : U.Entity, U.ExistsAt U.actualWorld t ∧ ∃ w : U.World, ¬ U.ExistsAt w t)` — **the one `{}` row of the batch, and a real countermodel rather than a non-triviality note.** In a world-rigid universe every actual entity is necessary, so nothing witnesses the shape of `CreatedRealm.contingent`. *Scope limit, stated because it is easy to overread:* `PerfectUniverse` is an **unrelated free structure, not a model of Γ** (`CosmicExistence.lean:206-210`). What it shows is that the *shape* of the datum's contingency field is not forced by world-rigidity in general; it says nothing about Γ's worlds, on which the datum simply holds. Its positive companion `perfect_universe_actual_is_necessary` (`:222`, also `{}`) is the lemma it consumes and is itself ledgered here as the step inside C353 | PROVEN | `{}` |
| C354 | §35 | `CosmicExistence.cosmos_presence_model (h : ∃ s : Subject, ContingentSubjectKind s ∧ ∃ p : Prop, Logos.Agency.Means s p) : CreatedRealm` — **conditional satisfiability of the datum:** the realm does obtain, for any inhabitant of `Means` of the contingent kind, witnessed by such a subject (actual at the actual world by the kind disjunct\u2019s failure and the world equation, refuted at the all-`TV.f` world, distinct from the ground by `Entity.noConfusion`, bearing content because `EntityMeans (Entity.ofSubject s) p` unfolds to `Means s p`). The `Means` hypothesis is not a technicality and is not hidden: satisfiability *relative to* Γ's intentional vocabulary being inhabited, and stated that way rather than claimed outright. **This is not the identification of a subject with the cosmos** — the datum is declared, not read off a modelling artifact; the model witnesses only that the structure is satisfiable. Paired with C353 it is what lets C350 be declared rather than merely assumed | PROVEN | `{Means, NecessarySubjectKind, Subject, propext}` |

> Batch COSMOS-IS-PROVEN (2026-09-27): this batch **removes an axiom** — the registry moves
> **25 → 24**, `Tag: SEM` **7 → 6** — and it is the first batch in this corpus to *retire* a
> declared datum rather than add or ledger one.
> **(1) The finding is that the corpus asserted a false claim about its own closure.** C350 was
> declared `AXIOM` on the stated ground that the lemma `∃ s : Subject, ∃ p : Prop, Means s p` had
> **no producer in Γ**. It has one: `Plurality.cogito_from_T12` proves exactly that, with **no
> hypothesis**, from `T12_twoPersons` (= `AxTwoSubjects rightWrongDistinction`) and
> `person_is_intentional`, and `Logos.Core.rightWrongDistinction` is axiom-free. So the datum was
> **redundant** — it re-charged for a commitment Γ had already made.
> **(2) The same false claim was transcribed into four places**, all now corrected: this row, the
> `CosmicExistence.lean` module header and axiom docstring, `base.txt` §35(4), and
> `theorems/T30.txt`(4) — the last of which stated the lemma was "o **único** obstáculo". The
> precise truth is narrower and was missed: `Subject` and `Means` have no producer *individually*,
> but the **existential** does, via plurality.
> **(3) The recorded objection to deriving it was aimed at a different route.** The deleted docstring
> held that any deductive route "would equally force the judging subject's own claims to be
> necessary" (`poem.txt:26`). That objection is sound against the *reality-hook* route
> `(∃ s, Correct s p) → p`, which is unconditional in `p`. The plurality route never touches
> `Correct`: `Realm.bears_meaning` is meaning-**capacity**, and `Realm.contingent` *asserts*
> modal-fragility. The reductio does not apply, so it could not sustain the axiom.
> **(4) The price moved, it did not vanish.** Existence now rests on `AxTwoSubjects` (`Tag: META`) —
> "the reality of right-and-wrong demands at least two distinct persons". An ontological claim now
> leans on an axiological bridge. That is a **relocation** of the cost, and a tighter one: the
> position is now *falsifiable* (reject plurality ⇒ lose the cosmos). The row names the price.
> **(5) Two statements are now machine-checked that were previously prose claims.** C350
> `cosmos_obtains : CreatedRealm`, and its companion `gamma_exhibits_a_meaning_subject`, which
> isolates the "Γ cannot come about in an empty world" fact as a standalone theorem with the
> subject *produced inside Γ* rather than assumed.
> **(6) Renamed, to stop the deleted language leaking back in:** `the_cosmos_datum_is_not_refutable`
> → `the_cosmos_existence_is_not_refutable`. Its statement is unchanged; the word "datum" referred
> to an axiom that no longer exists, and the old name would have reappeared in the generated
> `README.md` and `kernel-audit.md`.
> **(7) What this batch does not touch.** C110's separation is untouched, and the two facts are
> independent and both hold: Γ **proves** a contingent realm exists, and Γ **refutes** that a
> necessary ground alone entails a creation record. Existence is not entailment. The
> whole-theory consistency-of-negation model is still unbuilt, and the residual debt is now
> "existence is conditional on plurality" rather than "existence is undeclared".

> Batch LOVESASGROUND-CATCHUP (2026-09-27): this batch **declares nothing** — the registry is unmoved at **25 (VOCAB 14 / SEM 7 / META 4)**, and the three `AXIOM` rows below (C339, C349, C350) are *ledgering* three axioms that already existed and were **invisible to every reader-facing artifact**. What the batch buys is criterion 5 of §0 of `IMPROVE.md`: no machine-verified theorem is invisible to the ledger. **28 of the 31 `LovesAsGround` declarations had no claim row at all**, and the whole `CosmicExistence` module was unledgered — so `the_ground_loves_the_cosmos`, a checked theorem, was not in `GAPMAP.md`, `base.txt`, `README.md`, `CHARACTERISTICS.md` or any `theorems/*.txt`, and the META bridge paying for it was unpriced.
> **(1) Row order is by C-id, not by declaration order, and the reason is deliberate.** The three declared axioms are gathered as C339 (META, the substance), C349 (VOCAB, the primitive) and C350 (SEM, the datum), so that the batch's three prices read as a set. The Lean declaration order is: C322–C330 → **C349** (`GroundBearsGood`, §2, `:284`) → `—` `GroundLoves` (`:300`) → C331–C338 → **C339** (`:410`) → C340–C343 → C344–C348 → **C350** (`CosmicExistence.lean:170`) → `—` `CreatedRealm` (`:137`) → C351–C354.
> **(2) Two of the 28 get `—` rows, not C-ids, and this is the corpus rule rather than a gap.** `the_ground_is_a_universal_modal_ground` and `ground_love_preserves_pure_actuality` are *literal restatements* of C204 and C217 — their bodies **are** `ofGround_universal_modal_ground` and `ofGround_no_transition_potency`. Giving them ids would record one proposition twice, which `theorems/T29.txt` already forbids (*"dois nomes para a mesma proposicao seriam uma proposicao com dois C-id"*). Both are still displayed, with their footprints, so nothing is hidden.
> **(3) The batch is mostly negative, and that is the finding.** Of 33 new claims, **24 are `PROVEN` on declared vocabulary alone, 6 rest on a declared bridge (`PROVEN↑`), and 3 are the `AXIOM` rows themselves (C339, C349, C350)**; not one new axiom was added to make a proposition true. **Corrected 2026-09-27:** this note previously read "27 are `PROVEN` … and 6 rest on a declared bridge", which is the sum 24 + 3 — the three `AXIOM` rows were being counted as `PROVEN`. `scripts/gapmap_taxonomy.py` counts only `PROVEN`/`PROVEN↑` rows, so it never caught this. In particular: C336 machine-checks that "not *merely* a mathematical ground" is a **separation of two relations** rather than a slogan (grounding holds at an atom, love provably does not); C338 machine-checks that the *unrestricted* bridge is **false**, which is why the axiom carries a meaning hypothesis — the module declines the more attractive form; C346/C348 record the `Loves` transfer as **unstatable, not merely blocked**; and C344/C345 keep bridge #9 (C228) untouched.
> **(4) C330 must not be sold as evidence of love, and the ledger says so on the row.** `necessary_entities_are_ground_or_necessary_kind` (renamed 2026-09-28; was `only_the_ground_is_necessary`) — the ground disjunct is *forced by the three-constructor ontology* — `EntityExistsAt w .ofGround := True` is a definitional stipulation. Its footprint (`{NecessarySubjectKind, Subject, propext}`, world structure and constructor analysis) confirms there is no love content in it. Likewise C343's "necessary" half is `ofGround_necessary` and **the "chosen" half is exactly `AxGroundLovesContingentRealm` and nothing else** — no axiom of free choice is hidden, and the poem's cell is occupied by a bridge, not by a theorem. **Corrected 2026-09-28:** this note previously read "the ground is the unique necessary entity" and "the necessary ∧ chosen cell contains no person". The necessary-kind disjunct (C404, `Tag: META`) occupies the cell; what remains negative is the *contingent* person's exclusion from it.
> **(5) C353 is the batch's only `{}` row, and it is a genuine countermodel, per §0 criterion 2 of `IMPROVE.md` ("the fastest way to make this proof stronger is to refute more").** It refutes the *shape* of the SEM datum in a world-rigid universe — with the scope limit that `PerfectUniverse` is an unrelated free structure, not a model of Γ. Paired with C354 (conditional satisfiability), this is what makes C350's declared status honest rather than lazy: neither forced nor vacuous. Its companion `perfect_universe_actual_is_necessary` (`{}`, `:222`) is consumed inside C353 and is not given a separate id.
> **(6) The transfer bridge #9 is unchanged and is NOT re-priced here.** `Loves` is `Subject`-indexed (`Love.lean:49`) and the ground-constructor is provably no subject-correlate (C344), so "the ground loves" is **not well-formed** in the existing relational vocabulary — which is why this module *adds* a relation instead of reusing one, and why the design decision was to keep `GroundLoves` and `Loves` **distinct** rather than merge them (merging would silently reinterpret `T14` and `PersonStabilityPrinciple`, `Love.lean:101`). No hypostatic identification is assumed anywhere in the batch, so **C228 stays exactly as it was** and F3 is untouched. **Corrected 2026-09-28:** "the ground is provably no `Subject`" now reads "no subject-*correlate*": the personal ground of the necessary kind *is* a subject (C404), hence a different entity from the ground-constructor; C344 rules out identifying the two, not the existence of the necessary-kind person.
> **(7) What is still missing, named.** (a) A `GroundLoves → Loves` transfer is **unstatable** without hypostatic identification (C348), which is bridge #9 / C228, still `BLOCKED`. (b) A *directed* grounding relation at the `Entity` layer, so the price of C349 is not simply "new vocabulary" — that is F12's missing relation, and C299 (`{}`) shows why no relation of `GroundsEntity`'s containment shape can deliver it. (c) The remaining **10** unledgered `CosmicExistence` theorems, of 16 top-level declarations audited (6 are in: C350–C354 plus `CreatedRealm` on a display row). **Corrected 2026-09-27:** this item previously read "12 unledgered … (of 14 found; C353/C354 are in)", which double-counted — C351 and C352 are also among those 14 theorems and are also in. The 10 are `a_created_realm_obtains`, `a_contingent_reality_obtains`, `contingent_reality_is_not_necessary`, `perfect_universe_actual_is_necessary` (the `{}` lemma C353 consumes), `reality_is_not_exhausted_by_the_ground`, `realm_existence_does_not_imply_realm_necessity`, `the_cosmos_datum_is_not_refutable`, `the_ground_is_necessary_and_the_realm_is_contingent`, `the_ground_is_not_personal`, `the_realm_bears_meaning`. Listed in `IMPROVE.md` §1b.

## Level 22 — The empty-world suite, ledgered and scoped (`Logos.TheologicalModalHardening`)

**Why this level exists (2026-09-27).** `TheologicalModalHardening.lean` held ~26 machine-checked declarations about empty worlds, necessary entities and the four creation regimes (G1–G4), and **not one of them appeared in this ledger, in `base.txt`, in any `theorems/*.txt`, or in the generated `README.md`.** They were reachable only through `investigations/kernel-audit.md`. The user's objection — that the project proposes a world in which contingent reality does not exist — is aimed at that gap: the declarations were invisible *and* one of them (`g1_god_alone_properties`) does assert, in its own model's modality, that no contingent entity exists. Being invisible is not a defence, so they are ledgered here with the scope limit stated on every row.

**The scope limit, stated once and applying to every `COUNTERMODEL` row below.** Each of these is a statement about a **purpose-built free structure** — `CreationSignature`, `ModelG_Signature`, `DeepCreationSignature`, `RegimeG_Signature`, `ModalOntologySignature`, `ModalWorldModel` — and **none of them is a model of Γ, and none of them is a candidate for reality.** They answer one narrow question: *does the necessary-ground premise entail a creation relation?* They say nothing about whether the contingent world exists. That is `CosmicExistence.AxContingentCreationObtains` (C350), a declared `Tag: SEM` datum, and the same separation the C110 row now carries after its rebuild on a populated world.

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C355 | §28, §35 | `TheologicalModalHardening.necessary_entity_rules_out_empty_world (Entity World) (ExistsAt) (hNec : ∃ g, ∀ w, ExistsAt w g) : ¬ (∃ w, ∀ e, ¬ ExistsAt w e)` — **the row that answers the empty world directly, and it answers it by refutation.** Once a necessary entity exists, no world can be absolutely empty, because that entity exists in every world. Scope: about a free `ExistsAt`, not about Γ's worlds | PROVEN | `{}` |
| C356 | §28 | `TheologicalModalHardening.empty_world_excluded_by_non_emptiness_constraint (World) (M : ModalWorldModel World) (w_empty) (hConstraint : ∀ w, M.ModalConstraints w → False) : ¬ M.PossibleWorld w_empty` — the second, weaker route to the same verdict: stipulating non-emptiness as a necessary modal constraint formally excludes the empty world. **Honest reading:** this is an *exclusion by stipulation*, not a derivation, and the row says so rather than selling the stipulation as a proof | PROVEN | `{}` |
| C357 | §28 | `TheologicalModalHardening.non_contingent_not_entails_necessary : ¬ (∀ S : ModalOntologySignature, ∀ e, ¬ S.ContingentEntity e → S.NecessaryEntity e)` — an entity existing in *no* world is neither contingent nor necessary, so non-contingency does not entail necessity. Countermodel: `ExistsAt := fun _ _ => False` | COUNTERMODEL | `{}` |
| C358 | §28, §35 | `TheologicalModalHardening.necessary_entity_not_forces_contingent_creation : ∃ S : ModelG_Signature, ∃ w : S.World, S.ExistsAt w S.g ∧ (∀ x, S.ExistsAt w x → ¬ S.ContingentEntity x)` — a necessary entity does **not** force contingent creation. **Read the quantifier carefully, because it is the difference between this row and the empty world:** the claim is *per world* — there is a world at which no contingent entity exists — and `ConcreteModelG` is **not** an empty world (`Entity := Option Unit`; `some ()` is contingent at the actual world `true` and absent at `false`). The no-creation world is a *second* world, not the absence of a world | COUNTERMODEL | `{}` |
| C359 | §28 | `TheologicalModalHardening.model_G_consistent : ∃ _M : ModelG_Signature, True` — the model witness consumed by C358; displayed, not separately claimed | — | `{}` |
| C360 | §28, §35 | `TheologicalModalHardening.god_alone_has_no_creation : ¬ ∃ x : GodAloneModel.Entity, GodAloneModel.Creates GodAloneModel.g x` — **this row denies only the `Creates` relation, not the existence of contingent entities.** Scope: `GodAloneModel` has `World := Unit`, so it is a single-world, world-rigid structure — the `PerfectUniverse` shape of C353 — and nothing in it is contingent for that reason alone. It is a countermodel of *coexistence ⇒ creation*, not a proposal that there is nothing there | COUNTERMODEL | `{}` |
| C361 | §28, §35 | `TheologicalModalHardening.coexistence_without_creation_relation : (∃ x, CoexistenceWithoutCreationModel.ContingentEntity x) ∧ (¬ ∃ x, Creates g x)` — **the populated counterpart of C360, and the pair that keeps it honest.** A contingent entity `false` exists at the actual world; the creation relation is empty. Existence and derivation come apart in a world that is *not* empty | PROVEN | `{}` |
| C362 | §28 | `TheologicalModalHardening.necessary_non_emptiness_not_entails_necessary_entity : ¬ (∀ S : RegimeG_Signature, ∃ e, S.NecessaryEntity e)` — every world may hold an entity without any one entity holding in every world (`ShiftingEntityModel`, `ExistsAt := fun w e => w = e`). Relevant here because `RegimeG_Signature` carries `necessary_non_emptiness : ∀ w, ∃ e, ExistsAt w e`, the field whose *absence* is what makes the empty world admissible in `RegimeE_Signature` | COUNTERMODEL | `{}` |
| C363 | §28, §35 | `TheologicalModalHardening.g1_god_alone_properties : (¬ ∃ x : RegimeG1_GodAlone.Entity, RegimeG1_GodAlone.ContingentEntity x) ∧ (¬ ∃ x, Creates g x)` — **the row a reader is most entitled to call ridiculous, so the scope limit is on the row rather than in a Lean docstring.** `RegimeG1_GodAlone` is `World := Unit, ExistsAt := fun _ _ => True`: a single world, world-rigid, so `ContingentEntity e := ExistsAt actualWorld e ∧ ∃ w, ¬ ExistsAt w e` reduces to `True ∧ ∃ w, ¬ True` and nothing is contingent. It is a world-rigid countermodel of *necessity ⇒ contingency*, exactly the shape of C353 — **not** a claim about reality, and **not** a model of Γ. Its first conjunct is a fact about a one-world structure | COUNTERMODEL | `{}` |
| C364 | §28 | `TheologicalModalHardening.g2_creation_properties : (∃ x, RegimeG2_Creation.ContingentEntity x) ∧ RegimeG2_Creation.Creates g false` — the **positive** regime: a necessary ground and a contingent creature, with the creation relation holding. Ledgered so C363 cannot be read as "creation is impossible": the G1–G4 atlas is a set of *undetermined* regimes, and the entailment question is open in both directions | PROVEN | `{}` |
| C365 | §28, §35 | `TheologicalModalHardening.g3_coexistence_no_creation_properties : (∃ x, RegimeG3_CoexistenceNoCreation.ContingentEntity x) ∧ (¬ ∃ x, Creates g x)` — contingent entity present, creation relation empty, in a **two-world** structure. This is the same conclusion as the rebuilt C110, reached in the `DeepCreationSignature` idiom, and it is a populated world: the countermodel of *coexistence ⇒ creation* needs no empty sort | PROVEN | `{}` |
| C366 | §28 | `TheologicalModalHardening.g4_creation_is_contingent : ∃ w : RegimeG2_Creation.World, ¬ RegimeG2_Creation.ExistsAt w false` — where creation does hold, it is modal-fragile: the creature is absent at the counterfactual world. The `poem.txt:26` half of the creation question (`este mundo é necessário? Não`) in machine-checkable form | PROVEN | `{}` |
| — | §28 | `TheologicalModalHardening.RegimeE_Signature` — the **open-world** signature, whose field `has_empty_world : ∃ w, ∀ e, ¬ ExistsAt w e` *permits* an empty world; and `RegimeG_Signature`, whose field `necessary_non_emptiness : ∀ w, ∃ e, ExistsAt w e` excludes one. The pair is the formal shape of the "empty world model" as a *regime one may choose*, and it is what C355/C356/C362 operate on. Displayed with footprints; no C-id, since a signature is vocabulary rather than a proposition | — | `{}` |
| — | §28 | The model witnesses consumed by the rows above, each `{}` and displayed rather than claimed: `ConcreteModelG` (C359), `GodAloneModel` (C360), `CoexistenceWithoutCreationModel` (C361), `ShiftingEntityModel` (C362), `RegimeG1_GodAlone` (C363), `RegimeG2_Creation` (C364), `RegimeG3_CoexistenceNoCreation` (C365), plus the signatures `ModalOntologySignature`, `CreationSignature`, `DeepCreationSignature`, `ModalWorldModel` | — | `{}` |

> **Notes on this level.**
> **(1) Nothing here is new.** No declaration was added, renamed or altered by this level; it is a ledgering pass over 26 pre-existing `{}` declarations. The axiom registry is unmoved and no `AXIOM` row is introduced.
> **(2) C361 and C365 are the rows that keep C360 and C363 honest, and they are why the negative rows are safe to quote.** The substantive content of C361 is the *pair* it forms with C360: one structure where the `Creates` relation is empty and another where a contingent entity exists alongside it. C365 is the same separation in a two-world structure, and it shows the separation does not require an empty world. Both are `PROVEN`: a positive existence conjunct conjoined with a negated relation is a proved statement, and the *edge* they settle (`God ⇏ creation`, `edge_DivineGround_to_Creation`) is what carries the `COUNTERMODEL` status — visible on C110, not re-stated here.
> **(3) The one row that could be quoted against the project is C363, and its limit is on the row.** `g1_god_alone_properties` asserts `¬ ∃ x, ContingentEntity x` in a world that has one world. A reader who takes it as a claim about reality is reading a one-element type as a cosmology. C355 is the machine-checked statement that such a world is inadmissible once a necessary entity exists, and C356 the stipulation that excludes it; the rebuilt C110 now machine-checks on a **populated** world for the same verdict.
> **(4) Still unledgered in this module.** The uniqueness and ultimate-grounding candidates (Part 7 onward), the retorsion model (`ContingentSubjectRetorsionModel`, `retorsion_not_forces_necessary_subject`, `:540`/`:555`), the divine-specification separations (`:599`/`:616`) and the `FrameE1`/`FrameE2`/`FrameE3` block (`:504`–`:539`) remain outside the ledger, as does `plural_necessary_entities_consistent` (`:391`, referenced once at an earlier level for a different module). They are out of the empty-world question and are not claimed here.

---

## Dívida herdada de `def`-as-bridge — censo de 2026-09-28 (VISIBILITY.md Fase 7)

**O que isto é.** `scripts/audit_stipulated_defs.py` já impõe o *piso*: nenhuma ponte
nova não declarada, e o conjunto herdado não cresceu. O que ele não faz é **censusar**
esse conjunto. Esta secção é o censo, e cada linha é uma **`def` usada como premissa
por nome próprio** — o padrão de ponte que `#print axioms` não vê, porque uma `def`
não é um axioma e não entra na pegada. São 28 pontes herdadas, `reviewed: false` todas,
das quais **53 teoremas** dependem sem que o kernel os cobre.

**Divulgação não é pagamento.** Duas colunas que convém não confundir, porque o census
mantém as três precisamente para que ninguém confunda:

| | hoje | significa |
|---|---|---|
| `disclosed` | **28** de 28 | o preço está **escrito** neste ledger, e o leitor encontra-o |
| `reviewed` | **0** | o ponteiro do allowlist foi conferido contra o ledger — nenhum foi |
| `paid` | **0** | promovido a `axiom` declarado (só `SemanticFinitude`, F15/C388) ou registado `◈` |

Ou seja: **esta secção torna a dívida visível; não paga uma única dela.** As 28
continuam `def`, continuam invisíveis a `#print axioms`, e continuam contadas como
dívida herdada em `scripts/stipulated_def_allowlist.json`. Se algum dia a coluna
`paid` deixar de ser 0, essa linha passa a ser um axiome declarado e o preço entra na
pegada.

**A decisão de três vias, por entrada, continua a ser do autor** — exactamente como
F15 a resolveu: promover a `axiom` com `Tag:` e justificação (preço visível, teoremas
incondicionais), registar como `◈` (preço invisível mas declarado), ou aceitar como
dívida e dizê-lo aqui. O que é inaceceptável é o estado anterior a esta secção: uma
ponte não declarada com sete teoremos dependentes. `scripts/census_stipulated_defs.py --check`
verifica agora, e falha se, estes números deixarem de bater, ou se o campo `gapmap`
de uma entrada deixar de coincidir com o que o ledger realmente contém.

| figures | | |
|---|---|---|
| inherited bridges (allowlist, `reviewed: false`) | `total` | **28** |
| named in this section (disclosed, *not* paid) | `disclosed` | **28** |
| theorems resting on a bridge the kernel cannot see | `theorems` | **53** |

| `def` | módulo | dependentes | teoremas |
|---|---|---|---|
| `act_polarity_principle` | `Logos.Choice` | 7 | `act_polarity_implies_conditional`, `act_polarity_implies_contrastive`, `act_polarity_implies_existential`, `act_polarity_implies_existential_choice`, `act_polarity_implies_intentional_choice`, `deliberateResource_of_act_polarity`, `genuineChoice_exists_of_act_polarity` |
| `contrastive_agency_principle` | `Logos.Choice` | 4 | `contrastive_agency_implies_existential`, `freeSubject_exists_of_contrastive_act`, `freeWill_exists_of_contrastive_act`, `genuineChoice_exists_of_contrastive_act` |
| `PluralityLovePrinciple` | `Logos.Love` | 4 | `T14_content_conditional`, `T14_eternalRelation_conditional`, `T14_square_conditional`, `T14_world_conditional` |
| `weak_act_implies_strong_act` | `Logos.Agency` | 3 | `Cogito_of_bridge`, `noAct_conditional_selfRefutes`, `strong_act_of_weak_act` |
| `bilateral_intentionality_principle` | `Logos.Choice` | 3 | `bilateral_implies_act_polarity`, `deliberateResource_of_bilateral_intentionality`, `genuineChoice_exists_of_bilateral_intentionality` |
| `PersonStabilityPrinciple` | `Logos.Love` | 3 | `T14_eternalRelation_conditional`, `T14_square_conditional`, `T14_world_conditional` |
| `DoubtingDatum` | `Logos.Choice` | 2 | `freeWill_exists_of_doubt_datum`, `genuineChoice_exists_of_doubt_datum` |
| `deliberateGenuineChoiceResource` | `Logos.Choice` | 2 | `deliberateChoice_exists_of_assertion_and_negation_meaning`, `deliberate_resource_implies_genuine_choice` |
| `doubt_existence_bridge` | `Logos.Choice` | 2 | `freeWill_exists_of_doubt_bridge`, `genuineChoice_exists_of_doubt_bridge` |
| `existential_act_polarity` | `Logos.Choice` | 2 | `freeWill_exists_of_existential_act_polarity`, `genuineChoice_exists_of_existential_act_polarity` |
| `RestrictedTranscendentalBridge` | `Logos.Retorsion` | 2 | `restricted_bridge_derives_a17_weak`, `restricted_bridge_derives_a17b` |
| `NoGN` | `Logos.RetorsiveNormativity` | 2 | `denial_of_genuine_normativity_is_self_refuting`, `normative_denial_of_normativity_is_self_refuting` |
| `ConstitutiveRightWrong` | `Logos.UndeniableNormativeDerivation` | 2 | `bridge_a_constitutive_normativity_derives_free_will`, `normative_free_will` |
| `JudicativeBipolarityProp` | `Logos.BipolarityRetorsion` | 1 | `level_1_conditional_bipolarity_boundary` |
| `NoChoiceField` | `Logos.Choice` | 1 | `noChoiceField_contradicts_field` |
| `act_implies_asserts_bridge` | `Logos.Choice` | 1 | `selection_exists_of_act` |
| `existential_intentional_choice` | `Logos.Choice` | 1 | `freeWill_exists_of_existential_choice` |
| `NoRight` | `Logos.DirectNormativeRetorsion` | 1 | `proof_criticism_nihilism_self_refuting` |
| `AsymmetricGrounding` | `Logos.FoundationalUnicity` | 1 | `universal_ground_unicity` |
| `D` | `Logos.RealityHookAudit` | 1 | `settlementChoice_compatible_with_case_D` |
| `A17_strong` | `Logos.Retorsion` | 1 | `a17_strong_implies_a17_weak` |
| `A17b` | `Logos.Retorsion` | 1 | `a17b_implies_a17_weak` |
| `EverythingObjective` | `Logos.Retorsion` | 1 | `everything_objective_self_applies` |
| `EverythingSubjective` | `Logos.Retorsion` | 1 | `everything_subjective_self_applies` |
| `PigTranscendentalReflectionHypothesis` | `Logos.Retorsion` | 1 | `winged_pig_derived_of_pig_reflection` |
| `WeakenedTranscendentalReflectionHypothesis` | `Logos.Retorsion` | 1 | `weakened_retorsion_derives_intentional_subject` |
| `ExtensionalRightWrong` | `Logos.UndeniableNormativeDerivation` | 1 | `bridge_b_plurality_yields_choice_field` |
| `PersonsAffectPrinciple` | `Logos.Value` | 1 | `valueInterpersonal_of_split_conditional` |

**A entrada que manda na leitura.** `act_polarity_principle` tem **7** dependentes —
é o maior expoente, e o único em que uma `def` sustenta mais teoremas do que qualquer
axiome declarado do corpus. Em segunda ordem de prioridade, ponderando o centro teológico
além da contagem: `PluralityLovePrinciple` (4) e `PersonStabilityPrinciple` (3)
sustentam T13/T14, e `ConstitutiveRightWrong` (2) sustenta a rota normativa directa
inteira. Nenhuma delas foi tocada: esta secção mede e nomeia, e a promoção é uma
decisão semântica do autor, não um refactor.

