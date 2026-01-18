# Aquilo que Avalia sem Ser Avaliado
> Este argumento opera ao **nível meta-ontológico**: não discute verdades dentro de sistemas formais, mas as **condições de possibilidade de qualquer sistema avaliativo**.”

## Paradoxo do mentiroso
**Epimenides de Creta** formulou a versão mais antiga deste paradoxo que se conhece ao dizer que *"Todos os cretenses são mentirosos"* no século VI a.C.

O paradoxo, enquanto problema lógico explícito, é normalmente atribuído a **Eubúlides de Mileto** no século IV a.C. Com a versão clássica: *"Esta frase é falsa"*.

Esta proposição estabelece-se como paradoxo porque sendo falsa, é verdadeira, e sendo verdadeira, é falsa. Em efeito, igualando a própria expressão com a sua negação.

Mais tarde, **Aristóteles**, em *Metafísica* e *Sobre as Refutações Sofísticas*, sem que resolva o paradoxo, estabelece distinções fundamentais para mais tarde serem discutidos estes problemas de auto-referência.

Os **estoicos** levam este problema muito a sério e interpretam-no como um teste à coerência da lógica proposicional. O que os leva a analisar rigorosamente a noção de *lekton* (conteúdo dizível).

Na idade média, lógicos medievais como **Pedro Hispano** e **Guillaume d'Ockham** analisam frases autoreferenciais e propõem soluções técnicas (negação de significação plena, distinções semanticas). O paradoxo é tratado como um problema lógico legítimo, não como um jogo retórico.

No século XX, o paradoxo torna-se central em lógica matemática e fundamentos.

- **Bertrand Russel** vê nele um sintoma de inconsistência ligada à autoreferência.

- **Alfred Tarski** responde com a hierarquia de linguagens (objeto vs. metalinguagem).

- **Kurt Gödel** usa uma estrutura análoga para provar teoremas de incompletude. Aqui, o "metiroso" é arimetizado.

## Halting problem
**Alan Turing** traduz o mesmo esquema para máquinas ao perguntar se:
> Existe um procedimento geral que decide se qualquer programa pára?

E constrói um programa que:

- Consulta esse decisor,
- E faz o oposto do que ele prevê sobre si próprio.

Algo deste género:
```
Q(P) {
    if halts(P, P); then
        loop_forever
    else
        halt
    endif
}
```
Passando depois o próprio programa Q como argumento P, sendo que passamos a ter algo como:
```
Q(Q) faz o contrário de si próprio.
```
Na altura decidiu-se que não pode haver um decisor que consiga determinar se um programa pára ou não, por isto ser paradoxal.
Podemos, no entanto, formular uma versão mais simples do problema:
```
Q(P) {
    return !P(P)
}
```
O que, utilizando notação lógica, pode equivaler-se à expressão: **Q(P) = ¬P(P)**. Passando assim, conscientemente, do ambito da computação, de volta à lógica formal. Se substituirmos *P* por *Q*, obtemos a expressão:

**Q(Q) = ¬Q(Q)**

> **Nota técnica**: Não se trata de um programa executável nem de uma definição computacional literal, mas de um **esquema de diagonalização**. A expressão `Q(Q) = ¬Q(Q)` representa a fixação semântica do ponto diagonal onde uma função supostamente decisora é aplicada ao seu próprio índice. Não descreve um processo computável, mas explicita a impossibilidade estrutural de auto-decisão total.

Aqui ficamos com uma expressão iguala *algo* ao seu contrário, o que é claramente contradição. Apesar de já não existir um verificador de paragem universal, o paradoxo ressurge. Porquê? Porque surge o mesmo problema:

**A auto-avaliação total, correcta e completa.**

No caso do mentiroso, o critério é **verdade/falsidade**. No caso do halting problem, o critério é **pára/não pára**. Em ambos os casos, quando a função avaliadora é aplicada ao seu **próprio índice**, surge uma contradição.

## Sobre a Verdade Forte
Da mesma forma que **Epimenides** disse que *"Todos os cretenses são mentirosos"* (apesar de não ter dito *"Todos os cretenses só dizem mentiras"*, sendo ele próprio de Creta. A negação contemporânea da normatividade última manifesta-se na proposição: **'Não existe Verdade Forte (absoluta)'**. Esta afirmação não é apenas um erro de facto, mas uma **aporia performativa**: para que a negação seja inteligível e vinculativa, ela teria de habitar a própria 'Verdade Forte' que pretende abolir. O proferimento tenta suicidar a sua própria condição de validade.

O problema aqui é que a frase também se afirma sobre si própria. Isto é, se não existe verdade, então a própria frase não o pode ser. É a chamada contradição performativa, e uma outra forma (implícita) do **Paradoxo do mentiroso**.

De forma coloquial, afirma-se: **A verdade é subjetiva**. Contudo, o erro lógico é duplo: primeiro, a afirmação pretende ser uma verdade *objetiva* sobre a subjetividade; segundo, ela tenta localizar a autoridade normativa no indivíduo empírico. Ora, o indivíduo, enquanto objeto biológico ou psicológico, é um sistema avaliado por leis (física, biologia, psicologia). Ao dizer que a verdade é subjetiva, o falante tenta atribuir ao 'eu' a função de Sujeito Ontológico (o que avalia) enquanto o mantém como objeto (o que é avaliado), resultando no mesmo colapso auto-referencial.

O que implica que o contrário da afirmação (neste caso *"existe verdade objectiva"*) é verdade necessária.

Postula-se pois, pela mesma razão que **Existe Verdade Forte** é verdade necessária.

> **Nota** — Qualquer crítica a esta conclusão que pretenda validade geral já pressupõe exatamente o tipo de verdade necessária aqui demonstrada, invalidando-se performativamente no próprio acto de formulação.
> Além disso, a distinção verdadeiro/falso é já uma **distinção normativa mínima** — algo deve ser afirmado e algo rejeitado — pelo que todo fundamento da verdade é, por necessidade lógica, também fundamento da normatividade, não existindo verdade objectiva semanticamente neutra.

> **Nota aclaratória** — “Verdade Forte” não designa uma teoria semântica específica, mas a impossibilidade de eliminar a distinção normativa verdadeiro/falso sem incoerência performativa.
> O argumento é independente de qualquer análise particular da verdade, pois **toda análise já pressupõe um critério normativo de correção**.

## Sobre o fundamento da verdade
> O termo “necessário” é aqui usado num sentido estrito: aquilo cuja negação implica **contradição performativa** ou impossibilidade de discurso normativo coerente. Não se trata de necessidade psicológica nem meramente formal, mas de necessidade ontológica mínima exigida pela possibilidade de avaliação racional.

O fundamento da verdade de um sistema tem que ser externo a esse sistema. A auto-fundação não é sustentável.

> A hipótese de um “facto bruto” último não resolve o problema do fundamento. Um facto bruto pode interromper perguntas causais, mas não **fundamenta normatividade**. Um fundamento que não explica por que a avaliação é válida não a funda — apenas suspende a exigência racional, o que equivale a abdicar da própria noção de fundamento.

Aqui questiona-se: **não são sistemas que regem o mundo material?**. E responde-se: regem-no enquanto **mecanismos de funcionamento**, mas não enquanto **fundamentos de validade**. Um sistema físico descreve a regularidade de um processo; ele não fundamenta a 'correção' da sua própria existência nem a obrigatoriedade da sua inteligibilidade. Confundir a *regularidade descritiva* (o modo como as coisas funcionam) com a *soberania normativa* (o porquê de o sistema ser verdadeiro) é um erro categorial: o funcionamento é um **dado**, o fundamento é uma **condição**.

Isto implica que **há fundamento que o transcende**, e é, sem sombra de dúvida, **incontornável sem cair no absurdo**. Isto é, **tem de haver fundamento último externo a todo e qualquer sistema.**

Apenas por necessidade lógica, pretendemos derivar as caracterísitcas necessárias deste fundamento.

## Características necessárias do fundamento último
### 1) Não pode ser um sistema
> Porque todo sistema pressupõe regras e domínio; fundar isso exigiria algo anterior ao próprio sistema, levando a regressão infinita ou paradoxo de auto-avaliação.
### 2) Não é uma lei
> Leis apenas regulam o funcionamento de algo já dado; não explicam a possibilidade do próprio funcionamento, recaindo na impossibilidade de auto-fundação.
### 3) Não é um conjunto de axiomas
> Axiomas valem dentro de estruturas formais; o fundamento não pode depender de uma estrutura prévia, senão colapsaria em circularidade como nos paradoxos.
### 4) Não é contingente
> Se pudesse não existir, a possibilidade geral de verdade e sentido não estaria assegurada, permitindo o absurdo de um mundo sem normatividade coerente.
### 5) Não é totalmente formalizável
> Se fosse exaustivamente formalizável, tornar-se-ia objeto avaliável e voltaria a ser sistema, gerando contradição auto-referencial.
### 6) Não pode ser relativo
> Se variasse por perspectiva ou sistema, deixaria de fundamentar todos os sistemas, levando a subjetivismo performativamente incoerente.
### 7) Não depende de validação
> O que torna a validação possível não pode depender de ser validado, evitando regressão e mantendo a exterioridade necessária.
### 8) É anterior à distinção verdadeiro/falso
> A própria distinção pressupõe algo que a torne possível, precedendo-a para evitar que a dualidade se auto-fundamente paradoxalmente.
### 9) Não é composto
> Se tivesse partes, exigiria um princípio de unidade mais fundamental do que ele próprio, criando regressão infinita.
### 10) Não é derivável
> Se pudesse ser deduzido de algo mais básico, esse algo — e não ele — seria o verdadeiro fundamento, violando a ultimidade.
### 11) Não pode ser causado
> Se tivesse causa, essa causa seria mais fundamental do que ele, levando a regressão e contradizendo a necessidade de um fim último.
### 12) Não pode emergir
> Emergência pressupõe condições prévias; o fundamento não pode depender delas, senão recairia em dependência circular.
### 13) Não pode ser condicionado
> Qualquer condição que o limitasse funcionaria como fundamento superior, gerando paradoxo de hierarquia infinita.
### 14) Não pode estar em relação de dependência
> Dependência é assimétrica e exige um termo mais básico do qual depender, contrariando a independência última.
### 15) Não pode ser particular
> Um fundamento particular não poderia fundamentar universalmente, permitindo inconsistências locais como nos paradoxos.
### 16) Não pode ser limitado
> Limites exigem um critério externo que os imponha, subordinando o fundamento e criando regressão.
### 17) Não pode ser probabilístico
> Probabilidade pressupõe espaço de possibilidades já estruturado, que o fundamento deve preceder para evitar circularidade.
### 18) Não pode ser temporalmente situado
> A situação temporal implica sucessão e submissão à causalidade (antes/depois). Se o fundamento estivesse no tempo, ele seria condicionado pelo momento da sua ocorrência, exigindo uma explicação para a sua génese. O fundamento deve possuir **anterioridade ontológica (atemporalidade)**, sendo a condição de possibilidade da própria sucessão temporal, e não um evento dentro dela.
### 19) Não pode falhar
> Falha pressupõe norma externa em relação à qual algo falha, contradizendo a superioridade do fundamento.
### 20) Não pode não ser livre
> Exatamente por não poder ser determinado por algo externo, evitando dependência e mantendo autoridade inerente.

> Normatividade não é mera estrutura descritiva, mas **autoridade prescritiva**. Estruturas descrevem regularidades; autoridade discrimina o que deve ou não deve ser afirmado. Prescrição sem fonte de autoridade é um erro categorial. Logo, um fundamento normativo último não pode ser impessoal sem perder precisamente aquilo que pretende fundar.

### 21) Não pode ser impessoal
> A impessoalidade é a categoria do **objeto subordinado**; define-se pela reatividade a leis externas e pela inércia normativa. Um fundamento impessoal (como uma 'lei da natureza' ou um 'facto bruto') possui **poder causal**, mas carece de **autoridade normativa**. Factos apenas *são*; a Verdade *exige*. Como a exigência de correção não pode emanar da passividade de um objeto, o fundamento tem de ser a instância ativa da distinção — o que define a função ontológica de **Sujeito Originário**."

## Sobre a impossibilidade de normatividade sem autoridade não derivada
Normatividade não se reduz a regularidade descritiva, coerência estrutural ou conformidade factual. A distinção correcto/incorreto, quando dotada de validade geral, envolve **vinculação racional**: não apenas descreve critérios de correção, mas determina o que conta como razão suficiente para aceitar ou rejeitar uma posição.

Regras, estruturas formais, factos empíricos ou padrões emergentes podem especificar condições de validade, mas não explicam por que essas condições são **racionalmente obrigatórias**. A forma lógica de uma regra não gera, por si só, autoridade normativa; do mesmo modo, a existência de um facto não impõe obrigação racional de aceitá-lo como critério último. **A normatividade não é uma propriedade emergente da complexidade.** Um milhão de factos brutos continuam a ser apenas 'dados' passivos; nenhum salto quantitativo de informação produz a qualidade da *vinculação*. Confundir funcionamento normativo com fundamento da normatividade é um erro categorial.

Se existe distinção correcto/incorreto com pretensão de validade geral, então existe uma **fonte de normatividade** cuja autoridade não deriva de qualquer regra, estrutura ou critério externo, nem está sujeita a avaliação superior. Essa fonte não pode consistir apenas em entidades ou descrições impessoais, pois nenhuma delas explica a vinculatividade racional do critério que enunciam. O que aqui se afirma não é a introdução de uma entidade adicional, mas a identificação de uma **condição de possibilidade** da normatividade enquanto tal.

Qualquer fundamento que satisfaça estas condições exerce funcionalmente o papel mínimo exigido para que a avaliação normativa com validade geral seja possível. A designação tradicional dessa função ontológica será introduzida apenas posteriormente; neste ponto, o argumento limita-se a estabelecer a sua necessidade estrutural.

## Definição (Sujeito mínimo)
Qualquer instância que exerça avaliação normativa vinculativa, sem derivar essa autoridade e sem estar subordinada a outra, desempenha funcionalmente aquilo que a tradição ontológica denomina **Sujeito** — não no sentido psicológico ou fenomenológico, mas como função ontológica mínima de autoridade normativa. Introduzir o termo não acrescenta conteúdo; apenas nomeia uma função cuja necessidade já foi logicamente estabelecida. Recusar o nome não elimina a função, apenas a disfarça.

> A introdução do termo ‘Sujeito’ não adiciona conteúdo ontológico ao argumento, mas apenas nomeia a função mínima já implicitamente exigida pelas características do fundamento.

Designamos por **Sujeito** o *locus* da **Agência Normativa Não-Derivada**. Esta função não descreve uma psique ou um ego empírico, mas a **necessidade transcendental de um Avaliador que não é passível de avaliação**. Na gramática do ser, se o objeto é o que é 'posto' (), o Sujeito é o que 'sustenta' () a validade do que é posto. Recusar o termo enquanto se aceita a função é um nominalismo irrelevante; o compromisso ontológico com uma Agência Transcedental já foi consumado pela lógica do argumento.

### Nota Terminológica sobre “Sujeito”
O termo "Sujeito" é aqui usado em sentido estritamente ontológico, não psicológico nem fenomenológico. Remete à tradição clássica do *ὑποκείμενον* (hypokeímenon: termo grego antigo que significa 'aquilo que subjaz', como base que sustenta determinações, sem conotações de 'eu' consciente moderno). Nesta acepção original — anterior à reinterpretação cartesiana — o Sujeito não é consciência representacional, mas condição de possibilidade da determinação normativa. A oposição entre *subjectum* e *objectum* é assimétrica: o objecto é posto; o Sujeito sustenta a relação. É nesse sentido arcaico que usamos o termo.

“Sujeito” não designa aqui consciência psicológica ou ego empírico, mas a função ontológica mínima que exerce autoridade normativa não derivada (cf. o ὑποκείμενον em Aristóteles, Metafísica, Ζ).

Os atributos positivos que se seguem não são propriedades adicionadas arbitrariamente, mas **formulações afirmativas das exclusões lógicas previamente estabelecidas**. Cada atributo corresponde à negação de uma forma de dependência, limitação ou contingência. Não se trata de acumulação ontológica, mas de depuração lógica.

## Conclusão

### Primeira parte
Da impossibilidade de auto-fundação, regressão infinita e relativização normativa, segue-se necessariamente a existência de um fundamento último com as seguintes características mínimas:
- não derivado
- não sistémico
- normativamente autoritativo
- transcendente a qualquer estrutura formal
- condição de possibilidade da distinção correcta/incorreta

Negar este resultado implica abdicar da possibilidade de crítica racional com validade geral.

### Segunda parte
A partir deste fundamento mínimo, e analisando o que ele **não pode ser** sem colapsar nas contradições previamente excluídas, derivam-se atributos adicionais tradicionalmente associados ao fundamento último (unidade, simplicidade, eternidade, etc.).

Estas derivações não introduzem novos princípios, mas explicitam consequências lógicas da ultimidade já estabelecida.

### Terceira parte
A identificação deste fundamento como **Deus** não constitui um salto fideísta, mas uma **identidade semântica necessária**. No léxico da Ontologia Fundamental, o 'Sujeito absoluto, necessário, simples e fonte de toda a normatividade' é a definição exaustiva de Divindade. A relutância em usar o termo não altera a estrutura da realidade revelada: quem aceita a necessidade de um fundamento último e pessoal para a verdade, já está a descrever aquilo que a tradição denomina.

Recusar essa designação não altera o compromisso ontológico assumido, desde que a função normativa última aqui identificada seja mantida.

## Sobre a Alegada Falibilidade do Argumento

Todas as objeções que pretendem validade geral sem abdicar da normatividade — apesar de variarem no vocabulário — reduzem-se, em última análise, a **uma única estratégia**: a alegação de que a conclusão **não é logicamente necessária**. As restantes objeções não são independentes, mas **variações derivadas** dessa mesma confusão de níveis.

### A objeção central: “não é logicamente necessário”

Esta objeção sustenta que, mesmo concedendo os limites da auto-referência e da auto-fundação, **não é dedutivamente forçado** concluir a existência de um fundamento último com as características derivadas.

O erro aqui é técnico e decisivo:
o argumento **não opera ao nível da dedução lógico-formal**, mas ao nível **transcendental**.

A questão não é o que pode ser formalmente derivado a partir de premissas neutras, mas:

> **O que tem de ser o caso para que avaliação racional, crítica válida e objeção com pretensão universal sejam possíveis?**

Qualquer tentativa de negar a conclusão:

* pretende validade geral,
* distingue correto/incorreto,
* e exige que a sua negação seja racionalmente vinculativa.

Ao fazê-lo, **já exerce exatamente o tipo de normatividade** cuja possibilidade está em causa no argumento.


Se a objeção abdicar dessa pretensão — tornando-se local, contingente ou meramente atitudinal — deixa de ser objeção racional e passa a ser apenas ruído subjetivo. Se a mantiver, **ela confessa a sua dependência**: o crítico tenta usar a autoridade da lógica para negar a autoridade do fundamento da lógica. É uma tentativa de suicídio intelectual: o crítico só consegue formular a negação porque o fundamento que ele nega lhe fornece os instrumentos de validade para o fazer. Não existe terceira via estável.

### Nota sobre as objeções derivadas

As alegadas “alternativas normativas impessoais” e a crítica do “salto ilegítimo para o Sujeito” não introduzem dificuldades adicionais. Ambas pressupõem precisamente aquilo que a objeção central tenta negar: a possibilidade de normatividade vinculativa com validade geral.

A primeira confunde **condições de funcionamento** com **condições de validade**;
a segunda confunde **nomeação funcional** com **acréscimo ontológico**.

Em ambos os casos, o erro só parece plausível enquanto se ignora o nível transcendental em que o argumento opera.

## Abdicar da validade geral (Verdade Forte) não é uma opção intelectual
> é o silenciamento da razão.

Quem renuncia ao fundamento último renuncia à capacidade de distinguir o argumento do ruído, a crítica da força, e a verdade do delírio. Fora desta estrutura, o discurso não se torna 'livre' ou 'plural' — torna-se estritamente **impossível**."

**Em suma, o argumento repousa sobre uma Tríade de Necessidade:**
1. **Lógica:** A auto-referência total sem fundamento externo gera paradoxo.
2. **Transcendental:** A normatividade exige uma autoridade que não seja um objeto avaliado.
3. **Ontológica:** O fundamento desta autoridade tem de ser um Sujeito Livre e Necessário.

## Diagrama lógico
```mermaid
graph TD
    %% Definição de Estilos para clareza visual
    classDef base fill:#f5f5f5,stroke:#333,stroke-width:1px;
    classDef logic fill:#d4e6f1,stroke:#2980b9,stroke-width:2px;
    classDef ontology fill:#d5f5e3,stroke:#27ae60,stroke-width:2px;
    classDef final fill:#2c3e50,stroke:#f1c40f,stroke-width:4px,color:#fff;
    classDef fail fill:#fadbd8,stroke:#c0392b,stroke-dasharray: 5 5;

    %% O Início
    Start([Qualquer Afirmação Racional]) -->|Tenta descrever a realidade| A{Existe Verdade Forte?}
    
    %% Passo 1: A Armadilha da Negação
    A -- "Não" --> B[Contradição Performativa]
    B -->|Negar é afirmar uma verdade| A
    
    %% Passo 2 e 3: A Lógica
    A -- "Sim" --> C[Verdade exige AVALIAÇÃO]
    C -->|Distinção Verdadeiro/Falso| D[Sistemas não se auto-fundam]
    D -->|Teorema da Incompletude| E(Necessidade de Ponto Exterior)

    %% Passo 4: A Natureza do Fundamento
    E --> F{O que é esse Ponto?}
    F -- "Objeto ou Lei?" --> G[Objeto: É avaliado, não avalia]
    G -.->|Falha como fundamento| H[Regressão Infinita]
    
    F -- "Única opção lógica" --> I[SUJEITO]
    
    %% Passo 5, 6 e 7: Os Atributos Divinos
    I -->|Não condicionado| J[LIVRE]
    I -->|Fonte de dever/norma| K[Fonte de VALOR]
    
    J & K --> L[O Bem Absoluto é RELACIONAL]
    L -->|Doação / Amor Ontológico| M((DEUS))

    %% Aplicação dos Estilos
    class Start,A base;
    class C,D,E,F logic;
    class I,J,K,L ontology;
    class M final;
    class B,G,H fail;
```

# Vídeo explicativo
[Aqui disponível](https://tty.pt/maquina.mp4)
