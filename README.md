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

# Nota metodológica sobre o tipo de necessidade envolvida
O presente argumento não opera ao nível da contradição lógico-formal (do tipo p ∧ ¬p), mas ao nível da **necessidade transcendental**: investiga as condições sem as quais **avaliação racional, crítica válida e distinção normativa** não são possíveis.

A negação das conclusões aqui derivadas não produz, em geral, uma contradição sintáctica imediata, mas produz **incoerência performativa**: o acto de negar pressupõe exactamente o tipo de autoridade normativa cuja possibilidade está em causa.

Assim, a necessidade envolvida não é psicológica, empírica ou meramente formal, mas **ontológica-discursiva**: aquilo que tem de ser o caso para que o discurso racional enquanto tal seja possível.

## Sobre a Verdade Forte
Da mesma forma que **Epimenides** disse que *"Todos os cretenses são mentirosos"*, sendo ele próprio de Creta. Também um homem moderno pode formular coisas como:

**Não Existe Verdade Forte**.

> Sim, é verdade que não disse o que seria uma forma mais equivalente ao paradoxo *"Todos os cretenses mentem sempre"*.

O problema aqui é que a frase também se afirma sobre si própria. Isto é, se não existe verdade, então a própria frase não o pode ser. É a chamada contradição performativa, e uma outra forma (implícita) do **Paradoxo do mentiroso**.

De forma coloquial, também pode afirmar: **A verdade é subjectiva** (ou *toda a verdade é subjectiva*). Mas sendo rigorosos, podemos observar que isto implicaria, se literal, a existência de sujeitos numa base objectiva, e seria mais uma forma deste **paradoxo**.

O que implica que o contrário da afirmação (neste caso *"existe verdade objectiva"*) é verdade necessária.

Postula-se, pela mesma razão que **Existe Verdade Forte** é verdade necessária.

> **Nota**: Qualquer crítica a esta conclusão que pretenda validade geral (isto é, que se aplique a todos os casos e não apenas como opinião local) já pressupõe exatamente o tipo de verdade necessária que aqui se demonstra, invalidando-se a si própria no ato da formulação.
>
> Enquanto este tipo de afirmações possam *parecer* humildes e tolerantes, são na verdade afirmações que se **auto-invalidam**.
>
> Importa notar que a distinção verdadeiro/falso já é uma **distinção normativa mínima**: algo deve ser afirmado e algo rejeitado. Logo, qualquer fundamento da verdade é, por necessidade lógica, também fundamento da normatividade. Não existe verdade objetiva semanticamente neutra; toda verdade implica um critério de correção.

> **Nota aclaratória**
> A expressão “Verdade Forte” não designa aqui uma teoria semântica específica (correspondência, coerência, pragmatismo, etc.), mas a impossibilidade de eliminar a distinção normativa verdadeiro/falso sem incoerência performativa.
> 
> O argumento não depende de como a verdade é analisada, mas do facto de que **qualquer análise já pressupõe um critério normativo de correção.**

## Sobre o fundamento da verdade
> O termo “necessário” é aqui usado num sentido estrito: aquilo cuja negação implica **contradição performativa** ou impossibilidade de discurso normativo coerente. Não se trata de necessidade psicológica nem meramente formal, mas de necessidade ontológica mínima exigida pela possibilidade de avaliação racional.

> Chegados aqui, convém fazer o que raramente se faz: **parar de fingir que o sistema se sustenta sozinho**. Todo o sistema que avalia — seja lógico, matemático ou discursivo — pressupõe algo que **não é avaliado por ele**, sob pena de regressão infinita (que não providencia fundamento, apenas evita a questão) ou colapso paradoxal. Isto não é uma falha acidental; é uma condição estrutural.

O fundamento da verdade de um sistema tem que ser externo a esse sistema. A auto-fundação não é sustentável.

> A hipótese de um “facto bruto” último não resolve o problema do fundamento. Um facto bruto pode interromper perguntas causais, mas não **fundamenta normatividade**. Um fundamento que não explica por que a avaliação é válida não a funda — apenas suspende a exigência racional, o que equivale a abdicar da própria noção de fundamento.

Aqui questiona-se: **não são sistemas que regem o mundo material?**. E responde-se: **não no sentido em que o fundam**, porque aí caímos no erro de um **sistema não poder fundar-se a si mesmo**. Mas sim num outro sentido - **são sistemas que determinam o funcionamento do mundo material**.

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
> Situação temporal implica antes/depois e condições de ocorrência, violando a eternidade necessária para fundar o tempo.
### 19) Não pode falhar
> Falha pressupõe norma externa em relação à qual algo falha, contradizendo a superioridade do fundamento.
### 20) Não pode não ser livre
> Exatamente por não poder ser determinado por algo externo, evitando dependência e mantendo autoridade inerente.

> Normatividade não é mera estrutura descritiva, mas **autoridade prescritiva**. Estruturas descrevem regularidades; autoridade discrimina o que deve ou não deve ser afirmado. Prescrição sem fonte de autoridade é um erro categorial. Logo, um fundamento normativo último não pode ser impessoal sem perder precisamente aquilo que pretende fundar.
### 21) Não pode ser impessoal
> O fundamento precisa ser a fonte de normatividade (não só o espaço onde normas ‘estão’), e fonte implica posse de autoridade não derivada. Autoridade não derivada é um modo de ser que é melhor descrito como sujeito.

## Sobre a impossibilidade de normatividade sem autoridade não derivada
Qualquer critério normativo exige algo que **autorize** a sua aplicação.
- Regras não se autorizam a si próprias.
- Estruturas não obrigam.
- Factos não prescrevem.

> **Nota** — Normatividade não consiste apenas em critérios de validade, mas em **vinculação racional**. Regras, estruturas ou factos podem descrever correção, mas não explicam **por que** alguém está obrigado a segui-los. A obrigatoriedade não é redutível à forma lógica da regra (cf. Immanuel Kant, Crítica da Razão Prática).

Logo, se existe distinção correcta/incorreta com validade geral, então existe uma instância cuja autoridade **não deriva** de nenhum critério externo **e não é validável por instância superior**.

> A autoridade normativa não é uma propriedade flutuante de estruturas, mas algo que **se exerce**; falar de normatividade vinculativa sem instância que a exerça é um erro categorial.

Qualquer instância que satisfaça estas condições exerce funcionalmente aquilo que a tradição ontológica denomina Sujeito. O termo não acrescenta propriedades; apenas nomeia a função já demonstrada como necessária.

## Definição (Sujeito mínimo)
> A introdução do termo ‘Sujeito’ não adiciona conteúdo ontológico ao argumento, mas apenas nomeia a função mínima já implicitamente exigida pelas características do fundamento.
Designamos por **Sujeito** a instância mínima que satisfaz simultaneamente quatro condições irredutíveis:
1. Exercer **avaliação normativa** (discriminar o correcto do incorrecto);
2. Não derivar a sua autoridade de qualquer regra ou critério externo;
3. Não estar sujeito a qualquer avaliação superior;
4. Não se reduzir a propriedades, estruturas, leis ou funções formais.
Qualquer instância que satisfaça estas quatro condições exerce, funcionalmente, aquilo que na tradição ontológica se denomina **Sujeito**. Recusar o termo mantendo a função é mera substituição lexical sem ganho explanatório.
Estas condições não descrevem uma entidade empírica, mas uma função ontológica mínima exigida pela normatividade racional.
> **Nota Terminológica (sobre “Sujeito”)**
> O termo "Sujeito" é aqui usado em sentido estritamente ontológico, não psicológico nem fenomenológico. Remete à tradição clássica do *ὑποκείμενον* (hypokeímenon: termo grego antigo que significa 'aquilo que subjaz', como base que sustenta determinações, sem conotações de 'eu' consciente moderno). Nesta acepção original — anterior à reinterpretação cartesiana — o Sujeito não é consciência representacional, mas condição de possibilidade da determinação normativa. A oposição entre *subjectum* e *objectum* é assimétrica: o objecto é posto; o Sujeito sustenta a relação. É nesse sentido arcaico que usamos o termo.
>
> “Sujeito” não designa aqui consciência psicológica ou ego empírico, mas a função ontológica mínima que exerce autoridade normativa não derivada (cf. o ὑποκείμενον em Aristóteles, Metafísica, Ζ).

> Os atributos positivos que se seguem não são propriedades adicionadas arbitrariamente, mas **formulações afirmativas das exclusões lógicas previamente estabelecidas**. Cada atributo corresponde à negação de uma forma de dependência, limitação ou contingência. Não se trata de acumulação ontológica, mas de depuração lógica.

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
O que a tradição filosófica clássica denomina “Deus” não é aqui introduzido como hipótese teológica adicional, mas como **designação histórica** para o tipo de fundamento cuja existência foi demonstrada como necessária.

Recusar essa designação não altera o compromisso ontológico assumido, desde que a função normativa última aqui identificada seja mantida.

## Sobre a Alegada Falibilidade do Argumento
Todas as objeções que pretendem validade geral sem abdicar da normatividade — apesar de variarem no vocabulário e na sofisticação aparente — reduzem-se estruturalmente a **três estratégias falhadas**, nenhuma das quais consegue escapar àquilo que o próprio argumento demonstra como necessário. Não são objeções independentes; são variações do mesmo erro categorial.

### 1. A objeção do “há alternativas normativas impessoais”

Esta objeção afirma, explicitamente ou por implicação, que a normatividade pode emergir de **estruturas, práticas, sistemas inferenciais ou regularidades constitutivas**, sem requerer um fundamento último dotado de autoridade não derivada.

O problema é simples e fatal:
essas “alternativas” **não explicam normatividade**, apenas **deslocam-na**.

* Estruturas **descrevem** relações.
* Práticas **instituem** hábitos.
* Regras **operam** dentro de domínios.

Nenhuma dessas coisas possui, por si só, o poder de **obrigar racionalmente**.
Elas só funcionam **sob a condição já pressuposta** de que *se deve* seguir a estrutura, *se deve* aceitar a prática, *se deve* respeitar a regra.

Logo, tais propostas **presumem exatamente aquilo que dizem dispensar**:
um critério de correção não derivado que torne válida a obediência normativa.

Não se trata de uma lacuna empírica, mas de uma **falha ontológica**:
confundir **condições de funcionamento** com **condições de validade**.

### 2. A objeção do “salto ilegítimo para o Sujeito”

Esta objeção sustenta que a introdução do **Sujeito** constitui um acréscimo ontológico arbitrário, uma personalização indevida de algo que poderia permanecer impessoal.

Mas esta crítica confunde **nomeação funcional** com **postulação gratuita**.

O argumento não acrescenta um Sujeito — ele **torna explícita** uma função que já estava implicitamente exigida desde o primeiro passo:
a função de **avaliar normativamente com autoridade não derivada**.

Se:

* há distinção correta/incorreta,
* essa distinção não é relativa,
* não deriva de regras superiores,
* e não é validável por instância externa,

então **há algo que exerce autoridade avaliativa por si mesmo**.

Recusar o termo “Sujeito” mantendo a função não elimina o compromisso ontológico — apenas o **oculta sob vocabulário neutro**.
Isso não é parcimónia; é **evasão semântica**.

Negar simultaneamente o Sujeito *e* a função dissolve o próprio estatuto da objeção enquanto crítica racional, pois já não há critério pelo qual ela poderia ser correta.

### 3. A objeção do “não é logicamente necessário”

Esta é a objeção mais comum e a mais fraca. Afirma que, mesmo concedendo os limites da auto-referência, **não é logicamente forçado** concluir um fundamento último com as características derivadas.

Mas aqui ocorre um erro técnico decisivo:
o argumento **não opera ao nível da dedução formal**, mas ao nível **transcendental**.

Não se pergunta “o que se pode imaginar?”, mas:

> **O que tem de ser o caso para que avaliação racional, crítica válida e objeção universal sejam possíveis?**

Qualquer tentativa de negar a conclusão:

* pretende validade geral,
* distingue correto/incorreto,
* e exige que a sua negação seja racionalmente vinculativa.

Logo, **já exerce exatamente o tipo de normatividade** cuja possibilidade está em questão.

Se a objeção for apenas local, contingente ou atitudinal, ela não refuta o argumento — apenas abdica de qualquer pretensão racional.
Se pretender validade geral, **confirma performativamente** a necessidade do fundamento.

Não existe terceira via estável.

### Síntese Final

Todas as objeções falham pelo mesmo motivo estrutural:

> tentam negar o fundamento último **usando** os recursos que só são possíveis **se esse fundamento existir**.

Ou:

* substituem autoridade por regularidade,
* confundem descrição com prescrição,
* ou exigem validade universal enquanto negam a sua própria possibilidade.

Nenhuma escapa à regressão, à circularidade ou à auto-invalidade performativa.

Assim, o argumento não é enfraquecido pelas objeções —
ele **explica por que elas surgem**, **por que parecem plausíveis** e **por que não podem, em princípio, ser conclusivas**.

O fundamento último não é uma hipótese opcional, nem um adorno metafísico:
é a **condição de possibilidade de qualquer crítica que pretenda ser mais do que ruído**.

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
