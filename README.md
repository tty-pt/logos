## Enquadramento

Nos anos 1920, um dos problemas centrais da lógica matemática era o **Entscheidungsproblem** (Hilbert/Ackermann): existiria um procedimento mecânico capaz de determinar, para qualquer fórmula lógica, se ela é validamente derivável — isto é, verdadeira em todos os modelos?

Em 1936, **Church** e **Turing**, por vias distintas, mostraram que tal algoritmo geral **não pode existir**.

A pergunta “**este programa pára ou não pára?**” cristaliza-se mais tarde como o exemplo mais directo — e mais destrutivo — desse limite.

A designação **“halting problem”**, na formulação moderna, estabiliza apenas depois, sendo frequentemente associada a **Martin Davis** (1958). Estudos históricos indicam que Turing não usou essa expressão, nem lhe atribuiu centralidade especial.

## O problema

A formulação de **Strachey** (1965) pode ser representada assim:

```python
Q(P):
    if halts(P) == true:
        loop_forever()
    else:
        return
```

Aqui, `Q(P)` entra em ciclo infinito **se e só se** `P` termina. A tensão surge quando se tenta aplicar `Q` a si próprio.

Para simplificar, consideremos um procedimento `P` que, dado um argumento, devolve sempre um valor binário: **sim** ou **não**.

Definimos `Q` como a inversão do resultado de `P` aplicado a si mesmo:

```python
Q(P):
    return not P(P)
```

Isto é: `Q(P)` devolve o contrário de `P(P)`. Se `P(P)` devolve **sim**, então `Q(P)` devolve **não**; e vice-versa.

O que acontece ao aplicarmos `Q` a si próprio?

Temos:

**Q(Q) = ¬Q(Q)**

Uma proposição que se identifica com a sua negação — o que é logicamente impossível. Em particular, “q = ¬q” é sempre **falsa**.

Trata-se de uma estrutura em que uma regra, ao ser auto-aplicada, destrói o valor que pretende fixar.

Este padrão antecipa o que ocorre no discurso racional quando se nega a **verdade forte**: a posição desfaz-se ao tentar aplicar-se a si própria.

**Verdade forte**: estatuto normativo que distingue acerto real de mera aceitação, independentemente de práticas, consenso ou sucesso instrumental. Não é “verdade” como predicado semântico (“corresponde a um modelo”), mas como **autoridade racional** (“conta como correcto”).

## Sobre a auto-contradição performativa

Há **contradição performativa** quando alguém afirma algo cuja estrutura nega o próprio acto de afirmar.

Exemplo: dizer “**não existe verdade forte**” é, na prática, apresentar essa frase **como** verdadeira em sentido forte — sob pena de não haver razão para a tomar como válida.

É um impasse do mesmo tipo que Gödel torna inevitável em sistemas formais suficientemente expressivos: **a auto-avaliação total falha**.

Um sistema não pode ser simultaneamente:

* **completo** (gerar todas as verdades),
* **consistente** (não gerar contradições),
* e **auto-validado** (fundar-se integralmente a si próprio).

Logo, o critério último de avaliação tem de estar **fora** do sistema.

## Sobre a impossibilidade de regressão infinita

Pode tentar-se salvar o esquema com um “avaliador externo”.

Mas, se esse avaliador estiver integrado noutro sistema que o valida, o problema reaparece. Forma-se uma cadeia de sistemas que se justificam mutuamente, sem produzir fundamento: apenas **adiamento indefinido**.

Se formos consequentes, segue-se:

> Para haver verdade forte, tem de existir um avaliador **exterior a qualquer sistema**.

Mesmo um “super-sistema” que contenha todos os avaliadores continua a ser um sistema — e volta a exigir critério exterior.

## Definição (Sujeito mínimo)
Chama-se Sujeito qualquer instância que:

1. exerce avaliação normativa;
2. não deriva essa autoridade de regra externa;
3. não é objecto de avaliação superior.

### Nota terminológica (sobre “Sujeito”).

O termo Sujeito é aqui usado em sentido estritamente ontológico, não psicológico nem fenomenológico. A sua acepção remete à tradição clássica do ὑποκείμενον (hypokeímenon): aquilo que “jaz por baixo”, o que está sub-posto, o que suporta e padece determinações.

Neste sentido original — anterior à reinterpretação moderna de matriz cartesiana — o Sujeito não é primariamente um “eu” representacional ou um centro de consciência, mas aquilo que se encontra na base, como condição de possibilidade da determinação, da afecção e da atribuição normativa.

A oposição clássica entre subjectum e objectum não designa, assim, dois pólos simétricos, mas uma relação ontológica assimétrica: o objeto é o que é posto diante; o sujeito é o que está por baixo, sustentando e possibilitando a própria relação. É neste sentido — e apenas neste — que o termo Sujeito deve ser entendido ao longo do argumento.

## Objecções sofisticadas — e por que não resolvem

As melhores objecções não são superficiais: assentam em lógica, filosofia da linguagem e epistemologia contemporânea. Ainda assim, nenhuma evita a conclusão central.

### 1) “A auto-referência só é problemática quando se exige totalidade”

Segundo esta objecção, a contradição surge quando o sistema pretende decidir **todos** os casos, incluindo os auto-aplicáveis. Propõe-se, então, renunciar à totalidade.

Mas ao renunciar à totalidade renuncia-se ao que está em causa: um critério último.

Um critério que falha **em princípio** nos casos-limite pode ser útil e poderoso, mas não funda a distinção entre verdadeiro e falso **enquanto tal**; administra-a apenas parcialmente.

Esta objecção é coerente — e concede o ponto: **não há verdade forte auto-fundada dentro de um sistema**.

### 2) “A verdade é semântica, não decidibilidade formal”

Invoca-se a distinção entre verdade semântica e decidibilidade sintáctica (por exemplo, em moldes tarskianos). Mas o problema não é confundir “verdade” com “prova”.

A pergunta é: **quem legitima a semântica?**

Hierarquias de linguagem evitam paradoxos locais, mas não eliminam a exigência de um critério último que valide a hierarquia como um todo:

> Por que razão esta estrutura semântica — e não outra — corresponde à verdade?

Enquanto esta pergunta fizer sentido, o sistema não se funda a si próprio. A hierarquia organiza o problema; não o encerra.

### 3) “O fundamento pode ser pragmático ou intersubjectivo”

Práticas estáveis, consenso racional ou sucesso pragmático explicam bem **como usamos** “verdade”. Não explicam **o que legitima** esse uso.

Práticas divergem, consensos falham, êxitos iludem. Chamar “verdade” ao que resulta dessas dinâmicas é possível — mas só se já se pressupõe um critério pelo qual essas dinâmicas contam como adequadas ou inadequadas.

Sem esse critério, “verdade” perde força normativa e torna-se descritivo. A objecção contorna o argumento ao preço de redefinir o conceito.

### 4) “A regressão infinita é aceitável; não precisamos de ponto final”

Uma regressão infinita pode ser formalmente consistente.

O problema aqui é fundacional: uma cadeia infinita diz apenas que cada justificação remete para outra, mas nunca explica por que razão o conjunto tem autoridade justificativa.

Se nenhuma instância da cadeia é fundante, nenhuma transmite fundamento. Aceitar a regressão equivale a aceitar ausência de fundamento — o que volta a negar a verdade forte.

### 5) “O avaliador último pode ser uma estrutura impessoal necessária”

Concede-se a exterioridade ao sistema, mas recusa-se o termo “Sujeito”.

Se essa estrutura opera por propriedades fixas suficientes para fundamentar a verdade, então é formalizável — e regressa-se ao problema da auto-avaliação.

Se não é formalizável, então exerce discriminação normativa sem regra externa. Nesse ponto, a recusa de “avaliador” é terminológica, não ontológica.

#### Sobre a impossibilidade de normatividade última impessoal

Um critério último não apenas classifica: **confere autoridade**. Distinguir correcto/incorreto não é descrição; é validação.

Para exercer essa função, é preciso:

1. **discriminação não derivada** (sem regra superior, sob pena de regressão);
2. **autoridade não herdada** (sem fundamento anterior).

Uma “estrutura impessoal” opera por propriedades fixas. Mas propriedades só são normativas se **contarem** como normativas — e isso já pressupõe um acto avaliativo.

Logo, uma estrutura impessoal pode transportar normatividade, mas não a pode fundar. Fundar normatividade implica um acto originário de validação que não decorre de regras — mas as institui.

Chamar-lhe “Sujeito” não acrescenta psicologia nem teologia: nomeia apenas a função mínima já exigida.

### 6) “Nada disto exige pessoalidade ou relacionalidade”

Não exige no sentido dedutivo estrito.

O argumento não pretende derivar todas as propriedades do fundamento; pretende mostrar que ele não é:

* objecto,
* sistema,
* produto de regras,
* nem condicionado por algo externo.

Até aqui a conclusão é negativa. “Sujeito” surge como identificação ontológica mínima compatível com o papel demonstrado: avaliar sem ser avaliado, fundar sem ser fundado.

### 7) “A normatividade é um facto bruto”

Um facto bruto pode descrever regularidades; não institui autoridade.

Um “facto” só é normativo se **contar como razão**. “Contar como razão” não é descritivo; é estatuto conferido.

Se a normatividade fosse facto bruto:

* ou vinculava (exigindo critério de validade),
* ou não vinculava (deixando de ser normatividade).

Portanto, “facto normativo bruto” é uma confusão categorial: ou é bruto e não normativo, ou normativo e não bruto.

## Conclusão desta secção

As objecções mais fortes não falham por erro técnico, mas por concessão estrutural: salvam racionalidade local sacrificando totalidade, normatividade ou fundamento.

Nenhuma consegue manter, simultaneamente, a prática racional da afirmação e a negação da verdade forte.

Não é coerente dizer simplesmente “a verdade não é fundamentável” como tese transcontextual, porque isso se apresenta como verdadeiro em sentido forte. Se não o fizer, abdica-se precisamente da pretensão que se quer manter.

**Princípio de Normatividade Forte:** toda afirmação racional que se apresenta como válida para além de um contexto local pressupõe um critério de verdade que não depende apenas de práticas, consenso ou sucesso pragmático.

Negar este princípio não gera contradição formal; dissolve a pretensão de validade racional forte, inclusive para a própria negação.

Assim, o dilema é assimétrico: qualquer afirmação com pretensão transcontextual já pressupõe a distinção normativa entre acerto e erro que não pode ser reduzida a consenso, utilidade ou estabilidade sem perda de sentido.

A verdade forte não é opcional: é condição de possibilidade do discurso com pretensão de correcção — incluindo as críticas a este argumento.

O resultado de Gödel e os esquemas de diagonalização não assinalam apenas um limite epistémico — isto é, do que pode ser provado. Revelam um limite estrutural: o critério último de correcção não pode ser totalmente especificado por meios internos ao sistema que avalia. Trata-se de dependência semântica e normativa, não meramente metodológica.

Nenhuma regressão infinita fornece fundamento. Um critério de verdade é instância de discriminação normativa: determina o que conta como correcto. Quem desempenha esse papel não pode ser puramente descritivo.

Chamar a esse fundamento “Avaliador”, “Fundamento” ou “Sujeito” não é retórica: é a nomeação da função ontológica mínima — avaliar sem ser avaliado, fundar sem ser fundado, sem operar por regra exterior.

O argumento não impõe teologia, mas impede uma recusa limpa do fundamento: a partir daqui, a discordância já não é sobre as inferências internas, mas sobre aceitar ou recusar os compromissos ontológicos que a normatividade racional forte exige.

# Princípio de suficiência ontológica mínima

Sempre que uma função explanatória é demonstrada como necessária, a ontologia mínima adequada é aquela que:

(i) é suficiente para desempenhar essa função,

(ii) não introduz entidades ou propriedades redundantes,

(iii) não reintroduz, sob outra forma, o problema que pretende resolver.

No presente caso, a função necessária é clara: fundar a distinção normativa entre verdadeiro e falso sem recorrer a critérios externos ou regras prévias.

Postular um fundamento que:

seja objeto,

seja estrutura impessoal,

ou seja conjunto de propriedades necessárias,

falha o critério (iii), pois cada uma dessas opções ou exige validação externa ou reincide na formalização que o argumento já excluiu.

A identificação do fundamento como Sujeito não acrescenta propriedades supérfluas; pelo contrário, remove todas as que se revelaram insuficientes. Trata-se, portanto, não de um enriquecimento metafísico, mas de uma redução ontológica orientada pela função.

À luz deste princípio, resta agora identificar que tipo de entidade satisfaz minimamente essas condições sem reintroduzir os problemas já excluídos.

### Sujeito no sentido forte

Esse Avaliador é **necessário**, como demonstrado.
Não é condicionado por nada externo e, nesse sentido rigoroso, é livre.

É **Sujeito** no sentido forte.

Na lógica formal:

* um **objeto** de avaliação é algo inscrito num sistema;
* um **avaliador** é o que está fora, e estabelece o critério de verdade.

Ao usarmos a palavra *Sujeito*, não falamos de consciência psicológica nem de alguma propriedade emergente de sistemas complexos.

(Essa tese, aliás, seria equivalente a tentar somar números negativos e esperar obter um número positivo por mágica.)

Falamos de Alguém que **realmente merece** o nome de Sujeito:
livre, incondicionado, e **exterior a todos os sistemas**.

### Bom, Pessoal e Relacional

Se o fundamento da verdade é também o fundamento da normatividade, então não pode ser axiologicamente neutro. A neutralidade já constituiria uma posição normativa entre outras.

Nesse sentido estrito — e apenas nesse — o fundamento identifica-se com o Bem: não como um valor entre valores, mas como a condição de possibilidade de qualquer valoração. Não se trata de uma propriedade acrescentada, mas de uma consequência directa da função já demonstrada: fundar a distinção entre o que conta como correcto e o que não conta.

A partir deste ponto, o argumento não introduz novas premissas lógicas, mas desenvolve consequências ontológicas. Se existirem outros sujeitos finitos (o que é plausível, embora não demonstrado aqui), então a relação entre eles e o fundamento não pode ser necessária nem mecânica. Uma relação necessária seria mera extensão estrutural; uma relação mecânica, simples efeito causal.

Se, pelo contrário, a relação não é imposta por necessidade externa, então é livre. Nesse caso, o fundamento não apenas avalia e normatiza, mas estabelece relação sem carência — por excesso ontológico, não por dependência.

É nesse sentido rigoroso que o fundamento pode ser dito **pessoal** e **relacional**: não por analogia psicológica, nem por projecção antropomórfica, mas porque exerce autoridade normativa e estabelece relação sem ser determinado por regras, leis ou estruturas que lhe sejam exteriores.

Assim, a passagem do Sujeito ao Bem, e do Bem à pessoalidade e relacionalidade, não constitui um salto retórico nem uma adição teológica. É o desdobramento mínimo compatível com o papel ontológico já estabelecido.

# Atributos clássicos.
A prova apresentada não se deixa negar sem abdicação explícita da normatividade racional forte.

Não se trata de um salto teológico nem de uma redefinição oportunista de 'Deus' (entendido aqui como o fundamento último da verdade e da normatividade). O que se segue é o **desdobramento necessário** das propriedades exigidas por um fundamento último da verdade e da normatividade. Cada atributo clássico surge por necessidade lógica decorrente do papel já demonstrado — não por herança doutrinal nem por tradição conceptual.

## 1. Existência necessária

Já foi demonstrado que:

* a verdade forte é inescapável;
* a verdade forte exige avaliação;
* nenhum sistema pode avaliar-se totalmente;
* logo, existe um **fundamento extra-sistémico da verdade**.

Esse fundamento **não pode não existir** sem destruir a própria possibilidade de afirmação verdadeira.

Não é, portanto, contingente.

Existe, assim, necessariamente uma instância que satisfaz exactamente os atributos tradicionalmente designados por ‘Deus’.

## 2. Unicidade

Suponhamos dois fundamentos últimos distintos.

Para serem distintos, teria de haver:

* um critério que os distinguisse, ou
* uma limitação que um não partilha com o outro.

Mas qualquer critério ou limitação exigiria:

* um fundamento superior que os avaliasse.

Contradição.

**Conclusão:** o fundamento último é **único**.

## 3. Simplicidade (não-composto)

Tudo o que é composto:

* depende das suas partes,
* e da regra que as une.

O fundamento último:

* não pode depender de nada,
* nem ser explicado por estrutura interna.

Logo, não é composto, não tem partes, não é agregável.

**Conclusão:** Deus é **simples** (no sentido clássico, não material).

## 4. Aseidade (existência por Si)

Se o fundamento recebesse o ser de outro:

* esse outro seria o verdadeiro fundamento.

Impossível.

**Conclusão:** Deus existe **por Si**, não por causa externa.

## 5. Imutabilidade

Mudança implica:

* passar de potência a acto,
* adquirir o que antes faltava.

Mas o fundamento último:

* não carece de nada,
* não pode tornar-se mais do que é.

**Conclusão:** Deus é **imutável**.

## 6. Eternidade (fora do tempo)

O tempo mede mudança.

Sendo imutável, o fundamento:

* não está no tempo,
* não sofre antes/depois.

**Conclusão:** Deus é **eterno**, não temporalmente infinito, mas **fora do tempo**.

## 7. Onipotência (no sentido rigoroso)

Poder significa:

* capacidade de realizar o possível.

O fundamento:

* não é limitado por nada externo,
* é a condição de possibilidade de toda a realidade.

Não pode fazer o logicamente contraditório — isso não é poder, é destituído de sentido.

**Conclusão:** Deus é **omnipotente** no sentido clássico e coerente.

## 8. Onisciência

A verdade de qualquer coisa depende, em última instância, do fundamento da verdade.

Logo:

* nada verdadeiro pode ser exterior ao seu conhecimento,
* nada real pode escapar ao seu alcance cognitivo.

**Conclusão:** Deus é **onisciente**.

## 9. Bondade absoluta

O mal é sempre:

* privação,
* desordem,
* falta de ser.

O fundamento do ser:

* não carece,
* não falha,
* não é deficiente.

Além disso, tudo o que existe fora de Si é **doação**, não necessidade.

**Conclusão:** Deus é **o Bem absoluto**.

## 10. Intelecto e vontade (pessoalidade)

O fundamento:

* avalia (intelecto),
* funda normatividade (vontade),
* não opera por regra externa.

Isso é exactamente o que define **agir pessoal**, não mecânico.

Não se trata de psicologia.
Trata-se de **acto livre com conhecimento**.

**Conclusão:** Deus é **pessoal**.

## 11. Relacionalidade

Se existirem outros sujeitos finitos:

* o seu ser deriva do fundamento,
* a relação não é necessária, mas livre.

Logo, a criação é **acto relacional**, não efeito mecânico.

**Conclusão:** Deus é **relacional por liberdade**, não por carência.

## 12. Inegabilidade

Negar este Deus implica uma das seguintes opções:

1. Negar verdade forte
   → contradição performativa.

2. Aceitar verdade sem fundamento
   → colapso normativo.

3. Aceitar fundamento impessoal formalizável
   → regressão ao problema da auto-avaliação.

4. Aceitar regressão infinita
   → ausência total de fundamento.

Nenhuma preserva discurso racional pleno.

## Conclusão final

O Deus aqui demonstrado não é:

* uma hipótese,
* uma explicação concorrente,
* um “Deus das lacunas”.

É **condição de possibilidade** da verdade, do valor e da racionalidade.

Por isso:

> Deus, com os atributos clássicos de necessidade, unicidade, simplicidade, eternidade, omnipotência, onisciência, bondade e pessoalidade, **não é apenas demonstrável** — é **extremamente convincente**.

De qualquer forma, o que se mostra aqui não é que a negação de Deus seja logicamente impossível, mas que ela não pode ser mantida sem custo: exige a renúncia explícita à verdade forte e à normatividade racional plena.

Nesse sentido preciso — e apenas nesse — o fundamento último não é refutável a partir de dentro do discurso racional que continua a operar com pretensões de verdade.

A partir deste ponto, a discordância já não incide sobre inferências lógicas, mas sobre a disposição de assumir ou não os compromissos ontológicos exigidos pela normatividade racional forte.

# Forma lógica do argumento

```
Se:
existe verdade forte;
verdade forte exige critério último;
nenhum sistema formal pode fornecer tal critério;

então:
existe um fundamento extra-sistémico da verdade.

Se, adicionalmente:
4. esse fundamento não opera por regras externas;

então:
Resta, então, um tipo de instância que exerce avaliação sem ser regida por critérios externos — isto é, uma fonte originária de normatividade.

Na tradição filosófica, tal instância é denominada Sujeito, não no sentido psicológico, mas no sentido ontológico: aquilo que age e avalia sem ser previamente determinado.
```

# Pensamentos para fechar

1. Se algo é **Lei**, é formalizável e, por isso, recai no limite demonstrado por Gödel.

2. Se for **mecânico**, é um sistema e, como tal, exige avaliador externo.

3. Se é a **Origem da Norma**, deve ser um **Ato**.

Na filosofia da linguagem, isso nos remete ao conceito de ilocução: a verdade não é apenas um estado de coisas, é um "crer" ou um "dizer" que algo é o caso. Se o fundamento da verdade opera essa distinção sem ser compelido por uma regra anterior, ele está exercendo **Liberdade**.

Não é à toa que se usa a palavra **Verbo** para O descrever.

O argumento não pretende provar a existência de Deus a partir de premissas teológicas, mas mostrar que a negação de um fundamento último da normatividade racional tem custos conceptuais que devem ser assumidos explicitamente.

# Diagrama lógico
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
    C -->|Distinção Verdadeiro/Falso| D[Sistemas Lógicos são Fechados]
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
