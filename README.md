# Aquilo que Avalia sem Ser Avaliado

## Enquadramento

Nos anos 1920, um dos problemas centrais da lógica matemática era o **Entscheidungsproblem** (Hilbert/Ackermann): existiria um procedimento mecânico capaz de determinar, para qualquer fórmula lógica, se ela é validamente derivável — isto é, verdadeira em todos os modelos?

Em 1936, **Church** e **Turing**, por vias distintas, mostraram que tal algoritmo geral **não pode existir**.

A pergunta **“este programa pára ou não pára?”** cristaliza-se mais tarde como a formulação paradigmática desse limite, conhecido posteriormente como *halting problem*.

### O problema

Consideremos um procedimento `P` que devolve um valor binário. Definimos `Q` como a inversão do resultado de `P` aplicado a si mesmo:

```python
Q(P):
    return not P(P)
```

O que acontece ao aplicarmos `Q` a si próprio?

Temos:

**Q(Q) = ¬Q(Q)**

Uma proposição que se identifica com a sua negação — uma impossibilidade lógica. O essencial não é o paradoxo em si, mas o padrão estrutural que ele revela. Nenhum sistema pode fundar **a partir de si mesmo** o critério normativo pelo qual é avaliado.

Este padrão reaparece no discurso racional sempre que se tenta negar a **verdade forte**.

Por “verdade forte” entende-se aqui aquilo que conta como correcto independentemente de aceitação, consenso, prática ou sucesso instrumental.

## Sobre a auto-contradição performativa

Há contradição performativa quando o conteúdo de uma afirmação nega o próprio acto de afirmar.

Exemplo: dizer “**não existe verdade forte**” é, na prática, apresentar essa frase **como** verdadeira em sentido forte — sob pena de não haver razão para a tomar como válida.

Trata-se do mesmo impasse estrutural identificado por Gödel: a auto-avaliação total falha.

Gödel não é aqui invocado como teorema técnico estrito, mas como instância paradigmática de um limite estrutural: a impossibilidade de auto-fundação normativa total.

O argumento não depende de incompletude matemática, mas da impossibilidade de auto-legitimação normativa.

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

Mesmo um “super-sistema” continua a exigir critério exterior.

## Definição (Sujeito mínimo)
Chama-se Sujeito qualquer instância que:

1. Exerce avaliação normativa;
2. Não deriva essa autoridade de regra externa;
3. Não está sujeito a avaliação superior;
4. Não é redutível a propriedades, estruturas, leis ou funções formais;

Estas condições não descrevem uma entidade empírica, mas uma função ontológica mínima exigida pela normatividade racional.

### Nota terminológica (sobre “Sujeito”).

O termo Sujeito é aqui usado em sentido estritamente ontológico, não psicológico nem fenomenológico. A sua acepção remete à tradição clássica do ὑποκείμενον (hypokeímenon): aquilo que “jaz por baixo”, o que está sub-posto, o que sustenta e suporta determinações.

Neste sentido original — anterior à reinterpretação moderna de matriz cartesiana — o Sujeito não é primariamente um “eu” representacional ou um centro de consciência, mas aquilo que se encontra na base, como condição de possibilidade da determinação e da atribuição normativa.

A oposição clássica entre subjectum e objectum é ontologicamente assimétrica: o objecto é o que é posto; o sujeito é o que sustenta a própria possibilidade da relação. É apenas neste sentido que o termo Sujeito é usado.

## Objecções sofisticadas — e por que não resolvem

As melhores objecções não são superficiais: assentam em lógica, filosofia da linguagem e epistemologia contemporânea. Ainda assim, nenhuma evita a conclusão central.

### 1) “A auto-referência só é problemática quando se exige totalidade”

Segundo esta objecção, a contradição surge quando o sistema pretende decidir **todos** os casos, incluindo os auto-aplicáveis. Propõe-se, então, renunciar à totalidade.

Mas ao renunciar à totalidade renuncia-se ao que está em causa: um critério último.

Um critério que falha **em princípio** nos casos-limite pode ser útil e poderoso, mas não funda a distinção entre verdadeiro e falso **enquanto tal**; administra-a apenas parcialmente.

Esta objecção é coerente, mas concede o ponto: **não há verdade forte auto-fundada dentro de um sistema**.

### 2) “A verdade é semântica, não decidibilidade formal”

Invoca-se a distinção entre verdade semântica e decidibilidade sintáctica (por exemplo, em moldes tarskianos). Mas o problema não é confundir “verdade” com “prova”.

A pergunta é: **quem legitima a semântica?**

Hierarquias de linguagem evitam paradoxos locais, mas não eliminam a exigência de um critério último que valide a hierarquia como um todo:

> Por que razão esta estrutura semântica — e não outra — corresponde à verdade?

Enquanto esta pergunta fizer sentido, o sistema não se funda a si próprio. A hierarquia organiza o problema; não o encerra.

### 3) “O fundamento pode ser pragmático ou intersubjectivo”

Práticas estáveis, consenso racional ou sucesso pragmático explicam bem **como usamos** “verdade”. Não explicam **o que legitima** esse uso.

Práticas divergem, consensos falham, êxitos iludem. Chamar “verdade” ao que resulta dessas dinâmicas é possível — mas só se já se pressupõe um critério pelo qual essas dinâmicas contam como adequadas ou inadequadas.

Sem esse critério, “verdade” perde força normativa e torna-se descritivo. Essa objecção evita o argumento apenas ao custo de alterar o próprio conceito de verdade.

### 4) “A regressão infinita é aceitável; não precisamos de ponto final”

O problema aqui é fundacional: uma cadeia infinita diz apenas que cada justificação remete para outra, mas nunca explica por que razão o conjunto tem autoridade justificativa.

Se nenhuma instância da cadeia é fundante, nenhuma transmite fundamento. Aceitar a regressão equivale a admitir ausência de fundamento.

### 5) “O avaliador último pode ser uma estrutura impessoal necessária”

Concede-se a exterioridade ao sistema, mas recusa-se o termo “Sujeito”.

Se essa estrutura opera por propriedades fixas suficientes para fundamentar a verdade, então é formalizável — e regressa-se ao problema da auto-avaliação.

Se não é formalizável, então exerce discriminação normativa sem regra externa. Nesse ponto, a recusa de “avaliador” é terminológica, não ontológica.

**Sobre a impossibilidade de normatividade última impessoal:** Uma estrutura impessoal pode transportar normatividade, mas não a pode fundar.

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

### Conclusão desta secção

As objecções mais fortes não falham por erro técnico, mas por concessão estrutural: salvam racionalidade local sacrificando totalidade, normatividade ou fundamento.

Nenhuma consegue manter, simultaneamente, a prática racional da afirmação e a negação da verdade forte.

Dizer “a verdade não é fundamentável” como tese transcontextual já a apresenta como verdadeira em sentido forte. Se não o fizer, abdica-se precisamente da pretensão que se quer manter.

**Princípio de Normatividade Forte:** toda afirmação racional que se apresenta como válida para além de um contexto local pressupõe um critério de verdade que não se reduz a práticas, consensos ou êxitos pragmáticos.

Negar esse princípio não gera uma contradição formal, mas dissolve a própria pretensão de validade racional forte, inclusive para a própria negação.

Assim, o dilema é assimétrico: qualquer afirmação com pretensão transcontextual já pressupõe a distinção normativa entre acerto e erro que não pode ser reduzida a consenso, utilidade ou estabilidade sem perda de sentido.

A verdade forte não é opcional: é condição de possibilidade do discurso com pretensão de correcção — incluindo as críticas a este argumento.

O resultado de Gödel e os esquemas de diagonalização não assinalam apenas um limite epistémico — isto é, do que pode ser provado. Revelam um limite estrutural: o critério último de correcção não pode ser totalmente especificado por meios internos ao sistema que avalia. Trata-se de dependência semântica e normativa, não meramente metodológica.

Nenhuma regressão infinita fornece fundamento. Um critério de verdade é instância de discriminação normativa: determina o que conta como correcto. Quem desempenha esse papel não pode ser puramente descritivo.

Chamar a esse fundamento “Avaliador”, “Fundamento” ou “Sujeito” não é retórica: é a nomeação da função ontológica mínima — avaliar sem ser avaliado, fundar sem ser fundado, sem depender de regra exterior.

O argumento não exige teologia, mas impossibilita uma recusa limpa do fundamento: a partir daqui, a discordância já não é sobre as inferências internas, mas sobre aceitar ou recusar os compromissos ontológicos que a normatividade racional forte exige.

## Princípio de suficiência ontológica mínima

Sempre que uma função explanatória é demonstrada como necessária, a ontologia mínima adequada é aquela que:

(i) é suficiente para desempenhar essa função,

(ii) não introduz entidades ou propriedades redundantes,

(iii) não reintroduz, sob outra forma, o problema que pretende resolver.

No presente caso, a função necessária é clara: fundar a distinção normativa entre verdadeiro e falso sem recorrer a critérios externos ou regras prévias.

Postular um fundamento que:

1. seja objeto,
2. seja estrutura impessoal,
2. ou seja conjunto de propriedades necessárias,

viola o critério (iii), pois cada uma dessas opções exige validação externa ou reincide na formalização que o argumento já descartou.

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
livre, incondicionado e **exterior a todos os sistemas**.

### Bom, Pessoal e Relacional

Se o fundamento da verdade é também o fundamento da normatividade, então não pode ser axiologicamente neutro. A neutralidade já constituiria uma posição normativa entre outras.

Nesse sentido estrito — e apenas nesse — o fundamento identifica-se com o Bem: não como um valor entre outros, mas como a própria condição de possibilidade de toda valoração. Não se trata de uma propriedade acrescentada, mas de uma consequência directa da função já demonstrada: fundar a distinção entre o que conta como correcto e o que não conta.

A partir deste ponto, o argumento não introduz novas premissas lógicas, mas desenvolve consequências ontológicas. Se existirem outros sujeitos finitos (o que é plausível, embora não demonstrado aqui), então a relação entre eles e o fundamento não pode ser necessária nem mecânica. Uma relação necessária seria mera extensão estrutural; uma relação mecânica, simples efeito causal.

Se, pelo contrário, a relação não decorre de necessidade externa, então é livre. Nesse caso, o fundamento não apenas avalia e normatiza, mas estabelece relação sem carência — por plenitude ontológica, não por dependência.

É nesse sentido rigoroso que o fundamento pode ser dito **pessoal** e **relacional**: não por analogia com a psicologia, nem por projecção antropomórfica, mas porque exerce autoridade normativa e estabelece relação sem ser determinado por regras, leis ou estruturas que lhe sejam exteriores.

Assim, a passagem do Sujeito ao Bem, e do Bem à pessoalidade e relacionalidade, não constitui um salto retórico nem uma adição teológica. É o desdobramento mínimo compatível com o papel ontológico já estabelecido.

O que se segue não introduz novas premissas, mas analisa que propriedades são logicamente inevitáveis para qualquer fundamento que desempenhe a função já demonstrada.

## Atributos clássicos.
A prova apresentada não se deixa negar sem abdicação explícita da normatividade racional forte.

Não se trata de teologia, mas de consequência ontológica. O que se segue é o **desdobramento necessário** das propriedades exigidas por um fundamento último da verdade e da normatividade. Cada atributo clássico surge por necessidade lógica decorrente do papel já demonstrado — não por herança doutrinal nem por tradição conceptual.

### 1. Existência necessária

Já foi demonstrado que:

* a verdade forte é inescapável;
* a verdade forte exige avaliação;
* nenhum sistema pode avaliar-se totalmente;
* logo, existe um **fundamento extra-sistémico da verdade**.

Esse fundamento **não pode não existir** sem destruir a própria possibilidade de afirmação verdadeira.

É, portanto, necessário.

'Deus' é aqui um termo de identificação ontológica, não uma premissa teológica.

Existe, assim, necessariamente uma instância que satisfaz exactamente os atributos tradicionalmente designados por ‘Deus’.

### 2. Unicidade

Suponhamos dois fundamentos últimos distintos.

Para serem distintos, teria de haver:

* um critério que os distinguisse, ou
* uma limitação que um não partilha com o outro.

Mas qualquer critério ou limitação exigiria:

* um fundamento superior que os avaliasse.

Contradição.

**Conclusão:** o fundamento último é **único**.

### 3. Simplicidade (não-composto)

Tudo o que é composto:

* depende das suas partes,
* e da regra que as une.

O fundamento último:

* não pode depender de nada,
* nem ser explicado por estrutura interna.

Logo, não é composto, não tem partes, não é agregável.

**Conclusão:** Deus é **simples** (no sentido clássico, não material).

### 4. Aseidade (existência por Si)

Se o fundamento recebesse o ser de outro:

* esse outro seria o verdadeiro fundamento.

Impossível.

**Conclusão:** Deus existe **por Si**, não por causa externa.

### 5. Imutabilidade

Mudança implica:

* passar de potência a acto,
* adquirir o que antes faltava.

Mas o fundamento último:

* não carece de nada,
* não pode tornar-se mais do que é.

**Conclusão:** Deus é **imutável**.

### 6. Eternidade (fora do tempo)

O tempo mede mudança.

Sendo imutável, o fundamento:

* não está no tempo,
* não sofre antes/depois.

**Conclusão:** Deus é **eterno**, não temporalmente infinito, mas **fora do tempo**.

### 7. Onipotência (no sentido rigoroso)

Poder significa:

* capacidade de realizar o possível.

O fundamento:

* não é limitado por nada externo,
* é a condição de possibilidade de toda a realidade.

Não pode fazer o logicamente contraditório — isso não é poder, mas ausência de sentido.

**Conclusão:** Deus é **omnipotente** no sentido clássico e coerente.

### 8. Onisciência

A verdade de qualquer coisa depende, em última instância, do fundamento da verdade.

Logo:

* nada verdadeiro pode ser exterior ao seu conhecimento,
* nada real pode escapar ao seu alcance cognitivo.

**Conclusão:** Deus é **omnisciente**.

### 9. Bondade absoluta

O mal é sempre:

* privação,
* desordem,
* falta de ser.

O fundamento do ser:

* não carece,
* não falha,
* não é deficiente.

Além disso, tudo o que existe fora de Si é **dádiva**, não necessidade.

**Conclusão:** Deus é **o Bem absoluto**.

### 10. Intelecto e vontade (pessoalidade)

O fundamento:

* avalia (intelecto),
* funda normatividade (vontade),
* não opera por regra externa.

Isso **define exactamente o que é agir pessoal**.

Não se trata de psicologia.
Trata-se de **acto livre com conhecimento**.

**Conclusão:** Deus é **pessoal**.

### 11. Relacionalidade

Se existirem outros sujeitos finitos:

* o seu ser deriva do fundamento,
* a relação não é necessária, mas livre.

Logo, a criação é **acto relacional**, não efeito mecânico.

**Conclusão:** Deus **relaciona-se por liberdade**, não por carência.

### 12. Inegabilidade

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

### Conclusão final

O Deus aqui demonstrado não é um "Deus das lacunas". É o fundamento no qual a própria noção de “lacuna explicativa” deixa de ter aplicação, e **condição de possibilidade** da verdade, do valor e da racionalidade.

Por isso:

> Deus, com os atributos clássicos de necessidade, unicidade, simplicidade, eternidade, omnipotência, onisciência, bondade e pessoalidade, **não é apenas demonstrável** — é **racionalmente vinculativo**.

De qualquer forma, o que se mostra aqui não é que a negação de Deus seja logicamente impossível, mas que ela não pode ser sustentada sem custo: obriga à renúncia explícita da verdade forte e da normatividade racional plena.

Nesse sentido preciso — e apenas nesse — o fundamento último não é refutável a partir de dentro do discurso racional que continua a operar com pretensão de validade.

## Forma lógica do argumento

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

Na tradição filosófica, tal instância é denominada Sujeito, não no sentido psicológico, mas no sentido ontológico: a instância que age e avalia sem ser determinada por outra.
```

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
