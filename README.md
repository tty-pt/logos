### Enquadramento

Nos anos 1920, o problema central da lógica matemática era o **Entscheidungsproblem** (Hilbert/Ackermann): existiria um procedimento mecânico capaz de determinar, para qualquer fórmula lógica, se ela é validamente derivável — ou seja, verdadeira em todos os modelos?

Em 1936, **Church** e **Turing**, por vias distintas, demonstram que tal algoritmo geral **não pode existir**.

A pergunta “**este programa pára ou não pára?**” cristaliza-se mais tarde como o exemplo mais direto — e devastador — desse limite.

O termo **“halting problem”**, na sua formulação moderna, só se estabiliza posteriormente, sendo geralmente atribuído a **Martin Davis** (1958). Estudos históricos mostram que Turing não usou esse nome, nem lhe atribuiu centralidade especial.

### O problema

A formulação de **Strachey** (1965) assemelha-se a este pseudocódigo:

```python
Q(P):
    if halts(P) == true:
        loop_forever()
    else:
        return
```

Aqui, `Q(P)` entra em loop infinito **se e só se** `P` termina. Assim, se `P` termina ao receber `P` como entrada, `Q(P)` não termina. A contradição emerge quando se tenta aplicar `Q` a si mesmo.

Para simplificar, pensemos assim:

Consideremos um procedimento `P` que, dado um argumento, **retorna sempre** um valor binário: **sim** ou **não**.

Definimos então `Q` como a inversão do resultado de `P` aplicado a si mesmo:

```python
Q(P):
    return not P(P)
```

Ou seja, `Q(P)` devolve o **contrário** de `P(P)`.
Se `P(P)` devolve **sim**, então `Q(P)` devolve **não** — e vice-versa.

Mas o que acontece ao aplicarmos `Q` a si próprio?

Isso nos dá:

**Q(Q) = ¬Q(Q)**

Uma proposição que se afirma igual ao seu próprio oposto — o que é logicamente impossível.

Ou seja, a expressão “q = ¬q” é sempre **falsa**.
(Q(Q)) é uma estrutura que se autonega. Implode. A sua própria regra, quando auto-aplicada, destrói o valor que pretendia estabelecer.

Este padrão formal antecipa o que ocorre **no discurso racional**, quando se nega a existência da verdade forte. É uma estrutura que se desfaz ao tentar aplicar-se a si própria.

### Sobre a auto-contradição performativa

Uma **contradição performativa** ocorre quando alguém **afirma** algo cuja estrutura interna **nega** o próprio ato de afirmar.

Por exemplo: ao dizer “**não existe verdade forte**”, a pessoa está implicitamente a apresentar essa afirmação **como se fosse** verdade forte — negando, na forma, o conteúdo que propõe.

É precisamente esse tipo de impasse que Gödel demonstra:
Em qualquer sistema formal suficientemente expressivo, **a auto-avaliação total falha**.

Um sistema não pode ser simultaneamente:

* completo (produz todas as verdades),
* consistente (não gera contradições),
* e auto-validado (fundar-se a si mesmo sem depender de critério externo).

Logo, **o critério de avaliação do sistema tem de estar fora dele**.

### Sobre a impossibilidade de regressão infinita

Pode-se tentar salvar o sistema com um “avaliador externo”.

Mas se esse avaliador, por sua vez, estiver dentro de outro sistema que o valida, o problema reaparece.

Estamos perante uma **cadeia de sistemas**, cada um tentando fundamentar o anterior. Mas isso não resolve: apenas **adiamos indefinidamente** o problema do fundamento.

Se formos consistentes, temos de assumir:

> Para que haja verdade forte, tem de haver um avaliador **exterior a todo e qualquer sistema**.

Mesmo que se defina um “super-sistema” que inclua todos os outros avaliadores, ele ainda é um sistema — e exige critério exterior.

---

### Sujeito no sentido forte

Esse Avaliador é **necessário**, como demonstrado.
Não é contingente. É **pura causa**, e portanto **livre**: nada o condiciona, nada o limita, nada o contém.

É **Sujeito** no sentido forte.

Na lógica formal:

* um **objeto** de avaliação é algo inscrito num sistema;
* um **avaliador** é o que está fora, e estabelece o critério de verdade.

Ao usarmos a palavra *Sujeito*, não falamos de consciência psicológica nem de alguma propriedade emergente de sistemas complexos.

(Essa tese, aliás, seria equivalente a tentar somar números negativos e esperar obter um número positivo por mágica.)

Falamos de Alguém que **realmente merece** o nome de Sujeito:
livre, incondicionado, e **exterior a todos os sistemas**.

### Bom, Pessoal e Relacional

Como fundamento da Verdade e do Valor, este Sujeito é, por definição, **Bom**.

Tudo o que existe fora de Si é **doação**: expressão livre de um Ser necessário.
E se existirem outros sujeitos (como é razoável supor, embora não se prove aqui), então Ele partilha a sua essência com eles — sendo, por isso, também **pessoal** e **relacional**.

Ou seja, a estrutura da Verdade e do Valor conduz, de forma natural, às características tradicionalmente atribuídas a Deus — **sem saltos retóricos, sem apelos emocionais, sem hipóteses ad hoc**.

## Objecções sofisticadas — e porque não resolvem o problema

As objecções mais interessantes a este argumento não são superficiais. Pelo contrário: partem de leituras sérias da lógica, da filosofia da linguagem e da epistemologia contemporânea. Ainda assim, nenhuma consegue evitar a conclusão central. Vejamos porquê.

### 1. “A auto-referência só é problemática em sistemas que exigem totalidade”

Esta objecção reconhece o ponto técnico: a contradição surge quando um sistema pretende **decidir todos os casos**, incluindo os que se aplicam a si próprio. A proposta, então, é abdicar dessa exigência de totalidade.

A resposta é simples e decisiva:
ao abdicar da totalidade, abdica-se precisamente daquilo que está em causa.

Um critério de verdade que falha **em princípio** nos casos-limite não é um critério último. Pode ser útil, operativo, até extremamente poderoso — mas não funda a distinção entre verdadeiro e falso *enquanto tal*. Apenas a gere parcialmente.

Esta objecção é coerente, mas concede o ponto central: **não existe verdade forte auto-fundada dentro de um sistema**.

### 2. “A verdade é definida semanticamente, não decidida formalmente”

Aqui invoca-se a distinção clássica entre verdade semântica e decidibilidade sintáctica, muitas vezes com referência a teorias da verdade hierárquicas (à maneira de Tarski).

Mas o problema não é confundirmos verdade com prova. O problema é outro:
**quem valida a adequação da semântica?**

Uma hierarquia de linguagens evita paradoxos locais, mas não elimina a exigência de um critério último que legitime a hierarquia como um todo. A pergunta reaparece inevitavelmente:

> Por que razão esta estrutura semântica — e não outra — é a que corresponde à verdade?

Enquanto essa pergunta fizer sentido, o sistema não se funda a si próprio. A hierarquia organiza o problema; não o resolve.

### 3. “O fundamento pode ser pragmático ou intersubjectivo”

Segundo esta abordagem, a verdade não exige um avaliador último, mas apenas práticas estáveis de justificação, consenso racional ou sucesso pragmático.

Isto funciona bem para explicar **como usamos** o conceito de verdade. Não explica **o que legitima** esse uso.

Práticas podem divergir, consensos podem falhar, êxitos podem ser ilusórios. Chamar “verdade” ao que resulta dessas dinâmicas é possível — mas apenas se já se pressupõe um critério pelo qual práticas, consensos e êxitos são avaliados como adequados ou inadequados.

Sem esse critério, o termo “verdade” perde força normativa e torna-se descritivo. O argumento não é derrotado; é contornado ao preço de redefinir o conceito.

### 4. “A regressão infinita é aceitável; não precisamos de um ponto final”

Alguns filósofos aceitam regressões infinitas como estruturalmente legítimas. Não há contradição formal em tal regressão.

O problema aqui não é formal, mas fundacional.

Uma cadeia infinita de justificações explica **como algo é sempre justificado por outra coisa**, mas nunca explica **por que razão o conjunto inteiro tem autoridade justificativa**.

Se nenhuma instância da cadeia possui estatuto fundante, então nenhuma a transmite. A regressão pode ser logicamente consistente, mas permanece epistemicamente vazia.

Aceitá-la equivale a aceitar que não há fundamento — o que volta a negar a verdade forte.

### 5. “O avaliador último pode ser uma estrutura impessoal necessária”

Esta é talvez a objecção mais forte. Concede a necessidade de algo extra-sistémico, mas recusa chamá-lo “Sujeito”.

O problema é que uma estrutura impessoal necessária continua a funcionar segundo propriedades fixas. Se essas propriedades são suficientes para fundamentar a verdade, então podem, em princípio, ser formalizadas — e voltamos ao problema da auto-avaliação.

Se não podem ser formalizadas, então já não estamos a falar de uma estrutura no sentido forte, mas de algo que **exerce avaliação sem ser redutível a regras**.

Nesse ponto, a diferença entre “estrutura impessoal” e “avaliador” torna-se nominal. O papel ontológico é o mesmo.

### 6. “Nada disto exige pessoalidade ou relacionalidade”

Correcto: não *exige* no sentido dedutivo estrito.

Mas o argumento não pretende deduzir todas as propriedades do fundamento. Pretende mostrar que:

* o fundamento não é objeto,
* não é sistema,
* não é produto de regras,
* e não é condicionado por nada externo.

Chamar a isso “Sujeito” não é uma metáfora psicológica, mas uma descrição mínima do papel que desempenha. A questão da pessoalidade plena surge depois, como desenvolvimento metafísico — não como premissa escondida.

Conclusão desta secção (revista)

As objecções mais sofisticadas não falham por erro técnico, mas por concessão estrutural. Cada uma tenta preservar a racionalidade local sacrificando algo essencial: totalidade, normatividade, ou fundamento. O que nenhuma consegue fazer é manter, ao mesmo tempo, a prática racional da afirmação e a negação da verdade forte.

Isso é decisivo.

Não é coerente dizer simplesmente que “a verdade não é fundamentável” — porque essa própria afirmação se apresenta como verdadeira em sentido forte. Não é proposta como uma convenção local, um sucesso pragmático ou uma regra provisória, mas como uma descrição correta da realidade racional.

Ou seja:
negar a verdade forte exige aquilo que se pretende negar.

A posição “não existe verdade forte” não é uma alternativa neutra ao argumento; é uma contradição performativa. Ela só pode ser afirmada assumindo, no próprio acto de afirmá-la, um critério de verdade que não reconhece como legítimo.

Assim, o dilema inicial revela-se assimétrico:

Não é possível abandonar a verdade forte sem abandonar a própria inteligibilidade do discurso racional.

Logo, a verdade forte não é opcional; é condição de possibilidade de qualquer afirmação significativa — incluindo as críticas a este argumento.

Uma vez reconhecida a necessidade da verdade forte, o resto segue-se com rigor:

nenhum sistema pode fundamentar totalmente o seu próprio critério de verdade;

nenhuma regressão infinita fornece fundamento;

logo, o critério último da verdade tem de ser extra-sistémico.

Chamar a esse fundamento “Avaliador”, “Fundamento”, ou “Sujeito” não é uma escolha retórica, mas ontológica: trata-se de algo que avalia sem ser avaliado, que funda sem ser fundado, e que não opera segundo regras que lhe sejam externas.

O argumento não força uma teologia.
Mas impede, de forma limpa, a recusa do fundamento.

Depois disso, discordar já não é questão de lógica — é uma decisão metafísica consciente.

# Diagrama lógico
![Diagrama](./diagram.png)
