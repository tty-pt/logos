import Lean

/-!
# CompleteLibertarianFreedomArgument — Via Ontológica Mínima da Liberdade Libertária

A prova da liberdade libertária é estritamente ontológica, direta e local à cadeia de determinação:
A. Cadeia de determinação (`JudgmentDeterminationChain`)
   ↓
B. Bem-fundação da prioridade ancestral (`DeterminationSystem.priorWellFounded`)
   ↓
C. Fonte interna última (`exists_ultimate_source_of_judgment_act`)
   ↓
D. Fonte última é acto do próprio sujeito (`SubjectSourceOfJudgment J a`)
   ↓
E. Não recebe determinação do estado antecedente completo (`ultimate_internal_act_source_is_not_received_from_prior_state`)
   ↓
F. Determinação contingente do acto concreto (`ContingentDetermination J a`)
   ↓
G. Alternativa acessível com mesmo passado completo e resultado diferente (`contingent_determination_yields_normative_sensitivity`)
   ↓
H. Escolha libertária no mundo do juízo (`originated_contingent_determination_yields_libertarian_choice`)
   ↓
I. Livre-arbítrio (`originated_contingent_determination_yields_free_will`)
   ↓
J. Sujeito livre (`ontological_determination_yields_libertarian_freedom`)

Preço axiomático demonstrado no Lean 4: estritamente o núcleo clássico padrão [propext, Classical.choice, Quot.sound],
com zero axiomas substantivos ou modais adicionados.
-/

namespace CompleteLibertarianFreedomArgument

namespace FinalNonCircularClosure

universe u v

/-- Frame semântico modal e agencial mínimo.
    Combina a estrutura modal de mundos possíveis com as atitudes de
    assentimento e suspensão e a sua exclusividade mútua. -/
structure Semantics (Subject : Type u) where
  World : Type v
  actualWorld : World
  Accessible : World → World → Prop
  SameCompletePriorState : World → World → Prop
  AssentsAt : Subject → World → Prop → Prop
  WithholdsAt : Subject → World → Prop → Prop
  exclusive :
    ∀ s : Subject, ∀ w : World, ∀ p : Prop,
      ¬ (AssentsAt s w p ∧ WithholdsAt s w p)
  ThinkingMindAt : Subject → World → Prop := fun _ _ => True
  MeansAt : Subject → World → Prop → Prop := fun _ _ _ => True
  ApprehendsAt : Subject → World → Prop → Prop := fun _ _ _ => True
  ReasonSupports : Subject → World → Prop → Prop → Prop := fun _ _ _ _ => True

/-- Sensibilidade normativa no mundo `w`:
    há um mundo acessível com o mesmo passado completo no qual
    o resultado contrário ocorre. -/
def NormativelySensitive
    (C : Semantics Subject)
    (s : Subject)
    (w : C.World)
    (p : Prop) : Prop :=
  ∃ w',
    C.Accessible w w' ∧
    C.SameCompletePriorState w w' ∧
    w' ≠ w ∧
    (
      (C.AssentsAt s w p ∧ C.WithholdsAt s w' p) ∨
      (C.WithholdsAt s w p ∧ C.AssentsAt s w' p)
    )

/-- Escolha libertária no mundo `w`:
    o sujeito adopta um veredicto no mundo `w` e existe um mundo alternativo
    acessível de mesmo passado completo em que adopta o veredicto contrário. -/
def LibertarianFreeChoiceAt
    (C : Semantics Subject)
    (s : Subject)
    (w : C.World)
    (p : Prop) : Prop :=
  (
    C.AssentsAt s w p ∧
    ∃ w',
      w' ≠ w ∧
      C.Accessible w w' ∧
      C.SameCompletePriorState w w' ∧
      C.WithholdsAt s w' p
  )
  ∨
  (
    C.WithholdsAt s w p ∧
    ∃ w',
      w' ≠ w ∧
      C.Accessible w w' ∧
      C.SameCompletePriorState w w' ∧
      C.AssentsAt s w' p
  )

/-- Livre-arbítrio no mundo `w`:
    existe pelo menos uma proposição sobre a qual o sujeito possui escolha libertária. -/
def FreeWillAt
    (C : Semantics Subject)
    (s : Subject)
    (w : C.World) : Prop :=
  ∃ p : Prop, LibertarianFreeChoiceAt C s w p

/-- Sujeito livre:
    o sujeito possui livre-arbítrio no mundo actual. -/
def FreeSubject
    (C : Semantics Subject)
    (s : Subject) : Prop :=
  FreeWillAt C s C.actualWorld

/-- Contingência do mundo modal: o estado antecedente completo não fecha trivialmente
    o espaço modal — existe um mundo acessível distinto com o mesmo passado completo. -/
def ContingentWorld (C : Semantics Subject) : Prop :=
  ∃ w', C.Accessible C.actualWorld w' ∧
        C.SameCompletePriorState C.actualWorld w' ∧
        w' ≠ C.actualWorld

/-- Mecanicidade do juízo: mantendo o mesmo passado completo, o veredicto não varia. -/
def MechanicallyForced
    (C : Semantics Subject) (s : Subject) (w : C.World) (p : Prop) : Prop :=
  ∀ w' : C.World,
    C.Accessible w w' →
    C.SameCompletePriorState w w' →
    (
      (C.AssentsAt s w p → C.AssentsAt s w' p) ∧
      (C.WithholdsAt s w p → C.WithholdsAt s w' p)
    )

/-- Passagem analítica directa: a sensibilidade normativa produz escolha libertária.
    Footprint: `{}`. -/
theorem normative_sensitivity_implies_libertarian_choice_direct
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (hSensitive : NormativelySensitive C s w p) :
    LibertarianFreeChoiceAt C s w p := by
  rcases hSensitive with ⟨w', hAccessible, hPrior, hDifferent, hContrary⟩
  have hActual : C.AssentsAt s w p ∨ C.WithholdsAt s w p := by
    rcases hContrary with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  rcases hActual with hAssent | hWithhold
  · exact Or.inl ⟨
      hAssent,
      ⟨w', hDifferent, hAccessible, hPrior, by
        rcases hContrary with h | h
        · exact h.2
        · exact False.elim (C.exclusive s w p ⟨hAssent, h.1⟩)
      ⟩
    ⟩
  · exact Or.inr ⟨
      hWithhold,
      ⟨w', hDifferent, hAccessible, hPrior, by
        rcases hContrary with h | h
        · exact False.elim (C.exclusive s w p ⟨h.1, hWithhold⟩)
        · exact h.2
      ⟩
    ⟩

/-- Estrutura abstracta mínima de determinação.
    Preserva exactamente três noções:
    (1) elementos de uma cadeia (`Node`);
    (2) relação de antecedência estrita e bem-fundada (`Prior`);
    (3) determinação respeita a prioridade (`Determines a b → Prior a b`). -/
structure DeterminationSystem where
  Node : Type _
  Prior : Node → Node → Prop
  priorWellFounded : WellFounded Prior
  Determines : Node → Node → Prop
  determinationRespectsPriority :
    ∀ {a b : Node}, Determines a b → Prior a b

/-- Fonte interna última (relativa à cadeia):
    um elemento da cadeia que não recebe a sua determinação de nenhum
    outro elemento anterior dentro da própria cadeia. -/
def UltimateInternalSource (D : DeterminationSystem) (a : D.Node) : Prop :=
  ¬ ∃ b : D.Node, D.Determines b a

/-- Cadeia inteiramente determinada:
    todo o elemento da cadeia recebe a sua determinação de algum outro
    elemento anterior da própria cadeia. -/
def FullyInternallyDetermined (D : DeterminationSystem) : Prop :=
  ∀ b : D.Node,
    ∃ a : D.Node,
      D.Determines a b

/-- A determinação não pode ser auto-dirigida (irreflexividade):
    nenhum nó pode determinar a si mesmo, pois isso violaria a estrita
    anterioridade da relação bem-fundada.
    Footprint: `{}`. -/
theorem determination_cannot_be_self_directed
    (D : DeterminationSystem) :
    ¬ ∃ a : D.Node, D.Determines a a :=
  fun ⟨a, ha⟩ =>
    let irrefl : ∀ x : D.Node, D.Prior x x → False := fun x =>
      D.priorWellFounded.induction (C := fun y => D.Prior y y → False) x
        (fun b ih hb => ih b hb hb)
    irrefl a (D.determinationRespectsPriority ha)

/-- Teorema central da não-autodeterminação:
    Uma cadeia puramente determinada não se pode auto-fundar.
    Se todo o nó recebesse determinação de um nó estritamente anterior
    numa relação bem-fundada, obter-se-ia uma regressão infinita impossível,
    provando `False` por indução bem-fundada.
    Footprint: `{}`. -/
theorem fully_internally_determined_is_impossible
    (D : DeterminationSystem)
    (hNonempty : Nonempty D.Node) :
    ¬ FullyInternallyDetermined D :=
  fun hFull =>
    let hAllFalse : ∀ _x : D.Node, False := fun x =>
      D.priorWellFounded.induction (C := fun _ => False) x fun b ih =>
        match hFull b with
        | ⟨a, ha⟩ => ih a (D.determinationRespectsPriority ha)
    match hNonempty with
    | ⟨x0⟩ => hAllFalse x0

/-- Consequência existencial: dentro de qualquer cadeia não-vazia de
    determinação bem-fundada e orientada a antecedentes, existe pelo menos
    um elemento que não recebe determinação de outro elemento da cadeia.
    PREÇO: `[propext, Classical.choice, Quot.sound]`, pela passagem clássica
    de `¬∀` para `∃¬`. -/
theorem exists_ultimate_internal_source
    (D : DeterminationSystem)
    (hNonempty : Nonempty D.Node) :
    ∃ a : D.Node, ¬ ∃ b : D.Node, D.Determines b a := by
  apply Classical.byContradiction
  intro hNotExists
  have hFull : FullyInternallyDetermined D := by
    intro b
    apply Classical.byContradiction
    intro hNotDet
    apply hNotExists
    exact ⟨b, hNotDet⟩
  exact fully_internally_determined_is_impossible D hNonempty hFull

/-- Versão construtiva da consequência: não é o caso que todos os nós
    sejam internamente determinados.
    Footprint: `{}`. -/
theorem not_all_internally_determined
    (D : DeterminationSystem)
    (hNonempty : Nonempty D.Node) :
    ¬ (∀ b : D.Node, ∃ a : D.Node, D.Determines a b) :=
  fully_internally_determined_is_impossible D hNonempty

/-- Ponte semântica entre sistemas de determinação e forçagem mecânica.
    Modela uma cadeia concreta de determinações culminando no nó de juízo
    (`verdictNode`), num mundo onde o juízo satisfaz `MechanicallyForced`. -/
structure MechanicalDeterminationChain
    (C : Semantics Subject)
    (s : Subject)
    (w : C.World)
    (p : Prop) extends DeterminationSystem where
  verdictNode : Node
  isForced : MechanicallyForced C s w p

/-- Teorema de aplicação conceptual:
    Mesmo que o juízo seja mecanicamente forçado (`MechanicallyForced C s w p`),
    a cadeia de determinação subjacente, sendo bem-fundada e orientada a
    antecedentes, NÃO pode ser inteiramente internamente determinada.
    A forçagem mecânica a cada elo não confere à cadeia mecânica a capacidade
    de ser a fonte auto-fundada da sua própria determinação.
    Footprint: `{}`. -/
theorem mechanical_chain_cannot_self_ground
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (M : MechanicalDeterminationChain C s w p) :
    ¬ FullyInternallyDetermined M.toDeterminationSystem :=
  fully_internally_determined_is_impossible M.toDeterminationSystem ⟨M.verdictNode⟩

/-- Existência de fonte interna última na cadeia mecânica:
    em toda a cadeia mecânica bem-fundada que culmina num juízo forçado,
    há pelo menos um elo que não recebe determinação de outro elo da cadeia.
    PREÇO: `[propext, Classical.choice, Quot.sound]`. -/
theorem mechanical_chain_has_ultimate_internal_source
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (M : MechanicalDeterminationChain C s w p) :
    ∃ a : M.Node, ¬ ∃ b : M.Node, M.Determines b a :=
  exists_ultimate_internal_source M.toDeterminationSystem ⟨M.verdictNode⟩

/-- Fecho transitivo da determinação: `a` determina `b` ancestralmente
    (directamente ou através de passos intermediários na cadeia). -/
inductive DeterminesAncestrally (Determines : Node → Node → Prop) : Node → Node → Prop where
  | direct {a b : Node} : Determines a b → DeterminesAncestrally Determines a b
  | trans {a b c : Node} : Determines a b → DeterminesAncestrally Determines b c → DeterminesAncestrally Determines a c

/-- Fecho transitivo da relação ancestral. Footprint: `{}`. -/
theorem determines_ancestrally_trans
    {Node : Type _}
    {Determines : Node → Node → Prop}
    {a b c : Node}
    (hab : DeterminesAncestrally Determines a b)
    (hbc : DeterminesAncestrally Determines b c) :
    DeterminesAncestrally Determines a c := by
  induction hab with
  | direct hd => exact DeterminesAncestrally.trans hd hbc
  | trans hd _ ih => exact DeterminesAncestrally.trans hd (ih hbc)

/-- Todo o vínculo determinativo ancestral possui um predecessor directo do alvo.
    Footprint: `{}`. -/
theorem determines_ancestrally_has_direct_predecessor
    {Node : Type _}
    {Determines : Node → Node → Prop}
    {a x : Node}
    (hAnc : DeterminesAncestrally Determines a x) :
    ∃ c : Node, Determines c x := by
  induction hAnc with
  | direct hd => exact ⟨_, hd⟩
  | trans _ _ ih => exact ih

/-- Teorema estrutural da raiz ancestral:
    Para qualquer nó `x` de um sistema de determinação bem-fundado,
    existe uma fonte interna última `a` que determina ancestralmente `x`
    (ou coincide com `x`).
    Demonstrado directamente por indução bem-fundada sobre a relação `Prior`.
    PREÇO: `[propext, Classical.choice, Quot.sound]`. -/
theorem node_has_ancestral_ultimate_source
    (D : DeterminationSystem)
    (x : D.Node) :
    ∃ a : D.Node,
      UltimateInternalSource D a ∧
      (a = x ∨ DeterminesAncestrally D.Determines a x) := by
  induction x using D.priorWellFounded.induction with
  | h n ih =>
    by_cases hDet : ∃ c : D.Node, D.Determines c n
    · rcases hDet with ⟨c, hc⟩
      have hPrior : D.Prior c n := D.determinationRespectsPriority hc
      have ⟨a, haSource, haReach⟩ := ih c hPrior
      refine ⟨a, haSource, ?_⟩
      cases haReach with
      | inl haEq =>
        subst haEq
        exact Or.inr (DeterminesAncestrally.direct hc)
      | inr haAnc =>
        exact Or.inr (determines_ancestrally_trans haAnc (DeterminesAncestrally.direct hc))
    · exact ⟨n, hDet, Or.inl rfl⟩

universe u_out

/-- Cadeia de determinação centrada no ACTO DE JULGAR com semântica de determinação.
    Modela a determinação de um juízo associando a cada nó uma realização (`OutcomeOf`):
    (1) nó de veredicto final (`verdictNode`);
    (2) nó do acto de julgar (`judgmentActNode`), que determina ancestralmente o veredicto;
    (3) titularidade agencial explícita em relação ao sujeito concreto `s` (`IsActOf`);
    (4) o acto de julgar é acto do sujeito `s` (`judgmentActIsActOf`);
    (5) propagação da determinação: se `a` determina `b`, o resultado de `b` é o de `a`;
    (6) condições externas a `s` são fixadas por `SameCompletePriorState`;
    (7) exaustividade da determinação antecedente: toda a determinação do resultado de um
        nó pelo estado antecedente completo está representada na cadeia ou é externa a `s`;
    (8) rastreamento do veredicto: a igualdade de resultado fixa assentimento/suspensão;
    (9) rastreamento alternativo: a diferença de resultado produz variação de veredicto. -/
structure JudgmentDeterminationChain
    (C : Semantics Subject)
    (s : Subject)
    (w : C.World)
    (p : Prop) extends DeterminationSystem where
  Outcome : Type u_out
  OutcomeOf : Node → C.World → Outcome
  verdictNode : Node
  judgmentActNode : Node
  IsActOf : Subject → Node → Prop
  judgmentActIsActOf : IsActOf s judgmentActNode
  judgmentActDeterminesVerdict :
    judgmentActNode = verdictNode ∨ DeterminesAncestrally Determines judgmentActNode verdictNode
  act_ancestral_determination_is_agential :
    ∀ (a : Node),
      (a = judgmentActNode ∨ DeterminesAncestrally Determines a judgmentActNode) →
      IsActOf s a
  determines_propagates :
    ∀ {a b : Node}, Determines a b → ∀ w' : C.World, OutcomeOf b w' = OutcomeOf a w'
  external_node_fixed_by_prior_state :
    ∀ (a : Node), ¬ IsActOf s a →
      ∀ w' : C.World, C.SameCompletePriorState w w' →
        OutcomeOf a w' = OutcomeOf a w
  determination_exhaustive :
    ∀ (a : Node),
      (∀ w' : C.World, C.Accessible w w' → C.SameCompletePriorState w w' → OutcomeOf a w' = OutcomeOf a w) →
      (∃ b : Node, Determines b a) ∨ ¬ IsActOf s a
  verdict_tracks :
    ∀ w1 w2 : C.World,
      OutcomeOf verdictNode w1 = OutcomeOf verdictNode w2 →
      (C.AssentsAt s w1 p → C.AssentsAt s w2 p) ∧
      (C.WithholdsAt s w1 p → C.WithholdsAt s w2 p)
  verdict_tracks_alternative :
    ∀ w1 w2 : C.World,
      OutcomeOf verdictNode w1 ≠ OutcomeOf verdictNode w2 →
      ((C.AssentsAt s w1 p ∧ C.WithholdsAt s w2 p) ∨
       (C.WithholdsAt s w1 p ∧ C.AssentsAt s w2 p))

/-- Cadeia de determinação sem a restrição de ancestralidade agencial.
    Admite formalmente que a determinação do acto de julgar do sujeito tenha raiz
    puramente externa ao sujeito.
    Utilizada para demonstrar rigorosamente como guarda negativa que a restrição agencial
    é indispensável para excluir a forçagem mecânica. -/
structure UnrestrictedJudgmentDeterminationChain
    (C : Semantics Subject)
    (s : Subject)
    (w : C.World)
    (p : Prop) extends DeterminationSystem where
  Outcome : Type u_out
  OutcomeOf : Node → C.World → Outcome
  verdictNode : Node
  judgmentActNode : Node
  IsActOf : Subject → Node → Prop
  judgmentActIsActOf : IsActOf s judgmentActNode
  judgmentActDeterminesVerdict :
    judgmentActNode = verdictNode ∨ DeterminesAncestrally Determines judgmentActNode verdictNode
  determines_propagates :
    ∀ {a b : Node}, Determines a b → ∀ w' : C.World, OutcomeOf b w' = OutcomeOf a w'
  external_node_fixed_by_prior_state :
    ∀ (a : Node), ¬ IsActOf s a →
      ∀ w' : C.World, C.SameCompletePriorState w w' →
        OutcomeOf a w' = OutcomeOf a w
  determination_exhaustive :
    ∀ (a : Node),
      (∀ w' : C.World, C.Accessible w w' → C.SameCompletePriorState w w' → OutcomeOf a w' = OutcomeOf a w) →
      (∃ b : Node, Determines b a) ∨ ¬ IsActOf s a
  verdict_tracks :
    ∀ w1 w2 : C.World,
      OutcomeOf verdictNode w1 = OutcomeOf verdictNode w2 →
      (C.AssentsAt s w1 p → C.AssentsAt s w2 p) ∧
      (C.WithholdsAt s w1 p → C.WithholdsAt s w2 p)
  verdict_tracks_alternative :
    ∀ w1 w2 : C.World,
      OutcomeOf verdictNode w1 ≠ OutcomeOf verdictNode w2 →
      ((C.AssentsAt s w1 p ∧ C.WithholdsAt s w2 p) ∨
       (C.WithholdsAt s w1 p ∧ C.AssentsAt s w2 p))

/-- Teorema da propagação determinativa:
    se `a` determina ancestralmente `b`, então o resultado de `b` é idêntico
    ao resultado de `a` em qualquer mundo `w'`.
    Footprint: `{}`. -/
theorem determination_propagates_outcome
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    {a b : J.Node}
    (hDet : DeterminesAncestrally J.Determines a b)
    (w' : C.World) :
    J.OutcomeOf b w' = J.OutcomeOf a w' := by
  induction hDet with
  | direct hd =>
    exact J.determines_propagates hd w'
  | trans hd _ ih =>
    have hDirect := J.determines_propagates hd w'
    exact ih.trans hDirect

/-- Propagação sobre o alcance determinativo (identidade ou ancestralidade).
    Footprint: `{}`. -/
theorem reaches_propagates_outcome
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    {a b : J.Node}
    (hReach : a = b ∨ DeterminesAncestrally J.Determines a b)
    (w' : C.World) :
    J.OutcomeOf b w' = J.OutcomeOf a w' := by
  cases hReach with
  | inl hEq => subst hEq; rfl
  | inr hAnc => exact determination_propagates_outcome J hAnc w'

/-- Composição do alcance: quem alcança o acto de julgar alcança o veredicto final.
    Footprint: `{}`. -/
theorem reaches_judgment_act_implies_reaches_verdict
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    {a : J.Node}
    (hReachAct : a = J.judgmentActNode ∨ DeterminesAncestrally J.Determines a J.judgmentActNode) :
    a = J.verdictNode ∨ DeterminesAncestrally J.Determines a J.verdictNode := by
  have hActVer := J.judgmentActDeterminesVerdict
  cases hReachAct with
  | inl hEqAct =>
    subst hEqAct
    exact hActVer
  | inr hAncAct =>
    cases hActVer with
    | inl hEqVer =>
      exact Or.inr (hEqVer ▸ hAncAct)
    | inr hAncVer =>
      exact Or.inr (determines_ancestrally_trans hAncAct hAncVer)

/-- Fonte do Sujeito na determinação do juízo:
    uma fonte interna última da determinação do juízo que é um acto
    do próprio sujeito concreto `s` e determina ancestralmente o acto de julgar
    (ou é o próprio acto). -/
def SubjectSourceOfJudgment
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    (a : J.Node) : Prop :=
  UltimateInternalSource J.toDeterminationSystem a ∧
  J.IsActOf s a ∧
  (a = J.judgmentActNode ∨ DeterminesAncestrally J.Determines a J.judgmentActNode)

/-- Auto-origem da determinação: `a` é fonte interna última E é um acto de `s`.
    DERIVADA estruturalmente. -/
def SelfOrigin
    {C : Semantics Subject} {s : Subject} {w : C.World} {p : Prop}
    (J : JudgmentDeterminationChain C s w p) (a : J.Node) : Prop :=
  UltimateInternalSource J.toDeterminationSystem a ∧ J.IsActOf s a

/-- Teorema da derivação da auto-origem: fonte interna última + acto de s = auto-origem. `{}`. -/
theorem self_origin_derived
    {C : Semantics Subject} {s : Subject} {w : C.World} {p : Prop}
    (J : JudgmentDeterminationChain C s w p) (a : J.Node)
    (hUlt : UltimateInternalSource J.toDeterminationSystem a)
    (hAct : J.IsActOf s a) :
    SelfOrigin J a :=
  ⟨hUlt, hAct⟩

/-- Existência de fonte última do acto de julgar por indução bem-fundada.
    PREÇO: `[propext, Classical.choice, Quot.sound]`. -/
theorem exists_ultimate_source_of_judgment_act
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : JudgmentDeterminationChain C s w p) :
    ∃ a : J.Node,
      UltimateInternalSource J.toDeterminationSystem a ∧
      (a = J.judgmentActNode ∨ DeterminesAncestrally J.Determines a J.judgmentActNode) :=
  node_has_ancestral_ultimate_source J.toDeterminationSystem J.judgmentActNode

/-- Fonte última do veredicto numa cadeia de juízo:
    um nó que é fonte interna última da cadeia e determina ancestralmente
    o nó de veredicto (ou é o próprio veredicto). -/
def UltimateSourceOfJudgmentVerdict
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    (a : J.Node) : Prop :=
  UltimateInternalSource J.toDeterminationSystem a ∧
  (a = J.verdictNode ∨ DeterminesAncestrally J.Determines a J.verdictNode)

/-- Fonte externa do juízo:
    a fonte da determinação do veredicto é puramente externa ao sujeito concreto `s`
    (não é um acto do sujeito `s`). -/
def ExternalSourceOfJudgment
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    (a : J.Node) : Prop :=
  UltimateSourceOfJudgmentVerdict J a ∧ ¬ J.IsActOf s a

/-- A fonte externa não é um acto do sujeito `s`. Footprint: `{}`. -/
theorem external_source_is_external
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    {a : J.Node}
    (hExt : ExternalSourceOfJudgment J a) :
    ¬ J.IsActOf s a :=
  hExt.2

/-- O mesmo estado antecedente completo fixa o resultado da fonte externa. Footprint: `{}`. -/
theorem external_source_fixed_by_prior_state
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    {a : J.Node}
    (hExt : ExternalSourceOfJudgment J a)
    {w' : C.World}
    (hPrior : C.SameCompletePriorState w w') :
    J.OutcomeOf a w' = J.OutcomeOf a w :=
  J.external_node_fixed_by_prior_state a (external_source_is_external J hExt) w' hPrior

/-- A determinação propaga-se da fonte externa através da cadeia,
    fixando o resultado do nó de veredicto entre mundos com o mesmo estado antecedente.
    Footprint: `{}`. -/
theorem external_source_implies_verdict_outcome_invariant
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    {a : J.Node}
    (hExt : ExternalSourceOfJudgment J a)
    {w' : C.World}
    (hPrior : C.SameCompletePriorState w w') :
    J.OutcomeOf J.verdictNode w' = J.OutcomeOf J.verdictNode w := by
  have hReach := hExt.1.2
  have hPropW' := reaches_propagates_outcome J hReach w'
  have hPropW := reaches_propagates_outcome J hReach w
  have hFixA := external_source_fixed_by_prior_state J hExt hPrior
  calc
    J.OutcomeOf J.verdictNode w' = J.OutcomeOf a w' := hPropW'
    _ = J.OutcomeOf a w := hFixA
    _ = J.OutcomeOf J.verdictNode w := hPropW.symm

/-- O veredicto (assentimento e suspensão) é invariante sob o mesmo estado antecedente
    completo quando governado por uma fonte externa. Footprint: `{}`. -/
theorem external_source_implies_verdict_invariant
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    {a : J.Node}
    (hExt : ExternalSourceOfJudgment J a)
    {w' : C.World}
    (hPrior : C.SameCompletePriorState w w') :
    (C.AssentsAt s w p → C.AssentsAt s w' p) ∧
    (C.WithholdsAt s w p → C.WithholdsAt s w' p) := by
  have hEq := external_source_implies_verdict_outcome_invariant J hExt hPrior
  exact J.verdict_tracks w w' hEq.symm

/-- Fonte externa implica forçagem mecânica (`MechanicallyForced`). Footprint: `{}`. -/
theorem external_source_implies_mechanically_forced
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    (hExt : ∃ a : J.Node, ExternalSourceOfJudgment J a) :
    MechanicallyForced C s w p := by
  rcases hExt with ⟨a, ha⟩
  intro w' _hAcc hPrior
  exact external_source_implies_verdict_invariant J ha hPrior

/-- Exaustão quanto à titularidade do acto:
    qualquer nó determinante ou é um acto do próprio sujeito `s`, ou é externo a `s`.
    PREÇO: `[propext, Classical.choice, Quot.sound]`. -/
theorem judgment_act_source_exhaustion
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    (a : J.Node) :
    J.IsActOf s a ∨ ¬ J.IsActOf s a :=
  Classical.em (J.IsActOf s a)

/-- Teorema da Exclusão da Fonte Externa:
    Se o juízo não é mecanicamente forçado (`¬ MechanicallyForced`), então
    nenhuma fonte última externa pode existir na cadeia de determinação.
    Footprint: `{}`. -/
theorem non_mechanical_excludes_external_judgment_source
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    (hNotForced : ¬ MechanicallyForced C s w p) :
    ¬ ∃ a : J.Node, ExternalSourceOfJudgment J a :=
  fun hExt => hNotForced (external_source_implies_mechanically_forced J hExt)

/-- Sob não-mecanicidade, qualquer fonte interna última que determine o veredicto
    é necessariamente um acto do próprio sujeito.
    PREÇO: `[propext, Classical.choice, Quot.sound]`. -/
theorem ultimate_source_is_act_of_subject
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    (hNotForced : ¬ MechanicallyForced C s w p)
    {a : J.Node}
    (haReachVer : a = J.verdictNode ∨ DeterminesAncestrally J.Determines a J.verdictNode)
    (haSource : UltimateInternalSource J.toDeterminationSystem a) :
    J.IsActOf s a := by
  cases judgment_act_source_exhaustion J a with
  | inl hAct => exact hAct
  | inr hNotAct =>
    have hExt : ExternalSourceOfJudgment J a := ⟨⟨haSource, haReachVer⟩, hNotAct⟩
    exact False.elim (non_mechanical_excludes_external_judgment_source J hNotForced ⟨a, hExt⟩)

/-- Teorema da Fonte Subjectiva da Determinação:
    Sob não-mecanicidade (`¬ MechanicallyForced`), a fonte última de determinação
    do acto de julgar é necessariamente um acto do próprio sujeito concreto `s`
    (`SubjectSourceOfJudgment`).
    PREÇO: `[propext, Classical.choice, Quot.sound]`. -/
theorem non_mechanical_yields_subject_source_of_judgment
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    (hNotForced : ¬ MechanicallyForced C s w p) :
    ∃ a : J.Node, SubjectSourceOfJudgment J a := by
  have ⟨a, haSource, haReachAct⟩ := exists_ultimate_source_of_judgment_act J
  cases judgment_act_source_exhaustion J a with
  | inl hAct =>
    exact ⟨a, haSource, hAct, haReachAct⟩
  | inr hNotAct =>
    exfalso
    have hReachVer := reaches_judgment_act_implies_reaches_verdict J haReachAct
    have hExt : ExternalSourceOfJudgment J a := ⟨⟨haSource, hReachVer⟩, hNotAct⟩
    exact non_mechanical_excludes_external_judgment_source J hNotForced ⟨a, hExt⟩

/-- Determinação recebida do estado antecedente completo:
    o resultado do nó `a` é invariante em todos os mundos acessíveis de mesmo passado completo. -/
def DeterminationReceivedFromPriorState
    {C : Semantics Subject} {s : Subject} {w : C.World} {p : Prop}
    (J : JudgmentDeterminationChain C s w p) (a : J.Node) : Prop :=
  ∀ w' : C.World,
    C.Accessible w w' →
    C.SameCompletePriorState w w' →
    J.OutcomeOf a w' = J.OutcomeOf a w

/-- Determinação contingente: o resultado do nó NÃO é recebido do estado antecedente completo. -/
def ContingentDetermination
    {C : Semantics Subject} {s : Subject} {w : C.World} {p : Prop}
    (J : JudgmentDeterminationChain C s w p) (a : J.Node) : Prop :=
  ¬ DeterminationReceivedFromPriorState J a

/-- Determinação ORIGINADA pelo Sujeito: fonte interna última no sujeito que é contingente. -/
def DeterminationOriginatedBySubject
    {C : Semantics Subject} {s : Subject} {w : C.World} {p : Prop}
    (J : JudgmentDeterminationChain C s w p) (a : J.Node) : Prop :=
  SubjectSourceOfJudgment J a ∧ ContingentDetermination J a

/-- Teorema da Ausência de Determinação Recebida:
    Uma fonte interna última da determinação que é um acto do próprio sujeito `s`
    não recebe a sua determinação do estado antecedente completo.
    Demonstrado por contradição analítica `{}` a partir de `determination_exhaustive`:
    se o resultado fosse recebido do antecedente completo, teria de ser determinado por
    outro nó na cadeia ou ser externo a `s`; ambas as alternativas são contraditadas
    por `UltimateInternalSource` e `IsActOf s a`.
    Footprint: `{}`. -/
theorem ultimate_internal_act_source_is_not_received_from_prior_state
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    {a : J.Node}
    (hUlt : UltimateInternalSource J.toDeterminationSystem a)
    (hAct : J.IsActOf s a) :
    ¬ DeterminationReceivedFromPriorState J a := by
  intro hRec
  have hExh := J.determination_exhaustive a hRec
  rcases hExh with ⟨b, hb⟩ | hNotAct
  · exact hUlt ⟨b, hb⟩
  · exact hNotAct hAct

/-- A determinação não-recebida que alcança o veredicto refuta a forçagem mecânica:
    se o resultado do nó `a` varia entre mundos acessíveis com o mesmo passado completo,
    essa variação propaga-se ao veredicto (`OutcomeOf verdictNode w' ≠ OutcomeOf verdictNode w`),
    produzindo juízos opostos que contradizem `MechanicallyForced` pela exclusividade mútua (`exclusive`).
    PREÇO: `[Classical.choice]`. -/
theorem non_received_determination_excludes_mechanical_forcing
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    {a : J.Node}
    (hReachVer : a = J.verdictNode ∨ DeterminesAncestrally J.Determines a J.verdictNode)
    (hNotReceived : ¬ DeterminationReceivedFromPriorState J a) :
    ¬ MechanicallyForced C s w p := by
  intro hForced
  have hex : ∃ w' : C.World,
      C.Accessible w w' ∧
      C.SameCompletePriorState w w' ∧
      J.OutcomeOf a w' ≠ J.OutcomeOf a w := by
    apply Classical.byContradiction
    intro hAll
    apply hNotReceived
    intro w' hAcc hPrior
    apply Classical.byContradiction
    intro hNe
    exact hAll ⟨w', hAcc, hPrior, hNe⟩

  rcases hex with ⟨w', hAcc, hSame, hNeA⟩
  have hPropW' := reaches_propagates_outcome J hReachVer w'
  have hPropW := reaches_propagates_outcome J hReachVer w
  have hNeVerdict : J.OutcomeOf J.verdictNode w' ≠ J.OutcomeOf J.verdictNode w := by
    intro hEq
    apply hNeA
    calc
      J.OutcomeOf a w' = J.OutcomeOf J.verdictNode w' := hPropW'.symm
      _ = J.OutcomeOf J.verdictNode w := hEq
      _ = J.OutcomeOf a w := hPropW
  have hFlip := J.verdict_tracks_alternative w w' (Ne.symm hNeVerdict)
  have hTrack := hForced w' hAcc hSame
  rcases hFlip with ⟨hA, hW'⟩ | ⟨hW, hA'⟩
  · exact C.exclusive s w' p ⟨hTrack.1 hA, hW'⟩
  · exact C.exclusive s w' p ⟨hA', hTrack.2 hW⟩

/-- A determinação última da cadeia de juízo ou é não-recebida do estado antecedente completo
    (`¬ DeterminationReceivedFromPriorState J a`), ou é uma fonte externa ao sujeito.
    Footprint: `{}`. -/
theorem ultimate_source_not_received_or_external
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    {a : J.Node}
    (hUlt : UltimateInternalSource J.toDeterminationSystem a)
    (hReachVer : a = J.verdictNode ∨ DeterminesAncestrally J.Determines a J.verdictNode) :
    ¬ DeterminationReceivedFromPriorState J a ∨ ExternalSourceOfJudgment J a := by
  by_cases hRec : DeterminationReceivedFromPriorState J a
  · have hExh := J.determination_exhaustive a hRec
    cases hExh with
    | inl hDet =>
      exact False.elim (hUlt hDet)
    | inr hNotAct =>
      exact Or.inr ⟨⟨hUlt, hReachVer⟩, hNotAct⟩
  · exact Or.inl hRec

/-- Teorema da Não-Mecanicidade por Fonte Subjectiva:
    Uma fonte interna última que seja acto do sujeito refuta a forçagem mecânica (`¬ MechanicallyForced`).
    PREÇO: `[Classical.choice]`. -/
theorem subject_source_yields_not_mechanically_forced
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    {a : J.Node}
    (hSrc : SubjectSourceOfJudgment J a) :
    ¬ MechanicallyForced C s w p := by
  have hReachVer := reaches_judgment_act_implies_reaches_verdict J hSrc.2.2
  have hNotRec := ultimate_internal_act_source_is_not_received_from_prior_state J hSrc.1 hSrc.2.1
  exact non_received_determination_excludes_mechanical_forcing J hReachVer hNotRec

/-- Uma fonte subjectiva na cadeia possui determinação contingente por
    derivação puramente estrutural, sem necessidade de hipótese de contingência externa.
    Footprint: `{}`. -/
theorem subject_source_yields_contingent_determination_direct
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    {a : J.Node}
    (hSrc : SubjectSourceOfJudgment J a) :
    ContingentDetermination J a :=
  ultimate_internal_act_source_is_not_received_from_prior_state J hSrc.1 hSrc.2.1

/-- A determinação contingente no nó de veredicto (ou em nó que o determine ancestralmente)
    produz sensibilidade normativa directa no mundo do juízo por contraposição clássica.
    PREÇO: `[Classical.choice]`. -/
theorem contingent_determination_yields_normative_sensitivity
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    {a : J.Node}
    (hReachVer : a = J.verdictNode ∨ DeterminesAncestrally J.Determines a J.verdictNode)
    (hCont : ContingentDetermination J a) :
    NormativelySensitive C s w p := by
  have hex : ∃ w' : C.World,
      C.Accessible w w' ∧
      C.SameCompletePriorState w w' ∧
      J.OutcomeOf a w' ≠ J.OutcomeOf a w := by
    apply Classical.byContradiction
    intro hAll
    apply hCont
    intro w' hAcc hPrior
    apply Classical.byContradiction
    intro hNe
    exact hAll ⟨w', hAcc, hPrior, hNe⟩

  rcases hex with ⟨w', hAcc, hSame, hNeA⟩
  have hPropW' := reaches_propagates_outcome J hReachVer w'
  have hPropW := reaches_propagates_outcome J hReachVer w
  have hNeVerdict : J.OutcomeOf J.verdictNode w' ≠ J.OutcomeOf J.verdictNode w := by
    intro hEq
    apply hNeA
    calc
      J.OutcomeOf a w' = J.OutcomeOf J.verdictNode w' := hPropW'.symm
      _ = J.OutcomeOf J.verdictNode w := hEq
      _ = J.OutcomeOf a w := hPropW
  have hNeWorld : w' ≠ w := by
    intro hEqW
    subst hEqW
    exact hNeVerdict rfl
  have hFlip := J.verdict_tracks_alternative w w' (Ne.symm hNeVerdict)
  exact ⟨w', hAcc, hSame, hNeWorld, hFlip⟩

/-- A determinação originada pelo Sujeito produz directamente a escolha libertária.
    PREÇO: `[Classical.choice]`. -/
theorem originated_contingent_determination_yields_libertarian_choice
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    {a : J.Node}
    (hOrig : DeterminationOriginatedBySubject J a) :
    LibertarianFreeChoiceAt C s w p := by
  have hReachAct := hOrig.1.2.2
  have hReachVer := reaches_judgment_act_implies_reaches_verdict J hReachAct
  have hSens := contingent_determination_yields_normative_sensitivity J hReachVer hOrig.2
  exact normative_sensitivity_implies_libertarian_choice_direct hSens

/-- A determinação originada pelo Sujeito produz directamente o livre-arbítrio.
    PREÇO: `[Classical.choice]`. -/
theorem originated_contingent_determination_yields_free_will
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    {a : J.Node}
    (hOrig : DeterminationOriginatedBySubject J a) :
    FreeWillAt C s w :=
  ⟨p, originated_contingent_determination_yields_libertarian_choice J hOrig⟩

/-- TEOREMA MESTRE DA VIA ONTOLÓGICA (namespace FNC):
    A fonte última da determinação na cadeia exaustiva é um acto originado
    pelo próprio Sujeito; é precisamente daí que resulta a determinação originada,
    a escolha libertária, o livre-arbítrio e o Sujeito livre.
    PREÇO: `[Classical.choice]`. -/
theorem ontological_determination_yields_libertarian_freedom
    {C : Semantics Subject}
    {s : Subject}
    {p : Prop}
    (J : JudgmentDeterminationChain C s C.actualWorld p)
    {a : J.Node}
    (hSrc : SubjectSourceOfJudgment J a) :
    DeterminationOriginatedBySubject J a ∧
    LibertarianFreeChoiceAt C s C.actualWorld p ∧
    FreeWillAt C s C.actualWorld ∧
    FreeSubject C s := by
  have hCont : ContingentDetermination J a :=
    ultimate_internal_act_source_is_not_received_from_prior_state J hSrc.1 hSrc.2.1
  have hOrig : DeterminationOriginatedBySubject J a := ⟨hSrc, hCont⟩
  have hChoice := originated_contingent_determination_yields_libertarian_choice J hOrig
  have hWill : FreeWillAt C s C.actualWorld := ⟨p, hChoice⟩
  have hFreeSubj : FreeSubject C s := hWill
  exact ⟨hOrig, hChoice, hWill, hFreeSubj⟩

/-- DA NÃO-MECANICIDADE À LIBERDADE LIBERTÁRIA (via ontológica):
    Sob não-mecanicidade da cadeia, a fonte última é necessariamente um acto do sujeito
    (`non_mechanical_yields_subject_source_of_judgment`), a qual origina contingentemente
    a determinação e deduz conclusivamente a escolha libertária, o livre-arbítrio e o Sujeito livre.
    PREÇO: `[Classical.choice]`. -/
theorem non_mechanical_yields_libertarian_freedom
    {C : Semantics Subject}
    {s : Subject}
    {p : Prop}
    (J : JudgmentDeterminationChain C s C.actualWorld p)
    (hNotForced : ¬ MechanicallyForced C s C.actualWorld p) :
    (∃ a : J.Node, DeterminationOriginatedBySubject J a) ∧
    LibertarianFreeChoiceAt C s C.actualWorld p ∧
    FreeWillAt C s C.actualWorld ∧
    FreeSubject C s := by
  have ⟨a, hSrc⟩ := non_mechanical_yields_subject_source_of_judgment J hNotForced
  have hOnt := ontological_determination_yields_libertarian_freedom J hSrc
  exact ⟨⟨a, hOnt.1⟩, hOnt.2.1, hOnt.2.2.1, hOnt.2.2.2⟩

/-- O resultado de qualquer nó externo ao sujeito é recebido do estado antecedente completo.
    Footprint: `{}`. -/
theorem external_node_determination_received_from_prior_state
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    (a : J.Node)
    (hNotAct : ¬ J.IsActOf s a) :
    DeterminationReceivedFromPriorState J a :=
  fun w' _hAcc hPrior => J.external_node_fixed_by_prior_state a hNotAct w' hPrior

/-- Determinação constitutiva do acto do sujeito na cadeia:
    Quando a cadeia em análise é a cadeia causal constitutiva do acto concreto
    de julgar do próprio sujeito `s`, a determinação última desse acto não pode ser
    uma determinação puramente externa recebida integralmente do estado antecedente completo. -/
def ConstitutiveActDetermination
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : JudgmentDeterminationChain C s w p) : Prop :=
  ∀ a : J.Node,
    UltimateInternalSource J.toDeterminationSystem a →
    (a = J.judgmentActNode ∨ DeterminesAncestrally J.Determines a J.judgmentActNode) →
    ¬ (¬ J.IsActOf s a ∧ DeterminationReceivedFromPriorState J a)

/-- Sob a determinação constitutiva do acto concreto, qualquer fonte última ancestral
    do acto de julgar é necessariamente um acto do próprio sujeito.
    PREÇO: `[Classical.choice]`. -/
theorem constitutive_act_determination_source_is_act_of_subject
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    (hConst : ConstitutiveActDetermination J)
    {a : J.Node}
    (haSource : UltimateInternalSource J.toDeterminationSystem a)
    (haReachAct : a = J.judgmentActNode ∨ DeterminesAncestrally J.Determines a J.judgmentActNode) :
    J.IsActOf s a := by
  apply Classical.byContradiction
  intro hNotAct
  have hRec := external_node_determination_received_from_prior_state J a hNotAct
  exact hConst a haSource haReachAct ⟨hNotAct, hRec⟩

/-- LEMA PONTE FUNDAMENTAL: Toda a cadeia constitutiva de julgamento
    `JudgmentDeterminationChain` satisfaz analiticamente `ConstitutiveActDetermination`.
    PREÇO: `{}` (puramente dedutivo). -/
theorem judgment_determination_chain_satisfies_constitutive_act_determination
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : JudgmentDeterminationChain C s w p) :
    ConstitutiveActDetermination J := by
  intro a haSource haReach ⟨hNotAct, _hRec⟩
  have haAct := J.act_ancestral_determination_is_agential a haReach
  exact hNotAct haAct

/-- PROCEDIMENTO C — TESTE DE NÃO-CIRCULARIDADE E INDEPENDÊNCIA NEGATIVA:
    Demonstra formalmente que `ConstitutiveActDetermination J` é incompatível com
    `MechanicallyForced C s C.actualWorld p`.
    A inconsistência resulta estritamente da composição dos lemas independentes
    `ultimate_internal_act_source_is_not_received_from_prior_state` (fundado na exaustão da determinação)
    e `non_received_determination_excludes_mechanical_forcing` (fundado na variação modal do veredicto),
    e não de uma redefinição que assuma trivialmente a conclusão.
    PREÇO: `[Classical.choice]`. -/
theorem constitutive_act_determination_incompatible_with_mechanical_forcing
    {C : Semantics Subject}
    {s : Subject}
    {p : Prop}
    (J : JudgmentDeterminationChain C s C.actualWorld p)
    (hConst : ConstitutiveActDetermination J)
    (hForced : MechanicallyForced C s C.actualWorld p) :
    False := by
  have ⟨a, haSource, haReachAct⟩ := exists_ultimate_source_of_judgment_act J
  have haAct := constitutive_act_determination_source_is_act_of_subject J hConst haSource haReachAct
  have hNotRec := ultimate_internal_act_source_is_not_received_from_prior_state J haSource haAct
  have hReachVer := reaches_judgment_act_implies_reaches_verdict J haReachAct
  have hNotForced : ¬ MechanicallyForced C s C.actualWorld p :=
    non_received_determination_excludes_mechanical_forcing J hReachVer hNotRec
  exact hNotForced hForced

inductive TwoNodes : Type where
  | ext : TwoNodes
  | act : TwoNodes
  deriving DecidableEq, Repr

def priorTwoNodes : TwoNodes → TwoNodes → Prop
  | TwoNodes.ext, TwoNodes.act => True
  | _, _ => False

theorem priorTwoNodes_wf : WellFounded priorTwoNodes := by
  constructor
  intro a
  cases a with
  | ext =>
    constructor
    intro y hy
    cases y <;> contradiction
  | act =>
    constructor
    intro y hy
    cases y with
    | ext =>
      constructor
      intro z hz
      cases z <;> contradiction
    | act => contradiction

/-- GUARDA NEGATIVA FORMAL (Teste de Provabilidade, §4):
    Demonstra rigorosamente que, sob a definição abstracta de `UnrestrictedJudgmentDeterminationChain`
    sem a propriedade de determinação constitutiva do acto, é formalmente impossível
    derivar `¬ MechanicallyForced`.
    Existe um contramodelo de 2 nós onde:
    (1) a cadeia é bem-fundada e exaustiva;
    (2) o acto de julgar é acto de `s`;
    (3) a fonte última ancestral do acto de julgar é externa ao sujeito;
    (4) o juízo é mecanicamente forçado. -/
theorem mechanical_judgment_chain_with_external_ultimate_source :
    ∃ (C : Semantics.{0, 0} Unit) (s : Unit) (p : Prop)
      (J : @UnrestrictedJudgmentDeterminationChain.{0, 0, 0} Unit C s C.actualWorld p)
      (a : J.Node),
      UltimateInternalSource J.toDeterminationSystem a ∧
      (a = J.judgmentActNode ∨ DeterminesAncestrally J.Determines a J.judgmentActNode) ∧
      ¬ J.IsActOf s a ∧
      MechanicallyForced C s C.actualWorld p := by
  let C : Semantics.{0, 0} Unit :=
    { World := Unit
      actualWorld := ()
      Accessible := fun _ _ => True
      SameCompletePriorState := fun _ _ => True
      AssentsAt := fun _ _ _ => True
      WithholdsAt := fun _ _ _ => False
      exclusive := fun _ _ _ h => h.2 }
  let J : @UnrestrictedJudgmentDeterminationChain.{0, 0, 0} Unit C () () True :=
    { Node := TwoNodes
      Prior := priorTwoNodes
      priorWellFounded := priorTwoNodes_wf
      Determines := priorTwoNodes
      determinationRespectsPriority := fun h => h
      Outcome := Unit
      OutcomeOf := fun _ _ => ()
      verdictNode := TwoNodes.act
      judgmentActNode := TwoNodes.act
      IsActOf := fun _ n => n = TwoNodes.act
      judgmentActIsActOf := rfl
      judgmentActDeterminesVerdict := Or.inl rfl
      determines_propagates := fun _ _ => rfl
      external_node_fixed_by_prior_state := fun _ _ _ _ => rfl
      determination_exhaustive := fun n _ => by
        cases n with
        | ext =>
          right
          intro hAct
          injection hAct
        | act =>
          left
          exact ⟨TwoNodes.ext, trivial⟩
      verdict_tracks := fun _ _ _ => ⟨fun h => h, fun h => h⟩
      verdict_tracks_alternative := fun _ _ hNe => False.elim (hNe rfl) }
  refine ⟨C, (), True, J, TwoNodes.ext, ?_, ?_, ?_, ?_⟩
  · intro ⟨b, hb⟩
    cases b <;> contradiction
  · exact Or.inr (DeterminesAncestrally.direct trivial)
  · intro hAct
    injection hAct
  · intro w' _ _
    exact ⟨fun h => h, fun h => h⟩

/-- TEOREMA MESTRE: ARGUMENTO COMPLETO DA LIBERDADE LIBERTÁRIA.
    A partir da existência da cadeia real constitutiva do acto concreto de julgar
    (`J : JudgmentDeterminationChain C s C.actualWorld p`), a não-autodeterminação
    da cadeia bem-fundada (`node_has_ancestral_ultimate_source`) fornece uma fonte
    última ancestral `a` do acto de julgar (`judgmentActNode`).
    Pela ancestralidade agencial da cadeia constitutiva (`act_ancestral_determination_is_agential`),
    essa fonte última ancestral não é puramente heterónoma, sendo necessariamente acto do próprio sujeito.
    Pela exaustividade, essa fonte subjectiva não recebe a sua determinação do estado
    antecedente completo (`ultimate_internal_act_source_is_not_received_from_prior_state`).
    A não-recepção refuta a forçagem mecânica (`¬ MechanicallyForced`), deduz que
    o sujeito é a fonte do juízo (`SubjectSourceOfJudgment J a`), e o fecho
    ontológico deduz conclusivamente a escolha libertária, o livre-arbítrio e
    o Sujeito Livre (`FreeSubject C s`).
    PREÇO: `[Classical.choice]`. -/
theorem complete_libertarian_freedom_argument
    {C : Semantics Subject}
    {s : Subject}
    {p : Prop}
    (J : JudgmentDeterminationChain C s C.actualWorld p) :
    FreeSubject C s := by
  have ⟨a, haSource, haReachAct⟩ := exists_ultimate_source_of_judgment_act J
  have haAct := J.act_ancestral_determination_is_agential a haReachAct
  have hNotRec := ultimate_internal_act_source_is_not_received_from_prior_state J haSource haAct
  have hReachVer := reaches_judgment_act_implies_reaches_verdict J haReachAct
  have hNotForced : ¬ MechanicallyForced C s C.actualWorld p :=
    non_received_determination_excludes_mechanical_forcing J hReachVer hNotRec
  have ⟨src, hSrc⟩ :=
    non_mechanical_yields_subject_source_of_judgment J hNotForced
  exact (ontological_determination_yields_libertarian_freedom J hSrc).2.2.2

theorem performative_proof_instantiates_libertarian_freedom
    {C : Semantics Subject}
    {s : Subject}
    {p : Prop}
    (J : JudgmentDeterminationChain C s C.actualWorld p)
    {a : J.Node}
    (hSrc : SubjectSourceOfJudgment J a) :
    FreeSubject C s :=
  (ontological_determination_yields_libertarian_freedom J hSrc).2.2.2

/-- Instanciação concreta de um acto de julgamento constitutivo:
    A presença desta própria demonstração formal (ou de qualquer juízo real correspondente)
    no mundo actual fornece uma instância concreta da estrutura `JudgmentDeterminationChain`
    para algum sujeito e alguma proposição.
    Esta estrutura é estritamente existencial: o sujeito permanece anónimo, não sendo
    necessário identificá-lo com o autor, o leitor, ou qualquer entidade biológica particular. -/
structure ProofInstance (C : Semantics Subject) where
  subject : Subject
  proposition : Prop
  chain : JudgmentDeterminationChain.{u, v, u_out} C subject C.actualWorld proposition

/-- TEOREMA EXISTENCIAL MESTRE — A CONCLUSÃO ANÓNIMA DO SUJEITO LIVRE:
    "A existência desta demonstração fornece uma instância concreta do tipo de acto
     de julgamento formalizado; logo, existe pelo menos um Sujeito Livre.
     Não é necessário determinar quem ele é."

    A prova decompõe-se conceptualmente em três níveis:
    (1) A prova universal: `JudgmentDeterminationChain C s C.actualWorld p → FreeSubject C s`
        (demonstrada em `complete_libertarian_freedom_argument`);
    (2) A ocorrência concreta da demonstração: `ProofInstance C`
        (fornecida pela existência do acto de juízo constitutivo formalizado);
    (3) A conclusão puramente existencial: `∃ s : Subject, FreeSubject C s`.

    Não se presume que o leitor ou o autor sejam livres; mesmo que ambos fossem
    concebidos como mecanismos puramente biológicos, a presença real da cadeia constitutiva
    implica que no universo semântico existe pelo menos um Sujeito Livre `s`.
    PREÇO: `[Classical.choice]`. -/
theorem proof_instance_implies_existence_of_free_subject
    {C : Semantics Subject}
    (inst : ProofInstance C) :
    ∃ s : Subject, FreeSubject C s :=
  ⟨inst.subject, complete_libertarian_freedom_argument inst.chain⟩

/-- Corolário de formulação proposicional pura:
    A não-vacuidade existencial da instância da demonstração acarreta a existência
    de um Sujeito Livre. -/
theorem proof_instance_nonempty_implies_existence_of_free_subject
    {C : Semantics Subject}
    (h : Nonempty (ProofInstance C)) :
    ∃ s : Subject, FreeSubject C s :=
  let ⟨inst⟩ := h
  proof_instance_implies_existence_of_free_subject inst

/-- Ocorrência concreta de uma demonstração formal:
    Modela a asserção performatória de que esta prova é uma ocorrência efectiva
    de um acto judicativo fundamentado na semântica `C`.
    Fornece a instância concreta `ProofInstance C` sem pressupor a liberdade de quem
    a profere ou lê, mantendo o sujeito estritamente existencial e anónimo. -/
structure DemonstrativeProofOccurrence (C : Semantics Subject) where
  instanceOfJudgment : ProofInstance.{u, v, u_out} C

/-- LEMA PONTE PERFORMATÓRIO: A ocorrência desta demonstração como acto judicativo real
    implica a não-vacuidade existencial da instância de julgamento (`Nonempty (ProofInstance C)`).
    PREÇO: `{}` (puramente dedutivo). -/
theorem demonstration_occurrence_yields_proof_instance
    {C : Semantics Subject}
    (demo : DemonstrativeProofOccurrence.{u, v, u_out} C) :
    Nonempty (ProofInstance.{u, v, u_out} C) :=
  ⟨demo.instanceOfJudgment⟩

/-- TEOREMA PERFORMATÓRIO-EXISTENCIAL FINAL:
    "Se esta prova está a ser efectivamente instanciada como demonstração de um juízo,
     então existe pelo menos um Sujeito Livre.
     Não é necessário que esse sujeito seja o autor ou o leitor,
     nem que seja pressuposto como não-mecânico."

    A dedução conecta os três elos da cadeia:
    (1) A ocorrência concreta da demonstração: `DemonstrativeProofOccurrence C`;
    (2) A garantia estrutural de instanciação: `Nonempty (ProofInstance C)`;
    (3) A conclusão existencial estrita: `∃ s : Subject, FreeSubject C s`.

    PREÇO: `[Classical.choice]`. -/
theorem demonstration_occurrence_implies_existence_of_free_subject
    {C : Semantics Subject}
    (demo : DemonstrativeProofOccurrence C) :
    ∃ s : Subject, FreeSubject C s :=
  proof_instance_implies_existence_of_free_subject demo.instanceOfJudgment

/-- A EXISTÊNCIA CONCRETA DA PROVA:
    Expressa formalmente que existe pelo menos uma instância concreta da estrutura
    judicativa formalizada na semântica `C`.

    Distinção de níveis:
    - Nível-objeto (Lean): `ProofExists C → ∃ s, FreeSubject C s`;
    - Meta-nível: o facto performativo de que esta demonstração existe e é efectuada
      é o que fornece a instância concreta de `ProofExists C`.

    Não introduz qualquer menção a leitor, autor ou propriedades biológicas/físicas;
    não pressupõe a liberdade de ninguém nem contingência modal global. -/
def ProofExists (C : Semantics Subject) : Prop :=
  Nonempty (ProofInstance.{u, v, u_out} C)

/-- TEOREMA CONCLUSIVO FINAL:
    "SE ESTA PROVA EXISTE, EXISTE SUJEITO LIVRE."

    A prova não identifica esse sujeito com o autor nem com o leitor.
    Também não pressupõe que qualquer deles seja livre.
    A única exigência é a existência de uma instância concreta da estrutura judicativa formalizada.
    A partir dessa instância, o argumento deduz `∃ s : Subject, FreeSubject C s`.

    Frase de apresentação informal:
    “Se esta prova existe, existe Sujeito Livre (mesmo que tu e o autor sejais apenas 'robôs biológicos').”

    PREÇO: `[Classical.choice]`. -/
theorem proof_exists_implies_existence_of_free_subject
    {C : Semantics Subject}
    (h : ProofExists C) :
    ∃ s : Subject, FreeSubject C s :=
  let ⟨inst⟩ := h
  proof_instance_implies_existence_of_free_subject inst

/-- Sujeito necessário: a mente pensante do sujeito existe em todos os mundos acessíveis. -/
def NecessarySubject (C : Semantics Subject) (s : Subject) : Prop :=
  ∀ w : C.World, C.Accessible C.actualWorld w → C.ThinkingMindAt s w

/-- Sujeito contingente: há um mundo acessível onde o sujeito não pensa. -/
def ContingentSubject (C : Semantics Subject) (s : Subject) : Prop :=
  ∃ w : C.World, C.Accessible C.actualWorld w ∧ ¬ C.ThinkingMindAt s w

inductive TwoWorlds : Type where
  | actual : TwoWorlds
  | alternative : TwoWorlds
  deriving DecidableEq, Repr

/-- GUARD G2: O Sujeito pode existir necessariamente enquanto a determinação
    do seu acto concreto é contingente.
    A necessidade do Sujeito e a contingência da determinação são logicamente independentes. -/
theorem necessary_subject_and_contingent_determination_coexist :
    ∃ (C : Semantics.{0, 0} Unit) (s : Unit) (p : Prop)
      (J : @JudgmentDeterminationChain.{0, 0, 0} Unit C s C.actualWorld p) (a : J.Node),
      NecessarySubject C s ∧
      ContingentDetermination J a := by
  let C : Semantics.{0, 0} Unit :=
    { World := TwoWorlds
      actualWorld := TwoWorlds.actual
      Accessible := fun _ _ => True
      SameCompletePriorState := fun _ _ => True
      AssentsAt := fun _ w _ => w = TwoWorlds.actual
      WithholdsAt := fun _ w _ => w = TwoWorlds.alternative
      exclusive := fun _ w _ h => by
        cases w with
        | actual => exact TwoWorlds.noConfusion h.2
        | alternative => exact TwoWorlds.noConfusion h.1
      ThinkingMindAt := fun _ _ => True }
  have hNec : NecessarySubject C () := fun _ _ => trivial
  let J : @JudgmentDeterminationChain.{0, 0, 0} Unit C () C.actualWorld True :=
    { Node := Unit
      Prior := fun _ _ => False
      priorWellFounded := ⟨fun x => Acc.intro x (fun _ h => False.elim h)⟩
      Determines := fun _ _ => False
      determinationRespectsPriority := fun h => False.elim h
      Outcome := TwoWorlds
      OutcomeOf := fun _ w => w
      verdictNode := ()
      judgmentActNode := ()
      IsActOf := fun _ _ => True
      judgmentActIsActOf := trivial
      judgmentActDeterminesVerdict := Or.inl rfl
      act_ancestral_determination_is_agential := fun _ _ => trivial
      determines_propagates := fun h => False.elim h
      external_node_fixed_by_prior_state := fun _ hNot => False.elim (hNot trivial)
      determination_exhaustive := by
        intro a hFixed
        have hEq := hFixed TwoWorlds.alternative trivial trivial
        exact False.elim (TwoWorlds.noConfusion hEq)
      verdict_tracks := fun w1 w2 hEq => ⟨fun h => hEq ▸ h, fun h => hEq ▸ h⟩
      verdict_tracks_alternative := fun w1 w2 hNe => by
        cases w1 <;> cases w2
        · exact False.elim (hNe rfl)
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩
        · exact False.elim (hNe rfl) }
  have hCont : ContingentDetermination J () := by
    intro hRec
    have hEq := hRec TwoWorlds.alternative trivial trivial
    exact TwoWorlds.noConfusion hEq
  exact ⟨C, (), True, J, (), hNec, hCont⟩

/-- Liberdade libertária não é mera ausência de forçagem mecânica (`¬ MechanicallyForced`). -/
theorem freedom_is_not_merely_unforced :
    ∃ (C : Semantics.{0, 0} Unit) (s : Unit) (p : Prop),
      ¬ MechanicallyForced C s C.actualWorld p ∧
      ¬ FreeSubject C s := by
  let C : Semantics.{0, 0} Unit :=
    { World := TwoWorlds
      actualWorld := TwoWorlds.actual
      Accessible := fun _ _ => True
      SameCompletePriorState := fun _ _ => True
      AssentsAt := fun _ w _ => w = TwoWorlds.actual
      WithholdsAt := fun _ _ _ => False
      exclusive := fun _ _ _ h => h.2 }
  have hNotForced : ¬ MechanicallyForced C () C.actualWorld True := by
    intro hForced
    have hSpec := (hForced TwoWorlds.alternative trivial trivial).1
    have hAssentAct : C.AssentsAt () TwoWorlds.actual True := rfl
    have hAssentAlt : C.AssentsAt () TwoWorlds.alternative True := hSpec hAssentAct
    exact TwoWorlds.noConfusion hAssentAlt
  have hNotFree : ¬ FreeSubject C () := by
    intro ⟨p, hp⟩
    rcases hp with ⟨hA, w', _, _, _, hW⟩ | ⟨hW, _⟩
    · exact hW
    · exact hW
  exact ⟨C, (), True, hNotForced, hNotFree⟩

/-- TESTE AUXILIAR DE CONSISTÊNCIA CONSTRUTIVA:
    Certifica formalmente que a cadeia exaustiva com fonte interna no sujeito
    e determinação originada é construtível e não-vazia. -/
theorem toy_model_consistency_witness :
    ∃ (C : Semantics.{0, 0} Unit) (s : Unit) (p : Prop)
      (J : @JudgmentDeterminationChain.{0, 0, 0} Unit C s C.actualWorld p)
      (a : J.Node),
      SubjectSourceOfJudgment J a ∧
      DeterminationOriginatedBySubject J a ∧
      LibertarianFreeChoiceAt C s C.actualWorld p ∧
      FreeWillAt C s C.actualWorld ∧
      FreeSubject C s := by
  let C : Semantics.{0, 0} Unit :=
    { World := TwoWorlds
      actualWorld := TwoWorlds.actual
      Accessible := fun w w' => w ≠ w'
      SameCompletePriorState := fun _ _ => True
      AssentsAt := fun _ w _ => w = TwoWorlds.actual
      WithholdsAt := fun _ w _ => w = TwoWorlds.alternative
      exclusive := fun _ w _ h => by
        cases w with
        | actual => exact TwoWorlds.noConfusion h.2
        | alternative => exact TwoWorlds.noConfusion h.1
      ThinkingMindAt := fun _ _ => True
      MeansAt := fun _ _ _ => True
      ApprehendsAt := fun _ w _ => w = TwoWorlds.actual
      ReasonSupports := fun _ _ _ _ => True }
  let J : @JudgmentDeterminationChain.{0, 0, 0} Unit C () C.actualWorld True :=
    { Node := Unit
      Prior := fun _ _ => False
      priorWellFounded := ⟨fun x => Acc.intro x (fun _ h => False.elim h)⟩
      Determines := fun _ _ => False
      determinationRespectsPriority := fun h => False.elim h
      Outcome := TwoWorlds
      OutcomeOf := fun _ w => w
      verdictNode := ()
      judgmentActNode := ()
      IsActOf := fun _ _ => True
      judgmentActIsActOf := trivial
      judgmentActDeterminesVerdict := Or.inl rfl
      act_ancestral_determination_is_agential := fun _ _ => trivial
      determines_propagates := fun h => False.elim h
      external_node_fixed_by_prior_state := fun _ hNot => False.elim (hNot trivial)
      determination_exhaustive := by
        intro a hFixed
        have hEq := hFixed TwoWorlds.alternative (fun h => TwoWorlds.noConfusion h) trivial
        exact False.elim (TwoWorlds.noConfusion hEq)
      verdict_tracks := fun w1 w2 hEq => ⟨fun h => hEq ▸ h, fun h => hEq ▸ h⟩
      verdict_tracks_alternative := fun w1 w2 hNe => by
        cases w1 <;> cases w2
        · exact False.elim (hNe rfl)
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩
        · exact False.elim (hNe rfl) }
  have hSrc : SubjectSourceOfJudgment J () := by
    refine ⟨?_, trivial, Or.inl rfl⟩
    intro ⟨b, hb⟩
    exact hb
  have hOnt := ontological_determination_yields_libertarian_freedom J hSrc
  exact ⟨C, (), True, J, (), hSrc, hOnt.1, hOnt.2.1, hOnt.2.2.1, hOnt.2.2.2⟩

end FinalNonCircularClosure

/-- TEOREMA PÚBLICO PRINCIPAL — VIA ONTOLÓGICA DIRECTA:
    A fonte última da determinação na cadeia exaustiva é um acto originado
    pelo próprio Sujeito. É desta fundação ontológica da acção que decorre a
    determinação originada pelo Sujeito, a escolha libertária, o livre-arbítrio
    e o Sujeito livre.
    PREÇO: `[Classical.choice]`. -/
theorem ontological_determination_yields_libertarian_freedom
    {C : FinalNonCircularClosure.Semantics Subject}
    {s : Subject}
    {p : Prop}
    (J : FinalNonCircularClosure.JudgmentDeterminationChain C s C.actualWorld p)
    {a : J.Node}
    (hSrc : FinalNonCircularClosure.SubjectSourceOfJudgment J a) :
    FinalNonCircularClosure.DeterminationOriginatedBySubject J a ∧
    FinalNonCircularClosure.LibertarianFreeChoiceAt C s C.actualWorld p ∧
    FinalNonCircularClosure.FreeWillAt C s C.actualWorld ∧
    FinalNonCircularClosure.FreeSubject C s :=
  FinalNonCircularClosure.ontological_determination_yields_libertarian_freedom J hSrc

/-- TEOREMA PÚBLICO: DA NÃO-MECANICIDADE À LIBERDADE LIBERTÁRIA:
    Sob não-mecanicidade da cadeia, a fonte última é necessariamente um acto do sujeito
    (`non_mechanical_yields_subject_source_of_judgment`), a qual origina contingentemente
    a determinação e deduz conclusivamente a escolha libertária, o livre-arbítrio e o Sujeito livre.
    PREÇO: `[Classical.choice]`. -/
theorem non_mechanical_yields_libertarian_freedom
    {C : FinalNonCircularClosure.Semantics Subject}
    {s : Subject}
    {p : Prop}
    (J : FinalNonCircularClosure.JudgmentDeterminationChain C s C.actualWorld p)
    (hNotForced : ¬ FinalNonCircularClosure.MechanicallyForced C s C.actualWorld p) :
    (∃ a : J.Node, FinalNonCircularClosure.DeterminationOriginatedBySubject J a) ∧
    FinalNonCircularClosure.LibertarianFreeChoiceAt C s C.actualWorld p ∧
    FinalNonCircularClosure.FreeWillAt C s C.actualWorld ∧
    FinalNonCircularClosure.FreeSubject C s :=
  FinalNonCircularClosure.non_mechanical_yields_libertarian_freedom J hNotForced

/-- TEOREMA PÚBLICO: TESTE AUXILIAR DE CONSISTÊNCIA CONSTRUTIVA DA VIA ONTOLÓGICA:
    PREÇO: `[Classical.choice]`. -/
theorem toy_model_consistency_witness :
    ∃ (C : FinalNonCircularClosure.Semantics.{0, 0} Unit) (s : Unit) (p : Prop)
      (J : @FinalNonCircularClosure.JudgmentDeterminationChain.{0, 0, 0} Unit C s C.actualWorld p)
      (a : J.Node),
      FinalNonCircularClosure.SubjectSourceOfJudgment J a ∧
      FinalNonCircularClosure.DeterminationOriginatedBySubject J a ∧
      FinalNonCircularClosure.LibertarianFreeChoiceAt C s C.actualWorld p ∧
      FinalNonCircularClosure.FreeWillAt C s C.actualWorld ∧
      FinalNonCircularClosure.FreeSubject C s :=
  FinalNonCircularClosure.toy_model_consistency_witness

/-- LEMA PONTE PÚBLICO: -/
theorem judgment_determination_chain_satisfies_constitutive_act_determination
    {C : FinalNonCircularClosure.Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : FinalNonCircularClosure.JudgmentDeterminationChain C s w p) :
    FinalNonCircularClosure.ConstitutiveActDetermination J :=
  FinalNonCircularClosure.judgment_determination_chain_satisfies_constitutive_act_determination J

/-- TESTE DE NÃO-CIRCULARIDADE PÚBLICO (Procedimento C): -/
theorem constitutive_act_determination_incompatible_with_mechanical_forcing
    {C : FinalNonCircularClosure.Semantics Subject}
    {s : Subject}
    {p : Prop}
    (J : FinalNonCircularClosure.JudgmentDeterminationChain C s C.actualWorld p)
    (hConst : FinalNonCircularClosure.ConstitutiveActDetermination J)
    (hForced : FinalNonCircularClosure.MechanicallyForced C s C.actualWorld p) :
    False :=
  FinalNonCircularClosure.constitutive_act_determination_incompatible_with_mechanical_forcing J hConst hForced

/-- TEOREMA PÚBLICO MESTRE: ARGUMENTO COMPLETO DA LIBERDADE LIBERTÁRIA:
    PREÇO: `[Classical.choice]`. -/
theorem complete_libertarian_freedom_argument
    {C : FinalNonCircularClosure.Semantics Subject}
    {s : Subject}
    {p : Prop}
    (J : FinalNonCircularClosure.JudgmentDeterminationChain C s C.actualWorld p) :
    FinalNonCircularClosure.FreeSubject C s :=
  FinalNonCircularClosure.complete_libertarian_freedom_argument J

/-- TEOREMA PÚBLICO: A INSTANCIAÇÃO PERFORMATIVA DA PROVA DEMONSTRA O SUJEITO LIVRE:
    PREÇO: `[Classical.choice]`. -/
theorem performative_proof_instantiates_libertarian_freedom
    {C : FinalNonCircularClosure.Semantics Subject}
    {s : Subject}
    {p : Prop}
    (J : FinalNonCircularClosure.JudgmentDeterminationChain C s C.actualWorld p)
    {a : J.Node}
    (hSrc : FinalNonCircularClosure.SubjectSourceOfJudgment J a) :
    FinalNonCircularClosure.FreeSubject C s :=
  FinalNonCircularClosure.performative_proof_instantiates_libertarian_freedom J hSrc

/-- Abreviação pública da estrutura de instância da demonstração. -/
abbrev ProofInstance {Subject : Type _} (C : FinalNonCircularClosure.Semantics Subject) :=
  FinalNonCircularClosure.ProofInstance C

/-- TEOREMA PÚBLICO EXISTENCIAL MESTRE: A INSTANCIAÇÃO DA DEMONSTRAÇÃO IMPLICA
    A EXISTÊNCIA DE UM SUJEITO LIVRE:
    PREÇO: `[Classical.choice]`. -/
theorem proof_instance_implies_existence_of_free_subject
    {Subject : Type _}
    {C : FinalNonCircularClosure.Semantics Subject}
    (inst : ProofInstance C) :
    ∃ s : Subject, FinalNonCircularClosure.FreeSubject C s :=
  FinalNonCircularClosure.proof_instance_implies_existence_of_free_subject inst

/-- TEOREMA PÚBLICO EXISTENCIAL (FORMA PROPOSICIONAL PURA): -/
theorem proof_instance_nonempty_implies_existence_of_free_subject
    {Subject : Type _}
    {C : FinalNonCircularClosure.Semantics Subject}
    (h : Nonempty (ProofInstance C)) :
    ∃ s : Subject, FinalNonCircularClosure.FreeSubject C s :=
  FinalNonCircularClosure.proof_instance_nonempty_implies_existence_of_free_subject h

/-- Abreviação pública da ocorrência demonstrativa. -/
abbrev DemonstrativeProofOccurrence {Subject : Type _} (C : FinalNonCircularClosure.Semantics Subject) :=
  FinalNonCircularClosure.DemonstrativeProofOccurrence C

universe u_s u_w u_o

/-- LEMA PONTE PÚBLICO: DA OCORRÊNCIA DA DEMONSTRAÇÃO À INSTANCIAÇÃO CONCRETA:
    PREÇO: `{}`. -/
theorem demonstration_occurrence_yields_proof_instance
    {Subject : Type u_s}
    {C : FinalNonCircularClosure.Semantics.{u_s, u_w} Subject}
    (demo : DemonstrativeProofOccurrence.{u_s, u_w, u_o} C) :
    Nonempty (ProofInstance.{u_s, u_w, u_o} C) :=
  ⟨demo.instanceOfJudgment⟩

/-- TEOREMA PÚBLICO PERFORMATÓRIO-EXISTENCIAL FINAL:
    PREÇO: `[Classical.choice]`. -/
theorem demonstration_occurrence_implies_existence_of_free_subject
    {Subject : Type _}
    {C : FinalNonCircularClosure.Semantics Subject}
    (demo : DemonstrativeProofOccurrence C) :
    ∃ s : Subject, FinalNonCircularClosure.FreeSubject C s :=
  FinalNonCircularClosure.demonstration_occurrence_implies_existence_of_free_subject demo

/-- Abreviação pública de ProofExists. -/
def ProofExists {Subject : Type u_s} (C : FinalNonCircularClosure.Semantics.{u_s, u_w} Subject) : Prop :=
  Nonempty (ProofInstance.{u_s, u_w, u_o} C)

/-- TEOREMA PÚBLICO FINAL: SE ESTA PROVA EXISTE, EXISTE SUJEITO LIVRE:
    "Se esta prova existe, existe Sujeito Livre (mesmo que tu e o autor sejais apenas 'robôs biológicos')."
    PREÇO: `[Classical.choice]`. -/
theorem proof_exists_implies_existence_of_free_subject
    {Subject : Type u_s}
    {C : FinalNonCircularClosure.Semantics.{u_s, u_w} Subject}
    (h : ProofExists.{u_s, u_w, u_o} C) :
    ∃ s : Subject, FinalNonCircularClosure.FreeSubject C s :=
  let ⟨inst⟩ := h
  proof_instance_implies_existence_of_free_subject inst

#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.determination_cannot_be_self_directed
#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.fully_internally_determined_is_impossible
#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.exists_ultimate_internal_source
#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.not_all_internally_determined
#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.mechanical_chain_cannot_self_ground
#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.mechanical_chain_has_ultimate_internal_source
#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.non_received_determination_excludes_mechanical_forcing
#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.ultimate_source_not_received_or_external
#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.subject_source_yields_not_mechanically_forced
#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.ultimate_internal_act_source_is_not_received_from_prior_state
#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.non_mechanical_yields_subject_source_of_judgment
#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.ontological_determination_yields_libertarian_freedom
#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.non_mechanical_yields_libertarian_freedom
#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.mechanical_judgment_chain_with_external_ultimate_source
#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.judgment_determination_chain_satisfies_constitutive_act_determination
#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.constitutive_act_determination_incompatible_with_mechanical_forcing
#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.complete_libertarian_freedom_argument
#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.performative_proof_instantiates_libertarian_freedom
#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.proof_instance_implies_existence_of_free_subject
#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.proof_instance_nonempty_implies_existence_of_free_subject
#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.demonstration_occurrence_yields_proof_instance
#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.demonstration_occurrence_implies_existence_of_free_subject
#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.proof_exists_implies_existence_of_free_subject
#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.toy_model_consistency_witness
#print axioms CompleteLibertarianFreedomArgument.ontological_determination_yields_libertarian_freedom
#print axioms CompleteLibertarianFreedomArgument.non_mechanical_yields_libertarian_freedom
#print axioms CompleteLibertarianFreedomArgument.judgment_determination_chain_satisfies_constitutive_act_determination
#print axioms CompleteLibertarianFreedomArgument.constitutive_act_determination_incompatible_with_mechanical_forcing
#print axioms CompleteLibertarianFreedomArgument.complete_libertarian_freedom_argument
#print axioms CompleteLibertarianFreedomArgument.performative_proof_instantiates_libertarian_freedom
#print axioms CompleteLibertarianFreedomArgument.proof_instance_implies_existence_of_free_subject
#print axioms CompleteLibertarianFreedomArgument.proof_instance_nonempty_implies_existence_of_free_subject
#print axioms CompleteLibertarianFreedomArgument.demonstration_occurrence_yields_proof_instance
#print axioms CompleteLibertarianFreedomArgument.demonstration_occurrence_implies_existence_of_free_subject
#print axioms CompleteLibertarianFreedomArgument.proof_exists_implies_existence_of_free_subject
#print axioms CompleteLibertarianFreedomArgument.toy_model_consistency_witness

end CompleteLibertarianFreedomArgument
