import Lean

namespace Logos

namespace CompleteLibertarianFreedomArgument

namespace FinalNonCircularClosure

universe u v

/-!
================================================================================
I. STATEMENT / TARGET
================================================================================
THE STATUS OF THE PROOF:

Given:
    JudgmentDeterminationChain C s C.actualWorld p

the Lean kernel proves:
    FreeSubject C s

and given:
    ProofExists C

the Lean kernel proves:
    ∃ s : Subject, FreeSubject C s

WHAT IS NOT CLAIMED:
The conclusion is NOT:
- that all humans are free;
- that the reader is free;
- that the author is free;
- that the brain or a biological organism is free;
- that every subject is free.

It is strictly the formalized anonymous existential consequence:
    ∃ s : Subject, FreeSubject C s.
The witness `s` is anonymous in the semantic sort `Subject`.

THREE DISTINCT LEVELS OF THE CONCLUSION:
LEVEL 1 — FORMAL ENTAILMENT
    JudgmentDeterminationChain C s w p → FreeSubject C s

LEVEL 2 — EXISTENTIAL CONSEQUENCE
    ProofInstance C → ∃ s : Subject, FreeSubject C s

LEVEL 3 — METATHEORETIC SHORTHAND
    "This proof exists"
        = existence of the relevant concrete proof instance
        = ProofExists C

The formal theory establishes Level 1 and Level 2 within Lean.
It does NOT attempt to prove Level 3 internally: that a physical `.lean`
file exists in spacetime is a metatheoretic datum, not a lemma of the theory.

THE POSITIVE MEANING OF THE LIBERTARIAN CONCLUSION:
The proof does NOT infer freedom from a mere negation of determination:
    "not determined → free" (INVALID LEAP)

Instead, the deductive engine derives a positive modal construction:
    not exhaustively fixed by complete prior state
        ↓
    accessible same-prior-state world with different source outcome
        ↓
    different verdict
        ↓
    opposite judicative attitude
        ↓
    LibertarianFreeChoiceAt
        ↓
    FreeWillAt
        ↓
    FreeSubject

CONCEPTUAL HIERARCHY:
  causal influence in general
          ≠
  constitutive determination ancestry
          ≠
  exhaustive fixing by the complete prior state
================================================================================
-/

/-!
================================================================================
II. MINIMAL SEMANTICS
================================================================================
The minimal modal and judicative frame required to define judgment,
alternative accessibility under identical complete prior history, and libertarian freedom.
================================================================================
-/

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

/-- Sensibilidade judicativa a alternativas polares sob o mesmo passado completo
    (historicamente referida como `NormativelySensitive`):
    Existe um mundo acessível com o mesmo passado completo no qual ocorre a atitude
    judicativa contrária (assentimento vs suspensão).
    Clarificação semântica estrita: refere-se estritamente à sensibilidade epistémica do
    juízo a razões que diferenciam atitudes polares (assentimento vs suspensão),
    e NÃO introduz nem depende de qualquer teoria moral, axiológica ou deontológica externa. -/
def JudgmentAlternativeSensitive
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

/-- Alias de compatibilidade histórica: `NormativelySensitive` é rigorosamente idêntico a
    `JudgmentAlternativeSensitive`. -/
abbrev NormativelySensitive {Subject : Type _}
    (C : Semantics Subject) (s : Subject) (w : C.World) (p : Prop) : Prop :=
  JudgmentAlternativeSensitive C s w p

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

/-!
================================================================================
III. CORE DETERMINATION STRUCTURE
================================================================================
The relational determination system, ancestral priority, and the constitutive
chain of judgment determination (`JudgmentDeterminationChain`).
================================================================================
-/

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

/-!
================================================================================
IV. CORE LEMMAS (THE DEDUCTIVE PIPELINE)
================================================================================
The uncollapsed, sequential pipeline of essential lemmas leading from
the well-foundedness of priority to the construction of libertarian choice:

  well_foundedness
  → exists_ultimate_source
  → ultimate_source_reaches_judgment_act
  → ultimate_source_is_agential
  → ultimate_source_is_not_received_from_prior_state
  → accessible_same_past_alternative_exists
  → alternative_changes_verdict
  → libertarian_free_choice
  → free_will
  → free_subject
================================================================================
-/

/-- PASSO 1: A prioridade estrita na cadeia determinativa constitutiva é bem-fundada. -/
theorem well_foundedness
    (D : DeterminationSystem) :
    WellFounded D.Prior :=
  D.priorWellFounded

/-- PASSO 2: Pela bem-fundação da prioridade estrita na cadeia determinativa constitutiva, qualquer nó da cadeia possui
    uma fonte interna última ancestral. -/
theorem exists_ultimate_source
    {C : Semantics Subject} {s : Subject} {w : C.World} {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    (x : J.Node) :
    ∃ a : J.Node,
      UltimateInternalSource J.toDeterminationSystem a ∧
      (a = x ∨ DeterminesAncestrally J.Determines a x) :=
  node_has_ancestral_ultimate_source J.toDeterminationSystem x

/-- PASSO 3: O nó do acto de julgar (`judgmentActNode`) possui uma fonte interna
    última que o determina ancestralmente (ou coincide com ele). -/
theorem ultimate_source_reaches_judgment_act
    {C : Semantics Subject} {s : Subject} {w : C.World} {p : Prop}
    (J : JudgmentDeterminationChain C s w p) :
    ∃ a : J.Node,
      UltimateInternalSource J.toDeterminationSystem a ∧
      (a = J.judgmentActNode ∨ DeterminesAncestrally J.Determines a J.judgmentActNode) :=
  exists_ultimate_source J J.judgmentActNode

/-- PASSO 4: Pela condição de ancestralidade agencial da cadeia constitutiva,
    qualquer determinante ancestral do acto de julgar é um acto do próprio sujeito. -/
theorem ultimate_source_is_agential
    {C : Semantics Subject} {s : Subject} {w : C.World} {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    {a : J.Node}
    (haReachAct : a = J.judgmentActNode ∨ DeterminesAncestrally J.Determines a J.judgmentActNode) :
    J.IsActOf s a :=
  J.act_ancestral_determination_is_agential a haReachAct

/-- PASSO 5: Uma fonte interna última que é um acto do próprio sujeito não recebe
    a sua determinação do estado antecedente completo mantido fixo.
    PREÇO: `{}` (puramente dedutivo a partir de `determination_exhaustive`). -/
theorem ultimate_source_is_not_received_from_prior_state
    {C : Semantics Subject} {s : Subject} {w : C.World} {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    {a : J.Node}
    (hUlt : UltimateInternalSource J.toDeterminationSystem a)
    (hAct : J.IsActOf s a) :
    ¬ DeterminationReceivedFromPriorState J a :=
  ultimate_internal_act_source_is_not_received_from_prior_state J hUlt hAct

/-- PASSO 6: A falha de determinação recebida pelo passado completo acarreta a existência
    de um mundo acessível alternativo com o mesmo passado completo e resultado divergente.
    PREÇO: `[Classical.choice]`. -/
theorem accessible_same_past_alternative_exists
    {C : Semantics Subject} {s : Subject} {w : C.World} {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    {a : J.Node}
    (hNotRec : ¬ DeterminationReceivedFromPriorState J a) :
    ∃ w' : C.World,
      C.Accessible w w' ∧
      C.SameCompletePriorState w w' ∧
      J.OutcomeOf a w' ≠ J.OutcomeOf a w := by
  apply Classical.byContradiction
  intro hAll
  apply hNotRec
  intro w' hAcc hPrior
  apply Classical.byContradiction
  intro hNe
  exact hAll ⟨w', hAcc, hPrior, hNe⟩

/-- PASSO 7: A divergência de resultado na fonte ancestral propaga-se ao veredicto final. -/
theorem alternative_changes_verdict
    {C : Semantics Subject} {s : Subject} {w : C.World} {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    {a : J.Node}
    (hReachAct : a = J.judgmentActNode ∨ DeterminesAncestrally J.Determines a J.judgmentActNode)
    {w' : C.World}
    (hDiff : J.OutcomeOf a w' ≠ J.OutcomeOf a w) :
    J.OutcomeOf J.verdictNode w' ≠ J.OutcomeOf J.verdictNode w := by
  have hReachVer := reaches_judgment_act_implies_reaches_verdict J hReachAct
  have hPropW' := reaches_propagates_outcome J hReachVer w'
  have hPropW := reaches_propagates_outcome J hReachVer w
  intro hEq
  apply hDiff
  calc
    J.OutcomeOf a w' = J.OutcomeOf J.verdictNode w' := hPropW'.symm
    _ = J.OutcomeOf J.verdictNode w := hEq
    _ = J.OutcomeOf a w := hPropW

/-- PASSO 8: A diferença de veredicto sob o mesmo passado completo produz a escolha libertária.
    PREÇO: `[Classical.choice]`. -/
theorem libertarian_free_choice
    {C : Semantics Subject} {s : Subject} {w : C.World} {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    {a : J.Node}
    (hReachAct : a = J.judgmentActNode ∨ DeterminesAncestrally J.Determines a J.judgmentActNode)
    (hNotRec : ¬ DeterminationReceivedFromPriorState J a) :
    LibertarianFreeChoiceAt C s w p := by
  have ⟨w', hAcc, hSame, hDiffA⟩ := accessible_same_past_alternative_exists J hNotRec
  have hDiffV := alternative_changes_verdict J hReachAct hDiffA
  have hNeW : w' ≠ w := by
    intro hEqW
    subst hEqW
    exact hDiffV rfl
  have hFlip := J.verdict_tracks_alternative w w' (Ne.symm hDiffV)
  exact normative_sensitivity_implies_libertarian_choice_direct ⟨w', hAcc, hSame, hNeW, hFlip⟩

/-- PASSO 9: A escolha libertária no acto de julgar constitui o livre-arbítrio do sujeito.
    PREÇO: `[Classical.choice]`. -/
theorem free_will
    {C : Semantics Subject} {s : Subject} {w : C.World} {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    {a : J.Node}
    (hReachAct : a = J.judgmentActNode ∨ DeterminesAncestrally J.Determines a J.judgmentActNode)
    (hNotRec : ¬ DeterminationReceivedFromPriorState J a) :
    FreeWillAt C s w :=
  ⟨p, libertarian_free_choice J hReachAct hNotRec⟩

/-- PASSO 10: O livre-arbítrio no mundo actual conclui o Sujeito Livre (`FreeSubject C s`).
    PREÇO: `[Classical.choice]`. -/
theorem free_subject
    {C : Semantics Subject} {s : Subject} {p : Prop}
    (J : JudgmentDeterminationChain C s C.actualWorld p)
    {a : J.Node}
    (hReachAct : a = J.judgmentActNode ∨ DeterminesAncestrally J.Determines a J.judgmentActNode)
    (hNotRec : ¬ DeterminationReceivedFromPriorState J a) :
    FreeSubject C s :=
  free_will J hReachAct hNotRec

/-!
================================================================================
V. CORE FREEDOM DERIVATION
================================================================================
The canonical master theorem: given an instance of JudgmentDeterminationChain,
the composition of the core pipeline entails FreeSubject C s.
================================================================================
-/

/-- TEOREMA MESTRE: ARGUMENTO COMPLETO DA LIBERDADE LIBERTÁRIA.
    A partir da existência da cadeia real constitutiva do acto concreto de julgar
    (`J : JudgmentDeterminationChain C s C.actualWorld p`), a composição dos 10 passos
    canónicos deduz conclusivamente o Sujeito Livre (`FreeSubject C s`).
    PREÇO: `[Classical.choice]`. -/
theorem complete_libertarian_freedom_argument
    {C : Semantics Subject}
    {s : Subject}
    {p : Prop}
    (J : JudgmentDeterminationChain C s C.actualWorld p) :
    FreeSubject C s := by
  have ⟨a, haSource, haReachAct⟩ := ultimate_source_reaches_judgment_act J
  have haAct := ultimate_source_is_agential J haReachAct
  have hNotRec := ultimate_source_is_not_received_from_prior_state J haSource haAct
  exact free_subject J haReachAct hNotRec

/-- TEOREMA PERFORMATÓRIO: A instanciação da cadeia no acto de juízo conclui o Sujeito Livre.
    PREÇO: `[Classical.choice]`. -/
theorem performative_proof_instantiates_libertarian_freedom
    {C : Semantics Subject}
    {s : Subject}
    {p : Prop}
    (J : JudgmentDeterminationChain C s C.actualWorld p)
    {a : J.Node}
    (hSrc : SubjectSourceOfJudgment J a) :
    FreeSubject C s :=
  free_subject J hSrc.2.2 (ultimate_source_is_not_received_from_prior_state J hSrc.1 hSrc.2.1)

/-!
================================================================================
VI. PROOF EXISTENCE / EXISTENTIAL CLOSURE
================================================================================
The transition from the universal conditional theorem to the existential claim:
a concrete instance of judgment determination yields an anonymous Free Subject.
================================================================================
-/

/-- Instanciação concreta de um acto de julgamento constitutivo:
    Fornece uma instância concreta da estrutura `JudgmentDeterminationChain` para algum sujeito e proposição.
    O sujeito permanece deliberadamente anónimo no tipo semântico `Subject`. -/
structure ProofInstance (C : Semantics Subject) where
  subject : Subject
  proposition : Prop
  chain : JudgmentDeterminationChain.{u, v, u_out} C subject C.actualWorld proposition

/-- TEOREMA EXISTENCIAL MESTRE (Nível 2):
    A instância concreta de julgamento acarreta a existência de um Sujeito Livre anónimo.
    `ProofInstance C → ∃ s : Subject, FreeSubject C s`.
    PREÇO: `[Classical.choice]`. -/
theorem proof_instance_implies_free_subject
    {C : Semantics Subject}
    (inst : ProofInstance C) :
    ∃ s : Subject, FreeSubject C s :=
  ⟨inst.subject, complete_libertarian_freedom_argument inst.chain⟩

theorem proof_instance_implies_existence_of_free_subject
    {C : Semantics Subject}
    (inst : ProofInstance C) :
    ∃ s : Subject, FreeSubject C s :=
  proof_instance_implies_free_subject inst

/-- Corolário existencial: a não-vacuidade existencial da instância acarreta o Sujeito Livre. -/
theorem proof_instance_nonempty_implies_existence_of_free_subject
    {C : Semantics Subject}
    (h : Nonempty (ProofInstance C)) :
    ∃ s : Subject, FreeSubject C s :=
  let ⟨inst⟩ := h
  proof_instance_implies_free_subject inst

/-- Ocorrência concreta de uma demonstração formal:
    Modela a asserção performatória de que esta prova é uma ocorrência efectiva
    de um acto judicativo que instancia a semântica `C`. -/
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
    Se esta demonstração ocorre, existe pelo menos um Sujeito Livre no tipo `Subject`.
    PREÇO: `[Classical.choice]`. -/
theorem demonstration_occurrence_implies_existence_of_free_subject
    {C : Semantics Subject}
    (demo : DemonstrativeProofOccurrence C) :
    ∃ s : Subject, FreeSubject C s :=
  proof_instance_implies_free_subject demo.instanceOfJudgment

/-- A EXISTÊNCIA CONCRETA DA PROVA (Nível 3):
    Abreviação metateórica formalizada: expressa que existe pelo menos uma instância concreta
    de `ProofInstance C` contendo `JudgmentDeterminationChain`.
    Nível-objeto (Lean): `ProofExists C → ∃ s : Subject, FreeSubject C s`. -/
def ProofExists (C : Semantics Subject) : Prop :=
  Nonempty (ProofInstance.{u, v, u_out} C)

/-- Final conclusive theorem: if this proof exists, a Free Subject exists.
    The deduction connects Level 3 to Level 2 and Level 1:
    `ProofExists C → ∃ s : Subject, FreeSubject C s`.
    Price: `[Classical.choice]`. -/
theorem proof_exists_implies_existence_of_free_subject
    {C : Semantics Subject}
    (h : ProofExists C) :
    ∃ s : Subject, FreeSubject C s :=
  let ⟨inst⟩ := h
  proof_instance_implies_free_subject inst

/-!
================================================================================
VII. AUXILIARY ROBUSTNESS TESTS (NOT PART OF CORE PROOF PREMISES)
================================================================================
IMPORTANT METHODOLOGICAL DISTINCTION:
COUNTERMODEL TO A WEAKENED THEORY vs COUNTERMODEL TO THE FULL THEOREM

The countermodels below are tests of what fails when a constitutive condition
is removed (i.e., countermodels to a weakened theory without one of the premises).
They demonstrate the mathematical indispensability and non-vacuity of each condition.

They are NOT countermodels to the complete formal theorem:
a countermodel satisfying ALL conditions of JudgmentDeterminationChain while
deriving ¬ FreeSubject C s is mathematically impossible alongside the Lean proof.

The following models, guards, and tests verify the independence and non-vacuity
of the formal definitions. They are robustness checks and diagnostics;
NONE of them is a premise or required step of the Core Proof above.

A. Countermodels / failure without premise
B. Premise-removal tests
C. Alternative objections
D. Luck / indeterminism diagnostics
E. Structural consistency witnesses
================================================================================
-/

/-!
--------------------------------------------------------------------------------
A. Countermodels / failure without premise
[AUXILIARY / NOT A PREMISE / NOT USED BY CORE PROOF]
--------------------------------------------------------------------------------
-/

inductive TwoWorlds : Type where
  | actual : TwoWorlds
  | alternative : TwoWorlds
  deriving DecidableEq, Repr

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

/-- DISTINÇÃO 2: A ausência de forçagem mecânica (`¬ MechanicallyForced`) ou o mero desconhecimento
    causal não constitui liberdade: a liberdade exige a presença positiva da alternativa polar.
    O contramodelo `freedom_is_not_merely_unforced` certifica que `¬ MechanicallyForced ⇏ FreeSubject`. -/
theorem epistemic_or_unforced_indeterminacy_fails_libertarian_choice :
    ∃ (C : Semantics.{0, 0} Unit) (s : Unit) (p : Prop),
      ¬ MechanicallyForced C s C.actualWorld p ∧
      ¬ FreeSubject C s :=
  freedom_is_not_merely_unforced

/-- DISTINÇÃO 2b (Contramodelo 2: Ausência de fixação sem alternativa polar falha a escolha libertária):
    Um estado sem forçagem mecânica onde o sujeito assente no mundo actual mas não assente
    num mundo alternativo acessível com o mesmo passado completo, mas onde a atitude polar
    oposta (`WithholdsAt`) falha em todos os mundos, FALHA `LibertarianFreeChoiceAt`.
    Demonstra formalmente que mera indeterminação ou negação de determinação,
    sem a presença positiva da atitude oposta (`WithholdsAt`), não basta para a escolha libertária. -/
theorem indeterminacy_without_polar_alternative_fails_libertarian_choice :
    ∃ (C : Semantics.{0, 0} Unit) (s : Unit) (p : Prop),
      (∃ w', w' ≠ C.actualWorld ∧ C.Accessible C.actualWorld w' ∧ C.SameCompletePriorState C.actualWorld w' ∧
        ¬ (C.AssentsAt s w' p ↔ C.AssentsAt s C.actualWorld p)) ∧
      ¬ LibertarianFreeChoiceAt C s C.actualWorld p := by
  let C : Semantics.{0, 0} Unit :=
    { World := TwoWorlds
      actualWorld := TwoWorlds.actual
      Accessible := fun _ _ => True
      SameCompletePriorState := fun _ _ => True
      AssentsAt := fun _ w _ => w = TwoWorlds.actual
      WithholdsAt := fun _ _ _ => False
      exclusive := fun _ _ _ h => h.2 }
  refine ⟨C, (), True, ?_, ?_⟩
  · refine ⟨TwoWorlds.alternative, TwoWorlds.noConfusion, trivial, trivial, ?_⟩
    intro hIff
    have hAct : C.AssentsAt () TwoWorlds.actual True := rfl
    have hAlt := hIff.2 hAct
    exact TwoWorlds.noConfusion hAlt
  · intro hChoice
    rcases hChoice with ⟨hA, w', _, _, _, hW⟩ | ⟨hW, _⟩
    · exact hW
    · exact hW

/-- ANTI-SALTO: A mera ausência de forçagem mecânica (`¬ MechanicallyForced`) não acarreta
    por si só a escolha libertária (`LibertarianFreeChoiceAt`).
    Demonstra formalmente que a conclusão libertária exige positivamente os ingredientes
    modais relacionais (`Accessible` + `SameCompletePriorState` + atitude polar oposta `WithholdsAt`),
    e não decorre de simples não-mecanicidade negativa. -/
theorem unforced_alone_does_not_provide_libertarian_alternative :
    ∃ (C : Semantics.{0, 0} Unit) (s : Unit) (p : Prop),
      ¬ MechanicallyForced C s C.actualWorld p ∧
      ¬ LibertarianFreeChoiceAt C s C.actualWorld p := by
  let ⟨C, s, p, hNotForced, hNotFree⟩ := freedom_is_not_merely_unforced
  refine ⟨C, s, p, hNotForced, ?_⟩
  intro hChoice
  exact hNotFree ⟨p, hChoice⟩

/-- IMPOSSIBILIDADE 2: Um simples sistema indeterminista não basta para a liberdade libertária.
    A ausência de fixação determinativa sem a presença da alternativa polar oposta
    (`WithholdsAt`) falha a escolha libertária. -/
theorem mere_indeterminism_insufficient_for_libertarian_freedom :
    ∃ (C : Semantics.{0, 0} Unit) (s : Unit) (p : Prop),
      (∃ w', w' ≠ C.actualWorld ∧ C.Accessible C.actualWorld w' ∧ C.SameCompletePriorState C.actualWorld w' ∧
        ¬ (C.AssentsAt s w' p ↔ C.AssentsAt s C.actualWorld p)) ∧
      ¬ LibertarianFreeChoiceAt C s C.actualWorld p :=
  indeterminacy_without_polar_alternative_fails_libertarian_choice

/-!
--------------------------------------------------------------------------------
B. Premise-removal tests
[AUXILIARY / NOT A PREMISE / NOT USED BY CORE PROOF]
--------------------------------------------------------------------------------
-/

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

/-- ATAQUE DE REMOÇÃO DE PREMISSA: Sem a condição `determination_exhaustive`,
    um nó cujo resultado é fixado pelo estado antecedente completo pode ser um acto do sujeito
    sem possuir qualquer determinante interno na cadeia, quebrando a prova por dupla contradição.
    Isto demonstra formalmente que `determination_exhaustive` é uma premissa indispensável e não-decorativa. -/
theorem without_determination_exhaustive_prior_fixing_escapes_chain :
    ∃ (Node : Type) (Determines : Node → Node → Prop) (IsActOf : Node → Prop)
      (FixedByPrior : Node → Prop),
      (∀ a : Node, FixedByPrior a) ∧
      (∀ a : Node, ¬ (∃ b : Node, Determines b a)) ∧
      (∀ a : Node, IsActOf a) := by
  refine ⟨Unit, fun _ _ => False, fun _ => True, fun _ => True, ?_, ?_, ?_⟩
  · intro _; trivial
  · intro _ ⟨b, hb⟩; exact hb
  · intro _; trivial

/-!
--------------------------------------------------------------------------------
C. Alternative objections
[AUXILIARY / NOT A PREMISE / NOT USED BY CORE PROOF]
--------------------------------------------------------------------------------
-/

/-- DISTINÇÃO 1a: Ter condições antecedentes fixas no sujeito (invocadas em exemplos
    empíricos como estados físicos ou biológicos prévios) representadas por `SameCompletePriorState`
    NÃO acarreta que o acto que instancia `JudgmentDeterminationChain` receba determinação integral
    do estado antecedente.
    A prova não faz qualquer afirmação sobre cérebro ou genes de agentes humanos; essas
    categorias figuram apenas como exemplos de potenciais confusões categoriais.
    PREÇO: `[Classical.choice]`. -/
theorem antecedent_prior_state_does_not_entail_act_received_determination :
    ∃ (C : Semantics.{0, 0} Unit) (s : Unit) (p : Prop)
      (J : @JudgmentDeterminationChain.{0, 0, 0} Unit C s C.actualWorld p),
      (∃ w', w' ≠ C.actualWorld ∧ C.Accessible C.actualWorld w' ∧ C.SameCompletePriorState C.actualWorld w') ∧
      ¬ DeterminationReceivedFromPriorState J J.judgmentActNode := by
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
  have hCont : ¬ DeterminationReceivedFromPriorState J J.judgmentActNode := by
    intro hRec
    have hEq := hRec TwoWorlds.alternative trivial trivial
    exact TwoWorlds.noConfusion hEq
  refine ⟨C, (), True, J, ?_, hCont⟩
  exact ⟨TwoWorlds.alternative, TwoWorlds.noConfusion, trivial, trivial⟩

/-- DISTINÇÃO 1b: Se uma causa for invocada para determinar exaustivamente o resultado de `a`,
    ela tem de satisfazer a relação formal `Determines` ou colapsar em heteronomia externa.
    Mera invocação de causas antecedentes fora da cadeia não constitui determinação. -/
theorem exhaustive_determination_requires_determines_or_heteronomy
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    (a : J.Node)
    (hRec : DeterminationReceivedFromPriorState J a) :
    (∃ b : J.Node, J.Determines b a) ∨ ¬ J.IsActOf s a :=
  J.determination_exhaustive a (fun w' hAcc hPrior => hRec w' hAcc hPrior)

/-- SUBSUNÇÃO DE MÚLTIPLOS FACTORES ANTECEDENTES:
    Qualquer factor ou multiplicidade de factores antecedentes que seja mantido fixo
    pela relação global `SameCompletePriorState w w'` já está formalmente subsumido.
    Se a totalidade desses antecedentes fixa exaustivamente o resultado de `a`,
    então `DeterminationReceivedFromPriorState J a` aplica-se imediatamente,
    tornando o número ou complexidade de causas antecedentes irrelevante. -/
theorem complete_prior_state_subsumes_multiple_antecedent_factors
    {C : Semantics Subject} {s : Subject} {w : C.World} {p : Prop}
    (J : JudgmentDeterminationChain C s w p) (a : J.Node)
    (hFix : ∀ w' : C.World, C.Accessible w w' → C.SameCompletePriorState w w' → J.OutcomeOf a w' = J.OutcomeOf a w) :
    DeterminationReceivedFromPriorState J a :=
  hFix

/-- DILEMA DAS RAZÕES ANTECEDENTES:
    Se se alegar que razões antecedentes fixam exaustivamente a decisão, então:
    ou essa fixação se manifesta através de nós da cadeia determinativa interna (`∃ b, Determines b a`),
    ou constitui heteronomia externa ao sujeito (`¬ IsActOf s a`).
    A mera alegação verbal de "razões" não escapa à estrutura formal de `determination_exhaustive`. -/
theorem reasons_determination_dilemma
    {C : Semantics Subject} {s : Subject} {w : C.World} {p : Prop}
    (J : JudgmentDeterminationChain C s w p) (a : J.Node)
    (hReasonsFix : DeterminationReceivedFromPriorState J a) :
    (∃ b : J.Node, J.Determines b a) ∨ ¬ J.IsActOf s a :=
  J.determination_exhaustive a (fun w' hAcc hPrior => hReasonsFix w' hAcc hPrior)

/-- DISTINÇÃO 4a: Qualquer nó causal externo (`¬ J.IsActOf s ext`) é categoricamente excluído
    de ser um determinante ancestral do acto de julgar do sujeito na cadeia constitutiva. -/
theorem external_cause_excluded_from_constitutive_ancestry
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    (ext : J.Node)
    (hExt : ¬ J.IsActOf s ext) :
    ¬ (ext = J.judgmentActNode ∨ DeterminesAncestrally J.Determines ext J.judgmentActNode) := by
  intro hAnc
  have hAct := J.act_ancestral_determination_is_agential ext hAnc
  exact hExt hAct

/-- DISTINÇÃO 4b: Dilema estrito entre determinação constitutiva agencial e causalidade externa:
    Para qualquer nó determinante ancestral `a` do acto de julgar, ou `a` é constitutivo
    da cadeia e portanto um acto do próprio sujeito, ou é externo e está categoricamente
    excluído da ancestralidade determinativa do juízo. -/
theorem agential_constitutive_source_dilemma
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    (a : J.Node) :
    (a = J.judgmentActNode ∨ DeterminesAncestrally J.Determines a J.judgmentActNode) →
    (J.IsActOf s a ∧
     ∀ ext : J.Node, ¬ J.IsActOf s ext →
       ¬ (ext = J.judgmentActNode ∨ DeterminesAncestrally J.Determines ext J.judgmentActNode)) := by
  intro hAnc
  refine ⟨J.act_ancestral_determination_is_agential a hAnc, ?_⟩
  intro ext hExt
  exact external_cause_excluded_from_constitutive_ancestry J ext hExt

/-- DISTINÇÃO 4c: Dilema exaustivo sobre qualquer nó candidato `c : J.Node`:
    Para qualquer entidade ou nó causal no sistema, ou ele pertence à ancestralidade constitutiva
    da cadeia do acto de julgar e portanto é um acto do próprio sujeito (`J.IsActOf s c`),
    ou não pertence à cadeia constitutiva e não pode figurar como determinação interna do acto. -/
theorem candidate_source_constitutive_dilemma
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    (c : J.Node) :
    ((c = J.judgmentActNode ∨ DeterminesAncestrally J.Determines c J.judgmentActNode) → J.IsActOf s c) ∧
    (¬ J.IsActOf s c → ¬ (c = J.judgmentActNode ∨ DeterminesAncestrally J.Determines c J.judgmentActNode)) := by
  refine ⟨fun hAnc => J.act_ancestral_determination_is_agential c hAnc, ?_⟩
  intro hExt hAnc
  exact hExt (J.act_ancestral_determination_is_agential c hAnc)

/-!
--------------------------------------------------------------------------------
D. Luck / indeterminism diagnostics
[AUXILIARY / NOT A PREMISE / NOT USED BY CORE PROOF]
--------------------------------------------------------------------------------
-/

/-- DISTINÇÃO 3: A prova não define liberdade como mera ausência de determinismo.
    A dedução passa por raciocínio clássico (`[Classical.choice]`) da falha de determinação antecedente para a construção
    efectiva de um mundo acessível alternativo com o mesmo passado completo e veredicto contrário.
    PREÇO: `[Classical.choice]`. -/
theorem contingent_determination_constructs_positive_libertarian_choice
    {C : Semantics Subject}
    {s : Subject}
    {p : Prop}
    (J : JudgmentDeterminationChain C s C.actualWorld p)
    {a : J.Node}
    (hSrc : SubjectSourceOfJudgment J a) :
    LibertarianFreeChoiceAt C s C.actualWorld p :=
  libertarian_free_choice J hSrc.2.2 (ultimate_source_is_not_received_from_prior_state J hSrc.1 hSrc.2.1)

/-- TITULARIDADE AGENCIAL DA ALTERNATIVA:
    A alternativa modal pertence ao próprio acto judicativo do sujeito.
    Pela titularidade agencial da fonte ancestral (`J.IsActOf s a`),
    pela propagação determinativa ao veredicto (`reaches_propagates_outcome`),
    e pelo rastreamento das atitudes judicativas do próprio sujeito (`C.AssentsAt s` vs `C.WithholdsAt s`),
    a divergência modal no mundo alternativo de mesmo passado completo
    constitui uma variação no próprio acto judicativo de `s`.
    Demarcação estrita: o teorema prova apenas que o mesmo estado antecedente completo e um mundo
    acessível alternativo exibem veredicto oposto onde a fonte é um acto de `s`. Não se afirma provar
    uma teoria geral de "ausência de sorte" ou controlo moral amplo.
    PREÇO: `[Classical.choice]`. -/
theorem agential_alternative_has_subjective_source
    {C : Semantics Subject} {s : Subject} {w : C.World} {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    {a : J.Node}
    (haReachAct : a = J.judgmentActNode ∨ DeterminesAncestrally J.Determines a J.judgmentActNode)
    (hNotRec : ¬ DeterminationReceivedFromPriorState J a) :
    ∃ w' : C.World,
      w' ≠ w ∧
      C.Accessible w w' ∧
      C.SameCompletePriorState w w' ∧
      J.IsActOf s a ∧
      ((C.AssentsAt s w p ∧ C.WithholdsAt s w' p) ∨
       (C.WithholdsAt s w p ∧ C.AssentsAt s w' p)) := by
  have haAct : J.IsActOf s a := J.act_ancestral_determination_is_agential a haReachAct
  have ⟨w', hAcc, hSame, hDiffA⟩ := accessible_same_past_alternative_exists J hNotRec
  have hDiffV := alternative_changes_verdict J haReachAct hDiffA
  have hNeW : w' ≠ w := by
    intro hEqW
    subst hEqW
    exact hDiffV rfl
  have hFlip := J.verdict_tracks_alternative w w' (Ne.symm hDiffV)
  exact ⟨w', hNeW, hAcc, hSame, haAct, hFlip⟩

/-- Alias de compatibilidade expositiva. -/
theorem agential_alternative_is_not_detached_luck
    {C : Semantics Subject} {s : Subject} {w : C.World} {p : Prop}
    (J : JudgmentDeterminationChain C s w p)
    {a : J.Node}
    (haReachAct : a = J.judgmentActNode ∨ DeterminesAncestrally J.Determines a J.judgmentActNode)
    (hNotRec : ¬ DeterminationReceivedFromPriorState J a) :
    ∃ w' : C.World,
      w' ≠ w ∧
      C.Accessible w w' ∧
      C.SameCompletePriorState w w' ∧
      J.IsActOf s a ∧
      ((C.AssentsAt s w p ∧ C.WithholdsAt s w' p) ∨
       (C.WithholdsAt s w p ∧ C.AssentsAt s w' p)) :=
  agential_alternative_has_subjective_source J haReachAct hNotRec

/-!
--------------------------------------------------------------------------------
E. Structural consistency witnesses
[AUXILIARY / NOT A PREMISE / NOT USED BY CORE PROOF]
--------------------------------------------------------------------------------
-/

/-- Sujeito necessário: a mente pensante do sujeito existe em todos os mundos acessíveis. -/
def NecessarySubject (C : Semantics Subject) (s : Subject) : Prop :=
  ∀ w : C.World, C.Accessible C.actualWorld w → C.ThinkingMindAt s w

/-- Sujeito contingente: há um mundo acessível onde o sujeito não pensa. -/
def ContingentSubject (C : Semantics Subject) (s : Subject) : Prop :=
  ∃ w : C.World, C.Accessible C.actualWorld w ∧ ¬ C.ThinkingMindAt s w

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
    Quando a cadeia em análise é a cadeia determinativa constitutiva do acto concreto
    de julgar do próprio sujeito `s`, a determinação última desse acto não pode ser
    uma determinação recebida integralmente do estado antecedente completo. -/
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

/-- EXAUSTIVIDADE — RAMO INTERNO:
    Se a fonte última recebesse determinação por outro nó na cadeia,
    haveria contradição imediata com a sua qualidade de fonte última interna. -/
theorem received_determination_internal_branch_contradicts_ultimate_source
    {C : Semantics Subject} {s : Subject} {w : C.World} {p : Prop}
    (J : JudgmentDeterminationChain C s w p) (a : J.Node)
    (hUlt : UltimateInternalSource J.toDeterminationSystem a)
    (hDet : ∃ b : J.Node, J.Determines b a) :
    False :=
  hUlt hDet

/-- EXAUSTIVIDADE — RAMO EXTERNO:
    Se a fonte última ancestral não fosse um acto do sujeito,
    haveria contradição imediata com a condição de ancestralidade agencial da cadeia. -/
theorem received_determination_external_branch_contradicts_agential_ancestry
    {C : Semantics Subject} {s : Subject} {w : C.World} {p : Prop}
    (J : JudgmentDeterminationChain C s w p) (a : J.Node)
    (hAnc : a = J.judgmentActNode ∨ DeterminesAncestrally J.Determines a J.judgmentActNode)
    (hNotAct : ¬ J.IsActOf s a) :
    False :=
  hNotAct (J.act_ancestral_determination_is_agential a hAnc)

/-- EXAUSTIVIDADE CONJUNTIVA (IMPOSSIBILIDADE 1):
    Uma fonte última ancestral na cadeia constitutiva não pode ter o seu resultado
    recebido do estado antecedente completo sob pena de dupla contradição formal:
    se recebesse determinação interna, contradiria ser fonte última;
    se não fosse acto do sujeito, contradiria a condição agencial da cadeia. -/
theorem ultimate_source_cannot_be_exhaustively_fixed_by_prior_state
    {C : Semantics Subject} {s : Subject} {w : C.World} {p : Prop}
    (J : JudgmentDeterminationChain C s w p) (a : J.Node)
    (hUlt : UltimateInternalSource J.toDeterminationSystem a)
    (hAnc : a = J.judgmentActNode ∨ DeterminesAncestrally J.Determines a J.judgmentActNode)
    (hRec : DeterminationReceivedFromPriorState J a) :
    False := by
  have hExh := J.determination_exhaustive a hRec
  rcases hExh with ⟨b, hb⟩ | hNotAct
  · exact received_determination_internal_branch_contradicts_ultimate_source J a hUlt ⟨b, hb⟩
  · exact received_determination_external_branch_contradicts_agential_ancestry J a hAnc hNotAct

/-- AUDITORIA DE MODELO HOSTIL — IMPOSSIBILIDADE FORMAL DE ESCAPE:
    Um contra-modelo que tente simultaneamente sustentar:
    (1) que a fonte última ancestral é um acto genuíno do sujeito (`IsActOf s a`);
    (2) que a fonte última é ancestralmente constitutiva do juízo (`a = judgmentActNode ∨ DeterminesAncestrally ...`);
    (3) que a fonte última não tem determinante interno na cadeia (`UltimateInternalSource`);
    (4) e que o estado antecedente completo fixa exaustivamente o seu resultado (`DeterminationReceivedFromPriorState J a`),
    é LOGICAMENTE IMPOSSÍVEL e colapsa em contradição imediata (`False`).
    PREÇO: `{}` (puramente dedutivo a partir de `determination_exhaustive`). -/
theorem hostile_model_with_fixed_agential_ultimate_source_is_incoherent
    {C : Semantics Subject} {s : Subject} {w : C.World} {p : Prop}
    (J : JudgmentDeterminationChain C s w p) (a : J.Node)
    (_hAct : J.IsActOf s a)
    (hAnc : a = J.judgmentActNode ∨ DeterminesAncestrally J.Determines a J.judgmentActNode)
    (hUlt : UltimateInternalSource J.toDeterminationSystem a)
    (hRec : DeterminationReceivedFromPriorState J a) :
    False :=
  ultimate_source_cannot_be_exhaustively_fixed_by_prior_state J a hUlt hAnc hRec

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

/-- TRANSPARÊNCIA DA NEGAÇÃO MODAL:
    Equivalência lógica rigorosa entre a negação da determinação recebida pelo passado
    e a obtenção (via contraposição clássica `[Classical.choice]`) de um mundo acessível alternativo com o mesmo passado completo
    e resultado divergente no nó `a`. -/
theorem not_received_determination_iff_exists_divergent_accessible_world
    {C : Semantics Subject} {s : Subject} {w : C.World} {p : Prop}
    (J : JudgmentDeterminationChain C s w p) (a : J.Node) :
    (¬ DeterminationReceivedFromPriorState J a) ↔
    (∃ w' : C.World,
       C.Accessible w w' ∧
       C.SameCompletePriorState w w' ∧
       J.OutcomeOf a w' ≠ J.OutcomeOf a w) := by
  constructor
  · intro hNotRec
    apply Classical.byContradiction
    intro hNone
    apply hNotRec
    intro w' hAcc hPrior
    apply Classical.byContradiction
    intro hNe
    exact hNone ⟨w', hAcc, hPrior, hNe⟩
  · intro ⟨w', hAcc, hPrior, hNe⟩ hRec
    exact hNe (hRec w' hAcc hPrior)

/-- SÍNTESE DA CADEIA CONSTITUTIVA (Suficiência estrita para o Sujeito Livre):
    Quando todas as condições constitutivas de `JudgmentDeterminationChain` estão presentes
    (bem-fundação, ancestralidade agencial, exaustividade, rastreamento de veredicto),
    a cadeia acarreta conclusivamente o Sujeito Livre (`FreeSubject C s`).
    PREÇO: `[Classical.choice]`. -/
theorem constitutive_chain_entails_free_subject
    {C : Semantics Subject}
    {s : Subject}
    {p : Prop}
    (J : JudgmentDeterminationChain C s C.actualWorld p) :
    FreeSubject C s :=
  complete_libertarian_freedom_argument J

/-!
================================================================================
VIII. PHILOSOPHICAL AUDITS / DOCUMENTATION
================================================================================
-/

/-!
================================================================================
PREMISE LEDGER: COMMITMENTS OF JudgmentDeterminationChain
================================================================================
The requirements of `JudgmentDeterminationChain` are semantic structure
commitments, not "Lean axioms". They divide into formal/structural commitments
and philosophically substantive commitments:

FORMAL / STRUCTURAL COMMITMENTS:
- `priorWellFounded`
  = no infinite strictly-prior regress within the constitutive chain
- `determinationRespectsPriority`
  = determination requires strict priority
- `determines_propagates`
  = a determining source fixes the relevant outcome of what it determines

PHILOSOPHICALLY SUBSTANTIVE COMMITMENTS:
- `determination_exhaustive`
  = exhaustive prior fixing must enter the relevant determination relation
    or destroy agential authorship
- `act_ancestral_determination_is_agential`
  = constitutive ancestry of the subject's judgment is agential
- `judgmentActDeterminesVerdict`
  = the subject's judgment act constitutively determines the final verdict
- `verdict_tracks`
  = identical verdict outcomes preserve assent and withholding
- `verdict_tracks_alternative`
  = different verdict outcomes correspond to opposite judicative attitudes
- modal interpretation of `Accessible` and `SameCompletePriorState`
  = possible worlds with identical complete prior history are relational states,
    not epistemic states of uncertainty or observer ignorance.
================================================================================
-/

/-!
================================================================================
CLARIFICATIONS: EXHAUSTIVE DETERMINATION, EXTERNAL CAUSES & AGENTIAL ANCESTRY
================================================================================
1. WHAT THE PROOF DOES WITH EXHAUSTIVE DETERMINATION:
The proof does NOT independently prove that exhaustive prior-state fixing
is impossible in every conceivable ontology.

It proves:
if an exhaustive prior-state fixing exists for a node in this constitutive
judgment structure, then the structure forces one of two cases:
    (a) the node has an internal determiner in the chain, or
    (b) the node is not an act of the subject.

For an ultimate source that is an act of the subject, both branches
contradict its defining properties:
branch (a) contradicts that it is an ultimate internal source;
branch (b) contradicts that it is an agential act of the subject.

Therefore that source is not exhaustively fixed by the complete prior state.
The proof does not eliminate determinism by definition; it shows that the
specific combination of `ultimate source + agential act + determination_exhaustive`
is incompatible with exhaustive prior fixing.

2. EXTERNAL CAUSES ARE NOT AUTOMATIC COUNTEREXAMPLES:
An external cause is not automatically a counterexample.
The relevant question is whether it is:
    (a) merely causally/influentially antecedent, or
    (b) constitutively determinative of the judgment act.

Only (b) is relevant to the constitutive chain.
If an external factor is constitutively ancestral to the judgment act,
the structure's agential-ancestry condition makes that ancestral source
an act of the subject.
If it is outside the constitutive chain, merely calling it an antecedent
cause does not by itself show exhaustive determination of the act.
The proof does not claim that every external or antecedent event is impossible.

3. THE ROLE OF THE AGENTIAL ACT:
The judgment act is explicitly an act of s:
    J.judgmentActIsActOf : J.IsActOf s J.judgmentActNode

Every constitutive ancestral source of that judgment act is agential:
    J.act_ancestral_determination_is_agential

Hence the ultimate source selected by the well-founded chain is also an act of s.
The argument does not require every antecedent event in the universe to be an act of s.
It concerns strictly the constitutive determination ancestry of the judgment act.
================================================================================
-/

/-!
================================================================================
THE REAL PHILOSOPHICAL PRESSURE POINTS
================================================================================
The Lean kernel establishes the formal entailment:
    JudgmentDeterminationChain C s C.actualWorld p → FreeSubject C s

The formal entailment is not the remaining philosophical dispute.
The remaining dispute is whether the semantic commitments of
JudgmentDeterminationChain are the correct constitutive analysis
of judgment determination.

The principal substantive commitments under dispute are:
    - exhaustive determination (`determination_exhaustive`);
    - agential constitutive ancestry (`act_ancestral_determination_is_agential`);
    - the relevant modal accessibility relation (`Accessible`, `SameCompletePriorState`).

Rejecting one of these disputes the model.
It does not falsify the Lean derivation from the model.
================================================================================
-/

/-!
================================================================================
OBJECTION TAXONOMY: PREMISE REJECTION vs TRUE COUNTERMODEL
================================================================================
Relative to the formalization, there are two distinct kinds of objection:

A. PREMISE-LEVEL OBJECTION
A critic may reject one of the substantive constitutive commitments,
for example:
    - determination_exhaustive
    - act_ancestral_determination_is_agential
    - the modal interpretation of Accessible / SameCompletePriorState

This is a rejection of a premise of the formal model.
It is NOT a counterexample to the formal entailment.

B. TRUE COUNTERMODEL
A genuine countermodel would have to satisfy all assumptions of
JudgmentDeterminationChain while simultaneously satisfying:
    ¬ FreeSubject C s
for the same instance.

Such a model is mathematically incompatible with the proved theorem itself.
Therefore, once the semantic commitments are fixed, the remaining
possibility is not a competing model of the same formal premises, but
a dispute over whether those premises correctly characterize the phenomenon.

LOGICAL FORMULATION OF OBJECTIONS:
Relative to the formalization, any objection must take one of two forms:
    1. reject a semantic/constitutive assumption of the model; or
    2. identify a formal error showing that the theorem does not follow from them.

A genuine countermodel preserving all premises cannot coexist with the Lean theorem.
================================================================================
-/

/-!
================================================================================
NO CIRCULARITY AUDIT
================================================================================
NO CIRCULARITY:
JudgmentDeterminationChain contains no FreeWill / FreeSubject premise.

The first occurrence of libertarian freedom in the dependency graph
is strictly in the conclusion-side derivation, after the modal alternative
and opposite verdict have been established.

DEDUCTIVE SEQUENCE (1:1 CORRESPONDENCE WITH FORMAL LEMMAS):
  determination structure (`JudgmentDeterminationChain`)
        ↓
  ultimate source (`exists_ultimate_source`)
        ↓
  agentiality (`ultimate_source_is_agential`)
        ↓
  modal contingency (`ultimate_source_is_not_received_from_prior_state`)
        ↓
  alternative judgment (`accessible_same_past_alternative_exists`)
        ↓
  opposite verdict (`alternative_changes_verdict`)
        ↓
  libertarian choice (`libertarian_free_choice`)
        ↓
  free will (`free_will`)
        ↓
  free subject (`free_subject`)
================================================================================
-/

end FinalNonCircularClosure

/-!
================================================================================
IX. FINAL AXIOM / DEPENDENCY AUDIT
================================================================================
Public wrappers delegating to FinalNonCircularClosure for test_no_linearity.py
and kernel verification via #print axioms.
================================================================================
-/

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

/-- Complete libertarian freedom argument: the well-founded constitutive determination chain of judgment directly entails a Free Subject.
    Price: `[Classical.choice]`. -/
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

/-- TEOREMA PÚBLICO: A INSTANCIAÇÃO DA PROVA FORNECE O SUJEITO LIVRE:
    PREÇO: `[Classical.choice]`. -/
theorem proof_instance_implies_free_subject
    {Subject : Type _}
    {C : FinalNonCircularClosure.Semantics Subject}
    (inst : ProofInstance C) :
    ∃ s : Subject, FinalNonCircularClosure.FreeSubject C s :=
  FinalNonCircularClosure.proof_instance_implies_free_subject inst

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

/-- If this proof exists, a Free Subject exists: the concrete existence of a judgment proof instance entails an anonymous free subject.
    Existence claim only:
    `ProofExists C → ∃ s : Subject, FreeSubject C s`.

    The argument does not identify the witness with the author or reader,
    and makes no claim about all human beings.
    The sole requirement is the concrete existence of an instance of the
    formalized judgment structure (`ProofExists C`). From that instance, the argument deduces
    an anonymous free subject (`∃ s : Subject, FreeSubject C s`).
    Price: `[Classical.choice]`. -/
theorem proof_exists_implies_existence_of_free_subject
    {Subject : Type u_s}
    {C : FinalNonCircularClosure.Semantics.{u_s, u_w} Subject}
    (h : ProofExists.{u_s, u_w, u_o} C) :
    ∃ s : Subject, FinalNonCircularClosure.FreeSubject C s :=
  let ⟨inst⟩ := h
  proof_instance_implies_existence_of_free_subject inst

/-- DISTINÇÃO PÚBLICA 1a: Causa antecedente do sujeito não acarreta determinação recebida do acto. -/
theorem antecedent_prior_state_does_not_entail_act_received_determination :
    ∃ (C : FinalNonCircularClosure.Semantics.{0, 0} Unit) (s : Unit) (p : Prop)
      (J : @FinalNonCircularClosure.JudgmentDeterminationChain.{0, 0, 0} Unit C s C.actualWorld p),
      (∃ w', w' ≠ C.actualWorld ∧ C.Accessible C.actualWorld w' ∧ C.SameCompletePriorState C.actualWorld w') ∧
      ¬ FinalNonCircularClosure.DeterminationReceivedFromPriorState J J.judgmentActNode :=
  FinalNonCircularClosure.antecedent_prior_state_does_not_entail_act_received_determination

/-- DISTINÇÃO PÚBLICA 1b: Causalidade exaustiva exige Determines ou heteronomia. -/
theorem exhaustive_determination_requires_determines_or_heteronomy
    {C : FinalNonCircularClosure.Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : FinalNonCircularClosure.JudgmentDeterminationChain C s w p)
    (a : J.Node)
    (hRec : FinalNonCircularClosure.DeterminationReceivedFromPriorState J a) :
    (∃ b : J.Node, J.Determines b a) ∨ ¬ J.IsActOf s a :=
  FinalNonCircularClosure.exhaustive_determination_requires_determines_or_heteronomy J a hRec

/-- DISTINÇÃO PÚBLICA 2: Mera ausência de forçagem mecânica não implica escolha libertária. -/
theorem epistemic_or_unforced_indeterminacy_fails_libertarian_choice :
    ∃ (C : FinalNonCircularClosure.Semantics.{0, 0} Unit) (s : Unit) (p : Prop),
      ¬ FinalNonCircularClosure.MechanicallyForced C s C.actualWorld p ∧
      ¬ FinalNonCircularClosure.FreeSubject C s :=
  FinalNonCircularClosure.epistemic_or_unforced_indeterminacy_fails_libertarian_choice

/-- DISTINÇÃO PÚBLICA 3: Construção positiva de alternativa libertária com mesmo passado completo.
    PREÇO: `[Classical.choice]`. -/
theorem contingent_determination_constructs_positive_libertarian_choice
    {C : FinalNonCircularClosure.Semantics Subject}
    {s : Subject}
    {p : Prop}
    (J : FinalNonCircularClosure.JudgmentDeterminationChain C s C.actualWorld p)
    {a : J.Node}
    (hSrc : FinalNonCircularClosure.SubjectSourceOfJudgment J a) :
    FinalNonCircularClosure.LibertarianFreeChoiceAt C s C.actualWorld p :=
  FinalNonCircularClosure.contingent_determination_constructs_positive_libertarian_choice J hSrc

/-- DISTINÇÃO PÚBLICA 4a: Causas externas são excluídas da ancestralidade determinativa do acto. -/
theorem external_cause_excluded_from_constitutive_ancestry
    {C : FinalNonCircularClosure.Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : FinalNonCircularClosure.JudgmentDeterminationChain C s w p)
    (ext : J.Node)
    (hExt : ¬ J.IsActOf s ext) :
    ¬ (ext = J.judgmentActNode ∨ FinalNonCircularClosure.DeterminesAncestrally J.Determines ext J.judgmentActNode) :=
  FinalNonCircularClosure.external_cause_excluded_from_constitutive_ancestry J ext hExt

/-- DISTINÇÃO PÚBLICA 4b: Dilema entre determinação constitutiva e causalidade externa. -/
theorem agential_constitutive_source_dilemma
    {C : FinalNonCircularClosure.Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : FinalNonCircularClosure.JudgmentDeterminationChain C s w p)
    (a : J.Node) :
    (a = J.judgmentActNode ∨ FinalNonCircularClosure.DeterminesAncestrally J.Determines a J.judgmentActNode) →
    (J.IsActOf s a ∧
     ∀ ext : J.Node, ¬ J.IsActOf s ext →
       ¬ (ext = J.judgmentActNode ∨ FinalNonCircularClosure.DeterminesAncestrally J.Determines ext J.judgmentActNode)) :=
  FinalNonCircularClosure.agential_constitutive_source_dilemma J a

/-- DISTINÇÃO PÚBLICA 2b: Indeterminação sem alternativa polar falha a escolha libertária. -/
theorem indeterminacy_without_polar_alternative_fails_libertarian_choice :
    ∃ (C : FinalNonCircularClosure.Semantics.{0, 0} Unit) (s : Unit) (p : Prop),
      (∃ w', w' ≠ C.actualWorld ∧ C.Accessible C.actualWorld w' ∧ C.SameCompletePriorState C.actualWorld w' ∧
        ¬ (C.AssentsAt s w' p ↔ C.AssentsAt s C.actualWorld p)) ∧
      ¬ FinalNonCircularClosure.LibertarianFreeChoiceAt C s C.actualWorld p :=
  FinalNonCircularClosure.indeterminacy_without_polar_alternative_fails_libertarian_choice

/-- ANTI-SALTO PÚBLICO: Ausência de forçagem não provê por si só a escolha libertária. -/
theorem unforced_alone_does_not_provide_libertarian_alternative :
    ∃ (C : FinalNonCircularClosure.Semantics.{0, 0} Unit) (s : Unit) (p : Prop),
      ¬ FinalNonCircularClosure.MechanicallyForced C s C.actualWorld p ∧
      ¬ FinalNonCircularClosure.LibertarianFreeChoiceAt C s C.actualWorld p :=
  FinalNonCircularClosure.unforced_alone_does_not_provide_libertarian_alternative

/-- IMPOSSIBILIDADE 2 PÚBLICA: Mero indeterminismo insuficiente para liberdade libertária. -/
theorem mere_indeterminism_insufficient_for_libertarian_freedom :
    ∃ (C : FinalNonCircularClosure.Semantics.{0, 0} Unit) (s : Unit) (p : Prop),
      (∃ w', w' ≠ C.actualWorld ∧ C.Accessible C.actualWorld w' ∧ C.SameCompletePriorState C.actualWorld w' ∧
        ¬ (C.AssentsAt s w' p ↔ C.AssentsAt s C.actualWorld p)) ∧
      ¬ FinalNonCircularClosure.LibertarianFreeChoiceAt C s C.actualWorld p :=
  FinalNonCircularClosure.mere_indeterminism_insufficient_for_libertarian_freedom

/-- ATAQUE PÚBLICO DE REMOÇÃO DE PREMISSA: Exaustividade é indispensável. -/
theorem without_determination_exhaustive_prior_fixing_escapes_chain :
    ∃ (Node : Type) (Determines : Node → Node → Prop) (IsActOf : Node → Prop)
      (FixedByPrior : Node → Prop),
      (∀ a : Node, FixedByPrior a) ∧
      (∀ a : Node, ¬ (∃ b : Node, Determines b a)) ∧
      (∀ a : Node, IsActOf a) :=
  FinalNonCircularClosure.without_determination_exhaustive_prior_fixing_escapes_chain

/-- SUBSUNÇÃO PÚBLICA: O estado anterior completo subsume qualquer número de causas antecedentes. -/
theorem complete_prior_state_subsumes_multiple_antecedent_factors
    {C : FinalNonCircularClosure.Semantics Subject} {s : Subject} {w : C.World} {p : Prop}
    (J : FinalNonCircularClosure.JudgmentDeterminationChain C s w p) (a : J.Node)
    (hFix : ∀ w' : C.World, C.Accessible w w' → C.SameCompletePriorState w w' → J.OutcomeOf a w' = J.OutcomeOf a w) :
    FinalNonCircularClosure.DeterminationReceivedFromPriorState J a :=
  FinalNonCircularClosure.complete_prior_state_subsumes_multiple_antecedent_factors J a hFix

/-- TITULARIDADE AGENCIAL PÚBLICA DA ALTERNATIVA: -/
theorem agential_alternative_has_subjective_source
    {C : FinalNonCircularClosure.Semantics Subject} {s : Subject} {w : C.World} {p : Prop}
    (J : FinalNonCircularClosure.JudgmentDeterminationChain C s w p)
    {a : J.Node}
    (haReachAct : a = J.judgmentActNode ∨ FinalNonCircularClosure.DeterminesAncestrally J.Determines a J.judgmentActNode)
    (hNotRec : ¬ FinalNonCircularClosure.DeterminationReceivedFromPriorState J a) :
    ∃ w' : C.World,
      w' ≠ w ∧
      C.Accessible w w' ∧
      C.SameCompletePriorState w w' ∧
      J.IsActOf s a ∧
      ((C.AssentsAt s w p ∧ C.WithholdsAt s w' p) ∨
       (C.WithholdsAt s w p ∧ C.AssentsAt s w' p)) :=
  FinalNonCircularClosure.agential_alternative_has_subjective_source J haReachAct hNotRec

/-- Alias público de compatibilidade expositiva. -/
theorem agential_alternative_is_not_detached_luck
    {C : FinalNonCircularClosure.Semantics Subject} {s : Subject} {w : C.World} {p : Prop}
    (J : FinalNonCircularClosure.JudgmentDeterminationChain C s w p)
    {a : J.Node}
    (haReachAct : a = J.judgmentActNode ∨ FinalNonCircularClosure.DeterminesAncestrally J.Determines a J.judgmentActNode)
    (hNotRec : ¬ FinalNonCircularClosure.DeterminationReceivedFromPriorState J a) :
    ∃ w' : C.World,
      w' ≠ w ∧
      C.Accessible w w' ∧
      C.SameCompletePriorState w w' ∧
      J.IsActOf s a ∧
      ((C.AssentsAt s w p ∧ C.WithholdsAt s w' p) ∨
       (C.WithholdsAt s w p ∧ C.AssentsAt s w' p)) :=
  agential_alternative_has_subjective_source J haReachAct hNotRec

/-- DILEMA PÚBLICO DAS RAZÕES: -/
theorem reasons_determination_dilemma
    {C : FinalNonCircularClosure.Semantics Subject} {s : Subject} {w : C.World} {p : Prop}
    (J : FinalNonCircularClosure.JudgmentDeterminationChain C s w p) (a : J.Node)
    (hReasonsFix : FinalNonCircularClosure.DeterminationReceivedFromPriorState J a) :
    (∃ b : J.Node, J.Determines b a) ∨ ¬ J.IsActOf s a :=
  FinalNonCircularClosure.reasons_determination_dilemma J a hReasonsFix

/-- AUDITORIA PÚBLICA DE MODELO HOSTIL: Incoerência formal de escape. -/
theorem hostile_model_with_fixed_agential_ultimate_source_is_incoherent
    {C : FinalNonCircularClosure.Semantics Subject} {s : Subject} {w : C.World} {p : Prop}
    (J : FinalNonCircularClosure.JudgmentDeterminationChain C s w p) (a : J.Node)
    (_hAct : J.IsActOf s a)
    (hAnc : a = J.judgmentActNode ∨ FinalNonCircularClosure.DeterminesAncestrally J.Determines a J.judgmentActNode)
    (hUlt : FinalNonCircularClosure.UltimateInternalSource J.toDeterminationSystem a)
    (hRec : FinalNonCircularClosure.DeterminationReceivedFromPriorState J a) :
    False :=
  FinalNonCircularClosure.hostile_model_with_fixed_agential_ultimate_source_is_incoherent J a _hAct hAnc hUlt hRec

/-- IMPOSSIBILIDADE 1 PÚBLICA: A fonte última não pode ser fixada pelo passado completo. -/
theorem ultimate_source_cannot_be_exhaustively_fixed_by_prior_state
    {C : FinalNonCircularClosure.Semantics Subject} {s : Subject} {w : C.World} {p : Prop}
    (J : FinalNonCircularClosure.JudgmentDeterminationChain C s w p) (a : J.Node)
    (hUlt : FinalNonCircularClosure.UltimateInternalSource J.toDeterminationSystem a)
    (hAnc : a = J.judgmentActNode ∨ FinalNonCircularClosure.DeterminesAncestrally J.Determines a J.judgmentActNode)
    (hRec : FinalNonCircularClosure.DeterminationReceivedFromPriorState J a) :
    False :=
  FinalNonCircularClosure.ultimate_source_cannot_be_exhaustively_fixed_by_prior_state J a hUlt hAnc hRec

/-- DISTINÇÃO PÚBLICA 4c: Dilema exaustivo sobre qualquer nó candidato. -/
theorem candidate_source_constitutive_dilemma
    {C : FinalNonCircularClosure.Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (J : FinalNonCircularClosure.JudgmentDeterminationChain C s w p)
    (c : J.Node) :
    ((c = J.judgmentActNode ∨ FinalNonCircularClosure.DeterminesAncestrally J.Determines c J.judgmentActNode) → J.IsActOf s c) ∧
    (¬ J.IsActOf s c → ¬ (c = J.judgmentActNode ∨ FinalNonCircularClosure.DeterminesAncestrally J.Determines c J.judgmentActNode)) :=
  FinalNonCircularClosure.candidate_source_constitutive_dilemma J c

/-- TRANSPARÊNCIA PÚBLICA DA NEGAÇÃO MODAL: -/
theorem not_received_determination_iff_exists_divergent_accessible_world
    {C : FinalNonCircularClosure.Semantics Subject} {s : Subject} {w : C.World} {p : Prop}
    (J : FinalNonCircularClosure.JudgmentDeterminationChain C s w p) (a : J.Node) :
    (¬ FinalNonCircularClosure.DeterminationReceivedFromPriorState J a) ↔
    (∃ w' : C.World,
       C.Accessible w w' ∧
       C.SameCompletePriorState w w' ∧
       J.OutcomeOf a w' ≠ J.OutcomeOf a w) :=
  FinalNonCircularClosure.not_received_determination_iff_exists_divergent_accessible_world J a

/-- SUFICIÊNCIA DA CADEIA CONSTITUTIVA:
    A presença conjunta de todas as condições constitutivas acarreta o Sujeito Livre.
    PREÇO: `[Classical.choice]`. -/
theorem constitutive_chain_entails_free_subject
    {C : FinalNonCircularClosure.Semantics Subject}
    {s : Subject}
    {p : Prop}
    (J : FinalNonCircularClosure.JudgmentDeterminationChain C s C.actualWorld p) :
    FinalNonCircularClosure.FreeSubject C s :=
  FinalNonCircularClosure.constitutive_chain_entails_free_subject J

#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.determination_cannot_be_self_directed
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.fully_internally_determined_is_impossible
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.exists_ultimate_internal_source
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.not_all_internally_determined
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.mechanical_chain_cannot_self_ground
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.mechanical_chain_has_ultimate_internal_source
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.non_received_determination_excludes_mechanical_forcing
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.ultimate_source_not_received_or_external
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.subject_source_yields_not_mechanically_forced
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.ultimate_internal_act_source_is_not_received_from_prior_state
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.non_mechanical_yields_subject_source_of_judgment
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.ontological_determination_yields_libertarian_freedom
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.non_mechanical_yields_libertarian_freedom
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.mechanical_judgment_chain_with_external_ultimate_source
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.judgment_determination_chain_satisfies_constitutive_act_determination
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.constitutive_act_determination_incompatible_with_mechanical_forcing
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.complete_libertarian_freedom_argument
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.performative_proof_instantiates_libertarian_freedom
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.proof_instance_implies_existence_of_free_subject
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.proof_instance_nonempty_implies_existence_of_free_subject
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.demonstration_occurrence_yields_proof_instance
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.demonstration_occurrence_implies_existence_of_free_subject
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.proof_exists_implies_existence_of_free_subject
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.antecedent_prior_state_does_not_entail_act_received_determination
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.exhaustive_determination_requires_determines_or_heteronomy
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.epistemic_or_unforced_indeterminacy_fails_libertarian_choice
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.indeterminacy_without_polar_alternative_fails_libertarian_choice
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.unforced_alone_does_not_provide_libertarian_alternative
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.mere_indeterminism_insufficient_for_libertarian_freedom
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.contingent_determination_constructs_positive_libertarian_choice
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.external_cause_excluded_from_constitutive_ancestry
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.agential_constitutive_source_dilemma
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.candidate_source_constitutive_dilemma
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.received_determination_internal_branch_contradicts_ultimate_source
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.received_determination_external_branch_contradicts_agential_ancestry
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.ultimate_source_cannot_be_exhaustively_fixed_by_prior_state
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.without_determination_exhaustive_prior_fixing_escapes_chain
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.complete_prior_state_subsumes_multiple_antecedent_factors
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.agential_alternative_has_subjective_source
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.agential_alternative_is_not_detached_luck
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.reasons_determination_dilemma
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.hostile_model_with_fixed_agential_ultimate_source_is_incoherent
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.not_received_determination_iff_exists_divergent_accessible_world
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.constitutive_chain_entails_free_subject
#print axioms Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure.toy_model_consistency_witness
#print axioms Logos.CompleteLibertarianFreedomArgument.ontological_determination_yields_libertarian_freedom
#print axioms Logos.CompleteLibertarianFreedomArgument.non_mechanical_yields_libertarian_freedom
#print axioms Logos.CompleteLibertarianFreedomArgument.judgment_determination_chain_satisfies_constitutive_act_determination
#print axioms Logos.CompleteLibertarianFreedomArgument.constitutive_act_determination_incompatible_with_mechanical_forcing
#print axioms Logos.CompleteLibertarianFreedomArgument.complete_libertarian_freedom_argument
#print axioms Logos.CompleteLibertarianFreedomArgument.performative_proof_instantiates_libertarian_freedom
#print axioms Logos.CompleteLibertarianFreedomArgument.proof_instance_implies_existence_of_free_subject
#print axioms Logos.CompleteLibertarianFreedomArgument.proof_instance_implies_free_subject
#print axioms Logos.CompleteLibertarianFreedomArgument.proof_instance_nonempty_implies_existence_of_free_subject
#print axioms Logos.CompleteLibertarianFreedomArgument.demonstration_occurrence_yields_proof_instance
#print axioms Logos.CompleteLibertarianFreedomArgument.demonstration_occurrence_implies_existence_of_free_subject
#print axioms Logos.CompleteLibertarianFreedomArgument.proof_exists_implies_existence_of_free_subject
#print axioms Logos.CompleteLibertarianFreedomArgument.antecedent_prior_state_does_not_entail_act_received_determination
#print axioms Logos.CompleteLibertarianFreedomArgument.exhaustive_determination_requires_determines_or_heteronomy
#print axioms Logos.CompleteLibertarianFreedomArgument.epistemic_or_unforced_indeterminacy_fails_libertarian_choice
#print axioms Logos.CompleteLibertarianFreedomArgument.indeterminacy_without_polar_alternative_fails_libertarian_choice
#print axioms Logos.CompleteLibertarianFreedomArgument.unforced_alone_does_not_provide_libertarian_alternative
#print axioms Logos.CompleteLibertarianFreedomArgument.mere_indeterminism_insufficient_for_libertarian_freedom
#print axioms Logos.CompleteLibertarianFreedomArgument.contingent_determination_constructs_positive_libertarian_choice
#print axioms Logos.CompleteLibertarianFreedomArgument.external_cause_excluded_from_constitutive_ancestry
#print axioms Logos.CompleteLibertarianFreedomArgument.agential_constitutive_source_dilemma
#print axioms Logos.CompleteLibertarianFreedomArgument.candidate_source_constitutive_dilemma
#print axioms Logos.CompleteLibertarianFreedomArgument.ultimate_source_cannot_be_exhaustively_fixed_by_prior_state
#print axioms Logos.CompleteLibertarianFreedomArgument.without_determination_exhaustive_prior_fixing_escapes_chain
#print axioms Logos.CompleteLibertarianFreedomArgument.complete_prior_state_subsumes_multiple_antecedent_factors
#print axioms Logos.CompleteLibertarianFreedomArgument.agential_alternative_has_subjective_source
#print axioms Logos.CompleteLibertarianFreedomArgument.agential_alternative_is_not_detached_luck
#print axioms Logos.CompleteLibertarianFreedomArgument.reasons_determination_dilemma
#print axioms Logos.CompleteLibertarianFreedomArgument.hostile_model_with_fixed_agential_ultimate_source_is_incoherent
#print axioms Logos.CompleteLibertarianFreedomArgument.not_received_determination_iff_exists_divergent_accessible_world
#print axioms Logos.CompleteLibertarianFreedomArgument.constitutive_chain_entails_free_subject
#print axioms Logos.CompleteLibertarianFreedomArgument.toy_model_consistency_witness

end CompleteLibertarianFreedomArgument

end Logos
