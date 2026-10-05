universe u v

namespace CompleteLibertarianFreedomArgument

variable {Subject : Type u}

/-
========================================================================
I. SEMÂNTICA MODAL DA LIBERDADE LIBERTÁRIA
========================================================================

A liberdade libertária não será definida simplesmente como:

    "poder fazer o contrário"

deixando "poder" primitivo.

Em vez disso:

    existe um mundo alternativo possível
    acessível a partir do mundo actual,
    mantendo o mesmo estado antecedente completo,
    no qual o mesmo sujeito realiza a alternativa contrária.

Assim, a noção de alternativa aberta é explicitamente incompatibilista
com a fixação completa dos antecedentes relevantes.
========================================================================
-/

structure LibertarianChoiceSemantics (Subject : Type u) where
  World : Type v

  actualWorld : World

  Accessible : World → World → Prop

  SameCompletePriorState : World → World → Prop

  AssentsAt : Subject → World → Prop → Prop

  WithholdsAt : Subject → World → Prop → Prop

  /-
  Um mesmo sujeito, relativamente à mesma proposição e ao mesmo mundo,
  não pode simultaneamente assentir e suspender o assentimento.
  -/
  exclusive :
    ∀ s : Subject, ∀ w : World, ∀ p : Prop,
      ¬ (AssentsAt s w p ∧ WithholdsAt s w p)

/-
------------------------------------------------------------------------
II. ACTOS NO MUNDO ACTUAL
------------------------------------------------------------------------
-/

def Assents
    {Subject : Type u}
    (C : LibertarianChoiceSemantics Subject) :
    Subject → Prop → Prop :=
  fun s p =>
    C.AssentsAt s C.actualWorld p

def WithholdsAssent
    {Subject : Type u}
    (C : LibertarianChoiceSemantics Subject) :
    Subject → Prop → Prop :=

  fun s p =>
    C.WithholdsAt s C.actualWorld p

/-
------------------------------------------------------------------------
III. ALTERNATIVAS GENUINAMENTE ABERTAS
------------------------------------------------------------------------
-/

def OpenAssentAlternative
    {Subject : Type u}
    (C : LibertarianChoiceSemantics Subject)
    (s : Subject)
    (p : Prop) : Prop :=
  ∃ w : C.World,
    w ≠ C.actualWorld ∧
    C.Accessible C.actualWorld w ∧
    C.SameCompletePriorState C.actualWorld w ∧
    C.AssentsAt s w p

def OpenWithholdingAlternative
    {Subject : Type u}
    (C : LibertarianChoiceSemantics Subject)
    (s : Subject)
    (p : Prop) : Prop :=
  ∃ w : C.World,
    w ≠ C.actualWorld ∧
    C.Accessible C.actualWorld w ∧
    C.SameCompletePriorState C.actualWorld w ∧
    C.WithholdsAt s w p

/-
"Pode assentir" significa precisamente:
há uma alternativa aberta em que assente.

"Pode suspender" significa precisamente:
há uma alternativa aberta em que suspende.

Portanto estas capacidades já têm conteúdo libertário explícito.
-/

def CanAssent
    {Subject : Type u}
    (C : LibertarianChoiceSemantics Subject) :
    Subject → Prop → Prop :=
  OpenAssentAlternative C

def CanWithholdAssent
    {Subject : Type u}
    (C : LibertarianChoiceSemantics Subject) :
    Subject → Prop → Prop :=
  OpenWithholdingAlternative C

theorem can_assent_iff_open_assent
    {Subject : Type u}
    {C : LibertarianChoiceSemantics Subject}
    {s : Subject}
    {p : Prop} :
    CanAssent C s p ↔ OpenAssentAlternative C s p := by
  rfl

theorem can_withhold_iff_open_withholding
    {Subject : Type u}
    {C : LibertarianChoiceSemantics Subject}
    {s : Subject}
    {p : Prop} :
    CanWithholdAssent C s p ↔ OpenWithholdingAlternative C s p := by
  rfl

/-
Se há assentimento actual e uma alternativa de suspensão,
o mundo alternativo não pode ser o mundo actual.

A condição de w ≠ actualWorld já está incorporada na definição,
mas este teorema explicita a interpretação.
-/

theorem open_withholding_is_genuine_alternative
    {Subject : Type u}
    {C : LibertarianChoiceSemantics Subject}
    {s : Subject}
    {p : Prop}
    (h : OpenWithholdingAlternative C s p) :
    ∃ w : C.World,
      w ≠ C.actualWorld ∧
      C.Accessible C.actualWorld w ∧
      C.SameCompletePriorState C.actualWorld w ∧
      C.WithholdsAt s w p := by
  exact h

/-
========================================================================
IV. OBJECTIVIDADE E SUBJECTIVIDADE
========================================================================
-/

def EverythingIsObjective
    (ObjectiveStandard : Prop → Prop) : Prop :=
  ∀ p : Prop, ObjectiveStandard p

def GenuineNormativity
    (ObjectiveStandard : Prop → Prop) : Prop :=
  ∃ p : Prop, ObjectiveStandard p

def NoGenuineNormativity
    (ObjectiveStandard : Prop → Prop) : Prop :=
  ¬ GenuineNormativity ObjectiveStandard

def CorrectFor
    (ObjectiveStandard : Prop → Prop)
    (ForSubject : Subject → Prop → Prop) :
    Subject → Prop → Prop :=
  fun s p =>
    ObjectiveStandard p ∧
    p ∧
    ForSubject s p

theorem correct_for_implies_objective_standard
    (ObjectiveStandard : Prop → Prop)
    (ForSubject : Subject → Prop → Prop)
    {s : Subject}
    {p : Prop}
    (h : CorrectFor ObjectiveStandard ForSubject s p) :
    ObjectiveStandard p := by
  exact h.1

theorem correct_for_implies_truth
    (ObjectiveStandard : Prop → Prop)
    (ForSubject : Subject → Prop → Prop)
    {s : Subject}
    {p : Prop}
    (h : CorrectFor ObjectiveStandard ForSubject s p) :
    p := by
  exact h.2.1

theorem correct_for_implies_subject_relation
    (ObjectiveStandard : Prop → Prop)
    (ForSubject : Subject → Prop → Prop)
    {s : Subject}
    {p : Prop}
    (h : CorrectFor ObjectiveStandard ForSubject s p) :
    ForSubject s p := by
  exact h.2.2

def SubjectDependent
    (Means : Subject → Prop → Prop)
    (ForSubject : Subject → Prop → Prop)
    (s : Subject) (p : Prop) : Prop :=
  Means s p ∨ ForSubject s p

def NothingDependsOnSubject
    (Means : Subject → Prop → Prop)
    (ForSubject : Subject → Prop → Prop) : Prop :=
  ∀ s : Subject, ∀ p : Prop,
    ¬ SubjectDependent Means ForSubject s p

def StrongSubjectIndependentThesis
    (ObjectiveStandard : Prop → Prop)
    (Means : Subject → Prop → Prop)
    (ForSubject : Subject → Prop → Prop) : Prop :=
  EverythingIsObjective ObjectiveStandard ∧
  NothingDependsOnSubject Means ForSubject

theorem meaning_implies_subject_dependence
    (Means : Subject → Prop → Prop)
    (ForSubject : Subject → Prop → Prop)
    {s : Subject}
    {p : Prop}
    (hMeans : Means s p) :
    SubjectDependent Means ForSubject s p := by
  exact Or.inl hMeans

theorem correct_for_implies_subject_dependence
    (ObjectiveStandard : Prop → Prop)
    (Means : Subject → Prop → Prop)
    (ForSubject : Subject → Prop → Prop)
    {s : Subject}
    {p : Prop}
    (hCorrect : CorrectFor ObjectiveStandard ForSubject s p) :
    SubjectDependent Means ForSubject s p := by
  exact Or.inr hCorrect.2.2

/-
========================================================================
V. RETORSÃO CONTRA "NADA DEPENDE DE UM SUJEITO"
========================================================================
-/

/-!
REPAIR NOTE (2026-10-05).

The unconditional form `Means s Thesis → False` is FALSE: meaning the
thesis does not establish it (take `Means := fun _ _ => True`; the
antecedent holds and `False` does not follow). What holds is the
retorsion *given the thesis*: meaning the thesis refutes its own
`NothingDependsOnSubject` conjunct. The statement below is that true
content; the name and position are preserved.
-/

theorem strong_subject_independence_is_self_refuting
    (ObjectiveStandard : Prop → Prop)
    (ForSubject : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    {s : Subject}
    (hMeans :
      Means s
        (StrongSubjectIndependentThesis
          ObjectiveStandard
          Means
          ForSubject)) :
    ¬ StrongSubjectIndependentThesis
      ObjectiveStandard
      Means
      ForSubject := by

  intro hThesis

  have hDependent :
      SubjectDependent
        Means
        ForSubject
        s
        (StrongSubjectIndependentThesis
          ObjectiveStandard
          Means
          ForSubject) :=
    meaning_implies_subject_dependence
      Means
      ForSubject
      hMeans

  exact
    hThesis.2
      s
      (StrongSubjectIndependentThesis
        ObjectiveStandard
        Means
        ForSubject)
      hDependent

theorem no_one_can_mean_strong_subject_independence
    (ObjectiveStandard : Prop → Prop)
    (ForSubject : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    (hThesis :
      StrongSubjectIndependentThesis
        ObjectiveStandard
        Means
        ForSubject) :
    ¬ ∃ s : Subject,
        Means s
          (StrongSubjectIndependentThesis
            ObjectiveStandard
            Means
            ForSubject) := by

  intro h

  rcases h with ⟨s, hMeans⟩

  have hDependent :
      SubjectDependent
        Means
        ForSubject
        s
        (StrongSubjectIndependentThesis
          ObjectiveStandard
          Means
          ForSubject) :=
    meaning_implies_subject_dependence
      Means
      ForSubject
      hMeans

  exact
    hThesis.2
      s
      (StrongSubjectIndependentThesis
        ObjectiveStandard
        Means
        ForSubject)
      hDependent

/-
========================================================================
VI. DELIBERAÇÃO GENUÍNA
========================================================================

Deliberar sobre p:

  1. apreender alternativas;
  2. poder assentir numa alternativa aberta;
  3. poder suspender o assentimento numa alternativa aberta.

Como CanAssent e CanWithholdAssent já são modais,
a própria definição de deliberação contém a abertura libertária.
========================================================================
-/

def Deliberates
    {Subject : Type u}
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop) :
    Subject → Prop → Prop :=
  fun s p =>
    Apprehends s p ∧
    CanAssent C s p ∧
    CanWithholdAssent C s p

theorem deliberation_implies_alternative_apprehension
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    {s : Subject}
    {p : Prop}
    (h :
      Deliberates
        C
        Apprehends
        s p) :
    Apprehends s p := by
  exact h.1

theorem deliberation_implies_open_assent
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    {s : Subject}
    {p : Prop}
    (h :
      Deliberates
        C
        Apprehends
        s p) :
    OpenAssentAlternative C s p := by
  exact h.2.1

theorem deliberation_implies_open_withholding
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    {s : Subject}
    {p : Prop}
    (h :
      Deliberates
        C
        Apprehends
        s p) :
    OpenWithholdingAlternative C s p := by
  exact h.2.2

theorem deliberation_implies_can_assent
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    {s : Subject}
    {p : Prop}
    (h :
      Deliberates
        C
        Apprehends
        s p) :
    CanAssent C s p := by
  exact h.2.1

theorem deliberation_implies_can_withhold
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    {s : Subject}
    {p : Prop}
    (h :
      Deliberates
        C
        Apprehends
        s p) :
    CanWithholdAssent C s p := by
  exact h.2.2

/-
========================================================================
VII. ASSENTIMENTO RACIONAL
========================================================================
-/

def RationallyAssents
    {Subject : Type u}
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    : Subject → Prop → Prop :=
  fun s p =>
    Means s p ∧
    Assents C s p ∧
    Deliberates C Apprehends s p

theorem rational_assent_implies_meaning
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    {s : Subject}
    {p : Prop}
    (h :
      RationallyAssents
        C
        Apprehends
        Means
        s p) :
    Means s p := by
  exact h.1

theorem rational_assent_implies_actual_assent
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    {s : Subject}
    {p : Prop}
    (h :
      RationallyAssents
        C
        Apprehends
        Means
        s p) :
    Assents C s p := by
  exact h.2.1

theorem rational_assent_implies_deliberation
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    {s : Subject}
    {p : Prop}
    (h :
      RationallyAssents
        C
        Apprehends
        Means
        s p) :
    Deliberates C Apprehends s p := by
  exact h.2.2

/-
========================================================================
VIII. ESCOLHA LIVRE NO SENTIDO LIBERTÁRIO
========================================================================

Uma escolha libertária é:

  actual assent
  +
  alternativa aberta de suspensão

ou:

  actual suspensão
  +
  alternativa aberta de assentimento.

A expressão "poderia ter feito o contrário"
é portanto descarregada em uma existência explícita de outro mundo
possível com o mesmo estado antecedente completo.
========================================================================
-/

def LibertarianFreeChoice
    {Subject : Type u}
    (C : LibertarianChoiceSemantics Subject) :
    Subject → Prop → Prop :=
  fun s p =>
    (Assents C s p ∧ OpenWithholdingAlternative C s p) ∨
    (WithholdsAssent C s p ∧ OpenAssentAlternative C s p)

def Chooses
    {Subject : Type u}
    (C : LibertarianChoiceSemantics Subject) :
    Subject → Prop → Prop :=
  LibertarianFreeChoice C

def FreeWill
    {Subject : Type u}
    (C : LibertarianChoiceSemantics Subject) :
    Subject → Prop :=
  fun s =>
    ∃ p : Prop,
      LibertarianFreeChoice C s p

def FreeSubject
    {Subject : Type u}
    (C : LibertarianChoiceSemantics Subject) :
    Subject → Prop :=
  FreeWill C

/-
Pessoa = sujeito com FreeWill, como convenção terminológica desta
formalização.
-/

def Person
    {Subject : Type u}
    (C : LibertarianChoiceSemantics Subject) :
    Subject → Prop :=
  FreeSubject C

def NoFreeSubject
    {Subject : Type u}
    (C : LibertarianChoiceSemantics Subject) : Prop :=
  ∀ s : Subject,
    ¬ FreeSubject C s

theorem rational_assent_yields_libertarian_free_choice
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    {s : Subject}
    {p : Prop}
    (h :
      RationallyAssents
        C
        Apprehends
        Means
        s p) :
    LibertarianFreeChoice C s p := by

  have hAssents :
      Assents C s p :=
    rational_assent_implies_actual_assent
      C
      Apprehends
      Means
      h

  have hDeliberates :
      Deliberates C Apprehends s p :=
    rational_assent_implies_deliberation
      C
      Apprehends
      Means
      h

  have hOpenWithholding :
      OpenWithholdingAlternative C s p :=
    deliberation_implies_open_withholding
      C
      Apprehends
      hDeliberates

  exact Or.inl ⟨hAssents, hOpenWithholding⟩

theorem rational_assent_yields_libertarian_free_will
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    {s : Subject}
    {p : Prop}
    (h :
      RationallyAssents
        C
        Apprehends
        Means
        s p) :
    FreeWill C s := by

  exact ⟨p,
    rational_assent_yields_libertarian_free_choice
      C
      Apprehends
      Means
      h⟩

theorem rational_assent_yields_free_subject
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    {s : Subject}
    {p : Prop}
    (h :
      RationallyAssents
        C
        Apprehends
        Means
        s p) :
    FreeSubject C s := by

  exact
    rational_assent_yields_libertarian_free_will
      C
      Apprehends
      Means
      h

theorem rational_assent_yields_person
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    {s : Subject}
    {p : Prop}
    (h :
      RationallyAssents
        C
        Apprehends
        Means
        s p) :
    Person C s := by

  exact rational_assent_yields_free_subject
    C
    Apprehends
    Means
    h

/-
========================================================================
IX. ACTIVIDADE RACIONAL EXISTENTE
========================================================================
-/

def RationalActivityExists
    {Subject : Type u}
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop) : Prop :=
  ∃ s : Subject, ∃ p : Prop,
    RationallyAssents
      C
      Apprehends
      Means

      s p

theorem exists_free_subject_of_rational_activity
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    (hActivity :
      RationalActivityExists
        C
        Apprehends
        Means) :
    ∃ s : Subject, FreeSubject C s := by

  rcases hActivity with ⟨s, p, hRational⟩

  exact
    ⟨s,
      rational_assent_yields_free_subject
        C
        Apprehends
        Means
hRational⟩

/-
=======================================================================
X. APRESENTAÇÃO RACIONAL
========================================================================

Este é o passo performativo.

Não colocamos como axioma:

    ∃ s p, RationallyAssents s p.

Em vez disso, formalizamos o acto que está a ser afirmado:

    "este conteúdo está a ser apresentado racionalmente".

Esse acto contém exactamente:

    - significação;
    - assentimento;
    - deliberação.

Portanto ele dá origem à actividade racional sem um axioma existencial
independente.

========================================================================
-/

structure RationalPresentation
    {Subject : Type u}
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    (s : Subject)
    (p : Prop) : Prop where
  means : Means s p

  assents : Assents C s p

  deliberates :
    Deliberates C Apprehends s p

def PresentedAsRational
    {Subject : Type u}
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    (p : Prop) : Prop :=
  ∃ s : Subject,
    RationalPresentation
      C
      Apprehends
      Means
      s
      p

theorem rational_presentation_implies_rational_assent
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    {s : Subject}
    {p : Prop}
    (h :
      RationalPresentation
        C
        Apprehends
        Means
        s
        p) :
    RationallyAssents
      C
      Apprehends
      Means
      s p := by

  exact
    ⟨h.means, h.assents, h.deliberates⟩

theorem presented_as_rational_implies_rational_activity
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    {p : Prop}
    (h :
      PresentedAsRational
        C
        Apprehends
        Means
        p) :
    RationalActivityExists
      C
      Apprehends
      Means := by

  rcases h with ⟨s, hPresentation⟩

  exact
    ⟨s, p,
      rational_presentation_implies_rational_assent
        C
        Apprehends
        Means
        hPresentation⟩

/-
========================================================================
XI. A APRESENTAÇÃO RACIONAL IMPLICA LIBERDADE LIBERTÁRIA
========================================================================
-/

theorem presented_as_rational_implies_libertarian_free_subject
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    {p : Prop}
    (h :
      PresentedAsRational
        C
        Apprehends
        Means
        p) :
    ∃ s : Subject, FreeSubject C s := by

  rcases h with ⟨s, hPresentation⟩

  have hRational :
      RationallyAssents
        C
        Apprehends
        Means
        s p :=
    rational_presentation_implies_rational_assent
      C
      Apprehends
      Means
      hPresentation

  exact
    ⟨s,
      rational_assent_yields_free_subject
        C
        Apprehends
        Means
        hRational⟩

theorem presented_as_rational_implies_libertarian_free_will
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    {p : Prop}
    (h :
      PresentedAsRational
        C
        Apprehends
        Means
        p) :
    ∃ s : Subject, FreeWill C s := by


  rcases h with ⟨s, hPresentation⟩

  have hRational :
      RationallyAssents
        C
        Apprehends
        Means
        s p :=
    rational_presentation_implies_rational_assent
      C
      Apprehends
      Means
      hPresentation

  exact
    ⟨s,
      rational_assent_yields_libertarian_free_will
        C
        Apprehends
        Means
        hRational⟩

theorem presented_as_rational_implies_person
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    {p : Prop}
    (h :
      PresentedAsRational
        C
        Apprehends
        Means
        p) :
    ∃ s : Subject, Person C s := by

  rcases h with ⟨s, hPresentation⟩

  have hRational :
      RationallyAssents
        C
        Apprehends
        Means
        s p :=
    rational_presentation_implies_rational_assent
      C
      Apprehends
      Means
      hPresentation

  exact
    ⟨s,
      rational_assent_yields_person
        C
        Apprehends
        Means
        hRational⟩

/-
========================================================================
XII. "SE NADA RACIONALMENTE ASSENTE..."
========================================================================
-/

def NoRationalActivity
    {Subject : Type u}
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop) : Prop :=
  ∀ s : Subject, ∀ p : Prop,
    ¬ RationallyAssents
      C
      Apprehends
      Means
      s p

theorem no_rational_activity_blocks_rational_presentation
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    (hNoActivity :
      NoRationalActivity
        C
        Apprehends
        Means)
    {p : Prop} :
    ¬ PresentedAsRational
      C
      Apprehends
      Means
      p := by

  intro hPresentation

  rcases hPresentation with ⟨s, hP⟩

  exact
    (hNoActivity s p)
      (rational_presentation_implies_rational_assent
        C
        Apprehends
        Means
        hP)

theorem presented_rationally_refutes_no_rational_activity
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    {p : Prop}
    (hPresentation :
      PresentedAsRational
        C
        Apprehends
        Means
        p) :
    ¬ NoRationalActivity
      C
      Apprehends
      Means := by

  intro hNoActivity

  rcases hPresentation with ⟨s, hP⟩

  have hRational :
      RationallyAssents
        C
        Apprehends
        Means
        s p :=
    rational_presentation_implies_rational_assent
      C
      Apprehends
      Means
      hP

  exact
    (hNoActivity s p) hRational

/-
========================================================================
XIII. "NINGUÉM É LIVRE" NÃO PODE SER RACIONALMENTE APRESENTADO
========================================================================
-/

/-!
REPAIR NOTE (2026-10-05).

The unconditional form `RationallyAssents … → False` is FALSE: the act
of assenting to the no-freedom thesis *yields* a free subject
(`rational_assent_yields_free_subject`), and that free subject refutes
the thesis — but only *given the thesis*. What holds is the retorsion:
assent to the thesis refutes the thesis. The statements below are that
true content; names and positions are preserved.
-/

theorem rational_assent_to_no_free_subject_is_self_refuting
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    {s : Subject}
    (h :
      RationallyAssents
        C
        Apprehends
        Means
        s
        (NoFreeSubject C)) :
    ¬ NoFreeSubject C := by

  intro hNo

  have hFree :
      FreeSubject C s :=
    rational_assent_yields_free_subject
      C
      Apprehends
      Means
      h

  exact hNo s hFree

theorem rational_presentation_of_no_free_subject_is_self_refuting
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    (h :
      PresentedAsRational
        C
        Apprehends
        Means
        (NoFreeSubject C)) :
    ¬ NoFreeSubject C := by

  rcases h with ⟨s, hP⟩

  have hRational :
      RationallyAssents
        C
        Apprehends
        Means
        s
        (NoFreeSubject C) :=
    rational_presentation_implies_rational_assent
      C
      Apprehends
      Means
      hP

  exact
    rational_assent_to_no_free_subject_is_self_refuting
      C
      Apprehends
      Means
      hRational

theorem no_free_subject_cannot_be_presented_as_rational
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    (hNo : NoFreeSubject C) :
    ¬ PresentedAsRational
      C
      Apprehends
      Means
      (NoFreeSubject C) := by

  intro h

  exact
    (rational_presentation_of_no_free_subject_is_self_refuting
      C
      Apprehends
      Means
      h)
    hNo

/-
========================================================================
XIV. "NADA DEPENDE DE UM SUJEITO" NÃO PODE SER RACIONALMENTE APRESENTADO
========================================================================
-/

theorem rational_presentation_of_strong_subject_independence_is_self_refuting
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    {ObjectiveStandard : Prop → Prop}
    {ForSubject : Subject → Prop → Prop}
    (h :
      PresentedAsRational
        C
        Apprehends
        Means
        (StrongSubjectIndependentThesis
          ObjectiveStandard
          Means
          ForSubject)) :
    ¬ StrongSubjectIndependentThesis
      ObjectiveStandard
      Means
      ForSubject := by

  intro hThesis

  rcases h with ⟨s, hP⟩

  have hMeans :
      Means s
        (StrongSubjectIndependentThesis
          ObjectiveStandard
          Means
          ForSubject) :=
    hP.means

  have hDependent :
      SubjectDependent
        Means
        ForSubject
        s
        (StrongSubjectIndependentThesis
          ObjectiveStandard
          Means
          ForSubject) :=
    meaning_implies_subject_dependence
      Means
      ForSubject
      hMeans

  exact
    hThesis.2
      s
      (StrongSubjectIndependentThesis
        ObjectiveStandard
        Means
        ForSubject)
      hDependent

theorem strong_subject_independence_cannot_be_presented_as_rational
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    (ObjectiveStandard : Prop → Prop)
    (ForSubject : Subject → Prop → Prop)
    (hThesis :
      StrongSubjectIndependentThesis
        ObjectiveStandard
        Means
        ForSubject) :
    ¬ PresentedAsRational
      C
      Apprehends
      Means
      (StrongSubjectIndependentThesis
        ObjectiveStandard
        Means
        ForSubject) := by

  intro h

  exact
    (rational_presentation_of_strong_subject_independence_is_self_refuting
      C
      Apprehends
      Means
      h)
    hThesis

/-
========================================================================
XV. A NEGAÇÃO DA ACTIVIDADE RACIONAL TAMBÉM SE AUTO-REFUTA
========================================================================
-/

theorem no_rational_activity_cannot_be_presented_as_rational
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    (hNo : NoRationalActivity C Apprehends Means) :
    ¬ PresentedAsRational
      C
      Apprehends
      Means
      (NoRationalActivity
        C
        Apprehends
        Means) := by

  intro h

  exact
    (presented_rationally_refutes_no_rational_activity
      C
      Apprehends
      Means
      h)
    hNo

/-
========================================================================
XVI. NORMATIVIDADE OBJECTIVA
========================================================================
-/

def RationallyJudgesCorrectly
    {Subject : Type u}
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    (_AssentsActual : Subject → Prop → Prop)
    (ObjectiveStandard : Prop → Prop)
    (ForSubject : Subject → Prop → Prop)
    (s : Subject)
    (p : Prop) : Prop :=
  RationallyAssents
    C
    Apprehends
    Means
    s p
  ∧
  CorrectFor
    ObjectiveStandard
    ForSubject
    s p

theorem rational_correct_judgment_implies_objective_standard
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    (AssentsActual : Subject → Prop → Prop)
    {ObjectiveStandard : Prop → Prop}
    {ForSubject : Subject → Prop → Prop}
    {s : Subject}
    {p : Prop}
    (h :
      RationallyJudgesCorrectly
        C
        Apprehends
        Means
        AssentsActual
        ObjectiveStandard
        ForSubject
        s p) :
    ObjectiveStandard p := by

  exact h.2.1

theorem rational_correct_judgment_implies_truth
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    (AssentsActual : Subject → Prop → Prop)
    {ObjectiveStandard : Prop → Prop}
    {ForSubject : Subject → Prop → Prop}
    {s : Subject}
    {p : Prop}
    (h :
      RationallyJudgesCorrectly
        C
        Apprehends
        Means
        AssentsActual
        ObjectiveStandard
        ForSubject
        s p) :
    p := by

  exact h.2.2.1

theorem rational_correct_judgment_implies_subject_relation
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    (AssentsActual : Subject → Prop → Prop)
    {ObjectiveStandard : Prop → Prop}
    {ForSubject : Subject → Prop → Prop}
    {s : Subject}
    {p : Prop}
    (h :
      RationallyJudgesCorrectly
        C
        Apprehends
        Means
        AssentsActual
        ObjectiveStandard
        ForSubject
        s p) :
    ForSubject s p := by

  exact h.2.2.2

theorem exists_genuine_normativity_of_rational_correct_judgment
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    (AssentsActual : Subject → Prop → Prop)
    {ObjectiveStandard : Prop → Prop}
    {ForSubject : Subject → Prop → Prop}
    {s : Subject}
    {p : Prop}
    (h :
      RationallyJudgesCorrectly
        C
        Apprehends
        Means
        AssentsActual
        ObjectiveStandard
        ForSubject
        s p) :
    GenuineNormativity ObjectiveStandard := by

  exact
    ⟨p,
      rational_correct_judgment_implies_objective_standard
        C
        Apprehends
        Means
        AssentsActual
        h⟩

theorem no_rational_correct_judgment_under_no_normativity
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    (AssentsActual : Subject → Prop → Prop)
    {ObjectiveStandard : Prop → Prop}
    {ForSubject : Subject → Prop → Prop}
    (hNoNorm :
      NoGenuineNormativity ObjectiveStandard)
    {s : Subject}
    {p : Prop}
    (h :
      RationallyJudgesCorrectly
        C
        Apprehends
        Means
        AssentsActual
        ObjectiveStandard
        ForSubject
        s p) :
    False := by

  exact
    hNoNorm
      (exists_genuine_normativity_of_rational_correct_judgment
        C
        Apprehends
        Means
        AssentsActual
        h)

/-
========================================================================
XVII. FORMA PERFORMATIVA FINAL
========================================================================

A hipótese factual é simplesmente:

    "este argumento está efectivamente a ser apresentado como
     raciocínio racional".

A partir daí o kernel deriva:

    actividade racional
          ↓
    assentimento racional
          ↓
    deliberação genuína
          ↓
    alternativa libertária aberta
          ↓
    escolha libertária
          ↓
    FreeWill
          ↓
    FreeSubject
          ↓
    Person
========================================================================
-/

theorem complete_performative_argument
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    {ObjectiveStandard : Prop → Prop}
    {ForSubject : Subject → Prop → Prop}
    {p : Prop}
    (hNoFree : NoFreeSubject C)
    (hStrongThesis :
      StrongSubjectIndependentThesis
        ObjectiveStandard
        Means
        ForSubject)
    (hThisArgumentIsPresented :
      PresentedAsRational
        C
        Apprehends
        Means
        p) :
    (∃ s : Subject,
      FreeSubject C s)
    ∧
    (∃ s : Subject,
      FreeWill C s)
    ∧
    (∃ s : Subject,
      Person C s)
    ∧
    RationalActivityExists
      C
      Apprehends
      Means
    ∧
    ¬ NoRationalActivity
      C
      Apprehends
      Means
    ∧
    ¬ PresentedAsRational
      C
      Apprehends
      Means
      (NoFreeSubject C)
    ∧
    ¬ PresentedAsRational
      C
      Apprehends
      Means
      (StrongSubjectIndependentThesis
        ObjectiveStandard
        Means
        ForSubject) := by

  rcases hThisArgumentIsPresented with
    ⟨s, hPresentation⟩

  have hRational :
      RationallyAssents
        C
        Apprehends
        Means
        s p :=
    rational_presentation_implies_rational_assent
      C
      Apprehends
      Means
      hPresentation

  have hFree :
      FreeSubject C s :=
    rational_assent_yields_free_subject
      C
      Apprehends
      Means
      hRational

  have hWill :
      FreeWill C s :=
    rational_assent_yields_libertarian_free_will
      C
      Apprehends
      Means
      hRational

  have hPerson :
      Person C s :=
    rational_assent_yields_person
      C
      Apprehends
      Means
      hRational

  have hActivity :
      RationalActivityExists
        C
        Apprehends
        Means :=
    ⟨s, p, hRational⟩

  have hNotNoActivity :
      ¬ NoRationalActivity
        C
        Apprehends
        Means := by

    intro hNoActivity

    exact
      (hNoActivity s p) hRational

  have hNoFreePresentation :
      ¬ PresentedAsRational
        C
        Apprehends
        Means
        (NoFreeSubject C) := by

    exact
      no_free_subject_cannot_be_presented_as_rational
        C
        Apprehends
        Means
        hNoFree

  have hNoStrongPresentation :
      ¬ PresentedAsRational
        C
        Apprehends
        Means
        (StrongSubjectIndependentThesis
          ObjectiveStandard
          Means
          ForSubject) := by

    exact
      strong_subject_independence_cannot_be_presented_as_rational
        C
        Apprehends
        Means
        ObjectiveStandard
        ForSubject
        hStrongThesis

  exact
    ⟨
      ⟨s, hFree⟩,
      ⟨s, hWill⟩,
      ⟨s, hPerson⟩,
      hActivity,
      hNotNoActivity,
      hNoFreePresentation,
      hNoStrongPresentation
    ⟩

/-
========================================================================
XVIII. TEOREMA CENTRAL EM FORMA DIRECTA
========================================================================

Este é o resultado que corresponde directamente à tese:

    "Se este argumento está a ser racionalmente apresentado,
     então existe um sujeito libertariamente livre."

========================================================================
-/

theorem this_argument_implies_libertarian_freedom
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    {p : Prop}
    (hThisArgumentIsPresented :
      PresentedAsRational
        C
        Apprehends
        Means
        p) :
    ∃ s : Subject,
      FreeSubject C s := by

  exact
    presented_as_rational_implies_libertarian_free_subject
      C
      Apprehends
      Means
      hThisArgumentIsPresented

/-
========================================================================
XIX. FORMA DE RETORSÃO

A negação:

    NoFreeSubject C

não pode ser apresentada racionalmente.

Logo, se alguém racionalmente apresenta a tese:

    "ninguém é libertariamente livre",

o próprio acto realizado por ele implica:

    ∃ s, FreeSubject C s

e a tese entra em contradição performativa.
========================================================================
-/

theorem denial_of_libertarian_freedom_is_performatively_inconsistent
    (C : LibertarianChoiceSemantics Subject)
    (Apprehends : Subject → Prop → Prop)
    (Means : Subject → Prop → Prop)
    (hDenial :
      PresentedAsRational
        C
        Apprehends
        Means
        (NoFreeSubject C)) :
    ¬ NoFreeSubject C := by

  exact
    rational_presentation_of_no_free_subject_is_self_refuting
      C
      Apprehends
      Means
      hDenial

/-
========================================================================
XX. RESULTADO FINAL

A cadeia completa que o kernel verifica é:

  apresentação racional efectiva
          ↓
  actividade racional efectiva
          ↓
  assentimento racional
          ↓
  deliberação
          ↓
  apreensão de alternativas
          ↓
  assentimento aberto
          +
  suspensão aberta
          ↓
  alternativa possível com o mesmo estado antecedente completo
          ↓
  escolha libertária
          ↓
  FreeWill
          ↓
  FreeSubject
          ↓
  Person

E as negações universais correspondentes são performativamente
inapresentáveis.
========================================================================
-/

/-
================================================================================
XXV. RETORSÃO DO DETERMINISMO RADICAL
================================================================================

A questão não é:

    "Será que conseguimos DEFINIR uma escolha livre?"

Isso seria circular.

A questão é:

    "Pode uma conclusão ser apresentada como racionalmente justificada
     se o próprio juízo que a aceita for invariavelmente determinado
     pelo estado antecedente completo?"

A resposta formal é:

    se "racionalmente justificado" significa que a conclusão é aceite
    porque é vista como sustentada pelas razões apresentadas, então
    a relação racional não pode ser meramente uma relação causal cega
    entre estados antecedentes e conclusões.

Importante:
isto não transforma magicamente a metafísica libertária num teorema
da lógica proposicional. A ponte é formalizada como uma condição
constitutiva mínima da própria noção de "justificação racional".

O ganho é que a ponte já não diz simplesmente:

    "racionalidade -> liberdade"

mas:

    "ser racionalmente guiado por razões -> a razão pode fazer diferença
     no juízo".

A partir daí, sob completude binária e a semântica modal adoptada,
a liberdade libertária segue formalmente.
================================================================================
-/

/-
REPAIR NOTE (2026-10-05, integration into best.lean).

`Semantics` did not exist anywhere in the repo (`ThinkingMindAt`,
`MeansAt`, `ApprehendsAt` are new vocabulary). It is introduced here as
an *extension* of the file's `LibertarianChoiceSemantics`, so the whole
modal core (`World`, `actualWorld`, `Accessible`, `SameCompletePriorState`,
`AssentsAt`, `WithholdsAt`, `exclusive`) is inherited untouched and the
new block stays isolated inside `FinalNonCircularClosure`.

Elaboration fixes applied (all verified by `lean best.lean`):

1. `NonMechanicalImpliesNormativeSensitivity` was a `def : Prop` *applied
   as a function*. As a bare implication it is FALSE (a deviating world
   need not differ from the actual one). It is now the *theorem*
   `non_mechanical_implies_normative_sensitive`, proved constructively
   from `JudgmentComplete` (which quantifies over *every* world, hence
   also the deviant) plus irreflexivity of `Accessible` (which forces
   `w' ≠ w`).
2. `universal_mechanics_self_refuting` passed a vacuous
   `(hUniversal := fun s w p => by exact id)`. It now takes a genuine
   `(hUniversal : UniversalMechanics C)`.
3. `C.exclusive s w p` indexed the actual world where the deviant `w'`
   was required (two sites).
4. `Withholds` did not exist (`WithholdsAssent` did); it is aliased.
5. `normative_sensitivity_implies_free_will` had `{w} {p}` after an
   explicit binder; reordered.

Status ledger (nothing here is called "derived" that is not proved;
cf. AGENTS.md): the *bridge*
`RationalApprehensionIsCausallyNonEpiphenomenal` and `JudgmentComplete`
remain `def`-stipulations — they are the explicit price of the chain.
Irreflexivity of `Accessible` is an explicit structural hypothesis.
Everything else is a checked proof.
-/

namespace FinalNonCircularClosure

/-
The rational-judgment frame: the libertarian modal core plus the three
cognitive predicates (thinking, meaning, apprehension) at a world.
-/
structure Semantics (Subject : Type u) extends LibertarianChoiceSemantics Subject where
  ThinkingMindAt : Subject → World → Prop
  MeansAt : Subject → World → Prop → Prop
  ApprehendsAt : Subject → World → Prop → Prop

/-
`Withholds` is the world-indexed counterpart of the file's
`WithholdsAssent` (which fixes the world to `actualWorld`).
-/
def Withholds
    (C : Semantics Subject)
    (s : Subject)
    (p : Prop) : Prop :=
  WithholdsAssent C.toLibertarianChoiceSemantics s p


/-
Uma razão é efectiva para um juízo quando o sujeito pode estar
racionalmente orientado por ela para o resultado que adopta.

Não introduzimos `FreeSubject`, `FreeWill`, nem uma alternativa modal
nesta estrutura.
-/
structure ReasonGuidedJudgment
    (C : Semantics Subject)
    (s : Subject)
    (p : Prop) : Prop where
  thinking : C.ThinkingMindAt s C.actualWorld
  means : C.MeansAt s C.actualWorld p
  apprehends : C.ApprehendsAt s C.actualWorld p
  judgment : Assents C.toLibertarianChoiceSemantics s p ∨ Withholds C s p


/-
"Racionalmente sensível" não significa ainda libertário.

Significa apenas que o juízo é guiado pela razão apresentada, em vez
de ser simplesmente uma ocorrência causal indiferente ao seu conteúdo
racional.
-/
def RationallyReasonResponsive
    (C : Semantics Subject)
    (s : Subject)
    (p : Prop) : Prop :=
  ∃ _ : ReasonGuidedJudgment C s p,
    C.ApprehendsAt s C.actualWorld p


/-
Mecanicidade forte do juízo.

Se o juízo é mecanicamente forçado, então, mantendo exactamente
o mesmo estado antecedente completo, o resultado não pode variar.
-/
def MechanicallyForced
    (C : Semantics Subject)
    (s : Subject)
    (w : C.World)
    (p : Prop) : Prop :=
  ∀ w' : C.World,
    C.Accessible w w' →
    C.SameCompletePriorState w w' →
    (
      (C.AssentsAt s w p → C.AssentsAt s w' p) ∧
      (C.WithholdsAt s w p → C.WithholdsAt s w' p)
    )


/-
Completude do juízo:
em qualquer mundo relevante, o sujeito ou assente ou suspende.
-/
def JudgmentComplete
    (C : Semantics Subject) : Prop :=
  ∀ s : Subject, ∀ w : C.World, ∀ p : Prop,
    C.AssentsAt s w p ∨ C.WithholdsAt s w p


/-
Sensibilidade normativa:

há um mundo acessível com o mesmo passado completo no qual
o resultado contrário ocorre.
-/
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


/-
A definição modal da escolha libertária.
-/
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


def FreeWillAt
    (C : Semantics Subject)
    (s : Subject)
    (w : C.World) : Prop :=
  ∃ p : Prop, LibertarianFreeChoiceAt C s w p


def FreeSubject
    (C : Semantics Subject)
    (s : Subject) : Prop :=
  FreeWillAt C s C.actualWorld


/-
================================================================================
A PARTE MAIS IMPORTANTE:
REJEIÇÃO DO DETERMINISMO POR RETORSÃO
================================================================================

Uma apresentação racional do determinismo universal não pode tratar
a própria racionalidade como causalmente irrelevante.

Formalmente, introduzimos apenas a condição constitutiva:

    RationallyJustified
        ->
    ReasonCanMakeADifference.

Isto não contém "FreeSubject".

-/

def RationalJustificationIsReasonEffective
    (C : Semantics Subject) : Prop :=
  ∀ s : Subject,
  ∀ w : C.World,
  ∀ p : Prop,

    C.ApprehendsAt s w p →
    ¬ MechanicallyForced C s w p


/-
Esta é a versão exacta da antiga ponte.

A diferença arquitectural é importante:

ela não é escondida dentro de `RationalPresentation`.

É uma tese independente sobre o significado de justificação racional.
-/
def RationalApprehensionIsCausallyNonEpiphenomenal
    (C : Semantics Subject) : Prop :=
  RationalJustificationIsReasonEffective C


/-
================================================================================
LEMA FUNDAMENTAL
================================================================================

Se a actividade racional inclui uma apreensão genuína e se essa
apreensão é racionalmente efectiva, então o juízo não é mecanicamente
forçado.

Isto é simples aplicação da ponte, não uma definição de liberdade.
-/
theorem rational_apprehension_implies_not_mechanically_forced
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (hBridge :
      RationalApprehensionIsCausallyNonEpiphenomenal C)
    (hApprehends :
      C.ApprehendsAt s w p) :
    ¬ MechanicallyForced C s w p := by
  exact hBridge s w p hApprehends


/-
================================================================================
NÃO-MECANICIDADE -> SENSIBILIDADE NORMATIVA
================================================================================

Aqui fazemos a ponte modal explicitamente.

Se um juízo é não-mecanicamente-forçado, então deve existir uma
alternativa acessível com exactamente o mesmo passado completo.

Prova: a não-mecanicidade dá um mundo desviante acessível (extracção
`¬∀ → ∃¬`, passo clássico); a irreflexividade de `Accessible` força-o a
diferir do actual; a completude — que vale em *todos* os mundos, logo
também no desviante — fixa o resultado contrário; a exclusividade
elimina o ramo errado.
-/
theorem non_mechanical_implies_normative_sensitive
    (C : Semantics Subject)
    (hComplete : JudgmentComplete C)
    (hIrreflex : ∀ w : C.World, ¬ C.Accessible w w)
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (h : ¬ MechanicallyForced C s w p) :
    NormativelySensitive C s w p := by

  have hex : ∃ w' : C.World,
      C.Accessible w w' ∧
      C.SameCompletePriorState w w' ∧
      ¬ ((C.AssentsAt s w p → C.AssentsAt s w' p) ∧
         (C.WithholdsAt s w p → C.WithholdsAt s w' p)) := by
    classical
    by_cases hAll : ∃ w' : C.World,
        C.Accessible w w' ∧
        C.SameCompletePriorState w w' ∧
        ¬ ((C.AssentsAt s w p → C.AssentsAt s w' p) ∧
           (C.WithholdsAt s w p → C.WithholdsAt s w' p))
    · exact hAll
    · exfalso
      apply h
      intro w' hAcc hPrior
      by_cases hCon : (C.AssentsAt s w p → C.AssentsAt s w' p) ∧
                      (C.WithholdsAt s w p → C.WithholdsAt s w' p)
      · exact hCon
      · exact False.elim (hAll ⟨w', hAcc, hPrior, hCon⟩)

  rcases hex with ⟨w', hAcc, hPrior, hNot⟩

  have hne : w' ≠ w := by
    intro heq
    subst heq
    exact hIrreflex _ hAcc

  have hExcl : ¬ (C.AssentsAt s w p ∧ C.WithholdsAt s w p) :=
    C.exclusive s w p

  rcases hComplete s w p with hA | hW

  · have hNW : ¬ C.WithholdsAt s w p := fun hW => hExcl ⟨hA, hW⟩
    have hStep : ¬ (C.AssentsAt s w p → C.AssentsAt s w' p) := by
      intro hImp
      exact hNot ⟨hImp, fun hW => absurd hW hNW⟩
    have hNA' : ¬ C.AssentsAt s w' p := fun hA' => hStep (fun _ => hA')
    rcases hComplete s w' p with hA' | hW'
    · exact absurd hA' hNA'
    · exact ⟨w', hAcc, hPrior, hne, Or.inl ⟨hA, hW'⟩⟩

  · have hNA : ¬ C.AssentsAt s w p := fun hA => hExcl ⟨hA, hW⟩
    have hStep : ¬ (C.WithholdsAt s w p → C.WithholdsAt s w' p) := by
      intro hImp
      exact hNot ⟨fun hA => absurd hA hNA, hImp⟩
    have hNW' : ¬ C.WithholdsAt s w' p := fun hW' => hStep (fun _ => hW')
    rcases hComplete s w' p with hA' | hW'
    · exact ⟨w', hAcc, hPrior, hne, Or.inr ⟨hW, hA'⟩⟩
    · exact absurd hW' hNW'


/-
================================================================================
SENSIBILIDADE NORMATIVA -> ESCOLHA LIBERTÁRIA
================================================================================
-/

theorem normative_sensitivity_implies_libertarian_choice
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (hComplete : JudgmentComplete C)
    (hSensitive :
      NormativelySensitive C s w p) :
    LibertarianFreeChoiceAt C s w p := by

  rcases hSensitive with
    ⟨w', hAccessible, hPrior, hDifferent, hContrary⟩

  have hActual :
      C.AssentsAt s w p ∨ C.WithholdsAt s w p :=
    hComplete s w p

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


/-
================================================================================
ESCOLHA -> FREE WILL -> FREE SUBJECT
================================================================================
-/

theorem normative_sensitivity_implies_free_will
    {C : Semantics Subject}
    {s : Subject}
    {w : C.World}
    {p : Prop}
    (hComplete : JudgmentComplete C)
    (hSensitive :
      NormativelySensitive C s w p) :
    FreeWillAt C s w := by
  exact ⟨
    p,
    normative_sensitivity_implies_libertarian_choice
      hComplete
      hSensitive
  ⟩


theorem normative_sensitivity_implies_free_subject
    {C : Semantics Subject}
    {s : Subject}
    {p : Prop}
    (hComplete : JudgmentComplete C)
    (hSensitive :
      NormativelySensitive C s C.actualWorld p) :
    FreeSubject C s := by
  exact normative_sensitivity_implies_free_will
    hComplete
    hSensitive


/-
================================================================================
TEOREMA CENTRAL
================================================================================

Racionalidade genuína + ponte de efectividade racional
+ completude modal
=> sujeito livre.

Não há `FreeSubject` na apresentação racional.
-/
theorem rational_apprehension_implies_free_subject
    {C : Semantics Subject}
    (hComplete : JudgmentComplete C)
    (hIrreflex : ∀ w : C.World, ¬ C.Accessible w w)
    (hBridge :
      RationalApprehensionIsCausallyNonEpiphenomenal C)
    {s : Subject}
    {p : Prop}
    (hApprehends :
      C.ApprehendsAt s C.actualWorld p) :
    FreeSubject C s := by

  have hNotForced :
      ¬ MechanicallyForced
        C s C.actualWorld p :=
    rational_apprehension_implies_not_mechanically_forced
      hBridge
      hApprehends

  have hSensitive :
      NormativelySensitive
        C s C.actualWorld p :=
    non_mechanical_implies_normative_sensitive
      C
      hComplete
      hIrreflex
      hNotForced

  exact normative_sensitivity_implies_free_subject
    hComplete
    hSensitive


/-
A sensibilidade racional (o juízo guiado pela razão) também chega a
sujeito livre — isto dá uso a `RationallyReasonResponsive`, que de outro
modo ficaria declarada mas nunca utilizada.
-/
theorem rationally_reason_responsive_implies_free_subject
    {C : Semantics Subject}
    (hComplete : JudgmentComplete C)
    (hIrreflex : ∀ w : C.World, ¬ C.Accessible w w)
    (hBridge :
      RationalApprehensionIsCausallyNonEpiphenomenal C)
    {s : Subject}
    {p : Prop}
    (hResp :
      RationallyReasonResponsive C s p) :
    FreeSubject C s := by
  rcases hResp with ⟨hGuided, hApprehends⟩
  exact rational_apprehension_implies_free_subject
    hComplete
    hIrreflex
    hBridge
    hApprehends


/-
================================================================================
RETORSÃO CONTRA O DETERMINISMO UNIVERSAL
================================================================================

UniversalMechanics:
todo juízo é mecanicamente forçado.

Se existe uma apresentação racional efectiva de qualquer juízo,
a ponte diz que esse mesmo juízo NÃO é mecanicamente forçado.

Contradição.
-/
def UniversalMechanics
    (C : Semantics Subject) : Prop :=
  ∀ s : Subject,
  ∀ w : C.World,
  ∀ p : Prop,
    MechanicallyForced C s w p


theorem rational_presentation_defeats_universal_mechanics
    {C : Semantics Subject}
    (hUniversal :
      UniversalMechanics C)
    (hBridge :
      RationalApprehensionIsCausallyNonEpiphenomenal C)
    {s : Subject}
    {p : Prop}
    (hApprehends :
      C.ApprehendsAt s C.actualWorld p) :
    False := by

  have hForced :
      MechanicallyForced C s C.actualWorld p :=
    hUniversal s C.actualWorld p

  have hNotForced :
      ¬ MechanicallyForced C s C.actualWorld p :=
    hBridge s C.actualWorld p hApprehends

  exact hNotForced hForced


/-
================================================================================
A AUTO-APLICAÇÃO
================================================================================

Se o próprio determinismo universal é apresentado racionalmente,
então ele próprio está sujeito à sua condição racional.

Logo:

    "tudo é mecanicamente determinado"

não pode ser simultaneamente uma apresentação racional efectiva.
-/
structure RationalPresentation
    (C : Semantics Subject)
    (s : Subject)
    (p : Prop) : Prop where
  thinking :
    C.ThinkingMindAt s C.actualWorld
  means :
    C.MeansAt s C.actualWorld p
  apprehends :
    C.ApprehendsAt s C.actualWorld p
  judgment :
    C.AssentsAt s C.actualWorld p ∨
    C.WithholdsAt s C.actualWorld p


/-
NOTE (2026-10-05): `UniversalMechanicsCannotBeRationallyPresented`
(`¬ ∃ s, RationalPresentation C s (UniversalMechanics C)`) is kept as
the stated *denial* position. It does NOT follow from the bridge plus
universality alone (those give `Presentation → False`, i.e. the three
cannot stand together — that is `universal_mechanics_self_refuting`
below). It is the claim the determinist must deny at the price
identified in `final_critic_dilemma`.
-/
def UniversalMechanicsCannotBeRationallyPresented
    (C : Semantics Subject) : Prop :=
  ¬ ∃ s : Subject,
      RationalPresentation C s (UniversalMechanics C)


theorem universal_mechanics_self_refuting
    {C : Semantics Subject}
    (hBridge :
      RationalApprehensionIsCausallyNonEpiphenomenal C)
    (hUniversal :
      UniversalMechanics C)
    (hPresentation :
      ∃ s : Subject,
        RationalPresentation C s (UniversalMechanics C)) :
    False := by

  rcases hPresentation with ⟨s, hPres⟩

  exact rational_presentation_defeats_universal_mechanics
    hUniversal
    hBridge
    hPres.apprehends


/-
================================================================================
A DILEMA FINAL
================================================================================

O crítico tem exactamente duas opções:

  1. aceitar que uma apreensão racional genuína é racionalmente efectiva;
     então a conclusão libertária segue;

  2. rejeitar isso.

Mas a segunda opção tem um preço filosófico muito preciso:
ela implica que uma pessoa pode apresentar uma razão como razão,
mas que a sua apreensão da razão nunca pode fazer qualquer diferença
para o seu juízo.

Isto já não é uma defesa normal do determinismo:
é a tese de que a racionalidade é causalmente epifenoménica.
-/
theorem final_critic_dilemma
    {C : Semantics Subject}
    (hComplete : JudgmentComplete C)
    (hIrreflex : ∀ w : C.World, ¬ C.Accessible w w)
    (hRationalPresentation :
      ∃ s : Subject,
        RationalPresentation C s (UniversalMechanics C)) :
    (¬ RationalApprehensionIsCausallyNonEpiphenomenal C)
    ∨
    (∃ s : Subject, FreeSubject C s) := by

  classical

  by_cases hBridge :
      RationalApprehensionIsCausallyNonEpiphenomenal C

  · rcases hRationalPresentation with ⟨s, hPres⟩

    have hApp : C.ApprehendsAt s C.actualWorld (UniversalMechanics C) :=
      hPres.apprehends

    have hFree : FreeSubject C s :=
      rational_apprehension_implies_free_subject
        hComplete
        hIrreflex
        hBridge
        hApp

    exact Or.inr ⟨s, hFree⟩

  · exact Or.inl hBridge


/-
================================================================================
FORMA MAIS FORTE DO RESULTADO
================================================================================

Se aceitarmos a constituição mínima da racionalidade:

    apreensão racional genuína
        ->
    não-epifenomenalidade racional
        ->
    não-mecanicidade
        ->
    sensibilidade normativa
        ->
    alternativa com mesmo passado completo
        ->
    escolha libertária
        ->
    FreeWill
        ->
    FreeSubject
        ->
    Person

então a conclusão é kernel-forced.
================================================================================
-/

end FinalNonCircularClosure

-- ---------------------------------------------------------------------------
-- Axiom-footprint audit for the new section (repo convention; informational:
-- best.lean is outside the lake build, so these are not consumed by any
-- script — cf. AGENTS.md sync rule, which governs formal/ only).
-- ---------------------------------------------------------------------------
#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.rational_apprehension_implies_not_mechanically_forced
#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.non_mechanical_implies_normative_sensitive
#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.normative_sensitivity_implies_libertarian_choice
#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.normative_sensitivity_implies_free_will
#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.normative_sensitivity_implies_free_subject
#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.rational_apprehension_implies_free_subject
#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.rationally_reason_responsive_implies_free_subject
#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.rational_presentation_defeats_universal_mechanics
#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.universal_mechanics_self_refuting
#print axioms CompleteLibertarianFreedomArgument.FinalNonCircularClosure.final_critic_dilemma

end CompleteLibertarianFreedomArgument


