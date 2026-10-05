/-
# Logos.DefinitionalMeaningRetorsion — Comparative Formalization of Definitional Choice & Retorsion

Comparative formalization module (investigations/meaning_retorsion_audit.md).

This module formalizes and audits the proposal to reach a `FreeSubject` via
definitional packaging inside intentional acts, rather than via transcendental deduction.

## Theoretical Contrast with Γ's Foundational Architecture

1. **Definitional stipulation vs. transcendental derivation**:
   In this module, `MeaningAct` contains `chooses : Chooses subject proposition` as an
   explicit record field, and `Means` is defined as the existence of such an act.
   Consequently, `means_implies_choice` is a trivial unpacking of the record field:
   freedom is postulated into the definition of meaning rather than derived.
   In Γ (`Logos.Choice`, `Logos.EpistemicNecessity`, `Logos.Agency`), `Means` is an
   uninterpreted primitive relation (`axiom Means : Subject → Prop → Prop`, VOCAB), and
   freedom is earned via the transcendental necessity of normative commitment (`ClaimsNormativeCorrectness`).

2. **Independence of freedom from retorsion**:
   In this module, `means_implies_free_subject` holds for *any* proposition `p` whatsoever:
   `Means Chooses s p → FreeSubject Chooses s`. The retorsion step (`NoMeaning`) plays zero
   inferential role in securing freedom; `retorsion_yields_free_subject` merely specializes `p`
   to `NoMeaning Chooses`.

3. **Unary content vs. incompatible alternatives**:
   Here `Chooses s p` takes a single propositional content. As documented in the 2026-09-18
   repair (`formal/Logos/Choice.lean:1-40`), unary choice collapses genuine choice into a
   determined occurrence. Genuine rational choice requires co-meaning mutually incompatible
   alternatives (`Chooses s p q := Means s p ∧ Means s q ∧ Incompatible p q`).

4. **Logical analysis of the retorsion step**:
   In the user's uncorrected draft, `retorsion` attempted to derive `False` from
   `Means Chooses s (NoMeaning Chooses)` alone by applying the definition `NoMeaning Chooses`
   as if it were an in-scope hypothesis. A subject meaning a falsehood does not derive logical
   `False`; rather, it refutes the truth of the denial (`¬ NoMeaning Chooses`, proved in
   `denial_of_meaning_is_false`). Both the corrected retorsion-under-hypothesis and the valid
   existential refutation are machine-verified below.
-/

universe u

namespace DefinitionalMeaningRetorsion

/-!
  Core semantic vocabulary.

  `Subject` is the type of possible subjects.

  `Chooses s p` means that subject `s` chooses proposition `p`
  as the content of an intentional act.
-/

variable {Subject : Type u}

variable (Chooses : Subject → Prop → Prop)

/--
A meaningful intentional act has:
  * a subject,
  * a proposition as its content,
  * and a choice of that content by the subject.
-/
structure MeaningAct where
  subject : Subject
  proposition : Prop
  chooses : Chooses subject proposition


/--
`Means s p` means that there exists a meaningful intentional act
whose subject is `s` and whose content is `p`.
-/
def Means (s : Subject) (p : Prop) : Prop :=
  Nonempty {
    a : MeaningAct Chooses //
      a.subject = s ∧ a.proposition = p
  }


/--
A proposition has meaning iff the proposition is meaningful
to at least one subject.

This is the requested "meaning is to someone" definition:
meaning is the inhabitation of the subject-relative meaning relation.
-/
def Meaning (p : Prop) : Prop :=
  Nonempty {
    s : Subject // Means Chooses s p
  }


/--
"The proposition `p` has no meaning to anyone."
-/
def NoMeaning : Prop :=
  ∀ p : Prop, ¬ Meaning Chooses p


/--
A subject who chooses some proposition possesses free will.
-/
def FreeWill (s : Subject) : Prop :=
  ∃ p : Prop, Chooses s p


/--
A free subject is a subject possessing free will.
-/
def FreeSubject (s : Subject) : Prop :=
  FreeWill Chooses s


/-!
  ---------------------------------------------------------------
  Meaning entails choice
  ---------------------------------------------------------------
-/

/--
If something means a proposition, then the subject of that meaning
has chosen that proposition.

No axiom is required: this follows by unpacking the definition of
`Means`.
-/
theorem means_implies_choice
    {s : Subject} {p : Prop}
    (h : Means Chooses s p) :
    Chooses s p := by
  rcases h with ⟨a⟩
  rcases a.property with ⟨hs, hp⟩
  simpa [hs, hp] using a.val.chooses


/--
Therefore anything that means something has a free subject.
-/
theorem means_implies_free_subject
    {s : Subject} {p : Prop}
    (h : Means Chooses s p) :
    FreeSubject Chooses s := by
  exact ⟨p, means_implies_choice Chooses h⟩


/-!
  ---------------------------------------------------------------
  Meaning is inhabited / "meaning is to someone"
  ---------------------------------------------------------------
-/

/--
If proposition `p` means something to subject `s`,
then `p` has meaning simpliciter.
-/
theorem means_implies_meaning
    {s : Subject} {p : Prop}
    (h : Means Chooses s p) :
    Meaning Chooses p := by
  exact ⟨⟨s, h⟩⟩


/--
Conversely, meaning is precisely the existence of someone
to whom the proposition means something.
-/
theorem meaning_is_to_someone
    {p : Prop}
    (h : Meaning Chooses p) :
    ∃ s : Subject, Means Chooses s p := by
  rcases h with ⟨s⟩
  exact ⟨s.val, s.property⟩


/-!
  ---------------------------------------------------------------
  RETORSION
  ---------------------------------------------------------------

  The denial is:

      NoMeaning := ∀ p, ¬ Meaning p

  Now suppose somebody actually means/asserts that proposition.

  That act itself gives:

      Meaning NoMeaning

  If `NoMeaning` were also assumed true, we would have:

      ¬ Meaning NoMeaning

  Hence contradiction.
-/

/--
If a subject means the proposition "nothing has meaning",
then the proposition "nothing has meaning" is false.

Equivalently:

    ¬ NoMeaning

This is the direct retorsive result.
-/
theorem denial_of_meaning_is_false
    {s : Subject}
    (h : Means Chooses s (NoMeaning Chooses)) :
    ¬ NoMeaning Chooses := by
  intro hNoMeaning
  have hMeaning :
      Meaning Chooses (NoMeaning Chooses) :=
    means_implies_meaning Chooses h
  exact hNoMeaning (NoMeaning Chooses) hMeaning


/--
The denial of meaning defeats itself whenever it is both meaningful and assumed true.
(Corrected version: requires hypothesis `hNoMeaning : NoMeaning Chooses`).
-/
theorem retorsion
    {s : Subject}
    (h : Means Chooses s (NoMeaning Chooses))
    (hNoMeaning : NoMeaning Chooses) :
    False := by
  have hMeaning :
      Meaning Chooses (NoMeaning Chooses) :=
    means_implies_meaning Chooses h
  exact hNoMeaning (NoMeaning Chooses) hMeaning


/--
A meaningful denial of meaning cannot be true.
-/
theorem meaningful_denial_is_impossible
    (h : ∃ s : Subject, Means Chooses s (NoMeaning Chooses))
    (hNoMeaning : NoMeaning Chooses) :
    False := by
  rcases h with ⟨s, hs⟩
  exact retorsion Chooses hs hNoMeaning


/--
The retorsive conclusion in existential form:

    If the denial of meaning is actually entertained,
    then meaning cannot fail to exist.
-/
theorem meaning_cannot_not_exist
    (h : ∃ s : Subject, Means Chooses s (NoMeaning Chooses)) :
    ¬ NoMeaning Chooses := by
  rcases h with ⟨s, hs⟩
  exact denial_of_meaning_is_false Chooses hs


/-!
  ---------------------------------------------------------------
  FREE SUBJECT
  ---------------------------------------------------------------

  The very same subject who means the denial must be a free subject,
  because meaning is defined through an intentional act containing
  that subject's choice.
-/

/--
A subject who meaningfully entertains the denial of meaning
is a free subject.
-/
theorem retorsion_yields_free_subject
    {s : Subject}
    (h : Means Chooses s (NoMeaning Chooses)) :
    FreeSubject Chooses s := by
  exact means_implies_free_subject Chooses h


/--
Therefore, if the denial of meaning is actually entertained,
there exists a free subject.
-/
theorem exists_free_subject
    (h : ∃ s : Subject, Means Chooses s (NoMeaning Chooses)) :
    ∃ s : Subject, FreeSubject Chooses s := by
  rcases h with ⟨s, hs⟩
  exact ⟨s, retorsion_yields_free_subject Chooses hs⟩


/-!
  ---------------------------------------------------------------
  THE COMPLETE RETORSIVE CHAIN
  ---------------------------------------------------------------
-/

/--
Complete result:

An actual meaningful denial of meaning entails

    1. meaning exists;
    2. the denial is false;
    3. there exists someone to whom it means;
    4. that someone chooses its content;
    5. that someone possesses free will;
    6. therefore there exists a free subject.
-/
theorem complete_retorsion
    (h : ∃ s : Subject, Means Chooses s (NoMeaning Chooses)) :
    (¬ NoMeaning Chooses) ∧
    (∃ p : Prop, Meaning Chooses p) ∧
    (∃ s : Subject, FreeSubject Chooses s) := by
  rcases h with ⟨s, hs⟩

  have hMeaning :
      Meaning Chooses (NoMeaning Chooses) :=
    means_implies_meaning Chooses hs

  have hNotNoMeaning :
      ¬ NoMeaning Chooses :=
    denial_of_meaning_is_false Chooses hs

  have hFreeSubject :
      ∃ s : Subject, FreeSubject Chooses s :=
    ⟨s, retorsion_yields_free_subject Chooses hs⟩

  exact ⟨
    hNotNoMeaning,
    ⟨NoMeaning Chooses, hMeaning⟩,
    hFreeSubject
  ⟩

end DefinitionalMeaningRetorsion
