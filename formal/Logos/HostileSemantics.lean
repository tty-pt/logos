/-
# Logos.HostileSemantics — Reconstruction of the core under hostile semantics

Addresses foundational conflations in the formalization:
1. Distinguishes a theorem derived from premises from a theorem true because
   the datatype/definition was constructed to contain the witness.
2. Destroys the constructed Cogito witness (`Sum.inl ()`, "silent origin").
   Evaluates what genuinely follows from the performative act-datum `hAct : ∃ s p, A s p`.
3. Mathematical proof that one act cannot logically imply plurality
   (Unit countermodel: `S := Unit`, `A () True := True`, `Person () := True`).
4. Demolition of `everyContentIsAPerson`: tests `Person` as an uninterpreted predicate
   and proves that propositional existence does not imply personhood.
5. Hostile separation theorems over explicit abstract interfaces:
   - Act does not imply Person
   - Act does not imply Plurality
   - Act does not imply genuine choice (`Chooses`) nor FreeWill
   - Content does not imply Personhood

   Freedom/choice fix (2026-09-18): the old `not_entails_freewill` treated
   `Chooses` and `FreeWill` as independent predicates. In Logos `FreeWill` is
   now *defined* from `Chooses` (`Choice.chooses_implies_freeWill`), so that
   abstract model no longer bears on `Chooses ↛ FreeWill` — it only shows a
   *decoupled* FreeWill-predicate is unforced. It is renamed
   `not_entails_decoupled_freewill` and the concrete model below proves the
   honest separation `Act ↛ Chooses`.
6. Semantic attacks on uniform grounding (C18), ultimate ground (C79/C89),
   personal ground (T8), and love (T13/T14).
7. Semantic attack on the necessity lift (batches esse-est-agere / lift-necessário):
   subject-persistence (`NecessarySubject` in the general signature) does not
   entail entity-necessity (`NecessaryEntity`) by logic alone — the lift
   `Modal.subject_nec_entity_nec` (C91) is definitional, not a logical law
   (`CountermodelSubjectNecessityNotEntityNecessity`). Step-6 verdict
   (2026-09-18): person-persistence (`AxPersonStability`) is *definitional*
   too — abstract `Person` does not logically force `NecessarySubject`
   (`CountermodelPersonNotNecessary.not_entails_person_necessary`); the
concrete countermodel `Person s ∧ ¬ NecessarySubject s` cannot exist
    (`Love.no_contingent_person`).
8. Veridical-meaning attack on the choice frontier (milestone 2026-09-18):
   the act-datum does NOT force `genuineChoice_exists` even under the *Logos*
   definition of `Chooses` (co-meaned incompatible contents). `Means` may be
   *veridical* (`Means s p → p`), and veridicality makes two-horned meaning
   impossible (`Choice.genuineChoice_requires_error_possibility`), while
   assertion is truth-laden and hence single-horned by definition
   (`Choice.assertion_consistency` /
   `Choice.no_one_asserts_incompatible_pair`). The concrete model
   `CountermodelVeridicalMeaning` satisfies the whole agency/choice/order
   fragment (act datum, plurality, right-and-wrong, `judge_commits`,
   fallibility) with genuine choice empty; the abstract signatures
   `not_entails_genuine_choice(_with_plurality)` state the non-entailment.
   The frontier's single irreducible resource is same-subject co-meaning of a
   negation (`Choice.rejectedHornCoMeant`, BLOCKED).
9. Personhood frontier (milestone 2026-09-18): the chain
   `Act → SubjectExists → Intentional → Person` is a chain of *definitional
   identities* in Logos (every node unfolds to `∃ p, Means s p`);
   `Person.person_intentional_iff` makes the §12 bridge explicit. NO hostile
   model attacks that identity — it is a fact about the definitions. The
   models in Part A2 attack only the STRONGER SUBSTANTIVE readings of
   personhood (self-reflection, deliberative rationality, autonomous agency,
   full moral responsibility): the performative datum does
   not force any of them, each via a DISTINCT model that preserves the other
   predicates (orthogonal matrix).
10. Semantic selection frontier (milestone 2026-09-18 / F1b reopening):
    separates Alternatives (`ChoiceField`) → Selection (`Selects`) → Free Choice (`FreeWill`).
    While bare meaning does not force selection (`CountermodelOmniMeaning`: an
    omni-entertaining subject represents all contents without rejecting any),
    assertion constitutively entails semantic selection (`Choice.asserts_selects`).
    However, semantic selection does NOT force genuine choice (co-meaning both horns)
    nor libertarian free will: `CountermodelVeridicalMeaning.Single` satisfies
    `Selects () True False` while `Chooses` and `FreeWill` are identically empty,
    and abstract signatures formalize the non-entailments.
-/

import Logos.Core
import Logos.Alternatives

namespace Logos.HostileSemantics

-- ===========================================================================
-- Part A: Abstract Signature and Formal Non-Entailment Theorems
-- ===========================================================================

structure CoreSignature where
  Subject : Type
  A : Subject → Prop → Prop
  Means : Subject → Prop → Prop
  Person : Subject → Prop
  Chooses : Subject → Prop → Prop → Prop
  FreeWill : Subject → Prop

def Γ_act (I : CoreSignature) : Prop :=
  ∃ s : I.Subject, ∃ p : Prop, I.A s p

def Γ_means (I : CoreSignature) : Prop :=
  ∀ s p, I.A s p → I.Means s p

def Γ_person (I : CoreSignature) : Prop :=
  Γ_act I ∧ Γ_means I

def PersonExistence (I : CoreSignature) : Prop :=
  ∃ s : I.Subject, I.Person s

def TwoPersons (I : CoreSignature) : Prop :=
  ∃ s₁ s₂ : I.Subject, I.Person s₁ ∧ I.Person s₂ ∧ s₁ ≠ s₂

def FreeWillExistence (I : CoreSignature) : Prop :=
  ∃ s : I.Subject, I.FreeWill s

/-- Separation Theorem 1: Act does not logically imply Personhood.

    Audit notice (personhood frontier, 2026-09-18): this targets the
    SUBSTANTIVE reading of `Person` — an uninterpreted, independent predicate
    (deliberation, responsibility, self-reflection, ...). It is NOT a
    countermodel to the Logos nominal identity `Person ↔ Intentional`
    (`Person.person_intentional_iff`): in Logos `Person` unfolds to
    `∃ p, Means s p`, so the formal implication `Act → Person` holds
    definitionally. Formal derivability ≠ semantic neutrality of the
    definition. -/
theorem not_entails_person :
    ¬ (∀ I : CoreSignature, Γ_person I → PersonExistence I) := by
  intro h
  let I : CoreSignature := {
    Subject := Unit
    A := fun _ _ => True
    Means := fun _ _ => True
    Person := fun _ => False
    Chooses := fun _ _ _ => True
    FreeWill := fun _ => False
  }
  have hΓ : Γ_person I := ⟨⟨(), True, trivial⟩, fun _ _ _ => trivial⟩
  have hNot : ¬ PersonExistence I := fun ⟨_, hp⟩ => hp
  exact hNot (h I hΓ)

/-- Separation Theorem 2: Act and single personhood do not logically imply Plurality. -/
theorem not_entails_plurality :
    ¬ (∀ I : CoreSignature, Γ_act I ∧ (∃ s : I.Subject, I.Person s) → TwoPersons I) := by
  intro h
  let I : CoreSignature := {
    Subject := Unit
    A := fun _ _ => True
    Means := fun _ _ => True
    Person := fun _ => True
    Chooses := fun _ _ _ => True
    FreeWill := fun _ => False
  }
  have hΓ : Γ_act I ∧ (∃ s : I.Subject, I.Person s) :=
    ⟨⟨(), True, trivial⟩, ⟨(), trivial⟩⟩
  have hNot : ¬ TwoPersons I := by
    intro ⟨s₁, s₂, _, _, hne⟩
    cases s₁; cases s₂
    exact hne rfl
  exact hNot (h I hΓ)

/-- Separation Theorem 3 (decoupled form): a `FreeWill` predicate treated as
    *independent* of `Chooses` is not implied by act + choice.

  Audit notice (freedom/choice fix, 2026-09-18): this is NOT a countermodel to
    `Chooses ↛ FreeWill`. In Logos `FreeWill` is *defined* from `Chooses`
    (`Choice.FreeWill s := ∃ p q, Chooses s p q`), so no Logos-model can set
    `FreeWill := False` while `Chooses` holds. The model below only shows that
    an abstract signature which decouples the two predicates does not force the
    link — i.e. the link in Logos is definitional, not logical. Kept as a
    precise statement of what the old F1b "block" actually established. -/
theorem not_entails_decoupled_freewill :
    ¬ (∀ I : CoreSignature, Γ_act I ∧ (∀ s : I.Subject, I.Person s → ∃ p q, I.Chooses s p q) → FreeWillExistence I) := by
  intro h
  let I : CoreSignature := {
    Subject := Unit
    A := fun _ _ => True
    Means := fun _ _ => True
    Person := fun _ => True
    Chooses := fun _ _ _ => True
    FreeWill := fun _ => False
  }
  have hΓ : Γ_act I ∧ (∀ s : I.Subject, I.Person s → ∃ p q, I.Chooses s p q) :=
    ⟨⟨(), True, trivial⟩, fun _ _ => ⟨True, True, trivial⟩⟩
  have hNot : ¬ FreeWillExistence I := fun ⟨_, hfw⟩ => hfw
  exact hNot (h I hΓ)

/-- Separation Theorem 4: Content existence and meaning do not logically imply Personhood. -/
theorem not_entails_content_person :
    ¬ (∀ (S : Type) (Means : S → Prop → Prop) (Person : S → Prop),
        (∃ _p : Prop, True) ∧ (∀ p : Prop, ∃ s : S, Means s p) → (∃ s : S, Person s)) := by
  intro h
  let S : Type := Prop
  let Means : S → Prop → Prop := fun s p => s = p
  let Person : S → Prop := fun _ => False
  have hPremise : (∃ _p : Prop, True) ∧ (∀ p : Prop, ∃ s : S, Means s p) :=
    ⟨⟨True, trivial⟩, fun p => ⟨p, rfl⟩⟩
  have hNot : ¬ (∃ s : S, Person s) := fun ⟨_, hp⟩ => hp
  exact hNot (h S Means Person hPremise)

-- ===========================================================================
-- Part A2: Personhood frontier — formal identity vs substantive reading
-- ===========================================================================
--
-- Logos *defines* the chain `Act → SubjectExists → Intentional → Person`:
-- every node unfolds to `∃ p, Means s p` (Act s p := Means s p,
-- SubjectExists s := ∃ p, Act s p, Intentional s := ∃ p, Means s p, and
-- Person s := Agent s ∧ Rational s ∧ Intentional s with Agent/Rational
-- analytic True). Hence `Person ↔ Intentional`
-- (`Person.person_intentional_iff`) and the arrows are definitional
-- identities -- model-independent, NOT hostile-separable. NO model below
-- attacks that identity. What Part A2 attacks is the STRONGER semantic
-- readings that the §12 label "person" must not smuggle in: self-reflection
-- (inner awareness), deliberative rationality, autonomous agency, and full
-- moral personhood (responsibility). Under those readings none of the arrows
-- hold: the performative datum forces only the actualized meaning-subject.
-- Each separation theorem uses a DISTINCT model that preserves the other
-- substantive predicates (strongest minimal witnesses), so the matrix is
-- orthogonal: no four copies of one model.

/-- Substantive readings of the personhood vocabulary, kept LOCAL to the
    hostile models (NO new Logos formal predicate): `Mind` = reflective
    intentionality (inner awareness), `Ratio` = deliberative rationality,
    `Auto` = autonomous agency, `Degree` = full moral personhood
    (responsibility). -/
structure SubstantivePersonhood where
  Subject : Type
  Act : Subject → Prop → Prop
  Mind : Subject → Prop
  Ratio : Subject → Prop
  Auto : Subject → Prop
  Degree : Subject → Prop

def SubstantiveDatum (I : SubstantivePersonhood) : Prop :=
  ∃ s : I.Subject, ∃ p : Prop, I.Act s p

def SubstantiveMind (I : SubstantivePersonhood) : Prop := ∃ s : I.Subject, I.Mind s
def SubstantiveRatio (I : SubstantivePersonhood) : Prop := ∃ s : I.Subject, I.Ratio s
def SubstantiveAuto (I : SubstantivePersonhood) : Prop := ∃ s : I.Subject, I.Auto s
def SubstantiveDegree (I : SubstantivePersonhood) : Prop := ∃ s : I.Subject, I.Degree s

/-- Separation (reflective intentionality): the act-datum does NOT force
    inner awareness — not even in a deliberatively rational autonomous
    agent (`Ratio`/`Auto` present, `Mind` empty). NOT a countermodel to
    Logos `Intentional` (which is definitionally `∃ p, Means s p` — see
    `Person.act_implies_intentional`). -/
theorem not_entails_substantive_intentionality :
    ¬ (∀ I : SubstantivePersonhood, SubstantiveDatum I → SubstantiveMind I) := by
  intro h
  let I : SubstantivePersonhood := {
    Subject := Unit
    Act := fun _ _ => True
    Mind := fun _ => False
    Ratio := fun _ => True
    Auto := fun _ => True
    Degree := fun _ => False
  }
  have hd : SubstantiveDatum I := ⟨(), True, trivial⟩
  have hn : ¬ SubstantiveMind I := fun ⟨_, hm⟩ => hm
  exact hn (h I hd)

/-- Separation (deliberative rationality): the act-datum does NOT force
    deliberative rationality — not even in a self-aware autonomous agent
    (`Mind`/`Auto` present, `Ratio` empty). NOT a countermodel to Logos
    `Rational` (analytic `:= True`). -/
theorem not_entails_substantive_rationality :
    ¬ (∀ I : SubstantivePersonhood, SubstantiveDatum I → SubstantiveRatio I) := by
  intro h
  let I : SubstantivePersonhood := {
    Subject := Unit
    Act := fun _ _ => True
    Mind := fun _ => True
    Ratio := fun _ => False
    Auto := fun _ => True
    Degree := fun _ => False
  }
  have hd : SubstantiveDatum I := ⟨(), True, trivial⟩
  have hn : ¬ SubstantiveRatio I := fun ⟨_, hr⟩ => hr
  exact hn (h I hd)

/-- Separation (autonomous agency): the act-datum does NOT force autonomous
    agency — not even in a self-aware deliberative agent (`Mind`/`Ratio`
    present, `Auto` empty). NOT a countermodel to Logos `Agent` (analytic
    `:= True`). -/
theorem not_entails_substantive_autonomy :
    ¬ (∀ I : SubstantivePersonhood, SubstantiveDatum I → SubstantiveAuto I) := by
  intro h
  let I : SubstantivePersonhood := {
    Subject := Unit
    Act := fun _ _ => True
    Mind := fun _ => True
    Ratio := fun _ => True
    Auto := fun _ => False
    Degree := fun _ => False
  }
  have hd : SubstantiveDatum I := ⟨(), True, trivial⟩
  have hn : ¬ SubstantiveAuto I := fun ⟨_, ha⟩ => ha
  exact hn (h I hd)

/-- Separation (substantive personhood): the act-datum does NOT force a full
    moral person — not even with self-awareness, deliberative rationality
    and autonomous agency ALL present (`Mind`/`Ratio`/`Auto` full,
    `Degree` empty). Honest restatement of `not_entails_person` framed
    against the Logos nominal identity: it targets the SUBSTANTIVE reading;
    it is NOT a countermodel to `Person ↔ Intentional`
    (`Person.person_intentional_iff`). -/
theorem not_entails_substantive_person :
    ¬ (∀ I : SubstantivePersonhood, SubstantiveDatum I → SubstantiveDegree I) := by
  intro h
  let I : SubstantivePersonhood := {
    Subject := Unit
    Act := fun _ _ => True
    Mind := fun _ => True
    Ratio := fun _ => True
    Auto := fun _ => True
    Degree := fun _ => False
  }
  have hd : SubstantiveDatum I := ⟨(), True, trivial⟩
  have hn : ¬ SubstantiveDegree I := fun ⟨_, hd'⟩ => hd'
  exact hn (h I hd)

-- ===========================================================================
-- Part B: Hostile Abstraction of Agency and Direct Models
-- ===========================================================================

section HostileAbstraction

variable {S : Type}
variable (A : S → Prop → Prop)

/-- Follows from datum: some subject exists. -/
theorem subject_exists_of_act (hAct : ∃ s : S, ∃ p : Prop, A s p) : ∃ _s : S, True := by
  rcases hAct with ⟨s, _, _⟩
  exact ⟨s, trivial⟩

/-- Follows from datum: an act presently occurs. -/
theorem act_exists_of_act (hAct : ∃ s : S, ∃ p : Prop, A s p) : ∃ s : S, ∃ p : Prop, A s p :=
  hAct

end HostileAbstraction

/-- Open ontology for analyzing the constitutive dependence of acts on subjects and persons. -/
structure ActOntology where
  Entity : Type
  Act : Entity → Prop → Prop
  Subject : Entity → Prop
  Person : Entity → Prop

/- Hostile Countermodel 1: An act without a subject (Lichtenberg's objection).
   Shows that without a constitutive rule, an act can occur in the void without an actualizing subject. -/
namespace CountermodelActWithoutSubject
def Entity : Type := Unit
def Act : Entity → Prop → Prop := fun _ _ => True
def Subject : Entity → Prop := fun _ => False
def Person : Entity → Prop := fun _ => False

theorem act_occurs : ∃ s : Entity, ∃ p : Prop, Act s p := ⟨(), True, trivial⟩
theorem no_subject : ¬ ∃ s : Entity, Subject s := fun ⟨_, hs⟩ => hs
theorem no_person : ¬ ∃ s : Entity, Person s := fun ⟨_, hp⟩ => hp

/-- Hostile separation: an act occurs without any subject. -/
theorem act_without_subject :
    (∃ s : Entity, ∃ p : Prop, Act s p) ∧ ¬ (∃ s : Entity, Subject s) :=
  ⟨act_occurs, no_subject⟩

/-- Constitutive rule: an act cannot exist without a subject that performs/actualizes it. -/
def ConstitutiveAct (I : ActOntology) : Prop :=
  ∀ s : I.Entity, ∀ p : Prop, I.Act s p → I.Subject s

/-- Under the constitutive rule, an act strictly entails a subject. -/
theorem subject_of_constitutive_act (I : ActOntology) (hConst : ConstitutiveAct I)
    (hAct : ∃ s : I.Entity, ∃ p : Prop, I.Act s p) : ∃ s : I.Entity, I.Subject s := by
  obtain ⟨s, p, ha⟩ := hAct
  exact ⟨s, hConst s p ha⟩

/-- The countermodel is impossible solely because of the constitutive definition of Act:
    applying the constitutive rule to CountermodelActWithoutSubject yields an explicit contradiction. -/
theorem countermodel_violates_constitutive_act :
    ¬ ConstitutiveAct {
      Entity := Entity,
      Act := Act,
      Subject := Subject,
      Person := Person
    } := by
  intro hConst
  have hSubj : Subject () := hConst () True trivial
  exact no_subject ⟨(), hSubj⟩

end CountermodelActWithoutSubject

/- Hostile Countermodel 1b: A weak act / performed event without intentional meaning.
   Shows that a performed event (utterance, keystroke, physical emission, mechanical act)
   does not logically entail an intentional meaning-act (`Act s p := Means s p`).
   Separates weak act `act` from strong act `Act` in pure logic without axioms (`{}`). -/
namespace CountermodelWeakActWithoutMeaning

def Entity : Type := Unit
def act : Entity → Prop → Prop := fun _ _ => True
def Means : Entity → Prop → Prop := fun _ _ => False
def Act (s : Entity) (p : Prop) : Prop := Means s p

theorem weak_act_occurs : ∃ s : Entity, ∃ p : Prop, act s p := ⟨(), True, trivial⟩
theorem no_strong_act : ¬ ∃ s : Entity, ∃ p : Prop, Act s p := fun ⟨_, _, hm⟩ => hm

/-- Hostile separation: a performed event occurs without any intentional meaning. -/
theorem weak_act_without_meaning :
    (∃ s : Entity, ∃ p : Prop, act s p) ∧ ¬ (∃ s : Entity, ∃ p : Prop, Act s p) :=
  ⟨weak_act_occurs, no_strong_act⟩

/-- Separation theorem: the occurrence of a performed event does not entail an intentional act.
    Footprint `{}`: pure logic over the relational signatures. -/
theorem not_entails_strong_act :
    ¬ (∀ (I_act : Entity → Prop → Prop) (I_Means : Entity → Prop → Prop),
        (∃ s p, I_act s p) → (∃ s p, I_Means s p)) := by
  intro h
  exact no_strong_act (h act Means weak_act_occurs)

end CountermodelWeakActWithoutMeaning

/- Hostile Countermodel 2: A subject of an act that is NOT a person.
   Shows that if Person is an uninterpreted substantive predicate, Subject does
   not logically entail Person. (Personhood frontier, 2026-09-18: NOT a
   countermodel to the Logos nominal identity `Person ↔ Intentional`
   (`Person.person_intentional_iff`) — a Logos-model with `Subject := True`
   and the Logos definition `Person s := ∃ p, Means s p` would make a person.
   This model only refutes the SUBSTANTIVE reading.) -/
namespace CountermodelSubjectWithoutPerson
def Entity : Type := Unit
def Act : Entity → Prop → Prop := fun _ _ => True
def Subject : Entity → Prop := fun _ => True
def Person : Entity → Prop := fun _ => False

/-- The constitutive Act→Subject rule is satisfied. -/
theorem constitutive_act_holds :
    ∀ (s : Entity) (p : Prop), Act s p → Subject s := fun _ _ _ => trivial

theorem act_occurs : ∃ s : Entity, ∃ p : Prop, Act s p := ⟨(), True, trivial⟩
theorem subject_exists : ∃ s : Entity, Subject s := ⟨(), trivial⟩
theorem no_person : ¬ ∃ s : Entity, Person s := fun ⟨_, hp⟩ => hp

/-- Hostile separation: a subject of an act exists, but is NOT a person. -/
theorem subject_without_person :
    (∃ s : Entity, Subject s) ∧ ¬ (∃ s : Entity, Person s) :=
  ⟨subject_exists, no_person⟩

/-- Full separation: act occurs and subject exists, but no person exists. -/
theorem act_and_subject_without_person :
    (∃ s : Entity, ∃ p : Prop, Act s p) ∧ (∃ s : Entity, Subject s) ∧ ¬ (∃ s : Entity, Person s) :=
  ⟨act_occurs, subject_exists, no_person⟩

end CountermodelSubjectWithoutPerson

namespace CountermodelNoPerson
def S : Type := Unit
def A : S → Prop → Prop := fun _ _ => True
def Person : S → Prop := fun _ => False

theorem act_occurs : ∃ s : S, ∃ p : Prop, A s p := ⟨(), True, trivial⟩
theorem no_person : ¬ ∃ s : S, Person s := fun ⟨_, hp⟩ => hp
theorem act_does_not_imply_person :
    (∃ s : S, ∃ p : Prop, A s p) ∧ ¬ (∃ s : S, Person s) :=
  ⟨act_occurs, no_person⟩
end CountermodelNoPerson

/- Hostile Countermodel 3 (freedom/choice fix, 2026-09-18): mere occurrence
   does not entail genuine choice. `A` is uninterpreted and set to `True`
   (a determined meaning-act occurs), while `Chooses` is set to `False` — no
   subject ever co-means an incompatible alternative. `FreeWill` is defined
   from `Chooses`, so it too is empty *consistently* with the Logos
   definition. This is the honest replacement for the old `Act ↛ FreeWill`
   model: it attacks genuine choice, not a free-floating predicate. -/
namespace CountermodelNoFreeWill
def S : Type := Unit
def A : S → Prop → Prop := fun _ _ => True
def Chooses : S → Prop → Prop → Prop := fun _ _ _ => False
def FreeWill : S → Prop := fun s => ∃ p q : Prop, Chooses s p q

theorem act_occurs : ∃ s : S, ∃ p : Prop, A s p := ⟨(), True, trivial⟩
theorem no_choice : ¬ ∃ s : S, ∃ p q : Prop, Chooses s p q := fun ⟨_, _, _, hc⟩ => hc
theorem no_free_will : ¬ ∃ s : S, FreeWill s := fun ⟨s, hfw⟩ => no_choice ⟨s, hfw⟩
theorem act_does_not_imply_choice :
    (∃ s : S, ∃ p : Prop, A s p) ∧ ¬ (∃ s : S, ∃ p q : Prop, Chooses s p q) :=
  ⟨act_occurs, no_choice⟩
theorem act_does_not_imply_freewill :
    (∃ s : S, ∃ p : Prop, A s p) ∧ ¬ (∃ s : S, FreeWill s) :=
  ⟨act_occurs, no_free_will⟩
end CountermodelNoFreeWill

namespace UnitPluralityCountermodel
def S : Type := Unit
def A : S → Prop → Prop := fun _ _ => True
def Person : S → Prop := fun _ => True

theorem act_occurs : ∃ s : S, ∃ p : Prop, A s p := ⟨(), True, trivial⟩
theorem person_exists : ∃ s : S, Person s := ⟨(), trivial⟩
theorem no_plurality : ¬ ∃ s t : S, s ≠ t := by
  intro ⟨s, t, hne⟩
  cases s; cases t
  exact hne rfl

theorem agency_does_not_imply_plurality :
    (∃ s : S, ∃ p : Prop, A s p) ∧ (∃ s : S, Person s) ∧ (¬ ∃ s t : S, s ≠ t) :=
  ⟨act_occurs, person_exists, no_plurality⟩
end UnitPluralityCountermodel

namespace PropositionalPersonhood
namespace CountermodelContentWithoutPerson
def S : Type := Prop
def Means : S → Prop → Prop := fun s p => s = p
def Person : S → Prop := fun _ => False

theorem content_exists : ∃ _p : Prop, True := ⟨True, trivial⟩
theorem every_content_meant (p : Prop) : ∃ s : S, Means s p := ⟨p, rfl⟩
theorem no_person : ¬ ∃ s : S, Person s := fun ⟨_, hp⟩ => hp

theorem content_does_not_imply_personhood :
    (∃ _p : Prop, True) ∧ (∀ p : Prop, ∃ s : S, Means s p) ∧ ¬ (∃ s : S, Person s) :=
  ⟨content_exists, every_content_meant, no_person⟩
end CountermodelContentWithoutPerson

def TripartiteVerdict : String :=
  "CONTENT EXISTS\n" ++
  "MEANING MAY REQUIRE A SUBJECT\n" ++
  "PERSONHOOD DOES NOT FOLLOW WITHOUT AN ADDITIONAL PRINCIPLE"

end PropositionalPersonhood

-- ===========================================================================
-- Part C: Semantic Attack on C18 (Worldwise Truthmaking ≠ Uniform Ground)
-- ===========================================================================

namespace CountermodelWorldwiseTruthmaking

abbrev World : Type := Bool
abbrev Entity : Type := Bool

def ExistsAt (w : World) (e : Entity) : Prop := e = w
def Ground (_e : Entity) (_φ : Unit) : Prop := True

theorem worldwise_truthmaking : ∀ w : World, ∃ e : Entity, ExistsAt w e ∧ Ground e () := by
  intro w
  exact ⟨w, rfl, trivial⟩

theorem no_uniform_ground : ¬ ∃ e : Entity, ∀ w : World, ExistsAt w e ∧ Ground e () := by
  intro ⟨e, he⟩
  have h1 : e = true := (he true).1
  have h2 : e = false := (he false).1
  have h_contra : true = false := h1.symm.trans h2
  nomatch h_contra

/-- Worldwise truthmaking does not entail uniform necessary ground. -/
theorem worldwise_not_entails_uniform_ground :
    (∀ w : World, ∃ e : Entity, ExistsAt w e ∧ Ground e ()) ∧
    ¬ (∃ e : Entity, ∀ w : World, ExistsAt w e ∧ Ground e ()) :=
  ⟨worldwise_truthmaking, no_uniform_ground⟩

end CountermodelWorldwiseTruthmaking

-- ===========================================================================
-- Part C2: Semantic Attack on the Necessity Lift (subject → entity, #4/C91)
-- ===========================================================================
--
-- In Logos, `Modal.subject_nec_entity_nec` holds because `ExistsAt` is one
-- shared relation and `EntityOf` is the Truthmaker embedding — the lift is
-- *definitional*. This countermodel shows the transfer is NOT a logical law:
-- with independent persistence/existence predicates, a subject can persist in
-- every world while its entity-correlate exists in none (here: only in the
-- `true` world). Necessity is not hidden in the semantics; the definitions
-- chosen are what do the work.

namespace CountermodelSubjectNecessityNotEntityNecessity

abbrev World : Type := Bool
abbrev Subject : Type := Unit
abbrev Entity : Type := Unit

/-- The entity-correlate of the subject (chosen independently of the
    existence predicates). -/
def EntityOf (_s : Subject) : Entity := ()

/-- Subject-persistence: the subject's correlate is present in every world
    (world-rigid by stipulation, mirroring the esse-est-agere reading). -/
def SubjectExistsAt (_w : World) (_s : Subject) : Prop := True

/-- Entity-existence: genuinely world-dependent — entities exist only in the
    `true` world. -/
def EntityExistsAt (w : World) (_e : Entity) : Prop := w = true

/-- A subject is necessary iff its correlate persists in every world. -/
def NecessarySubject (s : Subject) : Prop := ∀ w : World, SubjectExistsAt w s

/-- An entity is necessary iff it exists in every world. -/
def NecessaryEntity (e : Entity) : Prop := ∀ w : World, EntityExistsAt w e

/-- The unique subject is necessary: it persists at every world. -/
theorem necessary_subject_is_necessary : NecessarySubject () := by
  intro w
  trivial

/-- No entity is necessary: each entity exists only at the `true` world. -/
theorem no_necessary_entity : ¬ ∃ e : Entity, NecessaryEntity e := by
  rintro ⟨e, h⟩
  nomatch h false

/-- Hostile separation: a necessary subject exists, yet no entity is
    necessary — the lift `NecessarySubject s → NecessaryEntity (EntityOf s)`
    is not a logical law. -/
theorem subject_necessity_not_entails_entity_necessity :
    (∃ s : Subject, NecessarySubject s) ∧ ¬ (∃ e : Entity, NecessaryEntity e) :=
  ⟨⟨(), necessary_subject_is_necessary⟩, no_necessary_entity⟩

/-- Abstract-signature form: for arbitrary interpretations of the five
    notions, the transfer need not hold. -/
structure NecessityLift where
  Subject : Type
  Entity : Type
  EntityOf : Subject → Entity
  NecessarySubject : Subject → Prop
  NecessaryEntity : Entity → Prop

/-- No abstract signature forces the lift: some guarantee it and others do
    not, so it is not a theorem of the vocabulary alone. -/
theorem not_holds_of_arbitrary_signature :
    ¬ (∀ (I : NecessityLift), ∀ s : I.Subject,
         I.NecessarySubject s → I.NecessaryEntity (I.EntityOf s)) := by
  intro h
  let I : NecessityLift := {
    Subject := Subject,
    Entity := Entity,
    EntityOf := EntityOf,
    NecessarySubject := NecessarySubject,
    NecessaryEntity := NecessaryEntity
  }
  have hinst : ∀ s : I.Subject, I.NecessarySubject s → I.NecessaryEntity (I.EntityOf s) :=
    h I
  have hN : I.NecessarySubject () := necessary_subject_is_necessary
  have hn : I.NecessaryEntity (I.EntityOf ()) := hinst () hN
  exact no_necessary_entity ⟨I.EntityOf (), hn⟩

end CountermodelSubjectNecessityNotEntityNecessity

-- ===========================================================================
-- Part C2b: Person-persistence is definitional, not logical (step 6)
-- ===========================================================================
--
-- In Logos, `Person s → NecessarySubject s` (`AxPersonStability`) holds because
-- `ExistsAt` for subject-correlates is flow from agency — definitional
-- (esse est agere). This countermodel shows the implication is NOT a logical
-- law: a person can exist while no subject persists in every world. Necessity
-- is not hidden in the semantics; the definitions chosen are what do the
-- work. Concrete side: `Love.no_contingent_person` (no `Person s ∧
-- ¬ NecessarySubject s` exists).

namespace CountermodelPersonNotNecessary

abbrev Subject : Type := Unit
abbrev World : Type := Bool

/-- Simulated world-existence: the subject exists only in the `true` world. -/
def ExistsAt (w : World) (_s : Subject) : Prop := w = true

def Person (_s : Subject) : Prop := True

def NecessarySubject (s : Subject) : Prop := ∀ w : World, ExistsAt w s

theorem person_exists : ∃ s : Subject, Person s := ⟨(), trivial⟩

theorem no_necessary_subject : ¬ ∃ s : Subject, NecessarySubject s := by
  rintro ⟨s, h⟩
  nomatch h false

/-- Hostile separation: a person exists but no subject is necessary — the
    implication `Person → NecessarySubject` is not a logical law. -/
theorem person_not_entails_necessary :
    (∃ s : Subject, Person s) ∧ ¬ (∃ s : Subject, NecessarySubject s) :=
  ⟨person_exists, no_necessary_subject⟩

/-- Abstract-signature form: for arbitrary interpretations of the three
    notions, personhood does not force persistence. -/
structure NecessitySignature where
  Subject : Type
  Person : Subject → Prop
  NecessarySubject : Subject → Prop

/-- No abstract signature forces `Person → NecessarySubject`; some guarantee it
    and others do not, so it is not a theorem of the vocabulary alone (the
    step-6 verdict: in Logos it holds *by definition*, not by logic). -/
theorem not_entails_person_necessary :
    ¬ (∀ I : NecessitySignature,
        (∃ s : I.Subject, I.Person s) → ∃ s : I.Subject, I.NecessarySubject s) := by
  intro h
  let I : NecessitySignature := {
    Subject := Unit
    Person := fun _ => True
    NecessarySubject := fun _ => False
  }
  have hp : ∃ s : I.Subject, I.Person s := ⟨(), trivial⟩
  have hno : ¬ (∃ s : I.Subject, I.NecessarySubject s) := fun ⟨_, hn⟩ => hn
  exact hno (h I hp)

end CountermodelPersonNotNecessary

-- ===========================================================================
-- Part C2c: Veridical Meaning vs. the Choice Frontier (F1b / 2026-09-18)
-- ===========================================================================
--
-- `genuineChoice_exists` (Choice.F1b) demands that ONE subject co-mean two
-- incompatible contents. Nothing forces `Means` to be truth-neutral: in a
-- model where meaning is *veridical* (`Means s p → p`), co-meaning a
-- disagreement is impossible (`p ∧ q ∧ ¬(p∧q)`). The models below instantiate
-- the Logos definitions exactly (A := Means, Person := ∃p, Means s p,
-- Chooses := co-meaned incompatibility, FreeWill := ∃p q, Chooses) and show
-- the whole agency/choice/order fragment holds — act datum, plurality,
-- right-and-wrong, `judge_commits`, fallibility — while genuine choice is
-- empty. These are the honest replacements for `CountermodelNoFreeWill`
-- (which decouples `Chooses` from its Logos definition and so does not bear
-- on `genuineChoice_exists`).

namespace CountermodelVeridicalMeaning

-- Single subject, veridical meaning: `Unit` with `Means () p := p`.
namespace Single

def S : Type := Unit
def M (_s : S) (p : Prop) : Prop := p
def A (s : S) (p : Prop) : Prop := M s p
def Person (s : S) : Prop := ∃ p : Prop, M s p
def Chooses (s : S) (p q : Prop) : Prop := A s p ∧ A s q ∧ Logos.Alternatives.Incompatible p q
def FreeWill (s : S) : Prop := ∃ p q : Prop, Chooses s p q
def Asserts (s : S) (p : Prop) : Prop := A s p ∧ p
def Selects (s : S) (p q : Prop) : Prop :=
  Asserts s p ∧ Logos.Alternatives.Incompatible p q ∧ ¬ Asserts s q
def DeliberateChoice (s : S) (p q : Prop) : Prop :=
  M s p ∧ M s q ∧ Logos.Alternatives.Incompatible p q ∧ Asserts s p ∧ ¬ Asserts s q

theorem act_datum_holds : ∃ s : S, ∃ p : Prop, A s p :=
  ⟨(), True, trivial⟩

theorem field_holds : ∃ s : S, ∃ p q : Prop, A s p ∧ Logos.Alternatives.Incompatible p q := by
  exact ⟨(), True, False, trivial, fun h => h.2⟩

theorem selection_holds : ∃ s : S, ∃ p q : Prop, Selects s p q := by
  refine ⟨(), True, False, ⟨trivial, trivial⟩, fun h => h.2, ?_⟩
  rintro ⟨_, hFalse⟩
  exact hFalse

theorem no_genuine_choice : ¬ ∃ s : S, ∃ p q : Prop, Chooses s p q := by
  rintro ⟨s, p, q, hp, hq, hI⟩
  exact hI ⟨hp, hq⟩

theorem no_deliberate_choice : ¬ ∃ s : S, ∃ p q : Prop, DeliberateChoice s p q := by
  rintro ⟨s, p, q, hp, hq, hI, _, _⟩
  exact hI ⟨hp, hq⟩

theorem no_freewill : ¬ ∃ s : S, FreeWill s := by
  rintro ⟨s, p, q, hc⟩
  exact no_genuine_choice ⟨s, p, q, hc⟩

theorem no_rejected_horn : ¬ ∃ s : S, ∃ p : Prop, A s p ∧ A s (¬ p) := by
  rintro ⟨s, p, hp, hnp⟩
  exact hnp hp

/-- Hostile separation: the act occurs (the performative datum), the choice
    field obtains, yet genuine choice is impossible. -/
theorem act_does_not_imply_genuine_choice :
    (∃ s : S, ∃ p : Prop, A s p) ∧
    ¬ (∃ s : S, ∃ p q : Prop, Chooses s p q) :=
  ⟨act_datum_holds, no_genuine_choice⟩

/-- Semantic selection holds in the veridical model, yet genuine choice fails:
    selection does not entail co-meaning both incompatible horns. -/
theorem selection_does_not_imply_genuine_choice :
    (∃ s : S, ∃ p q : Prop, Selects s p q) ∧
    ¬ (∃ s : S, ∃ p q : Prop, Chooses s p q) :=
  ⟨selection_holds, no_genuine_choice⟩

/-- Semantic selection holds in the veridical model, yet deliberate choice fails:
    selection does not entail deliberative co-meaning of the rejected alternative. -/
theorem selection_does_not_imply_deliberate_choice :
    (∃ s : S, ∃ p q : Prop, Selects s p q) ∧
    ¬ (∃ s : S, ∃ p q : Prop, DeliberateChoice s p q) :=
  ⟨selection_holds, no_deliberate_choice⟩

/-- Semantic selection holds in the deterministic/veridical model, yet free will fails:
    semantic selection does not entail libertarian free will. -/
theorem selection_does_not_imply_freewill :
    (∃ s : S, ∃ p q : Prop, Selects s p q) ∧
    ¬ (∃ s : S, FreeWill s) :=
  ⟨selection_holds, no_freewill⟩

/-- Semantic selection does not entail meaning the rejected alternative (F1b boundary):
    A subject can select `p` against its negation `¬p` (via factive assertion) without
    meaning or entertaining the rejected horn `¬p` in thought. -/
theorem selects_does_not_imply_rejected_horn_meaning :
    (∃ s : S, ∃ p : Prop, Selects s p (¬p)) ∧
    ¬ (∃ s : S, ∃ p : Prop, Selects s p (¬p) ∧ M s (¬p)) := by
  constructor
  · refine ⟨(), True, ?_⟩
    have hI : Logos.Alternatives.Incompatible True (¬True) := by
      intro h; exact h.2 h.1
    refine ⟨⟨trivial, trivial⟩, hI, ?_⟩
    rintro ⟨_, hFalse⟩
    exact hFalse trivial
  · rintro ⟨_s, _p, hSel, hMn⟩
    exact hMn hSel.1.2

/-- Factive assertion does not entail meaning the rejected alternative:
    Asserting `p` guarantees semantic selection against `¬p`, but does not force
    the subject to represent `¬p` in thought. -/
theorem assertion_does_not_imply_rejected_horn_meaning :
    (∃ s : S, ∃ p : Prop, Asserts s p) ∧
    ¬ (∃ s : S, ∃ p : Prop, Asserts s p ∧ M s (¬p)) := by
  constructor
  · exact ⟨(), True, trivial, trivial⟩
  · rintro ⟨_s, _p, hAss, hMn⟩
    exact hMn hAss.2

end Single

-- Two persons, veridical meaning: `Bool` with `Means _ p := p`, mirroring
-- the agency/choice/order fragment (Person, Correct/Incorrect, Fallible).
namespace TwoPersons

def S : Type := Bool
def M (_s : S) (p : Prop) : Prop := p
def A (s : S) (p : Prop) : Prop := M s p
def Person (s : S) : Prop := ∃ p : Prop, M s p
def Chooses (s : S) (p q : Prop) : Prop := A s p ∧ A s q ∧ Logos.Alternatives.Incompatible p q
def FreeWill (s : S) : Prop := ∃ p q : Prop, Chooses s p q

/-- Order-fragment mirrors (Logos.Order). -/
def T (p : Prop) : Prop := p
def IsFalse (p : Prop) : Prop := ¬ p
def Correct (s : S) (p : Prop) : Prop := A s p ∧ T p
def Incorrect (s : S) (p : Prop) : Prop := A s p ∧ IsFalse p
def Fallible (_s : S) (p : Prop) : Prop := IsFalse p
def Asserts (s : S) (p : Prop) : Prop := A s p ∧ p
def Selects (s : S) (p q : Prop) : Prop :=
  Asserts s p ∧ Logos.Alternatives.Incompatible p q ∧ ¬ Asserts s q
def DeliberateChoice (s : S) (p q : Prop) : Prop :=
  M s p ∧ M s q ∧ Logos.Alternatives.Incompatible p q ∧ Asserts s p ∧ ¬ Asserts s q

theorem act_datum_holds : ∃ s : S, ∃ p : Prop, A s p :=
  ⟨false, True, trivial⟩

theorem assertion_holds : ∃ s : S, ∃ p : Prop, Asserts s p :=
  ⟨false, True, trivial, trivial⟩

theorem two_persons_exist : ∃ s₁ s₂ : S, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ := by
  refine ⟨true, false, ?_, ?_, ?_⟩
  · exact ⟨True, trivial⟩
  · exact ⟨True, trivial⟩
  · intro h
    cases h

theorem rightWrong_holds : (¬ (∀ p : Prop, ¬ T p)) ∧ (¬ (∀ p : Prop, T p)) := by
  constructor
  · intro h
    exact h True trivial
  · intro h
    exact h False

theorem judge_commits_holds :
    ∃ (s : S) (p q : Prop),
      A s p ∧ (Correct s p ∨ Incorrect s p) ∧ Logos.Alternatives.Incompatible p q := by
  refine ⟨false, True, False, ?_, ?_, ?_⟩
  · trivial
  · exact Or.inl ⟨trivial, trivial⟩
  · intro h
    exact h.2

theorem fallibility_holds : ∃ (s : S) (p : Prop), Fallible s p ∧ IsFalse p := by
  refine ⟨false, False, ?_, ?_⟩
  · intro h
    exact h
  · intro h
    exact h

theorem no_genuine_choice : ¬ ∃ s : S, ∃ p q : Prop, Chooses s p q := by
  rintro ⟨s, p, q, hp, hq, hI⟩
  exact hI ⟨hp, hq⟩

theorem no_rejected_horn : ¬ ∃ s : S, ∃ p : Prop, A s p ∧ A s (¬ p) := by
  rintro ⟨s, p, hp, hnp⟩
  exact hnp hp

theorem no_deliberate_choice : ¬ ∃ s : S, ∃ p q : Prop, DeliberateChoice s p q := by
  rintro ⟨s, p, q, hp, hq, hI, _, _⟩
  exact hI ⟨hp, hq⟩

theorem no_deliberate_resource : ¬ ∃ s : S, ∃ p : Prop, Asserts s p ∧ M s (¬ p) := by
  rintro ⟨s, p, hAss, hMn⟩
  exact hMn hAss.2

/-- Hostile separation: an assertion occurs under two persons, yet meaning the rejected alternative is impossible. -/
theorem assertion_does_not_imply_rejected_horn_meaning :
    (∃ s : S, ∃ p : Prop, Asserts s p) ∧
    ¬ (∃ s : S, ∃ p : Prop, Asserts s p ∧ M s (¬ p)) :=
  ⟨assertion_holds, no_deliberate_resource⟩

/-- Hostile separation, full fragment: act datum, two distinct persons,
    right-and-wrong, the judge committing a choice field, and fallibility all
    hold — yet genuine choice (and with it `FreeWill`) is empty. This is the
    "satisfies all relevant existing assumptions while falsifying
    `genuineChoice_exists`" witness of the frontier. -/
theorem full_fragment_without_genuine_choice :
    (∃ s : S, ∃ p : Prop, A s p) ∧
    (∃ s₁ s₂ : S, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂) ∧
    ((¬ (∀ p : Prop, ¬ T p)) ∧ (¬ (∀ p : Prop, T p))) ∧
    (∃ (s : S) (p q : Prop), A s p ∧ (Correct s p ∨ Incorrect s p) ∧ Logos.Alternatives.Incompatible p q) ∧
    (∃ (s : S) (p : Prop), Fallible s p ∧ IsFalse p) ∧
    ¬ (∃ s : S, ∃ p q : Prop, Chooses s p q) :=
  ⟨act_datum_holds, two_persons_exist, rightWrong_holds, judge_commits_holds,
   fallibility_holds, no_genuine_choice⟩

/-- Hostile separation, full fragment with assertion: factive assertion, two distinct persons,
    right-and-wrong, the judge committing a choice field, and fallibility all hold —
    yet the minimal deliberative resource (asserting p while meaning ¬p) is provably empty. -/
theorem full_fragment_without_deliberate_resource :
    (∃ s : S, ∃ p : Prop, Asserts s p) ∧
    (∃ s₁ s₂ : S, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂) ∧
    ((¬ (∀ p : Prop, ¬ T p)) ∧ (¬ (∀ p : Prop, T p))) ∧
    (∃ (s : S) (p q : Prop), A s p ∧ (Correct s p ∨ Incorrect s p) ∧ Logos.Alternatives.Incompatible p q) ∧
    (∃ (s : S) (p : Prop), Fallible s p ∧ IsFalse p) ∧
    ¬ (∃ s : S, ∃ p : Prop, Asserts s p ∧ M s (¬ p)) :=
  ⟨assertion_holds, two_persons_exist, rightWrong_holds, judge_commits_holds,
   fallibility_holds, no_deliberate_resource⟩

end TwoPersons

-- ===========================================================================
-- Abstract-signature forms: non-entailment over the choice vocabulary
-- ===========================================================================

structure GenuineChoiceSignature where
  Subject : Type
  Means : Subject → Prop → Prop

def GCdatum (I : GenuineChoiceSignature) : Prop :=
  ∃ s : I.Subject, ∃ p : Prop, I.Means s p

/-- Genuine choice over the signature, exactly as Logos defines it
    (`Chooses s p q := A s p ∧ A s q ∧ Incompatible p q` with `A ∘ Means`). -/
def GenuineChoice (I : GenuineChoiceSignature) : Prop :=
  ∃ s : I.Subject, ∃ p q : Prop, I.Means s p ∧ I.Means s q ∧ Logos.Alternatives.Incompatible p q

/-- Two distinct persons over the signature (`Person s := ∃ p, Means s p`). -/
def Γ_twoGCSubjects (I : GenuineChoiceSignature) : Prop :=
  ∃ s₁ s₂ : I.Subject, (∃ p : Prop, I.Means s₁ p) ∧ (∃ p : Prop, I.Means s₂ p) ∧ s₁ ≠ s₂

/-- Separation: the act-datum does not force genuine choice under the Logos
    definition — the veridical model witnesses the failure. -/
theorem not_entails_genuine_choice :
    ¬ (∀ I : GenuineChoiceSignature, GCdatum I → GenuineChoice I) := by
  intro h
  let I : GenuineChoiceSignature := { Subject := Unit, Means := fun _ p => p }
  have hd : GCdatum I := ⟨(), True, trivial⟩
  have hn : ¬ GenuineChoice I := by
    rintro ⟨s, p, q, hp, hq, hI⟩
    exact hI ⟨hp, hq⟩
  exact hn (h I hd)

/-- Separation, strengthened: act-datum plus two distinct persons still does
    not force genuine choice — plurality is not the missing resource either. -/
theorem not_entails_genuine_choice_with_plurality :
    ¬ (∀ I : GenuineChoiceSignature, GCdatum I ∧ Γ_twoGCSubjects I → GenuineChoice I) := by
  intro h
  let I : GenuineChoiceSignature := { Subject := Bool, Means := fun _ p => p }
  have hd : GCdatum I ∧ Γ_twoGCSubjects I := by
    constructor
    · exact ⟨false, True, trivial⟩
    · refine ⟨true, false, ⟨True, trivial⟩, ⟨True, trivial⟩, ?_⟩
      intro h
      cases h
  have hn : ¬ GenuineChoice I := by
    rintro ⟨s, p, q, hp, hq, hI⟩
    exact hI ⟨hp, hq⟩
  exact hn (h I hd)

-- ===========================================================================
-- Boundary signature: the negative boundary generalized to the modal layer.
-- `Value` stands in for `Satisfies w τ` of a witness content; `ModalOpen`
-- mirrors the two inhabited satisfaction-horns that C95/C96 establish for
-- atoms. Even with a modal-open channel as an extra datum, the choice
-- relation cannot be forced (the completed negative boundary of F1b).
-- ===========================================================================

structure BoundarySignature where
  Subject : Type
  World : Type
  Value : World → Prop
  Means : Subject → Prop → Prop

/-- Modal openness of a content over the signature: the two satisfaction-horns
    `(∃ w, Satisfies w τ) ∧ (∃ w, ¬ Satisfies w τ)` that C95/C96 prove at the
    content level, abstracted over `Value`. -/
def ModalOpen (I : BoundarySignature) : Prop :=
  (∃ w : I.World, I.Value w) ∧ (∃ w : I.World, ¬ I.Value w)

/-- The boundary datum: someone means something, and the modal channel is open. -/
def BoundaryDatum (I : BoundarySignature) : Prop :=
  (∃ s : I.Subject, ∃ p : Prop, I.Means s p) ∧ ModalOpen I

/-- Genuine choice over the boundary signature, exactly as over
    `GenuineChoiceSignature` (`Chooses s p q := A s p ∧ A s q ∧ Incompatible p q`). -/
def BoundaryGenuineChoice (I : BoundarySignature) : Prop :=
  ∃ s : I.Subject, ∃ p q : Prop,
    I.Means s p ∧ I.Means s q ∧ Logos.Alternatives.Incompatible p q

/-- Two distinct subjects with content over the boundary signature. -/
def BoundaryTwoSubjects (I : BoundarySignature) : Prop :=
  ∃ s₁ s₂ : I.Subject,
    (∃ p : Prop, I.Means s₁ p) ∧ (∃ p : Prop, I.Means s₂ p) ∧ s₁ ≠ s₂

/-- Separation over the modal boundary: even feeding the modal-openness datum
    (the C95/C96 outcome at the content level) as an extra premise, the choice
    relation cannot be forced — the veridical model witnesses the failure. -/
theorem modal_openness_does_not_entail_genuine_choice :
    ¬ (∀ I : BoundarySignature, BoundaryDatum I → BoundaryGenuineChoice I) := by
  intro h
  let I : BoundarySignature :=
    { Subject := Unit, World := Bool, Value := fun b => b = true, Means := fun _ p => p }
  have hd : BoundaryDatum I := by
    constructor
    · exact ⟨(), True, trivial⟩
    · constructor
      · exact ⟨true, rfl⟩
      · exact ⟨false, by decide⟩
  have hn : ¬ BoundaryGenuineChoice I := by
    rintro ⟨s, p, q, hp, hq, hI⟩
    exact hI ⟨hp, hq⟩
  exact hn (h I hd)

/-- Separation, strengthened: modal openness plus two distinct subjects still
    does not force genuine choice — plurality is not the missing resource
    either, even with the modal channel open. -/
theorem modal_openness_and_plurality_do_not_entail_genuine_choice :
    ¬ (∀ I : BoundarySignature, BoundaryDatum I ∧ BoundaryTwoSubjects I →
         BoundaryGenuineChoice I) := by
  intro h
  let I : BoundarySignature :=
    { Subject := Bool, World := Bool, Value := fun b => b = true, Means := fun _ p => p }
  have hd : BoundaryDatum I ∧ BoundaryTwoSubjects I := by
    constructor
    · constructor
      · exact ⟨false, True, trivial⟩
      · constructor
        · exact ⟨true, rfl⟩
        · exact ⟨false, by decide⟩
    · refine ⟨true, false, ⟨True, trivial⟩, ⟨True, trivial⟩, ?_⟩
      intro h
      cases h
  have hn : ¬ BoundaryGenuineChoice I := by
    rintro ⟨s, p, q, hp, hq, hI⟩
    exact hI ⟨hp, hq⟩
  exact hn (h I hd)

end CountermodelVeridicalMeaning

-- ===========================================================================
-- Part C2: Semantic Selection and Non-Entailment Boundary
-- ===========================================================================

namespace CountermodelOmniMeaning

def S : Type := Unit
def Means (_s : S) (_p : Prop) : Prop := True
def Act (s : S) (p : Prop) : Prop := Means s p
def MeansSelects (s : S) (p q : Prop) : Prop :=
  Means s p ∧ Logos.Alternatives.Incompatible p q ∧ ¬ Means s q

theorem act_datum_holds : ∃ s : S, ∃ p : Prop, Act s p :=
  ⟨(), True, trivial⟩

theorem no_means_selection : ¬ ∃ s : S, ∃ p q : Prop, MeansSelects s p q := by
  rintro ⟨s, p, q, _, _, hnq⟩
  exact hnq trivial

/-- Bare meaning does not entail semantic selection at the level of Means:
    an omni-entertaining subject represents every content without rejecting any. -/
theorem means_does_not_entail_means_selection :
    (∃ s : S, ∃ p : Prop, Act s p) ∧
    ¬ (∃ s : S, ∃ p q : Prop, MeansSelects s p q) :=
  ⟨act_datum_holds, no_means_selection⟩

end CountermodelOmniMeaning

namespace CountermodelActWithoutAssertion

def S : Type := Unit
def Means (_s : S) (p : Prop) : Prop := (p = False)
def Act (s : S) (p : Prop) : Prop := Means s p
def Asserts (s : S) (p : Prop) : Prop := Act s p ∧ p

theorem act_datum_holds : ∃ s : S, ∃ p : Prop, Act s p :=
  ⟨(), False, rfl⟩

theorem no_assertion : ¬ ∃ s : S, ∃ p : Prop, Asserts s p := by
  rintro ⟨s, p, hp1, hp2⟩
  subst hp1
  exact hp2

/-- An intentional act does not entail assertion: an agent can mean falsehood,
    in which case an act occurs, but no veridical assertion obtains. -/
theorem act_does_not_imply_assertion :
    (∃ s : S, ∃ p : Prop, Act s p) ∧
    ¬ (∃ s : S, ∃ p : Prop, Asserts s p) :=
  ⟨act_datum_holds, no_assertion⟩

end CountermodelActWithoutAssertion

-- ===========================================================================
-- Abstract-signature forms: non-entailment over the selection vocabulary
-- Note on Asserts ↛ Selection: no countermodel can exist in Γ because
-- `Choice.asserts_selects` is a verified theorem in the kernel. The definition
-- `Asserts s p := Act s p ∧ p` requires p to be true, which constitutively
-- excludes asserting any incompatible q (via `assertion_consistency`).
-- Hence `Asserts ↛ Selection` is mathematically impossible under Γ's logic.
-- ===========================================================================

structure SelectionSignature where
  Subject : Type
  Means : Subject → Prop → Prop
  Asserts : Subject → Prop → Prop
  Selects : Subject → Prop → Prop → Prop
  DeliberateChoice : Subject → Prop → Prop → Prop
  Chooses : Subject → Prop → Prop → Prop
  FreeWill : Subject → Prop

def ActDatum (I : SelectionSignature) : Prop :=
  ∃ s : I.Subject, ∃ p : Prop, I.Means s p

def AssertsDatum (I : SelectionSignature) : Prop :=
  ∃ s : I.Subject, ∃ p : Prop, I.Asserts s p

def SelectionDatum (I : SelectionSignature) : Prop :=
  ∃ s : I.Subject, ∃ p q : Prop, I.Selects s p q

def DeliberateChoiceDatum (I : SelectionSignature) : Prop :=
  ∃ s : I.Subject, ∃ p q : Prop, I.DeliberateChoice s p q

def GenuineChoiceDatum (I : SelectionSignature) : Prop :=
  ∃ s : I.Subject, ∃ p q : Prop, I.Chooses s p q

def FreeWillDatum (I : SelectionSignature) : Prop :=
  ∃ s : I.Subject, I.FreeWill s

/-- Separation: the occurrence of an intentional act does not logically entail an assertion.
    An agent may mean false content; because assertion contains the truth condition `p`,
    an act without true content constitutes no assertion. -/
theorem act_not_entails_asserts :
    ¬ (∀ I : SelectionSignature, ActDatum I → AssertsDatum I) := by
  intro h
  let I : SelectionSignature := {
    Subject := Unit
    Means := fun _ p => p = False
    Asserts := fun _ p => (p = False) ∧ p
    Selects := fun _ p q => (p = False) ∧ p ∧ Logos.Alternatives.Incompatible p q ∧ ¬ ((q = False) ∧ q)
    DeliberateChoice := fun _ p q => False
    Chooses := fun _ p q => False
    FreeWill := fun _ => False
  }
  have ha : ActDatum I := ⟨(), False, rfl⟩
  have hna : ¬ AssertsDatum I := by
    rintro ⟨s, p, hp1, hp2⟩
    subst hp1
    exact hp2
  exact hna (h I ha)

/-- Separation: the occurrence of an intentional act does not logically entail semantic selection.
    An agent meaning only falsehood performs an act but cannot make a factive assertion or selection. -/
theorem act_not_entails_selects :
    ¬ (∀ I : SelectionSignature, ActDatum I → SelectionDatum I) := by
  intro h
  let I : SelectionSignature := {
    Subject := Unit
    Means := fun _ p => p = False
    Asserts := fun _ p => (p = False) ∧ p
    Selects := fun _ p q => (p = False) ∧ p ∧ Logos.Alternatives.Incompatible p q ∧ ¬ ((q = False) ∧ q)
    DeliberateChoice := fun _ p q => False
    Chooses := fun _ p q => False
    FreeWill := fun _ => False
  }
  have ha : ActDatum I := ⟨(), False, rfl⟩
  have hns : ¬ SelectionDatum I := by
    rintro ⟨s, p, q, hp1, hp2, _, _⟩
    subst hp1
    exact hp2
  exact hns (h I ha)

/-- Separation: genuine choice (co-meaning incompatible contents) does not logically entail
    deliberate choice (which requires asserting one horn).
    An agent may entertain two incompatible hypotheses in contemplation without committing to either. -/
theorem chooses_not_entails_deliberateChoice :
    ¬ (∀ I : SelectionSignature, GenuineChoiceDatum I → DeliberateChoiceDatum I) := by
  intro h
  let I : SelectionSignature := {
    Subject := Unit
    Means := fun _ _ => True
    Asserts := fun _ _ => False
    Selects := fun _ _ _ => False
    DeliberateChoice := fun _ p q => True ∧ True ∧ Logos.Alternatives.Incompatible p q ∧ False ∧ ¬ False
    Chooses := fun _ p q => True ∧ True ∧ Logos.Alternatives.Incompatible p q
    FreeWill := fun _ => False
  }
  have hc : GenuineChoiceDatum I := ⟨(), True, False, trivial, trivial, fun h => h.2⟩
  have hnd : ¬ DeliberateChoiceDatum I := by
    rintro ⟨s, p, q, _, _, _, hAss, _⟩
    exact hAss
  exact hnd (h I hc)

/-- Separation: semantic selection does not logically entail deliberate choice
    (entertaining both horns in thought while asserting one). -/
theorem selection_not_entails_deliberate_choice :
    ¬ (∀ I : SelectionSignature, SelectionDatum I → DeliberateChoiceDatum I) := by
  intro h
  let I : SelectionSignature := {
    Subject := Unit
    Means := fun _ p => p
    Asserts := fun _ p => p
    Selects := fun _ p q => p ∧ Logos.Alternatives.Incompatible p q ∧ ¬ q
    DeliberateChoice := fun _ p q => p ∧ q ∧ Logos.Alternatives.Incompatible p q ∧ p ∧ ¬ q
    Chooses := fun _ p q => p ∧ q ∧ Logos.Alternatives.Incompatible p q
    FreeWill := fun _ => False
  }
  have hd : SelectionDatum I := ⟨(), True, False, trivial, fun h => h.2, id⟩
  have hn : ¬ DeliberateChoiceDatum I := by
    rintro ⟨s, p, q, hp, hq, hI, _, _⟩
    exact hI ⟨hp, hq⟩
  exact hn (h I hd)

/-- Separation: semantic selection does not logically entail genuine choice
    (co-meaning both incompatible horns). -/
theorem selection_not_entails_genuine_choice :
    ¬ (∀ I : SelectionSignature, SelectionDatum I → GenuineChoiceDatum I) := by
  intro h
  let I : SelectionSignature := {
    Subject := Unit
    Means := fun _ p => p
    Asserts := fun _ p => p
    Selects := fun _ p q => p ∧ Logos.Alternatives.Incompatible p q ∧ ¬ q
    DeliberateChoice := fun _ p q => p ∧ q ∧ Logos.Alternatives.Incompatible p q ∧ p ∧ ¬ q
    Chooses := fun _ p q => p ∧ q ∧ Logos.Alternatives.Incompatible p q
    FreeWill := fun _ => False
  }
  have hd : SelectionDatum I := ⟨(), True, False, trivial, fun h => h.2, id⟩
  have hn : ¬ GenuineChoiceDatum I := by
    rintro ⟨s, p, q, hp, hq, hI⟩
    exact hI ⟨hp, hq⟩
  exact hn (h I hd)

/-- Separation: semantic selection does not logically entail libertarian free will. -/
theorem selection_not_entails_freewill :
    ¬ (∀ I : SelectionSignature, SelectionDatum I → FreeWillDatum I) := by
  intro h
  let I : SelectionSignature := {
    Subject := Unit
    Means := fun _ p => p
    Asserts := fun _ p => p
    Selects := fun _ p q => p ∧ Logos.Alternatives.Incompatible p q ∧ ¬ q
    DeliberateChoice := fun _ p q => p ∧ q ∧ Logos.Alternatives.Incompatible p q ∧ p ∧ ¬ q
    Chooses := fun _ p q => p ∧ q ∧ Logos.Alternatives.Incompatible p q
    FreeWill := fun _ => False
  }
  have hd : SelectionDatum I := ⟨(), True, False, trivial, fun h => h.2, id⟩
  have hn : ¬ FreeWillDatum I := by
    rintro ⟨s, hf⟩
    exact hf
  exact hn (h I hd)

structure MeansSelectionSignature where
  Subject : Type
  Means : Subject → Prop → Prop
  Selects : Subject → Prop → Prop → Prop

def BareMeansDatum (I : MeansSelectionSignature) : Prop :=
  ∃ s : I.Subject, ∃ p : Prop, I.Means s p

def MeansSelectionDatum (I : MeansSelectionSignature) : Prop :=
  ∃ s : I.Subject, ∃ p q : Prop, I.Selects s p q

/-- Separation: bare meaning does not logically entail selection. -/
theorem not_entails_selection_of_bare_means :
    ¬ (∀ I : MeansSelectionSignature, BareMeansDatum I → MeansSelectionDatum I) := by
  intro h
  let I : MeansSelectionSignature := {
    Subject := Unit
    Means := fun _ _ => True
    Selects := fun _ _ _ => False
  }
  have hd : BareMeansDatum I := ⟨(), True, trivial⟩
  have hn : ¬ MeansSelectionDatum I := by
    rintro ⟨s, p, q, hs⟩
    exact hs
  exact hn (h I hd)

-- ===========================================================================
-- Part D: Semantic Attack on Ultimate Ground (Infinite Descending Chain)
-- ===========================================================================

namespace CountermodelInfiniteGroundChain

abbrev Entity : Type := Int

-- x grounds y iff x > y (x is strictly prior in the explanatory order)
def GroundEntity (x y : Entity) : Prop := x > y

def UltimateGround (u : Entity) : Prop := ¬ ∃ x : Entity, GroundEntity x u

theorem irreflexive (x : Entity) : ¬ GroundEntity x x :=
  Int.lt_irrefl x

theorem asymmetric (x y : Entity) : GroundEntity x y → ¬ GroundEntity y x :=
  fun hxy hyx => Int.lt_irrefl x (Int.lt_trans hyx hxy)

theorem transitive (x y z : Entity) : GroundEntity x y → GroundEntity y z → GroundEntity x z :=
  fun hxy hyz => Int.lt_trans hyz hxy

theorem no_ultimate : ¬ ∃ u : Entity, UltimateGround u :=
  fun ⟨u, hu⟩ => hu ⟨u + 1, Int.le_refl (u + 1)⟩

/-- Strict partial order does not entail the existence of an ultimate element. -/
theorem infinite_chain_has_no_ultimate :
    (∀ x, ¬ GroundEntity x x) ∧
    (∀ x y, GroundEntity x y → ¬ GroundEntity y x) ∧
    (∀ x y z, GroundEntity x y → GroundEntity y z → GroundEntity x z) ∧
    (¬ ∃ u, UltimateGround u) :=
  ⟨irreflexive, asymmetric, transitive, no_ultimate⟩

end CountermodelInfiniteGroundChain

-- ===========================================================================
-- Part E: Semantic Attack on Personal Ultimate Ground
-- ===========================================================================

namespace CountermodelImpersonalUltimateGround

abbrev Entity : Type := Unit

def GroundEntity (_x _y : Entity) : Prop := False
def UltimateGround (u : Entity) : Prop := ¬ ∃ x : Entity, GroundEntity x u
def Personal (_e : Entity) : Prop := False

theorem ultimate_exists : ∃ u : Entity, UltimateGround u := by
  refine ⟨(), ?_⟩
  intro ⟨_, hx⟩
  exact hx

theorem no_personal_ultimate : ¬ ∃ u : Entity, UltimateGround u ∧ Personal u := by
  intro ⟨_, _, hp⟩
  exact hp

/-- Existence of an ultimate ground does not entail that it is personal. -/
theorem ultimate_not_entails_personal :
    (∃ u : Entity, UltimateGround u) ∧
    ¬ (∃ u : Entity, UltimateGround u ∧ Personal u) :=
  ⟨ultimate_exists, no_personal_ultimate⟩

end CountermodelImpersonalUltimateGround

-- ===========================================================================
-- Part F: Semantic Attack on Love (Plurality Does Not Imply Love)
-- ===========================================================================

namespace CountermodelPluralityWithoutLove

abbrev Subject : Type := Bool
def Person (_s : Subject) : Prop := True
def Loves (_s _t : Subject) : Prop := False

theorem two_persons_exist : ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ := by
  refine ⟨true, false, trivial, trivial, ?_⟩
  decide

theorem no_love : ¬ ∃ s₁ s₂ : Subject, Loves s₁ s₂ := by
  intro ⟨_, _, hl⟩
  exact hl

/-- Plurality of distinct persons does not entail love without substantive relational bridges. -/
theorem plurality_not_entails_love :
    (∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂) ∧
    ¬ (∃ s₁ s₂ : Subject, Loves s₁ s₂) :=
  ⟨two_persons_exist, no_love⟩

end CountermodelPluralityWithoutLove

end Logos.HostileSemantics
