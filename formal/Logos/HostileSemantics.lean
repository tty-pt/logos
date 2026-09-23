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
import Logos.Initiation
import Logos.Entity
import Logos.Modal

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
-- Person s := Agent s ∧ Rational s ∧ Intentional s with `Agent` analytic
-- `True` and `Rational` the derived floor `∃ p, Means s p` (PERSON.md,
-- 2026-09-23)). Hence `Person ↔ Intentional`
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
    `Rational` (derived floor `∃ p, Means s p`, `{Means, Subject}`; still NOT
    substantive `Ratio` / deliberative rationality). -/
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

/- Hostile Countermodel 1b: A weak act / performed event without intentional meaning.
   Shows that a performed event (utterance, keystroke, physical emission, mechanical act)
   does not logically entail an intentional meaning-act (`Act s p := Means s p`).
   Separates weak act `act` from strong act `Act` in pure logic without axioms (`{}`). -/

/- Hostile Countermodel 1c: Intentional meaning without initiation.
   Shows that pure semantic meaning does not logically entail initiation of movement,
   nor strong Act (Means ↛ Initiates and Means alone ↛ Act). -/
namespace CountermodelMeaningWithoutInitiation

def Entity : Type := Unit
def State : Type := Unit
def Means : Entity → Prop → Prop := fun _ _ => True
def Initiates : Entity → State → State → Prop → Prop := fun _ _ _ _ => False
def Act (s : Entity) (p : Prop) : Prop :=
  Means s p ∧ ∃ w w' : State, Initiates s w w' p

theorem meaning_occurs : ∃ s : Entity, ∃ p : Prop, Means s p := ⟨(), True, trivial⟩
theorem no_initiation : ¬ ∃ s : Entity, ∃ p : Prop, ∃ w w' : State, Initiates s w w' p :=
  fun ⟨_, _, _, _, hi⟩ => hi
theorem no_act : ¬ ∃ s : Entity, ∃ p : Prop, Act s p :=
  fun ⟨_, _, _, _, _, hi⟩ => hi

/-- Separation: meaning occurs without initiation (Means ↛ Initiates). -/
theorem means_does_not_imply_initiates :
    (∃ s : Entity, ∃ p : Prop, Means s p) ∧
    ¬ (∃ s : Entity, ∃ p : Prop, ∃ w w' : State, Initiates s w w' p) :=
  ⟨meaning_occurs, no_initiation⟩

/-- Separation: meaning occurs without strong Act (Means alone ↛ Act). -/
theorem means_does_not_imply_act :
    (∃ s : Entity, ∃ p : Prop, Means s p) ∧
    ¬ (∃ s : Entity, ∃ p : Prop, Act s p) :=
  ⟨meaning_occurs, no_act⟩

end CountermodelMeaningWithoutInitiation

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
-- Part C2: Semantic Attack on the Necessity Lift (subject → entity, #4/C91)
-- ===========================================================================
--
-- In Logos, `Modal.subject_nec_entity_nec` holds because `ExistsAt` is one
-- shared relation and `EntityOf` is the entity embedding — the lift is
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

/-
### Core Conceptual Distinctions (Preserved Invariants):
1. Weak act vs. Strong Act:
   - `act(s,p)`   : weak act = performed event (pure sort / uninterpreted relation).
   - `Act(s,p)`   : strong Act = meaningful initiation (`Means s p ∧ ∃ w w', Initiates s w w' p`).
2. Choice field vs. Strong choice:
   - `ChoiceField(s,p,q)` : weak choice = means p + incompatibility (alternatives available in reality).
   - `Chooses(s,p,q)`     : strong choice = means p + means q + incompatibility (both horns co-meant in thought).
3. Field ≠ Choice, Choice → FreeWill:
   - `ChoiceField ≠ Chooses`: having a contradictory proposition ¬p available in the object language
     does NOT imply that the agent represents that proposition (`Means s (¬p)`). Object-language
     contradiction is free logic; cognitive representation is an intentional achievement.
   - `Chooses → FreeWill`: definitional (`FreeWill s := ∃ p q, Chooses s p q`).
-/

namespace CountermodelVeridicalMeaning

-- Single subject, veridical meaning: `Unit` with `Means () p := p`.
namespace Single

def S : Type := Unit
def State : Type := Unit
def M (_s : S) (p : Prop) : Prop := p
def Initiates (_s : S) (_w _w' : State) (p : Prop) : Prop := p
def A (s : S) (p : Prop) : Prop := M s p ∧ ∃ w w' : State, Initiates s w w' p
def Person (s : S) : Prop := ∃ p : Prop, M s p
def Chooses (s : S) (p q : Prop) : Prop := M s p ∧ M s q ∧ Logos.Alternatives.Incompatible p q
def FreeWill (s : S) : Prop := ∃ p q : Prop, Chooses s p q
def Asserts (s : S) (p : Prop) : Prop := A s p ∧ p
def Selects (s : S) (p q : Prop) : Prop :=
  Asserts s p ∧ Logos.Alternatives.Incompatible p q ∧ ¬ Asserts s q
def DeliberateChoice (s : S) (p q : Prop) : Prop :=
  M s p ∧ M s q ∧ Logos.Alternatives.Incompatible p q ∧ Asserts s p ∧ ¬ Asserts s q

theorem act_datum_holds : ∃ s : S, ∃ p : Prop, A s p :=
  ⟨(), True, trivial, (), (), trivial⟩

theorem field_holds : ∃ s : S, ∃ p q : Prop, M s p ∧ Logos.Alternatives.Incompatible p q := by
  exact ⟨(), True, False, trivial, fun h => h.2⟩

theorem selection_holds : ∃ s : S, ∃ p q : Prop, Selects s p q := by
  refine ⟨(), True, False, ⟨⟨trivial, (), (), trivial⟩, trivial⟩, fun h => h.2, ?_⟩
  rintro ⟨⟨_, _, _, hFalse⟩, _⟩
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
  exact hnp.1 hp.1

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
    refine ⟨⟨⟨trivial, (), (), trivial⟩, trivial⟩, hI, ?_⟩
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
  · exact ⟨(), True, ⟨trivial, (), (), trivial⟩, trivial⟩
  · rintro ⟨_s, _p, hAss, hMn⟩
    exact hMn hAss.2

/-- Unilateral meaning witness: a subject means a proposition while not meaning its negation. -/
theorem unilateral_meaning_witness : ∃ s : S, ∃ p : Prop, M s p ∧ ¬ M s (¬ p) :=
  ⟨(), True, trivial, fun h => h trivial⟩

/-- Bilateral intentionality fails in the veridical model: meaning p does not force meaning ¬p. -/
theorem bilateral_intentionality_fails : ¬ (∀ (s : S) (p : Prop), M s p → M s (¬ p)) := by
  intro h
  have hF : M () (¬ True) := h () True trivial
  exact hF trivial

/-- Hostile witness: an intentional act occurs positing True, yet the subject does not mean ¬True. -/
theorem unilateral_act_witness : ∃ s : S, ∃ p : Prop, A s p ∧ ¬ M s (¬ p) :=
  ⟨(), True, ⟨trivial, (), (), trivial⟩, fun h => h trivial⟩

/-- Act polarity fails in the veridical model: performing an act positing p does not force meaning ¬p. -/
theorem act_polarity_fails : ¬ (∀ (s : S) (p : Prop), A s p → M s (¬ p)) := by
  intro h
  have hF : M () (¬ True) := h () True ⟨trivial, (), (), trivial⟩
  exact hF trivial

end Single

-- Two persons, veridical meaning: `Bool` with `Means _ p := p`, mirroring
-- the agency/choice/order fragment (Person, Correct/Incorrect, Fallible).
namespace TwoPersons

def S : Type := Bool
def State : Type := Unit
def M (_s : S) (p : Prop) : Prop := p
def Initiates (_s : S) (_w _w' : State) (p : Prop) : Prop := p
def A (s : S) (p : Prop) : Prop := M s p ∧ ∃ w w' : State, Initiates s w w' p
def Person (s : S) : Prop := ∃ p : Prop, M s p
def Chooses (s : S) (p q : Prop) : Prop := M s p ∧ M s q ∧ Logos.Alternatives.Incompatible p q
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
def Doubts (s : S) (p : Prop) : Prop := M s p ∧ M s (¬ p)

theorem act_datum_holds : ∃ s : S, ∃ p : Prop, A s p :=
  ⟨false, True, trivial, (), (), trivial⟩

theorem assertion_holds : ∃ s : S, ∃ p : Prop, Asserts s p :=
  ⟨false, True, ⟨trivial, (), (), trivial⟩, trivial⟩

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
  refine ⟨false, True, False, ⟨trivial, (), (), trivial⟩, ?_, ?_⟩
  · exact Or.inl ⟨⟨trivial, (), (), trivial⟩, trivial⟩
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
  exact hnp.1 hp.1

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

theorem no_doubt : ¬ ∃ s : S, ∃ p : Prop, Doubts s p := by
  rintro ⟨s, p, hp, hnp⟩
  exact hnp hp

/-- Hostile separation: an intentional act occurs, yet doubt is impossible. -/
theorem act_does_not_imply_doubt :
    (∃ s : S, ∃ p : Prop, A s p) ∧
    ¬ (∃ s : S, ∃ p : Prop, Doubts s p) :=
  ⟨act_datum_holds, no_doubt⟩

/-- Hostile separation: an assertive commitment occurs, yet doubt is impossible. -/
theorem asserts_does_not_imply_doubt :
    (∃ s : S, ∃ p : Prop, Asserts s p) ∧
    ¬ (∃ s : S, ∃ p : Prop, Doubts s p) :=
  ⟨assertion_holds, no_doubt⟩

/-- Hostile separation: judgment commits right/wrong, yet doubt is impossible. -/
theorem judgment_does_not_imply_doubt :
    (∃ (s : S) (p q : Prop), A s p ∧ (Correct s p ∨ Incorrect s p) ∧ Logos.Alternatives.Incompatible p q) ∧
    ¬ (∃ s : S, ∃ p : Prop, Doubts s p) :=
  ⟨judge_commits_holds, no_doubt⟩

/-- Hostile separation, full fragment: act datum, assertion, two distinct persons,
    right-and-wrong, judge committing a choice field, and fallibility all hold —
    yet Cartesian doubt is provably empty. -/
theorem full_fragment_without_doubt :
    (∃ s : S, ∃ p : Prop, Asserts s p) ∧
    (∃ s₁ s₂ : S, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂) ∧
    ((¬ (∀ p : Prop, ¬ T p)) ∧ (¬ (∀ p : Prop, T p))) ∧
    (∃ (s : S) (p q : Prop), A s p ∧ (Correct s p ∨ Incorrect s p) ∧ Logos.Alternatives.Incompatible p q) ∧
    (∃ (s : S) (p : Prop), Fallible s p ∧ IsFalse p) ∧
    ¬ (∃ s : S, ∃ p : Prop, Doubts s p) :=
  ⟨assertion_holds, two_persons_exist, rightWrong_holds, judge_commits_holds,
   fallibility_holds, no_doubt⟩

def NoAct : Prop := ¬ ∃ s : S, ∃ p : Prop, A s p

theorem noAct_selfRefutes (speaker : S) : Asserts speaker NoAct → False := by
  rintro ⟨hA, hNoAct⟩
  exact hNoAct ⟨speaker, NoAct, hA⟩

def FreeSubject (s : S) : Prop := FreeWill s

/-- Personhood does not imply a Free Subject:
    In TwoPersons, two distinct ontological persons exist, yet neither is a FreeSubject. -/
theorem person_does_not_imply_freeSubject :
    (∃ s : S, Person s) ∧ ¬ (∃ s : S, FreeSubject s) :=
  ⟨⟨false, True, trivial⟩, fun ⟨s, p, q, hChooses⟩ => no_genuine_choice ⟨s, p, q, hChooses⟩⟩

/-- Transcendental retorsion holds fully in TwoPersons, yet Cartesian doubt is empty. -/
theorem retorsion_does_not_imply_doubt :
    (∀ speaker : S, Asserts speaker NoAct → False) ∧
    ¬ (∃ s : S, ∃ p : Prop, Doubts s p) :=
  ⟨noAct_selfRefutes, no_doubt⟩

/-- Unilateral meaning witness: an intentional subject means a proposition while not meaning its negation. -/
theorem unilateral_meaning_witness : ∃ s : S, ∃ p : Prop, M s p ∧ ¬ M s (¬ p) :=
  ⟨false, True, trivial, fun h => h trivial⟩

/-- Bilateral intentionality fails in the two-person veridical model. -/
theorem bilateral_intentionality_fails : ¬ (∀ (s : S) (p : Prop), M s p → M s (¬ p)) := by
  intro h
  have hF : M false (¬ True) := h false True trivial
  exact hF trivial

/-- Hostile separation, full fragment with unilateral meaning: all agency, plurality,
    normative, judgment, and fallibility axioms hold while meaning is strictly unilateral. -/
theorem full_fragment_with_unilateral_meaning :
    (∃ s : S, ∃ p : Prop, A s p) ∧
    (∃ s₁ s₂ : S, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂) ∧
    ((¬ (∀ p : Prop, ¬ T p)) ∧ (¬ (∀ p : Prop, T p))) ∧
    (∃ (s : S) (p q : Prop), A s p ∧ (Correct s p ∨ Incorrect s p) ∧ Logos.Alternatives.Incompatible p q) ∧
    (∃ (s : S) (p : Prop), Fallible s p ∧ IsFalse p) ∧
    (∃ s : S, ∃ p : Prop, M s p ∧ ¬ M s (¬ p)) :=
  ⟨act_datum_holds, two_persons_exist, rightWrong_holds, judge_commits_holds,
   fallibility_holds, unilateral_meaning_witness⟩

/-- Hostile witness: an intentional act occurs in the two-person fragment, yet the agent does not mean ¬p. -/
theorem unilateral_act_witness : ∃ s : S, ∃ p : Prop, A s p ∧ ¬ M s (¬ p) :=
  ⟨false, True, ⟨trivial, (), (), trivial⟩, fun h => h trivial⟩

/-- Act polarity fails in the two-person veridical model: the act positing True does not force meaning ¬True. -/
theorem act_polarity_fails : ¬ (∀ (s : S) (p : Prop), A s p → M s (¬ p)) := by
  intro h
  have hF : M false (¬ True) := h false True ⟨trivial, (), (), trivial⟩
  exact hF trivial

/-- Hostile separation, full fragment with unilateral act: all agency, plurality,
    normative, judgment, and fallibility axioms hold while act polarity provably fails.
    Demonstrates that AxActPolarity is an irreducible semantic commitment of the current architecture. -/
theorem full_fragment_with_unilateral_act :
    (∃ s : S, ∃ p : Prop, A s p) ∧
    (∃ s₁ s₂ : S, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂) ∧
    ((¬ (∀ p : Prop, ¬ T p)) ∧ (¬ (∀ p : Prop, T p))) ∧
    (∃ (s : S) (p q : Prop), A s p ∧ (Correct s p ∨ Incorrect s p) ∧ Logos.Alternatives.Incompatible p q) ∧
    (∃ (s : S) (p : Prop), Fallible s p ∧ IsFalse p) ∧
    (∃ s : S, ∃ p : Prop, A s p ∧ ¬ M s (¬ p)) :=
  ⟨act_datum_holds, two_persons_exist, rightWrong_holds, judge_commits_holds,
   fallibility_holds, unilateral_act_witness⟩

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

/-- Separation: the act datum does not force universal bilateral intentionality. -/
theorem not_entails_bilateral_intentionality :
    ¬ (∀ I : GenuineChoiceSignature, GCdatum I → ∀ (s : I.Subject) (p : Prop), I.Means s p → I.Means s (¬ p)) := by
  intro h
  let I : GenuineChoiceSignature := { Subject := Unit, Means := fun _ p => p }
  have hd : GCdatum I := ⟨(), True, trivial⟩
  have hF : I.Means () (¬ True) := h I hd () True trivial
  exact hF trivial

/-- Separation: act datum plus plurality still does not force bilateral intentionality. -/
theorem not_entails_bilateral_intentionality_with_plurality :
    ¬ (∀ I : GenuineChoiceSignature, GCdatum I ∧ Γ_twoGCSubjects I →
        ∀ (s : I.Subject) (p : Prop), I.Means s p → I.Means s (¬ p)) := by
  intro h
  let I : GenuineChoiceSignature := { Subject := Bool, Means := fun _ p => p }
  have hd : GCdatum I ∧ Γ_twoGCSubjects I := by
    constructor
    · exact ⟨false, True, trivial⟩
    · refine ⟨true, false, ⟨True, trivial⟩, ⟨True, trivial⟩, fun heq => by cases heq⟩
  have hF : I.Means false (¬ True) := (h I hd) false True trivial
  exact hF trivial

structure ActSignature where
  Subject : Type
  State : Type
  Means : Subject → Prop → Prop
  Initiates : Subject → State → State → Prop → Prop

def ActOf (I : ActSignature) (s : I.Subject) (p : Prop) : Prop :=
  I.Means s p ∧ ∃ w w' : I.State, I.Initiates s w w' p

def ActDatum (I : ActSignature) : Prop :=
  ∃ s : I.Subject, ∃ p : Prop, ActOf I s p

def ActTwoSubjects (I : ActSignature) : Prop :=
  ∃ s₁ s₂ : I.Subject, (∃ p, I.Means s₁ p) ∧ (∃ p, I.Means s₂ p) ∧ s₁ ≠ s₂

/-- Separation: the performative act datum does not force Act Polarity under the Logos signature. -/
theorem not_entails_act_polarity :
    ¬ (∀ I : ActSignature, ActDatum I → ∀ (s : I.Subject) (p : Prop), ActOf I s p → I.Means s (¬ p)) := by
  intro h
  let I : ActSignature := {
    Subject := Unit,
    State := Unit,
    Means := fun _ p => p,
    Initiates := fun _ _ _ p => p
  }
  have hd : ActDatum I := ⟨(), True, trivial, (), (), trivial⟩
  have ha : ActOf I () True := ⟨trivial, (), (), trivial⟩
  have hF : I.Means () (¬ True) := h I hd () True ha
  exact hF trivial

/-- Separation: act datum plus plurality still does not force Act Polarity. -/
theorem not_entails_act_polarity_with_plurality :
    ¬ (∀ I : ActSignature, ActDatum I ∧ ActTwoSubjects I →
        ∀ (s : I.Subject) (p : Prop), ActOf I s p → I.Means s (¬ p)) := by
  intro h
  let I : ActSignature := {
    Subject := Bool,
    State := Unit,
    Means := fun _ p => p,
    Initiates := fun _ _ _ p => p
  }
  have hd : ActDatum I ∧ ActTwoSubjects I := by
    constructor
    · exact ⟨false, True, trivial, (), (), trivial⟩
    · refine ⟨true, false, ⟨True, trivial⟩, ⟨True, trivial⟩, fun heq => by cases heq⟩
  have ha : ActOf I false True := ⟨trivial, (), (), trivial⟩
  have hF : I.Means false (¬ True) := (h I hd) false True ha
  exact hF trivial

-- ===========================================================================
-- Pre-A13 Agency Theory Independence: Claim B
-- ===========================================================================

/-
### 14-Row Candidate Derivation Route Audit Table (`Act s p` to `Means s (¬p)`):

| Route | Intermediate Step | Classification | Exact Mathematical Obstruction |
|---|---|---|---|
| 1. Act → Means p | Analytic unrolling | DERIVES | `Act s p := Means s p ∧ ...`; only yields positive horn `Means s p`. |
| 2. Act → Asserts | Factive commitment | REQUIRES A NEW BRIDGE | Requires `act_implies_asserts_bridge` (factual truth of `p`). |
| 3. Act → Correct ∨ Incorrect | Bivalent partition | DERIVES | Proved via `act_iff_correct_or_incorrect` (C101). |
| 4. Correct/Incorrect → Means ¬p | Normative truth-value | DOES NOT DERIVE | Concerns truth-value of `p`, not mental representation of `¬p`. |
| 5. ChoiceField → Means ¬p | Incompatible availability | DOES NOT DERIVE | `¬p` occurs only in `Incompatible p (¬p) := ¬(p ∧ ¬p)`, not in `Means s _`. |
| 6. DeliberateChoice → Means ¬p | Deliberative co-meaning | REQUIRES A NEW BRIDGE | `DeliberateChoice` defines co-meaning, but `Act → DeliberateChoice` does not derive. |
| 7. Bivalence / LEM → Means ¬p | Propositional excluded middle | DOES NOT DERIVE | Intensional barrier: `p ∨ ¬p` in `Prop` does not force `Means s (¬p)`. |
| 8. Truth / Falsehood → Means ¬p | Semantic status | DOES NOT DERIVE | External truth-values do not populate intentional relations. |
| 9. Retorsion → Means ¬p | Performative contradiction | DOES NOT DERIVE | Refutes `NoAct`; does not force every act to co-mean contradictory negations. |
| 10. Intentional → Means ¬p | Representation faculty | DOES NOT DERIVE | `Intentional s := ∃ p, Means s p` provides only a single content. |
| 11. Person → Means ¬p | Rational personhood | DOES NOT DERIVE | Inherits only single intentional content of `Intentional s`. |
| 12. Plurality → Means ¬p | Distinct subjects | DOES NOT DERIVE | `AxTwoSubjects` gives two distinct subjects with single contents, not dual co-meaning. |
| 13. Modal Principles → Means ¬p | Propositional necessity | DOES NOT DERIVE | Modal backbone governs world-satisfaction, not internal cognitive representation. |
| 14. Grounding Principles → Means ¬p | Entity grounding | DOES NOT DERIVE | `Ground e p` relates entities to propositions, entirely outside `Means`. |
-/

structure PreA13AgencySignature where
  Subject : Type
  State : Type
  Means : Subject → Prop → Prop
  Initiates : Subject → State → State → Prop → Prop
  T : Prop → Prop
  IsFalse : Prop → Prop

def PreA13Act (I : PreA13AgencySignature) (s : I.Subject) (p : Prop) : Prop :=
  I.Means s p ∧ ∃ w w' : I.State, I.Initiates s w w' p

def PreA13Person (I : PreA13AgencySignature) (s : I.Subject) : Prop :=
  ∃ p : Prop, I.Means s p

def PreA13Correct (I : PreA13AgencySignature) (s : I.Subject) (p : Prop) : Prop :=
  PreA13Act I s p ∧ I.T p

def PreA13Incorrect (I : PreA13AgencySignature) (s : I.Subject) (p : Prop) : Prop :=
  PreA13Act I s p ∧ I.IsFalse p

def PreA13Fallible (I : PreA13AgencySignature) (_s : I.Subject) (p : Prop) : Prop :=
  I.IsFalse p

/-- The pre-A13 agency-side theory relevant to F1b:
    bundles (1) act datum, (2) plurality of two distinct persons, (3) bivalent normative order,
    (4) judge committing a choice field, (5) fallibility, (6) transcendental retorsion,
    and (7) C101 bivalent partition.
    Precisely scoped to the agency/normative fragment that could participate in deriving AxActPolarity. -/
def PreA13AgencyTheory (I : PreA13AgencySignature) : Prop :=
  -- 1. Performative Act Datum
  (∃ s : I.Subject, ∃ p : Prop, PreA13Act I s p) ∧
  -- 2. Two distinct persons (Plurality / AxTwoSubjects conclusion)
  (∃ s₁ s₂ : I.Subject, PreA13Person I s₁ ∧ PreA13Person I s₂ ∧ s₁ ≠ s₂) ∧
  -- 3. Bivalent normative order (Right/Wrong)
  ((¬ ∀ p : Prop, ¬ I.T p) ∧ (¬ ∀ p : Prop, I.T p)) ∧
  -- 4. Judge commits a choice field
  (∃ (s : I.Subject) (p q : Prop), PreA13Act I s p ∧ (PreA13Correct I s p ∨ PreA13Incorrect I s p) ∧ Logos.Alternatives.Incompatible p q) ∧
  -- 5. Fallibility
  (∃ (s : I.Subject) (p : Prop), PreA13Fallible I s p ∧ I.IsFalse p) ∧
  -- 6. Transcendental retorsion
  (∀ (speaker : I.Subject), (PreA13Act I speaker (¬ ∃ s p, PreA13Act I s p) ∧ (¬ ∃ s p, PreA13Act I s p)) → False) ∧
  -- 7. C101 bivalent partition
  (∀ (s : I.Subject) (p : Prop), PreA13Act I s p ↔ (PreA13Act I s p ∧ p) ∨ PreA13Incorrect I s p)

/-- Concrete two-subject hostile agency model instance.
    Two subjects (Bool: true, false), unit state (Unit), veridical meaning (Means s p := p),
    initiation (Initiates s w w' p := p), truth (T p := p), and falsehood (IsFalse p := ¬p). -/
def hostileAgencyInstance : PreA13AgencySignature := {
  Subject := Bool,
  State := Unit,
  Means := fun _ p => p,
  Initiates := fun _ _ _ p => p,
  T := fun p => p,
  IsFalse := fun p => ¬ p
}

theorem hostile_act_datum : ∃ s p, PreA13Act hostileAgencyInstance s p :=
  ⟨false, True, trivial, (), (), trivial⟩

theorem hostile_two_persons :
    ∃ s₁ s₂ : hostileAgencyInstance.Subject,
      PreA13Person hostileAgencyInstance s₁ ∧
      PreA13Person hostileAgencyInstance s₂ ∧ s₁ ≠ s₂ := by
  refine ⟨true, false, ⟨True, trivial⟩, ⟨True, trivial⟩, ?_⟩
  intro h
  cases h

theorem hostile_right_wrong :
    (¬ ∀ p : Prop, ¬ hostileAgencyInstance.T p) ∧
    (¬ ∀ p : Prop, hostileAgencyInstance.T p) := by
  constructor
  · intro h
    exact h True trivial
  · intro h
    exact h False

theorem hostile_judge_commits :
    ∃ (s : hostileAgencyInstance.Subject) (p q : Prop),
      PreA13Act hostileAgencyInstance s p ∧
      (PreA13Correct hostileAgencyInstance s p ∨ PreA13Incorrect hostileAgencyInstance s p) ∧
      Logos.Alternatives.Incompatible p q := by
  refine ⟨false, True, False, ⟨trivial, (), (), trivial⟩, ?_, ?_⟩
  · exact Or.inl ⟨⟨trivial, (), (), trivial⟩, trivial⟩
  · intro h
    exact h.2

theorem hostile_fallibility :
    ∃ (s : hostileAgencyInstance.Subject) (p : Prop),
      PreA13Fallible hostileAgencyInstance s p ∧ hostileAgencyInstance.IsFalse p :=
  ⟨false, False, fun h => h, fun h => h⟩

theorem hostile_retorsion :
    ∀ (speaker : hostileAgencyInstance.Subject),
      (PreA13Act hostileAgencyInstance speaker (¬ ∃ s p, PreA13Act hostileAgencyInstance s p) ∧
        (¬ ∃ s p, PreA13Act hostileAgencyInstance s p)) → False := by
  intro speaker ⟨⟨_, _, _, hNoAct⟩, hNoAct2⟩
  exact hNoAct2 ⟨speaker, _, ⟨trivial, (), (), trivial⟩⟩

theorem hostile_c101 :
    ∀ (s : hostileAgencyInstance.Subject) (p : Prop),
      PreA13Act hostileAgencyInstance s p ↔
        (PreA13Act hostileAgencyInstance s p ∧ p) ∨ PreA13Incorrect hostileAgencyInstance s p := by
  intro s p
  constructor
  · intro ha
    by_cases hp : p
    · exact Or.inl ⟨ha, hp⟩
    · exact Or.inr ⟨ha, hp⟩
  · rintro (⟨ha, _⟩ | ⟨ha, _⟩)
    · exact ha
    · exact ha

/-- Step-by-step verification that hostileAgencyInstance satisfies all 7 clauses of PreA13AgencyTheory. -/
theorem hostileAgencyTheory_holds : PreA13AgencyTheory hostileAgencyInstance :=
  ⟨hostile_act_datum,
   hostile_two_persons,
   hostile_right_wrong,
   hostile_judge_commits,
   hostile_fallibility,
   hostile_retorsion,
   hostile_c101⟩

def PreA13ChoiceField (I : PreA13AgencySignature) (s : I.Subject) (p q : Prop) : Prop :=
  PreA13Act I s p ∧ Logos.Alternatives.Incompatible p q

def PreA13Chooses (I : PreA13AgencySignature) (s : I.Subject) (p q : Prop) : Prop :=
  I.Means s p ∧ I.Means s q ∧ Logos.Alternatives.Incompatible p q

/-- Key semantic assignment of the hostile model:
    The acting subject means True, does not mean ¬True, and an intentional Act occurs. -/
theorem hostile_semantic_assignment :
    hostileAgencyInstance.Means false True ∧
    ¬ hostileAgencyInstance.Means false (¬ True) ∧
    PreA13Act hostileAgencyInstance false True :=
  ⟨trivial, fun h => h trivial, ⟨trivial, (), (), trivial⟩⟩

/-- Separation of ChoiceField and Chooses in hostileAgencyInstance:
    The agent commits a ChoiceField between True and False,
    yet genuine Chooses between True and False is completely false. -/
theorem hostile_choice_field_holds :
    PreA13ChoiceField hostileAgencyInstance false True False :=
  ⟨⟨trivial, (), (), trivial⟩, fun h => h.2⟩

theorem hostile_no_chooses :
    ¬ PreA13Chooses hostileAgencyInstance false True False := by
  rintro ⟨_, hq, _⟩
  exact hq

theorem hostile_choice_field_not_implies_chooses :
    PreA13ChoiceField hostileAgencyInstance false True False ∧
    ¬ PreA13Chooses hostileAgencyInstance false True False :=
  ⟨hostile_choice_field_holds, hostile_no_chooses⟩

/-- Hostile separation establishing Claim B:
    ActPolarity is NOT derivable from the pre-A13 agency-side theory relevant to F1b.
    Even when all 7 core agency, plurality, normative, judgment, fallibility, and retorsion
    principles of Γ hold simultaneously, an intentional act positing True does not force
    the subject to represent its contradictory negation ¬True.

    Note on Claim C: This model explicitly interprets the agency/normative fragment
    (Subject, State, Means, Initiates, Act, Person, Correct, Incorrect, Fallible).
    It does not interpret the non-agency grounding/axioms (A1, A3, A4, A7, A8, A9);
    therefore Claim C is not formally established by this signature model alone, but holds
    metatheoretically by conservative extension because those axioms do not mention Means. -/
theorem not_entails_act_polarity_from_preA13 :
    ¬ (∀ I : PreA13AgencySignature, PreA13AgencyTheory I →
        ∀ (s : I.Subject) (p : Prop), PreA13Act I s p → I.Means s (¬ p)) := by
  intro h
  have hF : hostileAgencyInstance.Means false (¬ True) :=
    (h hostileAgencyInstance hostileAgencyTheory_holds) false True hostile_semantic_assignment.2.2
  exact hostile_semantic_assignment.2.1 hF

/-- Hostile separation establishing that even the cheaper existential polarity premise:
    `∃ s p, Act s p ∧ Means s (¬p)`
    is NOT derivable from the pre-A13 agency-side theory.
    In hostileAgencyInstance, any act positing p requires p to be True,
    while Means s (¬p) requires ¬p to be True, which is an absolute contradiction (p ∧ ¬p). -/
theorem not_entails_existential_polarity_from_preA13 :
    ¬ (∀ I : PreA13AgencySignature, PreA13AgencyTheory I →
        ∃ (s : I.Subject) (p : Prop), PreA13Act I s p ∧ I.Means s (¬ p)) := by
  intro h
  obtain ⟨_s, p, ha, hmn⟩ := h hostileAgencyInstance hostileAgencyTheory_holds
  have hp : p := ha.1
  have hnp : ¬ p := hmn
  exact hnp hp

-- ===========================================================================
-- Full Pre-A13 Theory Independence (Desired Outcomes 3 & 4)
-- Interprets all 12 pre-A13 axioms of Γ across all modules simultaneously.
-- ===========================================================================

structure PreA13FullTheorySignature where
  Subject : Type
  State : Type
  Entity : Type
  World : Type
  Means : Subject → Prop → Prop
  Initiates : Subject → State → State → Prop → Prop
  T : Prop → Prop
  IsFalse : Prop → Prop
  Ground : Entity → Prop → Prop
  GroundProp : Entity → Prop → Prop
  Personal : Entity → Prop
  IsPresentPersonalFeature : Prop → Prop

def FullAct (I : PreA13FullTheorySignature) (s : I.Subject) (p : Prop) : Prop :=
  I.Means s p ∧ ∃ w w' : I.State, I.Initiates s w w' p

def FullPerson (I : PreA13FullTheorySignature) (s : I.Subject) : Prop :=
  ∃ p : Prop, I.Means s p

/-- The complete pre-A13 theory of Γ:
    bundles all 12 pre-A13 axioms across Agency, Plurality, Modal, and Value:
    1. Performative Act Datum (∃ s p, Act s p)
    2. Plurality of two distinct persons (AxTwoSubjects conclusion)
    3. Bivalent normative order ((¬ ∀ p, ¬ T p) ∧ (¬ ∀ p, T p))
    4. Entity grounding (∀ p, T p → ∃ e, I.Ground e p)
    5. Global ground existence (∃ e, ∀ p, T p → I.Ground e p)
    6. GroundPrincipleProp (∀ p, T p → ∃ e, I.GroundProp e p)
    7. AxPersonalGround (∀ p, I.IsPresentPersonalFeature p → ∃ e, I.GroundProp e p ∧ I.Personal e)
    8. Fallibility (∃ s p, IsFalse p)
    9. Transcendental retorsion (∀ speaker, (FullAct I speaker NoAct ∧ NoAct) → False)
    10. C101 bivalent partition (∀ s p, FullAct I s p ↔ (FullAct I s p ∧ p) ∨ (FullAct I s p ∧ I.IsFalse p)) -/
def PreA13FullTheory (I : PreA13FullTheorySignature) : Prop :=
  -- 1. Performative Act Datum
  (∃ s : I.Subject, ∃ p : Prop, FullAct I s p) ∧
  -- 2. Plurality of two distinct persons (AxTwoSubjects conclusion)
  (∃ s₁ s₂ : I.Subject, FullPerson I s₁ ∧ FullPerson I s₂ ∧ s₁ ≠ s₂) ∧
  -- 3. Bivalent normative order
  ((¬ ∀ p : Prop, ¬ I.T p) ∧ (¬ ∀ p : Prop, I.T p)) ∧
  -- 4. Entity Grounding
  (∀ p : Prop, I.T p → ∃ e : I.Entity, I.Ground e p) ∧
  -- 5. Global ground
  (∃ e : I.Entity, ∀ p : Prop, I.T p → I.Ground e p) ∧
  -- 6. GroundPrincipleProp
  (∀ p : Prop, I.T p → ∃ e : I.Entity, I.GroundProp e p) ∧
  -- 7. AxPersonalGround
  (∀ p : Prop, I.IsPresentPersonalFeature p → ∃ e : I.Entity, I.GroundProp e p ∧ I.Personal e) ∧
  -- 8. Fallibility
  (∃ (_s : I.Subject) (p : Prop), I.IsFalse p) ∧
  -- 9. Transcendental retorsion
  (∀ (speaker : I.Subject), (FullAct I speaker (¬ ∃ s p, FullAct I s p) ∧ (¬ ∃ s p, FullAct I s p)) → False) ∧
  -- 10. C101 bivalent partition
  (∀ (s : I.Subject) (p : Prop), FullAct I s p ↔ (FullAct I s p ∧ p) ∨ (FullAct I s p ∧ I.IsFalse p))

/-- Concrete hostile instance of the entire pre-A13 theory of Γ. -/
def fullTheoryHostileInstance : PreA13FullTheorySignature := {
  Subject := Bool,
  State := Unit,
  Entity := Unit,
  World := Unit,
  Means := fun _ p => p,
  Initiates := fun _ _ _ p => p,
  T := fun p => p,
  IsFalse := fun p => ¬ p,
  Ground := fun _ _ => True,
  GroundProp := fun _ _ => True,
  Personal := fun _ => True,
  IsPresentPersonalFeature := fun _ => True
}

/-- Step-by-step verification that all 12 pre-A13 axioms of Γ hold simultaneously in fullTheoryHostileInstance. -/
theorem fullTheory_holds : PreA13FullTheory fullTheoryHostileInstance := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨false, True, trivial, (), (), trivial⟩
  · refine ⟨true, false, ⟨True, trivial⟩, ⟨True, trivial⟩, fun heq => by cases heq⟩
  · exact ⟨fun h => h True trivial, fun h => h False⟩
  · intro p hp; exact ⟨(), trivial⟩
  · exact ⟨(), fun _ _ => trivial⟩
  · intro p hp; exact ⟨(), trivial⟩
  · intro p hp; exact ⟨(), trivial, trivial⟩
  · exact ⟨false, False, fun h => h⟩
  · rintro speaker ⟨⟨_, _, _, hNoAct⟩, hNoAct2⟩
    exact hNoAct2 ⟨speaker, _, ⟨trivial, (), (), trivial⟩⟩
  · intro s p
    constructor
    · intro ha
      by_cases hp : p
      · exact Or.inl ⟨ha, hp⟩
      · exact Or.inr ⟨ha, hp⟩
    · rintro (⟨ha, _⟩ | ⟨ha, _⟩)
      · exact ha
      · exact ha

/-- Full-Theory Independence Theorem (Desired Outcome 3):
    Universal AxActPolarity is strictly independent of the ENTIRE pre-A13 theory of Γ.
    Even when all 12 axioms across Agency, Plurality, Modal,
    and Value hold simultaneously, an intentional Act positing True does not force Means (¬True). -/
theorem not_entails_act_polarity_from_full_theory :
    ¬ (∀ I : PreA13FullTheorySignature, PreA13FullTheory I →
        ∀ (s : I.Subject) (p : Prop), FullAct I s p → I.Means s (¬ p)) := by
  intro h
  have hF : fullTheoryHostileInstance.Means false (¬ True) :=
    (h fullTheoryHostileInstance fullTheory_holds) false True ⟨trivial, (), (), trivial⟩
  exact hF trivial

/-- Full-Theory Existential Independence Theorem (Desired Outcome 3 & 4):
    Even the cheaper existential polarity resource `∃ s p, Act s p ∧ Means s (¬p)`
    is strictly independent of the ENTIRE pre-A13 theory of Γ.
    In any model where meaning is factive (Means s p → p), co-meaning both horns
    forces p ∧ ¬p, which is an absolute classical contradiction. -/
theorem not_entails_existential_polarity_from_full_theory :
    ¬ (∀ I : PreA13FullTheorySignature, PreA13FullTheory I →
        ∃ (s : I.Subject) (p : Prop), FullAct I s p ∧ I.Means s (¬ p)) := by
  intro h
  obtain ⟨_s, p, ha, hmn⟩ := h fullTheoryHostileInstance fullTheory_holds
  have hp : p := ha.1
  have hnp : ¬ p := hmn
  exact hnp hp

/-- Genuine choice relation within a PreA13FullTheorySignature. -/
def FullChooses (I : PreA13FullTheorySignature) (s : I.Subject) (p q : Prop) : Prop :=
  I.Means s p ∧ I.Means s q ∧ Logos.Alternatives.Incompatible p q

/-- Free will predicate within a PreA13FullTheorySignature. -/
def FullFreeWill (I : PreA13FullTheorySignature) (s : I.Subject) : Prop :=
  ∃ p q : Prop, FullChooses I s p q

/-- Contrastive agency predicate within a PreA13FullTheorySignature. -/
def FullContrastiveAgency (I : PreA13FullTheorySignature) (s : I.Subject) (p : Prop) : Prop :=
  ∃ q : Prop, I.Means s q ∧ Logos.Alternatives.Incompatible p q

/-- Orthogonality of Strong Act and Genuine Choice in Pre-A13 Full Theory:
    In the presence of the entire pre-A13 axiomatic theory of Γ (12 axioms across
    Agency, Plurality, Modal, and Value),
    the existence of a strong intentional Act does NOT entail the existence of genuine Choice.
    Strong Act and Genuine Choice are formally orthogonal (Act ⟂ Chooses) in the base theory.

    Architectural Note: This orthogonality theorem is strictly scoped to the Pre-A13 theory of Γ.
    It demonstrates why genuine choice cannot be derived from pre-A13 primitives,
    motivating the explicit adoption of `AxIntentionalChoice` (Tag: SEM) as the constitutive
    principle of intentional action in the enlarged theory. -/
theorem act_orthogonal_to_genuine_choice_in_full_theory :
    ¬ (∀ I : PreA13FullTheorySignature, PreA13FullTheory I →
        (∃ (s : I.Subject) (p : Prop), FullAct I s p) →
        ∃ (s : I.Subject) (p q : Prop), FullChooses I s p q) := by
  intro h
  have hAct : ∃ (s : fullTheoryHostileInstance.Subject) (p : Prop), FullAct fullTheoryHostileInstance s p :=
    ⟨false, True, ⟨trivial, (), (), trivial⟩⟩
  obtain ⟨_s, p, q, hp, hq, hincomp⟩ := h fullTheoryHostileInstance fullTheory_holds hAct
  exact hincomp ⟨hp, hq⟩

/-- Orthogonality of Strong Act and Free Will in Pre-A13 Full Theory:
    Similarly, Strong Act does not entail Free Will in the pre-A13 theory. -/
theorem act_orthogonal_to_freewill_in_full_theory :
    ¬ (∀ I : PreA13FullTheorySignature, PreA13FullTheory I →
        (∃ (s : I.Subject) (p : Prop), FullAct I s p) →
        ∃ (s : I.Subject), FullFreeWill I s) := by
  intro h
  have hAct : ∃ (s : fullTheoryHostileInstance.Subject) (p : Prop), FullAct fullTheoryHostileInstance s p :=
    ⟨false, True, ⟨trivial, (), (), trivial⟩⟩
  obtain ⟨_s, p, q, hp, hq, hincomp⟩ := h fullTheoryHostileInstance fullTheory_holds hAct
  exact hincomp ⟨hp, hq⟩

/-- Orthogonality of Strong Act and Contrastive Agency in Pre-A13 Full Theory:
    Strong Act does not entail that the acting agent represents an incompatible alternative. -/
theorem act_orthogonal_to_contrastive_agency_in_full_theory :
    ¬ (∀ I : PreA13FullTheorySignature, PreA13FullTheory I →
        ∀ (s : I.Subject) (p : Prop), FullAct I s p → FullContrastiveAgency I s p) := by
  intro h
  have hAct : FullAct fullTheoryHostileInstance false True := ⟨trivial, (), (), trivial⟩
  obtain ⟨q, hq, hincomp⟩ := h fullTheoryHostileInstance fullTheory_holds false True hAct
  exact hincomp ⟨trivial, hq⟩

/-- Existential Orthogonality: Strong Act does not even entail the existence of any
    contrastive agent under the full pre-A13 theory. -/
theorem act_orthogonal_to_existential_contrastive_agency_in_full_theory :
    ¬ (∀ I : PreA13FullTheorySignature, PreA13FullTheory I →
        (∃ (s : I.Subject) (p : Prop), FullAct I s p) →
        ∃ (s : I.Subject) (p : Prop), FullAct I s p ∧ FullContrastiveAgency I s p) := by
  intro h
  have hAct : ∃ (s : fullTheoryHostileInstance.Subject) (p : Prop), FullAct fullTheoryHostileInstance s p :=
    ⟨false, True, ⟨trivial, (), (), trivial⟩⟩
  obtain ⟨_s, p, ha, q, hq, hincomp⟩ := h fullTheoryHostileInstance fullTheory_holds hAct
  have hp : p := ha.1
  have hq_true : q := hq
  exact hincomp ⟨hp, hq_true⟩

-- ===========================================================================
-- Part G: The Four-Model Hierarchy (M0, M1, M2, M3)
-- Diagnostics of Act, ChoiceField, Chooses, and FreeSubject
-- ===========================================================================

namespace ModelHierarchy

/-
### Model M1: Strong Act / Factive Veridical Model (CountermodelVeridicalMeaning.TwoPersons)
- `Act false True`: TRUE
- `ChoiceField false True False`: TRUE
- `Chooses false True False`: FALSE
- `FreeWill false`: FALSE
-/

/-
### Six-Attack Audit on Deriving Polarity from Strong Act:

| Attack Vector | Candidate Principle | Outcome Classification | Hostile Witness / Model | Exact Separating Valuation & Analysis |
|---|---|---|---|---|
| **Attack 1 (Existential Act Polarity)** | `(∃ s p, Act s p) → ∃ s p, Act s p ∧ Means s (¬p)` | **C. REFUTED BY HOSTILE MODEL** | `fullTheoryHostileInstance` (`not_entails_existential_polarity_from_full_theory`) | Valuation: `s = false, p = True`. In veridical semantics (`Means s p := p`), `Act s p` forces $p$, while `Means s (¬p)` forces $\neg p$, making dual co-meaning an absolute contradiction ($p \land \neg p \equiv \bot$). |
| **Attack 2 (Semantics of Means)** | `Act s p → ∃ q, Means s q ∧ Incompatible p q` | **C. REFUTED BY HOSTILE MODEL** | `CountermodelVeridicalMeaning.Single` (`Single.no_genuine_choice`, `genuineChoice_requires_error_possibility`) | Valuation: `p = True`. If meaning is factive, any incompatible pair $p, q$ would require $p \land q \land \neg(p \land q) \equiv \bot$. Factive meaning mathematically excludes co-meaning incompatible alternatives. |
| **Attack 3 (Contrastive Initiation)** | `Branches (fun w w' => ∃ p, Initiates s w w' p) → ∃ q, Means s q ∧ Incompatible p q` | **C. REFUTED / D. REDUNDANT** | `ModelM2BranchingInitiation` (`m2_diagnostic_separation`) | For physical branching: **C. REFUTED** by Model M2 (`w = false ∧ w' ∈ {true, false}`); physical state transitions are extensional and do not force mental co-meaning. For intentional contrast: **D. REDUNDANT** (extensionally equivalent to A13). |
| **Attack 4 (DeliberateChoice Decomposition)** | `Act s p → ∃ q, DeliberateChoice s p q` | **C. REFUTED BY HOSTILE MODEL** | `hostileAgencyInstance` (`deliberateChoice_negation_decomposition`) | Valuation: `s = false, p = True, q = False`. Executive selection `Selects s p (¬p)` holds by assertion, but alternative awareness `Means s (¬p)` fails by veridicality. Deliberation fails strictly at the missing cognitive horn. |
| **Attack 5 (Performative Doubt & Retorsion)** | `(Asserts speaker NoAct → False) → ∃ s p, Doubts s p` | **C. REFUTED BY HOSTILE MODEL** | `TwoPersons.retorsion_does_not_imply_doubt` | Valuation: `NoAct := ¬ ∃ s p, Act s p`. Retorsion establishes that denying action is performatively self-refuting, but refutation of an assertion does not populate the agent's mind with dual contradictory contents. |
| **Attack 6 (C101 Normative Bivalence)** | `(Act s p ↔ Asserts s p ∨ Incorrect s p) → ∃ s p, Means s p ∧ Means s (¬p)` | **C. REFUTED BY HOSTILE MODEL** | `hostileAgencyInstance` (`hostile_c101`) | Valuation: `s = false, p = True`. Bivalent partition classifies the normative status of the posited content $p$ relative to reality; it tracks the world, not dual cognitive representations in the same subject $s$. |
-/

/-
### Model M2: Stronger Executive Initiation Semantics (Branching Initiation)
Shows that enriching `Initiates` with non-trivial state-space branching (`Branches`)
still fails to yield genuine `Chooses`: physical branching of state transitions
does not constrain internal cognitive representation.
-/
namespace ModelM2BranchingInitiation

def S : Type := Unit
def State : Type := Bool
def Means (_s : S) (p : Prop) : Prop := p
def Initiates (_s : S) (w w' : State) (p : Prop) : Prop :=
  (w = false ∧ w' = true ∧ p) ∨ (w = false ∧ w' = false ∧ ¬ p)

def Act (s : S) (p : Prop) : Prop := Means s p ∧ ∃ w w' : State, Initiates s w w' p
def ChoiceField (s : S) (p q : Prop) : Prop := Act s p ∧ Logos.Alternatives.Incompatible p q
def Chooses (s : S) (p q : Prop) : Prop := Means s p ∧ Means s q ∧ Logos.Alternatives.Incompatible p q
def FreeWill (s : S) : Prop := ∃ p q : Prop, Chooses s p q
def FreeSubject (s : S) : Prop := FreeWill s

/-- Strong Act holds in M2. -/
theorem strong_act_holds : ∃ s : S, ∃ p : Prop, Act s p :=
  ⟨(), True, trivial, false, true, Or.inl ⟨rfl, rfl, trivial⟩⟩

/-- Initiation relation branches non-trivially across states in M2. -/
theorem initiation_branches :
    ∃ s : S, Logos.Initiation.Branches (fun w w' => ∃ p : Prop, Initiates s w w' p) :=
  ⟨(), false, true, false, ⟨True, Or.inl ⟨rfl, rfl, trivial⟩⟩, ⟨False, Or.inr ⟨rfl, rfl, fun h => h⟩⟩, Bool.noConfusion⟩

/-- ChoiceField holds in M2: the agent acts against an incompatible alternative. -/
theorem choice_field_holds : ∃ s : S, ∃ p q : Prop, ChoiceField s p q :=
  ⟨(), True, False, ⟨trivial, false, true, Or.inl ⟨rfl, rfl, trivial⟩⟩, fun h => h.2⟩

/-- Genuine choice fails completely in M2: veridical meaning prevents co-meaning incompatible alternatives. -/
theorem no_chooses : ¬ ∃ s : S, ∃ p q : Prop, Chooses s p q := by
  rintro ⟨_, p, q, hp, hq, hIncomp⟩
  exact hIncomp ⟨hp, hq⟩

/-- Free will fails in M2. -/
theorem no_free_will : ¬ ∃ s : S, FreeWill s := by
  rintro ⟨s, p, q, hChooses⟩
  exact no_chooses ⟨s, p, q, hChooses⟩

/-- Free subject fails in M2. -/
theorem no_free_subject : ¬ ∃ s : S, FreeSubject s :=
  no_free_will

/-- Diagnostic separation for Model M2:
    Strong Act occurs and initiation branches in state space, ChoiceField holds,
    yet Chooses and FreeWill remain empty. -/
theorem m2_diagnostic_separation :
    (∃ s : S, ∃ p : Prop, Act s p) ∧
    (∃ s : S, Logos.Initiation.Branches (fun w w' => ∃ p, Initiates s w w' p)) ∧
    (∃ s : S, ∃ p q : Prop, ChoiceField s p q) ∧
    ¬ (∃ s : S, ∃ p q : Prop, Chooses s p q) ∧
    ¬ (∃ s : S, FreeWill s) ∧
    ¬ (∃ s : S, FreeSubject s) :=
  ⟨strong_act_holds, initiation_branches, choice_field_holds, no_chooses, no_free_will, no_free_subject⟩

end ModelM2BranchingInitiation

/-
### Model M3: Contrastive Semantic Agency (AxActPolarity Validated)
Demonstrates where Strong Choice, FreeWill, and FreeSubject first become valid:
when initiating an intentional act constitutively endows the agent with
representation of the incompatible alternative.
-/
namespace ModelM3ContrastiveAgency

def S : Type := Unit
def State : Type := Unit
def Means (_s : S) (_p : Prop) : Prop := True
def Initiates (_s : S) (_w _w' : State) (_p : Prop) : Prop := True

def Act (s : S) (p : Prop) : Prop := Means s p ∧ ∃ w w' : State, Initiates s w w' p
def ChoiceField (s : S) (p q : Prop) : Prop := Act s p ∧ Logos.Alternatives.Incompatible p q
def Chooses (s : S) (p q : Prop) : Prop := Means s p ∧ Means s q ∧ Logos.Alternatives.Incompatible p q
def FreeWill (s : S) : Prop := ∃ p q : Prop, Chooses s p q
def FreeSubject (s : S) : Prop := FreeWill s

theorem act_holds : ∃ s : S, ∃ p : Prop, Act s p :=
  ⟨(), True, trivial, (), (), trivial⟩

theorem choice_field_holds : ∃ s : S, ∃ p q : Prop, ChoiceField s p q :=
  ⟨(), True, False, ⟨trivial, (), (), trivial⟩, fun h => h.2⟩

/-- Strong Choice becomes valid in M3. -/
theorem chooses_holds : ∃ s : S, ∃ p q : Prop, Chooses s p q :=
  ⟨(), True, False, trivial, trivial, fun h => h.2⟩

/-- FreeWill becomes valid in M3. -/
theorem free_will_holds : ∃ s : S, FreeWill s :=
  ⟨(), True, False, trivial, trivial, fun h => h.2⟩

/-- FreeSubject becomes valid in M3. -/
theorem free_subject_holds : ∃ s : S, FreeSubject s :=
  free_will_holds

/-- Diagnostic fulfillment for Model M3:
    Act, ChoiceField, Chooses, FreeWill, and FreeSubject all hold simultaneously. -/
theorem m3_diagnostic_fulfillment :
    (∃ s : S, ∃ p : Prop, Act s p) ∧
    (∃ s : S, ∃ p q : Prop, ChoiceField s p q) ∧
    (∃ s : S, ∃ p q : Prop, Chooses s p q) ∧
    (∃ s : S, FreeWill s) ∧
    (∃ s : S, FreeSubject s) :=
  ⟨act_holds, choice_field_holds, chooses_holds, free_will_holds, free_subject_holds⟩

end ModelM3ContrastiveAgency

/-
### Separation Model: Contrastive Agency vs. Act Polarity
Demonstrates that contrastive agency (meaning an incompatible alternative q)
is conceptually and intensionally strictly weaker than Act Polarity (meaning the formal negation ¬p).
An agent can choose between two incompatible courses of action (e.g. North vs. East)
without possessing or entertaining the logical operator of contradictory negation ¬P.
-/
namespace ContrastiveSeparation

inductive Form3 : Type
  | North : Form3
  | East : Form3
  | NotNorth : Form3

def Incompatible3 (p q : Form3) : Prop :=
  match p, q with
  | Form3.North, Form3.East => True
  | Form3.East, Form3.North => True
  | Form3.North, Form3.NotNorth => True
  | Form3.NotNorth, Form3.North => True
  | _, _ => False

def S : Type := Unit
def State : Type := Unit

-- The agent means North and means East, but does not represent NotNorth.
def Means (_s : S) : Form3 → Prop
  | Form3.North => True
  | Form3.East => True
  | Form3.NotNorth => False

def Initiates (_s : S) (_w _w' : State) : Form3 → Prop
  | Form3.North => True
  | _ => False

def Act (s : S) (p : Form3) : Prop := Means s p ∧ ∃ w w' : State, Initiates s w w' p

/-- Contrastive agency holds: when acting on North, the agent means an incompatible alternative (East). -/
theorem contrastive_holds : ∀ (s : S) (p : Form3), Act s p → ∃ q : Form3, Means s q ∧ Incompatible3 p q := by
  intro s p ha
  cases p with
  | North => exact ⟨Form3.East, trivial, trivial⟩
  | East =>
    obtain ⟨_w, _w', hInit⟩ := ha.2
    exact False.elim hInit
  | NotNorth => exact False.elim ha.1

/-- But act polarity specifically requiring representation of contradictory negation (NotNorth) fails. -/
theorem negation_meaning_fails : ¬ Means () Form3.NotNorth := fun h => h

theorem contrastive_strictly_weaker :
    (∀ (s : S) (p : Form3), Act s p → ∃ q : Form3, Means s q ∧ Incompatible3 p q) ∧
    ¬ Means () Form3.NotNorth :=
  ⟨contrastive_holds, negation_meaning_fails⟩

end ContrastiveSeparation

end ModelHierarchy

/- Separation model demonstrating that ActPolarity is strictly weaker than universal bilateral intentionality:
    active agency can be constitutively polar while non-active meaning remains unilateral. -/
namespace ActPolaritySeparation

inductive S : Type
  | active : S
  | passive : S

def Act : S → Prop → Prop
  | S.active, _ => True
  | S.passive, _ => False

def Means : S → Prop → Prop
  | S.active, _ => True   -- active subject has polar meaning
  | S.passive, p => p     -- passive subject has unilateral/veridical meaning

/-- Act polarity holds: whenever an act occurs, the subject means its negation. -/
theorem act_polarity_holds : ∀ (s : S) (p : Prop), Act s p → Means s (¬ p) := by
  intro s p ha
  cases s with
  | active => trivial
  | passive => cases ha

/-- Universal bilateral intentionality fails: the passive subject means True without meaning ¬True. -/
theorem universal_bilateral_fails : ¬ (∀ (s : S) (p : Prop), Means s p → Means s (¬ p)) := by
  intro h
  have hF : Means S.passive (¬ True) := h S.passive True trivial
  exact hF trivial

/-- Formal separation: Act polarity does NOT entail universal bilateral intentionality.
    Proves that AxActPolarity is strictly weaker than AxBilateralIntentionality. -/
theorem act_polarity_strictly_weaker :
    (∀ (s : S) (p : Prop), Act s p → Means s (¬ p)) ∧
    ¬ (∀ (s : S) (p : Prop), Means s p → Means s (¬ p)) :=
  ⟨act_polarity_holds, universal_bilateral_fails⟩

end ActPolaritySeparation

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
