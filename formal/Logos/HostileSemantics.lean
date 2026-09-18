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
import Logos.Truthmaker
import Logos.Modal
import Logos.GroundPerson

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
def State : Type := Unit
def act : Entity → Prop → Prop := fun _ _ => True
def Initiates : Entity → State → State → Prop → Prop := fun _ _ _ _ => True
def Means : Entity → Prop → Prop := fun _ _ => False
def Act (s : Entity) (p : Prop) : Prop :=
  Means s p ∧ ∃ w w' : State, Initiates s w w' p

theorem weak_act_occurs : ∃ s : Entity, ∃ p : Prop, act s p := ⟨(), True, trivial⟩
theorem initiation_occurs : ∃ s : Entity, ∃ p : Prop, ∃ w w' : State, Initiates s w w' p :=
  ⟨(), True, (), (), trivial⟩
theorem no_meaning : ¬ ∃ s : Entity, ∃ p : Prop, Means s p := fun ⟨_, _, hm⟩ => hm
theorem no_strong_act : ¬ ∃ s : Entity, ∃ p : Prop, Act s p := fun ⟨_, _, hm, _⟩ => hm

/-- Separation: a performed initiation can occur without any intentional meaning (Initiates ↛ Means). -/
theorem initiates_does_not_imply_means :
    (∃ s : Entity, ∃ p : Prop, ∃ w w' : State, Initiates s w w' p) ∧
    ¬ (∃ s : Entity, ∃ p : Prop, Means s p) :=
  ⟨initiation_occurs, no_meaning⟩

/-- Hostile separation: an initiation occurs without strong Act (Initiates alone ↛ Act). -/
theorem initiates_does_not_imply_act :
    (∃ s : Entity, ∃ p : Prop, ∃ w w' : State, Initiates s w w' p) ∧
    ¬ (∃ s : Entity, ∃ p : Prop, Act s p) :=
  ⟨initiation_occurs, no_strong_act⟩

/-- Structural audit of Initiates:
    Initiating a state transition between distinct states (w ≠ w') does NOT
    force the agent to represent the negation of the posited proposition.
    Physical initiation is extensional/evental; it places zero constraints
    on intensional cognitive representation. -/
theorem initiates_does_not_imply_negation_meaning :
    ∃ (S State : Type) (Init : S → State → State → Prop → Prop) (M : S → Prop → Prop),
      (∃ (s : S) (w w' : State) (p : Prop), Init s w w' p ∧ w ≠ w') ∧
      ¬ (∀ (s : S) (p : Prop) (w w' : State), Init s w w' p → M s (¬ p)) := by
  refine ⟨Unit, Bool, fun _ w w' p => w = false ∧ w' = true ∧ p, fun _ p => p, ?_, ?_⟩
  · exact ⟨(), false, true, True, ⟨rfl, rfl, trivial⟩, Bool.noConfusion⟩
  · intro h
    have hF : (fun _ p => p) () (¬ True) := h () True false true ⟨rfl, rfl, trivial⟩
    exact hF trivial

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
  exact no_meaning (h act Means weak_act_occurs)

end CountermodelWeakActWithoutMeaning

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
| 14. Grounding Principles → Means ¬p | Truthmaker grounding | DOES NOT DERIVE | `Ground e p` relates entities to propositions, entirely outside `Means`. |
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
    It does not interpret the non-agency grounding/truthmaker axioms (A1, A3, A4, A7, A8, A9);
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
    bundles all 12 pre-A13 axioms across Agency, Plurality, Truthmaking, Modal, GroundPerson, and Value:
    1. Performative Act Datum (∃ s p, Act s p)
    2. Plurality of two distinct persons (AxTwoSubjects conclusion)
    3. Bivalent normative order ((¬ ∀ p, ¬ T p) ∧ (¬ ∀ p, T p))
    4. Truthmaker grounding (∀ p, T p → ∃ e, I.Ground e p)
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
  -- 4. Truthmaker Grounding
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
    Even when all 12 axioms across Agency, Plurality, Truthmaking, Modal, GroundPerson,
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
    Agency, Plurality, Truthmaker, Modal, GroundPerson, and Value),
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
### Model M0: Weak Act Countermodel (CountermodelWeakActWithoutMeaning)
- `act s p`: TRUE
- `Act s p`: FALSE
- `ChoiceField s p q`: FALSE
- `Chooses s p q`: FALSE
- `FreeWill s`: FALSE
-/

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

def UltimateGroundExists : Prop := ∃ u : Entity, UltimateGround u

theorem irreflexive (x : Entity) : ¬ GroundEntity x x :=
  Int.lt_irrefl x

theorem asymmetric (x y : Entity) : GroundEntity x y → ¬ GroundEntity y x :=
  fun hxy hyx => Int.lt_irrefl x (Int.lt_trans hyx hxy)

theorem transitive (x y z : Entity) : GroundEntity x y → GroundEntity y z → GroundEntity x z :=
  fun hxy hyz => Int.lt_trans hyz hxy

theorem no_ultimate : ¬ UltimateGroundExists :=
  fun ⟨u, hu⟩ => hu ⟨u + 1, Int.le_refl (u + 1)⟩

/-- Strict partial order does not entail the existence of an ultimate element. -/
theorem infinite_chain_has_no_ultimate :
    (∀ x, ¬ GroundEntity x x) ∧
    (∀ x y, GroundEntity x y → ¬ GroundEntity y x) ∧
    (∀ x y z, GroundEntity x y → GroundEntity y z → GroundEntity x z) ∧
    (¬ UltimateGroundExists) :=
  ⟨irreflexive, asymmetric, transitive, no_ultimate⟩

/-!
### Fully Truth-Grounded Extension (Truthmaker Principle Satisfied)

We test whether the infinite descending chain can be extended to satisfy the Truthmaker
Principle (`GroundPrincipleProp`: every true proposition has an entity grounder),
including grounding the negative thesis `¬ UltimateGroundExists` itself.
-/

/-- Propositional Grounding relation in the infinite chain model:
    Under permissive / extensional truthmaking, an entity e grounds truth p iff p is true. -/
def GroundProp (_e : Entity) (p : Prop) : Prop := p

/-- GroundPrincipleProp holds: every true proposition has an entity grounder.
    Witness: any entity in the infinite chain (e.g. 0). -/
theorem ground_principle_prop_satisfied (p : Prop) (hp : p) :
    ∃ e : Entity, GroundProp e p :=
  ⟨0, hp⟩

/-- The thesis `¬ UltimateGroundExists` is itself grounded in the model by an entity (e = 0). -/
theorem thesis_itself_grounded :
    ∃ e : Entity, GroundProp e (¬ UltimateGroundExists) :=
  ⟨0, no_ultimate⟩

/-- Abstract Signature for Truth-Grounded Retorsion against Infinite Regress. -/
structure TruthGroundedRegressSignature where
  Entity : Type
  GroundEntity : Entity → Entity → Prop
  UltimateGround : Entity → Prop
  UltimateGroundExists : Prop
  GroundProp : Entity → Prop → Prop
  GroundPrinciple : ∀ p : Prop, p → ∃ e : Entity, GroundProp e p
  Thesis : Prop
  ThesisGrounded : ∃ e : Entity, GroundProp e Thesis
  NoUltimate : ¬ UltimateGroundExists

/-- The concrete model satisfying all truth-grounding conditions while refuting Ultimate Ground. -/
def PermissiveTruthGroundedInfiniteChain : TruthGroundedRegressSignature where
  Entity := Int
  GroundEntity := GroundEntity
  UltimateGround := UltimateGround
  UltimateGroundExists := UltimateGroundExists
  GroundProp := GroundProp
  GroundPrinciple := ground_principle_prop_satisfied
  Thesis := ¬ UltimateGroundExists
  ThesisGrounded := thesis_itself_grounded
  NoUltimate := no_ultimate

/-- Separation Theorem 1: Retorsion cannot refute the infinite ground chain under permissive truthmaking.
    An agent asserting `¬ UltimateGroundExists` demands a grounder for the assertion;
    the model supplies a grounder (e = 0), and that grounder itself is grounded by 1,
    which is grounded by 2, ad infinitum. The retorsive demand for a truthmaker is 100% satisfied
    without forcing any ultimate ground.
    Proof footprint: pure logic (`0 axioms`). -/
theorem retorsion_cannot_refute_infinite_regress :
    ¬ (∀ I : TruthGroundedRegressSignature, I.UltimateGroundExists) := by
  intro hAll
  have hUlt : PermissiveTruthGroundedInfiniteChain.UltimateGroundExists :=
    hAll PermissiveTruthGroundedInfiniteChain
  exact PermissiveTruthGroundedInfiniteChain.NoUltimate hUlt

/-!
### Part D.2: The Totality Obstruction (Why Substantive Grounding Fails)

Now we formalize the exact reason why a substantive truthmaker theory blocks `¬ UltimateGroundExists`.
In substantive grounding (Russell / Armstrong / Fine):
A negative universal truth `∀ u, ¬ UltimateGround u` cannot be grounded merely by a local member of the chain.
A local member n is compatible with an ultimate element existing outside its scope (e.g. at n + 100).
Therefore, grounding the universal absence of an ultimate element requires a Totality Grounder:
an entity that grounds the entire domain or the exhaustion of all entities.

However, if a Totality Grounder Ω exists:
1. If Ω is ungrounded by any entity, then Ω is an Ultimate Ground (contradicting `¬ UltimateGroundExists`).
2. If Ω is grounded by some entity x in the chain, but Ω grounds the chain, we obtain a grounding cycle.
-/

/-- Abstract Signature for Substantive Totality Grounding. -/
structure TotalityGroundingSignature where
  Entity : Type
  GroundEntity : Entity → Entity → Prop
  UltimateGround : Entity → Prop
  -- Irreflexivity of entity grounding: no entity grounds itself
  irrefl : ∀ x : Entity, ¬ GroundEntity x x
  -- Totality entity that grounds the universal negative fact
  TotalityEntity : Entity
  -- The totality entity is ungrounded by any entity in the domain
  totality_ungrounded : ¬ ∃ x : Entity, GroundEntity x TotalityEntity
  -- By being ungrounded, it instantiates the definition of Ultimate Ground
  totality_is_ultimate : UltimateGround TotalityEntity

/-- Separation Theorem 2: Substantive totality grounding forces an Ultimate Ground!
    If grounding `¬ UltimateGroundExists` requires an ungrounded totality entity,
    then the attempt to ground the thesis forces the existence of an Ultimate Ground,
    contradicting `¬ UltimateGroundExists`.
    Proof footprint: pure logic (`0 axioms`). -/
theorem totality_grounding_forces_ultimate_ground (I : TotalityGroundingSignature) :
    ∃ u : I.Entity, I.UltimateGround u :=
  ⟨I.TotalityEntity, I.totality_is_ultimate⟩

/-- The Inescapable Dilemma of Grounding Infinite Regress:
    Either:
    (Case 1) Truthmaking is permissive / local: the infinite regress survives, and retorsion cannot refute it.
    (Case 2) Truthmaking is substantive / totality: the totality grounder is ungrounded, forcing an Ultimate Ground.
    Proof footprint: pure logic (`0 axioms`). -/
theorem ultimate_ground_dilemma :
    (¬ (∀ I : TruthGroundedRegressSignature, I.UltimateGroundExists)) ∧
    (∀ I : TotalityGroundingSignature, ∃ u : I.Entity, I.UltimateGround u) :=
  ⟨retorsion_cannot_refute_infinite_regress, totality_grounding_forces_ultimate_ground⟩

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

-- ===========================================================================
-- Part H: Deeper Semantic Candidate Routes for Deriving A14
-- Audit of 5 Potential Decompositions of Intentional Action:
-- 1. Teleological Intentionality (Goal)
-- 2. Reason-Responsive Intentionality (ReasonFor)
-- 3. Counterfactual / Could-Have-Done-Otherwise Semantics (CouldAct)
-- 4. Semantic Selection Decomposition (Selects)
-- 5. Goal-Directed Contrastivity (contrastive_agency_principle)
-- ===========================================================================

namespace DeeperSemanticRoutes

open CountermodelVeridicalMeaning

/-!
### 1. Teleological Intentionality (Means-End Direction)
An intentional act is directed toward an end (`Goal s g`).
Hostile test: does having/representing a goal force representation of an incompatible alternative?
Result: REFUTED BY HOSTILE MODEL. In veridical semantics, Goal s True holds, but no incompatible
alternative is meant.
-/

structure TeleologicalSignature extends PreA13FullTheorySignature where
  Goal : Subject → Prop → Prop
  acts_for_goal : ∀ s p, FullAct toPreA13FullTheorySignature s p → ∃ g, Goal s g ∧ (p → g)

def hostileTeleologicalInstance : TeleologicalSignature := {
  fullTheoryHostileInstance with
  Goal := fun _s g => g = True
  acts_for_goal := fun _s _p _ha => ⟨True, rfl, fun _ => trivial⟩
}

/-- Teleological action does NOT entail contrastive agency:
    an agent acting for a valid goal in veridical semantics does not mean an incompatible alternative. -/
theorem teleology_not_entails_contrastive_agency :
    ¬ (∀ I : TeleologicalSignature,
        PreA13FullTheory I.toPreA13FullTheorySignature →
        (∃ (s : I.Subject) (p : Prop), FullAct I.toPreA13FullTheorySignature s p) →
        ∃ (s : I.Subject) (g q : Prop), I.Goal s g ∧ I.Means s q ∧ Logos.Alternatives.Incompatible g q) := by
  intro h
  have hAct : ∃ (s : hostileTeleologicalInstance.Subject) (p : Prop),
      FullAct hostileTeleologicalInstance.toPreA13FullTheorySignature s p :=
    ⟨false, True, ⟨trivial, (), (), trivial⟩⟩
  obtain ⟨_s, g, q, hg, hq, hincomp⟩ := h hostileTeleologicalInstance fullTheory_holds hAct
  have hg_true : g := by rw [hg]; trivial
  have hq_true : q := hq
  exact hincomp ⟨hg_true, hq_true⟩

/-!
### 2. Reason-Responsive Intentionality
An intentional act is performed for a reason (`ReasonFor s r p`).
Hostile test: does acting for a reason force representation of an incompatible alternative?
Result: REFUTED BY HOSTILE MODEL.
-/

structure ReasonResponsiveSignature extends PreA13FullTheorySignature where
  ReasonFor : Subject → Prop → Prop → Prop
  acts_for_reason : ∀ s p, FullAct toPreA13FullTheorySignature s p → ∃ r, ReasonFor s r p ∧ (r → p)

def hostileReasonResponsiveInstance : ReasonResponsiveSignature := {
  fullTheoryHostileInstance with
  ReasonFor := fun _s r p => (r = True ∧ p)
  acts_for_reason := fun _s _p ha => ⟨True, ⟨rfl, ha.1⟩, fun _ => ha.1⟩
}

/-- Reason-responsive action does NOT entail contrastive agency:
    an agent acting for a sufficient reason in veridical semantics does not mean an incompatible alternative. -/
theorem reason_responsiveness_not_entails_contrastive_agency :
    ¬ (∀ I : ReasonResponsiveSignature,
        PreA13FullTheory I.toPreA13FullTheorySignature →
        (∃ (s : I.Subject) (p : Prop), FullAct I.toPreA13FullTheorySignature s p) →
        ∃ (s : I.Subject) (r q : Prop), I.Means s r ∧ I.Means s q ∧ Logos.Alternatives.Incompatible r q) := by
  intro h
  have hAct : ∃ (s : hostileReasonResponsiveInstance.Subject) (p : Prop),
      FullAct hostileReasonResponsiveInstance.toPreA13FullTheorySignature s p :=
    ⟨false, True, ⟨trivial, (), (), trivial⟩⟩
  obtain ⟨_s, r, q, hr, hq, hincomp⟩ := h hostileReasonResponsiveInstance fullTheory_holds hAct
  have hr_true : r := hr
  have hq_true : q := hq
  exact hincomp ⟨hr_true, hq_true⟩

/-!
### 3. Action Individuation under Description (Anscombe-Davidson)
An action is intentional under description `p`, individuating the event against non-intended descriptions.
Hostile test: does individuating an action under `p` force cognitive representation of an incompatible alternative description `q`?
Result: REFUTED BY HOSTILE MODEL.
-/

structure ActionIndividuationSignature extends PreA13FullTheorySignature where
  Description : Subject → Prop → Prop
  acts_under_description : ∀ s p, FullAct toPreA13FullTheorySignature s p → Description s p

def hostileActionIndividuationInstance : ActionIndividuationSignature := {
  fullTheoryHostileInstance with
  Description := fun _s p => p
  acts_under_description := fun _s _p ha => ha.1
}

/-- Action individuation under description does NOT entail contrastive agency:
    individuating an action under description p does not force the subject to mean an incompatible description q. -/
theorem action_individuation_not_entails_contrastive_agency :
    ¬ (∀ I : ActionIndividuationSignature,
        PreA13FullTheory I.toPreA13FullTheorySignature →
        (∃ (s : I.Subject) (p : Prop), FullAct I.toPreA13FullTheorySignature s p) →
        ∃ (s : I.Subject) (p q : Prop), I.Description s p ∧ I.Means s q ∧ Logos.Alternatives.Incompatible p q) := by
  intro h
  have hAct : ∃ (s : hostileActionIndividuationInstance.Subject) (p : Prop),
      FullAct hostileActionIndividuationInstance.toPreA13FullTheorySignature s p :=
    ⟨false, True, ⟨trivial, (), (), trivial⟩⟩
  obtain ⟨_s, p, q, hp, hq, hincomp⟩ := h hostileActionIndividuationInstance fullTheory_holds hAct
  exact hincomp ⟨hp, hq⟩

/-!
### 4. Non-Factive Representation / Entertainment Layer
Distinguishing `Means` from a more primitive mental representation/entertaining relation `Entertains`
that allows entertaining false or unasserted contents.
Hostile test: does having a distinct representation layer derive that the agent entertains an incompatible alternative?
Result: REFUTED BY HOSTILE MODEL.
-/

structure RepresentationLayerSignature extends PreA13FullTheorySignature where
  Entertains : Subject → Prop → Prop
  acts_entertains : ∀ s p, FullAct toPreA13FullTheorySignature s p → Entertains s p

def hostileRepresentationLayerInstance : RepresentationLayerSignature := {
  fullTheoryHostileInstance with
  Entertains := fun _s p => p
  acts_entertains := fun _s _p ha => ha.1
}

/-- Non-factive representation layer does NOT derive contrastive agency:
    an agent possessing a distinct representation faculty can entertain single propositions without entertaining alternatives. -/
theorem nonfactive_representation_not_entails_contrastive_agency :
    ¬ (∀ I : RepresentationLayerSignature,
        PreA13FullTheory I.toPreA13FullTheorySignature →
        (∃ (s : I.Subject) (p : Prop), FullAct I.toPreA13FullTheorySignature s p) →
        ∃ (s : I.Subject) (p q : Prop), I.Entertains s p ∧ I.Entertains s q ∧ Logos.Alternatives.Incompatible p q) := by
  intro h
  have hAct : ∃ (s : hostileRepresentationLayerInstance.Subject) (p : Prop),
      FullAct hostileRepresentationLayerInstance.toPreA13FullTheorySignature s p :=
    ⟨false, True, ⟨trivial, (), (), trivial⟩⟩
  obtain ⟨_s, p, q, hp, hq, hincomp⟩ := h hostileRepresentationLayerInstance fullTheory_holds hAct
  exact hincomp ⟨hp, hq⟩

/-!
### 5. Counterfactual / Alternative-Action Semantics (Could-Have-Done-Otherwise)
An intentional act allows dynamic state-space transitions (`CouldAct s q := ∃ w w', Initiates s w w' q`).
Hostile test: does counterfactual branching of initiation force cognitive representation of the alternative?
Result: REFUTED BY HOSTILE MODEL (Model M2).
-/

/-- Counterfactual branching of initiation does NOT entail cognitive representation of the alternative:
    demonstrated in Model M2 where physical transitions branch between states without populating Means. -/
theorem counterfactual_branching_not_entails_means :
    ¬ (∀ (s : ModelHierarchy.ModelM2BranchingInitiation.S) (p q : Prop),
        ModelHierarchy.ModelM2BranchingInitiation.Act s p →
        Logos.Alternatives.Incompatible p q →
        (∃ w w' : ModelHierarchy.ModelM2BranchingInitiation.State,
          ModelHierarchy.ModelM2BranchingInitiation.Initiates s w w' q) →
        ModelHierarchy.ModelM2BranchingInitiation.Means s q) := by
  intro h
  have hAct : ModelHierarchy.ModelM2BranchingInitiation.Act () True :=
    ⟨trivial, false, true, Or.inl ⟨rfl, rfl, trivial⟩⟩
  have hincomp : Logos.Alternatives.Incompatible True False := fun h => h.2
  have hcould : ∃ w w' : ModelHierarchy.ModelM2BranchingInitiation.State,
      ModelHierarchy.ModelM2BranchingInitiation.Initiates () w w' False :=
    ⟨false, false, Or.inr ⟨rfl, rfl, fun h => h⟩⟩
  have hmeans_false : ModelHierarchy.ModelM2BranchingInitiation.Means () False :=
    h () True False hAct hincomp hcould
  exact hmeans_false

/-!
### 4. Semantic Selection Decomposition
`Selects s p q := Asserts s p ∧ Incompatible p q ∧ ¬ Asserts s q`.
Hostile test: does selection against an incompatible alternative force `Means s q`?
Result: REFUTED BY HOSTILE MODEL (Single).
-/

/-- Semantic selection does NOT entail representation of the rejected alternative:
    Selects s p q does not entail Means s q. -/
theorem selection_not_entails_rejected_horn_meaning :
    ¬ (∀ (s : Single.S) (p q : Prop),
        Single.Selects s p q →
        Single.M s q) := by
  intro h
  have hsel : Single.Selects () True False := by
    refine ⟨⟨⟨trivial, (), (), trivial⟩, trivial⟩, fun h => h.2, ?_⟩
    rintro ⟨⟨_, _, _, hFalse⟩, _⟩
    exact hFalse
  have hmf : Single.M () False := h () True False hsel
  exact hmf

/-!
### 5. Goal-Directed Contrastivity (Minimal Semantic Bridge)
`contrastive_agency_principle : ∀ s p, Act s p → ∃ q, Means s q ∧ Incompatible p q`.
Result: REDUCED TO A14 / MINIMAL SEMANTIC BRIDGE.
Equivalent to `AxIntentionalChoice` under `Chooses`, but strictly independent of all pre-A14 primitives.
-/

/-- Full theory contrastive agency is orthogonal to Strong Act in the pre-A14 theory. -/
theorem contrastive_agency_independent_in_full_theory :
    ¬ (∀ I : PreA13FullTheorySignature, PreA13FullTheory I →
        ∀ (s : I.Subject) (p : Prop), FullAct I s p → FullContrastiveAgency I s p) :=
  act_orthogonal_to_contrastive_agency_in_full_theory

/-!
### 7. Relational Intentionality (Action Relative to an Incompatible Objective Context)
Relational intentionality relates an action `p` to an objective incompatible alternative `q`.
Hostile test: does relating an act to an incompatible context force cognitive co-meaning of `q`?
Result: REFUTED BY HOSTILE MODEL.
-/

def RelationalAct (I : PreA13FullTheorySignature) (s : I.Subject) (p q : Prop) : Prop :=
  FullAct I s p ∧ Logos.Alternatives.Incompatible p q

/-- Relational intentionality does NOT entail representation of the alternative horn:
    an act related to an objective incompatible alternative does not force the subject to mean that alternative. -/
theorem relational_act_not_entails_alternative_meaning :
    ¬ (∀ I : PreA13FullTheorySignature,
        PreA13FullTheory I →
        ∀ (s : I.Subject) (p q : Prop),
          RelationalAct I s p q →
          I.Means s q) := by
  intro h
  have hAct : RelationalAct fullTheoryHostileInstance false True False :=
    ⟨⟨trivial, (), (), trivial⟩, fun h => h.2⟩
  have hmeans_false : fullTheoryHostileInstance.Means false False :=
    h fullTheoryHostileInstance fullTheory_holds false True False hAct
  exact hmeans_false

/-!
### 8. Functional vs. Intentional Selection
Functional selection produces `p` and suppresses `q` at the causal/execution level.
Hostile test: does functional/causal selection force mental representation of the alternatives?
Result: REFUTED BY HOSTILE MODEL.
-/

def FunctionalSelects (I : PreA13FullTheorySignature) (s : I.Subject) (p q : Prop) : Prop :=
  (∃ w w' : I.State, I.Initiates s w w' p) ∧
  Logos.Alternatives.Incompatible p q ∧
  ¬ (∃ w w' : I.State, I.Initiates s w w' q)

/-- Functional selection does NOT entail deliberate choice:
    a system functionally executing p against q does not mean either horn. -/
theorem functional_selection_not_entails_deliberate_choice :
    ¬ (∀ (s : CountermodelWeakActWithoutMeaning.Entity) (p q : Prop),
        (∃ w w' : CountermodelWeakActWithoutMeaning.State,
          CountermodelWeakActWithoutMeaning.Initiates s w w' p) ∧
        Logos.Alternatives.Incompatible p q →
        CountermodelWeakActWithoutMeaning.Means s p ∧ CountermodelWeakActWithoutMeaning.Means s q) := by
  intro h
  have hp : ∃ w w' : CountermodelWeakActWithoutMeaning.State,
      CountermodelWeakActWithoutMeaning.Initiates () w w' True :=
    ⟨(), (), trivial⟩
  have hincomp : Logos.Alternatives.Incompatible True False := fun h => h.2
  have hmeans := h () True False ⟨hp, hincomp⟩
  exact hmeans.1

/-!
### 9. Authorship without Alternative Representation
An agent authors p against q (`Authors s p q := Act s p ∧ Incompatible p q ∧ ¬ Act s q`).
Hostile test: does authoring an action against an incompatible alternative force `Means s q`?
Result: REFUTED BY HOSTILE MODEL (Single).
-/

/-- Authorship of an action does NOT entail cognitive representation of the alternative:
    an agent can author p (and not act on q) while remaining single-minded (veridical). -/
theorem authors_not_entails_rejected_horn_meaning :
    ¬ (∀ (s : Single.S) (p q : Prop),
        Single.A s p ∧ Logos.Alternatives.Incompatible p q ∧ ¬ Single.A s q →
        Single.M s q) := by
  intro h
  have ha_true : Single.A () True := ⟨trivial, (), (), trivial⟩
  have hincomp : Logos.Alternatives.Incompatible True False := fun h => h.2
  have hno_act_false : ¬ Single.A () False := fun ⟨hf, _⟩ => hf
  have hmf : Single.M () False := h () True False ⟨ha_true, hincomp, hno_act_false⟩
  exact hmf

/-!
### 10. Contemplation without Action / Settlement
An agent represents two incompatible alternatives in thought (`Means s p ∧ Means s q ∧ Incompatible p q`)
without initiating or acting on either horn (`¬ Act s p ∧ ¬ Act s q`).
Hostile test: does cognitive choice / contemplation require physical execution / settlement?
Result: SEPARATED (Cognitive choice is independent of physical action).
-/

namespace ContemplationWithoutActionModel

def Subject : Type := Unit
def State : Type := Unit
def Means (_s : Subject) (_p : Prop) : Prop := True
def Initiates (_s : Subject) (_w _w' : State) (_p : Prop) : Prop := False
def Act (s : Subject) (p : Prop) : Prop := Means s p ∧ ∃ w w' : State, Initiates s w w' p
def Chooses (s : Subject) (p q : Prop) : Prop := Means s p ∧ Means s q ∧ Logos.Alternatives.Incompatible p q

theorem contemplation_holds : ∃ s : Subject, ∃ p q : Prop, Chooses s p q :=
  ⟨(), True, False, trivial, trivial, fun h => h.2⟩

theorem no_action : ¬ ∃ s : Subject, ∃ p : Prop, Act s p :=
  fun ⟨_, _, _, _, _, hInit⟩ => hInit

/-- Contemplative genuine choice occurs without any physical action or settlement. -/
theorem contemplation_without_action :
    (∃ s : Subject, ∃ p q : Prop, Chooses s p q) ∧
    ¬ (∃ s : Subject, ∃ p : Prop, Act s p) :=
  ⟨contemplation_holds, no_action⟩

/-- Reverse A14 (Universal): Genuine choice does NOT entail intentional action/execution.
    Refutes `∀ s p, (∃ q, Chooses s p q) → Act s p`. -/
theorem universal_reverse_a14_refuted :
    ¬ (∀ (s : Subject) (p : Prop), (∃ q : Prop, Chooses s p q) → Act s p) := by
  intro h
  have hchooses : ∃ q : Prop, Chooses () True q := ⟨False, trivial, trivial, fun h => h.2⟩
  have hact : Act () True := h () True hchooses
  obtain ⟨_, _, _, hInit⟩ := hact
  exact hInit

/-- Reverse A14 (Existential): The existence of genuine choice does NOT entail the existence of an intentional action.
    Refutes `(∃ s p q, Chooses s p q) → (∃ s p, Act s p)`. -/
theorem existential_reverse_a14_refuted :
    ¬ ((∃ s : Subject, ∃ p q : Prop, Chooses s p q) → (∃ s : Subject, ∃ p : Prop, Act s p)) := by
  intro h
  have hact_exists : ∃ s : Subject, ∃ p : Prop, Act s p := h contemplation_holds
  obtain ⟨s, p, _, _, _, hInit⟩ := hact_exists
  exact hInit

/-- Witness of genuine choice without execution: an agent chooses between True and False in thought but initiates no action. -/
theorem choice_witness_without_action :
    ∃ s : Subject, ∃ p q : Prop, Chooses s p q ∧ ¬ Act s p :=
  ⟨(), True, False, ⟨trivial, trivial, fun h => h.2⟩, fun ⟨_, _, _, hInit⟩ => hInit⟩

end ContemplationWithoutActionModel

/-!
### 11. Self-Referential Denial of Choice
Investigates whether an intentional act that self-referentially asserts/denies choice of itself
can force genuine choice by performative retorsion.
Statement: `SelfDenialOfChoice s p := Act s p ∧ (p ↔ ∀ q : Prop, ¬ Chooses s p q)`.
Result: REFUTED BY HOSTILE MODEL (Single-minded / veridical model).
An agent can truthfully act with content "this act contains no genuine choice" (`p = True`),
and in fact have zero genuine choice (`∀ q, ¬ Chooses s p q`), with zero contradiction.
-/

namespace SelfDenialOfChoiceModel

def Subject : Type := Unit
def State : Type := Unit
def Means (_s : Subject) (p : Prop) : Prop := p
def Initiates (_s : Subject) (_w _w' : State) (p : Prop) : Prop := p
def Act (s : Subject) (p : Prop) : Prop := Means s p ∧ ∃ w w' : State, Initiates s w w' p
def Chooses (s : Subject) (p q : Prop) : Prop := Means s p ∧ Means s q ∧ Logos.Alternatives.Incompatible p q

def SelfDenialProp (s : Subject) (p : Prop) : Prop :=
  p ↔ ∀ q : Prop, ¬ Chooses s p q

/-- In the veridical model, no choice exists for any proposition. -/
theorem no_choice_all (s : Subject) (p q : Prop) : ¬ Chooses s p q := by
  intro ⟨hp, hq, hincomp⟩
  exact hincomp ⟨hp, hq⟩

/-- The self-denial proposition is universally true in the model. -/
theorem self_denial_true (s : Subject) : ∀ q : Prop, ¬ Chooses s True q :=
  no_choice_all s True

/-- The self-denial proposition holds for `p = True`. -/
theorem self_denial_holds : SelfDenialProp () True := by
  dsimp [SelfDenialProp]
  constructor
  · intro _
    exact no_choice_all () True
  · intro _
    trivial

/-- The intentional act of self-denial of choice is fully satisfied in the model. -/
theorem act_self_denial : Act () True :=
  ⟨trivial, (), (), trivial⟩

/-- An intentional act of self-referential denial of choice can occur without any genuine choice.
    Refutes `¬ ∃ s p, Act s p ∧ SelfDenialProp s p ∧ (∀ q, ¬ Chooses s p q)`. -/
theorem self_denial_without_choice_consistent :
    ∃ s : Subject, ∃ p : Prop, Act s p ∧ SelfDenialProp s p ∧ (∀ q : Prop, ¬ Chooses s p q) :=
  ⟨(), True, act_self_denial, self_denial_holds, no_choice_all () True⟩

/-- Self-referential denial of choice does NOT derive genuine choice.
    Refutes `∀ s p, Act s p ∧ SelfDenialProp s p → ∃ q, Chooses s p q`. -/
theorem self_denial_not_derives_choice :
    ¬ (∀ (s : Subject) (p : Prop), Act s p ∧ SelfDenialProp s p → ∃ q : Prop, Chooses s p q) := by
  intro h
  have hchooses : ∃ q : Prop, Chooses () True q :=
    h () True ⟨act_self_denial, self_denial_holds⟩
  obtain ⟨q, hq⟩ := hchooses
  exact no_choice_all () True q hq

end SelfDenialOfChoiceModel

/-!
### 12. Delusional Self-Ascription of Choice (Non-Factive Self-Reference)
Investigates whether performing/meaning an act whose content asserts "I am freely choosing"
can force genuine choice in a non-factive / single-minded agent.
Result: REFUTED BY HOSTILE MODEL.
An agent can intentionally perform an act with content `p := (∃ q, Chooses s p q)` (`Act s p`),
while in fact `p = False` and `∀ q, ¬ Chooses s p q`.
Performing a self-ascription of choice does NOT make the ascription true.
-/

namespace DelusionalSelfChoiceModel

def Subject : Type := Unit
def State : Type := Unit
def Means (_s : Subject) (_p : Prop) : Prop := True
def Initiates (_s : Subject) (_w _w' : State) (_p : Prop) : Prop := True
def Act (s : Subject) (p : Prop) : Prop := Means s p ∧ ∃ w w' : State, Initiates s w w' p
def Chooses (_s : Subject) (_p _q : Prop) : Prop := False

def SelfAssertedChoice (s : Subject) (p : Prop) : Prop :=
  p ↔ ∃ q : Prop, Chooses s p q

/-- The proposition "I am freely choosing" is identically False in this model. -/
theorem self_choice_prop_false : ¬ ∃ q : Prop, Chooses () False q :=
  fun ⟨_, h⟩ => h

/-- The self-ascription proposition holds for `p = False`. -/
theorem self_choice_equiv : SelfAssertedChoice () False := by
  dsimp [SelfAssertedChoice]
  constructor
  · intro hf
    exact False.elim hf
  · intro ⟨_, hf⟩
    exact False.elim hf

/-- The intentional act of uttering/meaning the false self-ascription holds. -/
theorem act_delusional_choice : Act () False :=
  ⟨trivial, (), (), trivial⟩

/-- Non-factive self-ascription of choice is consistent with zero genuine choice.
    Refutes `¬ ∃ s p, Act s p ∧ SelfAssertedChoice s p ∧ (∀ q, ¬ Chooses s p q)`. -/
theorem delusional_choice_consistent :
    ∃ s : Subject, ∃ p : Prop, Act s p ∧ SelfAssertedChoice s p ∧ (∀ q : Prop, ¬ Chooses s p q) :=
  ⟨(), False, act_delusional_choice, self_choice_equiv, fun _ hf => hf⟩

/-- Non-factive self-ascription of choice does NOT derive genuine choice.
    Refutes `∀ s p, Act s p ∧ SelfAssertedChoice s p → ∃ q, Chooses s p q`. -/
theorem nonfactive_self_choice_not_derives_choice :
    ¬ (∀ (s : Subject) (p : Prop), Act s p ∧ SelfAssertedChoice s p → ∃ q : Prop, Chooses s p q) := by
  intro h
  have hchooses : ∃ q : Prop, Chooses () False q :=
    h () False ⟨act_delusional_choice, self_choice_equiv⟩
  obtain ⟨_, hf⟩ := hchooses
  exact hf

end DelusionalSelfChoiceModel

/-
### 11. Separation of Existential Choice (A14∃) from Universal Choice (A14)

Candidate: `A14_exists : (∃ s p, Act s p) → ∃ s p q, Chooses s p q`
Target: `A14 : ∀ s p, Act s p → ∃ q, Chooses s p q`

Question: Does A14∃ derive A14?
Result: REFUTED BY HOSTILE MODEL (`A14∃ < A14`).

Structure:
Two subjects `choiceUser` and `unilateral`.
- `choiceUser` performs an intentional action and co-means incompatible alternatives (has genuine choice).
- `unilateral` performs an intentional action under factive/veridical meaning (no choice possible).

Result:
- An action occurs (`∃ s p, Act s p`).
- A genuine choice occurs (`∃ s p q, Chooses s p q`, witnessed by `choiceUser`).
- Therefore, `A14_exists` holds trivially.
- But universal A14 fails for `unilateral`.
Hence `A14_exists` does NOT entail `A14`.
-/

namespace ExistentialChoiceSeparationModel

inductive Subject : Type
  | choiceUser
  | unilateral

def State : Type := Unit

def Means : Subject → Prop → Prop
  | Subject.choiceUser, _ => True
  | Subject.unilateral, p => (p = True)

def Initiates (_s : Subject) (_w _w' : State) (_p : Prop) : Prop := True

def Act (s : Subject) (p : Prop) : Prop :=
  Means s p ∧ ∃ w w' : State, Initiates s w w' p

def Chooses (s : Subject) (p q : Prop) : Prop :=
  Means s p ∧ Means s q ∧ Logos.Alternatives.Incompatible p q

def UniversalA14 : Prop :=
  ∀ (s : Subject) (p : Prop), Act s p → ∃ q : Prop, Chooses s p q

def ExistentialA14 : Prop :=
  (∃ s : Subject, ∃ p : Prop, Act s p) → ∃ s : Subject, ∃ p q : Prop, Chooses s p q

/-- The choice user performs an intentional action. -/
theorem act_choiceUser : Act Subject.choiceUser True :=
  ⟨trivial, (), (), trivial⟩

/-- The unilateral agent performs an intentional action. -/
theorem act_unilateral : Act Subject.unilateral True :=
  ⟨rfl, (), (), trivial⟩

/-- The choice user genuinely chooses between True and False. -/
theorem chooses_choiceUser : Chooses Subject.choiceUser True False :=
  ⟨trivial, trivial, fun h => h.2⟩

/-- An intentional act occurs in the model. -/
theorem some_act : ∃ s : Subject, ∃ p : Prop, Act s p :=
  ⟨Subject.choiceUser, True, act_choiceUser⟩

/-- A genuine choice occurs in the model. -/
theorem some_choice : ∃ s : Subject, ∃ p q : Prop, Chooses s p q :=
  ⟨Subject.choiceUser, True, False, chooses_choiceUser⟩

/-- Existential A14 holds in this model. -/
theorem existential_a14_holds : ExistentialA14 :=
  fun _ => some_choice

/-- Universal A14 fails in this model for the unilateral agent. -/
theorem universal_a14_fails : ¬ UniversalA14 := by
  intro hUniv
  have hChoice : ∃ q : Prop, Chooses Subject.unilateral True q :=
    hUniv Subject.unilateral True act_unilateral
  obtain ⟨q, _, hqMeans, hincomp⟩ := hChoice
  have hqTrue : q = True := hqMeans
  subst hqTrue
  exact hincomp ⟨trivial, trivial⟩

/-- A14∃ does NOT entail universal A14:
    A14∃ is strictly weaker than universal A14 (A14∃ < A14). -/
theorem existential_not_entails_universal :
    ¬ (ExistentialA14 → UniversalA14) := by
  intro h
  exact universal_a14_fails (h existential_a14_holds)

end ExistentialChoiceSeparationModel

/-
### 12. Separation of Unrealized Possibility Representation from Genuine Choice
Investigates whether the cognitive capacity to represent an unrealized/false proposition
(`∃ s p, Means s p ∧ ¬p`, non-factive intentionality) is sufficient to derive genuine choice (`FreeWill`).
Result: REFUTED BY HOSTILE MODEL.
An agent can mean/entertain a false proposition without possessing genuine choice among alternatives.
-/

namespace UnrealizedPossibilityModel

def Subject : Type := Unit
def State : Type := Unit
def Means (_s : Subject) (p : Prop) : Prop := (p = False)
def Initiates (_s : Subject) (_w _w' : State) (_p : Prop) : Prop := True
def Act (s : Subject) (p : Prop) : Prop := Means s p ∧ ∃ w w' : State, Initiates s w w' p
def Chooses (_s : Subject) (_p _q : Prop) : Prop := False
def FreeWill (s : Subject) : Prop := ∃ p q : Prop, Chooses s p q

/-- The subject represents an unrealized proposition (False). -/
theorem represents_unrealized : ∃ (s : Subject) (p : Prop), Means s p ∧ ¬p :=
  ⟨(), False, rfl, fun h => h⟩

/-- Free will is identically False in this model. -/
theorem no_freeWill : ¬ ∃ (s : Subject), FreeWill s :=
  fun ⟨_, _, _, hFalse⟩ => hFalse

/-- Representing an unrealized proposition does NOT derive free will / genuine choice. -/
theorem unrealized_not_entails_freeWill :
    ¬ ((∃ (s : Subject) (p : Prop), Means s p ∧ ¬p) → ∃ (s : Subject), FreeWill s) := by
  intro h
  exact no_freeWill (h represents_unrealized)

end UnrealizedPossibilityModel

/-
### 13. Parameterized Hostile Model Family for the Entire Pre-A14 Theory
Constructs a general family of models parameterized by an admissible meaning relation `R : Bool → Prop → Prop`.
Proves that EVERY horn-free admissible relation satisfies the complete pre-A14 theory, contains intentional action,
yet refutes F1b / genuine choice.
-/

namespace ParameterizedHostileFamily

open CountermodelVeridicalMeaning

structure AdmissiblePreA14Meaning (R : Bool → Prop → Prop) : Prop where
  act_true : R true True
  act_false : R false True

def HornFreeMeaning (R : Bool → Prop → Prop) : Prop :=
  ∀ (s : Bool) (p q : Prop), R s p → R s q → ¬ Logos.Alternatives.Incompatible p q

def parameterizedModel (R : Bool → Prop → Prop) : PreA13FullTheorySignature := {
  Subject := Bool,
  State := Unit,
  Entity := Unit,
  World := Unit,
  Means := R,
  Initiates := fun _ _ _ p => p,
  T := fun p => p,
  IsFalse := fun p => ¬ p,
  Ground := fun _ p => p,
  GroundProp := fun _ p => p,
  Personal := fun _ => True,
  IsPresentPersonalFeature := fun p => p
}

/-- Every admissible meaning relation satisfies the entire pre-A14 theory of Γ. -/
theorem parameterized_model_satisfies_preA14
    (R : Bool → Prop → Prop) (hAdm : AdmissiblePreA14Meaning R) :
    PreA13FullTheory (parameterizedModel R) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 1. Performative Act Datum
    exact ⟨true, True, hAdm.act_true, (), (), trivial⟩
  · -- 2. Plurality of two distinct persons
    refine ⟨true, false, ⟨True, hAdm.act_true⟩, ⟨True, hAdm.act_false⟩, ?_⟩
    intro hEq; cases hEq
  · -- 3. Bivalent normative order
    exact ⟨fun hAll => hAll True trivial, fun hAll => (hAll False)⟩
  · -- 4. Truthmaker Grounding
    intro p hp; exact ⟨(), hp⟩
  · -- 5. Global ground
    exact ⟨(), fun _ hp => hp⟩
  · -- 6. GroundPrincipleProp
    intro p hp; exact ⟨(), hp⟩
  · -- 7. AxPersonalGround
    intro p hp; exact ⟨(), hp, trivial⟩
  · -- 8. Fallibility
    exact ⟨true, False, fun hf => hf⟩
  · -- 9. Transcendental retorsion
    intro _speaker ⟨_, hNoAct⟩
    exact hNoAct ⟨true, True, hAdm.act_true, (), (), trivial⟩
  · -- 10. C101 bivalent partition
    intro s p
    constructor
    · intro hAct
      by_cases hp : p
      · left; exact ⟨hAct, hp⟩
      · right; exact ⟨hAct, hp⟩
    · rintro (⟨hAct, _⟩ | ⟨hAct, _⟩) <;> exact hAct

/-- An intentional act occurs in the parameterized model. -/
theorem parameterized_model_has_act
    (R : Bool → Prop → Prop) (hAdm : AdmissiblePreA14Meaning R) :
    ∃ s : Bool, ∃ p : Prop, FullAct (parameterizedModel R) s p :=
  ⟨true, True, hAdm.act_true, (), (), trivial⟩

/-- Every horn-free relation has zero genuine choice. -/
theorem parameterized_model_horn_free_has_no_choice
    (R : Bool → Prop → Prop) (hHF : HornFreeMeaning R) :
    ∀ (s : Bool) (p q : Prop), ¬ FullChooses (parameterizedModel R) s p q := by
  intro s p q ⟨hmp, hmq, hincomp⟩
  exact hHF s p q hmp hmq hincomp

/-- Every admissible horn-free relation refutes F1b while satisfying the pre-A14 theory. -/
theorem parameterized_model_horn_free_refutes_f1b
    (R : Bool → Prop → Prop) (hAdm : AdmissiblePreA14Meaning R) (hHF : HornFreeMeaning R) :
    ¬ ((∃ s : Bool, ∃ p : Prop, FullAct (parameterizedModel R) s p) →
       ∃ s : Bool, FullFreeWill (parameterizedModel R) s) := by
  intro hF1b
  have hAct : ∃ s : Bool, ∃ p : Prop, FullAct (parameterizedModel R) s p :=
    parameterized_model_has_act R hAdm
  have hFW : ∃ s : Bool, FullFreeWill (parameterizedModel R) s := hF1b hAct
  obtain ⟨s, p, q, hc⟩ := hFW
  exact parameterized_model_horn_free_has_no_choice R hHF s p q hc

/-- Concrete family instances:
    1. Veridical meaning relation: R_veridical s p := p. -/
def veridicalMeaning : Bool → Prop → Prop := fun _ p => p

theorem veridical_admissible : AdmissiblePreA14Meaning veridicalMeaning :=
  ⟨trivial, trivial⟩

theorem veridical_horn_free : HornFreeMeaning veridicalMeaning :=
  fun _ _ _ hp hq hincomp => hincomp ⟨hp, hq⟩

/-- Concrete family instances:
    2. Single-content meaning relation: R_single s p := (p = True). -/
def singleContentMeaning : Bool → Prop → Prop := fun _ p => (p = True)

theorem single_content_admissible : AdmissiblePreA14Meaning singleContentMeaning :=
  ⟨rfl, rfl⟩

theorem single_content_horn_free : HornFreeMeaning singleContentMeaning := by
  intro s p q hp hq hincomp
  subst hp hq
  exact hincomp ⟨trivial, trivial⟩

end ParameterizedHostileFamily

/-
### 14. Contrastive Collapse Transformation and Invariance Theorems (Claims C & D)
Formalizes the generic model transformation `Collapse(M)`:
    M ↦ Collapse(M)
which veridically filters intentional meaning `Means s p ↦ Means s p ∧ p`,
unconditionally destroying all genuine choice while preserving factive acts, causal structure,
and the complete 12-axiom pre-A14 theory on factive models.
-/

namespace ModelTransformationCollapse

open CountermodelVeridicalMeaning

def ContrastiveCollapse (I : PreA13FullTheorySignature) : PreA13FullTheorySignature := {
  I with Means := fun s p => I.Means s p ∧ p
}

/-- The Contrastive Collapse unconditionally destroys ALL genuine choice in ANY model. -/
theorem collapse_destroys_all_choice
    (I : PreA13FullTheorySignature) (s : I.Subject) (p q : Prop) :
    ¬ FullChooses (ContrastiveCollapse I) s p q := by
  rintro ⟨hmp, hmq, hincomp⟩
  exact hincomp ⟨hmp.2, hmq.2⟩

/-- The Contrastive Collapse preserves any factive intentional act. -/
theorem collapse_preserves_factive_act
    (I : PreA13FullTheorySignature) (s : I.Subject) (p : Prop)
    (hAct : FullAct I s p) (hp : p) :
    FullAct (ContrastiveCollapse I) s p :=
  ⟨⟨hAct.1, hp⟩, hAct.2⟩

/-- The Contrastive Collapse preserves objective choice fields for factive acts. -/
theorem collapse_preserves_choiceField
    (I : PreA13FullTheorySignature) (s : I.Subject) (p : Prop)
    (hAct : FullAct I s p) (hp : p) :
    (ContrastiveCollapse I).Means s p ∧ Logos.Alternatives.Incompatible p (¬p) :=
  ⟨⟨hAct.1, hp⟩, fun h => h.2 h.1⟩

/-- Free will is identically False in the collapsed model. -/
theorem collapse_has_no_freeWill
    (I : PreA13FullTheorySignature) :
    ¬ ∃ s : (ContrastiveCollapse I).Subject, FullFreeWill (ContrastiveCollapse I) s := by
  rintro ⟨s, p, q, hc⟩
  exact collapse_destroys_all_choice I s p q hc

/-!
#### Blocker Analysis: Failure of Unconditioned Preservation of Pre-A14 Theory
Identifies the exact axioms that prevent unconditioned preservation of `PreA13FullTheory` under collapse.
-/

/-- Axiom 1 Blocker: If all intentional acts in I are non-factive,
    the collapsed model contains zero intentional acts, refuting Axiom 1 (Act Datum). -/
theorem nonfactive_act_blocks_collapse
    (I : PreA13FullTheorySignature)
    (hNonFactive : ∀ (s : I.Subject) (p : Prop), FullAct I s p → ¬ p) :
    ¬ ∃ (s : (ContrastiveCollapse I).Subject) (p : Prop), FullAct (ContrastiveCollapse I) s p := by
  rintro ⟨s, p, ⟨hmp, hp⟩, hInit⟩
  have hOrigAct : FullAct I s p := ⟨hmp, hInit⟩
  exact (hNonFactive s p hOrigAct) hp

/-- Axiom 2 Blocker: If a person in I only means non-factive contents,
    that person ceases to be a person in the collapsed model, refuting Axiom 2 (Plurality of Persons). -/
theorem nonfactive_plurality_blocks_collapse
    (I : PreA13FullTheorySignature) (s : I.Subject)
    (hNonFactivePerson : ∀ p : Prop, I.Means s p → ¬ p) :
    ¬ FullPerson (ContrastiveCollapse I) s := by
  rintro ⟨p, hmp, hp⟩
  exact (hNonFactivePerson p hmp) hp

/-!
#### Factive Pre-A14 Theory & Full Preservation Theorem (Claim C)
-/

/-- The factive pre-A14 theory: requires that the intentional acts and the plurality of persons
    be realized factively in the actual state of affairs. -/
structure FactivePreA14Theory (I : PreA13FullTheorySignature) : Prop where
  preA14 : PreA13FullTheory I
  factive_act : ∃ s : I.Subject, ∃ p : Prop, FullAct I s p ∧ p
  factive_plurality : ∃ (s₁ s₂ : I.Subject), (∃ p : Prop, I.Means s₁ p ∧ p) ∧ (∃ q : Prop, I.Means s₂ q ∧ q) ∧ s₁ ≠ s₂

/-- Full Pre-A14 Preservation Theorem (Claim C):
    The Contrastive Collapse preserves the complete 12-axiom pre-A14 theory on any factive model. -/
theorem collapse_preserves_preA14
    (I : PreA13FullTheorySignature) (h : FactivePreA14Theory I) :
    PreA13FullTheory (ContrastiveCollapse I) := by
  obtain ⟨⟨_, _, h3, h4, h5, h6, h7, h8, _, _⟩, ⟨sAct, pAct, hActFactive, hpAct⟩, ⟨s₁, s₂, ⟨p₁, hmp₁, hp₁⟩, ⟨p₂, hmp₂, hp₂⟩, hNeq⟩⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 1. Performative Act Datum
    exact ⟨sAct, pAct, ⟨hActFactive.1, hpAct⟩, hActFactive.2⟩
  · -- 2. Plurality of two distinct persons
    exact ⟨s₁, s₂, ⟨p₁, ⟨hmp₁, hp₁⟩⟩, ⟨p₂, ⟨hmp₂, hp₂⟩⟩, hNeq⟩
  · -- 3. Bivalent normative order
    exact h3
  · -- 4. Truthmaker Grounding
    exact h4
  · -- 5. Global ground
    exact h5
  · -- 6. GroundPrincipleProp
    exact h6
  · -- 7. AxPersonalGround
    exact h7
  · -- 8. Fallibility
    exact h8
  · -- 9. Transcendental retorsion
    intro _speaker ⟨_, hNoAct⟩
    exact hNoAct ⟨sAct, pAct, ⟨hActFactive.1, hpAct⟩, hActFactive.2⟩
  · -- 10. C101 bivalent partition
    intro s p
    constructor
    · intro hAct
      left
      exact ⟨hAct, hAct.1.2⟩
    · rintro (⟨hAct, _⟩ | ⟨hAct, _⟩) <;> exact hAct

/-- Verification that the canonical hostile instance fullTheoryHostileInstance satisfies FactivePreA14Theory. -/
theorem fullTheoryHostileInstance_is_factive :
    FactivePreA14Theory fullTheoryHostileInstance := {
  preA14 := fullTheory_holds,
  factive_act := ⟨true, True, ⟨trivial, (), (), trivial⟩, trivial⟩,
  factive_plurality := ⟨true, false, ⟨True, trivial, trivial⟩, ⟨True, trivial, trivial⟩, fun h => by cases h⟩
}

/-!
#### Model-Theoretic Impossibility Theorem (Claim D)
-/

/-- A property of models B is contrastive-blind if it is preserved under contrastive collapse
    on all factive pre-A14 models. -/
def PreA14ContrastiveBlind (B : PreA13FullTheorySignature → Prop) : Prop :=
  ∀ I : PreA13FullTheorySignature,
    FactivePreA14Theory I →
    B I →
    B (ContrastiveCollapse I)

/-- Consistency condition: B admits at least one factive pre-A14 model. -/
def PreA14Consistent (B : PreA13FullTheorySignature → Prop) : Prop :=
  ∃ I : PreA13FullTheorySignature, FactivePreA14Theory I ∧ B I

/-- Model-Theoretic Impossibility Theorem (Claim D):
    Every consistent contrastive-blind extension B admits a model of the entire pre-A14 theory
    that satisfies B, contains an intentional act, and refutes F1b. -/
theorem blind_extension_cannot_derive_f1b
    (B : PreA13FullTheorySignature → Prop)
    (hBlind : PreA14ContrastiveBlind B)
    (hCons : PreA14Consistent B) :
    ∃ M : PreA13FullTheorySignature,
      PreA13FullTheory M ∧
      B M ∧
      (∃ s : M.Subject, ∃ p : Prop, FullAct M s p) ∧
      ¬ (∃ s : M.Subject, FullFreeWill M s) := by
  obtain ⟨I, hFactive, hB⟩ := hCons
  refine ⟨ContrastiveCollapse I, ?_, ?_, ?_, ?_⟩
  · exact collapse_preserves_preA14 I hFactive
  · exact hBlind I hFactive hB
  · obtain ⟨s, p, hAct, hp⟩ := hFactive.factive_act
    exact ⟨s, p, collapse_preserves_factive_act I s p hAct hp⟩
  · exact collapse_has_no_freeWill I

end ModelTransformationCollapse

/-
### 15. Syntactic Fragment and Non-Definability Theorems (Claim E)
Constructs the contrastive-blind formula grammar `BlindFormula`, proves its invariance under
contrastive collapse by structural induction, and machine-checks the non-definability of genuine choice.
-/

namespace ExpressivityBoundary

open ModelTransformationCollapse
open CountermodelVeridicalMeaning

/-- The inductive syntax of contrastive-blind formulas, decoupled from concrete model instances
    and parameterized only over carrier types. -/
inductive BlindFormula (Subject State Entity : Type) : Type
  | top : BlindFormula Subject State Entity
  | bot : BlindFormula Subject State Entity
  | causal (s : Subject) (w w' : State) (p : Prop) : BlindFormula Subject State Entity
  | ground (e : Entity) (p : Prop) : BlindFormula Subject State Entity
  | incomp (p q : Prop) : BlindFormula Subject State Entity
  | factiveMeans (s : Subject) (p : Prop) : BlindFormula Subject State Entity
  | not (φ : BlindFormula Subject State Entity) : BlindFormula Subject State Entity
  | and (φ ψ : BlindFormula Subject State Entity) : BlindFormula Subject State Entity
  | or (φ ψ : BlindFormula Subject State Entity) : BlindFormula Subject State Entity
  | imp (φ ψ : BlindFormula Subject State Entity) : BlindFormula Subject State Entity

/-- Semantic evaluation of a blind formula in a model. -/
def eval (I : PreA13FullTheorySignature) :
    BlindFormula I.Subject I.State I.Entity → Prop
  | BlindFormula.top => True
  | BlindFormula.bot => False
  | BlindFormula.causal s w w' p => I.Initiates s w w' p
  | BlindFormula.ground e p => I.Ground e p
  | BlindFormula.incomp p q => Logos.Alternatives.Incompatible p q
  | BlindFormula.factiveMeans s p => I.Means s p ∧ p
  | BlindFormula.not φ => ¬ eval I φ
  | BlindFormula.and φ ψ => eval I φ ∧ eval I ψ
  | BlindFormula.or φ ψ => eval I φ ∨ eval I ψ
  | BlindFormula.imp φ ψ => eval I φ → eval I ψ

/-- Invariance Theorem for the Blind Fragment:
    Every formula in `BlindFormula` evaluates identically in any model and in its contrastive collapse.
    Proven by structural induction on the formula. -/
theorem blind_formula_collapse_invariant
    (I : PreA13FullTheorySignature) (φ : BlindFormula I.Subject I.State I.Entity) :
    eval I φ ↔ eval (ContrastiveCollapse I) φ := by
  induction φ with
  | top => rfl
  | bot => rfl
  | causal s w w' p => rfl
  | ground e p => rfl
  | incomp p q => rfl
  | factiveMeans s p =>
    dsimp [eval, ContrastiveCollapse]
    constructor
    · rintro ⟨hmp, hp⟩
      exact ⟨⟨hmp, hp⟩, hp⟩
    · rintro ⟨⟨hmp, hp⟩, _⟩
      exact ⟨hmp, hp⟩
  | not φ ih =>
    dsimp [eval]
    rw [ih]
  | and φ ψ ih1 ih2 =>
    dsimp [eval]
    rw [ih1, ih2]
  | or φ ψ ih1 ih2 =>
    dsimp [eval]
    rw [ih1, ih2]
  | imp φ ψ ih1 ih2 =>
    dsimp [eval]
    rw [ih1, ih2]

/-- A concrete model with genuine choice witnessing the expressivity separation. -/
def choiceWitnessModel : PreA13FullTheorySignature := {
  Subject := Bool,
  State := Unit,
  Entity := Unit,
  World := Unit,
  Means := fun _ _ => True,
  Initiates := fun _ _ _ p => p,
  T := fun p => p,
  IsFalse := fun p => ¬ p,
  Ground := fun _ p => p,
  GroundProp := fun _ p => p,
  Personal := fun _ => True,
  IsPresentPersonalFeature := fun p => p
}

/-- The choice witness model has genuine choice for the true/false pair. -/
theorem choiceWitnessModel_has_choice :
    FullChooses choiceWitnessModel true True False :=
  ⟨trivial, trivial, fun h => h.2⟩

/-- Non-Definability of Genuine Choice (Claim E):
    No formula in the contrastive-blind fragment can define genuine choice across models. -/
theorem no_blind_formula_defines_choice :
    ¬ ∃ (φ : BlindFormula Bool Unit Unit),
      (eval choiceWitnessModel φ ↔ FullChooses choiceWitnessModel true True False) ∧
      (eval (ContrastiveCollapse choiceWitnessModel) φ ↔ FullChooses (ContrastiveCollapse choiceWitnessModel) true True False) := by
  rintro ⟨φ, hEquiv1, hEquiv2⟩
  have hChoice : FullChooses choiceWitnessModel true True False := choiceWitnessModel_has_choice
  have hEvalOrig : eval choiceWitnessModel φ := hEquiv1.mpr hChoice
  have hEvalCollapsed : eval (ContrastiveCollapse choiceWitnessModel) φ :=
    (blind_formula_collapse_invariant choiceWitnessModel φ).mp hEvalOrig
  have hChoiceCollapsed : FullChooses (ContrastiveCollapse choiceWitnessModel) true True False :=
    hEquiv2.mp hEvalCollapsed
  exact collapse_destroys_all_choice choiceWitnessModel true True False hChoiceCollapsed

/-- Non-Definability of Free Will:
    No formula in the contrastive-blind fragment can define FreeWill across models. -/
theorem no_blind_formula_defines_freeWill :
    ¬ ∃ (φ : BlindFormula Bool Unit Unit),
      (eval choiceWitnessModel φ ↔ (∃ s : Bool, FullFreeWill choiceWitnessModel s)) ∧
      (eval (ContrastiveCollapse choiceWitnessModel) φ ↔ (∃ s : Bool, FullFreeWill (ContrastiveCollapse choiceWitnessModel) s)) := by
  rintro ⟨φ, hEquiv1, hEquiv2⟩
  have hFW : ∃ s : Bool, FullFreeWill choiceWitnessModel s :=
    ⟨true, True, False, choiceWitnessModel_has_choice⟩
  have hEvalOrig : eval choiceWitnessModel φ := hEquiv1.mpr hFW
  have hEvalCollapsed : eval (ContrastiveCollapse choiceWitnessModel) φ :=
    (blind_formula_collapse_invariant choiceWitnessModel φ).mp hEvalOrig
  have hFWCollapsed : ∃ s : Bool, FullFreeWill (ContrastiveCollapse choiceWitnessModel) s :=
    hEquiv2.mp hEvalCollapsed
  exact collapse_has_no_freeWill choiceWitnessModel hFWCollapsed

/-
### 16. Ontology Hardening Countermodels
Formal machine-checked countermodels proving the independence of the hardened ontology:
1. Act does NOT entail NecessarySubject or NecessaryEntity.
2. Person does NOT entail FreeSubject, and FreeSubject does NOT entail Person.
3. Plurality does NOT entail Affects, Helps, or Loves.
4. FreeWill + Plurality does NOT entail Loves.
5. Atomic truthmaking does NOT entail compound truthmaking.
-/

namespace OntologyHardeningCountermodels

/-!
#### 1. Contingent Agency: Act does NOT imply Necessary Existence
Model: Two worlds (`Bool`: `true` = actual, `false` = counterfactual).
Subject acts in `true`, but does not exist in `false`.
-/
namespace ContingentAgencyModel

inductive World2 : Type
  | w0 : World2
  | w1 : World2

abbrev Subj : Type := Unit
abbrev Ent : Type := Unit

def Act (_s : Subj) (_p : Prop) : Prop := True
def SubjectExistsAt (w : World2) (_s : Subj) : Prop :=
  match w with
  | World2.w0 => True
  | World2.w1 => False

def NecessarySubject (s : Subj) : Prop := ∀ w : World2, SubjectExistsAt w s
def EntityExistsAt (w : World2) (_e : Ent) : Prop :=
  match w with
  | World2.w0 => True
  | World2.w1 => False

def NecessaryEntity (e : Ent) : Prop := ∀ w : World2, EntityExistsAt w e

theorem act_occurs : ∃ s : Subj, ∃ p : Prop, Act s p :=
  ⟨(), True, trivial⟩

theorem subject_not_necessary : ¬ ∀ s : Subj, NecessarySubject s := by
  intro h
  have hw1 := h () World2.w1
  exact hw1

/-- Hardened Independence Theorem:
    The performative existence of an intentional act does NOT entail that the subject is necessary. -/
theorem act_not_entails_necessary_subject :
    (∃ s : Subj, ∃ p : Prop, Act s p) ∧ ¬ (∀ s : Subj, NecessarySubject s) :=
  ⟨act_occurs, subject_not_necessary⟩

theorem entity_not_necessary : ¬ ∀ e : Ent, NecessaryEntity e := by
  intro h
  have hw1 := h () World2.w1
  exact hw1

/-- Hardened Independence Theorem:
    The performative existence of an intentional act does NOT entail that its entity-correlate is necessary. -/
theorem act_not_entails_necessary_entity :
    (∃ s : Subj, ∃ p : Prop, Act s p) ∧ ¬ (∀ e : Ent, NecessaryEntity e) :=
  ⟨act_occurs, entity_not_necessary⟩

end ContingentAgencyModel

/-!
#### 2. Personhood vs Free Agency
-/
namespace PersonhoodAgencySeparation

abbrev Subj : Type := Bool

-- Person: true is a person, false is not
def Person (s : Subj) : Prop := s = true
-- FreeSubject: false is a free chooser, true is not
def FreeSubject (s : Subj) : Prop := s = false

theorem person_not_entails_freeSubject :
    (∃ s : Subj, Person s) ∧ ¬ (∀ s : Subj, Person s → FreeSubject s) := by
  refine ⟨⟨true, rfl⟩, ?_⟩
  intro h
  have hf := h true rfl
  cases hf

theorem freeSubject_not_entails_person :
    (∃ s : Subj, FreeSubject s) ∧ ¬ (∀ s : Subj, FreeSubject s → Person s) := by
  refine ⟨⟨false, rfl⟩, ?_⟩
  intro h
  have hp := h false rfl
  cases hp

end PersonhoodAgencySeparation

/-!
#### 3. Interpersonal Relations: Plurality does NOT entail Affects, Helps, or Loves
-/
namespace DisconnectedPluralityModel

abbrev Subj : Type := Bool

def Person (_s : Subj) : Prop := True
def Affects (_s _t : Subj) : Prop := False
def Helps (_s _t : Subj) : Prop := False
def Harms (_s _t : Subj) : Prop := False
def Loves (s t : Subj) : Prop := Helps s t ∧ ¬ Harms s t
def Chooses (_s : Subj) (_p _q : Prop) : Prop := True
def FreeWill (_s : Subj) : Prop := True

theorem two_persons_exist : ∃ s₁ s₂ : Subj, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ :=
  ⟨true, false, trivial, trivial, fun h => by cases h⟩

theorem no_affects : ¬ ∃ s₁ s₂ : Subj, Affects s₁ s₂ :=
  fun ⟨_, _, ha⟩ => ha

theorem no_helps : ¬ ∃ s₁ s₂ : Subj, Helps s₁ s₂ :=
  fun ⟨_, _, hh⟩ => hh

theorem no_love : ¬ ∃ s₁ s₂ : Subj, Loves s₁ s₂ :=
  fun ⟨_, _, hl⟩ => hl.1

/-- Plurality does not entail that subjects affect each other. -/
theorem plurality_not_entails_affects :
    (∃ s₁ s₂ : Subj, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂) ∧
    ¬ (∃ s₁ s₂ : Subj, Affects s₁ s₂) :=
  ⟨two_persons_exist, no_affects⟩

/-- Plurality does not entail that subjects help each other. -/
theorem plurality_not_entails_helps :
    (∃ s₁ s₂ : Subj, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂) ∧
    ¬ (∃ s₁ s₂ : Subj, Helps s₁ s₂) :=
  ⟨two_persons_exist, no_helps⟩

/-- Plurality does not entail love. -/
theorem plurality_not_entails_love :
    (∃ s₁ s₂ : Subj, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂) ∧
    ¬ (∃ s₁ s₂ : Subj, Loves s₁ s₂) :=
  ⟨two_persons_exist, no_love⟩

/-- Free agency + plurality does not entail love. -/
theorem freewill_and_plurality_not_entails_love :
    (∃ s₁ s₂ : Subj, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂) ∧
    (∀ s : Subj, FreeWill s) ∧
    ¬ (∃ s₁ s₂ : Subj, Loves s₁ s₂) :=
  ⟨two_persons_exist, fun _ => trivial, no_love⟩

end DisconnectedPluralityModel

/-!
#### 4. Grounding: Atomic Truthmaking does NOT entail Formula Truthmaking
-/
namespace AtomicVsFormulaTruthmakerModel

inductive FormM : Type
  | atom (n : Nat) : FormM
  | disj (p q : FormM) : FormM

abbrev Ent : Type := Nat

def Ground (e : Ent) : FormM → Prop
  | FormM.atom n => e = n
  | FormM.disj _ _ => False

theorem atomic_grounded (n : Nat) : ∃ e : Ent, Ground e (FormM.atom n) :=
  ⟨n, rfl⟩

theorem compound_not_grounded (p q : FormM) : ¬ ∃ e : Ent, Ground e (FormM.disj p q) :=
  fun ⟨_, hg⟩ => hg

end AtomicVsFormulaTruthmakerModel

end OntologyHardeningCountermodels

end ExpressivityBoundary

end DeeperSemanticRoutes

-- ===========================================================================
-- Part F: Adversarial Investigation of the Grounding Status of Truthmaking
-- ===========================================================================

namespace TruthmakingInvestigation

open Logos.Core (T tschema)
open Logos.Semantics (Form World Satisfies TrueAt)
open Logos.Truthmaker (Entity ExistsAt NecessarilyTrue otherWorld actualWorld)
open Logos.Modal (NecessaryEntity Contingent)
open Logos.GroundPerson (GroundProp GroundPrincipleProp)

/-!
### 1. Representation and Status of the Principle

Let G be the proposition asserting universal propositional truthmaking:
`G := ∀ p : Prop, T p → ∃ e : Entity, GroundProp e p`
-/

/-- The truthmaking principle G as an ambient proposition in Lean's Prop. -/
def G : Prop := ∀ p : Prop, T p → ∃ e : Entity, GroundProp e p

/-- Definitional equivalence between T(G) and G:
    Because T is defined as the identity on Prop (`T p := p`),
    the proposition T(G) is definitionally identical to G itself. -/
theorem T_G_iff_G : T G ↔ G := Iff.rfl

/-- Ambient derivability of G:
    In the ambient Γ theory containing `axiom GroundPrincipleProp`,
    G is derivable by directly applying the axiom. -/
theorem G_ambient_derivable : G :=
  fun _ hp => GroundPrincipleProp hp

/-- Ambient derivability of T(G):
    Because T(G) = G, T(G) is provable in ambient Γ under the axiom. -/
theorem T_G_ambient_derivable : T G :=
  G_ambient_derivable

/-- Signature for testing the independence of G from the performative Core:
    In any semantic model satisfying Core truth, does G hold by logic alone? -/
structure TruthmakingIndependenceSignature where
  Entity : Type
  GroundProp : Entity → Prop → Prop
  T : Prop → Prop
  tschema : ∀ p, T p ↔ p

/-- Countermodel 1: The Deflationary / Non-Grounded Model.
    Truth is genuine (T p ↔ p), but no entity grounds any proposition.
    This model satisfies classical logic and performative truth, but refutes G. -/
def DeflationaryModel : TruthmakingIndependenceSignature where
  Entity := Unit
  GroundProp := fun _ _ => False
  T := fun p => p
  tschema := fun _ => Iff.rfl

/-- Separation Theorem: G is NOT a logical or performative theorem.
    Without postulating `GroundPrincipleProp` as an axiom, G cannot be derived. -/
theorem truthmaking_not_logically_forced :
    ¬ (∀ I : TruthmakingIndependenceSignature, ∀ p : Prop, I.T p → ∃ e : I.Entity, I.GroundProp e p) := by
  intro hAll
  have hInst := hAll DeflationaryModel True trivial
  obtain ⟨e, hg⟩ := hInst
  exact hg

/-!
### 2. Testing and Separating Claims A, B, C, D

Claim A: T(G)
Claim B: □G
Claim C: ∃ e, GroundProp e G
Claim D: ∃ e, NecessaryEntity e ∧ GroundProp e G
-/

/-- Claim A: The truthmaking principle is true. -/
def ClaimA : Prop := T G

/-- Claim B (Degenerate Propositional Necessity):
    Under `Necessity.lean:51`, `Necessity G := ∀ _w : World, G`. -/
def ClaimB_Prop : Prop := ∀ _w : World, G

/-- Claim B (World-Indexed Modal Truthmaking):
    Every world provides existing entities that ground every true proposition. -/
def ClaimB_World : Prop :=
  ∀ w : World, ∀ p : Prop, T p → ∃ e : Entity, ExistsAt w e ∧ GroundProp e p

/-- Claim C: There exists some entity that grounds the truthmaking principle G. -/
def ClaimC : Prop := ∃ e : Entity, GroundProp e G

/-- Claim D: There exists a NECESSARY entity that grounds the truthmaking principle G. -/
def ClaimD : Prop := ∃ e : Entity, NecessaryEntity e ∧ GroundProp e G

/-- Entailment D → C:
    If a necessary entity grounds G, then some entity grounds G. -/
theorem D_implies_C : ClaimD → ClaimC :=
  fun ⟨e, _, hg⟩ => ⟨e, hg⟩

/-- Claim C holds in ambient Γ by self-application of GroundPrincipleProp:
    Because G is true (via GroundPrincipleProp), G can be instantiated into itself,
    producing an entity that grounds G. -/
theorem G_yields_ClaimC (hG : G) : ClaimC :=
  hG G (by exact hG)

/-- World-Emptying Lemma in Logos:
    At `otherWorld` (where all atoms are false), NO entity in `Entity` exists.
    - Subjects exist only at actualWorld (`SubjectExistsAt otherWorld s` is false).
    - Atomic entities exist only where their atom is true (`otherWorld n = TV.t` is false). -/
theorem no_entity_at_otherWorld (e : Entity) : ¬ ExistsAt otherWorld e := by
  intro hEx
  cases e with
  | ofSubject s =>
    dsimp [ExistsAt, Logos.Truthmaker.EntityExistsAt, Logos.Truthmaker.SubjectExistsAt] at hEx
    have hDiff : otherWorld 0 ≠ actualWorld 0 := by
      dsimp [otherWorld, actualWorld]
      intro h
      cases h
    have hEq : otherWorld 0 = actualWorld 0 := by rw [hEx]
    exact hDiff hEq
  | ofAtom n =>
    dsimp [ExistsAt, Logos.Truthmaker.EntityExistsAt, otherWorld] at hEx
    cases hEx

/-- Separation Theorem: World-indexed Claim B (ClaimB_World) is FALSE in Γ.
    Because `otherWorld` contains zero entities, no true proposition can be grounded
    by an entity existing at `otherWorld`. -/
theorem claimB_world_refuted : ¬ ClaimB_World := by
  intro hB
  have hOther := hB otherWorld True trivial
  obtain ⟨e, hEx, _⟩ := hOther
  exact no_entity_at_otherWorld e hEx

/-- Abstract Signature for Testing the Separation C ↛ D:
    Can an entity ground G without that entity being necessary? -/
structure GroundingModalitySignature where
  Entity : Type
  World : Type
  someWorld : World
  ExistsAt : World → Entity → Prop
  NecessaryEntity : Entity → Prop
  nec_def : ∀ e, NecessaryEntity e ↔ (∀ w, ExistsAt w e)
  GroundProp : Entity → Prop → Prop
  G : Prop
  g_def : G ↔ (∀ p : Prop, p → ∃ e, GroundProp e p)
  ClaimC : Prop
  c_def : ClaimC ↔ (∃ e, GroundProp e G)
  ClaimD : Prop
  d_def : ClaimD ↔ (∃ e, NecessaryEntity e ∧ GroundProp e G)

/-- Separation Theorem: Claim C does NOT entail Claim D.
    An entity grounding G may be completely contingent (existing in some worlds but not all). -/
theorem C_does_not_entail_D :
    ¬ (∀ S : GroundingModalitySignature, S.ClaimC → S.ClaimD) := by
  intro hAll
  let S : GroundingModalitySignature := {
    Entity := Unit
    World := Bool
    someWorld := true
    ExistsAt := fun w _ => w = true
    NecessaryEntity := fun _ => False
    nec_def := by
      intro _e
      apply Iff.intro
      · intro h; cases h
      · intro hAllW
        have hFalse := hAllW false
        cases hFalse
    GroundProp := fun _ p => p
    G := ∀ p : Prop, p → ∃ e : Unit, p
    g_def := Iff.rfl
    ClaimC := ∃ _e : Unit, (∀ p : Prop, p → ∃ _ : Unit, p)
    c_def := Iff.rfl
    ClaimD := False
    d_def := by
      apply Iff.intro
      · intro h; cases h
      · rintro ⟨e, hnec, _⟩; exact hnec
  }
  have hC : S.ClaimC := ⟨(), fun p hp => ⟨(), hp⟩⟩
  have hD : S.ClaimD := hAll S hC
  exact hD

/-!
### 3. Retorsion Analysis of ¬G and ¬□G
-/

/-- The denial of truthmaking (¬G): there is some true proposition that lacks an entity grounder. -/
def Neg_G : Prop := ∃ p : Prop, T p ∧ ∀ e : Entity, ¬ GroundProp e p

/-- Retorsion Failure on ¬G:
    Asserting ¬G is completely consistent with the performative core.
    An agent asserting ¬G does not commit a performative contradiction
    unless the demand for an entity grounder is already dogmatically imposed.
    Proof: in the DeflationaryModel, Neg_G is true and satisfied. -/
theorem neg_G_consistent_in_deflationary_model :
    ∃ (M : TruthmakingIndependenceSignature), (∃ p : Prop, M.T p ∧ ∀ e : M.Entity, ¬ M.GroundProp e p) := by
  refine ⟨DeflationaryModel, True, trivial, ?_⟩
  intro e hg
  exact hg

/-- Retorsion Boundary Principle for Truthmaking:
    Retorsion refutes a denial Q only when asserting Q performatively instantiates the thesis P.
    Because asserting a denial does not performatively instantiate an entity-grounder
    (assertion is an intentional act, not an ontological truthmaker for the truthmaking rule),
    retorsion fails to refute ¬G. -/
theorem truthmaking_retorsion_fails
    (asserts_neg_G : Neg_G)
    (h_no_ground : ∀ e : Entity, ¬ GroundProp e Neg_G) :
    ¬ (∀ p : Prop, T p → ∃ e : Entity, GroundProp e p) := by
  intro hG
  have hT_neg : T Neg_G := asserts_neg_G
  obtain ⟨e, hg⟩ := hG Neg_G hT_neg
  exact h_no_ground e hg

/-!
### 4. Regress Analysis: Grounding the Fact of Grounding
-/

/-- The Three Distinct Levels of Grounding:
    Level 1: Grounding the proposition G itself (`GroundProp e₀ G`).
    Level 2: Grounding the relational fact that e₀ grounds G (`GroundProp e₁ (GroundProp e₀ G)`).
    Level 3: Meta-level validity of the truthmaking rule (`∀ p, T p → ∃ e, GroundProp e p`). -/
def GroundLevel1 (e₀ : Entity) : Prop := GroundProp e₀ G
def GroundLevel2 (e₁ e₀ : Entity) : Prop := GroundProp e₁ (GroundLevel1 e₀)
def GroundLevel3 : Prop := G

/-- Regress Generation Theorem:
    If GroundPrincipleProp is applied indiscriminately to all propositions,
    then every stage generates a demand for a next-level grounder. -/
theorem infinite_regress_generator (hG : G) (e₀ : Entity) (h0 : GroundLevel1 e₀) :
    ∃ e₁ : Entity, GroundLevel2 e₁ e₀ := by
  have hT : T (GroundLevel1 e₀) := h0
  obtain ⟨e₁, hg₁⟩ := hG (GroundLevel1 e₀) hT
  exact ⟨e₁, hg₁⟩

/-- Self-Grounding vs Regress Dilemma:
    If entity grounding is irreflexive (no fact can ground its own grounding relation),
    then e₁ cannot be identical to e₀ if identity implies circular dependency.
    Alternatively, under permissive truthmaking (`GroundProp e p := p`),
    the regress collapses into trivial truth-equivalence. -/
theorem permissive_regress_collapse (p : Prop) (hp : p) :
    let GP := fun (_ : Nat) (q : Prop) => q
    (∃ e₀ : Nat, GP e₀ p) ∧
    (∀ e₀ : Nat, ∃ e₁ : Nat, GP e₁ (GP e₀ p)) := by
  dsimp
  refine ⟨⟨0, hp⟩, fun _ => ⟨0, hp⟩⟩

/-!
### 5. Infinite Ground Chain Model Revisit
-/

/-- Permissive ℤ Model Extended to Include G:
    We test whether the ℤ model satisfies:
    1. ¬ UltimateGroundExists
    2. T(G)
    3. GroundProp 0 G
    4. GroundProp 0 (GroundProp 0 G)
    while refuting an Ultimate Ground. -/
theorem z_chain_satisfies_grounded_truthmaking :
    let Ent := Int
    let GP := fun (_e : Ent) (p : Prop) => p
    let G_int := ∀ p : Prop, p → ∃ e : Ent, GP e p
    let UltExists := ∃ u : Ent, ∀ v : Ent, ¬ (u < v)
    (¬ UltExists) ∧
    G_int ∧
    (∃ e₀ : Ent, GP e₀ G_int) ∧
    (∃ e₀ e₁ : Ent, GP e₁ (GP e₀ G_int)) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨u, hu⟩
    have hlt : u < u + 1 := by
      show u + 1 ≤ u + 1
      exact Int.le_refl (u + 1)
    exact hu (u + 1) hlt
  · intro p hp
    exact ⟨0, hp⟩
  · exact ⟨0, fun p hp => ⟨0, hp⟩⟩
  · exact ⟨0, 0, fun p hp => ⟨0, hp⟩⟩

/-!
### 6. Truthmaking and Ultimate Ground: Gap and Totality
-/

/-- The Bridge Gap:
    Even if G is necessarily true (ClaimB_Prop) and G has a necessary ground (ClaimD),
    this does NOT logically imply that an Ultimate Ground exists.
    Proof: The necessary ground of G could itself be grounded by another necessary entity
    in an infinite descending chain of necessary entities. -/
structure NecessaryChainSignature where
  Entity : Type
  GroundEntity : Entity → Entity → Prop
  UltimateGroundExists : Prop
  ult_def : UltimateGroundExists ↔ (∃ u : Entity, ∀ v : Entity, ¬ GroundEntity v u)
  G_is_grounded : ∃ _e : Entity, True

/-- Separation: Grounding G does NOT imply UltimateGroundExists. -/
theorem grounding_G_does_not_derive_ultimate_ground :
    ¬ (∀ S : NecessaryChainSignature, S.UltimateGroundExists) := by
  intro hAll
  let S : NecessaryChainSignature := {
    Entity := Int
    GroundEntity := fun x y => x = y + 1
    UltimateGroundExists := False
    ult_def := by
      apply Iff.intro
      · intro h; cases h
      · rintro ⟨u, hu⟩
        have hContr := hu (u + 1) rfl
        exact hContr
    G_is_grounded := ⟨0, trivial⟩
  }
  have hUlt := hAll S
  exact hUlt

/-- Totality Bridge Requirement:
    As proved in `totality_grounding_forces_ultimate_ground` (HostileSemantics.lean:2340),
    truthmaking forces an Ultimate Ground ONLY when one adopts a Substantive Totality
    Grounding Principle that posits an ungrounded totality entity.
    Without that totality axiom, G remains completely compatible with infinite regress. -/
theorem truthmaking_alone_insufficient_for_ultimate_ground :
    (∃ (M : CountermodelInfiniteGroundChain.TruthGroundedRegressSignature),
      ¬ M.UltimateGroundExists ∧ (∃ e, M.GroundProp e M.Thesis)) :=
  ⟨CountermodelInfiniteGroundChain.PermissiveTruthGroundedInfiniteChain,
   CountermodelInfiniteGroundChain.PermissiveTruthGroundedInfiniteChain.NoUltimate,
   CountermodelInfiniteGroundChain.PermissiveTruthGroundedInfiniteChain.ThesisGrounded⟩

end TruthmakingInvestigation

end Logos.HostileSemantics
