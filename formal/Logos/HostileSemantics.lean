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
   - Act does not imply FreeWill
   - Content does not imply Personhood
6. Semantic attacks on uniform grounding (C18), ultimate ground (C79/C89),
   personal ground (T8), and love (T13/T14).
7. Semantic attack on the necessity lift (batches esse-est-agere / lift-necessário):
   subject-persistence (`NecessarySubject` in the general signature) does not
   entail entity-necessity (`NecessaryEntity`) by logic alone — the lift
   `Modal.subject_nec_entity_nec` (C91) is definitional, not a logical law
   (`CountermodelSubjectNecessityNotEntityNecessity`).
-/

import Logos.Core

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

/-- Separation Theorem 1: Act does not logically imply Personhood. -/
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

/-- Separation Theorem 3: Act and choice do not logically imply Free Will. -/
theorem not_entails_freewill :
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

/- Hostile Countermodel 2: A subject of an act that is NOT a person.
   Shows that if Person is an uninterpreted substantive predicate, Subject does not logically entail Person. -/
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

namespace CountermodelNoFreeWill
def S : Type := Unit
def A : S → Prop → Prop := fun _ _ => True
def FreeWill : S → Prop → Prop := fun _ _ => False

theorem act_occurs : ∃ s : S, ∃ p : Prop, A s p := ⟨(), True, trivial⟩
theorem no_free_will : ¬ ∃ s : S, ∃ p : Prop, FreeWill s p := fun ⟨_, _, hfw⟩ => hfw
theorem act_does_not_imply_freewill :
    (∃ s : S, ∃ p : Prop, A s p) ∧ ¬ (∃ s : S, ∃ p : Prop, FreeWill s p) :=
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
