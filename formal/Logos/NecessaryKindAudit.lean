/-
# Logos.NecessaryKindAudit — the second necessary being, and the price of the kind vocabulary

`Agency.lean:62` declares `NecessarySubjectKind : Subject → Prop` (`Tag: VOCAB`) and, for a long
time, no theorem in the corpus mentioned it in theorem position at all. It is nonetheless
load-bearing everywhere: `Entity.SubjectExistsAt w s := NecessarySubjectKind s ∨ w = actualWorld`,
so a subject of the necessary kind is **world-rigid by construction** — its entity-correlate
exists in every world, hence is a `NecessaryEntity`.

The kernel already interprets the badge (`Plurality.kinds_are_the_modal_partition`:
`NecessarySubjectKind s ↔ NecessarySubject s`). This module asks the question the interpretation
does not answer: **what does a second necessary being do to the theory?** `Plurality` prices the
*inhabitation* of the necessary kind by the META bridge `necessaryPersonalSubjectExists`
(`∃ s, NecessarySubjectKind s ∧ Person s`). Combined with `ofGround_ne_ofSubject` (a subject's
correlate is provably not the ground), that bridge yields a result no characteristic row in the
corpus records:

- **the necessary being is not unique** — Γ admits an entity that is necessary and provably not
  the ground, so "every property of God is a property of every necessary being" is **refuted**,
  not merely unproved. This is the `ofGround_not_truth_tracking` genre (§14), applied to *ST* I
  q.19 a.4. It is a refutation of a *reading*, resting on one `Tag: META` bridge: reject
  `necessaryPersonalSubjectExists` and the refutation and the grade statement both disappear,
  leaving the question open.
- **necessity is the one characteristic that does not pick the ground out.** The six
  discriminating characteristics each satisfy `∀ e, P e → e = Entity.ofGround` (C439,
  C442–C445, C307 — collected by C446); `NecessaryEntity` does not, and cannot while the
  necessary kind is inhabited: C495 proves `NecessaryEntity` cannot be C446's seventh
  conjunct under that inhabitation.

It also gives the **profile of the second necessary being**: it is necessary and *gaplessly
operative* (it ties the ground there — the reason C443's `universal_ground` field, not
`gapless_operate` alone, is what excludes it from full omnipotence), yet it provably lacks
transcendence, maximal capacity, and pure actuality. The last two are the `SemanticFinitude`
price C445 already pays; nothing new is charged here.

Section 6 (added 2026-09-29) closes the audit **positively**: C515 rules out the necessary atom,
C516 proves the necessary realm is *exhausted* by the ground and the necessary-kind correlates,
and C517 makes the two disjuncts exclusive — the module's final statement is a two-genera
partition, not only a refutation. Those three rows are `PROVEN` and vocabulary-only: the audit
needed no inhabitation axiom to say what the necessary realm *is*, only to say it is *populated*.

**0 new axioms.** The register stays 32. This module only *reads* the kind vocabulary and one
already-declared META bridge; it declares no axioms — its eleven theorems are the only additions.
-/

import Logos.Core
import Logos.Semantics
import Logos.Entity
import Logos.Agency
import Logos.Necessity
import Logos.RecoveredOntologicalGround
import Logos.Modal
import Logos.Plurality
import Logos.NecessityEternity
import Logos.FoundationalUnicity
import Logos.DivineSimplicity
import Logos.FoundationalOmnipresence
import Logos.SemanticFinitude
import Logos.DivinePureActuality
import Logos.DivineOmnipotence
import Logos.TheologicalModalHardening
import Logos.LovesAsGround

namespace Logos.NecessaryKindAudit

open Logos.Semantics (World)
open Logos.Necessity (WProp)
open Logos.Entity (Entity EntityOf ExistsAt actualWorld)
open Logos.Agency (Subject Means NecessarySubjectKind)
open Logos.RecoveredOntologicalGround (EntityMeans)
open Logos.Modal (NecessaryEntity)
open Logos.Plurality (NecessarySubject necessaryPersonalSubjectExists)
open Logos.FoundationalUnicity (ofGround_ne_ofSubject)
open Logos.DivineSimplicity (TranscendentGround)
open Logos.FoundationalOmnipresence (MaximalCapacity)
open Logos.SemanticFinitude (SemanticFinitude)
open Logos.DivinePureActuality (DivinePureActuality discriminating_subject_fails_pure_actuality)
open Logos.DivineOmnipotence (GaplessOperate OperatesAt PossibleAt)
open Logos.TheologicalModalHardening (UniversalFrame necessary_not_contingent)
open Logos.LovesAsGround (an_atom_is_contingent)
open Logos.Plurality (kinds_are_the_modal_partition)

-- ============================================================================
-- Section 1 — The lift: a necessary-kind subject's correlate is a necessary entity
-- ============================================================================

/-- **The necessity lift, made explicit.** A subject of the necessary kind is present in every
    world (left disjunct of `SubjectExistsAt`), so its entity-correlate is a `NecessaryEntity`.
    The kernel already contains this as `Plurality.necessaryKindSubject_is_necessary`; it is
    restated here against `NecessaryEntity` (rather than the subject-level `NecessarySubject`)
    so the module reads against one necessity predicate. `Tag: VOCAB` throughout — this is the
    kind distinction being read, not a new claim about it.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem necessary_kind_correlate_is_necessary (s : Subject)
    (hKind : NecessarySubjectKind s) : NecessaryEntity (EntityOf s) := by
  intro w
  exact Or.inl hKind

-- ============================================================================
-- Section 2 — The grade statement: necessity does not single out the ground
-- ============================================================================

/-- **Necessity is not sole-bearer of the ground (C495).** No other characteristic in the corpus
    has this shape: `∀ e, NecessaryEntity e → e = Entity.ofGround` is **false**, because the META
    bridge `necessaryPersonalSubjectExists` inhabits the necessary kind and
    `ofGround_ne_ofSubject` denies that its correlate is the ground. So among the footprint
    characteristics, *necessity is the one that does not pick the ground out* — the honest
    counterpart of the six discriminating results (C439, C442–C445, C307 — collected by C446).
    It proves that `NecessaryEntity` cannot be C446's seventh conjunct while the necessary kind is
    inhabited.

    This is `PROVEN↑` under the META bridge, not a refutation of Γ: it says the ground is not the
    *only* necessary being, not that the ground fails to be necessary (`ofGround_necessary`
    stands). Reject `necessaryPersonalSubjectExists` and this row returns to open.
    Contrast with C489/C490: those are free-signature *countermodels* (`{}`) separating a
    per-kind-subject form from the act-datum without touching Γ, while this row is a *proof inside
    Γ* — the negation is witnessed by the bridge-inhabited necessary kind, so its status is
    `PROVEN↑`, not separation.
    Footprint: `{Means, NecessarySubjectKind, Subject, Will, subjectWill,
      necessaryPersonalSubjectExists}`. -/
theorem necessity_is_not_sole_bearer_of_the_ground :
    ¬ (∀ e : Entity, NecessaryEntity e → e = Entity.ofGround) := by
  intro hSole
  obtain ⟨s, hKind, _hPerson⟩ := necessaryPersonalSubjectExists
  have hNec : NecessaryEntity (EntityOf s) := necessary_kind_correlate_is_necessary s hKind
  have hEq := hSole (EntityOf s) hNec
  exact ofGround_ne_ofSubject s hEq

/-- **The ground is not the only necessary being (C494)** — the refutation of *ST* I q.19 a.4 in
    its extensional reading. The claim that every property of God is shared by every necessary
    being is false: taking `Q := fun e => e = Entity.ofGround`, a necessary-kind subject's
    correlate is a counterexample. This is the `ofGround_not_truth_tracking` genre applied to
    *ST* I q.19 a.4 — a classical reading **refuted**, not merely unproved.

    `PROVEN↑` under the META bridge. It is a refutation of a *reading*, and it rests on one
    declared `Tag: META` inhabitation axiom; it is not a doctrine and not a consistency claim.
    Footprint: `{Means, NecessarySubjectKind, Subject, Will, subjectWill,
      necessaryPersonalSubjectExists}`. -/
theorem the_ground_is_not_the_only_necessary_being :
    ¬ (∀ Q : Entity → Prop, Q Entity.ofGround →
        ∀ e : Entity, NecessaryEntity e → Q e) := by
  intro hShare
  obtain ⟨s, hKind, _hPerson⟩ := necessaryPersonalSubjectExists
  have hNec : NecessaryEntity (EntityOf s) := necessary_kind_correlate_is_necessary s hKind
  have hQ := hShare (fun e => e = Entity.ofGround) rfl (EntityOf s) hNec
  exact ofGround_ne_ofSubject s hQ

-- ============================================================================
-- Section 3 — What the second necessary being lacks
-- ============================================================================

/-- **A necessary-kind subject is not transcendent (C496).** Free in the sense that requires no
    new axiom — `TranscendentGround` is *defined* as "neither an atom nor any subject-correlate"
    (`DivineSimplicity.lean:145-146`), so denying the necessary-kind subject that property is a
    definitional contradiction. The footprint is exactly the two vocabulary axioms the statement
    itself mentions (`NecessarySubjectKind`, `Subject`) — nothing larger. This is the control case:
    it shows the exclusion is not uniformly hard, and that where it *is* paid (below) the price is
    visible.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem necessary_kind_subject_is_not_transcendent (s : Subject)
    (_hKind : NecessarySubjectKind s) :
    ¬ TranscendentGround (EntityOf s) := by
  intro hT
  exact hT.2 s rfl

/-- **A necessary-kind subject is not a maximal-capacity entity (F15).** `MaximalCapacity` is
    `∀ p, EntityMeans e p`; for a subject that is `∀ p, Means s p`, exactly what `SemanticFinitude`
    denies. This is the same `SemanticFinitude` price C445 and C444 pay for the same exclusion;
    nothing new is charged. Footprint: the `SemanticFinitude` bridge plus the vocabulary the
    statement mentions (`Means`, `NecessarySubjectKind`, `Subject`).
    Footprint: `{Means, NecessarySubjectKind, SemanticFinitude, Subject}`. -/
theorem necessary_kind_subject_lacks_maximal_capacity (s : Subject)
    (_hKind : NecessarySubjectKind s) :
    ¬ MaximalCapacity (EntityOf s) := by
  obtain ⟨p, hp⟩ := SemanticFinitude s
  intro hMC
  exact hp (hMC p)

/-- **A necessary-kind subject is not pure actuality (F15).** By the existing
    `discriminating_subject_fails_pure_actuality`: a subject with any content it does not mean has
    passive intentional potency, and the whole necessary kind is subject to `SemanticFinitude`.
    Footprint is shared with that theorem: `SemanticFinitude` plus the four vocabulary axioms
    `DivinePureActuality` itself carries (`Initiates`, `Means`, `State`, `Subject`) and the two of
    this statement (`NecessarySubjectKind`).
    Footprint: `{Initiates, Means, NecessarySubjectKind, State, Subject, SemanticFinitude}`. -/
theorem necessary_kind_subject_fails_pure_actuality (s : Subject)
    (_hKind : NecessarySubjectKind s) :
    ¬ DivinePureActuality (EntityOf s) :=
  discriminating_subject_fails_pure_actuality s (SemanticFinitude s)

-- ============================================================================
-- Section 4 — What the second necessary being has: the operativeness tie
-- ============================================================================

/-- **A necessary-kind subject IS a gapless operator (F15-free, and the honest half of C443).**
    Whoever is present in every world operates everything satisfiable. This is the *forward*
    direction of `DivineOmnipotence.gapless_operators_are_ground_or_necessary_kind` (which is the
    converse) and it is what makes the second necessary being *tie the ground* on operativeness.
    It is precisely why C443's `universal_ground` field — not `gapless_operate` alone — is what
    excludes the necessary-kind subject from full Foundational Omnipotence.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem necessary_kind_subject_is_gapless_operator (s : Subject)
    (hKind : NecessarySubjectKind s) :
    GaplessOperate (UniversalFrame World) OperatesAt (EntityOf s) := by
  intro w P hPoss
  obtain ⟨u, hRw, hPu⟩ := hPoss
  refine ⟨u, hRw, ?_⟩
  exact ⟨Or.inl hKind, hPu⟩

-- ============================================================================
-- Section 5 — The master: the profile of the second necessary being
-- ============================================================================

/-- **The profile of the second necessary being (C497).** For a subject of the necessary kind,
    its entity-correlate:

    - **has** `NecessaryEntity` and `GaplessOperate` — it ties the ground on operativeness;
    - **lacks** `TranscendentGround` (free), `MaximalCapacity` and `DivinePureActuality` (both
      `SemanticFinitude`).

    The combination is the batch's transferable statement: the necessary kind is a *near-ground*
    but is cut off from every discriminating characteristic except operativeness — and there it
    is not cut off at all, which is why the `universal_ground` field exists. The conjunction is a
    new statement about a second necessary being; its cells are the existing vocabulary results.
    Note that "second" is shorthand for "other": the theorem is universal over the kind
    (`∀ s, NecessarySubjectKind s → …`), so it describes *every* non-ground necessary subject's
    correlate, not one particular being.
    Footprint: `{Initiates, Means, NecessarySubjectKind, State, Subject, SemanticFinitude}`. -/
theorem the_second_necessary_being_profile (s : Subject)
    (hKind : NecessarySubjectKind s) :
    NecessaryEntity (EntityOf s) ∧
    GaplessOperate (UniversalFrame World) OperatesAt (EntityOf s) ∧
    ¬ TranscendentGround (EntityOf s) ∧
    ¬ MaximalCapacity (EntityOf s) ∧
    ¬ DivinePureActuality (EntityOf s) :=
  ⟨necessary_kind_correlate_is_necessary s hKind,
   necessary_kind_subject_is_gapless_operator s hKind,
   necessary_kind_subject_is_not_transcendent s hKind,
   necessary_kind_subject_lacks_maximal_capacity s hKind,
   necessary_kind_subject_fails_pure_actuality s hKind⟩

-- ============================================================================
-- Section 6 — The positive closure: the necessary realm has no third shape
-- ============================================================================

/-- **No atom is necessary (C515).** Atoms are contingent (C323, read from `LovesAsGround`) and
    the necessary is never contingent, so no atom — however many, whatever its number — is
    necessary. This is the atom case of the closure below, discharged once and named.
    The footprint is exactly the two vocabulary axioms the statement's own derivation reads,
    plus `propext` (inherited from C323's cone; see GAPMAP's `CL`/raw-grafia note).
    Footprint: `{NecessarySubjectKind, Subject, propext}`. -/
theorem no_necessary_atom (n : Nat) : ¬ NecessaryEntity (Entity.ofAtom n) :=
  fun hNec => necessary_not_contingent _ hNec (an_atom_is_contingent n)

/-- **The necessary is exhausted by the ground and the necessary-kind subjects (C516).**
    Everything necessary is either the ground or a necessary-kind subject's correlate: no
    necessary atom, no necessary matter, no third necessary shape. This is the **positive
    closure** of the audit — C495 showed the ground-only universal is *false*, C496/C497
    profiled the second necessary being, and this row says the second disjunct is not merely
    *a* second necessary being but *all* the rest of the necessary realm.

    Unconditional and free: `PROVEN`, no axiom, no hypothesis beyond `NecessaryEntity e`. The
    subject arm is the partition the kernel already interprets (C410, `.mpr` direction — the
    kernel documents `NecessarySubject s` and `NecessaryEntity (EntityOf s)` as the same
    proposition); the ground arm is `rfl`; the atom arm is C515. Cases analysis on the closed
    `Entity` inductive, the same idiom as C508 (whose row the author filed in the TRINITY
    lote as `C508`; the ids C515–C517 here are the NECESSARY follow-on).

    What it does **not** say: nothing about *who* the ground is, and nothing about inhabiting
    the necessary kind. The first disjunct is read as the ground whatever the reader takes the
    ground to be — a principle, or (per the author's position of 2026-09-29) a Trinity; the
    theorem forces neither reading. Contingent-kind inhabitation remains the open mirror and
    is untouched here.
    Footprint: `{NecessarySubjectKind, Subject, propext}`. -/
theorem necessary_exhaustion (e : Entity) (hNec : NecessaryEntity e) :
    e = Entity.ofGround ∨ ∃ s : Subject, NecessarySubjectKind s ∧ e = EntityOf s := by
  cases e with
  | ofSubject s =>
      exact Or.inr ⟨s, (kinds_are_the_modal_partition s).mpr hNec, rfl⟩
  | ofAtom n => exact False.elim (no_necessary_atom n hNec)
  | ofGround => exact Or.inl rfl

/-- **The necessary realm is the ground and the necessary kind, or nothing (C517).** C516 read
    as a shape statement: the two disjuncts are exclusive (`ofGround_ne_ofSubject`) and the
    ground is not itself a subject's correlate, so the closure is a genuine partition of the
    necessary realm into two genera rather than an overlapping cover. Exclusive, not covering
    twice: nothing is both the ground and a correlate, in either direction.
    Footprint: `{NecessarySubjectKind, Subject, propext}`. -/
theorem necessary_realm_is_two_genera :
    (∀ e : Entity, NecessaryEntity e → e = Entity.ofGround ∨
        (∃ s : Subject, NecessarySubjectKind s ∧ e = EntityOf s)) ∧
    (∀ e : Entity, NecessaryEntity e →
        (e = Entity.ofGround → ∀ s : Subject, e = EntityOf s → False) ∧
        (∀ s : Subject, NecessarySubjectKind s → e = EntityOf s → e ≠ Entity.ofGround)) := by
  refine ⟨necessary_exhaustion, ?_⟩
  intro e _hNec
  constructor
  · intro hGround s hEq
    exact ofGround_ne_ofSubject s (hEq.symm.trans hGround)
  · intro s _hKind hEq hGround
    exact ofGround_ne_ofSubject s (hEq.symm.trans hGround)

-- Axiom footprint audit
#print axioms necessary_kind_correlate_is_necessary
#print axioms necessity_is_not_sole_bearer_of_the_ground
#print axioms no_necessary_atom
#print axioms necessary_exhaustion
#print axioms necessary_realm_is_two_genera
#print axioms the_ground_is_not_the_only_necessary_being
#print axioms necessary_kind_subject_is_not_transcendent
#print axioms necessary_kind_subject_lacks_maximal_capacity
#print axioms necessary_kind_subject_fails_pure_actuality
#print axioms necessary_kind_subject_is_gapless_operator
#print axioms the_second_necessary_being_profile

end Logos.NecessaryKindAudit
