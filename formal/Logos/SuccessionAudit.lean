/-
# Logos.SuccessionAudit — what `NotInSuccession` actually says, and what it does not

This module is the answer to an objection raised on 2026-09-28:

> *"The ground Initiates is refuted because there's a mistake in the proof."*

The object was `the_ground_not_in_succession` (`NecessityEternity.lean:196-198`), the fact on which
the immutability headline and C217 rest. The verdict is that the **objection is right and the
mistake is real — but it is not in the kernel term.** That term is perfectly sound, which is exactly
why it survived every audit. The proof binds the initiation conjunct and throws it away:

```lean
theorem the_ground_not_in_succession : NotInSuccession Entity.ofGround := by
  rintro ⟨s, σ, σ', p, ⟨hEq, _h⟩⟩        -- _h : Initiates s σ σ' p is never used
  exact Entity.noConfusion hEq            -- consumes only ofGround = ofSubject s
```

So the ground's transition invariance is discharged by **constructor disjointness** and decides
nothing whatever about `Initiates`. Its content is `¬ ∃ s, ofGround = EntityOf s`, which is
`ofGround_ne_ofSubject` — already a theorem in the corpus twice over
(`FoundationalUnicity.lean:131`, `NecessityEternity.lean:160`).

Two consequences follow, and this module machine-checks both of them:

1. **The field cannot tell the ground from an atom.** Every atom is equally far from being a subject
   correlate, so every atom satisfies `NotInSuccession` too. This is the *identical* asymmetry C321
   found in `capacity_invariance` — `capacity_invariance_holds_for_every_entity`
   (`DivineImmutability.lean:161`) — on the other field of the same structure, and it was not on
   record. `DivineImmutability.lean:153-154` calls `TransitionInvariance` "the real predicate"; it is
   real in general (C460 below shows it can fail) but it carries no information about the ground.
2. **The ground's non-agency is unstatable, not refuted.** Γ has no entity-level agency relation at
   all: `Initiates : Subject → State → State → Prop → Prop`, and the only way an `Entity` reaches it
   is `EntityOf s = Entity.ofSubject s`. "The ground does not initiate" therefore has no denotation —
   the same wall F16 hit with `EntityMeansAt`. The claim is recorded as C462 (`BLOCKED`) in the
   ledger with the exact missing statement, and the vocabulary that would state it is C463
   (`Produces : Entity → World → Form → Prop`).

**Disclosure, not demotion.** `ofGround_divine_immutability` and C217 keep their status and their
footprints; no badge moves. What changes is the *reading* of one field of one structure — the
F16 precedent (`DivineImmutability.lean:142-165`), applied to the sibling it left unexamined.

**What the sentence "the fact Γ exists means someone initiates" costs.** It is adjudicated here too,
at the end of the module (C468), and the honest answer is: the existence half is free (C350
`contingent_realm_obtains`, `PROVEN`, `{CL, NecessarySubjectKind, Subject}`) and the whole remaining
price is the performative datum C454, because the consequent of the implication is already
unconditional (C455). A bridge axiom "existence implies initiation" would therefore be *strictly
dominated*: its conclusion is already derived, so it would add a priced axiom and no theorems. It is
refused on ledger grounds, not on theological ones.
-/

import Logos.Core
import Logos.Semantics
import Logos.Entity
import Logos.Agency
import Logos.NecessityEternity
import Logos.CosmicExistence

namespace Logos.SuccessionAudit

open Logos.Semantics (World)
open Logos.Entity (Entity EntityOf ExistsAt)
open Logos.Agency (Subject State Initiates some_subject_initiates)
open Logos.NecessityEternity (NotInSuccession the_ground_not_in_succession)
open Logos.CosmicExistence (ContingentRealmObtains)

-- ===========================================================================
-- Part I: The content of `NotInSuccession`, extracted
-- ===========================================================================

/-- A subject-correlate-free entity is outside succession whatever its relation to initiation may be.

 C458 — the extraction. `NotInSuccession e` is `¬ ∃ s σ σ' p, e = EntityOf s ∧ Initiates s σ σ' p`
 (`NecessityEternity.lean:102-104`), and this row proves that the *first* conjunct alone suffices.
 So the predicate is, in general, a statement about **which constructor an entity is** — a type fact
 — and only incidentally about initiation.

 This is the lemma `the_ground_not_in_succession` actually uses, promoted to a theorem so that it can
 be read: the ground's transition invariance follows from `ofGround_is_not_a_subject_correlate`
 (below), and the `Initiates` conjunct of the definition is inert in that instance.

 Not a claim that the ground acts. It is the *absence* of a claim, made explicit.

 Footprint: `{Initiates, State, Subject}` — the *statement* mentions `Initiates` and `State`, though
 the proof uses no axiom; the same reason `FoundationalUnicity.groundsEntity_reflexive` is not `{}`
 (see the `Entity`-layer floor). -/
theorem non_correlate_is_outside_succession {e : Entity}
    (h : ¬ ∃ s : Subject, e = EntityOf s) : NotInSuccession e := by
  intro hEx
  obtain ⟨s, _σ, _σ', _p, hEq, _hInit⟩ := hEx
  exact h ⟨s, hEq⟩

/-- The ground is the correlate of no subject — which is the whole of its transition invariance.

 The content of `the_ground_not_in_succession`, stated so that it can be read directly. It is
 `ofGround_ne_ofSubject` in existential form, and it is the reason the immutability headline's
 `transition_invariance` field is satisfied.

 Footprint: `{Subject}` — the sort is in the statement; the proof is a single `noConfusion`. -/
theorem ofGround_is_not_a_subject_correlate :
    ¬ ∃ s : Subject, Entity.ofGround = EntityOf s := by
  rintro ⟨s, hEq⟩
  exact Entity.noConfusion hEq

/-- An atom is the correlate of no subject either.

 The same argument one constructor over, and the reason C459 below holds. `Entity.ofAtom` and
 `Entity.ofGround` are disjoint from `Entity.ofSubject` in the same way; nothing about the atom's
 relation to initiation is used or decided.

 Footprint: `{Subject}` — the sort is in the statement; the proof is a single `nomatch`. -/
theorem ofAtom_is_not_a_subject_correlate (n : Nat) :
    ¬ ∃ s : Subject, Entity.ofAtom n = EntityOf s := by
  rintro ⟨s, hEq⟩
  exact nomatch hEq

-- ===========================================================================
-- Part II: C459 — the field does not separate the ground from an atom
-- ===========================================================================

/-- Transition invariance holds of the ground and of every atom alike, so it cannot characterise the ground.

 C459 — **the asymmetry, and C321's twin.** `DivineImmutability.capacity_invariance` is satisfied by
 every entity whatever (`DivineImmutability.lean:161`, C321); this row records that
 `transition_invariance` — the field `DivineImmutability.lean:153-154` calls "the real predicate" —
 is satisfied by every **non-subject** entity, ground and atoms together, for the same structural
 reason: none of them is a subject correlate.

 So the immutability headline's fourth field carries no ground-specific weight. This is DISCLOSURE,
 NOT DEMOTION: `ofGround_divine_immutability` stays `PROVEN` with footprint
 `{Initiates, Means, NecessarySubjectKind, State, Subject}`, and C217
 (`ofGround_no_transition_potency`, built on this field) stays `PROVEN` as well. What is withdrawn is
 the *reading* that the field says the ground is inert with respect to becoming. The footprint is
 C458's: the statement reaches `Initiates` and `State` through the very field it is about.

 Footprint: `{Initiates, State, Subject}`. -/
theorem the_ground_and_every_atom_are_outside_succession :
    NotInSuccession Entity.ofGround ∧ ∀ n : Nat, NotInSuccession (Entity.ofAtom n) :=
  ⟨non_correlate_is_outside_succession ofGround_is_not_a_subject_correlate,
   fun n => non_correlate_is_outside_succession (ofAtom_is_not_a_subject_correlate n)⟩

-- ===========================================================================
-- Part III: C460 — the non-triviality countermodel the ledger misattributed to C197
-- ===========================================================================

/-- Not every entity is outside succession: the correlate of an initiating subject is not.

 C460 — the non-triviality result, **for the field itself**. The F16 gloss and `T22.txt:92` both
 claimed that every sibling field of `DivineImmutability` has a `{}` non-triviality countermodel "on
 record (C197 …)"; C197 is `DivineImmutability.lean`'s modal-invariance countermodel
 (`GAPMAP.md:2628`) and says nothing about `NotInSuccession`. This row supplies the missing instance,
 and the live sort makes it free: take the correlate of the subject C455 exhibits.

 So the correction is two-sided, and both halves matter. The field is **not** vacuous in general —
 it can fail, and C460 shows exactly when (C459: it holds for the ground and the atoms, so what
 discriminates is being the correlate of a subject who initiates). What is vacuous is the *ground's
 instance* of it, which is C459. C197's scope is corrected in the ledger to modal and stage
 invariance.

 Priced on the performative datum (`Tag: TRANS`, C454) — the witness subject exists because C455
 says so. The honest alternative, a free-signature countermodel, is C461's neighbour in
 `Logos.SuccessionCountermodel`; this row is kept in the live signature because the live sort supplies
 the witness for nothing.

 Footprint: `{performative_act_datum, Initiates, Means, State, Subject}`. -/
theorem someone_is_in_succession : ¬ ∀ e : Entity, NotInSuccession e := by
  intro hAll
  obtain ⟨s, p, w, w', hInit⟩ := some_subject_initiates
  exact hAll (EntityOf s) ⟨s, w, w', p, rfl, hInit⟩

/-- The bridge of the author's sentence, discharged: given that Γ exists, someone initiates.

 C468 — *"The fact Γ exists means Someone Initiates"* (2026-09-28), in the ledger. The implication is
 `ContingentRealmObtains → ∃ s p σ σ' p, Initiates s σ σ' p`, and the proof is the consequent alone:
 the hypothesis is bound, named for the record, and unused.

 **The premise does no work, and the row says so.** The consequent is C455, unconditional, so any
 antecedent whatsoever would yield this row — the antecedent is a *phylogenetic* remark about why the
 author expects the sentence to be true, not a premise. Decomposed honestly:

 * *something exists* — C350 `contingent_realm_obtains`, `PROVEN`, `{CL, NecessarySubjectKind, Subject}`: free;
 * *someone means* — `Plurality.cogito_from_T12` (`Plurality.lean:220`), from the axiom-free
   `Core.rightWrongDistinction`: free;
 * *someone initiates* — C455: the performative datum C454, the only price in the sentence.

 **Why no axiom is added for the implication.** A bridge `existence → initiation` would be *strictly
 dominated*: its conclusion is already a theorem, so it would raise the registry and add no theorems
 to Γ. Refused on ledger grounds. The non-redundant strengthening — the *ground* as the initiator —
 is C462 (`BLOCKED`, unstatable) and, in its Thomistic form, C463/C465/C467.

 **The antecedent is `Nonempty ContingentRealm`, not the `def` `ContingentRealmObtains`.** The two are
 definitionally the same proposition (`ContingentRealmObtains := Nonempty ContingentRealm`,
 `CosmicExistence.lean:247`), but stating the structure is what keeps the row free of a
 `def`-used-as-premise: `scripts/audit_stipulated_defs.py` treats a bare `Prop` `def` in premise
 position as an assumption invisible to `#print axioms`, and it needs no invisible price here — the
 house style for an existential premise is the explicit structure, as in C367's hypothesis.

Footprint: `{performative_act_datum, Initiates, Means, State, Subject}` — **exactly C455's cone.**
 Worth recording: with the `def` antecedent this row carried `NecessarySubjectKind` as the
 fingerprint of the existence half, and stating the structure explicitly removed it. The existence
 half of the author's sentence now leaves *no* trace in the footprint, which is the machine-checked
 form of \"that side is free\" — the premise is inert, and now provably costless too.

 -/
theorem existence_implies_someone_initiates (_hExistence : Nonempty ContingentRealm) :
    ∃ s : Subject, ∃ p : Prop, ∃ w w' : State, Initiates s w w' p :=
  some_subject_initiates

#print axioms non_correlate_is_outside_succession
#print axioms ofGround_is_not_a_subject_correlate
#print axioms ofAtom_is_not_a_subject_correlate
#print axioms the_ground_and_every_atom_are_outside_succession
#print axioms someone_is_in_succession
#print axioms existence_implies_someone_initiates

end Logos.SuccessionAudit
