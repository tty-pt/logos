/-
# trinitarian-probe.lean — machine-checked basis for the personal-ground work (C567-C572)

Status: **audit artifact, NOT in the kernel.** Not in the `Logos` lean_lib, never imported,
never compiled by `lake build`. It exists so that every `{}` claim the plan rests on is
re-checkable by running the kernel rather than read off a transcript — the rule `AGENTS.md`
states for `goal_audit.json`, applied to the plan.

Run it (from `formal/`):

```sh
export PATH="$HOME/.elan/bin:$PATH"
cd formal && taskset -c 0-3 lake env lean ../investigations/trinitarian-probe.lean
```

Every `{}` below denotes **zero substantive axioms** — the plan's and the ledger's price unit,
which counts `SEM`/`META`/`TRANS` and not `VOCAB`. It does **not** mean literally axiom-free:
nothing quantified over a subject is, because `Subject` and `Means` are themselves declared
`Tag: VOCAB` axioms, so the machine-measured `#print axioms` line for every row here reads
`[Means, Subject]` (plus `NecessarySubjectKind` on the grounding rows) even when the plan's price
is `{}`. The two readings are reconciled by `scripts/gapmap_taxonomy.py --check`, which is the
authority on which tags are substantive; read the `#print axioms` output for the literal set and
the plan's §2 table for the price. Any `sorryAx` in the output is a failure. Expected output is
the `#print axioms` lines and nothing else.

Sections:
  P1  §3.4  the unrestricted meaning thesis is refutable at {}
  P2  §5.1  the ground is not a fourth chooser, at {}
  P3  §5.4  grounding-by-being: the ground sustains all being, at {}
  P4  §5.4  the two grounding routes, and the personal-ground conjunction, at {}
  P5  §4.2  the potency guard excludes the ground and the atoms, at {}
  P6  §4.4  the REJECTED `T p` arm trades infallibility for pure actuality (the reason §4.4
            is not in the plan) — recorded here so the rejection stays re-checkable

STATUS (S3, 2026-10-02): **P1–P5 are now kernel** — P2, P3 and P4 were promoted into
`formal/Logos/TrinitarianPersonalGround.lean` at S2 and P1 and P5 into
`formal/Logos/BoundedMeaning.lean` at S3, all with their footprints audited in
`formal/axiom_audit.json`, so this file is no longer their only check. P6 is filed as a finding
and is **not** adopted by the plan. The rows below are the standalone re-derivations, kept so
each remains checkable without importing `Logos.BoundedMeaning` (whose names would collide); the
kernel is authoritative for footprints, and `BoundedMeaning.lean` additionally proves
`guard_excludes_exactly_the_impersonal_cases`, which has no counterpart here. The plan's §2 table
is therefore still fully re-checkable here for the rows it lists.

Two declarations the plan names are **not** in this file and were never in it:
`Perichoretic` (plan §5.2) and `no_person_is_the_ground` (plan §5.3). Both are kernel, both
machine-checked there at `{}` (`{Means, Subject}` and `{Subject}` respectively), and the plan's
§5.3 sentence "All four are in the probe" is corrected accordingly.
-/

import Logos.Core
import Logos.Semantics
import Logos.Entity
import Logos.Agency
import Logos.Alternatives
import Logos.Choice
import Logos.RecoveredOntologicalGround
import Logos.AsieticChoice
import Logos.Person
import Logos.DivinePureActuality
import Logos.FoundationalOmnipresence
import Logos.DivineOmniscience

namespace Logos.TrinitarianProbe

open Logos.Core (T)
open Logos.Semantics (World)
open Logos.Entity (Entity EntityOf ExistsAt actualWorld)
open Logos.Agency (Subject Means)
open Logos.Alternatives (Incompatible)
open Logos.Choice (Chooses FreeWill)
open Logos.RecoveredOntologicalGround (EntityMeans OneEssence ActualEntity)
open Logos.AsieticChoice (TrueChoice Asiety)
open Logos.Person (Person)
open Logos.DivinePureActuality (PassiveIntentionalPotency)
open Logos.FoundationalUnicity (ofGround_ne_ofSubject)
open Logos.FoundationalOmnipresence (MaximalCapacity)
open Logos.DivineOmniscience (TruthTracking)
open Logos.DivinePureActuality (ofGround_no_intentional_potency)

/-! ## P1 · the unrestricted thesis is refutable at {} -/

/-- The ground's scope is total *as it stands today* (`EntityMeans Entity.ofGround p := True`),
    so the unrestricted thesis reaches `Entity.ofGround` and dies on injectivity. This is why
    the plan's thesis is the guarded one and why §4.4 is a rejected alternative rather than a
    step. Footprint: `{}`. -/
theorem unrestricted_meaning_thesis_is_refuted :
    ¬ (∀ e : Entity, ∀ p : Prop, EntityMeans e p → ∃ s : Subject, e = EntityOf s ∧ FreeWill s) := by
  intro h
  obtain ⟨s, hs, _⟩ := h Entity.ofGround True trivial
  exact ofGround_ne_ofSubject s hs.symm

#print axioms unrestricted_meaning_thesis_is_refuted

/-! ## P2 · the ground is not a fourth chooser, at {}

This is *doctrine*, not a defect. `Asiety e` witnesses a `Subject` with `e = EntityOf s`, so the
ground has no asiety. The one essence is not a fourth instance of choosing alongside the three;
its freedom is their freedom, shared rather than duplicated (`AsietyFreedomOfGround`, META).
-/

/-- The ground is not an asietic entity: no subject, so no true choice at the ground. This is
    the row the plan promotes from an accident of injectivity to a named doctrine row
    (*praeter hoc, quod unus est, tres sunt*). Footprint: `{}`. -/
theorem ground_is_not_a_fourth_chooser : ¬ Asiety Entity.ofGround := by
  intro h
  obtain ⟨s, _p, _q, hs, _⟩ := h
  exact ofGround_ne_ofSubject s hs.symm

#print axioms ground_is_not_a_fourth_chooser

/-- **The ground's scope does co-contain incompatible contents** — with the total arm it means
    every proposition, so it takes in both horns of every conflict. This is the result the
    checker forced, and it is the doctrine: *plenitude of scope is not freedom.* A rejected
    alternative in this plan asserted the ground "cannot co-mean incompatibles"; that is simply
    false against today's arm, and asserting it would have imported a claim nothing supports.
    Freedom in Γ is not bearing all content — it is `Asiety` (`P2`, first theorem), which
    requires being a `Subject`. Footprint: `{}`. -/
theorem ground_scope_does_contain_incompatibles :
    ∃ p q : Prop, EntityMeans Entity.ofGround p ∧ EntityMeans Entity.ofGround q ∧ Incompatible p q :=
  ⟨True, False, trivial, trivial, fun h => h.2⟩


#print axioms ground_scope_does_contain_incompatibles

/-! ## P3 · grounding-by-being, at {} -/

/-- Presence-grounding: `g` is present wherever `e` is. Footprint: `{}`. -/
def GroundByBeing (g e : Entity) : Prop := ∀ w : World, ExistsAt w e → ExistsAt w g

/-- **The ground sustains the being of every entity.** `EntityExistsAt _ Entity.ofGround := True`
    is what makes this free, so the ground is the sustaining cause of all creatures
    (*ST I q.44 a.1* — God is the cause of the whole being of creatures) at no price. This is
    the route by which the ground grounds the **atoms**, which the `OneEssence` route covers only
    vacuously (atoms mean nothing, so `EntityMeans Entity.ofAtom _ p := False` makes the
    containment `True` by vacuity rather than by intent). Footprint: `{}`. -/
theorem ofGround_grounds_every_being_by_presence (e : Entity) :
    GroundByBeing Entity.ofGround e := by
  intro w _
  trivial

#print axioms ofGround_grounds_every_being_by_presence

/-! ## P4 · the two grounding routes, and the personal-ground conjunction, at {} -/

/-- Every person is grounded in the ground *by indwelling*. With the `EntityMeans
    Entity.ofGround p := True` arm this is free; §4.4's rejection keeps it that way, which is
    the load-bearing consequence of *not* truth-restricting the arm. Footprint: `{}`. -/
theorem ofGround_grounds_every_person (s : Subject) (_hP : Person s) :
    OneEssence Entity.ofGround (EntityOf s) := by
  intro p _
  trivial

#print axioms ofGround_grounds_every_person

/-- **No entity is outside the ground**: the ground sustains its being and contains all its
    meaning, so nothing is left ungrounded. Footprint: `{}`. -/
theorem ofGround_leaves_nothing_ungrounded (e : Entity) (_hAct : ActualEntity e) :
    e = Entity.ofGround ∨ (GroundByBeing Entity.ofGround e ∨ OneEssence Entity.ofGround e) :=
  Or.inr (Or.inl (ofGround_grounds_every_being_by_presence e))

#print axioms ofGround_leaves_nothing_ungrounded

/-- **The ground is not void of personhood.** Every person is grounded in it; it sustains all
    being; and it is not a fourth chooser. The three Persons are what make the essence alive;
    this is homoousios-shared personhood, not subject-predication of the ground, which is
    impossible (`ground_is_not_a_fourth_chooser`, `P2`). Footprint: `{}`. -/
structure PersonalGround (g : Entity) : Prop where
  sustains : ∀ e : Entity, ActualEntity e → (e = g ∨ GroundByBeing g e)
  indwells : ∀ s : Subject, Person s → OneEssence g (EntityOf s)

theorem the_ground_is_not_void_of_personhood : PersonalGround Entity.ofGround where
  sustains := fun e _ => Or.inr (ofGround_grounds_every_being_by_presence e)
  indwells := fun _ hP => ofGround_grounds_every_person _ hP

#print axioms the_ground_is_not_void_of_personhood

/-! ## P5 · the potency guard excludes the ground and the atoms, at {}

This is what makes the plan's thesis `{}`-*consistent*: neither the ground nor an atom satisfies
both conjuncts of the guard. A countermodel for the axiom itself (interpret `Means s p := False`
for every `s`) is a separate artifact required by the plan's step, not asserted here.
-/

/-- The ground has no passive intentional potency, so the guard's first conjunct excludes it.
    Footprint: `{}`. -/
theorem potency_guard_excludes_the_ground :
    ¬ (PassiveIntentionalPotency Entity.ofGround ∧ (∃ p : Prop, EntityMeans Entity.ofGround p)) :=
  fun h => ofGround_no_intentional_potency h.1

#print axioms potency_guard_excludes_the_ground

/-- An atom has passive potency (it means nothing) but means nothing, so the guard's second
    conjunct excludes it. Footprint: `{}`. -/
theorem potency_guard_excludes_the_atoms (n : Nat) :
    ¬ (PassiveIntentionalPotency (Entity.ofAtom n) ∧ (∃ p : Prop, EntityMeans (Entity.ofAtom n) p)) := by
  rintro ⟨_, ⟨p, hp⟩⟩
  exact hp

#print axioms potency_guard_excludes_the_atoms

/-! ## P6 · why the `T p` arm is REJECTED — the trade, as a structural fact

The rejected alternative was `EntityMeans Entity.ofGround p := T p` (truth-restricted, since
`T p := p`), on the reasoning that it would make divine infallibility provable
(`TruthTracking Entity.ofGround`). That reasoning was right and the conclusion was still wrong,
for a reason the checker makes visible in three lines: **`PassiveIntentionalPotency` and
`MaximalCapacity` are the same field read in two directions.** `DivinePureActuality`'s
`no_intentional_potency` and C444's `maximal_capacity` route are therefore not two
characteristics but one, and they cannot both be non-trivial. Aquinas holds both pure actuality
(`ST I q.19 a.4`) and infallibility (`ST I q.14 a.1`), so the corpus is already right to want
both — which means the fix is to re-specify `PassiveIntentionalPotency` (it measures passive
potentiality by *semantic* limitation, i.e. `potentia obedientialis` collapsed into
"does not mean some proposition"), **not** to move the match arm. That is a separate milestone
with its own gate; it is recorded here as a finding, not adopted.
-/

/-- **Maximal meaning-capacity excludes passive intentional potency**, axiom-free. This is the
    finding: C444's `maximal_capacity` route and `DivinePureActuality`'s `no_intentional_potency`
    read the *same* field in opposite directions, so they are one characteristic and not two.
    Footprint: `{}`.

    Stated in this direction on purpose. The converse (`¬ MaximalCapacity e →
    PassiveIntentionalPotency e`) is valid classically but needs `not_forall`, so it is **not**
    axiom-free; the plan's argument needs only this direction, and an earlier draft of this
    probe asserted the biconditional, which was false as an `{}` claim. -/
theorem maximal_capacity_excludes_potency (e : Entity) :
    MaximalCapacity e → ¬ PassiveIntentionalPotency e := by
  rintro hmax ⟨p, hp⟩
  exact hp (hmax p)

#print axioms maximal_capacity_excludes_potency

/-- Today the ground has maximal meaning-capacity, so by the identity above it has **no** passive
    intentional potency, so `ofGround_divine_pure_actuality` closes. Footprint: `{}`. -/
theorem the_ground_is_maximally_capable_today : MaximalCapacity Entity.ofGround := by
  intro p
  trivial

#print axioms the_ground_is_maximally_capable_today

/-- And so today the ground is **not** infallible — `EntityMeans Entity.ofGround False := True`
    while `T False` does not hold. This is the refutation row the `T p` arm would have removed,
    and the reason it is *not* removed by moving the arm. Footprint: `{}`. -/
theorem the_ground_is_not_infallible_today : ¬ TruthTracking Entity.ofGround := by
  intro h
  exact h False trivial

#print axioms the_ground_is_not_infallible_today

end Logos.TrinitarianProbe
