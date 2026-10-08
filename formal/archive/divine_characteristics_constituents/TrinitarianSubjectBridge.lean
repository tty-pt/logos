import Logos.Core
import Logos.Entity
import Logos.Semantics
import Logos.Agency
import Logos.Alternatives
import Logos.Choice
import Logos.Person
import Logos.Plurality
import Logos.RecoveredOntologicalGround
import Logos.NecessityEternity
import Logos.AsieticChoice
import Logos.DivineAgape
import Logos.FoundationalOmnipresence
import Logos.FoundationalUnicity
import Logos.SemanticFinitude
import Logos.TrinitarianPersonalGround
import Logos.BoundedMeaning
import Logos.PersonalNormativeGround
import Logos.DivinePureActuality

/-
# TrinitarianSubjectBridge (plan S4, D-1 + D-2)

The bridge the plan names as the missing work at §3.3: `DivineAgape` declares and prices the
procession vocabulary over `DivineHypostasis`, but nothing connects that sort to `Subject`,
`Person`, freedom, or necessity. This module supplies the connection and nothing else.

**What is declared here.** `DivineRole` (a role sort, three constructors, zero axioms) and
`DivineSubjectRole` (`Tag: VOCAB`, the D-1 classifier); `TrinitarianPersonalBridge` (`Tag: META`,
the D-2 bridge). Two axioms. Every theorem in the module is derived from those plus the existing
corpus.

**What is deliberately not done.** `GroundsRightWrong` is never used (plan §7, F12). It is
definitionally `∃ p q, Chooses s p q` — already free will — so using it as the personal-ground
antecedent would assume what this step must establish. The bridge is therefore asserted flat,
and the freedom it carries is *independently* posited for the three subjects, not smuggled
through a relation that already contains it.

**What is not claimed.** Nothing here is derived from the procession axioms; `AxAgapeEssence`,
`AxProcessionWord` and `AxProcessionSpirit` are **not** in this module's footprint, and their
absence is the honest reading of §6.3: identity between the divine-hypostasis sort and `Subject`
is not the claim (and `Entity.noConfusion` forbids it for the ground). What is claimed is the
weaker, correctly-typed thing the Nicene formula actually needs — three *distinct* divine-role
subjects, each a necessary person, sharing the one ground. Connecting those subjects to the
`DivineHypostasis` centers is a further, separate bridge and is **not** discharged here; see
§11.
-/

namespace Logos.TrinitarianSubjectBridge

open Logos.Core
open Logos.Semantics (World)
open Logos.Entity (Entity EntityOf)
open Logos.Agency (Subject Means NecessarySubjectKind)
open Logos.Alternatives (Incompatible)
open Logos.Choice (Chooses FreeWill FreeSubject)
open Logos.Person (Person)
open Logos.Plurality (NecessarySubject)
open Logos.RecoveredOntologicalGround (ActualEntity OneEssence GroundOfReality EntityMeans
  NecessaryGroundOfReality)
open Logos.AsieticChoice (Asiety)
open Logos.DivineAgape (divineReality)
open Logos.PersonalNormativeGround (GroundsRightWrong)
open Logos.NecessityEternity (ofGround_necessary_ground_of_reality)
open Logos.DivinePureActuality (PassiveIntentionalPotency ofGround_no_intentional_potency)
open Logos.BoundedMeaning (BoundedMeaningRequiresFreeSubject
  guard_excludes_exactly_the_impersonal_cases)
open Logos.FoundationalOmnipresence (UniversalModalGround)
open Logos.FoundationalUnicity (exactly_one_universal_modal_ground ofGround_ne_ofSubject)
open Logos.SemanticFinitude (SemanticFinitude)
open Logos.TrinitarianPersonalGround (Perichoretic ofGround_is_perichoretic)

-- ===========================================================================
-- Section 1: D-1 — the role vocabulary on the `Subject` sort
-- ===========================================================================

/-- **D-1, the role sort.** `DivineRole` is the content of `DivineAgape.IsWord` and
    `IsSpirit` lifted off the `DivineHypostasis` sort: the three roles by relations of origin
    (`ST` I q.28 a.3), namely the source (`ST` I q.38 a.1), the Word (`ST` I q.7 a.3), and the
    Spirit (`ST` I q.36 a.4).

    A `def`-like constructor set, **not** an axiom: it costs nothing and it is not a parallel
    hypostasis sort. Plan §6.4 rejected introducing a *second* sort of divine centers beside
    `DivineHypostasis`; this is a sort of **roles**, and it introduces no inhabitants of
    anything. It is `inductive` rather than three `opaque` predicates precisely so that the
    roles are *distinguishable* — `IsWord`/`IsSpirit` are `opaque … := True` (the `BearingOf`
    pattern) and therefore cannot distinguish anything from each other, which is why the corpus
    needed a `relational_distinction` field it could only fill with `fun a b => a ≠ b`.
    Footprint: `{}`. -/
inductive DivineRole where
  /-- The unoriginated source. -/
  | source
  /-- The Word: the object of the essential self-giving. -/
  | word
  /-- The Spirit: the return of the gift. -/
  | spirit
  deriving DecidableEq, Repr

/-- The three roles are pairwise distinct. `deriving DecidableEq` is what makes this a
    *computation* rather than a priced claim: no axiom is consumed, which is the whole reason D-1
    is a constructor set and not three opaque predicates.
    Footprint: `{}`. -/
theorem DivineRole.source_ne_word : DivineRole.source ≠ DivineRole.word := by decide

/-- Word and Spirit are distinct roles.
    Footprint: `{}`. -/
theorem DivineRole.word_ne_spirit : DivineRole.word ≠ DivineRole.spirit := by decide

/-- Source and Spirit are distinct roles.
    Footprint: `{}`. -/
theorem DivineRole.source_ne_spirit : DivineRole.source ≠ DivineRole.spirit := by decide

/--Tag: VOCAB
Vocabulary: the hypostatic role of a subject — the relation of origin that distinguishes the
three divine persons from one another.

  `DivineAgape.IsWord` and `IsSpirit` classify `DivineHypostasis`, so they **cannot** be
  applied to a `Subject`: the two sorts have no common carrier, and `Entity.ofSubject` embeds a
  subject into `Entity`, not into `DivineHypostasis`. The role content therefore has to be
  re-declared on the `Subject` sort, and this is that declaration. It says which *relation of
  origin* a subject bears; it does not say that any subject bears one, which is `D-2`'s work
  (`TrinitarianPersonalBridge`, `Tag: META`).

  Plan §7 budgets this as `VOCAB`: a classifier over an opaque sort, exactly as
  `NecessarySubjectKind` (`Agency.lean:62`) is. `Subject` is `axiom Subject : Type` with no
  constructors, so this predicate is genuinely not derivable — there is no inhabitant to apply it
  to. It is vocabulary rather than a substantive choice because it introduces no connection
  between entities: it is a three-valued classifier on one uninterpreted sort.
  Footprint: `{Subject}` (vocabulary only; the classifier's own `Subject` argument is the
  `Subject` sort axiom, which every declaration over `Subject` already pays). -/
axiom DivineSubjectRole : Subject → DivineRole

/-- The three roles exhaust the sort: every role is one of the three named relations of origin.
    A decidability fact about three constructors, so it costs nothing and closes the risk that
    `DivineSubjectRole` is a fourth, unnamed role in disguise.
    Footprint: `{propext}`. -/
theorem role_exhausts_the_sort (r : DivineRole) :
    r = DivineRole.source ∨ r = DivineRole.word ∨ r = DivineRole.spirit := by
  cases r <;> simp

-- ===========================================================================
-- Section 2: D-2 — the bridge
-- ===========================================================================

/--Tag: META
TrinitarianPersonalBridge (META; plan §7 D-2, poem P5/P7): the three divine persons are
  `Subject`s, and they are necessary persons who share the one ground.

  **Why this must be declared.** `Subject` is `axiom Subject : Type`, opaque, with **no
  constructors** (`Agency.lean:49`). Every existential over `Subject` therefore needs an axiom,
  and this is the one the Nicene formula needs. `DivineHypostasis` is a different sort with
  inhabited constructors, but there is no map from it into `Subject`, and §6.3 is explicit that
  *identity* is not the claim: `Entity.noConfusion` blocks identifying the ground with any
  subject, and the same reflexive move would be the wrong shape for the persons.

  **Why it does not route through `GroundsRightWrong`.** That relation is definitionally
  `∃ p q, Chooses s p q` (`PersonalNormativeGround.lean:288`) — already free will (`ClaimMeanings`
  F12, C168). Using it as the personal-ground antecedent would assume the freedom this axiom is
  meant to establish, so the freedom is posited here flat and independently, and the audit of
  `BoundedMeaning` is explicit that the three persons' `FreeWill` "rests entirely on" this
  bridge rather than on D-3.

  **What is load-bearing, and what is not.** Load-bearing: `Person`, `FreeSubject`,
  `NecessarySubject`, the three role assignments, and the exhaustion of `NecessarySubjectKind`.
  *Not* load-bearing: subsistence. `Subsists d := d.deiformEntity = divineReality`
  (`DivineAgape.lean:85`) already fixes each hypostasis in the one ground, so asserting it here
  would be restating a `def`; the one-ground consequence is *derived* below
  (`the_three_persons_share_the_one_ground`) as **perichoretic indwelling** and rests on
  `divineReality := Entity.ofGround`, a `def` (`DivineAgape.lean:70`), not on the three `META`
  procession axioms.

  **The three persons are never equated with the ground.** An earlier revision of this axiom
  carried `EntityOf a = divineReality ∧ EntityOf b = divineReality ∧ EntityOf c = divineReality`
  among its conjuncts. Since `divineReality := Entity.ofGround` is a `def` and the corpus proves
  `ofGround_ne_ofSubject (s) : EntityOf s ≠ Entity.ofGround` (`FoundationalUnicity.lean:134`), those
  three conjuncts made `False` derivable: the axiom was *refuted by a theorem of the same
  theory*. Indwelling is not identity, and the Nicene claim is indwelling — *praeter hoc, quod
  unus est, tres sunt* is not that the three **are** the one. The conjuncts are therefore deleted,
  and `the_three_persons_share_the_one_ground` below states the honest consequence: the three are
  perichoretic in the one ground, and **none of them is it**
  (`TrinitarianPersonalGround.no_person_is_the_ground`, `{Subject}`). The regression test is
  `formal/consistency/FalseNotDerivable.lean`, which must fail to compile; run
  `python3 scripts/check_consistency.py`.

  **Price.** `Person a` already entails `FreeSubject a` definitionally
  (`DominionOverActs = FreeWill`, `Person.lean:56`), so the three `FreeSubject` conjuncts are not
  an independent purchase — they are carried, and stated, by the `Person` conjuncts. They are
  nevertheless asserted explicitly and exported as separate theorems, because *stating* them is
  what discharges D-3's debt at the point a reader looks for it
  (`BoundedMeaning.lean:69`). Footprint: `{DivineSubjectRole, Means, NecessarySubjectKind, Subject, Will, subjectWill}` plus
  this axiom. -/
axiom TrinitarianPersonalBridge :
    ∃ a b c : Subject,
      DivineSubjectRole a = DivineRole.source ∧
      DivineSubjectRole b = DivineRole.word ∧
      DivineSubjectRole c = DivineRole.spirit ∧
      Person a ∧ Person b ∧ Person c ∧
      FreeSubject a ∧ FreeSubject b ∧ FreeSubject c ∧
      NecessarySubject a ∧ NecessarySubject b ∧ NecessarySubject c ∧
      (∀ s : Subject, NecessarySubjectKind s → s = a ∨ s = b ∨ s = c)

/-- The three persons exist and carry the three roles of origin. This is the witness projection
    of the bridge: everything downstream destructs this, so the shape a reader sees first is the
    doctrine rather than the flat conjunction.
    Footprint: `{DivineSubjectRole, Means, NecessarySubjectKind, Subject, TrinitarianPersonalBridge, Will, subjectWill}`. -/
theorem three_divine_persons_exist_with_roles :
    ∃ a b c : Subject,
      DivineSubjectRole a = DivineRole.source ∧
      DivineSubjectRole b = DivineRole.word ∧
      DivineSubjectRole c = DivineRole.spirit ∧
      Person a ∧ Person b ∧ Person c := by
  obtain ⟨a, b, c, hra, hrb, hrc, hpa, hpb, hpc, _, _, _, _, _, _, _⟩ :=
    TrinitarianPersonalBridge
  exact ⟨a, b, c, hra, hrb, hrc, hpa, hpb, hpc⟩

/-- Each of the three is a person.
    Footprint: `{DivineSubjectRole, Means, NecessarySubjectKind, Subject, TrinitarianPersonalBridge, Will, subjectWill}`. -/
theorem three_divine_persons_are_persons :
    ∃ a b c : Subject, Person a ∧ Person b ∧ Person c := by
  obtain ⟨a, b, c, _, _, _, hpa, hpb, hpc, _, _, _, _, _, _, _⟩ :=
    TrinitarianPersonalBridge
  exact ⟨a, b, c, hpa, hpb, hpc⟩

/-- **The three persons are free subjects — and this is the row the D-3 audit reads.** The
    audit gate is that these trace to `TrinitarianPersonalBridge` (`META`) and *not* to
    `BoundedMeaningRequiresFreeSubject` (`TRANS`); the footprint below is the evidence, and
    `BoundedMeaningRequiresFreeSubject` is absent from it. The conclusion is carried by the
    bridge's `FreeSubject` conjuncts, and is also reachable from its `Person` conjuncts
    definitionally, so it is stated twice over on purpose: once as the theorem a reader checks,
    once as the definitional consequence that shows the price is not being double-counted.
    Footprint: `{DivineSubjectRole, Means, NecessarySubjectKind, Subject, TrinitarianPersonalBridge, Will, subjectWill}`. -/
theorem three_divine_persons_are_free_subjects :
    ∃ a b c : Subject, FreeSubject a ∧ FreeSubject b ∧ FreeSubject c := by
  obtain ⟨a, b, c, _, _, _, _, _, _, hfa, hfb, hfc, _, _, _, _⟩ :=
    TrinitarianPersonalBridge
  exact ⟨a, b, c, hfa, hfb, hfc⟩

/-- The same three, at the definitional route: `Person s → FreeSubject s` is `h.2.2`, so the
    freedom in the preceding theorem is *not* an independent purchase. Stated so the price table
    cannot be read as charging twice for one fact.
    Footprint: `{Means, Subject, Will, subjectWill}` (vocabulary only — no bridge, no META). -/
theorem person_is_freeSubject (s : Subject) (h : Person s) : FreeSubject s :=
  h.2.2

/-- Each of the three is a necessary subject.
    Footprint: `{DivineSubjectRole, Means, NecessarySubjectKind, Subject, TrinitarianPersonalBridge, Will, subjectWill}`. -/
theorem three_divine_persons_are_necessary :
    ∃ a b c : Subject, NecessarySubject a ∧ NecessarySubject b ∧ NecessarySubject c := by
  obtain ⟨a, b, c, _, _, _, _, _, _, _, _, _, hna, hnb, hnc, _⟩ :=
    TrinitarianPersonalBridge
  exact ⟨a, b, c, hna, hnb, hnc⟩

/-- The three persons exhaust the necessary kind: there is no fourth necessary subject. This is
    the clause that turns "at least three" into "exactly three", and it is a *priced* claim —
    `NecessarySubjectKind` is vocabulary, but its inhabitant set is not, and nothing in the
    preceding corpus bounds it. Distinctness is separately **derived** below, from the role
    assignment, at zero cost.
    Footprint: `{DivineSubjectRole, Means, NecessarySubjectKind, Subject,
    TrinitarianPersonalBridge, Will, subjectWill}`. -/
theorem three_divine_persons_exhaust_the_necessary_kind :
    ∃ a b c : Subject,
      Person a ∧ Person b ∧ Person c ∧
      (∀ s : Subject, NecessarySubjectKind s → s = a ∨ s = b ∨ s = c) := by
  obtain ⟨a, b, c, _, _, _, hpa, hpb, hpc, _, _, _, _, _, _, hEx⟩ :=
    TrinitarianPersonalBridge
  exact ⟨a, b, c, hpa, hpb, hpc, hEx⟩

/-- **Distinctness is derived, not bought.** Three distinct roles cannot be borne by one subject,
    so `a ≠ b ∧ b ≠ c ∧ a ≠ c` follows from the role assignment alone. Plan §7 says distinctness
    "is C510's; do not re-derive it" — but C510 is about `DivineHypostasis` and does not reach
    `Subject`, so on this sort the derivation is both necessary and free. Nothing is paid here
    beyond the bridge itself.
    Footprint: `{DivineSubjectRole, Subject}`. -/
theorem roles_make_the_three_persons_distinct {a b c : Subject}
    (ha : DivineSubjectRole a = DivineRole.source)
    (hb : DivineSubjectRole b = DivineRole.word)
    (hc : DivineSubjectRole c = DivineRole.spirit) :
    a ≠ b ∧ b ≠ c ∧ a ≠ c := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> subst h
  · rw [ha] at hb
    exact DivineRole.source_ne_word hb
  · rw [hb] at hc
    exact DivineRole.word_ne_spirit hc
  · rw [ha] at hc
    exact DivineRole.source_ne_spirit hc

/-- **The three persons share the one ground — by indwelling, not by identity.** `divineReality`
    is `Entity.ofGround` by definition (`DivineAgape.lean:70`), so the ground is *one*; the three
    are related to it by `Perichoretic`, i.e. `OneEssence` instantiated three times. This is the
    derived form of subsistence and rests on a `def` unfolding, not on the three `META` procession
    axioms.

    The second conjunct is load-bearing and was not optional. An earlier revision stated this as
    `EntityOf a = Entity.ofGround ∧ …`, which `ofGround_ne_ofSubject` (`FoundationalUnicity.lean:134`)
    refutes outright: that made the corpus derive `False`. "Share one ground" is *praeter hoc, quod
    unus est, tres sunt* — the ground is not one of the three, and the three are not the ground. So
    the honest statement carries both halves: the three are perichoretic in the one ground **and**
    no subject is it.
    Footprint: `{DivineSubjectRole, Means, NecessarySubjectKind, Subject, TrinitarianPersonalBridge, Will, subjectWill}`. -/
theorem the_three_persons_share_the_one_ground :
    ∃ a b c : Subject,
      Person a ∧ Person b ∧ Person c ∧
      Perichoretic Entity.ofGround a b c ∧
      (∀ s : Subject, EntityOf s ≠ Entity.ofGround) := by
  obtain ⟨a, b, c, _, _, _, hpa, hpb, hpc, _, _, _, _, _, _, _⟩ :=
    TrinitarianPersonalBridge
  exact ⟨a, b, c, hpa, hpb, hpc,
    ofGround_is_perichoretic a b c hpa hpb hpc,
    fun s => ofGround_ne_ofSubject s⟩

/-- **The explicit negative boundary**, kept as its own row so no reader has to infer it from the
    shape of the conjunct above: no divine person *is* the ground. The ground is Personal and
    indwells all three; it is not a fourth person and not any of the three
    (`TrinitarianPersonalGround.no_person_is_the_ground` states the same fact with no bridge).
    Footprint: `{Subject}`. -/
theorem no_divine_person_is_the_ground (s : Subject) : EntityOf s ≠ Entity.ofGround :=
  ofGround_ne_ofSubject s

-- ===========================================================================
-- Section 3: §5.1 — one necessary ground, three free necessary persons
-- ===========================================================================

/-- **§5.1, the master theorem.** One necessary ground of reality; exactly one universal modal
    ground; and exactly three necessary persons, distinct by relation of origin, each a
    `Person`, each a `FreeSubject`, exhausting the necessary kind of subject, and perichoretic in
    the one ground.

    Two honest notes on the statement, both forced by types rather than by taste.

    (1) The plan's draft identified the persons by `DivineHypostasis.P1 = a`. That does not
    elaborate: `P1` is a field of `TrinitarianStructure` (`ConditionalTheology.lean:308`),
    instantiated at `Subj := DivineHypostasis`, and a `DivineHypostasis` cannot be equated with a
    `Subject` — there is no coercion and no common sort. The identification is therefore stated
    the only way the vocabulary allows: by **role** (`DivineSubjectRole a = .source`, and so on),
    which is also theologically the right content, since §6.3 and `ST` I q.28 a.3 distinguish the
    Persons by relations of origin rather than by essence. Naming which *hypostasis* each subject
    corresponds to is a further bridge and is **not** discharged — see §11.

    (2) The unicity conjunct (spelled out, since `ExistsUnique` does not exist in this
    environment) is **not** axiom-free: ground-unicity is conditional on
    the transcendence bound F15, the declared axiom `GroundTranscendence` (`Tag: META`).
    Existence of the ground was
    already unconditional (`ofGround_necessary_ground_of_reality`, 0 substantive); it is
    *unicity* that rests on the bound. Plan §10 lists this row as a reader defect, and plan §0.2
    settles how the price is displayed. **This changed on 2026-10-03:** before the finitude
    split, the bound here was `SemanticFinitude` at `Tag: VOCAB`, so the row kept a
    vocabulary-only `PROVEN` badge and the price was disclosed by
    `census_semantic_finitude.py` and by `semantic_omnipotence_is_consistent`
    (what a reader who rejects the bound loses). The split moved the unrestricted bound
    onto `GroundTranscendence` at `Tag: META`, so this row now prints a **metaphysical**
    price and reads `PROVEN↑` — **AXIOMATIC (GroundTranscendence)** to a reader — which is
    the honest outcome: the unicity of the ground was never vocabulary.

    Footprint: `{DivineSubjectRole, GroundTranscendence, Means, NecessarySubjectKind, Subject,
    TrinitarianPersonalBridge, Will, subjectWill}` — measured; identical to plan §7 except
    that `GroundTranscendence` stands where `SemanticFinitude` stood before the split.
    Note what is **absent**: no `AxAgapeEssence`, `AxProcessionWord` or `AxProcessionSpirit`, because
    the persons are identified by role rather than by hypostasis. Their absence is the honest
    measure of the open item at §11, and is deliberately not hidden inside the bridge's price. -/
theorem one_necessary_ground_three_free_necessary_persons :
    NecessaryGroundOfReality Entity.ofGround ∧
    (∃ g : Entity, UniversalModalGround g ∧
      ∀ g' : Entity, UniversalModalGround g' → g' = g) ∧
    (∃ a b c : Subject,
        DivineSubjectRole a = DivineRole.source ∧
        DivineSubjectRole b = DivineRole.word ∧
        DivineSubjectRole c = DivineRole.spirit ∧
        a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
        Person a ∧ Person b ∧ Person c ∧
        FreeSubject a ∧ FreeSubject b ∧ FreeSubject c ∧
        NecessarySubject a ∧ NecessarySubject b ∧ NecessarySubject c ∧
        (∀ s : Subject, NecessarySubjectKind s → s = a ∨ s = b ∨ s = c) ∧
        Perichoretic Entity.ofGround a b c) := by
  refine ⟨ofGround_necessary_ground_of_reality, ?_, ?_⟩
  · exact exactly_one_universal_modal_ground Logos.SemanticFinitude.GroundTranscendence
  · obtain ⟨a, b, c, hra, hrb, hrc, hpa, hpb, hpc, hfa, hfb, hfc,
      hna, hnb, hnc, hEx⟩ := TrinitarianPersonalBridge
    have hne := roles_make_the_three_persons_distinct hra hrb hrc
    exact ⟨a, b, c, hra, hrb, hrc, hne.1, hne.2.1, hne.2.2,
      hpa, hpb, hpc, hfa, hfb, hfc, hna, hnb, hnc, hEx,
      TrinitarianPersonalGround.ofGround_is_perichoretic a b c hpa hpb hpc⟩

/-- **The S4 gate, in the only form a kernel can carry.** The audit gate is that the three
    persons' freedom traces to the `META` bridge and *not* to the `TRANS` bounded-meaning axiom.
    A footprint is not statable inside the theory, so the gate has two halves and both are here.

    The kernel half, stated precisely because the loose version is **false**: D-3's antecedent is
    *not* confined to the impersonal cases. `guard_excludes_exactly_the_impersonal_cases`
    (`BoundedMeaning.lean:158`) shows the antecedent's survivors are ground, atoms, **and
    subjects** — the axiom is named *bounded* meaning precisely because it constrains subjects
    rather than excluding them. What D-3 cannot do is turn an impersonal entity into a free
    subject: on every survivor that is not a subject, the conclusion is never reached, because
    the antecedent already fails there (the ground has no passive intentional potency, an atom
    means nothing). So D-3 never *produces* freedom; where it applies it reads it off a subject,
    and D-2 is what asserts that subject has it.

    The footprint half, which is the part the gate is really checked by: the `#print axioms` line
    for `three_divine_persons_are_free_subjects` reads `{DivineSubjectRole, Means,
    TrinitarianPersonalBridge, Will, subjectWill}` — `BoundedMeaningRequiresFreeSubject` is
    **absent**. If a future refactor routes this existence through the `TRANS` axiom, that
    footprint grows it and the gate fails visibly, which is the intended failure mode.
    Footprint: `{BoundedMeaningRequiresFreeSubject, DivineSubjectRole, Means, NecessarySubjectKind, Subject, TrinitarianPersonalBridge, Will, subjectWill}`. -/
theorem the_three_persons_freedom_is_asserted_not_earned :
    (∃ a b c : Subject, FreeSubject a ∧ FreeSubject b ∧ FreeSubject c) ∧
    (∀ e : Entity, PassiveIntentionalPotency e → (∃ p : Prop, EntityMeans e p) →
      (e = Entity.ofGround ∨ (∃ n : Nat, e = Entity.ofAtom n)) ∨
        (∃ s : Subject, e = EntityOf s ∧ FreeWill s)) :=
  ⟨three_divine_persons_are_free_subjects, by
    intro e hPot hMeans
    rcases guard_excludes_exactly_the_impersonal_cases e with hImp | ⟨s, hs⟩
    · exact Or.inl hImp
    · obtain ⟨t, ht, hFree⟩ := BoundedMeaningRequiresFreeSubject e hPot hMeans
      exact Or.inr ⟨t, ht, hFree⟩⟩

/-- The impersonal survivors of D-3's antecedent are exactly the two that can never satisfy it:
    the ground has no passive intentional potency, and an atom means nothing. So D-3's antecedent
    is satisfiable **only** for subjects — which is why it cannot be the source of the three
    divine persons' freedom, and why the axiom is about creatures rather than about God.
    Footprint: `{Means, Subject, propext}` (vocabulary only). -/
theorem d3s_antecedent_cannot_fire_on_the_impersonal :
    (∀ (e : Entity), e = Entity.ofGround → ¬ PassiveIntentionalPotency e) ∧
    (∀ (e : Entity) (n : Nat), e = Entity.ofAtom n → ¬ (∃ p : Prop, EntityMeans e p)) :=
  ⟨fun _ h => by subst h; exact ofGround_no_intentional_potency,
   fun _ _ h hp => by subst h; simp [EntityMeans] at hp⟩

/-- The bridge is **not** derived from `GroundsRightWrong`, and is not routed through it: the
    relation is definitionally free will already, so a bridge built on it would be circular
    (plan §7, `ClaimMeanings` F12). This row records the *shape* of the freedom the bridge
    asserts, next to the shape `GroundsRightWrong` carries, so the difference is visible in the
    kernel rather than only in a prose note.
    Footprint: `{DivineSubjectRole, Means, NecessarySubjectKind, Subject, TrinitarianPersonalBridge, Will, subjectWill}`. -/
theorem the_bridge_asserts_freedom_independently_of_groundsRightWrong :
    (∃ a b c : Subject, FreeSubject a ∧ FreeSubject b ∧ FreeSubject c) ∧
    (∀ s : Subject, GroundsRightWrong s → ∃ p q : Prop, Chooses s p q) := by
  refine ⟨three_divine_persons_are_free_subjects, ?_⟩
  intro s h
  exact h.agential_foundation

/-- The ground is still not a fourth chooser after S4: adding three divine persons does not make
    the ground personal. This is the `praeter hoc, quod unus est, tres sunt` boundary, and it is
    re-checked here rather than inherited, because S4 is exactly the step at which it would have
    been tempting to let the ground's `Asiety` transfer into personhood.
    Footprint: `{Means, Subject}` (vocabulary only). -/
theorem s4_does_not_make_the_ground_a_fourth_chooser :
    ¬ Asiety Entity.ofGround :=
  TrinitarianPersonalGround.ground_is_not_a_fourth_chooser

-- ===========================================================================
-- Section 4: Footprint audit
-- ===========================================================================

#print axioms DivineRole.source_ne_word
#print axioms DivineRole.word_ne_spirit
#print axioms DivineRole.source_ne_spirit
#print axioms role_exhausts_the_sort
#print axioms three_divine_persons_exist_with_roles
#print axioms three_divine_persons_are_persons
#print axioms three_divine_persons_are_free_subjects
#print axioms person_is_freeSubject
#print axioms three_divine_persons_are_necessary
#print axioms three_divine_persons_exhaust_the_necessary_kind
#print axioms roles_make_the_three_persons_distinct
#print axioms the_three_persons_share_the_one_ground
#print axioms no_divine_person_is_the_ground
#print axioms one_necessary_ground_three_free_necessary_persons
#print axioms the_three_persons_freedom_is_asserted_not_earned
#print axioms d3s_antecedent_cannot_fire_on_the_impersonal
#print axioms the_bridge_asserts_freedom_independently_of_groundsRightWrong
#print axioms s4_does_not_make_the_ground_a_fourth_chooser

end Logos.TrinitarianSubjectBridge