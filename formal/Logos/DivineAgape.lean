/-
# Logos.DivineAgape — a good case for the Trinity from self-giving love

The Trinity **cannot be derived** in Γ's discipline, and this module does not
attempt to force it. What it supplies is the strongest legitimate "case" — the
same shape the corpus already uses for the moral Good (C177 PROVEN↑ +
C176/C499 refusals):

  1. a **conditional corridor**: under three disclosed, priced `Tag: META`
     axioms — the Agape datum, the procession of the Word, the procession of
     the Spirit — the divine reality is inhabited by three pairwise-distinct
     subsistent personal centers (`TrinitarianStructure`, C108); and
  2. a catalogue of separation models (Stage B of plan `TRINITY.md`) proving
     every cheaper reading stays consistent.

Plan of record: `TRINITY.md` (root). Stage A of that plan is this file: the
divine sort, the vocabulary, the three priced axioms, the corridor theorems
(C507–C509) and the main theorem (C510). **No Γ axiom is modified.** The
creature-beloved lane stays walled (C481/C482, C503); this corridor runs in the
Godhead, where the beloved is a divine personal center — by declaration, never
by projection from the subject level.

Design decisions (locked with the author 2026-09-29):

  * **New sort, real ontology untouched.** `DivineHypostasis` is a fresh abstract
    sort. The ground is provably not a `Subject` (`ofGround_ne_ofSubject`) and
    no contingent-kind subject is necessary
    (`no_subject_is_a_necessary_entity`), so a "divine person as `Subject`"
    reading is structurally awkward. Inside the Godhead the plurality is
    *expressed*, not forced.
  * **Unicity kept, not relaxed.** `divineReality := Entity.ofGround`, the one
    universal modal ground (C320). Subsistence is defined as *having one's
    being in that one reality*. The three centers share it (C212's
    non-collapse).
  * **Three priced axioms, house pattern.** `AxAgapeEssence` (the datum),
    `AxProcessionWord` and `AxProcessionSpirit` mirror
    `AxBenevolentBearingObtains`/`AxGroundLovesContingentRealm`: declared,
    tagged `META`, priced in the docstring, with a consistency-model note.
    The love relation and the two role predicates are `opaque` vocabulary
    (the `BearingOf` pattern), so the declared-axiom count moves 32 → 35
    (17 VOCAB, 18 substantive) — exactly the plan's §3.1 estimate.
  * **Three is exactly the Spirit price.** The datum gives the source and the
    beloved (two centers). The Word bridge names the beloved the Word. The
    Spirit bridge adds the third center, distinct from both. Nothing cheaper
    can force it.

Stage B (separations, ledger/prose sync, regeneration) follows `TRINITY.md`.
-/

import Logos.ConditionalTheology
import Logos.NecessityEternity
import Logos.TheologicalModalHardening

namespace Logos.DivineAgape

open Logos.ConditionalTheology (TrinitarianStructure)
open Logos.Entity (Entity ExistsAt actualWorld)
open Logos.NecessityEternity (ofGround_necessary)
open Logos.TheologicalModalHardening
    (ContingentEntity NecessaryEntity necessary_not_contingent)

-- ============================================================================
-- Section 1: The divine sort and the Godhead vocabulary (all `def`/`opaque`,
-- zero new axioms)
-- ============================================================================

/-- The one divine reality: `Entity.ofGround`, the world-rigid universal modal
    ground (C320). A `def`, not a new axiom: it does not restate unicity, it
    names the unique ground as the Godhead's single reality. -/
def divineReality : Entity := Entity.ofGround

/-- A divine person: a fresh abstract sort (real Γ ontologies untouched),
    equipped with its location-entity — the one reality it shares. The
    structure does not force the location; that is the content of the priced
    axioms below, where each centered person is asserted to *subsist in*
    `divineReality`. -/
structure DivineHypostasis where
  deiformEntity : Entity

/-- Subsistence: a divine person has its being in the one divine reality.
    (VOCAB predicate; the "in the Godhead" conjunct every centered person
    carries.) Defined as a location-equality — by contrast, an *attribute*
    reading (self-knowledge/self-love as an intrinsic non-subsistent state)
    carries no `DivineHypostasis` at all, which is the separation of Stage B. -/
def Subsists (d : DivineHypostasis) : Prop :=
  d.deiformEntity = divineReality

/-- `is_divine d e`: the `TrinitarianStructure` relation — the personal center
    `d` is in the divine reality `e`. -/
def is_divine (d : DivineHypostasis) (e : Entity) : Prop :=
  d.deiformEntity = e

/-- The source's love of a personal object, inside the Godhead. An `opaque`
    primitive (the `BearingOf` pattern): the kernel cannot reduce on it, so
    the love datum is a genuine commitment, never a definitional accident.
    The value `True` is hidden; the semantic content lives in this docstring:
    self-giving love — agape — aimed at a personal center. -/
opaque DivineLove (_f _o : DivineHypostasis) : Prop := True

/-- The Word: an opaque role predicate (BearingOf pattern) whose content is
    "the subsistent divine person that is the beloved object of the essential
    self-giving" — the intellectual procession, the object. -/
opaque IsWord (_d : DivineHypostasis) : Prop := True

/-- The Spirit: an opaque role predicate (BearingOf pattern) whose content is
    "the subsistent divine person through whom the gift returns" — the
    receptive/returning procession, the third center. -/
opaque IsSpirit (_d : DivineHypostasis) : Prop := True

-- ============================================================================
-- Section 2: The three priced axioms (all `Tag: META`)
-- ============================================================================

/--Tag: META
The divine source's love is essential self-giving: it reaches, and sustains,
  a distinct personal center in the Godhead (the beloved). This is the Agape
  datum — the one big price of the case.

  Content: some divine person `f` (the source, the Father) subsists in the one
  divine reality, and its love (`DivineLove`) reaches an `o` distinct from it
  that also subsists there. The object is *personal* (a `DivineHypostasis`, not a
  contingent creature, not an attribute), and the love is *directed*, in the
  `GroundBearsGood`/`DivineLove` idiom.

  Refusal model (the Narcissus world): a world whose `DivineLove` is uniformly
  `False` satisfies the whole vocabulary — every divine person subsists, no
  love reaches another — and there the datum fails. The lesser theory (unitary
  self-possession, no beloved) is therefore machine-checked consistent: the
  Agape datum is a genuine choice, never a consequence of unicity alone (C212
  is exactly what leaves the frontier open).

  Philosophical cost: a substantive doctrine of the divine love as *ecstatic,
  self-giving* — not self-love, not an intrinsic attribute. A reader who
  rejects the price rejects this axiom, and with it the whole corridor. -/
axiom AxAgapeEssence :
    ∃ f : DivineHypostasis,
      Subsists f ∧ (∃ o : DivineHypostasis, o ≠ f ∧ Subsists o ∧ DivineLove f o)

/-- The source center (the Father), extracted from the datum by choice. -/
noncomputable def the_father : DivineHypostasis := Classical.choose AxAgapeEssence

/-- The beloved center, extracted from the datum by choice. -/
noncomputable def the_beloved : DivineHypostasis :=
  Classical.choose (Classical.choose_spec AxAgapeEssence).2

/-- The datum unwrapped: the source subsists. -/
theorem the_father_subsists : Subsists the_father :=
  (Classical.choose_spec AxAgapeEssence).1

/-- The datum unwrapped: the beloved is other than the source. -/
theorem the_beloved_distinct : the_beloved ≠ the_father :=
  (Classical.choose_spec (Classical.choose_spec AxAgapeEssence).2).1

/-- The datum unwrapped: the beloved subsists in the divine reality. -/
theorem the_beloved_subsists : Subsists the_beloved :=
  (Classical.choose_spec (Classical.choose_spec AxAgapeEssence).2).2.1

/-- The datum unwrapped: the source loves the beloved. -/
theorem the_source_loves_the_beloved : DivineLove the_father the_beloved :=
  (Classical.choose_spec (Classical.choose_spec AxAgapeEssence).2).2.2

/--Tag: META
The beloved of the essential love subsists as the Word: the personal object of
  the source's self-giving is not an accidental object-of-love but a divine
  person in its own right, the intellectual procession — named, not invented.

  Refusal model (the attribute-love world): self-knowledge/self-love as an
  intrinsic non-subsistent state — a Godhead with no `DivineHypostasis` at all
  beyond the source's enacted content — satisfies the vocabulary and the datum's
  *agent* half while nothing is a Word. The subsistence conjunct of the
  procession is therefore load-bearing, and the "step 6" gap of the Augustinian
  route is exhibited, not asserted.

  Philosophical cost: the beloved is a *person*, not a mode. Substantive on
  its own account; the datum already supplied the person, this bridge names it
  the Word. -/
axiom AxProcessionWord : IsWord the_beloved

/--Tag: META
The self-gift returns: a third divine person, the Spirit, subsists in the
  divine reality, other than the source and other than every Word.

  This is the axle of the whole case. The datum gives *two* centers (father
  and beloved); nothing forces a third. The Spirit is the extra price, and the
  Stage-B binitarian separation proves three is exactly this price: Agape plus
  Word alone leave a two-center Godhead legal.

  Refusal model (the binitarian world): Agape + Word, no Spirit modality —
  a two-person Godhead is machine-checked consistent (separation C514, `{}`).

  Philosophical cost: God as *ecstatic community*, not merely as lover-and-
  beloved. A reader who stops at the procession of the Word rejects this axiom
  — and with it the *full* Trinity, keeping a binitarian reading. -/
axiom AxProcessionSpirit :
    ∃ σ : DivineHypostasis,
      IsSpirit σ ∧ Subsists σ ∧ σ ≠ the_father ∧ (∀ w : DivineHypostasis, IsWord w → σ ≠ w)

/-- The Spirit, extracted by choice. -/
noncomputable def the_spirit : DivineHypostasis := Classical.choose AxProcessionSpirit

/-- The Spirit is the returning gift (role). -/
theorem the_spirit_is_spirit : IsSpirit the_spirit :=
  (Classical.choose_spec AxProcessionSpirit).1

/-- The Spirit subsists in the divine reality. -/
theorem the_spirit_subsists : Subsists the_spirit :=
  (Classical.choose_spec AxProcessionSpirit).2.1

/-- The Spirit is other than the source. -/
theorem the_spirit_ne_father : the_spirit ≠ the_father :=
  (Classical.choose_spec AxProcessionSpirit).2.2.1

/-- The Spirit is other than every Word (role-distinction, second half). -/
theorem the_spirit_ne_any_word : ∀ w : DivineHypostasis, IsWord w → the_spirit ≠ w :=
  (Classical.choose_spec AxProcessionSpirit).2.2.2

/-- The Spirit is other than the Word (instantiated at the beloved). -/
theorem the_spirit_ne_beloved : the_spirit ≠ the_beloved :=
  the_spirit_ne_any_word the_beloved AxProcessionWord

-- ============================================================================
-- Section 3: The corridor (C507–C509)
-- ============================================================================

/-- Essential self-giving has a necessary object (C507, PROVEN↑): under the
    datum, the source's love reaches a distinct personal center that *subsists*
    — its being is the necessary divine reality. The object is thereby as
    necessary as the love itself: it is not fetched from the contingent realm
    the WALLs guard (C481/C482, C503), it is in the Godhead by declaration.
    Footprint: `{Subject, AxAgapeEssence, Classical.choice}` (the datum; `Subject`
    and `Classical.choice` are vocabulary — the extractor's choice operator). -/
theorem essential_love_has_necessary_object :
    ∃ f o : DivineHypostasis, f ≠ o ∧ Subsists f ∧ Subsists o ∧ DivineLove f o := by
  refine ⟨the_father, the_beloved, the_beloved_distinct.symm, the_father_subsists,
    the_beloved_subsists, the_source_loves_the_beloved⟩

/-- The beloved is not a creature (C508): every subsistent divine center has,
    in place of a contingent reality, the necessary ground — and is no atom.
    This is the Godhead-level answer to WALL 2: the beloved is not a
    `ContingentSubjectKind` subject (it is not a `Subject` at all), it does not
    live in a contingent entity, and it is not an atom — the three creature
    shapes of Γ's `Entity` ontology. **Provable, not priced**: it follows from the
    vocabulary once subsistence holds, which is why the row is PROVEN and not
    PROVEN↑ — no META axiom is paid here.
    Footprint: `{NecessarySubjectKind, Subject}` (vocabulary only, via
    `ofGround_necessary` and `necessary_not_contingent`). -/
theorem agape_beloved_is_not_creature {o : DivineHypostasis} (h : Subsists o) :
    ¬ ContingentEntity o.deiformEntity ∧ (∀ n : Nat, o.deiformEntity ≠ Entity.ofAtom n) := by
  constructor
  · intro hc
    have hn : NecessaryEntity o.deiformEntity := by
      dsimp [Subsists, divineReality] at h
      rw [h]
      exact ofGround_necessary
    exact necessary_not_contingent _ hn hc
  · intro n hn
    dsimp [Subsists, divineReality] at h
    rw [h] at hn
    cases hn

/-- The divine object subsists in the Godhead (C509): a subsistent center is a
    divine center — `is_divine o divineReality` holds by definition of
    subsistence. The step the Augustinian route had to leave at "step 6" is
    here *stated* as the content of `Subsists` and discharged. **Provable, not
    priced**: pure unfolding, so the row is PROVEN, not PROVEN↑.
    Footprint: `{Subject}` (vocabulary only: `is_divine o divineReality` names
    the `Entity` sort, whose ground constructor carries `Subject`). -/
theorem divine_object_subsists_in_godhead {o : DivineHypostasis} (h : Subsists o) :
    is_divine o divineReality := by
  dsimp [Subsists, is_divine, divineReality] at h ⊢
  exact h

/-- The centers are each in the divine reality (helpers for the inhabitation). -/
theorem the_father_is_divine : is_divine the_father divineReality := by
  dsimp [is_divine]
  exact the_father_subsists

/-- The centers are each in the divine reality (helpers for the inhabitation). -/
theorem the_beloved_is_divine : is_divine the_beloved divineReality := by
  dsimp [is_divine]
  exact the_beloved_subsists

/-- The centers are each in the divine reality (helpers for the inhabitation). -/
theorem the_spirit_is_divine : is_divine the_spirit divineReality := by
  dsimp [is_divine]
  exact the_spirit_subsists

-- ============================================================================
-- Section 4: The main theorem (C510)
-- ============================================================================

/-- The canonical inhabitation: the source, the beloved and the Spirit, with
    pairwise distinctness and mutual relational distinction, sharing the one
    divine reality. `relational_distinction` is taken as distinctness itself —
    the minimal, content-honest reading available at kernel level. -/
noncomputable def trinitarian_inhabitation : TrinitarianStructure DivineHypostasis Entity :=
  { P1 := the_father
    P2 := the_beloved
    P3 := the_spirit
    distinct_12 := the_beloved_distinct.symm
    distinct_23 := the_spirit_ne_beloved.symm
    distinct_13 := the_spirit_ne_father.symm
    divine_reality := divineReality
    is_divine := is_divine
    divine_1 := the_father_is_divine
    divine_2 := the_beloved_is_divine
    divine_3 := the_spirit_is_divine
    relational_distinction := fun (a b : DivineHypostasis) => a ≠ b
    rel_12 := the_beloved_distinct.symm
    rel_23 := the_spirit_ne_beloved.symm
    rel_13 := the_spirit_ne_father.symm
  }

/-- Agape entails tripersonality (C510, PROVEN↑): under the three disclosed
    Agape axioms — the datum, the procession of the Word, the procession of
    the Spirit — there is a `TrinitarianStructure` (C108) on the divine sort
    whose three distinct personal centers are *exactly* the source, the
    beloved-as-Word and the returning Spirit, all sharing the one divine
    reality. The witness form is `∃ t` because `TrinitarianStructure` is a
    `structure` in `Type`, not a `Prop` (the `∃ (_t : TrinitarianStructure Subj
    Ent), True` idiom of `ConditionalTheology`); the role conjuncts are in the
    statement so that the whole price saturates the footprint.

    Not a derivation: the case rests on three declared META premises, and
    every cheaper reading (Narcissus, creature-love, attribute-love, binitarian)
    is kept machine-checked consistent by the Stage-B separations. Unicity is
    preserved: one divine reality, three centers inside it (C212's
    non-collapse). The Word here is not the Incarnation (F8 untouched).
    Footprint: `{Subject, AxAgapeEssence, AxProcessionWord, AxProcessionSpirit,
    Classical.choice}`. -/
theorem agape_entails_tripersonality :
    ∃ t : TrinitarianStructure DivineHypostasis Entity,
      t.P1 = the_father ∧ t.P2 = the_beloved ∧ t.P3 = the_spirit ∧
        IsWord the_beloved ∧ IsSpirit the_spirit :=
  ⟨trinitarian_inhabitation, rfl, rfl, rfl, AxProcessionWord, the_spirit_is_spirit⟩

/-- A subsistent center is a necessary being (C518, PROVEN): the Agape datum
    puts the divine centers inside the necessary realm, not merely somewhere
    real. The one-line corollary of C508's first conjunct, isolated and named
    because it is what lets the NECESSARY audit's two-genera closure (C516)
    apply to the Trinity: a subsistent `DivineHypostasis`'s `deiformEntity` is
    either the ground or a necessary-kind subject's correlate — and by
    `Subsists` it is the ground, so the centers sit in the *first* genus.

    **Provable, not priced**: `Subsists` is location-equality to
    `divineReality = Entity.ofGround`, and `ofGround_necessary` is vocabulary.
    No META axiom is paid; the row is the same content as C508 read under the
    modal vocabulary, and it is filed separately because the author's position
    (the ground *is* personal) needs the modal form to be legible.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem subsisting_centre_is_necessary {d : DivineHypostasis} (h : Subsists d) :
    NecessaryEntity d.deiformEntity := by
  dsimp [Subsists, divineReality] at h
  rw [h]
  exact ofGround_necessary

/-- Co-subsistence is co-location (C519, PROVEN): two subsistent centers have
    the *same* location-entity. Read with C518 this is the "one reality, three
    centers" of C510 in the modal vocabulary, isolated so the coincidence is a
    named, reusable fact rather than a side condition. Location identity only —
    no claim about shared nature, property or act.
    Footprint: `{Subject}`. -/
theorem co_subsistence_is_co_location {a b : DivineHypostasis} (ha : Subsists a) (hb : Subsists b) :
    a.deiformEntity = b.deiformEntity := by
  dsimp [Subsists, divineReality] at ha hb
  exact ha.trans hb.symm

/-- The three centers are necessary, and one necessary reality (C520, PROVEN↑):
    the instantiations of C518 at the father, the beloved and the Spirit, plus
    the coincidence of their location-entities. The last two conjuncts are
    C519; the first three are the modal reading of C510's one-reality field.
    Coincidence of location only — consubstantiality of natures is **not**
    claimed and not proved here; it is not in the vocabulary of the sort, and
    the non-collapse of C212 is preserved (three distinct centers, one reality).
    Footprint: `{NecessarySubjectKind, Subject, AxAgapeEssence, AxProcessionSpirit,
    Classical.choice}`. -/
theorem the_three_centres_are_one_necessary_reality :
    NecessaryEntity the_father.deiformEntity ∧
      NecessaryEntity the_beloved.deiformEntity ∧
      NecessaryEntity the_spirit.deiformEntity ∧
      the_father.deiformEntity = the_beloved.deiformEntity ∧
        the_beloved.deiformEntity = the_spirit.deiformEntity :=
  ⟨subsisting_centre_is_necessary the_father_subsists,
   subsisting_centre_is_necessary the_beloved_subsists,
   subsisting_centre_is_necessary the_spirit_subsists,
   co_subsistence_is_co_location the_father_subsists the_beloved_subsists,
   co_subsistence_is_co_location the_beloved_subsists the_spirit_subsists⟩

end Logos.DivineAgape

-- ---------------------------------------------------------------------------
-- Axiom footprint audit (as of 2026-09-29, after Stage A):
--   C507 (essential_love_has_necessary_object) .. {Subject, AxAgapeEssence, Classical.choice}
--   C508 (agape_beloved_is_not_creature) ...... {NecessarySubjectKind, Subject}
--   C509 (divine_object_subsists_in_godhead) .. {Subject}
--   C510 (agape_entails_tripersonality) ....... {Subject, AxAgapeEssence,
--                                                AxProcessionWord,
--                                                AxProcessionSpirit,
--                                                Classical.choice}
-- ---------------------------------------------------------------------------
#print axioms Logos.DivineAgape.essential_love_has_necessary_object
#print axioms Logos.DivineAgape.agape_beloved_is_not_creature
#print axioms Logos.DivineAgape.divine_object_subsists_in_godhead
#print axioms Logos.DivineAgape.agape_entails_tripersonality
#print axioms Logos.DivineAgape.the_father_subsists
#print axioms Logos.DivineAgape.the_beloved_subsists
#print axioms Logos.DivineAgape.the_spirit_subsists
#print axioms Logos.DivineAgape.subsisting_centre_is_necessary
#print axioms Logos.DivineAgape.co_subsistence_is_co_location
#print axioms Logos.DivineAgape.the_three_centres_are_one_necessary_reality