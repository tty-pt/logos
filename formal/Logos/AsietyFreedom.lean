/-
# Logos.AsietyFreedom — asiety from Act-free weak choice, and the ground's sharing of it

## The thesis

> **Weak choice, in the Act-free sense, already yields asiety. Because the ground of reality
> grounds freedom and not only entities, its freedom is shared: true choice and `AsietyFreeWill`
> obtain for those it grounds.**

Two steps of very different prices, kept apart on purpose.

**L1 is axiom-free.** The Act-free weak choice is `GenuineNormativity`
(`IndubitableNormativeFreeWill.lean:84`), whose fields are

    opposition : Incompatible p q ∧ p ≠ q          (`:72`)
    address    : Means s p ∧ Means s q            (`:78`)

There is no `Act` and no `Initiates` in either field — `Act s p := Means s p ∧ ∃ w w',
Initiates s w w' p` is the act-level notion (`Agency.lean:155`) and is absent here. So
`GenuineNormativity s p q → Asiety (EntityOf s)` needs only `Means`, plus the frame's
`ContestedContent` (`{}`). This is the step the author asked for first, and it carries no
stipulation, no `Act`, no `Initiates`, and no `AxTwoSubjects`.

**L2 is a declared stipulation, not a derivation.** It cannot be derived, for three independent
reasons, all recorded in `AsietyFreedom.md` §2.2:

1. `GroundsEntity` is **vacuous**: `EntityMeans Entity.ofGround p` is `True` by the
   world-rigid constructor's match arm, so `ground_grounds_every_entity` is
   `intro p _; exact True.intro` (`LovesAsGround.lean:194`) and the ground even grounds
   meaningless entities. The module that declares it says the transfer "is vacuous, which is
   exactly the point".
2. `GroundsRightWrong` is **definitionally** `∃ p q, Chooses s p q` (C168) — subject-level,
   already collapsed to free will, carrying no ground content.
3. The **substantive** grounding relation is `BLOCKED` with a named lemma (C228).

So `AsietyFreedomOfGround` is registered as a **definitional stipulation ◈** in
`Stipulations.lean` with `Tag: META`, following the precedent of
`operatesAt_presencePlusObtaining`. Stipulations do not enter the declared-axiom tally: the count
stays 25 (VOCAB 14 / SEM 7 / META 4), and the price is machine-checked by the `{}` countermodels
in §3 below.

## What this module does not claim

- **Not an existence theorem.** The right/wrong fact `Core.rightWrongDistinction : ¬ N_T ∧ ¬ N_F`
  (`:145`) is a fact about *contents*; it quantifies over no `Subject`, and
  `rightWrongFactYieldsNoChooser` proves it is compatible with a meaning-vocabulary in which no
  subject means anything. So the Creator-sharing step is **conditional**, and its existence half is
  recorded as not derivable rather than asserted. The pre-existing unconditional route still costs
  `AxTwoSubjects` (META), as `AsieticChoice.trueChoice_exists` already discloses.
- **Not a claim that the ground chooses.** `AsietyFreedomOfGround` quantifies over *subjects* and
  says the ground's freedom reaches them. It does not make the ground a chooser: C285
  (`ground_is_not_a_true_chooser`) stands, and `groundIsNotASharerOfAsietyFreeWill` restates it in
  this module's vocabulary so the two cannot be read as contradicting each other.
- **Not a strengthening of `TrueChoice`.** `ContestedContent` is a global frame fact and
  `strongChoice_iff_trueChoice` (C265) is `PROVEN`; `frameContingencyDoesNotBindAPair` records why
  a per-pair conjunct is not available for free (`Incompatible` is `Prop`-level while
  `NecessarilyTrue` is `Form`-level, and the library has no `Prop ↔ Form` bridge).
- **Not the disappearance of the `?` at `base.txt:460`.** That step is still discharged under the
  `ClaimsCorrect` premise, and the bare form is still refuted (C273/C274). L1 routes around it
  rather than closing it: it starts from a hypothesis that already contains both horns.

## A disclosure about `indubitable_normative_freeWill`

`indubitable_normative_free_will` (`:115`, `{Means, Subject}`) is a **sub-formula extraction**, not
a derivation. Its hypothesis unfolds to `Incompatible p q ∧ p ≠ q ∧ Means s p ∧ Means s q`; the
proof uses `.1`s and **discards `p ≠ q`**. Its conclusion `Chooses s p q` is a reordering of three
of the four conjuncts, and `FreeWill s` is that existentially closed. The footprint is correct —
it records that the structure's fields are `Means` — but it does not measure a derivation from
independent premises. It is the right row in the ledger for what it is, and it is not evidence
that a weak principle was strengthened into a strong one.
-/
import Logos.Core
import Logos.Entity
import Logos.Agency
import Logos.Alternatives
import Logos.Choice
import Logos.RecoveredOntologicalGround
import Logos.NecessityEternity
import Logos.AsieticChoice
import Logos.IndubitableNormativeFreeWill
import Logos.Stipulations

namespace Logos.AsietyFreedom

open Logos.Core (N_T N_F rightWrongDistinction)
open Logos.Entity (Entity EntityOf)
open Logos.Agency (Subject Means)
open Logos.Alternatives (Incompatible)
open Logos.Choice (Chooses FreeWill)
open Logos.RecoveredOntologicalGround (GroundsEntity)
open Logos.NecessityEternity (ofGround_ne_ofSubject)
open Logos.AsieticChoice (ContestedContent contested_content OpenAlternative TrueChoice Asiety)
open Logos.IndubitableNormativeFreeWill (GenuineNormativity)

/-!
## Section 1: the stipulated predicate
-/

/-- The ground of reality is the ground of *freedom*, not only of entities: whatever it grounds
    participates in true choice at every incompatible pair, not merely at the pair the subject
    happens to be witnessed with.

    This is a **stipulation ◈** (`Tag: META`), registered as `asietyFreedom_ofGroundFreedom` in
    `Stipulations.lean`. It is not an axiom and does not move the declared-axiom count, and it is
    not derivable: `GroundsEntity` is vacuous, `GroundsRightWrong` is definitionally `FreeWill`
    (C168), and the substantive grounding relation is `BLOCKED` (C228).

    The `GroundsEntity` premise is retained because it is the library's own grounding relation,
    and it is **vacuous by construction** — `EntityMeans Entity.ofGround p` is `True`. All the
    weight therefore sits in the leading universal quantifier, and the countermodels below price
    exactly that quantifier.

    **Read the footprint with this in mind.** `{Means, Subject}` is *only* Γ's vocabulary: those
    are the two axioms the word `Subject` and the word `Means` carry, nothing more. The
    stipulation itself is **invisible to the kernel** — it is a `def`, so `#print axioms` cannot
    see it and no audit will ever flag it. That is exactly why it is registered as ◈ in
    `Stipulations.lean` and badged in the README: the badge is the only place the price is visible.
    Footprint: `{Means, Subject}` (vocabulary only; the stipulation is a `def`, not an `axiom`). -/
def AsietyFreedomOfGround : Prop :=
  ∀ (s : Subject) (p q : Prop), GroundsEntity Entity.ofGround (EntityOf s) →
    Asiety (EntityOf s) → TrueChoice s p q

/-- `AsietyFreeWill s`: `s`'s true freedom is the ground's freedom, shared with `s` — the
    ground-participation and the subject's own asiety are two different things conjoined, so this
    is not a repackaging of the `TrueChoice` it is used to derive.

    Sharing is *participation*, not identity: the subject does not become the ground, and the
    ground does not become a chooser (see `groundIsNotASharerOfAsietyFreeWill`).
    Footprint: `{Means, Subject}` (vocabulary only). -/
def AsietyFreeWill (s : Subject) : Prop :=
  AsietyFreedomOfGround ∧ Asiety (EntityOf s)

/-!
## Section 2: L1 — asiety from Act-free weak choice, with no axiom and no stipulation
-/

/-- **Asiety follows from the Act-free weak choice, with no axiom and no stipulation.** A subject
    addressed by genuine normativity is an asietic subject: its entity exhibits true freedom.

    This is the step the author asked for first, and it is the only axiom-free step in the chain.
    `GenuineNormativity` carries both horns in its `address` field (`Means s p ∧ Means s q`) and
    the incompatibility in `opposition.1`, so the sole content beyond them is the frame's
    `ContestedContent` — a `{}` fact. No `Act`, no `Initiates`, no `AxJudicativeBipolarity`, no
    `AxTwoSubjects`.

    Read honestly: it is a near-projection, because `AgentialDeonticAddress` already contains the
    co-signification. What it adds over `indubitable_normative_free_will` is the `ContestedContent`
    conjunct, i.e. the openness condition, and nothing else.
    Footprint: `{Means, Subject}`. -/
theorem weakChoice_implies_asiety {s : Subject} {p q : Prop}
    (h : GenuineNormativity s p q) : Asiety (EntityOf s) :=
  ⟨s, p, q, rfl, ⟨⟨h.address.1, h.address.2, h.opposition.1⟩, h.opposition.1, contested_content⟩⟩

/-- The same step, read in the `FreeWill` direction: Act-free weak choice already delivers
    `FreeWill`, and `weakChoice_implies_asiety` above delivers `Asiety` with the openness
    conjunct attached. Recorded separately so the two are not confused: neither of them is the
    `?` at `base.txt:460`, which remains discharged only under the `ClaimsCorrect` premise.
    Footprint: `{Means, Subject}`. -/
theorem weakChoice_implies_freeWill {s : Subject} {p q : Prop}
    (h : GenuineNormativity s p q) : FreeWill s :=
  ⟨p, q, ⟨h.address.1, h.address.2, h.opposition.1⟩⟩

/-!
## Section 3: the transfers, each carrying the stipulation
-/

/-- Under the stipulated ground-freedom, a subject the ground grounds and that is asietic makes a
    true choice at **every** incompatible pair — not only at the pair witnessing its asiety. This
    extension beyond the witness is the entire content of the stipulation and the reason it is not
    free (`asietyAloneDoesNotYieldTrueChoice`).

    The `GroundsEntity` premise is vacuous (`EntityMeans Entity.ofGround p` is `True`), so what
    remains after the vocabulary is exactly the stipulated universal — and, being a `def`, it does
    not appear in the footprint at all.
    Footprint: `{Means, Subject}` (vocabulary only; the stipulation is a `def`, not an `axiom`). -/
theorem asietyFreedom_yields_trueChoice (h : AsietyFreedomOfGround) {s : Subject} {p q : Prop}
    (hG : GroundsEntity Entity.ofGround (EntityOf s)) (hA : Asiety (EntityOf s)) :
    TrueChoice s p q :=
  h s p q hG hA

/-- **The ground's freedom, shared: an asietic subject the ground grounds has `AsietyFreeWill`.**
    This single theorem is both halves of the author's step, and they are one step because they
    are one inference: the ledger reads the mechanism ("the ground's freedom, shared"), the
    author's phrasing reads the same inference as "which is shared with us by the creator". Two
    declarations for it would be one proposition wearing two C-ids, so there is one.

    The `GroundsEntity` premise is **vacuous** (`EntityMeans Entity.ofGround p` is `True`), which
    is why it is named `_hG`: it is retained because it is the library's own grounding relation,
    and it is named as vacuous rather than deleted so that the `{}` footprint cannot be mistaken
    for depth (rule R3).
    Footprint: `{Means, Subject}` (vocabulary only). -/
theorem asietyFreedom_yields_asietyFreeWill (h : AsietyFreedomOfGround) {s : Subject}
    (_hG : GroundsEntity Entity.ofGround (EntityOf s)) (hA : Asiety (EntityOf s)) :
    AsietyFreeWill s :=
  ⟨h, hA⟩

/-- `AsietyFreeWill` yields true choice — the direction the author described as "gives rise to
    true choice". The whole step rests on the stipulated first conjunct; the second conjunct
    supplies the witness. The `GroundsEntity` premise is vacuous again (R3), and is used here
    because the transfer does consume it, not merely to keep the signature uniform.
    Footprint: `{Means, Subject}` (vocabulary only). -/
theorem asietyFreeWill_yields_trueChoice {s : Subject} {p q : Prop} (h : AsietyFreeWill s)
    (hG : GroundsEntity Entity.ofGround (EntityOf s)) : TrueChoice s p q :=
  h.1 s p q hG h.2

/-!
## Section 4: the price of the stipulation, machine-checked
-/

/-- **Asiety at one witness does not deliver true choice everywhere — the stipulation is not
    free.** In this model a subject `s₀` has asiety (it means both horns of an incompatible pair
    and the frame's contested-content conjunct holds), while a second subject `s₁` lacks true
    choice at the very same pair. So `AsietyFreedomOfGround`'s universal quantifier over subjects
    is doing real work, and dropping it — the weaker existential reading, "the ground's freedom
    is shared with *some* one" — would be a strictly cheaper stipulation that still delivers the
    Creator-sharing step.

    This is the counterpart of that weaker reading, recorded so the price of the strong one is
    visible rather than assumed.
    Footprint: `{}`. -/
theorem asietyAloneDoesNotYieldTrueChoice :
    ∃ (S : Type) (M : S → Prop → Prop) (I : Prop → Prop → Prop) (C : Prop) (s₀ s₁ : S)
      (p q : Prop),
      I p q ∧ M s₀ p ∧ M s₀ q ∧ C ∧
        ¬ (M s₁ p ∧ M s₁ q ∧ I p q ∧ C) := by
  refine ⟨Bool, ?_, ?_, True, false, true, True, False, ?_⟩
  · intro s _; exact s = false
  · intro _ _; exact True
  refine ⟨trivial, rfl, rfl, trivial, ?_⟩
  intro h
  have hEq : (true = false) := h.1
  exact Bool.noConfusion hEq

/-- **The frame's contingency does not bind a given pair**, which is why `TrueChoice ≡ Chooses`
    (C265) is forced rather than lazy. `ContestedContent` is `Form`-level
    (`∃ τ, ¬ NecessarilyTrue τ ∧ ¬ NecessarilyFalse τ`) while `Incompatible` is `Prop`-level, and
    the library has no `Prop ↔ Form` bridge (`AsieticChoice.lean:117-119`).

    The countermodel therefore carries a **withheld** per-pair predicate `PairContested`, holding
    nowhere, next to a global `C` that holds. A model importing Γ's own vocabulary cannot
    express this, because the per-pair binding is precisely what is in dispute; the withholding is
    what makes the countermodel admissible, and it is stated in the signature rather than glossed.
    Footprint: `{}`. -/
theorem frameContingencyDoesNotBindAPair :
    ∃ (C : Prop) (PairContested : Prop → Prop) (p : Prop), C ∧ ¬ PairContested p := by
  refine ⟨True, fun _ => False, True, trivial, ?_⟩
  intro h
  exact h

/-- The right/wrong fact — "right and wrong cannot not exist",
    `Core.rightWrongDistinction : ¬ N_T ∧ ¬ N_F` (`Core.lean:145`, `{}`) — is a fact about
    **contents**. It is compatible with a meaning-vocabulary in which no subject means anything,
    so it cannot by itself deliver the co-signification of any pair, and the existence half of the
    Creator-sharing step is not derivable from it.

    The first conjunct is the author's named fact, already `PROVEN` in pure logic; the second
    **exhibits** a one-element subject sort and a meaning-vocabulary that means nothing, in which
    no subject means any pair. They are joined because the joint statement is the honest one: the
    fact holds, and it is silent on choosers.

    A note on the shape. The second conjunct is `∃`, not `∀` over vocabularies: no `False` follows
    from `M s p` for an arbitrary `M`, so a universally quantified form would have been unsound
    rather than strong. A countermodel *exhibits* a vocabulary; it does not range over all of them.
    Footprint: `{}`. -/
theorem rightWrongFactYieldsNoChooser :
    (¬ N_T ∧ ¬ N_F) ∧
      ∃ (S : Type) (M : S → Prop → Prop), ¬ (∃ s : S, ∃ p q : Prop, M s p ∧ M s q) :=
  ⟨rightWrongDistinction, Unit, fun _ _ => False, fun h => by
    obtain ⟨s, p, q, hM⟩ := h
    exact hM.1⟩

/-- **Coherence with the previous batch: the ground is still not a chooser.** C285 proved
    `¬ ∃ s, EntityOf s = Entity.ofGround`; this restates it in the present vocabulary, so the new
    chain cannot be read as putting the ground inside the chooser inventory. `AsietyFreedomOfGround`
    quantifies over subjects and says the ground's freedom *reaches* them — participation, not
    identity. `AsietyFreedom` is a characteristic of the ground **as ground**, and the ground
    remains canonically aseitous-but-not-asietic under C284's honest conditional.

    The footprint is `{Means, Subject}` — vocabulary only. It is vocabulary only because
    `AsietyFreeWill` mentions `Subject` and `Means`, not because the exclusion is deep: the proof
    is C285's `ofGround_ne_ofSubject` and nothing more.
    Footprint: `{Means, Subject}`. -/
theorem groundIsNotASharerOfAsietyFreeWill :
    ¬ ∃ s : Subject, EntityOf s = Entity.ofGround ∧ AsietyFreeWill s :=
  fun ⟨s, h, _⟩ => absurd h (Ne.symm (ofGround_ne_ofSubject s))

/-!
## Section 5: the module in one line
-/

/-- The chain in one conjunction: Act-free weak choice yields asiety with no axiom and no
    stipulation; everything from `AsietyFreedom` onward carries the ◈ META stipulation; the
    existence of a chooser is not free; and the ground is still not one.
    Footprint: `{Means, Subject}` (vocabulary only; the ◈ stipulation is a `def`, so no audit can
    see it). -/
theorem asietyFreedom_summary :
    (∀ (s : Subject) (p q : Prop), GenuineNormativity s p q → Asiety (EntityOf s)) ∧
      ((h : AsietyFreedomOfGround) → ∀ (s : Subject) (p q : Prop),
        GroundsEntity Entity.ofGround (EntityOf s) → Asiety (EntityOf s) → TrueChoice s p q) ∧
      (∀ (s : Subject) (p q : Prop), AsietyFreeWill s →
        GroundsEntity Entity.ofGround (EntityOf s) → TrueChoice s p q) ∧
      (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) ∧
      (¬ ∃ s : Subject, EntityOf s = Entity.ofGround ∧ AsietyFreeWill s) :=
  ⟨fun _s _p _q h => weakChoice_implies_asiety h,
   fun h s p q hG hA => h s p q hG hA,
   fun s p q h hG => h.1 s p q hG h.2,
   rightWrongFactYieldsNoChooser.1,
   groundIsNotASharerOfAsietyFreeWill⟩

/-!
## Section 6: the derived side at maximum strength, and the two named obligations

Section 2 proved `Asiety` from weak choice; Section 3 spent ◈ to extend it. This section closes
the gap in both directions at once, so the ledger records the *exact* width of what the stipulation
buys rather than an impression of it.

Three additions, all strictly additive — no earlier statement is weakened, narrowed, or discharged:

- **C300** states the derived side at its *actual* maximum: `GenuineNormativity s p q` already
  yields `TrueChoice s p q` **at the specified pair**, axiom-free. This is the true maximum.
- **C297/C298** restate the same boundary routed through `Asiety`, as a *witnessed* pair. They are
  **strictly weaker than C300** as statements. An earlier version of this section called them "at
  full strength"; that was false, was withdrawn on 2026-09-26, and is recorded in §0.6.8. They are
  retained rather than deleted, because removing ledger rows would itself be a weakening.
- **C299** states the price on the other side, and is the machine-checked reason the ◈ step
  cannot be discharged from a grounding premise of containment shape.

`groundFreedomSharedWithSomeone` then names the existence obligation so the frontier row can cite
a name rather than quote prose — the `F11` precedent.
-/

/-- **The derived side at its actual maximum: true choice, axiom-free, at the *specified* pair.**

    This is the strongest statement reachable from `GenuineNormativity` alone, and it is
    **stronger than C297** — C297 existentially closes the pair and so discards *which* pair the
    weak choice was about. Read C300 first; C297 below is retained (not deleted) as the same fact
    routed through `Asiety`, and is strictly weaker as a statement.

    **How little work this is.** With
    - `Chooses s p q := Means s p ∧ Means s q ∧ Incompatible p q` (`Choice.lean:116`),
    - `OpenAlternative p q := Incompatible p q ∧ ContestedContent` (`AsieticChoice.lean:132`),
    - `DeonticOpposition p q := Incompatible p q ∧ (p ≠ q)` (`IndubitableNormativeFreeWill.lean:72`),
    - `AgentialDeonticAddress s p q := Means s p ∧ Means s q` (`:78`),

    the structure's two fields are **literally** the two conjuncts of `Chooses`, so `h` assembles
    `TrueChoice s p q` outright. The only input not already inside `h` is the global frame fact
    `ContestedContent`, supplied by the `{}` theorem `contested_content`. So the whole of L1's
    "axiom-free" content is: *the hypothesis already contains the choice, and the world is
    contingent.* That is the deflationary reading of §0.2 in its sharpest form — the `p ≠ q` field
    is not even needed.

    **The limit is part of the statement, not a caveat.** This gives true choice at the *given*
    pair `p q`. The author's claim needs it at **every** incompatible pair, and that extension is
    exactly what `AsietyFreedomOfGround` asserts. So the price ◈ pays is narrower — and worse —
    than C297's framing suggested: ◈ buys *extension from the given pair to all pairs*, not the
    existence of a pair, which was already free. See §0.6.8.
    Footprint: `{Means, Subject}`. -/
theorem weakChoice_yields_trueChoice {s : Subject} {p q : Prop}
    (h : GenuineNormativity s p q) : TrueChoice s p q :=
  ⟨⟨h.address.1, h.address.2, h.opposition.1⟩, ⟨h.opposition.1, contested_content⟩⟩

/-- **The derived side, via `Asiety`: axieticity carries witnessed true choice.**

    `Asiety (EntityOf s)` yields `∃ p q, TrueChoice s p q` — axiom-free, with no `Act`, no
    `Initiates`, no `AxTwoSubjects` and **no ◈**.

    **Correction (2026-09-26): this is *not* the derived side "at full strength", and an earlier
    version of this docstring said so. It is strictly weaker than
    `weakChoice_yields_trueChoice` (C300)**, which delivers `TrueChoice` at the *specified* pair
    instead of at some pair. C300 is the true maximum; this theorem is kept because it is the same
    fact stated in the form the `Asiety` route needs, and because deleting ledger rows would itself
    be a weakening.

    The content is `Asiety`'s own unfolding, `Asiety e := ∃ s, ∃ p q, e = EntityOf s ∧
    TrueChoice s p q` (`AsieticChoice.lean:147`); the only work done here is the injectivity of
    `EntityOf`, which is constructor injectivity and nothing more.

    **The limit is part of the statement, not a caveat.** This delivers true choice at the
    *witnessing* pair only. The author's claim needs `TrueChoice s p q` at **every** incompatible
    pair, and that extension is precisely what `AsietyFreedomOfGround` asserts and precisely what
    `asietyAloneDoesNotYieldTrueChoice` (C292) and `groundingCannotDeliverTrueChoice` (C299)
    price. Nothing here discharges, softens, or substitutes for the stipulation; it fixes the
    boundary so the price is measurable.
    Footprint: `{Means, Subject}`. -/
theorem asiety_yields_witnessed_trueChoice {s : Subject} (h : Asiety (EntityOf s)) :
    ∃ p q : Prop, TrueChoice s p q := by
  obtain ⟨s', p, q, hEq, hTC⟩ := h
  have hinj : s = s' := Entity.ofSubject.inj hEq
  subst hinj
  exact ⟨p, q, hTC⟩

/-- The same derived side in the `FreeWill` direction, which is the form the author's sentence
    actually needs for "the ground's freedom, shared". Axiom-free, no ◈ — and equally bounded:
    `FreeWill s` is `∃ p q, Chooses s p q`, so it too is a *witnessed* pair, not every pair.
    Footprint: `{Means, Subject}`. -/
theorem asiety_yields_freeWill {s : Subject} (h : Asiety (EntityOf s)) : FreeWill s := by
  obtain ⟨p, q, hTC⟩ := asiety_yields_witnessed_trueChoice h
  exact ⟨p, q, hTC.1⟩

/-- **The price, in its strongest available form: no grounding premise of containment shape can
    deliver true choice to a subject that lacks it.**

    This is the machine-checked reason the ◈ step is `BLOCKED` rather than merely unasserted, and
    it is stated over *any* relation of `GroundsEntity`'s shape rather than over Γ's particular
    one, so it is not an artefact of the vacuity at `LovesAsGround.lean:194`. The countermodel
    grants, in full:

    - a ground `g` whose meaning-capacity is **total** — `∀ v, M g v`, which is exactly what
      ◈ `ofGround_meansAll` buys for `Entity.ofGround`;
    - the containment premise **at every entity**, `∀ e v, M e v → M g v`, which is
      `GroundsEntity`'s definition verbatim and therefore holds at the second subject `s₁` as
      well;
    - a first subject `s₀` with `I p q`, `C` and both `Means` conjuncts — genuine asiety, witnessed
      at the pair `p q`;

    and it denies the conclusion **at that same pair** for `s₁`. So granting the grounding
    premise in full buys nothing: containment transfers *meaning-capacity*, never *which contents
    a subject means*, and only the latter delivers `TrueChoice`. This is why the disease is not
    the vacuity — it is that a content-transfer relation has no route to a choice of contents.

    Reading: the price of ◈ is not "our premise is weak". It is that the premise is of the wrong
    *kind*, and no amount of strengthening it in its own direction would help.
    Footprint: `{}`. -/
theorem groundingCannotDeliverTrueChoice :
    ∃ (E : Type) (M : E → Prop → Prop) (I : Prop → Prop → Prop) (C : Prop)
      (g s₀ s₁ : E) (p q : Prop),
      (∀ v : Prop, M g v) ∧
        (∀ e : E, ∀ v : Prop, M e v → M g v) ∧
        I p q ∧ C ∧ M s₀ p ∧ M s₀ q ∧
        ¬ (I p q ∧ M s₁ p ∧ M s₁ q ∧ C) :=
  ⟨Bool, fun e _ => e = false, fun _ _ => True, True, false, false, true, True, False,
   fun _ => rfl, fun _ _ _ => rfl, trivial, trivial, rfl, rfl, fun h => Bool.noConfusion h.2.1⟩

/-- **The Creator-sharing obligation, named** — frontier row F13, status `BLOCKED`.

    The author's sentence ends "*which is shared with us by the creator*", and "us" is an
    **existence** claim: someone shares it. This `def` gives that obligation a name, so the
    frontier row cites a declaration instead of quoting prose, following the `F11` precedent
    (`AsieticChoice.bareRejectedHornCoMeant`).

    It is `BLOCKED` and its derivation is **refuted, not merely open**: `Core.rightWrongDistinction`
    is a fact about contents that quantifies over no `Subject`, and
    `rightWrongFactYieldsNoChooser` (C294, `{}`) exhibits a meaning-vocabulary in which no subject
    means anything, so the fact does not deliver the existence of a sharer. The unconditional
    route still costs `AxTwoSubjects` (META), as `AsieticChoice.trueChoice_exists` discloses.

    Naming this does not advance it. It is here so the batch's strongest negative result is a
    citable frontier row rather than a footnote inside a module.
    Footprint: `{Means, Subject}` (vocabulary only; the obligation is a `def`, not an `axiom`). -/
def groundFreedomSharedWithSomeone : Prop :=
  ∃ (s : Subject), AsietyFreeWill s

end Logos.AsietyFreedom
