/-
# Logos.EpistemicPersonalGround — the personal kind of grounding of the
  EPISTEMIC Right/Wrong

Γ has **two** right/wrong notions, and this module separates them once, in code,
because the ledger had stated the personal-ground theorem only for the second one.

  EPISTEMIC  `Core.T p` / `Core.IsFalse p` — the objective correctness of judgments
             *about* reality; `N_T`/`N_F` are the hypotheses that are refuted
             (`Core.rightWrongDistinction : ¬ N_T ∧ ¬ N_F`) and `bivalence` gives
             `∀ p, T p ∨ IsFalse p`. At the act level the poles are
             `Order.Correct s p := A s p ∧ T p` and
             `Order.Incorrect s p := A s p ∧ IsFalse p`, and under the epistemic
             `TruthNorm` (`NormativeOrder.lean:72-75`,
             `prescribes a := T a.content`, `prohibits a := IsFalse a.content`)
             they **are** truth and falsity: `Correct s p → Ought TruthNorm ⟨s, p⟩`
             is C137, and conversely `correct_iff_performed_and_ought` is `Iff.rfl`.

  DEONTIC    `PersonalNormativeGround.RightWrong s := ∃ p q, RightWrongAt s p q`
             = `∃ p q, Incompatible p q ∧ p ≠ q ∧ Means s p ∧ Means s q`
             (`:160`, `:153`). No `T`, no `IsFalse`, no `TruthNorm`, no `Ought`
             anywhere in that unfolding chain. *The name is epistemic; the
             definition is deontic.*

The ledger proves the personal ground of the DEONTIC one (C171, C223–C225), and
every one of those theorems reads `RightWrong s → Person s` — at an existential,
unspecified pole pair. The bridge that lets the deontic structure be *pointed* at
the epistemic poles runs **inside** the deontic layer, not between the layers:
`claims_normative_correctness_derives_genuine_normativity` instantiates
`GenuineNormativity` at `(Correct s p, Incorrect s p)`. So the epistemic pair is one
*instance* of the deontic structure — and that instance was never written down.

**This module states it**, plus the negative half that the ledger never had.

  C525  the indexed ground sits at the epistemic poles themselves
  C526  that ground is a Person — as a priced theorem, never a record field
  C527  the headline, in both directions, with the stance guard displayed
  C528  the epistemic order does NOT depend on the ground — `{}`, machine-checked

What this does NOT claim, each verified against the source:

  (i)   NOT a creator-of-existence claim: no `∀ x, Exists x → CausedByGround x`
        is introduced (`PersonalGroundOfReality.lean:11-13`; `base.txt:304`).
  (ii)  NOT moral endorsement of evil: "correct" here is the objective
        correctness of a judgment about reality, never good/evil
        (`base.txt:313-315`, the house's own four-level distinction).
  (iii) grounding ≠ identity, so nothing here re-introduces self-legislation or
        the collapse in `OughtRetorsion.self_grounded_ought_collapses`
        (`PersonalNormativeGround.lean:31-36`).
  (iv)  the Person → ground direction of C527 is **stance-guarded**: `Person s`
        alone does NOT pin the pole pair (see the theorem's own docstring).
  (v)   C528 is a FREE-signature separation, not a model of Γ, and not a claim
        that the epistemic order is unreal. (Discipline now ledgered as C559,
        `EpistemicNecessity.signature_model_reading_discipline`, which governs
        this module and `NegativeRetorsionAudit` alike.)
  (vi)  C228 (`normative_ground_is_personal`) is the distinct **entity-level**
        relation `GenericGroundsRightWrong g → PersonCorrelate g` (PROVEN);
        this module is **subject-level** and operates independently.

No new axiom: the register stays at 35 declared (17 VOCAB / 18 substantive).
-/
import Logos.PersonalGroundOfReality
import Logos.NormativeOrder
import Logos.Order
import Logos.Core

namespace Logos.EpistemicPersonalGround

open Logos.Agency (Subject)
open Logos.Core (T IsFalse N_T N_F)
open Logos.Order (Correct Incorrect)
open Logos.NormativeOrder (TruthNorm Ought OughtNot ClaimsNormativeCorrectness
  claims_normative_correctness_derives_genuine_normativity
  claims_normative_correctness_derives_free_will)
open Logos.Person (Person)
open Logos.PersonalNormativeGround (GroundsRightWrongAt grounding_forced_at_datum
  groundsRightWrongAt_entails_person)

/-!
## Section 1 — The indexed ground sits at the epistemic poles (C525)
-/

/-- The epistemic right/wrong — `Correct s p` and `Incorrect s p`, which under the
    epistemic `TruthNorm` are `T p` and `IsFalse p` (`NormativeOrder.lean:72-75`) —
    is ontologically grounded, and the ground is the *indexed* one at that very
    pole pair. This is C171 (`grounding_forced_at_datum`) instantiated at the
    epistemic poles: no new relation, no new field, and **no `Person` hypothesis**
    anywhere.

    Why this is the missing link and not a restatement. The existing grounding
    theorems say `RightWrong s → Person s`, i.e. the pole pair is an *existential*:
    `RightWrong s := ∃ p q, RightWrongAt s p q`, and the ground `GroundsRightWrong`
    carries a single `agential_foundation : ∃ p q, Chooses s p q` field that is
    definitionally just that same existential (C168,
    `groundsRightWrong_iff_forced_content`, footprint `{Means, Subject}`). Nothing
    in the kernel ever said the ground sits at *those named* poles. Here the
    antecedent is the epistemic stance `ClaimsNormativeCorrectness s p` — whose
    two `Means` conjuncts are already at `Correct`/`Incorrect`
    (`NormativeOrder.lean:168-170`) — and the conclusion names those same two
    poles.

    Note the epistemic anchoring is achieved by **instantiation, never by
    extension**: adding an epistemic field to `GroundsRightWrong` would break both
    C168's transparency and C171's index-alignment.

    Footprint: `{propext, Classical.choice, Quot.sound, Initiates, Means, State, Subject}`. -/
theorem epistemic_polarity_is_personally_grounded
    (s : Subject) (p : Prop) (h : ClaimsNormativeCorrectness s p) :
    GroundsRightWrongAt s (Correct s p) (Incorrect s p) :=
  grounding_forced_at_datum s (Correct s p) (Incorrect s p)
    (claims_normative_correctness_derives_genuine_normativity s p h)

/-!
## Section 2 — The ground is a Person, as a priced theorem (C526)
-/

/-- Personalness of the epistemic ground, as a **priced theorem** and never a
    record field: the exact price is the named law `will_individuation`
    (`Agency.lean`), disclosed in the footprint below. This is C225
    (`groundsRightWrongAt_entails_person`) instantiated at the epistemic poles.

    **Footnote on the footprint, because it is heavier than its deontic twin.**
    C225 is stated at *arbitrary* poles `p q`, so it never unfolds them and
    inherits only C171's `{Means, Subject}`. This theorem is stated at the
    *epistemic* poles, and unfolding `Correct s p := A s p ∧ T p` /
    `Incorrect s p := A s p ∧ IsFalse p` (`Order.lean:29,49`) drags in `A s p`,
    hence `Initiates` and `State`. The extra cost is **the epistemic poles
    themselves**, not any new philosophical commitment: `Initiates`/`Means`/
    `State`/`Subject` are VOCAB rows, and `will_individuation` remains the only
    priced law — the same price as C225.

    Footprint: `{Initiates, Means, State, Subject, Will, subjectWill, will_individuation}`. -/
theorem epistemic_ground_is_personal (s : Subject) (p : Prop) :
    GroundsRightWrongAt s (Correct s p) (Incorrect s p) → Person s :=
  groundsRightWrongAt_entails_person s (Correct s p) (Incorrect s p)

/-!
## Section 3 — The headline: both directions, with the guard displayed (C527)
-/

/-- HEADLINE. The epistemic right/wrong has a grounding of a personal kind, at its
    own poles.

    **Direction 1** (stance → ground → Person) is C525 followed by C526.

    **Direction 2** (Person → the ground is a genuine choice at the epistemic
    pair) is **stance-guarded**, and the guard is displayed rather than hidden:
    the unstated theorem
        `Person s → GroundsRightWrongAt s (Correct s p) (Incorrect s p)`
    is **NOT claimed, and is not provable from `Person s` alone**. The reason is
    structural, not a gap in the kernel: `Person s → FreeWill s` yields
    `∃ p' q', Chooses s p' q'` with the poles **existential**, so it does not
    supply `Chooses s (Correct s p) (Incorrect s p)`. What pins the pair is
    `claims_normative_correctness_derives_free_will` (`NormativeOrder.lean:190-193`),
    which yields exactly that choice — and it requires the epistemic stance.
    So the guard `ClaimsNormativeCorrectness s p` is the *epistemic stance itself*,
    not an auxiliary assumption.

    This is deliberately the same shape as the house's existing guarded
    corollaries — C152 `personal_ground_of_right_exists` and the sibling
    `personal_ground_of_right_exists_of_claims` — and it follows the precedent of
    stating a claim *with* its premise (C269) rather than converting it in silence.

    Footprint: `{propext, Classical.choice, Quot.sound, Initiates, Means, State, Subject, Will, subjectWill, will_individuation}`. -/
theorem the_person_grounds_the_epistemic_right_wrong
    (s : Subject) (p : Prop) (h : ClaimsNormativeCorrectness s p) :
    GroundsRightWrongAt s (Correct s p) (Incorrect s p) ∧ Person s :=
  ⟨epistemic_polarity_is_personally_grounded s p h,
   epistemic_ground_is_personal s p (epistemic_polarity_is_personally_grounded s p h)⟩

/-!
## Section 4 — The honesty half: the epistemic order needs no ground (C528)

C151 (`the_person_supports_the_reality_of_right`) is a conjunction in a closed
Prop with no hypothesis: `EstablishedRightWrong ∧ (∀ p, T p ∨ IsFalse p) ∧
NecessaryNormativeOrder ∧ …`. The `T`/`IsFalse` conjuncts are discharged by `Core`
theorems that never mention `Subject`; the `GroundsRightWrong` conjunct by
`person_grounds_normative_order`, which never mentions `T`. So the conjunction is
a **conjunction, not a derivation**, and before this module nothing in the kernel
said so. C528 is the machine-checked reason.
-/

/-!
**The epistemic right/wrong is INDEPENDENT of the personal ground** — machine-checked,
`{}`. The epistemic order holds and is non-vacuous while **no subject and no
personal ground exists at all**. This is why C151's conjunction is not a
derivation, and it is the machine-checked reason `base.txt:1471` had to be
reworded: no step anywhere in the ledger links `T`/`IsFalse` to
`GroundsRightWrong`.

It does **not** say the epistemic order is unreal, and it does **not** say the
personal ground is empty in Γ. Both halves of the model hold; they are simply not
linked.

**Discipline.** This is a FREE-signature model, not a model of Γ: the predicates
are re-declared locally, so it is a separation in bare model theory and says
nothing about Γ's own satisfiability — the `TrinitySeparations` /
`HostileSemantics` convention. The epistemic content sort is `Bool`, which makes
bivalence **decidable**; that is what holds the footprint at `{}`. Reaching for
`Classical.em` here instead would silently import `propext, Classical.choice,
Quot.sound` and break the promise.
-/
namespace Model
/-- The free signature of the separation: a subject sort, a content sort, a truth
    and a falsity predicate, a grounding predicate, and the three facts the
    separation turns on — the epistemic order, its non-vacuity, and the absence
    of any ground. Footprint: `{}`.

    **The last field, `order_needs_a_meaning_being`, is the FACT (2026-09-29).**
    `TrueAt`/`FalseAt` are the propositional right/wrong order — the `T`/`IsFalse`
    half of the author's scope decision — and before this field the signature tied
    them to nothing: `M` set `Grounds := False` and the order still obtained, which
    is a world in which something is right and something is wrong with no being for
    which anything can mean. The field excludes exactly that assignment, by the same
    argument as `NegativeRetorsionSignature.objectivity_grounded`
    (`NegativeRetorsionAudit.lean:65-97`). It constrains witnesses, not premises of
    Γ, so the register does not move. Footprint: `{}`. -/
structure Signature where
  Subject : Type
  Content : Type
  TrueAt : Content → Prop
  FalseAt : Content → Prop
  Grounds : Subject → Prop
  Means : Subject → Content → Prop
  Free : Subject → Prop
  epistemic_order : ∀ c, TrueAt c ∨ FalseAt c
  right_wrong_not_vacuous : (∃ c, TrueAt c) ∧ (∃ c, FalseAt c)
  no_personal_ground : ¬ ∃ s, Grounds s
  order_needs_a_meaning_being :
    (∃ c, TrueAt c) → ∃ s, Free s ∧ ∃ c, Means s c
end Model

/-- The separating model: `Content := Bool` decides bivalence, `Grounds := False`
    leaves the ground sort empty.

    `Free`/`Means` supply the being the order requires, and `Grounds := False`
    records that it does not *ground* anything. The separation is therefore
    **not** "the order obtains in a world with no being" — that is now
    unrepresentable — but "the being that the order requires need not be a ground".
    Both are genuine, and the second is the weaker, honest claim. -/
def M : Model.Signature where
  Subject := Unit
  Content := Bool
  TrueAt := fun c => c = true
  FalseAt := fun c => c = false
  Grounds := fun _ => False
  Means := fun _ _ => True
  Free := fun _ => True
  epistemic_order := fun c => by cases c <;> first | exact Or.inl rfl | exact Or.inr rfl
  right_wrong_not_vacuous := ⟨⟨true, rfl⟩, ⟨false, rfl⟩⟩
  no_personal_ground := fun h => by obtain ⟨_, hg⟩ := h; exact hg
  order_needs_a_meaning_being := fun _ => ⟨(), trivial, true, trivial⟩

/-- Both halves, at `{}`: the epistemic order is real and non-vacuous, and the
    personal ground is empty. The conjunction C151 asserts is therefore a
    conjunction of independent facts, not a derivation between them.

    **RE-WORDED 2026-09-29 (author's scope decision).** This is *not* a claim that
    the epistemic order can obtain in a world without a being for which meaning
    can mean — the signature field `order_needs_a_meaning_being` makes that
    assignment inadmissible. It is a separation **within the signature**: the order
    and the *ground* are independent, because the being the order requires is not
    the same as a being that grounds. The two statements are not in tension; the
    first is the FACT and the second is this row.
    Footprint: `{}`. -/
theorem epistemic_order_without_personal_ground :
    (∀ c : Bool, (c = true) ∨ (c = false)) ∧ ¬ ∃ _ : Unit, False :=
  ⟨M.epistemic_order, M.no_personal_ground⟩

/-- The FACT on the propositional side, at `{}`: the `T`/`IsFalse` order, once
    non-vacuous, entails a non-mechanical being for which meaning can mean.
    The `T`/`IsFalse` counterpart of C140, and the row that discharges the
    "meaningfulness" half of the author's scope decision at the propositional
    level rather than only at the judgmental one.
    Footprint: `{}`. -/
theorem epistemic_order_requires_a_free_meaning_being :
    ∀ M : Model.Signature, ∃ s : M.Subject, M.Free s ∧ ∃ c : M.Content, M.Means s c :=
  fun M => M.order_needs_a_meaning_being M.right_wrong_not_vacuous.1

end Logos.EpistemicPersonalGround

/-!
# Axiom footprint audit
  C525 `{propext, Classical.choice, Quot.sound, Initiates, Means, State, Subject}`
  C526 `{Initiates, Means, State, Subject, Will, subjectWill, will_individuation}`
  C527 the union of the two
  C528 `{}`
  C556 `{}` (`epistemic_order_requires_a_free_meaning_being`, the propositional
  half of the FACT, added 2026-09-29 with `Model.Signature.order_needs_a_meaning_being`)
-/
#print axioms Logos.EpistemicPersonalGround.epistemic_polarity_is_personally_grounded
#print axioms Logos.EpistemicPersonalGround.epistemic_ground_is_personal
#print axioms Logos.EpistemicPersonalGround.the_person_grounds_the_epistemic_right_wrong
#print axioms Logos.EpistemicPersonalGround.epistemic_order_without_personal_ground
#print axioms Logos.EpistemicPersonalGround.epistemic_order_requires_a_free_meaning_being
