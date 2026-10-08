/-
# Logos.SecondPersonGoodAttempt — a second person does not prove the Good

Machine answer to the author's hypothesis: "If we can prove a second person, we
can prove the Good." The honest attempt delivers two `{}` countermodel witnesses
and a BLOCKED probe:

(1) `lone_will_is_vacuously_individual` (C501) — refutes the personhood-side
retorsion "if a will is individual but there is no one else to be individual
of, how can even a single person exist?". Γ's `IndependentWill` is uniqueness
over the class of *others*; for a lone will the `∀` empties and the conjunct
holds vacuously. A one-subject world whose subject is vacuously an individual
of rational nature with dominion is a legal model, so a single person is not
incoherent. The vacuity is disclosed: the lone will's individuality has NO
contrast content.

(2) `two_persons_do_not_force_good_obtains` (C502) — the plurality-instantiation
reading of C176: two distinct persons (`Unit ⊕ Unit`) can exist while no Good
obtains, because the missing datum is the *bearing value* (opaque
`BearingOf`), never the Other. Distinct persons plus an `unbearing` bearing
layer in every direction is a legal model.

(3) The love-lane probe (C503, BLOCKED, no declaration) — "the ground loves a
person" needs the exact missing lemma
`∃ s : Subject, ContingentSubjectKind s ∧ (∃ q : Prop, Means s q) ∧ Person s`
(WALL 2 instance), WALL 1 (`∃ p, GroundBearsGood Entity.ofGround (EntityOf s) p`),
and an Entity-level → Subject-level projection of the ground's love into
`BearingOf = benevolent` that Γ does not have and this attempt refuses to
force (see plan `OTHER.md`).

No axiom is added; nothing is forced. The moral Good remains PROVEN↑ under the
single disclosed META bridge C177, and C176/C499/C501/C502 are exactly what make
that bridge a disclosed price rather than a hidden premise.
-/

import Logos.PersonhoodOntologyAudit
import Logos.Value

namespace Logos.SecondPersonGoodAttempt

open Logos.PersonhoodOntologyAudit (PersonhoodVocab)
open Logos.PersonhoodOntologyAudit.Vocab
open Logos.Value (InterpersonalBearing)

/-- The lone-will model: a single subject (`Unit`) with a single trivial will
    faculty (`Unit`), meaning everything. Computed, not stipulated. The will is
    `()` and there is no second subject to share it — so every subject is the
    unique owner of its will. A `def`, not an axiom; the counterexample works
    by exhibiting a one-element model. Footprint: `{}`. -/
def LoneWillModel : PersonhoodVocab where
  Subj := Unit
  MeansRel := fun _ _ => True
  WillSort := Unit
  WillOf := fun _ => ()

/-- A lone will is vacuously individual (C501, COUNTERMODEL): there is a
    one-subject world in which that subject owns its will uniquely and is alone.

    Γ's `IndependentWill s := ∀ s' : Subject, s' ≠ s → subjectWill s' ≠
    subjectWill s` quantifies over the class of *others*; for a lone subject that
    class is empty, so the conjunct is vacuously true — exactly how "no one else
    has my fingerprints" is true in a one-person world. The retorsion "if a will
    is individual but there's no one else to be individual of, how can even a
    single person exist?" is therefore answered by vacuity: a single person CAN
    exist, and its individuality is well-formed, true, and content-empty.

    The vacuity caveat (house disclosure pattern, C457/C498): the lone will's
    individuality has NO contrast content — it refutes "a lone person cannot
    exist", not "a lone person is a robust person". Uniqueness is non-sharing;
    it is what GRANTS the "individual" conjunct, not what demands an Other.
    This is the personhood-side twin of the Solitary Universe
    (`AxiomNegationAudit.core_compatible_with_neg_a6`): `will_individuation`
    runs distinctness → will-distinction (it presupposes plurality, never
    generates it — `WillIndividuationAudit`, `{}`), and the corpus has no
    theorem `Person s → ∃ t, t ≠ s`.
    Footprint: `{}`. -/
theorem lone_will_is_vacuously_individual :
    ∃ (M : PersonhoodVocab) (s : M.Subj),
      IndependentWill M s ∧ ∀ t : M.Subj, t = s := by
  refine ⟨LoneWillModel, (), ?_, ?_⟩
  · intro s'
    intro hne
    cases s'
    exact False.elim (hne rfl)
  · intro t
    cases t
    rfl

/-- Two distinct persons do not force the Good (C502, COUNTERMODEL): distinct
    persons can exist while no Good obtains — for any subject vocabulary and
    any propositional act.

    This is the plurality-instantiation reading of C176 (`{}`): `Good`'s
    definiens is `∃ t ≠ s, Person t ∧ Helps s t ∧ ¬ Harms s t` and
    `Helps s t := BearingOf s t = InterpersonalBearing.benevolent` with
    `BearingOf` opaque. In the model below `S := Unit ⊕ Unit`, every
    `P s` holds (two genuine persons), yet every directed bearing is
    `unbearing`, so no pair `s ≠ t` is `benevolent`-joined and the Good never
    obtains. The answer to "if we can prove a second person, we can prove the
    Good" is therefore **no**: the missing datum is the bearing value, not the
    Other — a two-person `unbearing` world is a legal model (the census: no
    theorem or axiom in Γ concludes `BearingOf _ _ = benevolent` except the META
    bridge C177 itself). Free-signature, `{}` — a shape result, not a claim
    about Γ, and not a refutation of C178, which stays PROVEN↑ under C177.
    Footprint: `{}`. -/
theorem two_persons_do_not_force_good_obtains :
    ∃ (S : Type) (P : S → Prop) (B : S → S → InterpersonalBearing),
      (∃ s₁ s₂ : S, s₁ ≠ s₂ ∧ P s₁ ∧ P s₂) ∧
      ¬ ∃ (s : S) (a : Prop),
        ∃ t : S, t ≠ s ∧ P t ∧ B s t = InterpersonalBearing.benevolent ∧
          ¬ (B s t = InterpersonalBearing.harmful) := by
  refine ⟨Unit ⊕ Unit, fun _ => True, fun _ _ => InterpersonalBearing.unbearing, ?_, ?_⟩
  · refine ⟨Sum.inl (), Sum.inr (), ?_, trivial, trivial⟩
    intro h
    cases h
  · rintro ⟨_s, _a, _t, _hne, _hP, hb, _hNotHarmful⟩
    cases hb

end Logos.SecondPersonGoodAttempt

-- ---------------------------------------------------------------------------
-- Axiom footprint audit (expected: `{}` for both witnesses)
-- ---------------------------------------------------------------------------
#print axioms Logos.SecondPersonGoodAttempt.lone_will_is_vacuously_individual
#print axioms Logos.SecondPersonGoodAttempt.two_persons_do_not_force_good_obtains