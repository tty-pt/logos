import Logos.DivineAgape

/-!
# The Trinity separations (C511–C514) — Stage B of the Agape case

Four axiom-free (`{}`) countermodels that close every reading of the Agape case
cheaper than the Trinity. Together with Stage A (`Logos.DivineAgape`, C504–C510)
they make the price of the case exact: *three is exactly the price of the Spirit*.

Each theorem ranges over a **free signature** — a shadow of the divine
vocabulary, not an instantiation of it. `DivineLove`, `IsWord` and `IsSpirit` are
`opaque` (`DivineAgape.lean:98,103,108`), so no model of Γ can replace them by
construction; the shadows are what makes each statement checkable at all. The
mirror is:

| divine sort/predicate | shadow |
| --- | --- |
| `DivineHypostasis` | `β` |
| `Subsists` | `Sub` |
| `DivineLove` | `Love` |
| `IsWord` | `IsW` |
| `IsSpirit` | `IsS` |
| `TrinitarianStructure` | "three pairwise-distinct subsisting centres" |

That last row is the shape every conclusion carries: `TrinitarianStructure`
(`ConditionalTheology.lean:307`, C108) is a structure of three pairwise-distinct
centres, so a model *without* a `p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ p₁ ≠ p₃` triple is a model
with no trinity — in the vocabulary of the mirror.

These are shape results, **not** claims about Γ's consistency and **not**
refutations of any declared axiom. C514 in particular is the axle of the whole
case: it shows that the two centres of the Agape datum *together with* the Word
bridge leave a legal two-centre (binitarian) Godhead, so the third centre is not
a consequence of anything cheaper than `AxProcessionSpirit`.
-/

namespace Logos.TrinitySeparations

/-- **No second centre (C511).** A Godhead whose love is purely self-directed is
consistent with the whole vocabulary, and in that world no two distinct centres
subsist — the source loves itself, and the shape of a trinity cannot be built.

    What this shows: `AxAgapeEssence` (C504) is a genuine *choice*, not a
    consequence of unicity — a world without a second centre is legal.

    What this does NOT do: it does not refute `AxAgapeEssence`. The Narcissus
    world **fails** the axiom's "distinct subsisting beloved" conjunct — that is
    exactly the point: the datum is not available for free, it is the price. Nor
    does it touch C510, which is a theorem *under* the datum.
    Footprint: `{}`. -/
theorem unitarian_self_love_gives_no_second_centre :
    ∃ (β : Type) (Sub : β → Prop) (Love : β → β → Prop),
      (∃ f, Sub f ∧ Love f f) ∧
      (∀ f o, Sub f → Love f o → o = f) ∧
      (¬ ∃ p₁ p₂ p₃ : β, Sub p₁ ∧ Sub p₂ ∧ Sub p₃ ∧ p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ p₁ ≠ p₃) := by
  refine ⟨Unit, fun _ => True, fun _ o => o = (), ?_, ?_, ?_⟩
  · exact ⟨(), trivial, rfl⟩
  · intro f o _hSub hLove
    cases f
    exact hLove
  · rintro ⟨p₁, p₂, p₃, _h1, _h2, _h3, h12, _h23, _h13⟩
    cases p₁
    cases p₂
    exact h12 rfl

/-- **Creature-love.** Love may reach an Other which is a creature and *not* a
    subsisting centre; such a world still contains no trinity.

    What this shows: "the beloved is another person" does not by itself deliver
    a second *subsistent* centre — the content of C508/C509 is a conjunct, not a
    name, and cannot be read back as "whatever is loved is divine".

    What this does NOT do: `Crt` is the shape-mirror of
    `ContingentSubjectKind`, and Γ's real creature level has **no inhabitant**
    (WALL 2, C481/C482/C503) — the shadow inhabits it deliberately, because the
    creature level is not what is missing; *subsistence* is.
    Footprint: `{}`. -/
theorem creature_love_gives_no_divine_beloved :
    ∃ (β : Type) (Sub Crt : β → Prop) (Love : β → β → Prop),
      (∃ f c, Sub f ∧ Crt c ∧ ¬ Sub c ∧ Love f c) ∧
      (∀ f o, Sub f → Love f o → Sub o ∨ Crt o) ∧
      (¬ ∃ p₁ p₂ p₃ : β, Sub p₁ ∧ Sub p₂ ∧ Sub p₃ ∧ p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ p₁ ≠ p₃) := by
  refine ⟨Bool, fun d => d = false, fun d => d = true, fun _ o => o = true, ?_, ?_, ?_⟩
  · exact ⟨false, true, rfl, rfl, by decide, rfl⟩
  · intro f o _hSub _hLove
    cases o
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro ⟨p₁, p₂, p₃, _h1, _h2, _h3, _h12, _h23, _h13⟩
    cases p₁ <;> cases p₂ <;> cases p₃ <;>
      first | exact _h12 rfl | exact _h23 rfl | exact _h13 rfl

/-- **Attribute-love.** The source subsists and loves an object that is *distinct*
    — and that object does not subsist: it is an intrinsic state of the source.

    What this shows: even granting a distinct object of love, `Subsists` is
    exactly what is missing, which is the content of `AxProcessionWord` (C505)
    and the Augustinian route's "step 6" gap exhibited rather than asserted.

    What this does NOT do: it does not refute C505 (the Word *is* subsistent there
    — by declaration), and it says nothing about the name of the beloved, only
    about the subsistence conjunct.
    Footprint: `{}`. -/
theorem attribute_love_gives_no_subsistent_word :
    ∃ (β : Type) (Sub : β → Prop) (Attr : β → β → Prop) (Love : β → β → Prop),
      (∃ f o, Attr f o ∧ o ≠ f ∧ ¬ Sub o ∧ Love f o) ∧
      (¬ ∃ p₁ p₂ p₃ : β, Sub p₁ ∧ Sub p₂ ∧ Sub p₃ ∧ p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ p₁ ≠ p₃) := by
  refine ⟨Bool, fun d => d = false, fun _ _ => True, fun _ o => o = true, ?_, ?_⟩
  · exact ⟨false, true, trivial, by decide, by decide, rfl⟩
  · rintro ⟨p₁, p₂, p₃, _h1, _h2, _h3, _h12, _h23, _h13⟩
    cases p₁ <;> cases p₂ <;> cases p₃ <;>
      first | exact _h12 rfl | exact _h23 rfl | exact _h13 rfl

/-- **Binitarian: Agape + Word, exactly two centres, no Spirit.** The two centres
    of the Agape datum, the Word bridge, and *no* Spirit at all: the two-centre
    world is legal.

    What this shows: "three is exactly the price of the Spirit". Everything the
    Agape datum and `AxProcessionWord` jointly give — a self-giving source, a
    distinct beloved, that beloved *named* as the Word, and the source's own
    subsistence — is consistent with a Godhead of exactly two subsisting centres.
    The third conjunct (`∀ d, ¬ IsS d`) is the machine form of "the Spirit
    modality is unpopulated", and the fourth is the machine form of "at most two"
    (every subsisting centre is one of the two).

    What this does NOT do: it does not refute `AxProcessionSpirit` (C506), and it
    does not weaken C510, which is proven under that axiom. A reader who rejects
    C506 keeps a binitarian reading, and that is the honest boundary of the case.
    Footprint: `{}`. -/
theorem agape_and_word_without_spirit_is_binitarian :
    ∃ (β : Type) (Sub : β → Prop) (Love : β → β → Prop) (IsW IsS : β → Prop),
      (∃ f w, f ≠ w ∧ Sub f ∧ Sub w ∧ Love f w) ∧
      (∃ w, Sub w ∧ IsW w) ∧
      (∀ d, ¬ IsS d) ∧
      (∀ d, Sub d → ∃ f w, f ≠ w ∧ ((d = f ∨ d = w) ∧ Sub f ∧ Sub w)) ∧
      (¬ ∃ p₁ p₂ p₃ : β, Sub p₁ ∧ Sub p₂ ∧ Sub p₃ ∧ p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ p₁ ≠ p₃) := by
  refine ⟨Bool, fun _ => True, fun a b => a = false ∧ b = true,
    fun d => d = true, fun _ => False, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨false, true, by decide, trivial, trivial, ⟨rfl, rfl⟩⟩
  · exact ⟨true, trivial, rfl⟩
  · intro d hIsS
    exact hIsS
  · intro d _hSub
    refine ⟨false, true, by decide, ?_, trivial, trivial⟩
    cases d
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro ⟨p₁, p₂, p₃, _h1, _h2, _h3, _h12, _h23, _h13⟩
    cases p₁ <;> cases p₂ <;> cases p₃ <;>
      first | exact _h12 rfl | exact _h23 rfl | exact _h13 rfl

end Logos.TrinitySeparations

/-!
# Axiom footprint audit (expected: `{}` for all four witnesses)
-/
#print axioms Logos.TrinitySeparations.unitarian_self_love_gives_no_second_centre
#print axioms Logos.TrinitySeparations.creature_love_gives_no_divine_beloved
#print axioms Logos.TrinitySeparations.attribute_love_gives_no_subsistent_word
#print axioms Logos.TrinitySeparations.agape_and_word_without_spirit_is_binitarian
