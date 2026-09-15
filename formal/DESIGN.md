# DESIGN.md — decision log of the Logos formalization

Running record of every modeling choice. Each entry: the decision, why it was
taken, what it costs, and (where relevant) the consistency model that keeps
the axiom system contradiction-free.

## D0 — Two-level architecture

- **Level 0 (`Core`)**: Lean's impredicative `Prop` is the universe of
  propositions; truth `T : Prop → Prop` is primitive. Self-refutation (T3)
  lives here because it needs quantification *over all propositions*.
- **Level 1 (`Semantics`, `Truthmaker`, `Modal`)**: a separate syntactic
  `Form` code type + worlds. Needed for necessity (□ as ∀-over-worlds) and
  grounding, without mixing object-language codes with metalanguage `Prop`.
- **Level 2 (`Agency`, `Person`, `Alternatives`, `Order`, `GroundPerson`)**:
  subjects, acts, agency, personhood, correctness, and the T8 pass — back at
  `Prop` level, wired to Level 1 only through explicitly declared bridges.

## D1 — Classical metalogic (declared, not smuggled)

`Classical.em` / `Classical.byContradiction` are used openly (T3's
`¬∀p¬Tp ⇒ ∃pTp` step, bivalence §10, §22). This *is* the prose's "pela lógica
clássica" (§22), now a visible meta-decision. Footprints show exactly
`{propext, Classical.choice, Quot.sound}` where classicality enters.

## D2 — Stratified truth, liar blocked at the door

`T` is primitive with `tschema : ∀ p, T p ↔ p`. Consistency model (SEM):
interpret `T` as identity on `{True, False}`. No fixed point `p = ¬T p` is
assumed or derivable, so the liar cannot form — the exact requirement of a
stratified theory of truth (Tarski). The alternative `def T p := p`
(zero-axiom core) is documented and rejected: it would erase the
proposition/truth gap the normative layer (§8, §24a) needs (see plan D4).

## D3 — `cogito` is the single irreducible premise (TRANS)

`∃ s p, A s p` is an axiom, tagged TRANS. Everything about subjects, content,
agency and personhood carries it in its footprint. The *datum* of the act
cannot be derived inside the system that reasons from it — that is the
honest formal content of §1.

## D4 — Truthmaker semantics: §24a as a lemma

Truth is *defined* as being-made-true
(`TrueAt w φ := ∃ e, ExistsAt w e ∧ Ground e φ`), so `groundPrinciple`
is proved by unfolding. The principle is worn by the semantics, never
hidden. Consistency model (SEM): the face-value model
`Entity := Form`, `ExistsAt w e := (eval… )`, `Ground e φ := (e = φ)` —
i.e. ordinary Tarskian semantics, which satisfies every axiom below.

## D5 — Connective axioms `AxOr/AxAnd/AxNot` (SEM)

Ground-level composition principles making truth two-valued over the
propositional fragment. §22/§23 are then theorems *inside* truthmaker
semantics. Price: exact (non-exact) truthmaker theories reject `AxNot`;
asserting all three is the semantic choice that keeps classical logic.

## D6 — World-rigid grounding; `actualWorld` (SEM)

`Ground : Entity → Form → Prop` takes no world argument: what an entity
grounds does not vary across worlds; only its *existence* does. This
defuses the cross-world-identity problem by modeling choice (Q7.1).
`actualWorld : World` carries the performed actuality of §1 into the
semantics (mirror of the cogito datum at this level).

## D7 — `AxGlobalGround` (SEM): the named quantifier swap of T7

`∀w∃r … → ∃r∀w …` is invalid in general; T7's informal proof hides exactly
this move. It is declared as `AxGlobalGround` and flagged. Its negation
does not self-refute, so it stays a *semantic axiom*, never a
"transcendental theorem". With it, T7 is a genuine theorem; without it,
T7 is BLOCKED on precisely this lemma.

## D8 — Q3.1/Q3.2: §24b renderings

Features of an act = propositions entailed by its content
(`HasFeature a f := a → f`); personal = meant (`Means`); logical =
true-or-false (bivalence). On these readings `inseparability_24b` is a
theorem. Both directions use only the act datum + bivalence. Documented
limitation: the theorem's strength is bounded by these renderings; a
richer feature ontology would need re-modeling.

## D9 — Q4: T8 failure trace and the two META bridges

Attempting `∃ e, NecessaryEntity e ∧ Personal e` from T1–T7 alone fails at:
(a) no transfer of *necessity* onto the grounder of the present act's
contingent content — T7's necessity applies to world-necessary truths only;
(b) `GroundProp e f` does not definitionally yield "e *carries* f".
Declared bridges (META, with prices stated in-file):
`AxPersonalGround` (necessary reality grounds present personal features —
the poem's step, beyond deduction) and `AxGroundBearing` (minimal
non-reductive realism: a ground realizes what it grounds). T8 is then
PROVEN↑ under exactly these two.

## Q7.2 (DEFERRED)

Can `AxGlobalGround` be weakened (e.g. "every contingent ground of a
necessary truth is mirrored by a necessary ground")? Recorded as research;
not required for T7 as stated.

## Toolchain incident log (2026-09-15)

- `import Mathlib` in every module made each elaboration load ~8900 modules;
  ×3 parallel jobs on 7.5 GB RAM ⇒ swap thrash. Grep proved zero uses of any
  `Mathlib.*` content (only `by_contra`/`rintro`/bare-`em` conveniences).
- Fix: all modules import Lean core only; `by_contra`→`Classical.byContradiction`,
  `rintro`→`intro`+`obtain`, bare `em`→`Classical.em`; mathlib require dropped.
  Builds went from >10 min (thrashing) to seconds.
- Lean core notes learned the hard way: core `simp` is weaker than Mathlib's
  (`cases`+`simp [eval]` left goals) — fixed by defining `Satisfies` directly
  by recursion so Tarskian clauses hold definitionally (`Iff.rfl`);
  `subst h` with `h : a = q` eliminated the wrong-side variable — fixed with
  explicit directional `rw [heq]`; application `hnt (h s p).1 hf` parses as
  `(hnt (h s p).1) hf` — needs `hnt ((h s p).1 hf)`.
