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

Amended by E0 (2026-09-15): the alternative is ADOPTED — `def T p := p`,
`theorem tschema := Iff.rfl` (see D-E0). Reason: the T-schema was the single
premise a skeptic could deny without self-refuting; making the D2 model
definitional removes the attack surface, and the §4–§6 proofs go through
unchanged (they were already logic). Reversal = restore the two declarations.
The §8 "gap" concern stands as flavor: `Correct s p := T p` is now `p`
itself; the world-level semantics (`Satisfies`/`TrueAt`) never used `T`.

## D3 — `cogito` is the single irreducible premise (TRANS)

`∃ s p, A s p` was an axiom, tagged TRANS. Everything about subjects, content,
agency and personhood carried it in its footprint. The *datum* of the act
cannot be derived inside the system that reasons from it — that was the
honest formal content of §1.

Amended by cogito-rethinking (2026-09-15): cogito IS derivable from
T12_twoPersons (C48, `Plurality.cogito_from_T12`). The axiom remained
declared in `Agency.lean` for import-order reasons (Agency cannot import
Plurality — cycle) and was formally redundant. The denial of cogito is
refuted by a *theorem*, exactly as N_T is refuted by `notNothingTrue`:
"there is no wrong" refutes itself by self-reference (Level 0);
"no act exists" refutes itself because the present act IS an act, and
that act is *derived* from the plurality bridge rather than declared.

Amended by A1 (2026-09-16): **the `axiom cogito` is DELETED.** The datum is
the theorem `Plurality.cogito_from_T12`, anchored on `AxTwoSubjects`. The
existence theorems that used the axiom (T1/T4/T5) are re-homed into
Plurality as T12 projections (`Plurality.T1_subjectExists`,
`Plurality.T4_agentExists`, `Plurality.T5_personExists`); Agency can no
longer import Plurality (cycle), which is why the constant no longer lives
here. The TRANS tag retires from the ledger — no TRANS axioms remain. Every
former `{cogito, Means, Subject}` footprint now reads
`{AxTwoSubjects, Means, Subject}` (project-wide "Path B"; C57).

Amended by M0/M1 (2026-09-16, `FORCED_SUBJECT.md` — COMPLETED).
**The flow is forced, not derived.** The user's ruling (§0 of
FORCED_SUBJECT.md): plurality cannot witness the act-datum, because the very
attempt to *deny* the act is an act (R0.1–R0.2). So `Agency.Cogito`
(`axiom Cogito : ∃ s p, A s p`) is **redeclared as the FORCED foundation**
(TRANS/FORCED; its negation refutes itself, `noCogito_selfRefutes`). The
A1-re-homed existence names switch from "produced by T12" back to
"projection of `Cogito`" — `Plurality.cogito_from_T12` becomes a corollary,
not the anchor. Every `{AxTwoSubjects, …}` footprint on the transcendental
chain is now `{Cogito, …}` (measured: C48, C21/C23/C24, C28/C29/C30,
C39, C52–C55, C57). Axiom inventory goes **12 → 11**:
+Cogito (forced), −Affects (→ def), −AxPersonsAffect (→ theorem). The
"lone-subject countermodel is the price of AxTwoSubjects" story is kept —
but it is now the price of *plurality* (M2 spike),
not of the act-datum.

## D4 — Truthmaker semantics: §24a atom-only, structural `TrueAt` (A2)

Since A2 (2026-09-16):
`TrueAt` is *defined* *structurally* — an atom is true in `w` iff some entity
exists in `w` and grounds it (`∃ e : Entity, ExistsAt w e ∧ Ground e (Form.atom n)`),
and `not`/`and`/`or`/`imp` are Tarskian-compositional **by definition**
(mirroring `Semantics.Satisfies`). The truth-maker principle is therefore a
*lemma*, atom-only: `groundPrinciple_atom : TrueAt w (Form.atom n) → ∃ e,
ExistsAt w e ∧ Ground e (Form.atom n) := fun h => h`. The former formula-level
`groundPrinciple` is dropped: for compounds it is underivable (not false) —
`Ground e (or …)` is a free relation, neither asserted nor denied; composite
truth is compositional. Consistency model (SEM): the face-value model
`Entity := Form`, `ExistsAt w e := (eval… )`, `Ground e φ := (e = φ)` —
i.e. ordinary Tarskian semantics, which satisfies every axiom below.

Amended by C2 (2026-09-15): the carrier is `Entity := Subject`
(Q2/D11 identification, definitional; see D-C2). Level-1 reading of the
face-value model: interpret `Subject := Form`, `ExistsAt w e := Satisfies w e`,
`Ground e φ := (e = φ)` — then `TrueAt w φ ↔ Satisfies w φ`, the connective
clauses follow from `sat_*` (theorems), and `AxGlobalGround` is witnessed by
`e := φ` itself. The Form-side Tarskian clauses (`Satisfies`) are untouched.
Honesty limit (A2): only the atom-clause carries existential grounding; there
is no provable `TrueAt = Satisfies` ∈-correspondence in general.

## D5 — Connective clauses `AxOr/AxAnd/AxNot` → THEOREMS (A2)

Formerly SEM composition axioms making truth two-valued over the
propositional fragment. Price of the old axioms: exact (non-exact) truthmaker
theories reject `AxNot`; asserting all three was the semantic choice that kept
classical logic.

**A2 (2026-09-16): these three axioms are DELETED.** `TrueAt` is now defined
*structurally* (atom-grounding + Tarskian recursion), so the connective
clauses are **THEOREMS** (`Iff.rfl`): `sat_ground_or/and/not/imp`, and
`lawExcludedMiddle`/`nonContradiction` are re-proved by definitional
reduction. This is the **strong version** (per user ruling): the connective
content is *proven*, not posited. The sole definitional commitment is the
structural identification (atoms + Tarskian recursion) — not a new belief,
but the face-value model already in D4/D6 and `Semantics.Satisfies`. See
DETAILS.md §6.1. **Honesty limits:** there is no `TrueAt = Satisfies`
∈-theorem in general (`Ground`/`ExistsAt` stay free VOCAB), and `Ground e
(or …)` is neither asserted nor denied — `groundPrinciple` for compounds is
dropped (underivable, not false).

## D6 — World-rigid grounding; `actualWorld` (SEM)

`Ground : Subject → Form → Prop` (C2: over the subject carrier; was `Entity`)
takes no world argument: what an entity *grounds*
does not vary across worlds; only its *existence* does. This
defuses the cross-world-identity problem by modeling choice (Q7.1).
`actualWorld : World` carries the performed actuality of §1 into the
semantics (mirror of the act-datum of §1 at this level).

Amended (2026-09-15, actualWorld batch): `actualWorld` is now a **definition**
— `def actualWorld : World := fun _ => Logos.Semantics.TV.t` (precedent:
`Necessity.someWorld`). No theorem uses *which* world is actual: T7 invokes
`Ground e τ` at `actualWorld` and nothing else, so the "present world" needs
only to exist, and the always-true valuation provides it. This is a SEM
modeling choice of the same class as E0, not a demoted datum; axiom count
23 → 22, C18–C20 lose `actualWorld` from their footprints.

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

## D9 — Q4: T8 failure trace and the META bridges

Attempting `∃ e, NecessaryEntity e ∧ Personal e` from T1–T7 alone fails at:
(a) no transfer of *necessity* onto the grounder of the present act's
contingent content — T7's necessity applies to world-necessary truths only;
(b) `GroundProp e f` does not definitionally yield "e *carries* f".
Declared bridges (META, with prices stated in-file):
`AxPersonalGround` (necessary reality grounds present personal features —
the poem's step, beyond deduction) and `AxGroundBearing` (minimal
non-reductive realism: a ground realizes what it grounds). T8 was PROVEN↑
under exactly these two.

Amended by B2 (2026-09-15): `AxGroundBearing` is dissolved — `Realizes` is
*defined* as `GroundProp` (a rename), so "the ground bears what it grounds"
is the unfolding of the vocabulary, not a separate assumption. T8 is now
PROVEN↑ under `AxPersonalGround` alone; the remaining failure point is (a).

## Q7.2 (DEFERRED)

Can `AxGlobalGround` be weakened (e.g. "every contingent ground of a
necessary truth is mirrored by a necessary ground")? Recorded as research;
not required for T7 as stated.

## D10 — Interpersonal value bridge (Value.lean, split C3-I)

The poem's pivot: logical right/wrong (T3/T6, one-person compatible) becomes
moral/interpersonal right/wrong only if the reality of value demands a
patient-other. The attempt to derive `∃ two persons` from existing axioms
fails at: nothing forces a subject other than the present one, and no link
exists from logical normativity to interpersonal moral value (see D14
failure trace + spike x2_spikeA). The named missing lemma is `ALONE_EXCLUDED
: ¬ (∃ s, Person s ∧ Alone s)`.

Amended by C3-I (2026-09-15): the monolithic `AxValueInterpersonal` (META)
is split into two narrower bridges:

- `AxTwoSubjects` (META): plurality only (right-and-wrong demands two persons).
- `AxPersonsAffect` (SEM meaning-postulate): distinct persons, by definition,
  bear on each other — a universal statement that asserts no existence.

Recovery theorem `valueInterpersonal_of_split` recovers the exact old statement
from the two new bridges: no strength lost. Consistency model for the split:
the same two-subject boolean {present, other}, but the *contents* of the
premises are now independent and individually priced.

## D11 — EntityOf bridge (Plurality.lean, Q2 decision)

`EntityOf : Subject → Entity` closes the Subject/Entity gap (Q2): each person
has an entity-correlate, letting the love layer (T14) attach necessity to
the relata via world-rigid grounding. SEM (each subject has a first-person
reality; consistency model: any injection `Subject → Entity`).

## D12 — Prop-level necessity operator (Necessity.lean)

The prose uses □/◇ at the propositional level; the formal machinery only
had world-level necessity over `Form`. Two operators now coexist (C1,
2026-09-15):

1. `NecessityPH (P : World → Prop) : Prop := ∀ w, P w` — the *real*,
   semantics-grounded modal operator, with S4 rules K/T/4 proved as theorems.
2. `Necessity (p : Prop) : Prop := NecessityPH (fun _ => p)` — the *degenerate
   identity-model alias*: for a world-invariant proposition, necessity is just
   truth. This preserves the old `Prop → Prop` interface; its K/T/4 rules are
   also theorems (plain universal quantification). The alias is intentionally
   vacuous — the non-trivial modality lives in `NecessityPH`.

A general rule `p → □p` is deliberately NOT declared for the alias (the "no
collapse" guard); the contingency of the world (P9, "este mundo é necessário?
Não") is expressed at the world level by `Semantics` (contingent forms), not by
the degenerate prop-level box.

`necDistinction : Necessity (¬ N_T ∧ ¬ N_F)` is now a theorem (was the SEM
axiom of D12, now `rightWrongDistinction` itself under the alias). Its genuine
world-level content is `Semantics.bothNecessarilyTrueAndFalse` (C37). FAITH-1
dissolved.

Future use: freedom (F1b) and the eternal love of T14 must be built on
`NecessityPH` (world-level), not on the degenerate alias, to preserve
meaningful modal content.

## D13 — Faith boundary scope (Love.lean, T14, C4)

The deductive chain stops at "eternal love-relation" (T14). Trinity,
incarnation and creation-contingency (poem P9/P10) are explicitly outside
pure deduction (§28/§29) and remain DEFERRED or flagged FAITH, per the
user's Q4 decision.

Amended by C4 (2026-09-15): `AxEternalLove` (FAITH/META, the former D14b
bridge) is dissolved. The poem's "de alguma forma" is now carried by a
*single priced SEM bridge*, `AxPersonStability : ∀ s, Person s → NecessarySubject s`,
attached to the relata: every person's entity-correlate exists in all worlds,
so a loving pair — derived via the C3-I bridges + affectivity — persists
eternally. T14 is now PROVEN↑ (a theorem under priced bridges, not a
directly declared axiom), and the FAITH layer is empty.

## D14b — Eternal love bridge (Love.lean)

The "eternal" step of T14 — that a loving pair *necessarily* exists —
was the hardest bridge. At D13's faith boundary it was declared as
`AxEternalLove : Necessity (∃ two persons, Person ∧ Person ∧ Love)` (FAITH/META),
on the ground that the denial of eternal love does not destroy the act of
denying it. Its consistency model was implicit: "the world is such that
love persists" — the poem's "de alguma forma."

Amended by C4 (2026-09-15): `AxEternalLove` is dissolved. The *eternal*
content is now carried by a structural bridge, `AxPersonStability`,
attached to the *relata* rather than to the relation itself — a metaphysical
bridge (SEM, with a consistency model to be added below if needed) asserting
that every person's entity-correlate exists in all worlds. The affectivity
(`Loves := Affects`) is a definition; the pair existence follows from the
C3-I bridges. All three are individually priced and individually failed to
be excluded:

- spike x2_spikeA: `AxTwoSubjects` (plurality) — stuck at `ALONE_EXCLUDED`;
- spike x2_spikeB: `AxPersonsAffect` (affectivity) — `Affects` has no intro rule;
- spike x2_spikeD: `AxPersonStability` (persistence) — `Person` (T5) gives no world-coverage. (Superseded 2026-09-17 by esse-est-agere: the rule is supplied by definition; `AxPersonStability` is now a theorem.)

### 2.0 retries (E0/C2/A3 campaign, 2026-09-15, `/tmp/opencode/x3_spikeB{1,2,3}.lean`)

- **x3_spikeB1** (`ALONE_EXCLUDED` retried post-campaign): strawmen — T6
  fallibility is a *one-subject* metatheorem (does not need an other);
  `rightWrongDistinction` is axiom-free but *quantification-agnostic* (does
  not construct a relatum); `Means`/`A s p` never name another subject.
  **Stuck.** Lemma stays named; `AxTwoSubjects` stays the priced META bridge.
- **x3_spikeB2** (`PERSONS_BEAR`, from act-structure over the A3 bundle):
  `Helps`/`Harms` have *no introduction rule* from `Agent/Rational/Means`;
  nothing of personhood is directed at another's welfare. **Stuck.**
  Named missing lemma: `PERSONS_BEAR : ∀ s t, Person s → Person t → s ≠ t →
  (Helps s t ∨ Harms s t) ∨ (Helps t s ∨ Harms t s)`; `AxPersonsAffect`
  stays the priced SEM meaning-postulate.
- **x3_spikeB3** (`PERSON_PERSISTS`, post-C2): `ExistsAt : World → Subject → Prop`
  has *no introduction rule* from `Person` (act datum is world-local; Form-level
  necessity is disconnected from subject-world-existence). **Stuck.**
  Named missing lemma: `PERSON_PERSISTS : ∀ s, Person s → ∀ w, ExistsAt w s`;
  `AxPersonStability` stays the priced SEM bridge. (Superseded 2026-09-17 by
  esse-est-agere: `ExistsAt _w s := ∃ p, A s p` supplies the rule —
  `AxPersonStability` is now a `{}` theorem; see D-esse-est-agere.)

## D14 — Plurality failure trace and poem mapping (Value.lean, Plurality.lean)
Attempting `∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂` from
Core + Agency + Person + Alternatives alone:

Available facts: T5 (one person s), T9 (incompatible contents p, q).
Kernel context after `obtain`: `s : Subject`, `hs : Person s`.
No construction of a *second* subject is available; the goal remains open.
The missing step is exactly the interpersonal normativity bridge (D10).

### C3-II research note (one-shot spike, 2026-09-15)

Transcendental attempt (x2_spikeC): derive `∃ t : Subject, t ≠ s` from the
**denial** of the lone-person scenario — refute `∃ s, Person s ∧ Alone s`
using only `cogito + T6_truthTranscendsWill + T5 + P6 + defs`, with no new
existence axioms and no new vocabulary. Verdict: **stuck (not derived)**, as
predicted by D14. The one-person interpretation satisfies every derivable
theorem (T6 is a single-subject metatheorem; P6 only neutralizes a lone act),
so no contradiction is produced. Named missing lemma:

    ALONE_EXCLUDED : ¬ (∃ s : Subject, Person s ∧ Alone s)

Unprovable from the current axioms; the interpersonal step remains separated
into the priced bridges `AxTwoSubjects` (META) + `AxPersonsAffect` (SEM).
Any future transcendental defense of T12 must target `ALONE_EXCLUDED`
directly.

## D-B1 — Act bundle (Agency.lean)

The six meaning postulates `act_implies_exists/content/agent` and the two
Person variants (`act_implies_means/rational`) were declared as *axioms*,
acting as a tax on every Level-2 and Level-3 theorem's footprint. They were
replaced by a *bundle definition*:

    A s p := Agent s ∧ Exists s ∧ Content p ∧ Rational s ∧ Means s p.

The postulates become `rfl`-projections; cogito was the single
performative datum, now deleted in A1 (2026-09-16) — the act-datum is the
theorem `cogito_from_T12` (see D-cogito-rethinking).
The primitives `Subject`/`Agent`/`Rational`/`Means` remain opaque vocabulary.
`Exists`/`Content` were originally also opaque but are now *analytical
definitions* (`Exists _ := True`, `Content _ := True`, cogito-rethinking
batch): every subject meets existence, every proposition meets content —
these were always meaning-intended as definitional, and making them so
removes two opaque axioms.
This reifies what base.txt §1–§15 already asserts
the act *contains* — no philosophical cost; eight axioms dissolved total.

Amended by **D-Tier1** (2026-09-16): the collapse is now complete —
`Agent` and `Rational` are ALSO analytical definitions (`:= True`), and the
bundle `A` is the meaning-act all the way down:

    def A s p := Means s p.

`act_implies_agent`/`act_implies_rational` remain `rfl`; `Person` (T5)
collapses conceptually to the intentional meaning-subject (`∃ p, Means s p`),
though the conjunct form is retained. The `axiom` inventory loses
`Agent`/`Rational` (−2), 16 declarations remain (then 15 after A1
cogito-removal, 2026-09-16).

## D-ActInitiation — the act is the initiation of movement, not its transfer (Agency.lean, Initiation.lean)

User correction (2026-09-17): a subject is one who acts, not the act itself;
an act is the *initiation* of movement, not its transfer (a transfer is a
function of the prior state; an initiation is not). Resident rebase:

- `Means` ceases to be primitive: **`def Means s p := ∃ w w' : State,
  Initiates s w w' p`**, over the new vocabulary `State` (abstract state sort
  — deliberately NOT `Semantics.World`, which is a valuation = a state = a
  transfer-object) and `Initiates : Subject → State → State → Prop → Prop`.
  `A s p := Means s p` unchanged; `Cogito` unchanged.
- `Initiation.lean` (barrel): `branches_not_transfer : Branches R → ¬
  IsTransfer R` (**footprint `{}`** — an initiation with genuine alternatives
  is not the graph of a function); `originates_not_transfer` and
  `person_iff_originates` (`{Initiates, State, Subject}`, vocab-only);
  `Cogito_Init` / `noInitiation_selfRefutes` (`{Cogito, Initiates, State,
  Subject}`).
- **The subject stays the forced posit `Cogito`**: the soundness obstruction
  (empty model satisfies the static vocabulary yet falsifies `∃p Meaning_I p`)
  forbids a derivation, so the datum is merely *relabeled* as the
  initiation-foundation. Cost: vocabulary +1 (`−Means`, `+State`, `+Initiates`);
  axiom inventory **11 → 12 declarations**, substantive unchanged.
- Current `Person` (T5) reading: `Intentional s := ∃ p, Means s p`, now
  unfolding to `∃ w w' p, Initiates s w w' p` — the person is the *origin* of
  an initiation (`person_iff_originates`).
- (Superseded 2026-09-17, definitional-subject batch: `Subject`/`State`/
  `Initiates` are definitions, `Cogito` a theorem `{}`; inventory 12 → 8.
  See `formal/GAPMAP.md`.)

## D-A1 — Fallibility (Order.lean)

`Fallible s p` was declared axiom, deliberately opaque. Its only consistent
model was `Fallible _ p := (p = False)`. In A1 the axiom was replaced by a
*definition*: `def Fallible (_s) (p) := IsFalse p`, and `fallible_false`
becomes a theorem from `Core.someFalse` + `cogito_from_T12` (after the A1
cogito-removal). T6 becomes PROVEN↑ with no standalone fallibility premises.

## D-B2 — Realizes := GroundProp (GroundPerson.lean)

`Realizes` and `GroundProp` were distinct axioms connected by `AxGroundBearing`
(META). In B2: `def Realizes e f := GroundProp e f`; `AxGroundBearing` becomes
an `rfl`-theorem. T8 now loads on `AxPersonalGround` only — the remaining
failure point is the necessity-to-person transfer (D9 (a)).

## D-C1 — Necessity derived (Necessity.lean)

See D12. The primitive modal operator was replaced by two operators: (1)
`NecessityPH`, the real world-level box (def, with K/T/4 theorems); (2) `Necessity`,
the degenerate identity-model alias (def, with K/T/4 theorems). `necDistinction`
becomes a theorem. Saves 5 axiom declarations (`Necessity`, `necK`, `necT`,
`nec4`, `necDistinction`); FAITH-1 dissolves.

## D-C4 — Structural love: `Loves := Affects` (Love.lean, T14)

The love-relation was primitive (`axiom Loves`) and the eternal step was the
faith bridge `AxEternalLove`. Appendix C4 (2026-09-15):

- **Definitional choice**: `def Loves s t := Affects s t` — love is *directed
  constitutive bearing*, the "ajuda/não prejudica" that the poem already makes
  a relation (P6). This dissolves the `Loves` axiom and gives T14 a structural
  (rather than primitive) relation. The *affective fullness* of "Amar" is
  explicitly left on the prose side; enriching the definition later is a
  forward-compatible option (a `LovesFull` would be a new bridge, not a rewrite).
- **Rejected variant**: `Loves := Helps`-based. Richer willing-the-good
  reading, but demands a new help-bridge of the same shape as the dissolved
  faith bridge — barely better than status quo, so rejected in favor of the
  `Affects` reading (approved in the Q4 decision round).
- **Stability price**: the "eternal" half is the *new* priced bridge
  `AxPersonStability : ∀ s, Person s → NecessarySubject s` (SEM). Exclusion
  spike x2_spikeD stuck (see D14b): `Person`'s agency structure (T5) yields
  no fact about which worlds its entity-correlate inhabits. Consistency model
  note: interpret `World` as the set of worlds where persons' correlates exist
  (i.e. the "de alguma forma" is *modeled in*, not argued for).
  (Amended 2026-09-17 by esse-est-agere: the bridge is now a theorem —
  see D-esse-est-agere. The "de alguma forma" lives in the agency reading
  of existence, not in a postulate.)
- **Resulting theorem set**: `T14_eternalRelation` (pair + `NecessarySubject`
  relata), `T14_world` (`NecessityPH` — the honest world-level □), `T14_square`
  (alias-□ image of the old statement), `T14_content`. Footprint drops
  `AxEternalLove` and `Loves` entirely.

## D-E0 — Truth as identity: `T := id` (Core.lean)

The T-schema was the one premise a skeptic could deny without self-refuting
(§29 criterion). E0 (2026-09-15) makes the D2 consistency model definitional:
`def T (p : Prop) : Prop := p`, `theorem tschema (p) : T p ↔ p := Iff.rfl`.
All §4–§6 proof bodies survive unchanged (they were already logic; the T-schema
steps are now `rfl`-instances) — re-verified by build. `rightWrongDistinction`
("há certo e há errado") is axiom-free. Reversal = restore the two
declarations; the D4 "T/p gap" flavor concern is re-recorded: with E0,
`Correct s p := T p` is `p` itself, i.e. correctness = truth of the content —
the world-level semantics (`Satisfies`, `TrueAt`) never used `T` and carry the
genuine modality independently. This shrinks every Level-0/2/3 footprint by
`{T, tschema}` and moves six theorems to `does not depend on any axioms`.

## D-C2 — Entity carrier: `Entity := Subject` (Truthmaker.lean, Plurality.lean)

The Q2/D11 identification becomes definitional: `def Entity : Type := Subject`
(`Truthmaker` imports `Agency`; no cycle), `def EntityOf : Subject → Entity :=
fun s => s`. `Ground : Subject → Form → Prop` and `ExistsAt : World → Subject
→ Prop` remain the two real semantics axioms. This is a *reification*, not a
vacuous collapse (contrast the rejected full face-value collapse — see plan):
T7 still says "∃ subject-entity grounding every necessary truth" with a real,
world-rigid `Ground`. Level-1 face-value model (D4, updated): `Subject := Form`,
`ExistsAt := Satisfies`, `Ground := eq` — T7's witness is `e := φ` itself.
`Entity`/`EntityOf` leave every Level-1 and T8/T14 footprint (T14 family 13 → 10).

## D-A3 — Affect bundle: `Affects := ?` (Value.lean)

`axiom Affects` + `help_affects` + `harm_affects` → three SEPARATE axioms
defined away. **M1 (2026-09-16, `FORCED_SUBJECT.md` — COMPLETED):** the
definition is now real — `def Affects s t := s ≠ t` (S1 × C3-II: a subject
bears on what is *other*; the lone subject affects nothing, P1–P2).
`Helps`/`Harms` are projections (`Helps := Affects`, `Harms := Affects`);
`AxPersonsAffect` is a **theorem** (distinct – persons affect, `Or.inl hne`).
Axiom inventory **−1** (`Affects`) and **−1** (`AxPersonsAffect`); all
value-chain footprints drop both (measured C42–C47, C56). SEM tag retires for
these two; `Affects` and `AxPersonsAffect` cease to be axiom declarations.
The "Amar é escolhido" prose price (F1) is untouched (choice, not
affectivity, carries it). Design note D-A3's "straightforward but S1-priced"
wording is superseded by the definitional collapse (A3/M1).

**D-A3-r (A3-refactor, Chooses-def batch, 2026-09-15):** the direction is now
reversed — `Affects` is the *single primitive* value relation
(`axiom Affects : Subject → Subject → Prop`) and `Helps`/`Harms` are its
*definitional projections* (`def Helps s t := Affects s t`,
`def Harms s t := Affects s t`); `help_affects`/`harm_affects` are `rfl`.
Rationale: the love layer's real semantic primitive was already `Affects` (C4,
`Loves := Affects`, and C47's node); the two helps/harms axioms only ever
appeared in footprints via the A3-bundle unfold. Promoting the real primitive
is the honest footprint: every love-chain theorem now prints `{Affects}`
instead of `{Helps, Harms}`. **Honesty note**: the HELP/HARM *distinction* is
no longer formal — both predicates unfold to the very same `Affects`. The
distinction survives as prose/conceptual content (P6), and `AxPersonsAffect`
(SEM) still does the analytical work for pairs; a future need for genuinely
asymmetric helping/harming semantics must restore a real help-bridge (a new
priced move, not a silent revert).

## D-Chooses — `Chooses` restored to a real definition (Choice.lean, Order.lean)

Amended by the **choice-realism batch** (2026-09-16). Originally
`axiom Chooses : Subject → Prop → Prop → Prop` — the §14 interface for F1
(freedom, DEFERRED). The Chooses-def batch (2026-09-15) demoted it to
`def Chooses _ _ _ := False` (dead placeholder; only `CanChoose`/`FreeWill`
used it). The user's point — "there is no right and wrong without choice!
OBVIOUSLY" — exposed the placeholder as the *mislabeled gap*: with
`Chooses := False`, choice was unrepresentable, so "subject ⇒ choice" and
"right/wrong ⇒ choice" looked OPEN. The real definition (no axiom, no price):

    def Chooses s p q := A s p ∧ Incompatible p q

i.e. a subject choosing content `p` against an incompatible content `q`
(§14: choosing is adopting p over q). `Incompatible p (¬p)` is pure logic,
so every meaning-act is a choice against its own negation. Theorems:
`meaning_needs_subject`, `person_chooses` (subject ⇒ choice, `{Means,
Subject}` — no cogito), `choiceExists`, `noChoice_selfRefutes` (denying
choice is itself a choice), `JUDGE_COMMITTED` (right/wrong ⇒ choice),
`Order.judge_commits` (the §8 judge is a chooser, needs bivalence +
`cogito_from_T12` after A1), `canChoose_unfold` (the aliased-◇ `CanChoose`
collapses to real choice). `Order.lean` gained `import Logos.Choice` (no
cycle).

- **F1 split**: F1a (choice-existence, the transcendental step) is now
  PROVEN↑; F1b (bipolar freedom `FreeWill ↔ ◇Choose ∧ ◇Choose¬`, world-level
  on `NecessityPH`) stays DEFERRED — a subject may mean `p` without being
  able to mean `¬p`. `FreeWill` remains an unproven definitional interface;
  restoring it is a future priced move (semantic choice for the modal
  choice-alternatives), never a silent revert.

## D-cogito-rethinking — non-cogito refutes itself (Agency.lean, Plurality.lean)

The user's observation: non-cogito refutes itself, structurally mirroring N_T
("there is no wrong" refutes itself because the claim is a proposition that
would be a truth if it were true). RETHINKING-COGITO.md records the full
parallel.

D-cogito-rethinking (2026-09-15):

1. **Exists → def, Content → def** (`Agency.lean`): `def Exists (_s) := True`,
   `def Content (_p) := True` — analytical: every subject in the system exists
   (it is encountered as a subject of an act); every proposition is a valid
   content. These two axioms were meaning-intended as definitional; now made so.
2. **cogito → derivable theorem** (`Plurality.lean`, C48): from
   `T12_twoPersons` (AxTwoSubjects + rightWrongDistinction), take a Person;
   `Intentional` supplies a proposition it means; `Exists`/`Content` (now defs)
   fill the remaining act-aspects. Footprint `{AxTwoSubjects}` + kind-predicates
   — no `cogito`, no `Exists`, no `Content`. T2 becomes axiom-free (`{}`).
3. **A1 (2026-09-16): axiom cogito DELETED.** The former `axiom cogito` in
   `Agency.lean` is gone — the act-datum is the theorem
   `Plurality.cogito_from_T12` (C48), anchored on `AxTwoSubjects`. The
   existence theorems that used the axiom (T1/T4/T5) are re-homed into
   Plurality as T12 projections; Choice/Order switch to the new nodes
   (explicit imports; acyclic). TRANS tag retires; no TRANS axioms remain.
4. **footprint consequence**: every former `{cogito, Means, Subject}` footprint
   became `{AxTwoSubjects, Means, Subject}` (project-wide "Path B"; C57).
   The "present act" datum is now a derived consequence of the plurality
   bridge + logical distinction (Level 0 + one META bridge), not an
   irreducible assumption. This is a strict strengthening.

Cost: three axioms removed in cogito-rethinking (−2 declarations: Exists/Content;
then −1 more in A1: cogito itself), two theorems added (C48 + T1/T4/T5 re-homed).
The philosophical price: the footprint transitively contains `AxTwoSubjects` via
the plurality bridge — this is the existing META cost, now visible as the
sole source of the act-datum.

5. **(M0, 2026-09-16, `FORCED_SUBJECT.md` — the correction that retirement
   needed).** Item 4 was the bug. The act-datum is **not** a consequence of
   plurality: to deny it IS the act, so it cannot be witnessed by the
   plurality bridge (it precedes the bridge — R0.1–R0.2, forced foundation).
   `Agency.Cogito` is **redeclared** (TRANS/FORCED), `noCogito_selfRefutes`
   is re-proved kernel-checked, and every former "projection off T12" name on
   the act-chain is re-pointed at `Cogito`: `Plurality.cogito_from_T12`
   becomes a corollary (C48), no longer the anchor; the A1-era footprint flip
   `{AxTwoSubjects,…} → {Cogito,…}` (measured). The corpus's plurality
   theorems (T12/T5/T11/Choice/Order/Love) keep `AxTwoSubjects` exactly where
   plurality is genuinely in play — the M2/M3 spike prices, not the datum's.

Cost: three axioms removed in cogito-rethinking (−2 declarations: Exists/Content;
then −1 more in A1: cogito itself), two theorems added (C48 + T1/T4/T5 re-homed).
The philosophical price: the footprint transitively contains `AxTwoSubjects` via
the plurality bridge — this is the existing META cost, now visible as the
sole source of the act-datum.

## D-Tier1 — act = meaning; `Subject` as a pure sort (Agency.lean, Person.lean)

The user pushes the reducibility audit one step further: the act is,
essentially, meaning (§2 §14). 2026-09-16:

1. `Agent`/`Rational` → `def _ := True` — the same analytical class as
   `Exists`/`Content` from the cogito-rethinking batch: every subject we
   encounter (via the act datum) is by definition an agent and rational.
   Two more opaque axioms dissolved; **axiom inventory 18 → 16**.
2. `def A s p := Means s p` — the B1 bundle is the meaning-act all the way
   down; `act_implies_*` stay `rfl`. `Person` (T5) collapses conceptually to
   the intentional meaning-subject; conjunct form retained for stability.
3. **`Subject` stays an axiom — as a pure sort, justified on consistency
   grounds.** The tempting "remove it" moves all fail:
   - `inductive Subject` (empty) refutes `∃ s` (`cases s`), contradicting
     `cogito`/`AxTwoSubjects` → `False` is derivable — invalid;
   - `Subject := Bool` / `fin 2` *smuggles* "exactly two subjects" — a META
     claim, not a modeling neutral;
   - `Subject := ℕ` asserts infinity (no finite-persons model);
   - `Subject := Unit` makes `s₁ ≠ s₂` (T12) impossible.
   So `axiom Subject : Type` is the honest minimum: a sort whose existence is
   supplied by `cogito`/T12, with no cardinality commitment.
4. **Cost**: none forced; only the honest residue of the act-vocabulary
   (`Means` + `Subject`). Footprints of every Level-2/3 theorem drop
   `{Agent, Rational}` (measured: T1/T4/T5 now `{AxTwoSubjects, Means, Subject}`
   after A1 cogito-removal).

## D-choice-realism — judgment as choice; the chain closes (Choice.lean, Order.lean)

The user's chain is "no right and wrong without choice; no choice without a
subject; no meaning without a subject". The formal ledger now closes it for
the *existence* half (F1a; the bipolar modal half F1b stays deferred). 2026-09-16:

- `Chooses s p q := A s p ∧ Incompatible p q` — a real, axiom-free definition
  replacing the `:= False` placeholder (see D-Chooses). `Incompatible p (¬p)`
  is pure logic (`{}`), so the field of choice around any act is non-empty.
- **subject ⇒ choice** (`person_chooses`): `Person s → ∃ p q, Chooses s p q` —
  kernel-checked, `{Means, Subject}`, no `cogito` in the footprint. The
  subject that means `p` chooses `p` against `¬p`. This was the former "OPEN
  gap" (mislabel, fixed by the real definition).
- **right/wrong ⇒ choice** (`JUDGE_COMMITTED`): `(¬N_T ∧ ¬N_F) → ∃ s p q,
  Chooses s p q`. The premise is in fact unused — choice already holds via
  `choiceExists` from T5 (C52, `Plurality.T5_personExists`). Also the in-layer
  version (`Order.judge_commits`): the §8 judge (content `p`, `T p ∨ IsFalse p`)
  choosing against `¬p` — needs bivalence + `cogito_from_T12` (`CL +
  {AxTwoSubjects, Means, Subject}`).
- **denying choice refutes itself** (`noChoice_selfRefutes`): the denial is
  itself an act → a choice — the same self-refutation structure as N_T and
  non-cogito (RETHINKING-COGITO.md parallel applies).
- **a subject exists is un-denyable** (`noSubject_selfRefutes`):
  `(¬ ∃ _s : Subject, True) → False` — the denial of a subject is itself an
  act/choice of a subject; `choiceExists` (C52) supplies the resident witness.
  Footprint `{AxTwoSubjects, Means, Subject}` (Path B is the only path after
  A1 cogito-removal). The pure-logical shell of the bare sort alone (empty
  model) is consistent, so "no subject" is refutable only given the
  act-datum resident in the theory (the Tarski/Gödel wall — IM_STUPID §3).
- **F1 split**: F1a PROVEN↑ (this batch); F1b (bipolar `FreeWill`, on
  `NecessityPH`) DEFERRED — a subject may mean `p` without being able to mean
  `¬p`; nothing in the current axioms forces world-level possibility of the
  negation. `canChoose_unfold` shows the aliased-◇ scaffolding collapses to
  real choice, so F1b is exactly the modal claim, not a vocabulary gap.
- Cost: zero new axioms; `Order.lean` imports `Logos.Choice` (acyclic).

## D-C47 — Chain node `T12_directedPair` (Plurality.lean)

The love layer (T14) needs a pair carrying *both* affectivity direction and
world-stability. Before this decision T14 re-derived the orientation inline
(`obtain … T12_twoPersons` + `cases` on `AxPersonsAffect`) and then applied
`AxPersonStability` to the resulting pair — correct, but the direction step
was invisible to the ledger. D-C47 (2026-09-15) names it:

```lean
theorem T12_directedPair :
    ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ Affects s₁ s₂
```

Obtained from `T12_twoPersons` by cases on `AxPersonsAffect` (which decides
a direction), swapping the pair if needed. `T14_eternalRelation` now
destructures this node directly, so direction and stability provably live on
the *same* pair. No cost: identical footprint (`{AxTwoSubjects,
AxPersonsAffect, AxPersonStability}` + vocabulary + `{ExistsAt, Affects}`).

- **Rejected alternative**: a lone stability-only node
  (`∃ s₁ s₂, Person ∧ Person ∧ s₁ ≠ s₂ ∧ NecessarySubject s₁ ∧ NecessarySubject s₂`
  from `T12_twoPersons` + `AxPersonStability`). It would typecheck but leaves
  the loving *direction* unconnected to the stable pair — T14 would have to
  re-invoke `AxPersonsAffect` independently, risking a pair different from the
  stable one. T12_directedPair guarantees the pair is the same throughout.
- Note: `Affects` is now the single primitive (D-A3-r, A3-refactor), so the
  node prints `Affects` (not `Helps`/`Harms`) in its footprint.

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

## D-esse-est-agere — existence as agency; persistence proven (Truthmaker.lean, Love.lean)

The M3 wall (`PERSON_PERSISTS`: `Person`/`Means` has no introduction rule
into `ExistsAt`) is answered by supplying the rule as a definition —
*esse est agere*, to be is to act:

- **Definitional choice**: `def ExistsAt (_w : World) (s : Subject) : Prop :=
  ∃ p : Prop, A s p` (arity kept, so all 18 use-sites still elaborate with
  zero proof-body changes). The world-index is vacuous **by principle**:
  `Means` takes no `World` parameter, so agency is not world-located; the
  existential does the real work (only actors exist). This is not the
  degenerate `Necessity p := p` alias: `∃ p, A s p` is substantive, and the
  alternative (free relation) makes persistence unprovable in principle.
- **Why not the rejected variants**: defining *truth* from agency was
  rejected (§4.3, breaks D2/T-purity) — existence is a different move and `T`
  is untouched. The §4.12 `ExistsAt := Satisfies` sketch rested on D-Tier1
  (subjects as formulas), itself superseded by `Subject := Unit ⊕ Prop`.
- **Result**: `AxPersonStability` (name kept, M1 precedent) is now a theorem
  with footprint `{}` (`Person → Intentional → Means`, `w` discarded).
  Measured: T14 family → `{AxTwoSubjects}`; C18/C34 → `{AxGlobalGround,
  Ground}`; C15/C16/C17/C60 → `{Ground}`. Inventory 8 → 6.
- **Untouched**: M2 (`Alone` never mentions `ExistsAt`; its countermodel
  doesn't interpret it) — this batch proves *persistence*, not plurality.
  `Ground` stays the one free VOCAB relation.
- **Honestly recorded costs**: `T14_world` is trivially witnessed (same act
  in all worlds); T7/T8 "necessary" turns agent-flavored (grounded by an
  acting subject); the "de alguma forma" now lives in the agency reading
  of existence rather than in a postulate.
