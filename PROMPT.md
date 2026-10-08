# PROMPT.md — SemanticFinitude must not reach the Divine Persons (only creatures)

Composite hand-off. Written 2026-10-08 by the previous agent (context exhausted before
implementing). READ THIS FIRST, then `AGENTS.md` (binding conventions), then the files
cited below with `file:line`.

> **Line-number caveat:** all `file:line` refs were re-verified 2026-10-08 against the
> post-consolidation tree (commits `ae2b945` + `30045fd`, see §2.5). DTA refs carry a +1
> import-line shift from `30045fd` wherever the cited line moved; each was checked by
> content, not by arithmetic. After the first *new* edit, locate declarations **by name**.

## 1. The user's instruction (verbatim)

> "SemanticFinitude should not apply to Divine Persons. Only contingent human beings."
> "(creatures)"

Follow-up answers to my two design questions (verbatim):

> Q: what should Γ say about the Divine Persons' semantic capacity?
> **"However is more Catholic."**
> Q: how should the ground's aseity/unicity/sole-bearer conclusions carve the Persons out?
> **"Whatever is more Catholic."**

Interpretation I settled on (verify it still reads right, but do not re-ask the same
questions):

- **"more Catholic" for capacity ⇒ ASSERT, not merely exempt.** Classical doctrine
  affirms God's fullness (omniscience/omnipotence); leaving it open would be neutral,
  asserting is affirmative. So: new declared axiom that the divine Persons' semantic
  capacity is total (see §5, Option E).
- **"more Catholic" for carve-out ⇒ name the three Persons (D-2), not the anonymous
  `NecessarySubjectKind`.** Nicene shape: one ground/ousia, three named hypostases
  (source/word/spirit). Cost is neutral: carved rows pay `TrinitarianPersonalBridge`
  (META) in place of `GroundTranscendence` (META) — same single substantive price.
  The kind-level carve would make those rows drop to 0 substantive axioms
  (AXIOMATIC → PROVEN), i.e. a price *decrease* that reads as a free lunch.

**D-numbering (internal jargon, defined only in DTA docstrings — do not guess):**
`D-1` = `DivineSubjectRole` (Tag VOCAB, the role sort, `DTA:2716-2742`);
`D-2` = `TrinitarianPersonalBridge` (Tag META, `DTA:2671-2672` — roles, `Person`,
`FreeSubject`, `NecessarySubject`, exhaustion `NecessarySubjectKind s → s = a ∨ s = b ∨ s = c`);
`D-3` = `BoundedMeaningRequiresFreeSubject` (Tag TRANS, `BoundedMeaning.lean:116` — its
antecedent is `PassiveIntentionalPotency e ∧ ∃ p, EntityMeans e p`, which never fires on a
semantically total subject; `guard_excludes_exactly_the_impersonal_cases`,
`BoundedMeaning.lean:158`). The new totality axiom would be the next **D**-number only if
the codebase's numbering is extended; otherwise give it a plain name (§5).

## 2. Current kernel state (verified this session)

Two axioms, both in `formal/Logos/DivineTrinitarianAttributes.lean`:

- `:198` `axiom SemanticFinitude : ∀ s : Subject, ContingentSubjectKind s → ∃ p : Prop, ¬ Means s p`
  — `Tag: VOCAB`, scoped 2026-10-03 (S5), **0 dependents** (inert; the audit lists only the
  axiom itself). The *named* axiom the user names is already creature-only.
- `:243` `axiom GroundTranscendence : ∀ s : Subject, ∃ p : Prop, ¬ Means s p`
  — `Tag: META`, **27 dependents** (28 audit entries incl. the axiom itself) from
  `formal/axiom_audit.json` (5 939 decls). **This is the axiom
  that actually reaches the Divine Persons.** Deleting/replacing it is the core edit.

`ContingentSubjectKind s := ¬ NecessarySubjectKind s` (`Agency.lean:67`).
`NecessarySubjectKind : Subject → Prop` is `Agency.lean:62` (VOCAB).
The three Persons are `NecessarySubject` via `TrinitarianPersonalBridge`
(`DTA:2835`, Tag META, conjuncts: roles, `Person`, `FreeSubject`, `NecessarySubject`,
and exhaustion `∀ s, NecessarySubjectKind s → s = a ∨ s = b ∨ s = c`).
`Plurality.kinds_are_the_modal_partition : NecessarySubjectKind s ↔ NecessarySubject s`
(`Plurality.lean:82`) is FREE (vocabulary only) — gate-pinned by
`scripts/test_finitude_bound_scope.py:56`.

**The denial chain (what must stop):**
`kinds_are_the_modal_partition` (free) + `NecessaryKindAudit.necessary_kind_subject_lacks_maximal_capacity`
(`formal/Logos/DivineThomisticProduction.lean:594`, body `obtain ⟨p,hp⟩ := GroundTranscendence s`)
⇒ `¬ MaximalCapacity (EntityOf p)` for each of the three Persons. Reader surfaces celebrating
this: `scripts/test_finitude_bound_scope.py:150` ("DENIED at a META price"),
`README.md:1771`, `investigations/ledger.md:3297`, `base.txt:2423-2425`,
`theorems/T24.txt:261-262`.

### 2.5 Repo layout after the 2026-10-08 consolidation (read this before grepping)

Commits `ae2b945` ("code surface reduction") + `30045fd` ("attempt readme correction",
which also committed this file) merged the ~30 divine-characteristics/frontier modules:
active kernel is now 53 modules in `formal/Logos/` (incl. three new big files —
`ModalCreationFrontiers.lean` 4 040 lines, `AgencyAuditsAndFrontiers.lean` 6 976,
`ActionAndNormativeChoice.lean` 3 324). Verified 2026-10-08: **all three new modules
contain 0 references to `GroundTranscendence`/`MaximalCapacity`/`CanonicalAseity`** — no
new denial content. The pre-consolidation originals live on, **unbuilt**, in
`formal/archive/` (`consolidated_exploratory/` 28 files: `AdversarialReductioAudit`,
`ActionChoiceDefinitions`, `CognitiveDiscrimination`, …; `divine_characteristics_constituents/`:
`NecessaryKindAudit`, `TrinitarianSubjectBridge`, `CharacteristicClosure`,
`CharacteristicSoleBearer`, `Precedence`, `SemanticFinitude`, …;
`exploratory_freedom/`). Consequences for this task:

- The old GT-dependent copies in `formal/archive/divine_characteristics_constituents/`
  still contain GT statements and footprints — **every "no X anywhere" assertion and the
  §4.5 gate must scope to active `formal/Logos/*.lean`, never to the whole `formal/`
  tree.** `Logos.lean` does not import `formal/archive/`; `lake build` never sees it.
- Stale in-repo cross-references to the old paths already exist: `DTA:725` and `DTA:1115`
  cite `SemanticFinitude.lean:151` — that file is now
  `formal/archive/divine_characteristics_constituents/SemanticFinitude.lean`. The docstring
  rewrite (§7) fixes these to the live `DTA:198` location.
- Context (untracked, not normative): `investigations/consolidation_roadmap.md` documents
  the module merge and workspace hygiene; `investigations/archived_plans/` now holds the
  old root scratch plans (`ISSUE_K_PLAN.md` etc.); `investigations/issue-k/` +
  `issue-k-meaning-coherence-audit.md` hold the countermodel meaning-coherence audit.

## 3. The hard kernel fact (why a mere re-scope is not enough) — DEFINITIONALLY CHECKED

- `OneEssence a b := ∀ p, EntityMeans b p → EntityMeans a p`
  (`RecoveredOntologicalGround.lean:72`)
- `EntityMeans (EntityOf s) p = Means s p`; `EntityMeans Entity.ofGround p = True`
  ⇒ **`OneEssence (EntityOf s) Entity.ofGround ≡ ∀ p, Means s p`**
- `ExternalGrounding g e := g ≠ e ∧ OneEssence g e` (`DivineClassicalAttributes.lean:514`)
- `CanonicalAseity e := ¬ ∃ g, ExternalGrounding g e` (`:519`)
- `UniversalModalGround g := ∀ w e, ExistsAt w e → e = g ∨ OneEssence g e` (`:1696`)
- `MaximalCapacity e := ∀ p, EntityMeans e p` (`:1771`)

Consequences (all verified):

1. A semantically total Person's correlate **is** an `ExternalGrounding` of the ground
   (`EntityOf s ≠ ofGround` is free, `ofGround_ne_ofSubject`, `DivineClassicalAttributes.lean:1993`)
   and **is** a second `UniversalModalGround`. So:
   - unrestricted `CanonicalAseity Entity.ofGround` and Persons'-totality are
     **jointly contradictory** — there is no re-tagging/re-scoping that keeps both;
   - `exactly_one_universal_modal_ground` (`:2163`, the Classical Monotheism row C320)
     is **false** once totality is asserted, and must be restated modulo the Persons.
2. The kernel already records the trade as undecided:
   `DivineClassicalAttributes.lean:1719-1720` — "repairing `OneEssence` would make
   grounded Persons rival grounds and that trade has not been decided."
   **Read `unconditional_aseity_independent_of_bare_agency` (`:622`) precisely — I read its
   statement this session: it is a signature-model existence,**
   `∃ (Subj : Type) (MeansRel : Subj → Prop → Prop) s, (∀ p, MeansRel s p) ∧ …` proved
   `{}` over `Unit` — i.e. "unconditional aseity is not a theorem of bare unconstrained
   `Means`". It is **not** a Γ theorem of aseity, proves nothing about Γ's consistency,
   and carries **no** weight for or against Option E. Do not cite it as a countermodel to
   the design; the real evidence is §5's completeness check.
3. The *conditional* originals keep their anonymous premise and are untouched/free:
   `conditional_canonical_aseity (hFinite)` (`:592`), `ofGround_modal_aseity_conditional`
   (`:608`), `ofGround_non_composite (hFinite)` (`:719`), `ofGround_divine_simplicity`
   (`:820`), `ofGround_simplicity_and_transcendence` (`:831`), `exactly_one_universal_modal_ground
   (hNoTotal)` (`:2164`), `ofGround_sole_universal_grounding (hNoTotal)` (`:2146`),
   `ofGround_unicity_from_no_discriminating_subject` (`:2097`), the AsieticChoice one
   (`AsieticChoice.lean:675`), `discriminating_subject_cannot_ground_the_ground (s) (hDiscrim)`
   (`:572`), `discriminating_subject_fails_pure_actuality`. **Only the `_stipulated`
   corollaries and the `ofSubject s` case-splits are unconditional, and those are the
   27 dependents.**

## 4. The 27 dependents (from `formal/axiom_audit.json`) and their two lanes

**Lane A — 24 decls, subject arbitrary (`ofSubject s` case-split gives NO kind info):**

- 10 `_stipulated` corollaries in `DTA:261-323` (first decl at :262, last ends :323;
  names unchanged):
  `exactly_one_universal_modal_ground_stipulated`, `ofGround_sole_universal_grounding_stipulated`,
  `conditional_canonical_aseity_stipulated`, `ofGround_modal_aseity_conditional_stipulated`,
  `ofGround_divine_pure_actuality_stipulated`, `ofGround_no_grounding_potency_stipulated`,
  `ofGround_divine_simplicity_stipulated`, `ofGround_non_composite_stipulated`,
  `ofGround_simplicity_and_transcendence_stipulated`, `ground_is_canonically_aseitous_but_not_asietic_stipulated`
  (`AsieticChoice.ground_is_canonically_aseitous_but_not_asietic` is the underlying conditional).
- `SemanticFinitude.semanticFinitude_excludes_ground_from_subjects` (`DTA:382`) — conclusion
  is FREE via `ofGround_ne_ofSubject`; GT was added only "so the price appears" — drop GT,
  re-prove free.
- `Precedence.ofGround_sole_precedes_right_wrong` (C433, `DTA:745`) and
  `Precedence.precedence_identifies_the_ground_where_stage_invariance_does_not` (C435, `:813`).
- `CharacteristicSoleBearer` (namespace `DTA:1150-1361`): `no_subject_grounds_the_ground` (C441, `:1180`
  — the `obtain ⟨p, hp⟩ := GroundTranscendence s` is in the proof body following),
  `ofGround_sole_foundational_omniscience`
  (C442, `:1200`), `..._omnipotence` (C443, `:1237`), `..._omnipresence` (C444, `:1263`),
  `..._divine_pure_actuality` (C445, `:1287`), `the_ground_is_sole_bearer_of_the_footprint_characteristics`
  (C446, `:1312`).
- `CharacteristicClosure` (namespace `DTA:902-1087`; section intro `:840-870`):
  `the_ground_is_divinely_simple` (C484, `:936`),
  `some_entity_is_divinely_simple` (`:942`), `the_ground_is_sole_bearer_of_divine_simplicity` (C485, `:962`),
  `transcendence_and_semantic_finitude_yield_divine_simplicity` (C486, `:1033`).
- Master theorem unicity conjunct: `TrinitarianSubjectBridge.one_necessary_ground_three_free_necessary_persons`
  (`DTA:3003`), consumed at **exactly one line, `DTA:3018`**
  (`exact exactly_one_universal_modal_ground Logos.SemanticFinitude.GroundTranscendence`).
  Only conjunct 2 (unicity) is priced; conjunct 3 (three Persons, freedom, perichoresis)
  rests on `TrinitarianPersonalBridge` alone and is untouched.

**Lane B — 3 decls, subject ALREADY `NecessarySubjectKind` (these ARE the denial):**

- `DivineThomisticProduction.lean:594` `necessary_kind_subject_lacks_maximal_capacity` — DELETE/FLIP.
  (Body confirmed `:597`: `obtain ⟨p, hp⟩ := GroundTranscendence s`.)
- `:608` `necessary_kind_subject_fails_pure_actuality` — body confirmed `:611`:
  `discriminating_subject_fails_pure_actuality s (GroundTranscendence s)` — i.e. it applies
  the *conditional* (`DCA`, premise-taking, stays free) with GT supplying the premise.
  Under E the premise is false for Persons, so this must be **re-proved free** — see §5
  part 3. The free route covers only the `no_grounding_potency` field in the current draft;
  the declaration's footprint (`Initiates`, `State`) means `DivinePureActuality` has more
  fields — re-proving `¬ DivinePureActuality` only needs ONE failing field, but verify the
  structure's exact fields before assuming the one-liner suffices.
- `:651` `the_second_necessary_being_profile` — update cells (drop/flip `¬ MaximalCapacity`,
  keep `¬ DivinePureActuality` via the free route).

**No GT references outside DTA + DTP** (confirmed: `grep GroundTranscendence formal/Logos/*.lean`
→ 59 hits in DTA, 6 in DTP, **0** in `AsieticChoice.lean` and everywhere else — the
`AsieticChoice` stipulated corollary lives in DTA). Migration touches 3 Lean files at most.

**There is no contingent lane:** Γ has **no theorem inhabiting `ContingentSubjectKind`**
(`DivineClassicalAttributes.lean:418-421` — "every occurrence of it in the corpus is a
hypothesis"; population of the necessary kind comes only from the bridge, C404). The
scoped bound is only usable via a classical case split:
`rcases Classical.em (NecessarySubjectKind s) with hNec | hCon` (or `by_cases`).
This is the implementation idiom for every migrated case-split:
necessary branch ⇒ carved out (conclusion permits the Persons);
contingent branch ⇒ `SemanticFinitude s hCon` ⇒ `∃ p, ¬ Means s p`.

### 4.5 Completeness argument (recorded 2026-10-08 so it need not be re-derived)

The migration is safe **iff** the 27 dependents are the *complete* set of kernel statements
refuted by the new totality axiom — a statement refuted by the axiom but proven *without*
GT would silently make the theory inconsistent, and **Gate A's probe would probably not
catch it** (the probe is a fixed short route: bridge + `ofGround_ne_ofSubject`; Lean does
not derive `False` in general just because the axioms are inconsistent — someone must
write the term). Spot-checks performed this pass, all negative (no refutable statement
found outside the 27):

- Unconditional `CanonicalAseity Entity.ofGround` exists **only** via the `_stipulated`
  corollaries (`DTA:276`, `AsieticChoice` variant via DTA:321) — the underlying results are
  all premise-taking (`conditional_canonical_aseity (hFinite)` etc.). Verified by grep.
- `¬ MaximalCapacity` sites: only lane B (`DTP:596`, `:656`) and the closed biconditional
  `no_discriminating_subject_iff_no_maximal_non_ground` (`DCA:2113`), which stays TRUE
  under E (both sides become false). Nothing else in `Logos/*.lean`.
- `s4_does_not_make_the_ground_a_fourth_chooser : ¬ Asiety Entity.ofGround`
  (`DTA:3087`, FREE) is **not** refuted by E: E only *adds* grounding relations, so
  `Asiety` stays false and the free theorem stays true.
- `noMeaning_is_unmeaned` is conditional on `NoMeaning`, which is refuted; `MeansAt`
  occurrences are parameterised signature models; D-3's antecedent never fires on total
  subjects; `HostileSemantics:2213` is model-internal.
- `OneEssence`/`ExternalGrounding` with the ground are *positive* theorems under E, not
  contradictions — the danger is only for statements asserting their **negation**, and all
  such statements needed GT (that is what GT-dependence means).

**Turn this into a gate assertion** when re-authoring `test_finitude_bound_scope.py`: no
declaration outside an explicit allow-list may have a statement of the form
`¬ Means _ _` / `¬ MaximalCapacity _` / `¬ OneEssence _ ofGround` / `¬ CanonicalAseity _`
without `GroundTranscendence` in its (now empty) vocabulary — or, simpler and stronger:
assert the old GT shape appears nowhere in any theorem statement in active
`formal/Logos/*.lean` (**active only**: `formal/archive/` holds the pre-consolidation
copies with stale GT statements and is not built — see §2.5).
Re-run the spot-checks once after the kernel edit as a belt-and-braces pass.

**Claim-id map for the 27 (from the GAPMAP META roster, `:2241-2253`):** 24 of them carry
rows — `GroundTranscendence` (24): C389–C398, C400, C433, C435, C441–C446, C484–C486,
C491, C497. The 3 without C-ids are the master-theorem unicity conjunct (inside the
`TrinitarianSubjectBridge` row) and the two lane-B theorems
`necessary_kind_subject_lacks_maximal_capacity` / `..._fails_pure_actuality`.

## 5. The design (Option E + named-Persons carve-out) — what to build

### 5.0 Implementation order (binding — the count pin and the build both constrain it)

Do **not** interleave freely; each step leaves a green `lake build`:

1. **Add the new axiom** (part 1.2). Count transiently becomes **40** — expected; the
   pin test is run only at the end. Keep GT for now.
2. **Migrate the 24 lane-A consumers** (part 2), file by file: DTA first (59 mentions,
   mostly docstrings), then DTP. Build after each file. The proofs stop referencing GT but
   GT stays declared.
3. **Flip lane B** (part 3): delete `necessary_kind_subject_lacks_maximal_capacity`,
   re-prove `..._fails_pure_actuality` free (start with the helper of §5 part 3 and check
   it compiles before touching the declaration), update `the_second_necessary_being_profile`.
4. **Delete `GroundTranscendence`** (part 1.1) — now unreferenced, so the build stays green.
   Count returns to **39**.
5. **Update pins and gates** in the same change: `check_consistency.py` comment,
   re-authored `test_finitude_bound_scope.py`, re-derived `census_semantic_finitude.py`
   EXPECT counts.
6. **Regenerate artifacts** (§8), then prose sync (§7), then run the full §8 sequence.

Never commit an intermediate state (40-axiom transit, or GT present with unfixed gates).

**Kernel, part 1 — swap the bound:**

1. DELETE `axiom GroundTranscendence` (`DTA:243`) with its whole docstring section
   (`DTA:199-242`; keep the historical record in prose files, not in the kernel).
2. ADD a new declared axiom asserting the Persons' totality, e.g.:
   ```lean
   /--Tag: META
       **Divine semantic fullness.** ... -/
   axiom DivinePersonsTotalMeaning :
     ∀ s : Subject, NecessarySubjectKind s → ∀ p : Prop, Means s p
   ```
   Kind-scoped is equivalent to the three Persons (bridge exhaustion), and keeps positive
   rows from needing the bridge for the *statement*. Tag **META** (metaphysical bridge).
   `check_consistency.py` Gate B scans axiom statements for banned shapes
   (`EntityOf _ = divineReality` etc.) — this shape is clean; Tag must be in the
   closed vocabulary.
3. **Axiom count: 39 → 39** (delete 1, add 1). The constant is
   `EXPECTED_AXIOM_STATEMENTS` at `scripts/check_consistency.py:85`, pinned at **39**
   (= 18 VOCAB + 6 SEM + 13 META + 2 TRANS, derived by `test_axiom_census.py`,
   cross-checked against `depgraph.json`).
   **Trap I fell into:** the comment block at `check_consistency.py:61-70` still says
   "(40 statements: 18 VOCAB, 7 SEM…)" and "S5 took this from 39 to 40" — **stale**,
   contradicted by the correction directly below it at `:83-84` ("S5 moved 38 → 39,
   not 39 → 40"; the old "40" was 39 axioms plus a comment-phantom — AGENTS.md) and by
   the passing census (GAPMAP `:3865`, `:3939`, `:3958` all say 39). My earlier draft
   said 40 because I read the stale comment instead of the constant. When the axiom is
   swapped, **rewrite the `:61-70` block** (it must describe this milestone, not S5) and
   keep the pin at 39. Never assert the count by eye;
   `python3 scripts/test_axiom_census.py` derives it.

**Kernel, part 2 — restate lane A conclusions modulo the three named Persons:**

Pattern for every `ofSubject s` case-split and every `_stipulated` corollary:
replace "the only X is the ground" by
"the only X is the ground **or one of `EntityOf a`, `EntityOf b`, `EntityOf c`**"
(where a,b,c are the bridge witnesses; use an `∃ a b c`-packaging or a namespace-level
helper to avoid naming hygiene problems). Proof idiom:

```lean
rcases Classical.em (NecessarySubjectKind s) with hNec | hCon
· -- Person: carved out by the new conclusion
  right; obtain ⟨a,b,c,...⟩ := TrinitarianPersonalBridge
  -- (hNec + exhaustion) ⇒ s = a ∨ s = b ∨ s = c
· -- creature: scoped bound does the old work
  obtain ⟨p, hp⟩ := SemanticFinitude s hCon
  ... (old argument, verbatim) ...
```

Concrete statement changes needed (verify each by building):

- `ConditionalAseity`-family: `CanonicalAseity Entity.ofGround` becomes
  "no entity **other than the three Persons' correlates** externally grounds the ground"
  — either a new def (`CanonicalAseityModuloPersons`) or restated inline. Note the
  Catholic reading: Person-correlate "grounding" of the ground is *procession*, not
  foreign dependence (`ExternalGrounding` is misnamed for that case; disclose in the
  docstring, do not silently redefine `ExternalGrounding` — that ripples everywhere).
- `exactly_one_universal_modal_ground`-family (C320/C389): `∀ g', UMG g' → g' = ofGround
  ∨ g' = EntityOf a ∨ g' = EntityOf b ∨ g' = EntityOf c`. Proof: `g' = EntityOf s` ⇒
  UMG instantiated at `ofGround` (which exists at every world — use
  `ofGround_universal_modal_ground`'s supporting facts / `ExistsAt w Entity.ofGround`)
  ⇒ `OneEssence (EntityOf s) ofGround` ⇒ `∀ p, Means s p` ⇒ scoped bound kills the
  contingent branch ⇒ exhaustion ⇒ named disjunction.
- `SoleUniversalGrounding.unicity` field (`:2141`) and `subject_transcendence` field
  (`:2139`, note: for the ground itself `subject_transcendence` is FREE —
  `fun s _ hEq => by cases hEq` at `:2151` exploits the constructor clash).
- `Precedence` C433/C435, `CharacteristicSoleBearer` C441-C446, `CharacteristicClosure`
  C484-C486 — same modulo-Persons restatement.
- `no_discriminating_subject_iff_no_maximal_non_ground` (`:2111`) is a closed
  biconditional; under E **both sides become false** (Persons are non-ground maximal
  entities), so it stays TRUE and its existing proof (a pure equivalence) still works.
  Only its prose gloss needs re-reading.

**Kernel, part 3 — flip the direct denial:**

- DELETE `necessary_kind_subject_lacks_maximal_capacity` (`DivineThomisticProduction.lean:594`)
  and REPLACE with the positive `MaximalCapacity (EntityOf a)` etc. derived from the new
  axiom (via `kinds_are_the_modal_partition` to get `NecessarySubjectKind a` from the
  bridge's `NecessarySubject a`).
- RE-PROVE `necessary_kind_subject_fails_pure_actuality` (`:608`) **free**: `DivinePureActuality`
  has field `no_grounding_potency : ¬ PassiveGroundingPotency`; `PassiveGroundingPotency`
  (`DivineClassicalAttributes.lean:2331`) holds for every subject's correlate because
  `ground_conditions_every_content_bearer` (`DTA:606`, decl; docstring `:604-605`, free,
  `fun _ _ _ _ => trivial`)
  + `ofGround_ne_ofSubject` give `ExternalGrounding Entity.ofGround (EntityOf s)`.
  **No theorem currently states that one-liner — prove it as a small helper first and
  check it compiles.**
- UPDATE `the_second_necessary_being_profile` (`:651`): drop the `¬ MaximalCapacity` cell
  (or flip it), keep `¬ TranscendentGround` (definitional/free) and `¬ DivinePureActuality`
  (free route above).

**Consistency sanity (not a gate, but think it through):** the new totality axiom must not
contradict anything live. Checked this session:
- `BoundedMeaningRequiresFreeSubject` (`BoundedMeaning.lean:116`, Tag TRANS): antecedent
  is `PassiveIntentionalPotency e ∧ ∃ p, EntityMeans e p`; `PassiveIntentionalPotency e
  := ∃ p, ¬ EntityMeans e p` (`DivineClassicalAttributes.lean:2367`) ⇒ under totality the
  antecedent NEVER fires on a Person — exactly what `BoundedMeaning.lean:62-64` and
  `DTA:3030-3038` already document. Freedom of the Persons rests on D-2 alone
  (`the_three_persons_freedom_is_asserted_not_earned`, `DTA:3046`). No conflict.
- `MeaningRetorsion.noMeaning_is_unmeaned` is conditional on `NoMeaning`, which is refuted
  (`NoMeanerNoFalsity.no_meaning_world_is_impossible`).
- `MeansAt` occurrences (`AdversarialReductioAudit`, `ActionChoiceDefinitions` — both now
  in `formal/archive/consolidated_exploratory/`, unbuilt — and `HostileSemantics`, still
  active) are parameterised free-signature models, NOT Γ's `Means`.
- `HostileSemantics.lean:2213` denies existence of contingent subjects **inside a signature
  model**, not in Γ.
- No live theorem proves `∃ p, ¬ Means s p` for arbitrary `s` by any route other than
  `GroundTranscendence` (grep `¬ Means` done this session; the only other hits are
  conditional premises or local models).
- Run `scripts/check_consistency.py` (Gate A probe must FAIL to compile = theory still
  consistent; Gate B syntactic scan) after any axiom change.

## 6. Gates and scripts to re-author (in the same change, not after)

- `scripts/test_finitude_bound_scope.py` — **its assertion inverts.** Confirmed internals
  this pass: `DENIAL_CHAIN` tuple at `:47` (declarations "that make the Persons' denial of
  maximal capacity reachable", absence-checked per-decl at `:90-92`), dependent-distribution
  math at `:117-149`, `FAIL: … has no dependents` at `:138`, `FAIL: … does not rest on
  UNRESTRICTED; §17's denial chain no longer holds` at `:143-144`, summary prints
  "0 dependents — inert" at `:148` and "DENIED at a META price" at `:150`. Its docstring (`:13-29`) already prescribes the
  post-milestone state: "If a future milestone genuinely narrows the bound, this gate fails
  and the prose obligation transfers with it: §1.7/§10/§11 may then say 'unasserted', and
  only then." New assertions to consider: `GroundTranscendence` absent from
  `axiom_audit.json`; `SemanticFinitude` has ≥ 1 dependent (invert `:138`); the lane-B
  denial decls absent or flipped (invert `:142-144`); **the §4.5 shape rule** (no residual
  GT-shaped theorem statements); the positive totality axiom exists and has dependents;
  `kinds_are_the_modal_partition` stays free (keep the `FREE_LINK` check at `:54-56`).
- **Consistency probe:** consider extending `formal/consistency/FalseNotDerivable.lean` —
  the current route (bridge + `ofGround_ne_ofSubject`) would likely **miss** an
  inconsistency of the form "kernel ⊢ T, new axiom ⊢ ¬T" (see §4.5). A cheap addition:
  assert `False` is not derivable from the new axiom + any free theorem whose statement
  negates a total-meaning consequence (e.g. instantiate a risky free theorem on a
  necessary-kind subject). Gate A's contract stays: the probe must FAIL to compile.
- `scripts/check_consistency.py:85` — the pin constant (39). **Also rewrite the stale
  `:61-70` comment block in the same change** (see §5 part 1.3).
- Two more GT-mentioning scripts for the inventory (discovered this pass):
  `scripts/stipulated_def_allowlist.json:146` — the `AsymmetricGrounding` REFUTED entry
  references the live unicity route "via GroundTranscendence/SemanticFinitude
  (GAPMAP C320/C389)": reword to the new route (totality/carve-out) or it misdirects;
- `scripts/author_reading_path_prose.py:144` — emits "declared META bound
  (`GroundTranscendence`: no subject means every proposition, unrestricted)": same
  treatment. (`test_generator_price_prose.py` `SOURCES` at `:26-28` includes this file,
  so the price-prose test will police the rewording.)
- `scripts/census_semantic_finitude.py` — docstring still quotes the UNRESTRICTED form
  at `:4`; its `EXPECTED` occurrence counts will drift as consumers re-point — re-derive,
  do not hand-patch numbers.
- `scripts/test_generator_price_prose.py` — `SOURCES` includes `AGENTS.md`,
  `presentation_spine.json`, `build_deduction.py`, `author_reading_path_prose.py`; it will
  reject Tag-attribution errors after the re-tag.
- `scripts/test_axiom_census.py`, `scripts/test_goal_audit.py` (+ `goal_audit_fingerprint.py`),
  `scripts/audit_stipulated_defs.py`, `scripts/test_deduction_dependencies.py`,
  `scripts/test_circularity_audit.py` — run all; statements changed ⇒ `goal_audit.json`
  and any fingerprints must be regenerated.
- `Makefile:81, :110, :146` — comments referencing SemanticFinitude/GroundTranscendence scope.
- `scripts/build_deduction.py` hand-authored prose (see §7) — remember the AGENTS rule:
  **chain-list membership is hand-maintained**; `SEMANTIC_FINITUDE_STEPS` at
  `build_deduction.py:10477-10515` (header verified at `:10477`, chain glosses `:1004-1012`,
  Chain-14 header `:11854-11861`) needs its C388 entry corrected. Note the regenerated
  ledger already shows the drift: `ledger.md:3277` prints C389's footprint as
  `{Means, NecessarySubjectKind, SemanticFinitude, Subject}` while the audit says
  `GroundTranscendence`, and `ledger.md:4033/4040` say C497 pays the "SemanticFinitude
  price" while its footprint is GT — fix at the `build_deduction.py` source cells
  (monotheism cluster `:9127-9225`, C497 cell `:11881`), never in the ledger.

## 7. Prose / surface inventory (edit sites, with lines) — `AGENTS.md` sync rule applies

Hand-authored cells that GENERATE reader prose (never hand-edit README/ledger/kernel-audit — regenerate):

- `formal/presentation_spine.json:813` — the README sentence "**The three divine Persons are
  denied full omniscience too**…" (currently `README.md:1771`; PROMPT's earlier `:865/1896`
  were pre-consolidation — the spine file changed 826 lines in `30045fd`).
- `scripts/build_deduction.py:9643` — the ledger `sense` cell with the same denial text
  (currently `ledger.md:3297`; earlier `:9634/2522` pre-consolidation). Note the ledger's
  evolved wording: "denied full **capacity**", footprint "two META axioms".
- `build_deduction.py:9127-9225` (monotheism row prose: `sense` opens `:9127`, decl anchor
  `:9192`, the re-tag warning comment at `:9204` — hand-written `sense` "does NOT fail
  when a bound is re-tagged", the exact silent-drift hazard — C389 line `:9225`).
- `build_deduction.py:11015` ("Cost of the C388 declaration", axiom-count story;
  references `formal/Logos/SemanticFinitude.lean` — an archived path, fix the pointer),
  `:11361` (C433 chain tuple), `:11513` (C441, "the one place this batch pays F15" —
  misattributed),
  `:11805` (comment "C484-C486 and C491 are PROVEN because SemanticFinitude has Tag VOCAB"),
  `:11881` (C497 sense cell — verified: TranscendentGround paragraph),
  `:12123` (C494/C495 sense cell — verified: *ST* I q.19 a.4 paragraph), `:12857`
  (FoundationalUnicity phantom-decl note), `:10477-10481` (SEMANTIC-FINITUDE chain header).
- **Found this pass:** `build_deduction.py:11854-11861` — **Chain 14 header** ("C497 profile
  … lacks transcendence/maximal capacity/pure actuality" — the maximal-capacity cell flips)
  and `:1004-1012` — the chain-list glosses (`"C497 — the profile: has necessity and gapless
  operativeness, lacks transcendence/maximal capacity/pure actuality"` etc.). Chain-14
  membership itself is hand-maintained (AGENTS rule).
- **Found this pass:** GAPMAP stale blocks beyond the ones previously listed:
  **`:2016-2031`** (claims "C441–C446 price `SemanticFinitude`" — wrong *today*, they price
  `GroundTranscendence` per row `:296`), **`:2090-2091`** (calls C496/C497 vocabulary-only
  while row `:447` lists `GroundTranscendence`), **`:591`** ("Logo: um sujeito não pode ser
  um chão universal" — derived from C441's unrestricted statement, must be reworded modulo
  the Persons). Fix all while in the file; GAPMAP tests check status/footprint cells
  against derived values, not this prose, so these rot silently.

Prose corpus (Portuguese — keep language):

- `base.txt:2395-2432` (§34 bis FINITUDE-SPLIT; **:2423-2425 is the "negação … NÃO foi
  removida — foi reatribuída" paragraph** — now it IS removed/reversed; rewrite as a new
  dated milestone, do not delete the history).
- `theorems/T24.txt:245-262`, `theorems/T6.txt:163-172`, `theorems/T21.txt:79-114`.
- `formal/GAPMAP.md` — C388 rows (`:770`, `:820`), C389-C400 (`:821-832`; verified:
  summary `:770-782`, detail `:820-832`), C441-C446 (`:296-301`; verified all six),
  C484-C486 (`:538-540`, C491 at `:545`), C494-C498 (`:444-448`), the axiom roster with
  the GT entry (`:2236-2253`; verified: "`GroundTranscendence` (24…): C389–C398, C400,
  C433, C435, C441–C446, C484–C486, C491, C497"),
  **stale pre-split paragraph `:2085-2105` (still claims C496/C497 pay
  `SemanticFinitude` as PROVEN — fix while here)**, F15 row `:3613` (verified: still the
  UNRESTRICTED missing lemma + "27th axiom" + "every subject is meaning-restricted"),
  bucket counts (`:1962-1968`, `:2094-2105`). GAPMAP status/footprint cells are CHECKED against derived
  values — edit to match the new audit, then run the tests.
- `formal/Logos/ClaimMeanings.lean:205` (`F15` — long reader gloss, still unrestricted form
  and 27th-axiom story), `:241` (`C400`).
- Lean docstrings that misquote the bound: `DTA:725` (verified content; also cites
  archived `SemanticFinitude.lean:151`),
  `DTA:1115` and `:1171` (verified: module header still "SemanticFinitude … 27th axiom …
  Tag VOCAB, `SemanticFinitude.lean:151`" while writing the unrestricted formula),
  `DTA:1254` (verified: "exactly what `SemanticFinitude` denies"), `DTA:2983-3004`
  (verified: unicity price note), `DTA:166-197` (the `SemanticFinitude` docstring —
  axiom at `:198` — update "Scoped on 2026-10-03" section to record THIS milestone),
  `DivineThomisticProduction.lean:588, 617-657` (verified regions).
- `CHARACTERISTICS.md:331` (verified: Precedence disambiguation line; C433 price
  misattributed to `SemanticFinitude`).
- `investigations/kernel-audit.md` — regenerated in `30045fd` (2 494 lines): audit
  mismatches at `:231-240` (C444–C446, C497; verified), C441 row at `:303` (verified),
  C485 at `:353`, C433 at `:456`, C441 detail at `:464`. **Resolved 2026-10-08: this file
  IS generated** — `build_deduction.py:15105` renders it (`Makefile:152-154` builds
  README.md + kernel-audit.md together). Same rule as README/ledger: **never hand-edit**;
  fix the generator cells, and note its content lags the kernel the same way the ledger
  does (e.g. it still prints GT footprints everywhere).
- `ISSUES.md:229`, `AGENTS.md` — no denial text found (grep done), but AGENTS will need the
  new gate/scope rule recorded if behaviour changes materially.
- **Dangling references (re-checked 2026-10-08):** the gate and GAPMAP cite "plan
  §1.7/§8.2/§10/§11/§17" and `READINGPATH.md` — `READINGPATH.md` does not exist, and
  `RULE_R_CORRECTION_PLAN.md` exists but has only §§0–12 (no §17, no §1.7/§8.2, and its
  §10/§11 are "VERIFICATION COMMANDS"/"IMPLEMENTATION ORDER", not the cited rows). Either
  create the plan section (a `PLAN-FINITUDE.md` or add to an existing plan) or drop the
  dead references; do not leave pointers to nothing.

## 8. Verification sequence (binding, from AGENTS.md)

```sh
export PATH="$HOME/.elan/bin:$PATH"
cd formal && lake build                      # must be green
cd ..
python3 scripts/check_consistency.py         # Gate A probe must FAIL to compile (green);
                                              # Gate B syntactic scan passes
python3 scripts/test_axiom_census.py         # derives the pinned count — never eyeball it
python3 scripts/test_finitude_bound_scope.py # re-authored first
python3 scripts/census_semantic_finitude.py
python3 scripts/test_generator_price_prose.py
python3 scripts/test_goal_audit.py
python3 scripts/test_argument_surface.py
python3 scripts/ledger_superset.py
cd formal && lake exe depviz --roots Logos --json-out depgraph.json --dot-out depgraph.dot
cd .. && python3 scripts/audit_footprints.py && python3 scripts/audit_goals.py \
     && python3 scripts/build_deduction.py   # regenerates README.md + investigations/ledger.md + investigations/kernel-audit.md
```
Run ONE `lake env lean` at a time (overlapping `.lake` access causes 21 % timing swings,
AGENTS.md). Do not hand-edit `README.md`/`investigations/ledger.md`/`investigations/kernel-audit.md`.

**Blast radius / effort estimate (2026-10-08):** ~3 Lean files (DTA heavy, DTP small,
AsieticChoice untouched — 0 GT refs), ~6 gate scripts (one major rewrite), 6 regenerated
artifacts (depgraph.json/.dot, axiom_audit.json, goal_audit.json, README.md, ledger.md,
kernel-audit.md), ~15 prose files + ~25 GAPMAP cells + 2 chain blocks + 1 spine cell. One long
session. **Difficulty is concentrated in four places:**
1. the UMG-modulo-Persons proof (needs `ExistsAt w Entity.ofGround` support facts — find
   how `ofGround_universal_modal_ground` gets them before writing the case split);
2. the `CanonicalAseity` restatement *shape* (new def vs inline — new def ripples into
   `canonical_aseity_implies_modal_aseity` consumers at `DCA:601-611`, `:2431`);
3. **README lint budget** — statements get longer (named disjunctions); `_lint_readme`
   enforces ≤900 chars per table cell and ≤300 chars per paragraph outside the score block,
   and `README_VISIBLE_BUDGET` enforces the 1715-line cap — expect to shorten prose while
   restating, not just lengthen it;
4. re-deriving `census_semantic_finitude.py` EXPECT counts (docstrings will cite
   `SemanticFinitude` far more often once the case-split idiom is quoted in them).

**Price/badge projection:** ~26 of 27 rows swap `GroundTranscendence` (META) for
`TrinitarianPersonalBridge` (META) → same single-substantive price, `AXIOMATIC` badges
survive; **every footprint cell still changes** (large mechanical GAPMAP wave). A few rows
drop to `PROVEN` outright (e.g. `semanticFinitude_excludes_ground_from_subjects`, whose GT
was added only "so the price appears"). Positive flips: `MaximalCapacity (EntityOf a)`,
`FoundationalOmniscience (EntityOf a)` etc. become provable — decide claim-ID lifecycle
for C494/C497 (flip cells in place vs retire; see §9.6).

## 9. Open points the next agent must resolve (in order)

1. **Confirm the Option-E reading of "more Catholic"** if anything in §1 looks off against
   the user's intent — but do not re-ask the two questions already answered; if genuinely
   unsure, show the user the two candidate *statements* (asserted vs open) rather than the
   abstract options.
2. Draft the new axiom's docstring + name (English, first paragraph is the gloss,
   `Tag: META`, footprint line) and the exact modulo-Persons wording for the unicity row —
   this is the doctrinally sensitive sentence ("one God, three consubstantial Persons;
   the Persons are not rival grounds but proceed from / are perichoretically one with the
    ground"). `Perichoretic ofGround a b c` already exists
    (`TrinitarianPersonalGround.ofGround_is_perichoretic`, `DTA:2499`).
3. Kernel edits §5 (order in §5.0), smallest possible diffs, building after each file.
4. Re-author the finitude gate (§6), then regenerate all artifacts (§8), then prose sync (§7).
5. Final: full §8 sequence green, then report per AGENTS (no commits unless asked).
6. **Claim-ID lifecycle decision** (can run in parallel with 3): C494/C495 keep their
   content (they already say the ground is *not* the only necessary being — they get
   *stronger*); C497's `¬ MaximalCapacity` cell flips to positive; C441–C446 statements
   change shape. Flip cells in place (same C-id, new text) or retire+replace? GAPMAP tests
   pin claim sets — check `test_argument_surface.py`/GAPMAP tests before choosing.
7. **The pure-actuality tension (see §11.4) — surface it to the user, do not silently
   decide.** The current plan *keeps* `necessary_kind_subject_fails_pure_actuality`
   (re-proved free), i.e. it fixes omniscience while entrenching "the Son and Spirit lack
   pure actuality". Options: (a) keep as-is and disclose the tension in prose;
   (b) also restate `PassiveGroundingPotency`/`DivinePureActuality` modulo procession
   (carve intra-Trinitarian grounding out of "deficiency"), which is a second, larger
   kernel change; (c) ask the user. Default if no guidance: (a) + explicit prose
   disclosure — never (b) silently.

## 10. Traps already sprung by others (do not repeat)

- **Never assert an axiom count by eye** — `test_axiom_census.py` is the only derivation
  (`AGENTS.md`; the phantom-comment axiom story). **Concrete instance, 2026-10-08:** the
  previous draft of this file said "40 → 40" because `check_consistency.py:61-70` still
  narrates S5 as "39 → 40" — while the constant at `:85` is pinned at **39** and the
  census passes at 39. Read the constant and the correction at `:83-84`, never the old
  comment.
- **Scope every "nowhere in the kernel" grep to active `formal/Logos/`** — since the
  2026-10-08 consolidation, `formal/archive/` holds pre-consolidation copies containing
  stale GT statements/footprints (`divine_characteristics_constituents/`) that are not
  built. Whole-`formal/` greps will false-positive.
- **Regenerated surfaces moved.** `README.md`, `ledger.md`, `kernel-audit.md`,
  `presentation_spine.json` and `build_deduction.py` were all rewritten by `30045fd`
  (README 529 lines, ledger 1 265, kernel-audit 2 494, spine 826, generator 135) — every
  line number for them in older notes (incl. earlier drafts of this file) is suspect;
  §7's are re-verified post-consolidation.
- Hand-written `sense` cells in `build_deduction.py` do NOT fail on re-tagging — they
  drifted once already (the warning comment is now at `:9204`).
- **Never describe a re-scope as done because prose says so** — that is exactly the §17
  failure `test_finitude_bound_scope.py` was written to catch; measure dependent
  DISTRIBUTION across the two bounds instead.
- Hand-written `sense` cells in `build_deduction.py` do NOT fail on re-tagging — the
  warning comment says so itself (now at `:9204`); the ledger already shows the drift
  (`ledger.md:3277` prints a `SemanticFinitude` footprint the audit denies).
- Comment-scan hazard: no module-docstring line may begin at column 0 with `axiom <ident>`
  (`DTA:138-145`) — `build_deduction.load_decls` does not strip comments.
- `{}` countermodels must instantiate the vocabulary they deny; signature models are not
  candidate states (C559, AGENTS.md 2026-09-29).
- Prose corpus language is **Portuguese**; Lean comments/docstrings **English**;
  conversation matches the user.

## 11. Philosophical consequences (plain statement — written for the wording decisions in §9.2/§9.7)

Recorded because the *prose* of this migration is where it can go wrong: the doctrine
below is what the reworded statements must actually say, not a summary of it.

**The central shift.** Γ today is three-tiered — ground (unique, total, aseitic), Persons
(necessary and free but semantically cut off), creatures (bounded). After the change it is
two-realm: Godhead (ground + three Persons, all semantically total) versus everything
contingent. The system's load-bearing boundary becomes the single predicate
`∃ p, ¬ Means s p`, falling exactly where the user wants it: on creatures. A precise gain
follows: scoped bound (contingent → bounded) + new axiom (necessary → total) derive
**`NecessarySubjectKind s ↔ ∀ p, Means s p`** — modal status and semantic capacity
coincide (necessity = infinitude = total disclosure). That equivalence is false today; the
change repairs it.

**What is gained.** (1) Doctrinal regularity: the corpus currently asserts a
limited-Knowledge thesis about God's Persons and prices it META — the most un-Catholic
claim in the tree; it becomes the credal *homoousios*, META for META, honestly priced.
(2) A cleaner metaphysics: the ground/Person distinction stops being a difference of
*perfection* (sole-bearer rows C441–C446 dissolve into "shared with the Persons") and
becomes only a difference of **origin and operation** — attributes shared, relations differ.
The dualism relocates from a perfection hierarchy to the honest Christian one: Godhead vs
creatures. (3) The retorsion core (C553, creaturely bounded meaning, determinism-rebuttal)
is untouched and the creaturely bound *gains dependents* — the philosophical center is
reinforced.

**What is given up — four things, state them in prose:**
1. **Strict monotheism-as-uniqueness.** "Exactly one universal modal ground" becomes
   false (each Person's correlate is provably a second/third/fourth UMG). The replaceable
   theorem is "UMG(x) → x = ground ∨ x ∈ {a,b,c}". The anti-polytheism burden moves from
   the uniqueness theorem to **perichoresis**: four UMGs are one God by coinherence,
   because they can no longer be one by exclusion. If `ofGround_is_perichoretic` is thin,
   the monotheism defense is thin. This is the single most important structural
   consequence — the new monotheism row prose must say *this*, not re-assert uniqueness.
2. **Absolute aseity.** "Nothing outside the Godhead grounds the ground" survives;
   *within* the vocabulary, the Persons' correlates now do (it becomes a kernel theorem).
   "External" stops meaning "alien" and must be disclosed as procession — Γ's
   `ExternalGrounding` conflates creature-on-God dependence with Son-from-Father
   procession, and the predicate must NOT be silently redefined (ripples everywhere);
   the docstrings carry the distinction instead.
3. **The clean division of epistemic labor.** Today the omniscient one (ground) does not
   choose and the choosers (Persons) are not omniscient — that quietly dissolved the
   problem of divine knowledge/freedom. The change destroys the division: Γ must now say
   how an omniscient Person chooses. Its `FreeSubject` for Persons was always a bare
   bridge assertion ("freedom is asserted, not earned") and stays one, with **no
   mechanism**, while creaturely freedom has a full retorsion story; and the problem of
   evil lands squarely on free, fully-knowing Persons where boundedness previously blunted
   it. Divine freedom is confessed, not explained — consistent with doctrine, visible as
   an asymmetry in the ledger.
4. **The via negativa posture.** Γ loses its most distinctive heterodox flourish and the
   rhetorical drama of "the denial costs META". Orthodoxy is less striking.

**Also true and worth one clause somewhere:** exhaustion (`NecessarySubjectKind s →
s = a ∨ s = b ∨ s = c`) means **no intermediate infinite minds** — no angelic-tier
semantic totalities, no emanated infinite intellects; the semantic infinite is strictly
Trinitarian (Christian/Anselmian, not Neoplatonic). And the ground's totality is
*definitional* (`EntityMeans ofGround p = True`) while the Persons' is *priced* — i.e.
consubstantiality is confessed, not derived, which is exactly the Nicene status.

**The live tension (→ §9.7, must be surfaced).** The plan keeps
`necessary_kind_subject_fails_pure_actuality`, re-proved free: Persons are grounded, hence
lack `DivinePureActuality`. Classically pure act belongs to the divine essence *in each
Person* — procession does not make the Son less act. So the change trades one
anti-classical claim (limited omniscience) for another (Son and Spirit are not actus
purus), because Γ's definition of pure actuality (`no_grounding_potency`) treats any
grounding as deficiency. Either procession is exempted from that definition too —
restating C445/C497 exactly as aseity is restated — or the corpus, after all this work for
Catholicity, will assert that two of the Three Persons are not pure act. **This is the
sharpest philosophical consequence of the migration and it currently sits inside the plan
rather than being resolved by it.**

**One-line summary for the eventual report:** the change relocates Γ's metaphysics from a
perfection hierarchy to a shared-essence/ordered-relations model, sharpens the
infinite/finite line to exactly the creaturely bound, buys orthodoxy on omniscience, and
pays by making perichoresis, divine freedom, and (unless also restated) pure actuality the
places where dogma, not argument, carries the system.
