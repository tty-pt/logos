# CHARS.md — Characteristics Formalization Roadmap

> ⚠️ **HISTORICAL ROADMAP NOTICE:** This document (`CHARS.md`) records a research and implementation roadmap. For the authoritative, machine-checked state of the deduction and classical attributes, see [`README.md`](README.md), [`formal/GAPMAP.md`](formal/GAPMAP.md), and [`formal/Logos/`](formal/Logos/).

> **Purpose:** A reusable research and implementation plan for the characteristics discussed in `CHARACTERISTICS.md`.
>
> **Snapshot:** updated against the live working tree after the 2026-09-25 C182/C184/C183 batch. Re-audit the live files before changing anything; this document is a roadmap, not an authority over `formal/axiom_audit.json`, `formal/GAPMAP.md`, or the Lean kernel.
>
> **Important:** This file is deliberately not a generated deduction artifact. It records the state of the project and the safest next experiments. It does not promote a candidate to a theorem, and it does not make a blocked bridge sound by describing it optimistically.

## 1. How to use this document

Read this file before starting a new characteristics milestone. The canonical sources, in order of authority, are:

1. `formal/Logos/*.lean` — actual declarations and proofs;
2. `formal/axiom_audit.json` — exact transitive `#print axioms` footprints;
3. `formal/GAPMAP.md` — theorem ledger and status;
4. `theorems/*.txt` and `base.txt` — Portuguese prose claims, which must reflect the formal status;
5. `CHARACTERISTICS.md` — inventory of the original arguments and their current formal correspondence;
6. generated `README.md` and `investigations/kernel-audit.md` — corroborating output only, never a source to edit by hand.

The project status vocabulary is:

- `PROVEN`: kernel-checked with no substantive named axioms; vocabulary and `CL` footprints must still be reported honestly;
- `PROVEN↑`: kernel-checked under a disclosed `SEM` or `META` axiom; reader-facing output calls this `AXIOMATIC`, not “proved without premises”;
- `AXIOM`: the claim itself is declared;
- `BLOCKED`: the exact missing lemma or vocabulary bridge is recorded;
- `DEFERRED`: intentionally outside the current milestone;
- `COUNTERMODEL`: the machine witness shows the proposed implication is not entailed.

`T p := p` in `Logos.Core` is a definitional consistency choice, not a general theory of truth. Several apparently strong results are therefore purely logical or vocabulary-level results. Do not describe them as transcendental discoveries without an explicit bridge.

## 2. Current strategic conclusion

The project has a strong formal performative core and has established Canonical Aseity (`conditional_canonical_aseity`, `{Means, Subject}`) and atom exclusion (`atom_cannot_ground_the_ground`), but it does **not** yet have a cheap route to positive divine characteristics such as transcendence, unity of the divine Being (monotheism — since **PROVEN** via C320), simplicity, omniscience, omnipotence, benevolence, or ordinary personhood. The person-*count* of that one God (numerical unitarianism) is a separate question, left **open** rather than settled either way.

The easiest remaining work is therefore mostly one of the following:

1. close a small logical bundle of already-proved results;
2. formalize a countermodel or non-entailment that prevents an overclaim;
3. make a new semantic or metaphysical bridge explicit and price its footprint;
4. leave a characteristic deferred until its vocabulary is actually defined.

The completed small batch is:

1. **C182**: prove that generic `Aseity` does not entail the existence of a `Level3_VolitionAlternative` (`Unit`/`False` countermodel);
2. **C184**: prove that a volitional alternative does not entail `Aseity` (`ExtDepAt := True` countermodel); together these give two-way logical independence at the generic frontier;
3. **C183**: bundle the already-proved `greatResult` and `noBothTrueAndFalse` (`Core.lean`);
4. audit, synchronize prose and ledgers, regenerate outputs, and run the full `make` pipeline;
5. only then choose a bridge for a genuinely positive characteristic.

The next work is no longer to re-prove these three generic boundary results. It is to decide whether their logical separation is philosophically useful and, if so, propose an explicit, priced bridge for one positive characteristic.

## 3. Immediate proof queue

### 3.1 C182 — Aseity does not force volitional alternatives

**Current status:** ✅ **PROVEN** in `formal/Logos/ModalPossibilityFrontier.lean:463`; audited footprint `{}` at the `#print axioms` line `:626`.

**Target location:** implemented at `formal/Logos/ModalPossibilityFrontier.lean:463-483`, near the `Aseity` and `Level3_VolitionAlternative` definitions.

**Target statement:**

```lean
theorem aseity_does_not_force_any_volition_alternatives :
    ∃ (World Entity Subject : Type)
      (ExtDepAt : World → Entity → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (g : Entity),
      Aseity World Entity ExtDepAt g ∧
        ¬ ∃ (s : Subject) (a : Prop) (v u : World),
          Level3_VolitionAlternative World Subject WillsAt s a v u
```

**Proof model:** use `Unit` for all three sorts, `fun _ _ => False` for external dependence, and `fun _ _ _ => False` for will. Aseity then reduces to a tautology, while any alleged volitional alternative begins with a false premise.

**Audited footprint:** `{}`. The model uses no substantive axioms; this is now an audited result, not an expectation.

**What it proves:** generic predicate separation only. It does not prove that `Entity.ofGround` is aseitous, does not define causal dependence, and does not establish a divine metaphysics.

**Status after the batch:** ✅ C182 is a generic countermodel with `Unit`/`False`; C184 is the complementary model with `Bool`/`True`. The pair is machine-checked with `{}` footprints. Together they show two-way non-entailment, not aseity of `Entity.ofGround`.

### 3.2 C184 — Volitional alternatives do not imply aseity

**Current status:** ✅ **PROVEN** in `formal/Logos/ModalPossibilityFrontier.lean:485`; audited footprint `{}` at the `#print axioms` line `:627`. The companion received ledger ID C184.

**Target statement shape:**

```lean
theorem volitional_alternative_does_not_force_aseity :
    ∃ (World Entity Subject : Type)
      (ExtDepAt : World → Entity → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (g : Entity) (s : Subject) (a : Prop) (v u : World),
      Level3_VolitionAlternative World Subject WillsAt s a v u ∧
        ¬ Aseity World Entity ExtDepAt g
```

**Proof model:** `World := Bool`, `Entity := Subject := Unit`, `ExtDepAt := fun _ _ => True`, and `WillsAt := fun w _ _ => w = true`. Use worlds `true` and `false`. The will relation supplies the first conjunct and `Aseity` is refuted by applying it to `true`.

**Audited footprint:** `{}`. The model uses `World := Bool`, `Entity := Subject := Unit`, `ExtDepAt := fun _ _ => True`, and `WillsAt := fun w _ _ => w = true`.

**Logical consequence:** C182 plus C184 establishes both non-entailments:

- `Aseity ↛ ∃ Level3_VolitionAlternative`;
- `∃ Level3_VolitionAlternative ↛ Aseity`.

This is a frontier theorem about independently chosen generic predicates, not a claim about the canonical foundation. C182 and C184 are now assigned and audited as C182 and C184 respectively.

### 3.3 C183 — Nonempty and nonconflating truth/falsity bundle

**Current status:** ✅ **PROVEN** in `formal/Logos/Core.lean:170`; audited footprint `{}` at the `#print axioms` line `:209`.

**Target location:** implemented at `formal/Logos/Core.lean:170-176`, immediately after `greatResult` and `noBothTrueAndFalse`.

**Target statement:**

```lean
theorem rightWrong_nonempty_and_nonconflating :
    (∃ p q : Prop, T p ∧ IsFalse q) ∧
      ∀ p : Prop, ¬ (T p ∧ IsFalse p)
```

**Proof:**

```lean
exact ⟨greatResult, noBothTrueAndFalse⟩
```

**Audited footprint:** `{}`. The declaration is a mechanical bundle of the already-proved C8 and C9 results.

**Value:** mechanically safe and useful as a closure of the Level-0 logical spine. It bundles C8 and C9 only. Because `T p := p`, it is not a new truth theorem, not a new transcendence argument, and not a divine characteristic.

**Decision:** C183 has been implemented because the goal was to close the queued logical batch. It is a bookkeeping closure, not a substantive philosophical advance.

## 4. Characteristic-by-characteristic status and next action

### 1. Transcendence and externality

- **Prose source:** `CHARACTERISTICS.md:21-55`; original argument is strong prose but formally absent.
- **Live nearest results:** `NecessityEternity.ofGround_ground_of_reality` (`formal/Logos/NecessityEternity.lean:140-142`) is thin definitional grounding; `PersonalGroundOfReality.the_person_supports_the_reality_of_right` is grounding the reality of Right/Wrong, not externality to every system.
- **Ledger status:** ultimate-ground and quantifier-swap routes C78/C79/C88 are blocked or retired (`formal/GAPMAP.md:440-444`).
- **Easy next proof:** none from current vocabulary. A generic countermodel could show that “grounds every actual entity” does not imply “external to every formal/evaluative system,” but this requires first defining the two notions separately.
- **Required design decision:** define whether externality is logical, ontological, causal, or hierarchical. Do not encode all four under one name.
- **Stop condition:** until that definition and a bridge are approved, keep the characteristic `❌ absent`.

### 2. Aseity

- **Current source:** `ModalPossibilityFrontier.lean:122-124` and `CanonicalAseity.lean`.
- **Current distinction:** generic `Aseity` exists; C182/C184 provide two-way independence with volitional alternatives (`{}`); canonical external grounding `ExternalGrounding` and `CanonicalAseity` are formalized in `Logos.CanonicalAseity`.
- **Current result:** C185 (`{}`) establishes generic meaning exclusion; C186 (`{Means, Subject}`) proves `CanonicalAseity Entity.ofGround` conditional on discriminating subjects (`∀ s, ∃ p, ¬ Means s p`); unconditional atom exclusion is proven (`atom_cannot_ground_the_ground`, `{Means, Subject}`); and `unconditional_aseity_independent_of_bare_agency` (`{}`) isolates the exact independence boundary showing that unconstrained `Means` does not entail unconditional aseity without a finite-subjectivity premise.
- **Do not claim:** that unconditional aseity is proved for the ultimate foundation without the discriminating-subject premise, or that the current formalization establishes uncausedness in an efficient-causal sense.

### 3. Necessity and non-contingency

- **Live result:** `ofGround_necessary` and `ofGround_necessary_ground_of_reality` are definitional consequences of the world-rigid `Entity.ofGround` constructor.
- **Additional separation:** `PersonhoodOntologyAudit.faithful_contingent_person_fails_necessary_subject` (`formal/Logos/PersonhoodOntologyAudit.lean:216-227`) refutes the unqualified implication from personhood to necessary personhood.
- **Next work:** no new positive theorem is cheap. C181 is already the generic stage-uniformity transport (`NecessityEternity.lean:101-121`); do not add a duplicate canonical corollary merely to increase the theorem count.
- **Boundary:** performative necessity in the prose is not automatically the same thing as modal `NecessaryEntity` or `NecessarySubject`.

### 4. Normative sovereignty and authority

- **Live result:** C179, `DirectNormativeRetorsion.no_correct_claim_of_no_right_can_be_true`, is a local interpreted-signature result with footprint `{}`. The broader personal-ground and reality-hook results are conditional or vocabulary-priced.
- **Ledger:** C102–C105 remain the direct retorsion route; the canonical attribution to the ultimate foundation is not automatic.
- **Easy next proof:** none that establishes divine sovereignty. A local theorem can only show that a particular normative denial cannot be both correctly claimed and true.
- **Missing bridge:** a justified connection from the local retorsion/judicative structure to the canonical `Entity.ofGround` or an explicit foundational subject.
- **Do not claim:** C179 alone proves that the foundation is sovereign, authoritative, or God.

### 5. Freedom, personality, and minimal subjecthood

- **Live positive results:** the conditional route through `GenuineNormativity` and `Chooses → FreeWill`; `Person.free_subject_is_person`; A14 route `Choice.freeWill_exists` is `PROVEN↑` under `AxIntentionalChoice`.
- **Completed live layer (2026-09-26, batch ASIETIC-CHOICE):** ✅ **`formal/Logos/AsieticChoice.lean`** (C259–C286 + F11, GAPMAP level 18; `theorems/T28.txt`; `base.txt` §30) closes the weak-choice → strong-choice step and adds true choice, **with zero new axioms** — the register is unmoved at 25 declared (VOCAB 14 / SEM 7 / META 4), and that immobility is the test.
  1. `weakChoice_implies_chooses : ChoiceField s p q → ClaimsCorrect s p → Chooses s p (¬ p)` (C266, `PROVEN↑`, `{AxJudicativeBipolarity, Initiates, Means, State, Subject}`) — **the `?` of `base.txt:460`, discharged with its premise written**. C267 is the pair-level form; C269 makes the price of the premise explicit rather than a claim about the world.
  2. Existence, unconditional, both ways: `trueChoice_exists` / `freeWill_exists` / `an_asietic_entity_exists` (C277–C279, `PROVEN↑`, `{AxTwoSubjects, Means, Subject, Will, subjectWill}` — **not** `{}`); and the thesis itself, vocabulary-only, `asietic_is_true_freedom` (C280).
  3. The performative route, at pinned content: `retorsion_yields_genuine_normativity_on_its_own_content` (C270) and `retorsion_implies_rejectedHornCoMeant` (C271), both `PROVEN↑` under the premise `∃ s, ClaimsCorrect s NoGN`. C270 answers residue (b) of F1b at `GAPMAP.md:758`.
- **The `Choice` blocker is now *named and refuted*, not merely open.** `Choice.rejectedHornCoMeant` (`formal/Logos/Choice.lean:231-246`) is the **consequent only**. The blocked *implication* is `AsieticChoice.bareRejectedHornCoMeant` (F11), and `singleContentModelRefutesBareRejectedHorn` (C273) / `bareRejectedHornCoMeant_is_not_derivable` (C274), both `{}`, exhibit a faithful single-content model in which the antecedent holds and the consequent does not.
- **Existing countermodel:** the veridical-meaning model shows that the performative datum, plurality, and Right/Wrong do not force a subject to co-mean both horns. The single-content model above is the sharper version: the horn does not follow even from a meaning-act *alone*, and the load-bearing field is **faithfulness** (`means s p → p`), not single-valuedness — from `p = ¬ p` no contradiction follows, since `p` need not be provable.
- **Disclosed weakness (do not upgrade):** `strongChoice_iff_trueChoice : Chooses ↔ TrueChoice` (C265, `PROVEN`) — "true choice" adds **no** force over strong choice, because `ContestedContent` is a *global* frame fact, not a per-pair modality. Accepted as D6 and disclosed in the module docstring, the Level 18 note, `base.txt` §30, and T28. It must not be quietly turned into a per-pair modality.
- **Next work:** object/action deliberation is still unanswered — it needs the separate `DeliberateChoice` / `ClaimsNormativeCorrectness` route (C140/C141). Do not prove F1b by weakening the target or silently declaring the rejected-horn datum — the batch shows that would be *false*, not merely unproved.
  - **⚠️ CORRECTED 2026-09-28 (batch INHABITED + batch ACT-CASCADE).** This bullet used to name "the single upstream gap is the **`Initiates`-existence gap** (`∃ s p, Act s p`)". **That gap is closed.** `performative_act_datum` (C454, `Tag: TRANS`) is unconditional, and C455 `some_subject_initiates` inhabits `Initiates` outright; `not_noAct` (C456) refutes the denial. The `Act`-gating is therefore **no longer an existence gap** — it is a *disclosed price*. What remains open is different and narrower: the **`Asserts`** lane, which is closed *by construction* and not by neglect. `Asserts s p := Act s p ∧ p`, so C454 yields no existential of `Asserts` — there is no proposition available that is both `Act`-bearing and true. `Choice.act_implies_asserts_bridge` (`Choice.lean:652`) is still unpriced, and **twelve theorems remain conditional** by that construction. The horn-saturation part of the old claim stands: all four of Γ's routes to `Means s (¬ p)` are still `Act`-gated and `Doubts` is still circular.
- **Completed live layer (2026-09-28, batch ACT-CASCADE, C469–C480):** ✅ **`formal/Logos/ActCascade.lean`** turns the act-datum's consequences into **twelve unconditional corollaries**, with **zero new axioms** (register unmoved at 31 = VOCAB 17 / SEM 6 / META 7 / TRANS 1).
  1. **The problem.** Eighteen theorems across five modules carried `performative_act_datum` as their *sole* hypothesis. A hypothesis that is itself a declared axiom of Γ is not a hypothesis — it is a leftover from before the datum was admitted. Each of the eighteen is a one-line corollary of a parent that already exists.
  2. **Eighteen → twelve distinct conclusions.** `act_datum_implies_initiates` is already unconditional in form (it *is* C455); `subject_exists_of_act` = `T1_subjectExists_of_act` = `T1_subjectExists`; `intentionalSubject_exists_of_act` = `T5_intentionalSubjectExists`; `freeWill_exists_of_act` = `freeWill_exists`; `freeSubject_exists_of_act` = `freeSubject_exists`; a duplicated corollary is not a second result.
  3. **Not free, and now visibly so.** Every row **pays `performative_act_datum` in its footprint**, and the five free-will / genuine-choice / free-subject rows still pay `AxIntentionalChoice` or `AxActPolarity` on top. The price was hidden in a binder; it is now mandatory on the row. Disclosure, not strengthening: Γ gained a theorem about one more thing, not one more premise.
  4. **Two rows say nothing beyond a definitional fold, and say so.** C471 is **definitionally C470** (`AnActualSubjectExists := ∃ s, SubjectExists s`). C473/C474/C479 are the same predication under the corpus's other names (`IntentionalSubject s := ∃ p, Means s p`; `Intentional := IntentionalSubject`; `FreeSubject := FreeWill`). They exist because the corpus enuncates them in those forms, not to add results.
  5. **C472 must not be read as agency.** `Agent (_s : Subject) := True`, so `an_agent_exists` is **exactly as strong as C470 and nothing more** (C321's precedent: a property of everything characterises nothing). It discharges the `T4_agentExists` step of the T chain; it is not evidence of agency in any sense the word carries outside that `def`.
  6. **⚠️ The plan was wrong about F1b, and the audit said so.** The plan asserted F1b's footprint cell was stale "by the same reason as C455". It is **not** stale: `Choice.freeWill_exists` — F1b's first named theorem — is **unconditional** with footprint exactly `{AxIntentionalChoice, Initiates, Means, State, Subject}`, which is what the cell already said. There was no hypothesis to discharge. The cell is **unchanged**; what changed is that the cascade now has its **own** rows (C475/C477/C479) carrying that price. Pointing F1b at C477's declaration would have dissolved F1b into an alias (and `F7 → F1b` with it), breaking the generator's pinned 7-alias invariant — an `F` row is canonical by design and must not be pointed at a `C`. See `GAPMAP.md`, "CORRECÇÃO", and `WIN.md` §12.
- **Completed live layer (2026-09-26, batch ASIETY-FREEDOM):** ◈ **`formal/Logos/AsietyFreedom.lean`** (C287–C296, GAPMAP level 19; `theorems/T29.txt`; `base.txt` §31; plan `AsietyFreedom.md`) adds the *Act-free* route into asiety and the ground→freedom transfer, **with zero new `axiom`s** — register unmoved at 25 (VOCAB 14 / SEM 7 / META 4).
  1. **Axiom-free, Act-free, conditional on GenuineNormativity (Rule R clause 4):** `weakChoice_implies_asiety : GenuineNormativity s p q → Asiety (EntityOf s)` (C287) and `weakChoice_implies_freeWill` (C288), both `PROVEN`, `{Means, Subject}` — **no `Act`, no `Initiates`, no `ClaimsCorrect`, no stipulation**. Disclosed: `indubitable_normative_free_will` is a **sub-formula extraction** (it discards `p ≠ q`), so this is very near a projection, and saying so is part of the row.
  2. **The bridge is a priced ◈ META `def`,** not an axiom: `AsietyFreedomOfGround` ("the ground's freedom reaches every subject") and its transfers `asietyFreedom_yields_trueChoice` / `…_yields_asietyFreeWill` / `asietyFreeWill_yields_trueChoice` (C289–C291) and `asietyFreedom_summary` (C296), all `PROVEN` **given** the declaration, all `{Means, Subject}`. R1 checked: `TrueChoice` is **not** a conjunct of `AsietyFreeWill`, so these are not self-projections.
  3. **Priced by three `{}` countermodels:** C292 (asiety alone yields no true choice — the universal reading is strictly stronger than the existential one), C293 (frame contingency binds no pair — pins D6), C294 (**no axiom-free existence of a chooser**). C295 keeps C285: the ground is **not** a chooser.
- **⚠ The disclosed weakness that outranks the others here: the axiom-count invariant is NOT a test for this batch.** `AsietyFreedomOfGround` is a `def`, so `#print axioms` cannot see it, and `{Means, Subject}` would be reported *whether the bridge is principled or arbitrary*. Unlike ASIETIC-CHOICE, "the count did not move" proves nothing here; the ◈ registry entry and the README step-by-step block are the only places the price is visible, and they are load-bearing. Additionally the `GroundsEntity` premise of the three transfers is **vacuous** (the ground grounds even meaningless entities), so the metaphysical weight sits entirely on the declaration.
- **Next work:** the substantive grounding relation **behind** the stipulation (C228, `BLOCKED`) — not another transfer, which would only multiply a price already paid. Also still open: the `Initiates`-existence gap (see above), unaffected by this batch.
- **Do not claim:** that minimal structural subjecthood is ordinary consciousness, psychological personality, or necessary divine personhood; that true choice is stronger than strong choice; that the ground is an asietic entity (`ground_is_canonically_aseitous_but_not_asietic`, C284; `ground_is_not_a_true_chooser`, C285); that **existence** of a chooser sharing the ground's freedom is axiom-free (C294 refutes it — the Creator step is *conditional*); that the universal reading of the bridge is the correct one; or that this batch's axiom-count immobility is evidence of anything (see the ⚠ bullet).

### 6. Unity and oneness

- **Completed live layer:** ✅ **PROVEN** in `formal/Logos/FoundationalUnicity.lean` (C207–C213; audited footprints `{}` and `{CL, Means, Subject}`).
- **Results:**
  1. Master Metaphysical Unicity: `universal_ground_unicity` (C207, `{CL, Means, Subject}`) — two distinct entities cannot both be universal modal grounds under asymmetric grounding;
  2. Concrete Atom Exclusion: `no_atom_is_universal_modal_ground` (C208, `{Means, Subject}`) — no atomic factual state can ground all reality;
  3. Discriminating Subject Exclusion: `no_discriminating_subject_is_universal_modal_ground` (C209, `{Means, Subject}`) — no finite subject can ground all reality;
  4. Sole Universal Ground: `ofGround_sole_universal_ground` (C210, `{Means, Subject}`) — `Entity.ofGround` is the unique universal ground candidate in Γ;
  5. The Master Synthesis: `ofGround_foundational_unicity` (C211, `{CL, Means, Subject}`, 0 substantive axioms);
  6. Metatheoretic Independence: `unicity_does_not_force_unitarian_monad` (C212, `{}`) — foundational unicity of universal grounding does not force a solitary, relationless monad, keeping the Trinitarian frontier open;
  7. Ontological Transcendence: `unicity_strictly_transcends_world` (C213, `{Subject}`) — strictly excludes pantheistic conflation with the world.
- **Honest boundary:** establishes foundational unicity of universal grounding in reality (Aquinas *ST* I, q. 11, a. 3); strictly separated from numerical unitarianism (the person-count of that one ground, separated as `🧱 INDEPENDENT` via C212 — *not entailed by unicity, not refuted by it*) and theological identification (One God ✅ **PROVEN** via C301/C302).
- **Existing separation:** `TheologicalModalHardening.necessary_existence_not_entails_uniqueness` (`formal/Logos/TheologicalModalHardening.lean:405-414`) has footprint `{}` and supplies a two-ground countermodel for bare necessity.
- **Do not conflate:** foundational unicity (one universal ground of all reality — this *is* monotheism, one God, ✅ PROVEN) with numerical unitarianism (how many Persons that one God bears — a distinct question that unicity leaves **open**, 🧱 INDEPENDENT via C212, neither entailed nor refuted) or pantheism (which collapses the ground into the world). The positive plural reading is the declared META axiom `AxAgapeEssence` (C504), not C212.

### 7. Simplicity and non-compositeness

- **Current status:** ✅ **PROVEN** in `formal/Logos/DivineSimplicity.lean` (C192–C196; audited footprints `{}` and `{Means, Subject, propext}`), with the last conditional form discharged in `formal/Logos/CharacteristicClosure.lean` (C484–C486, C491–C492).
- **Results:**
  1. `ProperPart p e := p ≠ e ∧ GroundsEntity p e`, `NonComposite e := ¬ ∃ p, ProperPart p e`, proving `non_composite_iff_canonical_aseity` and `ofGround_non_composite` (`{Means, Subject, propext}`);
  2. Structural Inextension: `ofGround_has_no_internal_components` (C193, `{Subject}`);
  3. Intentional Simplicity: `ofGround_undivided_meaning` (C194, `{Means, Subject}`) and `discriminating_subject_not_undivided`;
  4. Ontological Transcendence: `ofGround_transcendent` (C195, `{Subject}`);
  5. The Master Synthesis: `ofGround_divine_simplicity` (C196, `{Means, Subject, propext}`, 0 substantive axioms);
  6. Metatheoretic Independence: `composite_entity_fails_simplicity` (C192, `{}`);
  7. Unconditional Simplicity: `the_ground_is_divinely_simple` (C484), `some_entity_is_divinely_simple` (C485), and `the_ground_is_sole_bearer_of_divine_simplicity` (C486), all vocabulary-only with declared F15;
  8. Thomistic Principle: `transcendence_and_semantic_finitude_yield_divine_simplicity` (C491) for every transcendent entity, given F15;
  9. Bound Independence: `the_semantic_bound_does_not_close_the_grounding_arm` (C492, `{}`), separating `Means`-side and `GroundsEntity`-side finitude.
- **Honest boundary:** this establishes mereological, structural, and intentional simplicity of `Entity.ofGround` — it does not establish identity of essence and existence or exhaustive formal simplicity. Scholastic simplicity (essence-existence identity) is explicitly separated in the attributes table as `❌ NOT ESTABLISHED`.

### 8. Eternity, timelessness, and ontological precedence

- **Completed live layer:** C181 and canonical corollaries in `NecessityEternity.lean:101-188`: stage uniformity, everlasting, atemporal, and non-succession results. **Leitura exacta (2026-09-28, lote SUCCESSION C458–C462):** a não-sucessão é *não-correlatividade*, não *não-iniciação* — `the_ground_not_in_succession` descarta o conjugado `Initiates`; C459 mostra que o mesmo predicado vale para todo o átomo, e C460 a sua não-trivialidade.
- **Divine Immutability completed:** ✅ **PROVEN** in `formal/Logos/DivineImmutability.lean` (C197–C201; footprints `{}` and `{Initiates, Means, State, Subject}`), with the transition-field refuter and sole-bearer separation in `formal/Logos/CharacteristicClosure.lean` and `formal/Logos/ImmutabilitySoleBearer.lean` (C487–C490, F17). Results:
  1. `ModalInvariance` (`ofGround_modal_invariance`, C198, `{Subject}`);
  2. `StageInvariance` (`ofGround_stage_invariance`, C199, `{Subject}`);
  3. `TransitionInvariance` (`ofGround_transition_invariance`, C200, `{Initiates, State, Subject}`);
  4. `CapacityInvariance` (`ofGround_capacity_invariance`, `{Means, Subject}`);
  5. The Master Synthesis: `ofGround_divine_immutability` (C201, `{Initiates, Means, State, Subject}`, 0 substantive axioms);
  6. The Thomistic Principle: `necessity_and_atemporality_yield_immutability` (ST I q. 9 a. 1–2);
  7. Metatheoretic Independence: `contingent_entity_fails_immutability` (C197, `{}`);
  8. Transition Non-Vacuity: `some_entity_is_in_succession` (C487, `PROVEN↑`) and `a_subject_that_acts_is_in_succession` (C488, vocabulary-only);
  9. Sole-Bearer Separation: `immutability_is_not_sole_bearer` (C489, `{}`) and `the_act_datum_does_not_entail_every_subject_acts` (C490, `{}`), with frontier F17 naming the unavailable per-necessary-kind-subject universal.
- **Honest boundary:** establishes modal, temporal, process, and capacity unchangeability in Γ; it no longer claims unique immutability. It does not claim psychological impassibility or constrain relational intentionality. Psychological impassibility is explicitly separated in the attributes table as `❌ NOT ESTABLISHED`.

### 9. Precedence to the true/false distinction

- **Current status:** no live precedence theorem (`CHARACTERISTICS.md:264-288`); only truth/falsity distinction and personal grounding results exist.
- **Next work:** define `Precedes` at the intended level. Logical precedence, ontological grounding, temporal precedence, and causal priority are different predicates.
- **Safe exploratory step:** a generic model separating “ground of the distinction” from “priority before the distinction” can be built only after those predicates are declared.
- **Do not claim:** that `ofGround_ground_of_reality` automatically means the ground precedes truth/falsity.

### 10. Non-conditioned and non-relative character

- **Completed architectural result:** C180, `HardenedInvariance.agent_invariant_core_is_strictly_inside_freewill_invariant_core` (`formal/Logos/HardenedInvariance.lean:223-237`), footprint `{}`.
- **Boundary:** it compares dependency-layer cores; it is not metaphysical non-relativity across systems, perspectives, or worlds.
- **Next work:** if desired, a generic countermodel can show that architectural invariance does not imply a canonical `Absolute`/`Unconditioned` predicate. Do not rename C180 as divine non-relativity.

### 11. Universality and infinity

- **Completed live layer:** ✅ **PROVEN** in `formal/Logos/FoundationalOmnipresence.lean` (C202–C206; footprints `{}` and `{Means, Subject}`). Results:
  1. `WorldRigidPresence` (`ofGround_world_rigid_presence`, C203, `{Subject}`);
  2. `UniversalModalGround` (`ofGround_universal_modal_ground`, C204, `{Means, Subject}`): grounds every entity in every possible world;
  3. `NonReciprocalGround` (`ofGround_non_reciprocal_ground`, C205, `{Means, Subject}`): asymmetric grounding, ungrounded by atoms or finite subjects;
  4. `MaximalCapacity` (`ofGround_maximal_capacity`, `{Means, Subject}`);
  5. The Master Synthesis: `ofGround_foundational_omnipresence` (C206, `{Means, Subject}`, 0 substantive axioms);
  6. The Thomistic Principle: `omnipresence_from_universal_ground_and_aseity` (ST I q. 8 a. 1–3);
  7. Metatheoretic Independence: `finite_entity_fails_omnipresence` (C202, `{}`).
- **Honest boundary:** establishes foundational sustaining presence across modal reality in Γ; explicitly distinguishes foundational omnipresence from physical spatial omnipresence or quantitative metric infinity (both of which are explicitly separated in the attributes table as `❌ NOT ESTABLISHED`).
- **Do not claim:** omniscience or omnipotence from universality; `CHARACTERISTICS.md` explicitly disclaims that inference.

### 12. Pure actuality

- **Completed live layer:** ✅ **PROVEN** in `formal/Logos/DivinePureActuality.lean` (C214–C220; footprints `{}` and `{Initiates, Means, State, Subject}`). Results:
  1. Absence of Passive Existential Potency (`ofGround_no_existential_potency`, C215, `{Subject}`): necessary existence across all possible worlds;
  2. Absence of Passive Grounding Potency (`ofGround_no_grounding_potency`, C216, `{Means, Subject}`): ungrounded by any external entity under finite subjectivity;
  3. Absence of Passive Transition Potency (`ofGround_no_transition_potency`, C217, `{Initiates, State, Subject}`): immune to temporal becoming and agential succession — **com a leitura de 2026-09-28**: isto herda a não-correlatividade de C458, é disjunção de construtores, e não é um resultado sobre iniciativa (C462 `BLOCKED`);
  4. Absence of Passive Intentional Potency (`ofGround_no_intentional_potency`, C218, `{Means, Subject}`): exhaustive propositional meaning capacity;
  5. The Master Synthesis: `ofGround_divine_pure_actuality` (C219, `{Initiates, Means, State, Subject}`, 0 substantive axioms);
  6. Divine Incorporeality and Immateriality: `ofGround_incorporeal` (C220, `{Subject}`, Aquinas ST I q. 3 a. 1–2: *Deus non est corpus*);
  7. The Thomistic Principle: `necessity_aseity_and_immutability_yield_pure_actuality` (ST I q. 3 a. 1–2, q. 4 a. 1);
  8. Metatheoretic Independence: `entity_with_potency_fails_pure_actuality` (C214, `{}`).
- **Honest boundary:** establishes metaphysical Pure Actuality (*Actus Purus* in Γ: zero passive potentiality and universal modal grounding); strictly distinguished from physical kinetic motion or thermodynamic energy (separated as `❌ NOT ESTABLISHED` in the attributes table).

### 13. Sovereignty over value and goodness

- **Separation already machine-checked:** `MoralFrontierAudit.epistemic_normativity_without_practical_obligation` (`formal/Logos/MoralFrontierAudit.lean:173-183`) has footprint `{}`.
- **Positive moral layer:** `Good` is a fair relational definition; `moral_good_obtains` is `PROVEN↑` under the disclosed `AxBenevolentBearingObtains` META bridge (`MoralFrontierAudit.lean:189-214`).
- **Next work:** the remaining gap is divine attribution and the negative `Evil` pole, not a new proof that logical normativity entails moral value.
- **Do not claim:** that a moral-good inhabitant is necessarily the ultimate foundation.

### 14. Omniscience

- **Completed live layer:** `formal/Logos/DivineOmniscience.lean` proves the *weak foundational* sense for `Entity.ofGround` (C233–C240, vocabulary-only, 0 substantive axioms): truth-exhaustive scope (`ofGround_truth_exhaustive`, `{Means, Subject}`), the same world-indexed (`ofGround_world_truth_exhaustive`, `{Means, Subject}`), atoms and discriminating subjects excluded (`atom_not_truth_exhaustive`, `discriminating_subject_not_truth_exhaustive`, `{Means, Subject}`), and the master synthesis `ofGround_foundational_omniscience` (`{Means, Subject}`).
- **The strong sense is refuted, not open:** `ofGround_not_truth_tracking` (`{Means, Subject}`) proves `¬ TruthTracking Entity.ofGround` — because the ground's scope reduces to `True`, the exclusive half of "all and only truths" is false of the ground in Γ. The refutation is carried as a *field* of `FoundationalOmniscience`, so the boundary is part of the record.
- **Honest boundary:** the counterfactual sense is independent (`exhaustive_scope_without_counterfactual_knowledge`, `{}`); the scope/infallibility separation is metatheoretic (`entity_scope_exhaustiveness_is_not_infallibility`, `{}`).
- **Do not claim:** ordinary/classical omniscience. Γ has no `Knows` predicate; `KnowsAt` / `KnowsCounterfactualAt` are generic vocabulary definitions and `Entity.ofGround` is not a subject correlate (`ofGround_ne_ofSubject`). Retain the explicit prose disclaimer (`README-OLD.md:263`); do not manufacture a divine knowledge bridge. See `theorems/T26.txt`.

### 15. Omnipotence

- **Completed live layer:** `formal/Logos/DivineOmnipotence.lean` proves the *orthodox non-contradictory* sense for `Entity.ofGround` (C241–C251, 0 substantive axioms): no satisfiable state of affairs is closed to the ground's operative scope (`ofGround_gapless_operative_scope`, `{NecessarySubjectKind, Subject}`), with both faces of the restriction explicit — nothing unobtained is operated (`ofGround_operates_only_what_obtains`, `{NecessarySubjectKind, Subject}`) and no contradiction is ever operated (`ofGround_does_not_operate_contradictions`, `{NecessarySubjectKind, Subject, propext}`) — plus the master synthesis `ofGround_foundational_omnipotence` (`{CL, Means, NecessarySubjectKind, Subject}`) and the *semper* principle `necessity_and_presence_yield_foundational_omnipotence`.
- **Reframed, not overstated (2026-09-26):** the batch's first draft proposed to refute "the strong sense of omnipotence" by naming contradiction-omni as *the* classical sense. That was wrong — Aquinas' sense is power over whatever does not involve a contradiction (*ST* I q. 25 a. 5 ad 1) — so the restriction is **affirmed**, and only the contradiction-omni reading is refuted (C244), by the restriction itself.
- **The price is disclosed:** in this batch Γ had no production relation, so `OperatesAt` reads "operates" as presence plus obtaining, priced as ◈ `operatesAt_presencePlusObtaining` (`Tag: SEM`). The price is machine-checked, not asserted: `existence_everywhere_does_not_entail_operation` (`{}`) — presence everywhere ⇏ operation; `exhaustive_scope_without_operative_scope` (`{}`) — exhaustive scope ⇏ operative scope; `gapless_operative_scope_without_conjunctive_power` (`{}`) — gapless scope ⇏ conjunctive power. The relation (C463) and the universal (C493) have since been declared; the weakened reading and its price stay exactly as stated for the non-contradictory sense.
- **Honest boundary:** causal/creative omnipotence ("can bring X about") was 🔴 **BLOCKED** until 2026-09-29, and is now **declared, not derived** (GAPMAP Level 17, row F10 now `AXIOM`). The two statements both landed, in order: the vocabulary `Produces : Entity → World → Form → Prop` (C463, `Tag: VOCAB`), and the universal `ground_produces_every_satisfiable_form` (C493, `Tag: META`) — every satisfiable form is produced by the ground somewhere. C483 remains the proof the bridge was new content. `Agency.Initiates` is subject-indexed and `Entity.ofGround` is not a subject correlate (`ofGround_ne_ofSubject`); `GroundsEntity` cannot substitute, by C250. Production is still not creation (C110 stands).
- **Do not claim:** that universal production derives creation, or read Foundational Omnipotence as a claim about bringing contingent beings into existence. The causal sense now rests on the named C493 bridge; reject the bridge and the sense goes with it.

### 16. Benevolence and ordinary moral perfection

- **Current status:** `moral_good_obtains` is only `PROVEN↑` under `AxBenevolentBearingObtains`; the divine attribution remains a frontier.
- **Next work:** a new positive claim needs an explicit relation from the canonical foundation to benevolent willing, not merely the existence of a good action.
- **Recommendation:** do not promote a META-priced moral pole to an unconditional divine attribute.

### 17. Founding all reality versus creation

- **Completed thin result:** `ofGround_ground_of_reality` is definitional grounding, not efficient causation.
- **Existing separation:** `ConditionalTheology.necessary_ground_not_entails_contingent_creation` (`formal/Logos/ConditionalTheology.lean:417-424`) is a countermodel.
- **2026-09-27 — the existence half is now a *free theorem*, still not an entailment.** Two rows, split: `CosmicExistence.contingent_realm_obtains : ContingentRealmObtains` (**C350**) derives the realm's **existence** inside Γ with footprint `{CL, NecessarySubjectKind, Subject}` — no bridge at all — from `LovesAsGround.an_atom_is_contingent 0`; and `CosmicExistence.cosmos_obtains : CreatedRealm` (**C367**) derives its **meaning** from an exhibited contingent person — footprint `{CL, Means, NecessarySubjectKind, Subject, Will, subjectWill}`, no bridge since the two-kinds correction. Rejecting the person-datum therefore no longer removes the cosmos's existence: it removes only its being a bearer of content. The old `PROVEN↑` Cosmos-existence row (C350, `cosmos_obtains`) was the 2026-09-27 intermediate state, superseded the same day (lot COSMOS-EXISTENCE-IS-FREE); an earlier draft of this line readoSubjects}` (GAPMAP Level 21, C350 `PROVEN↑`; `theorems/T30.txt`; `base.txt` §35; `CHARACTERISTICS.md` §6c). `[Earlier today this row said the cosmos was a declared `Tag: SEM` datum; that was wrong and has been retired — see batch COSMOS-IS-PROVEN.]` Conditional satisfiability is machine-checked relative to a `Means` inhabitant (C354); the contingency shape is non-trivial (C353, `{}`). What F9's existence half does **not** become: an entailment from the necessary ground (the C110 separation stands), a purpose claim, or an incarnation claim. It also does not become axiom-free — an ontological claim now rests on declared vocabulary (an exhibited witness).
- **Next work:** creation ex nihilo *as entailment* still requires a creator/creation relation, temporal beginning or contingency semantics — all still BLOCKED. The bridge from necessary ground to *production* now exists (C493, declared); what is still missing is any bridge from production to *creation*. Purpose remains deliberately unformalized.
- **Do not claim:** that grounding validity creates entities, or that the realm's existence derives *from the ground*. **(Re-split 2026-09-27: an earlier version of this line said it "derives from plurality" — that was the pre-split reading and is now false for existence.)** Existence (C350) derives from a **bare atom witness** (`LovesAsGround.an_atom_is_contingent 0`), with no bridge and no plurality. Plurality (`AxTwoSubjects`) pays only for the *meaning* (C367).

### 18. Pantheism as the excluded alternative

- **Current status: re-dated 2026-09-27.** The original note ("no formal universe-composition or contingency theorem") was written when the cosmos had no ledger row at all. It now has one: `cosmos_obtains` (C350) **proves** the contingent realm's existence (was a `Tag: SEM` datum until 2026-09-27; retired), and the creation/countermodels batch added C351–C366 on top of it. **This still does not establish the pantheism exclusion**, and the boundary is unchanged in kind — but the reason is now precise rather than absent.
- **What exists:** C350 (the realm exists — **derived**, `PROVEN` at `{CL, NecessarySubjectKind, Subject}`, free) and C367 (it bears content — `PROVEN` given an exhibited contingent person, no bridge), C355 (`necessary_entity_rules_out_empty_world` — an absolutely empty world is refuted once a necessary entity exists), and C366 (`g4_creation_is_contingent` — where creation holds, the creature is modal-fragile). The rebuilt C110 adds a **populated** separation: a necessary ground grounding every content need not produce a creation record.
- **What is still missing:** a `Universe = Ground` identity predicate, a definition of the universe as an object, and a derivation that does not route through the plurality bridge (C350 now supplies existence *and needs no bridge*, but not from the ground either — it is inhabited by an atom, so C324's prohibition on reading the atom as the cosmos still stands, and C367 is what identifies the realm). `ofGround_ne_ofSubject` still separates the ground from *subject correlates* only, never from the universe as a whole.
- **Recommendation:** keep this as a documented boundary, not a derived rejection. The re-dating sharpens it twice over — the project can now say the contingent realm exists as a **free** *theorem* (`PROVEN`, `{propext, Subject}`, not routed through any bridge at all), which it cannot yet say the universe is *not* the ground.

### 19. Trinity, incarnation, and biblical personal relations

- **Existing separations:** `preceding_theory_not_entails_trinity` and `preceding_theory_not_entains_incarnation` (`formal/Logos/ConditionalTheology.lean:336-355`, `:376-396`) are countermodel/independence results, not positive theology.
- **Ledger:** F6/F8 remain deferred.
- **Next work:** no cheap proof; a positive result would require explicit Trinitarian/incarnational structures and substantive premises.
- **Do not infer:** Trinity or incarnation from generic plurality, personhood, or necessary existence.

## 5. Existing negative results that should be reused, not re-proved

The following already provide useful boundaries for future work:

- `TheologicalModalHardening.necessary_existence_not_entails_uniqueness` — necessary existence does not imply one ground;
- `PersonhoodOntologyAudit.faithful_contingent_person_fails_necessary_subject` — personhood does not imply necessary personhood;
- `MoralFrontierAudit.epistemic_normativity_without_practical_obligation` — epistemic normativity does not imply practical obligation;
- `MoralFrontierAudit.moral_pole_postulate_is_not_a_consequence` — the moral poles are not forced by the relying structure;
- `ConditionalTheology.necessary_ground_not_entails_contingent_creation` — necessary grounding does not imply creation;
- `ConditionalTheology.preceding_theory_not_entails_trinity` and `preceding_theory_not_entails_incarnation` — the preceding theory does not entail those structures;
- `HardenedInvariance.agent_invariant_core_is_strictly_inside_freewill_invariant_core` — architectural invariance is not metaphysical non-relativity;
- `ModalPossibilityFrontier.model_MC21_consistent` — aseity and a selected volitional alternative can coexist.

These are not “failed attempts.” They are the current reason a positive theorem is blocked and should be cited in every new roadmap entry.

## 6. Recommended milestone sequence

### Milestone A — close the current generic frontier (completed 2026-09-25)

The batch is complete:

1. C182, the `Aseity`/`Level3_VolitionAlternative` separation;
2. C184, the companion non-entailment model;
3. C183, the truth/falsity bundle.

Each declaration has an English docstring, a nearby proof, a `#print axioms`
audit line, and the actual footprint `{}`. The synchronized records are in
`formal/GAPMAP.md`, `base.txt`, `theorems/T3.txt`, `theorems/T19.txt`, and
`CHARACTERISTICS.md`.

The result is deliberately narrow: C182/C184 are generic countermodels, while
C183 is nearly definitional. None is evidence for a positive divine
characteristic. The next milestone is bridge selection, not more packaging.

### Milestone B — decide whether the separation is philosophically useful

`CHARACTERISTICS.md` now states the two-way independence explicitly. If the
separation is useful, propose one explicit bridge; otherwise retain it as a
formal frontier theorem and move on. Do not manufacture a positive bridge
merely to make the table look complete.

### Milestone C — propose bridges one at a time

For any positive characteristic, write a short bridge proposal before adding Lean code. It must identify:

- the old predicate and the new predicate;
- the exact proposed implication;
- whether it is `VOCAB`, `SEM`, or `META`;
- a consistency model for its negation;
- the resulting theorem footprint;
- which prose claims would be strengthened or withdrawn.

Priority for bridge proposals, if the project wants the most philosophically load-bearing results:

1. canonical aseity/externality;
2. unconditional free will (`rejectedHornCoMeant`);
3. divine uniqueness;
4. moral or value attribution to the foundation.

Do not implement a bridge merely because it is easy to state. A transparent axiom is preferable to a hidden `sorry` or an overstated theorem.

### Milestone D — absent-vocabulary research

Only after Milestone C should the project add predicates for simplicity, pure actuality, infinity, omniscience, omnipotence, or logical precedence. Each new predicate needs:

1. a formal definition;
2. a neutral consistency model;
3. a non-entailment test against the existing theory;
4. an English gloss;
5. a ledger classification and exact footprint.

This prevents the vocabulary from being designed backwards from a desired theological conclusion.

## 7. Definition of done for any future characteristic theorem

A candidate is complete only when all applicable items are done:

- [x] Lean declaration exists in the correct module and namespace.
- [x] The statement matches the prose claim exactly; no stronger adjective is smuggled in.
- [x] The theorem has an English docstring explaining both the result and its boundary.
- [x] `#print axioms` is present and the actual footprint is audited.
- [x] `formal/GAPMAP.md` receives the correct ID, status, theorem name, and footprint.
- [x] `formal/axiom_audit.json` is regenerated, never hand-edited.
- [x] The matching `theorems/T*.txt` is created or updated, with the exact Lean dependency and axiom footprint.
- [x] `base.txt` is patched in Portuguese, including any “still requires proof” or countermodel note.
- [x] `CHARACTERISTICS.md` uses the new status and does not overstate divine scope.
- [x] `formal/Logos/ClaimMeanings.lean` needs no update: all three claims have kernel declarations.
- [x] Generated `README.md`, `investigations/kernel-audit.md`, and dependency artifacts are regenerated.
- [x] `make` passes from the repository root.
- [ ] No `sorry`, no staged secret, and no accidental generated-file edit is left behind.

From the repository root, the standard regeneration sequence is:

```sh
export PATH="$HOME/.elan/bin:$PATH"
cd formal && lake exe depviz --roots Logos --json-out depgraph.json --dot-out depgraph.dot
cd .. && python3 scripts/audit_footprints.py && python3 scripts/build_deduction.py
make
```

`README.md` is auto-generated. Never edit it by hand.

## 8. Red flags for future agents

- “Necessary” in the prose does not automatically mean `NecessarySubject`.
- “Universal grounding” does not mean infinity, omnipresence, or omnipotence.
- “Normative authority” does not automatically mean benevolence.
- `Aseity` over an arbitrary relation does not prove aseity of `Entity.ofGround`.
- `Level3_VolitionAlternative` has no built-in accessibility, incompatibility, or distinct-world requirement.
- A countermodel is a positive formal result, but it is not a positive characteristic proof.
- A theorem with `{Means, Subject}` or `{Subject}` is vocabulary-priced even when its logical content is trivial.
- `PROVEN↑` is not unconditional proof; reader-facing output must say `AXIOMATIC`.
- A deferred claim is not an axiom unless it is explicitly declared and tagged.
- Do not resurrect deleted bridges (`ConstitutiveNormativeBridge`, retired manufactured ground witnesses, or old necessary-person theorems).
- Do not edit `README.md`, `kernel-audit.md`, or `axiom_audit.json` as a shortcut around the audit pipeline.

## 9. Source index

- `CHARACTERISTICS.md:1-765` — full prose inventory, formal-status layer, and current candidate checkpoints.
- `formal/Logos/Core.lean:35-199` — Level-0 truth/falsity definitions, C8/C9, and the C183 location.
- `formal/Logos/ModalPossibilityFrontier.lean:122-124,302-304,448-497` — `Aseity`, Level-3 alternatives, MC21, and the C182/C184 countermodels.
- `formal/Logos/NecessityEternity.lean:101-188` — C181 and canonical necessity/eternity corollaries.
- `formal/Logos/HardenedInvariance.lean:223-237` — C180 architectural invariance boundary.
- `formal/Logos/TheologicalModalHardening.lean:405-414` — necessary existence versus uniqueness countermodel.
- `formal/Logos/PersonhoodOntologyAudit.lean:216-227` — personhood versus necessary-subject countermodel.
- `formal/Logos/Choice.lean:231-268` — exact F1b missing resource and its consequence.
- `formal/Logos/MoralFrontierAudit.lean:173-214,255-269` — epistemic/practical separation and the priced moral-positive route.
- `formal/Logos/ConditionalTheology.lean:336-424` — Trinity, incarnation, and creation separations.
- `formal/GAPMAP.md:403-445,743-799` — Level-0/1 ledger and deferred/blocked frontier.
- `base.txt:1140-1146` — Portuguese formal-status boundary and C182/C184/C183 records.
- `theorems/T3.txt` — Level-0 truth/falsity theorem prose, including the C183 bundle record.
- `theorems/T19.txt` — Portuguese C182/C184 separation record and scope limitations.
- `theorems/T15.txt` — current necessity/eternity scope and honest limitations.
- `AGENTS.md:3-60` — synchronization, audit, regeneration, and generated-file rules.
