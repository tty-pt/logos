# [HISTORICAL AUDIT INVENTORY OF README-OLD.MD]
# Arguments for the Characteristics of the Ultimate Foundation

> ⚠️ **HISTORICAL AUDIT NOTICE FOR AGENTS AND CRITICS:**
> This document (`CHARACTERISTICS.md`) is a **historical audit inventory** that reconstructs and evaluates the informal arguments from the legacy draft [`README-OLD.md`](README-OLD.md).
> It does **not** define the active architecture of the Γ formalization, and its negative or absent badges reflect the informal claims of `README-OLD.md`, **not** the boundaries of the machine-verified Lean 4 kernel.
>
> **Authoritative Canonical References:**
> - **The Machine-Checked Deduction:** [`README.md`](README.md)
> - **Formal Kernel:** [`formal/Logos/`](formal/Logos/)
> - **Status Ledger:** [`formal/GAPMAP.md`](formal/GAPMAP.md)
> - **Verified Classical Attributes:** See `## Which Classical Attributes Are Already Established?` in `README.md` (where Divine Ground Necessity, Everlasting, Atemporal, and Canonical Aseity are machine-verified ✅).

> **Source scope:** This inventory reconstructs the arguments in [`README-OLD.md`](README-OLD.md) itself. It does not assess formalizability, import conclusions from the Lean formalization, or use external sources.
>
> **Formal-status layer (added 2026-09-25):** Each section below carries a `Formal status:` line audited against live Lean (`formal/Logos/*.lean`, `formal/GAPMAP.md`, `formal/axiom_audit.json`, `base.txt`, `theorems/*.txt`; `README.md` used only as corroboration). The prose inventory above is untouched; `✅` = PROVEN with no substantive named axioms (VOCAB + `CL` only), `AXIOMATIC / PROVEN↑` = machine-verified only under a named SEM/META axiom, `❌` = axiom / blocked / deferred / absent / countermodeled / disclaimed. Prose derivations are not claimed as formal theorems.

## Argumentative method

The text presents itself as a **meta-ontological** argument about the conditions of possibility of every evaluative system, rather than an ordinary deduction within one formal system (`README-OLD.md:3`).

Its five movements are:

1. Establish the logical pattern of self-reference through classical paradoxes.
2. Apply that pattern to the negation of ultimate normative truth.
3. Derive the foundation's characteristics by transcendental necessity.
4. Answer the principal objections.
5. Extract the alleged ontological consequences (`README-OLD.md:7`).

The method used to derive characteristics is explicitly **apophatic** or *via negationis*: each characteristic is the positive reformulation of a dependence, limitation, or contingency that the foundation cannot possess without ceasing to be ultimate (`README-OLD.md:144-145,189`). The text claims that the resulting positive attributes do not accumulate arbitrary properties onto the foundation; instead, they “purify” it by removing forms of dependence that would produce circularity, regress, or subordination (`README-OLD.md:189`).

## 1. Transcendence and externality

**Status in the prose:** Central, repeated, and one of the strongest explicit arguments.

**Formal status: ❌ absent — no live theorem establishes a foundation external/transcendent to every system.** Nearest live nodes prove only a definitional world-rigid ground (`NecessityEternity.ofGround_ground_of_reality`, `formal/Logos/NecessityEternity.lean:118`, footprint `{Means, Subject}` VOCAB) and a personal ground-*type* for Right/Wrong (`PersonalGroundOfReality.the_person_supports_the_reality_of_right`, `formal/Logos/PersonalGroundOfReality.lean:150`, footprint `{Initiates, Means, State, Subject, CL}`), neither of which is externality to every formal/evaluative system. Ultimate-ground and quantifier-swap claims are BLOCKED/retired (`formal/GAPMAP.md` C78/C79/C88). Gödel/Tarski/Turing pattern is not formalized.

### Argument

The text begins with self-referential systems:

- Tarski's object-language/metalanguage distinction presents truth at one level as depending on evaluation at a higher level (`README-OLD.md:29`).
- Gödel is described as showing that a sufficiently expressive system contains propositions it cannot decide by its own means (`README-OLD.md:31`).
- The halting argument is reduced to the diagonal scheme `Q(P) = ¬P(P)`, which becomes paradoxical when applied to itself: `Q(Q) = ¬Q(Q)` (`README-OLD.md:67-71`).
- The common pattern is described as the impossibility of a total, correct, and complete evaluator that includes itself in its own domain (`README-OLD.md:73-79`).

The text then generalizes that pattern beyond formal systems:

1. A system cannot exhaustively provide its own evaluative foundation.
2. Evaluation therefore requires a point outside the evaluated domain.
3. A brute fact is insufficient because it can terminate causal explanation without grounding why an evaluation is valid (`README-OLD.md:132-136`).
4. A physical mechanism may describe how something functions, but it does not thereby ground the correctness of its own existence or the obligatoriness of its intelligibility (`README-OLD.md:136`).
5. Consequently, there must be an ultimate foundation external to any and every system (`README-OLD.md:138`).

The same conclusion is summarized as “transcendent to any formal structure” and as a condition of possibility of the correct/incorrect distinction (`README-OLD.md:229-234`). In the theological identification, this becomes “non-systemic (transcends all formal structure)” (`README-OLD.md:249`).

### Characteristic argued for

The foundation is **transcendent**: it is not exhausted by membership in any formal or evaluative system.

> **Now established in Γ, both halves.** Ontological transcendence — neither an atomic worldly
> state nor the correlate of any subject — is PROVEN with existence (`ofGround_transcendent`, C195)
> *and* uniqueness (`ofGround_sole_transcendent_ground`, C307, `{Subject}`, unconditional). The
> uniqueness theorem had been proved for a long time with **no reader-facing row at all**; it now
> has one (batch SOLE-BEARER-AND-DERIVABILITY, 2026-09-28, C439–C453). The four boundaries below
> were already ledgered (C301, C304, C306, C308) and are what keep the sense from reading as causal.

### Gaps and ambiguities

- “External” is not defined. It shifts among logical, ontological, hierarchical, and possibly causal senses. **Γ's proved sense is the ontological one only**, and the module machine-checks that the other three do not follow: universal grounding does not entail causal externality (C306), membership exclusion does not entail grounding exclusion (C304), the diagonal route delivers no system externality even given the whole `DiagonalSpec` (C308), and outsiders of different systems need not coalesce (C301).
- The passage from “each system needs something outside itself” to “one foundation is external to every system” is asserted rather than demonstrated (`README-OLD.md:132-138`). Different systems might, on the text's own account, possess different outside points.
- The extension of the Gödel/Tarski/Turing pattern to every normative claim is the decisive transcendental move, but it is not independently established (`README-OLD.md:83-89`).
- The rejection of brute facts presupposes that a foundation must explain the binding character of normativity, not merely terminate explanatory regress (`README-OLD.md:134-136`).

## 2. Aseity: non-derived, uncaused, and non-dependent

**Status in the prose:** Explicit, direct, and closely tied to the definition of ultimacy.

**Formal status: ✅ (qualified) conditional canonical aseity and generic exclusion PROVEN; unconditional aseity independent without finite-subjectivity premise.** Generic `Logos.ModalPossibilityFrontier.Aseity` (`formal/Logos/ModalPossibilityFrontier.lean:122-124`, `{}`) and its two-way independence with volitional alternatives (C182/C184, `{}`) establish the bare modal frontier. Canonical external grounding (`ExternalGrounding g e := g ≠ e ∧ GroundsEntity g e`) and canonical aseity (`CanonicalAseity e := ¬ ∃ g, ExternalGrounding g e`) are formalized in `Logos.CanonicalAseity` (`formal/Logos/CanonicalAseity.lean`). Results: (1) generic meaning-exclusion `false_meaning_cannot_ground_true_meaning` (C185, `{}`); (2) unconditional exclusion of atomic entities `atom_cannot_ground_the_ground` and `no_atom_externally_grounds_the_ground` (`{Means, Subject}`); (3) conditional canonical aseity `conditional_canonical_aseity` (C186, `{Means, Subject}`), proving `CanonicalAseity Entity.ofGround` provided all subjects are discriminating (`∀ s, ∃ p, ¬ Means s p`); (4) modal aseity `ofGround_modal_aseity_conditional` (`{Means, Subject}`); and (5) metatheoretic independence `unconditional_aseity_independent_of_bare_agency` (`{}`), showing that bare agency logic alone without a finite-subjectivity premise does not force unconditional aseity.

### Argument

The text argues by contradiction:

1. Suppose the foundation could not exist.
2. Alternatively, suppose it were derived from something more basic.
3. In the first case, there would be something more fundamental whose existence was required.
4. In the second case, the proposed foundation would be a derived entity and the more basic source would be the actual foundation.
5. The same reasoning applies to causation: if the foundation had a cause, the cause would be more fundamental than the alleged foundation (`README-OLD.md:151-152`).
6. Since the argument concerns the ultimate foundation, nothing may be more fundamental than it.
7. Therefore, the foundation cannot be contingent in the relevant sense, derived, or caused; it is non-derived (`README-OLD.md:151-152,230,248`).

The same regress structure supports the broader prohibition on dependence: a condition that governed the foundation would itself function as a higher foundation (`README-OLD.md:154-155`). Normative authority must likewise derive from no rule, structure, or external criterion (`README-OLD.md:173-175`).

The “Minimal Subject” is consequently defined as the locus of **Non-Derived Normative Agency** (`README-OLD.md:179-183`).

### Characteristic argued for

The foundation is **a se**: it depends on nothing else and is neither derived nor subordinate.

### Gaps and ambiguities

- The argument depends on “ultimate” meaning non-derived. The result may therefore be analytic rather than independently demonstrated.
- It does not distinguish causal dependence, explanatory dependence, logical derivation, and ontological grounding, although the prose shifts among them.
- The text admits the risk of circularity in self-foundation but does not show that the proposed definition avoids circularity (`README-OLD.md:149`).
- Aseity in the causal sense is not explicitly named; the prose argument is a regress argument against dependence.

## 3. Necessity and non-contingency

**Status in the prose:** Explicit, but supported by a transcendental and performative argument rather than ordinary modal deduction.

**Formal status: ✅ (qualified) for necessary truth/order and definitional entity-necessity; ❌ for a necessary person.** `Semantics.strongTruthExists` (`formal/Logos/Semantics.lean:113`, footprint `{CL}`) PROVEN; `Core.rightWrongDistinction` (`formal/Logos/Core.lean:145`, `{}`) PROVEN; `NecessityEternity.ofGround_necessary` (`formal/Logos/NecessityEternity.lean:110`, `{Subject}` VOCAB, definitional `EntityExistsAt w .ofGround := True`) PROVEN — world-rigidity by stipulation, not derived from the act. `Person → NecessarySubject` is machine-refuted (`PersonhoodOntologyAudit.faithful_contingent_person_fails_necessary_subject`, `formal/Logos/PersonhoodOntologyAudit.lean:221`, `{}` COUNTERMODEL); necessary-entity/person conjunctions are DEFERRED (`formal/GAPMAP.md` C77/C92). Prose performative necessity ≠ modal `NecessaryEntity`/`NecessarySubject`.

### Argument

The text defines “Strong Truth” as the existence of at least one proposition whose negation would make the act of negating it performatively incoherent (`README-OLD.md:93-105`). It then argues:

1. The claim “there is no Strong Truth” must be intelligible and binding if it is to function as a rational denial.
2. But intelligibility and bindingness require the normative distinction between acceptance and rejection—the very kind of normativity the claim denies.
3. The denial therefore attempts to invalidate a condition required for its own formulation and evaluation (`README-OLD.md:109-115`).
4. The same objection is applied to “truth is subjective”: the empirical individual is itself an evaluated object and cannot simultaneously supply the unevaluated normative authority it claims (`README-OLD.md:117`).
5. The text concludes that the contrary—objective or Strong Truth—cannot be denied without performative incoherence and is therefore “necessarily true” in its defined sense (`README-OLD.md:119-127`).
6. Since denouncing universal rational validity would abandon the possibility of rational evaluation, criticism, or generally valid objection, the foundation's necessity is said to be unavoidable (`README-OLD.md:195-216,229-236,270`).

“Necessary” is explicitly redefined as “that whose negation implies performative impossibility or impossibility of coherent normative discourse,” rather than merely formal or psychological necessity (`README-OLD.md:127`). The theological summary renders this as “timeless and necessary,” glossed as independence from spatiotemporal conditions (`README-OLD.md:254`).

### Characteristic argued for

The foundation is **necessary** in the performative-transcendental sense that rational evaluation cannot coherently deny the normative conditions it presupposes.

### Gaps and ambiguities

- The argument moves from the incoherence of denying **all Strong Truth** to the truth of a more general claim about **objective truth** (`README-OLD.md:119`) without an intermediate argument.
- “Necessary” is stipulated or redefined in a special performative sense, not derived under an independently fixed modality.
- It remains unclear whether the conclusion requires the existence of a particular entity, merely the indispensability of some normative condition, or the impossibility of coherently denying that condition.
- The text uses “postulated” as well as “necessarily follows,” leaving the inferential status of the conclusion ambiguous (`README-OLD.md:119-121`).

## 4. Normative sovereignty and authority

**Status in the prose:** One of the most elaborately argued positive characteristics.

**Formal status: ✅ datum-conditional, no substantive axioms.** `Core.rightWrongDistinction` (`formal/Logos/Core.lean:145`, `{}`) PROVEN; `PersonalNormativeGround.freeWill_grounds_right_wrong` (`formal/Logos/PersonalNormativeGround.lean`, `{Means, Subject}`) PROVEN with personalness as the priced theorem `grounding_right_wrong_entails_person`; headline `PersonalGroundOfReality.the_person_supports_the_reality_of_right` (`formal/Logos/PersonalGroundOfReality.lean:152`, `{Initiates, Means, State, Subject, Will, subjectWill, will_individuation, CL}`) PROVEN; reality-hook `RealityHookAudit.content_reality_hook` (`formal/Logos/RealityHookAudit.lean:85`, `{Initiates, Means, State, Subject}`) PROVEN. The new local retorsional corollary `DirectNormativeRetorsion.no_correct_claim_of_no_right_can_be_true` (`formal/Logos/DirectNormativeRetorsion.lean:174`, `{}`) is also PROVEN. Boundary: unconditional `¬NoGN` is underivable (`M_inanimate`, `formal/GAPMAP.md` C167, `{}`); the broader theorems are conditional on the judicative datum/stance, with `CL` only.

### Argument

The text argues:

1. The true/false distinction is already a minimal normative distinction: some assertions must be accepted and others rejected (`README-OLD.md:125`).
2. Every analysis of truth, even a skeptical one, presupposes a criterion of correctness (`README-OLD.md:126`).
3. Therefore, the foundation of truth is also the foundation of normativity (`README-OLD.md:125`).
4. Normativity is more than descriptive regularity. A structure can describe what happens; only authority can discriminate what rationally should be accepted (`README-OLD.md:167`).
5. Brute facts, accumulated complexity, formal rule-structure, and passive mechanisms may describe or register evaluation, but none explains the binding quality of rational obligation (`README-OLD.md:167-175`).
6. A correct/incorrect distinction claiming general validity therefore requires a source of authority that derives its authority from no prior rule, structure, or external criterion (`README-OLD.md:175`).
7. The source is called the “Original Subject,” defined functionally as the locus of non-derived normative agency (`README-OLD.md:167,179-187`).

The conclusion calls this foundation “normatively authoritative” and the source of rational binding (`README-OLD.md:232,250`).

### Characteristic argued for

The foundation possesses **normative sovereignty**: ultimate authority to determine what is rationally binding, rather than merely describing regularities.

### Gaps and ambiguities

- The key premise is that binding normativity requires an authoritative source. This is asserted rather than defended (`README-OLD.md:167,173-175`).
- The argument moves from epistemic normativity—what is correct to assert—to “ought” and VALUE without establishing that theoretical correctness itself generates practical or moral obligation.
- “Authority” is not independently defined. The text alternates among source, agency, active discrimination, and subjecthood.
- Calling the source a “Subject” is said to add no content (`README-OLD.md:181-187`), but the term later carries theological weight in the identification as Divinity (`README-OLD.md:243-260`).

## 5. Freedom, personality, and minimal subjecthood

**Status in the prose:** The most elaborated personality argument, but “personal” is explicitly functional rather than psychological.

**Formal status: ✅ conditional on judicative-stance/GN datum (no substantive axioms); AXIOMATIC / PROVEN↑ via A14; ❌ unconditional.** `IndubitableNormativeFreeWill.indubitable_normative_free_will` (`formal/Logos/IndubitableNormativeFreeWill.lean:115`, `{Means, Subject}`) PROVEN conditional on `GenuineNormativity` datum (`Chooses → FreeWill` is definitional, `Choice.FreeWill`, `formal/Logos/Choice.lean:163`); `NormativeOrder.claims_normative_correctness_derives_free_will` (`formal/Logos/NormativeOrder.lean:190`, `{Initiates, Means, State, Subject, CL}`) and `RetorsiveNormativity.attack_inviable_without_axioms` (`formal/Logos/RetorsiveNormativity.lean:309`, same footprint) PROVEN conditional on stance datum; `Person.free_subject_is_person` (`formal/Logos/Person.lean:33`, `{Means, Subject}`) PROVEN. A14 route `Choice.freeWill_exists` (`formal/Logos/Choice.lean:1066`) PROVEN↑ under `AxIntentionalChoice` (`formal/Logos/Choice.lean:770`, SEM). Unconditional `∃ s, FreeWill s` BLOCKED (missing `rejectedHornCoMeant`, `formal/GAPMAP.md` F1bUncond); substantive personhood separated (`CountermodelSubjectWithoutPerson`, `not_entails_person`).

### Argument

After excluding dependence, mechanisms, and impersonal regularity, the text argues:

1. Truth requires rational obligation, while mere objects and passive facts merely are (`README-OLD.md:167-175`).
2. Since obligation cannot arise from passive description, normative evaluation requires active discrimination (`README-OLD.md:167`).
3. An entity wholly dependent upon another could not possess ultimate authority (`README-OLD.md:154-155,171`).
4. Therefore, the ultimate source of normativity must be free in the sense of unconditioned and non-subordinate (`README-OLD.md:166-171,252`).
5. The text defines a **Minimal Subject** as any instance exercising binding normative evaluation whose authority is neither derived nor subordinate (`README-OLD.md:179-183`).
6. This is compared to Aristotle's `ὑποκείμενον`: what sustains or underlies the validity of what is posited (`README-OLD.md:183-185`).
7. Refusing the name “Subject” while accepting this function is characterized as merely nominal; the argument says the designation adds no further ontological content (`README-OLD.md:187`).
8. The resulting triad is logical self-reference requiring an external foundation, transcendental normativity requiring unevaluated authority, and ontological freedom requiring a Free and Necessary Subject (`README-OLD.md:272-275`).

### Characteristic argued for

The foundation is **free and personal** in the minimal sense of being an unconditioned locus of normative agency.

### Gaps and ambiguities

- “Freedom” is not independently defined; it largely means freedom from dependence or subordination (`README-OLD.md:171`).
- The argument assumes that normative authority requires agency and that agency must be personal in the text's functional sense (`README-OLD.md:167,171-175`).
- The text explicitly denies that “personal” establishes consciousness, psychological will, or ordinary personal relations (`README-OLD.md:181-187,263`).
- The slide from “source of normativity” to “Subject” is partly definitional and therefore does not independently establish personhood in the ordinary theistic sense.
- There is a tension between calling “Subject” a functionally neutral name (`README-OLD.md:187`) and including “free and personal” in the definition of Divinity (`README-OLD.md:243-260`).

## 6. Unity and oneness

**Status in the prose:** Explicit but compressed; closely connected to simplicity and universality.

**Formal status: ✅ PROVEN under one named hypothesis (Foundational Unicity; Aquinas ST I q. 11 a. 3) — see the 2026-09-27 correction below; ⊨ SEPARATED (Numerical Unitarianism); ⏸ DEFERRED (Strict Monotheism branch).**
Formalized in `Logos.FoundationalUnicity` (`formal/Logos/FoundationalUnicity.lean`):
(1) Master Metaphysical Theorem: `universal_ground_unicity` (C207, `{CL, Means, Subject}`), proving that two distinct entities cannot both be universal modal grounds under asymmetric grounding;
(2) Concrete Atom Exclusion: `no_atom_is_universal_modal_ground` (C208, `{Means, Subject}`), proving no atomic factual state can be a universal ground;
(3) Discriminating Subject Exclusion: `no_discriminating_subject_is_universal_modal_ground` (C209, `{Means, Subject}`), proving no finite subject can be a universal ground;
(4) Sole Universal Ground: `ofGround_sole_universal_ground` (C210, `{Means, Subject}`), proving `Entity.ofGround` is the unique universal ground candidate in Γ;
(5) Master Synthesis: `ofGround_foundational_unicity` (C211, `{CL, Means, Subject}`, 0 substantive axioms);
(6) Metatheoretic Independence: `unicity_does_not_force_unitarian_monad` (C212, `{}`), proving that foundational unicity does not force a solitary, relationless monad, keeping the Trinitarian frontier open;
(7) Ontological Transcendence: `unicity_strictly_transcends_world` (C213, `{Subject}`), confirming that the unique ground strictly transcends the world.
> **⚠ CORRECTION (2026-09-27, C313–C320 / F15).** Items (1) and (5) above rested on
> `AsymmetricGrounding`, which **C316 (`not_asymmetric_grounding`, COUNTERMODEL) proves
> unsatisfiable**: grounding is meaning-containment and therefore reflexive
> (`groundsEntity_reflexive`, C313), and the definition omitted the `g1 ≠ g2` guard. C207 and
> C211 remain PROVEN as *conditional* theorems and were not weakened or removed, but the
> attribute they were credited with was not established. The route was rebuilt:
> (8) `grounds_ground_iff_maximal` (C314, `{Means, Subject}`) — grounding the ground **is**
> `MaximalCapacity`, so the needed notion already existed and no new axiom was invented;
> (9) `ofGround_unicity_from_no_discriminating_subject` (C317, `{Means, Subject}`) — full
> unicity from the single hypothesis that no subject has total meaning-capacity;
> (10) `no_discriminating_subject_iff_no_maximal_non_ground` (C318, `{CL, Means, Subject}`) —
> that hypothesis **is** the exclusion of maximal capacity among non-ground entities, so the
> whole price is one existing predicate;
> (11) `ofGround_sole_universal_grounding` (C319, `{Means, Subject}`) — repaired synthesis with
> a plain-identity unicity field;
> (12) `exactly_one_universal_modal_ground` (C320, `{Means, Subject}`) — **Classical Monotheism
> stated outright**: existence unconditional, uniqueness under that one hypothesis.
> **Open (F15), but not a new act of faith:** the hypothesis is not asserted by any *axiom*,
> so C320 cannot consume it unconditionally. However the **identical sentence is already the standing
> premise of the corpus**: `canonical_aseity_conditional` (`DivineSimplicity.lean:79`),
> `ofGround_divine_simplicity` (`:180`) and `ofGround_divine_simplicity_and_transcendence` (`:191`)
> all take `hFinite : ∀ s : Subject, ∃ p : Prop, ¬ Means s p` — the same hypothesis, character for
> character — and C195/C196 are ledgered on it. **A second correction, same day: "three call sites"
> was a file-local count and badly understated the case.** The hypothesis shape occurs **20 times
> across 5 files** — `DivinePureActuality` 5, `FoundationalUnicity` 7, `CanonicalAseity` 4,
> `AsieticChoice` 1, `DivineSimplicity` 3 — so Γ pays this exact price for **five** attribute
> arguments (aseity, simplicity, pure actuality, choice/freedom, unicity), not two, and is no richer
> for it. F15 is an *unnamed* commitment passed ad hoc, not a new bridge. The outstanding decision is
> **consolidation** of that already-paid sentence into one named stipulation (`Tag: VOCAB`; being a
> `def` it leaves the axiom count at 25 and raises the stipulation registry from 5 to 6), which would
> make C320 an unconditional corollary and retire the row.

Separation: `TheologicalModalHardening.necessary_existence_not_entails_uniqueness` (`formal/Logos/TheologicalModalHardening.lean:406`, `{}`) proves uniqueness does not follow from bare necessity alone. Generated `README.md` corroborates: Foundational unicity ✅ PROVEN, Strict numerical unitarianism ⊨ INDEPENDENT, One God / strict monotheism ⏸ DEFERRED.

### Argument

The text gives the following via-negationis argument:

1. Suppose the foundation had parts.
2. The composition of those parts would require a more fundamental principle of unity (`README-OLD.md:163-164`).
3. That unifying principle would be more fundamental than the composite foundation, contradicting its ultimacy.
4. Suppose instead that the foundation were merely particular rather than universal.
5. A particular entity could found only its own domain, not reality as a whole (`README-OLD.md:164`).
6. Therefore, the ultimate foundation must be one and universal (`README-OLD.md:163-164,253`).

### Characteristic argued for

The foundation is **one**: it is non-composite and universally foundational.

### Gaps and ambiguities

- The text does not rule out two co-ultimate foundations. It argues against parts and particularity, not explicitly against a plurality of independent ultimate principles.
- “One” may mean numerical unity, non-composition, universality of scope, or all three.
- The premise that composition always requires a prior unifier is asserted rather than defended (`README-OLD.md:164`).
- Simplicity and unity are not clearly distinguished in the argument.

## 7. Simplicity and non-compositeness

**Status in the prose:** Present in the conclusions and theological identification, but only compressed within the unity and non-systemicity arguments.

**Formal status: ✅ PROVEN (mereological, structural, and intentional simplicity).** Formalized in `Logos.DivineSimplicity` (`formal/Logos/DivineSimplicity.lean`):
(1) Mereological Simplicity: `ProperPart p e := p ≠ e ∧ GroundsEntity p e`, `NonComposite e := ¬ ∃ p, ProperPart p e`, proving `non_composite_iff_canonical_aseity` and `ofGround_non_composite` (footprint `{Means, Subject, propext}`);
(2) Structural Inextension: `ofGround_has_no_internal_components` (C193, `{Subject}`), proving `Entity.ofGround` has zero internal decomposition;
(3) Intentional Simplicity: `ofGround_undivided_meaning` (C194, `{Means, Subject}`), proving uniform intentional capacity across reality;
(4) Ontological Transcendence: `ofGround_transcendent` (C195, `{Subject}`);
(5) The Master Synthesis: `ofGround_divine_simplicity` (C196, `{Means, Subject, propext}`, 0 substantive axioms), proving that `Entity.ofGround` satisfies classical Divine Simplicity under finite subjectivity;
(6) Metatheoretic Independence: `composite_entity_fails_simplicity` (C192, `{}`).
Honest boundary: This establishes mereological, structural, and intentional simplicity of `Entity.ofGround` — it does not establish identity of essence and existence or exhaustive formal simplicity.

### Argument

Two passages jointly support simplicity:

1. If the foundation had parts, their composition would presuppose a more fundamental principle of unity, contradicting ultimacy (`README-OLD.md:164`).
2. If the foundation were exhaustively formalizable, it would become an evaluable object within a system and thus reintroduce the self-reference excluded at the outset (`README-OLD.md:148-149`).

The Second Part explicitly lists simplicity among attributes derived from what the foundation cannot be (`README-OLD.md:238-241`). The later identification describes Divinity as “absolute, necessary Subject, simple and source of all normativity” (`README-OLD.md:258`).

### Characteristic argued for

The foundation is **simple** in at least two senses: non-composite and not exhaustibly reducible to a formal system.

### Gaps and ambiguities

- Non-compositeness, oneness, non-systemicity, inexhaustibility, and ineffability are not clearly separated.
- **Simplicity now discriminates the ground** (`divine_simplicity_sole_bearer`, C440; unicity alone is C439, `{Means, Subject}` — the cheapest sole-bearership in the corpus, and free of any substantive axiom, because the `no_internal_components` field closes the case: `HasInternalComponent` is `True` on `ofSubject` and `ofAtom` and `False` only on `ofGround`). **Disclosure, because it changes what the third conjunct is worth:** `EntityMeans (ofAtom _) = False` is a definitional stipulation, so `undivided_meaning` is *vacuously true of every atom* — an atom has uniform meaning capacity because it has none — and a subject that discriminates *nothing* satisfies it too. The structure is satisfied vacuously for the wrong reasons by non-ground entities; only `no_internal_components` is load-bearing for unicity. The mereological and intentional conjuncts remain meaningful for the ground, they simply do not discriminate.
- The classical metaphysical doctrine of divine simplicity normally includes claims such as identity of essence and existence or absence of potency. The prose supplies no argument for those stronger senses (`README-OLD.md:258`), and Scholastic simplicity (essence-existence identity) is explicitly separated in the attributes table as `❌ NOT ESTABLISHED`.
- The non-systemicity argument rules out exhaustive formal representation of the foundation, but it does not by itself establish a traditional doctrine of metaphysical simplicity.

## 8. Eternity, timelessness, and ontological precedence

**Status in the prose:** Explicit, although “eternity” is developed primarily as timelessness and precedence rather than everlasting duration.

**Formal status: ✅ definitional corollary of world-rigidity (VOCAB-only); not a full divine-eternity theology.** `NecessityEternity.the_ground_everlasting` (`formal/Logos/NecessityEternity.lean:160`, `{Subject}`), `the_ground_atemporal` (`:164`, `{Subject}`), `necessary_implies_everlasting` (`:145`, `{Subject}`), `necessary_implies_atemporal` (`:152`, `{Subject}`), `the_ground_not_in_succession` (`:169`, `{Initiates, State, Subject}`) all PROVEN. Honest boundary in `base.txt` §28: stage-unmodulated existence only; strong metaphysical divine eternity not claimed. Distinct from the love-*relation* `Love.T14_eternalRelation_conditional` (`formal/Logos/Love.lean:105`, `{AxTwoSubjects, Means, Subject}` PROVEN↑).

### Argument

The text argues:

1. To be temporally situated is to participate in succession and be submitted to causality (`README-OLD.md:160-161`).
2. The ultimate foundation cannot be conditioned by something more fundamental (`README-OLD.md:154-155`).
3. Therefore, it cannot be temporally conditioned in that way.
4. Instead, it must possess ontological precedence as the condition of possibility of temporal succession itself (`README-OLD.md:160-161`).
5. The foundation is thus identified as “timeless and necessary,” independent of spatiotemporal conditions (`README-OLD.md:254`).
6. This also supports the rejection of pantheism insofar as the universe is said to be contingent, composite, and in time (`README-OLD.md:264`).

### Characteristic argued for

The foundation is **timeless or eternal** in the sense of being prior to and independent of temporal succession.

### Gaps and ambiguities

- ~~The text does not distinguish timelessness from everlastingness.~~ **Discharged 2026-09-28 (C436–C438).** `Logos.NecessityEternity.lean` §6 now states the relation: `everlasting_implies_atemporal` (C436) is the generic step — `Everlasting e := ∀ t, ExistsAtTime t e`, `Atemporal e := ∀ t₁ t₂, ExistsAtTime t₁ e ↔ ExistsAtTime t₂ e`, so the second is the first stated twice, and the `↔` is discharged by the two one-directional instances. It was missing because the module had only the ground-level instances (`the_ground_everlasting`, `the_ground_atemporal`), both routed through `ofGround_necessary`. `contingent_subject_is_timeless_but_not_everlasting` (C437) is the separating counterexample, and its `Atemporal` half holds **vacuously**: under `ContingentSubjectKind s` the existence clause reduces to `stageOf t = actualWorld`, false at every `t` (at index `t+1`, `stageOf t (t+1) = TV.f` against `actualWorld (t+1) = TV.t`), so both sides of the `↔` are false. That vacuity is the *point*, not a defect — it is how an entity can be "timeless" without existing everywhere. `everlastingness_and_timelessness_are_distinct` (C438) is the bundle.
  **The limit, and it is not optional:** Γ has **no theorem inhabiting `ContingentSubjectKind`** — every occurrence in the corpus is a hypothesis (`LovesAsGround.lean:196`, `CosmicExistence.lean:299` and following, with the `Creates` row at `CosmicExistence.lean:695` still BLOCKED). So the separating region is inhabited in the *models*, not the *kernel*: what is proved is that the vocabulary **distinguishes** the two notions, **not** that some subject of Γ falls in the difference. The unconditional schema `¬ (Atemporal e → Everlasting e)` is **not derivable** and is deliberately not stated — the ground is atemporal *and* everlasting, and so is `Entity.ofAtom 0`.
  **A vocabulary finding that changes how this entry reads:** C432 (Chain 6) shows `StageInvariance` and `Atemporal` are the *same predicate under two names*. The immutability master's second field and §8's "timelessness" are one step, not two.
- ~~“Precedence” could mean logical, ontological, or temporal priority.~~ **Partly discharged 2026-09-28 (C432–C435), and the two temporal/logical senses are now *separated* rather than conjoined.** `ofGround_sole_precedes_right_wrong` (C433) gives §9's precedence a **unique** instance, and its price is F15: the `ofSubject s` case forces `∀ p, Means s p`, refuted by `SemanticFinitude` — so §9's unicity is a corollary of the same declared bound that closed F15's foundational unicity. `stage_invariance_does_not_uniquely_identify_the_ground` (C434) is the counterexample that makes the comparison possible: `Entity.ofAtom 0` *is* stage-invariant (`0 ≤ t` at every stage) and is not the ground. The ontology sense of "precedes" remains a reading, disclosed as `GroundsEntity` — a condition, never a derivation.
- The premise that temporal existence necessarily implies submission to causality is asserted rather than argued (`README-OLD.md:161`).
- Immutability: Formally established in `Logos.DivineImmutability` (`formal/Logos/DivineImmutability.lean`, C197–C201). `ofGround_divine_immutability` proves Classical Divine Immutability (Aquinas *ST* I, q. 9) via modal invariance (`ofGround_modal_invariance`, `{Subject}`), stage invariance (`ofGround_stage_invariance`, `{Subject}`), process invariance (`ofGround_transition_invariance`, `{Initiates, State, Subject}`), and capacity invariance (`ofGround_capacity_invariance`, `{Means, Subject}`), with footprint `{Initiates, Means, State, Subject}` (0 substantive axioms). The countermodel `contingent_entity_fails_immutability` (C197, `{}`) confirms that contingent entities fail immutability. **Vacuity disclosure (C321, `{}`-free: `{Means, Subject}`):** the fourth field, capacity invariance, **discriminates nothing** — `capacity_invariance_holds_for_every_entity : ∀ e, CapacityInvariance e`. `EntityMeans` is `Entity → Prop → Prop` and takes **no world argument** (`RecoveredOntologicalGround.lean:46`), so the two worlds in `CapacityInvariance` are bound and unused and the body is `P ↔ P` (`exact Iff.rfl`); the property holds for every entity, subjects and atoms included. All three siblings genuinely quantify and each has a `{}` non-triviality countermodel (C197, with C192/C202/C214 for the other attribute masters); this field has none, because there is nothing in it to refute. **This is disclosure, not demotion — `ofGround_divine_immutability` remains `PROVEN`.** The substantive reading (constancy *across worlds*, *ST* I q. 9 a. 3) is inexpressible in the present vocabulary: it needs a world-indexed `EntityMeansAt` plus proof that its variation is non-empty, which is frontier **F16**, not added. Honest boundary: this establishes modal, temporal, process, and capacity unchangeability in Γ; it does not claim psychological impassibility (which is explicitly separated in the attributes table as `❌ NOT ESTABLISHED`, with Γ affirming the eternal relation of love in T14).
- The claim that the universe is contingent, composite, and temporal is assumed in the pantheism objection rather than derived there (`README-OLD.md:264`).

## 9. Precedence to the true/false distinction

**Status in the prose:** Explicit, although its relation to later logical and temporal precedence is not fully explained.

**Formal status (re-dated 2026-09-28): ✅ PROVEN in the semantic layer, ❌ not established in the truth-predicate layer — a split, not a bare ✅.** The characteristic had **no theorem and no row at all** in the generated `CLASSICAL_ATTRIBUTES` table; it now has ten claims, C417–C426, in `formal/Logos/Precedence.lean`, on **0 new axioms, 0 new primitives, 0 new stipulations, 0 new ◈ registrations**. The headline `ofGround_precedes_the_right_wrong_distinction` (C425, `{Means, NecessarySubjectKind, Subject}`) packages four senses into `Precedence.PrecedesRightWrong`: the ground *obtains where no atom is true* (C419, `ofGround_obtains_where_no_atom_is_true`, `{NecessarySubjectKind, Subject}`), *conditions every content-bearing entity* through `GroundsEntity` (C423, `{Means, NecessarySubjectKind, Subject}`), *does not stand under the distinction* (C422, `ground_scope_is_not_the_truth_set`, `{Means, Subject}`), and *is not discriminated by it* (C424, `atom_fails_precedence`, `{NecessarySubjectKind, Subject}`). C420 adds the converse (`ground_existence_does_not_entail_any_truth`), so precedence is a **separation and not a filter**; C421 is the two halves conjoined. 

**The reason the badge is a split, and it is the most important sentence in this entry:** `Core.T p := p` is the identity on `Prop`, so `N_T` and `N_F` carry **no world index**. A precedence *relative to a world* at the level of the truth predicate is therefore not well-formed on the current vocabulary, and C426 (`rightWrongDistinction_is_world_invariant`, `{}`) is the machine-checked statement of that inertness — deliberately inert, so that the obstruction is exhibited rather than hidden. Lifting the entry to a single `✅` would require a world-indexed `T`, which is new vocabulary at `Tag: SEM` at minimum and is the author's decision, not the implementer's.

**And the first lemma this batch planned was false.** The batch plan opened with `no_form_satisfied_at_falsity_world`; `Satisfies` is closed under negation, so the all-`TV.f` world satisfies every negated form and no world satisfies no form. C418 (`every_world_satisfies_some_form`, `{}`) is the refutation, constructed without `Classical.choice` (the branch is on `w 0 = TV.t`). The positive form that replaced it — **no *atom* is true** (C417, `{}`) — is what the precedence is now stated over. The argument of §9 is not weakened by the correction; it is stated precisely for the first time. The author has not been asked to rewrite §9 itself: the characteristic remains his, and what changes is what Γ can say about it.

**Vacuity disclosure, to be read with the table.** On the current signature the *positive* half of §9 does no work: every world satisfies some form (C418), and in every world the ground's obtaining is already guaranteed by the `ofGround` arm of `EntityExistsAt`. C423 is meanwhile stronger than §9 asks and weaker than it looks — its meaning hypothesis is **not used**, because `GroundsEntity ofGround e` is `∀ p, EntityMeans e p → True`, so the ground conditions *everything*, meaning-bearing or not (the fact C328 already records for the meaningless). The discriminating force is entirely in the negative direction and in the vacuity report itself. A reader who wants §9 to *bite* needs a semantics leaving some form unassigned.

### Argument

The text argues:

1. Evaluation requires the distinction between true and false.
2. The distinction therefore presupposes a condition making it possible.
3. If the duality founded itself, its own foundation would be self-referential.
4. The foundation must consequently precede the distinction as its transcendental condition (`README-OLD.md:157-158`).
5. The conclusion summarizes the foundation as “condition of possibility of the correct/incorrect distinction” (`README-OLD.md:234,251`).

### Characteristic argued for

The foundation is **logically or ontologically prior to the true/false distinction**, making evaluation possible rather than emerging from it.

### Gaps and ambiguities

- The meaning of “precede” is left undefined. **Partly discharged (2026-09-28):** the implementation reads it as `GroundsEntity` — a **condition, never a derivation** — and says so in the claim's own text; the word is now a declared reading, not a free one.
- The argument does not explain how the same foundation can precede the distinction and serve as its active discriminator. **Now formalized, and with a caveat:** the ground's obtaining and its *not* standing under the distinction are C419 and C422, and the discrimination is C423 (it conditions every bearer). The caveat is C423's non-use of its meaning hypothesis, reported above.
- ~~The relation between precedence over evaluation and precedence over time is not articulated.~~ **Discharged 2026-09-28 (C435), as a separation of discriminating power — which is the honest form and not the conjunctive one.** `precedence_identifies_the_ground_where_stage_invariance_does_not` reads: `PrecedesRightWrong` has a unique instance (C433) and `StageInvariance` has at least two (C434). So the two precedences are **different predicates with different extensions**, and only §9's singularises the ground. **What is established:** they are not coextensive, and only one picks the ground out. **What is not:** any identification of "precedence over evaluation" with "precedence over time" — the first two sentences of this paragraph *are* that refusal. The obvious wrong move is to conjoin `PrecedesRightWrong Entity.ofGround` with `StageInvariance Entity.ofGround`: that is a restatement of C425 plus `ofGround_stage_invariance` and discriminates nothing, which is the identical defect `CapacityInvariance` carries and which C321 already reports as vacuous. A vocabulary finding belongs here too — C432 records that `StageInvariance` is `Atemporal` under another name, so the comparison is between *one* temporal notion and *one* logical notion, not between two each.

**Nearest live results outside the batch:** the distinction itself (`Core.rightWrongDistinction`, `formal/Logos/Core.lean:145`, `{}`) and its personal ground-type (`PersonalNormativeGround.freeWill_grounds_right_wrong` + `grounding_right_wrong_entails_person`).

## 10. Non-conditioned and non-relative character

**Status in the prose:** Explicit, and partly distributive across necessity, freedom, and universality.

**Formal status: ✅ limited architectural invariance only; ❌ metaphysical non-relativity.** The new theorem `HardenedInvariance.agent_invariant_core_is_strictly_inside_freewill_invariant_core` (`formal/Logos/HardenedInvariance.lean:226`, C180/T18) proves that the agent-invariant dependency-layer core is a proper subset of the free-will-invariant core, with literal footprint `{}`. The regenerated reader-facing table in `README.md` (“Which Classical Attributes Are Already Established?”) places it in a separate `Proof architecture (not divine scope)` row with derived `✅ PROVEN`. It does not establish that the ultimate foundation is invariant across systems, perspectives, or possible worlds; no canonical `Unconditioned`/`Absolute`/`NonRelative` bridge is instantiated.

### Argument

The text argues:

1. Any condition limiting the foundation would act as a higher foundation (`README-OLD.md:154-155`).
2. If the foundation varied by perspective or evaluative system, it would cease to ground all systems (`README-OLD.md:154-155`).
3. A thing relative to one system cannot be the universal condition of all systems.
4. Therefore, the foundation is unconditioned and non-relative (`README-OLD.md:154-155,171`).

### Characteristic argued for

The foundation is **absolute**: unrestricted by prior conditions and invariant across perspectives or systems.

### Gaps and ambiguities

- “Condition,” “perspective,” “system,” and “relative” are not defined.
- The argument does not show that an unconditioned foundation must be metaphysically invariant; it infers that from its universal foundational role.
- Freedom from causal dependence, logical conditions, and spatiotemporal conditions are treated together without distinction.

## 11. Universality and infinity

**Status in the prose:** Universality is explicit; infinity is an allusive traditional identification rather than a developed independent argument.

**Formal status: ✅ Foundational Omnipresence & Universal Modal Grounding PROVEN (`Logos.FoundationalOmnipresence`, C202–C206); ❌ quantitative infinity.** `FoundationalOmnipresence.ofGround_foundational_omnipresence` (`formal/Logos/FoundationalOmnipresence.lean:160`, `{Means, Subject}` — VOCAB only) proves Classical Foundational Omnipresence (Aquinas *ST* I, q. 8) for `Entity.ofGround`:
1. World-Rigid Presence (`ofGround_world_rigid_presence`, `{Subject}`): present across all possible worlds;
2. Universal Modal Grounding (`ofGround_universal_modal_ground`, `{Means, Subject}`): grounds every entity existing in any possible world;
3. Non-Reciprocal Grounding (`ofGround_non_reciprocal_ground`, `{Means, Subject}`): no worldly atom or discriminating subject grounds the ground;
4. Maximal Intentional Capacity (`ofGround_maximal_capacity`, `{Means, Subject}`): comprehensive meaning capacity across reality.
Metatheoretic countermodel `finite_entity_fails_omnipresence` (C202, `{}`) confirms that localized entities fail universal grounding. Honest boundary: establishes foundational sustaining presence across modal reality in Γ; explicitly distinguishes foundational omnipresence from physical spatial omnipresence or quantitative metric infinity.

### Argument

The universality argument is implicit but repeated:

1. A foundation that varied by system would fail to ground other systems (`README-OLD.md:154-155`).
2. A merely particular foundation could not found reality universally (`README-OLD.md:163-164`).
3. Thus, the foundation must be universal in scope and is later described as founding “all reality” (`README-OLD.md:253`).
4. The identification associates the same result with Spinoza's “infinite substance” (`README-OLD.md:258`).

### Characteristic argued for

The foundation is **universal** in scope, and is traditionally identified as an “infinite substance.”

### Gaps and ambiguities

- Physical omnipresence: Spatial coordinates and physical spacetime are absent from Γ's ontology; physical omnipresence (diffusion throughout physical space) is explicitly separated in the attributes table as `❌ NOT ESTABLISHED`.
- Quantitative infinity: No independent argument from unconditionedness to quantitative infinity appears in the prose. Quantitative metric infinity (spatial magnitude or cardinal size) is explicitly separated as `❌ NOT ESTABLISHED`.
- The text explicitly disclaims any inference to omnipotence or omniscience (`README-OLD.md:263`).
- “Infinite substance” is introduced through identification with traditional language, not derived through a separate argument (`README-OLD.md:258`).

## 12. Pure actuality

**Status in the prose:** A traditional label is mentioned, but no act/potency argument is developed.

**Formal status: ✅ PROVEN for classical Pure Actuality (*Actus Purus*) in `formal/Logos/DivinePureActuality.lean` (C214–C220; `{Initiates, Means, State, Subject}`, 0 substantive axioms); ❌ NOT ESTABLISHED for physical kinetic/thermodynamic energy.** Results: (1) `ofGround_no_existential_potency` (C215, `{Subject}`): zero existential potency; (2) `ofGround_no_grounding_potency` (C216, `{Means, Subject}`): zero grounding potency; (3) `ofGround_no_transition_potency` (C217, `{Initiates, State, Subject}`): zero transition potency; (4) `ofGround_no_intentional_potency` (C218, `{Means, Subject}`): zero intentional potency; (5) `ofGround_divine_pure_actuality` (C219, `{Initiates, Means, State, Subject}`): Master Synthesis of Divine Pure Actuality; (6) `ofGround_incorporeal` (C220, `{Subject}`): Divine Incorporeality and Immateriality (Aquinas ST I q. 3 a. 1–2: *Deus non est corpus*); (7) `entity_with_potency_fails_pure_actuality` (C214, `{}`): Metatheoretic Independence Countermodel.

### Argument

The text says that definitions of God as Aquinas's “pure act,” Leibniz's “necessary being,” Spinoza's “infinite substance,” and “That which is” are different attempts to articulate the characteristics already derived (`README-OLD.md:258`).

The closest positive support comes from the claims that the foundation is unconditioned, non-systemic, timeless, and non-relative (`README-OLD.md:148-167`).

### Characteristic argued for

The foundation is **pure act**, meaning actuality without dependence on potentiality—although this act/potency interpretation is supplied by the cited tradition, not explained in the text.

### Gaps and ambiguities

- The document contains no developed argument about potentiality, change, or act.
- The timelessness argument does not explicitly infer the absence of unrealized possibility.
- The text assumes that “pure act” names the same structure as its own argument without an intermediate metaphysical bridge (`README-OLD.md:258`).

## 13. Sovereignty over value and goodness

**Status in the prose:** Only an allusive extension of normative sovereignty; moral goodness is not independently argued.

**Formal status: AXIOMATIC / PROVEN↑ for the moral pole under one META bridge; ❌ as derivation from epistemic normativity alone or as divine attribution.** Epistemic normativity never forces a practical pole (`MoralFrontierAudit.epistemic_normativity_without_practical_obligation`, `formal/Logos/MoralFrontierAudit.lean:179`, `{}` COUNTERMODEL; `moral_pole_postulate_is_not_a_consequence`, `:261`, `{Initiates, Means, State, Subject}`). `Good` is a fair VOCAB-only definition (`MoralFrontierAudit.Good`, `:203`, `{Means, Subject}`) and `moral_good_obtains` (`:212`, `{AxBenevolentBearingObtains, Means, Subject}`) is PROVEN↑ under `AxBenevolentBearingObtains` (`formal/Logos/Value.lean:183`, META AXIOM); the bare layer is empty (`Value.no_help_obtains`, `:110`, `{Subject}`) and `Evil` remains a SEM datum (`formal/Logos/MoralFrontierAudit.lean:238`). Divine attribution stays a frontier (`formal/GAPMAP.md` F3; `base.txt` §21/§28).

### Argument

The text establishes authority over rational correctness and binding normativity (`README-OLD.md:125,167-175`). It then calls the foundation:

- the source of rational binding (`README-OLD.md:250`);
- the source of all normativity (`README-OLD.md:258`); and
- in the diagram, the “Source of VALUE” (`README-OLD.md:307-309`).

The argument does not separately reason from normative authority to moral goodness.

### Characteristic argued for

At most, the foundation is the **source of value** in the broad sense of normativity.

### Gaps and ambiguities

- “Value” is not defined.
- Epistemic correctness—distinguishing what is true from false—is not by itself a derivation of moral goodness, benevolence, or the summum bonum.
- Benevolence is explicitly excluded from the demonstrated attributes (`README-OLD.md:262-263`).
- The VALUE node appears in the diagram without a corresponding prose argument (`README-OLD.md:308-309`).

## 14. Omniscience

**Status in the prose:** Explicitly disclaimed.

**Formal status: 🟡 partially established — the weak foundational sense is PROVEN; the classical sense is machine-checked as refuted for the ground.** `formal/Logos/DivineOmniscience.lean` proves *foundational* omniscience for `Entity.ofGround` (C233–C240, all vocabulary-only, 0 substantive axioms): no true proposition and no state of affairs true in any world is closed to the ground's scope (`ofGround_truth_exhaustive`, `ofGround_world_truth_exhaustive`, `{Means, Subject}`), atoms and discriminating subjects are excluded from that scope, and the master synthesis is `ofGround_foundational_omniscience` (`{Means, Subject}`). The *strong* (infallible, "all and only truths") sense is **not merely unproven but refuted** for the ground: `ofGround_not_truth_tracking` (`{Means, Subject}`) proves `¬ TruthTracking Entity.ofGround`, since the ground's scope bears every proposition (`EntityMeans .ofGround p` reduces to `True`). The counterfactual sense is independent (`exhaustive_scope_without_counterfactual_knowledge`, `{}`). Ordinary omniscience remains out of reach: Γ has no `Knows` predicate, `DeepModalFrontier`'s `Omniscience_AllTruths` / `Omniscience_Counterfactuals` remain frontier vocabulary definitions, and `Entity.ofGround` is not a subject correlate (`ofGround_ne_ofSubject`). The prose disclaimer therefore **agrees** with the kernel: see `theorems/T26.txt` and `formal/GAPMAP.md` Level 16.

### Boundary of the argument

The text says that the conclusion does not demonstrate ordinary omniscience, because “personal” has been defined only functionally and does not establish consciousness, knowledge, or ordinary personal attributes (`README-OLD.md:179-187,262-266`).

### Characteristic argued for

No classical omniscience argument is supplied. Knowledge of all truth does not follow merely from being the condition of truth.

### Gaps and ambiguities

- To derive omniscience, one would need a bridge from normativity to knowledge and a proof that the foundation possesses unrestricted knowledge.
- The text explicitly draws the boundary against such an inference (`README-OLD.md:263`).
- Machine-checked consequence: the kernel now *refutes* the exclusive half of the classical sense for the canonical ground (C236), so the remaining gap is not "the proof is missing" but "the vocabulary must change" — a knowledge predicate (`Knows`) is required before any omniscience claim can even be stated, let alone proved.

## 15. Omnipotence

**Status in the prose:** Explicitly disclaimed — **for the causal sense only**.

**Formal status: 🟡 partially established — the orthodox non-contradictory sense is PROVEN; the causal/creative sense remains 🔴 BLOCKED.** `formal/Logos/DivineOmnipotence.lean` proves *foundational* omnipotence for `Entity.ofGround` (C241–C251, 0 substantive axioms), on the reading that is Aquinas' own (*ST* I, q. 25, a. 5, ad 1, *semper et ubique operans*): **power over whatever does not involve a contradiction**. No state of affairs satisfiable in any accessible world is closed to the ground's operative scope (`ofGround_gapless_operative_scope`, `{Subject}`); nothing unobtained — hence nothing unsatisfiable — is operated (`ofGround_operates_only_what_obtains`, `{Subject}`); and no contradiction is ever operated (`ofGround_does_not_operate_contradictions`, `{Subject, propext}`, via `Semantics.nonContradiction`, C14). The reading is substantive rather than vacuous, since the scope domain is machine-checked non-empty and contradiction-free (`satisfiable_scope_is_nonempty_and_contradiction_free`, `{propext}`), and the ground is the **sole** gapless operator in Γ's `Entity` inventory (`ofGround_sole_gapless_operator` with `atom_not_gapless_operate` and `discriminating_subject_not_gapless_operate`, `{Subject}`). The master synthesis is `ofGround_foundational_omnipotence` (`{Means, Subject, propext}`), with the Thomistic *semper* principle `necessity_and_presence_yield_foundational_omnipotence` alongside it.

**Only the contradiction-omni reading is refuted** — "power over everything conceivable, *including contradictions*" — and it is refuted *by* the orthodox restriction, not against it. It was never the classical sense, and the first draft of this batch, which proposed to refute it as *the* sense, was wrong and has been corrected.

**The batch's price is disclosed, not hidden.** Γ declares no entity-level production relation, so `OperatesAt v e P := ExistsAt v e ∧ P v` reads "operates" as *presence plus obtaining*; this is registered and priced as the 4th stipulation ◈ `operatesAt_presencePlusObtaining` (`Tag: SEM`), and the price is machine-checked: `existence_everywhere_does_not_entail_operation` (`{}`) shows an entity present in every world can still operate nothing, and `exhaustive_scope_without_operative_scope` (`{}`) shows exhaustive meaning scope does not entail operative scope — so the result is proved from world-rigid presence, never read off `FoundationalOmniscience`. A further boundary, `gapless_operative_scope_without_conjunctive_power` (`{}`), records that Γ's modal accessibility is not conjunctive.

**The causal/creative sense — "can bring X about", as against "is present where X obtains" — stays 🔴 BLOCKED**, and the prose disclaimer (`README-OLD.md:263`) is **retained but narrowed to it**: the non-contradictory sense is now PROVEN, so the blanket disclaimer no longer describes the kernel. Γ's only initiation relation, `Agency.Initiates`, is subject-indexed (`Agency.lean:150`) and `Entity.ofGround` is provably not a subject correlate (`ofGround_ne_ofSubject`), so it cannot be instantiated by the ground; the closest relation is explanatory containment `GroundsEntity` (`RecoveredOntologicalGround.lean:57`), which C250 already blocks. See `theorems/T27.txt` and `formal/GAPMAP.md` Level 17 (row F10).

### Boundary of the argument

Founding the conditions of evaluation is not identified with causal power over every possible state of affairs. The text's claims concern foundational and normative priority, not the ability to bring about any contingent being (`README-OLD.md:263,266`). **The kernel now matches that boundary exactly:** it proves presence-and-obtaining over the non-contradictory and refuses to manufacture production.

### Characteristic argued for

No causal/creative omnipotence argument is supplied, and none can be stated in Γ's current vocabulary. The non-contradictory sense is not argued in the text either — it is derived in the kernel from the ground's world-rigid presence, and it is proved *over a priced identification* (◈ `operatesAt_presencePlusObtaining`).

### Gaps and ambiguities

- **Machine-checked consequence of the reframing:** the remaining gap is no longer "the proof is missing" for the foundational sense; it is that the identification used to state it is a stipulation. The price is now machine-checked on both sides (C241, C250), so it is disclosed rather than smuggled.
- The causal sense still requires **two** statements, in this order: (1) the vocabulary, a production relation `Produces : Entity → World → Form → Prop`; and (2) the derivation that the ground produces every satisfiable state of affairs, which (1) alone would not give.
- Universality of scope still does not establish ability to produce every possible state of affairs — and this is now a theorem, not an argument: `exhaustive_scope_without_operative_scope` (`{}`).
- The text expressly declines to derive causal omnipotence (`README-OLD.md:263`); the kernel agrees on that point and only there.
- A second trap, recorded in `theorems/T27.txt`: any consistency predicate built on `Core.T` is degenerate (`def T p := p`, `Core.lean:40`), so "does not involve a contradiction" must be read as satisfiability in Γ's classical valuation semantics, which is what C242/C251 do.

## 16. Benevolence and ordinary moral perfection

**Status in the prose:** Explicitly disclaimed.

**Formal status: ❌ as a divine attribute (agrees with the prose disclaimer).** The moral pole itself obtains only AXIOMATICALLY (`MoralFrontierAudit.moral_good_obtains`, `formal/Logos/MoralFrontierAudit.lean:212`, `{AxBenevolentBearingObtains, Means, Subject}` PROVEN↑ under `Value.AxBenevolentBearingObtains`, `formal/Logos/Value.lean:183`); epistemic-to-practical derivation is permanently separated (`epistemic_normativity_without_practical_obligation`, `:179`, `{}`); divine attribution remains a frontier (generated `README.md`: "Perfect (moral) goodness 🧱 INDEPENDENT" for the divine attribution).

### Boundary of the argument

Although the foundation is normatively authoritative, the argument does not establish that it is benevolent, morally perfect, or that its will is necessarily the summum bonum. The document distinguishes its minimal conclusion from ordinary theism (`README-OLD.md:262-266`).

### Characteristic argued for

No argument for benevolence or moral perfection is supplied.

### Gaps and ambiguities

- Normative authority does not logically imply benevolent intention.
- Source of truth is not the same as source of moral value without a further premise connecting correctness to goodness.
- The prose explicitly excludes the inference (`README-OLD.md:263`).

## 17. Founding all reality versus creation

**Status in the prose:** Founding reality is implicit; creation is neither named nor argued.

**Formal status: ✅ thin/foundational grounding only; 📌 creation *as a derived theorem*, not as entailment; ❌ creation ex nihilo as derivation.** `NecessityEternity.ofGround_ground_of_reality` (`formal/Logos/NecessityEternity.lean:118`, `{Means, Subject}`) PROVEN definitionally, and `PersonalGroundOfReality.person_grounds_normative_order` (`formal/Logos/PersonalGroundOfReality.lean:117`, `{Means, Subject}`) PROVEN for grounding correctness *about* reality (not causing existents). Contingent creation is NOT DEFERRED as existence — it is a **theorem**, and since lot COSMOS-EXISTENCE-IS-FREE (2026-09-27) it is a **free** one: `CosmicExistence.contingent_realm_obtains : ContingentRealmObtains` (**C350**, `PROVEN`) at footprint `{propext, Subject}`, with no bridge and no substantive axiom, witnessed by an atom through `LovesAsGround.an_atom_is_contingent 0`. Its *meaning* is the separate `PROVEN↑` row **C367** `CosmicExistence.cosmos_obtains : CreatedRealm`, derived from `Plurality.cogito_from_T12` under the plurality bridge `AxTwoSubjects` (`Tag: META`) — footprint `{propext, Means, Subject, Will, subjectWill, AxTwoSubjects}` — with conditional satisfiability (C354, on a `Means` inhabitant) and a `{}` countermodel for the contingency shape (C353). `[This said "a declared `Tag: SEM` datum, `AxContingentCreationObtains`" until 2026-09-27; the axiom was deleted and the lemma it lacked was found already proven — batch COSMOS-IS-PROVEN. An intermediate state made the whole claim `PROVEN↑`; the same day's COSMOS-EXISTENCE-IS-FREE split existence from meaning. It is still not an entailment from the ground, and no production is claimed.]` Creation *as entailment from the ground* remains separated and BLOCKED (`ConditionalTheology.necessary_ground_not_entails_contingent_creation`, `formal/Logos/ConditionalTheology.lean:420`, `{}` COUNTERMODEL; `formal/GAPMAP.md` Level 17, F9's entailment half). See §6c, `theorems/T30.txt`, `base.txt` §35.

### Argument

The text repeatedly says that the foundation:

- grounds all evaluative systems (`README-OLD.md:138,155`);
- is universal (`README-OLD.md:163-164`);
- is “one and universal (founds all reality)” (`README-OLD.md:253`); and
- is the source of all normativity (`README-OLD.md:258`).

These statements establish or claim a foundational relation to reality. They do not describe efficient causality, creation ex nihilo, a creative will, or a temporal beginning.

### Characteristic argued for

The foundation **grounds reality** in a transcendental or foundational sense.

### Gaps and ambiguities

- “Grounding validity” and “bringing entities into existence” are not distinguished clearly enough.
- The text uses “foundation of reality” without a theory of what reality is or how it is created.
- The word “creation” and any argument for it are absent; thus no classical creatio ex nihilo conclusion follows from the stated argument.

## 18. Pantheism as the excluded alternative

**Status in the prose:** Explicitly rejected, relying on previously alleged divine characteristics.

**Formal status (re-dated 2026-09-28): ✅ PROVEN in the identity form, with a named limit.** `formal/Logos/CosmicExistence.lean` now carries the `Universe` predicate and three claims, C429–C431, on **0 new axioms, 0 new primitives, 0 new ◈ registrations**; `Universe` is a `def` used **only in conclusions**. The reading is the only identity form well-formed over Γ's `Entity`: `Universe e := ∀ w x, ExistsAt w x → e = x` (“whatever obtains **is** e”). C429 (`no_entity_is_identical_to_the_whole`, `{NecessarySubjectKind, Subject}`) exhausts the three `Entity` constructors; C430 (`the_ground_is_not_the_universe`, `{NecessarySubjectKind, Subject}`) is that row read at the ground — the identity form fails; C431 (`grounding_never_yields_identity_of_the_totality`, `{Means, NecessarySubjectKind, Subject}`) discharges this section's stated gap below: **founded and identical are not compatible alternatives**. **Read C429 as the cheap thing it is:** it says Γ's `Entity` is an inductive with distinguishable constructors, **not** that an ontology of the universe has been philosophically adjudicated, and its witness is the same one C323 already used. **What remains out of reach, stated plainly:** the aggregate reading (“the universe is not an entity”) is **not a proposition over `Entity` at all**, so it is left *unstatable* rather than refuted, and would have to be formalized as a separate, weaker row; and the other half of §18 — realm contingency — is untouched and still BLOCKED in `SUBJECTS.md` §4.

**Prior status (re-dated 2026-09-27), retained for the audit trail: ❌ the exclusion did not follow.** The reason was no longer that nothing exists on this question. `CosmicExistence.contingent_realm_obtains` (**C350**) now **proves** the contingent realm's existence as a `PROVEN` theorem with **no bridge at all** — `{propext, Subject}`, witnessed by an atom — while its meaning is proved separately as `PROVEN↑` by `CosmicExistence.cosmos_obtains` (**C367**) under the plurality bridge `AxTwoSubjects`, Γ itself producing the meaning-bearing subject, so nothing is conditioned from outside — and the creation/countermodels batch added C351–C366 (notably C355, which refutes an absolutely empty world once a necessary entity exists, and C366, which makes creation modal-fragile where it holds). The C110 countermodel is now a **populated** world: a necessary ground that grounds every content need not produce a creation record. So the project can say *the realm exists, at a named price, and the ground does not entail it*. It still cannot say the universe is not the ground. What remains undelivered is a `Universe = Ground` identity predicate, a definition of the universe as an object, and a derivation of existence that routes from the **ground** rather than from plurality or from a bare contingency shape — note that C350 now needs no bridge, but it is also *not* derived from the ground, and its witness is an atom, which C324 explicitly refuses to identify with the cosmos. `NecessityEternity.ofGround_ne_ofSubject` (`formal/Logos/NecessityEternity.lean:133`, `{Subject}`) blocks only hypostatic identity (`ofGround ≠ EntityOf s`), not pantheism.

### Argument

The text contrasts its conclusion with pantheism:

1. Pantheism identifies the ultimate foundation with the universe or nature.
2. The universe is characterized as contingent, composite, and temporal.
3. Contingency, composition, and temporal dependence have each been excluded from the ultimate foundation.
4. Therefore, the universe cannot be the foundation and pantheism is rejected (`README-OLD.md:264`).

### Characteristic argued for

This does not add a new positive characteristic. It applies the previously argued characteristics to reject **pantheism**.

### Gaps and ambiguities

- The claims that the universe is contingent, composite, and in time are asserted in this section rather than independently derived.
- The rejection depends on the strength of the arguments for contingency, simplicity, and timelessness.
- It also relies on the ambiguous sense in which the ultimate foundation “founds all reality”; it does not specify whether founded and identical are compatible alternatives. **Now settled (C431):** they are not compatible — `GroundsEntity Entity.ofGround e → ¬ Universe e`. Note the price, which is a *consequence* of Γ's own definitions and not a new fact: the antecedent holds for **every** entity (C328), so the row's content lies entirely in the `¬ Universe e` half.

## 19. Trinity, incarnation, and biblical personal relations

**Status in the prose:** Absent as positive derivations.

**Formal status: ❌ deferred, with machine-checked independence (agrees with the prose absence).** `ConditionalTheology.preceding_theory_not_entails_trinity` (`formal/Logos/ConditionalTheology.lean:336`, `{}`), `preceding_theory_not_entails_incarnation` (`:380`, `{}`) are COUNTERMODELS; `formal/GAPMAP.md` F6/F8 DEFERRED. At most generic plurality is PROVEN↑ (`Plurality.T12_twoPersons`, `formal/Logos/Plurality.lean:45`, `{AxTwoSubjects, Means, Subject}`), not Trinitarian personhood.

### Boundary of the argument

The text invokes the traditional formula “That which is” (`README-OLD.md:258`) and refers to the “Biblical God” only to distinguish ordinary personal theism from the argument's more limited result (`README-OLD.md:262-266`). It contains no argument concerning:

- the Trinity;
- incarnation;
- revelation;
- Christ;
- the Spirit; or
- biblical personal relations.

### Characteristic argued for

None. The text explicitly disclaims those personal-theological conclusions.

### Gaps and ambiguities

- Moving from a “necessary Subject” to trinitarian personhood would require a wholly new set of premises.
- Moving from functional subjecthood to incarnation would additionally require incarnation as a concept and argument.
- The prose itself recognizes that its “personal” conclusion is not ordinary personal theism (`README-OLD.md:263,266`).

# Cross-characteristic retorsive argument

The text supplies one shared defense for many of its conclusions:

1. A critic may attempt to deny that an ultimate normative foundation is necessary (`README-OLD.md:195-199`).
2. If the criticism makes a generally valid claim, it must distinguish correct from incorrect, rely on logic, and expect its conclusions to have rational validity (`README-OLD.md:201-214`).
3. The criticism therefore already uses the normativity whose necessity it denies (`README-OLD.md:214-216`).
4. If it abandons that general validity and becomes merely local, contingent, or attitudinal, it is no longer a rationally authoritative objection (`README-OLD.md:208-216,270`).
5. The text describes this dilemma as having no stable third position (`README-OLD.md:216`).

This retorsion supports the general conclusion of a necessary foundation. It does not independently prove each of the foundation's specific characteristics; those are derived separately through the arguments summarized above.

# Strongest-to-weakest order of the prose arguments

From most explicit and developed to most allusive or unsupported, the text's argument inventory is approximately:

1. **Transcendence/externality** — repeated throughout and central to the method.
2. **Aseity/non-derived character** — direct regress argument from ultimacy.
3. **Normative sovereignty** — explicit argument from binding evaluation to source of authority.
4. **Necessity/non-contingency** — performative and transcendental argument, with important definitional ambiguity.
5. **Freedom/minimal subjecthood** — extended functional argument, but not ordinary personal theism.
6. **Unity/non-compositeness** — concise via-negationis argument.
7. **Non-conditioned/non-relative character** — concise but semantically broad.
8. **Eternity/timelessness** — concise argument from temporal succession and causation.
9. **Precedence to true/false** — explicit but underdeveloped.
10. **Universality** — supported through all-system foundationality, though thin as an independent characteristic.
11. **Simplicity** — supported partly by unity and partly by non-systemicity, with senses left conflated.
12. **Infinity and pure act** — traditional identifications rather than independent arguments.
13. **Value-source/goodness** — allusive extension from normativity, not a moral-goodness proof.
14. **Founding all reality** — implied but not a theory of creation.
15. **Omniscience, omnipotence, and benevolence** — explicitly disclaimed.
16. **Trinity, incarnation, and ordinary biblical personhood** — absent.

# Scope of the demonstrated conclusion

The strongest conclusion actually supported by the prose's own stated method is not ordinary theism but its explicitly restricted position: the existence, by transcendental necessity, of an ultimate functional foundation of normative evaluation that is non-derived, non-systemic, normative, transcendent, timeless, unconditioned, free in the minimal sense, one, and universal (`README-OLD.md:228-266`).

The text itself places firm boundaries on that conclusion:

- it does not demonstrate omniscience, omnipotence, or benevolence;
- it does not establish ordinary consciousness, will, or personal relations;
- it distinguishes its result from pantheism because the universe is taken to be contingent, composite, and temporal; and
- it describes the result as closer to **transcendental theism** or **philosophical deism** than to ordinary theism (`README-OLD.md:262-266`).

# Axiom-free proof candidates

The following audit was performed read-only against the live Lean sources and `formal/axiom_audit.json`. A literal empty footprint means that `#print axioms` reports `{}`. This is stricter than saying that a theorem has no substantive SEM/META axioms: VOCAB-only footprints and `CL` (classical logic) are called out separately.

## Existing declarations verified with literal `{}` footprints

The following declarations were checked with `lake env lean --stdin` and reported no axiom dependencies:

- `Logos.Core.greatResult`
- `Logos.Core.noBothTrueAndFalse`
- `Logos.DirectNormativeRetorsion.sig_model_c_normative_denial_is_impossible`
- `Logos.HardenedInvariance.agent_invariant_iff_agent_neutral_core`
- `Logos.HardenedInvariance.freewill_invariant_iff_freewill_neutral_core`
- `Logos.HardenedInvariance.strict_core_inclusion`
- `Logos.HardenedInvariance.agent_invariant_core_is_strictly_inside_freewill_invariant_core`
- `Logos.NecessityEternity.necessary_existence_is_stage_uniform` (C181)
- `Logos.ModalPossibilityFrontier.Aseity`
- `Logos.ModalPossibilityFrontier.model_MC21_consistent`
- `Logos.TheologicalModalHardening.necessary_existence_not_entails_uniqueness`
- `Logos.MoralFrontierAudit.epistemic_normativity_without_practical_obligation`

## Best literal-`{}` candidates

### 1. Normative sovereignty: consequence of the no-right retorsion

**Characteristic:** Normative sovereignty, in a narrow local form.

**Proved theorem:**

```lean
theorem no_correct_claim_of_no_right_can_be_true
    (sig : RetorsionSig) (s : sig.Subject) :
    SigClaimsCorrect sig s (SigNoRight sig) → ¬ SigNoRight sig
```

**Proof sketch:**

```lean
intro hClaim hTrue
exact sig_model_c_normative_denial_is_impossible sig s ⟨hClaim, hTrue⟩
```

**Reusable source:** `formal/Logos/DirectNormativeRetorsion.lean:96-111`, `:161-178`; the source audit is at `:226`.

**Footprint:** `{}`.

**Assessment:** This is now implemented and kernel-checked. It proves that the proposition denying normative right cannot be both claimed correct and true. It does **not**, by itself, establish that the ultimate foundation is normative or sovereign; that would require a further bridge from the local interpreted signature to the canonical foundation.

### 2. Non-relativity: strict agent-invariant core

**Characteristic:** Non-relativity or invariance, only in a limited architectural sense.

**Proved theorem (C180/T18):**

```lean
theorem agent_invariant_core_is_strictly_inside_freewill_invariant_core :
    (∀ l, AgentInvariant l → FreeWillInvariant l) ∧
      ∃ l, FreeWillInvariant l ∧ ¬ AgentInvariant l
```

**Proof source and reuse:** `formal/Logos/HardenedInvariance.lean:223-237`; the strictness witness and the equivalences are supplied by `strict_core_inclusion` and the two invariant/neutral-core theorems at `:117-176`.

**Footprint:** `{}`.

**Assessment:** This is now implemented and kernel-checked. It proves that the layer core admissible even in the non-agentive structural regime is a proper subset of the core admissible across all agentive regimes. It does not establish metaphysical non-relativity of the ultimate foundation.

### 3. Eternity: generic necessity-to-stage-uniformity transport

**Characteristic:** Eternity or timelessness, as a generic modal theorem.

**Proved theorem (C181):**

```lean
theorem necessary_existence_is_stage_uniform
    {World Stage Entity : Type}
    (ExistsAt : World → Entity → Prop)
    (At : Stage → Entity → Prop)
    (stage : Stage → World)
    (e : Entity)
    (hNecessary : ∀ w : World, ExistsAt w e)
    (hAt : ∀ t : Stage, At t e ↔ ExistsAt (stage t) e) :
    ∀ t : Stage, At t e ∧ ∀ u : Stage, At t e ↔ At u e
```

**Proof source and reuse:** `formal/Logos/NecessityEternity.lean:106-124`; the canonical corollaries remain in `:145-165`.

**Footprint:** `{}` for the generic theorem.

**Assessment:** This is now implemented and kernel-checked. It proves a clean modal transport lemma: an entity present in every world is present at every stage corresponding to those worlds, with equivalent stage occurrences. It deliberately avoids the canonical `Entity` sort, so it does not replace the existing `ofGround_eternity` results or establish metaphysical eternity. Those canonical results retain `{Subject}` footprints because they mention the vocabulary sort `Subject`.

### 4. Formalized separation: Aseity and volitional alternatives

**Characteristic:** Aseity, but as a separation theorem rather than a positive proof of divine aseity.

**Formal status: ✅ PROVEN.** The C182 declaration is present in `formal/Logos/ModalPossibilityFrontier.lean:463`; its audited footprint is `{}`.

**Recommended countermodel theorem (stronger than the original one-world sketch):**

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

**Proof sketch:**

```lean
refine ⟨Unit, Unit, Unit, fun _ _ => False,
  fun _ _ _ => False, (), ?_⟩
constructor
· intro w h
  exact h
· rintro ⟨s, a, v, u, h⟩
  exact h.1
```

**Audited footprint:** `{}` (the `#print axioms` audit is at `formal/Logos/ModalPossibilityFrontier.lean:626`); this is pure logic with no substantive axioms.

**Assessment:** C182 is now a generic countermodel: `Aseity` is compatible with the absence of every `Level3_VolitionAlternative`. Its companion C184 supplies the converse compatibility model, so together they establish two-way logical independence for the generic predicates. The existing `model_MC21_consistent` remains a separate example of compatibility between aseity and one selected alternative. `Level3_VolitionAlternative` is only `WillsAt v s a ∧ ¬ WillsAt u s a`; it has no accessibility relation, incompatibility condition, or distinct-world requirement. None of this proves aseity of `Entity.ofGround` or the ultimate foundation.

### 4a. C184 — Volitional alternatives do not imply aseity

**Formal status: ✅ PROVEN.** The declaration is at
`formal/Logos/ModalPossibilityFrontier.lean:485` and its audited footprint is
`{}` (`#print axioms` at `:627`).

```lean
theorem volitional_alternative_does_not_force_aseity :
    ∃ (World Entity Subject : Type)
      (ExtDepAt : World → Entity → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (g : Entity) (s : Subject) (a : Prop) (v u : World),
      Level3_VolitionAlternative World Subject WillsAt s a v u ∧
        ¬ Aseity World Entity ExtDepAt g
```

The countermodel uses `World := Bool`, `Entity := Subject := Unit`,
`ExtDepAt := fun _ _ => True`, and `WillsAt := fun w _ _ => w = true`.
The alternative holds across `true`/`false`, while external dependence at
`true` refutes generic aseity. This is the converse half of the C182/C184
independence result; it is not a positive claim about the canonical ground.

### 5. Formalized core truth/falsity bundle

**Characteristic:** The minimum logical distinction required for evaluation, not a substantive divine attribute.

**Formal status: ✅ PROVEN.** The C183 declaration is present in `formal/Logos/Core.lean:170`; its audited footprint is `{}`.

**Recommended theorem:**

```lean
theorem rightWrong_nonempty_and_nonconflating :
    (∃ p q : Prop, T p ∧ IsFalse q) ∧
      ∀ p : Prop, ¬ (T p ∧ IsFalse p)
```

**Proof sketch:**

```lean
⟨greatResult, noBothTrueAndFalse⟩
```

**Reusable source:** `formal/Logos/Core.lean:170-176`; the `#print axioms` audit is at `:209`.

**Audited footprint:** `{}`; C183 is a mechanical bundle of C8 and C9, with no substantive axioms.

**Assessment:** C183 is mechanically safe but almost definitional because the current semantic layer uses `T p := p`. It bundles the existing explicit witnesses C8 and C9, showing that the logical core contains truth and falsity without conflating them. It is not an independent transcendental proof of God or of a new divine characteristic.

**Implementation checkpoint (2026-09-26):** batch ASIETIC-CHOICE, C259–C286 + F11 — see §6 below.

## 6. True choice, asieticity, and the refuted bare horn

**Characteristic:** *True choice* — freedom as the co-signification of the **rejected** horn, and the
`?` of the weak-choice → strong-choice step discharged. Classical in the tradition of
"malum contra malum non appetitur, nisi bonum" (Aquino ST I q. 13 a. 6 ad 2): evil is only
appetible *as* an alternative to good, which is to say the alternative must be co-signified.

**Formal status: ✅ PROVEN / ⚠️ PROVEN↑, with the frontier row 🔴 BLOCKED *and refuted*.** Module
`formal/Logos/AsieticChoice.lean`; GAPMAP level 18, C259–C286 and F11; `theorems/T28.txt`;
`base.txt` §30; `CHARS.md` §5. **Zero new axioms** — the register is unmoved at 25 declared
(VOCAB 14 / SEM 7 / META 4), and that immobility *is* the test, since every footprint comes from
`formal/axiom_audit.json`.

**What is new, positively:**

| | Result | Status | Footprint |
|---|---|---|---|
| C261 | `chooses_implies_trueChoice` — the substantive direction | PROVEN | `{Means, Subject}` |
| C263/C264 | `trueChoice_implies_choiceField`, `trueChoice_implies_freeWill` | PROVEN | `{Means, Subject}` |
| C266/C267 | `weakChoice_implies_chooses` / `weakChoice_implies_trueChoice` — **the `?`, with `ClaimsCorrect s p` written** | PROVEN↑ | `{AxJudicativeBipolarity, Initiates, Means, State, Subject}` |
| C268 | `derives_rejectedHornCoMeant` — the conditional rejected horn | PROVEN↑ | `{AxJudicativeBipolarity, Initiates, Means, State, Subject}` |
| C270/C271 | `retorsion_yields_genuine_normativity_on_its_own_content`, `retorsion_implies_rejectedHornCoMeant` | PROVEN↑ | `{AxJudicativeBipolarity, Initiates, Means, State, Subject}` |
| C275 | `doubt_implies_trueChoice` — Cartesian doubt suffices, no axiom | PROVEN | `{Means, Subject}` |
| C277–C279 | `trueChoice_exists`, `freeWill_exists`, `an_asietic_entity_exists` | PROVEN↑ | `{AxTwoSubjects, Means, Subject, Will, subjectWill}` |
| C280 | `asietic_is_true_freedom` — the thesis, vocabulary-only | PROVEN | `{Means, Subject}` |
| C286 | `asietic_summary` — master synthesis | PROVEN↑ | `{AxJudicativeBipolarity, AxTwoSubjects, Initiates, Means, State, Subject, Will, subjectWill}` |

**The disclosed weakness, stated first (D6, accepted):** C265
`strongChoice_iff_trueChoice : Chooses s p q ↔ TrueChoice s p q` is **PROVEN**, and it *removes*
from the notion. The `ContestedContent` conjunct is a **global** frame fact (C259, `{}`, from
C96), not a per-pair modality, so "true choice" adds nothing to `Chooses` beyond the existential
disjunction. Do not upgrade it to a per-pair modality.

**The frontier is refuted, not open:** F11's bare implication
`AsieticChoice.bareRejectedHornCoMeant` is a named `def` (before this batch it existed only as
prose at `Choice.lean:33-35`, under a label colliding with the `def rejectedHornCoMeant` at
`Choice.lean:247` — the *consequent*). C273 `singleContentModelRefutesBareRejectedHorn` and
C274 `bareRejectedHornCoMeant_is_not_derivable`, both `{}`, exhibit a faithful single-content model
in which the antecedent holds and the consequent does not. The load-bearing field is
**faithfulness** (`means s p → p`), not single-valuedness: from `p = ¬ p` no contradiction follows,
since `p` need not be provable; faithfulness converts `means t p ∧ means t (¬ p)` into `p ∧ ¬ p`,
which `incompatible_self_negation` forbids.

**Why that is the honest boundary.** All four of Γ's routes to `Means s (¬ p)` are `Act`-gated —
`AxJudicativeBipolarity` (premise `ClaimsCorrect s p`), `AxActPolarity` and
`AxIntentionalChoice` (premise `Act s p`; its `q` is arbitrary, never `¬ p`),
`ClaimsNormativeCorrectness` (premise `Act s p ∧ …`) — and `Doubts` is itself
`Means s p ∧ Means s (¬ p)`, hence circular. So the single upstream gap is the
**`Initiates`-existence gap** (`∃ s p, Act s p`), *not* horn-saturation: no axiom of Γ supplies an
`Initiates` witness (`ProofPresentationRetorsion.lean:95`), with countermodel
`syntactic_validity_without_subject_or_normativity` (`{}`).

**What this does not answer:** object/action deliberation, which still needs the separate
`DeliberateChoice` / `ClaimsNormativeCorrectness` route (C140/C141). What it does answer is F1b's
residue (b) at `formal/GAPMAP.md:758`, **at pinned content** — which is not the same as closing
deliberation in general.

**Assessment:** the `?` of `base.txt:460` is closed *with its premise named*, which is why
`base.txt:451`'s prohibition on the **silent** `ChoiceField → Chooses` conversion stands unchanged:
what is new is a *priced* conversion (C269 makes the price visible in the footprint), not a
weakened prohibition. `CanonicalAseity → TrueChoice` is **refuted** (C283), recorded at
countermodel grade because a later pass that "helpfully" adds the bridge breaks Γ; and the ground
is canonically aseitous but not asietic (C284) and cannot be a true chooser (C285), since `Means`
is subject-indexed (`ofGround_ne_ofSubject`).

## 6b. `AsietyFreedom`: the ground's freedom, shared — and the one step that is not a theorem

**Characteristic:** *Shared freedom of the ground* — "because of the nature of Him who grounds
reality … one then asserts `AsietyFreedom`, which gives rise to true choice and `AsietyFreeWill`,
which is shared with us by the creator." Classical in the tradition of the divine act of
creation as the communication of *life* and not merely of *existence* (the causal vs. merely
ontological grounding question of §4, on the freedom side).

**Formal status: ✅ PROVEN for the `Asiety` half, ◈ STIPULATED (META) for the transfer.**
Module `formal/Logos/AsietyFreedom.lean`; GAPMAP level 19, C287–C296; `theorems/T29.txt`;
`base.txt` §31; plan `AsietyFreedom.md`. **Zero new `axiom`s** — the register is unmoved at 25
declared (VOCAB 14 / SEM 7 / META 4). **But that immobility is *not* the test for this batch**;
see "The audit does not test this batch" below, which is the honest headline of §6b.

**What is new, positively:**

| | Result | Status | Footprint |
|---|---|---|---|
| C287 | `weakChoice_implies_asiety` — `GenuineNormativity s p q → Asiety (EntityOf s)`, **no `Act`, no `Initiates`, no `ClaimsCorrect`, no stipulation** | PROVEN | `{Means, Subject}` |
| C288 | `weakChoice_implies_freeWill` — the same step toward free will | PROVEN | `{Means, Subject}` |
| ◈ | `AsietyFreedomOfGround` — the ground's freedom *reaches* every subject (**a `def`, not an axiom**) | ◈ STIPULATED (META) | `{Means, Subject}` |
| C289 | `asietyFreedom_yields_trueChoice` | PROVEN ◈ | `{Means, Subject}` |
| C290 | `asietyFreedom_yields_asietyFreeWill` — the *"shared with us by the creator"* step | PROVEN ◈ | `{Means, Subject}` |
| C291 | `asietyFreeWill_yields_trueChoice` | PROVEN ◈ | `{Means, Subject}` |
| C292 | `asietyAloneDoesNotYieldTrueChoice` — asiety alone yields no true choice | INDEPENDENT `{}` | `{}` |
| C293 | `frameContingencyDoesNotBindAPair` — pins §6's global-`ContestedContent` collapse | INDEPENDENT `{}` | `{}` |
| C294 | `rightWrongFactYieldsNoChooser` — **no axiom-free existence of a chooser** | INDEPENDENT `{}` | `{}` |
| C295 | `groundIsNotASharerOfAsietyFreeWill` — C285 preserved, by `ofGround_ne_ofSubject` | PROVEN | `{Means, Subject}` |
| C296 | `asietyFreedom_summary` — master synthesis | PROVEN ◈ | `{Means, Subject}` |

**The disclosed weakness, stated first: the audit does not test this batch.** C287/C288 are
genuinely axiom-free, and the register's immobility would have caught a new `axiom` — as it did
in §6. But the batch's one substantive input, `AsietyFreedomOfGround`, is a **`def`**, so
`#print axioms` cannot see it at all, and its reported `{Means, Subject}` footprint is
vocabulary-only *whether the bridge is principled or arbitrary*. The ◈ registry entry
(`formal/Logos/Stipulations.lean`, 5th entry) and the step-by-step block in `README.md` are
therefore **load-bearing rather than decorative**: they are the only places the price is
visible. This is a limitation of the instrument, declared rather than exploited.

**Why the bridge cannot be derived — three independent blocks.** (i) `GroundsEntity` is
**vacuous**: `EntityMeans Entity.ofGround p` reduces to `True`, so `ground_grounds_every_entity`
is `intro p _; exact True.intro` (`LovesAsGround.lean:194`) and the ground grounds even
meaningless entities (`ground_grounds_the_meaningless`). (ii) The only non-vacuous grounding
predicate, `GroundsRightWrong`, is **definitionally** `∃ p q, Chooses s p q` (C168) — already
collapsed to free will, with no Ground content. (iii) The substantive grounding relation is
`BLOCKED` with a named lemma (C228). Hence: declared, priced, and registered.

**No dishonest definitions (the R1 test).** `AsietyFreeWill s := AsietyFreedomOfGround ∧
Asiety (EntityOf s)` does **not** make `TrueChoice` a conjunct of the proposition that is
supposed to *yield* it, so C290/C291 are not projections of their own conclusion. What they do
conjoin is ground-*participation* with subject-*asiety* — two different things. A fourth
theorem, `creator_shares_asietyFreeWill`, was written and **deleted as a duplicate**: it was
literally C290 again, and one inference gets one ledger id.

**Why the existence half is conditional, not asserted.** `Core.rightWrongDistinction :
¬ N_T ∧ ¬ N_F` (`Core.lean:145`, `{}`) is a fact about **contents**: it quantifies only over
`p : Prop` and mentions no `Subject`. C294 exhibits a meaning-vocabulary in which **no subject
means anything**, so the fact is compatible with there being no chooser. The Creator step is
therefore stated conditionally, and its existence half is recorded as **not derivable** — the
unconditional route remains `AxTwoSubjects` (META) at C277–C279.

**Also not claimed.** (i) The universal reading of the bridge is **strictly stronger** than the
existential one ("the ground's freedom is shared with *someone*"), and nothing here shows the
stronger reading is the correct one — C292 is what makes the difference visible.
(ii) The `GroundsEntity` premise of the three transfers is **vacuous**; it is named `_hG` and
declared vacuous in the docstrings rather than quietly dropped, so a `{Means, Subject}` footprint
cannot be mistaken for depth. (iii) The Act-free `?` of `base.txt:460` is **bypassed, not
closed**: C287 starts from a hypothesis that already contains both horns, and the bare
`ChoiceField → Chooses` form stays machine-refuted (C273/C274). (iv) The ground is **not** a
chooser (C295 = C285): it *reaches* subjects, it is not one of them.

**Assessment:** this closes the author's chain in the only shape Γ currently pays for — the
`Asiety` step honestly, the Ground step as a priced META declaration. The characteristic to
argue for next is **not** another transfer but the *substantive* grounding relation behind
(C228); every further transfer would multiply a price already paid.

## 6c. `GroundLoves`: the ground as lover — and the two prices that claim pays

**Formal status: ⚠️ AXIOMATIC (AxGroundLovesContingentRealm) — see the 2026-09-27 notes
below; ❌ the `GroundLoves → Loves` transfer is unstatable, not merely unproved (C348);
C228 / bridge #9 untouched.**

Modules `formal/Logos/LovesAsGround.lean` and `formal/Logos/CosmicExistence.lean`;
GAPMAP Level 21, C322–C354 + 4 `—` display rows; `theorems/T30.txt`; `base.txt` §35.
**No new `axiom` was declared** — the register is unmoved at 25 (VOCAB 14 / SEM 7 / META
4). The three prices below already existed and were invisible to every reader-facing
artifact; this batch makes them visible. That is criterion 5 of §0 of `IMPROVE.md`:
no machine-verified theorem is invisible to the ledger.

The claim, in the shape the author asked for: `poem.txt:24`'s "Amar é escolhido e também
é necessário" is now **occupied as a kind-claim about the ground** by
`the_ground_is_a_necessary_and_chosen_lover` (C343). The asymmetry is the honest content:
the *necessary* half is `ofGround_necessary` (`trivial`, ontology-forced — see the C321
precedent of the §6 unicity disclosure, where the forced half was likewise disclosed
rather than celebrated); the *chosen* half is **exactly**
`AxGroundLovesContingentRealm` and nothing else — no axiom of free choice is hidden, and
`AxTwoSubjects` is not consumed here.

Two prices, different in kind, and confusing them is the mistake the kernel audit cannot
catch:

| # | Price | Status | Footprint |
|---|---|---|---|
| 1 | `GroundBearsGood : Entity → Entity → Prop → Prop` — **vocabulary** (`Tag: VOCAB`). A primitive directional good, because the library's grounding vocabulary expresses only undirected sufficiency (`GroundsEntity`, vacuously satisfied, C326/C328), the one content predicate (`EntityMeans`) is a *capacity of the target*, not an attitude of the bearer, and `Good s (_a)` is `Subject`-indexed while the ground provably is no `Subject` (C344). Satisfiable by any interpretation including constant-`False`. **Rejecting it rejects the relation's content, not the theory.** | ◆ AXIOM | `{GroundBearsGood, Subject}` |
| 2 | `AxGroundLovesContingentRealm` — **substance** (`Tag: META`). A necessary ground bears a directional good toward every contingent realm bearing content of its own. *Not derivable*: the primitive constrains nothing, and universal grounding carries no directed content from which love could follow. Consistency model: interpret `GroundBearsGood` as `False` everywhere — vocabulary, reality-hook and every per-constructor `Divine*` theorem hold, every inhabitant fails. And not a triviality: not satisfied by `True` (actual, distinct, meaningful target; directional good). | ◆ AXIOM | `{AxGroundLovesContingentRealm, GroundBearsGood, Means, Subject}` |

A third price from the sibling module was **not** created here and has since been
**retired** `[2026-09-27]`: `AxContingentCreationObtains : CreatedRealm` (`Tag: SEM`,
formerly C350) is gone. The claim was then split in two, and the price now falls where it
belongs:

- the realm's **existence** is the **free** theorem `contingent_realm_obtains` (**C350**,
  `PROVEN`, `{propext, Subject}`) — **no price at all**;
- the realm's **meaning** is the theorem `cosmos_obtains` (**C367**, `PROVEN↑`), whose price
  is the plurality bridge `AxTwoSubjects` (`Tag: META`) — shared with C351/C352, so this
  table's two rows and C367 rest on a common footing rather than on an independent semantic
  datum.

So this table's rows are now supported without a third axiom, and rejecting
`AxTwoSubjects` costs the cosmos its content-bearinghood but **not** its existence.

The reductio that once forced the datum is real but narrower than it was stated: the
reality-hook is unconditional in content (`RealityHookAudit.lean:85`), so the route
`(∃ s, Correct s p) → p` would indeed make the judging subject's own claims necessary — the
outcome `poem.txt:26` denies. But the route that actually derives C350 **never touches
`Correct`**: `Realm.bears_meaning` is a *capacity*, and `Realm.contingent` asserts modal
fragility. So the reductio does not apply, and it could not sustain an axiom.

Net effect on the ledger: *existence* moved from the faith zone to the **plurality**
commitment — a genuine narrowing, but not a free one. Purpose and the incarnation do not
follow.

What this batch is **mostly**, and why that is the finding:

| Row | Content | Why it matters |
|---|---|---|
| C336 `grounding_reaches_what_love_cannot` | The separation in one statement: grounding reaches an atom, love does not | The machine-checked content of "not *merely* a mathematical ground" |
| C338 `meaningful_love_bridge_is_refuted` | The unrestricted bridge — the stronger, more attractive form — is **false** | The *only* machine-checked justification for the axiom's meaning hypothesis; the module **declines** the attractive form rather than quietly stating the weaker one |
| C346/C348 | `Loves` and `GroundLoves` are provably disjoint; the transfer is **unstatable** | No route from the ground's love to a created person exists here; bridge #9 (C228) stands exactly as it was, so F3, F6/Trinity and the personal-monotheism frontier do not move |

Limits that belong to the row, not to a footnote:

- C330 (`necessary_entities_are_ground_or_necessary_kind`; was `only_the_ground_is_necessary`,
  re-scoped 2026-09-28, two-kinds) is **forced by the three-constructor ontology** for its
  ground disjunct (`EntityExistsAt w .ofGround := True` is definitional) and is **not evidence that the
  ground loves**; its legitimate content is now positive (the "necessary ∧ chosen" cell
  is occupied — by the ground and the necessary kind), with the contingent person's exclusion
  (C329, kind-relative) carrying the old negative content. The footprint (`{NecessarySubjectKind, Subject, propext}`) confirms no love content.
- C336's footprint is `{GroundBearsGood, Means, Subject}` — it already *consumes* the
  VOCAB primitive, so it is substantive-axiom-free, not axiom-free in the strict sense
  (the same regime as `Means`).
- C353 (`perfect_universe_has_no_contingent_realm`, `{}`) is a countermodel on an
  **unrelated free structure, not a model of Γ** (`CosmicExistence.lean:206-210`); it says
  nothing about Γ's worlds.
- C354 (`cosmos_presence_model`) is satisfiability **conditional on an inhabitant of
  `Means`**, and it is *not* claimed that the datum's negation is consistent with all of
  Γ — a model-theoretic statement over the whole theory, not built here.
- The PROVEN↑ badge names **only the substantive axiom**: `GroundBearsGood` does not
  appear in the `(AxGroundLovesContingentRealm)` parenthetical because
  `footprint_parts` files it under the vocabulary baseline. The `LOVE chain, step by
  step` block in the generated `README.md` is therefore load-bearing, not decorative —
  it is the only place the VOCAB price is visible.

## Important blockers and separations

- **Transcendence:** No theorem establishes externality to every formal or evaluative system. The quantifier-swap route remains BLOCKED in `formal/GAPMAP.md:433`; the Gödel/Tarski/Turing pattern is not formalized.
- **Canonical eternity:** Existing `NecessityEternity` corollaries carry `{Subject}` (`formal/GAPMAP.md:52-69`). C181's generic empty-footprint transport does not automatically produce an empty-footprint canonical-ground theorem.
- **Unity:** `TheologicalModalHardening.necessary_existence_not_entails_uniqueness` (`formal/Logos/TheologicalModalHardening.lean:406-414`, `{}`) is a countermodel showing that necessary existence does not entail uniqueness. `universal_ground_unique` remains deferred.
- **Freedom and personhood:** Relevant positive results have `{Means, Subject}` or larger footprints. The weak-choice → strong-choice step is now **PROVEN↑ under a named premise** (`ClaimsCorrect s p`, via `AxJudicativeBipolarity`) and the bare rejected horn is **refuted** (C273/C274), so the remaining gap is the `Initiates`-existence gap; the existence of true choice is **PROVEN↑** but not `{}` (it carries `{AxTwoSubjects, Will, subjectWill}`). Substantive personhood remains separated from the minimal definitional subjecthood. See §6.
- **The ground's freedom reaching subjects (batch ASIETY-FREEDOM):** the `Asiety` half is **axiom-free** (C287/C288, `{Means, Subject}`, no `Act`), but **every transfer from `AsietyFreedom` onward is ◈ META** (C289–C291, C296) and the bridge is a `def` that `#print axioms` cannot see — so the immobility of the register is **not** a test for this batch. There is **no axiom-free existence of a chooser** (C294 `{}` refutes it), the `GroundsEntity` premise is **vacuous**, and the ground is still **not** a chooser (C295 = C285). See §6b.
- **Moral goodness:** `MoralFrontierAudit.moral_good_obtains` carries `Logos.Value.AxBenevolentBearingObtains`; epistemic normativity does not imply practical obligation (`formal/Logos/MoralFrontierAudit.lean:179-183`).
- **Omniscience and omnipotence:** These have only local frontier definitions or models and no bridge to the canonical foundation.
- **Simplicity, pure actuality, and divine attribute bundles:** No substantive source predicates or missing bridges justify new positive claims.

## Documentation discrepancy resolved

The former statement in §2 that no live `Aseity` declaration existed was stale. The current source contains:

- Definition: `formal/Logos/ModalPossibilityFrontier.lean:122-124`
- Audit footprint: `formal/axiom_audit.json:5023`, `[]`
- Compatibility model: `formal/axiom_audit.json:5068`, `[]`

The definition must not be confused with a positive theorem about the canonical ultimate foundation: it is a generic predicate over an arbitrary world, entity, and external-dependence relation. C181 is likewise a generic modal transport theorem, not a canonical divine-eternity theorem.
