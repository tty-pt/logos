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

### Gaps and ambiguities

- “External” is not defined. It shifts among logical, ontological, hierarchical, and possibly causal senses.
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

**Formal status: ✅ datum-conditional, no substantive axioms.** `Core.rightWrongDistinction` (`formal/Logos/Core.lean:145`, `{}`) PROVEN; `PersonalNormativeGround.person_grounds_right_wrong` (`formal/Logos/PersonalNormativeGround.lean:373`, `{Means, Subject}`) PROVEN; headline `PersonalGroundOfReality.the_person_supports_the_reality_of_right` (`formal/Logos/PersonalGroundOfReality.lean:150`, `{Initiates, Means, State, Subject, CL}`) PROVEN; reality-hook `RealityHookAudit.content_reality_hook` (`formal/Logos/RealityHookAudit.lean:85`, `{Initiates, Means, State, Subject}`) PROVEN. The new local retorsional corollary `DirectNormativeRetorsion.no_correct_claim_of_no_right_can_be_true` (`formal/Logos/DirectNormativeRetorsion.lean:174`, `{}`) is also PROVEN. Boundary: unconditional `¬NoGN` is underivable (`M_inanimate`, `formal/GAPMAP.md` C167, `{}`); the broader theorems are conditional on the judicative datum/stance, with `CL` only.

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

**Formal status: ✅ PROVEN (Foundational Unicity; Aquinas ST I q. 11 a. 3); ⊨ SEPARATED (Numerical Unitarianism); ⏸ DEFERRED (Strict Monotheism branch).**
Formalized in `Logos.FoundationalUnicity` (`formal/Logos/FoundationalUnicity.lean`):
(1) Master Metaphysical Theorem: `universal_ground_unicity` (C207, `{CL, Means, Subject}`), proving that two distinct entities cannot both be universal modal grounds under asymmetric grounding;
(2) Concrete Atom Exclusion: `no_atom_is_universal_modal_ground` (C208, `{Means, Subject}`), proving no atomic factual state can be a universal ground;
(3) Discriminating Subject Exclusion: `no_discriminating_subject_is_universal_modal_ground` (C209, `{Means, Subject}`), proving no finite subject can be a universal ground;
(4) Sole Universal Ground: `ofGround_sole_universal_ground` (C210, `{Means, Subject}`), proving `Entity.ofGround` is the unique universal ground candidate in Γ;
(5) Master Synthesis: `ofGround_foundational_unicity` (C211, `{CL, Means, Subject}`, 0 substantive axioms);
(6) Metatheoretic Independence: `unicity_does_not_force_unitarian_monad` (C212, `{}`), proving that foundational unicity does not force a solitary, relationless monad, keeping the Trinitarian frontier open;
(7) Ontological Transcendence: `unicity_strictly_transcends_world` (C213, `{Subject}`), confirming that the unique ground strictly transcends the world.
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

- The text does not distinguish timelessness from everlastingness.
- “Precedence” could mean logical, ontological, or temporal priority.
- The premise that temporal existence necessarily implies submission to causality is asserted rather than argued (`README-OLD.md:161`).
- Immutability: Formally established in `Logos.DivineImmutability` (`formal/Logos/DivineImmutability.lean`, C197–C201). `ofGround_divine_immutability` proves Classical Divine Immutability (Aquinas *ST* I, q. 9) via modal invariance (`ofGround_modal_invariance`, `{Subject}`), stage invariance (`ofGround_stage_invariance`, `{Subject}`), process invariance (`ofGround_transition_invariance`, `{Initiates, State, Subject}`), and capacity invariance (`ofGround_capacity_invariance`, `{Means, Subject}`), with footprint `{Initiates, Means, State, Subject}` (0 substantive axioms). The countermodel `contingent_entity_fails_immutability` (C197, `{}`) confirms that contingent entities fail immutability. Honest boundary: this establishes modal, temporal, process, and capacity unchangeability in Γ; it does not claim psychological impassibility (which is explicitly separated in the attributes table as `❌ NOT ESTABLISHED`, with Γ affirming the eternal relation of love in T14).
- The claim that the universe is contingent, composite, and temporal is assumed in the pantheism objection rather than derived there (`README-OLD.md:264`).

## 9. Precedence to the true/false distinction

**Status in the prose:** Explicit, although its relation to later logical and temporal precedence is not fully explained.

**Formal status: ❌ absent — no precedence-to-truth/falsity theorem.** Nearest live results establish the distinction (`Core.rightWrongDistinction`, `formal/Logos/Core.lean:145`, `{}`) and its personal ground-type (`PersonalNormativeGround.person_grounds_right_wrong`, `formal/Logos/PersonalNormativeGround.lean:373`, `{Means, Subject}`), not logical/ontological precedence of the ground to the distinction.

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

- The meaning of “precede” is left undefined.
- The argument does not explain how the same foundation can precede the distinction and serve as its active discriminator.
- The relation between precedence over evaluation and precedence over time is not articulated.

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

**Formal status: ❌ absent — no act/potency or pure-act formalization.** No `PureAct`/`ActusPurus`/`Potentiality` declaration in `formal/Logos/*.lean` or `formal/GAPMAP.md`.

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

**Formal status: ❌ not established (agrees with the prose disclaimer).** `Omniscience_AllTruths` / `Omniscience_Counterfactuals` (`formal/Logos/DeepModalFrontier.lean:313` / `:317`, `{}`) are frontier vocabulary definitions, not theorems; generated `README.md` corroborates "Omniscience ❌ NOT ESTABLISHED".

### Boundary of the argument

The text says that the conclusion does not demonstrate ordinary omniscience, because “personal” has been defined only functionally and does not establish consciousness, knowledge, or ordinary personal attributes (`README-OLD.md:179-187,262-266`).

### Characteristic argued for

No classical omniscience argument is supplied. Knowledge of all truth does not follow merely from being the condition of truth.

### Gaps and ambiguities

- To derive omniscience, one would need a bridge from normativity to knowledge and a proof that the foundation possesses unrestricted knowledge.
- The text explicitly draws the boundary against such an inference (`README-OLD.md:263`).

## 15. Omnipotence

**Status in the prose:** Explicitly disclaimed.

**Formal status: ❌ not established (agrees with the prose disclaimer).** No omnipotence theorem in `formal/Logos/*.lean` or `formal/GAPMAP.md`; generated `README.md` corroborates "Omnipotence ❌ NOT ESTABLISHED".

### Boundary of the argument

Founding the conditions of evaluation is not identified with causal power over every possible state of affairs. The text's claims concern foundational and normative priority, not the ability to bring about any contingent being (`README-OLD.md:263,266`).

### Characteristic argued for

No omnipotence argument is supplied.

### Gaps and ambiguities

- A derivation would require at least a bridge from ultimate normative foundation to creative or causal power.
- Universality of scope does not establish ability to produce every possible state of affairs.
- The text expressly declines to derive omnipotence (`README-OLD.md:263`).

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

**Formal status: ✅ thin/foundational grounding only; ❌ creation ex nihilo.** `NecessityEternity.ofGround_ground_of_reality` (`formal/Logos/NecessityEternity.lean:118`, `{Means, Subject}`) PROVEN definitionally, and `PersonalGroundOfReality.person_grounds_normative_order` (`formal/Logos/PersonalGroundOfReality.lean:117`, `{Means, Subject}`) PROVEN for grounding correctness *about* reality (not causing existents). Contingent creation is DEFERRED (`formal/GAPMAP.md` F9) and separated: `ConditionalTheology.necessary_ground_not_entails_contingent_creation` (`formal/Logos/ConditionalTheology.lean:420`, `{}` COUNTERMODEL).

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

**Formal status: ❌ the exclusion is not formally established.** No pantheism/universe-contingency/composition theorem exists; the premises the prose exclusion relies on (contingency, simplicity, timelessness of the universe vs. ground) are not derived. `NecessityEternity.ofGround_ne_ofSubject` (`formal/Logos/NecessityEternity.lean:133`, `{Subject}`) blocks only hypostatic identity (`ofGround ≠ EntityOf s`), not pantheism.

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
- It also relies on the ambiguous sense in which the ultimate foundation “founds all reality”; it does not specify whether founded and identical are compatible alternatives.

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

**Implementation checkpoint (2026-09-25):** C182, C184, and C183 are now implemented, audited, and recorded in `formal/GAPMAP.md`. C182/C184 establish only generic two-way non-entailment between aseity and a Level-3 volitional alternative; C183 closes the truth/falsity logical bundle. No positive divine characteristic follows from these results.

## Important blockers and separations

- **Transcendence:** No theorem establishes externality to every formal or evaluative system. The quantifier-swap route remains BLOCKED in `formal/GAPMAP.md:433`; the Gödel/Tarski/Turing pattern is not formalized.
- **Canonical eternity:** Existing `NecessityEternity` corollaries carry `{Subject}` (`formal/GAPMAP.md:52-69`). C181's generic empty-footprint transport does not automatically produce an empty-footprint canonical-ground theorem.
- **Unity:** `TheologicalModalHardening.necessary_existence_not_entails_uniqueness` (`formal/Logos/TheologicalModalHardening.lean:406-414`, `{}`) is a countermodel showing that necessary existence does not entail uniqueness. `universal_ground_unique` remains deferred.
- **Freedom and personhood:** Relevant positive results have `{Means, Subject}` or larger footprints. Unconditional existence of free will is blocked on the rejected-horn lemma, and substantive personhood is separated from the minimal definitional subjecthood.
- **Moral goodness:** `MoralFrontierAudit.moral_good_obtains` carries `Logos.Value.AxBenevolentBearingObtains`; epistemic normativity does not imply practical obligation (`formal/Logos/MoralFrontierAudit.lean:179-183`).
- **Omniscience and omnipotence:** These have only local frontier definitions or models and no bridge to the canonical foundation.
- **Simplicity, pure actuality, and divine attribute bundles:** No substantive source predicates or missing bridges justify new positive claims.

## Documentation discrepancy resolved

The former statement in §2 that no live `Aseity` declaration existed was stale. The current source contains:

- Definition: `formal/Logos/ModalPossibilityFrontier.lean:122-124`
- Audit footprint: `formal/axiom_audit.json:5023`, `[]`
- Compatibility model: `formal/axiom_audit.json:5068`, `[]`

The definition must not be confused with a positive theorem about the canonical ultimate foundation: it is a generic predicate over an arbitrary world, entity, and external-dependence relation. C181 is likewise a generic modal transport theorem, not a canonical divine-eternity theorem.
