/-!
Meanings (EN) for prose claims that have no kernel declaration behind them
(some are deferred/faith rows, some resolve to a spike file outside `Logos/`,
and some are retired/blocked steps under hostile semantics).

These are "def strings": each meaning is the literal value of a `String`
constant, so every English sentence consumed by `README.md` lives in code
and needs no external gloss file.
-/
namespace Logos.ClaimMeanings

def F1b : String := "Existence of genuine choice and free will is closed (PROVEN↑) under the substantive semantic constitutive principle AxIntentionalChoice (∀ s p, Act s p → ∃ q, Chooses s p q): an intentional act is an initiation performed through the subject's apprehension of an incompatible alternative. Together with the performative act datum, this derives genuine choice (genuineChoice_exists_of_act_constitutive) and free will (freeWill_exists) under footprint {AxIntentionalChoice, Initiates, Means, State, Subject}. The stronger contradictory-negation polarity bridge AxActPolarity (Act s p → Means s (¬p)) strictly implies AxIntentionalChoice via act_polarity_implies_intentional_choice, while pre-A14 independence is preserved (act_orthogonal_to_genuine_choice_in_full_theory)."

def F2 : String := "Deontic teleology is deferred: how norms point at goals is not yet derived."

def F3 : String := "Moral good from logical normativity is machine-separated from practical bindingness: the faithful model M_amoral satisfies epistemic agential normativity with zero practical obligation (epistemic_normativity_without_practical_obligation, C175, {}), so normativity alone never forces a moral pole. The positive close is nevertheless earned honestly (C176-C178): the bare value layer is machine-proven empty (BearingOf is a closed def, so Helps/Harms/Affects are refutable for every pair — no_help_obtains, C176), so the moral pole is a FAIR DEFINITION (Good := helpfulness toward the other: some distinct person is helped and none is harmed) whose INHABITATION rests on ONE disclosed, tagged, priced META bridge AxBenevolentBearingObtains (some person is actually helped, C177). Good obtains under that bridge (moral_good_obtains, C178, PROVEN↑); the definition itself is vocabulary-only, so nothing is smuggled — only the existence of benevolence in the world is declared, and declared openly. The negative pole Evil remains a declared SEM datum (its fair reading is uninhabited without a parallel 'some harm occurs' bridge)."

def F4 : String := "There are two distinct persons, both lovable, under the two-subjects bridge."

def F5 : String := "Eternal loveship is proven: two distinct persons stand in an eternal love-relation, under the bridges and person-stability."

def F6 : String := "The Trinity is deferred: no argument exists yet."

def F7 : String := "F7 (free will under AxActPolarity) is DERIVED / DISSOLVED into F1b: A13 strictly implies A14 (act_polarity_implies_intentional_choice), closing free will via genuineChoice_exists_of_act_constitutive. AxActPolarity itself remains an optional stronger SEMANTIC principle, while world-level ChoiceAt remains an independent future SEM vocabulary."

def F8 : String := "The Trinity is not attempted."

def F9 : String := "Incarnation and creation are faith data from the poem, deferred."

def F10 : String := "Causal (creative) omnipotence — the power to BRING a state of affairs about, as against being present where it obtains — is BLOCKED, and the prose disclaimer is retained for this causal sense alone, since the non-contradictory sense of omnipotence is now PROVEN (C242, the ground operates every satisfiable state of affairs, and C251, that scope domain is non-empty and contradiction-free). Γ declares no entity-level production relation: its only initiation relation, Agency.Initiates : Subject → State → State → Prop → Prop, is subject-indexed, and Entity.ofGround is provably not a subject correlate (ofGround_ne_ofSubject), so the ground cannot instantiate it at all. The closest relation Γ has is explanatory containment (GroundsEntity), and exhaustive_scope_without_operative_scope already machine-checks that an exhaustive scope does not entail an operative one, so the causal sense must not be weakened to it. Two exact statements are missing, in this order: (1) the vocabulary, a production relation Produces : Entity → World → Form → Prop; and (2) the derivation, that the ground produces every satisfiable state of affairs."

def Q7_2 : String := "Research question, answered: the swap is a theorem for atoms (no axiom needed); the compound instance is unforced."

def F1bUncond : String := "The unconditional existence claim ∃ s, FreeWill s is BLOCKED, as the companion row to F1b (the conditional/closed front). Corrected by the ASIETIC-CHOICE batch (2026-09-26): the missing datum is the IMPLICATION, now named bareRejectedHornCoMeant, not merely its consequent (see F11). F1b itself is already PROVEN↑ by the retorsion route, and the batch adds a second, pinned-content route (retorsion_yields_genuine_normativity_on_its_own_content) answering residue (b) at GAPMAP.md:758; what remains untouched is object/action deliberation, which still needs the separate DeliberateChoice / ClaimsNormativeCorrectness route (C140/C141)."

def EvalSettlement : String := "Executive settlement (executive Choice/Selects/FreeAgency) is proven independent of deliberative Chooses with no bridge axioms — separated by M_det (ExecutiveDeliberativeFrontier Track A–H). CommittedChoice bundles settlement via the Act conjunct but derives no executive causation or sourcehood; ContemplatesWithoutSettling still implies FreeWill."

def OpenBridgeNormativity : String := "The positive bivalence→normativity bridge (∀ s p, Judge s p → GenuineNormativity s p (¬p), or stand-antecedent variant) is BLOCKED: bivalence alone is insufficient (M_inanimate, C167); the weak-voice route C106 closes it at SEM cost AxJudicativeBipolarity (independent via M_opaque, dispensable); the axiom-free full-stance route C164/C165 needs the stance datum; unconditional ¬NoGN is not derivable."

-- Retired / blocked claims under hostile semantics

def C78 : String := "Contingent ground is retired: manufactured witness destroyed under hostile semantics."

def C79 : String := "Ultimate ground existence is blocked: infinite descending chains have no ultimate element without a well-foundedness axiom."

def C87 : String := "Origin necessity is retired: manufactured origin witness destroyed."

def C89 : String := "Ultimate ground by initiation is blocked: non-entailed without well-foundedness."

def C90 : String := "Personal ultimate ground is blocked: ultimate grounding does not entail personal nature."

def C69 : String := "Free will of origin is retired: manufactured constructor split destroyed."

def C70 : String := "Posited content non-freedom is retired: manufactured witness destroyed."

def C71 : String := "Origin freedom denial self-refuting is retired: manufactured witness destroyed."

def C72 : String := "Judge is free is retired: act does not entail free will; `judge_commits` yields only the choice field."

def C73 : String := "Plurality without bridges is blocked: unit countermodel settles that 1 act does not entail plurality; requires AxTwoSubjects."

def C75 : String := "Propositional personhood is blocked: content existence does not entail personhood."

def C76 : String := "Canonical rigid love is retired: plurality does not entail love without substantive relational bridges."

def C88 : String := "Transcendental quantifier swap is retired: the manufactured origin quantifier swap was destroyed under hostile semantics; the declaration is absent from the live kernel."

def C77 : String := "Conditional necessary-person claim is deferred: the theorem Love.necessaryPersonExists_conditional was removed from the live kernel (commit ae7f4bd); retained as annotated conditional surface only, never a derived divine Person."

def C92 : String := "Conditional necessary-entity claim is deferred: the theorem Love.necessary_entity_exists_conditional was removed from the live kernel (commit ae7f4bd); retained as annotated conditional surface only."

def C64 : String := "Movement not transfer is retired: initiation constructor evaluation excised."

def C65 : String := "Person iff originates is retired: manufactured initiation identity excised."

def C66 : String := "Cogito as initiation is retired: manufactured initiation witness excised."

def C67 : String := "Denial of initiation self-refuting is retired: manufactured witness excised."

def C80 : String := "Posited content deterministic transfer is retired: constructor evaluation excised."

def C81 : String := "Origin branching is retired: constructor evaluation excised."

def C82 : String := "Origin initiating person is retired: constructor evaluation excised."

def C102 : String := "NoRight is the universal skeptical thesis asserting that no genuine normative correctness judgment exists."

def C103 : String := "Claiming NoRight as correct while NoRight is true produces a strict, constructive contradiction."

def C104 : String := "No agent can claim NoRight as correct if NoRight is true."

def C105 : String := "If any agent actually performs a normative correctness claim on NoRight, the thesis NoRight is strictly false."

def C106 : String := "Asserting p as correct constitutively instantiates genuine normative governance between p and ¬p for subject s under AxJudicativeBipolarity."

def C107 : String := "The shortest complete master proof: Genuine Normativity derives Choice and Free Will."

def C108 : String := "Neutral formalization of Trinitarian structure: exactly three distinct personal centers sharing divine status."

def C109 : String := "Binitarian separation model: the existing theory is fully consistent with a Binitarian reality and does not entail a Trinity."

def C110 : String := "Separation model, on a POPULATED world: a necessary ground that grounds every content may still create nothing, so the necessary ground does not entail a creation record. The separating world provably contains a genuinely contingent subject, and its positive counterpart provably does carry a record, so the entailment is undetermined in both directions. NOT an empty world, NOT a model of Gamma, and NOT a claim that the contingent world does not exist -- that existence is a proved theorem, cosmos_obtains (C350), derived from the plurality bridge."

def C111 : String := "Neutral formalization of Incarnational structure: expresses the teleological union of divine and human nature in a single personal subject."

def C112 : String := "Unincarnate hostile model: the existing theory is completely consistent with God remaining purely transcendent and unincarnate."

-- Level 22 (Logos.TheologicalModalHardening): the empty-world suite. Every row below is a
-- statement about a purpose-built free structure, none of them a model of Gamma and none of
-- them a candidate for reality.

def C355 : String := "Once a necessary entity exists, no world can be absolutely empty -- the empty world is refuted, not merely set aside."

def C356 : String := "Stipulating non-emptiness as a necessary modal constraint formally excludes the empty world from the possible worlds. An exclusion by stipulation, stated as such rather than sold as a derivation."

def C357 : String := "An entity existing in no world is neither contingent nor necessary, so non-contingency does not entail necessity."

def C358 : String := "A necessary entity does not force contingent creation. The claim is per world -- there is a world at which no contingent entity exists -- and the model is not an empty world: the contingent creature exists at the actual world and is absent at another."

def C359 : String := "The model witness behind the necessary-entity separation, displayed rather than separately claimed."

def C360 : String := "The creation relation is empty in a world-rigid structure. This denies the Creates relation, not the existence of contingent entities."

def C361 : String := "The populated counterpart: a contingent entity exists while the creation relation is empty, so existence and derivation come apart in a world that is not empty."

def C362 : String := "Every world may hold an entity without any one entity holding in every world, so world-by-world non-emptiness does not entail a necessary entity."

def C363 : String := "A single-world, world-rigid structure in which nothing is contingent and nothing is created. This is a countermodel of necessity implying contingency, of the same world-rigid shape as C353; it is not a claim about reality and not a model of Gamma."

def C364 : String := "The positive regime: a necessary ground and a contingent creature with the creation relation holding. Ledgered so that the negative regime C363 cannot be read as creation being impossible."

def C365 : String := "In a two-world structure a contingent entity exists and the creation relation is empty, so the ground does not entail creation without any empty sort being needed."

def C366 : String := "Where creation does hold, it is modal-fragile: the creature is absent at a counterfactual world. The poem's 'this world is necessary? No' in machine-checkable form."

def C368 : String := "The thesis 'there is no meaning', stated in the vocabulary Gamma already uses rather than in the internal IntentionalSubject form. base.txt section 26 item 3 ('Nao existe conteudo') and poem.txt P3 ('ha significado') both say this; before this def no named NoMeaning existed anywhere in the library. It is the negative of Meaning_I, which base.txt section 11 defines as exists p, exists s, Means s p, so the subject is a constituent of the notion and the thesis is a negation of an existential over contents. Footprint {Means, Subject}. This def is the sentence section 26 item 3 asserts; it is not a refutation of it."

def C369 : String := "The thesis and the audited negation of the retorsive conclusion are the same sentence, re-indexed. NoI_canonical is the negation of P_canonical, which is exists s, IntentionalSubject s, and IntentionalSubject s is exists p, Means s p; NoMeaning is the negation of exists p, exists s, Means s p. The two differ only in the order of two existential quantifiers, so the equivalence is pure logic. Stated as an Iff and not an Equals because the formulas are not definitionally equal - the quantifiers bind in the opposite order - so an equality form would need propext and would suggest the identity is definitional. It is not; it is a re-index, and the absence of propext from the footprint is the machine-checked confirmation. This is the sentence that makes section 26 item 3 and the audited NoI_canonical visibly the same claim, which was not on record."

def C370 : String := "The pointwise reading of the thesis: no subject means anything at all. The corpus already draws this equivalence for the internal form; this is the re-index of it in the meaning vocabulary."

def C371 : String := "Rung 1 of 4. If nothing is meant, no subject means the thesis: the thesis is among the things that would have to be meant for it to be true, so it is unmeaned. This is the self-application closed at the Means rung, and it is CONSISTENT - a universal negative is not a liar, which is exactly why the diagonal does not produce a refutation here."

def C372 : String := "Rung 2 of 4. The thesis cannot be entertained as an act, because the act is the meaning-act: performing the thesis as an act already means it."

def C373 : String := "Rung 3 of 4, and NEW to the corpus. The thesis cannot be judged correct. Gamma has a Correct-rung for the act-thesis (Order.no_correct_judgment_of_no_act) and for nothing else; this is the first for any meaninglessness thesis. Judging NoMeaning correct is an act of meaning it plus a truth-claim of it; the act supplies the meaning the thesis denies and the truth-claim supplies the thesis. Pure logic, no axiom. It places the thesis outside Gamma's own epistemic criterion, F12 JudicativeGood."

def C374 : String := "Rung 3 prime, the exhaustive form mirroring Order.judgment_of_no_act_is_incorrect: whoever judges the thesis at all judges it incorrectly, so error is the only status the thesis can have as a judgment. This adds nothing over rung 3 logically - it is the same content packaged as exhaustiveness over the bivalent partition - and is landed so that the meaninglessness thesis appears in the corpus beside the act-thesis in the same two-row shape. The docstring says so."

def C375 : String := "Rung 4 of 4: THE RETORSION, unconditional. Nobody can hold the thesis as correct. No hypothesis, no subject supplied, no bridge, and no axiom beyond the declared meaning vocabulary - the footprint is vocabulary only. Asserts s p is Act s p and p, so an assertion of the thesis is at once an act meaning it, which rung 1 forbids given the thesis, and a truth-claim of the thesis, which is the thesis; either conjunct alone is fatal. This is the author's sentence in the corpus's own form: to affirm that there is no meaning is to prove the invalidity of one's own affirmation. The honest limit is that the affirmation is the INPUT that makes the contradiction, so the retorsion is free in axioms and NOT free in performance. It does not yield the unconditional negation of the thesis, which the complement C382 forbids."

def C376 : String := "The four rungs in one conjunction, for the ledger: the thesis cannot be meant, cannot be acted, cannot be judged correct, and cannot be affirmed. The last conjunct is unconditional; the first two are conditional on the thesis being true, which is what makes them consistent rather than contradictory."

def C377 : String := "The retorsion stated positively, which is the form the author asked for: to affirm that there is no meaning is itself a meaning, because affirming the thesis produces an instance of exactly what the thesis denies. The conclusion is the Meaning_I form with the content NAMED - NoMeaning itself is the proposition that comes out meaning. Generalized on 2026-09-27: the hypothesis is now Act, not Asserts, because Asserts s p is Act s p and p - the old statement is the special case, so this one subsumes it and the C-id does not change. The hypothesis is still not available in advance: C372 excludes Act s NoMeaning wherever NoMeaning holds, so the reading is the author's - whoever performs the thesis meaningfully thereby refutes it. Both theorems in this pair are implications FROM an affirmation, so neither yields the unconditional negation of the thesis; the affirmation is the thing being paid for, not something at hand."

def C378 : String := "The same at the judging level, which is the form poem.txt P3 actually uses: 'ha certo e ha errado implica ha significado'. Judging the thesis correct already exhibits a meaning, so a correct judgment of the thesis is an instance of what the thesis denies."

def C384 : String := "The performance without the success condition, and the predicate Gamma lacked: every asserts in the corpus carries a conjunction with p - asserts s p is act s p and p, Asserts s p is Act s p and p, Correct s p is A s p and T p - so the word 'assert' had come to mean 'correctly assert', and the performance it should have named had none. This names it. It is what the performative contradiction leaves standing, since the retorsion C375 refutes only the act SUCCEEDING, and it is the machine-checked sense of the author's 'it can be uttered, it can be asserted'. Built on the weak act rather than Act, because Act requires Means and C372 already excludes Act s NoMeaning wherever NoMeaning holds - an assertion-predicate built on Act could never witness the thesis being said."

def C385 : String := "The world in which the thesis IS uttered: a subject, no meaning anywhere, the thesis true, the thesis performed - and still no assertion of it that succeeds. C382's world with act set to True instead of False; the third conjunct is C379 applied to it. This is what makes C383's word 'unutterable' a misnomer rather than a reading, and it is the machine-checked content of the author's 'I have just affirmed it so it is not unuterable'. The act is weak because C372 excludes Act s NoMeaning wherever NoMeaning holds: in a world where the thesis is true the only available act of it is the weak one - saying it is not thinking it. The same instance disposes of C294's countermodel as an answer, since that lifts into this signature by setting Means to M and act to True. Standing limit: Subject is a nullary uninterpreted sort, the witness is the unit, and no axiom says a natural-language speaker is a Subject, so the theory exhibits the possibility of the utterance and cannot certify the author's."

def C379 : String := "No model of the meaning vocabulary, of any shape, can host an affirmation of the thesis: if nothing is meant, nothing affirms the claim that nothing is meant. THIS IS A COROLLARY, NOT A DISCOVERY, and its docstring says so. It is level2_signature_asserts_noi_selfRefutes generalised from one signature to all of them, and the corpus already had it for the internal NoI_canonical form. It is landed and badged because it is the sentence the author actually asked for, stated once over the signature, and because the internal form is not the form section 26 item 3 uses. The batch's novelty rests on C369, C373, C380 and C382, not on this row."

def C380 : String := "The weak retorsion, signature-general: affirming that no performed event occurs is self-refuting, because the affirmation is itself a performed event. This lifts Agency.noWeakAct_selfRefutes from Gamma's canonical vocabulary to an arbitrary signature, which is what the joint refutation needs in order to quantify over the countermodels; the canonical version was the only one on record. Empty footprint: pure logic over the signature's own act field."

def C381 : String := "The joint refutation in one sentence: a meaning-vocabulary in which nothing is meant cannot also be one in which the act-datum is denied AND that denial is then affirmed. This is what refutes the countermodel family M1 and C294 as ANSWERS, at empty footprint. The reasoning is that a countermodel is not a counterexample but a description of a world, an answer is a move made inside discourse, and a world with no moves has no answers and so cannot contain the affirmation of its own silence. M1 sets act to False as well as Means to False, so the countermodel is refuted by a denial it performs against itself. What this does NOT do is refute the countermodel as a model: see C382."

def C382 : String := "THE COMPLEMENT, and the reason the refutation above is honest rather than a trick. A world with subjects, no meaning anywhere, the thesis true, and the thesis unassertable - the exact shape of M1 with the Asserts-total-unassertability conjunct made explicit. It is CONSISTENT, and the corpus already had the weak version at unassertability_does_not_imply_falsity, but that one is built on the EMPTY subject sort, where unassertability holds vacuously. This is the populated version, and it was not on record. Three consequences, and they are the price of C379 and C381: the countermodel is refuted as an answer and not as a model; the content of the thesis stays alive and stays consistent; and the positive existence of meaning still costs AxTwoSubjects (C367) for a subject that is not supplied as input. This is also the machine-checked reason the unconditional negation of the thesis is refused, so it is a gate: if the refutation rows ever land without this one, the batch stops."

def C383 : String := "The two halves of the refutation read together as one statement: the countermodel's world is a world in which the thesis is true, and the thesis cannot be affirmed anywhere, including there. This is the honest form of the demand that the countermodel be shown wrong - wrong as an answer, in a populated world, at empty footprint, with the content itself untouched."

def C142 : String := "Personhood is constitutively equivalent to possessing a free, independently individuated will."

def C143 : String := "A personal subject with free independent will satisfies the specification of the personal ontological ground of Right/Wrong."

def C144 : String := "Personhood supplies the ontological ground-type required by objective Right/Wrong, derived directly from Personhood without Act."

def C145 : String := "Transcendental discovery of the free subject from normative polarity is logically independent of the ontological grounding bridge."

def C146 : String := "Model B proves that in bare theory, the hypothesis of a free subject does not by itself entail an external grounding relation; grounding is instead achieved via the free-will route with personalness as a priced theorem (0 substantive axioms)."

def C147 : String := "Denying Right is performatively self-contradictory: no agent can present NoRight as correct while NoRight is true."

def C148 : String := "Right and Wrong are real, and the normative order is necessary — both unconditional, zero substantive axioms. 'Right/Wrong' here denotes the objective truth-based correctness polarity (some propositions true, some false), not moral good/evil (moral good is DEFERRED, F3)."

def C149 : String := "The judicative stance forces the Person: any agent grasping a proposition as correct and as incorrect is a free subject (FreeWill), hence a Person."

def C150 : String := "Personhood supplies the ontological ground-type for all subjects without Act."

def C151 : String := "HEADLINE — The Person supports the reality of Right: deny-Right is contradictory, Right/Wrong is real and necessary, the normative datum forces the Person, and the ground required by Right/Wrong is personal in kind. 'Supports the reality of Right' = grounds the objective correctness/normativity structure governing judgments (RightWrong-reality); not a claim that the Person creates existence or legitimizes evil."

def C152 : String := "Given the performative datum (some agent actually faces Right/Wrong), there exists a personal ontological ground of Right/Wrong, and the normative order is necessary."

def C153 : String := "The derived Person instantiates the personal ontological ground of the objective normative/truth order governing judgments about Gamma-reality — grounding the correctness of propositions about what is the case, not producing what exists or approving evil (instance form of the headline)."

def F11 : String := "The bare rejected horn is BLOCKED, and now nameable: Logos.AsieticChoice.bareRejectedHornCoMeant : (∃ s : Subject, ∃ p : Prop, Means s p) → ∃ s : Subject, ∃ p : Prop, Means s p ∧ Means s (¬ p). Every non-circular route in Gamma to Means s (¬ p) is Act-gated — AxJudicativeBipolarity (premise ClaimsCorrect s p), AxActPolarity and AxIntentionalChoice (premise Act s p, and its q is arbitrary, never ¬ p), ClaimsNormativeCorrectness (premise Act s p) — while Act s p := Means s p ∧ ∃ w w', Initiates s w w' p, and no axiom of Gamma supplies an Initiates witness. So the single upstream gap is the Initiates-existence gap, NOT horn-saturation. Two discharges do work and both name their premise: derives_rejectedHornCoMeant from a correctness-judgment, and retorsion_implies_rejectedHornCoMeant from the retorsion event. The bare form is not merely unproved but REFUTED — singleContentModelRefutesBareRejectedHorn exhibits a model of the meaning vocabulary in which the antecedent holds and the consequent does not — so the blocker is a sentence false in a model, not an artefact of an unsuccessful search. Footprint and status are orthogonal: the {Means, Subject} marker on the definition is what it depends on, BLOCKED is that it is not discharged."

/-- English closed-caption gloss for frontier row F12 (consumed by scripts/build_deduction.py). -/
def F12 : String := "The justification for the ASIETY-FREEDOM stipulation is BLOCKED, in two halves that must both be closed. (1) MISSING VOCABULARY: a substantive grounding relation relating Entity.ofGround to the normative content of a subject. Gamma declares none. GroundsEntity is vacuous on the ground side, because EntityMeans Entity.ofGround p reduces to True; and the only non-vacuous grounding predicate, GroundsRightWrong, is definitionally ∃ p q, Chooses s p q (C168) — already free will, so using it as the antecedent would be circular. The substantive relation stays BLOCKED at C228, with its named lemma verbatim. (2) MISSING DERIVATION: from such a relation plus Asiety (EntityOf s), derive TrueChoice s p q at every incompatible pair, not merely the witnessing pair. C299 groundingCannotDeliverTrueChoice (footprint {}) is the machine-checked reason this cannot be discharged from a premise of containment shape: it grants the full premise — a ground of total meaning-capacity, forall v, M g v, and the containment premise at every entity, forall e v, M e v -> M g v, which is GroundsEntity verbatim — and still denies the conclusion at the same pair. So the corpus records both facts about the bridge at once: we chose to assert it, and we cannot justify it. Note the scope limit: C299 covers relations of containment shape only, so a relation of some other shape remains open work, which makes the block serious rather than permanent."

/-- English closed-caption gloss for frontier row F13 (consumed by scripts/build_deduction.py). -/
def F13 : String := "The Creator-sharing existence claim is BLOCKED, and refuted as derivable rather than open. The obligation is now nameable, following the F11 precedent: Logos.AsietyFreedom.groundFreedomSharedWithSomeone : Prop := ∃ s, AsietyFreeWill s, footprint {Means, Subject}. Sharing the ground's freedom with us contains an existence claim, and Gamma cannot supply it: Core.rightWrongDistinction is a fact about contents, quantifies over no Subject, and is compatible with a meaning-vocabulary in which no subject means anything — that is C294, whose content-vocabulary countermodel shows the antecedent holding with no subject to be shared with. The unconditional route therefore still costs AxTwoSubjects (Tag: META). Naming this advances nothing; it is recorded so that the batch's strongest negative result is a citable frontier row rather than a footnote inside a module. This def is an obligation, not a reading, and must never be badged as a stipulation: the registry stays at 5 stipulations, 25 dependents."

/-- English closed-caption gloss for frontier row F15 (consumed by scripts/build_deduction.py). -/
def F15 : String := "Foundational Unicity - the ground of reality is the SOLE universal ground, with no subject of total meaning-capacity competing with it. STATUS: RETIRED 2026-09-27 (lote SEMANTIC-FINITUDE); the bound it named was PROMOTED from a def-stipulation to a DECLARED AXIOM on 2026-09-28, so it is now the 27th axiom and its price is visible to every footprint tool. The missing lemma, verbatim, was: for every subject there is a proposition it does not mean, that is, every subject is meaning-restricted - all s : Subject, exists p : Prop, not Means s p. It was never derivable, because the meaning-predicate is vocabulary and its subject-type is a nullary uninterpreted sort (Agency.lean:49), and nothing in Gamma bounds a subject propositional reach. But it was never a new payment either: the corpus already paid it as an anonymous explicit premise across 5 attribute modules. The census is re-derived 2026-09-28 by `scripts/census_semantic_finitude.py`, which is checkable and states its method, because the earlier numbers here did neither. TWO measures, since "how many times" has no single answer: `any` = 19 (every declaration whose statement mentions the bound, in the ∀-form or the per-subject ∃-form; DivinePureActuality 5, FoundationalUnicity 6, CanonicalAseity 4, DivineSimplicity 3, AsieticChoice 1) and `forall` = 14 (only those carrying the exact F15 ∀-form: 3, 5, 2, 3, 1). Proof bodies are excluded, since an occurrence in a proof is a use of a price already paid. The earlier "20", then "19 (17 premissas + 2 campos de estrutura)", then "17" were inconsistent: the total 19 is right for the `any` measure, the per-file breakdowns behind it were wrong (FoundationalUnicity is 6 not 7; DivinePureActuality 5 not 4), and the bare 17 belongs to no consistent measure. The conclusion is robust under either measure and is what matters: Γ pays this price by FIVE distinct attribute arguments — canonical aseity, divine simplicity, divine pure actuality, asietic choice, foundational unicity. On 2026-09-27 the sentence was named SemanticFinitude (formal/Logos/SemanticFinitude.lean) and registered as a def-stipulation semanticFinitude, Tag VOCAB, in Stipulations.lean. On 2026-09-28 that entry was RETIRED (registry 8 to 7) and the bound was declared an axiom. The ten headline theorems that were conditional on an anonymous copy are keyed to the named bound as ten _stipulated corollaries: exactly_one_universal_modal_ground_stipulated (the unicity of the ground), ofGround_sole_universal_grounding_stipulated, conditional_canonical_aseity_stipulated, ofGround_modal_aseity_conditional_stipulated, ofGround_divine_pure_actuality_stipulated, ofGround_no_grounding_potency_stipulated, ofGround_divine_simplicity_stipulated, ofGround_non_composite_stipulated, ofGround_simplicity_and_transcendence_stipulated, and ground_is_canonically_aseitous_but_not_asietic_stipulated. All ten are PROVEN and, since the promotion, all ten are UNCONDITIONAL theorems of Gamma rather than theorems-conditional-on-a-hypothesis; the _stipulated suffix is historical and is kept only because GAPMAP and the prose corpus cite these names. HOW IT IS PRICED, AFTER THE PROMOTION: SemanticFinitude is a declared Tag VOCAB axiom, so it now appears in the audited #print-axioms footprint of every dependent - for example exactly_one_universal_modal_ground_stipulated is at {Means, NecessarySubjectKind, SemanticFinitude, Subject}. Before the promotion it was a def of a Prop taken as an argument, so zero new axioms were declared, every corollary footprint was byte-identical to the conditional theorem it mirrored, and the price was INVISIBLE to every footprint tool with the badge as the only signal. That is the defect the promotion removes. The axiom count DID move, 26 to 27, and its absence was the point: the old arrangement was unauditable, so the count not moving was not a test of anything. The bound is falsifiable, not vacuous: semantic_omnipotence_is_consistent (empty footprint) is a model of its negation (a semantically omnipotent carrier), so the unicity genuinely rests on it. It is also load-bearing in the other direction: semanticFinitude_excludes_ground_from_subjects shows that, since ofGround_meansAll gives the ground every proposition, the bound is exactly what keeps the ground off the Subject sort. The corollaries are no longer conditional on a named premise: declaring the bound made them unconditional, which is the whole reason for the promotion and the reason the earlier decision to leave it as a def was reversed. The ten pre-existing conditional theorems are still NOT edited (they keep the anonymous premise) and remain the axiom-free conditional forms; the corollaries are additive. The ten pre-existing conditional theorems are NOT edited (they keep the anonymous premise); the corollaries are additive. Existence of a ground was already PROVEN unconditionally (C319) and is untouched; what rests on the bound is its UNICITY, together with every divine attribute in the attribute lane. Personhood (C228), Trinity (F6/F8) and explanatory grounding (C326/C328) are untouched. Tag VOCAB says the bound restricts one uninterpreted relation on one nullary sort and asserts no connection between entities (same status as ofGround_existsAt). This is why the ten corollaries KEEP the PROVEN badge they had as stipulations: the generator treats only SEM, META and TRANS as substantive, so a VOCAB axiom yields PROVEN. SEM remains the documented fallback if a future author judges the bound a genuine semantic choice, and re-tagging would then correctly cost the ten corollaries their badge. Kept for the record: C314 shows grounding the ground IS the existing MaximalCapacity predicate, and C318 proves the bound equivalent to exclusion of maximal capacity among non-ground entities."
def F16 : String := "Divine Immutability - the substantive reading of capacity invariance, that a subject's meaning capacity is constant ACROSS WORLDS - is BLOCKED, and it is blocked for a reason no proof can repair: the claim cannot even be STATED. The meaning relation is EntityMeans (e : Entity) (p : Prop) : Prop at RecoveredOntologicalGround.lean:46, which takes no world argument at all, so there is no Entity -> World -> Prop -> Prop relation anywhere in the library and "capacity varies across worlds" has no denotation. C321 machine-checks what follows from the world-free reading: CapacityInvariance is the tautology forall p, forall w1 w2, EntityMeans e p <-> EntityMeans e p, discharged by Iff.rfl, and therefore holds for EVERY entity, subjects and atoms included. The asymmetry is the finding. All three sibling fields of DivineImmutability genuinely quantify and do discriminate - ModalInvariance over two worlds via ExistsAt, StageInvariance over two times via ExistsAtTime, TransitionInvariance as the real predicate NotInSuccession - and each has an axiom-free non-triviality countermodel on record (C197, with C192, C202 and C214 for the other attribute masters). This field has none, because there is nothing in it to refute. Note carefully that this is DISCLOSURE, NOT DEMOTION: ofGround_divine_immutability remains PROVEN and untouched; what changes is that the ledger used to state the property only where it could not fail, which read as if it carried weight. The missing statement, verbatim, is a world-indexed relation EntityMeansAt : Entity -> World -> Prop -> Prop together with a proof that some entity's meaning capacity genuinely FAILS to be world-constant, so that the invariance is a discriminator. Why it is not derivable: adding the world index is a new primitive, so the price is new vocabulary, honest-tagging it would cost SEM at minimum, and the same wall blocks F10's missing Produces relation. It is NOT added - author decision."


def C386 : String := "THE GOD-LANE, first half: the same meaning-bearing realm C367 inhabits, reached without the plurality bridge. C367 pays AxTwoSubjects because that is how cogito_from_T12 gets a subject who means; the performative act-datum gets one for free, since Act already contains Means as a conjunct, so act_datum_implies_means turns 'someone acted' straight into 'someone means' with no bridge at all. This is a NEW ROW and not a re-anchoring of C367, and it does not replace it: a theorem discovers and does not manufacture, so Gamma supplies no subject from nothing - the datum is GIVEN, as Agency puts it, not inferred. Re-anchoring cosmos_obtains on it would repeat exactly the A1 bug, where subject-existence became a consequence of plurality, the very datum it must precede, and A1 was reverted for that reason. The claim is falsifiable in both directions: reject the bridge and C367 falls, this row stands on the datum alone. It is not free - the price is relocated to the stipulated TRANS act-datum, free in axioms and not free in performance."

def C387 : String := "THE GOD-LANE's payoff: the ground's love, with a statement byte-identical to C351's and without the plurality route. Measured, C351 is {AxGroundLovesContingentRealm, AxTwoSubjects, GroundBearsGood, Means, Subject, Will, propext, subjectWill} and this is {AxGroundLovesContingentRealm, GroundBearsGood, Initiates, Means, State, Subject, propext} - three axioms and a sort fewer, since AxTwoSubjects took Will and subjectWill down with it. So the interpersonal metaphysics is no longer a premise of the ground's love, and because the two remaining premises are independent of it, the removal is VISIBLE rather than quietly absorbed. The love bridge and GroundBearsGood stay and must stay: a directional good held by the ground is not expressible in Gamma's grounding vocabulary, which reaches only undirected sufficiency, and the corpus has already recorded that no reading of it is axiom-free. A reader who rejects AxTwoSubjects keeps this row; a reader who will not grant that an act occurred rejects it. Relocated price, not a free lunch."

def C388 : String := "THE F15 BOUND, BY DECLARATION: no subject means every proposition - no creature is semantically omnipotent. Paid 17 times as an anonymous premise across five files and never registered; now named, badged, and falsifiable. It bounds one uninterpreted relation on one nullary sort and asserts no connection between entities, so it is VOCAB, not META - the same status as ofGround_existsAt, and contrast asietyFreedom_ofGroundFreedom which is META because it declares a connection the vocabulary cannot support."

def C389 : String := "The unicity of the ground of all reality, on the named bound rather than the anonymous premise. Existence was already PROVEN unconditionally at C319; what is stipulated here is the UNICITY. The price is invisible to print-axioms by construction, since a premise is not an axiom - the badge is the only signal."

def C390 : String := "Sole universal grounding of reality, on the named F15 bound."

def C391 : String := "Canonical aseity of the ground, conditional on the named F15 bound."

def C392 : String := "Modal aseity of the ground with respect to CanonicalExtDepAt, on the named F15 bound."

def C393 : String := "Divine pure actuality, actus purus, of the ground - on the named F15 bound rather than the anonymous premise."

def C394 : String := "Zero passive grounding potency in the ground, on the named F15 bound."

def C395 : String := "Divine simplicity of the ground, on the named F15 bound. The logic is classical, so the footprint carries propext - a Lean meta-logic cost, not a substantive axiom."

def C396 : String := "Mereological non-compositeness of the ground, on the named F15 bound. Same classical-logic propext cost as C395."

def C397 : String := "Divine simplicity AND ontological transcendence of the ground, on the named F15 bound. Same classical-logic propext cost."

def C398 : String := "Canonically aseitous but not itself asietic: canonical aseity holds of the ground, asiety does not. The ground must stay out of the chooser inventory. On the named F15 bound."

def C399 : String := "The bound is FALSIFIABLE, not vacuous: take S as Unit and M as always-True, and every subject means every proposition - a semantically omnipotent carrier is a model of the negation. So the unicity genuinely rests on the bound and must be badged accordingly. The counterpart to C382's role for the meaning batch: the model that keeps the price honest."

def C400 : String := "The bound doing REAL WORK: ofGround_meansAll gives the ground EVERY proposition, so the finitude bound is exactly what keeps the ground off the Subject sort - if some subject were the ground, that subject would mean every proposition, contradicting the bound at that subject. Stated through the bound on purpose so the dependence is visible rather than hidden behind C315's unconditional ofGround_ne_ofSubject."

def C401 : String := "THE REFUTATION: the no-meaning world is not possible in Gamma. Meaning_I p is definitionally exists s, Means s p, so a subject who means something is already a counterexample to the thesis, and cogito_from_T12 exhibits one with no hypothesis. Three lines, never written down until now. This is NOT axiom-free - nothing in the bare meaning vocabulary refutes the thesis, and C382 IS the machine-checked proof of that impossibility. What C382 exhibits is a free signature satisfying its own NoI, a different proposition about a different sort; it is consistent AS A SIGNATURE and stays that way. What this row shows is that the thesis does not survive THE THEORY: given the plurality bridge, Gamma refutes it outright. Companion, not replacement, to the ladder, the retorsion, the complement and the utterance model."

def C402 : String := "The same refutation on the act-datum, with no META bridge: act_datum_implies_means turns 'someone acted' straight into a meaning witness, because Act already contains Means - so whoever grants that an act occurred grants the thesis's falsity with it. The God-lane twin of C401: C401 is unconditional on the plurality bridge, this row is conditional on the performative datum and bridge-free, price relocated to the TRANS act-datum - free in axioms, not free in performance. The hypothesis is anonymous, so the registry listing is the ONLY signal of the dependence."

def C403 : String := "The vocabulary of the two kinds: the necessary-kind predicate over subjects. Its negation is the contingent kind - an individual person, actual-world-relative, which might not have existed. Whether the necessary kind is inhabited is the priced bridge C404, never part of this row."

def C404 : String := "The bridge: the necessary kind of subject is inhabited by a Person - the ground of reality in its Personal Type, read as a Subject. A Person is a Subject by definition, and the Personal Type of the ground is proved; the modal step from personal ground to world-rigid subject is this bridge, and it is the whole price of 'a person who means must be necessary'. It does not identify the ground-constructor with any correlate, does not say the Creator inhabits the world, and does not make any other subject necessary."

def C405 : String := "A subject of the necessary kind is necessary: its correlate exists at every world by the kind disjunct. The kind-relative form of persistence - of the necessary kind only, never of subjects as such."

def C406 : String := "A subject of the contingent kind is not necessary: at the all-false world its correlate fails. This is where every contingency finding that used to be stated unconditionally now lives, carrying the kind hypothesis that was always its real content."

def C407 : String := "A necessary subject exists, from the bridge. Vocabulary plus the bridge only."

def C408 : String := "A necessary person exists, from the bridge: the person who means is of the necessary kind, the contingent person of the other kind."

def C409 : String := "Claim D derived instead of annotated: the necessary person exists. This retires the 'annotated only' note. The price is exactly the bridge - reject it and this goes with it; the contingent person, the world inhabitant, and every countermodel are untouched by it."

end Logos.ClaimMeanings