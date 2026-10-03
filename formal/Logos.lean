-- Logos — architectural barrel file.
-- Import here every module that should be built as part of the library.
import Logos.Core
import Logos.Necessity
import Logos.Semantics
import Logos.Entity
import Logos.Modal
import Logos.Agency
import Logos.Person
import Logos.Initiation
import Logos.Alternatives
import Logos.Order
import Logos.GroundPerson
import Logos.Choice
import Logos.Value
import Logos.Plurality
import Logos.Love
import Logos.HostileSemantics
import Logos.ConditionalTheology
import Logos.Retorsion
import Logos.TheologicalModalHardening
import Logos.ModalCreationAgency
import Logos.EssenceActCollapse
import Logos.ModalPossibilityFrontier
import Logos.DeepModalFrontier
import Logos.NonLibertarianCreation
import Logos.FreeWillInvariance
import Logos.ContextualDevelopment
import Logos.HardenedInvariance
import Logos.CognitiveDiscrimination
import Logos.SubContrastFoundations
import Logos.ProofSpecificContrast
import Logos.AdversarialReductioAudit
import Logos.CognitiveToAgencyFrontier
import Logos.FreeWillIndependence
import Logos.ChoiceRepair
import Logos.AgencyFrontierAudit
import Logos.A14SemanticAudit
import Logos.PostA14Frontier
import Logos.DefinitiveAgencyFrontier
import Logos.AxiomNegationAudit
import Logos.WillIndividuationAudit
import Logos.JointForcing
import Logos.NegativeRetorsionAudit
import Logos.ExecutiveDeliberativeFrontier
import Logos.DeepContrastiveFrontier
import Logos.DeterministicReductioFrontier
import Logos.AgencyDeterminismConsequences
import Logos.ActionChoiceDefinitions
import Logos.StrongActionChoice
import Logos.NormativeTruth
import Logos.DirectNormativeFreeWill
import Logos.ConstitutiveNormativeFreeWill
import Logos.A14DerivationAudit
-- Registry of definitional stipulations (tagged, priced, badged; no new axioms).
import Logos.Stipulations
import Logos.IndubitableNormativeFreeWill
import Logos.UndeniableNormativeDerivation
import Logos.RetorsiveNormativity
import Logos.BipolarityRetorsion
import Logos.DirectNormativeRetorsion
import Logos.NormativeOrder
import Logos.PersonhoodOntologyAudit
import Logos.OughtRetorsion
import Logos.NecessaryPersonalGround
import Logos.PersonalNormativeGround
import Logos.RecoveredOntologicalGround
-- New constitutive headline: the free personal act grounds the Gamma judicative/normative order (Claim I).
import Logos.PersonalGroundOfReality
-- Necessity and eternity of the ultimate ground (Claim E / stage layer).
import Logos.NecessityEternity
-- Reality-hook & moral frontier audit (countermodel vs "right/wrong has nothing to do
-- with reality", and the machine-separated moral bridge).
import Logos.RealityHookAudit
import Logos.MoralFrontierAudit
-- Canonical aseity and external grounding boundary.
import Logos.CanonicalAseity
-- Proof-presentation retorsion, syntactic checker separation, and adversarial audit.
import Logos.ProofPresentationRetorsion
-- Classical divine simplicity and ontological transcendence.
import Logos.DivineSimplicity
-- Classical divine immutability and ontological invariance.
import Logos.DivineImmutability
-- Classical foundational omnipresence and universal modal grounding.
import Logos.FoundationalOmnipresence
-- Classical foundational unicity and structural monotheism.
import Logos.FoundationalUnicity
-- Classical divine pure actuality and perfection.
import Logos.DivinePureActuality
-- Classical foundational omniscience and truth-exhaustiveness.
import Logos.DivineOmniscience
-- Classical foundational omnipotence and the non-contradictory restriction.
import Logos.DivineOmnipotence
-- The ground's love as a distinct, Entity-level relation (not-merge with `Loves`).
import Logos.LovesAsGround
-- The cosmos exists, as a declared empirical datum.
import Logos.CosmicExistence
-- True choice, asiety as true freedom, and the closing of the `?` in the choice chain
-- (no axiom introduced; the rejected horn comes from AxJudicativeBipolarity, already in Gamma).
import Logos.AsieticChoice
-- Classical divine transcendence and the four senses of externality (the quantifier-swap
-- inference behind C78/C79/C88 machine-checked as a countermodel; no axiom introduced).
import Logos.DivineTranscendence
-- Asiety from the Act-free weak choice (axiom-free), and the ground's stipulated sharing of it:
-- `AsietyFreedomOfGround` is a definitional stipulation (Tag: META, registered in
-- Logos.Stipulations), not an axiom, so the declared-axiom count is unchanged.
import Logos.AsietyFreedom
-- The personal ground (`Logos.TrinitarianPersonalGround`): the ground is not void of
-- personhood, at zero substantive axioms. Two grounding routes are named — `GroundByBeing`
-- (presence-grounding, the non-vacuous one, which covers the atoms for a reason nobody chose;
-- ST I q. 44 a. 1) and `OneEssence` (providential indwelling) — and conjoined in `PersonalGround`,
-- with `Perichoretic` as perichoresis over the existing asymmetric relation. Nothing in
-- `EntityMeans` moves; §6.1 records why the match arm must not move. Twelve declarations
-- (3 declarations of vocabulary, 9 theorems), zero new axioms, so the declared-axiom count is
-- unchanged.
-- Its machine-checked basis is `GAPMAP.md` and the audit suite; the governing workflow is
-- `investigations/trinitarian-probe.lean` (audit artifact, never compiled by `lake build`).
import Logos.TrinitarianPersonalGround
import Logos.BoundedMeaning
-- The Trinitarian subject bridge (`Logos.TrinitarianSubjectBridge`, plan S4, D-1 + D-2): the
-- missing link between the divine-hypostasis sort and `Subject`. `DivineSubjectRole`
-- (`Tag: VOCAB`) is the relation of origin that distinguishes the three persons, re-declared on
-- the `Subject` sort because `DivineAgape.IsWord`/`IsSpirit` are indexed by `DivineHypostasis`
-- and cannot be applied there. `TrinitarianPersonalBridge` (`Tag: META`) asserts the three
-- persons are necessary persons sharing the one ground, and exhausts `NecessarySubjectKind` — so
-- there is no fourth. It deliberately does NOT route through `GroundsRightWrong`, which is
-- definitionally free will already and would be circular. The three `FreeSubject` conjuncts
-- therefore trace to this `META` bridge and not to the `TRANS` bounded-meaning axiom; plan §5.1's
-- draft identified the persons by `DivineHypostasis.P1 = a`, which does not elaborate (no such
-- field, and no common sort), so identification is by role instead. Two new axioms; distinctness
-- is derived from the role assignment at zero cost.
import Logos.TrinitarianSubjectBridge
-- The single-person denial refuted at the chain's hinge (`Logos.SinglePersonDenial`, C579,
-- `LOVE-2.md` D5): the ground is a personal necessary essence indwelt by every Person and no
-- Person itself; a donation's terminus is the necessary ground, so the self-giving cannot depend
-- on a contingent being and the contingency conclusion has no premise. Zero new axioms and no
-- `AxAgapeEssence` on the refutation rows — the datum is priced on C575's own row and is not
-- used to refute the objection that grants it.
import Logos.SinglePersonDenial
-- Semantic finitude (`SemanticFinitude`, Tag: VOCAB, registered in Logos.Stipulations as
-- ◈ `semanticFinitude`): the per-subject meaning bound F15 named, consolidated and badged,
-- with ten priced corollaries. A premise carried on each corollary, not a new axiom, so the
-- declared-axiom count is unchanged; the ◈ badge is the only signal.
import Logos.SemanticFinitude
-- The meaninglessness thesis stated in the corpus's own `Meaning_I` vocabulary (`NoMeaning`),
-- its four-rung ladder up to the unconditional retorsion, and the joint refutation of the
-- M1/C294 countermodel family *as answers* — with the populated complement that keeps the
-- countermodel alive as a model, and the utterance model in which the thesis *is* said.
-- The meaninglessness batch of 2026-09-27. 19 declarations — 16 theorems
-- and 3 `def`s (`NoMeaning`, `NoWeakActIn`, `Voices`) — and zero new axioms.
import Logos.MeaningRetorsion
-- §9 — precedence to the true/false distinction, in four senses with four verdicts
-- (`Logos.Precedence`), plus the refutation of the "empty world" reading the prose
-- route needed: no world satisfies no form. Ten declarations, one `structure`, zero new
-- axioms. `Core.T p := p` is world-free, so the row's status is a split, not a bare
-- PROVEN. The plan of record is `PLAN.md`; there is no root `AUDIT.md`.
import Logos.Precedence
-- The sole-bearer suite (`Logos.CharacteristicSoleBearer`): the discriminating form
-- `∀ e, P e → e = Entity.ofGround` for the six footprint characteristics, plus the master
-- theorem. Zero new axioms; the four `SemanticFinitude`-priced rows pay the 27th axiom
-- (`Tag: VOCAB`) once each, in one shared lemma (`no_subject_grounds_the_ground`).
-- Immutability is recorded as a priced boundary, not asserted.
import Logos.CharacteristicSoleBearer
-- The succession audit (`Logos.SuccessionAudit`, `Logos.SuccessionCountermodel`): what
-- `NotInSuccession` actually says. `the_ground_not_in_succession` binds the initiation
-- conjunct and discards it, so the ground's transition invariance is constructor
-- disjointness — and every atom shares it. Four live rows, zero new axioms: the
-- extraction lemma, the ground/atom asymmetry (C321's twin on the other field), the
-- non-triviality instance the ledger misattributed to C197, and the author's sentence
-- "the fact Γ exists means someone initiates" discharged with its premise explicitly
-- inert. The countermodel is free-signature, `{}`. Disclosure, not demotion: no badge
-- moves. The plan of record is `SUCCESSION.md`.
import Logos.SuccessionAudit
import Logos.SuccessionCountermodel
-- The Thomistic love-act batch (`Logos.ThomisticAct`): the entity-level production
-- relation F10 asks for, the subject-level love→act bridge, the ground-level
-- love→production bridge (scoped to `Entity.ofGround`), and the two derived rows —
-- among them the conjunction in which the ground produces and is immutable at once,
-- which is what the succession audit made statable. Three new axioms: one `VOCAB`
-- relation, two `META` bridges. The plan of record is `SUCCESSION.md` §4.
import Logos.ThomisticAct
-- The act-datum cascade (`Logos.ActCascade`): the unconditional consequences of C454.
-- Eighteen theorems across five modules carried `∃ s p, Act s p` as their *sole* hypothesis;
-- since the datum is a declared axiom, that is a leftover, not a premise. Twelve distinct
-- conclusions, collected in one module with the price (`performative_act_datum`, plus
-- `AxIntentionalChoice` or `AxActPolarity` on the two routes each) on every row. No axiom is
-- added, no existing proof altered, no existing statement weakened. The `Asserts` lane stays
-- closed: C454 yields no `Asserts`-existential, so twelve further theorems stay conditional by
-- construction. C465/C467 stay conditional and F10 stays BLOCKED. The plan of record is `WIN.md`.
import Logos.ActCascade
-- The production countermodel (`Logos.ProductionCountermodel`): C465's shape (`∃ w φ,
-- Produces g w φ`) and F10's missing derivation (2) (`∀ φ, (∃ w, Satisfies w φ) →
-- ∃ v, Produces g v φ`) are independent — the ground can produce one form and fail
-- every other satisfiable one, because `Produces` is a `Tag: VOCAB` axiom and nothing in
-- the corpus relates it to `Satisfies`. Free-signature, so `{}`: a shape result, not a
-- claim about Γ, and **not** a refutation of F10, which stays BLOCKED. Plan of record
-- is `WIN.md` §2 B2.
import Logos.ProductionCountermodel
-- The last two structural gaps in the characteristic family, closed at 0 new axioms.
-- `Logos.CharacteristicClosure`: Divine Simplicity was the last *conditional* instantiated
-- form, and its premise turned out to be the now-declared F15 `SemanticFinitude` (C484-C486);
-- `TransitionInvariance` is shown refutable, the one field C321's vacuity finding did not
-- reach (C487-C488); and the Thomistic principle form the characteristic was missing is
-- supplied together with the machine-checked finding that F15 bounds the wrong relation
-- for it (C491-C492). `Logos.ImmutabilitySoleBearer`: C453 is refuted, not deferred — a
-- second entity bears all four immutability fields while the act datum stays saturated
-- (C489), and the exact per-subject statement C454 does not give is named (C490).
import Logos.CharacteristicClosure
import Logos.ImmutabilitySoleBearer
-- The necessary-kind audit (`Logos.NecessaryKindAudit`): what `NecessarySubjectKind` being
-- inhabited does to the theory. Reads the kind vocabulary and one declared META bridge, adds
-- zero axioms. C494 refutes the extensional reading of *ST* I q.19 a.4 (`∀ Q, Q ofGround →
-- ∀ e, NecessaryEntity e → Q e`), C495 is the grade statement (necessity is the one footprint
-- characteristic that does *not* pick the ground out), and C496/C497 profile the second
-- necessary being: it has necessity and gapless operativeness but lacks transcendence, maximal
-- capacity, and pure actuality. The plan of record is `PLAN3.md`.
import Logos.NecessaryKindAudit
import Logos.GoodDenial
-- The second-person attempt (`Logos.SecondPersonGoodAttempt`): TWO `{}`
-- countermodel witnesses — a lone will is vacuously individual (C501), and
-- two distinct persons still do not force the moral Good (C502) — plus the
-- BLOCKED love-lane probe (C503). No axiom changes; the Good stays PROVEN↑
-- under the single disclosed META bridge C177. Plan of record: `OTHER.md`.
import Logos.SecondPersonGoodAttempt
-- The Trinity case (`Logos.DivineAgape`, plan `TRINITY.md`): the conditional
-- corridor from self-giving Agape to `TrinitarianStructure` (C510) under three
-- disclosed `Tag: META` axioms (C504–C506), plus the corridor theorems C507–C509.
-- New abstract sort `DivineHypostasis` (a `structure`, zero axioms), opaque role
-- vocabulary, no Γ axiom touched. Stage B: the separations C511–C514 land in
-- `Logos.TrinitySeparations`.
import Logos.DivineAgape
-- Stage B, landed: the four axiom-free separations C511–C514 (narcissist,
-- creature-love, attribute-love, binitarian) — all `{}`, zero axioms, the exact
-- price of the case (three is exactly the price of the Spirit).
import Logos.TrinitySeparations
-- The epistemic poles of the personal ground (C525-C528): the indexed ground at
-- `(Correct, Incorrect)` is personal, and the epistemic order needs no ground
-- (C528, `{}`).
import Logos.EpistemicPersonalGround
-- The necessity direction made unmissable (C553-C555): the author's FACT —
-- "nothing can be epistemologically right or wrong without a non-mechanical
-- (Free) being for which meaning can mean" — as three badged rows, plus the
-- propositional `T`/`IsFalse` half (C556). A visibility batch, not a proof
-- batch: C140 was already `{}`-substance. Zero axioms; register stays 35.
import Logos.EpistemicNecessity
-- The act datum's own polarity discharges the choice frontier (C565, C587):
-- a genuine Free Person derived with zero META axioms from performative_act_datum
-- and AxActPolarity via co-meaning and free will.
import Logos.NoMeanerNoFalsity
