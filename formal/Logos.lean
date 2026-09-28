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
-- PROVEN. The plan of record is AUDIT.md.
import Logos.Precedence
