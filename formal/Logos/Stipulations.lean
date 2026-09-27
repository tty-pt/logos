/-
# Logos.Stipulations — registry of definitional stipulations

A definitional stipulation is a match arm / definitional value that settles a
philosophical question by fiat (rather than by proof or by declared axiom).
This module registers each stipulation in scope with its `Tag:`, its
`Philosophical cost:`, and the list of theorems whose `trivial`-class proofs
rest on it — so a reader can see exactly which conclusions rest on a
stipulation. The `ofGround` constructor is NOT deleted (scope decision §47.2):
it is tagged, priced, and badged.

Machine contract (`scripts/audit_stipulations.py`): every entry is a
`def <name> : Stipulation where` block with one field per line
(`name`, `location`, `anchor`, `tag`, `cost`, `dependents`). The audit script
parses exactly this shape, verifies each `location` anchor against the source
and each dependent against `formal/depgraph.json`, and emits
`formal/stipulation_audit.json`, which `scripts/build_deduction.py` renders as
the ◈ stipulation badge in the kernel audit.
-/

namespace Logos.Stipulations

/-- Classification tag of a stipulation (closed vocabulary, as for axioms).
    `TRANS` (performative/transcendental) was added 2026-09-27 for the
    performative act-datum: a datum assumed *as given* rather than derived, whose
    denial is self-refuting. It is the only tag that is neither a definitional
    choice (VOCAB) nor a metaphysical bridge (META), and it is the tag
    `Logos.Agency` has always called its foundation "TRANS"
    (`Agency.lean:5`, "`Cogito` (TRANS)"). -/
inductive StipulationTag where
  | VOCAB
  | SEM
  | META
  | TRANS
  deriving Repr, DecidableEq

/-- A registered definitional stipulation. -/
structure Stipulation where
  name : String
  location : String
  anchor : String
  tag : StipulationTag
  cost : String
  dependents : List String

/-- Tag: VOCAB
World-rigidity of the ground: `EntityExistsAt w .ofGround := True`.

Philosophical cost: every "necessary existence" theorem about `ofGround`
unfolds this `True`. Necessity of the ground is therefore stipulated by the
constructor's match arm, never derived and never declared as an axiom. -/
def ofGround_existsAt : Stipulation where
  name := "ofGround_existsAt"
  location := "Entity.lean:48"
  anchor := "Entity.ofGround => True"
  tag := StipulationTag.VOCAB
  cost := "World-rigidity stipulated by match arm: necessity theorems about ofGround unfold this True."
  dependents := ["ofGround_necessary", "the_ground_everlasting", "the_ground_atemporal", "everlasting_and_atemporal_ground", "ofGround_necessary_ground_of_reality", "ofGround_gapless_operative_scope", "ofGround_foundational_omnipotence"]

/-- Tag: VOCAB
Meaning-everything of the ground: `EntityMeans .ofGround p := True`
(duplicated verbatim for the local `EntityMeans` copy).

Philosophical cost: every "ground means / grounds everything" theorem about
`ofGround` unfolds this `True`. Explanatory adequacy of the ground is
therefore stipulated by the match arm, never derived and never declared. -/
def ofGround_meansAll : Stipulation where
  name := "ofGround_meansAll"
  location := "RecoveredOntologicalGround.lean:50"
  anchor := "Entity.ofGround => True"
  tag := StipulationTag.VOCAB
  cost := "Meaning-everything stipulated by match arm (duplicated at NecessaryPersonalGround.lean:155): grounding theorems about ofGround unfold this True."
  dependents := ["ofGround_ground_of_reality", "ofGround_undivided_meaning", "ofGround_necessary_ground_of_reality", "ofGround_truth_exhaustive", "ofGround_world_truth_exhaustive", "ofGround_not_truth_tracking", "ofGround_foundational_omniscience"]

/-- Tag: VOCAB
Indivisibility of the ground: `HasInternalComponent .ofGround := False`.

Philosophical cost: structural simplicity of the ground (`¬ HasInternalComponent
.ofGround`) is proved by `intro h; exact h` — i.e. by unfolding this `False`.
Simplicity is therefore stipulated by the match arm, never derived. -/
def ofGround_noInternalComponents : Stipulation where
  name := "ofGround_noInternalComponents"
  location := "DivineSimplicity.lean:94"
  anchor := "Entity.ofGround => False"
  tag := StipulationTag.VOCAB
  cost := "Indivisibility stipulated by match arm: the simplicity theorem unfolds this False."
  dependents := ["ofGround_has_no_internal_components"]

/-- Tag: SEM
The identification of operation with presence-plus-obtaining:
`OperatesAt v e P := ExistsAt v e ∧ P v` — the founding definitional choice of
`DivineOmnipotence` (Aquinas *ST* I q. 25 a. 5: *semper et ubique* operans).

Philosophical cost: Γ has **no** causal production relation, so "the ground
operates P" is read as "the ground is present where P obtains" — presence, not
production. Foundational omnipotence is therefore proved over this weakened
reading, and the causal/creative sense is BLOCKED, not discharged
(`README-OLD.md:263`; GAPMAP Level 17). The price is machine-checked in both
directions: `existence_everywhere_does_not_entail_operation` (presence without
operation) and `exhaustive_scope_without_operative_scope` (maximal meaning scope
without operation) are `{}` countermodels, so the identification is not free.
Consistency model: Γ's own classical valuation semantics with `EntityExistsAt`
— every countermodel above is a finite two-element carrier, so the reading is
consistent. -/
def operatesAt_presencePlusObtaining : Stipulation where
  name := "operatesAt_presencePlusObtaining"
  location := "DivineOmnipotence.lean:118"
  anchor := "def OperatesAt"
  tag := StipulationTag.SEM
  cost := "Operation identified with presence-plus-obtaining: foundational omnipotence is proved over the weakened reading; the causal/creative sense stays BLOCKED."
  dependents := ["ofGround_gapless_operative_scope", "ofGround_operates_only_what_obtains", "ofGround_does_not_operate_contradictions", "ofGround_sole_gapless_operator", "ofGround_foundational_omnipotence", "necessity_and_presence_yield_foundational_omnipotence"]

/-- Tag: META
The ground of reality is the ground of *freedom*: `AsietyFreedomOfGround` says every subject the
ground grounds, and that is asietic, makes a true choice at **every** incompatible pair — so the
ground's freedom is shared with what it grounds, as `AsietyFreeWill`.

Philosophical cost: this is the metaphysical bridge of the chain, and it is **declared, not
derived**, because Γ's grounding vocabulary cannot support it. `GroundsEntity` is vacuous
(`EntityMeans .ofGround p := True`, so `ground_grounds_every_entity` is `intro p _; exact
True.intro`), the only non-vacuous grounding predicate, `GroundsRightWrong`, is definitionally
`∃ p q, Chooses s p q` and so already collapsed to free will (C168), and the substantive grounding
relation is BLOCKED (C228). The price is machine-checked in three directions:
`asietyAloneDoesNotYieldTrueChoice` (asiety at one witness does not give true choice at every
pair, so the universal quantifier over subjects is doing real work and the weaker existential
reading is strictly cheaper), `frameContingencyDoesNotBindAPair` (the frame's contingency is
`Form`-level and does not bind a given `Prop`-level pair), and `rightWrongFactYieldsNoChooser`
(the right/wrong fact is compatible with a meaning-vocabulary in which no subject means anything,
so **no axiom-free existence of a chooser** — the unconditional existence half still costs
`AxTwoSubjects`, META). Separately, the ground is not thereby made a chooser: C285 stands, and
`groundIsNotASharerOfAsietyFreeWill` restates it here.

Note what an audit can and cannot see: because this is a `def` and not an `axiom`, `#print axioms`
reports `{Means, Subject}` — vocabulary only — and **no axiom-counting tool will ever flag it**.
This ◈ entry and its badge are the only place the price is visible.
Consistency model: Γ's own classical valuation semantics; every countermodel above is a finite
one- or two-element carrier, so the reading is consistent. -/
def asietyFreedom_ofGroundFreedom : Stipulation where
  name := "asietyFreedom_ofGroundFreedom"
  location := "AsietyFreedom.lean:119"
  anchor := "def AsietyFreedomOfGround"
  tag := StipulationTag.META
  cost := "The ground's being the ground of freedom is declared, not derived: GroundsEntity is vacuous, GroundsRightWrong is definitionally FreeWill (C168), and substantive grounding is BLOCKED (C228). Priced by three {} countermodels; the universal reading is strictly stronger than the existential one."
  dependents := ["asietyFreedom_yields_trueChoice", "asietyFreedom_yields_asietyFreeWill", "asietyFreeWill_yields_trueChoice", "asietyFreedom_summary"]

/-- Tag: VOCAB
Semantic finitude: no subject means every proposition — no creature is semantically
omnipotent. `SemanticFinitude : Prop := ∀ s, ∃ p, ¬ Means s p`.

Philosophical cost: the per-subject meaning bound was already paid as an explicit
premise 17 times across `DivineSimplicity`, `DivinePureActuality`, `CanonicalAseity`,
`AsieticChoice` and `FoundationalUnicity`, and never registered. It is now named
(`SemanticFinitude`) and badged ◈, and the ten headline corollaries — unicity of the
ground, sole universal grounding, canonical and modal aseity, divine pure actuality, zero
grounding potency, divine simplicity, non-compositeness, simplicity-and-transcendence, and
aseity-without-asiety — carry it as a *named* hypothesis. The ten existing conditional
theorems are not edited and keep their anonymous premise; consolidation is the new
registered corollary. **No new axiom is added**: `SemanticFinitude` is a `def` of a
`Prop` and the corollaries take it as a premise, so `#print axioms` reports the same
`{Means, Subject}` (or `{Initiates, Means, State, Subject}`, or with `propext`) as the
corresponding conditional theorem, and the declared-axiom count is unmoved. The price is
therefore *invisible to every footprint tool*, and the ◈ badge is the only place it shows.
A reader must NOT read `exactly_one_universal_modal_ground_stipulated` at `{Means,
Subject}` as a proof of monotheism: the unicity of the ground is stipulated in the sense
that no subject of assertion reaches every proposition, and it is not derived.
`Tag: VOCAB` because the sentence bounds one uninterpreted relation (`Means`) on one
nullary sort (`Subject`) and asserts no connection between entities — the same status as
`ofGround_existsAt` and `ofGround_noInternalComponents`; contrast
`asietyFreedom_ofGroundFreedom`, which is META because it declares a connection Γ's
vocabulary cannot support. Consistency model / falsifiability: the reading does real
work in both directions and is *not* free — `semantic_omnipotence_is_consistent` is a
`{}` model of the negation (a semantically omnipotent carrier), so the stipulation is
falsifiable and the unicity genuinely rests on it; and
`semanticFinitude_excludes_ground_from_subjects` shows the bound doing work, since the
`ofGround_meansAll` match arm gives the ground every proposition and the bound is what
keeps it off the `Subject` sort.

The registry record itself is a value of the `Stipulation` structure — strings, a tag and
a list — and therefore depends on no axiom at all; it is the *ten theorems* it lists, and
the `SemanticFinitude` def they take as a premise, that carry the (invisible) price.
Footprint: `{}`. -/
def semanticFinitude : Stipulation where
  name := "semanticFinitude"
  location := "SemanticFinitude.lean:70"
  anchor := "def SemanticFinitude"
  tag := StipulationTag.VOCAB
  cost := "The per-subject meaning bound, paid 17 times as an anonymous premise and never registered, is now named and badged. The ten headline corollaries carry it as a named hypothesis; no new axiom is added and their kernel footprints are unchanged, so the ◈ badge is the only signal. A reader must not read exactly_one_universal_modal_ground_stipulated at {Means, Subject} as a proof of monotheism: the unicity of the ground is stipulated, not derived. Falsifiable via semantic_omnipotence_is_consistent ({})."
  dependents := ["exactly_one_universal_modal_ground_stipulated", "ofGround_sole_universal_grounding_stipulated", "conditional_canonical_aseity_stipulated", "ofGround_modal_aseity_conditional_stipulated", "ofGround_divine_pure_actuality_stipulated", "ofGround_no_grounding_potency_stipulated", "ofGround_divine_simplicity_stipulated", "ofGround_non_composite_stipulated", "ofGround_simplicity_and_transcendence_stipulated", "ground_is_canonically_aseitous_but_not_asietic_stipulated"]

/-- Tag: TRANS
The performative act-datum: `∃ s : Subject, ∃ p : Prop, Act s p` — an act occurred.

This is the one stipulation that is neither a definitional value nor a declared axiom. It
is the datum `Logos.Agency` has always named as the foundation of the system: "the present
act of reasoning is *given*, not inferred" (`Agency.lean:4`), whose denial is self-refuting
(`noCogito_selfRefutes`, C58). It is registered here rather than as a 27th axiom because
the act-datum is **given**, not asserted: Γ does not manufacture it, and it does not
discover it either — it is what any derivation *starts from*, and the fifteen-odd theorems
that take it as a hypothesis have always said so.

**Why register it now (2026-09-27).** The God-lane found that `Logos.Value.AxTwoSubjects`
was being paid to reach a meaning-bearing realm (`cosmos_obtains`, C367) when the act-datum
reaches the same witness with no bridge at all, since `Act` already contains `Means`. Left
unregistered, that relocation would have been invisible: a hypothesis is a hypothesis, and
`#print axioms` cannot see one. `cosmos_presence_model_of_the_act_datum` and
`the_ground_loves_the_cosmos_from_the_act_datum` are the two dependents, and the ◈ badge
is the only signal — the same arrangement as `semanticFinitude` above, and the same
limitation: the price here is invisible to `#print axioms` by construction.

**The price, stated honestly.** `AxTwoSubjects` is a `Tag: META` bridge and this is not;
the two are not interchangeable and neither is free. The act-datum is free *in axioms* and
not free *in performance* — the same account `MeaningRetorsion` gives for the retorsion
batch, and the reason C375's affirmation is called the *input* to its own contradiction.
Reject this datum and both dependents go; reject `AxTwoSubjects` and they stand. The
transition from one to the other is a relocation of the cost, and it is falsifiable in
both directions, which is more than either premise could claim alone.

Consistency model: the reading is not vacuous and not over-strong. It does **not** yield
unconditional subject-existence — no theorem in Γ concludes `∃ s, ∃ p, Act s p` from
nothing, precisely because Γ does not fabricate — so C350/C367 keep their own prices and
this row is a *companion* to them, never a replacement. And it does not touch `Act`'s
content: `Meanless` worlds (`Means := False`) cannot host the datum either, which is why
`semanticFinitude` and this stipulation are separate entries rather than one.
Footprint: `{}`. -/
def performativeActDatum : Stipulation where
  name := "performativeActDatum"
  location := "Agency.lean:4"
  anchor := "The performative datum of §1"
  tag := StipulationTag.TRANS
  cost := "The performative act-datum (someone acted), assumed as given rather than declared or derived, since a theorem discovers and does not manufacture. Registered so the God-lane's relocation of C367's price from the META bridge AxTwoSubjects to this datum is visible at all: a hypothesis is invisible to #print axioms, so the badge is the only signal. Free in axioms, not free in performance. Reject it and both dependents go; reject AxTwoSubjects and they stand."
  dependents := ["cosmos_presence_model_of_the_act_datum", "the_ground_loves_the_cosmos_from_the_act_datum"]

/-- The registered stipulations, in audit order. -/
def registeredStipulations : List Stipulation :=
  [ofGround_existsAt, ofGround_meansAll, ofGround_noInternalComponents,
   operatesAt_presencePlusObtaining, asietyFreedom_ofGroundFreedom,
   semanticFinitude, performativeActDatum]

end Logos.Stipulations
