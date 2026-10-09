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

**Retired 2026-09-28: `semanticFinitude` (registry 8 → 7).** The F15 meaning bound
`∀ s, ∃ p, ¬ Means s p` was registered here as a ◈ `def` on 2026-09-27. It is now a
**declared `Tag: VOCAB` axiom** in `SemanticFinitude.lean`, and the ten corollaries
that took it as a named hypothesis are now unconditional theorems of Γ. The entry
was retired because a `def`-premise is invisible to `#print axioms`: the ◈ badge was
the *only* place its price appeared, and it was simultaneously the most load-bearing
premise in the divine-attribute lane. A declared axiom shows up in every dependent's
audited footprint, in the axiom registry, and in `formal/axiom_audit.json`. The ten
`_stipulated` corollaries keep their names — historical, and cited from GAPMAP and
the prose corpus — but they are no longer stipulations and carry no ◈ badge. The
governing rule going forward: **a premise load-bearing enough to need a badge should
be an `axiom`, not a `def`**, because a `def` premise is not auditable.

**Retired 2026-09-28: `performativeActDatum` (registry 7 → 6).** The performative act-datum
`∃ s : Subject, ∃ p : Prop, Act s p` was registered here as a ◈ on 2026-09-27. It is now a
**declared `Tag: TRANS` axiom** (`Agency.performative_act_datum`, C454), on the author's
legislation that `Initiates` cannot be uninhabited. The three theorems that took it as a named
hypothesis (`cosmos_presence_model_of_the_act_datum`, `the_ground_loves_the_cosmos_from_the_act_datum`,
`noMeaning_is_refuted_from_the_act_datum`) keep their existing conditional statements — a
conditional theorem whose hypothesis is now provable is still true — and their `#print axioms`
footprints are unchanged, because the ◈ was a `def`-premise and contributed nothing to any
footprint. Same governing rule as above.
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
  location := "Entity.lean:78"
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
  location := "DivineClassicalAttributes.lean:748"
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
  location := "DivineClassicalAttributes.lean:2741"
  anchor := "def OperatesAt"
  tag := StipulationTag.SEM
  cost := "Operation identified with presence-plus-obtaining: foundational omnipotence is proved over the weakened reading; the causal/creative sense was BLOCKED until C493 declared universal production as a META bridge."
  dependents := ["ofGround_gapless_operative_scope", "ofGround_operates_only_what_obtains", "ofGround_does_not_operate_contradictions", "gapless_operators_are_ground_or_necessary_kind", "ofGround_foundational_omnipotence", "necessity_and_presence_yield_foundational_omnipotence"]

/-- Tag: META
The ground of reality is the ground of *freedom*: `AsietyFreedomOfGround` says every subject the
ground grounds, and that is asietic, makes a true choice at **every** incompatible pair — so the
ground's freedom is shared with what it grounds, as `AsietyFreeWill`.

Philosophical cost: this is the metaphysical bridge of the chain, and it is **declared, not
derived**, because Γ's grounding vocabulary cannot support it. `OneEssence` is vacuous
(`EntityMeans .ofGround p := True`, so `ground_grounds_every_entity` is `intro p _; exact
True.intro`), the only non-vacuous grounding predicate, `GroundsRightWrong`, is definitionally
`∃ p q, Chooses s p q` and so already collapsed to free will (C168), and no substantive grounding
relation over `Entity.ofGround` is available (C591). The price is machine-checked in three directions:
`asietyAloneDoesNotYieldTrueChoice` (asiety at one witness does not give true choice at every
pair, so the universal quantifier over subjects is doing real work and the weaker existential
reading is strictly cheaper), `frameContingencyDoesNotBindAPair` (the frame's contingency is
`Form`-level and does not bind a given `Prop`-level pair), and `rightWrongFactYieldsNoChooser`
(the right/wrong fact is compatible with a meaning-vocabulary that has **order and signification
and no chooser** — every subject means at most one content, so the fact
does not by itself deliver **any axiom-free existence of a chooser** — the unconditional existence half still costs
`AxTwoNecessaryPersonalCentres`, META, C584). Separately, the ground is not thereby made a chooser: C285 stands, and
`groundIsNotASharerOfAsietyFreeWill` restates it here.

**The vacuity of `OneEssence` is why the price is zero, not an argument that it is zero** (re-annotated
2026-10-03, and corrected the same day — `LOVE-2.md` D1). Two successive claims about this vacuity
are retracted here, and they were retracted in opposite directions, which is the tell. The first said
the vacuity was "load-bearing, not a defect" and the "marker that the ground's freedom is
*transferred* to the three persons and not *exercised* by a fourth chooser". The second over-corrected
and denied any relation at all: "there is no relation in Γ between the ground's scope and any
subject's freedom, so nothing is transferred, recorded or blocked".

**The relation exists, and it is this entry.** `AsietyFreedomOfGround` (`AsietyFreedom.lean:141`) is
the relation between the ground's scope and a subject's freedom; `AsietyFreeWill` is the predicate
the corpus gives to the freedom so shared; `asietyFreedom_summary` (`:357`) consumes it. The price is
zero because it is a `def` and not an `axiom`, **not** because nothing is transferred. The first
version's word *marker* was the only over-claim in it, and it over-claimed for a checkable reason: a
`def` is invisible to `#print axioms`, so nothing but this ◈ entry will ever flag it.

What the vacuity does support is narrower, and it is worth stating without embarrassment. The ground
is provably not asietic (`TrinitarianPersonalGround.ground_is_not_a_fourth_chooser`, `{Means,
Subject}`) and its total scope is not freedom
(`TrinitarianPersonalGround.ground_scope_does_contain_incompatibles`, `{Means, Subject}`), because
`Asiety` requires being a `Subject` (`AsieticChoice.lean:147-148`) — and the `≠` that discharges it
is `ofGround_ne_ofSubject`, which is the very fact `LovesAsGround.the_ground_is_not_a_person`
(`LovesAsGround.lean:604`) states. That is a limit of the predicate's reach over the ground. It is
not a refutation of freedom, and the limit does not touch the donation: a predicate that does not
reach the ground cannot deny the ground's gift either.

What the vacuity does *not* do is touch the donation. `self_donation_needs_no_personhood_of_the_ground`
(C578) holds the refusal and the gift together, and `denying_self_donation_is_absurd` (C576) closes
the absurdity: the ground is not a chooser **and** Agape is a gift between two distinct personal
properties of one location-entity (`agape_is_self_donation`, C575, one META axiom). Reading the
vacuity as shallowness says the opposite of what it is evidence for — and reading it as a transferred
freedom says something the kernel *does* contain, in a `def` no audit can see.

Note what an audit can and cannot see: because this is a `def` and not an `axiom`, `#print axioms`
reports `{Means, Subject}` — vocabulary only — and **no axiom-counting tool will ever flag it**.
This ◈ entry and its badge are the only place the price is visible.
Consistency model: Γ's own classical valuation semantics; every countermodel above is a finite
one- or two-element carrier, so the reading is consistent. -/
def asietyFreedom_ofGroundFreedom : Stipulation where
  name := "asietyFreedom_ofGroundFreedom"
  location := "AsietyFreedom.lean:141"
  anchor := "def AsietyFreedomOfGround"
  tag := StipulationTag.META
  cost := "The ground's being the ground of freedom is declared, not derived: OneEssence is vacuous, GroundsRightWrong is definitionally FreeWill (C168), and no grounding relation over Entity.ofGround is available (C591). Priced by three {} countermodels; the universal reading is strictly stronger than the existential one."
  dependents := ["asietyFreedom_yields_trueChoice", "asietyFreedom_yields_asietyFreeWill", "asietyFreeWill_yields_trueChoice", "asietyFreedom_summary"]

/-- Tag: TRANS
The world-datum: this world — the one I am writing the proof in — exists, and it
is contingent.

`Entity.actualWorld` fixes *which* world the proof is in (the all-`TV.t`
valuation) and `Entity.falsityWorld` names its opposite, so "the empty world is
not the actual world" becomes a theorem rather than a posture:
`falsityWorld_ne_actualWorld` (the two valuations differ), plus
`falsityWorld_holds_no_contingent_subject` (no subject of the contingent kind
exists at the falsity world) against `contingent_realm_obtains` (the actual
world *does* have contingent content, witnessed by an atom). Together, for zero
axioms, they rule out the one possibility the world-datum alone can kill.

**Why it is a datum and not a bridge.** The world's existence is not derived:
the author's line is "it is my stipulation that this world I'm writing the proof
in exists. But given that it does, consequences are in due." The consequences are
entailed; the existence is given. So this is `Tag: TRANS` — assumed as given, like the former `performativeActDatum` ◈
(now the declared axiom `Agency.performative_act_datum`, C454) — and NOT a `Tag: META` bridge, which would claim Γ
*infers* it, and NOT `Tag: VOCAB`, which would claim the valuation `def` decides
the question. What the `def actualWorld` decides is which world, not whether.

**What it buys, narrowly.** Free in axioms, not free in performance. It eliminates
the falsity world read as the actual world (`HostileSemantics.CountermodelFalsityWorld`,
`WorldStance.falsityWorldAsActual`) and it settles the falsity world's own content:
it is the necessary-subjects-only world, not an empty one. It does **not** reach
a world of necessary subjects only in general — that exclusion needs the
contingent-inhabitation lemma, which is BLOCKED and is recorded as a gap
(`SUBJECTS.md` §4), not as a price. And it does **not** touch the plurality of
subjects: `AxTwoNecessaryPersonalCentres` (`Tag: META`, C584) is a separate bridge on a separate ground,
per the author's "No, not yet a world of two persons. Unless something else in the
proof demands it."

**Why register it now (2026-09-28).** It was unregistered, and the generated C.1
preamble papered over the gap by naming the *act*-datum as the Lean content of the
*world*-stipulation. The two are different data with different dependents, and
conflating them made the world-datum's one genuine elimination invisible. The
ledger now answers the question the author actually asked — which countermodels are
wrong given that the contingent world exists — on its own axis, with the
classification derived in Lean (`WorldStance`) and cross-checked by
`scripts/build_deduction.py` against each model's declared structure.

Consistency model: not vacuous, not over-strong. The datum does not say the world
is *contingent* in the modal sense as a theorem — `contingent_realm_obtains` proves
it, and only for content; and it does not say the contingent kind of subject is
inhabited, which is exactly the blocked lemma. Reject it and the falsity-world
elimination goes; the attack verdicts and the act-datum are untouched.
Footprint: `{}`. -/
def contingentWorldDatum : Stipulation where
  name := "contingentWorldDatum"
  location := "Entity.lean:46"
  anchor := "def actualWorld"
  tag := StipulationTag.TRANS
  cost := "The world-datum (this world exists, and it is contingent), assumed as given rather than derived: the author stipulates the world the proof is written in exists, and only the consequences are in due. Registered so the world-datum is not silently merged with the performative act-datum in the C.1 preamble. Free in axioms, not free in performance. It eliminates the falsity world read as the actual world (WorldStance.falsityWorldAsActual) and settles that the falsity world is the necessary-subjects-only world; it does NOT reach a world of necessary subjects in general, which needs the BLOCKED contingent-inhabitation lemma, and it does NOT touch plurality (AxTwoNecessaryPersonalCentres is a separate META bridge, C584). Reject it and the falsity-world elimination goes; the attack verdicts stand."
  dependents := ["falsityWorld_holds_no_contingent_subject", "contingentSubject_might_not_have_existed", "nothing_contingent_at_its_actual"]

/-- The registered stipulations, in audit order. -/
def registeredStipulations : List Stipulation :=
  [ofGround_existsAt, ofGround_meansAll, ofGround_noInternalComponents,
   operatesAt_presencePlusObtaining, asietyFreedom_ofGroundFreedom,
   contingentWorldDatum]

end Logos.Stipulations
