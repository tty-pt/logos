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

/-- Classification tag of a stipulation (closed vocabulary, as for axioms). -/
inductive StipulationTag where
  | VOCAB
  | SEM
  | META
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

/-- The registered stipulations, in audit order. -/
def registeredStipulations : List Stipulation :=
  [ofGround_existsAt, ofGround_meansAll, ofGround_noInternalComponents,
   operatesAt_presencePlusObtaining, asietyFreedom_ofGroundFreedom]

end Logos.Stipulations
