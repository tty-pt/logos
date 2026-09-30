"""Author the READINGPATH.md reading-path fields into formal/presentation_spine.json.

Not part of the generator: a one-shot authoring script, run once, kept so the
prose it wrote is auditable in the repository rather than living only in a shell
history. Every `summary_short` / `*_short` / `disclosure` string here is prose
(a human author's judgement); every *status* in the rendered output is derived
from the kernel by scripts/build_deduction.py and is never written here.
"""
import json
import pathlib

P = pathlib.Path(__file__).resolve().parents[1] / "formal" / "presentation_spine.json"
d = json.loads(P.read_text(encoding="utf-8"))

# --- 1. the two-tier policy -------------------------------------------------
d["presentation_policy"] = {
    "audience": "argument",
    "ledger_target": "investigations/ledger.md",
    "include_main_spine": True,
    "include_detailed_appendix": False,
    "include_countermodels_appendix": False,
    "include_frontiers_appendix": True,
    "investigations_directory": "investigations",
    "dedupe_shared_definitions": True,
    "include_full_pushback": False,
    "include_summary_full": False,
    "include_natural_deduction": False,
    "include_definitions": False,
    "include_supporting_infrastructure": False,
    "include_obstruction_details": False,
    "include_subsections": False,
    "include_frontier_list": False,
    "include_attributes_table": False,
    "include_synthesis_paragraph": False,
    "include_chart_art": False,
}

# --- 2. per-step reading-path prose ----------------------------------------
# `summary_short`  : the claim the reader takes away from the step (≤300 chars,
#                    always carrying a Lean anchor, per the AGENTS.md facade rule)
# `pushback_short` : the skeptic's move, one line
# `reply_short`    : the reply, one line
# `disclosure`     : the price that must not be lost when the section is
#                    compressed — the load-bearing disclosures of READINGPATH.md §5
SHORT = {
    "right_wrong": {
        "summary_short": "Right and wrong both obtain: the binary normative distinction is real (`¬N_T ∧ ¬N_F`). `Right`/`Wrong` here are the objective truth/correctness polarity, not moral good/evil — that is a separate, separately-priced layer.",
        "pushback_short": "Deny Right/Wrong at all — adopt NoRight, claiming 'there is no correct standard' as if that were itself correct.",
        "reply_short": "Retorsive: claiming the denial as *correct* while it is true is a constructive contradiction. Downplaying to a bare assertion forfeits the claim to correctness.",
        "disclosure": "the extensional distinction (`¬N_T ∧ ¬N_F`) and the agential stance-conditional form (`RightWrong s`) are **two different formal objects**; only the second needs a subject. The moral pole is a separate, priced layer — see the attributes table.",
    },
    "ought": {
        "summary_short": "Objective correctness determines agential standards: `Ought` vs. `Ought-Not`. Under the objective epistemic `TruthNorm`, correct judgment implies what the subject ought to affirm, and incorrect judgment what it ought not to.",
        "pushback_short": "'Ought' is nothing but a relabel of 'correct' — no genuinely normative force is added.",
        "reply_short": "The deontic opposition is *derived* under `TruthNorm` (correct → ought to affirm; incorrect → ought not), so it is a new relation, not a relabel. The irreducible practical Ought of *actions* stays a separate primitive.",
    },
    "choice": {
        "summary_short": "Apprehending incompatible alternatives within a committed stance constitutes Choice: the agent co-means both horns (`Chooses s p q`) while committing to one. `FreeWill s := ∃ p q, Chooses s p q` is definitional — commitment is *not* inside `Chooses`.",
        "pushback_short": "Genuine Normativity is a stipulation — the chain GN → Chooses → FreeWill may be valid but empty.",
        "reply_short": "Retorsive: claiming the denial of genuine normativity *as correct* (`ClaimsCorrect s NoGN`) yields a term of the identical GenuineNormativity structure — `denial_of_genuine_normativity_is_self_refuting`.",
        "disclosure": "the retorsion block is a **supporting investigation**, not the load-bearing step. The load-bearing step is the axiom-free stance-level derivation, which does not presuppose the conclusion.",
    },
    "free_will": {
        "summary_short": "We did not assume a free subject. Free Will is **derived**, not assumed: from the reality of genuine normative address and rational choice it follows by pure logic, with zero substantive axioms (`indubitable_normative_free_will`).",
        "pushback_short": "You assumed freedom — a free will was smuggled in as a premise.",
        "reply_short": "The starting point is normative *address*, not a free subject. Freedom is the conclusion of the chain, and the chain is axiom-free.",
        "disclosure": "the chain starts from the **declared** act-datum C454 (axiom 28, `Tag: TRANS`, the one performative price in the series). Citing the free-will rows as evidence for the datum would be circular — see the epistemics section.",
    },
    "free_subject": {
        "summary_short": "A subject is definitionally a free subject iff it possesses free will (`FreeSubject(s) ↔ FreeWill(s)`, `Iff.rfl`). The recognition runs strictly **forward**: free will first, the free subject only after it.",
        "pushback_short": "A definitional manoeuvre — the free subject is bought by a definition, not proven.",
        "reply_short": "Precisely — the 'manoeuvre' *is* the theorem. The equivalence is `Iff.rfl`, which is exactly why nothing can get in front of free will.",
    },
    "person": {
        "summary_short": "A free subject is constitutively an authoritative Person. `Person s := ThomisticPersonCore s` — the classical Boethius–Aquinas criterion of an individual substance of a rational nature with dominion over its own acts.",
        "pushback_short": "A loaded, theological word smuggled into the deduction.",
        "reply_short": "Classical, not novel: the term follows Boethius and Aquinas rather than theological invention. Nothing theological is *assumed*; theology enters only downstream, in the branches — and is there bounded by countermodels.",
        "disclosure": "minimal personhood in Γ is **functional**, not psychological. `faithful_model_satisfies_free_will_without_opaque_person` is a countermodel satisfying free will with substantive psychological personality removed, so §6 does **not** establish a mind, a body or a stream of experience.",
    },
    "personal_will": {
        "summary_short": "Distinct persons have numerically distinct wills. By the law of numerical individuation, `subjectWill s₁ ≠ subjectWill s₂`; a Person is constitutively a subject with an independently individuated will.",
        "pushback_short": "Two persons could share one will — individuation is not forced.",
        "reply_short": "Individuation is a constitutive meaning-postulate, not a derived construction: `will_individuation` is a **declared** injectivity law, not a theorem. Given it, `Person ↔ FreeIndependentWill` follows with 0 substantive axioms.",
        "disclosure": "`will_individuation` is a **declared VOCAB law, and it is kernel-checked as underivable**: the hostile model `Subject := Bool`, `subjectWill := fun _ => ()` satisfies the pre-will spine and there the law arrives at a contradiction. It is a price, paid openly.",
    },
    "ground_right_wrong": {
        "summary_short": "Personal free agency ontologically grounds the normative order: the ground of objective normativity is **personal in kind**. Grounding is neither identity nor individual causation — `RightWrong s → Person s` says who grounds it, not what produced it.",
        "pushback_short": "Principle-of-Sufficient-Reason smuggling: this makes the Person (or the argument) the causal creator of morality.",
        "reply_short": "Grounding ≠ identity and ≠ causation. The bare ought survives the impersonal model; the personal ground is forced *within* the normative order, and the countermodel marks exactly what the antecedent does and does not reach.",
    },
    "necessary_truth": {
        "summary_short": "The objective logical and normative order entails necessary truth: `∃ τ, □ τ` (`Semantics.strongTruthExists`, C59, footprint `{CL}`).",
        "pushback_short": "Quietly assumes modal metaphysics — necessity is a contested fragment, not a consequence.",
        "reply_short": "This is the *logical* continuation of the classical meta-logic in Core/Semantics, not a theorem derived from the normative chain. The normative world-level continuation is recorded separately and never claimed to entail `∃ τ, □ τ`.",
        "disclosure": "§9 is a **separate logical continuation**, not a link in the normative chain. Do not read the ten steps as one derivation: the normative run is §1–§8 and §10; §9 runs on `{CL}` alone.",
    },
    "constructive_personal_ground": {
        "summary_short": "The machine-proved dependence: wherever Right/Wrong is real, its ground-type is personal — `∀ s, RightWrong s → Person s`, via the priced discovery theorem. The constructive form needs no grounding axiom: `ObjectiveNormativity → ∃ p, Person p` is discovery, and the type-personalness is a theorem, never a record field.",
        "pushback_short": "You still quietly pick a contingent author of morality — some particular person who happens to ground Right/Wrong.",
        "reply_short": "The indexing encodes *dependence without nomination*: RightWrong is indexed by a personal kind, not by an arbitrary contingent individual. Which particular person — and whether there is only one — is not claimed.",
        "disclosure": "the ground of Right/Wrong is personal **in kind**; no individual is nominated, and no numerical claim is made. That the person-level *monotheism* step is `BLOCKED` (C228) is stated in the boundaries section below.",
    },
}

for node in d["spine_nodes"]:
    node.update(SHORT[node["id"]])

# --- 3. the reading-path sections that are not spine steps -----------------
# `body` is authored prose carrying explicit C-ids (the AGENTS.md facade rule);
# `claims` names the rows whose status is rendered DERIVED from the kernel.
d["reading_sections"] = [
    {
        "id": "epistemic_closure",
        "title": "11. The Empty-World Closure (C553–C562)",
        "body": [
            "This is the newest and load-bearing batch, and it is what the deduction is "
            "*for*. **Meaningless worlds are excluded — not argued away, unintelligible as "
            "states.** Nothing can be epistemologically right or wrong without a Free being "
            "**for which meaning can mean** (C553, the FACT, `{}` — zero substantive axioms).",
            "The chain is short. The order needs meaning, and meaning needs a subject "
            "(C556) — so the *act datum is entailed by the order* rather than stipulated "
            "(C557), which is why C553 is free. A meaningless world's denial, voiced as a "
            "**judgment**, requires a Free Subject (C558). With no meaning subject there is "
            "no epistemic right/wrong anywhere (C560), and the retorsion against 'there is "
            "no meaning' is itself a term of the same structure (C561). Being true is being "
            "true **to**: `Correct → TrueTo → T` (C562).",
            "Two disciplines keep this honest, and both cut against the reading that would "
            "make the batch sound stronger than it is. **C294 is true at another level:** the "
            "Prop-level `¬N_T ∧ ¬N_F` needs no subject at all, because satisfaction is free "
            "and only *disclosure* needs someone — so the earlier result is not refuted, it "
            "is levelled. **C559 (C552 in the ledger):** Γ's core vocabulary (`Subject`, "
            "`Prop`, `State`, `Means`, `Initiates`) contains no `World` sort, so no "
            "expression of Γ denotes a world-state — a signature model (M0, M1, M6) is "
            "never a candidate state, only a witness about a signature. A model is not a "
            "state of affairs.",
        ],
        "claims": ["C553", "C554", "C555", "C556", "C557", "C558", "C559", "C560", "C561", "C562"],
    },
    {
        "id": "necessary_ground",
        "title": "12. The Necessary Ground, and Where Necessity Stops Working",
        "body": [
            "`Entity.ofGround` is necessary and the **sole universal modal ground**, on one "
            "declared VOCAB bound (`SemanticFinitude`: no subject means every proposition). "
            "From it follow aseity, simplicity, pure actuality, foundational "
            "omnipresence/omniscience/omnipotence, immutability, and everlasting/atemporal — "
            "the last two as definitional corollaries of world-rigid existence, with **no "
            "temporal premise imported**. The **person** side needs exactly one `META` "
            "bridge, C404 `necessaryPersonalSubjectExists`.",
            "Two results cut **against** the classical reading, and the theory reports them "
            "itself. Immutability is not sole-bearing (C453, C489). And the ground is **not "
            "the only necessary being** (C494), so necessity is precisely the one "
            "characteristic that does **not** pick the ground out (C495): the extensional "
            "reading of *ST* I q.19 a.4 is refuted by a countermodel, not left open.",
        ],
        "claims": ["C404", "C453", "C489", "C494", "C495"],
    },
    {
        "id": "instrument_limits",
        "title": "13. What the Instrument Cannot See",
        "body": [
            "`#print axioms` reads the kernel's dependency graph. It cannot see a **`def` "
            "used as a premise by name** — and the census below counts every such inherited "
            "bridge, the theorems it underwrites, and how many have been reviewed. A `✅` "
            "badge therefore means *kernel-verified conditional on a bridge the kernel does "
            "not charge*. This is disclosure, not payment: nothing here is promoted to a "
            "declared axiom, and the three-way decision (promote / declare / retire) is "
            "still open.",
        ],
        "def_bridge_census": True,
    },
    {
        "id": "boundaries",
        "title": "14. What Is Not Established",
        "body": [
            "Named, not implied. The person bridge — person-level **monotheism** — is "
            "`BLOCKED` (C228): the missing lemma is a personal identification principle, and "
            "the ground's personalness in kind does not deliver numerical uniqueness. "
            "**Trinity**, **contingent creation as production**, and **Incarnation** are "
            "`⏸` or `🧱`, not derived. Contingent creation *as existence* is no longer among "
            "them: it is a free theorem (C350, `{}`, witnessed by an atom); only the realm's "
            "*content* is priced, on an exhibited contingent person (C367).",
            "So the cost was relocated, and then for existence itself dissolved — but the act "
            "was never ours to claim, and nothing above should be read as claiming it.",
        ],
        "claims": ["C228", "C350", "C367"],
    },
]

P.write_text(json.dumps(d, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
print(f"wrote {P} ({len(P.read_text(encoding='utf-8').splitlines())} lines)")
