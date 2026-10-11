# Research Report: Formal and Prose Status of Key Claims (logos repo)

Working directory: /home/quirinpa/logos  
Generated: Thu Oct 08 2026

## Methodology

Read across:
- `formal/GAPMAP.md` (claim ledger/statuses, axiom footprints)
- `formal/Logos/*.lean` (declaration bodies, docstrings, #print axioms context)
- `formal/axiom_audit.json` (authoritative axiom footprints)
- `base.txt`, `theorems/*.txt` (Portuguese prose corpus - canonical per AGENTS.md)
- `README.md`, `investigations/ledger.md`, `investigations/kernel-audit.md` (generated argument/audit)
- `formal/consistency/` (guard; sits outside lean_lib Logos)
- `scripts/build_deduction.py` (how statuses/badges are derived)

---

## 1. "the ground" / Ground / fundament — physicalist atom? axiom or derived?

### Formal characterization (Entity)
- Declaration: `Logos.Entity.Entity` (inductive), constructor `ofGround : Entity` (formal/Logos/Entity.lean:26).  
  Docstring: "world-rigid ground of reality: the only entity whose existence the semantics make invariant across every world (definitional semantic stipulation, VOCAB class — `EntityExistsAt w .ofGround := True`). It is a constructor, not an axiom." (lines 19–25)
- Existence: `EntityExistsAt w (Entity.ofGround) := True` (def, line 66). Also `ExistsAt w e := EntityExistsAt w e`.
- Meaning: `EntityMeans (Entity.ofGround) p := True` for all p (def in RecoveredOntologicalGround/Entity context; see stipulation note below).  
  Note (formal/Logos/Stipulations.lean:95): "Meaning-everything stipulated by match arm (duplicated at NecessaryPersonalGround.lean:155): grounding theorems about ofGround unfold this True." (VOCAB/definitional stipulation class, not a substantive axiom).
- Identity: `ofGround_ne_ofSubject (n s)` in NecessaryPersonalGround.lean:155+ context (see later) establishes `Entity.ofGround ≠ EntityOf s`; `ofAtom_ne_ofSubject` etc. Also `ofGround_not_a_person_correlate` (C564, PROVEN, {Means,Subject,Will,subjectWill} context? ledger says PROVEN, footprint `{Means, Subject, Will, subjectWill}` per GAPMAP C564 row 140 shown above, but the core refutation is constructor no-confusion: `exact ofGround_ne_ofSubject s hs` reduces to `Entity.noConfusion`).

Key canonical theorems (GAPMAP highlights):
- C425 `Precedence.ofGround_precedes_the_right_wrong_distinction` — PROVEN, footprint `{Means, NecessarySubjectKind, Subject}`
- C430 `CosmicExistence.the_ground_is_not_the_universe` — PROVEN, `{NecessarySubjectKind, Subject}`
- C431 `CosmicExistence.grounding_never_yields_identity_of_the_totality` — PROVEN, `{Means, NecessarySubjectKind, Subject}`
- C564 `CosmicExistence.ofGround_not_a_person_correlate` — PROVEN, `{Means, Subject, Will, subjectWill}` (uses `ofGround_ne_ofSubject`)
- C433 `Precedence.ofGround_sole_precedes_right_wrong` — PROVEN↑ (paid by F15/SemanticFinitude + Trinity bridge context), footprint includes `{CL, DivineSubjectRole, Means, NecessarySubjectKind, SemanticFinitude, Subject, TrinitarianPersonalBridge, Will, subjectWill}`
- C439 `DivineSimplicity.divine_simplicity_is_unique_to_the_ground` — PROVEN, `{Means, Subject}`
- C441–C445, C442–C445 PROVEN↑ under SemanticFinitude/F15 (paid) — C441 is the only place paying F15 in that batch (GAPMAP 296)
- C430/C431: use `Universe e := ∀ w x, ExistsAt w x → e = x` and show incompatibility (identity of totality not possible). Also C564 excludes person-correlate.

### Is it a "physicalist atom / physicalist’s atom"?
No such characterization appears anywhere in Lean or prose:
- Entity has `ofAtom (n : Nat)` (non-agent worldly entities) — see Entity.lean:22–29; these are atomic entities in the model (indexed by Nat). Base/prose corpus also uses "átomo" in that technical/model sense (e.g. base.txt 740–749, 1436, 1485–1496, 1668–1714) — a model atom, not a "physicalist atom" as a metaphysical commitment label in the claim set.  
  Search in repo: `grep -rn "physicalist"` returns nothing (see tool call above). Also `grep -rn "physicalist's atom\|physicalist atom"` returns nothing.
- The ground is the distinct constructor `ofGround`, separate from `ofAtom`. C430/C431 explicitly contrast ground vs universe/totality; classical attributes distinguish it (simplicity, pure actuality, aseity, foundational omniscience/omnipotence in the stated senses) — no reduction to physicalist atom is asserted. In fact ground is transcendent relative to atoms/subjects (e.g. C564, C430, DivineSimplicity transcendence lines).

### Axiom or derived?
- `ofGround` is a constructor of an inductive type (Entity.lean:26) — not an axiom statement. The existence/meaning stipulations for it are definitional (match arms / defs). The axiom_audit.json does not list `ofGround` as a declared axiom name; declared axioms are the 40 tagged ones (census shows 40: VOCAB/META/SEM/TRANS).  
- The “ground” as the entity is vocabulary-structural (constructor). Many claims about the ground are theorems: e.g. `ofGround_existsAt_every_world` follows from `EntityExistsAt w .ofGround := True` (definitional). Others are PROVEN or PROVEN↑ depending on whether they need SemanticFinitude/F15 or Trinity/bridges (e.g. sole-bearer theorems pay F15).  
  Examples from GAPMAP: C425 PROVEN; C433 PROVEN↑ (price includes SemanticFinitude, TrinitarianPersonalBridge); C439 PROVEN; C441 PROVEN↑ (only this one pays F15 in that batch). So: the entity constructor/definitional properties are not axiomatic; some uniqueness/characteristic-sole-bearer claims are proven under priced axioms (PROVEN↑) — none are presented as “the ground is physicalist atom”.
---

## 2. "necessary person" / NecessaryPerson / personal necessity — AXIOM vs PROVEN

Key items:
- C404 `Plurality.necessaryPersonalSubjectExists : ∃ s : Subject, NecessarySubjectKind s ∧ Person s` — `Tag: META` (Plurality.lean), listed as AXIOM in GAPMAP (line 26: Status AXIOM, footprint `{Means, NecessarySubjectKind, Subject, Will, subjectWill}`). This is the bridge: the necessary kind is inhabited by a Person.
- C405 `necessaryKindSubject_is_necessary` — PROVEN, `{NecessarySubjectKind, Subject}`
- C407 `necessarySubject_exists` — PROVEN↑, footprint includes `necessaryPersonalSubjectExists` plus vocabulary
- C408 `necessaryPersonalSubject_derived` — PROVEN↑
- C409 `NecessaryPersonalGround.necessary_person_derived_from_bridge : ClaimD_NecessaryPerson` — PROVEN↑ (GAPMAP line 31: "Claim D derivada em vez de anotada"). Definition `ClaimD_NecessaryPerson : Prop := ∃ s : Subject, NecessarySubject s ∧ Person s` (NecessaryPersonalGround.lean:145). Proof obtains witness from C404 via C405.  
  axiom_audit.json footprint for `Logos.NecessaryPersonalGround.necessary_person_derived_from_bridge`: `[Means, NecessarySubjectKind, Subject, Will, subjectWill, Logos.Plurality.necessaryPersonalSubjectExists]` (axiom_audit.json:7842-7850).  
  Also depgraph shows it depends on `Logos.Plurality.necessaryPersonalSubjectExists`.

So:
- The *existential bridge* C404 is marked **AXIOM** (META). 
- The *derived claim* C409 (necessary person exists / Claim D) is **PROVEN↑** under that bridge (it uses `necessaryPersonalSubjectExists` as premise). It is not marked AXIOM; it’s derived once the bridge is given.  
  The prose/ledger states: “Claim D derivada em vez de anotada: a pessoa necessária existe…” (C409).  
- `necessary_normative_order` / related necessity of normative order are PROVEN with 0 substantive axioms (e.g. NecessaryPersonalGround.lean:120–139 shows `theorem necessary_normative_order : NecessaryNormativeOrder := fun _w => objective_normative_order_holds` with status PROVED 0 substantive axioms). That’s different from “a necessary person exists” (personal necessity).  
- Also `AxTwoNecessaryPersonalCentres` (`Tag: META`, C584) appears elsewhere (e.g. Trinity/plurality contexts) — separate bridge (two necessary personal centres). C404 is the single bridge for “the necessary kind is inhabited by a Person”; C409 derives Claim D from C404.

Summary for (2):
- `Plurality.necessaryPersonalSubjectExists` (C404) — **AXIOM** (META)
- `NecessaryPersonalGround.necessary_person_derived_from_bridge` (C409) — **PROVEN↑** (derives Claim D using C404)
- No declaration named `NecessaryPerson` as an axiom in the scanned files; ClaimD_NecessaryPerson is a def and C409 is the derived instance. The “necessary person” existential is derived under the META bridge, not itself declared AXIOM.

---

## 3. Free will — declarations about free will existing (FreeWill, voluntas, libera voluntas)

### Core formal definitions (Choice.lean)
- `FreeWill (s : Subject) : Prop := ∃ p q : Prop, Chooses s p q` (def, ~line 184–195 in Choice.lean context shown). Docstring states: “freedom is DEFINITIONAL (`FreeWill s := ∃ p q, Chooses s p q`)”.  
- `Chooses (s : Subject) (p q : Prop) : Prop := Means s p ∧ Means s q ∧ Incompatible p q` (def, ~line 149–158). Stronger than `ChoiceField`.
- `FreeSubject (s : Subject) := FreeWill s` (def, line 196–197), with `freeSubject_iff_freeWill` (rfl).
- Existence theorems:
  - `freeWillExists_of_genuineChoice : genuineChoice_exists → ∃ s : Subject, FreeWill s` (PROVEN, footprint `{Means, Subject}` by VOCAB; line ~263–280 in Choice.lean shown)
  - `rejectedHornCoMeant_implies_genuineChoice` and `freeWillExists_of_chooses` chain
  - Also unconditional existence from performative datum via priced routes in ActCascade:  
    - C477 `ActCascade.freeWill_exists_of_act_datum_constitutive : ∃ s : Subject, FreeWill s` — PROVEN↑, footprint `{AxIntentionalChoice, performative_act_datum, Initiates, Means, State, Subject}` (ledger 4121). Status PROVEN↑ (rests on `AxIntentionalChoice` SEM).  
    - C478 `ActCascade.freeWill_exists_of_act_datum_polarity` — PROVEN↑ under `AxActPolarity` (SEM).  
  - C479 is `freeSubject_exists_of_act_datum` (exists free subject) — PROVEN↑ under AxIntentionalChoice (ledger 4123), and `FreeSubject` is defined as `FreeWill`.

Also in AsieticChoice/other places: `freeWill_exists` derived under `AxTwoNecessaryPersonalCentres` (META) in certain routes (e.g. AsieticChoice lines ~601–635 show footprints including AxTwoNecessaryPersonalCentres) — so “free will exists” appears as PROVEN↑ under different priced axioms depending on route (SEM routes from performative datum: AxIntentionalChoice/AxActPolarity; or META route via plurality/centres in AsieticChoice context).

Search for Latin terms: `voluntas`, `libera voluntas` — grep across repo returned no matches in Lean/prose files (the tool call showed no hits in base.txt/theorems/*.txt). So formal claims use `FreeWill`/`FreeSubject`/`Chooses`.

### Status summary (free will existing)
- The *concept* `FreeWill` is definitional (not an axiom). 
- Unconditional existence `∃ s : Subject, FreeWill s` is **PROVEN↑** in the routes that are presented as the argument chain (priced). Specifically:  
  - C477: PROVEN↑ via `AxIntentionalChoice` (SEM)  
  - C478: PROVEN↑ via `AxActPolarity` (SEM)  
  - Also there is a route under `AxTwoNecessaryPersonalCentres` (META) in AsieticChoice (C278 context) giving `freeWill_exists` at footprint including AxTwoNecessaryPersonalCentres.  
- There is no declaration where `FreeWill` itself is marked AXIOM; it’s always defined or derived. The existence claims carry priced axioms (SEM/META) depending on route — hence PROVEN↑, not plain PROVEN.

---

## 4. "Free Subject" / SubjectLibre / free subject existence

Definitions:
- `FreeSubject (s : Subject) := FreeWill s` (Choice.lean 196–197) — definitional equality with FreeWill.
- `freeSubject_iff_freeWill s` is `Iff.rfl` (199).
- Existence:  
  - C479 `ActCascade.freeSubject_exists_of_act_datum : ∃ s : Subject, FreeSubject s` — PROVEN↑ under `AxIntentionalChoice` (ledger 4123). ClaimMeaning C479 states “FreeSubject is DEFINED as FreeWill, so this is C477 under the corpus’s third name…” and displayed AXIOMATIC (AxIntentionalChoice).  
  - `Choice.freeSubject_exists` theorem exists (e.g. line ~1101 in Choice.lean shows `theorem freeSubject_exists (h : ∃ s : Subject, ∃ p : Prop, Act s p) : ∃ s : Subject, FreeSubject s := ...` depending on context) and also AsieticChoice gives `freeSubject_exists` under AxTwoNecessaryPersonalCentres.
- Search for `SubjectLibre`/`libera` (Latin forms) — no matches found. So corpus uses `FreeSubject`.

Status: definitional (not axiom); existence is **PROVEN↑** under priced axioms (same routes as FreeWill). No declaration marks FreeSubject as AXIOM.

---

## 5. Other closely-related claims (candidates for “etc.”)

Look for existentially-asserted claims where prose might say AXIOM but kernel says proven or vice versa:

### (a) Two necessary personal centres / plurality bridge
- `AxTwoNecessaryPersonalCentres` is a declared axiom: `Tag: META` (e.g. in TwoNecessaryPersonalCentres.lean, also listed in axiom registry). C584 is associated with it. Status in GAPMAP as axiom where declared? Declared axioms are `AXIOM` type in the ledger sense for the axiom declaration itself; theorems using it become PROVEN↑. Yes.

### (b) Necessary personal kind inhabited (the bridge)
- C404 `necessaryPersonalSubjectExists` — **AXIOM** (META). This is explicitly marked AXIOM in GAPMAP. Kernel derivations consume it (C407–C409). So prose/ledger correctly marks bridge as AXIOM and derivatives as PROVEN↑.

### (c) C409 moved from “annotated only” to derived
- As above, GAPMAP C409 explicitly says “Claim D derivada em vez de anotada…” and status is **PROVEN↑**. Formal proof exists in NecessaryPersonalGround.lean:161–165. Footprint includes `necessaryPersonalSubjectExists`. So kernel says derived (under axiom) — which matches GAPMAP (PROVEN↑). No contradiction.

### (d) F1b/F1bUncond history (mentioned in ClaimMeanings)
- ClaimMeanings.lean:34 states F1bUncond superseded: “the unconditional existence of a free subject is no longer an open frontier, it is a theorem…” and refers to C278 in AsieticChoice (freeWill_exists) under `AxTwoNecessaryPersonalCentres`. Also GAPMAP shows dissolved claims (build_deduction reports “8 claims dissolved into a canonical claim: F1bUncond→C587…”). So former frontier (possibly annotated as open) became a theorem under priced axiom — status moved accordingly. This matches the sync rule (formal changed → prose/ledger updated).

### (e) Countermodels and boundaries (not existential claims of Γ, but independence)
- C453/C462 etc appear as COUNTERMODEL boundaries in some contexts (GAPMAP shows COUNTERMODEL status for C453). These are not “asserted to exist” by Γ; they mark non-consequences. The build_deduction dry-run also cleared 39 unresolvable lean_ref scraped from prose cells (including C453,C462) — that’s a generated artifact hygiene note, not a logical contradiction.

### (f) Other existentially-asserted, possibly priced
- Production/causal production: F10 was BLOCKED, later became C493 `ground_produces_every_satisfiable_form` declared as `Tag: META` (axiom) — GAPMAP/notes say “F10 is now AXIOM” in that sense? Wait, base.txt/GAPMAP note around 1448+ (divine omnipotence section): “Actualizado 2026-09-29: (i) was delivered by C463 (`Tag: VOCAB`) and (ii) was declared — not derived — by C493 (`ground_produces_every_satisfiable_form`, `Tag: META`); F10 is now `AXIOM`…” So the claim about causal/creative production (bringing satisfiable to existence in that sense) is declared as a META axiom (C493), not derived. That’s explicitly marked.
---

## 6. How statuses are derived (build_deduction.py)

From the codebase (build_deduction.py):
- `classify_proof_edge(proof, ...)` returns `(category, display_badge)`:
  - If `proof.boundary` set → `("COUNTERMODEL", "COUNTERMODEL | left ⇏ right")`
  - If `kind in ("def","structure")` → `("DEFINITIONAL", "DEFINITIONAL")`
  - Look up local axioms in footprint and check their registry tags: collect `local_meta` where tag==`META`, `local_sem` where tag==`SEM` (by axiom short name).  
    - if local_meta non-empty → `("METAPHYSICAL", f"AXIOMATIC ({req})")` (display says AXIOMATIC naming the axiom(s))  
    - if local_sem non-empty → `("SEMANTIC", f"AXIOMATIC ({req})")`  
    - else → `("PROVEN", "PROVEN | 0 substantive axioms")`
- The *category* keeps legacy strings (`SEMANTIC`/`METAPHYSICAL`) for tooling; *display* says `AXIOMATIC (AxName)`. The comment states: “AXIOMATIC never means ‘unproved’ — it means machine-verified while resting on the named, priced axiom.”
- `compute_price_lines(...)` / `compute_epistemic_badge(...)` derive price from the same selection (one source of truth). Badge/price derived from the audited footprint + registry tags.
- Statuses in GAPMAP/ledger come from kernel: GAPMAP columns are Status and Pegada (footprint). The build script reads GAPMAP, depgraph, axiom_audit.json, and Lean declarations to render README/ledger/kernel-audit. It does not transcribe badges arbitrarily — they’re derived.
- Chain lists (e.g. `ASIETY_FREEDOM_STEPS`) have membership maintained by hand (the script warns: adding declaration to chain module doesn’t add to README unless extended in that list). That’s a presentation-maintenance note, not how kernel status is derived.
- The axiom registry is built from Lean docstrings (Tag: VOCAB/SEM/META/TRANS) — 40 axioms total, census enforced by `test_axiom_census.py`.

Also AGENTS.md notes: “Statuses are derived, never transcribed: each step's badge is a pure function of (kernel node kind, audited #print axioms footprint, declared axiom Tag:). The GAPMAP status/footprint cells are checked against the derived values, never used as their source.”

So for a theorem declaration T:
- If it’s a `def`/`structure` identity in effect → DEFINITIONAL
- If it uses any declared axiom with Tag META → category METAPHYSICAL, display AXIOMATIC (<META axiom names>)
- If only SEM → SEMANTIC, display AXIOMATIC (<SEM axiom names>)
- If no substantive axioms (only CL/vocab as appropriate per audit) → PROVEN
- Boundaries → COUNTERMODEL

GAPMAP’s Status column (PROVEN/PROVEN↑/AXIOM/BLOCKED/DEFERRED) is the ledger status; reader-facing display collapses PROVEN↑ to AXIOMATIC with the named axiom on the price line (as above). AXIOM in GAPMAP means the claim itself is a declared axiom (e.g. C404 `necessaryPersonalSubjectExists` is AXIOM; C409 is PROVEN↑).

---

## 7. Sanctioned workflow for changing status (AGENTS.md sync rule)

Key points from AGENTS.md “Sync rule (mandatory)”:
- The prose corpus (`base.txt`, `theorems/*.txt`, `poem.txt`) is canonical and **must always reflect the current formal status** produced by Lean in `formal/`.
- Whenever formalization changes:
  - new theorem verified → create/update matching theorem file (`theorems/T*.txt`) with `Depends on:` listing exact Lean file and its axiom footprint
  - step demoted to axiom → mark it `AXIOM` in prose (`base.txt`/relevant `T*.txt`); never let prose keep presenting as derived; record consistency-model note
  - step blocked / still requires proof → record exact missing lemma (formal statement) in prose “still requires proof” list
  - new file added → update dependency lines and section references in `base.txt` and theorem files
- Only something already machine-verified (or explicitly tagged axiom) may be called “derived”/“undeniable” in prose.
- Practice: after each milestone, re-read affected prose and patch so prose and Lean ledger agree (see `formal/GAPMAP.md`).
- README/ledger are generated by `scripts/build_deduction.py` (never edit by hand). Regeneration workflow (canonical):
  ```sh
  export PATH="$HOME/.elan/bin:$PATH"
  cd formal && lake exe depviz --roots Logos --json-out depgraph.json --dot-out depgraph.dot
  cd .. && python3 scripts/audit_footprints.py && python3 scripts/audit_goals.py && python3 scripts/build_deduction.py
  ```
- Consistency gates: `scripts/check_consistency.py` fails if kernel derives `False`. Also axiom census is gated by `scripts/test_axiom_census.py` (40 axioms pinned in that sense; audit sizes move). Tests `test_goal_audit.py`, `test_argument_surface.py`, `ledger_superset.py` enforce contracts.

Workflow summary:
1. Change Lean (`formal/Logos/*.lean`) — add theorem/axiom, change status.
2. Regenerate audits: build depgraph (if deps changed), run `audit_footprints.py`, `audit_goals.py` (produce axiom_audit.json, goal_audit.json).
3. Update GAPMAP if needed to reflect new claim IDs/status/footprints (GAPMAP is the theorem ledger). 
4. Run `build_deduction.py` to regenerate README, investigations/ledger, kernel-audit, catalogues (machine-generated).
5. Update prose corpus (`base.txt`, `theorems/*.txt`) to match formal status exactly (add T*.txt, update Depends on, mark AXIOM if demoted, record missing lemma if blocked). Never call machine-unverified “derived”.
6. Verify gates: `test_axiom_census.py`, `test_goal_audit.py`, `test_argument_surface.py`, `ledger_superset.py`, `check_consistency.py` as applicable. If any fail, fix root cause (do not delete assertions to green unless the assertion was wrong by the stated rule).
7. Only then commit if explicitly requested (git rules apply).

Key constraint: prose is canonical in Portuguese but must track formal status; generated surfaces are never hand-edited.

