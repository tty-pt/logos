/-!
Meanings (EN) for the hostile-semantics countermodels referenced by
`README.md` (Appendix C and the per-claim `Challenge` lines).

Following the rule that every English sentence consumed by the generated
document lives in code, each countermodel carries two accounts: what it
attacks/refutes (`refutes_*`) and what survives it (`survives_*`). These are
"def strings": the literal value of a `String` constant, so no external gloss
file is needed. Keys are stable: the generator's countermodel catalog refers
to them by the base name (`<Key>_refutes` / `<Key>_survives`).
-/
namespace Logos.CountermodelMeanings

-- CountermodelSubjectWithoutPerson / CountermodelNoPerson / not_entails_person

def SubjectWithoutPerson_refutes : String :=
  "A subject of an act need not be a person: if `Person` is an uninterpreted substantive predicate, `Subject → Person` fails as a logical law."

def SubjectWithoutPerson_survives : String :=
  "Under §12 the identity `Person s ↔ ∃ p, Act s p` makes personhood definitional, so the implication holds in Γ by analysis, not by logic."

def NoPerson_refutes : String :=
  "The bare act-datum `∃ s p, A s p` does not force any `Person`."

def NoPerson_survives : String :=
  "Personhood is introduced by the definition of Act (esse est agere), not by the raw datum."

-- CountermodelNoFreeWill / not_entails_decoupled_freewill

def NoFreeWill_refutes : String :=
  "Mere occurrence of an act does not entail genuine choice: an uninterpreted determined act with `Chooses := False` satisfies the datum while `Chooses` and `FreeWill` stay empty."

def NoFreeWill_survives : String :=
  "`Chooses → FreeWill` holds in Γ by definition (`FreeWill s := ∃ p q, Chooses s p q`); the countermodel attacks the existence of genuine choice, not the implication."

-- UnitPluralityCountermodel / not_entails_plurality

def UnitPlurality_refutes : String :=
  "A single act (one subject) cannot force a plurality of subjects: the unit model with `Person := True` satisfies act and personhood but has no second subject."

def UnitPlurality_survives : String :=
  "Plurality rests on `AxTwoNecessaryPersonalCentres` (a necessary ground's freedom to self-give cannot depend on contingent subjects), not on the mere act. World-datum note: the model declares no world sort, so the datum is silent on it — but read with its one subject as of the contingent kind, it *is* a contingent world of one person, and therefore admissible given that the contingent world exists. The world-datum does not touch it; only the plurality bridge separates it from ours."

-- CountermodelContentWithoutPerson / not_entails_content_person

def ContentWithoutPerson_refutes : String :=
  "Propositional existence plus meaning does not entail personhood: `S := Prop`, `Means s p := s = p`, `Person := False`."

def ContentWithoutPerson_survives : String :=
  "Content-existence is a distinct step from personhood; the definitional link `Person s ↔ ∃ p, Act s p` is what Γ uses, not a logical law."

-- CountermodelSubjectNecessityNotEntityNecessity / not_holds_of_arbitrary_signature

def SubjectNecessityNotEntity_refutes : String :=
  "Subject-persistence does not entail entity-necessity by logic alone: the transfer fails with independent persistence/existence predicates."

def SubjectNecessityNotEntity_survives : String :=
  "In Γ `EntityOf` is the entity embedding and `ExistsAt` is one shared relation, so the lift (C91) is definitional, not a logical law."

-- CountermodelPersonNotNecessary / not_entails_person_necessary

def PersonNotNecessary_refutes : String :=
  "A person need not be a necessary subject: `Person → NecessarySubject` fails as a logical law (subject exists only in the `true` world)."

def PersonNotNecessary_survives : String :=
  "Person-persistence holds of the necessary kind (`PersonStabilityPrinciple`, `Love.lean:101`, kind-relative since 2026-09-28); the model exhibits the contingent kind, so within Γ the countermodel stands as the refutation of the unconditional law. What is wrong with it as our world is answered by the kind bridge (C404/C409), not by withdrawing the attack. World-datum note: this is the one catalogued model that demonstrably *satisfies* the world-datum — its `true` world is a contingent world of one person — so the datum gives it nothing and takes nothing from it."

-- CountermodelFalsityWorld / the falsity world read as the actual world

def FalsityWorld_refutes : String :=
  "The all-`TV.f` valuation is not the actual world: `falsityWorld_ne_actualWorld`, plus `falsityWorld_holds_no_contingent_subject` against `contingent_realm_obtains`, which witnesses contingent content in the real one. Refuted for free — no axiom is charged, and no contingent-inhabitation lemma is needed."

def FalsityWorld_survives : String :=
  "The valuation itself survives as a *world*: it is Γ's necessary-subjects-only world, holding every subject of the necessary kind and the ground-constructor, with no contingent subject and no atom. What dies is the reading of it as the actual world. So the falsity world is a coherent world and simply not ours."

-- CountermodelVeridicalMeaning (veridical meaning vs. the choice frontier)

def VeridicalMeaning_refutes : String :=
  "The act-datum does not force `genuineChoice_exists` even under the Logos definition of `Chooses`: veridical meaning makes co-meaning an incompatible pair impossible while the whole agency/choice/order fragment holds."

def VeridicalMeaning_survives : String :=
  "The frontier is not the implication `Chooses → FreeWill` but whether any subject co-means an incompatible horn — the single irreducible resource is `rejectedHornCoMeant` (BLOCKED)."

-- CountermodelPluralityWithoutLove

def PluralityWithoutLove_refutes : String :=
  "Plurality of distinct persons does not entail love: `Bool` with `Person := True` and `Loves := False`."

def PluralityWithoutLove_survives : String :=
  "Love follows in Γ from the definitions plus `AxTwoNecessaryPersonalCentres` — substantive relational bridges, not a logical consequence of plurality."

end Logos.CountermodelMeanings