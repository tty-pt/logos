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

-- CountermodelActWithoutSubject (Lichtenberg's objection)

def ActWithoutSubject_refutes : String :=
  "Without a constitutive rule, an act can occur in the void with no actualizing subject (Lichtenberg's objection)."

def ActWithoutSubject_survives : String :=
  "In Γ the Act relation is constitutive — `Act s p → Subject s` by definition — so the void-act is no countermodel to the formal implication."

-- CountermodelWeakActWithoutMeaning / not_entails_strong_act

def WeakActWithoutMeaning_refutes : String :=
  "A performed event (utterance, keystroke, physical emission) does not entail an intentional meaning-act: `act s p` can occur without `Means s p`."

def WeakActWithoutMeaning_survives : String :=
  "The weak retorsion proves directly only that an act-event occurs; the step from event to meaning requires the explicit intentionality bridge `weak_act_implies_strong_act`."

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
  "Plurality rests on `AxTwoSubjects` (the reality of right-and-wrong demands two subjects), not on the mere act."

-- CountermodelContentWithoutPerson / not_entails_content_person

def ContentWithoutPerson_refutes : String :=
  "Propositional existence plus meaning does not entail personhood: `S := Prop`, `Means s p := s = p`, `Person := False`."

def ContentWithoutPerson_survives : String :=
  "Content-existence is a distinct step from personhood; the definitional link `Person s ↔ ∃ p, Act s p` is what Γ uses, not a logical law."

-- CountermodelWorldwiseTruthmaking (worldwise ≠ uniform ground)

def WorldwiseTruthmaking_refutes : String :=
  "Worldwise truthmaking does not entail a uniform necessary ground: the `Bool` model has `∀ w ∃ e` with `ExistsAt w e := e = w` but no entity present in every world."

def WorldwiseTruthmaking_survives : String :=
  "For atoms the swap is a theorem without axioms; the compound/global instance is exactly what `AxGlobalGround` supplies."

-- CountermodelSubjectNecessityNotEntityNecessity / not_holds_of_arbitrary_signature

def SubjectNecessityNotEntity_refutes : String :=
  "Subject-persistence does not entail entity-necessity by logic alone: the transfer fails with independent persistence/existence predicates."

def SubjectNecessityNotEntity_survives : String :=
  "In Γ `EntityOf` is the Truthmaker embedding and `ExistsAt` is one shared relation, so the lift (C91) is definitional, not a logical law."

-- CountermodelPersonNotNecessary / not_entails_person_necessary

def PersonNotNecessary_refutes : String :=
  "A person need not be a necessary subject: `Person → NecessarySubject` fails as a logical law (subject exists only in the `true` world)."

def PersonNotNecessary_survives : String :=
  "Person-persistence is definitional (esse est agere, `AxPersonStability`), and `Love.no_contingent_person` shows the concrete refutation cannot exist in Γ."

-- CountermodelVeridicalMeaning (veridical meaning vs. the choice frontier)

def VeridicalMeaning_refutes : String :=
  "The act-datum does not force `genuineChoice_exists` even under the Logos definition of `Chooses`: veridical meaning makes co-meaning an incompatible pair impossible while the whole agency/choice/order fragment holds."

def VeridicalMeaning_survives : String :=
  "The frontier is not the implication `Chooses → FreeWill` but whether any subject co-means an incompatible horn — the single irreducible resource is `rejectedHornCoMeant` (BLOCKED)."

-- CountermodelInfiniteGroundChain

def InfiniteGroundChain_refutes : String :=
  "A strict partial order need not have an ultimate element: descending infinite chains in `Int` have none."

def InfiniteGroundChain_survives : String :=
  "Γ never claimed order-theoretic well-foundedness; the missing assumption (if adopted) would be a further axiom, not a hidden theorem."

-- CountermodelImpersonalUltimateGround

def ImpersonalUltimateGround_refutes : String :=
  "Existence of an ultimate ground does not entail that it is personal: `Personal := False` coexists with an ultimate element."

def ImpersonalUltimateGround_survives : String :=
  "Personal grounding is the content of `AxPersonalGround` (T8), a META bridge whose cost is explicit, not a consequence of grounding alone."

-- CountermodelPluralityWithoutLove

def PluralityWithoutLove_refutes : String :=
  "Plurality of distinct persons does not entail love: `Bool` with `Person := True` and `Loves := False`."

def PluralityWithoutLove_survives : String :=
  "Love follows in Γ from the definitions plus `AxTwoSubjects` — substantive relational bridges, not a logical consequence of plurality."

end Logos.CountermodelMeanings