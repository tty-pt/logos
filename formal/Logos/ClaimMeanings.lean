/-!
Meanings (EN) for prose claims that have no kernel declaration behind them
(some are deferred/faith rows, some resolve to a spike file outside `Logos/`,
and some are retired/blocked steps under hostile semantics).

These are "def strings": each meaning is the literal value of a `String`
constant, so every English sentence consumed by `DEDUCTION.md` lives in code
and needs no external gloss file.
-/
namespace Logos.ClaimMeanings

def C59 : String := "Strong truth exists: some formula is true in every world (spike-level, axiom-free)."

def F1b : String := "Existence of *genuine choice* has not yet been derived from the performative datum: the explicit target is `genuineChoice_exists := ∃ s, ∃ p q, Chooses s p q` (BLOCKED, no axiom/sorry), via `rejectedHornCoMeant` (nothing forces the performative subject to co-mean the rejected horn, A s p with A s (¬p)). The frontier `genuineChoice_exists → freeWillExists` is free (`freeWillExists_of_genuineChoice`, {Means, Subject} vocab-only); what is blocked is the existence of the genuine chooser, not the implication."

def F2 : String := "Deontic teleology is deferred: how norms point at goals is not yet derived."

def F3 : String := "Moral good from logical normativity is deferred: not yet derived."

def F4 : String := "There are two distinct persons, both lovable, under the two-subjects bridge."

def F5 : String := "Eternal loveship is proven: two distinct persons stand in an eternal love-relation, under the bridges and person-stability."

def F6 : String := "The Trinity is deferred: no argument exists yet."

def F7 : String := "The bipolar half of freedom is subsumed by unary `FreeWill`; the open gap is not 'freedom impossible to derive' but *existence of genuine choice* not yet derived from the performative datum (F1b, `genuineChoice_exists`). World-level `ChoiceAt : World → Subject → Prop → Prop` remains a future, priced SEM vocabulary."

def F8 : String := "The Trinity is not attempted."

def F9 : String := "Incarnation and creation are faith data from the poem, deferred."

def Q7_2 : String := "Research question, answered: the swap is a theorem for atoms (no axiom needed); the compound instance is unforced."

def C19 : String := "There is a necessary reality grounded on the indubitable: some entity existing in every world grounds 'φ or not-φ' under AxGlobalGround."

-- Retired / blocked claims under hostile semantics

def C78 : String := "Contingent ground is retired: manufactured witness destroyed under hostile semantics."

def C79 : String := "Ultimate ground existence is blocked: infinite descending chains have no ultimate element without a well-foundedness axiom."

def C87 : String := "Origin necessity is retired: manufactured origin witness destroyed."

def C88 : String := "Transcendental quantifier swap is retired: uniform necessary ground requires AxGlobalGround."

def C89 : String := "Ultimate ground by initiation is blocked: non-entailed without well-foundedness."

def C90 : String := "Personal ultimate ground is blocked: ultimate grounding does not entail personal nature."

def C69 : String := "Free will of origin is retired: manufactured constructor split destroyed."

def C70 : String := "Posited content non-freedom is retired: manufactured witness destroyed."

def C71 : String := "Origin freedom denial self-refuting is retired: manufactured witness destroyed."

def C72 : String := "Judge is free is retired: act does not entail free will; `judge_commits` yields only the choice field."

def C73 : String := "Plurality without bridges is blocked: unit countermodel settles that 1 act does not entail plurality; requires AxTwoSubjects."

def C75 : String := "Propositional personhood is blocked: content existence does not entail personhood."

def C76 : String := "Canonical rigid love is retired: plurality does not entail love without substantive relational bridges."

def C64 : String := "Movement not transfer is retired: initiation constructor evaluation excised."

def C65 : String := "Person iff originates is retired: manufactured initiation identity excised."

def C66 : String := "Cogito as initiation is retired: manufactured initiation witness excised."

def C67 : String := "Denial of initiation self-refuting is retired: manufactured witness excised."

def C80 : String := "Posited content deterministic transfer is retired: constructor evaluation excised."

def C81 : String := "Origin branching is retired: constructor evaluation excised."

def C82 : String := "Origin initiating person is retired: constructor evaluation excised."

end Logos.ClaimMeanings