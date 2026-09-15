/-
# Logos.Agency — Level 2a: the act, its subject, its content (base.txt §1–§2, T1–T2, T4)

The single irreducible premise of the whole system is the performative datum
of §1: the present act of reasoning is *given*, not inferred. It is declared
once, as `cogito`, tagged TRANS, and every later theorem carries it in its
footprint (see GAPMAP.md).
-/

import Logos.Core

namespace Logos.Agency

open Logos.Core (T)

/-- Subjects: that which performs acts of reasoning. -/
axiom Subject : Type

/-- `A s p`: subject `s` performs the act with propositional content `p`. -/
axiom A : Subject → Prop → Prop

/-- Existence predicate: `Exists s` (propositional form of "s exists"). -/
axiom Exists : Subject → Prop

/-- Content-ness: `Content p` — p is (a) a propositional content. -/
axiom Content : Prop → Prop

/-- Agency: `Agent s`. -/
axiom Agent : Subject → Prop

/-- cogito (TRANS): the present act is the given datum, not an inference. -/
axiom cogito : ∃ s : Subject, ∃ p : Prop, A s p

/-- An act entails a subject that exists (relational act, §1/T1). -/
axiom act_implies_exists : ∀ {s : Subject} {p : Prop}, A s p → Exists s

/-- An act entails content (nothing is asserted without something asserted, T2). -/
axiom act_implies_content : ∀ {s : Subject} {p : Prop}, A s p → Content p

/-- An act entails an agent (T4, §12). -/
axiom act_implies_agent : ∀ {s : Subject} {p : Prop}, A s p → Agent s

/-- T1 — the subject of the present act exists. -/
theorem T1_subjectExists : ∃ s : Subject, Exists s := by
  obtain ⟨s, _, ha⟩ := cogito
  exact ⟨s, act_implies_exists ha⟩

/-- T2 — there is propositional content. -/
theorem T2_contentExists : ∃ p : Prop, Content p := by
  obtain ⟨_, p, ha⟩ := cogito
  exact ⟨p, act_implies_content ha⟩

/-- T4 — the subject is an agent. -/
theorem T4_agentExists : ∃ s : Subject, Exists s ∧ Agent s := by
  obtain ⟨s, _, ha⟩ := cogito
  exact ⟨s, act_implies_exists ha, act_implies_agent ha⟩

end Logos.Agency

-- Axiom footprint audit
#print axioms Logos.Agency.T1_subjectExists
#print axioms Logos.Agency.T2_contentExists
#print axioms Logos.Agency.T4_agentExists