from pathlib import Path

source_file = Path("/home/quirinpa/logos4/OntologicalIncompletenessTheorem.lean")
formal_dir = Path("/home/quirinpa/logos4/formal")
logos_dir = formal_dir / "Logos"
logos_dir.mkdir(parents=True, exist_ok=True)

with open(source_file, "r", encoding="utf-8") as f:
    orig_lines = f.readlines()

# Find where 'open Classical' is
idx = 0
for i, line in enumerate(orig_lines[:10]):
    if line.strip() == "open Classical":
        idx = i + 1
        break

rest_lines = orig_lines[idx:]

preamble_lines = [
    "import Lean\n",
    "\n",
    "open Classical\n",
    "\n",
    "namespace Logos\n",
    "\n",
    "namespace Agency\n",
    "axiom Subject : Type\n",
    "axiom State : Type\n",
    "axiom Means : Subject → Prop → Prop\n",
    "axiom Initiates : Subject → State → State → Prop → Prop\n",
    "\n",
    "def Act (s : Subject) (p : Prop) : Prop :=\n",
    "  Means s p ∧ ∃ w w' : State, Initiates s w w' p\n",
    "end Agency\n",
    "\n",
    "namespace Alternatives\n",
    "def Incompatible (p q : Prop) : Prop := ¬ (p ∧ q)\n",
    "end Alternatives\n",
    "\n",
    "namespace Choice\n",
    "def Chooses (s : Logos.Agency.Subject) (p q : Prop) : Prop :=\n",
    "  Logos.Agency.Means s p ∧ Logos.Agency.Means s q ∧ Logos.Alternatives.Incompatible p q\n",
    "\n",
    "theorem incompatible_self_negation (p : Prop) : Logos.Alternatives.Incompatible p (¬ p) := by\n",
    "  intro ⟨hp, hnp⟩\n",
    "  exact hnp hp\n",
    "\n",
    "axiom AxActPolarity : ∀ (s : Logos.Agency.Subject) (p : Prop),\n",
    "  Logos.Agency.Act s p → Logos.Agency.Means s (¬ p)\n",
    "end Choice\n",
    "\n",
    "namespace Person\n",
    "def Person (s : Logos.Agency.Subject) : Prop :=\n",
    "  ∃ (p q : Prop), Logos.Choice.Chooses s p q\n",
    "end Person\n",
    "\n",
    "namespace Entity\n",
    "inductive Entity : Type\n",
    "  | ofGround : Entity\n",
    "  | ofSubject : Logos.Agency.Subject → Entity\n",
    "end Entity\n",
    "\n",
    "namespace FoundationalUnicity\n",
    "theorem ofGround_ne_ofSubject (s : Logos.Agency.Subject) :\n",
    "    Logos.Entity.Entity.ofSubject s ≠ Logos.Entity.Entity.ofGround := by\n",
    "  intro h\n",
    "  nomatch h\n",
    "\n",
    "def UniversalModalGround (g : Logos.Entity.Entity) : Prop :=\n",
    "  g = Logos.Entity.Entity.ofGround\n",
    "\n",
    "theorem exactly_one_universal_modal_ground (_hNoTotal : ∀ s : Logos.Agency.Subject, ∃ p : Prop, ¬ Logos.Agency.Means s p) :\n",
    "    ∃ g : Logos.Entity.Entity, UniversalModalGround g ∧ (∀ g' : Logos.Entity.Entity, UniversalModalGround g' → g' = g) := by\n",
    "  exact ⟨Logos.Entity.Entity.ofGround, rfl, fun g' hg' => hg'⟩\n",
    "end FoundationalUnicity\n",
    "\n",
    "namespace FoundationalOmnipresence\n",
    "def UniversalModalGround := Logos.FoundationalUnicity.UniversalModalGround\n",
    "end FoundationalOmnipresence\n",
    "\n",
    "namespace TrinitarianSubjectBridge\n",
    "inductive DivineRole : Type\n",
    "  | source : DivineRole\n",
    "  | word : DivineRole\n",
    "  | spirit : DivineRole\n",
    "deriving DecidableEq\n",
    "\n",
    "axiom DivineSubjectRole : Logos.Agency.Subject → DivineRole\n",
    "\n",
    "axiom three_divine_persons_exist_with_roles :\n",
    "  ∃ a b c : Logos.Agency.Subject,\n",
    "    DivineSubjectRole a = DivineRole.source ∧\n",
    "    DivineSubjectRole b = DivineRole.word ∧\n",
    "    DivineSubjectRole c = DivineRole.spirit ∧\n",
    "    Logos.Person.Person a ∧ Logos.Person.Person b ∧ Logos.Person.Person c\n",
    "end TrinitarianSubjectBridge\n",
    "\n",
    "end Logos\n",
    "\n"
]

cut1_idx = 1038
cut2_idx = 2147
cut3_idx = 4256

# 1. System.lean: preamble + rest_lines[71 to cut1_idx]
system_body = "".join(rest_lines[71:cut1_idx]).replace("private theorem emptyUnitWf", "theorem emptyUnitWf")
system_code = "".join(preamble_lines) + """namespace Logos
namespace OntologicalIncompleteness
""" + system_body + """
end OntologicalIncompleteness
end Logos
"""
with open(logos_dir / "System.lean", "w", encoding="utf-8") as f:
    f.write(system_code)
print("Wrote System.lean")

# 2. Elimination.lean: rest_lines[cut1_idx to cut2_idx]
elim_code = """import Lean
import Logos.System

open Classical

namespace Logos
namespace OntologicalIncompleteness

""" + "".join(rest_lines[cut1_idx:cut2_idx]) + """
end OntologicalIncompleteness
end Logos
"""
with open(logos_dir / "Elimination.lean", "w", encoding="utf-8") as f:
    f.write(elim_code)
print("Wrote Elimination.lean")

# 3. Agency.lean: rest_lines[cut2_idx to cut3_idx]
agency_code = """import Lean
import Logos.System
import Logos.Elimination

open Classical

namespace Logos
namespace OntologicalIncompleteness

""" + "".join(rest_lines[cut2_idx:cut3_idx]) + """
end OntologicalIncompleteness
end Logos
"""
with open(logos_dir / "Agency.lean", "w", encoding="utf-8") as f:
    f.write(agency_code)
print("Wrote Agency.lean")

# 4. Source.lean: rest_lines[cut3_idx to end]
source_code = """import Lean
import Logos.System
import Logos.Elimination
import Logos.Agency

open Classical

namespace Logos
namespace OntologicalIncompleteness

""" + "".join(rest_lines[cut3_idx:])
with open(logos_dir / "Source.lean", "w", encoding="utf-8") as f:
    f.write(source_code)
print("Wrote Source.lean")

# 5. Logos.lean
root_code = """import Logos.System
import Logos.Elimination
import Logos.Agency
import Logos.Source
"""
with open(formal_dir / "Logos.lean", "w", encoding="utf-8") as f:
    f.write(root_code)
print("Wrote Logos.lean")
