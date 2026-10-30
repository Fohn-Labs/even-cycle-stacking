import CycleStack.CycleFold

namespace CycleStack

open TreeStack

/-- The classical antipodal lower witness cannot stack: any legal cycle
stack would push forward to the impossible endpoint stack on the path. -/
theorem not_stackable_cycleLower {n : ℕ} (hn : 2 ≤ n) :
    ¬ Stackable (evenCycle n) (cycleLowerConfig n) := by
  exact not_stackable_cycleLower_of_path hn
    (not_stackable_pathLower (by omega))

/-- A fully formal lower obstruction of mass one below the upper threshold. -/
theorem even_cycle_lower {n : ℕ} (hn : 2 ≤ n) :
    EvenCycleLowerObstruction n := by
  exact ⟨cycleLowerConfig n, mass_cycleLowerConfig_add_one hn,
    not_stackable_cycleLower hn⟩

#print axioms not_stackable_cycleLower
#print axioms even_cycle_lower

end CycleStack
