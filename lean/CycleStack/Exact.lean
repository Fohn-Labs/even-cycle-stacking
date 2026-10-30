import CycleStack.Lower
import CycleStack.StackingNumber

namespace CycleStack

open TreeStack

/-- The exact least universal threshold for every ordinary even cycle. -/
theorem even_cycle_isStackingNumber {n : ℕ} (hn : 2 ≤ n) :
    IsStackingNumber (evenCycle n) (cycleThreshold n) :=
  even_cycle_isStackingNumber_of_obstruction hn (even_cycle_lower hn)

/-- The even-cycle stacking-number equality, without ASH or any other
mathematical premise beyond n >= 2. Both bounds are formalized. -/
theorem even_cycle_stackingNumber {n : ℕ} (hn : 2 ≤ n) :
    stackingNumber (evenCycle n) = 2 ^ (n + 1) - 1 :=
  (even_cycle_isStackingNumber hn).stackingNumber_eq

theorem even_cycle_universal_iff {n t : ℕ} (hn : 2 ≤ n) (ht : 2 ≤ t) :
    UniversalStackable (evenCycle n) t ↔ 2 ^ (n + 1) - 1 ≤ t := by
  have hExact := even_cycle_isStackingNumber hn
  constructor
  · intro hU
    exact hExact.2.2 t ht hU
  · intro hmass
    exact hExact.universal_ge (evenCycle_no_isolated (by omega)) hmass

theorem C4_exact : stackingNumber (evenCycle 2) = 7 :=
  even_cycle_stackingNumber (by decide)

theorem C6_exact : stackingNumber (evenCycle 3) = 15 :=
  even_cycle_stackingNumber (by decide)

theorem C8_exact : stackingNumber (evenCycle 4) = 31 :=
  even_cycle_stackingNumber (by decide)

#check @even_cycle_stackingNumber
#print axioms even_cycle_stackingNumber
#print axioms even_cycle_universal_iff
#print axioms C8_exact

end CycleStack
