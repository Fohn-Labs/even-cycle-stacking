import CycleStack.GoodRoot
import CycleStack.SmallAntipode
import CycleStack.EvenEnding
import CycleStack.OddEnding

namespace CycleStack

open TreeStack

/-- Every target-mass configuration on an even cycle has a legal sequence
ending with all remaining pebbles at one vertex. -/
theorem even_cycle_stackable {n : ℕ} (hn : 2 ≤ n)
    (C : Configuration (Fin (2 * n)))
    (hmass : mass C = 2 ^ (n + 1) - 1) :
    Stackable (evenCycle n) C := by
  let : NeZero (2 * n) := ⟨by omega⟩
  obtain ⟨r, hbal, hgood⟩ := exists_good_root hn C hmass
  by_cases hsmall : cycleAt C (r + n) ≤ 2
  · exact stackable_of_small_antipode hn C r hmass hbal hsmall
  have hb : 3 ≤ cycleAt C (r + n) := by omega
  by_cases heven : cycleAt C (r + (n - 1)) % 2 = 0 ∨
      cycleAt C (r + n + 1) % 2 = 0
  · exact stackable_of_even_ending hn C r hmass hbal hb heven
  have hx : cycleAt C (r + (n - 1)) % 2 = 1 := by omega
  have hy : cycleAt C (r + n + 1) % 2 = 1 := by omega
  apply stackable_of_odd_ending hn C r hmass hbal hb hx hy
  rcases hgood with hs | hx0 | hy0 | hCW | hCCW | hK
  · exact (hsmall hs).elim
  · exact (heven (Or.inl hx0)).elim
  · exact (heven (Or.inr hy0)).elim
  · exact Or.inl hCW
  · exact Or.inr (Or.inl hCCW)
  · exact Or.inr (Or.inr hK)

/-- The universal upper bound requested in fohn task #2, for every n>=2.
There is no bounded-order or almost-stacked hypothesis. -/
theorem even_cycle_upper {n : ℕ} (hn : 2 ≤ n) : EvenCycleUpper n := by
  intro C hmass
  exact even_cycle_stackable hn C hmass

theorem C4_universal : EvenCycleUpper 2 := even_cycle_upper (by decide)
theorem C6_universal : EvenCycleUpper 3 := even_cycle_upper (by decide)
theorem C8_universal : EvenCycleUpper 4 := even_cycle_upper (by decide)

#check @even_cycle_stackable
#check @even_cycle_upper
#print axioms even_cycle_stackable
#print axioms even_cycle_upper
#print axioms C6_universal
#print axioms C8_universal

end CycleStack
