import CycleStack.Cycle

namespace CycleStack

open TreeStack

/-- The known lower-bound witness: a large pile at zero and a singleton
at its antipode. Its mass is one below the proposed universal threshold. -/
def cycleLowerConfig (n : ℕ) : Configuration (Fin (2 * n)) :=
  fun v => if v.val = 0 then 2 ^ (n + 1) - 3 else if v.val = n then 1 else 0

theorem cycleLowerConfig_eq {n : ℕ} (hn : 2 ≤ n) :
    cycleLowerConfig n = fun v =>
      (if v = (⟨0, by omega⟩ : Fin (2 * n)) then 2 ^ (n + 1) - 3 else 0) +
      (if v = (⟨n, by omega⟩ : Fin (2 * n)) then 1 else 0) := by
  funext v
  have hz : v = (⟨0, by omega⟩ : Fin (2 * n)) ↔ v.val = 0 := by
    exact Fin.ext_iff
  have ha : v = (⟨n, by omega⟩ : Fin (2 * n)) ↔ v.val = n := by
    exact Fin.ext_iff
  simp only [cycleLowerConfig, hz, ha]
  by_cases h0 : v.val = 0
  · have hn0 : (0 : ℕ) ≠ n := by omega
    simp [h0, hn0]
  · simp [h0]

theorem mass_cycleLowerConfig {n : ℕ} (hn : 2 ≤ n) :
    mass (cycleLowerConfig n) = 2 ^ (n + 1) - 2 := by
  rw [cycleLowerConfig_eq hn, mass, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hp := two_mul_add_two_le_power n
  omega

theorem mass_cycleLowerConfig_add_one {n : ℕ} (hn : 2 ≤ n) :
    mass (cycleLowerConfig n) + 1 = cycleThreshold n := by
  rw [mass_cycleLowerConfig hn]
  have hp := two_mul_add_two_le_power n
  unfold cycleThreshold
  omega

#print axioms mass_cycleLowerConfig

end CycleStack
