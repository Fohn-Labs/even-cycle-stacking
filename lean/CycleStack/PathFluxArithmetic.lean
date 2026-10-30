import TreeStack.Transfer

namespace CycleStack

private theorem endpoint_power_ge_four {n : ℕ} (hn : 1 ≤ n) :
    4 ≤ (2 : ℕ) ^ (n + 1) := by
  have hpos : 0 < (2 : ℕ) ^ (n - 1) := pow_pos (by omega) _
  have hpow := pow_succ (2 : ℕ) (n - 1)
  have he : n - 1 + 1 = n := by omega
  rw [he] at hpow
  have hnext := pow_succ (2 : ℕ) n
  omega

/-- Exact transfer along the positive phase of the endpoint obstruction. -/
theorem F_pow_sub_three {k : ℕ} (hk : 1 ≤ k) :
    TreeStack.F ((2 : ℤ) ^ (k + 1) - 3) = (2 : ℤ) ^ k - 3 := by
  have hpos : (0 : ℤ) < 2 ^ (k - 1) := pow_pos (by omega) _
  have hpow := pow_succ (2 : ℤ) (k - 1)
  have he : k - 1 + 1 = k := by omega
  rw [he] at hpow
  have htwo : (2 : ℤ) ≤ 2 ^ k := by omega
  rw [pow_succ]
  unfold TreeStack.F
  split_ifs <;> omega

/-- F is monotone within a residue class modulo three. This does not assert
coordinatewise monotonicity of F on all integers. -/
private theorem F_le_same_residue {y z : ℤ} (hle : y ≤ z) (hmod : y % 3 = z % 3) :
    TreeStack.F y ≤ TreeStack.F z := by
  unfold TreeStack.F
  split_ifs <;> omega

private theorem F_same_residue {y z : ℤ} (hmod : y % 3 = z % 3) :
    TreeStack.F y % 3 = TreeStack.F z % 3 := by
  unfold TreeStack.F
  split_ifs <;> omega

/-- Positive outward flow from an occupied branch and nonnegative inward
flow satisfy the exact maximizing-transfer bound and its residue condition. -/
theorem transfer_flux_bound {y z O I : ℤ}
    (hO : 1 ≤ O) (hI : 0 ≤ I) (hbal : y + I - 2 * O = 0)
    (hle : y ≤ z) (hmod : y % 3 = z % 3) :
    O - 2 * I ≤ TreeStack.F z ∧ (O - 2 * I) % 3 = TreeStack.F z % 3 := by
  constructor
  · exact (TreeStack.one_vertex_flux_le hO hI hbal).trans (F_le_same_residue hle hmod)
  · exact (TreeStack.one_vertex_flux_mod_three hO hI hbal).trans (F_same_residue hmod)

theorem lower_endpoint_mass_cast {n : ℕ} (hn : 1 ≤ n) :
    (((2 ^ (n + 1) - 3) : ℕ) : ℤ) = (2 : ℤ) ^ (n + 1) - 3 := by
  have hge : 3 ≤ (2 : ℕ) ^ (n + 1) := (by omega : 3 ≤ 4).trans (endpoint_power_ge_four hn)
  rw [Nat.cast_sub hge]
  simp

theorem lower_endpoint_mass_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < (2 : ℕ) ^ (n + 1) - 3 := by
  have hge := endpoint_power_ge_four hn
  omega

end CycleStack

#print axioms CycleStack.F_pow_sub_three
#print axioms CycleStack.transfer_flux_bound
#print axioms CycleStack.lower_endpoint_mass_cast
#print axioms CycleStack.lower_endpoint_mass_pos
