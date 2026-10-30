import CycleStack.CyclePaths

namespace CycleStack

open TreeStack

/-- A balanced root to which one of the direct clearing cases applies.
The short prefixes exclude the root and the vertex next to its antipode. -/
def NonPivotRoot {n : ℕ} [NeZero (2 * n)]
    (C : Configuration (Fin (2 * n))) (r : ℕ) : Prop :=
  cycleAt C (r + n) ≤ 2 ∨
    cycleAt C (r + (n - 1)) % 2 = 0 ∨
    cycleAt C (r + n + 1) % 2 = 0 ∨
    2 ^ (n - 1) - 2 ≤ ((clockwiseArm r (n - 2)).map C).sum ∨
    2 ^ (n - 1) - 2 ≤ ((counterclockwiseArm r (n - 2)).map C).sum ∨
    cycleAt C (r + n) + cycleAt C (r + (n - 1)) + cycleAt C (r + n + 1) ≤ 2 ^ n - 1

/-- Root selection for the cycle upper bound. A balanced root either is a
direct case already, or one pivot makes the antipode small (n=3) or the
opposite triple small (n>=4). No stackability theorem is assumed. -/
theorem exists_good_root {n : ℕ} [NeZero (2 * n)] (hn : 2 ≤ n)
    (C : Configuration (Fin (2 * n)))
    (hmass : mass C = 2 ^ (n + 1) - 1) :
    ∃ r : ℕ, Balanced C (2 ^ n) r ∧ NonPivotRoot C r := by
  have hA : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
  have hm : (∑ v, C v) = 2 * 2 ^ n - 1 := by
    change mass C = 2 * 2 ^ n - 1
    rw [pow_succ] at hmass
    omega
  obtain ⟨rFin, hbal, _, _, _⟩ := exists_balanced_root hn hA C hm
  let r : ℕ := rFin.val
  change Balanced C (2 ^ n) r at hbal
  by_cases hn2 : n = 2
  · have hzero : 2 ^ (n - 1) - 2 = 0 := by rw [hn2]; decide
    refine ⟨r, hbal, Or.inr (Or.inr (Or.inr (Or.inl ?_)))⟩
    rw [hzero]
    exact Nat.zero_le _
  have hn3 : 3 ≤ n := by omega
  by_cases hgood : NonPivotRoot C r
  · exact ⟨r, hbal, hgood⟩
  have hbad := hgood
  simp only [NonPivotRoot, not_or] at hbad
  have hR := hbad.2.2.2.2.1
  have hK := hbad.2.2.2.2.2
  have htriple : 2 ^ n ≤ window (cycleAt C) (r + (n - 1)) 3 := by
    rw [opposite_triple_eq (cycleAt C) r n (by omega)]
    omega
  have hpivot : Balanced C (2 ^ n) (r + (n - 1)) :=
    (balanced_endings hn3 C hm hbal htriple).1
  by_cases hnEq3 : n = 3
  · have htwo : 2 ^ (n - 1) - 2 = 2 := by rw [hnEq3]; decide
    have hsmallR : ((counterclockwiseArm r (n - 2)).map C).sum < 2 := by
      rw [htwo] at hR
      omega
    rw [counterclockwiseArm_mass C r (by omega)] at hsmallR
    have he : r + 2 * n - (n - 2) = r + (n + 2) := by omega
    rw [he] at hsmallR
    have hanti := pivot_antipode_le_one (f := cycleAt C) (r := r) hn3 hsmallR
    refine ⟨r + (n - 1), hpivot, Or.inl ?_⟩
    have heAnti : r + (n - 1) + n = r + (2 * n - 1) := by omega
    rw [heAnti]
    omega
  · have hn4 : 4 ≤ n := by omega
    have hnew := pivot_triple_bound hn4 C hm htriple
    have he : (r + (n - 1)) + (n - 1) = r + (2 * n - 2) := by omega
    have hnewWindow : window (cycleAt C) ((r + (n - 1)) + (n - 1)) 3 ≤ 2 ^ n - 1 := by
      rw [he]
      exact hnew
    rw [opposite_triple_eq (cycleAt C) (r + (n - 1)) n (by omega)] at hnewWindow
    refine ⟨r + (n - 1), hpivot,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))⟩
    omega

end CycleStack
