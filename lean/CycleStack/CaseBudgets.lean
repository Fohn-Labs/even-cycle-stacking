import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace CycleStack

/-- A uniform upper bound on the local cost of clearing a pile at least three.
For an even pile the actual cost can be one smaller. -/
def localClearBound (b : ℕ) : ℕ := (b + 3) / 2

theorem localClearBound_le {b : ℕ} (hb : 3 ≤ b) :
    localClearBound b ≤ b := by
  unfold localClearBound
  omega

theorem even_ending_half_bound {B b q k : ℕ}
    (hB : 2 ≤ B) (hb : 3 ≤ b) (hq : q + b + 1 ≤ 2 * B)
    (hk : 2 * k ≤ q) : k ≤ B - 2 := by
  omega

theorem even_ending_negative_budget {B b k : ℕ}
    (hB : 2 ≤ B) (hb : 3 ≤ b) (hk : 2 * k + b + 1 ≤ 2 * B) :
    B + k - 2 + localClearBound b ≤ 2 * B := by
  unfold localClearBound
  omega

theorem even_ending_nonnegative_budget {A b q : ℕ}
    (hb : 3 ≤ b) (hq : q + b + 1 ≤ A) :
    q + 1 + localClearBound b ≤ A := by
  unfold localClearBound
  omega

theorem odd_ending_large_prefix_budget {A b q s t : ℕ}
    (hb : 3 ≤ b) (ht : 1 ≤ t) (htq : t ≤ q)
    (hs : s ≤ 2) (hq : q + b + 1 ≤ A) :
    s + q - t + localClearBound (b + t) ≤ A := by
  unfold localClearBound
  omega

theorem odd_ending_small_prefix_budget {B b t : ℕ}
    (hB : 2 ≤ B) (hb : 3 ≤ b) (ht : 1 ≤ t)
    (htriple : b + 4 * t ≤ 2 * B + 1) :
    B + t - 1 + localClearBound (b + t) ≤ 2 * B := by
  unfold localClearBound
  omega

theorem odd_ending_small_ending_bound {B b t u : ℕ}
    (hB : 2 ≤ B) (hb : 3 ≤ b) (ht : 1 ≤ t) (htu : t ≤ u)
    (htriple : b + (2 * t - 1) + (2 * u - 1) + 1 ≤ 2 * B) :
    2 * t - 1 ≤ B - 2 := by
  omega

theorem odd_ending_small_source_funding {A B a M t s : ℕ}
    (hAB : A = 2 * B) (hB : 2 ≤ B) (ht : 1 ≤ t)
    (hending : 2 * t - 1 ≤ B - 2)
    (hroot : A ≤ a + M + (2 * t - 1))
    (hs : s ≤ B - M) : s ≤ a := by
  omega

theorem full_pull_source_funding {A a q p : ℕ}
    (hroot : A ≤ a + q) (hq : q ≤ A - 1)
    (hA : 1 ≤ A) (hp : p ≤ A - 1 - q) : p + 1 ≤ a := by
  omega

theorem C4_hard_pivot_case_impossible {a b x y : ℕ}
    (hb : 3 ≤ b) (hab : b < a) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hmass : a + b + x + y ≤ 7) : False := by
  omega

#print axioms even_ending_negative_budget
#print axioms odd_ending_large_prefix_budget
#print axioms odd_ending_small_prefix_budget
#print axioms odd_ending_small_source_funding

end CycleStack
