import CycleStack.GraphPushforward
import CycleStack.PathLower
import CycleStack.LowerConfig

namespace CycleStack

open TreeStack

/-- Distance from zero around an even cycle, viewed as a path vertex. -/
def cycleFold (n : ℕ) (v : Fin (2 * n)) : Fin (n + 1) :=
  ⟨min v.val (2 * n - v.val), by have hv := v.isLt; omega⟩

@[simp] theorem cycleFold_val {n : ℕ} (v : Fin (2 * n)) :
    (cycleFold n v).val = min v.val (2 * n - v.val) := rfl

theorem cycleFold_eq_zero_iff {n : ℕ} (v : Fin (2 * n)) :
    cycleFold n v = 0 ↔ v.val = 0 := by
  rw [Fin.ext_iff]
  simp only [cycleFold_val, Fin.val_zero]
  have hv := v.isLt
  omega

theorem cycleFold_eq_last_iff {n : ℕ} (v : Fin (2 * n)) :
    cycleFold n v = Fin.last n ↔ v.val = n := by
  rw [Fin.ext_iff]
  simp only [cycleFold_val, Fin.val_last]
  have hv := v.isLt
  omega

@[simp] theorem cycleFold_zero {n : ℕ} (hzero : 0 < 2 * n) :
    cycleFold n ⟨0, hzero⟩ = 0 := by
  apply Fin.ext
  simp [cycleFold]

@[simp] theorem cycleFold_antipode {n : ℕ} (hanti : n < 2 * n) :
    cycleFold n ⟨n, hanti⟩ = Fin.last n := by
  apply Fin.ext
  change min n (2 * n - n) = n
  omega

private theorem fold_adj_of_step {n i j : ℕ} (_hn : 1 ≤ n)
    (hi : i < 2 * n) (hj : j < 2 * n) (hstep : (i + 1) % (2 * n) = j) :
    min i (2 * n - i) + 1 = min j (2 * n - j) ∨
      min j (2 * n - j) + 1 = min i (2 * n - i) := by
  by_cases hlt : i + 1 < 2 * n
  · rw [Nat.mod_eq_of_lt hlt] at hstep
    omega
  · have he : i + 1 = 2 * n := by omega
    rw [he, Nat.mod_self] at hstep
    omega

/-- Folding is a genuine graph homomorphism: no cycle edge collapses. -/
def cycleFoldHom {n : ℕ} (hn : 2 ≤ n) : evenCycle n →g pathGraph n where
  toFun := cycleFold n
  map_rel' := by
    intro u v h
    rcases h with ⟨_, hstep | hstep⟩
    · exact fold_adj_of_step (by omega) u.isLt v.isLt hstep
    · exact (fold_adj_of_step (by omega) v.isLt u.isLt hstep).symm

@[simp] theorem cycleFoldHom_apply {n : ℕ} (hn : 2 ≤ n) (v : Fin (2 * n)) :
    cycleFoldHom hn v = cycleFold n v := rfl

theorem cycleFold_ne_of_adj {n : ℕ} (hn : 2 ≤ n) {u v : Fin (2 * n)}
    (h : (evenCycle n).Adj u v) : cycleFold n u ≠ cycleFold n v :=
  ((cycleFoldHom hn).map_adj h).ne

theorem mass_cycleFold_pushforward {n : ℕ} (C : Configuration (Fin (2 * n))) :
    mass (pushforward (cycleFold n) C) = mass C := mass_pushforward _ _

theorem reach_cycleFold {n : ℕ} (hn : 2 ≤ n) {C D : Configuration (Fin (2 * n))}
    (h : Reach (evenCycle n) C D) :
    Reach (pathGraph n) (pushforward (cycleFold n) C) (pushforward (cycleFold n) D) :=
  reach_pushforward (cycleFoldHom hn) h

theorem stackable_cycleFold {n : ℕ} (hn : 2 ≤ n) {C : Configuration (Fin (2 * n))}
    (h : Stackable (evenCycle n) C) :
    Stackable (pathGraph n) (pushforward (cycleFold n) C) :=
  stackable_pushforward (cycleFoldHom hn) h

/-- The explicit cycle witness folds exactly to the endpoint path witness. -/
theorem pushforward_cycleLowerConfig {n : ℕ} (hn : 2 ≤ n) :
    pushforward (cycleFold n) (cycleLowerConfig n) = pathLowerConfig n := by
  rw [cycleLowerConfig_eq hn]
  change pushforward (cycleFold n)
      (vertexPile (⟨0, by omega⟩ : Fin (2 * n)) (2 ^ (n + 1) - 3) +
        vertexPile (⟨n, by omega⟩ : Fin (2 * n)) 1) = pathLowerConfig n
  rw [pushforward_add, pushforward_vertexPile, pushforward_vertexPile,
    cycleFold_zero, cycleFold_antipode]
  funext w
  have hz : w = (0 : Fin (n + 1)) ↔ w.val = 0 := Fin.ext_iff
  have ha : w = Fin.last n ↔ w.val = n := Fin.ext_iff
  simp only [vertexPile, Pi.add_apply, pathLowerConfig, endpointConfig, hz, ha]
  by_cases hzero : w.val = 0
  · have hnzero : (0 : ℕ) ≠ n := by omega
    simp [hzero, hnzero]
  · simp [hzero]

/-- The sole remaining lower-bound input is nonstackability of the endpoint
configuration on the path; no preservation principle is assumed here. -/
theorem not_stackable_cycleLower_of_path {n : ℕ} (hn : 2 ≤ n)
    (hpath : ¬ Stackable (pathGraph n) (pathLowerConfig n)) :
    ¬ Stackable (evenCycle n) (cycleLowerConfig n) := by
  intro hcycle
  have h := stackable_cycleFold hn hcycle
  rw [pushforward_cycleLowerConfig hn] at h
  exact hpath h

end CycleStack

#print axioms CycleStack.cycleFoldHom
#print axioms CycleStack.reach_cycleFold
#print axioms CycleStack.stackable_cycleFold
#print axioms CycleStack.pushforward_cycleLowerConfig
#print axioms CycleStack.not_stackable_cycleLower_of_path
