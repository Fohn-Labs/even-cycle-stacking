import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Periodic
import Lean.Elab.Tactic.Omega

namespace CycleStack

/-- A finite window of a natural-number sequence. -/
def window (f : ℕ → ℕ) (r k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, f (r + i)

@[simp] theorem window_zero (f : ℕ → ℕ) (r : ℕ) : window f r 0 = 0 := by
  simp [window]

@[simp] theorem window_one (f : ℕ → ℕ) (r : ℕ) : window f r 1 = f r := by
  simp [window]

theorem window_succ (f : ℕ → ℕ) (r k : ℕ) :
    window f r (k + 1) = window f r k + f (r + k) := by
  simp [window, Finset.sum_range_succ]

theorem window_two (f : ℕ → ℕ) (r : ℕ) :
    window f r 2 = f r + f (r + 1) := by
  rw [show 2 = 1 + 1 from rfl, window_succ, window_one]

theorem window_three (f : ℕ → ℕ) (r : ℕ) :
    window f r 3 = f r + f (r + 1) + f (r + 2) := by
  rw [show 3 = 2 + 1 from rfl, window_succ, window_two]

/-- Sliding a window exchanges its two endpoint values. -/
theorem window_shift (f : ℕ → ℕ) (r k : ℕ) :
    window f (r + 1) k + f r = window f r k + f (r + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [window_succ, window_succ]
    have hi : r + 1 + k = r + (k + 1) := by omega
    rw [hi]
    omega

theorem window_head (f : ℕ → ℕ) (r k : ℕ) :
    window f r (k + 1) = f r + window f (r + 1) k := by
  have hs := window_shift f r k
  have he := window_succ f r k
  omega

theorem window_add (f : ℕ → ℕ) (r k l : ℕ) :
    window f r (k + l) = window f r k + window f (r + k) l := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Nat.add_succ, window_succ, ih, window_succ]
    simp [Nat.add_assoc]

theorem window_mono (f : ℕ → ℕ) (r : ℕ) {k l : ℕ} (hkl : k ≤ l) :
    window f r k ≤ window f r l := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hkl
  rw [hd, window_add]
  omega

theorem window_term_le (f : ℕ → ℕ) (r : ℕ) {i k : ℕ} (hi : i < k) :
    f (r + i) ≤ window f r k := by
  have hm := window_mono f r (show i + 1 ≤ k by omega)
  have hs := window_succ f r i
  omega

/-- A subinterval of a window has no greater mass. -/
theorem window_subinterval_le (f : ℕ → ℕ) (r i k l : ℕ) (h : i + k ≤ l) :
    window f (r + i) k ≤ window f r l := by
  have hm := window_mono f r h
  have hs := window_add f r i k
  omega

theorem window_period_start {f : ℕ → ℕ} {N : ℕ}
    (hp : Function.Periodic f N) (r k : ℕ) :
    window f (r + N) k = window f r k := by
  unfold window
  apply Finset.sum_congr rfl
  intro i hi
  have he : r + N + i = (r + i) + N := by omega
  change f (r + N + i) = f (r + i)
  rw [he, hp]

/-- Every full-period window has the same total. -/
theorem window_cycle_mass {f : ℕ → ℕ} {N : ℕ}
    (hp : Function.Periodic f N) (r : ℕ) :
    window f r N = window f 0 N := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have hs := window_shift f r N
    rw [hp r] at hs
    omega

/-- Complementary half-windows partition a whole even cycle. -/
theorem half_complement {f : ℕ → ℕ} {n : ℕ}
    (hp : Function.Periodic f (2 * n)) (r : ℕ) :
    window f r n + window f (r + n) n = window f 0 (2 * n) := by
  calc
    window f r n + window f (r + n) n = window f r (n + n) :=
      (window_add f r n n).symm
    _ = window f r (2 * n) := by congr 1; omega
    _ = window f 0 (2 * n) := window_cycle_mass hp r

/-- The two half-windows excluding a root and including its antipode are low. -/
def WindowBalanced (f : ℕ → ℕ) (n A r : ℕ) : Prop :=
  window f (r + 1) n ≤ A - 1 ∧ window f (r + n) n ≤ A - 1

theorem balanced_of_high_low {f : ℕ → ℕ} {n A r : ℕ}
    (hp : Function.Periodic f (2 * n))
    (hmass : window f 0 (2 * n) = 2 * A - 1)
    (hhigh : A ≤ window f r n) (hlow : window f (r + 1) n ≤ A - 1) :
    WindowBalanced f n A r := by
  have hc := half_complement hp r
  rw [hmass] at hc
  exact ⟨hlow, by omega⟩

/-- Low half-windows imply high complements and strict root-antipode comparison. -/
theorem balanced_properties {f : ℕ → ℕ} {n A r : ℕ}
    (hA : 0 < A) (hp : Function.Periodic f (2 * n))
    (hmass : window f 0 (2 * n) = 2 * A - 1)
    (hb : WindowBalanced f n A r) :
    A ≤ window f r n ∧ A ≤ window f (r + n + 1) n ∧ f (r + n) < f r := by
  rcases hb with ⟨hb₁, hb₂⟩
  have hc := half_complement hp r
  have hc' := half_complement hp (r + 1)
  have he : r + 1 + n = r + n + 1 := by omega
  rw [he, hmass] at hc'
  rw [hmass] at hc
  have hs := window_shift f r n
  exact ⟨by omega, by omega, by omega⟩

private theorem high_low_between (H : ℕ → ℕ) (A start : ℕ) :
    ∀ L : ℕ, A ≤ H start → H (start + L) < A →
      ∃ k : ℕ, k < L ∧ A ≤ H (start + k) ∧ H (start + k + 1) < A := by
  intro L
  induction L with
  | zero =>
    intro hh hl
    simp only [Nat.add_zero] at hl
    omega
  | succ L ih =>
    intro hh hl
    by_cases hm : A ≤ H (start + L)
    · exact ⟨L, by omega, hm, by simpa [Nat.add_assoc] using hl⟩
    · obtain ⟨k, hk, hkh, hkl⟩ := ih hh (by omega)
      exact ⟨k, by omega, hkh, hkl⟩

/-- An odd-total periodic sequence has a high-to-low half-window transition. -/
theorem exists_window_balanced {f : ℕ → ℕ} {n A : ℕ}
    (_hn : 0 < n) (hA : 0 < A) (hp : Function.Periodic f (2 * n))
    (hmass : window f 0 (2 * n) = 2 * A - 1) :
    ∃ r : ℕ, r < 2 * n ∧ WindowBalanced f n A r := by
  have hc := half_complement hp 0
  simp only [Nat.zero_add] at hc
  rw [hmass] at hc
  by_cases hh : A ≤ window f 0 n
  · have hl : window f (0 + n) n < A := by
      simpa using (show window f n n < A by omega)
    obtain ⟨k, hk, hkh, hkl⟩ :=
      high_low_between (fun r => window f r n) A 0 n hh hl
    simp only [Nat.zero_add] at hkh hkl
    refine ⟨k, by omega, balanced_of_high_low hp hmass hkh ?_⟩
    omega
  · have hh' : A ≤ window f n n := by omega
    have hperiod : window f (n + n) n = window f 0 n := by
      simpa [two_mul] using window_period_start hp 0 n
    have hl : window f (n + n) n < A := by omega
    obtain ⟨k, hk, hkh, hkl⟩ :=
      high_low_between (fun r => window f r n) A n n hh' hl
    refine ⟨n + k, by omega, balanced_of_high_low hp hmass hkh ?_⟩
    omega

/-- Partition into the root-side prefix, the opposite triple, and the far prefix. -/
theorem triple_partition (f : ℕ → ℕ) (r n : ℕ) (hn : 2 ≤ n) :
    window f r (2 * n) = window f r (n - 1) +
      window f (r + (n - 1)) 3 + window f (r + (n + 2)) (n - 2) := by
  calc
    window f r (2 * n) = window f r ((n - 1) + (3 + (n - 2))) := by
      congr 1; omega
    _ = window f r (n - 1) + window f (r + (n - 1)) (3 + (n - 2)) :=
      window_add f r (n - 1) (3 + (n - 2))
    _ = window f r (n - 1) + window f (r + (n - 1)) 3 +
        window f (r + (n + 2)) (n - 2) := by
      rw [window_add]
      have he : r + (n - 1) + 3 = r + (n + 2) := by omega
      rw [he]
      omega

theorem opposite_triple_eq (f : ℕ → ℕ) (r n : ℕ) (hn : 0 < n) :
    window f (r + (n - 1)) 3 =
      f (r + (n - 1)) + f (r + n) + f (r + n + 1) := by
  rw [window_three]
  have h₁ : r + (n - 1) + 1 = r + n := by omega
  have h₂ : r + (n - 1) + 2 = r + n + 1 := by omega
  rw [h₁, h₂]

/-- If the opposite triple is high, all mass outside it is low. -/
theorem outside_triple_le {f : ℕ → ℕ} {n A r : ℕ}
    (hn : 2 ≤ n) (hp : Function.Periodic f (2 * n))
    (hmass : window f 0 (2 * n) = 2 * A - 1)
    (htriple : A ≤ window f (r + (n - 1)) 3) :
    window f r (n - 1) + window f (r + (n + 2)) (n - 2) ≤ A - 1 := by
  have hf := window_cycle_mass hp r
  rw [hmass] at hf
  have ht := triple_partition f r n hn
  omega

/-- A high opposite triple makes both of its ending vertices balanced. -/
theorem ending_offsets_balanced {f : ℕ → ℕ} {n A r : ℕ}
    (hn : 3 ≤ n) (hp : Function.Periodic f (2 * n))
    (hmass : window f 0 (2 * n) = 2 * A - 1)
    (hb : WindowBalanced f n A r)
    (htriple : A ≤ window f (r + (n - 1)) 3) :
    WindowBalanced f n A (r + (n - 1)) ∧
      WindowBalanced f n A (r + (n + 1)) := by
  have hout := outside_triple_le (by omega : 2 ≤ n) hp hmass htriple
  have hpLast := window_term_le f (r + (n + 2))
    (show n - 3 < n - 2 by omega)
  have heLast : r + (n + 2) + (n - 3) = r + (2 * n - 1) := by omega
  rw [heLast] at hpLast
  have hpre := window_mono f r (show 2 ≤ n - 1 by omega)
  rcases hb with ⟨hb₁, hb₂⟩
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have he : r + (n - 1) + 1 = r + n := by omega
    simpa [he] using hb₂
  · have hw : window f (r + (n - 1) + n) n =
        f (r + (2 * n - 1)) + window f r (n - 1) := by
      calc
        window f (r + (n - 1) + n) n =
            window f (r + (2 * n - 1)) (1 + (n - 1)) := by
          congr 1 <;> omega
        _ = window f (r + (2 * n - 1)) 1 +
            window f (r + (2 * n - 1) + 1) (n - 1) :=
          window_add f (r + (2 * n - 1)) 1 (n - 1)
        _ = f (r + (2 * n - 1)) + window f r (n - 1) := by
          have he : r + (2 * n - 1) + 1 = r + 2 * n := by omega
          rw [window_one, he, window_period_start hp]
    rw [hw]
    omega
  · have hw : window f (r + (n + 1) + 1) n =
        window f (r + (n + 2)) (n - 2) + window f r 2 := by
      calc
        window f (r + (n + 1) + 1) n =
            window f (r + (n + 2)) ((n - 2) + 2) := by
          congr 1; omega
        _ = window f (r + (n + 2)) (n - 2) +
            window f (r + (n + 2) + (n - 2)) 2 :=
          window_add f (r + (n + 2)) (n - 2) 2
        _ = window f (r + (n + 2)) (n - 2) + window f r 2 := by
          have he : r + (n + 2) + (n - 2) = r + 2 * n := by omega
          rw [he, window_period_start hp]
    rw [hw]
    omega
  · have he : r + (n + 1) + n = (r + 1) + 2 * n := by omega
    rw [he, window_period_start hp]
    exact hb₁

/-- For n >= 4 the pivot's opposite triple lies outside the old opposite triple. -/
theorem pivot_triple_small {f : ℕ → ℕ} {n A r : ℕ}
    (hn : 4 ≤ n) (hp : Function.Periodic f (2 * n))
    (hmass : window f 0 (2 * n) = 2 * A - 1)
    (htriple : A ≤ window f (r + (n - 1)) 3) :
    window f (r + (2 * n - 2)) 3 ≤ A - 1 := by
  have hout := outside_triple_le (by omega : 2 ≤ n) hp hmass htriple
  have hlast := window_subinterval_le f (r + (n + 2)) (n - 4) 2 (n - 2)
    (by omega)
  have he : r + (n + 2) + (n - 4) = r + (2 * n - 2) := by omega
  rw [he] at hlast
  have hfirst := window_term_le f r (show 0 < n - 1 by omega)
  simp only [Nat.add_zero] at hfirst
  have hs := window_succ f (r + (2 * n - 2)) 2
  have he' : r + (2 * n - 2) + 2 = r + 2 * n := by omega
  rw [he', hp r] at hs
  change window f (r + (2 * n - 2)) 3 =
    window f (r + (2 * n - 2)) 2 + f r at hs
  omega

/-- The small-prefix boundary case needed when n=3. -/
theorem pivot_antipode_le_one {f : ℕ → ℕ} {n r : ℕ}
    (hn : 3 ≤ n) (hsmall : window f (r + (n + 2)) (n - 2) < 2) :
    f (r + (2 * n - 1)) ≤ 1 := by
  have hlast := window_term_le f (r + (n + 2))
    (show n - 3 < n - 2 by omega)
  have he : r + (n + 2) + (n - 3) = r + (2 * n - 1) := by omega
  rw [he] at hlast
  omega

/-- Cyclic indexing on the finite vertex type used by the cycle graph. -/
def cycleIndex {n : ℕ} [NeZero (2 * n)] (i : ℕ) : Fin (2 * n) :=
  ⟨i % (2 * n), Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne (2 * n)))⟩

def cycleAt {n : ℕ} [NeZero (2 * n)] (c : Fin (2 * n) → ℕ) (i : ℕ) : ℕ :=
  c (cycleIndex i)

def halfMass {n : ℕ} [NeZero (2 * n)] (c : Fin (2 * n) → ℕ) (r : ℕ) : ℕ :=
  window (cycleAt c) r n

def Balanced {n : ℕ} [NeZero (2 * n)] (c : Fin (2 * n) → ℕ) (A r : ℕ) : Prop :=
  WindowBalanced (cycleAt c) n A r

@[simp] theorem cycleIndex_fin {n : ℕ} [NeZero (2 * n)] (v : Fin (2 * n)) :
    cycleIndex v.val = v := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt v.isLt

@[simp] theorem cycleAt_fin {n : ℕ} [NeZero (2 * n)]
    (c : Fin (2 * n) → ℕ) (v : Fin (2 * n)) : cycleAt c v.val = c v := by
  simp [cycleAt, cycleIndex, Nat.mod_eq_of_lt v.isLt]

theorem cycleAt_period {n : ℕ} [NeZero (2 * n)] (c : Fin (2 * n) → ℕ) :
    Function.Periodic (cycleAt c) (2 * n) := by
  intro i
  simp [cycleAt, cycleIndex]

theorem cycleAt_add_mod {n : ℕ} [NeZero (2 * n)]
    (c : Fin (2 * n) → ℕ) (r i : ℕ) :
    cycleAt c (r % (2 * n) + i) = cycleAt c (r + i) := by
  simp [cycleAt, cycleIndex, Nat.add_mod]

theorem cycle_window_offset_mod {n : ℕ} [NeZero (2 * n)]
    (c : Fin (2 * n) → ℕ) (r i k : ℕ) :
    window (cycleAt c) (r % (2 * n) + i) k = window (cycleAt c) (r + i) k := by
  unfold window
  apply Finset.sum_congr rfl
  intro j hj
  simpa [Nat.add_assoc] using cycleAt_add_mod c r (i + j)

/-- A natural offset and its finite cyclic vertex describe the same balance. -/
theorem balanced_cycleIndex {n : ℕ} [NeZero (2 * n)]
    (c : Fin (2 * n) → ℕ) (A r : ℕ) :
    Balanced c A (cycleIndex (n := n) r).val ↔ Balanced c A r := by
  change (window (cycleAt c) (r % (2 * n) + 1) n ≤ A - 1 ∧
      window (cycleAt c) (r % (2 * n) + n) n ≤ A - 1) ↔
    (window (cycleAt c) (r + 1) n ≤ A - 1 ∧
      window (cycleAt c) (r + n) n ≤ A - 1)
  rw [cycle_window_offset_mod, cycle_window_offset_mod]

theorem cycle_mass {n : ℕ} [NeZero (2 * n)] (c : Fin (2 * n) → ℕ) :
    window (cycleAt c) 0 (2 * n) = ∑ v, c v := by
  classical
  calc
    window (cycleAt c) 0 (2 * n) = ∑ i ∈ Finset.range (2 * n), cycleAt c i := by
      simp [window]
    _ = ∑ v : Fin (2 * n), cycleAt c v.val := by
      exact (Fin.sum_univ_eq_sum_range _ _).symm
    _ = ∑ v, c v := by simp

/-- A balanced root exists for every odd-total configuration on an even cycle. -/
theorem exists_balanced_root {n A : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (hA : 0 < A) (c : Fin (2 * n) → ℕ)
    (hmass : (∑ v, c v) = 2 * A - 1) :
    ∃ r : Fin (2 * n), Balanced c A r.val ∧
      A ≤ halfMass c r.val ∧ A ≤ halfMass c (r.val + n + 1) ∧
      cycleAt c (r.val + n) < c r := by
  have hm : window (cycleAt c) 0 (2 * n) = 2 * A - 1 :=
    (cycle_mass c).trans hmass
  obtain ⟨r, hr, hb⟩ := exists_window_balanced (by omega : 0 < n) hA
    (cycleAt_period c) hm
  have hprops := balanced_properties hA (cycleAt_period c) hm hb
  refine ⟨⟨r, hr⟩, hb, hprops.1, hprops.2.1, ?_⟩
  have he : cycleAt c r = c ⟨r, hr⟩ := cycleAt_fin c ⟨r, hr⟩
  change cycleAt c (r + n) < c ⟨r, hr⟩
  rw [← he]
  exact hprops.2.2

theorem balanced_root_properties {n A r : ℕ} [NeZero (2 * n)]
    (hA : 0 < A) (c : Fin (2 * n) → ℕ)
    (hmass : (∑ v, c v) = 2 * A - 1) (hb : Balanced c A r) :
    A ≤ halfMass c r ∧ A ≤ halfMass c (r + n + 1) ∧
      cycleAt c (r + n) < cycleAt c r := by
  exact balanced_properties hA (cycleAt_period c) ((cycle_mass c).trans hmass) hb

theorem balanced_endings {n A r : ℕ} [NeZero (2 * n)]
    (hn : 3 ≤ n) (c : Fin (2 * n) → ℕ)
    (hmass : (∑ v, c v) = 2 * A - 1) (hb : Balanced c A r)
    (htriple : A ≤ window (cycleAt c) (r + (n - 1)) 3) :
    Balanced c A (r + (n - 1)) ∧ Balanced c A (r + (n + 1)) := by
  exact ending_offsets_balanced hn (cycleAt_period c) ((cycle_mass c).trans hmass) hb htriple

theorem pivot_triple_bound {n A r : ℕ} [NeZero (2 * n)]
    (hn : 4 ≤ n) (c : Fin (2 * n) → ℕ)
    (hmass : (∑ v, c v) = 2 * A - 1)
    (htriple : A ≤ window (cycleAt c) (r + (n - 1)) 3) :
    window (cycleAt c) (r + (2 * n - 2)) 3 ≤ A - 1 := by
  exact pivot_triple_small hn (cycleAt_period c) ((cycle_mass c).trans hmass) htriple

end CycleStack

#print axioms CycleStack.exists_balanced_root
#print axioms CycleStack.balanced_endings
#print axioms CycleStack.pivot_triple_bound
#print axioms CycleStack.pivot_antipode_le_one
