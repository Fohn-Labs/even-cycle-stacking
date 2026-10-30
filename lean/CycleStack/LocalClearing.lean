import CycleStack.UnitOperations
import CycleStack.CaseBudgets
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace CycleStack

open TreeStack

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact mass accounting when all changes lie on a distinct vertex list. -/
theorem mass_balance_on_list (vs : List V) (C D : Configuration V)
    (hn : vs.Nodup) (hOutside : ∀ v, v ∉ vs → D v = C v) :
    mass D + (vs.map C).sum = mass C + (vs.map D).sum := by
  have hC := Finset.sum_sdiff (f := C)
    (Finset.subset_univ (vs.toFinset))
  have hD := Finset.sum_sdiff (f := D)
    (Finset.subset_univ (vs.toFinset))
  rw [List.sum_toFinset C hn] at hC
  rw [List.sum_toFinset D hn] at hD
  have hSame : (∑ v ∈ Finset.univ \ vs.toFinset, C v) =
      ∑ v ∈ Finset.univ \ vs.toFinset, D v := by
    apply Finset.sum_congr rfl
    intro v hv
    exact (hOutside v (by simpa using (Finset.mem_sdiff.mp hv).2)).symm
  change (∑ v ∈ Finset.univ \ vs.toFinset, C v) + (vs.map C).sum = mass C at hC
  change (∑ v ∈ Finset.univ \ vs.toFinset, D v) + (vs.map D).sum = mass D at hD
  omega

omit [Fintype V] [DecidableEq V] in
theorem list_mass_zero_of_clear (vs : List V) (D : Configuration V)
    (hz : ∀ v ∈ vs, D v = 0) : (vs.map D).sum = 0 := by
  have he : vs.map D = vs.map (fun _ => 0) := List.map_congr_left hz
  rw [he]
  simp

/-- Exact charged mass ledger for a funded unit pull. -/
theorem mass_pull_ledger (r : V) (vs : List V) (C D : Configuration V)
    (p : ℕ) (hn : (r :: vs).Nodup) (hFund : p ≤ C r)
    (hr : D r = C r - p + 1) (hz : ∀ v ∈ vs, D v = 0)
    (ho : ∀ v, v ∉ r :: vs → D v = C v) :
    mass D + p + (vs.map C).sum = mass C + 1 := by
  have hMass := mass_balance_on_list (r :: vs) C D hn ho
  have hzero := list_mass_zero_of_clear vs D hz
  simp only [List.map_cons, List.sum_cons, hzero, add_zero, hr] at hMass
  omega

/-- Exact charged mass ledger for a funded unit push. -/
theorem mass_push_ledger (t r : V) (vs : List V) (C D : Configuration V)
    (s : ℕ) (hn : (t :: (vs ++ [r])).Nodup) (hFund : s ≤ C r)
    (ht : D t = C t + 1) (hr : D r = C r - s)
    (hz : ∀ v ∈ vs, D v = 0)
    (ho : ∀ v, v ∉ t :: (vs ++ [r]) → D v = C v) :
    mass D + s + (vs.map C).sum = mass C + 1 := by
  have hMass := mass_balance_on_list (t :: (vs ++ [r])) C D hn ho
  have hzero := list_mass_zero_of_clear vs D hz
  simp only [List.map_cons, List.sum_cons, List.map_append, List.sum_append,
    List.map_nil, List.sum_nil, add_zero, hzero, ht, hr] at hMass
  omega

/-- Batched adjacent moves lose exactly their move count in total mass. -/
theorem mass_batch_ledger (u v : V) (C D : Configuration V) (k : ℕ)
    (huv : u ≠ v) (hFund : 2 * k ≤ C u)
    (hu : D u = C u - 2 * k) (hv : D v = C v + k)
    (ho : ∀ w, w ≠ u → w ≠ v → D w = C w) :
    mass D + k = mass C := by
  have hMass := mass_balance_on_list [u, v] C D (by simp [huv]) (by
    intro w hw
    apply ho
    · intro h; subst w; exact hw (by simp)
    · intro h; subst w; exact hw (by simp))
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, hu, hv] at hMass
  omega

def localClearGain (b : ℕ) : ℕ := (F (b : ℤ)).toNat

def localClearLoss (b : ℕ) : ℕ := b - localClearGain b

theorem localClearGain_cast {b : ℕ} (hb : 3 ≤ b) :
    (localClearGain b : ℤ) = F (b : ℤ) := by
  have hn : 0 ≤ F (b : ℤ) := by
    have h := F_neg_iff (b : ℤ)
    omega
  exact Int.toNat_of_nonneg hn

theorem localClearGain_le {b : ℕ} (hb : 3 ≤ b) : localClearGain b ≤ b := by
  have hc := localClearGain_cast hb
  unfold F at hc
  split_ifs at hc <;> omega

theorem localClearLoss_le {b : ℕ} (hb : 3 ≤ b) :
    localClearLoss b ≤ localClearBound b := by
  have hc := localClearGain_cast hb
  unfold localClearLoss localClearBound
  unfold F at hc
  split_ifs at hc <;> omega

omit [Fintype V] in
/-- Clear a pile into a neighbour. A pile of three needs a positive neighbour;
larger piles fund their own return move. -/
theorem local_clear {G : SimpleGraph V} {u v : V} (huv : G.Adj u v)
    (C : Configuration V) (hb : 3 ≤ C u) (hThree : C u = 3 → 0 < C v) :
    ∃ D : Configuration V,
      Reach G C D ∧ D u = 0 ∧ D v = C v + localClearGain (C u) ∧
      (∀ w, w ≠ u → w ≠ v → D w = C w) := by
  have hcast := localClearGain_cast hb
  have hpos : 0 < (C v : ℤ) + F (C u : ℤ) := by
    by_cases h3 : C u = 3
    · have hv := hThree h3
      simpa only [h3, Nat.cast_ofNat, F_three, add_zero] using
        (show 0 < (C v : ℤ) by exact_mod_cast hv)
    · have hf : 0 < F (C u : ℤ) := by
        have hzero := F_eq_zero_iff (C u : ℤ)
        omega
      omega
  obtain ⟨D, hCD, hDu, hDv, hOther⟩ :=
    reach_transfer_ge_two huv C (by omega) hpos
  refine ⟨D, hCD, hDu, ?_, hOther⟩
  omega

/-- The same local operation with exact total loss and its uniform bound. -/
theorem local_clear_with_mass {G : SimpleGraph V} {u v : V} (huv : G.Adj u v)
    (C : Configuration V) (hb : 3 ≤ C u) (hThree : C u = 3 → 0 < C v) :
    ∃ D : Configuration V,
      Reach G C D ∧ D u = 0 ∧ D v = C v + localClearGain (C u) ∧
      (∀ w, w ≠ u → w ≠ v → D w = C w) ∧
      mass D + localClearLoss (C u) = mass C ∧
      localClearLoss (C u) ≤ localClearBound (C u) := by
  obtain ⟨D, hCD, hDu, hDv, hOther⟩ := local_clear huv C hb hThree
  have hMass := mass_balance_on_list [u, v] C D (by simp [huv.ne]) (by
    intro w hw
    apply hOther
    · intro h; subst w; exact hw (by simp)
    · intro h; subst w; exact hw (by simp))
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, hDu, hDv, zero_add] at hMass
  have hGain := localClearGain_le hb
  refine ⟨D, hCD, hDu, hDv, hOther, ?_, localClearLoss_le hb⟩
  unfold localClearLoss
  omega

end CycleStack
