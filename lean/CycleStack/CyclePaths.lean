import CycleStack.Cycle
import CycleStack.BalancedRoot
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fin.Rev

namespace CycleStack

@[simp] theorem cycleIndex_period {n : ℕ} [NeZero (2 * n)] (r : ℕ) :
    cycleIndex (n := n) (r + 2 * n) = cycleIndex r := by
  apply Fin.ext
  simp [cycleIndex]

/-- Translating a complete residue interval preserves distinct cyclic indices. -/
theorem cycleIndex_add_inj {n : ℕ} [NeZero (2 * n)] (r : ℕ) {i j : ℕ}
    (hi : i < 2 * n) (hj : j < 2 * n)
    (h : cycleIndex (n := n) (r + i) = cycleIndex (r + j)) : i = j := by
  have hm : Nat.ModEq (2 * n) (r + i) (r + j) := congrArg Fin.val h
  have hc : Nat.ModEq (2 * n) i j := Nat.ModEq.add_left_cancel' r hm
  exact hc.eq_of_lt_of_lt hi hj

/-- Distinct bounded backward offsets also give distinct cyclic vertices. -/
theorem cycleIndex_sub_inj {n : ℕ} [NeZero (2 * n)] (r : ℕ) {i j : ℕ}
    (hi : i < 2 * n) (hj : j < 2 * n)
    (h : cycleIndex (n := n) (r + 2 * n - i) =
      cycleIndex (r + 2 * n - j)) : i = j := by
  have hm : Nat.ModEq (2 * n) (r + 2 * n - i) (r + 2 * n - j) :=
    congrArg Fin.val h
  have ha := hm.add_right (i + j)
  have he₁ : r + 2 * n - i + (i + j) = (r + 2 * n) + j := by omega
  have he₂ : r + 2 * n - j + (i + j) = (r + 2 * n) + i := by omega
  rw [he₁, he₂] at ha
  have hc : Nat.ModEq (2 * n) j i := Nat.ModEq.add_left_cancel' (r + 2 * n) ha
  exact (hc.eq_of_lt_of_lt hj hi).symm

theorem evenCycle_adj_clockwise {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (r : ℕ) :
    (evenCycle n).Adj (cycleIndex r) (cycleIndex (r + 1)) := by
  constructor
  · intro he
    have he' : cycleIndex (n := n) (r + 0) = cycleIndex (r + 1) := by simpa using he
    have hbad := cycleIndex_add_inj r (show 0 < 2 * n by omega)
      (show 1 < 2 * n by omega) he'
    omega
  · left
    simp [cycleIndex, Nat.add_mod]

/-- A clockwise arc of k vertices, with its initial vertex included. -/
def clockwiseArc {n : ℕ} [NeZero (2 * n)] (r k : ℕ) : List (Fin (2 * n)) :=
  List.ofFn fun i : Fin k => cycleIndex (r + i.val)

/-- A counterclockwise arc of k vertices, with its initial vertex included. -/
def counterclockwiseArc {n : ℕ} [NeZero (2 * n)] (r k : ℕ) : List (Fin (2 * n)) :=
  List.ofFn fun i : Fin k => cycleIndex (r + 2 * n - i.val)

/-- L clockwise vertices after the external boundary. -/
def clockwiseArm {n : ℕ} [NeZero (2 * n)] (r L : ℕ) : List (Fin (2 * n)) :=
  clockwiseArc (r + 1) L

/-- L counterclockwise vertices after the external boundary. -/
def counterclockwiseArm {n : ℕ} [NeZero (2 * n)] (r L : ℕ) : List (Fin (2 * n)) :=
  List.ofFn fun i : Fin L => cycleIndex (r + 2 * n - (i.val + 1))

@[simp] theorem clockwiseArc_length {n : ℕ} [NeZero (2 * n)] (r k : ℕ) :
    (clockwiseArc (n := n) r k).length = k := by simp [clockwiseArc]

@[simp] theorem counterclockwiseArc_length {n : ℕ} [NeZero (2 * n)] (r k : ℕ) :
    (counterclockwiseArc (n := n) r k).length = k := by simp [counterclockwiseArc]

@[simp] theorem clockwiseArm_length {n : ℕ} [NeZero (2 * n)] (r L : ℕ) :
    (clockwiseArm (n := n) r L).length = L := by simp [clockwiseArm]

@[simp] theorem counterclockwiseArm_length {n : ℕ} [NeZero (2 * n)] (r L : ℕ) :
    (counterclockwiseArm (n := n) r L).length = L := by simp [counterclockwiseArm]

theorem clockwiseArc_succ {n : ℕ} [NeZero (2 * n)] (r k : ℕ) :
    clockwiseArc (n := n) r (k + 1) = cycleIndex r :: clockwiseArc (r + 1) k := by
  simp [clockwiseArc, List.ofFn_succ, Nat.add_left_comm, Nat.add_comm]

theorem counterclockwiseArc_succ {n : ℕ} [NeZero (2 * n)] (r k : ℕ) :
    counterclockwiseArc (n := n) r (k + 1) =
      cycleIndex r :: counterclockwiseArm r k := by
  simp [counterclockwiseArc, counterclockwiseArm, List.ofFn_succ]

theorem clockwiseArc_nodup {n k : ℕ} [NeZero (2 * n)]
    (r : ℕ) (hk : k ≤ 2 * n) : (clockwiseArc (n := n) r k).Nodup := by
  unfold clockwiseArc
  apply List.nodup_ofFn.mpr
  intro i j he
  apply Fin.ext
  exact cycleIndex_add_inj r (by omega) (by omega) he

theorem counterclockwiseArc_nodup {n k : ℕ} [NeZero (2 * n)]
    (r : ℕ) (hk : k ≤ 2 * n) : (counterclockwiseArc (n := n) r k).Nodup := by
  unfold counterclockwiseArc
  apply List.nodup_ofFn.mpr
  intro i j he
  apply Fin.ext
  exact cycleIndex_sub_inj r (by omega) (by omega) he

theorem clockwiseArc_isChain {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (r k : ℕ) :
    (clockwiseArc (n := n) r k).IsChain (evenCycle n).Adj := by
  unfold clockwiseArc
  apply List.isChain_ofFn.mpr
  intro i hi
  change (evenCycle n).Adj (cycleIndex (r + i)) (cycleIndex (r + (i + 1)))
  simpa [Nat.add_assoc] using evenCycle_adj_clockwise hn (r + i)

theorem counterclockwiseArc_isChain {n k : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (r : ℕ) (hk : k ≤ 2 * n) :
    (counterclockwiseArc (n := n) r k).IsChain (evenCycle n).Adj := by
  unfold counterclockwiseArc
  apply List.isChain_ofFn.mpr
  intro i hi
  change (evenCycle n).Adj (cycleIndex (r + 2 * n - i))
    (cycleIndex (r + 2 * n - (i + 1)))
  have hc := evenCycle_adj_clockwise hn (r + 2 * n - (i + 1))
  have he : r + 2 * n - (i + 1) + 1 = r + 2 * n - i := by omega
  rw [he] at hc
  exact ⟨hc.1.symm, hc.2.symm⟩

theorem clockwiseArm_isChain {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (r L : ℕ) :
    (cycleIndex r :: clockwiseArm (n := n) r L).IsChain (evenCycle n).Adj := by
  change (cycleIndex r :: clockwiseArc (r + 1) L).IsChain (evenCycle n).Adj
  rw [← clockwiseArc_succ]
  exact clockwiseArc_isChain hn r (L + 1)

theorem clockwiseArm_nodup {n L : ℕ} [NeZero (2 * n)]
    (r : ℕ) (hL : L + 1 ≤ 2 * n) :
    (cycleIndex r :: clockwiseArm (n := n) r L).Nodup := by
  change (cycleIndex r :: clockwiseArc (r + 1) L).Nodup
  rw [← clockwiseArc_succ]
  exact clockwiseArc_nodup r hL

theorem counterclockwiseArm_isChain {n L : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (r : ℕ) (hL : L + 1 ≤ 2 * n) :
    (cycleIndex r :: counterclockwiseArm (n := n) r L).IsChain (evenCycle n).Adj := by
  rw [← counterclockwiseArc_succ]
  exact counterclockwiseArc_isChain hn r hL

theorem counterclockwiseArm_nodup {n L : ℕ} [NeZero (2 * n)]
    (r : ℕ) (hL : L + 1 ≤ 2 * n) :
    (cycleIndex r :: counterclockwiseArm (n := n) r L).Nodup := by
  rw [← counterclockwiseArc_succ]
  exact counterclockwiseArc_nodup r hL

/-- Appending consecutive arcs is the longer consecutive arc. -/
theorem clockwiseArc_append {n : ℕ} [NeZero (2 * n)] (r k l : ℕ) :
    clockwiseArc (n := n) r (k + l) =
      clockwiseArc r k ++ clockwiseArc (r + k) l := by
  simp [clockwiseArc, List.ofFn_add, Nat.add_assoc]

/-- The list mass agrees with the periodic finite-window mass. -/
theorem clockwiseArc_mass {n : ℕ} [NeZero (2 * n)]
    (c : Fin (2 * n) → ℕ) (r k : ℕ) :
    ((clockwiseArc r k).map c).sum = window (cycleAt c) r k := by
  unfold clockwiseArc
  rw [List.map_ofFn, Fin.sum_ofFn]
  simpa [window, cycleAt, Function.comp_def] using
    Fin.sum_univ_eq_sum_range (fun i => c (cycleIndex (r + i))) k

theorem clockwiseArm_mass {n : ℕ} [NeZero (2 * n)]
    (c : Fin (2 * n) → ℕ) (r L : ℕ) :
    ((clockwiseArm r L).map c).sum = window (cycleAt c) (r + 1) L := by
  exact clockwiseArc_mass c (r + 1) L

/-- Any full clockwise cycle lists exactly the total configuration mass. -/
theorem clockwiseArc_full_mass {n : ℕ} [NeZero (2 * n)]
    (c : Fin (2 * n) → ℕ) (r : ℕ) :
    ((clockwiseArc r (2 * n)).map c).sum = ∑ v, c v := by
  rw [clockwiseArc_mass, window_cycle_mass (cycleAt_period c), cycle_mass]

/-- Reversing a bounded natural interval does not change its sum. -/
theorem sum_reverse_window (f : ℕ → ℕ) (R k : ℕ) (hk : k ≤ R) :
    (∑ i : Fin k, f (R - (i.val + 1))) = window f (R - k) k := by
  calc
    (∑ i : Fin k, f (R - (i.val + 1))) =
        ∑ i : Fin k, f ((R - k) + i.val) := by
      refine Fintype.sum_equiv (Fin.revPerm : Equiv.Perm (Fin k)) _ _ ?_
      intro i
      apply congrArg f
      change R - (i.val + 1) = (R - k) + i.rev.val
      rw [Fin.val_rev]
      have hi := i.isLt
      omega
    _ = window f (R - k) k := by
      simpa [window] using Fin.sum_univ_eq_sum_range (fun i => f ((R - k) + i)) k

theorem counterclockwiseArm_mass {n L : ℕ} [NeZero (2 * n)]
    (c : Fin (2 * n) → ℕ) (r : ℕ) (hL : L ≤ 2 * n) :
    ((counterclockwiseArm r L).map c).sum =
      window (cycleAt c) (r + 2 * n - L) L := by
  unfold counterclockwiseArm
  rw [List.map_ofFn, Fin.sum_ofFn]
  exact sum_reverse_window (cycleAt c) (r + 2 * n) L (by omega)

theorem counterclockwiseArc_mass {n k : ℕ} [NeZero (2 * n)]
    (c : Fin (2 * n) → ℕ) (r : ℕ) (hk : k ≤ 2 * n) :
    ((counterclockwiseArc r k).map c).sum =
      window (cycleAt c) (r + 2 * n + 1 - k) k := by
  unfold counterclockwiseArc
  rw [List.map_ofFn, Fin.sum_ofFn]
  calc
    (∑ i : Fin k, c (cycleIndex (r + 2 * n - i.val))) =
        ∑ i : Fin k, cycleAt c (r + 2 * n + 1 - (i.val + 1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply congrArg c
      apply congrArg (cycleIndex (n := n))
      omega
    _ = window (cycleAt c) (r + 2 * n + 1 - k) k :=
      sum_reverse_window (cycleAt c) (r + 2 * n + 1) k (by omega)

theorem counterclockwiseArc_full_mass {n : ℕ} [NeZero (2 * n)]
    (c : Fin (2 * n) → ℕ) (r : ℕ) :
    ((counterclockwiseArc r (2 * n)).map c).sum = ∑ v, c v := by
  rw [counterclockwiseArc_mass c r (by omega)]
  have he : r + 2 * n + 1 - 2 * n = r + 1 := by omega
  rw [he, window_cycle_mass (cycleAt_period c), cycle_mass]

/-- The two open semicircular arms, root, and antipode partition total mass. -/
theorem openArms_mass {n : ℕ} [NeZero (2 * n)] (hn : 2 ≤ n)
    (c : Fin (2 * n) → ℕ) (r : ℕ) :
    cycleAt c r + ((clockwiseArm r (n - 1)).map c).sum +
      cycleAt c (r + n) + ((counterclockwiseArm r (n - 1)).map c).sum =
        ∑ v, c v := by
  rw [clockwiseArm_mass, counterclockwiseArm_mass c r (by omega)]
  have he : r + 2 * n - (n - 1) = r + n + 1 := by omega
  rw [he]
  have hc := half_complement (cycleAt_period c) r
  rw [cycle_mass] at hc
  have h₁ := window_head (cycleAt c) r (n - 1)
  have h₂ := window_head (cycleAt c) (r + n) (n - 1)
  have hn' : n - 1 + 1 = n := by omega
  rw [hn'] at h₁ h₂
  omega

theorem clockwise_half_mass {n : ℕ} [NeZero (2 * n)] (hn : 2 ≤ n)
    (c : Fin (2 * n) → ℕ) (r : ℕ) :
    halfMass c (r + 1) =
      ((clockwiseArm r (n - 1)).map c).sum + cycleAt c (r + n) := by
  rw [clockwiseArm_mass]
  have hs := window_succ (cycleAt c) (r + 1) (n - 1)
  have he₁ : n - 1 + 1 = n := by omega
  have he₂ : r + 1 + (n - 1) = r + n := by omega
  rw [he₁, he₂] at hs
  exact hs

theorem counterclockwise_half_mass {n : ℕ} [NeZero (2 * n)] (hn : 2 ≤ n)
    (c : Fin (2 * n) → ℕ) (r : ℕ) :
    halfMass c (r + n) =
      ((counterclockwiseArm r (n - 1)).map c).sum + cycleAt c (r + n) := by
  rw [counterclockwiseArm_mass c r (by omega)]
  have hs := window_head (cycleAt c) (r + n) (n - 1)
  have he₁ : n - 1 + 1 = n := by omega
  have he₂ : r + 2 * n - (n - 1) = r + n + 1 := by omega
  rw [he₁] at hs
  rw [he₂]
  exact hs.trans (Nat.add_comm _ _)

theorem clockwise_offset_bijective {n : ℕ} [NeZero (2 * n)] (r : ℕ) :
    Function.Bijective (fun i : Fin (2 * n) => cycleIndex (n := n) (r + i.val)) := by
  have hi : Function.Injective
      (fun i : Fin (2 * n) => cycleIndex (n := n) (r + i.val)) := by
    intro i j he
    apply Fin.ext
    exact cycleIndex_add_inj r i.isLt j.isLt he
  exact ⟨hi, Finite.surjective_of_injective hi⟩

theorem mem_clockwiseArc_full {n : ℕ} [NeZero (2 * n)]
    (r : ℕ) (v : Fin (2 * n)) : v ∈ clockwiseArc r (2 * n) := by
  obtain ⟨i, hi⟩ := (clockwise_offset_bijective (n := n) r).2 v
  exact List.mem_ofFn.mpr ⟨i, hi⟩

/-- Every vertex is the root, an open-arm vertex, or the antipode. -/
theorem openArms_cover {n : ℕ} [NeZero (2 * n)] (hn : 2 ≤ n)
    (r : ℕ) (v : Fin (2 * n)) :
    v = cycleIndex r ∨ v ∈ clockwiseArm r (n - 1) ∨
      v = cycleIndex (r + n) ∨ v ∈ counterclockwiseArm r (n - 1) := by
  obtain ⟨i, hi⟩ := (clockwise_offset_bijective (n := n) r).2 v
  have hiLt := i.isLt
  by_cases hz : i.val = 0
  · left
    simpa [hz] using hi.symm
  by_cases hlt : i.val < n
  · right; left
    apply List.mem_ofFn.mpr
    refine ⟨⟨i.val - 1, by omega⟩, ?_⟩
    change cycleIndex (r + 1 + (i.val - 1)) = v
    have he : r + 1 + (i.val - 1) = r + i.val := by omega
    rw [he]
    exact hi
  by_cases heq : i.val = n
  · right; right; left
    simpa [heq] using hi.symm
  · right; right; right
    apply List.mem_ofFn.mpr
    refine ⟨⟨2 * n - i.val - 1, by omega⟩, ?_⟩
    change cycleIndex (r + 2 * n - (2 * n - i.val - 1 + 1)) = v
    have he : r + 2 * n - (2 * n - i.val - 1 + 1) = r + i.val := by omega
    rw [he]
    exact hi

theorem openArms_disjoint {n : ℕ} [NeZero (2 * n)] (hn : 2 ≤ n) (r : ℕ) :
    List.Disjoint (clockwiseArm (n := n) r (n - 1))
      (counterclockwiseArm r (n - 1)) := by
  apply List.disjoint_left.mpr
  intro v hv hw
  change v ∈ List.ofFn (fun i : Fin (n - 1) => cycleIndex (r + 1 + i.val)) at hv
  change v ∈ List.ofFn
    (fun i : Fin (n - 1) => cycleIndex (r + 2 * n - (i.val + 1))) at hw
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hv
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hw
  have hiLt := i.isLt
  have hjLt := j.isLt
  have he := hi.trans hj.symm
  have he₁ : r + 1 + i.val = r + (i.val + 1) := by omega
  have he₂ : r + 2 * n - (j.val + 1) = r + (2 * n - (j.val + 1)) := by omega
  rw [he₁, he₂] at he
  have hbad := cycleIndex_add_inj r (show i.val + 1 < 2 * n by omega)
    (show 2 * n - (j.val + 1) < 2 * n by omega) he
  omega

end CycleStack

#print axioms CycleStack.clockwiseArc_nodup
#print axioms CycleStack.counterclockwiseArc_nodup
#print axioms CycleStack.clockwiseArm_isChain
#print axioms CycleStack.counterclockwiseArm_isChain
#print axioms CycleStack.clockwiseArc_full_mass
#print axioms CycleStack.counterclockwiseArc_full_mass
#print axioms CycleStack.openArms_mass
#print axioms CycleStack.openArms_cover
#print axioms CycleStack.openArms_disjoint
