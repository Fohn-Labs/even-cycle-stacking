import CycleStack.Moves
import CycleStack.MoveCounts
import CycleStack.PathFluxArithmetic

namespace CycleStack

open TreeStack

/-- The ordinary undirected path on vertices 0,...,n. -/
def pathGraph (n : ℕ) : SimpleGraph (Fin (n + 1)) where
  Adj u v := u.val + 1 = v.val ∨ v.val + 1 = u.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun v h => by rcases h with h | h <;> omega⟩

@[simp] theorem pathGraph_adj_iff {n : ℕ} (u v : Fin (n + 1)) :
    (pathGraph n).Adj u v ↔ u.val + 1 = v.val ∨ v.val + 1 = u.val := Iff.rfl

/-- Endpoint piles M and one, with all interior vertices empty. -/
def endpointConfig (n M : ℕ) : Configuration (Fin (n + 1)) :=
  fun v => if v.val = 0 then M else if v.val = n then 1 else 0

/-- The classical path lower obstruction, one below its upper threshold. -/
def pathLowerConfig (n : ℕ) : Configuration (Fin (n + 1)) :=
  endpointConfig n (2 ^ (n + 1) - 3)

@[simp] theorem endpointConfig_zero (n M : ℕ) : endpointConfig n M 0 = M := by
  simp [endpointConfig]

@[simp] theorem endpointConfig_last {n : ℕ} (hn : 1 ≤ n) (M : ℕ) :
    endpointConfig n M (Fin.last n) = 1 := by
  simp [endpointConfig, show n ≠ 0 by omega]

theorem endpointConfig_interior {n M : ℕ} (v : Fin (n + 1))
    (hzero : v.val ≠ 0) (hlast : v.val ≠ n) : endpointConfig n M v = 0 := by
  simp [endpointConfig, hzero, hlast]

private def pathNode (n i : ℕ) : Fin (n + 1) :=
  ⟨min i n, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

private theorem pathNode_val {n i : ℕ} (hi : i ≤ n) : (pathNode n i).val = i := by
  simp [pathNode, Nat.min_eq_left hi]

@[simp] private theorem pathNode_zero (n : ℕ) : pathNode n 0 = 0 := by
  apply Fin.ext
  simp [pathNode]

@[simp] private theorem pathNode_last (n : ℕ) : pathNode n n = Fin.last n := by
  apply Fin.ext
  simp [pathNode]

private theorem pathNode_self {n : ℕ} (v : Fin (n + 1)) : pathNode n v.val = v := by
  apply Fin.ext
  exact pathNode_val (by omega)

private theorem sum_one_of_support {V : Type*} [Fintype V]
    (f : V → ℕ) (a : V) (hs : ∀ v, 0 < f v → v = a) : (∑ v, f v) = f a := by
  classical
  apply Finset.sum_eq_single a
  · intro v _ hva
    by_contra hz
    exact hva (hs v (by omega))
  · simp

private theorem sum_two_of_support {V : Type*} [Fintype V]
    (f : V → ℕ) (a b : V) (hab : a ≠ b)
    (hs : ∀ v, 0 < f v → v = a ∨ v = b) : (∑ v, f v) = f a + f b := by
  classical
  apply Finset.sum_eq_add_of_mem a b (by simp) (by simp) hab
  intro v _ hv
  by_contra hz
  rcases hs v (by omega) with ha | hb
  · exact hv.1 ha
  · exact hv.2 hb

private def countRight {n : ℕ} {C D : Configuration (Fin (n + 1))}
    (m : MoveLedger (pathGraph n) C D) (i : ℕ) : ℕ :=
  m.count (pathNode n i) (pathNode n (i + 1))

private def countLeft {n : ℕ} {C D : Configuration (Fin (n + 1))}
    (m : MoveLedger (pathGraph n) C D) (i : ℕ) : ℕ :=
  m.count (pathNode n (i + 1)) (pathNode n i)

private def flowRight {n : ℕ} {C D : Configuration (Fin (n + 1))}
    (m : MoveLedger (pathGraph n) C D) (i : ℕ) : ℤ :=
  (countRight m i : ℤ) - 2 * (countLeft m i : ℤ)

private def flowLeft {n : ℕ} {C D : Configuration (Fin (n + 1))}
    (m : MoveLedger (pathGraph n) C D) (i : ℕ) : ℤ :=
  (countLeft m i : ℤ) - 2 * (countRight m i : ℤ)

private theorem neighbor_zero {n : ℕ} (hn : 1 ≤ n) (v : Fin (n + 1))
    (h : (pathGraph n).Adj v 0) : v = pathNode n 1 := by
  apply Fin.ext
  change v.val + 1 = 0 ∨ 0 + 1 = v.val at h
  rw [pathNode_val (by omega)]
  omega

private theorem neighbor_last {n : ℕ} (hn : 1 ≤ n) (v : Fin (n + 1))
    (h : (pathGraph n).Adj v (Fin.last n)) : v = pathNode n (n - 1) := by
  apply Fin.ext
  change v.val + 1 = n ∨ n + 1 = v.val at h
  rw [pathNode_val (by omega)]
  have hv := v.isLt
  omega

private theorem neighbor_middle {n i : ℕ} (hi0 : 0 < i) (hin : i < n)
    (v : Fin (n + 1)) (h : (pathGraph n).Adj v (pathNode n i)) :
    v = pathNode n (i - 1) ∨ v = pathNode n (i + 1) := by
  change v.val + 1 = (pathNode n i).val ∨ (pathNode n i).val + 1 = v.val at h
  rw [pathNode_val (by omega)] at h
  rcases h with h | h
  · left
    apply Fin.ext
    rw [pathNode_val (by omega)]
    omega
  · right
    apply Fin.ext
    rw [pathNode_val (by omega)]
    omega

private theorem ledger_balance_zero {n : ℕ} (hn : 1 ≤ n)
    {C D : Configuration (Fin (n + 1))} (m : MoveLedger (pathGraph n) C D) :
    (D 0 : ℤ) = (C 0 : ℤ) + flowLeft m 0 := by
  have hIn : (∑ v, m.count v 0) = m.count (pathNode n 1) 0 :=
    sum_one_of_support _ _ (fun v hv => neighbor_zero hn v (m.supported hv))
  have hOut : (∑ v, m.count 0 v) = m.count 0 (pathNode n 1) :=
    sum_one_of_support _ _ (fun v hv => neighbor_zero hn v (m.supported hv).symm)
  have h := m.balance 0
  rw [hIn, hOut] at h
  dsimp only [flowLeft, countLeft, countRight]
  simp only [pathNode_zero, Nat.zero_add] at *
  omega

private theorem ledger_balance_last {n : ℕ} (hn : 1 ≤ n)
    {C D : Configuration (Fin (n + 1))} (m : MoveLedger (pathGraph n) C D) :
    (D (Fin.last n) : ℤ) = (C (Fin.last n) : ℤ) + flowRight m (n - 1) := by
  have hIn : (∑ v, m.count v (Fin.last n)) = m.count (pathNode n (n - 1)) (Fin.last n) :=
    sum_one_of_support _ _ (fun v hv => neighbor_last hn v (m.supported hv))
  have hOut : (∑ v, m.count (Fin.last n) v) = m.count (Fin.last n) (pathNode n (n - 1)) :=
    sum_one_of_support _ _ (fun v hv => neighbor_last hn v (m.supported hv).symm)
  have h := m.balance (Fin.last n)
  rw [hIn, hOut] at h
  have he : n - 1 + 1 = n := by omega
  dsimp only [flowRight, countLeft, countRight]
  rw [he, pathNode_last]
  omega

private theorem ledger_balance_middle {n i : ℕ} (hi0 : 0 < i) (hin : i < n)
    {C D : Configuration (Fin (n + 1))} (m : MoveLedger (pathGraph n) C D) :
    (D (pathNode n i) : ℤ) = (C (pathNode n i) : ℤ) +
      flowRight m (i - 1) + flowLeft m i := by
  have hne : pathNode n (i - 1) ≠ pathNode n (i + 1) := by
    intro he
    have hv := congrArg Fin.val he
    rw [pathNode_val (by omega), pathNode_val (by omega)] at hv
    omega
  have hIn : (∑ v, m.count v (pathNode n i)) =
      m.count (pathNode n (i - 1)) (pathNode n i) +
        m.count (pathNode n (i + 1)) (pathNode n i) :=
    sum_two_of_support _ _ _ hne (fun v hv => neighbor_middle hi0 hin v (m.supported hv))
  have hOut : (∑ v, m.count (pathNode n i) v) =
      m.count (pathNode n i) (pathNode n (i - 1)) +
        m.count (pathNode n i) (pathNode n (i + 1)) :=
    sum_two_of_support _ _ _ hne (fun v hv => neighbor_middle hi0 hin v (m.supported hv).symm)
  have h := m.balance (pathNode n i)
  rw [hIn, hOut] at h
  simp only [Nat.cast_add] at h
  have he : i - 1 + 1 = i := by omega
  dsimp only [flowRight, flowLeft, countLeft, countRight]
  rw [he]
  omega

private theorem right_count_positive {n : ℕ} {C D : Configuration (Fin (n + 1))}
    (m : MoveLedger (pathGraph n) C D) (j : Fin (n + 1)) (hs : StackedAt D j)
    (hC : 0 < C 0) (i : ℕ) (hi : i < j.val) : 0 < countRight m i := by
  let S : Set (Fin (n + 1)) := {v | v.val ≤ i}
  have hOcc : ∃ v ∈ S, 0 < C v := ⟨0, by simp [S], hC⟩
  have hZero : ∀ v ∈ S, D v = 0 := by
    intro v hv
    apply hs.2 v
    intro he
    subst v
    change j.val ≤ i at hv
    omega
  obtain ⟨u, v, hu, hv, hcount⟩ := m.outward_positive S hOcc hZero
  have hadj := m.supported hcount
  change u.val + 1 = v.val ∨ v.val + 1 = u.val at hadj
  change u.val ≤ i at hu
  change ¬ v.val ≤ i at hv
  have hj := j.isLt
  have heU : u = pathNode n i := by
    apply Fin.ext
    rw [pathNode_val (by omega)]
    omega
  have heV : v = pathNode n (i + 1) := by
    apply Fin.ext
    rw [pathNode_val (by omega)]
    omega
  dsimp only [countRight]
  rw [← heU, ← heV]
  exact hcount

private theorem left_count_positive {n : ℕ} {C D : Configuration (Fin (n + 1))}
    (m : MoveLedger (pathGraph n) C D) (j : Fin (n + 1)) (hs : StackedAt D j)
    (hC : 0 < C (Fin.last n)) (i : ℕ) (hji : j.val ≤ i) (hin : i < n) :
    0 < countLeft m i := by
  let S : Set (Fin (n + 1)) := {v | i < v.val}
  have hOcc : ∃ v ∈ S, 0 < C v := ⟨Fin.last n, by simpa [S] using hin, hC⟩
  have hZero : ∀ v ∈ S, D v = 0 := by
    intro v hv
    apply hs.2 v
    intro he
    subst v
    change i < j.val at hv
    omega
  obtain ⟨u, v, hu, hv, hcount⟩ := m.outward_positive S hOcc hZero
  have hadj := m.supported hcount
  change u.val + 1 = v.val ∨ v.val + 1 = u.val at hadj
  change i < u.val at hu
  change ¬ i < v.val at hv
  have heU : u = pathNode n (i + 1) := by
    apply Fin.ext
    rw [pathNode_val (by omega)]
    omega
  have heV : v = pathNode n i := by
    apply Fin.ext
    rw [pathNode_val (by omega)]
    omega
  dsimp only [countLeft]
  rw [← heU, ← heV]
  exact hcount

private theorem opposite_flow_identity {n : ℕ} {C D : Configuration (Fin (n + 1))}
    (m : MoveLedger (pathGraph n) C D) (i : ℕ) :
    flowLeft m i + 2 * flowRight m i = -3 * (countLeft m i : ℤ) := by
  dsimp only [flowLeft, flowRight]
  omega

/-- The singleton end imposes an exponentially negative clearing flux.
The proof uses the positive outward count for every cleared suffix. -/
private theorem right_endpoint_flux_bound {n M : ℕ} (hn : 1 ≤ n)
    {D : Configuration (Fin (n + 1))}
    (m : MoveLedger (pathGraph n) (endpointConfig n M) D)
    (j : Fin (n + 1)) (hs : StackedAt D j) (i : ℕ)
    (hji : j.val ≤ i) (hin : i < n) :
    flowLeft m i ≤ 3 - (2 : ℤ) ^ (n - i + 1) := by
  have hCpos : 0 < endpointConfig n M (Fin.last n) := by
    rw [endpointConfig_last hn M]
    omega
  have haux : ∀ L : ℕ, ∀ i : ℕ, n - i = L → j.val ≤ i → i < n →
      flowLeft m i ≤ 3 - (2 : ℤ) ^ (n - i + 1) := by
    intro L
    induction L using Nat.strong_induction_on with
    | h L ih =>
      intro i heq hji hin
      have hOut := left_count_positive m j hs hCpos i hji hin
      have hOut' : 1 ≤ (countLeft m i : ℤ) := by omega
      have hident := opposite_flow_identity m i
      by_cases hlast : i + 1 = n
      · have hDlast : D (Fin.last n) = 0 := by
          apply hs.2
          intro he
          have hv := congrArg Fin.val he
          change n = j.val at hv
          omega
        have hb := ledger_balance_last hn m
        rw [hDlast, endpointConfig_last hn M] at hb
        have hpred : n - 1 = i := by omega
        rw [hpred] at hb
        have hpow : (2 : ℤ) ^ (n - i + 1) = 4 := by
          rw [show n - i = 1 by omega]
          norm_num
        rw [hpow]
        omega
      · have hin' : i + 1 < n := by omega
        have hc := ih (n - (i + 1)) (by omega) (i + 1) rfl (by omega) hin'
        have hDzero : D (pathNode n (i + 1)) = 0 := by
          apply hs.2
          intro he
          have hv := congrArg Fin.val he
          rw [pathNode_val (by omega)] at hv
          omega
        have hCzero : endpointConfig n M (pathNode n (i + 1)) = 0 := by
          apply endpointConfig_interior
          · rw [pathNode_val (by omega)]
            omega
          · rw [pathNode_val (by omega)]
            omega
        have hb := ledger_balance_middle (i := i + 1) (by omega) hin' m
        rw [hDzero, hCzero, show i + 1 - 1 = i by omega] at hb
        have hexp : n - i + 1 = (n - (i + 1) + 1) + 1 := by omega
        rw [hexp, pow_succ]
        omega
  exact haux (n - i) i rfl hji hin

/-- The large endpoint's clearing flux follows the transfer recursion,
including its residue. This is derived from actual directed move counts. -/
private theorem left_endpoint_flux_bounds {n : ℕ} (hn : 1 ≤ n)
    {D : Configuration (Fin (n + 1))}
    (m : MoveLedger (pathGraph n) (pathLowerConfig n) D)
    (j : Fin (n + 1)) (hs : StackedAt D j) :
    ∀ i : ℕ, i < j.val →
      flowRight m i ≤ (2 : ℤ) ^ (n - i) - 3 ∧
        flowRight m i % 3 = ((2 : ℤ) ^ (n - i) - 3) % 3 := by
  have hCpos : 0 < pathLowerConfig n 0 := by
    simpa only [pathLowerConfig, endpointConfig_zero] using lower_endpoint_mass_pos hn
  have hCcast : (pathLowerConfig n 0 : ℤ) = (2 : ℤ) ^ (n + 1) - 3 := by
    simpa only [pathLowerConfig, endpointConfig_zero] using lower_endpoint_mass_cast hn
  intro i
  induction i with
  | zero =>
    intro hi
    have hOut := right_count_positive m j hs hCpos 0 hi
    have hDzero : D 0 = 0 := by
      apply hs.2
      intro he
      have hv := congrArg Fin.val he
      change 0 = j.val at hv
      omega
    have hb := ledger_balance_zero hn m
    rw [hDzero, hCcast] at hb
    dsimp only [flowLeft] at hb
    have hbal : (2 : ℤ) ^ (n + 1) - 3 + (countLeft m 0 : ℤ) -
        2 * (countRight m 0 : ℤ) = 0 := by omega
    have hh := transfer_flux_bound (O := (countRight m 0 : ℤ))
      (I := (countLeft m 0 : ℤ)) (by omega) (by omega) hbal le_rfl rfl
    rw [F_pow_sub_three hn] at hh
    simpa only [flowRight, Nat.sub_zero] using hh
  | succ i ih =>
    intro hi
    have hj := j.isLt
    have hin : i + 1 < n := by omega
    obtain ⟨hprev, hprevmod⟩ := ih (by omega)
    have hOut := right_count_positive m j hs hCpos (i + 1) hi
    have hDzero : D (pathNode n (i + 1)) = 0 := by
      apply hs.2
      intro he
      have hv := congrArg Fin.val he
      rw [pathNode_val (by omega)] at hv
      omega
    have hCzero : pathLowerConfig n (pathNode n (i + 1)) = 0 := by
      apply endpointConfig_interior
      · rw [pathNode_val (by omega)]
        omega
      · rw [pathNode_val (by omega)]
        omega
    have hb := ledger_balance_middle (i := i + 1) (by omega) hin m
    rw [hDzero, hCzero, show i + 1 - 1 = i by omega] at hb
    dsimp only [flowLeft] at hb
    have hbal : flowRight m i + (countLeft m (i + 1) : ℤ) -
        2 * (countRight m (i + 1) : ℤ) = 0 := by omega
    have hh := transfer_flux_bound (O := (countRight m (i + 1) : ℤ))
      (I := (countLeft m (i + 1) : ℤ)) (by omega) (by omega) hbal hprev hprevmod
    have hexp : n - i = n - (i + 1) + 1 := by omega
    rw [hexp, F_pow_sub_three (by omega : 1 ≤ n - (i + 1))] at hh
    simpa only [flowRight] using hh

/-- The endpoint configuration of mass `2^(n+1)-2` cannot be stacked on
the ordinary path. Necessity is proved from legal move counts, not assumed
as a tree-score criterion. -/
theorem not_stackable_pathLower {n : ℕ} (hn : 1 ≤ n) :
    ¬ Stackable (pathGraph n) (pathLowerConfig n) := by
  rintro ⟨j, D, hReach, hs⟩
  obtain ⟨m⟩ := moveLedger_of_reach hReach
  have hj := j.isLt
  by_cases hjzero : j.val = 0
  · have he : j = 0 := Fin.ext hjzero
    subst j
    have hb := ledger_balance_zero hn m
    have hc : (pathLowerConfig n 0 : ℤ) = (2 : ℤ) ^ (n + 1) - 3 := by
      simpa only [pathLowerConfig, endpointConfig_zero] using lower_endpoint_mass_cast hn
    rw [hc] at hb
    have hr := right_endpoint_flux_bound (M := 2 ^ (n + 1) - 3) hn m 0 hs 0
      (by simp) (by omega)
    simp only [Nat.sub_zero] at hr
    change flowLeft m 0 ≤ 3 - (2 : ℤ) ^ (n + 1) at hr
    have hd : (0 : ℤ) < D 0 := by exact_mod_cast hs.1
    omega
  · by_cases hjlast : j.val = n
    · have he : j = Fin.last n := Fin.ext hjlast
      subst j
      have hb := ledger_balance_last hn m
      have hc : pathLowerConfig n (Fin.last n) = 1 := by
        simpa only [pathLowerConfig] using endpointConfig_last hn (2 ^ (n + 1) - 3)
      rw [hc] at hb
      have hl := (left_endpoint_flux_bounds hn m (Fin.last n) hs (n - 1) (by
        change n - 1 < n
        omega)).1
      rw [show n - (n - 1) = 1 by omega] at hl
      norm_num at hl
      have hd : (0 : ℤ) < D (Fin.last n) := by exact_mod_cast hs.1
      omega
    · have hjpos : 0 < j.val := by omega
      have hjlt : j.val < n := by omega
      have hb := ledger_balance_middle hjpos hjlt m
      rw [pathNode_self j] at hb
      have hc : pathLowerConfig n j = 0 := endpointConfig_interior j hjzero hjlast
      rw [hc] at hb
      have hl := (left_endpoint_flux_bounds hn m j hs (j.val - 1) (by omega)).1
      have hr := right_endpoint_flux_bound (M := 2 ^ (n + 1) - 3) hn m j hs j.val
        (by omega) hjlt
      change flowLeft m j.val ≤ 3 - (2 : ℤ) ^ (n - j.val + 1) at hr
      have hexp : n - (j.val - 1) = n - j.val + 1 := by omega
      rw [hexp] at hl
      have hd : (0 : ℤ) < D j := by exact_mod_cast hs.1
      omega

end CycleStack
