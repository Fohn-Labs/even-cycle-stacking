import CycleStack.CycleReduction
import CycleStack.UnitOperations
import CycleStack.LocalClearing

namespace CycleStack

open TreeStack

private theorem small_balance_data {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (C : Configuration (Fin (2 * n))) (r : ℕ)
    (hmass : mass C = 2 ^ (n + 1) - 1) (hbal : Balanced C (2 ^ n) r) :
    4 ≤ 2 ^ n ∧
      ((clockwiseArm r (n - 1)).map C).sum + C (cycleIndex (r + n)) ≤ 2 ^ n - 1 ∧
      2 ^ n ≤ C (cycleIndex r) + ((clockwiseArm r (n - 1)).map C).sum ∧
      C (cycleIndex (r + n)) < C (cycleIndex r) ∧
      mass C = 2 * 2 ^ n - 1 := by
  have hnsub : n - 1 + 1 = n := by omega
  have hpow := two_mul_add_two_le_power (n - 1)
  rw [hnsub] at hpow
  have hA : 4 ≤ 2 ^ n := by omega
  have hm : mass C = 2 * 2 ^ n - 1 := by
    rw [pow_succ] at hmass
    omega
  have hb : halfMass C (r + 1) ≤ 2 ^ n - 1 ∧
      halfMass C (r + n) ≤ 2 ^ n - 1 := hbal
  obtain ⟨hqb, htb⟩ := hb
  rw [clockwise_half_mass hn C r] at hqb
  rw [counterclockwise_half_mass hn C r] at htb
  have hpart := openArms_mass hn C r
  change cycleAt C r + ((clockwiseArm r (n - 1)).map C).sum +
    cycleAt C (r + n) + ((counterclockwiseArm r (n - 1)).map C).sum = mass C at hpart
  simp only [cycleAt] at hqb htb hpart
  refine ⟨hA, hqb, ?_, ?_, hm⟩ <;> omega

private theorem pull_fuel_affordable {xs : List ℕ} {A a b : ℕ}
    (hA : 1 ≤ A) (ha : 2 ≤ a) (hb : b ≤ 2)
    (hpow : (2 : ℤ) ^ (xs.length + 1) = (A : ℤ))
    (hqa : A ≤ a + xs.sum) (hqb : xs.sum + b ≤ A - 1) :
    pullFuel xs ≤ a ∧ pullFuel xs + xs.sum + b ≤ A + 1 := by
  by_cases hneg : (armMessage xs).getD 0 < 0
  · have hh := (pullFuel_negative hneg).2
    rw [hpow] at hh
    constructor <;> omega
  · have hp := pullFuel_nonnegative (xs := xs) (by omega)
    constructor <;> omega

private theorem offset_not_mem_open_clockwise {n j : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (r : ℕ) (hj : n ≤ j) (hjlt : j < 2 * n) :
    cycleIndex (r + j) ∉ clockwiseArm (n := n) r (n - 1) := by
  intro hv
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hv
  change cycleIndex (r + 1 + i.val) = cycleIndex (r + j) at hi
  have hiLt := i.isLt
  have he : r + 1 + i.val = r + (i.val + 1) := by omega
  rw [he] at hi
  exact (cycleIndex_add_ne r (i := i.val + 1) (j := j)
    (by omega) hjlt (by omega)) hi

private theorem antipode_not_in_open_carrier {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (r : ℕ) :
    cycleIndex (r + n) ∉ cycleIndex r :: clockwiseArm (n := n) r (n - 1) := by
  have hne : cycleIndex (n := n) r ≠ cycleIndex (r + n) := by
    simpa only [Nat.add_zero] using
      (cycleIndex_add_ne r (i := 0) (j := n) (by omega) (by omega) (by omega))
  simp only [List.mem_cons, not_or]
  exact ⟨hne.symm, offset_not_mem_open_clockwise hn r (by omega) (by omega)⟩

private theorem clear_clockwise_of_open_and_antipode {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (r : ℕ) (D : Configuration (Fin (2 * n)))
    (hz : ∀ v ∈ clockwiseArm r (n - 1), D v = 0)
    (hu : D (cycleIndex (r + n)) = 0) :
    ∀ v ∈ clockwiseArm r n, D v = 0 := by
  have hnsub : n - 1 + 1 = n := by omega
  have he : r + (n - 1) + 1 = r + n := by omega
  have hs := clockwiseArm_succ (n := n) r (n - 1)
  rw [hnsub, he] at hs
  intro v hv
  rw [hs] at hv
  rcases List.mem_append.mp hv with hv | hv
  · exact hz v hv
  · have heq := List.mem_singleton.mp hv
    simpa [heq] using hu

private theorem stackable_of_funded_open_pull {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (C : Configuration (Fin (2 * n))) (r : ℕ)
    (hu : C (cycleIndex (r + n)) = 0)
    (hFund : pullFuel ((clockwiseArm r (n - 1)).map C) ≤ C (cycleIndex r))
    (hBudget : 2 ^ n - 1 + pullFuel ((clockwiseArm r (n - 1)).map C) +
      ((clockwiseArm r (n - 1)).map C).sum ≤ mass C + 1) :
    Stackable (evenCycle n) C := by
  have hp := clockwise_pathArm (L := n - 1) hn r (by omega)
  obtain ⟨D, hCD, hDr, hDz, hOther⟩ :=
    unit_pull (cycleIndex r) (clockwiseArm r (n - 1)) C hp hFund
  have hDu : D (cycleIndex (r + n)) = 0 := by
    rw [hOther _ (antipode_not_in_open_carrier hn r)]
    exact hu
  have hm := mass_pull_ledger (cycleIndex r) (clockwiseArm r (n - 1)) C D
    (pullFuel ((clockwiseArm r (n - 1)).map C)) hp.nodup hFund hDr hDz hOther
  apply stackable_of_reach_cleared_clockwise hn r hCD
    (clear_clockwise_of_open_and_antipode hn r D hDz hDu)
  omega

/-- All balanced-root cases with antipodal pile zero, one, or two.
For antipode zero and root one, one nonnegative-score arm is cleared and
the accepted path upper bound handles the retained path. -/
theorem stackable_of_small_antipode {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (C : Configuration (Fin (2 * n))) (r : ℕ)
    (hmass : mass C = 2 ^ (n + 1) - 1) (hbal : Balanced C (2 ^ n) r)
    (hsmall : cycleAt C (r + n) ≤ 2) : Stackable (evenCycle n) C := by
  obtain ⟨hA4, hqb, hqa, hba, hm⟩ := small_balance_data hn C r hmass hbal
  let A : ℕ := 2 ^ n
  let root : Fin (2 * n) := cycleIndex r
  let anti : Fin (2 * n) := cycleIndex (r + n)
  let w : Fin (2 * n) := cycleIndex (r + n + 1)
  let Q : List (Fin (2 * n)) := clockwiseArm r (n - 1)
  let q : ℕ := (Q.map C).sum
  change 4 ≤ A at hA4
  change q + C anti ≤ A - 1 at hqb
  change A ≤ C root + q at hqa
  change C anti < C root at hba
  change mass C = 2 * A - 1 at hm
  change C anti ≤ 2 at hsmall
  have hnsub : n - 1 + 1 = n := by omega
  have hpow : (2 : ℤ) ^ ((Q.map C).length + 1) = (A : ℤ) := by
    simp [Q, A, hnsub]
  have hp : PathArm (evenCycle n) root Q :=
    clockwise_pathArm hn r (by omega)
  have hantiNot : anti ∉ root :: Q := antipode_not_in_open_carrier hn r
  have hantiQ : anti ∉ Q := by
    intro hv
    exact hantiNot (by simp [hv])
  have hwQ : w ∉ Q := by
    simpa only [w, Q, Nat.add_assoc] using
      (offset_not_mem_open_clockwise (j := n + 1) hn r (by omega) (by omega))
  have hrootAnti : root ≠ anti := by
    intro he
    exact hantiNot (by simp [he])
  have hrootW : root ≠ w := by
    simpa only [root, w, Nat.add_zero, Nat.add_assoc] using
      (cycleIndex_add_ne r (i := 0) (j := n + 1) (by omega) (by omega) (by omega))
  have hadj : (evenCycle n).Adj anti w := evenCycle_adj_clockwise hn (r + n)
  by_cases hb0 : C anti = 0
  · by_cases ha1 : C root = 1
    · have hqeq : q = A - 1 := by omega
      cases hmsg : armMessage (Q.map C) with
      | none =>
        have hz := (armMessage_eq_none_iff (Q.map C)).mp hmsg
        change q = 0 at hz
        omega
      | some m =>
        have hmnonneg : 0 ≤ m := by
          by_contra h
          have hN := arm_negative_mass hmsg (by omega)
          rw [hpow] at hN
          change (q : ℤ) - m ≤ (A : ℤ) - 2 at hN
          omega
        have hpos : 0 < (C root : ℤ) + m := by omega
        obtain ⟨D, hCD, hDr, hDz, hOther⟩ :=
          path_boundary_attainment root Q C m hp hmsg hpos
        have hDu : D anti = 0 := by rw [hOther anti hantiNot, hb0]
        have hQzero := list_mass_zero_of_clear Q D hDz
        have hM := mass_balance_on_list (root :: Q) C D hp.nodup hOther
        simp only [List.map_cons, List.sum_cons, hQzero, add_zero] at hM
        have hDroot : 1 ≤ D root := by omega
        apply stackable_of_reach_cleared_clockwise hn r hCD
          (clear_clockwise_of_open_and_antipode hn r D hDz hDu)
        change A - 1 ≤ mass D
        omega
    · have ha2 : 2 ≤ C root := by omega
      have hFuel := pull_fuel_affordable (xs := Q.map C) (A := A) (a := C root)
        (b := C anti) (by omega) ha2 hsmall hpow hqa hqb
      apply stackable_of_funded_open_pull hn C r hb0 hFuel.1
      change A - 1 + pullFuel (Q.map C) + q ≤ mass C + 1
      omega
  · by_cases hb1 : C anti = 1
    · have he : r + (n - 1) + 1 = r + n := by omega
      have hpushPath : PathArm (evenCycle n) anti (Q.reverse ++ [root]) := by
        simpa only [Q, root, anti, he] using
          (clockwise_push_pathArm (L := n - 1) hn r (by omega))
      have hQmass : (Q.reverse.map C).sum = q := by simp [q, List.map_reverse]
      have hPpow : (2 : ℤ) ^ (Q.reverse.length + 1) = (A : ℤ) := by
        simp [Q, A, hnsub]
      obtain ⟨s, _, hsSmall, _, hExec⟩ :=
        unit_push_reserve anti root Q.reverse C hpushPath
      have hqSmall : ((Q.reverse.map C).sum : ℤ) ≤
          (2 : ℤ) ^ (Q.reverse.length + 1) - 2 := by
        rw [hQmass, hPpow]
        omega
      have hsBudget := hsSmall hqSmall
      rw [hQmass, hPpow] at hsBudget
      have hsFund : s ≤ C root := by omega
      obtain ⟨E, hCE, hEt, hEr, hEz, hOther⟩ := hExec hsFund
      have hEtwo : E anti = 2 := by omega
      have hME := mass_push_ledger anti root Q.reverse C E s hpushPath.nodup
        hsFund hEt hEr hEz hOther
      rw [hQmass] at hME
      obtain ⟨D, hED, hDu, hDw, hDo⟩ := reach_repeat_move hadj E 1 (by omega)
      have hMD := mass_batch_ledger anti w E D 1 hadj.ne (by omega) hDu hDw hDo
      have hDanti : D anti = 0 := by omega
      have hDz : ∀ v ∈ Q, D v = 0 := by
        intro v hv
        have hvAnti : v ≠ anti := by intro heq; subst v; exact hantiQ hv
        have hvW : v ≠ w := by intro heq; subst v; exact hwQ hv
        rw [hDo v hvAnti hvW]
        exact hEz v (by simpa using hv)
      apply stackable_of_reach_cleared_clockwise hn r (hCE.trans hED)
        (clear_clockwise_of_open_and_antipode hn r D hDz hDanti)
      change A - 1 ≤ mass D
      omega
    · have hb2 : C anti = 2 := by omega
      have ha2 : 2 ≤ C root := by omega
      have hFuel := pull_fuel_affordable (xs := Q.map C) (A := A) (a := C root)
        (b := C anti) (by omega) ha2 hsmall hpow hqa hqb
      obtain ⟨E, hCE, hEu, hEw, hOther⟩ := reach_repeat_move hadj C 1 (by omega)
      have hME := mass_batch_ledger anti w C E 1 hadj.ne (by omega) hEu hEw hOther
      have hEanti : E anti = 0 := by omega
      have hEroot : E root = C root := hOther root hrootAnti hrootW
      have hmap : Q.map E = Q.map C := by
        apply List.map_congr_left
        intro v hv
        apply hOther
        · intro heq; subst v; exact hantiQ hv
        · intro heq; subst v; exact hwQ hv
      apply stackable_of_reach hCE
      apply stackable_of_funded_open_pull hn E r hEanti
      · change pullFuel (Q.map E) ≤ E root
        rw [hmap, hEroot]
        exact hFuel.1
      · change A - 1 + pullFuel (Q.map E) + (Q.map E).sum ≤ mass E + 1
        rw [hmap]
        change A - 1 + pullFuel (Q.map C) + q ≤ mass E + 1
        omega

end CycleStack
