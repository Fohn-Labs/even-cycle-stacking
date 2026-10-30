import CycleStack.LocalClearing
import CycleStack.CycleReduction

namespace CycleStack

open TreeStack

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The charged shortening argument is independent of the direction chosen
around the cycle. `P` is the short arm, `x` its even ending, `w` its inward
neighbour, `b` the antipode, and `y` the retained neighbour of the antipode. -/
theorem clear_even_ending {G : SimpleGraph V} (C : Configuration V)
    (root x w b y : V) (P : List V) (A B k : ℕ)
    (hp : PathArm G root P) (hd : ((root :: P) ++ [x, b, y]).Nodup)
    (hw : w ∈ P) (hxw : G.Adj x w) (hby : G.Adj b y)
    (hx : C x = 2 * k) (hPower : 2 ^ (P.length + 1) = B)
    (hB : 2 ≤ B) (hAB : A = 2 * B)
    (hRoot : 4 ≤ C root) (hb : 3 ≤ C b)
    (hRootMass : A ≤ C root + (P.map C).sum + C x)
    (hArmMass : (P.map C).sum + C x + C b + 1 ≤ A)
    (hThree : C b = 3 → 0 < C y) :
    ∃ D : Configuration V,
      Reach G C D ∧ (∀ v ∈ P, D v = 0) ∧ D x = 0 ∧ D b = 0 ∧
      mass C ≤ mass D + A := by
  have hSep := (List.nodup_append.mp hd).2.2
  have hNot : ∀ z ∈ [x, b, y], z ∉ root :: P := by
    intro z hz hmem
    exact hSep z hmem z hz rfl
  have hxy : x ≠ y := by
    have ht := (List.nodup_cons.mp (List.nodup_append.mp hd).2.1).1
    intro h
    exact ht (by simp [h])
  have hxb : x ≠ b := by
    have ht := (List.nodup_cons.mp (List.nodup_append.mp hd).2.1).1
    intro h
    exact ht (by simp [h])
  have hwy : w ≠ y := hSep w (by simp [hw]) y (by simp)
  have hwb : w ≠ b := hSep w (by simp [hw]) b (by simp)
  have hrx : root ≠ x := hSep root (by simp) x (by simp)
  have hrw : root ≠ w := by intro h; subst w; exact hp.not_mem hw
  obtain ⟨C₁, hCC₁, hC₁x, hC₁w, hC₁other⟩ :=
    reach_repeat_move hxw C k (by omega)
  have hC₁xZero : C₁ x = 0 := by omega
  have hC₁root : C₁ root = C root := hC₁other root hrx hrw
  have hC₁b : C₁ b = C b := hC₁other b hxb.symm hwb.symm
  have hC₁y : C₁ y = C y := hC₁other y hxy.symm hwy.symm
  have hMass₁ := mass_batch_ledger x w C C₁ k hxw.ne (by omega)
    hC₁x hC₁w hC₁other
  have hxP : x ∉ P := by intro h; exact hNot x (by simp) (by simp [h])
  have hPNodup : P.Nodup := (List.nodup_cons.mp hp.nodup).2
  have hPerim := mass_balance_on_list (x :: P) C C₁
    (List.nodup_cons.mpr ⟨hxP, hPNodup⟩) (by
      intro v hv
      apply hC₁other
      · intro h; subst v; exact hv (by simp)
      · intro h; subst v; exact hv (by simp [hw]))
  simp only [List.map_cons, List.sum_cons, hC₁xZero, zero_add] at hPerim
  let q : ℕ := (P.map C).sum + C x
  let M : ℕ := (P.map C₁).sum
  have hMq : M + k = q := by dsimp [M, q]; omega
  have hq : q + C b + 1 ≤ A := hArmMass
  have h2k : 2 * k ≤ q := by dsimp [q]; omega
  have hk : k ≤ B - 2 := even_ending_half_bound hB hb (by omega) h2k
  let p : ℕ := pullFuel (P.map C₁)
  have hPowerZ : (2 : ℤ) ^ (P.length + 1) = (B : ℤ) := by exact_mod_cast hPower
  have hNegBound : (armMessage (P.map C₁)).getD 0 < 0 → p + M + 1 ≤ B := by
    intro hneg
    have hh := (pullFuel_negative hneg).2
    simp only [List.length_map] at hh
    rw [hPowerZ] at hh
    dsimp [p, M]
    omega
  have hNonnegBound : 0 ≤ (armMessage (P.map C₁)).getD 0 → p ≤ 2 :=
    pullFuel_nonnegative
  have hFund : p ≤ C₁ root := by
    rw [hC₁root]
    by_cases hneg : (armMessage (P.map C₁)).getD 0 < 0
    · have hcost := hNegBound hneg
      dsimp [q] at hMq
      omega
    · have hcost := hNonnegBound (by omega)
      omega
  obtain ⟨C₂, hC₁C₂, hC₂root, hC₂zero, hC₂other⟩ := unit_pull root P C₁ hp hFund
  have hMass₂ := mass_pull_ledger root P C₁ C₂ p hp.nodup hFund
    hC₂root hC₂zero hC₂other
  have hC₂x : C₂ x = 0 := by rw [hC₂other x (hNot x (by simp)), hC₁xZero]
  have hC₂b : C₂ b = C b := by rw [hC₂other b (hNot b (by simp)), hC₁b]
  have hC₂y : C₂ y = C y := by rw [hC₂other y (hNot y (by simp)), hC₁y]
  obtain ⟨D, hC₂D, hDb, hDy, hDother, hMass₃, hLoss⟩ :=
    local_clear_with_mass hby C₂ (by omega) (by
      intro h3
      rw [hC₂y]
      exact hThree (hC₂b.symm.trans h3))
  have hBudget : k + p + M + localClearLoss (C b) ≤ A + 1 := by
    rw [hC₂b] at hLoss
    by_cases hneg : (armMessage (P.map C₁)).getD 0 < 0
    · have hcost := hNegBound hneg
      have hc := even_ending_negative_budget hB hb (by omega : 2 * k + C b + 1 ≤ 2 * B)
      omega
    · have hcost := hNonnegBound (by omega)
      have hc := even_ending_nonnegative_budget hb hq
      omega
  refine ⟨D, hCC₁.trans (hC₁C₂.trans hC₂D), ?_, ?_, hDb, ?_⟩
  · intro v hv
    rw [hDother v (hSep v (by simp [hv]) b (by simp))
      (hSep v (by simp [hv]) y (by simp))]
    exact hC₂zero v hv
  · rw [hDother x hxb hxy, hC₂x]
  · rw [hC₂b] at hMass₃
    change mass C₂ + p + M = mass C₁ + 1 at hMass₂
    omega

/-- A zero ending beside a pile of three can be cleared by donating one,
pushing a unit to that ending, returning its pair, and removing the resulting
antipodal pair. This includes an empty short arm. -/
theorem clear_three_zero_ending {G : SimpleGraph V} (C : Configuration V)
    (root x b y : V) (P : List V) (A B : ℕ)
    (hp : PathArm G x (P.reverse ++ [root]))
    (hd : ((root :: P) ++ [x, b, y]).Nodup)
    (hbx : G.Adj b x) (hby : G.Adj b y)
    (hx : C x = 0) (hb : C b = 3)
    (hPower : 2 ^ (P.length + 1) = B) (hB : 2 ≤ B) (hAB : A = 2 * B)
    (hRoot : 4 ≤ C root)
    (hRootMass : A ≤ C root + (P.map C).sum)
    (hArmMass : (P.map C).sum + 4 ≤ A) :
    ∃ D : Configuration V,
      Reach G C D ∧ (∀ v ∈ P, D v = 0) ∧ D x = 0 ∧ D b = 0 ∧
      mass C ≤ mass D + A := by
  have hSep := (List.nodup_append.mp hd).2.2
  have hNot : ∀ z ∈ [x, b, y], z ∉ root :: P := by
    intro z hz hmem
    exact hSep z hmem z hz rfl
  have hxy : x ≠ y := by
    have ht := (List.nodup_cons.mp (List.nodup_append.mp hd).2.1).1
    intro h
    exact ht (by simp [h])
  have hrootb : root ≠ b := hSep root (by simp) b (by simp)
  have hrootx : root ≠ x := hSep root (by simp) x (by simp)
  obtain ⟨C₁, hCC₁, hC₁b, hC₁x, hC₁other⟩ :=
    reach_repeat_move hbx C 1 (by omega)
  have hC₁bOne : C₁ b = 1 := by omega
  have hC₁xOne : C₁ x = 1 := by omega
  have hC₁root : C₁ root = C root := hC₁other root hrootb hrootx
  have hC₁P : ∀ v ∈ P, C₁ v = C v := by
    intro v hv
    exact hC₁other v (hSep v (by simp [hv]) b (by simp))
      (hSep v (by simp [hv]) x (by simp))
  have hMass₁ := mass_batch_ledger b x C C₁ 1 hbx.ne (by omega)
    hC₁b hC₁x hC₁other
  let M : ℕ := (P.map C).sum
  have hM : ((P.reverse).map C₁).sum = M := by
    rw [List.map_reverse, List.sum_reverse, List.map_congr_left hC₁P]
  obtain ⟨s, hs, hsmall, hlarge, hExecute⟩ := unit_push_reserve x root P.reverse C₁ hp
  have hPowerZ : (2 : ℤ) ^ (P.length + 1) = (B : ℤ) := by exact_mod_cast hPower
  simp only [List.length_reverse] at hs hsmall hlarge
  rw [hPowerZ, hM] at hs hsmall hlarge
  have hFund : s ≤ C₁ root := by
    rw [hC₁root]
    by_cases hreg : M ≤ B - 2
    · have hh := hsmall (by omega)
      dsimp [M] at hh hreg
      omega
    · have hh := hlarge (by omega)
      omega
  have hBudget : s + M + 2 ≤ A := by
    by_cases hreg : M ≤ B - 2
    · have hh := hsmall (by omega)
      omega
    · have hh := hlarge (by omega)
      dsimp [M] at hreg
      omega
  obtain ⟨C₂, hC₁C₂, hC₂x, hC₂root, hC₂zero, hC₂other⟩ := hExecute hFund
  have hC₂xTwo : C₂ x = 2 := by omega
  have hOffPush : ∀ z ∈ [b, y], z ∉ x :: (P.reverse ++ [root]) := by
    intro z hz
    have hzNot := hNot z (List.mem_cons_of_mem x hz)
    have hzr : z ≠ root := by intro h; subst z; exact hzNot (by simp)
    have hzP : z ∉ P := by intro h; exact hzNot (by simp [h])
    have hzx : z ≠ x := by
      have hz' : z = b ∨ z = y := by simpa using hz
      rcases hz' with rfl | rfl
      · exact hbx.ne
      · exact hxy.symm
    simp [hzx, hzP, hzr]
  have hC₂b : C₂ b = 1 := by rw [hC₂other b (hOffPush b (by simp)), hC₁bOne]
  have hMass₂ := mass_push_ledger x root P.reverse C₁ C₂ s hp.nodup hFund
    hC₂x hC₂root hC₂zero hC₂other
  rw [hM] at hMass₂
  obtain ⟨C₃, hC₂C₃, hC₃x, hC₃b, hC₃other⟩ :=
    reach_repeat_move hbx.symm C₂ 1 (by omega)
  have hC₃xZero : C₃ x = 0 := by omega
  have hC₃bTwo : C₃ b = 2 := by omega
  have hMass₃ := mass_batch_ledger x b C₂ C₃ 1 hbx.ne.symm (by omega)
    hC₃x hC₃b hC₃other
  obtain ⟨D, hC₃D, hDb, hDy, hDother⟩ :=
    reach_repeat_move hby C₃ 1 (by omega)
  have hDbZero : D b = 0 := by omega
  have hMass₄ := mass_batch_ledger b y C₃ D 1 hby.ne (by omega) hDb hDy hDother
  refine ⟨D, hCC₁.trans (hC₁C₂.trans (hC₂C₃.trans hC₃D)), ?_, ?_, hDbZero, ?_⟩
  · intro v hv
    have hvx := hSep v (by simp [hv]) x (by simp)
    have hvb := hSep v (by simp [hv]) b (by simp)
    have hvy := hSep v (by simp [hv]) y (by simp)
    rw [hDother v hvb hvy, hC₃other v hvx hvb]
    exact hC₂zero v (by simpa using hv)
  · rw [hDother x hbx.ne.symm hxy, hC₃xZero]
  · omega

def endingIndex {n : ℕ} [NeZero (2 * n)]
    (rev : Bool) (r i : ℕ) : Fin (2 * n) :=
  if rev then cycleIndex (r + 2 * n - i) else cycleIndex (r + i)

def endingArm {n : ℕ} [NeZero (2 * n)]
    (rev : Bool) (r L : ℕ) : List (Fin (2 * n)) :=
  if rev then counterclockwiseArm r L else clockwiseArm r L

@[simp] theorem endingArm_length {n : ℕ} [NeZero (2 * n)]
    (rev : Bool) (r L : ℕ) : (endingArm (n := n) rev r L).length = L := by
  cases rev <;> simp [endingArm]

theorem endingArm_succ {n : ℕ} [NeZero (2 * n)]
    (rev : Bool) (r L : ℕ) : endingArm (n := n) rev r (L + 1) =
      endingArm rev r L ++ [endingIndex rev r (L + 1)] := by
  cases rev
  · simpa [endingArm, endingIndex, Nat.add_assoc] using clockwiseArm_succ (n := n) r L
  · simpa [endingArm, endingIndex] using counterclockwiseArm_succ (n := n) r L

theorem endingArm_two {n : ℕ} [NeZero (2 * n)]
    (rev : Bool) (r L : ℕ) : endingArm (n := n) rev r (L + 2) =
      endingArm rev r L ++ [endingIndex rev r (L + 1), endingIndex rev r (L + 2)] := by
  have h := endingArm_succ (n := n) rev r (L + 1)
  rw [endingArm_succ (n := n) rev r L] at h
  simpa [List.append_assoc] using h

theorem endingArm_three {n : ℕ} [NeZero (2 * n)]
    (rev : Bool) (r L : ℕ) : endingArm (n := n) rev r (L + 3) =
      endingArm rev r L ++ [endingIndex rev r (L + 1),
        endingIndex rev r (L + 2), endingIndex rev r (L + 3)] := by
  have h := endingArm_succ (n := n) rev r (L + 2)
  rw [endingArm_two (n := n) rev r L] at h
  simpa [List.append_assoc] using h

private theorem ending_path {n L : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (rev : Bool) (r : ℕ) (hL : L + 1 ≤ 2 * n) :
    PathArm (evenCycle n) (cycleIndex r) (endingArm rev r L) := by
  cases rev
  · exact clockwise_pathArm hn r hL
  · exact counterclockwise_pathArm hn r hL

theorem ending_push_path {n L : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (rev : Bool) (r : ℕ) (hL : L + 2 ≤ 2 * n) :
    PathArm (evenCycle n) (endingIndex rev r (L + 1))
      ((endingArm rev r L).reverse ++ [cycleIndex r]) := by
  cases rev
  · simpa [endingIndex, endingArm, Nat.add_assoc] using clockwise_push_pathArm hn r hL
  · exact counterclockwise_push_pathArm hn r hL

theorem ending_adj {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (rev : Bool) (r i : ℕ) (hi : i + 1 ≤ 2 * n) :
    (evenCycle n).Adj (endingIndex rev r i) (endingIndex rev r (i + 1)) := by
  cases rev
  · simpa [endingIndex, Nat.add_assoc] using evenCycle_adj_clockwise hn (r + i)
  · have h := evenCycle_adj_clockwise hn (r + 2 * n - (i + 1))
    have he : r + 2 * n - (i + 1) + 1 = r + 2 * n - i := by omega
    rw [he] at h
    exact h.symm

theorem endingIndex_antipode {n : ℕ} [NeZero (2 * n)]
    (rev : Bool) (r : ℕ) : endingIndex (n := n) rev r n = cycleIndex (r + n) := by
  cases rev <;> simp [endingIndex, show r + 2 * n - n = r + n by omega]

private theorem endingArm_last_mem {n L : ℕ} [NeZero (2 * n)]
    (rev : Bool) (r : ℕ) (hL : 0 < L) :
    endingIndex (n := n) rev r L ∈ endingArm rev r L := by
  have he : L - 1 + 1 = L := by omega
  have ha := endingArm_succ (n := n) rev r (L - 1)
  rw [he] at ha
  rw [ha]
  simp

theorem ending_distinct {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (rev : Bool) (r : ℕ) :
    ((cycleIndex r :: endingArm (n := n) rev r (n - 2)) ++
      [endingIndex rev r (n - 1), cycleIndex (r + n), endingIndex rev r (n + 1)]).Nodup := by
  have hd := (ending_path hn rev r (show n + 1 + 1 ≤ 2 * n by omega)).nodup
  have he₁ : n - 2 + 1 = n - 1 := by omega
  have he₂ : n - 2 + 2 = n := by omega
  have he₃ : n - 2 + 3 = n + 1 := by omega
  have ha := endingArm_three (n := n) rev r (n - 2)
  rw [he₁, he₂, he₃, endingIndex_antipode] at ha
  rw [ha] at hd
  simpa only [List.cons_append] using hd

theorem ending_balanced_bounds {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (C : Configuration (Fin (2 * n))) (r : ℕ)
    (hmass : mass C = 2 ^ (n + 1) - 1) (hbal : Balanced C (2 ^ n) r)
    (rev : Bool) :
    2 ^ n ≤ C (cycleIndex r) + ((endingArm rev r (n - 1)).map C).sum ∧
      ((endingArm rev r (n - 1)).map C).sum + C (cycleIndex (r + n)) + 1 ≤ 2 ^ n ∧
      C (cycleIndex (r + n)) < C (cycleIndex r) := by
  have hb : halfMass C (r + 1) ≤ 2 ^ n - 1 ∧
      halfMass C (r + n) ≤ 2 ^ n - 1 := hbal
  rw [clockwise_half_mass hn C r, counterclockwise_half_mass hn C r] at hb
  change ((clockwiseArm r (n - 1)).map C).sum + C (cycleIndex (r + n)) ≤ 2 ^ n - 1 ∧
    ((counterclockwiseArm r (n - 1)).map C).sum + C (cycleIndex (r + n)) ≤ 2 ^ n - 1 at hb
  have hp := openArms_mass hn C r
  change C (cycleIndex r) + ((clockwiseArm r (n - 1)).map C).sum +
    C (cycleIndex (r + n)) + ((counterclockwiseArm r (n - 1)).map C).sum = mass C at hp
  rw [hmass, pow_succ] at hp
  have hA : 0 < (2 : ℕ) ^ n := pow_pos (by omega) _
  cases rev <;> simp only [endingArm, Bool.false_eq_true, ite_false, ite_true] <;> omega

private theorem stackable_of_oriented_even_ending {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (C : Configuration (Fin (2 * n))) (r : ℕ)
    (hmass : mass C = 2 ^ (n + 1) - 1) (hbal : Balanced C (2 ^ n) r)
    (hb : 3 ≤ C (cycleIndex (r + n))) (rev : Bool)
    (heven : C (endingIndex rev r (n - 1)) % 2 = 0)
    (hThree : C (cycleIndex (r + n)) = 3 →
      C (endingIndex rev r (n - 1)) = 0 ∨ 0 < C (endingIndex rev r (n + 1))) :
    Stackable (evenCycle n) C := by
  let root : Fin (2 * n) := cycleIndex r
  let x : Fin (2 * n) := endingIndex rev r (n - 1)
  let b : Fin (2 * n) := cycleIndex (r + n)
  let y : Fin (2 * n) := endingIndex rev r (n + 1)
  let P : List (Fin (2 * n)) := endingArm rev r (n - 2)
  have hb' : 3 ≤ C b := hb
  have hEven : C x % 2 = 0 := heven
  have he₁ : n - 2 + 1 = n - 1 := by omega
  have he₂ : n - 2 + 2 = n := by omega
  have he₃ : n - 2 + 3 = n + 1 := by omega
  have hOpen : endingArm (n := n) rev r (n - 1) = P ++ [x] := by
    simpa only [he₁] using endingArm_succ (n := n) rev r (n - 2)
  have hOpenMass : ((endingArm rev r (n - 1)).map C).sum = (P.map C).sum + C x := by
    rw [hOpen]
    simp
  have hBounds := ending_balanced_bounds hn C r hmass hbal rev
  rw [hOpenMass] at hBounds
  have hRoot : 4 ≤ C root := by change 4 ≤ C (cycleIndex r); omega
  have hRootMass : 2 ^ n ≤ C root + (P.map C).sum + C x := by
    simpa only [Nat.add_assoc] using hBounds.1
  have hArmMass : (P.map C).sum + C x + C b + 1 ≤ 2 ^ n := hBounds.2.1
  have hPower : 2 ^ (P.length + 1) = 2 ^ (n - 1) := by
    dsimp [P]
    rw [endingArm_length, he₁]
  have hB : 2 ≤ (2 : ℕ) ^ (n - 1) := by
    have hpos : 0 < (2 : ℕ) ^ (n - 2) := pow_pos (by omega) _
    have hpow : (2 : ℕ) ^ (n - 1) = 2 ^ (n - 2) * 2 := by rw [← he₁, pow_succ]
    omega
  have hAB : (2 : ℕ) ^ n = 2 * 2 ^ (n - 1) := by
    have hpow := pow_succ (2 : ℕ) (n - 1)
    have he : n - 1 + 1 = n := by omega
    rw [he] at hpow
    omega
  have hd : ((root :: P) ++ [x, b, y]).Nodup := ending_distinct hn rev r
  have hbx : (evenCycle n).Adj b x := by
    have h := ending_adj hn rev r (n - 1) (by omega)
    have he : n - 1 + 1 = n := by omega
    rw [he, endingIndex_antipode] at h
    exact h.symm
  have hby : (evenCycle n).Adj b y := by
    have h := ending_adj hn rev r n (by omega)
    rw [endingIndex_antipode] at h
    exact h
  have hClear : ∃ D : Configuration (Fin (2 * n)),
      Reach (evenCycle n) C D ∧ (∀ v ∈ P, D v = 0) ∧ D x = 0 ∧ D b = 0 ∧
      mass C ≤ mass D + 2 ^ n := by
    by_cases hZero : C b = 3 ∧ C x = 0
    · have hpPush : PathArm (evenCycle n) x (P.reverse ++ [root]) := by
        simpa only [he₁] using ending_push_path hn rev r (show n - 2 + 2 ≤ 2 * n by omega)
      exact clear_three_zero_ending C root x b y P (2 ^ n) (2 ^ (n - 1)) hpPush hd
        hbx hby hZero.2 hZero.1 hPower hB hAB hRoot (by omega) (by omega)
    · have hn3 : 3 ≤ n := by
        by_contra h
        have hn2 : n = 2 := by omega
        have hA : (2 : ℕ) ^ n = 4 := by rw [hn2]; norm_num
        have hb3 : C b = 3 := by omega
        have hx0 : C x = 0 := by omega
        exact hZero ⟨hb3, hx0⟩
      let w : Fin (2 * n) := endingIndex rev r (n - 2)
      have hw : w ∈ P := endingArm_last_mem rev r (by omega)
      have hxw : (evenCycle n).Adj x w := by
        have h := ending_adj hn rev r (n - 2) (by omega)
        rw [he₁] at h
        exact h.symm
      let k : ℕ := C x / 2
      have hxk : C x = 2 * k := by dsimp [k]; omega
      have hThree' : C b = 3 → 0 < C y := by
        intro h3
        rcases hThree h3 with hx0 | hypos
        · exact (hZero ⟨h3, hx0⟩).elim
        · exact hypos
      exact clear_even_ending C root x w b y P (2 ^ n) (2 ^ (n - 1)) k
        (ending_path hn rev r (by omega)) hd hw hxw hby hxk hPower hB hAB
        hRoot hb hRootMass hArmMass hThree'
  obtain ⟨D, hCD, hDP, hDx, hDb, hMass⟩ := hClear
  have hArm : endingArm (n := n) rev r n = P ++ [x, b] := by
    have h := endingArm_two (n := n) rev r (n - 2)
    rw [he₁, he₂, endingIndex_antipode] at h
    exact h
  have hDz : ∀ v ∈ endingArm rev r n, D v = 0 := by
    intro v hv
    rw [hArm] at hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hDP v hv
    · have hv' : v = x ∨ v = b := by simpa using hv
      rcases hv' with rfl | rfl
      · exact hDx
      · exact hDb
  have hDmass : 2 ^ n - 1 ≤ mass D := by
    rw [hmass, pow_succ] at hMass
    omega
  cases rev
  · exact stackable_of_reach_cleared_clockwise hn r hCD hDz hDmass
  · exact stackable_of_reach_cleared_counterclockwise hn r hCD hDz hDmass

/-- Every balanced target-mass cycle configuration with antipodal pile at
least three and an even adjacent ending is stackable. Zero counts as even. -/
theorem stackable_of_even_ending {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (C : Configuration (Fin (2 * n))) (r : ℕ)
    (hmass : mass C = 2 ^ (n + 1) - 1) (hbal : Balanced C (2 ^ n) r)
    (hb : 3 ≤ cycleAt C (r + n))
    (heven : cycleAt C (r + (n - 1)) % 2 = 0 ∨
      cycleAt C (r + n + 1) % 2 = 0) : Stackable (evenCycle n) C := by
  have hCW : cycleAt C (r + (n - 1)) % 2 = 0 →
      (cycleAt C (r + n) = 3 → cycleAt C (r + (n - 1)) = 0 ∨
        0 < cycleAt C (r + n + 1)) → Stackable (evenCycle n) C := by
    intro he hc
    apply stackable_of_oriented_even_ending hn C r hmass hbal hb false
    · simpa [endingIndex, cycleAt] using he
    · intro h3
      simpa [endingIndex, cycleAt, Nat.add_assoc] using hc h3
  have hCCW : cycleAt C (r + n + 1) % 2 = 0 →
      (cycleAt C (r + n) = 3 → cycleAt C (r + n + 1) = 0 ∨
        0 < cycleAt C (r + (n - 1))) → Stackable (evenCycle n) C := by
    intro he hc
    have hMinus : r + 2 * n - (n - 1) = r + n + 1 := by omega
    have hPlus : r + 2 * n - (n + 1) = r + (n - 1) := by omega
    apply stackable_of_oriented_even_ending hn C r hmass hbal hb true
    · simpa [endingIndex, cycleAt, hMinus] using he
    · intro h3
      simpa [endingIndex, cycleAt, hMinus, hPlus] using hc h3
  by_cases hx0 : cycleAt C (r + (n - 1)) = 0
  · exact hCW (by rw [hx0]) (fun _ => Or.inl hx0)
  by_cases hy0 : cycleAt C (r + n + 1) = 0
  · exact hCCW (by rw [hy0]) (fun _ => Or.inl hy0)
  rcases heven with hx | hy
  · exact hCW hx (fun _ => Or.inr (by omega))
  · exact hCCW hy (fun _ => Or.inr (by omega))

end CycleStack
