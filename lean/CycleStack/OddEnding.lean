import CycleStack.CycleReduction
import CycleStack.CaseBudgets
import CycleStack.EvenEnding

namespace CycleStack

open TreeStack

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem odd_add_one {x t : ℕ} (ht : 1 ≤ t) (hx : x = 2 * t - 1) :
    x + 1 = 2 * t := by omega

private theorem odd_large_charge {A b M x s t : ℕ}
    (hb : 3 ≤ b) (ht : 1 ≤ t) (hx : x = 2 * t - 1)
    (hs : s ≤ 2) (hq : M + x + b + 1 ≤ A) :
    s + M + t + localClearLoss (b + t) ≤ A + 1 := by
  have htq : t ≤ M + x := by omega
  have hc := odd_ending_large_prefix_budget hb ht htq hs hq
  have hl := localClearLoss_le (show 3 ≤ b + t by omega)
  omega

private theorem odd_small_charge {A B b M s t : ℕ}
    (hAB : A = 2 * B) (hB : 2 ≤ B) (hb : 3 ≤ b) (ht : 1 ≤ t)
    (htriple : b + 4 * t ≤ A + 1) (hs : s + M ≤ B) :
    s + M + t + localClearLoss (b + t) ≤ A + 1 := by
  have hc := odd_ending_small_prefix_budget hB hb ht
    (show b + 4 * t ≤ 2 * B + 1 by omega)
  have hl := localClearLoss_le (show 3 ≤ b + t by omega)
  omega

/-- The odd-ending push/batch/clear construction is independent of cycle
orientation.  The internal path is listed from the original source. -/
theorem clear_odd_ending {G : SimpleGraph V} (C : Configuration V)
    (root x b y : V) (P : List V) (A B t : ℕ)
    (hp : PathArm G x (P.reverse ++ [root]))
    (hd : ((root :: P) ++ [x, b, y]).Nodup)
    (hxb : G.Adj x b) (hby : G.Adj b y)
    (ht : 1 ≤ t) (hx : C x = 2 * t - 1)
    (hPower : 2 ^ (P.length + 1) = B) (hB : 2 ≤ B) (hAB : A = 2 * B)
    (hRoot : 4 ≤ C root) (hb : 3 ≤ C b)
    (hRootMass : A ≤ C root + (P.map C).sum + C x)
    (hArmMass : (P.map C).sum + C x + C b + 1 ≤ A)
    (hmode : B - 2 ≤ (P.map C).sum ∨
      (C x ≤ B - 2 ∧ C b + 4 * t ≤ A + 1)) :
    ∃ D : Configuration V,
      Reach G C D ∧ (∀ v ∈ P, D v = 0) ∧ D x = 0 ∧ D b = 0 ∧
      mass C ≤ mass D + A := by
  let M := (P.map C).sum
  have hSep := (List.nodup_append.mp hd).2.2
  have hNot : ∀ z ∈ [x, b, y], z ∉ root :: P := by
    intro z hz hmem
    exact hSep z hmem z hz rfl
  have hxy : x ≠ y := by
    have ht' := (List.nodup_cons.mp (List.nodup_append.mp hd).2.1).1
    intro he
    exact ht' (by simp [he])
  have hbRoot : b ≠ root := by intro he; subst b; exact hNot root (by simp) (by simp)
  have hyRoot : y ≠ root := by intro he; subst y; exact hNot root (by simp) (by simp)
  have hbP : b ∉ P := by intro hv; exact hNot b (by simp) (by simp [hv])
  have hyP : y ∉ P := by intro hv; exact hNot y (by simp) (by simp [hv])
  have hbOutside : b ∉ x :: (P.reverse ++ [root]) := by
    simp [hxb.ne.symm, hbRoot, hbP]
  have hyOutside : y ∉ x :: (P.reverse ++ [root]) := by
    simp [hxy.symm, hyRoot, hyP]
  obtain ⟨s, _hbound, hsmall, hlarge, hexec⟩ := unit_push_reserve x root P.reverse C hp
  have hPowerZ : (2 : ℤ) ^ (P.length + 1) = (B : ℤ) := by exact_mod_cast hPower
  simp only [List.length_reverse, List.map_reverse, List.sum_reverse] at hsmall hlarge
  rw [hPowerZ] at hsmall hlarge
  have hSmallFuel : M ≤ B - 2 → s + M ≤ B := by
    intro hM
    have hh := hsmall (by change (M : ℤ) ≤ (B : ℤ) - 2; omega)
    change (s : ℤ) + (M : ℤ) ≤ (B : ℤ) at hh
    omega
  have hLargeFuel : B - 2 ≤ M → s ≤ 2 := by
    intro hM
    apply hlarge
    change (B : ℤ) - 2 ≤ (M : ℤ)
    omega
  have hFund : s ≤ C root := by
    by_cases hM : B - 2 ≤ M
    · have hh := hLargeFuel hM
      omega
    · have hh := hSmallFuel (by omega)
      have he := hmode.resolve_left hM
      change A ≤ C root + M + C x at hRootMass
      omega
  have hBudget : s + M + t + localClearLoss (C b + t) ≤ A + 1 := by
    by_cases hM : B - 2 ≤ M
    · exact odd_large_charge hb ht hx (hLargeFuel hM) hArmMass
    · exact odd_small_charge hAB hB hb ht (hmode.resolve_left hM).2
        (hSmallFuel (by omega))
  clear hsmall hlarge _hbound hPower hPowerZ hSmallFuel hLargeFuel
  obtain ⟨C₁, hCC₁, hC₁x, hC₁root, hC₁zero, hC₁other⟩ := hexec hFund
  have hC₁b : C₁ b = C b := hC₁other b hbOutside
  have hMass₁ := mass_push_ledger x root P.reverse C C₁ s hp.nodup hFund
    hC₁x hC₁root hC₁zero hC₁other
  simp only [List.map_reverse, List.sum_reverse] at hMass₁
  change mass C₁ + s + M = mass C + 1 at hMass₁
  have hC₁x' : C₁ x = 2 * t := hC₁x.trans (odd_add_one ht hx)
  obtain ⟨C₂, hC₁C₂, hC₂x, hC₂b, hC₂other⟩ :=
    reach_repeat_move hxb C₁ t hC₁x'.ge
  have hC₂xZero : C₂ x = 0 := by simpa only [hC₁x', Nat.sub_self] using hC₂x
  have hC₂b' : C₂ b = C b + t := by simpa only [hC₁b] using hC₂b
  have hMass₂ := mass_batch_ledger x b C₁ C₂ t hxb.ne hC₁x'.ge
    hC₂x hC₂b hC₂other
  have hC₂zero : ∀ v ∈ P, C₂ v = 0 := by
    intro v hv
    rw [hC₂other v (hSep v (by simp [hv]) x (by simp))
      (hSep v (by simp [hv]) b (by simp))]
    exact hC₁zero v (by simpa using hv)
  obtain ⟨D, hC₂D, hDb, hDy, hDother, hMass₃, hLoss⟩ :=
    local_clear_with_mass hby C₂ (by omega) (by intro h3; omega)
  refine ⟨D, hCC₁.trans (hC₁C₂.trans hC₂D), ?_, ?_, hDb, ?_⟩
  · intro v hv
    rw [hDother v (hSep v (by simp [hv]) b (by simp))
      (hSep v (by simp [hv]) y (by simp))]
    exact hC₂zero v hv
  · rw [hDother x hxb.ne hxy, hC₂xZero]
  · rw [hC₂b'] at hMass₃
    omega

private theorem half_power_bounds {n : ℕ} (hn : 2 ≤ n) :
    2 ≤ (2 : ℕ) ^ (n - 1) ∧ 2 ^ n = 2 * 2 ^ (n - 1) := by
  have he₁ : n - 2 + 1 = n - 1 := by omega
  have he₂ : n - 1 + 1 = n := by omega
  have hpos : 0 < (2 : ℕ) ^ (n - 2) := pow_pos (by omega) _
  have hpow₁ : (2 : ℕ) ^ (n - 1) = 2 ^ (n - 2) * 2 := by rw [← he₁, pow_succ]
  have hpow₂ := pow_succ (2 : ℕ) (n - 1)
  rw [he₂] at hpow₂
  exact ⟨by omega, by omega⟩

private theorem odd_smaller_bounds {A B b x y : ℕ}
    (hAB : A = 2 * B) (hB : 2 ≤ B) (hb : 3 ≤ b)
    (hx : x % 2 = 1) (hy : y % 2 = 1) (hxy : x ≤ y)
    (htriple : b + x + y ≤ A - 1) :
    x ≤ B - 2 ∧ b + 4 * ((x + 1) / 2) ≤ A + 1 := by
  let t := (x + 1) / 2
  let u := (y + 1) / 2
  have ht : 1 ≤ t := by dsimp [t]; omega
  have hu : 1 ≤ u := by dsimp [u]; omega
  have hxt : x = 2 * t - 1 := by dsimp [t]; omega
  have hyu : y = 2 * u - 1 := by dsimp [u]; omega
  have htu : t ≤ u := by dsimp [t, u]; omega
  have he := odd_ending_small_ending_bound hB hb ht htu
    (show b + (2 * t - 1) + (2 * u - 1) + 1 ≤ 2 * B by omega)
  exact ⟨by omega, by change b + 4 * t ≤ A + 1; omega⟩

private theorem stackable_of_oriented_odd_ending {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (C : Configuration (Fin (2 * n))) (r : ℕ)
    (hmass : mass C = 2 ^ (n + 1) - 1) (hbal : Balanced C (2 ^ n) r)
    (hb : 3 ≤ C (cycleIndex (r + n))) (rev : Bool)
    (hodd : C (endingIndex rev r (n - 1)) % 2 = 1)
    (hmode : 2 ^ (n - 1) - 2 ≤ ((endingArm rev r (n - 2)).map C).sum ∨
      (C (endingIndex rev r (n - 1)) ≤ 2 ^ (n - 1) - 2 ∧
        C (cycleIndex (r + n)) + 4 * ((C (endingIndex rev r (n - 1)) + 1) / 2) ≤
          2 ^ n + 1)) : Stackable (evenCycle n) C := by
  let root : Fin (2 * n) := cycleIndex r
  let x : Fin (2 * n) := endingIndex rev r (n - 1)
  let b : Fin (2 * n) := cycleIndex (r + n)
  let y : Fin (2 * n) := endingIndex rev r (n + 1)
  let P : List (Fin (2 * n)) := endingArm rev r (n - 2)
  let t : ℕ := (C x + 1) / 2
  have ht : 1 ≤ t := by dsimp [t, x]; omega
  have hx : C x = 2 * t - 1 := by dsimp [t, x]; omega
  have he₁ : n - 2 + 1 = n - 1 := by omega
  have he₂ : n - 2 + 2 = n := by omega
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
  obtain ⟨hB, hAB⟩ := half_power_bounds hn
  have hd : ((root :: P) ++ [x, b, y]).Nodup := ending_distinct hn rev r
  have hxb : (evenCycle n).Adj x b := by
    have h := ending_adj hn rev r (n - 1) (by omega)
    have he : n - 1 + 1 = n := by omega
    rw [he, endingIndex_antipode] at h
    exact h
  have hby : (evenCycle n).Adj b y := by
    have h := ending_adj hn rev r n (by omega)
    rw [endingIndex_antipode] at h
    exact h
  have hp : PathArm (evenCycle n) x (P.reverse ++ [root]) := by
    simpa only [he₁] using ending_push_path hn rev r (show n - 2 + 2 ≤ 2 * n by omega)
  obtain ⟨D, hCD, hDP, hDx, hDb, hMass⟩ :=
    clear_odd_ending C root x b y P (2 ^ n) (2 ^ (n - 1)) t hp hd hxb hby
      ht hx hPower hB hAB hRoot hb hRootMass hArmMass hmode
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

/-- The nonpivot odd-ending cases: either short prefix is large, or the
opposite triple is small.  The smaller ending is chosen in the latter case. -/
theorem stackable_of_odd_ending {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (C : Configuration (Fin (2 * n))) (r : ℕ)
    (hmass : mass C = 2 ^ (n + 1) - 1) (hbal : Balanced C (2 ^ n) r)
    (hb : 3 ≤ cycleAt C (r + n))
    (hx : cycleAt C (r + (n - 1)) % 2 = 1)
    (hy : cycleAt C (r + n + 1) % 2 = 1)
    (hmode : 2 ^ (n - 1) - 2 ≤ ((clockwiseArm r (n - 2)).map C).sum ∨
      2 ^ (n - 1) - 2 ≤ ((counterclockwiseArm r (n - 2)).map C).sum ∨
      cycleAt C (r + n) + cycleAt C (r + (n - 1)) + cycleAt C (r + n + 1) ≤
        2 ^ n - 1) : Stackable (evenCycle n) C := by
  let x := cycleAt C (r + (n - 1))
  let y := cycleAt C (r + n + 1)
  let b := cycleAt C (r + n)
  have hCW : (2 ^ (n - 1) - 2 ≤ ((clockwiseArm r (n - 2)).map C).sum ∨
      (x ≤ 2 ^ (n - 1) - 2 ∧ b + 4 * ((x + 1) / 2) ≤ 2 ^ n + 1)) →
      Stackable (evenCycle n) C := by
    intro h
    apply stackable_of_oriented_odd_ending hn C r hmass hbal hb false
    · simpa [endingIndex, cycleAt] using hx
    · simpa [endingArm, endingIndex, cycleAt, x, b] using h
  have hCCW : (2 ^ (n - 1) - 2 ≤ ((counterclockwiseArm r (n - 2)).map C).sum ∨
      (y ≤ 2 ^ (n - 1) - 2 ∧ b + 4 * ((y + 1) / 2) ≤ 2 ^ n + 1)) →
      Stackable (evenCycle n) C := by
    intro h
    have hMinus : r + 2 * n - (n - 1) = r + n + 1 := by omega
    apply stackable_of_oriented_odd_ending hn C r hmass hbal hb true
    · simpa [endingIndex, cycleAt, hMinus] using hy
    · simpa [endingArm, endingIndex, cycleAt, hMinus, y, b] using h
  rcases hmode with hM | hR | hK
  · exact hCW (Or.inl hM)
  · exact hCCW (Or.inl hR)
  · obtain ⟨hB, hAB⟩ := half_power_bounds hn
    by_cases hxy : x ≤ y
    · exact hCW (Or.inr (odd_smaller_bounds hAB hB hb hx hy hxy hK))
    · have hyx : y ≤ x := by omega
      have hK' : b + y + x ≤ 2 ^ n - 1 := by omega
      exact hCCW (Or.inr (odd_smaller_bounds hAB hB hb hy hx hyx hK'))

end CycleStack

#print axioms CycleStack.clear_odd_ending
#print axioms CycleStack.stackable_of_odd_ending
