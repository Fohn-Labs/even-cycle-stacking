import TreeStack.Transfer
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.NormCast

namespace CycleStack

/-- A path arm listed from the vertex closest to its external parent.
An entirely empty arm is kept distinct from an occupied arm of message zero. -/
def armMessage : List ℕ → TreeStack.Message
  | [] => none
  | c :: cs =>
    match armMessage cs with
    | none => if c = 0 then none else some (TreeStack.F (c : ℤ))
    | some t => some (TreeStack.F ((c : ℤ) + t))

/-- The integer weighted sum recording the transfer residue. -/
def armWeight : List ℕ → ℤ
  | [] => 0
  | c :: cs => 2 * ((c : ℤ) + armWeight cs)

theorem F_mod_three (x : ℤ) :
    TreeStack.F x % 3 = (2 * x) % 3 := by
  unfold TreeStack.F
  split_ifs <;> omega

/-- The numeric EMPTY contribution is zero, so the residue identity also
holds through the transition from an empty arm to an occupied arm. -/
theorem armMessage_getD_mod_three (xs : List ℕ) :
    (armMessage xs).getD 0 % 3 = armWeight xs % 3 := by
  induction xs with
  | nil => simp [armMessage, armWeight]
  | cons c cs ih =>
    cases ht : armMessage cs with
    | none =>
      have hr : armWeight cs % 3 = 0 := by simpa [ht] using ih.symm
      by_cases hc : c = 0
      · simp only [armMessage, ht, hc, ite_eq_left, armWeight, Nat.cast_zero,
          zero_add, Option.getD_none]
        omega
      · simp only [armMessage, ht, ite_eq_right hc, Option.getD_some, armWeight]
        rw [F_mod_three]
        omega
    | some t =>
      have hr : t % 3 = armWeight cs % 3 := by simpa [ht] using ih
      simp only [armMessage, ht, Option.getD_some, armWeight]
      rw [F_mod_three]
      omega

theorem armMessage_mod_three {xs : List ℕ} {m : ℤ}
    (hm : armMessage xs = some m) : m % 3 = armWeight xs % 3 := by
  simpa [hm] using armMessage_getD_mod_three xs

theorem armWeight_mod_three_of_none {xs : List ℕ}
    (hm : armMessage xs = none) : armWeight xs % 3 = 0 := by
  simpa [hm] using (armMessage_getD_mod_three xs).symm

theorem armWeight_append (xs ys : List ℕ) :
    armWeight (xs ++ ys) = armWeight xs + (2 : ℤ) ^ xs.length * armWeight ys := by
  induction xs with
  | nil => simp [armWeight]
  | cons c cs ih =>
    simp only [List.cons_append, armWeight, List.length_cons, pow_succ]
    rw [ih]
    ring

theorem armWeight_append_singleton (xs : List ℕ) (s : ℕ) :
    armWeight (xs ++ [s]) =
      armWeight xs + (2 : ℤ) ^ (xs.length + 1) * (s : ℤ) := by
  rw [armWeight_append]
  simp only [armWeight, add_zero, pow_succ]
  ring

theorem pow_two_mod_three_cases (n : ℕ) :
    (2 : ℤ) ^ n % 3 = 1 ∨ (2 : ℤ) ^ n % 3 = 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    omega

private theorem residue_one_offset {a b : ℤ}
    (ha : a % 3 = 1 ∨ a % 3 = 2) :
    ∃ s : ℕ, s ≤ 2 ∧ (b + a * (s : ℤ)) % 3 = 1 := by
  by_cases hzero : b % 3 = 1
  · exact ⟨0, by omega, by simpa using hzero⟩
  by_cases hone : (b + a) % 3 = 1
  · exact ⟨1, by omega, by simpa using hone⟩
  refine ⟨2, by omega, ?_⟩
  change (b + a * 2) % 3 = 1
  omega

/-- Every three consecutive far-end fuel values include one in the unit
message residue class, including when the zero-fuel arm is EMPTY. -/
theorem armWeight_unit_fuel (xs : List ℕ) (base : ℕ) :
    ∃ s : ℕ, base ≤ s ∧ s ≤ base + 2 ∧ armWeight (xs ++ [s]) % 3 = 1 := by
  let a : ℤ := 2 ^ (xs.length + 1)
  let b : ℤ := armWeight xs + a * (base : ℤ)
  have ha : a % 3 = 1 ∨ a % 3 = 2 := pow_two_mod_three_cases (xs.length + 1)
  obtain ⟨d, hd, hres⟩ := residue_one_offset (a := a) (b := b) ha
  refine ⟨base + d, by omega, by omega, ?_⟩
  rw [armWeight_append_singleton]
  have heq : armWeight xs + (2 : ℤ) ^ (xs.length + 1) * ((base + d : ℕ) : ℤ) =
      b + a * (d : ℤ) := by
    push_cast
    dsimp [a, b]
    ring
  rw [heq]
  exact hres

theorem armMessage_eq_none_iff (xs : List ℕ) :
    armMessage xs = none ↔ xs.sum = 0 := by
  induction xs with
  | nil => simp [armMessage]
  | cons c cs ih =>
    cases ht : armMessage cs with
    | none =>
      have hs : cs.sum = 0 := ih.mp ht
      simp [armMessage, ht, List.sum_cons, hs]
    | some t =>
      have hs : cs.sum ≠ 0 := by
        intro hs
        have hnone := ih.mpr hs
        simp [ht] at hnone
      simp [armMessage, ht, List.sum_cons, hs]

private theorem pow_two_length_pos (xs : List ℕ) :
    (0 : ℤ) < 2 ^ xs.length := by
  exact pow_pos (by norm_num) _

private theorem pow_two_length_ge_one (xs : List ℕ) :
    (1 : ℤ) ≤ 2 ^ xs.length := by
  have := pow_two_length_pos xs
  omega

private theorem pow_two_length_ge_two {xs : List ℕ} {m : ℤ}
    (hm : armMessage xs = some m) : (2 : ℤ) ≤ 2 ^ xs.length := by
  cases xs with
  | nil => simp [armMessage] at hm
  | cons c cs =>
    have hp := pow_two_length_ge_one cs
    simp only [List.length_cons, pow_succ]
    nlinarith

private theorem F_input_upper {x : ℤ} (h : 0 ≤ TreeStack.F x) :
    x ≤ 2 * TreeStack.F x + 3 := by
  have hp := (TreeStack.F_eq_nonneg_iff h).mp rfl
  omega

/-- The simultaneous quantitative arm bounds U, N, and P. -/
theorem arm_bounds (xs : List ℕ) {m : ℤ}
    (hm : armMessage xs = some m) :
    3 - (2 : ℤ) ^ (xs.length + 1) ≤ m ∧
      (m < 0 → (xs.sum : ℤ) - m ≤ (2 : ℤ) ^ (xs.length + 1) - 2) ∧
      (0 ≤ m → (xs.sum : ℤ) ≤ (2 : ℤ) ^ xs.length * (m + 3) - 3) := by
  induction xs generalizing m with
  | nil => simp [armMessage] at hm
  | cons c cs ih =>
    let k : ℤ := 2 ^ cs.length
    have hk1 : 1 ≤ k := pow_two_length_ge_one cs
    have hc0 : (0 : ℤ) ≤ c := by omega
    have hpow1 : (2 : ℤ) ^ (c :: cs).length = 2 * k := by
      simp only [List.length_cons, pow_succ]
      dsimp [k]
      ring
    have hpow2 : (2 : ℤ) ^ ((c :: cs).length + 1) = 4 * k := by
      rw [pow_succ, hpow1]
      ring
    rw [hpow2, hpow1]
    simp only [List.sum_cons, Nat.cast_add]
    cases ht : armMessage cs with
    | none =>
      have hs : cs.sum = 0 := (armMessage_eq_none_iff cs).mp ht
      by_cases hc : c = 0
      · simp [armMessage, ht, hc] at hm
      · have hc1 : (1 : ℤ) ≤ c := by omega
        have hmeq : m = TreeStack.F (c : ℤ) := by
          simpa [armMessage, ht, hc] using hm.symm
        rw [hmeq]
        simp only [hs, Nat.cast_zero, add_zero]
        have hf_floor : -1 ≤ TreeStack.F (c : ℤ) := by
          by_cases hx : (c : ℤ) ≤ 1
          · rw [TreeStack.F_of_le_one hx]
            omega
          · have hh := TreeStack.F_neg_iff (c : ℤ)
            omega
        refine ⟨?_, ?_, ?_⟩
        · nlinarith
        · intro hn
          have hx := (TreeStack.F_neg_iff (c : ℤ)).mp hn
          rw [TreeStack.F_of_le_one hx]
          nlinarith
        · intro hp
          have hx := F_input_upper hp
          have hprod : 0 ≤ (k - 1) * (TreeStack.F (c : ℤ) + 3) :=
            mul_nonneg (by omega) (by omega)
          nlinarith
    | some t =>
      have hk2 : 2 ≤ k := pow_two_length_ge_two ht
      obtain ⟨hu, hn, hp⟩ := ih ht
      have hchildpow : (2 : ℤ) ^ (cs.length + 1) = 2 * k := by
        rw [pow_succ]
        dsimp [k]
        ring
      rw [hchildpow] at hu hn
      change (0 ≤ t → (cs.sum : ℤ) ≤ k * (t + 3) - 3) at hp
      let x : ℤ := (c : ℤ) + t
      have hxeq : x = (c : ℤ) + t := rfl
      have hmeq : m = TreeStack.F x := by
        simpa [armMessage, ht, x] using hm.symm
      rw [hmeq]
      refine ⟨?_, ?_, ?_⟩
      · by_cases hx : x ≤ 1
        · rw [TreeStack.F_of_le_one hx]
          nlinarith
        · have hh := TreeStack.F_neg_iff x
          have hf : 0 ≤ TreeStack.F x := by omega
          nlinarith
      · intro hneg
        have hx := (TreeStack.F_neg_iff x).mp hneg
        rw [TreeStack.F_of_le_one hx]
        by_cases htneg : t < 0
        · have hmass := hn htneg
          nlinarith
        · have ht0 : 0 ≤ t := by omega
          have hmass := hp ht0
          have ht_cases : t = 0 ∨ t = 1 := by omega
          rcases ht_cases with htzero | htone
          · rw [htzero] at hmass hxeq
            nlinarith
          · rw [htone] at hmass hxeq
            nlinarith
      · intro hnonneg
        have hxu := F_input_upper hnonneg
        by_cases htneg : t < 0
        · have hmass := hn htneg
          have hprod : 0 ≤ (k - 1) * (TreeStack.F x + 2) :=
            mul_nonneg (by omega) (by omega)
          nlinarith
        · have ht0 : 0 ≤ t := by omega
          have hmass := hp ht0
          have htx : t ≤ x := by omega
          have hmul : (k - 1) * t ≤ (k - 1) * x :=
            mul_le_mul_of_nonneg_left htx (by omega)
          have hmul2 : k * x ≤ k * (2 * TreeStack.F x + 3) :=
            mul_le_mul_of_nonneg_left hxu (by omega)
          nlinarith

theorem arm_message_lower {xs : List ℕ} {m : ℤ}
    (hm : armMessage xs = some m) :
    3 - (2 : ℤ) ^ (xs.length + 1) ≤ m :=
  (arm_bounds xs hm).1

theorem arm_negative_mass {xs : List ℕ} {m : ℤ}
    (hm : armMessage xs = some m) (hneg : m < 0) :
    (xs.sum : ℤ) - m ≤ (2 : ℤ) ^ (xs.length + 1) - 2 :=
  (arm_bounds xs hm).2.1 hneg

theorem arm_nonnegative_mass {xs : List ℕ} {m : ℤ}
    (hm : armMessage xs = some m) (hpos : 0 ≤ m) :
    (xs.sum : ℤ) ≤ (2 : ℤ) ^ xs.length * (m + 3) - 3 :=
  (arm_bounds xs hm).2.2 hpos

/-- A nonpositive message in the unit residue class forces mass strictly
below the unit-push cutoff. No minimum arm length is needed. -/
theorem arm_unit_mass_cutoff {xs : List ℕ} {m : ℤ}
    (hm : armMessage xs = some m) (hres : m % 3 = 1) (hnonpos : m ≤ 0) :
    (xs.sum : ℤ) ≤ (2 : ℤ) ^ xs.length - 3 := by
  cases xs with
  | nil => simp [armMessage] at hm
  | cons c cs =>
    have hc0 : (0 : ℤ) ≤ c := by omega
    cases ht : armMessage cs with
    | none =>
      by_cases hc : c = 0
      · simp [armMessage, ht, hc] at hm
      · have hmeq : TreeStack.F (c : ℤ) = m := by
          simpa [armMessage, ht, hc] using hm
        have hx : (c : ℤ) ≤ -1 := by
          unfold TreeStack.F at hmeq
          split_ifs at hmeq <;> omega
        omega
    | some t =>
      let x : ℤ := (c : ℤ) + t
      have hxeq : x = (c : ℤ) + t := rfl
      have hmeq : TreeStack.F x = m := by
        simpa [armMessage, ht, x] using hm
      have hx : x ≤ -1 := by
        unfold TreeStack.F at hmeq
        split_ifs at hmeq <;> omega
      have htneg : t < 0 := by omega
      have hmass := arm_negative_mass ht htneg
      simp only [List.sum_cons, Nat.cast_add, List.length_cons]
      nlinarith

theorem arm_unit_residue_positive {xs : List ℕ} {m : ℤ}
    (hm : armMessage xs = some m) (hres : m % 3 = 1)
    (hmass : (2 : ℤ) ^ xs.length - 2 ≤ (xs.sum : ℤ)) : 0 < m := by
  by_contra h
  have hcut := arm_unit_mass_cutoff hm hres (by omega)
  omega

/-- Numerical fuel selection for an empty target. The list records only
the internal piles; the source fuel is appended at its far end. -/
theorem arm_unit_fuel_budget (xs : List ℕ) :
    ∃ s : ℕ, armWeight (xs ++ [s]) % 3 = 1 ∧
      (2 : ℤ) ^ (xs.length + 1) - 2 ≤ (s : ℤ) + (xs.sum : ℤ) ∧
      (s : ℤ) ≤ max ((2 : ℤ) ^ (xs.length + 1) - (xs.sum : ℤ)) 2 ∧
      ((xs.sum : ℤ) ≤ (2 : ℤ) ^ (xs.length + 1) - 2 →
        (s : ℤ) + (xs.sum : ℤ) ≤ (2 : ℤ) ^ (xs.length + 1)) ∧
      ((2 : ℤ) ^ (xs.length + 1) - 2 ≤ (xs.sum : ℤ) → s ≤ 2) := by
  let T : ℤ := 2 ^ (xs.length + 1)
  let M : ℤ := xs.sum
  change ∃ s : ℕ, armWeight (xs ++ [s]) % 3 = 1 ∧
    T - 2 ≤ (s : ℤ) + M ∧ (s : ℤ) ≤ max (T - M) 2 ∧
    (M ≤ T - 2 → (s : ℤ) + M ≤ T) ∧ (T - 2 ≤ M → s ≤ 2)
  by_cases hsmall : M ≤ T - 2
  · let base : ℕ := (T - M - 2).toNat
    have hb : (base : ℤ) = T - M - 2 :=
      Int.toNat_of_nonneg (by omega)
    obtain ⟨s, hslo, hshi, hres⟩ := armWeight_unit_fuel xs base
    have hslo' : (base : ℤ) ≤ (s : ℤ) := by exact_mod_cast hslo
    have hshi' : (s : ℤ) ≤ (base : ℤ) + 2 := by exact_mod_cast hshi
    refine ⟨s, hres, ?_, ?_, ?_, ?_⟩
    · omega
    · calc
        (s : ℤ) ≤ T - M := by omega
        _ ≤ max (T - M) 2 := le_max_left _ _
    · intro _
      omega
    · intro hlarge
      omega
  · obtain ⟨s, _, hshi, hres⟩ := armWeight_unit_fuel xs 0
    have hs2 : s ≤ 2 := by omega
    have hs2' : (s : ℤ) ≤ 2 := by exact_mod_cast hs2
    have hs0 : (0 : ℤ) ≤ s := by omega
    refine ⟨s, hres, ?_, ?_, ?_, ?_⟩
    · omega
    · exact hs2'.trans (le_max_right _ _)
    · intro hle
      omega
    · intro _
      exact hs2

/-- The quantitative unit-push reserve, including its occupied message,
strictly positive score, residue, and the two mass regimes. -/
theorem arm_unit_push_reserve (xs : List ℕ) :
    ∃ (s : ℕ) (m : ℤ), armMessage (xs ++ [s]) = some m ∧
      0 < m ∧ m % 3 = 1 ∧
      (s : ℤ) ≤ max ((2 : ℤ) ^ (xs.length + 1) - (xs.sum : ℤ)) 2 ∧
      ((xs.sum : ℤ) ≤ (2 : ℤ) ^ (xs.length + 1) - 2 →
        (s : ℤ) + (xs.sum : ℤ) ≤ (2 : ℤ) ^ (xs.length + 1)) ∧
      ((2 : ℤ) ^ (xs.length + 1) - 2 ≤ (xs.sum : ℤ) → s ≤ 2) := by
  obtain ⟨s, hw, hlo, hbound, hsmall, hlarge⟩ := arm_unit_fuel_budget xs
  cases hm : armMessage (xs ++ [s]) with
  | none =>
    have hh := armWeight_mod_three_of_none hm
    omega
  | some m =>
    have hres : m % 3 = 1 := by
      have hh := armMessage_mod_three hm
      omega
    have hmass : (2 : ℤ) ^ (xs ++ [s]).length - 2 ≤ ((xs ++ [s]).sum : ℤ) := by
      simpa [List.sum_append, Nat.cast_add, add_comm] using hlo
    have hpos := arm_unit_residue_positive hm hres hmass
    exact ⟨s, m, hm, hpos, hres, hbound, hsmall, hlarge⟩

end CycleStack
