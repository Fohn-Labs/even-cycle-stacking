import CycleStack.PathConstruction

namespace CycleStack

open TreeStack

/-- Fuel making the attained boundary total positive and one modulo three. -/
def unitPullFuel (m : ℤ) : ℕ :=
  if m < 0 then (1 - m).toNat
  else if m % 3 = 1 then 0
  else if m % 3 = 0 then 1
  else 2

theorem unitPullFuel_neg {m : ℤ} (hneg : m < 0) :
    (unitPullFuel m : ℤ) = 1 - m := by
  simp only [unitPullFuel, ite_eq_left hneg]
  exact Int.toNat_of_nonneg (by omega)

theorem unitPullFuel_nonneg {m : ℤ} (h : 0 ≤ m) : unitPullFuel m ≤ 2 := by
  unfold unitPullFuel
  split_ifs <;> omega

theorem unitPullFuel_unit (m : ℤ) :
    0 < (unitPullFuel m : ℤ) + m ∧
      ((unitPullFuel m : ℤ) + m) % 3 = 1 := by
  by_cases hneg : m < 0
  · rw [unitPullFuel_neg hneg]
    constructor <;> omega
  · unfold unitPullFuel
    simp only [ite_eq_right hneg]
    split_ifs <;> norm_num <;> omega

/-- EMPTY has numeric contribution zero and receives the harmless unit base. -/
def pullFuel (xs : List ℕ) : ℕ := unitPullFuel (armMessage xs |>.getD 0)

theorem pullFuel_unit (xs : List ℕ) :
    0 < (pullFuel xs : ℤ) + (armMessage xs).getD 0 ∧
      ((pullFuel xs : ℤ) + (armMessage xs).getD 0) % 3 = 1 :=
  unitPullFuel_unit _

theorem pullFuel_empty {xs : List ℕ} (hm : armMessage xs = none) :
    pullFuel xs = 1 := by
  norm_num [pullFuel, hm, unitPullFuel]

theorem pullFuel_nonnegative {xs : List ℕ}
    (h : 0 ≤ (armMessage xs).getD 0) : pullFuel xs ≤ 2 :=
  unitPullFuel_nonneg h

theorem pullFuel_negative {xs : List ℕ}
    (h : (armMessage xs).getD 0 < 0) :
    (pullFuel xs : ℤ) = 1 - (armMessage xs).getD 0 ∧
      (pullFuel xs : ℤ) + (xs.sum : ℤ) ≤
        (2 : ℤ) ^ (xs.length + 1) - 1 := by
  have hp := unitPullFuel_neg h
  change (pullFuel xs : ℤ) = 1 - (armMessage xs).getD 0 at hp
  refine ⟨hp, ?_⟩
  cases hm : armMessage xs with
  | none => simp [hm] at h
  | some m =>
      have hneg : m < 0 := by simpa [hm] using h
      have hmass := arm_negative_mass hm hneg
      simp only [hm, Option.getD_some] at hp
      omega

variable {V : Type*} [DecidableEq V]

/-- Pull an arm to one active pebble at its boundary. All unused boundary
pebbles are carried as an inactive configuration. -/
theorem unit_pull {G : SimpleGraph V} (r : V) (vs : List V)
    (C : Configuration V) (hp : PathArm G r vs)
    (hFund : pullFuel (vs.map C) ≤ C r) :
    ∃ D : Configuration V,
      Reach G C D ∧ D r = C r - pullFuel (vs.map C) + 1 ∧
      (∀ v ∈ vs, D v = 0) ∧
      (∀ v, v ∉ r :: vs → D v = C v) := by
  let p : ℕ := pullFuel (vs.map C)
  let A : Configuration V := Function.update C r p
  let E : Configuration V := fun v => if v = r then C r - p else 0
  have hAr : A r = p := by simp [A]
  have hmap : vs.map A = vs.map C := by
    apply List.map_congr_left
    intro v hv
    have hvr : v ≠ r := by intro h; subst v; exact hp.not_mem hv
    simp [A, hvr]
  have hdecomp : A + E = C := by
    funext v
    by_cases hvr : v = r
    · subst v
      simp only [Pi.add_apply, A, E, Function.update_self, ite_true]
      dsimp [p]
      omega
    · simp [A, E, Pi.add_apply, hvr]
  have hActive :
      ∃ B : Configuration V,
        Reach G A B ∧ B r = 1 ∧ (∀ v ∈ vs, B v = 0) ∧
        (∀ v, v ∉ r :: vs → B v = A v) := by
    cases hm : armMessage (vs.map C) with
    | none =>
        have hpOne : p = 1 := pullFuel_empty hm
        have hmA : armMessage (vs.map A) = none := by rw [hmap]; exact hm
        have hEmptyPositive : ∀ m : ℤ, armMessage (vs.map A) = some m →
            0 < (A r : ℤ) + m := by
          intro m hmsg
          rw [hmA] at hmsg
          contradiction
        obtain ⟨B, hAB, hBr, hBz, hOther⟩ :=
          path_boundary_clear r vs A hp hEmptyPositive
        have hBrOne : B r = 1 := by
          simp only [hmA, Option.getD_none, add_zero] at hBr
          rw [hAr, hpOne] at hBr
          exact_mod_cast hBr
        exact ⟨B, hAB, hBrOne, hBz, hOther⟩
    | some m =>
        have hmA : armMessage (vs.map A) = some m := by rw [hmap]; exact hm
        have hUnit := pullFuel_unit (vs.map C)
        have hpos : 0 < (A r : ℤ) + m := by simpa [hAr, p, hm] using hUnit.1
        have hres : ((A r : ℤ) + m) % 3 = 1 := by
          simpa [hAr, p, hm] using hUnit.2
        exact path_boundary_unit_of_residue r vs A m hp hmA hpos hres
  obtain ⟨B, hAB, hBr, hBz, hOther⟩ := hActive
  have hReach := reach_add hAB E
  rw [hdecomp] at hReach
  refine ⟨B + E, hReach, ?_, ?_, ?_⟩
  · simp [Pi.add_apply, E, hBr, p, Nat.add_comm]
  · intro v hv
    have hvr : v ≠ r := by intro h; subst v; exact hp.not_mem hv
    simp [Pi.add_apply, E, hvr, hBz v hv]
  · intro v hv
    have hvr : v ≠ r := by intro h; subst v; exact hv (by simp)
    simp [Pi.add_apply, E, hvr, hOther v hv, A]

/-- Quantitative pull selection, followed by the legal operation whenever
the selected fuel is available. -/
theorem unit_pull_reserve {G : SimpleGraph V} (r : V) (vs : List V)
    (C : Configuration V) (hp : PathArm G r vs) :
    ∃ p : ℕ,
      ((armMessage (vs.map C)).getD 0 < 0 →
        (p : ℤ) = 1 - (armMessage (vs.map C)).getD 0 ∧
        (p : ℤ) + ((vs.map C).sum : ℤ) ≤ (2 : ℤ) ^ (vs.length + 1) - 1) ∧
      (0 ≤ (armMessage (vs.map C)).getD 0 → p ≤ 2) ∧
      (p ≤ C r → ∃ D : Configuration V,
        Reach G C D ∧ D r = C r - p + 1 ∧ (∀ v ∈ vs, D v = 0) ∧
        (∀ v, v ∉ r :: vs → D v = C v)) := by
  refine ⟨pullFuel (vs.map C), ?_, ?_, ?_⟩
  · intro hneg
    simpa only [List.length_map] using pullFuel_negative hneg
  · exact pullFuel_nonnegative
  · exact unit_pull r vs C hp

/-- Push one active pebble to a target, preserving the target's old pile and
all source fuel beyond `s`. The internal list is ordered from the target. -/
theorem unit_push_of_message {G : SimpleGraph V} (t r : V)
    (internal : List V) (C : Configuration V) (s : ℕ) (m : ℤ)
    (hp : PathArm G t (internal ++ [r]))
    (hm : armMessage (internal.map C ++ [s]) = some m)
    (hpos : 0 < m) (hres : m % 3 = 1) (hFund : s ≤ C r) :
    ∃ D : Configuration V,
      Reach G C D ∧ D t = C t + 1 ∧ D r = C r - s ∧
      (∀ v ∈ internal, D v = 0) ∧
      (∀ v, v ∉ t :: (internal ++ [r]) → D v = C v) := by
  have htNot : t ∉ internal ++ [r] := hp.not_mem
  have htr : t ≠ r := by intro h; subst t; exact htNot (by simp)
  have htInternal : t ∉ internal := by
    intro h
    exact htNot (by simp [h])
  have hNodup : (internal ++ [r]).Nodup := (List.nodup_cons.mp hp.nodup).2
  have hrInternal : r ∉ internal := by
    intro h
    exact (List.nodup_append.mp hNodup).2.2 r h r (by simp) rfl
  let A : Configuration V := Function.update (Function.update C t 0) r s
  let E : Configuration V := fun v =>
    if v = t then C t else if v = r then C r - s else 0
  have hAt : A t = 0 := by simp [A, htr]
  have hAr : A r = s := by simp [A]
  have hAi : ∀ v ∈ internal, A v = C v := by
    intro v hv
    have hvt : v ≠ t := by intro h; subst v; exact htInternal hv
    have hvr : v ≠ r := by intro h; subst v; exact hrInternal hv
    simp [A, hvt, hvr]
  have hmap : (internal ++ [r]).map A = internal.map C ++ [s] := by
    rw [List.map_append, List.map_congr_left hAi]
    simp [hAr]
  have hmA : armMessage ((internal ++ [r]).map A) = some m := by
    rw [hmap]
    exact hm
  obtain ⟨B, hAB, hBt, hBz, hOther⟩ :=
    path_boundary_unit_of_residue t (internal ++ [r]) A m hp hmA
      (by simpa [hAt] using hpos) (by simpa [hAt] using hres)
  have hdecomp : A + E = C := by
    funext v
    by_cases hvt : v = t
    · subst v
      simp [Pi.add_apply, E, hAt]
    · by_cases hvr : v = r
      · subst v
        simp only [Pi.add_apply, hAr, E, ite_eq_right hvt, ite_true]
        omega
      · simp [Pi.add_apply, A, E, hvt, hvr]
  have hReach := reach_add hAB E
  rw [hdecomp] at hReach
  have hBr : B r = 0 := hBz r (by simp)
  refine ⟨B + E, hReach, ?_, ?_, ?_, ?_⟩
  · simp [Pi.add_apply, E, hBt, Nat.add_comm]
  · simp [Pi.add_apply, E, htr.symm, hBr]
  · intro v hv
    have hvt : v ≠ t := by intro h; subst v; exact htInternal hv
    have hvr : v ≠ r := by intro h; subst v; exact hrInternal hv
    have hBv : B v = 0 := hBz v (by simp [hv])
    simp [Pi.add_apply, E, hvt, hvr, hBv]
  · intro v hv
    have hvt : v ≠ t := by intro h; subst v; exact hv (by simp)
    have hvr : v ≠ r := by intro h; subst v; exact hv (by simp)
    simp [Pi.add_apply, E, hvt, hvr, hOther v hv, A]

/-- Select unit-push fuel with both reserve regimes, and execute it once
the source contains that fuel. -/
theorem unit_push_reserve {G : SimpleGraph V} (t r : V)
    (internal : List V) (C : Configuration V)
    (hp : PathArm G t (internal ++ [r])) :
    ∃ s : ℕ,
      (s : ℤ) ≤ max ((2 : ℤ) ^ (internal.length + 1) -
        ((internal.map C).sum : ℤ)) 2 ∧
      (((internal.map C).sum : ℤ) ≤ (2 : ℤ) ^ (internal.length + 1) - 2 →
        (s : ℤ) + ((internal.map C).sum : ℤ) ≤
          (2 : ℤ) ^ (internal.length + 1)) ∧
      ((2 : ℤ) ^ (internal.length + 1) - 2 ≤ ((internal.map C).sum : ℤ) →
        s ≤ 2) ∧
      (s ≤ C r → ∃ D : Configuration V,
        Reach G C D ∧ D t = C t + 1 ∧ D r = C r - s ∧
        (∀ v ∈ internal, D v = 0) ∧
        (∀ v, v ∉ t :: (internal ++ [r]) → D v = C v)) := by
  obtain ⟨s, m, hm, hpos, hres, hbound, hsmall, hlarge⟩ :=
    arm_unit_push_reserve (internal.map C)
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · simpa only [List.length_map] using hbound
  · simpa only [List.length_map] using hsmall
  · simpa only [List.length_map] using hlarge
  · exact unit_push_of_message t r internal C s m hp hm hpos hres

end CycleStack
