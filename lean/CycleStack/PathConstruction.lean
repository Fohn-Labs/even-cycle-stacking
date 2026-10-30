import CycleStack.ArmBounds
import CycleStack.Moves

namespace CycleStack

open TreeStack

variable {V : Type*}

/-- A simple path beginning at the external boundary.  Additional edges of
the ambient graph are allowed.  The list head is closest to the boundary. -/
def PathArm (G : SimpleGraph V) : V → List V → Prop
  | _, [] => True
  | r, u :: us => G.Adj r u ∧ PathArm G u us ∧ r ∉ u :: us

theorem PathArm.not_mem {G : SimpleGraph V} {r : V} {vs : List V}
    (h : PathArm G r vs) : r ∉ vs := by
  cases vs with
  | nil => simp
  | cons u us => exact h.2.2

theorem PathArm.isChain {G : SimpleGraph V} {r : V} {vs : List V}
    (h : PathArm G r vs) : (r :: vs).IsChain G.Adj := by
  induction vs generalizing r with
  | nil => exact .singleton r
  | cons u us ih => exact .cons_cons h.1 (ih h.2.1)

theorem PathArm.nodup {G : SimpleGraph V} {r : V} {vs : List V}
    (h : PathArm G r vs) : (r :: vs).Nodup := by
  induction vs generalizing r with
  | nil => simp
  | cons u us ih => exact List.nodup_cons.mpr ⟨h.2.2, ih h.2.1⟩

/-- Adapter from the standard consecutive-edge and distinct-vertex predicates. -/
theorem PathArm.of_chain_nodup {G : SimpleGraph V} {r : V} {vs : List V}
    (hc : (r :: vs).IsChain G.Adj) (hn : (r :: vs).Nodup) :
    PathArm G r vs := by
  induction vs generalizing r with
  | nil => trivial
  | cons u us ih =>
      obtain ⟨hadj, htail⟩ := List.isChain_cons_cons.mp hc
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      exact ⟨hadj, ih htail hnodup, hnot⟩

private theorem map_eq_of_eq_on (vs : List V) (C D : Configuration V)
    (h : ∀ v ∈ vs, C v = D v) : vs.map C = vs.map D := by
  induction vs with
  | nil => rfl
  | cons u us ih =>
      simp only [List.map_cons]
      rw [h u (by simp), ih (fun v hv => h v (by simp [hv]))]

private theorem zero_on_of_map_sum_eq_zero (vs : List V)
    (C : Configuration V) (h : (vs.map C).sum = 0) :
    ∀ v ∈ vs, C v = 0 := by
  induction vs with
  | nil => simp
  | cons u us ih =>
      simp only [List.map_cons, List.sum_cons] at h
      intro v hv
      simp only [List.mem_cons] at hv
      rcases hv with rfl | hv
      · omega
      · exact ih (by omega) v hv

variable [DecidableEq V]

/-- Constructive path-boundary sufficiency proved from legal moves.
Only vertices on this path are changed. -/
theorem path_boundary_attainment {G : SimpleGraph V} (r : V)
    (vs : List V) (C : Configuration V) (m : ℤ)
    (hp : PathArm G r vs) (hm : armMessage (vs.map C) = some m)
    (hpos : 0 < (C r : ℤ) + m) :
    ∃ D : Configuration V,
      Reach G C D ∧ (D r : ℤ) = (C r : ℤ) + m ∧
      (∀ v ∈ vs, D v = 0) ∧
      (∀ v, v ∉ r :: vs → D v = C v) := by
  induction vs generalizing r C m with
  | nil => simp [armMessage] at hm
  | cons u us ih =>
      rcases hp with ⟨hruAdj, hpTail, hrNot⟩
      have hru : r ≠ u := by
        intro h
        subst r
        exact hrNot (by simp)
      have hrTail : r ∉ us := by
        intro h
        exact hrNot (by simp [h])
      have huTail : u ∉ us := hpTail.not_mem
      let z : ℤ := (armMessage (us.map C)).getD 0
      let x : ℤ := (C u : ℤ) + z
      have hxEq : x = (C u : ℤ) + z := rfl
      have hF : F x = m := by
        cases ht : armMessage (us.map C) with
        | none =>
            by_cases hzero : C u = 0
            · simp [armMessage, ht, hzero] at hm
            · simpa [armMessage, ht, hzero, x, z] using hm
        | some t =>
            simpa [armMessage, ht, x, z] using hm
      have hposF : 0 < (C r : ℤ) + F x := by rw [hF]; exact hpos
      have hclearTail :
          ∀ E : Configuration V,
            (∀ v ∈ us, E v = C v) →
            0 < (E u : ℤ) + z →
            ∃ D : Configuration V,
              Reach G E D ∧ (D u : ℤ) = (E u : ℤ) + z ∧
              (∀ v ∈ us, D v = 0) ∧
              (∀ v, v ∉ u :: us → D v = E v) := by
        intro E hSame hEpos
        have hmap : us.map E = us.map C := map_eq_of_eq_on us E C hSame
        cases ht : armMessage (us.map C) with
        | none =>
            have hsum : (us.map C).sum = 0 :=
              (armMessage_eq_none_iff (us.map C)).mp ht
            have hzero := zero_on_of_map_sum_eq_zero us C hsum
            refine ⟨E, Relation.ReflTransGen.refl, ?_, ?_, ?_⟩
            · simp [z, ht]
            · intro v hv
              rw [hSame v hv]
              exact hzero v hv
            · intro v hv
              rfl
        | some t =>
            have hmsgE : armMessage (us.map E) = some t := by rw [hmap]; exact ht
            have hposE : 0 < (E u : ℤ) + t := by simpa [z, ht] using hEpos
            obtain ⟨D, hED, hDu, hDzero, hDother⟩ :=
              ih u E t hpTail hmsgE hposE
            refine ⟨D, hED, ?_, hDzero, hDother⟩
            simpa [z, ht] using hDu
      by_cases hx : x ≤ 1
      · let b : ℕ := (2 - x).toNat
        have hb : (b : ℤ) = 2 - x := by
          dsimp [b]
          exact Int.toNat_of_nonneg (by omega)
        have hxF : F x = 2 * x - 3 := F_of_le_one hx
        have hFund : 2 * b ≤ C r := by
          rw [hxF] at hposF
          omega
        obtain ⟨Epre, hPre, hPr, hPu, hPreOther⟩ :=
          reach_repeat_move hruAdj C b hFund
        have hSame : ∀ v ∈ us, Epre v = C v := by
          intro v hv
          apply hPreOther
          · intro h; subst v; exact hrTail hv
          · intro h; subst v; exact huTail hv
        have hEffective : (Epre u : ℤ) + z = 2 := by
          rw [hPu]
          push_cast
          omega
        obtain ⟨E, hTail, hEu, hEz, hEother⟩ :=
          hclearTail Epre hSame (by rw [hEffective]; norm_num)
        have hEuTwo : E u = 2 := by rw [hEffective] at hEu; exact_mod_cast hEu
        have hEr : E r = Epre r := hEother r hrNot
        obtain ⟨D, hFinal, hDu, hDr, hOther⟩ :=
          reach_repeat_move hruAdj.symm E 1 (by omega)
        refine ⟨D, hPre.trans (hTail.trans hFinal), ?_, ?_, ?_⟩
        · rw [hDr, hEr, hPr]
          rw [← hF, hxF]
          omega
        · intro v hv
          simp only [List.mem_cons] at hv
          rcases hv with rfl | hv
          · omega
          · rw [hOther v (by intro h; subst v; exact huTail hv)
                (by intro h; subst v; exact hrTail hv)]
            exact hEz v hv
        · intro v hv
          have hvr : v ≠ r := by intro h; subst v; exact hv (by simp)
          have hvu : v ≠ u := by intro h; subst v; exact hv (by simp)
          have hvTail : v ∉ u :: us := by intro h; exact hv (by simp [h])
          rw [hOther v hvu hvr, hEother v hvTail, hPreOther v hvr hvu]
      · have hxTwo : 2 ≤ x := by omega
        obtain ⟨E, hTail, hEu, hEz, hEother⟩ :=
          hclearTail C (fun v hv => rfl) (by omega)
        have hEuX : (E u : ℤ) = x := by simpa [x] using hEu
        have hEuTwo : 2 ≤ E u := by omega
        have hEr : E r = C r := hEother r hrNot
        have hEpos : 0 < (E r : ℤ) + F (E u : ℤ) := by
          rw [hEr, hEuX]
          exact hposF
        obtain ⟨D, hFinal, hDu, hDr, hOther⟩ :=
          reach_transfer_ge_two hruAdj.symm E hEuTwo hEpos
        refine ⟨D, hTail.trans hFinal, ?_, ?_, ?_⟩
        · rw [hDr, hEr, hEuX, hF]
        · intro v hv
          simp only [List.mem_cons] at hv
          rcases hv with rfl | hv
          · exact hDu
          · rw [hOther v (by intro h; subst v; exact huTail hv)
                (by intro h; subst v; exact hrTail hv)]
            exact hEz v hv
        · intro v hv
          have hvr : v ≠ r := by intro h; subst v; exact hv (by simp)
          have hvu : v ≠ u := by intro h; subst v; exact hv (by simp)
          have hvTail : v ∉ u :: us := by intro h; exact hv (by simp [h])
          rw [hOther v hvu hvr, hEother v hvTail]

/-- The construction yields the original graph-level stackability predicate
when there are no pebbles outside the path carrier. -/
theorem stackableAt_of_path_boundary {G : SimpleGraph V} (r : V)
    (vs : List V) (C : Configuration V) (m : ℤ)
    (hp : PathArm G r vs) (hm : armMessage (vs.map C) = some m)
    (hpos : 0 < (C r : ℤ) + m)
    (hzero : ∀ v, v ∉ r :: vs → C v = 0) : StackableAt G C r := by
  obtain ⟨D, hCD, hDr, hDz, hOther⟩ :=
    path_boundary_attainment r vs C m hp hm hpos
  refine ⟨D, hCD, ?_, ?_⟩
  · have hz : 0 < (D r : ℤ) := by rw [hDr]; exact hpos
    exact_mod_cast hz
  · intro v hvr
    by_cases hv : v ∈ vs
    · exact hDz v hv
    · have hnot : v ∉ r :: vs := by simp [hvr, hv]
      rw [hOther v hnot, hzero v hnot]

/-- The EMPTY-aware form: an empty arm is left alone, including when its
boundary is empty.  Positivity is required only for occupied arms. -/
theorem path_boundary_clear {G : SimpleGraph V} (r : V)
    (vs : List V) (C : Configuration V) (hp : PathArm G r vs)
    (hpos : ∀ m : ℤ, armMessage (vs.map C) = some m →
      0 < (C r : ℤ) + m) :
    ∃ D : Configuration V,
      Reach G C D ∧
      (D r : ℤ) = (C r : ℤ) + (armMessage (vs.map C)).getD 0 ∧
      (∀ v ∈ vs, D v = 0) ∧
      (∀ v, v ∉ r :: vs → D v = C v) := by
  cases hm : armMessage (vs.map C) with
  | none =>
      have hsum := (armMessage_eq_none_iff (vs.map C)).mp hm
      refine ⟨C, Relation.ReflTransGen.refl, ?_, ?_, ?_⟩
      · simp
      · exact zero_on_of_map_sum_eq_zero vs C hsum
      · intro v hv
        rfl
  | some m =>
      obtain ⟨D, hCD, hDr, hDz, hOther⟩ :=
        path_boundary_attainment r vs C m hp hm (hpos m hm)
      refine ⟨D, hCD, ?_, hDz, hOther⟩
      simpa [hm] using hDr

/-- A positive attained boundary total congruent to one modulo three can be
reduced to exactly one, leaving all off-path pebbles untouched. -/
theorem path_boundary_unit {G : SimpleGraph V} (r : V)
    (vs : List V) (C : Configuration V) (m : ℤ) (k : ℕ)
    (hp : PathArm G r vs) (hm : armMessage (vs.map C) = some m)
    (hfinal : (C r : ℤ) + m = 1 + 3 * (k : ℤ)) :
    ∃ D : Configuration V,
      Reach G C D ∧ D r = 1 ∧ (∀ v ∈ vs, D v = 0) ∧
      (∀ v, v ∉ r :: vs → D v = C v) := by
  have hpos : 0 < (C r : ℤ) + m := by omega
  obtain ⟨E, hCE, hEr, hEz, hEother⟩ :=
    path_boundary_attainment r vs C m hp hm hpos
  have hErNat : E r = 1 + 3 * k := by omega
  cases vs with
  | nil => simp [armMessage] at hm
  | cons u us =>
      obtain ⟨D, hED, hDr, hDu, hOther⟩ :=
        reach_burn_triples hp.1 1 k (by omega) E hErNat
      refine ⟨D, hCE.trans hED, hDr, ?_, ?_⟩
      · intro v hv
        by_cases hvu : v = u
        · subst v
          rw [hDu]
          exact hEz u (by simp)
        · have hvr : v ≠ r := by
            intro h
            subst v
            exact hp.not_mem hv
          rw [hOther v hvr hvu]
          exact hEz v hv
      · intro v hv
        have hvr : v ≠ r := by intro h; subst v; exact hv (by simp)
        have hvu : v ≠ u := by intro h; subst v; exact hv (by simp)
        rw [hOther v hvr hvu, hEother v hv]

/-- Exact-one clearing from a positive boundary total in the unit residue. -/
theorem path_boundary_unit_of_residue {G : SimpleGraph V} (r : V)
    (vs : List V) (C : Configuration V) (m : ℤ)
    (hp : PathArm G r vs) (hm : armMessage (vs.map C) = some m)
    (hpos : 0 < (C r : ℤ) + m)
    (hres : ((C r : ℤ) + m) % 3 = 1) :
    ∃ D : Configuration V,
      Reach G C D ∧ D r = 1 ∧ (∀ v ∈ vs, D v = 0) ∧
      (∀ v, v ∉ r :: vs → D v = C v) := by
  let a : ℤ := (C r : ℤ) + m
  have hdiv : 0 ≤ a / 3 := by dsimp [a]; omega
  let k : ℕ := (a / 3).toNat
  have hk : (k : ℤ) = a / 3 := by
    dsimp [k]
    exact Int.toNat_of_nonneg hdiv
  have hfinal : (C r : ℤ) + m = 1 + 3 * (k : ℤ) := by
    dsimp [a] at hk
    omega
  exact path_boundary_unit r vs C m k hp hm hfinal

end CycleStack
