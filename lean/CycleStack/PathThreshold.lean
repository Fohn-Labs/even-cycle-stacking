import CycleStack.PathConstruction

namespace CycleStack

open TreeStack

/-- An occupied endpoint has positive score above the path mass threshold.
This follows directly from the negative-message mass bound. -/
theorem path_score_pos_of_mass {q : ℕ} {xs : List ℕ} {m : ℤ}
    (hq : 0 < q) (hm : armMessage xs = some m)
    (hmass : (2 : ℤ) ^ (xs.length + 1) - 1 ≤ (q : ℤ) + (xs.sum : ℤ)) :
    0 < (q : ℤ) + m := by
  by_contra h
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have hmneg : m < 0 := by omega
  have hbound := arm_negative_mass hm hmneg
  omega

variable {V : Type*} [DecidableEq V]

/-- The occupied-endpoint version of the path upper bound, with the
mass written in integers to match the arm arithmetic. -/
theorem stackableAt_of_occupied_path_mass {G : SimpleGraph V} (r : V)
    (vs : List V) (C : Configuration V)
    (hp : PathArm G r vs) (hq : 0 < C r)
    (hzero : ∀ v, v ∉ r :: vs → C v = 0)
    (hmass : (2 : ℤ) ^ (vs.length + 1) - 1 ≤
      (C r : ℤ) + ((vs.map C).sum : ℤ)) : StackableAt G C r := by
  have hpos : ∀ m : ℤ, armMessage (vs.map C) = some m →
      0 < (C r : ℤ) + m := by
    intro m hm
    apply path_score_pos_of_mass hq hm
    simpa only [List.length_map] using hmass
  obtain ⟨D, hCD, hDr, hDz, hOther⟩ := path_boundary_clear r vs C hp hpos
  refine ⟨D, hCD, ?_, ?_⟩
  · cases ht : armMessage (vs.map C) with
    | none =>
      have hr : (D r : ℤ) = (C r : ℤ) := by simpa [ht] using hDr
      omega
    | some m =>
      have hs := hpos m ht
      have hr : (D r : ℤ) = (C r : ℤ) + m := by simpa [ht] using hDr
      omega
  · intro v hvr
    by_cases hv : v ∈ vs
    · exact hDz v hv
    · have hnot : v ∉ r :: vs := by simp [hvr, hv]
      rw [hOther v hnot]
      exact hzero v hnot

/-- Every configuration supported on an embedded nonempty simple path
with at least `2^length - 1` pebbles is stackable in the ambient graph.
The vertex type need not be finite, and extra ambient edges are allowed. -/
theorem stackable_of_path_mass {G : SimpleGraph V} (vs : List V)
    (C : Configuration V) (hne : vs ≠ []) (hn : vs.Nodup)
    (hc : vs.IsChain G.Adj) (hzero : ∀ v, v ∉ vs → C v = 0)
    (hmass : 2 ^ vs.length - 1 ≤ (vs.map C).sum) : Stackable G C := by
  revert hne hn hc hzero hmass
  induction vs with
  | nil =>
    intro hne
    exact (hne rfl).elim
  | cons r vs ih =>
    intro hne hn hc hzero hmass
    by_cases hz : C r = 0
    · cases vs with
      | nil => simp [hz] at hmass
      | cons u us =>
        have hnTail : (u :: us).Nodup := (List.nodup_cons.mp hn).2
        have hcTail : (u :: us).IsChain G.Adj := (List.isChain_cons_cons.mp hc).2
        have hzTail : ∀ v, v ∉ u :: us → C v = 0 := by
          intro v hv
          by_cases hvr : v = r
          · subst v
            exact hz
          · exact hzero v (by simp [hvr, hv])
        have hfull : 2 ^ ((u :: us).length + 1) - 1 ≤ ((u :: us).map C).sum := by
          simpa only [List.length_cons, List.map_cons, List.sum_cons, hz, zero_add]
            using hmass
        have htailmass : 2 ^ (u :: us).length - 1 ≤ ((u :: us).map C).sum := by
          rw [pow_succ] at hfull
          omega
        exact ih (by simp) hnTail hcTail hzTail htailmass
    · have hq : 0 < C r := by omega
      have htotal : 2 ^ (vs.length + 1) - 1 ≤ C r + (vs.map C).sum := by
        simpa only [List.length_cons, List.map_cons, List.sum_cons] using hmass
      have hp : (0 : ℕ) < 2 ^ (vs.length + 1) := pow_pos (by norm_num) _
      have htotal' : 2 ^ (vs.length + 1) ≤ C r + (vs.map C).sum + 1 := by omega
      have hcast : (2 : ℤ) ^ (vs.length + 1) ≤
          (C r : ℤ) + ((vs.map C).sum : ℤ) + 1 := by exact_mod_cast htotal'
      refine ⟨r, stackableAt_of_occupied_path_mass r vs C
        (PathArm.of_chain_nodup hc hn) hq hzero ?_⟩
      omega

end CycleStack
