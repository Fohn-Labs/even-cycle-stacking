import CycleStack.CyclePaths
import CycleStack.PathThreshold
import CycleStack.LocalClearing
import Mathlib.Data.List.Chain

namespace CycleStack

open TreeStack

variable {V : Type*} [DecidableEq V]

theorem stackableAt_of_reach {G : SimpleGraph V} {C D : Configuration V} {r : V}
    (hCD : Reach G C D) (hD : StackableAt G D r) : StackableAt G C r := by
  rcases hD with ⟨E, hDE, hE⟩
  exact ⟨E, hCD.trans hDE, hE⟩

theorem stackable_of_reach {G : SimpleGraph V} {C D : Configuration V}
    (hCD : Reach G C D) (hD : Stackable G D) : Stackable G C := by
  rcases hD with ⟨r, hr⟩
  exact ⟨r, stackableAt_of_reach hCD hr⟩

theorem mass_eq_list_sum_of_supported [Fintype V]
    (vs : List V) (C : Configuration V) (hn : vs.Nodup)
    (hzero : ∀ v, v ∉ vs → C v = 0) : mass C = (vs.map C).sum := by
  have h := mass_balance_on_list vs (fun _ => 0) C hn hzero
  simpa [mass] using h

theorem cycleIndex_add_ne {n : ℕ} [NeZero (2 * n)] (r : ℕ) {i j : ℕ}
    (hi : i < 2 * n) (hj : j < 2 * n) (hij : i ≠ j) :
    cycleIndex (n := n) (r + i) ≠ cycleIndex (r + j) := by
  intro he
  exact hij (cycleIndex_add_inj r hi hj he)

theorem clockwise_pathArm {n L : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (r : ℕ) (hL : L + 1 ≤ 2 * n) :
    PathArm (evenCycle n) (cycleIndex r) (clockwiseArm r L) :=
  PathArm.of_chain_nodup (clockwiseArm_isChain hn r L) (clockwiseArm_nodup r hL)

theorem counterclockwise_pathArm {n L : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (r : ℕ) (hL : L + 1 ≤ 2 * n) :
    PathArm (evenCycle n) (cycleIndex r) (counterclockwiseArm r L) :=
  PathArm.of_chain_nodup (counterclockwiseArm_isChain hn r hL)
    (counterclockwiseArm_nodup r hL)

theorem clockwiseArm_succ {n : ℕ} [NeZero (2 * n)] (r L : ℕ) :
    clockwiseArm (n := n) r (L + 1) =
      clockwiseArm r L ++ [cycleIndex (r + L + 1)] := by
  change clockwiseArc (r + 1) (L + 1) =
    clockwiseArc (r + 1) L ++ [cycleIndex (r + L + 1)]
  rw [clockwiseArc_append]
  have he : r + 1 + L = r + L + 1 := by omega
  simp [clockwiseArc, List.ofFn_succ, he]

theorem counterclockwiseArm_succ {n : ℕ} [NeZero (2 * n)] (r L : ℕ) :
    counterclockwiseArm (n := n) r (L + 1) =
      counterclockwiseArm r L ++ [cycleIndex (r + 2 * n - (L + 1))] := by
  unfold counterclockwiseArm
  rw [List.ofFn_succ_last]
  rfl

omit [DecidableEq V] in
theorem pathArm_of_reverse_chain {G : SimpleGraph V} {r t : V} {vs : List V}
    (hc : (r :: vs ++ [t]).IsChain G.Adj) (hn : (r :: vs ++ [t]).Nodup) :
    PathArm G t (vs.reverse ++ [r]) := by
  apply PathArm.of_chain_nodup
  · have hrev := List.isChain_reverse.mpr (hc.imp (fun {a b} hab => hab.symm))
    simpa [List.reverse_cons, List.reverse_append, List.append_assoc] using hrev
  · have hrev := List.nodup_reverse.mpr hn
    simpa only [List.reverse_cons, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.append_assoc, List.reverse_nil, List.nil_append] using hrev

theorem clockwise_push_pathArm {n L : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (r : ℕ) (hL : L + 2 ≤ 2 * n) :
    PathArm (evenCycle n) (cycleIndex (r + L + 1))
      ((clockwiseArm r L).reverse ++ [cycleIndex r]) := by
  have hc := clockwiseArm_isChain hn r (L + 1)
  have hd := clockwiseArm_nodup (n := n) r (show (L + 1) + 1 ≤ 2 * n by omega)
  rw [clockwiseArm_succ] at hc hd
  exact pathArm_of_reverse_chain hc hd

theorem counterclockwise_push_pathArm {n L : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (r : ℕ) (hL : L + 2 ≤ 2 * n) :
    PathArm (evenCycle n) (cycleIndex (r + 2 * n - (L + 1)))
      ((counterclockwiseArm r L).reverse ++ [cycleIndex r]) := by
  have hc := counterclockwiseArm_isChain hn r (show (L + 1) + 1 ≤ 2 * n by omega)
  have hd := counterclockwiseArm_nodup (n := n) r (show (L + 1) + 1 ≤ 2 * n by omega)
  rw [counterclockwiseArm_succ] at hc hd
  exact pathArm_of_reverse_chain hc hd

theorem clockwiseArm_mem_mono {n L M : ℕ} [NeZero (2 * n)] (r : ℕ)
    (hLM : L ≤ M) {v : Fin (2 * n)} (hv : v ∈ clockwiseArm r L) :
    v ∈ clockwiseArm r M := by
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hv
  apply List.mem_ofFn.mpr
  exact ⟨⟨i.val, by omega⟩, hi⟩

theorem counterclockwiseArm_mem_mono {n L M : ℕ} [NeZero (2 * n)] (r : ℕ)
    (hLM : L ≤ M) {v : Fin (2 * n)} (hv : v ∈ counterclockwiseArm r L) :
    v ∈ counterclockwiseArm r M := by
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hv
  apply List.mem_ofFn.mpr
  exact ⟨⟨i.val, by omega⟩, hi⟩

theorem antipode_mem_clockwiseArm {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (r : ℕ) : cycleIndex (r + n) ∈ clockwiseArm (n := n) r n := by
  apply List.mem_ofFn.mpr
  refine ⟨⟨n - 1, by omega⟩, ?_⟩
  change cycleIndex (r + 1 + (n - 1)) = cycleIndex (r + n)
  congr 1
  omega

theorem antipode_mem_counterclockwiseArm {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (r : ℕ) : cycleIndex (r + n) ∈ counterclockwiseArm (n := n) r n := by
  apply List.mem_ofFn.mpr
  refine ⟨⟨n - 1, by omega⟩, ?_⟩
  change cycleIndex (r + 2 * n - (n - 1 + 1)) = cycleIndex (r + n)
  congr 1
  omega

theorem clockwiseArc_root_cons {n k : ℕ} [NeZero (2 * n)]
    (r : ℕ) (hk : 0 < k) : clockwiseArc (n := n) r k =
      cycleIndex r :: clockwiseArm r (k - 1) := by
  have he : k - 1 + 1 = k := by omega
  simpa only [he, clockwiseArm] using clockwiseArc_succ (n := n) r (k - 1)

theorem counterclockwiseArc_root_cons {n k : ℕ} [NeZero (2 * n)]
    (r : ℕ) (hk : 0 < k) : counterclockwiseArc (n := n) r k =
      cycleIndex r :: counterclockwiseArm r (k - 1) := by
  have he : k - 1 + 1 = k := by omega
  simpa only [he] using counterclockwiseArc_succ (n := n) r (k - 1)

theorem mem_clockwiseArm_or_counterclockwiseArc {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (r : ℕ) (v : Fin (2 * n)) :
    v ∈ clockwiseArm r n ∨ v ∈ counterclockwiseArc r n := by
  have hcons := counterclockwiseArc_root_cons (n := n) r (show 0 < n by omega)
  rcases openArms_cover hn r v with hr | hc | ha | hw
  · right
    rw [hcons, hr]
    exact List.mem_cons_self
  · left
    exact clockwiseArm_mem_mono r (by omega) hc
  · left
    rw [ha]
    exact antipode_mem_clockwiseArm hn r
  · right
    rw [hcons]
    exact List.mem_cons_of_mem _ hw

theorem mem_counterclockwiseArm_or_clockwiseArc {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (r : ℕ) (v : Fin (2 * n)) :
    v ∈ counterclockwiseArm r n ∨ v ∈ clockwiseArc r n := by
  have hcons := clockwiseArc_root_cons (n := n) r (show 0 < n by omega)
  rcases openArms_cover hn r v with hr | hc | ha | hw
  · right
    rw [hcons, hr]
    exact List.mem_cons_self
  · right
    rw [hcons]
    exact List.mem_cons_of_mem _ hc
  · left
    rw [ha]
    exact antipode_mem_counterclockwiseArm hn r
  · left
    exact counterclockwiseArm_mem_mono r (by omega) hw

theorem zero_off_counterclockwiseArc_of_cleared_clockwise
    {n : ℕ} [NeZero (2 * n)] (hn : 2 ≤ n) (r : ℕ)
    (D : Configuration (Fin (2 * n)))
    (hclear : ∀ v ∈ clockwiseArm r n, D v = 0) :
    ∀ v, v ∉ counterclockwiseArc r n → D v = 0 := by
  intro v hv
  rcases mem_clockwiseArm_or_counterclockwiseArc hn r v with hc | hr
  · exact hclear v hc
  · exact (hv hr).elim

theorem zero_off_clockwiseArc_of_cleared_counterclockwise
    {n : ℕ} [NeZero (2 * n)] (hn : 2 ≤ n) (r : ℕ)
    (D : Configuration (Fin (2 * n)))
    (hclear : ∀ v ∈ counterclockwiseArm r n, D v = 0) :
    ∀ v, v ∉ clockwiseArc r n → D v = 0 := by
  intro v hv
  rcases mem_counterclockwiseArm_or_clockwiseArc hn r v with hc | hr
  · exact hclear v hc
  · exact (hv hr).elim

theorem mass_eq_counterclockwiseArc_of_cleared_clockwise
    {n : ℕ} [NeZero (2 * n)] (hn : 2 ≤ n) (r : ℕ)
    (D : Configuration (Fin (2 * n)))
    (hclear : ∀ v ∈ clockwiseArm r n, D v = 0) :
    mass D = ((counterclockwiseArc r n).map D).sum := by
  exact mass_eq_list_sum_of_supported _ D (counterclockwiseArc_nodup r (by omega))
    (zero_off_counterclockwiseArc_of_cleared_clockwise hn r D hclear)

theorem mass_eq_clockwiseArc_of_cleared_counterclockwise
    {n : ℕ} [NeZero (2 * n)] (hn : 2 ≤ n) (r : ℕ)
    (D : Configuration (Fin (2 * n)))
    (hclear : ∀ v ∈ counterclockwiseArm r n, D v = 0) :
    mass D = ((clockwiseArc r n).map D).sum := by
  exact mass_eq_list_sum_of_supported _ D (clockwiseArc_nodup r (by omega))
    (zero_off_clockwiseArc_of_cleared_counterclockwise hn r D hclear)

theorem stackable_of_clockwiseArc_mass {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (r : ℕ) (D : Configuration (Fin (2 * n)))
    (hzero : ∀ v, v ∉ clockwiseArc r n → D v = 0)
    (hmass : 2 ^ n - 1 ≤ mass D) : Stackable (evenCycle n) D := by
  have hd := clockwiseArc_nodup (n := n) r (show n ≤ 2 * n by omega)
  have hm := mass_eq_list_sum_of_supported _ D hd hzero
  have hne : clockwiseArc (n := n) r n ≠ [] := by
    intro he
    have hl := congrArg List.length he
    simp only [clockwiseArc_length, List.length_nil] at hl
    omega
  apply stackable_of_path_mass _ D hne hd (clockwiseArc_isChain hn r n) hzero
  rw [clockwiseArc_length, ← hm]
  exact hmass

theorem stackable_of_counterclockwiseArc_mass {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (r : ℕ) (D : Configuration (Fin (2 * n)))
    (hzero : ∀ v, v ∉ counterclockwiseArc r n → D v = 0)
    (hmass : 2 ^ n - 1 ≤ mass D) : Stackable (evenCycle n) D := by
  have hd := counterclockwiseArc_nodup (n := n) r (show n ≤ 2 * n by omega)
  have hm := mass_eq_list_sum_of_supported _ D hd hzero
  have hne : counterclockwiseArc (n := n) r n ≠ [] := by
    intro he
    have hl := congrArg List.length he
    simp only [counterclockwiseArc_length, List.length_nil] at hl
    omega
  apply stackable_of_path_mass _ D hne hd
    (counterclockwiseArc_isChain hn r (by omega)) hzero
  rw [counterclockwiseArc_length, ← hm]
  exact hmass

theorem stackable_of_cleared_clockwise {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (r : ℕ) (D : Configuration (Fin (2 * n)))
    (hclear : ∀ v ∈ clockwiseArm r n, D v = 0)
    (hmass : 2 ^ n - 1 ≤ mass D) : Stackable (evenCycle n) D := by
  exact stackable_of_counterclockwiseArc_mass hn r D
    (zero_off_counterclockwiseArc_of_cleared_clockwise hn r D hclear) hmass

theorem stackable_of_cleared_counterclockwise {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (r : ℕ) (D : Configuration (Fin (2 * n)))
    (hclear : ∀ v ∈ counterclockwiseArm r n, D v = 0)
    (hmass : 2 ^ n - 1 ≤ mass D) : Stackable (evenCycle n) D := by
  exact stackable_of_clockwiseArc_mass hn r D
    (zero_off_clockwiseArc_of_cleared_counterclockwise hn r D hclear) hmass

theorem stackable_of_reach_cleared_clockwise {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (r : ℕ) {C D : Configuration (Fin (2 * n))}
    (hCD : Reach (evenCycle n) C D)
    (hclear : ∀ v ∈ clockwiseArm r n, D v = 0)
    (hmass : 2 ^ n - 1 ≤ mass D) : Stackable (evenCycle n) C := by
  exact stackable_of_reach hCD (stackable_of_cleared_clockwise hn r D hclear hmass)

theorem stackable_of_reach_cleared_counterclockwise {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (r : ℕ) {C D : Configuration (Fin (2 * n))}
    (hCD : Reach (evenCycle n) C D)
    (hclear : ∀ v ∈ counterclockwiseArm r n, D v = 0)
    (hmass : 2 ^ n - 1 ≤ mass D) : Stackable (evenCycle n) C := by
  exact stackable_of_reach hCD (stackable_of_cleared_counterclockwise hn r D hclear hmass)

end CycleStack

#print axioms CycleStack.clockwise_push_pathArm
#print axioms CycleStack.counterclockwise_push_pathArm
#print axioms CycleStack.stackable_of_cleared_clockwise
#print axioms CycleStack.stackable_of_cleared_counterclockwise
#print axioms CycleStack.stackable_of_reach_cleared_clockwise
#print axioms CycleStack.stackable_of_reach_cleared_counterclockwise
