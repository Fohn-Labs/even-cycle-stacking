import TreeStack.PebblingMove
import TreeStack.Transfer

namespace CycleStack

open TreeStack

variable {V : Type*} [DecidableEq V]

/-- A legal move in a subgraph is legal in the ambient graph. -/
theorem pebbleStep_mono {G H : SimpleGraph V} (hGH : G ≤ H)
    {C D : Configuration V} (h : PebbleStep G C D) :
    PebbleStep H C D := by
  rcases h with ⟨u, v, huv, hu, rfl⟩
  exact ⟨u, v, hGH huv, hu, rfl⟩

/-- Edge inclusion transports an entire legal move sequence. -/
theorem reach_mono {G H : SimpleGraph V} (hGH : G ≤ H)
    {C D : Configuration V} (h : Reach G C D) : Reach H C D := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hCE hED ih =>
      exact Relation.ReflTransGen.tail ih (pebbleStep_mono hGH hED)

theorem stackableAt_mono {G H : SimpleGraph V} (hGH : G ≤ H)
    {C : Configuration V} {r : V} (h : StackableAt G C r) :
    StackableAt H C r := by
  rcases h with ⟨D, hCD, hD⟩
  exact ⟨D, reach_mono hGH hCD, hD⟩

theorem stackable_mono {G H : SimpleGraph V} (hGH : G ≤ H)
    {C : Configuration V} (h : Stackable G C) : Stackable H C := by
  rcases h with ⟨r, hr⟩
  exact ⟨r, stackableAt_mono hGH hr⟩

/-- Carrying an inactive configuration through a legal move preserves it. -/
theorem move_add (C E : Configuration V) {u v : V}
    (huv : u ≠ v) (hu : 2 ≤ C u) :
    move (C + E) u v = move C u v + E := by
  funext w
  by_cases hwv : w = v
  · subst w
    simp [move, Pi.add_apply]
    omega
  · by_cases hwu : w = u
    · subst w
      simp [move, huv, Pi.add_apply]
      omega
    · simp [move, hwu, hwv, Pi.add_apply]

theorem pebbleStep_add {G : SimpleGraph V} {C D : Configuration V}
    (h : PebbleStep G C D) (E : Configuration V) :
    PebbleStep G (C + E) (D + E) := by
  rcases h with ⟨u, v, huv, hu, rfl⟩
  refine ⟨u, v, huv, ?_, ?_⟩
  · change 2 ≤ C u + E u
    omega
  · exact (move_add C E huv.ne hu).symm

/-- A legal sequence can use only its active pebbles and preserve all extras. -/
theorem reach_add {G : SimpleGraph V} {C D : Configuration V}
    (h : Reach G C D) (E : Configuration V) :
    Reach G (C + E) (D + E) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hCE hED ih =>
      exact Relation.ReflTransGen.tail ih (pebbleStep_add hED E)

/-- Batch `n` moves along one edge, with exact endpoint values. -/
theorem reach_repeat_move {G : SimpleGraph V} {u v : V}
    (huv : G.Adj u v) (C : Configuration V) (n : ℕ)
    (hTotal : 2 * n ≤ C u) :
    ∃ D : Configuration V,
      Reach G C D ∧
      D u = C u - 2 * n ∧ D v = C v + n ∧
      (∀ w, w ≠ u → w ≠ v → D w = C w) := by
  induction n generalizing C with
  | zero =>
      refine ⟨C, Relation.ReflTransGen.refl, ?_, ?_, ?_⟩
      · simp
      · simp
      · intro w hwu hwv
        rfl
  | succ n ih =>
      have hLegal : 2 ≤ C u := by omega
      let E : Configuration V := move C u v
      have hStep : PebbleStep G C E := ⟨u, v, huv, hLegal, rfl⟩
      have hEu : E u = C u - 2 := by simp [E, move, huv.ne]
      have hEv : E v = C v + 1 := by simp [E, move]
      have hRemain : 2 * n ≤ E u := by rw [hEu]; omega
      obtain ⟨D, hED, hDu, hDv, hOther⟩ := ih E hRemain
      refine ⟨D, Relation.ReflTransGen.head hStep hED, ?_, ?_, ?_⟩
      · rw [hDu, hEu]
        omega
      · rw [hDv, hEv]
        omega
      · intro w hwu hwv
        rw [hOther w hwu hwv]
        simp [E, move, hwu, hwv]

/-- Three surplus pebbles can be consumed while restoring the neighbour. -/
theorem reach_burn_three {G : SimpleGraph V} {r v : V}
    (hrv : G.Adj r v) (C : Configuration V) (hCr : 4 ≤ C r) :
    ∃ D : Configuration V,
      Reach G C D ∧ D r = C r - 3 ∧ D v = C v ∧
      (∀ w, w ≠ r → w ≠ v → D w = C w) := by
  obtain ⟨E, hCE, hEr, hEv, hOther⟩ :=
    reach_repeat_move hrv C 2 (by omega)
  have hLegal : 2 ≤ E v := by omega
  let D := move E v r
  have hStep : PebbleStep G E D := ⟨v, r, hrv.symm, hLegal, rfl⟩
  refine ⟨D, Relation.ReflTransGen.tail hCE hStep, ?_, ?_, ?_⟩
  · simp only [D, move, Function.update_self]
    rw [hEr]
    omega
  · simp [D, move, hrv.ne.symm, hEv]
  · intro w hwr hwv
    simp [D, move, hwr, hwv, hOther w hwr hwv]

/-- Burn any prescribed multiple of three while preserving a positive base
pile and every pebble at other vertices. -/
theorem reach_burn_triples {G : SimpleGraph V} {r v : V}
    (hrv : G.Adj r v) (q k : ℕ) (hq : 1 ≤ q)
    (C : Configuration V) (hCr : C r = q + 3 * k) :
    ∃ D : Configuration V,
      Reach G C D ∧ D r = q ∧ D v = C v ∧
      (∀ w, w ≠ r → w ≠ v → D w = C w) := by
  induction k generalizing C with
  | zero =>
      refine ⟨C, Relation.ReflTransGen.refl, ?_, rfl, ?_⟩
      · simpa using hCr
      · intro w hwr hwv
        rfl
  | succ k ih =>
      obtain ⟨E, hCE, hEr, hEv, hOther⟩ :=
        reach_burn_three hrv C (by omega)
      have hEr' : E r = q + 3 * k := by omega
      obtain ⟨D, hED, hDr, hDv, hOther'⟩ := ih E hEr'
      refine ⟨D, hCE.trans hED, hDr, ?_, ?_⟩
      · rw [hDv, hEv]
      · intro w hwr hwv
        rw [hOther' w hwr hwv, hOther w hwr hwv]

/-- Clear a pile of at least two into its neighbour, attaining the transfer
`F` exactly whenever the resulting boundary pile is positive. -/
theorem reach_transfer_ge_two {G : SimpleGraph V} {u r : V}
    (hur : G.Adj u r) (C : Configuration V) (hCu : 2 ≤ C u)
    (hpos : 0 < (C r : ℤ) + F (C u : ℤ)) :
    ∃ D : Configuration V,
      Reach G C D ∧ D u = 0 ∧
      (D r : ℤ) = (C r : ℤ) + F (C u : ℤ) ∧
      (∀ w, w ≠ u → w ≠ r → D w = C w) := by
  let k : ℕ := C u / 2
  have hk : 1 ≤ k := by dsimp [k]; omega
  by_cases he : C u % 2 = 0
  · have hCuEq : C u = 2 * k := by dsimp [k]; omega
    have hF : F (C u : ℤ) = (k : ℤ) := by
      rw [hCuEq]
      unfold F
      push_cast
      split_ifs <;> omega
    obtain ⟨D, hCD, hDu, hDr, hOther⟩ :=
      reach_repeat_move hur C k (by omega)
    refine ⟨D, hCD, ?_, ?_, hOther⟩
    · omega
    · rw [hDr, hF]
      push_cast
      rfl
  · have hCuEq : C u = 2 * k + 1 := by dsimp [k]; omega
    have hF : F (C u : ℤ) = (k : ℤ) - 1 := by
      rw [hCuEq]
      unfold F
      push_cast
      split_ifs <;> omega
    obtain ⟨E, hCE, hEu, hEr, hOther⟩ :=
      reach_repeat_move hur C k (by omega)
    have hEuOne : E u = 1 := by omega
    have hLegalR : 2 ≤ E r := by
      rw [hF] at hpos
      rw [hEr]
      omega
    let J := move E r u
    have hEJ : PebbleStep G E J := ⟨r, u, hur.symm, hLegalR, rfl⟩
    have hJu : J u = 2 := by simp [J, move, hEuOne]
    have hJr : J r = E r - 2 := by simp [J, move, hur.ne.symm]
    let D := move J u r
    have hJD : PebbleStep G J D := ⟨u, r, hur, by omega, rfl⟩
    refine ⟨D, Relation.ReflTransGen.tail
      (Relation.ReflTransGen.tail hCE hEJ) hJD, ?_, ?_, ?_⟩
    · simp [D, move, hur.ne, hJu]
    · have hDr : D r = E r - 2 + 1 := by simp [D, move, hJr]
      rw [hDr, hEr, hF]
      omega
    · intro w hwu hwr
      simp [D, J, move, hwu, hwr, hOther w hwu hwr]

end CycleStack
