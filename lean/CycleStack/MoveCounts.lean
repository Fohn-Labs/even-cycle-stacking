import TreeStack.PebblingMove

namespace CycleStack

open TreeStack

/-- Directed move counts extracted from an actual legal sequence. Besides
the integer balance equations, the ledger records the last-pebble invariant:
an initially occupied set cannot become empty without an outgoing move. -/
structure MoveLedger {V : Type*} [Fintype V] (G : SimpleGraph V)
    (C D : Configuration V) where
  count : V → V → ℕ
  supported : ∀ {u v}, 0 < count u v → G.Adj u v
  balance : ∀ v, (D v : ℤ) = (C v : ℤ) + ((∑ u, count u v : ℕ) : ℤ) -
    2 * ((∑ w, count v w : ℕ) : ℤ)
  persists : ∀ S : Set V, (∃ v ∈ S, 0 < C v) →
    (∀ u ∈ S, ∀ v ∉ S, count u v = 0) → ∃ v ∈ S, 0 < D v

variable {V : Type*} [Fintype V]

/-- If a set is emptied by the sequence, some recorded move leaves it. -/
theorem MoveLedger.outward_positive {G : SimpleGraph V} {C D : Configuration V}
    (m : MoveLedger G C D) (S : Set V) (hOcc : ∃ v ∈ S, 0 < C v)
    (hZero : ∀ v ∈ S, D v = 0) :
    ∃ u v, u ∈ S ∧ v ∉ S ∧ 0 < m.count u v := by
  classical
  by_contra hOut
  have hClosed : ∀ u ∈ S, ∀ v ∉ S, m.count u v = 0 := by
    intro u hu v hv
    by_contra hn
    have hp : 0 < m.count u v := by omega
    exact hOut ⟨u, v, hu, hv, hp⟩
  obtain ⟨v, hv, hpos⟩ := m.persists S hOcc hClosed
  rw [hZero v hv] at hpos
  omega

variable [DecidableEq V]

private def addMoveCount (f : V → V → ℕ) (u v : V) : V → V → ℕ :=
  fun a b => f a b + if a = u ∧ b = v then 1 else 0

private theorem addMoveCount_incoming (f : V → V → ℕ) (u v w : V) :
    (∑ a, addMoveCount f u v a w) = (∑ a, f a w) + if w = v then 1 else 0 := by
  simp only [addMoveCount, Finset.sum_add_distrib]
  congr 1
  by_cases hw : w = v
  · subst w
    simp
  · simp [hw]

private theorem addMoveCount_outgoing (f : V → V → ℕ) (u v w : V) :
    (∑ b, addMoveCount f u v w b) = (∑ b, f w b) + if w = u then 1 else 0 := by
  simp only [addMoveCount, Finset.sum_add_distrib]
  congr 1
  by_cases hw : w = u
  · subst w
    simp
  · simp [hw]

omit [Fintype V] in
private theorem move_balance_at (C : Configuration V) {u v : V}
    (huv : u ≠ v) (hLegal : 2 ≤ C u) (w : V) :
    (move C u v w : ℤ) = (C w : ℤ) + (if w = v then 1 else 0) -
      2 * (if w = u then 1 else 0) := by
  by_cases hwu : w = u
  · subst w
    simp [move, huv]
    omega
  · by_cases hwv : w = v
    · subst w
      simp [move, huv.symm]
    · simp [move, hwu, hwv]

omit [Fintype V] in
private theorem occupied_after_move (C : Configuration V) (u v : V) (S : Set V)
    (hOcc : ∃ w ∈ S, 0 < C w) (hStay : u ∈ S → v ∈ S) :
    ∃ w ∈ S, 0 < move C u v w := by
  classical
  by_cases hu : u ∈ S
  · refine ⟨v, hStay hu, ?_⟩
    simp [move]
  · obtain ⟨w, hw, hpos⟩ := hOcc
    have hwu : w ≠ u := by intro h; subst w; exact hu hw
    by_cases hwv : w = v
    · subst w
      refine ⟨v, hw, ?_⟩
      simp [move]
    · refine ⟨w, hw, ?_⟩
      simpa [move, hwu, hwv] using hpos

/-- Append one actual legal move to a ledger, preserving all invariants. -/
def MoveLedger.extend {G : SimpleGraph V} {C D : Configuration V}
    (m : MoveLedger G C D) {u v : V} (huv : G.Adj u v) (hLegal : 2 ≤ D u) :
    MoveLedger G C (move D u v) := by
  classical
  refine {
    count := addMoveCount m.count u v
    supported := ?_
    balance := ?_
    persists := ?_
  }
  · intro a b hpos
    by_cases hold : 0 < m.count a b
    · exact m.supported hold
    · have hz : m.count a b = 0 := by omega
      have he : a = u ∧ b = v := by
        by_contra hn
        simp [addMoveCount, hz, hn] at hpos
      rcases he with ⟨rfl, rfl⟩
      exact huv
  · intro w
    rw [move_balance_at D huv.ne hLegal w, m.balance w,
      addMoveCount_incoming, addMoveCount_outgoing]
    by_cases hwu : w = u
    · by_cases hwv : w = v
      · exact (huv.ne (hwu.symm.trans hwv)).elim
      · simp [hwu, huv.ne]
        omega
    · by_cases hwv : w = v
      · subst w
        simp [huv.ne.symm]
        omega
      · simp [hwu, hwv]
  · intro S hOcc hClosed
    have hPrefixClosed : ∀ a ∈ S, ∀ b ∉ S, m.count a b = 0 := by
      intro a ha b hb
      have h := hClosed a ha b hb
      change addMoveCount m.count u v a b = 0 at h
      simp only [addMoveCount] at h
      omega
    have hStay : u ∈ S → v ∈ S := by
      intro hu
      by_contra hv
      have h := hClosed u hu v hv
      simp [addMoveCount] at h
    exact occupied_after_move D u v S (m.persists S hOcc hPrefixClosed) hStay

/-- Every legal finite reachability proof has a supported, balanced move
ledger satisfying the last-pebble invariant, including the reflexive case. -/
theorem moveLedger_of_reach {G : SimpleGraph V} {C D : Configuration V}
    (hCD : Reach G C D) : Nonempty (MoveLedger G C D) := by
  induction hCD with
  | refl =>
      refine ⟨{
        count := fun _ _ => 0
        supported := ?_
        balance := ?_
        persists := ?_
      }⟩
      · intro u v h
        omega
      · intro v
        simp
      · intro S hOcc hClosed
        exact hOcc
  | tail hCE hED ih =>
      obtain ⟨m⟩ := ih
      obtain ⟨u, v, huv, hLegal, rfl⟩ := hED
      exact ⟨m.extend huv hLegal⟩

end CycleStack
