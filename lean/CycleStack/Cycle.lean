import TreeStack.PebblingMove

namespace CycleStack

/-- The undirected simple cycle on vertices 0,...,N-1.
The distinctness conjunct also makes the definition valid at N=0,1,2. -/
def cycleGraph (N : ℕ) : SimpleGraph (Fin N) where
  Adj u v := u ≠ v ∧
    ((u.val + 1) % N = v.val ∨ (v.val + 1) % N = u.val)
  symm := by
    refine ⟨?_⟩
    intro u v h
    exact ⟨h.1.symm, h.2.symm⟩
  loopless := by
    refine ⟨?_⟩
    intro u h
    exact h.1 rfl

def evenCycle (n : ℕ) : SimpleGraph (Fin (2 * n)) := cycleGraph (2 * n)

def cycleThreshold (n : ℕ) : ℕ := 2 ^ (n + 1) - 1

/-- The actual upper-bound target. This definition makes no assertion that
the property has already been proved. -/
def EvenCycleUpper (n : ℕ) : Prop :=
  TreeStack.UniversalStackable (evenCycle n) (cycleThreshold n)

/-- The matching lower-bound target, as an explicit bad configuration. -/
def EvenCycleLowerObstruction (n : ℕ) : Prop :=
  ∃ C : TreeStack.Configuration (Fin (2 * n)),
    TreeStack.mass C + 1 = cycleThreshold n ∧
      ¬ TreeStack.Stackable (evenCycle n) C

theorem two_mul_add_two_le_power (n : ℕ) :
    2 * n + 2 ≤ 2 ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      omega

theorem card_lt_cycleThreshold (n : ℕ) :
    Fintype.card (Fin (2 * n)) < cycleThreshold n := by
  have h := two_mul_add_two_le_power n
  simp only [Fintype.card_fin, cycleThreshold]
  omega

theorem cycleGraph_adj_next {N : ℕ} (hN : 2 ≤ N) (u : Fin N) :
    (cycleGraph N).Adj u
      ⟨(u.val + 1) % N, Nat.mod_lt _ (by omega)⟩ := by
  constructor
  · intro he
    have hval : u.val = (u.val + 1) % N := congrArg Fin.val he
    by_cases hlt : u.val + 1 < N
    · rw [Nat.mod_eq_of_lt hlt] at hval
      omega
    · have heq : u.val + 1 = N := by omega
      simp [heq] at hval
      omega
  · exact Or.inl rfl

#print axioms two_mul_add_two_le_power
#print axioms card_lt_cycleThreshold
#print axioms cycleGraph_adj_next

end CycleStack
