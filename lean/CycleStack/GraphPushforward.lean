import TreeStack.PebblingMove
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace CycleStack

open TreeStack

variable {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]

/-- Aggregate a finite configuration over the fibers of a vertex map. -/
def pushforward (f : V → W) (C : Configuration V) : Configuration W :=
  fun w => ∑ v, if f v = w then C v else 0

omit [DecidableEq V] in
@[simp] theorem pushforward_zero (f : V → W) :
    pushforward f (fun _ => 0) = fun _ => 0 := by
  funext w
  simp [pushforward]

omit [DecidableEq V] in
theorem pushforward_add (f : V → W) (C D : Configuration V) :
    pushforward f (C + D) = pushforward f C + pushforward f D := by
  funext w
  simp only [pushforward, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases h : f v = w <;> simp [h]

omit [DecidableEq V] in
theorem le_pushforward (f : V → W) (C : Configuration V) (u : V) :
    C u ≤ pushforward f C (f u) := by
  have h := Finset.single_le_sum (f := fun v => if f v = f u then C v else 0)
    (fun v _ => Nat.zero_le _) (Finset.mem_univ u)
  simpa [pushforward] using h

omit [DecidableEq V] in
theorem pushforward_eq_zero_of_fiber (f : V → W) (C : Configuration V) (w : W)
    (hzero : ∀ v, f v = w → C v = 0) : pushforward f C w = 0 := by
  apply Finset.sum_eq_zero
  intro v hv
  by_cases h : f v = w <;> simp [h, hzero v]

/-- Replacing one source pile gives this subtraction-free fiber ledger. -/
theorem pushforward_update_balance (f : V → W) (C : Configuration V)
    (u : V) (a : ℕ) (w : W) :
    pushforward f (Function.update C u a) w + (if f u = w then C u else 0) =
      pushforward f C w + (if f u = w then a else 0) := by
  classical
  let g : V → ℕ := fun v => if f v = w then C v else 0
  have he : (fun v => if f v = w then Function.update C u a v else 0) =
      Function.update g u (if f u = w then a else 0) := by
    funext v
    by_cases h : v = u
    · subst v
      simp
    · simp [g, h]
  have hu := Finset.sum_erase_add Finset.univ g (Finset.mem_univ u)
  unfold pushforward
  rw [he, Finset.sum_update_of_mem (Finset.mem_univ u),
    Finset.sdiff_singleton_eq_erase]
  change (if f u = w then a else 0) + (∑ v ∈ Finset.univ.erase u, g v) +
    g u = (∑ v, g v) + (if f u = w then a else 0)
  omega

/-- A legal edge transfer commutes with aggregation when its images differ. -/
theorem pushforward_move (f : V → W) (C : Configuration V) {u v : V}
    (huv : f u ≠ f v) (hfund : 2 ≤ C u) :
    pushforward f (move C u v) = move (pushforward f C) (f u) (f v) := by
  have hsource : u ≠ v := by intro h; subst v; exact huv rfl
  let C₁ := Function.update C u (C u - 2)
  have hC₁v : C₁ v = C v := by simp [C₁, hsource.symm]
  funext w
  have h₁ := pushforward_update_balance f C u (C u - 2) w
  have h₂ := pushforward_update_balance f C₁ v (C v + 1) w
  rw [hC₁v] at h₂
  change pushforward f (move C u v) w + (if f v = w then C v else 0) =
    pushforward f C₁ w + (if f v = w then C v + 1 else 0) at h₂
  change pushforward f C₁ w + (if f u = w then C u else 0) =
    pushforward f C w + (if f u = w then C u - 2 else 0) at h₁
  by_cases hwv : w = f v
  · subst w
    simp only [huv, ite_false, ite_true, add_zero] at h₁ h₂
    have he : move (pushforward f C) (f u) (f v) (f v) =
        pushforward f C (f v) + 1 := by simp [move]
    rw [he]
    omega
  · by_cases hwu : w = f u
    · subst w
      simp only [huv.symm, ite_false, ite_true, add_zero] at h₁ h₂
      have he : move (pushforward f C) (f u) (f v) (f u) =
          pushforward f C (f u) - 2 := by simp [move, huv]
      rw [he]
      omega
    · simp only [Ne.symm hwv, Ne.symm hwu, ite_false, add_zero] at h₁ h₂
      have he : move (pushforward f C) (f u) (f v) w =
          pushforward f C w := by simp [move, hwv, hwu]
      rw [he]
      omega

theorem pebbleStep_pushforward {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G →g H) {C D : Configuration V} (h : PebbleStep G C D) :
    PebbleStep H (pushforward φ C) (pushforward φ D) := by
  rcases h with ⟨u, v, huv, hfund, rfl⟩
  have himage := φ.map_adj huv
  refine ⟨φ u, φ v, himage, hfund.trans (le_pushforward φ C u), ?_⟩
  exact pushforward_move φ C himage.ne hfund

theorem reach_pushforward {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G →g H) {C D : Configuration V} (h : Reach G C D) :
    Reach H (pushforward φ C) (pushforward φ D) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hCE hED ih => exact ih.tail (pebbleStep_pushforward φ hED)

omit [DecidableEq V] in
theorem stackedAt_pushforward (f : V → W) {C : Configuration V} {r : V}
    (h : StackedAt C r) : StackedAt (pushforward f C) (f r) := by
  constructor
  · exact h.1.trans_le (le_pushforward f C r)
  · intro w hw
    apply pushforward_eq_zero_of_fiber
    intro v hv
    by_cases hvr : v = r
    · subst v
      exact (hw hv.symm).elim
    · exact h.2 v hvr

theorem stackableAt_pushforward {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G →g H) {C : Configuration V} {r : V} (h : StackableAt G C r) :
    StackableAt H (pushforward φ C) (φ r) := by
  rcases h with ⟨D, hCD, hD⟩
  exact ⟨pushforward φ D, reach_pushforward φ hCD, stackedAt_pushforward φ hD⟩

theorem stackable_pushforward {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G →g H) {C : Configuration V} (h : Stackable G C) :
    Stackable H (pushforward φ C) := by
  rcases h with ⟨r, hr⟩
  exact ⟨φ r, stackableAt_pushforward φ hr⟩

omit [DecidableEq V] in
theorem mass_pushforward [Fintype W] (f : V → W) (C : Configuration V) :
    mass (pushforward f C) = mass C := by
  unfold mass pushforward
  rw [Finset.sum_comm]
  simp

/-- A single pile, useful for identifying explicit folded configurations. -/
def vertexPile (u : V) (k : ℕ) : Configuration V := fun v => if v = u then k else 0

theorem pushforward_vertexPile (f : V → W) (u : V) (k : ℕ) :
    pushforward f (vertexPile u k) = vertexPile (f u) k := by
  funext w
  unfold pushforward vertexPile
  rw [Finset.sum_eq_single u]
  · simp [eq_comm]
  · intro v hv hvu
    simp [hvu]
  · simp

end CycleStack

#print axioms CycleStack.pushforward_move
#print axioms CycleStack.reach_pushforward
#print axioms CycleStack.stackable_pushforward
#print axioms CycleStack.mass_pushforward
