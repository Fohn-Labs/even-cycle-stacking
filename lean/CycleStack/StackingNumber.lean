import CycleStack.Upper
import Mathlib.Order.Lattice.Nat

namespace CycleStack

open TreeStack

/-- Every vertex has a neighbour. Connectedness is unnecessary for the
exact-size propagation argument below. This condition is vacuous on an
empty vertex type and fails on a singleton simple graph. -/
def NoIsolatedVertices {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ v, ∃ w, G.Adj v w

/-- The genuine least universal exact-size threshold, with the source
convention that admissible thresholds begin at two. -/
def IsStackingNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : ℕ) : Prop :=
  2 ≤ S ∧ UniversalStackable G S ∧
    ∀ t : ℕ, 2 ≤ t → UniversalStackable G t → S ≤ t

/-- The least universal exact size at least two. The natural infimum is
zero if no such size exists; the equality theorems below establish an
actual admissible minimum, so that convention is never used for cycles. -/
noncomputable def stackingNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  sInf {t : ℕ | 2 ≤ t ∧ UniversalStackable G t}

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem IsStackingNumber.stackingNumber_eq {G : SimpleGraph V} {S : ℕ}
    (hS : IsStackingNumber G S) : stackingNumber G = S := by
  have hmem : S ∈ {t : ℕ | 2 ≤ t ∧ UniversalStackable G t} :=
    ⟨hS.1, hS.2.1⟩
  apply le_antisymm
  · exact Nat.sInf_le hmem
  · have hmin := Nat.sInf_mem ⟨S, hmem⟩
    exact hS.2.2 _ hmin.1 hmin.2

/-- Universality at an exact size at least two propagates one step. The
vertex-count obstruction supplies a legal source, and its neighbour supplies
one move reducing the mass to the already universal size. The lower bound
two is essential; universality at size one alone would not suffice. -/
theorem universal_stackable_succ_of_no_isolated {G : SimpleGraph V} {t : ℕ}
    (hNo : NoIsolatedVertices G) (hU : UniversalStackable G t) (ht : 2 ≤ t) :
    UniversalStackable G (t + 1) := by
  intro C hMass
  have hCard : Fintype.card V < t := universal_stackable_gt_card hU ht
  have hBig : Fintype.card V < mass C := by omega
  obtain ⟨u, hu⟩ := exists_two_le_of_card_lt_mass C hBig
  obtain ⟨v, huv⟩ := hNo u
  let D : Configuration V := move C u v
  have hStep : PebbleStep G C D := ⟨u, v, huv, hu, rfl⟩
  have hDrop : mass D + 1 = mass C := mass_move_add_one C huv.ne hu
  have hD : mass D = t := by omega
  exact stackable_of_step hStep (hU D hD)

/-- Exact-size universality is upward closed above any universal size at
least two, without assuming individual configurations are monotone. -/
theorem universal_stackable_mono_of_no_isolated {G : SimpleGraph V} {t u : ℕ}
    (hNo : NoIsolatedVertices G) (hU : UniversalStackable G t) (ht : 2 ≤ t)
    (htu : t ≤ u) : UniversalStackable G u := by
  have hAll : ∀ k : ℕ, UniversalStackable G (t + k) := by
    intro k
    induction k with
    | zero => simpa using hU
    | succ k ih =>
        simpa only [Nat.add_assoc] using
          universal_stackable_succ_of_no_isolated hNo ih (by omega)
  have he : t + (u - t) = u := by omega
  simpa only [he] using hAll (u - t)

theorem IsStackingNumber.unique {G : SimpleGraph V} {S T : ℕ}
    (hS : IsStackingNumber G S) (hT : IsStackingNumber G T) : S = T := by
  exact le_antisymm (hS.2.2 T hT.1 hT.2.1) (hT.2.2 S hS.1 hS.2.1)

/-- This base case needs no lower obstruction. In particular it permits
the empty and singleton conventions without inventing a bad unit pile. -/
theorem isStackingNumber_two_of_universal {G : SimpleGraph V}
    (hU : UniversalStackable G 2) : IsStackingNumber G 2 :=
  ⟨by decide, hU, fun _ ht _ => ht⟩

/-- A genuine bad configuration immediately below a universal exact size
proves minimality. A hypothetical smaller universal size would propagate to
the bad configuration's mass, giving a contradiction. -/
theorem isStackingNumber_of_universal_and_obstruction {G : SimpleGraph V} {S : ℕ}
    (hNo : NoIsolatedVertices G) (hS : 2 ≤ S) (hU : UniversalStackable G S)
    (hBad : ∃ C : Configuration V, mass C + 1 = S ∧ ¬ Stackable G C) :
    IsStackingNumber G S := by
  refine ⟨hS, hU, ?_⟩
  intro t ht hUt
  by_contra hNot
  obtain ⟨C, hMass, hC⟩ := hBad
  have htC : t ≤ mass C := by omega
  have hUniversal := universal_stackable_mono_of_no_isolated hNo hUt ht htC
  exact hC (hUniversal C rfl)

theorem IsStackingNumber.universal_ge {G : SimpleGraph V} {S u : ℕ}
    (hS : IsStackingNumber G S) (hNo : NoIsolatedVertices G) (hu : S ≤ u) :
    UniversalStackable G u :=
  universal_stackable_mono_of_no_isolated hNo hS.2.1 hS.1 hu

theorem IsStackingNumber.not_universal_below {G : SimpleGraph V} {S t : ℕ}
    (hS : IsStackingNumber G S) (ht : 2 ≤ t) (hlt : t < S) :
    ¬ UniversalStackable G t := by
  intro hU
  have hle := hS.2.2 t ht hU
  omega

/-- The cycle has no isolated vertices as soon as it has at least two
vertices; its explicit next-vertex edge suffices. -/
theorem cycleGraph_no_isolated {N : ℕ} (hN : 2 ≤ N) :
    NoIsolatedVertices (cycleGraph N) := by
  intro u
  exact ⟨⟨(u.val + 1) % N, Nat.mod_lt _ (by omega)⟩, cycleGraph_adj_next hN u⟩

theorem evenCycle_no_isolated {n : ℕ} (hn : 1 ≤ n) :
    NoIsolatedVertices (evenCycle n) :=
  cycleGraph_no_isolated (by omega)

/-- The universal cycle threshold is an admissible size under the source
convention. The stronger vertex-count bound has already been proved. -/
theorem two_le_cycleThreshold {n : ℕ} (hn : 1 ≤ n) : 2 ≤ cycleThreshold n := by
  have hCard := card_lt_cycleThreshold n
  simp only [Fintype.card_fin] at hCard
  omega

/-- The all-n upper certificate also applies to every larger total mass. -/
theorem even_cycle_stackable_above {n : ℕ} (hn : 2 ≤ n)
    (C : Configuration (Fin (2 * n))) (hMass : cycleThreshold n ≤ mass C) :
    Stackable (evenCycle n) C := by
  have hU : UniversalStackable (evenCycle n) (cycleThreshold n) := even_cycle_upper hn
  have hAbove := universal_stackable_mono_of_no_isolated
    (evenCycle_no_isolated (by omega)) hU (two_le_cycleThreshold (by omega)) hMass
  exact hAbove C rfl

/-- Equality with the least stacking threshold, conditional only on an
actual lower obstruction. No published path lower bound is assumed here. -/
theorem even_cycle_isStackingNumber_of_obstruction {n : ℕ} (hn : 2 ≤ n)
    (hLower : EvenCycleLowerObstruction n) :
    IsStackingNumber (evenCycle n) (cycleThreshold n) := by
  exact isStackingNumber_of_universal_and_obstruction
    (evenCycle_no_isolated (by omega)) (two_le_cycleThreshold (by omega))
    (even_cycle_upper hn) hLower

theorem even_cycle_stackingNumber_eq_of_obstruction {n : ℕ} (hn : 2 ≤ n)
    (hLower : EvenCycleLowerObstruction n) :
    stackingNumber (evenCycle n) = 2 ^ (n + 1) - 1 :=
  (even_cycle_isStackingNumber_of_obstruction hn hLower).stackingNumber_eq

#print axioms IsStackingNumber.stackingNumber_eq
#print axioms even_cycle_stackingNumber_eq_of_obstruction

end CycleStack
