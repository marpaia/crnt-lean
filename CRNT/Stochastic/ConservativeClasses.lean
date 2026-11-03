import CRNT.Stochastic.IntegerLattice
import CRNT.Flux.PSemiflow
import Mathlib.Data.Fintype.BigOperators

/-!
# Conservative stochastic communication classes

A positive integer P-semiflow makes every stochastic communication class finite:
the conserved weighted molecule count gives a coordinatewise bound.  This is the
integer-state counterpart of bounded deterministic stoichiometric compatibility classes.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Integer P-invariant: an integer species weight annihilating every integer reaction move. -/
def IsIntegerPInvariant (N : Network S) (w : S → ℕ) : Prop :=
  ∀ r : N.R, ∑ s : S, (w s : ℤ) * N.integerReactionVector r s = 0

/-- Strictly positive integer P-semiflow. -/
def IsStrictIntegerPSemiflow (N : Network S) (w : S → ℕ) : Prop :=
  N.IsIntegerPInvariant w ∧ ∀ s, 0 < w s

/-- Conserved integer molecule-weight total. -/
def countWeightedTotal (w : S → ℕ) (n : S → ℕ) : ℕ :=
  ∑ s : S, w s * n s

/-- One firing preserves every integer P-invariant. -/
theorem countWeightedTotal_fireCount_eq (N : Network S)
    {w : S → ℕ} (hw : N.IsIntegerPInvariant w)
    {n : S → ℕ} {r : N.R} (hen : N.Enabled n r) :
    countWeightedTotal w (N.fireCount n r) = countWeightedTotal w n := by
  -- The statement is over `ℕ`, but the invariance hypothesis is over `ℤ`; prove the cast
  -- equality and then strip the cast.
  have hcast : ((countWeightedTotal w (N.fireCount n r) : ℕ) : ℤ)
      = ((countWeightedTotal w n : ℕ) : ℤ) := by
    simp only [countWeightedTotal, Nat.cast_sum, Nat.cast_mul, fireCount, dif_pos hen]
    have hsub : ∀ s : S, ((n s - (N.reaction r).source s + (N.reaction r).target s : ℕ) : ℤ)
        = (n s : ℤ) + N.integerReactionVector r s := by
      intro s
      have h := hen s
      rw [Nat.cast_add, Nat.cast_sub h]
      simp only [integerReactionVector]
      ring
    rw [Finset.sum_congr rfl fun s _ => by rw [hsub s]]
    simp only [mul_add, Finset.sum_add_distrib, hw r, add_zero]
  exact Nat.cast_injective hcast

/-- Reachability preserves an integer P-invariant. -/
theorem countWeightedTotal_eq_of_reachable (N : Network S)
    {w : S → ℕ} (hw : N.IsIntegerPInvariant w)
    {n m : S → ℕ} (h : N.CountReachable n m) :
    countWeightedTotal w m = countWeightedTotal w n := by
  induction h with
  | refl => rfl
  | tail hreach hstep ih =>
      rcases hstep with ⟨r, hen, rfl⟩
      rw [N.countWeightedTotal_fireCount_eq hw hen, ih]

/-- A positive integer P-semiflow gives an explicit coordinate bound on all reachable states. -/
theorem reachable_coordinate_le_of_strictIntegerPSemiflow
    (N : Network S) {w : S → ℕ} (hw : N.IsStrictIntegerPSemiflow w)
    {n m : S → ℕ} (hreach : N.CountReachable n m) (s : S) :
    m s ≤ countWeightedTotal w n / w s := by
  have htot := N.countWeightedTotal_eq_of_reachable hw.1 hreach
  have hterm : w s * m s ≤ countWeightedTotal w m := by
    unfold countWeightedTotal
    exact Finset.single_le_sum (f := fun t => w t * m t)
      (fun t _ => Nat.zero_le _) (Finset.mem_univ s)
  rw [htot] at hterm
  exact (Nat.le_div_iff_mul_le (hw.2 s)).2 (by simpa [Nat.mul_comm] using hterm)

/-- The finite box containing a conservative communication class. -/
def conservativeCountBox (w : S → ℕ) (n : S → ℕ) : Set (S → ℕ) :=
  {m | ∀ s, m s ≤ countWeightedTotal w n / w s}

/-- Every state reachable from `n` lies in the conservative box. -/
theorem reachable_mem_conservativeCountBox (N : Network S)
    {w : S → ℕ} (hw : N.IsStrictIntegerPSemiflow w)
    {n m : S → ℕ} (hreach : N.CountReachable n m) :
    m ∈ conservativeCountBox w n :=
  fun s => N.reachable_coordinate_le_of_strictIntegerPSemiflow hw hreach s

/-- A finite product of bounded natural-number coordinates is finite. -/
theorem conservativeCountBox_finite (w : S → ℕ) (n : S → ℕ)
    (hw : ∀ s, 0 < w s) :
    Set.Finite (conservativeCountBox w n) := by
  let t : S → Set ℕ := fun s => Set.Iic (countWeightedTotal w n / w s)
  have hfinite : Set.Finite (Set.univ.pi t) :=
    Set.Finite.pi (fun s => Set.finite_Iic _)
  refine hfinite.subset ?_
  intro m hm
  rw [Set.mem_pi]
  intro s _
  exact hm s

/-- **Finite stochastic communication classes in conservative networks.** -/
theorem reachableSet_finite_of_strictIntegerPSemiflow
    (N : Network S) {w : S → ℕ} (hw : N.IsStrictIntegerPSemiflow w)
    (n : S → ℕ) :
    Set.Finite {m : S → ℕ | N.CountReachable n m} := by
  exact (conservativeCountBox_finite w n hw.2).subset
    (fun m hm => N.reachable_mem_conservativeCountBox hw hm)

/-- Mutual communication class. -/
def CountCommunicates (N : Network S) (n m : S → ℕ) : Prop :=
  N.CountReachable n m ∧ N.CountReachable m n

/-- Conservative communicating classes are finite. -/
theorem communicationClass_finite_of_strictIntegerPSemiflow
    (N : Network S) {w : S → ℕ} (hw : N.IsStrictIntegerPSemiflow w)
    (n : S → ℕ) :
    Set.Finite {m : S → ℕ | N.CountCommunicates n m} := by
  exact (N.reachableSet_finite_of_strictIntegerPSemiflow hw n).subset
    (fun m hm => hm.1)

end Network
end CRNT
