import CRNT.Dynamics.MassActionAlgebra

/-!
# Pairing the kinetic map with functions on complexes

For a vector `v` on complexes and a function `φ` on complexes,
`∑_c (A_κ v)_c φ(c) = ∑_r κ_r v(source r) (φ(target r) − φ(source r))`. With `φ(c) = c_s` this is
`(Y A_κ v)_s = ∑_r κ_r v(source r) (y'_r − y_r)_s`.

* `sum_kineticMap_mul`, `complexMap_kineticMap_apply`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Pairing the kinetic image with a function on complexes. -/
theorem sum_kineticMap_mul (N : Network S) (κ : RateConstants N) (v : N.ComplexIdx → ℝ)
    (φ : N.ComplexIdx → ℝ) :
    ∑ c, N.kineticMap κ v c * φ c =
      ∑ r : N.R, κ.k r * v (N.sourceIdx r) * (φ (N.targetIdx r) - φ (N.sourceIdx r)) := by
  simp only [kineticMap_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  have : ∀ c : N.ComplexIdx, κ.k r * v (N.sourceIdx r) *
      ((if N.targetIdx r = c then (1 : ℝ) else 0) - (if N.sourceIdx r = c then 1 else 0)) * φ c =
      κ.k r * v (N.sourceIdx r) * ((if N.targetIdx r = c then φ c else 0) -
        (if N.sourceIdx r = c then φ c else 0)) := by
    intro c; split_ifs <;> ring
  simp only [this]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
  simp

/-- `Y A_κ v = ∑_r κ_r v_{source r} (y'_r − y_r)`. -/
theorem complexMap_kineticMap_apply (N : Network S) (κ : RateConstants N) (v : N.ComplexIdx → ℝ)
    (s : S) :
    N.complexMap (N.kineticMap κ v) s = ∑ r : N.R, κ.k r * v (N.sourceIdx r) * N.reactionVector r s := by
  rw [complexMap_apply, sum_kineticMap_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp [targetIdx, sourceIdx, reactionVector_apply]

end Network

end CRNT
