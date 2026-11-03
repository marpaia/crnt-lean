import CRNT.Oscillation.ReturnMapPersistence
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Attraction from a contracting Poincare return map

Linear Floquet stability is converted into nonlinear orbital stability through a local Poincare map.
This file closes the metric fixed-point half of that argument.  If a section return map is a strict
contraction around its fixed point, successive returns converge geometrically to that fixed point.

What remains Floquet-specific is to obtain such a contraction (possibly after choosing an equivalent
norm on the transversal section) from the nontrivial Floquet multipliers, and then to control the
continuous-time pieces between successive section hits.
-/

namespace CRNT

open Filter Topology

variable {E : Type*} [PseudoMetricSpace E]

/-- A globally stated contraction certificate for a return map.  Local Poincare arguments can use a
closed invariant local section domain as `E` (for example a subtype). -/
structure ContractingReturnMapData (E : Type*) [PseudoMetricSpace E] where
  returnMap : E → E
  fixedPoint : E
  factor : ℝ
  factor_nonneg : 0 ≤ factor
  factor_lt_one : factor < 1
  fixed : returnMap fixedPoint = fixedPoint
  dist_le : ∀ x y, dist (returnMap x) (returnMap y) ≤ factor * dist x y

namespace ContractingReturnMapData

variable (D : ContractingReturnMapData E)

/-- Discrete sequence of successive section returns. -/
def iterates (D : ContractingReturnMapData E) (x : E) : ℕ → E
  | 0 => x
  | n + 1 => D.returnMap (iterates D x n)

@[simp] theorem iterates_zero (x : E) : D.iterates x 0 = x := rfl

@[simp] theorem iterates_succ (x : E) (n : ℕ) :
    D.iterates x (n + 1) = D.returnMap (D.iterates x n) := rfl

/-- Geometric distance estimate for successive returns. -/
theorem dist_iterates_fixedPoint_le (x : E) :
    ∀ n : ℕ,
      dist (D.iterates x n) D.fixedPoint ≤ D.factor ^ n * dist x D.fixedPoint := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [D.iterates_succ]
      calc
        dist (D.returnMap (D.iterates x n)) D.fixedPoint =
            dist (D.returnMap (D.iterates x n)) (D.returnMap D.fixedPoint) := by
              rw [D.fixed]
        _ ≤ D.factor * dist (D.iterates x n) D.fixedPoint := D.dist_le _ _
        _ ≤ D.factor * (D.factor ^ n * dist x D.fixedPoint) :=
              mul_le_mul_of_nonneg_left ih D.factor_nonneg
        _ = D.factor ^ (n + 1) * dist x D.fixedPoint := by
              rw [pow_succ]
              ring

/-- Successive returns converge to the fixed point. -/
theorem tendsto_iterates_fixedPoint (x : E) :
    Tendsto (D.iterates x) atTop (𝓝 D.fixedPoint) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hpow : Tendsto (fun n : ℕ => D.factor ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one D.factor_nonneg D.factor_lt_one
  have hbound : Tendsto
      (fun n : ℕ => D.factor ^ n * dist x D.fixedPoint) atTop (𝓝 0) := by
    simpa using hpow.mul_const (dist x D.fixedPoint)
  exact squeeze_zero (fun _ => dist_nonneg) (D.dist_iterates_fixedPoint_le x) hbound

/-- The fixed point is unique for a strict contraction.

The ambient space here is only a `PseudoMetricSpace`, in which distinct points may be at distance
`0`; uniqueness genuinely fails there. Rather than strengthen the section variable (which would
clash with the existing instance), the separation property is taken as an explicit hypothesis. -/
theorem fixedPoint_unique (hsep : ∀ a b : E, dist a b = 0 → a = b)
    {x : E} (hx : D.returnMap x = x) : x = D.fixedPoint := by
  refine hsep _ _ ?_
  have h := D.dist_le x D.fixedPoint
  rw [hx, D.fixed] at h
  have hk := D.factor_lt_one
  have hf0 := D.factor_nonneg
  have hnn : 0 ≤ dist x D.fixedPoint := dist_nonneg
  nlinarith

end ContractingReturnMapData

end CRNT
