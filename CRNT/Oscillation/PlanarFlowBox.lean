import CRNT.Oscillation.PlanarNoCrossing
import CRNT.Multistationarity.GaleNikaido

/-!
# Canonical planar flow boxes

This file closes the inverse-function-theorem part of the Poincare--Bendixson construction.

For a non-equilibrium point `q`, use coordinates `z : Fin 2 → ℝ` with

* `z 0` = time along the flow;
* `z 1` = displacement along the canonical transversal
  `q + u • quarterTurn (field q)`.

The local flow-box map is

`Ψ(z) = trajectory (q + z 1 • quarterTurn (field q)) (z 0)`.

At the origin its two derivative columns are `field q` and `quarterTurn (field q)`.  Their
2×2 determinant is `‖field q‖²`, hence nonzero at every non-equilibrium point.  Consequently any
certified strict derivative of the complete flow in the initial state/time variables yields a local
homeomorphism by the ordinary inverse function theorem.

The repository's `FlowTrappingData` deliberately carries exact trajectories but not differentiable
dependence on their initial states.  `CanonicalFlowBoxRegularity` records precisely that missing ODE
regularity and nothing about recurrence or global planar topology.
-/

namespace CRNT
namespace Planar

/-- Canonical time/transversal flow-box map through `q`. -/
noncomputable def canonicalFlowBoxMap {field : Phase2 → Phase2}
    (D : FlowTrappingData field) (q : Phase2) (z : Phase2) : Phase2 :=
  D.trajectory (canonicalSectionPoint field q (z 1)) (z 0)

/-- The expected derivative of the canonical flow-box map at the origin. -/
noncomputable def canonicalFlowBoxLinear (field : Phase2 → Phase2) (q : Phase2) :
    Phase2 →ₗ[ℝ] Phase2 where
  toFun := fun z => z 0 • field q + z 1 • quarterTurn (field q)
  map_add' := by
    intro x y
    ext i
    simp [add_smul, add_assoc, add_left_comm, add_comm]
  map_smul' := by
    intro a x
    ext i
    simp [mul_smul, smul_add]

/-- Matrix representation of the canonical derivative: first column is the flow direction and the
second is the quarter-turn tangent direction. -/
def canonicalFlowBoxMatrix (field : Phase2 → Phase2) (q : Phase2) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![field q 0, -(field q 1);
     field q 1,   field q 0]

@[simp] theorem canonicalFlowBoxMatrix_apply_zero_zero
    (field : Phase2 → Phase2) (q : Phase2) :
    canonicalFlowBoxMatrix field q 0 0 = field q 0 := by
  simp [canonicalFlowBoxMatrix]

/-- The canonical flow-box determinant is the squared Euclidean norm of the vector field. -/
theorem canonicalFlowBoxMatrix_det (field : Phase2 → Phase2) (q : Phase2) :
    (canonicalFlowBoxMatrix field q).det = ‖field q‖ ^ 2 := by
  -- `det_fin_two` leaves `!![..] 0 0` entries; `det_fin_two_of` consumes the literal.
  simp only [canonicalFlowBoxMatrix, quarterTurn, WithLp.ofLp_toLp,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [Matrix.det_fin_two_of, norm_sq_coords]
  ring

/-- Hence the canonical derivative is nonsingular at every non-equilibrium point. -/
theorem canonicalFlowBoxMatrix_det_ne_zero
    {field : Phase2 → Phase2} {q : Phase2} (hne : field q ≠ 0) :
    (canonicalFlowBoxMatrix field q).det ≠ 0 := by
  rw [canonicalFlowBoxMatrix_det]
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)

/-- ODE regularity needed to invoke the inverse-function theorem for the *supplied* complete flow.

A future general ODE-flow theorem may construct this automatically from `ContDiff ℝ 1 field`; until
then this record makes the exact missing dependence-on-initial-data fact explicit. -/
structure CanonicalFlowBoxRegularity {field : Phase2 → Phase2}
    (D : FlowTrappingData field) (q : Phase2) : Prop where
  strictDerivative :
    HasStrictFDerivAt (canonicalFlowBoxMap D q)
      ((canonicalFlowBoxLinear field q).toContinuousLinearMap) 0

namespace CanonicalFlowBoxRegularity

variable {field : Phase2 → Phase2} {D : FlowTrappingData field} {q : Phase2}

/-- Matrix of `canonicalFlowBoxLinear` in the standard Euclidean basis.  Column `j` is the
image of `EuclideanSpace.single j 1`, i.e. the flow direction for `j = 0` and its
quarter-turn for `j = 1` — exactly the columns of `canonicalFlowBoxMatrix`. -/
theorem toMatrix_canonicalFlowBoxLinear (field : Phase2 → Phase2) (q : Phase2) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis (canonicalFlowBoxLinear field q)
      = canonicalFlowBoxMatrix field q := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  fin_cases j <;> fin_cases i <;>
    simp [canonicalFlowBoxLinear, canonicalFlowBoxMatrix, quarterTurn,
      OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
      EuclideanSpace.single_apply]

/-- Hence the linear-map determinant is the matrix determinant, so it is nonzero away from
equilibria. -/
theorem canonicalFlowBoxLinear_det_ne_zero {field : Phase2 → Phase2} {q : Phase2}
    (hne : field q ≠ 0) : LinearMap.det (canonicalFlowBoxLinear field q) ≠ 0 := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
    toMatrix_canonicalFlowBoxLinear]
  exact canonicalFlowBoxMatrix_det_ne_zero hne

/-- The derivative bundled as a continuous linear equivalence. -/
noncomputable def linearEquiv
    (R : CanonicalFlowBoxRegularity D q) (hne : field q ≠ 0) : Phase2 ≃L[ℝ] Phase2 := by
  let L : Phase2 →L[ℝ] Phase2 := (canonicalFlowBoxLinear field q).toContinuousLinearMap
  have hdet : L.det ≠ 0 := by
    simpa [L, ContinuousLinearMap.det] using
      canonicalFlowBoxLinear_det_ne_zero hne
  exact L.toContinuousLinearEquivOfDetNeZero hdet

/-- The strict derivative can be rewritten against the invertible derivative equivalence. -/
theorem strictDerivative_equiv
    (R : CanonicalFlowBoxRegularity D q) (hne : field q ≠ 0) :
    HasStrictFDerivAt (canonicalFlowBoxMap D q)
      (R.linearEquiv hne : Phase2 →L[ℝ] Phase2) 0 := by
  let L : Phase2 →L[ℝ] Phase2 := (canonicalFlowBoxLinear field q).toContinuousLinearMap
  have hdet : L.det ≠ 0 := by
    -- the `rw [← jacobianMatrix_det]` pattern does not match a let-bound `L.det`;
    -- unfold `ContinuousLinearMap.det` in the simp set instead.
    simpa [L, ContinuousLinearMap.det] using
      canonicalFlowBoxLinear_det_ne_zero hne
  have hcoe : (L.toContinuousLinearEquivOfDetNeZero hdet : Phase2 →L[ℝ] Phase2) = L :=
    L.coe_toContinuousLinearEquivOfDetNeZero hdet
  simpa [CanonicalFlowBoxRegularity.linearEquiv, L, hcoe] using R.strictDerivative

/-- Local inverse-function-theorem chart for the canonical flow box. -/
noncomputable def localHomeomorph
    (R : CanonicalFlowBoxRegularity D q) (hne : field q ≠ 0) :
    OpenPartialHomeomorph Phase2 Phase2 :=
  (R.strictDerivative_equiv hne).toOpenPartialHomeomorph (canonicalFlowBoxMap D q)

/-- The coordinate origin belongs to the flow-box source. -/
theorem zero_mem_source
    (R : CanonicalFlowBoxRegularity D q) (hne : field q ≠ 0) :
    (0 : Phase2) ∈ (R.localHomeomorph hne).source :=
  (R.strictDerivative_equiv hne).mem_toOpenPartialHomeomorph_source

/-- The flow-box map sends the coordinate origin to the recurrent point. -/
@[simp] theorem map_zero
    (R : CanonicalFlowBoxRegularity D q) :
    canonicalFlowBoxMap D q 0 = q := by
  simp [canonicalFlowBoxMap, canonicalSectionPoint, D.trajectory_zero]

/-- The recurrent point belongs to the target of the local flow box. -/
theorem q_mem_target
    (R : CanonicalFlowBoxRegularity D q) (hne : field q ≠ 0) :
    q ∈ (R.localHomeomorph hne).target := by
  have h := (R.strictDerivative_equiv hne).image_mem_toOpenPartialHomeomorph_target
  simpa [localHomeomorph, R.map_zero] using h

/-- Local uniqueness of time/transversal coordinates inside the IFT source. -/
theorem coordinates_unique
    (R : CanonicalFlowBoxRegularity D q) (hne : field q ≠ 0)
    {z₁ z₂ : Phase2}
    (hz₁ : z₁ ∈ (R.localHomeomorph hne).source)
    (hz₂ : z₂ ∈ (R.localHomeomorph hne).source)
    (heq : canonicalFlowBoxMap D q z₁ = canonicalFlowBoxMap D q z₂) :
    z₁ = z₂ := by
  exact (R.localHomeomorph hne).injOn hz₁ hz₂ (by simpa [localHomeomorph] using heq)

end CanonicalFlowBoxRegularity

/-- Exact regularity theorem still needed from the general ODE layer to make Poincare--Bendixson
fully automatic from `FlowTrappingData + C¹ field`.  All inverse-function work after this proposition
is closed above. -/
def CanonicalFlowRegularityTarget : Prop :=
  ∀ (field : Phase2 → Phase2) (D : FlowTrappingData field) (q : Phase2),
    ContDiff ℝ 1 field → Nonempty (CanonicalFlowBoxRegularity D q)

end Planar
end CRNT
