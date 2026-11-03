import CRNT.Oscillation.PlanarCanonicalReturn
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Explicit coordinates on the canonical planar transversal

The canonical Poincare section through a recurrent point `q` has normal `field q`.  In two
coordinates there is a canonical tangent direction as well: rotate the normal by ninety degrees.
This file makes the scalar section coordinate completely explicit, eliminating another arbitrary
choice from the remaining Poincare--Bendixson construction.
-/

namespace CRNT

-- `⟪x, y⟫_ℝ` lives in the `InnerProductSpace` scope; without this the bracket is not a
-- valid token, which surfaces as a bare `expected token` parse error.
open scoped InnerProductSpace

namespace Planar

/-- Counterclockwise quarter-turn in `R^2`. -/
noncomputable def quarterTurn (v : Phase2) : Phase2 :=
  -- `Phase2` is `EuclideanSpace ℝ (Fin 2)`, so a raw vector literal must be transported
  -- into the `WithLp` wrapper.
  WithLp.toLp 2 ![-v 1, v 0]

@[simp] theorem quarterTurn_zero (v : Phase2) : quarterTurn v 0 = -v 1 := by
  simp [quarterTurn]

@[simp] theorem quarterTurn_one (v : Phase2) : quarterTurn v 1 = v 0 := by
  simp [quarterTurn]

/-- A vector is orthogonal to its quarter-turn. -/
theorem real_inner_quarterTurn_self (v : Phase2) :
    ⟪quarterTurn v, v⟫_ℝ = 0 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two,
    quarterTurn_zero, quarterTurn_one]
  ring

/-- Quarter-turn preserves squared norm. -/
theorem norm_sq_quarterTurn (v : Phase2) :
    ‖quarterTurn v‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two,
    quarterTurn_zero, quarterTurn_one]
  ring

/-- Hence the quarter-turn is nonzero whenever the original vector is nonzero. -/
theorem quarterTurn_ne_zero {v : Phase2} (hv : v ≠ 0) : quarterTurn v ≠ 0 := by
  intro hzero
  have hnorm : ‖quarterTurn v‖ ^ 2 = 0 := by simp [hzero]
  rw [norm_sq_quarterTurn] at hnorm
  have : ‖v‖ = 0 := sq_eq_zero_iff.mp hnorm
  exact hv (norm_eq_zero.mp this)

/-- Explicit scalar parameterization of the canonical affine section through `q`. -/
noncomputable def canonicalSectionPoint (field : Phase2 → Phase2) (q : Phase2) (u : ℝ) : Phase2 :=
  q + u • quarterTurn (field q)

@[simp] theorem canonicalSectionPoint_zero (field : Phase2 → Phase2) (q : Phase2) :
    canonicalSectionPoint field q 0 = q := by
  simp [canonicalSectionPoint]

/-- Every point of the explicit parameterization lies on the canonical section. -/
theorem canonicalSectionPoint_mem (field : Phase2 → Phase2) (q : Phase2) (u : ℝ) :
    canonicalSectionPoint field q u ∈ canonicalSection field q := by
  unfold canonicalSection canonicalSectionPoint
  have hcancel : q + u • quarterTurn (field q) - q = u • quarterTurn (field q) := by abel
  simp only [Set.mem_setOf_eq, hcancel]
  rw [real_inner_smul_left, real_inner_quarterTurn_self, mul_zero]

/-- At a non-equilibrium point the scalar section parameterization is injective. -/
theorem canonicalSectionPoint_injective
    {field : Phase2 → Phase2} {q : Phase2} (hne : field q ≠ 0) :
    Function.Injective (canonicalSectionPoint field q) := by
  intro u v huv
  have ht : quarterTurn (field q) ≠ 0 := quarterTurn_ne_zero hne
  have heq : u • quarterTurn (field q) = v • quarterTurn (field q) := by
    apply_fun fun x => x - q at huv
    simpa [canonicalSectionPoint] using huv
  have hsub : (u - v) • quarterTurn (field q) = 0 := by
    rw [sub_smul, heq, sub_self]
  rcases smul_eq_zero.mp hsub with huv0 | ht0
  · linarith
  · exact (ht ht0).elim

/-- Every point on the canonical affine section has a unique scalar coordinate when `field q != 0`.
The coordinate is the projection onto the quarter-turn direction. -/
noncomputable def canonicalSectionScalar
    (field : Phase2 → Phase2) (q x : Phase2) : ℝ :=
  ⟪x - q, quarterTurn (field q)⟫_ℝ / ‖field q‖ ^ 2

/-- Squared Euclidean norm on `Phase2` in coordinates.  Stated once here because the
canonical-section and flow-box files both need it; `rw [← real_inner_self_eq_norm_sq]` does
not fire on the goal directly, so take the inner-product equation as a hypothesis. -/
theorem norm_sq_coords (v : Phase2) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
  have h := real_inner_self_eq_norm_sq v
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two] at h
  rw [← h]; ring

/-- Scalar-coordinate reconstruction for points lying on the canonical section. -/
theorem canonicalSectionPoint_scalar
    {field : Phase2 → Phase2} {q x : Phase2}
    (hne : field q ≠ 0) (hx : x ∈ canonicalSection field q) :
    canonicalSectionPoint field q (canonicalSectionScalar field q x) = x := by
  have hn2 := norm_sq_coords (field q)
  have hnz : field q 0 ^ 2 + field q 1 ^ 2 ≠ 0 := by
    rw [← hn2]; exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)
  -- section membership, in coordinates
  have hd : (x 0 - q 0) * field q 0 + (x 1 - q 1) * field q 1 = 0 := by
    have h := hx
    simp only [canonicalSection, Set.mem_setOf_eq, PiLp.inner_apply, RCLike.inner_apply,
      conj_trivial, Fin.sum_univ_two, WithLp.ofLp_sub, Pi.sub_apply] at h
    linear_combination h
  -- the scalar coordinate, in coordinates
  have hu : canonicalSectionScalar field q x
      = (-(field q 1) * (x 0 - q 0) + field q 0 * (x 1 - q 1))
          / (field q 0 ^ 2 + field q 1 ^ 2) := by
    simp only [canonicalSectionScalar, quarterTurn, PiLp.inner_apply, RCLike.inner_apply,
      conj_trivial, Fin.sum_univ_two, hn2, WithLp.ofLp_sub, WithLp.ofLp_toLp,
      Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  -- Work with the *underlying functions*: `ofLp` of `+`, `•` and `toLp` are all `rfl`,
  -- so the coordinate facts below close the vector goal by defeq -- which is what `simp`
  -- would not do through the sum at a `fin_cases` Fin literal.
  have hvec : ∀ i : Fin 2,
      (q.ofLp + canonicalSectionScalar field q x •
        (![-(field q 1), field q 0] : Fin 2 → ℝ)) i = x.ofLp i := by
    -- `fin_cases` yields the Fin literal `⟨0, ⋯⟩`, which `Matrix.cons_val_zero` (keyed on
    -- `0`) cannot match.  `Fin.forall_fin_two` splits into goals at literal `0` and `1`.
    rw [Fin.forall_fin_two]
    constructor
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, hu]
      field_simp
      linear_combination (-(field q 0)) * hd
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.cons_val_zero, hu]
      field_simp
      linear_combination (-(field q 1)) * hd
  ext i
  exact hvec i

/-- The scalar coordinate inverts the explicit parameterization. -/
@[simp] theorem canonicalSectionScalar_point
    {field : Phase2 → Phase2} {q : Phase2} (hne : field q ≠ 0) (u : ℝ) :
    canonicalSectionScalar field q (canonicalSectionPoint field q u) = u := by
  have hmem := canonicalSectionPoint_mem field q u
  have hrecon := canonicalSectionPoint_scalar hne hmem
  exact canonicalSectionPoint_injective hne hrecon

/-- On an equilibrium-free minimal omega set the canonical section therefore comes with a genuine
one-dimensional coordinate chart, not merely an affine-set representation. -/
theorem MinimalOmegaData.canonicalSectionParam_injective
    {field : Phase2 → Phase2} {D : FlowTrappingData field}
    (M : MinimalOmegaData D) {q : Phase2} (hq : q ∈ M.carrier) :
    Function.Injective (canonicalSectionPoint field q) :=
  canonicalSectionPoint_injective (M.equilibriumFree q hq)

end Planar
end CRNT
