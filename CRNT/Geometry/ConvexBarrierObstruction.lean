import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Polyrith

/-!
# Why a convex polyhedral zero-separating surface cannot work

`CRNT.Geometry.PolyhedralBarrier` provides two trapping engines: `barrier`, the maximum of
finitely many affine functions, which guards a *convex* polyhedron, and `minMaxBarrier`, a minimum
of such maxima, which guards a possibly non-convex region.  This module records why the convex one
is not enough, so that the extra generality of `minMaxBarrier` is not gratuitous.

## The requirement

Craciun, *Toric differential inclusions and a proof of the global attractor conjecture* (v3),
Lemma 9.5: at a smooth point `X` of a zero-separating hypersurface the outer normal must lie in
the fan cone containing `X`; Lemma 9.7 adds the `δ`-slack, which forces the surface to be flat on a
slab of width at least `δ` around each cone, with the normal of that flat piece lying in that cone.

For the barrier `g X = max i (⟪n i, X⟫ - b i)` the piece attaining the maximum on a cone `C` must
therefore have `n_C ∈ C`, and — because a maximum of affine functions is what it is — also

  `⟪n_C, X⟫ - b_C ≥ ⟪n_{C'}, X⟫ - b_{C'}`  for every `X ∈ C` and every other cone `C'`.

Constant offsets cannot repair a violation of the underlying inequality `⟪n_C, X⟫ ≥ ⟪n_{C'}, X⟫`,
since the deficit scales linearly in `X` along `C`.  So the normals must be the face points of a
polytope whose normal fan refines the given fan, each lying inside its own normal cone.

## Reduction to weights

Craciun's fans of interest are hyperplane-generated (v3, §3): normals `a_1, …, a_m`, cones indexed
by realizable sign vectors `σ`.  Such an arrangement fan is the normal fan of the zonotope
`Z_w = ∑_j w_j [-a_j, a_j]` for *any* positive weights `w`, because its support function
`∑_j w_j |⟪a_j, X⟫|` has the arrangement as its linearity decomposition.  Matching the flat pieces
across a wall forces the normals of two adjacent maximal cones to differ by a multiple of that
wall's normal — precisely the zonotope edge structure — so the vertex dual to `σ` is

  `v_σ(w) = ∑_j w_j σ_j a_j`,

and the requirement `v_σ(w) ∈ C_σ` reads `0 ≤ σ_k ⟪a_k, v_σ(w)⟫` for every `k`.  This is **linear
in `w`**, so the whole convex route reduces to a linear feasibility question.

## The obstruction

`scripts/probe_zonotope_cone_selection.py` solves that feasibility problem.  In dimension two it is
always strictly feasible; in dimension three and above it is infeasible for generic arrangements.
The theorems below are the exact, floating-point-free core of that computation: three unit vectors
with all pairwise inner products equal to `c > 1/2` admit no positive weights at all.  Such a
triple exists (`c = 3/5` gives Gram matrix minors `1, 16/25, 44/125`, all positive, so the vectors
are a basis and hence *every* sign vector is realizable and every constraint really is imposed).

The moral: the guarded region must be allowed to be non-convex, which is exactly what
`PolyhedralBarrier.minMaxBarrier` supports and what Craciun's tile-by-tile surface is.  The
obstruction is specific to the globally homogeneous convex ansatz; the paper's construction escapes
it by living in a bounded window of log-coordinates with the scale hierarchy of §7.

Nothing here is an axiom or a `sorry`.

Depends on: Mathlib inner-product spaces and `Fin` big operators.
-/

open scoped RealInnerProductSpace

namespace CRNT
namespace ConvexBarrierObstruction

/-! ### The Gram-matrix form -/

/-- **No positive weights, Gram form.**  Write `G k j` for `⟪a k, a j⟫`, so that
`∑ j, w j * σ j * G k j` is `⟪a k, ∑ j, w j • σ j • a j⟫ = ⟪a k, v_σ(w)⟫`.

If the three vectors are unit and pairwise at inner product `c > 1/2`, the three sign vectors
`(+,-,-)`, `(-,+,-)`, `(-,-,+)` give
`w k ≥ c * (w i + w j)` for each `k`; summing these yields `W ≥ 2c · W` with `W > 0`, hence
`2c ≤ 1`, contradicting `c > 1/2`. -/
theorem not_exists_weights_gram
    (G : Fin 3 → Fin 3 → ℝ) (c : ℝ) (hc : 1 / 2 < c)
    (hdiag : ∀ k, G k k = 1) (hoff : ∀ i j, i ≠ j → G i j = c)
    (w : Fin 3 → ℝ) (hw : ∀ k, 0 < w k)
    (hsel : ∀ σ : Fin 3 → ℝ, (∀ j, σ j = 1 ∨ σ j = -1) →
      ∀ k, 0 ≤ σ k * ∑ j, w j * σ j * G k j) :
    False := by
  have d0 : G 0 0 = 1 := hdiag 0
  have d1 : G 1 1 = 1 := hdiag 1
  have d2 : G 2 2 = 1 := hdiag 2
  have e01 : G 0 1 = c := hoff 0 1 (by decide)
  have e02 : G 0 2 = c := hoff 0 2 (by decide)
  have e10 : G 1 0 = c := hoff 1 0 (by decide)
  have e12 : G 1 2 = c := hoff 1 2 (by decide)
  have e20 : G 2 0 = c := hoff 2 0 (by decide)
  have e21 : G 2 1 = c := hoff 2 1 (by decide)
  -- the sign vector `(+,-,-)`, tested at coordinate `0`
  have hA : ∀ j : Fin 3, (![1, -1, -1] : Fin 3 → ℝ) j = 1 ∨ (![1, -1, -1] : Fin 3 → ℝ) j = -1 := by
    intro j; fin_cases j <;> simp
  have h0 := hsel ![1, -1, -1] hA 0
  -- the sign vector `(-,+,-)`, tested at coordinate `1`
  have hB : ∀ j : Fin 3, (![-1, 1, -1] : Fin 3 → ℝ) j = 1 ∨ (![-1, 1, -1] : Fin 3 → ℝ) j = -1 := by
    intro j; fin_cases j <;> simp
  have h1 := hsel ![-1, 1, -1] hB 1
  -- the sign vector `(-,-,+)`, tested at coordinate `2`
  have hC : ∀ j : Fin 3, (![-1, -1, 1] : Fin 3 → ℝ) j = 1 ∨ (![-1, -1, 1] : Fin 3 → ℝ) j = -1 := by
    intro j; fin_cases j <;> simp
  have h2 := hsel ![-1, -1, 1] hC 2
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, d0, d1, d2, e01, e02, e10, e12, e20, e21] at h0 h1 h2
  nlinarith [hw 0, hw 1, hw 2, h0, h1, h2]

/-! ### The vector form -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **No positive weights, vector form.**  Three unit vectors in a real inner-product space with
all pairwise inner products equal to some `c > 1/2` admit no positive weights `w` for which every
zonotope vertex `v_σ(w) = ∑_j w_j σ_j a_j` lies in its own normal cone
`{X | ∀ k, 0 ≤ σ_k ⟪a_k, X⟫}`.

Consequently no max-of-affine barrier over such a hyperplane arrangement can carry, on each
maximal cone, a normal lying inside that cone. -/
theorem not_exists_weights_vector
    (a : Fin 3 → E) (c : ℝ) (hc : 1 / 2 < c)
    (hunit : ∀ k, ⟪a k, a k⟫ = 1) (hpair : ∀ i j, i ≠ j → ⟪a i, a j⟫ = c)
    (w : Fin 3 → ℝ) (hw : ∀ k, 0 < w k)
    (hsel : ∀ σ : Fin 3 → ℝ, (∀ j, σ j = 1 ∨ σ j = -1) →
      ∀ k, 0 ≤ σ k * ⟪a k, ∑ j, (w j * σ j) • a j⟫) :
    False := by
  refine not_exists_weights_gram (fun k j => ⟪a k, a j⟫) c hc hunit hpair w hw ?_
  intro σ hσ k
  have hinner : ⟪a k, ∑ j, (w j * σ j) • a j⟫ = ∑ j, w j * σ j * ⟪a k, a j⟫ := by
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_right]
  rw [← hinner]
  exact hsel σ hσ k

/-! ### The witness exists -/

/-- The obstruction is not vacuous: `c = 3/5` is admissible, and the Gram matrix
`[[1,c,c],[c,1,c],[c,c,1]]` is positive definite, so three such unit vectors exist in `ℝ³` and
form a basis — whence every sign vector is realizable and every selection constraint used above is
genuinely imposed by the fan. -/
theorem witness_gram_posDef :
    (1 / 2 : ℝ) < 3 / 5 ∧
      (1 : ℝ) > 0 ∧ (1 : ℝ) * 1 - (3 / 5) * (3 / 5) > 0 ∧
      (1 : ℝ) * (1 * 1 - (3 / 5) * (3 / 5)) - (3 / 5) * ((3 / 5) * 1 - (3 / 5) * (3 / 5))
        + (3 / 5) * ((3 / 5) * (3 / 5) - 1 * (3 / 5)) > 0 := by
  norm_num

end ConvexBarrierObstruction
end CRNT
