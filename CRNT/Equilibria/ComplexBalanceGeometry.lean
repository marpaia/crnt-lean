import CRNT.Theorems.DeficiencyZero.Toric
import CRNT.LinearAlgebra.OrthogonalComplement
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Path

/-!
# Geometry of the positive complex-balanced equilibrium set

Once one positive complex-balanced reference `x*` exists on a weakly reversible network,
all positive complex-balanced equilibria are obtained by exponentiating the orthogonal
complement of the stoichiometric subspace:

`x = x* ⊙ exp μ`,  `μ ∈ Sᗮ`.

Thus the global CBE set is a smooth multiplicative torus of dimension `|species|-s`.
Its tangent space at `x` is `diag(x) Sᗮ`, and it is geometrically/logarithmically convex:
coordinatewise geometric interpolation between two CBEs remains complex balanced.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Positive complex-balanced equilibrium set at fixed rate constants. -/
def positiveComplexBalancedSet (N : Network S) (κ : N.RateConstants) :
    Set (Concentration S) :=
  {x | x.Positive ∧ N.IsComplexBalanced κ x}

/-- Multiplicative exponential parametrization through a positive reference state. -/
noncomputable def toricParam (xstar : Concentration S) (μ : S → ℝ) : Concentration S :=
  fun s => xstar s * Real.exp (μ s)

/-- The toric parametrization is always positive when its reference is positive. -/
theorem toricParam_positive {xstar : Concentration S} (hxs : xstar.Positive)
    (μ : S → ℝ) : (toricParam xstar μ).Positive := by
  intro s
  exact mul_pos (hxs s) (Real.exp_pos _)

/-- Exact logarithmic displacement of the toric parametrization. -/
theorem logRatio_toricParam {xstar : Concentration S} (hxs : xstar.Positive)
    (μ : S → ℝ) :
    (fun s => Real.log (toricParam xstar μ s) - Real.log (xstar s)) = μ := by
  funext s
  simp [toricParam, Real.log_mul (hxs s).ne' (Real.exp_ne_zero _), hxs s, Real.log_exp]

/-- Orthogonal logarithmic directions preserve complex balance. -/
theorem toricParam_complexBalanced
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcbs : N.IsComplexBalanced κ xstar)
    {μ : S → ℝ} (hμ : μ ∈ orthSum N.stoichSubspace) :
    N.IsComplexBalanced κ (toricParam xstar μ) := by
  apply N.complexBalanced_of_logRatio_orthogonal κ
    (toricParam_positive hxs μ) hxs hcbs
  simpa [logRatio_toricParam hxs μ] using hμ

/-- **Global Horn--Jackson toric characterization.** -/
theorem mem_positiveComplexBalancedSet_iff_toric
    (N : Network S) (κ : N.RateConstants) (hwr : N.WeaklyReversible)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcbs : N.IsComplexBalanced κ xstar) (x : Concentration S) :
    x ∈ N.positiveComplexBalancedSet κ ↔
      ∃ μ ∈ orthSum N.stoichSubspace, x = toricParam xstar μ := by
  constructor
  · rintro ⟨hx, hcbx⟩
    let μ : S → ℝ := fun s => Real.log (x s) - Real.log (xstar s)
    refine ⟨μ, N.logRatio_orthogonal_of_complexBalanced hwr κ hx hxs hcbx hcbs, ?_⟩
    funext s
    dsimp [μ, toricParam]
    rw [Real.exp_sub, Real.exp_log (hx s), Real.exp_log (hxs s)]
    field_simp [(hxs s).ne']
  · rintro ⟨μ, hμ, rfl⟩
    exact ⟨toricParam_positive hxs μ,
      N.toricParam_complexBalanced κ hxs hcbs hμ⟩

/-- Coordinatewise multiplication by a fixed concentration, as a linear map. -/
noncomputable def diagonalMulLinear (x : Concentration S) :
    (S → ℝ) →ₗ[ℝ] (S → ℝ) where
  toFun := fun v s => x s * v s
  map_add' := by intros; ext s; simp [mul_add]
  map_smul' := by intros; ext s; simp [mul_assoc, mul_left_comm]

/-- Tangent space to the positive complex-balanced manifold at `x`. -/
noncomputable def complexBalancedTangentSpace (N : Network S)
    (x : Concentration S) : Submodule ℝ (S → ℝ) :=
  (orthSum N.stoichSubspace).map (diagonalMulLinear x)

/-- Positive diagonal multiplication is injective. -/
theorem diagonalMulLinear_injective {x : Concentration S} (hx : x.Positive) :
    Function.Injective (diagonalMulLinear x) := by
  intro u v huv
  funext s
  have hs := congrFun huv s
  simpa [diagonalMulLinear] using (mul_left_cancel₀ (hx s).ne' hs)

/-- Dimension of the CBE tangent space equals the number of independent conservation
laws, `|S|-s`. -/
theorem finrank_complexBalancedTangentSpace
    (N : Network S) {x : Concentration S} (hx : x.Positive) :
    Module.finrank ℝ (N.complexBalancedTangentSpace x) =
      Fintype.card S - N.stoichRank := by
  let f := (diagonalMulLinear x).domRestrict (orthSum N.stoichSubspace)
  have hfinj : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    exact diagonalMulLinear_injective hx huv
  have hrange : LinearMap.range f = N.complexBalancedTangentSpace x := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u.1, u.2, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, rfl⟩
  rw [← hrange, LinearMap.finrank_range_of_inj hfinj]
  exact finrank_orthSum N.stoichSubspace

/-- Coordinatewise geometric interpolation. -/
noncomputable def geometricInterpolate (x y : Concentration S) (t : ℝ) : Concentration S :=
  fun s => Real.exp ((1 - t) * Real.log (x s) + t * Real.log (y s))

/-- Geometric interpolation is positive. -/
theorem geometricInterpolate_positive (x y : Concentration S) (t : ℝ) :
    (geometricInterpolate x y t).Positive := fun s => Real.exp_pos _

/-- The log displacement from the first endpoint is `t` times the endpoint log
ratio. -/
theorem logRatio_geometricInterpolate
    {x y : Concentration S} (hx : x.Positive) (hy : y.Positive) (t : ℝ) :
    (fun s => Real.log (geometricInterpolate x y t s) - Real.log (x s)) =
      t • (fun s => Real.log (y s) - Real.log (x s)) := by
  funext s
  simp [geometricInterpolate, Real.log_exp, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Log/geodesic convexity of the complex-balanced equilibrium set.** -/
theorem complexBalanced_geometricInterpolate
    (N : Network S) (κ : N.RateConstants) (hwr : N.WeaklyReversible)
    {x y : Concentration S} (hx : x.Positive) (hy : y.Positive)
    (hcx : N.IsComplexBalanced κ x) (hcy : N.IsComplexBalanced κ y)
    (t : ℝ) :
    N.IsComplexBalanced κ (geometricInterpolate x y t) := by
  have horth := N.logRatio_orthogonal_of_complexBalanced hwr κ hy hx hcy hcx
  apply N.complexBalanced_of_logRatio_orthogonal κ
    (geometricInterpolate_positive x y t) hx hcx
  rw [logRatio_geometricInterpolate hx hy t]
  exact (orthSum N.stoichSubspace).smul_mem t horth

/-- The positive complex-balanced set is path connected whenever nonempty. -/
theorem positiveComplexBalancedSet_pathConnected
    (N : Network S) (κ : N.RateConstants) (hwr : N.WeaklyReversible)
    (hne : (N.positiveComplexBalancedSet κ).Nonempty) :
    IsPathConnected (N.positiveComplexBalancedSet κ) := by
  rcases hne with ⟨x, hx⟩
  refine ⟨x, hx, ?_⟩
  intro y hy
  let f : ℝ → Concentration S := fun t => geometricInterpolate x y t
  have hf : Continuous f := by
    unfold f geometricInterpolate
    fun_prop
  have h0 : f 0 = x := by
    funext s
    simp [f, geometricInterpolate, Real.exp_log (hx.1 s)]
  have h1 : f 1 = y := by
    funext s
    simp [f, geometricInterpolate, Real.exp_log (hy.1 s)]
  apply JoinedIn.ofLine hf.continuousOn h0 h1
  rintro z ⟨t, ht, rfl⟩
  exact ⟨geometricInterpolate_positive x y t,
    N.complexBalanced_geometricInterpolate κ hwr hx.1 hy.1 hx.2 hy.2 t⟩

end Network
end CRNT
