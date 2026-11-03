import CRNT.Equilibria.GeneralizedComplexBalanceToric
import CRNT.Equilibria.ComplexBalanceGeometry

/-!
# Geometry of generalized complex-balanced equilibria

For generalized mass-action systems the role of the stoichiometric subspace in the
equilibrium torus is played by the kinetic-order subspace `T`.  Relative to one positive
generalized CBE, all positive generalized CBEs form a multiplicative torus parallel to
`Tᗮ`.  Its tangent dimension is `|S|-rank(T)`.
-/

namespace CRNT
namespace Network
namespace GeneralizedMassActionData

variable {S : Type} [DecidableEq S] [Fintype S]
variable {N : Network S}

/-- Positive generalized complex-balanced set. -/
def positiveComplexBalancedSet (G : N.GeneralizedMassActionData)
    (κ : N.RateConstants) : Set (Concentration S) :=
  {x | x.Positive ∧ G.IsComplexBalanced κ x}

/-- Generalized toric tangent space. -/
noncomputable def complexBalancedTangentSpace
    (G : N.GeneralizedMassActionData) (x : Concentration S) :
    Submodule ℝ (S → ℝ) :=
  (orthSum G.kineticOrderSubspace).map (diagonalMulLinear x)

/-- The generalized CBE manifold has codimension equal to the kinetic-order rank. -/
theorem finrank_complexBalancedTangentSpace
    (G : N.GeneralizedMassActionData) {x : Concentration S} (hx : x.Positive) :
    Module.finrank ℝ (G.complexBalancedTangentSpace x) =
      Fintype.card S - G.kineticOrderRank := by
  let f := (diagonalMulLinear x).domRestrict (orthSum G.kineticOrderSubspace)
  have hfinj : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    exact diagonalMulLinear_injective hx huv
  have hrange : LinearMap.range f = G.complexBalancedTangentSpace x := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u.1, u.2, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, rfl⟩
  rw [← hrange, LinearMap.finrank_range_of_inj hfinj]
  exact finrank_orthSum G.kineticOrderSubspace

/-- Global toric characterization of positive generalized CBEs. -/
theorem mem_positiveComplexBalancedSet_iff_toric
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcbs : G.IsComplexBalanced κ xstar) (x : Concentration S) :
    x ∈ G.positiveComplexBalancedSet κ ↔
      x.Positive ∧ logRatio x xstar ∈ orthSum G.kineticOrderSubspace := by
  constructor
  · rintro ⟨hx, hcbx⟩
    exact ⟨hx, G.logRatio_mem_orth_kineticOrderSubspace κ hwr hx hxs hcbx hcbs⟩
  · rintro ⟨hx, horth⟩
    exact ⟨hx, G.complexBalanced_of_toricLeaf κ hwr hxs hcbs ⟨hx, horth⟩⟩

/-- Geometric interpolation of generalized CBEs stays complex balanced. -/
theorem complexBalanced_geometricInterpolate
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible)
    {x y : Concentration S} (hx : x.Positive) (hy : y.Positive)
    (hcx : G.IsComplexBalanced κ x) (hcy : G.IsComplexBalanced κ y)
    (t : ℝ) :
    G.IsComplexBalanced κ (geometricInterpolate x y t) := by
  have horth := G.logRatio_mem_orth_kineticOrderSubspace κ hwr hy hx hcy hcx
  apply G.complexBalanced_of_toricLeaf κ hwr hx hcx
  refine ⟨geometricInterpolate_positive x y t, ?_⟩
  have hlog := logRatio_geometricInterpolate hx hy t
  change (fun s => Real.log (geometricInterpolate x y t s) - Real.log (x s)) ∈
    orthSum G.kineticOrderSubspace
  rw [hlog]
  exact (orthSum G.kineticOrderSubspace).smul_mem t horth

/-- Nonempty generalized CBE sets are path connected. -/
theorem positiveComplexBalancedSet_pathConnected
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible)
    (hne : (G.positiveComplexBalancedSet κ).Nonempty) :
    IsPathConnected (G.positiveComplexBalancedSet κ) := by
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
    G.complexBalanced_geometricInterpolate κ hwr hx.1 hy.1 hx.2 hy.2 t⟩

end GeneralizedMassActionData
end Network
end CRNT
