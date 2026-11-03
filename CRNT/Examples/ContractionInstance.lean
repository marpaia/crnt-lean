import CRNT.Dynamics.EuclideanContraction

/-!
# Non-vacuity of `massAction_contraction`

For `0 → X`, `X → 0` with unit rates the Jacobian is `u ↦ −u` everywhere, so the hypothesis of
`massAction_contraction` holds on the whole space with `c = 1`, and any two solutions satisfy
`|x(t) − y(t)|² ≤ e^{−2t} |x(0) − y(0)|²`.
-/

namespace CRNT
namespace Examples
namespace ContractionInstance

open Network

/-- `0 → X`, `X → 0`. -/
abbrev net : Network Unit :=
  ⟨Fin 2, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨0, fun _ => 1⟩ else ⟨fun _ => 1, 0⟩⟩

/-- Unit rates. -/
def κ : RateConstants net := ⟨fun _ => 1, fun _ => one_pos⟩

theorem jacobian_eq (x u : Concentration Unit) :
    net.massActionJacobianCLM κ x u = -u := by
  funext s
  simp only [massActionJacobianCLM, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul, Fin.sum_univ_two, Pi.neg_apply]
  simp [κ, massActionMonomialGrad, Network.reactionVector, Reaction.vector]

theorem jacobian_bound (x u : Concentration Unit) :
    ∑ s, u s * net.massActionJacobianCLM κ x u s ≤ -1 * ∑ s, u s ^ 2 := by
  rw [jacobian_eq]
  simp only [Pi.neg_apply]
  apply le_of_eq
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- **Contraction for `0 ⇌ X`.** -/
theorem contraction {x y : ℝ → Concentration Unit}
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (net.massActionVectorField κ (x t)) t)
    (hy : ∀ t, 0 ≤ t → HasDerivAt y (net.massActionVectorField κ (y t)) t) :
    ∀ t, 0 ≤ t → sqDist (x t) (y t) ≤ Real.exp (-(2 * 1 * t)) * sqDist (x 0) (y 0) :=
  net.massAction_contraction κ convex_univ (fun x _ u => jacobian_bound x u) hx hy
    (fun _ _ => Set.mem_univ _) (fun _ _ => Set.mem_univ _)

end ContractionInstance
end Examples
end CRNT
