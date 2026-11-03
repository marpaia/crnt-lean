import CRNT.Dynamics.WeightedL1Contraction
import CRNT.Multistationarity.TwoReactionNondegenerate

/-!
# Weighted `ℓ¹` contraction where the Euclidean criterion fails

Species `X, Y` (indices `0, 1`), reactions `0 → X`, `X → Y`, `Y → 0` with rates `1, 8, 1`.
The mass-action Jacobian is constant, `[[−8, 0], [8, −1]]` (`jac_col0`, `jac_col1`).

* The weighted `ℓ¹` column condition holds with weights `(1, 1/2)` and rate `1`, so any two
  solutions satisfy `|x₀ − y₀| + |x₁ − y₁|/2 ≤ e^{−t} (…)(0)` (`contracts`).
* The weighted `ℓ^∞` row condition holds with weights `(1, 1/16)` and rate `1/2`
  (`contracts_linf`).
* The Euclidean logarithmic-norm criterion `⟨u, J u⟩ ≤ −c |u|²` fails for every `c ≥ 0`:
  `⟨u, J u⟩ = 8` for `u = (1, 4)` (`not_euclidean`).

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Examples
namespace L1Contraction

open Network Finset

/-- `0 → X`, `X → Y`, `Y → 0`. -/
abbrev net : Network (Fin 2) :=
  ⟨Fin 3, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨0, ![1, 0]⟩ else if r = 1 then ⟨![1, 0], ![0, 1]⟩ else ⟨![0, 1], 0⟩⟩

/-- Rates `1, 8, 1`. -/
def κ : net.RateConstants := ⟨![1, 8, 1], by intro r; fin_cases r <;> norm_num⟩

theorem erase0 : (univ.erase (0 : Fin 2)) = {1} := by decide
theorem erase1 : (univ.erase (1 : Fin 2)) = {0} := by decide

theorem jac_apply (x u : Concentration (Fin 2)) :
    net.massActionJacobianCLM κ x u = ![-8 * u 0, 8 * u 0 - u 1] := by
  rw [massActionJacobianCLM_apply_sum]
  funext i
  fin_cases i <;>
    simp [Fin.sum_univ_three, Fin.sum_univ_two, κ, massActionMonomialGrad, reactionVector_apply,
      erase0, erase1] <;> ring

theorem jac_col0 (x : Concentration (Fin 2)) :
    net.massActionJacobianCLM κ x (Pi.single 0 1) = ![-8, 8] := by
  rw [jac_apply]; funext i; fin_cases i <;> simp

theorem jac_col1 (x : Concentration (Fin 2)) :
    net.massActionJacobianCLM κ x (Pi.single 1 1) = ![0, -1] := by
  rw [jac_apply]; funext i; fin_cases i <;> simp

/-- The weights `(1, 1/2)`. -/
noncomputable def w : Fin 2 → ℝ := ![1, 1 / 2]

theorem hw : ∀ s, 0 < w s := by intro s; fin_cases s <;> norm_num [w]

theorem column_condition (x : Concentration (Fin 2)) (j : Fin 2) :
    w j * net.massActionJacobianCLM κ x (Pi.single j 1) j +
      ∑ i ∈ univ.erase j, w i * |net.massActionJacobianCLM κ x (Pi.single j 1) i| ≤ -1 * w j := by
  rcases (show ∀ q : Fin 2, q = 0 ∨ q = 1 by decide) j with rfl | rfl
  · rw [jac_col0]
    simp [erase0, w]
    norm_num
  · rw [jac_col1]
    simp [erase1, w]

/-- **Exponential contraction in the weighted `ℓ¹` distance.** -/
theorem contracts {x y : ℝ → Concentration (Fin 2)}
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (net.massActionVectorField κ (x t)) t)
    (hy : ∀ t, 0 ≤ t → HasDerivAt y (net.massActionVectorField κ (y t)) t) :
    ∀ t, 0 ≤ t → wl1Dist w (x t) (y t) ≤ Real.exp (-1 * t) * wl1Dist w (x 0) (y 0) :=
  net.massAction_l1_contraction κ convex_univ hw (fun x _ j => column_condition x j) hx hy
    (fun _ _ => Set.mem_univ _) (fun _ _ => Set.mem_univ _)

/-- **The Euclidean criterion fails** for every nonnegative rate. -/
theorem not_euclidean (c : ℝ) (hc : 0 ≤ c) :
    ¬ ∀ (x u : Concentration (Fin 2)),
      ∑ s, u s * net.massActionJacobianCLM κ x u s ≤ -c * ∑ s, u s ^ 2 := by
  intro h
  have := h 0 ![1, 4]
  rw [jac_apply] at this
  simp [Fin.sum_univ_two] at this
  nlinarith

/-- The weights `(1, 1/16)` for the row condition. -/
noncomputable def v : Fin 2 → ℝ := ![1, 1 / 16]

theorem hv : ∀ s, 0 < v s := by intro s; fin_cases s <;> norm_num [v]

theorem row_condition (x : Concentration (Fin 2)) (i : Fin 2) :
    net.massActionJacobianCLM κ x (Pi.single i 1) i +
      ∑ j ∈ univ.erase i, v i / v j * |net.massActionJacobianCLM κ x (Pi.single j 1) i| ≤
        -(1 / 2) := by
  rcases (show ∀ q : Fin 2, q = 0 ∨ q = 1 by decide) i with rfl | rfl
  · rw [jac_col0]
    simp [erase0, v, jac_col1]
    norm_num
  · rw [jac_col1]
    simp [erase1, v, jac_col0]
    norm_num

/-- **Exponential contraction in the weighted `ℓ^∞` distance**, rate `1/2`. -/
theorem contracts_linf {x y : ℝ → Concentration (Fin 2)}
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (net.massActionVectorField κ (x t)) t)
    (hy : ∀ t, 0 ≤ t → HasDerivAt y (net.massActionVectorField κ (y t)) t) :
    ∀ t, 0 ≤ t → wlinfDist v (x t) (y t) ≤ Real.exp (-(1 / 2) * t) * wlinfDist v (x 0) (y 0) :=
  net.massAction_linf_contraction κ convex_univ hv (fun x _ i => row_condition x i) hx hy
    (fun _ _ => Set.mem_univ _) (fun _ _ => Set.mem_univ _)

end L1Contraction
end Examples
end CRNT
