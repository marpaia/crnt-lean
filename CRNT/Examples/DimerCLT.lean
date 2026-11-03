import CRNT.Stochastic.NonlinearCLT

/-!
# CLT instance: `2X ⇌ Y` at the equilibrium `(1, 1)`

For `2X ⇌ Y` with unit rates (`CRNT.Examples.Dimerization`), `Df(1, 1) = [[−4, 2], [2, −1]]`
(`jac_apply`), and `θ(u) = e^{5(u − T)} (2, −1)` solves the adjoint equation (`adjoint`).
Started from `(V, V)` molecules, the fluctuation `2 ζ_X − ζ_Y` at time `T` is asymptotically
normal with variance `5 (1 − e^{−10 T})`:

`E exp(i (2 ζ_X(T) − ζ_Y(T))) → exp(−(5/2)(1 − e^{−10 T}))`  (`clt`).
-/

open Set Filter Complex
open scoped Topology

namespace CRNT
namespace Examples
namespace DimerCLT

open Network Dimerization

/-- The Jacobian at `(1, 1)`. -/
theorem jac_apply (v : Fin 2 → ℝ) :
    fderiv ℝ (net.massActionVectorField κ) xstar v = ![-4 * v 0 + 2 * v 1, 2 * v 0 - v 1] := by
  set f := net.massActionVectorField κ with hf
  have hD : HasFDerivAt f (fderiv ℝ f xstar) xstar :=
    ((net.contDiff_massActionVectorField κ).differentiable (by simp) xstar).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => xstar + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add xstar
  have hD' : HasFDerivAt f (fderiv ℝ f xstar) (xstar + (0 : ℝ) • v) := by simpa using hD
  have h1 : HasDerivAt (fun t : ℝ => f (xstar + t • v)) (fderiv ℝ f xstar v) (0 : ℝ) := by
    have := HasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => xstar + t • v) (0 : ℝ) hD' hline
    exact this
  have h2 : HasDerivAt (fun t : ℝ => f (xstar + t • v)) ![-4 * v 0 + 2 * v 1, 2 * v 0 - v 1]
      (0 : ℝ) := by
    rw [hasDerivAt_pi]
    intro s
    fin_cases s
    · show HasDerivAt (fun t : ℝ => f (xstar + t • v) 0) (-4 * v 0 + 2 * v 1) 0
      have hfun : (fun t : ℝ => f (xstar + t • v) 0) =
          fun t => -((1 + t * v 0) ^ 2 * 2) + (1 + t * v 1) * 2 := by
        funext t
        simp [hf, massActionVectorField_apply, Fin.sum_univ_two, massActionRate, κ, xstar,
          Complex.massActionMonomial, Fin.prod_univ_two, Network.reactionVector, Reaction.vector]
      rw [hfun]
      have ha : HasDerivAt (fun t : ℝ => 1 + t * v 0) (v 0) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v 0)).const_add 1
      have hb : HasDerivAt (fun t : ℝ => 1 + t * v 1) (v 1) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v 1)).const_add 1
      convert ((ha.pow 2).mul_const 2).neg.add (hb.mul_const 2) using 1
      simp; ring
    · show HasDerivAt (fun t : ℝ => f (xstar + t • v) 1) (2 * v 0 - v 1) 0
      have hfun : (fun t : ℝ => f (xstar + t • v) 1) =
          fun t => (1 + t * v 0) ^ 2 + -(1 + t * v 1) := by
        funext t
        simp [hf, massActionVectorField_apply, Fin.sum_univ_two, massActionRate, κ, xstar,
          Complex.massActionMonomial, Fin.prod_univ_two, Network.reactionVector, Reaction.vector]
      rw [hfun]
      have ha : HasDerivAt (fun t : ℝ => 1 + t * v 0) (v 0) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v 0)).const_add 1
      have hb : HasDerivAt (fun t : ℝ => 1 + t * v 1) (v 1) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v 1)).const_add 1
      convert (ha.pow 2).add hb.neg using 1
      simp; ring
  exact h1.unique h2

/-- The adjoint solution `θ(u) = e^{5(u − T)} (2, −1)`. -/
noncomputable def θf (T u : ℝ) : Fin 2 → ℝ := fun s => Real.exp (5 * (u - T)) * ![2, -1] s

noncomputable def θf' (T u : ℝ) : Fin 2 → ℝ := fun s => 5 * Real.exp (5 * (u - T)) * ![2, -1] s

theorem hasDerivAt_θf (T u : ℝ) : HasDerivAt (θf T) (θf' T u) u := by
  rw [hasDerivAt_pi]
  intro s
  have h : HasDerivAt (fun u : ℝ => Real.exp (5 * (u - T))) (Real.exp (5 * (u - T)) * 5) u := by
    have := ((hasDerivAt_id u).sub_const T).const_mul 5
    simpa using this.exp
  have := h.mul_const (![2, -1] s)
  have e : θf' T u s = Real.exp (5 * (u - T)) * 5 * ![2, -1] s := by
    show 5 * Real.exp (5 * (u - T)) * ![2, -1] s = _
    ring
  rw [e]
  exact this

theorem adjoint (T u : ℝ) (v : Fin 2 → ℝ) :
    ∑ s, θf' T u s * v s = -∑ s, θf T u s * fderiv ℝ (net.massActionVectorField κ) xstar v s := by
  rw [jac_apply]
  simp [θf, θf', Fin.sum_univ_two]
  ring

theorem quadG_θf (T u : ℝ) : net.quadG κ xstar (θf T u) = 50 * Real.exp (10 * (u - T)) := by
  simp [quadG, θf, Fin.sum_univ_two, massActionRate, κ, xstar, Complex.massActionMonomial,
    Network.reactionVector, Reaction.vector]
  have : Real.exp (10 * (u - T)) = Real.exp (5 * (u - T)) ^ 2 := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [this]; ring

theorem integral_quadG (T : ℝ) :
    ∫ u in (0 : ℝ)..T, net.quadG κ xstar (θf T u) = 5 * (1 - Real.exp (-10 * T)) := by
  simp_rw [quadG_θf]
  have hder : ∀ u ∈ Set.uIcc 0 T, HasDerivAt (fun u : ℝ => 5 * Real.exp (10 * (u - T)))
      (50 * Real.exp (10 * (u - T))) u := by
    intro u _
    have h0 : HasDerivAt (fun u : ℝ => 10 * (u - T)) 10 u := by
      simpa using ((hasDerivAt_id u).sub_const T).const_mul 10
    have := h0.exp.const_mul 5
    convert this using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder
    ((by fun_prop : Continuous fun u : ℝ => 50 * Real.exp (10 * (u - T))).intervalIntegrable _ _)]
  simp
  ring_nf

/-- **CLT for `2X ⇌ Y`.** Started from `(V, V)` molecules at volume `V = k + 1`,
`E exp(i (2 ζ_X(T) − ζ_Y(T))) → exp(−(5/2)(1 − e^{−10 T}))`: the fluctuation `2 ζ_X − ζ_Y` is
asymptotically `N(0, 5 (1 − e^{−10 T}))`. -/
theorem clt {T : ℝ} (hT : 0 < T) :
    Tendsto (fun k : ℕ => ∑' m, (net.transition (net.volumeScale κ ((k : ℝ) + 1) (by positivity))
        T (fun _ => k + 1) m : ℂ) *
          Complex.exp (I * ((2 * zeta ((k : ℝ) + 1) xstar m 0 -
            zeta ((k : ℝ) + 1) xstar m 1 : ℝ) : ℂ))) atTop
      (𝓝 (Complex.exp ((-(5 / 2) * (1 - Real.exp (-10 * T)) : ℝ) : ℂ))) := by
  have hz : Tendsto (fun k : ℕ => zeta ((k : ℝ) + 1) xstar (fun _ => k + 1)) atTop (𝓝 0) := by
    have : ∀ k : ℕ, zeta ((k : ℝ) + 1) xstar (fun _ => k + 1) = 0 := by
      intro k; funext s
      have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
      simp [zeta, xstar, hk]
    simp only [this]; exact tendsto_const_nhds
  have h := nonlinear_clt net κ w_inv w_pos equilibrium (fun _ => zero_le_one) (M := 3)
    (by norm_num) hT (θf T) (θf' T) (hasDerivAt_θf T) (fun u _ v => adjoint T u v)
    (fun k _ => k + 1) (fun k => by simp [w, Fin.sum_univ_two]; linarith) hz
  have hθT : ∀ s, θf T T s = ![2, -1] s := fun s => by simp [θf]
  have hlhs : ∀ (k : ℕ) (m : Fin 2 → ℕ), ∑ s, θf T T s * zeta ((k : ℝ) + 1) xstar m s =
      2 * zeta ((k : ℝ) + 1) xstar m 0 - zeta ((k : ℝ) + 1) xstar m 1 := fun k m => by
    simp [hθT, Fin.sum_univ_two]; ring
  simp_rw [hlhs] at h
  rw [integral_quadG] at h
  convert h using 2
  simp
  ring_nf

end DimerCLT
end Examples
end CRNT
