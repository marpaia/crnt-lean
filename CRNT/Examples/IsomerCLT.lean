import CRNT.Stochastic.NonlinearCLTTraj

/-!
# CLT instance along a moving trajectory: `X ⇌ Y`

For `X ⇌ Y` with unit rates, `x(t) = (1 + e^{−2t}, 1 − e^{−2t})` solves the mass-action equation
from `x(0) = (2, 0)` (`hasDerivAt_xsol`), `Df = [[−1, 1], [1, −1]]` everywhere (`jac_apply`), and
`θ(u) = e^{2(u − T)} (1, −1)` solves the adjoint equation (`adjoint`).  Started from `(2V, 0)`
molecules, the fluctuation `ζ_X − ζ_Y` around `x(T)` is asymptotically normal with variance
`2 (1 − e^{−4 T})`:

`E exp(i (ζ_X(T) − ζ_Y(T))) → exp(−(1 − e^{−4 T}))`  (`clt`).
-/

open Set Filter Complex
open scoped Topology

namespace CRNT
namespace Examples
namespace IsomerCLT

open Network

/-- `X → Y`, `Y → X`. -/
abbrev net : Network (Fin 2) :=
  ⟨Fin 2, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨![1, 0], ![0, 1]⟩ else ⟨![0, 1], ![1, 0]⟩⟩

def κ : RateConstants net := ⟨fun _ => 1, fun _ => one_pos⟩

def w : Fin 2 → ℝ := ![1, 1]

theorem w_inv : net.IsPInvariant w := by
  unfold IsPInvariant stoichSubspace
  refine mem_orthSum_span ?_
  rintro _ ⟨r, rfl⟩
  fin_cases r <;>
    simp [w, Fin.sum_univ_two, Network.reactionVector, Reaction.vector]

theorem w_pos : ∀ s, 0 < w s := by
  intro s; fin_cases s <;> simp [w]

theorem field_apply (z : Concentration (Fin 2)) :
    net.massActionVectorField κ z = ![-z 0 + z 1, z 0 - z 1] := by
  funext s
  fin_cases s <;>
    simp [massActionVectorField_apply, Fin.sum_univ_two, massActionRate, κ,
      Complex.massActionMonomial, Fin.prod_univ_two, Network.reactionVector, Reaction.vector] <;>
    ring

/-- The solution from `(2, 0)`. -/
noncomputable def xsol (t : ℝ) : Concentration (Fin 2) :=
  ![1 + Real.exp (-2 * t), 1 - Real.exp (-2 * t)]

theorem hasDerivAt_xsol (t : ℝ) :
    HasDerivAt xsol (net.massActionVectorField κ (xsol t)) t := by
  rw [field_apply, hasDerivAt_pi]
  have he : HasDerivAt (fun t : ℝ => Real.exp (-2 * t)) (Real.exp (-2 * t) * (-2)) t := by
    simpa using ((hasDerivAt_id t).const_mul (-2)).exp
  intro s
  fin_cases s
  · show HasDerivAt (fun t => 1 + Real.exp (-2 * t)) _ t
    convert he.const_add 1 using 1
    simp [xsol]; ring
  · show HasDerivAt (fun t => 1 - Real.exp (-2 * t)) _ t
    convert he.const_sub 1 using 1
    simp [xsol]; ring

theorem xsol_mem {t : ℝ} (ht : 0 ≤ t) : xsol t ∈ Icc (0 : Concentration (Fin 2)) fun _ => 2 := by
  have h1 : Real.exp (-(2 * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h0 := Real.exp_pos (-(2 * t))
  refine ⟨fun s => ?_, fun s => ?_⟩ <;> fin_cases s <;> simp [xsol] <;> linarith

/-- The Jacobian, at every point. -/
theorem jac_apply (z v : Fin 2 → ℝ) :
    fderiv ℝ (net.massActionVectorField κ) z v = ![-v 0 + v 1, v 0 - v 1] := by
  set f := net.massActionVectorField κ with hf
  have hD : HasFDerivAt f (fderiv ℝ f z) z :=
    ((net.contDiff_massActionVectorField κ).differentiable (by simp) z).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have hD' : HasFDerivAt f (fderiv ℝ f z) (z + (0 : ℝ) • v) := by simpa using hD
  have h1 : HasDerivAt (fun t : ℝ => f (z + t • v)) (fderiv ℝ f z v) (0 : ℝ) := by
    have := HasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => z + t • v) (0 : ℝ) hD' hline
    exact this
  have h2 : HasDerivAt (fun t : ℝ => f (z + t • v)) ![-v 0 + v 1, v 0 - v 1] (0 : ℝ) := by
    have hfun : (fun t : ℝ => f (z + t • v)) =
        fun t => ![-(z 0 + t * v 0) + (z 1 + t * v 1), (z 0 + t * v 0) - (z 1 + t * v 1)] := by
      funext t
      rw [hf, field_apply]
      simp
    rw [hfun, hasDerivAt_pi]
    intro s
    have ha : HasDerivAt (fun t : ℝ => z 0 + t * v 0) (v 0) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v 0)).const_add (z 0)
    have hb : HasDerivAt (fun t : ℝ => z 1 + t * v 1) (v 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v 1)).const_add (z 1)
    fin_cases s
    · exact ha.neg.add hb
    · exact ha.sub hb
  exact h1.unique h2

/-- The adjoint solution `θ(u) = e^{2(u − T)} (1, −1)`. -/
noncomputable def θf (T u : ℝ) : Fin 2 → ℝ := fun s => Real.exp (2 * (u - T)) * ![1, -1] s

noncomputable def θf' (T u : ℝ) : Fin 2 → ℝ := fun s => 2 * Real.exp (2 * (u - T)) * ![1, -1] s

theorem hasDerivAt_θf (T u : ℝ) : HasDerivAt (θf T) (θf' T u) u := by
  rw [hasDerivAt_pi]
  intro s
  have h : HasDerivAt (fun u : ℝ => Real.exp (2 * (u - T))) (Real.exp (2 * (u - T)) * 2) u := by
    have := ((hasDerivAt_id u).sub_const T).const_mul 2
    simpa using this.exp
  have := h.mul_const (![1, -1] s)
  have e : θf' T u s = Real.exp (2 * (u - T)) * 2 * ![1, -1] s := by
    show 2 * Real.exp (2 * (u - T)) * ![1, -1] s = _
    ring
  rw [e]
  exact this

theorem adjoint (T u : ℝ) (v : Fin 2 → ℝ) :
    ∑ s, θf' T u s * v s =
      -∑ s, θf T u s * fderiv ℝ (net.massActionVectorField κ) (xsol u) v s := by
  rw [jac_apply]
  simp [θf, θf', Fin.sum_univ_two]
  ring

theorem quadG_θf (T u : ℝ) : net.quadG κ (xsol u) (θf T u) = 8 * Real.exp (4 * (u - T)) := by
  simp [quadG, θf, xsol, Fin.sum_univ_two, massActionRate, κ, Complex.massActionMonomial,
    Network.reactionVector, Reaction.vector]
  have : Real.exp (4 * (u - T)) = Real.exp (2 * (u - T)) ^ 2 := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [this]; ring

theorem integral_quadG (T : ℝ) :
    ∫ u in (0 : ℝ)..T, net.quadG κ (xsol u) (θf T u) = 2 * (1 - Real.exp (-4 * T)) := by
  simp_rw [quadG_θf]
  have hder : ∀ u ∈ Set.uIcc 0 T, HasDerivAt (fun u : ℝ => 2 * Real.exp (4 * (u - T)))
      (8 * Real.exp (4 * (u - T))) u := by
    intro u _
    have h0 : HasDerivAt (fun u : ℝ => 4 * (u - T)) 4 u := by
      simpa using ((hasDerivAt_id u).sub_const T).const_mul 4
    have := h0.exp.const_mul 2
    convert this using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder
    ((by fun_prop : Continuous fun u : ℝ => 8 * Real.exp (4 * (u - T))).intervalIntegrable _ _)]
  simp
  ring_nf

/-- **CLT along the trajectory for `X ⇌ Y`.** Started from `(2V, 0)` molecules at volume
`V = k + 1`, `E exp(i (ζ_X(T) − ζ_Y(T))) → exp(−(1 − e^{−4 T}))`, with the fluctuation
`ζ = √V (X^V(T)/V − x(T))` centred at the moving solution. -/
theorem clt {T : ℝ} (hT : 0 < T) :
    Tendsto (fun k : ℕ => ∑' m, (net.transition (net.volumeScale κ ((k : ℝ) + 1) (by positivity))
        T ![2 * (k + 1), 0] m : ℂ) *
          Complex.exp (I * ((zeta ((k : ℝ) + 1) (xsol T) m 0 -
            zeta ((k : ℝ) + 1) (xsol T) m 1 : ℝ) : ℂ))) atTop
      (𝓝 (Complex.exp ((-(1 - Real.exp (-4 * T)) : ℝ) : ℂ))) := by
  have hz : Tendsto (fun k : ℕ => zeta ((k : ℝ) + 1) (xsol 0) ![2 * (k + 1), 0]) atTop (𝓝 0) := by
    have : ∀ k : ℕ, zeta ((k : ℝ) + 1) (xsol 0) ![2 * (k + 1), 0] = 0 := by
      intro k; funext s
      have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
      have h2 : ((2 * (k + 1) : ℕ) : ℝ) / ((k : ℝ) + 1) = 2 := by
        push_cast; field_simp
      fin_cases s
      · show Real.sqrt ((k : ℝ) + 1) * (((2 * (k + 1) : ℕ) : ℝ) / ((k : ℝ) + 1) -
          (1 + Real.exp (-2 * 0))) = 0
        rw [h2]; norm_num
      · show Real.sqrt ((k : ℝ) + 1) * (((0 : ℕ) : ℝ) / ((k : ℝ) + 1) -
          (1 - Real.exp (-2 * 0))) = 0
        simp
    simp only [this]; exact tendsto_const_nhds
  have h := nonlinear_clt_traj net κ w_inv w_pos (M := 2) (Rx := 2) (by norm_num) hT
    (by norm_num) xsol (fun t _ => (hasDerivAt_xsol t).continuousAt.continuousWithinAt)
    (fun t _ => hasDerivAt_xsol t) (fun t ht => xsol_mem ht.1) (θf T) (θf' T)
    (fun u _ => (hasDerivAt_θf T u).continuousAt.continuousWithinAt)
    (fun u _ => hasDerivAt_θf T u) (fun u _ v => adjoint T u v) (fun k => ![2 * (k + 1), 0])
    (fun k => by simp [w, Fin.sum_univ_two]) hz
  have hθT : ∀ s, θf T T s = ![1, -1] s := fun s => by simp [θf]
  have hlhs : ∀ (k : ℕ) (m : Fin 2 → ℕ), ∑ s, θf T T s * zeta ((k : ℝ) + 1) (xsol T) m s =
      zeta ((k : ℝ) + 1) (xsol T) m 0 - zeta ((k : ℝ) + 1) (xsol T) m 1 := fun k m => by
    simp [hθT, Fin.sum_univ_two]; ring
  simp_rw [hlhs] at h
  rw [integral_quadG] at h
  convert h using 2
  simp

end IsomerCLT
end Examples
end CRNT
