import CRNT.Stochastic.KurtzScaling
import CRNT.Kinetics.MassActionJacobian
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Diffusion approximation and linear noise approximation: generator level

Kurtz's central limit theorem (Kurtz 1971, "Limit theorems for sequences of jump Markov processes
approximating ordinary differential processes"; Kurtz 1976; Anderson–Kurtz 2015, ch. 4) and the
chemical Langevin equation (Gillespie 2000) refine the law of large numbers of
`CRNT.Stochastic.KurtzScaling` to second order. This module proves the generator-level statements
behind both.

Notation: `A^V f (x) = ∑_r V κ_r x^{y_r} (f(x + v_r/V) − f(x))` is the volume-scaled generator
(`Network.scaledGenerator`), `F` the mass-action field, `λ_r(x) = κ_r x^{y_r}`.

* `tendsto_secondOrder_slope`: for `f` differentiable everywhere with derivative `f'` that is
  differentiable at `x` with derivative `f''`,
  `(f(x + h w) − f(x) − h f'(x) w) / h² → ½ f''(x) w w` as `h → 0⁺`.
* `Network.tendsto_volume_mul_scaledGenerator_sub_drift`: the error of the law-of-large-numbers
  generator is of order exactly `1/V`:
  `V · (A^V f(x) − f'(x)(F(x))) → ½ ∑_r λ_r(x) f''(x)(v_r, v_r)`.
* `Network.langevinGenerator` and `Network.tendsto_volume_mul_scaledGenerator_sub_langevin`: the
  generator `f'(x)(F(x)) + (2V)⁻¹ ∑_r λ_r(x) f''(x)(v_r, v_r)` of the chemical Langevin
  (diffusion) approximation agrees with `A^V f(x)` up to `o(1/V)`.
* `Network.fluctuationGenerator` and `Network.tendsto_fluctuationGenerator`: for the fluctuation
  `U = √V (X − φ)` around a point `φ` of the deterministic flow, the generator
  `∑_r V λ_r(φ + U/√V) (g(U + v_r/√V) − g(U)) − √V g'(U)(F(φ))` converges to the generator of
  the linear noise approximation (an Ornstein–Uhlenbeck operator)
  `g'(u)(DF(φ) u) + ½ ∑_r λ_r(φ) g''(u)(v_r, v_r)` (`Network.linearNoiseGenerator`).

Not formalized: the process-level statements (weak convergence of the fluctuation process to the
Gaussian diffusion, the strong approximation of Kurtz 1978). They need martingale central limit
theorems, which Mathlib lacks.
-/

namespace CRNT

open Filter Topology Asymptotics Set

open scoped BigOperators

section SecondOrder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Second-order expansion along a direction.** If `f` has derivative `f' y` at every `y` and
`f'` has derivative `f''` at `x`, then
`(f(x + h • w) − f(x) − h · f'(x) w) / h² → ½ f''(x) w w` as `h → 0⁺`. -/
theorem tendsto_secondOrder_slope {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {f'' : E →L[ℝ] E →L[ℝ] ℝ}
    {x : E} (hf : ∀ y, HasFDerivAt f (f' y) y) (hx : HasFDerivAt f' f'' x) (w : E) :
    Tendsto (fun h : ℝ => (f (x + h • w) - f x - h * f' x w) / h ^ 2) (𝓝[>] 0)
      (𝓝 ((1 / 2) * f'' w w)) := by
  have hT := Convex.taylor_approx_two_segment (s := univ) convex_univ
    (fun y _ => hf y) (mem_univ x) hx.hasFDerivWithinAt (v := 0) (w := w)
    (by simp) (by simp)
  have hT' : (fun h : ℝ => f (x + h • w) - f x - h * f' x w - h ^ 2 / 2 * f'' w w) =o[𝓝[>] 0]
      fun h => h ^ 2 := by
    refine hT.congr_left fun h => ?_
    simp [smul_eq_mul]
  have hlim := hT'.tendsto_div_nhds_zero
  have : Tendsto (fun h : ℝ => (f (x + h • w) - f x - h * f' x w - h ^ 2 / 2 * f'' w w) / h ^ 2
      + (1 / 2) * f'' w w) (𝓝[>] 0) (𝓝 (0 + (1 / 2) * f'' w w)) :=
    hlim.add_const _
  rw [zero_add] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
  have : h ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- **Second-order expansion along the scaled increment `w/V`.**
`V² (f(x + V⁻¹ • w) − f(x)) − V · f'(x) w → ½ f''(x) w w` as `V → ∞`. -/
theorem tendsto_volume_sq_mul_sub {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {f'' : E →L[ℝ] E →L[ℝ] ℝ}
    {x : E} (hf : ∀ y, HasFDerivAt f (f' y) y) (hx : HasFDerivAt f' f'' x) (w : E) :
    Tendsto (fun V : ℝ => V ^ 2 * (f (x + V⁻¹ • w) - f x) - V * f' x w) atTop
      (𝓝 ((1 / 2) * f'' w w)) := by
  have h := (tendsto_secondOrder_slope hf hx w).comp tendsto_inv_atTop_nhdsGT_zero
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with V hV
  simp only [Function.comp_apply]
  have hV0 : V ≠ 0 := hV.ne'
  field_simp

end SecondOrder

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The derivative of an observable along the mass-action field, reaction by reaction. -/
theorem fderiv_apply_massActionVectorField (N : Network S) (κ : RateConstants N)
    (L : Concentration S →L[ℝ] ℝ) (x : Concentration S) :
    L (N.massActionVectorField κ x) = ∑ r : N.R, N.massActionRate κ r x * L (N.reactionVector r) := by
  have hsum : N.massActionVectorField κ x =
      ∑ r : N.R, N.massActionRate κ r x • N.reactionVector r := by
    funext s
    simp [massActionVectorField, Finset.sum_apply, smul_eq_mul]
  rw [hsum, map_sum]
  exact Finset.sum_congr rfl fun r _ => by rw [map_smul, smul_eq_mul]

/-- **The law-of-large-numbers generator error is of order `1/V`.** For an observable `f`
differentiable everywhere, twice at `x`,
`V · (A^V f(x) − f'(x)(F(x))) → ½ ∑_r λ_r(x) f''(x)(v_r, v_r)`. -/
theorem tendsto_volume_mul_scaledGenerator_sub_drift (N : Network S) (κ : RateConstants N)
    {f : Concentration S → ℝ} {f' : Concentration S → Concentration S →L[ℝ] ℝ}
    {f'' : Concentration S →L[ℝ] Concentration S →L[ℝ] ℝ} {x : Concentration S}
    (hf : ∀ y, HasFDerivAt f (f' y) y) (hx : HasFDerivAt f' f'' x) :
    Tendsto (fun V : ℝ => V * (N.scaledGenerator κ V f x - f' x (N.massActionVectorField κ x)))
      atTop (𝓝 ((1 / 2) * ∑ r : N.R, N.massActionRate κ r x *
        f'' (N.reactionVector r) (N.reactionVector r))) := by
  have hterm : ∀ r : N.R, Tendsto (fun V : ℝ => N.massActionRate κ r x *
      (V ^ 2 * (f (x + V⁻¹ • N.reactionVector r) - f x) - V * f' x (N.reactionVector r))) atTop
      (𝓝 (N.massActionRate κ r x * ((1 / 2) * f'' (N.reactionVector r) (N.reactionVector r)))) :=
    fun r => (tendsto_volume_sq_mul_sub hf hx (N.reactionVector r)).const_mul _
  have hsum := tendsto_finsetSum (Finset.univ : Finset N.R) fun r _ => hterm r
  rw [Finset.mul_sum]
  refine (hsum.congr fun V => ?_).congr (fun _ => rfl) |>.mono_right (le_of_eq ?_)
  · rw [fderiv_apply_massActionVectorField, scaledGenerator, mul_sub, Finset.mul_sum,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [densityScaledRate_apply]
    ring
  · congr 1
    exact Finset.sum_congr rfl fun r _ => by ring

/-- **The chemical Langevin (diffusion) generator** at volume `V`, written with the first and
second derivatives `L`, `Q` of the observable at `x`:
`L(F(x)) + (2V)⁻¹ ∑_r λ_r(x) Q(v_r, v_r)`. It is the generator of the diffusion
`dX = F(X) dt + V^{-1/2} ∑_r √λ_r(X) v_r dW_r`. -/
noncomputable def langevinGenerator (N : Network S) (κ : RateConstants N) (V : ℝ)
    (L : Concentration S →L[ℝ] ℝ) (Q : Concentration S →L[ℝ] Concentration S →L[ℝ] ℝ)
    (x : Concentration S) : ℝ :=
  L (N.massActionVectorField κ x) +
    (2 * V)⁻¹ * ∑ r : N.R, N.massActionRate κ r x * Q (N.reactionVector r) (N.reactionVector r)

/-- **The chemical Langevin generator matches the jump generator to order `o(1/V)`.**
`V · (A^V f(x) − L^V_{CLE} f(x)) → 0`, whereas the drift alone leaves the error of
`tendsto_volume_mul_scaledGenerator_sub_drift`. -/
theorem tendsto_volume_mul_scaledGenerator_sub_langevin (N : Network S) (κ : RateConstants N)
    {f : Concentration S → ℝ} {f' : Concentration S → Concentration S →L[ℝ] ℝ}
    {f'' : Concentration S →L[ℝ] Concentration S →L[ℝ] ℝ} {x : Concentration S}
    (hf : ∀ y, HasFDerivAt f (f' y) y) (hx : HasFDerivAt f' f'' x) :
    Tendsto (fun V : ℝ => V * (N.scaledGenerator κ V f x - N.langevinGenerator κ V (f' x) f'' x))
      atTop (𝓝 0) := by
  have h := (N.tendsto_volume_mul_scaledGenerator_sub_drift κ hf hx).sub_const
    ((1 / 2) * ∑ r : N.R, N.massActionRate κ r x * f'' (N.reactionVector r) (N.reactionVector r))
  rw [sub_self] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with V hV
  simp only [langevinGenerator]
  field_simp
  ring

/-- **Generator of the fluctuation process** `U = √V (X − φ)` around a point `φ` of the
deterministic flow, acting on an observable `g` with derivative `g'`:
`∑_r V λ_r(φ + U/√V) (g(U + v_r/√V) − g(U)) − √V g'(U)(F(φ))`. The last term is the
contribution of the moving centre `φ̇ = F(φ)`. -/
noncomputable def fluctuationGenerator (N : Network S) (κ : RateConstants N) (V : ℝ)
    (φ : Concentration S) (g : Concentration S → ℝ) (g' : Concentration S →L[ℝ] ℝ)
    (u : Concentration S) : ℝ :=
  ∑ r : N.R, V * N.massActionRate κ r (φ + (Real.sqrt V)⁻¹ • u) *
      (g (u + (Real.sqrt V)⁻¹ • N.reactionVector r) - g u)
    - Real.sqrt V * g' (N.massActionVectorField κ φ)

/-- **The linear noise approximation generator** at `φ`: the Ornstein–Uhlenbeck operator
`g'(u)(DF(φ) u) + ½ ∑_r λ_r(φ) g''(u)(v_r, v_r)`, with drift matrix the Jacobian `DF(φ)` and
diffusion matrix `∑_r λ_r(φ) v_r v_rᵀ`. -/
noncomputable def linearNoiseGenerator (N : Network S) (κ : RateConstants N) (φ : Concentration S)
    (g' : Concentration S →L[ℝ] ℝ) (g'' : Concentration S →L[ℝ] Concentration S →L[ℝ] ℝ)
    (u : Concentration S) : ℝ :=
  g' (fderiv ℝ (fun x => N.massActionVectorField κ x) φ u) +
    (1 / 2) * ∑ r : N.R, N.massActionRate κ r φ * g'' (N.reactionVector r) (N.reactionVector r)

/-- The Jacobian of the mass-action field, reaction by reaction:
`DF(φ) u = ∑_r (Dλ_r(φ) u) v_r`. -/
theorem fderiv_massActionVectorField_apply (N : Network S) (κ : RateConstants N)
    (φ u : Concentration S) :
    fderiv ℝ (fun x => N.massActionVectorField κ x) φ u =
      ∑ r : N.R, fderiv ℝ (fun x => N.massActionRate κ r x) φ u • N.reactionVector r := by
  have hfun : (fun x : Concentration S => N.massActionVectorField κ x)
      = fun x => ∑ r : N.R, N.massActionRate κ r x • N.reactionVector r := by
    funext x s
    simp only [massActionVectorField, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hd : HasFDerivAt (fun x : Concentration S => ∑ r : N.R,
      N.massActionRate κ r x • N.reactionVector r)
      (∑ r : N.R, (fderiv ℝ (fun x => N.massActionRate κ r x) φ).smulRight (N.reactionVector r))
      φ := by
    apply HasFDerivAt.fun_sum
    intro r _
    exact ((N.massActionRate_differentiable κ r) φ).hasFDerivAt.smul_const _
  rw [hfun, hd.fderiv, sum_apply]
  rfl

/-- **Linear noise approximation (Kurtz's CLT), generator level.** For an observable `g`
differentiable everywhere, twice at `u`, the generator of the fluctuation `√V (X − φ)` converges
to the Ornstein–Uhlenbeck generator of the linear noise approximation:
`fluctuationGenerator V φ g (g' u) u → linearNoiseGenerator φ (g' u) g'' u` as `V → ∞`. -/
theorem tendsto_fluctuationGenerator (N : Network S) (κ : RateConstants N) (φ : Concentration S)
    {g : Concentration S → ℝ} {g' : Concentration S → Concentration S →L[ℝ] ℝ}
    {g'' : Concentration S →L[ℝ] Concentration S →L[ℝ] ℝ} {u : Concentration S}
    (hg : ∀ y, HasFDerivAt g (g' y) y) (hu : HasFDerivAt g' g'' u) :
    Tendsto (fun V : ℝ => N.fluctuationGenerator κ V φ g (g' u) u) atTop
      (𝓝 (N.linearNoiseGenerator κ φ (g' u) g'' u)) := by
  -- the expansion in `h = 1/√V`
  set R : N.R → ℝ → ℝ := fun r h => N.massActionRate κ r (φ + h • u) with hR
  set D : N.R → ℝ := fun r => fderiv ℝ (fun x => N.massActionRate κ r x) φ u with hD
  have hρ : ∀ r, Tendsto (fun h : ℝ => h⁻¹ * (R r h - R r 0)) (𝓝[>] 0) (𝓝 (D r)) := by
    intro r
    have hline := (((N.massActionRate_differentiable κ r) φ).hasFDerivAt).hasLineDerivAt u
    have := hline.tendsto_slope_zero_right
    refine this.congr fun h => ?_
    simp [hR, smul_eq_mul]
  have hσ : ∀ r, Tendsto (fun h : ℝ => (g (u + h • N.reactionVector r) - g u
      - h * g' u (N.reactionVector r)) / h ^ 2) (𝓝[>] 0)
      (𝓝 ((1 / 2) * g'' (N.reactionVector r) (N.reactionVector r))) :=
    fun r => tendsto_secondOrder_slope hg hu _
  have hterm : ∀ r, Tendsto (fun h : ℝ =>
      R r 0 * ((g (u + h • N.reactionVector r) - g u - h * g' u (N.reactionVector r)) / h ^ 2)
      + h⁻¹ * (R r h - R r 0) * g' u (N.reactionVector r)
      + h * (h⁻¹ * (R r h - R r 0)) *
          ((g (u + h • N.reactionVector r) - g u - h * g' u (N.reactionVector r)) / h ^ 2))
      (𝓝[>] 0)
      (𝓝 (R r 0 * ((1 / 2) * g'' (N.reactionVector r) (N.reactionVector r))
        + D r * g' u (N.reactionVector r)
        + 0 * D r * ((1 / 2) * g'' (N.reactionVector r) (N.reactionVector r)))) := by
    intro r
    have hh : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    exact (((hσ r).const_mul _).add ((hρ r).mul_const _)).add ((hh.mul (hρ r)).mul (hσ r))
  have hsum := tendsto_finsetSum (Finset.univ : Finset N.R) fun r _ => hterm r
  -- the limit value
  have hval : ∑ r : N.R, (R r 0 * ((1 / 2) * g'' (N.reactionVector r) (N.reactionVector r))
        + D r * g' u (N.reactionVector r)
        + 0 * D r * ((1 / 2) * g'' (N.reactionVector r) (N.reactionVector r)))
      = N.linearNoiseGenerator κ φ (g' u) g'' u := by
    rw [linearNoiseGenerator, fderiv_massActionVectorField_apply, map_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [hR, hD, zero_smul, add_zero, map_smul, smul_eq_mul]
    ring
  rw [hval] at hsum
  -- pull back along `V ↦ 1/√V`
  have hinv : Tendsto (fun V : ℝ => (Real.sqrt V)⁻¹) atTop (𝓝[>] 0) := by
    exact tendsto_inv_atTop_nhdsGT_zero.comp Real.tendsto_sqrt_atTop
  refine (hsum.comp hinv).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with V hV
  simp only [Function.comp_apply]
  have hs : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV
  have hsq : Real.sqrt V ^ 2 = V := Real.sq_sqrt hV.le
  have hh0 : (Real.sqrt V)⁻¹ ≠ 0 := inv_ne_zero hs.ne'
  have hh2 : ((Real.sqrt V)⁻¹ ^ 2)⁻¹ = V := by rw [inv_pow, inv_inv, hsq]
  have key : ∀ (R0 Rh G a : ℝ), R0 * ((G - (Real.sqrt V)⁻¹ * a) / (Real.sqrt V)⁻¹ ^ 2)
      + (Real.sqrt V)⁻¹⁻¹ * (Rh - R0) * a
      + (Real.sqrt V)⁻¹ * ((Real.sqrt V)⁻¹⁻¹ * (Rh - R0)) *
          ((G - (Real.sqrt V)⁻¹ * a) / (Real.sqrt V)⁻¹ ^ 2)
      = ((Real.sqrt V)⁻¹ ^ 2)⁻¹ * Rh * G - (Real.sqrt V)⁻¹⁻¹ * R0 * a := by
    intro R0 Rh G a
    field_simp
    ring
  rw [fluctuationGenerator, fderiv_apply_massActionVectorField, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [hR, zero_smul, add_zero]
  rw [key, hh2, inv_inv]
  ring

end Network

end CRNT
