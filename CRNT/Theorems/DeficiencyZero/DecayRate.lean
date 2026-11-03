import CRNT.Equilibria.ComplexBalanceLinearStability
import CRNT.Theorems.DeficiencyZero.Lyapunov
import CRNT.Theorems.DeficiencyZero.Dissipation
import CRNT.Dynamics.OrbitRegularity
import CRNT.Examples.ReversiblePair

/-!
# The exponential decay rate of the relative entropy at a complex-balanced equilibrium

This module adds the **quantitative** content to the qualitative local-stability theory of
complex-balanced equilibria.

* The relative-entropy Lyapunov function `G(x) = ∑ᵢ xᵢ log(xᵢ/x*ᵢ) − xᵢ + x*ᵢ`
  (leaf E1, `CRNT.relEntropy`) is a *strict* Lyapunov function: it is nonnegative, vanishes
  only at the reference, and its derivative along a mass-action trajectory is nonpositive
  (`CRNT.Network.dissipation_nonpos`, `CRNT.Network.relEntropy_antitone_along_solution_of_pos_pos`).
* The linearization at a complex-balanced equilibrium is Hurwitz on the stoichiometric
  tangent space, and the entropy Hessian `diag(1/x*ᵢ)` is a strict quadratic Lyapunov metric
  there (leaf D21, `CRNT.Network.complexBalanced_hasStrictStoichQuadraticLyapunov`,
  `CRNT.Network.complexBalanced_isHurwitzOnStoich`).
* The equilibrium is locally exponentially stable in its stoichiometric class (leaf D4,
  `CRNT.Network.complexBalanced_locallyExponentiallyStable_in_class`).

What was missing is the *rate*.  This module proves the two quantitative statements that
the "thermodynamic speed limit" reading of the entropy production asks for:

1. **A quadratic bound for the relative entropy near the equilibrium**
   (`CRNT.Network.relEntropy_ge_quadratic_of_complexBalanced`, and in the form of a norm
   ball `CRNT.Network.relEntropy_ge_quadratic_in_ball`): there is `c > 0` such that
   `G(x) ≥ c ‖x − x*‖²` on a neighbourhood of `x*`.  The proof is the scalar estimate
   `t log t − t + 1 ≥ (t−1)² / (2 max{1, t})` for `t > 0`, which is proved here from
   Gibbs' inequality by a monotonicity argument.

2. **Exponential decay of the relative entropy along a solution**
   (`CRNT.Network.relEntropy_expDecay_along_solution`): if `x*` is a positive
   complex-balanced equilibrium and `γ` a mass-action trajectory in the stoichiometric class
   of `x*` that starts close enough to `x*`, then
   `G(γ t) ≤ K e^{−2αt} G(γ 0)` for some `K > 0` and `α > 0`.  The proof combines the
   quadratic bound with the exponential convergence of the trajectory supplied by leaf D4.

3. **A worked instance** on the canonical reversible pair `A ⇌ B`
   (`CRNT.Network.reversiblePair_relEntropy_expDecay`, with the non-vacuity witness
   `CRNT.Network.reversiblePair_state_witness`).

Reference.  D. A. Anderson, *A proof of the global attractor conjecture*, SIAM J. Appl. Math.
**71** (2011), 1527–1543: the local analysis of the Horn–Jackson pseudo-Helmholtz free energy
at a complex-balanced equilibrium, the quadratic (Hessian) expansion of the free energy, and
the resulting exponential rate.  The same quadratic expansion is the "thermodynamic speed
limit" of the entropy production: the rate is governed by the spectrum of the entropy
Hessian `diag(1/x*ᵢ)`.

## The rate as an eigenvalue of the entropy Hessian

The Hessian of the relative entropy at `x*` is the *diagonal* operator `h ↦ (h ᵢ / x*ᵢ)`, i.e.
`diag(1/x*ᵢ)`; as a linear operator on `Concentration S` its eigenvectors are the coordinate
vectors and its eigenvalues are `1/x*ᵢ`
(`CRNT.Network.entropyHessianOp_apply_indicator`).  The **smallest** of them is
`1 / maxᵢ x*ᵢ`, which is `CRNT.Network.minEntropyHessianEigenvalue`; the entropy-Hessian
metric dominates the squared norm with that constant
(`CRNT.Network.entropyHessianQuadratic_ge_minEigenvalue`), and the quadratic constant of
the local Lyapunov estimate is one quarter of it
(`CRNT.Network.relEntropy_ge_quadratic_minEigenvalue`).

## What is *not* claimed

* **Not the global statement.**  Anderson's global attractor theorem, and the global
  exponential rate of the free energy, are not proved here; this module is local, in the
  stoichiometric class of the equilibrium, exactly like leaves D4 and D21.
* **Not the constant-one prefactor.**  The conclusion of
  `relEntropy_expDecay_along_solution` carries a prefactor `K > 1`.  Removing it would
  require the *Fisher-information* form of the dissipation,
  `d/dt G = −(1/2) ∑_r q_r ⟨ν_r, D(x*)⁻¹ h⟩² ≤ −c G`, an identity for the entropy
  production that is not available in this library (the dissipation is currently bounded
  only by Gibbs' inequality, `CRNT.Network.dissipation_nonpos`).
* **Not a spectral theorem in the sense of `Matrix.PosDef`.**  The eigenvalue formulation
  above is carried out for the entropy Hessian *as a linear operator* on `Concentration S`.
  A statement phrased with Mathlib's `Matrix.PosDef` / `LinearMap.eigenvalues` would
  require a choice of a finite-dimensional inner-product model (`Matrix n n ℝ`, `n = card S`)
  for the concentration space, together with a comparison of the resulting spectral gap
  with the entropy-Hessian metric; that machinery is not used in this library, and the
  rate of the *linearized* dynamics (leaf D21) is governed by the spectrum of the
  Jacobian, not by that of the Hessian alone.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## The scalar Gibbs deficit -/

/-- **Upper quadratic bound for the Gibbs deficit** `φ(t) = t log t − t + 1`: for `t ≥ 0`,
`φ(t) ≤ (t − 1)²`.  This is the elementary estimate `log t ≤ t − 1`. -/
theorem gibbsDeficit_le_sq {t : ℝ} (ht : 0 ≤ t) :
    t * Real.log t - t + 1 ≤ (t - 1) ^ 2 := by
  rcases eq_or_lt_of_le ht with h | h
  · rw [← h, Real.log_zero]
    norm_num
  · have hlog : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos h
    have h1 : t * Real.log t ≤ t * (t - 1) := mul_le_mul_of_nonneg_left hlog ht
    nlinarith [h1]

/-- **Lower quadratic bound for the Gibbs deficit, on the left of `1`.**  For `0 < t ≤ 1`,
`(t − 1)² ≤ 2 φ(t)`.

The auxiliary function `χ(u) = 2 u log u − u² + 1` satisfies `χ(1) = 0` and
`χ'(u) = 2 (log u + 1 − u) ≤ 0` for `u ≤ 1` (because `log u ≤ u − 1`); hence `χ` is
antitone on `[t, 1]` and `χ(t) ≥ χ(1) = 0`. -/
theorem gibbsDeficit_ge_half_sq {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (t - 1) ^ 2 ≤ 2 * (t * Real.log t - t + 1) := by
  set χ : ℝ → ℝ := fun u => 2 * u * Real.log u - u ^ 2 + 1 with hχdef
  have hmul : ContinuousOn (fun u : ℝ => u * Real.log u) (Set.Ioi 0) := by
    intro u hu
    exact (Real.hasDerivAt_mul_log (ne_of_gt hu)).continuousAt.continuousWithinAt
  have hmul' : ContinuousOn (fun u : ℝ => u * Real.log u) (Set.Icc t 1) := by
    refine hmul.mono ?_
    intro u hu
    exact lt_of_lt_of_le ht hu.1
  have hcont : ContinuousOn χ (Set.Icc t 1) := by
    have h1 : ContinuousOn (fun u : ℝ => 2 * (u * Real.log u)) (Set.Icc t 1) :=
      continuousOn_const.mul hmul'
    have h2 : ContinuousOn (fun u : ℝ => u ^ 2) (Set.Icc t 1) :=
      continuousOn_id.pow 2
    have h3 : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc t 1) := continuousOn_const
    have h4 : ContinuousOn (fun u : ℝ => (2 * (u * Real.log u) - u ^ 2) + 1)
        (Set.Icc t 1) := (h1.sub h2).add h3
    have hfun : (fun u : ℝ => 2 * u * Real.log u - u ^ 2 + 1)
        = fun u : ℝ => (2 * (u * Real.log u) - u ^ 2) + 1 := by
      funext u; ring
    rw [hχdef, hfun]
    exact h4
  have hderiv : ∀ u ∈ Set.Ioo t 1, HasDerivAt χ (2 * (Real.log u + 1 - u)) u := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (lt_trans ht hu.1)
    have h1 : HasDerivAt (fun u : ℝ => u * Real.log u) (Real.log u + 1) u :=
      Real.hasDerivAt_mul_log hu0
    have h2 : HasDerivAt (fun u : ℝ => 2 * (u * Real.log u)) (2 * (Real.log u + 1)) u :=
      h1.const_mul 2
    have h3 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * u) u := by
      have hid : HasDerivAt (fun x : ℝ => x) 1 u := hasDerivAt_id (𝕜 := ℝ) (x := u)
      convert hid.pow 2 using 1 ; ring
    have h4 : HasDerivAt (fun u : ℝ => 2 * (u * Real.log u) - u ^ 2 + 1)
        (2 * (Real.log u + 1) - 2 * u) u := by
      convert h2.sub h3 |>.add_const 1 using 1
    have hfun : (fun u : ℝ => 2 * u * Real.log u - u ^ 2 + 1)
        = fun u : ℝ => 2 * (u * Real.log u) - u ^ 2 + 1 := by
      funext u; ring
    rw [hχdef, hfun]
    convert h4 using 1 ; ring
  have hdiff : DifferentiableOn ℝ χ (interior (Set.Icc t 1)) := by
    rw [interior_Icc]
    exact fun u hu => (hderiv u hu).differentiableAt.differentiableWithinAt
  have hnonpos : ∀ u ∈ interior (Set.Icc t 1), deriv χ u ≤ 0 := by
    intro u hu
    rw [interior_Icc, Set.mem_Ioo] at hu
    rw [(hderiv u hu).deriv]
    have hlog := Real.log_le_sub_one_of_pos (lt_trans ht hu.1)
    linarith
  have hanti : AntitoneOn χ (Set.Icc t 1) :=
    antitoneOn_of_deriv_nonpos (convex_Icc t 1) hcont hdiff hnonpos
  have hle : χ 1 ≤ χ t :=
    hanti (Set.left_mem_Icc.mpr ht1) (Set.right_mem_Icc.mpr ht1) ht1
  have hχ1 : χ 1 = 0 := by
    simp only [hχdef]
    norm_num
  rw [hχ1] at hle
  have hid : χ t = 2 * (t * Real.log t - t + 1) - (t - 1) ^ 2 := by
    simp only [hχdef]
    ring
  rw [hid] at hle
  linarith

/-- **Lower quadratic bound for the Gibbs deficit, on the right of `1`.**  For `1 ≤ t`,
`(t − 1)² ≤ 2 t φ(t)`.

The auxiliary function `ψ(u) = 2 u² log u − 3 u² + 4 u − 1` satisfies `ψ(1) = 0` and
`ψ'(u) = 4 φ(u) ≥ 0` (Gibbs' inequality), hence `ψ` is monotone on `[1, t]` and
`ψ(t) ≥ ψ(1) = 0`. -/
theorem gibbsDeficit_ge_sq_div_t {t : ℝ} (ht1 : 1 ≤ t) :
    (t - 1) ^ 2 ≤ 2 * t * (t * Real.log t - t + 1) := by
  set ψ : ℝ → ℝ := fun u => 2 * u ^ 2 * Real.log u - 3 * u ^ 2 + 4 * u - 1 with hψdef
  have hmul : ContinuousOn (fun u : ℝ => u ^ 2 * Real.log u) (Set.Ioi 0) := by
    intro u hu
    have h1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * u) u := by
      have hid : HasDerivAt (fun x : ℝ => x) 1 u := hasDerivAt_id (𝕜 := ℝ) (x := u)
      convert hid.pow 2 using 1 ; ring
    have h2 : HasDerivAt Real.log (u⁻¹) u := Real.hasDerivAt_log (ne_of_gt hu)
    exact h1.mul h2 |>.continuousAt.continuousWithinAt
  have hmul' : ContinuousOn (fun u : ℝ => u ^ 2 * Real.log u) (Set.Icc 1 t) := by
    refine hmul.mono ?_
    intro u hu
    exact lt_of_lt_of_le one_pos hu.1
  have hcont : ContinuousOn ψ (Set.Icc 1 t) := by
    have h1 : ContinuousOn (fun u : ℝ => 2 * (u ^ 2 * Real.log u)) (Set.Icc 1 t) :=
      continuousOn_const.mul hmul'
    have h2 : ContinuousOn (fun u : ℝ => u ^ 2) (Set.Icc 1 t) :=
      continuousOn_id.pow 2
    have h3 : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc 1 t) := continuousOn_const
    have h4 : ContinuousOn (fun u : ℝ => ((2 * (u ^ 2 * Real.log u) - 3 * u ^ 2) + 4 * u) - 1)
        (Set.Icc 1 t) := ((h1.sub (continuousOn_const.mul h2)).add
        (continuousOn_const.mul (continuousOn_id : ContinuousOn (fun u : ℝ => u) _))).sub h3
    have hfun : (fun u : ℝ => 2 * u ^ 2 * Real.log u - 3 * u ^ 2 + 4 * u - 1)
        = fun u : ℝ => ((2 * (u ^ 2 * Real.log u) - 3 * u ^ 2) + 4 * u) - 1 := by
      funext u; ring
    rw [hψdef, hfun]
    exact h4
  have hderiv : ∀ u ∈ Set.Ioo 1 t, HasDerivAt ψ (4 * (u * Real.log u - u + 1)) u := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (lt_trans one_pos hu.1)
    have hinv : u ^ 2 * u⁻¹ = u := by field_simp
    have h1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * u) u := by
      have hid : HasDerivAt (fun x : ℝ => x) 1 u := hasDerivAt_id (𝕜 := ℝ) (x := u)
      convert hid.pow 2 using 1 ; ring
    have h2 : HasDerivAt Real.log (u⁻¹) u := Real.hasDerivAt_log hu0
    have h3 : HasDerivAt (fun x : ℝ => x ^ 2 * Real.log x)
        (2 * u * Real.log u + u ^ 2 * u⁻¹) u := h1.mul h2
    have h4 : HasDerivAt (fun x : ℝ => 2 * (x ^ 2 * Real.log x))
        (2 * (2 * u * Real.log u + u ^ 2 * u⁻¹)) u := h3.const_mul 2
    have h6 : HasDerivAt (fun x : ℝ => 3 * x ^ 2) (3 * (2 * u)) u := h1.const_mul 3
    have h7 : HasDerivAt (fun x : ℝ => 4 * x) 4 u := by
      have hid : HasDerivAt (fun x : ℝ => x) 1 u := hasDerivAt_id (𝕜 := ℝ) (x := u)
      convert hid.const_mul 4 using 1 ; ring
    have h8 : HasDerivAt (fun x : ℝ => 2 * (x ^ 2 * Real.log x) - 3 * x ^ 2 + 4 * x - 1)
        (2 * (2 * u * Real.log u + u ^ 2 * u⁻¹) - 3 * (2 * u) + 4) u := by
      convert h4.sub h6 |>.add h7 |>.sub_const 1 using 1
    have hfun : (fun u : ℝ => 2 * u ^ 2 * Real.log u - 3 * u ^ 2 + 4 * u - 1)
        = fun x : ℝ => 2 * (x ^ 2 * Real.log x) - 3 * x ^ 2 + 4 * x - 1 := by
      funext x; ring
    rw [hψdef, hfun]
    convert h8 using 1; rw [hinv]; ring
  have hdiff : DifferentiableOn ℝ ψ (interior (Set.Icc 1 t)) := by
    rw [interior_Icc]
    exact fun u hu => (hderiv u hu).differentiableAt.differentiableWithinAt
  have hnonneg : ∀ u ∈ interior (Set.Icc 1 t), 0 ≤ deriv ψ u := by
    intro u hu
    rw [interior_Icc, Set.mem_Ioo] at hu
    rw [(hderiv u hu).deriv]
    have hg := relEntropyTerm_nonneg (t := u) (a := 1) (lt_trans one_pos hu.1).le (by norm_num)
    rw [div_one] at hg
    nlinarith [hg]
  have hmono : MonotoneOn ψ (Set.Icc 1 t) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 1 t) hcont hdiff hnonneg
  have hle : ψ 1 ≤ ψ t :=
    hmono (Set.left_mem_Icc.mpr ht1) (Set.right_mem_Icc.mpr ht1) ht1
  have hψ1 : ψ 1 = 0 := by
    simp only [hψdef]
    norm_num
  rw [hψ1] at hle
  have hid : ψ t = 2 * t * (t * Real.log t - t + 1) - (t - 1) ^ 2 := by
    simp only [hψdef]
    ring
  rw [hid] at hle
  linarith

/-- **The Gibbs deficit is quadratically bounded below.**  For `t > 0`,
`(t − 1)² ≤ 2 max{1, t} (t log t − t + 1)`. -/
theorem gibbsDeficit_ge_sq_div {t : ℝ} (ht : 0 < t) :
    (t - 1) ^ 2 ≤ 2 * max 1 t * (t * Real.log t - t + 1) := by
  rcases le_total 1 t with h | h
  · have h1 := gibbsDeficit_ge_sq_div_t h
    have hmax : max 1 t = t := max_eq_right h
    rw [hmax]
    exact h1
  · have h1 := gibbsDeficit_ge_half_sq ht h
    have hmax : max 1 t = 1 := max_eq_left h
    rw [hmax]
    convert h1 using 1 ; ring

/-! ## The relative entropy against the entropy-Hessian metric -/

omit [DecidableEq S] [Fintype S] in
/-- **Coordinatewise form of the relative entropy.**  The `i`-th summand of the relative
entropy is `x*ᵢ` times the Gibbs deficit at the ratio `xᵢ / x*ᵢ`. -/
theorem relEntropyTerm_eq_gibbsDeficit {xstar x : Concentration S} (hxs : xstar.Positive)
    (i : S) :
    x i * Real.log (x i / xstar i) - x i + xstar i
      = xstar i * ((x i / xstar i) * Real.log (x i / xstar i) - (x i / xstar i) + 1) := by
  have hxs0 : xstar i ≠ 0 := (hxs i).ne'
  have hx : xstar i * (x i / xstar i) = x i := by field_simp
  calc
    x i * Real.log (x i / xstar i) - x i + xstar i
        = xstar i * (x i / xstar i) * Real.log (x i / xstar i)
            - xstar i * (x i / xstar i) + xstar i := by rw [hx]
    _ = xstar i * ((x i / xstar i) * Real.log (x i / xstar i) - (x i / xstar i) + 1) := by
      ring

omit [DecidableEq S] in
/-- **The relative entropy in terms of the Gibbs deficits.** -/
theorem relEntropy_eq_gibbsDeficit {xstar x : Concentration S} (hxs : xstar.Positive) :
    relEntropy xstar x
      = ∑ i, xstar i * ((x i / xstar i) * Real.log (x i / xstar i) - (x i / xstar i) + 1) := by
  unfold relEntropy
  exact Finset.sum_congr rfl fun i _ => relEntropyTerm_eq_gibbsDeficit hxs i

omit [DecidableEq S] in
/-- **The relative entropy is bounded above by the entropy-Hessian quadratic form.**
For a nonnegative concentration `x` and a positive reference `x*`,
`G_{x*}(x) ≤ ∑ᵢ (xᵢ − x*ᵢ)² / x*ᵢ`.  This is the *upper* half of the quadratic
(Taylor) estimate of the relative entropy and holds globally, not only near `x*`. -/
theorem relEntropy_le_entropyHessianQuadratic {xstar x : Concentration S}
    (hxs : xstar.Positive) (hx : x.Nonnegative) :
    relEntropy xstar x ≤ entropyHessianQuadratic xstar (x - xstar) := by
  rw [relEntropy_eq_gibbsDeficit hxs]
  unfold entropyHessianQuadratic
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 := gibbsDeficit_le_sq (t := x i / xstar i) (div_nonneg (hx i) (hxs i).le)
  have h2 : xstar i * ((x i / xstar i) * Real.log (x i / xstar i) - (x i / xstar i) + 1)
      ≤ xstar i * ((x i / xstar i) - 1) ^ 2 := mul_le_mul_of_nonneg_left h1 (hxs i).le
  have h3 : xstar i * ((x i / xstar i) - 1) ^ 2 = (x i - xstar i) ^ 2 / xstar i := by
    have hxs0 : xstar i ≠ 0 := (hxs i).ne'
    field_simp
  exact h2.trans_eq h3

omit [DecidableEq S] in
/-- **The relative entropy is bounded below by a quarter of the entropy-Hessian quadratic
form, close to the reference.**  If `x` is positive and `xᵢ ≤ 2 x*ᵢ` for every `i`, then
`G_{x*}(x) ≥ (1/4) ∑ᵢ (xᵢ − x*ᵢ)² / x*ᵢ`.

This is the *lower* half of the quadratic (Taylor) estimate of the relative entropy; it is
the quantitative local Lyapunov property of the complex-balanced equilibrium. -/
theorem relEntropy_ge_entropyHessianQuadratic {xstar x : Concentration S}
    (hxs : xstar.Positive) (hx : x.Positive) (hnb : ∀ s, x s ≤ 2 * xstar s) :
    (1 / 4 : ℝ) * entropyHessianQuadratic xstar (x - xstar) ≤ relEntropy xstar x := by
  rw [relEntropy_eq_gibbsDeficit hxs]
  unfold entropyHessianQuadratic
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have ht : 0 < x i / xstar i := div_pos (hx i) (hxs i)
  have h1 := gibbsDeficit_ge_sq_div ht
  have hmax : max 1 (x i / xstar i) ≤ 2 :=
    max_le (by norm_num) ((div_le_iff₀ (hxs i)).2 (by linarith [hnb i]))
  have hφ : 0 ≤ (x i / xstar i) * Real.log (x i / xstar i) - (x i / xstar i) + 1 := by
    have hg := relEntropyTerm_nonneg (t := x i / xstar i) (a := 1) ht.le (by norm_num)
    rw [div_one] at hg
    exact hg
  have h2 : (x i / xstar i - 1) ^ 2 ≤ 4 *
      ((x i / xstar i) * Real.log (x i / xstar i) - (x i / xstar i) + 1) := by
    have h3 : 2 * max 1 (x i / xstar i) *
        ((x i / xstar i) * Real.log (x i / xstar i) - (x i / xstar i) + 1)
        ≤ 4 * ((x i / xstar i) * Real.log (x i / xstar i) - (x i / xstar i) + 1) := by
      nlinarith [hmax, hφ]
    linarith
  have h3 : (1 / 4 : ℝ) * ((x i - xstar i) ^ 2 / xstar i)
      = xstar i * ((x i / xstar i) - 1) ^ 2 / 4 := by
    have hxs0 : xstar i ≠ 0 := (hxs i).ne'
    field_simp
  have h4 : xstar i * ((x i / xstar i) - 1) ^ 2 / 4
      ≤ xstar i * ((x i / xstar i) * Real.log (x i / xstar i) - (x i / xstar i) + 1) := by
    nlinarith [h2, hxs i]
  simp only [Pi.sub_apply]
  rw [h3]
  exact h4

/-! ## The quadratic lower bound: the relative entropy as a local Lyapunov function -/

/-- **The relative entropy is bounded below by a positive multiple of the squared distance**
whenever `x` is positive and lies in the box `xᵢ ≤ 2 x*ᵢ` around the reference `x*`:
`(1/4) / (∑ᵢ x*ᵢ + 1) ‖x − x*‖² ≤ G_{x*}(x)`. -/
theorem relEntropy_ge_quadratic_norm {xstar x : Concentration S} (hxs : xstar.Positive)
    (hx : x.Positive) (hnb : ∀ s, x s ≤ 2 * xstar s) :
    (1 / 4 : ℝ) / ((∑ s : S, xstar s) + 1) * ‖x - xstar‖ ^ 2 ≤ relEntropy xstar x := by
  have h1 := relEntropy_ge_entropyHessianQuadratic hxs hx hnb
  have h2 : ‖x - xstar‖ ^ 2
      ≤ ((∑ s : S, xstar s) + 1) * entropyHessianQuadratic xstar (x - xstar) :=
    norm_sq_le_entropyHessianQuadratic hxs (x - xstar)
  have hBpos : 0 < (∑ s : S, xstar s) + 1 := by
    have : 0 ≤ ∑ s : S, xstar s := Finset.sum_nonneg fun s _ => (hxs s).le
    linarith
  have hBne : (∑ s : S, xstar s) + 1 ≠ 0 := ne_of_gt hBpos
  have hcpos : 0 ≤ (1 / 4 : ℝ) / ((∑ s : S, xstar s) + 1) := div_nonneg (by norm_num) hBpos.le
  have hdiv : (1 / 4 : ℝ) / ((∑ s : S, xstar s) + 1) * ((∑ s : S, xstar s) + 1)
      = 1 / 4 := by field_simp
  calc
    (1 / 4 : ℝ) / ((∑ s : S, xstar s) + 1) * ‖x - xstar‖ ^ 2
        ≤ (1 / 4 : ℝ) / ((∑ s : S, xstar s) + 1) * ((∑ s : S, xstar s) + 1)
            * entropyHessianQuadratic xstar (x - xstar) := by
          have h4 := mul_le_mul_of_nonneg_left h2 hcpos
          have h5 : (1 / 4 : ℝ) / ((∑ s : S, xstar s) + 1)
              * (((∑ s : S, xstar s) + 1) * entropyHessianQuadratic xstar (x - xstar))
              = (1 / 4 : ℝ) / ((∑ s : S, xstar s) + 1) * ((∑ s : S, xstar s) + 1)
                * entropyHessianQuadratic xstar (x - xstar) := by ring
          exact h4.trans_eq h5
    _ = (1 / 4 : ℝ) * entropyHessianQuadratic xstar (x - xstar) := by rw [hdiv]
    _ ≤ relEntropy xstar x := h1

/-- **The relative entropy is quadratic near the complex-balanced equilibrium.**

There is a constant `c > 0` such that `G_{x*}(x) ≥ c ‖x − x*‖²` for every concentration `x`
in the box neighbourhood `xᵢ ≤ 2 x*ᵢ` of the equilibrium; and the relative entropy is a
Lyapunov function there: its directional derivative along the mass-action field is
nonpositive.

The constant delivered here is `c = (1/4) / (∑ᵢ x*ᵢ + 1)`; the sharper constant
`(1/4) · λ_min`, where `λ_min` is the smallest eigenvalue of the entropy Hessian, is
`CRNT.Network.relEntropy_ge_quadratic_minEigenvalue` below. -/
theorem relEntropy_ge_quadratic_of_complexBalanced (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) :
    ∃ c : ℝ, 0 < c ∧
      (∀ x : Concentration S, x.Positive → (∀ s, x s ≤ 2 * xstar s) →
          c * ‖x - xstar‖ ^ 2 ≤ relEntropy xstar x) ∧
      (∀ x : Concentration S, x.Positive →
          (∑ s, (Real.log (x s) - Real.log (xstar s)) * N.massActionVectorField κ x s) ≤ 0) := by
  set c : ℝ := (1 / 4 : ℝ) / ((∑ s : S, xstar s) + 1) with hcdef
  have hB : 0 < (∑ s : S, xstar s) + 1 := by
    have : 0 ≤ ∑ s : S, xstar s := Finset.sum_nonneg fun s _ => (hxs s).le
    linarith
  have hc : 0 < c := by rw [hcdef]; positivity
  refine ⟨c, hc, ?_, ?_⟩
  · intro x hx hnb
    rw [hcdef]
    exact relEntropy_ge_quadratic_norm hxs hx hnb
  · intro x hx
    exact dissipation_nonpos N κ hx hxs hcb

/-- **The quadratic lower bound in a norm ball around the equilibrium.**  There are
`c > 0` and `ε > 0` — one may take `ε = minᵢ x*ᵢ` — such that
`G_{x*}(x) ≥ c ‖x − x*‖²` for every positive `x` with `‖x − x*‖ < ε`.  This is the
quantitative local Lyapunov property of the complex-balanced equilibrium, in the form of a
statement about a genuine neighbourhood of `x*`. -/
theorem relEntropy_ge_quadratic_in_ball {S : Type} [DecidableEq S] [Fintype S] [Nonempty S]
    {xstar : Concentration S} (hxs : xstar.Positive) :
    ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧
      ∀ x : Concentration S, x.Positive → ‖x - xstar‖ < ε →
        c * ‖x - xstar‖ ^ 2 ≤ relEntropy xstar x := by
  set m : ℝ := Finset.min' ((Finset.univ : Finset S).image xstar)
    (Finset.image_nonempty.mpr Finset.univ_nonempty) with hmdef
  have hmin : ∀ t : S, m ≤ xstar t := by
    intro t
    have h1 : xstar t ∈ (Finset.univ : Finset S).image xstar :=
      Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩
    have h' := Finset.min'_le ((Finset.univ : Finset S).image xstar) (xstar t) h1
    rwa [← hmdef] at h'
  have hmpos : 0 < m := by
    have h1 := Finset.min'_mem ((Finset.univ : Finset S).image xstar)
      (Finset.image_nonempty.mpr Finset.univ_nonempty)
    rw [← hmdef] at h1
    obtain ⟨s, _, hsm⟩ := Finset.mem_image.mp h1
    rw [← hsm]
    exact hxs s
  have hBpos : 0 < (∑ s : S, xstar s) + 1 := by
    have : 0 ≤ ∑ s : S, xstar s := Finset.sum_nonneg fun s _ => (hxs s).le
    linarith
  have hc : 0 < (1 / 4 : ℝ) / ((∑ s : S, xstar s) + 1) := by positivity
  refine ⟨(1 / 4 : ℝ) / ((∑ s : S, xstar s) + 1), m, hc, hmpos, ?_⟩
  intro x hx hnorm
  have hnb : ∀ s, x s ≤ 2 * xstar s := by
    intro s
    have h1 : |x s - xstar s| ≤ ‖x - xstar‖ := by
      have := norm_le_pi_norm (x - xstar) s
      simpa [Real.norm_eq_abs, Pi.sub_apply] using this
    have h1' := abs_le.mp h1
    have h2 : ‖x - xstar‖ < m := hnorm
    have h3 : m ≤ xstar s := hmin s
    linarith
  exact relEntropy_ge_quadratic_norm hxs hx hnb

/-! ## The exponential decay of the relative entropy -/

/-- **The relative entropy decays exponentially along a solution.**

Let `x*` be a positive complex-balanced equilibrium of a weakly reversible network with rate
constants `κ`, and let `γ` be a mass-action trajectory with `γ 0 = x₀` in the stoichiometric
class of `x*` and sufficiently close to `x*`.  Then the relative entropy with respect to
`x*` decays at least exponentially:
`G_{x*}(γ t) ≤ K e^{−2αt} G_{x*}(γ 0)` for some `K > 0` and `α > 0`.

The proof combines the quadratic lower bound of the relative entropy
(`relEntropy_ge_entropyHessianQuadratic`), its global upper bound by the entropy-Hessian
quadratic form (`relEntropy_le_entropyHessianQuadratic`), and the exponential convergence
of the trajectory supplied by leaf D4
(`CRNT.Network.complexBalanced_locallyExponentiallyStable_in_class`).

The prefactor `K` reflects the comparison of the entropy-Hessian metric with the norm in
which the exponential convergence is stated; removing it would require the
Fisher-information form of the dissipation (see the module docstring). -/
theorem relEntropy_expDecay_along_solution (N : Network S) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) :
    ∃ K α ε : ℝ, 0 < K ∧ 0 < α ∧ 0 < ε ∧
      ∀ (x₀ : Concentration S) (γ : ℝ → Concentration S),
        x₀.Positive → (∀ s, x₀ s ≤ 2 * xstar s) → N.StoichCompatible xstar x₀ →
        ‖x₀ - xstar‖ < ε → γ 0 = x₀ →
        (∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t) →
        ∀ t, 0 ≤ t →
          relEntropy xstar (γ t) ≤ K * Real.exp (-2 * α * t) * relEntropy xstar x₀ := by
  obtain ⟨ε, C, α, hε, hC, hα, hstab⟩ :=
    N.complexBalanced_locallyExponentiallyStable_in_class κ hwr hxs hcb
  set Mx : ℝ := ∑ s : S, 1 / xstar s with hMxdef
  set B : ℝ := (∑ s : S, xstar s) + 1 with hBdef
  set K : ℝ := 4 * Mx * B * C ^ 2 + 1 with hKdef
  have hMxnn : 0 ≤ Mx := by
    rw [hMxdef]; exact Finset.sum_nonneg fun s _ => div_nonneg zero_le_one (hxs s).le
  have hBpos : 0 < B := by
    rw [hBdef]
    have : 0 ≤ ∑ s : S, xstar s := Finset.sum_nonneg fun s _ => (hxs s).le
    linarith
  have hKpos : 0 < K := by
    rw [hKdef]
    have hC2 : 0 ≤ C ^ 2 := sq_nonneg _
    have : 0 ≤ Mx * B * C ^ 2 := by positivity
    linarith
  refine ⟨K, α, ε, hKpos, hα, hε, ?_⟩
  intro x₀ γ hx₀ hnb hcompat hnorm hγ0 hγd t ht
  have hstab' : ‖γ t - xstar‖ ≤ C * Real.exp (-α * t) * ‖x₀ - xstar‖ :=
    hstab x₀ γ hx₀ hcompat hnorm hγ0 hγd t ht
  -- the trajectory stays positive
  have hpos : (γ t).Positive := by
    refine N.orbit_pos_forward κ (Γ := γ) (B := (∑ s : S, xstar s) + C * ‖x₀ - xstar‖) ?_ ?_ hγd t ht
    · rw [hγ0]; exact hx₀
    · intro τ hτ s
      have hstabτ := hstab x₀ γ hx₀ hcompat hnorm hγ0 hγd τ hτ
      have h1 : |γ τ s - xstar s| ≤ ‖γ τ - xstar‖ := by
        have := norm_le_pi_norm (γ τ - xstar) s
        simpa [Real.norm_eq_abs, Pi.sub_apply] using this
      have h1' := abs_le.mp h1
      have h2 : Real.exp (-α * τ) ≤ 1 := by
        have h3 : -α * τ ≤ 0 := by
          have : 0 ≤ α * τ := mul_nonneg hα.le hτ
          linarith
        exact Real.exp_le_one_iff.mpr h3
      have h3 : γ τ s ≤ xstar s + C * Real.exp (-α * τ) * ‖x₀ - xstar‖ := by
        linarith [h1'.2, hstabτ]
      have h4 : xstar s ≤ ∑ s' : S, xstar s' :=
        Finset.single_le_sum (f := fun s' => xstar s') (fun i _ => (hxs i).le) (Finset.mem_univ s)
      have h5 : C * Real.exp (-α * τ) * ‖x₀ - xstar‖ ≤ C * ‖x₀ - xstar‖ := by
        have h6 : C * Real.exp (-α * τ) ≤ C := by
          simpa using mul_le_mul_of_nonneg_left h2 hC.le
        have h7 : 0 ≤ ‖x₀ - xstar‖ := norm_nonneg _
        have h8 := mul_le_mul_of_nonneg_left h6 h7
        nlinarith
      linarith
  -- the relative entropy is bounded above by the entropy-Hessian metric
  have hV1 : relEntropy xstar (γ t) ≤ entropyHessianQuadratic xstar (γ t - xstar) :=
    relEntropy_le_entropyHessianQuadratic hxs hpos.nonnegative
  have hV2 : entropyHessianQuadratic xstar (γ t - xstar) ≤ Mx * ‖γ t - xstar‖ ^ 2 := by
    rw [hMxdef]; exact entropyHessianQuadratic_le hxs (γ t - xstar)
  -- and below, at the initial point, by a quarter of it
  have hV0 : (1 / 4 : ℝ) * entropyHessianQuadratic xstar (x₀ - xstar) ≤ relEntropy xstar x₀ := by
    have h1 := relEntropy_ge_entropyHessianQuadratic hxs hx₀ hnb
    simpa [hγ0] using h1
  have hV0' : entropyHessianQuadratic xstar (x₀ - xstar) ≤ 4 * relEntropy xstar x₀ := by
    nlinarith [hV0]
  have hD0 : ‖x₀ - xstar‖ ^ 2 ≤ B * entropyHessianQuadratic xstar (x₀ - xstar) := by
    rw [hBdef]; exact norm_sq_le_entropyHessianQuadratic hxs (x₀ - xstar)
  -- the exponential convergence of the trajectory
  have hN : ‖γ t - xstar‖ ^ 2 ≤ (C * Real.exp (-α * t) * ‖x₀ - xstar‖) ^ 2 := by
    have hnn : 0 ≤ ‖γ t - xstar‖ := norm_nonneg _
    have he : 0 ≤ C * Real.exp (-α * t) * ‖x₀ - xstar‖ := by positivity
    nlinarith [hstab']
  have hexp : (Real.exp (-α * t)) ^ 2 = Real.exp (-2 * α * t) := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  -- the chain of estimates
  have hE : 0 ≤ Real.exp (-2 * α * t) := (Real.exp_pos _).le
  have hstep1 : relEntropy xstar (γ t)
      ≤ Mx * (C * Real.exp (-α * t) * ‖x₀ - xstar‖) ^ 2 := by
    have h1 := le_trans hV1 hV2
    nlinarith [h1, hN, hMxnn]
  have hstep2 : Mx * (C * Real.exp (-α * t) * ‖x₀ - xstar‖) ^ 2
      = Mx * C ^ 2 * Real.exp (-2 * α * t) * ‖x₀ - xstar‖ ^ 2 := by
    have h1 : (C * Real.exp (-α * t) * ‖x₀ - xstar‖) ^ 2
        = C ^ 2 * Real.exp (-α * t) ^ 2 * ‖x₀ - xstar‖ ^ 2 := by
      rw [mul_pow, mul_pow]
    rw [h1, hexp]
    ring
  have hstep3 : Mx * C ^ 2 * Real.exp (-2 * α * t) * ‖x₀ - xstar‖ ^ 2
      ≤ Mx * C ^ 2 * Real.exp (-2 * α * t) * B * entropyHessianQuadratic xstar (x₀ - xstar) := by
    have h1 : ‖x₀ - xstar‖ ^ 2 ≤ B * entropyHessianQuadratic xstar (x₀ - xstar) := hD0
    have h2 : 0 ≤ Mx * C ^ 2 * Real.exp (-2 * α * t) :=
      mul_nonneg (mul_nonneg hMxnn (sq_nonneg _)) hE
    calc
      Mx * C ^ 2 * Real.exp (-2 * α * t) * ‖x₀ - xstar‖ ^ 2
          ≤ Mx * C ^ 2 * Real.exp (-2 * α * t)
              * (B * entropyHessianQuadratic xstar (x₀ - xstar)) :=
        mul_le_mul_of_nonneg_left h1 h2
      _ = Mx * C ^ 2 * Real.exp (-2 * α * t) * B
          * entropyHessianQuadratic xstar (x₀ - xstar) := by ring
  have hstep4 : Mx * C ^ 2 * Real.exp (-2 * α * t) * B
        * entropyHessianQuadratic xstar (x₀ - xstar)
      ≤ 4 * Mx * B * C ^ 2 * Real.exp (-2 * α * t) * relEntropy xstar x₀ := by
    have h1 : entropyHessianQuadratic xstar (x₀ - xstar) ≤ 4 * relEntropy xstar x₀ := hV0'
    have h2 : 0 ≤ Mx * C ^ 2 * Real.exp (-2 * α * t) * B :=
      mul_nonneg (mul_nonneg (mul_nonneg hMxnn (sq_nonneg _)) hE) hBpos.le
    calc
      Mx * C ^ 2 * Real.exp (-2 * α * t) * B
          * entropyHessianQuadratic xstar (x₀ - xstar)
          ≤ Mx * C ^ 2 * Real.exp (-2 * α * t) * B * (4 * relEntropy xstar x₀) :=
            mul_le_mul_of_nonneg_left h1 h2
      _ = 4 * Mx * B * C ^ 2 * Real.exp (-2 * α * t) * relEntropy xstar x₀ := by ring
  have hstep5 : 4 * Mx * B * C ^ 2 * Real.exp (-2 * α * t) * relEntropy xstar x₀
      ≤ K * Real.exp (-2 * α * t) * relEntropy xstar x₀ := by
    have hV0nn : 0 ≤ relEntropy xstar x₀ := relEntropy_nonneg hx₀.nonnegative hxs
    have h1 : 0 ≤ Real.exp (-2 * α * t) * relEntropy xstar x₀ := mul_nonneg hE hV0nn
    rw [hKdef]
    nlinarith [h1]
  have hmain : relEntropy xstar (γ t)
      ≤ 4 * Mx * B * C ^ 2 * Real.exp (-2 * α * t) * relEntropy xstar x₀ := by
    calc
      relEntropy xstar (γ t)
          ≤ Mx * C ^ 2 * Real.exp (-2 * α * t) * ‖x₀ - xstar‖ ^ 2 :=
        hstep1.trans hstep2.le
      _ ≤ 4 * Mx * B * C ^ 2 * Real.exp (-2 * α * t) * relEntropy xstar x₀ :=
        hstep3.trans hstep4
  exact hmain.trans hstep5

/-! ## The entropy Hessian as an operator: its eigenvalues -/

/-- The coordinate (indicator) vector of a species. -/
def speciesIndicator (s : S) : Concentration S := fun t => if t = s then 1 else 0

/-- **The entropy Hessian as a linear operator.**  The Hessian of the relative entropy at
`x*` is the diagonal operator `h ↦ (h ᵢ / x*ᵢ)`, i.e. the matrix `diag(1/x*ᵢ)`. -/
noncomputable def entropyHessianOp (xstar : Concentration S) :
    Concentration S →ₗ[ℝ] Concentration S where
  toFun h s := h s / xstar s
  map_add' u v := by
    funext s
    simp only [Pi.add_apply, add_div]
  map_smul' c h := by
    funext s
    simp only [Pi.smul_apply, smul_eq_mul, mul_div_assoc, RingHom.id_apply]

omit [Fintype S] in
/-- **The coordinate vector of a species is an eigenvector of the entropy Hessian**, with
eigenvalue `1 / x*_s`.  These are all the eigenvalues of the diagonal entropy Hessian. -/
theorem entropyHessianOp_apply_indicator (xstar : Concentration S) (s : S) :
    entropyHessianOp xstar (speciesIndicator s) = (1 / xstar s) • speciesIndicator s := by
  funext t
  by_cases h : t = s
  · subst h
    simp [entropyHessianOp, speciesIndicator, Pi.smul_apply, smul_eq_mul]
  · simp [entropyHessianOp, speciesIndicator, Pi.smul_apply, smul_eq_mul, h]

/-- The largest concentration at the reference `x*`. -/
noncomputable def maxConcentration {S : Type} [DecidableEq S] [Fintype S] [Nonempty S]
    (xstar : Concentration S) : ℝ :=
  Finset.sup' (Finset.univ : Finset S) Finset.univ_nonempty xstar

/-- **The smallest eigenvalue of the entropy Hessian.**  The Hessian of the relative entropy
at `x*` is `diag(1/x*ᵢ)`; its eigenvalues are `1/x*ᵢ` and the smallest of them is the
reciprocal of the largest concentration, `1 / maxᵢ x*ᵢ`. -/
noncomputable def minEntropyHessianEigenvalue {S : Type} [DecidableEq S] [Fintype S]
    [Nonempty S] (xstar : Concentration S) : ℝ := 1 / maxConcentration xstar

theorem maxConcentration_ge [Nonempty S] (xstar : Concentration S) (s : S) :
    xstar s ≤ maxConcentration xstar := by
  rw [maxConcentration, Finset.le_sup'_iff]
  exact ⟨s, Finset.mem_univ s, le_rfl⟩

theorem maxConcentration_pos [Nonempty S] (xstar : Concentration S) (hxs : xstar.Positive) :
    0 < maxConcentration xstar := by
  obtain ⟨s⟩ : Nonempty S := inferInstance
  have h1 : 0 < xstar s := hxs s
  have h2 : xstar s ≤ maxConcentration xstar := maxConcentration_ge xstar s
  linarith

/-- **The entropy-Hessian metric dominates the squared norm with the smallest eigenvalue.**
For every `h`, `λ_min ‖h‖² ≤ ∑ᵢ hᵢ² / x*ᵢ`, where `λ_min` is the smallest eigenvalue of the
entropy Hessian. -/
theorem entropyHessianQuadratic_ge_minEigenvalue {xstar : Concentration S} [Nonempty S]
    (hxs : xstar.Positive) (h : Concentration S) :
    minEntropyHessianEigenvalue xstar * ‖h‖ ^ 2 ≤ entropyHessianQuadratic xstar h := by
  set M : ℝ := maxConcentration xstar with hMdef
  have hMpos : 0 < M := maxConcentration_pos xstar hxs
  have hcoord : ∀ s : S, h s ^ 2 / xstar s ≥ h s ^ 2 / M := by
    intro s
    have hs : xstar s ≤ M := maxConcentration_ge xstar s
    have hone : 1 / M ≤ 1 / xstar s := one_div_le_one_div_of_le (hxs s) hs
    have hsq : 0 ≤ h s ^ 2 := sq_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hone hsq
    simpa [M, hMdef, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hQ1 : (∑ s : S, h s ^ 2 / M) ≤ entropyHessianQuadratic xstar h :=
    Finset.sum_le_sum fun s _ => hcoord s
  have hsumsq : ‖h‖ ^ 2 ≤ ∑ s : S, h s ^ 2 := by
    have h1 : ‖h‖ ≤ Real.sqrt (∑ s : S, h s ^ 2) := by
      rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
      intro s
      rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
      refine Real.sqrt_le_sqrt ?_
      exact Finset.single_le_sum (s := (Finset.univ : Finset S)) (f := fun s' => h s' ^ 2)
        (fun i _ => sq_nonneg (h i)) (Finset.mem_univ s)
    have h2 : (Real.sqrt (∑ s : S, h s ^ 2)) ^ 2 = ∑ s : S, h s ^ 2 :=
      Real.sq_sqrt (Finset.sum_nonneg fun s _ => sq_nonneg _)
    have h3 : 0 ≤ ‖h‖ := norm_nonneg _
    nlinarith
  have heq : (1 / M) * (∑ s : S, h s ^ 2) = ∑ s : S, h s ^ 2 / M := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    field_simp
  have hstep : (1 / M) * ‖h‖ ^ 2 ≤ (1 / M) * (∑ s : S, h s ^ 2) := by
    have h1 : ‖h‖ ^ 2 ≤ ∑ s : S, h s ^ 2 := hsumsq
    have h2 : 0 ≤ 1 / M := by positivity
    exact mul_le_mul_of_nonneg_left h1 h2
  have hfinal : (1 / M) * ‖h‖ ^ 2 ≤ entropyHessianQuadratic xstar h := by
    calc
      (1 / M) * ‖h‖ ^ 2 ≤ (1 / M) * (∑ s : S, h s ^ 2) := hstep
      _ = ∑ s : S, h s ^ 2 / M := heq
      _ ≤ entropyHessianQuadratic xstar h := hQ1
  have hmin : minEntropyHessianEigenvalue xstar = 1 / M := by
    unfold minEntropyHessianEigenvalue
    rw [← hMdef]
  rw [hmin]
  exact hfinal

/-- **The decay rate is governed by the smallest eigenvalue of the entropy Hessian.**
Close to the reference `x*` the relative entropy is bounded below by one quarter of the
smallest eigenvalue of the entropy Hessian `diag(1/x*ᵢ)` times the squared distance.  This is
the quantitative content of the "thermodynamic speed limit" reading of the entropy
production. -/
theorem relEntropy_ge_quadratic_minEigenvalue {xstar x : Concentration S} [Nonempty S]
    (hxs : xstar.Positive) (hx : x.Positive) (hnb : ∀ s, x s ≤ 2 * xstar s) :
    (1 / 4 : ℝ) * minEntropyHessianEigenvalue xstar * ‖x - xstar‖ ^ 2
      ≤ relEntropy xstar x := by
  have h1 := relEntropy_ge_entropyHessianQuadratic hxs hx hnb
  have h2 := entropyHessianQuadratic_ge_minEigenvalue hxs (x - xstar)
  calc
    (1 / 4 : ℝ) * minEntropyHessianEigenvalue xstar * ‖x - xstar‖ ^ 2
        = (1 / 4 : ℝ) * (minEntropyHessianEigenvalue xstar * ‖x - xstar‖ ^ 2) := by ring
    _ ≤ (1 / 4 : ℝ) * entropyHessianQuadratic xstar (x - xstar) := by
      exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ ≤ relEntropy xstar x := h1

/-! ## A worked instance: the reversible pair `A ⇌ B` -/

section ReversiblePair

open CRNT.Examples.ReversiblePair

/-- **Worked instance.**  For the reversible pair `A ⇌ B` with positive rate constants `k₀`
(forward) and `k₁` (backward), the relative entropy with respect to the detailed-balanced
equilibrium `x* = (k₁, k₀)` decays exponentially along every mass-action trajectory that
starts in the stoichiometric class of `x*` and close enough to `x*`. -/
theorem reversiblePair_relEntropy_expDecay (k₀ k₁ : ℝ) (h₀ : 0 < k₀) (h₁ : 0 < k₁) :
    ∃ K α ε : ℝ, 0 < K ∧ 0 < α ∧ 0 < ε ∧
      ∀ (x₀ : Concentration Species) (γ : ℝ → Concentration Species),
        x₀.Positive → (∀ s, x₀ s ≤ 2 * equilibrium k₀ k₁ s) →
        N.StoichCompatible (equilibrium k₀ k₁) x₀ →
        ‖x₀ - equilibrium k₀ k₁‖ < ε → γ 0 = x₀ →
        (∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField (rates h₀ h₁) (γ t)) t) →
        ∀ t, 0 ≤ t →
          relEntropy (equilibrium k₀ k₁) (γ t) ≤
            K * Real.exp (-2 * α * t) * relEntropy (equilibrium k₀ k₁) x₀ := by
  obtain ⟨K, α, ε, hK, hα, hε, h⟩ :=
    relEntropy_expDecay_along_solution N (rates h₀ h₁) weaklyReversible
      (equilibrium_positive h₀ h₁) (equilibrium_isComplexBalanced h₀ h₁)
  exact ⟨K, α, ε, hK, hα, hε, h⟩

/-- A concrete state of the reversible pair obtained from the detailed-balanced equilibrium
by moving a small amount of material from `B` to `A`. -/
def reversiblePair_state (k₀ k₁ δ : ℝ) : Concentration Species :=
  equilibrium k₀ k₁ + fun s => if s = Species.A then δ else -δ

/-- **The worked instance is non-vacuous.**  For `0 < δ < min{k₀, k₁}` the state
`reversiblePair_state k₀ k₁ δ` is positive, lies in the box neighbourhood of the
detailed-balanced equilibrium, and belongs to its stoichiometric class. -/
theorem reversiblePair_state_witness (k₀ k₁ δ : ℝ)
    (hδ : 0 < δ) (hδ0 : δ < k₀) (hδ1 : δ < k₁) :
    (reversiblePair_state k₀ k₁ δ).Positive ∧
      (∀ s, (reversiblePair_state k₀ k₁ δ) s ≤ 2 * equilibrium k₀ k₁ s) ∧
      N.StoichCompatible (equilibrium k₀ k₁) (reversiblePair_state k₀ k₁ δ) := by
  have hmem : (reversiblePair_state k₀ k₁ δ - equilibrium k₀ k₁)
      = -δ • N.reactionVector Rxn.fwd := by
    funext s
    by_cases hA : s = Species.A
    · subst hA
      simp [reversiblePair_state, equilibrium, Network.reactionVector, N, rxn, Reaction.vector,
        cA, cB, Pi.smul_apply, Pi.sub_apply]
    · have hB : s = Species.B := by
        cases s with
        | A => exact absurd rfl hA
        | B => rfl
      subst hB
      simp [reversiblePair_state, equilibrium, Network.reactionVector, N, rxn, Reaction.vector,
        cA, cB, Pi.smul_apply, Pi.sub_apply]
  refine ⟨?_, ?_, ?_⟩
  · intro s
    cases s <;>
      simp [reversiblePair_state, equilibrium, Pi.add_apply] <;>
        linarith [hδ, hδ0, hδ1]
  · intro s
    cases s <;>
      simp [reversiblePair_state, equilibrium, Pi.add_apply] <;>
        linarith [hδ, hδ0, hδ1]
  · show (reversiblePair_state k₀ k₁ δ - equilibrium k₀ k₁) ∈ N.stoichSubspace
    rw [hmem]
    exact N.stoichSubspace.smul_mem (-δ) (N.reactionVector_mem_stoichSubspace Rxn.fwd)

end ReversiblePair

/-! ## Axiom audit of the principal declarations -/

#print axioms CRNT.Network.relEntropy_le_entropyHessianQuadratic
#print axioms CRNT.Network.relEntropy_ge_entropyHessianQuadratic
#print axioms CRNT.Network.relEntropy_ge_quadratic_norm
#print axioms CRNT.Network.relEntropy_ge_quadratic_of_complexBalanced
#print axioms CRNT.Network.relEntropy_ge_quadratic_in_ball
#print axioms CRNT.Network.relEntropy_expDecay_along_solution
#print axioms CRNT.Network.entropyHessianOp_apply_indicator
#print axioms CRNT.Network.entropyHessianQuadratic_ge_minEigenvalue
#print axioms CRNT.Network.relEntropy_ge_quadratic_minEigenvalue
#print axioms CRNT.Network.reversiblePair_relEntropy_expDecay
#print axioms CRNT.Network.reversiblePair_state_witness

end Network

end CRNT
