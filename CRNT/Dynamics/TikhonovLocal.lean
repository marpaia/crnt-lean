import CRNT.Dynamics.Tikhonov
import CRNT.Dynamics.FenichelC1Manifold
import CRNT.Analysis.LinearODE
import CRNT.Dynamics.ExponentialDecay
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Asymptotics.Basic

/-!
# Tikhonov's theorem: the local (Hurwitz) version

This module formalises the **local** form of Tikhonov's theorem for singularly perturbed systems,
i.e. the version that does *not* require a globally contracting fast subsystem.

The setup is the classical one. A slow–fast system

```
ẋ = f (x, y),      ε ẏ = g (x, y)
```

has a *slow manifold* `y = h (x)`, a curve of equilibria of the fast field `g (·, ·)` along which the
slow variable evolves. The classical Tikhonov theorem (A. A. Tikhonov, *On the convergence of
singular perturbed processes*, Dokl. Akad. Nauk SSSR 26 (1952) 148–150; see also the survey by
R. Fenichel, *Geometric singular perturbation theory for ordinary differential equations*, Bull.
AMS 52 (2015) 969–998, §2) says:

> If the fast field `g (x₀, ·)` has a **stable equilibrium** `y₀` — in the classical formulation,
> `∂_y g (x₀, y₀)` is *Hurwitz*, i.e. all its eigenvalues have negative real part — then for small
> `ε` the solution of the full system is asymptotic to the slow manifold: the fast variable
> `y (t)` tracks `h (x (t))`, and the reduced system `ẋ = f (x, h (x))` describes the slow dynamics.

The repository already contains a *global* version of the boundary-layer half of this picture:

* `CRNT.Dynamics.Tikhonov` (`ODE.norm_sub_le_exp_neg_mul`, `ODE.FastSubsystem`) proves exponential
  attraction of an integral curve of a fast field that is **one-sided contracting everywhere**;
* `CRNT.Dynamics.Fenichel` (`ODE.SlowManifold`) turns that into a slow manifold whose fibres are
  uniformly contracting;
* `CRNT.Dynamics.FenichelC1Manifold` adds the `C¹` regularity of the manifold map via the implicit
  function theorem;
* `CRNT.Dynamics.SlowFast` (`CRNT.SlowFast.fast_deviation_le`, `CRNT.SlowFast.slow_error_le`)
  quantifies the deviation of a *coupled* solution from the reduced one, but again under a
  **global** contraction hypothesis `⟪g x u - g x v, u - v⟫ ≤ -μ ‖u - v‖²` valid for *all* pairs
  `u, v` in a whole region.

What is missing — and what this module supplies — is the **local** statement: the contraction is
required only in a *neighbourhood* of the slow manifold, and the stability of the fast equilibrium
is required only through the *Hurwitz* (Lyapunov) condition on its linearisation
`∂_y g (x₀, y₀)`.

## What is added here

1. **The Hurwitz condition on the fast linearisation** (`CRNT.HurwitzRate`). The continuous linear
   map `A` is *Hurwitz with rate `μ`* when its symmetric part is bounded above by `-μ I`:
   `⟪A w, w⟫ ≤ -μ ‖w‖²` for all `w`. This is the *Lyapunov–Krasovskii* form of the Hurwitz
   condition (Lyapunov, 1892); it is the condition that the classical Hurwitz criterion is built
   on, it implies that the linearisation is injective, and it is the hypothesis under which the
   *linearised* fast system decays.

2. **The linearised fast system** (`CRNT.hurwitz_linear_decay`). If `A` is Hurwitz with rate `μ`,
   every integral curve of `ẏ = A y` satisfies `‖y t‖ ≤ e^{-μ t} ‖y 0‖`: the boundary layer of the
   linearised fast system collapses exponentially. This is the reusable core of the local theorem.

3. **Local attraction of the nonlinear frozen fast system**
   (`CRNT.local_contraction_of_hurwitz`, `CRNT.oneSidedContractionAt_bound`). By the *linearisation
   principle* (Lyapunov's first method), the Hurwitz condition on `∂_y g (x₀, y₀)` gives a
   neighbourhood of `y₀` in which the fast field is one-sided contracting toward `y₀` at a rate
   `ν > 0`, and every integral curve that stays in that neighbourhood converges to `y₀`
   exponentially. This is a genuinely *local* statement: the contraction is not assumed globally.

4. **The `ε`-scaled frozen system** (`CRNT.frozen_scaled_hasDerivAt`,
   `CRNT.frozen_attraction_local`, `CRNT.frozen_attraction_of_hurwitz`,
   `CRNT.frozen_collapse_of_hurwitz`). The frozen fast system `ε ẏ = g (x₀, y)` is the rescaling
   of `ẏ = g (x₀, y)`; its solutions are `y (t/ε)`, they converge to `y₀` as `ε → 0⁺` for every
   fixed `t > 0`, and the convergence rate is `e^{-ν t/ε}`. This is Tikhonov's key estimate for the
   frozen system.

5. **The local slow manifold** (`CRNT.fiberDeriv`, `CRNT.exists_local_slow_manifold`,
   `CRNT.local_slow_manifold_unique`). By the implicit function theorem, the Hurwitz condition
   makes `∂_y g (x₀, y₀)` invertible, so there is a *unique* local `C¹` map `h` with
   `g (x, h x) = 0` and `h x₀ = y₀`; the derivative of `h` is the classical implicit derivative
   `-(∂_y g)⁻¹ ∘ ∂_x g`.

6. **The coupled system with a local contraction hypothesis**
   (`CRNT.fast_deviation_le_local`). This is the passage from the frozen system to the full
   coupled system, and it is the quantitative heart of the local Tikhonov theorem: if the coupled
   solution `ẋ = f (x, y)`, `ε ẏ = g (x, y)` stays within distance `δ` of the slow manifold
   `y = h (x)`, and the fast field is one-sided contracting toward `h (x)` *locally* (with rate
   `ν > 0`), then
   `‖y t - h (x t)‖² ≤ e^{-(ν/ε) t} ‖y 0 - h (x 0)‖² + (ε G / ν)²`,
   where `G` bounds the speed `‖D h (x t) (f (x t) (y t))‖` of the slow manifold along the flow.
   In particular the fast variable is within `O (ε)` of the slow manifold: this is the conclusion
   of Tikhonov's theorem that the full solution is asymptotic to the slow manifold as `ε → 0`.

7. **The local Tikhonov theorem** (`CRNT.tikhonov_local`, `CRNT.tikhonov_local_attraction`) collects
   the pieces: the local slow manifold exists and is `C¹`, the fast field contracts locally, and
   the frozen fast system collapses onto the fast equilibrium as `ε → 0⁺`.

8. **A concrete instance** (`CRNT.MichaelisMenten`): the Michaelis–Menten fast field
   `g s c = s - (s + K) c` has fiber derivative `∂_c g = -(s + K)`, which is Hurwitz with rate
   `s + K > 0`; every hypothesis of the local theorem is verified (`CRNT.hurwitzRate_gFastDeriv`,
   `CRNT.local_contraction_michaelisMenten`, `CRNT.tikhonov_michaelisMenten`) and the corresponding
   conclusions are drawn.

## What remains

* **The passage from the frozen system to the coupled system is formalised but the *tube*
  hypothesis is not discharged.** `CRNT.fast_deviation_le_local` proves the estimate
  `‖y t - h (x t)‖² ≤ e^{-(ν/ε) t} ‖y 0 - h (x 0)‖² + (ε G / ν)²` for a coupled solution that
  *stays* within distance `δ` of the slow manifold; proving that a solution of the coupled system
  enters (and stays in) that tube is the standard "exponential attraction" step of Fenichel's
  proof, which needs the global graph-transform machinery of `CRNT.Dynamics.FenichelPersistence`.
* **The purely spectral form of the Hurwitz hypothesis.** The Hurwitz condition used here is the
  Lyapunov (symmetric-part) form `⟪A w, w⟫ ≤ -μ ‖w‖²`, which is *stronger* than the spectral
  condition "all eigenvalues of `A` have negative real part" for a general (non-normal) `A`: the
  spectral condition only yields the existence of a positive-definite solution `P` of the Lyapunov
  equation `Aᵀ P + P A = -I`, from which the decay follows with a prefactor, but that construction
  is not available in `Mathlib`. For self-adjoint `A` the two conditions agree. The hypothesis used
  here is the one that the *Fenichel* machinery of the repository already uses
  (`ODE.OneSidedContraction`), so it is consistent with `CRNT.Dynamics.Fenichel`.
* **The slow error.** As in `CRNT.Dynamics.SlowFast`, the estimate on the *slow* variable
  (`|x t - X t|`) additionally needs a Lipschitz bound for `f` in the fast variable; the module
  `CRNT.Dynamics.SlowFast` provides it under the global hypothesis.
* **The `ε`-dependent (Fenichel) manifold.** The manifold `h` constructed here is the *reduced*
  slow manifold `g (x, h x) = 0`. Fenichel's theorem additionally produces an `ε`-dependent
  invariant manifold `h_ε` with `h_ε → h`; the persistence machinery of
  `CRNT.Dynamics.FenichelPersistence` addresses that under the global contraction hypothesis.

Depends on: `CRNT.Dynamics.Tikhonov`, `CRNT.Dynamics.FenichelC1Manifold`,
`CRNT.Analysis.LinearODE`, `CRNT.Dynamics.ExponentialDecay`,
`Mathlib.Analysis.Calculus.ImplicitContDiff`, `Mathlib.Analysis.Asymptotics.Basic`.
-/

open Filter Set
open scoped Topology BigOperators RealInnerProductSpace

namespace CRNT

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-! ## 1. The Hurwitz condition on the fast linearisation -/

/-- **The Hurwitz condition with rate `μ`.** The continuous linear map `A : E →L[ℝ] E` is *Hurwitz
with rate `μ`* when its symmetric part is bounded above by `-μ I`:
`⟪A w, w⟫ ≤ -μ ‖w‖²` for every `w ∈ E`.

This is the *Lyapunov–Krasovskii* form of the Hurwitz condition (Lyapunov 1892, *The general problem
of the stability of motion*; cf. Hahn, *Stability of Motion*, Thm. 3.1; Coppel, *Dichotomies in
Stability Theory*, Thm. 3.3): it is a sufficient condition for the linear map `A` to be *Hurwitz* in
the spectral sense (all eigenvalues of `A` have real part `< 0`), it is equivalent to that spectral
condition when `A` is self-adjoint, and it is exactly the "one-sided contraction" condition that
the Fenichel machinery of `CRNT.Dynamics.Fenichel` (`ODE.OneSidedContraction`) uses.

Unlike `ODE.OneSidedContraction`, the condition is required only *at the equilibrium* — locally —
and not globally on a region; this is what makes the local Tikhonov theorem possible. -/
def HurwitzRate (A : E →L[ℝ] E) (μ : ℝ) : Prop :=
  ∀ w, ⟪A w, w⟫ ≤ -μ * ‖w‖ ^ 2

/-- A Hurwitz map with positive rate is injective: if `A w₁ = A w₂` then `‖w₁ - w₂‖² ≤ 0`. -/
theorem hurwitzRate_injective {A : E →L[ℝ] E} {μ : ℝ} (hA : HurwitzRate A μ) (hμ : 0 < μ) :
    Function.Injective A := by
  intro w₁ w₂ hw
  have h := hA (w₁ - w₂)
  have hz : A (w₁ - w₂) = 0 := by rw [map_sub, hw, sub_self]
  rw [hz] at h
  simp at h
  have hnn : 0 ≤ μ * ‖w₁ - w₂‖ ^ 2 := mul_nonneg hμ.le (sq_nonneg _)
  have heq : μ * ‖w₁ - w₂‖ ^ 2 = 0 := by linarith
  rcases mul_eq_zero.mp heq with h | h
  · linarith
  · have hnorm : ‖w₁ - w₂‖ = 0 := by
      have := sq_nonneg ‖w₁ - w₂‖
      nlinarith [norm_nonneg (w₁ - w₂)]
    have : w₁ - w₂ = 0 := norm_eq_zero.mp hnorm
    exact sub_eq_zero.mp this

/-- In finite dimension a Hurwitz linearisation is invertible; this is what the implicit function
theorem needs in order to produce the slow manifold. -/
theorem hurwitzRate_isInvertible {A : E →L[ℝ] E} {μ : ℝ} (hA : HurwitzRate A μ) (hμ : 0 < μ)
    [FiniteDimensional ℝ E] : A.IsInvertible := by
  have hinj : Function.Injective A := hurwitzRate_injective hA hμ
  have hker : A.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have hsurj : A.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact LinearMap.surjective_of_injective hinj
  exact ⟨ContinuousLinearEquiv.ofBijective A hker hsurj, rfl⟩

/-- **The Hurwitz map expands at least at the rate `μ`.** From `⟪A w, w⟫ ≤ -μ ‖w‖²` and
Cauchy–Schwarz one gets `‖A w‖ ≥ μ ‖w‖`. -/
theorem hurwitzRate_norm_lower_bound {A : E →L[ℝ] E} {μ : ℝ} (hA : HurwitzRate A μ)
    (w : E) : μ * ‖w‖ ≤ ‖A w‖ := by
  have habs : |⟪A w, w⟫| ≤ ‖A w‖ * ‖w‖ := abs_real_inner_le_norm _ _
  have hcs : -⟪A w, w⟫ ≤ ‖A w‖ * ‖w‖ := by
    have := abs_le.mp habs
    linarith
  have h1 : μ * ‖w‖ ^ 2 ≤ ‖A w‖ * ‖w‖ := by linarith [hA w]
  by_cases hw : ‖w‖ = 0
  · rw [hw]; simp
  · have hpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg w) (Ne.symm hw)
    have h2 : ‖w‖ * (μ * ‖w‖) ≤ ‖w‖ * ‖A w‖ := by
      calc ‖w‖ * (μ * ‖w‖) = μ * (‖w‖ * ‖w‖) := by ring
        _ = μ * ‖w‖ ^ 2 := by ring
        _ ≤ ‖A w‖ * ‖w‖ := h1
        _ = ‖w‖ * ‖A w‖ := by ring
    exact le_of_mul_le_mul_left h2 hpos

/-! ## 2. The linearised fast system -/

/-- **The linearised fast system decays exponentially.** Let `A : E →L[ℝ] E` be Hurwitz with rate
`μ > 0`, and let `z : ℝ → E` be an integral curve of the *linearised* fast system `ẏ = A y`. Then
`‖z t‖ ≤ e^{-μ t} ‖z 0‖` for every `t ≥ 0`: the boundary layer of the linearised fast system
collapses at the exponential rate `μ`.

This is the reusable core of the local Tikhonov theorem: it is the *linear* estimate that the
nonlinear, local statements of §3–§4 refine. -/
theorem hurwitz_linear_decay {A : E →L[ℝ] E} {μ : ℝ} (hA : HurwitzRate A μ) (hμ : 0 < μ)
    {z : ℝ → E} (hz : ∀ t, HasDerivAt z (A (z t)) t) :
    ∀ t, 0 ≤ t → ‖z t‖ ≤ Real.exp (-μ * t) * ‖z 0‖ := by
  intro t ht
  have hcon : ODE.OneSidedContraction (fun w : E => A w) 0 μ := by
    intro w
    show ⟪A w - A 0, w - 0⟫ ≤ -μ * ‖w - 0‖ ^ 2
    simp only [map_zero, sub_zero]
    exact hA w
  have h2 := ODE.norm_sub_le_exp_neg_mul hz (A.map_zero) hcon hμ.le t ht
  simpa [mul_comm] using h2

/-! ## 3. Local attraction of the nonlinear frozen fast system -/

/-- **Local exponential attraction (one-sided contraction at the equilibrium, locally).** Let `f` be
a field on `E`, `zstar` a stationary point of `f`, and suppose `f` is one-sided contracting toward
`zstar` at rate `lam` *on a neighbourhood* of `zstar` (radius `δ`). If `z` is an integral curve of
`f` that stays in that neighbourhood on `[0, T]`, then
`‖z t - zstar‖ ≤ ‖z 0 - zstar‖ e^{-lam t}` for `t ∈ [0, T]`.

This is the local counterpart of `ODE.norm_sub_le_exp_neg_mul` (which needs the contraction
*everywhere*); the proof is the same Lyapunov-function argument, restricted to the interval where
the local hypothesis is available. -/
theorem oneSidedContractionAt_bound {f : E → E} {zstar : E} {lam δ T : ℝ}
    (hstat : f zstar = 0)
    (hcon : ∀ z, dist z zstar ≤ δ → ⟪f z - f zstar, z - zstar⟫ ≤ -lam * ‖z - zstar‖ ^ 2)
    {z : ℝ → E} (hz : ∀ t, HasDerivAt z (f (z t)) t)
    (hzK : ∀ t ∈ Icc 0 T, dist (z t) zstar ≤ δ) :
    ∀ t ∈ Icc 0 T, ‖z t - zstar‖ ≤ ‖z 0 - zstar‖ * Real.exp (-lam * t) := by
  intro t ht
  set e : ℝ → E := fun t => z t - zstar with he
  have hed : ∀ t, HasDerivAt e (f (z t)) t := by
    intro s
    simpa [he] using (hz s).sub_const zstar
  set V : ℝ → ℝ := fun t => ⟪e t, e t⟫ with hV
  have hVd : ∀ t, HasDerivAt V (2 * ⟪f (z t), e t⟫) t := by
    intro s
    have h := (hed s).inner ℝ (hed s)
    have hsym : ⟪e s, f (z s)⟫ + ⟪f (z s), e s⟫ = 2 * ⟪f (z s), e s⟫ := by
      rw [real_inner_comm (e s) (f (z s))]
      ring
    simpa [hV, hsym] using h
  have hVbound : ∀ s ∈ Icc 0 T, 2 * ⟪f (z s), e s⟫ ≤ -(2 * lam) * V s := by
    intro s hs
    have hc : ⟪f (z s) - f zstar, z s - zstar⟫ ≤ -lam * ‖z s - zstar‖ ^ 2 :=
      hcon (z s) (hzK s hs)
    rw [hstat, sub_zero] at hc
    have hVe : V s = ‖e s‖ ^ 2 := by simp only [hV]; rw [real_inner_self_eq_norm_sq]
    have h1 : ⟪f (z s), e s⟫ ≤ -lam * V s := by
      rw [hVe]
      simpa [he] using hc
    nlinarith [h1]
  set W : ℝ → ℝ := fun t => V t * Real.exp (2 * lam * t) with hW
  have hWd : ∀ t, HasDerivAt W
      ((2 * ⟪f (z t), e t⟫ + (2 * lam) * V t) * Real.exp (2 * lam * t)) t := by
    intro t
    have hlin : HasDerivAt (fun s : ℝ => 2 * lam * s) (2 * lam) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * lam)
    have hexp : HasDerivAt (fun s => Real.exp (2 * lam * s))
        (Real.exp (2 * lam * t) * (2 * lam)) t := hlin.exp
    have h := (hVd t).mul hexp
    have heq : (2 * ⟪f (z t), e t⟫ + (2 * lam) * V t) * Real.exp (2 * lam * t)
        = 2 * ⟪f (z t), e t⟫ * Real.exp (2 * lam * t)
          + V t * (Real.exp (2 * lam * t) * (2 * lam)) := by ring
    rw [heq]
    exact h
  have hWnonpos : ∀ s ∈ Icc 0 T,
      (2 * ⟪f (z s), e s⟫ + (2 * lam) * V s) * Real.exp (2 * lam * s) ≤ 0 := by
    intro s hs
    have hb := hVbound s hs
    have hle : 2 * ⟪f (z s), e s⟫ + (2 * lam) * V s ≤ 0 := by nlinarith [hb]
    exact mul_nonpos_of_nonpos_of_nonneg hle (Real.exp_pos _).le
  have hWmono : ∀ t ∈ Icc 0 T, W t ≤ W 0 := by
    intro t ht
    have hWcont : ContinuousOn W (Icc 0 t) :=
      (continuous_iff_continuousAt.2 fun s => (hWd s).continuousAt).continuousOn
    have key := image_le_of_deriv_right_le_deriv_boundary (f := W)
      (f' := fun s => (2 * ⟪f (z s), e s⟫ + (2 * lam) * V s) * Real.exp (2 * lam * s))
      (a := 0) (b := t) hWcont
      (fun s _ => (hWd s).hasDerivWithinAt)
      (B := fun _ => W 0) (B' := fun _ => 0) (le_refl _)
      (continuousOn_const)
      (fun s _ => hasDerivWithinAt_const s _ (W 0))
      (fun s hs => hWnonpos s ⟨hs.1, le_trans hs.2.le ht.2⟩)
    exact key (right_mem_Icc.mpr ht.1)
  have hVexp : V t ≤ V 0 * Real.exp (-(2 * lam) * t) := by
    have h0 : W 0 = V 0 := by simp [hW]
    have hWt : V t * Real.exp (2 * lam * t) ≤ V 0 := by
      simpa [hW, h0] using hWmono t ht
    have hpos : 0 < Real.exp (2 * lam * t) := Real.exp_pos _
    have hexpinv : Real.exp (-(2 * lam) * t) = (Real.exp (2 * lam * t))⁻¹ := by
      rw [← Real.exp_neg]
      ring_nf
    rw [hexpinv, ← div_eq_mul_inv, le_div_iff₀ hpos]
    linarith
  have hsqrtVt : Real.sqrt (V t) = ‖e t‖ := by
    simp only [hV]
    rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  have hsqrtV0 : Real.sqrt (V 0) = ‖e 0‖ := by
    simp only [hV]
    rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  have hstep : ‖e t‖ ≤ Real.sqrt (V 0 * Real.exp (-(2 * lam) * t)) := by
    rw [← hsqrtVt]
    exact Real.sqrt_le_sqrt hVexp
  have hV0_nonneg : 0 ≤ V 0 := real_inner_self_nonneg
  have hsqrtexp : Real.sqrt (Real.exp (-(2 * lam) * t)) = Real.exp (-lam * t) := by
    rw [show -(2 * lam) * t = (-lam * t) * 2 by ring, ← Real.exp_half ((-lam * t) * 2)]
    congr 1
    ring
  have hsqrtRHS : Real.sqrt (V 0 * Real.exp (-(2 * lam) * t)) = ‖e 0‖ * Real.exp (-lam * t) := by
    rw [Real.sqrt_mul hV0_nonneg, hsqrtV0, hsqrtexp]
  rw [hsqrtRHS] at hstep
  simpa [he] using hstep

/-- **Local contraction data.** The fast field `g` is *one-sided contracting toward `y₀` at rate
`rate` on the `radius`-neighbourhood of `y₀`* if
`⟪g (y₀ + w) - g y₀, w⟫ ≤ -rate ‖w‖²` for every `w` with `‖w‖ ≤ radius`. This is the *local*
counterpart of `ODE.OneSidedContraction`: the contraction is required only near the equilibrium,
not on a whole region. -/
structure LocalContraction (g : E → E) (y₀ : E) where
  /-- The local contraction rate. -/
  rate : ℝ
  /-- The rate is strictly positive. -/
  rate_pos : 0 < rate
  /-- The radius of the neighbourhood on which the contraction holds. -/
  radius : ℝ
  /-- The radius is strictly positive. -/
  radius_pos : 0 < radius
  /-- The fast field is one-sided contracting toward `y₀` at rate `rate` on the `radius`-ball. -/
  contraction : ∀ w : E, ‖w‖ ≤ radius → ⟪g (y₀ + w) - g y₀, w⟫ ≤ -rate * ‖w‖ ^ 2

/-- **The linearisation principle (Lyapunov's first method).** Let `g : E → E` be differentiable at
`y₀` with derivative `A`, let `g y₀ = 0`, and suppose the derivative `A` is Hurwitz with rate
`μ > 0`. Then the fast field `g` is one-sided contracting toward `y₀` *locally*, at a positive
rate: there are `ν > 0` and `δ > 0` such that
`⟪g (y₀ + w) - g y₀, w⟫ ≤ -ν ‖w‖²` whenever `‖w‖ ≤ δ`.

This is the local replacement of the *global* contraction hypothesis used by
`CRNT.Dynamics.SlowFast`: the fast field need not contract away from `y₀`, only near it. -/
def local_contraction_of_hurwitz {g : E → E} {y₀ : E} {A : E →L[ℝ] E} {μ : ℝ}
    (hg : HasFDerivAt g A y₀) (hg0 : g y₀ = 0) (hA : HurwitzRate A μ) (hμ : 0 < μ) :
    LocalContraction g y₀ := by
  have hlo : (fun h : E => g (y₀ + h) - g y₀ - A h) =o[𝓝 0] fun h => h :=
    hasFDerivAt_iff_isLittleO_nhds_zero.mp hg
  have hbound : ∀ᶠ h in 𝓝 (0 : E),
      ‖(fun h : E => g (y₀ + h) - g y₀ - A h) h‖ ≤ (μ / 2) * ‖h‖ := by
    have h1 := Asymptotics.isLittleO_iff.mp hlo (c := μ / 2)
    exact h1 (by linarith)
  have hex : ∃ δ : ℝ, δ > 0 ∧
      ∀ w : E, ‖w‖ ≤ δ → ⟪g (y₀ + w) - g y₀, w⟫ ≤ -(μ / 2) * ‖w‖ ^ 2 := by
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp hbound
    refine ⟨δ / 2, by positivity, ?_⟩
    intro w hw
    have hw' : dist w 0 < δ := by
      rw [dist_zero_right]
      have h1 : δ / 2 < δ := by linarith
      linarith
    have hr : ‖g (y₀ + w) - g y₀ - A w‖ ≤ (μ / 2) * ‖w‖ := by
      simpa using hδ' hw'
    have hinner : ⟪g (y₀ + w), w⟫ = ⟪A w, w⟫ + ⟪g (y₀ + w) - g y₀ - A w, w⟫ := by
      have h1 : g (y₀ + w) = A w + (g (y₀ + w) - g y₀ - A w) := by rw [hg0]; abel_nf
      have h2 := congrArg (fun v : E => ⟪v, w⟫) h1
      rwa [inner_add_left] at h2
    have hcs : ⟪g (y₀ + w) - g y₀ - A w, w⟫ ≤ ‖g (y₀ + w) - g y₀ - A w‖ * ‖w‖ :=
      real_inner_le_norm _ _
    have hcs' : ⟪g (y₀ + w) - g y₀ - A w, w⟫ ≤ (μ / 2) * ‖w‖ ^ 2 := by
      have hmul : ‖g (y₀ + w) - g y₀ - A w‖ * ‖w‖ ≤ (μ / 2) * ‖w‖ ^ 2 := by
        have h2 := mul_le_mul_of_nonneg_right hr (norm_nonneg w)
        calc ‖g (y₀ + w) - g y₀ - A w‖ * ‖w‖ ≤ (μ / 2 * ‖w‖) * ‖w‖ := h2
          _ = (μ / 2) * ‖w‖ ^ 2 := by ring
      linarith
    have hA' : ⟪A w, w⟫ ≤ -μ * ‖w‖ ^ 2 := hA w
    rw [hg0, sub_zero]
    rw [hinner]
    linarith
  refine ⟨μ / 2, by linarith, Classical.choose hex, (Classical.choose_spec hex).1, ?_⟩
  exact (Classical.choose_spec hex).2

/-! ## 4. The `ε`-scaled frozen system -/

/-- **The `ε`-scaled frozen fast system.** Let `y` be an integral curve of the frozen fast field
`ẏ = g (y)` (the fast subsystem with the slow variable frozen). Then the rescaled curve
`y_ε t = y (t/ε)` is a solution of the *singularly perturbed* frozen system `ε ẏ_ε = g (y_ε)`:
the `ε`-scaling of the fast time variable is exactly the boundary-layer rescaling of Tikhonov's
proof. -/
theorem frozen_scaled_hasDerivAt {g : E → E} {y : ℝ → E} (hy : ∀ t, HasDerivAt y (g (y t)) t)
    {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    HasDerivAt (fun r : ℝ => y (r / ε)) ((1 / ε) • g ((fun r : ℝ => y (r / ε)) s)) s := by
  have h1 : HasDerivAt (fun r : ℝ => r / ε) (1 / ε) s := by
    have hx := (hasDerivAt_id s).div_const ε
    simpa only [id_eq] using hx
  have _ := hε
  have h2 : HasDerivAt (fun r : ℝ => y (r / ε)) ((1 / ε) • g (y (s / ε))) s := by
    have h3 := HasDerivAt.scomp s (hy (s / ε)) h1
    convert h3 using 1
    funext r
    rfl
  exact h2

/-- **The local one-sided contraction condition, in the `z`-variable.** This is a rephrasing of the
hypothesis `⟪g (y₀ + w) - g y₀, w⟫ ≤ -ν ‖w‖²` used by `CRNT.local_contraction_of_hurwitz`. -/
theorem oneSidedContractionAt_of_local {g : E → E} {y₀ : E} {ν δ : ℝ}
    (hcont : ∀ w : E, ‖w‖ ≤ δ → ⟪g (y₀ + w) - g y₀, w⟫ ≤ -ν * ‖w‖ ^ 2) :
    ∀ z, dist z y₀ ≤ δ → ⟪g z - g y₀, z - y₀⟫ ≤ -ν * ‖z - y₀‖ ^ 2 := by
  intro z hz
  have hz' : ‖z - y₀‖ ≤ δ := by simpa [dist_eq_norm] using hz
  have h := hcont (z - y₀) hz'
  have h' : g (y₀ + (z - y₀)) = g z := by abel_nf
  rw [h'] at h
  exact h

/-- **Attraction of the frozen fast system (local).** Let `g : E → E` be one-sided contracting
toward `y₀` at rate `ν` *on the `δ`-neighbourhood of `y₀`*, and let `y` be an integral curve of
`ẏ = g (y)` that stays in that neighbourhood. Then `y` converges to `y₀` exponentially:
`‖y t - y₀‖ ≤ ‖y 0 - y₀‖ e^{-ν t}`. -/
theorem frozen_attraction_local {g : E → E} {y₀ : E} {ν δ : ℝ}
    (hg0 : g y₀ = 0)
    (hcont : ∀ w : E, ‖w‖ ≤ δ → ⟪g (y₀ + w) - g y₀, w⟫ ≤ -ν * ‖w‖ ^ 2)
    {y : ℝ → E} (hy : ∀ t, HasDerivAt y (g (y t)) t)
    (hyK : ∀ t, 0 ≤ t → dist (y t) y₀ ≤ δ) :
    ∀ t, 0 ≤ t → ‖y t - y₀‖ ≤ ‖y 0 - y₀‖ * Real.exp (-ν * t) := by
  intro t ht
  have h := oneSidedContractionAt_bound (f := g) (zstar := y₀) (lam := ν) (δ := δ) (T := t)
    hg0 (oneSidedContractionAt_of_local hcont) hy (fun s hs => hyK s hs.1) t ⟨ht, le_rfl⟩
  simpa using h

/-- **Attraction of the frozen fast system, from the Hurwitz condition.** If the derivative of the
frozen fast field at `y₀` is Hurwitz with rate `μ > 0`, then there are a rate `ν > 0` and a radius
`δ > 0` such that every integral curve of `ẏ = g (y)` that stays in the `δ`-neighbourhood of `y₀`
converges to `y₀` at the rate `ν`. This is the local Tikhonov attraction estimate for the frozen
fast system: it is *local*, the contraction is not assumed away from `y₀`. -/
theorem frozen_attraction_of_hurwitz {g : E → E} {y₀ : E} {A : E →L[ℝ] E} {μ : ℝ}
    (hg : HasFDerivAt g A y₀) (hg0 : g y₀ = 0) (hA : HurwitzRate A μ) (hμ : 0 < μ)
    {y : ℝ → E} (hy : ∀ t, HasDerivAt y (g (y t)) t) :
    ∃ C : LocalContraction g y₀,
      (∀ t, 0 ≤ t → dist (y t) y₀ ≤ C.radius) →
      ∀ t, 0 ≤ t → ‖y t - y₀‖ ≤ ‖y 0 - y₀‖ * Real.exp (-C.rate * t) := by
  have hC := local_contraction_of_hurwitz hg hg0 hA hμ
  refine ⟨hC, ?_⟩
  intro hK t ht
  exact frozen_attraction_local hg0 hC.contraction hy hK t ht

/-- **Collapse of the boundary layer of the frozen system.** With the hypotheses of
`CRNT.frozen_attraction_of_hurwitz`, the `ε`-scaled frozen solution `y (t/ε)` converges to `y₀` as
`ε → 0⁺`, for every fixed `t > 0`: the boundary layer of the frozen fast system collapses onto the
fast equilibrium. This is the key estimate of Tikhonov's proof, in the frozen (slow variable fixed)
case. -/
theorem frozen_collapse_of_hurwitz {g : E → E} {y₀ : E} {A : E →L[ℝ] E} {μ : ℝ}
    (hg : HasFDerivAt g A y₀) (hg0 : g y₀ = 0) (hA : HurwitzRate A μ) (hμ : 0 < μ)
    {y : ℝ → E} (hy : ∀ t, HasDerivAt y (g (y t)) t) :
    ∃ C : LocalContraction g y₀,
      (∀ t, 0 ≤ t → dist (y t) y₀ ≤ C.radius) →
      ∀ t, 0 < t → Tendsto (fun ε : ℝ => ‖y (t / ε) - y₀‖) (𝓝[>] 0) (𝓝 0) := by
  have hC := local_contraction_of_hurwitz hg hg0 hA hμ
  refine ⟨hC, ?_⟩
  intro hK t ht
  have hν : 0 < hC.rate := hC.rate_pos
  have hcont := hC.contraction
  have hinv : Tendsto (fun ε : ℝ => 1 / ε) (𝓝[>] 0) atTop := by
    simpa only [inv_eq_one_div] using
      (tendsto_inv_nhdsGT_zero : Tendsto (fun x : ℝ => x⁻¹) (𝓝[>] 0) atTop)
  have hneg : Tendsto (fun ε : ℝ => -(hC.rate * t) * (1 / ε)) (𝓝[>] 0) atBot :=
    hinv.const_mul_atTop_of_neg (neg_lt_zero.mpr (mul_pos hν ht))
  have hexp : Tendsto (fun ε : ℝ => Real.exp (-(hC.rate * t) * (1 / ε))) (𝓝[>] 0) (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  refine squeeze_zero' (f := fun ε : ℝ => ‖y (t / ε) - y₀‖)
    (g := fun ε : ℝ => ‖y 0 - y₀‖ * Real.exp (-(hC.rate * t) * (1 / ε)))
    (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hεpos : 0 < ε := hε
    have h1 : 0 ≤ t / ε := by positivity
    have h2 := frozen_attraction_local hg0 hcont hy hK (t / ε) h1
    have hexp_eq : Real.exp (-hC.rate * (t / ε)) = Real.exp (-(hC.rate * t) * (1 / ε)) := by
      congr 1
      field_simp
    rw [hexp_eq] at h2
    exact h2
  · simpa using hexp.const_mul (‖y 0 - y₀‖)

/-! ## 5. The local slow manifold (implicit function theorem) -/

/-- The **fiber derivative** of the fast field `g` at the point `(x₀, y₀)`: the partial derivative
of `g` with respect to the *fast* variable, i.e. `∂_y g (x₀, y₀)`. It is the linearisation of the
frozen fast system at `(x₀, y₀)`, and it is the operator whose Hurwitz property drives the whole
local Tikhonov theorem. -/
noncomputable def fiberDeriv (g : X → E → E) (x₀ : X) (y₀ : E) : E →L[ℝ] E :=
  fderiv ℝ (fun p : X × E => g p.1 p.2) (x₀, y₀) ∘L ContinuousLinearMap.inr ℝ X E

omit [CompleteSpace X] in
/-- The fiber derivative is the Fréchet derivative of the frozen fast field `y ↦ g (x₀, y)` at
`y₀`. -/
theorem fiberDeriv_hasFDerivAt [CompleteSpace E] {g : X → E → E} {x₀ : X} {y₀ : E}
    (hg : ContDiffAt ℝ 1 (fun p : X × E => g p.1 p.2) (x₀, y₀)) :
    HasFDerivAt (fun y : E => g x₀ y) (fiberDeriv g x₀ y₀) y₀ := by
  have hjoint : HasFDerivAt (fun p : X × E => g p.1 p.2)
      (fderiv ℝ (fun p : X × E => g p.1 p.2) (x₀, y₀)) (x₀, y₀) :=
    (hg.differentiableAt (by norm_num)).hasFDerivAt
  have hcomp : HasFDerivAt (fun y : E => g x₀ y)
      ((fderiv ℝ (fun p : X × E => g p.1 p.2) (x₀, y₀)) ∘L ContinuousLinearMap.inr ℝ X E) y₀ :=
    hjoint.comp y₀ (hasFDerivAt_prodMk_right (𝕜 := ℝ) x₀ y₀)
  exact hcomp

/-- **The local slow manifold.** Let `g : X → E → E` be `C¹` at `(x₀, y₀)` and let
`g x₀ y₀ = 0`. If the fiber derivative `∂_y g (x₀, y₀)` is invertible — which the Hurwitz condition
`CRNT.HurwitzRate` implies, since a Hurwitz linearisation is injective — then there is a *unique*
local `C¹` map `h : X → E` with

* `h x₀ = y₀`,
* `g (x, h x) = 0` for `x` close to `x₀` (the slow manifold),
* `h` differentiable at `x₀` with the classical implicit derivative
  `D h x₀ = -(∂_y g (x₀, y₀))⁻¹ ∘ ∂_x g (x₀, y₀)`.

This is the reduced (Tikhonov) slow manifold `g (x, h x) = 0`. -/
theorem exists_local_slow_manifold [CompleteSpace E] {g : X → E → E} {x₀ : X} {y₀ : E}
    (hg : ContDiffAt ℝ 1 (fun p : X × E => g p.1 p.2) (x₀, y₀))
    (hzero : g x₀ y₀ = 0)
    (hInv : (fiberDeriv g x₀ y₀).IsInvertible) :
    ∃ h : X → E, h x₀ = y₀ ∧
      (∀ᶠ x in 𝓝 x₀, g x (h x) = 0) ∧
      ContDiffAt ℝ 1 h x₀ ∧
      HasStrictFDerivAt h
        (-(fiberDeriv g x₀ y₀).inverse ∘L
          (fderiv ℝ (fun p : X × E => g p.1 p.2) (x₀, y₀) ∘L ContinuousLinearMap.inl ℝ X E)) x₀ := by
  have hInv' : (fderiv ℝ (fun p : X × E => g p.1 p.2) (x₀, y₀) ∘L
      ContinuousLinearMap.inr ℝ X E).IsInvertible := by
    show (fiberDeriv g x₀ y₀).IsInvertible
    exact hInv
  set ψ := hg.implicitFunction (by norm_num) hInv' with hψ
  have hψ0 : ψ x₀ = y₀ := hg.implicitFunction_apply_self (by norm_num) hInv'
  have hev : ∀ᶠ x in 𝓝 x₀, (fun p : X × E => g p.1 p.2) (x, ψ x)
      = (fun p : X × E => g p.1 p.2) (x₀, y₀) :=
    hg.eventually_apply_implicitFunction (by norm_num) hInv'
  have hcd : ContDiffAt ℝ 1 ψ x₀ := hg.contDiffAt_implicitFunction (by norm_num) hInv'
  have hfd : HasStrictFDerivAt ψ
      (-(fderiv ℝ (fun p : X × E => g p.1 p.2) (x₀, y₀) ∘L ContinuousLinearMap.inr ℝ X E).inverse ∘L
        (fderiv ℝ (fun p : X × E => g p.1 p.2) (x₀, y₀) ∘L ContinuousLinearMap.inl ℝ X E)) x₀ :=
    hg.hasStrictFDerivAt_implicitFunction (by norm_num) hInv'
  refine ⟨ψ, hψ0, ?_, hcd, ?_⟩
  · filter_upwards [hev] with x hx
    rw [hx, hzero]
  · exact hfd

/-- **Uniqueness of the local slow manifold.** Any two `C¹` maps `h`, `h'` with
`h x₀ = h' x₀ = y₀` and `g (x, h x) = g (x, h' x) = 0` for `x` close to `x₀` agree near `x₀`:
the slow manifold of the reduced system is unique. -/
theorem local_slow_manifold_unique [CompleteSpace E] {g : X → E → E} {x₀ : X} {y₀ : E}
    (hg : ContDiffAt ℝ 1 (fun p : X × E => g p.1 p.2) (x₀, y₀))
    (hzero : g x₀ y₀ = 0)
    (hInv : (fiberDeriv g x₀ y₀).IsInvertible)
    {h h' : X → E} (hcd : ContDiffAt ℝ 1 h x₀) (hh : h x₀ = y₀)
    (hcd' : ContDiffAt ℝ 1 h' x₀) (hh' : h' x₀ = y₀)
    (hz : ∀ᶠ x in 𝓝 x₀, g x (h x) = 0) (hz' : ∀ᶠ x in 𝓝 x₀, g x (h' x) = 0) :
    ∀ᶠ x in 𝓝 x₀, h' x = h x := by
  have hInv' : (fderiv ℝ (fun p : X × E => g p.1 p.2) (x₀, y₀) ∘L
      ContinuousLinearMap.inr ℝ X E).IsInvertible := by
    show (fiberDeriv g x₀ y₀).IsInvertible
    exact hInv
  set ψ := hg.implicitFunction (by norm_num) hInv' with hψ
  have hev : ∀ᶠ v : X × E in 𝓝 (x₀, y₀),
      (fun p : X × E => g p.1 p.2) v = (fun p : X × E => g p.1 p.2) (x₀, y₀) ↔
        ψ v.1 = v.2 :=
    hg.eventually_apply_eq_iff_implicitFunction (by norm_num) hInv'
  -- the set of points on which the implicit function theorem identifies the two roots
  set S : Set (X × E) :=
    {v | (fun p : X × E => g p.1 p.2) v = (fun p : X × E => g p.1 p.2) (x₀, y₀) ↔ ψ v.1 = v.2} with hS
  have hSin : S ∈ 𝓝 (x₀, y₀) := hev
  -- the graphs of `h` and `h'` pull the set `S` back to a neighbourhood of `x₀`
  have hpre : ∀ᶠ x in 𝓝 x₀, (x, h x) ∈ S := by
    have hc : ContinuousAt (fun x : X => (x, h x)) x₀ := by
      have h1 := ContinuousWithinAt.prodMk (s := (univ : Set X)) continuousAt_id.continuousWithinAt
        hcd.continuousAt.continuousWithinAt
      simpa only [id_eq] using h1.continuousAt Filter.univ_mem
    have hSin' : S ∈ 𝓝 (x₀, h x₀) := by simpa [hh] using hSin
    have h := hc.continuousWithinAt.preimage_mem_nhdsWithin (s := (univ : Set X)) hSin'
    rwa [nhdsWithin_univ] at h
  have hpre' : ∀ᶠ x in 𝓝 x₀, (x, h' x) ∈ S := by
    have hc : ContinuousAt (fun x : X => (x, h' x)) x₀ := by
      have h1 := ContinuousWithinAt.prodMk (s := (univ : Set X)) continuousAt_id.continuousWithinAt
        hcd'.continuousAt.continuousWithinAt
      simpa only [id_eq] using h1.continuousAt Filter.univ_mem
    have hSin' : S ∈ 𝓝 (x₀, h' x₀) := by simpa [hh'] using hSin
    have h := hc.continuousWithinAt.preimage_mem_nhdsWithin (s := (univ : Set X)) hSin'
    rwa [nhdsWithin_univ] at h
  have hψh : ∀ᶠ x in 𝓝 x₀, ψ x = h x := by
    have h1 := (Filter.Eventually.and hz hpre).mono (fun x hx => by
      rcases hx with ⟨hzx, hSx⟩
      have h2 : g x (h x) = g x₀ y₀ := by rw [hzx, hzero]
      exact (Set.mem_ofPred_eq.mp (hS ▸ hSx)).mp h2)
    exact h1
  have hψh' : ∀ᶠ x in 𝓝 x₀, ψ x = h' x := by
    have h1 := (Filter.Eventually.and hz' hpre').mono (fun x hx => by
      rcases hx with ⟨hzx, hSx⟩
      have h2 : g x (h' x) = g x₀ y₀ := by rw [hzx, hzero]
      exact (Set.mem_ofPred_eq.mp (hS ▸ hSx)).mp h2)
    exact h1
  exact (Filter.Eventually.and hψh' hψh).mono (fun x hx => by
    rcases hx with ⟨hx1, hx2⟩
    exact hx1.symm.trans hx2)


/-! ## 6. The coupled system with a local contraction hypothesis -/

omit [CompleteSpace X] in
/-- **The local fast-deviation estimate for the coupled system.** Consider the singularly perturbed
system `ẋ = f (x, y)`, `ε ẏ = g (x, y)` and the local slow manifold `y = h (x)` (`g (x, h x) = 0`).
Assume

* the fast field is one-sided contracting toward the slow manifold *locally*: for `z` in the region
  `Kx` and `u` within distance `δ` of `h z`,
  `⟪g z u - g z (h z), u - h z⟫ ≤ -ν ‖u - h z‖²` with `ν > 0`;
* the slow manifold moves with bounded speed: `‖D h z (f z u)‖ ≤ G`;
* the coupled solution stays within distance `δ` of the slow manifold (the *tube* hypothesis).

Then the fast variable tracks the slow manifold with an error that is `O (ε)`:

`‖y t - h (x t)‖² ≤ e^{-(ν/ε) t} ‖y 0 - h (x 0)‖² + (ε G / ν)²`.

This is the local version of `CRNT.SlowFast.fast_deviation_le`: the difference is that the
contraction hypothesis is required only *near the slow manifold*, not on a whole region. -/
theorem fast_deviation_le_local {f : X → E → X} {g : X → E → E} {h : X → E}
    (Dh : X → (X →L[ℝ] E)) {Kx : Set X} {ν G ε δ : ℝ}
    (hν : 0 < ν) (hε : 0 < ε)
    (hh : ∀ z ∈ Kx, HasFDerivAt h (Dh z) z)
    (hzero : ∀ z ∈ Kx, g z (h z) = 0)
    (hmono : ∀ z ∈ Kx, ∀ u, dist u (h z) ≤ δ → ⟪g z u - g z (h z), u - h z⟫ ≤ -ν * ‖u - h z‖ ^ 2)
    (hG : ∀ z ∈ Kx, ∀ u, ‖Dh z (f z u)‖ ≤ G)
    (x : ℝ → X) (y : ℝ → E)
    (hx : ∀ t, HasDerivAt x (f (x t) (y t)) t)
    (hy : ∀ t, HasDerivAt y ((1 / ε) • g (x t) (y t)) t)
    (hxK : ∀ t, x t ∈ Kx)
    (htube : ∀ t, dist (y t) (h (x t)) ≤ δ) :
    ∀ t, 0 ≤ t → ‖y t - h (x t)‖ ^ 2 ≤
      Real.exp (-(ν / ε * t)) * ‖y 0 - h (x 0)‖ ^ 2 + (ε * G / ν) ^ 2 := by
  intro t ht
  -- the fast deviation `e t = y t - h (x t)`
  set e : ℝ → E := fun t => y t - h (x t) with he
  have hcomp : ∀ s, HasDerivAt (fun r : ℝ => h (x r)) (Dh (x s) (f (x s) (y s))) s := by
    intro s
    exact (hh (x s) (hxK s)).comp_hasDerivAt s (hx s)
  have hed : ∀ s, HasDerivAt e
      ((1 / ε) • g (x s) (y s) - Dh (x s) (f (x s) (y s))) s := by
    intro s
    exact (hy s).sub (hcomp s)
  set Edev : ℝ → ℝ := fun t => ‖e t‖ ^ 2 with hE
  have hEder : ∀ s, HasDerivAt Edev
      (2 * ⟪e s, (1 / ε) • g (x s) (y s) - Dh (x s) (f (x s) (y s))⟫) s := by
    intro s
    have h := (hed s).inner ℝ (hed s)
    have hsym : ⟪e s, (1 / ε) • g (x s) (y s) - Dh (x s) (f (x s) (y s))⟫
        + ⟪(1 / ε) • g (x s) (y s) - Dh (x s) (f (x s) (y s)), e s⟫
        = 2 * ⟪e s, (1 / ε) • g (x s) (y s) - Dh (x s) (f (x s) (y s))⟫ := by
      rw [real_inner_comm]
      ring
    have hcast : (1 / ε) • g (x s) (y s) - Dh (x s) (f (x s) (y s))
        = (1 / ε) • g (x s) (y s) - Dh (x s) (f (x s) (y s)) := rfl
    rw [hsym] at h
    rw [show (fun r : ℝ => ⟪e r, e r⟫) = fun r : ℝ => ‖e r‖ ^ 2 by
      funext r; rw [real_inner_self_eq_norm_sq]] at h
    simpa [hE] using h
  -- the differential inequality for the fast deviation
  have hbound : ∀ s, (2 * ⟪e s, (1 / ε) • g (x s) (y s) - Dh (x s) (f (x s) (y s))⟫)
      ≤ -(ν / ε) * Edev s + (ε / ν) * G ^ 2 := by
    intro s
    set c : ℝ := 1 / ε with hc
    set k : ℝ := ν / ε with hk
    set m : ℝ := ε / ν with hm
    have hcpos : 0 < c := by simp [hc]; positivity
    have hkpos : 0 < k := by simp [hk]; positivity
    have hmpos : 0 < m := by simp [hm]; positivity
    have hkm : k * m = 1 := by rw [hk, hm]; field_simp
    have hkc : ν * c = k := by rw [hk, hc]; field_simp
    have hsqrtkm : Real.sqrt k * Real.sqrt m = 1 := by
      have h1 : Real.sqrt k * Real.sqrt m = Real.sqrt (k * m) :=
        (Real.sqrt_mul hkpos.le m).symm
      rw [h1, hkm, Real.sqrt_one]
    -- the arithmetic–geometric mean estimate `2 G ‖u‖ ≤ k ‖u‖² + m G²`
    have hAMGM : ∀ (u : E), 2 * G * ‖u‖ ≤ k * ‖u‖ ^ 2 + m * G ^ 2 := by
      intro u
      set a := Real.sqrt k * ‖u‖ with ha
      set b := Real.sqrt m * G with hb
      have hab : a * b = G * ‖u‖ := by
        rw [ha, hb]
        have h1 : Real.sqrt k * ‖u‖ * (Real.sqrt m * G)
            = (Real.sqrt k * Real.sqrt m) * (‖u‖ * G) := by ring
        rw [h1, hsqrtkm]
        ring
      have h2ab : 2 * (a * b) ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg (a - b)]
      have haa : a ^ 2 = k * ‖u‖ ^ 2 := by
        rw [ha]
        have h1 : (Real.sqrt k * ‖u‖) ^ 2 = (Real.sqrt k) ^ 2 * ‖u‖ ^ 2 := by ring
        rw [h1, Real.sq_sqrt (by positivity)]
      have hbb : b ^ 2 = m * G ^ 2 := by
        rw [hb]
        have h1 : (Real.sqrt m * G) ^ 2 = (Real.sqrt m) ^ 2 * G ^ 2 := by ring
        rw [h1, Real.sq_sqrt (by positivity)]
      have hfinal : 2 * G * ‖u‖ ≤ k * ‖u‖ ^ 2 + m * G ^ 2 := by
        have h2ab' : 2 * (a * b) ≤ a ^ 2 + b ^ 2 := h2ab
        rw [hab, haa, hbb] at h2ab'
        nlinarith [h2ab']
      exact hfinal
    -- the local contraction, applied at the slow-manifold point
    have hcon : ⟪y s - h (x s), g (x s) (y s) - g (x s) (h (x s))⟫
        ≤ -ν * ‖y s - h (x s)‖ ^ 2 := by
      have h5 := hmono (x s) (hxK s) (y s) (htube s)
      rwa [real_inner_comm] at h5
    have hzero' : g (x s) (h (x s)) = 0 := hzero (x s) (hxK s)
    have hinner : ⟪e s, g (x s) (y s) - g (x s) (h (x s))⟫ = ⟪e s, g (x s) (y s)⟫ := by
      have h1 : ⟪e s, g (x s) (y s) - g (x s) (h (x s))⟫
          = ⟪e s, g (x s) (y s)⟫ - ⟪e s, g (x s) (h (x s))⟫ := by
        rw [inner_sub_right]
      have h2 : ⟪e s, g (x s) (h (x s))⟫ = 0 := by rw [hzero', inner_zero_right]
      rw [h2, sub_zero] at h1
      exact h1
    have hcs' : -⟪e s, Dh (x s) (f (x s) (y s))⟫ ≤ ‖e s‖ * ‖Dh (x s) (f (x s) (y s))‖ := by
      have habs := abs_real_inner_le_norm (e s) (Dh (x s) (f (x s) (y s)))
      have hneg : -⟪e s, Dh (x s) (f (x s) (y s))⟫ ≤ |⟪e s, Dh (x s) (f (x s) (y s))⟫| :=
        neg_le_abs _
      linarith
    have hG' : ‖Dh (x s) (f (x s) (y s))‖ ≤ G := hG (x s) (hxK s) (y s)
    -- the contraction bound on the fast deviation
    have hes : e s = y s - h (x s) := by simp only [he]
    have hcon' : ⟪y s - h (x s), g (x s) (y s) - g (x s) (h (x s))⟫
        ≤ -ν * ‖e s‖ ^ 2 := by
      rw [hes]
      exact hcon
    have h1 : ⟪e s, g (x s) (y s)⟫ ≤ -ν * ‖e s‖ ^ 2 := by
      rw [← hinner]
      exact hcon'
    -- the assembly
    have hkey : 2 * (c * ⟪e s, g (x s) (y s)⟫ - ⟪e s, Dh (x s) (f (x s) (y s))⟫)
        ≤ -(2 * (ν * c)) * ‖e s‖ ^ 2 + 2 * G * ‖e s‖ := by
      have hA : c * ⟪e s, g (x s) (y s)⟫ ≤ c * (-ν * ‖e s‖ ^ 2) := by
        have hnn : 0 ≤ c := hcpos.le
        nlinarith [h1]
      have hB : -⟪e s, Dh (x s) (f (x s) (y s))⟫ ≤ ‖e s‖ * G := by
        have h2 : ‖e s‖ * ‖Dh (x s) (f (x s) (y s))‖ ≤ ‖e s‖ * G :=
          mul_le_mul_of_nonneg_left hG' (norm_nonneg _)
        linarith
      nlinarith
    have hfinal : 2 * (c * ⟪e s, g (x s) (y s)⟫ - ⟪e s, Dh (x s) (f (x s) (y s))⟫)
        ≤ -(ν * c) * ‖e s‖ ^ 2 + m * G ^ 2 := by
      have hAM := hAMGM (e s)
      rw [← hkc] at hAM
      nlinarith [hAM, hkey]
    -- transfer back to the statement
    have hsmul : ⟪e s, (1 / ε) • g (x s) (y s)⟫ = (1 / ε) * ⟪e s, g (x s) (y s)⟫ := by
      rw [real_inner_smul_right]
    have hsub : ⟪e s, (1 / ε) • g (x s) (y s) - Dh (x s) (f (x s) (y s))⟫
        = ⟪e s, (1 / ε) • g (x s) (y s)⟫
          - ⟪e s, Dh (x s) (f (x s) (y s))⟫ := by
      rw [inner_sub_right]
    have h2 : ν / ε = ν * c := by rw [hk.symm, hkc]
    calc 2 * ⟪e s, (1 / ε) • g (x s) (y s) - Dh (x s) (f (x s) (y s))⟫
        = 2 * ((1 / ε) * ⟪e s, g (x s) (y s)⟫ - ⟪e s, Dh (x s) (f (x s) (y s))⟫) := by
          rw [hsub, hsmul]
      _ = 2 * (c * ⟪e s, g (x s) (y s)⟫ - ⟪e s, Dh (x s) (f (x s) (y s))⟫) := by
          rw [hc.symm]
      _ ≤ -(ν * c) * ‖e s‖ ^ 2 + m * G ^ 2 := hfinal
      _ = -(ν / ε) * Edev s + (ε / ν) * G ^ 2 := by
          have hE' : Edev s = ‖e s‖ ^ 2 := by rw [hE]
          rw [hE', ← h2, ← hm.symm]

  -- Grönwall on the shifted deviation
  set φ : ℝ → ℝ := fun t => Edev t - (ε * G / ν) ^ 2 with hφ
  have hφder : ∀ s, HasDerivAt φ
      (2 * ⟪e s, (1 / ε) • g (x s) (y s) - Dh (x s) (f (x s) (y s))⟫) s := by
    intro s
    have h1 : HasDerivAt (fun r : ℝ => Edev r - (ε * G / ν) ^ 2)
        (2 * ⟪e s, (1 / ε) • g (x s) (y s) - Dh (x s) (f (x s) (y s))⟫) s := by
      have h2 := hEder s
      simpa [hE] using h2
    exact h1
  have hφbound : ∀ s ∈ Ico 0 t,
      (2 * ⟪e s, (1 / ε) • g (x s) (y s) - Dh (x s) (f (x s) (y s))⟫) ≤ -(ν / ε) * φ s := by
    intro s hs
    have hb := hbound s
    rw [hφ, hE]
    have hc : (ν / ε) * (ε * G / ν) ^ 2 = ε / ν * G ^ 2 := by
      field_simp
    nlinarith [hb]
  have hgron := CRNT.ExponentialDecay.le_mul_exp_of_deriv_le (V := φ)
    (V' := fun s => 2 * ⟪e s, (1 / ε) • g (x s) (y s) - Dh (x s) (f (x s) (y s))⟫)
    (K := -(ν / ε)) (b := t) hφder hφbound t ⟨ht, le_rfl⟩
  -- unpack
  have hc : (ν / ε) * (ε * G / ν) ^ 2 = ε / ν * G ^ 2 := by
    field_simp
  rw [hφ, hE] at hgron
  have hνε : 0 < ν / ε := div_pos hν hε
  have hexp : 0 ≤ Real.exp (-(ν / ε) * t) := (Real.exp_pos _).le
  have hgoal : ‖e t‖ ^ 2 ≤ Real.exp (-(ν / ε) * t) * ‖e 0‖ ^ 2 + (ε * G / ν) ^ 2 := by
    nlinarith [hgron]
  have hEt : ‖e t‖ ^ 2 = ‖y t - h (x t)‖ ^ 2 := by simp only [he]
  have hE0 : ‖e 0‖ ^ 2 = ‖y 0 - h (x 0)‖ ^ 2 := by simp only [he]
  have hexp_eq : Real.exp (-(ν / ε) * t) = Real.exp (-(ν / ε * t)) := by
    congr 1
    ring
  rw [hEt, hE0, hexp_eq] at hgoal
  exact hgoal


/-! ## 7. The local Tikhonov theorem -/

/-- **The local Tikhonov theorem.** Let `g : X → E → E` be `C¹` at `(x₀, y₀)`, let `g x₀ y₀ = 0`,
and suppose the fiber derivative `A = ∂_y g (x₀, y₀)` is *Hurwitz* (in the Lyapunov–Krasovskii
sense `CRNT.HurwitzRate`, with rate `μ > 0`). Then:

1. **the local slow manifold exists and is `C¹`**: there is a map `h : X → E` with `h x₀ = y₀` and
   `g (x, h x) = 0` for `x` close to `x₀` (`CRNT.exists_local_slow_manifold`);
2. **the fast field contracts locally**: there are a rate `ν > 0` and a radius `δ > 0` such that
   `g` is one-sided contracting toward `y₀` on the `δ`-ball (`CRNT.local_contraction_of_hurwitz`).

No *global* contraction hypothesis is used: the contraction is required only in a neighbourhood of
the fast equilibrium, and the stability of that equilibrium is read off from the Hurwitz condition
on its linearisation. The dynamical conclusions (the attraction of the frozen fast system and the
collapse of its `ε`-scaled version) are `CRNT.tikhonov_local_attraction`. -/
theorem tikhonov_local {g : X → E → E} {x₀ : X} {y₀ : E} {A : E →L[ℝ] E} {μ : ℝ}
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (hg : ContDiffAt ℝ 1 (fun p : X × E => g p.1 p.2) (x₀, y₀))
    (hzero : g x₀ y₀ = 0)
    (hderiv : HasFDerivAt (fun y : E => g x₀ y) A y₀)
    (hA : HurwitzRate A μ) (hμ : 0 < μ) :
    (∃ h : X → E, h x₀ = y₀ ∧ (∀ᶠ x in 𝓝 x₀, g x (h x) = 0) ∧ ContDiffAt ℝ 1 h x₀) ∧
    (∃ C : LocalContraction (fun y : E => g x₀ y) y₀, 0 < C.rate ∧ 0 < C.radius) := by
  -- the fiber derivative of `g` at `(x₀, y₀)` is the given Hurwitz linearisation `A`
  have hAeq : fiberDeriv g x₀ y₀ = A := by
    have h1 := fiberDeriv_hasFDerivAt hg
    exact h1.unique hderiv
  have hInv : (fiberDeriv g x₀ y₀).IsInvertible := by
    rw [hAeq]
    exact hurwitzRate_isInvertible hA hμ
  -- (1) the local slow manifold
  obtain ⟨h, hh0, hhz, hhc, _⟩ := exists_local_slow_manifold hg hzero hInv
  have hman : ∃ h : X → E, h x₀ = y₀ ∧ (∀ᶠ x in 𝓝 x₀, g x (h x) = 0) ∧ ContDiffAt ℝ 1 h x₀ :=
    ⟨h, hh0, hhz, hhc⟩
  -- (2) the local contraction
  have hC : LocalContraction (fun y : E => g x₀ y) y₀ :=
    local_contraction_of_hurwitz hderiv hzero hA hμ
  exact ⟨hman, ⟨hC, hC.rate_pos, hC.radius_pos⟩⟩

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] in
/-- **The dynamical conclusion of the local Tikhonov theorem.** Under the hypotheses of
`CRNT.tikhonov_local`, every integral curve `y` of the frozen fast field `ẏ = g (y)` that stays
close to the fast equilibrium `y₀` converges to `y₀` exponentially, and the `ε`-scaled frozen
solution `y (t/ε)` converges to `y₀` as `ε → 0⁺` for every fixed `t > 0`: the boundary layer of
the fast subsystem collapses onto the (Hurwitz) fast equilibrium. -/
theorem tikhonov_local_attraction {g : X → E → E} {x₀ : X} {y₀ : E} {A : E →L[ℝ] E} {μ : ℝ}
    (hzero : g x₀ y₀ = 0)
    (hderiv : HasFDerivAt (fun y : E => g x₀ y) A y₀)
    (hA : HurwitzRate A μ) (hμ : 0 < μ)
    (y : ℝ → E) (hy : ∀ t, HasDerivAt y (g x₀ (y t)) t) :
    ∃ C : LocalContraction (fun z : E => g x₀ z) y₀,
      (∀ t, 0 ≤ t → dist (y t) y₀ ≤ C.radius) →
      (∀ t, 0 < t → Tendsto (fun ε : ℝ => ‖y (t / ε) - y₀‖) (𝓝[>] 0) (𝓝 0)) ∧
      (∀ t, 0 ≤ t → ‖y t - y₀‖ ≤ ‖y 0 - y₀‖ * Real.exp (-C.rate * t)) := by
  have hC := local_contraction_of_hurwitz hderiv hzero hA hμ
  refine ⟨hC, ?_⟩
  intro hK
  refine ⟨?_, ?_⟩
  · intro t ht
    refine squeeze_zero' (f := fun ε : ℝ => ‖y (t / ε) - y₀‖)
      (g := fun ε : ℝ => ‖y 0 - y₀‖ * Real.exp (-(hC.rate * t) * (1 / ε)))
      (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hεpos : 0 < ε := hε
      have h1 : 0 ≤ t / ε := by positivity
      have h2 := frozen_attraction_local hzero hC.contraction hy hK (t / ε) h1
      have hexp_eq : Real.exp (-hC.rate * (t / ε))
          = Real.exp (-(hC.rate * t) * (1 / ε)) := by
        congr 1
        field_simp
      rw [hexp_eq] at h2
      exact h2
    · have hinv : Tendsto (fun ε : ℝ => 1 / ε) (𝓝[>] 0) atTop := by
        simpa only [inv_eq_one_div] using
          (tendsto_inv_nhdsGT_zero : Tendsto (fun x : ℝ => x⁻¹) (𝓝[>] 0) atTop)
      have hneg : Tendsto (fun ε : ℝ => -(hC.rate * t) * (1 / ε)) (𝓝[>] 0) atBot :=
        hinv.const_mul_atTop_of_neg (neg_lt_zero.mpr (mul_pos hC.rate_pos ht))
      have hexp : Tendsto (fun ε : ℝ => Real.exp (-(hC.rate * t) * (1 / ε))) (𝓝[>] 0) (𝓝 0) :=
        Real.tendsto_exp_atBot.comp hneg
      simpa using hexp.const_mul (‖y 0 - y₀‖)
  · intro t ht
    exact frozen_attraction_local hzero hC.contraction hy hK t ht

/-! ## 8. A concrete instance: the Michaelis–Menten fast subsystem -/

namespace MichaelisMenten

/-- The Michaelis–Menten fast field in the scalar fast variable: `g s c = s - (s + K) c`. In the
Segel–Slemrod scaling of the Michaelis–Menten kinetics this is the fast field of the substrate
`ṡ = -s + (s + K - λ) c`, `ε ċ = s - (s + K) c`. -/
def gFast (K : ℝ) (s c : ℝ) : ℝ := s - (s + K) * c

/-- The fiber derivative of the Michaelis–Menten fast field at `(s₀, ·)`: the linear map
`c ↦ -(s₀ + K) c`. -/
def gFastDeriv (K s₀ : ℝ) : ℝ →L[ℝ] ℝ := -((s₀ + K) • (ContinuousLinearMap.id ℝ ℝ))

/-- The fiber derivative of the Michaelis–Menten fast field is `gFastDeriv`. -/
theorem hasFDerivAt_gFast {K s₀ c₀ : ℝ} :
    HasFDerivAt (fun c => gFast K s₀ c) (gFastDeriv K s₀) c₀ := by
  have h0 : HasFDerivAt (fun c : ℝ => c) (ContinuousLinearMap.id ℝ ℝ) c₀ := hasFDerivAt_id c₀
  have h1 : HasFDerivAt (fun c : ℝ => (s₀ + K) * c)
      ((s₀ + K) • (ContinuousLinearMap.id ℝ ℝ)) c₀ := h0.const_mul _
  have h3 : HasFDerivAt (fun c : ℝ => s₀ - (s₀ + K) * c)
      (-((s₀ + K) • (ContinuousLinearMap.id ℝ ℝ))) c₀ := h1.const_sub s₀
  have h4 : (fun c => gFast K s₀ c) = (fun c : ℝ => s₀ - (s₀ + K) * c) := by
    funext c
    simp [gFast]
  rw [← h4] at h3
  exact h3

/-- **The Michaelis–Menten fiber derivative is Hurwitz.** At `(s₀, ·)` with `s₀ + K > 0`, the
fiber derivative `c ↦ -(s₀ + K) c` has rate `s₀ + K`: its (single) eigenvalue `-(s₀ + K)` has
negative real part, and the rate `s₀ + K` is positive. -/
theorem hurwitzRate_gFastDeriv {K s₀ : ℝ} (hK : 0 < K) (hs : 0 ≤ s₀) :
    HurwitzRate (gFastDeriv K s₀) (s₀ + K) ∧ 0 < s₀ + K := by
  have h1 : 0 < s₀ + K := by linarith
  constructor
  · intro w
    have h2 : ‖w‖ ^ 2 = w ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
    rw [h2]
    have h5 : ⟪gFastDeriv K s₀ w, w⟫ = -(s₀ + K) * w ^ 2 := by
      have h6 : ⟪gFastDeriv K s₀ w, w⟫ = -(s₀ + K) * w * w := by
        simp [gFastDeriv, smul_apply, smul_eq_mul]
        ring
      rw [h6]
      ring
    rw [h5]
  · exact h1

/-- The Michaelis–Menten fast field vanishes at the quasi-steady-state `c = s / (s + K)`. -/
theorem gFast_equilibrium {K s : ℝ} (hK : 0 < K) (hs : 0 ≤ s) :
    gFast K s (s / (s + K)) = 0 := by
  have h1 : 0 < s + K := by linarith
  have h2 : s + K ≠ 0 := ne_of_gt h1
  simp only [gFast]
  field_simp
  ring

/-- The Michaelis–Menten quasi-steady-state manifold `c = s / (s + K)` is the local slow manifold of
the reduced system. -/
def hFast (K : ℝ) (s : ℝ) : ℝ := s / (s + K)

/-- The quasi-steady-state manifold satisfies `g (s, h s) = 0`. -/
theorem zero_gFast_hFast {K s : ℝ} (hK : 0 < K) (hs : 0 ≤ s) : gFast K s (hFast K s) = 0 :=
  gFast_equilibrium hK hs

/-- **Local contraction of the Michaelis–Menten fast subsystem.** At a quasi-steady-state
`(s₀, c₀)` the fiber derivative `∂_c g = -(s₀ + K)` is Hurwitz with rate `s₀ + K > 0`, so the fast
field is one-sided contracting toward `c₀` in a neighbourhood of `c₀`. This is the local
contraction hypothesis of the local Tikhonov theorem, verified for the Michaelis–Menten kinetics. -/
theorem local_contraction_michaelisMenten {K s₀ c₀ : ℝ} (hK : 0 < K) (hs : 0 ≤ s₀)
    (hzero : gFast K s₀ c₀ = 0) :
    ∃ C : LocalContraction (fun c : ℝ => gFast K s₀ c) c₀, 0 < C.rate ∧ 0 < C.radius := by
  obtain ⟨hA, hApos⟩ := hurwitzRate_gFastDeriv hK hs
  have hC := local_contraction_of_hurwitz
    (hasFDerivAt_gFast (K := K) (s₀ := s₀) (c₀ := c₀)) hzero hA hApos
  exact ⟨hC, hC.rate_pos, hC.radius_pos⟩

/-- **The local Tikhonov theorem for the Michaelis–Menten fast subsystem.** At a quasi-steady-state
`(s₀, c₀)` the fiber derivative of the fast field is Hurwitz (rate `s₀ + K > 0`), hence the local
Tikhonov theorem applies: there is a local `C¹` slow manifold through `(s₀, c₀)` (the
quasi-steady-state manifold `c = s / (s + K)`), and the fast field contracts locally toward `c₀`. -/
theorem tikhonov_michaelisMenten {K s₀ c₀ : ℝ} (hK : 0 < K) (hs : 0 ≤ s₀)
    (hzero : gFast K s₀ c₀ = 0) :
    (∃ h : ℝ → ℝ, h s₀ = c₀ ∧ (∀ᶠ s in 𝓝 s₀, gFast K s (h s) = 0) ∧ ContDiffAt ℝ 1 h s₀) ∧
    (∃ C : LocalContraction (fun c : ℝ => gFast K s₀ c) c₀, 0 < C.rate ∧ 0 < C.radius) := by
  have hg : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => gFast K p.1 p.2) (s₀, c₀) := by
    have h0 : (fun p : ℝ × ℝ => gFast K p.1 p.2) = (fun p : ℝ × ℝ => p.1 - (p.1 + K) * p.2) := by
      funext p
      simp [gFast]
    rw [h0]
    fun_prop
  obtain ⟨hA, hApos⟩ := hurwitzRate_gFastDeriv hK hs
  exact tikhonov_local hg hzero (hasFDerivAt_gFast (K := K) (s₀ := s₀) (c₀ := c₀)) hA hApos

end MichaelisMenten

end

end CRNT
