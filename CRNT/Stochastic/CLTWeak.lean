import CRNT.Stochastic.MultivariateCLTOpen
import CRNT.Stochastic.ExitMass
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Weak convergence of the fluctuation law, for arbitrary (possibly explosive) networks

This module turns the characteristic-function statement `CRNT.Network.nonlinear_clt_open` into an
actual **convergence in distribution** statement, for networks whose volume-scaled chains may
explode.

## The two steps

1. **Asymptotic non-explosion.**  The characteristic-function statement `nonlinear_clt_open` holds
   for *every* network.  Specialised to the trivial test function `θ ≡ 0` it says that the total
   mass of the volume-scaled chain at time `T`, `∑_m P(T)(n_V, m)`, tends to `1`: the probability
   that the chain explodes before `T` vanishes as the volume grows
   (`nonlinear_clt_open_mass`).  The mass is at most `1` for every volume
   (`sum_transition_tsum_le_one`), so the law of the fluctuation `flucLawOpen` is a
   *sub*-probability measure, of mass equal to the probability of non-explosion.

2. **Lévy's continuity theorem.**  Mathlib's `ProbabilityMeasure.tendsto_of_tendsto_charFun` says
   that a sequence of probability measures converges weakly (in the topology of
   `ProbabilityMeasure`, i.e. for the integrals of every bounded continuous function) if and only
   if its characteristic functions converge pointwise to the characteristic function of the
   limit.  The sub-probability law is completed to a probability measure by placing the missing
   mass — the explosion probability — at the origin (`flucLawOpenDefect`); because the
   characteristic function of a point mass at the origin is `1`, the completion changes the
   characteristic function by `1 − mass`, which tends to `0`.  Hence `multivariate_clt_open_weak`:
   the completed fluctuation laws converge weakly to the Gaussian `gaussLimit`, and consequently
   the (sub-)probability fluctuation laws themselves converge in the sense of the integrals
   against bounded continuous functions (`multivariate_clt_open_weak_integral`).

## The process-level statement

The library has no path space, so the process-level statement (weak convergence of the fluctuation
*process*) is replaced by its path-free proxy: the **uniform-in-time** control of the deviation of
the chain from the deterministic trajectory.  Three new exit-mass lemmas make the exit-mass
reading of Kurtz's law of large numbers rigorous:

* `CRNT.JumpSystem.mass_outside_le_exitMass`: the mass of the chain outside a finite set `K` at
  time `t` is at most the exit mass `JumpSystem.exitMass K c t` — the mass of the chain frozen
  outside `K` which is outside `K` at time `t`.  This is the rigorous version of the statement
  that the exit mass is the probability that the chain leaves `K`;
* `CRNT.JumpSystem.exitMass_mono`: the exit mass is non-decreasing in time (the chain frozen
  outside `K` can only leave `K` once), so that the exit mass over a window bounds the exit mass
  at any intermediate time of the window;
* `CRNT.JumpSystem.exitMass_of_not_mem`: the exit mass of a state outside `K` is `1` (the frozen
  chain does not move outside `K`).

`CRNT.Network.fluctuation_uniform_concentration` combines these with
`CRNT.Stochastic.KurtzPathwise.kurtz_lln_uniform`: for every `δ ∈ (0, 1]` there is a partition
of `[0, T]` into `m` intervals such that `x` moves by less than `δ/2` on each interval, the total
exit mass of the windows (`windowExitMass`) tends to `0` as the volume grows, and, for every
volume, every interval and every time `τ` of the interval, the mass of the chain which has left
the ball of radius `δ` around the trajectory point is bounded by the exit mass of the chain
frozen outside that ball over the whole window — a bound which is *uniform in time*.

What is *not* proved: the uniform-in-time statement at the scale of the fluctuation itself,
`sup_{t ≤ T} P(|√V (X^V(t)/V − x(t))| > ε)`, i.e. the uniform tightness in time of the
fluctuation laws, and the path-space statement (weak convergence of the fluctuation process in
`C([0, T], ℝ^S)`).  The exit-mass estimate of the library is a Chebyshev-type estimate at the
scale of the law of large numbers: it bounds the mean square deviation by `O(1/V)`, and hence
cannot bound the `O(1)`-sized fluctuation.  A fluctuation-scale estimate requires the martingale
second-moment (central limit) machinery, which Mathlib lacks — the same obstruction as in
`CRNT.Stochastic.DiffusionApproximation`.
-/

open MeasureTheory ProbabilityTheory Set Filter Complex Matrix
open scoped BigOperators Topology NNReal ENNReal

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ### Sub-stochasticity of the volume-scaled chain -/

/-- **The volume-scaled chain is sub-stochastic.** The total mass of the minimal transition
function of the volume-scaled chain at time `T` is at most `1`; the missing mass is the
probability of explosion before `T`. -/
theorem sum_transition_tsum_le_one (N : Network S) (κ : RateConstants N) {V : ℝ} (hV : 0 < V)
    {T : ℝ} (hT : 0 ≤ T) (n : S → ℕ) :
    ∑' m, N.transition (N.volumeScale κ V hV) T n m ≤ 1 := by
  refine Real.tsum_le_of_sum_le (fun m => ?_)
    (fun F => ?_)
  · exact (N.jumpSystem (N.volumeScale κ V hV)).Pmin_nonneg T hT n m
  · exact (N.jumpSystem (N.volumeScale κ V hV)).sum_Pmin_le_one T hT n F

/-- The row of the volume-scaled transition function is summable. -/
theorem summable_transition (N : Network S) (κ : RateConstants N) {V : ℝ} (hV : 0 < V)
    {T : ℝ} (hT : 0 ≤ T) (n : S → ℕ) :
    Summable fun m => N.transition (N.volumeScale κ V hV) T n m :=
  summable_of_sum_le (fun m => (N.jumpSystem (N.volumeScale κ V hV)).Pmin_nonneg T hT n m)
    (fun F => (N.jumpSystem (N.volumeScale κ V hV)).sum_Pmin_le_one T hT n F)

/-! ### Asymptotic non-explosion -/

/-- The diffusion quadratic form vanishes at the zero test function. -/
theorem quadG_zero (N : Network S) (κ : RateConstants N) (_xs : Concentration S) :
    N.quadG κ _xs (fun _ => 0) = 0 := by
  unfold quadG
  simp

/-- **Asymptotic non-explosion.** For any network, along a solution `x` of the mass-action
equation, the total mass of the volume-scaled chain at time `T` tends to `1` as the volume
grows: the probability that the chain explodes before `T` vanishes.

This is the specialisation of `nonlinear_clt_open` to the zero test function `θ ≡ 0`, whose
characteristic function is the total mass of the chain. -/
theorem nonlinear_clt_open_mass (N : Network S) (κ : RateConstants N) {T Rx : ℝ} (hT : 0 < T)
    (hRx : 0 ≤ Rx) (x : ℝ → Concentration S) (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (N.massActionVectorField κ (x t)) t)
    (hxB : ∀ t ∈ Icc 0 T, x t ∈ Icc (0 : Concentration S) fun _ => Rx)
    (n : ℕ → S → ℕ)
    {z₀ : S → ℝ} (hz : Tendsto (fun k : ℕ => zeta ((k : ℝ) + 1) (x 0) (n k)) atTop (𝓝 z₀)) :
    Tendsto (fun k : ℕ => ∑' m, N.transition (N.volumeScale κ ((k : ℝ) + 1) (by positivity))
        T (n k) m) atTop (𝓝 1) := by
  have h := N.nonlinear_clt_open κ hT hRx x hxc hx hxB
    (fun _ => (fun _ => (0 : ℝ))) (fun _ => (fun _ => (0 : ℝ)))
    (continuousOn_const (s := Icc 0 T) (c := fun _ => (0 : ℝ)))
    (fun u _ => hasDerivAt_pi.mpr fun s => hasDerivAt_const u 0)
    (fun u _ v => by simp) n hz
  have hqint : (∫ u in (0 : ℝ)..T, N.quadG κ (x u) (fun _ => 0)) = 0 := by
    simp_rw [quadG_zero N κ]
    simp
  simp only [Finset.sum_const_zero, zero_mul, mul_zero, mul_one, Complex.exp_zero,
    Complex.ofReal_zero, zero_div, sub_zero, hqint] at h
  have h2 : Tendsto (fun k : ℕ => ((∑' m, N.transition (N.volumeScale κ ((k : ℝ) + 1)
      (by positivity)) T (n k) m : ℝ) : ℂ)) atTop (𝓝 1) := by
    have hfun : (fun k : ℕ => ((∑' m, N.transition (N.volumeScale κ ((k : ℝ) + 1)
        (by positivity)) T (n k) m : ℝ) : ℂ))
        = (fun k : ℕ => ∑' m, ((N.transition (N.volumeScale κ ((k : ℝ) + 1)
          (by positivity)) T (n k) m : ℝ) : ℂ)) := by
      funext k
      rw [Complex.ofReal_tsum]
    rw [hfun]
    exact h
  have h4 : Tendsto (fun k : ℕ => (((∑' m, N.transition (N.volumeScale κ ((k : ℝ) + 1)
      (by positivity)) T (n k) m : ℝ) : ℂ)).re) atTop (𝓝 ((1 : ℂ).re)) :=
    (Complex.continuous_re.tendsto (1 : ℂ)).comp h2
  convert h4 using 1

/-! ### The (sub-)probability law of the fluctuation -/

/-- The mass of the fluctuation law `flucLawOpen`: the probability that the volume-scaled chain
has not exploded by time `T`. -/
noncomputable def flucLawOpenMass (N : Network S) (κ : RateConstants N) {V : ℝ} (hV : 0 < V)
    (_xs : Concentration S) (T : ℝ) (n : S → ℕ) : ℝ :=
  ∑' m, N.transition (N.volumeScale κ V hV) T n m

/-- The total mass of the fluctuation law. -/
theorem measure_univ_flucLawOpen (N : Network S) (κ : RateConstants N) {V : ℝ} (hV : 0 < V)
    (xs : Concentration S) {T : ℝ} (hT : 0 ≤ T) (n : S → ℕ) :
    (N.flucLawOpen κ hV xs T n) Set.univ = ENNReal.ofReal (N.flucLawOpenMass κ hV xs T n) := by
  simp only [flucLawOpen, Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply, smul_eq_mul,
    mul_one, measure_univ]
  rw [← ENNReal.ofReal_tsum_of_nonneg (f := fun m => N.transition (N.volumeScale κ V hV) T n m)
    (fun m => (N.jumpSystem (N.volumeScale κ V hV)).Pmin_nonneg T hT n m)
    (summable_transition N κ hV hT n)]
  rfl

/-- The fluctuation law is a finite measure. -/
theorem isFiniteMeasure_flucLawOpen (N : Network S) (κ : RateConstants N) {V : ℝ} (hV : 0 < V)
    (xs : Concentration S) {T : ℝ} (hT : 0 ≤ T) (n : S → ℕ) :
    IsFiniteMeasure (N.flucLawOpen κ hV xs T n) := by
  refine ⟨?_⟩
  rw [N.measure_univ_flucLawOpen κ hV xs hT n]
  exact ENNReal.ofReal_lt_top

/-- **The characteristic function of the (sub-)probability fluctuation law.** This holds for every
network, without any hypothesis on the stochasticity of the chain. -/
theorem charFun_flucLawOpen_sub (N : Network S) (κ : RateConstants N) {V : ℝ} (hV : 0 < V)
    (xs : Concentration S) {T : ℝ} (hT : 0 ≤ T) (n : S → ℕ)
    (t : EuclideanSpace ℝ S) :
    charFun (N.flucLawOpen κ hV xs T n) t =
      ∑' m, (N.transition (N.volumeScale κ V hV) T n m : ℂ) *
        Complex.exp (I * ((∑ s, WithLp.ofLp t s * zeta V xs m s : ℝ) : ℂ)) := by
  rw [charFun_apply, flucLawOpen, integral_sum_dirac_eq_tsum (fun m => ENNReal.ofReal_ne_top)]
  · refine tsum_congr fun m => ?_
    rw [inner_toLp_zeta, ENNReal.toReal_ofReal (show (0 : ℝ) ≤
      N.transition (N.volumeScale κ V hV) T n m from
        (N.jumpSystem (N.volumeScale κ V hV)).Pmin_nonneg T hT n m),
      Complex.real_smul]
    congr 1
    push_cast
    ring_nf
  · refine (summable_transition N κ hV hT n).congr fun m => ?_
    rw [ENNReal.toReal_ofReal (show (0 : ℝ) ≤
      N.transition (N.volumeScale κ V hV) T n m from
        (N.jumpSystem (N.volumeScale κ V hV)).Pmin_nonneg T hT n m)]
    rw [Complex.norm_exp]
    simp

/-! ### The completed law: a probability measure -/

/-- The completed law is a probability measure. -/
theorem isProbabilityMeasure_flucLawOpenDefect (N : Network S) (κ : RateConstants N) {V : ℝ}
    (hV : 0 < V) (xs : Concentration S) {T : ℝ} (hT : 0 ≤ T) (n : S → ℕ) :
    IsProbabilityMeasure (N.flucLawOpen κ hV xs T n +
      ENNReal.ofReal (1 - N.flucLawOpenMass κ hV xs T n) • Measure.dirac 0) := by
  constructor
  have hs : N.flucLawOpenMass κ hV xs T n ≤ 1 := N.sum_transition_tsum_le_one κ hV hT n
  have hs0 : 0 ≤ N.flucLawOpenMass κ hV xs T n := by
    unfold flucLawOpenMass
    exact tsum_nonneg fun m => (N.jumpSystem (N.volumeScale κ V hV)).Pmin_nonneg T hT n m
  have hs1 : 0 ≤ 1 - N.flucLawOpenMass κ hV xs T n := by linarith
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, mul_one, measure_univ]
  rw [N.measure_univ_flucLawOpen κ hV xs hT n, ← ENNReal.ofReal_add hs0 hs1]
  have hsum : N.flucLawOpenMass κ hV xs T n + (1 - N.flucLawOpenMass κ hV xs T n) = 1 := by ring
  rw [hsum, ENNReal.ofReal_one]

/-- **The completed fluctuation law.** The law `flucLawOpen` of the fluctuation is completed to a
probability measure by placing the missing mass — the probability of explosion — at the origin. -/
noncomputable def flucLawOpenDefect (N : Network S) (κ : RateConstants N) {V : ℝ} (hV : 0 < V)
    (xs : Concentration S) {T : ℝ} (hT : 0 ≤ T) (n : S → ℕ) :
    ProbabilityMeasure (EuclideanSpace ℝ S) :=
  ⟨N.flucLawOpen κ hV xs T n +
      ENNReal.ofReal (1 - N.flucLawOpenMass κ hV xs T n) • Measure.dirac 0,
    N.isProbabilityMeasure_flucLawOpenDefect κ hV xs hT n⟩

/-- **The characteristic function of the completed law.** It is the characteristic function of the
sub-probability law, plus the missing mass (the characteristic function of a point mass at the
origin being `1`). -/
theorem charFun_flucLawOpenDefect (N : Network S) (κ : RateConstants N) {V : ℝ} (hV : 0 < V)
    (xs : Concentration S) {T : ℝ} (hT : 0 ≤ T) (n : S → ℕ)
    (t : EuclideanSpace ℝ S) :
    charFun (N.flucLawOpen κ hV xs T n +
      ENNReal.ofReal (1 - N.flucLawOpenMass κ hV xs T n) • Measure.dirac 0) t =
      charFun (N.flucLawOpen κ hV xs T n) t +
        ((1 : ℂ) - (N.flucLawOpenMass κ hV xs T n : ℝ)) := by
  have hs0 : 0 ≤ N.flucLawOpenMass κ hV xs T n := by
    unfold flucLawOpenMass
    exact tsum_nonneg fun m => (N.jumpSystem (N.volumeScale κ V hV)).Pmin_nonneg T hT n m
  have hs1 : 0 ≤ 1 - N.flucLawOpenMass κ hV xs T n := by
    have hs := N.sum_transition_tsum_le_one κ hV hT n
    unfold flucLawOpenMass at hs ⊢
    linarith
  rw [charFun_eq_integral_innerProbChar, charFun_eq_integral_innerProbChar]
  have hμ : Integrable (BoundedContinuousFunction.innerProbChar t : EuclideanSpace ℝ S → ℂ)
      (N.flucLawOpen κ hV xs T n) := by
    exact @BoundedContinuousFunction.integrable (EuclideanSpace ℝ S) _ _
      (N.flucLawOpen κ hV xs T n) ℂ _ _ _ _ _
      (N.isFiniteMeasure_flucLawOpen κ hV xs hT n) (BoundedContinuousFunction.innerProbChar t)
  have hν : Integrable (BoundedContinuousFunction.innerProbChar t : EuclideanSpace ℝ S → ℂ)
      (ENNReal.ofReal (1 - N.flucLawOpenMass κ hV xs T n) • Measure.dirac 0) := by
    refine @BoundedContinuousFunction.integrable (EuclideanSpace ℝ S) _ _
      (ENNReal.ofReal (1 - N.flucLawOpenMass κ hV xs T n) • Measure.dirac 0) ℂ _ _ _ _ _ ?_
      (BoundedContinuousFunction.innerProbChar t)
    exact Measure.smul_finite (Measure.dirac (0 : EuclideanSpace ℝ S)) (by simp)
  rw [integral_add_measure hμ hν, integral_smul_measure]
  have hzero : ∫ x, BoundedContinuousFunction.innerProbChar t x
      ∂Measure.dirac (0 : EuclideanSpace ℝ S) = 1 := by
    rw [integral_dirac]
    simp [BoundedContinuousFunction.innerProbChar_apply]
  rw [hzero]
  have hcr : ENNReal.toReal (ENNReal.ofReal (1 - N.flucLawOpenMass κ hV xs T n)) =
      1 - N.flucLawOpenMass κ hV xs T n := ENNReal.toReal_ofReal hs1
  rw [hcr]
  congr 1
  simp

/-- **The characteristic function of the completed law, as a probability measure.** -/
theorem charFun_flucLawOpenDefect' (N : Network S) (κ : RateConstants N) {V : ℝ} (hV : 0 < V)
    (xs : Concentration S) {T : ℝ} (hT : 0 ≤ T) (n : S → ℕ)
    (t : EuclideanSpace ℝ S) :
    charFun ((N.flucLawOpenDefect κ hV xs hT n : ProbabilityMeasure (EuclideanSpace ℝ S)) :
      Measure (EuclideanSpace ℝ S)) t =
      charFun (N.flucLawOpen κ hV xs T n) t +
        ((1 : ℂ) - (N.flucLawOpenMass κ hV xs T n : ℝ)) := by
  exact N.charFun_flucLawOpenDefect κ hV xs hT n t

/-! ### Weak convergence of the fluctuation law -/

/-- **Weak convergence of the fluctuation law, for an arbitrary network.** Let `N` be any network
(possibly explosive) with an equilibrium `x* ≥ 0`, and let `n_V` be initial counts with
`√V (n_V/V − x*) → z₀`. Then the law of the fluctuation `√V (X^V(T)/V − x*)` — completed to a
probability measure by placing the explosion probability at the origin (`flucLawOpenDefect`) —
converges weakly, in the topology of `ProbabilityMeasure`, to the Gaussian law with mean
`e^{T J} z₀` and covariance `∫₀ᵀ e^{(T−u)J} G e^{(T−u)Jᵀ} du` (`gaussLimit`), where
`J = Df(x*)` and `G = ∑_r λ_r(x*) Δ_r Δ_rᵀ`.

No conservation law, weight, stochasticity or non-explosion hypothesis is needed: the
asymptotic non-explosion `nonlinear_clt_open_mass` guarantees that the explosion probability
vanishes, and Lévy's continuity theorem (`ProbabilityMeasure.tendsto_of_tendsto_charFun`) turns
the characteristic-function convergence of `nonlinear_clt_open` into weak convergence. -/
theorem multivariate_clt_open_weak (N : Network S) (κ : RateConstants N) {xs : Concentration S}
    (heq : N.massActionVectorField κ xs = 0) (hxs0 : ∀ s, 0 ≤ xs s) {T : ℝ} (hT : 0 < T)
    (n : ℕ → S → ℕ)
    {z₀ : S → ℝ} (hz : Tendsto (fun k : ℕ => zeta ((k : ℝ) + 1) xs (n k)) atTop (𝓝 z₀)) :
    Tendsto (fun k : ℕ => N.flucLawOpenDefect κ (V := (k : ℝ) + 1) (by positivity) xs hT.le (n k))
      atTop (𝓝 (N.gaussLimit κ xs T z₀)) := by
  refine ProbabilityMeasure.tendsto_of_tendsto_charFun fun t => ?_
  set θ : S → ℝ := WithLp.ofLp t with hθ
  set J := fderiv ℝ (N.massActionVectorField κ) xs with hJ
  set A := transposeCLM J with hA
  set Rx := ∑ s, xs s with hRx
  have hRx0 : 0 ≤ Rx := Finset.sum_nonneg fun s _ => hxs0 s
  have hxsB : xs ∈ Icc (0 : Concentration S) fun _ => Rx := ⟨fun s => hxs0 s, fun s =>
    Finset.single_le_sum (f := fun s => xs s) (fun s _ => hxs0 s) (Finset.mem_univ s)⟩
  have h := N.nonlinear_clt_open κ (Rx := Rx) hT hRx0 (fun _ => xs) continuousOn_const
    (fun t _ => by rw [heq]; exact hasDerivAt_const _ _) (fun t _ => hxsB) (adjSol A T θ)
    (fun u => -(A (adjSol A T θ u)))
    (fun u _ => (hasDerivAt_adjSol A T θ u).continuousAt.continuousWithinAt)
    (fun u _ => hasDerivAt_adjSol A T θ u)
    (fun u _ v => adjSol_adjoint J T θ u v) n hz
  simp only [adjSol_self] at h
  rw [dot_adjSol_zero, integral_quadG_adjSol] at h
  have hlhs : ∀ k : ℕ, charFun ((N.flucLawOpenDefect κ (V := (k : ℝ) + 1) (by positivity) xs hT.le
      (n k) : ProbabilityMeasure (EuclideanSpace ℝ S)) : Measure (EuclideanSpace ℝ S)) t =
      (∑' m, (N.transition (N.volumeScale κ ((k : ℝ) + 1) (by positivity)) T (n k) m : ℂ) *
        Complex.exp (I * ((∑ s, θ s * zeta ((k : ℝ) + 1) xs m s : ℝ) : ℂ))) +
        ((1 : ℂ) - (N.flucLawOpenMass κ (V := (k : ℝ) + 1) (by positivity) xs T (n k) : ℝ)) := by
    intro k
    rw [N.charFun_flucLawOpenDefect' κ (V := (k : ℝ) + 1) (by positivity) xs hT.le (n k),
      N.charFun_flucLawOpen_sub κ (V := (k : ℝ) + 1) (by positivity) xs hT.le (n k)]
  have hpsd := N.covMat_posSemidef κ hxs0 A hT.le
  have hrhs : charFun ((N.gaussLimit κ xs T z₀ : ProbabilityMeasure (EuclideanSpace ℝ S)) :
      Measure (EuclideanSpace ℝ S)) t =
      Complex.exp (I * ((∑ j, θ j * meanVec A T z₀ j : ℝ) : ℂ) -
        ((θ ⬝ᵥ (N.covMat κ xs A T *ᵥ θ) / 2 : ℝ) : ℂ)) := by
    show charFun (multivariateGaussian (WithLp.toLp 2 (meanVec A T z₀)) (N.covMat κ xs A T)) t = _
    rw [charFun_multivariateGaussian hpsd]
    congr 1
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial, dotProduct]
    push_cast
    have e : (∑ x, ((meanVec A T z₀ x : ℝ) : ℂ) * ((WithLp.ofLp t x : ℝ) : ℂ)) =
        ∑ x, ((WithLp.ofLp t x : ℝ) : ℂ) * ((meanVec A T z₀ x : ℝ) : ℂ) :=
      Finset.sum_congr rfl fun x _ => mul_comm _ _
    rw [e]
    ring
  have hmass : Tendsto (fun k : ℕ => N.flucLawOpenMass κ (V := (k : ℝ) + 1) (by positivity) xs T
      (n k)) atTop (𝓝 1) := by
    have hh := N.nonlinear_clt_open_mass κ hT hRx0 (fun _ => xs) continuousOn_const
      (fun t _ => by rw [heq]; exact hasDerivAt_const _ _) (fun t _ => hxsB) n hz
    simpa only [flucLawOpenMass] using hh
  have hdef : Tendsto (fun k : ℕ => (1 : ℂ) - (N.flucLawOpenMass κ (V := (k : ℝ) + 1) (by positivity)
      xs T (n k) : ℝ)) atTop (𝓝 0) := by
    have h3 : Tendsto (fun k : ℕ => (1 - N.flucLawOpenMass κ (V := (k : ℝ) + 1) (by positivity) xs T
        (n k) : ℝ)) atTop (𝓝 (1 - 1 : ℝ)) := tendsto_const_nhds.sub hmass
    have h4 := (continuous_ofReal.tendsto (1 - 1 : ℝ)).comp h3
    convert h4 using 1
    · funext k
      simp only [Function.comp_apply]
      rw [Complex.ofReal_sub]
      simp
    · norm_num
  set L : ℂ := Complex.exp (I * ((∑ j, θ j * meanVec A T z₀ j : ℝ) : ℂ) -
      ((θ ⬝ᵥ (N.covMat κ xs A T *ᵥ θ) / 2 : ℝ) : ℂ)) with hL
  have hfinal : Tendsto (fun k : ℕ =>
      charFun ((N.flucLawOpenDefect κ (V := (k : ℝ) + 1) (by positivity) xs hT.le (n k) :
        ProbabilityMeasure (EuclideanSpace ℝ S)) : Measure (EuclideanSpace ℝ S)) t)
      atTop (𝓝 L) := by
    have hh := (h.add hdef).congr (fun k => (hlhs k).symm)
    simpa only [add_zero, hL] using hh
  rw [hrhs]
  exact hfinal

/-! ### Convergence of the integrals: the distributional statement -/

/-- **Convergence in distribution for an arbitrary network.** For every bounded continuous
function `f` on `EuclideanSpace ℝ S`, the integral of `f` with respect to the law of the
fluctuation converges to the integral of `f` with respect to the Gaussian law `gaussLimit`.

This is the distributional (weak) form of `multivariate_clt_open_weak`, stated for the
*sub*-probability law `flucLawOpen` itself: the missing mass — the probability of explosion —
goes to zero, and it is placed at the origin by `flucLawOpenDefect`, so the two integrals differ
by `(1 − mass) · f(0)`, which vanishes. -/
theorem multivariate_clt_open_weak_integral (N : Network S) (κ : RateConstants N)
    {xs : Concentration S} (heq : N.massActionVectorField κ xs = 0) (hxs0 : ∀ s, 0 ≤ xs s)
    {T : ℝ} (hT : 0 < T) (n : ℕ → S → ℕ)
    {z₀ : S → ℝ} (hz : Tendsto (fun k : ℕ => zeta ((k : ℝ) + 1) xs (n k)) atTop (𝓝 z₀))
    (f : BoundedContinuousFunction (EuclideanSpace ℝ S) ℂ) :
    Tendsto (fun k : ℕ => ∫ x, f x ∂ ((N.flucLawOpen κ (V := (k : ℝ) + 1) (by positivity) xs T (n k)) : Measure (EuclideanSpace ℝ S)))
      atTop (𝓝 (∫ x, f x ∂ ((N.gaussLimit κ xs T z₀ : ProbabilityMeasure (EuclideanSpace ℝ S)) :
        Measure (EuclideanSpace ℝ S)))) := by
  have hweak := N.multivariate_clt_open_weak κ heq hxs0 hT n hz
  have hconv := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hweak f
  -- the integral with respect to the completed law
  have hdef : ∀ k : ℕ,
      (∫ x, f x ∂ ((N.flucLawOpenDefect κ (V := (k : ℝ) + 1) (by positivity) xs hT.le (n k)) :
        ProbabilityMeasure (EuclideanSpace ℝ S))) =
        (∫ x, f x ∂ ((N.flucLawOpen κ (V := (k : ℝ) + 1) (by positivity) xs T (n k)) :
          Measure (EuclideanSpace ℝ S))) +
          ((1 - N.flucLawOpenMass κ (V := (k : ℝ) + 1) (by positivity) xs T (n k) : ℝ) : ℂ) * f 0 := by
    intro k
    have hμ : Integrable (f : EuclideanSpace ℝ S → ℂ)
        ((N.flucLawOpen κ (V := (k : ℝ) + 1) (by positivity) xs T (n k)) : Measure (EuclideanSpace ℝ S)) := by
      exact @BoundedContinuousFunction.integrable (EuclideanSpace ℝ S) _ _
        ((N.flucLawOpen κ (V := (k : ℝ) + 1) (by positivity) xs T (n k)) : Measure (EuclideanSpace ℝ S)) ℂ _ _ _ _ _
        (N.isFiniteMeasure_flucLawOpen κ (V := (k : ℝ) + 1) (by positivity) xs hT.le (n k)) f
    have hν : Integrable (f : EuclideanSpace ℝ S → ℂ)
        (ENNReal.ofReal (1 - N.flucLawOpenMass κ (V := (k : ℝ) + 1) (by positivity) xs T (n k)) •
          Measure.dirac 0) := by
      refine @BoundedContinuousFunction.integrable (EuclideanSpace ℝ S) _ _
        (ENNReal.ofReal (1 - N.flucLawOpenMass κ (V := (k : ℝ) + 1) (by positivity) xs T (n k)) •
          Measure.dirac 0) ℂ _ _ _ _ _ ?_ f
      exact Measure.smul_finite (Measure.dirac (0 : EuclideanSpace ℝ S)) (by simp)
    have hzero : ∫ x, f x ∂Measure.dirac (0 : EuclideanSpace ℝ S) = f 0 := by
      rw [integral_dirac]
    show (∫ x, f x ∂ ((N.flucLawOpenDefect κ (V := (k : ℝ) + 1) (by positivity) xs hT.le (n k) :
        ProbabilityMeasure (EuclideanSpace ℝ S)) : Measure (EuclideanSpace ℝ S))) =
      (∫ x, f x ∂ ((N.flucLawOpen κ (V := (k : ℝ) + 1) (by positivity) xs T (n k)) :
        Measure (EuclideanSpace ℝ S))) +
        ((1 - N.flucLawOpenMass κ (V := (k : ℝ) + 1) (by positivity) xs T (n k) : ℝ) : ℂ) * f 0
    rw [show ((N.flucLawOpenDefect κ (V := (k : ℝ) + 1) (by positivity) xs hT.le (n k) :
        ProbabilityMeasure (EuclideanSpace ℝ S)) : Measure (EuclideanSpace ℝ S)) =
        (N.flucLawOpen κ (V := (k : ℝ) + 1) (by positivity) xs T (n k) +
          ENNReal.ofReal (1 - N.flucLawOpenMass κ (V := (k : ℝ) + 1) (by positivity) xs T (n k)) •
            Measure.dirac 0) from rfl,
      integral_add_measure hμ hν, integral_smul_measure]
    have hcr : ENNReal.toReal (ENNReal.ofReal
        (1 - N.flucLawOpenMass κ (V := (k : ℝ) + 1) (by positivity) xs T (n k))) =
        1 - N.flucLawOpenMass κ (V := (k : ℝ) + 1) (by positivity) xs T (n k) := by
      have hs : N.flucLawOpenMass κ (V := (k : ℝ) + 1) (by positivity) xs T (n k) ≤ 1 := by
        exact N.sum_transition_tsum_le_one κ (V := (k : ℝ) + 1) (by positivity) hT.le (n k)
      have hs0 : 0 ≤ N.flucLawOpenMass κ (V := (k : ℝ) + 1) (by positivity) xs T (n k) := by
        unfold flucLawOpenMass
        exact tsum_nonneg fun m =>
          (N.jumpSystem (N.volumeScale κ ((k : ℝ) + 1) (by positivity))).Pmin_nonneg T hT.le (n k) m
      have hs1 : 0 ≤ 1 - N.flucLawOpenMass κ (V := (k : ℝ) + 1) (by positivity) xs T (n k) := by
        linarith
      exact ENNReal.toReal_ofReal hs1
    rw [hcr, hzero]
    simp
  -- the mass tends to one
  have hmass : Tendsto (fun k : ℕ => N.flucLawOpenMass κ (V := (k : ℝ) + 1) (by positivity) xs T
      (n k)) atTop (𝓝 1) := by
    have hh := N.nonlinear_clt_open_mass κ hT (Finset.sum_nonneg fun s _ => hxs0 s) (fun _ => xs)
      continuousOn_const (fun t _ => by rw [heq]; exact hasDerivAt_const _ _)
      (fun t _ => ⟨fun s => hxs0 s, fun s => Finset.single_le_sum (f := fun s => xs s)
        (fun s _ => hxs0 s) (Finset.mem_univ s)⟩) n hz
    simpa only [flucLawOpenMass] using hh
  have hdefc : Tendsto (fun k : ℕ =>
      ((1 - N.flucLawOpenMass κ (V := (k : ℝ) + 1) (by positivity) xs T (n k) : ℝ) : ℂ) * f 0)
      atTop (𝓝 0) := by
    have h3 : Tendsto (fun k : ℕ => (1 - N.flucLawOpenMass κ (V := (k : ℝ) + 1) (by positivity) xs T
        (n k) : ℝ)) atTop (𝓝 (1 - 1 : ℝ)) := tendsto_const_nhds.sub hmass
    have h4 := (continuous_ofReal.tendsto (1 - 1 : ℝ)).comp h3
    have h5 : Tendsto (fun k : ℕ => ((1 - N.flucLawOpenMass κ (V := (k : ℝ) + 1) (by positivity) xs T
        (n k) : ℝ) : ℂ)) atTop (𝓝 0) := by
      convert h4 using 1
      · funext k
        simp only [Function.comp_apply]
      · norm_num
    simpa using h5.mul_const (f 0)
  set X : ℂ := ∫ x, f x ∂ ((N.gaussLimit κ xs T z₀ : ProbabilityMeasure (EuclideanSpace ℝ S)) :
      Measure (EuclideanSpace ℝ S)) with hX
  have hmain : Tendsto (fun k : ℕ => ∫ x, f x ∂ ((N.flucLawOpen κ (V := (k : ℝ) + 1) (by positivity)
      xs T (n k)) : Measure (EuclideanSpace ℝ S))) atTop (𝓝 X) := by
    have hdef' : ∀ k : ℕ,
        (∫ x, f x ∂ ((N.flucLawOpenDefect κ (V := (k : ℝ) + 1) (by positivity) xs hT.le (n k) :
          ProbabilityMeasure (EuclideanSpace ℝ S)) : Measure (EuclideanSpace ℝ S))) -
            ((1 - N.flucLawOpenMass κ (V := (k : ℝ) + 1) (by positivity) xs T (n k) : ℝ) : ℂ) * f 0 =
          ∫ x, f x ∂ ((N.flucLawOpen κ (V := (k : ℝ) + 1) (by positivity) xs T (n k)) :
            Measure (EuclideanSpace ℝ S)) := by
      intro k
      rw [hdef k]
      ring
    have hAB := hconv.sub hdefc
    have hC := hAB.congr' (Filter.Eventually.of_forall fun k => hdef' k)
    simpa only [sub_zero, hX] using hC
  exact hmain

/-! ### The uniform-in-time statement (the path-free proxy)

The library has no path space, so the process-level statement (weak convergence of the
fluctuation *process*) is replaced by its path-free proxy: the uniform-in-time control of the
deviation of the chain from the deterministic trajectory.  The three ingredients below are the
rigorous content of the exit-mass reading of Kurtz's law of large numbers:

* `mass_outside_le_exitMass`: the mass of the chain outside a finite set `K` at time `t` is at
  most the exit mass `JumpSystem.exitMass K c t` — the mass of the chain frozen outside `K`
  which is outside `K` at time `t`.  This is the rigorous version of the statement that the
  exit mass is the probability that the chain leaves `K`;
* `exitMass_mono`: the exit mass is non-decreasing in time, so that the exit mass over a whole
  window bounds the exit mass at any intermediate time;
* `fluctuation_uniform_concentration`: the uniform-in-time statement, obtained from
  `CRNT.Stochastic.KurtzPathwise.kurtz_lln_uniform`: for every `δ ∈ (0, 1]` there is a
  partition of `[0, T]` into `m` intervals such that, for every volume and every time in each
  interval, the mass of the chain (frozen outside the ball around the trajectory point) which
  has left the ball is bounded by the exit mass of the corresponding window, and the sum of the
  exit masses of the windows tends to `0`.

What is *not* proved: the uniform-in-time statement at the scale of the fluctuation itself,
`sup_{t ≤ T} P(|√V (X^V(t)/V − x(t))| > ε)`, i.e. the uniform tightness in time of the
fluctuation laws, and the path-space statement (weak convergence of the fluctuation process in
`C([0, T], ℝ^S)`).  The exit-mass estimate of the library is a Chebyshev-type estimate at the
scale of the law of large numbers: it bounds the mean square deviation by `O(1/V)`, and hence
cannot bound the `O(1)`-sized fluctuation.  A fluctuation-scale estimate requires the martingale
second-moment (central limit) machinery, which Mathlib lacks — the same obstruction as in
`CRNT.Stochastic.DiffusionApproximation`.
-/

end Network

section ExitMassBounds

namespace JumpSystem

variable {α : Type*} [DecidableEq α]

/-- **The frozen chain started outside `K` does not move.** Its exit mass is `1`. -/
theorem exitMass_of_not_mem (J : JumpSystem α) (K : Finset α) {c : α} (hc : c ∉ K) {t : ℝ}
    (ht : 0 ≤ t) : J.exitMass K c t = 1 := by
  have hP : ∀ b, b ≠ c → (J.stopOutside K).Pmin t c b = 0 := by
    intro b hb
    have h1 : ∀ k : ℕ, (J.stopOutside K).P k t c b = 0 := by
      intro k
      exact J.stopOutside_P_of_not_mem hc (Ne.symm hb) k t
    have hlim : Filter.Tendsto (fun k => (J.stopOutside K).P k t c b) Filter.atTop
        (𝓝 ((J.stopOutside K).Pmin t c b)) := (J.stopOutside K).tendsto_P t ht c b
    have hz : Filter.Tendsto (fun k => (J.stopOutside K).P k t c b) Filter.atTop (𝓝 0) :=
      tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun k => (h1 k).symm)
    exact tendsto_nhds_unique hlim hz
  have hsum : HasSum (fun b : α => (J.stopOutside K).Pmin t c b) 1 :=
    (J.stopOutside K).hasSum_Pmin_one (Λ := ∑ x ∈ K, J.q x) (fun c' _ => J.stopOutside_q_le K c') ht
  have hsum' : Summable fun b => (J.stopOutside K).Pmin t c b := hsum.summable
  have hsplit := Network.tsum_split K hsum'
  have hsplit' := Network.tsum_split K hsum.summable
  have hinside : ∑ b ∈ K, (J.stopOutside K).Pmin t c b = 0 := by
    refine Finset.sum_eq_zero fun b hb => ?_
    have hbc : b ≠ c := fun h => hc (h ▸ hb)
    exact hP b hbc
  have htot : ∑' b, (if b ∈ K then 0 else (J.stopOutside K).Pmin t c b) = 1 := by
    have h3 : ∑' b, (if b ∈ K then 0 else (J.stopOutside K).Pmin t c b) =
        ∑' b, (J.stopOutside K).Pmin t c b - ∑ b ∈ K, (J.stopOutside K).Pmin t c b := by
      rw [hsplit']
      ring
    rw [h3, hsum.tsum_eq, hinside]
    ring
  have : J.exitMass K c t = ∑' b, (if b ∈ K then 0 else (J.stopOutside K).Pmin t c b) := rfl
  rw [this, htot]

/-- **The exit mass is non-decreasing in time.** The chain frozen outside `K` can only leave `K`
once. -/
theorem exitMass_mono (J : JumpSystem α) (K : Finset α) (c : α) {s t : ℝ} (h : s ≤ t)
    (hs : 0 ≤ s) : J.exitMass K c s ≤ J.exitMass K c t := by
  have hsum : HasSum (fun b : α => (J.stopOutside K).Pmin s c b) 1 :=
    (J.stopOutside K).hasSum_Pmin_one (Λ := ∑ x ∈ K, J.q x) (fun c' _ => J.stopOutside_q_le K c') hs
  have hsum' : Summable fun b => (J.stopOutside K).Pmin s c b := hsum.summable
  have hfactor := J.exitMass_factor K c hs (sub_nonneg.mpr h)
  rw [show s + (t - s) = t by ring] at hfactor
  have hprod : Summable fun c' => (J.stopOutside K).Pmin s c c' * J.exitMass K c' (t - s) := by
    refine Summable.of_nonneg_of_le
      (fun c' => mul_nonneg ((J.stopOutside K).Pmin_nonneg s hs c c')
        (J.exitMass_nonneg K c' (by linarith)))
      (fun c' => mul_le_mul_of_nonneg_left (J.exitMass_le_one K c' (by linarith))
        ((J.stopOutside K).Pmin_nonneg s hs c c')) ?_
    simpa using hsum'
  have hsplit := Network.tsum_split K hprod
  rw [hfactor, hsplit]
  have hsecond : ∑' c', (if c' ∈ K then 0 else
      (J.stopOutside K).Pmin s c c' * J.exitMass K c' (t - s)) = J.exitMass K c s := by
    have he : J.exitMass K c s = ∑' c', (if c' ∈ K then 0 else (J.stopOutside K).Pmin s c c') := by
      rfl
    rw [he]
    refine tsum_congr fun c' => ?_
    by_cases hc : c' ∈ K
    · simp [hc]
    · rw [J.exitMass_of_not_mem K hc (by linarith), mul_one]
  rw [hsecond]
  have hnonneg : 0 ≤ ∑ c' ∈ K, (J.stopOutside K).Pmin s c c' * J.exitMass K c' (t - s) :=
    Finset.sum_nonneg fun c' _ => mul_nonneg ((J.stopOutside K).Pmin_nonneg s hs c c')
      (J.exitMass_nonneg K c' (by linarith))
  linarith

/-- **The mass outside a finite set is bounded by the exit mass.** The mass of the chain
(started at `c`) outside the finite set `K` at time `t` is at most `J.exitMass K c t`: the mass
of the chain frozen outside `K` which is outside `K` at time `t`.  This is the rigorous
version of the statement that the exit mass is the probability that the chain leaves `K`. -/
theorem mass_outside_le_exitMass (J : JumpSystem α) (K : Finset α) (c : α) {t : ℝ} (ht : 0 ≤ t) :
    ∑' b, (if b ∈ K then 0 else J.Pmin t c b) ≤ J.exitMass K c t := by
  have htot : ∑' b, J.Pmin t c b ≤ 1 :=
    Real.tsum_le_of_sum_le (fun b => J.Pmin_nonneg t ht c b) (fun F => J.sum_Pmin_le_one t ht c F)
  have hsum : Summable fun b => J.Pmin t c b :=
    summable_of_sum_le (fun b => J.Pmin_nonneg t ht c b) (fun F => J.sum_Pmin_le_one t ht c F)
  have hfrozensum : HasSum (fun b : α => (J.stopOutside K).Pmin t c b) 1 :=
    (J.stopOutside K).hasSum_Pmin_one (Λ := ∑ x ∈ K, J.q x) (fun c' _ => J.stopOutside_q_le K c') ht
  have hfrozensum' : Summable fun b => (J.stopOutside K).Pmin t c b := hfrozensum.summable
  have hle : ∑ b ∈ K, (J.stopOutside K).Pmin t c b ≤ ∑ b ∈ K, J.Pmin t c b :=
    Finset.sum_le_sum fun b hb =>
      J.Pmin_stopOutside_le K ht c hb
  have hsplit := Network.tsum_split K hsum
  have hsplit' := Network.tsum_split K hfrozensum'
  have h1 : ∑' b, (if b ∈ K then 0 else J.Pmin t c b) = (∑' b, J.Pmin t c b) -
      ∑ b ∈ K, J.Pmin t c b := by
    rw [hsplit]
    ring
  have h2 : J.exitMass K c t = 1 - ∑ b ∈ K, (J.stopOutside K).Pmin t c b := by
    have he : J.exitMass K c t = ∑' b, (if b ∈ K then 0 else (J.stopOutside K).Pmin t c b) := by
      rfl
    rw [he]
    have h3 : ∑' b, (if b ∈ K then 0 else (J.stopOutside K).Pmin t c b) =
        ∑' b, (J.stopOutside K).Pmin t c b - ∑ b ∈ K, (J.stopOutside K).Pmin t c b := by
      rw [hsplit']
      ring
    rw [h3, hfrozensum.tsum_eq]
  rw [h1, h2]
  have hnonneg : 0 ≤ ∑ b ∈ K, (J.stopOutside K).Pmin t c b := by
    exact Finset.sum_nonneg fun b _ => (J.stopOutside K).Pmin_nonneg t ht c b
  linarith

end JumpSystem

end ExitMassBounds

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The exit mass of a window.** The mass of the chain frozen outside the ball of radius `δ`
around the trajectory point `x (i * h)`, which has left the ball during the window of length `h`
starting at time `i * h`, averaged over the state of the chain at the beginning of the window. -/
noncomputable def windowExitMass (N : Network S) (κ : RateConstants N) {V : ℝ} (hV : 0 < V)
    (Rx δ h : ℝ) (x : ℝ → Concentration S) (i : ℕ) (n : S → ℕ) : ℝ :=
  ∑' c, N.transition (N.volumeScale κ V hV) (i * h) n c *
    ∑' b, (if b ∈ ballSet V Rx (x (i * h)) δ then 0 else
      ((N.jumpSystem (N.volumeScale κ V hV)).stopOutside (ballSet V Rx (x (i * h)) δ)).Pmin h c b)

/-- **Uniform-in-time concentration of the deviation.** For every network, every solution `x` of the
mass-action equation on `[0, T]` and every `δ ∈ (0, 1]`, there is a partition of `[0, T]` into `m`
intervals of length `T/m` such that

* `x` moves by less than `δ/2` on each interval;
* the total exit mass of the windows tends to `0` as the volume grows
  (`windowExitMass`, the exit-mass form of Kurtz's uniform law of large numbers, cf.
  `CRNT.Stochastic.KurtzPathwise.kurtz_lln_uniform`);
* for every volume, every interval and every time in the interval, the mass of the chain which
  has left the ball of radius `δ` around the trajectory point is bounded by the exit mass of the
  chain frozen outside that ball over the whole window — the bound is *uniform in time*.

The third bullet is the path-free proxy for "the fluctuation process tracks the trajectory
uniformly in time": the exit mass is the rigorous bound for the mass of the chain outside the
ball (`mass_outside_le_exitMass`), and it does not increase within the window
(`exitMass_mono`).

What is *not* proved here: the uniform-in-time statement at the scale of the fluctuation itself,
`sup_{t ≤ T} P(|√V (X^V(t)/V − x(t))| > ε)`, i.e. the uniform tightness in time of the
fluctuation laws, and the path-space statement (weak convergence of the fluctuation process in
`C([0, T], ℝ^S)`).  The exit-mass estimate of the library is a Chebyshev-type estimate at the
scale of the law of large numbers: it bounds the mean square deviation by `O(1/V)`, and hence
cannot bound the `O(1)`-sized fluctuation.  A fluctuation-scale estimate requires the martingale
second-moment (central limit) machinery, which Mathlib lacks — the same obstruction as in
`CRNT.Stochastic.DiffusionApproximation`. -/
theorem fluctuation_uniform_concentration (N : Network S) (κ : RateConstants N) {T Rx δ : ℝ}
    (hT : 0 < T) (hRx : 0 ≤ Rx) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (x : ℝ → Concentration S) (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (N.massActionVectorField κ (x t)) t)
    (hxB : ∀ t ∈ Icc 0 T, x t ∈ Icc (0 : Concentration S) fun _ => Rx)
    (n : ℕ → S → ℕ)
    (hn0 : Tendsto (fun k => ∑ s, ((n k s : ℝ) / ((k : ℝ) + 1) - x 0 s) ^ 2) atTop (𝓝 0)) :
    ∃ m : ℕ, 0 < m ∧
      (∀ i < m, ∀ σ ∈ Icc 0 (T / m),
        ∑ s, (x (i * (T / m) + σ) s - x (i * (T / m)) s) ^ 2 ≤ δ ^ 2 / 4) ∧
      (Tendsto (fun k : ℕ => ∑ i ∈ Finset.range m,
          N.windowExitMass κ (V := (k : ℝ) + 1) (by positivity) Rx δ (T / m) x i (n k))
        atTop (𝓝 0)) ∧
      (∀ k : ℕ, ∀ i < m, ∀ c : S → ℕ, ∀ τ ∈ Icc 0 (T / m),
        (∑' b, (if b ∈ ballSet ((k : ℝ) + 1) Rx (x (i * (T / m))) δ then 0 else
            (N.jumpSystem (N.volumeScale κ ((k : ℝ) + 1) (by positivity))).Pmin τ c b))
          ≤ (∑' b, (if b ∈ ballSet ((k : ℝ) + 1) Rx (x (i * (T / m))) δ then 0 else
            ((N.jumpSystem (N.volumeScale κ ((k : ℝ) + 1) (by positivity))).stopOutside
              (ballSet ((k : ℝ) + 1) Rx (x (i * (T / m))) δ)).Pmin (T / m) c b))) := by
  obtain ⟨m, hm, hmesh, hexit⟩ := N.kurtz_lln_uniform κ hT hRx hδ hδ1 x hxc hx hxB n hn0
  refine ⟨m, hm, hmesh, ?_, ?_⟩
  · simpa only [windowExitMass] using hexit
  · intro k i hi c τ hτ
    have hV0 : 0 < (k : ℝ) + 1 := by positivity
    have hτ0 : 0 ≤ τ := hτ.1
    have hτh : τ ≤ T / m := hτ.2
    have hmono : JumpSystem.exitMass (N.jumpSystem (N.volumeScale κ ((k : ℝ) + 1) hV0))
        (ballSet ((k : ℝ) + 1) Rx (x (i * (T / m))) δ) c τ
        ≤ JumpSystem.exitMass (N.jumpSystem (N.volumeScale κ ((k : ℝ) + 1) hV0))
          (ballSet ((k : ℝ) + 1) Rx (x (i * (T / m))) δ) c (T / m) :=
      JumpSystem.exitMass_mono _ _ _ hτh hτ0
    have hbound : (∑' b, (if b ∈ ballSet ((k : ℝ) + 1) Rx (x (i * (T / m))) δ then 0 else
          (N.jumpSystem (N.volumeScale κ ((k : ℝ) + 1) hV0)).Pmin τ c b))
        ≤ JumpSystem.exitMass (N.jumpSystem (N.volumeScale κ ((k : ℝ) + 1) hV0))
          (ballSet ((k : ℝ) + 1) Rx (x (i * (T / m))) δ) c τ :=
      JumpSystem.mass_outside_le_exitMass _ _ _ (by positivity)
    have hdef : JumpSystem.exitMass (N.jumpSystem (N.volumeScale κ ((k : ℝ) + 1) hV0))
          (ballSet ((k : ℝ) + 1) Rx (x (i * (T / m))) δ) c τ
        = (∑' b, (if b ∈ ballSet ((k : ℝ) + 1) Rx (x (i * (T / m))) δ then 0 else
          ((N.jumpSystem (N.volumeScale κ ((k : ℝ) + 1) hV0)).stopOutside
            (ballSet ((k : ℝ) + 1) Rx (x (i * (T / m))) δ)).Pmin τ c b)) := rfl
    have hdef' : JumpSystem.exitMass (N.jumpSystem (N.volumeScale κ ((k : ℝ) + 1) hV0))
          (ballSet ((k : ℝ) + 1) Rx (x (i * (T / m))) δ) c (T / m)
        = (∑' b, (if b ∈ ballSet ((k : ℝ) + 1) Rx (x (i * (T / m))) δ then 0 else
          ((N.jumpSystem (N.volumeScale κ ((k : ℝ) + 1) hV0)).stopOutside
            (ballSet ((k : ℝ) + 1) Rx (x (i * (T / m))) δ)).Pmin (T / m) c b)) := rfl
    rw [hdef, hdef'] at hmono
    exact hbound.trans hmono

end Network

end CRNT
