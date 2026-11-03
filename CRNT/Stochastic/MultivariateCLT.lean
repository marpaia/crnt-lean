import CRNT.Stochastic.NonlinearCLT
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# The multivariate CLT in distribution at an equilibrium

For a conservative network with an equilibrium `x* ≥ 0`, the law of the fluctuation
`ζ^V(T) = √V (X^V(T)/V − x*)` on `EuclideanSpace ℝ S` converges weakly to the multivariate
Gaussian with mean `e^{T J} z₀` and covariance `Σ(T) = ∫₀ᵀ e^{uJ} G e^{uJᵀ} du`, where
`J = Df(x*)` and `G = ∑_r λ_r(x*) Δ_r Δ_rᵀ` (`multivariate_clt`).

The adjoint solutions are `θ(u) = e^{(T − u) Jᵀ} θ` (`fundSol`, exponential in the Banach algebra of
continuous linear maps), for which `nonlinear_clt` gives the convergence of the characteristic
function at every `θ`; the limit is identified with the characteristic function of
`multivariateGaussian` (`charFun_multivariateGaussian`), and Lévy's continuity theorem
(`ProbabilityMeasure.tendsto_of_tendsto_charFun`) gives weak convergence.
-/

open MeasureTheory ProbabilityTheory Set Filter Complex Matrix
open scoped BigOperators Topology NNReal

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The transpose of a continuous linear map of `S → ℝ`. -/
noncomputable def transposeCLM (J : (S → ℝ) →L[ℝ] (S → ℝ)) : (S → ℝ) →L[ℝ] (S → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun θ s' => ∑ s, θ s * J (Pi.single s' 1) s
      map_add' := fun a b => by
        funext s'; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c a => by
        funext s'; simp [Finset.mul_sum, mul_assoc] }

theorem transposeCLM_apply (J : (S → ℝ) →L[ℝ] (S → ℝ)) (θ : S → ℝ) (s' : S) :
    transposeCLM J θ s' = ∑ s, θ s * J (Pi.single s' 1) s := rfl

/-- `θ · J v = Jᵀ θ · v`. -/
theorem transpose_dot (J : (S → ℝ) →L[ℝ] (S → ℝ)) (θ v : S → ℝ) :
    ∑ s, transposeCLM J θ s * v s = ∑ s, θ s * J v s := by
  have hv : v = ∑ s', v s' • (Pi.single s' (1 : ℝ) : S → ℝ) := by
    funext s; simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hv]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, transposeCLM_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => by ring

/-- The fundamental solution `u ↦ e^{(T − u) A}` of the adjoint equation. -/
noncomputable def fundSol (A : (S → ℝ) →L[ℝ] (S → ℝ)) (T u : ℝ) : (S → ℝ) →L[ℝ] (S → ℝ) :=
  NormedSpace.exp ((T - u) • A)

theorem hasDerivAt_fundSol (A : (S → ℝ) →L[ℝ] (S → ℝ)) (T u : ℝ) :
    HasDerivAt (fundSol A T) (-(A * fundSol A T u)) u := by
  have h1 := hasDerivAt_exp_smul_const' (𝕂 := ℝ) A (T - u)
  have h2 : HasDerivAt (fun u : ℝ => T - u) (-1) u := by
    simpa using (hasDerivAt_id u).const_sub T
  have := h1.scomp u h2
  rw [neg_one_smul] at this
  exact this

theorem fundSol_self (A : (S → ℝ) →L[ℝ] (S → ℝ)) (T : ℝ) : fundSol A T T = 1 := by
  simp [fundSol]

theorem continuous_fundSol (A : (S → ℝ) →L[ℝ] (S → ℝ)) (T : ℝ) : Continuous (fundSol A T) :=
  continuous_iff_continuousAt.mpr fun u => (hasDerivAt_fundSol A T u).continuousAt

/-- The adjoint solution with terminal value `θ`. -/
noncomputable def adjSol (A : (S → ℝ) →L[ℝ] (S → ℝ)) (T : ℝ) (θ : S → ℝ) (u : ℝ) : S → ℝ :=
  fundSol A T u θ

theorem hasDerivAt_adjSol (A : (S → ℝ) →L[ℝ] (S → ℝ)) (T : ℝ) (θ : S → ℝ) (u : ℝ) :
    HasDerivAt (adjSol A T θ) (-(A (adjSol A T θ u))) u := by
  have h := (ContinuousLinearMap.apply ℝ (S → ℝ) θ).hasFDerivAt.comp_hasDerivAt u
    (hasDerivAt_fundSol A T u)
  have e : -(A (adjSol A T θ u)) = (ContinuousLinearMap.apply ℝ (S → ℝ) θ) (-(A * fundSol A T u)) := by
    simp [adjSol]
  rw [e]
  exact h

theorem adjSol_self (A : (S → ℝ) →L[ℝ] (S → ℝ)) (T : ℝ) (θ : S → ℝ) : adjSol A T θ T = θ := by
  simp [adjSol, fundSol_self]

/-- Linearity in the terminal value. -/
theorem adjSol_eq_sum (A : (S → ℝ) →L[ℝ] (S → ℝ)) (T : ℝ) (θ : S → ℝ) (u : ℝ) :
    adjSol A T θ u = ∑ j, θ j • fundSol A T u (Pi.single j 1) := by
  have hθ : θ = ∑ j, θ j • (Pi.single j (1 : ℝ) : S → ℝ) := by
    funext s; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [adjSol, hθ]
  simp only [map_sum, map_smul]

/-- The adjoint relation `θ'(u) · v = −θ(u) · J v` for `A = Jᵀ`. -/
theorem adjSol_adjoint (J : (S → ℝ) →L[ℝ] (S → ℝ)) (T : ℝ) (θ : S → ℝ) (u : ℝ) (v : S → ℝ) :
    ∑ s, (-(transposeCLM J (adjSol (transposeCLM J) T θ u))) s * v s =
      -∑ s, adjSol (transposeCLM J) T θ u s * J v s := by
  rw [← transpose_dot]
  simp [Finset.sum_neg_distrib, neg_mul]

/-- The mean `e^{T J} z₀`, in coordinates. -/
noncomputable def meanVec (A : (S → ℝ) →L[ℝ] (S → ℝ)) (T : ℝ) (z₀ : S → ℝ) : S → ℝ :=
  fun j => ∑ i, fundSol A T 0 (Pi.single j 1) i * z₀ i

theorem dot_adjSol_zero (A : (S → ℝ) →L[ℝ] (S → ℝ)) (T : ℝ) (θ z₀ : S → ℝ) :
    ∑ i, adjSol A T θ 0 i * z₀ i = ∑ j, θ j * meanVec A T z₀ j := by
  rw [adjSol_eq_sum]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, meanVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

/-- The pairing of two adjoint solutions through the diffusion matrix at time `u`. -/
noncomputable def covDensity (N : Network S) (κ : RateConstants N) (xs : Concentration S)
    (A : (S → ℝ) →L[ℝ] (S → ℝ)) (T u : ℝ) (j k : S) : ℝ :=
  ∑ r, N.massActionRate κ r xs *
    (∑ s, fundSol A T u (Pi.single j 1) s * N.reactionVector r s) *
    (∑ s, fundSol A T u (Pi.single k 1) s * N.reactionVector r s)

/-- The covariance `Σ(T) = ∫₀ᵀ e^{(T−u)J} G e^{(T−u)Jᵀ} du`. -/
noncomputable def covMat (N : Network S) (κ : RateConstants N) (xs : Concentration S)
    (A : (S → ℝ) →L[ℝ] (S → ℝ)) (T : ℝ) : Matrix S S ℝ :=
  fun j k => ∫ u in (0 : ℝ)..T, N.covDensity κ xs A T u j k

theorem quadG_adjSol (N : Network S) (κ : RateConstants N) (xs : Concentration S)
    (A : (S → ℝ) →L[ℝ] (S → ℝ)) (T : ℝ) (θ : S → ℝ) (u : ℝ) :
    N.quadG κ xs (adjSol A T θ u) = ∑ j, ∑ k, θ j * θ k * N.covDensity κ xs A T u j k := by
  unfold quadG covDensity
  rw [adjSol_eq_sum]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have : ∀ r, (∑ s, (∑ j, θ j * fundSol A T u (Pi.single j 1) s) * N.reactionVector r s) =
      ∑ j, θ j * ∑ s, fundSol A T u (Pi.single j 1) s * N.reactionVector r s := by
    intro r
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s _ => by ring
  simp_rw [this]
  have hsq : ∀ r, N.massActionRate κ r xs *
      (∑ j, θ j * ∑ s, fundSol A T u (Pi.single j 1) s * N.reactionVector r s) ^ 2 =
      ∑ j, ∑ k, θ j * θ k * (N.massActionRate κ r xs *
        (∑ s, fundSol A T u (Pi.single j 1) s * N.reactionVector r s) *
        (∑ s, fundSol A T u (Pi.single k 1) s * N.reactionVector r s)) := by
    intro r
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp_rw [hsq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]

theorem continuous_covDensity (N : Network S) (κ : RateConstants N) (xs : Concentration S)
    (A : (S → ℝ) →L[ℝ] (S → ℝ)) (T : ℝ) (j k : S) :
    Continuous fun u => N.covDensity κ xs A T u j k := by
  unfold covDensity
  have hc : ∀ j : S, Continuous fun u => fundSol A T u (Pi.single j 1) := fun j =>
    (ContinuousLinearMap.apply ℝ (S → ℝ) (Pi.single j 1)).continuous.comp (continuous_fundSol A T)
  refine continuous_finsetSum _ fun r _ => ?_
  refine (continuous_const.mul ?_).mul ?_ <;>
  · refine continuous_finsetSum _ fun s _ => ?_
    exact ((continuous_apply s).comp (hc _)).mul continuous_const

theorem integral_quadG_adjSol (N : Network S) (κ : RateConstants N) (xs : Concentration S)
    (A : (S → ℝ) →L[ℝ] (S → ℝ)) (T : ℝ) (θ : S → ℝ) :
    ∫ u in (0 : ℝ)..T, N.quadG κ xs (adjSol A T θ u) = θ ⬝ᵥ (N.covMat κ xs A T *ᵥ θ) := by
  simp_rw [quadG_adjSol]
  have hint : ∀ j k, IntervalIntegrable (fun u => θ j * θ k * N.covDensity κ xs A T u j k)
      MeasureTheory.volume 0 T := fun j k =>
    (continuous_const.mul (N.continuous_covDensity κ xs A T j k)).intervalIntegrable _ _
  have hint2 : ∀ j, IntervalIntegrable (fun u => ∑ k, θ j * θ k * N.covDensity κ xs A T u j k)
      MeasureTheory.volume 0 T := fun j => by
    have hc : Continuous fun u => ∑ k, θ j * θ k * N.covDensity κ xs A T u j k :=
      continuous_finsetSum _ fun k _ => continuous_const.mul (N.continuous_covDensity κ xs A T j k)
    exact hc.intervalIntegrable _ _
  rw [intervalIntegral.integral_finset_sum fun j _ => hint2 j]
  simp only [dotProduct, Matrix.mulVec, covMat]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_finset_sum fun k _ => hint j k, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_const_mul]
  ring

theorem covMat_posSemidef (N : Network S) (κ : RateConstants N) {xs : Concentration S}
    (hxs : ∀ s, 0 ≤ xs s) (A : (S → ℝ) →L[ℝ] (S → ℝ)) {T : ℝ} (hT : 0 ≤ T) :
    (N.covMat κ xs A T).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext j k
    simp only [Matrix.conjTranspose_apply, star_trivial, covMat, covDensity]
    congr 1; funext u
    exact Finset.sum_congr rfl fun r _ => by ring
  · simp only [star_trivial]
    rw [← integral_quadG_adjSol]
    exact intervalIntegral.integral_nonneg hT fun u _ => N.quadG_nonneg κ hxs _

/-- The law of the fluctuation `ζ^V(T)` started from `n`: a finite mixture of point masses on
`EuclideanSpace ℝ S` over the (finite) class of `n`. -/
noncomputable def flucLaw (N : Network S) (κ : RateConstants N) (hcons : N.IsConservative)
    {V : ℝ} (hV : 0 < V) (xs : Concentration S) (T : ℝ) (n : S → ℕ) :
    Measure (EuclideanSpace ℝ S) :=
  ∑ m ∈ N.reachClass (N.volumeScale κ V hV) hcons n,
    ENNReal.ofReal (N.transition (N.volumeScale κ V hV) T n m) •
      Measure.dirac (WithLp.toLp 2 (zeta V xs m))

theorem sum_transition_reachClass (N : Network S) (κ : RateConstants N) (hcons : N.IsConservative)
    {V : ℝ} (hV : 0 < V) {T : ℝ} (hT : 0 ≤ T) (n : S → ℕ) :
    ∑ m ∈ N.reachClass (N.volumeScale κ V hV) hcons n, N.transition (N.volumeScale κ V hV) T n m = 1 := by
  have h := N.hasSum_transition_one_of_conservative (N.volumeScale κ V hV) hcons n hT
  rw [← h.tsum_eq]
  exact (tsum_eq_sum (s := N.reachClass (N.volumeScale κ V hV) hcons n) fun m hm =>
    N.transition_eq_zero_of_not_reachPos _ T fun hr =>
      hm ((N.mem_reachClass _ hcons).mpr hr)).symm

theorem isProbabilityMeasure_flucLaw (N : Network S) (κ : RateConstants N)
    (hcons : N.IsConservative) {V : ℝ} (hV : 0 < V) (xs : Concentration S) {T : ℝ} (hT : 0 ≤ T)
    (n : S → ℕ) : IsProbabilityMeasure (N.flucLaw κ hcons hV xs T n) := by
  constructor
  simp only [flucLaw, Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun m _ =>
    (show (0 : ℝ) ≤ N.transition (N.volumeScale κ V hV) T n m from
      JumpSystem.Pmin_nonneg _ T hT n m),
    N.sum_transition_reachClass κ hcons hV hT n, ENNReal.ofReal_one]

theorem inner_toLp_zeta (V : ℝ) (xs : Concentration S) (m : S → ℕ) (t : EuclideanSpace ℝ S) :
    inner ℝ (WithLp.toLp 2 (zeta V xs m)) t = ∑ s, WithLp.ofLp t s * zeta V xs m s := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct]

theorem charFun_flucLaw (N : Network S) (κ : RateConstants N) (hcons : N.IsConservative)
    {V : ℝ} (hV : 0 < V) (xs : Concentration S) {T : ℝ} (hT : 0 ≤ T) (n : S → ℕ)
    (t : EuclideanSpace ℝ S) :
    charFun (N.flucLaw κ hcons hV xs T n) t =
      ∑' m, (N.transition (N.volumeScale κ V hV) T n m : ℂ) *
        Complex.exp (I * ((∑ s, WithLp.ofLp t s * zeta V xs m s : ℝ) : ℂ)) := by
  rw [charFun_apply, flucLaw, integral_finset_sum_measure (fun m _ =>
    (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top)]
  rw [tsum_eq_sum (s := N.reachClass (N.volumeScale κ V hV) hcons n) fun m hm => by
    rw [N.transition_eq_zero_of_not_reachPos _ T fun hr =>
      hm ((N.mem_reachClass _ hcons).mpr hr)]; simp]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_smul_measure, integral_dirac, inner_toLp_zeta,
    ENNReal.toReal_ofReal (show (0 : ℝ) ≤ N.transition (N.volumeScale κ V hV) T n m from
      JumpSystem.Pmin_nonneg _ T hT n m)]
  rw [Complex.real_smul]
  congr 1
  push_cast
  ring_nf

/-- The law of the fluctuation as a probability measure. -/
noncomputable def flucLawP (N : Network S) (κ : RateConstants N) (hcons : N.IsConservative)
    {V : ℝ} (hV : 0 < V) (xs : Concentration S) {T : ℝ} (hT : 0 ≤ T) (n : S → ℕ) :
    ProbabilityMeasure (EuclideanSpace ℝ S) :=
  ⟨N.flucLaw κ hcons hV xs T n, N.isProbabilityMeasure_flucLaw κ hcons hV xs hT n⟩

/-- The Gaussian limit. -/
noncomputable def gaussLimit (N : Network S) (κ : RateConstants N) (xs : Concentration S)
    (T : ℝ) (z₀ : S → ℝ) : ProbabilityMeasure (EuclideanSpace ℝ S) :=
  ⟨multivariateGaussian
    (WithLp.toLp 2 (meanVec (transposeCLM (fderiv ℝ (N.massActionVectorField κ) xs)) T z₀))
    (N.covMat κ xs (transposeCLM (fderiv ℝ (N.massActionVectorField κ) xs)) T), inferInstance⟩

/-- **Multivariate CLT in distribution for nonlinear conservative networks at an equilibrium.**
For a conservative network with an equilibrium `x* ≥ 0` and initial counts with
`⟨w, n_V⟩ ≤ M V` and `√V (n_V/V − x*) → z₀`, the law of `√V (X^V(T)/V − x*)` on
`EuclideanSpace ℝ S` (`flucLawP`) converges weakly to the Gaussian with mean `e^{T J} z₀`
(`meanVec`) and covariance `∫₀ᵀ e^{(T−u)J} G e^{(T−u)Jᵀ} du` (`covMat`), where `J = Df(x*)`
and `G = ∑_r λ_r(x*) Δ_r Δ_rᵀ` (`gaussLimit`). -/
theorem multivariate_clt (N : Network S) (κ : RateConstants N) {w : S → ℝ}
    (hwinv : N.IsPInvariant w) (hwpos : ∀ s, 0 < w s) {xs : Concentration S}
    (heq : N.massActionVectorField κ xs = 0) (hxs0 : ∀ s, 0 ≤ xs s) {M T : ℝ} (hM : 0 ≤ M)
    (hT : 0 < T) (n : ℕ → S → ℕ) (hn : ∀ k : ℕ, ∑ s, w s * (n k s : ℝ) ≤ M * ((k : ℝ) + 1))
    {z₀ : S → ℝ} (hz : Tendsto (fun k : ℕ => zeta ((k : ℝ) + 1) xs (n k)) atTop (𝓝 z₀)) :
    Tendsto (fun k : ℕ => N.flucLawP κ ⟨w, hwinv, hwpos⟩ (V := (k : ℝ) + 1) (by positivity) xs
      hT.le (n k)) atTop (𝓝 (N.gaussLimit κ xs T z₀)) := by
  set J := fderiv ℝ (N.massActionVectorField κ) xs with hJ
  set A := transposeCLM J with hA
  have hcons : N.IsConservative := ⟨w, hwinv, hwpos⟩
  refine ProbabilityMeasure.tendsto_of_tendsto_charFun fun t => ?_
  set θ : S → ℝ := WithLp.ofLp t with hθ
  have h := N.nonlinear_clt κ hwinv hwpos heq hxs0 hM hT (adjSol A T θ)
    (fun u => -(A (adjSol A T θ u))) (hasDerivAt_adjSol A T θ)
    (fun u _ v => adjSol_adjoint J T θ u v) n hn hz
  simp only [adjSol_self] at h
  rw [dot_adjSol_zero, integral_quadG_adjSol] at h
  have hlhs : ∀ k : ℕ, charFun ((N.flucLawP κ ⟨w, hwinv, hwpos⟩ (V := (k : ℝ) + 1)
      (by positivity) xs hT.le (n k) : ProbabilityMeasure (EuclideanSpace ℝ S)) :
        Measure (EuclideanSpace ℝ S)) t =
      ∑' m, (N.transition (N.volumeScale κ ((k : ℝ) + 1) (by positivity)) T (n k) m : ℂ) *
        Complex.exp (I * ((∑ s, θ s * zeta ((k : ℝ) + 1) xs m s : ℝ) : ℂ)) := fun k =>
    N.charFun_flucLaw κ hcons _ xs hT.le (n k) t
  have hpsd := N.covMat_posSemidef κ hxs0 A hT.le
  have hrhs : charFun ((N.gaussLimit κ xs T z₀ : ProbabilityMeasure (EuclideanSpace ℝ S)) :
      Measure (EuclideanSpace ℝ S)) t =
      Complex.exp (I * ((∑ j, θ j * meanVec A T z₀ j : ℝ) : ℂ) -
        ((θ ⬝ᵥ (N.covMat κ xs A T *ᵥ θ) / 2 : ℝ) : ℂ)) := by
    show charFun (multivariateGaussian (WithLp.toLp 2 (meanVec A T z₀)) (N.covMat κ xs A T)) t = _
    rw [charFun_multivariateGaussian hpsd]
    congr 1
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [WithLp.ofLp_toLp, star_trivial, dotProduct]
    push_cast
    have e : (∑ x, ((meanVec A T z₀ x : ℝ) : ℂ) * ((WithLp.ofLp t x : ℝ) : ℂ)) =
        ∑ x, ((WithLp.ofLp t x : ℝ) : ℂ) * ((meanVec A T z₀ x : ℝ) : ℂ) :=
      Finset.sum_congr rfl fun x _ => mul_comm _ _
    rw [e]
    ring
  rw [hrhs]
  exact h.congr fun k => (hlhs k).symm

end Network
end CRNT

namespace CRNT
namespace Examples
namespace DimerMultivariateCLT

open Network Dimerization

/-- **Multivariate CLT instance for `2X ⇌ Y` at `(1, 1)`.** Started from `(V, V)` molecules, the
law of `√V (X^V(T)/V − (1, 1))` converges weakly to the centred Gaussian with covariance
`∫₀ᵀ e^{(T−u)J} G e^{(T−u)Jᵀ} du`. -/
theorem clt {T : ℝ} (hT : 0 < T) :
    Tendsto (fun k : ℕ => net.flucLawP κ ⟨w, w_inv, w_pos⟩ (V := (k : ℝ) + 1) (by positivity)
      xstar hT.le (fun _ => k + 1)) atTop (𝓝 (net.gaussLimit κ xstar T 0)) := by
  have hz : Tendsto (fun k : ℕ => zeta ((k : ℝ) + 1) xstar (fun _ => k + 1)) atTop (𝓝 0) := by
    have : ∀ k : ℕ, zeta ((k : ℝ) + 1) xstar (fun _ => k + 1) = 0 := by
      intro k; funext s
      have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
      simp [zeta, xstar, hk]
    simp only [this]; exact tendsto_const_nhds
  exact net.multivariate_clt κ w_inv w_pos equilibrium (fun _ => zero_le_one) (M := 3)
    (by norm_num) hT (fun k _ => k + 1) (fun k => by simp [w, Fin.sum_univ_two]; linarith) hz

end DimerMultivariateCLT
end Examples
end CRNT
