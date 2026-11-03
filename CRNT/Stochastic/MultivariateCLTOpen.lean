import CRNT.Stochastic.MultivariateCLT
import CRNT.Stochastic.NonlinearCLTOpen

/-!
# The multivariate CLT in distribution for non-conservative networks

At an equilibrium `x* ≥ 0` of an arbitrary network whose volume-scaled chains are stochastic from
the initial counts (e.g. weights grown at most monomolecularly, `hasSum_transition_one_of_weight`),
the law of `√V (X^V(T)/V − x*)` — a countable mixture of point masses on `EuclideanSpace ℝ S` —
converges weakly to `multivariateGaussian(e^{TJ} z₀, Σ(T))` (`multivariate_clt_open`).  The
characteristic-function convergence comes from `nonlinear_clt_open`; the rest is as in
`multivariate_clt`.
-/

open MeasureTheory ProbabilityTheory Set Filter Complex Matrix
open scoped BigOperators Topology NNReal

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The law of the fluctuation `ζ^V(T)` from `n`, a countable mixture of point masses. -/
noncomputable def flucLawOpen (N : Network S) (κ : RateConstants N) {V : ℝ} (hV : 0 < V)
    (xs : Concentration S) (T : ℝ) (n : S → ℕ) : Measure (EuclideanSpace ℝ S) :=
  Measure.sum fun m => ENNReal.ofReal (N.transition (N.volumeScale κ V hV) T n m) •
    Measure.dirac (WithLp.toLp 2 (zeta V xs m))

theorem isProbabilityMeasure_flucLawOpen (N : Network S) (κ : RateConstants N) {V : ℝ}
    (hV : 0 < V) (xs : Concentration S) {T : ℝ} (hT : 0 ≤ T) (n : S → ℕ)
    (hstoch : HasSum (fun m => N.transition (N.volumeScale κ V hV) T n m) 1) :
    IsProbabilityMeasure (N.flucLawOpen κ hV xs T n) := by
  constructor
  simp only [flucLawOpen, Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (f := fun m => N.transition (N.volumeScale κ V hV) T n m)
    (fun m => JumpSystem.Pmin_nonneg _ T hT n m) hstoch.summable, hstoch.tsum_eq,
    ENNReal.ofReal_one]

theorem charFun_flucLawOpen (N : Network S) (κ : RateConstants N) {V : ℝ} (hV : 0 < V)
    (xs : Concentration S) {T : ℝ} (hT : 0 ≤ T) (n : S → ℕ)
    (hstoch : HasSum (fun m => N.transition (N.volumeScale κ V hV) T n m) 1)
    (t : EuclideanSpace ℝ S) :
    charFun (N.flucLawOpen κ hV xs T n) t =
      ∑' m, (N.transition (N.volumeScale κ V hV) T n m : ℂ) *
        Complex.exp (I * ((∑ s, WithLp.ofLp t s * zeta V xs m s : ℝ) : ℂ)) := by
  rw [charFun_apply, flucLawOpen, integral_sum_dirac_eq_tsum (fun m => ENNReal.ofReal_ne_top)]
  · refine tsum_congr fun m => ?_
    rw [inner_toLp_zeta, ENNReal.toReal_ofReal (show (0 : ℝ) ≤
      N.transition (N.volumeScale κ V hV) T n m from JumpSystem.Pmin_nonneg _ T hT n m),
      Complex.real_smul]
    congr 1
    push_cast
    ring_nf
  · refine hstoch.summable.congr fun m => ?_
    rw [ENNReal.toReal_ofReal (show (0 : ℝ) ≤
      N.transition (N.volumeScale κ V hV) T n m from JumpSystem.Pmin_nonneg _ T hT n m)]
    rw [Complex.norm_exp]
    simp

/-- The law as a probability measure. -/
noncomputable def flucLawOpenP (N : Network S) (κ : RateConstants N) {V : ℝ} (hV : 0 < V)
    (xs : Concentration S) {T : ℝ} (hT : 0 ≤ T) (n : S → ℕ)
    (hstoch : HasSum (fun m => N.transition (N.volumeScale κ V hV) T n m) 1) :
    ProbabilityMeasure (EuclideanSpace ℝ S) :=
  ⟨N.flucLawOpen κ hV xs T n, N.isProbabilityMeasure_flucLawOpen κ hV xs hT n hstoch⟩

/-- **Multivariate CLT in distribution for an arbitrary network at an equilibrium.** If the
chains are stochastic from the initial counts and `√V (n_V/V − x*) → z₀`, the law of
`√V (X^V(T)/V − x*)` converges weakly to `multivariateGaussian(e^{TJ} z₀, Σ(T))`. -/
theorem multivariate_clt_open (N : Network S) (κ : RateConstants N) {xs : Concentration S}
    (heq : N.massActionVectorField κ xs = 0) (hxs0 : ∀ s, 0 ≤ xs s) {T : ℝ} (hT : 0 < T)
    (n : ℕ → S → ℕ)
    (hstoch : ∀ k : ℕ, HasSum (fun m => N.transition (N.volumeScale κ ((k : ℝ) + 1)
      (by positivity)) T (n k) m) 1)
    {z₀ : S → ℝ} (hz : Tendsto (fun k : ℕ => zeta ((k : ℝ) + 1) xs (n k)) atTop (𝓝 z₀)) :
    Tendsto (fun k : ℕ => N.flucLawOpenP κ (V := (k : ℝ) + 1) (by positivity) xs hT.le (n k)
      (hstoch k)) atTop (𝓝 (N.gaussLimit κ xs T z₀)) := by
  set J := fderiv ℝ (N.massActionVectorField κ) xs with hJ
  set A := transposeCLM J with hA
  set Rx := ∑ s, xs s with hRx
  have hRx0 : 0 ≤ Rx := Finset.sum_nonneg fun s _ => hxs0 s
  have hxsB : xs ∈ Icc (0 : Concentration S) fun _ => Rx := ⟨fun s => hxs0 s, fun s =>
    Finset.single_le_sum (f := fun s => xs s) (fun s _ => hxs0 s) (Finset.mem_univ s)⟩
  refine ProbabilityMeasure.tendsto_of_tendsto_charFun fun t => ?_
  set θ : S → ℝ := WithLp.ofLp t with hθ
  have h := N.nonlinear_clt_open κ (Rx := Rx) hT hRx0 (fun _ => xs) continuousOn_const
    (fun t _ => by rw [heq]; exact hasDerivAt_const _ _) (fun t _ => hxsB) (adjSol A T θ)
    (fun u => -(A (adjSol A T θ u)))
    (fun u _ => (hasDerivAt_adjSol A T θ u).continuousAt.continuousWithinAt)
    (fun u _ => hasDerivAt_adjSol A T θ u)
    (fun u _ v => adjSol_adjoint J T θ u v) n hz
  simp only [adjSol_self] at h
  rw [dot_adjSol_zero, integral_quadG_adjSol] at h
  have hlhs : ∀ k : ℕ, charFun ((N.flucLawOpenP κ (V := (k : ℝ) + 1) (by positivity) xs hT.le
      (n k) (hstoch k) : ProbabilityMeasure (EuclideanSpace ℝ S)) :
        Measure (EuclideanSpace ℝ S)) t =
      ∑' m, (N.transition (N.volumeScale κ ((k : ℝ) + 1) (by positivity)) T (n k) m : ℂ) *
        Complex.exp (I * ((∑ s, θ s * zeta ((k : ℝ) + 1) xs m s : ℝ) : ℂ)) := fun k =>
    N.charFun_flucLawOpen κ _ xs hT.le (n k) (hstoch k) t
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

namespace Examples
namespace InflowAnnihilationMultivariateCLT

open Network InflowAnnihilation

/-- **Distributional CLT for the non-conservative `0 → X`, `2X → 0` at `x* = 1`.** -/
theorem clt {T : ℝ} (hT : 0 < T) :
    Tendsto (fun k : ℕ => net.flucLawOpenP κ (V := (k : ℝ) + 1) (by positivity) xstar hT.le
      (fun _ => k + 1) (net.hasSum_transition_one_of_weight _ w (fun _ => one_pos)
        (fun r hr => inflowWeight.monoWeight r hr) hT.le _)) atTop
      (𝓝 (net.gaussLimit κ xstar T 0)) := by
  have hz : Tendsto (fun k : ℕ => zeta ((k : ℝ) + 1) xstar (fun _ => k + 1)) atTop (𝓝 0) := by
    have : ∀ k : ℕ, zeta ((k : ℝ) + 1) xstar (fun _ => k + 1) = 0 := by
      intro k; funext s
      have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
      simp [zeta, xstar, hk]
    simp only [this]; exact tendsto_const_nhds
  exact net.multivariate_clt_open κ equilibrium (fun _ => zero_le_one) hT (fun k _ => k + 1) _ hz

end InflowAnnihilationMultivariateCLT
end Examples

end CRNT
