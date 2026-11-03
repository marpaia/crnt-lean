import CRNT.Stochastic.MultivariateCLT
import CRNT.Stochastic.NonlinearCLTTraj
import CRNT.Analysis.LinearODE
import CRNT.Examples.IsomerCLT
import CRNT.Stochastic.MultivariateCLTOpen

/-!
# The multivariate CLT in distribution along a trajectory

For a conservative network and a solution `x` of the mass-action equation on `[0, T]`, the law of
`√V (X^V(T)/V − x(T))` converges weakly to the Gaussian with mean `Φ(0)ᵀ z₀` and covariance
`∫₀ᵀ Φ(u)ᵀ G(x(u)) Φ(u) du`, where `Φ(u)` is the fundamental solution of the adjoint linearized
equation `θ' = −Df(x(u))ᵀ θ` with `Φ(T) = I` (`multivariate_clt_traj`).

The fundamental solution is built column by column from global solutions of linear ODEs
(`exists_linear_ode_Icc`), run backwards in time (`exists_adjoint_basis`); combining columns linearly
(`trajAdj`) gives an adjoint solution for every terminal value, linear in it, so that the limit of
the characteristic functions (`nonlinear_clt_traj`) is the characteristic function of a Gaussian
(`charFun_multivariateGaussian`), and Lévy's continuity theorem concludes.
-/

open MeasureTheory ProbabilityTheory Set Filter Complex Matrix
open scoped BigOperators Topology NNReal

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Backward solutions of the adjoint equation `θ' = −A(u) θ`, `θ(T) = θ₀`. -/
theorem exists_adjoint_basis (A : ℝ → (S → ℝ) →L[ℝ] (S → ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (hA : ContinuousOn A (Icc 0 T)) (θ₀ : S → ℝ) :
    ∃ θ : ℝ → S → ℝ, θ T = θ₀ ∧ ContinuousOn θ (Icc 0 T) ∧
      ∀ u ∈ Ioo 0 T, HasDerivAt θ (-(A u (θ u))) u := by
  have hmaps : MapsTo (fun s : ℝ => T - s) (Icc 0 T) (Icc 0 T) := fun s hs =>
    ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hB : ContinuousOn (fun s => A (T - s)) (Icc 0 T) :=
    hA.comp (continuous_const.sub continuous_id).continuousOn hmaps
  obtain ⟨φ, hφ0, hφ⟩ := exists_linear_ode_Icc (fun s => A (T - s)) hT hB θ₀
  refine ⟨fun u => φ (T - u), by simp [hφ0], ?_, fun u hu => ?_⟩
  · have hφc : ContinuousOn φ (Icc 0 T) := fun s hs => (hφ s hs).continuousWithinAt
    exact hφc.comp (continuous_const.sub continuous_id).continuousOn hmaps
  · have hs : T - u ∈ Ioo 0 T := ⟨by linarith [hu.2], by linarith [hu.1]⟩
    have h1 : HasDerivAt φ (A (T - (T - u)) (φ (T - u))) (T - u) :=
      (hφ (T - u) (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
    have h2 : HasDerivAt (fun u : ℝ => T - u) (-1) u := by
      simpa using (hasDerivAt_id u).const_sub T
    have h3 := h1.scomp u h2
    rw [neg_one_smul, sub_sub_cancel] at h3
    exact h3

/-- The adjoint solution with terminal value `Pi.single j 1`. -/
noncomputable def adjBasis (A : ℝ → (S → ℝ) →L[ℝ] (S → ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (hA : ContinuousOn A (Icc 0 T)) (j : S) : ℝ → S → ℝ :=
  Classical.choose (exists_adjoint_basis A hT hA (Pi.single j 1))

theorem adjBasis_spec (A : ℝ → (S → ℝ) →L[ℝ] (S → ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (hA : ContinuousOn A (Icc 0 T)) (j : S) :
    adjBasis A hT hA j T = Pi.single j 1 ∧ ContinuousOn (adjBasis A hT hA j) (Icc 0 T) ∧
      ∀ u ∈ Ioo 0 T, HasDerivAt (adjBasis A hT hA j) (-(A u (adjBasis A hT hA j u))) u :=
  Classical.choose_spec (exists_adjoint_basis A hT hA (Pi.single j 1))

/-- The adjoint solution with terminal value `θ`, linear in `θ`. -/
noncomputable def trajAdj (A : ℝ → (S → ℝ) →L[ℝ] (S → ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (hA : ContinuousOn A (Icc 0 T)) (θ : S → ℝ) (u : ℝ) : S → ℝ :=
  ∑ j, θ j • adjBasis A hT hA j u

theorem trajAdj_T (A : ℝ → (S → ℝ) →L[ℝ] (S → ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (hA : ContinuousOn A (Icc 0 T)) (θ : S → ℝ) : trajAdj A hT hA θ T = θ := by
  simp only [trajAdj, (adjBasis_spec A hT hA _).1]
  funext s; simp [Finset.sum_apply, Pi.single_apply]

theorem continuousOn_trajAdj (A : ℝ → (S → ℝ) →L[ℝ] (S → ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (hA : ContinuousOn A (Icc 0 T)) (θ : S → ℝ) : ContinuousOn (trajAdj A hT hA θ) (Icc 0 T) := by
  unfold trajAdj
  exact continuousOn_finsetSum _ fun j _ => (adjBasis_spec A hT hA j).2.1.const_smul (θ j)

theorem hasDerivAt_trajAdj (A : ℝ → (S → ℝ) →L[ℝ] (S → ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (hA : ContinuousOn A (Icc 0 T)) (θ : S → ℝ) {u : ℝ} (hu : u ∈ Ioo 0 T) :
    HasDerivAt (trajAdj A hT hA θ) (-(A u (trajAdj A hT hA θ u))) u := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (A := fun j u => θ j • adjBasis A hT hA j u)
    (A' := fun j => θ j • (-(A u (adjBasis A hT hA j u)))) fun j _ =>
      ((adjBasis_spec A hT hA j).2.2 u hu).const_smul (θ j)
  have e : -(A u (trajAdj A hT hA θ u)) = ∑ j, θ j • (-(A u (adjBasis A hT hA j u))) := by
    simp only [trajAdj, map_sum, map_smul, smul_neg, Finset.sum_neg_distrib]
  rw [e]
  exact h

/-- The mean `Φ(0)ᵀ z₀`. -/
noncomputable def trajMean (A : ℝ → (S → ℝ) →L[ℝ] (S → ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (hA : ContinuousOn A (Icc 0 T)) (z₀ : S → ℝ) : S → ℝ :=
  fun j => ∑ i, adjBasis A hT hA j 0 i * z₀ i

theorem dot_trajAdj_zero (A : ℝ → (S → ℝ) →L[ℝ] (S → ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (hA : ContinuousOn A (Icc 0 T)) (θ z₀ : S → ℝ) :
    ∑ i, trajAdj A hT hA θ 0 i * z₀ i = ∑ j, θ j * trajMean A hT hA z₀ j := by
  simp only [trajAdj, trajMean, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

/-- The covariance density along the trajectory. -/
noncomputable def trajCovDensity (N : Network S) (κ : RateConstants N) (x : ℝ → Concentration S)
    (A : ℝ → (S → ℝ) →L[ℝ] (S → ℝ)) {T : ℝ} (hT : 0 ≤ T) (hA : ContinuousOn A (Icc 0 T))
    (u : ℝ) (j k : S) : ℝ :=
  ∑ r, N.massActionRate κ r (x u) *
    (∑ s, adjBasis A hT hA j u s * N.reactionVector r s) *
    (∑ s, adjBasis A hT hA k u s * N.reactionVector r s)

/-- The covariance `∫₀ᵀ Φ(u)ᵀ G(x(u)) Φ(u) du`. -/
noncomputable def trajCov (N : Network S) (κ : RateConstants N) (x : ℝ → Concentration S)
    (A : ℝ → (S → ℝ) →L[ℝ] (S → ℝ)) {T : ℝ} (hT : 0 ≤ T) (hA : ContinuousOn A (Icc 0 T)) :
    Matrix S S ℝ :=
  fun j k => ∫ u in (0 : ℝ)..T, N.trajCovDensity κ x A hT hA u j k

theorem quadG_trajAdj (N : Network S) (κ : RateConstants N) (x : ℝ → Concentration S)
    (A : ℝ → (S → ℝ) →L[ℝ] (S → ℝ)) {T : ℝ} (hT : 0 ≤ T) (hA : ContinuousOn A (Icc 0 T))
    (θ : S → ℝ) (u : ℝ) :
    N.quadG κ (x u) (trajAdj A hT hA θ u) =
      ∑ j, ∑ k, θ j * θ k * N.trajCovDensity κ x A hT hA u j k := by
  unfold quadG trajCovDensity trajAdj
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have : ∀ r, (∑ s, (∑ j, θ j * adjBasis A hT hA j u s) * N.reactionVector r s) =
      ∑ j, θ j * ∑ s, adjBasis A hT hA j u s * N.reactionVector r s := by
    intro r
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s _ => by ring
  simp_rw [this]
  have hsq : ∀ r, N.massActionRate κ r (x u) *
      (∑ j, θ j * ∑ s, adjBasis A hT hA j u s * N.reactionVector r s) ^ 2 =
      ∑ j, ∑ k, θ j * θ k * (N.massActionRate κ r (x u) *
        (∑ s, adjBasis A hT hA j u s * N.reactionVector r s) *
        (∑ s, adjBasis A hT hA k u s * N.reactionVector r s)) := by
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

theorem continuousOn_trajCovDensity (N : Network S) (κ : RateConstants N)
    {x : ℝ → Concentration S} {T : ℝ} (hxc : ContinuousOn x (Icc 0 T))
    (A : ℝ → (S → ℝ) →L[ℝ] (S → ℝ)) (hT : 0 ≤ T) (hA : ContinuousOn A (Icc 0 T))
    (j k : S) : ContinuousOn (fun u => N.trajCovDensity κ x A hT hA u j k) (Icc 0 T) := by
  unfold trajCovDensity
  have hρ : ∀ r, ContinuousOn (fun u => N.massActionRate κ r (x u)) (Icc 0 T) := fun r => by
    have : Continuous fun z => N.massActionRate κ r z := by
      unfold massActionRate Complex.massActionMonomial; fun_prop
    exact this.comp_continuousOn hxc
  have hb : ∀ j r, ContinuousOn (fun u => ∑ s, adjBasis A hT hA j u s * N.reactionVector r s)
      (Icc 0 T) := fun j r => continuousOn_finsetSum _ fun s _ =>
    ((continuous_apply s).comp_continuousOn (adjBasis_spec A hT hA j).2.1).mul continuousOn_const
  exact continuousOn_finsetSum _ fun r _ => ((hρ r).mul (hb j r)).mul (hb k r)

theorem integral_quadG_trajAdj (N : Network S) (κ : RateConstants N) {x : ℝ → Concentration S}
    {T : ℝ} (hxc : ContinuousOn x (Icc 0 T)) (A : ℝ → (S → ℝ) →L[ℝ] (S → ℝ)) (hT : 0 ≤ T)
    (hA : ContinuousOn A (Icc 0 T)) (θ : S → ℝ) :
    ∫ u in (0 : ℝ)..T, N.quadG κ (x u) (trajAdj A hT hA θ u) =
      θ ⬝ᵥ (N.trajCov κ x A hT hA *ᵥ θ) := by
  simp_rw [quadG_trajAdj]
  have hint : ∀ j k, IntervalIntegrable (fun u => θ j * θ k * N.trajCovDensity κ x A hT hA u j k)
      MeasureTheory.volume 0 T := fun j k => by
    have hc : ContinuousOn (fun u => θ j * θ k * N.trajCovDensity κ x A hT hA u j k) (Icc 0 T) :=
      continuousOn_const.mul (N.continuousOn_trajCovDensity κ hxc A hT hA j k)
    exact hc.intervalIntegrable_of_Icc hT
  have hint2 : ∀ j, IntervalIntegrable
      (fun u => ∑ k, θ j * θ k * N.trajCovDensity κ x A hT hA u j k) MeasureTheory.volume 0 T :=
    fun j => by
    have hc : ContinuousOn (fun u => ∑ k, θ j * θ k * N.trajCovDensity κ x A hT hA u j k)
        (Icc 0 T) := continuousOn_finsetSum _ fun k _ =>
      continuousOn_const.mul (N.continuousOn_trajCovDensity κ hxc A hT hA j k)
    exact hc.intervalIntegrable_of_Icc hT
  rw [intervalIntegral.integral_finset_sum fun j _ => hint2 j]
  simp only [dotProduct, Matrix.mulVec, trajCov]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_finset_sum fun k _ => hint j k, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_const_mul]
  ring

theorem trajCov_posSemidef (N : Network S) (κ : RateConstants N) {x : ℝ → Concentration S}
    {T : ℝ} (hxc : ContinuousOn x (Icc 0 T)) (hx0 : ∀ u ∈ Icc 0 T, ∀ s, 0 ≤ x u s)
    (A : ℝ → (S → ℝ) →L[ℝ] (S → ℝ)) (hT : 0 ≤ T) (hA : ContinuousOn A (Icc 0 T)) :
    (N.trajCov κ x A hT hA).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v => ?_⟩
  · ext j k
    simp only [Matrix.conjTranspose_apply, star_trivial, trajCov, trajCovDensity]
    congr 1; funext u
    exact Finset.sum_congr rfl fun r _ => by ring
  · simp only [star_trivial]
    rw [← N.integral_quadG_trajAdj κ hxc A hT hA v]
    exact intervalIntegral.integral_nonneg hT fun u hu => N.quadG_nonneg κ (hx0 u hu) _

/-- Transposition as a linear map on continuous linear maps. -/
noncomputable def transposeLin : ((S → ℝ) →L[ℝ] (S → ℝ)) →ₗ[ℝ] ((S → ℝ) →L[ℝ] (S → ℝ)) where
  toFun := transposeCLM
  map_add' := fun J₁ J₂ => by
    ext θ s'
    simp [transposeCLM_apply, mul_add, Finset.sum_add_distrib]
  map_smul' := fun c J => by
    ext θ s'
    simp [transposeCLM_apply, Finset.mul_sum, mul_left_comm]

theorem continuous_transposeCLM :
    Continuous (transposeCLM : ((S → ℝ) →L[ℝ] (S → ℝ)) → ((S → ℝ) →L[ℝ] (S → ℝ))) :=
  (transposeLin (S := S)).continuous_of_finiteDimensional

/-- The adjoint generator along a trajectory, `Df(x(u))ᵀ`. -/
noncomputable def adjGen (N : Network S) (κ : RateConstants N) (x : ℝ → Concentration S) (u : ℝ) :
    (S → ℝ) →L[ℝ] (S → ℝ) :=
  transposeCLM (fderiv ℝ (N.massActionVectorField κ) (x u))

theorem continuousOn_adjGen (N : Network S) (κ : RateConstants N) {x : ℝ → Concentration S}
    {T : ℝ} (hxc : ContinuousOn x (Icc 0 T)) : ContinuousOn (N.adjGen κ x) (Icc 0 T) := by
  have hD : Continuous (fderiv ℝ (N.massActionVectorField κ)) :=
    (N.contDiff_massActionVectorField κ).continuous_fderiv (by simp)
  exact (continuous_transposeCLM.comp hD).comp_continuousOn hxc

/-- The Gaussian limit along the trajectory. -/
noncomputable def gaussLimitTraj (N : Network S) (κ : RateConstants N) {x : ℝ → Concentration S}
    {T : ℝ} (hT : 0 ≤ T) (hxc : ContinuousOn x (Icc 0 T)) (z₀ : S → ℝ) :
    ProbabilityMeasure (EuclideanSpace ℝ S) :=
  ⟨multivariateGaussian (WithLp.toLp 2 (trajMean (N.adjGen κ x) hT (N.continuousOn_adjGen κ hxc) z₀))
    (N.trajCov κ x (N.adjGen κ x) hT (N.continuousOn_adjGen κ hxc)), inferInstance⟩

/-- **Multivariate CLT in distribution along a trajectory, conservative networks.** For a solution
`x` of the mass-action equation on `[0, T]` with values in `[0, R_x]^S` and initial counts with
`⟨w, n_V⟩ ≤ M V` and `√V (n_V/V − x(0)) → z₀`, the law of `√V (X^V(T)/V − x(T))` converges
weakly to the Gaussian with mean `Φ(0)ᵀ z₀` and covariance `∫₀ᵀ Φ(u)ᵀ G(x(u)) Φ(u) du`. -/
theorem multivariate_clt_traj (N : Network S) (κ : RateConstants N) {w : S → ℝ}
    (hwinv : N.IsPInvariant w) (hwpos : ∀ s, 0 < w s) {M T Rx : ℝ} (hM : 0 ≤ M) (hT : 0 < T)
    (hRx : 0 ≤ Rx) (x : ℝ → Concentration S) (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (N.massActionVectorField κ (x t)) t)
    (hxB : ∀ t ∈ Icc 0 T, x t ∈ Icc (0 : Concentration S) fun _ => Rx)
    (n : ℕ → S → ℕ) (hn : ∀ k : ℕ, ∑ s, w s * (n k s : ℝ) ≤ M * ((k : ℝ) + 1))
    {z₀ : S → ℝ} (hz : Tendsto (fun k : ℕ => zeta ((k : ℝ) + 1) (x 0) (n k)) atTop (𝓝 z₀)) :
    Tendsto (fun k : ℕ => N.flucLawP κ ⟨w, hwinv, hwpos⟩ (V := (k : ℝ) + 1) (by positivity) (x T)
      hT.le (n k)) atTop (𝓝 (N.gaussLimitTraj κ hT.le hxc z₀)) := by
  set A := N.adjGen κ x with hA
  have hAc : ContinuousOn A (Icc 0 T) := N.continuousOn_adjGen κ hxc
  have hcons : N.IsConservative := ⟨w, hwinv, hwpos⟩
  have hx0 : ∀ u ∈ Icc 0 T, ∀ s, 0 ≤ x u s := fun u hu s => (hxB u hu).1 s
  refine ProbabilityMeasure.tendsto_of_tendsto_charFun fun t => ?_
  set θ : S → ℝ := WithLp.ofLp t with hθ
  have hadj : ∀ u ∈ Icc 0 T, ∀ v : S → ℝ,
      ∑ s, (-(A u (trajAdj A hT.le hAc θ u))) s * v s =
        -∑ s, trajAdj A hT.le hAc θ u s * fderiv ℝ (N.massActionVectorField κ) (x u) v s := by
    intro u _ v
    have h1 := transpose_dot (fderiv ℝ (N.massActionVectorField κ) (x u))
      (trajAdj A hT.le hAc θ u) v
    have h2 : ∑ s, (-(A u (trajAdj A hT.le hAc θ u))) s * v s =
        -∑ s, (A u (trajAdj A hT.le hAc θ u)) s * v s := by
      simp [Finset.sum_neg_distrib]
    rw [h2]
    exact congrArg Neg.neg h1
  have h := N.nonlinear_clt_traj κ hwinv hwpos hM hT hRx x hxc hx hxB (trajAdj A hT.le hAc θ)
    (fun u => -(A u (trajAdj A hT.le hAc θ u))) (continuousOn_trajAdj A hT.le hAc θ)
    (fun u hu => hasDerivAt_trajAdj A hT.le hAc θ hu) hadj n hn hz
  simp only [trajAdj_T] at h
  rw [dot_trajAdj_zero, N.integral_quadG_trajAdj κ hxc A hT.le hAc] at h
  have hlhs : ∀ k : ℕ, charFun ((N.flucLawP κ ⟨w, hwinv, hwpos⟩ (V := (k : ℝ) + 1)
      (by positivity) (x T) hT.le (n k) : ProbabilityMeasure (EuclideanSpace ℝ S)) :
        Measure (EuclideanSpace ℝ S)) t =
      ∑' m, (N.transition (N.volumeScale κ ((k : ℝ) + 1) (by positivity)) T (n k) m : ℂ) *
        Complex.exp (I * ((∑ s, θ s * zeta ((k : ℝ) + 1) (x T) m s : ℝ) : ℂ)) := fun k =>
    N.charFun_flucLaw κ hcons _ (x T) hT.le (n k) t
  have hpsd := N.trajCov_posSemidef κ hxc hx0 A hT.le hAc
  have hrhs : charFun ((N.gaussLimitTraj κ hT.le hxc z₀ : ProbabilityMeasure (EuclideanSpace ℝ S)) :
      Measure (EuclideanSpace ℝ S)) t =
      Complex.exp (I * ((∑ j, θ j * trajMean A hT.le hAc z₀ j : ℝ) : ℂ) -
        ((θ ⬝ᵥ (N.trajCov κ x A hT.le hAc *ᵥ θ) / 2 : ℝ) : ℂ)) := by
    show charFun (multivariateGaussian (WithLp.toLp 2 (trajMean A hT.le hAc z₀))
      (N.trajCov κ x A hT.le hAc)) t = _
    rw [charFun_multivariateGaussian hpsd]
    congr 1
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [WithLp.ofLp_toLp, star_trivial, dotProduct]
    push_cast
    have e : (∑ x, ((trajMean A hT.le hAc z₀ x : ℝ) : ℂ) * ((WithLp.ofLp t x : ℝ) : ℂ)) =
        ∑ x, ((WithLp.ofLp t x : ℝ) : ℂ) * ((trajMean A hT.le hAc z₀ x : ℝ) : ℂ) :=
      Finset.sum_congr rfl fun x _ => mul_comm _ _
    rw [e]
    ring
  rw [hrhs]
  exact h.congr fun k => (hlhs k).symm

/-- **Multivariate CLT in distribution along a trajectory, any network.** If the chains are
stochastic from the initial counts (e.g. `MonoWeight` networks) and `√V (n_V/V − x(0)) → z₀`,
the law of `√V (X^V(T)/V − x(T))` converges weakly to the same Gaussian. -/
theorem multivariate_clt_traj_open (N : Network S) (κ : RateConstants N) {T Rx : ℝ} (hT : 0 < T)
    (hRx : 0 ≤ Rx) (x : ℝ → Concentration S) (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (N.massActionVectorField κ (x t)) t)
    (hxB : ∀ t ∈ Icc 0 T, x t ∈ Icc (0 : Concentration S) fun _ => Rx) (n : ℕ → S → ℕ)
    (hstoch : ∀ k : ℕ, HasSum (fun m => N.transition (N.volumeScale κ ((k : ℝ) + 1)
      (by positivity)) T (n k) m) 1)
    {z₀ : S → ℝ} (hz : Tendsto (fun k : ℕ => zeta ((k : ℝ) + 1) (x 0) (n k)) atTop (𝓝 z₀)) :
    Tendsto (fun k : ℕ => N.flucLawOpenP κ (V := (k : ℝ) + 1) (by positivity) (x T) hT.le (n k)
      (hstoch k)) atTop (𝓝 (N.gaussLimitTraj κ hT.le hxc z₀)) := by
  set A := N.adjGen κ x with hA
  have hAc : ContinuousOn A (Icc 0 T) := N.continuousOn_adjGen κ hxc
  have hx0 : ∀ u ∈ Icc 0 T, ∀ s, 0 ≤ x u s := fun u hu s => (hxB u hu).1 s
  refine ProbabilityMeasure.tendsto_of_tendsto_charFun fun t => ?_
  set θ : S → ℝ := WithLp.ofLp t with hθ
  have hadj : ∀ u ∈ Icc 0 T, ∀ v : S → ℝ,
      ∑ s, (-(A u (trajAdj A hT.le hAc θ u))) s * v s =
        -∑ s, trajAdj A hT.le hAc θ u s * fderiv ℝ (N.massActionVectorField κ) (x u) v s := by
    intro u _ v
    have h1 := transpose_dot (fderiv ℝ (N.massActionVectorField κ) (x u))
      (trajAdj A hT.le hAc θ u) v
    have h2 : ∑ s, (-(A u (trajAdj A hT.le hAc θ u))) s * v s =
        -∑ s, (A u (trajAdj A hT.le hAc θ u)) s * v s := by
      simp [Finset.sum_neg_distrib]
    rw [h2]
    exact congrArg Neg.neg h1
  have h := N.nonlinear_clt_open κ hT hRx x hxc hx hxB (trajAdj A hT.le hAc θ)
    (fun u => -(A u (trajAdj A hT.le hAc θ u))) (continuousOn_trajAdj A hT.le hAc θ)
    (fun u hu => hasDerivAt_trajAdj A hT.le hAc θ hu) hadj n hz
  simp only [trajAdj_T] at h
  rw [dot_trajAdj_zero, N.integral_quadG_trajAdj κ hxc A hT.le hAc] at h
  have hlhs : ∀ k : ℕ, charFun ((N.flucLawOpenP κ (V := (k : ℝ) + 1) (by positivity) (x T) hT.le
      (n k) (hstoch k) : ProbabilityMeasure (EuclideanSpace ℝ S)) :
        Measure (EuclideanSpace ℝ S)) t =
      ∑' m, (N.transition (N.volumeScale κ ((k : ℝ) + 1) (by positivity)) T (n k) m : ℂ) *
        Complex.exp (I * ((∑ s, θ s * zeta ((k : ℝ) + 1) (x T) m s : ℝ) : ℂ)) := fun k =>
    N.charFun_flucLawOpen κ _ (x T) hT.le (n k) (hstoch k) t
  have hpsd := N.trajCov_posSemidef κ hxc hx0 A hT.le hAc
  have hrhs : charFun ((N.gaussLimitTraj κ hT.le hxc z₀ : ProbabilityMeasure (EuclideanSpace ℝ S)) :
      Measure (EuclideanSpace ℝ S)) t =
      Complex.exp (I * ((∑ j, θ j * trajMean A hT.le hAc z₀ j : ℝ) : ℂ) -
        ((θ ⬝ᵥ (N.trajCov κ x A hT.le hAc *ᵥ θ) / 2 : ℝ) : ℂ)) := by
    show charFun (multivariateGaussian (WithLp.toLp 2 (trajMean A hT.le hAc z₀))
      (N.trajCov κ x A hT.le hAc)) t = _
    rw [charFun_multivariateGaussian hpsd]
    congr 1
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [WithLp.ofLp_toLp, star_trivial, dotProduct]
    push_cast
    have e : (∑ x, ((trajMean A hT.le hAc z₀ x : ℝ) : ℂ) * ((WithLp.ofLp t x : ℝ) : ℂ)) =
        ∑ x, ((WithLp.ofLp t x : ℝ) : ℂ) * ((trajMean A hT.le hAc z₀ x : ℝ) : ℂ) :=
      Finset.sum_congr rfl fun x _ => mul_comm _ _
    rw [e]
    ring
  rw [hrhs]
  exact h.congr fun k => (hlhs k).symm

end Network
end CRNT

namespace CRNT
namespace Examples
namespace IsomerMultivariateCLT

open Network IsomerCLT

/-- **Multivariate CLT in distribution along the moving solution of `X ⇌ Y`.** Started from
`(2V, 0)` molecules, the law of `√V (X^V(T)/V − x(T))`, `x(t) = (1 + e^{−2t}, 1 − e^{−2t})`,
converges weakly to the centred Gaussian `gaussLimitTraj`. -/
theorem clt {T : ℝ} (hT : 0 < T) :
    Tendsto (fun k : ℕ => net.flucLawP κ ⟨w, w_inv, w_pos⟩ (V := (k : ℝ) + 1) (by positivity)
      (xsol T) hT.le ![2 * (k + 1), 0]) atTop
      (𝓝 (net.gaussLimitTraj κ hT.le
        (fun t _ => (hasDerivAt_xsol t).continuousAt.continuousWithinAt) 0)) := by
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
  exact net.multivariate_clt_traj κ w_inv w_pos (M := 2) (Rx := 2) (by norm_num) hT
    (by norm_num) xsol (fun t _ => (hasDerivAt_xsol t).continuousAt.continuousWithinAt)
    (fun t _ => hasDerivAt_xsol t) (fun t ht => xsol_mem ht.1) (fun k => ![2 * (k + 1), 0])
    (fun k => by simp [w, Fin.sum_univ_two]) hz

end IsomerMultivariateCLT
end Examples
end CRNT
