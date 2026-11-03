import CRNT.Stochastic.MonomolecularLLN
import CRNT.Stochastic.PoissonCLT

/-!
# The central limit theorem for monomolecular networks at a fixed time

For a monomolecular network with the zero-order rates scaled by `V` and the chain started from
Poisson(`V μ(0)`), the law at time `T` is Poisson(`V μ(T)`) (Jahnke–Huisinga), and the fluctuation
`√V (X_s(T)/V − μ_s(T)) = (X_s(T) − V μ_s(T))/√V` of every species converges in distribution to
`N(0, μ_s(T))` as `V → ∞` (`monomolecular_clt`). The Gaussian variance equals the mean, as for the
linear noise approximation of these networks.
-/

open MeasureTheory ProbabilityTheory Filter Complex Set
open scoped Topology NNReal BigOperators

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The species-`s` marginal of the product-Poisson law is Poisson(`c_s`). -/
theorem productPoisson_map_eval (c : Concentration S) (hc : c.Nonnegative) (s : S) :
    (productPoisson c hc).map (Function.eval s) = poissonMeasure ⟨c s, hc s⟩ := by
  unfold productPoisson
  rw [Measure.pi_map_eval]
  simp
  rfl

/-- The fluctuation law `(X_s − c_s)/√V` of species `s` under the product-Poisson law `c`. -/
noncomputable def speciesFluct (c : Concentration S) (hc : c.Nonnegative) (s : S) (V : ℝ) :
    Measure ℝ :=
  (productPoisson c hc).map fun m => ((m s : ℝ) - c s) / Real.sqrt V

instance (c : Concentration S) (hc : c.Nonnegative) (s : S) (V : ℝ) :
    IsProbabilityMeasure (speciesFluct c hc s V) := by
  unfold speciesFluct; infer_instance

theorem speciesFluct_eq (c : Concentration S) (hc : c.Nonnegative) (s : S) {V : ℝ} (hV : 0 < V)
    (hcs : 0 < c s) :
    speciesFluct c hc s V = (poissonFluct ⟨c s, hc s⟩).map (Real.sqrt (c s / V) * ·) := by
  have hm1 : Measurable fun m : S → ℕ => m s := measurable_pi_apply s
  unfold speciesFluct poissonFluct
  rw [show (fun m : S → ℕ => ((m s : ℝ) - c s) / Real.sqrt V) =
      (fun k : ℕ => ((k : ℝ) - c s) / Real.sqrt V) ∘ Function.eval s from rfl,
    ← Measure.map_map (Measurable.of_discrete) hm1, productPoisson_map_eval,
    Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (Measurable.of_discrete)]
  congr 1
  funext k
  change ((k : ℝ) - c s) / Real.sqrt V =
    Real.sqrt (c s / V) * ((Real.sqrt (c s))⁻¹ * ((k : ℝ) + -(c s)))
  have hs : 0 < Real.sqrt (c s) := Real.sqrt_pos.mpr hcs
  have hsV : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV
  rw [Real.sqrt_div hcs.le]
  field_simp
  ring

/-- The fluctuation law as a probability measure. -/
noncomputable def speciesFluctPM (c : Concentration S) (hc : c.Nonnegative) (s : S) (V : ℝ) :
    ProbabilityMeasure ℝ := ⟨speciesFluct c hc s V, inferInstance⟩

/-- The centered Gaussian with variance `v`. -/
noncomputable def gaussianPM (v : ℝ≥0) : ProbabilityMeasure ℝ := ⟨gaussianReal 0 v, inferInstance⟩

theorem charFun_gaussianPM (v : ℝ≥0) (u : ℝ) :
    charFun (gaussianPM v : Measure ℝ) u = cexp (-((v : ℝ) : ℂ) * (u : ℂ) ^ 2 / 2) := by
  simp only [gaussianPM, ProbabilityMeasure.coe_mk]
  rw [charFun_gaussianReal]
  congr 1
  push_cast
  ring

/-- **CLT for the scaled product-Poisson family**: under Poisson(`V μ`) with `V = n + 1`, the
fluctuation of species `s` converges to `N(0, μ_s)`. -/
theorem tendsto_speciesFluct (μ : Concentration S) (hμ : μ.Positive) (s : S)
    (hc : ∀ n : ℕ, (((n : ℝ) + 1) • μ).Nonnegative) :
    Tendsto (fun n : ℕ => speciesFluctPM (((n : ℝ) + 1) • μ) (hc n) s ((n : ℝ) + 1)) atTop
      (𝓝 (gaussianPM (⟨μ s, (hμ s).le⟩ : ℝ≥0))) := by
  rw [ProbabilityMeasure.tendsto_iff_tendsto_charFun]
  intro u
  set r : ℕ → ℝ≥0 := fun n => ⟨(((n : ℝ) + 1) • μ) s, hc n s⟩ with hr
  have hrt : Tendsto (fun n => (r n : ℝ)) atTop atTop := by
    simp only [hr, NNReal.coe_mk, Pi.smul_apply, smul_eq_mul]
    exact Tendsto.atTop_mul_const (hμ s) (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hP := (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp (tendsto_poissonFluct hrt))
    (Real.sqrt (μ s) * u)
  have heq : ∀ n : ℕ, charFun (speciesFluctPM (((n : ℝ) + 1) • μ) (hc n) s ((n : ℝ) + 1) :
      Measure ℝ) u = charFun (poissonFluctPM (r n) : Measure ℝ) (Real.sqrt (μ s) * u) := by
    intro n
    have hV : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hcs : 0 < (((n : ℝ) + 1) • μ) s := by
      simp only [Pi.smul_apply, smul_eq_mul]; exact mul_pos hV (hμ s)
    simp only [speciesFluctPM, poissonFluctPM, ProbabilityMeasure.coe_mk]
    rw [speciesFluct_eq _ _ s hV hcs, charFun_map_mul]
    congr 2
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_div_cancel_left₀ _ hV.ne']
  simp_rw [heq]
  erw [charFun_gaussianPM]
  convert hP using 2
  simp only [stdGaussianPM, ProbabilityMeasure.coe_mk]
  erw [charFun_gaussianReal]
  congr 1
  have h : ((Real.sqrt (μ s) : ℝ) : ℂ) ^ 2 = (μ s : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (hμ s).le]
  change -(((⟨μ s, (hμ s).le⟩ : ℝ≥0) : ℝ) : ℂ) * (u : ℂ) ^ 2 / 2 =
    ((Real.sqrt (μ s) * u : ℝ) : ℂ) * ((0 : ℝ) : ℂ) * I -
      (((1 : ℝ≥0) : ℝ) : ℂ) * ((Real.sqrt (μ s) * u : ℝ) : ℂ) ^ 2 / 2
  simp only [NNReal.coe_mk, NNReal.coe_one]
  push_cast
  rw [mul_pow, h]
  ring

/-- **Fixed-time CLT for monomolecular networks.** With the zero-order rates scaled by
`V = n + 1` and the chain started from Poisson(`V μ(0)`), the law at time `T` is
Poisson(`V μ(T)`), and the fluctuation `(X_s(T) − V μ_s(T))/√V` converges in distribution to
`N(0, μ_s(T))`. -/
theorem monomolecular_clt (N : Network S) (κ : RateConstants N) (hmono : N.IsMonomolecular)
    {T : ℝ} (hT : 0 < T) (μ : ℝ → Concentration S) (hpos : ∀ t ∈ Icc 0 T, (μ t).Positive)
    (hcont : ContinuousOn μ (Icc 0 T))
    (hode : ∀ t ∈ Ioo 0 T, HasDerivAt μ (N.massActionVectorField κ (μ t)) t) (s : S)
    (hc : ∀ n : ℕ, (((n : ℝ) + 1) • μ T).Nonnegative) :
    (∀ (n : ℕ) (m : S → ℕ), ∑' x, productPoissonPMF (((n : ℝ) + 1) • μ 0) x *
        N.transition (N.scaleInflow κ ((n : ℝ) + 1) (Nat.cast_add_one_pos n)) T x m =
          productPoissonPMF (((n : ℝ) + 1) • μ T) m) ∧
      Tendsto (fun n : ℕ => speciesFluctPM (((n : ℝ) + 1) • μ T) (hc n) s ((n : ℝ) + 1)) atTop
        (𝓝 (gaussianPM (⟨μ T s, (hpos T ⟨hT.le, le_rfl⟩ s).le⟩ : ℝ≥0))) := by
  refine ⟨fun n m => ?_, tendsto_speciesFluct (μ T) (hpos T ⟨hT.le, le_rfl⟩) s hc⟩
  have hV : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  exact N.jahnke_huisinga (N.scaleInflow κ ((n : ℝ) + 1) hV) hmono hT
    (fun t => ((n : ℝ) + 1) • μ t)
    (fun t ht q => by simp only [Pi.smul_apply, smul_eq_mul]; exact mul_pos hV (hpos t ht q))
    (hcont.const_smul ((n : ℝ) + 1)) (fun t ht => by
      rw [massActionVectorField_scaleInflow N κ hmono hV]
      exact (hode t ht).const_smul ((n : ℝ) + 1)) m

end Network

namespace Examples
namespace PoissonBirthDeath

open Network

/-- **CLT instance**: for `0 ⇌ X` with unit rates and inflow scaled by `V = n + 1`, started from
Poisson(`2V`), the fluctuation `(X(1) − V(1 + e^{−1}))/√V` converges in distribution to
`N(0, 1 + e^{−1})`. -/
theorem clt :
    Tendsto (fun n : ℕ => speciesFluctPM (((n : ℝ) + 1) • μ 1)
        (fun q => by simp only [Pi.smul_apply, smul_eq_mul, μ]; positivity) () ((n : ℝ) + 1))
      atTop (𝓝 (gaussianPM (⟨1 + Real.exp (-1), by positivity⟩ : ℝ≥0))) :=
  (net.monomolecular_clt κ monomolecular one_pos μ (fun t _ q => by simp only [μ]; positivity)
    (by unfold μ; fun_prop) (fun t _ => ode t) () _).2

end PoissonBirthDeath
end Examples

end CRNT
