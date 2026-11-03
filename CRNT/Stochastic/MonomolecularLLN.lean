import CRNT.Stochastic.JahnkeHuisinga

/-!
# A law of large numbers for monomolecular density-dependent families

Product-Poisson laws have total mass one (`hasSum_productPoissonPMF`), factorial moments
`∑_n π_c(n) n_s^{(k)} = c_s^k` (`tsum_productPoissonPMF_mul_descFactorial`) and variance
`∑_n π_c(n) (n_s − c_s)² = c_s` (`tsum_productPoissonPMF_mul_sq`), hence Chebyshev's bound
(`tsum_productPoissonPMF_dev_le`).

For a monomolecular network, scale the zero-order rates by `V` (`scaleInflow`). If `μ(t) > 0`
solves the mass-action equation, the chain started from Poisson(`V μ(0)`) has law
Poisson(`V μ(T)`) at time `T` (Jahnke–Huisinga), so the probability that the concentration
`X_s(T)/V` deviates from `μ_s(T)` by at least `ε` is at most `μ_s(T) / (V ε²)`
(`monomolecular_lln`): Kurtz's law of large numbers at fixed times, with an explicit rate, for
this class.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

omit [DecidableEq S] in
/-- Product-Poisson laws have total mass one. -/
theorem hasSum_productPoissonPMF {c : Concentration S} (hc : c.Nonnegative) :
    HasSum (productPoissonPMF c) 1 := by
  have hs : Summable (productPoissonPMF c) := summable_of_sum_le (c := 1)
    (fun n => productPoissonPMF_nonneg hc n) (sum_productPoissonPMF_le_one hc)
  have h := tsum_measure_preimage_singleton (μ := productPoisson c hc)
    (s := (Set.univ : Set (S → ℕ))) Set.countable_univ (f := id)
    (fun y _ => measurableSet_singleton y)
  simp only [Set.preimage_id, measure_univ, Set.preimage_id_eq, id] at h
  rw [tsum_univ (f := fun b => productPoisson c hc {b})] at h
  simp only [productPoisson_singleton] at h
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => productPoissonPMF_nonneg hc n) hs,
    ENNReal.ofReal_eq_one] at h
  exact h ▸ hs.hasSum

omit [DecidableEq S] in
theorem tsum_shiftedPMF {c : Concentration S} (hc : c.Nonnegative) (y : S → ℕ) :
    ∑' n, shiftedPMF c n y = 1 := by
  have hinj : Function.Injective fun m : S → ℕ => m + y := fun a b h => by
    funext s; have := congrFun h s; simpa using this
  have hsupp : Function.support (fun n => shiftedPMF c n y) ⊆ Set.range fun m : S → ℕ => m + y := by
    intro n hn
    by_contra hr
    apply hn
    simp only [shiftedPMF]
    rw [if_neg]
    intro hle
    exact hr ⟨fun s => n s - y s, funext fun s => by simp [Nat.sub_add_cancel (hle s)]⟩
  rw [← hinj.tsum_eq hsupp]
  have : ∀ m : S → ℕ, shiftedPMF c (m + y) y = productPoissonPMF c m := fun m => by
    simp only [shiftedPMF]
    rw [if_pos fun s => by simp]
    congr 1; funext s; simp
  simp only [this]
  exact (hasSum_productPoissonPMF hc).tsum_eq

omit [DecidableEq S] in
/-- `π_c(n) ∏_s n_s^{(y_s)} = c^y π_c(n − y)` at every count. -/
theorem productPoissonPMF_mul_prod_descFactorial (c : Concentration S) (n y : S → ℕ) :
    productPoissonPMF c n * ∏ s, ((n s).descFactorial (y s) : ℝ) =
      (∏ s, c s ^ y s) * shiftedPMF c n y := by
  unfold shiftedPMF
  split_ifs with hle
  · unfold productPoissonPMF
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun s _ => poissonFactor_mul_descFactorial (c s) (hle s)
  · push Not at hle
    obtain ⟨s, hs⟩ := hle
    rw [mul_zero, Finset.prod_eq_zero (Finset.mem_univ s)
      (by exact_mod_cast Nat.descFactorial_eq_zero_iff_lt.mpr hs), mul_zero]

/-- Factorial moments of product-Poisson laws. -/
theorem hasSum_productPoissonPMF_mul_descFactorial {c : Concentration S} (hc : c.Nonnegative)
    (s : S) (k : ℕ) :
    HasSum (fun n => productPoissonPMF c n * ((n s).descFactorial k : ℝ)) (c s ^ k) := by
  set y : S → ℕ := fun t => if t = s then k else 0 with hy
  have h : ∀ n, productPoissonPMF c n * ((n s).descFactorial k : ℝ) =
      c s ^ k * shiftedPMF c n y := by
    intro n
    have := productPoissonPMF_mul_prod_descFactorial c n y
    rw [Finset.prod_eq_single s (fun t _ ht => by simp [hy, ht])
      (by simp), Finset.prod_eq_single s (fun t _ ht => by simp [hy, ht]) (by simp)] at this
    simpa [hy] using this
  have hs : Summable fun n => shiftedPMF c n y :=
    summable_of_sum_le (c := 1) (fun n => shiftedPMF_nonneg c hc n y) fun F =>
      (summable_shiftedPMF hc y).sum_le_tsum F (fun n _ => shiftedPMF_nonneg c hc n y) |>.trans
        (tsum_shiftedPMF hc y).le
  simp only [h]
  have := (hs.hasSum.mul_left (c s ^ k))
  rwa [tsum_shiftedPMF hc y, mul_one] at this

theorem descFactorial_two_cast (m : ℕ) : ((m.descFactorial 2 : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) - 1) := by
  rcases m with _ | m
  · simp
  · simp [Nat.descFactorial_succ, Nat.succ_sub_one]
    ring

/-- The variance of a coordinate of a product-Poisson law. -/
theorem hasSum_productPoissonPMF_mul_sq {c : Concentration S} (hc : c.Nonnegative) (s : S) :
    HasSum (fun n => productPoissonPMF c n * ((n s : ℝ) - c s) ^ 2) (c s) := by
  have h0 := hasSum_productPoissonPMF hc
  have h1 := hasSum_productPoissonPMF_mul_descFactorial hc s 1
  have h2 := hasSum_productPoissonPMF_mul_descFactorial hc s 2
  simp only [Nat.descFactorial_one] at h1
  simp only [descFactorial_two_cast] at h2
  have := ((h2.add h1).add ((h1.mul_left (-2 * c s)).add (h0.mul_left (c s ^ 2))))
  convert this using 1
  · funext n; ring
  · ring

/-- **Chebyshev's bound** for a coordinate of a product-Poisson law. -/
theorem tsum_productPoissonPMF_dev_le {c : Concentration S} (hc : c.Nonnegative) (s : S)
    {a : ℝ} (ha : 0 < a) :
    ∑' n, productPoissonPMF c n * (if a ≤ |(n s : ℝ) - c s| then 1 else 0) ≤ c s / a ^ 2 := by
  have hv := hasSum_productPoissonPMF_mul_sq hc s
  have hle : ∀ n, productPoissonPMF c n * (if a ≤ |(n s : ℝ) - c s| then 1 else 0) ≤
      productPoissonPMF c n * ((n s : ℝ) - c s) ^ 2 / a ^ 2 := by
    intro n
    have hπ := productPoissonPMF_nonneg hc n
    split_ifs with h
    · rw [mul_one, le_div_iff₀ (by positivity)]
      have : a ^ 2 ≤ ((n s : ℝ) - c s) ^ 2 := by
        rw [← sq_abs ((n s : ℝ) - c s)]
        exact pow_le_pow_left₀ ha.le h 2
      nlinarith
    · rw [mul_zero]; positivity
  have hs : Summable fun n => productPoissonPMF c n * ((n s : ℝ) - c s) ^ 2 / a ^ 2 :=
    hv.summable.div_const _
  calc ∑' n, productPoissonPMF c n * (if a ≤ |(n s : ℝ) - c s| then 1 else 0)
      ≤ ∑' n, productPoissonPMF c n * ((n s : ℝ) - c s) ^ 2 / a ^ 2 :=
        Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le (fun n => mul_nonneg
          (productPoissonPMF_nonneg hc n) (by split_ifs <;> norm_num)) hle hs) hs
    _ = c s / a ^ 2 := by rw [tsum_div_const, hv.tsum_eq]

/-- Zero-order rates scaled by the system size `V`. -/
def scaleInflow (N : Network S) (κ : RateConstants N) (V : ℝ) (hV : 0 < V) : RateConstants N :=
  ⟨fun r => if ∀ s, (N.reaction r).source s = 0 then V * κ.k r else κ.k r, fun r => by
    split_ifs
    · exact mul_pos hV (κ.positive r)
    · exact κ.positive r⟩

theorem massActionRate_scaleInflow (N : Network S) (κ : RateConstants N)
    (hmono : N.IsMonomolecular) {V : ℝ} (hV : 0 < V) (r : N.R) (x : Concentration S) :
    N.massActionRate (N.scaleInflow κ V hV) r (V • x) = V * N.massActionRate κ r x := by
  unfold massActionRate Complex.massActionMonomial
  show (if ∀ s, (N.reaction r).source s = 0 then V * κ.k r else κ.k r) *
    ∏ s, (V • x) s ^ (N.reaction r).source s = _
  rcases complex_of_sum_le_one (hmono r).1 with hz | ⟨j, hj, ho⟩
  · rw [if_pos hz]; simp [hz]
  · have hnz : ¬ ∀ s, (N.reaction r).source s = 0 := fun h => by have := h j; omega
    rw [if_neg hnz, Finset.prod_eq_single j (fun s _ hs => by rw [ho s hs, pow_zero]) (by simp),
      Finset.prod_eq_single j (fun s _ hs => by rw [ho s hs, pow_zero]) (by simp), hj]
    simp only [Pi.smul_apply, smul_eq_mul, pow_one]
    ring

theorem massActionVectorField_scaleInflow (N : Network S) (κ : RateConstants N)
    (hmono : N.IsMonomolecular) {V : ℝ} (hV : 0 < V) (x : Concentration S) :
    N.massActionVectorField (N.scaleInflow κ V hV) (V • x) = V • N.massActionVectorField κ x := by
  funext s
  simp only [massActionVectorField_apply, massActionRate_scaleInflow N κ hmono hV, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => by ring

/-- **Law of large numbers for monomolecular networks.** Scaling the zero-order rates by `V`
and starting from Poisson(`V μ(0)`), the probability at time `T` that the concentration of `s`
deviates from the solution `μ_s(T)` of the mass-action equation by at least `ε` is at most
`μ_s(T) / (V ε²)`. -/
theorem monomolecular_lln (N : Network S) (κ : RateConstants N) (hmono : N.IsMonomolecular)
    {T : ℝ} (hT : 0 < T) (μ : ℝ → Concentration S) (hpos : ∀ t ∈ Icc 0 T, (μ t).Positive)
    (hcont : ContinuousOn μ (Icc 0 T))
    (hode : ∀ t ∈ Ioo 0 T, HasDerivAt μ (N.massActionVectorField κ (μ t)) t)
    {V : ℝ} (hV : 0 < V) (s : S) {ε : ℝ} (hε : 0 < ε) :
    ∑' m, (∑' n, productPoissonPMF (V • μ 0) n * N.transition (N.scaleInflow κ V hV) T n m) *
      (if ε ≤ |(m s : ℝ) / V - μ T s| then 1 else 0) ≤ μ T s / (V * ε ^ 2) := by
  have hJH := N.jahnke_huisinga (N.scaleInflow κ V hV) hmono hT (fun t => V • μ t)
    (fun t ht q => by simp only [Pi.smul_apply, smul_eq_mul]; exact mul_pos hV (hpos t ht q))
    (hcont.const_smul V) (fun t ht => by
      rw [massActionVectorField_scaleInflow N κ hmono hV]
      exact (hode t ht).const_smul V)
  simp only [hJH]
  have hiff : ∀ m : S → ℕ, (ε ≤ |(m s : ℝ) / V - μ T s|) ↔
      (V * ε ≤ |(m s : ℝ) - (V • μ T) s|) := by
    intro m
    have : (m s : ℝ) - (V • μ T) s = V * ((m s : ℝ) / V - μ T s) := by
      simp only [Pi.smul_apply, smul_eq_mul]; field_simp
    rw [this, abs_mul, abs_of_pos hV]
    constructor
    · intro h; exact mul_le_mul_of_nonneg_left h hV.le
    · intro h; exact le_of_mul_le_mul_left h hV
  simp_rw [hiff]
  have hc : (V • μ T).Nonnegative := fun q => by
    simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hV.le (hpos T ⟨hT.le, le_rfl⟩ q).le
  have := tsum_productPoissonPMF_dev_le hc s (mul_pos hV hε)
  calc _ ≤ (V • μ T) s / (V * ε) ^ 2 := this
    _ = μ T s / (V * ε ^ 2) := by
        simp only [Pi.smul_apply, smul_eq_mul]; field_simp

end Network
end CRNT
