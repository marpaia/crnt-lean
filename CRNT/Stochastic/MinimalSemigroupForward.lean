import CRNT.Stochastic.MinimalSemigroupErgodic
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The Kolmogorov forward equation for the minimal transition function

With the generator matrix `Q(c, b) = ∑ᵢ rateᵢ(c) [nextᵢ c = b] − q(c) [c = b]`, the minimal
transition function satisfies, for `t > 0` and `∑_c P(t)(a, c) q(c) < ∞`,

`∂ₜ P(t)(a, b) = ∑_c P(t)(a, c) Q(c, b)`  (`hasDerivAt_Pmin_forward`; Feller 1940).

No non-explosion assumption is used. Proof: the right difference quotient is
`∑_c P(t)(a, c) (P(h)(c, b) − [c = b]) / h` (Chapman–Kolmogorov); each quotient tends to `Q(c, b)`
(`tendsto_slope_Pmin_zero`, mean value theorem and continuity of the backward right-hand side at
`0`) and is bounded by `q(c)`, so Tannery's theorem gives the limit, which must equal the backward
derivative.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace CRNT

namespace JumpSystem

variable {α : Type*} [DecidableEq α] (J : JumpSystem α)

/-- The generator matrix. -/
noncomputable def Q (c b : α) : ℝ :=
  ∑ i, J.rate i c * (if J.next i c = b then 1 else 0) - J.q c * (if c = b then 1 else 0)

theorem Pmin_zero (a b : α) : J.Pmin 0 a b = if a = b then 1 else 0 := by
  have h : ∀ k, J.P k 0 a b = if a = b then 1 else 0 := by
    intro k; cases k <;> simp [P_zero, P_succ]
  simp [Pmin, h]

/-- The backward right-hand side. -/
noncomputable def bwd (c b : α) (s : ℝ) : ℝ :=
  -J.q c * J.Pmin s c b + ∑ i, J.rate i c * J.Pmin s (J.next i c) b

theorem continuousOn_bwd (c b : α) : ContinuousOn (J.bwd c b) (Ici 0) := by
  unfold bwd
  exact (continuousOn_const.mul (J.continuousOn_Pmin c b)).add
    (continuousOn_finsetSum _ fun i _ => continuousOn_const.mul (J.continuousOn_Pmin _ b))

theorem bwd_zero (c b : α) : J.bwd c b 0 = J.Q c b := by
  simp only [bwd, Pmin_zero, Q]
  ring

/-- **Right derivative at `0`:** `(P(h)(c, b) − [c = b]) / h → Q(c, b)` as `h → 0⁺`. -/
theorem tendsto_slope_Pmin_zero (c b : α) :
    Tendsto (fun h => (J.Pmin h c b - (if c = b then 1 else 0)) / h) (𝓝[>] 0)
      (𝓝 (J.Q c b)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hcw : ContinuousWithinAt (J.bwd c b) (Ici 0) 0 := J.continuousOn_bwd c b 0 (Set.mem_Ici.mpr le_rfl)
  obtain ⟨η, hη, hηc⟩ := Metric.continuousWithinAt_iff.mp hcw ε hε
  refine ⟨η, hη, fun h hh hdist => ?_⟩
  have hh0 : 0 < h := hh
  have hhη : h < η := by rw [Real.dist_eq, sub_zero, abs_of_pos hh0] at hdist; exact hdist
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (fun s => J.Pmin s c b) (J.bwd c b) hh0
    ((J.continuousOn_Pmin c b).mono Icc_subset_Ici_self) fun x hx => J.hasDerivAt_Pmin x hx.1 c b
  rw [Pmin_zero, sub_zero] at hslope
  rw [← hslope, ← J.bwd_zero c b]
  refine hηc (le_of_lt hξ.1) ?_
  rw [Real.dist_eq, sub_zero, abs_of_pos hξ.1]
  linarith [hξ.2]

/-- `|P(h)(c, b) − [c = b]| ≤ q(c) h`. -/
theorem abs_Pmin_sub_le (c b : α) {h : ℝ} (hh : 0 ≤ h) :
    |J.Pmin h c b - (if c = b then 1 else 0)| ≤ J.q c * h := by
  have hself : Real.exp (-(J.q c * h)) ≤ J.Pmin h c c := by
    have := J.P_le_Pmin 0 hh c c
    simpa [P_zero] using this
  have hexp : 1 - J.q c * h ≤ Real.exp (-(J.q c * h)) := by
    have := Real.add_one_le_exp (-(J.q c * h)); linarith
  by_cases hcb : c = b
  · subst hcb
    rw [if_pos rfl, abs_of_nonpos (by linarith [J.Pmin_le_one h hh c c])]
    linarith
  · rw [if_neg hcb, sub_zero, abs_of_nonneg (J.Pmin_nonneg h hh c b)]
    have h2 := J.sum_Pmin_le_one h hh c {b, c}
    rw [Finset.sum_pair (Ne.symm hcb)] at h2
    linarith

/-- **Kolmogorov forward equation.** -/
theorem hasDerivAt_Pmin_forward {t : ℝ} (ht : 0 < t) (a b : α)
    (hsum : Summable fun c => J.Pmin t a c * J.q c) :
    HasDerivAt (fun s => J.Pmin s a b) (∑' c, J.Pmin t a c * J.Q c b) t := by
  have hback := J.hasDerivAt_Pmin t ht a b
  have hrow : Summable fun c => J.Pmin t a c :=
    summable_of_sum_le (c := 1) (fun c => J.Pmin_nonneg t ht.le a c)
      (J.sum_Pmin_le_one t ht.le a)
  -- the right difference quotient through Chapman–Kolmogorov
  have hquot : ∀ h : ℝ, 0 < h → h⁻¹ • (J.Pmin (t + h) a b - J.Pmin t a b) =
      ∑' c, J.Pmin t a c * ((J.Pmin h c b - (if c = b then 1 else 0)) / h) := by
    intro h hh
    have hs1 : Summable fun c => J.Pmin t a c * J.Pmin h c b :=
      Summable.of_nonneg_of_le (fun c => mul_nonneg (J.Pmin_nonneg t ht.le a c)
        (J.Pmin_nonneg h hh.le c b))
        (fun c => mul_le_of_le_one_right (J.Pmin_nonneg t ht.le a c) (J.Pmin_le_one h hh.le c b))
        hrow
    have hs2 : Summable fun c => J.Pmin t a c * (if c = b then 1 else 0) :=
      summable_of_ne_finset_zero (s := {b}) fun c hc => by
        rw [Finset.mem_singleton] at hc; rw [if_neg hc, mul_zero]
    have hδ : ∑' c, J.Pmin t a c * (if c = b then 1 else 0) = J.Pmin t a b := by
      rw [tsum_eq_single b fun c hc => by rw [if_neg hc, mul_zero]]; simp
    rw [J.Pmin_add ht.le hh.le a b, ← hδ, ← hs1.tsum_sub hs2, smul_eq_mul, ← tsum_mul_left]
    exact tsum_congr fun c => by ring
  -- its limit by Tannery's theorem
  have hlim : Tendsto (fun h => ∑' c, J.Pmin t a c * ((J.Pmin h c b - (if c = b then 1 else 0)) / h))
      (𝓝[>] 0) (𝓝 (∑' c, J.Pmin t a c * J.Q c b)) := by
    refine tendsto_tsum_of_dominated_convergence hsum (fun c =>
      (J.tendsto_slope_Pmin_zero c b).const_mul _) ?_
    filter_upwards [self_mem_nhdsWithin] with h hh c
    have hh0 : 0 < h := hh
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (J.Pmin_nonneg t ht.le a c), abs_div,
      abs_of_pos hh0]
    refine mul_le_mul_of_nonneg_left ?_ (J.Pmin_nonneg t ht.le a c)
    rw [div_le_iff₀ hh0]
    exact J.abs_Pmin_sub_le c b hh0.le
  -- the same quotient tends to the backward derivative
  have hslope := hback.tendsto_slope_zero
  have hright : Tendsto (fun h => h⁻¹ • (J.Pmin (t + h) a b - J.Pmin t a b)) (𝓝[>] 0)
      (𝓝 (-J.q a * J.Pmin t a b + ∑ i, J.rate i a * J.Pmin t (J.next i a) b)) :=
    hslope.mono_left (nhdsWithin_mono _ fun x hx => ne_of_gt hx)
  have heq : -J.q a * J.Pmin t a b + ∑ i, J.rate i a * J.Pmin t (J.next i a) b =
      ∑' c, J.Pmin t a c * J.Q c b := by
    refine tendsto_nhds_unique hright (hlim.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact (hquot h hh).symm
  rwa [heq] at hback

end JumpSystem

end CRNT
