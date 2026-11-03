import CRNT.Stochastic.ForwardCME
import CRNT.Stochastic.ProductFormInvariance

/-!
# Poisson laws of monomolecular networks (Jahnke–Huisinga 2007)

For a monomolecular network (every source and every target complex has at most one molecule),
if the mean `μ(t) > 0` solves the deterministic mass-action equation `μ' = f(μ)`, the product-
Poisson law `π_{μ(t)}` solves the forward master equation (`hasDerivAt_productPoisson_cme`), so by
`tsum_mul_transition_of_forwardCME` the chain started from `π_{μ(0)}` has law `π_{μ(T)}` at time
`T` (`jahnke_huisinga`).

Computation: `inflow_r(n) − π(n) λ_r(n) = rate_r(μ) (π^{shift}(n, y'_r) − π^{shift}(n, y_r))`, and for a
complex with at most one molecule `π^{shift}(n, y) = π(n) (1 + ∑_s y_s (n_s/μ_s − 1))`
(`shiftedPMF_of_molecularity`); hence the right-hand side is `π(n) ∑_s (n_s/μ_s − 1) f_s(μ)`, the
derivative of `π_{μ(t)}(n)`.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Every source and target complex has at most one molecule. -/
def IsMonomolecular (N : Network S) : Prop :=
  ∀ r, ∑ s, (N.reaction r).source s ≤ 1 ∧ ∑ s, (N.reaction r).target s ≤ 1

/-- Complexes with at most one molecule are `0` or a unit vector. -/
theorem complex_of_sum_le_one {y : S → ℕ} (hy : ∑ s, y s ≤ 1) :
    (∀ s, y s = 0) ∨ ∃ j, y j = 1 ∧ ∀ s, s ≠ j → y s = 0 := by
  by_cases hz : ∀ s, y s = 0
  · exact Or.inl hz
  · obtain ⟨j, hj⟩ := not_forall.mp hz
    have hle : ∀ s, s ≠ j → y s = 0 := by
      intro s hs
      by_contra h
      have h2 : y j + y s ≤ ∑ s, y s := by
        rw [← Finset.sum_pair (Ne.symm hs)]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ =>
          Nat.zero_le _
      omega
    have h1 : y j ≤ ∑ s, y s := Finset.single_le_sum (f := y) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
    exact Or.inr ⟨j, by omega, hle⟩

/-- `π(n − e_j) = π(n) n_j / c_j` for `n_j ≥ 1`. -/
theorem productPoissonPMF_sub_unit {c : Concentration S} {j : S} (hcj : 0 < c j) {n : S → ℕ}
    (hn : 1 ≤ n j) {y : S → ℕ} (hyj : y j = 1) (hy : ∀ s, s ≠ j → y s = 0) :
    productPoissonPMF c (fun s => n s - y s) = productPoissonPMF c n * n j / c j := by
  unfold productPoissonPMF
  rw [Fintype.prod_eq_mul_prod_compl j, Fintype.prod_eq_mul_prod_compl j (f := fun s =>
    Real.exp (-(c s)) * c s ^ n s / (n s).factorial)]
  have hrest : ∏ s ∈ ({j} : Finset S)ᶜ, Real.exp (-(c s)) * c s ^ (n s - y s) / (n s - y s).factorial
      = ∏ s ∈ ({j} : Finset S)ᶜ, Real.exp (-(c s)) * c s ^ n s / (n s).factorial :=
    Finset.prod_congr rfl fun s hs => by
      rw [hy s (by simpa using hs), Nat.sub_zero]
  rw [hrest]
  simp only [hyj]
  obtain ⟨k, hk⟩ : ∃ k, n j = k + 1 := ⟨n j - 1, by omega⟩
  rw [hk, Nat.add_sub_cancel, Nat.factorial_succ, pow_succ]
  push_cast
  field_simp

/-- Shifted product-Poisson densities at complexes with at most one molecule. -/
theorem shiftedPMF_of_molecularity {c : Concentration S} (hc : c.Positive) (n : S → ℕ)
    {y : S → ℕ} (hy : ∑ s, y s ≤ 1) :
    shiftedPMF c n y = productPoissonPMF c n * (1 + ∑ s, (y s : ℝ) * ((n s : ℝ) / c s - 1)) := by
  rcases complex_of_sum_le_one hy with hz | ⟨j, hyj, hyo⟩
  · unfold shiftedPMF
    rw [if_pos fun s => by rw [hz s]; exact Nat.zero_le _]
    simp [hz]
  · have hsum : ∑ s, (y s : ℝ) * ((n s : ℝ) / c s - 1) = (n j : ℝ) / c j - 1 := by
      rw [Finset.sum_eq_single j (fun s _ hs => by rw [hyo s hs]; simp) (by simp), hyj]
      simp
    rw [hsum, add_sub_cancel]
    unfold shiftedPMF
    by_cases hn : 1 ≤ n j
    · rw [if_pos fun s => by
        by_cases hs : s = j
        · subst hs; omega
        · rw [hyo s hs]; exact Nat.zero_le _]
      rw [productPoissonPMF_sub_unit (hc j) hn hyj hyo]
      ring
    · rw [if_neg fun h => by have := h j; omega]
      have : n j = 0 := by omega
      simp [this]

/-- The forward master equation applied to a product-Poisson law of a monomolecular network. -/
theorem cmeRHS_productPoisson (N : Network S) (κ : RateConstants N) (hmono : N.IsMonomolecular)
    {c : Concentration S} (hc : c.Positive) (n : S → ℕ) :
    N.cmeRHS κ (productPoissonPMF c) n =
      productPoissonPMF c n * ∑ s, ((n s : ℝ) / c s - 1) * N.massActionVectorField κ c s := by
  have h1 : N.cmeRHS κ (productPoissonPMF c) n = ∑ r, N.massActionRate κ r c *
      (shiftedPMF c n (N.reaction r).target - shiftedPMF c n (N.reaction r).source) := by
    unfold cmeRHS exitRate
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [cmeInflow_productPoisson, productPoissonPMF_mul_rate]; ring
  have h2 : ∀ r, N.massActionRate κ r c *
      (shiftedPMF c n (N.reaction r).target - shiftedPMF c n (N.reaction r).source) =
      productPoissonPMF c n * ∑ s, ((n s : ℝ) / c s - 1) *
        (N.massActionRate κ r c * N.reactionVector r s) := by
    intro r
    rw [shiftedPMF_of_molecularity hc n (hmono r).2, shiftedPMF_of_molecularity hc n (hmono r).1]
    have hA : ∑ s, ((n s : ℝ) / c s - 1) * (N.massActionRate κ r c * N.reactionVector r s) =
        N.massActionRate κ r c * (∑ s, (((N.reaction r).target s : ℕ) : ℝ) * ((n s : ℝ) / c s - 1) -
          ∑ s, (((N.reaction r).source s : ℕ) : ℝ) * ((n s : ℝ) / c s - 1)) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by rw [reactionVector_apply]; ring
    rw [hA]; ring
  rw [h1, Finset.sum_congr rfl fun r _ => h2 r, ← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [massActionVectorField_apply, Finset.mul_sum]

omit [DecidableEq S] [Fintype S] in
/-- Derivative of a Poisson factor along a positive differentiable mean. -/
theorem hasDerivAt_poissonFactor {g : ℝ → ℝ} {g' t : ℝ} (hg : HasDerivAt g g' t)
    (hpos : 0 < g t) (k : ℕ) :
    HasDerivAt (fun t => Real.exp (-(g t)) * g t ^ k / k.factorial)
      (Real.exp (-(g t)) * g t ^ k / k.factorial * (((k : ℝ) / g t - 1) * g')) t := by
  have h := ((hg.neg.exp).mul (hg.pow k)).div_const (k.factorial : ℝ)
  convert h using 1
  have hne : g t ≠ 0 := hpos.ne'
  rcases k with _ | k
  · simp
  · simp only [Nat.add_sub_cancel, pow_succ, Nat.factorial_succ, Pi.neg_apply, Pi.pow_apply,
      Pi.mul_apply]
    push_cast
    field_simp
    ring

/-- Derivative of a product-Poisson density along a positive differentiable mean. -/
theorem hasDerivAt_productPoissonPMF {μ : ℝ → Concentration S} {μ' : S → ℝ} {t : ℝ}
    (hμ : HasDerivAt μ μ' t) (hpos : (μ t).Positive) (n : S → ℕ) :
    HasDerivAt (fun t => productPoissonPMF (μ t) n)
      (productPoissonPMF (μ t) n * ∑ s, ((n s : ℝ) / μ t s - 1) * μ' s) t := by
  have hcomp : ∀ s, HasDerivAt (fun t => μ t s) (μ' s) t := fun s => (hasDerivAt_pi.mp hμ) s
  unfold productPoissonPMF
  have h := HasDerivAt.finsetProd (u := Finset.univ)
    (f := fun s t => Real.exp (-(μ t s)) * μ t s ^ (n s) / (n s).factorial)
    (fun s _ => hasDerivAt_poissonFactor (hcomp s) (hpos s) (n s))
  have h' : HasDerivAt (fun t => ∏ s, Real.exp (-(μ t s)) * μ t s ^ (n s) / (n s).factorial)
      (∑ i, (∏ j ∈ Finset.univ.erase i, Real.exp (-(μ t j)) * μ t j ^ n j / (n j).factorial) •
        (Real.exp (-(μ t i)) * μ t i ^ n i / (n i).factorial * (((n i : ℝ) / μ t i - 1) * μ' i))) t := by
    convert h using 1
    ext t
    simp [Finset.prod_apply]
  convert h' using 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  ring

/-- **Jahnke–Huisinga.** For a monomolecular network, if the mean `μ(t) > 0` solves the
mass-action equation on `[0, T]`, the chain started from the product-Poisson law with mean `μ(0)`
has the product-Poisson law with mean `μ(T)` at time `T`. -/
theorem jahnke_huisinga (N : Network S) (κ : RateConstants N) (hmono : N.IsMonomolecular)
    {T : ℝ} (hT : 0 < T) (μ : ℝ → Concentration S) (hpos : ∀ t ∈ Icc 0 T, (μ t).Positive)
    (hcont : ContinuousOn μ (Icc 0 T))
    (hode : ∀ t ∈ Ioo 0 T, HasDerivAt μ (N.massActionVectorField κ (μ t)) t) (m : S → ℕ) :
    ∑' n, productPoissonPMF (μ 0) n * N.transition κ T n m = productPoissonPMF (μ T) m := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hcont
  set Λ := max M 1 with hΛ
  have hΛ1 : 1 ≤ Λ := le_max_right _ _
  have hle : ∀ t ∈ Icc 0 T, ∀ s, μ t s ≤ Λ := fun t ht s =>
    (le_abs_self _).trans ((norm_le_pi_norm (μ t) s).trans ((hM t ht).trans (le_max_left _ _)))
  set cΛ : Concentration S := fun _ => Λ with hcΛ
  have hΛnn : cΛ.Nonnegative := fun _ => by simp only [hcΛ]; linarith
  set D : (S → ℕ) → ℝ := fun n => Real.exp (Fintype.card S * Λ) * productPoissonPMF cΛ n
    with hDdef
  have hD : ∀ t ∈ Icc 0 T, ∀ n, productPoissonPMF (μ t) n ≤ D n := by
    intro t ht n
    have hexp : Real.exp (Fintype.card S * Λ) = ∏ _s : S, Real.exp Λ := by
      rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
    simp only [hDdef, productPoissonPMF, hexp, ← Finset.prod_mul_distrib, hcΛ]
    refine Finset.prod_le_prod₀ (fun s _ => by have := hpos t ht s; positivity) fun s _ => ?_
    have h0 := hpos t ht s
    have h1 := hle t ht s
    have hfac : (0 : ℝ) < (n s).factorial := by exact_mod_cast Nat.factorial_pos _
    rw [show Real.exp Λ * (Real.exp (-Λ) * Λ ^ n s / (n s).factorial) = Λ ^ n s / (n s).factorial by
      rw [← mul_div_assoc, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]]
    rw [mul_div_assoc]
    calc Real.exp (-(μ t s)) * (μ t s ^ n s / (n s).factorial) ≤ 1 * (Λ ^ n s / (n s).factorial) :=
          mul_le_mul (Real.exp_le_one_iff.mpr (by linarith)) (div_le_div_of_nonneg_right
            (pow_le_pow_left₀ h0.le h1 _) hfac.le) (by positivity) zero_le_one
      _ = Λ ^ n s / (n s).factorial := one_mul _
  have hDs : Summable fun n => D n * (1 + N.exitRate κ n) := by
    have h1 : Summable (productPoissonPMF cΛ) := summable_of_sum_le (c := 1)
      (fun m => productPoissonPMF_nonneg hΛnn m) (sum_productPoissonPMF_le_one hΛnn)
    have h2 : Summable fun n => productPoissonPMF cΛ n * N.exitRate κ n := by
      simp only [exitRate, Finset.mul_sum]
      exact summable_sum fun r _ => N.summable_productPoisson_mul_rate κ hΛnn r
    refine ((h1.add h2).mul_left (Real.exp (Fintype.card S * Λ))).congr fun n => ?_
    simp only [hDdef]; ring
  have hcomp : ∀ s, ContinuousOn (fun t => μ t s) (Icc 0 T) := fun s =>
    (continuous_apply s).comp_continuousOn hcont
  refine N.tsum_mul_transition_of_forwardCME κ hT (fun t n => productPoissonPMF (μ t) n) D
    (fun t ht n => productPoissonPMF_nonneg (fun s => (hpos t ht s).le) n) hD hDs
    (fun n => ?_) (fun t ht n => ?_) m
  · unfold productPoissonPMF
    exact continuousOn_finsetProd _ fun s _ =>
      ((Real.continuous_exp.comp_continuousOn (hcomp s).neg).mul ((hcomp s).pow _)).div_const _
  · have h := hasDerivAt_productPoissonPMF (hode t ht) (hpos t ⟨ht.1.le, ht.2.le⟩) n
    rw [cmeRHS_productPoisson N κ hmono (hpos t ⟨ht.1.le, ht.2.le⟩) n]
    exact h

end Network

namespace Examples
namespace PoissonBirthDeath

open Network

/-- `0 → X`, `X → 0`. -/
abbrev net : Network Unit :=
  ⟨Fin 2, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨0, fun _ => 1⟩ else ⟨fun _ => 1, 0⟩⟩

def κ : RateConstants net := ⟨fun _ => 1, fun _ => one_pos⟩

theorem monomolecular : net.IsMonomolecular := by
  intro r; fin_cases r <;> simp

/-- The mean `μ(t) = 1 + e^{−t}`. -/
noncomputable def μ (t : ℝ) : Concentration Unit := fun _ => 1 + Real.exp (-t)

theorem ode (t : ℝ) : HasDerivAt μ (net.massActionVectorField κ (μ t)) t := by
  rw [hasDerivAt_pi]
  intro u
  have h : HasDerivAt (fun t : ℝ => 1 + Real.exp (-t)) (-Real.exp (-t)) t := by
    simpa using ((hasDerivAt_neg t).exp).const_add 1
  have h' : HasDerivAt (fun x => μ x u) (-Real.exp (-t)) t := h
  convert h' using 1
  show ∑ r : Fin 2, net.massActionRate κ r (μ t) * net.reactionVector r u = _
  simp [Fin.sum_univ_two, massActionRate, κ, μ, Complex.massActionMonomial,
    Network.reactionVector, Reaction.vector]

/-- **Poisson laws of the birth–death chain.** Started from Poisson(2), the chain has law
Poisson(1 + e^{−T}) at time `T`. -/
theorem poisson (T : ℝ) (hT : 0 < T) (m : Unit → ℕ) :
    ∑' n, productPoissonPMF (μ 0) n * net.transition κ T n m = productPoissonPMF (μ T) m :=
  net.jahnke_huisinga κ monomolecular hT μ (fun t _ _ => by simp [μ]; positivity)
    (continuous_pi fun _ => by simp only [μ]; fun_prop).continuousOn
    (fun t _ => ode t) m

end PoissonBirthDeath
end Examples

end CRNT
