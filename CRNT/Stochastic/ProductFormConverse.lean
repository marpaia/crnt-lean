import CRNT.Stochastic.CTMC
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Converse to the Anderson--Craciun--Kurtz product-form theorem

For a strictly positive parameter `c`, the shifted product-Poisson functions

  n ↦ π_c(n-y),   y a complex,

are linearly independent.  After the standard ACK substitution, the stationary
master equation is therefore a linear combination of these functions whose
coefficient at complex `y` is exactly `inflow(y)-outflow(y)`.  Consequently the
*unconditioned* product-Poisson density is stationary iff `c` is complex balanced.

The linear-independence proof is the multivariate falling-factorial basis theorem:
a shifted Poisson density is the common positive density `π_c(n)` times a
falling-factorial monomial divided by `c^y`.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Falling-factorial monomial indexed by a complex. -/
def fallingMonomial (y : Complex S) (n : S → ℕ) : ℕ :=
  ∏ s : S, (n s).descFactorial (y s)

/-- On counts dominating `y`, shifted product-Poisson density differs from the
unshifted density by exactly the falling-factorial monomial divided by `c^y`. -/
theorem shiftedPMF_eq_productPoisson_mul_fallingMonomial
    (N : Network S) {c : Concentration S} (hc : c.Positive)
    (n : S → ℕ) (y : Complex S) :
    shiftedPMF c n y =
      productPoissonPMF c n *
        ((fallingMonomial y n : ℝ) /
          ∏ s : S, (c s) ^ (y s)) := by
  by_cases hdom : ∀ s, y s ≤ n s
  · rw [shiftedPMF, if_pos hdom]
    have hprod : productPoissonPMF c n * (fallingMonomial y n : ℝ) =
        (∏ s : S, (c s) ^ (y s)) *
          productPoissonPMF c (fun s => n s - y s) := by
      unfold productPoissonPMF fallingMonomial
      rw [Nat.cast_prod]
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro s _
      exact poissonFactor_mul_descFactorial (c s) (hdom s)
    have hden : (∏ s : S, (c s) ^ (y s)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro s _
      exact pow_ne_zero _ (hc s).ne'
    rw [mul_div]
    apply (eq_div_iff hden).2
    calc
      productPoissonPMF c (fun s => n s - y s) * ∏ s : S, c s ^ y s
          = (∏ s : S, c s ^ y s) *
              productPoissonPMF c (fun s => n s - y s) := by ring
      _ = productPoissonPMF c n * (fallingMonomial y n : ℝ) := hprod.symm
  · rw [shiftedPMF, if_neg hdom]
    have hex : ∃ s, n s < y s := by
      push_neg at hdom
      exact hdom
    obtain ⟨s, hs⟩ := hex
    have hfall : fallingMonomial y n = 0 := by
      unfold fallingMonomial
      apply Finset.prod_eq_zero (Finset.mem_univ s)
      exact Nat.descFactorial_eq_zero_iff_lt.mpr hs
    simp [hfall]

/-- Multivariate falling-factorial monomials indexed by distinct natural exponent
vectors are linearly independent as functions on `ℕ^S`. -/
theorem fallingMonomials_linearIndependent :
    LinearIndependent ℝ
      (fun y : Complex S => fun n : S → ℕ => (fallingMonomial y n : ℝ)) := by
  rw [linearIndependent_iff']
  intro A g hsum i hi
  by_contra hgi
  let T : Finset (Complex S) := A.filter (fun z => g z ≠ 0)
  have hiT : i ∈ T := by simp [T, hi, hgi]
  have hTne : T.Nonempty := ⟨i, hiT⟩
  let deg : Complex S → ℕ := fun z => ∑ s : S, z s
  obtain ⟨y, hyT, hymin⟩ := T.exists_min_image deg hTne
  have hyA : y ∈ A := (Finset.mem_filter.mp hyT).1
  have hgy : g y ≠ 0 := (Finset.mem_filter.mp hyT).2
  have htermzero : ∀ z ∈ A, z ≠ y →
      g z * (fallingMonomial z y : ℝ) = 0 := by
    intro z hzA hzy
    by_cases hgz : g z = 0
    · simp [hgz]
    have hzT : z ∈ T := by simp [T, hzA, hgz]
    have hfall0 : fallingMonomial z y = 0 := by
      by_contra hfall
      have hle : ∀ s : S, z s ≤ y s := by
        intro s
        by_contra hnle
        have hlt : y s < z s := Nat.lt_of_not_ge hnle
        have hfactor : (y s).descFactorial (z s) = 0 :=
          Nat.descFactorial_eq_zero_iff_lt.mpr hlt
        apply hfall
        unfold fallingMonomial
        exact Finset.prod_eq_zero (Finset.mem_univ s) hfactor
      have hdeg_le : deg z ≤ deg y := by
        dsimp [deg]
        exact Finset.sum_le_sum (fun s _ => hle s)
      have hdeg_ge : deg y ≤ deg z := hymin z hzT
      have hdeg_eq : deg z = deg y := Nat.le_antisymm hdeg_le hdeg_ge
      have hzeq : z = y := by
        funext s
        apply Nat.le_antisymm (hle s)
        by_contra hnot
        have hlt : z s < y s := Nat.lt_of_not_ge hnot
        have hsumlt : (∑ q : S, z q) < ∑ q : S, y q := by
          apply Finset.sum_lt_sum
          · intro q _; exact hle q
          · exact ⟨s, Finset.mem_univ s, hlt⟩
        exact (Nat.ne_of_lt hsumlt) (by simpa [deg] using hdeg_eq)
      exact hzy hzeq
    simp [hfall0]
  have heval := congrFun hsum y
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at heval
  have hsingle : (∑ z ∈ A, g z * (fallingMonomial z y : ℝ)) =
      g y * (fallingMonomial y y : ℝ) :=
    Finset.sum_eq_single y htermzero (by intro hy; exact (hy hyA).elim)
  rw [hsingle] at heval
  have hself : fallingMonomial y y ≠ 0 := by
    unfold fallingMonomial
    rw [Finset.prod_ne_zero_iff]
    intro s _
    rw [Nat.descFactorial_self]
    exact Nat.factorial_ne_zero _
  exact hgy (mul_eq_zero.mp heval |>.resolve_right (mod_cast hself))

/-- Shifted product-Poisson functions are linearly independent at positive `c`. -/
theorem shiftedPMF_linearIndependent (N : Network S)
    {c : Concentration S} (hc : c.Positive) :
    LinearIndependent ℝ
      (fun y : Complex S => fun n : S → ℕ => shiftedPMF c n y) := by
  rw [linearIndependent_iff']
  intro A g hsum y hyA
  let D : Complex S → ℝ := fun z => ∏ s : S, (c s) ^ (z s)
  let g' : Complex S → ℝ := fun z => g z / D z
  have hpmf_ne : ∀ n : S → ℕ, productPoissonPMF c n ≠ 0 := by
    intro n
    unfold productPoissonPMF
    apply Finset.prod_ne_zero_iff.mpr
    intro s _
    have hcs : 0 < c s := hc s
    positivity
  have hsumfall : ∑ z ∈ A, g' z •
      (fun n : S → ℕ => (fallingMonomial z n : ℝ)) = 0 := by
    funext n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have hn := congrFun hsum n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hn
    simp_rw [N.shiftedPMF_eq_productPoisson_mul_fallingMonomial hc] at hn
    apply (mul_left_cancel₀ (hpmf_ne n))
    rw [mul_zero]
    calc
      productPoissonPMF c n *
          (∑ z ∈ A, g' z * (fallingMonomial z n : ℝ)) =
        ∑ z ∈ A, g z *
          (productPoissonPMF c n *
            ((fallingMonomial z n : ℝ) / D z)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro z _
              dsimp [g', D]
              ring
      _ = 0 := by
        simpa [D] using hn
  have hcoeff :=
    (linearIndependent_iff'.mp (fallingMonomials_linearIndependent (S := S)))
      A g' hsumfall y hyA
  have hDne : D y ≠ 0 := by
    dsimp [D]
    apply Finset.prod_ne_zero_iff.mpr
    intro s _
    exact pow_ne_zero _ (hc s).ne'
  dsimp [g'] at hcoeff
  exact (div_eq_zero_iff.mp hcoeff).resolve_right hDne

/-- ACK residual regrouped explicitly by complexes. -/
theorem ackResidual_eq_sum_complex_imbalance (N : Network S)
    (κ : N.RateConstants) (c : Concentration S) (n : S → ℕ) :
    N.ackResidual κ c n =
      ∑ y ∈ N.complexes,
        shiftedPMF c n y * (N.inflow κ c y - N.outflow κ c y) := by
  unfold ackResidual generatorFlux
  -- `Finset.sum_mul_sub` does not exist; distribute the product over the difference
  -- `simp` already discharges the goal once the product is distributed
  simp only [mul_sub, Finset.sum_sub_distrib,
    N.sum_target_flux_eq_inflow κ c n, N.sum_source_flux_eq_outflow κ c n]

/-- If the product-Poisson law is master-stationary at a positive parameter, then
that parameter is a deterministic complex-balanced equilibrium. -/
theorem complexBalanced_of_productPoisson_masterStationary
    (N : Network S) (κ : N.RateConstants)
    {c : Concentration S} (hc : c.Positive)
    (hstat : N.IsMasterStationary κ c) :
    N.IsComplexBalanced κ c := by
  have hfun :
      (fun n : S → ℕ =>
        ∑ y ∈ N.complexes,
          shiftedPMF c n y * (N.inflow κ c y - N.outflow κ c y)) = 0 := by
    funext n
    rw [← N.ackResidual_eq_sum_complex_imbalance κ c n, hstat n]
    rfl
  -- Linear independence of all shifted Poisson functions forces every complex
  -- coefficient to vanish.
  have hli := N.shiftedPMF_linearIndependent hc
  have hcoeff : ∀ y ∈ N.complexes,
      N.inflow κ c y - N.outflow κ c y = 0 := by
    let g : Complex S → ℝ := fun y => N.inflow κ c y - N.outflow κ c y
    have hsum : ∑ y ∈ N.complexes,
        g y • (fun n : S → ℕ => shiftedPMF c n y) = 0 := by
      funext n
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      have hn := congrFun hfun n
      simpa [g, mul_comm] using hn
    exact (linearIndependent_iff'.mp hli) N.complexes g hsum
  intro y hy
  linarith [hcoeff y hy]

/-- **ACK product-form iff theorem.** At a strictly positive concentration, the full
product-Poisson density is stationary exactly at deterministic complex-balanced states. -/
theorem productPoisson_masterStationary_iff_complexBalanced
    (N : Network S) (κ : N.RateConstants)
    {c : Concentration S} (hc : c.Positive) :
    N.IsMasterStationary κ c ↔ N.IsComplexBalanced κ c :=
  ⟨N.complexBalanced_of_productPoisson_masterStationary κ hc,
    N.productPoisson_isStationary_of_complexBalanced κ c⟩

/-- Generator-level version of the ACK iff theorem. -/
theorem productPoisson_generatorStationary_iff_complexBalanced
    (N : Network S) (κ : N.RateConstants)
    {c : Concentration S} (hc : c.Positive) :
    N.IsGeneratorStationary κ c ↔ N.IsComplexBalanced κ c := by
  rw [N.isGeneratorStationary_iff_isMasterStationary]
  exact N.productPoisson_masterStationary_iff_complexBalanced κ hc

end Network
end CRNT
