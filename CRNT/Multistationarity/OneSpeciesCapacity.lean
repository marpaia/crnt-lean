import CRNT.Equilibria.OneSpeciesDescartes
import CRNT.Stoich.Subspace
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Polynomial

/-!
# Multistationarity of one-species networks from an arrow pattern

For a one-species network, draw an arrow at each reactant coefficient: up if the reaction
increases the species, down if it decreases it. Joshi and Shiu (*Which small reaction networks
are multistationary?*, SIAM J. Appl. Dyn. Syst. 16 (2017), Theorem 3.6) show that a pattern
`up, down, up` at three reactant coefficients `m₁ < m₂ < m₃` gives the capacity for multiple
positive steady states. Here we prove that sufficiency direction: rate constants exist for which
the network has two distinct positive steady states (necessarily in the same compatibility
class, since one species with a nonzero reaction vector spans the whole line).

The construction gives rate `1` to the two up reactions, a large rate `β` to the down reaction,
and a small rate `ε` to every other reaction; the intermediate value theorem then produces two
positive roots of the steady-state polynomial on either side of `1`.

Main result: `CRNT.Network.oneSpecies_multistationary_of_upDownUp`.
-/

namespace CRNT

namespace Network

open Polynomial
open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S] [Unique S]

/-- Evaluation of the one-species polynomial. -/
theorem oneSpeciesPoly_eval_eq (N : Network S) (κ : RateConstants N) (t : ℝ) :
    (N.oneSpeciesPoly κ).eval t =
      ∑ r, κ.k r * N.reactionVector r default * t ^ (N.reaction r).source default := by
  simp [oneSpeciesPoly, eval_finsetSum]

/-- One species with a nonzero reaction vector spans the whole line. -/
theorem stoichSubspace_eq_top_of_one_species (N : Network S) {r : N.R}
    (hr : N.reactionVector r default ≠ 0) : N.stoichSubspace = ⊤ := by
  rw [eq_top_iff]
  intro w _
  have hw : w = (w default / N.reactionVector r default) • N.reactionVector r := by
    funext s
    rw [Unique.eq_default s, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hr]
  rw [hw]
  exact Submodule.smul_mem _ _ (N.reactionVector_mem_stoichSubspace r)

set_option maxHeartbeats 1000000 in
/-- Signed form of the arrow-pattern construction: `σ = 1` is up–down–up, `σ = -1`
is down–up–down. -/
theorem oneSpecies_multistationary_of_signed (N : Network S) (σ : ℝ) (hσ : σ ≠ 0) (r₁ r₂ r₃ : N.R)
    (h12 : (N.reaction r₁).source default < (N.reaction r₂).source default)
    (h23 : (N.reaction r₂).source default < (N.reaction r₃).source default)
    (hu₁ : 0 < σ * N.reactionVector r₁ default) (hd₂ : σ * N.reactionVector r₂ default < 0)
    (hu₃ : 0 < σ * N.reactionVector r₃ default) :
    ∃ (κ : RateConstants N) (x z : Concentration S), N.oneSpeciesPoly κ ≠ 0 ∧
      x.Positive ∧ z.Positive ∧ x ≠ z ∧
      x - z ∈ N.stoichSubspace ∧ N.IsMassActionSteadyState κ x ∧
        N.IsMassActionSteadyState κ z := by
  classical
  have h12' : r₁ ≠ r₂ := fun h => by rw [h] at h12; exact lt_irrefl _ h12
  have h23' : r₂ ≠ r₃ := fun h => by rw [h] at h23; exact lt_irrefl _ h23
  have h13' : r₁ ≠ r₃ := fun h => by rw [h] at h12; exact lt_irrefl _ (h12.trans h23)
  set m₁ := (N.reaction r₁).source default
  set m₂ := (N.reaction r₂).source default
  set m₃ := (N.reaction r₃).source default
  set c₁ := σ * N.reactionVector r₁ default
  set c₂ := σ * N.reactionVector r₂ default
  set c₃ := σ * N.reactionVector r₃ default
  -- the three-term main part
  set β : ℝ := (c₁ + c₃ + 2) / (-c₂)
  have hβ : 0 < β := div_pos (by linarith) (by linarith)
  have hnc2 : 0 < -c₂ := by linarith
  have hβc₂ : β * c₂ = -(c₁ + c₃ + 2) := by
    simp only [β]; rw [div_mul_eq_mul_div, div_eq_iff hnc2.ne']; ring
  have hden : 0 < 2 * β * (-c₂) := mul_pos (mul_pos two_pos hβ) hnc2
  let f : ℝ → ℝ := fun t => c₁ * t ^ m₁ + β * c₂ * t ^ m₂ + c₃ * t ^ m₃
  -- the rest
  let q : ℝ → ℝ := fun t => ∑ r ∈ Finset.univ.filter (fun r => r ≠ r₁ ∧ r ≠ r₂ ∧ r ≠ r₃),
    σ * N.reactionVector r default * t ^ (N.reaction r).source default
  -- three test points
  set t₀ : ℝ := min (1 / 2) (c₁ / (2 * β * (-c₂)))
  have ht₀ : 0 < t₀ := lt_min (by norm_num) (div_pos hu₁ hden)
  have ht₀1 : t₀ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  set T : ℝ := max 2 ((β * (-c₂) + 1) / c₃)
  have hT1 : 1 < T := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hfmid : f 1 = -2 := by simp only [f, one_pow, mul_one]; linarith [hβc₂]
  have hflow : 0 < f t₀ := by
    have hpow : t₀ ^ m₂ ≤ t₀ ^ m₁ * t₀ := by
      rw [← pow_succ]; exact pow_le_pow_of_le_one ht₀.le ht₀1.le h12
    have hle : β * (-c₂) * t₀ ≤ c₁ / 2 := by
      have := min_le_right (1 / 2) (c₁ / (2 * β * (-c₂)))
      rw [le_div_iff₀ hden] at this
      nlinarith
    have hm1 : 0 < t₀ ^ m₁ := pow_pos ht₀ _
    have hc3 : 0 ≤ c₃ * t₀ ^ m₃ := mul_nonneg hu₃.le (pow_nonneg ht₀.le _)
    have : β * c₂ * t₀ ^ m₂ ≥ -(c₁ / 2) * t₀ ^ m₁ := by
      have h1 : β * (-c₂) * t₀ ^ m₂ ≤ β * (-c₂) * (t₀ ^ m₁ * t₀) :=
        mul_le_mul_of_nonneg_left hpow (mul_pos hβ hnc2).le
      nlinarith
    simp only [f]; nlinarith
  have hfhigh : 0 < f T := by
    have hpow : T ^ m₂ * T ≤ T ^ m₃ := by
      rw [← pow_succ]; exact pow_le_pow_right₀ hT1.le h23
    have hcT : β * (-c₂) + 1 ≤ c₃ * T := by
      have := le_max_right 2 ((β * (-c₂) + 1) / c₃)
      rw [div_le_iff₀ hu₃] at this; linarith
    have hm1 : 0 ≤ c₁ * T ^ m₁ := mul_nonneg hu₁.le (pow_nonneg (by linarith) _)
    have hm2 : 0 < T ^ m₂ := pow_pos (by linarith) _
    have : c₃ * (T ^ m₂ * T) ≤ c₃ * T ^ m₃ := mul_le_mul_of_nonneg_left hpow hu₃.le
    simp only [f]; nlinarith
  -- choose `ε`
  set Mq : ℝ := |q t₀| + |q 1| + |q T| + 1
  have hMq : 0 < Mq := by positivity
  set ε : ℝ := min (min (f t₀) 1) (f T) / (2 * Mq)
  have hε : 0 < ε := div_pos (lt_min (lt_min hflow one_pos) hfhigh) (by positivity)
  have hεq : ∀ t, |q t| ≤ Mq - 1 → ε * |q t| ≤ min (min (f t₀) 1) (f T) / 2 := by
    intro t ht
    simp only [ε]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    have hm : 0 < min (min (f t₀) 1) (f T) := lt_min (lt_min hflow one_pos) hfhigh
    nlinarith [abs_nonneg (q t)]
  -- the rate constants
  let κ : RateConstants N := ⟨fun r => if r = r₁ then 1 else if r = r₂ then β else
    if r = r₃ then 1 else ε, fun r => by split_ifs <;> positivity⟩
  have hpoly : ∀ t, σ * (N.oneSpeciesPoly κ).eval t = f t + ε * q t := by
    intro t
    rw [oneSpeciesPoly_eval_eq, Finset.mul_sum]
    simp only [f, q, Finset.mul_sum]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun r => r ≠ r₁ ∧ r ≠ r₂ ∧ r ≠ r₃)]
    have hrest : ∑ r ∈ Finset.univ.filter (fun r => r ≠ r₁ ∧ r ≠ r₂ ∧ r ≠ r₃),
        σ * (κ.k r * N.reactionVector r default * t ^ (N.reaction r).source default) =
        ∑ r ∈ Finset.univ.filter (fun r => r ≠ r₁ ∧ r ≠ r₂ ∧ r ≠ r₃),
          ε * (σ * N.reactionVector r default * t ^ (N.reaction r).source default) := by
      refine Finset.sum_congr rfl fun r hr => ?_
      obtain ⟨n1, n2, n3⟩ := (Finset.mem_filter.mp hr).2
      simp only [κ, n1, n2, n3, ite_false]; ring
    have hthree : Finset.univ.filter (fun r => ¬ (r ≠ r₁ ∧ r ≠ r₂ ∧ r ≠ r₃)) = {r₁, r₂, r₃} := by
      ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]; tauto
    rw [hrest, hthree, Finset.sum_insert (by simp [h12', h13']),
      Finset.sum_insert (by simp [h23']), Finset.sum_singleton]
    simp only [κ, ite_true, h12'.symm, h13'.symm, h23'.symm, ite_false]
    simp only [c₁, c₂, c₃, m₁, m₂, m₃]
    ring
  have hcont : Continuous fun t => σ * (N.oneSpeciesPoly κ).eval t :=
    continuous_const.mul (N.oneSpeciesPoly κ).continuous
  have hpt₀ : 0 < σ * (N.oneSpeciesPoly κ).eval t₀ := by
    rw [hpoly]
    have := hεq t₀ (by simp only [Mq]; linarith [abs_nonneg (q 1), abs_nonneg (q T)])
    have h1 := neg_abs_le (q t₀)
    have : ε * (-|q t₀|) ≤ ε * q t₀ := mul_le_mul_of_nonneg_left h1 hε.le
    have hmin : min (min (f t₀) 1) (f T) ≤ f t₀ := (min_le_left _ _).trans (min_le_left _ _)
    nlinarith
  have hp1 : σ * (N.oneSpeciesPoly κ).eval 1 < 0 := by
    rw [hpoly, hfmid]
    have := hεq 1 (by simp only [Mq]; linarith [abs_nonneg (q t₀), abs_nonneg (q T)])
    have h1 := le_abs_self (q 1)
    have : ε * q 1 ≤ ε * |q 1| := mul_le_mul_of_nonneg_left h1 hε.le
    have hmin : min (min (f t₀) 1) (f T) ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
    linarith
  have hpT : 0 < σ * (N.oneSpeciesPoly κ).eval T := by
    rw [hpoly]
    have := hεq T (by simp only [Mq]; linarith [abs_nonneg (q 1), abs_nonneg (q t₀)])
    have h1 := neg_abs_le (q T)
    have : ε * (-|q T|) ≤ ε * q T := mul_le_mul_of_nonneg_left h1 hε.le
    have hmin : min (min (f t₀) 1) (f T) ≤ f T := min_le_right _ _
    nlinarith
  -- two roots by the intermediate value theorem
  obtain ⟨ρ₁, hρ₁, hρ₁0⟩ := intermediate_value_Icc' ht₀1.le hcont.continuousOn
    ⟨hp1.le, hpt₀.le⟩
  obtain ⟨ρ₂, hρ₂, hρ₂0⟩ := intermediate_value_Icc hT1.le hcont.continuousOn
    ⟨hp1.le, hpT.le⟩
  have hρ₁1 : ρ₁ < 1 := lt_of_le_of_ne hρ₁.2 (fun h => by rw [h] at hρ₁0; linarith)
  have hρ₂1 : 1 < ρ₂ := lt_of_le_of_ne hρ₂.1 (fun h => by rw [← h] at hρ₂0; linarith)
  have hρ₁pos : 0 < ρ₁ := lt_of_lt_of_le ht₀ hρ₁.1
  refine ⟨κ, oneSpeciesConc ρ₁, oneSpeciesConc ρ₂, fun h0 => ?_, fun _ => hρ₁pos,
    fun _ => show 0 < ρ₂ by linarith, fun h => ?_, ?_, ?_, ?_⟩
  · rw [h0, eval_zero, mul_zero] at hp1; exact lt_irrefl _ hp1
  · have := congrFun h default
    simp only [oneSpeciesConc] at this
    linarith
  · have hv : N.reactionVector r₁ default ≠ 0 := fun h => by
      simp only [c₁, h, mul_zero] at hu₁; exact lt_irrefl _ hu₁
    rw [stoichSubspace_eq_top_of_one_species N hv]; exact Submodule.mem_top
  · exact (N.oneSpecies_steadyState_iff_isRoot κ ρ₁).mpr
      ((mul_eq_zero.mp hρ₁0).resolve_left hσ)
  · exact (N.oneSpecies_steadyState_iff_isRoot κ ρ₂).mpr
      ((mul_eq_zero.mp hρ₂0).resolve_left hσ)


/-- **One-species multistationarity from an up–down–up pattern** (Joshi–Shiu 2017). If
reactions `r₁, r₂, r₃` have reactant coefficients `m₁ < m₂ < m₃` and respectively increase,
decrease and increase the species, then for suitable rate constants the network has two distinct
positive steady states in one compatibility class. -/
theorem oneSpecies_multistationary_of_upDownUp (N : Network S) (r₁ r₂ r₃ : N.R)
    (h12 : (N.reaction r₁).source default < (N.reaction r₂).source default)
    (h23 : (N.reaction r₂).source default < (N.reaction r₃).source default)
    (hu₁ : 0 < N.reactionVector r₁ default) (hd₂ : N.reactionVector r₂ default < 0)
    (hu₃ : 0 < N.reactionVector r₃ default) :
    ∃ (κ : RateConstants N) (x z : Concentration S), x.Positive ∧ z.Positive ∧ x ≠ z ∧
      x - z ∈ N.stoichSubspace ∧ N.IsMassActionSteadyState κ x ∧
        N.IsMassActionSteadyState κ z :=
  let ⟨κ, x, z, _, h⟩ := N.oneSpecies_multistationary_of_signed 1 one_ne_zero r₁ r₂ r₃ h12 h23
    (by linarith) (by linarith) (by linarith)
  ⟨κ, x, z, h⟩

/-- **One-species multistationarity from a down–up–down pattern.** -/
theorem oneSpecies_multistationary_of_downUpDown (N : Network S) (r₁ r₂ r₃ : N.R)
    (h12 : (N.reaction r₁).source default < (N.reaction r₂).source default)
    (h23 : (N.reaction r₂).source default < (N.reaction r₃).source default)
    (hd₁ : N.reactionVector r₁ default < 0) (hu₂ : 0 < N.reactionVector r₂ default)
    (hd₃ : N.reactionVector r₃ default < 0) :
    ∃ (κ : RateConstants N) (x z : Concentration S), x.Positive ∧ z.Positive ∧ x ≠ z ∧
      x - z ∈ N.stoichSubspace ∧ N.IsMassActionSteadyState κ x ∧
        N.IsMassActionSteadyState κ z :=
  let ⟨κ, x, z, _, h⟩ := N.oneSpecies_multistationary_of_signed (-1) (by norm_num) r₁ r₂ r₃ h12 h23
    (by linarith) (by linarith) (by linarith)
  ⟨κ, x, z, h⟩

end Network

end CRNT
