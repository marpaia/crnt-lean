import CRNT.Persistence.CirculationPairing
import CRNT.Equilibria.ComplexBalanced
import CRNT.Kinetics.MassAction
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Complex-balanced fields push along every valid normal

Let `x*` be a positive complex-balanced state and `x` a positive state.  If a vector `a`
satisfies, for every pair of complexes `c, c'`,

`⟨a, c - c'⟩ < 0  →  δ ≤ ⟨c - c', log x⟩`,

where `δ` exceeds every `|⟨c - c', log x*⟩|`, then `⟨a, f(x)⟩ ≥ 0` for the mass-action field
`f`.  Writing each rate as `κ_r x*^{y} · exp ⟨y, log (x / x*)⟩`, the complex-balanced fluxes
`κ_r x*^{y}` form a circulation on the complexes, the height `exp ⟨c, log (x / x*)⟩` orders the
complexes, and the hypothesis says `⟨a, ·⟩` is nonincreasing in that height; the pairing
inequality `circulation_pairing_nonneg` finishes the proof.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Network

open Finset Real

variable {S : Type} [DecidableEq S] [Fintype S]

theorem massActionMonomial_eq_exp {x : Concentration S} (hx : x.Positive) (c : Complex S) :
    c.massActionMonomial x = exp (∑ s, (c s : ℝ) * log (x s)) := by
  unfold Complex.massActionMonomial
  rw [exp_sum]
  refine prod_congr rfl fun s _ => ?_
  rw [← exp_log (hx s), ← exp_nat_mul, exp_log (hx s)]

theorem dot_massActionField_nonneg (N : Network S) (κ : N.RateConstants)
    {xs : Concentration S} (hxs : xs.Positive) (hcb : N.IsComplexBalanced κ xs)
    {x : Concentration S} (hx : x.Positive) (a : S → ℝ) (δ : ℝ)
    (hδ : ∀ c ∈ N.complexes, ∀ c' ∈ N.complexes,
      |∑ s, ((c s : ℝ) - c' s) * log (xs s)| < δ)
    (hvalid : ∀ c ∈ N.complexes, ∀ c' ∈ N.complexes,
      ∑ s, a s * ((c s : ℝ) - c' s) < 0 → δ ≤ ∑ s, ((c s : ℝ) - c' s) * log (x s)) :
    0 ≤ ∑ s, a s * N.massActionVectorField κ x s := by
  set V := N.complexes
  set U : Complex S → ℝ := fun c => ∑ s, (c s : ℝ) * (log (x s) - log (xs s))
  set g : Complex S → ℝ := fun c => exp (U c)
  set φ : Complex S → ℝ := fun c => ∑ s, a s * (c s : ℝ)
  set w : Complex S → Complex S → ℝ := fun c c' => ∑ r : N.R,
    if (N.reaction r).source = c ∧ (N.reaction r).target = c' then
      κ.k r * c.massActionMonomial xs else 0
  have hw : ∀ c c', 0 ≤ w c c' := fun c c' => sum_nonneg fun r _ => by
    split_ifs
    · exact mul_nonneg (κ.positive r).le (Complex.massActionMonomial_nonneg hxs.nonnegative _)
    · exact le_rfl
  -- the monomial factorization
  have hmono : ∀ c : Complex S, c.massActionMonomial x = c.massActionMonomial xs * g c := by
    intro c
    rw [massActionMonomial_eq_exp hx, massActionMonomial_eq_exp hxs, ← exp_add]
    congr 1
    simp only [U, ← sum_add_distrib]
    exact sum_congr rfl fun s _ => by ring
  -- rewrite the dot product as a double sum over complexes
  have hdot : ∑ s, a s * N.massActionVectorField κ x s =
      ∑ c ∈ V, ∑ c' ∈ V, w c c' * (g c * (φ c' - φ c)) := by
    have h1 : ∑ s, a s * N.massActionVectorField κ x s = ∑ r : N.R,
        κ.k r * (N.reaction r).source.massActionMonomial xs * g (N.reaction r).source *
          (φ (N.reaction r).target - φ (N.reaction r).source) := by
      simp only [massActionVectorField_apply, mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun r _ => ?_
      simp only [massActionRate, hmono, reactionVector_apply, Reaction.vector_apply, φ]
      rw [← sum_sub_distrib, mul_sum]
      exact sum_congr rfl fun s _ => by ring
    rw [h1]
    have h2 : ∀ c ∈ V, ∑ c' ∈ V, w c c' * (g c * (φ c' - φ c)) = ∑ r : N.R,
        ∑ c' ∈ V, if (N.reaction r).source = c ∧ (N.reaction r).target = c' then
          κ.k r * c.massActionMonomial xs * (g c * (φ c' - φ c)) else 0 := by
      intro c _
      simp only [w, sum_mul]
      rw [sum_comm]
      refine sum_congr rfl fun r _ => sum_congr rfl fun c' _ => ?_
      split_ifs <;> ring
    rw [sum_congr rfl h2, sum_comm]
    refine sum_congr rfl fun r _ => ?_
    have hs := N.source_mem_complexes r
    have ht := N.target_mem_complexes r
    have h3 : ∀ c ∈ V, (∑ c' ∈ V, if (N.reaction r).source = c ∧ (N.reaction r).target = c' then
        κ.k r * c.massActionMonomial xs * (g c * (φ c' - φ c)) else 0) =
        if (N.reaction r).source = c then κ.k r * c.massActionMonomial xs *
          (g c * (φ (N.reaction r).target - φ c)) else 0 := by
      intro c _
      by_cases hc : (N.reaction r).source = c
      · simp only [hc, true_and, if_true]
        rw [sum_ite_eq V (N.reaction r).target, if_pos ht]
      · simp [hc]
    rw [sum_congr rfl h3, sum_ite_eq V (N.reaction r).source, if_pos hs]
    ring
  rw [hdot]
  refine CRNT.Persistence.circulation_pairing_nonneg g φ V w hw ?_ ?_
  · -- complex balance is the circulation property
    intro c hc
    have hcb' := hcb c hc
    have hout : ∑ c' ∈ V, w c c' = N.outflow κ xs c := by
      simp only [w, outflow]
      rw [sum_comm]
      refine sum_congr rfl fun r _ => ?_
      by_cases hsr : (N.reaction r).source = c
      · simp only [hsr, true_and]
        rw [sum_ite_eq V (N.reaction r).target, if_pos (N.target_mem_complexes r), if_pos trivial,
          massActionRate, ← hsr]
      · simp [hsr]
    have hin : ∑ c' ∈ V, w c' c = N.inflow κ xs c := by
      simp only [w, inflow]
      rw [sum_comm]
      refine sum_congr rfl fun r _ => ?_
      by_cases htr : (N.reaction r).target = c
      · simp only [htr, and_true]
        rw [sum_ite_eq V (N.reaction r).source, if_pos (N.source_mem_complexes r), if_pos trivial,
          massActionRate]
      · simp [htr]
    rw [hout, hin, hcb']
  · -- the potential is nonincreasing in the height
    intro c hc c' hc' hgle
    by_contra hcon
    push Not at hcon
    have hneg : ∑ s, a s * ((c s : ℝ) - c' s) < 0 := by
      have : ∑ s, a s * ((c s : ℝ) - c' s) = φ c - φ c' := by
        simp only [φ, ← sum_sub_distrib]; exact sum_congr rfl fun s _ => by ring
      rw [this]; linarith
    have h1 := hvalid c hc c' hc' hneg
    have h2 := hδ c hc c' hc'
    have hU : U c' < U c := by
      have : U c - U c' = ∑ s, ((c s : ℝ) - c' s) * log (x s) -
          ∑ s, ((c s : ℝ) - c' s) * log (xs s) := by
        simp only [U, ← sum_sub_distrib]; exact sum_congr rfl fun s _ => by ring
      have := (abs_lt.mp h2).2
      linarith
    have : g c' < g c := exp_lt_exp.mpr hU
    linarith

end Network
end CRNT
