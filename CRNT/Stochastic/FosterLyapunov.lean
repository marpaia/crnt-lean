import CRNT.Stochastic.CTMC

/-!
# Foster--Lyapunov drift certificates for stochastic CRNs

This file introduces the observable (backward) generator of the stochastic mass-action
chain and packages the standard linear Foster--Lyapunov drift condition.  It is theorem-
level infrastructure only: no LP solver or stochastic simulation is included.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Count vector after firing an enabled reaction.  Disabled reactions leave the state
unchanged; their stochastic propensity is zero anyway. -/
def fireCount (N : Network S) (n : S → ℕ) (r : N.R) : S → ℕ :=
  if h : N.Enabled n r then
    fun s => n s - (N.reaction r).source s + (N.reaction r).target s
  else n

/-- Backward generator acting on a real observable. -/
noncomputable def observableGenerator (N : Network S) (κ : N.RateConstants)
    (f : (S → ℕ) → ℝ) (n : S → ℕ) : ℝ :=
  ∑ r : N.R, N.stochasticMassActionRate κ n r * (f (N.fireCount n r) - f n)

/-- Linear count observable. -/
def linearObservable (w : S → ℝ) (n : S → ℕ) : ℝ :=
  ∑ s : S, w s * (n s : ℝ)

/-- Increment of a linear observable along an enabled reaction equals the weight paired
with the reaction vector. -/
theorem linearObservable_fireCount_sub {N : Network S} (w : S → ℝ)
    (n : S → ℕ) (r : N.R) (hen : N.Enabled n r) :
    linearObservable w (N.fireCount n r) - linearObservable w n =
      ∑ s : S, w s * N.reactionVector r s := by
  unfold fireCount linearObservable
  simp [hen]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  have hs := hen s
  rw [Nat.cast_sub hs]
  ring

/-- Disabled reactions have zero stochastic propensity. -/
theorem stochasticMassActionRate_eq_zero_of_not_enabled (N : Network S)
    (κ : N.RateConstants) (n : S → ℕ) (r : N.R) (hdis : ¬ N.Enabled n r) :
    N.stochasticMassActionRate κ n r = 0 := by
  unfold Enabled at hdis
  push_neg at hdis
  obtain ⟨s, hs⟩ := hdis
  unfold stochasticMassActionRate
  have hz : (n s).descFactorial ((N.reaction r).source s) = 0 :=
    Nat.descFactorial_eq_zero_iff_lt.mpr hs
  have hprod : (∏ t : S, ((n t).descFactorial ((N.reaction r).source t) : ℝ)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ s)
    norm_num [hz]
  rw [hprod, mul_zero]

/-- **Exact linear-observable drift formula.** -/
theorem observableGenerator_linear (N : Network S) (κ : N.RateConstants)
    (w : S → ℝ) (n : S → ℕ) :
    N.observableGenerator κ (linearObservable w) n =
      ∑ r : N.R, N.stochasticMassActionRate κ n r *
        (∑ s : S, w s * N.reactionVector r s) := by
  unfold observableGenerator
  apply Finset.sum_congr rfl
  intro r _
  by_cases hen : N.Enabled n r
  · rw [linearObservable_fireCount_sub w n r hen]
  · rw [N.stochasticMassActionRate_eq_zero_of_not_enabled κ n r hen]
    simp

/-- Positive linear Lyapunov weight. -/
def IsPositiveWeight (w : S → ℝ) : Prop := ∀ s, 0 < w s

/-- A standard linear Foster--Lyapunov certificate:
`LV(n) ≤ b - c V(n)` with `w>0`, `c>0`, and `b≥0`. -/
structure LinearFosterLyapunovCertificate (N : Network S) (κ : N.RateConstants) where
  weight : S → ℝ
  c : ℝ
  b : ℝ
  weight_pos : IsPositiveWeight weight
  c_pos : 0 < c
  b_nonneg : 0 ≤ b
  drift : ∀ n : S → ℕ,
    N.observableGenerator κ (linearObservable weight) n ≤
      b - c * linearObservable weight n

/-- A Foster certificate gives negative drift outside the sublevel `V ≤ b/c`. -/
theorem LinearFosterLyapunovCertificate.drift_neg_above
    {N : Network S} {κ : N.RateConstants}
    (C : LinearFosterLyapunovCertificate N κ) {n : S → ℕ}
    (hn : C.b / C.c < linearObservable C.weight n) :
    N.observableGenerator κ (linearObservable C.weight) n < 0 := by
  have hbc : C.b < C.c * linearObservable C.weight n :=
    by simpa [mul_comm] using (div_lt_iff₀ C.c_pos).mp hn
  exact lt_of_le_of_lt (C.drift n) (sub_neg.mpr hbc)

/-- Positive weights make the linear observable nonnegative. -/
theorem linearObservable_nonneg_of_positive {w : S → ℝ} (hw : IsPositiveWeight w)
    (n : S → ℕ) : 0 ≤ linearObservable w n := by
  unfold linearObservable
  exact Finset.sum_nonneg fun s _ => mul_nonneg (hw s).le (Nat.cast_nonneg _)

end Network

end CRNT
