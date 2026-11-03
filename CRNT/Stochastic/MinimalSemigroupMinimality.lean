import CRNT.Stochastic.MinimalSemigroupNonExplosion

/-!
# Minimality and uniqueness of the minimal transition function

Feller's minimality theorem: every nonnegative supersolution `F` of the backward integral equation

`F(t)(a, b) ≥ e^{−q(a) t} [a = b] + ∫₀ᵗ e^{−q(a) s} ∑ᵢ rateᵢ(a) F(t − s)(nextᵢ a, b) ds`

dominates the minimal transition function: `Pmin ≤ F` (`Pmin_le_of_supersolution`). Consequently,
when `Pmin` is stochastic at `a` (no explosion), it is the only sub-stochastic solution of the
backward integral equation in the row of `a` (`eq_Pmin_of_solution`). For stochastic mass action
under the weight condition of `Network.hasSum_transition_one_of_weight`, the backward integral
equation therefore determines the transition function (`Network.eq_transition_of_solution`).
-/

open MeasureTheory intervalIntegral Set Filter
open scoped BigOperators Topology

namespace CRNT

namespace JumpSystem

variable {α : Type*} [DecidableEq α] (J : JumpSystem α)

/-- **Feller's minimality theorem.** -/
theorem P_le_of_supersolution (F : ℝ → α → α → ℝ) (hF0 : ∀ t, 0 ≤ t → ∀ a b, 0 ≤ F t a b)
    (hFc : ∀ a b, ContinuousOn (fun t => F t a b) (Ici 0))
    (hsup : ∀ t, 0 ≤ t → ∀ a b, Real.exp (-(J.q a * t)) * (if a = b then 1 else 0) +
      ∫ s in (0 : ℝ)..t, Real.exp (-(J.q a * s)) * ∑ i, J.rate i a * F (t - s) (J.next i a) b ≤
        F t a b) (k : ℕ) :
    ∀ t, 0 ≤ t → ∀ a b, J.P k t a b ≤ F t a b := by
  have hint : ∀ t, 0 ≤ t → ∀ a b, IntervalIntegrable (fun s => Real.exp (-(J.q a * s)) *
      ∑ i, J.rate i a * F (t - s) (J.next i a) b) volume 0 t := by
    intro t ht a b
    refine ContinuousOn.intervalIntegrable ?_
    refine (Continuous.continuousOn (by fun_prop)).mul (continuousOn_finsetSum _ fun i _ => ?_)
    refine continuousOn_const.mul ((hFc _ b).comp (continuous_const.sub continuous_id).continuousOn
      fun s hs => ?_)
    rw [uIcc_of_le ht] at hs
    exact sub_nonneg.mpr hs.2
  have hnn : ∀ t, 0 ≤ t → ∀ a b, 0 ≤ ∫ s in (0 : ℝ)..t, Real.exp (-(J.q a * s)) *
      ∑ i, J.rate i a * F (t - s) (J.next i a) b := by
    intro t ht a b
    refine intervalIntegral.integral_nonneg ht fun s hs => ?_
    exact mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun i _ =>
      mul_nonneg (J.rate_nonneg i a) (hF0 _ (by linarith [hs.2]) _ _))
  induction k with
  | zero =>
      intro t ht a b
      rw [P_zero]
      linarith [hsup t ht a b, hnn t ht a b]
  | succ k ih =>
      intro t ht a b
      refine le_trans ?_ (hsup t ht a b)
      rw [P_succ]
      refine add_le_add le_rfl (intervalIntegral.integral_mono_on ht
        (J.integrable_term k t a b) (hint t ht a b) fun s hs => ?_)
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_left (ih (t - s) (by linarith [hs.2]) _ _) (J.rate_nonneg i a)

theorem Pmin_le_of_supersolution (F : ℝ → α → α → ℝ) (hF0 : ∀ t, 0 ≤ t → ∀ a b, 0 ≤ F t a b)
    (hFc : ∀ a b, ContinuousOn (fun t => F t a b) (Ici 0))
    (hsup : ∀ t, 0 ≤ t → ∀ a b, Real.exp (-(J.q a * t)) * (if a = b then 1 else 0) +
      ∫ s in (0 : ℝ)..t, Real.exp (-(J.q a * s)) * ∑ i, J.rate i a * F (t - s) (J.next i a) b ≤
        F t a b) {t : ℝ} (ht : 0 ≤ t) (a b : α) : J.Pmin t a b ≤ F t a b :=
  le_of_tendsto' (J.tendsto_P t ht a b) fun k => J.P_le_of_supersolution F hF0 hFc hsup k t ht a b

/-- **Uniqueness without explosion.** If the minimal transition function is stochastic at `a`,
every nonnegative, sub-stochastic solution of the backward integral equation (continuous on
`[0, ∞)`) agrees with it in the row of `a`. -/
theorem eq_Pmin_of_solution (F : ℝ → α → α → ℝ) (hF0 : ∀ t, 0 ≤ t → ∀ a b, 0 ≤ F t a b)
    (hFc : ∀ a b, ContinuousOn (fun t => F t a b) (Ici 0))
    (hsol : ∀ t, 0 ≤ t → ∀ a b, F t a b = Real.exp (-(J.q a * t)) * (if a = b then 1 else 0) +
      ∫ s in (0 : ℝ)..t, Real.exp (-(J.q a * s)) * ∑ i, J.rate i a * F (t - s) (J.next i a) b)
    (hsub : ∀ t, 0 ≤ t → ∀ a (B : Finset α), ∑ b ∈ B, F t a b ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) {a : α} (hstoch : HasSum (fun b => J.Pmin t a b) 1) (b : α) :
    F t a b = J.Pmin t a b := by
  have hle : ∀ c, J.Pmin t a c ≤ F t a c := fun c =>
    J.Pmin_le_of_supersolution F hF0 hFc (fun t ht a b => (hsol t ht a b).symm.le) ht a c
  by_contra hne
  have hlt : J.Pmin t a b < F t a b := lt_of_le_of_ne (hle b) (Ne.symm hne)
  set δ := F t a b - J.Pmin t a b with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  obtain ⟨B, hB⟩ : ∃ B : Finset α, 1 - δ < ∑ c ∈ B, J.Pmin t a c :=
    (Filter.Tendsto.eventually hstoch (lt_mem_nhds (by linarith))).exists
  have hdiff : δ ≤ ∑ c ∈ insert b B, (F t a c - J.Pmin t a c) :=
    Finset.single_le_sum (f := fun c => F t a c - J.Pmin t a c)
      (fun c _ => sub_nonneg.mpr (hle c)) (Finset.mem_insert_self b B)
  have hB' : ∑ c ∈ B, J.Pmin t a c ≤ ∑ c ∈ insert b B, J.Pmin t a c :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_insert b B) fun c _ _ =>
      J.Pmin_nonneg t ht a c
  have h1 := hsub t ht a (insert b B)
  rw [Finset.sum_sub_distrib] at hdiff
  linarith

end JumpSystem

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The backward equation determines the transition function** of stochastic mass action when
some positive linear weight is increased only by reactions with at most one reactant molecule. -/
theorem eq_transition_of_solution (N : Network S) (κ : RateConstants N) (w : S → ℝ)
    (hw : ∀ s, 0 < w s)
    (hmol : ∀ r, 0 < ∑ s, w s * N.reactionVector r s → ∑ s, (N.reaction r).source s ≤ 1)
    (F : ℝ → (S → ℕ) → (S → ℕ) → ℝ) (hF0 : ∀ t, 0 ≤ t → ∀ n m, 0 ≤ F t n m)
    (hFc : ∀ n m, ContinuousOn (fun t => F t n m) (Set.Ici 0))
    (hsol : ∀ t, 0 ≤ t → ∀ n m, F t n m = Real.exp (-((N.jumpSystem κ).q n * t)) *
      (if n = m then 1 else 0) + ∫ s in (0 : ℝ)..t, Real.exp (-((N.jumpSystem κ).q n * s)) *
        ∑ i, (N.jumpSystem κ).rate i n * F (t - s) ((N.jumpSystem κ).next i n) m)
    (hsub : ∀ t, 0 ≤ t → ∀ n (B : Finset (S → ℕ)), ∑ m ∈ B, F t n m ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) (n m : S → ℕ) : F t n m = N.transition κ t n m :=
  (N.jumpSystem κ).eq_Pmin_of_solution F hF0 hFc hsol hsub ht
    (N.hasSum_transition_one_of_weight κ w hw hmol ht n) m

end Network

end CRNT
