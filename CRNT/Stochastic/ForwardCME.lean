import CRNT.Stochastic.MinimalSemigroupStationary

/-!
# Solutions of the forward master equation are given by the transition function

Let `π_s`, `s ∈ [0, T]`, be nonnegative laws on counts solving the forward chemical master equation
`∂ₛ π_s(n) = ∑_r inflow_r(π_s)(n) − π_s(n) λ(n)` (`cmeRHS`), dominated by `D` with
`∑_n D(n) (1 + λ(n)) < ∞`. Then `π_T = π_0 P(T)`: `∑_n π_0(n) P(T)(n, m) = π_T(m)`
(`tsum_mul_transition_of_forwardCME`). No non-explosion assumption is needed.

Proof: `h(s) = ∑_n π_s(n) P(T − s)(n, m)` is continuous on `[0, T]` and, by term-by-term
differentiation with the backward equation, has derivative
`∑_n cmeRHS(π_s)(n) f(n) − ∑_n π_s(n) (A f)(n)` with `f = P(T − s)(·, m)`, which vanishes by the
reindexing of the flux along the jumps (`tsum_mul_rate_fire_eq`).
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The right-hand side of the forward chemical master equation. -/
noncomputable def cmeRHS (N : Network S) (κ : RateConstants N) (π : (S → ℕ) → ℝ) (n : S → ℕ) :
    ℝ := ∑ r, N.cmeInflow κ π n r - π n * N.exitRate κ n

theorem cmeInflow_nonneg (N : Network S) (κ : RateConstants N) {π : (S → ℕ) → ℝ}
    (hπ : ∀ n, 0 ≤ π n) (m : S → ℕ) (r : N.R) : 0 ≤ N.cmeInflow κ π m r := by
  unfold cmeInflow
  split_ifs
  · exact mul_nonneg (hπ _) (N.stochasticMassActionRate_nonneg κ _ r)
  · exact le_rfl

theorem cmeInflow_mono (N : Network S) (κ : RateConstants N) {π π' : (S → ℕ) → ℝ}
    (_hπ : ∀ n, 0 ≤ π n) (hle : ∀ n, π n ≤ π' n) (m : S → ℕ) (r : N.R) :
    N.cmeInflow κ π m r ≤ N.cmeInflow κ π' m r := by
  unfold cmeInflow
  split_ifs
  · exact mul_le_mul_of_nonneg_right (hle _) (N.stochasticMassActionRate_nonneg κ _ r)
  · exact le_rfl

/-- **Representation of forward CME solutions.** -/
theorem tsum_mul_transition_of_forwardCME (N : Network S) (κ : RateConstants N) {T : ℝ}
    (hT : 0 < T) (π : ℝ → (S → ℕ) → ℝ) (D : (S → ℕ) → ℝ)
    (hπ0 : ∀ s ∈ Icc 0 T, ∀ n, 0 ≤ π s n) (hD : ∀ s ∈ Icc 0 T, ∀ n, π s n ≤ D n)
    (hDs : Summable fun n => D n * (1 + N.exitRate κ n))
    (hcont : ∀ n, ContinuousOn (fun s => π s n) (Icc 0 T))
    (hderiv : ∀ s ∈ Ioo 0 T, ∀ n, HasDerivAt (fun s => π s n) (N.cmeRHS κ (π s) n) s)
    (m : S → ℕ) : ∑' n, π 0 n * N.transition κ T n m = π T m := by
  have hD0 : ∀ n, 0 ≤ D n := fun n => (hπ0 0 ⟨le_rfl, hT.le⟩ n).trans (hD 0 ⟨le_rfl, hT.le⟩ n)
  have hE0 := N.exitRate_nonneg κ
  have hDsum : Summable D := Summable.of_nonneg_of_le hD0
    (fun n => le_mul_of_one_le_right (hD0 n) (by linarith [hE0 n])) hDs
  have hDE : Summable fun n => D n * N.exitRate κ n := Summable.of_nonneg_of_le
    (fun n => mul_nonneg (hD0 n) (hE0 n))
    (fun n => mul_le_mul_of_nonneg_left (by linarith) (hD0 n)) hDs
  have hDlam : ∀ r, Summable fun n => D n * N.stochasticMassActionRate κ n r := fun r =>
    Summable.of_nonneg_of_le (fun n => mul_nonneg (hD0 n) (N.stochasticMassActionRate_nonneg κ n r))
      (fun n => mul_le_mul_of_nonneg_left (Finset.single_le_sum
        (f := fun r => N.stochasticMassActionRate κ n r)
        (fun r _ => N.stochasticMassActionRate_nonneg κ n r) (Finset.mem_univ r)) (hD0 n)) hDE
  -- summable majorants of the inflows
  have hinD : ∀ r, Summable fun n => N.cmeInflow κ D n r := fun r => by
    have := (N.tsum_mul_rate_fire_eq κ D (fun _ => 1) r (by simpa using hDlam r)).1
    simpa using this
  have hP0 : ∀ τ, 0 ≤ τ → ∀ n, 0 ≤ N.transition κ τ n m := fun τ hτ n =>
    N.transition_nonneg κ hτ n m
  have hP1 : ∀ τ, 0 ≤ τ → ∀ n, N.transition κ τ n m ≤ 1 := fun τ hτ n =>
    N.transition_le_one κ hτ n m
  -- the term derivative
  let G : (S → ℕ) → ℝ → ℝ := fun n s => π s n * N.transition κ (T - s) n m
  let G' : (S → ℕ) → ℝ → ℝ := fun n s => N.cmeRHS κ (π s) n * N.transition κ (T - s) n m -
    π s n * (-N.exitRate κ n * N.transition κ (T - s) n m +
      ∑ r, N.stochasticMassActionRate κ n r * N.transition κ (T - s) (N.jumpNextCount n r) m)
  have hG : ∀ n s, s ∈ Ioo (0 : ℝ) T → HasDerivAt (G n) (G' n s) s := by
    intro n s hs
    have h1 := hderiv s hs n
    have h2 : HasDerivAt (fun s => N.transition κ (T - s) n m)
        ((-N.exitRate κ n * N.transition κ (T - s) n m +
          ∑ r, N.stochasticMassActionRate κ n r *
            N.transition κ (T - s) (N.jumpNextCount n r) m) * (-1)) s :=
      (N.hasDerivAt_transition κ (show 0 < T - s by linarith [hs.2]) n m).comp s
        ((hasDerivAt_id s).const_sub T)
    have := h1.mul h2
    convert this using 1
    simp only [G']; ring
  -- bound on the derivative
  set u : (S → ℕ) → ℝ := fun n => ∑ r, N.cmeInflow κ D n r + 3 * (D n * N.exitRate κ n) with hu
  have husum : Summable u := (summable_sum fun r _ => hinD r).add (hDE.mul_left 3)
  have hGb : ∀ n s, s ∈ Ioo (0 : ℝ) T → ‖G' n s‖ ≤ u n := by
    intro n s hs
    have hsI : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.le⟩
    have hTs : 0 ≤ T - s := by linarith [hs.2]
    have hπ := hπ0 s hsI
    have hin : ∀ r, N.cmeInflow κ (π s) n r ≤ N.cmeInflow κ D n r := fun r =>
      N.cmeInflow_mono κ hπ (hD s hsI) n r
    have hin0 : ∀ r, 0 ≤ N.cmeInflow κ (π s) n r := fun r => N.cmeInflow_nonneg κ hπ n r
    have hsumin : ∑ r, N.cmeInflow κ (π s) n r ≤ ∑ r, N.cmeInflow κ D n r :=
      Finset.sum_le_sum fun r _ => hin r
    have hsumin0 : 0 ≤ ∑ r, N.cmeInflow κ (π s) n r := Finset.sum_nonneg fun r _ => hin0 r
    have hp0 := hP0 (T - s) hTs n
    have hp1 := hP1 (T - s) hTs n
    have hS0 : 0 ≤ ∑ r, N.stochasticMassActionRate κ n r *
        N.transition κ (T - s) (N.jumpNextCount n r) m :=
      Finset.sum_nonneg fun r _ => mul_nonneg (N.stochasticMassActionRate_nonneg κ n r)
        (hP0 _ hTs _)
    have hS1 : ∑ r, N.stochasticMassActionRate κ n r *
        N.transition κ (T - s) (N.jumpNextCount n r) m ≤ N.exitRate κ n := by
      unfold exitRate
      exact Finset.sum_le_sum fun r _ =>
        mul_le_of_le_one_right (N.stochasticMassActionRate_nonneg κ n r) (hP1 _ hTs _)
    have hπD := hD s hsI n
    have hπn := hπ n
    have hE := hE0 n
    rw [Real.norm_eq_abs, abs_le]
    simp only [G', cmeRHS, hu]
    have hDE' : π s n * N.exitRate κ n ≤ D n * N.exitRate κ n := mul_le_mul_of_nonneg_right hπD hE
    constructor <;> nlinarith [mul_nonneg hπn hE, mul_nonneg (mul_nonneg hπn hE) hp0,
      mul_nonneg hsumin0 hp0, mul_le_mul_of_nonneg_left hp1 hsumin0, mul_nonneg hπn hS0,
      mul_le_mul_of_nonneg_left hS1 hπn, mul_le_mul_of_nonneg_left hp1 (mul_nonneg hπn hE)]
  have hsumG : ∀ s ∈ Icc (0 : ℝ) T, Summable fun n => G n s := fun s hs =>
    Summable.of_nonneg_of_le (fun n => mul_nonneg (hπ0 s hs n) (hP0 (T - s) (by linarith [hs.2]) n))
      (fun n => (mul_le_of_le_one_right (hπ0 s hs n) (hP1 _ (by linarith [hs.2]) n)).trans
        (hD s hs n)) hDsum
  have hzero : ∀ s ∈ Ioo (0 : ℝ) T, ∑' n, G' n s = 0 := by
    intro s hs
    have hsI : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.le⟩
    have hTs : 0 ≤ T - s := by linarith [hs.2]
    have hfire : ∀ r, Summable fun n => π s n * N.stochasticMassActionRate κ n r *
        N.transition κ (T - s) (N.fireCount n r) m := fun r =>
      Summable.of_nonneg_of_le (fun n => mul_nonneg (mul_nonneg (hπ0 s hsI n)
        (N.stochasticMassActionRate_nonneg κ n r)) (hP0 _ hTs _))
        (fun n => (mul_le_of_le_one_right (mul_nonneg (hπ0 s hsI n)
          (N.stochasticMassActionRate_nonneg κ n r)) (hP1 _ hTs _)).trans
          (mul_le_mul_of_nonneg_right (hD s hsI n) (N.stochasticMassActionRate_nonneg κ n r)))
        (hDlam r)
    have hre : ∀ r, Summable (fun l => N.transition κ (T - s) l m * N.cmeInflow κ (π s) l r) ∧
        ∑' l, π s l * N.stochasticMassActionRate κ l r * N.transition κ (T - s) (N.fireCount l r) m
          = ∑' l, N.transition κ (T - s) l m * N.cmeInflow κ (π s) l r := fun r =>
      N.tsum_mul_rate_fire_eq κ (π s) (fun l => N.transition κ (T - s) l m) r (hfire r)
    have hrewrite : ∀ n, G' n s = ∑ r, (N.transition κ (T - s) n m * N.cmeInflow κ (π s) n r -
        π s n * N.stochasticMassActionRate κ n r * N.transition κ (T - s) (N.fireCount n r) m) := by
      intro n
      have hj := N.sum_rate_mul_jumpNextCount κ (fun l => N.transition κ (T - s) l m) n
      calc G' n s = (∑ r, N.cmeInflow κ (π s) n r) * N.transition κ (T - s) n m -
            π s n * ∑ r, N.stochasticMassActionRate κ n r *
              N.transition κ (T - s) (N.fireCount n r) m := by
            simp only [G', cmeRHS]
            rw [hj, exitRate]
            ring
        _ = _ := by
            rw [Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
            congr 1
            · exact Finset.sum_congr rfl fun r _ => by ring
            · exact Finset.sum_congr rfl fun r _ => by ring
    rw [tsum_congr hrewrite, Summable.tsum_finsetSum fun r _ => (hre r).1.sub (hfire r)]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [(hre r).1.tsum_sub (hfire r), (hre r).2, sub_self]
  have hderivH : ∀ s ∈ Ioo (0 : ℝ) T, HasDerivAt (fun s => ∑' n, G n s) 0 s := by
    intro s hs
    have h := hasDerivAt_tsum_of_isPreconnected husum isOpen_Ioo isPreconnected_Ioo hG hGb hs
      (hsumG s ⟨hs.1.le, hs.2.le⟩) hs
    rwa [hzero s hs] at h
  have hcontH : ContinuousOn (fun s => ∑' n, G n s) (Icc 0 T) := by
    refine continuousOn_tsum (u := D) (fun n => (hcont n).mul ?_) hDsum fun n s hs => ?_
    · refine (N.continuousOn_transition κ n m).comp (continuous_const.sub continuous_id).continuousOn
        fun s hs => ?_
      show (0 : ℝ) ≤ T - s
      linarith [hs.2]
    · have hTs : 0 ≤ T - s := by linarith [hs.2]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hπ0 s hs n) (hP0 _ hTs n))]
      exact (mul_le_of_le_one_right (hπ0 s hs n) (hP1 _ hTs n)).trans (hD s hs n)
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun s => ∑' n, G n s) (fun _ => (0 : ℝ))
    hT hcontH fun x hx => hderivH x hx
  rw [eq_div_iff (by linarith), zero_mul] at hslope
  have hT0 : ∑' n, G n T = π T m := by
    have h : ∀ n, G n T = if n = m then π T m else 0 := by
      intro n
      simp only [G, sub_self, transition_zero]
      split_ifs with h
      · subst h; simp
      · simp
    simp only [h, tsum_ite_eq]
  have h00 : ∑' n, G n 0 = ∑' n, π 0 n * N.transition κ T n m := by
    simp only [G, sub_zero]
  linarith

end Network
end CRNT
