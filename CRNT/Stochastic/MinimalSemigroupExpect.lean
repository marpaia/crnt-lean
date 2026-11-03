import CRNT.Stochastic.MinimalSemigroupForward
import CRNT.Stochastic.MinimalSemigroupNonExplosion
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Forward equation for expectations (Dynkin's formula in derivative form)

For an observable `g`, write `(Qg)(x) = ∑_i λ_i(x) (g(next_i x) − g(x))` (`drift g`). If there is
`W > 0` with `QW ≤ cW` and `((1 + |g|)(1 + q) + ∑_i λ_i |g ∘ next_i|)/W` summable, then for `t > 0`

`d/dt ∑_b P(t)(a, b) g(b) = ∑_x P(t)(a, x) (Qg)(x)`

(`hasDerivAt_expect`). The proof differentiates the series term by term with the pointwise forward
equation, dominated through `P(s)(a, b) ≤ e^{cs} W(a)/W(b)` (`Pmin_le_div`).
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace CRNT
namespace JumpSystem

variable {α : Type*} [DecidableEq α] (J : JumpSystem α)

/-- The neighbourhood carrying the row `Q(x, ·)`. -/
noncomputable def nbhd (x : α) : Finset α := insert x (Finset.univ.image fun i => J.next i x)

theorem Q_eq_zero_of_not_mem {x b : α} (hb : b ∉ J.nbhd x) : J.Q x b = 0 := by
  unfold Q
  have h1 : x ≠ b := fun h => hb (h ▸ Finset.mem_insert_self _ _)
  have h2 : ∀ i, J.next i x ≠ b := fun i h =>
    hb (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h⟩))
  simp [h1, h2]

theorem abs_Q_le (x b : α) :
    |J.Q x b| ≤ ∑ i, J.rate i x * (if J.next i x = b then 1 else 0) +
      J.q x * (if x = b then 1 else 0) := by
  unfold Q
  refine (abs_sub _ _).trans (add_le_add (le_of_eq (abs_of_nonneg (Finset.sum_nonneg fun i _ =>
    mul_nonneg (J.rate_nonneg i x) (by split_ifs <;> norm_num)))) (le_of_eq (abs_of_nonneg
      (mul_nonneg (J.q_nonneg x) (by split_ifs <;> norm_num)))))

theorem tsum_Q_mul (g : α → ℝ) (x : α) : ∑' b, J.Q x b * g b = J.drift g x := by
  rw [tsum_eq_sum (s := J.nbhd x) fun b hb => by rw [J.Q_eq_zero_of_not_mem hb, zero_mul]]
  unfold Q drift
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]
  have h1 : ∀ i, ∑ b ∈ J.nbhd x, J.rate i x * (if J.next i x = b then 1 else 0) * g b =
      J.rate i x * g (J.next i x) := by
    intro i
    rw [Finset.sum_eq_single (J.next i x) (fun b _ hb => by simp [Ne.symm hb])
      (fun h => absurd (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _,
        rfl⟩)) h)]
    simp
  have h2 : ∑ b ∈ J.nbhd x, J.q x * (if x = b then 1 else 0) * g b = J.q x * g x := by
    simp [nbhd]
  rw [Finset.sum_congr rfl fun i _ => h1 i, h2, q, Finset.sum_mul]
  simp only [mul_sub, Finset.sum_sub_distrib]

theorem sum_abs_Q_mul_le (g : α → ℝ) (x : α) :
    ∑' b, |J.Q x b| * |g b| ≤ ∑ i, J.rate i x * |g (J.next i x)| + J.q x * |g x| := by
  rw [tsum_eq_sum (s := J.nbhd x) fun b hb => by rw [J.Q_eq_zero_of_not_mem hb, abs_zero, zero_mul]]
  calc ∑ b ∈ J.nbhd x, |J.Q x b| * |g b|
      ≤ ∑ b ∈ J.nbhd x, (∑ i, J.rate i x * (if J.next i x = b then 1 else 0) +
          J.q x * (if x = b then 1 else 0)) * |g b| :=
        Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right (J.abs_Q_le x b) (abs_nonneg _)
    _ = ∑ i, J.rate i x * |g (J.next i x)| + J.q x * |g x| := by
        simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
        rw [Finset.sum_comm]
        congr 1
        · refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_eq_single (J.next i x) (fun b _ hb => by simp [Ne.symm hb])
            (fun h => absurd (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,
              Finset.mem_univ _, rfl⟩)) h)]
          simp
        · simp [nbhd]

/-- Pointwise bound from a Lyapunov function. -/
theorem Pmin_le_div (W : α → ℝ) (hW : ∀ x, 0 < W x) {c : ℝ} (hc : 0 ≤ c)
    (hdrift : ∀ x, J.drift W x ≤ c * W x) {t : ℝ} (ht : 0 ≤ t) (a b : α) :
    J.Pmin t a b ≤ Real.exp (c * t) * W a / W b := by
  have h := J.sum_Pmin_mul_le W (fun x => (hW x).le) hc hdrift ht a {b}
  rw [Finset.sum_singleton] at h
  rw [le_div_iff₀ (hW b)]
  exact h

/-- **Forward equation for expectations.** -/
theorem hasDerivAt_expect (g W : α → ℝ) (hW : ∀ x, 0 < W x) {c : ℝ} (hc : 0 ≤ c)
    (hdrift : ∀ x, J.drift W x ≤ c * W x)
    (hH : Summable fun x =>
      ((1 + |g x|) * (1 + J.q x) + ∑ i, J.rate i x * |g (J.next i x)|) / W x)
    {t : ℝ} (ht : 0 < t) (a : α) :
    HasDerivAt (fun s => ∑' b, J.Pmin s a b * g b) (∑' x, J.Pmin t a x * J.drift g x) t := by
  set H : α → ℝ := fun x =>
    ((1 + |g x|) * (1 + J.q x) + ∑ i, J.rate i x * |g (J.next i x)|) / W x with hHdef
  have hRi : ∀ x, 0 ≤ ∑ i, J.rate i x * |g (J.next i x)| := fun x =>
    Finset.sum_nonneg fun i _ => mul_nonneg (J.rate_nonneg i x) (abs_nonneg _)
  have hH0 : ∀ x, 0 ≤ H x := fun x => div_nonneg (add_nonneg (mul_nonneg (by positivity)
    (by linarith [J.q_nonneg x])) (hRi x)) (hW x).le
  set T := t + 1 with hT
  set B := Real.exp (c * T) * W a with hB
  have hB0 : 0 ≤ B := mul_nonneg (Real.exp_pos _).le (hW a).le
  have hP : ∀ s, 0 ≤ s → s ≤ T → ∀ x, J.Pmin s a x ≤ B / W x := by
    intro s hs hsT x
    refine (J.Pmin_le_div W hW hc hdrift hs a x).trans ?_
    refine div_le_div_of_nonneg_right ?_ (hW x).le
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsT hc))
      (hW a).le
  -- the dominating double family
  set E : α → α → ℝ := fun x b => |J.Q x b| * (1 + |g b|) / W x with hE
  have hE0 : ∀ x b, 0 ≤ E x b := fun x b =>
    div_nonneg (mul_nonneg (abs_nonneg _) (by positivity)) (hW x).le
  have hErow : ∀ x, Summable (E x) := fun x =>
    summable_of_ne_finset_zero (s := J.nbhd x) fun b hb => by
      simp only [hE, J.Q_eq_zero_of_not_mem hb, abs_zero, zero_mul, zero_div]
  have hErowsum : ∀ x, ∑' b, E x b ≤ 2 * H x := by
    intro x
    have h1 := J.sum_abs_Q_mul_le (fun b => 1 + |g b|) x
    have e1 : ∀ y, abs (1 + |g y|) = 1 + |g y| := fun y => abs_of_nonneg (by positivity)
    simp only [e1] at h1
    have e : ∑' b, E x b = (∑' b, |J.Q x b| * (1 + |g b|)) / W x := by
      rw [← tsum_div_const]
    rw [e, div_le_iff₀ (hW x)]
    have h2 : ∑ i, J.rate i x * (1 + |g (J.next i x)|) = J.q x + ∑ i, J.rate i x * |g (J.next i x)| := by
      simp only [mul_add, mul_one, Finset.sum_add_distrib, q]
    have h3 : 2 * H x * W x = 2 * ((1 + |g x|) * (1 + J.q x) + ∑ i, J.rate i x * |g (J.next i x)|) := by
      simp only [hHdef]; field_simp [(hW x).ne']
    rw [h3]
    have := J.q_nonneg x
    have := abs_nonneg (g x)
    nlinarith [hRi x]
  have hEsum : Summable (Function.uncurry E) :=
    (summable_prod_of_nonneg fun p => hE0 p.1 p.2).mpr ⟨hErow,
      Summable.of_nonneg_of_le (fun x => tsum_nonneg (hE0 x)) hErowsum (hH.mul_left 2)⟩
  have hEcol : Summable fun b => ∑' x, E x b := hEsum.prod_symm.prod
  have hEfix : ∀ b, Summable fun x => E x b := fun b => hEsum.prod_symm.prod_factor b
  -- termwise derivatives on `U = (t/2, T)`
  set U := Ioo (t / 2) T with hU
  have hsumq : ∀ s ∈ U, Summable fun x => J.Pmin s a x * J.q x := by
    intro s hs
    have hs0 : 0 ≤ s := by linarith [hs.1]
    refine Summable.of_nonneg_of_le (fun x => mul_nonneg (J.Pmin_nonneg s hs0 a x) (J.q_nonneg x))
      (fun x => ?_) (hH.mul_left B)
    have hqH : J.q x / W x ≤ H x := by
      simp only [hHdef]
      refine div_le_div_of_nonneg_right ?_ (hW x).le
      have := abs_nonneg (g x); have := J.q_nonneg x; nlinarith [hRi x]
    calc J.Pmin s a x * J.q x ≤ B / W x * J.q x :=
          mul_le_mul_of_nonneg_right (hP s hs0 hs.2.le x) (J.q_nonneg x)
      _ = B * (J.q x / W x) := by ring
      _ ≤ B * H x := mul_le_mul_of_nonneg_left hqH hB0
  have hderiv : ∀ b, ∀ s ∈ U, HasDerivAt (fun s => J.Pmin s a b * g b)
      ((∑' x, J.Pmin s a x * J.Q x b) * g b) s := by
    intro b s hs
    have hs0 : 0 < s := by linarith [hs.1]
    exact (J.hasDerivAt_Pmin_forward hs0 a b (hsumq s hs)).mul_const (g b)
  have hbound : ∀ b, ∀ s ∈ U, ‖(∑' x, J.Pmin s a x * J.Q x b) * g b‖ ≤ B * ∑' x, E x b := by
    intro b s hs
    have hs0 : 0 ≤ s := by linarith [hs.1]
    have hpt : ∀ x, ‖J.Pmin s a x * J.Q x b‖ ≤ B * (|J.Q x b| / W x) := fun x => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (J.Pmin_nonneg s hs0 a x)]
      calc J.Pmin s a x * |J.Q x b| ≤ B / W x * |J.Q x b| :=
            mul_le_mul_of_nonneg_right (hP s hs0 hs.2.le x) (abs_nonneg _)
        _ = B * (|J.Q x b| / W x) := by ring
    have hsQ : Summable fun x => |J.Q x b| / W x :=
      Summable.of_nonneg_of_le (fun x => div_nonneg (abs_nonneg _) (hW x).le)
        (fun x => div_le_div_of_nonneg_right (le_mul_of_one_le_right (abs_nonneg _)
          (by linarith [abs_nonneg (g b)])) (hW x).le) (hEfix b)
    have h1 : |∑' x, J.Pmin s a x * J.Q x b| ≤ ∑' x, B * (|J.Q x b| / W x) := by
      have hn : Summable fun x => ‖J.Pmin s a x * J.Q x b‖ :=
        Summable.of_nonneg_of_le (fun x => norm_nonneg _) hpt (hsQ.mul_left B)
      have := norm_tsum_le_tsum_norm hn
      rw [Real.norm_eq_abs] at this
      exact this.trans (Summable.tsum_le_tsum hpt hn (hsQ.mul_left B))
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |∑' x, J.Pmin s a x * J.Q x b| * |g b|
        ≤ (B * ∑' x, |J.Q x b| / W x) * (1 + |g b|) :=
          mul_le_mul (h1.trans (le_of_eq tsum_mul_left)) (by linarith) (abs_nonneg _)
            (mul_nonneg hB0 (tsum_nonneg fun x => div_nonneg (abs_nonneg _) (hW x).le))
      _ = B * ∑' x, E x b := by
          rw [mul_assoc, ← tsum_mul_right]
          congr 1
          exact tsum_congr fun x => by simp only [hE]; ring
  have htU : t ∈ U := ⟨by linarith, by linarith⟩
  have hg0 : Summable fun b => J.Pmin t a b * g b := by
    refine Summable.of_norm_bounded (hH.mul_left B) fun b => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (J.Pmin_nonneg t ht.le a b)]
    have hgH : |g b| / W b ≤ H b := by
      simp only [hHdef]
      refine div_le_div_of_nonneg_right ?_ (hW b).le
      have := abs_nonneg (g b); have := J.q_nonneg b; nlinarith [hRi b]
    calc J.Pmin t a b * |g b| ≤ B / W b * |g b| :=
          mul_le_mul_of_nonneg_right (hP t ht.le (by linarith) b) (abs_nonneg _)
      _ = B * (|g b| / W b) := by ring
      _ ≤ B * H b := mul_le_mul_of_nonneg_left hgH hB0
  have hmain := hasDerivAt_tsum_of_isPreconnected (hEcol.mul_left B) isOpen_Ioo
    (convex_Ioo _ _).isPreconnected hderiv hbound htU hg0 htU
  -- identify the derivative
  convert hmain using 1
  -- `∑_x P(t)(a,x) (Qg)(x) = ∑_b (∑_x P(t)(a,x) Q(x,b)) g(b)`
  set G : α → α → ℝ := fun x b => J.Pmin t a x * J.Q x b * g b with hG
  have hGb : ∀ x b, ‖G x b‖ ≤ B * E x b := fun x b => by
    simp only [hG, hE, Real.norm_eq_abs, abs_mul, abs_of_nonneg (J.Pmin_nonneg t ht.le a x)]
    have h1 := hP t ht.le (by linarith) x
    calc J.Pmin t a x * |J.Q x b| * |g b| ≤ B / W x * |J.Q x b| * (1 + |g b|) :=
          mul_le_mul (mul_le_mul_of_nonneg_right h1 (abs_nonneg _)) (by linarith)
            (abs_nonneg _) (mul_nonneg (div_nonneg hB0 (hW x).le) (abs_nonneg _))
      _ = B * (|J.Q x b| * (1 + |g b|) / W x) := by ring
  have hGsum : Summable (Function.uncurry G) :=
    Summable.of_norm_bounded (hEsum.mul_left B) fun p => hGb p.1 p.2
  calc ∑' x, J.Pmin t a x * J.drift g x = ∑' x, ∑' b, G x b := by
        refine tsum_congr fun x => ?_
        rw [← J.tsum_Q_mul g x, ← tsum_mul_left]
        exact tsum_congr fun b => by simp only [hG]; ring
    _ = ∑' b, ∑' x, G x b := hGsum.tsum_comm.symm
    _ = ∑' b, (∑' x, J.Pmin t a x * J.Q x b) * g b := by
        refine tsum_congr fun b => ?_
        rw [← tsum_mul_right]

end JumpSystem
end CRNT
