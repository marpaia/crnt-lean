import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Minimal transition functions of continuous-time jump processes

A **jump system** on a state type `α` has finitely many jump channels `i`, each with a
nonnegative rate `rate i a` and a target `next i a`; the exit rate is `q a = ∑ i, rate i a`.
Stochastic mass-action kinetics is the jump system on `ℕ^S` with one channel per reaction.

The transition probabilities of the process with at most `k` jumps are defined by the backward
recursion (Feller's construction of the minimal solution of the Kolmogorov equations)

`P₀(t)(a, b) = e^{−q(a) t} [a = b]`,
`P_{k+1}(t)(a, b) = e^{−q(a) t} [a = b] + ∫₀ᵗ e^{−q(a) s} ∑ᵢ rate_i(a) P_k(t − s)(next_i a, b) ds`.

Proved here: each `P_k(·)(a, b)` is continuous (`continuous_P`), nonnegative on `t ≥ 0`
(`P_nonneg`), nondecreasing in `k` (`P_mono`), and sub-stochastic: every finite row sum is at most
`1` (`sum_P_le_one`). The limit `Pmin = lim_k P_k` (the minimal transition function) is
sub-stochastic (`sum_Pmin_le_one`), satisfies the first-jump integral equation (`Pmin_eq`, by
dominated convergence), is continuous on `[0, ∞)` (`continuousOn_Pmin`), and solves the backward
Kolmogorov equation `∂ₜP(a, b) = −q(a) P(a, b) + ∑ᵢ rateᵢ(a) P(nextᵢ a, b)` (`hasDerivAt_Pmin`).
-/

open MeasureTheory intervalIntegral Set
open scoped BigOperators

namespace CRNT

/-- A continuous-time jump system with finitely many channels. -/
structure JumpSystem (α : Type*) where
  ι : Type
  [fintype : Fintype ι]
  rate : ι → α → ℝ
  rate_nonneg : ∀ i a, 0 ≤ rate i a
  next : ι → α → α

namespace JumpSystem

attribute [instance] JumpSystem.fintype

variable {α : Type*} [DecidableEq α] (J : JumpSystem α)

/-- The exit rate. -/
def q (a : α) : ℝ := ∑ i, J.rate i a

theorem q_nonneg (a : α) : 0 ≤ J.q a := Finset.sum_nonneg fun i _ => J.rate_nonneg i a

/-- The transition probabilities with at most `k` jumps. -/
noncomputable def P : ℕ → ℝ → α → α → ℝ
  | 0, t, a, b => Real.exp (-(J.q a * t)) * (if a = b then 1 else 0)
  | k + 1, t, a, b => Real.exp (-(J.q a * t)) * (if a = b then 1 else 0) +
      ∫ s in (0 : ℝ)..t, Real.exp (-(J.q a * s)) *
        ∑ i, J.rate i a * P k (t - s) (J.next i a) b

theorem P_zero (t : ℝ) (a b : α) :
    J.P 0 t a b = Real.exp (-(J.q a * t)) * (if a = b then 1 else 0) := rfl

theorem P_succ (k : ℕ) (t : ℝ) (a b : α) :
    J.P (k + 1) t a b = Real.exp (-(J.q a * t)) * (if a = b then 1 else 0) +
      ∫ s in (0 : ℝ)..t, Real.exp (-(J.q a * s)) *
        ∑ i, J.rate i a * J.P k (t - s) (J.next i a) b := rfl

theorem continuous_P (k : ℕ) : ∀ a b : α, Continuous fun t => J.P k t a b := by
  induction k with
  | zero => intro a b; simp only [P_zero]; fun_prop
  | succ k ih =>
      intro a b
      simp only [P_succ]
      refine Continuous.add (by fun_prop) ?_
      have hF : Continuous (Function.uncurry fun (t s : ℝ) => Real.exp (-(J.q a * s)) *
          ∑ i, J.rate i a * J.P k (t - s) (J.next i a) b) := by
        refine Continuous.mul (by fun_prop) (continuous_finset_sum _ fun i _ => ?_)
        exact continuous_const.mul ((ih (J.next i a) b).comp (continuous_fst.sub continuous_snd))
      exact continuous_parametric_intervalIntegral_of_continuous (a₀ := 0) hF continuous_id

theorem P_nonneg (k : ℕ) : ∀ (t : ℝ), 0 ≤ t → ∀ a b : α, 0 ≤ J.P k t a b := by
  induction k with
  | zero => intro t _ a b; simp only [P_zero]; split_ifs <;> positivity
  | succ k ih =>
      intro t ht a b
      simp only [P_succ]
      refine add_nonneg (by split_ifs <;> positivity) (integral_nonneg ht fun s hs => ?_)
      refine mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun i _ => ?_)
      exact mul_nonneg (J.rate_nonneg i a) (ih (t - s) (by linarith [hs.2]) _ _)

theorem integrable_term (k : ℕ) (t : ℝ) (a b : α) :
    IntervalIntegrable (fun s => Real.exp (-(J.q a * s)) *
      ∑ i, J.rate i a * J.P k (t - s) (J.next i a) b) volume 0 t := by
  apply Continuous.intervalIntegrable
  refine Continuous.mul (by fun_prop) (continuous_finset_sum _ fun i _ => ?_)
  exact continuous_const.mul ((J.continuous_P k (J.next i a) b).comp (continuous_const.sub
    continuous_id))

theorem P_mono (k : ℕ) : ∀ (t : ℝ), 0 ≤ t → ∀ a b : α, J.P k t a b ≤ J.P (k + 1) t a b := by
  induction k with
  | zero =>
      intro t ht a b
      rw [P_succ, P_zero]
      refine le_add_of_nonneg_right (integral_nonneg ht fun s hs => ?_)
      refine mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun i _ => ?_)
      exact mul_nonneg (J.rate_nonneg i a) (J.P_nonneg 0 (t - s) (by linarith [hs.2]) _ _)
  | succ k ih =>
      intro t ht a b
      rw [P_succ J (k + 1), P_succ J k]
      refine add_le_add le_rfl (integral_mono_on ht (J.integrable_term k t a b)
        (J.integrable_term (k + 1) t a b) fun s hs => ?_)
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_left (ih (t - s) (by linarith [hs.2]) _ _) (J.rate_nonneg i a)

/-- `∫₀ᵗ q e^{−q s} ds = 1 − e^{−q t}`. -/
theorem integral_exp_decay (c t : ℝ) :
    ∫ s in (0 : ℝ)..t, c * Real.exp (-(c * s)) = 1 - Real.exp (-(c * t)) := by
  have hd : ∀ s ∈ uIcc (0 : ℝ) t,
      HasDerivAt (fun s => -Real.exp (-(c * s))) (c * Real.exp (-(c * s))) s := by
    intro s _
    have hin : HasDerivAt (fun s : ℝ => -(c * s)) (-c) s := by
      have h0 := ((hasDerivAt_id s).const_mul c).neg
      have hf : (fun s : ℝ => -(c * s)) = -(fun y => c * id y) := by funext y; simp
      rw [hf]; convert h0 using 1; ring
    have := hin.exp.neg
    convert this using 1
    ring
  rw [integral_eq_sub_of_hasDerivAt hd (by apply Continuous.intervalIntegrable; fun_prop)]
  simp; ring

/-- **Sub-stochasticity.** Every finite row sum of `P_k(t)` is at most `1`. -/
theorem sum_P_le_one (k : ℕ) : ∀ (t : ℝ), 0 ≤ t → ∀ (a : α) (F : Finset α),
    ∑ b ∈ F, J.P k t a b ≤ 1 := by
  induction k with
  | zero =>
      intro t ht a F
      simp only [P_zero]
      rw [← Finset.mul_sum]
      have h1 : ∑ b ∈ F, (if a = b then (1 : ℝ) else 0) ≤ 1 := by
        rw [Finset.sum_ite_eq]; split_ifs <;> norm_num
      have h2 : Real.exp (-(J.q a * t)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [J.q_nonneg a])
      calc Real.exp (-(J.q a * t)) * ∑ b ∈ F, (if a = b then (1 : ℝ) else 0)
          ≤ Real.exp (-(J.q a * t)) * 1 :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ ≤ 1 := by linarith
  | succ k ih =>
      intro t ht a F
      simp only [P_succ]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [← intervalIntegral.integral_finsetSum fun b _ => J.integrable_term k t a b]
      have h1 : ∑ b ∈ F, (if a = b then (1 : ℝ) else 0) ≤ 1 := by
        rw [Finset.sum_ite_eq]; split_ifs <;> norm_num
      have hint : ∫ s in (0 : ℝ)..t, ∑ b ∈ F, Real.exp (-(J.q a * s)) *
          ∑ i, J.rate i a * J.P k (t - s) (J.next i a) b ≤
          ∫ s in (0 : ℝ)..t, J.q a * Real.exp (-(J.q a * s)) := by
        refine integral_mono_on ht ?_ (by apply Continuous.intervalIntegrable; fun_prop)
          fun s hs => ?_
        · have := IntervalIntegrable.sum F fun b _ => J.integrable_term k t a b
          convert this using 1
          funext s; simp [Finset.sum_apply]
        · calc ∑ b ∈ F, Real.exp (-(J.q a * s)) * ∑ i, J.rate i a * J.P k (t - s) (J.next i a) b
              = Real.exp (-(J.q a * s)) * ∑ i, J.rate i a *
                  ∑ b ∈ F, J.P k (t - s) (J.next i a) b := by
                simp only [Finset.mul_sum]; exact Finset.sum_comm
            _ ≤ Real.exp (-(J.q a * s)) * ∑ i, J.rate i a := by
                refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_)
                  (Real.exp_pos _).le
                calc J.rate i a * ∑ b ∈ F, J.P k (t - s) (J.next i a) b ≤ J.rate i a * 1 :=
                      mul_le_mul_of_nonneg_left (ih (t - s) (by linarith [hs.2]) _ F)
                        (J.rate_nonneg i a)
                  _ = J.rate i a := mul_one _
            _ = J.q a * Real.exp (-(J.q a * s)) := by unfold q; ring
      rw [integral_exp_decay] at hint
      have h2 : Real.exp (-(J.q a * t)) * ∑ b ∈ F, (if a = b then (1 : ℝ) else 0) ≤
          Real.exp (-(J.q a * t)) := by
        calc _ ≤ Real.exp (-(J.q a * t)) * 1 :=
              mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
          _ = _ := mul_one _
      linarith

/-! ## The minimal transition function and its integral equation -/

theorem P_le_one (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (a b : α) : J.P k t a b ≤ 1 := by
  simpa using J.sum_P_le_one k t ht a {b}

/-- The minimal transition function `P(t)(a, b) = lim_k P_k(t)(a, b)`. -/
noncomputable def Pmin (t : ℝ) (a b : α) : ℝ := ⨆ k, J.P k t a b

theorem tendsto_P (t : ℝ) (ht : 0 ≤ t) (a b : α) :
    Filter.Tendsto (fun k => J.P k t a b) Filter.atTop (nhds (J.Pmin t a b)) :=
  tendsto_atTop_ciSup (monotone_nat_of_le_succ fun k => J.P_mono k t ht a b)
    ⟨1, by rintro _ ⟨k, rfl⟩; exact J.P_le_one k t ht a b⟩

theorem Pmin_nonneg (t : ℝ) (ht : 0 ≤ t) (a b : α) : 0 ≤ J.Pmin t a b :=
  ge_of_tendsto' (J.tendsto_P t ht a b) fun k => J.P_nonneg k t ht a b

theorem Pmin_le_one (t : ℝ) (ht : 0 ≤ t) (a b : α) : J.Pmin t a b ≤ 1 :=
  le_of_tendsto' (J.tendsto_P t ht a b) fun k => J.P_le_one k t ht a b

/-- Finite row sums of the minimal transition function are at most `1`. -/
theorem sum_Pmin_le_one (t : ℝ) (ht : 0 ≤ t) (a : α) (F : Finset α) :
    ∑ b ∈ F, J.Pmin t a b ≤ 1 :=
  le_of_tendsto' (tendsto_finsetSum F fun b _ => J.tendsto_P t ht a b)
    fun k => J.sum_P_le_one k t ht a F

theorem measurable_Pmin (a b : α) : Measurable fun t => J.Pmin t a b :=
  Measurable.iSup fun k => (J.continuous_P k a b).measurable

/-- **Integral equation** for the minimal transition function. -/
theorem Pmin_eq (t : ℝ) (ht : 0 ≤ t) (a b : α) :
    J.Pmin t a b = Real.exp (-(J.q a * t)) * (if a = b then 1 else 0) +
      ∫ s in (0 : ℝ)..t, Real.exp (-(J.q a * s)) *
        ∑ i, J.rate i a * J.Pmin (t - s) (J.next i a) b := by
  have hlhs : Filter.Tendsto (fun k => J.P (k + 1) t a b) Filter.atTop
      (nhds (J.Pmin t a b)) := (J.tendsto_P t ht a b).comp (Filter.tendsto_add_atTop_nat 1)
  have hint : Filter.Tendsto (fun k => ∫ s in (0 : ℝ)..t, Real.exp (-(J.q a * s)) *
      ∑ i, J.rate i a * J.P k (t - s) (J.next i a) b) Filter.atTop
      (nhds (∫ s in (0 : ℝ)..t, Real.exp (-(J.q a * s)) *
        ∑ i, J.rate i a * J.Pmin (t - s) (J.next i a) b)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun s => Real.exp (-(J.q a * s)) * J.q a) ?_ ?_ ?_ ?_
    · refine Filter.Eventually.of_forall fun k => ?_
      rw [uIoc_of_le ht]
      exact ((J.integrable_term k t a b).1).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun k => Filter.Eventually.of_forall fun s hs => ?_
      rw [uIoc_of_le ht] at hs
      have hts : 0 ≤ t - s := by linarith [hs.2]
      have hsum_nn : 0 ≤ ∑ i, J.rate i a * J.P k (t - s) (J.next i a) b :=
        Finset.sum_nonneg fun i _ => mul_nonneg (J.rate_nonneg i a) (J.P_nonneg k _ hts _ _)
      have hsum_le : ∑ i, J.rate i a * J.P k (t - s) (J.next i a) b ≤ J.q a := by
        unfold q
        refine Finset.sum_le_sum fun i _ => ?_
        calc J.rate i a * J.P k (t - s) (J.next i a) b ≤ J.rate i a * 1 :=
              mul_le_mul_of_nonneg_left (J.P_le_one k _ hts _ _) (J.rate_nonneg i a)
          _ = J.rate i a := mul_one _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hsum_nn)]
      exact mul_le_mul_of_nonneg_left hsum_le (Real.exp_pos _).le
    · apply Continuous.intervalIntegrable; fun_prop
    · refine Filter.Eventually.of_forall fun s hs => ?_
      rw [uIoc_of_le ht] at hs
      have hts : 0 ≤ t - s := by linarith [hs.2]
      refine Filter.Tendsto.const_mul _ (tendsto_finsetSum _ fun i _ => ?_)
      exact (J.tendsto_P _ hts _ _).const_mul _
  have hrhs := hint.const_add (Real.exp (-(J.q a * t)) * (if a = b then 1 else 0))
  exact tendsto_nhds_unique hlhs (by simpa only [P_succ] using hrhs)

/-! ## The backward Kolmogorov equation -/

/-- The jump term `g(u) = ∑ᵢ rate_i(a) P(u)(next_i a, b)`. -/
noncomputable def jumpTerm (a b : α) (u : ℝ) : ℝ := ∑ i, J.rate i a * J.Pmin u (J.next i a) b

theorem measurable_jumpTerm (a b : α) : Measurable (J.jumpTerm a b) := by
  unfold jumpTerm
  exact Finset.measurable_sum _ fun i _ => (J.measurable_Pmin _ _).const_mul _

theorem jumpTerm_bound (a b : α) {u : ℝ} (hu : 0 ≤ u) : |J.jumpTerm a b u| ≤ J.q a := by
  have hnn : 0 ≤ J.jumpTerm a b u :=
    Finset.sum_nonneg fun i _ => mul_nonneg (J.rate_nonneg i a) (J.Pmin_nonneg u hu _ _)
  rw [abs_of_nonneg hnn]
  unfold jumpTerm q
  refine Finset.sum_le_sum fun i _ => ?_
  calc J.rate i a * J.Pmin u (J.next i a) b ≤ J.rate i a * 1 :=
        mul_le_mul_of_nonneg_left (J.Pmin_le_one u hu _ _) (J.rate_nonneg i a)
    _ = J.rate i a := mul_one _

/-- The integral equation after the substitution `u = t − s`. -/
theorem Pmin_eq_exp (t : ℝ) (ht : 0 ≤ t) (a b : α) :
    J.Pmin t a b = Real.exp (-(J.q a * t)) * ((if a = b then 1 else 0) +
      ∫ u in (0 : ℝ)..t, Real.exp (J.q a * u) * J.jumpTerm a b u) := by
  rw [J.Pmin_eq t ht a b]
  have hsub : ∫ s in (0 : ℝ)..t, Real.exp (-(J.q a * s)) *
      ∑ i, J.rate i a * J.Pmin (t - s) (J.next i a) b =
      ∫ u in (0 : ℝ)..t, Real.exp (-(J.q a * (t - u))) * J.jumpTerm a b u := by
    have := intervalIntegral.integral_comp_sub_left
      (fun u => Real.exp (-(J.q a * (t - u))) * J.jumpTerm a b u) (a := 0) (b := t) t
    simp only [sub_sub_cancel, sub_self, sub_zero] at this
    rw [← this]
    rfl
  rw [hsub]
  have hfac : ∀ u, Real.exp (-(J.q a * (t - u))) * J.jumpTerm a b u =
      Real.exp (-(J.q a * t)) * (Real.exp (J.q a * u) * J.jumpTerm a b u) := by
    intro u
    rw [← mul_assoc, ← Real.exp_add]; congr 2; ring
  simp only [hfac, intervalIntegral.integral_const_mul]
  ring

theorem integrableOn_jump (a b : α) (T : ℝ) (hT : 0 ≤ T) :
    IntegrableOn (fun u => Real.exp (J.q a * u) * J.jumpTerm a b u) (uIcc 0 T) := by
  rw [uIcc_of_le hT]
  refine Measure.integrableOn_of_bounded (M := Real.exp (J.q a * T) * J.q a)
    (measure_Icc_lt_top.ne) ?_ ?_
  · exact ((by fun_prop : Continuous fun u => Real.exp (J.q a * u)).measurable.mul
      (J.measurable_jumpTerm a b)).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall fun u hu => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul (Real.exp_le_exp.mpr ?_) (J.jumpTerm_bound a b hu.1) (abs_nonneg _)
      (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_left hu.2 (J.q_nonneg a)

/-- The minimal transition function is continuous on `[0, ∞)`. -/
theorem continuousOn_Pmin (a b : α) : ContinuousOn (fun t => J.Pmin t a b) (Ici 0) := by
  intro t ht
  have hT : (0 : ℝ) ≤ t + 1 := by linarith [mem_Ici.mp ht]
  have hH : ContinuousOn (fun x => ∫ u in (0 : ℝ)..x, Real.exp (J.q a * u) * J.jumpTerm a b u)
      (uIcc 0 (t + 1)) := intervalIntegral.continuousOn_primitive_interval (J.integrableOn_jump a b _ hT)
  have hR : ContinuousOn (fun x => Real.exp (-(J.q a * x)) * ((if a = b then 1 else 0) +
      ∫ u in (0 : ℝ)..x, Real.exp (J.q a * u) * J.jumpTerm a b u)) (uIcc 0 (t + 1)) :=
    ((by fun_prop : Continuous fun x => Real.exp (-(J.q a * x))).continuousOn).mul
      (continuousOn_const.add hH)
  have htmem : t ∈ uIcc (0 : ℝ) (t + 1) := by rw [uIcc_of_le hT]; exact ⟨mem_Ici.mp ht, by linarith⟩
  have heq : EqOn (fun x => J.Pmin x a b) (fun x => Real.exp (-(J.q a * x)) *
      ((if a = b then 1 else 0) + ∫ u in (0 : ℝ)..x, Real.exp (J.q a * u) * J.jumpTerm a b u))
      (Ici 0) := fun x hx => J.Pmin_eq_exp x hx a b
  refine ((hR t htmem).mono_of_mem_nhdsWithin ?_).congr (fun x hx => heq hx) (heq ht)
  rw [uIcc_of_le hT]
  exact Filter.mem_of_superset (inter_mem_nhdsWithin (Ici 0) (Iio_mem_nhds (by linarith : t < t + 1)))
    fun x hx => ⟨mem_Ici.mp hx.1, le_of_lt hx.2⟩

/-- **Backward Kolmogorov equation** for the minimal transition function. -/
theorem hasDerivAt_Pmin (t : ℝ) (ht : 0 < t) (a b : α) :
    HasDerivAt (fun τ => J.Pmin τ a b)
      (-J.q a * J.Pmin t a b + ∑ i, J.rate i a * J.Pmin t (J.next i a) b) t := by
  have hgcont : ContinuousAt (fun u => Real.exp (J.q a * u) * J.jumpTerm a b u) t := by
    have hg : ContinuousOn (J.jumpTerm a b) (Ici 0) := by
      unfold jumpTerm
      exact continuousOn_finsetSum _ fun i _ => continuousOn_const.mul (J.continuousOn_Pmin _ _)
    exact ((by fun_prop : Continuous fun u => Real.exp (J.q a * u)).continuousAt).mul
      (hg.continuousAt (Ici_mem_nhds ht))
  have hH : HasDerivAt (fun x => ∫ u in (0 : ℝ)..x, Real.exp (J.q a * u) * J.jumpTerm a b u)
      (Real.exp (J.q a * t) * J.jumpTerm a b t) t :=
    intervalIntegral.integral_hasDerivAt_right
      ((J.integrableOn_jump a b t ht.le).intervalIntegrable)
      (((by fun_prop : Continuous fun u => Real.exp (J.q a * u)).measurable.mul
        (J.measurable_jumpTerm a b)).stronglyMeasurable.stronglyMeasurableAtFilter) hgcont
  have hE : HasDerivAt (fun x => Real.exp (-(J.q a * x))) (Real.exp (-(J.q a * t)) * -(J.q a)) t := by
    have hin : HasDerivAt (fun s : ℝ => -(J.q a * s)) (-(J.q a)) t := by
      have h0 := ((hasDerivAt_id t).const_mul (J.q a)).neg
      have hf : (fun s : ℝ => -(J.q a * s)) = -(fun y => J.q a * id y) := by funext y; simp
      rw [hf]; convert h0 using 1; ring
    exact hin.exp
  have hR := hE.mul (hH.const_add (if a = b then (1 : ℝ) else 0))
  have heq : (fun τ => J.Pmin τ a b) =ᶠ[nhds t] fun x => Real.exp (-(J.q a * x)) *
      ((if a = b then 1 else 0) + ∫ u in (0 : ℝ)..x, Real.exp (J.q a * u) * J.jumpTerm a b u) := by
    filter_upwards [Ioi_mem_nhds ht] with x hx
    exact J.Pmin_eq_exp x (le_of_lt hx) a b
  refine (hR.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [J.Pmin_eq_exp t ht.le a b]
  have hexp : Real.exp (-(J.q a * t)) * Real.exp (J.q a * t) = 1 := by
    rw [← Real.exp_add]; simp
  simp only [jumpTerm]
  linear_combination (∑ i, J.rate i a * J.Pmin t (J.next i a) b) * hexp

end JumpSystem

end CRNT
