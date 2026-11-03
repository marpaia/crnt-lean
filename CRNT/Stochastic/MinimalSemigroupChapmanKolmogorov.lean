import CRNT.Stochastic.MinimalSemigroupStochastic
import CRNT.Stochastic.MinimalSemigroupNetwork

/-!
# The Chapman–Kolmogorov equation for the minimal transition function

The transition probabilities with exactly `k` jumps are

`E₀(t)(a, b) = e^{−q(a) t} [a = b]`,
`E_{k+1}(t)(a, b) = ∫₀ᵗ e^{−q(a) s} ∑ᵢ rate_i(a) E_k(t − s)(next_i a, b) ds`,

so that `P_k = ∑_{j ≤ k} E_j` (`P_eq_sum_Pexact`). Splitting the first-jump time at `t` gives
the convolution identity `E_k(t + s) = ∑_{j ≤ k} E_j(t) E_{k − j}(s)` (`Pexact_add`), and summing
over `k` gives the Chapman–Kolmogorov equation for the minimal transition function:

`P(t + s)(a, b) = ∑_c P(t)(a, c) P(s)(c, b)`  (`hasSum_Pmin_add`),

with mass-action form `Network.hasSum_transition_add`. No conservation or boundedness assumption
is needed: the identity holds for the (possibly sub-stochastic) minimal solution.
-/

open MeasureTheory intervalIntegral Set Filter
open scoped BigOperators Topology ENNReal

namespace CRNT

namespace JumpSystem

variable {α : Type*} [DecidableEq α] (J : JumpSystem α)

/-- The transition probabilities with exactly `k` jumps. -/
noncomputable def Pexact : ℕ → ℝ → α → α → ℝ
  | 0, t, a, b => Real.exp (-(J.q a * t)) * (if a = b then 1 else 0)
  | k + 1, t, a, b => ∫ s in (0 : ℝ)..t, Real.exp (-(J.q a * s)) *
        ∑ i, J.rate i a * Pexact k (t - s) (J.next i a) b

theorem Pexact_zero (t : ℝ) (a b : α) :
    J.Pexact 0 t a b = Real.exp (-(J.q a * t)) * (if a = b then 1 else 0) := rfl

theorem Pexact_succ (k : ℕ) (t : ℝ) (a b : α) :
    J.Pexact (k + 1) t a b = ∫ s in (0 : ℝ)..t, Real.exp (-(J.q a * s)) *
        ∑ i, J.rate i a * J.Pexact k (t - s) (J.next i a) b := rfl

theorem continuous_Pexact (k : ℕ) : ∀ a b : α, Continuous fun t => J.Pexact k t a b := by
  induction k with
  | zero => intro a b; simp only [Pexact_zero]; fun_prop
  | succ k ih =>
      intro a b
      simp only [Pexact_succ]
      have hF : Continuous (Function.uncurry fun (t s : ℝ) => Real.exp (-(J.q a * s)) *
          ∑ i, J.rate i a * J.Pexact k (t - s) (J.next i a) b) := by
        refine Continuous.mul (by fun_prop) (continuous_finsetSum _ fun i _ => ?_)
        exact continuous_const.mul ((ih (J.next i a) b).comp (continuous_fst.sub continuous_snd))
      exact continuous_parametric_intervalIntegral_of_continuous (a₀ := 0) hF continuous_id

theorem continuous_Pexact_term (k : ℕ) (t : ℝ) (a b : α) :
    Continuous (fun s => Real.exp (-(J.q a * s)) *
      ∑ i, J.rate i a * J.Pexact k (t - s) (J.next i a) b) := by
  refine Continuous.mul (by fun_prop) (continuous_finsetSum _ fun i _ => ?_)
  exact continuous_const.mul ((J.continuous_Pexact k (J.next i a) b).comp (continuous_const.sub
    continuous_id))

theorem Pexact_nonneg (k : ℕ) : ∀ (t : ℝ), 0 ≤ t → ∀ a b : α, 0 ≤ J.Pexact k t a b := by
  induction k with
  | zero => intro t _ a b; simp only [Pexact_zero]; split_ifs <;> positivity
  | succ k ih =>
      intro t ht a b
      simp only [Pexact_succ]
      refine integral_nonneg ht fun s hs => ?_
      refine mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun i _ => ?_)
      exact mul_nonneg (J.rate_nonneg i a) (ih (t - s) (by linarith [hs.2]) _ _)

/-- `P_k` is the sum of the exact-jump terms `E_j`, `j ≤ k`. -/
theorem P_eq_sum_Pexact (k : ℕ) : ∀ (t : ℝ) (a b : α),
    J.P k t a b = ∑ j ∈ Finset.range (k + 1), J.Pexact j t a b := by
  induction k with
  | zero => intro t a b; simp [P_zero, Pexact_zero]
  | succ k ih =>
      intro t a b
      rw [P_succ, Finset.sum_range_succ', Pexact_zero, add_comm]
      congr 1
      have h : ∀ s, Real.exp (-(J.q a * s)) * ∑ i, J.rate i a * J.P k (t - s) (J.next i a) b =
          ∑ j ∈ Finset.range (k + 1), Real.exp (-(J.q a * s)) *
            ∑ i, J.rate i a * J.Pexact j (t - s) (J.next i a) b := by
        intro s
        simp only [ih, Finset.mul_sum]
        rw [Finset.sum_comm]
      simp only [h]
      rw [intervalIntegral.integral_finsetSum fun j _ =>
        (J.continuous_Pexact_term j t a b).intervalIntegrable 0 t]
      rfl

theorem Pexact_eq_zero_of_not_mem (k : ℕ) :
    ∀ (t : ℝ) (a b : α), b ∉ J.reachK k a → J.Pexact k t a b = 0 := by
  induction k with
  | zero =>
      intro t a b hb
      have : a ≠ b := fun h => hb (by simp [reachK, h])
      simp [Pexact_zero, this]
  | succ k ih =>
      intro t a b hb
      rw [Pexact_succ]
      have hzero : ∀ s, Real.exp (-(J.q a * s)) *
          ∑ i, J.rate i a * J.Pexact k (t - s) (J.next i a) b = 0 := by
        intro s
        rw [Finset.sum_eq_zero fun i _ => by
          rw [ih _ _ _ fun h => hb (J.reachK_next_subset k a i h), mul_zero], mul_zero]
      simp [hzero]

theorem reachK_subset_succ (k : ℕ) : ∀ a : α, J.reachK k a ⊆ J.reachK (k + 1) a := by
  induction k with
  | zero => intro a; simp [reachK]
  | succ k ih =>
      intro a b hb
      rw [reachK, Finset.mem_insert, Finset.mem_biUnion] at hb
      rw [reachK, Finset.mem_insert, Finset.mem_biUnion]
      rcases hb with hb | ⟨i, _, hi⟩
      · exact Or.inl hb
      · exact Or.inr ⟨i, Finset.mem_univ _, ih _ hi⟩

theorem reachK_mono {j k : ℕ} (h : j ≤ k) (a : α) : J.reachK j a ⊆ J.reachK k a := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (J.reachK_subset_succ _ a)

theorem sum_Pexact_zero_mul (t : ℝ) (a : α) (F : Finset α) (haF : a ∈ F) (g : α → ℝ) :
    ∑ c ∈ F, J.Pexact 0 t a c * g c = Real.exp (-(J.q a * t)) * g a := by
  rw [Finset.sum_eq_single_of_mem a haF fun c _ hca => by simp [Pexact_zero, Ne.symm hca]]
  simp [Pexact_zero]

/-- **Convolution identity** for the exact-jump terms: splitting at time `t`,
`E_k(t + s)(a, b) = ∑_{j ≤ k} ∑_c E_j(t)(a, c) E_{k − j}(s)(c, b)`, for any finite set of
intermediate states containing the states reachable from `a` in at most `k` jumps. -/
theorem Pexact_add (k : ℕ) : ∀ (t s : ℝ), 0 ≤ t → ∀ (a b : α) (F : Finset α),
    J.reachK k a ⊆ F →
    J.Pexact k (t + s) a b =
      ∑ j ∈ Finset.range (k + 1), ∑ c ∈ F, J.Pexact j t a c * J.Pexact (k - j) s c b := by
  induction k with
  | zero =>
      intro t s _ a b F hF
      have haF : a ∈ F := hF (J.mem_reachK_self 0 a)
      simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.sub_zero]
      rw [J.sum_Pexact_zero_mul t a F haF, Pexact_zero, Pexact_zero,
        show -(J.q a * (t + s)) = -(J.q a * t) + -(J.q a * s) by ring, Real.exp_add]
      ring
  | succ k ih =>
      intro t s ht a b F hF
      have haF : a ∈ F := hF (J.mem_reachK_self (k + 1) a)
      have hFi : ∀ i, J.reachK k (J.next i a) ⊆ F :=
        fun i => (J.reachK_next_subset k a i).trans hF
      have hfc := J.continuous_Pexact_term k (t + s) a b
      rw [Pexact_succ, Finset.sum_range_succ', Nat.sub_zero,
        J.sum_Pexact_zero_mul t a F haF,
        ← intervalIntegral.integral_add_adjacent_intervals (b := t)
          (hfc.intervalIntegrable _ _) (hfc.intervalIntegrable _ _)]
      congr 1
      · -- first jump before time `t`
        have hpt : ∀ u ∈ uIcc (0 : ℝ) t, Real.exp (-(J.q a * u)) *
            ∑ i, J.rate i a * J.Pexact k (t + s - u) (J.next i a) b =
            ∑ j ∈ Finset.range (k + 1), ∑ c ∈ F,
              (Real.exp (-(J.q a * u)) * ∑ i, J.rate i a * J.Pexact j (t - u) (J.next i a) c) *
                J.Pexact (k - j) s c b := by
          intro u hu
          rw [uIcc_of_le ht] at hu
          have hih : ∀ i, J.Pexact k (t + s - u) (J.next i a) b =
              ∑ j ∈ Finset.range (k + 1), ∑ c ∈ F,
                J.Pexact j (t - u) (J.next i a) c * J.Pexact (k - j) s c b := by
            intro i
            rw [show t + s - u = (t - u) + s by ring]
            exact ih (t - u) s (by linarith [hu.2]) _ b F (hFi i)
          simp only [hih, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun c _ => ?_
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
        rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_finsetSum]
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [intervalIntegral.integral_finsetSum]
          · refine Finset.sum_congr rfl fun c _ => ?_
            rw [intervalIntegral.integral_mul_const, ← Pexact_succ, Nat.add_sub_add_right]
          · intro c _
            exact ((J.continuous_Pexact_term j t a c).mul continuous_const).intervalIntegrable _ _
        · intro j _
          exact (continuous_finsetSum _ fun c _ =>
            (J.continuous_Pexact_term j t a c).mul continuous_const).intervalIntegrable _ _
      · -- first jump after time `t`
        have hshift := intervalIntegral.integral_comp_add_left (fun u => Real.exp (-(J.q a * u)) *
            ∑ i, J.rate i a * J.Pexact k (t + s - u) (J.next i a) b) t (a := 0) (b := s)
        rw [add_zero] at hshift
        rw [← hshift, Pexact_succ, ← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun v _ => ?_
        rw [show t + s - (t + v) = s - v by ring,
          show -(J.q a * (t + v)) = -(J.q a * t) + -(J.q a * v) by ring, Real.exp_add]
        ring

/-- The minimal transition function is the sum of the exact-jump terms. -/
theorem hasSum_Pexact (t : ℝ) (ht : 0 ≤ t) (a b : α) :
    HasSum (fun j => J.Pexact j t a b) (J.Pmin t a b) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun j => J.Pexact_nonneg j t ht a b),
    ← Filter.tendsto_add_atTop_iff_nat 1]
  simpa [← J.P_eq_sum_Pexact] using J.tendsto_P t ht a b

theorem ofReal_Pmin (t : ℝ) (ht : 0 ≤ t) (a b : α) :
    ENNReal.ofReal (J.Pmin t a b) = ∑' j, ENNReal.ofReal (J.Pexact j t a b) := by
  rw [← (J.hasSum_Pexact t ht a b).tsum_eq, ENNReal.ofReal_tsum_of_nonneg
    (fun j => J.Pexact_nonneg j t ht a b) (J.hasSum_Pexact t ht a b).summable]

/-- The Chapman–Kolmogorov identity in `ℝ≥0∞`. -/
theorem tsum_ofReal_Pmin_mul (t s : ℝ) (ht : 0 ≤ t) (hs : 0 ≤ s) (a b : α) :
    ∑' c, ENNReal.ofReal (J.Pmin t a c * J.Pmin s c b) = ENNReal.ofReal (J.Pmin (t + s) a b) := by
  have hG : ∀ j l, ∑' c, ENNReal.ofReal (J.Pexact j t a c) * ENNReal.ofReal (J.Pexact l s c b) =
      ENNReal.ofReal (∑ c ∈ J.reachK (j + l) a, J.Pexact j t a c * J.Pexact l s c b) := by
    intro j l
    rw [tsum_eq_sum (s := J.reachK (j + l) a) fun c hc => by
      rw [J.Pexact_eq_zero_of_not_mem j t a c fun h => hc (J.reachK_mono (Nat.le_add_right j l) a h),
        ENNReal.ofReal_zero, zero_mul]]
    rw [ENNReal.ofReal_sum_of_nonneg fun c _ =>
      mul_nonneg (J.Pexact_nonneg j t ht a c) (J.Pexact_nonneg l s hs c b)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [ENNReal.ofReal_mul (J.Pexact_nonneg j t ht a c)]
  calc ∑' c, ENNReal.ofReal (J.Pmin t a c * J.Pmin s c b)
      = ∑' c, ∑' j, ∑' l,
          ENNReal.ofReal (J.Pexact j t a c) * ENNReal.ofReal (J.Pexact l s c b) := by
        refine tsum_congr fun c => ?_
        rw [ENNReal.ofReal_mul (J.Pmin_nonneg t ht a c), J.ofReal_Pmin t ht, J.ofReal_Pmin s hs,
          ← ENNReal.tsum_mul_right]
        refine tsum_congr fun j => ?_
        rw [← ENNReal.tsum_mul_left]
    _ = ∑' j, ∑' l, ∑' c,
          ENNReal.ofReal (J.Pexact j t a c) * ENNReal.ofReal (J.Pexact l s c b) := by
        rw [ENNReal.tsum_comm]
        refine tsum_congr fun j => ?_
        rw [ENNReal.tsum_comm]
    _ = ∑' p : ℕ × ℕ, ENNReal.ofReal
          (∑ c ∈ J.reachK (p.1 + p.2) a, J.Pexact p.1 t a c * J.Pexact p.2 s c b) := by
        rw [ENNReal.tsum_prod']
        simp only [hG]
    _ = ∑' k, ∑ p ∈ Finset.antidiagonal k, ENNReal.ofReal
          (∑ c ∈ J.reachK (p.1 + p.2) a, J.Pexact p.1 t a c * J.Pexact p.2 s c b) := by
        rw [← (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd).tsum_eq, ENNReal.tsum_sigma']
        refine tsum_congr fun k => ?_
        exact (Finset.tsum_subtype (Finset.antidiagonal k) (fun p : ℕ × ℕ => ENNReal.ofReal
          (∑ c ∈ J.reachK (p.1 + p.2) a, J.Pexact p.1 t a c * J.Pexact p.2 s c b)))
    _ = ∑' k, ENNReal.ofReal (J.Pexact k (t + s) a b) := by
        refine tsum_congr fun k => ?_
        rw [J.Pexact_add k t s ht a b (J.reachK k a) le_rfl,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
          ENNReal.ofReal_sum_of_nonneg fun j _ => Finset.sum_nonneg fun c _ =>
            mul_nonneg (J.Pexact_nonneg j t ht a c) (J.Pexact_nonneg _ s hs c b)]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_range] at hj
        simp only [Nat.add_sub_cancel' (Nat.lt_succ_iff.mp hj)]
    _ = ENNReal.ofReal (J.Pmin (t + s) a b) := (J.ofReal_Pmin (t + s) (add_nonneg ht hs) a b).symm

/-- **Chapman–Kolmogorov equation** for the minimal transition function:
`P(t + s)(a, b) = ∑_c P(t)(a, c) P(s)(c, b)` for `t, s ≥ 0`. -/
theorem hasSum_Pmin_add {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (a b : α) :
    HasSum (fun c => J.Pmin t a c * J.Pmin s c b) (J.Pmin (t + s) a b) := by
  have hnn : ∀ c, 0 ≤ J.Pmin t a c * J.Pmin s c b :=
    fun c => mul_nonneg (J.Pmin_nonneg t ht a c) (J.Pmin_nonneg s hs c b)
  have hto : ∀ c, (ENNReal.ofReal (J.Pmin t a c * J.Pmin s c b)).toReal =
      J.Pmin t a c * J.Pmin s c b := fun c => ENNReal.toReal_ofReal (hnn c)
  have h := J.tsum_ofReal_Pmin_mul t s ht hs a b
  have hfin : ∑' c, ENNReal.ofReal (J.Pmin t a c * J.Pmin s c b) ≠ ∞ := by
    rw [h]; exact ENNReal.ofReal_ne_top
  have hsum := ENNReal.summable_toReal hfin
  simp only [hto] at hsum
  have htsum : ∑' c, J.Pmin t a c * J.Pmin s c b = J.Pmin (t + s) a b := by
    have := ENNReal.tsum_toReal_eq
      (f := fun c => ENNReal.ofReal (J.Pmin t a c * J.Pmin s c b)) fun _ => ENNReal.ofReal_ne_top
    simp only [hto] at this
    rw [← this, h, ENNReal.toReal_ofReal (J.Pmin_nonneg _ (add_nonneg ht hs) a b)]
  exact htsum ▸ hsum.hasSum

theorem Pmin_add {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (a b : α) :
    J.Pmin (t + s) a b = ∑' c, J.Pmin t a c * J.Pmin s c b :=
  (J.hasSum_Pmin_add ht hs a b).tsum_eq.symm

end JumpSystem

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Chapman–Kolmogorov equation** for stochastic mass-action kinetics. -/
theorem hasSum_transition_add (N : Network S) (κ : RateConstants N) {t s : ℝ} (ht : 0 ≤ t)
    (hs : 0 ≤ s) (n m : S → ℕ) :
    HasSum (fun l => N.transition κ t n l * N.transition κ s l m) (N.transition κ (t + s) n m) :=
  (N.jumpSystem κ).hasSum_Pmin_add ht hs n m

end Network

end CRNT
