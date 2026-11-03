import CRNT.Theorems.DeficiencyZero.Characterization
import CRNT.Theorems.DeficiencyZero.PositiveKernel
import CRNT.Equilibria.ComplexBalanceStructure
import CRNT.Equilibria.Wegscheider
import CRNT.Deficiency.KernelDimension

/-!
# Horn's characterization of unconditional complex balancing

**Theorem (Horn 1972).**  A reaction network admits a positive complex-balanced equilibrium for
*every* choice of positive rate constants if and only if it is weakly reversible and has
deficiency zero.

The "if" direction is the existence half of the deficiency-zero theorem
(`Network.exists_isComplexBalanced`).  This module proves the converse,
`weaklyReversible_and_deficiencyZero_of_forall_complexBalanced`, and packages both directions
as `forall_complexBalanced_iff`.

**Proof of the converse.**  One positive complex-balanced state already forces weak
reversibility.  For deficiency zero, take `d` in the deficiency subspace `ker Y ∩ im ∂`, a
positive circulation `c` (in-flow equals out-flow at every complex), and the rates
`κ r = c r · exp (-d (source r))`.  If `x > 0` is complex balanced for `κ`, put
`g y = ⟨y, log x⟩ - d y` and `ρ = exp ∘ g`, so `κ r · x^{source r} = c r · ρ (source r)`.
Complex balance and the circulation identity give

  `∑ r, c r ρ_s (g_s - g_t) = 0 = ∑ r, c r (ρ_s - ρ_t)`,

while `e^a (a - b) ≥ e^a - e^b` termwise with equality only at `a = b`.  Hence `g` takes the
same value at the source and target of every reaction, so
`‖d‖² = ∑ r, v r (d_t - d_s) = ⟪Y ∂ v, log x⟫ = ⟪Y d, log x⟫ = 0` for `d = ∂ v`.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Regrouping a sum over reactions by target complex. -/
theorem sum_mul_targetIdx (N : Network S) (F : N.R → ℝ) (h : N.ComplexIdx → ℝ) :
    ∑ r : N.R, F r * h (N.targetIdx r) =
      ∑ y : N.ComplexIdx, h y * ∑ r : N.R, (if N.targetIdx r = y then F r else 0) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp [mul_comm]

/-- Regrouping a sum over reactions by source complex. -/
theorem sum_mul_sourceIdx (N : Network S) (F : N.R → ℝ) (h : N.ComplexIdx → ℝ) :
    ∑ r : N.R, F r * h (N.sourceIdx r) =
      ∑ y : N.ComplexIdx, h y * ∑ r : N.R, (if N.sourceIdx r = y then F r else 0) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp [mul_comm]

/-- **Positive circulations.**  A weakly reversible network carries a strictly positive flux
vector whose in-flow equals its out-flow at every complex. -/
theorem exists_positive_circulation (N : Network S) (hwr : N.WeaklyReversible) :
    ∃ c : N.R → ℝ, (∀ r, 0 < c r) ∧ ∀ y : N.ComplexIdx,
      ∑ r : N.R, (if N.targetIdx r = y then c r else 0) =
        ∑ r : N.R, (if N.sourceIdx r = y then c r else 0) := by
  let κ₁ : N.RateConstants := ⟨fun _ => 1, fun _ => one_pos⟩
  obtain ⟨b, hb, hk⟩ := PositiveKernel.weaklyReversible_exists_positive_kernelVector N hwr κ₁
  refine ⟨fun r => b (N.sourceIdx r), fun r => hb _, fun y => ?_⟩
  have h := congrFun hk y
  change ∑ r : N.R, κ₁.k r * b (N.sourceIdx r) *
      ((if N.targetIdx r = y then 1 else 0) - (if N.sourceIdx r = y then 1 else 0)) = 0 at h
  have hsplit : ∀ r : N.R, κ₁.k r * b (N.sourceIdx r) *
      ((if N.targetIdx r = y then 1 else 0) - (if N.sourceIdx r = y then 1 else 0)) =
      (if N.targetIdx r = y then b (N.sourceIdx r) else 0) -
        (if N.sourceIdx r = y then b (N.sourceIdx r) else 0) := by
    intro r
    change 1 * b (N.sourceIdx r) * _ = _
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun r _ => hsplit r), Finset.sum_sub_distrib] at h
  linarith

/-- `e^a (a - b) ≥ e^a - e^b`, with equality only when `a = b`. -/
theorem exp_mul_sub_ge (a b : ℝ) :
    Real.exp a - Real.exp b ≤ Real.exp a * (a - b) ∧
      (Real.exp a * (a - b) = Real.exp a - Real.exp b → a = b) := by
  have hexp : Real.exp b = Real.exp a * Real.exp (b - a) := by
    rw [← Real.exp_add]; ring_nf
  have ha := Real.exp_pos a
  refine ⟨?_, fun heq => ?_⟩
  · have := Real.add_one_le_exp (b - a)
    rw [hexp]; nlinarith
  · by_contra hne
    have hlt := Real.add_one_lt_exp (sub_ne_zero.mpr (Ne.symm hne))
    rw [hexp] at heq
    nlinarith

/-- **Horn's converse to the deficiency-zero theorem.** -/
theorem weaklyReversible_and_deficiencyZero_of_forall_complexBalanced (N : Network S)
    (hall : ∀ κ : N.RateConstants, ∃ x : Concentration S,
      x.Positive ∧ N.IsComplexBalanced κ x) :
    N.WeaklyReversible ∧ N.DeficiencyZero := by
  have hwr : N.WeaklyReversible := by
    obtain ⟨x, hx, hcb⟩ := hall ⟨fun _ => 1, fun _ => one_pos⟩
    exact N.weaklyReversible_of_positive_complexBalanced _ hx hcb
  refine ⟨hwr, ?_⟩
  rw [N.deficiencyZero_iff_deficiencySubspace_eq_bot, eq_bot_iff]
  intro d hd
  rw [Submodule.mem_bot]
  obtain ⟨hdY, v, hv⟩ : N.complexMap d = 0 ∧ ∃ v, N.incidenceMap v = d := by
    have h := hd
    simp only [deficiencySubspace, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_range]
      at h
    exact h
  obtain ⟨c, hc, hcirc⟩ := N.exists_positive_circulation hwr
  let κ : N.RateConstants :=
    ⟨fun r => c r * Real.exp (-d (N.sourceIdx r)), fun r => mul_pos (hc r) (Real.exp_pos _)⟩
  obtain ⟨x, hx, hcb⟩ := hall κ
  set g : N.ComplexIdx → ℝ := fun y => (∑ s : S, (y.val s : ℝ) * Real.log (x s)) - d y with hg
  set ρ : N.ComplexIdx → ℝ := fun y => Real.exp (g y) with hρ
  -- the mass-action rates in the new variables
  have hrate : ∀ r : N.R, N.massActionRate κ r x = c r * ρ (N.sourceIdx r) := by
    intro r
    have hmono : (N.reaction r).source.massActionMonomial x =
        Real.exp (∑ s : S, ((N.sourceIdx r).val s : ℝ) * Real.log (x s)) := by
      rw [← log_massActionMonomial_eq hx, Real.exp_log (Complex.massActionMonomial_pos hx _)]
      rfl
    simp only [massActionRate, hmono, hρ, hg]
    change c r * Real.exp (-d (N.sourceIdx r)) * _ = _
    rw [mul_assoc, ← Real.exp_add]; ring_nf
  -- complex balance in the new variables
  have hbal : ∀ y : N.ComplexIdx,
      ∑ r : N.R, (if N.targetIdx r = y then c r * ρ (N.sourceIdx r) else 0) =
        ∑ r : N.R, (if N.sourceIdx r = y then c r * ρ (N.sourceIdx r) else 0) := by
    intro y
    have h := hcb y.val y.property
    simp only [inflow, outflow] at h
    have ht : ∀ r : N.R, (if (N.reaction r).target = y.val then N.massActionRate κ r x else 0) =
        (if N.targetIdx r = y then c r * ρ (N.sourceIdx r) else 0) := by
      intro r
      have : ((N.reaction r).target = y.val) ↔ (N.targetIdx r = y) :=
        ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
      by_cases hh : N.targetIdx r = y
      · rw [if_pos (this.mpr hh), if_pos hh, hrate]
      · rw [if_neg (fun h' => hh (this.mp h')), if_neg hh]
    have hs : ∀ r : N.R, (if (N.reaction r).source = y.val then N.massActionRate κ r x else 0) =
        (if N.sourceIdx r = y then c r * ρ (N.sourceIdx r) else 0) := by
      intro r
      have : ((N.reaction r).source = y.val) ↔ (N.sourceIdx r = y) :=
        ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
      by_cases hh : N.sourceIdx r = y
      · rw [if_pos (this.mpr hh), if_pos hh, hrate]
      · rw [if_neg (fun h' => hh (this.mp h')), if_neg hh]
    rw [Finset.sum_congr rfl (fun r _ => ht r), Finset.sum_congr rfl (fun r _ => hs r)] at h
    exact h
  -- the two sums vanish
  have hA : ∑ r : N.R, c r * ρ (N.sourceIdx r) * (g (N.sourceIdx r) - g (N.targetIdx r)) = 0 := by
    have e1 := N.sum_mul_sourceIdx (fun r => c r * ρ (N.sourceIdx r)) g
    have e2 := N.sum_mul_targetIdx (fun r => c r * ρ (N.sourceIdx r)) g
    have : ∑ r : N.R, c r * ρ (N.sourceIdx r) * (g (N.sourceIdx r) - g (N.targetIdx r)) =
        ∑ r : N.R, c r * ρ (N.sourceIdx r) * g (N.sourceIdx r) -
          ∑ r : N.R, c r * ρ (N.sourceIdx r) * g (N.targetIdx r) := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun r _ => by ring
    rw [this, e1, e2]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_eq_zero fun y _ => by rw [hbal y]; ring
  have hB : ∑ r : N.R, c r * (ρ (N.sourceIdx r) - ρ (N.targetIdx r)) = 0 := by
    have e1 := N.sum_mul_sourceIdx c ρ
    have e2 := N.sum_mul_targetIdx c ρ
    have : ∑ r : N.R, c r * (ρ (N.sourceIdx r) - ρ (N.targetIdx r)) =
        ∑ r : N.R, c r * ρ (N.sourceIdx r) - ∑ r : N.R, c r * ρ (N.targetIdx r) := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun r _ => by ring
    rw [this, e1, e2, ← Finset.sum_sub_distrib]
    exact Finset.sum_eq_zero fun y _ => by rw [hcirc y]; ring
  -- termwise equality
  have hterm : ∀ r : N.R, g (N.sourceIdx r) = g (N.targetIdx r) := by
    have hnn : ∀ r ∈ (Finset.univ : Finset N.R), 0 ≤ c r * (ρ (N.sourceIdx r) *
        (g (N.sourceIdx r) - g (N.targetIdx r)) - (ρ (N.sourceIdx r) - ρ (N.targetIdx r))) := by
      intro r _
      exact mul_nonneg (hc r).le (by
        have := (exp_mul_sub_ge (g (N.sourceIdx r)) (g (N.targetIdx r))).1
        simp only [hρ]; linarith)
    have hsum : ∑ r : N.R, c r * (ρ (N.sourceIdx r) *
        (g (N.sourceIdx r) - g (N.targetIdx r)) - (ρ (N.sourceIdx r) - ρ (N.targetIdx r))) = 0 := by
      have : ∑ r : N.R, c r * (ρ (N.sourceIdx r) *
          (g (N.sourceIdx r) - g (N.targetIdx r)) - (ρ (N.sourceIdx r) - ρ (N.targetIdx r))) =
          ∑ r : N.R, c r * ρ (N.sourceIdx r) * (g (N.sourceIdx r) - g (N.targetIdx r)) -
            ∑ r : N.R, c r * (ρ (N.sourceIdx r) - ρ (N.targetIdx r)) := by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun r _ => by ring
      rw [this, hA, hB, sub_zero]
    intro r
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum r (Finset.mem_univ r)
    have h1 : ρ (N.sourceIdx r) * (g (N.sourceIdx r) - g (N.targetIdx r)) =
        ρ (N.sourceIdx r) - ρ (N.targetIdx r) := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h (hc r).ne'
      · linarith
    exact (exp_mul_sub_ge (g (N.sourceIdx r)) (g (N.targetIdx r))).2 (by simpa [hρ] using h1)
  -- `‖d‖² = 0`
  have hdd : ∑ y : N.ComplexIdx, d y * d y = 0 := by
    have hdiff : ∀ r : N.R, d (N.targetIdx r) - d (N.sourceIdx r) =
        ∑ s : S, (((N.targetIdx r).val s : ℝ) - ((N.sourceIdx r).val s : ℝ)) * Real.log (x s) := by
      intro r
      have := hterm r
      simp only [hg] at this
      have hsum : ∑ s : S, (((N.targetIdx r).val s : ℝ) - ((N.sourceIdx r).val s : ℝ)) *
          Real.log (x s) = ∑ s : S, ((N.targetIdx r).val s : ℝ) * Real.log (x s) -
            ∑ s : S, ((N.sourceIdx r).val s : ℝ) * Real.log (x s) := by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun s _ => by ring
      rw [hsum]; linarith
    calc ∑ y : N.ComplexIdx, d y * d y
        = ∑ y : N.ComplexIdx, d y * N.incidenceMap v y := by rw [hv]
      _ = ∑ r : N.R, v r * (d (N.targetIdx r) - d (N.sourceIdx r)) := by
          simp only [incidenceMap_apply, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r _ => ?_
          have h1 : ∀ y : N.ComplexIdx, d y * (v r * ((if N.targetIdx r = y then (1 : ℝ) else 0) -
              (if N.sourceIdx r = y then 1 else 0))) =
              v r * ((if N.targetIdx r = y then d y else 0) -
                (if N.sourceIdx r = y then d y else 0)) := by
            intro y; split_ifs <;> ring
          rw [Finset.sum_congr rfl (fun y _ => h1 y), ← Finset.mul_sum, Finset.sum_sub_distrib]
          rw [Finset.sum_ite_eq, Finset.sum_ite_eq]
          simp
      _ = ∑ r : N.R, v r * ∑ s : S, (((N.targetIdx r).val s : ℝ) -
            ((N.sourceIdx r).val s : ℝ)) * Real.log (x s) := by
          exact Finset.sum_congr rfl fun r _ => by rw [hdiff r]
      _ = ∑ s : S, Real.log (x s) * N.complexMap (N.incidenceMap v) s := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun s _ => ?_
          change _ = Real.log (x s) * ∑ y : N.ComplexIdx, N.incidenceMap v y * (y.val s : ℝ)
          simp only [incidenceMap_apply, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r _ => ?_
          have h1 : ∀ y : N.ComplexIdx, Real.log (x s) * (v r * ((if N.targetIdx r = y then
              (1 : ℝ) else 0) - (if N.sourceIdx r = y then 1 else 0)) * (y.val s : ℝ)) =
              v r * Real.log (x s) * ((if N.targetIdx r = y then (y.val s : ℝ) else 0) -
                (if N.sourceIdx r = y then (y.val s : ℝ) else 0)) := by
            intro y; split_ifs <;> ring
          rw [Finset.sum_congr rfl (fun y _ => h1 y), ← Finset.mul_sum, Finset.sum_sub_distrib,
            Finset.sum_ite_eq, Finset.sum_ite_eq]
          simp only [Finset.mem_univ, if_true]
          ring
      _ = 0 := by rw [hv, hdY]; simp
  funext y
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => mul_self_nonneg (d y))).mp hdd y
    (Finset.mem_univ y)
  simpa using this

/-- **Horn's characterization.** -/
theorem forall_complexBalanced_iff (N : Network S) :
    (∀ κ : N.RateConstants, ∃ x : Concentration S, x.Positive ∧ N.IsComplexBalanced κ x) ↔
      N.WeaklyReversible ∧ N.DeficiencyZero :=
  ⟨N.weaklyReversible_and_deficiencyZero_of_forall_complexBalanced,
    fun ⟨hwr, hδ⟩ κ => N.exists_isComplexBalanced hwr hδ κ⟩

end Network
end CRNT
