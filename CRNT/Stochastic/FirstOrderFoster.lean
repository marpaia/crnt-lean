import CRNT.Stochastic.FosterLyapunov

/-!
# First-order stochastic CRNs and affine Foster drift

For networks whose source complexes have total molecularity at most one, every propensity
is constant (zeroth order) or linear in one count coordinate.  Consequently the generator
drift of a linear observable is affine.  Coefficientwise negativity yields a Foster--
Lyapunov certificate.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Zeroth-order reaction. -/
def IsZeroOrderReaction (N : Network S) (r : N.R) : Prop :=
  ∀ s, (N.reaction r).source s = 0

/-- Reaction with exactly one molecule of exactly one source species. -/
def IsUnimolecularFrom (N : Network S) (r : N.R) (s0 : S) : Prop :=
  (N.reaction r).source s0 = 1 ∧
    ∀ s, s ≠ s0 → (N.reaction r).source s = 0

/-- First-order network: every reaction is zeroth order or unimolecular from a unique species. -/
def IsFirstOrderNetwork (N : Network S) : Prop :=
  ∀ r : N.R, N.IsZeroOrderReaction r ∨ ∃ s, N.IsUnimolecularFrom r s

/-- A reaction cannot be unimolecular from two distinct species. -/
theorem unimolecularFrom_unique (N : Network S) {r : N.R} {s t : S}
    (hs : N.IsUnimolecularFrom r s) (ht : N.IsUnimolecularFrom r t) : s = t := by
  by_contra hst
  have h0 := hs.2 t (Ne.symm hst)
  rw [ht.1] at h0
  omega

/-- Stochastic propensity of a zeroth-order reaction is its rate constant. -/
theorem stochasticRate_zeroOrder (N : Network S) (κ : N.RateConstants)
    (n : S → ℕ) {r : N.R} (hr : N.IsZeroOrderReaction r) :
    N.stochasticMassActionRate κ n r = κ.k r := by
  unfold stochasticMassActionRate
  have hp : (∏ s : S, ((n s).descFactorial ((N.reaction r).source s) : ℝ)) = 1 := by
    apply Finset.prod_eq_one
    intro s _
    simp [hr s]
  rw [hp, mul_one]

/-- Stochastic propensity of a unimolecular reaction is `κ_r n_s`. -/
theorem stochasticRate_unimolecular (N : Network S) (κ : N.RateConstants)
    (n : S → ℕ) {r : N.R} {s0 : S} (hr : N.IsUnimolecularFrom r s0) :
    N.stochasticMassActionRate κ n r = κ.k r * n s0 := by
  unfold stochasticMassActionRate
  have hp : (∏ s : S, ((n s).descFactorial ((N.reaction r).source s) : ℝ)) = n s0 := by
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ s0)]
    rw [hr.1]
    simp only [Nat.descFactorial_one, Nat.cast_id]
    have hprod : (∏ s ∈ Finset.univ \ {s0},
        ((n s).descFactorial ((N.reaction r).source s) : ℝ)) = 1 := by
      apply Finset.prod_eq_one
      intro s hs
      have hne : s ≠ s0 := by
        simpa using (Finset.mem_sdiff.mp hs).2
      simp [hr.2 s hne]
    rw [hprod, mul_one]
  rw [hp]

/-- Weighted stoichiometric increment of a reaction. -/
def weightedReactionIncrement (N : Network S) (w : S → ℝ) (r : N.R) : ℝ :=
  ∑ s : S, w s * N.reactionVector r s

/-- Constant drift contribution from zeroth-order reactions. -/
noncomputable def zeroOrderDrift (N : Network S) (κ : N.RateConstants) (w : S → ℝ) : ℝ := by
  classical
  exact ∑ r : N.R, if N.IsZeroOrderReaction r then
    κ.k r * N.weightedReactionIncrement w r else 0

/-- Linear drift coefficient multiplying count `n s`. -/
noncomputable def firstOrderDriftCoefficient (N : Network S) (κ : N.RateConstants)
    (w : S → ℝ) (s : S) : ℝ := by
  classical
  exact ∑ r : N.R, if N.IsUnimolecularFrom r s then
    κ.k r * N.weightedReactionIncrement w r else 0

/-- **Affine drift formula for first-order networks.** -/
theorem observableGenerator_linear_eq_affine_of_firstOrder
    (N : Network S) (κ : N.RateConstants) (hfirst : N.IsFirstOrderNetwork)
    (w : S → ℝ) (n : S → ℕ) :
    N.observableGenerator κ (linearObservable w) n =
      N.zeroOrderDrift κ w +
        ∑ s : S, N.firstOrderDriftCoefficient κ w s * (n s : ℝ) := by
  classical
  rw [N.observableGenerator_linear κ w n]
  unfold zeroOrderDrift firstOrderDriftCoefficient
  have hreaction : ∀ r : N.R,
      N.stochasticMassActionRate κ n r * N.weightedReactionIncrement w r =
        (if N.IsZeroOrderReaction r then κ.k r * N.weightedReactionIncrement w r else 0) +
          ∑ s : S, (if N.IsUnimolecularFrom r s then
            κ.k r * N.weightedReactionIncrement w r else 0) * (n s : ℝ) := by
    intro r
    rcases hfirst r with h0 | ⟨s0, hs0⟩
    · have hnot : ∀ s : S, ¬ N.IsUnimolecularFrom r s := by
        intro s hs
        have hz := h0 s
        rw [hs.1] at hz
        omega
      rw [N.stochasticRate_zeroOrder κ n h0]
      simp [h0, hnot]
    · have hn0 : ¬ N.IsZeroOrderReaction r := by
        intro h0
        have hz := h0 s0
        rw [hs0.1] at hz
        omega
      have hu : ∀ s : S, N.IsUnimolecularFrom r s ↔ s = s0 := by
        intro s
        constructor
        · intro hs
          exact N.unimolecularFrom_unique hs hs0
        · rintro rfl
          exact hs0
      rw [N.stochasticRate_unimolecular κ n hs0]
      simp [hn0, hu]
      ring
  calc
    ∑ r : N.R, N.stochasticMassActionRate κ n r *
        (∑ s : S, w s * N.reactionVector r s) =
      ∑ r : N.R, N.stochasticMassActionRate κ n r *
        N.weightedReactionIncrement w r := by rfl
    _ = ∑ r : N.R,
        ((if N.IsZeroOrderReaction r then κ.k r * N.weightedReactionIncrement w r else 0) +
          ∑ s : S, (if N.IsUnimolecularFrom r s then
            κ.k r * N.weightedReactionIncrement w r else 0) * (n s : ℝ)) := by
          apply Finset.sum_congr rfl
          intro r _
          exact hreaction r
    _ = (∑ r : N.R, if N.IsZeroOrderReaction r then
          κ.k r * N.weightedReactionIncrement w r else 0) +
        ∑ r : N.R, ∑ s : S, (if N.IsUnimolecularFrom r s then
          κ.k r * N.weightedReactionIncrement w r else 0) * (n s : ℝ) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ r : N.R, if N.IsZeroOrderReaction r then
          κ.k r * N.weightedReactionIncrement w r else 0) +
        ∑ s : S, ∑ r : N.R, (if N.IsUnimolecularFrom r s then
          κ.k r * N.weightedReactionIncrement w r else 0) * (n s : ℝ) := by
          rw [Finset.sum_comm]
    _ = (∑ r : N.R, if N.IsZeroOrderReaction r then
          κ.k r * N.weightedReactionIncrement w r else 0) +
        ∑ s : S, (∑ r : N.R, if N.IsUnimolecularFrom r s then
          κ.k r * N.weightedReactionIncrement w r else 0) * (n s : ℝ) := by
          congr 1
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.sum_mul]

/-- Coefficientwise first-order Foster condition. -/
structure FirstOrderFosterCoefficientCertificate (N : Network S)
    (κ : N.RateConstants) where
  firstOrder : N.IsFirstOrderNetwork
  weight : S → ℝ
  c : ℝ
  weight_pos : IsPositiveWeight weight
  c_pos : 0 < c
  coeff : ∀ s,
    N.firstOrderDriftCoefficient κ weight s ≤ -c * weight s

/-- The nonnegative constant needed in the Foster bound. -/
noncomputable def FirstOrderFosterCoefficientCertificate.bound
    {N : Network S} {κ : N.RateConstants}
    (C : FirstOrderFosterCoefficientCertificate N κ) : ℝ :=
  max 0 (N.zeroOrderDrift κ C.weight)

/-- **Coefficient criterion automatically yields a linear Foster certificate.** -/
noncomputable def FirstOrderFosterCoefficientCertificate.toFoster
    {N : Network S} {κ : N.RateConstants}
    (C : FirstOrderFosterCoefficientCertificate N κ) :
    LinearFosterLyapunovCertificate N κ where
  weight := C.weight
  c := C.c
  b := C.bound
  weight_pos := C.weight_pos
  c_pos := C.c_pos
  b_nonneg := le_max_left _ _
  drift := by
    intro n
    rw [N.observableGenerator_linear_eq_affine_of_firstOrder κ C.firstOrder C.weight n]
    have hzero : N.zeroOrderDrift κ C.weight ≤ C.bound := le_max_right _ _
    have hsum :
        (∑ s : S, N.firstOrderDriftCoefficient κ C.weight s * (n s : ℝ)) ≤
          ∑ s : S, (-C.c * C.weight s) * (n s : ℝ) := by
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_right (C.coeff s) (Nat.cast_nonneg _)
    calc
      N.zeroOrderDrift κ C.weight +
          ∑ s : S, N.firstOrderDriftCoefficient κ C.weight s * (n s : ℝ)
        ≤ C.bound + ∑ s : S, (-C.c * C.weight s) * (n s : ℝ) :=
          add_le_add hzero hsum
      _ = C.bound - C.c * linearObservable C.weight n := by
          unfold linearObservable
          rw [Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
          congr 1
          apply Finset.sum_congr rfl
          intro s _
          ring

end Network

end CRNT
