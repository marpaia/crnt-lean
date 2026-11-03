import CRNT.Dynamics.TierLyapunov
import Mathlib.Topology.Order.Compact

/-!
# Origin geometry for the tier Lyapunov function

The lower-bound half of the strongly-endotactic permanence proof needs one elementary geometric
fact about

`U(x) = 1 + relEntropy 1 x`.

On the nonnegative unit coordinate box, the origin is the unique maximizer of `U`.  In particular

`U(0) = 1 + card S`,

and every nonzero nonnegative `x` with `‖x‖ ≤ 1` satisfies `U(x) < U(0)`.

We also record the complementary compactness fact used to choose an origin-exclusion ball: a
compact set of strictly positive concentrations is uniformly separated from the origin.
-/

open scoped BigOperators Topology

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Coordinate contribution to `relEntropy 1 x`. -/
noncomputable def tierEntropyCoordinate (t : ℝ) : ℝ :=
  t * Real.log t - t + 1

/-- `tierEntropy` is one plus the sum of the coordinate contributions. -/
theorem tierEntropy_eq_one_add_sum (x : Concentration S) :
    tierEntropy x = 1 + ∑ s : S, tierEntropyCoordinate (x s) := by
  simp [tierEntropy, relEntropy, tierReference, tierEntropyCoordinate]

/-- A zero coordinate contributes exactly one unit of entropy. -/
@[simp] theorem tierEntropyCoordinate_zero : tierEntropyCoordinate 0 = 1 := by
  simp [tierEntropyCoordinate]

/-- The tier entropy at the origin is `1 + |S|`. -/
theorem tierEntropy_zero :
    tierEntropy (0 : Concentration S) = 1 + (Fintype.card S : ℝ) := by
  rw [tierEntropy_eq_one_add_sum]
  simp [tierEntropyCoordinate]

/-- On `[0,1]`, each coordinate contributes at most its value at zero. -/
theorem tierEntropyCoordinate_le_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    tierEntropyCoordinate t ≤ 1 := by
  have hlog : Real.log t ≤ 0 := Real.log_nonpos ht0 ht1
  have hmul : t * Real.log t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 hlog
  unfold tierEntropyCoordinate
  linarith

/-- On `(0,1]`, the coordinate contribution is strictly below its value at zero. -/
theorem tierEntropyCoordinate_lt_one {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    tierEntropyCoordinate t < 1 := by
  have hlog : Real.log t ≤ 0 := Real.log_nonpos ht0.le ht1
  have hmul : t * Real.log t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0.le hlog
  unfold tierEntropyCoordinate
  linarith

/-- A nonnegative vector of Pi norm at most one has every coordinate in `[0,1]`. -/
theorem coord_mem_unitInterval_of_nonnegative_norm_le_one
    {x : Concentration S} (hx : x.Nonnegative) (hnorm : ‖x‖ ≤ 1) (s : S) :
    x s ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨hx s, ?_⟩
  have hcoord : |x s| ≤ ‖x‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm x s
  have hxabs : x s ≤ |x s| := le_abs_self _
  exact hxabs.trans (hcoord.trans hnorm)

/-- **Origin upper bound.** Every nonnegative point in the unit Pi-norm ball has entropy no larger
than the origin. -/
theorem tierEntropy_le_zero_of_nonnegative_norm_le_one
    {x : Concentration S} (hx : x.Nonnegative) (hnorm : ‖x‖ ≤ 1) :
    tierEntropy x ≤ tierEntropy (0 : Concentration S) := by
  rw [tierEntropy_eq_one_add_sum, tierEntropy_zero]
  have hsum : (∑ s : S, tierEntropyCoordinate (x s)) ≤ ∑ _s : S, (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro s _
    exact tierEntropyCoordinate_le_one
      (coord_mem_unitInterval_of_nonnegative_norm_le_one hx hnorm s).1
      (coord_mem_unitInterval_of_nonnegative_norm_le_one hx hnorm s).2
  simpa using add_le_add_left hsum 1

/-- A nonzero nonnegative finite vector has a strictly positive coordinate. -/
theorem exists_coord_pos_of_nonnegative_ne_zero
    {x : Concentration S} (hx : x.Nonnegative) (hne : x ≠ 0) :
    ∃ s : S, 0 < x s := by
  by_contra hnot
  push_neg at hnot
  apply hne
  funext s
  exact le_antisymm (hnot s) (hx s)

/-- **Strict origin maximum on the unit box.** The origin is the unique entropy maximizer among
nonnegative concentrations of Pi norm at most one. -/
theorem tierEntropy_lt_zero_of_nonnegative_norm_le_one_ne_zero
    {x : Concentration S} (hx : x.Nonnegative) (hnorm : ‖x‖ ≤ 1) (hne : x ≠ 0) :
    tierEntropy x < tierEntropy (0 : Concentration S) := by
  obtain ⟨s₀, hs₀⟩ := exists_coord_pos_of_nonnegative_ne_zero hx hne
  rw [tierEntropy_eq_one_add_sum, tierEntropy_zero]
  have hle : ∀ s : S, tierEntropyCoordinate (x s) ≤ 1 := by
    intro s
    exact tierEntropyCoordinate_le_one
      (coord_mem_unitInterval_of_nonnegative_norm_le_one hx hnorm s).1
      (coord_mem_unitInterval_of_nonnegative_norm_le_one hx hnorm s).2
  have hlt : tierEntropyCoordinate (x s₀) < 1 :=
    tierEntropyCoordinate_lt_one hs₀
      (coord_mem_unitInterval_of_nonnegative_norm_le_one hx hnorm s₀).2
  have hsum : (∑ s : S, tierEntropyCoordinate (x s)) < ∑ _s : S, (1 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro s _
      exact hle s
    · exact ⟨s₀, Finset.mem_univ s₀, hlt⟩
  simpa using add_lt_add_left hsum 1

/-- The headline origin formula used by the finite-segment exclusion argument. -/
theorem tierEntropy_origin_value :
    tierEntropy (0 : Concentration S) = 1 + (Fintype.card S : ℝ) :=
  tierEntropy_zero

/-- **Uniform separation of a compact positive set from the origin.**

The `Nonempty S` assumption is necessary: for an empty species type the unique concentration is the
zero vector while positivity is vacuous. -/
theorem exists_pos_norm_lower_bound_of_isCompact_positive [Nonempty S]
    {K : Set (Concentration S)} (hK : IsCompact K)
    (hKpos : ∀ x ∈ K, x.Positive) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ K, r ≤ ‖x‖ := by
  have hnormpos : ∀ x ∈ K, (0 : ℝ) < ‖x‖ := by
    intro x hx
    rw [norm_pos_iff]
    intro hzero
    have hs := hKpos x hx (Classical.choice inferInstance)
    rw [hzero] at hs
    simpa using hs
  exact hK.exists_forall_le' continuous_norm.continuousOn hnormpos

/-- Equivalent ball-disjointness form of compact-positive origin separation. -/
theorem exists_ball_zero_disjoint_of_isCompact_positive [Nonempty S]
    {K : Set (Concentration S)} (hK : IsCompact K)
    (hKpos : ∀ x ∈ K, x.Positive) :
    ∃ r : ℝ, 0 < r ∧ Disjoint K (Metric.ball (0 : Concentration S) r) := by
  obtain ⟨r, hr, hnorm⟩ := exists_pos_norm_lower_bound_of_isCompact_positive hK hKpos
  refine ⟨r, hr, Set.disjoint_left.2 ?_⟩
  intro x hxK hxball
  have hdist : ‖x‖ < r := by
    simpa [Metric.mem_ball, dist_zero_right] using hxball
  exact (not_lt_of_ge (hnorm x hxK)) hdist

end Network
end CRNT
