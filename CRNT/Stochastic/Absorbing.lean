import CRNT.Stochastic.IntegerLattice

/-!
# Deadlocked states and structural boundary traps

A count state is deadlocked exactly when no reaction source is dominated by the state.
This is the elementary boundary obstruction underlying stochastic irreducibility tests.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- No reaction can fire from the count state. -/
def IsDeadlockedCount (N : Network S) (n : S → ℕ) : Prop :=
  ∀ r : N.R, ¬ N.Enabled n r

/-- Equivalent source-deficiency characterization of deadlocked states. -/
theorem isDeadlockedCount_iff (N : Network S) (n : S → ℕ) :
    N.IsDeadlockedCount n ↔
      ∀ r : N.R, ∃ s : S, n s < (N.reaction r).source s := by
  unfold IsDeadlockedCount Enabled
  simp only [not_forall, not_le]

/-- The stochastic exit rate vanishes at every deadlocked state. -/
theorem exitRate_eq_zero_of_deadlocked (N : Network S) (κ : N.RateConstants)
    {n : S → ℕ} (h : N.IsDeadlockedCount n) : N.exitRate κ n = 0 := by
  unfold exitRate
  apply Finset.sum_eq_zero
  intro r _
  exact N.stochasticMassActionRate_eq_zero_of_not_enabled κ n r (h r)

/-- Conversely, under strictly positive rate constants, zero exit rate forces every
reaction to be disabled. -/
theorem deadlocked_of_exitRate_eq_zero (N : Network S) (κ : N.RateConstants)
    {n : S → ℕ} (hκ : ∀ r, 0 < κ.k r) (hzero : N.exitRate κ n = 0) :
    N.IsDeadlockedCount n := by
  intro r hen
  have hpos : 0 < N.stochasticMassActionRate κ n r := by
    unfold stochasticMassActionRate
    apply mul_pos (hκ r)
    apply Finset.prod_pos
    intro s _
    exact_mod_cast Nat.descFactorial_pos.mpr (hen s)
  have hle : N.stochasticMassActionRate κ n r ≤ N.exitRate κ n := by
    unfold exitRate
    exact Finset.single_le_sum
      (fun r _ => N.stochasticMassActionRate_nonneg κ n r) (Finset.mem_univ r)
  rw [hzero] at hle
  linarith

/-- Deadlocked states are terminal for count reachability. -/
theorem reachable_eq_of_deadlocked (N : Network S) {n m : S → ℕ}
    (habs : N.IsDeadlockedCount n) (hreach : N.CountReachable n m) : m = n := by
  induction hreach with
  | refl => rfl
  | tail hreach hstep ih =>
      subst ih
      rcases hstep with ⟨r, hen, rfl⟩
      exact False.elim (habs r hen)

/-- The zero count is deadlocked exactly when every reaction has a nonzero source complex. -/
theorem zero_deadlocked_iff_no_zero_source (N : Network S) :
    N.IsDeadlockedCount (fun _ => 0) ↔
      ∀ r : N.R, (N.reaction r).source ≠ 0 := by
  rw [N.isDeadlockedCount_iff]
  constructor
  · intro h r hzero
    obtain ⟨s, hs⟩ := h r
    rw [hzero] at hs
    simp at hs
  · intro h r
    by_contra hnone
    push_neg at hnone
    apply h r
    funext s
    specialize hnone s
    simp only [Pi.zero_apply]
    omega

/-- A zero-source reaction rules out deadlock at the origin. -/
theorem zero_not_deadlocked_of_zeroSourceReaction (N : Network S)
    {r : N.R} (hr : (N.reaction r).source = 0) :
    ¬ N.IsDeadlockedCount (fun _ => 0) := by
  rw [N.zero_deadlocked_iff_no_zero_source]
  push_neg
  exact ⟨r, hr⟩

end Network
end CRNT

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- An absorbing count state has no enabled firing to a distinct state.
Enabled null reactions are allowed. -/
def IsAbsorbingCount (N : Network S) (n : S → ℕ) : Prop :=
  ∀ r : N.R, N.Enabled n r → N.fireCount n r = n

/-- Enabled null firings are exactly the reactions with equal source and target. -/
theorem fireCount_eq_self_iff (N : Network S) {n : S → ℕ} {r : N.R}
    (hen : N.Enabled n r) :
    N.fireCount n r = n ↔ (N.reaction r).source = (N.reaction r).target := by
  constructor
  · intro h
    funext s
    have hs := hen s
    have heq := congrFun h s
    simp only [fireCount, dif_pos hen] at heq
    omega
  · intro h
    funext s
    have hs := hen s
    simp only [fireCount, dif_pos hen, ← h]
    omega

theorem isAbsorbingCount_iff (N : Network S) (n : S → ℕ) :
    N.IsAbsorbingCount n ↔
      ∀ r, N.Enabled n r → (N.reaction r).source = (N.reaction r).target := by
  exact forall_congr' fun r => forall_congr' fun hen => N.fireCount_eq_self_iff hen

theorem IsDeadlockedCount.absorbing {N : Network S} {n : S → ℕ}
    (h : N.IsDeadlockedCount n) : N.IsAbsorbingCount n := by
  intro r hen
  exact (h r hen).elim

theorem reachable_eq_of_absorbing (N : Network S) {n m : S → ℕ}
    (habs : N.IsAbsorbingCount n) (hreach : N.CountReachable n m) : m = n := by
  induction hreach with
  | refl => rfl
  | tail _ hstep ih =>
    subst ih
    rcases hstep with ⟨r, hen, rfl⟩
    exact habs r hen

theorem absorbing_iff_deadlocked_of_nontrivial (N : Network S)
    (hnt : ∀ r, (N.reaction r).Nontrivial) (n : S → ℕ) :
    N.IsAbsorbingCount n ↔ N.IsDeadlockedCount n := by
  constructor
  · intro h r hen
    exact hnt r ((N.fireCount_eq_self_iff hen).mp (h r hen))
  · exact IsDeadlockedCount.absorbing

/-- At the origin only a zero-source reaction with nonzero target can leave the state. -/
theorem zero_absorbing_iff_zeroSource_target_zero (N : Network S) :
    N.IsAbsorbingCount (fun _ => 0) ↔
      ∀ r, (N.reaction r).source = 0 → (N.reaction r).target = 0 := by
  rw [N.isAbsorbingCount_iff]
  constructor
  · intro h r hsrc
    have hen : N.Enabled (fun _ => 0) r := by intro s; simp [hsrc]
    exact (h r hen).symm.trans hsrc
  · intro h r hen
    have hsrc : (N.reaction r).source = 0 := by
      funext s
      exact Nat.eq_zero_of_le_zero (hen s)
    rw [hsrc, h r hsrc]

theorem zero_not_absorbing_of_zeroSourceReaction (N : Network S) {r : N.R}
    (hsrc : (N.reaction r).source = 0) (htgt : (N.reaction r).target ≠ 0) :
    ¬ N.IsAbsorbingCount (fun _ => 0) := by
  intro h
  exact htgt ((N.zero_absorbing_iff_zeroSource_target_zero.mp h) r hsrc)

end CRNT.Network
