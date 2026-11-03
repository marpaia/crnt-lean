import CRNT.Stochastic.MinimalSemigroup
import CRNT.Stochastic.MinimalSemigroupStochastic
import CRNT.Stochastic.CTMC
import CRNT.Stochastic.Kernel
import CRNT.Stochastic.FosterLyapunov
import CRNT.Flux.PSemiflow

/-!
# The minimal transition function of stochastic mass-action kinetics

The stochastic mass-action dynamics of a network is the jump system on `ℕ^S` with one channel per
reaction, rate `λ_r(n)` (`stochasticMassActionRate`) and target `n − y_r + y'_r`
(`jumpNextCount`). Its minimal transition function `transition κ t n m` is sub-stochastic,
continuous in `t ≥ 0`, and satisfies the backward Kolmogorov (chemical master) equation

`d/dt P(t)(n, m) = −λ(n) P(t)(n, m) + ∑_r λ_r(n) P(t)(n − y_r + y'_r, m)`

with `λ(n) = exitRate κ n` (`hasDerivAt_transition`). This is constructed on the whole count
lattice, with no conservation or boundedness assumption.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The jump system of stochastic mass-action kinetics. -/
noncomputable def jumpSystem (N : Network S) (κ : RateConstants N) : JumpSystem (S → ℕ) where
  ι := N.R
  rate r n := N.stochasticMassActionRate κ n r
  rate_nonneg r n := N.stochasticMassActionRate_nonneg κ n r
  next r n := N.jumpNextCount n r

/-- The minimal transition function of the stochastic mass-action dynamics. -/
noncomputable def transition (N : Network S) (κ : RateConstants N) (t : ℝ) (n m : S → ℕ) : ℝ :=
  (N.jumpSystem κ).Pmin t n m

theorem jumpSystem_q (N : Network S) (κ : RateConstants N) (n : S → ℕ) :
    (N.jumpSystem κ).q n = N.exitRate κ n := rfl

theorem transition_nonneg (N : Network S) (κ : RateConstants N) {t : ℝ} (ht : 0 ≤ t)
    (n m : S → ℕ) : 0 ≤ N.transition κ t n m :=
  (N.jumpSystem κ).Pmin_nonneg t ht n m

/-- **Sub-stochasticity.** -/
theorem sum_transition_le_one (N : Network S) (κ : RateConstants N) {t : ℝ} (ht : 0 ≤ t)
    (n : S → ℕ) (F : Finset (S → ℕ)) : ∑ m ∈ F, N.transition κ t n m ≤ 1 :=
  (N.jumpSystem κ).sum_Pmin_le_one t ht n F

/-- **Backward Kolmogorov equation** for stochastic mass-action kinetics. -/
theorem hasDerivAt_transition (N : Network S) (κ : RateConstants N) {t : ℝ} (ht : 0 < t)
    (n m : S → ℕ) :
    HasDerivAt (fun τ => N.transition κ τ n m)
      (-N.exitRate κ n * N.transition κ t n m +
        ∑ r, N.stochasticMassActionRate κ n r * N.transition κ t (N.jumpNextCount n r) m) t :=
  (N.jumpSystem κ).hasDerivAt_Pmin t ht n m

/-- The integral equation (first-jump decomposition). -/
theorem transition_eq (N : Network S) (κ : RateConstants N) {t : ℝ} (ht : 0 ≤ t)
    (n m : S → ℕ) :
    N.transition κ t n m = Real.exp (-(N.exitRate κ n * t)) * (if n = m then 1 else 0) +
      ∫ s in (0 : ℝ)..t, Real.exp (-(N.exitRate κ n * s)) *
        ∑ r, N.stochasticMassActionRate κ n r *
          N.transition κ (t - s) (N.jumpNextCount n r) m :=
  (N.jumpSystem κ).Pmin_eq t ht n m

end Network
end CRNT

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Positive-rate jumps preserve a P-invariant weight. -/
theorem weight_jumpNextCount (N : Network S) (κ : RateConstants N) {w : S → ℝ}
    (hw : N.IsPInvariant w) {n : S → ℕ} {r : N.R} (hr : 0 < N.stochasticMassActionRate κ n r) :
    ∑ s, w s * (N.jumpNextCount n r s : ℝ) = ∑ s, w s * (n s : ℝ) := by
  have hen : N.Enabled n r := by
    by_contra h
    rw [N.stochasticMassActionRate_eq_zero_of_not_enabled κ n r h] at hr
    exact lt_irrefl _ hr
  have hcast : ∀ s, (N.jumpNextCount n r s : ℝ) =
      (n s : ℝ) + N.reactionVector r s := by
    intro s
    simp only [jumpNextCount, reactionVector_apply]
    rw [Nat.cast_add, Nat.cast_sub (hen s)]
    ring
  simp only [hcast, mul_add, Finset.sum_add_distrib]
  have h0 : ∑ s, w s * N.reactionVector r s = 0 :=
    hw _ (N.reactionVector_mem_stoichSubspace r)
  rw [h0, add_zero]

/-- **Stochasticity for conservative networks.** The minimal transition function of a conservative
network is stochastic: from every count, the row sums to `1` at every time `t ≥ 0`. -/
theorem hasSum_transition_one_of_conservative (N : Network S) (κ : RateConstants N)
    (hcons : N.IsConservative) (n₀ : S → ℕ) {t : ℝ} (ht : 0 ≤ t) :
    HasSum (fun m => N.transition κ t n₀ m) 1 := by
  classical
  obtain ⟨w, hwinv, hwpos⟩ := hcons
  set W := ∑ s, w s * (n₀ s : ℝ)
  -- reachable counts keep the weight
  have hW : ∀ c, (N.jumpSystem κ).ReachPos n₀ c → ∑ s, w s * (c s : ℝ) = W := by
    intro c hc
    induction hc with
    | refl => rfl
    | @tail x y _ hxy ih =>
        obtain ⟨r, hr, rfl⟩ := hxy
        exact (N.weight_jumpNextCount κ hwinv hr).trans ih
  -- hence they lie in a finite box
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ c : S → ℕ, ∑ s, w s * (c s : ℝ) = W → ∀ s, c s ≤ K := by
    refine ⟨⌈∑ s, W / w s⌉₊, fun c hc s => ?_⟩
    have h1 : w s * (c s : ℝ) ≤ W := by
      rw [← hc]
      exact Finset.single_le_sum (f := fun s => w s * (c s : ℝ))
        (fun s _ => mul_nonneg (hwpos s).le (Nat.cast_nonneg _)) (Finset.mem_univ s)
    have h2 : (c s : ℝ) ≤ W / w s := by rw [le_div_iff₀ (hwpos s)]; linarith
    have hW0 : 0 ≤ W := Finset.sum_nonneg fun s _ => mul_nonneg (hwpos s).le (Nat.cast_nonneg _)
    have h3 : W / w s ≤ ∑ s, W / w s :=
      Finset.single_le_sum (f := fun s => W / w s) (fun s _ => div_nonneg hW0 (hwpos s).le)
        (Finset.mem_univ s)
    exact_mod_cast (h2.trans h3).trans (Nat.le_ceil _)
  set B : Finset (S → ℕ) := Fintype.piFinset fun _ => Finset.range (K + 1)
  refine (N.jumpSystem κ).hasSum_Pmin_one (Λ := ∑ c ∈ B, N.exitRate κ c) (fun c hc => ?_) ht
  have hcB : c ∈ B := by
    simp only [B, Fintype.mem_piFinset, Finset.mem_range]
    exact fun s => Nat.lt_succ_of_le (hK c (hW c hc) s)
  rw [jumpSystem_q]
  exact Finset.single_le_sum (f := fun c => N.exitRate κ c) (fun c _ => N.exitRate_nonneg κ c) hcB

end Network
end CRNT
