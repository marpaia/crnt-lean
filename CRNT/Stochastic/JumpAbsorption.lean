import CRNT.Stochastic.FiniteAbsorption
import CRNT.Stochastic.Kernel
import Mathlib.Logic.Relation

/-!
# Absorption of the embedded jump chain on a finite closed set of counts

On a finite set `T` of counts that is closed under every jump of positive propensity, the
embedded jump chain of the stochastic mass-action model is a finite Markov chain; counts with
zero exit rate are absorbing. If from every count of `T` some absorbing count is reachable by
jumps of positive propensity, the chain is absorbed with probability one
(`CRNT.FiniteAbsorption.tendsto_absorbedMass_one`). This is the probabilistic form of extinction
results for stochastic reaction networks (Anderson–Enciso–Johnston 2014).

Main results:
* `CRNT.Network.jumpMatrix`, `CRNT.Network.jumpMatrix_absorbingChain`.
* `CRNT.Network.exists_pow_pos_of_jumpReach`.
* `CRNT.Network.tendsto_jumpAbsorption_one`.
-/

namespace CRNT

namespace Network

open Filter Topology FiniteAbsorption
open scoped BigOperators ENNReal

variable {S : Type} [DecidableEq S] [Fintype S]

/-- `T` is closed under every jump of positive propensity. -/
def JumpClosed (N : Network S) (κ : RateConstants N) (T : Finset (S → ℕ)) : Prop :=
  ∀ n ∈ T, ∀ r, 0 < N.stochasticMassActionRate κ n r → N.jumpNextCount n r ∈ T

/-- The column-stochastic transition matrix of the embedded jump chain on `T`
(entry `(i, j)`: probability of the jump `j → i`). -/
noncomputable def jumpMatrix (N : Network S) (κ : RateConstants N) (T : Finset (S → ℕ)) :
    Matrix T T ℝ := fun i j =>
  if N.exitRate κ j = 0 then (if i = j then 1 else 0)
  else ∑ r, N.jumpProb κ j r * (if N.jumpNextCount j r = (i : S → ℕ) then 1 else 0)

/-- The absorbing counts of `T` (zero exit rate). -/
noncomputable def absorbingCounts (N : Network S) (κ : RateConstants N) (T : Finset (S → ℕ)) :
    Finset T := Finset.univ.filter (fun j => N.exitRate κ j = 0)

theorem stochasticMassActionRate_eq_zero_of_jumpProb (N : Network S) (κ : RateConstants N)
    {n : S → ℕ} {r : N.R} (h : N.stochasticMassActionRate κ n r = 0) : N.jumpProb κ n r = 0 := by
  simp [jumpProb, h]

theorem jumpMatrix_absorbingChain (N : Network S) (κ : RateConstants N) {T : Finset (S → ℕ)}
    (hT : N.JumpClosed κ T) :
    AbsorbingChain (N.jumpMatrix κ T) (N.absorbingCounts κ T) where
  nonneg := by
    intro i j
    unfold jumpMatrix
    split_ifs
    · norm_num
    · norm_num
    · exact Finset.sum_nonneg fun r _ =>
        mul_nonneg (N.jumpProb_nonneg κ _ r) (by split_ifs <;> norm_num)
  colSum := by
    intro j
    unfold jumpMatrix
    by_cases h0 : N.exitRate κ j = 0
    · simp [h0]
    · simp only [h0, ite_false]
      rw [Finset.sum_comm]
      have hpos : 0 < N.exitRate κ j := lt_of_le_of_ne (N.exitRate_nonneg κ j) (Ne.symm h0)
      calc ∑ r, ∑ i : T, N.jumpProb κ j r *
            (if N.jumpNextCount j r = (i : S → ℕ) then 1 else 0) = ∑ r, N.jumpProb κ j r := by
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [← Finset.mul_sum]
            rcases (N.stochasticMassActionRate_nonneg κ j r).lt_or_eq with hr | hr
            · have hmem := hT j j.2 r hr
              rw [Finset.sum_eq_single ⟨N.jumpNextCount j r, hmem⟩]
              · simp
              · intro b _ hb
                have : N.jumpNextCount j r ≠ (b : S → ℕ) := fun he => hb (Subtype.ext he.symm)
                simp [this]
              · simp
            · rw [stochasticMassActionRate_eq_zero_of_jumpProb N κ hr.symm]; simp
        _ = 1 := N.sum_jumpProb_eq_one κ j hpos
  absorbing := by
    intro a ha
    have : N.exitRate κ a = 0 := (Finset.mem_filter.mp ha).2
    simp [jumpMatrix, this]

/-- One jump of positive propensity inside `T`. -/
def JumpAbsStep (N : Network S) (κ : RateConstants N) (T : Finset (S → ℕ)) (j i : T) : Prop :=
  ∃ r, 0 < N.stochasticMassActionRate κ j r ∧ N.jumpNextCount j r = i

theorem jumpMatrix_pos_of_step (N : Network S) (κ : RateConstants N) {T : Finset (S → ℕ)}
    {j i : T} (h : N.JumpAbsStep κ T j i) : 0 < N.jumpMatrix κ T i j := by
  obtain ⟨r, hr, hnext⟩ := h
  have hexit : 0 < N.exitRate κ j :=
    lt_of_lt_of_le hr (Finset.single_le_sum (f := fun r => N.stochasticMassActionRate κ j r)
      (fun r _ => N.stochasticMassActionRate_nonneg κ j r) (Finset.mem_univ r))
  unfold jumpMatrix
  rw [if_neg hexit.ne']
  have hp : 0 < N.jumpProb κ j r := div_pos hr hexit
  calc (0 : ℝ) < N.jumpProb κ j r * (if N.jumpNextCount j r = (i : S → ℕ) then 1 else 0) := by
        rw [if_pos hnext, mul_one]; exact hp
    _ ≤ _ := Finset.single_le_sum (f := fun r => N.jumpProb κ j r *
        (if N.jumpNextCount j r = (i : S → ℕ) then 1 else 0))
        (fun r _ => mul_nonneg (N.jumpProb_nonneg κ _ r) (by split_ifs <;> norm_num))
        (Finset.mem_univ r)

/-- Reachability by jumps of positive propensity gives a positive multi-step probability. -/
theorem exists_pow_pos_of_jumpReach (N : Network S) (κ : RateConstants N) {T : Finset (S → ℕ)}
    (hT : N.JumpClosed κ T) {j i : T} (h : Relation.ReflTransGen (N.JumpAbsStep κ T) j i) :
    ∃ n, 0 < (N.jumpMatrix κ T ^ n) i j := by
  have hc := N.jumpMatrix_absorbingChain κ hT
  induction h with
  | refl => exact ⟨0, by simp⟩
  | @tail k i' _ hstep ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    rw [pow_succ', Matrix.mul_apply]
    calc (0 : ℝ) < N.jumpMatrix κ T i' k * (N.jumpMatrix κ T ^ n) k j :=
          mul_pos (N.jumpMatrix_pos_of_step κ hstep) hn
      _ ≤ _ := Finset.single_le_sum (f := fun l => N.jumpMatrix κ T i' l *
          (N.jumpMatrix κ T ^ n) l j)
          (fun l _ => mul_nonneg (hc.nonneg _ _) (pow_nonneg' hc n l j)) (Finset.mem_univ k)

/-- **Absorption with probability one for the jump chain.** If `T` is jump-closed and every
count of `T` can reach an absorbing count of `T` through jumps of positive propensity, then the
probability that the embedded jump chain started at `j` has been absorbed by step `n` tends to
one. -/
theorem tendsto_jumpAbsorption_one (N : Network S) (κ : RateConstants N) {T : Finset (S → ℕ)}
    (hT : N.JumpClosed κ T)
    (hreach : ∀ j : T, ∃ a : T, N.exitRate κ a = 0 ∧ Relation.ReflTransGen (N.JumpAbsStep κ T) j a)
    (j : T) :
    Tendsto (fun n => absorbedMass (N.jumpMatrix κ T) (N.absorbingCounts κ T) n j) atTop (𝓝 1) := by
  have hc := N.jumpMatrix_absorbingChain κ hT
  refine tendsto_absorbedMass_one hc (fun j => ?_) j
  obtain ⟨a, ha, hr⟩ := hreach j
  obtain ⟨n, hn⟩ := N.exists_pow_pos_of_jumpReach κ hT hr
  refine ⟨n, lt_of_lt_of_le hn ?_⟩
  exact Finset.single_le_sum (f := fun b => (N.jumpMatrix κ T ^ n) b j)
    (fun b _ => pow_nonneg' hc n b j) (Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩)

attribute [local instance] CRNT.Network.instMeasurableSpaceCount in
/-- The jump matrix is the restriction of the library's embedded-jump-chain kernel
`CRNT.Network.jumpKernel` to `T`. -/
theorem jumpMatrix_eq_jumpKernel (N : Network S) (κ : RateConstants N) (T : Finset (S → ℕ))
    (i j : T) : N.jumpMatrix κ T i j = (N.jumpKernel κ j {(i : S → ℕ)}).toReal := by
  rw [jumpKernel_apply']
  have hind : ∀ x : S → ℕ, ({(i : S → ℕ)} : Set (S → ℕ)).indicator (1 : (S → ℕ) → ℝ≥0∞) x =
      if x = (i : S → ℕ) then 1 else 0 := by
    intro x
    by_cases hx : x = (i : S → ℕ)
    · simp [hx]
    · simp [hx]
  by_cases h0 : N.exitRate κ j = 0
  · simp only [jumpMatrix, h0, ite_true, hind]
    by_cases hij : i = j
    · subst hij; simp
    · have : (j : S → ℕ) ≠ i := fun e => hij (Subtype.ext e.symm)
      simp [hij, this]
  · simp only [jumpMatrix, h0, ite_false, hind]
    rw [ENNReal.toReal_sum (fun r _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (by split_ifs <;> simp))]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (N.jumpProb_nonneg κ _ r)]
    split_ifs <;> simp

end Network

end CRNT
