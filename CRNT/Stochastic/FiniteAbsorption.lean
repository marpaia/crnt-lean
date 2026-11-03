import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Absorption with probability one in finite Markov chains

Let `P` be the column-stochastic transition matrix of a finite Markov chain (`P i j` is the
probability of a jump `j → i`) and `A` a set of absorbing states. If from every state some
absorbing state is reached with positive probability, then the probability of being absorbed by
time `n` tends to one (Kemeny–Snell, *Finite Markov Chains*, Theorem 3.1.1). This is the
probabilistic conclusion behind extinction results for stochastic reaction networks
(Anderson–Enciso–Johnston 2014).

Main results:
* `CRNT.FiniteAbsorption.absorbedMass_mono`: absorbed mass is nondecreasing in time.
* `CRNT.FiniteAbsorption.tendsto_absorbedMass_one`.
-/

namespace CRNT

namespace FiniteAbsorption

open Filter Topology
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Hypotheses on a finite chain with absorbing set `A`. -/
structure AbsorbingChain (P : Matrix ι ι ℝ) (A : Finset ι) : Prop where
  nonneg : ∀ i j, 0 ≤ P i j
  colSum : ∀ j, ∑ i, P i j = 1
  absorbing : ∀ a ∈ A, P a a = 1

variable {P : Matrix ι ι ℝ} {A : Finset ι}

theorem pow_nonneg' (h : AbsorbingChain P A) (n : ℕ) : ∀ i j, 0 ≤ (P ^ n) i j := by
  induction n with
  | zero => intro i j; simp [Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    intro i j
    rw [pow_succ', Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (h.nonneg i k) (ih k j)

theorem pow_colSum (h : AbsorbingChain P A) (n : ℕ) : ∀ j, ∑ i, (P ^ n) i j = 1 := by
  induction n with
  | zero => intro j; simp [Matrix.one_apply]
  | succ n ih =>
    intro j
    simp only [pow_succ', Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, h.colSum, one_mul]
    exact ih j

/-- In an absorbing column all mass stays put. -/
theorem absorbing_col (h : AbsorbingChain P A) {a : ι} (ha : a ∈ A) (i : ι) (hi : i ≠ a) :
    P i a = 0 := by
  have hs := h.colSum a
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), h.absorbing a ha] at hs
  have hz : ∑ k ∈ Finset.univ.erase a, P k a = 0 := by linarith
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => h.nonneg k a)).mp hz i
    (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)

theorem pow_absorbing_col (h : AbsorbingChain P A) {a : ι} (ha : a ∈ A) (n : ℕ) (i : ι) :
    (P ^ n) i a = if i = a then 1 else 0 := by
  induction n generalizing i with
  | zero => simp [Matrix.one_apply]
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [ih, h.absorbing a ha]; split_ifs <;> simp
    · intro k _ hk; rw [absorbing_col h ha k hk, mul_zero]
    · simp

/-- Probability of being in `A` after `n` steps from `j`. -/
def absorbedMass (P : Matrix ι ι ℝ) (A : Finset ι) (n : ℕ) (j : ι) : ℝ := ∑ a ∈ A, (P ^ n) a j

/-- Probability of being outside `A` after `n` steps from `j`. -/
theorem escapeMass_eq (h : AbsorbingChain P A) (n : ℕ) (j : ι) :
    1 - absorbedMass P A n j = ∑ k ∈ Finset.univ.filter (· ∉ A), (P ^ n) k j := by
  rw [← pow_colSum h n j, absorbedMass, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ A)]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  ring

/-- Absorbed mass at time `m + n` decomposes over the state at time `n`. -/
theorem absorbedMass_add (_h : AbsorbingChain P A) (m n : ℕ) (j : ι) :
    absorbedMass P A (m + n) j = ∑ l, absorbedMass P A m l * (P ^ n) l j := by
  unfold absorbedMass
  simp only [pow_add, Matrix.mul_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => by rw [Finset.sum_mul]

theorem absorbedMass_le_one (h : AbsorbingChain P A) (n : ℕ) (j : ι) :
    absorbedMass P A n j ≤ 1 := by
  have := escapeMass_eq h n j
  have : 0 ≤ ∑ k ∈ Finset.univ.filter (· ∉ A), (P ^ n) k j :=
    Finset.sum_nonneg fun k _ => pow_nonneg' h n k j
  linarith

/-- Absorbed states contribute their full mass. -/
theorem absorbedMass_of_mem (h : AbsorbingChain P A) {a : ι} (ha : a ∈ A) (m : ℕ) :
    absorbedMass P A m a = 1 := by
  unfold absorbedMass
  rw [Finset.sum_eq_single a]
  · rw [pow_absorbing_col h ha]; simp
  · intro b _ hb; rw [pow_absorbing_col h ha]; simp [hb]
  · exact fun h' => absurd ha h'

/-- **Monotonicity**: absorbed mass never decreases. -/
theorem absorbedMass_mono (h : AbsorbingChain P A) (j : ι) :
    Monotone (fun n => absorbedMass P A n j) := by
  refine monotone_nat_of_le_succ fun n => ?_
  show absorbedMass P A n j ≤ absorbedMass P A (n + 1) j
  rw [add_comm n 1, absorbedMass_add h 1 n j]
  unfold absorbedMass
  calc ∑ a ∈ A, (P ^ n) a j = ∑ l ∈ A, (∑ a ∈ A, (P ^ 1) a l) * (P ^ n) l j := by
        refine Finset.sum_congr rfl fun l hl => ?_
        have := absorbedMass_of_mem h hl 1
        unfold absorbedMass at this
        rw [this, one_mul]
    _ ≤ ∑ l, (∑ a ∈ A, (P ^ 1) a l) * (P ^ n) l j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun l _ _ =>
          mul_nonneg (Finset.sum_nonneg fun a _ => pow_nonneg' h 1 a l) (pow_nonneg' h n l j)

/-- **Absorption with probability one.** If every state reaches `A` with positive probability,
the absorbed mass tends to `1` from every state. -/
theorem tendsto_absorbedMass_one (h : AbsorbingChain P A)
    (hreach : ∀ j, ∃ n, 0 < absorbedMass P A n j) (j : ι) :
    Tendsto (fun n => absorbedMass P A n j) atTop (𝓝 1) := by
  classical
  choose t ht using hreach
  set T := ∑ k, t k
  have htT : ∀ k, t k ≤ T := fun k =>
    Finset.single_le_sum (f := t) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  -- uniform lower bound at time `T`
  have hpos : ∀ k, 0 < absorbedMass P A T k := fun k =>
    lt_of_lt_of_le (ht k) (absorbedMass_mono h k (htT k))
  obtain ⟨δ, hδ, hδle⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ k, δ ≤ absorbedMass P A T k := by
    by_cases hne : (Finset.univ : Finset ι).Nonempty
    · obtain ⟨k₀, -, hk₀⟩ := Finset.exists_min_image Finset.univ
        (fun k => absorbedMass P A T k) hne
      exact ⟨_, hpos k₀, fun k => hk₀ k (Finset.mem_univ k)⟩
    · exact ⟨1, one_pos, fun k => absurd ⟨k, Finset.mem_univ k⟩ hne⟩
  -- geometric decay of the escape mass along multiples of `T`
  set e : ℕ → ι → ℝ := fun n k => 1 - absorbedMass P A n k
  have he_nonneg : ∀ n k, 0 ≤ e n k := fun n k => by
    simp only [e]; linarith [absorbedMass_le_one h n k]
  have hstep : ∀ n k, e (T + n) k ≤ (1 - δ) * e n k := by
    intro n k
    simp only [e]
    rw [absorbedMass_add h T n k]
    have hsum : ∑ l, (P ^ n) l k = 1 := pow_colSum h n k
    have : 1 - ∑ l, absorbedMass P A T l * (P ^ n) l k =
        ∑ l, (1 - absorbedMass P A T l) * (P ^ n) l k := by
      rw [← hsum]; rw [hsum]
      simp only [sub_mul, one_mul, Finset.sum_sub_distrib, hsum]
    rw [this]
    -- split over `A` and its complement
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ A)]
    have hA : ∑ l ∈ Finset.univ.filter (· ∈ A), (1 - absorbedMass P A T l) * (P ^ n) l k = 0 :=
      Finset.sum_eq_zero fun l hl => by
        rw [absorbedMass_of_mem h (Finset.mem_filter.mp hl).2, sub_self, zero_mul]
    rw [hA, zero_add, escapeMass_eq h n k, Finset.mul_sum]
    exact Finset.sum_le_sum fun l _ =>
      mul_le_mul_of_nonneg_right (by linarith [hδle l]) (pow_nonneg' h n l k)
  have hgeom : ∀ m, e (T * m) j ≤ (1 - δ) ^ m := by
    intro m
    induction m with
    | zero =>
      simp only [mul_zero, pow_zero, e]
      linarith [(show 0 ≤ absorbedMass P A 0 j from
        Finset.sum_nonneg fun a _ => pow_nonneg' h 0 a j)]
    | succ m ih =>
      calc e (T * (m + 1)) j = e (T + T * m) j := by ring_nf
        _ ≤ (1 - δ) * e (T * m) j := hstep _ _
        _ ≤ (1 - δ) * (1 - δ) ^ m := by
            refine mul_le_mul_of_nonneg_left ih ?_
            have := hδle j
            linarith [absorbedMass_le_one h T j]
        _ = (1 - δ) ^ (m + 1) := by ring
  -- conclude with monotonicity
  have hδ1 : δ ≤ 1 := (hδle j).trans (absorbedMass_le_one h T j)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (by linarith : 1 - δ < 1)
  refine ⟨T * m, fun n hn => ?_⟩
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [absorbedMass_le_one h n j])]
  have hmono := absorbedMass_mono h j hn
  have := hgeom m
  simp only [e] at this
  have hpow_nn : 0 ≤ (1 - δ) ^ m := pow_nonneg (by linarith) m
  linarith

end FiniteAbsorption

end CRNT
