import CRNT.Stochastic.FiniteAbsorption

/-!
# Absorption into a closed set

`CRNT.Stochastic.FiniteAbsorption` treats absorption by a set of absorbing states. The same
argument works for any **closed** set `A` (no transition leaves `A`): the probability of being in
`A` after `n` steps is nondecreasing, and if `A` is reachable from every state it tends to one.
This is the form needed when the chain keeps moving after it is trapped, for example inside the
closed communicating classes of a stochastic reaction network.

* `ClosedChain`, `ClosedChain.of_absorbing`.
* `closedMass_of_mem`, `closedMass_mono`, `tendsto_closedMass_one`.
-/

namespace CRNT

namespace FiniteAbsorption

open Filter Topology

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A column-stochastic matrix with a closed set `A`: no mass moves from `A` to its complement. -/
structure ClosedChain (P : Matrix ι ι ℝ) (A : Finset ι) : Prop where
  nonneg : ∀ i j, 0 ≤ P i j
  colSum : ∀ j, ∑ i, P i j = 1
  closed : ∀ a ∈ A, ∀ i, i ∉ A → P i a = 0

variable {P : Matrix ι ι ℝ} {A : Finset ι}

/-- A set of absorbing states is closed. -/
theorem ClosedChain.of_absorbing (h : AbsorbingChain P A) : ClosedChain P A :=
  ⟨h.nonneg, h.colSum, fun _ ha i hi => absorbing_col h ha i (fun hia => hi (hia ▸ ha))⟩

theorem ClosedChain.pow_nonneg (h : ClosedChain P A) (n : ℕ) : ∀ i j, 0 ≤ (P ^ n) i j := by
  induction n with
  | zero => intro i j; simp [Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    intro i j
    rw [pow_succ', Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (h.nonneg i k) (ih k j)

theorem ClosedChain.pow_colSum (h : ClosedChain P A) (n : ℕ) : ∀ j, ∑ i, (P ^ n) i j = 1 := by
  induction n with
  | zero => intro j; simp [Matrix.one_apply]
  | succ n ih =>
    intro j
    simp only [pow_succ', Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, h.colSum, one_mul]
    exact ih j

theorem ClosedChain.pow_closed (h : ClosedChain P A) (n : ℕ) :
    ∀ a ∈ A, ∀ i, i ∉ A → (P ^ n) i a = 0 := by
  induction n with
  | zero => intro a ha i hi; simp [show i ≠ a from fun e => hi (e ▸ ha)]
  | succ n ih =>
    intro a ha i hi
    rw [pow_succ', Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k ∈ A
    · rw [h.closed k hk i hi, zero_mul]
    · rw [ih a ha k hk, mul_zero]

/-- From a state of `A`, all mass stays in `A`. -/
theorem closedMass_of_mem (h : ClosedChain P A) {a : ι} (ha : a ∈ A) (m : ℕ) :
    absorbedMass P A m a = 1 := by
  unfold absorbedMass
  have hs := h.pow_colSum m a
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ A)] at hs
  have hz : ∑ i ∈ Finset.univ.filter (· ∉ A), (P ^ m) i a = 0 :=
    Finset.sum_eq_zero fun i hi => h.pow_closed m a ha i (Finset.mem_filter.mp hi).2
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter] at hs
  linarith

theorem closedMass_add (m n : ℕ) (j : ι) :
    absorbedMass P A (m + n) j = ∑ l, absorbedMass P A m l * (P ^ n) l j := by
  unfold absorbedMass
  simp only [pow_add, Matrix.mul_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => by rw [Finset.sum_mul]

theorem closedMass_le_one (h : ClosedChain P A) (n : ℕ) (j : ι) : absorbedMass P A n j ≤ 1 := by
  unfold absorbedMass
  rw [← h.pow_colSum n j]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun k _ _ => h.pow_nonneg n k j

/-- **Monotonicity.** -/
theorem closedMass_mono (h : ClosedChain P A) (j : ι) :
    Monotone (fun n => absorbedMass P A n j) := by
  refine monotone_nat_of_le_succ fun n => ?_
  show absorbedMass P A n j ≤ absorbedMass P A (n + 1) j
  rw [add_comm n 1, closedMass_add 1 n j]
  unfold absorbedMass
  calc ∑ a ∈ A, (P ^ n) a j = ∑ l ∈ A, (∑ a ∈ A, (P ^ 1) a l) * (P ^ n) l j := by
        refine Finset.sum_congr rfl fun l hl => ?_
        have := closedMass_of_mem h hl 1
        unfold absorbedMass at this
        rw [this, one_mul]
    _ ≤ ∑ l, (∑ a ∈ A, (P ^ 1) a l) * (P ^ n) l j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun l _ _ =>
          mul_nonneg (Finset.sum_nonneg fun a _ => h.pow_nonneg 1 a l) (h.pow_nonneg n l j)

/-- **Absorption into a closed set with probability one.** -/
theorem tendsto_closedMass_one (h : ClosedChain P A)
    (hreach : ∀ j, ∃ n, 0 < absorbedMass P A n j) (j : ι) :
    Tendsto (fun n => absorbedMass P A n j) atTop (𝓝 1) := by
  classical
  choose t ht using hreach
  set T := ∑ k, t k
  have htT : ∀ k, t k ≤ T := fun k =>
    Finset.single_le_sum (f := t) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have hpos : ∀ k, 0 < absorbedMass P A T k := fun k =>
    lt_of_lt_of_le (ht k) (closedMass_mono h k (htT k))
  obtain ⟨δ, hδ, hδle⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ k, δ ≤ absorbedMass P A T k := by
    by_cases hne : (Finset.univ : Finset ι).Nonempty
    · obtain ⟨k₀, -, hk₀⟩ := Finset.exists_min_image Finset.univ
        (fun k => absorbedMass P A T k) hne
      exact ⟨_, hpos k₀, fun k => hk₀ k (Finset.mem_univ k)⟩
    · exact ⟨1, one_pos, fun k => absurd ⟨k, Finset.mem_univ k⟩ hne⟩
  set e : ℕ → ι → ℝ := fun n k => 1 - absorbedMass P A n k
  have hesc : ∀ n k, e n k = ∑ l ∈ Finset.univ.filter (· ∉ A), (P ^ n) l k := by
    intro n k
    simp only [e, absorbedMass]
    rw [← h.pow_colSum n k, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ A)]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    ring
  have hstep : ∀ n k, e (T + n) k ≤ (1 - δ) * e n k := by
    intro n k
    simp only [e]
    rw [closedMass_add T n k]
    have hsum : ∑ l, (P ^ n) l k = 1 := h.pow_colSum n k
    have : 1 - ∑ l, absorbedMass P A T l * (P ^ n) l k =
        ∑ l, (1 - absorbedMass P A T l) * (P ^ n) l k := by
      simp only [sub_mul, one_mul, Finset.sum_sub_distrib, hsum]
    rw [this, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ A)]
    have hA : ∑ l ∈ Finset.univ.filter (· ∈ A), (1 - absorbedMass P A T l) * (P ^ n) l k = 0 :=
      Finset.sum_eq_zero fun l hl => by
        rw [closedMass_of_mem h (Finset.mem_filter.mp hl).2, sub_self, zero_mul]
    rw [hA, zero_add]
    have := hesc n k
    simp only [e] at this
    rw [this, Finset.mul_sum]
    exact Finset.sum_le_sum fun l _ =>
      mul_le_mul_of_nonneg_right (by linarith [hδle l]) (h.pow_nonneg n l k)
  have hgeom : ∀ m, e (T * m) j ≤ (1 - δ) ^ m := by
    intro m
    induction m with
    | zero =>
      simp only [mul_zero, pow_zero, e]
      linarith [(show 0 ≤ absorbedMass P A 0 j from
        Finset.sum_nonneg fun a _ => h.pow_nonneg 0 a j)]
    | succ m ih =>
      calc e (T * (m + 1)) j = e (T + T * m) j := by ring_nf
        _ ≤ (1 - δ) * e (T * m) j := hstep _ _
        _ ≤ (1 - δ) * (1 - δ) ^ m := by
            refine mul_le_mul_of_nonneg_left ih ?_
            have := hδle j
            linarith [closedMass_le_one h T j]
        _ = (1 - δ) ^ (m + 1) := by ring
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (by linarith : 1 - δ < 1)
  refine ⟨T * m, fun n hn => ?_⟩
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [closedMass_le_one h n j])]
  have hmono := closedMass_mono h j hn
  have := hgeom m
  simp only [e] at this
  linarith

end FiniteAbsorption

end CRNT
