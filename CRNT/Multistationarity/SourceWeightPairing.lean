import CRNT.Multistationarity.Discordance
import CRNT.Open.Augmentation

/-!
# Source-supported weight vectors and the concordance sign clauses

A **source weight** for a complex `y` is a nonnegative vector `p : S → ℝ` whose strict
support is exactly the support of `y`.  These are the vectors appearing in Shinar--Feinberg
weak normality (`SourceInfluence` in `CRNT.Multistationarity.WeakNormality`), but nothing
here depends on the analytic machinery imported by that file, so all of the combinatorial
sign analysis lives in this module.

Two facts are proved.

* **Sign clauses are automatic for pairings.**  For any source weight `p` and any `σ`, the
  scalar `p · σ` satisfies exactly the two sign clauses that a `ConcordanceWitness`
  demands of `α r` at the reaction with source `y`
  (`sign_match_of_pairing_ne_zero`, `sign_balance_of_pairing_eq_zero`).
* **Conversely the clauses are realizable.**  Whenever a scalar `a` satisfies those two
  clauses relative to `y` and `σ`, some source weight `p` has `p · σ = a` exactly
  (`exists_sourceWeight_pairing_eq`).

Together these say that, for a fixed `σ`, the admissible rate-displacement values at a
reaction are *precisely* the source-weight pairings with `σ`.  That is the bridge between
the sign-combinatorial definition of concordance and the linear algebra of the
weak-normality operator.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A nonnegative weight vector whose strict support is exactly the support of `y`. -/
def IsSourceWeight (y : Complex S) (p : S → ℝ) : Prop :=
  (∀ s, 0 ≤ p s) ∧ (∀ s, 0 < p s ↔ y s ≠ 0)

theorem IsSourceWeight.nonneg {y : Complex S} {p : S → ℝ}
    (h : IsSourceWeight y p) (s : S) : 0 ≤ p s := h.1 s

theorem IsSourceWeight.pos {y : Complex S} {p : S → ℝ}
    (h : IsSourceWeight y p) {s : S} (hs : y s ≠ 0) : 0 < p s := (h.2 s).2 hs

theorem IsSourceWeight.source_ne_zero {y : Complex S} {p : S → ℝ}
    (h : IsSourceWeight y p) {s : S} (hs : 0 < p s) : y s ≠ 0 := (h.2 s).1 hs

theorem IsSourceWeight.eq_zero {y : Complex S} {p : S → ℝ}
    (h : IsSourceWeight y p) {s : S} (hs : y s = 0) : p s = 0 := by
  have hnp : ¬ (0 < p s) := by
    intro hlt
    exact (h.source_ne_zero hlt) hs
  exact le_antisymm (not_lt.mp hnp) (h.nonneg s)

/-- **Clause (i) is automatic for source-weight pairings.**  If the pairing is nonzero then
some species in the source support carries the pairing's sign. -/
theorem sign_match_of_pairing_ne_zero {y : Complex S} {p σ : S → ℝ}
    (hp : IsSourceWeight y p) (hne : (∑ s : S, p s * σ s) ≠ 0) :
    ∃ s : S, y s ≠ 0 ∧ SignType.sign (σ s) = SignType.sign (∑ t : S, p t * σ t) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hex : ∃ s ∈ (Finset.univ : Finset S), p s * σ s < 0 := by
      by_contra hc
      push_neg at hc
      have hnn : 0 ≤ ∑ s : S, p s * σ s :=
        Finset.sum_nonneg fun s hs => hc s hs
      linarith
    obtain ⟨s, -, hs⟩ := hex
    have hps : 0 < p s := by
      rcases (hp.nonneg s).lt_or_eq with h | h
      · exact h
      · exfalso
        rw [← h, zero_mul] at hs
        exact lt_irrefl 0 hs
    have hσs : σ s < 0 := by
      by_contra hc
      push_neg at hc
      have := mul_nonneg (hp.nonneg s) hc
      linarith
    exact ⟨s, hp.source_ne_zero hps, by rw [sign_neg hσs, sign_neg hlt]⟩
  · have hex : ∃ s ∈ (Finset.univ : Finset S), 0 < p s * σ s := by
      by_contra hc
      push_neg at hc
      have hnp : ∑ s : S, p s * σ s ≤ 0 :=
        Finset.sum_nonpos fun s hs => hc s hs
      linarith
    obtain ⟨s, -, hs⟩ := hex
    have hps : 0 < p s := by
      rcases (hp.nonneg s).lt_or_eq with h | h
      · exact h
      · exfalso
        rw [← h, zero_mul] at hs
        exact lt_irrefl 0 hs
    have hσs : 0 < σ s := by
      by_contra hc
      push_neg at hc
      have := mul_nonpos_of_nonneg_of_nonpos (hp.nonneg s) hc
      linarith
    exact ⟨s, hp.source_ne_zero hps, by rw [sign_pos hσs, sign_pos hgt]⟩

/-- **Clause (ii) is automatic for source-weight pairings.**  If the pairing vanishes then
either `σ` vanishes on the source support or that support carries strictly opposite signs. -/
theorem sign_balance_of_pairing_eq_zero {y : Complex S} {p σ : S → ℝ}
    (hp : IsSourceWeight y p) (h0 : (∑ s : S, p s * σ s) = 0) :
    (∀ s : S, y s ≠ 0 → σ s = 0) ∨
      (∃ s s' : S, y s ≠ 0 ∧ y s' ≠ 0 ∧ σ s < 0 ∧ 0 < σ s') := by
  by_cases hall : ∀ s : S, y s ≠ 0 → σ s = 0
  · exact Or.inl hall
  · right
    push_neg at hall
    obtain ⟨s0, hs0, hσ0⟩ := hall
    have hp0 : 0 < p s0 := hp.pos hs0
    rcases lt_or_gt_of_ne hσ0 with hneg | hpos
    · -- `σ s0 < 0`: the vanishing sum must contain a strictly positive term
      have hex : ∃ s ∈ (Finset.univ : Finset S), 0 < p s * σ s := by
        by_contra hc
        push_neg at hc
        have hstrict : p s0 * σ s0 < 0 := mul_neg_of_pos_of_neg hp0 hneg
        have hsum : ∑ s : S, p s * σ s < 0 :=
          Finset.sum_neg' (fun s hs => hc s hs) ⟨s0, Finset.mem_univ s0, hstrict⟩
        rw [h0] at hsum
        exact lt_irrefl 0 hsum
      obtain ⟨s1, -, hs1⟩ := hex
      have hp1 : 0 < p s1 := by
        rcases (hp.nonneg s1).lt_or_eq with h | h
        · exact h
        · exfalso
          rw [← h, zero_mul] at hs1
          exact lt_irrefl 0 hs1
      have hσ1 : 0 < σ s1 := by
        by_contra hc
        push_neg at hc
        have := mul_nonpos_of_nonneg_of_nonpos (hp.nonneg s1) hc
        linarith
      exact ⟨s0, s1, hs0, hp.source_ne_zero hp1, hneg, hσ1⟩
    · -- `0 < σ s0`: the vanishing sum must contain a strictly negative term
      have hex : ∃ s ∈ (Finset.univ : Finset S), p s * σ s < 0 := by
        by_contra hc
        push_neg at hc
        have hstrict : 0 < p s0 * σ s0 := mul_pos hp0 hpos
        have hsum : 0 < ∑ s : S, p s * σ s :=
          Finset.sum_pos' (fun s hs => hc s hs) ⟨s0, Finset.mem_univ s0, hstrict⟩
        rw [h0] at hsum
        exact lt_irrefl 0 hsum
      obtain ⟨s1, -, hs1⟩ := hex
      have hp1 : 0 < p s1 := by
        rcases (hp.nonneg s1).lt_or_eq with h | h
        · exact h
        · exfalso
          rw [← h, zero_mul] at hs1
          exact lt_irrefl 0 hs1
      have hσ1 : σ s1 < 0 := by
        by_contra hc
        push_neg at hc
        have := mul_nonneg (hp.nonneg s1) hc
        linarith
      exact ⟨s1, s0, hp.source_ne_zero hp1, hs0, hσ1, hpos⟩

/-! ## Realizing a prescribed pairing value -/

/-- Sum of `σ` over the support of `y`. -/
def sourceSupportSum (y : Complex S) (σ : S → ℝ) : ℝ :=
  ∑ s : S, if y s = 0 then 0 else σ s

/-- The uniform source weight of height `δ`. -/
def uniformSourceWeight (y : Complex S) (δ : ℝ) : S → ℝ :=
  fun s => if y s = 0 then 0 else δ

/-- The uniform source weight of height `δ` with an extra nonnegative boost `t` on `s₀`. -/
def boostedSourceWeight (y : Complex S) (δ : ℝ) (s₀ : S) (t : ℝ) : S → ℝ :=
  fun s => (if y s = 0 then 0 else δ) + (if s = s₀ then t else 0)

theorem isSourceWeight_uniform (y : Complex S) {δ : ℝ} (hδ : 0 < δ) :
    IsSourceWeight y (uniformSourceWeight y δ) := by
  refine ⟨fun s => ?_, fun s => ?_⟩
  · simp only [uniformSourceWeight]
    split_ifs
    · exact le_refl 0
    · exact hδ.le
  · simp only [uniformSourceWeight]
    split_ifs with h
    · simp [h]
    · simp [h, hδ]

theorem isSourceWeight_boosted (y : Complex S) {δ t : ℝ} {s₀ : S}
    (hδ : 0 < δ) (ht : 0 ≤ t) (hs₀ : y s₀ ≠ 0) :
    IsSourceWeight y (boostedSourceWeight y δ s₀ t) := by
  refine ⟨fun s => ?_, fun s => ?_⟩
  · simp only [boostedSourceWeight]
    have h1 : 0 ≤ (if y s = 0 then 0 else δ) := by
      split_ifs
      · exact le_refl 0
      · exact hδ.le
    have h2 : 0 ≤ (if s = s₀ then t else 0) := by
      split_ifs
      · exact ht
      · exact le_refl 0
    linarith
  · simp only [boostedSourceWeight]
    by_cases h : y s = 0
    · have hne : s ≠ s₀ := by
        intro hEq
        rw [hEq] at h
        exact hs₀ h
      simp [h, hne]
    · have h1 : 0 ≤ (if s = s₀ then t else 0) := by
        split_ifs
        · exact ht
        · exact le_refl 0
      simp only [h, if_false]
      constructor
      · intro _; exact h
      · intro _; linarith

theorem uniform_pairing (y : Complex S) (σ : S → ℝ) (δ : ℝ) :
    (∑ s : S, uniformSourceWeight y δ s * σ s) = δ * sourceSupportSum y σ := by
  rw [sourceSupportSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [uniformSourceWeight]
  split_ifs
  · ring
  · ring

theorem boosted_pairing (y : Complex S) (σ : S → ℝ) (δ t : ℝ) (s₀ : S) :
    (∑ s : S, boostedSourceWeight y δ s₀ t s * σ s)
      = δ * sourceSupportSum y σ + t * σ s₀ := by
  have hsplit : ∀ s : S, boostedSourceWeight y δ s₀ t s * σ s
      = uniformSourceWeight y δ s * σ s + (if s = s₀ then t * σ s₀ else 0) := by
    intro s
    simp only [boostedSourceWeight, uniformSourceWeight, add_mul]
    rcases eq_or_ne s s₀ with h | h
    · subst h; simp
    · simp [h]
  rw [Finset.sum_congr rfl (fun s _ => hsplit s), Finset.sum_add_distrib,
    uniform_pairing]
  congr 1
  rw [Finset.sum_ite_eq' (Finset.univ : Finset S) s₀ (fun _ => t * σ s₀)]
  simp

/-- **Realization of a prescribed pairing value.**  If the scalar `a` satisfies the two
concordance sign clauses relative to the complex `y` and the species vector `σ`, then some
source weight for `y` pairs with `σ` to give exactly `a`.

Together with `sign_match_of_pairing_ne_zero` and `sign_balance_of_pairing_eq_zero` this
says the admissible rate displacements at a reaction are exactly the source-weight
pairings. -/
theorem exists_sourceWeight_pairing_eq (y : Complex S) (σ : S → ℝ) (a : ℝ)
    (h1 : a ≠ 0 → ∃ s : S, y s ≠ 0 ∧ SignType.sign (σ s) = SignType.sign a)
    (h2 : a = 0 → (∀ s : S, y s ≠ 0 → σ s = 0) ∨
      (∃ s s' : S, y s ≠ 0 ∧ y s' ≠ 0 ∧ σ s < 0 ∧ 0 < σ s')) :
    ∃ p : S → ℝ, IsSourceWeight y p ∧ (∑ s : S, p s * σ s) = a := by
  by_cases ha : a = 0
  · subst ha
    rcases h2 rfl with hzero | ⟨sm, sp, hsm, hsp, hσm, hσp⟩
    · refine ⟨uniformSourceWeight y 1, isSourceWeight_uniform y one_pos, ?_⟩
      rw [uniform_pairing]
      have hUz : sourceSupportSum y σ = 0 := by
        rw [sourceSupportSum]
        apply Finset.sum_eq_zero
        intro s _
        split_ifs with h
        · rfl
        · exact hzero s h
      rw [hUz, mul_zero]
    · rcases le_or_gt (sourceSupportSum y σ) 0 with hle | hgt
      · refine ⟨boostedSourceWeight y 1 sp (-sourceSupportSum y σ / σ sp),
          isSourceWeight_boosted y one_pos
            (div_nonneg (neg_nonneg.mpr hle) hσp.le) hsp, ?_⟩
        rw [boosted_pairing]
        field_simp
        ring
      · refine ⟨boostedSourceWeight y 1 sm (sourceSupportSum y σ / (-σ sm)),
          isSourceWeight_boosted y one_pos
            (div_pos hgt (by linarith)).le hsm, ?_⟩
        rw [boosted_pairing]
        have hne : σ sm ≠ 0 := ne_of_lt hσm
        field_simp
        ring
  · obtain ⟨s₀, hs₀, hsign⟩ := h1 ha
    have hA : 0 < |a| := abs_pos.mpr ha
    have hUnn : 0 ≤ |sourceSupportSum y σ| := abs_nonneg _
    set δ : ℝ := |a| / (2 * (|sourceSupportSum y σ| + 1)) with hδdef
    have hden : 0 < 2 * (|sourceSupportSum y σ| + 1) := by linarith
    have hδ : 0 < δ := div_pos hA hden
    have hprod : δ * (|sourceSupportSum y σ| + 1) = |a| / 2 := by
      rw [hδdef]
      field_simp
    have hsmall : δ * |sourceSupportSum y σ| ≤ |a| / 2 := by
      nlinarith [hδ, hUnn, hprod]
    have habs : |δ * sourceSupportSum y σ| < |a| := by
      rw [abs_mul, abs_of_pos hδ]
      linarith
    rcases lt_or_gt_of_ne ha with hneg | hpos
    · -- `a < 0`, so `σ s₀ < 0`
      have hσ0 : σ s₀ < 0 := by
        have : SignType.sign (σ s₀) = -1 := by
          rw [hsign, sign_neg hneg]
        exact sign_eq_neg_one_iff.mp this
      have hnum : a - δ * sourceSupportSum y σ < 0 := by
        have h1' : -(δ * sourceSupportSum y σ) ≤ |δ * sourceSupportSum y σ| :=
          neg_le_abs _
        have h2' : |a| = -a := abs_of_neg hneg
        linarith
      refine ⟨boostedSourceWeight y δ s₀ ((a - δ * sourceSupportSum y σ) / σ s₀),
        isSourceWeight_boosted y hδ (div_pos_of_neg_of_neg hnum hσ0).le hs₀, ?_⟩
      rw [boosted_pairing]
      have hne : σ s₀ ≠ 0 := ne_of_lt hσ0
      field_simp
      ring
    · -- `0 < a`, so `0 < σ s₀`
      have hσ0 : 0 < σ s₀ := by
        have : SignType.sign (σ s₀) = 1 := by
          rw [hsign, sign_pos hpos]
        exact sign_eq_one_iff.mp this
      have hnum : 0 < a - δ * sourceSupportSum y σ := by
        have h1' : δ * sourceSupportSum y σ ≤ |δ * sourceSupportSum y σ| := le_abs_self _
        have h2' : |a| = a := abs_of_pos hpos
        linarith
      refine ⟨boostedSourceWeight y δ s₀ ((a - δ * sourceSupportSum y σ) / σ s₀),
        isSourceWeight_boosted y hδ (div_pos hnum hσ0).le hs₀, ?_⟩
      rw [boosted_pairing]
      have hne : σ s₀ ≠ 0 := ne_of_gt hσ0
      field_simp
      ring

/-! ## Source-weight families and the fully open extension -/

/-- One source weight per reaction.  This is the raw-vector form of
`SourceInfluenceFamily`. -/
def IsSourceWeightFamily (N : Network S) (p : N.R → S → ℝ) : Prop :=
  ∀ r : N.R, IsSourceWeight (N.reaction r).source (p r)

/-- The weak-normality operator of a raw source-weight family:
`T̄ σ = Σ_r (p_r · σ) ν_r`. -/
noncomputable def rawWeakNormalityOperator (N : Network S) (p : N.R → S → ℝ)
    (σ : S → ℝ) : S → ℝ :=
  ∑ r : N.R, (∑ s : S, p r s * σ s) • N.reactionVector r

theorem rawWeakNormalityOperator_apply (N : Network S) (p : N.R → S → ℝ)
    (σ : S → ℝ) (s' : S) :
    N.rawWeakNormalityOperator p σ s'
      = ∑ r : N.R, (∑ s : S, p r s * σ s) * N.reactionVector r s' := by
  simp [rawWeakNormalityOperator, Finset.sum_apply]

@[simp] theorem reactionVector_fullyOpen_inl (N : Network S) (r : N.R) :
    N.fullyOpen.reactionVector (Sum.inl r) = N.reactionVector r := rfl

/-- **Diagonal-eigenpair criterion for fully open discordance.**  If some source-weight
family `p`, some nonzero `σ` and some strictly positive `d` satisfy `T̄_p σ = d ⊙ σ`, then
the fully open extension is discordant.

The rate displacement is `p_r · σ` on the original reactions, `0` on the inflows and
`d_s σ_s` on the outflow of `s`; the kernel condition is exactly the eigenrelation, and the
sign clauses hold automatically by `sign_match_of_pairing_ne_zero` and
`sign_balance_of_pairing_eq_zero` at the original reactions, vacuously at the inflows (whose
source support is empty), and by `d_s > 0` at the outflows (whose source support is the
single species `s`). -/
theorem discordant_fullyOpen_of_diagonalPair (N : Network S)
    {p : N.R → S → ℝ} (hp : N.IsSourceWeightFamily p)
    {σ d : S → ℝ} (hσ : σ ≠ 0) (hd : ∀ s : S, 0 < d s)
    (heq : N.rawWeakNormalityOperator p σ = fun s => d s * σ s) :
    N.fullyOpen.Discordant := by
  classical
  set α : N.fullyOpen.R → ℝ :=
    Sum.elim (fun r : N.R => ∑ s : S, p r s * σ s)
      (Sum.elim (fun _ : S => (0 : ℝ)) (fun s : S => d s * σ s)) with hα
  rw [discordant_iff_exists_witness]
  refine ⟨α, σ, ?_, ?_, hσ, ?_, ?_⟩
  · -- kernel condition
    apply Network.inKerL_of_apply
    intro s'
    show ∑ r : N.R ⊕ S ⊕ S, α r * N.fullyOpen.reactionVector r s' = 0
    rw [Fintype.sum_sum_type]
    have hleft : ∑ r : N.R, α (Sum.inl r) * N.fullyOpen.reactionVector (Sum.inl r) s'
        = d s' * σ s' := by
      have := congrFun heq s'
      rw [rawWeakNormalityOperator_apply] at this
      simpa [hα] using this
    have hright : ∑ x : S ⊕ S, α (Sum.inr x) * N.fullyOpen.reactionVector (Sum.inr x) s'
        = -(d s' * σ s') := by
      rw [Fintype.sum_sum_type]
      have h0 : ∑ s : S, α (Sum.inr (Sum.inl s)) *
          N.fullyOpen.reactionVector (Sum.inr (Sum.inl s)) s' = 0 := by
        apply Finset.sum_eq_zero
        intro s _
        simp [hα]
      have h1 : ∑ s : S, α (Sum.inr (Sum.inr s)) *
          N.fullyOpen.reactionVector (Sum.inr (Sum.inr s)) s' = -(d s' * σ s') := by
        have hterm : ∀ s : S, α (Sum.inr (Sum.inr s)) *
            N.fullyOpen.reactionVector (Sum.inr (Sum.inr s)) s'
            = if s = s' then -(d s' * σ s') else 0 := by
          intro s
          rw [reactionVector_outflow]
          rcases eq_or_ne s s' with h | h
          · subst h
            simp [hα]
          · simp [hα, h, Ne.symm h]
        rw [Finset.sum_congr rfl (fun s _ => hterm s)]
        simp
      rw [h0, h1, zero_add]
    rw [hleft, hright]
    ring
  · rw [stoichSubspace_fullyOpen_eq_top]
    exact Submodule.mem_top
  · -- clause (i)
    intro r hrne
    cases r with
    | inl r =>
      have hmatch := sign_match_of_pairing_ne_zero (hp r) (by simpa [hα] using hrne)
      obtain ⟨s, hs, hsg⟩ := hmatch
      exact ⟨s, hs, by simpa [hα] using hsg⟩
    | inr x =>
      cases x with
      | inl s => exact absurd (by simp [hα] : α (Sum.inr (Sum.inl s)) = 0) hrne
      | inr s =>
        refine ⟨s, by simp [outflowReaction], ?_⟩
        simp only [hα, Sum.elim_inr]
        have hdσ : SignType.sign (d s * σ s) = SignType.sign (σ s) := by
          rcases lt_trichotomy (σ s) 0 with h | h | h
          · rw [sign_neg h, sign_neg (mul_neg_of_pos_of_neg (hd s) h)]
          · rw [h, mul_zero]
          · rw [sign_pos h, sign_pos (mul_pos (hd s) h)]
        rw [hdσ]
  · -- clause (ii)
    intro r hr0
    cases r with
    | inl r =>
      have := sign_balance_of_pairing_eq_zero (hp r) (by simpa [hα] using hr0)
      simpa [hα] using this
    | inr x =>
      cases x with
      | inl s =>
        left
        intro s' hs'
        exact absurd (by simp [inflowReaction] : (N.fullyOpen.reaction
          (Sum.inr (Sum.inl s))).source s' = 0) hs'
      | inr s =>
        left
        have hσs : σ s = 0 := by
          have h := hr0
          simp only [hα, Sum.elim_inr] at h
          rcases mul_eq_zero.mp h with h' | h'
          · exact absurd h' (ne_of_gt (hd s))
          · exact h'
        intro s' hs'
        have : s' = s := by
          by_contra hne
          simp [outflowReaction, singletonComplex_apply, hne] at hs'
        rw [this, hσs]

/-- Only the species `s` lies in the source support of the outflow of `s`. -/
theorem outflow_source_ne_zero_iff (s s' : S) :
    (outflowReaction s).source s' ≠ 0 ↔ s' = s := by
  simp only [outflowReaction, singletonComplex_apply]
  split_ifs with h
  · simp [h]
  · simp [h]

/-- The inflow source support is empty. -/
theorem inflow_source_eq_zero (s s' : S) : (inflowReaction s).source s' = 0 := rfl

/-- Splitting the fully open kernel condition: once the inflow displacements vanish, the
original-reaction part of the kernel sum is the outflow displacement, coordinatewise. -/
theorem fullyOpen_kerL_split (N : Network S) {α : N.fullyOpen.R → ℝ}
    (hker : N.fullyOpen.InKerL α) (hin : ∀ s : S, α (Sum.inr (Sum.inl s)) = 0)
    (s' : S) :
    (∑ r : N.R, α (Sum.inl r) * N.reactionVector r s') = α (Sum.inr (Sum.inr s')) := by
  classical
  have h := Network.inKerL_apply hker s'
  rw [show (∑ r : N.fullyOpen.R, α r * N.fullyOpen.reactionVector r s')
      = ∑ r : N.R ⊕ S ⊕ S, α r * N.fullyOpen.reactionVector r s' from rfl,
    Fintype.sum_sum_type, Fintype.sum_sum_type] at h
  have h0 : ∑ s : S, α (Sum.inr (Sum.inl s)) *
      N.fullyOpen.reactionVector (Sum.inr (Sum.inl s)) s' = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    rw [hin s, zero_mul]
  have h1 : ∑ s : S, α (Sum.inr (Sum.inr s)) *
      N.fullyOpen.reactionVector (Sum.inr (Sum.inr s)) s' = -α (Sum.inr (Sum.inr s')) := by
    have hterm : ∀ s : S, α (Sum.inr (Sum.inr s)) *
        N.fullyOpen.reactionVector (Sum.inr (Sum.inr s)) s'
        = if s = s' then -α (Sum.inr (Sum.inr s')) else 0 := by
      intro s
      rw [reactionVector_outflow]
      rcases eq_or_ne s s' with hh | hh
      · subst hh
        simp
      · simp [hh, Ne.symm hh]
    rw [Finset.sum_congr rfl (fun s _ => hterm s)]
    simp
  rw [h0, h1] at h
  have hleft : ∑ r : N.R, α (Sum.inl r) * N.fullyOpen.reactionVector (Sum.inl r) s'
      = ∑ r : N.R, α (Sum.inl r) * N.reactionVector r s' := rfl
  rw [hleft] at h
  linarith

/-- **Converse of the diagonal-eigenpair criterion.**  A discordance witness for the fully
open extension can be reorganized into a source-weight family together with a genuine
positive-diagonal eigenrelation for its weak-normality operator. -/
theorem exists_diagonalPair_of_discordant_fullyOpen (N : Network S)
    (h : N.fullyOpen.Discordant) :
    ∃ (p : N.R → S → ℝ) (σ d : S → ℝ),
      N.IsSourceWeightFamily p ∧ σ ≠ 0 ∧ (∀ s : S, 0 < d s) ∧
        N.rawWeakNormalityOperator p σ = fun s => d s * σ s := by
  classical
  rw [discordant_iff_exists_witness] at h
  obtain ⟨α, σ, hW⟩ := h
  -- realize each original-reaction displacement as a source-weight pairing
  have hrep : ∀ r : N.R, ∃ q : S → ℝ, IsSourceWeight (N.reaction r).source q ∧
      (∑ s : S, q s * σ s) = α (Sum.inl r) := by
    intro r
    refine exists_sourceWeight_pairing_eq _ _ _ (fun hne => ?_) (fun h0 => ?_)
    · exact hW.sign_match (Sum.inl r) hne
    · exact hW.sign_balance (Sum.inl r) h0
  choose p hp hpair using hrep
  -- inflow displacements vanish: their source support is empty
  have hin : ∀ s : S, α (Sum.inr (Sum.inl s)) = 0 := by
    intro s
    by_contra hne
    obtain ⟨s', hs', -⟩ := hW.sign_match (Sum.inr (Sum.inl s)) hne
    exact hs' (inflow_source_eq_zero s s')
  -- outflow displacements share the sign of `σ`, coordinatewise
  have hsign : ∀ s : S, α (Sum.inr (Sum.inr s)) ≠ 0 →
      SignType.sign (σ s) = SignType.sign (α (Sum.inr (Sum.inr s))) := by
    intro s hne
    obtain ⟨s', hs', hsg⟩ := hW.sign_match (Sum.inr (Sum.inr s)) hne
    have hEq : s' = s := (outflow_source_ne_zero_iff s s').1 hs'
    rw [hEq] at hsg
    exact hsg
  have hzero : ∀ s : S, σ s = 0 → α (Sum.inr (Sum.inr s)) = 0 := by
    intro s hσs
    by_contra hne
    have hs := hsign s hne
    rw [hσs, sign_zero] at hs
    exact hne (sign_eq_zero_iff.mp hs.symm)
  refine ⟨p, σ, fun s => if σ s = 0 then 1 else α (Sum.inr (Sum.inr s)) / σ s,
    hp, hW.sigma_ne, ?_, ?_⟩
  · intro s
    by_cases hσs : σ s = 0
    · simp [hσs]
    · simp only [hσs, if_false]
      have hαne : α (Sum.inr (Sum.inr s)) ≠ 0 := by
        intro hh
        rcases hW.sign_balance (Sum.inr (Sum.inr s)) hh with hall | hopp
        · exact hσs (hall s ((outflow_source_ne_zero_iff s s).2 rfl))
        · obtain ⟨u, v, hu, hv, hun, hvp⟩ := hopp
          have hu' : u = s := (outflow_source_ne_zero_iff s u).1 hu
          have hv' : v = s := (outflow_source_ne_zero_iff s v).1 hv
          rw [hu'] at hun
          rw [hv'] at hvp
          linarith
      have hs := hsign s hαne
      rcases lt_trichotomy (σ s) 0 with hlt | he | hgt
      · rw [sign_neg hlt] at hs
        exact div_pos_of_neg_of_neg (sign_eq_neg_one_iff.mp hs.symm) hlt
      · exact absurd he hσs
      · rw [sign_pos hgt] at hs
        exact div_pos (sign_eq_one_iff.mp hs.symm) hgt
  · funext s'
    rw [rawWeakNormalityOperator_apply]
    rw [Finset.sum_congr rfl (fun r _ => by rw [hpair r] :
      ∀ r ∈ (Finset.univ : Finset N.R), (∑ s : S, p r s * σ s) * N.reactionVector r s'
        = α (Sum.inl r) * N.reactionVector r s')]
    rw [N.fullyOpen_kerL_split hW.mem_kerL hin s']
    by_cases hσs : σ s' = 0
    · rw [hzero s' hσs, hσs]
      simp
    · simp only [hσs, if_false]
      field_simp

/-- **Fully open discordance is a positive-diagonal eigenvalue problem.**  The fully open
extension of `N` is discordant exactly when some source-weight family's weak-normality
operator carries a nonzero vector to a strictly positive rescaling of itself.

This replaces the sign-combinatorial definition of concordance for `N.fullyOpen` by a
statement of linear algebra about `N`. -/
theorem discordant_fullyOpen_iff (N : Network S) :
    N.fullyOpen.Discordant ↔
      ∃ (p : N.R → S → ℝ) (σ d : S → ℝ),
        N.IsSourceWeightFamily p ∧ σ ≠ 0 ∧ (∀ s : S, 0 < d s) ∧
          N.rawWeakNormalityOperator p σ = fun s => d s * σ s := by
  constructor
  · exact N.exists_diagonalPair_of_discordant_fullyOpen
  · rintro ⟨p, σ, d, hp, hσ, hd, heq⟩
    exact N.discordant_fullyOpen_of_diagonalPair hp hσ hd heq

/-- Concordance of the fully open extension, as the absence of positive-diagonal
eigenrelations. -/
theorem concordant_fullyOpen_iff (N : Network S) :
    N.fullyOpen.Concordant ↔
      ∀ (p : N.R → S → ℝ) (σ d : S → ℝ),
        N.IsSourceWeightFamily p → σ ≠ 0 → (∀ s : S, 0 < d s) →
          N.rawWeakNormalityOperator p σ ≠ fun s => d s * σ s := by
  constructor
  · intro hcon p σ d hp hσ hd heq
    exact (N.discordant_fullyOpen_of_diagonalPair hp hσ hd heq) hcon
  · intro hall
    by_contra hcon
    obtain ⟨p, σ, d, hp, hσ, hd, heq⟩ :=
      N.exists_diagonalPair_of_discordant_fullyOpen hcon
    exact hall p σ d hp hσ hd heq

/-- A positive real eigenvalue of any source-weight operator already forces fully open
discordance: take the diagonal to be constant. -/
theorem discordant_fullyOpen_of_positive_eigenvalue (N : Network S)
    {p : N.R → S → ℝ} (hp : N.IsSourceWeightFamily p)
    {σ : S → ℝ} (hσ : σ ≠ 0) {μ : ℝ} (hμ : 0 < μ)
    (heq : N.rawWeakNormalityOperator p σ = fun s => μ * σ s) :
    N.fullyOpen.Discordant :=
  N.discordant_fullyOpen_of_diagonalPair hp hσ (fun _ => hμ) heq

/-- **Spectral consequence of fully open concordance.**  If the fully open extension of `N`
is concordant then no weak-normality operator of `N` has a positive real eigenvalue. -/
theorem no_positive_eigenvalue_of_concordant_fullyOpen (N : Network S)
    (hcon : N.fullyOpen.Concordant)
    {p : N.R → S → ℝ} (hp : N.IsSourceWeightFamily p)
    {σ : S → ℝ} (hσ : σ ≠ 0) {μ : ℝ} (hμ : 0 < μ) :
    N.rawWeakNormalityOperator p σ ≠ fun s => μ * σ s := by
  intro heq
  exact (N.discordant_fullyOpen_of_positive_eigenvalue hp hσ hμ heq) hcon

end Network
end CRNT
