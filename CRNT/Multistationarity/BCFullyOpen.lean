import CRNT.Multistationarity.BCIntersectionCert
import CRNT.Multistationarity.BCColumnExpansion
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The true-SR criterion implies strong concordance of the fully open extension

This module proves the true-chemistry species--reaction-graph theorem by the Banaji--Craciun
determinant argument (M. Banaji and G. Craciun, *Graph-theoretic approaches to injectivity and
multiple equilibria in systems of interacting elements*, Commun. Math. Sci. 7 (2009); the
argument there is phrased for `P₀`-matrices).

**Reduction (`det_bcProduct_eq_zero_of_witness`).**  A strong-concordance witness `(α, σ)` of
`N.fullyOpen` yields nonnegative weights `w` and a positive diagonal `d` such that
`(A * B) σ = 0`, where `A = [Γ | I]` is the stoichiometric matrix augmented by the identity and
`B k t = w k t * A t k`.  The outflow clauses of the witness force `d > 0`; each internal rate
displacement `α r` is rewritten as `-∑ s, w r s * Γ s r * σ s`.

**Positivity (`det_bcProduct_pos`).**  By the column expansion `det (A * B)` is a sum of
nonnegative monomials in `w` times the coefficients `(∏ t, G t t) * det G`, `G = A.submatrix id f`,
and the identity term contributes `∏ d > 0`.  Each coefficient is nonnegative
(`bc_coeff_nonneg`): after normalizing `G` to unit diagonal, a cyclic permutation of nonzero
weight is a true-SR cycle (`CycleChannels`); a negative weight forces an even cycle, condition
(i) makes it an s-cycle, hence its weight is `-1`; condition (ii) forbids two distinct negative
cycles from meeting (`CyclePair.sToRIntersection`); and `DetCycle.det_nonneg_of_negCycles`
concludes.

Nothing here is an axiom or a `sorry`.
-/

open Equiv Finset

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## The augmented stoichiometric matrix -/

/-- `A = [Γ | I]`, rows indexed by species, columns by channels and species. -/
def bcMatrix (N : Network S) : Matrix S (N.R ⊕ S) ℝ :=
  fun s k => Sum.elim (fun r => N.reactionVector r s) (fun t => if s = t then 1 else 0) k

@[simp] theorem bcMatrix_inl (N : Network S) (s : S) (r : N.R) :
    N.bcMatrix s (Sum.inl r) = N.reactionVector r s := rfl

@[simp] theorem bcMatrix_inr (N : Network S) (s t : S) :
    N.bcMatrix s (Sum.inr t) = if s = t then 1 else 0 := rfl

/-- The hypothesis `ZeroComplexReactionsAreFlows`, inlined. -/
def FlowsAreSingletons (N : Network S) : Prop :=
  ∀ r, N.IsFlowChannel r →
    (∃ s : S, N.reaction r = inflowReaction s) ∨ (∃ s : S, N.reaction r = outflowReaction s)

/-- A flow channel has at most one species with nonzero stoichiometry. -/
theorem eq_of_flow_coeff_ne (N : Network S) (hflow : N.FlowsAreSingletons) {r : N.R}
    (hr : N.IsFlowChannel r) {s t : S} (hs : N.reactionVector r s ≠ 0)
    (ht : N.reactionVector r t ≠ 0) : s = t := by
  rcases hflow r hr with ⟨u, hu⟩ | ⟨u, hu⟩
  · have hs' := hs; have ht' := ht
    simp only [reactionVector_apply, hu, inflowReaction, singletonComplex_apply,
      Complex.zero_apply] at hs' ht'
    split_ifs at hs' ht' with h1 h2 <;> simp_all
  · have hs' := hs; have ht' := ht
    simp only [reactionVector_apply, hu, outflowReaction, singletonComplex_apply,
      Complex.zero_apply] at hs' ht'
    split_ifs at hs' ht' with h1 h2 <;> simp_all

/-! ## The normalized minor -/

/-- The square submatrix selected by `f`. -/
def bcG (N : Network S) (f : S → N.R ⊕ S) : Matrix S S ℝ := N.bcMatrix.submatrix id f

/-- Its normalization to unit diagonal. -/
noncomputable def bcH (N : Network S) (f : S → N.R ⊕ S) : Matrix S S ℝ :=
  Matrix.of fun s t => N.bcG f s t / N.bcG f t t

/-- The channel read off `f` (with an arbitrary fallback on identity columns). -/
noncomputable def bcCh (N : Network S) [Nonempty N.R] (f : S → N.R ⊕ S) : S → N.R :=
  fun t => Sum.elim id (fun _ => Classical.arbitrary N.R) (f t)

section Minor

variable (N : Network S) (f : S → N.R ⊕ S)

theorem bcG_apply (s t : S) : N.bcG f s t = N.bcMatrix s (f t) := rfl

theorem bcH_diag (hz : ∀ t, N.bcG f t t ≠ 0) (t : S) : N.bcH f t t = 1 := by
  simp [bcH, div_self (hz t)]

theorem bcG_eq_mul (hz : ∀ t, N.bcG f t t ≠ 0) :
    N.bcG f = N.bcH f * Matrix.diagonal (fun t => N.bcG f t t) := by
  ext s t
  rw [Matrix.mul_diagonal]
  simp [bcH, div_mul_cancel₀ _ (hz t)]

/-- On the support of a nonzero-weight cycle the columns are internal channels. -/
theorem col_inl_of_ne (hz : ∀ t, N.bcG f t t ≠ 0) {y : S} (hy : (f y).isRight → False)
    : ∃ r, f y = Sum.inl r := by
  cases h : f y with
  | inl r => exact ⟨r, rfl⟩
  | inr t => exact absurd (by rw [h]; rfl) hy

theorem exists_inl_of_offdiag_ne (hz : ∀ t, N.bcG f t t ≠ 0) {y x : S} (hxy : x ≠ y)
    (hne : N.bcG f x y ≠ 0) : ∃ r, f y = Sum.inl r := by
  cases h : f y with
  | inl r => exact ⟨r, rfl⟩
  | inr t =>
    exfalso
    have h1 := hz y
    rw [bcG_apply, h, bcMatrix_inr] at h1 hne
    split_ifs at h1 hne with ha hb <;> simp_all

variable [Nonempty N.R]

theorem bcCh_spec {y : S} {r : N.R} (h : f y = Sum.inl r) : N.bcCh f y = r := by
  simp [bcCh, h]

/-- **A cyclic permutation of nonzero weight is admissible.** -/
theorem cycleChannels_of_weight_ne (hflow : N.FlowsAreSingletons)
    (hz : ∀ t, N.bcG f t t ≠ 0)
    (hcol : ∀ a b, a ≠ b → ∀ r q, f a = Sum.inl r → f b = Sum.inl q → ¬ N.SameTrueReaction r q)
    {c : Perm S} (hc : c.IsCycle) (hw : DetCycle.permWeight (N.bcH f) c ≠ 0) :
    N.CycleChannels c (N.bcCh f) ∧
      (∀ y ∈ c.support, f y = Sum.inl (N.bcCh f y)) ∧
      DetCycle.permWeight (N.bcH f) c = ((Perm.sign c : ℤ) : ℝ) *
        ∏ y ∈ c.support, (N.reactionVector (N.bcCh f y) (c y) /
          N.reactionVector (N.bcCh f y) y) := by
  classical
  have hprod : ∏ i, N.bcH f (c i) i = ∏ y ∈ c.support, N.bcH f (c y) y := by
    symm
    apply Finset.prod_subset (Finset.subset_univ _)
    intro i _ hi
    rw [Perm.notMem_support.mp hi, N.bcH_diag f hz]
  have hw' : ∏ y ∈ c.support, N.bcH f (c y) y ≠ 0 := by
    intro h0
    apply hw
    unfold DetCycle.permWeight
    rw [hprod, h0, mul_zero]
  have hfac : ∀ y ∈ c.support, N.bcH f (c y) y ≠ 0 := fun y hy =>
    (Finset.prod_ne_zero_iff.mp hw') y hy
  have hG : ∀ y ∈ c.support, N.bcG f (c y) y ≠ 0 := by
    intro y hy h0
    apply hfac y hy
    simp [bcH, h0]
  have hinl : ∀ y ∈ c.support, f y = Sum.inl (N.bcCh f y) := by
    intro y hy
    obtain ⟨r, hr⟩ := N.exists_inl_of_offdiag_ne f hz (Perm.mem_support.mp hy) (hG y hy)
    rw [hr, N.bcCh_spec f hr]
  have hself : ∀ y ∈ c.support, N.reactionVector (N.bcCh f y) y ≠ 0 := by
    intro y hy
    have h1 := hz y
    rwa [bcG_apply, hinl y hy, bcMatrix_inl] at h1
  have hnext : ∀ y ∈ c.support, N.reactionVector (N.bcCh f y) (c y) ≠ 0 := by
    intro y hy
    have h1 := hG y hy
    rwa [bcG_apply, hinl y hy, bcMatrix_inl] at h1
  refine ⟨⟨hc, ?_, hself, hnext, ?_⟩, hinl, ?_⟩
  · intro y hy hfl
    exact Perm.mem_support.mp hy
      (N.eq_of_flow_coeff_ne hflow hfl (hnext y hy) (hself y hy))
  · intro y hy y' hy' hcls
    by_contra hne
    exact hcol y y' hne _ _ (hinl y hy) (hinl y' hy') (Quotient.exact hcls)
  · unfold DetCycle.permWeight
    rw [hprod]
    congr 1
    refine Finset.prod_congr rfl (fun y hy => ?_)
    simp only [bcH, Matrix.of_apply, bcG_apply, hinl y hy, bcMatrix_inl]

/-- **The normalized minor has nonnegative determinant under the true-SR criterion.** -/
theorem det_bcH_nonneg (hsep : N.ReactantProductSeparated) (hflow : N.FlowsAreSingletons)
    (hSR : N.TrueSRStrongCriterion) (hz : ∀ t, N.bcG f t t ≠ 0)
    (hcol : ∀ a b, a ≠ b → ∀ r q, f a = Sum.inl r → f b = Sum.inl q →
      ¬ N.SameTrueReaction r q) :
    0 ≤ (N.bcH f).det := by
  classical
  apply DetCycle.det_nonneg_of_negCycles _ (N.bcH_diag f hz)
  · intro c hc hneg
    obtain ⟨hch, -, hweq⟩ := N.cycleChannels_of_weight_ne f hflow hz hcol hc (ne_of_lt hneg)
    obtain ⟨x₀, hx₀⟩ : ∃ x, x ∈ c.support := hc.nonempty_support
    rw [hweq] at hneg ⊢
    have heven := hch.even_of_weight_neg hsep hx₀ hneg
    exact hch.weight_eq_neg_one_of_sCycle hsep hx₀ heven (hSR.1 _ heven)
  · intro c d hc hd hcneg hdneg hne
    by_contra hdisj
    obtain ⟨x, hxc, hxd⟩ : ∃ x, c x ≠ x ∧ d x ≠ x := by
      unfold Perm.Disjoint at hdisj
      push_neg at hdisj
      exact hdisj
    obtain ⟨hcc, hcinl, hcw⟩ :=
      N.cycleChannels_of_weight_ne f hflow hz hcol hc (ne_of_lt hcneg)
    obtain ⟨hdc, hdinl, hdw⟩ :=
      N.cycleChannels_of_weight_ne f hflow hz hcol hd (ne_of_lt hdneg)
    have hxc' : x ∈ c.support := Perm.mem_support.mpr hxc
    have hxd' : x ∈ d.support := Perm.mem_support.mpr hxd
    have P : N.CyclePair c d (N.bcCh f) := by
      refine ⟨hcc, hdc, ?_, hne⟩
      intro y hy y' hy' hcls
      by_contra hyy
      exact hcol y y' hyy _ _ (hcinl y hy) (hdinl y' hy') (Quotient.exact hcls)
    rw [hcw] at hcneg
    rw [hdw] at hdneg
    have hCe := hcc.even_of_weight_neg hsep hxc' hcneg
    have hDe := hdc.even_of_weight_neg hsep hxd' hdneg
    exact hSR.2 _ _ hCe hDe ⟨P.sToRIntersection hxc' hxd' ⟨x, hxc', hxd'⟩⟩

end Minor

/-- Columns of the same true-reaction class are proportional, so the minor vanishes. -/
theorem det_bcG_eq_zero_of_sameClass (N : Network S) (f : S → N.R ⊕ S) {a b : S}
    (hab : a ≠ b) {r q : N.R} (ha : f a = Sum.inl r) (hb : f b = Sum.inl q)
    (hrq : N.SameTrueReaction r q) : (N.bcG f).det = 0 := by
  rcases hrq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · apply Matrix.det_zero_of_column_eq hab
    intro k
    simp [bcG_apply, ha, hb, reactionVector_apply, h1, h2]
  · have hcol : (fun k => N.bcG f k b) = (-1 : ℝ) • (fun k => N.bcG f k a) := by
      funext k
      simp only [bcG_apply, ha, hb, bcMatrix_inl, reactionVector_apply, Pi.smul_apply,
        smul_eq_mul, h1, h2]
      ring
    have hupd : N.bcG f = Matrix.updateCol (N.bcG f) b ((-1 : ℝ) • fun k => N.bcG f k a) := by
      rw [← hcol]
      ext i j
      by_cases hj : j = b
      · subst hj; simp
      · simp [Matrix.updateCol_apply, hj]
    rw [hupd, Matrix.det_updateCol_smul]
    have : (Matrix.updateCol (N.bcG f) b fun k => N.bcG f k a).det = 0 := by
      apply Matrix.det_zero_of_column_eq hab
      intro k
      simp [Matrix.updateCol_apply, hab]
    rw [this, mul_zero]

/-- **Every coefficient of the column expansion is nonnegative.** -/
theorem bc_coeff_nonneg (N : Network S) (hsep : N.ReactantProductSeparated)
    (hflow : N.FlowsAreSingletons) (hSR : N.TrueSRStrongCriterion) (f : S → N.R ⊕ S) :
    0 ≤ (∏ t, N.bcMatrix t (f t)) * (N.bcMatrix.submatrix id f).det := by
  classical
  change 0 ≤ (∏ t, N.bcG f t t) * (N.bcG f).det
  by_cases hz : ∃ t, N.bcG f t t = 0
  · obtain ⟨t, ht⟩ := hz
    rw [Finset.prod_eq_zero (f := fun u => N.bcG f u u) (Finset.mem_univ t) ht, zero_mul]
  push_neg at hz
  by_cases hcolex : ∃ a b, a ≠ b ∧ ∃ r q, f a = Sum.inl r ∧ f b = Sum.inl q ∧
      N.SameTrueReaction r q
  · obtain ⟨a, b, hab, r, q, ha, hb, hrq⟩ := hcolex
    rw [N.det_bcG_eq_zero_of_sameClass f hab ha hb hrq, mul_zero]
  push_neg at hcolex
  have hcol : ∀ a b, a ≠ b → ∀ r q, f a = Sum.inl r → f b = Sum.inl q →
      ¬ N.SameTrueReaction r q := fun a b hab r q ha hb => hcolex a b hab r q ha hb
  rcases isEmpty_or_nonempty N.R with hR | hR
  · -- only identity columns: the minor is the identity
    have hf : ∀ t, f t = Sum.inr t := by
      intro t
      cases h : f t with
      | inl r => exact (hR.false r).elim
      | inr u =>
        have h1 := hz t
        rw [bcG_apply, h, bcMatrix_inr] at h1
        split_ifs at h1 with hu
        · rw [hu]
        · exact absurd rfl h1
    have hG : N.bcG f = 1 := by
      ext s t
      simp [bcG_apply, hf, Matrix.one_apply]
    rw [hG, Matrix.det_one, mul_one]
    exact Finset.prod_nonneg fun t _ => by simp
  · have hdet : (N.bcG f).det = (N.bcH f).det * ∏ t, N.bcG f t t := by
      conv_lhs => rw [N.bcG_eq_mul f hz]
      rw [Matrix.det_mul, Matrix.det_diagonal]
    rw [hdet]
    have hH := N.det_bcH_nonneg f hsep hflow hSR hz hcol
    have : (∏ t, N.bcG f t t) * ((N.bcH f).det * ∏ t, N.bcG f t t) =
        ((∏ t, N.bcG f t t) ^ 2) * (N.bcH f).det := by ring
    rw [this]
    exact mul_nonneg (sq_nonneg _) hH

/-! ## From a strong-concordance witness to a singular product -/

section Witness

variable {N : Network S}

theorem sign_mul_pos {x y : ℝ} (hy : y ≠ 0) (h : SignType.sign x = SignType.sign y) :
    0 < x * y := by
  rcases lt_or_gt_of_ne hy with hy' | hy'
  · rw [sign_neg hy', sign_eq_neg_one_iff] at h
    exact mul_pos_of_neg_of_neg h hy'
  · rw [sign_pos hy', sign_eq_one_iff] at h
    exact mul_pos h hy'

theorem sign_mul_neg {x y : ℝ} (hy : y ≠ 0) (h : SignType.sign x = -SignType.sign y) :
    x * y < 0 := by
  rcases lt_or_gt_of_ne hy with hy' | hy'
  · rw [sign_neg hy', neg_neg, sign_eq_one_iff] at h
    exact mul_neg_of_pos_of_neg h hy'
  · rw [sign_pos hy', sign_eq_neg_one_iff] at h
    exact mul_neg_of_neg_of_pos h hy'

theorem dir_outflow (s t : S) :
    N.fullyOpen.reactionDirectionSign (Sum.inr (Sum.inr s)) t = if t = s then 1 else 0 := by
  simp only [reactionDirectionSign, fullyOpen_reaction_outflow, outflowReaction,
    singletonComplex_apply, Complex.zero_apply]
  split_ifs <;> simp

theorem dir_inflow (s t : S) :
    N.fullyOpen.reactionDirectionSign (Sum.inr (Sum.inl s)) t =
      -(if t = s then 1 else 0) := by
  simp only [reactionDirectionSign, fullyOpen_reaction_inflow, inflowReaction,
    singletonComplex_apply, Complex.zero_apply]
  split_ifs <;> simp

theorem dir_inl (r : N.R) (t : S) :
    N.fullyOpen.reactionDirectionSign (Sum.inl r) t = -N.reactionVector r t := by
  simp [reactionDirectionSign, reactionVector_apply]

variable {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}

theorem outflow_sign (W : N.fullyOpen.StrongConcordanceWitness α σ) (s : S) :
    (0 < α (Sum.inr (Sum.inr s)) → 0 < σ s) ∧ (α (Sum.inr (Sum.inr s)) < 0 → σ s < 0) ∧
      (α (Sum.inr (Sum.inr s)) = 0 → σ s = 0) := by
  have hdir : ∀ t, N.fullyOpen.reactionDirectionSign (Sum.inr (Sum.inr s)) t ≠ 0 → t = s := by
    intro t ht
    rw [dir_outflow] at ht
    by_contra h
    simp [h] at ht
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨t, hsg, hne⟩ := W.positive_reaction _ h
    have := hdir t hne
    subst this
    rw [dir_outflow, if_pos rfl, sign_one, sign_eq_one_iff] at hsg
    exact hsg
  · obtain ⟨t, hsg, hne⟩ := W.negative_reaction _ h
    have := hdir t hne
    subst this
    rw [dir_outflow, if_pos rfl, sign_one, sign_eq_neg_one_iff] at hsg
    exact hsg
  · rcases W.zero_reaction _ h with h0 | ⟨t, t', ⟨hsg, hne⟩, ⟨hsg', hne'⟩⟩
    · apply h0 s
      simp [outflowReaction]
    · have h1 := hdir t hne
      have h2 := hdir t' hne'
      subst h1; subst h2
      rw [dir_outflow, if_pos rfl, sign_one] at hsg hsg'
      rw [hsg] at hsg'
      exact absurd hsg' (by decide)

theorem inflow_sign (W : N.fullyOpen.StrongConcordanceWitness α σ) (s : S) :
    (0 < α (Sum.inr (Sum.inl s)) → σ s < 0) ∧ (α (Sum.inr (Sum.inl s)) < 0 → 0 < σ s) := by
  have hdir : ∀ t, N.fullyOpen.reactionDirectionSign (Sum.inr (Sum.inl s)) t ≠ 0 → t = s := by
    intro t ht
    rw [dir_inflow] at ht
    by_contra h
    simp [h] at ht
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨t, hsg, hne⟩ := W.positive_reaction _ h
    have := hdir t hne
    subst this
    rw [dir_inflow, if_pos rfl, sign_neg (by norm_num : (-1 : ℝ) < 0),
      sign_eq_neg_one_iff] at hsg
    exact hsg
  · obtain ⟨t, hsg, hne⟩ := W.negative_reaction _ h
    have := hdir t hne
    subst this
    rw [dir_inflow, if_pos rfl, sign_neg (by norm_num : (-1 : ℝ) < 0), neg_neg,
      sign_eq_one_iff] at hsg
    exact hsg

/-- Net outflow at a species. -/
def netOut (α : N.fullyOpen.R → ℝ) (s : S) : ℝ :=
  α (Sum.inr (Sum.inr s)) - α (Sum.inr (Sum.inl s))

theorem netOut_spec (W : N.fullyOpen.StrongConcordanceWitness α σ) (s : S) :
    (σ s = 0 → netOut α s = 0) ∧ (σ s ≠ 0 → 0 < netOut α s / σ s) := by
  obtain ⟨ho1, ho2, ho3⟩ := outflow_sign W s
  obtain ⟨hi1, hi2⟩ := inflow_sign W s
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hoz : α (Sum.inr (Sum.inr s)) = 0 := by
      rcases lt_trichotomy (α (Sum.inr (Sum.inr s))) 0 with h1 | h1 | h1
      · exact absurd (ho2 h1) (by rw [h]; exact lt_irrefl 0)
      · exact h1
      · exact absurd (ho1 h1) (by rw [h]; exact lt_irrefl 0)
    have hiz : α (Sum.inr (Sum.inl s)) = 0 := by
      rcases lt_trichotomy (α (Sum.inr (Sum.inl s))) 0 with h1 | h1 | h1
      · exact absurd (hi2 h1) (by rw [h]; exact lt_irrefl 0)
      · exact h1
      · exact absurd (hi1 h1) (by rw [h]; exact lt_irrefl 0)
    simp [netOut, hoz, hiz]
  · unfold netOut
    rcases lt_or_gt_of_ne h with hs | hs
    · have hon : α (Sum.inr (Sum.inr s)) < 0 := by
        rcases lt_trichotomy (α (Sum.inr (Sum.inr s))) 0 with h1 | h1 | h1
        · exact h1
        · exact absurd (ho3 h1) h
        · exact absurd (ho1 h1) (not_lt.mpr hs.le)
      have hin : 0 ≤ α (Sum.inr (Sum.inl s)) := by
        by_contra h1
        push_neg at h1
        exact absurd (hi2 h1) (not_lt.mpr hs.le)
      exact div_pos_of_neg_of_neg (by linarith) hs
    · have hop : 0 < α (Sum.inr (Sum.inr s)) := by
        rcases lt_trichotomy (α (Sum.inr (Sum.inr s))) 0 with h1 | h1 | h1
        · exact absurd (ho2 h1) (not_lt.mpr hs.le)
        · exact absurd (ho3 h1) h
        · exact h1
      have hin : α (Sum.inr (Sum.inl s)) ≤ 0 := by
        by_contra h1
        push_neg at h1
        exact absurd (hi1 h1) (not_lt.mpr hs.le)
      exact div_pos (by linarith) hs

/-- The diagonal produced by the flows. -/
noncomputable def flowDiag (α : N.fullyOpen.R → ℝ) (σ : S → ℝ) (s : S) : ℝ :=
  if σ s = 0 then 1 else netOut α s / σ s

theorem flowDiag_pos (W : N.fullyOpen.StrongConcordanceWitness α σ) (s : S) :
    0 < flowDiag α σ s := by
  unfold flowDiag
  split_ifs with h
  · exact one_pos
  · exact (netOut_spec W s).2 h

theorem flowDiag_mul (W : N.fullyOpen.StrongConcordanceWitness α σ) (s : S) :
    flowDiag α σ s * σ s = netOut α s := by
  unfold flowDiag
  split_ifs with h
  · rw [h, mul_zero, (netOut_spec W s).1 h]
  · field_simp

theorem exists_species_of_rate_ne (W : N.fullyOpen.StrongConcordanceWitness α σ) (r : N.R)
    (h : α (Sum.inl r) ≠ 0) :
    ∃ s, 0 < α (Sum.inl r) / (N.fullyOpen.reactionDirectionSign (Sum.inl r) s * σ s) := by
  rcases lt_or_gt_of_ne h with hneg | hpos
  · obtain ⟨s, hsg, hne⟩ := W.negative_reaction _ hneg
    exact ⟨s, div_pos_of_neg_of_neg hneg (by
      rw [mul_comm]; exact sign_mul_neg hne hsg)⟩
  · obtain ⟨s, hsg, hne⟩ := W.positive_reaction _ hpos
    exact ⟨s, div_pos hpos (by rw [mul_comm]; exact sign_mul_pos hne hsg)⟩

open Classical in
/-- The weights on internal channels. -/
noncomputable def chanWeight (W : N.fullyOpen.StrongConcordanceWitness α σ) (r : N.R)
    (t : S) : ℝ :=
  if h : α (Sum.inl r) ≠ 0 then
    (if t = Classical.choose (exists_species_of_rate_ne W r h) then
      α (Sum.inl r) / (N.fullyOpen.reactionDirectionSign (Sum.inl r) t * σ t) else 0)
  else 0

theorem chanWeight_nonneg (W : N.fullyOpen.StrongConcordanceWitness α σ) (r : N.R) (t : S) :
    0 ≤ chanWeight W r t := by
  unfold chanWeight
  split_ifs with h ht
  · subst ht
    exact (Classical.choose_spec (exists_species_of_rate_ne W r h)).le
  · exact le_refl 0
  · exact le_refl 0

theorem sum_chanWeight (W : N.fullyOpen.StrongConcordanceWitness α σ) (r : N.R) :
    ∑ t, chanWeight W r t * N.reactionVector r t * σ t = -α (Sum.inl r) := by
  classical
  by_cases h : α (Sum.inl r) ≠ 0
  · set s₀ := Classical.choose (exists_species_of_rate_ne W r h) with hs₀
    have hspec := Classical.choose_spec (exists_species_of_rate_ne W r h)
    rw [← hs₀] at hspec
    have hden : N.fullyOpen.reactionDirectionSign (Sum.inl r) s₀ * σ s₀ ≠ 0 := by
      intro h0; rw [h0, div_zero] at hspec; exact lt_irrefl 0 hspec
    rw [Finset.sum_eq_single s₀]
    · unfold chanWeight
      rw [dif_pos h, if_pos hs₀]
      rw [dir_inl] at hden ⊢
      have hν : N.reactionVector r s₀ ≠ 0 := fun h0 => hden (by rw [h0]; ring)
      have hσ : σ s₀ ≠ 0 := fun h0 => hden (by rw [h0]; ring)
      field_simp
    · intro t _ ht
      unfold chanWeight
      rw [dif_pos h, if_neg (by rw [← hs₀]; exact ht)]
      ring
    · intro h'; exact absurd (Finset.mem_univ s₀) h'
  · push_neg at h
    rw [h, neg_zero]
    apply Finset.sum_eq_zero
    intro t _
    unfold chanWeight
    rw [dif_neg (by push_neg; exact h)]
    ring

/-- All weights. -/
noncomputable def bcWeight (W : N.fullyOpen.StrongConcordanceWitness α σ) :
    N.R ⊕ S → S → ℝ :=
  Sum.elim (chanWeight W) (fun t' _ => flowDiag α σ t')

theorem bcWeight_nonneg (W : N.fullyOpen.StrongConcordanceWitness α σ) (k : N.R ⊕ S)
    (t : S) : 0 ≤ bcWeight W k t := by
  cases k with
  | inl r => exact chanWeight_nonneg W r t
  | inr t' => exact (flowDiag_pos W t').le

/-- The kernel relation of `fullyOpen`, at one species. -/
theorem kernel_at (W : N.fullyOpen.StrongConcordanceWitness α σ) (s : S) :
    ∑ r : N.R, α (Sum.inl r) * N.reactionVector r s = netOut α s := by
  have h := inKerL_apply W.mem_kerL s
  change ∑ r : N.R ⊕ S ⊕ S, α r * N.fullyOpen.reactionVector r s = 0 at h
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at h
  have h1 : ∑ t : S, α (Sum.inr (Sum.inl t)) *
      N.fullyOpen.reactionVector (Sum.inr (Sum.inl t)) s = α (Sum.inr (Sum.inl s)) := by
    simp only [reactionVector_inflow, Pi.single_apply]
    simp
  have h2 : ∑ t : S, α (Sum.inr (Sum.inr t)) *
      N.fullyOpen.reactionVector (Sum.inr (Sum.inr t)) s = -α (Sum.inr (Sum.inr s)) := by
    simp only [reactionVector_outflow, Pi.neg_apply, Pi.single_apply]
    simp
  rw [h1, h2] at h
  have h3 : ∑ r : N.R, α (Sum.inl r) * N.fullyOpen.reactionVector (Sum.inl r) s =
      ∑ r : N.R, α (Sum.inl r) * N.reactionVector r s := rfl
  rw [h3] at h
  unfold netOut
  linarith

/-- **The witness makes the product singular.** -/
theorem det_bcProduct_eq_zero_of_witness (W : N.fullyOpen.StrongConcordanceWitness α σ) :
    (N.bcMatrix * Matrix.of (fun k t => bcWeight W k t * N.bcMatrix t k)).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨σ, W.sigma_ne, ?_⟩
  rw [← Matrix.mulVec_mulVec]
  have hinner : (Matrix.of (fun k t => bcWeight W k t * N.bcMatrix t k)).mulVec σ =
      Sum.elim (fun r => -α (Sum.inl r)) (fun t' => netOut α t') := by
    funext k
    cases k with
    | inl r =>
      show ∑ t, bcWeight W (Sum.inl r) t * N.bcMatrix t (Sum.inl r) * σ t = -α (Sum.inl r)
      rw [← sum_chanWeight W r]
      rfl
    | inr t' =>
      show ∑ t, bcWeight W (Sum.inr t') t * N.bcMatrix t (Sum.inr t') * σ t = netOut α t'
      simp only [bcWeight, Sum.elim_inr, bcMatrix_inr]
      rw [Finset.sum_eq_single t']
      · rw [if_pos rfl, mul_one, flowDiag_mul W]
      · intro t _ ht; rw [if_neg ht]; ring
      · intro h'; exact absurd (Finset.mem_univ t') h'
  rw [hinner]
  funext s
  show ∑ k : N.R ⊕ S, N.bcMatrix s k *
      Sum.elim (fun r => -α (Sum.inl r)) (fun t' => netOut α t') k = 0
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, bcMatrix_inl, bcMatrix_inr]
  rw [Finset.sum_eq_single (f := fun t' => (if s = t' then (1 : ℝ) else 0) * netOut α t') s]
  · rw [if_pos rfl, one_mul, ← kernel_at W s]
    simp only [mul_neg, Finset.sum_neg_distrib]
    rw [show (∑ r : N.R, N.reactionVector r s * α (Sum.inl r)) =
        ∑ r : N.R, α (Sum.inl r) * N.reactionVector r s from
      Finset.sum_congr rfl (fun _ _ => mul_comm _ _)]
    ring
  · intro t _ ht; rw [if_neg (Ne.symm ht)]; ring
  · intro h'; exact absurd (Finset.mem_univ s) h'

end Witness

/-- **Positivity of the product.** -/
theorem det_bcProduct_pos (N : Network S) (hsep : N.ReactantProductSeparated)
    (hflow : N.FlowsAreSingletons) (hSR : N.TrueSRStrongCriterion)
    (w : N.R ⊕ S → S → ℝ) (hw : ∀ k t, 0 ≤ w k t) (hd : ∀ t, 0 < w (Sum.inr t) t) :
    0 < (N.bcMatrix * Matrix.of (fun k t => w k t * N.bcMatrix t k)).det := by
  apply DetCycle.det_mul_pos_of_coeff_nonneg _ w hw (N.bc_coeff_nonneg hsep hflow hSR)
    (fun t => Sum.inr t)
  have hid : N.bcMatrix.submatrix id (fun t => Sum.inr t) = 1 := by
    ext s t
    simp [Matrix.one_apply]
  rw [hid, Matrix.det_one]
  simp only [bcMatrix_inr, if_true, Finset.prod_const_one, mul_one]
  exact Finset.prod_pos fun t _ => hd t

/-- **The true-SR criterion implies strong concordance of the fully open extension**
(Banaji--Craciun route). -/
theorem stronglyConcordant_fullyOpen_of_trueSRCriterion_bc (N : Network S)
    (hsep : N.ReactantProductSeparated) (hflow : N.FlowsAreSingletons)
    (hSR : N.TrueSRStrongCriterion) : N.fullyOpen.StronglyConcordant := by
  rintro ⟨α, σ, W⟩
  have hzero := det_bcProduct_eq_zero_of_witness W
  have hpos := N.det_bcProduct_pos hsep hflow hSR (bcWeight W) (bcWeight_nonneg W)
    (fun t => flowDiag_pos W t)
  rw [hzero] at hpos
  exact lt_irrefl 0 hpos

end Network
end CRNT
