import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Basic.Sign.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import CRNT.Kinetics.Generalized

/-!
# Sign-vector criterion for log-affine/affine intersections

Positive equilibria of complex-balanced *generalized* mass-action systems form a log-affine set
`x* · exp(T)` (with `T` the orthogonal complement of the kinetic-order subspace `S̃`), while the
dynamics is confined to affine classes `x₀ + S`. Müller and Regensburger (*Generalized mass
action systems: complex balancing equilibria and sign vectors of the stoichiometric and
kinetic-order subspaces*, SIAM J. Appl. Math. 72 (2012), Proposition 3.9 and Theorem 3.10)
characterize when every such intersection has at most one point: exactly when no nonzero
vector of `S` has the same sign pattern as a vector of `T`.

This module proves that characterization for arbitrary subspaces `V, T ⊆ ℝ^S`:
* `CRNT.logAffine_affine_injective_iff`: `(x* exp T) ∩ (x₀ + V)` has at most one point for all
  positive `x*, x₀` iff `σ(V) ∩ σ(T) = {0}`.
* `CRNT.signCondition_of_orthogonal`: when `T ⊆ V^⊥` (classical mass action, `S̃ = S`) the
  sign condition holds automatically, recovering uniqueness of complex-balanced equilibria in
  each class.
-/

namespace CRNT

open scoped BigOperators

variable {S : Type}

/-- The sign condition `σ(V) ∩ σ(T) = {0}`. -/
def SignCondition (V T : Submodule ℝ (S → ℝ)) : Prop :=
  ∀ u ∈ V, ∀ v ∈ T, (∀ i, SignType.sign (u i) = SignType.sign (v i)) → u = 0

/-- Componentwise log-difference. -/
noncomputable def logDiff (x y : S → ℝ) : S → ℝ := fun i => Real.log (x i) - Real.log (y i)

theorem sign_sub_eq_sign_logDiff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    SignType.sign (a - b) = SignType.sign (Real.log a - Real.log b) := by
  rcases lt_trichotomy a b with h | h | h
  · rw [sign_neg (sub_neg.mpr h), sign_neg (sub_neg.mpr (Real.log_lt_log ha h))]
  · subst h; simp
  · rw [sign_pos (sub_pos.mpr h), sign_pos (sub_pos.mpr (Real.log_lt_log hb h))]

/-- **Sign-vector criterion** (Müller–Regensburger 2012). For subspaces `V` (stoichiometric)
and `T` (log-directions), two positive points with `x - y ∈ V` and `log x - log y ∈ T` must
coincide iff `σ(V) ∩ σ(T) = {0}`. -/
theorem logAffine_affine_injective_iff (V T : Submodule ℝ (S → ℝ)) :
    (∀ x y : S → ℝ, (∀ i, 0 < x i) → (∀ i, 0 < y i) → x - y ∈ V → logDiff x y ∈ T →
        x = y) ↔ SignCondition V T := by
  constructor
  · intro hinj u hu v hv hsign
    -- realize `u` as a difference and `v` as a log-difference of positive points
    let y : S → ℝ := fun i => if u i = 0 then 1 else u i / (Real.exp (v i) - 1)
    let x : S → ℝ := fun i => y i * Real.exp (v i)
    have hcomp : ∀ i, 0 < y i ∧ x i - y i = u i ∧ Real.log (x i) - Real.log (y i) = v i := by
      intro i
      have hs := hsign i
      by_cases h0 : u i = 0
      · have hv0 : v i = 0 := by
          rw [h0, sign_zero] at hs
          exact sign_eq_zero_iff.mp hs.symm
        simp [x, y, h0, hv0]
      · have hv0 : v i ≠ 0 := fun e => h0 (by rw [e, sign_zero] at hs; exact sign_eq_zero_iff.mp hs)
        have hy : 0 < u i / (Real.exp (v i) - 1) := by
          rcases lt_or_gt_of_ne h0 with hneg | hpos
          · have hvn : v i < 0 := by
              rw [sign_neg hneg] at hs
              exact sign_eq_neg_one_iff.mp hs.symm
            exact div_pos_of_neg_of_neg hneg (by linarith [Real.exp_lt_one_iff.mpr hvn])
          · have hvp : 0 < v i := by
              rw [sign_pos hpos] at hs
              exact sign_eq_one_iff.mp hs.symm
            exact div_pos hpos (by linarith [Real.one_lt_exp_iff.mpr hvp])
        have hden : Real.exp (v i) - 1 ≠ 0 := by
          intro e
          have : Real.exp (v i) = Real.exp 0 := by rw [Real.exp_zero]; linarith
          exact hv0 (Real.exp_injective this)
        refine ⟨by simpa [y, h0] using hy, ?_, ?_⟩
        · simp only [x, y, h0, ite_false]
          field_simp
        · simp only [x]
          rw [Real.log_mul (by simpa [y, h0] using hy.ne') (Real.exp_pos _).ne', Real.log_exp]
          ring
    have hxy : x - y = u := funext fun i => (hcomp i).2.1
    have hlog : logDiff x y = v := funext fun i => (hcomp i).2.2
    have hy : ∀ i, 0 < y i := fun i => (hcomp i).1
    have hx : ∀ i, 0 < x i := fun i => mul_pos (hy i) (Real.exp_pos _)
    have := hinj x y hx hy (hxy ▸ hu) (hlog ▸ hv)
    rw [← hxy, this, sub_self]
  · intro hsc x y hx hy hV hT
    have := hsc _ hV _ hT (fun i => sign_sub_eq_sign_logDiff (hx i) (hy i))
    exact sub_eq_zero.mp this

/-- **Classical mass action.** If every vector of `T` is orthogonal to every vector of `V`
(as for `T = S^⊥`, `V = S`), the sign condition holds. -/
theorem signCondition_of_orthogonal [Fintype S] (V T : Submodule ℝ (S → ℝ))
    (horth : ∀ u ∈ V, ∀ v ∈ T, ∑ i, u i * v i = 0) : SignCondition V T := by
  intro u hu v hv hsign
  have hnonneg : ∀ i, 0 ≤ u i * v i := by
    intro i
    have hs := hsign i
    rcases lt_trichotomy (u i) 0 with h | h | h
    · rw [sign_neg h] at hs
      have : v i < 0 := sign_eq_neg_one_iff.mp hs.symm
      nlinarith
    · rw [h, zero_mul]
    · rw [sign_pos h] at hs
      have : 0 < v i := sign_eq_one_iff.mp hs.symm
      positivity
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i)).mp (horth u hu v hv)
  funext i
  have h := hzero i (Finset.mem_univ i)
  rcases mul_eq_zero.mp h with h1 | h1
  · exact h1
  · have hs := hsign i
    rw [h1, sign_zero] at hs
    exact sign_eq_zero_iff.mp hs

/-- `SignCondition` is the library's Müller–Regensburger condition `SignCompatible`. -/
theorem signCondition_iff_signCompatible [Fintype S] (V T : Submodule ℝ (S → ℝ)) :
    SignCondition V T ↔ SignCompatible V T := by
  have key : ∀ u v : S → ℝ,
      (∀ i, SignType.sign (u i) = SignType.sign (v i)) ↔ SameSign u v := by
    intro u v
    rw [sameSign_iff_signVector_eq, funext_iff]
    rfl
  constructor
  · intro h u hu v hv hs; exact h u hu v hv ((key u v).mpr hs)
  · intro h u hu v hv hs; exact h u hu v hv ((key u v).mp hs)

/-- **Converse of generalized uniqueness.** If the sign condition `SignCompatible V T` fails,
there are two distinct positive points with `x - y ∈ V` and `log x - log y ∈ T`; i.e. some
affine class meets some log-affine set in at least two points. Together with the library's
uniqueness theorem this makes `SignCompatible` necessary and sufficient. -/
theorem exists_two_points_of_not_signCompatible [Fintype S] (V T : Submodule ℝ (S → ℝ))
    (h : ¬ SignCompatible V T) :
    ∃ x y : S → ℝ, (∀ i, 0 < x i) ∧ (∀ i, 0 < y i) ∧ x - y ∈ V ∧ logDiff x y ∈ T ∧ x ≠ y := by
  rw [← signCondition_iff_signCompatible, ← logAffine_affine_injective_iff] at h
  push Not at h
  exact h

end CRNT
