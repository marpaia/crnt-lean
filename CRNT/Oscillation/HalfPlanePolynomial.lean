import CRNT.Oscillation.SpectralOpenness
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Real polynomial coefficient signs from half-plane root location

This module supplies the elementary polynomial fact used by the diagonal-scaling arguments:
a monic real polynomial all of whose complex roots lie in the closed left half-plane has
nonnegative coefficients.  Equivalently, if a monic real polynomial has a negative coefficient,
it has a root with strictly positive real part.

The proof is constructive.  A real polynomial is peeled apart one root at a time.  A real root
`r <= 0` contributes the nonnegative-coefficient linear factor `X-r`.  A non-real root `z=a+ib`
occurs together with its conjugate and contributes

`(X-z)(X-conj z) = X^2 - 2 a X + |z|^2`,

whose three real coefficients are nonnegative when `a <= 0`.  The quotient remains real and the
induction continues.  This avoids using a Routh--Hurwitz theorem in arbitrary dimension.
-/

namespace Polynomial

open Complex

/-- Every coefficient of a real polynomial is nonnegative. -/
def CoeffNonneg (p : Polynomial ℝ) : Prop := ∀ k, 0 ≤ p.coeff k

namespace CoeffNonneg

@[simp] theorem zero : CoeffNonneg (0 : Polynomial ℝ) := by
  intro k; simp

@[simp] theorem one : CoeffNonneg (1 : Polynomial ℝ) := by
  intro k
  by_cases h : k = 0
  · subst k
    simp
  · rw [coeff_eq_zero_of_natDegree_lt (by simpa using Nat.zero_lt_of_ne_zero h)]

/-- Products preserve coefficientwise nonnegativity. -/
theorem mul {p q : Polynomial ℝ} (hp : CoeffNonneg p) (hq : CoeffNonneg q) :
    CoeffNonneg (p * q) := by
  intro k
  rw [coeff_mul]
  exact Finset.sum_nonneg fun i hi => mul_nonneg (hp i.1) (hq i.2)

/-- `X-r` has nonnegative coefficients for a nonpositive real root. -/
theorem X_sub_C {r : ℝ} (hr : r ≤ 0) : CoeffNonneg (X - C r) := by
  intro k
  rcases k with _ | k
  · simp [coeff_sub, coeff_X, coeff_C]
    linarith
  · rw [← mul_one (X - C r), coeff_X_sub_C_mul]
    rcases k with _ | k
    · simp [coeff_one]
    · simp [coeff_one]

/-- The real quadratic belonging to a conjugate pair in the closed left half-plane has
nonnegative coefficients. -/
theorem conjugateQuadratic {a b : ℝ} (ha : a ≤ 0) :
    CoeffNonneg (X ^ 2 - C (2 * a) * X + C (a ^ 2 + b ^ 2)) := by
  intro k
  have hcoeff : (X ^ 2 - C (2 * a) * X + C (a ^ 2 + b ^ 2)).coeff k =
      (if k = 2 then 1 else 0) - (if k = 1 then 2 * a else 0) +
        (if k = 0 then a ^ 2 + b ^ 2 else 0) := by
    simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul_X, coeff_C]
  rw [hcoeff]
  by_cases h0 : k = 0
  · subst k
    simp
    nlinarith [sq_nonneg a, sq_nonneg b]
  · by_cases h1 : k = 1
    · subst k
      simp
      linarith
    · by_cases h2 : k = 2
      · subst k
        simp
      · have h3 : 3 ≤ k := by omega
        simp [h0, h1, h2, h3]

end CoeffNonneg

/-- The real quadratic factor corresponding to a complex number and its conjugate. -/
noncomputable def conjugatePairFactor (z : ℂ) : Polynomial ℝ :=
  X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2)

/-- Complexification of `conjugatePairFactor` is exactly `(X-z)(X-conj z)`. -/
theorem map_conjugatePairFactor (z : ℂ) :
    (conjugatePairFactor z).map (algebraMap ℝ ℂ) =
      (X - C z) * (X - C (star z)) := by
  simp only [conjugatePairFactor, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C]
  have hadd : algebraMap ℝ ℂ (2 * z.re) = z + star z :=
    (Complex.add_conj z).symm
  have hnorm : algebraMap ℝ ℂ (‖z‖ ^ 2) = z * star z := by
    calc
      algebraMap ℝ ℂ (‖z‖ ^ 2) = (Complex.normSq z : ℂ) := by
        exact congrArg (fun x : ℝ => (x : ℂ)) (Complex.normSq_eq_norm_sq z).symm
      _ = z * star z := (Complex.mul_conj z).symm
  rw [hadd, hnorm]
  rw [C_add, C_mul]
  ring

/-- A conjugate-pair factor has nonnegative coefficients whenever the root has nonpositive real
part. -/
theorem conjugatePairFactor_coeffNonneg {z : ℂ} (hz : z.re ≤ 0) :
    (conjugatePairFactor z).CoeffNonneg := by
  intro k
  have hcoeff : (conjugatePairFactor z).coeff k =
      (if k = 2 then 1 else 0) - (if k = 1 then 2 * z.re else 0) +
        (if k = 0 then ‖z‖ ^ 2 else 0) := by
    simp only [conjugatePairFactor, coeff_add, coeff_sub, coeff_X_pow,
      coeff_C_mul_X, coeff_C]
  rw [hcoeff]
  by_cases h0 : k = 0
  · subst k
    simp
  · by_cases h1 : k = 1
    · subst k
      simp
      linarith
    · by_cases h2 : k = 2
      · subst k
        simp
      · have h3 : 3 ≤ k := by omega
        simp [h0, h1, h2, h3]

/-- Real coefficients imply conjugation symmetry of evaluation. -/
theorem eval₂_conj_of_real (p : Polynomial ℝ) (z : ℂ) :
    Polynomial.eval₂ (algebraMap ℝ ℂ) (star z) p =
      star (Polynomial.eval₂ (algebraMap ℝ ℂ) z p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [eval₂_add, hp, hq]
      rw [eval₂_add]
      exact (map_add (starRingEnd ℂ) _ _).symm
  | monomial n a => simp [map_pow]

/-- Hence a non-real complex root of a real polynomial comes with its conjugate. -/
theorem conj_isRoot_of_isRoot_real {p : Polynomial ℝ} {z : ℂ}
    (hz : Polynomial.eval₂ (algebraMap ℝ ℂ) z p = 0) :
    Polynomial.eval₂ (algebraMap ℝ ℂ) (star z) p = 0 := by
  rw [eval₂_conj_of_real, hz]
  exact map_zero (starRingEnd ℂ)

/-- Division by a real linear factor is exact at a real root. -/
theorem exists_real_quotient_of_real_root {p : Polynomial ℝ} {r : ℝ}
    (hr : p.eval r = 0) :
    ∃ q : Polynomial ℝ, p = (X - C r) * q := by
  refine ⟨p / (X - C r), ?_⟩
  have hdvd : X - C r ∣ p := Polynomial.dvd_iff_isRoot.mpr hr
  exact (EuclideanDomain.mul_div_cancel' (monic_X_sub_C r).ne_zero hdvd).symm

/-- Division by the real conjugate-pair quadratic is exact at a non-real complex root. -/
theorem exists_real_quotient_of_nonreal_root {p : Polynomial ℝ} {z : ℂ}
    (hz : Polynomial.eval₂ (algebraMap ℝ ℂ) z p = 0) (him : z.im ≠ 0) :
    ∃ q : Polynomial ℝ, p = conjugatePairFactor z * q := by
  have hz' : Polynomial.eval₂ (algebraMap ℝ ℂ) (star z) p = 0 :=
    conj_isRoot_of_isRoot_real hz
  have hquad : conjugatePairFactor z ∣ p := by
    -- `z` and `conj z` are distinct, so their product divides the complexification; injectivity of
    -- the real-to-complex map then reflects divisibility by the real quadratic.
    have hzA : Polynomial.aeval z p = 0 := by simpa [Polynomial.aeval_def] using hz
    have hq := quadratic_dvd_of_aeval_eq_zero_im_ne_zero p hzA him
    simpa [conjugatePairFactor, Complex.normSq_eq_norm_sq] using hq
  rcases hquad with ⟨q, hq⟩
  exact ⟨q, hq⟩

/-- A monic real polynomial whose roots all have nonpositive real part has nonnegative
coefficients.  The statement includes the split hypothesis explicitly so it also applies over any
future real-closed replacement of `ℝ`; for `ℂ` it is discharged by algebraic closure. -/
theorem coeffNonneg_of_roots_re_nonpos
    (p : Polynomial ℝ) (hpmonic : p.Monic)
    (hroots : ∀ z : ℂ,
      Polynomial.eval₂ (algebraMap ℝ ℂ) z p = 0 → z.re ≤ 0) :
    p.CoeffNonneg := by
  classical
  induction hdeg : p.natDegree using Nat.strong_induction_on generalizing p with
  | h n ih =>
      by_cases hn : n = 0
      · have hp : p = 1 := by
          have hdp : p.natDegree = 0 := by simpa [hdeg] using hn
          have hpcoeff : p.coeff 0 = 1 := by
            change p.leadingCoeff = 1 at hpmonic
            rw [← coeff_natDegree, hdp] at hpmonic
            exact hpmonic
          rw [eq_C_of_natDegree_eq_zero hdp, hpcoeff]
          rfl
        simpa [hp] using CoeffNonneg.one
      · have hpne : p ≠ 0 := hpmonic.ne_zero
        have hdegpos : 0 < p.natDegree := by simpa [hdeg] using Nat.pos_of_ne_zero hn
        obtain ⟨z, hz⟩ : ∃ z : ℂ,
            Polynomial.eval₂ (algebraMap ℝ ℂ) z p = 0 := by
          let pc := p.map (algebraMap ℝ ℂ)
          have hpcmonic : pc.Monic := hpmonic.map _
          have hpcdeg : 0 < pc.degree := by
            rw [degree_eq_natDegree hpcmonic.ne_zero]
            exact_mod_cast (by simpa [pc] using hdegpos)
          obtain ⟨z, hz⟩ := Complex.exists_root hpcdeg
          exact ⟨z, by simpa [pc, eval₂_eq_eval_map] using hz⟩
        have hzhalf : z.re ≤ 0 := hroots z hz
        by_cases him : z.im = 0
        · let r : ℝ := z.re
          have hzreal : z = (r : ℂ) := by
            apply Complex.ext <;> simp [r, him]
          have hrroot : p.eval r = 0 := by
            have hz' : Polynomial.eval₂ (algebraMap ℝ ℂ)
                (algebraMap ℝ ℂ r) p = 0 := by
              simpa [hzreal] using hz
            have hcast : algebraMap ℝ ℂ (Polynomial.eval r p) = 0 := by
              rw [← Polynomial.eval₂_at_apply]
              exact hz'
            change ((Polynomial.eval r p : ℝ) : ℂ) = 0 at hcast
            exact Complex.ofReal_eq_zero.mp hcast
          obtain ⟨q, hq⟩ := exists_real_quotient_of_real_root hrroot
          have hqmonic : q.Monic := by
            rw [hq] at hpmonic
            exact (monic_X_sub_C r).of_mul_monic_left hpmonic
          have hqdeg : q.natDegree < p.natDegree := by
            rw [hq, natDegree_mul (monic_X_sub_C r).ne_zero hqmonic.ne_zero]
            simp
          have hqroots : ∀ w : ℂ,
              Polynomial.eval₂ (algebraMap ℝ ℂ) w q = 0 → w.re ≤ 0 := by
            intro w hw
            apply hroots w
            rw [hq, eval₂_mul, hw, mul_zero]
          have hqn := ih q.natDegree (by simpa [hdeg] using hqdeg) q hqmonic hqroots rfl
          rw [hq]
          exact (CoeffNonneg.X_sub_C (by simpa [r] using hzhalf)).mul hqn
        · obtain ⟨q, hq⟩ := exists_real_quotient_of_nonreal_root hz him
          have hcoef : (conjugatePairFactor z).coeff 2 = 1 := by
            simp only [conjugatePairFactor, coeff_add, coeff_sub, coeff_X_pow,
              coeff_C_mul_X, coeff_C]
            norm_num
          have hfacdegree : (conjugatePairFactor z).natDegree = 2 := by
            apply le_antisymm
            · apply natDegree_le_iff_coeff_eq_zero.mpr
              intro k hk
              have hk3 : 3 ≤ k := by omega
              simp only [conjugatePairFactor, coeff_add, coeff_sub, coeff_X_pow,
                coeff_C_mul_X, coeff_C]
              have hk2 : k ≠ 2 := by omega
              have hk1 : k ≠ 1 := by omega
              have hk0 : k ≠ 0 := by omega
              simp [hk2, hk1, hk0]
            · exact le_natDegree_of_ne_zero (by rw [hcoef]; norm_num)
          have hfacmonic : (conjugatePairFactor z).Monic := by
            change (conjugatePairFactor z).leadingCoeff = 1
            rw [leadingCoeff, hfacdegree]
            exact hcoef
          have hqmonic : q.Monic := by
            rw [hq] at hpmonic
            exact hfacmonic.of_mul_monic_left hpmonic
          have hqdeg : q.natDegree < p.natDegree := by
            rw [hq, natDegree_mul hfacmonic.ne_zero hqmonic.ne_zero]
            rw [hfacdegree]
            omega
          have hqroots : ∀ w : ℂ,
              Polynomial.eval₂ (algebraMap ℝ ℂ) w q = 0 → w.re ≤ 0 := by
            intro w hw
            apply hroots w
            rw [hq, eval₂_mul, hw, mul_zero]
          have hqn := ih q.natDegree (by simpa [hdeg] using hqdeg) q hqmonic hqroots rfl
          rw [hq]
          exact (conjugatePairFactor_coeffNonneg hzhalf).mul hqn

/-- Contrapositive form used by the matrix scaling theorem: a negative coefficient of a monic real
polynomial forces a strict right-half-plane root. -/
theorem exists_root_re_pos_of_monic_coeff_neg
    {p : Polynomial ℝ} (hp : p.Monic) {k : ℕ} (hk : p.coeff k < 0) :
    ∃ z : ℂ, Polynomial.eval₂ (algebraMap ℝ ℂ) z p = 0 ∧ 0 < z.re := by
  by_contra h
  push_neg at h
  have hnonpos : ∀ z : ℂ,
      Polynomial.eval₂ (algebraMap ℝ ℂ) z p = 0 → z.re ≤ 0 := by
    intro z hz
    exact h z hz
  have hcoeff := coeffNonneg_of_roots_re_nonpos p hp hnonpos k
  linarith

end Polynomial

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace IsHurwitzReal

/-- The determinant of a Hurwitz real matrix has the standard sign `(-1)^n`.  This general-
dimension fact is obtained from coefficient nonnegativity plus nonsingularity. -/
theorem signed_det_pos {M : Matrix n n ℝ} (h : M.IsHurwitzReal) :
    0 < (-1 : ℝ) ^ Fintype.card n * M.det := by
  have hroots : ∀ z : ℂ,
      Polynomial.eval₂ (algebraMap ℝ ℂ) z M.charpoly = 0 → z.re ≤ 0 := by
    intro z hz
    have hzroot : z ∈ (M.map (algebraMap ℝ ℂ)).charpoly.roots := by
      have hmap : (M.map (algebraMap ℝ ℂ)).charpoly =
          M.charpoly.map (algebraMap ℝ ℂ) := Matrix.charpoly_map M _
      rw [hmap, Polynomial.mem_roots (by simpa using (Matrix.charpoly_monic M).ne_zero)]
      simpa [Polynomial.eval_map] using hz
    exact le_of_lt (h z hzroot)
  have hcoeff0 : 0 ≤ M.charpoly.coeff 0 :=
    Polynomial.coeffNonneg_of_roots_re_nonpos M.charpoly (Matrix.charpoly_monic M) hroots 0
  have hcoeff0ne : M.charpoly.coeff 0 ≠ 0 := by
    intro hzero
    apply h.det_ne_zero
    rw [Matrix.det_eq_sign_charpoly_coeff, hzero, mul_zero]
  have hcoeff0pos : 0 < M.charpoly.coeff 0 := lt_of_le_of_ne hcoeff0 (Ne.symm hcoeff0ne)
  rw [Matrix.det_eq_sign_charpoly_coeff]
  have hsignsq : ((-1 : ℝ) ^ Fintype.card n) * ((-1 : ℝ) ^ Fintype.card n) = 1 := by
    rw [← pow_add, ← two_mul]
    simp [pow_mul]
  nlinarith

end IsHurwitzReal
end Matrix
