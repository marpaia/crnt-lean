import CRNT.Multistationarity.PMatrix
import CRNT.Multistationarity.PMatrixSchur
import CRNT.Multistationarity.PMatrixSignature
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Gale–Nikaido global univalence for P-matrix maps

The degree-free Gale–Nikaido theorem (Math. Ann. 159 (1965), 81–93): a `C¹` map whose Jacobian is a
P-matrix at every point of a rectangle is globally injective on that rectangle. The development
follows the original proof — Theorem 1 (a P-matrix reverses no nonnegative vector to nonpositive) →
Corollaries 1–2 (theorem-of-the-alternative consequences) → Theorem 3 (order-interval monotonicity,
by dimension induction) → Theorem 4 (univalence, by signature normalization) — and uses no topological
degree.

This module starts with the linear-algebra foundation. The reductions consume the P-matrix
API: principal-submatrix closure (`IsPMatrix.submatrix_isPMatrix`), signature-conjugation invariance
(`IsPMatrix.signatureConj`), and positivity of determinants/diagonals (`IsPMatrix.det_pos`,
`IsPMatrix.diag_pos`).

Depends on: `CRNT.Multistationarity.PMatrix`,
`CRNT.Multistationarity.PMatrixSchur`, `CRNT.Multistationarity.PMatrixSignature`.
-/

set_option linter.unusedSectionVars false

namespace Matrix

variable {n R : Type*}
variable [Fintype n] [DecidableEq n]
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **The transpose of a P-matrix is a P-matrix.** Each principal minor of `Mᵀ` is the transpose of
the corresponding principal minor of `M`, hence has the same (positive) determinant. -/
theorem IsPMatrix.transpose {M : Matrix n n R} (h : M.IsPMatrix) : Mᵀ.IsPMatrix := by
  intro s
  have hsub : Mᵀ.submatrix (fun i : s => (i : n)) (fun i : s => (i : n))
      = (M.submatrix (fun i : s => (i : n)) (fun i : s => (i : n)))ᵀ := by
    rw [Matrix.transpose_submatrix]
  rw [hsub, Matrix.det_transpose]
  exact h s

/-- **The diagonal of `A⁻¹` is positive for a P-matrix.** `(A⁻¹) j j = (det A)⁻¹ · adjugate A j j`,
and `adjugate A j j` is the `(j,j)` principal minor (the cofactor sign is `+1`), itself a positive
P-matrix principal minor; `det A > 0`. -/
theorem IsPMatrix.inv_diag_pos {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsPMatrix) (j : Fin (n + 1)) : 0 < A⁻¹ j j := by
  have hdet : 0 < A.det := hA.det_pos
  have hadj : 0 < adjugate A j j := by
    rw [adjugate_fin_succ_eq_det_submatrix]
    have hsign : ((-1 : ℝ)) ^ ((j : ℕ) + (j : ℕ)) = 1 :=
      Even.neg_one_pow ⟨(j : ℕ), rfl⟩
    rw [hsign, one_mul]
    exact hA.submatrix_det_pos (Fin.succAbove_right_injective)
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact mul_pos (inv_pos.mpr hdet) hadj

/-- **Gale–Nikaido Theorem 1.** A P-matrix sends no nonnegative vector to a nonpositive one except
`0`: if `A` is a P-matrix, `x ≥ 0`, and `A *ᵥ x ≤ 0`, then `x = 0`. Proof by induction on dimension:
the column `b = A⁻¹ e₀` satisfies `A *ᵥ b = e₀` with positive diagonal entry `b 0`; the minimal ratio
`θ = minᵢ xᵢ/bᵢ` zeroes a coordinate `k` of `y = x − θ b` while keeping `y ≥ 0`, `A *ᵥ y ≤ 0`; deleting
`k` (a principal submatrix, again a P-matrix) and applying the inductive hypothesis forces `y = 0`,
whence `x = θ b`, `A *ᵥ x = θ e₀ ≤ 0` gives `θ = 0`, so `x = 0`. -/
theorem IsPMatrix.eq_zero_of_mulVec_nonpos {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsPMatrix) {x : Fin n → ℝ} (hx : 0 ≤ x) (hAx : A *ᵥ x ≤ 0) : x = 0 := by
  induction n with
  | zero => funext i; exact i.elim0
  | succ m ih =>
    classical
    have hunit : IsUnit A.det := hA.det_ne_zero.isUnit
    set b : Fin (m + 1) → ℝ := fun i => A⁻¹ i 0 with hbdef
    have hAb : A *ᵥ b = Pi.single (0 : Fin (m + 1)) 1 := by
      funext i
      have h1 : (A *ᵥ b) i = (A * A⁻¹) i 0 := by
        simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, hbdef]
      rw [h1, mul_nonsing_inv A hunit]
      simp [Matrix.one_apply, Pi.single_apply]
    have hb0 : 0 < b 0 := hA.inv_diag_pos 0
    set S : Finset (Fin (m + 1)) := Finset.univ.filter (fun i => 0 < b i) with hSdef
    have hSne : S.Nonempty := ⟨0, by rw [hSdef, Finset.mem_filter]; exact ⟨Finset.mem_univ 0, hb0⟩⟩
    set θ : ℝ := S.inf' hSne (fun i => x i / b i) with hθdef
    have hθnn : 0 ≤ θ := by
      rw [hθdef, Finset.le_inf'_iff]
      intro i hi
      rw [hSdef, Finset.mem_filter] at hi
      exact div_nonneg (hx i) (le_of_lt hi.2)
    obtain ⟨k, hkS, hθk⟩ := S.exists_mem_eq_inf' hSne (fun i => x i / b i)
    rw [hSdef, Finset.mem_filter] at hkS
    have hbk : 0 < b k := hkS.2
    set y : Fin (m + 1) → ℝ := x - θ • b with hydef
    have hyk : y k = 0 := by
      have hbk' : b k ≠ 0 := ne_of_gt hbk
      rw [hydef]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [show θ = x k / b k from hθk, div_mul_cancel₀ (x k) hbk', sub_self]
    have hynn : 0 ≤ y := by
      intro i
      rw [Pi.zero_apply, hydef]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have hxi : (0 : ℝ) ≤ x i := hx i
      by_cases hbi : 0 < b i
      · have hle : θ ≤ x i / b i := by
          rw [hθdef]
          exact Finset.inf'_le _ (by rw [hSdef, Finset.mem_filter]; exact ⟨Finset.mem_univ i, hbi⟩)
        have hmul := (le_div_iff₀ hbi).mp hle
        linarith
      · rw [not_lt] at hbi
        have hmul : θ * b i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθnn hbi
        linarith
    have hAy : A *ᵥ y ≤ 0 := by
      intro i
      rw [Pi.zero_apply]
      have hexp : (A *ᵥ y) i = (A *ᵥ x) i - θ * (A *ᵥ b) i := by
        rw [hydef, Matrix.mulVec_sub, Matrix.mulVec_smul]
        simp [Pi.sub_apply, Pi.smul_apply]
      rw [hexp, hAb]
      have hAxi : (A *ᵥ x) i ≤ 0 := hAx i
      by_cases hi0 : i = 0
      · subst hi0; rw [Pi.single_eq_same, mul_one]; linarith [hθnn]
      · rw [Pi.single_eq_of_ne hi0, mul_zero, sub_zero]; exact hAxi
    have hÂP : (A.submatrix k.succAbove k.succAbove).IsPMatrix :=
      hA.submatrix_isPMatrix Fin.succAbove_right_injective
    set ŷ : Fin m → ℝ := fun i => y (k.succAbove i) with hŷdef
    have hŷnn : 0 ≤ ŷ := fun i => hynn (k.succAbove i)
    have hÂŷ : (A.submatrix k.succAbove k.succAbove) *ᵥ ŷ ≤ 0 := by
      intro i
      have heq : ((A.submatrix k.succAbove k.succAbove) *ᵥ ŷ) i = (A *ᵥ y) (k.succAbove i) := by
        simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, hŷdef]
        rw [Fin.sum_univ_succAbove (fun j => A (k.succAbove i) j * y j) k, hyk, mul_zero, zero_add]
      rw [heq]; exact hAy (k.succAbove i)
    have hŷ0 : ŷ = 0 := ih hÂP hŷnn hÂŷ
    have hy0 : y = 0 := by
      funext i
      rcases eq_or_ne i k with rfl | hik
      · exact hyk
      · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hik
        have hl := congrFun hŷ0 l
        rw [hŷdef] at hl
        exact hl
    have hxθb : x = θ • b := sub_eq_zero.mp (by rw [← hydef]; exact hy0)
    have hθ0 : θ = 0 := by
      have hAx0 : (A *ᵥ x) 0 ≤ 0 := hAx 0
      rw [hxθb, Matrix.mulVec_smul, hAb, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
        mul_one] at hAx0
      linarith [hθnn]
    rw [hxθb, hθ0, zero_smul]

/-- **Gale–Nikaido Corollary 1.** For a P-matrix there is a uniform `lam > 0` such that every
nonnegative vector `v` has a component of `A *ᵥ v` at least `lam‖v‖`. By Theorem 1, on the compact set
of nonnegative unit vectors the maximal component of `A *ᵥ ·` is everywhere positive, so it attains a
positive minimum `lam`; scaling recovers the bound for all `v ≥ 0`. -/
theorem IsPMatrix.exists_pos_le_mulVec {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsPMatrix) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ v : Fin (n + 1) → ℝ, 0 ≤ v → ∃ i, lam * ‖v‖ ≤ (A *ᵥ v) i := by
  classical
  set g : (Fin (n + 1) → ℝ) → ℝ :=
    fun v => Finset.univ.sup' Finset.univ_nonempty (fun i => (A *ᵥ v) i) with hgdef
  have hgcont : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro v
    refine ContinuousAt.finset_sup'_apply Finset.univ_nonempty (fun i _ => ?_)
    exact ((continuous_apply i).comp A.mulVecLin.continuous_of_finiteDimensional).continuousAt
  set K : Set (Fin (n + 1) → ℝ) := Metric.sphere 0 1 ∩ {v | 0 ≤ v} with hKdef
  have hKcompact : IsCompact K :=
    (isCompact_sphere 0 1).inter_right (isClosed_le continuous_const continuous_id)
  have hKne : K.Nonempty := by
    refine ⟨Pi.single 0 1, ?_, ?_⟩
    · rw [Metric.mem_sphere, dist_zero_right, Pi.norm_single, norm_one]
    · intro i
      rw [Pi.zero_apply, Pi.single_apply]
      split <;> norm_num
  obtain ⟨v₀, hv₀K, hv₀min⟩ := hKcompact.exists_isMinOn hKne hgcont.continuousOn
  set lam : ℝ := g v₀ with hlamdef
  have hv₀ne : v₀ ≠ 0 := by
    intro h; rw [h] at hv₀K; simp [hKdef] at hv₀K
  have hv₀nn : 0 ≤ v₀ := hv₀K.2
  have hlampos : 0 < lam := by
    have hnotle : ¬ A *ᵥ v₀ ≤ 0 := fun hle => hv₀ne (hA.eq_zero_of_mulVec_nonpos hv₀nn hle)
    rw [Pi.le_def] at hnotle
    simp only [not_forall, not_le] at hnotle
    obtain ⟨i, hi⟩ := hnotle
    rw [Pi.zero_apply] at hi
    exact lt_of_lt_of_le hi (Finset.le_sup' (fun i => (A *ᵥ v₀) i) (Finset.mem_univ i))
  -- the unit-vector bound: every w ∈ K has a component ≥ lam
  have hunit : ∀ w ∈ K, ∃ i, lam ≤ (A *ᵥ w) i := by
    intro w hwK
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => (A *ᵥ w) i)
    exact ⟨i, by rw [hlamdef]; rw [← hi]; exact hv₀min hwK⟩
  refine ⟨lam, hlampos, fun v hv => ?_⟩
  rcases eq_or_ne v 0 with rfl | hvne
  · exact ⟨0, by simp⟩
  · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hvne
    set w : Fin (n + 1) → ℝ := ‖v‖⁻¹ • v with hwdef
    have hwnn : 0 ≤ w := by
      intro i; rw [Pi.zero_apply, hwdef, Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (le_of_lt (inv_pos.mpr hvpos)) (hv i)
    have hwK : w ∈ K := by
      refine ⟨?_, hwnn⟩
      rw [Metric.mem_sphere, dist_zero_right, hwdef, norm_smul, norm_inv, Real.norm_eq_abs,
        abs_of_pos hvpos, inv_mul_cancel₀ (ne_of_gt hvpos)]
    obtain ⟨i, hi⟩ := hunit w hwK
    refine ⟨i, ?_⟩
    have hAw : (A *ᵥ w) i = ‖v‖⁻¹ * (A *ᵥ v) i := by
      rw [hwdef, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    rw [hAw] at hi
    have := mul_le_mul_of_nonneg_left hi (le_of_lt hvpos)
    rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hvpos), one_mul, mul_comm] at this

/-- **Gale–Nikaido Corollary 2.** For a P-matrix `A` there is a nonnegative `w` with every component
of `A *ᵥ w` strictly positive. This is Stiemke's theorem of the alternative: were the image of the
nonnegative orthant under `A` disjoint from the open positive orthant, a separating hyperplane would
supply `p ≥ 0`, `p ≠ 0` with `Aᵀ *ᵥ p ≤ 0`, contradicting Theorem 1 applied to the P-matrix `Aᵀ`. -/
theorem IsPMatrix.exists_nonneg_mulVec_pos {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsPMatrix) :
    ∃ w : Fin (n + 1) → ℝ, 0 ≤ w ∧ ∀ i, 0 < (A *ᵥ w) i := by
  classical
  by_contra hcon
  simp only [not_exists, not_and, not_forall, not_lt] at hcon
  set C : Set (Fin (n + 1) → ℝ) := (fun w => A *ᵥ w) '' {w | 0 ≤ w} with hCdef
  set P : Set (Fin (n + 1) → ℝ) := {q | ∀ i, 0 < q i} with hPdef
  have hCconv : Convex ℝ C := by
    rw [hCdef]
    exact (convex_Ici 0).is_linear_image ⟨fun _ _ => Matrix.mulVec_add A _ _,
      fun c v => Matrix.mulVec_smul A c v⟩
  have hPconv : Convex ℝ P := by
    intro a ha b hb s t hs ht hst i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases eq_or_lt_of_le hs with hs0 | hs0
    · have ht1 : t = 1 := by rw [← hs0] at hst; linarith
      rw [← hs0, ht1]; simp only [zero_mul, one_mul, zero_add]; exact hb i
    · exact add_pos_of_pos_of_nonneg (mul_pos hs0 (ha i)) (mul_nonneg ht (hb i).le)
  have hPopen : IsOpen P := by
    rw [hPdef, show {q : Fin (n+1) → ℝ | ∀ i, 0 < q i} = ⋂ i, (fun q => q i) ⁻¹' Set.Ioi 0 by
      ext q; simp]
    exact isOpen_iInter_of_finite fun i => (isOpen_Ioi).preimage (continuous_apply i)
  have hdisj : Disjoint P C := by
    rw [Set.disjoint_left]
    rintro q hqP ⟨w, hw, rfl⟩
    obtain ⟨i, hi⟩ := hcon w hw
    exact absurd (hqP i) (not_lt.mpr hi)
  obtain ⟨f, u, hfP, hfC⟩ := geometric_hahn_banach_open hPconv hPopen hCconv hdisj
  have h0C : (0 : Fin (n + 1) → ℝ) ∈ C := by
    refine ⟨0, ?_, ?_⟩
    · simp
    · simp
  have hu0 : u ≤ 0 := by have := hfC 0 h0C; rwa [map_zero] at this
  -- C-side scaling: f (A *ᵥ single j 1) ≥ 0
  have hfAj : ∀ j, 0 ≤ f (A *ᵥ Pi.single j 1) := by
    intro j
    by_contra hlt
    rw [not_le] at hlt
    set c := f (A *ᵥ Pi.single j 1) with hc
    set t := u / c + 1 with ht
    have htnn : 0 ≤ t := by
      rw [ht]; have : 0 ≤ u / c := div_nonneg_of_nonpos hu0 (le_of_lt hlt)
      linarith
    have hwnn : (0 : Fin (n+1) → ℝ) ≤ t • Pi.single j 1 := by
      intro i; rw [Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg htnn (by rw [Pi.single_apply]; split <;> norm_num)
    have hmem : (A *ᵥ (t • Pi.single j 1)) ∈ C := ⟨t • Pi.single j 1, hwnn, rfl⟩
    have hle := hfC _ hmem
    rw [Matrix.mulVec_smul, map_smul, smul_eq_mul, ← hc] at hle
    have htc : t * c < u := by
      rw [ht, add_mul, one_mul, div_mul_cancel₀ u (ne_of_lt hlt)]; linarith
    linarith
  -- P-side scaling: f (single i 1) ≤ 0
  have hfei : ∀ i, f (Pi.single i 1) ≤ 0 := by
    intro i
    by_contra hgt
    rw [not_le] at hgt
    set d := f (Pi.single i 1) with hd
    set t := (u - f 1) / d with ht
    have hf1 : f 1 < u := hfP 1 (fun _ => one_pos)
    have htpos : 0 < t := div_pos (by linarith) hgt
    have hqmem : (1 + t • Pi.single i 1) ∈ P := by
      intro k
      have h1 : (0 : ℝ) ≤ (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ) k := by
        rw [Pi.single_apply]; split <;> norm_num
      simp only [Pi.add_apply, Pi.one_apply, Pi.smul_apply, smul_eq_mul]
      have : 0 ≤ t * (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ) k :=
        mul_nonneg (le_of_lt htpos) h1
      linarith
    have hlt := hfP _ hqmem
    rw [map_add, map_smul, smul_eq_mul, ← hd, ht, div_mul_cancel₀ _ (ne_of_gt hgt)] at hlt
    linarith
  -- assemble p
  set p : Fin (n + 1) → ℝ := fun i => - f (Pi.single i 1) with hpdef
  have hpnn : 0 ≤ p := fun i => by rw [Pi.zero_apply, hpdef]; exact neg_nonneg.mpr (hfei i)
  have hAtp : Aᵀ *ᵥ p ≤ 0 := by
    intro j
    rw [Pi.zero_apply]
    have hcol : (A *ᵥ Pi.single j 1) = (fun i => A i j) := by
      funext i; rw [Matrix.mulVec_single]; simp
    have hrep : (fun i => A i j) = ∑ i, (A i j) • Pi.single i (1 : ℝ) := by
      funext k; simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq]
    have hsum : f (A *ᵥ Pi.single j 1) = ∑ i, A i j * f (Pi.single i 1) := by
      rw [hcol, hrep, map_sum]; simp only [map_smul, smul_eq_mul]
    have hkey : (Aᵀ *ᵥ p) j = - f (A *ᵥ Pi.single j 1) := by
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hpdef]
      rw [hsum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hkey]
    exact neg_nonpos.mpr (hfAj j)
  have hpne : p ≠ 0 := by
    intro h
    have hf1 : f 1 < u := hfP 1 (fun _ => one_pos)
    have hsum : f 1 = - ∑ i, p i := by
      rw [show (1 : Fin (n+1) → ℝ) = ∑ i, Pi.single i (1:ℝ) by
        funext k; simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq], map_sum]
      simp only [hpdef]; rw [← Finset.sum_neg_distrib]; simp
    rw [h] at hsum; simp at hsum; linarith
  exact hpne (hA.transpose.eq_zero_of_mulVec_nonpos hpnn hAtp)

end Matrix
