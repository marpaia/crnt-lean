import CRNT.Oscillation.DiagonalScaling
import CRNT.Oscillation.SimpleNegativeSpectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic.FunProp

/-!
# Fisher--Fuller positive diagonal stabilization

This is the classical nested-principal-minor induction in the right-diagonal convention used by
Vassena.  We prove the stronger Fisher--Fuller conclusion: there is a positive right diagonal
scaling whose characteristic polynomial has *distinct negative real roots*.  Hurwitz stability is
then immediate.

Induction step.  Stabilize the codimension-one predecessor with distinct negative real roots.  Give
the remaining column weight `eps`.  At `eps = 0` the characteristic polynomial is `X` times the
predecessor polynomial.  Thus its roots are the distinct negative predecessor roots plus the simple
root zero.  For small positive `eps`, continuity of roots gives one simple real root in each
disjoint root ball.  The old roots remain negative.  The full signed determinant is positive by the
`P^-_0` + nonsingular-full-minor hypothesis, so the root born from zero is negative too.
-/

namespace Matrix

open Polynomial Filter Topology

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Extend a scaling on a codimension-one principal block by a scalar weight on the complement. -/
def extendCodimOneScaling (I : Finset n) (dI : I → ℝ) (eps : ℝ) : n → ℝ :=
  fun i => if hi : i ∈ I then dI ⟨i, hi⟩ else eps

/-- The extension is positive if the block scaling and outside scalar are positive. -/
theorem extendCodimOneScaling_pos {I : Finset n} {dI : I → ℝ} {eps : ℝ}
    (hdI : ∀ i, 0 < dI i) (heps : 0 < eps) :
    ∀ i, 0 < extendCodimOneScaling I dI eps i := by
  intro i
  by_cases hi : i ∈ I
  · simp [extendCodimOneScaling, hi, hdI ⟨i, hi⟩]
  · simp [extendCodimOneScaling, hi, heps]

/-- Product of a codimension-one extended scaling. -/
theorem prod_extendCodimOneScaling
    (I : Finset n) (hcodim : I.card + 1 = Fintype.card n)
    (dI : I → ℝ) (eps : ℝ) :
    (∏ i : n, extendCodimOneScaling I dI eps i) = (∏ i : I, dI i) * eps := by
  classical
  have hcomp : (Finset.univ \ I).card = 1 := by
    rw [Finset.card_sdiff]
    simp
    omega
  obtain ⟨j, hj⟩ : ∃ j : n, Finset.univ \ I = {j} :=
    Finset.card_eq_one.mp hcomp
  have hI : ∏ i ∈ I, extendCodimOneScaling I dI eps i = ∏ i : I, dI i := by
    rw [← Finset.prod_coe_sort]
    apply Finset.prod_congr rfl
    intro i hi
    simp [extendCodimOneScaling]
  have hjnot : j ∉ I := by
    intro hjI
    have hmem : j ∈ Finset.univ \ I := by
      rw [hj]
      simp
    exact (Finset.mem_sdiff.mp hmem).2 hjI
  have hC : ∏ i ∈ Iᶜ, extendCodimOneScaling I dI eps i = eps := by
    have : Iᶜ = {j} := by simpa [Finset.compl_eq_univ_sdiff] using hj
    simp [this, extendCodimOneScaling, hjnot]
  let f := extendCodimOneScaling I dI eps
  calc
    ∏ i, f i = (∏ i ∈ Iᶜ, f i) * ∏ i ∈ I, f i :=
      (Finset.prod_compl_mul_prod I f).symm
    _ = eps * (∏ i : I, dI i) := by rw [hC, hI]
    _ = (∏ i : I, dI i) * eps := mul_comm _ _

/-- Principal predecessor of the extended scaling. -/
theorem principalSubmatrix_mul_extendCodimOneScaling
    (M : Matrix n n ℝ) (I : Finset n) (dI : I → ℝ) (eps : ℝ) :
    (M * Matrix.diagonal (extendCodimOneScaling I dI eps)).principalSubmatrix I =
      M.principalSubmatrix I * Matrix.diagonal dI := by
  ext i j
  simp [principalSubmatrix, mul_diagonal_apply, extendCodimOneScaling, i.2, j.2]

/-- At zero outside-column weight, the characteristic polynomial factors into `X` times the
predecessor characteristic polynomial. -/
theorem charpoly_extendCodimOneScaling_zero
    (M : Matrix n n ℝ) (I : Finset n)
    (hcodim : I.card + 1 = Fintype.card n) (dI : I → ℝ) :
    (M * Matrix.diagonal (extendCodimOneScaling I dI 0)).charpoly =
      Polynomial.X * (M.principalSubmatrix I * Matrix.diagonal dI).charpoly := by
  classical
  -- Reindex by the decomposition `I ⊕ Iᶜ`.  The complement has one element and its whole column
  -- is zero, giving a block-lower-triangular matrix with diagonal blocks `M_I D_I` and `[0]`.
  let e := (Equiv.sumCompl (fun i : n => i ∈ I)).symm
  let A := Matrix.reindex e e (M * Matrix.diagonal (extendCodimOneScaling I dI 0))
  let B11 := (M * Matrix.diagonal (extendCodimOneScaling I dI 0)).principalSubmatrix I
  let C := {i : n // i ∉ I}
  let B21 : Matrix C I ℝ := A.submatrix Sum.inr Sum.inl
  let B22 : Matrix C C ℝ := A.submatrix Sum.inr Sum.inr
  have hinl (i : I) : e.symm (Sum.inl i) ∈ I := by
    simp [e, Equiv.sumCompl_apply_inl]
  have hinr (i : C) : e.symm (Sum.inr i) ∉ I := by
    simpa [e, Equiv.sumCompl_apply_inr] using i.2
  have hA : A = Matrix.fromBlocks B11 0 B21 B22 := by
    ext a b
    rcases a with a | a <;> rcases b with b | b
    · simp [A, B11, e, Matrix.reindex_apply, principalSubmatrix,
        extendCodimOneScaling, Equiv.sumCompl_apply_inl]
    · simp [A, Matrix.reindex_apply, Equiv.sumCompl_apply_inl,
        Equiv.sumCompl_apply_inr, extendCodimOneScaling, hinr b]
    · simp [B21, A, Matrix.reindex_apply]
    · simp [B22, A, Matrix.reindex_apply]
  have hB22 : B22 = 0 := by
    ext i j
    simp [B22, A, Matrix.reindex_apply, Equiv.sumCompl_apply_inr,
      extendCodimOneScaling, hinr j]
  have hB11 : B11 = M.principalSubmatrix I * Matrix.diagonal dI := by
    exact principalSubmatrix_mul_extendCodimOneScaling M I dI 0
  have hcompcard : Fintype.card {i : n // i ∉ I} = 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe]
    omega
  rw [← Matrix.charpoly_reindex e]
  change A.charpoly = Polynomial.X *
    (M.principalSubmatrix I * Matrix.diagonal dI).charpoly
  rw [hA, Matrix.charpoly_fromBlocks_zero₁₂, hB22, Matrix.charpoly_zero,
    hcompcard, hB11]
  ring

/-- For a `P^-_0` matrix, a nonzero principal minor has the strict Hurwitz sign. -/
theorem IsPMinusZeroMatrix.signedPrincipalDet_pos
    {M : Matrix n n ℝ} (hP0 : M.IsPMinusZeroMatrix)
    {I : Finset n} (hne : principalDet M I ≠ 0) :
    0 < (-1 : ℝ) ^ I.card * principalDet M I := by
  have hnonneg : 0 ≤ principalDet (-M) I := hP0 I
  rw [principalDet_neg] at hnonneg
  have hne' : (-1 : ℝ) ^ I.card * principalDet M I ≠ 0 :=
    mul_ne_zero (by simp) hne
  exact lt_of_le_of_ne hnonneg (Ne.symm hne')

/-- The characteristic polynomial coefficients of the one-column family are continuous in `eps`. -/
theorem continuousAt_charpoly_extend_coeff
    (M : Matrix n n ℝ) (I : Finset n) (dI : I → ℝ) (k : ℕ) :
    ContinuousAt (fun eps : ℝ =>
      (M * Matrix.diagonal (extendCodimOneScaling I dI eps)).charpoly.coeff k) 0 := by
  let entry : ℝ → n × n → ℝ := fun eps ij =>
    (M * Matrix.diagonal (extendCodimOneScaling I dI eps)) ij.1 ij.2
  have hentry : ContinuousAt entry 0 := by
    apply continuousAt_pi.mpr
    intro ij
    have hscale : ContinuousAt
        (fun eps : ℝ => extendCodimOneScaling I dI eps ij.2) 0 := by
      by_cases hi : ij.2 ∈ I
      · simp [extendCodimOneScaling, hi]
        exact continuousAt_const
      · simp [extendCodimOneScaling, hi]
        exact continuousAt_id
    have hformula : (fun eps : ℝ => entry eps ij) =
        fun eps => M ij.1 ij.2 * extendCodimOneScaling I dI eps ij.2 := by
      funext eps
      simp [entry, Matrix.mul_diagonal_apply]
    rw [hformula]
    exact continuousAt_const.mul hscale
  let q : MvPolynomial (n × n) ℝ := (Matrix.charpoly.univ ℝ n).coeff k
  have hq : Continuous (fun x : n × n → ℝ => MvPolynomial.eval x q) := by
    simpa [q] using q.continuous_eval
  have hc := hq.continuousAt.comp hentry
  convert hc using 1
  funext eps
  change (Matrix.of (Function.curry (entry eps))).charpoly.coeff k =
    MvPolynomial.eval (entry eps) q
  exact (Matrix.charpoly.univ_coeff_eval₂Hom n (RingHom.id ℝ) (entry eps) k).symm

/-- The constant characteristic coefficient of a positive codimension-one extension has positive
Hurwitz sign whenever the full signed determinant does. -/
theorem charpoly_const_pos_extend
    (M : Matrix n n ℝ) (I : Finset n)
    (hcodim : I.card + 1 = Fintype.card n)
    (dI : I → ℝ) (hdI : ∀ i, 0 < dI i)
    (hfull : 0 < (-1 : ℝ) ^ Fintype.card n * M.det)
    {eps : ℝ} (heps : 0 < eps) :
    0 < (M * Matrix.diagonal (extendCodimOneScaling I dI eps)).charpoly.coeff 0 := by
  have hp : 0 < ∏ i : I, dI i := Finset.prod_pos fun i _ => hdI i
  let B := M * Matrix.diagonal (extendCodimOneScaling I dI eps)
  let s : ℝ := (-1 : ℝ) ^ Fintype.card n
  have hs : s * s = 1 := by
    dsimp [s]
    rw [← pow_add, ← two_mul]
    simp [pow_mul]
  have hcoeff : B.charpoly.coeff 0 = s * B.det := by
    calc
      B.charpoly.coeff 0 = (s * s) * B.charpoly.coeff 0 := by rw [hs]; simp
      _ = s * B.det := by rw [Matrix.det_eq_sign_charpoly_coeff]; ring
  have hdet : s * B.det = (s * M.det) * (∏ i : I, dI i) * eps := by
    dsimp [B, s]
    rw [Matrix.det_mul, Matrix.det_diagonal, prod_extendCodimOneScaling I hcodim]
    rw [← Finset.univ_eq_attach I]
    ring_nf
  rw [hcoeff, hdet]
  exact mul_pos (mul_pos hfull hp) heps

/-- **Bordering step with simple negative spectrum.** -/
theorem exists_small_extension_simpleNegative
    (M : Matrix n n ℝ) (I : Finset n)
    (hcodim : I.card + 1 = Fintype.card n)
    (dI : I → ℝ) (hdI : ∀ i, 0 < dI i)
    (hsimple : Polynomial.SimpleNegativeRealRoots
      (M.principalSubmatrix I * Matrix.diagonal dI).charpoly)
    (hfull : 0 < (-1 : ℝ) ^ Fintype.card n * M.det) :
    ∃ eps : ℝ, 0 < eps ∧
      Nonempty (Polynomial.SimpleNegativeRealRoots
        (M * Matrix.diagonal (extendCodimOneScaling I dI eps)).charpoly) := by
  let q : ℝ → Polynomial ℝ := fun eps =>
    (M * Matrix.diagonal (extendCodimOneScaling I dI eps)).charpoly
  have hqmonic : ∀ eps, (q eps).Monic := fun eps => Matrix.charpoly_monic _
  have hqdeg : ∀ eps, (q eps).natDegree =
      (M.principalSubmatrix I * Matrix.diagonal dI).charpoly.natDegree + 1 := by
    intro eps
    simp [q, hcodim]
  have hqzero : q 0 = Polynomial.X *
      (M.principalSubmatrix I * Matrix.diagonal dI).charpoly := by
    simpa [q] using charpoly_extendCodimOneScaling_zero M I hcodim dI
  have hqcoeff : ∀ k, ContinuousAt (fun eps => (q eps).coeff k) 0 := by
    intro k
    exact continuousAt_charpoly_extend_coeff M I dI k
  have hconst : ∀ eps, 0 < eps → 0 < (q eps).coeff 0 := by
    intro eps heps
    exact charpoly_const_pos_extend M I hcodim dI hdI hfull heps
  have hev := Polynomial.eventually_simpleNegativeRealRoots_of_zeroExtension
    hsimple hqmonic hqdeg hqzero hqcoeff hconst
  obtain ⟨eps, hepsmem, hepspos⟩ := (hev.and self_mem_nhdsWithin).exists
  exact ⟨eps, hepspos, hepsmem⟩


/-- Transitive closure of an adjacent nested-finset chain. -/
theorem nested_finset_chain_subset
    {κ : ℕ → Finset n}
    (hnest : ∀ k : ℕ, 1 ≤ k → k < Fintype.card n → κ k ⊆ κ (k + 1))
    {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ Fintype.card n) :
  κ a ⊆ κ b := by
  suffices h : ∀ d b, b - a = d → a ≤ b → b ≤ Fintype.card n → κ a ⊆ κ b by
    exact h (b - a) b rfl hab hb
  intro d
  induction d with
  | zero =>
      intro b hdiff hab hb
      have hba : b = a := by omega
      subst b
      exact Finset.Subset.rfl
  | succ d ih =>
      intro b hdiff hab hb
      have hprevdiff : (b - 1) - a = d := by omega
      have hprev := ih (b - 1) hprevdiff (by omega) (by omega)
      have hstep := hnest (b - 1) (by omega) (by omega)
      rw [← Nat.sub_add_cancel (by omega : 1 ≤ b)]
      exact hprev.trans hstep

/-- Principal determinants are unchanged when a principal block is restricted once more. -/
theorem principalDet_principalSubmatrix
    (M : Matrix n n ℝ) (I : Finset n) (J : Finset I) :
    principalDet (M.principalSubmatrix I) J =
      principalDet M (J.image Subtype.val) := by
  classical
  let K := J.image (Subtype.val : I → n)
  let e : {i : I // i ∈ J} ≃ {i : n // i ∈ K} :=
    { toFun := fun i => ⟨i.1.1, Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩⟩
      invFun := fun i => ⟨(Finset.mem_image.mp i.2).choose,
        (Finset.mem_image.mp i.2).choose_spec.1⟩
      left_inv := by
        intro i
        apply Subtype.ext
        apply Subtype.ext
        exact (Finset.mem_image.mp (Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩)).choose_spec.2
      right_inv := by
        intro i
        apply Subtype.ext
        exact (Finset.mem_image.mp i.2).choose_spec.2 }
  have hmat :
      (M.submatrix (fun i : I => (i : n)) (fun i : I => (i : n))).submatrix
        (fun i : {i : I // i ∈ J} => i.1) (fun i : {i : I // i ∈ J} => i.1) =
      Matrix.reindex e.symm e.symm
        (M.submatrix (fun i : {i : n // i ∈ K} => (i : n))
          (fun i : {i : n // i ∈ K} => (i : n))) := by
    ext i j
    rfl
  change
    ((M.submatrix (fun i : I => (i : n)) (fun i : I => (i : n))).submatrix
      (fun i : {i : I // i ∈ J} => i.1) (fun i : {i : I // i ∈ J} => i.1)).det =
    (M.submatrix (fun i : {i : n // i ∈ K} => (i : n))
      (fun i : {i : n // i ∈ K} => (i : n))).det
  rw [hmat, Matrix.det_reindex_self]

/-- The principal determinant on the full index set is the determinant of the matrix. -/
theorem principalDet_univ (M : Matrix n n ℝ) :
    principalDet M Finset.univ = M.det := by
  simp only [principalDet]
  have he : (fun i : {x // x ∈ (Finset.univ : Finset n)} => (i : n)) =
      (Equiv.subtypeUnivEquiv (fun i => Finset.mem_univ i) : _ → n) := rfl
  rw [he, Matrix.det_submatrix_equiv_self]

/-- Restrict a Fisher--Fuller chain to its codimension-one predecessor. -/
theorem IsFisherFullerPMinusMatrix.predecessor
    {M : Matrix n n ℝ} (h : M.IsFisherFullerPMinusMatrix)
    (hcard : 1 < Fintype.card n) :
    ∃ I : Finset n,
      I.card + 1 = Fintype.card n ∧
      (M.principalSubmatrix I).IsFisherFullerPMinusMatrix ∧
      principalDet M I ≠ 0 := by
  classical
  obtain ⟨hP0, hnpos, κ, hminor, hnest, hfull⟩ := h
  let N := Fintype.card n
  let I := κ (N - 1)
  have hNm1 : 1 ≤ N - 1 := by omega
  have hNm1N : N - 1 ≤ N := Nat.sub_le _ _
  have hIcard : I.card = N - 1 := (hminor (N - 1) hNm1 hNm1N).1
  have hIdet : principalDet M I ≠ 0 := (hminor (N - 1) hNm1 hNm1N).2
  have hcodim : I.card + 1 = N := by omega
  have hcardI : Fintype.card I = I.card := by simp
  have hcardIeq : Fintype.card I = N - 1 := by simpa [hIcard] using hcardI
  refine ⟨I, hcodim, ?_, hIdet⟩
  have hsubchain : ∀ k, 1 ≤ k → k ≤ N - 1 → κ k ⊆ I := by
    intro k hk hkN
    apply Finset.Subset.trans (show κ k ⊆ κ (N - 1) by
      exact nested_finset_chain_subset hnest hk hkN hNm1N)
    rfl
  let pull : (J : Finset n) → J ⊆ I → Finset I := fun J hJI =>
    J.attach.map ⟨fun j => ⟨j.1, hJI j.2⟩,
      by intro a b hab; apply Subtype.ext; exact congrArg (fun x : I => (x : n)) hab⟩
  have hpull_image (J : Finset n) (hJI : J ⊆ I) :
      (pull J hJI).image Subtype.val = J := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨y, hy, hyx⟩
      rcases Finset.mem_map.mp hy with ⟨z, hz, hzy⟩
      have hzx : (z : n) = x := by
        calc
          (z : n) = (⟨(z : n), hJI z.property⟩ : I) := rfl
          _ = y := congrArg (fun q : I => (q : n)) hzy
          _ = x := hyx
      exact hzx ▸ z.property
    · intro hx
      apply Finset.mem_image.mpr
      refine ⟨⟨x, hJI hx⟩, ?_, rfl⟩
      apply Finset.mem_map.mpr
      refine ⟨⟨x, hx⟩, Finset.mem_attach _ _, ?_⟩
      rfl
  have hpull_card (J : Finset n) (hJI : J ⊆ I) : (pull J hJI).card = J.card := by
    simp [pull]
  refine ⟨?_, by rw [hcardIeq]; omega,
    fun k => if hk : 1 ≤ k ∧ k ≤ N - 1 then pull (κ k) (hsubchain k hk.1 hk.2) else ∅,
    ?_, ?_, ?_⟩
  · intro J
    change 0 ≤ principalDet (-(M.principalSubmatrix I)) J
    have hbase : 0 ≤ principalDet ((-M).principalSubmatrix I) J := by
      rw [principalDet_principalSubmatrix]
      exact hP0 (J.image (fun j : I => (j : n)))
    have hmatrix : (-M).principalSubmatrix I = -(M.principalSubmatrix I) := by
      simp [principalSubmatrix, Matrix.submatrix_neg]
    rw [← hmatrix]
    exact hbase
  · intro k hk hkN
    have hkNm1 : k ≤ N - 1 := by simpa [hcardIeq] using hkN
    have hkN' : k ≤ N := by omega
    have hkcond : 1 ≤ k ∧ k ≤ N - 1 := ⟨hk, hkNm1⟩
    change (if hk' : 1 ≤ k ∧ k ≤ N - 1 then
        pull (κ k) (hsubchain k hk'.1 hk'.2) else ∅).card = k ∧
      principalDet (M.principalSubmatrix I)
        (if hk' : 1 ≤ k ∧ k ≤ N - 1 then
          pull (κ k) (hsubchain k hk'.1 hk'.2) else ∅) ≠ 0
    rw [dif_pos hkcond]
    constructor
    · rw [hpull_card]
      exact (hminor k hk hkN').1
    · have hdetEq : principalDet (M.principalSubmatrix I)
          (pull (κ k) (hsubchain k hk hkNm1)) = principalDet M (κ k) := by
        rw [principalDet_principalSubmatrix, hpull_image]
      rw [hdetEq]
      exact (hminor k hk hkN').2
  · intro k hk hklt
    have hkNm1 : k ≤ N - 1 := by simpa [hcardIeq] using Nat.le_of_lt hklt
    have hkltNm1 : k < N - 1 := by simpa [hcardIeq] using hklt
    have hkNext : k + 1 ≤ N - 1 := Nat.succ_le_of_lt hkltNm1
    have hkcond : 1 ≤ k ∧ k ≤ N - 1 := ⟨hk, hkNm1⟩
    have hkNextCond : 1 ≤ k + 1 ∧ k + 1 ≤ N - 1 := ⟨by omega, hkNext⟩
    change (if hk' : 1 ≤ k ∧ k ≤ N - 1 then
        pull (κ k) (hsubchain k hk'.1 hk'.2) else ∅) ⊆
      (if hk' : 1 ≤ k + 1 ∧ k + 1 ≤ N - 1 then
        pull (κ (k + 1)) (hsubchain (k + 1) hk'.1 hk'.2) else ∅)
    rw [dif_pos hkcond, dif_pos hkNextCond]
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_map.mp hx
    have hy' : (y.1 : n) ∈ κ (k + 1) := hnest k hk (by omega) y.2
    apply Finset.mem_map.mpr
    refine ⟨⟨y.1, hy'⟩, Finset.mem_attach _ _, ?_⟩
    apply Subtype.ext
    exact congrArg (fun z : I => (z : n)) hxy
  · rw [hcardIeq]
    change (if hk : 1 ≤ N - 1 ∧ N - 1 ≤ N - 1 then
      pull (κ (N - 1)) (hsubchain (N - 1) hk.1 hk.2) else ∅) = Finset.univ
    rw [dif_pos ⟨hNm1, le_rfl⟩]
    change pull I (by intro x hx; exact hx) = Finset.univ
    ext x
    simp [pull]

/-- Strong Fisher--Fuller form: positive diagonal scaling with distinct negative real spectrum. -/
theorem fisherFullerSimpleNegativeScaling
    {M : Matrix n n ℝ} (hFF : M.IsFisherFullerPMinusMatrix) :
    ∃ d : n → ℝ, (∀ i, 0 < d i) ∧
      Nonempty (Polynomial.SimpleNegativeRealRoots (M * Matrix.diagonal d).charpoly) := by
  classical
  induction hN : Fintype.card n using Nat.strong_induction_on generalizing n with
  | h N ih =>
      by_cases hN1 : N = 1
      · have hcardOne : Fintype.card n = 1 := by simpa [hN] using hN1
        obtain ⟨i, hi⟩ := Fintype.card_eq_one_iff.mp hcardOne
        letI : Unique n := ⟨⟨i⟩, fun y => hi y⟩
        have hneg : M i i < 0 := by
          have hdet' : principalDet M Finset.univ ≠ 0 := by
            rw [principalDet_univ]
            exact hFF.det_ne_zero
          have hsign := hFF.1.signedPrincipalDet_pos hdet'
          have hdet : M.det = M i i := Matrix.det_eq_elem_of_subsingleton M i
          have hcard : Fintype.card n = 1 := by omega
          rw [principalDet_univ, hdet] at hsign
          have hpos : 0 < (-1 : ℝ) * M i i := by
            simpa [hcard] using hsign
          linarith
        let d : n → ℝ := fun _ => 1
        refine ⟨d, fun _ => zero_lt_one, ?_⟩
        refine ⟨{
          roots := {M i i}
          card_roots := by simp [d]
          nodup := by simp
          negative := by
            intro r hr
            have hr' : r = M i i := Multiset.mem_singleton.mp hr
            simpa [hr'] using hneg
          factorization := ?_ }⟩
        have hchar : (M * Matrix.diagonal d).charpoly = X - C (M i i) := by
          have hdefault : (default : n) = i := Subsingleton.elim _ _
          simp [Matrix.charpoly, d, hdefault, Matrix.det_eq_elem_of_subsingleton]
        simpa [hchar]
      · have hNgt : 1 < N := by
          have hpos : 0 < N := by simpa [hN] using hFF.2.1
          omega
        obtain ⟨I, hcodim, hFFI, hIdet⟩ := hFF.predecessor (by simpa [hN] using hNgt)
        have hIlt : Fintype.card I < N := by
          simp [Fintype.card_coe]
          omega
        obtain ⟨dI, hdI, ⟨hSimpleI⟩⟩ :=
          ih (Fintype.card I) hIlt hFFI rfl
        have hfullsign : 0 < (-1 : ℝ) ^ Fintype.card n * M.det := by
          have hdet' : principalDet M Finset.univ ≠ 0 := by
            rw [principalDet_univ]
            exact hFF.det_ne_zero
          simpa [principalDet_univ] using
            hFF.1.signedPrincipalDet_pos (I := Finset.univ) hdet'
        obtain ⟨eps, heps, hSimpleFull⟩ := exists_small_extension_simpleNegative
          M I hcodim dI hdI hSimpleI hfullsign
        exact ⟨extendCodimOneScaling I dI eps,
          extendCodimOneScaling_pos hdI heps, hSimpleFull⟩

/-- **Fisher--Fuller theorem, closed in the exact form consumed by Vassena Criterion II.** -/
theorem fisherFullerStabilizingScaling : FisherFullerStabilizingScalingTarget := by
  intro m _ _ M hFF
  obtain ⟨d, hd, ⟨hsimple⟩⟩ := fisherFullerSimpleNegativeScaling hFF
  exact ⟨d, hd, isHurwitzReal_of_simpleNegativeRealRoots hsimple⟩

end Matrix
