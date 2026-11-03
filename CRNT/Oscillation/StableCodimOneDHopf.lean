import CRNT.Oscillation.FisherFullerScaling
import CRNT.Oscillation.HurwitzBordering
import CRNT.Oscillation.DHopf

/-!
# Stable-codimension-one class-II cores give D-Hopf witnesses

The second branch in the 2026 class-II definition does not require a separate spectral theorem.
If an unstable negative-feedback core has a Hurwitz principal block of codimension one, keep that
block at unit column scaling and make the one missing column sufficiently small.  The Fisher--Fuller
bordering lemma makes the full matrix Hurwitz.  At the identity scaling the original matrix still
has a strict right-half-plane eigenvalue.  The negative-feedback determinant sign gives
nonsingularity.
-/

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Reindexing preserves the characteristic-polynomial spectral predicates. -/
theorem IsHurwitzReal.reindex {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (e : m ≃ n) (M : Matrix m m ℝ)
    (hM : M.IsHurwitzReal) : (Matrix.reindex e e M).IsHurwitzReal := by
  change CRNT.IsHurwitz
    ((Matrix.reindex e e (M.map (algebraMap ℝ ℂ))).charpoly)
  rw [Matrix.charpoly_reindex e (M.map (algebraMap ℝ ℂ))]
  exact hM

theorem HasUnstableEigenvalue.reindex {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (e : m ≃ n) (M : Matrix m m ℝ)
    (hM : M.HasUnstableEigenvalue) :
    (Matrix.reindex e e M).HasUnstableEigenvalue := by
  change ∃ z : ℂ, z ∈
    (Matrix.reindex e e (M.map (algebraMap ℝ ℂ))).charpoly.roots ∧ 0 < z.re
  rw [Matrix.charpoly_reindex e (M.map (algebraMap ℝ ℂ))]
  exact hM

theorem HasNegativeFeedbackSign.reindex {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (e : m ≃ n) (M : Matrix m m ℝ)
    (hM : M.HasNegativeFeedbackSign) :
    (Matrix.reindex e e M).HasNegativeFeedbackSign := by
  unfold HasNegativeFeedbackSign at hM ⊢
  rw [Matrix.det_reindex_self e M]
  have hcard : Fintype.card n = Fintype.card m := Fintype.card_congr e.symm
  simpa [hcard] using hM

/-- Mapping a finite set along an equivalence induces an equivalence of its subtypes. -/
def mapFinsetEquiv {m n : Type*} (e : m ≃ n) (I : Finset m) :
    {x // x ∈ I} ≃ {y // y ∈ I.map e.toEmbedding} where
  toFun x := ⟨e x.1, Finset.mem_map.mpr ⟨x.1, x.2, rfl⟩⟩
  invFun y := ⟨e.symm y.1, by
    obtain ⟨x, hx, hxy⟩ := Finset.mem_map.mp y.2
    change e x = y.1 at hxy
    rw [← hxy]
    simpa using hx⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp

/-- Stable codimension-one principal submatrices transport across a reindexing equivalence. -/
theorem HasStableCodimOnePrincipalSubmatrix.reindex {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (e : m ≃ n) (M : Matrix m m ℝ)
    (hM : M.HasStableCodimOnePrincipalSubmatrix) :
    (Matrix.reindex e e M).HasStableCodimOnePrincipalSubmatrix := by
  classical
  obtain ⟨I, hIcard, hIstab⟩ := hM
  let J := I.map e.toEmbedding
  let eI := mapFinsetEquiv e I
  have hprincipal :
      (Matrix.reindex e e M).principalSubmatrix J =
        Matrix.reindex eI eI (M.principalSubmatrix I) := by
    ext i j
    rfl
  have hJcard : J.card = I.card := by simp [J]
  have hJstable : ((Matrix.reindex e e M).principalSubmatrix J).IsHurwitzReal := by
    rw [hprincipal]
    exact IsHurwitzReal.reindex eI (M.principalSubmatrix I) hIstab
  refine ⟨J, ?_, hJstable⟩
  rw [hJcard, Fintype.card_congr e.symm]
  exact hIcard

/-- The stable codimension-one branch directly gives a strong D-Hopf witness on the full matrix. -/
theorem strongDHopf_of_stableCodimOne
    (hrootCluster : Polynomial.ZeroBorderRootClusterContinuityTarget)
    {M : Matrix n n ℝ}
    (hunstable : M.HasUnstableEigenvalue)
    (hfullsign : M.HasNegativeFeedbackSign)
    (hcodim : M.HasStableCodimOnePrincipalSubmatrix) :
    Nonempty (StrongDHopfWitness M) := by
  classical
  obtain ⟨I, hIcard, hIstab⟩ := hcodim
  let dI : I → ℝ := fun _ => 1
  have hdI : ∀ i, 0 < dI i := fun _ => zero_lt_one
  have hIstab' : IsHurwitzReal (M.principalSubmatrix I * Matrix.diagonal dI) := by
    have hdiag : Matrix.diagonal dI = (1 : Matrix I I ℝ) := by
      ext i j
      simp [dI, Matrix.diagonal_apply, Matrix.one_apply]
    simpa [hdiag] using hIstab
  have hIdet : principalDet M I ≠ 0 := by
    intro hzero
    have hsubdet : (M.principalSubmatrix I).det = 0 := by
      simpa [principalDet, principalSubmatrix] using hzero
    exact hIstab.det_ne_zero hsubdet
  have hIsign : 0 < (-1 : ℝ) ^ I.card * principalDet M I := by
    have hsubsign : 0 < (-1 : ℝ) ^ Fintype.card I * (M.principalSubmatrix I).det :=
      IsHurwitzReal.signed_det_pos hIstab
    simpa [Fintype.card_coe, principalDet, principalSubmatrix] using hsubsign
  have hfullsign' : 0 < (-1 : ℝ) ^ Fintype.card n * M.det := hfullsign
  have hMdet : M.det ≠ 0 := by
    intro hzero
    have hs : 0 < (-1 : ℝ) ^ Fintype.card n * M.det := hfullsign
    rw [hzero, mul_zero] at hs
    exact (lt_irrefl 0) hs
  obtain ⟨eps, heps, hstable⟩ := exists_small_extension_hurwitz
    hrootCluster M I hIcard dI hdI hIstab' hIsign hfullsign'
  refine ⟨
    { nonsingular := hMdet
      stableDiagonal := extendCodimOneScaling I dI eps
      stablePositive := extendCodimOneScaling_pos hdI heps
      unstableDiagonal := fun _ => 1
      unstablePositive := fun _ => zero_lt_one
      stable := hstable
      unstable := ?_ }⟩
  have hdiag : Matrix.diagonal (fun _ : n => (1 : ℝ)) = (1 : Matrix n n ℝ) := by
    ext i j
    simp [Matrix.diagonal_apply, Matrix.one_apply]
  simpa [hdiag] using hunstable

/-- The formerly isolated stable-codimension-one class-II target is now a theorem. -/
theorem stableCodimOneClassIIImpliesStrongDHopfBlock
    (hrootCluster : Polynomial.ZeroBorderRootClusterContinuityTarget) :
    StableCodimOneClassIIImpliesStrongDHopfBlockTarget := by
  intro m _ _ M hneg hcodim
  refine ⟨Finset.univ, ?_⟩
  let e : {i : m // i ∈ (Finset.univ : Finset m)} ≃ m :=
    Equiv.subtypeUnivEquiv (fun i => Finset.mem_univ i)
  have hfull : M.principalSubmatrix (Finset.univ : Finset m) =
      Matrix.reindex e.symm e.symm M := by
    ext i j
    rfl
  have hunstable := HasUnstableEigenvalue.reindex e.symm M hneg.1.1
  have hsign := HasNegativeFeedbackSign.reindex e.symm M hneg.2
  have hcodim' := HasStableCodimOnePrincipalSubmatrix.reindex e.symm M hcodim
  rw [hfull]
  exact strongDHopf_of_stableCodimOne hrootCluster hunstable hsign hcodim'

end Matrix
