import CRNT.Deficiency.PositiveKineticObstructionIVT
import CRNT.Deficiency.ClassConservation

/-!
# Linkage-scale invariance of the deficiency logarithmic obstruction

A deficiency vector has zero total mass on each linkage class.  Consequently the scalar
logarithmic obstruction is unchanged when a positive complex vector is multiplied by an
arbitrary positive constant on each linkage class.  This is the quotient symmetry behind the
Type-II Boros reduction: Birch transport changes only linkage scales, hence cannot change the
one-dimensional deficiency obstruction.
-/

namespace CRNT.Network

open scoped BigOperators Classical
open Matrix

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The logarithmic deficiency pairing is invariant under arbitrary positive linkage-class
rescaling. -/
theorem deficiencyLogObstruction_classScale_invariant
    (N : Network S) {g v : N.ComplexIdx → ℝ} (hg : g ∈ N.deficiencySubspace)
    (hv : ∀ c, 0 < v c) {mu : Quotient N.linkedSetoid → ℝ} (hmu : ∀ q, 0 < mu q) :
    (∑ c, g c * Real.log (mu (N.classOf c) * v c)) =
      ∑ c, g c * Real.log (v c) := by
  have hlog : ∀ c, Real.log (mu (N.classOf c) * v c) =
      Real.log (mu (N.classOf c)) + Real.log (v c) := by
    intro c
    exact Real.log_mul (ne_of_gt (hmu _)) (ne_of_gt (hv c))
  simp_rw [hlog, mul_add, Finset.sum_add_distrib]
  have hscale : (∑ c, g c * Real.log (mu (N.classOf c))) = 0 := by
    obtain ⟨q, hq⟩ := (Submodule.mem_inf.mp hg).2
    let w : N.ComplexIdx → ℝ := fun c => Real.log (mu (N.classOf c))
    have hwker : w ∈ LinearMap.ker (N.incidenceMatrixᵀ.mulVecLin) := by
      rw [N.ker_incidenceTranspose]
      refine ⟨fun q => Real.log (mu q), ?_⟩
      funext c
      rfl
    have hpair := N.incidenceTranspose_pairing w q
    have hleft : (∑ r, N.incidenceMatrixᵀ.mulVec w r * q r) = 0 := by
      have hz : N.incidenceMatrixᵀ.mulVecLin w = 0 := LinearMap.mem_ker.mp hwker
      have hz' : N.incidenceMatrixᵀ *ᵥ w = 0 := hz
      rw [hz']
      simp
    rw [hleft, hq] at hpair
    simpa [w, mul_comm] using hpair.symm
  simpa [hscale]

/-- Any positive linkage-class-scaled monomial vector annihilates every deficiency
logarithmic pairing. -/
theorem deficiencyLogObstruction_eq_zero_of_classScaledMonomial
    (N : Network S) {g v : N.ComplexIdx → ℝ} (hg : g ∈ N.deficiencySubspace)
    {x : Concentration S} (hx : x.Positive)
    {lambda : Quotient N.linkedSetoid → ℝ} (hlambda : ∀ q, 0 < lambda q)
    (hv : ∀ c, v c = lambda (N.classOf c) * N.complexMonomialVector x c) :
    (∑ c, g c * Real.log (v c)) = 0 := by
  have hmonoPos : ∀ c, 0 < N.complexMonomialVector x c := by
    intro c
    simpa [N.complexMonomialVector_apply] using Complex.massActionMonomial_pos hx c.val
  have hinv := N.deficiencyLogObstruction_classScale_invariant hg hmonoPos hlambda
  have hgY : N.complexMap g = 0 := LinearMap.mem_ker.mp hg.1
  have hzero := N.affineLogObstruction_eq_zero_of_complexMonomialVector
    (g := g) (v := N.complexMonomialVector x) hgY hx rfl
  rw [← hinv] at hzero
  simpa [hv] using hzero

/-- At deficiency one, the scalar logarithmic equation exactly characterizes positive vectors
that are monomial up to one positive scalar per linkage class. -/
theorem deficiencyOne_logObstruction_zero_iff_classScaledMonomial
    (N : Network S) (hδ : N.DeficiencyOne)
    {g v : N.ComplexIdx → ℝ} (hg : g ∈ N.deficiencySubspace) (hg0 : g ≠ 0)
    (hspan : ∀ w ∈ N.deficiencySubspace, ∃ a : ℝ, a • g = w)
    (hvpos : ∀ c, 0 < v c) :
    (∑ c, g c * Real.log (v c)) = 0 ↔
      ∃ (x : Concentration S) (lambda : Quotient N.linkedSetoid → ℝ),
        x.Positive ∧ (∀ q, 0 < lambda q) ∧
        ∀ c, v c = lambda (N.classOf c) * N.complexMonomialVector x c := by
  constructor
  · intro hzero
    exact N.exists_classScales_monomial_of_deficiencyOne_logObstruction_zero
      hδ hg hg0 hspan hvpos hzero
  · rintro ⟨x, lambda, hx, hlambda, hv⟩
    exact N.deficiencyLogObstruction_eq_zero_of_classScaledMonomial hg hx hlambda hv

/-- Zero of the obstruction is therefore invariant under positive linkage-class rescaling. -/
theorem deficiencyLogObstruction_classScale_eq_zero_iff
    (N : Network S) {g v : N.ComplexIdx → ℝ} (hg : g ∈ N.deficiencySubspace)
    (hv : ∀ c, 0 < v c) {mu : Quotient N.linkedSetoid → ℝ} (hmu : ∀ q, 0 < mu q) :
    (∑ c, g c * Real.log (mu (N.classOf c) * v c)) = 0 ↔
      (∑ c, g c * Real.log (v c)) = 0 := by
  rw [N.deficiencyLogObstruction_classScale_invariant hg hv hmu]

end CRNT.Network
