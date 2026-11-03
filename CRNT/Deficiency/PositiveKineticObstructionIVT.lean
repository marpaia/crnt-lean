import CRNT.Deficiency.PositiveKineticSection
import CRNT.Analysis.FixedPoint
import CRNT.Deficiency.CycleExactSequence
import CRNT.Stoich.Transpose

/-!
# Scalar obstruction along a positive affine kinetic section

This is the analytic IVT layer in the Type-II Boros reduction.  Once a deficiency generator `g`
and an affine positive kinetic section `v(a)=b+a z` have been chosen, the only logarithmic
compatibility functional needed by the deficiency-one argument is

`F(a) = ∑ c, g c * log (v(a) c)`.

The lemmas below prove continuity on the positivity interval and isolate the exact endpoint-sign
obligation needed for Bolzano/IVT.
-/

namespace CRNT.Network

open scoped BigOperators Classical Topology
open Matrix

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The scalar logarithmic obstruction paired with a deficiency vector. -/
noncomputable def affineLogObstruction (N : Network S)
    (g b z : N.ComplexIdx → ℝ) (a : ℝ) : ℝ :=
  ∑ c, g c * Real.log ((b + a • z) c)

/-- The logarithmic obstruction is continuous throughout every interval on which the affine
kinetic section stays strictly positive. -/
theorem continuousOn_affineLogObstruction
    (N : Network S) (g b z : N.ComplexIdx → ℝ) {ε : ℝ}
    (hpos : ∀ a, |a| < ε → ∀ c, 0 < (b + a • z) c) :
    ContinuousOn (N.affineLogObstruction g b z) (Set.Ioo (-ε) ε) := by
  have hlog := continuousOn_log_positiveAffineKineticSection b z hpos
  have hlogc := continuousOn_pi.mp hlog
  unfold affineLogObstruction
  apply continuousOn_finset_sum
  intro c _
  exact continuousOn_const.mul (hlogc c)

/-- **Bolzano closure of the Type-II scalar step.**  If two interior parameters have opposite
signs for the logarithmic obstruction, some parameter between them has zero obstruction. -/
theorem exists_affineLogObstruction_eq_zero_of_sign_change
    (N : Network S) (g b z : N.ComplexIdx → ℝ) {ε aL aR : ℝ}
    (hpos : ∀ a, |a| < ε → ∀ c, 0 < (b + a • z) c)
    (hminus : aL ∈ Set.Ioo (-ε) ε) (hplus : aR ∈ Set.Ioo (-ε) ε)
    (hle : aL ≤ aR)
    (hsign : N.affineLogObstruction g b z aL ≤ 0 ∧
      0 ≤ N.affineLogObstruction g b z aR) :
    ∃ a ∈ Set.Icc aL aR, N.affineLogObstruction g b z a = 0 := by
  have hsub : Set.Icc aL aR ⊆ Set.Ioo (-ε) ε := by
    intro a ha
    exact ⟨lt_of_lt_of_le hminus.1 ha.1, lt_of_le_of_lt ha.2 hplus.2⟩
  have hcont : ContinuousOn (N.affineLogObstruction g b z) (Set.Icc aL aR) :=
    (N.continuousOn_affineLogObstruction g b z hpos).mono hsub
  have hmem : (0 : ℝ) ∈ N.affineLogObstruction g b z '' Set.Icc aL aR :=
    intermediate_value_Icc hle hcont ⟨hsign.1, hsign.2⟩
  rcases hmem with ⟨a, ha, hzero⟩
  exact ⟨a, ha, hzero⟩

/-- Every exactly realized monomial vector annihilates the deficiency logarithmic functional.
Thus zero of `affineLogObstruction` is a necessary condition for the affine kinetic section to
hit the mass-action monomial image. -/
theorem affineLogObstruction_eq_zero_of_complexMonomialVector
    (N : Network S) {g v : N.ComplexIdx → ℝ} (hgY : N.complexMap g = 0)
    {x : Concentration S} (hx : x.Positive) (hv : N.complexMonomialVector x = v) :
    (∑ c, g c * Real.log (v c)) = 0 := by
  have hterm : ∀ c, g c * Real.log (v c) =
      ∑ s, g c * ((c.val s : ℝ) * Real.log (x s)) := by
    intro c
    rw [← hv, N.log_complexMonomialVector hx c, Finset.mul_sum]
  simp only [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro s _
  rw [show (∑ c, g c * ((c.val s : ℝ) * Real.log (x s))) =
      (∑ c, g c * (c.val s : ℝ)) * Real.log (x s) by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c _
    ring]
  have hY : ∑ c, g c * (c.val s : ℝ) = 0 := by
    have hs := congrFun hgY s
    simpa [N.complexMap_apply] using hs
  rw [hY, zero_mul]

/-- Specialized to the affine section. -/
theorem affineLogObstruction_eq_zero_of_affine_monomial_realization
    (N : Network S) {g b z : N.ComplexIdx → ℝ} (hgY : N.complexMap g = 0)
    {a : ℝ} {x : Concentration S} (hx : x.Positive)
    (hmono : N.complexMonomialVector x = b + a • z) :
    N.affineLogObstruction g b z a = 0 := by
  unfold affineLogObstruction
  exact N.affineLogObstruction_eq_zero_of_complexMonomialVector hgY hx hmono

/-- Transpose/incidence pairing in the coordinate conventions used by the CRNT library. -/
theorem incidenceTranspose_pairing (N : Network S) (w : N.ComplexIdx → ℝ) (q : N.R → ℝ) :
    (∑ r, N.incidenceMatrixᵀ.mulVec w r * q r) =
      ∑ c, w c * N.incidenceMap q c := by
  change (N.incidenceMatrixᵀ.mulVec w) ⬝ᵥ q = w ⬝ᵥ N.incidenceMap q
  rw [N.incidenceMap_eq_mulVecLin]
  change (N.incidenceMatrixᵀ.mulVec w) ⬝ᵥ q = w ⬝ᵥ N.incidenceMatrix.mulVec q
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

/-- At deficiency one, vanishing of the scalar deficiency pairing is sufficient for all reaction
edge log-ratios to come from a species potential.  This is the precise one-dimensional
row-space obstruction statement. -/
theorem exists_speciesPotential_of_deficiencyOne_logObstruction_zero
    (N : Network S) (hδ : N.DeficiencyOne)
    {g v : N.ComplexIdx → ℝ} (hg : g ∈ N.deficiencySubspace) (hg0 : g ≠ 0)
    (hspan : ∀ w ∈ N.deficiencySubspace, ∃ a : ℝ, a • g = w)
    (hvpos : ∀ c, 0 < v c)
    (hobs : (∑ c, g c * Real.log (v c)) = 0) :
    ∃ p : S → ℝ, ∀ r : N.R,
      Real.log (v (N.targetIdx r)) - Real.log (v (N.sourceIdx r)) =
        ∑ s : S, N.reactionVector r s * p s := by
  let beta : N.R → ℝ := N.incidenceMatrixᵀ.mulVec (fun c => Real.log (v c))
  have hbetaOrth : beta ∈ orthSum (LinearMap.ker N.stoichMap) := by
    rw [mem_orthSum]
    intro q hq
    have hd : N.incidenceMap q ∈ N.deficiencySubspace := by
      constructor
      · apply LinearMap.mem_ker.mpr
        have hfac := congrArg (fun f => f q) N.complexMap_comp_incidenceMap
        have hs : N.stoichMap q = 0 := hq
        simpa [hs] using hfac
      · exact ⟨q, rfl⟩
    obtain ⟨a, ha⟩ := hspan (N.incidenceMap q) hd
    rw [show (∑ r, beta r * q r) =
        ∑ c, Real.log (v c) * N.incidenceMap q c by
      exact N.incidenceTranspose_pairing (fun c => Real.log (v c)) q]
    rw [← ha]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show (∑ c, Real.log (v c) * (a * g c)) =
        a * ∑ c, g c * Real.log (v c) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring]
    rw [hobs, mul_zero]
  obtain ⟨p, hp⟩ := (N.mem_orthSum_ker_iff_exists_stoichPotential beta).mp hbetaOrth
  refine ⟨p, ?_⟩
  intro r
  have hr := hp r
  rw [show beta r = Real.log (v (N.targetIdx r)) - Real.log (v (N.sourceIdx r)) by
    exact N.incidenceTranspose_apply (fun c => Real.log (v c)) r] at hr
  exact hr

/-- Vanishing of the one-dimensional deficiency obstruction realizes a positive complex vector as
mass-action monomials up to one positive multiplicative constant on each linkage class. -/
theorem exists_classScales_monomial_of_deficiencyOne_logObstruction_zero
    (N : Network S) (hδ : N.DeficiencyOne)
    {g v : N.ComplexIdx → ℝ} (hg : g ∈ N.deficiencySubspace) (hg0 : g ≠ 0)
    (hspan : ∀ w ∈ N.deficiencySubspace, ∃ a : ℝ, a • g = w)
    (hvpos : ∀ c, 0 < v c)
    (hobs : (∑ c, g c * Real.log (v c)) = 0) :
    ∃ (x : Concentration S) (lambda : Quotient N.linkedSetoid → ℝ),
      x.Positive ∧ (∀ q, 0 < lambda q) ∧
      ∀ c, v c = lambda (N.classOf c) * N.complexMonomialVector x c := by
  obtain ⟨p, hp⟩ := N.exists_speciesPotential_of_deficiencyOne_logObstruction_zero
    hδ hg hg0 hspan hvpos hobs
  let x : Concentration S := fun s => Real.exp (p s)
  have hx : x.Positive := fun s => Real.exp_pos _
  let w : N.ComplexIdx → ℝ := fun c => Real.log (v c) - N.complexMatrixᵀ.mulVecLin p c
  have hwker : w ∈ LinearMap.ker N.incidenceMatrixᵀ.mulVecLin := by
    rw [LinearMap.mem_ker]
    funext r
    rw [N.incidenceTranspose_apply, Pi.zero_apply]
    simp only [w]
    have hr := hp r
    have hcp : N.complexMatrixᵀ.mulVecLin p (N.targetIdx r) -
        N.complexMatrixᵀ.mulVecLin p (N.sourceIdx r) =
        ∑ s, N.reactionVector r s * p s := by
      rw [N.complexTranspose_apply, N.complexTranspose_apply, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro s _
      simp [Network.reactionVector_apply, Network.sourceIdx, Network.targetIdx]
      ring
    linarith [hr, hcp]
  rw [N.ker_incidenceTranspose] at hwker
  obtain ⟨ell, hell⟩ := hwker
  let lambda : Quotient N.linkedSetoid → ℝ := fun q => Real.exp (ell q)
  refine ⟨x, lambda, hx, fun q => Real.exp_pos _, ?_⟩
  intro c
  have hwc := congrFun hell c
  change N.linkageLift ell c = w c at hwc
  rw [N.linkageLift_apply] at hwc
  dsimp [w] at hwc
  have hlogPsi : Real.log (N.complexMonomialVector x c) = (N.complexMatrixᵀ.mulVec p) c := by
    change Real.log (N.complexMonomialVector x c) = N.complexMatrixᵀ.mulVecLin p c
    rw [N.log_complexMonomialVector hx c, N.complexTranspose_apply]
    apply Finset.sum_congr rfl
    intro s _
    simp [x]
  rw [← hlogPsi] at hwc
  change ell (N.classOf c) = Real.log (v c) - Real.log (N.complexMonomialVector x c) at hwc
  have hvlog : Real.exp (Real.log (v c)) = v c := Real.exp_log (hvpos c)
  rw [← hvlog]
  rw [show Real.log (v c) = ell (N.classOf c) + Real.log (N.complexMonomialVector x c) by
    change Real.log (v c) = ell (N.classOf c) + _
    rw [hlogPsi]
    linarith [hwc]]
  rw [Real.exp_add]
  change Real.exp (ell (N.classOf c)) * Real.exp (Real.log (N.complexMonomialVector x c)) = _
  have hPsiPos : 0 < N.complexMonomialVector x c := by
    simpa [N.complexMonomialVector_apply] using Complex.massActionMonomial_pos hx c.val
  rw [Real.exp_log hPsiPos]

end CRNT.Network
