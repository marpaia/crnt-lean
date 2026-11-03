import CRNT.Deficiency.ClassScaleSynchronization
import CRNT.Kinetics.Generalized
import CRNT.Deficiency.LogMonomialRatio
import CRNT.Deficiency.LogObstructionClassScaling

/-! Birch transport of linkage-class monomial scales into a prescribed stoichiometric class. -/
namespace CRNT.Network

open scoped BigOperators Classical Topology
open Matrix

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Classical Birch transport from a positive reference state to a prescribed positive
stoichiometric class.  Along this transport, the complex-monomial ratio is constant on every
linkage class. -/
theorem exists_birchTransport_with_linkageScales
    (N : Network S) {x x₀ : Concentration S} (hx : x.Positive) (hx₀ : x₀.Positive) :
    ∃ (y : Concentration S) (mu : Quotient N.linkedSetoid → ℝ),
      y ∈ N.positiveCompatibilityClass x₀ ∧ (∀ q, 0 < mu q) ∧
      ∀ c, N.complexMonomialVector y c =
        mu (N.classOf c) * N.complexMonomialVector x c := by
  obtain ⟨y, hypos, hyclass, horth⟩ :=
    gen_birch_existence N.stoichSubspace hx hx₀
  have htoric : ∀ r,
      N.logMonomialRatio y x (N.targetIdx r) =
        N.logMonomialRatio y x (N.sourceIdx r) :=
    (N.logRatio_mem_orthSum_iff hypos hx).1 (by
      simpa [Pi.sub_apply] using horth)
  let w : N.ComplexIdx → ℝ := fun c => N.logMonomialRatio y x c
  have hker : w ∈ LinearMap.ker N.incidenceMatrixᵀ.mulVecLin := by
    rw [LinearMap.mem_ker]
    funext r
    rw [N.incidenceTranspose_apply, Pi.zero_apply]
    exact sub_eq_zero.mpr (htoric r)
  rw [N.ker_incidenceTranspose] at hker
  obtain ⟨ell, hell⟩ := hker
  let mu : Quotient N.linkedSetoid → ℝ := fun q => Real.exp (ell q)
  refine ⟨y, mu, ⟨hyclass, hypos⟩, fun q => Real.exp_pos _, ?_⟩
  intro c
  have hc := congrFun hell c
  change N.linkageLift ell c = N.logMonomialRatio y x c at hc
  rw [N.linkageLift_apply] at hc
  have hpy : 0 < N.complexMonomialVector y c := by
    simpa [N.complexMonomialVector_apply] using Complex.massActionMonomial_pos hypos c.val
  have hpx : 0 < N.complexMonomialVector x c := by
    simpa [N.complexMonomialVector_apply] using Complex.massActionMonomial_pos hx c.val
  have hc' : ell (N.classOf c) = Real.log (N.complexMonomialVector y c) -
      Real.log (N.complexMonomialVector x c) := by
    simpa [classOf, logMonomialRatio, complexMonomialVector_apply] using hc
  have hlog : Real.log (N.complexMonomialVector y c) =
      ell (N.classOf c) + Real.log (N.complexMonomialVector x c) := by
    linarith [hc']
  calc
    N.complexMonomialVector y c = Real.exp (Real.log (N.complexMonomialVector y c)) :=
      (Real.exp_log hpy).symm
    _ = Real.exp (ell (N.classOf c) + Real.log (N.complexMonomialVector x c)) := by rw [hlog]
    _ = Real.exp (ell (N.classOf c)) * Real.exp (Real.log (N.complexMonomialVector x c)) :=
      Real.exp_add _ _
    _ = mu (N.classOf c) * N.complexMonomialVector x c := by
      rw [Real.exp_log hpx]

/-- If a positive kinetic preimage is class-scaled monomial at `x`, Birch transport to `x₀`
keeps it class-scaled monomial; the new scale is the old scale divided by the positive Birch
linkage scale. -/
theorem exists_classScales_after_birchTransport
    (N : Network S) {x x₀ : Concentration S} {v : N.ComplexIdx → ℝ}
    {lambda : Quotient N.linkedSetoid → ℝ}
    (hx : x.Positive) (hx₀ : x₀.Positive) (hlambda : ∀ q, 0 < lambda q)
    (hv : ∀ c, v c = lambda (N.classOf c) * N.complexMonomialVector x c) :
    ∃ (y : Concentration S) (lambda' : Quotient N.linkedSetoid → ℝ),
      y ∈ N.positiveCompatibilityClass x₀ ∧ (∀ q, 0 < lambda' q) ∧
      ∀ c, v c = lambda' (N.classOf c) * N.complexMonomialVector y c := by
  obtain ⟨y, mu, hyclass, hmupos, hmu⟩ :=
    N.exists_birchTransport_with_linkageScales hx hx₀
  let lambda' : Quotient N.linkedSetoid → ℝ := fun q => lambda q / mu q
  refine ⟨y, lambda', hyclass, ?_, ?_⟩
  · intro q
    exact div_pos (hlambda q) (hmupos q)
  · intro c
    rw [hv c, hmu c]
    dsimp [lambda']
    field_simp [(hmupos (N.classOf c)).ne']


/-- A zero deficiency logarithmic obstruction can be realized in any prescribed positive
stoichiometric class, still up to positive linkage-class scales.  Thus Birch transport removes
compatibility-class placement as a separate obstruction; only synchronization of the transported
linkage scales remains. -/
theorem exists_classScales_monomial_in_positiveClass_of_logObstruction_zero
    (N : Network S) (hδ : N.DeficiencyOne)
    {g v : N.ComplexIdx → ℝ} (hg : g ∈ N.deficiencySubspace) (hg0 : g ≠ 0)
    (hspan : ∀ w ∈ N.deficiencySubspace, ∃ a : ℝ, a • g = w)
    (hvpos : ∀ c, 0 < v c) (hobs : (∑ c, g c * Real.log (v c)) = 0)
    {x₀ : Concentration S} (hx₀ : x₀.Positive) :
    ∃ (y : Concentration S) (lambda : Quotient N.linkedSetoid → ℝ),
      y ∈ N.positiveCompatibilityClass x₀ ∧ (∀ q, 0 < lambda q) ∧
      ∀ c, v c = lambda (N.classOf c) * N.complexMonomialVector y c := by
  obtain ⟨x, lambda, hx, hlambda, hv⟩ :=
    N.exists_classScales_monomial_of_deficiencyOne_logObstruction_zero
      hδ hg hg0 hspan hvpos hobs
  exact N.exists_classScales_after_birchTransport hx hx₀ hlambda hv

/-- In a prescribed positive stoichiometric class, zero of the deficiency-one logarithmic
obstruction is *equivalent* to class-scaled monomial realizability.  Birch transport therefore
preserves not only existence but the exact scalar obstruction criterion. -/
theorem deficiencyOne_logObstruction_zero_iff_classScaledMonomial_in_positiveClass
    (N : Network S) (hδ : N.DeficiencyOne)
    {g v : N.ComplexIdx → ℝ} (hg : g ∈ N.deficiencySubspace) (hg0 : g ≠ 0)
    (hspan : ∀ w ∈ N.deficiencySubspace, ∃ a : ℝ, a • g = w)
    (hvpos : ∀ c, 0 < v c) {x₀ : Concentration S} (hx₀ : x₀.Positive) :
    (∑ c, g c * Real.log (v c)) = 0 ↔
      ∃ (x : Concentration S) (lambda : Quotient N.linkedSetoid → ℝ),
        x ∈ N.positiveCompatibilityClass x₀ ∧ (∀ q, 0 < lambda q) ∧
        ∀ c, v c = lambda (N.classOf c) * N.complexMonomialVector x c := by
  constructor
  · intro hzero
    exact N.exists_classScales_monomial_in_positiveClass_of_logObstruction_zero
      hδ hg hg0 hspan hvpos hzero hx₀
  · rintro ⟨x, lambda, hxclass, hlambda, hv⟩
    exact N.deficiencyLogObstruction_eq_zero_of_classScaledMonomial
      hg hxclass.2 hlambda hv


end CRNT.Network
