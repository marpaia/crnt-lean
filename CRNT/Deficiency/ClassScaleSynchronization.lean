import CRNT.Deficiency.PositiveKineticObstructionIVT
import CRNT.Deficiency.LinkageCouplingLine

/-!
# Class-scale synchronization in the Type-II deficiency-one reduction

A zero logarithmic obstruction realizes a positive kinetic preimage as a monomial vector only up
 to one positive scalar per linkage class.  This file isolates exactly what those scalars do to the
species-space cancellation.  It turns the remaining nonlinear problem into a one-dimensional
linkage-coupling synchronization problem.
-/

namespace CRNT.Network

open scoped BigOperators Classical

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Multiply a complex-space vector by a scalar depending only on its linkage class. -/
noncomputable def scaleByLinkage (N : Network S)
    (lambda : Quotient N.linkedSetoid → ℝ) (v : N.ComplexIdx → ℝ) :
    N.ComplexIdx → ℝ := fun c => lambda (N.classOf c) * v c

/-- Restricting a linkage-scaled vector to a class extracts the corresponding scalar. -/
theorem restrictToClass_scaleByLinkage (N : Network S)
    (lambda : Quotient N.linkedSetoid → ℝ) (v : N.ComplexIdx → ℝ)
    (q : Quotient N.linkedSetoid) :
    N.restrictToClass q (N.scaleByLinkage lambda v) =
      lambda q • N.restrictToClass q v := by
  funext c
  by_cases hc : N.classOf c = q <;> simp [restrictToClass, scaleByLinkage, hc]

/-- The kinetic map commutes with linkage-wise rescaling. -/
theorem kineticMap_scaleByLinkage (N : Network S) (κ : N.RateConstants)
    (lambda : Quotient N.linkedSetoid → ℝ) (v : N.ComplexIdx → ℝ) :
    N.kineticMap κ (N.scaleByLinkage lambda v) =
      N.scaleByLinkage lambda (N.kineticMap κ v) := by
  rw [← N.sum_restrictToClass (N.kineticMap κ (N.scaleByLinkage lambda v))]
  rw [← N.sum_restrictToClass (N.scaleByLinkage lambda (N.kineticMap κ v))]
  apply Finset.sum_congr rfl
  intro q _
  rw [← N.kineticMap_restrictToClass, N.restrictToClass_scaleByLinkage,
      map_smul, N.kineticMap_restrictToClass, N.restrictToClass_scaleByLinkage]

/-- If `v = lambda * Psi(x)` classwise, the classwise kinetic defect of `Psi(x)` is obtained by
 dividing the classwise defect of `v` by `lambda`. -/
theorem restrict_kineticMap_monomial_of_classScales
    (N : Network S) (κ : N.RateConstants)
    {v : N.ComplexIdx → ℝ} {x : Concentration S}
    {lambda : Quotient N.linkedSetoid → ℝ}
    (hlambda : ∀ q, 0 < lambda q)
    (hv : ∀ c, v c = lambda (N.classOf c) * N.complexMonomialVector x c)
    (q : Quotient N.linkedSetoid) :
    N.restrictToClass q (N.kineticMap κ (N.complexMonomialVector x)) =
      (lambda q)⁻¹ • N.restrictToClass q (N.kineticMap κ v) := by
  have hveq : v = N.scaleByLinkage lambda (N.complexMonomialVector x) := by
    funext c
    exact hv c
  have hA := N.kineticMap_scaleByLinkage κ lambda (N.complexMonomialVector x)
  rw [← hveq] at hA
  have hq := congrArg (N.restrictToClass q) hA
  rw [N.restrictToClass_scaleByLinkage] at hq
  have hne : lambda q ≠ 0 := (hlambda q).ne'
  funext c
  have hc := congrFun hq c
  simp only [Pi.smul_apply, smul_eq_mul] at hc ⊢
  field_simp [hne]
  nlinarith [hc]

/-- Species-space steady-state cancellation after a class-scaled monomial realization is exactly
 the weighted sum of the classwise species imbalances of the original kinetic preimage. -/
theorem complexMap_kineticMap_monomial_eq_weighted_class_sum
    (N : Network S) (κ : N.RateConstants)
    {v : N.ComplexIdx → ℝ} {x : Concentration S}
    {lambda : Quotient N.linkedSetoid → ℝ}
    (hlambda : ∀ q, 0 < lambda q)
    (hv : ∀ c, v c = lambda (N.classOf c) * N.complexMonomialVector x c) :
    N.complexMap (N.kineticMap κ (N.complexMonomialVector x)) =
      ∑ q, (lambda q)⁻¹ • N.complexMap (N.restrictToClass q (N.kineticMap κ v)) := by
  rw [← N.sum_restrictToClass (N.kineticMap κ (N.complexMonomialVector x)), map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [N.restrict_kineticMap_monomial_of_classScales κ hlambda hv q, map_smul]

/-- If the linkage scalars agree on every class carrying a nonzero species imbalance, then the
class-scaled monomial realization is already a mass-action steady state whenever the original
kinetic preimage has zero total species imbalance. -/
theorem isMassActionSteadyState_of_classScales_synchronized
    (N : Network S) (κ : N.RateConstants)
    {v : N.ComplexIdx → ℝ} {x : Concentration S}
    {lambda : Quotient N.linkedSetoid → ℝ}
    (hlambda : ∀ q, 0 < lambda q)
    (hv : ∀ c, v c = lambda (N.classOf c) * N.complexMonomialVector x c)
    (hzero : N.complexMap (N.kineticMap κ v) = 0)
    (hsync : ∃ L : ℝ, 0 < L ∧ ∀ q,
      N.complexMap (N.restrictToClass q (N.kineticMap κ v)) ≠ 0 → lambda q = L) :
    N.IsMassActionSteadyState κ x := by
  rcases hsync with ⟨L, hL, hsync⟩
  have hweighted :
      (∑ q, (lambda q)⁻¹ • N.complexMap (N.restrictToClass q (N.kineticMap κ v))) = 0 := by
    have hsum : (∑ q, N.complexMap (N.restrictToClass q (N.kineticMap κ v))) = 0 := by
      rw [← map_sum, N.sum_restrictToClass, hzero]
    calc
      (∑ q, (lambda q)⁻¹ • N.complexMap (N.restrictToClass q (N.kineticMap κ v))) =
          L⁻¹ • ∑ q, N.complexMap (N.restrictToClass q (N.kineticMap κ v)) := by
            rw [Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro q _
            by_cases hq : N.complexMap (N.restrictToClass q (N.kineticMap κ v)) = 0
            · simp [hq]
            · rw [hsync q hq]
      _ = 0 := by rw [hsum, smul_zero]
  have hfield := N.complexMap_kineticMap_monomial_eq_weighted_class_sum κ hlambda hv
  rw [hweighted] at hfield
  intro s
  show N.massActionVectorField κ x s = 0
  rw [N.massActionVectorField_eq κ x]
  exact congrFun hfield s



/-- For a kinetic preimage on the deficiency line, its tuple of classwise species imbalances is
exactly the same scalar multiple of the deficiency-to-coupling vector. -/
theorem classImbalance_eq_smul_deficiencyToLinkageCoupling
    (N : Network S) (κ : N.RateConstants)
    {g v : N.ComplexIdx → ℝ} (hg : g ∈ N.deficiencySubspace) {a : ℝ}
    (hAv : N.kineticMap κ v = a • g) (q : Quotient N.linkedSetoid) :
    N.complexMap (N.restrictToClass q (N.kineticMap κ v)) =
      a • ((N.deficiencyToLinkageCoupling ⟨g, hg⟩ q : N.linkageStoichSubspace q) : S → ℝ) := by
  rw [hAv, N.restrictToClass_smul, map_smul]
  rfl


/-- Away from the zero point on the deficiency line, the active linkage classes are exactly the
nonzero components of the associated linkage-coupling vector. -/
theorem classImbalance_ne_zero_iff_coupling_ne_zero
    (N : Network S) (κ : N.RateConstants)
    {g v : N.ComplexIdx → ℝ} (hg : g ∈ N.deficiencySubspace) {a : ℝ} (ha : a ≠ 0)
    (hAv : N.kineticMap κ v = a • g) (q : Quotient N.linkedSetoid) :
    N.complexMap (N.restrictToClass q (N.kineticMap κ v)) ≠ 0 ↔
      ((N.deficiencyToLinkageCoupling ⟨g, hg⟩ q : N.linkageStoichSubspace q) : S → ℝ) ≠ 0 := by
  rw [N.classImbalance_eq_smul_deficiencyToLinkageCoupling κ hg hAv q]
  exact (smul_ne_zero_iff).trans (and_iff_right ha)


/-- On a nonzero point of the deficiency line, the synchronization condition can be stated purely
on the fixed Type-II coupling vector; it no longer depends on the chosen kinetic preimage. -/
theorem classScales_synchronized_iff_coupling
    (N : Network S) (κ : N.RateConstants)
    {g v : N.ComplexIdx → ℝ} (hg : g ∈ N.deficiencySubspace) {a : ℝ} (ha : a ≠ 0)
    (hAv : N.kineticMap κ v = a • g)
    (lambda : Quotient N.linkedSetoid → ℝ) :
    (∃ L : ℝ, 0 < L ∧ ∀ q,
      N.complexMap (N.restrictToClass q (N.kineticMap κ v)) ≠ 0 → lambda q = L) ↔
    (∃ L : ℝ, 0 < L ∧ ∀ q,
      ((N.deficiencyToLinkageCoupling ⟨g, hg⟩ q : N.linkageStoichSubspace q) : S → ℝ) ≠ 0 →
        lambda q = L) := by
  constructor <;> rintro ⟨L, hL, h⟩ <;> refine ⟨L, hL, ?_⟩ <;> intro q hq
  · exact h q ((N.classImbalance_ne_zero_iff_coupling_ne_zero κ hg ha hAv q).2 hq)
  · exact h q ((N.classImbalance_ne_zero_iff_coupling_ne_zero κ hg ha hAv q).1 hq)

/-- Package the final Type-II reduction: a positive deficiency-line preimage whose logarithmic
realization has synchronized active linkage scales yields a positive steady state in the requested
stoichiometric class.  This isolates the only remaining existence input from the algebraic
steady-state verification. -/
theorem exists_positiveSteadyState_of_synchronized_classScale_realization
    (N : Network S) (κ : N.RateConstants) {x₀ : Concentration S}
    {g : N.ComplexIdx → ℝ} (hg : g ∈ N.deficiencySubspace)
    (hrealize : ∃ (a : ℝ) (v : N.ComplexIdx → ℝ) (x : Concentration S)
        (lambda : Quotient N.linkedSetoid → ℝ),
      (∀ c, 0 < v c) ∧ x ∈ N.positiveCompatibilityClass x₀ ∧
      (∀ q, 0 < lambda q) ∧
      (∀ c, v c = lambda (N.classOf c) * N.complexMonomialVector x c) ∧
      N.kineticMap κ v = a • g ∧
      ∃ L : ℝ, 0 < L ∧ ∀ q,
        N.complexMap (N.restrictToClass q (N.kineticMap κ v)) ≠ 0 → lambda q = L) :
    ∃ x : Concentration S,
      x ∈ N.positiveCompatibilityClass x₀ ∧ N.IsMassActionSteadyState κ x := by
  rcases hrealize with ⟨a, v, x, lambda, hvpos, hxclass, hlambda, hv, hAv, hsync⟩
  refine ⟨x, hxclass, ?_⟩
  apply N.isMassActionSteadyState_of_classScales_synchronized κ hlambda hv
  · rw [hAv, map_smul]
    have hgY : N.complexMap g = 0 := LinearMap.mem_ker.mp hg.1
    rw [hgY, smul_zero]
  · exact hsync

end CRNT.Network

namespace CRNT.Network

open scoped BigOperators Classical

variable {S : Type} [DecidableEq S] [Fintype S]

/-- In the Type-II one-dimensional coupling case, a class-scaled monomial realization on a
nonzero deficiency fibre is a steady state exactly when its active linkage scales synchronize.
This is the converse to `isMassActionSteadyState_of_classScales_synchronized`. -/
theorem isMassActionSteadyState_iff_classScales_synchronized_of_coupling_one
    (N : Network S) (κ : N.RateConstants)
    {g v : N.ComplexIdx → ℝ} (hg : g ∈ N.deficiencySubspace) (hg0 : g ≠ 0)
    (hclass : ∀ q, N.linkageDeficiency q = 0)
    {a : ℝ} (ha : a ≠ 0) (hAv : N.kineticMap κ v = a • g)
    (hcoupling : N.linkageCouplingDeficiency = 1)
    {x : Concentration S} {lambda : Quotient N.linkedSetoid → ℝ}
    (hlambda : ∀ q, 0 < lambda q)
    (hv : ∀ c, v c = lambda (N.classOf c) * N.complexMonomialVector x c) :
    N.IsMassActionSteadyState κ x ↔
      ∃ L : ℝ, 0 < L ∧ ∀ q,
        N.complexMap (N.restrictToClass q (N.kineticMap κ v)) ≠ 0 → lambda q = L := by
  constructor
  · intro hss
    let d : N.LinkageStoichProduct := fun q =>
      ⟨N.complexMap (N.restrictToClass q (N.kineticMap κ v)), by
        apply N.complexMap_restrictToClass_mem_linkageStoichSubspace q
        rw [hAv]
        exact (LinearMap.range N.incidenceMap).smul_mem a hg.2⟩
    let e : N.LinkageStoichProduct := fun q =>
      (lambda q)⁻¹ • d q
    have hdker : d ∈ LinearMap.ker N.linkageStoichSumMap := by
      rw [LinearMap.mem_ker]
      change (∑ q, (d q : S → ℝ)) = 0
      simp only [d]
      rw [← map_sum, N.sum_restrictToClass, hAv, map_smul]
      have hgY : N.complexMap g = 0 := LinearMap.mem_ker.mp hg.1
      rw [hgY, smul_zero]
    have heker : e ∈ LinearMap.ker N.linkageStoichSumMap := by
      rw [LinearMap.mem_ker]
      change (∑ q, (e q : S → ℝ)) = 0
      have hfield := N.complexMap_kineticMap_monomial_eq_weighted_class_sum κ hlambda hv
      have hzero : N.complexMap (N.kineticMap κ (N.complexMonomialVector x)) = 0 := by
        rw [← N.massActionVectorField_eq κ x]
        exact funext hss
      rw [hzero] at hfield
      simpa [e, d] using hfield.symm
    have hdim : Module.finrank ℝ (LinearMap.ker N.linkageStoichSumMap) = 1 := by
      rw [N.finrank_ker_linkageStoichSumMap, hcoupling]
    have hd0 : (⟨d, hdker⟩ : LinearMap.ker N.linkageStoichSumMap) ≠ 0 := by
      intro hzero
      have hdq : ∀ q, d q = 0 := by
        intro q
        have hq := congrFun (congrArg Subtype.val hzero) q
        simpa using hq
      have hcoupling0 : N.deficiencyToLinkageCoupling ⟨g, hg⟩ = 0 := by
        funext q
        have hbal := N.classImbalance_eq_smul_deficiencyToLinkageCoupling κ hg hAv q
        have hz : a • ((N.deficiencyToLinkageCoupling ⟨g, hg⟩ q :
            N.linkageStoichSubspace q) : S → ℝ) = 0 := by
          rw [← hbal]
          exact congrArg Subtype.val (hdq q)
        have hc : ((N.deficiencyToLinkageCoupling ⟨g, hg⟩ q :
            N.linkageStoichSubspace q) : S → ℝ) = 0 := (smul_eq_zero.mp hz).resolve_left ha
        exact Subtype.ext hc
      have hinj := N.deficiencyToLinkageCoupling_injective_of_all_linkageDeficiency_zero hclass
      have hcoupling0' : N.deficiencyToLinkageCoupling ⟨g, hg⟩ =
          N.deficiencyToLinkageCoupling (0 : N.deficiencySubspace) := by
        simpa using hcoupling0
      have hgsub : (⟨g, hg⟩ : N.deficiencySubspace) = 0 := hinj hcoupling0'
      exact hg0 (congrArg Subtype.val hgsub)
    obtain ⟨t, ht⟩ := exists_smul_eq_of_finrank_eq_one hdim hd0
      (⟨e, heker⟩ : LinearMap.ker N.linkageStoichSumMap)
    have htfun : t • d = e := congrArg Subtype.val ht
    have hactive : ∀ q, d q ≠ 0 → (lambda q)⁻¹ = t := by
      intro q hdq
      have hq := congrFun htfun q
      change t • d q = (lambda q)⁻¹ • d q at hq
      have hdqv : (d q : S → ℝ) ≠ 0 := by
        intro hz
        exact hdq (Subtype.ext hz)
      have hex : ∃ s : S, (d q : S → ℝ) s ≠ 0 := by
        by_contra hn
        push Not at hn
        apply hdqv
        funext s
        exact hn s
      obtain ⟨s, hs⟩ := hex
      have hqs := congrFun (congrArg Subtype.val hq) s
      change t * (d q : S → ℝ) s = (lambda q)⁻¹ * (d q : S → ℝ) s at hqs
      exact (mul_right_cancel₀ hs hqs).symm
    -- Any active class supplies positivity of `t`, and then all active scales equal `t⁻¹`.
    have hex : ∃ q, d q ≠ 0 := by
      by_contra hnone
      push_neg at hnone
      apply hd0
      apply Subtype.ext
      funext q
      exact hnone q
    obtain ⟨q0, hq0⟩ := hex
    have htpos : 0 < t := by
      rw [← hactive q0 hq0]
      exact inv_pos.mpr (hlambda q0)
    refine ⟨t⁻¹, inv_pos.mpr htpos, ?_⟩
    intro q hq
    have hdin : d q ≠ 0 := by simpa [d] using hq
    have hi := hactive q hdin
    calc
      lambda q = ((lambda q)⁻¹)⁻¹ := (inv_inv _).symm
      _ = t⁻¹ := congrArg Inv.inv hi
  · intro hsync
    apply N.isMassActionSteadyState_of_classScales_synchronized κ hlambda hv
    · rw [hAv, map_smul]
      have hgY : N.complexMap g = 0 := LinearMap.mem_ker.mp hg.1
      rw [hgY, smul_zero]
    · exact hsync



/-- A class-scaled monomial realization of an actual kinetic-kernel vector is automatically a
mass-action steady state; no synchronization hypothesis is needed on the zero deficiency fibre. -/
theorem isMassActionSteadyState_of_kernel_classScaledMonomial
    (N : Network S) (κ : N.RateConstants)
    {v : N.ComplexIdx → ℝ} (hvker : N.kineticMap κ v = 0)
    {x : Concentration S} {lambda : Quotient N.linkedSetoid → ℝ}
    (hlambda : ∀ q, 0 < lambda q)
    (hv : ∀ c, v c = lambda (N.classOf c) * N.complexMonomialVector x c) :
    N.IsMassActionSteadyState κ x := by
  apply N.isMassActionSteadyState_of_classScales_synchronized κ hlambda hv
  · simpa using congrArg N.complexMap hvker
  · refine ⟨1, zero_lt_one, ?_⟩
    intro q hq
    exfalso
    rw [hvker] at hq
    have hz : N.restrictToClass q (0 : N.ComplexIdx → ℝ) = 0 := by
      funext c
      simp [restrictToClass]
    rw [hz, map_zero] at hq
    exact hq rfl

end CRNT.Network
