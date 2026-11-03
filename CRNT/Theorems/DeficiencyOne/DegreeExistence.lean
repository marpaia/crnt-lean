import CRNT.Theorems.DeficiencyOne.MultiClass
import CRNT.Theorems.DeficiencyOne.JacobianOnStoich
import CRNT.Deficiency.WeaklyReversibleSteadyState
import CRNT.Multistationarity.SteadyStateDegree
import CRNT.Multistationarity.DegreeAdditivity
import CRNT.Dynamics.MassActionAlgebra
import CRNT.Graph.PositiveCirculation
import CRNT.Equilibria.ComplexBalanceStructure
import Mathlib.Topology.MetricSpace.Isometry
import CRNT.Multistationarity.LocalDegreeOn
import CRNT.Kinetics.CatalystFace
import CRNT.Multistationarity.ParametrizedLocalDegree
import CRNT.Dynamics.MassActionField

/-!
# Topological-degree architecture for the Deficiency One existence theorem

The weakly reversible existence half of Feinberg's Deficiency One Theorem is not a
complex-balance statement.  Its classical proof is a finite-dimensional degree argument on one
positive stoichiometric compatibility class.  This module records that argument at the natural
coordinate-free level, using the stoichiometric subspace itself as the chart.

The topological information is carried explicitly by a finite local-degree certificate: a bounded
positive domain, finite zero sets for the reference and target maps, nonzero reference local degree,
and equality of local degrees along the continuation.  Once such a certificate is constructed,
existence of a target zero follows from the elementary fact that an empty zero set has local degree
zero.  The certificate constructor below packages an independently established weakly reversible
steady state as a constant homotopy; it does not make the degree argument itself the source of the
existence result.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

private theorem localDegreeOn_ne_zero_of_single_regular_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) {U : Set E} {x : E}
    (hpre : f ⁻¹' {(0 : E)} ∩ U = {x})
    (hfin : (f ⁻¹' {(0 : E)} ∩ U).Finite)
    (hdet : LinearMap.det (fderiv ℝ f x).toLinearMap ≠ 0) :
    localDegreeOn f 0 U hfin ≠ 0 := by
  have htoFinset : hfin.toFinset = {x} := by
    ext y
    simp only [Set.Finite.mem_toFinset, Finset.mem_singleton]
    rw [hpre]
    simp
  unfold localDegreeOn
  rw [htoFinset, Finset.sum_singleton]
  rcases lt_or_gt_of_ne hdet with hdneg | hdpos
  · simpa [sign_neg hdneg] using (show (-1 : ℤ) ≠ 0 by norm_num)
  · simpa [sign_pos hdpos] using (show (1 : ℤ) ≠ 0 by norm_num)

/-- Affine chart of the stoichiometric compatibility class through `x₀`. -/
def stoichClassChart (N : Network S) (x₀ : Concentration S)
    (u : N.stoichSubspace) : Concentration S := x₀ + u.1

/-- Positive domain in stoichiometric coordinates. -/
def positiveStoichChartDomain (N : Network S) (x₀ : Concentration S) :
    Set N.stoichSubspace :=
  {u | (N.stoichClassChart x₀ u).Positive}

/-- Mass-action field as a self-map of the stoichiometric tangent space. -/
noncomputable def reducedMassActionField (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) : N.stoichSubspace → N.stoichSubspace :=
  fun u => ⟨N.massActionVectorField κ (N.stoichClassChart x₀ u),
    N.massActionVectorField_mem_stoichSubspace κ _⟩

/-- A zero of the reduced field is exactly a steady state in the affine compatibility class. -/
theorem reducedMassActionField_eq_zero_iff
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (u : N.stoichSubspace) :
    N.reducedMassActionField κ x₀ u = 0 ↔
      N.IsMassActionSteadyState κ (N.stoichClassChart x₀ u) := by
  constructor
  · intro h s
    have hv : N.massActionVectorField κ (N.stoichClassChart x₀ u) = 0 := by
      have hh := congrArg Subtype.val h
      simpa [reducedMassActionField] using hh
    exact congrFun hv s
  · intro h
    apply Subtype.ext
    funext s
    exact h s

/-- Degree domain: a bounded open subset of the positive class chart whose boundary contains no
steady state. -/
structure DeficiencyOneDegreeDomain (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) where
  U : Set N.stoichSubspace
  isOpen : IsOpen U
  bounded : Bornology.IsBounded U
  zero_mem : (0 : N.stoichSubspace) ∈ U
  closure_positive : closure U ⊆ N.positiveStoichChartDomain x₀
  boundary_nonzero : ∀ u ∈ frontier U, N.reducedMassActionField κ x₀ u ≠ 0

/-- A reference rate vector making a prescribed positive concentration complex-balanced.
Weak reversibility supplies a strictly positive graph circulation `α`; dividing its reaction fluxes
by the source monomials at `x` makes those fluxes exactly `α`, hence kills the incidence map. -/
noncomputable def complexBalancedReferenceRates
    (N : Network S) {x : Concentration S} (hx : x.Positive)
    (α : N.R → ℝ) (hα : N.IsPositiveGraphCirculation α) : N.RateConstants where
  k r := α r / N.complexMonomialVector x (N.sourceIdx r)
  positive r := div_pos (hα.1 r) (N.complexMonomialVector_pos hx (N.sourceIdx r))

/-- The reference rates built from a positive circulation make the prescribed point
complex-balanced. -/
theorem complexBalanced_complexBalancedReferenceRates
    (N : Network S) {x : Concentration S} (hx : x.Positive)
    (α : N.R → ℝ) (hα : N.IsPositiveGraphCirculation α) :
    N.IsComplexBalanced (N.complexBalancedReferenceRates hx α hα) x := by
  rw [N.isComplexBalanced_iff_kineticMap]
  rw [N.kineticMap_eq_incidenceMap]
  have hflux : (fun r : N.R =>
      (N.complexBalancedReferenceRates hx α hα).k r *
        N.complexMonomialVector x (N.sourceIdx r)) = α := by
    funext r
    simp only [complexBalancedReferenceRates]
    exact div_mul_cancel₀ (α r)
      (N.complexMonomialVector_pos hx (N.sourceIdx r)).ne'
  rw [hflux, hα.2]

/-- Positivity is an open condition, so the positive part of the chart is open. -/
theorem isOpen_positiveStoichChartDomain (N : Network S) (x₀ : Concentration S) :
    IsOpen (N.positiveStoichChartDomain x₀) := by
  have hset : N.positiveStoichChartDomain x₀
      = ⋂ s : S, {u : N.stoichSubspace | 0 < (x₀ + u.1) s} := by
    ext u
    simp only [positiveStoichChartDomain, stoichClassChart, Set.mem_setOf_eq,
      Set.mem_iInter, Concentration.Positive]
  rw [hset]
  refine isOpen_iInter_of_finite fun s => ?_
  have hcont : Continuous fun u : N.stoichSubspace => (x₀ + u.1) s :=
    (continuous_apply s).comp (continuous_const.add continuous_subtype_val)
  exact isOpen_lt continuous_const hcont

/-- **An admissible degree domain exists as soon as the positive steady states are confined.**
If every zero of the reduced mass-action field inside the positive part of the chart lies in one
compact subset `K` of that positive part, then a `DeficiencyOneDegreeDomain` exists: thicken
`K ∪ {0}` slightly inside the positive region.  The thickening is open and bounded, contains the
origin, has closure inside the positive part, and — because every zero in the positive part is
already in `K` and hence in the open thickening — carries no zero on its frontier.

This isolates what the domain half of `exists_deficiencyOneDegreeCertificate` actually needs: not
a construction, but a confinement statement.  Steady states in a positive compatibility class must
not escape to the boundary of the orthant or to infinity. -/
theorem exists_deficiencyOneDegreeDomain_of_confinement
    (N : Network S) (κ : N.RateConstants) {x₀ : Concentration S} (hx₀ : x₀.Positive)
    {K : Set N.stoichSubspace} (hKcpt : IsCompact K)
    (hKsub : K ⊆ N.positiveStoichChartDomain x₀)
    (hconf : ∀ u ∈ N.positiveStoichChartDomain x₀,
      N.reducedMassActionField κ x₀ u = 0 → u ∈ K) :
    Nonempty (N.DeficiencyOneDegreeDomain κ x₀) := by
  classical
  have hPopen : IsOpen (N.positiveStoichChartDomain x₀) :=
    N.isOpen_positiveStoichChartDomain x₀
  have h0P : (0 : N.stoichSubspace) ∈ N.positiveStoichChartDomain x₀ := by
    intro s
    simpa [stoichClassChart] using hx₀ s
  have hK'cpt : IsCompact (insert (0 : N.stoichSubspace) K) := hKcpt.insert 0
  have hK'sub : insert (0 : N.stoichSubspace) K ⊆ N.positiveStoichChartDomain x₀ :=
    Set.insert_subset_iff.2 ⟨h0P, hKsub⟩
  obtain ⟨δ, hδ, hsub⟩ := hK'cpt.exists_cthickening_subset_open hPopen hK'sub
  have hclsub : closure (Metric.thickening δ (insert (0 : N.stoichSubspace) K))
      ⊆ N.positiveStoichChartDomain x₀ :=
    (Metric.closure_thickening_subset_cthickening δ _).trans hsub
  refine ⟨{ U := Metric.thickening δ (insert (0 : N.stoichSubspace) K)
            isOpen := Metric.isOpen_thickening
            bounded := hK'cpt.isBounded.thickening
            zero_mem := Metric.self_subset_thickening hδ _ (Set.mem_insert _ _)
            closure_positive := hclsub
            boundary_nonzero := ?_ }⟩
  intro u hu hzero
  rw [Metric.isOpen_thickening.frontier_eq] at hu
  have huP : u ∈ N.positiveStoichChartDomain x₀ := hclsub hu.1
  have huK : u ∈ K := hconf u huP hzero
  exact hu.2 (Metric.self_subset_thickening hδ _ (Set.mem_insert_of_mem _ huK))

/-- The confinement construction can also record that the compact set of zeros is inside its
open domain. -/
theorem exists_deficiencyOneDegreeDomain_of_confinement_contains
    (N : Network S) (κ : N.RateConstants) {x₀ : Concentration S} (hx₀ : x₀.Positive)
    {K : Set N.stoichSubspace} (hKcpt : IsCompact K)
    (hKsub : K ⊆ N.positiveStoichChartDomain x₀)
    (hconf : ∀ u ∈ N.positiveStoichChartDomain x₀,
      N.reducedMassActionField κ x₀ u = 0 → u ∈ K) :
    ∃ D : N.DeficiencyOneDegreeDomain κ x₀, K ⊆ D.U := by
  classical
  have hPopen : IsOpen (N.positiveStoichChartDomain x₀) :=
    N.isOpen_positiveStoichChartDomain x₀
  have h0P : (0 : N.stoichSubspace) ∈ N.positiveStoichChartDomain x₀ := by
    intro s
    simpa [stoichClassChart] using hx₀ s
  have hK'cpt : IsCompact (insert (0 : N.stoichSubspace) K) := hKcpt.insert 0
  have hK'sub : insert (0 : N.stoichSubspace) K ⊆ N.positiveStoichChartDomain x₀ :=
    Set.insert_subset_iff.2 ⟨h0P, hKsub⟩
  obtain ⟨δ, hδ, hsub⟩ := hK'cpt.exists_cthickening_subset_open hPopen hK'sub
  have hclsub : closure (Metric.thickening δ (insert (0 : N.stoichSubspace) K))
      ⊆ N.positiveStoichChartDomain x₀ :=
    (Metric.closure_thickening_subset_cthickening δ _).trans hsub
  let D : N.DeficiencyOneDegreeDomain κ x₀ := {
    U := Metric.thickening δ (insert (0 : N.stoichSubspace) K)
    isOpen := Metric.isOpen_thickening
    bounded := hK'cpt.isBounded.thickening
    zero_mem := Metric.self_subset_thickening hδ _ (Set.mem_insert _ _)
    closure_positive := hclsub
    boundary_nonzero := by
      intro u hu hzero
      rw [Metric.isOpen_thickening.frontier_eq] at hu
      have huP : u ∈ N.positiveStoichChartDomain x₀ := hclsub hu.1
      have huK : u ∈ K := hconf u huP hzero
      exact hu.2 (Metric.self_subset_thickening hδ _ (Set.mem_insert_of_mem _ huK)) }
  refine ⟨D, ?_⟩
  intro u hu
  exact Metric.self_subset_thickening hδ _ (Set.mem_insert_of_mem _ hu)

/-- **Under the deficiency-one hypotheses an admissible domain always exists.**  Uniqueness makes
the set of positive steady states in one positive compatibility class a subsingleton, hence
compact, so the confinement hypothesis of
`exists_deficiencyOneDegreeDomain_of_confinement` is free.

The consequence is worth stating explicitly, because it says where the difficulty of
`exists_deficiencyOneDegreeCertificate` is *not*: the domain costs nothing.  All the content sits
in the continuation — a `C¹` homotopy from an invertible linear map to the reduced field whose
zeros stay off the frontier of that domain for every parameter, and stay nondegenerate inside
it. -/
theorem exists_deficiencyOneDegreeDomain_containingPositiveZeros_of_deficiencyOneHypotheses
    (N : Network S) (h : N.DeficiencyOneHypotheses) (κ : N.RateConstants)
    {x₀ : Concentration S} (hx₀ : x₀.Positive) :
    ∃ D : N.DeficiencyOneDegreeDomain κ x₀,
      ∀ u ∈ N.positiveStoichChartDomain x₀,
        N.reducedMassActionField κ x₀ u = 0 → u ∈ D.U := by
  classical
  set K : Set N.stoichSubspace :=
    {u | u ∈ N.positiveStoichChartDomain x₀ ∧ N.reducedMassActionField κ x₀ u = 0} with hKdef
  have hKsub : K ⊆ N.positiveStoichChartDomain x₀ := fun u hu => hu.1
  have hKsubsingleton : K.Subsingleton := by
    intro u hu v hv
    have hupos : (N.stoichClassChart x₀ u).Positive := hu.1
    have hvpos : (N.stoichClassChart x₀ v).Positive := hv.1
    have huss : N.IsMassActionSteadyState κ (N.stoichClassChart x₀ u) :=
      (N.reducedMassActionField_eq_zero_iff κ x₀ u).1 hu.2
    have hvss : N.IsMassActionSteadyState κ (N.stoichClassChart x₀ v) :=
      (N.reducedMassActionField_eq_zero_iff κ x₀ v).1 hv.2
    have humem : N.stoichClassChart x₀ u ∈ N.positiveCompatibilityClass x₀ := by
      refine ⟨?_, hupos⟩
      change N.stoichClassChart x₀ u - x₀ ∈ N.stoichSubspace
      simp [stoichClassChart]
    have hvmem : N.stoichClassChart x₀ v ∈ N.positiveCompatibilityClass x₀ := by
      refine ⟨?_, hvpos⟩
      change N.stoichClassChart x₀ v - x₀ ∈ N.stoichSubspace
      simp [stoichClassChart]
    have heq : N.stoichClassChart x₀ u = N.stoichClassChart x₀ v :=
      N.deficiencyOneUniqueness_multiClass h κ x₀ hx₀ humem huss hvmem hvss
    apply Subtype.ext
    have hadd : x₀ + u.1 = x₀ + v.1 := heq
    exact add_left_cancel hadd
  have hKcpt : IsCompact K := hKsubsingleton.finite.isCompact
  obtain ⟨D, hKD⟩ := N.exists_deficiencyOneDegreeDomain_of_confinement_contains
    κ hx₀ hKcpt hKsub (fun u huP hzero => ⟨huP, hzero⟩)
  refine ⟨D, ?_⟩
  intro u huP hzero
  exact hKD ⟨huP, hzero⟩

/-- The weaker nonempty-domain interface. -/
theorem exists_deficiencyOneDegreeDomain_of_deficiencyOneHypotheses
    (N : Network S) (h : N.DeficiencyOneHypotheses) (κ : N.RateConstants)
    {x₀ : Concentration S} (hx₀ : x₀.Positive) :
    Nonempty (N.DeficiencyOneDegreeDomain κ x₀) := by
  obtain ⟨D, _⟩ :=
    N.exists_deficiencyOneDegreeDomain_containingPositiveZeros_of_deficiencyOneHypotheses
      h κ hx₀
  exact ⟨D⟩

/-- **Global-finiteness degree certificate (superseded).**  The original formulation of the
certificate, which asks for the zero sets of the reference map and of the reduced mass-action
field to be finite on the *whole* affine chart.

That demand is not satisfiable in general, and not because the CRNT content is hard: if some
species occurs in every source complex then the mass-action field vanishes identically on the
face of the chart where that species is zero, so the global zero set contains an affine line as
soon as the stoichiometric subspace has dimension at least two.
`CRNT.Theorems.DeficiencyOne.DegreeCertificateObstruction` proves that this rules out a
certificate outright, for every rate vector and every basepoint.

It is kept because it is strictly stronger than the corrected notion
(`DeficiencyOneDegreeCertificateGlobal.toRelative`), so results established for it remain
usable, but nothing should be *required* to produce one. -/
structure DeficiencyOneDegreeCertificateGlobal (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) where
  domain : N.DeficiencyOneDegreeDomain κ x₀
  reference : N.stoichSubspace → N.stoichSubspace
  homotopy : ℝ → N.stoichSubspace → N.stoichSubspace
  homotopy_zero : homotopy 0 = reference
  homotopy_one : homotopy 1 = N.reducedMassActionField κ x₀
  boundary_nonzero : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ∀ u ∈ frontier domain.U, homotopy t u ≠ 0
  reference_unique_zero : ∃! u ∈ domain.U, reference u = 0
  /-- Finiteness of the reference zero set on the whole chart. -/
  reference_preimage_finite : (reference ⁻¹' {(0 : N.stoichSubspace)}).Finite
  /-- Finiteness of the steady-state set on the whole chart.  This is the unsatisfiable field. -/
  target_preimage_finite :
    ((N.reducedMassActionField κ x₀) ⁻¹' {(0 : N.stoichSubspace)}).Finite
  reference_localDegree_nonzero :
    localDegree reference 0 reference_preimage_finite domain.U ≠ 0
  localDegree_homotopy_invariant :
    localDegree reference 0 reference_preimage_finite domain.U =
      localDegree (N.reducedMassActionField κ x₀) 0 target_preimage_finite domain.U

/-- **Degree certificate for the deficiency-one existence theorem.**  A homotopy/degree
certificate comparing the reduced steady-state map to a reference map of known nonzero degree.

All finiteness and degree data are relative to the admissible domain `domain.U`, which is what
a degree argument on one bounded region of a compatibility class actually needs: the zero sets
are only ever counted inside `U`, so only their intersections with `U` have to be finite.  The
topological payload is unchanged — a nonzero reference degree, and its invariance along a
continuation whose zeros never reach `frontier domain.U`. -/
structure DeficiencyOneDegreeCertificate (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) where
  domain : N.DeficiencyOneDegreeDomain κ x₀
  reference : N.stoichSubspace → N.stoichSubspace
  homotopy : ℝ → N.stoichSubspace → N.stoichSubspace
  homotopy_zero : homotopy 0 = reference
  homotopy_one : homotopy 1 = N.reducedMassActionField κ x₀
  boundary_nonzero : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ∀ u ∈ frontier domain.U, homotopy t u ≠ 0
  reference_unique_zero : ∃! u ∈ domain.U, reference u = 0
  /-- The reference zero set is finite **inside the admissible domain**. -/
  reference_preimage_finite :
    (reference ⁻¹' {(0 : N.stoichSubspace)} ∩ domain.U).Finite
  /-- The steady-state set is finite **inside the admissible domain**.  Deficiency-one
  uniqueness already gives this on a positive class: at most one positive steady state lies in
  it. -/
  target_preimage_finite :
    ((N.reducedMassActionField κ x₀) ⁻¹' {(0 : N.stoichSubspace)} ∩ domain.U).Finite
  /-- The reference map has genuinely nonzero local degree on the admissible domain. -/
  reference_localDegree_nonzero :
    localDegreeOn reference 0 domain.U reference_preimage_finite ≠ 0
  /-- The continuation preserves that local degree.  This is the actual topological payload
  that the boundary-nonvanishing homotopy must establish. -/
  localDegree_homotopy_invariant :
    localDegreeOn reference 0 domain.U reference_preimage_finite =
      localDegreeOn (N.reducedMassActionField κ x₀) 0 domain.U target_preimage_finite

/-- A global-finiteness certificate yields a domain-relative one: the correction only ever
weakens what has to be supplied. -/
def DeficiencyOneDegreeCertificateGlobal.toRelative {N : Network S} {κ : N.RateConstants}
    {x₀ : Concentration S} (C : N.DeficiencyOneDegreeCertificateGlobal κ x₀) :
    N.DeficiencyOneDegreeCertificate κ x₀ where
  domain := C.domain
  reference := C.reference
  homotopy := C.homotopy
  homotopy_zero := C.homotopy_zero
  homotopy_one := C.homotopy_one
  boundary_nonzero := C.boundary_nonzero
  reference_unique_zero := C.reference_unique_zero
  reference_preimage_finite := C.reference_preimage_finite.subset Set.inter_subset_left
  target_preimage_finite := C.target_preimage_finite.subset Set.inter_subset_left
  reference_localDegree_nonzero := by
    rw [localDegreeOn_eq_localDegree C.reference 0 C.domain.U C.reference_preimage_finite]
    exact C.reference_localDegree_nonzero
  localDegree_homotopy_invariant := by
    rw [localDegreeOn_eq_localDegree C.reference 0 C.domain.U C.reference_preimage_finite,
      localDegreeOn_eq_localDegree (N.reducedMassActionField κ x₀) 0 C.domain.U
        C.target_preimage_finite]
    exact C.localDegree_homotopy_invariant

/-- Finite-dimensional degree principle used by the deficiency-one proof.  Homotopy invariance
transfers the nonzero reference degree to the mass-action field, and a nonzero degree on `U`
forces a zero in `U`. -/
theorem exists_zero_of_deficiencyOneDegreeCertificate
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (C : N.DeficiencyOneDegreeCertificate κ x₀) :
    ∃ u ∈ C.domain.U, N.reducedMassActionField κ x₀ u = 0 := by
  have hdeg :
      localDegreeOn (N.reducedMassActionField κ x₀) 0 C.domain.U C.target_preimage_finite ≠ 0 := by
    rw [← C.localDegree_homotopy_invariant]
    exact C.reference_localDegree_nonzero
  exact exists_mem_of_localDegreeOn_ne_zero (N.reducedMassActionField κ x₀) 0
    C.target_preimage_finite hdeg

/-- **Certificate from geometric data alone.**  Given an admissible domain, a reference map, and
a continuation of the reference map into the reduced mass-action field such that

* no zero of any slice sits on `frontier domain.U`,
* every zero of every slice inside `domain.U` is nondegenerate, and there are finitely many,
* the reference map has a unique zero in `domain.U` and nonzero relative degree there,

the degree certificate exists.  The topological payload — invariance of the relative degree
along the continuation — is discharged by
`CRNT.Multistationarity.ParametrizedLocalDegree.localDegreeOn_homotopy_invariant`, so no degree
theory has to be supplied by the caller.

This reduces `exists_deficiencyOneDegreeCertificate` to the CRNT geometry of one positive
compatibility class: exhibit the domain and the continuation with the sign conditions.  The
nondegeneracy hypothesis at the mass-action end is itself available under the deficiency-one
hypotheses, from `deficiencyOne_jacobianOnStoich_det_ne_zero`. -/
noncomputable def deficiencyOneDegreeCertificate_ofHomotopy
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (domain : N.DeficiencyOneDegreeDomain κ x₀)
    (reference : N.stoichSubspace → N.stoichSubspace)
    (homotopy : ℝ → N.stoichSubspace → N.stoichSubspace)
    (hcd : ContDiff ℝ 1 (fun p : ℝ × N.stoichSubspace => homotopy p.1 p.2))
    (hzero : homotopy 0 = reference)
    (hone : homotopy 1 = N.reducedMassActionField κ x₀)
    (hbd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ frontier domain.U, homotopy t u ≠ 0)
    (hreg : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ domain.U, homotopy t u = 0 →
      LinearMap.det (partialFDeriv
        (fun p : ℝ × N.stoichSubspace => homotopy p.1 p.2) (t, u)).toLinearMap ≠ 0)
    (hfin : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ((homotopy t) ⁻¹' {(0 : N.stoichSubspace)} ∩ domain.U).Finite)
    (huniq : ∃! u ∈ domain.U, reference u = 0)
    (hrefdeg : ∀ hfr : (reference ⁻¹' {(0 : N.stoichSubspace)} ∩ domain.U).Finite,
      localDegreeOn reference 0 domain.U hfr ≠ 0) :
    N.DeficiencyOneDegreeCertificate κ x₀ := by
  classical
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have hcpt : IsCompact (closure domain.U) := domain.bounded.isCompact_closure
  have hbdcl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ closure domain.U,
      homotopy t u = 0 → u ∈ domain.U := by
    intro t ht u hu hz
    by_contra hnot
    refine hbd t ht u ?_ hz
    rw [domain.isOpen.frontier_eq]
    exact ⟨hu, hnot⟩
  have rpf : (reference ⁻¹' {(0 : N.stoichSubspace)} ∩ domain.U).Finite := hzero ▸ hfin 0 h0
  have tpf : ((N.reducedMassActionField κ x₀) ⁻¹' {(0 : N.stoichSubspace)} ∩ domain.U).Finite :=
    hone ▸ hfin 1 h1
  have hinv := localDegreeOn_homotopy_invariant
    (fun p : ℝ × N.stoichSubspace => homotopy p.1 p.2) hcd domain.isOpen hcpt
    hbdcl hreg hfin h0 h1
  refine
    { domain := domain
      reference := reference
      homotopy := homotopy
      homotopy_zero := hzero
      homotopy_one := hone
      boundary_nonzero := hbd
      reference_unique_zero := huniq
      reference_preimage_finite := rpf
      target_preimage_finite := tpf
      reference_localDegree_nonzero := hrefdeg rpf
      localDegree_homotopy_invariant := ?_ }
  calc localDegreeOn reference 0 domain.U rpf
      = localDegreeOn (homotopy 0) 0 domain.U (hfin 0 h0) :=
        localDegreeOn_congr_fun hzero.symm 0 domain.U rpf (hfin 0 h0)
    _ = localDegreeOn (homotopy 1) 0 domain.U (hfin 1 h1) := hinv
    _ = localDegreeOn (N.reducedMassActionField κ x₀) 0 domain.U tpf :=
        localDegreeOn_congr_fun hone 0 domain.U (hfin 1 h1) tpf

/-- **Certificate from a linear reference map.**  Specializes
`deficiencyOneDegreeCertificate_ofHomotopy` to the case where the reference map is an invertible
continuous linear map, which is the natural choice: the admissible domain contains the origin by
definition, so an invertible linear map has the origin as its unique zero there, with relative
degree the sign of its determinant.

What is left for the caller is exactly the CRNT geometry: an admissible domain, and a `C¹`
continuation from a linear map to the reduced mass-action field whose zeros stay off
`frontier domain.U` and stay nondegenerate inside it. -/
noncomputable def deficiencyOneDegreeCertificate_ofLinearHomotopy
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (domain : N.DeficiencyOneDegreeDomain κ x₀)
    (T : N.stoichSubspace →L[ℝ] N.stoichSubspace)
    (hdet : LinearMap.det T.toLinearMap ≠ 0)
    (homotopy : ℝ → N.stoichSubspace → N.stoichSubspace)
    (hcd : ContDiff ℝ 1 (fun p : ℝ × N.stoichSubspace => homotopy p.1 p.2))
    (hzero : homotopy 0 = (T : N.stoichSubspace → N.stoichSubspace))
    (hone : homotopy 1 = N.reducedMassActionField κ x₀)
    (hbd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ frontier domain.U, homotopy t u ≠ 0)
    (hreg : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ domain.U, homotopy t u = 0 →
      LinearMap.det (partialFDeriv
        (fun p : ℝ × N.stoichSubspace => homotopy p.1 p.2) (t, u)).toLinearMap ≠ 0)
    (hfin : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ((homotopy t) ⁻¹' {(0 : N.stoichSubspace)} ∩ domain.U).Finite) :
    N.DeficiencyOneDegreeCertificate κ x₀ :=
  N.deficiencyOneDegreeCertificate_ofHomotopy κ x₀ domain
    (T : N.stoichSubspace → N.stoichSubspace) homotopy hcd hzero hone hbd hreg hfin
    (existsUnique_zero_of_det_ne_zero T hdet domain.zero_mem)
    (fun hfr => localDegreeOn_continuousLinearMap_ne_zero T hdet domain.zero_mem hfr)

/-- Every weakly reversible network admits a positive reference rate vector for which any
prescribed positive concentration is complex-balanced.  This supplies the canonical `t = 0`
endpoint for the deficiency-one continuation to arbitrary target rates. -/
theorem exists_referenceRateConstants_complexBalanced
    (N : Network S) (hwr : N.WeaklyReversible)
    {x : Concentration S} (hx : x.Positive) :
    ∃ κ₀ : N.RateConstants, N.IsComplexBalanced κ₀ x := by
  obtain ⟨α, hα⟩ := N.exists_positiveGraphCirculation_of_weaklyReversible hwr
  exact ⟨N.complexBalancedReferenceRates hx α hα,
    N.complexBalanced_complexBalancedReferenceRates hx α hα⟩

/-- A complex-balanced point is the zero of the reduced steady-state field at the origin
of its own stoichiometric chart.  Together with `exists_referenceRateConstants_complexBalanced`,
this gives the continuation a concrete known zero at its reference endpoint. -/
theorem reducedMassActionField_zero_of_complexBalanced
    (N : Network S) (κ : N.RateConstants) {x : Concentration S}
    (hcb : N.IsComplexBalanced κ x) :
    N.reducedMassActionField κ x 0 = 0 := by
  rw [N.reducedMassActionField_eq_zero_iff]
  simpa [stoichClassChart] using hcb.isMassActionSteadyState

/-- Convex interpolation from a reference rate vector to the target rate vector.  The
parameter is bundled in `[0,1]`, so positivity of every intermediate rate is part of the
definition rather than an extra continuation hypothesis. -/
noncomputable def rateConstantsSegment (N : Network S)
    (κ₀ κ : N.RateConstants) (t : Set.Icc (0 : ℝ) 1) : N.RateConstants where
  k r := (1 - t.1) * κ₀.k r + t.1 * κ.k r
  positive r := by
    have ht0 : 0 ≤ t.1 := t.2.1
    have ht1 : t.1 ≤ 1 := t.2.2
    by_cases hz : t.1 = 0
    · simp [hz, κ₀.positive r]
    · have htp : 0 < t.1 := lt_of_le_of_ne ht0 (Ne.symm hz)
      exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr ht1) (κ₀.positive r).le)
        (mul_pos htp (κ.positive r))

@[simp] theorem rateConstantsSegment_zero_k (N : Network S)
    (κ₀ κ : N.RateConstants) :
    (N.rateConstantsSegment κ₀ κ ⟨0, by norm_num⟩).k = κ₀.k := by
  funext r
  simp [rateConstantsSegment]

@[simp] theorem rateConstantsSegment_one_k (N : Network S)
    (κ₀ κ : N.RateConstants) :
    (N.rateConstantsSegment κ₀ κ ⟨1, by norm_num⟩).k = κ.k := by
  funext r
  simp [rateConstantsSegment]

/-- Linear homotopy of the reduced steady-state fields from reference rates to target
rates.  Mass-action kinetics is affine-linear in the rate vector, so this is the natural
continuation map; its endpoints are definitionally the two reduced fields. -/
noncomputable def reducedMassActionLinearHomotopy (N : Network S)
    (κ₀ κ : N.RateConstants) (x₀ : Concentration S) :
    ℝ → N.stoichSubspace → N.stoichSubspace :=
  fun t u => (1 - t) • N.reducedMassActionField κ₀ x₀ u +
    t • N.reducedMassActionField κ x₀ u

@[simp] theorem reducedMassActionLinearHomotopy_zero (N : Network S)
    (κ₀ κ : N.RateConstants) (x₀ : Concentration S) :
    N.reducedMassActionLinearHomotopy κ₀ κ x₀ 0 =
      N.reducedMassActionField κ₀ x₀ := by
  funext u
  simp [reducedMassActionLinearHomotopy]

@[simp] theorem reducedMassActionLinearHomotopy_one (N : Network S)
    (κ₀ κ : N.RateConstants) (x₀ : Concentration S) :
    N.reducedMassActionLinearHomotopy κ₀ κ x₀ 1 =
      N.reducedMassActionField κ x₀ := by
  funext u
  simp [reducedMassActionLinearHomotopy]

/-- On the admissible parameter interval, the linear field homotopy is exactly the
reduced mass-action field for the convexly interpolated positive rate constants.  This exposes
all intermediate zeros to the ordinary CRNT Jacobian/nondegeneracy API. -/
theorem reducedMassActionLinearHomotopy_eq_segment (N : Network S)
    (κ₀ κ : N.RateConstants) (x₀ : Concentration S)
    (t : Set.Icc (0 : ℝ) 1) (u : N.stoichSubspace) :
    N.reducedMassActionLinearHomotopy κ₀ κ x₀ t.1 u =
      N.reducedMassActionField (N.rateConstantsSegment κ₀ κ t) x₀ u := by
  apply Subtype.ext
  funext s
  simp only [reducedMassActionLinearHomotopy, Submodule.coe_add, Pi.add_apply,
    Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul, reducedMassActionField,
    massActionVectorField_apply, massActionRate, rateConstantsSegment]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  ring

/-- Zeros of the continuation are exactly mass-action steady states for the positive
intermediate rate vector in the fixed affine stoichiometric class. -/
theorem reducedMassActionLinearHomotopy_eq_zero_iff (N : Network S)
    (κ₀ κ : N.RateConstants) (x₀ : Concentration S)
    (t : Set.Icc (0 : ℝ) 1) (u : N.stoichSubspace) :
    N.reducedMassActionLinearHomotopy κ₀ κ x₀ t.1 u = 0 ↔
      N.IsMassActionSteadyState (N.rateConstantsSegment κ₀ κ t)
        (N.stoichClassChart x₀ u) := by
  rw [N.reducedMassActionLinearHomotopy_eq_segment]
  exact N.reducedMassActionField_eq_zero_iff _ _ _

/-- At each continuation parameter there is at most one zero inside the positive
stoichiometric chart.  This is the already-proved deficiency-one uniqueness theorem applied to
the positive interpolated rate vector. -/
theorem reducedMassActionLinearHomotopy_zero_unique_positive
    (N : Network S) (h : N.DeficiencyOneHypotheses)
    (κ₀ κ : N.RateConstants) {x₀ : Concentration S} (hx₀ : x₀.Positive)
    (t : Set.Icc (0 : ℝ) 1) {u v : N.stoichSubspace}
    (hu : N.reducedMassActionLinearHomotopy κ₀ κ x₀ t.1 u = 0)
    (hv : N.reducedMassActionLinearHomotopy κ₀ κ x₀ t.1 v = 0)
    (hupos : (N.stoichClassChart x₀ u).Positive)
    (hvpos : (N.stoichClassChart x₀ v).Positive) : u = v := by
  let κt := N.rateConstantsSegment κ₀ κ t
  have hsu : N.IsMassActionSteadyState κt (N.stoichClassChart x₀ u) :=
    (N.reducedMassActionLinearHomotopy_eq_zero_iff κ₀ κ x₀ t u).mp hu
  have hsv : N.IsMassActionSteadyState κt (N.stoichClassChart x₀ v) :=
    (N.reducedMassActionLinearHomotopy_eq_zero_iff κ₀ κ x₀ t v).mp hv
  have hcu : N.stoichClassChart x₀ u ∈ N.positiveCompatibilityClass x₀ := by
    refine ⟨?_, hupos⟩
    change N.stoichClassChart x₀ u - x₀ ∈ N.stoichSubspace
    simpa [stoichClassChart] using u.2
  have hcv : N.stoichClassChart x₀ v ∈ N.positiveCompatibilityClass x₀ := by
    refine ⟨?_, hvpos⟩
    change N.stoichClassChart x₀ v - x₀ ∈ N.stoichSubspace
    simpa [stoichClassChart] using v.2
  have huv := N.deficiencyOneUniqueness_multiClass h κt x₀ hx₀ hcu hsu hcv hsv
  apply Subtype.ext
  have hd := congrArg (fun z : Concentration S => z - x₀) huv
  simpa [stoichClassChart] using hd

/-- Consequently, the zero set of every intermediate field is finite after restriction
to any positive chart region.  The proof is stronger: the restricted zero set is a subsingleton.
This is the finiteness actually needed by a local-degree construction. -/
theorem reducedMassActionLinearHomotopy_zeroSet_inter_finite
    (N : Network S) (h : N.DeficiencyOneHypotheses)
    (κ₀ κ : N.RateConstants) {x₀ : Concentration S} (hx₀ : x₀.Positive)
    (t : Set.Icc (0 : ℝ) 1) {U : Set N.stoichSubspace}
    (hUpos : U ⊆ N.positiveStoichChartDomain x₀) :
    ((N.reducedMassActionLinearHomotopy κ₀ κ x₀ t.1) ⁻¹' {0} ∩ U).Finite := by
  apply Set.Subsingleton.finite
  intro u hu v hv
  apply N.reducedMassActionLinearHomotopy_zero_unique_positive h κ₀ κ hx₀ t hu.1 hv.1
  · exact hUpos hu.2
  · exact hUpos hv.2

/-- For a complex-balanced reference endpoint, the chart origin is the unique zero on
any region lying in the positive stoichiometric chart.  This discharges the
`reference_unique_zero` part of the degree certificate once an admissible domain is chosen. -/
theorem reducedMassActionField_reference_unique_zero_on_positive_domain
    (N : Network S) (h : N.DeficiencyOneHypotheses)
    (κ₀ : N.RateConstants) {x₀ : Concentration S} (hx₀ : x₀.Positive)
    (hcb : N.IsComplexBalanced κ₀ x₀)
    {U : Set N.stoichSubspace} (h0 : (0 : N.stoichSubspace) ∈ U)
    (hUpos : U ⊆ N.positiveStoichChartDomain x₀) :
    ∃! u : N.stoichSubspace,
      u ∈ U ∧ N.reducedMassActionField κ₀ x₀ u = 0 := by
  refine ⟨0, ⟨h0, N.reducedMassActionField_zero_of_complexBalanced κ₀ hcb⟩, ?_⟩
  intro u hu
  have hupos : (N.stoichClassChart x₀ u).Positive := hUpos hu.1
  have huss : N.IsMassActionSteadyState κ₀ (N.stoichClassChart x₀ u) :=
    (N.reducedMassActionField_eq_zero_iff κ₀ x₀ u).mp hu.2
  have huc : N.stoichClassChart x₀ u ∈ N.positiveCompatibilityClass x₀ := by
    refine ⟨?_, hupos⟩
    change N.stoichClassChart x₀ u - x₀ ∈ N.stoichSubspace
    simpa [stoichClassChart] using u.2
  have h0c : x₀ ∈ N.positiveCompatibilityClass x₀ := by
    refine ⟨?_, hx₀⟩
    simp [Network.StoichCompatible]
  have heq := N.deficiencyOneUniqueness_multiClass h κ₀ x₀ hx₀
    huc huss h0c hcb.isMassActionSteadyState
  apply Subtype.ext
  have hd := congrArg (fun z : Concentration S => z - x₀) heq
  simpa [stoichClassChart] using hd

private noncomputable def degreeStoichSubspaceCoordEquiv (N : Network S) :
    (Fin N.stoichRank → ℝ) ≃L[ℝ] N.stoichSubspace :=
  N.stoichBasis.equivFun.symm.toContinuousLinearEquiv

@[simp] private theorem degreeStoichSubspaceCoordEquiv_coe (N : Network S)
    (y : Fin N.stoichRank → ℝ) :
    ((N.degreeStoichSubspaceCoordEquiv y : N.stoichSubspace) : Concentration S) =
      N.stoichChart y := by
  simp [degreeStoichSubspaceCoordEquiv, stoichChart, stoichChartLM]

private theorem reducedMassActionField_contDiff_degree (N : Network S)
    (κ : N.RateConstants) (x₀ : Concentration S) {n : WithTop ℕ∞} :
    ContDiff ℝ n (N.reducedMassActionField κ x₀) := by
  let e := N.degreeStoichSubspaceCoordEquiv
  have he : ContDiff ℝ n (e : (Fin N.stoichRank → ℝ) → N.stoichSubspace) := e.contDiff
  have hes : ContDiff ℝ n (e.symm : N.stoichSubspace → (Fin N.stoichRank → ℝ)) :=
    e.symm.contDiff
  have hred : ContDiff ℝ n (N.reducedField κ x₀) := by
    have hchart : ContDiff ℝ n (N.affineChart x₀) :=
      contDiff_const.add N.stoichChart.contDiff
    have hf : ContDiff ℝ n (fun y => N.massActionVectorField κ (N.affineChart x₀ y)) := by
      simpa only [Function.comp_def] using (N.massActionVectorField_contDiff κ).comp hchart
    change ContDiff ℝ n
      (fun y => N.stoichProj (N.massActionVectorField κ (N.affineChart x₀ y)))
    simpa only [Function.comp_def] using N.stoichProj.contDiff.comp hf
  have hmid : ContDiff ℝ n (fun u : N.stoichSubspace =>
      N.reducedField κ x₀ (e.symm u)) := by
    simpa only [Function.comp_def] using hred.comp hes
  have h : ContDiff ℝ n (fun u : N.stoichSubspace =>
      e (N.reducedField κ x₀ (e.symm u))) := by
    simpa only [Function.comp_def] using he.comp hmid
  have heq : (fun u : N.stoichSubspace =>
      e (N.reducedField κ x₀ (e.symm u))) = N.reducedMassActionField κ x₀ := by
    funext u
    apply Subtype.ext
    change N.stoichChart (N.reducedField κ x₀ (e.symm u)) =
      N.massActionVectorField κ (N.stoichClassChart x₀ u)
    rw [reducedField]
    rw [N.stoichChart_stoichProj (N.massActionVectorField_mem_stoichSubspace κ _)]
    congr 2
    simp only [affineChart, stoichClassChart]
    congr 1
    rw [← N.degreeStoichSubspaceCoordEquiv_coe (e.symm u)]
    simp [e]
  rw [← heq]
  exact h

private theorem reducedMassActionField_fderiv_det_ne_zero
    (N : Network S) (h : N.DeficiencyOneHypotheses) (κ : N.RateConstants)
    {x₀ : Concentration S} (u : N.stoichSubspace)
    (hx : (N.stoichClassChart x₀ u).Positive)
    (hss : N.IsMassActionSteadyState κ (N.stoichClassChart x₀ u)) :
    LinearMap.det
      (fderiv ℝ (N.reducedMassActionField κ x₀) u).toLinearMap ≠ 0 := by
  let j := N.stoichSubspace.subtypeL
  let f := N.reducedMassActionField κ x₀
  have hfdiff : Differentiable ℝ f :=
    (N.reducedMassActionField_contDiff_degree κ x₀ (n := 1)).differentiable (by norm_num)
  have hchart : HasFDerivAt (N.stoichClassChart x₀) j u := by
    change HasFDerivAt (fun v : N.stoichSubspace => x₀ + (v : Concentration S)) j u
    simpa [j, stoichClassChart] using (j.hasFDerivAt).const_add x₀
  have hsub : HasFDerivAt (fun v : N.stoichSubspace => j (f v))
      (j.comp (fderiv ℝ f u)) u := by
    exact j.hasFDerivAt.comp u (hfdiff u).hasFDerivAt
  have hambient : HasFDerivAt
      (fun v : N.stoichSubspace => N.massActionVectorField κ (N.stoichClassChart x₀ v))
      ((N.massActionJacobianCLM κ (N.stoichClassChart x₀ u)).comp j) u :=
    (N.massActionVectorField_hasFDerivAt κ _).comp u hchart
  have hfunctions : (fun v : N.stoichSubspace => j (f v)) =
      (fun v => N.massActionVectorField κ (N.stoichClassChart x₀ v)) := by
    funext v
    rfl
  have hderiv : j.comp (fderiv ℝ f u) =
      (N.massActionJacobianCLM κ (N.stoichClassChart x₀ u)).comp j := by
    have hsub' : HasFDerivAt
        (fun v : N.stoichSubspace => N.massActionVectorField κ
          (N.stoichClassChart x₀ v)) (j.comp (fderiv ℝ f u)) u := by
      simpa only [hfunctions] using hsub
    exact hsub'.unique hambient
  have hinj : Function.Injective (fderiv ℝ f u).toLinearMap := by
    rw [← LinearMap.ker_eq_bot]
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    apply Subtype.ext
    have heq := congrArg (fun T : N.stoichSubspace →L[ℝ] Concentration S => T v) hderiv
    have hvval : j ((fderiv ℝ f u) v) = 0 := by
      simpa [j] using congrArg Subtype.val hv
    have hJ : N.massActionJacobianCLM κ (N.stoichClassChart x₀ u) v.1 = 0 := by
      calc
        N.massActionJacobianCLM κ (N.stoichClassChart x₀ u) v.1 =
            j ((fderiv ℝ f u) v) := heq.symm
        _ = 0 := hvval
    exact N.massActionJacobianCLM_eq_zero_of_mem_stoich_of_deficiencyOne
      h κ hx hss v.2 hJ
  have hsurj : Function.Surjective (fderiv ℝ f u).toLinearMap :=
    LinearMap.injective_iff_surjective.mp hinj
  let e : N.stoichSubspace ≃ₗ[ℝ] N.stoichSubspace :=
    LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩
  have hunit := e.isUnit_det'
  have hcoe : (e : N.stoichSubspace →ₗ[ℝ] N.stoichSubspace) =
      (fderiv ℝ f u).toLinearMap := rfl
  rw [hcoe] at hunit
  exact hunit.ne_zero

/-- **CRNT degree certificate construction.** Weak reversibility and the three Deficiency One
structural hypotheses provide an admissible domain around the independently established positive
steady state.  We use the target field as both endpoints of a constant homotopy; uniqueness and
Jacobian nondegeneracy make its relative local degree nonzero.  Thus this theorem packages a valid
certificate, while the separate weakly reversible existence theorem supplies the steady state. -/
theorem exists_deficiencyOneDegreeCertificate
    (N : Network S) (h : N.DeficiencyOneHypotheses) (hwr : N.WeaklyReversible)
    (κ : N.RateConstants) {x₀ : Concentration S} (hx₀ : x₀.Positive) :
    Nonempty (N.DeficiencyOneDegreeCertificate κ x₀) := by
  classical
  obtain ⟨x, hxc, hss⟩ := N.exists_positiveSteadyState_of_weaklyReversible hwr κ hx₀
  let u : N.stoichSubspace := ⟨x - x₀, hxc.1⟩
  have huChart : N.stoichClassChart x₀ u = x := by
    simp [u, stoichClassChart]
  have huPos : u ∈ N.positiveStoichChartDomain x₀ := by
    change (N.stoichClassChart x₀ u).Positive
    simpa [huChart] using hxc.2
  have huZero : N.reducedMassActionField κ x₀ u = 0 := by
    rw [N.reducedMassActionField_eq_zero_iff]
    simpa [huChart] using hss
  obtain ⟨D, hcontains⟩ :=
    N.exists_deficiencyOneDegreeDomain_containingPositiveZeros_of_deficiencyOneHypotheses
      h κ hx₀
  have huD : u ∈ D.U := hcontains u huPos huZero
  have hussChart : N.IsMassActionSteadyState κ (N.stoichClassChart x₀ u) := by
    simpa [huChart] using hss
  let f := N.reducedMassActionField κ x₀
  let H : ℝ → N.stoichSubspace → N.stoichSubspace := fun _ => f
  have hcd : ContDiff ℝ 1 (fun p : ℝ × N.stoichSubspace => H p.1 p.2) := by
    dsimp [H, f]
    exact (N.reducedMassActionField_contDiff_degree κ x₀ (n := 1)).comp contDiff_snd
  have huniqProp : ∀ v : N.stoichSubspace, v ∈ D.U ∧ f v = 0 → v = u := by
    intro v hv
    have hvPos : (N.stoichClassChart x₀ v).Positive :=
      D.closure_positive (subset_closure hv.1)
    have huZero' : N.reducedMassActionLinearHomotopy κ κ x₀ 0 u = 0 := by
      simpa [reducedMassActionLinearHomotopy] using huZero
    have hvZero' : N.reducedMassActionLinearHomotopy κ κ x₀ 0 v = 0 := by
      simpa [f, reducedMassActionLinearHomotopy] using hv.2
    exact (N.reducedMassActionLinearHomotopy_zero_unique_positive h κ κ hx₀
      ⟨0, by norm_num⟩ (u := u) (v := v) huZero' hvZero'
      (by simpa [huChart] using hxc.2) hvPos).symm
  have huniq : ∃! v : N.stoichSubspace, v ∈ D.U ∧ f v = 0 :=
    ⟨u, ⟨huD, huZero⟩, huniqProp⟩
  have hpre : f ⁻¹' {(0 : N.stoichSubspace)} ∩ D.U = {u} := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hvZero, hvU⟩
      exact huniqProp v ⟨hvU, hvZero⟩
    · intro hvu
      subst v
      exact ⟨huZero, huD⟩
  have htargetfin : (f ⁻¹' {(0 : N.stoichSubspace)} ∩ D.U).Finite := by
    rw [hpre]
    exact Set.finite_singleton u
  have hboundary : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ frontier D.U, H t v ≠ 0 := by
    intro t ht v hv
    simpa [H, f] using D.boundary_nonzero v hv
  have hregular : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ D.U, H t v = 0 →
      LinearMap.det (partialFDeriv
        (fun p : ℝ × N.stoichSubspace => H p.1 p.2) (t, v)).toLinearMap ≠ 0 := by
    intro t ht v hvU hvZero
    have hvPos : (N.stoichClassChart x₀ v).Positive :=
      D.closure_positive (subset_closure hvU)
    have hvFieldZero : N.reducedMassActionField κ x₀ v = 0 := by
      simpa [H, f] using hvZero
    have hvss : N.IsMassActionSteadyState κ (N.stoichClassChart x₀ v) :=
      (N.reducedMassActionField_eq_zero_iff κ x₀ v).mp hvFieldZero
    have hdet := N.reducedMassActionField_fderiv_det_ne_zero h κ v hvPos hvss
    have hHdiff : DifferentiableAt ℝ
        (fun p : ℝ × N.stoichSubspace => H p.1 p.2) (t, v) :=
      (hcd.differentiable (by norm_num)) (t, v)
    have hpartial : fderiv ℝ f v =
        partialFDeriv (fun p : ℝ × N.stoichSubspace => H p.1 p.2) (t, v) := by
      simpa [H, f] using
        (partialFDeriv_eq (fun p : ℝ × N.stoichSubspace => H p.1 p.2) hHdiff)
    rw [← hpartial]
    exact hdet
  have hfinite : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ((H t) ⁻¹' {(0 : N.stoichSubspace)} ∩ D.U).Finite := by
    intro t ht
    simpa [H, f] using htargetfin
  have huDet := N.reducedMassActionField_fderiv_det_ne_zero h κ u
    (by simpa [huChart] using hxc.2) hussChart
  have hrefdeg : ∀ hfr : (f ⁻¹' {(0 : N.stoichSubspace)} ∩ D.U).Finite,
      localDegreeOn f 0 D.U hfr ≠ 0 := by
    intro hfr
    exact localDegreeOn_ne_zero_of_single_regular_zero f hpre hfr huDet
  exact ⟨N.deficiencyOneDegreeCertificate_ofHomotopy κ x₀ D f H hcd rfl rfl
    hboundary hregular hfinite huniq hrefdeg⟩

/-- **Weakly reversible Deficiency One existence, degree proof.** -/
theorem deficiencyOne_exists_positiveSteadyState_via_degree
    (N : Network S) (h : N.DeficiencyOneHypotheses) (hwr : N.WeaklyReversible)
    (κ : N.RateConstants) {x₀ : Concentration S} (hx₀ : x₀.Positive) :
    ∃ x : Concentration S,
      x ∈ N.positiveCompatibilityClass x₀ ∧ N.IsMassActionSteadyState κ x := by
  obtain ⟨C⟩ := N.exists_deficiencyOneDegreeCertificate h hwr κ hx₀
  obtain ⟨u, huU, hzero⟩ := N.exists_zero_of_deficiencyOneDegreeCertificate κ x₀ C
  refine ⟨N.stoichClassChart x₀ u, ?_, (N.reducedMassActionField_eq_zero_iff κ x₀ u).1 hzero⟩
  constructor
  · change N.stoichClassChart x₀ u - x₀ ∈ N.stoichSubspace
    simp [stoichClassChart]
  · exact C.domain.closure_positive (subset_closure huU)

/-- Combining the degree existence theorem with deficiency-one uniqueness gives exactly one
positive steady state in every positive class. -/
theorem deficiencyOne_existence_via_degree
    (N : Network S) (h : N.DeficiencyOneHypotheses) (hwr : N.WeaklyReversible) :
    N.DeficiencyOneExistence := by
  intro κ x₀ hx₀
  obtain ⟨x, hxmem, hxss⟩ :=
    N.deficiencyOne_exists_positiveSteadyState_via_degree h hwr κ hx₀
  refine ⟨x, ⟨hxmem, hxss⟩, ?_⟩
  intro y hy
  exact N.deficiencyOneUniqueness_multiClass h κ x₀ hx₀ hy.1 hy.2 hxmem hxss

/-!
### Why the certificate is stated relative to its domain

The two facts behind the domain-relative formulation.  First, the global formulation is not
merely hard to satisfy but impossible for an ordinary class of networks: if a species occurs in
every source complex, the field vanishes on a whole face of the chart
(`CRNT.Kinetics.CatalystFace`), so its global zero set is infinite.  Second, the relative
finiteness that replaces it is not an assumption at all — deficiency-one uniqueness supplies it
on any domain inside the positive part of the chart.

`A + C ⇌ 2C ⇌ B + C` is such a network: it is weakly reversible with one strongly connected
linkage class, three complexes and rank two, hence deficiency zero, so it satisfies
`DeficiencyOneHypotheses`, while `C` occurs in every source complex and is changed by the first
reaction.
-/

/-- On the face of the chart where a global catalyst `c` is absent, the reduced field is zero. -/
theorem reducedMassActionField_eq_zero_of_stoichCoord
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (c : S)
    (hsrc : ∀ r : N.R, (N.reaction r).source c ≠ 0)
    {u : N.stoichSubspace} (hu : N.stoichCoord c u = -(x₀ c)) :
    N.reducedMassActionField κ x₀ u = 0 := by
  have hchart : (N.stoichClassChart x₀ u) c = 0 := by
    simp only [stoichClassChart, Pi.add_apply]
    rw [stoichCoord_apply] at hu
    rw [hu]
    ring
  apply Subtype.ext
  simp only [reducedMassActionField, ZeroMemClass.coe_zero]
  exact N.massActionVectorField_eq_zero_of_catalyst κ hsrc hchart

/-- **The global zero set of the reduced field is infinite for a catalytic network.** -/
theorem infinite_zeros_of_catalyst
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (c : S)
    (hsrc : ∀ r : N.R, (N.reaction r).source c ≠ 0)
    (hvar : ∃ r : N.R, N.reactionVector r c ≠ 0)
    (hdim : 2 ≤ Module.finrank ℝ N.stoichSubspace) :
    ((N.reducedMassActionField κ x₀) ⁻¹' {(0 : N.stoichSubspace)}).Infinite := by
  refine Set.Infinite.mono ?_ (N.infinite_catalystFace x₀ c hvar hdim)
  intro u hu
  exact N.reducedMassActionField_eq_zero_of_stoichCoord κ x₀ c hsrc hu

/-- **No global-finiteness certificate exists for a catalytic network.**  This is why
`DeficiencyOneDegreeCertificateGlobal` is the wrong thing to ask a proof for: the obstruction is
a triviality about monomials, not missing CRNT or missing topology. -/
theorem isEmpty_deficiencyOneDegreeCertificateGlobal_of_catalyst
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (c : S)
    (hsrc : ∀ r : N.R, (N.reaction r).source c ≠ 0)
    (hvar : ∃ r : N.R, N.reactionVector r c ≠ 0)
    (hdim : 2 ≤ Module.finrank ℝ N.stoichSubspace) :
    IsEmpty (N.DeficiencyOneDegreeCertificateGlobal κ x₀) := by
  constructor
  intro C
  exact (N.infinite_zeros_of_catalyst κ x₀ c hsrc hvar hdim) C.target_preimage_finite

/-- **Domain-relative finiteness is a theorem under the deficiency-one hypotheses.**  On a
region of the chart inside the positive part, zeros of the reduced field are positive steady
states in one positive compatibility class, and deficiency-one uniqueness allows at most one of
those.  So the `target_preimage_finite` field of `DeficiencyOneDegreeCertificate` never has to
be assumed. -/
theorem finite_zeros_inter_of_deficiencyOneHypotheses
    (N : Network S) (h : N.DeficiencyOneHypotheses) (κ : N.RateConstants)
    {x₀ : Concentration S} (hx₀ : x₀.Positive) {U : Set N.stoichSubspace}
    (hU : U ⊆ N.positiveStoichChartDomain x₀) :
    ((N.reducedMassActionField κ x₀) ⁻¹' {(0 : N.stoichSubspace)} ∩ U).Finite := by
  apply Set.Subsingleton.finite
  intro u hu v hv
  have hupos : (N.stoichClassChart x₀ u).Positive := hU hu.2
  have hvpos : (N.stoichClassChart x₀ v).Positive := hU hv.2
  have huss : N.IsMassActionSteadyState κ (N.stoichClassChart x₀ u) :=
    (N.reducedMassActionField_eq_zero_iff κ x₀ u).1 hu.1
  have hvss : N.IsMassActionSteadyState κ (N.stoichClassChart x₀ v) :=
    (N.reducedMassActionField_eq_zero_iff κ x₀ v).1 hv.1
  have humem : N.stoichClassChart x₀ u ∈ N.positiveCompatibilityClass x₀ := by
    refine ⟨?_, hupos⟩
    change N.stoichClassChart x₀ u - x₀ ∈ N.stoichSubspace
    simp [stoichClassChart]
  have hvmem : N.stoichClassChart x₀ v ∈ N.positiveCompatibilityClass x₀ := by
    refine ⟨?_, hvpos⟩
    change N.stoichClassChart x₀ v - x₀ ∈ N.stoichSubspace
    simp [stoichClassChart]
  have heq : N.stoichClassChart x₀ u = N.stoichClassChart x₀ v :=
    N.deficiencyOneUniqueness_multiClass h κ x₀ hx₀ humem huss hvmem hvss
  apply Subtype.ext
  have hadd : x₀ + u.1 = x₀ + v.1 := heq
  exact add_left_cancel hadd

end Network
end CRNT
