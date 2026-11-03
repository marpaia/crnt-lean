import CRNT.Theorems.DeficiencyOne.DegreeExistence
import CRNT.Dynamics.MassActionField

/-!
# Compatibility bridges for the merged deficiency-one degree frontier

This module preserves verified auxiliary claims from the earlier common-domain degree branch
that are independent of, and complementary to, the newer parametrized-relative-degree branch.
They are kept outside `DegreeExistence.lean` to avoid replacing the newer continuation architecture.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Continuous linear coordinates identifying the abstract stoichiometric subspace with the
finite coordinate space used by `reducedField`. -/
noncomputable def stoichSubspaceCoordEquiv (N : Network S) :
    (Fin N.stoichRank → ℝ) ≃L[ℝ] N.stoichSubspace :=
  N.stoichBasis.equivFun.symm.toContinuousLinearEquiv

@[simp] theorem stoichSubspaceCoordEquiv_coe (N : Network S) (y : Fin N.stoichRank → ℝ) :
    ((N.stoichSubspaceCoordEquiv y : N.stoichSubspace) : Concentration S) =
      N.stoichChart y := by
  simp [stoichSubspaceCoordEquiv, stoichChart, stoichChartLM]

@[simp] theorem stoichSubspaceCoordEquiv_symm_apply (N : Network S) (u : N.stoichSubspace) :
    N.stoichProj (u : Concentration S) = N.stoichSubspaceCoordEquiv.symm u := by
  apply N.stoichSubspaceCoordEquiv.injective
  apply Subtype.ext
  rw [stoichSubspaceCoordEquiv_coe]
  rw [N.stoichChart_stoichProj u.2]
  simp [stoichSubspaceCoordEquiv]

/-- The coordinate reduced mass-action field is smooth. -/
theorem reducedField_contDiff (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) {n : WithTop ℕ∞} :
    ContDiff ℝ n (N.reducedField κ x₀) := by
  have hchart : ContDiff ℝ n (N.affineChart x₀) :=
    contDiff_const.add N.stoichChart.contDiff
  have hf : ContDiff ℝ n (fun y => N.massActionVectorField κ (N.affineChart x₀ y)) := by
    simpa only [Function.comp_def] using (N.massActionVectorField_contDiff κ).comp hchart
  change ContDiff ℝ n (fun y => N.stoichProj (N.massActionVectorField κ (N.affineChart x₀ y)))
  simpa only [Function.comp_def] using N.stoichProj.contDiff.comp hf

/-- The coordinate-free reduced mass-action field on the stoichiometric subspace is smooth. -/
theorem reducedMassActionField_contDiff (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) {n : WithTop ℕ∞} :
    ContDiff ℝ n (N.reducedMassActionField κ x₀) := by
  let e := N.stoichSubspaceCoordEquiv
  have he : ContDiff ℝ n (e : (Fin N.stoichRank → ℝ) → N.stoichSubspace) := e.contDiff
  have hes : ContDiff ℝ n (e.symm : N.stoichSubspace → (Fin N.stoichRank → ℝ)) :=
    e.symm.contDiff
  have hred : ContDiff ℝ n (N.reducedField κ x₀) := N.reducedField_contDiff κ x₀
  have hmid : ContDiff ℝ n (fun u : N.stoichSubspace =>
      N.reducedField κ x₀ (e.symm u)) := by
    simpa only [Function.comp_def] using hred.comp hes
  have h : ContDiff ℝ n (fun u : N.stoichSubspace =>
      e (N.reducedField κ x₀ (e.symm u))) := by
    simpa only [Function.comp_def] using he.comp hmid
  have heq : (fun u : N.stoichSubspace => e (N.reducedField κ x₀ (e.symm u))) =
      N.reducedMassActionField κ x₀ := by
    funext u
    apply Subtype.ext
    change N.stoichChart (N.reducedField κ x₀ (e.symm u)) =
      N.massActionVectorField κ (N.stoichClassChart x₀ u)
    rw [reducedField]
    rw [N.stoichChart_stoichProj (N.massActionVectorField_mem_stoichSubspace κ _)]
    congr 2
    simp only [affineChart, stoichClassChart]
    congr 1
    rw [← N.stoichSubspaceCoordEquiv_coe (e.symm u)]
    simp [e]
  rw [← heq]
  exact h

/-- **Family confinement gives one common degree domain.**  If a compact set `K` in the positive
chart contains every zero of every slice of a homotopy on `[0,1]`, then there is one bounded open
neighborhood `U` of `K` whose closure stays positive and whose frontier is zero-free for every
slice.  This is the compactness/topology step needed to turn a family-confinement estimate into
uniform boundary control for degree invariance. -/
theorem exists_commonDegreeDomain_of_family_confinement
    (N : Network S) {x₀ : Concentration S}
    (H : ℝ → N.stoichSubspace → N.stoichSubspace)
    {K : Set N.stoichSubspace} (hKc : IsCompact K)
    (h0K : (0 : N.stoichSubspace) ∈ K)
    (hKpos : K ⊆ N.positiveStoichChartDomain x₀)
    (hzeros : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u,
      u ∈ N.positiveStoichChartDomain x₀ → H t u = 0 → u ∈ K) :
    ∃ U : Set N.stoichSubspace,
      IsOpen U ∧ Bornology.IsBounded U ∧ (0 : N.stoichSubspace) ∈ U ∧
      closure U ⊆ N.positiveStoichChartDomain x₀ ∧
      K ⊆ U ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ frontier U, H t u ≠ 0 := by
  have hposOpen : IsOpen (N.positiveStoichChartDomain x₀) :=
    N.isOpen_positiveStoichChartDomain x₀
  have hnhds : N.positiveStoichChartDomain x₀ ∈ nhdsSet K :=
    (hposOpen.mem_nhdsSet).2 hKpos
  obtain ⟨V, hVopen, hKV, hVcl⟩ := hKc.exists_isOpen_closure_subset hnhds
  obtain ⟨r, hKr⟩ := hKc.isBounded.subset_ball (0 : N.stoichSubspace)
  let U := V ∩ Metric.ball (0 : N.stoichSubspace) r
  have hUopen : IsOpen U := hVopen.inter Metric.isOpen_ball
  have hKU : K ⊆ U := fun u hu => ⟨hKV hu, hKr hu⟩
  refine ⟨U, hUopen, Metric.isBounded_ball.subset Set.inter_subset_right,
    hKU h0K, (closure_mono Set.inter_subset_left).trans hVcl, hKU, ?_⟩
  intro t ht u hu hHu
  have hucl : u ∈ closure U := frontier_subset_closure hu
  have hupos : u ∈ N.positiveStoichChartDomain x₀ :=
    hVcl ((closure_mono Set.inter_subset_left) hucl)
  have huK : u ∈ K := hzeros t ht u hupos hHu
  have huU : u ∈ U := hKU huK
  have huint : u ∈ interior U := by
    rw [hUopen.interior_eq]
    exact huU
  exact hu.2 huint

/-- Family confinement specialized to the degree-domain structure for the target slice. -/
theorem exists_deficiencyOneDegreeDomain_of_family_confinement
    (N : Network S) (κ : N.RateConstants) {x₀ : Concentration S}
    (H : ℝ → N.stoichSubspace → N.stoichSubspace)
    (hone : H 1 = N.reducedMassActionField κ x₀)
    {K : Set N.stoichSubspace} (hKc : IsCompact K)
    (h0K : (0 : N.stoichSubspace) ∈ K)
    (hKpos : K ⊆ N.positiveStoichChartDomain x₀)
    (hzeros : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u,
      u ∈ N.positiveStoichChartDomain x₀ → H t u = 0 → u ∈ K) :
    ∃ D : N.DeficiencyOneDegreeDomain κ x₀,
      K ⊆ D.U ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ frontier D.U, H t u ≠ 0 := by
  obtain ⟨U, hUopen, hUbounded, h0U, hUpos, hKU, hfront⟩ :=
    N.exists_commonDegreeDomain_of_family_confinement H hKc h0K hKpos hzeros
  let D : N.DeficiencyOneDegreeDomain κ x₀ := {
    U := U
    isOpen := hUopen
    bounded := hUbounded
    zero_mem := h0U
    closure_positive := hUpos
    boundary_nonzero := by
      intro u hu hzero
      exact hfront 1 (by norm_num) u hu (by simpa [hone] using hzero) }
  exact ⟨D, hKU, hfront⟩

/-- The straight-line continuation is jointly `C¹` in parameter and stoichiometric
coordinate.  This is the regularity input for the repository's degree-homotopy machinery. -/
theorem reducedMassActionLinearHomotopy_contDiff (N : Network S)
    (κ₀ κ : N.RateConstants) (x₀ : Concentration S) :
    ContDiff ℝ 1 (fun p : ℝ × N.stoichSubspace =>
      N.reducedMassActionLinearHomotopy κ₀ κ x₀ p.1 p.2) := by
  have h0 : ContDiff ℝ 1 (fun p : ℝ × N.stoichSubspace =>
      N.reducedMassActionField κ₀ x₀ p.2) := by
    simpa only [Function.comp_def] using
      (N.reducedMassActionField_contDiff κ₀ x₀ (n := 1)).comp contDiff_snd
  have h1 : ContDiff ℝ 1 (fun p : ℝ × N.stoichSubspace =>
      N.reducedMassActionField κ x₀ p.2) := by
    simpa only [Function.comp_def] using
      (N.reducedMassActionField_contDiff κ x₀ (n := 1)).comp contDiff_snd
  have hs0 : ContDiff ℝ 1 (fun p : ℝ × N.stoichSubspace => (1 : ℝ) - p.1) :=
    contDiff_const.sub contDiff_fst
  have hs1 : ContDiff ℝ 1 (fun p : ℝ × N.stoichSubspace => p.1) := contDiff_fst
  unfold reducedMassActionLinearHomotopy
  convert (hs0.smul h0).add (hs1.smul h1) using 1

end Network
end CRNT
