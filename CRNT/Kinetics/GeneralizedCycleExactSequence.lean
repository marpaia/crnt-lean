import CRNT.Kinetics.GeneralizedNetwork
import CRNT.Deficiency.CycleExactSequence
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The kinetic-order cycle exact sequence

For generalized mass-action systems there is a second deficiency exact sequence,
obtained by replacing the stoichiometric complex embedding `Y` by the kinetic-order
embedding `Y~`:

`0 → ker ∂ → ker (Y~∂) → (ker Y~ ∩ im ∂) → 0`.

The quotient therefore has dimension equal to the kinetic-order deficiency
`δ~ = rank ∂ - rank (Y~∂)`.  Thus ordinary deficiency and kinetic deficiency have
precisely parallel meanings: each measures how many reaction-cycle directions remain
stationary after forgetting graph circulation, for the stoichiometric and kinetic-order
complex embeddings respectively.
-/

namespace CRNT
namespace Network
namespace GeneralizedMassActionData

variable {S : Type} [DecidableEq S] [Fintype S]
variable {N : Network S}

/-- Reaction vectors killed by the generalized kinetic-order reaction map. -/
noncomputable def kineticCycleSpace (G : N.GeneralizedMassActionData) :
    Submodule ℝ (N.R → ℝ) :=
  LinearMap.ker G.kineticOrderMap

/-- Kinetic-order deficiency space `ker Y~ ∩ im ∂`. -/
noncomputable def kineticDeficiencySubspace (G : N.GeneralizedMassActionData) :
    Submodule ℝ (N.ComplexIdx → ℝ) :=
  LinearMap.ker G.kineticComplexMap ⊓ LinearMap.range N.incidenceMap

/-- Graph circulations are automatically kinetic-order cycles because
`Y~ ∂ v = 0` whenever `∂v=0`. -/
theorem graphCycleSpace_le_kineticCycleSpace (G : N.GeneralizedMassActionData) :
    N.graphCycleSpace ≤ G.kineticCycleSpace := by
  intro v hv
  rw [kineticCycleSpace, LinearMap.mem_ker]
  unfold kineticOrderMap
  rw [LinearMap.comp_apply, LinearMap.mem_ker.mp hv]
  simp

/-- Inclusion of graph cycles into kinetic-order cycles. -/
noncomputable def graphCycleInclusionKinetic (G : N.GeneralizedMassActionData) :
    N.graphCycleSpace →ₗ[ℝ] G.kineticCycleSpace :=
  Submodule.inclusion G.graphCycleSpace_le_kineticCycleSpace

/-- The incidence boundary of a kinetic-order cycle lies in the kinetic deficiency
space. -/
theorem incidenceMap_mem_kineticDeficiency_of_cycle
    (G : N.GeneralizedMassActionData) (v : G.kineticCycleSpace) :
    N.incidenceMap v.1 ∈ G.kineticDeficiencySubspace := by
  constructor
  · change G.kineticComplexMap (N.incidenceMap v.1) = 0
    have hv := v.2
    change G.kineticOrderMap v.1 = 0 at hv
    unfold kineticOrderMap at hv
    exact hv
  · exact ⟨v.1, rfl⟩

/-- Boundary map from kinetic-order cycles to the kinetic deficiency space. -/
noncomputable def kineticCycleToDeficiency (G : N.GeneralizedMassActionData) :
    G.kineticCycleSpace →ₗ[ℝ] G.kineticDeficiencySubspace :=
  (N.incidenceMap.domRestrict G.kineticCycleSpace).codRestrict
    G.kineticDeficiencySubspace G.incidenceMap_mem_kineticDeficiency_of_cycle

@[simp] theorem kineticCycleToDeficiency_apply
    (G : N.GeneralizedMassActionData) (v : G.kineticCycleSpace) :
    (G.kineticCycleToDeficiency v : N.ComplexIdx → ℝ) = N.incidenceMap v.1 := rfl

/-- Kernel of the kinetic cycle boundary consists precisely of ordinary graph
circulations. -/
theorem kineticCycleToDeficiency_ker (G : N.GeneralizedMassActionData) :
    LinearMap.ker G.kineticCycleToDeficiency =
      N.graphCycleSpace.comap G.kineticCycleSpace.subtype := by
  ext v
  constructor
  · intro hv
    have hz := LinearMap.mem_ker.mp hv
    have hinc : N.incidenceMap v.1 = 0 := congrArg Subtype.val hz
    change N.incidenceMap v.1 = 0
    exact hinc
  · intro hv
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change N.incidenceMap v.1 = 0
    exact hv

/-- Every kinetic-deficiency displacement has a kinetic-order cycle preimage. -/
theorem kineticCycleToDeficiency_surjective (G : N.GeneralizedMassActionData) :
    Function.Surjective G.kineticCycleToDeficiency := by
  rintro ⟨z, hzY, hzI⟩
  rcases hzI with ⟨v, rfl⟩
  have hK : G.kineticOrderMap v = 0 := by
    simpa [kineticOrderMap] using LinearMap.mem_ker.mp hzY
  exact ⟨⟨v, hK⟩, rfl⟩

/-- **Generalized cycle exact sequence.** -/
theorem kineticCycle_exact (G : N.GeneralizedMassActionData) :
    LinearMap.range G.graphCycleInclusionKinetic =
      LinearMap.ker G.kineticCycleToDeficiency := by
  rw [G.kineticCycleToDeficiency_ker]
  ext v
  constructor
  · rintro ⟨g, rfl⟩
    exact g.2
  · intro hv
    refine ⟨⟨v.1, hv⟩, ?_⟩
    apply Subtype.ext
    rfl

/-- Canonical quotient realization of the kinetic deficiency space. -/
noncomputable def kineticCycleQuotientEquivDeficiency
    (G : N.GeneralizedMassActionData) :
    (↥G.kineticCycleSpace ⧸
      (N.graphCycleSpace.comap G.kineticCycleSpace.subtype)) ≃ₗ[ℝ]
      G.kineticDeficiencySubspace := by
  let Q := N.graphCycleSpace.comap G.kineticCycleSpace.subtype
  let K := LinearMap.ker G.kineticCycleToDeficiency
  have hQK : Q = K := G.kineticCycleToDeficiency_ker.symm
  let e₀ : (↥G.kineticCycleSpace ⧸ Q) ≃ₗ[ℝ] (↥G.kineticCycleSpace ⧸ K) :=
    Submodule.quotEquivOfEq Q K hQK
  let e₁ := LinearMap.quotKerEquivRange G.kineticCycleToDeficiency
  have hr : LinearMap.range G.kineticCycleToDeficiency = ⊤ :=
    LinearMap.range_eq_top.mpr G.kineticCycleToDeficiency_surjective
  let e₂ : LinearMap.range G.kineticCycleToDeficiency ≃ₗ[ℝ] G.kineticDeficiencySubspace :=
    (LinearEquiv.ofEq _ _ hr).trans Submodule.topEquiv
  exact e₀.trans (e₁.trans e₂)

/-- The kinetic deficiency is the dimension of `ker Y~ ∩ im ∂`. -/
theorem kineticDeficiency_eq_finrank_subspace
    (G : N.GeneralizedMassActionData) :
    G.kineticDeficiency = Module.finrank ℝ G.kineticDeficiencySubspace := by
  have hbd := LinearMap.finrank_range_add_finrank_ker G.kineticCycleToDeficiency
  have hr : LinearMap.range G.kineticCycleToDeficiency = ⊤ :=
    LinearMap.range_eq_top.mpr G.kineticCycleToDeficiency_surjective
  have hk : Module.finrank ℝ (LinearMap.ker G.kineticCycleToDeficiency) =
      Module.finrank ℝ N.graphCycleSpace := by
    rw [← G.kineticCycle_exact]
    exact LinearMap.finrank_range_of_inj
      (Submodule.inclusion_injective G.graphCycleSpace_le_kineticCycleSpace)
  rw [hr, finrank_top, hk] at hbd
  have hK := LinearMap.finrank_range_add_finrank_ker G.kineticOrderMap
  have hI := LinearMap.finrank_range_add_finrank_ker N.incidenceMap
  change G.kineticOrderRank + Module.finrank ℝ G.kineticCycleSpace =
      Module.finrank ℝ (N.R → ℝ) at hK
  change N.incidenceRank + Module.finrank ℝ N.graphCycleSpace =
      Module.finrank ℝ (N.R → ℝ) at hI
  have hdef := G.incidenceRank_eq_kineticOrderRank_add_kineticDeficiency
  omega

/-- Dimension form of the generalized cycle exact sequence. -/
theorem finrank_kineticCycleSpace_eq_graphCycles_add_kineticDeficiency
    (G : N.GeneralizedMassActionData) :
    Module.finrank ℝ G.kineticCycleSpace =
      Module.finrank ℝ N.graphCycleSpace + G.kineticDeficiency := by
  have hK := LinearMap.finrank_range_add_finrank_ker G.kineticOrderMap
  have hI := LinearMap.finrank_range_add_finrank_ker N.incidenceMap
  change G.kineticOrderRank + Module.finrank ℝ G.kineticCycleSpace =
      Module.finrank ℝ (N.R → ℝ) at hK
  change N.incidenceRank + Module.finrank ℝ N.graphCycleSpace =
      Module.finrank ℝ (N.R → ℝ) at hI
  have hdef := G.incidenceRank_eq_kineticOrderRank_add_kineticDeficiency
  omega

/-- Kinetic deficiency is the cycle-space dimension gap. -/
theorem kineticDeficiency_eq_cycle_gap (G : N.GeneralizedMassActionData) :
    G.kineticDeficiency =
      Module.finrank ℝ G.kineticCycleSpace - Module.finrank ℝ N.graphCycleSpace := by
  have h := G.finrank_kineticCycleSpace_eq_graphCycles_add_kineticDeficiency
  omega

/-- Kinetic deficiency zero iff every kinetic-order stationary reaction vector is an
ordinary graph circulation. -/
theorem kineticDeficiency_zero_iff_cycles_eq_graphCycles
    (G : N.GeneralizedMassActionData) :
    G.kineticDeficiency = 0 ↔ G.kineticCycleSpace = N.graphCycleSpace := by
  constructor
  · intro hδ
    have h := G.finrank_kineticCycleSpace_eq_graphCycles_add_kineticDeficiency
    have hfin : Module.finrank ℝ N.graphCycleSpace = Module.finrank ℝ G.kineticCycleSpace := by
      omega
    exact (Submodule.eq_of_le_of_finrank_eq
      (show N.graphCycleSpace ≤ G.kineticCycleSpace from G.graphCycleSpace_le_kineticCycleSpace)
      hfin).symm
  · intro hEq
    have h := G.finrank_kineticCycleSpace_eq_graphCycles_add_kineticDeficiency
    rw [hEq] at h
    omega

/-- Pointwise form of kinetic deficiency zero. -/
theorem kineticDeficiency_zero_iff_cycle_is_graphCycle
    (G : N.GeneralizedMassActionData) :
    G.kineticDeficiency = 0 ↔
      ∀ v : N.R → ℝ, G.kineticOrderMap v = 0 → N.incidenceMap v = 0 := by
  rw [G.kineticDeficiency_zero_iff_cycles_eq_graphCycles]
  constructor
  · intro h v hv
    have hmem : v ∈ G.kineticCycleSpace := by
      change G.kineticOrderMap v = 0
      exact hv
    have : v ∈ N.graphCycleSpace := by rw [← h]; exact hmem
    exact LinearMap.mem_ker.mp this
  · intro h
    apply le_antisymm
    · intro v hv
      apply LinearMap.mem_ker.mpr
      exact h v (LinearMap.mem_ker.mp hv)
    · exact G.graphCycleSpace_le_kineticCycleSpace

/-- In the classical specialization, the generalized cycle exact sequence reduces to
its ordinary stoichiometric counterpart. -/
theorem classical_kineticCycleSpace_eq_stoichCycleSpace (N : Network S) :
    (GeneralizedMassActionData.classical N).kineticCycleSpace = N.stoichCycleSpace := by
  unfold kineticCycleSpace Network.stoichCycleSpace
  rw [classical_kineticOrderMap_eq_stoichMap]

/-- In the classical specialization the two deficiency spaces coincide. -/
theorem classical_kineticDeficiencySubspace_eq_deficiencySubspace (N : Network S) :
    (GeneralizedMassActionData.classical N).kineticDeficiencySubspace =
      N.deficiencySubspace := by
  unfold kineticDeficiencySubspace Network.deficiencySubspace
  congr 1

end GeneralizedMassActionData
end Network
end CRNT
