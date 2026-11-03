import CRNT.Deficiency.ExactSequence
import CRNT.Flux.Cone
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The reaction-cycle exact sequence and deficiency

Besides the familiar exact sequence

`0 → D → im ∂ → S → 0`,

where `D = ker Y ∩ im ∂` is the deficiency space, there is an equally useful
reaction-space exact sequence

`0 → ker ∂ → ker S → D → 0`.

Thus deficiency measures precisely the stationary reaction flux directions that are
not graph-circulations.  Equivalently, it is the gap between the stoichiometric cycle
space and the ordinary incidence-cycle space.

This is a particularly useful formulation because it connects deficiency directly to
T-invariants/steady fluxes, graph cycles, and Wegscheider relations.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The real graph-cycle space: reaction flows with zero incidence boundary. -/
noncomputable def graphCycleSpace (N : Network S) : Submodule ℝ (N.R → ℝ) :=
  LinearMap.ker N.incidenceMap

/-- The real stoichiometric-cycle space.  This is the linear hull of the steady flux
cone, and is definitionally the kernel of the stoichiometric map. -/
noncomputable def stoichCycleSpace (N : Network S) : Submodule ℝ (N.R → ℝ) :=
  LinearMap.ker N.stoichMap

@[simp] theorem stoichCycleSpace_eq_fluxSpace (N : Network S) :
    N.stoichCycleSpace = N.fluxSpace := rfl

/-- Every graph circulation is stoichiometrically stationary because `S = Y∂`. -/
theorem graphCycleSpace_le_stoichCycleSpace (N : Network S) :
    N.graphCycleSpace ≤ N.stoichCycleSpace := by
  intro v hv
  rw [graphCycleSpace, LinearMap.mem_ker] at hv
  rw [stoichCycleSpace, LinearMap.mem_ker]
  have hfac := congrArg (fun f => f v) N.complexMap_comp_incidenceMap
  simpa [hv] using hfac.symm

/-- Inclusion of graph cycles into stoichiometric cycles. -/
noncomputable def graphCycleInclusion (N : Network S) :
    N.graphCycleSpace →ₗ[ℝ] N.stoichCycleSpace :=
  Submodule.inclusion (N.graphCycleSpace_le_stoichCycleSpace)

/-- A stoichiometric cycle has incidence displacement in the deficiency subspace. -/
theorem incidenceMap_mem_deficiency_of_stoichCycle (N : Network S)
    (v : N.stoichCycleSpace) : N.incidenceMap v.1 ∈ N.deficiencySubspace := by
  constructor
  · simp only [SetLike.mem_coe, LinearMap.mem_ker]
    have hfac := congrArg (fun f => f v.1) N.complexMap_comp_incidenceMap
    have hS : N.stoichMap v.1 = 0 := v.2
    simpa [hS] using hfac
  · exact ⟨v.1, rfl⟩

/-- The boundary of a stoichiometric cycle, regarded as a deficiency vector. -/
noncomputable def cycleToDeficiency (N : Network S) :
    N.stoichCycleSpace →ₗ[ℝ] N.deficiencySubspace :=
  (N.incidenceMap.domRestrict N.stoichCycleSpace).codRestrict N.deficiencySubspace
    (N.incidenceMap_mem_deficiency_of_stoichCycle)

@[simp] theorem cycleToDeficiency_apply (N : Network S) (v : N.stoichCycleSpace) :
    (N.cycleToDeficiency v : N.ComplexIdx → ℝ) = N.incidenceMap v.1 := rfl

/-- The kernel of the cycle-to-deficiency map consists exactly of graph cycles. -/
theorem cycleToDeficiency_ker (N : Network S) :
    LinearMap.ker N.cycleToDeficiency =
      N.graphCycleSpace.comap N.stoichCycleSpace.subtype := by
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

/-- Every deficiency displacement is the incidence boundary of some stoichiometric
cycle.  This is the surjectivity half of the cycle exact sequence. -/
theorem cycleToDeficiency_surjective (N : Network S) :
    Function.Surjective N.cycleToDeficiency := by
  rintro ⟨z, hzY, hzI⟩
  rcases hzI with ⟨v, rfl⟩
  have hS : N.stoichMap v = 0 := by
    have hfac := congrArg (fun f => f v) N.complexMap_comp_incidenceMap
    have hY : N.complexMap (N.incidenceMap v) = 0 := LinearMap.mem_ker.mp hzY
    simpa [hY] using hfac.symm
  refine ⟨⟨v, hS⟩, ?_⟩
  rfl

/-- Exactness of `graph cycles → stoichiometric cycles → deficiency`. -/
theorem cycle_exact_at_stoichCycles (N : Network S) :
    LinearMap.range N.graphCycleInclusion = LinearMap.ker N.cycleToDeficiency := by
  rw [N.cycleToDeficiency_ker]
  ext v
  constructor
  · rintro ⟨g, rfl⟩
    exact g.2
  · intro hv
    refine ⟨⟨v.1, hv⟩, ?_⟩
    apply Subtype.ext
    rfl

/-- **Reaction-cycle exact sequence.**  The quotient of stoichiometric cycles by graph
cycles is canonically the deficiency space. -/
noncomputable def cycleQuotientEquivDeficiency (N : Network S) :
    (↥N.stoichCycleSpace ⧸
      (N.graphCycleSpace.comap N.stoichCycleSpace.subtype)) ≃ₗ[ℝ]
      N.deficiencySubspace := by
  let Q := N.graphCycleSpace.comap N.stoichCycleSpace.subtype
  let K := LinearMap.ker N.cycleToDeficiency
  have hQK : Q = K := N.cycleToDeficiency_ker.symm
  let e₀ : (↥N.stoichCycleSpace ⧸ Q) ≃ₗ[ℝ] (↥N.stoichCycleSpace ⧸ K) :=
    Submodule.quotEquivOfEq Q K hQK
  let e₁ := LinearMap.quotKerEquivRange N.cycleToDeficiency
  have hr : LinearMap.range N.cycleToDeficiency = ⊤ :=
    LinearMap.range_eq_top.mpr N.cycleToDeficiency_surjective
  let e₂ : LinearMap.range N.cycleToDeficiency ≃ₗ[ℝ] N.deficiencySubspace :=
    (LinearEquiv.ofEq _ _ hr).trans Submodule.topEquiv
  exact e₀.trans (e₁.trans e₂)

/-- Dimension form of the reaction-cycle exact sequence. -/
theorem finrank_stoichCycleSpace_eq_graphCycles_add_deficiency (N : Network S) :
    Module.finrank ℝ N.stoichCycleSpace =
      Module.finrank ℝ N.graphCycleSpace + Module.finrank ℝ N.deficiencySubspace := by
  have hrn := LinearMap.finrank_range_add_finrank_ker N.cycleToDeficiency
  have hr : LinearMap.range N.cycleToDeficiency = ⊤ :=
    LinearMap.range_eq_top.mpr N.cycleToDeficiency_surjective
  have hk : Module.finrank ℝ (LinearMap.ker N.cycleToDeficiency) =
      Module.finrank ℝ N.graphCycleSpace := by
    -- inclusion identifies the graph-cycle space with this kernel
    rw [← N.cycle_exact_at_stoichCycles]
    exact LinearMap.finrank_range_of_inj
      (Submodule.inclusion_injective N.graphCycleSpace_le_stoichCycleSpace)
  rw [hr, finrank_top, hk] at hrn
  omega

/-- Deficiency is the dimension gap between stoichiometric and graph cycle spaces. -/
theorem deficiency_finrank_eq_cycle_gap (N : Network S) :
    Module.finrank ℝ N.deficiencySubspace =
      Module.finrank ℝ N.stoichCycleSpace - Module.finrank ℝ N.graphCycleSpace := by
  have h := N.finrank_stoichCycleSpace_eq_graphCycles_add_deficiency
  omega

/-- Deficiency zero means that every stationary real reaction flux is already an
ordinary circulation of the reaction graph. -/
theorem deficiencyZero_iff_stoichCycles_eq_graphCycles (N : Network S) :
    N.DeficiencyZero ↔ N.stoichCycleSpace = N.graphCycleSpace := by
  constructor
  · intro hδ
    apply le_antisymm
    · intro v hv
      have hz : N.cycleToDeficiency ⟨v, hv⟩ = 0 := by
        have hD : N.deficiencySubspace = ⊥ :=
          N.deficiencyZero_iff_deficiencySubspace_eq_bot.mp hδ
        apply Subtype.ext
        exact (N.deficiencySubspace.eq_bot_iff.mp hD)
          (N.cycleToDeficiency ⟨v, hv⟩).1
          (N.cycleToDeficiency ⟨v, hv⟩).2
      have hk : ⟨v, hv⟩ ∈ LinearMap.ker N.cycleToDeficiency :=
        LinearMap.mem_ker.mpr hz
      rw [← N.cycle_exact_at_stoichCycles] at hk
      rcases hk with ⟨g, hg⟩
      have hval : (g.1 : N.R → ℝ) = v := congrArg Subtype.val hg
      simpa [hval] using g.2
    · exact N.graphCycleSpace_le_stoichCycleSpace
  · intro hEq
    apply N.deficiencyZero_iff_deficiencySubspace_eq_bot.mpr
    apply (N.deficiencySubspace.eq_bot_iff).2
    intro z hz
    obtain ⟨v, hvout⟩ := N.cycleToDeficiency_surjective ⟨z, hz⟩
    have hv : (v.1 : N.R → ℝ) ∈ N.graphCycleSpace := by
      rw [← hEq]
      exact v.2
    have hc0 : N.cycleToDeficiency v = 0 := by
      apply Subtype.ext
      change N.incidenceMap v.1 = 0
      exact LinearMap.mem_ker.mp hv
    calc
      z = (N.cycleToDeficiency v).1 := (congrArg Subtype.val hvout).symm
      _ = 0 := congrArg Subtype.val hc0

/-- Equivalent pointwise form: deficiency zero iff `Sv=0` forces `∂v=0`. -/
theorem deficiencyZero_iff_stoichCycle_is_graphCycle (N : Network S) :
    N.DeficiencyZero ↔
      ∀ v : N.R → ℝ, N.stoichMap v = 0 → N.incidenceMap v = 0 := by
  rw [N.deficiencyZero_iff_stoichCycles_eq_graphCycles]
  constructor
  · intro h v hv
    have : v ∈ N.graphCycleSpace := by rw [← h]; exact hv
    exact LinearMap.mem_ker.mp this
  · intro h
    apply le_antisymm
    · intro v hv
      exact LinearMap.mem_ker.mpr (h v (LinearMap.mem_ker.mp hv))
    · exact N.graphCycleSpace_le_stoichCycleSpace

end Network
end CRNT
