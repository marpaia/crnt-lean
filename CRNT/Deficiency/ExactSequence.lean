import CRNT.Deficiency.KernelDimension
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The deficiency exact sequence

The deficiency is not only the number `n-ℓ-s`.  Intrinsically it is the kernel
of the complex map after restricting to the graph incidence image.  Thus every CRN
has a canonical short exact sequence

  0 → D → im ∂ → S → 0,

where `D = ker Y ∩ im ∂` is the deficiency subspace and `S` is the
stoichiometric subspace.  Deficiency zero is exactly injectivity of `Y` on
`im ∂`, and the quotient `(im ∂)/D` is canonically isomorphic to `S`.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Incidence image as a named subspace. -/
noncomputable abbrev incidenceSubspace (N : Network S) : Submodule ℝ (N.ComplexIdx → ℝ) :=
  LinearMap.range N.incidenceMap

/-- The complex map restricted to the incidence image, with codomain restricted to the
stoichiometric subspace. -/
noncomputable def incidenceToStoich (N : Network S) :
    N.incidenceSubspace →ₗ[ℝ] N.stoichSubspace :=
  (N.complexMap.domRestrict N.incidenceSubspace).codRestrict N.stoichSubspace
    (by
      intro z
      rcases z with ⟨z, ⟨u, rfl⟩⟩
      change N.complexMap (N.incidenceMap u) ∈ N.stoichSubspace
      rw [← LinearMap.comp_apply, N.complexMap_comp_incidenceMap]
      rw [← N.range_stoichMap]
      exact ⟨u, rfl⟩)

/-- The restricted complex map is surjective onto the stoichiometric subspace. -/
theorem incidenceToStoich_surjective (N : Network S) :
    Function.Surjective N.incidenceToStoich := by
  rintro ⟨x, hx⟩
  rw [← N.range_stoichMap] at hx
  rcases hx with ⟨u, rfl⟩
  refine ⟨⟨N.incidenceMap u, ⟨u, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change N.complexMap (N.incidenceMap u) = N.stoichMap u
  simpa using congrArg (fun f => f u) N.complexMap_comp_incidenceMap

/-- Kernel of the restricted map, written inside the incidence subspace. -/
noncomputable def deficiencyKernel (N : Network S) :
    Submodule ℝ N.incidenceSubspace :=
  LinearMap.ker N.incidenceToStoich

/-- The deficiency kernel maps isomorphically onto `ker Y ∩ im ∂`. -/
noncomputable def deficiencyKernelEquiv (N : Network S) :
    N.deficiencyKernel ≃ₗ[ℝ] N.deficiencySubspace where
  toFun z :=
    ⟨z.1.1, by
      constructor
      · have hz : N.incidenceToStoich z.1 = 0 := LinearMap.mem_ker.mp z.2
        exact LinearMap.mem_ker.mpr (congrArg Subtype.val hz)
      · exact z.1.2⟩
  invFun z :=
    ⟨⟨z.1, z.2.2⟩, by
      change N.incidenceToStoich ⟨z.1, z.2.2⟩ = 0
      apply Subtype.ext
      exact LinearMap.mem_ker.mp z.2.1⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    rfl
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' a x := by
    apply Subtype.ext
    rfl

/-- Deficiency is the nullity of the restricted complex map. -/
theorem finrank_deficiencyKernel (N : Network S) :
    Module.finrank ℝ N.deficiencyKernel =
      Module.finrank ℝ N.deficiencySubspace := by
  exact LinearEquiv.finrank_eq N.deficiencyKernelEquiv

/-- Rank-nullity written as the canonical deficiency exact sequence. -/
theorem incidence_finrank_eq_deficiency_add_stoich (N : Network S) :
    Module.finrank ℝ N.incidenceSubspace =
      Module.finrank ℝ N.deficiencySubspace + Module.finrank ℝ N.stoichSubspace := by
  have hrn := LinearMap.finrank_range_add_finrank_ker N.incidenceToStoich
  have hsur : LinearMap.range N.incidenceToStoich = ⊤ :=
    LinearMap.range_eq_top.mpr N.incidenceToStoich_surjective
  have hker : Module.finrank ℝ (LinearMap.ker N.incidenceToStoich) =
      Module.finrank ℝ N.deficiencySubspace := by
    change Module.finrank ℝ N.deficiencyKernel = _
    exact N.finrank_deficiencyKernel
  have hrange : Module.finrank ℝ (LinearMap.range N.incidenceToStoich) =
      Module.finrank ℝ N.stoichSubspace := by
    rw [hsur, finrank_top]
  rw [hrange, hker] at hrn
  omega

/-- **Deficiency-zero injectivity criterion.** -/
theorem deficiencySubspace_eq_bot_iff_incidenceToStoich_injective (N : Network S) :
    N.deficiencySubspace = ⊥ ↔ Function.Injective N.incidenceToStoich := by
  constructor
  · intro hD
    have hD0 : Module.finrank ℝ N.deficiencySubspace = 0 := by simp [hD]
    have hK0 : Module.finrank ℝ N.deficiencyKernel = 0 := by
      rw [N.finrank_deficiencyKernel]
      exact hD0
    have hKbot : N.deficiencyKernel = ⊥ := Submodule.finrank_eq_zero.mp hK0
    apply LinearMap.ker_eq_bot.mp
    simpa [deficiencyKernel] using hKbot
  · intro hinj
    have hKbot : N.deficiencyKernel = ⊥ := by
      simpa [deficiencyKernel] using (LinearMap.ker_eq_bot.mpr hinj)
    have hK0 : Module.finrank ℝ N.deficiencyKernel = 0 := by simp [hKbot]
    have hD0 : Module.finrank ℝ N.deficiencySubspace = 0 := by
      rw [← N.finrank_deficiencyKernel]
      exact hK0
    exact Submodule.finrank_eq_zero.mp hD0

/-- **Intrinsic deficiency-zero criterion:** `Y` is injective on the graph cut space. -/
theorem deficiencyZero_iff_incidenceToStoich_injective (N : Network S) :
    N.DeficiencyZero ↔ Function.Injective N.incidenceToStoich := by
  rw [N.deficiencyZero_iff_deficiencySubspace_eq_bot,
      N.deficiencySubspace_eq_bot_iff_incidenceToStoich_injective]

/-- A deficiency vector is exactly a nonzero incidence displacement invisible to the
species-complex map. -/
def IsDeficiencyWitness (N : Network S) (z : N.ComplexIdx → ℝ) : Prop :=
  z ∈ LinearMap.range N.incidenceMap ∧ N.complexMap z = 0 ∧ z ≠ 0

/-- Positive deficiency is equivalent to existence of a nontrivial deficiency witness. -/
theorem deficiencySubspace_ne_bot_iff_exists_witness (N : Network S) :
    N.deficiencySubspace ≠ ⊥ ↔ ∃ z, N.IsDeficiencyWitness z := by
  constructor
  · intro hne
    letI : Nontrivial N.deficiencySubspace := Submodule.nontrivial_iff_ne_bot.mpr hne
    obtain ⟨w, hw0⟩ := exists_ne (0 : N.deficiencySubspace)
    refine ⟨w.1, w.2.2, LinearMap.mem_ker.mp w.2.1, ?_⟩
    intro hz
    apply hw0
    apply Subtype.ext
    exact hz
  · rintro ⟨z, hzI, hzY, hz0⟩ hbot
    have hz : z ∈ N.deficiencySubspace :=
      ⟨LinearMap.mem_ker.mpr hzY, hzI⟩
    have : z = 0 := by
      have hz' : z ∈ (⊥ : Submodule ℝ (N.ComplexIdx → ℝ)) := by simpa [hbot] using hz
      simpa using hz'
    exact hz0 this

/-- Quotient of the incidence image by deficiency is canonically equivalent to the
stoichiometric subspace (first isomorphism theorem). -/
noncomputable def incidenceQuotientDeficiencyEquivStoich (N : Network S) :
    (↥N.incidenceSubspace ⧸ N.deficiencyKernel) ≃ₗ[ℝ] N.stoichSubspace := by
  change (↥N.incidenceSubspace ⧸ LinearMap.ker N.incidenceToStoich) ≃ₗ[ℝ]
    N.stoichSubspace
  exact N.incidenceToStoich.quotKerEquivOfSurjective N.incidenceToStoich_surjective

end Network
end CRNT
