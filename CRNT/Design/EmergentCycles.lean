import CRNT.Design.BufferingStructure
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Emergent cycles of a structural subnetwork

For a structural subnetwork `γ = (Vγ,Eγ)`, a **locally balanced flux** is a reaction
flux supported on `Eγ` whose stoichiometric production vanishes on the internal species
`Vγ`.  Such a flux need not be a cycle of the full network: it may leak stoichiometric
change into species outside `Vγ`.

The exterior-leakage map sends a locally balanced flux to this exterior change.  Its
range is the intrinsic, basis-independent space of **emergent cycles**.  Its kernel is
exactly the globally balanced cycles supported on `Eγ`.  Rank-nullity therefore gives

`dim local cycles = dim supported global cycles + dim emergent cycles`.

This is the coordinate-free counterpart of the `ker S11` / `S21` construction used in
RPAFinder and the buffering-structure literature.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Species outside a structural subnetwork. -/
def exteriorSpecies {N : Network S} (γ : StructuralSubnetwork N) : Finset S :=
  Finset.univ \ γ.species

/-- Stoichiometric change restricted to the internal species of `γ`. -/
noncomputable def internalStoichMap (N : Network S) (γ : StructuralSubnetwork N) :
    (N.R → ℝ) →ₗ[ℝ] (↥γ.species → ℝ) :=
  (speciesRestriction γ.species).comp N.stoichMap

/-- Fluxes supported on `Eγ` that balance every internal species. -/
noncomputable def localCycleSubspace (N : Network S) (γ : StructuralSubnetwork N) :
    Submodule ℝ (N.R → ℝ) :=
  N.supportedReactionSubspace γ.reactions ⊓ LinearMap.ker (N.internalStoichMap γ)

/-- A local cycle is, in particular, supported on the reactions of the subnetwork. -/
theorem localCycle_mem_supported (N : Network S) {γ : StructuralSubnetwork N}
    {v : N.R → ℝ} (hv : v ∈ N.localCycleSubspace γ) :
    v ∈ N.supportedReactionSubspace γ.reactions := hv.1

/-- A local cycle produces no net change on the internal species. -/
theorem localCycle_internal_balance (N : Network S) {γ : StructuralSubnetwork N}
    {v : N.R → ℝ} (hv : v ∈ N.localCycleSubspace γ) :
    N.internalStoichMap γ v = 0 := hv.2

/-- Exterior stoichiometric leakage of a locally balanced flux. -/
noncomputable def exteriorLeakageMap (N : Network S) (γ : StructuralSubnetwork N) :
    N.localCycleSubspace γ →ₗ[ℝ] (↥(exteriorSpecies γ) → ℝ) :=
  (speciesRestriction (exteriorSpecies γ)).comp
    (N.stoichMap.domRestrict (N.localCycleSubspace γ))

/-- The basis-independent space of emergent cycles: possible exterior leakage generated
by internally balanced reaction fluxes. -/
noncomputable def emergentCycleSubspace (N : Network S) (γ : StructuralSubnetwork N) :
    Submodule ℝ (↥(exteriorSpecies γ) → ℝ) :=
  LinearMap.range (N.exteriorLeakageMap γ)

/-- Locally balanced fluxes with zero exterior leakage. -/
noncomputable def trueLocalCycleSubspace (N : Network S) (γ : StructuralSubnetwork N) :
    Submodule ℝ (N.localCycleSubspace γ) :=
  LinearMap.ker (N.exteriorLeakageMap γ)

noncomputable def localCycleDim (N : Network S) (γ : StructuralSubnetwork N) : ℕ :=
  Module.finrank ℝ (N.localCycleSubspace γ)

noncomputable def emergentCycleDim (N : Network S) (γ : StructuralSubnetwork N) : ℕ :=
  Module.finrank ℝ (N.emergentCycleSubspace γ)

noncomputable def trueLocalCycleDim (N : Network S) (γ : StructuralSubnetwork N) : ℕ :=
  Module.finrank ℝ (N.trueLocalCycleSubspace γ)

/-- Rank-nullity for exterior leakage. -/
theorem localCycleDim_eq_true_add_emergent (N : Network S)
    (γ : StructuralSubnetwork N) :
    N.localCycleDim γ = N.trueLocalCycleDim γ + N.emergentCycleDim γ := by
  unfold localCycleDim trueLocalCycleDim emergentCycleDim emergentCycleSubspace
    trueLocalCycleSubspace
  have h := LinearMap.finrank_range_add_finrank_ker (N.exteriorLeakageMap γ)
  calc
    Module.finrank ℝ ↥(N.localCycleSubspace γ) =
        Module.finrank ℝ ↥(LinearMap.range (N.exteriorLeakageMap γ)) +
          Module.finrank ℝ ↥(LinearMap.ker (N.exteriorLeakageMap γ)) := h.symm
    _ = Module.finrank ℝ ↥(LinearMap.ker (N.exteriorLeakageMap γ)) +
          Module.finrank ℝ ↥(LinearMap.range (N.exteriorLeakageMap γ)) := Nat.add_comm _ _

/-- Vanishing internal and exterior restrictions force the full stoichiometric change to
vanish.  This is the finite coordinate decomposition `Vγ ⊔ Vγᶜ = S`. -/
theorem stoichMap_eq_zero_of_internal_external_zero (N : Network S)
    (γ : StructuralSubnetwork N) (v : N.R → ℝ)
    (hin : N.internalStoichMap γ v = 0)
    (hout : speciesRestriction (exteriorSpecies γ) (N.stoichMap v) = 0) :
    N.stoichMap v = 0 := by
  funext s
  by_cases hs : s ∈ γ.species
  · have := congrFun hin ⟨s, hs⟩
    simpa [internalStoichMap, speciesRestriction] using this
  · have hsout : s ∈ exteriorSpecies γ := by
      simp [exteriorSpecies, hs]
    have := congrFun hout ⟨s, hsout⟩
    simpa [speciesRestriction] using this

/-- The kernel of exterior leakage is precisely the supported global cycle space, after
forgetting the subtype wrappers. -/
theorem trueLocalCycle_iff_supportedCycle (N : Network S)
    (γ : StructuralSubnetwork N) (v : N.localCycleSubspace γ) :
    v ∈ N.trueLocalCycleSubspace γ ↔
      (v.1 : N.R → ℝ) ∈ N.supportedCycleSubspace γ := by
  constructor
  · intro h
    refine ⟨?_, v.property.1⟩
    apply N.stoichMap_eq_zero_of_internal_external_zero γ v.1
    · exact v.property.2
    · exact h
  · intro h
    change N.exteriorLeakageMap γ v = 0
    simp only [exteriorLeakageMap, LinearMap.comp_apply, LinearMap.domRestrict_apply]
    rw [h.1]
    rfl

/-- The true local-cycle kernel has the same dimension as the globally balanced cycle
space supported in `Eγ`. -/
theorem trueLocalCycleDim_eq_supportedCycleDim (N : Network S)
    (γ : StructuralSubnetwork N) :
    N.trueLocalCycleDim γ = N.supportedCycleDim γ := by
  let e : N.trueLocalCycleSubspace γ ≃ₗ[ℝ] N.supportedCycleSubspace γ :=
    { toFun := fun v =>
        ⟨v.1.1, (N.trueLocalCycle_iff_supportedCycle γ v.1).1 v.2⟩
      invFun := fun w =>
        ⟨⟨w.1, by
            constructor
            · exact w.2.2
            · change N.internalStoichMap γ w.1 = 0
              simp only [internalStoichMap, LinearMap.comp_apply]
              rw [LinearMap.mem_ker.mp w.2.1]
              rfl⟩, by
          apply (N.trueLocalCycle_iff_supportedCycle γ _).2
          exact w.2⟩
      left_inv := by
        intro v
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := by
        intro w
        apply Subtype.ext
        rfl
      map_add' := by
        intro x y
        apply Subtype.ext
        rfl
      map_smul' := by
        intro a x
        apply Subtype.ext
        rfl }
  simpa [trueLocalCycleDim, supportedCycleDim] using e.finrank_eq

/-- **Emergent-cycle dimension formula.** -/
theorem localCycleDim_eq_supportedCycleDim_add_emergentCycleDim
    (N : Network S) (γ : StructuralSubnetwork N) :
    N.localCycleDim γ = N.supportedCycleDim γ + N.emergentCycleDim γ := by
  rw [N.localCycleDim_eq_true_add_emergent γ,
    N.trueLocalCycleDim_eq_supportedCycleDim γ]

/-- No emergent cycles iff every internally balanced supported flux is already a global
stoichiometric cycle. -/
theorem emergentCycleDim_eq_zero_iff (N : Network S)
    (γ : StructuralSubnetwork N) :
    N.emergentCycleDim γ = 0 ↔
      ∀ v : N.R → ℝ, v ∈ N.localCycleSubspace γ → N.stoichMap v = 0 := by
  constructor
  · intro h v hv
    have hrange : LinearMap.range (N.exteriorLeakageMap γ) = ⊥ := by
      have hem : N.emergentCycleSubspace γ = ⊥ :=
        Submodule.finrank_eq_zero.mp h
      simpa [emergentCycleSubspace] using hem
    let vv : N.localCycleSubspace γ := ⟨v, hv⟩
    have hout : N.exteriorLeakageMap γ vv = 0 := by
      have hm : N.exteriorLeakageMap γ vv ∈ LinearMap.range (N.exteriorLeakageMap γ) :=
        ⟨vv, rfl⟩
      rw [hrange] at hm
      exact hm
    exact N.stoichMap_eq_zero_of_internal_external_zero γ v hv.2 hout
  · intro h
    have hem : N.emergentCycleSubspace γ = ⊥ := by
      unfold emergentCycleSubspace
      apply (LinearMap.range (N.exteriorLeakageMap γ)).eq_bot_iff.mpr
      intro y hy
      rcases hy with ⟨v, rfl⟩
      have hz := h v.1 v.property
      simp [exteriorLeakageMap, hz]
    unfold emergentCycleDim
    exact Submodule.finrank_eq_zero.mpr hem

end Network
end CRNT
