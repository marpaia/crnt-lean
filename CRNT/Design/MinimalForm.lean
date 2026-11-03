import CRNT.Design.BufferingStructure
import CRNT.Design.EmergentConservation

/-!
# Stoichiometric block elimination and minimal-form flux reconstruction

This module isolates the linear algebra behind the strong-buffering minimal form of
Hong--Moon--Hirono--Kim.  No pseudoinverse is chosen.  Instead, an `InternalEliminator`
is explicit certificate data saying how an exterior flux forcing `S12 c₂` is solved by
an internal flux.  This makes the exact hypotheses visible and avoids silently replacing
an inconsistent system by a least-squares solution.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Reactions outside a structural subnetwork. -/
def exteriorReactions {N : Network S} (γ : StructuralSubnetwork N) : Finset N.R :=
  Finset.univ \ γ.reactions

/-- Extend selected reaction coordinates by zero. -/
def reactionExtension {N : Network S} (E : Finset N.R) :
    (↥E → ℝ) →ₗ[ℝ] (N.R → ℝ) where
  toFun u := fun r => if hr : r ∈ E then u ⟨r, hr⟩ else 0
  map_add' u v := by
    funext r
    by_cases hr : r ∈ E <;> simp [hr]
  map_smul' a u := by
    funext r
    by_cases hr : r ∈ E <;> simp [hr]

/-- Restrict reaction coordinates. -/
def reactionRestriction {N : Network S} (E : Finset N.R) :
    (N.R → ℝ) →ₗ[ℝ] (↥E → ℝ) where
  toFun v := fun r => v r.1
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp] theorem reactionRestriction_extension {N : Network S}
    (E : Finset N.R) (u : ↥E → ℝ) :
    reactionRestriction E (reactionExtension E u) = u := by
  funext r
  simp [reactionRestriction, reactionExtension, r.property]

/-- Internal-species/internal-reaction stoichiometric block `S11`. -/
noncomputable def stoichBlock11 (N : Network S) (γ : StructuralSubnetwork N) :
    (↥γ.reactions → ℝ) →ₗ[ℝ] (↥γ.species → ℝ) :=
  (speciesRestriction γ.species).comp (N.stoichMap.comp (reactionExtension γ.reactions))

/-- Internal-species/exterior-reaction block `S12`. -/
noncomputable def stoichBlock12 (N : Network S) (γ : StructuralSubnetwork N) :
    (↥(exteriorReactions γ) → ℝ) →ₗ[ℝ] (↥γ.species → ℝ) :=
  (speciesRestriction γ.species).comp
    (N.stoichMap.comp (reactionExtension (exteriorReactions γ)))

/-- Exterior-species/internal-reaction block `S21`. -/
noncomputable def stoichBlock21 (N : Network S) (γ : StructuralSubnetwork N) :
    (↥γ.reactions → ℝ) →ₗ[ℝ] (↥(exteriorSpecies γ) → ℝ) :=
  (speciesRestriction (exteriorSpecies γ)).comp
    (N.stoichMap.comp (reactionExtension γ.reactions))

/-- Exterior-species/exterior-reaction block `S22`. -/
noncomputable def stoichBlock22 (N : Network S) (γ : StructuralSubnetwork N) :
    (↥(exteriorReactions γ) → ℝ) →ₗ[ℝ] (↥(exteriorSpecies γ) → ℝ) :=
  (speciesRestriction (exteriorSpecies γ)).comp
    (N.stoichMap.comp (reactionExtension (exteriorReactions γ)))

/-- Exact internal elimination certificate.  It is required only to solve forcings lying
in the image of `S12`; no Moore--Penrose inverse or arbitrary complement is part of the
mathematics. -/
structure InternalEliminator (N : Network S) (γ : StructuralSubnetwork N) where
  solve : (↥γ.species → ℝ) →ₗ[ℝ] (↥γ.reactions → ℝ)
  solves_exterior_forcing :
    ∀ c₂, N.stoichBlock11 γ (solve (N.stoichBlock12 γ c₂)) = N.stoichBlock12 γ c₂

/-- Reduced stoichiometric operator `S' = S22 - S21 P S12`. -/
noncomputable def reducedStoichMap (N : Network S) (γ : StructuralSubnetwork N)
    (P : N.InternalEliminator γ) :
    (↥(exteriorReactions γ) → ℝ) →ₗ[ℝ] (↥(exteriorSpecies γ) → ℝ) :=
  N.stoichBlock22 γ -
    (N.stoichBlock21 γ).comp (P.solve.comp (N.stoichBlock12 γ))

/-- Reconstruct a full flux by solving the internal block and retaining the exterior
flux unchanged. -/
noncomputable def reconstructFlux (N : Network S) (γ : StructuralSubnetwork N)
    (P : N.InternalEliminator γ) :
    (↥(exteriorReactions γ) → ℝ) →ₗ[ℝ] (N.R → ℝ) :=
  reactionExtension (exteriorReactions γ) -
    (reactionExtension γ.reactions).comp (P.solve.comp (N.stoichBlock12 γ))

/-- Reconstructed flux has zero internal-species stoichiometric residual. -/
theorem reconstructFlux_internal_balance (N : Network S)
    (γ : StructuralSubnetwork N) (P : N.InternalEliminator γ)
    (c₂ : ↥(exteriorReactions γ) → ℝ) :
    speciesRestriction γ.species (N.stoichMap (N.reconstructFlux γ P c₂)) = 0 := by
  have h := P.solves_exterior_forcing c₂
  change
    speciesRestriction γ.species
        (N.stoichMap
          (reactionExtension γ.reactions
            (P.solve (N.stoichBlock12 γ c₂)))) =
      speciesRestriction γ.species
        (N.stoichMap (reactionExtension (exteriorReactions γ) c₂)) at h
  simp only [reconstructFlux, LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
  rw [h]
  exact sub_self _


/-- Exterior residual of a reconstructed flux is exactly the reduced stoichiometric map. -/
theorem reconstructFlux_exterior_residual (N : Network S)
    (γ : StructuralSubnetwork N) (P : N.InternalEliminator γ)
    (c₂ : ↥(exteriorReactions γ) → ℝ) :
    speciesRestriction (exteriorSpecies γ)
      (N.stoichMap (N.reconstructFlux γ P c₂)) =
        N.reducedStoichMap γ P c₂ := by
  simp [reconstructFlux, reducedStoichMap, stoichBlock21, stoichBlock22, stoichBlock12]

/-- **Kernel reconstruction theorem.**  Every reduced steady-state flux reconstructs to
a full steady-state flux. -/
theorem reconstructFlux_mem_kernel (N : Network S)
    (γ : StructuralSubnetwork N) (P : N.InternalEliminator γ)
    {c₂ : ↥(exteriorReactions γ) → ℝ}
    (hc₂ : N.reducedStoichMap γ P c₂ = 0) :
    N.stoichMap (N.reconstructFlux γ P c₂) = 0 := by
  apply N.stoichMap_eq_zero_of_internal_external_zero γ
    (N.reconstructFlux γ P c₂)
  · exact N.reconstructFlux_internal_balance γ P c₂
  · rw [N.reconstructFlux_exterior_residual γ P c₂, hc₂]

/-- Reconstruction preserves the exterior reaction coordinates exactly. -/
theorem reconstructFlux_exterior_coordinates (N : Network S)
    (γ : StructuralSubnetwork N) (P : N.InternalEliminator γ)
    (c₂ : ↥(exteriorReactions γ) → ℝ) :
    reactionRestriction (exteriorReactions γ) (N.reconstructFlux γ P c₂) = c₂ := by
  funext r
  have hr : r.1 ∉ γ.reactions := by
    have hmem : r.1 ∈ Finset.univ \ γ.reactions := by
      exact r.property
    exact (Finset.mem_sdiff.mp hmem).2
  simp [reconstructFlux, reactionRestriction, reactionExtension, r.property, hr]

/-- Reconstruction is injective because exterior coordinates are unchanged. -/
theorem reconstructFlux_injective (N : Network S)
    (γ : StructuralSubnetwork N) (P : N.InternalEliminator γ) :
    Function.Injective (N.reconstructFlux γ P) := by
  intro a b h
  have := congrArg (reactionRestriction (exteriorReactions γ)) h
  simpa [N.reconstructFlux_exterior_coordinates γ P] using this

/-- If `S11` has trivial kernel, every full stationary flux is uniquely reconstructed
from its exterior coordinates. -/
theorem stationaryFlux_eq_reconstruct_of_block11_injective
    (N : Network S) (γ : StructuralSubnetwork N) (P : N.InternalEliminator γ)
    (h11 : Function.Injective (N.stoichBlock11 γ))
    {c : N.R → ℝ} (hc : N.stoichMap c = 0) :
    c = N.reconstructFlux γ P (reactionRestriction (exteriorReactions γ) c) := by
  let c1 : ↥γ.reactions → ℝ := reactionRestriction γ.reactions c
  let c2 : ↥(exteriorReactions γ) → ℝ := reactionRestriction (exteriorReactions γ) c
  have hdecomp :
      c = reactionExtension γ.reactions c1 +
        reactionExtension (exteriorReactions γ) c2 := by
    funext r
    by_cases hr : r ∈ γ.reactions
    · have hrext : r ∉ exteriorReactions γ := by
        simp [exteriorReactions, hr]
      simp [c1, c2, reactionRestriction, reactionExtension, hr, hrext]
    · have hrext : r ∈ exteriorReactions γ := by
        simp [exteriorReactions, hr]
      simp [c1, c2, reactionRestriction, reactionExtension, hr, hrext]
  have hbal : N.stoichBlock11 γ c1 + N.stoichBlock12 γ c2 = 0 := by
    change
      speciesRestriction γ.species
          (N.stoichMap (reactionExtension γ.reactions c1)) +
        speciesRestriction γ.species
          (N.stoichMap (reactionExtension (exteriorReactions γ) c2)) = 0
    rw [← map_add]
    rw [← map_add]
    rw [← hdecomp, hc]
    rfl
  have hsolve : N.stoichBlock11 γ (-P.solve (N.stoichBlock12 γ c2)) =
      -N.stoichBlock12 γ c2 := by
    rw [map_neg, P.solves_exterior_forcing]
  have hc1 : c1 = -P.solve (N.stoichBlock12 γ c2) := by
    apply h11
    rw [hsolve]
    exact eq_neg_of_add_eq_zero_left hbal
  rw [show reactionRestriction (exteriorReactions γ) c = c2 by rfl]
  unfold reconstructFlux
  funext r
  by_cases hr : r ∈ γ.reactions
  · have hrext : r ∉ exteriorReactions γ := by
      simp [exteriorReactions, hr]
    have hc1r := congrFun hc1 ⟨r, hr⟩
    simp [reactionExtension, hr, hrext, c1, reactionRestriction] at hc1r ⊢
    linarith
  · have hrext : r ∈ exteriorReactions γ := by
      simp [exteriorReactions, hr]
    simp [reactionExtension, hr, hrext, c2, reactionRestriction]

/-- Under injective `S11`, restriction and reconstruction give a linear equivalence
between the reduced kernel and the full stoichiometric kernel. -/
noncomputable def reducedKernelEquivFullKernel (N : Network S)
    (γ : StructuralSubnetwork N) (P : N.InternalEliminator γ)
    (h11 : Function.Injective (N.stoichBlock11 γ)) :
    LinearMap.ker (N.reducedStoichMap γ P) ≃ₗ[ℝ] LinearMap.ker N.stoichMap := by
  let f : LinearMap.ker (N.reducedStoichMap γ P) →ₗ[ℝ]
      LinearMap.ker N.stoichMap :=
    { toFun := fun z => ⟨N.reconstructFlux γ P z.1,
        N.reconstructFlux_mem_kernel γ P z.2⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp
      map_smul' := by
        intro a x
        apply Subtype.ext
        simp }
  let g : LinearMap.ker N.stoichMap →ₗ[ℝ]
      LinearMap.ker (N.reducedStoichMap γ P) :=
    { toFun := fun c => ⟨reactionRestriction (exteriorReactions γ) c.1, by
          have hrec :=
            N.stationaryFlux_eq_reconstruct_of_block11_injective γ P h11 c.2
          have hres := N.reconstructFlux_exterior_residual γ P
            (reactionRestriction (exteriorReactions γ) c.1)
          rw [← hrec, c.2] at hres
          simpa using hres.symm⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp
      map_smul' := by
        intro a x
        apply Subtype.ext
        simp }
  refine LinearEquiv.ofLinear f g ?_ ?_
  · apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact
      N.stationaryFlux_eq_reconstruct_of_block11_injective γ P h11 c.2 |>.symm
  · apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact N.reconstructFlux_exterior_coordinates γ P z.1

/-- Consequently the reduced and original stationary-flux spaces have equal dimension. -/
theorem finrank_reducedKernel_eq_fullKernel (N : Network S)
    (γ : StructuralSubnetwork N) (P : N.InternalEliminator γ)
    (h11 : Function.Injective (N.stoichBlock11 γ)) :
    Module.finrank ℝ (LinearMap.ker (N.reducedStoichMap γ P)) =
      Module.finrank ℝ (LinearMap.ker N.stoichMap) := by
  exact LinearEquiv.finrank_eq (N.reducedKernelEquivFullKernel γ P h11)

end Network
end CRNT
