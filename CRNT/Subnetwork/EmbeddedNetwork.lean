import CRNT.Subnetwork.ReactionRestriction
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Species projection and embedded reaction networks

An embedded CRN is obtained by selecting reaction channels and observing only a selected
set of species.  This is the standard structural operation used in many inheritance and
forbidden-subnetwork arguments.

The species set of the embedded network is the subtype `{s // s ∈ V}`.  Complexes and
reaction vectors are restricted coordinatewise; a projected reaction is allowed to become
a self-reaction.  A later simplification can remove those zero-vector channels without
changing the projected vector field.
-/

namespace CRNT

namespace Complex

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Restriction of a complex to a finite species subset. -/
def restrict (V : Finset S) (y : Complex S) : Complex {s : S // s ∈ V} :=
  fun s => y s.1

@[simp] theorem restrict_apply (V : Finset S) (y : Complex S)
    (s : {s : S // s ∈ V}) : restrict V y s = y s.1 := rfl

end Complex

namespace Reaction

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Species-coordinate restriction of a reaction. -/
def restrictSpecies (V : Finset S) (r : Reaction S) :
    Reaction {s : S // s ∈ V} where
  source := Complex.restrict V r.source
  target := Complex.restrict V r.target

@[simp] theorem restrictSpecies_vector_apply (V : Finset S) (r : Reaction S)
    (s : {s : S // s ∈ V}) :
    (r.restrictSpecies V).vector s = r.vector s.1 := rfl

end Reaction

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Projection of every reaction to a selected species set. -/
def projectSpecies (N : Network S) (V : Finset S) :
    Network {s : S // s ∈ V} where
  R := N.R
  decEqR := N.decEqR
  fintypeR := N.fintypeR
  reaction := fun r => (N.reaction r).restrictSpecies V

/-- Embedded network obtained by selecting both species and reaction channels. -/
def embedded (N : Network S) (V : Finset S) (E : Finset N.R) :
    Network {s : S // s ∈ V} where
  R := {r : N.R // r ∈ E}
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun r => (N.reaction r.1).restrictSpecies V

/-- Coordinate-restriction linear map on real species vectors. -/
noncomputable def restrictSpeciesLinear (V : Finset S) :
    (S → ℝ) →ₗ[ℝ] ({s : S // s ∈ V} → ℝ) where
  toFun := fun x s => x s.1
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- Embedded reaction vectors are exactly coordinate restrictions of parent reaction
vectors. -/
@[simp] theorem embedded_reactionVector (N : Network S) (V : Finset S)
    (E : Finset N.R) (r : (N.embedded V E).R) :
    (N.embedded V E).reactionVector r =
      restrictSpeciesLinear V (N.reactionVector r.1) := by
  rfl

/-- The embedded stoichiometric subspace is contained in the image of the parent
stoichiometric subspace under species projection. -/
theorem embedded_stoichSubspace_le_map (N : Network S) (V : Finset S)
    (E : Finset N.R) :
    (N.embedded V E).stoichSubspace ≤
      N.stoichSubspace.map (restrictSpeciesLinear V) := by
  apply Submodule.span_le.mpr
  intro v hv
  rcases hv with ⟨r, rfl⟩
  refine ⟨N.reactionVector r.1, N.reactionVector_mem_stoichSubspace r.1, ?_⟩
  rfl

/-- Species/reaction embedding cannot increase stoichiometric rank. -/
theorem embedded_stoichRank_le (N : Network S) (V : Finset S)
    (E : Finset N.R) :
    (N.embedded V E).stoichRank ≤ N.stoichRank := by
  calc
    (N.embedded V E).stoichRank
        ≤ Module.finrank ℝ (N.stoichSubspace.map (restrictSpeciesLinear V)) :=
          Submodule.finrank_mono (N.embedded_stoichSubspace_le_map V E)
    _ ≤ Module.finrank ℝ N.stoichSubspace := by
      exact Submodule.finrank_map_le _ _
    _ = N.stoichRank := rfl

/-- If all parent reaction vectors are supported inside `V`, species projection loses no
stoichiometric information. -/
def ReactionVectorsSupportedIn (N : Network S) (V : Finset S) : Prop :=
  ∀ r s, s ∉ V → N.reactionVector r s = 0

/-- Under full reaction retention and support inside `V`, the parent stoichiometric
subspace is linearly equivalent to the projected one. -/
theorem projectSpecies_stoichRank_eq_of_supported
    (N : Network S) (V : Finset S) (hV : N.ReactionVectorsSupportedIn V) :
    (N.projectSpecies V).stoichRank = N.stoichRank := by
  classical
  let f := restrictSpeciesLinear (S := S) V
  have himage : f '' N.reactionVectors = (N.projectSpecies V).reactionVectors := by
    ext w
    constructor
    · rintro ⟨v, ⟨r, rfl⟩, rfl⟩
      exact ⟨r, rfl⟩
    · rintro ⟨r, rfl⟩
      exact ⟨N.reactionVector r, ⟨r, rfl⟩, rfl⟩
  have hmap : N.stoichSubspace.map f = (N.projectSpecies V).stoichSubspace := by
    unfold stoichSubspace
    rw [Submodule.map_span]
    exact congrArg (Submodule.span ℝ) himage
  have hsupport : ∀ x ∈ N.stoichSubspace, ∀ s, s ∉ V → x s = 0 := by
    intro x hx
    change x ∈ Submodule.span ℝ N.reactionVectors at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨r, rfl⟩ := hx
        exact fun s hs => hV r s hs
    | zero => simp
    | add x y _ _ hx hy =>
        intro s hs
        simp [hx s hs, hy s hs]
    | smul a x _ hx =>
        intro s hs
        simp [hx s hs]
  have hinj : Function.Injective (f.domRestrict N.stoichSubspace) := by
    intro x y hxy
    apply Subtype.ext
    funext s
    by_cases hs : s ∈ V
    · let sv : {s : S // s ∈ V} := ⟨s, hs⟩
      have := congrFun hxy sv
      exact this
    · rw [hsupport x x.property s hs, hsupport y y.property s hs]
  unfold stoichRank
  rw [← hmap, ← LinearMap.range_domRestrict]
  exact LinearMap.finrank_range_of_inj hinj

/-- Projecting to all species changes only the species-index representation. -/
noncomputable def projectSpeciesUnivEquiv (N : Network S) :
    S ≃ {s : S // s ∈ (Finset.univ : Finset S)} where
  toFun := fun s => ⟨s, Finset.mem_univ s⟩
  invFun := Subtype.val
  left_inv := by intro s; rfl
  right_inv := by intro s; cases s; rfl

end Network
end CRNT
