import CRNT.Basic.Network
import CRNT.Stoich.Subspace
import CRNT.Kinetics.MassAction

/-!
# Reaction-restricted subnetworks

A reaction-restricted subnetwork keeps the species set fixed and selects a finite set of
reaction channels.  This is the cleanest intrinsic notion of subnetwork for a CRN with
parallel reaction channels, because the selected reaction indices remain distinct.

The main structural facts are monotonicity of the complex set and stoichiometric
subspace/rank.  The module deliberately does not claim monotonicity of deficiency, which
is false in general under arbitrary reaction deletion.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The reaction-restricted network on a finite set of reaction indices. -/
def restrictReactions (N : Network S) (E : Finset N.R) : Network S where
  R := {r : N.R // r ∈ E}
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun r => N.reaction r.1

@[simp] theorem restrictReactions_reaction (N : Network S) (E : Finset N.R)
    (r : (N.restrictReactions E).R) :
    (N.restrictReactions E).reaction r = N.reaction r.1 := rfl

/-- Every complex of a reaction-restricted network is a complex of the parent network. -/
theorem restrictReactions_complexes_subset (N : Network S) (E : Finset N.R) :
    (N.restrictReactions E).complexes ⊆ N.complexes := by
  intro y hy
  rcases Finset.mem_union.mp hy with hy | hy
  · rcases Finset.mem_image.mp hy with ⟨r, _, rfl⟩
    exact N.source_mem_complexes r.1
  · rcases Finset.mem_image.mp hy with ⟨r, _, rfl⟩
    exact N.target_mem_complexes r.1

/-- Reaction vectors are inherited literally from the parent network. -/
@[simp] theorem restrictReactions_reactionVector (N : Network S) (E : Finset N.R)
    (r : (N.restrictReactions E).R) :
    (N.restrictReactions E).reactionVector r = N.reactionVector r.1 := rfl

/-- The stoichiometric subspace of a reaction-restricted network is contained in that
of the parent network. -/
theorem restrictReactions_stoichSubspace_le (N : Network S) (E : Finset N.R) :
    (N.restrictReactions E).stoichSubspace ≤ N.stoichSubspace := by
  apply Submodule.span_le.mpr
  intro v hv
  rcases hv with ⟨r, rfl⟩
  simpa using N.reactionVector_mem_stoichSubspace r.1

/-- Reaction deletion cannot increase stoichiometric rank. -/
theorem restrictReactions_stoichRank_le (N : Network S) (E : Finset N.R) :
    (N.restrictReactions E).stoichRank ≤ N.stoichRank := by
  exact Submodule.finrank_mono (N.restrictReactions_stoichSubspace_le E)

/-- Restriction to the full reaction set recovers the original network up to the
canonical subtype indexing of reactions. -/
def fullRestrictionReactionEquiv (N : Network S) :
    (N.restrictReactions Finset.univ).R ≃ N.R where
  toFun := Subtype.val
  invFun := fun r => ⟨r, Finset.mem_univ r⟩
  left_inv := by intro r; cases r; rfl
  right_inv := by intro r; rfl

/-- Inclusion of one reaction set into another induces inclusion of their stoichiometric
subspaces. -/
theorem restrictReactions_stoichSubspace_mono (N : Network S)
    {E F : Finset N.R} (hEF : E ⊆ F) :
    (N.restrictReactions E).stoichSubspace ≤ (N.restrictReactions F).stoichSubspace := by
  apply Submodule.span_le.mpr
  intro v hv
  rcases hv with ⟨r, rfl⟩
  have hrF : r.1 ∈ F := hEF r.2
  exact Submodule.subset_span ⟨⟨r.1, hrF⟩, rfl⟩

/-- Restrict a set of parent rate constants to selected reaction channels. -/
def RateConstants.restrict {N : Network S} (κ : N.RateConstants) (E : Finset N.R) :
    (N.restrictReactions E).RateConstants where
  k := fun r => κ.k r.1
  positive := fun r => κ.positive r.1

/-- The restricted mass-action vector field is exactly the partial reaction sum over the
selected channels. -/
theorem restrictReactions_massActionVectorField
    (N : Network S) (E : Finset N.R) (κ : N.RateConstants) (x : Concentration S) :
    (N.restrictReactions E).massActionVectorField (κ.restrict E) x =
      fun s => ∑ r ∈ E, N.massActionRate κ r x * N.reactionVector r s := by
  funext s
  -- The restricted network's reaction type is `{r // r ∈ E}`; `Finset.sum_coe_sort`
  -- identifies a sum over that subtype with the sum over `E` itself.
  simp only [massActionVectorField_apply, massActionRate, restrictReactions_reaction,
    RateConstants.restrict, reactionVector_apply]
  exact Finset.sum_coe_sort E
    (fun r => κ.k r * (N.reaction r).source.massActionMonomial x *
      (((N.reaction r).target s : ℝ) - ((N.reaction r).source s : ℝ)))

/-- A reaction partition decomposes the original vector field into the sum of the two
restricted vector fields. -/
theorem massActionVectorField_partition
    (N : Network S) (E : Finset N.R) (κ : N.RateConstants) (x : Concentration S) :
    N.massActionVectorField κ x =
      (N.restrictReactions E).massActionVectorField (κ.restrict E) x +
      (N.restrictReactions (Finset.univ \ E)).massActionVectorField
        (κ.restrict (Finset.univ \ E)) x := by
  funext s
  rw [restrictReactions_massActionVectorField,
    restrictReactions_massActionVectorField]
  simp [massActionVectorField_apply, Finset.sum_sdiff]

end Network
end CRNT
