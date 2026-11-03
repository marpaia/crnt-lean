import CRNT.Flux.PSemiflow
import CRNT.LinearAlgebra.OrthogonalComplement
import CRNT.Equilibria.CompatibilityClass

/-!
# Conservation-law and compatibility-class dimensions

For a CRN with `m` species and stoichiometric rank `s`, the linear conservation-law
space is `Sᗮ` and has dimension `m-s`.  Stoichiometric compatibility classes are affine
copies of `S` and therefore have dimension `s`.  These elementary dimension facts are
used implicitly throughout CRNT; this file makes them explicit reusable theorems.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Linear conservation-law space. -/
noncomputable def conservationLawSpace (N : Network S) : Submodule ℝ (S → ℝ) :=
  orthSum N.stoichSubspace

@[simp] theorem mem_conservationLawSpace_iff (N : Network S) (w : S → ℝ) :
    w ∈ N.conservationLawSpace ↔ N.IsPInvariant w := Iff.rfl

/-- Number of independent linear conservation laws. -/
theorem finrank_conservationLawSpace (N : Network S) :
    Module.finrank ℝ N.conservationLawSpace = Fintype.card S - N.stoichRank := by
  -- `finrank_orthSum` in `CRNT/LinearAlgebra/OrthogonalComplement.lean` already gives this;
  -- the `sorry` here was reaching for a result the tree already had.
  exact finrank_orthSum N.stoichSubspace

/-- Rank-nullity form `s + c = m`. -/
theorem stoichRank_add_numConservationLaws (N : Network S) :
    N.stoichRank + Module.finrank ℝ N.conservationLawSpace = Fintype.card S := by
  rw [N.finrank_conservationLawSpace]
  -- `omega` needs to know the rank does not exceed the number of species
  have h := N.stoichRank_le_card
  omega

/-- Translation space of every compatibility class is exactly the stoichiometric
subspace. -/
theorem compatibilityClass_eq_translate (N : Network S) (x₀ : Concentration S) :
    N.compatibilityClass x₀ = {x | ∃ v ∈ N.stoichSubspace, x = x₀ + v} := by
  ext x
  constructor
  · intro hx
    refine ⟨x - x₀, hx, ?_⟩
    ext s; simp [sub_add_cancel]
  · rintro ⟨v, hv, rfl⟩
    have h : x₀ + v - x₀ = v := by ext s; simp
    simpa [compatibilityClass, StoichCompatible, h] using hv

/-- Affine dimension of a stoichiometric compatibility class.  The theorem is stated in
terms of its translation subspace, avoiding dependence on a particular affine-space API. -/
theorem compatibilityClass_translation_finrank (N : Network S) :
    Module.finrank ℝ N.stoichSubspace = N.stoichRank := rfl

/-- Full stoichiometric rank means there are no nontrivial linear conservation laws. -/
theorem stoichRank_eq_card_iff_conservationLawSpace_eq_bot (N : Network S) :
    N.stoichRank = Fintype.card S ↔ N.conservationLawSpace = ⊥ := by
  -- Both sides are statements about `finrank` of the conservation space, which is
  -- `card S - stoichRank` by `finrank_conservationLawSpace`.
  rw [← Submodule.finrank_eq_zero (R := ℝ) (M := (S → ℝ)),
    N.finrank_conservationLawSpace]
  have h := N.stoichRank_le_card
  omega

/-- Zero stoichiometric rank means every species linear functional is conserved. -/
theorem stoichRank_zero_iff_conservationLawSpace_eq_top (N : Network S) :
    N.stoichRank = 0 ↔ N.conservationLawSpace = ⊤ := by
  have hcard : Module.finrank ℝ (S → ℝ) = Fintype.card S :=
    Module.finrank_fintype_fun_eq_card ℝ
  have hle := N.stoichRank_le_card
  constructor
  · intro h
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [N.finrank_conservationLawSpace, hcard, h]
    omega
  · intro h
    have hr := N.finrank_conservationLawSpace
    rw [h, finrank_top, hcard] at hr
    omega

end Network
end CRNT
