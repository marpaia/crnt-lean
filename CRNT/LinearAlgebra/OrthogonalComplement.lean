import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# The dot-product orthogonal complement on `ι → ℝ`

`orthSum S` is the orthogonal complement of `S ⊆ (ι → ℝ)` with respect to the standard
dot product `⟨w, s⟩ = ∑ i, wᵢ sᵢ`, expressed directly as a sum so it matches the
orthogonality conditions used in Birch's theorem. The double-complement identity
`orthSum (orthSum S) = S` is obtained by identifying `ι → ℝ` with `EuclideanSpace ℝ ι`
(the same module, with the dot product as its inner product) and transporting Mathlib's
`Submodule.orthogonal_orthogonal`.
-/

namespace CRNT

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The orthogonal complement of `S` for the standard dot product on `ι → ℝ`: the vectors
`w` with `∑ i, wᵢ sᵢ = 0` for every `s ∈ S`. -/
def orthSum (S : Submodule ℝ (ι → ℝ)) : Submodule ℝ (ι → ℝ) where
  carrier := {w | ∀ s ∈ S, ∑ i, w i * s i = 0}
  add_mem' {a b} ha hb := by
    intro s hs
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, ha s hs, hb s hs, add_zero]
  zero_mem' := by intro s _; simp
  smul_mem' r a ha := by
    intro s hs
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, ha s hs, mul_zero]

@[simp] lemma mem_orthSum {S : Submodule ℝ (ι → ℝ)} {w : ι → ℝ} :
    w ∈ orthSum S ↔ ∀ s ∈ S, ∑ i, w i * s i = 0 := Iff.rfl

/-- Orthogonality to a spanning set extends to the whole span: if `w` is orthogonal to
every generator, it lies in `orthSum (span G)`. -/
theorem mem_orthSum_span {G : Set (ι → ℝ)} {w : ι → ℝ}
    (h : ∀ g ∈ G, ∑ i, w i * g i = 0) : w ∈ orthSum (Submodule.span ℝ G) := by
  rw [mem_orthSum]
  intro s hs
  induction hs using Submodule.span_induction with
  | mem g hg => exact h g hg
  | zero => simp
  | add x y _ _ hx hy =>
    have : ∑ i, w i * (x + y) i = (∑ i, w i * x i) + ∑ i, w i * y i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply]; ring
    rw [this, hx, hy, add_zero]
  | smul r x _ hx =>
    have : ∑ i, w i * (r • x) i = r * ∑ i, w i * x i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [Pi.smul_apply, smul_eq_mul]; ring
    rw [this, hx, mul_zero]

/-- The standard linear identification of `ι → ℝ` with `EuclideanSpace ℝ ι` (the identity
on coordinates), used to borrow Mathlib's inner-product orthogonal-complement theory. -/
noncomputable def toEuclid : (ι → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ ι :=
  (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm

omit [Fintype ι] in
@[simp] lemma toEuclid_apply (w : ι → ℝ) (i : ι) : toEuclid w i = w i := rfl

/-- The Euclidean inner product transported back to `ι → ℝ` is the dot product. -/
lemma inner_toEuclid (x y : ι → ℝ) :
    @inner ℝ (EuclideanSpace ℝ ι) _ (toEuclid x) (toEuclid y) = ∑ i, x i * y i := by
  rw [PiLp.inner_apply]
  simp only [toEuclid_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- `orthSum` is Mathlib's inner-product orthogonal complement, transported across
`toEuclid`. -/
lemma orthSum_eq (S : Submodule ℝ (ι → ℝ)) :
    orthSum S = (S.map toEuclid.toLinearMap).orthogonal.comap toEuclid.toLinearMap := by
  ext w
  simp only [mem_orthSum, Submodule.mem_comap, Submodule.mem_orthogonal',
    Submodule.mem_map, LinearEquiv.coe_toLinearMap, forall_exists_index, and_imp]
  constructor
  · intro h u s hs hsu
    subst hsu
    rw [inner_toEuclid]; exact h s hs
  · intro h s hs
    rw [← inner_toEuclid]; exact h (toEuclid s) s hs rfl

/-- **The double dot-product orthogonal complement returns the original subspace.**
`(Sᗮ)ᗮ = S` in finite dimensions, with no general-position hypothesis. -/
theorem orthSum_orthSum (S : Submodule ℝ (ι → ℝ)) : orthSum (orthSum S) = S := by
  rw [orthSum_eq (orthSum S)]
  have h1 : (orthSum S).map toEuclid.toLinearMap
      = (S.map toEuclid.toLinearMap).orthogonal := by
    rw [orthSum_eq S, Submodule.map_comap_eq_of_surjective toEuclid.surjective]
  rw [h1, Submodule.orthogonal_orthogonal,
    Submodule.comap_map_eq_of_injective toEuclid.injective]

/-- **Orthogonal decomposition of a subspace relative to a smaller one.**  For `U ≤ V`,
`V` splits as `U` together with the part of `V` orthogonal to `U`.  This is the dot-product
form of Mathlib's `Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection`, transported
across `toEuclid`; in finite dimensions the projection hypothesis is automatic. -/
theorem sup_inf_orthSum_of_le {U V : Submodule ℝ (ι → ℝ)} (h : U ≤ V) :
    U ⊔ (V ⊓ orthSum U) = V := by
  classical
  have hinj : Function.Injective (toEuclid.toLinearMap : (ι → ℝ) →ₗ[ℝ] _) :=
    toEuclid.injective
  have hmapU : (orthSum U).map toEuclid.toLinearMap
      = (U.map toEuclid.toLinearMap).orthogonal := by
    rw [orthSum_eq U, Submodule.map_comap_eq_of_surjective toEuclid.surjective]
  -- `comap` does not distribute over `⊔`, so compare the images instead and use that
  -- `Submodule.map` along an injective map is injective.
  refine Submodule.map_injective_of_injective hinj ?_
  rw [Submodule.map_sup, Submodule.map_inf _ hinj, hmapU, inf_comm]
  exact Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection (Submodule.map_mono h)

/-- A subspace meets its own dot-product complement only at zero: if `w` is in both then
`∑ i, wᵢ² = 0`, and a sum of squares vanishes only when every term does. -/
theorem inf_orthSum_eq_bot (U : Submodule ℝ (ι → ℝ)) : U ⊓ orthSum U = ⊥ := by
  classical
  refine le_antisymm ?_ bot_le
  intro w hw
  obtain ⟨hU, hO⟩ := hw
  have h0 : ∑ i, w i * w i = 0 := hO w hU
  have hnn : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ w i * w i :=
    fun i _ => mul_self_nonneg _
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0
  have : w = 0 := by
    funext i
    exact mul_self_eq_zero.mp (hz i (Finset.mem_univ i))
  simpa [this] using Submodule.zero_mem (⊥ : Submodule ℝ (ι → ℝ))

/-- **Dimension form of the orthogonal decomposition.**  For `U ≤ V`, the dimension of `V`
splits as `dim U` plus the dimension of the part of `V` orthogonal to `U`. -/
theorem finrank_add_finrank_inf_orthSum_of_le {U V : Submodule ℝ (ι → ℝ)} (h : U ≤ V) :
    Module.finrank ℝ U + Module.finrank ℝ (V ⊓ orthSum U : Submodule ℝ (ι → ℝ))
      = Module.finrank ℝ V := by
  classical
  have hsup : U ⊔ (V ⊓ orthSum U) = V := sup_inf_orthSum_of_le h
  have hinf : U ⊓ (V ⊓ orthSum U) = ⊥ := by
    rw [← inf_assoc, inf_eq_left.mpr h, inf_orthSum_eq_bot]
  have key := Submodule.finrank_sup_add_finrank_inf_eq U (V ⊓ orthSum U)
  rw [hsup, hinf] at key
  simpa using key.symm

/-- **Rank–nullity for the dot-product complement.** The complement `Sᗮ` has dimension
`card ι − dim S`: the conservation-law space (`orthSum` of the stoichiometric subspace) is
the cokernel of the stoichiometric map, whose dimension is the number of species minus the
stoichiometric rank. Obtained from Mathlib's inner-product `finrank_add_finrank_orthogonal`
transported across `toEuclid`. -/
theorem finrank_orthSum (S : Submodule ℝ (ι → ℝ)) :
    Module.finrank ℝ (orthSum S) = Fintype.card ι - Module.finrank ℝ S := by
  have hmap : (orthSum S).map toEuclid.toLinearMap
      = (S.map toEuclid.toLinearMap).orthogonal := by
    rw [orthSum_eq S, Submodule.map_comap_eq_of_surjective toEuclid.surjective]
  have h1 := LinearEquiv.finrank_map_eq toEuclid (orthSum S)
  rw [hmap] at h1
  have hW : Module.finrank ℝ (S.map toEuclid.toLinearMap) = Module.finrank ℝ S :=
    LinearEquiv.finrank_map_eq toEuclid S
  have hperp : Module.finrank ℝ (S.map toEuclid.toLinearMap)
      + Module.finrank ℝ ((S.map toEuclid.toLinearMap).orthogonal) = Fintype.card ι := by
    rw [Submodule.finrank_add_finrank_orthogonal, finrank_euclideanSpace]
  omega

end CRNT
