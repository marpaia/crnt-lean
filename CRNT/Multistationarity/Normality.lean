import CRNT.Multistationarity.Discordance
import CRNT.Open.Augmentation
import CRNT.Graph.WeakReversibility
import CRNT.Graph.Reversibility
import CRNT.Graph.PositiveCirculation

/-!
# Normal reaction networks

Following Feinberg and Shinar, a network with stoichiometric subspace `S` is **normal**
when there are positive species weights `q_s` and positive reaction weights `η_r` for
which

`T σ = Σ_r η_r ⟨source(r), σ⟩_q ν_r`

is nonsingular on the stoichiometric subspace.  Here
`⟨y,σ⟩_q = Σ_s q_s y_s σ_s`.

Normality is a mild structural nondegeneracy condition.  Classical CRNT results include:

* every weakly reversible network is normal;
* if a normal network's fully open extension is concordant, then the original network
  is concordant.

The hard graph/linear-algebra constructions proving those literature theorems are
localized below; the normality operator itself is fully explicit.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Positive species weights for the weighted inner product in normality theory. -/
structure PositiveSpeciesWeights (S : Type) [Fintype S] where
  weight : S → ℝ
  positive : ∀ s, 0 < weight s

/-- Weighted pairing between a complex and a species displacement. -/
def weightedComplexPairing (q : PositiveSpeciesWeights S)
    (y : Complex S) (σ : S → ℝ) : ℝ :=
  ∑ s : S, q.weight s * (y s : ℝ) * σ s

/-- Positive reaction weights entering the normality operator. -/
structure PositiveReactionWeights (N : Network S) where
  weight : N.R → ℝ
  positive : ∀ r, 0 < weight r

/-- Ambient normality operator. Its image lies in the stoichiometric subspace because it
is a linear combination of reaction vectors. -/
noncomputable def normalityOperator (N : Network S)
    (q : PositiveSpeciesWeights S) (η : PositiveReactionWeights N) :
    (S → ℝ) →ₗ[ℝ] (S → ℝ) where
  toFun := fun σ =>
    ∑ r : N.R,
      (η.weight r * weightedComplexPairing q (N.reaction r).source σ) •
        N.reactionVector r
  map_add' := by
    intro σ τ
    ext s
    simp only [weightedComplexPairing, mul_add, Finset.sum_add_distrib, Pi.add_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, reactionVector_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ => by ring
  map_smul' := by
    intro c σ
    ext s
    simp only [weightedComplexPairing, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
      reactionVector_apply, Finset.mul_sum, RingHom.id_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    have h : (∑ i, η.weight r * (q.weight i * ((N.reaction r).source i : ℝ) * (c * σ i)))
        = c * ∑ i, η.weight r * (q.weight i * ((N.reaction r).source i : ℝ) * σ i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h]
    ring

/-- The normality operator preserves the stoichiometric subspace. -/
theorem normalityOperator_mem_stoichSubspace (N : Network S)
    (q : PositiveSpeciesWeights S) (η : PositiveReactionWeights N)
    (σ : S → ℝ) :
    N.normalityOperator q η σ ∈ N.stoichSubspace := by
  unfold normalityOperator
  exact Submodule.sum_mem _ fun r _ =>
    Submodule.smul_mem _ _ (N.reactionVector_mem_stoichSubspace r)

/-- Restriction of the normality operator to the stoichiometric subspace. -/
noncomputable def normalityOperatorOnStoich (N : Network S)
    (q : PositiveSpeciesWeights S) (η : PositiveReactionWeights N) :
    N.stoichSubspace →ₗ[ℝ] N.stoichSubspace :=
  (N.normalityOperator q η).domRestrict N.stoichSubspace |>.codRestrict
    N.stoichSubspace (fun σ => N.normalityOperator_mem_stoichSubspace q η σ)

/-- A certificate of network normality. -/
structure NormalWitness (N : Network S) where
  speciesWeights : PositiveSpeciesWeights S
  reactionWeights : PositiveReactionWeights N
  nonsingular : Function.Injective
    (N.normalityOperatorOnStoich speciesWeights reactionWeights)

/-- **Normal network** in the sense of Feinberg/Shinar. -/
def Normal (N : Network S) : Prop := Nonempty N.NormalWitness

/-- Finite-dimensional normality can equivalently be expressed by a trivial kernel. -/
theorem normalWitness_iff_kernel_bot (N : Network S)
    (q : PositiveSpeciesWeights S) (η : PositiveReactionWeights N) :
    Function.Injective (N.normalityOperatorOnStoich q η) ↔
      LinearMap.ker (N.normalityOperatorOnStoich q η) = ⊥ := by
  exact LinearMap.ker_eq_bot.symm

/-- Normality is invariant under uniformly rescaling all reaction weights. -/
theorem normal_of_scale_reactionWeights (N : Network S)
    (q : PositiveSpeciesWeights S) (η : PositiveReactionWeights N)
    (h : Function.Injective (N.normalityOperatorOnStoich q η))
    {c : ℝ} (hc : 0 < c) : N.Normal := by
  let η' : PositiveReactionWeights N :=
    { weight := fun r => c * η.weight r
      positive := fun r => mul_pos hc (η.positive r) }
  refine ⟨⟨q, η', ?_⟩⟩
  -- New operator is scalar `c` times the old one.
  intro x y hxy
  apply h
  -- the rescaled operator is literally `c •` the original, so cancel the scalar
  have key : ∀ z : N.stoichSubspace,
      N.normalityOperatorOnStoich q η' z = c • N.normalityOperatorOnStoich q η z := by
    intro z
    refine Subtype.ext ?_
    funext s
    show (N.normalityOperator q η' (z : S → ℝ)) s
        = c * (N.normalityOperator q η (z : S → ℝ)) s
    simp only [normalityOperator, LinearMap.coe_mk, AddHom.coe_mk, η',
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring
  rw [key x, key y] at hxy
  -- cancel `c` via `smul_eq_zero` rather than a cancellation lemma, which keeps the
  -- module argument determined
  have h0 : c • (N.normalityOperatorOnStoich q η x - N.normalityOperatorOnStoich q η y) = 0 := by
    rw [smul_sub, hxy, sub_self]
  rcases smul_eq_zero.mp h0 with hc0 | hd
  · exact absurd hc0 hc.ne'
  · exact sub_eq_zero.mp hd


private theorem circulation_potential_sum_zero
    (N : Network S) {α : N.R → ℝ} (hinc : N.incidenceMap α = 0)
    (φ : N.ComplexIdx → ℝ) :
    ∑ r : N.R, α r * (φ (N.targetIdx r) - φ (N.sourceIdx r)) = 0 := by
  have hM : N.incidenceMatrix.mulVec α = 0 := by
    have h := hinc
    rw [N.incidenceMap_eq_mulVecLin] at h
    exact h
  have htrans : (fun r : N.R => φ (N.targetIdx r) - φ (N.sourceIdx r)) =
      Matrix.vecMul φ N.incidenceMatrix := by
    funext r
    simpa [Matrix.mulVecLin_apply] using (N.incidenceTranspose_apply φ r).symm
  change α ⬝ᵥ (fun r : N.R => φ (N.targetIdx r) - φ (N.sourceIdx r)) = 0
  rw [htrans]
  calc
    α ⬝ᵥ Matrix.vecMul φ N.incidenceMatrix =
        Matrix.vecMul φ N.incidenceMatrix ⬝ᵥ α := dotProduct_comm _ _
    _ = φ ⬝ᵥ N.incidenceMatrix.mulVec α := by
      rw [Matrix.dotProduct_mulVec]
    _ = 0 := by rw [hM]; simp

/-- **Classical theorem:** every weakly reversible network is normal. -/
theorem normal_of_weaklyReversible (N : Network S) (hwr : N.WeaklyReversible) :
    N.Normal := by
  rcases N.exists_positiveGraphCirculation_of_weaklyReversible hwr with ⟨α, hαpos, hinc⟩
  let q : PositiveSpeciesWeights S :=
    { weight := fun _ => 1
      positive := fun _ => one_pos }
  let η : PositiveReactionWeights N :=
    { weight := α
      positive := hαpos }
  refine ⟨⟨q, η, ?_⟩⟩
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm
  · intro v hv
    rw [Submodule.mem_bot]
    let σ : S → ℝ := v.1
    let z : N.ComplexIdx → ℝ := fun c => ∑ s : S, (c.1 s : ℝ) * σ s
    let d : N.R → ℝ := fun r => z (N.targetIdx r) - z (N.sourceIdx r)
    have hT : N.normalityOperator q η σ = 0 := by
      have hh := congrArg Subtype.val hv
      unfold normalityOperatorOnStoich at hh
      change N.normalityOperator q η (v : S → ℝ) = 0 at hh
      simpa [σ] using hh
    have hpair_source : ∀ r : N.R,
        weightedComplexPairing q (N.reaction r).source σ = z (N.sourceIdx r) := by
      intro r
      simp [weightedComplexPairing, q, z, sourceIdx]
    have hpair_rv : ∀ r : N.R,
        (∑ s : S, σ s * N.reactionVector r s) = d r := by
      intro r
      simp only [d, z, targetIdx, sourceIdx, reactionVector_apply]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro s _
      ring
    have hTop : ∀ s : S,
        (N.normalityOperator q η σ) s =
          ∑ r : N.R, (α r * z (N.sourceIdx r)) * N.reactionVector r s := by
      intro s
      simp only [normalityOperator, LinearMap.coe_mk, AddHom.coe_mk,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, η]
      apply Finset.sum_congr rfl
      intro r _
      rw [hpair_source r]
    have hE : ∑ r : N.R, α r * z (N.sourceIdx r) * d r = 0 := by
      have hzero : ∑ s : S, σ s * (N.normalityOperator q η σ) s = 0 := by
        rw [hT]
        simp
      calc
        ∑ r : N.R, α r * z (N.sourceIdx r) * d r
            = ∑ r : N.R, (α r * z (N.sourceIdx r)) *
                (∑ s : S, σ s * N.reactionVector r s) := by
                  apply Finset.sum_congr rfl
                  intro r _
                  rw [hpair_rv r]
        _ = ∑ r : N.R, ∑ s : S, σ s *
              ((α r * z (N.sourceIdx r)) * N.reactionVector r s) := by
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          ring
        _ = ∑ s : S, ∑ r : N.R, σ s *
              ((α r * z (N.sourceIdx r)) * N.reactionVector r s) := by
          rw [Finset.sum_comm]
        _ = ∑ s : S, σ s * (N.normalityOperator q η σ) s := by
          apply Finset.sum_congr rfl
          intro s _
          rw [hTop s, Finset.mul_sum]
        _ = 0 := hzero
    have hpot : ∑ r : N.R, α r *
        ((z (N.targetIdx r))^2 - (z (N.sourceIdx r))^2) = 0 := by
      exact circulation_potential_sum_zero N hinc (fun c => (z c)^2)
    have hsquares : ∑ r : N.R, α r * (d r)^2 = 0 := by
      calc
        ∑ r : N.R, α r * (d r)^2
            = (∑ r : N.R, α r *
                ((z (N.targetIdx r))^2 - (z (N.sourceIdx r))^2)) -
              2 * (∑ r : N.R, α r * z (N.sourceIdx r) * d r) := by
                rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl
                intro r _
                dsimp [d]
                ring
        _ = 0 := by rw [hpot, hE]; ring
    have hd0 : ∀ r : N.R, d r = 0 := by
      intro r
      have hnonneg : ∀ q ∈ (Finset.univ : Finset N.R),
          0 ≤ α q * (d q)^2 := by
        intro q _
        exact mul_nonneg (hαpos q).le (sq_nonneg _)
      have hterm :=
        (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hsquares r (Finset.mem_univ r)
      have hαne : α r ≠ 0 := (hαpos r).ne'
      have hsquare : (d r)^2 = 0 := (mul_eq_zero.mp hterm).resolve_left hαne
      exact sq_eq_zero_iff.mp hsquare
    let L : (S → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun τ => ∑ s : S, σ s * τ s
        map_add' := by intro a b; simp [mul_add, Finset.sum_add_distrib]
        map_smul' := by
          intro c a
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          ring }
    have hrv : ∀ r : N.R, L (N.reactionVector r) = 0 := by
      intro r
      change ∑ s : S, σ s * N.reactionVector r s = 0
      rw [hpair_rv r, hd0 r]
    have hle : N.stoichSubspace ≤ LinearMap.ker L := by
      rw [stoichSubspace]
      apply Submodule.span_le.2
      rintro _ ⟨r, rfl⟩
      exact LinearMap.mem_ker.mpr (hrv r)
    have hσmem : σ ∈ N.stoichSubspace := v.property
    have hσdot : L σ = 0 := LinearMap.mem_ker.mp (hle hσmem)
    have hsumsq : ∑ s : S, (σ s)^2 = 0 := by
      simpa [L, pow_two] using hσdot
    have hσzero : σ = 0 := by
      funext s
      have hnonneg : ∀ i ∈ (Finset.univ : Finset S), 0 ≤ (σ i)^2 :=
        fun i _ => sq_nonneg _
      have hs :=
        (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hsumsq s (Finset.mem_univ s)
      exact sq_eq_zero_iff.mp hs
    apply Subtype.ext
    simpa [σ] using hσzero
  · exact bot_le

/-- Reversible networks are normal. -/
theorem normal_of_reversible (N : Network S) (hrev : N.Reversible) : N.Normal :=
  N.normal_of_weaklyReversible hrev.weaklyReversible

end Network
end CRNT
