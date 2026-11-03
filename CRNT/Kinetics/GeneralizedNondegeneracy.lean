import CRNT.Kinetics.GeneralizedConditions

/-!
# Transversality and nondegeneracy for generalized toric intersections

For positive `x`, the tangent space to the multiplicative toric manifold
`x * exp(Tᗮ)` at `x` is `diag(x)(Tᗮ)`.  Its intersection with the stoichiometric
subspace `S` measures degeneracy of the affine/toric intersection.

The Müller--Regensburger sign condition is stronger than mere transversality: because
positive diagonal scaling preserves coordinate signs, sign compatibility immediately
forces this tangent intersection to be trivial at every positive point.
-/

namespace CRNT

variable {ι : Type*} [Fintype ι]

/-- Positive diagonal coordinate scaling. -/
def diagonalScale (x : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun v := fun i => x i * v i
  map_add' v w := by funext i; simp [mul_add]
  map_smul' a v := by funext i; simp [mul_assoc, mul_left_comm]

@[simp] theorem diagonalScale_apply (x v : ι → ℝ) (i : ι) :
    diagonalScale x v i = x i * v i := rfl

/-- Tangent space to the generalized toric leaf with kinetic-order subspace `T`. -/
def toricTangentSubspace (T : Submodule ℝ (ι → ℝ)) (x : ι → ℝ) :
    Submodule ℝ (ι → ℝ) :=
  (orthSum T).map (diagonalScale x)

/-- Nondegenerate/transverse affine--toric intersection at `x`. -/
def GeneralizedToricNondegenerateAt
    (S T : Submodule ℝ (ι → ℝ)) (x : ι → ℝ) : Prop :=
  S ⊓ toricTangentSubspace T x = ⊥

/-- Positive coordinate scaling preserves strict sign. -/
theorem sameSign_diagonalScale_of_positive {x v : ι → ℝ}
    (hx : ∀ i, 0 < x i) : SameSign (diagonalScale x v) v := by
  intro i
  simp only [diagonalScale_apply]
  constructor
  · constructor
    · intro h
      exact pos_of_mul_pos_right h (hx i).le
    · intro hv
      exact mul_pos (hx i) hv
  · constructor
    · intro h
      have : v i < 0 := by
        by_contra hn
        have hv0 : 0 ≤ v i := le_of_not_gt hn
        exact (not_lt_of_ge (mul_nonneg (hx i).le hv0)) h
      exact this
    · intro hv
      exact mul_neg_of_pos_of_neg (hx i) hv

/-- A vector in a positively scaled subspace can be represented by a same-sign preimage. -/
theorem exists_sameSign_preimage_toricTangent
    {T : Submodule ℝ (ι → ℝ)} {x u : ι → ℝ}
    (hx : ∀ i, 0 < x i) (hu : u ∈ toricTangentSubspace T x) :
    ∃ v ∈ orthSum T, diagonalScale x v = u ∧ SameSign u v := by
  rcases hu with ⟨v, hv, rfl⟩
  exact ⟨v, hv, rfl, sameSign_diagonalScale_of_positive hx⟩

/-- **Sign compatibility implies transversality at every positive point.** -/
theorem generalizedToricNondegenerate_of_signCompatible
    (S T : Submodule ℝ (ι → ℝ))
    (hST : SignCompatible S (orthSum T))
    {x : ι → ℝ} (hx : ∀ i, 0 < x i) :
    GeneralizedToricNondegenerateAt S T x := by
  rw [GeneralizedToricNondegenerateAt, Submodule.eq_bot_iff]
  intro u hu
  rcases hu with ⟨huS, huT⟩
  rcases exists_sameSign_preimage_toricTangent hx huT with ⟨v, hv, hscale, hsign⟩
  have hz := hST u huS v hv hsign
  simpa [hz]

/-- Hence the generalized uniqueness condition implies nondegeneracy everywhere in the
positive orthant. -/
theorem generalizedToricNondegenerate_of_uniquenessCondition
    (S T : Submodule ℝ (ι → ℝ))
    (h : GeneralizedUniquenessCondition S T)
    {x : ι → ℝ} (hx : ∀ i, 0 < x i) :
    GeneralizedToricNondegenerateAt S T x :=
  generalizedToricNondegenerate_of_signCompatible S T h hx

/-- At a nondegenerate point the two tangent subspaces have dimension-additive sum. -/
theorem finrank_sup_toricTangent_of_nondegenerate
    (S T : Submodule ℝ (ι → ℝ)) {x : ι → ℝ}
    (h : GeneralizedToricNondegenerateAt S T x) :
    Module.finrank ℝ ↥(S ⊔ toricTangentSubspace T x) =
      Module.finrank ℝ S + Module.finrank ℝ (toricTangentSubspace T x) := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq S (toricTangentSubspace T x)
  rw [h] at hdim
  simpa using hdim

/-- If the tangent dimensions are complementary, sign compatibility gives a direct-sum
splitting of the whole ambient species space. -/
theorem generalizedToricTangent_directSum_of_complementary
    (S T : Submodule ℝ (ι → ℝ))
    (hST : SignCompatible S (orthSum T))
    {x : ι → ℝ} (hx : ∀ i, 0 < x i)
    (hdim : Module.finrank ℝ S + Module.finrank ℝ (orthSum T) = Fintype.card ι) :
    S ⊔ toricTangentSubspace T x = ⊤ := by
  have hnd := generalizedToricNondegenerate_of_signCompatible S T hST hx
  have hscaleRank : Module.finrank ℝ (toricTangentSubspace T x) =
      Module.finrank ℝ (orthSum T) := by
    rw [toricTangentSubspace, ← LinearMap.range_domRestrict]
    apply LinearMap.finrank_range_of_inj
    intro u v huv
    apply Subtype.ext
    funext i
    have hi := congrFun huv i
    simp only [LinearMap.domRestrict_apply, diagonalScale_apply] at hi
    exact (mul_left_cancel₀ (ne_of_gt (hx i)) hi)
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_sup_toricTangent_of_nondegenerate S T hnd, hscaleRank, hdim]
  simp

end CRNT
