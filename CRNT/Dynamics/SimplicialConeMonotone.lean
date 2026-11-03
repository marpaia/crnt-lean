import CRNT.Dynamics.MonotoneComparison

/-!
# Monotonicity with respect to simplicial cones

For an invertible linear map `M`, the simplicial cone `M(ℝ^S_{≥0})` orders vectors by
`x ≤_M y ↔ M⁻¹ x ≤ M⁻¹ y` (`ConeLE`). If `f` is Lipschitz on `K`, `K` is closed under the cone
maximum, and the conjugated field `z ↦ M⁻¹ f(M z)` satisfies the Kamke condition on `M⁻¹ K`
(cooperativity with respect to the cone), then solutions of `ẋ = f(x)` preserve `≤_M`
(`simplicialCone_comparison`). The orthant case is `M = id`.
-/

open Set
open scoped NNReal

namespace CRNT
namespace Monotone

variable {S : Type} [Fintype S]

/-- The order of the simplicial cone `M(ℝ^S_{≥0})`. -/
def ConeLE (M : (S → ℝ) ≃L[ℝ] (S → ℝ)) (x y : S → ℝ) : Prop := M.symm x ≤ M.symm y

/-- **Comparison principle for simplicial cones.** -/
theorem simplicialCone_comparison (M : (S → ℝ) ≃L[ℝ] (S → ℝ)) {f : (S → ℝ) → (S → ℝ)}
    {K : Set (S → ℝ)} {L : ℝ≥0} (hlip : LipschitzOnWith L f K)
    (hsup : ∀ a ∈ K, ∀ b ∈ K, M (M.symm a ⊔ M.symm b) ∈ K)
    (hk : KamkeOn (fun z => M.symm (f (M z))) (M.symm '' K)) {T : ℝ} {x y : ℝ → (S → ℝ)}
    (hx : ∀ t ∈ Icc 0 T, HasDerivWithinAt x (f (x t)) (Icc 0 T) t)
    (hy : ∀ t ∈ Icc 0 T, HasDerivWithinAt y (f (y t)) (Icc 0 T) t)
    (hxK : ∀ t ∈ Icc 0 T, x t ∈ K) (hyK : ∀ t ∈ Icc 0 T, y t ∈ K)
    (h0 : ConeLE M (x 0) (y 0)) : ∀ t ∈ Icc 0 T, ConeLE M (x t) (y t) := by
  have hmaps : MapsTo (fun z => M z) (M.symm '' K) K := by
    rintro _ ⟨a, ha, rfl⟩
    simpa using ha
  have hlip' : LipschitzOnWith (‖(M.symm : (S → ℝ) →L[ℝ] (S → ℝ))‖₊ * (L * ‖(M : (S → ℝ) →L[ℝ] (S → ℝ))‖₊))
      (fun z => M.symm (f (M z))) (M.symm '' K) :=
    (M.symm : (S → ℝ) →L[ℝ] (S → ℝ)).lipschitz.comp_lipschitzOnWith
      (hlip.comp ((M : (S → ℝ) →L[ℝ] (S → ℝ)).lipschitz.lipschitzOnWith) hmaps)
  have hsup' : ∀ a ∈ M.symm '' K, ∀ b ∈ M.symm '' K, a ⊔ b ∈ M.symm '' K := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact ⟨M (M.symm a ⊔ M.symm b), hsup a ha b hb, by simp⟩
  have hder : ∀ {z : ℝ → (S → ℝ)}, (∀ t ∈ Icc 0 T, HasDerivWithinAt z (f (z t)) (Icc 0 T) t) →
      ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun t => M.symm (z t))
        ((fun w => M.symm (f (M w))) (M.symm (z t))) (Icc 0 T) t := by
    intro z hz t ht
    have := (M.symm : (S → ℝ) →L[ℝ] (S → ℝ)).hasFDerivAt.comp_hasDerivWithinAt t (hz t ht)
    have h2 : (fun w => M.symm (f (M w))) (M.symm (z t)) = M.symm (f (z t)) := by simp
    rw [h2]
    exact this
  intro t ht
  exact kamke_comparison hlip' hsup' hk (hder hx) (hder hy)
    (fun t ht => ⟨x t, hxK t ht, rfl⟩) (fun t ht => ⟨y t, hyK t ht, rfl⟩) h0 t ht

end Monotone
end CRNT
