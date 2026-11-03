import CRNT.Multistationarity.SourceWeightPairing
import CRNT.Multistationarity.WeakNormality

/-!
# Fully open concordance as a spectral condition on weak-normality operators

`CRNT.Multistationarity.SourceWeightPairing` characterizes discordance of the fully open
extension by a positive-diagonal eigenrelation for raw source-weight families.  This module
transports that characterization to the project's `SourceInfluenceFamily` /
`weakNormalityOperator` API and records the resulting spectral consequences.

Main results.

* `discordant_fullyOpen_iff_influence`: `N.fullyOpen` is discordant iff some
  `SourceInfluenceFamily` has `T̄_P σ = d ⊙ σ` for a nonzero `σ` and a strictly positive
  diagonal `d`.
* `discordant_fullyOpen_of_positive_eigenvalue_onStoich`: a positive real eigenvalue of the
  restricted operator `T̄_P|_S` already forces fully open discordance.
* `weakNormality_eigenvalue_neg_of_concordant_fullyOpen`: if `N.fullyOpen` is concordant and
  `P` is a weak-normality witness, then every real eigenvalue of `T̄_P|_S` is strictly
  negative.

The third statement is the sharpest consequence currently available on the concordance side
of the Shinar--Feinberg descent theorem: fully open concordance removes the entire
nonnegative real spectrum of every weak-normality operator.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A `SourceInfluenceFamily` is a raw source-weight family. -/
theorem isSourceWeightFamily_of_influences (N : Network S) (P : N.SourceInfluenceFamily) :
    N.IsSourceWeightFamily (fun r s => (P.influence r).vec s) :=
  fun r => ⟨(P.influence r).nonneg, (P.influence r).pos_iff_source⟩

/-- A raw source-weight family is a `SourceInfluenceFamily`. -/
noncomputable def sourceInfluenceFamilyOfWeights (N : Network S) {p : N.R → S → ℝ}
    (hp : N.IsSourceWeightFamily p) : N.SourceInfluenceFamily where
  influence := fun r =>
    { vec := p r
      nonneg := (hp r).1
      pos_iff_source := (hp r).2 }

@[simp] theorem sourceInfluenceFamilyOfWeights_vec (N : Network S) {p : N.R → S → ℝ}
    (hp : N.IsSourceWeightFamily p) (r : N.R) :
    ((N.sourceInfluenceFamilyOfWeights hp).influence r).vec = p r := rfl

/-- The raw operator agrees with the `SourceInfluenceFamily` weak-normality operator. -/
theorem rawWeakNormalityOperator_eq (N : Network S) (P : N.SourceInfluenceFamily)
    (σ : S → ℝ) :
    N.rawWeakNormalityOperator (fun r s => (P.influence r).vec s) σ
      = N.weakNormalityOperator P σ := by
  rfl

/-- **Fully open discordance as a positive-diagonal eigenvalue problem**, in terms of the
project's source-influence API. -/
theorem discordant_fullyOpen_iff_influence (N : Network S) :
    N.fullyOpen.Discordant ↔
      ∃ (P : N.SourceInfluenceFamily) (σ d : S → ℝ),
        σ ≠ 0 ∧ (∀ s : S, 0 < d s) ∧
          N.weakNormalityOperator P σ = fun s => d s * σ s := by
  rw [N.discordant_fullyOpen_iff]
  constructor
  · rintro ⟨p, σ, d, hp, hσ, hd, heq⟩
    refine ⟨N.sourceInfluenceFamilyOfWeights hp, σ, d, hσ, hd, ?_⟩
    rw [← N.rawWeakNormalityOperator_eq (N.sourceInfluenceFamilyOfWeights hp) σ]
    exact heq
  · rintro ⟨P, σ, d, hσ, hd, heq⟩
    refine ⟨fun r s => (P.influence r).vec s, σ, d,
      N.isSourceWeightFamily_of_influences P, hσ, hd, ?_⟩
    rw [N.rawWeakNormalityOperator_eq P σ]
    exact heq

/-- Concordance of the fully open extension forbids positive-diagonal eigenrelations for
every source-influence family. -/
theorem concordant_fullyOpen_iff_influence (N : Network S) :
    N.fullyOpen.Concordant ↔
      ∀ (P : N.SourceInfluenceFamily) (σ d : S → ℝ),
        σ ≠ 0 → (∀ s : S, 0 < d s) →
          N.weakNormalityOperator P σ ≠ fun s => d s * σ s := by
  constructor
  · intro hcon P σ d hσ hd heq
    exact (N.discordant_fullyOpen_iff_influence.mpr ⟨P, σ, d, hσ, hd, heq⟩) hcon
  · intro hall
    by_contra hcon
    obtain ⟨P, σ, d, hσ, hd, heq⟩ := N.discordant_fullyOpen_iff_influence.mp hcon
    exact hall P σ d hσ hd heq

/-- Ambient positive real eigenvalues force fully open discordance. -/
theorem discordant_fullyOpen_of_positive_eigenvalue_influence (N : Network S)
    (P : N.SourceInfluenceFamily) {σ : S → ℝ} (hσ : σ ≠ 0) {μ : ℝ} (hμ : 0 < μ)
    (heq : N.weakNormalityOperator P σ = μ • σ) :
    N.fullyOpen.Discordant := by
  refine N.discordant_fullyOpen_iff_influence.mpr ⟨P, σ, fun _ => μ, hσ, fun _ => hμ, ?_⟩
  rw [heq]
  funext s
  simp [Pi.smul_apply]

/-- The restricted operator's value is the ambient operator's value. -/
theorem weakNormalityOperatorOnStoich_coe (N : Network S) (P : N.SourceInfluenceFamily)
    (σ : N.stoichSubspace) :
    ((N.weakNormalityOperatorOnStoich P) σ : S → ℝ)
      = N.weakNormalityOperator P (σ : S → ℝ) := by
  rfl

/-- **A positive real eigenvalue of the restricted weak-normality operator forces fully open
discordance.** -/
theorem discordant_fullyOpen_of_positive_eigenvalue_onStoich (N : Network S)
    (P : N.SourceInfluenceFamily) {σ : N.stoichSubspace} (hσ : σ ≠ 0)
    {μ : ℝ} (hμ : 0 < μ)
    (heq : (N.weakNormalityOperatorOnStoich P) σ = μ • σ) :
    N.fullyOpen.Discordant := by
  have hval : N.weakNormalityOperator P (σ : S → ℝ) = μ • (σ : S → ℝ) := by
    rw [← N.weakNormalityOperatorOnStoich_coe P σ, heq]
    exact congrArg _ rfl
  have hσ' : (σ : S → ℝ) ≠ 0 := fun h => hσ (Submodule.coe_eq_zero.mp h)
  exact N.discordant_fullyOpen_of_positive_eigenvalue_influence P hσ' hμ hval

/-- **Spectral consequence of fully open concordance.**  No weak-normality operator of `N`
has a nonnegative real eigenvalue on the stoichiometric subspace, once the operator is
nonsingular there (which is exactly what a weak-normality witness supplies). -/
theorem weakNormality_eigenvalue_neg_of_concordant_fullyOpen (N : Network S)
    (hcon : N.fullyOpen.Concordant) (W : N.WeakNormalWitness)
    {σ : N.stoichSubspace} (hσ : σ ≠ 0) {μ : ℝ}
    (heq : (N.weakNormalityOperatorOnStoich W.influences) σ = μ • σ) :
    μ < 0 := by
  rcases lt_trichotomy μ 0 with hneg | hzero | hpos
  · exact hneg
  · exfalso
    subst hzero
    have hker : (N.weakNormalityOperatorOnStoich W.influences) σ = 0 := by
      rw [heq, zero_smul]
    have : σ = 0 := by
      have h0 : (N.weakNormalityOperatorOnStoich W.influences) σ
          = (N.weakNormalityOperatorOnStoich W.influences) 0 := by
        rw [hker, map_zero]
      exact W.nonsingular h0
    exact hσ this
  · exact absurd hcon
      (N.discordant_fullyOpen_of_positive_eigenvalue_onStoich W.influences hσ hpos heq)

end Network
end CRNT
