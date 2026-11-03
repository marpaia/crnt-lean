import CRNT.Stochastic.CTMC
import CRNT.Stochastic.FosterLyapunov
import CRNT.Equilibria.Wegscheider
import CRNT.Equilibria.WegscheiderConverse

/-!
# Microscopic stochastic detailed balance

For a reversible mass-action CRN, reactionwise deterministic detailed balance at a
positive concentration lifts to detailed balance of the stochastic count process under
the product-Poisson law.  The proof is the discrete falling-factorial analogue of the
usual equilibrium flux identity.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Microscopic detailed balance for a chosen reverse-channel pairing. -/
def IsMicroscopicallyDetailedBalanced (N : Network S)
    (ρ : ReversiblePairing N) (κ : N.RateConstants)
    (c : Concentration S) : Prop :=
  ∀ n : S → ℕ, ∀ r : N.R, N.Enabled n r →
    productPoissonPMF c n * N.stochasticMassActionRate κ n r =
      productPoissonPMF c (N.fireCount n r) *
        N.stochasticMassActionRate κ (N.fireCount n r) (ρ.rev r)

/-- The reverse reaction is enabled after firing an enabled forward reaction. -/
theorem reverse_enabled_after_fire (N : Network S) (ρ : ReversiblePairing N)
    {n : S → ℕ} {r : N.R} (hen : N.Enabled n r) :
    N.Enabled (N.fireCount n r) (ρ.rev r) := by
  intro s
  rw [ρ.source_rev_apply]
  simp [fireCount, hen]

/-- Shifting the post-jump state down by the reverse source (the original target) gives
exactly the original state shifted down by the forward source. -/
theorem fire_sub_reverseSource (N : Network S) (ρ : ReversiblePairing N)
    {n : S → ℕ} {r : N.R} (hen : N.Enabled n r) :
    (fun s => N.fireCount n r s - (N.reaction (ρ.rev r)).source s) =
      (fun s => n s - (N.reaction r).source s) := by
  funext s
  rw [ρ.source_rev_apply]
  simp [fireCount, hen, Nat.add_sub_cancel]

/-- Per-reaction microscopic detailed balance under the product-Poisson law. -/
theorem productPoisson_reactionFlux_detailedBalance
    (N : Network S) (ρ : ReversiblePairing N) (κ : N.RateConstants)
    {c : Concentration S} (hc : c.Positive)
    (hdb : N.IsReactionwiseDetailedBalanced ρ κ c)
    (n : S → ℕ) (r : N.R) (hen : N.Enabled n r) :
    productPoissonPMF c n * N.stochasticMassActionRate κ n r =
      productPoissonPMF c (N.fireCount n r) *
        N.stochasticMassActionRate κ (N.fireCount n r) (ρ.rev r) := by
  have hf := N.productPoissonPMF_mul_stochasticRate κ c n r hen
  have hrevEn := N.reverse_enabled_after_fire ρ hen
  have hb := N.productPoissonPMF_mul_stochasticRate κ c
    (N.fireCount n r) (ρ.rev r) hrevEn
  -- Both sides become the same shifted Poisson density multiplied by equal
  -- deterministic forward/reverse equilibrium fluxes.
  rw [hf, hb]
  rw [hdb r]
  have hshift :
      shiftedPMF c (N.fireCount n r) (N.reaction (ρ.rev r)).source =
        shiftedPMF c n (N.reaction r).source := by
    have h1 : ∀ s, (N.reaction (ρ.rev r)).source s ≤ N.fireCount n r s := hrevEn
    have h2 : ∀ s, (N.reaction r).source s ≤ n s := hen
    unfold shiftedPMF
    rw [if_pos h1, if_pos h2, N.fire_sub_reverseSource ρ hen]
  rw [hshift]

/-- Deterministic reactionwise detailed balance lifts to microscopic CTMC detailed
balance. -/
theorem microscopicallyDetailedBalanced_of_reactionwise
    (N : Network S) (ρ : ReversiblePairing N) (κ : N.RateConstants)
    {c : Concentration S} (hc : c.Positive)
    (hdb : N.IsReactionwiseDetailedBalanced ρ κ c) :
    N.IsMicroscopicallyDetailedBalanced ρ κ c := by
  intro n r hen
  exact N.productPoisson_reactionFlux_detailedBalance ρ κ hc hdb n r hen

/-- Wegscheider conditions therefore provide microscopic stochastic detailed balance via
the positive reactionwise equilibrium constructed in the deterministic theory. -/
theorem exists_microscopicDetailedBalance_of_Wegscheider
    (N : Network S) (ρ : ReversiblePairing N) (κ : N.RateConstants)
    (hW : N.SatisfiesWegscheider ρ κ) :
    ∃ c : Concentration S,
      c.Positive ∧ N.IsMicroscopicallyDetailedBalanced ρ κ c := by
  have hpot : N.HasWegscheiderPotential ρ κ :=
    (N.satisfiesWegscheider_iff_hasWegscheiderPotential ρ κ).mp hW
  rcases (N.hasWegscheiderPotential_iff_exists_positive_reactionwiseDetailedBalanced ρ κ).mp hpot
    with ⟨c, hc, hdb⟩
  exact ⟨c, hc, N.microscopicallyDetailedBalanced_of_reactionwise ρ κ hc hdb⟩

end Network
end CRNT
