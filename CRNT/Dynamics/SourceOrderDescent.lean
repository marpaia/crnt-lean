import CRNT.Dynamics.ComplexBalanceCycleDecomposition

/-!
# Exact descent from the order of source log-rates

For a complex-balanced mass-action system with positive equilibrium `x*` and a positive state
`x`, write `u = log x - log x*` and order the reactions by their source log-rates
`⟪y_r, u⟫ = ∑ s, y_r s * u s` (`Network.sourceLogProjection u r`).  The mass-action field lies in
the polar cone of every direction that preserves this weak order
(`massActionVectorField_mem_polar_relativeSourceOrderCone`).  Read for a test vector `n`, this
says:

  if every source of strictly smaller `n`-weight has strictly larger log-rate,
  then `∑ s, n s * f s (x) ≥ 0`.

`inner_nonneg_of_sourceOrder` states this exactly.  It is pointwise and has no uncertainty
parameter: the `δ` of a toric differential inclusion appears only once the order of log-rates is
estimated from coarse information about `x`.  This is the descent condition used by the planar
zero-separating polygon near a codimension-two face.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Network

open scoped BigOperators InnerProductSpace

variable {S : Type} [DecidableEq S] [Fintype S]

theorem sourceLogProjection_neg (N : Network S) (w : S → ℝ) (r : N.R) :
    N.sourceLogProjection (-w) r = -N.sourceLogProjection w r := by
  simp [sourceLogProjection, Finset.sum_neg_distrib]

/-- **Exact source-order descent.** -/
theorem inner_nonneg_of_sourceOrder (N : Network S) (κ : N.RateConstants)
    {x xstar : Concentration S} (hx : x.Positive) (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) (n : S → ℝ)
    (hord : ∀ r q : N.R, N.sourceLogProjection n r < N.sourceLogProjection n q →
      N.sourceLogProjection (fun s => Real.log (x s) - Real.log (xstar s)) q <
        N.sourceLogProjection (fun s => Real.log (x s) - Real.log (xstar s)) r) :
    0 ≤ ∑ s, n s * N.massActionVectorField κ x s := by
  have hpol := N.massActionVectorField_mem_polar_relativeSourceOrderCone κ hx hxs hcb
  rw [mem_polarCone] at hpol
  have hz : CRNT.toEuclid (-n) ∈ N.relativeSourceOrderCone
      (fun s => Real.log (x s) - Real.log (xstar s)) := by
    change ∀ r q, _ ≤ _ → _ ≤ _
    intro r q hle
    rw [LinearEquiv.symm_apply_apply, sourceLogProjection_neg, sourceLogProjection_neg,
      neg_le_neg_iff]
    by_contra hlt
    push Not at hlt
    exact absurd hle (not_le.mpr (hord r q hlt))
  have h := hpol hz
  rw [CRNT.inner_toEuclid] at h
  have : ∑ s, (-n) s * N.massActionVectorField κ x s =
      -∑ s, n s * N.massActionVectorField κ x s := by
    simp [Finset.sum_neg_distrib]
  linarith

end Network
end CRNT
