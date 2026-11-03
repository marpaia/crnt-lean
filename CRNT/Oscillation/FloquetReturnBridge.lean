import CRNT.Oscillation.Floquet
import CRNT.Oscillation.ScalarReturnStability

/-!
# From a Floquet multiplier to contraction of a scalar Poincare map

For a planar autonomous system the Poincare section is one-dimensional.  The nontrivial Floquet
multiplier is therefore the derivative of the scalar return map at the fixed point.  The hard
geometric/variational part is establishing that identification for a concrete section.  Once it is
known, no additional spectral-radius machinery is needed: linear Floquet stability gives
`|P'(x₀)| < 1`, and `ScalarC1Map.exists_localContraction` upgrades that to a genuine nonlinear
contraction on a small invariant section interval.

This file formalizes that implication.  It narrows the remaining Floquet frontier to the precise
variational identity between monodromy and the derivative of a chosen Poincare map, plus the
continuous-time interpolation between section hits.
-/

namespace CRNT

open Filter Topology


namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]
variable {N : Network S} {κ : N.RateConstants}

/-- Certified identification of the derivative of a scalar Poincare return map with a nontrivial
Floquet multiplier of a periodic mass-action orbit.

The equality is stated at the level of moduli, which is exactly what stability needs and avoids an
irrelevant choice of orientation for the scalar section coordinate. -/
structure ScalarFloquetReturnBridge
    (P : N.LinearlyStablePositivePeriodicOrbit κ) (f : ℝ → ℝ) (x₀ : ℝ) where
  c1 : ScalarC1Map f
  fixed : f x₀ = x₀
  multiplier : ℂ
  hasMultiplier : P.floquet.HasMultiplier multiplier
  nontrivial : multiplier ≠ 1
  derivative_modulus : |c1.derivative x₀| = ‖multiplier‖

namespace ScalarFloquetReturnBridge

variable {P : N.LinearlyStablePositivePeriodicOrbit κ} {f : ℝ → ℝ} {x₀ : ℝ}

/-- Linear Floquet stability forces the scalar return derivative strictly inside the unit disk. -/
theorem derivative_abs_lt_one (B : N.ScalarFloquetReturnBridge P f x₀) :
    |B.c1.derivative x₀| < 1 := by
  rw [B.derivative_modulus]
  exact P.stable.2 B.multiplier B.hasMultiplier B.nontrivial

/-- **Floquet-to-nonlinear-section stability.** Once the scalar Poincare derivative is identified
with the nontrivial Floquet multiplier, a linearly stable periodic orbit has a local invariant
section interval on which the full nonlinear return map is a strict contraction. -/
theorem exists_localContraction (B : N.ScalarFloquetReturnBridge P f x₀) :
    Nonempty (ScalarLocalContraction f x₀) :=
  B.c1.exists_localContraction B.fixed B.derivative_abs_lt_one

/-- Successive Poincare hits from any point in the resulting local interval converge geometrically
to the periodic-orbit fixed point. -/
theorem exists_localSectionAttractor
    (B : N.ScalarFloquetReturnBridge P f x₀) :
    ∃ D : ScalarLocalContraction f x₀,
      ∀ x : D.LocalInterval,
        Tendsto ((D.toContractingReturnMapData B.fixed).iterates x) Filter.atTop
          (𝓝 (D.toContractingReturnMapData B.fixed).fixedPoint) := by
  obtain ⟨D⟩ := B.exists_localContraction
  exact ⟨D, fun x => D.tendsto_restrictedIterates B.fixed x⟩

end ScalarFloquetReturnBridge

end Network

end CRNT
