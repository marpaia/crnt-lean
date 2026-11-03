import CRNT.Deficiency.KernelDimension
import CRNT.Dynamics.SiphonAutocatalysis
import CRNT.Deficiency.Consistent
import CRNT.Oscillation.VassenaCriteria
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The steady reaction-flux cone

The CRNT flux cone is the nonnegative part of the kernel of the stoichiometric map

`C(N) = { v : R → ℝ | v ≥ 0, S v = 0 }`.

It is the natural home for T-invariants, elementary flux modes, positive steady-state
fluxes, and consistency witnesses.  This file packages the purely linear-algebraic
object independently of any choice of kinetics.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A reaction-indexed vector is stoichiometrically stationary when it lies in the
kernel of the stoichiometric map. -/
def IsStationaryFlux (N : Network S) (v : N.R → ℝ) : Prop :=
  N.stoichMap v = 0


/-- Coordinatewise strict positivity of a reaction flux. -/
def IsPositiveFlux (N : Network S) (v : N.R → ℝ) : Prop :=
  ∀ r, 0 < v r

/-- The steady reaction-flux cone. -/
def FluxCone (N : Network S) : Set (N.R → ℝ) :=
  {v | N.IsNonnegativeFlux v ∧ N.IsStationaryFlux v}

/-- The linear flux space underlying the flux cone. -/
noncomputable def fluxSpace (N : Network S) : Submodule ℝ (N.R → ℝ) :=
  LinearMap.ker N.stoichMap

@[simp] theorem mem_fluxSpace_iff (N : Network S) (v : N.R → ℝ) :
    v ∈ N.fluxSpace ↔ N.IsStationaryFlux v := by
  rfl

@[simp] theorem zero_mem_fluxCone (N : Network S) : (0 : N.R → ℝ) ∈ N.FluxCone := by
  constructor
  · intro r; simp
  · simp [IsStationaryFlux]

/-- The flux cone is closed under addition. -/
theorem fluxCone_add_mem (N : Network S) {v w : N.R → ℝ}
    (hv : v ∈ N.FluxCone) (hw : w ∈ N.FluxCone) : v + w ∈ N.FluxCone := by
  constructor
  · intro r
    exact add_nonneg (hv.1 r) (hw.1 r)
  · simp only [IsStationaryFlux]
    rw [map_add, hv.2, hw.2, add_zero]

/-- The flux cone is closed under multiplication by nonnegative scalars. -/
theorem fluxCone_smul_mem (N : Network S) {v : N.R → ℝ} (hv : v ∈ N.FluxCone)
    {a : ℝ} (ha : 0 ≤ a) : a • v ∈ N.FluxCone := by
  constructor
  · intro r
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg ha (hv.1 r)
  · simp only [IsStationaryFlux]
    rw [map_smul, hv.2, smul_zero]

/-- A strictly positive stationary flux is an interior-type point of the flux cone. -/
theorem positiveStationaryFlux_mem_fluxCone (N : Network S) {v : N.R → ℝ}
    (hpos : N.IsPositiveFlux v) (hstat : N.IsStationaryFlux v) : v ∈ N.FluxCone := by
  exact ⟨fun r => (hpos r).le, hstat⟩

/-- The coordinate form of stationarity. -/
theorem isStationaryFlux_iff_species_balance (N : Network S) (v : N.R → ℝ) :
    N.IsStationaryFlux v ↔ ∀ s : S, ∑ r : N.R, v r * N.reactionVector r s = 0 := by
  constructor
  · intro h s
    have hs := congrFun h s
    simpa [IsStationaryFlux, stoichMap_apply] using hs
  · intro h
    funext s
    simpa [IsStationaryFlux, stoichMap_apply] using h s

/-- The flux-space dimension is reaction count minus stoichiometric rank. -/
theorem finrank_fluxSpace (N : Network S) :
    Module.finrank ℝ N.fluxSpace + N.stoichRank = Fintype.card N.R := by
  have hrn := LinearMap.finrank_range_add_finrank_ker N.stoichMap
  -- `hrn` lands on `finrank ℝ (N.R → ℝ)`, not `Fintype.card N.R`; and `fluxSpace` is
  -- definitionally `stoichMap.ker` but not syntactically so, which is why `simpa` failed.
  rw [Module.finrank_fintype_fun_eq_card] at hrn
  simp only [fluxSpace]
  rw [N.stoichRank_eq_finrank_range, add_comm]
  exact hrn

/-- CRN consistency is exactly the existence of a strictly positive point of the flux cone. -/
theorem isConsistent_iff_exists_positive_fluxCone (N : Network S) :
    N.IsConsistent ↔ ∃ v : N.R → ℝ, v ∈ N.FluxCone ∧ N.IsPositiveFlux v := by
  constructor
  · rintro ⟨v, hpos, hzero⟩
    refine ⟨v, ?_, hpos⟩
    constructor
    · exact fun r => (hpos r).le
    · exact hzero
  · rintro ⟨v, hv, hpos⟩
    exact ⟨v, hpos, hv.2⟩

/-- The positive steady-state flux object used by the oscillation theory is precisely a
strictly positive point of the steady flux cone. -/
theorem positiveSteadyStateFlux_iff_positive_fluxCone (N : Network S) (v : N.R → ℝ) :
    N.PositiveSteadyStateFlux v ↔ v ∈ N.FluxCone ∧ N.IsPositiveFlux v := by
  constructor
  · intro h
    refine ⟨⟨fun r => (h.positive r).le, ?_⟩, h.positive⟩
    apply (N.isStationaryFlux_iff_species_balance v).2
    exact h.stationary
  · rintro ⟨hv, hpos⟩
    refine ⟨hpos, ?_⟩
    exact (N.isStationaryFlux_iff_species_balance v).1 hv.2

end Network

end CRNT
