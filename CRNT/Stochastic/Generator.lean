import CRNT.Stochastic.ProductForm

/-!
# CTMC master-equation generator and Anderson–Craciun–Kurtz stationarity

The stochastic mass-action dynamics of a reaction network on the count lattice `ℕ^S`
is a continuous-time Markov chain. Its generator `Q` acts on a state function `π` by,
at each count vector `n`, summing the inflow of probability into `n` (reactions firing
from `n - source_r` and landing on `n`) minus the outflow out of `n` (reactions firing
from `n`). The stationary master equation `πQ = 0` is, pointwise, the global balance
`∑ inflow = ∑ outflow` at every count vector `n`.

Mathlib has no continuous-time generator type, so the generator is rendered here as an
explicit pointwise-finite algebraic operator over `ℕ^S`. After applying the per-reaction
product-form identity `π(n)·λ_r(n) = c^{source_r}·π(n − source_r)` (and its inflow
analogue), each reaction's signed flux is the complex-indexed quantity
`massActionRate κ r c · (π(n − target_r) − π(n − source_r))`. Their reaction-indexed sum
is the `ackResidual`; the stationarity predicate `IsMasterStationary` is its vanishing at
every count.

The Anderson–Craciun–Kurtz theorem is `productPoisson_isStationary_of_complexBalanced`:
for a complex-balanced concentration `c`, the product-Poisson density satisfies the global
balance, i.e. `ackResidual = 0` everywhere. The proof regroups the inflow and outflow
reaction sums by complex (`target r ↦ complex` and `source r ↦ complex`), reducing the
balance to the complex-by-complex equation `inflow = outflow`, which is exactly
`IsComplexBalanced`.

Depends on: `CRNT.Stochastic.ProductForm`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The product-Poisson density at the count `n` shifted down by the complex `y`,
species-by-species via `ℕ`-subtraction. This is `π(n − y)`, the inflow/outflow target
density entering the master-equation balance. -/
noncomputable def shiftedPMF (c : Concentration S) (n : S → ℕ) (y : Complex S) : ℝ :=
  if ∀ s, y s ≤ n s then productPoissonPMF c (fun s => n s - y s) else 0

/-- Shifted product-Poisson masses are nonnegative at nonnegative concentrations. -/
theorem shiftedPMF_nonneg (c : Concentration S) (hc : c.Nonnegative)
    (n : S → ℕ) (y : Complex S) : 0 ≤ shiftedPMF c n y := by
  unfold shiftedPMF
  split
  · exact productPoissonPMF_nonneg hc _
  · exact le_rfl

/-- The signed master-equation flux of reaction `r` at count `n` in ACK-substituted,
complex-indexed form: the deterministic mass-action rate at the complex-balanced
concentration `c` times the difference of shifted densities at the target and the source
complexes. After the product-form substitution `π(n)·λ_r(n) = massActionRate κ r c · π(n −
source_r)` this is exactly `[inflow into n via r] − [outflow out of n via r]` divided
through by the common scaling. -/
noncomputable def generatorFlux (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (n : S → ℕ) (r : N.R) : ℝ :=
  N.massActionRate κ r c *
    (shiftedPMF c n (N.reaction r).target - shiftedPMF c n (N.reaction r).source)

/-- The Anderson–Craciun–Kurtz stationarity residual at the count `n`: the reaction-indexed
sum of signed master-equation fluxes. The product-Poisson law is master-equation
stationary exactly when this residual vanishes at every count. -/
noncomputable def ackResidual (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (n : S → ℕ) : ℝ :=
  ∑ r : N.R, N.generatorFlux κ c n r

/-- The master-equation stationarity predicate (πQ = 0 at the global-balance level): the
ACK residual vanishes at every count vector. -/
def IsMasterStationary (N : Network S) (κ : RateConstants N) (c : Concentration S) :
    Prop :=
  ∀ n : S → ℕ, N.ackResidual κ c n = 0

/-- Inflow grouping. The reaction-indexed inflow sum, weighting each reaction by the shifted
density at its target complex, regroups over the finite set of complexes into the
complex-indexed inflow `π(n − y) · inflow(y)`. -/
theorem sum_target_flux_eq_inflow (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (n : S → ℕ) :
    (∑ r : N.R, N.massActionRate κ r c * shiftedPMF c n (N.reaction r).target) =
      ∑ y ∈ N.complexes, shiftedPMF c n y * N.inflow κ c y := by
  classical
  have hinflow : ∀ y : Complex S,
      shiftedPMF c n y * N.inflow κ c y =
        ∑ r : N.R, if (N.reaction r).target = y
          then shiftedPMF c n y * N.massActionRate κ r c else 0 := by
    intro y
    rw [inflow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases h : (N.reaction r).target = y <;> simp [h]
  calc
    (∑ r : N.R, N.massActionRate κ r c * shiftedPMF c n (N.reaction r).target)
        = ∑ y ∈ N.complexes, ∑ r ∈ Finset.univ.filter
            (fun r => (N.reaction r).target = y),
              N.massActionRate κ r c * shiftedPMF c n (N.reaction r).target := by
          rw [← Finset.sum_fiberwise_of_maps_to
            (g := fun r : N.R => (N.reaction r).target)
            (fun r _ => N.target_mem_complexes r)]
    _ = ∑ y ∈ N.complexes, shiftedPMF c n y * N.inflow κ c y := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [hinflow y]
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun r _ => ?_
          by_cases h : (N.reaction r).target = y
          · simp [h, mul_comm]
          · simp [h]

/-- Outflow grouping. The reaction-indexed outflow sum, weighting each reaction by the
shifted density at its source complex, regroups over the finite set of complexes into the
complex-indexed outflow `π(n − y) · outflow(y)`. -/
theorem sum_source_flux_eq_outflow (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (n : S → ℕ) :
    (∑ r : N.R, N.massActionRate κ r c * shiftedPMF c n (N.reaction r).source) =
      ∑ y ∈ N.complexes, shiftedPMF c n y * N.outflow κ c y := by
  classical
  have houtflow : ∀ y : Complex S,
      shiftedPMF c n y * N.outflow κ c y =
        ∑ r : N.R, if (N.reaction r).source = y
          then shiftedPMF c n y * N.massActionRate κ r c else 0 := by
    intro y
    rw [outflow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases h : (N.reaction r).source = y <;> simp [h]
  calc
    (∑ r : N.R, N.massActionRate κ r c * shiftedPMF c n (N.reaction r).source)
        = ∑ y ∈ N.complexes, ∑ r ∈ Finset.univ.filter
            (fun r => (N.reaction r).source = y),
              N.massActionRate κ r c * shiftedPMF c n (N.reaction r).source := by
          rw [← Finset.sum_fiberwise_of_maps_to
            (g := fun r : N.R => (N.reaction r).source)
            (fun r _ => N.source_mem_complexes r)]
    _ = ∑ y ∈ N.complexes, shiftedPMF c n y * N.outflow κ c y := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [houtflow y]
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun r _ => ?_
          by_cases h : (N.reaction r).source = y
          · simp [h, mul_comm]
          · simp [h]

/-- The Anderson–Craciun–Kurtz theorem (master-equation / global-balance level).

For a complex-balanced concentration `c`, the product-Poisson density is stationary for the
stochastic mass-action master equation: the ACK residual vanishes at every count vector.
The reaction-indexed inflow and outflow fluxes regroup over the finite set of complexes, and
complex balance (`inflow = outflow` at each complex) collapses the global balance termwise to
zero. -/
theorem productPoisson_isStationary_of_complexBalanced (N : Network S)
    (κ : RateConstants N) (c : Concentration S) (hcb : N.IsComplexBalanced κ c) :
    N.IsMasterStationary κ c := by
  intro n
  unfold ackResidual generatorFlux
  have hsplit :
      (∑ r : N.R, N.massActionRate κ r c *
          (shiftedPMF c n (N.reaction r).target -
            shiftedPMF c n (N.reaction r).source)) =
        (∑ r : N.R, N.massActionRate κ r c * shiftedPMF c n (N.reaction r).target) -
          (∑ r : N.R, N.massActionRate κ r c * shiftedPMF c n (N.reaction r).source) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  rw [hsplit, N.sum_target_flux_eq_inflow κ c n, N.sum_source_flux_eq_outflow κ c n,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun y hy => ?_
  rw [hcb y hy]
  ring

/-- The product-Poisson density is master-stationary, restated in terms of the product
measure's density and the master-equation balance predicate, exposing that the inflow and
outflow complex-indexed fluxes coincide complex-by-complex under complex balance. -/
theorem ackResidual_eq_zero_of_complexBalanced (N : Network S)
    (κ : RateConstants N) (c : Concentration S) (hcb : N.IsComplexBalanced κ c)
    (n : S → ℕ) : N.ackResidual κ c n = 0 :=
  N.productPoisson_isStationary_of_complexBalanced κ c hcb n

/-- Grounding bridge to the stochastic propensity. For a count `n` dominating the source
complex of reaction `r`, the raw outflow probability flux `π(n)·λ_r(n)` equals the
complex-indexed form `massActionRate κ r c · π(n − source_r)`. This is the per-reaction
ACK product-form substitution that turns the literal master-equation flux into the
`generatorFlux` summand, obtained by wrapping `productPoissonPMF_mul_descFactorial`. -/
theorem productPoissonPMF_mul_stochasticRate (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (n : S → ℕ) (r : N.R)
    (hn : ∀ s, (N.reaction r).source s ≤ n s) :
    productPoissonPMF c n * N.stochasticMassActionRate κ n r =
      N.massActionRate κ r c * shiftedPMF c n (N.reaction r).source := by
  unfold stochasticMassActionRate shiftedPMF massActionRate Complex.massActionMonomial
  rw [if_pos hn]
  rw [← mul_assoc, mul_comm (productPoissonPMF c n) (κ.k r), mul_assoc]
  rw [productPoissonPMF_mul_descFactorial N c n r hn]
  ring

end Network

end CRNT
