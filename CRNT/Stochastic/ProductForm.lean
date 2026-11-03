import CRNT.Equilibria.ComplexBalanced
import CRNT.Kinetics.MassAction
import CRNT.Kinetics.Concentration
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Product-form stationary measure (Anderson–Craciun–Kurtz, measure side)

For a complex-balanced reaction network the stationary distribution of the
stochastic mass-action continuous-time Markov chain on `ℕ^S` is a product of
Poisson distributions, one per species, with rate equal to the complex-balanced
equilibrium concentration. This module supplies the measure-theoretic objects on
the state space `S → ℕ` and the algebraic identities that constitute the heart of
that statement.

The state space `S → ℕ` is the species-count lattice `ℕ^S`. `productPoisson c hc`
is the candidate stationary law: the product over species of `poissonMeasure (c s)`.
Its explicit density is `productPoissonPMF`, and `productPoisson_singleton` identifies
the measure of a single count vector with that density.

The stochastic mass-action propensity `stochasticMassActionRate` is the falling-
factorial counting law `κ r · ∏ s, (n s)^{(source r s)}`, the discrete analogue of the
deterministic mass-action monomial. The lemma `productPoissonPMF_mul_descFactorial`
is the central per-species/global identity: multiplying the product-Poisson
density by a falling-factorial propensity factor reproduces the density at the shifted
count weighted by a power of the rate, `π(n) · n^{(k)} = c^k · π(n - k)`. Feeding this
through `IsComplexBalanced` reduces the complex-by-complex stochastic flux balance
exactly to the deterministic complex-balance equation; that reduction is
`productPoisson_detailedBalance_of_complexBalanced`.

## Scope

This module supplies the measure side: the stationary product measure, its density, the
stochastic propensity, and the density/balance algebra that the generator-level stationarity
proof reduces to. Mathlib has discrete-time transition kernels (`Kernel.Invariant`,
`Kernel.IsReversible`) but no continuous-time generator type, so the generator is rendered as
an explicit pointwise-finite operator in `CRNT.Stochastic.CTMC`, where
`productPoisson_isGeneratorStationary_of_complexBalanced` proves that the product-Poisson
density is annihilated by the generator (`πQ = 0`) at a complex-balanced concentration.

Depends on: `CRNT.Equilibria.ComplexBalanced`,
`CRNT.Kinetics.MassAction`, `CRNT.Kinetics.Concentration`, Mathlib Poisson and product
measures.
-/

open MeasureTheory ProbabilityTheory

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The product-of-Poissons measure on the count space `S → ℕ`: one Poisson factor per
species with rate the nonnegative concentration `c s`. This is the product-form
stationary candidate of Anderson–Craciun–Kurtz. -/
noncomputable def productPoisson (c : Concentration S) (hc : c.Nonnegative) :
    Measure (S → ℕ) :=
  Measure.pi (fun s => poissonMeasure (NNReal.mk (c s) (hc s)))

instance (c : Concentration S) (hc : c.Nonnegative) :
    IsProbabilityMeasure (productPoisson c hc) := by
  unfold productPoisson; infer_instance

/-- The explicit product-Poisson density at a count vector `n`:
`∏ s, exp(-(c s)) · (c s)^(n s) / (n s)!`. -/
noncomputable def productPoissonPMF (c : Concentration S) (n : S → ℕ) : ℝ :=
  ∏ s : S, Real.exp (-(c s)) * (c s) ^ (n s) / (n s).factorial

/-- Each single-species Poisson density factor is nonnegative when the rate is. -/
theorem poissonFactor_nonneg {c : ℝ} (hc : 0 ≤ c) (m : ℕ) :
    0 ≤ Real.exp (-c) * c ^ m / m.factorial := by positivity

omit [DecidableEq S] in
/-- The product-Poisson density is nonnegative at every count vector. -/
theorem productPoissonPMF_nonneg {c : Concentration S} (hc : c.Nonnegative)
    (n : S → ℕ) : 0 ≤ productPoissonPMF c n :=
  Finset.prod_nonneg fun s _ => poissonFactor_nonneg (hc s) (n s)

omit [DecidableEq S] in
/-- The product-Poisson measure of a single count vector equals its product density,
coerced into `ℝ≥0∞`. Each Poisson factor's mass is `poissonMeasure_singleton`, and the
finite product over species is `Measure.pi_singleton`. -/
theorem productPoisson_singleton (c : Concentration S) (hc : c.Nonnegative)
    (n : S → ℕ) :
    productPoisson c hc {n} = ENNReal.ofReal (productPoissonPMF c n) := by
  unfold productPoisson productPoissonPMF
  rw [Measure.pi_singleton]
  rw [ENNReal.ofReal_prod_of_nonneg fun s _ => poissonFactor_nonneg (hc s) (n s)]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [poissonMeasure_singleton]
  rfl

/-- The stochastic mass-action propensity of reaction `r` at the count vector `n`:
the rate constant times the falling-factorial counting law `∏ s, (n s)^{(source r s)}`.
This is the discrete-state analogue of the deterministic mass-action monomial. -/
noncomputable def stochasticMassActionRate (N : Network S) (κ : RateConstants N)
    (n : S → ℕ) (r : N.R) : ℝ :=
  κ.k r * ∏ s : S, ((n s).descFactorial ((N.reaction r).source s) : ℝ)

/-- The stochastic mass-action propensity is nonnegative. -/
theorem stochasticMassActionRate_nonneg (N : Network S) (κ : RateConstants N)
    (n : S → ℕ) (r : N.R) : 0 ≤ N.stochasticMassActionRate κ n r := by
  unfold stochasticMassActionRate
  refine mul_nonneg (κ.positive r).le (Finset.prod_nonneg fun s _ => ?_)
  exact_mod_cast Nat.zero_le _

/-- The per-species product-form identity. For `k ≤ m` and a real rate `c`,
multiplying the Poisson density `exp(-c)·c^m/m!` by the falling factorial `m^{(k)}`
yields `c^k` times the density at the shifted count `m - k`. This is the exact algebraic
content (per coordinate) underlying Anderson–Craciun–Kurtz product form. -/
theorem poissonFactor_mul_descFactorial (c : ℝ) {m k : ℕ} (hk : k ≤ m) :
    (Real.exp (-c) * c ^ m / m.factorial) * ((m.descFactorial k : ℝ)) =
      c ^ k * (Real.exp (-c) * c ^ (m - k) / (m - k).factorial) := by
  have hfact : ((m - k).factorial : ℝ) * (m.descFactorial k : ℝ) = (m.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_mul_descFactorial hk
  have hmk : c ^ m = c ^ k * c ^ (m - k) := by
    rw [← pow_add, Nat.add_sub_cancel' hk]
  have hf0 : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  have hfk0 : ((m - k).factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos (m - k)).ne'
  field_simp
  rw [hmk]
  ring_nf
  rw [← hfact]
  ring

/-- The global product-form identity. For a count vector `n` dominating the source
complex of reaction `r` species-by-species, the product-Poisson density times the
falling-factorial propensity factor equals the source-monomial `c^{source}` times the
density at the count shifted down by the source complex. This is the multi-species
Anderson–Craciun–Kurtz identity, obtained by taking the product of the per-species
identity over all species. -/
theorem productPoissonPMF_mul_descFactorial (N : Network S) (c : Concentration S)
    (n : S → ℕ) (r : N.R)
    (hn : ∀ s, (N.reaction r).source s ≤ n s) :
    productPoissonPMF c n *
        (∏ s : S, ((n s).descFactorial ((N.reaction r).source s) : ℝ)) =
      (∏ s : S, (c s) ^ ((N.reaction r).source s)) *
        productPoissonPMF c (fun s => n s - (N.reaction r).source s) := by
  unfold productPoissonPMF
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  exact poissonFactor_mul_descFactorial (c s) (hn s)

end Network

end CRNT
