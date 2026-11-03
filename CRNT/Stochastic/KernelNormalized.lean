import CRNT.Stochastic.KernelIrreducible

/-!
# Normalizing the support-restricted invariant measure to a probability measure

`CRNT.Stochastic.KernelIrreducible` proves the embedded jump kernel leaves the support-restricted
density measure `restrictedStationaryMeasure κ c T` invariant over any closed enabled region `T`.
For a *finite* region that measure is finite, so it normalizes to a genuine **invariant probability
measure** — the stationary distribution of the jump chain on the region. This module supplies the
normalization layer (`IsProbabilityMeasure`).

The core is general measure theory: scaling an invariant measure by a constant preserves invariance
(`invariant_smul`, since `Measure.bind` is linear), so dividing a finite nonzero invariant measure
by its total mass gives an invariant probability measure (`invariant_normalize`). Applied to the
restricted stationary measure of a finite closed enabled region — finite by
`restrictedStationaryMeasure_isFiniteMeasure` — this yields
`jumpKernel_normalized_isInvariant_probabilityMeasure`: the normalized restricted stationary measure
is both `Kernel.Invariant` under the jump kernel and an `IsProbabilityMeasure`.

The total-mass gate `hpos` is discharged for a strictly positive concentration on a nonempty region:
the product-Poisson density is positive everywhere (`productPoissonPMF_pos`), so the holding-rate
reweighted jump-chain weight is positive on the region (`jumpStationaryMass_pos`, using `exit_ne`),
forcing the restricted measure's total mass positive (`restrictedStationaryMeasure_univ_pos`). The
resulting capstone `jumpKernel_isInvariant_probabilityMeasure_of_nonempty` is unconditional in the
mass. The *existence* of a finite closed enabled region for a given network — the canonical
communicating-class characterization — is a separate network-structural question.

## Main results

* `invariant_smul` — scaling an invariant measure preserves kernel invariance.
* `invariant_normalize` — a finite nonzero invariant measure normalizes to an invariant probability
  measure.
* `restrictedStationaryMeasure_isFiniteMeasure` — the restricted stationary measure is finite over a
  finite region.
* `jumpKernel_normalized_isInvariant_probabilityMeasure` — the normalized restricted stationary
  measure is an invariant probability measure for the embedded jump kernel.
* `productPoissonPMF_pos` — the product-Poisson density is positive at a positive concentration.
* `jumpStationaryMass_pos` — the lifted jump-chain weight is positive on a closed enabled region.
* `restrictedStationaryMeasure_univ_pos` — positive total mass over a nonempty closed enabled region.
* `jumpKernel_isInvariant_probabilityMeasure_of_nonempty` — the unconditional (mass-gate-free)
  invariant probability measure on a nonempty finite closed enabled region.

Depends on: `CRNT.Stochastic.KernelIrreducible`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CRNT

variable {α : Type*} [MeasurableSpace α]

/-- **Scaling preserves invariance.** If `μ` is invariant under the kernel `κ`, so is `a • μ` for
any constant `a`, because `Measure.bind` is linear in the measure. -/
theorem invariant_smul {κ : Kernel α α} {μ : Measure α} (h : Kernel.Invariant κ μ) (a : ℝ≥0∞) :
    Kernel.Invariant κ (a • μ) := by
  unfold Kernel.Invariant at h ⊢
  rw [Measure.bind_smul a μ (Kernel.aemeasurable κ), h]

/-- **Normalization to a probability measure.** A finite, nonzero invariant measure, divided by its
total mass, is an invariant probability measure. -/
theorem invariant_normalize {κ : Kernel α α} {μ : Measure α} (h : Kernel.Invariant κ μ)
    (hne : μ Set.univ ≠ 0) (hlt : μ Set.univ ≠ ∞) :
    Kernel.Invariant κ ((μ Set.univ)⁻¹ • μ) ∧ IsProbabilityMeasure ((μ Set.univ)⁻¹ • μ) := by
  refine ⟨invariant_smul h _, ⟨?_⟩⟩
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hne hlt]

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

attribute [local instance] CRNT.Network.instMeasurableSpaceCount

/-- **Finiteness over a finite region.** The support-restricted stationary measure has finite total
mass when the region `T` is finite: its mass is the finite sum, over `T`, of the lifted stationary
weights, each of which is a finite `ENNReal`. -/
theorem restrictedStationaryMeasure_isFiniteMeasure (N : Network S) (κ : RateConstants N)
    (c : Concentration S) {T : Set (S → ℕ)} (hTfin : T.Finite) :
    IsFiniteMeasure (N.restrictedStationaryMeasure κ c T) := by
  refine ⟨?_⟩
  rw [restrictedStationaryMeasure, Measure.restrict_apply_univ, jumpStationaryMeasure,
    Measure.sum_apply _ (MeasurableSpace.measurableSet_top (s := T))]
  have hzero : ∀ n ∉ hTfin.toFinset,
      (ENNReal.ofReal (N.jumpStationaryMass κ c n) • Measure.dirac n) T = 0 := by
    intro n hn
    rw [Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' n (MeasurableSpace.measurableSet_top (s := T)),
      Set.indicator_of_notMem (fun hT => hn (hTfin.mem_toFinset.mpr hT)), mul_zero]
  rw [tsum_eq_sum hzero]
  refine ENNReal.sum_lt_top.mpr (fun n _ => ?_)
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top (Measure.dirac n) T)

omit [DecidableEq S] in
/-- **Strict positivity of the product-Poisson density.** At a strictly positive concentration the
Anderson–Craciun–Kurtz product-form density `productPoissonPMF c n` is positive at every count
vector: each single-species Poisson factor `exp(-(c s))·(c s)^(n s)/(n s)!` is positive, and a
finite product of positive reals is positive. -/
theorem productPoissonPMF_pos {c : Concentration S} (hc : c.Positive) (n : S → ℕ) :
    0 < productPoissonPMF c n := by
  refine Finset.prod_pos fun s _ => ?_
  have hcs : 0 < c s := hc s
  positivity

/-- **Strict positivity of the lifted jump-chain stationary weight on a closed enabled region.** At
a strictly positive concentration the reweighted product-Poisson mass
`jumpStationaryMass κ c m = productPoissonPMF c m · exitRate κ m` is positive at every member of a
closed enabled region: the density is positive by `productPoissonPMF_pos`, and the exit rate is
positive there since the region admits no absorbing member (`exit_ne`). -/
theorem jumpStationaryMass_pos (N : Network S) (κ : RateConstants N) (c : Concentration S)
    (hc : c.Positive) {T : Set (S → ℕ)} (hT : N.ClosedEnabledRegion κ T) {m : S → ℕ}
    (hm : m ∈ T) : 0 < N.jumpStationaryMass κ c m := by
  rw [jumpStationaryMass]
  refine mul_pos (productPoissonPMF_pos hc m) ?_
  exact lt_of_le_of_ne (N.exitRate_nonneg κ m) (Ne.symm (hT.exit_ne m hm))

/-- **The restricted stationary measure has positive total mass over a nonempty closed enabled
region.** Picking any member `m` of the nonempty region, the singleton mass of the restricted
measure at `m` is `ofReal (jumpStationaryMass κ c m) > 0` by `restrictedStationaryMeasure_singleton`
and `jumpStationaryMass_pos`; monotonicity in the set then forces the total mass over the universe
to be positive, hence nonzero — discharging the `hpos` gate of the normalization capstone. -/
theorem restrictedStationaryMeasure_univ_pos (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (hc : c.Positive) {T : Set (S → ℕ)}
    (hT : N.ClosedEnabledRegion κ T) (hne : T.Nonempty) :
    N.restrictedStationaryMeasure κ c T Set.univ ≠ 0 := by
  obtain ⟨m, hm⟩ := hne
  have hsingle : 0 < N.restrictedStationaryMeasure κ c T {m} := by
    rw [N.restrictedStationaryMeasure_singleton κ c T m, Set.indicator_of_mem hm]
    exact ENNReal.ofReal_pos.mpr (N.jumpStationaryMass_pos κ c hc hT hm)
  have hmono : N.restrictedStationaryMeasure κ c T {m} ≤
      N.restrictedStationaryMeasure κ c T Set.univ :=
    measure_mono (Set.subset_univ _)
  exact (lt_of_lt_of_le hsingle hmono).ne'

/-- **The normalized restricted stationary measure is an invariant probability measure.** Over a
finite closed enabled region `T` with positive total mass, normalizing the support-restricted
stationary measure by its mass produces a measure that is both invariant under the embedded jump
kernel and a probability measure — the stationary distribution of the embedded jump chain on `T`. -/
theorem jumpKernel_normalized_isInvariant_probabilityMeasure (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (hc : c.Nonnegative) (hcb : N.IsComplexBalanced κ c)
    {T : Set (S → ℕ)} (hT : N.ClosedEnabledRegion κ T) (hTfin : T.Finite)
    (hpos : N.restrictedStationaryMeasure κ c T Set.univ ≠ 0) :
    Kernel.Invariant (N.jumpKernel κ)
        ((N.restrictedStationaryMeasure κ c T Set.univ)⁻¹ • N.restrictedStationaryMeasure κ c T) ∧
      IsProbabilityMeasure
        ((N.restrictedStationaryMeasure κ c T Set.univ)⁻¹ • N.restrictedStationaryMeasure κ c T) := by
  haveI hfin : IsFiniteMeasure (N.restrictedStationaryMeasure κ c T) :=
    N.restrictedStationaryMeasure_isFiniteMeasure κ c hTfin
  have hinv : Kernel.Invariant (N.jumpKernel κ) (N.restrictedStationaryMeasure κ c T) :=
    N.jumpKernel_invariant_restrictedStationaryMeasure κ c hc hcb T hT
  have hlt : N.restrictedStationaryMeasure κ c T Set.univ ≠ ∞ :=
    measure_ne_top (N.restrictedStationaryMeasure κ c T) Set.univ
  exact invariant_normalize hinv hpos hlt

/-- **Unconditional invariant probability measure on a nonempty finite closed enabled region.** At a
strictly positive complex-balanced concentration, the normalized support-restricted stationary
measure of a nonempty finite closed enabled region is both invariant under the embedded jump kernel
and a probability measure. This discharges the positive-mass gate of
`jumpKernel_normalized_isInvariant_probabilityMeasure`: strict positivity of the concentration makes
the lifted product-Poisson weight positive on the region, so the total mass is nonzero. -/
theorem jumpKernel_isInvariant_probabilityMeasure_of_nonempty (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (hc : c.Positive) (hcb : N.IsComplexBalanced κ c) {T : Set (S → ℕ)}
    (hT : N.ClosedEnabledRegion κ T) (hTfin : T.Finite) (hne : T.Nonempty) :
    Kernel.Invariant (N.jumpKernel κ)
        ((N.restrictedStationaryMeasure κ c T Set.univ)⁻¹ • N.restrictedStationaryMeasure κ c T) ∧
      IsProbabilityMeasure
        ((N.restrictedStationaryMeasure κ c T Set.univ)⁻¹ • N.restrictedStationaryMeasure κ c T) :=
  N.jumpKernel_normalized_isInvariant_probabilityMeasure κ c hc.nonnegative hcb hT hTfin
    (N.restrictedStationaryMeasure_univ_pos κ c hc hT hne)

end Network

end CRNT
