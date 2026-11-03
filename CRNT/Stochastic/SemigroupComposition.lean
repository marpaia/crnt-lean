import CRNT.Stochastic.Semigroup
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Basic

/-!
# Chapman-Kolmogorov composition law for the uniformized CME semigroup

The uniformized chemical-master-equation transition semigroup `cmeSemigroup κ hTfin t` of
`CRNT.Stochastic.Semigroup` satisfies the **Chapman-Kolmogorov equation** `P_{s+t} = P_s ∘ₖ P_t`:
composing the time-`s` and time-`t` transition kernels gives the time-`s+t` kernel. This is the
defining semigroup law of a continuous-time Markov transition function (Norris, "Markov Chains"),
and over a finite closed enabled region it follows from Jensen's uniformization (Jensen, "Markoff
chains as an aid in the study of Markoff processes") once two ingredients are in place.

The first is analytic: the Poisson point masses convolve,
`∑_{j+k=m} e^{−s} s^j/j! · e^{−t} t^k/k! = e^{−(s+t)} (s+t)^m/m!`, the Poisson family being closed
under convolution at the level of point masses. The exponentials factor as `e^{−(s+t)}`, and the
remaining sum is the binomial expansion of `(s+t)^m/m!`, with `(j+k)!/(j! k!) = C(j+k, j)` matching
each antidiagonal term. This is `poissonPMF_conv`, restated on `ℝ≥0∞` Poisson masses as
`poissonMeasure_singleton_conv`.

The second is the kernel power law `U^{∘j} ∘ₖ U^{∘k} = U^{∘(j+k)}` (`uniformizedPow_comp`), proved by
induction on `j` from associativity of kernel composition (`Kernel.comp_assoc`) and `U^{∘0} = id`.

Assembling these, the composition `P_s ∘ₖ P_t` distributes over the two Poisson superpositions at the
pointwise `Measure.sum` level (there is no `ℝ≥0∞`-scalar kernel smul instance, so the superposition
is integrated term by term against `Measure.sum`). The double lattice tsum reindexes by the
step-count antidiagonal (`tsum_sum_antidiagonal_eq_tsum_prod`), the power law collapses the inner
composition to `U^{∘(j+k)}`, and the scalar convolution collapses the Poisson weights to the
time-`s+t` weights, recovering `P_{s+t}` (`cmeSemigroup_comp`).

## Main results

* `poissonPMF_conv` — the scalar Poisson point-mass convolution identity.
* `poissonMeasure_singleton_conv` — its `ℝ≥0∞`-valued restatement on the Poisson measure masses.
* `uniformizedPow_comp` — the kernel power law `U^{∘j} ∘ₖ U^{∘k} = U^{∘(j+k)}`.
* `poissonRate_add` — additivity of the Poisson rate in time, `Λ(s+t) = Λs + Λt`.
* `tsum_sum_antidiagonal_eq_tsum_prod` — antidiagonal reindexing of an `ℝ≥0∞` two-index tsum.
* `cmeSemigroup_comp` — the Chapman-Kolmogorov law `P_{s+t} = P_s ∘ₖ P_t`.

Depends on: `CRNT.Stochastic.Semigroup`,
`Mathlib.Data.Nat.Choose.Sum`, `Mathlib.Data.Nat.Choose.Basic`.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

attribute [local instance] CRNT.Network.instMeasurableSpaceCount

/-- **Poisson point-mass convolution.** For real rates `s, t` the Poisson point masses convolve over
the step-count antidiagonal: `∑_{j+k=m} (e^{−s} s^j/j!)(e^{−t} t^k/k!) = e^{−(s+t)} (s+t)^m/m!`. The
exponentials factor as `e^{−(s+t)}`, and the remaining sum is the binomial expansion of
`(s+t)^m/m!` with the multinomial identity `(j+k)!/(j! k!) = C(j+k, j)` matching each antidiagonal
term. This is the scalar core of the Chapman-Kolmogorov law. -/
theorem poissonPMF_conv (s t : ℝ) (m : ℕ) :
    ∑ p ∈ Finset.antidiagonal m,
        (Real.exp (-s) * s ^ p.1 / p.1.factorial) * (Real.exp (-t) * t ^ p.2 / p.2.factorial) =
      Real.exp (-(s + t)) * (s + t) ^ m / m.factorial := by
  have hexp : Real.exp (-(s + t)) = Real.exp (-s) * Real.exp (-t) := by
    rw [← Real.exp_add]; ring_nf
  rw [hexp, (Commute.all s t).add_pow', Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨j, k⟩ := p
  rw [Finset.mem_antidiagonal] at hp
  subst hp
  rw [nsmul_eq_mul]
  have hfactN : (j + k).choose j * j.factorial * k.factorial = (j + k).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right j k)
    rwa [Nat.add_sub_cancel_left] at this
  have hfact : ((j + k).choose j : ℝ) * (j.factorial : ℝ) * (k.factorial : ℝ) =
      ((j + k).factorial : ℝ) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, hfactN]
  have hjf : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have hkf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hmf : ((j + k).factorial : ℝ) ≠ 0 := by exact_mod_cast (j + k).factorial_ne_zero
  field_simp
  rw [← hfact]
  ring

/-- The `ℝ≥0∞`-valued Poisson convolution on the measure point masses: the antidiagonal sum of
products of `Po(r₁)` and `Po(r₂)` singleton masses equals the `Po(r₁ + r₂)` singleton mass. This is
the `poissonPMF_conv` identity transported through `poissonMeasure_singleton`, with the nonnegativity
of each point mass letting `ENNReal.ofReal` distribute over the finite sum and the products. -/
theorem poissonMeasure_singleton_conv (r₁ r₂ : ℝ≥0) (m : ℕ) :
    ∑ p ∈ Finset.antidiagonal m,
        poissonMeasure r₁ {p.1} * poissonMeasure r₂ {p.2} =
      poissonMeasure (r₁ + r₂) {m} := by
  have hnn : ∀ (r : ℝ≥0) (n : ℕ), (0:ℝ) ≤ Real.exp (-r) * r ^ n / n.factorial := fun r n => by
    positivity
  simp_rw [poissonMeasure_singleton]
  have hterm : ∀ p : ℕ × ℕ,
      ENNReal.ofReal (Real.exp (-r₁) * r₁ ^ p.1 / p.1.factorial) *
          ENNReal.ofReal (Real.exp (-r₂) * r₂ ^ p.2 / p.2.factorial) =
        ENNReal.ofReal ((Real.exp (-r₁) * r₁ ^ p.1 / p.1.factorial) *
          (Real.exp (-r₂) * r₂ ^ p.2 / p.2.factorial)) := fun p =>
    (ENNReal.ofReal_mul (hnn r₁ p.1)).symm
  simp_rw [hterm]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => mul_nonneg (hnn r₁ p.1) (hnn r₂ p.2))]
  rw [poissonPMF_conv (r₁ : ℝ) (r₂ : ℝ) m]
  rw [NNReal.coe_add]

/-- **Power law for the uniformized kernel.** Composing the `j`-step and `k`-step transition kernels
of the uniformized chain gives the `(j+k)`-step kernel: `U^{∘j} ∘ₖ U^{∘k} = U^{∘(j+k)}`. The proof is
induction on `j`, using `U^{∘0} = id` for the base case and associativity of kernel composition
(`Kernel.comp_assoc`) for the successor step. -/
theorem uniformizedPow_comp (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    (hTfin : T.Finite) (j k : ℕ) :
    N.uniformizedPow κ hTfin j ∘ₖ N.uniformizedPow κ hTfin k =
      N.uniformizedPow κ hTfin (j + k) := by
  induction j with
  | zero =>
    rw [Nat.zero_add]
    show N.uniformizedPow κ hTfin 0 ∘ₖ N.uniformizedPow κ hTfin k = _
    rw [uniformizedPow, Kernel.id_comp]
  | succ j ih =>
    rw [uniformizedPow, Kernel.comp_assoc, ih, Nat.succ_add, uniformizedPow]

/-- The Poisson rate is additive in time: `Λ(s+t) = Λs + Λt`. The rate is the linear map
`t ↦ Λ.toNNReal · t`, so it distributes over the sum of elapsed times. -/
theorem poissonRate_add (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    (hTfin : T.Finite) (s t : ℝ≥0) :
    N.poissonRate κ hTfin (s + t) = N.poissonRate κ hTfin s + N.poissonRate κ hTfin t := by
  rw [poissonRate, poissonRate, poissonRate, mul_add]

/-- Antidiagonal reindexing in `ℝ≥0∞`: a tsum over `m` of the antidiagonal-`m` finite sums of a
two-index family equals the product tsum over `ℕ × ℕ`. Every `ℝ≥0∞` family is summable, so the
`Σ`-antidiagonal/product equivalence collapses the iterated sum directly. -/
theorem tsum_sum_antidiagonal_eq_tsum_prod (F : ℕ × ℕ → ℝ≥0∞) :
    (∑' m : ℕ, ∑ p ∈ Finset.antidiagonal m, F p) = ∑' q : ℕ × ℕ, F q := by
  rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq F, ENNReal.tsum_sigma']
  refine tsum_congr fun m => ?_
  rw [← Finset.tsum_subtype (Finset.antidiagonal m) (fun p => F p)]
  rfl

/-- **Chapman-Kolmogorov composition law.** The uniformized chemical-master-equation transition
semigroup satisfies `P_{s+t} = P_s ∘ₖ P_t`: composing the time-`s` and time-`t` kernels gives the
time-`s+t` kernel. Both sides agree on every measurable set. The time-`s+t` side expands by the
Poisson rate additivity `Λ(s+t) = Λs + Λt` and the point-mass convolution into a tsum over the
step-count antidiagonal, reindexed to a product tsum. The composed side integrates the time-`s`
superposition against the time-`t` superposition: the integral against `Measure.sum` splits into the
Poisson-weighted tsum over the step count, each inner composition `U^{∘j} ∘ₖ U^{∘k}` collapses to
`U^{∘(j+k)}` by the power law, and the two product tsums coincide. -/
theorem cmeSemigroup_comp (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    (hTfin : T.Finite) (s t : ℝ≥0) :
    N.cmeSemigroup κ hTfin (s + t) =
      N.cmeSemigroup κ hTfin s ∘ₖ N.cmeSemigroup κ hTfin t := by
  ext n A hA
  -- Common middle form `M`.
  set c : ℕ → ℝ≥0∞ := fun m => N.uniformizedPow κ hTfin m n A
  set rs := N.poissonRate κ hTfin s
  set rt := N.poissonRate κ hTfin t
  -- LHS reduces to the product tsum `M`.
  have hLHS : N.cmeSemigroup κ hTfin (s + t) n A =
      ∑' q : ℕ × ℕ, poissonMeasure rs {q.1} * poissonMeasure rt {q.2} * c (q.1 + q.2) := by
    rw [N.cmeSemigroup_apply' κ hTfin (s + t) n hA, poissonRate_add]
    rw [← tsum_sum_antidiagonal_eq_tsum_prod
      (fun q => poissonMeasure rs {q.1} * poissonMeasure rt {q.2} * c (q.1 + q.2))]
    refine tsum_congr fun m => ?_
    rw [← poissonMeasure_singleton_conv rs rt m, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    rw [hp]
  rw [hLHS]
  -- RHS reduces to the same product tsum, via the kernel power law.
  rw [Kernel.comp_apply' _ _ _ hA]
  -- Unfold `P_t n` as a `Measure.sum` and integrate term by term.
  have hPt : N.cmeSemigroup κ hTfin t n =
      Measure.sum fun k => poissonMeasure rt {k} • N.uniformizedPow κ hTfin k n := rfl
  rw [hPt, lintegral_sum_measure]
  -- Inner integrand `b ↦ P_s b A` as a lattice tsum.
  have hPs : ∀ b, N.cmeSemigroup κ hTfin s b A =
      ∑' j : ℕ, poissonMeasure rs {j} * N.uniformizedPow κ hTfin j b A := fun b =>
    N.cmeSemigroup_apply' κ hTfin s b hA
  simp_rw [lintegral_smul_measure, hPs]
  have hterm : ∀ k : ℕ,
      ∫⁻ b, ∑' j : ℕ, poissonMeasure rs {j} * N.uniformizedPow κ hTfin j b A
          ∂N.uniformizedPow κ hTfin k n =
        ∑' j : ℕ, poissonMeasure rs {j} * c (j + k) := by
    intro k
    rw [lintegral_tsum (fun j => by
      exact (measurable_const.mul ((N.uniformizedPow κ hTfin j).measurable_coe hA)).aemeasurable)]
    refine tsum_congr fun j => ?_
    rw [lintegral_const_mul _ ((N.uniformizedPow κ hTfin j).measurable_coe hA)]
    congr 1
    rw [← Kernel.comp_apply' _ _ _ hA, N.uniformizedPow_comp κ hTfin j k]
  simp_rw [hterm]
  -- Reindex the product tsum to match the iterated `k`-then-`j` order.
  rw [ENNReal.tsum_prod' (f := fun q : ℕ × ℕ =>
    poissonMeasure rs {q.1} * poissonMeasure rt {q.2} * c (q.1 + q.2)), ENNReal.tsum_comm]
  refine tsum_congr fun k => ?_
  rw [smul_eq_mul, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun j => ?_
  ring

end Network

end CRNT
