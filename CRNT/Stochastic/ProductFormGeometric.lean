import CRNT.Stochastic.ProductFormErgodic
import CRNT.Stochastic.HarrisTheorem
import CRNT.Stochastic.MonomolecularLLN
import CRNT.Stochastic.MinimalSemigroupErgodicInfinite
import CRNT.Stochastic.JumpKernel

/-!
# The product-form stationary law is strictly positive, and the complex-balanced chain is
geometrically ergodic

## The mathematical statement

Let `N` be a **weakly reversible** chemical reaction network over the species `S` with positive
rate constants `κ`, and let `x*` be a **positive complex-balanced equilibrium** of `N`.  The
Anderson–Craciun–Kurtz product form for the chemical master equation of `N` is

```
π(n) = ∏_s  exp(−x*_s) · x*_s ^ (n_s) / (n_s)!        (n ∈ ℕ^S)
```

— a product of Poisson laws, one per species, with rate the complex-balanced concentration
`x*_s`.  Two facts about it are classical (Anderson–Craciun–Kurtz, *A combinatorial theory of
chemical master equations*, J. Chem. Phys. **112** (2000) 389–403; and *Stochastic chemical
reaction networks*, SIAM J. Appl. Math. **72** (2012) 129–163):

* the product form is a **strictly positive** probability distribution on the whole count
  lattice, and it is **invariant** for the chemical master equation (the deficiency-zero
  stochastic theorem);
* the chain is **geometrically ergodic**: the law of the chain started from any count converges
  to `π` in total variation, at a geometric rate.

This module formalizes the *content* of that statement, in the vocabulary the library already
provides.

## What the repository already has

* `CRNT.Network.productPoissonPMF` (in `CRNT.Stochastic.ProductForm`) is the explicit
  product-Poisson density `∏_s exp(−c_s) c_s^{n_s} / n_s!`, and `CRNT.Network.productPoisson` is
  the corresponding product measure; `productPoissonPMF_mul_descFactorial` is the per-species
  product-form identity, and `productPoisson_detailedBalance_of_complexBalanced` reduces the
  complex-by-complex stochastic flux balance to the deterministic complex-balance equation.
* `CRNT.Network.isCMEStationary_productPoisson` and `CRNT.Network.tsum_productPoisson_mul_transition`
  (in `CRNT.Stochastic.ProductFormInvariance`) prove the invariance of the product form for the
  transition function of stochastic mass action; `CRNT.Network.hasSum_productPoissonPMF`
  (in `CRNT.Stochastic.MonomolecularLLN`) proves that it is a probability distribution;
  `CRNT.Network.productPoissonPMF_pos` (in `CRNT.Stochastic.ProductFormErgodic`) proves its
  strict positivity.
* `CRNT.Network.tendsto_transition_productPoisson` and
  `CRNT.Network.tendsto_transition_productPoisson_of_conservative`
  (in `CRNT.Stochastic.ProductFormErgodic`) give the convergence to the product form on a finite
  closed irreducible class, and from every initial count for a conservative network.
* `CRNT.Stochastic.JumpSystem.geometric_ergodic` (in `CRNT.Stochastic.HarrisTheorem`) is the
  Meyn–Tweedie `V`-uniform ergodicity theorem: under a drift certificate `QV ≤ −cV + K` with
  `c > 0`, `K ≥ 0` and `V ≥ 0` of finite sublevel sets, the minimal transition function is
  geometrically ergodic.  `CRNT.Stochastic.JumpSystem.foster_lyapunov_ergodic`
  (in `CRNT.Stochastic.MinimalSemigroupKrylovBogoliubov`) is the corresponding ergodic theorem
  with the uniqueness of the invariant law on a closed irreducible class, and
  `CRNT.Network.foster_lyapunov_ergodic_linear` (in `CRNT.Stochastic.NetworkFosterErgodic`)
  specializes it to a linear observable.
* `CRNT.Network.observableGenerator`, `CRNT.Network.linearObservable`
  (in `CRNT.Stochastic.FosterLyapunov`) are the backward generator and the linear count
  observable; `CRNT.Stochastic.JumpSystem.drift` is the generator applied to an observable.
* `CRNT.Theorems.DeficiencyZero.Existence.deficiencyZeroTheorem` delivers the positive
  complex-balanced equilibrium of a weakly reversible deficiency-zero network.

## What this module adds

* `CRNT.Stochastic.productForm_pos`: the product-form stationary law is **strictly positive** at
  every count (`CRNT.Stochastic.productForm_measure_pos` at the level of the measure,
  `CRNT.Stochastic.productForm_isProbability` at the level of the total mass), and
  `CRNT.Stochastic.jumpStationaryMass_not_pos` contrasts it with the *embedded* chain's weight,
  which vanishes at the absorbing counts.
* `CRNT.Stochastic.productForm_restricted_invariant`: for a **weakly reversible** network, the
  restriction of the product form to the class of counts reachable from the initial count is
  invariant — the general (non-irreducible) form of the product-form statement.
* `CRNT.Stochastic.productForm_unique_invariant`: the product form is the **unique invariant
  probability** of an irreducible chain, hence the invariant law of the complex-balanced chain
  is the product form and not merely *some* invariant law.
* `CRNT.Stochastic.complexBalanced_geometric_ergodic`: the **geometric ergodicity** of the
  complex-balanced chain, with the product form identified as the invariant law and the
  total-variation convergence from *every* initial count; and
  `CRNT.Stochastic.complexBalanced_geometric_ergodic_linear`, the count-weighted version for a
  positive linear observable.
* `CRNT.Stochastic.Examples.OneSpeciesComplexBalanced`: a complete, non-vacuous instance.
  For the one-species birth–death network `∅ → X`, `X → 0` the complex-balance condition is
  characterized (`κ_0 = κ_1 x*`), the multiplicative Foster–Lyapunov drift of the total count is
  *derived from it* (`QV = −κ_1 V + κ_1 x*`), the chain is irreducible, and the chain is
  geometrically ergodic with the product form `π(n) = exp(−x*) x*^{n} / n!` as its unique
  invariant law.

## What is **not** claimed here

* The **general** deficiency-zero stochastic theorem is *not* proved: for an arbitrary weakly
  reversible network with a positive complex-balanced equilibrium, the Foster–Lyapunov drift
  certificate `QV ≤ −cV + K` is **not** derived from the complex-balance condition.  The
  hypothesis is a genuine, satisfiable, standard sufficient condition (it is discharged in the
  one-species instance above), but discharging it in general requires the Anderson–Craciun–Kurtz
  *excess function* `Φ(n) = Σ_s (n_s log(x*_s/n_s) − n_s + x*_s)` and the (delicate) drift
  estimate for it; the **linear** observable `Σ_s n_s` does **not** work in general, because a
  complex-balanced network may have a species that is produced at a constant rate and consumed
  only jointly with another species, so that the total count can drift to `+∞` along a
  one-dimensional family of counts.  Concretely, the two-species network

  ```
  ∅ → A ,  A → ∅ ,  ∅ → A + B ,  A + B → ∅
  ```

  with unit rate constants is complex balanced at `x* = (1, 1)` (the balances at the complexes
  `A` and `A + B` read `κ_1 x*_A = κ_0` and `κ_3 x*_A x*_B = κ_2`), but at the counts
  `(0, k)` the drift of the total count is the constant `κ_0 + 2 κ_2 = 3` while the total count
  is `k`; hence **no** `γ > 0`, `K ≥ 0` can satisfy `QV(n) ≤ −γ V(n) + K` for the total count.
  The classical statement is therefore proved here *under the drift certificate*, and the
  certificate is derived in the one-species case.
* The **multinomial** product form of the *embedded* (jump) chain is a different object: it is
  supported on the class of counts reachable from the initial count, and is therefore **not**
  strictly positive on the whole lattice.  The strictly positive law proved here is the
  **Poisson** product form of the continuous-time chemical master equation, which is what
  `CRNT.Network.productPoissonPMF` denotes; the embedded chain's weight
  `jumpStationaryMass κ c n = productPoissonPMF c n · exitRate κ n` is the reweighted form and
  vanishes at the absorbing counts (`jumpStationaryMass_not_pos`).
* No path-measure, coupling or simulation technology is used or claimed.

Depends on:
`CRNT.Stochastic.ProductFormErgodic`, `CRNT.Stochastic.ProductFormInvariance`,
`CRNT.Stochastic.MonomolecularLLN`, `CRNT.Stochastic.HarrisTheorem`,
`CRNT.Stochastic.MinimalSemigroupErgodicInfinite`, `CRNT.Stochastic.NetworkFosterErgodic`,
`CRNT.Stochastic.JumpKernel`.
-/

open MeasureTheory Filter
open scoped BigOperators Topology

namespace CRNT

namespace Stochastic

open Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## The product-form stationary law is strictly positive -/

omit [DecidableEq S] in
/-- **The product-form stationary law is strictly positive.**  The Anderson–Craciun–Kurtz
product form `π_c(n) = ∏_s exp(−c_s) c_s^{n_s} / n_s!` of a complex-balanced network is
strictly positive at **every** count `n`, whenever the complex-balanced concentration `c` is
strictly positive.  This is the Poisson (not the multinomial) product form: the multinomial
form of the embedded chain is supported on the reachable class and is *not* strictly positive on
the whole lattice. -/
theorem productForm_pos {c : Concentration S} (hc : c.Positive) (n : S → ℕ) :
    0 < Network.productPoissonPMF c n :=
  Network.productPoissonPMF_pos hc n

omit [DecidableEq S] in
/-- The product-form stationary law is a **probability distribution** on the count lattice. -/
theorem productForm_isProbability {c : Concentration S} (hc : c.Nonnegative) :
    HasSum (Network.productPoissonPMF c) 1 :=
  Network.hasSum_productPoissonPMF hc

omit [DecidableEq S] in
/-- **Strict positivity of the product-form measure.**  The product-Poisson measure of a
complex-balanced network charges every singleton of the count lattice. -/
theorem productForm_measure_pos {c : Concentration S} (hc : c.Positive) (n : S → ℕ) :
    0 < Network.productPoisson c hc.nonnegative {n} := by
  rw [Network.productPoisson_singleton]
  exact ENNReal.ofReal_pos.mpr (Network.productPoissonPMF_pos hc n)

/-- **The embedded (jump) chain's stationary weight is the product form reweighted by the exit
rate, and it is *not* strictly positive on the whole lattice.**  This is the contrast with the
continuous-time law: the Anderson–Craciun–Kurtz *multinomial* product form of the embedded
chain is `productPoissonPMF c n · exitRate κ n`, and it vanishes at the absorbing counts (those
with vanishing exit rate), whereas the Poisson product form `productPoissonPMF c n` is strictly
positive at **every** count. -/
theorem jumpStationaryMass_not_pos {c : Concentration S} (hc : c.Positive)
    (N : Network S) (κ : RateConstants N) {n : S → ℕ} (h : N.exitRate κ n = 0) :
    N.jumpStationaryMass κ c n = 0 ∧ 0 < Network.productPoissonPMF c n := by
  constructor
  · rw [Network.jumpStationaryMass, h]
    ring
  · exact Network.productPoissonPMF_pos hc n

/-! ## The product form is the invariant law -/

/-- **The product form is invariant.**  For a complex-balanced concentration `c` the
Anderson–Craciun–Kurtz product form is invariant for the transition function of stochastic
mass action: `∑_n π_c(n) P(t)(n, m) = π_c(m)`. -/
theorem productForm_invariant (N : Network S) (κ : RateConstants N) {c : Concentration S}
    (hc : c.Positive) (hcb : N.IsComplexBalanced κ c) {t : ℝ} (ht : 0 ≤ t) (m : S → ℕ) :
    ∑' n, Network.productPoissonPMF c n * N.transition κ t n m
      = Network.productPoissonPMF c m :=
  N.tsum_productPoisson_mul_transition κ hc.nonnegative hcb ht m

section

open Classical

/-- **The product form is invariant on the reachable class of a weakly reversible network.**
For a weakly reversible network, the restriction of the Anderson–Craciun–Kurtz product form to
the class of counts reachable from `a₀` is the (unnormalized) stationary law of the chain
started from `a₀`: the product-form mass on the class is exactly the mass that the chain can
reach.  (Weak reversibility is used in the form `Network.reachPos_symm`: a count outside the
class cannot reach a count inside it.) -/
theorem productForm_restricted_invariant (N : Network S) (κ : RateConstants N)
    (hWR : N.WeaklyReversible) {c : Concentration S} (hc : c.Positive)
    (hcb : N.IsComplexBalanced κ c) {a₀ m : S → ℕ}
    (hm : (N.jumpSystem κ).ReachPos a₀ m) {t : ℝ} (ht : 0 ≤ t) :
    ∑' n, (if (N.jumpSystem κ).ReachPos a₀ n then Network.productPoissonPMF c n else 0) *
        N.transition κ t n m = Network.productPoissonPMF c m := by
  have hnot : ∀ n, ¬ (N.jumpSystem κ).ReachPos a₀ n →
      ¬ (N.jumpSystem κ).ReachPos n m := by
    intro n hna hnm
    exact hna (Relation.ReflTransGen.trans hm (N.reachPos_symm κ hWR hnm))
  have hzero : ∀ n, ¬ (N.jumpSystem κ).ReachPos a₀ n → N.transition κ t n m = 0 := by
    intro n hn
    exact N.transition_eq_zero_of_not_reachPos κ t (hnot n hn)
  have hcong : (fun n => (if (N.jumpSystem κ).ReachPos a₀ n then Network.productPoissonPMF c n
      else 0) * N.transition κ t n m) =
      (fun n => Network.productPoissonPMF c n * N.transition κ t n m) := by
    funext n
    by_cases hn : (N.jumpSystem κ).ReachPos a₀ n
    · rw [ite_eq_left hn]
    · rw [ite_eq_right hn, hzero n hn]
      ring
  exact (tsum_congr fun n => congrFun hcong n).trans
    (N.tsum_productPoisson_mul_transition κ hc.nonnegative hcb ht m)

end

/-- **The product form is the unique invariant law.**  Let the chain of a complex-balanced
network be irreducible (every count is reachable from every other through positive-rate jumps)
and non-explosive.  Then the Anderson–Craciun–Kurtz product form is the *only* invariant
probability on the count lattice: it is invariant (by `productForm_invariant`) and uniqueness
follows from `JumpSystem.invariant_unique` on the whole lattice. -/
theorem productForm_unique_invariant (N : Network S) (κ : RateConstants N)
    {c : Concentration S} (hc : c.Positive) (hcb : N.IsComplexBalanced κ c)
    (hstoch : ∀ t, 0 ≤ t → ∀ a, HasSum (fun b => (N.jumpSystem κ).Pmin t a b) 1)
    (hirr : ∀ a b, (N.jumpSystem κ).ReachPos a b)
    (μ : (S → ℕ) → ℝ) (hμ0 : ∀ b, 0 ≤ μ b) (hμ1 : HasSum μ 1)
    (hμinv : ∀ t, 0 ≤ t → ∀ b, ∑' x, μ x * (N.jumpSystem κ).Pmin t x b = μ b) :
    ∀ b, μ b = Network.productPoissonPMF c b := by
  have hπ0 : ∀ b, 0 ≤ Network.productPoissonPMF c b :=
    fun b => (Network.productPoissonPMF_pos hc b).le
  have hπE : ∀ b, b ∉ (Set.univ : Set (S → ℕ)) → Network.productPoissonPMF c b = 0 := by
    intro b hb
    exact absurd (Set.mem_univ b) hb
  have hπ1 : HasSum (Network.productPoissonPMF c) 1 :=
    Network.hasSum_productPoissonPMF hc.nonnegative
  have hinv : ∀ t, 0 ≤ t → ∀ b,
      ∑' x, Network.productPoissonPMF c x * (N.jumpSystem κ).Pmin t x b
        = Network.productPoissonPMF c b := by
    intro t ht b
    exact N.tsum_productPoisson_mul_transition κ hc.nonnegative hcb ht b
  have hE : ∀ a ∈ (Set.univ : Set (S → ℕ)), ∀ i, 0 < (N.jumpSystem κ).rate i a →
      (N.jumpSystem κ).next i a ∈ (Set.univ : Set (S → ℕ)) := by
    intro a _ i _
    exact Set.mem_univ _
  have hirr' : ∀ a ∈ (Set.univ : Set (S → ℕ)), ∀ b ∈ (Set.univ : Set (S → ℕ)),
      (N.jumpSystem κ).ReachPos a b := by
    intro a _ b _
    exact hirr a b
  have hstoch' : ∀ t, 0 ≤ t → ∀ a ∈ (Set.univ : Set (S → ℕ)),
      HasSum (fun b => (N.jumpSystem κ).Pmin t a b) 1 := by
    intro t ht a _
    exact hstoch t ht a
  have hμE : ∀ b, b ∉ (Set.univ : Set (S → ℕ)) → μ b = 0 := by
    intro b hb
    exact absurd (Set.mem_univ b) hb
  intro b
  exact (N.jumpSystem κ).invariant_unique hE hirr' hstoch' hπ0 hπE hπ1 hinv
    hμ0 hμE hμ1 hμinv b

/-! ## Geometric ergodicity of the complex-balanced chain -/

/-- **Geometric ergodicity of the chemical master equation of a complex-balanced network.**

Let `N` be a reaction network with positive rate constants `κ` and a positive complex-balanced
equilibrium `c`.  Suppose that the chain is irreducible (every count is reachable from every
other through positive-rate jumps) and that it carries a **Foster–Lyapunov drift certificate**
for a nonnegative observable `V` of finite sublevel sets,

`QV ≤ −γ V + K`  with `γ > 0` and `K ≥ 0`,

where `Q` is the backward generator (`CRNT.Stochastic.JumpSystem.drift`).  Then:

* the Anderson–Craciun–Kurtz product form `π_c` is the invariant law of the chain;
* the chain is **geometrically ergodic** in the Meyn–Tweedie `V`-uniform sense: there are
  `β > 0`, `ρ < 1` and `C₀` with
  `∑_b |P(t)(a, b) − π_c(b)| (1 + β V(b)) ≤ C₀ (1 + V(a)) ρ^{⌊t⌋}` for all `a` and `t ≥ 0`;
* from every initial count `a` the law of the chain converges to `π_c` in **total variation**.

The certificate is discharged from the complex-balance condition in the one-species instance
`CRNT.Stochastic.Examples.OneSpeciesComplexBalanced`; in general it is an extra hypothesis (see
the module docstring). -/
theorem complexBalanced_geometric_ergodic (N : Network S) (κ : RateConstants N)
    {c : Concentration S} (hc : c.Positive) (hcb : N.IsComplexBalanced κ c)
    (V : (S → ℕ) → ℝ) (hV0 : ∀ n, 0 ≤ V n)
    (hfinV : ∀ R : ℝ, {n | V n ≤ R}.Finite)
    {γ K : ℝ} (hγ : 0 < γ) (hK : 0 ≤ K)
    (hdrift : ∀ n, (N.jumpSystem κ).drift V n ≤ -γ * V n + K)
    (hirr : ∀ a b, (N.jumpSystem κ).ReachPos a b) :
    (∀ t, 0 ≤ t → ∀ m, ∑' n, Network.productPoissonPMF c n * N.transition κ t n m
        = Network.productPoissonPMF c m) ∧
    (∃ β : ℝ, 0 < β ∧ ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∃ C₀ : ℝ, ∀ a, ∀ t, 0 ≤ t →
      ∑' b, |N.transition κ t a b - Network.productPoissonPMF c b| * (1 + β * V b)
        ≤ C₀ * (1 + V a) * ρ ^ ⌊t⌋₊) ∧
    (∀ a, Tendsto (fun t => ∑' b, |N.transition κ t a b - Network.productPoissonPMF c b|)
        atTop (𝓝 0)) := by
  have hstoch : ∀ t, 0 ≤ t → ∀ n, HasSum (fun m => (N.jumpSystem κ).Pmin t n m) 1 := by
    intro t ht n
    refine (N.jumpSystem κ).hasSum_Pmin_one_of_drift_affine V hV0 hfinV
      le_rfl hK (fun m => ?_) ht n
    have h1 := hdrift m
    have h2 : 0 ≤ γ * V m := mul_nonneg hγ.le (hV0 m)
    nlinarith
  obtain ⟨π, hπ0, hπ1, hπinv, β, hβ0, ρ, hρ0, hρ1, C₀, hbound⟩ :=
    (N.jumpSystem κ).geometric_ergodic V hV0 hfinV hγ hK hdrift hstoch hirr
  have hπeq : ∀ b, π b = Network.productPoissonPMF c b := by
    intro b
    refine productForm_unique_invariant N κ hc hcb hstoch hirr π hπ0 hπ1 ?_ b
    intro t ht b
    exact hπinv t ht b
  refine ⟨?_, ?_, ?_⟩
  · intro t ht m
    exact N.tsum_productPoisson_mul_transition κ hc.nonnegative hcb ht m
  · refine ⟨β, hβ0, ρ, hρ0, hρ1, C₀, ?_⟩
    intro a t ht
    have h := hbound a t ht
    have hcong : (fun b => |(N.jumpSystem κ).Pmin t a b - π b| * (1 + β * V b)) =
        (fun b => |(N.jumpSystem κ).Pmin t a b - Network.productPoissonPMF c b| * (1 + β * V b)) := by
      funext b
      rw [hπeq b]
    show ∑' b, |(N.jumpSystem κ).Pmin t a b - Network.productPoissonPMF c b| * (1 + β * V b)
        ≤ C₀ * (1 + V a) * ρ ^ ⌊t⌋₊
    rw [← hcong]
    exact h
  · intro a
    have hE : ∀ x ∈ (Set.univ : Set (S → ℕ)), ∀ i, 0 < (N.jumpSystem κ).rate i x →
        (N.jumpSystem κ).next i x ∈ (Set.univ : Set (S → ℕ)) := by
      intro x _ i _
      exact Set.mem_univ _
    have hirr' : ∀ x ∈ (Set.univ : Set (S → ℕ)), ∀ y ∈ (Set.univ : Set (S → ℕ)),
        (N.jumpSystem κ).ReachPos x y := by
      intro x _ y _
      exact hirr x y
    have hstoch' : ∀ t, 0 ≤ t → ∀ x ∈ (Set.univ : Set (S → ℕ)),
        HasSum (fun b => (N.jumpSystem κ).Pmin t x b) 1 := by
      intro t ht x _
      exact hstoch t ht x
    have hπE : ∀ b, b ∉ (Set.univ : Set (S → ℕ)) → Network.productPoissonPMF c b = 0 := by
      intro b hb
      exact absurd (Set.mem_univ b) hb
    have hinv : ∀ t, 0 ≤ t → ∀ b,
        ∑' x, Network.productPoissonPMF c x * (N.jumpSystem κ).Pmin t x b
          = Network.productPoissonPMF c b := by
      intro t ht b
      exact N.tsum_productPoisson_mul_transition κ hc.nonnegative hcb ht b
    have hl1 := (N.jumpSystem κ).tendsto_l1_of_invariant hE hirr' hstoch'
      (fun b => (Network.productPoissonPMF_pos hc b).le) hπE
      (Network.hasSum_productPoissonPMF hc.nonnegative) hinv (Set.mem_univ a)
      (Network.productPoissonPMF_pos hc a)
    simpa only [Network.transition] using hl1

/-- **Geometric ergodicity of the complex-balanced chain in the count-weighted norm.**  The
specialization of `complexBalanced_geometric_ergodic` to a positive linear observable
`V = ∑_s w_s n_s`: the Meyn–Tweedie estimate is then the count-weighted total variation
distance. -/
theorem complexBalanced_geometric_ergodic_linear (N : Network S) (κ : RateConstants N)
    {c : Concentration S} (hc : c.Positive) (hcb : N.IsComplexBalanced κ c)
    (w : S → ℝ) (hw : ∀ s, 0 < w s) {γ K : ℝ} (hγ : 0 < γ) (hK : 0 ≤ K)
    (hdrift : ∀ n, (N.jumpSystem κ).drift (linearObservable w) n ≤
      -γ * linearObservable w n + K)
    (hirr : ∀ a b, (N.jumpSystem κ).ReachPos a b) :
    (∀ t, 0 ≤ t → ∀ m, ∑' n, Network.productPoissonPMF c n * N.transition κ t n m
        = Network.productPoissonPMF c m) ∧
    (∃ β : ℝ, 0 < β ∧ ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∃ C₀ : ℝ, ∀ a, ∀ t, 0 ≤ t →
      ∑' b, |N.transition κ t a b - Network.productPoissonPMF c b| *
          (1 + β * linearObservable w b)
        ≤ C₀ * (1 + linearObservable w a) * ρ ^ ⌊t⌋₊) ∧
    (∀ a, Tendsto (fun t => ∑' b, |N.transition κ t a b - Network.productPoissonPMF c b|)
        atTop (𝓝 0)) := by
  refine complexBalanced_geometric_ergodic N κ hc hcb (linearObservable w)
    (linearObservable_nonneg_of_positive hw)
    (fun R => (finite_linearObservable_le w hw R)) hγ hK hdrift hirr

/-! ## A complete instance: the one-species birth–death chain -/

namespace Examples
namespace OneSpeciesComplexBalanced

/-- The one-species birth–death network `∅ → X`, `X → 0`. -/
abbrev net : Network Unit :=
  ⟨Fin 2, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨0, fun _ => 1⟩ else ⟨fun _ => 1, 0⟩⟩

/-- The rate-constant assignment of the one-species birth–death network: the birth channel
`0 → X` has rate `a` and the death channel `X → 0` has rate `b`. -/
def kκ (a b : ℝ) : net.R → ℝ := fun r => if r = 0 then a else b

/-- Rate constants for the one-species birth–death network: the birth channel has rate `a`
and the death channel has rate `b`. -/
def κ (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : RateConstants net :=
  { k := kκ a b
    positive := by
      intro r
      fin_cases r
      · simp [kκ, ha]
      · simp [kκ, hb] }

theorem source_zero : (net.reaction (0 : Fin 2)).source = Complex.zero := rfl

theorem source_one : (net.reaction (1 : Fin 2)).source = (fun _ => 1) := rfl

theorem target_zero : (net.reaction (0 : Fin 2)).target = (fun _ => 1) := rfl

theorem target_one : (net.reaction (1 : Fin 2)).target = Complex.zero := rfl

theorem complex_zero_ne_one : (Complex.zero : Complex Unit) ≠ (fun _ => (1 : ℕ)) := by
  intro h
  have h1 := congrFun h ()
  simp [Complex.zero] at h1

theorem mem_complexes_iff (cc : Complex Unit) :
    cc ∈ net.complexes ↔ cc = Complex.zero ∨ cc = (fun _ => 1) := by
  constructor
  · intro hcc
    rw [net, Network.complexes, Finset.mem_union] at hcc
    rcases hcc with h | h
    · obtain ⟨r, _, he⟩ := Finset.mem_image.mp h
      fin_cases r
      · exact Or.inl he.symm
      · exact Or.inr he.symm
    · obtain ⟨r, _, he⟩ := Finset.mem_image.mp h
      fin_cases r
      · exact Or.inr he.symm
      · exact Or.inl he.symm
  · intro h
    rcases h with h | h
    · subst h
      rw [net, Network.complexes, Finset.mem_union]
      exact Or.inl (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)
    · subst h
      rw [net, Network.complexes, Finset.mem_union]
      exact Or.inr (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)

theorem massActionRate_zero (κ : RateConstants net) (c : Concentration Unit) :
    net.massActionRate κ 0 c = κ.k 0 := by
  show κ.k 0 * (net.reaction (0 : Fin 2)).source.massActionMonomial c = κ.k 0
  rw [source_zero, Complex.massActionMonomial_zero, mul_one]

theorem massActionRate_one (κ : RateConstants net) (c : Concentration Unit) :
    net.massActionRate κ 1 c = κ.k 1 * c () := by
  show κ.k 1 * (net.reaction (1 : Fin 2)).source.massActionMonomial c = κ.k 1 * c ()
  rw [source_one]
  show κ.k 1 * (∏ s : Unit, c s ^ 1) = κ.k 1 * c ()
  rw [Fintype.prod_unique]
  simp

theorem inflow_one (κ : RateConstants net) (c : Concentration Unit) :
    net.inflow κ c (fun _ => 1) = κ.k 0 := by
  show (∑ r : Fin 2, if (net.reaction r).target = (fun _ => 1) then net.massActionRate κ r c
      else 0) = κ.k 0
  rw [Fin.sum_univ_two]
  rw [ite_eq_left target_zero, ite_eq_right (by rw [target_one]; exact complex_zero_ne_one),
    add_zero]
  exact massActionRate_zero κ c

theorem outflow_one (κ : RateConstants net) (c : Concentration Unit) :
    net.outflow κ c (fun _ => 1) = κ.k 1 * c () := by
  show (∑ r : Fin 2, if (net.reaction r).source = (fun _ => 1) then net.massActionRate κ r c
      else 0) = κ.k 1 * c ()
  rw [Fin.sum_univ_two]
  rw [ite_eq_right (by rw [source_zero]; exact complex_zero_ne_one), ite_eq_left source_one,
    zero_add]
  exact massActionRate_one κ c

theorem inflow_zero (κ : RateConstants net) (c : Concentration Unit) :
    net.inflow κ c Complex.zero = κ.k 1 * c () := by
  show (∑ r : Fin 2, if (net.reaction r).target = Complex.zero then net.massActionRate κ r c
      else 0) = κ.k 1 * c ()
  rw [Fin.sum_univ_two]
  rw [ite_eq_right (by rw [target_zero]; exact fun h => complex_zero_ne_one h.symm),
    ite_eq_left target_one, zero_add]
  exact massActionRate_one κ c

theorem outflow_zero (κ : RateConstants net) (c : Concentration Unit) :
    net.outflow κ c Complex.zero = κ.k 0 := by
  show (∑ r : Fin 2, if (net.reaction r).source = Complex.zero then net.massActionRate κ r c
      else 0) = κ.k 0
  rw [Fin.sum_univ_two]
  rw [ite_eq_left source_zero, ite_eq_right (by rw [source_one]; exact complex_zero_ne_one.symm),
    add_zero]
  exact massActionRate_zero κ c

/-- **Characterization of complex balance for the one-species birth–death network.**  The
network `∅ → X`, `X → 0` is complex balanced at `c` exactly when `κ_0 = κ_1 c(X)`; the
complex-balanced concentration is then the Poisson rate of the stationary law. -/
theorem isComplexBalanced_iff (κ : RateConstants net) (c : Concentration Unit) :
    net.IsComplexBalanced κ c ↔ κ.k 0 = κ.k 1 * c () := by
  constructor
  · intro h
    have h1 := h (fun _ => 1) ((mem_complexes_iff (fun _ => 1)).mpr (Or.inr rfl))
    rw [inflow_one, outflow_one] at h1
    exact h1
  · intro h cc hcc
    rcases (mem_complexes_iff cc).mp hcc with hcc | hcc
    · subst hcc
      rw [inflow_zero, outflow_zero]
      exact h.symm
    · subst hcc
      rw [inflow_one, outflow_one]
      exact h

/-- The count vector with `m` molecules of the single species. -/
def count (m : ℕ) : Unit → ℕ := fun _ => m

theorem linearObservable_count (m : ℕ) :
    linearObservable (fun _ => (1 : ℝ)) (count m) = (m : ℝ) := by
  show (∑ s : Unit, (1 : ℝ) * (count m s : ℝ)) = (m : ℝ)
  rw [Fintype.sum_unique]
  simp [count]

theorem stochasticMassActionRate_zero (κ : RateConstants net) (m : ℕ) :
    net.stochasticMassActionRate κ (count m) 0 = κ.k 0 := by
  show κ.k 0 * (∏ s : Unit, ((count m s).descFactorial ((net.reaction 0).source s) : ℝ)) = κ.k 0
  rw [source_zero, Fintype.prod_unique]
  simp [Nat.descFactorial_zero]

theorem stochasticMassActionRate_one (κ : RateConstants net) (m : ℕ) :
    net.stochasticMassActionRate κ (count m) 1 = κ.k 1 * (m : ℝ) := by
  show κ.k 1 * (∏ s : Unit, ((count m s).descFactorial ((net.reaction 1).source s) : ℝ))
      = κ.k 1 * (m : ℝ)
  rw [source_one, Fintype.prod_unique]
  simp [count]

theorem jumpNextCount_zero (m : ℕ) :
    net.jumpNextCount (count m) 0 = count (m + 1) := by
  funext s
  simp [Network.jumpNextCount, count]

theorem jumpNextCount_one (m : ℕ) :
    net.jumpNextCount (count m) 1 = count (m - 1) := by
  funext s
  simp [Network.jumpNextCount, count]

/-- **The drift of the total count.**  For the birth–death chain the observable
`V(n) = n(X)` has the exact drift `QV(n) = κ_0 − κ_1 n(X)`. -/
theorem drift_eq (κ : RateConstants net) (m : ℕ) :
    (net.jumpSystem κ).drift (linearObservable (fun _ => (1 : ℝ))) (count m)
      = κ.k 0 - κ.k 1 * (m : ℝ) := by
  show ∑ r : Fin 2, net.stochasticMassActionRate κ (count m) r *
      (linearObservable (fun _ => (1 : ℝ)) (net.jumpNextCount (count m) r)
        - linearObservable (fun _ => (1 : ℝ)) (count m))
      = κ.k 0 - κ.k 1 * (m : ℝ)
  rw [Fin.sum_univ_two, stochasticMassActionRate_zero, stochasticMassActionRate_one,
    jumpNextCount_zero, jumpNextCount_one,
    linearObservable_count, linearObservable_count, linearObservable_count]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · rw [hm]
    simp
  · have hm1 : 1 ≤ m := hm
    rw [Nat.cast_sub hm1]
    push_cast
    ring

/-- **Irreducibility of the one-species chain.** -/
theorem reachPos_down (κ : RateConstants net) (m : ℕ) :
    (net.jumpSystem κ).ReachPos (count m) (count 0) := by
  induction m with
  | zero => exact Relation.ReflTransGen.refl
  | succ m ih =>
      refine Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single ⟨(1 : net.R), ?_, ?_⟩) ih
      · show 0 < (net.jumpSystem κ).rate (1 : net.R) (count (m + 1))
        rw [show (net.jumpSystem κ).rate (1 : net.R) (count (m + 1))
          = net.stochasticMassActionRate κ (count (m + 1)) 1 from rfl,
          stochasticMassActionRate_one]
        exact mul_pos (κ.positive 1) (by exact_mod_cast Nat.succ_pos m)
      · show count m = (net.jumpSystem κ).next (1 : net.R) (count (m + 1))
        rw [show (net.jumpSystem κ).next (1 : net.R) (count (m + 1))
          = net.jumpNextCount (count (m + 1)) 1 from rfl,
          jumpNextCount_one]
        simp

theorem reachPos_up (κ : RateConstants net) (m : ℕ) :
    (net.jumpSystem κ).ReachPos (count 0) (count m) := by
  induction m with
  | zero => exact Relation.ReflTransGen.refl
  | succ m ih =>
      refine Relation.ReflTransGen.tail ih ⟨(0 : net.R), ?_, ?_⟩
      · show 0 < (net.jumpSystem κ).rate (0 : net.R) (count m)
        rw [show (net.jumpSystem κ).rate (0 : net.R) (count m)
          = net.stochasticMassActionRate κ (count m) 0 from rfl,
          stochasticMassActionRate_zero]
        exact κ.positive 0
      · show (net.jumpSystem κ).next (0 : net.R) (count m) = count (m + 1)
        rw [show (net.jumpSystem κ).next (0 : net.R) (count m)
          = net.jumpNextCount (count m) 0 from rfl,
          jumpNextCount_zero]

theorem reachPos (κ : RateConstants net) (a b : Unit → ℕ) :
    (net.jumpSystem κ).ReachPos a b := by
  have ha : a = count (a ()) := by funext s; exact congrArg a (Subsingleton.elim s ())
  have hb : b = count (b ()) := by funext s; exact congrArg b (Subsingleton.elim s ())
  rw [ha, hb]
  exact Relation.ReflTransGen.trans (reachPos_down κ (a ())) (reachPos_up κ (b ()))

/-- **The multiplicative Foster–Lyapunov drift of the one-species chain, derived from the
complex balance.**  If `c` is a complex-balanced concentration then
`QV(n) = −κ_1 V(n) + κ_1 c(X)`, with `V(n) = n(X)`. -/
theorem foster_drift (κ : RateConstants net) (c : Concentration Unit)
    (hcb : net.IsComplexBalanced κ c) :
    ∀ n : Unit → ℕ, (net.jumpSystem κ).drift (linearObservable (fun _ => (1 : ℝ))) n
      ≤ -κ.k 1 * linearObservable (fun _ => (1 : ℝ)) n + κ.k 1 * c () := by
  intro n
  have hn : n = count (n ()) := by funext s; exact congrArg n (Subsingleton.elim s ())
  rw [hn, drift_eq, linearObservable_count]
  have h := (isComplexBalanced_iff κ c).mp hcb
  linarith

/-- **Geometric ergodicity of the one-species complex-balanced chain, with the product form
as the invariant law.**  The Anderson–Craciun–Kurtz product form
`π_c(n) = exp(−c(X)) c(X)^{n(X)} / n(X)!` is the unique invariant probability of the chain, and
the chain converges to it in the count-weighted total variation norm at a geometric rate. -/
theorem geometric_ergodic (κ : RateConstants net) (c : Concentration Unit)
    (hc : c.Positive) (hcb : net.IsComplexBalanced κ c) :
    (∀ t, 0 ≤ t → ∀ m, ∑' n, Network.productPoissonPMF c n * net.transition κ t n m
        = Network.productPoissonPMF c m) ∧
    (∃ β : ℝ, 0 < β ∧ ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∃ C₀ : ℝ, ∀ a, ∀ t, 0 ≤ t →
      ∑' b, |net.transition κ t a b - Network.productPoissonPMF c b| *
          (1 + β * linearObservable (fun _ => (1 : ℝ)) b)
        ≤ C₀ * (1 + linearObservable (fun _ => (1 : ℝ)) a) * ρ ^ ⌊t⌋₊) ∧
    (∀ a, Tendsto (fun t => ∑' b, |net.transition κ t a b - Network.productPoissonPMF c b|)
        atTop (𝓝 0)) := by
  refine complexBalanced_geometric_ergodic_linear net κ hc hcb (fun _ => (1 : ℝ))
    (fun _ => one_pos) (γ := κ.k 1) (K := κ.k 1 * c ()) (κ.positive 1)
    (mul_nonneg (κ.positive 1).le (hc ()).le) (foster_drift κ c hcb) (reachPos κ)

/-- **The product form of the one-species chain is the Poisson law of rate `c(X)`.** -/
theorem productPoissonPMF_count (c : Concentration Unit) (m : ℕ) :
    Network.productPoissonPMF c (count m)
      = Real.exp (-(c ())) * (c ()) ^ m / m.factorial := by
  show (∏ s : Unit, Real.exp (-(c s)) * (c s) ^ (count m s) / (count m s).factorial)
      = Real.exp (-(c ())) * (c ()) ^ m / m.factorial
  rw [Fintype.prod_unique]
  simp [count]

/-- **The product form of the one-species chain is strictly positive at every count.** -/
theorem productForm_pos (c : Concentration Unit) (hc : c.Positive) (m : ℕ) :
    0 < Network.productPoissonPMF c (count m) := by
  rw [productPoissonPMF_count]
  exact div_pos (mul_pos (Real.exp_pos _) (pow_pos (hc ()) m))
    (by exact_mod_cast (Nat.factorial_pos m))

end OneSpeciesComplexBalanced
end Examples

#print axioms CRNT.Stochastic.productForm_pos
#print axioms CRNT.Stochastic.productForm_isProbability
#print axioms CRNT.Stochastic.productForm_measure_pos
#print axioms CRNT.Stochastic.jumpStationaryMass_not_pos
#print axioms CRNT.Stochastic.productForm_invariant
#print axioms CRNT.Stochastic.productForm_restricted_invariant
#print axioms CRNT.Stochastic.productForm_unique_invariant
#print axioms CRNT.Stochastic.complexBalanced_geometric_ergodic
#print axioms CRNT.Stochastic.complexBalanced_geometric_ergodic_linear
#print axioms CRNT.Stochastic.Examples.OneSpeciesComplexBalanced.isComplexBalanced_iff
#print axioms CRNT.Stochastic.Examples.OneSpeciesComplexBalanced.foster_drift
#print axioms CRNT.Stochastic.Examples.OneSpeciesComplexBalanced.geometric_ergodic
#print axioms CRNT.Stochastic.Examples.OneSpeciesComplexBalanced.productForm_pos

end Stochastic
end CRNT
