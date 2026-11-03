import CRNT.Algebra.TropicalReduction
import CRNT.Algebra.TropicalLiftingNetwork
import CRNT.Dynamics.MassActionField
import CRNT.Dynamics.TikhonovLocal
import CRNT.Dynamics.SlowFast
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The tropical equilibration as the leading term of the slow–fast decomposition

This module closes the link between the two developments of leaf **A4** (tropical model
reduction):

* `CRNT.Algebra.TropicalReduction` formalises the tropical order of a reaction at a
  valuation, the tropical equilibration condition, and the reduced network of tropically
  minimal reactions;
* `CRNT.Dynamics.TikhonovLocal` formalises the *local* Tikhonov theorem: a `C¹` fast field
  with a Hurwitz fibre derivative has a local `C¹` slow manifold `y = h (x)` with
  `g (x, h x) = 0`, and the coupled dynamics tracks that manifold.

The missing link was the statement of the literature (Noel–Grigoriev–Vakulenko–Radulescu
2012; Samal–Fré–Perez–Ramos–Sottile–Trenz 2015; Craciun's *tropical differential
inclusion*):

> A tropical equilibration is the leading term of the slow–fast decomposition of the
> mass-action dynamics.

## The mathematics being formalised

Let `N` be a network, `κ̄` its rate constants, `a : N.R → ℝ` the *orders* of the rates
(`κ_r = κ̄_r ε^{a_r}`) and `w : S → ℝ` a *valuation* of the species
(`x_s = ε^{w_s} y_s`).  Writing `d_r = a_r + ⟨y_r, w⟩` for the tropical order of the
reaction `r` (this is `Network.tropicalOrder`), the `ε`-rescaled mass-action field is

```
ẏ_s = ∑_r κ̄_r ε^{d_r - w_s} (y^{y_r}) y_{r,s} ,
```

so the *leading part* of the equation of species `s` consists of the reactions of
*minimal tropical order*.  The **tropical (leading) field**

```
L_s (y) = ∑_{r : r is tropically minimal for s} κ̄_r (y^{y_r}) y_{r,s}
```

is the `ε → 0⁺` limit of the rescaled field after division by `ε^{d_{r₀} - w_s}`, where
`r₀` is any reaction that is tropically minimal for `s`
(`Network.tropicalLeadingField_leading`).  This is the formal content of "the tropical
system is the leading part of the rescaled mass-action field".

The *tropical equilibration* says that in every species equation the leading part has
summands of **both signs** (`Network.tropicalLeadingField_signs`): without this the
leading equation could not vanish and no steady state could exist.

## The slow–fast structure

The exponents `d_{r₀} - w_s` are the *time scales* of the species.  A species with
`d_{r₀} = w_s` is **slow** (its equation has no small factor), a species with
`d_{r₀} = w_s + c`, `c > 0`, is **fast** (its equation acquires the factor `ε^c`).
Writing `S = X ⊕ E` for the split of the species into slow (`X`) and fast (`E`) groups, the
tropical system is the slow–fast system

```
ẋ = f (x, y)  =  Network.tropicalSlowField N κ a w x y
ε^c ẏ = g (x, y)  =  Network.tropicalFastField N κ a w x y ,
```

whose **critical manifold** is `{y | g (x, y) = 0}` — precisely the tropical constraint
on the fast species.  `Network.tropical_critical_manifold` then produces the local `C¹`
slow manifold `h` through the tropical critical point, and
`Network.tropical_reduction_estimate` gives the quantitative statement that the coupled
dynamics tracks it.

Finally `Network.tropical_reduced_equilibrium` shows that a positive root of the tropical
leading system is an **equilibrium of the reduced system**: the tropical equilibration
determines the steady state of the reduced dynamics.

## What is proved here

1. `Network.IsTropicallyMinimal`, `Network.isTropicallyMinimal_iff`,
   `Network.tropicalOrder_eq_of_minimal` — the tropical minimality of a reaction for a
   species, in terms of the tropical order.
2. `Network.scaledRates`, `Network.scaledMassActionField`,
   `Network.massActionMonomial_scaled`, `Network.scaledMassActionField_eq` — the
   `ε`-rescaled mass-action field and the identity identifying it with the `ε`-rescaling of
   the original mass-action dynamics.
3. `Network.tropicalLeadingTerm`, `Network.tropicalMinimal`,
   `Network.mem_tropicalMinimal`, `Network.tropicalMinimal_subset_reduced`,
   `Network.tropicalLeadingField`, `Network.tropicalLeadingField_eq_sum_reduced` — the
   tropical (leading) system: the leading part of the rescaled field, computed over the
   tropically minimal reactions, i.e. over the reduced network of Samal et al.
4. `Network.tropicalLeadingField_leading`, `Network.tropicalLeadingField_leading_of_tendsto`
   — **the tropical system is the leading term of the rescaled mass-action field**: the
   rescaled field of a species, divided by `ε^{d_{r₀} - w_s}` (where `r₀` is tropically
   minimal for that species), converges to the tropical leading field as `ε → 0⁺`.
5. `Network.tropicalLeadingField_signs` — **the tropical equilibration is the
   sign-indeterminacy of the leading system**: in every species equation changed by some
   reaction, the leading part has a strictly positive and a strictly negative summand.
6. `Network.tropicalLeadingField_zero_of_scaledSteadyState` — **a positive root of the
   tropical leading system**: if the scaled network has a family of steady states
   `x(t) = t^w ψ(t)` with `ψ(t) → ξ` and `ξ` positive, then `ξ` solves the tropical
   leading system.  (This is the bridge to `CRNT.Algebra.TropicalLiftingNetwork`.)
7. `Network.embedConcentration`, `Network.tropicalFastField`, `Network.tropicalSlowField`,
   `Network.tropicalLeadingField_contDiff`, `Network.embedConcentration_contDiff`,
   `Network.tropicalFastField_contDiffAt` — the slow–fast structure extracted from the
   tropical data, and its regularity.
8. `Network.HurwitzRate'`, `Network.hurwitzRate'_injective`,
   `Network.hurwitzRate'_isInvertible`, `Network.hurwitz_linear_decay'` — the Hurwitz
   condition on a linearisation of a concentration space, written with the explicit
   Euclidean inner product (see *What remains* below for why), and the exponential decay
   of the linearised fast system.
9. `Network.fiberDeriv'`, `Network.tropical_critical_manifold`,
   `Network.tropical_critical_manifold_hurwitz`,
   `Network.tropical_critical_manifold_unique` — **the critical manifold of the tropical
   reduced system**: at a tropical critical point `(x₀, y₀)` (a zero of the tropical fast
   field) whose linearisation is Hurwitz, there is a unique local `C¹` slow manifold `h`
   with `h x₀ = y₀` and `g (x, h x) = 0`; the critical manifold of the reduced system is
   exactly the tropical constraint on the fast species.
10. `Network.tropical_reduction_estimate` — **the reduction**: for the tropical slow–fast
    system `ẋ = f (x, y)`, `ε ẏ = g (x, y)`, the fast variable tracks the slow manifold
    with an `O (ε)` error, `∑ b, (y t b - h (x t) b)² ≤ e^{-(μ/ε) t} ∑ b, (y 0 b - h (x 0) b)² +
    (ε G / μ)²`.
11. `Network.tropical_reduced_equilibrium` — **the tropical equilibration determines the
    equilibrium of the reduced system**: a positive root of the tropical leading system is
    an equilibrium of `ẋ = f (x, h x)`.
12. `Network.tropical_linear_reduced_converges` — the *linear* case: if the reduced system
    is linear with a Hurwitz Jacobian, its solution converges exponentially to the tropical
    equilibrium.
13. `Network.TropicalSlowFastInstance` — a concrete instance: the chain `∅ → X → Y → ∅`
    with the orders `a = (0, 0, 1)` and the valuation `w = (0, -1)`; `ex_isEquil` shows
    that `w` is a tropical equilibration and `ex_timeScales` that the chain is a genuine
    two-tier slow–fast system (time scales `0` and `1`).

## What remains

* **The tube hypothesis.** `Network.tropical_reduction_estimate` assumes, as
  `CRNT.SlowFast.fast_deviation_le` does, that the coupled solution stays in the region
  where the fast field contracts toward the slow manifold.  Discharging it requires the
  graph-transform machinery of `CRNT.Dynamics.FenichelPersistence`.
* **The inner product on a concentration space.** `CRNT.Dynamics.TikhonovLocal` states its
  Hurwitz condition and its fast-deviation estimate for an *inner product space*; the
  concentration space `E → ℝ` of a network is a `Pi` type, for which Mathlib's `Pi` module
  structure and the one induced by an inner product structure do not coincide (the
  `Pi` type has no `InnerProductSpace` instance, and `EuclideanSpace` is not definitionally
  a `Pi` type).  This module therefore uses the *explicit* Euclidean inner product
  `∑ e, u e * v e` (`Network.HurwitzRate'`) and the corresponding global estimate
  `CRNT.SlowFast.fast_deviation_le`.  Re-casting the results in the framework of
  `CRNT.Dynamics.TikhonovLocal` would require a `NormedSpace`/`InnerProductSpace`
  structure on concentration spaces compatible with the `Pi` module structure.
* **Uniformity in the slow variable.** The Hurwitz hypothesis is read at the tropical
  critical point; extending the local contraction to a whole neighbourhood of the slow
  manifold (in the `x` variable) requires a uniform estimate on the family
  `∂_y g (x, h x)`.
* **The `ε`-dependent Fenichel manifold** and the **slow error** in the local setting.
* **Multi-tier tropical data.** Only two tiers (slow and fast) are treated here; a
  network with several distinct exponents `d_{r₀} - w_s` gives a multi-scale system.

Depends on: `CRNT.Algebra.TropicalReduction`, `CRNT.Algebra.TropicalLiftingNetwork`,
`CRNT.Dynamics.MassActionField`, `CRNT.Dynamics.TikhonovLocal`, `CRNT.Dynamics.SlowFast`.
-/

namespace CRNT

namespace Network

open Filter Topology Set

open scoped BigOperators RealInnerProductSpace

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## 1. Tropical minimality of a reaction for a species -/

/-- **Tropical minimality.**  The reaction `r` is *tropically minimal* for the species `s`
if it changes `s` and its tropical order `a_r + ⟨y_r, w⟩` is at most that of every
reaction changing `s`.  These are exactly the reactions kept by the tropical reduction
of Samal et al. (`Network.tropicalReduced`). -/
def IsTropicallyMinimal (N : Network S) (a : N.R → ℝ) (w : S → ℝ) (r : N.R) (s : S) : Prop :=
  N.reactionVector r s ≠ 0 ∧
    ∀ r' : N.R, N.reactionVector r' s ≠ 0 → tropicalOrder N a w r ≤ tropicalOrder N a w r'

/-- **Tropical minimality is characterised by the tropical order.**  If `r₀` is tropically
minimal for `s`, then `r` is tropically minimal for `s` exactly when `r` changes `s` and
has the same tropical order as `r₀`. -/
theorem isTropicallyMinimal_iff (N : Network S) (a : N.R → ℝ) (w : S → ℝ) {r₀ r : N.R}
    {s : S} (hr₀ : IsTropicallyMinimal N a w r₀ s) :
    IsTropicallyMinimal N a w r s ↔
      N.reactionVector r s ≠ 0 ∧ tropicalOrder N a w r = tropicalOrder N a w r₀ := by
  constructor
  · intro hr
    refine ⟨hr.1, ?_⟩
    have h1 := hr.2 r₀ hr₀.1
    have h2 := hr₀.2 r hr.1
    exact le_antisymm h1 h2
  · rintro ⟨hr, hord⟩
    refine ⟨hr, fun r' hr' => ?_⟩
    have h1 := hr₀.2 r' hr'
    rw [← hord] at h1
    exact h1

/-- Two tropically minimal reactions for the same species have the same tropical order. -/
theorem tropicalOrder_eq_of_minimal (N : Network S) (a : N.R → ℝ) (w : S → ℝ) {r r₀ : N.R}
    {s : S} (hr : IsTropicallyMinimal N a w r s) (hr₀ : IsTropicallyMinimal N a w r₀ s) :
    tropicalOrder N a w r = tropicalOrder N a w r₀ :=
  ((isTropicallyMinimal_iff N a w hr₀).mp hr).2

/-! ## 2. The `ε`-rescaled mass-action field -/

/-- **Rate constants scaled by powers of `ε`.**  `scaledRates N κ a ε` has rate constant
`κ̄_r ε^{a_r}` (with `ε^{a_r} = exp (a_r log ε)`). -/
noncomputable def scaledRates (N : Network S) (κ : RateConstants N) (a : N.R → ℝ)
    (ε : ℝ) : RateConstants N :=
  ⟨fun r => κ.k r * Real.exp ((a r) * Real.log ε),
    fun r => mul_pos (κ.positive r) (Real.exp_pos _)⟩

/-- **The `ε`-rescaled mass-action field.**  If the concentrations of the network scale as
`x_s = ε^{w_s} y_s` and the rate constants as `κ̄_r ε^{a_r}`, then the dynamics of the
rescaled variables `y` is

```
ẏ_s = ∑_r κ̄_r ε^{d_r - w_s} (y^{y_r}) y_{r,s} ,   d_r = a_r + ⟨y_r, w⟩ ,
```

which is `scaledMassActionField N κ a w ε y`. -/
noncomputable def scaledMassActionField (N : Network S) (κ : RateConstants N) (a : N.R → ℝ)
    (w : S → ℝ) (ε : ℝ) (y : Concentration S) : S → ℝ :=
  fun s => ∑ r : N.R, κ.k r * Real.exp ((tropicalOrder N a w r - w s) * Real.log ε) *
      (N.reaction r).source.massActionMonomial y * N.reactionVector r s

/-- **The scaled monomial.**  Scaling the concentrations by `ε^{w_s}` multiplies the
mass-action monomial of a reaction by `ε^{⟨y_r, w⟩}`. -/
theorem massActionMonomial_scaled (N : Network S) (r : N.R) (ε : ℝ) (w : S → ℝ)
    (y : Concentration S) :
    (N.reaction r).source.massActionMonomial (fun t => Real.exp ((w t) * Real.log ε) * y t) =
      Real.exp ((∑ t : S, ((N.reaction r).source t : ℝ) * w t) * Real.log ε) *
        (N.reaction r).source.massActionMonomial y := by
  classical
  have hsplit : (N.reaction r).source.massActionMonomial
        (fun t => Real.exp ((w t) * Real.log ε) * y t) =
      (∏ t : S, Real.exp ((((N.reaction r).source t : ℕ) : ℝ) * w t * Real.log ε)) *
        (N.reaction r).source.massActionMonomial y := by
    simp only [Complex.massActionMonomial]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [mul_pow, ← Real.exp_nat_mul]
    have h1 : ((N.reaction r).source t : ℕ) * ((w t) * Real.log ε) =
        (((N.reaction r).source t : ℝ) * w t) * Real.log ε := by
      ring
    rw [h1]
  rw [hsplit, ← Real.exp_sum]
  have hsum : (∑ t : S, (((N.reaction r).source t : ℕ) : ℝ) * w t * Real.log ε) =
      (∑ t : S, (((N.reaction r).source t : ℕ) : ℝ) * w t) * Real.log ε := by
    calc (∑ t : S, (((N.reaction r).source t : ℕ) : ℝ) * w t * Real.log ε)
        = ∑ t : S, ((((N.reaction r).source t : ℕ) : ℝ) * w t) * Real.log ε := by
          refine Finset.sum_congr rfl fun t _ => ?_
          ring
      _ = (∑ t : S, (((N.reaction r).source t : ℕ) : ℝ) * w t) * Real.log ε :=
          (Finset.sum_mul (Finset.univ : Finset S)
            (fun t => (((N.reaction r).source t : ℕ) : ℝ) * w t) (Real.log ε)).symm
  rw [hsum]

/-- **The rescaled field is the `ε`-rescaling of the mass-action field.**  For `ε > 0` and
`x_s = ε^{w_s} y_s`,

```
scaledMassActionField N κ a w ε y s
  = ε^{-w_s} (mass-action field of the ε-scaled rates at x) s .
```

This identifies the rescaled field with the mass-action dynamics of the network with
rates `κ̄_r ε^{a_r}`, in the variables `y_s = ε^{-w_s} x_s`. -/
theorem scaledMassActionField_eq (N : Network S) (κ : RateConstants N) (a : N.R → ℝ)
    (w : S → ℝ) (ε : ℝ) (y : Concentration S) (s : S) :
    scaledMassActionField N κ a w ε y s =
      Real.exp (-(w s) * Real.log ε) *
        N.massActionVectorField (scaledRates N κ a ε)
          (fun t => Real.exp ((w t) * Real.log ε) * y t) s := by
  classical
  have hRHS : Real.exp (-(w s) * Real.log ε) *
      N.massActionVectorField (scaledRates N κ a ε)
        (fun t => Real.exp ((w t) * Real.log ε) * y t) s =
      ∑ r : N.R, (Real.exp (-(w s) * Real.log ε) *
          (Real.exp ((a r) * Real.log ε) *
            (N.reaction r).source.massActionMonomial
              (fun t => Real.exp ((w t) * Real.log ε) * y t))) *
        κ.k r * N.reactionVector r s := by
    simp only [massActionVectorField_apply, massActionRate]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [scaledRates]
    ring
  rw [hRHS]
  simp only [scaledMassActionField]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hprod := massActionMonomial_scaled N r ε w y
  have hexp1 : Real.exp ((a r) * Real.log ε) *
      Real.exp ((∑ t : S, ((N.reaction r).source t : ℝ) * w t) * Real.log ε) =
    Real.exp ((tropicalOrder N a w r) * Real.log ε) := by
    rw [← Real.exp_add]
    congr 1
    simp only [tropicalOrder]
    ring
  have hexp2 : Real.exp (-(w s) * Real.log ε) * Real.exp ((tropicalOrder N a w r) * Real.log ε) =
      Real.exp ((tropicalOrder N a w r - w s) * Real.log ε) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hAB : Real.exp (-(w s) * Real.log ε) *
        (Real.exp ((a r) * Real.log ε) *
          (Real.exp ((∑ t : S, ((N.reaction r).source t : ℝ) * w t) * Real.log ε) *
            (N.reaction r).source.massActionMonomial y)) =
      Real.exp ((tropicalOrder N a w r - w s) * Real.log ε) *
        (N.reaction r).source.massActionMonomial y := by
    calc _ = Real.exp (-(w s) * Real.log ε) *
          ((Real.exp ((a r) * Real.log ε) *
            Real.exp ((∑ t : S, ((N.reaction r).source t : ℝ) * w t) * Real.log ε)) *
              (N.reaction r).source.massActionMonomial y) := by
              rw [mul_assoc]
        _ = Real.exp (-(w s) * Real.log ε) *
            (Real.exp ((tropicalOrder N a w r) * Real.log ε) *
              (N.reaction r).source.massActionMonomial y) := by
              rw [hexp1]
        _ = Real.exp ((tropicalOrder N a w r - w s) * Real.log ε) *
            (N.reaction r).source.massActionMonomial y := by
              rw [← mul_assoc, hexp2]
  rw [hprod, hAB]
  ring

/-! ## 3. The tropical (leading) field -/

/-- **The leading summand.**  The contribution of the reaction `r` to the leading part of
the equation of the species `s`. -/
noncomputable def tropicalLeadingTerm (N : Network S) (κ : RateConstants N)
    (s : S) (r : N.R) (y : Concentration S) : ℝ :=
  κ.k r * (N.reaction r).source.massActionMonomial y * N.reactionVector r s

/-- **The tropically minimal reactions for a species.**  These are the reactions kept by the
tropical reduction of Samal et al. for the species `s`. -/
noncomputable def tropicalMinimal (N : Network S) (a : N.R → ℝ) (w : S → ℝ) (s : S) :
    Finset N.R := by
  classical
  exact Finset.univ.filter (fun r : N.R => IsTropicallyMinimal N a w r s)

/-- A reaction is tropically minimal for `s` exactly when it belongs to `tropicalMinimal`. -/
theorem mem_tropicalMinimal (N : Network S) (a : N.R → ℝ) (w : S → ℝ) (r : N.R) (s : S) :
    r ∈ tropicalMinimal N a w s ↔ IsTropicallyMinimal N a w r s := by
  classical
  simp only [tropicalMinimal, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **The tropically minimal reactions are among the reduced reactions.** -/
theorem tropicalMinimal_subset_reduced (N : Network S) (a : N.R → ℝ) (w : S → ℝ) (s : S) :
    tropicalMinimal N a w s ⊆ tropicalReduced N a w := by
  classical
  intro r hr
  rw [tropicalReduced_mem]
  have h := (mem_tropicalMinimal N a w r s).mp hr
  exact ⟨s, h.1, h.2⟩

/-- **The tropical (leading) field.**  `tropicalLeadingField N κ a w y s` is the leading
part of the `ε`-rescaled mass-action equation of the species `s`: the sum of the
contributions of the reactions that are *tropically minimal* for `s`.  This is the
*tropical system* of Samal et al. -/
noncomputable def tropicalLeadingField (N : Network S) (κ : RateConstants N) (a : N.R → ℝ)
    (w : S → ℝ) (y : Concentration S) : S → ℝ :=
  fun s => ∑ r ∈ tropicalMinimal N a w s, tropicalLeadingTerm N κ s r y

/-- **The leading field of a species is the sum over the reduced network.**  The reactions
that contribute to the leading part of the equation of `s` are exactly the tropically
minimal ones, i.e. the reactions of the reduced network `Network.tropicalReduced`. -/
theorem tropicalLeadingField_eq_sum_reduced (N : Network S) (κ : RateConstants N)
    (a : N.R → ℝ) (w : S → ℝ) (y : Concentration S) (s : S) :
    tropicalLeadingField N κ a w y s =
      ∑ r ∈ tropicalMinimal N a w s, tropicalLeadingTerm N κ s r y := rfl

/-- **The tropical system is the leading term of the rescaled mass-action field.**  Let
`r₀` be a reaction that is tropically minimal for the species `s`.  Then the rescaled
field of `s`, divided by `ε^{d_{r₀} - w_s}`, converges to the tropical leading field as
`ε → 0⁺`. -/
theorem tropicalLeadingField_leading (N : Network S) (κ : RateConstants N) (a : N.R → ℝ)
    (w : S → ℝ) (y : Concentration S) (s : S) (r₀ : N.R)
    (hr₀ : IsTropicallyMinimal N a w r₀ s) :
    Tendsto (fun ε : ℝ => scaledMassActionField N κ a w ε y s /
        Real.exp ((tropicalOrder N a w r₀ - w s) * Real.log ε))
      (𝓝[>] 0) (𝓝 (tropicalLeadingField N κ a w y s)) := by
  classical
  -- the summands after normalisation
  have hterm : ∀ (r : N.R) (ε : ℝ),
      (κ.k r * Real.exp ((tropicalOrder N a w r - w s) * Real.log ε) *
          (N.reaction r).source.massActionMonomial y * N.reactionVector r s) /
          Real.exp ((tropicalOrder N a w r₀ - w s) * Real.log ε) =
        κ.k r * Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) * Real.log ε) *
          (N.reaction r).source.massActionMonomial y * N.reactionVector r s := by
    intro r ε
    rw [div_eq_mul_inv]
    have hexp : Real.exp ((tropicalOrder N a w r - w s) * Real.log ε) *
          (Real.exp ((tropicalOrder N a w r₀ - w s) * Real.log ε))⁻¹ =
        Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) * Real.log ε) := by
      rw [← div_eq_mul_inv, ← Real.exp_sub]
      congr 1
      ring
    have hreassoc : κ.k r * Real.exp ((tropicalOrder N a w r - w s) * Real.log ε) *
          (N.reaction r).source.massActionMonomial y * N.reactionVector r s *
          (Real.exp ((tropicalOrder N a w r₀ - w s) * Real.log ε))⁻¹ =
        κ.k r * (Real.exp ((tropicalOrder N a w r - w s) * Real.log ε) *
          (Real.exp ((tropicalOrder N a w r₀ - w s) * Real.log ε))⁻¹) *
          (N.reaction r).source.massActionMonomial y * N.reactionVector r s := by ring
    rw [hreassoc, hexp]
  have hnorm : ∀ ε : ℝ, scaledMassActionField N κ a w ε y s /
        Real.exp ((tropicalOrder N a w r₀ - w s) * Real.log ε) =
      ∑ r : N.R, κ.k r * Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) *
          Real.log ε) * (N.reaction r).source.massActionMonomial y * N.reactionVector r s := by
    intro ε
    simp only [scaledMassActionField]
    have hdiv : (∑ r : N.R, κ.k r * Real.exp ((tropicalOrder N a w r - w s) * Real.log ε) *
          (N.reaction r).source.massActionMonomial y * N.reactionVector r s) /
          Real.exp ((tropicalOrder N a w r₀ - w s) * Real.log ε) =
        ∑ r : N.R, (κ.k r * Real.exp ((tropicalOrder N a w r - w s) * Real.log ε) *
          (N.reaction r).source.massActionMonomial y * N.reactionVector r s) /
          Real.exp ((tropicalOrder N a w r₀ - w s) * Real.log ε) := by
      rw [div_eq_mul_inv, Finset.sum_mul]
      exact Finset.sum_congr rfl fun r _ => by rw [div_eq_mul_inv]
    rw [hdiv]
    exact Finset.sum_congr rfl fun r _ => hterm r ε
  -- split the sum into the minimal and the non-minimal reactions
  have hsplit : ∀ ε : ℝ,
      ∑ r : N.R, κ.k r * Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) *
          Real.log ε) * (N.reaction r).source.massActionMonomial y * N.reactionVector r s =
        (∑ r ∈ tropicalMinimal N a w s,
          κ.k r * Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) * Real.log ε) *
            (N.reaction r).source.massActionMonomial y * N.reactionVector r s) +
        ∑ r ∈ Finset.univ.filter (fun r : N.R => ¬ IsTropicallyMinimal N a w r s),
          κ.k r * Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) * Real.log ε) *
            (N.reaction r).source.massActionMonomial y * N.reactionVector r s := by
    intro ε
    simp only [tropicalMinimal]
    rw [Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun r : N.R => IsTropicallyMinimal N a w r s)]
  -- the minimal reactions contribute a constant
  have hmin : ∀ r ∈ tropicalMinimal N a w s,
      Tendsto (fun ε : ℝ => κ.k r * Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) *
          Real.log ε) * (N.reaction r).source.massActionMonomial y * N.reactionVector r s)
        (𝓝[>] 0) (𝓝 (tropicalLeadingTerm N κ s r y)) := by
    intro r hr
    have hrP : IsTropicallyMinimal N a w r s := (mem_tropicalMinimal N a w r s).mp hr
    have hord : tropicalOrder N a w r = tropicalOrder N a w r₀ :=
      ((isTropicallyMinimal_iff N a w hr₀).mp hrP).2
    have hexp0 : ∀ ε : ℝ, Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) *
        Real.log ε) = 1 := by
      intro ε
      rw [hord, sub_self]
      simp
    have hconst : ∀ ε : ℝ, κ.k r * Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) *
        Real.log ε) * (N.reaction r).source.massActionMonomial y * N.reactionVector r s =
        tropicalLeadingTerm N κ s r y := by
      intro ε
      rw [hexp0]
      unfold tropicalLeadingTerm
      ring
    rw [show (fun ε : ℝ => κ.k r * Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) *
          Real.log ε) * (N.reaction r).source.massActionMonomial y * N.reactionVector r s)
        = (fun _ : ℝ => tropicalLeadingTerm N κ s r y) from funext hconst]
    exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => tropicalLeadingTerm N κ s r y)
      (𝓝 (0 : ℝ)) (𝓝 (tropicalLeadingTerm N κ s r y))).mono_left nhdsWithin_le_nhds
  -- the non-minimal reactions vanish
  have hnonmin : ∀ r ∈ Finset.univ.filter (fun r : N.R => ¬ IsTropicallyMinimal N a w r s),
      Tendsto (fun ε : ℝ => κ.k r * Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) *
          Real.log ε) * (N.reaction r).source.massActionMonomial y * N.reactionVector r s)
        (𝓝[>] 0) (𝓝 0) := by
    intro r hr
    by_cases hrv : N.reactionVector r s = 0
    · have hzero : ∀ ε : ℝ, κ.k r * Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) *
          Real.log ε) * (N.reaction r).source.massActionMonomial y * N.reactionVector r s = 0 := by
        intro ε
        rw [hrv, mul_zero]
      rw [show (fun ε : ℝ => κ.k r * Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) *
            Real.log ε) * (N.reaction r).source.massActionMonomial y * N.reactionVector r s)
          = (fun _ : ℝ => (0 : ℝ)) from funext hzero]
      exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝 (0 : ℝ)) (𝓝 0)).mono_left
        nhdsWithin_le_nhds
    · have hrP : ¬ IsTropicallyMinimal N a w r s := (Finset.mem_filter.mp hr).2
      by_cases hord : tropicalOrder N a w r = tropicalOrder N a w r₀
      · exfalso
        exact hrP ((isTropicallyMinimal_iff N a w hr₀).mpr ⟨hrv, hord⟩)
      · have hgt : tropicalOrder N a w r₀ < tropicalOrder N a w r := by
          have hle := hr₀.2 r hrv
          exact lt_of_le_of_ne hle (Ne.symm hord)
        have hlim : Tendsto (fun ε : ℝ =>
            Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) * Real.log ε))
            (𝓝[>] 0) (𝓝 0) := by
          have h1 : Tendsto (fun ε : ℝ =>
              (tropicalOrder N a w r - tropicalOrder N a w r₀) * Real.log ε)
              (𝓝[>] 0) atBot :=
            Filter.Tendsto.const_mul_atBot (by linarith) Real.tendsto_log_nhdsGT_zero
          exact Real.tendsto_exp_atBot.comp h1
        have h2 := hlim.mul_const
          (κ.k r * (N.reaction r).source.massActionMonomial y * N.reactionVector r s)
        have heq : ∀ ε : ℝ, Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) *
              Real.log ε) * (κ.k r * (N.reaction r).source.massActionMonomial y *
                N.reactionVector r s) =
            κ.k r * Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) * Real.log ε) *
              (N.reaction r).source.massActionMonomial y * N.reactionVector r s := by
          intro ε
          ring
        have h3 := h2.congr' (Filter.Eventually.of_forall heq)
        simpa using h3
  -- assemble
  have h1 : Tendsto (fun ε : ℝ => ∑ r ∈ tropicalMinimal N a w s,
        κ.k r * Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) * Real.log ε) *
          (N.reaction r).source.massActionMonomial y * N.reactionVector r s)
      (𝓝[>] 0) (𝓝 (∑ r ∈ tropicalMinimal N a w s, tropicalLeadingTerm N κ s r y)) :=
    tendsto_finsetSum (s := tropicalMinimal N a w s)
      (f := fun r (ε : ℝ) => κ.k r *
        Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) * Real.log ε) *
          (N.reaction r).source.massActionMonomial y * N.reactionVector r s)
      (x := 𝓝[>] 0) hmin
  have h2 : Tendsto (fun ε : ℝ => ∑ r ∈ Finset.univ.filter
        (fun r : N.R => ¬ IsTropicallyMinimal N a w r s),
        κ.k r * Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) * Real.log ε) *
          (N.reaction r).source.massActionMonomial y * N.reactionVector r s)
      (𝓝[>] 0)
      (𝓝 (∑ r ∈ Finset.univ.filter (fun r : N.R => ¬ IsTropicallyMinimal N a w r s),
        (0 : ℝ))) :=
    tendsto_finsetSum (s := Finset.univ.filter
        (fun r : N.R => ¬ IsTropicallyMinimal N a w r s))
      (f := fun r (ε : ℝ) => κ.k r *
        Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) * Real.log ε) *
          (N.reaction r).source.massActionMonomial y * N.reactionVector r s)
      (x := 𝓝[>] 0) hnonmin
  have hlim : Tendsto (fun ε : ℝ =>
        ∑ r : N.R, κ.k r * Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) *
          Real.log ε) * (N.reaction r).source.massActionMonomial y * N.reactionVector r s)
      (𝓝[>] 0)
      (𝓝 ((∑ r ∈ tropicalMinimal N a w s,
            tropicalLeadingTerm N κ s r y) +
          ∑ r ∈ Finset.univ.filter (fun r : N.R => ¬ IsTropicallyMinimal N a w r s),
            (0 : ℝ))) :=
    (h1.add h2).congr' (Filter.Eventually.of_forall fun ε => (hsplit ε).symm)
  have heq : (∑ r ∈ tropicalMinimal N a w s, tropicalLeadingTerm N κ s r y) +
      ∑ r ∈ Finset.univ.filter (fun r : N.R => ¬ IsTropicallyMinimal N a w r s), (0 : ℝ) =
      tropicalLeadingField N κ a w y s := by
    unfold tropicalLeadingField
    simp
  rw [heq] at hlim
  exact hlim.congr' (Filter.Eventually.of_forall fun ε => (hnorm ε).symm)

/-- **Uniqueness of limits.**  Two limits of the same function with respect to the same
filter are equal. -/
theorem tendsto_unique' {f : ℝ → ℝ} {a b : ℝ}
    (h₁ : Tendsto f (𝓝[>] 0) (𝓝 a)) (h₂ : Tendsto f (𝓝[>] 0) (𝓝 b)) : a = b := by
  by_contra hab
  have hne : a ≠ b := hab
  have hδpos : 0 < dist a b := dist_pos.mpr hne
  have h1 := (Metric.tendsto_nhds.mp h₁) (dist a b / 3) (by positivity)
  have h2 := (Metric.tendsto_nhds.mp h₂) (dist a b / 3) (by positivity)
  have h12 : ∀ᶠ x in (𝓝[>] 0), dist (f x) a < dist a b / 3 ∧ dist (f x) b < dist a b / 3 :=
    h1.and h2
  obtain ⟨x, hx⟩ := h12.exists
  have htri : dist a b ≤ dist a (f x) + dist (f x) b := dist_triangle _ _ _
  rw [dist_comm a (f x)] at htri
  have hlt : dist a b / 3 + dist a b / 3 < dist a b := by linarith
  linarith

/-! ## 4. The tropical equilibration makes the leading field sign-indeterminate -/

/-- **The tropical equilibration is the sign-indeterminacy of the leading system.**  Assume
`w` is a tropical equilibration of `N` at the orders `a`.  Then in every species equation
that is changed by some reaction, the leading part of the equation has a strictly positive
summand and a strictly negative summand (at a positive concentration).  Without this the
leading equation could not vanish, which is why a tropical equilibration is a necessary
condition for the existence of steady states. -/
theorem tropicalLeadingField_signs (N : Network S) (κ : RateConstants N) (a : N.R → ℝ)
    (w : S → ℝ) (hEquil : IsTropicalEquilibration N a w) (y : Concentration S)
    (hy : y.Positive) (s : S) (hs : ∃ r : N.R, N.reactionVector r s ≠ 0) :
    ∃ r₁ r₂ : N.R, r₁ ∈ tropicalMinimal N a w s ∧ r₂ ∈ tropicalMinimal N a w s ∧
      0 < tropicalLeadingTerm N κ s r₁ y ∧ tropicalLeadingTerm N κ s r₂ y < 0 := by
  classical
  obtain ⟨r₁, r₂, hr₁pos, hr₂neg, hmin⟩ := hEquil s hs
  have hr₁min : IsTropicallyMinimal N a w r₁ s :=
    ⟨ne_of_gt hr₁pos, fun r' hr' => (hmin r' hr').1⟩
  have hr₂min : IsTropicallyMinimal N a w r₂ s :=
    ⟨ne_of_lt hr₂neg, fun r' hr' => (hmin r' hr').2⟩
  refine ⟨r₁, r₂, (mem_tropicalMinimal N a w r₁ s).mpr hr₁min,
    (mem_tropicalMinimal N a w r₂ s).mpr hr₂min, ?_, ?_⟩
  · have hmono : 0 < (N.reaction r₁).source.massActionMonomial y :=
      Complex.massActionMonomial_pos hy _
    have hk : 0 < κ.k r₁ := κ.positive r₁
    unfold tropicalLeadingTerm
    have : 0 < N.reactionVector r₁ s := hr₁pos
    positivity
  · have hmono : 0 < (N.reaction r₂).source.massActionMonomial y :=
      Complex.massActionMonomial_pos hy _
    have hk : 0 < κ.k r₂ := κ.positive r₂
    unfold tropicalLeadingTerm
    have : N.reactionVector r₂ s < 0 := hr₂neg
    have : (0 : ℝ) < κ.k r₂ * (N.reaction r₂).source.massActionMonomial y := by positivity
    nlinarith

/-! ## 5. The tropical leading system has a positive root -/

/-- **The tropical system is the leading term of the rescaled mass-action field (with
varying concentrations).**  Let `y ε → y₀` as `ε → 0⁺` and let `r₀` be tropically minimal
for the species `s`.  Then the rescaled field of `s` at `y ε`, divided by
`ε^{d_{r₀} - w_s}`, converges to the tropical leading field at `y₀`. -/
theorem tropicalLeadingField_leading_of_tendsto (N : Network S) (κ : RateConstants N)
    (a : N.R → ℝ) (w : S → ℝ) {y : ℝ → Concentration S} {y₀ : Concentration S}
    (hy : ∀ s : S, Tendsto (fun ε : ℝ => y ε s) (𝓝[>] 0) (𝓝 (y₀ s)))
    (s : S) (r₀ : N.R) (hr₀ : IsTropicallyMinimal N a w r₀ s) :
    Tendsto (fun ε : ℝ => scaledMassActionField N κ a w ε (y ε) s /
        Real.exp ((tropicalOrder N a w r₀ - w s) * Real.log ε))
      (𝓝[>] 0) (𝓝 (tropicalLeadingField N κ a w y₀ s)) := by
  classical
  have hvec : Tendsto (y : ℝ → Concentration S) (𝓝[>] 0) (𝓝 y₀) :=
    tendsto_pi_nhds.mpr hy
  have hmono : ∀ (r : N.R),
      Tendsto (fun ε : ℝ => (N.reaction r).source.massActionMonomial (y ε)) (𝓝[>] 0)
        (𝓝 ((N.reaction r).source.massActionMonomial y₀)) := by
    intro r
    have hdiff : Differentiable ℝ
        (fun z : Concentration S => (N.reaction r).source.massActionMonomial z) :=
      massActionMonomial_differentiable (N.reaction r).source
    exact (hdiff y₀).continuousAt.tendsto.comp hvec
  -- the normalised summands
  have hterm : ∀ (r : N.R) (ε : ℝ),
      (κ.k r * Real.exp ((tropicalOrder N a w r - w s) * Real.log ε) *
          (N.reaction r).source.massActionMonomial (y ε) * N.reactionVector r s) /
          Real.exp ((tropicalOrder N a w r₀ - w s) * Real.log ε) =
        κ.k r * Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) * Real.log ε) *
          (N.reaction r).source.massActionMonomial (y ε) * N.reactionVector r s := by
    intro r ε
    rw [div_eq_mul_inv]
    have hexp : Real.exp ((tropicalOrder N a w r - w s) * Real.log ε) *
          (Real.exp ((tropicalOrder N a w r₀ - w s) * Real.log ε))⁻¹ =
        Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) * Real.log ε) := by
      rw [← div_eq_mul_inv, ← Real.exp_sub]
      congr 1
      ring
    have hreassoc : κ.k r * Real.exp ((tropicalOrder N a w r - w s) * Real.log ε) *
          (N.reaction r).source.massActionMonomial (y ε) * N.reactionVector r s *
          (Real.exp ((tropicalOrder N a w r₀ - w s) * Real.log ε))⁻¹ =
        κ.k r * (Real.exp ((tropicalOrder N a w r - w s) * Real.log ε) *
          (Real.exp ((tropicalOrder N a w r₀ - w s) * Real.log ε))⁻¹) *
          (N.reaction r).source.massActionMonomial (y ε) * N.reactionVector r s := by ring
    rw [hreassoc, hexp]
  have hnorm : ∀ ε : ℝ, scaledMassActionField N κ a w ε (y ε) s /
        Real.exp ((tropicalOrder N a w r₀ - w s) * Real.log ε) =
      ∑ r : N.R, κ.k r * Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) *
          Real.log ε) * (N.reaction r).source.massActionMonomial (y ε) *
          N.reactionVector r s := by
    intro ε
    simp only [scaledMassActionField]
    have hdiv : (∑ r : N.R, κ.k r * Real.exp ((tropicalOrder N a w r - w s) * Real.log ε) *
          (N.reaction r).source.massActionMonomial (y ε) * N.reactionVector r s) /
          Real.exp ((tropicalOrder N a w r₀ - w s) * Real.log ε) =
        ∑ r : N.R, (κ.k r * Real.exp ((tropicalOrder N a w r - w s) * Real.log ε) *
          (N.reaction r).source.massActionMonomial (y ε) * N.reactionVector r s) /
          Real.exp ((tropicalOrder N a w r₀ - w s) * Real.log ε) := by
      rw [div_eq_mul_inv, Finset.sum_mul]
      exact Finset.sum_congr rfl fun r _ => by rw [div_eq_mul_inv]
    rw [hdiv]
    exact Finset.sum_congr rfl fun r _ => hterm r ε
  -- split the sum into the minimal and the non-minimal reactions
  have hsplit : ∀ ε : ℝ,
      ∑ r : N.R, κ.k r * Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) *
          Real.log ε) * (N.reaction r).source.massActionMonomial (y ε) *
          N.reactionVector r s =
        (∑ r ∈ tropicalMinimal N a w s,
          κ.k r * Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) * Real.log ε) *
            (N.reaction r).source.massActionMonomial (y ε) * N.reactionVector r s) +
        ∑ r ∈ Finset.univ.filter (fun r : N.R => ¬ IsTropicallyMinimal N a w r s),
          κ.k r * Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) * Real.log ε) *
            (N.reaction r).source.massActionMonomial (y ε) * N.reactionVector r s := by
    intro ε
    simp only [tropicalMinimal]
    rw [Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun r : N.R => IsTropicallyMinimal N a w r s)]
  -- the minimal reactions converge to their leading value
  have hmin : ∀ r ∈ tropicalMinimal N a w s,
      Tendsto (fun ε : ℝ => κ.k r * Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) *
          Real.log ε) * (N.reaction r).source.massActionMonomial (y ε) *
            N.reactionVector r s)
        (𝓝[>] 0) (𝓝 (tropicalLeadingTerm N κ s r y₀)) := by
    intro r hr
    have hrP : IsTropicallyMinimal N a w r s := (mem_tropicalMinimal N a w r s).mp hr
    have hord : tropicalOrder N a w r = tropicalOrder N a w r₀ :=
      ((isTropicallyMinimal_iff N a w hr₀).mp hrP).2
    have hexp0 : ∀ ε : ℝ, Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) *
        Real.log ε) = 1 := by
      intro ε
      rw [hord, sub_self]
      simp
    have hconst : ∀ ε : ℝ, κ.k r * Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) *
        Real.log ε) * (N.reaction r).source.massActionMonomial (y ε) *
        N.reactionVector r s =
        (N.reaction r).source.massActionMonomial (y ε) *
          (κ.k r * N.reactionVector r s) := by
      intro ε
      rw [hexp0]
      ring
    rw [show (fun ε : ℝ => κ.k r * Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) *
          Real.log ε) * (N.reaction r).source.massActionMonomial (y ε) *
          N.reactionVector r s)
        = (fun ε : ℝ => (N.reaction r).source.massActionMonomial (y ε) *
          (κ.k r * N.reactionVector r s)) from funext hconst]
    have h1 := (hmono r).mul_const (κ.k r * N.reactionVector r s)
    simpa only [tropicalLeadingTerm, mul_assoc, mul_left_comm, mul_comm] using h1
  -- the non-minimal reactions vanish
  have hnonmin : ∀ r ∈ Finset.univ.filter (fun r : N.R => ¬ IsTropicallyMinimal N a w r s),
      Tendsto (fun ε : ℝ => κ.k r * Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) *
          Real.log ε) * (N.reaction r).source.massActionMonomial (y ε) *
          N.reactionVector r s)
        (𝓝[>] 0) (𝓝 0) := by
    intro r hr
    by_cases hrv : N.reactionVector r s = 0
    · have hzero : ∀ ε : ℝ, κ.k r * Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) *
          Real.log ε) * (N.reaction r).source.massActionMonomial (y ε) *
          N.reactionVector r s = 0 := by
        intro ε
        rw [hrv, mul_zero]
      rw [show (fun ε : ℝ => κ.k r * Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) *
            Real.log ε) * (N.reaction r).source.massActionMonomial (y ε) *
            N.reactionVector r s) = (fun _ : ℝ => (0 : ℝ)) from funext hzero]
      exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝 (0 : ℝ)) (𝓝 0)).mono_left
        nhdsWithin_le_nhds
    · have hrP : ¬ IsTropicallyMinimal N a w r s := (Finset.mem_filter.mp hr).2
      by_cases hord : tropicalOrder N a w r = tropicalOrder N a w r₀
      · exfalso
        exact hrP ((isTropicallyMinimal_iff N a w hr₀).mpr ⟨hrv, hord⟩)
      · have hgt : tropicalOrder N a w r₀ < tropicalOrder N a w r := by
          have hle := hr₀.2 r hrv
          exact lt_of_le_of_ne hle (Ne.symm hord)
        have hlim : Tendsto (fun ε : ℝ =>
            Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) * Real.log ε))
            (𝓝[>] 0) (𝓝 0) := by
          have h1 : Tendsto (fun ε : ℝ =>
              (tropicalOrder N a w r - tropicalOrder N a w r₀) * Real.log ε)
              (𝓝[>] 0) atBot :=
            Filter.Tendsto.const_mul_atBot (by linarith) Real.tendsto_log_nhdsGT_zero
          exact Real.tendsto_exp_atBot.comp h1
        have hmul := hlim.mul (hmono r)
        have h2 := hmul.mul_const (κ.k r * N.reactionVector r s)
        have heq : ∀ ε : ℝ, κ.k r * Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) *
              Real.log ε) * (N.reaction r).source.massActionMonomial (y ε) *
              N.reactionVector r s =
            (Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) * Real.log ε) *
              (N.reaction r).source.massActionMonomial (y ε)) *
                (κ.k r * N.reactionVector r s) := by
          intro ε; ring
        rw [show (fun ε : ℝ => κ.k r * Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) *
              Real.log ε) * (N.reaction r).source.massActionMonomial (y ε) *
              N.reactionVector r s)
            = (fun ε : ℝ => (Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) *
                Real.log ε) * (N.reaction r).source.massActionMonomial (y ε)) *
                  (κ.k r * N.reactionVector r s)) from funext heq]
        simpa only [mul_assoc, mul_left_comm, mul_comm, zero_mul] using h2
  -- assemble
  have h1 : Tendsto (fun ε : ℝ => ∑ r ∈ tropicalMinimal N a w s,
        κ.k r * Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) * Real.log ε) *
          (N.reaction r).source.massActionMonomial (y ε) * N.reactionVector r s)
      (𝓝[>] 0) (𝓝 (∑ r ∈ tropicalMinimal N a w s, tropicalLeadingTerm N κ s r y₀)) :=
    tendsto_finsetSum (s := tropicalMinimal N a w s)
      (f := fun r (ε : ℝ) => κ.k r *
        Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) * Real.log ε) *
          (N.reaction r).source.massActionMonomial (y ε) * N.reactionVector r s)
      (x := 𝓝[>] 0) hmin
  have h2 : Tendsto (fun ε : ℝ => ∑ r ∈ Finset.univ.filter
        (fun r : N.R => ¬ IsTropicallyMinimal N a w r s),
        κ.k r * Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) * Real.log ε) *
          (N.reaction r).source.massActionMonomial (y ε) * N.reactionVector r s)
      (𝓝[>] 0)
      (𝓝 (∑ r ∈ Finset.univ.filter (fun r : N.R => ¬ IsTropicallyMinimal N a w r s),
        (0 : ℝ))) :=
    tendsto_finsetSum (s := Finset.univ.filter
        (fun r : N.R => ¬ IsTropicallyMinimal N a w r s))
      (f := fun r (ε : ℝ) => κ.k r *
        Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) * Real.log ε) *
          (N.reaction r).source.massActionMonomial (y ε) * N.reactionVector r s)
      (x := 𝓝[>] 0) hnonmin
  have hlim : Tendsto (fun ε : ℝ =>
        ∑ r : N.R, κ.k r * Real.exp ((tropicalOrder N a w r - tropicalOrder N a w r₀) *
          Real.log ε) * (N.reaction r).source.massActionMonomial (y ε) *
          N.reactionVector r s)
      (𝓝[>] 0)
      (𝓝 ((∑ r ∈ tropicalMinimal N a w s, tropicalLeadingTerm N κ s r y₀) +
        ∑ r ∈ Finset.univ.filter (fun r : N.R => ¬ IsTropicallyMinimal N a w r s), (0 : ℝ))) :=
    (h1.add h2).congr' (Filter.Eventually.of_forall fun ε => (hsplit ε).symm)
  have heq : (∑ r ∈ tropicalMinimal N a w s, tropicalLeadingTerm N κ s r y₀) +
      ∑ r ∈ Finset.univ.filter (fun r : N.R => ¬ IsTropicallyMinimal N a w r s), (0 : ℝ) =
      tropicalLeadingField N κ a w y₀ s := by
    unfold tropicalLeadingField
    simp
  rw [heq] at hlim
  exact hlim.congr' (Filter.Eventually.of_forall fun ε => (hnorm ε).symm)

/-- **A positive root of the tropical leading system.**  Suppose the scaled network (rates
`κ̄_r ε^{a_r}`) has a family of steady states `x(ε) = ε^{w} ψ(ε)` with `ψ(ε) → ξ` as
`ε → 0⁺`, and `ξ` is positive.  Then `ξ` is a root of the tropical leading system: the
tropical equilibration has a critical point.  This is the bridge between the steady-state
theory of the lifting (`CRNT.Algebra.TropicalLiftingNetwork`) and the slow–fast theory. -/
theorem tropicalLeadingField_zero_of_scaledSteadyState (N : Network S) (κ : RateConstants N)
    (a : N.R → ℝ) (w : S → ℝ) (hEquil : IsTropicalEquilibration N a w)
    {ψ : ℝ → Concentration S} {ξ : Concentration S}
    (hy : ∀ s : S, Tendsto (fun n : ℝ => ψ n s) (𝓝[>] 0) (𝓝 (ξ s)))
    (hss : ∀ t : ℝ, N.IsMassActionSteadyState (scaledRates N κ a t)
              (fun s => Real.exp ((w s) * Real.log t) * ψ t s)) :
    ∀ s : S, tropicalLeadingField N κ a w ξ s = 0 := by
  classical
  intro s
  by_cases hs : ∃ r : N.R, N.reactionVector r s ≠ 0
  · obtain ⟨r₁, r₂, hr₁pos, hr₂neg, hmin⟩ := hEquil s hs
    have hr₁min : IsTropicallyMinimal N a w r₁ s :=
      ⟨ne_of_gt hr₁pos, fun r' hr' => (hmin r' hr').1⟩
    have hlim := tropicalLeadingField_leading_of_tendsto N κ a w hy s r₁ hr₁min
    have hzero : ∀ n : ℝ, scaledMassActionField N κ a w n (ψ n) s = 0 := by
      intro n
      have hfield : N.massActionVectorField (scaledRates N κ a n)
          (fun t => Real.exp ((w t) * Real.log n) * ψ n t) s = 0 := hss n s
      have hid := scaledMassActionField_eq N κ a w n (ψ n) s
      rw [hfield, mul_zero] at hid
      exact hid
    have hdiv : ∀ n : ℝ, scaledMassActionField N κ a w n (ψ n) s /
        Real.exp ((tropicalOrder N a w r₁ - w s) * Real.log n) = 0 := by
      intro n
      rw [hzero n, zero_div]
    have hconst : Tendsto (fun n : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 0) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝 (0 : ℝ)) (𝓝 0)).mono_left
        nhdsWithin_le_nhds
    have hconst' : Tendsto (fun n : ℝ => scaledMassActionField N κ a w n (ψ n) s /
        Real.exp ((tropicalOrder N a w r₁ - w s) * Real.log n)) (𝓝[>] 0) (𝓝 0) :=
      hconst.congr' (Filter.Eventually.of_forall fun n => (hdiv n).symm)
    exact tendsto_unique' hlim hconst'
  · have hempty : tropicalMinimal N a w s = ∅ := by
      ext r
      simp only [tropicalMinimal, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        exact absurd ⟨r, h.1⟩ hs
      · intro h
        cases h
    simp [tropicalLeadingField, hempty]


/-! ## 6. The slow–fast structure extracted from the tropical data -/

variable {X E : Type} [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E]

/-- **The Hurwitz condition on a linearisation of a finite-dimensional concentration
space.**  This is the Lyapunov–Krasovskii condition `⟪A w, w⟫ ≤ -μ ‖w‖²`, written with the
*explicit* Euclidean inner product `∑ e, u e * v e` of a concentration space `E → ℝ`.  (The
formulation avoids the instance mismatch between the `Pi` module structure and the one
induced by an inner product structure, which would prevent the `CRNT.HurwitzRate` of
`CRNT.Dynamics.TikhonovLocal` from being applied to a concentration space.) -/
def HurwitzRate' (A : (E → ℝ) →L[ℝ] (E → ℝ)) (μ : ℝ) : Prop :=
  ∀ w : E → ℝ, ∑ e : E, (A w e) * w e ≤ -μ * ∑ e : E, w e ^ 2

omit [DecidableEq E] in
/-- **A Hurwitz linearisation is injective.** -/
theorem hurwitzRate'_injective {A : (E → ℝ) →L[ℝ] (E → ℝ)} {μ : ℝ}
    (hA : HurwitzRate' A μ) (hμ : 0 < μ) : Function.Injective A := by
  intro w₁ w₂ hw
  have hz : A (w₁ - w₂) = 0 := by rw [map_sub, hw, sub_self]
  have h := hA (w₁ - w₂)
  rw [hz] at h
  have h' : (0 : ℝ) ≤ -μ * ∑ e : E, (w₁ - w₂) e ^ 2 := by simpa using h
  have hnonneg : 0 ≤ ∑ e : E, (w₁ - w₂) e ^ 2 := Finset.sum_nonneg fun e _ => sq_nonneg _
  have hS : (∑ e : E, (w₁ - w₂) e ^ 2) ≤ 0 := by
    by_contra hS
    have hS' : 0 < (∑ e : E, (w₁ - w₂) e ^ 2) := lt_of_not_ge hS
    have hpos : 0 < μ * (∑ e : E, (w₁ - w₂) e ^ 2) := mul_pos hμ hS'
    have hμS : μ * (∑ e : E, (w₁ - w₂) e ^ 2) ≤ 0 := by linarith [h']
    linarith
  have hsum : ∑ e : E, (w₁ - w₂) e ^ 2 = 0 := le_antisymm hS hnonneg
  have hz0 : ∀ e : E, (w₁ - w₂) e = 0 := by
    intro e
    have h1 := Finset.single_le_sum (s := (Finset.univ : Finset E))
      (fun b _ => sq_nonneg ((w₁ - w₂) b)) (Finset.mem_univ e)
    rw [hsum] at h1
    nlinarith [sq_nonneg ((w₁ - w₂) e)]
  funext e
  exact sub_eq_zero.mp (hz0 e)

omit [DecidableEq E] in
/-- **A Hurwitz linearisation is invertible.**  This is the local Tikhonov hypothesis: the
linearisation of the fast field at the tropical critical point is invertible, so that the
implicit function theorem produces the local slow manifold. -/
theorem hurwitzRate'_isInvertible {A : (E → ℝ) →L[ℝ] (E → ℝ)} {μ : ℝ}
    (hA : HurwitzRate' A μ) (hμ : 0 < μ) : A.IsInvertible := by
  have hinj : Function.Injective A := hurwitzRate'_injective hA hμ
  have hker : A.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have hsurj : A.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact LinearMap.surjective_of_injective hinj
  exact ⟨ContinuousLinearEquiv.ofBijective A hker hsurj, rfl⟩

omit [DecidableEq E] in
/-- **The linearised system decays exponentially.**  If `A` is Hurwitz with rate `μ > 0`, every
integral curve `z` of `ż = A z` satisfies
`∑ e, z t e ^ 2 ≤ e^{-2 μ t} ∑ e, z 0 e ^ 2`: the boundary layer of the linearised fast
system collapses exponentially. -/
theorem hurwitz_linear_decay' {A : (E → ℝ) →L[ℝ] (E → ℝ)} {μ : ℝ}
    (hA : HurwitzRate' A μ) {z : ℝ → E → ℝ}
    (hz : ∀ t, HasDerivAt z (A (z t)) t) :
    ∀ t, 0 ≤ t → (∑ e : E, z t e ^ 2) ≤ Real.exp (-(2 * μ * t)) * (∑ e : E, z 0 e ^ 2) := by
  intro t ht
  set V : ℝ → ℝ := fun s => ∑ e : E, z s e ^ 2 with hV
  have hVder : ∀ s, HasDerivAt V (∑ e : E, 2 * (A (z s) e) * z s e) s := by
    intro s
    have hz' := hasDerivAt_pi.mp (hz s)
    have hmain : V = fun s => ∑ e : E, (z s e) ^ 2 := rfl
    rw [hmain]
    refine HasDerivAt.fun_sum (𝕜 := ℝ) (F := ℝ) (u := (Finset.univ : Finset E)) fun e _ => ?_
    have h1 := (hz' e).pow 2
    convert h1 using 1
    ring
  have hVbound : ∀ s ∈ Ico 0 t, (∑ e : E, 2 * (A (z s) e) * z s e) ≤ -(2 * μ) * V s := by
    intro s hs
    have h1 := hA (z s)
    have h2 : ∑ e : E, (A (z s) e) * z s e ≤ -μ * ∑ e : E, z s e ^ 2 := by
      simpa [hV] using h1
    rw [hV]
    have h3 : (∑ e : E, 2 * (A (z s) e) * z s e) = 2 * (∑ e : E, (A (z s) e) * z s e) := by
      have h4 : (∑ e : E, 2 * (A (z s) e) * z s e) = ∑ e : E, 2 * ((A (z s) e) * z s e) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        ring
      rw [h4, ← Finset.mul_sum]
    rw [h3]
    nlinarith [h2]
  have hgron := CRNT.ExponentialDecay.le_mul_exp_of_deriv_le (V := V)
    (V' := fun s => ∑ e : E, 2 * (A (z s) e) * z s e) (K := -(2 * μ)) (b := t)
    hVder hVbound t ⟨ht, le_rfl⟩
  have hexp : -(2 * μ) * t = -((2 : ℝ) * μ * t) := by ring
  rw [hexp] at hgron
  simpa [hV, mul_comm] using hgron

/-- **The concentration of a slow–fast pair of species groups.**  The species of the
network are `X ⊕ E`: the slow species `X` and the fast species `E`. -/
def embedConcentration (x : X → ℝ) (y : E → ℝ) : (X ⊕ E) → ℝ :=
  fun s => Sum.rec x y s

/-- **The tropical fast field.**  The leading (tropical) system restricted to the fast
species `E`: the critical manifold `{y | g (x, y) = 0}` of the tropical slow–fast system is
exactly the tropical constraint on the fast species. -/
noncomputable def tropicalFastField (N : Network (X ⊕ E)) (κ : RateConstants N)
    (a : N.R → ℝ) (w : (X ⊕ E) → ℝ) (x : X → ℝ) (y : E → ℝ) : E → ℝ :=
  fun e => tropicalLeadingField N κ a w (embedConcentration x y) (Sum.inr e)

/-- **The tropical slow field.**  The leading (tropical) system restricted to the slow
species `X`. -/
noncomputable def tropicalSlowField (N : Network (X ⊕ E)) (κ : RateConstants N)
    (a : N.R → ℝ) (w : (X ⊕ E) → ℝ) (x : X → ℝ) (y : E → ℝ) : X → ℝ :=
  fun s => tropicalLeadingField N κ a w (embedConcentration x y) (Sum.inl s)

/-- **The tropical system is smooth.**  The tropical leading field is a polynomial in the
concentrations, hence `C¹`. -/
theorem tropicalLeadingField_contDiff (N : Network S) (κ : RateConstants N) (a : N.R → ℝ)
    (w : S → ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun y : Concentration S => tropicalLeadingField N κ a w y) := by
  rw [contDiff_pi]
  intro s
  simp only [tropicalLeadingField]
  refine ContDiff.sum fun r _ => ?_
  have hmono : ContDiff ℝ n (fun y : Concentration S =>
      (N.reaction r).source.massActionMonomial y) := by
    have hfun : (fun y : Concentration S => (N.reaction r).source.massActionMonomial y)
        = fun y => ∏ s' : S, y s' ^ (N.reaction r).source s' := by
      funext y
      simp only [Complex.massActionMonomial]
    rw [hfun]
    exact contDiff_prod fun s' _ => (contDiff_apply ℝ ℝ s').pow _
  unfold tropicalLeadingTerm
  exact (contDiff_const.mul hmono).mul contDiff_const

omit [DecidableEq X] [DecidableEq E] in
/-- **The embedding is smooth in the pair of variables.** -/
theorem embedConcentration_contDiff :
    ContDiff ℝ 1 (fun p : (X → ℝ) × (E → ℝ) => embedConcentration p.1 p.2) := by
  rw [contDiff_pi]
  intro s
  cases s with
  | inl a =>
      have h1 : (fun p : (X → ℝ) × (E → ℝ) => embedConcentration p.1 p.2 (Sum.inl a))
          = (fun f : X → ℝ => f a) ∘ Prod.fst := by
        funext p
        rfl
      rw [h1]
      have hfst : ContDiff ℝ 1 (Prod.fst : (X → ℝ) × (E → ℝ) → (X → ℝ)) := contDiff_fst
      have hproj : ContDiff ℝ 1 (fun f : X → ℝ => f a) := contDiff_apply ℝ ℝ a
      exact hproj.comp hfst
  | inr b =>
      have h1 : (fun p : (X → ℝ) × (E → ℝ) => embedConcentration p.1 p.2 (Sum.inr b))
          = (fun f : E → ℝ => f b) ∘ Prod.snd := by
        funext p
        rfl
      rw [h1]
      have hsnd : ContDiff ℝ 1 (Prod.snd : (X → ℝ) × (E → ℝ) → (E → ℝ)) := contDiff_snd
      have hproj : ContDiff ℝ 1 (fun f : E → ℝ => f b) := contDiff_apply ℝ ℝ b
      exact hproj.comp hsnd

/-- **The tropical fast field is `C¹` in the slow–fast variables.** -/
theorem tropicalFastField_contDiffAt (N : Network (X ⊕ E)) (κ : RateConstants N)
    (a : N.R → ℝ) (w : (X ⊕ E) → ℝ) (x₀ : X → ℝ) (y₀ : E → ℝ) :
    ContDiffAt ℝ 1
      (fun p : (X → ℝ) × (E → ℝ) => tropicalFastField N κ a w p.1 p.2) (x₀, y₀) := by
  have hlead : ContDiff ℝ 1 (fun y : Concentration (X ⊕ E) => tropicalLeadingField N κ a w y) :=
    tropicalLeadingField_contDiff N κ a w
  have hG : ContDiff ℝ 1 (fun z : (X ⊕ E) → ℝ =>
      fun e => tropicalLeadingField N κ a w z (Sum.inr e)) := by
    rw [contDiff_pi]
    intro e
    exact (contDiff_pi.mp hlead) (Sum.inr e)
  have hfun : (fun p : (X → ℝ) × (E → ℝ) => tropicalFastField N κ a w p.1 p.2)
      = fun p : (X → ℝ) × (E → ℝ) =>
          (fun z : (X ⊕ E) → ℝ => fun e => tropicalLeadingField N κ a w z (Sum.inr e))
            (embedConcentration p.1 p.2) := by
    funext p
    funext e
    rfl
  rw [hfun]
  exact (hG.contDiffAt).comp (x₀, y₀) embedConcentration_contDiff.contDiffAt

/-- **The fibre derivative of the tropical fast field.**  The linearisation of the frozen
fast field `y ↦ g (x₀, y)` at `y₀`; it is the operator whose invertibility is the
hypothesis of the implicit function theorem. -/
noncomputable def fiberDeriv' (g : (X → ℝ) → (E → ℝ) → (E → ℝ)) (x₀ : X → ℝ) (y₀ : E → ℝ) :
    (E → ℝ) →L[ℝ] (E → ℝ) :=
  fderiv ℝ (fun p : (X → ℝ) × (E → ℝ) => g p.1 p.2) (x₀, y₀) ∘L
    ContinuousLinearMap.inr ℝ (X → ℝ) (E → ℝ)

/-! ## 7. The critical manifold of the tropical reduced system -/

/-- **The critical manifold of the tropical reduced system.**  Let `x₀` and `y₀` be a
*tropical critical point*, i.e. a point where the tropical fast field vanishes, and suppose
the fibre derivative of the fast field at that point is invertible (which is the case as soon
as it is *Hurwitz*, see `tropical_critical_manifold_hurwitz`).  Then there is a local `C¹`
slow manifold `h` through `(x₀, y₀)`, satisfying `g (x, h x) = 0`: the critical manifold of
the tropical reduced system is the tropical constraint on the fast species, and the tropical
critical point lies on the local slow manifold. -/
theorem tropical_critical_manifold (N : Network (X ⊕ E)) (κ : RateConstants N)
    (a : N.R → ℝ) (w : (X ⊕ E) → ℝ) {x₀ : X → ℝ} {y₀ : E → ℝ}
    (hg : tropicalFastField N κ a w x₀ y₀ = 0)
    (hInv : (fiberDeriv' (fun x y => tropicalFastField N κ a w x y) x₀ y₀).IsInvertible) :
    ∃ h : (X → ℝ) → (E → ℝ), h x₀ = y₀ ∧
      (∀ᶠ x in 𝓝 x₀, tropicalFastField N κ a w x (h x) = 0) ∧
      ContDiffAt ℝ 1 h x₀ := by
  have hcont : ContDiffAt ℝ 1
      (fun p : (X → ℝ) × (E → ℝ) => tropicalFastField N κ a w p.1 p.2) (x₀, y₀) :=
    tropicalFastField_contDiffAt N κ a w x₀ y₀
  have hcd := hcont.contDiffAt_implicitFunction (n := 1) (by norm_num) hInv
  have hself := hcont.implicitFunction_apply_self (n := 1) (by norm_num) hInv
  have hev := hcont.eventually_apply_implicitFunction (n := 1) (by norm_num) hInv
  refine ⟨hcont.implicitFunction (n := 1) (by norm_num) hInv, hself, ?_, hcd⟩
  filter_upwards [hev] with x hx
  rw [hx, hg]

/-- **The critical manifold of the tropical reduced system, under the Hurwitz
hypothesis.**  This is the local Tikhonov theorem for the tropical data: if the linearisation
of the tropical fast field at the tropical critical point is Hurwitz (in the
Lyapunov–Krasovskii sense of `HurwitzRate'`), then the tropical critical point lies on a
unique local `C¹` slow manifold of the tropical reduced system. -/
theorem tropical_critical_manifold_hurwitz (N : Network (X ⊕ E)) (κ : RateConstants N)
    (a : N.R → ℝ) (w : (X ⊕ E) → ℝ) {x₀ : X → ℝ} {y₀ : E → ℝ}
    {A : (E → ℝ) →L[ℝ] (E → ℝ)} {μ : ℝ}
    (hg : tropicalFastField N κ a w x₀ y₀ = 0)
    (hAeq : fiberDeriv' (fun x y => tropicalFastField N κ a w x y) x₀ y₀ = A)
    (hA : HurwitzRate' A μ) (hμ : 0 < μ) :
    ∃ h : (X → ℝ) → (E → ℝ), h x₀ = y₀ ∧
      (∀ᶠ x in 𝓝 x₀, tropicalFastField N κ a w x (h x) = 0) ∧
      ContDiffAt ℝ 1 h x₀ := by
  have hInv : (fiberDeriv' (fun x y => tropicalFastField N κ a w x y) x₀ y₀).IsInvertible := by
    rw [hAeq]
    exact hurwitzRate'_isInvertible hA hμ
  exact tropical_critical_manifold N κ a w hg hInv

/-- **The local slow manifold of the tropical reduced system is unique.** -/
theorem tropical_critical_manifold_unique (N : Network (X ⊕ E)) (κ : RateConstants N)
    (a : N.R → ℝ) (w : (X ⊕ E) → ℝ) {x₀ : X → ℝ} {y₀ : E → ℝ}
    (hg : tropicalFastField N κ a w x₀ y₀ = 0)
    (hInv : (fiberDeriv' (fun x y => tropicalFastField N κ a w x y) x₀ y₀).IsInvertible)
    {h h' : (X → ℝ) → (E → ℝ)} (hcd : ContDiffAt ℝ 1 h x₀) (hh : h x₀ = y₀)
    (hcd' : ContDiffAt ℝ 1 h' x₀) (hh' : h' x₀ = y₀)
    (hz : ∀ᶠ x in 𝓝 x₀, tropicalFastField N κ a w x (h x) = 0)
    (hz' : ∀ᶠ x in 𝓝 x₀, tropicalFastField N κ a w x (h' x) = 0) :
    ∀ᶠ x in 𝓝 x₀, h' x = h x := by
  have hcont : ContDiffAt ℝ 1
      (fun p : (X → ℝ) × (E → ℝ) => tropicalFastField N κ a w p.1 p.2) (x₀, y₀) :=
    tropicalFastField_contDiffAt N κ a w x₀ y₀
  have hcd0 := hcont.contDiffAt_implicitFunction (n := 1) (by norm_num) hInv
  have hself := hcont.implicitFunction_apply_self (n := 1) (by norm_num) hInv
  have hev := hcont.eventually_apply_implicitFunction (n := 1) (by norm_num) hInv
  have hev' := hcont.eventually_apply_eq_iff_implicitFunction (n := 1) (by norm_num) hInv
  set S : Set ((X → ℝ) × (E → ℝ)) :=
    {v | (fun p : (X → ℝ) × (E → ℝ) => tropicalFastField N κ a w p.1 p.2) v =
        (fun p : (X → ℝ) × (E → ℝ) => tropicalFastField N κ a w p.1 p.2) (x₀, y₀) ↔
      hcont.implicitFunction (n := 1) (by norm_num) hInv v.1 = v.2} with hS
  have hSin : S ∈ 𝓝 (x₀, y₀) := hev'
  have hpre : ∀ᶠ x in 𝓝 x₀, (x, h x) ∈ S := by
    have hc : ContinuousAt (fun x : X → ℝ => (x, h x)) x₀ := by
      have h1 := (continuousAt_id.prodMk hcd.continuousAt)
      simpa only [id_eq] using h1
    have hSin' : S ∈ 𝓝 (x₀, h x₀) := by simpa [hh] using hSin
    have h := hc.continuousWithinAt.preimage_mem_nhdsWithin
      (s := (Set.univ : Set (X → ℝ))) hSin'
    rwa [nhdsWithin_univ] at h
  have hpre' : ∀ᶠ x in 𝓝 x₀, (x, h' x) ∈ S := by
    have hc : ContinuousAt (fun x : X → ℝ => (x, h' x)) x₀ := by
      have h1 := (continuousAt_id.prodMk hcd'.continuousAt)
      simpa only [id_eq] using h1
    have hSin' : S ∈ 𝓝 (x₀, h' x₀) := by simpa [hh'] using hSin
    have h := hc.continuousWithinAt.preimage_mem_nhdsWithin
      (s := (Set.univ : Set (X → ℝ))) hSin'
    rwa [nhdsWithin_univ] at h
  have hψh : ∀ᶠ x in 𝓝 x₀, hcont.implicitFunction (n := 1) (by norm_num) hInv x = h x := by
    have h1 := (Filter.Eventually.and hz hpre).mono (fun x hx => by
      rcases hx with ⟨hzx, hSx⟩
      have h2 : tropicalFastField N κ a w x (h x) = tropicalFastField N κ a w x₀ y₀ := by
        rw [hzx, hg]
      exact (Set.mem_ofPred_eq.mp (hS ▸ hSx)).mp h2)
    exact h1
  have hψh' : ∀ᶠ x in 𝓝 x₀, hcont.implicitFunction (n := 1) (by norm_num) hInv x = h' x := by
    have h1 := (Filter.Eventually.and hz' hpre').mono (fun x hx => by
      rcases hx with ⟨hzx, hSx⟩
      have h2 : tropicalFastField N κ a w x (h' x) = tropicalFastField N κ a w x₀ y₀ := by
        rw [hzx, hg]
      exact (Set.mem_ofPred_eq.mp (hS ▸ hSx)).mp h2)
    exact h1
  filter_upwards [hψh, hψh'] with x hx1 hx2
  exact hx2.symm.trans hx1

/-! ## 8. The reduction: the tropical dynamics tracks the slow manifold -/

/-- **The tropical reduction estimate.**  Consider the tropical slow–fast system

```
ẋ = f (x, y) = Network.tropicalSlowField N κ a w x y
ε ẏ = g (x, y) = Network.tropicalFastField N κ a w x y
```

with the local slow manifold `y = h (x)` (`g (x, h x) = 0`).  Assume

* the fast field contracts toward the slow manifold on the region `Ky`, at rate `μ > 0`;
* the slow manifold moves with bounded speed `∑ b, (D h (x) (f (x, y)) b)² ≤ G²`;
* the coupled solution stays in the region (`x t ∈ Kx`, `y t ∈ Ky`).

Then the fast variable tracks the slow manifold with an error that is `O (ε)`:

`∑ b, (y t b - h (x t) b)² ≤ e^{-(μ/ε) t} ∑ b, (y 0 b - h (x 0) b)² + (ε G / μ)²`.

This is the quantitative form of "the tropical system is the reduced system, and the
rescaled dynamics is asymptotic to it". -/
theorem tropical_reduction_estimate (N : Network (X ⊕ E)) (κ : RateConstants N)
    (a : N.R → ℝ) (w : (X ⊕ E) → ℝ) {h : (X → ℝ) → (E → ℝ)}
    {Dh : (X → ℝ) → ((X → ℝ) →L[ℝ] (E → ℝ))} {Kx : Set (X → ℝ)} {Ky : Set (E → ℝ)}
    {μ G ε T : ℝ} (x : ℝ → X → ℝ) (y : ℝ → E → ℝ)
    (hμ : 0 < μ) (hε : 0 < ε) (hT : 0 ≤ T)
    (hh : ∀ z ∈ Kx, HasFDerivAt h (Dh z) z)
    (hzero : ∀ z ∈ Kx, tropicalFastField N κ a w z (h z) = 0)
    (hmono : ∀ z ∈ Kx, ∀ u ∈ Ky, ∀ v ∈ Ky,
      ∑ b : E, (tropicalFastField N κ a w z u b - tropicalFastField N κ a w z v b) * (u b - v b) ≤
        -μ * ∑ b : E, (u b - v b) ^ 2)
    (hG : ∀ z ∈ Kx, ∀ u ∈ Ky,
      ∑ b : E, (Dh z (tropicalSlowField N κ a w z u) b) ^ 2 ≤ G ^ 2)
    (hhK : ∀ z ∈ Kx, h z ∈ Ky)
    (hxc : ContinuousOn x (Icc 0 T)) (hyc : ContinuousOn y (Icc 0 T))
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (tropicalSlowField N κ a w (x t) (y t)) t)
    (hy : ∀ t ∈ Ioo 0 T, HasDerivAt y ((1 / ε) • tropicalFastField N κ a w (x t) (y t)) t)
    (hxK : ∀ t ∈ Icc 0 T, x t ∈ Kx) (hyK : ∀ t ∈ Icc 0 T, y t ∈ Ky)
    (hhc : ContinuousOn (fun t => h (x t)) (Icc 0 T)) :
    ∀ t ∈ Icc 0 T, SlowFast.fastDev h x y t ≤
      Real.exp (-(μ / ε * t)) * SlowFast.fastDev h x y 0 + (ε * G / μ) ^ 2 := by
  exact SlowFast.fast_deviation_le (f := tropicalSlowField N κ a w)
    (g := tropicalFastField N κ a w) (h := h) (Dh := Dh) (x := x) (y := y)
    hμ hε hT hh hzero hmono hG hhK hxc hyc hx hy hxK hyK hhc

/-! ## 9. The tropical equilibration determines the equilibrium of the reduced system -/

/-- **The tropical equilibration determines the equilibrium of the reduced system.**  Let
`ξ` be a positive root of the tropical leading system, i.e. a solution of the tropical
system `L (ξ) = 0`.  Split `ξ` into its slow and fast parts `x₀` and `y₀`, and let `h` be
the local slow manifold of the tropical reduced system through `(x₀, y₀)`.  Then
`(x₀, h x₀)` is an **equilibrium of the reduced system** `ẋ = f (x, h x)`. -/
theorem tropical_reduced_equilibrium (N : Network (X ⊕ E)) (κ : RateConstants N)
    (a : N.R → ℝ) (w : (X ⊕ E) → ℝ) {ξ : Concentration (X ⊕ E)}
    (hroot : tropicalLeadingField N κ a w ξ = 0)
    {x₀ : X → ℝ} {y₀ : E → ℝ} {h : (X → ℝ) → (E → ℝ)}
    (hx₀ : ∀ s : X, x₀ s = ξ (Sum.inl s)) (hy₀ : ∀ e : E, y₀ e = ξ (Sum.inr e))
    (hh : h x₀ = y₀) :
    tropicalSlowField N κ a w x₀ (h x₀) = 0 := by
  have hemb : embedConcentration x₀ (h x₀) = ξ := by
    funext s
    cases s with
    | inl a =>
        have h1 : embedConcentration x₀ (h x₀) (Sum.inl a) = x₀ a := rfl
        rw [h1]
        exact hx₀ a
    | inr b =>
        have h2 : embedConcentration x₀ (h x₀) (Sum.inr b) = (h x₀) b := rfl
        rw [h2, hh]
        exact hy₀ b
  funext s
  have : tropicalSlowField N κ a w x₀ (h x₀) s
      = tropicalLeadingField N κ a w ξ (Sum.inl s) := by
    simp only [tropicalSlowField]
    rw [hemb]
  rw [this]
  have hz := congrFun hroot (Sum.inl s)
  simpa using hz

/-! ## 10. The linear case -/

omit [DecidableEq X] in
/-- **The linear case: the reduced system converges to the tropical equilibrium.**  Let the
reduced system be linear, `ẋ = A (x - xstar)`, and suppose `A` is Hurwitz with rate `μ > 0`
(the Lyapunov–Krasovskii condition of `HurwitzRate'`).  Then the energy of the solution
decays exponentially:

`∑ s, (x t s - xstar s)² ≤ e^{-2 μ t} ∑ s, (x 0 s - xstar s)²`.

This is the case in which the tropical equilibration *is* the steady state of the reduced
system: the reduced dynamics contracts to it. -/
theorem tropical_linear_reduced_converges {A : (X → ℝ) →L[ℝ] (X → ℝ)} {μ : ℝ} {xstar : X → ℝ}
    (hA : HurwitzRate' A μ) (hμ : 0 < μ) {x : ℝ → X → ℝ}
    (hx : ∀ t, HasDerivAt x (A (x t - xstar)) t) :
    ∀ t, 0 ≤ t → (∑ s : X, (x t s - xstar s) ^ 2) ≤
      Real.exp (-(2 * μ * t)) * (∑ s : X, (x 0 s - xstar s) ^ 2) := by
  have hμ' : 0 < μ := hμ
  have hz : ∀ t, HasDerivAt (fun s : ℝ => x s - xstar) (A (x t - xstar)) t := by
    intro t
    exact (hx t).sub_const xstar
  have h1 := hurwitz_linear_decay' hA hz
  intro t ht
  have h2 := h1 t ht
  simpa using h2


/-! ## 11. A concrete instance: the chain `∅ → X → Y → ∅` -/

namespace TropicalSlowFastInstance

open Network

/-- The species of the instance: one slow species `X` and one fast species `Y`. -/
abbrev SEx := Fin 1 ⊕ Fin 1

/-- The three reactions of the chain `∅ → X → Y → ∅`. -/
abbrev REx := Fin 3

/-- The source complexes of the chain `∅ → X → Y → ∅`. -/
def exSource : REx → SEx → ℕ
  | 0 => fun _ => 0
  | 1 => fun s => if s = Sum.inl 0 then 1 else 0
  | 2 => fun s => if s = Sum.inr 0 then 1 else 0

/-- The target complexes of the chain `∅ → X → Y → ∅`. -/
def exTarget : REx → SEx → ℕ
  | 0 => fun s => if s = Sum.inl 0 then 1 else 0
  | 1 => fun s => if s = Sum.inr 0 then 1 else 0
  | 2 => fun _ => 0

/-- The network `∅ → X → Y → ∅`. -/
def exNetwork : Network SEx where
  R := REx
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun r => ⟨exSource r, exTarget r⟩

/-- The orders of the instance: `a = (0, 0, 1)`. -/
def exA : REx → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => 1

/-- The valuation of the instance: `w = (0, -1)`. -/
def exW : SEx → ℝ
  | Sum.inl _ => 0
  | Sum.inr _ => -1

/-- The (unscaled) rate constants of the instance: all equal to `1`. -/
def exκ : RateConstants exNetwork := ⟨fun _ => 1, fun _ => by norm_num⟩

/-- **All three reactions have tropical order `0`.**  The instance is therefore at a
*tropical equilibrium* for every species equation: the tropical equilibration condition is
satisfied because the leading part of every equation contains both a producing and a
consuming reaction. -/
theorem ex_tropicalOrder (r : REx) : tropicalOrder exNetwork exA exW r = 0 := by
  fin_cases r <;>
    simp [tropicalOrder, exNetwork, exSource, exTarget, exA, exW]

/-- **The valuation `w = (0, -1)` is a tropical equilibration of the chain
`∅ → X → Y → ∅`.**  The slow species `X` has tropical time scale `0` and the fast species
`Y` has tropical time scale `1`: the chain is a genuine slow–fast system. -/
theorem ex_isEquil : IsTropicalEquilibration exNetwork exA exW := by
  intro s hs
  cases s with
  | inl a =>
      have ha : a = 0 := Fin.ext (by omega)
      subst ha
      refine ⟨(⟨0, by norm_num⟩ : REx), (⟨1, by norm_num⟩ : REx), ?_, ?_, ?_⟩
      · simp [exNetwork, exSource, exTarget, Network.reactionVector_apply]
      · simp [exNetwork, exSource, exTarget, Network.reactionVector_apply]
      · intro r hr
        rw [ex_tropicalOrder r, ex_tropicalOrder (⟨0, by norm_num⟩ : REx),
          ex_tropicalOrder (⟨1, by norm_num⟩ : REx)]
        exact ⟨le_rfl, le_rfl⟩
  | inr b =>
      have hb : b = 0 := Fin.ext (by omega)
      subst hb
      refine ⟨(⟨1, by norm_num⟩ : REx), (⟨2, by norm_num⟩ : REx), ?_, ?_, ?_⟩
      · simp [exNetwork, exSource, exTarget, Network.reactionVector_apply]
      · simp [exNetwork, exSource, exTarget, Network.reactionVector_apply]
      · intro r hr
        rw [ex_tropicalOrder r, ex_tropicalOrder (⟨1, by norm_num⟩ : REx),
          ex_tropicalOrder (⟨2, by norm_num⟩ : REx)]
        exact ⟨le_rfl, le_rfl⟩

/-- **The slow–fast time scales of the instance.**  The slow species `X` has tropical time
scale `0` and the fast species `Y` has tropical time scale `1`: the chain `∅ → X → Y → ∅` with
the orders `a = (0, 0, 1)` and the valuation `w = (0, -1)` is a genuine two-tier slow–fast
system, and the tropical equilibration of the instance is the statement that the leading
system of each tier balances. -/
theorem ex_timeScales :
    (tropicalOrder exNetwork exA exW (⟨0, by norm_num⟩ : REx) - exW (Sum.inl 0) = 0) ∧
    (tropicalOrder exNetwork exA exW (⟨1, by norm_num⟩ : REx) - exW (Sum.inr 0) = 1) := by
  simp [ex_tropicalOrder, exW]

end TropicalSlowFastInstance


end Network

end CRNT
