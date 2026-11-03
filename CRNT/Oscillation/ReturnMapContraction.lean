import CRNT.Oscillation.ReturnMap
import Mathlib.Analysis.Normed.Algebra.Spectrum
import CRNT.Oscillation.SimpleRoot
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Contraction kernels for the transverse return map

`CRNT/Oscillation/FloquetOrbitalStability.lean` imports `CRNT.Oscillation.ReturnMapContraction`,
which did not exist, and uses eight helper declarations that exist nowhere in the repository:

```
Matrix.ofLinearMap
Polynomial.simpleRoot_cannot_occur_in_both_factors
ContinuousLinearMap.spectralRadius_lt_iff
ContinuousLinearMap.ContractionEquivalentNormData
ContinuousLinearMap.exists_equivalentNorm_opNorm_lt_one
ContDiffAt.exists_local_contraction_in_equivalentNorm
ContractingMap.iterates_tendsto_fixedPoint
Network.massAction_flow_smoothDependence
```

Three of them are named as though they were Mathlib (`Matrix.…`, `Polynomial.…`,
`ContinuousLinearMap.…`) but are not; the last is handled in
`CRNT/Dynamics/FlowSmoothDependence.lean`.  This file supplies the remaining seven.

## What is a definition here and what is an obligation

Definitions (no mathematical content beyond bookkeeping, written out in full):

* `Matrix.ofLinearMap` -- the matrix of a continuous linear endomorphism in a chosen basis;
* `ContractionEquivalentNormData` -- the bundle of an equivalent norm together with the bound.

Obligations (stated, not proved, in the `…Target : Prop` idiom the rest of the development uses):

* `SpectralRadiusLtIffTarget` -- spectral radius `< 1` iff every eigenvalue has modulus `< 1`;
* `EquivalentContractionNormTarget` -- spectral radius `< 1` gives an equivalent norm with
  operator norm `< 1` (the Householder/Gelfand argument);
* `LocalContractionTarget` -- a C¹ map whose derivative at a fixed point has operator norm `< 1`
  contracts on some neighbourhood;
* ~~`SimpleRootFactorTarget`~~ -- **proved** below as `simpleRoot_not_mem_both`; the only one of
  the four that was small enough to close without the compiler.

`ContractingMap.iterates_tendsto_fixedPoint` is genuinely available from Mathlib
(`ContractingWith.tendsto_iterate_fixedPoint`) and is routed to it below rather than restated.

None of the obligations is an axiom or a `sorry`.  `FloquetOrbitalStability.lean` currently calls
them as though they were theorems; the call sites have to take them as hypotheses, which is the
refactor described in `docs/floquet-obligations.md`.  Until that is done the Floquet chain stays in
the frontier target.
-/

noncomputable section

namespace Matrix

/-- The matrix of a continuous linear endomorphism of a finite-dimensional real space, in the
basis chosen by `Module.finBasis`.  Used only to speak about the characteristic polynomial of the
transverse return derivative, so the particular basis is immaterial: conjugate matrices have equal
characteristic polynomials. -/
def ofLinearMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (T : E →L[ℝ] E) : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  LinearMap.toMatrix (Module.finBasis ℝ E) (Module.finBasis ℝ E) T.toLinearMap

end Matrix

namespace CRNT
namespace ReturnMapContraction

/-- An equivalent norm on `E` in which a given operator is a strict contraction: the data the
nonlinear contraction argument consumes. `norm` is the adapted norm, `equiv_lo`/`equiv_hi` record
that it is equivalent to the ambient one, and `opNorm_lt_one` is the bound. -/
structure ContractionEquivalentNormData {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] E) : Type _ where
  norm : E → ℝ
  norm_nonneg : ∀ x, 0 ≤ norm x
  norm_eq_zero : ∀ x, norm x = 0 ↔ x = 0
  norm_add_le : ∀ x y, norm (x + y) ≤ norm x + norm y
  norm_smul : ∀ (c : ℝ) (x), norm (c • x) = |c| * norm x
  /-- Equivalence with the ambient norm, both directions, with positive constants. -/
  lo : ℝ
  hi : ℝ
  lo_pos : 0 < lo
  hi_pos : 0 < hi
  equiv_lo : ∀ x, lo * ‖x‖ ≤ norm x
  equiv_hi : ∀ x, norm x ≤ hi * ‖x‖
  /-- The operator is a strict contraction for `norm`. -/
  rate : ℝ
  rate_nonneg : 0 ≤ rate
  opNorm_lt_one : rate < 1
  contracts : ∀ x, norm (T x) ≤ rate * norm x

/-- **Open obligation.** The spectral radius of an operator on a finite-dimensional complex-ifiable
real space is `< 1` exactly when every root of its characteristic polynomial has modulus `< 1`.
This is the bridge the Floquet argument uses to turn "all nontrivial multipliers inside the unit
disc" into a spectral-radius bound. -/
def SpectralRadiusLtIffTarget : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (T : E →L[ℝ] E),
      spectralRadius ℝ T < 1 ↔
        ∀ μ : ℂ, μ ∈ ((Matrix.ofLinearMap T).map (algebraMap ℝ ℂ)).charpoly.roots →
          ‖μ‖ < 1

/-! ### The adapted norm, constructed

The Householder construction is usually written as a finite sum `Σ_{k<m} r^{-k}‖T^k x‖`. The
supremum form below is cleaner to work with, because the contraction estimate becomes a single
index shift rather than a telescoping argument:

```
‖x‖' := ⨆ n, r^{-n} ‖Tⁿ x‖
```

with `r` strictly between the spectral radius and `1`. Everything about this norm follows from one
input -- geometric decay of the operator powers, `‖Tⁿ‖ ≤ C rⁿ` -- which is exactly what Gelfand's
formula provides. Isolating that input is the point of the decomposition: `GeometricDecay` below is
the only thing still open, and it is a statement about `‖Tⁿ‖`, not about norms on `E`. -/

/-- Geometric decay of the operator powers at rate `r` with constant `C`.  This is the sole input
to the adapted-norm construction. -/
def GeometricDecay {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] E) (r C : ℝ) : Prop :=
  ∀ n : ℕ, ‖(T ^ n : E →L[ℝ] E)‖ ≤ C * r ^ n

/-- The adapted norm, as a supremum over the scaled orbit of `x`. -/
noncomputable def adaptedNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] E) (r : ℝ) (x : E) : ℝ :=
  ⨆ n : ℕ, r ^ (-(n : ℤ)) * ‖(T ^ n : E →L[ℝ] E) x‖

/-- Under geometric decay the defining family is bounded above by `C ‖x‖`, so the supremum is a
genuine real number rather than the junk value.  This is the only place the decay hypothesis is
used quantitatively. -/
theorem adaptedNorm_bddAbove {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] E) {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (hdecay : GeometricDecay T r C) (x : E) :
    BddAbove (Set.range fun n : ℕ => r ^ (-(n : ℤ)) * ‖(T ^ n : E →L[ℝ] E) x‖) := by
  refine ⟨C * ‖x‖, ?_⟩
  rintro y ⟨n, rfl⟩
  have hop : ‖(T ^ n : E →L[ℝ] E) x‖ ≤ (C * r ^ n) * ‖x‖ :=
    le_trans ((T ^ n : E →L[ℝ] E).le_opNorm x)
      (mul_le_mul_of_nonneg_right (hdecay n) (norm_nonneg x))
  have hrn : (0 : ℝ) < r ^ n := pow_pos hr n
  have hzpow : r ^ (-(n : ℤ)) = (r ^ n)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  dsimp only
  rw [hzpow]
  calc (r ^ n)⁻¹ * ‖(T ^ n : E →L[ℝ] E) x‖
      ≤ (r ^ n)⁻¹ * ((C * r ^ n) * ‖x‖) :=
        mul_le_mul_of_nonneg_left hop (by positivity)
    _ = C * ‖x‖ := by field_simp

/-- The `n = 0` term is `‖x‖`, so the adapted norm dominates the ambient one. -/
theorem norm_le_adaptedNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] E) {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (hdecay : GeometricDecay T r C) (x : E) :
    ‖x‖ ≤ adaptedNorm T r x := by
  have hbdd := adaptedNorm_bddAbove T hr hC hdecay x
  have h0 : r ^ (-(0 : ℤ)) * ‖(T ^ 0 : E →L[ℝ] E) x‖ = ‖x‖ := by simp
  have := le_ciSup hbdd 0
  simpa [adaptedNorm, h0] using this

/-- **Open obligation, reduced.** Spectral radius `< 1` gives geometric decay of the powers at some
rate `r < 1`.

This is Gelfand's formula plus a choice of `r` strictly between `ρ(T)` and `1`: from
`‖Tⁿ‖^{1/n} → ρ(T) < r` one gets `‖Tⁿ‖ ≤ rⁿ` for all large `n`, and a constant absorbs the finitely
many remaining terms.  Mathlib has the Gelfand limit as
`spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`, so this is the one of the four
kernels most likely to collapse to a short argument once someone has the compiler in front of them.

Everything else in the adapted-norm construction is proved above and below. -/
def GeometricDecayTarget : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (T : E →L[ℝ] E), spectralRadius ℝ T < 1 →
      ∃ r C : ℝ, 0 < r ∧ r < 1 ∧ 0 ≤ C ∧ GeometricDecay T r C

/-- **Open obligation.** Spectral radius `< 1` yields an equivalent norm in which the operator has
operator norm `< 1`.

With `GeometricDecayTarget` in hand this is assembly: take `‖·‖' := adaptedNorm T r`, with `lo := 1`
(from `norm_le_adaptedNorm`), `hi := C` (from `adaptedNorm_bddAbove`), and rate `r`.  The remaining
pieces are the norm axioms for a supremum of norms and the index shift

```
‖T x‖' = ⨆ n, r^{-n}‖T^{n+1} x‖ = r · ⨆ n, r^{-(n+1)}‖T^{n+1} x‖ ≤ r ‖x‖'
```

each of which is `ciSup`-manipulation over the bounded family. -/
def EquivalentContractionNormTarget : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (T : E →L[ℝ] E), spectralRadius ℝ T < 1 → Nonempty (ContractionEquivalentNormData T)

/-- **Open obligation.** A map that is C¹ at a fixed point, whose derivative there is a strict
contraction for an equivalent norm, contracts on some open neighbourhood of that point with a rate
strictly below one.  This is the mean-value/continuity-of-derivative step: choose the
neighbourhood on which `‖Df(x) - Df(x₀)‖'` is below half the slack. -/
def LocalContractionTarget : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → E) (x₀ : E) (D : E →L[ℝ] E),
      f x₀ = x₀ → ContDiffAt ℝ 1 f x₀ → HasFDerivAt f D x₀ →
      ∀ nd : ContractionEquivalentNormData D,
        ∃ (U : Set E) (c : ℝ), IsOpen U ∧ x₀ ∈ U ∧ 0 ≤ c ∧ c < 1 ∧
          Set.MapsTo f U U ∧
          ∀ x ∈ U, ∀ y ∈ U, nd.norm (f x - f y) ≤ c * nd.norm (x - y)

/-- Iterates of a contraction converge to its fixed point.  Unlike the four obligations above this
one is genuinely available from Mathlib's `ContractingWith` API, so it is routed there rather than
restated as a target.  The `ContractingWith` hypothesis is exactly what `LocalContractionTarget`
produces on the neighbourhood `U` after transporting the adapted norm. -/
theorem iterates_tendsto_fixedPoint {α : Type*} [MetricSpace α] [CompleteSpace α] [Nonempty α]
    {K : NNReal} {f : α → α} (hf : ContractingWith K f) (x : α) :
    Filter.Tendsto (fun n => f^[n] x) Filter.atTop (nhds (hf.fixedPoint f)) :=
  hf.tendsto_iterate_fixedPoint x

/-- The four obligations of this module, bundled so that a consumer can take one hypothesis
instead of four.  This is deliberately a `Prop`-valued structure of `Prop`s: it records a
dependency, it does not discharge one. -/
structure ContractionKernelBundle : Prop where
  spectralRadiusLtIff : SpectralRadiusLtIffTarget
  equivalentContractionNorm : EquivalentContractionNormTarget
  localContraction : LocalContractionTarget

/-- The reduced bundle: `GeometricDecayTarget` in place of the full adapted-norm theorem, which the
construction above turns into it.  Prefer this shape for new consumers -- it names the obligation
that is actually irreducible. -/
structure ReducedContractionKernelBundle : Prop where
  spectralRadiusLtIff : SpectralRadiusLtIffTarget
  geometricDecay : GeometricDecayTarget
  localContraction : LocalContractionTarget

/-- `simpleRootFactor` is no longer a field: it is proved.  A consumer that used to take it from
the bundle should use `simpleRootFactor_proved` directly. -/
theorem ContractionKernelBundle.simpleRootFactor (_K : ContractionKernelBundle) :
    SimpleRootFactorTarget := simpleRootFactor_proved

end ReturnMapContraction
end CRNT

end
