import CRNT.Oscillation.ReturnMapAttraction
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Scalar Poincare stability from a derivative inside the unit disk

For a planar autonomous ODE the Poincare section is one-dimensional.  In that setting no general
matrix spectral-radius theorem is needed: if the scalar return map fixes `x₀`, its derivative varies
continuously, and `|P'(x₀)| < 1`, then a sufficiently small closed interval around `x₀` is mapped into
itself and the return map is a strict contraction there.

Together with `ReturnMapAttraction`, this proves geometric convergence of successive section hits.
The remaining continuous-time orbital-stability step is only the interpolation between returns.
-/

namespace CRNT

open Filter Set Topology

/-- A `C¹` scalar map represented by an explicit continuous derivative. -/
structure ScalarC1Map (f : ℝ → ℝ) where
  derivative : ℝ → ℝ
  hasDeriv : ∀ x, HasDerivAt f (derivative x) x
  continuous_derivative : Continuous derivative

/-- A local invariant interval on which a scalar map is a strict contraction. -/
structure ScalarLocalContraction (f : ℝ → ℝ) (x₀ : ℝ) where
  radius : ℝ
  radius_pos : 0 < radius
  factor : ℝ
  factor_nonneg : 0 ≤ factor
  factor_lt_one : factor < 1
  mapsTo : MapsTo f (Icc (x₀ - radius) (x₀ + radius))
    (Icc (x₀ - radius) (x₀ + radius))
  dist_le : ∀ x ∈ Icc (x₀ - radius) (x₀ + radius),
    ∀ y ∈ Icc (x₀ - radius) (x₀ + radius),
      dist (f x) (f y) ≤ factor * dist x y

namespace ScalarC1Map

/-- **Scalar local contraction theorem.** A fixed point whose derivative has modulus below one has
a closed invariant neighbourhood on which the map is a strict contraction. -/
theorem exists_localContraction {f : ℝ → ℝ} (C : ScalarC1Map f) {x₀ : ℝ}
    (hfix : f x₀ = x₀) (hstable : |C.derivative x₀| < 1) :
    Nonempty (ScalarLocalContraction f x₀) := by
  let q : ℝ := (|C.derivative x₀| + 1) / 2
  have habsnonneg : 0 ≤ |C.derivative x₀| := abs_nonneg _
  have hqnonneg : 0 ≤ q := by
    dsimp [q]
    linarith
  have habs_lt_q : |C.derivative x₀| < q := by
    dsimp [q]
    linarith
  have hq_lt_one : q < 1 := by
    dsimp [q]
    linarith
  have hcontAbs : Continuous (fun x => |C.derivative x|) :=
    continuous_abs.comp C.continuous_derivative
  have hev : ∀ᶠ x in 𝓝 x₀, |C.derivative x| < q :=
    (hcontAbs.tendsto x₀).eventually (eventually_lt_nhds habs_lt_q)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ρ, hρ, hball⟩ := hev
  let δ : ℝ := ρ / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδ_lt_ρ : δ < ρ := by dsimp [δ]; linarith
  have hderiv_bound : ∀ z ∈ Icc (x₀ - δ) (x₀ + δ), |C.derivative z| ≤ q := by
    intro z hz
    have hdist : dist z x₀ < ρ := by
      rw [Real.dist_eq]
      have hzlo : x₀ - δ ≤ z := hz.1
      have hzhi : z ≤ x₀ + δ := hz.2
      have habs : |z - x₀| ≤ δ := by
        rw [abs_le]
        constructor <;> linarith
      exact lt_of_le_of_lt habs hδ_lt_ρ
    exact (hball hdist).le
  have hlip : ∀ x ∈ Icc (x₀ - δ) (x₀ + δ),
      ∀ y ∈ Icc (x₀ - δ) (x₀ + δ),
        dist (f x) (f y) ≤ q * dist x y := by
    intro x hx y hy
    have hdiff : ∀ z ∈ Icc (x₀ - δ) (x₀ + δ), DifferentiableAt ℝ f z :=
      fun z _ => (C.hasDeriv z).differentiableAt
    have hbound : ∀ z ∈ Icc (x₀ - δ) (x₀ + δ), ‖deriv f z‖ ≤ q := by
      intro z hz
      rw [(C.hasDeriv z).deriv, Real.norm_eq_abs]
      exact hderiv_bound z hz
    have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (f := f)
      (s := Icc (x₀ - δ) (x₀ + δ)) hdiff hbound (convex_Icc _ _) hy hx
    simpa [Real.dist_eq, Real.norm_eq_abs, abs_sub_comm] using hmvt
  have hmaps : MapsTo f (Icc (x₀ - δ) (x₀ + δ))
      (Icc (x₀ - δ) (x₀ + δ)) := by
    intro x hx
    have hx0 : x₀ ∈ Icc (x₀ - δ) (x₀ + δ) := by
      constructor <;> linarith
    have hcontract := hlip x hx x₀ hx0
    rw [hfix] at hcontract
    have hdistx : dist x x₀ ≤ δ := by
      rw [Real.dist_eq]
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2]
    have hdistf : dist (f x) x₀ < δ := by
      have hqδ : q * δ < δ := by
        have : 0 < (1 - q) * δ := mul_pos (sub_pos.mpr hq_lt_one) hδ
        nlinarith
      exact lt_of_le_of_lt (hcontract.trans (mul_le_mul_of_nonneg_left hdistx hqnonneg)) hqδ
    rw [Real.dist_eq] at hdistf
    rw [abs_lt] at hdistf
    constructor <;> linarith
  exact ⟨
    { radius := δ
      radius_pos := hδ
      factor := q
      factor_nonneg := hqnonneg
      factor_lt_one := hq_lt_one
      mapsTo := hmaps
      dist_le := hlip }⟩

end ScalarC1Map

namespace ScalarLocalContraction

/-- The invariant interval as a metric subtype. -/
abbrev LocalInterval {f : ℝ → ℝ} {x₀ : ℝ} (D : ScalarLocalContraction f x₀) :=
  Set.Icc (x₀ - D.radius) (x₀ + D.radius)

/-- Restriction of the scalar return map to the invariant local interval. -/
def restrictedMap {f : ℝ → ℝ} {x₀ : ℝ} (D : ScalarLocalContraction f x₀) :
    D.LocalInterval → D.LocalInterval :=
  fun x => ⟨f x, D.mapsTo x.property⟩

/-- The center fixed point as an element of the invariant interval. -/
def center {f : ℝ → ℝ} {x₀ : ℝ} (D : ScalarLocalContraction f x₀) : D.LocalInterval :=
  ⟨x₀, by constructor <;> linarith [D.radius_pos]⟩

/-- Bundle the restricted scalar return map as the generic contraction object used by
`ReturnMapAttraction`. -/
def toContractingReturnMapData {f : ℝ → ℝ} {x₀ : ℝ}
    (D : ScalarLocalContraction f x₀) (hfix : f x₀ = x₀) :
    ContractingReturnMapData D.LocalInterval where
  returnMap := D.restrictedMap
  fixedPoint := D.center
  factor := D.factor
  factor_nonneg := D.factor_nonneg
  factor_lt_one := D.factor_lt_one
  fixed := by
    apply Subtype.ext
    exact hfix
  dist_le := by
    intro x y
    change dist (f x) (f y) ≤ D.factor * dist (x : ℝ) (y : ℝ)
    exact D.dist_le x x.property y y.property

/-- Successive local section returns converge to the fixed point geometrically. -/
theorem tendsto_restrictedIterates {f : ℝ → ℝ} {x₀ : ℝ}
    (D : ScalarLocalContraction f x₀) (hfix : f x₀ = x₀) (x : D.LocalInterval) :
    Tendsto ((D.toContractingReturnMapData hfix).iterates x) atTop
      (𝓝 (D.toContractingReturnMapData hfix).fixedPoint) :=
  (D.toContractingReturnMapData hfix).tendsto_iterates_fixedPoint x

end ScalarLocalContraction

end CRNT
