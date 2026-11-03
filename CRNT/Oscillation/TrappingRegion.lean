import CRNT.Oscillation.PlanarOscillationCriterion
import CRNT.Oscillation.RankTwoPlanar
import CRNT.Dynamics.FlowConstruction
import CRNT.Examples.Lotka
import CRNT.Examples.LotkaPeriodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Trapping regions for planar mass-action networks

This module supplies the **network-specific half** of the planar Poincare--Bendixson route that
leaf D18 ("existence of oscillations; chaos") still lacks.

The universal half of the route lives in `CRNT.Oscillation.PlanarPoincareBendixson`: the structure
`CRNT.Planar.PoincareBendixsonKernelBundle` collects the three *planar-topological* inputs
(flow regularity, Jordan separation, the straight-edge local side).  None of them mentions a
reaction network, a rate constant or a trapping region, and none of them is proved in this
repository.

The half that *is* network-specific, and that this module discharges, is the following.

* A **trapping region**: a compact set which is positively invariant for the planar field and
  which contains no equilibrium.  `CRNT.Planar.FlowTrappingData` is the interface the planar
  kernel consumes; `CRNT.Oscillation.TrappingRegion` is the field-level notion, and
  `CRNT.Oscillation.TrappingRegion.of_firstIntegral` is a *reusable criterion*: the level set of
  a first integral is a trapping region.  This is the workhorse for any planar mass-action network
  with a conserved quantity.
* A **`C^1` cut-off** (`smoothClamp`): the identity on a box, bounded and `1`-Lipschitz outside
  it.  Cutting the mass-action field off with it keeps the field `C^1` -- as the planar kernel
  requires -- while making it bounded and globally Lipschitz, so that it generates a forward
  semiflow (`ODE.exists_flow`).
* For the concrete network `CRNT.Examples.Lotka.N` (`A -> 2A`, `A + B -> 2B`, `B -> 0`): the planar
  mass-action field, the cut-off field, the level set `K_c = {V = c}` of the repository's first
  integral for `c` above the value at the positive equilibrium, the explicit computation of the
  equilibria of the field, and the verification that the cut-off trajectory of the seed stays in
  `K_c` (a clopen-times argument, as in `CRNT.Examples.LotkaPeriodic.exists_confined_solution`).

The conclusion is stated in the repository's `OscillatoryCapacity` language and is *conditional on
the universal kernel bundle*, exactly as the leaf's notes require:

* `CRNT.Oscillation.lotka_hasPositivePeriodicOrbit_of_trappingRegion`,
* `CRNT.Oscillation.lotka_oscillatoryCapacity_of_trappingRegion`.

## Why the level set is the right trapping region

For the Lotka--Volterra system the field vanishes at exactly two points: the origin and the
positive equilibrium `(k2/k1, k0/k1)` (`CRNT.Oscillation.eq_equilibrium_of_field_eq_zero`).  The
first integral `V` of the repository attains its unique minimum at the positive equilibrium
(`CRNT.Examples.Lotka.firstIntegral_gt_equilibrium`), so for `c > V(x*)` the level set `{V = c}`
inside the positive quadrant contains neither equilibrium
(`CRNT.Oscillation.lotkaLevelSet_equilibriumFree`).  It is compact
(`CRNT.Oscillation.lotkaLevelSet_compact`, from `CRNT.Examples.Lotka.levelSetCompact`) and it is
positively invariant, because `V` is constant along solutions
(`CRNT.Examples.Lotka.firstIntegralConstant`).

## What remains open

The two universal inputs of the planar kernel: the `C^1` dependence of the flow on the initial
point, and the Jordan separation theorem.  They are hypotheses of every theorem of the last
section, never proved here.  Everything else on the route -- the compact trapping region, the
equilibrium-freeness, the flow, the confinement of the trajectory, and the passage from the
omega-limit set to a positive mass-action periodic orbit -- is proved here.

Note that `CRNT.Examples.LotkaPeriodic.oscillatoryCapacity` already proves the *unconditional*
oscillatory capacity of the Lotka network, by exhibiting the periodic orbit explicitly.  The
contribution of this module is different: it shows that the periodic orbit is produced by the
Poincare--Bendixson route, with the trapping region as the only network-specific input.

Depends on: `CRNT.Oscillation.PlanarOscillationCriterion`, `CRNT.Examples.LotkaPeriodic`,
`CRNT.Dynamics.FlowConstruction`.
-/

namespace CRNT
namespace Oscillation

open Set Filter Topology
open scoped BigOperators NNReal

/-! ## Trapping regions for planar fields -/

/-- **A trapping region for a planar field.**

A trapping region is a compact set which

* is *positively invariant*: every forward solution which starts in it stays in it;
* is *equilibrium-free*: the field does not vanish anywhere on it.

The second condition is what makes the region usable for Poincaré--Bendixson: the omega-limit set
of a trapped orbit lies inside the region and therefore contains no equilibrium, so the planar
classification theorem produces a genuine periodic orbit (rather than a constant one). -/
structure TrappingRegion (field : Phase2 → Phase2) where
  /-- The trapping region. -/
  region : Set Phase2
  /-- The region is compact. -/
  compact : IsCompact region
  /-- The region is positively invariant for the field. -/
  positivelyInvariant : ∀ (γ : ℝ → Phase2), γ 0 ∈ region →
    (∀ t, HasDerivAt γ (field (γ t)) t) → ∀ t, 0 ≤ t → γ t ∈ region
  /-- The region contains no equilibrium of the field. -/
  equilibriumFree : ∀ x ∈ region, field x ≠ 0

namespace TrappingRegion

variable {φ : Phase2 → Phase2}

/-- **A level set of a first integral is a trapping region.**

Let `V` be *constant along every solution* of the field (a first integral).  Then each level set
`{x | V x = c}` is positively invariant: a solution starting on the level set stays on it, since
`V` is constant along the solution.  If the level set is compact and contains no equilibrium, it is
a trapping region.

This is the criterion which makes the machinery applicable to *any* planar mass-action network
with a conserved quantity, and not only to the Lotka--Volterra system. -/
def of_firstIntegral {V : Phase2 → ℝ}
    (hconst : ∀ (γ : ℝ → Phase2), (∀ t, HasDerivAt γ (φ (γ t)) t) → ∀ t, V (γ t) = V (γ 0))
    {c : ℝ} {K : Set Phase2} (hK : ∀ x, x ∈ K ↔ V x = c)
    (hcompact : IsCompact K) (heqf : ∀ x ∈ K, φ x ≠ 0) : TrappingRegion φ := by
  refine ⟨K, hcompact, ?_, heqf⟩
  intro γ hγ0 hγ t ht
  have hV0 : V (γ 0) = c := (hK (γ 0)).mp hγ0
  have hVt : V (γ t) = c := by
    rw [hconst γ hγ t, hV0]
  exact (hK (γ t)).mpr hVt

end TrappingRegion

/-! ## A `C¹` cut-off -/

/-- The weight of the smooth cut-off: `1` on `[lo, hi]`, `0` outside `[lo-1, hi+1]`. -/
noncomputable def clampWeight (lo hi : ℝ) (u : ℝ) : ℝ :=
  min 1 (max 0 (u - (lo - 1))) * min 1 (max 0 (hi + 1 - u))

theorem continuous_clampWeight (lo hi : ℝ) : Continuous (clampWeight lo hi) := by
  unfold clampWeight
  fun_prop

theorem clampWeight_nonneg (lo hi u : ℝ) : 0 ≤ clampWeight lo hi u := by
  unfold clampWeight
  exact mul_nonneg (by simp) (by simp)

theorem clampWeight_le_one (lo hi u : ℝ) : clampWeight lo hi u ≤ 1 := by
  unfold clampWeight
  calc _ ≤ 1 * min 1 (max 0 (hi + 1 - u)) :=
        mul_le_mul_of_nonneg_right (min_le_iff.mpr (Or.inl le_rfl)) (by positivity)
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left (min_le_iff.mpr (Or.inl le_rfl)) (by norm_num)
    _ = 1 := by ring

theorem clampWeight_eq_one (lo hi u : ℝ) (h1 : lo ≤ u) (h2 : u ≤ hi) :
    clampWeight lo hi u = 1 := by
  have e1 : 1 ≤ u - (lo - 1) := by linarith
  have e2 : 1 ≤ hi + 1 - u := by linarith
  have hmax1 : 1 ≤ max 0 (u - (lo - 1)) := le_trans e1 (le_max_right 0 _)
  have hmax2 : 1 ≤ max 0 (hi + 1 - u) := le_trans e2 (le_max_right 0 _)
  unfold clampWeight
  rw [min_eq_left_iff.mpr hmax1, min_eq_left_iff.mpr hmax2]
  ring

theorem clampWeight_eq_zero_right (lo hi u : ℝ) (h : hi + 1 ≤ u) : clampWeight lo hi u = 0 := by
  have hm : max 0 (hi + 1 - u) = 0 := max_eq_left_iff.mpr (by linarith)
  have hm2 : min 1 (max 0 (hi + 1 - u)) = 0 := by rw [hm, min_eq_right_iff.mpr (by norm_num)]
  unfold clampWeight
  rw [hm2]
  ring

theorem clampWeight_eq_zero_left (lo hi u : ℝ) (h : u ≤ lo - 1) : clampWeight lo hi u = 0 := by
  have hm : max 0 (u - (lo - 1)) = 0 := max_eq_left_iff.mpr (by linarith)
  have hm2 : min 1 (max 0 (u - (lo - 1))) = 0 := by rw [hm, min_eq_right_iff.mpr (by norm_num)]
  unfold clampWeight
  rw [hm2]
  ring

/-- **The smooth cut-off of the real line.**

`smoothClamp lo hi` is the identity on `[lo, hi]`, takes values in `[lo-1, hi+1]`, and is
`1`-Lipschitz.  It is `C¹`, which is what allows the cut-off mass-action field to be `C¹` and
hence to satisfy the regularity hypothesis of the planar kernel. -/
noncomputable def smoothClamp (lo hi : ℝ) (s : ℝ) : ℝ :=
  lo + ∫ u in lo..s, clampWeight lo hi u

theorem hasDerivAt_smoothClamp (lo hi s : ℝ) :
    HasDerivAt (smoothClamp lo hi) (clampWeight lo hi s) s := by
  have h := intervalIntegral.integral_hasDerivAt_right
    (hf := (continuous_clampWeight lo hi).intervalIntegrable lo s)
    (hmeas := (continuous_clampWeight lo hi).stronglyMeasurableAtFilter _ _)
    (hb := (continuous_clampWeight lo hi).continuousAt)
  have h2 := h.add_const lo
  show HasDerivAt (fun t : ℝ => lo + ∫ u in lo..t, clampWeight lo hi u) (clampWeight lo hi s) s
  simpa [add_comm] using h2

theorem contDiff_smoothClamp (lo hi : ℝ) : ContDiff ℝ 1 (smoothClamp lo hi) := by
  rw [contDiff_one_iff_deriv]
  constructor
  · exact fun s => (hasDerivAt_smoothClamp lo hi s).differentiableAt
  · have hderiv : deriv (smoothClamp lo hi) = clampWeight lo hi := by
      funext s
      exact (hasDerivAt_smoothClamp lo hi s).deriv
    rw [hderiv]
    exact continuous_clampWeight lo hi

theorem smoothClamp_lo (lo hi : ℝ) : smoothClamp lo hi lo = lo := by
  simp [smoothClamp]

/-- The mean value theorem for the smooth cut-off. -/
theorem exists_slope_smoothClamp (lo hi a b : ℝ) (hab : a < b) :
    ∃ c ∈ Set.Ioo a b,
      clampWeight lo hi c = (smoothClamp lo hi b - smoothClamp lo hi a) / (b - a) := by
  have hfc : ContinuousOn (smoothClamp lo hi) (Set.Icc a b) :=
    (contDiff_smoothClamp lo hi).continuous.continuousOn
  have hff' : ∀ x ∈ Set.Ioo a b, HasDerivAt (smoothClamp lo hi) (clampWeight lo hi x) x :=
    fun x _ => hasDerivAt_smoothClamp lo hi x
  exact exists_hasDerivAt_eq_slope (smoothClamp lo hi) (clampWeight lo hi) hab hfc hff'

/-- The smooth cut-off is the identity on `[lo, hi]`. -/
theorem smoothClamp_eq_self (lo hi s : ℝ) (h1 : lo ≤ s) (h2 : s ≤ hi) :
    smoothClamp lo hi s = s := by
  rcases lt_or_eq_of_le h1 with hlt | heq
  · obtain ⟨c, hc, hslope⟩ := exists_slope_smoothClamp lo hi lo s hlt
    have hwc : clampWeight lo hi c = 1 := clampWeight_eq_one lo hi c (le_of_lt hc.1) (hc.2.le.trans h2)
    have hden : s - lo ≠ 0 := sub_ne_zero.mpr hlt.ne'
    rw [hwc, smoothClamp_lo] at hslope
    field_simp at hslope
    linarith
  · rw [heq, smoothClamp_lo]

/-- The smooth cut-off is non-decreasing. -/
theorem smoothClamp_mono (lo hi a b : ℝ) (hab : a ≤ b) :
    smoothClamp lo hi a ≤ smoothClamp lo hi b := by
  rcases lt_or_eq_of_le hab with hlt | heq
  · obtain ⟨c, hc, hslope⟩ := exists_slope_smoothClamp lo hi a b hlt
    have hwc : 0 ≤ clampWeight lo hi c := clampWeight_nonneg lo hi c
    have hden : 0 < b - a := sub_pos.mpr hlt
    have h2 : 0 ≤ (smoothClamp lo hi b - smoothClamp lo hi a) / (b - a) := by
      rw [← hslope]; exact hwc
    have h3 : 0 ≤ smoothClamp lo hi b - smoothClamp lo hi a := by
      have := (le_div_iff₀ hden).mp h2
      simpa using this
    linarith
  · rw [heq]

/-- The smooth cut-off is `1`-Lipschitz. -/
theorem smoothClamp_sub_le (lo hi a b : ℝ) (hab : a ≤ b) :
    smoothClamp lo hi b - smoothClamp lo hi a ≤ b - a := by
  rcases lt_or_eq_of_le hab with hlt | heq
  · obtain ⟨c, hc, hslope⟩ := exists_slope_smoothClamp lo hi a b hlt
    have hwc : clampWeight lo hi c ≤ 1 := clampWeight_le_one lo hi c
    have hden : 0 < b - a := sub_pos.mpr hlt
    have h2 : (smoothClamp lo hi b - smoothClamp lo hi a) / (b - a) ≤ 1 := by
      rw [← hslope]; exact hwc
    have h3 : smoothClamp lo hi b - smoothClamp lo hi a ≤ 1 * (b - a) :=
      (div_le_iff₀ hden).mp h2
    linarith
  · simp [heq]

/-- Where the weight vanishes, the cut-off is constant. -/
theorem smoothClamp_const (lo hi a b : ℝ) (hab : a ≤ b)
    (hw : ∀ c ∈ Set.Ioo a b, clampWeight lo hi c = 0) :
    smoothClamp lo hi a = smoothClamp lo hi b := by
  rcases lt_or_eq_of_le hab with hlt | heq
  · obtain ⟨c, hc, hslope⟩ := exists_slope_smoothClamp lo hi a b hlt
    rw [hw c hc] at hslope
    have hden : b - a ≠ 0 := sub_ne_zero.mpr hlt.ne'
    field_simp at hslope
    linarith
  · rw [heq]

/-- The smooth cut-off takes values in `[lo-1, hi+1]`. -/
theorem smoothClamp_mem (lo hi s : ℝ) (hle : lo ≤ hi) :
    lo - 1 ≤ smoothClamp lo hi s ∧ smoothClamp lo hi s ≤ hi + 1 := by
  constructor
  · by_cases h1 : lo ≤ s
    · have := smoothClamp_mono lo hi lo s h1
      rw [smoothClamp_lo] at this
      linarith
    · by_cases h2 : lo - 1 ≤ s
      · have h3 := smoothClamp_sub_le lo hi s lo (by linarith)
        rw [smoothClamp_lo] at h3
        linarith
      · have hconst : smoothClamp lo hi s = smoothClamp lo hi (lo - 1) :=
          smoothClamp_const lo hi s (lo - 1) (by linarith)
            (fun c hc => clampWeight_eq_zero_left lo hi c (by linarith [hc.2.le]))
        rw [hconst]
        have h3 := smoothClamp_sub_le lo hi (lo - 1) lo (by linarith)
        rw [smoothClamp_lo] at h3
        linarith
  · by_cases h1 : s ≤ hi
    · have := smoothClamp_mono lo hi s hi h1
      have h4 : smoothClamp lo hi hi = hi :=
        smoothClamp_eq_self lo hi hi (by linarith) (by linarith)
      rw [h4] at this
      linarith
    · by_cases h2 : s ≤ hi + 1
      · have h3 := smoothClamp_sub_le lo hi hi s (by linarith)
        have h4 : smoothClamp lo hi hi = hi :=
          smoothClamp_eq_self lo hi hi (by linarith) (by linarith)
        rw [h4] at h3
        linarith
      · have hconst : smoothClamp lo hi s = smoothClamp lo hi (hi + 1) :=
          (smoothClamp_const lo hi (hi + 1) s (by linarith)
            (fun c hc => clampWeight_eq_zero_right lo hi c (by linarith [hc.1.le]))).symm
        rw [hconst]
        have h3 := smoothClamp_sub_le lo hi hi (hi + 1) (by linarith)
        have h4 : smoothClamp lo hi hi = hi :=
          smoothClamp_eq_self lo hi hi (by linarith) (by linarith)
        rw [h4] at h3
        linarith

/-! ## Planar norm helpers -/

/-- The Euclidean norm of a planar vector, in coordinates. -/
theorem norm_phase2_eq (z : Phase2) : ‖z‖ = Real.sqrt ((z 0)^2 + (z 1)^2) := by
  rw [PiLp.norm_eq_of_L2]
  simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

/-- Each coordinate of a planar vector is bounded by its norm. -/
theorem abs_le_norm_phase2 (z : Phase2) (i : Fin 2) : |z i| ≤ ‖z‖ := by
  rw [norm_phase2_eq]
  have h : (z 0)^2 ≤ (z 0)^2 + (z 1)^2 := by nlinarith [sq_nonneg (z 1)]
  have h' : (z 1)^2 ≤ (z 0)^2 + (z 1)^2 := by nlinarith [sq_nonneg (z 0)]
  fin_cases i
  · have hsq : |z 0| ^ 2 ≤ (z 0)^2 + (z 1)^2 := by simpa [sq_abs] using h
    have h1 : Real.sqrt (|z 0| ^ 2) ≤ Real.sqrt ((z 0)^2 + (z 1)^2) := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (abs_nonneg _)] at h1
    exact h1
  · have hsq : |z 1| ^ 2 ≤ (z 0)^2 + (z 1)^2 := by simpa [sq_abs] using h'
    have h1 : Real.sqrt (|z 1| ^ 2) ≤ Real.sqrt ((z 0)^2 + (z 1)^2) := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (abs_nonneg _)] at h1
    exact h1

/-- The Euclidean norm of a planar vector is bounded by twice the largest coordinate. -/
theorem norm_phase2_le (z : Phase2) : ‖z‖ ≤ 2 * max |z 0| |z 1| := by
  rw [norm_phase2_eq, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 : (z 0)^2 ≤ max |z 0| |z 1| ^ 2 := by
    have h := le_max_left (|z 0|) (|z 1|)
    have hsq : |z 0| * |z 0| ≤ (max |z 0| |z 1|) * (max |z 0| |z 1|) :=
      mul_self_le_mul_self (abs_nonneg _) h
    simpa [sq_abs, pow_two] using hsq
  have h2 : (z 1)^2 ≤ max |z 0| |z 1| ^ 2 := by
    have h := le_max_right (|z 0|) (|z 1|)
    have hsq : |z 1| * |z 1| ≤ (max |z 0| |z 1|) * (max |z 0| |z 1|) :=
      mul_self_le_mul_self (abs_nonneg _) h
    simpa [sq_abs, pow_two] using hsq
  have h3 : (z 0)^2 + (z 1)^2 ≤ 2 * (max |z 0| |z 1|) ^ 2 := by nlinarith
  have h4 : 2 * (max |z 0| |z 1|) ^ 2 ≤ (2 * max |z 0| |z 1|) ^ 2 := by
    have := sq_nonneg (max |z 0| |z 1|)
    nlinarith
  nlinarith

/-! ## The planar mass-action field of the Lotka network -/

/-- **The Lotka mass-action field on the planar phase space.**

The field is the transport of `CRNT.Examples.Lotka.N.massActionVectorField`; it is written in
coordinates because the planar phase space carries the Euclidean norm. -/
noncomputable def lotkaPlanarField (κ : Examples.Lotka.N.RateConstants) : Phase2 → Phase2 :=
  fun z => WithLp.toLp 2 (fun i => match i with
    | 0 => κ.k Examples.Lotka.grow * (z 0)
        - κ.k Examples.Lotka.prey * ((z 0) * (z 1))
    | 1 => κ.k Examples.Lotka.prey * ((z 0) * (z 1))
        - κ.k Examples.Lotka.decay * (z 1))

/-- The planar field is `C¹`, as the planar kernel requires. -/
theorem contDiff_lotkaPlanarField (κ : Examples.Lotka.N.RateConstants) :
    ContDiff ℝ 1 (lotkaPlanarField κ) := by
  rw [contDiff_piLp]
  intro i
  fin_cases i
  · simp only [lotkaPlanarField, PiLp.toLp_apply]
    fun_prop
  · simp only [lotkaPlanarField, PiLp.toLp_apply]
    fun_prop

/-- **The planar field is the transported mass-action field.** -/
theorem lotkaPlanarField_eq (κ : Examples.Lotka.N.RateConstants)
    (x : Concentration Examples.Lotka.Species) :
    lotkaPlanarField κ (WithLp.toLp 2 x)
      = WithLp.toLp 2 (Examples.Lotka.N.massActionVectorField κ x) := by
  rw [WithLp.ext_iff]
  funext i
  fin_cases i
  · simp only [lotkaPlanarField, PiLp.toLp_apply]
    rw [← Examples.Lotka.field_A]
    exact congrArg (fun v => Examples.Lotka.N.massActionVectorField κ x v) (Fin.ext rfl)
  · simp only [lotkaPlanarField, PiLp.toLp_apply]
    rw [← Examples.Lotka.field_B]
    exact congrArg (fun v => Examples.Lotka.N.massActionVectorField κ x v) (Fin.ext rfl)

/-! ## The cut-off field -/

/-- The coordinatewise smooth cut-off, as a concentration vector. -/
noncomputable def lotkaClamp2 (lo hi : ℝ) (z : Phase2) : Concentration (Fin 2) :=
  fun i => smoothClamp lo hi (z i)

/-- The coordinatewise smooth cut-off, as a planar vector. -/
noncomputable def lotkaClamp2Phase (lo hi : ℝ) (z : Phase2) : Phase2 :=
  WithLp.toLp 2 (fun i => smoothClamp lo hi (z i))

/-- **The cut-off planar Lotka field.** Outside the cut-off box the field is the mass-action field
evaluated at the cut-off, which makes it bounded and globally Lipschitz, while inside the box it
*is* the mass-action field. -/
noncomputable def lotkaClampedField (κ : Examples.Lotka.N.RateConstants) (lo hi : ℝ) :
    Phase2 → Phase2 :=
  fun z => lotkaPlanarField κ (lotkaClamp2Phase lo hi z)

/-- The cut-off field is `C¹`. -/
theorem contDiff_phase2_apply (i : Fin 2) : ContDiff ℝ 1 (fun z : Phase2 => z.ofLp i) := by
  rw [← contDiffOn_univ]
  intro x _
  exact contDiffWithinAt_piLp_apply (p := 2) (ι := Fin 2) (E := fun _ : Fin 2 => ℝ)

theorem contDiff_lotkaClampedField (κ : Examples.Lotka.N.RateConstants) (lo hi : ℝ) :
    ContDiff ℝ 1 (lotkaClampedField κ lo hi) := by
  rw [contDiff_piLp]
  intro i
  fin_cases i
  · simp only [lotkaClampedField, lotkaPlanarField, lotkaClamp2Phase, PiLp.toLp_apply]
    have h0 : ContDiff ℝ 1 (fun x : Phase2 => smoothClamp lo hi (x.ofLp 0)) :=
      (contDiff_smoothClamp lo hi).comp (contDiff_phase2_apply 0)
    have h1 : ContDiff ℝ 1 (fun x : Phase2 => smoothClamp lo hi (x.ofLp 1)) :=
      (contDiff_smoothClamp lo hi).comp (contDiff_phase2_apply 1)
    fun_prop
  · simp only [lotkaClampedField, lotkaPlanarField, lotkaClamp2Phase, PiLp.toLp_apply]
    have h0 : ContDiff ℝ 1 (fun x : Phase2 => smoothClamp lo hi (x.ofLp 0)) :=
      (contDiff_smoothClamp lo hi).comp (contDiff_phase2_apply 0)
    have h1 : ContDiff ℝ 1 (fun x : Phase2 => smoothClamp lo hi (x.ofLp 1)) :=
      (contDiff_smoothClamp lo hi).comp (contDiff_phase2_apply 1)
    fun_prop

/-- The absolute difference of two cut-off values is bounded by the absolute difference of the
inputs. -/
theorem abs_smoothClamp_sub_le (lo hi a b : ℝ) :
    |smoothClamp lo hi a - smoothClamp lo hi b| ≤ |a - b| := by
  rcases le_total a b with hab | hba
  · have hmono := smoothClamp_mono lo hi a b hab
    have h1 := smoothClamp_sub_le lo hi a b hab
    have habs : |smoothClamp lo hi a - smoothClamp lo hi b|
        = -(smoothClamp lo hi a - smoothClamp lo hi b) := abs_of_nonpos (by linarith)
    have haba : |a - b| = -(a - b) := abs_of_nonpos (sub_nonpos.mpr hab)
    rw [habs, haba]
    linarith
  · have hmono := smoothClamp_mono lo hi b a hba
    have h1 := smoothClamp_sub_le lo hi b a hba
    have habs : |smoothClamp lo hi a - smoothClamp lo hi b|
        = smoothClamp lo hi a - smoothClamp lo hi b := abs_of_nonneg (by linarith)
    have haba : |a - b| = a - b := abs_of_nonneg (sub_nonneg.mpr hba)
    rw [habs, haba]
    linarith

/-- **The cut-off is `1`-Lipschitz on the plane.** -/
theorem dist_lotkaClamp2Phase_le (lo hi : ℝ) (z w : Phase2) :
    dist (lotkaClamp2Phase lo hi z) (lotkaClamp2Phase lo hi w) ≤ dist z w := by
  simp only [dist_eq_norm]
  have hn1 := PiLp.norm_eq_of_L2 (ι := Fin 2) (β := fun _ : Fin 2 => ℝ)
    (lotkaClamp2Phase lo hi z - lotkaClamp2Phase lo hi w)
  have hn2 := PiLp.norm_eq_of_L2 (ι := Fin 2) (β := fun _ : Fin 2 => ℝ) (z - w)
  rw [hn1, hn2]
  have hsum : (∑ i, ‖(lotkaClamp2Phase lo hi z - lotkaClamp2Phase lo hi w).ofLp i‖ ^ 2)
      ≤ ∑ i, ‖(z - w).ofLp i‖ ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    have hcomp : (lotkaClamp2Phase lo hi z - lotkaClamp2Phase lo hi w).ofLp
        = fun j => smoothClamp lo hi (z j) - smoothClamp lo hi (w j) := by
      ext j
      rfl
    rw [hcomp]
    have hab := abs_smoothClamp_sub_le lo hi (z i) (w i)
    have hsq' : |smoothClamp lo hi (z i) - smoothClamp lo hi (w i)|
        * |smoothClamp lo hi (z i) - smoothClamp lo hi (w i)|
        ≤ |z i - w i| * |z i - w i| := mul_self_le_mul_self (abs_nonneg _) hab
    have hsq : (smoothClamp lo hi (z i) - smoothClamp lo hi (w i)) ^ 2 ≤ (z i - w i) ^ 2 := by
      simpa [sq_abs, pow_two] using hsq'
    simpa [Real.norm_eq_abs, sq_abs, pow_two] using hsq
  have := Real.sqrt_le_sqrt hsum
  simpa using this

/-- The cut-off takes values in the box `[lo-1, hi+1]`. -/
theorem lotkaClamp2Phase_mem (lo hi : ℝ) (hle : lo ≤ hi) (z : Phase2) (i : Fin 2) :
    lo - 1 ≤ (lotkaClamp2Phase lo hi z) i ∧ (lotkaClamp2Phase lo hi z) i ≤ hi + 1 := by
  have h := smoothClamp_mem lo hi (z i) hle
  simpa [lotkaClamp2Phase, PiLp.toLp_apply] using h

/-! ## A box in the plane -/

/-- The closed box `[lo, hi]` in the planar phase space. -/
def phase2Box (lo hi : ℝ) : Set Phase2 := {z | ∀ i, lo ≤ z i ∧ z i ≤ hi}

/-- The box is the image of the coordinate box. -/
theorem mem_phase2Box_iff (lo hi : ℝ) (z : Phase2) :
    z ∈ phase2Box lo hi ↔ ∀ i, lo ≤ z i ∧ z i ≤ hi := Iff.rfl

/-- The box is convex. -/
theorem convex_phase2Box (lo hi : ℝ) : Convex ℝ (phase2Box lo hi) := by
  intro x hx y hy a b ha hb hab
  rw [mem_phase2Box_iff] at hx hy ⊢
  intro i
  have hsmul : (a • x + b • y) i = a * x i + b * y i := by
    rw [PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply]
    rfl
  rw [hsmul]
  constructor
  · have h1 : a * lo + b * lo ≤ a * x i + b * y i :=
      add_le_add (mul_le_mul_of_nonneg_left (hx i).1 ha) (mul_le_mul_of_nonneg_left (hy i).1 hb)
    have h2 : lo = a * lo + b * lo := by rw [← add_mul, hab, one_mul]
    rw [h2]
    exact h1
  · have h1 : a * x i + b * y i ≤ a * hi + b * hi :=
      add_le_add (mul_le_mul_of_nonneg_left (hx i).2 ha) (mul_le_mul_of_nonneg_left (hy i).2 hb)
    have h2 : hi = a * hi + b * hi := by rw [← add_mul, hab, one_mul]
    rw [h2]
    exact h1

/-- The box is compact: it is the continuous image of a compact coordinate box. -/
theorem isCompact_phase2Box (lo hi : ℝ) : IsCompact (phase2Box lo hi) := by
  have hcont : Continuous (fun v : Fin 2 → ℝ => WithLp.toLp 2 v) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.continuous
  have himg : WithLp.toLp 2 '' Set.Icc (fun _ : Fin 2 => lo) (fun _ : Fin 2 => hi)
      = phase2Box lo hi := by
    ext z
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [mem_phase2Box_iff]
      intro i
      have hvi := Set.mem_Icc.mp hv
      simpa [PiLp.toLp_apply] using And.intro (hvi.1 i) (hvi.2 i)
    · intro hz
      refine ⟨fun i => z i, ?_, ?_⟩
      · refine Set.mem_Icc.mpr ⟨?_, ?_⟩
        · rw [Pi.le_def]
          exact fun i => (hz i).1
        · rw [Pi.le_def]
          exact fun i => (hz i).2
      · exact WithLp.toLp_ofLp (p := 2) z
  rw [← himg]
  exact (isCompact_Icc (a := (fun _ : Fin 2 => lo)) (b := fun _ => hi)).image hcont

/-! ## The flow of the cut-off field -/

/-- The mass-action field of the Lotka network is Lipschitz on every compact box. -/
theorem exists_lipschitzOnWith_lotkaPlanarField (κ : Examples.Lotka.N.RateConstants)
    (lo hi : ℝ) :
    ∃ K : ℝ≥0, LipschitzOnWith K (lotkaPlanarField κ) (phase2Box lo hi) :=
  (contDiff_lotkaPlanarField κ).contDiffOn (s := phase2Box lo hi)
    |>.exists_lipschitzOnWith (by simp) (convex_phase2Box lo hi) (isCompact_phase2Box lo hi)

/-- **The cut-off field is globally Lipschitz.** -/
theorem LipschitzWith_lotkaClampedField (κ : Examples.Lotka.N.RateConstants) (lo hi : ℝ)
    (hle : lo ≤ hi) {K : ℝ≥0}
    (hK : LipschitzOnWith K (lotkaPlanarField κ) (phase2Box (lo - 1) (hi + 1))) :
    LipschitzWith K (lotkaClampedField κ lo hi) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  have hxmem : lotkaClamp2Phase lo hi x ∈ phase2Box (lo - 1) (hi + 1) := by
    rw [mem_phase2Box_iff]
    intro i
    have h := lotkaClamp2Phase_mem lo hi hle x i
    exact ⟨h.1, h.2⟩
  have hymem : lotkaClamp2Phase lo hi y ∈ phase2Box (lo - 1) (hi + 1) := by
    rw [mem_phase2Box_iff]
    intro i
    have h := lotkaClamp2Phase_mem lo hi hle y i
    exact ⟨h.1, h.2⟩
  have h1 : dist (lotkaPlanarField κ (lotkaClamp2Phase lo hi x))
      (lotkaPlanarField κ (lotkaClamp2Phase lo hi y))
      ≤ K * dist (lotkaClamp2Phase lo hi x) (lotkaClamp2Phase lo hi y) :=
    hK.dist_le_mul _ hxmem _ hymem
  have h2 : dist (lotkaClamp2Phase lo hi x) (lotkaClamp2Phase lo hi y) ≤ dist x y :=
    dist_lotkaClamp2Phase_le lo hi x y
  have h3 : K * dist (lotkaClamp2Phase lo hi x) (lotkaClamp2Phase lo hi y)
      ≤ K * dist x y := by
    exact mul_le_mul_of_nonneg_left h2 K.coe_nonneg
  simpa [lotkaClampedField] using le_trans h1 h3

/-- **The cut-off field is bounded.** -/
theorem exists_bound_lotkaClampedField (κ : Examples.Lotka.N.RateConstants) (lo hi : ℝ)
    (hle : lo ≤ hi) :
    ∃ M : ℝ≥0, ∀ z, ‖lotkaClampedField κ lo hi z‖ ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_phase2Box (lo - 1) (hi + 1)).exists_bound_of_continuousOn
    (f := fun x : Phase2 => lotkaPlanarField κ x)
    (contDiff_lotkaPlanarField κ).continuous.continuousOn
  refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
  intro z
  have hmem : lotkaClamp2Phase lo hi z ∈ phase2Box (lo - 1) (hi + 1) := by
    rw [mem_phase2Box_iff]
    intro i
    have h := lotkaClamp2Phase_mem lo hi hle z i
    exact ⟨h.1, h.2⟩
  have h := hC (lotkaClamp2Phase lo hi z) hmem
  have h' : ‖lotkaClampedField κ lo hi z‖ ≤ max C 0 := by
    rw [lotkaClampedField]
    exact le_trans h (le_max_left _ _)
  exact h'

/-- **The flow of the cut-off field.** The cut-off field is `C¹`, bounded and globally Lipschitz,
so it generates a forward semiflow whose orbits are its solutions. -/
theorem exists_flow_lotkaClampedField (κ : Examples.Lotka.N.RateConstants) (lo hi : ℝ)
    (hle : lo ≤ hi) :
    ∃ (ϕ : Flow ℝ≥0 Phase2) (γ : Phase2 → ℝ → Phase2),
      (∀ x, γ x 0 = x) ∧
      (∀ x t, HasDerivAt (γ x) (lotkaClampedField κ lo hi (γ x t)) t) ∧
      (∀ x (t : ℝ≥0), ϕ t x = γ x (t : ℝ)) := by
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_lotkaPlanarField κ (lo - 1) (hi + 1)
  obtain ⟨M, hM⟩ := exists_bound_lotkaClampedField κ lo hi hle
  exact ODE.exists_flow (LipschitzWith_lotkaClampedField κ lo hi hle hK) hM

/-! ## The trapping region of the Lotka network -/

/-- **The level set of the first integral of the Lotka network.**

It is the natural trapping region: the first integral is constant along solutions, so the level
set is positively invariant; and for `c` above the value at the positive equilibrium it contains
no equilibrium. -/
def lotkaLevelSet (κ : Examples.Lotka.N.RateConstants) (c : ℝ) :
    Set (Concentration Examples.Lotka.Species) :=
  {x | x.Positive ∧ Examples.Lotka.firstIntegral κ x = c}

/-- **The level set is compact.** -/
theorem lotkaLevelSet_compact (κ : Examples.Lotka.N.RateConstants)
    (h0 : 0 < κ.k Examples.Lotka.grow) (h1 : 0 < κ.k Examples.Lotka.prey)
    (h2 : 0 < κ.k Examples.Lotka.decay) (c : ℝ) : IsCompact (lotkaLevelSet κ c) := by
  have hsub := Examples.Lotka.levelSetCompact κ h0 h1 h2 c
  have hcont : ContinuousOn (Examples.Lotka.firstIntegral κ)
      {x : Concentration Examples.Lotka.Species |
        x.Positive ∧ Examples.Lotka.firstIntegral κ x ≤ c} :=
    (Examples.Lotka.continuousOn_firstIntegral κ).mono fun x hx => hx.1
  have hclosed : IsClosed {x : Concentration Examples.Lotka.Species |
      x.Positive ∧ Examples.Lotka.firstIntegral κ x = c} := by
    have h := hcont.preimage_isClosed_of_isClosed hsub.isClosed (isClosed_singleton (x := c))
    convert h using 1
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun hx => ⟨⟨hx.1, hx.2.le⟩, hx.2⟩, fun hx => ⟨hx.1.1, hx.2⟩⟩
  exact IsCompact.of_isClosed_subset hsub hclosed fun x hx => ⟨hx.1, hx.2.le⟩

/-- **The only equilibrium of the Lotka field in the positive quadrant is the positive
equilibrium.** -/
theorem eq_equilibrium_of_field_eq_zero (κ : Examples.Lotka.N.RateConstants)
    (h1 : 0 < κ.k Examples.Lotka.prey)
    {x : Concentration Examples.Lotka.Species} (hx : x.Positive)
    (hzero : Examples.Lotka.N.massActionVectorField κ x = 0) :
    x = Examples.Lotka.equilibrium κ := by
  have hA := congrFun hzero Examples.Lotka.A
  have hB := congrFun hzero Examples.Lotka.B
  rw [Examples.Lotka.field_A] at hA
  rw [Examples.Lotka.field_B] at hB
  have hxA : 0 < x Examples.Lotka.A := hx Examples.Lotka.A
  have hxB : 0 < x Examples.Lotka.B := hx Examples.Lotka.B
  have hA0 : κ.k Examples.Lotka.grow * x Examples.Lotka.A
      - κ.k Examples.Lotka.prey * (x Examples.Lotka.A * x Examples.Lotka.B) = 0 := by
    simpa only [Pi.zero_apply] using hA
  have hB0 : κ.k Examples.Lotka.prey * (x Examples.Lotka.A * x Examples.Lotka.B)
      - κ.k Examples.Lotka.decay * x Examples.Lotka.B = 0 := by
    simpa only [Pi.zero_apply] using hB
  have hAy : κ.k Examples.Lotka.grow = κ.k Examples.Lotka.prey * x Examples.Lotka.B := by
    have h1 : κ.k Examples.Lotka.grow * x Examples.Lotka.A
        = κ.k Examples.Lotka.prey * (x Examples.Lotka.A * x Examples.Lotka.B) := by linarith
    have h2 : κ.k Examples.Lotka.prey * (x Examples.Lotka.A * x Examples.Lotka.B)
        = (κ.k Examples.Lotka.prey * x Examples.Lotka.B) * x Examples.Lotka.A := by ring
    rw [h2] at h1
    exact (mul_right_cancel₀ (ne_of_gt hxA) h1)
  have hBx : κ.k Examples.Lotka.prey * x Examples.Lotka.A = κ.k Examples.Lotka.decay := by
    have h1 : κ.k Examples.Lotka.prey * (x Examples.Lotka.A * x Examples.Lotka.B)
        = κ.k Examples.Lotka.decay * x Examples.Lotka.B := by linarith
    have h2 : κ.k Examples.Lotka.prey * (x Examples.Lotka.A * x Examples.Lotka.B)
        = (κ.k Examples.Lotka.prey * x Examples.Lotka.A) * x Examples.Lotka.B := by ring
    rw [h2] at h1
    exact (mul_right_cancel₀ (ne_of_gt hxB) h1)
  have hxA' : x Examples.Lotka.A = κ.k Examples.Lotka.decay / κ.k Examples.Lotka.prey := by
    rw [eq_div_iff (ne_of_gt h1)]
    simpa [mul_comm] using hBx
  have hxB' : x Examples.Lotka.B = κ.k Examples.Lotka.grow / κ.k Examples.Lotka.prey := by
    rw [eq_div_iff (ne_of_gt h1)]
    simpa [mul_comm] using hAy.symm
  funext s
  fin_cases s
  · show x Examples.Lotka.A = κ.k Examples.Lotka.decay / κ.k Examples.Lotka.prey
    exact hxA'
  · show x Examples.Lotka.B = κ.k Examples.Lotka.grow / κ.k Examples.Lotka.prey
    exact hxB'

/-- **The level set contains no equilibrium.** -/
theorem lotkaLevelSet_equilibriumFree (κ : Examples.Lotka.N.RateConstants)
    (h1 : 0 < κ.k Examples.Lotka.prey) (c : ℝ)
    (hc : Examples.Lotka.firstIntegral κ (Examples.Lotka.equilibrium κ) < c) :
    ∀ x ∈ lotkaLevelSet κ c, Examples.Lotka.N.massActionVectorField κ x ≠ 0 := by
  intro x hx hzero
  have hpos : x.Positive := hx.1
  have hV : Examples.Lotka.firstIntegral κ x = c := hx.2
  have hne : x ≠ Examples.Lotka.equilibrium κ := by
    intro heq
    have hEq : Examples.Lotka.firstIntegral κ (Examples.Lotka.equilibrium κ) = c := by
      rw [← heq, hV]
    linarith
  exact absurd (eq_equilibrium_of_field_eq_zero κ h1 hpos hzero) hne

/-- **A positive point of the Lotka network which is not the equilibrium.** -/
noncomputable def lotkaSeed (κ : Examples.Lotka.N.RateConstants) :
    Concentration Examples.Lotka.Species :=
  ![2 * (κ.k Examples.Lotka.decay / κ.k Examples.Lotka.prey),
    κ.k Examples.Lotka.grow / κ.k Examples.Lotka.prey]

theorem lotkaSeed_pos (κ : Examples.Lotka.N.RateConstants) (h1 : 0 < κ.k Examples.Lotka.prey)
    (h2 : 0 < κ.k Examples.Lotka.decay) (h0 : 0 < κ.k Examples.Lotka.grow) :
    (lotkaSeed κ).Positive := by
  intro s
  fin_cases s
  · show 0 < 2 * (κ.k Examples.Lotka.decay / κ.k Examples.Lotka.prey)
    positivity
  · show 0 < κ.k Examples.Lotka.grow / κ.k Examples.Lotka.prey
    positivity

theorem lotkaSeed_ne_equilibrium (κ : Examples.Lotka.N.RateConstants)
    (h1 : 0 < κ.k Examples.Lotka.prey) (h2 : 0 < κ.k Examples.Lotka.decay) :
    lotkaSeed κ ≠ Examples.Lotka.equilibrium κ := by
  intro h
  have := congrFun h Examples.Lotka.A
  simp only [lotkaSeed, Examples.Lotka.equilibrium, Matrix.cons_val_zero] at this
  change 2 * (κ.k Examples.Lotka.decay / κ.k Examples.Lotka.prey)
      = κ.k Examples.Lotka.decay / κ.k Examples.Lotka.prey at this
  have hne : κ.k Examples.Lotka.decay / κ.k Examples.Lotka.prey ≠ 0 := by positivity
  have hd : 0 < κ.k Examples.Lotka.decay / κ.k Examples.Lotka.prey := div_pos h2 h1
  linarith

/-- The cut-off is the identity on a box which contains the trajectory. -/
theorem lotkaClamp2_eq_self (lo hi : ℝ) (z : Phase2)
    (hz : ∀ i, lo ≤ z i ∧ z i ≤ hi) : lotkaClamp2 lo hi z = fun i => z i := by
  funext i
  simp [lotkaClamp2, smoothClamp_eq_self lo hi (z i) (hz i).1 (hz i).2]

/-- The cut-off field agrees with the mass-action field on a box. -/
theorem lotkaClampedField_apply (κ : Examples.Lotka.N.RateConstants) (lo hi : ℝ) (z : Phase2)
    (s : Fin 2) :
    lotkaClampedField κ lo hi z s
      = Examples.Lotka.N.massActionVectorField κ (lotkaClamp2 lo hi z) s := by
  rw [lotkaClampedField, lotkaClamp2Phase]
  rw [lotkaPlanarField_eq]
  rfl


/-- **The derivative of a coordinate of a planar trajectory.** -/
theorem hasDerivAt_phase2_apply (g : Phase2 → Phase2) (tr : ℝ → Phase2)
    (htr : ∀ t, HasDerivAt tr (g (tr t)) t) (v : ℝ) (s : Fin 2) :
    HasDerivAt (fun τ => (tr τ) s) (g (tr v) s) v := by
  have hclm : HasFDerivAt (fun z : Phase2 => z.ofLp s)
      (PiLp.proj 2 (fun _ : Fin 2 => ℝ) s) (tr v) :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 => ℝ) (tr v) s
  have hcomp := hclm.comp_hasDerivAt v (htr v)
  show HasDerivAt (fun τ => (tr τ).ofLp s) ((g (tr v)).ofLp s) v
  exact hcomp

/-! ## The trapping data of the Lotka network -/

/-- **The trapping data of the Lotka network.**

The compact trapping region is the image of the level set `K_c` of the first integral of the
network; the flow is the flow of the cut-off mass-action field, which agrees with the
mass-action field itself on the box containing `K_c`.

The hypotheses are

* `p₀` a positive concentration and `c` its first-integral value, so that `p₀ ∈ K_c`;
* `0 < lo ≤ hi` and the containment `K_c ⊂ (lo, hi)²`, which is what makes the cut-off
  invisible on the trajectory;
* the rate constants positive, so that the first integral is coercive and the level set is
  compact. -/
theorem exists_lotka_flowTrappingData (κ : Examples.Lotka.N.RateConstants)
    (h0 : 0 < κ.k Examples.Lotka.grow) (h1 : 0 < κ.k Examples.Lotka.prey)
    (h2 : 0 < κ.k Examples.Lotka.decay)
    (p₀ : Concentration Examples.Lotka.Species) (hp₀ : p₀.Positive)
    (c : ℝ) (hc : Examples.Lotka.firstIntegral κ p₀ = c)
    (hc' : Examples.Lotka.firstIntegral κ (Examples.Lotka.equilibrium κ) < c)
    (lo hi : ℝ) (hlo : 0 < lo) (hle : lo ≤ hi)
    (hK : ∀ x ∈ lotkaLevelSet κ c, ∀ s, lo < x s ∧ x s < hi) :
    ∃ D : Planar.FlowTrappingData (lotkaClampedField κ lo hi),
      D.region = WithLp.toLp 2 '' lotkaLevelSet κ c := by
  obtain ⟨ϕ, γ, hγ0, hγd, hϕγ⟩ := exists_flow_lotkaClampedField κ lo hi hle
  -- the trajectory of the seed
  set tr : ℝ → Phase2 := γ (WithLp.toLp 2 p₀) with htrdef
  have htr : ∀ t, HasDerivAt tr (lotkaClampedField κ lo hi (tr t)) t := by
    intro t
    exact hγd (WithLp.toLp 2 p₀) t
  have htrc : Continuous tr := continuous_iff_continuousAt.2 fun t => (htr t).continuousAt
  -- the concentration version of the trajectory
  set ζ : ℝ → Concentration Examples.Lotka.Species := fun t => fun s => (tr t) s with hζdef
  have hζc : Continuous ζ := by fun_prop
  -- the open box which contains the trajectory
  set U : Set (Concentration Examples.Lotka.Species) :=
    {x | ∀ s, lo < x s ∧ x s < hi} with hUdef
  have hUopen : IsOpen U := by
    have hU : U = ⋂ (s : Examples.Lotka.Species),
        ({x : Concentration Examples.Lotka.Species | lo < x s} ∩ {x | x s < hi}) := by
      ext x
      simp only [hUdef, Set.mem_iInter, Set.mem_inter_iff]
      exact ⟨fun h s => ⟨(h s).1, (h s).2⟩, fun h s => ⟨(h s).1, (h s).2⟩⟩
    rw [hU]
    exact isOpen_iInter_of_finite fun s : Examples.Lotka.Species =>
      (isOpen_lt continuous_const (continuous_apply s)).inter
        (isOpen_lt (continuous_apply s) continuous_const)
  have hUpos : ∀ x ∈ U, x.Positive := fun x hx s =>
    lt_of_le_of_lt hlo.le (hx s).1
  have hLU : lotkaLevelSet κ c ⊆ U := by
    intro x hx s
    exact hK x hx s
  -- the level set is closed
  have hLclosed : IsClosed (lotkaLevelSet κ c) := by
    have hsub := Examples.Lotka.levelSetCompact κ h0 h1 h2 c
    have hcont : ContinuousOn (Examples.Lotka.firstIntegral κ)
        {x : Concentration Examples.Lotka.Species |
          x.Positive ∧ Examples.Lotka.firstIntegral κ x ≤ c} :=
      (Examples.Lotka.continuousOn_firstIntegral κ).mono fun x hx => hx.1
    have hclosed : IsClosed {x : Concentration Examples.Lotka.Species |
        x.Positive ∧ Examples.Lotka.firstIntegral κ x = c} := by
      have h := hcont.preimage_isClosed_of_isClosed hsub.isClosed (isClosed_singleton (x := c))
      convert h using 1
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun hx => ⟨⟨hx.1, hx.2.le⟩, hx.2⟩, fun hx => ⟨hx.1.1, hx.2⟩⟩
    simpa [lotkaLevelSet] using hclosed
  -- the times at which the trajectory is on the level set form a clopen set
  set Aset : Set ℝ := {t | ζ t ∈ lotkaLevelSet κ c} with hAsetdef
  have hclosed : IsClosed Aset := hLclosed.preimage hζc
  have hopen : IsOpen Aset := by
    rw [Metric.isOpen_iff]
    intro t ht
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hUopen.preimage hζc) t (hLU ht)
    refine ⟨ε, hε, fun u hu => ?_⟩
    have hderiv : ∀ v ∈ Metric.ball t ε,
        HasDerivAt (fun τ => Examples.Lotka.firstIntegral κ (ζ τ)) 0 v := by
      intro v hv
      have hvU : ζ v ∈ U := hball hv
      refine Examples.Lotka.hasDerivAt_firstIntegral_comp κ (hUpos _ hvU) fun s => ?_
      have hclamp : lotkaClamp2 lo hi (tr v) = ζ v := by
        refine lotkaClamp2_eq_self lo hi (tr v) ?_
        intro i
        have hi' := (hUpos _ hvU) i
        have hib := hvU i
        exact ⟨le_of_lt hib.1, le_of_lt hib.2⟩
      have hproj : HasDerivAt (fun τ => (tr τ) s)
          (Examples.Lotka.N.massActionVectorField κ (ζ v) s) v := by
        have hcomp := hasDerivAt_phase2_apply (lotkaClampedField κ lo hi) tr htr v s
        rw [lotkaClampedField_apply, hclamp] at hcomp
        simpa using hcomp
      exact hproj
    have hconst := (Metric.isOpen_ball).is_const_of_deriv_eq_zero (convex_ball t ε).isPreconnected
      (fun v hv => (hderiv v hv).differentiableAt.differentiableWithinAt)
      (fun v hv => (hderiv v hv).deriv) hu (Metric.mem_ball_self hε)
    exact ⟨hUpos _ (hball hu), hconst.trans ht.2⟩
  have hAnempty : Aset.Nonempty := by
    refine ⟨0, ?_⟩
    have h0 : ζ 0 = p₀ := by
      funext s
      change (tr 0).ofLp s = p₀ s
      simp only [tr, hγ0, PiLp.toLp_apply]
    show Concentration.Positive (ζ 0) ∧ Examples.Lotka.firstIntegral κ (ζ 0) = c
    rw [h0]
    exact ⟨hp₀, hc⟩
  have huniv : Aset = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ hAnempty
  have hmem : ∀ t, ζ t ∈ lotkaLevelSet κ c := by
    intro t
    have hmem' : t ∈ Set.univ := Set.mem_univ t
    rw [← huniv] at hmem'
    exact hmem'
  -- the trapping data
  refine ⟨
    { flow := ϕ
      trajectory := γ
      trajectory_zero := ?_
      trajectory_solution := ?_
      flow_eq_trajectory := ?_
      seed := WithLp.toLp 2 p₀
      region := WithLp.toLp 2 '' lotkaLevelSet κ c
      compact := ?_
      trapped := ?_
      equilibriumFree := ?_ }, rfl⟩
  · exact hγ0
  · exact hγd
  · intro x t
    exact hϕγ x t
  · exact (lotkaLevelSet_compact κ h0 h1 h2 c).image
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.continuous
  · intro t
    rw [hϕγ (WithLp.toLp 2 p₀) t]
    exact ⟨ζ (t : ℝ), hmem (t : ℝ), rfl⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hyclamp : lotkaClamp2 lo hi (WithLp.toLp 2 y) = y := by
      refine lotkaClamp2_eq_self lo hi (WithLp.toLp 2 y) ?_
      intro i
      have hib := hK y hy i
      exact ⟨le_of_lt hib.1, le_of_lt hib.2⟩
    have hcomp : ∀ s, (lotkaClampedField κ lo hi (WithLp.toLp 2 y)) s
        = Examples.Lotka.N.massActionVectorField κ y s := by
      intro s
      rw [lotkaClampedField_apply, hyclamp]
    intro hzero
    have hzero' : ∀ s, Examples.Lotka.N.massActionVectorField κ y s = 0 := by
      intro s
      have hz := congrArg (fun z : Phase2 => z s) hzero
      rw [hcomp s] at hz
      simpa using hz
    have hfield : Examples.Lotka.N.massActionVectorField κ y = 0 := by
      funext s
      exact hzero' s
    exact absurd hfield (lotkaLevelSet_equilibriumFree κ h1 c hc' y hy)

/-- **The trapping data of the Lotka network.** -/
noncomputable def lotka_flowTrappingData (κ : Examples.Lotka.N.RateConstants)
    (h0 : 0 < κ.k Examples.Lotka.grow) (h1 : 0 < κ.k Examples.Lotka.prey)
    (h2 : 0 < κ.k Examples.Lotka.decay)
    (p₀ : Concentration Examples.Lotka.Species) (hp₀ : p₀.Positive)
    (c : ℝ) (hc : Examples.Lotka.firstIntegral κ p₀ = c)
    (hc' : Examples.Lotka.firstIntegral κ (Examples.Lotka.equilibrium κ) < c)
    (lo hi : ℝ) (hlo : 0 < lo) (hle : lo ≤ hi)
    (hK : ∀ x ∈ lotkaLevelSet κ c, ∀ s, lo < x s ∧ x s < hi) :
    Planar.FlowTrappingData (lotkaClampedField κ lo hi) :=
  Classical.choice
    (Exists.elim (exists_lotka_flowTrappingData κ h0 h1 h2 p₀ hp₀ c hc hc' lo hi hlo hle hK)
      (fun D _ => ⟨D⟩))


/-- **The omega-limit set of the trapped Lotka orbit contains no equilibrium.**

This is the step which turns the trapping region into an oscillation statement: the planar
Poincare--Bendixson theorem applies to an omega-limit set which contains no equilibrium, and the
periodic orbit it produces is therefore nonconstant. -/
theorem lotka_omegaSet_equilibriumFree {κ : Examples.Lotka.N.RateConstants} {lo hi : ℝ}
    (D : Planar.FlowTrappingData (lotkaClampedField κ lo hi))
    {z : Phase2} (hz : z ∈ D.omegaSet) : lotkaClampedField κ lo hi z ≠ 0 :=
  D.omegaSet_equilibriumFree z hz

/-! ## The omega-limit analysis and the conclusion -/

/-- **The Lotka network has a positive periodic orbit, provided the universal planar kernel is
available.**

This is the end-to-end statement of the network-specific part of the Poincaré--Bendixson route
for a concrete planar mass-action network: the trapping region is certified (compact, positively
invariant, equilibrium-free), the omega-limit set of the trapped orbit is computed to lie in the
positive quadrant and inside the cut-off box, and the planar kernel turns the omega-limit set into
a periodic orbit of the mass-action field.

The only hypothesis which is *not* discharged here is the universal kernel bundle
`CRNT.Planar.PoincareBendixsonKernelBundle`, i.e. the `C¹` dependence of the flow on the initial
point and the Jordan separation theorem. -/
theorem lotka_hasPositivePeriodicOrbit_of_trappingRegion
    (K : Planar.PoincareBendixsonKernelBundle)
    (κ : Examples.Lotka.N.RateConstants)
    (h0 : 0 < κ.k Examples.Lotka.grow) (h1 : 0 < κ.k Examples.Lotka.prey)
    (h2 : 0 < κ.k Examples.Lotka.decay) :
    Examples.Lotka.N.HasPositivePeriodicOrbit κ := by
  -- the level set of the first integral through the seed
  let c : ℝ := Examples.Lotka.firstIntegral κ (lotkaSeed κ)
  have hp₀ : (lotkaSeed κ).Positive := lotkaSeed_pos κ h1 h2 h0
  have hp₀ne : lotkaSeed κ ≠ Examples.Lotka.equilibrium κ := lotkaSeed_ne_equilibrium κ h1 h2
  have hc' : Examples.Lotka.firstIntegral κ (Examples.Lotka.equilibrium κ) < c := by
    have h := Examples.Lotka.firstIntegral_gt_equilibrium κ h0 h1 h2 hp₀ hp₀ne
    simpa [c] using h
  -- a box containing the level set
  obtain ⟨δ, M, hδ, hbox⟩ := Examples.Lotka.sublevel_box κ h0 h1 h2 c
  have hδM : δ ≤ M := by
    have h := hbox (lotkaSeed κ) hp₀ (by simp [c]) Examples.Lotka.A
    linarith [h.1, h.2]
  set lo : ℝ := δ / 2 with lodef
  set hi : ℝ := M + 1 with hidef
  have hlo : 0 < lo := by positivity
  have hle : lo ≤ hi := by linarith
  have hK : ∀ x ∈ lotkaLevelSet κ c, ∀ s, lo < x s ∧ x s < hi := by
    intro x hx s
    have h := hbox x hx.1 hx.2.le s
    constructor <;> linarith
  -- the trapping data
  obtain ⟨D, hDregion⟩ := exists_lotka_flowTrappingData κ h0 h1 h2 (lotkaSeed κ) hp₀ c (by simp [c])
    hc' lo hi hlo hle hK
  -- the planar kernel produces a periodic orbit in the omega-limit set
  obtain ⟨P, hPomega⟩ := Planar.periodicTrajectory_in_omegaSet_of_classification
    K.omegaClassification D (contDiff_lotkaClampedField κ lo hi)
  have hPmem : ∀ t, P.orbit t ∈ D.region := by
    intro t
    exact D.omegaSet_subset_region
      (hPomega (show P.orbit t ∈ P.orbitSet from ⟨t, rfl⟩))
  -- the orbit is positive and inside the cut-off box
  have hPpos : ∀ t s, 0 < (P.orbit t).ofLp s := by
    intro t s
    have hz' : P.orbit t ∈ WithLp.toLp 2 '' lotkaLevelSet κ c := by
      rw [← hDregion]
      exact hPmem t
    obtain ⟨y, hy, heq⟩ := hz'
    rw [← heq]
    exact hy.1 s
  have hPbox : ∀ t s, lo < (P.orbit t).ofLp s ∧ (P.orbit t).ofLp s < hi := by
    intro t s
    have hz' : P.orbit t ∈ WithLp.toLp 2 '' lotkaLevelSet κ c := by
      rw [← hDregion]
      exact hPmem t
    obtain ⟨y, hy, heq⟩ := hz'
    rw [← heq]
    exact hK y hy s
  -- on the orbit the cut-off field *is* the mass-action field
  have hPfield : ∀ t s, (lotkaClampedField κ lo hi (P.orbit t)).ofLp s
      = Examples.Lotka.N.massActionVectorField κ (fun s' => (P.orbit t).ofLp s') s := by
    intro t s
    rw [lotkaClampedField_apply]
    have hclamp : lotkaClamp2 lo hi (P.orbit t) = fun s' => (P.orbit t).ofLp s' := by
      refine lotkaClamp2_eq_self lo hi (P.orbit t) ?_
      intro i
      have hib := hPbox t i
      exact ⟨le_of_lt hib.1, le_of_lt hib.2⟩
    rw [hclamp]
  -- the periodic orbit of the cut-off field is a mass-action periodic orbit
  refine ⟨{ orbit := fun t => fun s => (P.orbit t).ofLp s
            period := P.period
            period_pos := P.period_pos
            positive := by
              intro t s
              exact hPpos t s
            solution := by
              intro t s
              have hproj := hasDerivAt_phase2_apply (lotkaClampedField κ lo hi) P.orbit P.solution t s
              rw [hPfield t s] at hproj
              exact hproj
            periodic := by
              intro t
              exact congrArg (fun z : Phase2 => fun s => z.ofLp s) (P.periodic t)
            nonconstant := by
              obtain ⟨t, ht⟩ := P.nonconstant
              refine ⟨t, fun h => ht ?_⟩
              rw [WithLp.ext_iff]
              funext s
              exact congrFun h s }⟩

/-- **The Lotka network has oscillatory capacity, provided the universal planar kernel is
available.**

This is the conclusion in the repository's `OscillatoryCapacity` language: there is a choice of
positive rate constants for which the network admits a positive nonconstant periodic orbit.

Note that `CRNT.Examples.LotkaPeriodic.oscillatoryCapacity` proves the same statement
*unconditionally*, by exhibiting the periodic orbit explicitly.  The point of the theorem here is
different: it shows that the periodic orbit is produced by the *Poincaré--Bendixson route*, with
the trapping region as the only network-specific input. -/
theorem lotka_oscillatoryCapacity_of_trappingRegion
    (K : Planar.PoincareBendixsonKernelBundle)
    (κ : Examples.Lotka.N.RateConstants)
    (h0 : 0 < κ.k Examples.Lotka.grow) (h1 : 0 < κ.k Examples.Lotka.prey)
    (h2 : 0 < κ.k Examples.Lotka.decay) :
    Examples.Lotka.N.OscillatoryCapacity :=
  ⟨κ, lotka_hasPositivePeriodicOrbit_of_trappingRegion K κ h0 h1 h2⟩

end Oscillation
end CRNT
