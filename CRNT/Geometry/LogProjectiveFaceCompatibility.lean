import CRNT.Geometry.LogProjectiveSmoothSection
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Compatibility of neighboring logarithmic projective sections

Two affine face sections reconstruct the same point on a common projective ray when their weights
have the same total on each fiber of the projective-coordinate map. This gives an exact pointwise
overlap criterion: coordinates tied on a blueprint face form the fibers, and matching the total
face weight on each such fiber makes the two scalar section equations identical. C¹ gluing
across a seam also needs transverse first-order compatibility. Matching the weighted first moments
on each fiber makes the scalar level equations' directional derivatives agree; the two-species
example below shows that fiber balance alone does not imply this stronger $C^1$ condition. The
cited ZSH construction requires a piecewise smooth surface and checks its non-crossing condition at
smooth points (arXiv:1501.02860v3, Definition 4.6), so a first-derivative mismatch alone does not
obstruct that construction. Verifying pointwise balance and the required seam geometry for a
particular faithful blueprint remains a geometric task.
-/

namespace CRNT
namespace LogProjectiveFaceCompatibility

open Filter Set

variable {ι : Type*} [Fintype ι]

/-- Total face weight carried by one fiber of the projective-coordinate map `y`. -/
noncomputable def projectiveFiberWeight (y b : ι → ℝ) (v : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => y i = v), b i

/-- Matching weights on every projective-coordinate fiber forces equal total affine weights. -/
theorem totalWeight_eq_of_projectiveFiberWeight_eq (b c y : ι → ℝ)
    (hfiber : ∀ v, projectiveFiberWeight y b v = projectiveFiberWeight y c v) :
    (∑ i, b i) = (∑ i, c i) := by
  classical
  let V := Finset.univ.image y
  have hmap (i : ι) (hi : i ∈ Finset.univ) : y i ∈ V :=
    Finset.mem_image_of_mem y hi
  have hbgroup : (∑ v ∈ V, projectiveFiberWeight y b v) = ∑ i, b i := by
    simpa [projectiveFiberWeight, V] using
      (Finset.sum_fiberwise_of_maps_to hmap b)
  have hcgroup : (∑ v ∈ V, projectiveFiberWeight y c v) = ∑ i, c i := by
    simpa [projectiveFiberWeight, V] using
      (Finset.sum_fiberwise_of_maps_to hmap c)
  calc
    (∑ i, b i) = ∑ v ∈ V, projectiveFiberWeight y b v := hbgroup.symm
    _ = ∑ v ∈ V, projectiveFiberWeight y c v := by
      apply Finset.sum_congr rfl
      intro v hv
      exact hfiber v
    _ = ∑ i, c i := hcgroup

/-- Two affine normals define the same linear form on every vector that is constant on the
projective-coordinate fibers exactly when their total weights agree on each fiber. This makes the
fiber-balance hypothesis a necessary and sufficient compatibility condition on a tied-coordinate
stratum, rather than only a sufficient condition for matching one exponential ray. -/
theorem affineForm_eq_on_projectiveFibers_iff (b c y : ι → ℝ) :
    (∀ φ : ℝ → ℝ, (∑ i, b i * φ (y i)) = (∑ i, c i * φ (y i))) ↔
      ∀ v, projectiveFiberWeight y b v = projectiveFiberWeight y c v := by
  classical
  constructor
  · intro h v
    have htest := h (fun q => if q = v then (1 : ℝ) else 0)
    simpa [projectiveFiberWeight, Finset.sum_filter, eq_comm] using htest
  · intro hfiber φ
    let V := Finset.univ.image y
    have hmap (i : ι) (hi : i ∈ Finset.univ) : y i ∈ V :=
      Finset.mem_image_of_mem y hi
    have hbgroup :
        (∑ v ∈ V, ∑ i ∈ Finset.univ.filter (fun i => y i = v), b i * φ (y i)) =
          ∑ i, b i * φ (y i) := by
      simpa [V] using Finset.sum_fiberwise_of_maps_to hmap (fun i => b i * φ (y i))
    have hcgroup :
        (∑ v ∈ V, ∑ i ∈ Finset.univ.filter (fun i => y i = v), c i * φ (y i)) =
          ∑ i, c i * φ (y i) := by
      simpa [V] using Finset.sum_fiberwise_of_maps_to hmap (fun i => c i * φ (y i))
    have hfiberB (v : ℝ) :
        (∑ i ∈ Finset.univ.filter (fun i => y i = v), b i * φ (y i)) =
          projectiveFiberWeight y b v * φ v := by
      calc
        (∑ i ∈ Finset.univ.filter (fun i => y i = v), b i * φ (y i)) =
            ∑ i ∈ Finset.univ.filter (fun i => y i = v), b i * φ v := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [(Finset.mem_filter.mp hi).2]
        _ = (∑ i ∈ Finset.univ.filter (fun i => y i = v), b i) * φ v := by
              rw [Finset.sum_mul]
        _ = projectiveFiberWeight y b v * φ v := rfl
    have hfiberC (v : ℝ) :
        (∑ i ∈ Finset.univ.filter (fun i => y i = v), c i * φ (y i)) =
          projectiveFiberWeight y c v * φ v := by
      calc
        (∑ i ∈ Finset.univ.filter (fun i => y i = v), c i * φ (y i)) =
            ∑ i ∈ Finset.univ.filter (fun i => y i = v), c i * φ v := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [(Finset.mem_filter.mp hi).2]
        _ = (∑ i ∈ Finset.univ.filter (fun i => y i = v), c i) * φ v := by
              rw [Finset.sum_mul]
        _ = projectiveFiberWeight y c v * φ v := rfl
    calc
      (∑ i, b i * φ (y i)) =
          ∑ v ∈ V, projectiveFiberWeight y b v * φ v := by
            rw [← hbgroup]
            apply Finset.sum_congr rfl
            intro v hv
            exact hfiberB v
      _ = ∑ v ∈ V, projectiveFiberWeight y c v * φ v := by
            apply Finset.sum_congr rfl
            intro v hv
            rw [hfiber v]
      _ = ∑ i, c i * φ (y i) := by
            rw [← hcgroup]
            apply Finset.sum_congr rfl
            intro v hv
            exact (hfiberC v).symm

/-- On a ray with pairwise distinct projective coordinates, exact agreement of two affine forms
for every projective-coordinate test function forces their weights to agree coordinatewise. The
quantification over all test functions is essential: agreement of the two scalar level equations
at one scale alone does not imply this conclusion. -/
theorem eq_of_affineForm_eq_of_injective (b c y : ι → ℝ)
    (hy : Function.Injective y)
    (hform : ∀ φ : ℝ → ℝ,
      (∑ i, b i * φ (y i)) = (∑ i, c i * φ (y i))) :
    b = c := by
  classical
  have hfiber : ∀ v, projectiveFiberWeight y b v = projectiveFiberWeight y c v :=
    (affineForm_eq_on_projectiveFibers_iff b c y).mp hform
  funext i
  have hfilter : Finset.univ.filter (fun j : ι => y j = y i) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hji
      exact hy hji
    · intro hji
      subst j
      rfl
  have hbi : projectiveFiberWeight y b (y i) = b i := by
    simp [projectiveFiberWeight, hfilter]
  have hci : projectiveFiberWeight y c (y i) = c i := by
    simp [projectiveFiberWeight, hfilter]
  calc
    b i = projectiveFiberWeight y b (y i) := hbi.symm
    _ = projectiveFiberWeight y c (y i) := hfiber (y i)
    _ = c i := hci

/-- Matching total weights on every projective-coordinate fiber forces identical weighted
exponential levels at every logarithmic ray scale. -/
theorem weightedExpLevel_eq_of_projectiveFiberWeight_eq (b c y : ι → ℝ) (t : ℝ)
    (hfiber : ∀ v, projectiveFiberWeight y b v = projectiveFiberWeight y c v) :
    LogProjectiveSection.weightedExpLevel b y t =
      LogProjectiveSection.weightedExpLevel c y t := by
  classical
  let V := Finset.univ.image y
  have hmap (i : ι) (hi : i ∈ Finset.univ) : y i ∈ V :=
    Finset.mem_image_of_mem y hi
  have hbgroup :
      (∑ v ∈ V, ∑ i ∈ Finset.univ.filter (fun i => y i = v),
        b i * Real.exp (-(t * y i))) = LogProjectiveSection.weightedExpLevel b y t := by
    simpa [LogProjectiveSection.weightedExpLevel, V] using
      (Finset.sum_fiberwise_of_maps_to hmap
        (fun i => b i * Real.exp (-(t * y i))))
  have hcgroup :
      (∑ v ∈ V, ∑ i ∈ Finset.univ.filter (fun i => y i = v),
        c i * Real.exp (-(t * y i))) = LogProjectiveSection.weightedExpLevel c y t := by
    simpa [LogProjectiveSection.weightedExpLevel, V] using
      (Finset.sum_fiberwise_of_maps_to hmap
        (fun i => c i * Real.exp (-(t * y i))))
  have hfiberExpB (v : ℝ) :
      (∑ i ∈ Finset.univ.filter (fun i => y i = v), b i * Real.exp (-(t * y i))) =
        projectiveFiberWeight y b v * Real.exp (-(t * v)) := by
    calc
      (∑ i ∈ Finset.univ.filter (fun i => y i = v),
          b i * Real.exp (-(t * y i))) =
          ∑ i ∈ Finset.univ.filter (fun i => y i = v),
            b i * Real.exp (-(t * v)) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [(Finset.mem_filter.mp hi).2]
      _ = (∑ i ∈ Finset.univ.filter (fun i => y i = v), b i) *
          Real.exp (-(t * v)) := by rw [Finset.sum_mul]
      _ = projectiveFiberWeight y b v * Real.exp (-(t * v)) := rfl
  have hfiberExpC (v : ℝ) :
      (∑ i ∈ Finset.univ.filter (fun i => y i = v), c i * Real.exp (-(t * y i))) =
        projectiveFiberWeight y c v * Real.exp (-(t * v)) := by
    calc
      (∑ i ∈ Finset.univ.filter (fun i => y i = v),
          c i * Real.exp (-(t * y i))) =
          ∑ i ∈ Finset.univ.filter (fun i => y i = v),
            c i * Real.exp (-(t * v)) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [(Finset.mem_filter.mp hi).2]
      _ = (∑ i ∈ Finset.univ.filter (fun i => y i = v), c i) *
          Real.exp (-(t * v)) := by rw [Finset.sum_mul]
      _ = projectiveFiberWeight y c v * Real.exp (-(t * v)) := rfl
  calc
    LogProjectiveSection.weightedExpLevel b y t =
        ∑ v ∈ V, projectiveFiberWeight y b v * Real.exp (-(t * v)) := by
          rw [← hbgroup]
          apply Finset.sum_congr rfl
          intro v hv
          exact hfiberExpB v
    _ = ∑ v ∈ V, projectiveFiberWeight y c v * Real.exp (-(t * v)) := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [hfiber v]
    _ = LogProjectiveSection.weightedExpLevel c y t := by
          rw [← hcgroup]
          apply Finset.sum_congr rfl
          intro v hv
          exact (hfiberExpC v).symm

/-- Derivative of a weighted exponential level when the projective coordinates vary linearly in a
direction `q`, with the scale `t` held fixed. -/
theorem hasDerivAt_weightedExpLevel_along_linear_ray (b y q : ι → ℝ) (t : ℝ) :
    HasDerivAt
      (fun r : ℝ => LogProjectiveSection.weightedExpLevel b (fun i => y i + r * q i) t)
      (∑ i, b i * Real.exp (-(t * y i)) * (-(t * q i))) 0 := by
  classical
  unfold LogProjectiveSection.weightedExpLevel
  apply HasDerivAt.fun_sum
  intro i hi
  have hlinear : HasDerivAt (fun r : ℝ => y i + r * q i) (q i) 0 := by
    have hid := (hasDerivAt_id (0 : ℝ)).mul_const (q i)
    have hadd := hid.add_const (y i)
    simpa [id_eq, add_comm, mul_comm] using hadd
  have hinner : HasDerivAt (fun r : ℝ => -(t * (y i + r * q i)))
      (-(t * q i)) 0 := by
    have hmul := hlinear.const_mul (-t)
    simpa [neg_mul] using hmul
  have hexp : HasDerivAt
      (fun r : ℝ => Real.exp (-(t * (y i + r * q i))))
      (Real.exp (-(t * y i)) * (-(t * q i))) 0 := by
    simpa using hinner.exp
  convert HasDerivAt.const_mul (b i) hexp using 1
  ring

/-- If neighboring weights match on each projective-coordinate fiber and also match their
directional first moments there, their weighted exponential level equations have the same first
derivative along that ray direction at every fixed scale. Fiber mass alone gives the value
compatibility; this additional moment condition is the first-order datum needed before applying
implicit differentiation to the selected section scales. -/
theorem exists_common_weightedExpLevel_derivative_of_fiber_first_moment
    (b c y q : ι → ℝ) (t : ℝ)
    (hfiber : ∀ v, projectiveFiberWeight y b v = projectiveFiberWeight y c v)
    (hmoment : ∀ v,
      projectiveFiberWeight y (fun i => b i * q i) v =
        projectiveFiberWeight y (fun i => c i * q i) v) :
    ∃ d : ℝ,
      LogProjectiveSection.weightedExpLevel b y t =
        LogProjectiveSection.weightedExpLevel c y t ∧
      HasDerivAt
        (fun r : ℝ => LogProjectiveSection.weightedExpLevel b (fun i => y i + r * q i) t)
        d 0 ∧
      HasDerivAt
        (fun r : ℝ => LogProjectiveSection.weightedExpLevel c (fun i => y i + r * q i) t)
        d 0 := by
  classical
  let d := ∑ i, b i * Real.exp (-(t * y i)) * (-(t * q i))
  have hlevels := weightedExpLevel_eq_of_projectiveFiberWeight_eq
    (fun i => b i * q i) (fun i => c i * q i) y t hmoment
  have hderivs :
      (∑ i, b i * Real.exp (-(t * y i)) * (-(t * q i))) =
        ∑ i, c i * Real.exp (-(t * y i)) * (-(t * q i)) := by
    calc
      (∑ i, b i * Real.exp (-(t * y i)) * (-(t * q i))) =
          (-t) * LogProjectiveSection.weightedExpLevel
            (fun i => b i * q i) y t := by
              unfold LogProjectiveSection.weightedExpLevel
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = (-t) * LogProjectiveSection.weightedExpLevel
            (fun i => c i * q i) y t := by rw [hlevels]
      _ = ∑ i, c i * Real.exp (-(t * y i)) * (-(t * q i)) := by
              unfold LogProjectiveSection.weightedExpLevel
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
  refine ⟨d, weightedExpLevel_eq_of_projectiveFiberWeight_eq b c y t hfiber, ?_, ?_⟩
  · simpa [d] using hasDerivAt_weightedExpLevel_along_linear_ray b y q t
  · simpa [d, hderivs] using hasDerivAt_weightedExpLevel_along_linear_ray c y q t

/-- Fiberwise-compatible affine sections have exactly the same level equation. -/
theorem affineLevel_eq_iff_of_projectiveFiberWeight_eq (b c y : ι → ℝ)
    (a t : ℝ)
    (hfiber : ∀ v, projectiveFiberWeight y b v = projectiveFiberWeight y c v) :
    (LogProjectiveSection.weightedExpLevel b y t = a * (∑ i, b i)) ↔
      (LogProjectiveSection.weightedExpLevel c y t = a * (∑ i, c i)) := by
  rw [weightedExpLevel_eq_of_projectiveFiberWeight_eq b c y t hfiber,
    totalWeight_eq_of_projectiveFiberWeight_eq b c y hfiber]

/-- If neighboring face weights match on every tied-coordinate fiber, then their unique positive
section scales agree exactly. Consequently the two faces reconstruct the same point on every
shared projective ray satisfying the fiber-balance condition. -/
theorem existsUnique_common_sectionScale (b c y : ι → ℝ) {a : ℝ}
    (hb : ∀ i, 0 ≤ b i) (hbsum : 0 < ∑ i, b i)
    (hy : ∀ i, 0 < y i) (ha0 : 0 < a) (ha1 : a < 1)
    (hfiber : ∀ v, projectiveFiberWeight y b v = projectiveFiberWeight y c v) :
    ∃! t : ℝ,
      0 < t ∧
      LogProjectiveSection.weightedExpLevel b y t = a * (∑ i, b i) ∧
      LogProjectiveSection.weightedExpLevel c y t = a * (∑ i, c i) := by
  obtain ⟨t, ht, hunique⟩ :=
    LogProjectiveSection.existsUnique_sectionScale_of_positive b y hb hbsum hy ha0 ha1
  have hrootC :=
    (affineLevel_eq_iff_of_projectiveFiberWeight_eq b c y a t hfiber).mp ht.2
  refine ⟨t, ⟨ht.1, ht.2, hrootC⟩, ?_⟩
  intro u hu
  exact hunique u ⟨hu.1, hu.2.1⟩

/-- When neighboring face weights balance on every projective-coordinate fiber, their canonical
smooth section points agree on the shared ray. This is the pointwise overlap condition needed to
glue the individual affine-face charts. -/
theorem positiveSectionPoint_eq_of_projectiveFiberWeight_eq
    [DecidableEq ι] (b c : ι → ℝ) {a : ℝ} {i₀ : ι}
    (hb : ∀ i, 0 ≤ b i) (hbsum : 0 < ∑ i, b i)
    (hc : ∀ i, 0 ≤ c i) (hcsum : 0 < ∑ i, c i)
    (ha0 : 0 < a) (ha1 : a < 1)
    (z : ({i : ι // i ≠ i₀} → ℝ))
    (hy : ∀ i, 0 < LogProjectiveSection.normalizedCoordinates i₀ z i)
    (hfiber : ∀ v,
      projectiveFiberWeight (LogProjectiveSection.normalizedCoordinates i₀ z) b v =
        projectiveFiberWeight (LogProjectiveSection.normalizedCoordinates i₀ z) c v) :
    LogProjectiveSection.positiveSectionPoint b a i₀ hb hbsum ha0 ha1 z =
      LogProjectiveSection.positiveSectionPoint c a i₀ hc hcsum ha0 ha1 z := by
  let y := LogProjectiveSection.normalizedCoordinates i₀ z
  let tb := LogProjectiveSection.positiveSectionScale b a i₀ hb hbsum ha0 ha1 z
  let tc := LogProjectiveSection.positiveSectionScale c a i₀ hc hcsum ha0 ha1 z
  have hB := LogProjectiveSection.positiveSectionScale_spec b a i₀ hb hbsum ha0 ha1 z hy
  have hC := LogProjectiveSection.positiveSectionScale_spec c a i₀ hc hcsum ha0 ha1 z hy
  have hcommon := existsUnique_common_sectionScale b c y hb hbsum hy ha0 ha1 hfiber
  obtain ⟨t, ht, hunique⟩ := hcommon
  have hrootC := (affineLevel_eq_iff_of_projectiveFiberWeight_eq b c y a tb hfiber).mp hB.2
  have hrootB := (affineLevel_eq_iff_of_projectiveFiberWeight_eq b c y a tc hfiber).mpr hC.2
  have htb : tb = t := hunique tb ⟨hB.1, hB.2, hrootC⟩
  have htc : tc = t := hunique tc ⟨hC.1, hrootB, hC.2⟩
  change LogProjectiveSection.sectionPoint y tb = LogProjectiveSection.sectionPoint y tc
  rw [htb, htc]

/-! ## A C¹-gluing diagnostic

Pointwise fiber balance makes neighboring section points agree on a shared ray, but does not
control how their scales vary transverse to that ray. The two-species example below gives matching
values at a tied-coordinate ray and different first derivatives there. Thus a C¹ gluing argument
needs a separate first-jet compatibility condition. The piecewise-smooth ZSH criterion cited above
imposes its tangent condition only at smooth points, so this example does not by itself block a
piecewise-smooth construction. -/

namespace TwoSpeciesJetExample

open LogProjectiveSection
open Filter Set
open scoped Topology

abbrev Species := Fin 2

def leftWeight : Species → ℝ := fun i => if i = 0 then 1 else 0
def rightWeight : Species → ℝ := fun i => if i = 1 then 1 else 0
def transverseDirection : Species → ℝ := rightWeight
def ray (r : ℝ) : ({i : Species // i ≠ 0} → ℝ) := fun _ => r

private theorem leftWeight_nonneg : ∀ i, 0 ≤ leftWeight i := by
  intro i
  fin_cases i <;> norm_num [leftWeight]

private theorem rightWeight_nonneg : ∀ i, 0 ≤ rightWeight i := by
  intro i
  fin_cases i <;> norm_num [rightWeight]

private theorem leftWeight_sum : (∑ i, leftWeight i) = 1 := by
  simp [leftWeight]

private theorem rightWeight_sum : (∑ i, rightWeight i) = 1 := by
  simp [rightWeight]

noncomputable def leftScale (r : ℝ) : ℝ :=
  positiveSectionScale leftWeight (1 / 2) (0 : Species)
    leftWeight_nonneg (by rw [leftWeight_sum]; norm_num) (by norm_num) (by norm_num) (ray r)

noncomputable def rightScale (r : ℝ) : ℝ :=
  positiveSectionScale rightWeight (1 / 2) (0 : Species)
    rightWeight_nonneg (by rw [rightWeight_sum]; norm_num) (by norm_num) (by norm_num) (ray r)

noncomputable def leftPoint (r : ℝ) : Species → ℝ :=
  positiveSectionPoint leftWeight (1 / 2) (0 : Species)
    leftWeight_nonneg (by rw [leftWeight_sum]; norm_num) (by norm_num) (by norm_num) (ray r)

noncomputable def rightPoint (r : ℝ) : Species → ℝ :=
  positiveSectionPoint rightWeight (1 / 2) (0 : Species)
    rightWeight_nonneg (by rw [rightWeight_sum]; norm_num) (by norm_num) (by norm_num) (ray r)

private theorem ray_coordinates_positive {r : ℝ} (hr : 0 < r) :
    ∀ i, 0 < normalizedCoordinates (0 : Species) (ray r) i := by
  intro i
  fin_cases i
  all_goals simp [normalizedCoordinates, ray] <;> linarith

private theorem leftScale_eq_log_two {r : ℝ} (hr : 0 < r) :
    leftScale r = Real.log 2 := by
  have hy := ray_coordinates_positive hr
  have hspec := positiveSectionScale_spec leftWeight (1 / 2) (0 : Species)
    leftWeight_nonneg (by rw [leftWeight_sum]; norm_num) (by norm_num) (by norm_num)
    (ray r) hy
  have hroot : 0 < Real.log 2 ∧
      weightedExpLevel leftWeight (normalizedCoordinates (0 : Species) (ray r))
        (Real.log 2) = (1 / 2 : ℝ) * (∑ i, leftWeight i) := by
    constructor
    · exact Real.log_pos (by norm_num)
    · rw [leftWeight_sum]
      simp [weightedExpLevel, leftWeight, normalizedCoordinates, ray]
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  obtain ⟨t, ht, hu⟩ := existsUnique_sectionScale_of_positive leftWeight
    (a := (1 / 2 : ℝ)) (normalizedCoordinates (0 : Species) (ray r))
    leftWeight_nonneg (by rw [leftWeight_sum]; norm_num)
    hy (by norm_num) (by norm_num)
  calc
    leftScale r = t := hu _ hspec
    _ = Real.log 2 := (hu _ hroot).symm

private theorem rightScale_eq_log_two_div {r : ℝ} (hr : 0 < r) :
    rightScale r = Real.log 2 / r := by
  have hy := ray_coordinates_positive hr
  have hspec := positiveSectionScale_spec rightWeight (1 / 2) (0 : Species)
    rightWeight_nonneg (by rw [rightWeight_sum]; norm_num) (by norm_num) (by norm_num)
    (ray r) hy
  have hroot : 0 < Real.log 2 / r ∧
      weightedExpLevel rightWeight (normalizedCoordinates (0 : Species) (ray r))
        (Real.log 2 / r) = (1 / 2 : ℝ) * (∑ i, rightWeight i) := by
    constructor
    · exact div_pos (Real.log_pos (by norm_num)) hr
    · rw [rightWeight_sum]
      simp [weightedExpLevel, rightWeight, normalizedCoordinates, ray]
      have hrne : r ≠ 0 := ne_of_gt hr
      have hcancel : (Real.log 2 / r) * r = Real.log 2 := by
        field_simp
      rw [hcancel, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  obtain ⟨t, ht, hu⟩ := existsUnique_sectionScale_of_positive rightWeight
    (a := (1 / 2 : ℝ)) (normalizedCoordinates (0 : Species) (ray r))
    rightWeight_nonneg (by rw [rightWeight_sum]; norm_num)
    hy (by norm_num) (by norm_num)
  calc
    rightScale r = t := hu _ hspec
    _ = Real.log 2 / r := (hu _ hroot).symm

private theorem fiber_weights_agree_at_tied_ray :
    ∀ v : ℝ,
      projectiveFiberWeight (normalizedCoordinates (0 : Species) (ray 1)) leftWeight v =
        projectiveFiberWeight (normalizedCoordinates (0 : Species) (ray 1)) rightWeight v := by
  classical
  intro v
  by_cases hv : v = 1
  · subst v
    simp [projectiveFiberWeight, leftWeight, rightWeight, normalizedCoordinates, ray]
  · simp [projectiveFiberWeight, leftWeight, rightWeight, normalizedCoordinates, ray, eq_comm, hv]

private theorem transverse_fiber_first_moments_differ :
    projectiveFiberWeight (normalizedCoordinates (0 : Species) (ray 1))
        (fun i => leftWeight i * transverseDirection i) 1 = 0 ∧
      projectiveFiberWeight (normalizedCoordinates (0 : Species) (ray 1))
        (fun i => rightWeight i * transverseDirection i) 1 = 1 := by
  constructor <;>
    simp [projectiveFiberWeight, leftWeight, rightWeight, transverseDirection,
      normalizedCoordinates, ray]

/-- At the tied ray `(1,1)`, the two face weights have equal mass on every projective-coordinate
fiber and hence their canonical section scales agree. Their transverse derivatives are `0` and
`-log 2`, respectively. This is a concrete witness that pointwise overlap compatibility alone
does not establish C¹ gluing across a face seam. It diagnoses the stronger C¹ requirement and does
not refute a piecewise-smooth ZSH construction. -/
theorem pointwise_compatibility_does_not_imply_first_jet_compatibility :
    (∀ v : ℝ,
      projectiveFiberWeight (normalizedCoordinates (0 : Species) (ray 1)) leftWeight v =
        projectiveFiberWeight (normalizedCoordinates (0 : Species) (ray 1)) rightWeight v) ∧
    projectiveFiberWeight (normalizedCoordinates (0 : Species) (ray 1))
        (fun i => leftWeight i * transverseDirection i) 1 = 0 ∧
      projectiveFiberWeight (normalizedCoordinates (0 : Species) (ray 1))
        (fun i => rightWeight i * transverseDirection i) 1 = 1 ∧
    leftScale 1 = rightScale 1 ∧
    leftPoint 1 = rightPoint 1 ∧
    HasDerivAt leftScale 0 1 ∧
    HasDerivAt rightScale (-Real.log 2) 1 ∧
    0 ≠ -Real.log 2 := by
  have h0eq : leftScale =ᶠ[𝓝 (1 : ℝ)] fun _ => Real.log 2 := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with r hr
    exact leftScale_eq_log_two hr
  have h1eq : rightScale =ᶠ[𝓝 (1 : ℝ)] fun r => Real.log 2 / r := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with r hr
    exact rightScale_eq_log_two_div hr
  have hd0 : HasDerivAt (fun _ : ℝ => Real.log 2) 0 1 := by
    simpa using (hasDerivAt_const (1 : ℝ) (Real.log 2))
  have hd1 : HasDerivAt (fun r : ℝ => Real.log 2 / r) (-Real.log 2) 1 := by
    simpa using
      (hasDerivAt_const (1 : ℝ) (Real.log 2)).fun_div
        (hasDerivAt_id (1 : ℝ)) (by norm_num)
  refine ⟨fiber_weights_agree_at_tied_ray, transverse_fiber_first_moments_differ.1,
    transverse_fiber_first_moments_differ.2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [leftScale_eq_log_two (by norm_num), rightScale_eq_log_two_div (by norm_num)]
    simp
  · exact positiveSectionPoint_eq_of_projectiveFiberWeight_eq leftWeight rightWeight
      leftWeight_nonneg (by rw [leftWeight_sum]; norm_num)
      rightWeight_nonneg (by rw [rightWeight_sum]; norm_num)
      (by norm_num) (by norm_num) (ray 1)
      (ray_coordinates_positive (by norm_num)) fiber_weights_agree_at_tied_ray
  · exact hd0.congr_of_eventuallyEq h0eq
  · exact hd1.congr_of_eventuallyEq h1eq
  · exact ne_of_gt (neg_lt_zero.mpr (Real.log_pos (by norm_num)))

end TwoSpeciesJetExample

end LogProjectiveFaceCompatibility
end CRNT
