import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# Log-projective sections of positive affine hyperplanes

In Craciun's three-dimensional face construction, the logarithmic projective map restricted to a
plane through the common initial point is a diffeomorphism onto its image (v3, §6.1.2). This file
proves the pointwise, arbitrary-finite-dimensional intersection statement behind that chart.

Given nonnegative weights `b` with positive total weight, a ray
`xᵢ = exp (-t * yᵢ)` with all `yᵢ ≥ 1` meets the affine section
`∑ bᵢ xᵢ = a * ∑ bᵢ` exactly once for every `0 < a < 1`. The result supplies a unique point
with the prescribed logarithmic projective coordinates. It does not establish smooth dependence
on those coordinates or compatibility of several such sections along shared tile faces.
-/

namespace CRNT
namespace LogProjectiveSection

open Filter Set

variable {ι : Type*} [Fintype ι]

/-- The value of a weighted positive ray at logarithmic projective coordinate `y` and scale `t`. -/
noncomputable def weightedExpLevel (b y : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, b i * Real.exp (-(t * y i))

/-- A ray with positive coordinates meets every positive fraction of its total affine weight
exactly once. Strict decrease follows from any positive coefficient, and the finite weighted
exponential sum tends to zero as the scale tends to infinity. -/
theorem existsUnique_sectionScale_of_positive (b y : ι → ℝ) {a : ℝ}
    (hb : ∀ i, 0 ≤ b i) (hbsum : 0 < ∑ i, b i)
    (hy : ∀ i, 0 < y i) (ha0 : 0 < a) (ha1 : a < 1) :
    ∃! t : ℝ, 0 < t ∧ weightedExpLevel b y t = a * (∑ i, b i) := by
  let F : ℝ → ℝ := weightedExpLevel b y
  have hFcont : Continuous F := by
    change Continuous (fun t => ∑ i, b i * Real.exp (-(t * y i)))
    fun_prop
  have hF0 : F 0 = ∑ i, b i := by
    simp [F, weightedExpLevel]
  have hFzero : Tendsto F atTop (nhds 0) := by
    change Tendsto (fun t : ℝ => ∑ i, b i * Real.exp (-(t * y i))) atTop (nhds 0)
    rw [← Finset.sum_const_zero]
    refine tendsto_finsetSum (Finset.univ : Finset ι) fun i _ => ?_
    have harg : Tendsto (fun t : ℝ => t * y i) atTop atTop :=
      (tendsto_mul_const_atTop_of_pos (hy i)).2 tendsto_id
    have hexp : Tendsto (fun t : ℝ => Real.exp (-(t * y i))) atTop (nhds 0) := by
      change Tendsto ((fun u : ℝ => Real.exp (-u)) ∘ (fun t => t * y i))
        atTop (nhds 0)
      exact Real.tendsto_exp_neg_atTop_nhds_zero.comp harg
    simpa using (tendsto_const_nhds.mul hexp)
  have hpositiveTerm : ∃ i, 0 < b i := by
    by_contra h
    have hall : ∀ i, b i ≤ 0 := fun i => le_of_not_gt (fun hi => h ⟨i, hi⟩)
    have hsumle : ∑ i, b i ≤ 0 := by
      calc
        (∑ i, b i) ≤ ∑ i, (0 : ℝ) := Finset.sum_le_sum (fun i _ => hall i)
        _ = 0 := by simp
    linarith
  obtain ⟨i₀, hi₀⟩ := hpositiveTerm
  have hFanti {s t : ℝ} (hst : s < t) : F t < F s := by
    apply Finset.sum_lt_sum
    · intro i _
      have harg : -(t * y i) < -(s * y i) :=
        neg_lt_neg (mul_lt_mul_of_pos_right hst (hy i))
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg.le) (hb i)
    · refine ⟨i₀, Finset.mem_univ _, ?_⟩
      have harg : -(t * y i₀) < -(s * y i₀) :=
        neg_lt_neg (mul_lt_mul_of_pos_right hst (hy i₀))
      exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr harg) hi₀
  have htargetpos : 0 < a * (∑ i, b i) := mul_pos ha0 hbsum
  have hev : ∀ᶠ t : ℝ in atTop, F t < a * (∑ i, b i) :=
    hFzero.eventually (Iio_mem_nhds htargetpos)
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.1 hev
  let T : ℝ := max B 1
  have hTB : B ≤ T := le_max_left _ _
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hFT : F T < a * (∑ i, b i) := hB T hTB
  have htargetle : a * (∑ i, b i) ≤ F 0 := by
    rw [hF0]
    calc
      a * (∑ i, b i) ≤ 1 * (∑ i, b i) :=
        mul_le_mul_of_nonneg_right ha1.le hbsum.le
      _ = ∑ i, b i := one_mul _
  have htargetmem : a * (∑ i, b i) ∈ Icc (F T) (F 0) := ⟨hFT.le, htargetle⟩
  have himage : a * (∑ i, b i) ∈ F '' Icc 0 T :=
    (intermediate_value_Icc' hTpos.le hFcont.continuousOn) htargetmem
  obtain ⟨t, htIcc, hteq⟩ := himage
  have htpos : 0 < t := by
    by_contra hnot
    have ht0 : t = 0 := le_antisymm (not_lt.mp hnot) htIcc.1
    rw [ht0, hF0] at hteq
    nlinarith [hbsum, ha1]
  refine ⟨t, ⟨htpos, hteq⟩, ?_⟩
  intro u hu
  have huF : F u = a * (∑ i, b i) := by simpa [F] using hu.2
  by_contra hne
  rcases lt_or_gt_of_ne hne with htu | hut
  · have hlt := hFanti htu
    rw [huF, hteq] at hlt
    exact (lt_irrefl _ hlt)
  · have hlt := hFanti hut
    rw [hteq, huF] at hlt
    exact (lt_irrefl _ hlt)

/-- An ordered projective ray meets every positive fraction of its total affine weight exactly
once. This is the `yᵢ ≥ 1` specialization used by the logarithmic projective chart. -/
theorem existsUnique_sectionScale (b y : ι → ℝ) {a : ℝ}
    (hb : ∀ i, 0 ≤ b i) (hbsum : 0 < ∑ i, b i)
    (hy : ∀ i, 1 ≤ y i) (ha0 : 0 < a) (ha1 : a < 1) :
    ∃! t : ℝ, 0 < t ∧ weightedExpLevel b y t = a * (∑ i, b i) :=
  existsUnique_sectionScale_of_positive b y hb hbsum
    (fun i => lt_of_lt_of_le zero_lt_one (hy i)) ha0 ha1

/-- The positive point on a projective ray at scale `t`. -/
noncomputable def sectionPoint (y : ι → ℝ) (t : ℝ) : ι → ℝ :=
  fun i => Real.exp (-(t * y i))

/-- The unique ray scale gives a point on the affine section. -/
theorem sectionPoint_mem_level (b y : ι → ℝ) {a t : ℝ}
    (ht : weightedExpLevel b y t = a * (∑ i, b i)) :
    (∑ i, b i * sectionPoint y t i) = a * (∑ i, b i) := by
  simpa [weightedExpLevel, sectionPoint] using ht

omit [Fintype ι] in
/-- The logarithmic projective coordinates of `sectionPoint` recover the ray coordinates when a
distinguished coordinate of the ray is normalized to one. -/
theorem sectionPoint_logProjective (y : ι → ℝ) {t : ℝ} (ht : 0 < t)
    {i₀ : ι} (hy₀ : y i₀ = 1) (i : ι) :
    Real.log (sectionPoint y t i) / Real.log (sectionPoint y t i₀) = y i := by
  simp only [sectionPoint, Real.log_exp, hy₀]
  field_simp

/-- Every positive normalized projective ray has a representative below one on the affine section,
with exactly the requested logarithmic projective coordinates. -/
theorem exists_sectionPoint_with_coordinates (b y : ι → ℝ) {a : ℝ} {i₀ : ι}
    (hb : ∀ i, 0 ≤ b i) (hbsum : 0 < ∑ i, b i)
    (hy : ∀ i, 0 < y i) (hy₀ : y i₀ = 1)
    (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ x : ι → ℝ, (∀ i, 0 < x i ∧ x i < 1) ∧
      (∑ i, b i * x i) = a * (∑ i, b i) ∧
      (∀ i, Real.log (x i) / Real.log (x i₀) = y i) := by
  obtain ⟨t, ⟨ht, hlevel⟩, _⟩ :=
    existsUnique_sectionScale_of_positive b y hb hbsum hy ha0 ha1
  refine ⟨sectionPoint y t, ?_, sectionPoint_mem_level b y hlevel, ?_⟩
  · intro i
    constructor
    · exact Real.exp_pos _
    · apply (Real.exp_lt_one_iff).2
      have hty : 0 < t * y i := mul_pos ht (hy i)
      linarith
  · intro i
    exact sectionPoint_logProjective y ht hy₀ i

/-- Any positive point below the unit section with the prescribed projective coordinates has a
unique ray scale. Its affine-level equation is exactly `weightedExpLevel`. -/
theorem exists_scale_of_sectionPoint_coordinates (b y : ι → ℝ) {a : ℝ} {i₀ : ι}
    (x : ι → ℝ) (hxpos : ∀ i, 0 < x i) (hxbase : x i₀ < 1)
    (hxlevel : (∑ i, b i * x i) = a * (∑ i, b i))
    (hxcoords : ∀ i, Real.log (x i) / Real.log (x i₀) = y i) :
    ∃ t : ℝ, 0 < t ∧ x = sectionPoint y t ∧
      weightedExpLevel b y t = a * (∑ i, b i) := by
  have hlogbase : Real.log (x i₀) < 0 := Real.log_neg (hxpos i₀) hxbase
  let t : ℝ := -Real.log (x i₀)
  have ht : 0 < t := by dsimp [t]; exact neg_pos.mpr hlogbase
  have hpoint : ∀ i, x i = sectionPoint y t i := by
    intro i
    have hlogeq : Real.log (x i) = y i * Real.log (x i₀) := by
      calc
        Real.log (x i) =
            (Real.log (x i) / Real.log (x i₀)) * Real.log (x i₀) := by
              field_simp [ne_of_lt hlogbase]
        _ = y i * Real.log (x i₀) := by rw [hxcoords i]
    calc
      x i = Real.exp (Real.log (x i)) := (Real.exp_log (hxpos i)).symm
      _ = Real.exp (-(t * y i)) := by
        congr 1
        rw [hlogeq]
        dsimp [t]
        ring
      _ = sectionPoint y t i := rfl
  have hroot : weightedExpLevel b y t = a * (∑ i, b i) := by
    calc
      weightedExpLevel b y t = ∑ i, b i * sectionPoint y t i := by
        simp [weightedExpLevel, sectionPoint]
      _ = ∑ i, b i * x i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [(hpoint i).symm]
      _ = a * (∑ i, b i) := hxlevel
  exact ⟨t, ht, funext hpoint, hroot⟩

/-- The positive affine section has exactly one point with any prescribed positive normalized
logarithmic projective coordinates. Thus each individual face plane in the blueprint chart has a
set-theoretic inverse, before gluing neighboring faces. -/
theorem existsUnique_sectionPoint_with_coordinates (b y : ι → ℝ) {a : ℝ} {i₀ : ι}
    (hb : ∀ i, 0 ≤ b i) (hbsum : 0 < ∑ i, b i)
    (hy : ∀ i, 0 < y i) (hy₀ : y i₀ = 1)
    (ha0 : 0 < a) (ha1 : a < 1) :
    ∃! x : ι → ℝ,
      (∀ i, 0 < x i ∧ x i < 1) ∧
      (∑ i, b i * x i) = a * (∑ i, b i) ∧
      (∀ i, Real.log (x i) / Real.log (x i₀) = y i) := by
  obtain ⟨t, ⟨ht, hlevel⟩, hunique⟩ :=
    existsUnique_sectionScale_of_positive b y hb hbsum hy ha0 ha1
  let x := sectionPoint y t
  have hx :
      (∀ i, 0 < x i ∧ x i < 1) ∧
      (∑ i, b i * x i) = a * (∑ i, b i) ∧
      (∀ i, Real.log (x i) / Real.log (x i₀) = y i) := by
    refine ⟨?_, sectionPoint_mem_level b y hlevel, ?_⟩
    · intro i
      constructor
      · exact Real.exp_pos _
      · apply (Real.exp_lt_one_iff).2
        have hty : 0 < t * y i := mul_pos ht (hy i)
        linarith
    · intro i
      exact sectionPoint_logProjective y ht hy₀ i
  refine ⟨x, hx, ?_⟩
  intro z hz
  obtain ⟨u, hu, hzu, huroot⟩ := exists_scale_of_sectionPoint_coordinates
    b y z (fun i => (hz.1 i).1) (hz.1 i₀ |>.2)
    hz.2.1 hz.2.2
  have hut : u = t := hunique u ⟨hu, huroot⟩
  rw [hzu, hut]

end LogProjectiveSection
end CRNT
