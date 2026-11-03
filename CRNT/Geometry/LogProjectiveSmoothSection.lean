import CRNT.Geometry.LogProjectiveSection
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Smooth local sections of logarithmic projective rays

The pointwise inverse in `LogProjectiveSection` is governed by a scalar affine-level equation.
Its derivative in the ray-scale direction is strictly negative, so the implicit function theorem
applies locally to the normalized projective coordinates.
-/

namespace CRNT
namespace LogProjectiveSection

open Filter Set
open scoped ContDiff Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Projective coordinates with the distinguished coordinate fixed to one. -/
noncomputable def normalizedCoordinates (i₀ : ι)
    (z : ({i : ι // i ≠ i₀} → ℝ)) : ι → ℝ := by
  classical
  exact fun i => if h : i = i₀ then 1 else z ⟨i, h⟩

/-- The affine-level equation whose local solution is the ray scale. -/
noncomputable def sectionEquation (b : ι → ℝ) (a : ℝ) (i₀ : ι)
    (p : ({i : ι // i ≠ i₀} → ℝ) × ℝ) : ℝ :=
  weightedExpLevel b (normalizedCoordinates i₀ p.1) p.2 - a * (∑ i, b i)

/-- The affine-level equation is smooth in all normalized ray coordinates and the scale. -/
theorem contDiff_sectionEquation (b : ι → ℝ) (a : ℝ) (i₀ : ι) :
    ContDiff ℝ ∞ (sectionEquation b a i₀) := by
  classical
  have hcoords : ContDiff ℝ ∞
      (fun p : (({i : ι // i ≠ i₀} → ℝ) × ℝ) => normalizedCoordinates i₀ p.1) := by
    apply contDiff_pi.2
    intro i
    by_cases hi : i = i₀
    · simp [normalizedCoordinates, hi]
      exact contDiff_const
    · simp [normalizedCoordinates, hi]
      fun_prop
  have hpre : ContDiff ℝ ∞
      (fun p : (({i : ι // i ≠ i₀} → ℝ) × ℝ) =>
        (normalizedCoordinates i₀ p.1, p.2)) := by
    exact hcoords.prodMk contDiff_snd
  have hlevel : ContDiff ℝ ∞
      (fun q : ((ι → ℝ) × ℝ) =>
        weightedExpLevel b q.1 q.2 - a * (∑ i, b i)) := by
    unfold weightedExpLevel
    fun_prop
  exact hlevel.comp hpre

omit [DecidableEq ι] in
/-- Derivative of the weighted exponential level along its scale coordinate. -/
theorem hasDerivAt_weightedExpLevel (b y : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s => weightedExpLevel b y s)
      (∑ i, b i * Real.exp (-(t * y i)) * (-y i)) t := by
  unfold weightedExpLevel
  apply HasDerivAt.fun_sum
  intro i hi
  have hinner : HasDerivAt (fun s : ℝ => -(s * y i)) (-(y i)) t := by
    convert (hasDerivAt_id t).mul_const (-(y i)) using 1
    · funext s
      simp only [id_eq]
      ring
    · ring
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(s * y i)))
      (Real.exp (-(t * y i)) * (-(y i))) t := by
    simpa using hinner.exp
  convert HasDerivAt.const_mul (b i) hexp using 1; ring

omit [DecidableEq ι] in
/-- With nonnegative weights and positive ray coordinates, the scale derivative is strictly
negative whenever the total weight is positive. -/
theorem weightedExpLevel_scale_deriv_neg (b y : ι → ℝ) (t : ℝ)
    (hb : ∀ i, 0 ≤ b i) (hbsum : 0 < ∑ i, b i) (hy : ∀ i, 0 < y i) :
    (∑ i, b i * Real.exp (-(t * y i)) * (-y i)) < 0 := by
  have hpositiveTerm : ∃ i, 0 < b i := by
    by_contra h
    have hall : ∀ i, b i ≤ 0 := fun i => le_of_not_gt (fun hi => h ⟨i, hi⟩)
    have hsumle : ∑ i, b i ≤ 0 := by
      calc
        (∑ i, b i) ≤ ∑ i, (0 : ℝ) := Finset.sum_le_sum (fun i _ => hall i)
        _ = 0 := by simp
    linarith
  obtain ⟨i₀, hi₀⟩ := hpositiveTerm
  have hsumlt :
      (∑ i, b i * Real.exp (-(t * y i)) * (-y i)) < ∑ i : ι, (0 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro i _
      have hnonneg : 0 ≤ b i * Real.exp (-(t * y i)) :=
        mul_nonneg (hb i) (Real.exp_pos _).le
      exact mul_nonpos_of_nonneg_of_nonpos hnonneg (neg_nonpos.mpr (hy i).le)
    · refine ⟨i₀, Finset.mem_univ _, ?_⟩
      exact mul_neg_of_pos_of_neg (mul_pos hi₀ (Real.exp_pos _)) (neg_neg_of_pos (hy i₀))
  simpa using hsumlt

omit [Fintype ι] in
/-- The normalized-coordinate family recovers its base point when the distinguished coordinate is
one. -/
theorem normalizedCoordinates_eq_of_anchor (i₀ : ι) (y : ι → ℝ) (hy₀ : y i₀ = 1) :
    normalizedCoordinates i₀ (fun j : {i : ι // i ≠ i₀} => y j) = y := by
  classical
  funext i
  by_cases hi : i = i₀
  · subst i
    simp [normalizedCoordinates, hy₀]
  · simp [normalizedCoordinates, hi]

/-- The unique section scale varies smoothly near every positive projective ray. The local implicit
branch agrees with the pointwise unique positive scale wherever the nearby coordinates remain
positive. This gives a smooth local inverse for each individual affine section; it says nothing
about gluing different tile faces. -/
theorem exists_contDiff_local_sectionScale (b y : ι → ℝ) {a : ℝ} {i₀ : ι}
    (hb : ∀ i, 0 ≤ b i) (hbsum : 0 < ∑ i, b i)
    (hy : ∀ i, 0 < y i) (hy₀ : y i₀ = 1)
    (ha0 : 0 < a) (ha1 : a < 1) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hroot : weightedExpLevel b y t₀ = a * (∑ i, b i)) :
    ∃ ψ : ({i : ι // i ≠ i₀} → ℝ) → ℝ,
      ContDiffAt ℝ ∞ ψ (fun j : {i : ι // i ≠ i₀} => y j) ∧
      ψ (fun j : {i : ι // i ≠ i₀} => y j) = t₀ ∧
      ∀ᶠ z in 𝓝 (fun j : {i : ι // i ≠ i₀} => y j),
        0 < ψ z ∧
        weightedExpLevel b (normalizedCoordinates i₀ z) (ψ z) = a * (∑ i, b i) ∧
        ((∀ i, 0 < normalizedCoordinates i₀ z i) →
          ∃! s : ℝ,
            (0 < s ∧ weightedExpLevel b (normalizedCoordinates i₀ z) s =
              a * (∑ i, b i)) ∧ s = ψ z) := by
  classical
  let z₀ : ({i : ι // i ≠ i₀} → ℝ) := fun j => y j
  let f := sectionEquation b a i₀
  have hcoords : normalizedCoordinates i₀ z₀ = y :=
    normalizedCoordinates_eq_of_anchor i₀ y hy₀
  have hF : ContDiffAt ℝ ∞ f (z₀, t₀) := by
    dsimp [f]
    exact (contDiff_sectionEquation b a i₀).contDiffAt
  have hFzero : f (z₀, t₀) = 0 := by
    simp [f, sectionEquation, hcoords, hroot]
  let d : ℝ := ∑ i, b i * Real.exp (-(t₀ * y i)) * (-y i)
  have hd : d < 0 := by
    exact weightedExpLevel_scale_deriv_neg b y t₀ hb hbsum hy
  have hslice : HasDerivAt (fun s : ℝ => f (z₀, s)) d t₀ := by
    have hlevel := (hasDerivAt_weightedExpLevel b y t₀).sub_const
      (a * (∑ i, b i))
    have hfun :
        (fun s : ℝ => f (z₀, s)) =
          (fun s => weightedExpLevel b y s - a * (∑ i, b i)) := by
      funext s
      simp [f, sectionEquation, hcoords]
    rw [hfun]
    simpa [d] using hlevel
  let L : ℝ →L[ℝ] ℝ := (fderiv ℝ f (z₀, t₀)) ∘L ContinuousLinearMap.inr ℝ _ ℝ
  have hcomp : HasFDerivAt (fun s : ℝ => f (z₀, s)) L t₀ := by
    have hFdiff : DifferentiableAt ℝ f (z₀, t₀) :=
      (hF.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)).differentiableAt_one
    have hFderiv : HasFDerivAt f (fderiv ℝ f (z₀, t₀)) (z₀, t₀) :=
      hFdiff.hasFDerivAt
    simpa [L, Function.comp_def] using
      hFderiv.comp t₀ (hasFDerivAt_prodMk_right z₀ t₀)
  have hLd : L 1 = d := hcomp.hasDerivAt.unique hslice
  have hLform : L = d • ContinuousLinearMap.id ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro x
    calc
      L x = L (x • (1 : ℝ)) := by simp
      _ = x • L 1 := map_smul L x 1
      _ = x * d := by rw [hLd]; simp [smul_eq_mul]
      _ = (d • ContinuousLinearMap.id ℝ ℝ) x := by simp [smul_eq_mul, mul_comm]
  have hLinvertible : L.IsInvertible := by
    refine ContinuousLinearMap.IsInvertible.of_inverse
      (g := d⁻¹ • ContinuousLinearMap.id ℝ ℝ) ?_ ?_
    · apply ContinuousLinearMap.ext
      intro x
      simp [hLform, ne_of_lt hd]
    · apply ContinuousLinearMap.ext
      intro x
      simp [hLform, ne_of_lt hd]
  let ψ := hF.implicitFunction (by norm_num) hLinvertible
  have hψsmooth : ContDiffAt ℝ ∞ ψ z₀ := by
    simpa [ψ] using hF.contDiffAt_implicitFunction (by norm_num) hLinvertible
  have hψbase : ψ z₀ = t₀ := by
    simpa [ψ] using hF.implicitFunction_apply_self (by norm_num) hLinvertible
  have hψpositive : ∀ᶠ z in 𝓝 z₀, 0 < ψ z := by
    have hψtendsto : Tendsto ψ (𝓝 z₀) (𝓝 t₀) := by
      simpa [hψbase] using hψsmooth.continuousAt.tendsto
    exact hψtendsto.eventually (Ioi_mem_nhds ht₀)
  have hψequation : ∀ᶠ z in 𝓝 z₀, f (z, ψ z) = 0 := by
    filter_upwards [hF.eventually_apply_implicitFunction (by norm_num) hLinvertible]
      with z hz
    rw [hFzero] at hz
    exact hz
  have hscaleBranch : ∀ᶠ z in 𝓝 z₀,
      0 < ψ z ∧
      weightedExpLevel b (normalizedCoordinates i₀ z) (ψ z) = a * (∑ i, b i) ∧
      ((∀ i, 0 < normalizedCoordinates i₀ z i) →
        ∃! s : ℝ,
          (0 < s ∧ weightedExpLevel b (normalizedCoordinates i₀ z) s =
            a * (∑ i, b i)) ∧ s = ψ z) := by
    filter_upwards [hψpositive, hψequation] with z hpos heq
    have hlevel : weightedExpLevel b (normalizedCoordinates i₀ z) (ψ z) =
        a * (∑ i, b i) := by
      have heq' : weightedExpLevel b (normalizedCoordinates i₀ z) (ψ z) -
          a * (∑ i, b i) = 0 := by
        simpa [f, sectionEquation] using heq
      exact sub_eq_zero.mp heq'
    refine ⟨hpos, hlevel, ?_⟩
    intro hzcoords
    obtain ⟨s, hs, hunique⟩ := existsUnique_sectionScale_of_positive b
      (normalizedCoordinates i₀ z) hb hbsum hzcoords ha0 ha1
    have hbranch : ψ z = s := hunique (ψ z) ⟨hpos, hlevel⟩
    refine ⟨s, ⟨hs, hbranch.symm⟩, ?_⟩
    intro u hu
    calc
      u = ψ z := hu.2
      _ = s := hbranch
  refine ⟨ψ, hψsmooth, ?_, hscaleBranch⟩
  simpa [z₀] using hψbase

/-- The canonical positive section scale on normalized coordinates with positive entries. It is
totalized by zero outside that open coordinate domain. -/
noncomputable def positiveSectionScale (b : ι → ℝ) (a : ℝ) (i₀ : ι)
    (hb : ∀ i, 0 ≤ b i) (hbsum : 0 < ∑ i, b i) (ha0 : 0 < a) (ha1 : a < 1)
    (z : ({i : ι // i ≠ i₀} → ℝ)) : ℝ := by
  classical
  exact if hz : ∀ i, 0 < normalizedCoordinates i₀ z i then
    Classical.choose
      (existsUnique_sectionScale_of_positive b (normalizedCoordinates i₀ z)
        hb hbsum hz ha0 ha1).exists
  else 0

/-- On its positive-coordinate domain, the canonical section scale is the unique positive root of
the affine-level equation. -/
theorem positiveSectionScale_spec (b : ι → ℝ) (a : ℝ) (i₀ : ι)
    (hb : ∀ i, 0 ≤ b i) (hbsum : 0 < ∑ i, b i) (ha0 : 0 < a) (ha1 : a < 1)
    (z : ({i : ι // i ≠ i₀} → ℝ))
    (hz : ∀ i, 0 < normalizedCoordinates i₀ z i) :
    0 < positiveSectionScale b a i₀ hb hbsum ha0 ha1 z ∧
      weightedExpLevel b (normalizedCoordinates i₀ z)
        (positiveSectionScale b a i₀ hb hbsum ha0 ha1 z) = a * (∑ i, b i) := by
  classical
  rw [positiveSectionScale, dite_eq_left hz]
  exact Classical.choose_spec
    (existsUnique_sectionScale_of_positive b (normalizedCoordinates i₀ z)
      hb hbsum hz ha0 ha1).exists

/-- The canonical section scale is smooth at every normalized ray with positive coordinates. Its
local implicit branches agree with the globally chosen root by uniqueness. -/
theorem contDiffAt_positiveSectionScale (b : ι → ℝ) (a : ℝ) (i₀ : ι)
    (hb : ∀ i, 0 ≤ b i) (hbsum : 0 < ∑ i, b i) (ha0 : 0 < a) (ha1 : a < 1)
    (z : ({i : ι // i ≠ i₀} → ℝ))
    (hz : ∀ i, 0 < normalizedCoordinates i₀ z i) :
    ContDiffAt ℝ ∞ (positiveSectionScale b a i₀ hb hbsum ha0 ha1) z := by
  classical
  let y := normalizedCoordinates i₀ z
  have hy : ∀ i, 0 < y i := by
    intro i
    exact hz i
  have hy₀ : y i₀ = 1 := by simp [y, normalizedCoordinates]
  have hroot := positiveSectionScale_spec b a i₀ hb hbsum ha0 ha1 z hz
  obtain ⟨ψ, hψsmooth, hψbase, hψbranch⟩ :=
    exists_contDiff_local_sectionScale b y hb hbsum hy hy₀ ha0 ha1
      (t₀ := positiveSectionScale b a i₀ hb hbsum ha0 ha1 z) hroot.1 hroot.2
  have hcoords : (fun j : {i : ι // i ≠ i₀} => y j) = z := by
    funext j
    simp [y, normalizedCoordinates, j.property]
  rw [hcoords] at hψsmooth hψbase hψbranch
  have hcoordinate : ∀ i, ContinuousAt
      (fun w : ({i : ι // i ≠ i₀} → ℝ) => normalizedCoordinates i₀ w i) z := by
    intro i
    by_cases hi : i = i₀
    · simpa [normalizedCoordinates, hi] using
        (continuousAt_const (x := z) :
          ContinuousAt (fun _ : ({i : ι // i ≠ i₀} → ℝ) => (1 : ℝ)) z)
    · simpa [normalizedCoordinates, hi] using
        (continuousAt_apply (⟨i, hi⟩ : {i : ι // i ≠ i₀}) z)
  have hcoordsNear : ∀ᶠ w in 𝓝 z, ∀ i, 0 < normalizedCoordinates i₀ w i := by
    simpa only [Filter.Eventually, Set.ofPred_forall] using
      (Filter.iInter_mem.2 fun i =>
        (hcoordinate i).eventually (Ioi_mem_nhds (hz i)))
  have heq :
      positiveSectionScale b a i₀ hb hbsum ha0 ha1 =ᶠ[𝓝 z] ψ := by
    filter_upwards [hcoordsNear, hψbranch] with w hwcoords hbranch
    obtain ⟨hψpos, hψlevel, _⟩ := hbranch
    have hglobal := positiveSectionScale_spec b a i₀ hb hbsum ha0 ha1 w hwcoords
    obtain ⟨t, ht, hunique⟩ := existsUnique_sectionScale_of_positive b
      (normalizedCoordinates i₀ w) hb hbsum hwcoords ha0 ha1
    calc
      positiveSectionScale b a i₀ hb hbsum ha0 ha1 w = t := hunique _ hglobal
      _ = ψ w := (hunique _ ⟨hψpos, hψlevel⟩).symm
  exact hψsmooth.congr_of_eventuallyEq heq

/-- The canonical section scale is smooth on the open domain of positive normalized coordinates. -/
theorem contDiffOn_positiveSectionScale (b : ι → ℝ) (a : ℝ) (i₀ : ι)
    (hb : ∀ i, 0 ≤ b i) (hbsum : 0 < ∑ i, b i) (ha0 : 0 < a) (ha1 : a < 1) :
    ContDiffOn ℝ ∞ (positiveSectionScale b a i₀ hb hbsum ha0 ha1)
      {z | ∀ i, 0 < normalizedCoordinates i₀ z i} := by
  intro z hz
  exact (contDiffAt_positiveSectionScale b a i₀ hb hbsum ha0 ha1 z hz).contDiffWithinAt

/-- The canonical positive representative on the affine section for a normalized positive
projective ray. -/
noncomputable def positiveSectionPoint (b : ι → ℝ) (a : ℝ) (i₀ : ι)
    (hb : ∀ i, 0 ≤ b i) (hbsum : 0 < ∑ i, b i) (ha0 : 0 < a) (ha1 : a < 1)
    (z : ({i : ι // i ≠ i₀} → ℝ)) : ι → ℝ :=
  sectionPoint (normalizedCoordinates i₀ z)
    (positiveSectionScale b a i₀ hb hbsum ha0 ha1 z)

/-- The canonical point is smooth on the domain of positive normalized coordinates. -/
theorem contDiffAt_positiveSectionPoint (b : ι → ℝ) (a : ℝ) (i₀ : ι)
    (hb : ∀ i, 0 ≤ b i) (hbsum : 0 < ∑ i, b i) (ha0 : 0 < a) (ha1 : a < 1)
    (z : ({i : ι // i ≠ i₀} → ℝ))
    (hz : ∀ i, 0 < normalizedCoordinates i₀ z i) :
    ContDiffAt ℝ ∞ (positiveSectionPoint b a i₀ hb hbsum ha0 ha1) z := by
  classical
  have hcoords : ContDiff ℝ ∞
      (fun w : ({i : ι // i ≠ i₀} → ℝ) => normalizedCoordinates i₀ w) := by
    apply contDiff_pi.2
    intro i
    by_cases hi : i = i₀
    · simp [normalizedCoordinates, hi]
      exact contDiff_const
    · simp [normalizedCoordinates, hi]
      fun_prop
  have hscale := contDiffAt_positiveSectionScale b a i₀ hb hbsum ha0 ha1 z hz
  have hpair : ContDiffAt ℝ ∞
      (fun w => (normalizedCoordinates i₀ w,
        positiveSectionScale b a i₀ hb hbsum ha0 ha1 w)) z :=
    hcoords.contDiffAt.prodMk hscale
  have hsection : ContDiff ℝ ∞
      (fun p : ((ι → ℝ) × ℝ) => sectionPoint p.1 p.2) := by
    apply contDiff_pi.2
    intro i
    unfold sectionPoint
    fun_prop
  change ContDiffAt ℝ ∞
    (fun w => sectionPoint (normalizedCoordinates i₀ w)
      (positiveSectionScale b a i₀ hb hbsum ha0 ha1 w)) z
  exact hsection.contDiffAt.comp z hpair

/-- The canonical smooth point lies on the requested positive affine section and recovers the
normalized logarithmic projective coordinates. -/
theorem positiveSectionPoint_spec (b : ι → ℝ) (a : ℝ) (i₀ : ι)
    (hb : ∀ i, 0 ≤ b i) (hbsum : 0 < ∑ i, b i) (ha0 : 0 < a) (ha1 : a < 1)
    (z : ({i : ι // i ≠ i₀} → ℝ))
    (hz : ∀ i, 0 < normalizedCoordinates i₀ z i) :
    (∀ i, 0 < positiveSectionPoint b a i₀ hb hbsum ha0 ha1 z i ∧
      positiveSectionPoint b a i₀ hb hbsum ha0 ha1 z i < 1) ∧
    (∑ i, b i * positiveSectionPoint b a i₀ hb hbsum ha0 ha1 z i) =
      a * (∑ i, b i) ∧
    (∀ i, Real.log (positiveSectionPoint b a i₀ hb hbsum ha0 ha1 z i) /
      Real.log (positiveSectionPoint b a i₀ hb hbsum ha0 ha1 z i₀) =
        normalizedCoordinates i₀ z i) := by
  have hscale := positiveSectionScale_spec b a i₀ hb hbsum ha0 ha1 z hz
  refine ⟨?_, ?_, ?_⟩
  · intro i
    constructor
    · exact Real.exp_pos _
    · apply (Real.exp_lt_one_iff).2
      have hty : 0 < positiveSectionScale b a i₀ hb hbsum ha0 ha1 z *
          normalizedCoordinates i₀ z i := mul_pos hscale.1 (hz i)
      linarith
  · simpa [positiveSectionPoint] using
      (sectionPoint_mem_level b (normalizedCoordinates i₀ z) hscale.2)
  · intro i
    simpa [positiveSectionPoint] using
      (sectionPoint_logProjective (normalizedCoordinates i₀ z) hscale.1
        (by simp [normalizedCoordinates]) i)

/-- The smooth positive representative is the unique point of its affine section having the
specified normalized logarithmic projective coordinates. -/
theorem positiveSectionPoint_unique (b : ι → ℝ) (a : ℝ) (i₀ : ι)
    (hb : ∀ i, 0 ≤ b i) (hbsum : 0 < ∑ i, b i) (ha0 : 0 < a) (ha1 : a < 1)
    (z : ({i : ι // i ≠ i₀} → ℝ))
    (hz : ∀ i, 0 < normalizedCoordinates i₀ z i)
    (x : ι → ℝ)
    (hx : (∀ i, 0 < x i ∧ x i < 1) ∧
      (∑ i, b i * x i) = a * (∑ i, b i) ∧
      (∀ i, Real.log (x i) / Real.log (x i₀) = normalizedCoordinates i₀ z i)) :
    x = positiveSectionPoint b a i₀ hb hbsum ha0 ha1 z := by
  have hcoords : normalizedCoordinates i₀ z i₀ = 1 := by
    simp [normalizedCoordinates]
  obtain ⟨xstar, _, hunique⟩ := existsUnique_sectionPoint_with_coordinates b
    (normalizedCoordinates i₀ z) (a := a) (i₀ := i₀)
    hb hbsum hz hcoords ha0 ha1
  have hpoint := positiveSectionPoint_spec b a i₀ hb hbsum ha0 ha1 z hz
  exact (hunique x hx).trans (hunique _ hpoint).symm

end LogProjectiveSection
end CRNT
