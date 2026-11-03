import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Linear norm-constraint sets

The multi-linkage-class Brouwer construction for weakly reversible existence uses a compact
convex set cut out by finitely many norm bounds on linear projections.  This module isolates the
geometric fact needed for such a domain: any intersection of inverse images of centered balls is
convex and closed, and it is compact as soon as one constraint bounds the whole ambient vector.
The network-specific projection decomposition and inward-pointing estimates remain separate.
-/

namespace CRNT.Analysis

open Set

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Intersection of norm constraints on continuous linear images. -/
def projectionConstraintSet (T : ι → E →L[ℝ] E) (r : ι → ℝ) : Set E :=
  {x | ∀ i, ‖T i x‖ ≤ r i}

/-- The points satisfying every projection constraint strictly. For finite index types this is the
relative-interior region of the corresponding closed constraint set. -/
def strictProjectionConstraintSet (T : ι → E →L[ℝ] E) (r : ι → ℝ) : Set E :=
  {x | ∀ i, ‖T i x‖ < r i}

/-- The strict projection constraints form an open set when the family is finite. -/
theorem isOpen_strictProjectionConstraintSet [Finite ι]
    (T : ι → E →L[ℝ] E) (r : ι → ℝ) :
    IsOpen (strictProjectionConstraintSet T r) := by
  rw [show strictProjectionConstraintSet T r =
      ⋂ i, {x : E | ‖T i x‖ < r i} by
    ext x
    simp [strictProjectionConstraintSet]]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt ((continuous_norm).comp (T i).continuous) continuous_const

/-- Every point with strict projection constraints is an interior point of the closed constraint
set. -/
theorem mem_interior_projectionConstraintSet_of_strict [Finite ι]
    (T : ι → E →L[ℝ] E) (r : ι → ℝ) {x : E}
    (hx : x ∈ strictProjectionConstraintSet T r) :
    x ∈ interior (projectionConstraintSet T r) := by
  apply mem_interior.mpr
  refine ⟨strictProjectionConstraintSet T r, ?_, isOpen_strictProjectionConstraintSet T r, hx⟩
  intro y hy i
  exact (hy i).le

/-- Centered projection constraints are convex. -/
theorem convex_projectionConstraintSet (T : ι → E →L[ℝ] E) (r : ι → ℝ) :
    Convex ℝ (projectionConstraintSet T r) := by
  intro x hx y hy a b ha hb hab i
  calc
    ‖T i (a • x + b • y)‖ = ‖a • T i x + b • T i y‖ := by simp
    _ ≤ ‖a • T i x‖ + ‖b • T i y‖ := norm_add_le _ _
    _ = a * ‖T i x‖ + b * ‖T i y‖ := by
      rw [norm_smul_of_nonneg ha, norm_smul_of_nonneg hb]
    _ ≤ a * r i + b * r i := add_le_add
      (mul_le_mul_of_nonneg_left (hx i) ha)
      (mul_le_mul_of_nonneg_left (hy i) hb)
    _ = r i := by rw [← add_mul, hab, one_mul]

/-- The constraint set is closed, as each norm bound is a closed condition. -/
theorem isClosed_projectionConstraintSet (T : ι → E →L[ℝ] E) (r : ι → ℝ) :
    IsClosed (projectionConstraintSet T r) := by
  rw [show projectionConstraintSet T r =
      ⋂ i, {x : E | ‖T i x‖ ≤ r i} by
    ext x
    simp [projectionConstraintSet]]
  apply isClosed_iInter
  intro i
  exact isClosed_le ((continuous_norm).comp (T i).continuous) continuous_const

/-- Nonnegative radii make the common origin a point of the constraint set. -/
theorem zero_mem_projectionConstraintSet (T : ι → E →L[ℝ] E) (r : ι → ℝ)
    (hr : ∀ i, 0 ≤ r i) :
    (0 : E) ∈ projectionConstraintSet T r := by
  intro i
  simp [hr i]

/-- Nonempty subsets of a finite set, used as the facet indices for Boros's nested domain. -/
abbrev BorosSubsetIndex (I : Type*) [Fintype I] [DecidableEq I] :=
  {Q : Finset I // Q.Nonempty}

/-- Radius of the constraint indexed by a nonempty class subset `Q` in Boros's nested domain.
Here `r` is the increasing sequence of radii selected in the inductive boundary estimate. -/
noncomputable def borosProjectionRadius {I : Type*} [Fintype I] [DecidableEq I]
    (r : ℕ → ℝ) (Q : BorosSubsetIndex I) : ℝ :=
  Real.sqrt ((r (Fintype.card I)) ^ 2 -
    (r (Fintype.card I - Q.1.card)) ^ 2)

/-- The finite-subset version of the Boros domain, cut out by the projection bounds
`‖P_Q z‖ ≤ sqrt(r_ℓ² - r_(ℓ-|Q|)²)`. -/
noncomputable def borosNestedProjectionDomain {I : Type*} [Fintype I] [DecidableEq I]
    (P : BorosSubsetIndex I → E →L[ℝ] E) (r : ℕ → ℝ) : Set E :=
  projectionConstraintSet P (borosProjectionRadius r)

/-- Every Boros subset radius is nonnegative. -/
theorem borosProjectionRadius_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    (r : ℕ → ℝ) (Q : BorosSubsetIndex I) :
    0 ≤ borosProjectionRadius r Q :=
  Real.sqrt_nonneg _

/-- Monotone nonnegative nested radii make every radicand in the Boros bound nonnegative. -/
theorem borosProjectionRadius_radicand_nonneg
    {I : Type*} [Fintype I] [DecidableEq I]
    (r : ℕ → ℝ) (hrmono : Monotone r) (hrnonneg : ∀ k, 0 ≤ r k)
    (Q : BorosSubsetIndex I) :
    0 ≤ (r (Fintype.card I)) ^ 2 -
      (r (Fintype.card I - Q.1.card)) ^ 2 := by
  have hcard : Q.1.card ≤ Fintype.card I := by
    calc
      Q.1.card ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card I := by simp
  have hsub : Fintype.card I - Q.1.card ≤ Fintype.card I := Nat.sub_le _ _
  have hlo : 0 ≤ r (Fintype.card I - Q.1.card) := hrnonneg _
  have hhi : 0 ≤ r (Fintype.card I) := hrnonneg _
  have horder : r (Fintype.card I - Q.1.card) ≤ r (Fintype.card I) := hrmono hsub
  have hsum : 0 ≤ r (Fintype.card I - Q.1.card) + r (Fintype.card I) :=
    add_nonneg hlo hhi
  have hprod : 0 ≤
      (r (Fintype.card I) - r (Fintype.card I - Q.1.card)) *
        (r (Fintype.card I) + r (Fintype.card I - Q.1.card)) :=
    mul_nonneg (sub_nonneg.mpr horder) (by linarith)
  nlinarith [hprod]

/-- When the nested radii start at zero, the full-subset radius is exactly the outer radius. -/
theorem borosProjectionRadius_univ
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (r : ℕ → ℝ) (hr0 : r 0 = 0) (hrtop : 0 ≤ r (Fintype.card I)) :
    borosProjectionRadius r (⟨(Finset.univ : Finset I), by simp⟩ : BorosSubsetIndex I) =
      r (Fintype.card I) := by
  simp [borosProjectionRadius, hr0, Real.sqrt_sq_eq_abs, abs_of_nonneg hrtop]

/-- The origin belongs to every Boros nested projection domain. -/
theorem zero_mem_borosNestedProjectionDomain {I : Type*} [Fintype I] [DecidableEq I]
    (P : BorosSubsetIndex I → E →L[ℝ] E) (r : ℕ → ℝ) :
    (0 : E) ∈ borosNestedProjectionDomain P r := by
  apply zero_mem_projectionConstraintSet
  exact borosProjectionRadius_nonneg r

/-- If one projection is the identity, its radius bounds the entire constraint set. Since `E` is
finite dimensional, closedness then yields compactness. -/
theorem isCompact_projectionConstraintSet_of_identity
    [FiniteDimensional ℝ E] (T : ι → E →L[ℝ] E) (r : ι → ℝ) (i₀ : ι)
    (hid : T i₀ = ContinuousLinearMap.id ℝ E) :
    IsCompact (projectionConstraintSet T r) := by
  have hsubset : projectionConstraintSet T r ⊆ Metric.closedBall (0 : E) (r i₀) := by
    intro x hx
    change dist x 0 ≤ r i₀
    rw [dist_zero_right]
    simpa [hid] using hx i₀
  exact (isCompact_closedBall (0 : E) (r i₀)).of_isClosed_subset
    (isClosed_projectionConstraintSet T r) hsubset

/-- The full-subset constraint bounds the Boros domain by a closed ball, so the nested domain is
compact in finite dimensions. -/
theorem isCompact_borosNestedProjectionDomain
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [FiniteDimensional ℝ E]
    (P : BorosSubsetIndex I → E →L[ℝ] E) (r : ℕ → ℝ)
    (hPtop : P (⟨(Finset.univ : Finset I), by simp⟩ : BorosSubsetIndex I) =
      ContinuousLinearMap.id ℝ E) :
    IsCompact (borosNestedProjectionDomain P r) := by
  let qtop : BorosSubsetIndex I := ⟨(Finset.univ : Finset I), by simp⟩
  unfold borosNestedProjectionDomain
  exact isCompact_projectionConstraintSet_of_identity P
    (borosProjectionRadius r) qtop (by simpa [qtop] using hPtop)

/-- An injective linear coordinate observation on a finite-dimensional space has a uniform
positive lower norm bound. This is the quantitative finite-dimensional step used in Boros's
linkage-subset decomposition: a component projection that is injective on the residual subspace
cannot shrink vectors there by an arbitrarily large factor. -/
theorem exists_positive_norm_lower_bound_of_injective
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] (f : E →ₗ[ℝ] F) (hinj : Function.Injective f) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, ε * ‖x‖ ≤ ‖f x‖ := by
  obtain ⟨ε, hε, hanti⟩ := (LinearMap.injective_iff_antilipschitz f).mp hinj
  have hε' : 0 < (ε⁻¹ : NNReal) := inv_pos.mpr hε
  refine ⟨(ε⁻¹ : NNReal), by exact_mod_cast hε', ?_⟩
  intro x
  have h := hanti.mul_le_nndist x 0
  have h' : (ε⁻¹ : NNReal) * ‖x‖₊ ≤ ‖f x‖₊ := by simpa using h
  exact_mod_cast h'

/-- The same lower bound for an injective observation restricted to a finite-dimensional
subspace. This is the form needed when Boros's coordinate projection is restricted to the
orthogonal residual space in a linkage-subset decomposition. -/
theorem exists_positive_norm_lower_bound_on_submodule
    {V : Submodule ℝ E} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] (f : E →ₗ[ℝ] F)
    (hinj : Function.Injective (fun x : V => f x.1)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, x ∈ V → ε * ‖x‖ ≤ ‖f x‖ := by
  let fV : V →ₗ[ℝ] F := f.comp V.subtype
  have hinjV : Function.Injective fV := by
    intro x y h
    apply Subtype.ext
    exact congrArg Subtype.val (hinj (a₁ := x) (a₂ := y) (by simpa [fV] using h))
  obtain ⟨ε, hε, hbound⟩ := exists_positive_norm_lower_bound_of_injective fV hinjV
  refine ⟨ε, hε, ?_⟩
  intro x hx
  exact hbound ⟨x, hx⟩

/-- The geometric package consumed by a compact-convex existence argument: the nested Boros
domain is nonempty, convex, and compact when its full-subset constraint is the identity bound. -/
theorem borosNestedProjectionDomain_compactConvex_nonempty
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [FiniteDimensional ℝ E]
    (P : BorosSubsetIndex I → E →L[ℝ] E) (r : ℕ → ℝ)
    (hPtop : P (⟨(Finset.univ : Finset I), by simp⟩ : BorosSubsetIndex I) =
      ContinuousLinearMap.id ℝ E) :
    (borosNestedProjectionDomain P r).Nonempty ∧
      Convex ℝ (borosNestedProjectionDomain P r) ∧
      IsCompact (borosNestedProjectionDomain P r) := by
  refine ⟨⟨0, zero_mem_borosNestedProjectionDomain P r⟩,
    ?_, isCompact_borosNestedProjectionDomain P r hPtop⟩
  exact convex_projectionConstraintSet P (borosProjectionRadius r)

section InwardVariationalPoint

variable {ι : Type*} [Fintype ι]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Finitely many local inward steps have a common positive step size. This is useful when a
boundary estimate is first proved separately for each active projection constraint. -/
theorem exists_positive_step_mem_projectionConstraintSet
    [Nonempty ι] (T : ι → V →L[ℝ] V) (r : ι → ℝ) {x v : V}
    (hlocal : ∀ i, ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      ‖T i (x - t • v)‖ ≤ r i) :
    ∃ t : ℝ, 0 < t ∧ x - t • v ∈ projectionConstraintSet T r := by
  classical
  let δ : ι → ℝ := fun i => Classical.choose (hlocal i)
  have hδpos : ∀ i, 0 < δ i := fun i => (Classical.choose_spec (hlocal i)).1
  have hδprop : ∀ i t, 0 < t → t < δ i → ‖T i (x - t • v)‖ ≤ r i := by
    intro i t ht0 htδ
    exact (Classical.choose_spec (hlocal i)).2 t ht0 htδ
  let D : Finset ℝ := Finset.univ.image δ
  have hDne : D.Nonempty := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨δ i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  let ε : ℝ := D.min' hDne
  have hεpos : 0 < ε := by
    change 0 < D.min' hDne
    rcases Finset.mem_image.mp (Finset.min'_mem D hDne) with ⟨i, _, heq⟩
    rw [← heq]
    exact hδpos i
  have hεle (i : ι) : ε ≤ δ i :=
    Finset.min'_le D (δ i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  let t := ε / 2
  refine ⟨t, div_pos hεpos (by norm_num), ?_⟩
  intro i
  apply hδprop i t (div_pos hεpos (by norm_num))
  dsimp [t]
  linarith [hεle i]

/-- The common-step result also covers an empty constraint family, where every point is feasible. -/
theorem exists_positive_step_mem_projectionConstraintSet_of_local
    (T : ι → V →L[ℝ] V) (r : ι → ℝ) {x v : V}
    (hlocal : ∀ i, ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      ‖T i (x - t • v)‖ ≤ r i) :
    ∃ t : ℝ, 0 < t ∧ x - t • v ∈ projectionConstraintSet T r := by
  classical
  by_cases hι : Nonempty ι
  · letI := hι
    exact exists_positive_step_mem_projectionConstraintSet T r hlocal
  · haveI : IsEmpty ι := not_nonempty_iff.mp hι
    refine ⟨1, by norm_num, ?_⟩
    intro i
    exact isEmptyElim i

/-- Strict decrease of every active quadratic projection constraint gives a feasible local step
along `-v`. Inactive constraints have slack, so their bounds persist for sufficiently small
steps. -/
theorem exists_positive_step_mem_projectionConstraintSet_of_active_inner
    (T : ι → V →L[ℝ] V) (r : ι → ℝ) {x v : V}
    (hx : x ∈ projectionConstraintSet T r)
    (hstrict : ∀ i, ‖T i x‖ = r i → 0 < inner ℝ (T i v) (T i x)) :
    ∃ t : ℝ, 0 < t ∧ x - t • v ∈ projectionConstraintSet T r := by
  apply exists_positive_step_mem_projectionConstraintSet_of_local T r
  intro i
  let a : ℝ := ‖T i v‖ ^ 2
  let b : ℝ := inner ℝ (T i v) (T i x)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hsq (t : ℝ) :
      ‖T i (x - t • v)‖ ^ 2 = ‖T i x‖ ^ 2 - 2 * t * b + t ^ 2 * a := by
    have hmap : T i (x - t • v) = T i x - t • T i v := by
      simp only [map_sub, map_smul]
    rw [hmap]
    calc
      ‖T i x - t • T i v‖ ^ 2 =
          inner ℝ (T i x - t • T i v) (T i x - t • T i v) :=
            (real_inner_self_eq_norm_sq _).symm
      _ = ‖T i x‖ ^ 2 - 2 * t * b + t ^ 2 * ‖T i v‖ ^ 2 := by
        rw [inner_sub_sub_self]
        simp only [real_inner_smul_right, real_inner_smul_left,
          real_inner_self_eq_norm_sq]
        rw [← real_inner_comm (T i x) (T i v)]
        dsimp [b]
        rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
        ring_nf
      _ = ‖T i x‖ ^ 2 - 2 * t * b + t ^ 2 * a := by rfl
  by_cases hactive : ‖T i x‖ = r i
  · have hb : 0 < b := hstrict i hactive
    let δ := b / (a + 1)
    have hδ : 0 < δ := div_pos hb (by linarith)
    refine ⟨δ, hδ, ?_⟩
    intro t ht0 htδ
    have hta : t * a < b := by
      have hbound := (lt_div_iff₀ (by linarith : 0 < a + 1)).mp htδ
      nlinarith [hbound]
    have hcross : t ^ 2 * a < t * b := by
      have hmul := mul_lt_mul_of_pos_left hta ht0
      nlinarith [hmul]
    have hsq' : ‖T i (x - t • v)‖ ^ 2 < (r i) ^ 2 := by
      rw [hsq, hactive]
      nlinarith [hcross, mul_pos ht0 hb]
    have hr : 0 ≤ r i := by rw [← hactive]; exact norm_nonneg _
    have hnorm : ‖T i (x - t • v)‖ < r i :=
      (sq_lt_sq₀ (norm_nonneg _) hr).mp hsq'
    exact hnorm.le
  · have hle : ‖T i x‖ ≤ r i := hx i
    have hlt : ‖T i x‖ < r i := lt_of_le_of_ne hle hactive
    have hsqlt : ‖T i x‖ ^ 2 < (r i) ^ 2 :=
      (sq_lt_sq₀ (norm_nonneg _) (le_of_lt (lt_of_le_of_lt (norm_nonneg _) hlt))).mpr hlt
    let d := (r i) ^ 2 - ‖T i x‖ ^ 2
    have hd : 0 < d := by dsimp [d]; linarith
    have hden : 0 < 2 * |b| + a + 1 := by positivity
    let δ := min 1 (d / (2 * |b| + a + 1))
    have hδ : 0 < δ := lt_min (by norm_num) (div_pos hd hden)
    refine ⟨δ, hδ, ?_⟩
    intro t ht0 htδ
    have ht1 : t < 1 := lt_of_lt_of_le htδ (min_le_left _ _)
    have htd : t < d / (2 * |b| + a + 1) := lt_of_lt_of_le htδ (min_le_right _ _)
    have hbound : t * (2 * |b| + a) < d := by
      have hmul := (lt_div_iff₀ hden).mp htd
      nlinarith [abs_nonneg b]
    have hta : t ^ 2 * a ≤ t * a := by
      have hprod : 0 ≤ t * (1 - t) * a :=
        mul_nonneg (mul_nonneg (le_of_lt ht0) (by linarith)) ha
      nlinarith [hprod]
    have hbabs : -b ≤ |b| := neg_le_abs b
    have hbupper : -2 * t * b ≤ 2 * t * |b| := by
      have hmul := mul_le_mul_of_nonneg_left hbabs
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt ht0))
      nlinarith [hmul]
    have hdelta : -2 * t * b + t ^ 2 * a < d := by
      calc
        -2 * t * b + t ^ 2 * a ≤ 2 * t * |b| + t * a := by nlinarith [hbupper, hta]
        _ = t * (2 * |b| + a) := by ring
        _ < d := hbound
    have hsq' : ‖T i (x - t • v)‖ ^ 2 < (r i) ^ 2 := by
      rw [hsq]
      dsimp [d] at hdelta ⊢
      nlinarith
    have hr : 0 < r i := lt_of_le_of_lt (norm_nonneg _) hlt
    have hnorm : ‖T i (x - t • v)‖ < r i :=
      (sq_lt_sq₀ (norm_nonneg _) (le_of_lt hr)).mp hsq'
    exact hnorm.le

/-- A variational-inequality point is a zero if a small step in the negative field direction
always remains feasible. -/
theorem variational_eq_zero_of_positive_inward_step
    {K : Set V} {x v : V}
    (hvi : ∀ y ∈ K, 0 ≤ inner ℝ v (y - x))
    (hstep : v ≠ 0 → ∃ t : ℝ, 0 < t ∧ x - t • v ∈ K) :
    v = 0 := by
  by_contra hv
  obtain ⟨t, ht, hmem⟩ := hstep hv
  have h := hvi (x - t • v) hmem
  have hsub : x - t • v - x = -(t • v) := by abel
  rw [hsub, inner_neg_right] at h
  have hs : inner ℝ v (t • v) = t * ‖v‖ ^ 2 := by
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
  rw [hs] at h
  have hnorm : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  nlinarith [mul_pos ht hnorm]

/-- At a variational point of finitely many quadratic projection constraints, strict decrease of
each active constraint along `-v` forces `v=0`. The decrease assumption is expressed by the
quadratic derivative pairing `⟪T_i v, T_i x⟫`. -/
theorem variational_eq_zero_of_active_inward_projectionConstraints
    (T : ι → V →L[ℝ] V) (r : ι → ℝ) {x v : V}
    (hx : x ∈ projectionConstraintSet T r)
    (hvi : ∀ y ∈ projectionConstraintSet T r, 0 ≤ inner ℝ v (y - x))
    (hstrict : ∀ i, ‖T i x‖ = r i → 0 < inner ℝ (T i v) (T i x)) :
    v = 0 := by
  by_contra hv
  obtain ⟨t, ht, hy⟩ :=
    exists_positive_step_mem_projectionConstraintSet_of_active_inner T r hx hstrict
  exact hv (variational_eq_zero_of_positive_inward_step hvi (fun _ => ⟨t, ht, hy⟩))

/-- The active-constraint form of the preceding variational argument. It accepts the local
quadratic decrease estimates directly, without assuming that different projections commute. -/
theorem variational_eq_zero_of_active_local_inward_projectionConstraints
    (T : ι → V →L[ℝ] V) (r : ι → ℝ) {x v : V}
    (hvi : ∀ y ∈ projectionConstraintSet T r, 0 ≤ inner ℝ v (y - x))
    (hlocal : v ≠ 0 → ∀ i,
      ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
        ‖T i (x - t • v)‖ ≤ r i) :
    v = 0 := by
  by_contra hv
  obtain ⟨t, ht, hy⟩ :=
    exists_positive_step_mem_projectionConstraintSet_of_local T r (hlocal hv)
  have hz := variational_eq_zero_of_positive_inward_step hvi
    (fun _ => ⟨t, ht, hy⟩)
  exact hv hz

end InwardVariationalPoint

end CRNT.Analysis
