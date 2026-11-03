import CRNT.Multistationarity.LocalDegreeOn
import CRNT.Multistationarity.DegreeStability

/-!
# Parametrized local constancy of the degree

`DegreeStability.eventually_localDegree_eq` gives local constancy of the local degree of a
**fixed** map as the value moves.  Homotopy invariance needs the other direction: the map moves
and the value stays fixed.  The docstring of `regularDegree_homotopy_invariant` leaves that as
the hypothesis `hloc`, "applied per slice with the parameter as the moving datum".  This module
proves the per-slice, per-point half of `hloc`.

The mechanism is the graph map

`homotopyGraph H (s, x) = (s, H (s, x))`,

whose derivative is block triangular, with the identity on the parameter and the partial
derivative `∂H/∂x` on the space.  It is therefore invertible exactly when `∂H/∂x` is, and the
inverse function theorem applies to it even though no single slice map controls the parameter
direction.  Transporting the resulting local homeomorphism back to the slices gives, near a
nondegenerate solution `x₀` of `H (s₀, ·) = y`:

* a fixed neighbourhood `V` of `x₀`, independent of `s`;
* for every `s` near `s₀`, exactly one solution of `H (s, ·) = y` in `V`;
* that solution carries the orientation sign of `x₀`.

Everything is stated with `localDegreeOn` (`CRNT.Multistationarity.LocalDegreeOn`), so no
finiteness is asked of the slice preimage outside `V`.  With the global `localDegree` these
statements would be unusable for mass-action homotopies, whose slices generally have infinite
zero sets away from the region of interest.

* `partialFDeriv` — the derivative of a homotopy in the space variable.
* `hasFDerivAt_slice`, `partialFDeriv_eq` — it really is the derivative of the slice map.
* `continuousAt_partialFDeriv` — it is continuous in `(s, x)` jointly.
* `homotopyGraph`, `homotopyGraphEquiv`, `hasStrictFDerivAt_homotopyGraph` — the graph map and
  its invertible block-triangular derivative.
* `exists_eventually_slice_singleton` — unique nearby solution with matching orientation.
* `exists_eventually_localDegreeOn_eq` — the per-piece statement in degree form.

## What this does not yet give

`hloc` also requires that the pieces **cover** the slice preimage and are pairwise disjoint.
Disjointness is a matter of shrinking finitely many neighbourhoods; covering is not local — it
needs the confinement argument of `DegreeProperConstant.eventually_confinement_of_isProperMap`
in the parameter direction, so that no solution enters the domain from outside as `s` moves.
That, plus finiteness of the reference slice preimage, is what still stands between this module
and an unconditional homotopy invariance theorem.
-/

namespace CRNT

open Set Filter
open scoped Topology Classical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

/-- The derivative of a homotopy in the space variable only. -/
noncomputable def partialFDeriv (H : ℝ × E → E) (p : ℝ × E) : E →L[ℝ] E :=
  (fderiv ℝ H p).comp (ContinuousLinearMap.inr ℝ ℝ E)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem hasFDerivAt_slice (H : ℝ × E → E) {p : ℝ × E} (hH : DifferentiableAt ℝ H p) :
    HasFDerivAt (fun x => H (p.1, x)) (partialFDeriv H p) p.2 :=
  hH.hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem partialFDeriv_eq (H : ℝ × E → E) {p : ℝ × E} (hH : DifferentiableAt ℝ H p) :
    fderiv ℝ (fun x => H (p.1, x)) p.2 = partialFDeriv H p :=
  (hasFDerivAt_slice H hH).fderiv

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- Precomposition with a fixed map is continuous, so the partial derivative is continuous
wherever the total derivative is. -/
theorem continuousAt_partialFDeriv (H : ℝ × E → E) {p : ℝ × E}
    (hH : ContDiffAt ℝ 1 H p) : ContinuousAt (partialFDeriv H) p := by
  have hpre : Continuous fun T : (ℝ × E) →L[ℝ] E =>
      T.comp (ContinuousLinearMap.inr ℝ ℝ E) :=
    ((ContinuousLinearMap.compL ℝ E (ℝ × E) E).flip
      (ContinuousLinearMap.inr ℝ ℝ E)).continuous
  exact hpre.continuousAt.comp (hH.continuousAt_fderiv (by norm_num))

/-- The graph map `(s, x) ↦ (s, H (s, x))` of a homotopy.  Its zero fibres over `(s, y)` are
exactly the slice solutions of `H (s, ·) = y`, and it is a local diffeomorphism wherever the
partial derivative in `x` is invertible. -/
noncomputable def homotopyGraph (H : ℝ × E → E) : ℝ × E → ℝ × E := fun p => (p.1, H p)

/-- The derivative of the graph map at `p`, packaged as an equivalence: it is block triangular
with the identity on the parameter and the invertible partial derivative on the space. -/
noncomputable def homotopyGraphEquiv (H : ℝ × E → E) {p : ℝ × E}
    (hdet : LinearMap.det (partialFDeriv H p).toLinearMap ≠ 0) : (ℝ × E) ≃L[ℝ] (ℝ × E) :=
  (ContinuousLinearEquiv.refl ℝ ℝ).skewProd
    ((partialFDeriv H p).toContinuousLinearEquivOfDetNeZero hdet)
    ((fderiv ℝ H p).comp (ContinuousLinearMap.inl ℝ ℝ E))

omit [CompleteSpace E] in
theorem coe_homotopyGraphEquiv (H : ℝ × E → E) {p : ℝ × E}
    (hdet : LinearMap.det (partialFDeriv H p).toLinearMap ≠ 0) :
    (homotopyGraphEquiv H hdet : (ℝ × E) →L[ℝ] (ℝ × E))
      = (ContinuousLinearMap.fst ℝ ℝ E).prod (fderiv ℝ H p) := by
  refine ContinuousLinearMap.ext fun q => ?_
  have hq : (fderiv ℝ H p) q
      = (fderiv ℝ H p) (ContinuousLinearMap.inl ℝ ℝ E q.1)
        + (fderiv ℝ H p) (ContinuousLinearMap.inr ℝ ℝ E q.2) := by
    rw [← map_add]
    congr 1
    simp
  simp only [homotopyGraphEquiv, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.skewProd_apply, ContinuousLinearEquiv.refl_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero_apply, partialFDeriv,
    ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [hq, add_comm]

omit [CompleteSpace E] in
theorem hasStrictFDerivAt_homotopyGraph (H : ℝ × E → E) {p : ℝ × E} (hH : ContDiffAt ℝ 1 H p)
    (hdet : LinearMap.det (partialFDeriv H p).toLinearMap ≠ 0) :
    HasStrictFDerivAt (homotopyGraph H)
      (homotopyGraphEquiv H hdet : (ℝ × E) →L[ℝ] (ℝ × E)) p := by
  rw [coe_homotopyGraphEquiv]
  exact hasStrictFDerivAt_fst.prodMk (hH.hasStrictFDerivAt (by norm_num))

/-- A real-valued function that is continuous and nonzero at a point has locally constant sign. -/
theorem eventually_sign_eq_of_continuousAt {X : Type*} [TopologicalSpace X] {d : X → ℝ} {q₀ : X}
    (hd : ContinuousAt d q₀) (h0 : d q₀ ≠ 0) :
    ∀ᶠ q in 𝓝 q₀, SignType.sign (d q) = SignType.sign (d q₀) := by
  rcases lt_trichotomy (d q₀) 0 with h | h | h
  · filter_upwards [hd.eventually_lt continuousAt_const (g := fun _ => (0 : ℝ)) h] with q hq
    rw [sign_neg hq, sign_neg h]
  · exact absurd h h0
  · filter_upwards [continuousAt_const.eventually_lt hd (f := fun _ => (0 : ℝ)) h] with q hq
    rw [sign_pos hq, sign_pos h]

/-- **Parametrized local structure of the slice solution set.**  Let `H` be a `C¹` homotopy and
let `x₀` be a nondegenerate solution of `H (s₀, ·) = y`, meaning the partial derivative in the
space variable is invertible there.  Then there is a fixed neighbourhood `V` of `x₀` such that
for every parameter `s` near `s₀` the slice equation `H (s, x) = y` has exactly one solution in
`V`, and its orientation sign is the orientation sign at `x₀`.

This is the parameter-direction analogue of `eventually_localDegree_eq`, obtained by applying the
inverse function theorem to the graph map `(s, x) ↦ (s, H (s, x))`, whose derivative is block
triangular and hence invertible exactly when the partial derivative in `x` is. -/
theorem exists_eventually_slice_singleton (H : ℝ × E → E) {s₀ : ℝ} {x₀ : E}
    (hH : ContDiffAt ℝ 1 H (s₀, x₀))
    (hdet : LinearMap.det (partialFDeriv H (s₀, x₀)).toLinearMap ≠ 0)
    {V₀ : Set E} (hV₀ : V₀ ∈ 𝓝 x₀) :
    ∃ V : Set E, V ⊆ V₀ ∧ IsOpen V ∧ x₀ ∈ V ∧
      ∀ᶠ s in 𝓝 s₀, ∃ x ∈ V,
        (fun z => H (s, z)) ⁻¹' {H (s₀, x₀)} ∩ V = {x} ∧
        SignType.sign (LinearMap.det (fderiv ℝ (fun z => H (s, z)) x).toLinearMap) =
          SignType.sign (LinearMap.det (partialFDeriv H (s₀, x₀)).toLinearMap) := by
  have hstrict := hasStrictFDerivAt_homotopyGraph H hH hdet
  set Φ := hstrict.toOpenPartialHomeomorph (homotopyGraph H) with hΦdef
  have hcoeΦ : (Φ : ℝ × E → ℝ × E) = homotopyGraph H := hstrict.toOpenPartialHomeomorph_coe
  have hpS : ((s₀, x₀) : ℝ × E) ∈ Φ.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hV₀prod : (Set.univ ×ˢ V₀ : Set (ℝ × E)) ∈ 𝓝 ((s₀, x₀) : ℝ × E) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod Filter.univ_mem hV₀
  obtain ⟨I, V, hIopen, hs₀I, hVopen, hx₀V, hboxfull⟩ :=
    mem_nhds_prod_iff'.1 (Filter.inter_mem (Φ.open_source.mem_nhds hpS) hV₀prod)
  have hbox : I ×ˢ V ⊆ Φ.source := fun q hq => (hboxfull hq).1
  have hVV₀ : V ⊆ V₀ := fun x hx => ((hboxfull (Set.mk_mem_prod hs₀I hx)).2).2
  have hWopen : IsOpen (Φ '' (I ×ˢ V)) :=
    Φ.isOpen_image_of_subset_source (hIopen.prod hVopen) hbox
  have hΦp : Φ ((s₀, x₀) : ℝ × E) = (s₀, H (s₀, x₀)) := by
    rw [hcoeΦ]; rfl
  have hmemW : ((s₀, H (s₀, x₀)) : ℝ × E) ∈ Φ '' (I ×ˢ V) :=
    ⟨(s₀, x₀), ⟨hs₀I, hx₀V⟩, hΦp⟩
  refine ⟨V, hVV₀, hVopen, hx₀V, ?_⟩
  have hcont : ContinuousAt (fun s : ℝ => ((s, H (s₀, x₀)) : ℝ × E)) s₀ :=
    (continuous_id.prodMk continuous_const).continuousAt
  have hevW : ∀ᶠ s in 𝓝 s₀, ((s, H (s₀, x₀)) : ℝ × E) ∈ Φ '' (I ×ˢ V) :=
    hcont.eventually_mem (hWopen.mem_nhds hmemW)
  have hevI : ∀ᶠ s in 𝓝 s₀, s ∈ I := hIopen.mem_nhds hs₀I
  have htgt : ((s₀, H (s₀, x₀)) : ℝ × E) ∈ Φ.target := hΦp ▸ Φ.map_source hpS
  have hsymm0 : Φ.symm ((s₀, H (s₀, x₀)) : ℝ × E) = (s₀, x₀) := by
    rw [← hΦp]; exact Φ.left_inv hpS
  have htend : Filter.Tendsto (fun s : ℝ => Φ.symm ((s, H (s₀, x₀)) : ℝ × E)) (𝓝 s₀)
      (𝓝 ((s₀, x₀) : ℝ × E)) := by
    have h1 : Filter.Tendsto Φ.symm (𝓝 ((s₀, H (s₀, x₀)) : ℝ × E))
        (𝓝 (Φ.symm ((s₀, H (s₀, x₀)) : ℝ × E))) := Φ.continuousAt_symm htgt
    rw [hsymm0] at h1
    exact h1.comp hcont
  have hsign := htend.eventually (eventually_sign_eq_of_continuousAt
    (ContinuousLinearMap.continuous_det.continuousAt.comp (continuousAt_partialFDeriv H hH)) hdet)
  have hdiff := htend.eventually ((hH.eventually (by norm_num)).mono
    fun q hq => hq.differentiableAt (by norm_num))
  filter_upwards [hevW, hevI, hsign, hdiff] with s hsW hsI hssign hsdiff
  obtain ⟨q, hqbox, hqΦ⟩ := hsW
  have hqS : q ∈ Φ.source := hbox hqbox
  have hqeq : homotopyGraph H q = ((s, H (s₀, x₀)) : ℝ × E) := by
    rw [← hcoeΦ]; exact hqΦ
  have hq1 : q.1 = s := congrArg Prod.fst hqeq
  have hq2 : H q = H (s₀, x₀) := congrArg Prod.snd hqeq
  have hqsymm : Φ.symm ((s, H (s₀, x₀)) : ℝ × E) = q := by
    rw [← hqΦ, Φ.left_inv hqS]
  rw [hqsymm] at hssign hsdiff
  refine ⟨q.2, hqbox.2, ?_, ?_⟩
  · apply Set.eq_singleton_iff_unique_mem.2
    refine ⟨⟨?_, hqbox.2⟩, ?_⟩
    · show H (s, q.2) = H (s₀, x₀)
      rw [← hq1]; exact hq2
    · rintro x' ⟨hx'pre, hx'V⟩
      have hx'S : ((s, x') : ℝ × E) ∈ Φ.source := hbox ⟨hsI, hx'V⟩
      have hΦx' : Φ ((s, x') : ℝ × E) = Φ q := by
        rw [hqΦ, hcoeΦ]
        exact Prod.ext rfl hx'pre
      exact congrArg Prod.snd (Φ.injOn hx'S hqS hΦx')
  · have hfd : fderiv ℝ (fun z => H (s, z)) q.2 = partialFDeriv H q := by
      have h := partialFDeriv_eq H hsdiff
      rw [hq1] at h
      exact h
    rw [hfd]
    exact hssign

/-- **Per-piece parametrized local constancy of the relative degree.**  Near a nondegenerate
solution `x₀` of `H (s₀, ·) = y` there is a fixed neighbourhood `V` on which, for every
parameter `s` close to `s₀`, the relative local degree of the slice map on `V` is the constant
orientation sign at `x₀`.

This is exactly the per-piece obligation in the parameter-local-constancy hypothesis `hloc` of
`regularDegree_homotopy_invariant`.  Because it is stated with `localDegreeOn`, no finiteness is
required away from `V`: the slice preimage inside `V` is a single point. -/
theorem exists_eventually_localDegreeOn_eq (H : ℝ × E → E) {s₀ : ℝ} {x₀ : E}
    (hH : ContDiffAt ℝ 1 H (s₀, x₀))
    (hdet : LinearMap.det (partialFDeriv H (s₀, x₀)).toLinearMap ≠ 0)
    {V₀ : Set E} (hV₀ : V₀ ∈ 𝓝 x₀) :
    ∃ V : Set E, V ⊆ V₀ ∧ IsOpen V ∧ x₀ ∈ V ∧
      ∀ᶠ s in 𝓝 s₀, ∃ hfin : ((fun z => H (s, z)) ⁻¹' {H (s₀, x₀)} ∩ V).Finite,
        localDegreeOn (fun z => H (s, z)) (H (s₀, x₀)) V hfin =
          ((SignType.sign
            (LinearMap.det (partialFDeriv H (s₀, x₀)).toLinearMap) : SignType) : ℤ) := by
  obtain ⟨V, hVV₀, hVopen, hx₀V, hev⟩ := exists_eventually_slice_singleton H hH hdet hV₀
  refine ⟨V, hVV₀, hVopen, hx₀V, ?_⟩
  filter_upwards [hev] with s hs
  obtain ⟨x, _hxV, hset, hsign⟩ := hs
  have hfin : ((fun z => H (s, z)) ⁻¹' {H (s₀, x₀)} ∩ V).Finite := by
    rw [hset]
    exact Set.finite_singleton x
  refine ⟨hfin, ?_⟩
  have htf : hfin.toFinset = {x} := by
    ext z
    simp only [Set.Finite.mem_toFinset, hset, Set.mem_singleton_iff, Finset.mem_singleton]
  unfold localDegreeOn
  rw [htf, Finset.sum_singleton, hsign]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- **Eventual confinement of slice solutions.**  Solutions of `H (s, ·) = y` inside a compact
set cannot appear away from the solutions of `H (s₀, ·) = y`: if every solution in `K` at the
parameter `s₀` lies in the open set `G`, then the same holds for every parameter near `s₀`.

This is the non-local half of the parameter-local-constancy hypothesis `hloc` of
`regularDegree_homotopy_invariant`: it is what stops a solution from wandering into the domain
from outside as the parameter moves, and it is the tube lemma rather than anything about
properness — compactness of `K` is enough. -/
theorem eventually_forall_mem_of_slice_zeros_subset (H : ℝ × E → E) (hH : Continuous H)
    {s₀ : ℝ} {K G : Set E} {y : E} (hK : IsCompact K) (hG : IsOpen G)
    (hz : ∀ x ∈ K, H (s₀, x) = y → x ∈ G) :
    ∀ᶠ s in 𝓝 s₀, ∀ x ∈ K, H (s, x) = y → x ∈ G := by
  have hKG : IsCompact (K \ G) := hK.diff hG
  have hpt : ∀ x ∈ K \ G, ∀ᶠ z : ℝ × E in 𝓝 ((s₀, x) : ℝ × E), H (z.1, z.2) ≠ y := by
    intro x hx
    have hne : H ((s₀, x) : ℝ × E) ≠ y := fun h => hx.2 (hz x hx.1 h)
    exact (hH.continuousAt).eventually_ne hne
  have h := hKG.eventually_forall_of_forall_eventually (x₀ := s₀)
    (P := fun (s : ℝ) (x : E) => H (s, x) ≠ y) hpt
  filter_upwards [h] with s hs x hxK hxy
  by_contra hxG
  exact hs x ⟨hxK, hxG⟩ hxy

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- A finite set of points admits a radius separating all of them. -/
theorem exists_pos_sep (Z : Finset E) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ Z, ∀ z ∈ Z, x ≠ z → 2 * r < dist x z := by
  classical
  set P := (Z ×ˢ Z).filter (fun p => p.1 ≠ p.2) with hP
  by_cases hPe : P.Nonempty
  · obtain ⟨p, hpP, hpmin⟩ := P.exists_min_image (fun p => dist p.1 p.2) hPe
    have hpne : p.1 ≠ p.2 := (Finset.mem_filter.1 hpP).2
    have hpos : 0 < dist p.1 p.2 := dist_pos.2 hpne
    refine ⟨dist p.1 p.2 / 3, by positivity, ?_⟩
    intro x hx z hz hxz
    have hmem : (x, z) ∈ P :=
      Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hx, hz⟩, hxz⟩
    have hle := hpmin (x, z) hmem
    simp only at hle
    linarith
  · refine ⟨1, one_pos, ?_⟩
    intro x hx z hz hxz
    exact absurd ⟨(x, z), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hx, hz⟩, hxz⟩⟩ hPe

/-- **Local constancy of the relative degree in the parameter.**  Let `H` be a `C¹` homotopy,
`U` an open set with compact closure, and `y` a value such that at the parameter `s₀`

* no solution of `H (s₀, ·) = y` lies on the boundary of `U`, and
* every solution in `U` is nondegenerate, and there are finitely many of them,

then the relative degree of the slice map on `U` is constant for all parameters near `s₀`.

This is the parameter-direction local constancy that `regularDegree_homotopy_invariant` takes
as the hypothesis `hloc`, now a theorem in the domain-relative setting.  The two ingredients
are `exists_eventually_localDegreeOn_eq` (each nondegenerate solution persists, alone in its
own neighbourhood, with its orientation) and
`eventually_forall_mem_of_slice_zeros_subset` (no further solution can enter `U` from
outside), combined by relative additivity over the resulting finite disjoint cover. -/
theorem eventually_localDegreeOn_eq (H : ℝ × E → E) (hH : ContDiff ℝ 1 H)
    {s₀ : ℝ} {U : Set E} (hUopen : IsOpen U) (hUcpt : IsCompact (closure U)) {y : E}
    (hbd : ∀ x ∈ closure U, H (s₀, x) = y → x ∈ U)
    (hreg : ∀ x ∈ U, H (s₀, x) = y → LinearMap.det (partialFDeriv H (s₀, x)).toLinearMap ≠ 0)
    (hZ : ((fun x => H (s₀, x)) ⁻¹' {y} ∩ U).Finite) :
    ∀ᶠ s in 𝓝 s₀, ∃ hfin : ((fun x => H (s, x)) ⁻¹' {y} ∩ U).Finite,
      localDegreeOn (fun x => H (s, x)) y U hfin
        = localDegreeOn (fun x => H (s₀, x)) y U hZ := by
  classical
  set Z : Finset E := hZ.toFinset with hZdef
  obtain ⟨r, hr0, hsep⟩ := exists_pos_sep Z
  have hchoice : ∀ x ∈ Z, ∃ V : Set E, V ⊆ U ∩ Metric.ball x r ∧ IsOpen V ∧ x ∈ V ∧
      ∀ᶠ s in 𝓝 s₀, ∃ hfinV : ((fun z => H (s, z)) ⁻¹' {y} ∩ V).Finite,
        localDegreeOn (fun z => H (s, z)) y V hfinV
          = ((SignType.sign
              (LinearMap.det (partialFDeriv H (s₀, x)).toLinearMap) : SignType) : ℤ) := by
    intro x hx
    rw [hZdef, Set.Finite.mem_toFinset] at hx
    have hxy : H (s₀, x) = y := hx.1
    have hnb : U ∩ Metric.ball x r ∈ 𝓝 x :=
      Filter.inter_mem (hUopen.mem_nhds hx.2) (Metric.ball_mem_nhds x hr0)
    obtain ⟨V, hVsub, hVopen, hxV, hev⟩ :=
      exists_eventually_localDegreeOn_eq H hH.contDiffAt (hreg x hx.2 hx.1) hnb
    rw [hxy] at hev
    exact ⟨V, hVsub, hVopen, hxV, hev⟩
  choose! V hVsub hVopen hxV hev using hchoice
  set W : E → Set E := fun x => if x ∈ Z then V x else ∅ with hWdef
  have hWU : ∀ x, W x ⊆ U := by
    intro x
    by_cases hx : x ∈ Z
    · simp only [hWdef, if_pos hx]
      exact fun z hz => ((hVsub x hx) hz).1
    · simp only [hWdef, if_neg hx]
      exact Set.empty_subset U
  have hWV : ∀ x ∈ Z, W x = V x := fun x hx => by simp only [hWdef, if_pos hx]
  have hWball : ∀ x ∈ Z, W x ⊆ Metric.ball x r := by
    intro x hx
    rw [hWV x hx]
    exact fun z hz => ((hVsub x hx) hz).2
  have hdisj : ∀ x ∈ Z, ∀ z ∈ Z, x ≠ z → ∀ w, w ∈ W x → w ∈ W z → False := by
    intro x hx z hz hxz w hwx hwz
    have h1 : dist w x < r := Metric.mem_ball.1 (hWball x hx hwx)
    have h2 : dist w z < r := Metric.mem_ball.1 (hWball z hz hwz)
    have h3 : dist x z ≤ dist x w + dist w z := dist_triangle x w z
    rw [dist_comm x w] at h3
    have := hsep x hx z hz hxz
    linarith
  -- the union of the pieces is an open set containing every solution at `s₀`
  have hGopen : IsOpen (⋃ x ∈ (Z : Set E), W x) := by
    refine isOpen_biUnion ?_
    intro x hx
    rw [hWV x hx]
    exact hVopen x hx
  have hzs₀ : ∀ x ∈ closure U, H (s₀, x) = y → x ∈ ⋃ x ∈ (Z : Set E), W x := by
    intro x hxcl hxy
    have hxU : x ∈ U := hbd x hxcl hxy
    have hxZ : x ∈ Z := by
      rw [hZdef, Set.Finite.mem_toFinset]
      exact ⟨hxy, hxU⟩
    exact Set.mem_biUnion hxZ ((hWV x hxZ) ▸ hxV x hxZ)
  have hconf := eventually_forall_mem_of_slice_zeros_subset H hH.continuous hUcpt hGopen hzs₀
  have hall : ∀ᶠ s in 𝓝 s₀, ∀ x ∈ Z,
      ∃ hfinV : ((fun z => H (s, z)) ⁻¹' {y} ∩ V x).Finite,
        localDegreeOn (fun z => H (s, z)) y (V x) hfinV
          = ((SignType.sign
              (LinearMap.det (partialFDeriv H (s₀, x)).toLinearMap) : SignType) : ℤ) :=
    (Filter.eventually_all_finset Z).2 hev
  -- the sum the degree equals, computed once
  have hsum : ∀ s : ℝ, (∀ x ∈ Z, ∃ hfinV : ((fun z => H (s, z)) ⁻¹' {y} ∩ V x).Finite,
        localDegreeOn (fun z => H (s, z)) y (V x) hfinV
          = ((SignType.sign
              (LinearMap.det (partialFDeriv H (s₀, x)).toLinearMap) : SignType) : ℤ)) →
      ∀ (hfin : ((fun x => H (s, x)) ⁻¹' {y} ∩ U).Finite),
      (∀ z ∈ (fun x => H (s, x)) ⁻¹' {y} ∩ U, ∃ x ∈ Z, z ∈ W x) →
      localDegreeOn (fun x => H (s, x)) y U hfin
        = ∑ x ∈ Z, ((SignType.sign
            (LinearMap.det (partialFDeriv H (s₀, x)).toLinearMap) : SignType) : ℤ) := by
    intro s hs hfin hcover
    refine localDegreeOn_eq_sum_of_cover (fun x => H (s, x)) y Z W _ hfin
      (fun i _ => hWU i) hcover hdisj ?_
    intro x hx h
    obtain ⟨hfinV, heq⟩ := hs x hx
    have hWVx : W x = V x := hWV x hx
    have h' : ((fun z => H (s, z)) ⁻¹' {y} ∩ V x).Finite := hWVx ▸ h
    calc localDegreeOn (fun z => H (s, z)) y (W x) h
        = localDegreeOn (fun z => H (s, z)) y (V x) h' := by
          congr 1
      _ = _ := heq
  -- at the base parameter
  have hcover₀ : ∀ z ∈ (fun x => H (s₀, x)) ⁻¹' {y} ∩ U, ∃ x ∈ Z, z ∈ W x := by
    intro z hz
    have hzZ : z ∈ Z := by rw [hZdef, Set.Finite.mem_toFinset]; exact hz
    exact ⟨z, hzZ, (hWV z hzZ) ▸ hxV z hzZ⟩
  have hbase := hsum s₀ (hall.self_of_nhds) hZ hcover₀
  filter_upwards [hconf, hall] with s hsconf hsall
  have hcover : ∀ z ∈ (fun x => H (s, x)) ⁻¹' {y} ∩ U, ∃ x ∈ Z, z ∈ W x := by
    intro z hz
    have hzcl : z ∈ closure U := subset_closure hz.2
    have := hsconf z hzcl hz.1
    rcases Set.mem_iUnion₂.1 this with ⟨x, hxZ, hzx⟩
    exact ⟨x, hxZ, hzx⟩
  have hfin : ((fun x => H (s, x)) ⁻¹' {y} ∩ U).Finite := by
    have hbig : (⋃ x ∈ (Z : Set E), ((fun z => H (s, z)) ⁻¹' {y} ∩ V x)).Finite := by
      refine Set.Finite.biUnion Z.finite_toSet (fun x hx => ?_)
      obtain ⟨hfinV, _⟩ := hsall x (Finset.mem_coe.1 hx)
      exact hfinV
    refine hbig.subset (fun z hz => ?_)
    obtain ⟨x, hxZ, hzx⟩ := hcover z hz
    refine Set.mem_biUnion (Finset.mem_coe.2 hxZ) ⟨hz.1, ?_⟩
    rwa [← hWV x hxZ]
  exact ⟨hfin, by rw [hsum s hsall hfin hcover, hbase]⟩

/-- **Homotopy invariance of the relative degree.**  For a `C¹` homotopy on a bounded region `U`
whose slices have no solutions on the boundary and only nondegenerate, finitely many solutions
inside, the relative degree on `U` is the same at both ends of the homotopy.

Unlike `regularDegree_homotopy_invariant` this is unconditional: the parameter-local-constancy
input is supplied by `eventually_localDegreeOn_eq`, so nothing is assumed beyond regularity of
the slices and boundary non-vanishing. -/
theorem localDegreeOn_homotopy_invariant (H : ℝ × E → E) (hH : ContDiff ℝ 1 H)
    {U : Set E} (hUopen : IsOpen U) (hUcpt : IsCompact (closure U)) {y : E}
    (hbd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ closure U, H (t, x) = y → x ∈ U)
    (hreg : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ U, H (t, x) = y →
      LinearMap.det (partialFDeriv H (t, x)).toLinearMap ≠ 0)
    (hfin : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((fun x => H (t, x)) ⁻¹' {y} ∩ U).Finite)
    (h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    localDegreeOn (fun x => H (0, x)) y U (hfin 0 h0)
      = localDegreeOn (fun x => H (1, x)) y U (hfin 1 h1) := by
  classical
  set F : Set.Icc (0 : ℝ) 1 → ℤ :=
    fun t => localDegreeOn (fun x => H ((t : ℝ), x)) y U (hfin (t : ℝ) t.2) with hF
  have hLC : IsLocallyConstant F := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t₀
    have hev := eventually_localDegreeOn_eq H hH hUopen hUcpt
      (hbd (t₀ : ℝ) t₀.2) (hreg (t₀ : ℝ) t₀.2) (hfin (t₀ : ℝ) t₀.2)
    have htend : Filter.Tendsto (fun t : Set.Icc (0 : ℝ) 1 => (t : ℝ)) (𝓝 t₀) (𝓝 (t₀ : ℝ)) :=
      continuous_subtype_val.continuousAt
    filter_upwards [htend.eventually hev] with t ht
    obtain ⟨hfin', heq⟩ := ht
    show localDegreeOn (fun x => H ((t : ℝ), x)) y U (hfin (t : ℝ) t.2)
      = localDegreeOn (fun x => H ((t₀ : ℝ), x)) y U (hfin (t₀ : ℝ) t₀.2)
    exact heq
  haveI : PreconnectedSpace (Set.Icc (0 : ℝ) 1) :=
    Subtype.preconnectedSpace (isPreconnected_Icc (a := (0 : ℝ)) (b := 1))
  have hconst := hLC.apply_eq_of_preconnectedSpace (⟨0, h0⟩ : Set.Icc (0 : ℝ) 1) ⟨1, h1⟩
  simpa [hF] using hconst

/-- **Existence from a nonzero degree along a homotopy.**  If the reference end of an admissible
homotopy has nonzero relative degree on `U`, the other end has a solution in `U`.

This is the conclusion that degree theory is used for in the deficiency-one existence argument,
and it now rests only on regularity of the slices and boundary non-vanishing. -/
theorem exists_mem_of_homotopy_of_localDegreeOn_ne_zero (H : ℝ × E → E) (hH : ContDiff ℝ 1 H)
    {U : Set E} (hUopen : IsOpen U) (hUcpt : IsCompact (closure U)) {y : E}
    (hbd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ closure U, H (t, x) = y → x ∈ U)
    (hreg : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ U, H (t, x) = y →
      LinearMap.det (partialFDeriv H (t, x)).toLinearMap ≠ 0)
    (hfin : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((fun x => H (t, x)) ⁻¹' {y} ∩ U).Finite)
    (h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (hdeg : localDegreeOn (fun x => H (0, x)) y U (hfin 0 h0) ≠ 0) :
    ∃ x ∈ U, H (1, x) = y := by
  by_contra hnone
  have hempty : (fun x => H (1, x)) ⁻¹' {y} ∩ U = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, iff_false, not_and]
    intro hx hxU
    exact hnone ⟨x, hxU, hx⟩
  have hzero := localDegreeOn_eq_zero_of_preimage_inter_empty
    (fun x => H (1, x)) y (hfin 1 h1) hempty
  rw [localDegreeOn_homotopy_invariant H hH hUopen hUcpt hbd hreg hfin h0 h1] at hdeg
  exact hdeg hzero

omit [CompleteSpace E] in
/-- The zero set of an invertible continuous linear map, intersected with any region, is finite:
it is at most the origin. -/
theorem finite_preimage_inter_of_det_ne_zero (T : E →L[ℝ] E)
    (hdet : LinearMap.det T.toLinearMap ≠ 0) (U : Set E) :
    ((⇑T) ⁻¹' {(0 : E)} ∩ U).Finite :=
  (finite_preimage_of_det_ne_zero T hdet 0).subset Set.inter_subset_left

omit [CompleteSpace E] in
/-- **The relative degree of an invertible linear reference map.**  On any region containing the
origin it is the orientation sign of the determinant.  This supplies the reference-map data of a
degree certificate: a single zero, finitely many of them, and a nonzero relative degree. -/
theorem localDegreeOn_continuousLinearMap (T : E →L[ℝ] E)
    (hdet : LinearMap.det T.toLinearMap ≠ 0) {U : Set E} (h0 : (0 : E) ∈ U)
    (hfin : ((⇑T) ⁻¹' {(0 : E)} ∩ U).Finite) :
    localDegreeOn (⇑T) 0 U hfin
      = ((SignType.sign (LinearMap.det T.toLinearMap) : SignType) : ℤ) := by
  have hpre : (⇑T) ⁻¹' {(0 : E)} = {(0 : E)} := by
    rw [preimage_singleton_of_det_ne_zero T hdet 0,
      show (equivOfDetNeZero T hdet).symm 0 = (0 : E) from map_zero _]
  have hset : (⇑T) ⁻¹' {(0 : E)} ∩ U = {(0 : E)} := by
    rw [hpre]
    exact Set.inter_eq_self_of_subset_left (Set.singleton_subset_iff.2 h0)
  have htf : hfin.toFinset = {(0 : E)} := by
    ext z
    rw [Set.Finite.mem_toFinset, hset, Finset.mem_singleton, Set.mem_singleton_iff]
  unfold localDegreeOn
  rw [htf, Finset.sum_singleton, show fderiv ℝ (⇑T) (0 : E) = T from T.fderiv]

omit [CompleteSpace E] in
/-- An invertible linear reference map has nonzero relative degree on any region containing the
origin. -/
theorem localDegreeOn_continuousLinearMap_ne_zero (T : E →L[ℝ] E)
    (hdet : LinearMap.det T.toLinearMap ≠ 0) {U : Set E} (h0 : (0 : E) ∈ U)
    (hfin : ((⇑T) ⁻¹' {(0 : E)} ∩ U).Finite) :
    localDegreeOn (⇑T) 0 U hfin ≠ 0 := by
  rw [localDegreeOn_continuousLinearMap T hdet h0 hfin]
  rcases lt_trichotomy (LinearMap.det T.toLinearMap) 0 with h | h | h
  · rw [sign_neg h]; decide
  · exact absurd h hdet
  · rw [sign_pos h]; decide

omit [CompleteSpace E] in
/-- An invertible linear map has the origin as its unique zero in any region containing it. -/
theorem existsUnique_zero_of_det_ne_zero (T : E →L[ℝ] E)
    (hdet : LinearMap.det T.toLinearMap ≠ 0) {U : Set E} (h0 : (0 : E) ∈ U) :
    ∃! u, u ∈ U ∧ (⇑T) u = 0 := by
  refine ⟨0, ⟨h0, map_zero _⟩, ?_⟩
  intro u hu
  have h1 : equivOfDetNeZero T hdet u = equivOfDetNeZero T hdet 0 := by
    rw [equivOfDetNeZero_apply, equivOfDetNeZero_apply, hu.2, map_zero]
  exact (equivOfDetNeZero T hdet).injective h1

end CRNT
