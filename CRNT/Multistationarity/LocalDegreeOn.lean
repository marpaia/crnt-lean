import CRNT.Multistationarity.DegreeAdditivity

/-!
# The domain-relative local degree

`localDegree` (`CRNT.Multistationarity.DegreeAdditivity`) takes a proof that the **whole**
preimage `f⁻¹{y}` is finite and then sums the orientation signs over `f⁻¹{y} ∩ U`.  Its value
therefore only ever depends on `f⁻¹{y} ∩ U`, but its *type* demands global finiteness.

That mismatch is fatal for the intended application.  A degree certificate on a bounded region
`U` of one stoichiometric compatibility class has to be usable for mass-action fields whose zero
set is infinite away from `U`: any network in which a species occurs in every source complex has
a whole face of the affine chart consisting of zeros, so global finiteness fails while the zero
set inside the positive region stays finite.  See
`CRNT.Theorems.DeficiencyOne.DegreeCertificateObstruction`.

This module introduces `localDegreeOn f y U hfin`, with `hfin : (f ⁻¹' {y} ∩ U).Finite`, and
records that it agrees with `localDegree` whenever the latter is defined.  The two facts that
degree-theoretic existence arguments actually consume — excision and "nonzero degree forces a
solution in `U`" — are proved here for the relative version.

* `localDegreeOn` — the signed count over `f⁻¹{y} ∩ U`, needing only relative finiteness.
* `localDegreeOn_eq_localDegree` — agreement with `localDegree` under global finiteness.
* `localDegreeOn_congr_of_preimage_inter_eq` — excision.
* `localDegreeOn_eq_zero_of_preimage_inter_empty` — a region with no solution has degree `0`.
* `exists_mem_of_localDegreeOn_ne_zero` — nonzero relative degree produces a solution in `U`.
-/

namespace CRNT

open scoped Finset Classical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The domain-relative local degree.**  For a region `U` on which the preimage of `y` is
finite (witnessed by `hfin`), the signed count `∑ x ∈ f⁻¹{y} ∩ U, sign (det (Df x))`.  Unlike
`localDegree` this places no finiteness demand on the preimage outside `U`. -/
noncomputable def localDegreeOn (f : E → E) (y : E) (U : Set E)
    (hfin : (f ⁻¹' {y} ∩ U).Finite) : ℤ :=
  ∑ x ∈ hfin.toFinset,
    ((SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) : SignType) : ℤ)

/-- The relative degree agrees with `localDegree` whenever the whole preimage is finite, so
nothing proved about `localDegree` is lost by working relatively. -/
theorem localDegreeOn_eq_localDegree (f : E → E) (y : E) (U : Set E)
    (hfin : (f ⁻¹' {y}).Finite) (hfin' : (f ⁻¹' {y} ∩ U).Finite) :
    localDegreeOn f y U hfin' = localDegree f y hfin U := by
  unfold localDegreeOn localDegree
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext x
  simp only [Set.Finite.mem_toFinset, Finset.mem_filter, Set.mem_inter_iff]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A global finiteness proof always restricts to a relative one. -/
theorem finite_inter_of_finite (f : E → E) (y : E) (U : Set E)
    (hfin : (f ⁻¹' {y}).Finite) : (f ⁻¹' {y} ∩ U).Finite :=
  hfin.subset Set.inter_subset_left

/-- **Excision.** The relative degree sees only the solutions inside the region. -/
theorem localDegreeOn_congr_of_preimage_inter_eq (f : E → E) (y : E) {U V : Set E}
    (h : f ⁻¹' {y} ∩ U = f ⁻¹' {y} ∩ V)
    (hU : (f ⁻¹' {y} ∩ U).Finite) (hV : (f ⁻¹' {y} ∩ V).Finite) :
    localDegreeOn f y U hU = localDegreeOn f y V hV := by
  unfold localDegreeOn
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext x
  simp only [Set.Finite.mem_toFinset]
  rw [h]

/-- **A region with no solution has relative degree zero.** -/
theorem localDegreeOn_eq_zero_of_preimage_inter_empty (f : E → E) (y : E) {U : Set E}
    (hfin : (f ⁻¹' {y} ∩ U).Finite) (h : f ⁻¹' {y} ∩ U = ∅) :
    localDegreeOn f y U hfin = 0 := by
  unfold localDegreeOn
  rw [Finset.sum_eq_zero]
  intro x hx
  rw [Set.Finite.mem_toFinset, h] at hx
  exact absurd hx (Set.notMem_empty x)

/-- **Existence principle.**  A nonzero relative degree on `U` forces a solution of `f x = y`
inside `U`.  This is the only consequence of degree theory that the deficiency-one existence
argument needs, and it holds with finiteness required only inside `U`. -/
theorem exists_mem_of_localDegreeOn_ne_zero (f : E → E) (y : E) {U : Set E}
    (hfin : (f ⁻¹' {y} ∩ U).Finite) (hdeg : localDegreeOn f y U hfin ≠ 0) :
    ∃ x ∈ U, f x = y := by
  by_contra hnone
  refine hdeg (localDegreeOn_eq_zero_of_preimage_inter_empty f y hfin ?_)
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
    Set.mem_empty_iff_false, iff_false, not_and]
  intro hx hxU
  exact hnone ⟨x, hxU, hx⟩

/-- **Additivity of the relative degree over a finite disjoint cover.**  If the regions `V i`
lie in `U`, are pairwise disjoint over the index finset `T`, and together catch every solution
in `U`, then the relative degree on `U` is the sum of the relative degrees on the pieces.

This is the relative form of `regularDegree_eq_sum_localDegree`, and it is what a
localization argument needs: each piece is handled separately and no finiteness is asked of
anything outside `U`. -/
theorem localDegreeOn_eq_sum_of_disjoint_cover (f : E → E) (y : E) {U : Set E}
    {ι : Type*} (T : Finset ι) (V : ι → Set E) (hVU : ∀ i, V i ⊆ U)
    (hfin : (f ⁻¹' {y} ∩ U).Finite)
    (hcover : ∀ x ∈ f ⁻¹' {y} ∩ U, ∃ i ∈ T, x ∈ V i)
    (hdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → ∀ z, z ∈ V i → z ∈ V j → False) :
    localDegreeOn f y U hfin
      = ∑ i ∈ T, localDegreeOn f y (V i)
          (hfin.subset (Set.inter_subset_inter_right _ (hVU i))) := by
  unfold localDegreeOn
  have hcov : hfin.toFinset
      = T.biUnion fun i =>
          (hfin.subset (Set.inter_subset_inter_right _ (hVU i))).toFinset := by
    ext z
    simp only [Set.Finite.mem_toFinset, Finset.mem_biUnion]
    constructor
    · intro hz
      obtain ⟨i, hiT, hzi⟩ := hcover z hz
      exact ⟨i, hiT, hz.1, hzi⟩
    · rintro ⟨i, _, hzy, hzi⟩
      exact ⟨hzy, hVU i hzi⟩
  rw [hcov, Finset.sum_biUnion]
  intro i hi j hj hij
  refine Finset.disjoint_left.2 fun z hzi hzj => ?_
  rw [Set.Finite.mem_toFinset] at hzi hzj
  exact hdisj i hi j hj hij z hzi.2 hzj.2

/-- **Additivity over a finite disjoint cover, value form.**  The same statement as
`localDegreeOn_eq_sum_of_disjoint_cover`, with the per-piece degrees supplied as values `g i`.
This form avoids carrying finiteness proofs inside the sum, so it composes with results that
produce a piece degree for whatever finiteness witness is at hand. -/
theorem localDegreeOn_eq_sum_of_cover (f : E → E) (y : E) {U : Set E}
    {ι : Type*} (T : Finset ι) (V : ι → Set E) (g : ι → ℤ)
    (hfin : (f ⁻¹' {y} ∩ U).Finite)
    (hVU : ∀ i ∈ T, V i ⊆ U)
    (hcover : ∀ x ∈ f ⁻¹' {y} ∩ U, ∃ i ∈ T, x ∈ V i)
    (hdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → ∀ z, z ∈ V i → z ∈ V j → False)
    (hpiece : ∀ i ∈ T, ∀ h : (f ⁻¹' {y} ∩ V i).Finite, localDegreeOn f y (V i) h = g i) :
    localDegreeOn f y U hfin = ∑ i ∈ T, g i := by
  unfold localDegreeOn
  have hcov : hfin.toFinset = T.biUnion fun i => hfin.toFinset.filter (· ∈ V i) := by
    ext z
    simp only [Set.Finite.mem_toFinset, Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · intro hz
      obtain ⟨i, hiT, hzi⟩ := hcover z hz
      exact ⟨i, hiT, hz, hzi⟩
    · rintro ⟨i, hiT, hz, _⟩
      exact hz
  rw [hcov, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl ?_
    intro i hi
    have hfi : (f ⁻¹' {y} ∩ V i).Finite :=
      hfin.subset (Set.inter_subset_inter_right _ (hVU i hi))
    have hset : hfin.toFinset.filter (· ∈ V i) = hfi.toFinset := by
      ext z
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_inter_iff]
      constructor
      · rintro ⟨hz, hzi⟩
        exact ⟨hz.1, hzi⟩
      · rintro ⟨hzy, hzi⟩
        exact ⟨⟨hzy, hVU i hi hzi⟩, hzi⟩
    rw [hset]
    exact hpiece i hi hfi
  · intro i hi j hj hij
    refine Finset.disjoint_left.2 fun z hzi hzj => ?_
    rw [Finset.mem_filter] at hzi hzj
    exact hdisj i hi j hj hij z hzi.2 hzj.2

/-- The relative degree only depends on the map, not on the finiteness witness, so equal maps
have equal relative degrees.  This is what lets a degree computed for one presentation of a map
be transported to another (`homotopy 0` versus `reference`, say). -/
theorem localDegreeOn_congr_fun {f g : E → E} (h : f = g) (y : E) (U : Set E)
    (hf : (f ⁻¹' {y} ∩ U).Finite) (hg : (g ⁻¹' {y} ∩ U).Finite) :
    localDegreeOn f y U hf = localDegreeOn g y U hg := by
  subst h
  rfl

end CRNT
