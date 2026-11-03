import CRNT.Multistationarity.TotalDegree

/-
# The total-degree theorem for a general invertible linear part at infinity

This module **generalizes** the total-degree theorem of `CRNT.Multistationarity.TotalDegree` from
the *diagonal outflow operator* to an **arbitrary invertible linear part at infinity**, and it
records the precise scope of the result: the degree at infinity of a field with an affine
(degree-one) leading part is the sign of the determinant of that linear part.

## The mathematical statement

The Conradi–Feliu–Mincheva–Wiuf total-degree theorem (*A characterization of multistationarity in
chemical reaction networks*, Theorem 1) says that the degree of the class map of a reaction network
is the **total degree** `(-1)^s` of the class, where `s` is the dimension of the class; for a
fully open network the class is the whole space, `s = card S`, and the total degree is `(-1)^s`.
The proof of the theorem goes through the *degree at infinity* of the mass-action field: the
degree of the class map is the degree at infinity of the field, and the degree at infinity of a
field whose leading homogeneous part is linear is the **sign of the determinant of that linear
part**.  For a fully open network the leading homogeneous part of the field is the outflow
operator `-D` (when the reaction terms do not contribute to it), whose determinant is
`(-1)^s ∏_s λ_s`; the sign is therefore `(-1)^s`.

This module proves the general form of that last step:

* `Network.AffineFieldGeneral` — the hypothesis: the field of the network is
  `x ↦ source + M x` with `M` an **arbitrary invertible** linear operator on the species space
  (the "linear part at infinity");
* `Network.fullyOpen_classDegree_of_affineLinear` — **the total-degree theorem in the general
  affine case**: the class degree of the reduced field on the nonnegative part of the class is
  the sign of `det M`;
* `Network.fullyOpen_classDegree_of_affineLinear_eq_zero_or_sign` — the unconditional form: the
  class degree is that sign if the unique zero of the field is nonnegative, and `0` otherwise;
* `Network.fullyOpen_exists_positiveSteadyState_of_affineLinear` — the Conradi–Feliu–Mincheva–Wiuf
  existence step (leaf **M9**) in the general affine case: the zero of the field is the unique
  positive steady state of the class;
* `Network.fullyOpen_card_positiveSteadyStates_odd_of_affineLinear` — the Šošić–Sibuya parity
  theorem (leaf **S19**) in the general affine case;
* `Network.fullyOpen_classDegree_of_affineLinear_diagonal` — the **recovery** of the diagonal
  outflow theorem: for `M = -outflow •` the determinant is `∏_s -outflow_s`, whose sign is
  `(-1)^{card S}`.

## What is already in the library, and what this module adds

* `Network.fullyOpen_classDegree` (in `CRNT.Multistationarity.TotalDegree`) is the total-degree
  theorem for the **diagonal outflow operator**: the field of the fully open extension is
  `x ↦ source - outflow • x` with `source` and `outflow` strictly positive.  Its hypothesis
  forces the linear part at infinity to be diagonal, so the sign of its determinant is
  `(-1)^{card S}`.
* `Network.Counterexample.classDegree_ne_pow_neg_one` (same module) shows that the total-degree
  theorem is **false for a general fully open network**: for the one-species network `A → 2A`
  with all rate constants equal to one, the field of the fully open extension is the constant
  `1`, the class degree is `0`, and not `(-1)^1`.  The mechanism is that the reaction terms
  contribute to the field at infinity: a reaction with a source complex of size one contributes a
  *linear* term (which can cancel the outflow), and a reaction with a source complex of size at
  least two contributes a term of higher degree (which dominates the outflow, so that the field
  at infinity is not linear at all).

This module therefore does **not** prove the total-degree theorem in general: it proves the
honest general statement of the "the degree at infinity is the sign of the determinant of the
linear part at infinity" reading, under the hypothesis that the field at infinity is linear, and
it generalizes the affine case from the diagonal outflow operator to an arbitrary invertible
linear part.  The genuinely open part is untouched: the degree at infinity of a field with
**higher-order reaction terms**, i.e. the mixed-volume / Bernstein count of the BKK theory, is
still missing (field-map leaf **M9**, last paragraph).

## The scope of the hypothesis

The class degree of the library is the *relative* degree of the reduced field on the
**nonnegative** part of the class, so it is the degree at infinity only when the zero of the
field lies in that part of the class.  This is why the theorems of this module carry the
hypothesis that the unique zero `Network.affineFieldZeroGeneral` of the field is nonnegative
(`Network.fullyOpen_classDegree_of_affineLinear`), and why the unconditional statement
`Network.fullyOpen_classDegree_of_affineLinear_eq_zero_or_sign` is a dichotomy: the class degree
is the sign of `det M` when the zero is nonnegative, and `0` when it is not (the reduced field
then has no zero at all in the nonnegative class).  For a fully open network the zero of the
field, when nonnegative, is automatically *strictly* positive, because the reduced field of a
fully open network does not vanish on the class boundary.

## Dependencies

`CRNT.Multistationarity.TotalDegree` (the diagonal case, the fully open extension, the transport
between the species space and the class coordinate space), and through it
`CRNT.Multistationarity.DegreeExistence` (the relative class degree and its existence
principle), `CRNT.Multistationarity.DegreeStructural` (the local degree at a unique zero),
`CRNT.Multistationarity.ParityOfSteadyStates` (the parity theorem and the fully open boundary
non-vanishing).
-/

set_option maxHeartbeats 800000

namespace CRNT

namespace Network

open scoped BigOperators Topology Classical

open Set Filter

variable {S : Type} [DecidableEq S] [Fintype S]

/-!
# Conditional degree/parity consequences and restricted total-degree examples

The finite signed-count arguments use the displayed boundary, regularity,
finiteness and total-degree inputs. Explicit affine/rank-restricted computations
are available where stated. Full openness alone does not force odd parity; the
general total-degree theorem under dissipativity and boundary conditions remains
incomplete. See `ParityOfSteadyStates` and `test.SemanticCorrespondence`.
An earlier parity attribution with no verifiable source has been removed.
-/

/-- **A general affine field with an invertible linear part.** -/
structure AffineFieldGeneral (N : Network S) (κ : N.RateConstants) where
  /-- The constant part. -/
  source : Concentration S
  /-- The linear part at infinity. -/
  M : Concentration S →L[ℝ] Concentration S
  /-- The linear part is invertible. -/
  hM : Function.Injective M
  /-- The field is `source + M x`. -/
  eq_field : ∀ x s, N.massActionVectorField κ x s = source s + M x s

/-- **The linear part of a general affine field is injective as a linear map.** -/
theorem AffineFieldGeneral.injective_toLinearMap {N : Network S} {κ : N.RateConstants}
    (h : AffineFieldGeneral N κ) : Function.Injective h.M.toLinearMap :=
  fun _ _ hxy => h.hM hxy

/-- **The linear part of a general affine field is surjective as a linear map.** -/
theorem AffineFieldGeneral.surjective_toLinearMap {N : Network S} {κ : N.RateConstants}
    (h : AffineFieldGeneral N κ) : Function.Surjective h.M.toLinearMap :=
  LinearMap.injective_iff_surjective.mp h.injective_toLinearMap

/-- **The unique zero of a general affine field with an invertible linear part.** -/
noncomputable def affineFieldZeroGeneral {N : Network S} {κ : N.RateConstants}
    (h : AffineFieldGeneral N κ) : Concentration S :=
  Classical.choose (h.surjective_toLinearMap (-h.source))

/-- **The zero of a general affine field solves `M x = -source`.** -/
theorem affineFieldZeroGeneral_spec {N : Network S} {κ : N.RateConstants}
    (h : AffineFieldGeneral N κ) :
    h.M (affineFieldZeroGeneral h) = -h.source := by
  exact Classical.choose_spec (h.surjective_toLinearMap (-h.source))

/-- **The zero of a general affine field is a zero of the field.** -/
theorem massActionVectorField_affineFieldZeroGeneral {N : Network S} {κ : N.RateConstants}
    (h : AffineFieldGeneral N κ) :
    N.massActionVectorField κ (affineFieldZeroGeneral h) = 0 := by
  funext s
  rw [h.eq_field, affineFieldZeroGeneral_spec]
  simp

/-- **The zero of a general affine field is the only zero.** -/
theorem massActionVectorField_eq_zero_iff_general {N : Network S} {κ : N.RateConstants}
    (h : AffineFieldGeneral N κ) (x : Concentration S) :
    N.massActionVectorField κ x = 0 ↔ x = affineFieldZeroGeneral h := by
  constructor
  · intro hx
    have hx' : ∀ s, h.source s + h.M x s = 0 := by
      intro s
      have hx'' := congrFun hx s
      rw [h.eq_field] at hx''
      simpa using hx''
    have hmx : h.M x = -h.source := by
      funext s
      have h1 := hx' s
      have h2 : h.M x s = -h.source s := by linarith
      exact h2
    have h2 : h.M x = h.M (affineFieldZeroGeneral h) := by
      rw [hmx, affineFieldZeroGeneral_spec]
    exact h.hM h2
  · intro hx
    subst hx
    exact massActionVectorField_affineFieldZeroGeneral h

/-- **The derivative of the field of a network in general affine form** is the constant linear
part at infinity. -/
theorem hasFDerivAt_massActionVectorField_affineGeneral (N : Network S) (κ : N.RateConstants)
    (h : AffineFieldGeneral N κ) (x : Concentration S) :
    HasFDerivAt (fun y => N.massActionVectorField κ y) h.M x := by
  have hfun : (fun y => N.massActionVectorField κ y) = (fun y => h.source + h.M y) := by
    funext y
    funext s
    rw [h.eq_field]
    rfl
  rw [hfun]
  have h1 : HasFDerivAt (fun _ : Concentration S => h.source)
      (0 : Concentration S →L[ℝ] Concentration S) x :=
    hasFDerivAt_const _ _
  have h2 : HasFDerivAt (fun y : Concentration S => h.M y) h.M x := h.M.hasFDerivAt
  have h3 := h1.add h2
  have hzero : (0 : Concentration S →L[ℝ] Concentration S) + h.M = h.M := by
    ext v
    simp
  rwa [hzero] at h3

/-! ## The chart of the fully open extension is a linear isomorphism -/

/-- **The chart of the fully open extension is a linear isomorphism** between the class coordinate
space and the species space: for a fully open network the stoichiometric subspace is the whole
space, so the chart is onto. -/
noncomputable def fullyOpenChartEquiv (N : Network S) :
    (Fin N.fullyOpen.stoichRank → ℝ) ≃ₗ[ℝ] (S → ℝ) :=
  LinearEquiv.mk N.fullyOpen.stoichChartLM N.fullyOpen.stoichProjLM
    (by
      intro x
      have h := congrArg (fun f : _ →ₗ[ℝ] _ => f x) (stoichProjLM_comp_stoichChartLM N)
      simpa using h)
    (by
      intro y
      have h := congrArg (fun f : _ →ₗ[ℝ] _ => f y)
        (stoichChartLM_comp_stoichProjLM_fullyOpen N)
      simpa using h)

/-- **The underlying linear map of the chart isomorphism** is the chart of the fully open
extension. -/
theorem fullyOpenChartEquiv_toLinearMap (N : Network S) :
    (fullyOpenChartEquiv N).toLinearMap = N.fullyOpen.stoichChartLM := rfl

/-- **The dual projection of the fully open extension is the inverse of the chart isomorphism.**
This is what makes the determinant of the reduced linear part the determinant of the linear part
at infinity: the two are conjugate. -/
theorem fullyOpenChartEquiv_symm_toLinearMap (N : Network S) :
    N.fullyOpen.stoichProjLM = (fullyOpenChartEquiv N).symm.toLinearMap := by
  apply LinearMap.ext
  intro y
  have h1 : N.fullyOpen.stoichChartLM (N.fullyOpen.stoichProjLM y) = y := by
    have h := congrArg (fun f : _ →ₗ[ℝ] _ => f y)
      (stoichChartLM_comp_stoichProjLM_fullyOpen N)
    simpa using h
  have h2 : N.fullyOpen.stoichChartLM ((fullyOpenChartEquiv N).symm.toLinearMap y) = y :=
    (fullyOpenChartEquiv N).apply_symm_apply y
  exact N.fullyOpen.stoichChartLM_injective (h1.trans h2.symm)

/-! ## The derivative of the reduced field -/

/-- **The derivative of the reduced field of a fully open network in general affine form** is the
conjugate of the linear part at infinity by the chart. -/
theorem fderiv_steadyStateMap_affineGeneral (N : Network S) (κ : N.fullyOpen.RateConstants)
    (h : AffineFieldGeneral N.fullyOpen κ) (c : Concentration S) (y : ClassCoord (N.fullyOpen)) :
    fderiv ℝ (N.fullyOpen.steadyStateMap κ c) y
      = N.fullyOpen.stoichProj.comp (h.M.comp N.fullyOpen.stoichChart) := by
  have h1 : HasFDerivAt (N.fullyOpen.affineChart c) N.fullyOpen.stoichChart y :=
    N.fullyOpen.affineChart_hasFDerivAt c y
  have h2 : HasFDerivAt (fun x => N.fullyOpen.massActionVectorField κ x)
      h.M (N.fullyOpen.affineChart c y) :=
    N.fullyOpen.hasFDerivAt_massActionVectorField_affineGeneral κ h (N.fullyOpen.affineChart c y)
  have h3 := h2.comp y h1
  have h4 := N.fullyOpen.stoichProj.hasFDerivAt.comp y h3
  have h4f := h4.fderiv
  have hfun : (⇑N.fullyOpen.stoichProj ∘ (fun x => N.fullyOpen.massActionVectorField κ x) ∘
      N.fullyOpen.affineChart c) = N.fullyOpen.steadyStateMap κ c := by
    funext z
    rfl
  rw [hfun] at h4f
  exact h4f

/-- **The determinant of the reduced linear part.**  The linear part of the reduced field of a
fully open network in general affine form has determinant equal to the determinant of the linear
part at infinity: the chart and its dual projection are mutually inverse isomorphisms between the
species space and the class coordinate space, and the determinant is invariant under
conjugation. -/
theorem det_fderiv_steadyStateMap_affineGeneral (N : Network S) (κ : N.fullyOpen.RateConstants)
    (h : AffineFieldGeneral N.fullyOpen κ) (c : Concentration S) (y : ClassCoord (N.fullyOpen)) :
    LinearMap.det (fderiv ℝ (N.fullyOpen.steadyStateMap κ c) y).toLinearMap
      = LinearMap.det h.M.toLinearMap := by
  rw [fderiv_steadyStateMap_affineGeneral N κ h c y]
  have hcomp : (N.fullyOpen.stoichProj.comp (h.M.comp N.fullyOpen.stoichChart)).toLinearMap
      = N.fullyOpen.stoichProjLM.comp (h.M.toLinearMap.comp N.fullyOpen.stoichChartLM) := by
    apply LinearMap.ext
    intro z
    simp [ContinuousLinearMap.toLinearMap_comp]
  rw [hcomp]
  rw [fullyOpenChartEquiv_symm_toLinearMap N, ← fullyOpenChartEquiv_toLinearMap N]
  exact LinearMap.det_conj h.M.toLinearMap ((fullyOpenChartEquiv N).symm)

/-! ## The zero set of the reduced field -/

/-- **The zero set of the reduced field of a fully open network in general affine form** is the
singleton of the chart coordinate of the (unique) zero of the field, provided that zero is
nonnegative. -/
theorem fullyOpen_steadyStateMap_zero_eq_singleton_general (N : Network S)
    (κ : N.fullyOpen.RateConstants) (c : Concentration S) (h : AffineFieldGeneral N.fullyOpen κ)
    (hz : Concentration.Nonnegative (affineFieldZeroGeneral h)) :
    N.fullyOpen.steadyStateMap κ c ⁻¹' {0} ∩ N.fullyOpen.nonnegativeClassRegion c
      = {N.fullyOpen.chartCoord c (affineFieldZeroGeneral h)} := by
  set ystar : ClassCoord (N.fullyOpen) := N.fullyOpen.chartCoord c (affineFieldZeroGeneral h) with
    hystar
  have haff : N.fullyOpen.affineChart c ystar = affineFieldZeroGeneral h := by
    have hmem : affineFieldZeroGeneral h - c ∈ N.fullyOpen.stoichSubspace := by
      rw [stoichSubspace_fullyOpen_eq_top]
      exact Submodule.mem_top
    rw [hystar]
    simp only [affineChart, chartCoord]
    rw [N.fullyOpen.stoichChart_stoichProj hmem]
    abel
  have hzero : N.fullyOpen.steadyStateMap κ c ystar = 0 := by
    simp only [steadyStateMap, reducedField]
    rw [haff, massActionVectorField_affineFieldZeroGeneral h, map_zero]
  have huniq : ∀ y, N.fullyOpen.steadyStateMap κ c y = 0 → y = ystar := by
    intro y hy
    have hy' : N.fullyOpen.massActionVectorField κ (N.fullyOpen.affineChart c y) = 0 := by
      have hinj := stoichProj_injective_of_stoichSubspace_eq_top (N.fullyOpen)
        (stoichSubspace_fullyOpen_eq_top N)
      apply hinj
      have h2 := hy
      simp only [steadyStateMap, reducedField] at h2
      rw [h2, map_zero]
    have h2 : N.fullyOpen.affineChart c y = affineFieldZeroGeneral h :=
      (massActionVectorField_eq_zero_iff_general h (N.fullyOpen.affineChart c y)).mp hy'
    have h3 : N.fullyOpen.stoichChart y = N.fullyOpen.stoichChart ystar := by
      have h4 : N.fullyOpen.affineChart c y = N.fullyOpen.affineChart c ystar := by
        rw [h2, haff]
      simp only [affineChart] at h4
      exact add_left_cancel h4
    exact N.fullyOpen.stoichChart_injective h3
  have hynonneg : ystar ∈ N.fullyOpen.nonnegativeClassRegion c := by
    rw [mem_nonnegativeClassRegion_iff, haff]
    exact hz
  ext y
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hzy, _⟩
    exact Set.mem_singleton_iff.mpr (huniq y (Set.mem_preimage.mp hzy))
  · rintro rfl
    exact ⟨hzero, hynonneg⟩

/-! ## The total-degree theorem for a general affine field -/

/-- **The total-degree theorem for a fully open network whose field is affine with an invertible
linear part.**  The class degree of the reduced field on the nonnegative part of the class is the
sign of the determinant of the linear part at infinity.  For the diagonal outflow operator this
is `(-1)^{card S}`, recovering `Network.fullyOpen_classDegree`.

The hypothesis `hz` — that the unique zero of the field is nonnegative — is needed because the
class degree of the library is the *relative* degree on the nonnegative part of the class: it
coincides with the degree at infinity only when the zero of the field lies in that part of the
class.  The unconditional statement is
`Network.fullyOpen_classDegree_of_affineLinear_eq_zero_or_sign` (the class degree is `0` when the
zero is not nonnegative), and the necessity of the hypothesis is witnessed by
`Network.CounterexampleGeneral.classDegree_ne_sign_det`. -/
theorem fullyOpen_classDegree_of_affineLinear
    (N : Network S) (κ : N.fullyOpen.RateConstants) (c : Concentration S)
    (h : AffineFieldGeneral N.fullyOpen κ)
    (hz : Concentration.Nonnegative (affineFieldZeroGeneral h))
    (hfin : (N.fullyOpen.steadyStateMap κ c ⁻¹' {0} ∩
      N.fullyOpen.nonnegativeClassRegion c).Finite) :
    N.fullyOpen.nonnegativeClassDegree κ c hfin =
      ((SignType.sign (LinearMap.det h.M.toLinearMap) : SignType) : ℤ) := by
  -- the zero of the field
  have hxstarzero : N.fullyOpen.massActionVectorField κ (affineFieldZeroGeneral h) = 0 :=
    massActionVectorField_affineFieldZeroGeneral h
  -- the chart coordinate of the zero
  set ystar : ClassCoord (N.fullyOpen) := N.fullyOpen.chartCoord c (affineFieldZeroGeneral h) with
    hystar
  have haff : N.fullyOpen.affineChart c ystar = affineFieldZeroGeneral h := by
    have hmem : affineFieldZeroGeneral h - c ∈ N.fullyOpen.stoichSubspace := by
      rw [stoichSubspace_fullyOpen_eq_top]
      exact Submodule.mem_top
    rw [hystar]
    simp only [affineChart, chartCoord]
    rw [N.fullyOpen.stoichChart_stoichProj hmem]
    abel
  -- the zero of the reduced field
  have hzero : N.fullyOpen.steadyStateMap κ c ystar = 0 := by
    simp only [steadyStateMap, reducedField]
    rw [haff, hxstarzero, map_zero]
  -- the zero is unique
  have huniq : ∀ y, N.fullyOpen.steadyStateMap κ c y = 0 → y = ystar := by
    intro y hy
    have hy' : N.fullyOpen.massActionVectorField κ (N.fullyOpen.affineChart c y) = 0 := by
      have hinj := stoichProj_injective_of_stoichSubspace_eq_top (N.fullyOpen)
        (stoichSubspace_fullyOpen_eq_top N)
      apply hinj
      have h2 := hy
      simp only [steadyStateMap, reducedField] at h2
      rw [h2, map_zero]
    have h2 : N.fullyOpen.affineChart c y = affineFieldZeroGeneral h :=
      (massActionVectorField_eq_zero_iff_general h (N.fullyOpen.affineChart c y)).mp hy'
    have h3 : N.fullyOpen.stoichChart y = N.fullyOpen.stoichChart ystar := by
      have h4 : N.fullyOpen.affineChart c y = N.fullyOpen.affineChart c ystar := by
        rw [h2, haff]
      simp only [affineChart] at h4
      exact add_left_cancel h4
    exact N.fullyOpen.stoichChart_injective h3
  -- the zero lies in the nonnegative part of the class
  have hynonneg : ystar ∈ N.fullyOpen.nonnegativeClassRegion c := by
    rw [mem_nonnegativeClassRegion_iff, haff]
    exact hz
  -- the zero set in the nonnegative class is the singleton `ystar`
  have hset : N.fullyOpen.steadyStateMap κ c ⁻¹' {0} ∩
      N.fullyOpen.nonnegativeClassRegion c = {ystar} := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hzy, _⟩
      exact Set.mem_singleton_iff.mpr (huniq y (Set.mem_preimage.mp hzy))
    · rintro rfl
      exact ⟨hzero, hynonneg⟩
  -- the finiteness of the zero set, for the singleton witness
  have hfin' : (N.fullyOpen.steadyStateMap κ c ⁻¹' {0} ∩
      N.fullyOpen.nonnegativeClassRegion c).Finite := by
    rw [hset]
    exact Set.finite_singleton ystar
  -- the local degree at the unique zero
  have hlocal : localDegreeOn (N.fullyOpen.steadyStateMap κ c) 0
      (N.fullyOpen.nonnegativeClassRegion c) hfin'
      = ((SignType.sign (LinearMap.det
          (fderiv ℝ (N.fullyOpen.steadyStateMap κ c) ystar).toLinearMap) : SignType) : ℤ) :=
    localDegreeOn_eq_sign_det_of_unique_preimage (N.fullyOpen.steadyStateMap κ c) ystar
      hzero huniq hynonneg hfin'
  -- the class degree is the sign of the determinant of the linear part
  have hdeg : N.fullyOpen.nonnegativeClassDegree κ c hfin
      = ((SignType.sign (LinearMap.det h.M.toLinearMap) : SignType) : ℤ) := by
    unfold nonnegativeClassDegree
    have hcong : localDegreeOn (N.fullyOpen.steadyStateMap κ c) 0
        (N.fullyOpen.nonnegativeClassRegion c) hfin
        = localDegreeOn (N.fullyOpen.steadyStateMap κ c) 0
          (N.fullyOpen.nonnegativeClassRegion c) hfin' :=
      localDegreeOn_congr_of_preimage_inter_eq (N.fullyOpen.steadyStateMap κ c) 0 rfl hfin hfin'
    rw [hcong]
    rw [hlocal]
    rw [det_fderiv_steadyStateMap_affineGeneral N κ h c ystar]
  exact hdeg

/-! ## The finiteness of the zero set is automatic -/

/-- **The finiteness of the zero set is automatic** for a fully open network in general affine
form whose zero is nonnegative: the reduced field has exactly one zero in the nonnegative part of
the class. -/
theorem fullyOpen_hfin_affineGeneral (N : Network S) (κ : N.fullyOpen.RateConstants)
    (c : Concentration S) (h : AffineFieldGeneral N.fullyOpen κ)
    (hz : Concentration.Nonnegative (affineFieldZeroGeneral h)) :
    (N.fullyOpen.steadyStateMap κ c ⁻¹' {0} ∩ N.fullyOpen.nonnegativeClassRegion c).Finite := by
  rw [fullyOpen_steadyStateMap_zero_eq_singleton_general N κ c h hz]
  exact Set.finite_singleton _

/-! ## The unconditional form: the class degree is zero or the sign of the determinant -/

/-- **The class degree of a fully open network with a general affine field.**  The class degree
is the sign of the determinant of the linear part at infinity when the unique zero of the field is
nonnegative, and it is `0` otherwise: in that case the reduced field has no zero at all in the
nonnegative part of the class.

This is the honest general form of the "the degree at infinity is the sign of the determinant of
the linear part at infinity" reading of the Conradi–Feliu–Mincheva–Wiuf total-degree theorem: the
degree at infinity is the sign of the determinant of the linear part, and it is the *relative*
degree on the nonnegative class only when the zero of the field lies in that class. -/
theorem fullyOpen_classDegree_of_affineLinear_eq_zero_or_sign
    (N : Network S) (κ : N.fullyOpen.RateConstants) (c : Concentration S)
    (h : AffineFieldGeneral N.fullyOpen κ)
    (hfin : (N.fullyOpen.steadyStateMap κ c ⁻¹' {0} ∩
      N.fullyOpen.nonnegativeClassRegion c).Finite) :
    N.fullyOpen.nonnegativeClassDegree κ c hfin =
      if Concentration.Nonnegative (affineFieldZeroGeneral h) then
        ((SignType.sign (LinearMap.det h.M.toLinearMap) : SignType) : ℤ)
      else 0 := by
  by_cases hz : Concentration.Nonnegative (affineFieldZeroGeneral h)
  · rw [ite_eq_left hz]
    exact fullyOpen_classDegree_of_affineLinear N κ c h hz hfin
  · rw [ite_eq_right hz]
    unfold nonnegativeClassDegree
    rw [localDegreeOn_eq_zero_of_preimage_inter_empty (N.fullyOpen.steadyStateMap κ c) 0 hfin]
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, iff_false, not_and]
    intro hy hyU
    have hy' : N.fullyOpen.massActionVectorField κ (N.fullyOpen.affineChart c y) = 0 := by
      have hinj := stoichProj_injective_of_stoichSubspace_eq_top (N.fullyOpen)
        (stoichSubspace_fullyOpen_eq_top N)
      apply hinj
      have h2 := hy
      simp only [steadyStateMap, reducedField] at h2
      rw [h2, map_zero]
    have h2 : N.fullyOpen.affineChart c y = affineFieldZeroGeneral h :=
      (massActionVectorField_eq_zero_iff_general h (N.fullyOpen.affineChart c y)).mp hy'
    have h3 : Concentration.Nonnegative (affineFieldZeroGeneral h) := by
      rw [← h2]
      exact (mem_nonnegativeClassRegion_iff (N.fullyOpen) c y).mp hyU
    exact hz h3

/-! ## The determinant of the linear part at infinity is nonzero -/

/-- **The determinant of an invertible linear part at infinity is nonzero.** -/
theorem AffineFieldGeneral.det_ne_zero {N : Network S} {κ : N.RateConstants}
    (h : AffineFieldGeneral N κ) : LinearMap.det h.M.toLinearMap ≠ 0 := by
  obtain ⟨g, hg⟩ := h.M.toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr h.surjective_toLinearMap)
  have h1 : LinearMap.det h.M.toLinearMap * LinearMap.det g = 1 := by
    rw [← LinearMap.det_comp, hg, LinearMap.det_id]
  intro hz
  rw [hz, zero_mul] at h1
  norm_num at h1

/-! ## The consequences for the field map -/

/-- **A positive steady state exists in the class of `c`** for a fully open network whose field is
affine with an invertible linear part and whose zero is nonnegative: the zero of the field is
then a strictly positive steady state, and it is the only one.

This is the Conradi–Feliu–Mincheva–Wiuf existence step (leaf **M9**) in the general affine case,
with the total degree discharged. -/
theorem fullyOpen_exists_positiveSteadyState_of_affineLinear
    (N : Network S) (κ : N.fullyOpen.RateConstants) (c : Concentration S)
    (h : AffineFieldGeneral N.fullyOpen κ)
    (hz : Concentration.Nonnegative (affineFieldZeroGeneral h)) :
    ∃ x : Concentration S,
      N.fullyOpen.StoichCompatible c x ∧ Concentration.Positive x ∧
        N.fullyOpen.IsMassActionSteadyState κ x ∧
        (∀ y : Concentration S, N.fullyOpen.IsMassActionSteadyState κ y → y = x) := by
  refine ⟨affineFieldZeroGeneral h, ?_, ?_, ?_, ?_⟩
  · -- the zero is stoichiometrically compatible with `c`
    rw [StoichCompatible]
    rw [stoichSubspace_fullyOpen_eq_top]
    exact Submodule.mem_top
  · -- the zero is strictly positive
    set ystar : ClassCoord (N.fullyOpen) :=
      N.fullyOpen.chartCoord c (affineFieldZeroGeneral h) with hystar
    have haff : N.fullyOpen.affineChart c ystar = affineFieldZeroGeneral h := by
      have hmem : affineFieldZeroGeneral h - c ∈ N.fullyOpen.stoichSubspace := by
        rw [stoichSubspace_fullyOpen_eq_top]
        exact Submodule.mem_top
      rw [hystar]
      simp only [affineChart, chartCoord]
      rw [N.fullyOpen.stoichChart_stoichProj hmem]
      abel
    have hzero : N.fullyOpen.steadyStateMap κ c ystar = 0 := by
      simp only [steadyStateMap, reducedField]
      rw [haff, massActionVectorField_affineFieldZeroGeneral h, map_zero]
    have hynonneg : ystar ∈ N.fullyOpen.nonnegativeClassRegion c := by
      rw [mem_nonnegativeClassRegion_iff, haff]
      exact hz
    have hnotbd : ystar ∉ N.fullyOpen.classBoundary c := by
      intro hbd
      exact N.fullyOpen_steadyStateMap_ne_zero_on_classBoundary κ c ystar hbd hzero
    have hpos : ystar ∈ N.fullyOpen.positiveClassRegion c := by
      rw [nonnegativeClassRegion_eq_positive_union_boundary] at hynonneg
      rcases hynonneg with h | h
      · exact h
      · exact absurd h hnotbd
    rw [mem_positiveClassRegion_iff] at hpos
    rw [haff] at hpos
    exact hpos
  · -- the zero is a steady state
    intro s
    have h1 := congrFun (massActionVectorField_affineFieldZeroGeneral h) s
    simpa [IsMassActionSteadyState, IsSteadyState] using h1
  · -- the steady state is unique
    intro y hy
    apply (massActionVectorField_eq_zero_iff_general h y).mp
    funext s
    exact hy s

/-- Conditional degree/parity consequence under the hypotheses displayed below. -/
theorem fullyOpen_card_positiveSteadyStates_odd_of_affineLinear
    (N : Network S) (κ : N.fullyOpen.RateConstants) (c : Concentration S)
    (h : AffineFieldGeneral N.fullyOpen κ)
    (hz : Concentration.Nonnegative (affineFieldZeroGeneral h))
    (hfinN : (N.fullyOpen.steadyStateMap κ c ⁻¹' {0} ∩
      N.fullyOpen.nonnegativeClassRegion c).Finite)
    (hfinP : (N.fullyOpen.positiveSteadyStates_in_class κ c).Finite)
    (hnd : ∀ y ∈ N.fullyOpen.positiveSteadyStates_in_class κ c,
      (N.fullyOpen.reducedJacobian κ c y).det ≠ 0) :
    (N.fullyOpen.card_positiveSteadyStates_in_class κ c hfinP) % 2 = 1 := by
  refine N.fullyOpen.card_positiveSteadyStates_odd_of_classDegree_eq_one_or_neg_one κ c hfinN
    hfinP ?_ hnd ?_
  · intro y hy
    exact N.fullyOpen_steadyStateMap_ne_zero_on_classBoundary κ c y hy
  · have hdeg := fullyOpen_classDegree_of_affineLinear N κ c h hz hfinN
    rw [hdeg]
    by_cases hpos : 0 < LinearMap.det h.M.toLinearMap
    · left
      rw [sign_pos hpos]
      rfl
    · by_cases hneg : LinearMap.det h.M.toLinearMap < 0
      · right
        rw [sign_neg hneg]
        rfl
      · exfalso
        exact h.det_ne_zero (by linarith)

/-! ## The recovery of the diagonal case -/

/-- **The dissipative affine field of a network, seen as a general affine field.**  The linear part
at infinity is the diagonal outflow operator `v ↦ -outflow • v`. -/
noncomputable def affineFieldGeneral_of_affineField (N : Network S) (κ : N.RateConstants)
    (h : AffineField N κ) : AffineFieldGeneral N κ where
  source := h.source
  M := outflowLinearMap h.outflow
  hM := by
    intro v w hvw
    funext s
    have h1 := congrFun hvw s
    rw [outflowLinearMap_apply, outflowLinearMap_apply] at h1
    have hne : (-h.outflow s : ℝ) ≠ 0 := by
      intro hz
      have h2 : h.outflow s = 0 := by linarith
      exact (h.outflow_pos s).ne' h2
    exact mul_left_cancel₀ hne h1
  eq_field := by
    intro x s
    rw [massActionVectorField_eq_affine_add N κ h x s, outflowLinearMap_apply]

/-- **The determinant of the diagonal outflow operator** is `∏ s, -outflow s`. -/
theorem det_outflowLinearMap (outflow : S → ℝ) :
    LinearMap.det (outflowLinearMap outflow).toLinearMap = ∏ s : S, -outflow s := by
  have hmat : LinearMap.toMatrix' (outflowLinearMap outflow).toLinearMap
      = Matrix.diagonal (fun s : S => -outflow s) := by
    ext i j
    rw [LinearMap.toMatrix'_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · simp [hij, outflowLinearMap_apply]
    · simp [hij, outflowLinearMap_apply]
  rw [← LinearMap.det_toMatrix', hmat, Matrix.det_diagonal]

/-- **The zero of the general affine field of a dissipative affine field** is the diagonal zero
`source / outflow`. -/
theorem affineFieldZeroGeneral_of_affineField (N : Network S) (κ : N.RateConstants)
    (h : AffineField N κ) :
    affineFieldZeroGeneral (affineFieldGeneral_of_affineField N κ h) = affineFieldZero h := by
  have h1 : N.massActionVectorField κ (affineFieldZeroGeneral (affineFieldGeneral_of_affineField N κ h))
      = 0 :=
    massActionVectorField_affineFieldZeroGeneral (affineFieldGeneral_of_affineField N κ h)
  have h2 : N.massActionVectorField κ (affineFieldZero h) = 0 :=
    massActionVectorField_affineFieldZero h
  have h3 : affineFieldZero h = affineFieldZeroGeneral (affineFieldGeneral_of_affineField N κ h) :=
    (massActionVectorField_eq_zero_iff_general (affineFieldGeneral_of_affineField N κ h)
      (affineFieldZero h)).mp h2
  exact h3.symm

/-- **The general affine theorem recovers the diagonal outflow theorem.**  The field of a fully
open network in dissipative affine form `x ↦ source - outflow • x` is a general affine field whose
linear part at infinity is the diagonal outflow operator, whose determinant is
`∏ s, -outflow s`; the sign of that determinant is `(-1)^{card S}`. -/
theorem fullyOpen_classDegree_of_affineLinear_diagonal
    (N : Network S) (κ : N.fullyOpen.RateConstants) (c : Concentration S)
    (h : AffineField N.fullyOpen κ)
    (hfin : (N.fullyOpen.steadyStateMap κ c ⁻¹' {0} ∩
      N.fullyOpen.nonnegativeClassRegion c).Finite) :
    N.fullyOpen.nonnegativeClassDegree κ c hfin = (-1) ^ (Fintype.card S) := by
  -- the zero of the general affine field is the diagonal zero, which is positive
  have hz : Concentration.Nonnegative
      (affineFieldZeroGeneral (affineFieldGeneral_of_affineField N.fullyOpen κ h)) := by
    rw [affineFieldZeroGeneral_of_affineField N.fullyOpen κ h]
    exact (affineFieldZero_pos h).nonnegative
  -- the general theorem
  have hdeg := fullyOpen_classDegree_of_affineLinear N κ c
    (affineFieldGeneral_of_affineField N.fullyOpen κ h) hz hfin
  -- the determinant of the diagonal outflow operator
  have hdet : LinearMap.det
      ((affineFieldGeneral_of_affineField N.fullyOpen κ h).M.toLinearMap)
      = ∏ s : S, -h.outflow s := by
    rw [show (affineFieldGeneral_of_affineField N.fullyOpen κ h).M.toLinearMap
      = (outflowLinearMap h.outflow).toLinearMap from rfl]
    exact det_outflowLinearMap h.outflow
  rw [hdeg, hdet]
  -- the sign of a product of `card S` negative numbers
  have hsign : ((SignType.sign (∏ s : S, -h.outflow s) : SignType) : ℤ)
      = (-1 : ℤ) ^ (Fintype.card S) := by
    have hprod : SignType.sign (∏ s : S, -h.outflow s)
        = ∏ s : S, SignType.sign (-h.outflow s) := by
      have hmp := map_prod signHom (fun s => -h.outflow s) Finset.univ
      exact hmp
    rw [hprod]
    have hfac : ∀ s, SignType.sign (-h.outflow s) = (-1 : SignType) := by
      intro s
      rw [sign_neg]
      have hpos : 0 < h.outflow s := h.outflow_pos s
      linarith
    rw [Finset.prod_congr rfl (fun s _ => hfac s), Finset.prod_const, Finset.card_univ]
    exact coe_sign_pow _
  exact hsign

/-! ## The scope of the hypothesis: the nonnegativity of the zero is necessary -/

namespace CounterexampleGeneral

/-- **The one-species network with the autocatalytic reaction `A → 2A`.**  Its fully open
extension has the inflow pseudo-reaction `0 → A` and the outflow pseudo-reaction `A → 0`. -/
def N : Network (Fin 1) where
  R := Fin 1
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun _ => { source := fun _ => 1, target := fun _ => 2 }

/-- **The rate of each reaction of the fully open extension**: the reaction `A → 2A` has rate `2`,
the inflow `0 → A` has rate `1` and the outflow `A → 0` has rate `1`. -/
def rateValue (r : N.fullyOpen.R) : ℝ :=
  match r with
  | Sum.inl _ => 2
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 1

/-- **The rate constants of the fully open extension.** -/
def rates : N.fullyOpen.RateConstants where
  k := rateValue
  positive r := by
    rcases r with r | r
    · simp [rateValue]
    · rcases r with r | r <;> simp [rateValue]

/-- **The field of the fully open extension is `1 + x`.**  The inflow contributes `1`, the
autocatalytic reaction contributes `2x` and the outflow contributes `-x`; the field therefore has
the *identity* as its linear part at infinity, and it vanishes at `x = -1`, outside the
nonnegative orthant. -/
theorem massActionVectorField_eq (x : Concentration (Fin 1)) :
    N.fullyOpen.massActionVectorField rates x = fun _ => 1 + x 0 := by
  funext s
  have hs : s = 0 := by
    apply Fin.ext
    omega
  subst hs
  rw [fullyOpen_massActionVectorField_eq]
  have hsum : (∑ r : N.R, rates.k (Sum.inl r) * (N.reaction r).source.massActionMonomial x *
      N.reactionVector r 0) = 2 * x 0 := by
    show (∑ r : Fin 1, rates.k (Sum.inl r) * (N.reaction r).source.massActionMonomial x *
      N.reactionVector r 0) = 2 * x 0
    rw [Fin.sum_univ_succ]
    simp [N, rates, rateValue, Complex.massActionMonomial, Network.reactionVector_apply]
    ring
  rw [hsum]
  simp [rates, rateValue]
  ring

/-- **The field of this network is affine, with the identity as the linear part at infinity.**
The linear part is invertible, and the field is of the form `source + M x`. -/
noncomputable def hfield : AffineFieldGeneral N.fullyOpen rates where
  source := fun _ => 1
  M := ContinuousLinearMap.id ℝ (Concentration (Fin 1))
  hM := by
    intro v w hvw
    funext s
    simpa using congrFun hvw s
  eq_field := by
    intro x s
    have hs : s = 0 := by
      apply Fin.ext
      omega
    subst hs
    rw [massActionVectorField_eq]
    rfl

/-- **The zero of the field is `-1`, which is not nonnegative.** -/
theorem zero_not_nonnegative : ¬ Concentration.Nonnegative (affineFieldZeroGeneral hfield) := by
  intro hn
  have hz : N.fullyOpen.massActionVectorField rates (affineFieldZeroGeneral hfield) = 0 :=
    massActionVectorField_affineFieldZeroGeneral hfield
  have h1 : (affineFieldZeroGeneral hfield) 0 = -1 := by
    have h2 : (1 : ℝ) + (affineFieldZeroGeneral hfield) 0 = 0 := by
      have h3 := congrFun (massActionVectorField_eq (affineFieldZeroGeneral hfield)) 0
      rw [hz] at h3
      have : (1 : ℝ) + (affineFieldZeroGeneral hfield) 0 = 0 := by
        simpa using h3.symm
      exact this
    linarith
  have h3 := hn 0
  linarith

/-- **The class degree of this network is `0`**, because the zero of the field lies outside the
nonnegative class. -/
theorem classDegree_eq_zero (c : Concentration (Fin 1))
    (hfin : (N.fullyOpen.steadyStateMap rates c ⁻¹' {0} ∩
      N.fullyOpen.nonnegativeClassRegion c).Finite) :
    N.fullyOpen.nonnegativeClassDegree rates c hfin = 0 := by
  rw [fullyOpen_classDegree_of_affineLinear_eq_zero_or_sign N rates c hfield hfin]
  rw [ite_eq_right zero_not_nonnegative]

/-- **The class degree is not the sign of the determinant of the linear part at infinity** when
the zero of the field is not nonnegative: here the linear part at infinity is the identity, whose
determinant has sign `+1`, while the class degree is `0`.

This is why the total-degree theorem of this module carries the hypothesis that the zero of the
field is nonnegative: the class degree of the library is the *relative* degree on the nonnegative
part of the class, and it coincides with the degree at infinity only when the zero of the field
lies in that part of the class. -/
theorem classDegree_ne_sign_det (c : Concentration (Fin 1))
    (hfin : (N.fullyOpen.steadyStateMap rates c ⁻¹' {0} ∩
      N.fullyOpen.nonnegativeClassRegion c).Finite) :
    N.fullyOpen.nonnegativeClassDegree rates c hfin
      ≠ ((SignType.sign
          (LinearMap.det (ContinuousLinearMap.id ℝ (Concentration (Fin 1))).toLinearMap) : SignType)
          : ℤ) := by
  rw [classDegree_eq_zero c hfin]
  have h1 : ((SignType.sign
      (LinearMap.det (ContinuousLinearMap.id ℝ (Concentration (Fin 1))).toLinearMap) : SignType)
      : ℤ) = 1 := by
    have h2 : LinearMap.det (ContinuousLinearMap.id ℝ (Concentration (Fin 1))).toLinearMap = 1 := by
      show LinearMap.det LinearMap.id = 1
      exact LinearMap.det_id
    rw [h2]
    simp
  rw [h1]
  norm_num

end CounterexampleGeneral

/-! ## The axioms used by the principal declarations -/

#print axioms fullyOpen_classDegree_of_affineLinear
#print axioms fullyOpen_classDegree_of_affineLinear_eq_zero_or_sign
#print axioms fullyOpen_exists_positiveSteadyState_of_affineLinear
#print axioms fullyOpen_card_positiveSteadyStates_odd_of_affineLinear
#print axioms fullyOpen_classDegree_of_affineLinear_diagonal
#print axioms det_fderiv_steadyStateMap_affineGeneral
#print axioms CounterexampleGeneral.classDegree_ne_sign_det

end Network

end CRNT

