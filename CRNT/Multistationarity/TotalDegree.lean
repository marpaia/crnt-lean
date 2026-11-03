import CRNT.Multistationarity.DegreeExistence
import CRNT.Multistationarity.DegreeStructural
import CRNT.Multistationarity.DegreeMultistationarity
import CRNT.Multistationarity.ParityOfSteadyStates
import CRNT.Open.Augmentation

/-!
# Conditional degree/parity consequences and restricted total-degree examples

The finite signed-count arguments use the displayed boundary, regularity,
finiteness and total-degree inputs. Explicit affine/rank-restricted computations
are available where stated. Full openness alone does not force odd parity; the
general total-degree theorem under dissipativity and boundary conditions remains
incomplete. See `ParityOfSteadyStates` and `test.SemanticCorrespondence`.
An earlier parity attribution with no verifiable source has been removed.
-/

set_option maxHeartbeats 800000

namespace CRNT

namespace Network

open scoped BigOperators Topology Classical

open Set Filter

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The linear part of a dissipative affine field: `v ↦ -outflow • v`. -/
noncomputable def outflowLinearMap (outflow : S → ℝ) : Concentration S →L[ℝ] Concentration S :=
  ContinuousLinearMap.pi (fun s =>
    (-outflow s) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s)

omit [DecidableEq S] [Fintype S] in
@[simp] theorem outflowLinearMap_apply (outflow : S → ℝ) (v : Concentration S) (s : S) :
    outflowLinearMap outflow v s = -outflow s * v s := by
  rw [outflowLinearMap, ContinuousLinearMap.pi_apply]
  simp

/-- **The dissipative affine form of the field of a fully open network.**

The field of the fully open extension is `x ↦ source - outflow • x`: a constant production term
and a diagonal, strictly negative linear part.  This is the form in which the degree at infinity
is the sign of the determinant of the linear part, namely `(-1)^s`. -/
structure AffineField (N : Network S) (κ : N.RateConstants) where
  /-- The constant part of the field. -/
  source : Concentration S
  /-- The outflow rates, one per species. -/
  outflow : S → ℝ
  /-- The constant part is strictly positive. -/
  source_pos : ∀ s, 0 < source s
  /-- The outflow rates are strictly positive. -/
  outflow_pos : ∀ s, 0 < outflow s
  /-- The field of the network is `source - outflow • x`. -/
  eq_field : ∀ x s, N.massActionVectorField κ x s = source s - outflow s * x s

/-- The field of a fully open network in dissipative affine form is `source + (-outflow) • x`. -/
theorem massActionVectorField_eq_affine_add (N : Network S) (κ : N.RateConstants)
    (h : AffineField N κ) (x : Concentration S) (s : S) :
    N.massActionVectorField κ x s = h.source s + (-h.outflow s) * x s := by
  rw [h.eq_field]
  ring

/-- **The derivative of the field of a fully open network in dissipative affine form** is the
diagonal operator `v ↦ -outflow • v`, independently of the point. -/
theorem hasFDerivAt_massActionVectorField_affine (N : Network S) (κ : N.RateConstants)
    (h : AffineField N κ) (x : Concentration S) :
    HasFDerivAt (fun y => N.massActionVectorField κ y)
      (outflowLinearMap h.outflow) x := by
  have hfun : (fun y => N.massActionVectorField κ y)
      = (fun y => fun s => h.source s + (-h.outflow s) * y s) := by
    funext y s
    exact N.massActionVectorField_eq_affine_add κ h y s
  rw [hfun]
  refine hasFDerivAt_pi.mpr fun s => ?_
  have hc : HasFDerivAt (fun y : Concentration S => -h.outflow s)
      (0 : Concentration S →L[ℝ] ℝ) x :=
    hasFDerivAt_const (-h.outflow s) x
  have h2 : HasFDerivAt (fun y : Concentration S => (-h.outflow s) * y s)
      ((-h.outflow s) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s) x := by
    have hmul := hc.mul (hasFDerivAt_apply s x)
    convert hmul using 1 ; ext y ; simp
  have h1 : HasFDerivAt (fun y : Concentration S => h.source s)
      (0 : Concentration S →L[ℝ] ℝ) x :=
    hasFDerivAt_const (h.source s) x
  have h3 := h1.add h2
  convert h3 using 1 ; ext y ; simp

/-- **The unique zero of a dissipative affine field**: the balance `source = outflow • x`. -/
noncomputable def affineFieldZero {N : Network S} {κ : N.RateConstants}
    (h : AffineField N κ) : Concentration S :=
  fun s => h.source s / h.outflow s

/-- The zero of a dissipative affine field is strictly positive. -/
theorem affineFieldZero_pos {N : Network S} {κ : N.RateConstants} (h : AffineField N κ) :
    (affineFieldZero h).Positive := by
  intro s
  exact div_pos (h.source_pos s) (h.outflow_pos s)

/-- The zero of a dissipative affine field is a zero of the field. -/
theorem massActionVectorField_affineFieldZero {N : Network S} {κ : N.RateConstants}
    (h : AffineField N κ) :
    N.massActionVectorField κ (affineFieldZero h) = 0 := by
  funext s
  have hne : h.outflow s ≠ 0 := (h.outflow_pos s).ne'
  rw [h.eq_field, affineFieldZero]
  field_simp
  simp

/-- The zero of a dissipative affine field is the only zero. -/
theorem massActionVectorField_eq_zero_iff {N : Network S} {κ : N.RateConstants}
    (h : AffineField N κ) (x : Concentration S) :
    N.massActionVectorField κ x = 0 ↔ x = affineFieldZero h := by
  constructor
  · intro hx
    funext s
    have hs : h.source s - h.outflow s * x s = 0 := by
      have hx' := congrFun hx s
      rw [h.eq_field x s] at hx'
      simpa using hx'
    have hne : h.outflow s ≠ 0 := (h.outflow_pos s).ne'
    have hbal : h.source s = h.outflow s * x s := by linarith
    show x s = h.source s / h.outflow s
    apply (eq_div_iff hne).mpr
    rw [mul_comm]
    exact hbal.symm
  · intro hx
    subst hx
    exact N.massActionVectorField_affineFieldZero h

/-! ## The transport of the species space to the class coordinates -/

/-- **The species space of the fully open extension, identified with its class coordinate
space.**  The stoichiometric subspace of the fully open extension is the whole space, so the class
has dimension `card S`, and the species space `S → ℝ` is isomorphic to the class coordinate space
`Fin (card S) → ℝ`. -/
noncomputable def fullyOpenSpeciesEquiv (N : Network S) : S ≃ Fin N.fullyOpen.stoichRank :=
  Fintype.equivFinOfCardEq (stoichRank_fullyOpen N).symm

/-- The forward transport: a species vector read in the class coordinates. -/
noncomputable def fullyOpenTransportFwdLM (N : Network S) :
    (S → ℝ) →ₗ[ℝ] (Fin N.fullyOpen.stoichRank → ℝ) where
  toFun v := fun i => v ((fullyOpenSpeciesEquiv N).symm i)
  map_add' u v := by
    funext i; simp [Pi.add_apply]
  map_smul' a v := by
    funext i; simp [Pi.smul_apply, smul_eq_mul]

/-- The backward transport: a class coordinate vector read in the species space. -/
noncomputable def fullyOpenTransportInvLM (N : Network S) :
    (Fin N.fullyOpen.stoichRank → ℝ) →ₗ[ℝ] (S → ℝ) where
  toFun w := fun s => w (fullyOpenSpeciesEquiv N s)
  map_add' u v := by
    funext s; simp [Pi.add_apply]
  map_smul' a v := by
    funext s; simp [Pi.smul_apply, smul_eq_mul]

/-- The forward and the backward transport are inverse to each other. -/
theorem fullyOpenTransportFwdLM_inv (N : Network S) (w : Fin N.fullyOpen.stoichRank → ℝ) :
    fullyOpenTransportFwdLM N (fullyOpenTransportInvLM N w) = w := by
  funext i
  simp [fullyOpenTransportFwdLM, fullyOpenTransportInvLM]

/-- The backward and the forward transport are inverse to each other. -/
theorem fullyOpenTransportInvLM_inv (N : Network S) (v : Concentration S) :
    fullyOpenTransportInvLM N (fullyOpenTransportFwdLM N v) = v := by
  funext s
  simp [fullyOpenTransportFwdLM, fullyOpenTransportInvLM]

/-- The chart of the fully open extension, as a linear map of the class coordinate space. -/
theorem stoichChartLM_comp_stoichProjLM_fullyOpen (N : Network S) :
    N.fullyOpen.stoichChartLM.comp N.fullyOpen.stoichProjLM = LinearMap.id := by
  apply LinearMap.ext
  intro w
  exact N.fullyOpen.stoichChart_stoichProj (w := w) (by
    rw [stoichSubspace_fullyOpen_eq_top]
    exact Submodule.mem_top)

/-- The projection of the fully open extension, as a linear map of the class coordinate space. -/
theorem stoichProjLM_comp_stoichChartLM (N : Network S) :
    N.fullyOpen.stoichProjLM.comp N.fullyOpen.stoichChartLM = LinearMap.id := by
  apply LinearMap.ext
  intro y
  exact N.fullyOpen.stoichProjLM_stoichChartLM y

/-- **The derivative of the reduced field of a fully open network in dissipative affine form** is
the conjugate of the diagonal operator `v ↦ -outflow • v` by the chart. -/
theorem fderiv_steadyStateMap_affine (N : Network S) (κ : N.fullyOpen.RateConstants)
    (h : AffineField N.fullyOpen κ) (c : Concentration S) (y : ClassCoord (N.fullyOpen)) :
    fderiv ℝ (N.fullyOpen.steadyStateMap κ c) y
      = N.fullyOpen.stoichProj.comp
          ((outflowLinearMap h.outflow).comp N.fullyOpen.stoichChart) := by
  have h1 : HasFDerivAt (N.fullyOpen.affineChart c) N.fullyOpen.stoichChart y :=
    N.fullyOpen.affineChart_hasFDerivAt c y
  have h2 : HasFDerivAt (fun x => N.fullyOpen.massActionVectorField κ x)
      (outflowLinearMap h.outflow) (N.fullyOpen.affineChart c y) :=
    N.fullyOpen.hasFDerivAt_massActionVectorField_affine κ h (N.fullyOpen.affineChart c y)
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
fully open network in dissipative affine form has determinant `∏ s, -outflow s`, the determinant
of the diagonal operator `-outflow •`. -/
theorem det_fderiv_steadyStateMap_affine (N : Network S) (κ : N.fullyOpen.RateConstants)
    (h : AffineField N.fullyOpen κ) (c : Concentration S) (y : ClassCoord (N.fullyOpen)) :
    LinearMap.det (fderiv ℝ (N.fullyOpen.steadyStateMap κ c) y).toLinearMap
      = ∏ s : S, -h.outflow s := by
  rw [fderiv_steadyStateMap_affine N κ h c y]
  -- the composite, as a linear map of the class coordinate space
  have hcomp : (N.fullyOpen.stoichProj.comp
      ((outflowLinearMap h.outflow).comp N.fullyOpen.stoichChart)).toLinearMap
      = N.fullyOpen.stoichProjLM.comp
          ((outflowLinearMap h.outflow).toLinearMap.comp N.fullyOpen.stoichChartLM) := by
    apply LinearMap.ext
    intro z
    simp [ContinuousLinearMap.toLinearMap_comp]
  rw [hcomp]
  -- the transported maps
  set I := fullyOpenTransportInvLM N with hI
  set F := fullyOpenTransportFwdLM N with hF
  set P' : (Fin N.fullyOpen.stoichRank → ℝ) →ₗ[ℝ] (Fin N.fullyOpen.stoichRank → ℝ) :=
    N.fullyOpen.stoichProjLM.comp I with hP'
  set C' : (Fin N.fullyOpen.stoichRank → ℝ) →ₗ[ℝ] (Fin N.fullyOpen.stoichRank → ℝ) :=
    F.comp N.fullyOpen.stoichChartLM with hC'
  set L' : (Fin N.fullyOpen.stoichRank → ℝ) →ₗ[ℝ] (Fin N.fullyOpen.stoichRank → ℝ) :=
    F.comp ((outflowLinearMap h.outflow).toLinearMap.comp I) with hL'
  -- the composite is the product of the transported maps
  have hmain : N.fullyOpen.stoichProjLM.comp
      ((outflowLinearMap h.outflow).toLinearMap.comp N.fullyOpen.stoichChartLM)
      = P'.comp (L'.comp C') := by
    apply LinearMap.ext
    intro z
    simp only [hP', hC', hL', hF, hI, LinearMap.comp_apply, fullyOpenTransportInvLM_inv]
  rw [hmain, LinearMap.det_comp, LinearMap.det_comp]
  -- the transported chart and projection are inverse to each other
  have hP'C' : P'.comp C' = LinearMap.id := by
    apply LinearMap.ext
    intro z
    simp only [hP', hC', hF, hI, LinearMap.comp_apply, fullyOpenTransportInvLM_inv]
    exact N.fullyOpen.stoichProjLM_stoichChartLM z
  have hdetPC : LinearMap.det P' * LinearMap.det C' = 1 := by
    rw [← LinearMap.det_comp, hP'C', LinearMap.det_id]
  rw [show LinearMap.det P' * (LinearMap.det L' * LinearMap.det C')
      = LinearMap.det L' * (LinearMap.det P' * LinearMap.det C') by ring]
  rw [hdetPC, mul_one]
  -- the determinant of the transported diagonal operator
  have hL'val : ∀ v i, L' v i = -h.outflow ((fullyOpenSpeciesEquiv N).symm i) * v i := by
    intro v i
    simp only [hL', hF, hI, LinearMap.comp_apply]
    have h1 : (F ((outflowLinearMap h.outflow).toLinearMap (I v))) i
        = (outflowLinearMap h.outflow) (I v) ((fullyOpenSpeciesEquiv N).symm i) := by
      rfl
    rw [h1, outflowLinearMap_apply]
    have h2 : (I v) ((fullyOpenSpeciesEquiv N).symm i) = v i := by
      simp [hI, fullyOpenTransportInvLM]
    rw [h2]
  have hmat : LinearMap.toMatrix' L' = Matrix.diagonal
      (fun i => -h.outflow ((fullyOpenSpeciesEquiv N).symm i)) := by
    ext i j
    rw [LinearMap.toMatrix'_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · simp [hij, hL'val]
    · simp [hij, hL'val]
  have hdetL' : LinearMap.det L' = ∏ i : Fin N.fullyOpen.stoichRank,
      -h.outflow ((fullyOpenSpeciesEquiv N).symm i) := by
    rw [← LinearMap.det_toMatrix', hmat, Matrix.det_diagonal]
  rw [hdetL']
  -- the product over the species
  have hprod : (∏ i : Fin N.fullyOpen.stoichRank,
      -h.outflow ((fullyOpenSpeciesEquiv N).symm i)) = ∏ s : S, -h.outflow s := by
    rw [Fintype.prod_equiv (fullyOpenSpeciesEquiv N).symm
      (fun i => -h.outflow ((fullyOpenSpeciesEquiv N).symm i)) (fun s => -h.outflow s)
      (fun _ => rfl)]
  rw [hprod]


/-! ## The total degree of the fully open network -/

/-- **The integer value of the sign of a product of signs.** -/
theorem coe_sign_mul (a b : SignType) : ((a * b : SignType) : ℤ) = (a : ℤ) * (b : ℤ) := by
  cases a <;> cases b <;> rfl

/-- **The integer value of a power of `-1` in `SignType`.** -/
theorem coe_sign_pow (n : ℕ) : (((-1 : SignType) ^ n : SignType) : ℤ) = (-1 : ℤ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hmul : (((-1 : SignType) ^ (n + 1) : SignType) : ℤ)
        = (((-1 : SignType) ^ n : SignType) : ℤ) * ((-1 : SignType) : ℤ) := by
      rw [pow_succ, coe_sign_mul]
    rw [hmul, ih, SignType.coe_neg_one]
    ring

/-- **The total-degree theorem for the fully open network.**  Let `N.fullyOpen` be the fully open
extension of `N` with rate constants `κ`, and suppose that its field is in dissipative affine
form `x ↦ source - outflow • x` with `source` strictly positive and `outflow` strictly positive —
the shape of the field of a fully open network whose reactions all have an empty source complex.
Then the class degree of the reduced field on the nonnegative part of the class of `c` is
`(-1)^{card S}`, the sign of the determinant of the linear part at infinity.

This is the Conradi–Feliu–Mincheva–Wiuf total-degree theorem in the form in which it is
available for a fully open network: the class of a fully open network is the whole space, the
degree of the class map is the degree at infinity, and the degree at infinity is the sign of the
determinant of the linear part `-outflow •`, namely `(-1)^s`. -/
theorem fullyOpen_classDegree (N : Network S) (κ : N.fullyOpen.RateConstants) (c : Concentration S)
    (h : AffineField N.fullyOpen κ)
    (hfin : (N.fullyOpen.steadyStateMap κ c ⁻¹' {0} ∩
      N.fullyOpen.nonnegativeClassRegion c).Finite) :
    N.fullyOpen.nonnegativeClassDegree κ c hfin = (-1) ^ (Fintype.card S) := by
  -- the positive zero of the field
  have hxstarpos : (affineFieldZero h).Positive := affineFieldZero_pos h
  have hxstarzero : N.fullyOpen.massActionVectorField κ (affineFieldZero h) = 0 :=
    massActionVectorField_affineFieldZero h
  -- the chart coordinate of the zero
  set ystar : ClassCoord (N.fullyOpen) := N.fullyOpen.chartCoord c (affineFieldZero h) with hystar
  have haff : N.fullyOpen.affineChart c ystar = affineFieldZero h := by
    have hmem : affineFieldZero h - c ∈ N.fullyOpen.stoichSubspace := by
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
    have h2 : N.fullyOpen.affineChart c y = affineFieldZero h :=
      (massActionVectorField_eq_zero_iff h (N.fullyOpen.affineChart c y)).mp hy'
    have h3 : N.fullyOpen.stoichChart y = N.fullyOpen.stoichChart ystar := by
      have h4 : N.fullyOpen.affineChart c y = N.fullyOpen.affineChart c ystar := by
        rw [h2, haff]
      simp only [affineChart] at h4
      exact add_left_cancel h4
    exact N.fullyOpen.stoichChart_injective h3
  -- the zero lies in the nonnegative part of the class
  have hynonneg : ystar ∈ N.fullyOpen.nonnegativeClassRegion c := by
    rw [mem_nonnegativeClassRegion_iff, haff]
    exact hxstarpos.nonnegative
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
      = ((SignType.sign (∏ s : S, -h.outflow s) : SignType) : ℤ) := by
    unfold nonnegativeClassDegree
    have hcong : localDegreeOn (N.fullyOpen.steadyStateMap κ c) 0
        (N.fullyOpen.nonnegativeClassRegion c) hfin
        = localDegreeOn (N.fullyOpen.steadyStateMap κ c) 0
        (N.fullyOpen.nonnegativeClassRegion c) hfin' :=
      localDegreeOn_congr_of_preimage_inter_eq (N.fullyOpen.steadyStateMap κ c) 0 rfl hfin hfin'
    rw [hcong]
    rw [hlocal]
    rw [det_fderiv_steadyStateMap_affine N κ h c ystar]
  -- the sign of the determinant: a product of `card S` negative numbers
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
  rw [hdeg, hsign]


/-! ## The zero set of the reduced field -/

/-- **The zero set of the reduced field of a fully open network in dissipative affine form** is the
singleton of the chart coordinate of the (strictly positive) zero of the field. -/
theorem fullyOpen_steadyStateMap_zero_eq_singleton (N : Network S) (κ : N.fullyOpen.RateConstants)
    (c : Concentration S) (h : AffineField N.fullyOpen κ) :
    N.fullyOpen.steadyStateMap κ c ⁻¹' {0} ∩ N.fullyOpen.nonnegativeClassRegion c
      = {N.fullyOpen.chartCoord c (affineFieldZero h)} := by
  set ystar : ClassCoord (N.fullyOpen) := N.fullyOpen.chartCoord c (affineFieldZero h) with hystar
  have haff : N.fullyOpen.affineChart c ystar = affineFieldZero h := by
    have hmem : affineFieldZero h - c ∈ N.fullyOpen.stoichSubspace := by
      rw [stoichSubspace_fullyOpen_eq_top]
      exact Submodule.mem_top
    rw [hystar]
    simp only [affineChart, chartCoord]
    rw [N.fullyOpen.stoichChart_stoichProj hmem]
    abel
  have hzero : N.fullyOpen.steadyStateMap κ c ystar = 0 := by
    simp only [steadyStateMap, reducedField]
    rw [haff, massActionVectorField_affineFieldZero h, map_zero]
  have huniq : ∀ y, N.fullyOpen.steadyStateMap κ c y = 0 → y = ystar := by
    intro y hy
    have hy' : N.fullyOpen.massActionVectorField κ (N.fullyOpen.affineChart c y) = 0 := by
      have hinj := stoichProj_injective_of_stoichSubspace_eq_top (N.fullyOpen)
        (stoichSubspace_fullyOpen_eq_top N)
      apply hinj
      have h2 := hy
      simp only [steadyStateMap, reducedField] at h2
      rw [h2, map_zero]
    have h2 : N.fullyOpen.affineChart c y = affineFieldZero h :=
      (massActionVectorField_eq_zero_iff h (N.fullyOpen.affineChart c y)).mp hy'
    have h3 : N.fullyOpen.stoichChart y = N.fullyOpen.stoichChart ystar := by
      have h4 : N.fullyOpen.affineChart c y = N.fullyOpen.affineChart c ystar := by
        rw [h2, haff]
      simp only [affineChart] at h4
      exact add_left_cancel h4
    exact N.fullyOpen.stoichChart_injective h3
  have hynonneg : ystar ∈ N.fullyOpen.nonnegativeClassRegion c := by
    rw [mem_nonnegativeClassRegion_iff, haff]
    exact (affineFieldZero_pos h).nonnegative
  ext y
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hzy, _⟩
    exact Set.mem_singleton_iff.mpr (huniq y (Set.mem_preimage.mp hzy))
  · rintro rfl
    exact ⟨hzero, hynonneg⟩

/-- **The finiteness of the zero set is automatic** for a fully open network in dissipative affine
form: the reduced field has exactly one zero in the nonnegative part of the class. -/
theorem fullyOpen_hfin_affine (N : Network S) (κ : N.fullyOpen.RateConstants) (c : Concentration S)
    (h : AffineField N.fullyOpen κ) :
    (N.fullyOpen.steadyStateMap κ c ⁻¹' {0} ∩ N.fullyOpen.nonnegativeClassRegion c).Finite := by
  rw [fullyOpen_steadyStateMap_zero_eq_singleton N κ c h]
  exact Set.finite_singleton _

/-! ## The fully open extension of a network with empty source complexes -/

/-- **The fully open extension of a network whose reactions all have an empty source complex has
a field in dissipative affine form.**  Every reaction then contributes a constant production term,
and the outflow pseudo-reactions contribute the diagonal linear part. -/
noncomputable def fullyOpen_affineField_of_source_zero (N : Network S) (κ : N.fullyOpen.RateConstants)
    (hsrc : ∀ r : N.R, (N.reaction r).source = 0) :
    AffineField N.fullyOpen κ where
  source := fun s => (∑ r : N.R, κ.k (Sum.inl r) * ((N.reaction r).target s : ℝ))
      + κ.k (Sum.inr (Sum.inl s))
  outflow := fun s => κ.k (Sum.inr (Sum.inr s))
  source_pos := by
    intro s
    have h1 : 0 ≤ ∑ r : N.R, κ.k (Sum.inl r) * ((N.reaction r).target s : ℝ) := by
      refine Finset.sum_nonneg fun r _ => ?_
      exact mul_nonneg (κ.positive _).le (Nat.cast_nonneg _)
    have h2 : 0 < κ.k (Sum.inr (Sum.inl s)) := κ.positive _
    linarith
  outflow_pos := by
    intro s
    exact κ.positive _
  eq_field := by
    intro x s
    rw [fullyOpen_massActionVectorField_eq]
    have hmono : ∀ r : N.R, (N.reaction r).source.massActionMonomial x = 1 := by
      intro r
      rw [hsrc r]
      exact Complex.massActionMonomial_zero x
    have hvec : ∀ r : N.R, N.reactionVector r s = ((N.reaction r).target s : ℝ) := by
      intro r
      rw [reactionVector_apply]
      have hz : ((N.reaction r).source s : ℝ) = 0 := by
        rw [hsrc r]
        simp
      rw [hz, sub_zero]
    simp only [hmono, hvec, mul_one]

/-- **The total-degree theorem for the fully open extension of a network whose reactions all have
an empty source complex.**  This is the Conradi–Feliu–Mincheva–Wiuf total degree `(-1)^s` for the
class of a fully open network in the case in which the field at infinity is the diagonal outflow
operator. -/
theorem fullyOpen_classDegree_of_source_zero (N : Network S) (κ : N.fullyOpen.RateConstants)
    (c : Concentration S) (hsrc : ∀ r : N.R, (N.reaction r).source = 0)
    (hfin : (N.fullyOpen.steadyStateMap κ c ⁻¹' {0} ∩
      N.fullyOpen.nonnegativeClassRegion c).Finite) :
    N.fullyOpen.nonnegativeClassDegree κ c hfin = (-1) ^ (Fintype.card S) :=
  fullyOpen_classDegree N κ c (fullyOpen_affineField_of_source_zero N κ hsrc) hfin

/-! ## The consequences for the field map -/

/-- **A positive steady state exists in the class of `c`** for a fully open network in dissipative
affine form: the total degree `(-1)^s` is nonzero, and the field does not vanish on the class
boundary.  This is the Conradi–Feliu–Mincheva–Wiuf existence step, with the total degree
discharged. -/
theorem fullyOpen_exists_positiveSteadyState_affine (N : Network S) (κ : N.fullyOpen.RateConstants)
    (c : Concentration S) (h : AffineField N.fullyOpen κ)
    (hfin : (N.fullyOpen.steadyStateMap κ c ⁻¹' {0} ∩
      N.fullyOpen.nonnegativeClassRegion c).Finite) :
    ∃ x : Concentration S,
      N.fullyOpen.StoichCompatible c x ∧ Concentration.Positive x ∧
        N.fullyOpen.IsMassActionSteadyState κ x := by
  refine N.fullyOpen.exists_positiveSteadyState_of_nonnegativeClassDegree_ne_zero κ c hfin ?_ ?_
  · rw [fullyOpen_classDegree N κ c h hfin]
    exact pow_ne_zero _ (by norm_num : (-1 : ℤ) ≠ 0)
  · intro y hy
    exact N.fullyOpen_steadyStateMap_ne_zero_on_classBoundary κ c y hy

/-- Conditional degree/parity consequence under the hypotheses displayed below. -/
theorem fullyOpen_card_positiveSteadyStates_odd_affine (N : Network S)
    (κ : N.fullyOpen.RateConstants) (c : Concentration S) (h : AffineField N.fullyOpen κ)
    (hfinN : (N.fullyOpen.steadyStateMap κ c ⁻¹' {0} ∩
      N.fullyOpen.nonnegativeClassRegion c).Finite)
    (hfinP : (N.fullyOpen.positiveSteadyStates_in_class κ c).Finite)
    (hnd : ∀ y ∈ N.fullyOpen.positiveSteadyStates_in_class κ c,
      (N.fullyOpen.reducedJacobian κ c y).det ≠ 0) :
    (N.fullyOpen.card_positiveSteadyStates_in_class κ c hfinP) % 2 = 1 := by
  refine N.fullyOpen.card_positiveSteadyStates_odd_of_classDegree_eq_pow_neg_one κ c
    (Fintype.card S) (stoichRank_fullyOpen N) hfinN hfinP ?_ hnd ?_
  · intro y hy
    exact N.fullyOpen_steadyStateMap_ne_zero_on_classBoundary κ c y hy
  · exact fullyOpen_classDegree N κ c h hfinN

/-- **The Conradi–Feliu–Mincheva–Wiuf conclusion for a fully open network in dissipative affine
form.**  If the class carries a steady state whose local degree is the exceptional one,
`(-1)^{s+1}`, then the class is multistationary: it carries two distinct positive steady states.
This is the ingredient of leaf **M13** (the parameter regions for multistationarity) with the
total-degree hypothesis discharged: the total degree is `(-1)^s`, so the exceptional local degree
`(-1)^{s+1}` is exactly the negative of the class degree. -/
theorem fullyOpen_exists_two_positiveSteadyStates_affine (N : Network S)
    (κ : N.fullyOpen.RateConstants) (c : Concentration S) (h : AffineField N.fullyOpen κ)
    (ystar : ClassCoord (N.fullyOpen))
    (hzero : N.fullyOpen.steadyStateMap κ c ystar = 0)
    (hystar : ystar ∈ N.fullyOpen.nonnegativeClassRegion c)
    (hfin : (N.fullyOpen.steadyStateMap κ c ⁻¹' {0} ∩
      N.fullyOpen.nonnegativeClassRegion c).Finite)
    (hdet : ((SignType.sign (N.fullyOpen.reducedJacobian κ c ystar).det : SignType) : ℤ)
        = (-1 : ℤ) ^ (N.fullyOpen.stoichRank + 1)) :
    ∃ x y : Concentration S,
      x ≠ y ∧ N.fullyOpen.StoichCompatible c x ∧ Concentration.Positive x ∧
        N.fullyOpen.IsMassActionSteadyState κ x ∧
      N.fullyOpen.StoichCompatible c y ∧ Concentration.Positive y ∧
        N.fullyOpen.IsMassActionSteadyState κ y := by
  refine N.fullyOpen.exists_two_positiveSteadyStates_of_classDegree_eq_pow_neg_one κ c ystar
    hzero hystar hfin ?_ hdet ?_
  · rw [fullyOpen_classDegree N κ c h hfin, stoichRank_fullyOpen]
  · intro y hy
    exact N.fullyOpen_steadyStateMap_ne_zero_on_classBoundary κ c y hy


/-! ## The purely linear flow network -/

/-- **The total degree of the purely linear flow network.**  The fully open extension of the
reaction-free network is the network `0 → s → 0` on every species; its field is
`inflow_s - outflow_s x_s`, so its class degree is the total degree `(-1)^{card S}`. -/
theorem emptyNet_fullyOpen_classDegree (κ : emptyNet.fullyOpen.RateConstants) (c : Concentration S)
    (hfin : (emptyNet.fullyOpen.steadyStateMap κ c ⁻¹' {0} ∩
      emptyNet.fullyOpen.nonnegativeClassRegion c).Finite) :
    emptyNet.fullyOpen.nonnegativeClassDegree κ c hfin = (-1) ^ (Fintype.card S) := by
  refine fullyOpen_classDegree (N := emptyNet) κ c ?_ hfin
  exact fullyOpen_affineField_of_source_zero (N := emptyNet) κ (fun r => Empty.elim r)

/-- **The finiteness of the zero set of the purely linear flow network** is automatic: its
reduced field has exactly one zero in the nonnegative part of the class. -/
theorem emptyNet_fullyOpen_hfin (κ : emptyNet.fullyOpen.RateConstants) (c : Concentration S) :
    (emptyNet.fullyOpen.steadyStateMap κ c ⁻¹' {0} ∩
      emptyNet.fullyOpen.nonnegativeClassRegion c).Finite :=
  fullyOpen_hfin_affine (N := emptyNet) κ c
    (fullyOpen_affineField_of_source_zero (N := emptyNet) κ (fun r => Empty.elim r))


/-! ## The total-degree theorem fails without the affine hypothesis -/

namespace Counterexample

/-- **The one-species network with the autocatalytic reaction `A → 2A`.**  Its fully open
extension has the inflow pseudo-reaction `0 → A` and the outflow pseudo-reaction `A → 0`. -/
def N : Network (Fin 1) where
  R := Fin 1
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun _ => { source := fun _ => 1, target := fun _ => 2 }

/-- All rate constants of the fully open extension equal to one. -/
def rates : N.fullyOpen.RateConstants where
  k _ := 1
  positive _ := by norm_num

/-- **The field of the fully open extension is the constant `1`.**  The inflow contributes `1`,
the autocatalytic reaction contributes `x` and the outflow contributes `-x`; the field therefore
never vanishes, and the class degree is `0` rather than the total degree `(-1)^1 = -1`. -/
theorem massActionVectorField_eq_one (x : Concentration (Fin 1)) :
    N.fullyOpen.massActionVectorField rates x = fun _ => 1 := by
  funext s
  have hs : s = 0 := by
    apply Fin.ext
    omega
  subst hs
  rw [fullyOpen_massActionVectorField_eq]
  have hsum : (∑ r : N.R, rates.k (Sum.inl r) * (N.reaction r).source.massActionMonomial x *
      N.reactionVector r 0) = x 0 := by
    show (∑ r : Fin 1, rates.k (Sum.inl r) * (N.reaction r).source.massActionMonomial x *
      N.reactionVector r 0) = x 0
    rw [Fin.sum_univ_succ]
    simp [N, rates, Complex.massActionMonomial, Network.reactionVector_apply]
    ring
  rw [hsum]
  simp [rates]


/-- **The reduced field of the counterexample never vanishes.**  The field is the constant `1`,
and the projection onto the class coordinates is injective. -/
theorem steadyStateMap_ne_zero (c : Concentration (Fin 1)) (y : ClassCoord (N.fullyOpen)) :
    N.fullyOpen.steadyStateMap rates c y ≠ 0 := by
  intro hzero
  have hfield : N.fullyOpen.massActionVectorField rates (N.fullyOpen.affineChart c y)
      = fun _ => 1 := massActionVectorField_eq_one _
  have hzero' : N.fullyOpen.stoichProj (fun _ : Fin 1 => (1 : ℝ)) = N.fullyOpen.stoichProj 0 := by
    simp only [map_zero]
    simp only [steadyStateMap, reducedField] at hzero
    rw [hfield] at hzero
    exact hzero
  have hinj := stoichProj_injective_of_stoichSubspace_eq_top (N.fullyOpen)
    (stoichSubspace_fullyOpen_eq_top N)
  have h1 : (fun _ : Fin 1 => (1 : ℝ)) = 0 := hinj hzero'
  have h2 : (1 : ℝ) = 0 := congrFun h1 (0 : Fin 1)
  norm_num at h2

/-- **The class degree of the counterexample is zero.** -/
theorem classDegree_eq_zero (c : Concentration (Fin 1))
    (hfin : (N.fullyOpen.steadyStateMap rates c ⁻¹' {0} ∩
      N.fullyOpen.nonnegativeClassRegion c).Finite) :
    N.fullyOpen.nonnegativeClassDegree rates c hfin = 0 := by
  unfold nonnegativeClassDegree
  rw [localDegreeOn_eq_zero_of_preimage_inter_empty (N.fullyOpen.steadyStateMap rates c) 0 hfin]
  ext y
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
    iff_false, not_and]
  intro hy hyU
  exact (steadyStateMap_ne_zero c y) hy

/-- **The total-degree theorem fails for a general fully open network.**  For the one-species
network with the autocatalytic reaction `A → 2A` (and all rate constants equal to one), the fully
open extension has the constant field `1`: the inflow and the autocatalytic reaction cancel the
outflow exactly.  The class degree is therefore `0`, and *not* the total degree
`(-1)^{card S} = -1`.

This shows that the total-degree theorem needs a hypothesis on the field at infinity: the
reaction terms of a mass-action field contribute to the linear part at infinity (here they cancel
the outflow), and for reactions of order `|y_r| ≥ 2` they even dominate it. -/
theorem classDegree_ne_pow_neg_one (c : Concentration (Fin 1))
    (hfin : (N.fullyOpen.steadyStateMap rates c ⁻¹' {0} ∩
      N.fullyOpen.nonnegativeClassRegion c).Finite) :
    N.fullyOpen.nonnegativeClassDegree rates c hfin ≠ (-1) ^ (Fintype.card (Fin 1)) := by
  rw [classDegree_eq_zero c hfin]
  norm_num [Fintype.card_fin]

end Counterexample

end Network

end CRNT
