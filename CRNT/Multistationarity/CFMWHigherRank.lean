import CRNT.Multistationarity.TotalDegreeGeneral
import CRNT.Multistationarity.ReducedDetHomogeneity

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

open scoped BigOperators Topology Classical

open Set Filter

/-! ## 1. The degree-counting lemma in the general form -/

theorem exists_other_zero_of_localDegreeOn_ne {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → E) {U : Set E}
    (hfin : (f ⁻¹' {(0 : E)} ∩ U).Finite)
    (y₀ : E) (hy₀ : y₀ ∈ U) (hzero : f y₀ = 0)
    (hlocal : ((SignType.sign (LinearMap.det (fderiv ℝ f y₀).toLinearMap) : SignType) : ℤ)
        ≠ localDegreeOn f 0 U hfin) :
    ∃ y ∈ U, f y = 0 ∧ y ≠ y₀ := by
  classical
  have hsum : (∑ x ∈ hfin.toFinset,
      ((SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) : SignType) : ℤ))
      = localDegreeOn f 0 U hfin := by
    rfl
  have hy₀fin : y₀ ∈ hfin.toFinset := by
    rw [hfin.mem_toFinset]
    exact ⟨hzero, hy₀⟩
  have hsplit : (∑ x ∈ hfin.toFinset,
        ((SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) : SignType) : ℤ))
      = (∑ x ∈ hfin.toFinset.erase y₀,
        ((SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) : SignType) : ℤ))
        + ((SignType.sign (LinearMap.det (fderiv ℝ f y₀).toLinearMap) : SignType) : ℤ) :=
    (Finset.sum_erase_add hfin.toFinset
      (fun x => ((SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) : SignType) : ℤ))
      hy₀fin).symm
  have hrest : (∑ x ∈ hfin.toFinset.erase y₀,
        ((SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) : SignType) : ℤ))
      = localDegreeOn f 0 U hfin
        - ((SignType.sign (LinearMap.det (fderiv ℝ f y₀).toLinearMap) : SignType) : ℤ) := by
    have h2 : (∑ x ∈ hfin.toFinset.erase y₀,
          ((SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) : SignType) : ℤ))
        = (∑ x ∈ hfin.toFinset,
          ((SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) : SignType) : ℤ))
          - ((SignType.sign (LinearMap.det (fderiv ℝ f y₀).toLinearMap) : SignType) : ℤ) := by
      linarith [hsplit]
    rw [h2, hsum]
  have hne : (hfin.toFinset.erase y₀).Nonempty := by
    by_contra hcon
    have hempty : hfin.toFinset.erase y₀ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hcon
    have hz0 : (∑ x ∈ hfin.toFinset.erase y₀,
        ((SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) : SignType) : ℤ)) = 0 := by
      rw [hempty, Finset.sum_empty]
    have hz0' : localDegreeOn f 0 U hfin
        - ((SignType.sign (LinearMap.det (fderiv ℝ f y₀).toLinearMap) : SignType) : ℤ) = 0 := by
      rw [← hrest, hz0]
    exact (hlocal (by linarith)).elim
  obtain ⟨z, hz⟩ := hne
  have hzmem : z ∈ hfin.toFinset := Finset.mem_of_mem_erase hz
  have hzne : z ≠ y₀ := (Finset.mem_erase.mp hz).1
  have hzset : z ∈ f ⁻¹' {(0 : E)} ∩ U := hfin.mem_toFinset.mp hzmem
  have hzpre : f z = 0 := Set.mem_singleton_iff.mp hzset.1
  exact ⟨z, hzset.2, hzpre, hzne⟩

end CRNT

namespace CRNT.Network

open scoped BigOperators Topology Classical

open Set Filter

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## 2. The higher-rank degree-counting theorem -/

/-- **The higher-rank degree-counting theorem.**  Let the class degree of the compatibility class
of `x₀` be `d`, and let `ystar` be a steady state of the class whose *local degree* — the sign of
the reduced Jacobian determinant there — is **different from** `d`.  Then the class carries **two
distinct positive steady states**.

This is the general form of the counting step of the Conradi–Feliu–Mincheva–Wiuf argument: the
class degree is the signed count of the zeros of the reduced field in the class, so the
contributions of the zeros other than `ystar` sum to `d - ℓ ≠ 0`; hence there is at least one
further zero, and (because the field does not vanish on the class boundary) two positive steady
states.

The hypothesis `ℓ ≠ d` is strictly weaker than the hypothesis `ℓ = -d` of
`Network.exists_two_positiveSteadyStates_of_classDegree_neg_localDegree`: it is satisfied, in
particular, by the *exceptional* local degree `ℓ = +1` whenever the class degree is not `+1`. -/
theorem exists_two_positiveSteadyStates_of_localDegree_ne_classDegree
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (ystar : ClassCoord N)
    (hzero : N.steadyStateMap κ x₀ ystar = 0)
    (hystar : ystar ∈ N.nonnegativeClassRegion x₀)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite)
    (hlocal : ((SignType.sign (N.reducedJacobian κ x₀ ystar).det : SignType) : ℤ)
        ≠ N.nonnegativeClassDegree κ x₀ hfin)
    (hbd : ∀ y ∈ N.classBoundary x₀, N.steadyStateMap κ x₀ y ≠ 0) :
    ∃ x y : Concentration S,
      x ≠ y ∧ N.StoichCompatible x₀ x ∧ Concentration.Positive x ∧ N.IsMassActionSteadyState κ x ∧
      N.StoichCompatible x₀ y ∧ Concentration.Positive y ∧ N.IsMassActionSteadyState κ y := by
  -- the local degree of the map at `ystar` is the sign of the reduced determinant
  have hlocal' : ((SignType.sign (LinearMap.det
      (fderiv ℝ (N.steadyStateMap κ x₀) ystar).toLinearMap) : SignType) : ℤ)
      ≠ N.nonnegativeClassDegree κ x₀ hfin := by
    rw [N.det_fderiv_steadyStateMap_eq_reducedJacobian_det]
    exact hlocal
  -- the counting step: a second zero of the reduced field in the class
  obtain ⟨z, hzreg, hzzero, hzne⟩ :=
    exists_other_zero_of_localDegreeOn_ne (N.steadyStateMap κ x₀)
      (U := N.nonnegativeClassRegion x₀) hfin ystar hystar hzero hlocal'
  -- the two zeros are positive: the field does not vanish on the class boundary
  have hystarpos : ystar ∈ N.positiveClassRegion x₀ := by
    rw [mem_positiveClassRegion_iff]
    by_contra hnp
    exact hbd ystar ⟨hystar, hnp⟩ hzero
  have hzpos : z ∈ N.positiveClassRegion x₀ := by
    rw [mem_positiveClassRegion_iff]
    by_contra hnp
    exact hbd z ⟨hzreg, hnp⟩ hzzero
  obtain ⟨hc1, hs1⟩ := N.isMassActionSteadyState_affineChart_of_reducedField_eq_zero κ x₀ hzero
  obtain ⟨hc2, hs2⟩ := N.isMassActionSteadyState_affineChart_of_reducedField_eq_zero κ x₀ hzzero
  refine ⟨N.affineChart x₀ ystar, N.affineChart x₀ z, ?_, hc1, hystarpos, hs1, hc2, hzpos, hs2⟩
  exact fun heq => hzne (N.affineChart_injective x₀ heq.symm)

/-- **The exceptional local degree `+1` forces a second positive steady state.**  If a steady
state of the class has local degree `+1` — the sign of a *positive* reduced Jacobian determinant —
and the class degree is not `+1`, then the class carries **two distinct positive steady states**.

This is the higher-rank form of the Conradi–Feliu–Mincheva–Wiuf conclusion: the "exceptional"
local degree is the one opposite to the class degree, and `+1` is exceptional as soon as the class
degree is not `+1`.  In the published orientation the class degree is `(-1)^s` and the exceptional
local degree is `(-1)^{s+1}`; the local degree `+1` is the exceptional one exactly when `s` is
odd. -/
theorem exists_two_positiveSteadyStates_of_localDegree_eq_one
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (ystar : ClassCoord N)
    (hzero : N.steadyStateMap κ x₀ ystar = 0)
    (hystar : ystar ∈ N.nonnegativeClassRegion x₀)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite)
    (hlocal : ((SignType.sign (N.reducedJacobian κ x₀ ystar).det : SignType) : ℤ) = 1)
    (hdeg : N.nonnegativeClassDegree κ x₀ hfin ≠ 1)
    (hbd : ∀ y ∈ N.classBoundary x₀, N.steadyStateMap κ x₀ y ≠ 0) :
    ∃ x y : Concentration S,
      x ≠ y ∧ N.StoichCompatible x₀ x ∧ Concentration.Positive x ∧ N.IsMassActionSteadyState κ x ∧
      N.StoichCompatible x₀ y ∧ Concentration.Positive y ∧ N.IsMassActionSteadyState κ y := by
  refine N.exists_two_positiveSteadyStates_of_localDegree_ne_classDegree κ x₀ ystar hzero
    hystar hfin ?_ hbd
  rw [hlocal]
  exact fun h => hdeg h.symm

/-- **A positive reduced Jacobian determinant forces a second positive steady state.**  If a
steady state of the class has a *positive* reduced Jacobian determinant — the Cauchy–Binet sum
being positive — and the class degree is not `+1`, then the class carries **two distinct positive
steady states**.

This is the higher-rank reading of the multistationarity criterion of Conradi–Feliu–Mincheva–Wiuf
in terms of the sign of the reduced determinant, the quantity that the Cauchy–Binet expansion of
`CRNT.Multistationarity.ReducedDetHomogeneity` computes. -/
theorem exists_two_positiveSteadyStates_of_reducedDet_pos
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (ystar : ClassCoord N)
    (hzero : N.steadyStateMap κ x₀ ystar = 0)
    (hystar : ystar ∈ N.nonnegativeClassRegion x₀)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite)
    (hdet : 0 < (N.reducedJacobian κ x₀ ystar).det)
    (hdeg : N.nonnegativeClassDegree κ x₀ hfin ≠ 1)
    (hbd : ∀ y ∈ N.classBoundary x₀, N.steadyStateMap κ x₀ y ≠ 0) :
    ∃ x y : Concentration S,
      x ≠ y ∧ N.StoichCompatible x₀ x ∧ Concentration.Positive x ∧ N.IsMassActionSteadyState κ x ∧
      N.StoichCompatible x₀ y ∧ Concentration.Positive y ∧ N.IsMassActionSteadyState κ y := by
  have hlocal : ((SignType.sign (N.reducedJacobian κ x₀ ystar).det : SignType) : ℤ) = 1 := by
    rw [sign_pos hdet]
    rfl
  exact N.exists_two_positiveSteadyStates_of_localDegree_eq_one κ x₀ ystar hzero hystar hfin
    hlocal hdeg hbd

/-! ## 3. The total-degree theorem -/

/-- **The mass-action field lies in the stoichiometric subspace.**  The field is a linear
combination of the reaction vectors, and each reaction vector lies in the stoichiometric
subspace. -/
theorem massActionField_mem_stoichSubspace (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) : N.massActionVectorField κ x ∈ N.stoichSubspace := by
  have hsum : N.massActionVectorField κ x
      = ∑ r : N.R, (N.massActionRate κ r x) • (N.reactionVector r) := by
    funext s
    rw [massActionVectorField_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun r _ => rfl
  rw [hsum]
  exact Submodule.sum_mem _ fun r _ =>
    Submodule.smul_mem _ _ (N.reactionVector_mem_stoichSubspace r)

/-- **The dual projection is injective on the stoichiometric subspace.**  A vector of the
stoichiometric subspace whose dual projection vanishes is the zero vector. -/
theorem stoichProj_eq_zero_of_mem_stoichSubspace {N : Network S} {w : S → ℝ}
    (hw : w ∈ N.stoichSubspace) (hproj : N.stoichProj w = 0) : w = 0 := by
  have h1 : N.stoichChart (N.stoichProj w) = w := N.stoichChart_stoichProj hw
  rw [hproj] at h1
  simp only [map_zero] at h1
  exact h1.symm

/-- **The total-degree theorem for a network with an affine field, in the chart coordinates.**
The class degree of the reduced field on the nonnegative part of the compatibility class of `x₀`
is the **sign of the reduced Jacobian determinant** at the unique zero of the field.

This is the Conradi–Feliu–Mincheva–Wiuf total-degree theorem in its affine form, read in the
chart coordinates of the class: the degree of the class map is the degree at infinity of the
field, and the degree at infinity of a field whose leading part is linear is the sign of the
determinant of that linear part, read in the chart of the stoichiometric subspace.  For the fully
open extension of a network the chart is an isomorphism of the whole species space, and the
linear part is the diagonal outflow operator, whose determinant has sign `(-1)^{card S}`
(`Network.fullyOpen_classDegree_eq_pow_neg_one`).

The hypothesis `hcompat` — that the unique zero of the field lies in the compatibility class of
`x₀` — and `hpos` — that it is strictly positive — are needed because the class degree of the
library is the *relative* degree on the nonnegative part of the class. -/
theorem classDegree_of_affineLinear_eq_sign_reducedDet
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (h : AffineFieldGeneral N κ)
    (hcompat : N.StoichCompatible x₀ (affineFieldZeroGeneral h))
    (hpos : Concentration.Positive (affineFieldZeroGeneral h))
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite) :
    N.nonnegativeClassDegree κ x₀ hfin =
      ((SignType.sign
          (N.reducedJacobian κ x₀ (N.chartCoord x₀ (affineFieldZeroGeneral h))).det : SignType) : ℤ) := by
  -- the zero of the field
  set xstar : Concentration S := affineFieldZeroGeneral h with hxstar
  have hxstarzero : N.massActionVectorField κ xstar = 0 :=
    massActionVectorField_affineFieldZeroGeneral h
  -- the chart coordinate of the zero
  set ystar : ClassCoord N := N.chartCoord x₀ xstar with hystar
  have haff : N.affineChart x₀ ystar = xstar := by
    rw [hystar]
    exact N.affineChart_chartCoord hcompat
  -- the zero of the reduced field
  have hzero : N.steadyStateMap κ x₀ ystar = 0 := by
    simp only [steadyStateMap, reducedField]
    rw [haff, hxstarzero, map_zero]
  -- the zero is unique
  have huniq : ∀ y, N.steadyStateMap κ x₀ y = 0 → y = ystar := by
    intro y hy
    have hy' : N.massActionVectorField κ (N.affineChart x₀ y) = 0 := by
      have hmem : N.massActionVectorField κ (N.affineChart x₀ y) ∈ N.stoichSubspace :=
        massActionField_mem_stoichSubspace N κ (N.affineChart x₀ y)
      have hproj : N.stoichProj (N.massActionVectorField κ (N.affineChart x₀ y)) = 0 := by
        have h2 := hy
        simp only [steadyStateMap, reducedField] at h2
        exact h2
      exact stoichProj_eq_zero_of_mem_stoichSubspace hmem hproj
    have h2 : N.affineChart x₀ y = xstar :=
      (massActionVectorField_eq_zero_iff_general h (N.affineChart x₀ y)).mp hy'
    have hyy : N.chartCoord x₀ (N.affineChart x₀ y) = y := N.chartCoord_affineChart x₀ y
    have hhy : N.chartCoord x₀ (N.affineChart x₀ ystar) = ystar := by
      rw [hystar, haff]
    have : y = ystar := by
      calc y = N.chartCoord x₀ (N.affineChart x₀ y) := hyy.symm
        _ = N.chartCoord x₀ xstar := by rw [h2]
        _ = ystar := hystar.symm
    exact this
  -- the zero lies in the nonnegative part of the class
  have hynonneg : ystar ∈ N.nonnegativeClassRegion x₀ := by
    rw [mem_nonnegativeClassRegion_iff, haff]
    exact hpos.nonnegative
  -- the zero set in the nonnegative class is the singleton `ystar`
  have hset : N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀ = {ystar} := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hzy, _⟩
      exact Set.mem_singleton_iff.mpr (huniq y (Set.mem_preimage.mp hzy))
    · rintro rfl
      exact ⟨hzero, hynonneg⟩
  -- the finiteness of the zero set, for the singleton witness
  have hfin' : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite := by
    rw [hset]
    exact Set.finite_singleton ystar
  -- the local degree at the unique zero
  have hlocal : localDegreeOn (N.steadyStateMap κ x₀) 0
      (N.nonnegativeClassRegion x₀) hfin'
      = ((SignType.sign (LinearMap.det
          (fderiv ℝ (N.steadyStateMap κ x₀) ystar).toLinearMap) : SignType) : ℤ) :=
    localDegreeOn_eq_sign_det_of_unique_preimage (N.steadyStateMap κ x₀) ystar
      hzero huniq hynonneg hfin'
  -- the class degree is the local degree
  have hdeg : N.nonnegativeClassDegree κ x₀ hfin
      = ((SignType.sign (N.reducedJacobian κ x₀ ystar).det : SignType) : ℤ) := by
    unfold nonnegativeClassDegree
    have hcong : localDegreeOn (N.steadyStateMap κ x₀) 0
        (N.nonnegativeClassRegion x₀) hfin
        = localDegreeOn (N.steadyStateMap κ x₀) 0
          (N.nonnegativeClassRegion x₀) hfin' :=
      localDegreeOn_congr_of_preimage_inter_eq (N.steadyStateMap κ x₀) 0 rfl hfin hfin'
    rw [hcong]
    rw [hlocal]
    rw [N.det_fderiv_steadyStateMap_eq_reducedJacobian_det]
  rw [hdeg]

/-- **The total degree of a fully open network with an affine field, in the chart
coordinates.**  The class degree of the reduced field on the nonnegative part of the class of `c`
is `(-1)^s`, where `s` is the stoichiometric rank — the dimension of the class coordinate space.

This is the Conradi–Feliu–Mincheva–Wiuf total-degree theorem in its affine form, in the chart
coordinates: the class degree is the degree at infinity of the field, and the degree at infinity
of a field whose leading part is the diagonal outflow operator is the sign of the determinant of
that operator, `(-1)^s`.  For the fully open extension the class is the whole space, so
`s = card S`, and this recovers `Network.fullyOpen_classDegree`. -/
theorem fullyOpen_classDegree_eq_pow_neg_one (N : Network S) (κ : N.fullyOpen.RateConstants)
    (c : Concentration S) (h : AffineField N.fullyOpen κ)
    (hfin : (N.fullyOpen.steadyStateMap κ c ⁻¹' {0} ∩ N.fullyOpen.nonnegativeClassRegion c).Finite) :
    N.fullyOpen.nonnegativeClassDegree κ c hfin = (-1 : ℤ) ^ N.fullyOpen.stoichRank := by
  rw [fullyOpen_classDegree N κ c h hfin, stoichRank_fullyOpen]

/-- **The total degree of a fully open network with a general affine field with a diagonal
negative linear part, in the chart coordinates.** -/
theorem fullyOpen_classDegree_of_affineLinear_diagonal_eq_pow_neg_one
    (N : Network S) (κ : N.fullyOpen.RateConstants) (c : Concentration S)
    (h : AffineField N.fullyOpen κ)
    (hfin : (N.fullyOpen.steadyStateMap κ c ⁻¹' {0} ∩ N.fullyOpen.nonnegativeClassRegion c).Finite) :
    N.fullyOpen.nonnegativeClassDegree κ c hfin = (-1 : ℤ) ^ N.fullyOpen.stoichRank := by
  rw [fullyOpen_classDegree_of_affineLinear_diagonal N κ c h hfin, stoichRank_fullyOpen]

/-! ## 4. The Conradi–Feliu–Mincheva–Wiuf conclusion in the affine case -/

/-- **The power of `-1` at a successor is the negative of the power.** -/
theorem pow_neg_one_succ_neg (n : ℕ) : (-1 : ℤ) ^ (n + 1) = -((-1 : ℤ) ^ n) := by
  rw [pow_succ]
  ring

/-- **The power of `-1` at an even number is `1`.** -/
theorem pow_neg_one_even (n : ℕ) : (-1 : ℤ) ^ (2 * n) = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : 2 * (n + 1) = 2 * n + 2 := by omega
    rw [h, pow_add, ih]
    norm_num

/-- **The power of `-1` is `1` or `-1`.** -/
theorem pow_neg_one_cases (n : ℕ) :
    (-1 : ℤ) ^ n = 1 ∨ (-1 : ℤ) ^ n = -1 := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    rcases ih with ih | ih
    · right
      rw [pow_succ, ih]
      ring
    · left
      rw [pow_succ, ih]
      ring

/-- **The real power of `-1` is the cast of the integer power.** -/
theorem pow_neg_one_cast (n : ℕ) : (Int.cast ((-1 : ℤ) ^ n) : ℝ) = (-1 : ℝ) ^ n := by
  have h1 : (Int.cast (-1 : ℤ) : ℝ) = -1 := by norm_num
  rw [Int.cast_pow, h1]

/-- **The Conradi–Feliu–Mincheva–Wiuf conclusion for a fully open network with an affine field,
in the sign of the reduced Jacobian determinant.**

Let `N.fullyOpen` be the fully open extension of `N` with rate constants `κ`, whose field is in
dissipative affine form `x ↦ source - outflow • x`.  The class degree of the class of `c` is the
total degree `(-1)^s`, where `s = N.fullyOpen.stoichRank` is the dimension of the class; hence the
*exceptional* local degree — the one opposite to the class degree — is `(-1)^{s+1}`.  If the class
carries a steady state whose **reduced Jacobian determinant has the exceptional sign**, i.e.
`(-1)^{s+1} · det > 0`, then the class carries **two distinct positive steady states**.

This is the Conradi–Feliu–Mincheva–Wiuf conclusion of leaf **M13** in the affine case, with the
total-degree hypothesis discharged and the sign condition expressed in terms of the reduced
determinant — the quantity computed by the Cauchy–Binet expansion of
`CRNT.Multistationarity.ReducedDetHomogeneity`. -/
theorem fullyOpen_exists_two_positiveSteadyStates_affine_of_det_sign
    (N : Network S) (κ : N.fullyOpen.RateConstants) (c : Concentration S)
    (h : AffineField N.fullyOpen κ)
    (ystar : ClassCoord (N.fullyOpen))
    (hzero : N.fullyOpen.steadyStateMap κ c ystar = 0)
    (hystar : ystar ∈ N.fullyOpen.nonnegativeClassRegion c)
    (hfin : (N.fullyOpen.steadyStateMap κ c ⁻¹' {0} ∩
      N.fullyOpen.nonnegativeClassRegion c).Finite)
    (hdet : (0 : ℝ) < (-1 : ℝ) ^ (N.fullyOpen.stoichRank + 1) *
        (N.fullyOpen.reducedJacobian κ c ystar).det) :
    ∃ x y : Concentration S,
      x ≠ y ∧ N.fullyOpen.StoichCompatible c x ∧ Concentration.Positive x ∧
        N.fullyOpen.IsMassActionSteadyState κ x ∧
      N.fullyOpen.StoichCompatible c y ∧ Concentration.Positive y ∧
        N.fullyOpen.IsMassActionSteadyState κ y := by
  -- the class degree is the total degree `(-1)^s`
  have hdeg : N.fullyOpen.nonnegativeClassDegree κ c hfin
      = (-1 : ℤ) ^ N.fullyOpen.stoichRank :=
    fullyOpen_classDegree_eq_pow_neg_one N κ c h hfin
  -- the exceptional sign is `+1` or `-1`
  have he : (-1 : ℤ) ^ (N.fullyOpen.stoichRank + 1) = 1 ∨
      (-1 : ℤ) ^ (N.fullyOpen.stoichRank + 1) = -1 :=
    pow_neg_one_cases _
  -- the local degree at `ystar` is the exceptional one
  have hlocal : ((SignType.sign (N.fullyOpen.reducedJacobian κ c ystar).det : SignType) : ℤ)
      = -(N.fullyOpen.nonnegativeClassDegree κ c hfin) := by
    rcases he with he | he
    · have heR : (-1 : ℝ) ^ (N.fullyOpen.stoichRank + 1) = 1 := by
        have h1 : (Int.cast ((-1 : ℤ) ^ (N.fullyOpen.stoichRank + 1)) : ℝ) = 1 := by
          rw [he]
          norm_num
        rw [pow_neg_one_cast] at h1
        exact h1
      rw [heR] at hdet
      have hpos : 0 < (N.fullyOpen.reducedJacobian κ c ystar).det := by
        linarith
      have hsign : ((SignType.sign
          (N.fullyOpen.reducedJacobian κ c ystar).det : SignType) : ℤ) = 1 := by
        rw [sign_pos hpos]
        rfl
      rw [hsign, hdeg]
      calc (1 : ℤ) = (-1 : ℤ) ^ (N.fullyOpen.stoichRank + 1) := by rw [he]
        _ = -((-1 : ℤ) ^ N.fullyOpen.stoichRank) := pow_neg_one_succ_neg _
    · have heR : (-1 : ℝ) ^ (N.fullyOpen.stoichRank + 1) = -1 := by
        have h1 : (Int.cast ((-1 : ℤ) ^ (N.fullyOpen.stoichRank + 1)) : ℝ) = -1 := by
          rw [he]
          norm_num
        rw [pow_neg_one_cast] at h1
        exact h1
      rw [heR] at hdet
      have hneg : (N.fullyOpen.reducedJacobian κ c ystar).det < 0 := by
        linarith
      have hsign : ((SignType.sign
          (N.fullyOpen.reducedJacobian κ c ystar).det : SignType) : ℤ) = -1 := by
        rw [sign_neg hneg]
        rfl
      rw [hsign, hdeg]
      calc (-1 : ℤ) = (-1 : ℤ) ^ (N.fullyOpen.stoichRank + 1) := by rw [he]
        _ = -((-1 : ℤ) ^ N.fullyOpen.stoichRank) := pow_neg_one_succ_neg _
  -- the counting step
  refine N.fullyOpen.exists_two_positiveSteadyStates_of_classDegree_neg_localDegree κ c ystar
    hzero hystar hfin ?_ hlocal ?_
  · rw [hdeg]
    exact pow_ne_zero _ (by norm_num : (-1 : ℤ) ≠ 0)
  · intro y hy
    exact N.fullyOpen_steadyStateMap_ne_zero_on_classBoundary κ c y hy

/-- **The Conradi–Feliu–Mincheva–Wiuf conclusion for a fully open network with an affine field:
a positive reduced Jacobian determinant.**

Let `N.fullyOpen` be the fully open extension of `N` with rate constants `κ`, whose field is in
dissipative affine form, and suppose the rank of the class is **odd**.  Then the total degree is
`(-1)^s = -1` and the exceptional local degree is `+1`, i.e. the reduced Jacobian determinant is
**positive** at the exceptional steady state.  If the class carries such a steady state, the class
carries **two distinct positive steady states**.

The oddness of the rank is the necessary condition: the local degree `+1` — the sign of a
positive reduced Jacobian determinant — is the exceptional one exactly when the class degree is
`-1`, i.e. when `s` is odd.  For even `s` the exceptional sign is the *negative* one, and the
statement is `Network.fullyOpen_exists_two_positiveSteadyStates_affine_of_det_sign`. -/
theorem fullyOpen_exists_two_positiveSteadyStates_affine_of_det_pos
    (N : Network S) (κ : N.fullyOpen.RateConstants) (c : Concentration S)
    (h : AffineField N.fullyOpen κ)
    (ystar : ClassCoord (N.fullyOpen))
    (hzero : N.fullyOpen.steadyStateMap κ c ystar = 0)
    (hystar : ystar ∈ N.fullyOpen.nonnegativeClassRegion c)
    (hfin : (N.fullyOpen.steadyStateMap κ c ⁻¹' {0} ∩
      N.fullyOpen.nonnegativeClassRegion c).Finite)
    (hodd : N.fullyOpen.stoichRank % 2 = 1)
    (hdet : 0 < (N.fullyOpen.reducedJacobian κ c ystar).det) :
    ∃ x y : Concentration S,
      x ≠ y ∧ N.fullyOpen.StoichCompatible c x ∧ Concentration.Positive x ∧
        N.fullyOpen.IsMassActionSteadyState κ x ∧
      N.fullyOpen.StoichCompatible c y ∧ Concentration.Positive y ∧
        N.fullyOpen.IsMassActionSteadyState κ y := by
  -- the rank is odd, so the exceptional sign is the positive one
  have hmod : (N.fullyOpen.stoichRank + 1) % 2 = 0 := by
    have h := Nat.mod_add_div (N.fullyOpen.stoichRank + 1) 2
    omega
  have heven : N.fullyOpen.stoichRank + 1 = 2 * ((N.fullyOpen.stoichRank + 1) / 2) := by
    have h := Nat.mod_add_div (N.fullyOpen.stoichRank + 1) 2
    rw [hmod] at h
    linarith
  have hsign : (-1 : ℤ) ^ (N.fullyOpen.stoichRank + 1) = 1 := by
    rw [heven, pow_neg_one_even]
  have heR : (-1 : ℝ) ^ (N.fullyOpen.stoichRank + 1) = 1 := by
    have h1 : (Int.cast ((-1 : ℤ) ^ (N.fullyOpen.stoichRank + 1)) : ℝ) = 1 := by
      rw [hsign]
      norm_num
    rw [pow_neg_one_cast] at h1
    exact h1
  refine fullyOpen_exists_two_positiveSteadyStates_affine_of_det_sign N κ c h ystar
    hzero hystar hfin ?_
  rw [heR]
  linarith

/-! ## 5. The multistationarity region in rank `s ≥ 2` -/

/-- **The multistationarity region in rank `s ≥ 2` is described by the sign of the reduced
determinant.**

Let the class degree of the compatibility class of `x₀` be the odd number `d ∈ {-1, 1}` — the
total degree `(-1)^s` of the Conradi–Feliu–Mincheva–Wiuf theorem — and suppose that every positive
steady state of the class is **nondegenerate**, i.e. that its reduced Jacobian determinant does not
vanish.  Then the class is **multistationary** — it carries two distinct positive steady states —
**if and only if** it carries a positive steady state whose **local degree**, the sign of its
reduced Jacobian determinant, is **opposite to the class degree**.

This is the higher-rank analogue of the rank-one description of the multistationarity region
(`Network.rankOne_multistationary_iff_det_pos`, and the explicit set of rate constants
`Network.rateMultistationarityRegion_iff_classIsMultistationary`): the region consists of those
parameters for which the reduced determinant has the exceptional sign at a positive steady state
of the class.  In rank one the class degree is `-1` and the exceptional sign is the positive one,
so the criterion reads "the reduced determinant is positive at some positive steady state"; in
rank `s ≥ 2` the exceptional sign is `(-1)^{s+1}`, positive exactly for odd `s`.

*Why the two directions hold.*  The class degree is the signed count of the zeros of the reduced
field in the nonnegative part of the class, the summand at a zero being the sign of the reduced
determinant there.  If one zero has the exceptional sign, the remaining zeros cannot be absent
(their contributions sum to `d - (-d) = 2d ≠ 0`), so there is a second zero; conversely, if there
are two zeros and every zero had the class degree `d`, the signed count would be `d · |Z|`, which
is `d` only for a single zero. -/
theorem multistationary_iff_exists_positiveSteadyState_localDegree_opposite
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite)
    (hdeg : N.nonnegativeClassDegree κ x₀ hfin = 1 ∨
      N.nonnegativeClassDegree κ x₀ hfin = -1)
    (hnd : ∀ y ∈ N.positiveSteadyStates_in_class κ x₀, (N.reducedJacobian κ x₀ y).det ≠ 0)
    (hbd : ∀ y ∈ N.classBoundary x₀, N.steadyStateMap κ x₀ y ≠ 0) :
    (∃ x y : Concentration S,
      x ≠ y ∧ N.StoichCompatible x₀ x ∧ Concentration.Positive x ∧ N.IsMassActionSteadyState κ x ∧
      N.StoichCompatible x₀ y ∧ Concentration.Positive y ∧ N.IsMassActionSteadyState κ y) ↔
      ∃ x : Concentration S, N.StoichCompatible x₀ x ∧ Concentration.Positive x ∧
        N.IsMassActionSteadyState κ x ∧
        ((SignType.sign (N.reducedJacobian κ x₀ (N.chartCoord x₀ x)).det : SignType) : ℤ)
          = -(N.nonnegativeClassDegree κ x₀ hfin) := by
  constructor
  · -- two distinct positive steady states: one of them has the exceptional local degree
    rintro ⟨x, y, hxy, hxc, hxp, hxs, hyc, hyp, hys⟩
    -- the chart coordinates of the two steady states are distinct zeros in the class
    have hz1 : N.chartCoord x₀ x ∈ hfin.toFinset := by
      rw [hfin.mem_toFinset, Set.mem_inter_iff]
      refine ⟨?_, ?_⟩
      · refine Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr ?_)
        have hfield : N.massActionVectorField κ x = 0 := by
          funext s
          exact hxs s
        simp only [steadyStateMap, reducedField]
        rw [N.affineChart_chartCoord hxc, hfield, map_zero]
      · rw [mem_nonnegativeClassRegion_iff, N.affineChart_chartCoord hxc]
        exact hxp.nonnegative
    have hz2 : N.chartCoord x₀ y ∈ hfin.toFinset := by
      rw [hfin.mem_toFinset, Set.mem_inter_iff]
      refine ⟨?_, ?_⟩
      · refine Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr ?_)
        have hfield : N.massActionVectorField κ y = 0 := by
          funext s
          exact hys s
        simp only [steadyStateMap, reducedField]
        rw [N.affineChart_chartCoord hyc, hfield, map_zero]
      · rw [mem_nonnegativeClassRegion_iff, N.affineChart_chartCoord hyc]
        exact hyp.nonnegative
    have hz1ne : N.chartCoord x₀ x ≠ N.chartCoord x₀ y := by
      intro hcon
      apply hxy
      have h1 : N.affineChart x₀ (N.chartCoord x₀ x) = N.affineChart x₀ (N.chartCoord x₀ y) := by
        rw [hcon]
      rwa [N.affineChart_chartCoord hxc, N.affineChart_chartCoord hyc] at h1
    -- every zero of the reduced field in the nonnegative class is a positive steady state
    have hzpos : ∀ z ∈ hfin.toFinset, z ∈ N.positiveSteadyStates_in_class κ x₀ := by
      intro z hz
      have hz1 : N.steadyStateMap κ x₀ z = 0 := (hfin.mem_toFinset.mp hz).1
      have hz2 : z ∈ N.nonnegativeClassRegion x₀ := (hfin.mem_toFinset.mp hz).2
      have hz3 : z ∉ N.classBoundary x₀ := by
        intro hzb
        exact hbd z hzb hz1
      have hz4 : z ∈ N.positiveClassRegion x₀ := by
        rcases (N.mem_nonnegativeClassRegion_iff_pos_or_boundary x₀ z).mp hz2 with h | h
        · exact h
        · exact absurd h hz3
      refine (N.mem_positiveSteadyStates_in_class_iff κ x₀ z).mpr ⟨?_, ?_⟩
      · exact (mem_positiveClassRegion_iff N x₀ z).mp hz4
      · exact (N.isMassActionSteadyState_affineChart_of_reducedField_eq_zero κ x₀ hz1).2
    -- the class degree is the signed count of the zeros
    have hsum : (∑ z ∈ hfin.toFinset,
        ((SignType.sign (N.reducedJacobian κ x₀ z).det : SignType) : ℤ))
        = N.nonnegativeClassDegree κ x₀ hfin := by
      unfold nonnegativeClassDegree localDegreeOn
      apply Finset.sum_congr rfl
      intro z hz
      rw [N.det_fderiv_steadyStateMap_eq_reducedJacobian_det]
    -- some zero has the local degree opposite to the class degree
    have hex : ∃ z ∈ hfin.toFinset,
        ((SignType.sign (N.reducedJacobian κ x₀ z).det : SignType) : ℤ)
          = -(N.nonnegativeClassDegree κ x₀ hfin) := by
      by_contra hcon
      -- otherwise every zero has the local degree of the class
      have hall : ∀ z ∈ hfin.toFinset,
          ((SignType.sign (N.reducedJacobian κ x₀ z).det : SignType) : ℤ)
            = N.nonnegativeClassDegree κ x₀ hfin := by
        intro z hz
        have hne0 : (N.reducedJacobian κ x₀ z).det ≠ 0 := hnd z (hzpos z hz)
        have hsign : ((SignType.sign (N.reducedJacobian κ x₀ z).det : SignType) : ℤ) = 1 ∨
            ((SignType.sign (N.reducedJacobian κ x₀ z).det : SignType) : ℤ) = -1 := by
          rcases lt_or_gt_of_ne hne0 with hlt' | hgt'
          · right
            rw [sign_neg hlt']
            rfl
          · left
            rw [sign_pos hgt']
            rfl
        rcases hsign with hsign | hsign
        · rcases hdeg with hdeg | hdeg
          · rw [hdeg, hsign]
          · exact (hcon ⟨z, hz, by norm_num [hdeg, hsign]⟩).elim
        · rcases hdeg with hdeg | hdeg
          · exact (hcon ⟨z, hz, by norm_num [hdeg, hsign]⟩).elim
          · rw [hdeg, hsign]
      -- the signed count is then `d` times the number of zeros
      have hsumd : N.nonnegativeClassDegree κ x₀ hfin
          = (hfin.toFinset.card : ℤ) * N.nonnegativeClassDegree κ x₀ hfin := by
        calc N.nonnegativeClassDegree κ x₀ hfin
            = (∑ z ∈ hfin.toFinset,
                ((SignType.sign (N.reducedJacobian κ x₀ z).det : SignType) : ℤ)) := hsum.symm
          _ = (∑ z ∈ hfin.toFinset, N.nonnegativeClassDegree κ x₀ hfin) := by
              rw [Finset.sum_congr rfl (fun z hz => hall z hz)]
          _ = (hfin.toFinset.card : ℤ) * N.nonnegativeClassDegree κ x₀ hfin := by
              rw [Finset.sum_const, nsmul_eq_mul]
      -- there are at least two zeros
      have hcard : 2 ≤ hfin.toFinset.card := by
        have hsub : {N.chartCoord x₀ x, N.chartCoord x₀ y} ⊆ hfin.toFinset := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with hz | hz
          · exact hz ▸ hz1
          · exact hz ▸ hz2
        calc 2 ≤ ({N.chartCoord x₀ x, N.chartCoord x₀ y} : Finset (ClassCoord N)).card := by
              rw [Finset.card_insert_of_notMem (by simp [hz1ne])]
              simp
            _ ≤ hfin.toFinset.card := Finset.card_le_card hsub
      -- the contradiction
      have hcardZ : (2 : ℤ) ≤ (hfin.toFinset.card : ℤ) := by
        exact_mod_cast hcard
      rcases hdeg with hdeg | hdeg
      · rw [hdeg] at hsumd
        linarith
      · rw [hdeg] at hsumd
        linarith
    obtain ⟨z, hz, hzlocal⟩ := hex
    -- the witness is the class point of the exceptional zero
    have hzst : N.StoichCompatible x₀ (N.affineChart x₀ z) ∧
        N.IsMassActionSteadyState κ (N.affineChart x₀ z) :=
      N.isMassActionSteadyState_affineChart_of_reducedField_eq_zero κ x₀
        (hfin.mem_toFinset.mp hz).1
    refine ⟨N.affineChart x₀ z, hzst.1,
      (N.mem_positiveSteadyStates_in_class_iff κ x₀ z).mp (hzpos z hz) |>.1, hzst.2, ?_⟩
    have hcoord : N.chartCoord x₀ (N.affineChart x₀ z) = z := N.chartCoord_affineChart x₀ z
    rw [hcoord]
    exact hzlocal
  · -- the exceptional local degree forces a second positive steady state
    rintro ⟨x, hxc, hxp, hxs, hlocal⟩
    set y := N.chartCoord x₀ x with hy
    have haff : N.affineChart x₀ y = x := by
      rw [hy]
      exact N.affineChart_chartCoord hxc
    have hfield : N.massActionVectorField κ x = 0 := by
      funext s
      exact hxs s
    have hzero : N.steadyStateMap κ x₀ y = 0 := by
      simp only [steadyStateMap, reducedField]
      rw [haff, hfield, map_zero]
    have hynonneg : y ∈ N.nonnegativeClassRegion x₀ := by
      rw [mem_nonnegativeClassRegion_iff, haff]
      exact hxp.nonnegative
    -- the class degree is not its own negative
    have hdne : N.nonnegativeClassDegree κ x₀ hfin ≠
        -(N.nonnegativeClassDegree κ x₀ hfin) := by
      rcases hdeg with hdeg | hdeg
      · rw [hdeg]
        intro h
        linarith
      · rw [hdeg]
        intro h
        linarith
    refine N.exists_two_positiveSteadyStates_of_localDegree_ne_classDegree κ x₀ y hzero hynonneg
      hfin ?_ hbd
    rw [hy]
    exact fun hcon => hdne (hcon.symm.trans hlocal)

/-- **The multistationarity region in rank `s ≥ 2`, in the determinant form: the class degree is
`-1`.**

This is the situation of the rank-one networks, and of the Conradi–Feliu–Mincheva–Wiuf total
degree in odd rank: the class degree is `-1`, so the exceptional local degree is `+1`, i.e. the
reduced Jacobian determinant is **positive**.  The class is multistationary if and only if it
carries a positive steady state with a positive reduced Jacobian determinant — the higher-rank
form of `Network.rankOne_multistationary_iff_det_pos`. -/
theorem multistationary_iff_exists_positiveSteadyState_det_pos
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite)
    (hdeg : N.nonnegativeClassDegree κ x₀ hfin = -1)
    (hnd : ∀ y ∈ N.positiveSteadyStates_in_class κ x₀, (N.reducedJacobian κ x₀ y).det ≠ 0)
    (hbd : ∀ y ∈ N.classBoundary x₀, N.steadyStateMap κ x₀ y ≠ 0) :
    (∃ x y : Concentration S,
      x ≠ y ∧ N.StoichCompatible x₀ x ∧ Concentration.Positive x ∧ N.IsMassActionSteadyState κ x ∧
      N.StoichCompatible x₀ y ∧ Concentration.Positive y ∧ N.IsMassActionSteadyState κ y) ↔
      ∃ x : Concentration S, N.StoichCompatible x₀ x ∧ Concentration.Positive x ∧
        N.IsMassActionSteadyState κ x ∧
        0 < (N.reducedJacobian κ x₀ (N.chartCoord x₀ x)).det := by
  rw [multistationary_iff_exists_positiveSteadyState_localDegree_opposite N κ x₀ hfin
    (Or.inr hdeg) hnd hbd]
  constructor
  · rintro ⟨x, hxc, hxp, hxs, hlocal⟩
    refine ⟨x, hxc, hxp, hxs, ?_⟩
    have hcast : ((SignType.sign (N.reducedJacobian κ x₀ (N.chartCoord x₀ x)).det : SignType) : ℤ)
        = 1 := by
      rw [hlocal, hdeg]
      norm_num
    have hsign : SignType.sign (N.reducedJacobian κ x₀ (N.chartCoord x₀ x)).det = 1 := by
      cases hs : SignType.sign (N.reducedJacobian κ x₀ (N.chartCoord x₀ x)).det with
      | zero => rw [hs] at hcast; norm_num at hcast
      | neg => rw [hs] at hcast; norm_num at hcast
      | pos => rfl
    exact (sign_eq_one_iff).mp hsign
  · rintro ⟨x, hxc, hxp, hxs, hdet⟩
    refine ⟨x, hxc, hxp, hxs, ?_⟩
    have hsign : ((SignType.sign (N.reducedJacobian κ x₀ (N.chartCoord x₀ x)).det : SignType) : ℤ)
        = 1 := by
      rw [sign_pos hdet]
      rfl
    rw [hsign, hdeg]
    norm_num

/-! ## 6. A consistency check: the fully open two-species instance -/

namespace CFMWExample

open DegreeExample

/-- **The local degree at the unique steady state of the fully open two-species network is the
class degree, not the exceptional sign.**

The network is the fully open extension of the reaction-free network on two species: the four
flow reactions `∅ → A`, `A → ∅`, `∅ → B`, `B → ∅`.  Its stoichiometric subspace is the whole
space, so `s = 2`, the smallest dimension in which the degree argument is not the rank-one
intermediate-value argument.  The class degree is the total degree `(-1)^2 = +1`, and the reduced
Jacobian determinant at its unique zero `b` is `1 > 0`, so the local degree there is `+1` — the
class degree itself, and *not* the exceptional sign `-1`.  The class therefore carries no
exceptional steady state, and indeed it carries exactly one positive steady state
(`DegreeExampleParity.card_positiveSteadyStates_eq_one`).

This is the `s = 2` instance of the higher-rank criterion: in even rank the exceptional sign is
the *negative* one, so a positive reduced determinant is *not* the multistationarity signature. -/
theorem twoSpecies_localDegree_eq_classDegree :
    ((SignType.sign (N.reducedJacobian rates 0 b).det : SignType) : ℤ)
      = N.nonnegativeClassDegree rates 0 hfinN := by
  rw [DegreeExampleHomogeneity.det_at_b]
  rw [sign_pos (by norm_num : (0 : ℝ) < 1)]
  rw [nonnegativeClassDegree_eq_one]
  rfl

/-- **The exceptional sign does not occur at the positive steady states of the fully open
two-species network.**  Every positive steady state of the class has a *positive* reduced
Jacobian determinant, so the local degree is `+1` everywhere, and the exceptional sign `-1` never
occurs: the class is not multistationary. -/
theorem twoSpecies_no_exceptionalSteadyState :
    ∀ y ∈ N.positiveSteadyStates_in_class rates 0,
      0 < (N.reducedJacobian rates 0 y).det := by
  intro y hy
  have hy0 : N.steadyStateMap rates 0 y = 0 := Set.mem_preimage.mp hy.1
  have hyb : y = b := by
    have hy' : y ∈ N.steadyStateMap rates 0 ⁻¹' {0} := Set.mem_preimage.mpr hy0
    rw [steadyStateMap_preimage_zero] at hy'
    exact Set.mem_singleton_iff.mp hy'
  subst hyb
  rw [DegreeExampleHomogeneity.det_at_b]
  norm_num

end CFMWExample

end CRNT.Network



/-! ## Axioms -/

#print axioms CRNT.exists_other_zero_of_localDegreeOn_ne
#print axioms CRNT.Network.exists_two_positiveSteadyStates_of_localDegree_ne_classDegree
#print axioms CRNT.Network.exists_two_positiveSteadyStates_of_localDegree_eq_one
#print axioms CRNT.Network.exists_two_positiveSteadyStates_of_reducedDet_pos
#print axioms CRNT.Network.classDegree_of_affineLinear_eq_sign_reducedDet
#print axioms CRNT.Network.fullyOpen_classDegree_eq_pow_neg_one
#print axioms CRNT.Network.fullyOpen_exists_two_positiveSteadyStates_affine_of_det_sign
#print axioms CRNT.Network.fullyOpen_exists_two_positiveSteadyStates_affine_of_det_pos
#print axioms CRNT.Network.multistationary_iff_exists_positiveSteadyState_localDegree_opposite
#print axioms CRNT.Network.multistationary_iff_exists_positiveSteadyState_det_pos
#print axioms CRNT.Network.CFMWExample.twoSpecies_localDegree_eq_classDegree
#print axioms CRNT.Network.CFMWExample.twoSpecies_no_exceptionalSteadyState
