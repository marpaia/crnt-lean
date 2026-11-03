import CRNT.Multistationarity.SteadyStateDegree
import CRNT.Multistationarity.ParametrizedLocalDegree
import CRNT.Multistationarity.DegreeHomotopyInvariant
import CRNT.Dynamics.MassActionField
import CRNT.Equilibria.CompatibilityClassGeometry

/-!
# Steady-state consequences of a finite signed degree count

The reduced field is represented in stoichiometric coordinates. A finite signed
count which is nonzero supplies a zero, and boundary exclusion makes it positive.
The rate-independence results require compact containment, boundary avoidance,
and regularity of every intermediate zero, as displayed in their signatures.
They do not cover homotopies through degenerate zeros or prove the general
Brouwer total-degree theorem under dissipativity.
-/

namespace CRNT

namespace Network

open scoped BigOperators Topology Classical

open Set Filter

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## The class-projected steady-state map -/

/-- **The reduced (class-coordinate) steady-state map.**  This is the mass-action
vector field restricted to the compatibility class of `x₀` and read in the chart
coordinates of `StoichChart`: `y ↦ stoichProj (F (affineChart x₀ y))`.  Its zeros are
exactly the mass-action steady states in the class. -/
noncomputable def steadyStateMap (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) : (Fin N.stoichRank → ℝ) → (Fin N.stoichRank → ℝ) :=
  N.reducedField κ x₀

/-- The chart coordinate space of the compatibility class. -/
abbrev ClassCoord (N : Network S) := Fin N.stoichRank → ℝ

/-- **The class-projected steady-state map on the ambient concentration space.**
This is `x ↦ π(x + F(x))`, where `π` is the affine projection onto the compatibility
class of `x₀` (the chart inverse of `StoichChart`).  Its fixed points are exactly the
mass-action steady states of the class; see
`isMassActionSteadyState_iff_fixed_classSteadyStateMap`. -/
noncomputable def classSteadyStateMap (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) (x : Concentration S) : Concentration S :=
  x₀ + N.stoichChart (N.stoichProj (x - x₀ + N.massActionVectorField κ x))

/-- The class-projected map lands in the compatibility class of `x₀`. -/
theorem classSteadyStateMap_mem_class (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) (x : Concentration S) :
    N.StoichCompatible x₀ (N.classSteadyStateMap κ x₀ x) := by
  refine (N.stoichCompatible_iff_exists_sub x₀ (N.classSteadyStateMap κ x₀ x)).mpr
    ⟨N.stoichChart (N.stoichProj (x - x₀ + N.massActionVectorField κ x)),
      N.stoichChart_mem _, ?_⟩
  rfl

/-- **The chart coordinate of the class map is `y + steadyStateMap y`.**  On the class
point `x = affineChart x₀ y`, the ambient fixed-point map `x ↦ π(x + F(x))` reads in
chart coordinates as `y ↦ y + reducedField κ x₀ y`. -/
theorem classSteadyStateMap_chartCoord (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) (y : ClassCoord N) :
    N.chartCoord x₀ (N.classSteadyStateMap κ x₀ (N.affineChart x₀ y)) =
      y + N.steadyStateMap κ x₀ y := by
  simp only [classSteadyStateMap, chartCoord, steadyStateMap, reducedField, affineChart,
    add_sub_cancel_left, map_add, N.stoichProj_stoichChart]

/-- The same statement in the "`x ↦ x + F`" form suggested by the ambient definition:
the chart coordinate is the ambient displacement plus the reduced field. -/
theorem classSteadyStateMap_chartCoord_eq (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) (y : ClassCoord N) :
    N.chartCoord x₀ (N.classSteadyStateMap κ x₀ (N.affineChart x₀ y)) =
      N.chartCoord x₀ (N.affineChart x₀ y) + N.steadyStateMap κ x₀ y := by
  rw [N.chartCoord_affineChart, N.classSteadyStateMap_chartCoord]

/-- **Fixed points of the class map are exactly steady states.**  For a point `x` in the
compatibility class of `x₀`, `π(x + F(x)) = x` if and only if `F(x) = 0`. -/
theorem isMassActionSteadyState_iff_fixed_classSteadyStateMap
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) {x : Concentration S}
    (hx : N.StoichCompatible x₀ x) :
    N.IsMassActionSteadyState κ x ↔ N.classSteadyStateMap κ x₀ x = x := by
  constructor
  · intro hsteady
    unfold classSteadyStateMap
    have hF : N.massActionVectorField κ x = 0 := funext hsteady
    rw [hF, add_zero]
    have hxcoord : N.affineChart x₀ (N.chartCoord x₀ x) = x := N.affineChart_chartCoord hx
    have hdiff : x - x₀ = N.stoichChart (N.chartCoord x₀ x) := by
      calc x - x₀ = N.affineChart x₀ (N.chartCoord x₀ x) - x₀ := by rw [hxcoord]
        _ = N.stoichChart (N.chartCoord x₀ x) := by rw [affineChart]; abel
    rw [hdiff, N.stoichProj_stoichChart]
    exact hxcoord
  · intro hfix
    -- compare chart coordinates
    have hxcoord : N.affineChart x₀ (N.chartCoord x₀ x) = x := N.affineChart_chartCoord hx
    have hfix' : N.classSteadyStateMap κ x₀ (N.affineChart x₀ (N.chartCoord x₀ x)) =
        N.affineChart x₀ (N.chartCoord x₀ x) := by
      rw [hxcoord]
      exact hfix
    have hcoord := congrArg (N.chartCoord x₀) hfix'
    rw [N.classSteadyStateMap_chartCoord, N.chartCoord_affineChart] at hcoord
    -- `y + F(y) = y`, hence `F(y) = 0`
    have hy : N.chartCoord x₀ x + N.steadyStateMap κ x₀ (N.chartCoord x₀ x) =
        N.chartCoord x₀ x := hcoord
    have hzero : N.steadyStateMap κ x₀ (N.chartCoord x₀ x) = 0 := by
      have := congrArg (fun v => v - N.chartCoord x₀ x) hy
      simpa using this
    -- transport the zero of the reduced field to the steady state
    have hss := N.isMassActionSteadyState_affineChart_of_reducedField_eq_zero κ x₀ hzero
    rw [N.affineChart_chartCoord hx] at hss
    exact hss.2

/-! ## The compact nonnegative part of the class and the class degree -/

/-- The chart image of the **positive** part of the compatibility class.  This is the
interior of the nonnegative class region (inside the chart). -/
def positiveClassRegion (N : Network S) (x₀ : Concentration S) : Set (ClassCoord N) :=
  {y | Concentration.Positive (N.affineChart x₀ y)}

/-- The chart image of the **nonnegative** part of the compatibility class.  This is
the compact part of the class when the class is bounded; its frontier consists of the
class points with at least one vanishing coordinate (`classBoundary`). -/
def nonnegativeClassRegion (N : Network S) (x₀ : Concentration S) : Set (ClassCoord N) :=
  {y | Concentration.Nonnegative (N.affineChart x₀ y)}

/-- The **boundary** of the nonnegative compatibility class: nonnegative class points
which are not strictly positive, i.e. points with at least one vanishing species
coordinate.  These are exactly the points which are not interior to the class. -/
def classBoundary (N : Network S) (x₀ : Concentration S) : Set (ClassCoord N) :=
  {y | Concentration.Nonnegative (N.affineChart x₀ y) ∧ ¬ Concentration.Positive (N.affineChart x₀ y)}

theorem mem_positiveClassRegion_iff (N : Network S) (x₀ : Concentration S)
    (y : ClassCoord N) :
    y ∈ N.positiveClassRegion x₀ ↔ Concentration.Positive (N.affineChart x₀ y) := Iff.rfl

theorem mem_nonnegativeClassRegion_iff (N : Network S) (x₀ : Concentration S)
    (y : ClassCoord N) :
    y ∈ N.nonnegativeClassRegion x₀ ↔ Concentration.Nonnegative (N.affineChart x₀ y) := Iff.rfl

theorem mem_classBoundary_iff (N : Network S) (x₀ : Concentration S)
    (y : ClassCoord N) :
    y ∈ N.classBoundary x₀ ↔
      Concentration.Nonnegative (N.affineChart x₀ y) ∧ ¬ Concentration.Positive (N.affineChart x₀ y) := Iff.rfl

/-- The positive class region is open. -/
theorem isOpen_positiveClassRegion (N : Network S) (x₀ : Concentration S) :
    IsOpen (N.positiveClassRegion x₀) := by
  have h : N.positiveClassRegion x₀
      = ⋂ s : S, {y : ClassCoord N | 0 < (N.affineChart x₀ y) s} := by
    apply Set.ext
    intro y
    simp [positiveClassRegion, Concentration.Positive]
  rw [h]
  refine isOpen_iInter_of_finite fun s => ?_
  have hcont : Continuous fun y : ClassCoord N => (N.affineChart x₀ y) s := by
    unfold affineChart
    fun_prop
  exact isOpen_lt continuous_const hcont

/-- The nonnegative class region is closed. -/
theorem isClosed_nonnegativeClassRegion (N : Network S) (x₀ : Concentration S) :
    IsClosed (N.nonnegativeClassRegion x₀) := by
  have h : N.nonnegativeClassRegion x₀
      = ⋂ s : S, {y : ClassCoord N | 0 ≤ (N.affineChart x₀ y) s} := by
    apply Set.ext
    intro y
    simp [nonnegativeClassRegion, Concentration.Nonnegative]
  rw [h]
  exact isClosed_iInter fun s => isClosed_le continuous_const (by unfold affineChart; fun_prop)

/-- The closure of the positive class region stays in the nonnegative class region. -/
theorem closure_positiveClassRegion_subset_nonnegativeClassRegion
    (N : Network S) (x₀ : Concentration S) :
    closure (N.positiveClassRegion x₀) ⊆ N.nonnegativeClassRegion x₀ := by
  apply closure_minimal _ (N.isClosed_nonnegativeClassRegion x₀)
  intro y hy
  exact (mem_positiveClassRegion_iff N x₀ y).mp hy |>.nonnegative

/-- The nonnegative class region is the disjoint union of the positive region and the
boundary. -/
theorem nonnegativeClassRegion_eq_positive_union_boundary
    (N : Network S) (x₀ : Concentration S) :
    N.nonnegativeClassRegion x₀ = N.positiveClassRegion x₀ ∪ N.classBoundary x₀ := by
  ext y
  simp only [mem_nonnegativeClassRegion_iff, mem_positiveClassRegion_iff, mem_classBoundary_iff,
    Set.mem_union]
  constructor
  · intro hnn
    by_cases hp : Concentration.Positive (N.affineChart x₀ y)
    · exact Or.inl hp
    · exact Or.inr ⟨hnn, hp⟩
  · rintro (hp | ⟨hnn, _⟩)
    · exact hp.nonnegative
    · exact hnn

/-- Convexity of the positive class region: positivity is convex, and the affine chart
identifies the region with the positive part of the compatibility class. -/
theorem convex_positiveClassRegion (N : Network S) (x₀ : Concentration S) :
    Convex ℝ (N.positiveClassRegion x₀) := by
  intro y hy z hz a b ha hb hab
  rw [mem_positiveClassRegion_iff] at hy hz ⊢
  -- the chart is affine: the combination in coordinates is the combination of points
  have hpt : N.affineChart x₀ (a • y + b • z) =
      a • N.affineChart x₀ y + b • N.affineChart x₀ z := by
    funext s
    simp only [affineChart, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hchart : N.stoichChart (a • y + b • z) s =
        a * N.stoichChart y s + b * N.stoichChart z s := by
      rw [map_add, map_smul, map_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hchart]
    have : a * x₀ s + b * x₀ s = x₀ s := by
      calc a * x₀ s + b * x₀ s = (a + b) * x₀ s := by ring
        _ = 1 * x₀ s := by rw [hab]
        _ = x₀ s := by ring
    linarith only [this]
  rw [hpt]
  intro s
  have h1 : 0 ≤ a * (N.affineChart x₀ y) s := mul_nonneg ha (hy s).le
  have h2 : 0 ≤ b * (N.affineChart x₀ z) s := mul_nonneg hb (hz s).le
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · have hb1 : b = 1 := by linarith
    have : a = 0 := ha0.symm
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, this, zero_mul, zero_add]
    rw [hb1, one_mul]
    exact hz s
  · have := mul_pos hapos (hy s)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_pos_of_pos_of_nonneg this h2

/-- The closure of the positive class region is convex. -/
theorem convex_closure_positiveClassRegion (N : Network S) (x₀ : Concentration S) :
    Convex ℝ (closure (N.positiveClassRegion x₀)) :=
  (N.convex_positiveClassRegion x₀).closure

/-! ## The class degree -/

/-- **The relative class degree on the nonnegative part of the class.**  The signed
count of the zeros of the steady-state map in the chart image of the nonnegative
compatibility class.  This is the degree used in the `s ≥ 2` existence argument; it is
relative because the mass-action field can have infinite zero sets outside the region. -/
noncomputable def nonnegativeClassDegree (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite) : ℤ :=
  localDegreeOn (N.steadyStateMap κ x₀) 0 (N.nonnegativeClassRegion x₀) hfin

/-- The class degree on the positive part of the class. -/
noncomputable def positiveClassDegree (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.positiveClassRegion x₀).Finite) : ℤ :=
  localDegreeOn (N.steadyStateMap κ x₀) 0 (N.positiveClassRegion x₀) hfin

/-! ## Nonzero degree forces a positive steady state -/

/-- **Nonzero class degree forces a zero in the nonnegative class.**  This is the
domain-relative existence principle `exists_mem_of_localDegreeOn_ne_zero` applied to
the steady-state map. -/
theorem exists_zero_of_nonnegativeClassDegree_ne_zero (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite)
    (hdeg : N.nonnegativeClassDegree κ x₀ hfin ≠ 0) :
    ∃ y ∈ N.nonnegativeClassRegion x₀, N.steadyStateMap κ x₀ y = 0 :=
  exists_mem_of_localDegreeOn_ne_zero (N.steadyStateMap κ x₀) 0 hfin hdeg

/-- **Nonzero class degree plus boundary nonvanishing forces a zero in the positive
class.**  A zero found in the nonnegative class cannot lie on `classBoundary`, since
the field is assumed nonzero there; hence it is strictly positive.  This is the
`x ↦ F(x)` form of the Conradi–Feliu–Mincheva–Wiuf existence step. -/
theorem exists_positive_of_nonnegativeClassDegree_ne_zero
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite)
    (hdeg : N.nonnegativeClassDegree κ x₀ hfin ≠ 0)
    (hbd : ∀ y ∈ N.classBoundary x₀, N.steadyStateMap κ x₀ y ≠ 0) :
    ∃ y ∈ N.positiveClassRegion x₀, N.steadyStateMap κ x₀ y = 0 := by
  obtain ⟨y, hynn, hzero⟩ := N.exists_zero_of_nonnegativeClassDegree_ne_zero κ x₀ hfin hdeg
  refine ⟨y, ?_, hzero⟩
  by_contra hypos
  exact hbd y ⟨hynn, hypos⟩ hzero

/-- **Positive steady state from a nonzero class degree.**  Combine the existence step
with the bridge from zeros of the reduced field to mass-action steady states
(`isMassActionSteadyState_affineChart_of_reducedField_eq_zero`).  The steady state lies
in the positive compatibility class of `x₀`. -/
theorem exists_positiveSteadyState_of_nonnegativeClassDegree_ne_zero
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite)
    (hdeg : N.nonnegativeClassDegree κ x₀ hfin ≠ 0)
    (hbd : ∀ y ∈ N.classBoundary x₀, N.steadyStateMap κ x₀ y ≠ 0) :
    ∃ x : Concentration S,
      N.StoichCompatible x₀ x ∧ Concentration.Positive x ∧ N.IsMassActionSteadyState κ x := by
  obtain ⟨y, hypos, hzero⟩ := N.exists_positive_of_nonnegativeClassDegree_ne_zero κ x₀ hfin hdeg hbd
  obtain ⟨hcompat, hsteady⟩ :=
    N.isMassActionSteadyState_affineChart_of_reducedField_eq_zero κ x₀ hzero
  exact ⟨N.affineChart x₀ y, hcompat, hypos, hsteady⟩

/-- A version using the positive-region degree directly: nonzero degree on the positive
part already yields a zero there, with no separate boundary hypothesis. -/
theorem exists_positive_of_positiveClassDegree_ne_zero
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.positiveClassRegion x₀).Finite)
    (hdeg : N.positiveClassDegree κ x₀ hfin ≠ 0) :
    ∃ y ∈ N.positiveClassRegion x₀, N.steadyStateMap κ x₀ y = 0 :=
  exists_mem_of_localDegreeOn_ne_zero (N.steadyStateMap κ x₀) 0 hfin hdeg

/-- Positive steady state from a nonzero degree on the positive part of the class. -/
theorem exists_positiveSteadyState_of_positiveClassDegree_ne_zero
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.positiveClassRegion x₀).Finite)
    (hdeg : N.positiveClassDegree κ x₀ hfin ≠ 0) :
    ∃ x : Concentration S,
      N.StoichCompatible x₀ x ∧ Concentration.Positive x ∧ N.IsMassActionSteadyState κ x := by
  obtain ⟨y, hypos, hzero⟩ := N.exists_positive_of_positiveClassDegree_ne_zero κ x₀ hfin hdeg
  obtain ⟨hcompat, hsteady⟩ :=
    N.isMassActionSteadyState_affineChart_of_reducedField_eq_zero κ x₀ hzero
  exact ⟨N.affineChart x₀ y, hcompat, hypos, hsteady⟩

/-! ## The homotopy-to-a-constant form and nonzero degree -/

/-- **A map avoiding zero on the closure of a region has relative degree zero.**  If
`f` has no zero in `closure U`, then it has no zero in `U` either, so the signed count
over `U` is the empty sum.  This is the endpoint of the classical homotopy-to-a-constant
argument: on a compact convex set a nowhere-zero map is homotopic, by contraction to a
point, to a constant nonzero map, whose degree at `0` is zero.  We record the direct
relative-degree form, which is what the existence argument actually uses. -/
theorem localDegreeOn_eq_zero_of_avoids_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → E} {U : Set E}
    {hfin : (f ⁻¹' {(0 : E)} ∩ U).Finite}
    (havoid : ∀ x ∈ closure U, f x ≠ 0) :
    localDegreeOn f 0 U hfin = 0 := by
  apply localDegreeOn_eq_zero_of_preimage_inter_empty f 0 hfin
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
    Set.mem_empty_iff_false, iff_false, not_and]
  intro hx hxU
  exact havoid x (subset_closure hxU) hx

/-- **Nonzero relative degree forces a zero on the closure.**  This is the
contrapositive of `localDegreeOn_eq_zero_of_avoids_zero`, and the homotopy-to-a-constant
form of the existence principle: a map whose degree on `U` is nonzero cannot avoid zero
on all of `closure U`. -/
theorem exists_mem_closure_of_localDegreeOn_ne_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → E} {U : Set E}
    {hfin : (f ⁻¹' {(0 : E)} ∩ U).Finite}
    (hdeg : localDegreeOn f 0 U hfin ≠ 0) :
    ∃ x ∈ closure U, f x = 0 := by
  by_contra h
  apply hdeg
  apply localDegreeOn_eq_zero_of_avoids_zero
  intro x hx hfx
  exact h ⟨x, hx, hfx⟩

/-- The reduced steady-state map is smooth in the class coordinates. -/
theorem steadyStateMap_contDiff (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) {n : WithTop ℕ∞} :
    ContDiff ℝ n (N.steadyStateMap κ x₀) := by
  have hchart : ContDiff ℝ n (N.affineChart x₀) :=
    contDiff_const.add N.stoichChart.contDiff
  have hf : ContDiff ℝ n (fun y => N.massActionVectorField κ (N.affineChart x₀ y)) :=
    (N.massActionVectorField_contDiff κ).comp hchart
  change ContDiff ℝ n (fun y => N.stoichProj (N.massActionVectorField κ (N.affineChart x₀ y)))
  simpa only [Function.comp_def] using N.stoichProj.contDiff.comp hf

/-! ### Rate-constant interpolation -/

/-- The convex interpolation `(1-t) κ + t κ'` of two positive rate vectors.  Positivity
is preserved because the positive cone in `ℝ` is convex. -/
noncomputable def rateConstantsInterpolate (N : Network S) (κ₀ κ₁ : N.RateConstants)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : N.RateConstants where
  k r := (1 - t) * κ₀.k r + t * κ₁.k r
  positive r := by
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    by_cases hz : t = 0
    · simp [hz, κ₀.positive r]
    · have htp : 0 < t := lt_of_le_of_ne ht0 (Ne.symm hz)
      exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr ht1) (κ₀.positive r).le)
        (mul_pos htp (κ₁.positive r))

/-- Mass-action kinetics is affine-linear in the rate vector, so interpolating the rate
constants interpolates the vector field with the same weights. -/
theorem massActionVectorField_interpolate (N : Network S) (κ₀ κ₁ : N.RateConstants)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (x : Concentration S) :
    N.massActionVectorField (N.rateConstantsInterpolate κ₀ κ₁ t ht) x =
      (1 - t) • N.massActionVectorField κ₀ x + t • N.massActionVectorField κ₁ x := by
  funext s
  simp only [massActionVectorField_apply, massActionRate, rateConstantsInterpolate,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- The reduced field of the interpolated rate vector is the linear interpolation of the
two reduced fields.  This is the coordinate form of the rate-constant homotopy. -/
theorem steadyStateMap_interpolate (N : Network S) (κ₀ κ₁ : N.RateConstants)
    (x₀ : Concentration S) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (y : ClassCoord N) :
    N.steadyStateMap (N.rateConstantsInterpolate κ₀ κ₁ t ht) x₀ y =
      (1 - t) • N.steadyStateMap κ₀ x₀ y + t • N.steadyStateMap κ₁ x₀ y := by
  simp only [steadyStateMap, reducedField]
  rw [massActionVectorField_interpolate]
  simp only [map_add, map_smul]

/-- **The rate-constant homotopy** on the class-coordinate steady-state maps.  Its two
endpoints are the steady-state maps for `κ₀` and `κ₁`; at parameter `t` it is the
steady-state map of the interpolated rate vector `(1-t) κ₀ + t κ₁`
(`steadyStateHomotopy_eq_rateConstantsInterpolate`). -/
noncomputable def steadyStateHomotopy (N : Network S) (κ₀ κ₁ : N.RateConstants)
    (x₀ : Concentration S) : ℝ × ClassCoord N → ClassCoord N :=
  fun p => (1 - p.1) • N.steadyStateMap κ₀ x₀ p.2 +
    p.1 • N.steadyStateMap κ₁ x₀ p.2

/-- The rate-constant homotopy is smooth. -/
theorem steadyStateHomotopy_contDiff (N : Network S) (κ₀ κ₁ : N.RateConstants)
    (x₀ : Concentration S) :
    ContDiff ℝ 1 (N.steadyStateHomotopy κ₀ κ₁ x₀) := by
  have h0 : ContDiff ℝ 1 (fun p : ℝ × ClassCoord N =>
      N.steadyStateMap κ₀ x₀ p.2) :=
    (N.steadyStateMap_contDiff (n := 1) κ₀ x₀).comp contDiff_snd
  have h1 : ContDiff ℝ 1 (fun p : ℝ × ClassCoord N =>
      N.steadyStateMap κ₁ x₀ p.2) :=
    (N.steadyStateMap_contDiff (n := 1) κ₁ x₀).comp contDiff_snd
  have ha : ContDiff ℝ 1 (fun p : ℝ × ClassCoord N => (1 : ℝ) - p.1) :=
    contDiff_const.sub contDiff_fst
  have hsum := (ha.smul h0).add (contDiff_fst.smul h1)
  change ContDiff ℝ 1 (fun p : ℝ × ClassCoord N =>
    (1 - p.1) • N.steadyStateMap κ₀ x₀ p.2 +
      p.1 • N.steadyStateMap κ₁ x₀ p.2)
  exact hsum

@[simp] theorem steadyStateHomotopy_apply_zero (N : Network S) (κ₀ κ₁ : N.RateConstants)
    (x₀ : Concentration S) (y : ClassCoord N) :
    N.steadyStateHomotopy κ₀ κ₁ x₀ (0, y) = N.steadyStateMap κ₀ x₀ y := by
  simp [steadyStateHomotopy]

@[simp] theorem steadyStateHomotopy_apply_one (N : Network S) (κ₀ κ₁ : N.RateConstants)
    (x₀ : Concentration S) (y : ClassCoord N) :
    N.steadyStateHomotopy κ₀ κ₁ x₀ (1, y) = N.steadyStateMap κ₁ x₀ y := by
  simp [steadyStateHomotopy]

/-- At every parameter in the unit interval, the rate-constant homotopy is the reduced
steady-state map of the convexly interpolated positive rate vector. -/
theorem steadyStateHomotopy_eq_rateConstantsInterpolate (N : Network S)
    (κ₀ κ₁ : N.RateConstants) (x₀ : Concentration S) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (y : ClassCoord N) :
    N.steadyStateHomotopy κ₀ κ₁ x₀ (t, y) =
      N.steadyStateMap (N.rateConstantsInterpolate κ₀ κ₁ t ht) x₀ y :=
  (N.steadyStateMap_interpolate κ₀ κ₁ x₀ t ht y).symm

/-! ## Independence of the rate constants -/

/-- **Rate-constant independence on the positive class region.**  Suppose that the class
degree is defined along the linear interpolation of the two reduced fields, that the
interpolated slices have no zero on the boundary of the positive region, that all
interior zeros are nondegenerate, and that the interior zero set is finite.  Then the
relative degree of the steady-state map on the positive part of the class is the same
for `κ₀` and `κ₁`.

This is the precise form of the CFMW statement that the degree is a property of the
network and of the boundary sign pattern, not of the numerical rate constants.  The
hypothesis `hbd` is the boundary sign/nonvanishing condition; it is what the convexity of
the inward cone turns into a condition on the interpolated field in applications. -/
theorem positiveClassDegree_rate_independent
    (N : Network S) (κ₀ κ₁ : N.RateConstants) (x₀ : Concentration S)
    (hUcpt : IsCompact (closure (N.positiveClassRegion x₀)))
    (hbd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ closure (N.positiveClassRegion x₀),
      N.steadyStateHomotopy κ₀ κ₁ x₀ (t, y) = 0 → y ∈ N.positiveClassRegion x₀)
    (hreg : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ N.positiveClassRegion x₀,
      N.steadyStateHomotopy κ₀ κ₁ x₀ (t, y) = 0 →
      LinearMap.det
        (partialFDeriv (N.steadyStateHomotopy κ₀ κ₁ x₀) (t, y)).toLinearMap ≠ 0)
    (hfin : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ((fun y => N.steadyStateHomotopy κ₀ κ₁ x₀ (t, y)) ⁻¹' {0} ∩
        N.positiveClassRegion x₀).Finite) :
    N.positiveClassDegree κ₀ x₀
        (by simpa [steadyStateHomotopy] using hfin 0 (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1))
      = N.positiveClassDegree κ₁ x₀
        (by simpa [steadyStateHomotopy] using hfin 1 (by norm_num : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)) := by
  have hmain := localDegreeOn_homotopy_invariant (N.steadyStateHomotopy κ₀ κ₁ x₀)
    (N.steadyStateHomotopy_contDiff κ₀ κ₁ x₀)
    (N.isOpen_positiveClassRegion x₀) hUcpt hbd hreg hfin
    (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (by norm_num : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
  simpa [positiveClassDegree, steadyStateHomotopy] using hmain

/-- **Passing from the positive region to the nonnegative region.**  If the steady-state
map has no zero on the boundary `classBoundary`, then its zeros in the nonnegative class
are exactly its zeros in the positive class, and the two relative degrees agree. -/
theorem nonnegativeClassDegree_eq_positiveClassDegree_of_boundary_ne_zero
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (hfinN : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite)
    (hfinP : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.positiveClassRegion x₀).Finite)
    (hbd : ∀ y ∈ N.classBoundary x₀, N.steadyStateMap κ x₀ y ≠ 0) :
    N.nonnegativeClassDegree κ x₀ hfinN = N.positiveClassDegree κ x₀ hfinP := by
  unfold nonnegativeClassDegree positiveClassDegree localDegreeOn
  congr 1
  ext y
  simp only [Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨hzero, hnn⟩
    refine ⟨hzero, ?_⟩
    by_contra hp
    exact hbd y ⟨hnn, hp⟩ hzero
  · rintro ⟨hzero, hp⟩
    exact ⟨hzero, (mem_positiveClassRegion_iff N x₀ y).mp hp |>.nonnegative⟩

/-- **Rate-constant independence on the nonnegative class.**  Combining the positive
region homotopy with the boundary-to-interior bridge.  The extra hypotheses `hbd₀` and
`hbd₁` say that the two endpoint fields are nonzero on the boundary, so that the
nonnegative and positive class degrees coincide at both ends. -/
theorem nonnegativeClassDegree_rate_independent
    (N : Network S) (κ₀ κ₁ : N.RateConstants) (x₀ : Concentration S)
    (hfinN₀ : (N.steadyStateMap κ₀ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite)
    (hfinN₁ : (N.steadyStateMap κ₁ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite)
    (hUcpt : IsCompact (closure (N.positiveClassRegion x₀)))
    (hbd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ closure (N.positiveClassRegion x₀),
      N.steadyStateHomotopy κ₀ κ₁ x₀ (t, y) = 0 → y ∈ N.positiveClassRegion x₀)
    (hreg : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ N.positiveClassRegion x₀,
      N.steadyStateHomotopy κ₀ κ₁ x₀ (t, y) = 0 →
      LinearMap.det
        (partialFDeriv (N.steadyStateHomotopy κ₀ κ₁ x₀) (t, y)).toLinearMap ≠ 0)
    (hfin : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ((fun y => N.steadyStateHomotopy κ₀ κ₁ x₀ (t, y)) ⁻¹' {0} ∩
        N.positiveClassRegion x₀).Finite)
    (hbd₀ : ∀ y ∈ N.classBoundary x₀, N.steadyStateMap κ₀ x₀ y ≠ 0)
    (hbd₁ : ∀ y ∈ N.classBoundary x₀, N.steadyStateMap κ₁ x₀ y ≠ 0) :
    N.nonnegativeClassDegree κ₀ x₀ hfinN₀ =
      N.nonnegativeClassDegree κ₁ x₀ hfinN₁ := by
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have h1mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hfinP₀ : (N.steadyStateMap κ₀ x₀ ⁻¹' {0} ∩ N.positiveClassRegion x₀).Finite := by
    simpa [steadyStateHomotopy] using hfin 0 h0mem
  have hfinP₁ : (N.steadyStateMap κ₁ x₀ ⁻¹' {0} ∩ N.positiveClassRegion x₀).Finite := by
    simpa [steadyStateHomotopy] using hfin 1 h1mem
  rw [N.nonnegativeClassDegree_eq_positiveClassDegree_of_boundary_ne_zero
    κ₀ x₀ hfinN₀ hfinP₀ hbd₀]
  rw [N.nonnegativeClassDegree_eq_positiveClassDegree_of_boundary_ne_zero
    κ₁ x₀ hfinN₁ hfinP₁ hbd₁]
  exact N.positiveClassDegree_rate_independent κ₀ κ₁ x₀ hUcpt hbd hreg hfin

/-- **Positive steady states are independent of the rate constants.**  If the degree for
`κ₀` is nonzero, the rate-constant homotopy preserves it, and the target field is
nonzero on the boundary, then `κ₁` has a positive steady state in the compatibility class
of `x₀`. -/
theorem exists_positiveSteadyState_of_rate_independent_degree
    (N : Network S) (κ₀ κ₁ : N.RateConstants) (x₀ : Concentration S)
    (hfinN₀ : (N.steadyStateMap κ₀ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite)
    (hfinN₁ : (N.steadyStateMap κ₁ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite)
    (hUcpt : IsCompact (closure (N.positiveClassRegion x₀)))
    (hbd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ closure (N.positiveClassRegion x₀),
      N.steadyStateHomotopy κ₀ κ₁ x₀ (t, y) = 0 → y ∈ N.positiveClassRegion x₀)
    (hreg : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ N.positiveClassRegion x₀,
      N.steadyStateHomotopy κ₀ κ₁ x₀ (t, y) = 0 →
      LinearMap.det
        (partialFDeriv (N.steadyStateHomotopy κ₀ κ₁ x₀) (t, y)).toLinearMap ≠ 0)
    (hfin : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ((fun y => N.steadyStateHomotopy κ₀ κ₁ x₀ (t, y)) ⁻¹' {0} ∩
        N.positiveClassRegion x₀).Finite)
    (hbd₀ : ∀ y ∈ N.classBoundary x₀, N.steadyStateMap κ₀ x₀ y ≠ 0)
    (hbd₁ : ∀ y ∈ N.classBoundary x₀, N.steadyStateMap κ₁ x₀ y ≠ 0)
    (hdeg₀ : N.nonnegativeClassDegree κ₀ x₀ hfinN₀ ≠ 0) :
    ∃ x : Concentration S,
      N.StoichCompatible x₀ x ∧ Concentration.Positive x ∧
        N.IsMassActionSteadyState κ₁ x := by
  have hdegEq := N.nonnegativeClassDegree_rate_independent κ₀ κ₁ x₀ hfinN₀ hfinN₁
    hUcpt hbd hreg hfin hbd₀ hbd₁
  exact N.exists_positiveSteadyState_of_nonnegativeClassDegree_ne_zero κ₁ x₀ hfinN₁
    (by rw [← hdegEq]; exact hdeg₀) hbd₁

/-! ## The affine reference map `y ↦ b - y` -/

/-- The determinant of `-id` is a power of `-1`, hence nonzero. -/
theorem det_neg_id_ne_zero (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    LinearMap.det (-(ContinuousLinearMap.id ℝ E)).toLinearMap ≠ 0 := by
  have hcoe : (-(ContinuousLinearMap.id ℝ E)).toLinearMap =
      (-1 : ℝ) • (LinearMap.id : E →ₗ[ℝ] E) := by
    ext x
    simp
  rw [hcoe, LinearMap.det_smul, LinearMap.det_id, mul_one]
  exact pow_ne_zero _ (by norm_num)

/-- The integer coercion of a nonzero sign is nonzero. -/
theorem sign_cast_ne_zero_of_ne_zero {a : ℝ} (ha : a ≠ 0) :
    ((SignType.sign a : SignType) : ℤ) ≠ 0 := by
  rcases lt_trichotomy a 0 with h | h | h
  · rw [sign_neg h]
    decide
  · exact absurd h ha
  · rw [sign_pos h]
    decide

/-- **Degree of the affine map `y ↦ b - y`.**  On any region containing its unique zero
`b`, the relative degree is the orientation sign of `-id`, i.e. `(-1)^s` as a sign.
This supplies the reference-map computation used in the concrete model below. -/
theorem localDegreeOn_sub_const_eq_sign {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (b : E) {U : Set E} (hb : b ∈ U)
    (hfin : ((fun y : E => b - y) ⁻¹' {(0 : E)} ∩ U).Finite) :
    localDegreeOn (fun y : E => b - y) 0 U hfin =
      ((SignType.sign (LinearMap.det
        (-(ContinuousLinearMap.id ℝ E)).toLinearMap) : SignType) : ℤ) := by
  have hpre : (fun y : E => b - y) ⁻¹' {(0 : E)} = {b} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      exact (sub_eq_zero.mp h).symm
    · intro h
      rw [h]
      simp
  have hset : (fun y : E => b - y) ⁻¹' {(0 : E)} ∩ U = {b} := by
    rw [hpre]
    exact Set.inter_eq_self_of_subset_left (Set.singleton_subset_iff.2 hb)
  have htf : hfin.toFinset = {b} := by
    ext z
    rw [Set.Finite.mem_toFinset, hset, Finset.mem_singleton, Set.mem_singleton_iff]
  have hderiv : fderiv ℝ (fun y : E => b - y) b =
      -(ContinuousLinearMap.id ℝ E) := by
    simpa using (fderiv_const_sub (𝕜 := ℝ) (x := b) (c := b) (f := id))
  unfold localDegreeOn
  rw [htf, Finset.sum_singleton, hderiv]

/-- A nonzero relative degree for `y ↦ b - y` on a region containing `b`. -/
theorem localDegreeOn_sub_const_ne_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (b : E) {U : Set E} (hb : b ∈ U)
    (hfin : ((fun y : E => b - y) ⁻¹' {(0 : E)} ∩ U).Finite) :
    localDegreeOn (fun y : E => b - y) 0 U hfin ≠ 0 := by
  rw [localDegreeOn_sub_const_eq_sign b hb hfin]
  exact sign_cast_ne_zero_of_ne_zero (det_neg_id_ne_zero E)

/-! ## A concrete `s = 2` instance: the fully open two-species network -/

namespace DegreeExample

/-- Sources of the four reactions `∅ → A`, `A → ∅`, `∅ → B`, `B → ∅`. -/
def source : Fin 4 → Complex (Fin 2)
  | 0 => ![0, 0]
  | 1 => ![1, 0]
  | 2 => ![0, 0]
  | 3 => ![0, 1]

/-- Targets of the four reactions `∅ → A`, `A → ∅`, `∅ → B`, `B → ∅`. -/
def target : Fin 4 → Complex (Fin 2)
  | 0 => ![1, 0]
  | 1 => ![0, 0]
  | 2 => ![0, 1]
  | 3 => ![0, 0]

/-- The reactions of the fully open two-species network. -/
def rxn (r : Fin 4) : Reaction (Fin 2) := { source := source r, target := target r }

/-- The fully open two-species network: inflow and outflow for both species.  Its
stoichiometric subspace is all of `ℝ²`, so `s = 2`, the smallest dimension in which the
degree argument is not the rank-one intermediate-value argument. -/
def N : Network (Fin 2) where
  R := Fin 4
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := rxn

/-- All four rate constants equal to one. -/
def rates : N.RateConstants where
  k _ := 1
  positive _ := by norm_num

theorem reactionVector_zero : N.reactionVector (0 : Fin 4) = ![1, 0] := by
  funext s
  fin_cases s <;> simp [N, rxn, source, target, Network.reactionVector_apply]

theorem reactionVector_two : N.reactionVector (2 : Fin 4) = ![0, 1] := by
  funext s
  fin_cases s <;> simp [N, rxn, source, target, Network.reactionVector_apply]

/-- The stoichiometric subspace is the whole concentration space. -/
theorem stoichSubspace_eq_top : N.stoichSubspace = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x = x 0 • N.reactionVector (0 : Fin 4) +
      x 1 • N.reactionVector (2 : Fin 4) := by
    funext s
    fin_cases s <;>
      simp [reactionVector_zero, reactionVector_two, Pi.add_apply, smul_eq_mul]
  rw [hx]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (N.reactionVector_mem_stoichSubspace (0 : Fin 4)))
    (Submodule.smul_mem _ _ (N.reactionVector_mem_stoichSubspace (2 : Fin 4)))

/-- The stoichiometric rank is `2`: the instance has `s ≥ 2`. -/
theorem stoichRank_eq : N.stoichRank = 2 := by
  rw [Network.stoichRank, stoichSubspace_eq_top, finrank_top, Module.finrank_fin_fun]

/-- The mass-action field is `x ↦ (1 - x_A, 1 - x_B)`. -/
theorem massActionVectorField_eq (x : Concentration (Fin 2)) :
    N.massActionVectorField rates x = fun s => 1 - x s := by
  funext s
  fin_cases s <;>
    simp [N, rxn, source, target, rates, Network.massActionVectorField_apply,
      Network.massActionRate, Complex.massActionMonomial, Fin.sum_univ_succ,
      Fin.prod_univ_succ] <;>
    ring

/-- The reference point `b = π(1)`, the projection of the all-ones vector to the
stoichiometric coordinates.  In this network `π` is an isomorphism, so `b` is the unique
zero of the reduced field. -/
noncomputable def b : ClassCoord N := N.stoichProj (fun _ : Fin 2 => (1 : ℝ))

theorem one_mem_stoichSubspace : (fun _ : Fin 2 => (1 : ℝ)) ∈ N.stoichSubspace := by
  rw [stoichSubspace_eq_top]
  exact Submodule.mem_top

/-- In the class of the origin, the zero of the reduced field is the all-ones
concentration. -/
theorem affineChart_b_eq_one : N.affineChart 0 b = fun _ : Fin 2 => (1 : ℝ) := by
  simp only [affineChart, b, zero_add]
  rw [N.stoichChart_stoichProj one_mem_stoichSubspace]

theorem affineChart_b_positive : Concentration.Positive (N.affineChart 0 b) := by
  rw [affineChart_b_eq_one]
  intro s
  norm_num

theorem b_mem_nonnegative : b ∈ N.nonnegativeClassRegion 0 :=
  (mem_nonnegativeClassRegion_iff N 0 b).mpr affineChart_b_positive.nonnegative

/-- **The reduced field is the invertible affine map `y ↦ b - y`.** -/
theorem steadyStateMap_eq (y : ClassCoord N) :
    N.steadyStateMap rates 0 y = b - y := by
  simp only [steadyStateMap, reducedField, affineChart, zero_add]
  rw [massActionVectorField_eq]
  change N.stoichProj ((fun _ : Fin 2 => (1 : ℝ)) - N.stoichChart y) = b - y
  rw [map_sub, N.stoichProj_stoichChart]
  rfl

theorem steadyStateMap_preimage_zero :
    N.steadyStateMap rates 0 ⁻¹' {(0 : ClassCoord N)} = {b} := by
  ext y
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  rw [steadyStateMap_eq]
  constructor
  · intro h
    exact (sub_eq_zero.mp h).symm
  · intro h
    rw [h]
    simp

/-- Finiteness of the zero set in the nonnegative class. -/
theorem hfinN :
    (N.steadyStateMap rates 0 ⁻¹' {(0 : ClassCoord N)} ∩
      N.nonnegativeClassRegion 0).Finite :=
  (Set.finite_singleton b).subset fun y hy => by
    rw [steadyStateMap_preimage_zero] at hy
    exact hy.1

/-- The class degree is the sign of `det (-id)`. -/
theorem nonnegativeClassDegree_eq_sign :
    N.nonnegativeClassDegree rates 0 hfinN =
      ((SignType.sign (LinearMap.det
        (-(ContinuousLinearMap.id ℝ (ClassCoord N))).toLinearMap) : SignType) : ℤ) := by
  have hfun : N.steadyStateMap rates 0 = fun y => b - y := funext steadyStateMap_eq
  have hfin' : ((fun y : ClassCoord N => b - y) ⁻¹' {(0 : ClassCoord N)} ∩
      N.nonnegativeClassRegion 0).Finite := by
    rw [← hfun]
    exact hfinN
  have hdegEq : N.nonnegativeClassDegree rates 0 hfinN =
      localDegreeOn (fun y : ClassCoord N => b - y) 0
        (N.nonnegativeClassRegion 0) hfin' := by
    unfold nonnegativeClassDegree
    exact localDegreeOn_congr_fun hfun 0 _ hfinN hfin'
  rw [hdegEq]
  exact localDegreeOn_sub_const_eq_sign b b_mem_nonnegative hfin'

/-- In this two-dimensional instance the determinant of `-id` is `(-1)^2 = 1`. -/
theorem det_neg_id_classCoord :
    LinearMap.det (-(ContinuousLinearMap.id ℝ (ClassCoord N))).toLinearMap = 1 := by
  have hcoe : (-(ContinuousLinearMap.id ℝ (ClassCoord N))).toLinearMap =
      (-1 : ℝ) • (LinearMap.id : ClassCoord N →ₗ[ℝ] ClassCoord N) := by
    ext x
    simp
  rw [hcoe, LinearMap.det_smul, LinearMap.det_id, mul_one]
  have hfr : Module.finrank ℝ (ClassCoord N) = 2 := by
    change Module.finrank ℝ (Fin N.stoichRank → ℝ) = 2
    rw [stoichRank_eq, Module.finrank_fin_fun]
  rw [hfr]
  norm_num

/-- **The class degree is exactly `1`.**  Since `s = 2`, the derivative `-id` at the
unique zero `b` has determinant `(-1)^2 = 1`, so the signed count is `+1`. -/
theorem nonnegativeClassDegree_eq_one :
    N.nonnegativeClassDegree rates 0 hfinN = 1 := by
  rw [nonnegativeClassDegree_eq_sign, det_neg_id_classCoord]
  rw [sign_pos (by norm_num : (0 : ℝ) < 1)]
  rfl

/-- **The class degree is `±1`, hence nonzero.**  The zero is `b`, the derivative there is
`-id`, and its determinant is nonzero in every dimension. -/
theorem nonnegativeClassDegree_ne_zero :
    N.nonnegativeClassDegree rates 0 hfinN ≠ 0 := by
  rw [nonnegativeClassDegree_eq_one]
  norm_num

/-- The reduced field does not vanish on the boundary of the nonnegative class. -/
theorem boundary_ne_zero :
    ∀ y ∈ N.classBoundary 0, N.steadyStateMap rates 0 y ≠ 0 := by
  intro y hy hzero
  rw [steadyStateMap_eq] at hzero
  have hyb : y = b := (sub_eq_zero.mp hzero).symm
  subst hyb
  exact hy.2 affineChart_b_positive

/-- **A positive steady state exists in the two-species network.**  All hypotheses of
`exists_positiveSteadyState_of_nonnegativeClassDegree_ne_zero` are checked: the zero set
is finite, the degree is `±1`, and the field is nonzero on the boundary. -/
theorem exists_positive_steady_state :
    ∃ x : Concentration (Fin 2),
      N.StoichCompatible 0 x ∧ Concentration.Positive x ∧
        N.IsMassActionSteadyState rates x :=
  N.exists_positiveSteadyState_of_nonnegativeClassDegree_ne_zero rates 0 hfinN
    nonnegativeClassDegree_ne_zero boundary_ne_zero

end DegreeExample

/-! ### Boundary sign preservation via a common linear functional -/

/-- **A common strict sign on the boundary is preserved along the rate homotopy.**  If a
continuous linear functional `ℓ` is strictly positive on both endpoint fields on the
boundary `classBoundary`, then every convex combination `(1-t) F_κ₀ + t F_κ₁` is
nonzero there.  This is the algebraic content of "the field points strictly inward along
a common direction, with the same sign for both rate vectors": the positivity cone is
convex, and convex combinations of positive numbers are positive (and cannot cancel). -/
theorem steadyStateHomotopy_ne_zero_on_classBoundary
    (N : Network S) (κ₀ κ₁ : N.RateConstants) (x₀ : Concentration S)
    (ℓ : (ClassCoord N) →L[ℝ] ℝ)
    (hℓ₀ : ∀ y ∈ N.classBoundary x₀,
      0 < ℓ (N.steadyStateMap κ₀ x₀ y))
    (hℓ₁ : ∀ y ∈ N.classBoundary x₀,
      0 < ℓ (N.steadyStateMap κ₁ x₀ y))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) {y : ClassCoord N}
    (hy : y ∈ N.classBoundary x₀) :
    N.steadyStateHomotopy κ₀ κ₁ x₀ (t, y) ≠ 0 := by
  intro hzero
  have hlin : ℓ (N.steadyStateHomotopy κ₀ κ₁ x₀ (t, y)) =
      (1 - t) * ℓ (N.steadyStateMap κ₀ x₀ y) +
        t * ℓ (N.steadyStateMap κ₁ x₀ y) := by
    simp [steadyStateHomotopy, map_add, map_smul, smul_eq_mul]
  rw [hzero, map_zero] at hlin
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have h0pos : 0 < ℓ (N.steadyStateMap κ₀ x₀ y) := hℓ₀ y hy
  have h1pos : 0 < ℓ (N.steadyStateMap κ₁ x₀ y) := hℓ₁ y hy
  have hpos : 0 < (1 - t) * ℓ (N.steadyStateMap κ₀ x₀ y) +
      t * ℓ (N.steadyStateMap κ₁ x₀ y) := by
    rcases eq_or_lt_of_le ht0 with ht00 | ht0pos
    · have ht_eq : t = 0 := ht00.symm
      simp [ht_eq, h0pos]
    · have hterm : 0 < t * ℓ (N.steadyStateMap κ₁ x₀ y) :=
        mul_pos ht0pos h1pos
      have hother : 0 ≤ (1 - t) * ℓ (N.steadyStateMap κ₀ x₀ y) :=
        mul_nonneg (sub_nonneg.mpr ht1) h0pos.le
      linarith
  linarith

/-- The boundary sign hypothesis in the form required by homotopy invariance: a common
strict `ℓ`-sign on the boundary makes the interpolated field avoid zero on the boundary
of the positive class region, hence on its closure. -/
theorem positiveClassRegion_boundary_avoidance_of_linearFunctional
    (N : Network S) (κ₀ κ₁ : N.RateConstants) (x₀ : Concentration S)
    (ℓ : (ClassCoord N) →L[ℝ] ℝ)
    (hℓ₀ : ∀ y ∈ N.classBoundary x₀,
      0 < ℓ (N.steadyStateMap κ₀ x₀ y))
    (hℓ₁ : ∀ y ∈ N.classBoundary x₀,
      0 < ℓ (N.steadyStateMap κ₁ x₀ y))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) {y : ClassCoord N}
    (hy : y ∈ closure (N.positiveClassRegion x₀))
    (hzero : N.steadyStateHomotopy κ₀ κ₁ x₀ (t, y) = 0) :
    y ∈ N.positiveClassRegion x₀ := by
  by_contra hp
  have hnn : y ∈ N.nonnegativeClassRegion x₀ :=
    N.closure_positiveClassRegion_subset_nonnegativeClassRegion x₀ hy
  exact N.steadyStateHomotopy_ne_zero_on_classBoundary κ₀ κ₁ x₀ ℓ hℓ₀ hℓ₁ ht
    ⟨hnn, hp⟩ hzero

/-- **Rate-constant independence from boundary sign preservation.**  This is
`positiveClassDegree_rate_independent` with the abstract boundary-avoidance hypothesis
discharged by the common strict linear functional `ℓ` on the boundary.  It is the exact
form of the structural statement: equal strict boundary signs for `κ₀` and `κ₁` imply
equal class degrees. -/
theorem positiveClassDegree_rate_independent_of_linearFunctional
    (N : Network S) (κ₀ κ₁ : N.RateConstants) (x₀ : Concentration S)
    (ℓ : (ClassCoord N) →L[ℝ] ℝ)
    (hUcpt : IsCompact (closure (N.positiveClassRegion x₀)))
    (hℓ₀ : ∀ y ∈ N.classBoundary x₀,
      0 < ℓ (N.steadyStateMap κ₀ x₀ y))
    (hℓ₁ : ∀ y ∈ N.classBoundary x₀,
      0 < ℓ (N.steadyStateMap κ₁ x₀ y))
    (hreg : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ N.positiveClassRegion x₀,
      N.steadyStateHomotopy κ₀ κ₁ x₀ (t, y) = 0 →
      LinearMap.det
        (partialFDeriv (N.steadyStateHomotopy κ₀ κ₁ x₀) (t, y)).toLinearMap ≠ 0)
    (hfin : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ((fun y => N.steadyStateHomotopy κ₀ κ₁ x₀ (t, y)) ⁻¹' {0} ∩
        N.positiveClassRegion x₀).Finite) :
    N.positiveClassDegree κ₀ x₀
        (by simpa [steadyStateHomotopy] using hfin 0 (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1))
      = N.positiveClassDegree κ₁ x₀
        (by simpa [steadyStateHomotopy] using hfin 1 (by norm_num : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)) :=
  N.positiveClassDegree_rate_independent κ₀ κ₁ x₀ hUcpt
    (fun _t ht _y hy hzero =>
      N.positiveClassRegion_boundary_avoidance_of_linearFunctional κ₀ κ₁ x₀ ℓ
        hℓ₀ hℓ₁ ht hy hzero)
    hreg hfin

end Network

end CRNT
