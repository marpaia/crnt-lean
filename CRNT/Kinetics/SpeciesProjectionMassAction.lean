import CRNT.Geometry.SpeciesProjection
import CRNT.Kinetics.VariableMassAction
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.ODE.PicardLindelof

/-!
# Mass-action kinetics under species projection

Restricting a full mass-action trajectory to a subset `P` of species produces a variable-k
mass-action trajectory on `speciesProjection N P`.  The omitted coordinates enter only through a
positive multiplicative factor in each source monomial.
-/

open scoped BigOperators

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Restrict a concentration to a species subset. -/
def projectConcentration (P : Finset S) (x : Concentration S) : Concentration {s // s ∈ P} :=
  fun s => x s.1

@[simp] theorem projectConcentration_apply (P : Finset S) (x : Concentration S)
    (s : {s // s ∈ P}) : projectConcentration P x s = x s.1 := rfl

/-- Product of the source-complex monomial over the omitted species. -/
def omittedMonomial (P : Finset S) (x : Concentration S) (y : Complex S) : ℝ :=
  ∏ s ∈ Pᶜ, x s ^ y s

/-- The full monomial factors into the projected monomial and the omitted-species monomial. -/
theorem massActionMonomial_project_mul_omitted (P : Finset S) (x : Concentration S)
    (y : Complex S) :
    (projectComplex P y).massActionMonomial (projectConcentration P x) *
        omittedMonomial P x y = y.massActionMonomial x := by
  rw [Complex.massActionMonomial, Complex.massActionMonomial, omittedMonomial]
  have hsub :
      (∏ s : {s // s ∈ P}, (projectConcentration P x s) ^ (projectComplex P y s)) =
        ∏ s ∈ P, x s ^ y s := by
    rw [Finset.prod_subtype P]
    · rfl
    · intro s
      simp
  rw [hsub]
  exact Finset.prod_mul_prod_compl P (fun s => x s ^ y s)

/-- The positive effective coefficient of reaction `r` after projecting a positive full
trajectory `x`. -/
def projectedVariableRates (N : Network S) (P : Finset S) (κ : N.RateConstants)
    (x : ℝ → Concentration S) (hpos : ∀ t, (x t).Positive) :
    (N.speciesProjection P).VariableRateConstants where
  k := fun t r => κ.k r * omittedMonomial P (x t) (N.reaction r).source
  positive := by
    intro t r
    apply mul_pos (κ.positive r)
    unfold omittedMonomial
    exact Finset.prod_pos fun s hs => pow_pos (hpos t s) _

/-- Exact factorization of a full reaction rate into a projected variable-k reaction rate. -/
theorem projectedVariableMassActionRate_eq (N : Network S) (P : Finset S)
    (κ : N.RateConstants) (x : ℝ → Concentration S) (hpos : ∀ t, (x t).Positive)
    (t : ℝ) (r : N.R) :
    (N.speciesProjection P).variableMassActionRate
        (N.projectedVariableRates P κ x hpos) t r (projectConcentration P (x t)) =
      N.massActionRate κ r (x t) := by
  simp only [variableMassActionRate, massActionRate, projectedVariableRates]
  rw [← massActionMonomial_project_mul_omitted P (x t) (N.reaction r).source]
  simp only [speciesProjection, projectReaction]
  ring

/-- The projected variable-k vector field is exactly the restriction of the full constant-k
mass-action vector field. -/
theorem projectedVariableMassActionVectorField_eq (N : Network S) (P : Finset S)
    (κ : N.RateConstants) (x : ℝ → Concentration S) (hpos : ∀ t, (x t).Positive)
    (t : ℝ) :
    (N.speciesProjection P).variableMassActionVectorField
        (N.projectedVariableRates P κ x hpos) t (projectConcentration P (x t)) =
      projectConcentration P (N.massActionVectorField κ (x t)) := by
  funext s
  rw [variableMassActionVectorField_apply, projectConcentration_apply,
    massActionVectorField_apply]
  apply Finset.sum_congr rfl
  intro r _
  change N.R at r
  rw [N.projectedVariableMassActionRate_eq P κ x hpos t r]
  simp only [speciesProjection_reactionVector_apply]

/-- Restricting a positive mass-action solution to `P` gives a solution of the projected
variable-k mass-action ODE. -/
theorem projectedTrajectory_hasDerivAt (N : Network S) (P : Finset S)
    (κ : N.RateConstants) {x : ℝ → Concentration S} (hpos : ∀ t, (x t).Positive)
    (hsol : ∀ t, HasDerivAt x (N.massActionVectorField κ (x t)) t) (t : ℝ) :
    HasDerivAt (fun τ => projectConcentration P (x τ))
      ((N.speciesProjection P).variableMassActionVectorField
        (N.projectedVariableRates P κ x hpos) t (projectConcentration P (x t))) t := by
  apply hasDerivAt_pi.mpr
  intro s
  have hs := (hasDerivAt_pi.mp (hsol t)) s.1
  rw [N.projectedVariableMassActionVectorField_eq P κ x hpos t]
  simpa [projectConcentration, massActionVectorField_apply, reactionVector_apply] using hs

/-- Lower endpoint obtained by replacing every omitted concentration by a common lower bound. -/
def projectedRateLowerEndpoint (N : Network S) (P : Finset S) (κ : N.RateConstants)
    (m : ℝ) (r : N.R) : ℝ :=
  κ.k r * ∏ s ∈ Pᶜ, m ^ (N.reaction r).source s

/-- Upper endpoint obtained by replacing every omitted concentration by a common upper bound. -/
def projectedRateUpperEndpoint (N : Network S) (P : Finset S) (κ : N.RateConstants)
    (M : ℝ) (r : N.R) : ℝ :=
  κ.k r * ∏ s ∈ Pᶜ, M ^ (N.reaction r).source s

/-- Coordinate bounds give pointwise lower and upper bounds on every effective projected
coefficient. -/
theorem projectedVariableRates_between_endpoints (N : Network S) (P : Finset S)
    (κ : N.RateConstants) {x : ℝ → Concentration S} (hpos : ∀ t, (x t).Positive)
    {m M : ℝ} (hm : 0 ≤ m) (hM : 0 ≤ M)
    (hbounds : ∀ t s, m ≤ x t s ∧ x t s ≤ M) (t : ℝ) (r : N.R) :
    N.projectedRateLowerEndpoint P κ m r ≤
        (N.projectedVariableRates P κ x hpos).k t r ∧
      (N.projectedVariableRates P κ x hpos).k t r ≤
        N.projectedRateUpperEndpoint P κ M r := by
  constructor
  · unfold projectedRateLowerEndpoint projectedVariableRates omittedMonomial
    apply mul_le_mul_of_nonneg_left _ (κ.positive r).le
    refine Finset.prod_le_prod₀ (fun s _ => pow_nonneg hm _) (fun s _ => ?_)
    exact pow_le_pow_left₀ hm (hbounds t s).1 _
  · unfold projectedRateUpperEndpoint projectedVariableRates omittedMonomial
    apply mul_le_mul_of_nonneg_left _ (κ.positive r).le
    refine Finset.prod_le_prod₀
      (fun s _ => pow_nonneg (le_trans hm (hbounds t s).1) _) (fun s _ => ?_)
    exact pow_le_pow_left₀ (le_trans hm (hbounds t s).1) (hbounds t s).2 _

/-- With a strictly positive common lower coordinate bound and a finite common upper coordinate
bound, all effective coefficients of the projected system lie in one compact positive interval
`[δ, δ⁻¹]`, uniformly in time. -/
theorem projectedVariableRates_uniformlyBounded (N : Network S) (P : Finset S)
    (κ : N.RateConstants) {x : ℝ → Concentration S} (hpos : ∀ t, (x t).Positive)
    {m M : ℝ} (hm : 0 < m) (hM : 0 < M)
    (hbounds : ∀ t s, m ≤ x t s ∧ x t s ≤ M) :
    ∃ δ : ℝ, (N.projectedVariableRates P κ x hpos).UniformlyBounded δ := by
  classical
  by_cases hR : Nonempty N.R
  · let lo : N.R → ℝ := fun r => N.projectedRateLowerEndpoint P κ m r
    let hi : N.R → ℝ := fun r => N.projectedRateUpperEndpoint P κ M r
    let lomin : ℝ := Finset.univ.inf' Finset.univ_nonempty lo
    let himax : ℝ := Finset.univ.sup' Finset.univ_nonempty hi
    have hlo_pos : ∀ r, 0 < lo r := by
      intro r
      unfold lo projectedRateLowerEndpoint
      exact mul_pos (κ.positive r) (Finset.prod_pos fun s hs => pow_pos hm _)
    have hlomin : 0 < lomin := by
      -- the infimum over a nonempty finite set is attained
      obtain ⟨r, -, hr⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty) lo
      dsimp only [lomin]
      rw [hr]
      exact hlo_pos r
    have hhi_pos : ∀ r, 0 < hi r := by
      intro r
      unfold hi projectedRateUpperEndpoint
      exact mul_pos (κ.positive r) (Finset.prod_pos fun s hs => pow_pos hM _)
    have hhimax : 0 < himax :=
      (hhi_pos (Classical.choice hR)).trans_le
        (Finset.le_sup' hi (Finset.mem_univ (Classical.choice hR)))
    let δ : ℝ := min lomin (min 1 himax⁻¹)
    have hδ : 0 < δ := by
      dsimp [δ]
      exact lt_min hlomin (lt_min zero_lt_one (inv_pos.mpr hhimax))
    refine ⟨δ, hδ, ?_⟩
    intro t r
    have hend := N.projectedVariableRates_between_endpoints P κ hpos hm.le hM.le hbounds t r
    have hlower : lomin ≤ lo r := Finset.inf'_le _ (Finset.mem_univ r)
    have hupper : hi r ≤ himax := Finset.le_sup' _ (Finset.mem_univ r)
    have hδlo : δ ≤ lomin := min_le_left _ _
    have hδinvhi : δ ≤ himax⁻¹ :=
      (min_le_right lomin _).trans (min_le_right 1 himax⁻¹)
    constructor
    · exact hδlo.trans (hlower.trans hend.1)
    · have hhiδ : himax ≤ δ⁻¹ := (le_inv_comm₀ hhimax hδ).2 hδinvhi
      exact hend.2.trans (hupper.trans hhiδ)
  · haveI hNe : IsEmpty N.R := not_nonempty_iff.mp hR
    refine ⟨1, zero_lt_one, ?_⟩
    intro t r
    -- `(N.speciesProjection P).R` is `N.R` by definition, so `r` is impossible
    exact (hNe.false (show N.R from r)).elim

end Network
end CRNT
