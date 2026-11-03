import CRNT.Equilibria.WegscheiderConverse
import CRNT.Deficiency.CycleExactSequence
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Finite generators for Wegscheider conditions

The basis-free Wegscheider condition requires the log-affinity to annihilate the whole
stoichiometric cycle space `ker S`.  Because reaction space is finite dimensional, it is
enough to check any finite spanning family.  This is the formal version of the usual
finite list of independent Wegscheider identities.

The development deliberately distinguishes:
* real cycle generators, natural for linear algebra;
* integer stoichiometric cycles, natural for multiplicative equilibrium-constant
  product identities.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A finite family that spans the real stoichiometric cycle space. -/
def SpansStoichCycles (N : Network S) (B : Finset (N.R → ℝ)) : Prop :=
  Submodule.span ℝ (B : Set (N.R → ℝ)) = N.stoichCycleSpace

/-- Log affinity evaluated on a reaction-space vector. -/
noncomputable def cycleAffinity (N : Network S) (ρ : ReversiblePairing N)
    (κ : N.RateConstants) (z : N.R → ℝ) : ℝ :=
  ∑ r : N.R, N.logEquilibriumConstant ρ κ r * z r

/-- The affinity functional is linear in the cycle vector. -/
noncomputable def cycleAffinityLinear (N : Network S) (ρ : ReversiblePairing N)
    (κ : N.RateConstants) : (N.R → ℝ) →ₗ[ℝ] ℝ where
  toFun := N.cycleAffinity ρ κ
  map_add' := by
    intro x y
    simp [cycleAffinity, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    simp only [cycleAffinity, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro r _
    ring

/-- A finite spanning family gives a finite Wegscheider certificate. -/
theorem satisfiesWegscheider_iff_generators
    (N : Network S) (ρ : ReversiblePairing N) (κ : N.RateConstants)
    {B : Finset (N.R → ℝ)} (hB : N.SpansStoichCycles B) :
    N.SatisfiesWegscheider ρ κ ↔
      ∀ z ∈ B, N.cycleAffinity ρ κ z = 0 := by
  rw [N.satisfiesWegscheider_iff ρ κ]
  constructor
  · intro h z hz
    apply h z
    have hzspan : z ∈ Submodule.span ℝ (B : Set (N.R → ℝ)) :=
      Submodule.subset_span hz
    rwa [hB] at hzspan
  · intro h z hz
    have hzspan : z ∈ Submodule.span ℝ (B : Set (N.R → ℝ)) := by
      rw [hB]
      exact hz
    have hle : Submodule.span ℝ (B : Set (N.R → ℝ)) ≤
        LinearMap.ker (N.cycleAffinityLinear ρ κ) := by
      apply Submodule.span_le.mpr
      intro y hy
      exact LinearMap.mem_ker.mpr (h y hy)
    exact LinearMap.mem_ker.mp (hle hzspan)

/-- In particular, any basis of `ker S` gives a complete independent set of
Wegscheider equations. -/
theorem satisfiesWegscheider_iff_basis
    (N : Network S) (ρ : ReversiblePairing N) (κ : N.RateConstants)
    (b : Module.Basis (Fin (Module.finrank ℝ N.stoichCycleSpace)) ℝ N.stoichCycleSpace) :
    N.SatisfiesWegscheider ρ κ ↔
      ∀ i, N.cycleAffinity ρ κ (b i : N.R → ℝ) = 0 := by
  rw [N.satisfiesWegscheider_iff ρ κ]
  constructor
  · intro h i
    exact h (b i : N.R → ℝ) (b i).2
  · intro h z hz
    let f : N.stoichCycleSpace →ₗ[ℝ] ℝ :=
      (N.cycleAffinityLinear ρ κ).comp N.stoichCycleSpace.subtype
    have hf : f = 0 := by
      apply LinearMap.ext_on b.span_eq
      intro y hy
      rcases hy with ⟨i, rfl⟩
      exact h i
    let zs : N.stoichCycleSpace := ⟨z, hz⟩
    have hz0 := LinearMap.congr_fun hf zs
    change f zs = 0 at hz0
    change N.cycleAffinity ρ κ z = 0 at hz0
    exact hz0

/-- Integer stoichiometric cycle. -/
def IsIntegerStoichCycle (N : Network S) (z : N.R → ℤ) : Prop :=
  ∀ s : S, ∑ r : N.R, (z r : ℝ) * N.reactionVector r s = 0

/-- Every integer stoichiometric cycle gives a real stoichiometric cycle. -/
theorem real_of_integerStoichCycle (N : Network S) {z : N.R → ℤ}
    (hz : N.IsIntegerStoichCycle z) :
    (fun r => (z r : ℝ)) ∈ N.stoichCycleSpace := by
  rw [stoichCycleSpace, LinearMap.mem_ker]
  funext s
  simpa [stoichMap_apply] using hz s

/-- Multiplicative equilibrium-constant product associated with an integer cycle. -/
noncomputable def wegProduct (N : Network S) (ρ : ReversiblePairing N)
    (κ : N.RateConstants) (z : N.R → ℤ) : ℝ :=
  ∏ r : N.R, (N.equilibriumConstant ρ κ r) ^ (z r)

/-- Wegscheider's logarithmic identity on an integer cycle. -/
theorem integerCycle_log_identity_of_Wegscheider
    (N : Network S) (ρ : ReversiblePairing N) (κ : N.RateConstants)
    {z : N.R → ℤ} (hz : N.IsIntegerStoichCycle z)
    (hW : N.SatisfiesWegscheider ρ κ) :
    ∑ r : N.R, (z r : ℝ) * N.logEquilibriumConstant ρ κ r = 0 := by
  have h := (N.satisfiesWegscheider_iff ρ κ).1 hW
    (fun r => (z r : ℝ)) (N.real_of_integerStoichCycle hz)
  simpa [mul_comm] using h

/-- Classical multiplicative Wegscheider identity. -/
theorem integerCycle_product_eq_one_of_Wegscheider
    (N : Network S) (ρ : ReversiblePairing N) (κ : N.RateConstants)
    {z : N.R → ℤ} (hz : N.IsIntegerStoichCycle z)
    (hW : N.SatisfiesWegscheider ρ κ) :
    N.wegProduct ρ κ z = 1 := by
  have hsum := N.integerCycle_log_identity_of_Wegscheider ρ κ hz hW
  have hpos : 0 < N.wegProduct ρ κ z := by
    apply Finset.prod_pos
    intro r _
    exact zpow_pos (N.equilibriumConstant_pos ρ κ r) (z r)
  have hlogK : ∀ r : N.R,
      Real.log (N.equilibriumConstant ρ κ r) = N.logEquilibriumConstant ρ κ r := by
    intro r
    rw [equilibriumConstant, logEquilibriumConstant,
      Real.log_div (κ.positive r).ne' (κ.positive (ρ.rev r)).ne']
  have hlog : Real.log (N.wegProduct ρ κ z) = 0 := by
    rw [wegProduct, Real.log_prod]
    · simp_rw [Real.log_zpow, hlogK]
      simpa [mul_comm] using hsum
    · intro r _
      exact (zpow_pos (N.equilibriumConstant_pos ρ κ r) (z r)).ne'
  have hexp := congrArg Real.exp hlog
  simpa [Real.exp_log hpos] using hexp

/-- If a finite integer cycle family spans the real stoichiometric cycle space, its
multiplicative identities are sufficient for detailed balance. -/
theorem Wegscheider_of_integer_generators
    (N : Network S) (ρ : ReversiblePairing N) (κ : N.RateConstants)
    (B : Finset (N.R → ℤ))
    (hspan : Submodule.span ℝ
      ((B.image (fun z r => (z r : ℝ)) : Finset (N.R → ℝ)) : Set (N.R → ℝ)) =
        N.stoichCycleSpace)
    (hprod : ∀ z ∈ B, N.wegProduct ρ κ z = 1) :
    N.SatisfiesWegscheider ρ κ := by
  apply (N.satisfiesWegscheider_iff_generators ρ κ hspan).2
  intro y hy
  rw [Finset.mem_image] at hy
  rcases hy with ⟨z, hzB, rfl⟩
  have hp := hprod z hzB
  have hlogK : ∀ r : N.R,
      Real.log (N.equilibriumConstant ρ κ r) = N.logEquilibriumConstant ρ κ r := by
    intro r
    rw [equilibriumConstant, logEquilibriumConstant,
      Real.log_div (κ.positive r).ne' (κ.positive (ρ.rev r)).ne']
  have hlog := congrArg Real.log hp
  rw [wegProduct, Real.log_prod] at hlog
  · simp_rw [Real.log_zpow, hlogK] at hlog
    simpa [cycleAffinity, mul_comm] using hlog
  · intro r _
    exact (zpow_pos (N.equilibriumConstant_pos ρ κ r) (z r)).ne'

end Network
end CRNT
