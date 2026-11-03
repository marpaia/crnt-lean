import CRNT.Equilibria.WegscheiderGenerators
import CRNT.Equilibria.Wegscheider
import Mathlib.Data.Int.Basic
import CRNT.Decision.ExactDeficiency
import CRNT.LinearAlgebra.RationalDenominator
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

/-!
# Integer Wegscheider cycles

Because CRN stoichiometric vectors are integral, classical Wegscheider identities may
be written multiplicatively over integer stoichiometric cycles.  This module connects
those product identities to the basis-free real log-affinity formulation.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

-- `IsIntegerStoichCycle` is declared in `Equilibria.WegscheiderGenerators`, which this module
-- imports; the local copy here was a second, ℤ-valued definition of the same predicate and
-- made the file fail to elaborate.  The imported ℝ-valued one is the one the rest of the
-- Wegscheider development is stated against, so it is the one kept.

/-- Cast an integer stoichiometric cycle to a real cycle. -/
theorem integerStoichCycle_cast_mem_ker (N : Network S) {z : N.R → ℤ}
    (hz : N.IsIntegerStoichCycle z) :
    (fun r => (z r : ℝ)) ∈ LinearMap.ker N.stoichMap :=
  N.real_of_integerStoichCycle hz

/-- Multiplicative Wegscheider identity for one integer cycle. Negative exponents are
interpreted using powers in the multiplicative group `ℝˣ` conceptually; the equality is
stated by splitting positive and negative parts to remain in positive reals. -/
def SatisfiesIntegerCycleIdentity (N : Network S) (ρ : N.ReversiblePairing)
    (κ : N.RateConstants) (z : N.R → ℤ) : Prop :=
  ∑ r : N.R, (z r : ℝ) * N.logEquilibriumConstant ρ κ r = 0

/-- The logarithmic and multiplicative integer-cycle forms agree for positive rates. -/
theorem integerCycleIdentity_iff_logIdentity (N : Network S)
    (ρ : N.ReversiblePairing) (κ : N.RateConstants) (z : N.R → ℤ) :
    N.SatisfiesIntegerCycleIdentity ρ κ z ↔
      ∑ r : N.R, (z r : ℝ) * N.logEquilibriumConstant ρ κ r = 0 :=
  Iff.rfl

/-- Basis-free Wegscheider implies every integer-cycle identity. -/
theorem integerCycleIdentity_of_Wegscheider (N : Network S)
    (ρ : N.ReversiblePairing) (κ : N.RateConstants)
    (hW : N.SatisfiesWegscheider ρ κ) {z : N.R → ℤ}
    (hz : N.IsIntegerStoichCycle z) :
    N.SatisfiesIntegerCycleIdentity ρ κ z := by
  rw [N.satisfiesWegscheider_iff ρ κ] at hW
  -- the imported Wegscheider form has the factors in the opposite order
  simpa [SatisfiesIntegerCycleIdentity, mul_comm] using
    hW _ (N.integerStoichCycle_cast_mem_ker hz)


/-- Rational stoichiometric map, whose matrix is the exact rational stoichiometric matrix. -/
noncomputable def stoichMapQ (N : Network S) : (N.R → ℚ) →ₗ[ℚ] (S → ℚ) :=
  N.stoichMatrixQ.mulVecLin

/-- Coordinatewise cast of reaction-space vectors from `ℚ` to `ℝ`. -/
noncomputable def castReactionLM (N : Network S) : (N.R → ℚ) →ₗ[ℚ] (N.R → ℝ) where
  toFun q := fun r => (q r : ℝ)
  map_add' := by intro a b; funext r; simp
  map_smul' := by intro c a; funext r; simp [Rat.smul_def]

lemma castReactionLM_injective (N : Network S) : Function.Injective N.castReactionLM := by
  intro a b h
  funext r
  have hr := congrFun h r
  change ((a r : ℚ) : ℝ) = ((b r : ℚ) : ℝ) at hr
  exact Rat.cast_injective hr

/-- Rational stoichiometric multiplication commutes with coordinatewise cast. -/
lemma cast_stoichMapQ (N : Network S) (q : N.R → ℚ) :
    castSpeciesLM S (N.stoichMapQ q) = N.stoichMap (N.castReactionLM q) := by
  funext s
  rw [N.stoichMap_apply]
  change ((∑ r : N.R, N.stoichMatrixQ s r * q r : ℚ) : ℝ) =
    ∑ r : N.R, (q r : ℝ) * N.reactionVector r s
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp [stoichMatrixQ, reactionVector_apply]
  ring

lemma castReaction_mem_realKer (N : Network S) {q : N.R → ℚ}
    (hq : q ∈ LinearMap.ker N.stoichMapQ) :
    N.castReactionLM q ∈ LinearMap.ker N.stoichMap := by
  rw [LinearMap.mem_ker] at hq ⊢
  have hcast := congrArg (castSpeciesLM S) hq
  rw [map_zero, N.cast_stoichMapQ q] at hcast
  exact hcast

/-- The rational and real stoichiometric kernels have the same dimension. -/
lemma finrank_ker_stoichMapQ_eq (N : Network S) :
    Module.finrank ℚ (LinearMap.ker N.stoichMapQ) =
      Module.finrank ℝ (LinearMap.ker N.stoichMap) := by
  have hQ := LinearMap.finrank_range_add_finrank_ker N.stoichMapQ
  have hR := LinearMap.finrank_range_add_finrank_ker N.stoichMap
  have hrankQ : Module.finrank ℚ (LinearMap.range N.stoichMapQ) = N.stoichRank := by
    change N.stoichMatrixQ.rank = N.stoichRank
    apply Nat.le_antisymm
    · exact N.rank_le_stoichRank
    · rw [N.stoichRank_eq_rank_map]
      exact N.rank_map_le_rank
  have hrankR : Module.finrank ℝ (LinearMap.range N.stoichMap) = N.stoichRank :=
    N.stoichRank_eq_finrank_range.symm
  rw [hrankQ] at hQ
  rw [hrankR] at hR
  have hdimQ : Module.finrank ℚ (N.R → ℚ) = Fintype.card N.R := by simp
  have hdimR : Module.finrank ℝ (N.R → ℝ) = Fintype.card N.R := by simp
  rw [hdimQ] at hQ
  rw [hdimR] at hR
  omega

noncomputable def rationalCycleBasis (N : Network S) :
    Module.Basis (Fin (Module.finrank ℚ (LinearMap.ker N.stoichMapQ))) ℚ
      (LinearMap.ker N.stoichMapQ) := Module.finBasis ℚ _

noncomputable def rationalCycleBasisR (N : Network S)
    (i : Fin (Module.finrank ℚ (LinearMap.ker N.stoichMapQ))) : N.R → ℝ :=
  N.castReactionLM ((N.rationalCycleBasis i : LinearMap.ker N.stoichMapQ).1)

lemma rationalCycleBasisR_mem (N : Network S) (i) :
    N.rationalCycleBasisR i ∈ LinearMap.ker N.stoichMap :=
  N.castReaction_mem_realKer (N.rationalCycleBasis i).2

lemma rationalCycleBasisR_linearIndependent (N : Network S) :
    LinearIndependent ℝ N.rationalCycleBasisR := by
  let b := N.rationalCycleBasis
  have hQsub : LinearIndependent ℚ
      (fun i => ((b i : LinearMap.ker N.stoichMapQ).1 : N.R → ℚ)) := by
    exact b.linearIndependent.map' (LinearMap.ker N.stoichMapQ).subtype (by simp)
  have hcast : LinearIndependent ℝ
      (fun i => (algebraMap ℚ ℝ) ∘ ((b i : LinearMap.ker N.stoichMapQ).1 : N.R → ℚ)) :=
    (linearIndependent_algebraMap_comp_iff (R := ℚ) (S := ℝ)).2 hQsub
  change LinearIndependent ℝ
    (fun i r => ((((b i : LinearMap.ker N.stoichMapQ).1 r : ℚ) : ℝ)))
  convert hcast using 1 <;> ext i r <;> simp

lemma span_rationalCycleBasisR_eq_ker (N : Network S) :
    Submodule.span ℝ (Set.range N.rationalCycleBasisR) = LinearMap.ker N.stoichMap := by
  have hle : Submodule.span ℝ (Set.range N.rationalCycleBasisR) ≤
      LinearMap.ker N.stoichMap := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact N.rationalCycleBasisR_mem i
  apply Submodule.eq_of_le_of_finrank_le hle
  have hdimSpan : Module.finrank ℝ (Submodule.span ℝ (Set.range N.rationalCycleBasisR)) =
      Fintype.card (Fin (Module.finrank ℚ (LinearMap.ker N.stoichMapQ))) := by
    rw [finrank_span_eq_card N.rationalCycleBasisR_linearIndependent]
  rw [Fintype.card_fin] at hdimSpan
  rw [hdimSpan, N.finrank_ker_stoichMapQ_eq]

lemma clearRationalToInt_isCycle (N : Network S) {q : N.R → ℚ}
    (hq : q ∈ LinearMap.ker N.stoichMapQ) :
    N.IsIntegerStoichCycle (clearRationalToInt q) := by
  intro s
  have hqR : ∑ r : N.R, (q r : ℝ) * N.reactionVector r s = 0 := by
    have hm := N.castReaction_mem_realKer hq
    rw [LinearMap.mem_ker] at hm
    have hs := congrFun hm s
    simpa [N.stoichMap_apply, castReactionLM] using hs
  let D : ℝ := (rationalCommonDenominator q : ℕ)
  calc
    ∑ r : N.R, ((clearRationalToInt q r : ℤ) : ℝ) * N.reactionVector r s
        = ∑ r : N.R, (D * (q r : ℝ)) * N.reactionVector r s := by
            apply Finset.sum_congr rfl
            intro r _
            have h := cast_clearRationalToInt q r
            have hr0 := congrArg (fun x : ℚ => (x : ℝ)) h
            have hr : ((clearRationalToInt q r : ℤ) : ℝ) =
                ((rationalCommonDenominator q : ℕ) : ℝ) * (q r : ℝ) := by
              simpa using hr0
            simpa [D] using congrArg (fun a : ℝ => a * N.reactionVector r s) hr
    _ = D * (∑ r : N.R, (q r : ℝ) * N.reactionVector r s) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          ring
    _ = 0 := by rw [hqR, mul_zero]

lemma cast_rational_mem_span_integer_cycles (N : Network S) {q : N.R → ℚ}
    (hq : q ∈ LinearMap.ker N.stoichMapQ) :
    N.castReactionLM q ∈ Submodule.span ℝ
      {v : N.R → ℝ | ∃ z : N.R → ℤ,
        N.IsIntegerStoichCycle z ∧ v = fun r => (z r : ℝ)} := by
  let z : N.R → ℤ := clearRationalToInt q
  have hz : N.IsIntegerStoichCycle z := N.clearRationalToInt_isCycle hq
  let zR : N.R → ℝ := fun r => (z r : ℝ)
  have hzmem : zR ∈ Submodule.span ℝ
      {v : N.R → ℝ | ∃ z : N.R → ℤ,
        N.IsIntegerStoichCycle z ∧ v = fun r => (z r : ℝ)} := by
    apply Submodule.subset_span
    exact ⟨z, hz, rfl⟩
  let D : ℝ := (rationalCommonDenominator q : ℕ)
  have hD : D ≠ 0 := by
    dsimp [D]
    exact_mod_cast (Nat.ne_of_gt (rationalCommonDenominator_pos q))
  have heq : N.castReactionLM q = D⁻¹ • zR := by
    funext r
    have h := cast_clearRationalToInt q r
    have hr0 := congrArg (fun x : ℚ => (x : ℝ)) h
    have hr : (z r : ℝ) = D * (q r : ℝ) := by
      dsimp [z, D]
      simpa using hr0
    simp only [castReactionLM, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul]
    dsimp [zR]
    rw [hr]
    field_simp
  rw [heq]
  exact Submodule.smul_mem _ _ hzmem

/-- Integer stoichiometric cycles span the real stoichiometric cycle space for a CRN
with integral stoichiometry. -/
theorem real_cycle_spanned_by_integer_cycles (N : Network S) :
    Submodule.span ℝ
      {v : N.R → ℝ | ∃ z : N.R → ℤ,
        N.IsIntegerStoichCycle z ∧ v = fun r => (z r : ℝ)} =
      LinearMap.ker N.stoichMap := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro v ⟨z, hz, rfl⟩
    exact N.integerStoichCycle_cast_mem_ker hz
  · rw [← N.span_rationalCycleBasisR_eq_ker]
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact N.cast_rational_mem_span_integer_cycles (N.rationalCycleBasis i).2

/-- It therefore suffices to check Wegscheider identities on all integer cycles. -/
theorem satisfiesWegscheider_iff_integerCycles (N : Network S)
    (ρ : N.ReversiblePairing) (κ : N.RateConstants) :
    N.SatisfiesWegscheider ρ κ ↔
      ∀ z : N.R → ℤ, N.IsIntegerStoichCycle z →
        N.SatisfiesIntegerCycleIdentity ρ κ z := by
  rw [N.satisfiesWegscheider_iff ρ κ]
  constructor
  · intro hW z hz
    simpa [SatisfiesIntegerCycleIdentity, mul_comm] using
      hW _ (N.integerStoichCycle_cast_mem_ker hz)
  · intro h v hv
    -- the log-affinity functional is linear and kills every integer cycle, hence kills
    -- their span, which is the whole real cycle space
    rw [← N.real_cycle_spanned_by_integer_cycles] at hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨z, hz, rfl⟩ := hx
        simpa [SatisfiesIntegerCycleIdentity, mul_comm] using h z hz
    | zero => simp
    | add x y _ _ hx hy =>
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hx, hy, add_zero]
    | smul a x _ hx =>
        simp only [Pi.smul_apply, smul_eq_mul, mul_comm a, ← mul_assoc,
          ← Finset.sum_mul, hx, zero_mul]

end Network
end CRNT
