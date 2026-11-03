import CRNT.Theorems.DeficiencyZero.GeneralKinetics
import CRNT.Kinetics.General
import CRNT.Deficiency.SteadyStateKernel

/-!
# Complex balancing in general kinetic systems

Feinberg ("Complex balancing in general kinetic systems", Arch. Rational Mech. Anal. 49, 1972)
showed that at deficiency zero every steady state of every kinetics is complex balanced: the rate
vector of a steady state lies in `ker (Y ∂)`, which at deficiency zero equals `ker ∂`. The
converse holds for weakly reversible networks already within mass action: a positive
deficiency produces rate constants with a positive steady state that is not complex balanced.

* `rateComplexBalanced_of_stoich_eq_zero_of_deficiencyZero`: at deficiency zero, any reaction-rate
  vector `ρ` with `∑ ρ_r (y'_r − y_r) = 0` balances every complex (no positivity needed).
* `Kinetics.isComplexBalancedAt_of_steadyState_of_deficiencyZero`: Feinberg's theorem for every
  admissible kinetics.
* `deficiencyZero_of_forall_positive_steadyState_complexBalanced`: for a weakly reversible network,
  if every positive mass-action steady state for every choice of rate constants is complex
  balanced, the deficiency is zero.
* `deficiencyZero_iff_forall_positive_steadyState_complexBalanced` and
  `deficiencyZero_iff_forall_kinetics_steadyState_complexBalanced`: the two characterizations
  for weakly reversible networks.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A reaction-rate vector `ρ` **balances every complex**: inflow equals outflow, `∂ ρ = 0`. -/
def IsRateComplexBalanced (N : Network S) (ρ : N.R → ℝ) : Prop := N.incidenceMap ρ = 0

/-- **Deficiency zero: every steady-state rate vector balances the complexes.** -/
theorem rateComplexBalanced_of_stoich_eq_zero_of_deficiencyZero (N : Network S)
    (hδ : N.DeficiencyZero) {ρ : N.R → ℝ} (hρ : N.stoichMap ρ = 0) :
    N.IsRateComplexBalanced ρ :=
  (N.deficiencyZero_iff_stoichCycle_is_graphCycle.mp hδ) ρ hρ

/-- A kinetics is complex balanced at `x` when its rate vector at `x` balances every complex. -/
def Kinetics.IsComplexBalancedAt {N : Network S} (K : Kinetics N) (x : Concentration S) : Prop :=
  N.IsRateComplexBalanced fun r => K.rate r x

theorem Kinetics.stoichMap_rate {N : Network S} (K : Kinetics N) (x : Concentration S) :
    N.stoichMap (fun r => K.rate r x) = K.vectorField x := by
  funext s
  rw [stoichMap_apply, Kinetics.vectorField_apply]

/-- **Feinberg 1972.** At deficiency zero, every steady state of every kinetics is complex
balanced. -/
theorem Kinetics.isComplexBalancedAt_of_steadyState_of_deficiencyZero {N : Network S}
    (hδ : N.DeficiencyZero) (K : Kinetics N) {x : Concentration S}
    (hx : K.vectorField x = 0) : K.IsComplexBalancedAt x :=
  N.rateComplexBalanced_of_stoich_eq_zero_of_deficiencyZero hδ (by rw [K.stoichMap_rate, hx])

/-- For mass action, complex balance of a kinetics at `x` is the usual complex balance. -/
theorem massActionKinetics_isComplexBalancedAt_iff (N : Network S) (κ : RateConstants N)
    (x : Concentration S) :
    (N.massActionKinetics κ).IsComplexBalancedAt x ↔ N.IsComplexBalanced κ x := by
  rw [isComplexBalanced_iff_kineticMap, kineticMap_eq_incidenceMap]
  rfl

/-- **Converse for weakly reversible networks.** If every positive steady state of every
mass-action system on a weakly reversible network is complex balanced, the deficiency is zero.
A vector `v` with `∑ v_r (y'_r − y_r) = 0` and `∂ v ≠ 0` plus a large positive circulation is a
positive rate vector; taking it as rate constants makes the all-ones state a positive steady
state that is not complex balanced. -/
theorem deficiencyZero_of_forall_positive_steadyState_complexBalanced (N : Network S)
    (hwr : N.WeaklyReversible)
    (h : ∀ (κ : RateConstants N) (x : Concentration S), x.Positive →
      N.IsMassActionSteadyState κ x → N.IsComplexBalanced κ x) :
    N.DeficiencyZero := by
  rw [deficiencyZero_iff_stoichCycle_is_graphCycle]
  intro v hv
  obtain ⟨α, hαpos, hαinc⟩ := N.exists_positiveGraphCirculation_of_weaklyReversible hwr
  have hαst : N.stoichMap α = 0 := by
    rw [← complexMap_comp_incidenceMap, LinearMap.comp_apply, hαinc, map_zero]
  -- a large multiple of the circulation makes `v` positive
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ r, 0 < v r + M * α r := by
    refine ⟨∑ r, |v r| / α r + 1, fun r => ?_⟩
    have hle : |v r| / α r ≤ ∑ r', |v r'| / α r' :=
      Finset.single_le_sum (f := fun r' => |v r'| / α r')
        (fun r' _ => div_nonneg (abs_nonneg _) (hαpos r').le) (Finset.mem_univ r)
    have h1 : |v r| = |v r| / α r * α r := by field_simp [(hαpos r).ne']
    have h2 : (|v r| / α r + 1) * α r ≤ (∑ r', |v r'| / α r' + 1) * α r :=
      mul_le_mul_of_nonneg_right (by linarith) (hαpos r).le
    nlinarith [neg_abs_le (v r), hαpos r]
  set ρ : N.R → ℝ := fun r => v r + M * α r with hρ
  let κ : RateConstants N := ⟨ρ, hM⟩
  set one : Concentration S := fun _ => 1 with hone
  have hone_pos : one.Positive := fun _ => one_pos
  have hmono : ∀ c : Complex S, c.massActionMonomial one = 1 := fun c => by
    simp [Complex.massActionMonomial, hone]
  have hρst : N.stoichMap ρ = 0 := by
    have : ρ = v + M • α := by funext r; simp [hρ]
    rw [this, map_add, map_smul, hv, hαst, smul_zero, add_zero]
  have hss : N.IsMassActionSteadyState κ one := by
    intro s
    have := congrFun hρst s
    rw [stoichMap_apply, Pi.zero_apply] at this
    rw [massActionVectorField_apply, ← this]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp [massActionRate, hmono, κ]
  have hcb := h κ one hone_pos hss
  rw [← massActionKinetics_isComplexBalancedAt_iff] at hcb
  have hρinc : N.incidenceMap ρ = 0 := by
    have : (fun r => (N.massActionKinetics κ).rate r one) = ρ := by
      funext r
      show N.massActionRate κ r one = ρ r
      simp [massActionRate, hmono, κ]
    unfold Kinetics.IsComplexBalancedAt IsRateComplexBalanced at hcb
    rwa [this] at hcb
  have : v = ρ - M • α := by funext r; simp [hρ]
  rw [this, map_sub, map_smul, hρinc, hαinc, smul_zero, sub_zero]

/-- **Characterization for weakly reversible networks (mass action).** A weakly reversible
network has deficiency zero iff every positive steady state of every mass-action system on it is
complex balanced. -/
theorem deficiencyZero_iff_forall_positive_steadyState_complexBalanced (N : Network S)
    (hwr : N.WeaklyReversible) :
    N.DeficiencyZero ↔ ∀ (κ : RateConstants N) (x : Concentration S), x.Positive →
      N.IsMassActionSteadyState κ x → N.IsComplexBalanced κ x :=
  ⟨fun hδ κ _ _ hx => N.isComplexBalanced_of_steadyState_of_deficiencyZero hδ κ hx,
    N.deficiencyZero_of_forall_positive_steadyState_complexBalanced hwr⟩

/-- **Characterization for weakly reversible networks (general kinetics).** A weakly reversible
network has deficiency zero iff every steady state of every admissible kinetics on it is complex
balanced. -/
theorem deficiencyZero_iff_forall_kinetics_steadyState_complexBalanced (N : Network S)
    (hwr : N.WeaklyReversible) :
    N.DeficiencyZero ↔ ∀ (K : Kinetics N) (x : Concentration S), K.vectorField x = 0 →
      K.IsComplexBalancedAt x := by
  refine ⟨fun hδ K _ hx => Kinetics.isComplexBalancedAt_of_steadyState_of_deficiencyZero hδ K hx,
    fun h => N.deficiencyZero_of_forall_positive_steadyState_complexBalanced hwr
      fun κ x _ hss => ?_⟩
  rw [← massActionKinetics_isComplexBalancedAt_iff]
  apply h
  funext s
  exact hss s

end Network

end CRNT
