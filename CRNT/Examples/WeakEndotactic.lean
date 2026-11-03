import CRNT.Geometry.EndotacticStandard
import CRNT.Dynamics.KnownGlobalPersistenceClasses
import CRNT.Dynamics.GlobalPersistence

/-!
# The library's `Endotactic` is weaker than the standard notion

The two-species first-order network `0 ⇌ X₀`, `X₁ → 0` satisfies the library's `Endotactic`
(reactions from sources that are `w`-maximal among all sources never increase `w`) but is not
endotactic in the standard sense (`EndotacticStd`): for `w = −e₁` the reaction `X₁ → 0` increases
`w` and no `w`-decreasing reaction has a larger source value. With unit rates the dynamics are
`x₀' = 1 − x₀`, `x₁' = −x₁`, an explicit global flow, and `x₁(t) = x₁(0) e^{−t} → 0`.

Consequently the frontier propositions `TwoSpeciesEndotacticPermanenceClaim` and
`FirstOrderEndotacticPersistenceClaim`, as first stated with the library's `Endotactic`, are
**false** for this network (`weakTwoSpeciesEndotacticPermanence_false`,
`weakFirstOrderEndotacticPersistence_false`). The claims now use `EndotacticStd`, the notion of
Craciun–Nazarov–Pantea, which this network does not satisfy.
-/

open scoped NNReal Topology
open Filter

namespace CRNT
namespace Examples
namespace WeakEndotactic

open Network

/-- The unit complex of species `i`. -/
def e (i : Fin 2) : Complex (Fin 2) := Pi.single i 1

/-- `0 → X₀`, `X₀ → 0`, `X₁ → 0`. -/
abbrev net : Network (Fin 2) :=
  ⟨Fin 3, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨0, e 0⟩ else if r = 1 then ⟨e 0, 0⟩ else ⟨e 1, 0⟩⟩

theorem wValue_eq (w : Fin 2 → ℝ) (r : net.R) :
    net.wValue w r = if r = 0 then 0 else if r = 1 then w 0 else w 1 := by
  fin_cases r <;>
    simp [Network.wValue, net, e, Network.dotProduct, exponentVector, Fin.sum_univ_two,
      Pi.single_apply]

theorem wRate_eq (w : Fin 2 → ℝ) (r : net.R) :
    net.wRate w r = if r = 0 then w 0 else if r = 1 then -w 0 else -w 1 := by
  fin_cases r <;>
    simp [Network.wRate, net, e, Network.dotProduct, Network.reactionVector, Reaction.vector,
      Fin.sum_univ_two, Pi.single_apply]

/-- The network is endotactic in the library's sense. -/
theorem endotactic : net.Endotactic := by
  intro w r hmax
  have h0 := hmax 0
  have h1 := hmax 1
  have h2 := hmax 2
  simp only [wValue_eq] at h0 h1 h2
  rw [wRate_eq]
  fin_cases r <;> simp at h0 h1 h2 ⊢ <;> linarith

/-- The network is not endotactic in the standard sense. -/
theorem not_endotacticStd : ¬ net.EndotacticStd := by
  intro h
  obtain ⟨r', hneg, hlt⟩ := h ![0, -1] 2 (by rw [wRate_eq]; simp)
  rw [wRate_eq] at hneg
  rw [wValue_eq, wValue_eq] at hlt
  fin_cases r' <;> simp at hneg hlt

/-- Unit rate constants. -/
def κ : RateConstants net := ⟨fun _ => 1, fun _ => one_pos⟩

theorem field_eq (x : Concentration (Fin 2)) :
    net.massActionVectorField κ x = ![1 - x 0, -x 1] := by
  funext s
  rw [massActionVectorField_apply, Fin.sum_univ_three]
  fin_cases s <;>
    simp [massActionRate, κ, net, e, Network.reactionVector, Complex.massActionMonomial,
      Fin.prod_univ_two, Pi.single_apply] <;> ring

/-- The explicit solution. -/
noncomputable def gam (x : Concentration (Fin 2)) (t : ℝ) : Concentration (Fin 2) :=
  ![1 + (x 0 - 1) * Real.exp (-t), x 1 * Real.exp (-t)]

theorem gam_hasDerivAt (x : Concentration (Fin 2)) (t : ℝ) :
    HasDerivAt (gam x) (net.massActionVectorField κ (gam x t)) t := by
  rw [field_eq, hasDerivAt_pi]
  intro i
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-t)) t := by
    convert (hasDerivAt_neg t).exp using 1; ring
  fin_cases i
  · show HasDerivAt (fun t => 1 + (x 0 - 1) * Real.exp (-t)) _ t
    convert (hexp.const_mul (x 0 - 1)).const_add 1 using 1
    simp [gam]
  · show HasDerivAt (fun t => x 1 * Real.exp (-t)) _ t
    convert hexp.const_mul (x 1) using 1
    simp [gam]

/-- The flow. -/
noncomputable def flow : Flow ℝ≥0 (Concentration (Fin 2)) where
  toFun t x := gam x t
  cont' := by
    unfold gam
    refine continuous_pi fun i => ?_
    fin_cases i
    · simp only [Function.uncurry]
      fun_prop
    · simp only [Function.uncurry]
      fun_prop
  map_add' t₁ t₂ x := by
    funext i
    fin_cases i
    · simp [gam, NNReal.coe_add, Real.exp_add]; ring
    · simp [gam, NNReal.coe_add, Real.exp_add]; ring
  map_zero' x := by
    funext i
    fin_cases i <;> simp [gam]

theorem isMassActionFlow : net.IsMassActionFlow κ flow gam := by
  refine ⟨fun x => ?_, fun x t => rfl, fun x t _ => gam_hasDerivAt x t⟩
  funext i
  fin_cases i <;> simp [gam]

/-- The network is not structurally persistent: `x₁(t) → 0`. -/
theorem not_structurallyPersistentStd : ¬ net.StructurallyPersistentStd := by
  intro h
  have hx : Concentration.Positive (fun _ : Fin 2 => (1 : ℝ)) := fun _ => one_pos
  obtain ⟨ε, hε, hle⟩ := h κ flow gam isMassActionFlow _ hx 1
  -- choose `t` with `e^{-t} < ε`
  obtain ⟨t, ht0, ht⟩ : ∃ t : ℝ, 0 ≤ t ∧ Real.exp (-t) < ε := by
    refine ⟨max 0 (-Real.log ε + 1), le_max_left _ _, ?_⟩
    calc Real.exp (-max 0 (-Real.log ε + 1)) ≤ Real.exp (-(-Real.log ε + 1)) :=
          Real.exp_le_exp.mpr (neg_le_neg (le_max_right _ _))
      _ < Real.exp (Real.log ε) := Real.exp_lt_exp.mpr (by linarith)
      _ = ε := Real.exp_log hε
  have := hle ⟨t, ht0⟩
  change ε ≤ gam (fun _ => 1) t 1 at this
  simp [gam] at this
  linarith

theorem isFirstOrder : net.IsFirstOrder := by
  intro c hc
  simp only [Network.complexes, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
    true_and] at hc
  rcases hc with ⟨r, rfl⟩ | ⟨r, rfl⟩ <;> fin_cases r <;>
    simp [e, Pi.single_apply]

/-- **Two-species permanence fails for the library's `Endotactic`** (the earlier form of
`TwoSpeciesEndotacticPermanenceClaim`). -/
theorem weakTwoSpeciesEndotacticPermanence_false :
    ¬ (Fintype.card (Fin 2) = 2 → net.Endotactic → net.StructurallyPermanent) :=
  fun h => not_structurallyPersistentStd (h (by simp) endotactic).toPersistentStd

/-- **First-order persistence fails for the library's `Endotactic`** (the earlier form of
`FirstOrderEndotacticPersistenceClaim`). -/
theorem weakFirstOrderEndotacticPersistence_false :
    ¬ (net.IsFirstOrder → net.Endotactic → net.StructurallyPersistentStd) :=
  fun h => not_structurallyPersistentStd (h isFirstOrder endotactic)

/-- The corrected claims hold vacuously here: the network is not endotactic in the standard
sense. -/
theorem twoSpeciesEndotacticPermanenceClaim : net.TwoSpeciesEndotacticPermanenceClaim :=
  fun _ h => absurd h not_endotacticStd

end WeakEndotactic
end Examples
end CRNT
