import CRNT.Stochastic.ACRExtinction
import CRNT.Stochastic.ACRExtinctionExample
import CRNT.Decision.ComputableDeficiency
import Mathlib.Tactic.FinCases

/-!
# The Anderson–Enciso–Johnston theorem on `A + B → 2B`, `B → A`

The network of `CRNT.ACRExample` satisfies every hypothesis of `Network.acrExtinction`:
it is conservative (`x_A + x_B`), has `n = 4` complexes, `ℓ = 2` linkage classes and `s = 1`
(deficiency one), has the positive steady state `(1, 1)` at unit rates, and its non-terminal
complexes `A + B` and `B` satisfy `A + B ≪ B`. The theorem therefore gives: at every recurrent
count, `B` is extinct (`acrExtinction_instance`).
-/

namespace CRNT

namespace ACRExample

open Network

theorem numComplexes_eq : net.numComplexes = 4 := by decide

theorem numLinkageClasses_eq : net.numLinkageClasses = 2 := by
  rw [← net.computeNumLinkageClasses_eq_numLinkageClasses]
  decide

theorem reactionVector_zero : net.reactionVector (0 : Fin 2) = ![-1, 1] := by
  funext s
  fin_cases s <;> norm_num [Network.reactionVector, r0]

theorem reactionVector_one : net.reactionVector (1 : Fin 2) = ![1, -1] := by
  funext s
  fin_cases s <;> norm_num [Network.reactionVector, r1]

theorem stoichRank_eq : net.stoichRank = 1 := by
  have hne : net.reactionVector (0 : Fin 2) ≠ 0 := by
    rw [reactionVector_zero]
    intro h
    have := congrFun h 0
    simp at this
  have hsub : net.stoichSubspace = Submodule.span ℝ {net.reactionVector (0 : Fin 2)} := by
    apply le_antisymm
    · apply Submodule.span_le.2
      rintro x ⟨r, rfl⟩
      fin_cases r
      · exact Submodule.subset_span rfl
      · have : net.reactionVector (1 : Fin 2) = -net.reactionVector (0 : Fin 2) := by
          rw [reactionVector_zero, reactionVector_one]
          funext s; fin_cases s <;> simp
        show net.reactionVector (1 : Fin 2) ∈ _
        rw [this]
        exact Submodule.neg_mem _ (Submodule.subset_span rfl)
    · apply Submodule.span_le.2
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact net.reactionVector_mem_stoichSubspace (0 : Fin 2)
  rw [Network.stoichRank, hsub, finrank_span_singleton hne]

theorem deficiencyOne : net.DeficiencyOne := by
  unfold DeficiencyOne deficiencyInt
  rw [numComplexes_eq, numLinkageClasses_eq, stoichRank_eq]
  norm_num

/-- Nothing is reachable from a complex that is not a source, except itself. -/
theorem reaches_eq_of_not_source {d e : Complex (Fin 2)}
    (hd : ∀ r : net.R, (net.reaction r).source ≠ d) (h : net.Reaches d e) : e = d := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hstep _ _ =>
    obtain ⟨r, hr, -⟩ := hstep
    exact absurd hr (hd r)

theorem not_terminal_AB : ¬ net.IsTerminalSLC ![1, 1] := by
  intro h
  have hsl := h (0 : Fin 2) (by rw [r0]; try exact StronglyLinked.refl _ _)
  rw [r0] at hsl
  have := reaches_eq_of_not_source (by decide) hsl.2
  exact absurd this (by decide)

theorem not_terminal_B : ¬ net.IsTerminalSLC ![0, 1] := by
  intro h
  have hsl := h (1 : Fin 2) (by rw [r1]; try exact StronglyLinked.refl _ _)
  rw [r1] at hsl
  have := reaches_eq_of_not_source (by decide) hsl.2
  exact absurd this (by decide)

theorem mem_AB : (![1, 1] : Complex (Fin 2)) ∈ net.complexes := by
  have := net.source_mem_complexes (0 : Fin 2)
  rwa [r0] at this

theorem mem_B : (![0, 1] : Complex (Fin 2)) ∈ net.complexes := by
  have := net.source_mem_complexes (1 : Fin 2)
  rwa [r1] at this

/-- Unit rate constants. -/
def unitRates : net.RateConstants := ⟨fun _ => 1, fun _ => one_pos⟩

theorem steadyState_one : net.IsMassActionSteadyState unitRates (fun _ => 1) := by
  intro s
  rw [massActionVectorField_apply, sum_R]
  fin_cases s <;>
    norm_num [massActionRate, reactionVector, r0, r1, Complex.massActionMonomial, unitRates]

/-- **Extinction of `B` at every recurrent count**, from the general theorem. -/
theorem acrExtinction_instance {n : Fin 2 → ℕ}
    (hrec : net.IsRecurrentVia (fun _ => True) n) : n 1 = 0 := by
  have h := acrExtinction net (fun _ => 1) (fun _ => one_pos)
    (by
      intro r
      fin_cases r <;> norm_num [Network.reactionVector, r0, r1, Fin.sum_univ_two])
    deficiencyOne unitRates (fun _ => one_pos) steadyState_one
    ⟨_, mem_AB⟩ ⟨_, mem_B⟩ not_terminal_AB not_terminal_B
    (by intro h; have := congrArg Subtype.val h; exact absurd this (by decide))
    (by decide) hrec ⟨_, mem_B⟩ not_terminal_B
  by_contra hn
  apply h
  intro s
  fin_cases s
  · simp
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    omega

end ACRExample

end CRNT
