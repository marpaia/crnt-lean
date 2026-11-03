import CRNT.Theorems.DeficiencyZero.Existence
import CRNT.Equilibria.QuasiThermostatic
import CRNT.Open.Boundary
import CRNT.Open.Deficiency

/-!
# The deficiency zero theorem for fully open systems (CFSTR form)

For a continuous-flow stirred-tank reactor every species has an inflow `0 → s` and an outflow
`s → 0`; this is `CRNT.Network.fullyOpen`. Its stoichiometric subspace is all of `ℝ^S`, so the
whole positive orthant is a single compatibility class. The deficiency zero theorem therefore
takes its open-system form (Feinberg, *Foundations of Chemical Reaction Network Theory*, 2019,
the CFSTR chapter): if the open network is weakly reversible with deficiency zero
`δ⁺ = n⁺ − ℓ⁺ − |S| = 0`, then for **every** choice of rate constants the reactor has **exactly
one** steady state in the closed nonnegative orthant; it is positive and complex balanced.

Main results:
* `CRNT.Network.fullyOpen_positiveCompatibilityClass_eq`: one positive class.
* `CRNT.Network.openDeficiencyZero_existsUnique_positive`: exactly one positive steady state,
  and it is complex balanced.
* `CRNT.Network.openDeficiencyZero_existsUnique_nonneg`: exactly one nonnegative steady state.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The fully open extension has a single positive compatibility class: the orthant. -/
theorem fullyOpen_positiveCompatibilityClass_eq (N : Network S) (x₀ : Concentration S) :
    N.fullyOpen.positiveCompatibilityClass x₀ = {x | x.Positive} := by
  ext x
  simp only [positiveCompatibilityClass, StoichCompatible, Set.mem_ofPred_eq,
    stoichSubspace_fullyOpen_eq_top, Submodule.mem_top, true_and]

/-- **Deficiency zero theorem, open form.** A weakly reversible fully open network of
deficiency zero has, for every choice of rate constants, exactly one positive steady state,
and that steady state is complex balanced. -/
theorem openDeficiencyZero_existsUnique_positive (N : Network S)
    (hwr : N.fullyOpen.WeaklyReversible) (hδ : N.fullyOpen.DeficiencyZero)
    (κ : RateConstants N.fullyOpen) :
    ∃! x : Concentration S, x.Positive ∧ N.fullyOpen.IsMassActionSteadyState κ x := by
  have hone : Concentration.Positive (fun _ : S => (1 : ℝ)) := fun _ => one_pos
  obtain ⟨x, ⟨hxmem, hxcb⟩, huniq⟩ :=
    N.fullyOpen.deficiencyZeroTheorem ⟨hwr, hδ⟩ κ (fun _ => 1) hone
  rw [fullyOpen_positiveCompatibilityClass_eq] at hxmem
  refine ⟨x, ⟨hxmem, N.fullyOpen.isMassActionSteadyState_of_complexBalanced κ hxcb⟩, ?_⟩
  rintro y ⟨hy, hys⟩
  refine huniq y ⟨by rw [fullyOpen_positiveCompatibilityClass_eq]; exact hy, ?_⟩
  exact (N.fullyOpen.positiveSteadyState_iff_complexBalanced κ hxmem hxcb hy).mp hys

/-- The unique positive steady state of the open deficiency-zero reactor is complex
balanced. -/
theorem openDeficiencyZero_positiveSteadyState_complexBalanced (N : Network S)
    (hwr : N.fullyOpen.WeaklyReversible) (hδ : N.fullyOpen.DeficiencyZero)
    (κ : RateConstants N.fullyOpen) {x : Concentration S} (hx : x.Positive)
    (hxs : N.fullyOpen.IsMassActionSteadyState κ x) : N.fullyOpen.IsComplexBalanced κ x := by
  obtain ⟨z, ⟨hzmem, hzcb⟩, _⟩ :=
    N.fullyOpen.deficiencyZeroTheorem ⟨hwr, hδ⟩ κ (fun _ => 1) (fun _ => one_pos)
  rw [fullyOpen_positiveCompatibilityClass_eq] at hzmem
  exact (N.fullyOpen.positiveSteadyState_iff_complexBalanced κ hzmem hzcb hx).mp hxs

/-- **No boundary equilibria; uniqueness in the closed orthant.** For a weakly reversible
deficiency-zero CFSTR there is exactly one nonnegative steady state for every choice of rate
constants. -/
theorem openDeficiencyZero_existsUnique_nonneg (N : Network S)
    (hwr : N.fullyOpen.WeaklyReversible) (hδ : N.fullyOpen.DeficiencyZero)
    (κ : RateConstants N.fullyOpen) :
    ∃! x : Concentration S, x.Nonnegative ∧ N.fullyOpen.IsMassActionSteadyState κ x := by
  obtain ⟨x, ⟨hx, hxs⟩, huniq⟩ := N.openDeficiencyZero_existsUnique_positive hwr hδ κ
  refine ⟨x, ⟨hx.nonnegative, hxs⟩, ?_⟩
  rintro y ⟨hy, hys⟩
  exact huniq y ⟨fullyOpen_steadyState_positive N κ hy hys, hys⟩

end Network

end CRNT
