import CRNT.Theorems.DeficiencyZero.NoPeriodicOrbit
import CRNT.Equilibria.ComplexBalanceStructure

/-!
# No positive periodic orbits in complex-balanced systems (any deficiency)

`eq_of_periodic_solution` excludes non-constant positive periodic orbits for weakly reversible
deficiency-zero networks.  Deficiency zero is used there only to produce a positive
complex-balanced equilibrium.  This module states the result directly for every mass-action
system that has one (Horn–Jackson 1972): `eq_of_periodic_solution_of_complexBalanced`.  The
proof is the same — the relative entropy is antitone and periodic, hence constant, so every
point of the orbit is complex balanced, and complex-balanced points of one positive class
coincide.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **No non-constant positive periodic orbit** in a complex-balanced mass-action system. -/
theorem eq_of_periodic_solution_of_complexBalanced
    (N : Network S) (κ : N.RateConstants) {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    {γ : ℝ → Concentration S} {T : ℝ} (hT : 0 < T)
    (hpos : ∀ t, (γ t).Positive)
    (hsol : ∀ t s, HasDerivAt (fun τ => γ τ s) (N.massActionVectorField κ (γ t) s) t)
    (hper : Function.Periodic γ T) :
    ∀ t, γ t = γ 0 := by
  have hwr : N.WeaklyReversible := N.weaklyReversible_of_positive_complexBalanced κ hxs hcb
  -- The relative entropy along the orbit is antitone (Lyapunov descent) and periodic, hence
  -- constant.
  have hanti : Antitone (fun t => relEntropy xstar (γ t)) :=
    N.relEntropy_antitone_along_solution κ hxs hcb hpos hsol
  have hgper : Function.Periodic (fun t => relEntropy xstar (γ t)) T := by
    intro t
    show relEntropy xstar (γ (t + T)) = relEntropy xstar (γ t)
    rw [hper t]
  have hgconst : ∀ a b, relEntropy xstar (γ a) = relEntropy xstar (γ b) :=
    eq_of_antitone_periodic hT hanti hgper
  -- Whole-vector form of the solution, for the compatibility-class lemma.
  have hsolwv : ∀ τ, HasDerivAt γ (N.massActionVectorField κ (γ τ)) τ :=
    fun τ => hasDerivAt_pi.mpr (fun s => hsol τ s)
  -- Every point of the orbit is complex-balanced: the relative entropy is locally constant, so
  -- its derivative (the dissipation) vanishes, and vanishing dissipation is complex balance.
  have hcbt : ∀ t, N.IsComplexBalanced κ (γ t) := by
    intro t₀
    have hchain := relEntropy_hasDerivAt hxs (hpos t₀) (fun s => hsol t₀ s)
    have hd0 : HasDerivAt (fun τ => relEntropy xstar (γ τ)) 0 t₀ := by
      have heq : (fun τ => relEntropy xstar (γ τ)) = fun _ => relEntropy xstar (γ t₀) := by
        funext u; exact hgconst u t₀
      rw [heq]; exact hasDerivAt_const t₀ _
    have hdiss : (∑ s, (Real.log (γ t₀ s) - Real.log (xstar s))
        * N.massActionVectorField κ (γ t₀) s) = 0 := hchain.unique hd0
    exact N.complexBalanced_of_dissipation_eq_zero κ (hpos t₀) hxs hcb hdiss
  -- Every point of the orbit lies in γ 0's positive compatibility class.
  have hmem : ∀ t, γ t ∈ N.positiveCompatibilityClass (γ 0) := by
    intro t
    refine ⟨?_, hpos t⟩
    show γ t - γ 0 ∈ N.stoichSubspace
    rcases le_total 0 t with h | h
    · have hsol0t : ∀ τ ∈ Set.Icc (0 : ℝ) t,
          HasDerivAt γ (N.massActionVectorField κ (γ τ)) τ := fun τ _ => hsolwv τ
      exact N.sub_mem_stoichSubspace_of_solution κ h hsol0t
    · have hsolt0 : ∀ τ ∈ Set.Icc t (0 : ℝ),
          HasDerivAt γ (N.massActionVectorField κ (γ τ)) τ := fun τ _ => hsolwv τ
      have h2 := N.sub_mem_stoichSubspace_of_solution κ h hsolt0
      simpa [neg_sub] using N.stoichSubspace.neg_mem h2
  -- Two complex-balanced points of one positive class are equal (deficiency-zero uniqueness).
  intro t
  exact N.isComplexBalanced_unique_in_positiveClass hwr κ (hmem t) (hmem 0) (hcbt t) (hcbt 0)

end Network
end CRNT
