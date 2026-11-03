import CRNT.Theorems.DeficiencyOne.WeaklyReversibleExistence

/-! Special cases preserved from the parallel weakly-reversible existence continuation. -/
namespace CRNT
namespace Network
variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Existence whenever the system is complex balanced at all.**  If some positive
complex-balanced state exists for these rates then every positive compatibility class contains
one, so existence is immediate — no deficiency or reversibility hypothesis is used.  Combined with
the structural dichotomy this confines the remaining Type II obstruction to rate vectors admitting
no positive complex-balanced state. -/
theorem exists_positive_steadyState_of_complexBalanced
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (x₀ : Concentration S) (hx₀ : x₀.Positive) :
    ∃ x : Concentration S,
      x ∈ N.positiveCompatibilityClass x₀ ∧ N.IsMassActionSteadyState κ x := by
  obtain ⟨x, hmem, hxcb⟩ := N.exists_isComplexBalanced_in_positiveClass κ hxs hcb hx₀
  exact ⟨x, hmem, hxcb.isMassActionSteadyState N κ⟩

end Network
end CRNT
