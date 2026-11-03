import CRNT.Dynamics.GlobalAttractorTheorem

/-! Closed Global Attractor special cases preserved from the parallel continuation branch. -/
namespace CRNT
namespace Network
variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Convergence form, no critical siphon.**  Every genuine positive trajectory in the positive
compatibility class of a complex-balanced equilibrium converges to it, for any network without a
critical siphon.  This is a fully closed special case of the Global Attractor Theorem: it does not
route through `complexBalanced_genuinePermanent`. -/
theorem complexBalanced_trajectory_converges_of_hasNoCriticalSiphon
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) (hncs : N.HasNoCriticalSiphon) :
    N.PositiveClassTrajectoryConverges κ xstar := by
  intro Γ hΓ0pos hcompat hΓd
  exact N.trajectory_converges_of_persistentForRates κ hxs hcb hΓ0pos hcompat
    (N.complexBalanced_persistentForRates_of_boundaryOmegaExcluded κ hxs hcb
      (N.boundaryOmegaExcluded_of_hasNoCriticalSiphon κ hncs)) rfl hΓd

end Network
end CRNT
