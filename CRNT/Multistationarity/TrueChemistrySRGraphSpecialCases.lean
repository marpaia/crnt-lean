import CRNT.Multistationarity.TrueChemistrySRCriterion

/-! Compatibility helper preserved from the corrected true-chemistry SR-graph branch. -/
namespace CRNT
namespace Network
variable {S : Type} [DecidableEq S] [Fintype S]

/-- The fully open extension of a network whose zero-complex reactions are already singleton
flows again has that property. -/
theorem zeroComplexReactionsAreFlows_of_no_zero_complex (N : Network S)
    (h : ∀ r : N.R, ¬ N.IsFlowChannel r) : N.ZeroComplexReactionsAreFlows :=
  fun r hr => absurd hr (h r)

end Network
end CRNT
