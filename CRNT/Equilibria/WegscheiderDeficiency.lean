import CRNT.Equilibria.WegscheiderGenerators
import CRNT.Deficiency.CycleExactSequence
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Deficiency as the excess Wegscheider-cycle space

The reaction-cycle exact sequence gives a precise interpretation of deficiency in
thermodynamic cycle constraints.

* `ker ∂` consists of ordinary directed graph circulations;
* `ker S` consists of all stoichiometric reaction cycles;
* `(ker S)/(ker ∂) ≃ D`, the deficiency space.

Hence a logarithmic affinity must first vanish on graph cycles and then on exactly
`δ` additional independent cycle directions.  At deficiency zero there are no extra
directions: graph-cycle Wegscheider identities already imply all stoichiometric
Wegscheider identities.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Wegscheider compatibility tested only on graph circulations. -/
def SatisfiesGraphWegscheider (N : Network S) (ρ : ReversiblePairing N)
    (κ : N.RateConstants) : Prop :=
  N.logEquilibriumConstant ρ κ ∈ orthSum N.graphCycleSpace

/-- Expanded graph-cycle form. -/
theorem satisfiesGraphWegscheider_iff
    (N : Network S) (ρ : ReversiblePairing N) (κ : N.RateConstants) :
    N.SatisfiesGraphWegscheider ρ κ ↔
      ∀ z ∈ N.graphCycleSpace,
        N.cycleAffinity ρ κ z = 0 := by
  rfl

/-- Full Wegscheider compatibility always implies graph-cycle compatibility. -/
theorem satisfiesGraphWegscheider_of_satisfiesWegscheider
    (N : Network S) (ρ : ReversiblePairing N) (κ : N.RateConstants)
    (hW : N.SatisfiesWegscheider ρ κ) :
    N.SatisfiesGraphWegscheider ρ κ := by
  rw [N.satisfiesGraphWegscheider_iff]
  intro z hz
  have hzS : z ∈ N.stoichCycleSpace := N.graphCycleSpace_le_stoichCycleSpace hz
  exact (N.satisfiesWegscheider_iff ρ κ).1 hW z hzS

/-- Quotient of stoichiometric cycles by ordinary graph circulations. -/
abbrev WegscheiderExcessSpace (N : Network S) :=
  N.stoichCycleSpace ⧸
    (N.graphCycleSpace.comap N.stoichCycleSpace.subtype)

/-- The excess Wegscheider-cycle space is canonically the deficiency space. -/
noncomputable def wegscheiderExcessEquivDeficiency (N : Network S) :
    N.WegscheiderExcessSpace ≃ₗ[ℝ] N.deficiencySubspace :=
  N.cycleQuotientEquivDeficiency

/-- Number of independent excess thermodynamic cycle directions is exactly the
deficiency. -/
theorem finrank_wegscheiderExcessSpace (N : Network S) :
    Module.finrank ℝ N.WegscheiderExcessSpace =
      Module.finrank ℝ N.deficiencySubspace := by
  exact LinearEquiv.finrank_eq N.wegscheiderExcessEquivDeficiency

/-- Integer-valued version of the preceding count. -/
theorem finrank_wegscheiderExcessSpace_eq_deficiencyInt (N : Network S) :
    (Module.finrank ℝ N.WegscheiderExcessSpace : ℤ) = N.deficiencyInt := by
  rw [N.finrank_wegscheiderExcessSpace]
  exact (N.deficiencyInt_eq_finrank_deficiencySubspace).symm

/-- Restriction of the affinity functional to the stoichiometric cycle space. -/
noncomputable def stoichCycleAffinity
    (N : Network S) (ρ : ReversiblePairing N) (κ : N.RateConstants) :
    N.stoichCycleSpace →ₗ[ℝ] ℝ :=
  (N.cycleAffinityLinear ρ κ).domRestrict N.stoichCycleSpace

/-- Under graph-cycle Wegscheider conditions, the cycle affinity descends to the
excess quotient. -/
noncomputable def excessAffinity
    (N : Network S) (ρ : ReversiblePairing N) (κ : N.RateConstants)
    (hgraph : N.SatisfiesGraphWegscheider ρ κ) :
    N.WegscheiderExcessSpace →ₗ[ℝ] ℝ := by
  -- quotient lift of `stoichCycleAffinity`; `hgraph` says the graph-cycle submodule is
  -- in its kernel.
  refine Submodule.liftQ _ (N.stoichCycleAffinity ρ κ) ?_
  intro z hz
  exact (N.satisfiesGraphWegscheider_iff ρ κ).1 hgraph z.1 hz

/-- Once graph-cycle constraints hold, full Wegscheider compatibility is exactly
vanishing of the induced deficiency/excess functional. -/
theorem satisfiesWegscheider_iff_graph_and_excess_zero
    (N : Network S) (ρ : ReversiblePairing N) (κ : N.RateConstants) :
    N.SatisfiesWegscheider ρ κ ↔
      ∃ hgraph : N.SatisfiesGraphWegscheider ρ κ,
        N.excessAffinity ρ κ hgraph = 0 := by
  constructor
  · intro hW
    let hgraph : N.SatisfiesGraphWegscheider ρ κ :=
      N.satisfiesGraphWegscheider_of_satisfiesWegscheider ρ κ hW
    refine ⟨hgraph, ?_⟩
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ z =>
      change N.stoichCycleAffinity ρ κ z = 0
      change N.cycleAffinity ρ κ z.1 = 0
      exact (N.satisfiesWegscheider_iff ρ κ).1 hW z.1 z.2
  · rintro ⟨hgraph, hex⟩
    rw [N.satisfiesWegscheider_iff]
    intro z hz
    let zs : N.stoichCycleSpace := ⟨z, hz⟩
    have hq := LinearMap.congr_fun hex (Submodule.Quotient.mk zs)
    rw [LinearMap.zero_apply] at hq
    change N.stoichCycleAffinity ρ κ zs = 0 at hq
    change N.cycleAffinity ρ κ z = 0 at hq
    exact hq

/-- **Deficiency-zero collapse of Wegscheider constraints.** -/
theorem deficiencyZero_graphWegscheider_iff_Wegscheider
    (N : Network S) (hδ : N.DeficiencyZero)
    (ρ : ReversiblePairing N) (κ : N.RateConstants) :
    N.SatisfiesGraphWegscheider ρ κ ↔ N.SatisfiesWegscheider ρ κ := by
  have hspaces := N.deficiencyZero_iff_stoichCycles_eq_graphCycles.mp hδ
  change N.logEquilibriumConstant ρ κ ∈ orthSum N.graphCycleSpace ↔
    N.logEquilibriumConstant ρ κ ∈ orthSum N.stoichCycleSpace
  rw [hspaces]

/-- Thus, for a deficiency-zero reversible network, ordinary graph-cycle product
identities already guarantee a positive detailed-balanced equilibrium. -/
theorem exists_positiveDetailedBalanced_of_graphWegscheider_deficiencyZero
    (N : Network S) (hδ : N.DeficiencyZero)
    (ρ : ReversiblePairing N) (κ : N.RateConstants)
    (hgraph : N.SatisfiesGraphWegscheider ρ κ) :
    ∃ x : Concentration S, N.IsPositiveDetailedBalanced κ x := by
  have hW := (N.deficiencyZero_graphWegscheider_iff_Wegscheider hδ ρ κ).1 hgraph
  exact N.exists_positiveDetailedBalanced_of_satisfiesWegscheider ρ κ hW

end Network
end CRNT
