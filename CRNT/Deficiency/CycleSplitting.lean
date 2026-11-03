import CRNT.Deficiency.CycleExactSequence
import CRNT.Deficiency.DeficiencyOne
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Splitting the stoichiometric cycle space

The exact sequence

`0 → ker ∂ → ker S → D → 0`

splits noncanonically over `ℝ`. Hence the steady reaction-cycle space is a direct sum of
ordinary graph circulations and a complementary deficiency-cycle space isomorphic to the
deficiency subspace.  This is the reaction-coordinate form of the statement that
`δ` counts independent stoichiometric cycles that are not graph cycles.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A choice of linear complement to graph circulations inside stoichiometric cycles. -/
noncomputable def deficiencyCycleComplement (N : Network S) :
    Submodule ℝ N.stoichCycleSpace :=
  Submodule.exists_isCompl (N.graphCycleSpace.comap N.stoichCycleSpace.subtype) |>.choose

/-- The chosen complement is complementary to graph cycles. -/
theorem graphCycles_isCompl_deficiencyCycleComplement (N : Network S) :
    IsCompl (N.graphCycleSpace.comap N.stoichCycleSpace.subtype)
      N.deficiencyCycleComplement := by
  exact (Submodule.exists_isCompl
    (N.graphCycleSpace.comap N.stoichCycleSpace.subtype)).choose_spec

/-- Every stoichiometric cycle has a unique graph-cycle plus deficiency-cycle decomposition. -/
theorem existsUnique_graph_plus_deficiencyCycle (N : Network S)
    (v : N.stoichCycleSpace) :
    ∃! p : (N.graphCycleSpace.comap N.stoichCycleSpace.subtype) ×
        N.deficiencyCycleComplement,
      (p.1.1 : N.R → ℝ) + p.2.1 = v.1 := by
  obtain ⟨p, hp, huniq⟩ :=
    Submodule.existsUnique_add_of_isCompl_prod
      (N.graphCycles_isCompl_deficiencyCycleComplement) v
  refine ⟨p, ?_, ?_⟩
  · change ((p.1.1 + p.2.1 : N.stoichCycleSpace) : N.R → ℝ) = v.1
    exact congrArg (fun x : N.stoichCycleSpace => x.1) hp
  · intro q hq
    apply huniq q
    apply Subtype.ext
    exact hq

/-- Restriction of the cycle-to-deficiency map to the complement is an isomorphism. -/
noncomputable def deficiencyCycleComplementEquivDeficiency (N : Network S) :
    N.deficiencyCycleComplement ≃ₗ[ℝ] N.deficiencySubspace := by
  let f : N.deficiencyCycleComplement →ₗ[ℝ] N.deficiencySubspace :=
    N.cycleToDeficiency.domRestrict N.deficiencyCycleComplement
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    have hdiff : f (x - y) = 0 := by
      calc
        f (x - y) = f x - f y := map_sub f x y
        _ = 0 := sub_eq_zero.mpr hxy
    have hgraph : ((x - y).1 : N.stoichCycleSpace) ∈
        N.graphCycleSpace.comap N.stoichCycleSpace.subtype := by
      rw [← N.cycleToDeficiency_ker]
      exact LinearMap.mem_ker.mpr hdiff
    have hcomp : ((x - y).1 : N.stoichCycleSpace) ∈ N.deficiencyCycleComplement :=
      (x - y).2
    have hinter : ((x - y).1 : N.stoichCycleSpace) ∈
        (N.graphCycleSpace.comap N.stoichCycleSpace.subtype) ⊓
          N.deficiencyCycleComplement := ⟨hgraph, hcomp⟩
    rw [(N.graphCycles_isCompl_deficiencyCycleComplement).inf_eq_bot,
      Submodule.mem_bot] at hinter
    have hxy0 : x - y = 0 := by
      apply Subtype.ext
      exact hinter
    exact sub_eq_zero.mp hxy0
  · intro z
    obtain ⟨v, hv⟩ := N.cycleToDeficiency_surjective z
    obtain ⟨p, hp, _⟩ := N.existsUnique_graph_plus_deficiencyCycle v
    refine ⟨p.2, ?_⟩
    change N.cycleToDeficiency p.2.1 = z
    have hgker : N.cycleToDeficiency p.1.1 = 0 := by
      apply LinearMap.mem_ker.mp
      rw [N.cycleToDeficiency_ker]
      exact p.1.2
    have hsum : p.1.1 + p.2.1 = v := by
      apply Subtype.ext
      exact hp
    have hmap := congrArg N.cycleToDeficiency hsum
    simp only [map_add, hgker, zero_add] at hmap
    exact hmap.trans hv

/-- Dimension of the deficiency-cycle complement is exactly the deficiency. -/
theorem finrank_deficiencyCycleComplement (N : Network S) :
    Module.finrank ℝ N.deficiencyCycleComplement = N.deficiency := by
  calc
    Module.finrank ℝ N.deficiencyCycleComplement
        = Module.finrank ℝ N.deficiencySubspace :=
          LinearEquiv.finrank_eq N.deficiencyCycleComplementEquivDeficiency
    _ = N.deficiency := rfl

/-- At deficiency zero, the complement is trivial. -/
theorem deficiencyCycleComplement_eq_bot_of_deficiencyZero (N : Network S)
    (hδ : N.deficiency = 0) : N.deficiencyCycleComplement = ⊥ := by
  apply Submodule.finrank_eq_zero.mp
  rw [N.finrank_deficiencyCycleComplement, hδ]

/-- At deficiency one, the complement is one-dimensional. -/
theorem finrank_deficiencyCycleComplement_eq_one_of_deficiencyOne (N : Network S)
    (hδ : N.DeficiencyOne) :
    Module.finrank ℝ N.deficiencyCycleComplement = 1 := by
  rw [N.finrank_deficiencyCycleComplement]
  exact (N.deficiencyOne_iff_deficiency_eq_one.mp hδ)

/-- A deficiency-one CRN admits a single excess stoichiometric cycle such that every
stoichiometric cycle is a graph circulation plus a scalar multiple of that cycle. -/
theorem exists_excessCycle_of_deficiencyOne (N : Network S)
    (hδ : N.DeficiencyOne) :
    ∃ e : N.R → ℝ,
      e ∈ N.stoichCycleSpace ∧ e ∉ N.graphCycleSpace ∧
      ∀ v : N.R → ℝ, v ∈ N.stoichCycleSpace →
        ∃ (g : N.R → ℝ) (a : ℝ),
          g ∈ N.graphCycleSpace ∧ v = g + a • e := by
  have hdim : Module.finrank ℝ N.deficiencyCycleComplement = 1 :=
    N.finrank_deficiencyCycleComplement_eq_one_of_deficiencyOne hδ
  have hne : N.deficiencyCycleComplement ≠ ⊥ := by
    intro hbot
    have h := hdim
    rw [hbot, finrank_bot] at h
    omega
  obtain ⟨ec, hec0⟩ :=
    Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hne)
  refine ⟨ec.1.1, ec.1.2, ?_, ?_⟩
  · intro hgraph
    have hboth : ec.1 ∈
        (N.graphCycleSpace.comap N.stoichCycleSpace.subtype) ⊓
          N.deficiencyCycleComplement := by
      refine ⟨?_, ec.2⟩
      exact hgraph
    rw [(N.graphCycles_isCompl_deficiencyCycleComplement).inf_eq_bot,
      Submodule.mem_bot] at hboth
    apply hec0
    apply Subtype.ext
    exact hboth
  · intro v hv
    let vv : N.stoichCycleSpace := ⟨v, hv⟩
    obtain ⟨p, hp, _⟩ := N.existsUnique_graph_plus_deficiencyCycle vv
    obtain ⟨a, ha⟩ :=
      (finrank_eq_one_iff_of_nonzero' ec hec0).mp hdim p.2
    refine ⟨p.1.1.1, a, p.1.2, ?_⟩
    have ha' : (a • ec).1.1 = p.2.1.1 :=
      congrArg (fun z : N.deficiencyCycleComplement => z.1.1) ha
    dsimp [vv] at hp
    rw [← hp, ← ha']
    rfl

end Network
end CRNT
