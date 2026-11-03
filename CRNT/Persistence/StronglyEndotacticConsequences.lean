import CRNT.Persistence.StronglyEndotacticPermanence
import CRNT.Dynamics.KnownGlobalPersistenceClasses
import CRNT.Dynamics.SingleLinkageGAC
import CRNT.Persistence.WeaklyReversibleFloor
import CRNT.Dynamics.GlobalAttractorTheorem

/-!
# Consequences of strongly endotactic persistence and permanence

* `StronglyEndotacticStd.persistentFrom`: from each positive state, one compact set of positive
  states contains every forward solution for all times (the library's `PersistentFrom`).
* `StronglyEndotacticStd.structurallyPersistent`, `.structurallyPersistentStd`.
* `StronglyEndotactic.toStd`: the legacy strong-endotactic definition implies the standard one.
* The frontier claims `StrongEndotacticStdPermanenceClaim`, `StrongEndotacticPermanenceClaim`,
  `SingleLinkagePermanenceClaim`, `SingleLinkagePersistenceClaim`,
  `SingleLinkageStrongPersistenceClaim` hold for every network.
* `StronglyEndotacticStd.gac`: the global attractor property for complex-balanced strongly
  endotactic systems (Gopalkrishnan–Miller–Shiu 2014, Theorem 1.2).
-/

open Filter Set
open scoped BigOperators Topology NNReal

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Compact confinement from each positive state.** -/
theorem StronglyEndotacticStd.persistentFrom {N : Network S} (hse : N.StronglyEndotacticStd)
    (κ : N.RateConstants) {x₀ : Concentration S} (hx₀ : x₀.Positive) : N.PersistentFrom κ x₀ := by
  classical
  have htd : N.TierDescending := (N.stronglyEndotacticStd_iff_tierDescending).mp hse
  obtain ⟨M, hM⟩ := htd.forward_bounded_uniform κ hx₀
  obtain ⟨g, hg, hgle⟩ : ∃ g : ℝ, 0 < g ∧ ∀ s, g ≤ x₀ s := by
    by_cases hS : Nonempty S
    · obtain ⟨s₀, -, h⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := S)) x₀
      exact ⟨Finset.univ.inf' Finset.univ_nonempty x₀, by rw [h]; exact hx₀ s₀,
        fun s => Finset.inf'_le _ (Finset.mem_univ s)⟩
    · exact ⟨1, one_pos, fun s => absurd ⟨s⟩ hS⟩
  set G : (ℝ → Concentration S) → Prop := fun Γ => Γ 0 = x₀ ∧
    ∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t
  obtain ⟨m, hm, hmle⟩ := StronglyEndotacticStd.persistent_uniform hse κ G x₀
    (fun Γ hΓ => hΓ.2) (fun Γ hΓ => by rw [hΓ.1, sub_self]; exact Submodule.zero_mem _)
    hg (fun Γ hΓ s => hΓ.1 ▸ hgle s) (M := M) (fun Γ hΓ => hM Γ hΓ.1 hΓ.2)
  refine ⟨N.classInteriorBox x₀ m M, N.isCompact_classInteriorBox x₀ m M,
    fun y hy s => hm.trans_le (hy.2 s).1, fun Γ hΓ0 hsol t ht => ?_⟩
  refine ⟨?_, fun s => ⟨hmle Γ ⟨hΓ0, hsol⟩ t ht s, hM Γ hΓ0 hsol t ht s⟩⟩
  have := N.stoichCompatible_of_forward_solution κ hsol t ht
  rw [hΓ0] at this
  exact this

/-- Strongly endotactic networks are structurally persistent (compact-confinement form). -/
theorem StronglyEndotacticStd.structurallyPersistent {N : Network S}
    (hse : N.StronglyEndotacticStd) : N.StructurallyPersistent :=
  fun κ _ hx₀ => hse.persistentFrom κ hx₀

/-- Strongly endotactic networks are structurally persistent (standard form). -/
theorem StronglyEndotacticStd.structurallyPersistentStd {N : Network S}
    (hse : N.StronglyEndotacticStd) : N.StructurallyPersistentStd :=
  hse.structurallyPermanent.toPersistentStd

/-- The legacy strong-endotactic definition implies the standard one: if all sources lie on one
`w`-level, every source is `w`-maximal and endotacticity makes an active reaction strictly
`w`-decreasing. -/
theorem StronglyEndotactic.toStd {N : Network S} (h : N.StronglyEndotactic) :
    N.StronglyEndotacticStd := by
  refine ⟨h.endotactic, fun w hactive => ?_⟩
  by_cases hdiff : ∃ r₁ r₂ : N.R, N.wValue w r₁ ≠ N.wValue w r₂
  · exact h.2 w hdiff
  · push Not at hdiff
    obtain ⟨r, hr⟩ := hactive
    have hmax : N.IsMaxSource w r := fun r' => (hdiff r' r).le
    exact ⟨r, hmax, lt_of_le_of_ne (h.endotactic w r hmax) hr⟩

/-! ## Frontier claims -/

theorem strongEndotacticStdPermanenceClaim (N : Network S) :
    N.StrongEndotacticStdPermanenceClaim :=
  fun hse => hse.structurallyPermanent

theorem strongEndotacticPermanenceClaim (N : Network S) : N.StrongEndotacticPermanenceClaim :=
  fun hse => hse.toStd.structurallyPermanent

theorem singleLinkagePermanenceClaim (N : Network S) : N.SingleLinkagePermanenceClaim :=
  fun hwr hslc => (hwr.stronglyEndotacticStd_of_singleLinkageClass hslc).structurallyPermanent

theorem singleLinkagePersistenceClaim (N : Network S) : N.SingleLinkagePersistenceClaim :=
  fun hwr hslc => (hwr.stronglyEndotacticStd_of_singleLinkageClass hslc).structurallyPersistentStd

theorem singleLinkageStrongPersistenceClaim (N : Network S) :
    N.SingleLinkageStrongPersistenceClaim :=
  fun hwr hslc => (hwr.stronglyEndotacticStd_of_singleLinkageClass hslc).structurallyPersistent

/-- **Global attractor property for complex-balanced strongly endotactic systems**
(Gopalkrishnan–Miller–Shiu 2014, Theorem 1.2). For a weakly reversible, strongly endotactic
network with a positive complex-balanced equilibrium `x*`, the ω-limit set of every positive
state in the class of `x*` is `{x*}`. -/
theorem StronglyEndotacticStd.gac {N : Network S} (hse : N.StronglyEndotacticStd)
    (hwr : N.WeaklyReversible) (κ : N.RateConstants) {xstar x₀ : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) (hx0 : x₀.Positive)
    (hx0compat : N.StoichCompatible x₀ xstar) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit atTop ϕ {x₀} = {xstar} :=
  N.gac_of_persistent hwr κ hxs hcb hx0 hx0compat (hse.persistentFrom κ hx0)

/-- **Single-linkage-class GAC, unconditionally** (Anderson 2011): the persistence hypothesis of
`singleLinkageClass_gac` is discharged. -/
theorem singleLinkageClass_gac_unconditional (N : Network S) (hwr : N.WeaklyReversible)
    (hslc : N.SingleLinkageClass) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) (hx0compat : N.StoichCompatible x₀ xstar) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit atTop ϕ {x₀} = {xstar} :=
  N.singleLinkageClass_gac hwr hslc κ hxs hcb hx0 hx0compat fun _ =>
    (hwr.stronglyEndotacticStd_of_singleLinkageClass hslc).persistentFrom κ hx0

/-- **Weakly reversible networks with bounded positive trajectories are persistent** (any
stoichiometric dimension; via the library's weakly reversible floor). -/
theorem weaklyReversible_structurallyPersistentStd_of_bounded {N : Network S}
    (hwr : N.WeaklyReversible) (hbdd : N.StructurallyBoundedPositiveTrajectories) :
    N.StructurallyPersistentStd := by
  intro κ ϕ γ hflow x₀ hx₀ s
  obtain ⟨K, hKc, hK⟩ := hbdd κ ϕ γ hflow x₀ hx₀
  obtain ⟨hzero, hϕγ, hsol⟩ := hflow
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ y ∈ K, ∀ s, y s ≤ M := by
    have hb : ∀ s : S, ∃ M : ℝ, ∀ y ∈ K, y s ≤ M := fun s => by
      obtain ⟨M, hM⟩ := hKc.bddAbove_image (continuous_apply s).continuousOn
      exact ⟨M, fun y hy => hM ⟨y, hy, rfl⟩⟩
    choose Mf hMf using hb
    by_cases hS : Nonempty S
    · refine ⟨Finset.univ.sup' Finset.univ_nonempty Mf, fun y hy s => ?_⟩
      exact (hMf s y hy).trans (Finset.le_sup' Mf (Finset.mem_univ s))
    · exact ⟨0, fun y _ s => absurd ⟨s⟩ hS⟩
  have hγ0 : (γ x₀ 0).Positive := by rw [hzero]; exact hx₀
  have hbd : ∀ t : ℝ, 0 ≤ t → ∀ s, γ x₀ t s ≤ M := fun t ht s => by
    have h1 := hK ⟨t, ht⟩
    rw [hϕγ x₀ ⟨t, ht⟩] at h1
    exact hM _ h1 s
  obtain ⟨η, hη, hfl⟩ := N.weaklyReversible_forward_floor κ hwr hγ0 (hsol x₀) hbd
  refine ⟨η, hη, fun t => ?_⟩
  rw [hϕγ x₀ t]
  exact hfl t t.2 s

/-- Pantea's two-dimensional theorem in the frontier's form holds (the rank hypothesis is not
needed). -/
theorem twoDimensionalWRBoundedPersistenceClaim (N : Network S) :
    N.TwoDimensionalWRBoundedPersistenceClaim :=
  fun hwr _ hbdd => weaklyReversible_structurallyPersistentStd_of_bounded hwr hbdd

/-- **Strongly endotactic networks are permanent, trajectory form** in the library's
`GenuinePermanentForRates` (no global flow is presupposed). -/
theorem StronglyEndotacticStd.genuinePermanentForRates {N : Network S}
    (hse : N.StronglyEndotacticStd) (κ : N.RateConstants) : N.GenuinePermanentForRates κ := by
  intro xref _
  obtain ⟨K, hKc, hKsub, hK⟩ := hse.permanent_trajectories κ xref
  exact ⟨K, hKc, hKsub, fun x₀ hx₀ Γ hΓ0 hsol => hK Γ (hΓ0 ▸ hx₀) hsol⟩

end Network
end CRNT
