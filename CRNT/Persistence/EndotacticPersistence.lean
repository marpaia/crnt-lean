import CRNT.Dynamics.TierFixedRateRegion
import CRNT.Persistence.ConservativePersistence

/-!
# Weakly reversible strongly endotactic networks are persistent

Strong endotacticity bounds every forward trajectory, uniformly over solutions from one initial
state (`TierDescending.forward_bounded_uniform`); weak reversibility then gives a uniform positive
floor (`weaklyReversible_forward_floor_uniform`).  Together: every forward solution from `x₀`
stays in one compact set of positive states.

* `weaklyReversible_stronglyEndotactic_structurallyPersistent`.
* `singleLinkageStrongPersistence`: the repository's `SingleLinkageStrongPersistenceClaim` (weakly
  reversible, single linkage class ⇒ structurally persistent), via
  `singleLinkageStrongEndotactic`.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Weakly reversible strongly endotactic networks are structurally persistent.** -/
theorem weaklyReversible_stronglyEndotactic_structurallyPersistent (N : Network S)
    (hwr : N.WeaklyReversible) (hse : N.StronglyEndotacticStd) : N.StructurallyPersistent := by
  intro κ x₀ hx₀
  have htd := (N.stronglyEndotacticStd_iff_tierDescending).mp hse
  obtain ⟨B, hB⟩ := htd.forward_bounded_uniform κ hx₀
  obtain ⟨η, hη, hfloor⟩ := N.weaklyReversible_forward_floor_uniform κ hwr hx₀ B
  refine ⟨Set.univ.pi fun _ => Set.Icc η B, isCompact_univ_pi fun _ => isCompact_Icc,
    fun y hy s => lt_of_lt_of_le hη (hy s (Set.mem_univ s)).1, fun Γ hΓ0 hΓd t ht => ?_⟩
  intro s _
  exact ⟨hfloor Γ hΓ0 hΓd (hB Γ hΓ0 hΓd) t ht s, hB Γ hΓ0 hΓd t ht s⟩

/-- **Weakly reversible single-linkage networks are structurally persistent**
(`SingleLinkageStrongPersistenceClaim`). -/
theorem singleLinkageStrongPersistence (N : Network S) : N.SingleLinkageStrongPersistenceClaim :=
  fun hwr hslc => N.weaklyReversible_stronglyEndotactic_structurallyPersistent hwr
    (singleLinkageStrongEndotactic hwr hslc)

/-- The standard-strength single-linkage persistence claim. -/
theorem singleLinkagePersistence (N : Network S) : N.SingleLinkagePersistenceClaim :=
  fun hwr hslc => (N.singleLinkageStrongPersistence hwr hslc).toStd

end Network
end CRNT
