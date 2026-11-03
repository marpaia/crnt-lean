import CRNT.Persistence.OrbitClosureSiphon
import CRNT.Dynamics.CriticalSiphonDichotomy

/-!
# Persistence from the absence of critical siphons (paper notion)

With criticality in the sense of Angeli–De Leenheer–Sontag and Deshpande–Gopalkrishnan
(`IsDGCritical`: no nonzero nonnegative conservation law supported in the set):

* `orbitClosure_positive_of_hasNoDGCriticalSiphon` — if no siphon is critical, every closure point
  of every positive forward orbit is positive (Angeli–De Leenheer–Sontag 2007, here with no
  boundedness or conservativity hypothesis).  Drainable sets are critical
  (`isDGCritical_of_isFluxDrainable`), so this follows from the drainable-siphon theorem.
* `hasNoDGCriticalSiphon_of_weaklyReversible_hasNoSelfReplicableSiphon` — a weakly reversible
  network with no self-replicable siphon has no critical siphon (Deshpande–Gopalkrishnan 2014,
  Theorem 5.3 with weak reversibility).

These replace, for the paper notion, the conditional theorems of `SiphonAutocatalysis.lean` that
take `MinimalCriticalSiphonDichotomy` as input; that input is false for the repository's
exact-support notion (`Examples/CriticalSiphonDichotomyCounterexample`).

Nothing here is an axiom or a `sorry`.
-/

open Finset

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- No critical siphon in the paper's sense. -/
def HasNoDGCriticalSiphon (N : Network S) : Prop := ∀ P : Finset S, ¬ N.IsDGCriticalSiphon P

/-- A drainable siphon is a critical siphon. -/
theorem IsDrainableSiphon.isDGCriticalSiphon {N : Network S} {P : Finset S}
    (h : N.IsDrainableSiphon P) : N.IsDGCriticalSiphon P :=
  ⟨h.1, h.2.1, isDGCritical_of_isFluxDrainable h.2.2.toFlux⟩

/-- No critical siphon implies no drainable siphon. -/
theorem hasNoDrainableSiphon_of_hasNoDGCriticalSiphon {N : Network S}
    (h : N.HasNoDGCriticalSiphon) : N.HasNoDrainableSiphon :=
  fun P hP => h P hP.isDGCriticalSiphon

/-- **Siphon criterion for persistence.** If no siphon is critical (paper notion), every point of
the closure of every positive forward mass-action orbit is positive. -/
theorem orbitClosure_positive_of_hasNoDGCriticalSiphon (N : Network S)
    (h : N.HasNoDGCriticalSiphon) (κ : N.RateConstants) {γ : ℝ → Concentration S}
    (hγ0 : (γ 0).Positive)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    {w : Concentration S} (hw : ∀ ε > 0, ∃ t, 0 ≤ t ∧ dist (γ t) w < ε) : w.Positive :=
  N.orbitClosure_positive_of_hasNoDrainableSiphon (hasNoDrainableSiphon_of_hasNoDGCriticalSiphon h)
    κ hγ0 hsol hw

/-- Every critical siphon contains a minimal one. -/
theorem exists_minimalDGCriticalSiphon_subset (N : Network S) :
    ∀ {P : Finset S}, N.IsDGCriticalSiphon P →
      ∃ Q ⊆ P, N.IsMinimalDGCriticalSiphon Q := by
  intro P
  induction P using Finset.strongInduction with
  | H P ih =>
    intro hP
    by_cases hmin : ∀ Q : Finset S, Q ⊆ P → Q ≠ P → Q.Nonempty → ¬ N.IsDGCriticalSiphon Q
    · exact ⟨P, subset_refl _, hP, hmin⟩
    · push Not at hmin
      obtain ⟨Q, hQP, hQne, -, hQ⟩ := hmin
      obtain ⟨R, hRQ, hR⟩ := ih Q (Finset.ssubset_iff_subset_ne.mpr ⟨hQP, hQne⟩) hQ
      exact ⟨R, hRQ.trans hQP, hR⟩

/-- **Weakly reversible, non-autocatalytic networks have no critical siphon** (paper notion). -/
theorem hasNoDGCriticalSiphon_of_weaklyReversible_hasNoSelfReplicableSiphon (N : Network S)
    (hwr : N.WeaklyReversible) (hnosr : N.HasNoSelfReplicableSiphon) : N.HasNoDGCriticalSiphon := by
  intro P hP
  obtain ⟨Q, -, hQ⟩ := N.exists_minimalDGCriticalSiphon_subset hP
  have heq := N.selfReplicable_iff_drainable_of_weaklyReversible N.fluxSignRealizable hwr Q
  have hsr : N.IsSelfReplicable Q := by
    rcases drainable_or_selfReplicable_of_minimalDGCritical hQ with h | h
    · exact heq.mpr h
    · exact h
  exact hnosr Q ⟨hQ.1.1, hQ.1.2.1, hsr⟩

end Network
end CRNT
