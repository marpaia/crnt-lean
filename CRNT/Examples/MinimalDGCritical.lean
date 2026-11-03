import CRNT.Examples.ConservativeNonPersistent
import CRNT.Examples.CriticalSiphonDichotomyCounterexample
import CRNT.Dynamics.CriticalSiphonDichotomy

set_option backward.isDefEq.respectTransparency false

/-!
# Instances for the corrected critical-siphon notion

* In `A → B` (`CRNT.Examples.Minimal.N`), `{A}` is a minimal critical siphon in the sense of
  Deshpande–Gopalkrishnan, so `drainable_or_selfReplicable_of_minimalDGCritical` applies
  (non-vacuity), and it yields drainability of `{A}`.
* In the counterexample `A ⇌ A + B`, the set `{A, B}` is not critical in that sense: the law
  `x_A` has support inside it.  The two notions differ exactly here.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT.Examples

open CRNT CRNT.Network

/-- `{A}` is a minimal critical siphon of `A → B` (paper's notion). -/
theorem Minimal.isMinimalDGCriticalSiphon_A :
    Minimal.N.IsMinimalDGCriticalSiphon {Minimal.Species.A} := by
  refine ⟨⟨⟨_, Finset.mem_singleton_self _⟩, ?_, ?_⟩, ?_⟩
  · rintro r ⟨s, hs, hprod⟩
    rw [Finset.mem_singleton] at hs
    subst hs
    cases r
    simp [IsProduct, Minimal.N, Minimal.rxn, Minimal.cB] at hprod
  · rintro ⟨w, hw0, hwP, ⟨s, hs⟩, hcons⟩
    have hB : w Minimal.Species.B = 0 := hwP _ (by simp)
    have hA : 0 < w Minimal.Species.A := by
      cases s
      · exact hs
      · rw [hB] at hs; exact absurd hs (lt_irrefl 0)
    have h := hcons Minimal.Rxn.r1
    rw [Minimal.reactionVector_r1] at h
    simp [Minimal.univ_species, hB] at h
    linarith
  · intro Q hQ hne hQne
    exact absurd (Finset.Nonempty.subset_singleton_iff hQne |>.mp hQ) hne

/-- Hence `{A}` is drainable in `A → B`, by the dichotomy (it is not self-replicable). -/
theorem Minimal.drainable_or_selfReplicable_A :
    Minimal.N.IsDrainable {Minimal.Species.A} ∨ Minimal.N.IsSelfReplicable {Minimal.Species.A} :=
  drainable_or_selfReplicable_of_minimalDGCritical Minimal.isMinimalDGCriticalSiphon_A

/-- In `A ⇌ A + B`, `{A, B}` is not critical in the paper's sense. -/
theorem CriticalDichotomyCE.not_isDGCritical_univ :
    ¬ CriticalDichotomyCE.N.IsDGCritical Finset.univ := fun h =>
  h ⟨![1, 0], fun s => by fin_cases s <;> simp, fun s hs => absurd (Finset.mem_univ s) hs,
    ⟨0, by simp⟩, fun r => by rw [Fin.sum_univ_two, CriticalDichotomyCE.reactionVector_A]; simp⟩

end CRNT.Examples
