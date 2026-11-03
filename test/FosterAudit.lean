import CRNT.Stochastic.FosterRecurrence
import CRNT.Kinetics.HillConcordance
import CRNT.Extensions.Turing
import CRNT.Dynamics.EnzymeFastContraction

#print axioms CRNT.Foster.FiniteBranchChain.survival_sum_le
#print axioms CRNT.Foster.FiniteBranchChain.tendsto_survival_zero
#print axioms CRNT.Network.observableGenerator_eq_exitRate_mul
#print axioms CRNT.Network.jumpChain_drift_of_generator
#print axioms CRNT.Network.jumpChain_foster_hitting_time

namespace FosterAudit
open CRNT Filter Topology

/-- Pure degradation `A → ∅`. -/
def decay : Network (Fin 1) := ⟨Fin 1, inferInstance, inferInstance, fun _ => ⟨![1], ![0]⟩⟩

theorem decay_rate (κ : decay.RateConstants) (n : Fin 1 → ℕ) (r : decay.R) :
    decay.stochasticMassActionRate κ n r = κ.k r * (n 0 : ℝ) := by
  simp [Network.stochasticMassActionRate, decay]

theorem decay_sum (g : decay.R → ℝ) : ∑ r, g r = g (0 : Fin 1) := Fin.sum_univ_one g

theorem decay_next (n : Fin 1 → ℕ) : decay.jumpNextCount n (0 : Fin 1) 0 = n 0 - 1 := by
  simp [Network.jumpNextCount, decay]

/-- Non-vacuity: the decay chain started anywhere hits `{0}` with probability one. -/
example (κ : decay.RateConstants) (x : Fin 1 → ℕ) :
    Tendsto (fun m => (decay.jumpChain κ).survival {n | n 0 = 0} m x) atTop (𝓝 0) := by
  classical
  refine (decay.jumpChain_foster_hitting_time κ {n | n 0 = 0} (V := fun n => (n 0 : ℝ))
    (ε := 1) (fun n => by positivity) one_pos (fun n hn => ?_) x).2
  have hn0 : n 0 ≠ 0 := hn
  have hk := κ.positive (0 : Fin 1)
  have hne' : κ.k (0 : Fin 1) * (n 0 : ℝ) ≠ 0 := mul_ne_zero hk.ne' (by exact_mod_cast hn0)
  have hexit : decay.exitRate κ n = κ.k (0 : Fin 1) * (n 0 : ℝ) := by
    rw [Network.exitRate, decay_sum]; exact decay_rate κ n _
  simp only [Foster.FiniteBranchChain.expect, Network.jumpChain, hexit, hne', ite_false,
    decay_sum, Network.jumpProb, decay_rate]
  rw [div_self hne', one_mul, decay_next]
  have : 1 ≤ n 0 := Nat.one_le_iff_ne_zero.mpr hn0
  push_cast [this]
  linarith

end FosterAudit

#print axioms CRNT.Network.hillKinetics_weaklyMonotonic
#print axioms CRNT.Network.Concordant.hill_subsingleton_steadyState
#print axioms CRNT.Network.Concordant.michaelisMenten_subsingleton_steadyState
#print axioms CRNT.Turing.modes_stable_of_equal_diffusion
#print axioms CRNT.Enzyme.fastField_isContracting
#print axioms CRNT.Enzyme.fastField_qss
#print axioms CRNT.Enzyme.fast_dist_qss_le
