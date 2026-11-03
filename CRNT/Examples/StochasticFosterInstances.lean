import CRNT.Stochastic.MinimalSemigroupFoster
import CRNT.Stochastic.MinimalSemigroupErgodic

/-!
# Instances of the non-explosion and Foster theorems

* `0 → X`, `X → 2X`, `2X → 0` (any positive rates) is not conservative; with `w = 1` the only
  reactions increasing `w` are `0 → X` and `X → 2X`, which have at most one reactant molecule, so
  its minimal transition function is stochastic (`Growth.stochastic`).
* `0 → X`, `X → 0` with unit rates: `QV(n) = 1 − n` for `V(n) = n`, which is `≤ −1` off
  `C = {0, 1}`; the chain enters `C` with probability tending to one, and the expected time
  spent outside `C` before entering it is at most `n` (`BirthDeath.tendsto_absorbed_one`,
  `BirthDeath.integral_notAbsorbed_le`).
* The two-state flip chain on `Bool` (rate `1`) is closed and irreducible on `univ`, so the ergodic
  theorem applies (`TwoState.ergodic`).
-/

namespace CRNT
namespace Examples

open Network

namespace Growth

/-- `0 → X`, `X → 2X`, `2X → 0`. -/
abbrev net : Network Unit :=
  ⟨Fin 3, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨0, fun _ => 1⟩ else if r = 1 then ⟨fun _ => 1, fun _ => 2⟩
    else ⟨fun _ => 2, 0⟩⟩

theorem molecularity (r : net.R) (hr : 0 < ∑ s, (fun _ => (1 : ℝ)) s * net.reactionVector r s) :
    ∑ s, (net.reaction r).source s ≤ 1 := by
  fin_cases r <;> simp_all [Network.reactionVector, Reaction.vector]
  norm_num at hr

/-- **Non-explosion of `0 → X`, `X → 2X`, `2X → 0`** for every choice of positive rates. -/
theorem stochastic (κ : RateConstants net) {t : ℝ} (ht : 0 ≤ t) (n : Unit → ℕ) :
    HasSum (fun m => net.transition κ t n m) 1 :=
  net.hasSum_transition_one_of_weight κ (fun _ => 1) (fun _ => one_pos) molecularity ht n

end Growth

namespace BirthDeath

/-- `0 → X`, `X → 0`. -/
abbrev net : Network Unit :=
  ⟨Fin 2, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨0, fun _ => 1⟩ else ⟨fun _ => 1, 0⟩⟩

/-- Unit rates. -/
def κ : RateConstants net := ⟨fun _ => 1, fun _ => one_pos⟩

/-- The Lyapunov function `V(n) = n`. -/
noncomputable def V (n : Unit → ℕ) : ℝ := linearObservable (fun _ => 1) n

theorem V_eq (n : Unit → ℕ) : V n = n () := by simp [V, linearObservable]

theorem drift_eq (n : Unit → ℕ) : (net.jumpSystem κ).drift V n = 1 - n () := by
  unfold V
  rw [jumpSystem_drift_linear]
  simp [Fin.sum_univ_two, stochasticMassActionRate, κ, Network.reactionVector, Reaction.vector]
  ring

/-- The finite set `C = {0, 1}`. -/
def C : Finset (Unit → ℕ) := (Finset.range 2).image fun m _ => m

theorem mem_C {n : Unit → ℕ} (h : n () ≤ 1) : n ∈ C := by
  refine Finset.mem_image.mpr ⟨n (), Finset.mem_range.mpr (by omega), ?_⟩
  funext u; rfl

theorem drift_le (n : Unit → ℕ) (hn : n ∉ C) : (net.jumpSystem κ).drift V n ≤ -1 := by
  rw [drift_eq]
  have : 2 ≤ n () := by
    by_contra h
    exact hn (mem_C (by omega))
  have : (2 : ℝ) ≤ n () := by exact_mod_cast this
  linarith

theorem V_nonneg (n : Unit → ℕ) : 0 ≤ V n := by rw [V_eq]; exact Nat.cast_nonneg _

theorem finite_V (R : ℝ) : {n | V n ≤ R}.Finite :=
  finite_linearObservable_le (fun _ => 1) (fun _ => one_pos) R

/-- **Hitting `{0, 1}` with probability one.** -/
theorem tendsto_absorbed_one (n : Unit → ℕ) :
    Filter.Tendsto (fun T => ∑ b ∈ C, ((net.jumpSystem κ).stopOn C).Pmin T n b) Filter.atTop
      (nhds 1) :=
  (net.jumpSystem κ).tendsto_absorbed_one C V V_nonneg finite_V one_pos drift_le n

/-- **Expected hitting time of `{0, 1}` is at most `n`.** -/
theorem integral_notAbsorbed_le (n : Unit → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, (1 - ∑ b ∈ C, ((net.jumpSystem κ).stopOn C).Pmin t n b) ≤ n () := by
  have := (net.jumpSystem κ).integral_notAbsorbed_le C V V_nonneg finite_V one_pos drift_le hT n
  rwa [div_one, V_eq] at this

end BirthDeath

namespace TwoState

/-- The flip chain on `Bool` with unit rate. -/
def J : JumpSystem Bool where
  ι := Unit
  rate _ _ := 1
  rate_nonneg _ _ := zero_le_one
  next _ b := !b

theorem closedOn : J.ClosedOn Finset.univ := fun _ _ _ _ => Finset.mem_univ _

theorem reach (a b : Bool) : J.ReachPos a b := by
  by_cases h : a = b
  · subst h; exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single ⟨(), one_pos, by cases a <;> cases b <;> simp_all [J]⟩

/-- **Ergodic theorem for the flip chain.** -/
theorem ergodic :
    ∃ π : Bool → ℝ, (∀ a ∈ Finset.univ, ∀ b ∈ Finset.univ,
        Filter.Tendsto (fun t => J.Pmin t a b) Filter.atTop (nhds (π b))) ∧
      ∑ b ∈ Finset.univ, π b = 1 ∧
      (∀ t, 0 ≤ t → ∀ b ∈ Finset.univ, ∑ a ∈ Finset.univ, π a * J.Pmin t a b = π b) ∧
      ∀ μ : Bool → ℝ, ∑ a ∈ Finset.univ, μ a = 1 →
        (∀ t, 0 ≤ t → ∀ b ∈ Finset.univ, ∑ a ∈ Finset.univ, μ a * J.Pmin t a b = μ b) →
          ∀ b ∈ Finset.univ, μ b = π b :=
  J.exists_ergodic_limit closedOn Finset.univ_nonempty fun a _ b _ => reach a b

end TwoState

end Examples
end CRNT
