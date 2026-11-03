import CRNT.Stochastic.MinimalSemigroupKrylovBogoliubov

/-!
# Ergodicity of stochastic mass action under a linear Lyapunov drift

Let `w > 0` and `V(n) = ∑_s w_s n_s`. If the generator satisfies `QV ≤ −c V + K` with `c > 0`,
the chain does not explode, and from every count `n₀` there is an invariant probability supported
on the counts reachable from `n₀`. For a weakly reversible network the reachable class is
irreducible, so the invariant probability is unique on it, charges every count of it, and the law
of the chain from any count of the class converges to it in total variation
(`foster_lyapunov_ergodic_linear`). No complex balance or deficiency assumption is used.
Instance: `0 → X`, `X → 0` with unit rates (`BirthDeathErgodic.ergodic`).
-/

open Filter
open scoped BigOperators Topology

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

theorem foster_lyapunov_ergodic_linear (N : Network S) (κ : RateConstants N)
    (hWR : N.WeaklyReversible) (w : S → ℝ) (hw : ∀ s, 0 < w s) {c K : ℝ} (hc : 0 < c)
    (hK : 0 ≤ K)
    (hdrift : ∀ n, ∑ r, N.stochasticMassActionRate κ n r * ∑ s, w s * N.reactionVector r s ≤
      -c * linearObservable w n + K) (n₀ : S → ℕ) :
    ∃ π : (S → ℕ) → ℝ, (∀ m, 0 ≤ π m) ∧ HasSum π 1 ∧
      (∀ t, 0 ≤ t → ∀ m, ∑' x, π x * N.transition κ t x m = π m) ∧
      (∀ m, ¬ (N.jumpSystem κ).ReachPos n₀ m → π m = 0) ∧
      (∀ m, (N.jumpSystem κ).ReachPos n₀ m → 0 < π m) ∧
      (∀ n, (N.jumpSystem κ).ReachPos n₀ n →
        Tendsto (fun t => ∑' m, |N.transition κ t n m - π m|) atTop (𝓝 0)) ∧
      ∀ μ : (S → ℕ) → ℝ, (∀ m, 0 ≤ μ m) → (∀ m, ¬ (N.jumpSystem κ).ReachPos n₀ m → μ m = 0) →
        HasSum μ 1 → (∀ t, 0 ≤ t → ∀ m, ∑' x, μ x * N.transition κ t x m = μ m) → μ = π := by
  have hV : ∀ n, 0 ≤ linearObservable w n := fun n =>
    Finset.sum_nonneg fun s _ => mul_nonneg (hw s).le (Nat.cast_nonneg _)
  have hdr : ∀ n, (N.jumpSystem κ).drift (linearObservable w) n ≤
      -(c * linearObservable w n) + K := fun n => by
    rw [jumpSystem_drift_linear]; linarith [hdrift n]
  have hstoch : ∀ t, 0 ≤ t → ∀ n, HasSum (fun m => (N.jumpSystem κ).Pmin t n m) 1 :=
    fun t ht n => (N.jumpSystem κ).hasSum_Pmin_one_of_drift_affine (linearObservable w) hV
      (finite_linearObservable_le w hw) le_rfl hK (fun m => by
        have := hdr m; have := mul_nonneg hc.le (hV m); linarith) ht n
  have hfin : ∀ R : ℝ, {n | c * linearObservable w n ≤ R}.Finite := fun R =>
    (finite_linearObservable_le w hw (R / c)).subset fun n hn => by
      simp only [Set.mem_ofPred_eq] at hn ⊢
      rw [le_div_iff₀ hc]; linarith
  exact (N.jumpSystem κ).foster_lyapunov_ergodic (linearObservable w)
    (fun n => c * linearObservable w n) hV (fun n => mul_nonneg hc.le (hV n)) hfin hK hdr hstoch
    (E := {m | (N.jumpSystem κ).ReachPos n₀ m})
    (fun a ha i hr => (ha : (N.jumpSystem κ).ReachPos n₀ a).tail ⟨i, hr, rfl⟩)
    (fun a ha b hb => (N.reachPos_symm κ hWR ha).trans hb) Relation.ReflTransGen.refl

end Network

namespace Examples
namespace BirthDeathErgodic

open Network

/-- `0 → X`, `X → 0`. -/
abbrev net : Network Unit :=
  ⟨Fin 2, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨0, fun _ => 1⟩ else ⟨fun _ => 1, 0⟩⟩

def κ : RateConstants net := ⟨fun _ => 1, fun _ => one_pos⟩

theorem weaklyReversible : net.WeaklyReversible := by
  intro r
  fin_cases r
  · exact Relation.ReflTransGen.single ⟨1, by simp, by simp⟩
  · exact Relation.ReflTransGen.single ⟨0, by simp, by simp⟩

theorem drift (n : Unit → ℕ) :
    ∑ r, net.stochasticMassActionRate κ n r * ∑ s, (fun _ => (1 : ℝ)) s * net.reactionVector r s ≤
      -1 * linearObservable (fun _ => 1) n + 1 := by
  simp [Fin.sum_univ_two, stochasticMassActionRate, κ, Network.reactionVector, Reaction.vector,
    linearObservable]

/-- **Ergodicity of the birth–death chain** from the empty state. -/
theorem ergodic : ∃ π : (Unit → ℕ) → ℝ, (∀ m, 0 ≤ π m) ∧ HasSum π 1 ∧
    (∀ t, 0 ≤ t → ∀ m, ∑' x, π x * net.transition κ t x m = π m) ∧
    ∀ n, (net.jumpSystem κ).ReachPos 0 n →
      Filter.Tendsto (fun t => ∑' m, |net.transition κ t n m - π m|) Filter.atTop (nhds 0) := by
  obtain ⟨π, h0, h1, hinv, -, -, hconv, -⟩ := net.foster_lyapunov_ergodic_linear κ
    weaklyReversible (fun _ => 1) (fun _ => one_pos) one_pos zero_le_one drift 0
  exact ⟨π, h0, h1, hinv, hconv⟩

end BirthDeathErgodic
end Examples

end CRNT
