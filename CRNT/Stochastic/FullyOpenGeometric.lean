import CRNT.Stochastic.HarrisTheorem
import CRNT.Stochastic.FullyOpenErgodic

/-!
# Geometric ergodicity of fully open networks

For the fully open extension of a network whose original reactions do not increase the number of
molecules, for every choice of rates, the law of the chain converges to the stationary law
exponentially fast in the count-weighted total variation norm
`∑_m |P(t)(n, m) − π(m)| (1 + β |m|)`, uniformly in the initial count up to a factor `1 + |n|`
(`fullyOpen_geometric_ergodic`).
-/

open Filter
open scoped BigOperators Topology

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

theorem fullyOpen_geometric_ergodic (N : Network S) (κ : RateConstants N.fullyOpen)
    (hmol : ∀ r : N.R, ∑ s, (N.reaction r).target s ≤ ∑ s, (N.reaction r).source s) :
    ∃ π : (S → ℕ) → ℝ, (∀ m, 0 ≤ π m) ∧ HasSum π 1 ∧
      (∀ t, 0 ≤ t → ∀ m, ∑' x, π x * N.fullyOpen.transition κ t x m = π m) ∧
      ∃ β : ℝ, 0 < β ∧ ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∃ C₀ : ℝ, ∀ n, ∀ t, 0 ≤ t →
        ∑' m, |N.fullyOpen.transition κ t n m - π m| *
            (1 + β * linearObservable (fun _ => 1) m) ≤
          C₀ * (1 + linearObservable (fun _ => 1) n) * ρ ^ ⌊t⌋₊ := by
  classical
  set V : (S → ℕ) → ℝ := linearObservable fun _ => 1 with hVdef
  set K := ∑ s, κ.k (Sum.inr (Sum.inl s)) with hKdef
  have hK : 0 ≤ K := Finset.sum_nonneg fun s _ => (κ.positive _).le
  obtain ⟨c, hc, hcle⟩ : ∃ c : ℝ, 0 < c ∧ ∀ s, c ≤ κ.k (Sum.inr (Sum.inr s)) := by
    by_cases hS : (Finset.univ : Finset S).Nonempty
    · exact ⟨Finset.univ.inf' hS fun s => κ.k (Sum.inr (Sum.inr s)),
        (Finset.lt_inf'_iff _).mpr fun s _ => κ.positive _,
        fun s => Finset.inf'_le _ (Finset.mem_univ s)⟩
    · exact ⟨1, one_pos, fun s => absurd ⟨s, Finset.mem_univ s⟩ hS⟩
  have hV : ∀ n, 0 ≤ V n := fun n => Finset.sum_nonneg fun s _ => by simp
  have hdr : ∀ n, (N.fullyOpen.jumpSystem κ).drift V n ≤ -c * V n + K := by
    intro n
    have h := N.fullyOpen_drift_le κ hmol n
    have h2 : c * V n ≤ ∑ s, κ.k (Sum.inr (Sum.inr s)) * n s := by
      simp only [hVdef, linearObservable, one_mul, Finset.mul_sum]
      exact Finset.sum_le_sum fun s _ =>
        mul_le_mul_of_nonneg_right (hcle s) (Nat.cast_nonneg _)
    linarith
  have hfinV := finite_linearObservable_le (S := S) (fun _ => (1 : ℝ)) fun _ => one_pos
  have hstoch : ∀ t, 0 ≤ t → ∀ n, HasSum (fun m => (N.fullyOpen.jumpSystem κ).Pmin t n m) 1 :=
    fun t ht n => (N.fullyOpen.jumpSystem κ).hasSum_Pmin_one_of_drift_affine V hV hfinV le_rfl hK
      (fun m => by have := hdr m; have := mul_nonneg hc.le (hV m); linarith) ht n
  exact (N.fullyOpen.jumpSystem κ).geometric_ergodic V hV hfinV hc hK hdr hstoch
    fun a b => N.fullyOpen_reachPos κ a b

end Network
end CRNT
