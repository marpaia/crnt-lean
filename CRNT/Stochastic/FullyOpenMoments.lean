import CRNT.Stochastic.FullyOpenErgodic
import CRNT.Stochastic.MinimalSemigroupMoments

/-!
# Convergence of means in fully open networks

For a fully open network whose original reactions do not increase the number of molecules, the
squared total count `S(n)² = (∑_s n_s)²` has an exponential drift `Q(S²) ≤ −c S² + K`
(`fullyOpen_drift_sq_le`). Hence, by the `f`-norm ergodic theorem, every observable `f = o(S²)`
(in particular every species count) has `E_n[f(X(t))] → E_π[f]` for the unique stationary law
`π` (`fullyOpen_tendsto_mean`).
-/

open Filter
open scoped BigOperators Topology

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The total molecule count. -/
def totalCount (n : S → ℕ) : ℕ := ∑ s, n s

theorem totalCount_jumpNextCount (N : Network S) {n : S → ℕ} {r : N.R} (hen : N.Enabled n r) :
    totalCount (N.jumpNextCount n r) + ∑ s, (N.reaction r).source s =
      totalCount n + ∑ s, (N.reaction r).target s := by
  unfold totalCount jumpNextCount
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by have := hen s; omega

/-- The drift of the squared total count of a fully open network. -/
theorem fullyOpen_drift_sq_le (N : Network S) (κ : RateConstants N.fullyOpen)
    (hmol : ∀ r : N.R, ∑ s, (N.reaction r).target s ≤ ∑ s, (N.reaction r).source s)
    (n : S → ℕ) :
    (N.fullyOpen.jumpSystem κ).drift (fun m => ((totalCount m : ℕ) : ℝ) ^ 2) n ≤
      ∑ s, κ.k (Sum.inr (Sum.inl s)) * (2 * (totalCount n : ℝ) + 1) +
        ∑ s, κ.k (Sum.inr (Sum.inr s)) * (n s : ℝ) * (1 - 2 * (totalCount n : ℝ)) := by
  set T : ℝ := ((totalCount n : ℕ) : ℝ) with hT
  show ∑ r : N.fullyOpen.R, N.fullyOpen.stochasticMassActionRate κ n r *
    (((totalCount (N.fullyOpen.jumpNextCount n r) : ℕ) : ℝ) ^ 2 - T ^ 2) ≤ _
  have hsplit : ∀ g : N.fullyOpen.R → ℝ, ∑ x, g x = ∑ r : N.R, g (Sum.inl r) +
      (∑ s : S, g (Sum.inr (Sum.inl s)) + ∑ s : S, g (Sum.inr (Sum.inr s))) := fun g =>
    (Fintype.sum_sum_type (f := g)).trans (by rw [Fintype.sum_sum_type])
  rw [hsplit]
  have h1 : ∑ r : N.R, N.fullyOpen.stochasticMassActionRate κ n (Sum.inl r) *
      (((totalCount (N.fullyOpen.jumpNextCount n (Sum.inl r)) : ℕ) : ℝ) ^ 2 - T ^ 2) ≤ 0 := by
    refine Finset.sum_nonpos fun r _ => ?_
    by_cases hen : N.fullyOpen.Enabled n (Sum.inl r)
    · refine mul_nonpos_of_nonneg_of_nonpos (N.fullyOpen.stochasticMassActionRate_nonneg κ n _) ?_
      have h := totalCount_jumpNextCount N.fullyOpen hen
      have hm := hmol r
      have hle : totalCount (N.fullyOpen.jumpNextCount n (Sum.inl r)) ≤ totalCount n := by
        have e1 : ∑ s, (N.fullyOpen.reaction (Sum.inl r)).source s =
            ∑ s, (N.reaction r).source s := rfl
        have e2 : ∑ s, (N.fullyOpen.reaction (Sum.inl r)).target s =
            ∑ s, (N.reaction r).target s := rfl
        rw [e1, e2] at h
        omega
      have hle' : ((totalCount (N.fullyOpen.jumpNextCount n (Sum.inl r)) : ℕ) : ℝ) ≤ T := by
        rw [hT]; exact_mod_cast hle
      have h0 : (0 : ℝ) ≤ ((totalCount (N.fullyOpen.jumpNextCount n (Sum.inl r)) : ℕ) : ℝ) :=
        Nat.cast_nonneg _
      nlinarith
    · rw [N.fullyOpen.stochasticMassActionRate_eq_zero_of_not_enabled κ n _ hen, zero_mul]
  have h2 : ∀ s, N.fullyOpen.stochasticMassActionRate κ n (Sum.inr (Sum.inl s)) *
      (((totalCount (N.fullyOpen.jumpNextCount n (Sum.inr (Sum.inl s))) : ℕ) : ℝ) ^ 2 - T ^ 2) =
        κ.k (Sum.inr (Sum.inl s)) * (2 * T + 1) := by
    intro s
    rw [fullyOpen_rate_inflow]
    have hen : N.fullyOpen.Enabled n (Sum.inr (Sum.inl s)) := fun t => by
      show (Complex.zero : Complex S) t ≤ n t
      simp [Complex.zero]
    have h := totalCount_jumpNextCount N.fullyOpen hen
    have e1 : ∑ t, (N.fullyOpen.reaction (Sum.inr (Sum.inl s))).source t = 0 := by
      show ∑ t, (Complex.zero : Complex S) t = 0
      simp [Complex.zero]
    have e2 : ∑ t, (N.fullyOpen.reaction (Sum.inr (Sum.inl s))).target t = 1 := by
      show ∑ t, singletonComplex s t = 1
      simp [singletonComplex]
    rw [e1, e2] at h
    have : ((totalCount (N.fullyOpen.jumpNextCount n (Sum.inr (Sum.inl s))) : ℕ) : ℝ) = T + 1 := by
      rw [hT]; exact_mod_cast (by omega : totalCount (N.fullyOpen.jumpNextCount n
        (Sum.inr (Sum.inl s))) = totalCount n + 1)
    rw [this]; ring
  have h3 : ∀ s, N.fullyOpen.stochasticMassActionRate κ n (Sum.inr (Sum.inr s)) *
      (((totalCount (N.fullyOpen.jumpNextCount n (Sum.inr (Sum.inr s))) : ℕ) : ℝ) ^ 2 - T ^ 2) =
        κ.k (Sum.inr (Sum.inr s)) * (n s : ℝ) * (1 - 2 * T) := by
    intro s
    rw [fullyOpen_rate_outflow]
    by_cases hns : n s = 0
    · simp [hns]
    · have hen : N.fullyOpen.Enabled n (Sum.inr (Sum.inr s)) := fun t => by
        show singletonComplex s t ≤ n t
        simp only [singletonComplex, Pi.single_apply]
        split_ifs with h
        · subst h; omega
        · exact Nat.zero_le _
      have h := totalCount_jumpNextCount N.fullyOpen hen
      have e1 : ∑ t, (N.fullyOpen.reaction (Sum.inr (Sum.inr s))).source t = 1 := by
        show ∑ t, singletonComplex s t = 1
        simp [singletonComplex]
      have e2 : ∑ t, (N.fullyOpen.reaction (Sum.inr (Sum.inr s))).target t = 0 := by
        show ∑ t, (Complex.zero : Complex S) t = 0
        simp [Complex.zero]
      rw [e1, e2] at h
      have hpos : 1 ≤ totalCount n := by
        unfold totalCount
        exact le_trans (by omega) (Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ s))
      have : ((totalCount (N.fullyOpen.jumpNextCount n (Sum.inr (Sum.inr s))) : ℕ) : ℝ) = T - 1 := by
        have h' : totalCount (N.fullyOpen.jumpNextCount n (Sum.inr (Sum.inr s))) + 1 =
            totalCount n := by omega
        rw [hT, ← h']; push_cast; ring
      rw [this]; ring
  simp only [h2, h3] at *
  linarith [h1]

/-- **`f`-norm ergodicity of fully open networks** with non-increasing molecularity: for every
`f ≥ 0` with `f = o(S²)`, `∑_m |P(t)(n, m) − π(m)| f(m) → 0` from every count. -/
theorem fullyOpen_tendsto_fnorm (N : Network S) (κ : RateConstants N.fullyOpen)
    (hmol : ∀ r : N.R, ∑ s, (N.reaction r).target s ≤ ∑ s, (N.reaction r).source s) :
    ∃ π : (S → ℕ) → ℝ, (∀ m, 0 ≤ π m) ∧ HasSum π 1 ∧
      (∀ t, 0 ≤ t → ∀ m, ∑' x, π x * N.fullyOpen.transition κ t x m = π m) ∧
      ∀ f : (S → ℕ) → ℝ, (∀ m, 0 ≤ f m) →
        (∀ ε, 0 < ε → ∃ R, ∀ m, R < ((totalCount m : ℕ) : ℝ) ^ 2 → f m ≤ ε * ((totalCount m : ℕ) : ℝ) ^ 2) →
        ∀ n, Tendsto (fun t => ∑' m, |N.fullyOpen.transition κ t n m - π m| * f m) atTop (𝓝 0) := by
  classical
  set J := N.fullyOpen.jumpSystem κ with hJ
  set V : (S → ℕ) → ℝ := fun m => ((totalCount m : ℕ) : ℝ) ^ 2 with hV
  have hV0 : ∀ m, 0 ≤ V m := fun m => sq_nonneg _
  obtain ⟨c₀, hc₀, hc₀le⟩ : ∃ c : ℝ, 0 < c ∧ ∀ s, c ≤ κ.k (Sum.inr (Sum.inr s)) := by
    by_cases hS : (Finset.univ : Finset S).Nonempty
    · exact ⟨Finset.univ.inf' hS fun s => κ.k (Sum.inr (Sum.inr s)),
        (Finset.lt_inf'_iff _).mpr fun s _ => κ.positive _,
        fun s => Finset.inf'_le _ (Finset.mem_univ s)⟩
    · exact ⟨1, one_pos, fun s => absurd ⟨s, Finset.mem_univ s⟩ hS⟩
  set a := ∑ s, κ.k (Sum.inr (Sum.inl s)) with ha
  set B := ∑ s, κ.k (Sum.inr (Sum.inr s)) with hB
  have ha0 : 0 ≤ a := Finset.sum_nonneg fun s _ => (κ.positive _).le
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun s _ => (κ.positive _).le
  set K := (2 * a + B) ^ 2 / (4 * c₀) + a with hK
  have hK0 : 0 ≤ K := by positivity
  have hdr : ∀ m, J.drift V m ≤ -c₀ * V m + K := by
    intro m
    have h := N.fullyOpen_drift_sq_le κ hmol m
    set T : ℝ := ((totalCount m : ℕ) : ℝ) with hT
    have hT0 : 0 ≤ T := Nat.cast_nonneg _
    have hsum_le : ∑ s, κ.k (Sum.inr (Sum.inr s)) * (m s : ℝ) ≤ B * T := by
      rw [hB, Finset.sum_mul]
      refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ (κ.positive _).le
      rw [hT]; unfold totalCount; push_cast
      exact Finset.single_le_sum (f := fun s => (m s : ℝ)) (fun _ _ => Nat.cast_nonneg _)
        (Finset.mem_univ s)
    have hsum_ge : c₀ * T ≤ ∑ s, κ.k (Sum.inr (Sum.inr s)) * (m s : ℝ) := by
      rw [hT]; unfold totalCount; push_cast; rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right (hc₀le s) (Nat.cast_nonneg _)
    have e1 : ∑ s, κ.k (Sum.inr (Sum.inl s)) * (2 * T + 1) = a * (2 * T + 1) := by
      rw [ha, Finset.sum_mul]
    have e2 : ∑ s, κ.k (Sum.inr (Sum.inr s)) * (m s : ℝ) * (1 - 2 * T) =
        (∑ s, κ.k (Sum.inr (Sum.inr s)) * (m s : ℝ)) * (1 - 2 * T) := by rw [Finset.sum_mul]
    rw [e1, e2] at h
    have hsq : -(c₀ * T ^ 2) + (2 * a + B) * T ≤ (2 * a + B) ^ 2 / (4 * c₀) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (2 * c₀ * T - (2 * a + B))]
    have hV' : V m = T ^ 2 := rfl
    rw [hV']
    nlinarith [mul_le_mul_of_nonneg_left hsum_ge hT0]
  have hfinV : ∀ R : ℝ, {m | V m ≤ R}.Finite := fun R =>
    (finite_linearObservable_le (S := S) (fun _ => (1 : ℝ)) (fun _ => one_pos) R).subset
      fun m hm => by
        simp only [Set.mem_ofPred_eq, hV] at hm ⊢
        have hl : linearObservable (fun _ => (1 : ℝ)) m = ((totalCount m : ℕ) : ℝ) := by
          simp [linearObservable, totalCount]
        rw [hl]
        have h1 : ((totalCount m : ℕ) : ℝ) ≤ ((totalCount m : ℕ) : ℝ) ^ 2 := by
          rcases Nat.eq_zero_or_pos (totalCount m) with h | h
          · simp [h]
          · have : (1 : ℝ) ≤ ((totalCount m : ℕ) : ℝ) := by exact_mod_cast h
            nlinarith
        linarith
  have hstoch : ∀ t, 0 ≤ t → ∀ m, HasSum (fun b => J.Pmin t m b) 1 := fun t ht m =>
    J.hasSum_Pmin_one_of_drift_affine V hV0 hfinV le_rfl hK0
      (fun x => by have := hdr x; have := mul_nonneg hc₀.le (hV0 x); linarith) ht m
  obtain ⟨π, hπ0, hπ1, hinv, -, hfn⟩ := J.tendsto_fnorm_of_drift V hV0 hfinV hc₀ hK0 hdr hstoch
    (E := Set.univ) (fun _ _ _ _ => Set.mem_univ _)
    (fun a _ b _ => N.fullyOpen_reachPos κ a b) (Set.mem_univ (0 : S → ℕ))
  exact ⟨π, hπ0, hπ1, hinv, fun f hf0 hfo n => hfn f hf0 hfo n (Set.mem_univ n)⟩

/-- **Convergence of means** in fully open networks with non-increasing molecularity: from every
count, the mean of every species converges to its stationary mean. -/
theorem fullyOpen_tendsto_mean (N : Network S) (κ : RateConstants N.fullyOpen)
    (hmol : ∀ r : N.R, ∑ s, (N.reaction r).target s ≤ ∑ s, (N.reaction r).source s) :
    ∃ π : (S → ℕ) → ℝ, (∀ m, 0 ≤ π m) ∧ HasSum π 1 ∧
      (∀ t, 0 ≤ t → ∀ m, ∑' x, π x * N.fullyOpen.transition κ t x m = π m) ∧
      ∀ s n, Tendsto (fun t => ∑' m, |N.fullyOpen.transition κ t n m - π m| * (m s : ℝ))
        atTop (𝓝 0) := by
  obtain ⟨π, h0, h1, hinv, hfn⟩ := N.fullyOpen_tendsto_fnorm κ hmol
  refine ⟨π, h0, h1, hinv, fun s n => hfn _ (fun m => Nat.cast_nonneg _) (fun ε hε => ?_) n⟩
  refine ⟨1 / ε ^ 2, fun m hm => ?_⟩
  set T : ℝ := ((totalCount m : ℕ) : ℝ)
  have hT0 : 0 ≤ T := Nat.cast_nonneg _
  have hms : (m s : ℝ) ≤ T := by
    show (m s : ℝ) ≤ ((∑ t, m t : ℕ) : ℝ)
    push_cast
    exact Finset.single_le_sum (f := fun t => (m t : ℝ)) (fun _ _ => Nat.cast_nonneg _)
      (Finset.mem_univ s)
  have hT : 1 / ε < T := by
    have h : (1 / ε) ^ 2 < T ^ 2 := by rw [div_pow, one_pow]; exact hm
    exact lt_of_pow_lt_pow_left₀ 2 hT0 h
  have hεT : 1 ≤ ε * T := by
    rw [div_lt_iff₀ hε] at hT; linarith
  nlinarith

end Network
end CRNT
