import CRNT.Stochastic.NetworkFosterErgodic
import CRNT.Open.Augmentation

/-!
# Ergodicity of fully open networks with non-increasing molecularity

For the fully open extension of a network (inflow `0 → X` and outflow `X → 0` for every species)
in which every original reaction `y → y'` has `|y'| ≤ |y|` molecules, the stochastic mass-action
chain is ergodic on the whole count lattice, for every choice of positive rates: there is a unique
stationary distribution, it charges every count, and the law of the chain converges to it in
total variation from every initial count (`fullyOpen_ergodic`).

Proof: the flows connect every count to every other (`fullyOpen_reachPos`), and the total
molecule count `V(n) = ∑_s n_s` has drift `≤ ∑_s κ_in(s) − min_s κ_out(s) · V(n)`
(`fullyOpen_drift_le`), so the Foster–Lyapunov ergodic theorem applies.
-/

open Filter
open scoped BigOperators Topology

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

theorem fullyOpen_rate_inflow (N : Network S) (κ : RateConstants N.fullyOpen) (s : S)
    (n : S → ℕ) : N.fullyOpen.stochasticMassActionRate κ n (Sum.inr (Sum.inl s)) =
      κ.k (Sum.inr (Sum.inl s)) := by
  simp [stochasticMassActionRate, inflowReaction, Complex.zero]

theorem fullyOpen_rate_outflow (N : Network S) (κ : RateConstants N.fullyOpen) (s : S)
    (n : S → ℕ) : N.fullyOpen.stochasticMassActionRate κ n (Sum.inr (Sum.inr s)) =
      κ.k (Sum.inr (Sum.inr s)) * n s := by
  simp only [stochasticMassActionRate, fullyOpen_reaction_outflow, outflowReaction,
    singletonComplex]
  rw [Finset.prod_eq_single s (fun t _ ht => by simp [Pi.single_apply, ht]) (by simp)]
  simp

/-- From any count, every count is reachable in a fully open network. -/
theorem fullyOpen_reachPos (N : Network S) (κ : RateConstants N.fullyOpen) (n m : S → ℕ) :
    (N.fullyOpen.jumpSystem κ).ReachPos n m := by
  have hdec : ∀ (x : S → ℕ) (s : S), 0 < x s →
      x = fun t => (x t - (if t = s then 1 else 0)) + (if t = s then 1 else 0) := fun x s hs => by
    funext t
    split_ifs with h
    · subst h; omega
    · omega
  have hsum : ∀ (x : S → ℕ) (s : S), 0 < x s →
      ∑ t, x t = ∑ t, (x t - (if t = s then 1 else 0)) + 1 := fun x s hs => by
    conv_lhs => rw [hdec x s hs]
    rw [Finset.sum_add_distrib]
    simp
  have hpos : ∀ x : S → ℕ, x ≠ 0 → ∃ s, 0 < x s := fun x hx => by
    by_contra h
    push Not at h
    exact hx (funext fun s => Nat.le_zero.mp (h s))
  -- down to the empty state by outflows
  have hdown : ∀ k (x : S → ℕ), ∑ t, x t = k → (N.fullyOpen.jumpSystem κ).ReachPos x 0 := by
    intro k
    induction k with
    | zero =>
        intro x hx
        have : x = 0 := funext fun s => by
          have := (Finset.sum_eq_zero_iff.mp hx) s (Finset.mem_univ s)
          simpa using this
        subst this; exact Relation.ReflTransGen.refl
    | succ k ih =>
        intro x hx
        have hx0 : x ≠ 0 := by rintro rfl; simp at hx
        obtain ⟨s, hs⟩ := hpos x hx0
        refine Relation.ReflTransGen.head ⟨Sum.inr (Sum.inr s), ?_, ?_⟩
          (ih (fun t => x t - (if t = s then 1 else 0)) (by have := hsum x s hs; omega))
        · show 0 < N.fullyOpen.stochasticMassActionRate κ x (Sum.inr (Sum.inr s))
          rw [fullyOpen_rate_outflow]
          exact mul_pos (κ.positive _) (by exact_mod_cast hs)
        · show _ = N.fullyOpen.jumpNextCount x (Sum.inr (Sum.inr s))
          funext t
          simp [jumpNextCount, outflowReaction, singletonComplex, Pi.single_apply, Complex.zero]
  -- up from the empty state by inflows
  have hup : ∀ k (x : S → ℕ), ∑ t, x t = k → (N.fullyOpen.jumpSystem κ).ReachPos 0 x := by
    intro k
    induction k with
    | zero =>
        intro x hx
        have : x = 0 := funext fun s => by
          have := (Finset.sum_eq_zero_iff.mp hx) s (Finset.mem_univ s)
          simpa using this
        subst this; exact Relation.ReflTransGen.refl
    | succ k ih =>
        intro x hx
        have hx0 : x ≠ 0 := by rintro rfl; simp at hx
        obtain ⟨s, hs⟩ := hpos x hx0
        refine (ih (fun t => x t - (if t = s then 1 else 0)) (by have := hsum x s hs; omega)).tail
          ⟨Sum.inr (Sum.inl s), ?_, ?_⟩
        · show 0 < N.fullyOpen.stochasticMassActionRate κ _ (Sum.inr (Sum.inl s))
          rw [fullyOpen_rate_inflow]; exact κ.positive _
        · show x = N.fullyOpen.jumpNextCount _ (Sum.inr (Sum.inl s))
          conv_lhs => rw [hdec x s hs]
          funext t
          simp [jumpNextCount, inflowReaction, singletonComplex, Pi.single_apply, Complex.zero]
  exact (hdown _ n rfl).trans (hup _ m rfl)

/-- The drift of the total molecule count in a fully open network whose original reactions do not
increase the number of molecules. -/
theorem fullyOpen_drift_le (N : Network S) (κ : RateConstants N.fullyOpen)
    (hmol : ∀ r : N.R, ∑ s, (N.reaction r).target s ≤ ∑ s, (N.reaction r).source s)
    (n : S → ℕ) :
    (N.fullyOpen.jumpSystem κ).drift (linearObservable fun _ => 1) n ≤
      ∑ s, κ.k (Sum.inr (Sum.inl s)) - ∑ s, κ.k (Sum.inr (Sum.inr s)) * n s := by
  rw [jumpSystem_drift_linear]
  simp only [one_mul]
  have hsplit : ∀ g : N.fullyOpen.R → ℝ, ∑ x, g x = ∑ r : N.R, g (Sum.inl r) +
      (∑ s : S, g (Sum.inr (Sum.inl s)) + ∑ s : S, g (Sum.inr (Sum.inr s))) := fun g =>
    (Fintype.sum_sum_type (f := g)).trans (by rw [Fintype.sum_sum_type])
  rw [hsplit]
  have h1 : ∑ r : N.R, N.fullyOpen.stochasticMassActionRate κ n (Sum.inl r) *
      ∑ s, N.fullyOpen.reactionVector (Sum.inl r) s ≤ 0 := by
    refine Finset.sum_nonpos fun r _ => mul_nonpos_of_nonneg_of_nonpos
      (N.fullyOpen.stochasticMassActionRate_nonneg κ n _) ?_
    have e : ∑ s, N.fullyOpen.reactionVector (Sum.inl r) s =
        ∑ s, (((N.reaction r).target s : ℝ) - ((N.reaction r).source s : ℝ)) := rfl
    rw [e, Finset.sum_sub_distrib]
    have h : ((∑ s, (N.reaction r).target s : ℕ) : ℝ) ≤ ((∑ s, (N.reaction r).source s : ℕ) : ℝ) :=
      by exact_mod_cast hmol r
    push_cast at h
    linarith
  have h2 : ∑ s, N.fullyOpen.stochasticMassActionRate κ n (Sum.inr (Sum.inl s)) *
      ∑ t, N.fullyOpen.reactionVector (Sum.inr (Sum.inl s)) t = ∑ s, κ.k (Sum.inr (Sum.inl s)) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [fullyOpen_rate_inflow]
    have e : ∑ t, N.fullyOpen.reactionVector (Sum.inr (Sum.inl s)) t =
        ∑ t, (((singletonComplex s t : ℕ) : ℝ) - ((Complex.zero : Complex S) t : ℝ)) := rfl
    rw [e]
    simp [singletonComplex, Complex.zero, Pi.single_apply, apply_ite (Nat.cast : ℕ → ℝ)]
  have h3 : ∑ s, N.fullyOpen.stochasticMassActionRate κ n (Sum.inr (Sum.inr s)) *
      ∑ t, N.fullyOpen.reactionVector (Sum.inr (Sum.inr s)) t =
        -∑ s, κ.k (Sum.inr (Sum.inr s)) * n s := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [fullyOpen_rate_outflow]
    have e : ∑ t, N.fullyOpen.reactionVector (Sum.inr (Sum.inr s)) t =
        ∑ t, (((Complex.zero : Complex S) t : ℝ) - ((singletonComplex s t : ℕ) : ℝ)) := rfl
    rw [e]
    simp [singletonComplex, Complex.zero, Pi.single_apply, apply_ite (Nat.cast : ℕ → ℝ)]
  linarith

/-- **Ergodicity of fully open networks with non-increasing molecularity.** -/
theorem fullyOpen_ergodic (N : Network S) (κ : RateConstants N.fullyOpen)
    (hmol : ∀ r : N.R, ∑ s, (N.reaction r).target s ≤ ∑ s, (N.reaction r).source s) :
    ∃ π : (S → ℕ) → ℝ, (∀ m, 0 < π m) ∧ HasSum π 1 ∧
      (∀ t, 0 ≤ t → ∀ m, ∑' x, π x * N.fullyOpen.transition κ t x m = π m) ∧
      (∀ n, Tendsto (fun t => ∑' m, |N.fullyOpen.transition κ t n m - π m|) atTop (𝓝 0)) ∧
      ∀ μ : (S → ℕ) → ℝ, (∀ m, 0 ≤ μ m) → HasSum μ 1 →
        (∀ t, 0 ≤ t → ∀ m, ∑' x, μ x * N.fullyOpen.transition κ t x m = μ m) → μ = π := by
  classical
  set V : (S → ℕ) → ℝ := linearObservable fun _ => 1 with hVdef
  set K := ∑ s, κ.k (Sum.inr (Sum.inl s)) with hKdef
  have hK : 0 ≤ K := Finset.sum_nonneg fun s _ => (κ.positive _).le
  -- the minimal outflow rate
  obtain ⟨c, hc, hcle⟩ : ∃ c : ℝ, 0 < c ∧ ∀ s, c ≤ κ.k (Sum.inr (Sum.inr s)) := by
    by_cases hS : (Finset.univ : Finset S).Nonempty
    · exact ⟨Finset.univ.inf' hS fun s => κ.k (Sum.inr (Sum.inr s)),
        (Finset.lt_inf'_iff _).mpr fun s _ => κ.positive _,
        fun s => Finset.inf'_le _ (Finset.mem_univ s)⟩
    · exact ⟨1, one_pos, fun s => absurd ⟨s, Finset.mem_univ s⟩ hS⟩
  have hV : ∀ n, 0 ≤ V n := fun n => Finset.sum_nonneg fun s _ => by simp
  have hdr : ∀ n, (N.fullyOpen.jumpSystem κ).drift V n ≤ -(c * V n) + K := by
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
  have hfin : ∀ R : ℝ, {n | c * V n ≤ R}.Finite := fun R =>
    (hfinV (R / c)).subset fun n hn => by
      simp only [Set.mem_ofPred_eq] at hn ⊢
      rw [le_div_iff₀ hc]; linarith
  obtain ⟨π, hπ0, hπ1, hinv, -, hpos, hconv, huniq⟩ :=
    (N.fullyOpen.jumpSystem κ).foster_lyapunov_ergodic V (fun n => c * V n) hV
      (fun n => mul_nonneg hc.le (hV n)) hfin hK hdr hstoch (E := Set.univ)
      (fun _ _ _ _ => Set.mem_univ _) (fun a _ b _ => N.fullyOpen_reachPos κ a b)
      (Set.mem_univ (0 : S → ℕ))
  exact ⟨π, fun m => hpos m (Set.mem_univ m), hπ1, hinv, fun n => hconv n (Set.mem_univ n),
    fun μ hμ0 hμ1 hμinv => huniq μ hμ0 (fun m hm => absurd (Set.mem_univ m) hm) hμ1 hμinv⟩

end Network
end CRNT
