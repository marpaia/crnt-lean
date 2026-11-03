import CRNT.Stochastic.MinimalSemigroupExpect
import CRNT.Stochastic.JahnkeHuisinga
import CRNT.Stochastic.FullyOpenMoments
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.ODE.Gronwall

/-!
# Means of monomolecular networks solve the mass-action equation

For a monomolecular network (every source and target has at most one molecule), the stochastic
propensities equal the deterministic mass-action rates at the counts
(`stochasticRate_eq_massActionRate`), so the generator maps each coordinate to the corresponding
component of the mass-action vector field (`drift_coord`). With the Lyapunov function
`W = (1 + |m|)^k` (`drift_powTotal_le`) the forward equation for expectations applies, and the
vector of means `E_n[X(t)]` solves the mass-action equation. Hence it equals the deterministic
solution started at `n`, for every initial count (`monomolecular_mean`).
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology NNReal

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The counts as concentrations. -/
def castCount (m : S → ℕ) : Concentration S := fun s => (m s : ℝ)

/-- The total count as a real number. -/
def tot (m : S → ℕ) : ℝ := ∑ s, (m s : ℝ)

theorem tot_nonneg (m : S → ℕ) : 0 ≤ tot m := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

theorem coord_le_tot (m : S → ℕ) (s : S) : (m s : ℝ) ≤ tot m :=
  Finset.single_le_sum (f := fun s => (m s : ℝ)) (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ s)

/-- Monomolecular propensities equal the mass-action rates at the counts. -/
theorem stochasticRate_eq_massActionRate (N : Network S) (κ : RateConstants N)
    (hmono : N.IsMonomolecular) (m : S → ℕ) (r : N.R) :
    N.stochasticMassActionRate κ m r = N.massActionRate κ r (castCount m) := by
  unfold stochasticMassActionRate massActionRate Complex.massActionMonomial castCount
  congr 1
  rcases complex_of_sum_le_one (hmono r).1 with h0 | ⟨j, hj, hz⟩
  · simp [h0]
  · rw [Finset.prod_eq_single j (fun s _ hs => by simp [hz s hs]) (by simp),
      Finset.prod_eq_single j (fun s _ hs => by simp [hz s hs]) (by simp), hj]
    simp

/-- Monomolecular propensities grow at most linearly. -/
theorem stochasticRate_le (N : Network S) (κ : RateConstants N) (hmono : N.IsMonomolecular)
    (m : S → ℕ) (r : N.R) : N.stochasticMassActionRate κ m r ≤ κ.k r * (1 + tot m) := by
  rw [stochasticRate_eq_massActionRate N κ hmono]
  unfold massActionRate Complex.massActionMonomial castCount
  refine mul_le_mul_of_nonneg_left ?_ (κ.positive r).le
  rcases complex_of_sum_le_one (hmono r).1 with h0 | ⟨j, hj, hz⟩
  · simp [h0]; linarith [tot_nonneg m]
  · rw [Finset.prod_eq_single j (fun s _ hs => by simp [hz s hs]) (by simp), hj, pow_one]
    linarith [coord_le_tot m j]

/-- The generator maps a coordinate to the mass-action vector field. -/
theorem drift_coord (N : Network S) (κ : RateConstants N) (hmono : N.IsMonomolecular)
    (s : S) (m : S → ℕ) :
    (N.jumpSystem κ).drift (fun b => (b s : ℝ)) m = N.massActionVectorField κ (castCount m) s := by
  have hlin : (fun b : S → ℕ => (b s : ℝ)) = linearObservable fun t => if t = s then 1 else 0 := by
    funext b; simp [linearObservable]
  rw [hlin, jumpSystem_drift_linear, massActionVectorField_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [stochasticRate_eq_massActionRate N κ hmono]
  simp

theorem tot_jumpNextCount (N : Network S) {m : S → ℕ} {r : N.R} (hen : N.Enabled m r) :
    tot (N.jumpNextCount m r) =
      tot m - ∑ s, ((N.reaction r).source s : ℝ) + ∑ s, ((N.reaction r).target s : ℝ) := by
  unfold tot jumpNextCount
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Nat.cast_add, Nat.cast_sub (hen s)]

/-- **Drift of `(1 + |m|)^k`** for monomolecular networks: only zero-order reactions raise the total
count, and they fire at constant rate. -/
theorem drift_powTotal_le (N : Network S) (κ : RateConstants N) (hmono : N.IsMonomolecular)
    (k : ℕ) (m : S → ℕ) :
    (N.jumpSystem κ).drift (fun b => (1 + tot b) ^ k) m ≤
      (2 ^ k * ∑ r, κ.k r) * (1 + tot m) ^ k := by
  have hT := tot_nonneg m
  have hW0 : 0 ≤ (1 + tot m) ^ k := by positivity
  show ∑ r : N.R, N.stochasticMassActionRate κ m r *
      ((1 + tot (N.jumpNextCount m r)) ^ k - (1 + tot m) ^ k) ≤ _
  rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ => ?_
  have hR : 0 ≤ 2 ^ k * (κ.k r * (1 + tot m) ^ k) := by
    have := (κ.positive r).le; positivity
  by_cases hen : N.Enabled m r
  · have htot := tot_jumpNextCount N hen
    have hsrc := (hmono r).1
    have htgt := (hmono r).2
    have htgt' : ∑ s, ((N.reaction r).target s : ℝ) ≤ 1 := by exact_mod_cast htgt
    rcases Nat.lt_or_ge (∑ s, (N.reaction r).source s) 1 with h0 | h1
    · -- zero-order reaction
      have hz : ∀ s, (N.reaction r).source s = 0 := fun s => by
        have : (N.reaction r).source s ≤ ∑ s, (N.reaction r).source s :=
          Finset.single_le_sum (f := fun s => (N.reaction r).source s) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ s)
        omega
      have hzR : ∑ s, ((N.reaction r).source s : ℝ) = 0 := by simp [hz]
      rw [stochasticMassActionRate_of_source_zero N κ hz]
      have hnext : 1 + tot (N.jumpNextCount m r) ≤ 2 * (1 + tot m) := by
        rw [htot, hzR]; linarith
      have hnext0 : 0 ≤ 1 + tot (N.jumpNextCount m r) := by
        have := tot_nonneg (N.jumpNextCount m r); linarith
      have hpow : (1 + tot (N.jumpNextCount m r)) ^ k ≤ 2 ^ k * (1 + tot m) ^ k := by
        rw [← mul_pow]; exact pow_le_pow_left₀ hnext0 hnext k
      have := (κ.positive r).le
      nlinarith
    · -- the total count does not increase
      have h1R : (1 : ℝ) ≤ ∑ s, ((N.reaction r).source s : ℝ) := by exact_mod_cast h1
      have hle : 1 + tot (N.jumpNextCount m r) ≤ 1 + tot m := by rw [htot]; linarith
      have hnext0 : 0 ≤ 1 + tot (N.jumpNextCount m r) := by
        have := tot_nonneg (N.jumpNextCount m r); linarith
      have hpow : (1 + tot (N.jumpNextCount m r)) ^ k ≤ (1 + tot m) ^ k :=
        pow_le_pow_left₀ hnext0 hle k
      have := N.stochasticMassActionRate_nonneg κ m r
      nlinarith
  · rw [N.stochasticMassActionRate_eq_zero_of_not_enabled κ m r hen, zero_mul]
    exact hR

/-- `∑_{m ∈ ℕ^S} ∏_s (1 + m_s)^{−2} < ∞`. -/
theorem summable_prod_inv_sq :
    Summable fun m : S → ℕ => ∏ s, ((1 + (m s : ℝ)) ^ 2)⁻¹ := by
  set f : ℕ → ℝ := fun n => ((1 + (n : ℝ)) ^ 2)⁻¹ with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => by simp only [hf]; positivity
  have hfs : Summable f := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2))
    refine h.congr fun n => ?_
    simp only [hf]; push_cast; ring
  refine summable_of_sum_le (c := (∑' n, f n) ^ Fintype.card S)
    (fun m => Finset.prod_nonneg fun s _ => hf0 _) fun F => ?_
  set M := F.sup (fun m => ∑ s, m s) + 1 with hM
  have hsub : F ⊆ Fintype.piFinset fun _ : S => Finset.range M := by
    intro m hm
    rw [Fintype.mem_piFinset]
    intro s
    rw [Finset.mem_range]
    have h1 : m s ≤ ∑ s, m s := Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ s)
    have h2 : ∑ s, m s ≤ F.sup (fun m => ∑ s, m s) := Finset.le_sup (f := fun m => ∑ s, m s) hm
    omega
  calc ∑ m ∈ F, ∏ s, f (m s)
      ≤ ∑ m ∈ Fintype.piFinset (fun _ : S => Finset.range M), ∏ s, f (m s) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ =>
          Finset.prod_nonneg fun s _ => hf0 _
    _ = ∏ _s : S, ∑ n ∈ Finset.range M, f n := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ _s : S, ∑' n, f n :=
        Finset.prod_le_prod₀ (fun _ _ => Finset.sum_nonneg fun n _ => hf0 n)
          fun _ _ => hfs.sum_le_tsum _ fun n _ => hf0 n
    _ = (∑' n, f n) ^ Fintype.card S := by rw [Finset.prod_const, Finset.card_univ]

/-- The domination needed by the forward equation for the coordinate observables, with
`W = (1 + |m|)^{2|S| + 2}`. -/
theorem summable_coord_bound (N : Network S) (κ : RateConstants N) (hmono : N.IsMonomolecular)
    (s : S) :
    Summable fun x : S → ℕ =>
      ((1 + |(x s : ℝ)|) * (1 + (N.jumpSystem κ).q x) +
        ∑ i, (N.jumpSystem κ).rate i x * |(((N.jumpSystem κ).next i x) s : ℝ)|) /
          (1 + tot x) ^ (2 * Fintype.card S + 2) := by
  set K := ∑ r, κ.k r with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun r _ => (κ.positive r).le
  refine Summable.of_nonneg_of_le (fun x => ?_) (fun x => ?_)
    ((summable_prod_inv_sq (S := S)).mul_left (1 + 2 * K))
  · refine div_nonneg (add_nonneg (mul_nonneg (by positivity) ?_) (Finset.sum_nonneg fun i _ =>
      mul_nonneg ((N.jumpSystem κ).rate_nonneg i x) (abs_nonneg _))) (by
        have := tot_nonneg x; positivity)
    have := (N.jumpSystem κ).q_nonneg x; linarith
  · set T := tot x with hTdef
    have hT := tot_nonneg x
    have hq : (N.jumpSystem κ).q x ≤ K * (1 + T) := by
      show ∑ r, N.stochasticMassActionRate κ x r ≤ _
      rw [hK, Finset.sum_mul]
      exact Finset.sum_le_sum fun r _ => stochasticRate_le N κ hmono x r
    have hnext : ∀ r, |((N.jumpNextCount x r) s : ℝ)| ≤ 1 + T := by
      intro r
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      have h1 : (N.jumpNextCount x r) s ≤ x s + 1 := by
        have ht : (N.reaction r).target s ≤ 1 :=
          le_trans (Finset.single_le_sum (f := fun s => (N.reaction r).target s)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)) (hmono r).2
        unfold jumpNextCount; omega
      have h2 : ((N.jumpNextCount x r) s : ℝ) ≤ (x s : ℝ) + 1 := by exact_mod_cast h1
      linarith [coord_le_tot x s]
    have hsum : ∑ i, (N.jumpSystem κ).rate i x * |(((N.jumpSystem κ).next i x) s : ℝ)| ≤
        K * (1 + T) ^ 2 := by
      show ∑ r, N.stochasticMassActionRate κ x r * |((N.jumpNextCount x r) s : ℝ)| ≤ _
      rw [hK, Finset.sum_mul]
      refine Finset.sum_le_sum fun r _ => ?_
      calc N.stochasticMassActionRate κ x r * |((N.jumpNextCount x r) s : ℝ)|
          ≤ (κ.k r * (1 + T)) * (1 + T) :=
            mul_le_mul (stochasticRate_le N κ hmono x r) (hnext r) (abs_nonneg _)
              (by have := (κ.positive r).le; positivity)
        _ = κ.k r * (1 + T) ^ 2 := by ring
    have hxs : |(x s : ℝ)| ≤ T := by rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact coord_le_tot x s
    have hnum : (1 + |(x s : ℝ)|) * (1 + (N.jumpSystem κ).q x) +
        ∑ i, (N.jumpSystem κ).rate i x * |(((N.jumpSystem κ).next i x) s : ℝ)| ≤
          (1 + 2 * K) * (1 + T) ^ 2 := by
      have h1 : (1 + |(x s : ℝ)|) * (1 + (N.jumpSystem κ).q x) ≤ (1 + T) * (1 + K * (1 + T)) :=
        mul_le_mul (by linarith) (by linarith) (by linarith [(N.jumpSystem κ).q_nonneg x])
          (by linarith)
      nlinarith
    -- the product bound
    set d := Fintype.card S
    have hP0 : 0 < ∏ t, (1 + (x t : ℝ)) ^ 2 := Finset.prod_pos fun t _ => by positivity
    have hPle : ∏ t, (1 + (x t : ℝ)) ^ 2 ≤ ((1 + T) ^ 2) ^ d :=
      calc ∏ t, (1 + (x t : ℝ)) ^ 2 ≤ ∏ _t : S, (1 + T) ^ 2 :=
            Finset.prod_le_prod₀ (fun t _ => by positivity) fun t _ =>
              pow_le_pow_left₀ (by positivity) (by linarith [coord_le_tot x t]) 2
        _ = ((1 + T) ^ 2) ^ d := by rw [Finset.prod_const, Finset.card_univ]
    have hinv : ∏ t, ((1 + (x t : ℝ)) ^ 2)⁻¹ = (∏ t, (1 + (x t : ℝ)) ^ 2)⁻¹ :=
      Finset.prod_inv_distrib _
    rw [hinv]
    have hW : (1 + T) ^ (2 * d + 2) = (1 + T) ^ 2 * ((1 + T) ^ 2) ^ d := by
      rw [← pow_mul, ← pow_add]; ring_nf
    rw [hW, div_le_iff₀ (by positivity)]
    have hT2 : 0 < (1 + T) ^ 2 := by positivity
    have hTd : 0 < ((1 + T) ^ 2) ^ d := by positivity
    calc _ ≤ (1 + 2 * K) * (1 + T) ^ 2 := hnum
      _ = (1 + 2 * K) * (1 + T) ^ 2 * (((1 + T) ^ 2) ^ d * (((1 + T) ^ 2) ^ d)⁻¹) := by
          rw [mul_inv_cancel₀ hTd.ne', mul_one]
      _ ≤ (1 + 2 * K) * (∏ t, (1 + (x t : ℝ)) ^ 2)⁻¹ * ((1 + T) ^ 2 * ((1 + T) ^ 2) ^ d) := by
          have h1 : (((1 + T) ^ 2) ^ d)⁻¹ ≤ (∏ t, (1 + (x t : ℝ)) ^ 2)⁻¹ :=
            inv_anti₀ hP0 hPle
          have h2 : 0 ≤ 1 + 2 * K := by linarith
          calc (1 + 2 * K) * (1 + T) ^ 2 * (((1 + T) ^ 2) ^ d * (((1 + T) ^ 2) ^ d)⁻¹)
              = (1 + 2 * K) * (((1 + T) ^ 2) ^ d)⁻¹ * ((1 + T) ^ 2 * ((1 + T) ^ 2) ^ d) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h2) (by positivity)

/-- Monomolecular mass-action rates are constant or a constant times one coordinate. -/
theorem massActionRate_cases (N : Network S) (κ : RateConstants N) (hmono : N.IsMonomolecular)
    (r : N.R) :
    (∀ z, N.massActionRate κ r z = κ.k r) ∨ ∃ j, ∀ z, N.massActionRate κ r z = κ.k r * z j := by
  unfold massActionRate Complex.massActionMonomial
  rcases complex_of_sum_le_one (hmono r).1 with h0 | ⟨j, hj, hz⟩
  · exact Or.inl fun z => by simp [h0]
  · refine Or.inr ⟨j, fun z => ?_⟩
    rw [Finset.prod_eq_single j (fun s _ hs => by simp [hz s hs]) (by simp), hj, pow_one]

/-- The mass-action vector field of a monomolecular network is Lipschitz. -/
theorem lipschitz_massActionVectorField (N : Network S) (κ : RateConstants N)
    (hmono : N.IsMonomolecular) :
    ∃ L : ℝ≥0, LipschitzWith L (N.massActionVectorField κ) := by
  refine ⟨⟨∑ r, κ.k r * ‖N.reactionVector r‖, Finset.sum_nonneg fun r _ =>
    mul_nonneg (κ.positive r).le (norm_nonneg _)⟩, LipschitzWith.of_dist_le_mul fun z w => ?_⟩
  have hF : ∀ u, N.massActionVectorField κ u = ∑ r, N.massActionRate κ r u • N.reactionVector r :=
    fun u => by funext s; simp [Finset.sum_apply]
  rw [dist_eq_norm, dist_eq_norm, hF, hF, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  show _ ≤ (∑ r, κ.k r * ‖N.reactionVector r‖) * ‖z - w‖
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun r _ => ?_
  rw [← sub_smul, norm_smul, Real.norm_eq_abs]
  have hrate : |N.massActionRate κ r z - N.massActionRate κ r w| ≤ κ.k r * ‖z - w‖ := by
    rcases massActionRate_cases N κ hmono r with h0 | ⟨j, hj⟩
    · rw [h0, h0, sub_self, abs_zero]; exact mul_nonneg (κ.positive r).le (norm_nonneg _)
    · rw [hj, hj, ← mul_sub, abs_mul, abs_of_pos (κ.positive r)]
      refine mul_le_mul_of_nonneg_left ?_ (κ.positive r).le
      have := norm_le_pi_norm (z - w) j
      rwa [Real.norm_eq_abs, Pi.sub_apply] at this
  calc |N.massActionRate κ r z - N.massActionRate κ r w| * ‖N.reactionVector r‖
      ≤ κ.k r * ‖z - w‖ * ‖N.reactionVector r‖ :=
        mul_le_mul_of_nonneg_right hrate (norm_nonneg _)
    _ = κ.k r * ‖N.reactionVector r‖ * ‖z - w‖ := by ring

/-- **The means of a monomolecular network solve the mass-action equation.** From every initial
count `n`, `E_n[X_s(t)] = x_s(t)` for the solution `x` of `ẋ = f(x)` with `x(0) = n`. -/
theorem monomolecular_mean (N : Network S) (κ : RateConstants N) (hmono : N.IsMonomolecular)
    (n : S → ℕ) (x : ℝ → Concentration S) (hx0 : x 0 = castCount n)
    (hxc : ContinuousOn x (Ici 0))
    (hx : ∀ t, 0 < t → HasDerivAt x (N.massActionVectorField κ (x t)) t)
    {t : ℝ} (ht : 0 ≤ t) (s : S) :
    ∑' m, N.transition κ t n m * (m s : ℝ) = x t s := by
  classical
  set k := 2 * Fintype.card S + 2 with hk
  set W : (S → ℕ) → ℝ := fun b => (1 + tot b) ^ k with hW
  have hbase : ∀ b : S → ℕ, 1 ≤ 1 + tot b := fun b => by linarith [tot_nonneg b]
  have hWge : ∀ b : S → ℕ, 1 + tot b ≤ W b := fun b => le_self_pow₀ (hbase b) (by omega)
  have hWpos : ∀ b : S → ℕ, 0 < W b := fun b => lt_of_lt_of_le one_pos ((hbase b).trans (hWge b))
  set c := 2 ^ k * ∑ r, κ.k r with hc
  have hc0 : 0 ≤ c := mul_nonneg (by positivity) (Finset.sum_nonneg fun r _ => (κ.positive r).le)
  have hdr : ∀ b, (N.jumpSystem κ).drift W b ≤ c * W b := fun b => drift_powTotal_le N κ hmono k b
  have hfin : ∀ R : ℝ, {b | W b ≤ R}.Finite := fun R =>
    (finite_linearObservable_le (S := S) (fun _ => (1 : ℝ)) (fun _ => one_pos) R).subset
      fun b hb => by
        simp only [Set.mem_ofPred_eq] at hb ⊢
        have hl : linearObservable (fun _ => (1 : ℝ)) b = tot b := by
          simp [linearObservable, tot]
        rw [hl]; linarith [hWge b]
  have hstoch : ∀ τ, 0 ≤ τ → HasSum (fun b => (N.jumpSystem κ).Pmin τ n b) 1 := fun τ hτ =>
    (N.jumpSystem κ).hasSum_Pmin_one_of_drift W (fun b => (hWpos b).le) hfin hc0 hdr hτ n
  have hmom : ∀ τ, 0 ≤ τ → Summable fun b => (N.jumpSystem κ).Pmin τ n b * (1 + tot b) := by
    intro τ hτ
    refine summable_of_sum_le (c := Real.exp (c * τ) * W n) (fun b => mul_nonneg
      ((N.jumpSystem κ).Pmin_nonneg τ hτ n b) (by linarith [hbase b])) fun F => ?_
    exact le_trans (Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hWge b)
      ((N.jumpSystem κ).Pmin_nonneg τ hτ n b))
      ((N.jumpSystem κ).sum_Pmin_mul_le W (fun b => (hWpos b).le) hc0 hdr hτ n F)
  set M : ℝ → Concentration S := fun τ j => ∑' b, (N.jumpSystem κ).Pmin τ n b * (b j : ℝ)
    with hM
  -- integrating the rates against the law
  have hrate : ∀ τ, 0 ≤ τ → ∀ r, ∑' b, (N.jumpSystem κ).Pmin τ n b *
      N.massActionRate κ r (castCount b) = N.massActionRate κ r (M τ) := by
    intro τ hτ r
    rcases massActionRate_cases N κ hmono r with h0 | ⟨j, hj⟩
    · simp only [h0]; rw [tsum_mul_right, (hstoch τ hτ).tsum_eq, one_mul]
    · simp only [hj, castCount, hM]
      rw [show (fun b => (N.jumpSystem κ).Pmin τ n b * (κ.k r * (b j : ℝ))) =
        fun b => κ.k r * ((N.jumpSystem κ).Pmin τ n b * (b j : ℝ)) from
        funext fun b => by ring, tsum_mul_left]
  -- the mean solves the mass-action equation for `τ > 0`
  have hderiv : ∀ τ, 0 < τ → HasDerivAt M (N.massActionVectorField κ (M τ)) τ := by
    intro τ hτ
    rw [hasDerivAt_pi]
    intro j
    have h := (N.jumpSystem κ).hasDerivAt_expect (fun b => (b j : ℝ)) W hWpos hc0 hdr
      (summable_coord_bound N κ hmono j) hτ n
    convert h using 1
    simp only [drift_coord N κ hmono j, massActionVectorField_apply]
    have hsum : ∀ r, Summable fun b => (N.jumpSystem κ).Pmin τ n b *
        N.massActionRate κ r (castCount b) * N.reactionVector r j := by
      intro r
      refine Summable.of_norm_bounded (((hmom τ hτ.le).mul_left (κ.k r)).mul_right
        |N.reactionVector r j|) fun b => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg ((N.jumpSystem κ).Pmin_nonneg τ hτ.le
        n b), ← stochasticRate_eq_massActionRate N κ hmono,
        abs_of_nonneg (N.stochasticMassActionRate_nonneg κ b r)]
      have := stochasticRate_le N κ hmono b r
      have hP := (N.jumpSystem κ).Pmin_nonneg τ hτ.le n b
      calc (N.jumpSystem κ).Pmin τ n b * N.stochasticMassActionRate κ b r *
            |N.reactionVector r j|
          ≤ (N.jumpSystem κ).Pmin τ n b * (κ.k r * (1 + tot b)) * |N.reactionVector r j| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hP) (abs_nonneg _)
        _ = κ.k r * ((N.jumpSystem κ).Pmin τ n b * (1 + tot b)) * |N.reactionVector r j| := by
            ring
    rw [show (fun b => (N.jumpSystem κ).Pmin τ n b *
        ∑ r, N.massActionRate κ r (castCount b) * N.reactionVector r j) =
        fun b => ∑ r, (N.jumpSystem κ).Pmin τ n b * N.massActionRate κ r (castCount b) *
          N.reactionVector r j from funext fun b => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring,
      Summable.tsum_finsetSum fun r _ => hsum r]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [tsum_mul_right, hrate τ hτ.le r]
  -- the value at `0`
  have hM0 : M 0 = castCount n := by
    funext j
    simp only [hM, JumpSystem.Pmin_zero, castCount]
    rw [tsum_eq_single n fun b hb => by rw [if_neg (Ne.symm hb), zero_mul]]
    simp
  -- right continuity at `0`
  have hcont0 : Tendsto M (𝓝[>] 0) (𝓝 (castCount n)) := by
    rw [tendsto_pi_nhds]
    intro j
    have hval : castCount n j = ∑' b, (if n = b then (1 : ℝ) else 0) * (b j : ℝ) := by
      rw [tsum_eq_single n fun b hb => by rw [if_neg (Ne.symm hb), zero_mul]]
      simp [castCount]
    rw [hval]
    have hbsum : Summable fun b : S → ℕ => (b j : ℝ) / W b := by
      refine Summable.of_nonneg_of_le (fun b => div_nonneg (Nat.cast_nonneg _) (hWpos b).le)
        (fun b => div_le_div_of_nonneg_right ?_ (hWpos b).le) (summable_coord_bound N κ hmono j)
      have h1 : (b j : ℝ) ≤ (1 + |(b j : ℝ)|) * (1 + (N.jumpSystem κ).q b) := by
        rw [abs_of_nonneg (Nat.cast_nonneg _)]
        nlinarith [(N.jumpSystem κ).q_nonneg b, (Nat.cast_nonneg (b j) : (0 : ℝ) ≤ b j)]
      have h2 : 0 ≤ ∑ i, (N.jumpSystem κ).rate i b * |(((N.jumpSystem κ).next i b) j : ℝ)| :=
        Finset.sum_nonneg fun i _ => mul_nonneg ((N.jumpSystem κ).rate_nonneg i b) (abs_nonneg _)
      linarith
    refine tendsto_tsum_of_dominated_convergence (hbsum.mul_left (Real.exp c * W n))
      (fun b => ?_) ?_
    · have hcw := (N.jumpSystem κ).continuousOn_Pmin n b 0 (Set.mem_Ici.mpr le_rfl)
      have ht0 : Tendsto (fun τ => (N.jumpSystem κ).Pmin τ n b) (𝓝[>] 0)
          (𝓝 ((N.jumpSystem κ).Pmin 0 n b)) :=
        hcw.tendsto.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
      rw [JumpSystem.Pmin_zero] at ht0
      exact ht0.mul_const _
    · filter_upwards [Ioc_mem_nhdsGT one_pos] with τ hτ b
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ((N.jumpSystem κ).Pmin_nonneg τ hτ.1.le n b),
        abs_of_nonneg (Nat.cast_nonneg _)]
      have hP := (N.jumpSystem κ).Pmin_le_div W hWpos hc0 hdr hτ.1.le n b
      have hexp : Real.exp (c * τ) ≤ Real.exp c :=
        Real.exp_le_exp.mpr (by nlinarith [hτ.2])
      calc (N.jumpSystem κ).Pmin τ n b * (b j : ℝ) ≤ Real.exp (c * τ) * W n / W b * (b j : ℝ) :=
            mul_le_mul_of_nonneg_right hP (Nat.cast_nonneg _)
        _ ≤ Real.exp c * W n / W b * (b j : ℝ) := by
            refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hexp (hWpos n).le) (hWpos b).le) (Nat.cast_nonneg _)
        _ = Real.exp c * W n * ((b j : ℝ) / W b) := by ring
  -- Grönwall
  obtain ⟨L, hL⟩ := lipschitz_massActionVectorField N κ hmono
  have hMt : M t = x t := by
    rcases ht.eq_or_lt with h0 | htpos
    · subst h0; rw [hM0, hx0]
    · have hgron : ∀ ε ∈ Ioo (0 : ℝ) t,
          dist (M t) (x t) ≤ dist (M ε) (x ε) * Real.exp (L * (t - ε)) := by
        intro ε hε
        have hpos : ∀ τ ∈ Icc ε t, 0 < τ := fun τ hτ => lt_of_lt_of_le hε.1 hτ.1
        exact dist_le_of_trajectories_ODE (v := fun _ => N.massActionVectorField κ) (K := L)
          (fun _ => hL)
          (fun τ hτ => (hderiv τ (hpos τ hτ)).continuousAt.continuousWithinAt)
          (fun τ hτ => (hderiv τ (hpos τ (Ico_subset_Icc_self hτ))).hasDerivWithinAt)
          (hxc.mono fun τ hτ => le_of_lt (hpos τ hτ))
          (fun τ hτ => (hx τ (hpos τ (Ico_subset_Icc_self hτ))).hasDerivWithinAt)
          le_rfl t ⟨hε.2.le, le_rfl⟩
      have hxlim : Tendsto x (𝓝[>] 0) (𝓝 (x 0)) :=
        (hxc 0 (Set.mem_Ici.mpr le_rfl)).tendsto.mono_left
          (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
      have hlim : Tendsto (fun ε => dist (M ε) (x ε) * Real.exp (L * (t - ε))) (𝓝[>] 0)
          (𝓝 (dist (castCount n) (x 0) * Real.exp (L * (t - 0)))) :=
        ((hcont0.dist hxlim).mul ((Real.continuous_exp.tendsto _).comp
          ((tendsto_const_nhds.sub tendsto_id).const_mul _ |>.mono_left nhdsWithin_le_nhds)))
      rw [hx0, dist_self, zero_mul] at hlim
      have hle : dist (M t) (x t) ≤ 0 :=
        ge_of_tendsto hlim (by
          filter_upwards [Ioo_mem_nhdsGT htpos] with ε hε using hgron ε hε)
      exact dist_le_zero.mp hle
  have := congrFun hMt s
  simpa [hM, transition] using this

end Network

namespace Examples
namespace PoissonBirthDeath

open Network

/-- The deterministic solution `x(t) = 1 + (n − 1) e^{−t}` of `ẋ = 1 − x` from `n`. -/
noncomputable def sol (n : ℕ) (t : ℝ) : Concentration Unit := fun _ => 1 + ((n : ℝ) - 1) * Real.exp (-t)

theorem sol_ode (n : ℕ) (t : ℝ) : HasDerivAt (sol n) (net.massActionVectorField κ (sol n t)) t := by
  rw [hasDerivAt_pi]
  intro u
  have h : HasDerivAt (fun t : ℝ => 1 + ((n : ℝ) - 1) * Real.exp (-t))
      (((n : ℝ) - 1) * -Real.exp (-t)) t := by
    simpa using (((hasDerivAt_neg t).exp).const_mul ((n : ℝ) - 1)).const_add 1
  have h' : HasDerivAt (fun x => sol n x u) (((n : ℝ) - 1) * -Real.exp (-t)) t := h
  convert h' using 1
  show ∑ r : Fin 2, net.massActionRate κ r (sol n t) * net.reactionVector r u = _
  simp [Fin.sum_univ_two, massActionRate, κ, sol, Complex.massActionMonomial,
    Network.reactionVector, Reaction.vector]

/-- **Mean of the birth–death chain** `0 ⇌ X` with unit rates: from `n` molecules,
`E_n[X(t)] = 1 + (n − 1) e^{−t}`. -/
theorem mean (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∑' m, net.transition κ t (fun _ => n) m * (m () : ℝ) = 1 + ((n : ℝ) - 1) * Real.exp (-t) :=
  net.monomolecular_mean κ monomolecular (fun _ => n) (sol n)
    (by funext u; simp [sol, castCount])
    (fun t _ => (sol_ode n t).continuousAt.continuousWithinAt) (fun t _ => sol_ode n t) ht ()

end PoissonBirthDeath
end Examples

end CRNT
