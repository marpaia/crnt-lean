import CRNT.Stochastic.ConservativeLLN

/-!
# Kurtz's law of large numbers for subconservative networks

A network is *subconservative* if a strictly positive weight `w` is not increased by any reaction:
`⟨w, y'_r − y_r⟩ ≤ 0` for every `r` (degradation and dimerization-type networks without inflows;
conservative networks are the case of equality).  From a count `n` the chain stays in the finite
set `{c : ⟨w, c⟩ ≤ ⟨w, n⟩}` (`finite_reachPos_of_subconservative`), and the proof of the
conservative law of large numbers goes through: `E_n |X^V(t)/V − x(t)|² ≤ gronwallBound(…)`
with constants independent of `V` (`subconservative_lln`), hence `→ 0` as `V → ∞`
(`subconservative_lln_tendsto`).

Instance: the non-conservative bimolecular network `2X → 0`, whose mass-action solution from
`x(0) = 1` is `x(t) = 1/(1 + 2t)` (`CRNT.Examples.Annihilation.lln`).

Nothing here is an axiom or a `sorry`.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology NNReal

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- An enabled jump does not increase a weight that no reaction increases. -/
theorem weight_jumpNextCount_le (N : Network S) (κ : RateConstants N) {w : S → ℝ}
    (hw : ∀ r, ∑ s, w s * N.reactionVector r s ≤ 0) {n : S → ℕ} {r : N.R}
    (hr : 0 < N.stochasticMassActionRate κ n r) :
    ∑ s, w s * (N.jumpNextCount n r s : ℝ) ≤ ∑ s, w s * (n s : ℝ) := by
  have hen : N.Enabled n r := by
    by_contra h
    rw [N.stochasticMassActionRate_eq_zero_of_not_enabled κ n r h] at hr
    exact lt_irrefl _ hr
  have hcast : ∀ s, (N.jumpNextCount n r s : ℝ) = (n s : ℝ) + N.reactionVector r s := by
    intro s
    simp only [jumpNextCount, reactionVector_apply]
    rw [Nat.cast_add, Nat.cast_sub (hen s)]
    ring
  simp only [hcast, mul_add, Finset.sum_add_distrib]
  linarith [hw r]

/-- The weight is nonincreasing along reachable counts. -/
theorem weight_of_reachPos_le (N : Network S) (κ : RateConstants N) {w : S → ℝ}
    (hw : ∀ r, ∑ s, w s * N.reactionVector r s ≤ 0) {n c : S → ℕ}
    (h : (N.jumpSystem κ).ReachPos n c) :
    ∑ s, w s * (c s : ℝ) ≤ ∑ s, w s * (n s : ℝ) := by
  induction h with
  | refl => exact le_rfl
  | @tail x y _ hxy ih =>
      obtain ⟨r, hr, rfl⟩ := hxy
      exact (N.weight_jumpNextCount_le κ hw hr).trans ih

/-- From a fixed count, a subconservative network reaches only finitely many counts. -/
theorem finite_reachPos_of_subconservative (N : Network S) (κ : RateConstants N) {w : S → ℝ}
    (hw : ∀ r, ∑ s, w s * N.reactionVector r s ≤ 0) (hwpos : ∀ s, 0 < w s) (n₀ : S → ℕ) :
    {c | (N.jumpSystem κ).ReachPos n₀ c}.Finite := by
  set W := ∑ s, w s * (n₀ s : ℝ)
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ c : S → ℕ, ∑ s, w s * (c s : ℝ) ≤ W → ∀ s, c s ≤ K := by
    refine ⟨⌈∑ s, W / w s⌉₊, fun c hc s => ?_⟩
    have h1 : w s * (c s : ℝ) ≤ W := by
      refine le_trans ?_ hc
      exact Finset.single_le_sum (f := fun s => w s * (c s : ℝ))
        (fun s _ => mul_nonneg (hwpos s).le (Nat.cast_nonneg _)) (Finset.mem_univ s)
    have h2 : (c s : ℝ) ≤ W / w s := by rw [le_div_iff₀ (hwpos s)]; linarith
    have hW0 : 0 ≤ W := Finset.sum_nonneg fun s _ => mul_nonneg (hwpos s).le (Nat.cast_nonneg _)
    have h3 : W / w s ≤ ∑ s, W / w s :=
      Finset.single_le_sum (f := fun s => W / w s) (fun s _ => div_nonneg hW0 (hwpos s).le)
        (Finset.mem_univ s)
    exact_mod_cast (h2.trans h3).trans (Nat.le_ceil _)
  refine (Fintype.piFinset fun _ : S => Finset.range (K + 1)).finite_toSet.subset fun c hc => ?_
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  exact fun s => Finset.mem_range.mpr
    (Nat.lt_succ_of_le (hK c (N.weight_of_reachPos_le κ hw hc) s))

/-- The finite set of counts reachable from `n` in a subconservative network. -/
noncomputable def subReachClass (N : Network S) (κ : RateConstants N) {w : S → ℝ}
    (hw : ∀ r, ∑ s, w s * N.reactionVector r s ≤ 0) (hwpos : ∀ s, 0 < w s) (n : S → ℕ) :
    Finset (S → ℕ) :=
  (N.finite_reachPos_of_subconservative κ hw hwpos n).toFinset

theorem mem_subReachClass (N : Network S) (κ : RateConstants N) {w : S → ℝ}
    (hw : ∀ r, ∑ s, w s * N.reactionVector r s ≤ 0) (hwpos : ∀ s, 0 < w s) {n m : S → ℕ} :
    m ∈ N.subReachClass κ hw hwpos n ↔ (N.jumpSystem κ).ReachPos n m := by
  simp [subReachClass]

/-- **Kurtz's law of large numbers for subconservative networks, at fixed times.** For a network
with a positive linear weight `w` that no reaction increases (`⟨w, y' − y⟩ ≤ 0`; conservative
networks are the case of equality), volume-scaled rate constants `κ_r V^{1 − |y_r|}`, and a
solution `x` of the mass-action equation on `[0, T]` with values in `[0, R_x]^S`, there are
constants `C₁, C₂ ≥ 0` such that for every `V ≥ 1`, every initial count `n` with `w · n ≤ M V`,
and every `t ∈ [0, T]`,

`E_n |X^V(t)/V − x(t)|² ≤ gronwallBound (|n/V − x(0)|²) C₁ (C₂/V) t`. -/
theorem subconservative_lln (N : Network S) (κ : RateConstants N) {w : S → ℝ}
    (hwsub : ∀ r, ∑ s, w s * N.reactionVector r s ≤ 0) (hwpos : ∀ s, 0 < w s) {M T Rx : ℝ} (hM : 0 ≤ M)
    (x : ℝ → Concentration S) (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (N.massActionVectorField κ (x t)) t)
    (hxB : ∀ t ∈ Icc 0 T, x t ∈ Icc (0 : Concentration S) fun _ => Rx) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ (V : ℝ) (hV : 1 ≤ V) (n : S → ℕ),
      ∑ s, w s * (n s : ℝ) ≤ M * V → ∀ t ∈ Icc 0 T,
        ∑' m, N.transition (N.volumeScale κ V (by linarith)) t n m *
            ∑ s, ((m s : ℝ) / V - x t s) ^ 2 ≤
          gronwallBound (∑ s, ((n s : ℝ) / V - x 0 s) ^ 2) C₁ (C₂ / V) t := by
  classical
  set R := ∑ s, M / w s with hRdef
  have hR : 0 ≤ R := Finset.sum_nonneg fun s _ => div_nonneg hM (hwpos s).le
  set Rb := max R Rx with hRb
  obtain ⟨L, hL⟩ := ((N.contDiff_massActionVectorField κ).contDiffOn
    (s := Icc (0 : Concentration S) fun _ => Rb)).exists_lipschitzOnWith
    (by simp) (convex_Icc _ _) isCompact_Icc
  set C₁ := 1 + 2 * (Fintype.card S : ℝ) * L with hC₁
  set C₂ := (Fintype.card S : ℝ) * N.rateErr κ R ^ 2 + N.noiseConst κ R with hC₂
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hC₂0 : 0 ≤ C₂ := by
    refine add_nonneg (by positivity) (Finset.sum_nonneg fun r _ => mul_nonneg
      (mul_nonneg (κ.positive r).le (by positivity)) (Finset.sum_nonneg fun s _ => sq_nonneg _))
  refine ⟨C₁, C₂, hC₁0, hC₂0, fun V hV n hn t ht => ?_⟩
  have hV0 : 0 < V := by linarith
  set κV := N.volumeScale κ V hV0 with hκV
  set J := N.jumpSystem κV with hJ
  set Rset := N.subReachClass κV hwsub hwpos n with hRset
  have hsupp : ∀ τ, ∀ b, b ∉ Rset → J.Pmin τ n b = 0 := fun τ b hb =>
    J.Pmin_eq_zero_of_not_reachPos τ fun h => hb ((N.mem_subReachClass κV hwsub hwpos).mpr h)
  have hclosed : ∀ c ∈ Rset, ∀ i, 0 < J.rate i c → J.next i c ∈ Rset := by
    intro c hc i hi
    rw [N.mem_subReachClass κV hwsub hwpos] at hc ⊢
    exact hc.tail ⟨i, hi, rfl⟩
  have hnR : n ∈ Rset := (N.mem_subReachClass κV hwsub hwpos).mpr Relation.ReflTransGen.refl
  have hcR : ∀ c ∈ Rset, ∀ s, (c s : ℝ) ≤ R * V := by
    intro c hc s
    have hw := N.weight_of_reachPos_le κV hwsub ((N.mem_subReachClass κV hwsub hwpos).mp hc)
    have h1 : w s * (c s : ℝ) ≤ M * V := by
      refine le_trans ?_ (hw.trans hn)
      exact Finset.single_le_sum (f := fun s => w s * (c s : ℝ))
        (fun s _ => mul_nonneg (hwpos s).le (Nat.cast_nonneg _)) (Finset.mem_univ s)
    have h2 : (c s : ℝ) ≤ M / w s * V := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (hwpos s)]; linarith
    have h3 : M / w s ≤ R := Finset.single_le_sum (f := fun s => M / w s)
      (fun s _ => div_nonneg hM (hwpos s).le) (Finset.mem_univ s)
    exact h2.trans (mul_le_mul_of_nonneg_right h3 hV0.le)
  -- the observable and the mean squared distance
  set g : ℝ → (S → ℕ) → ℝ := fun τ b => ∑ s, ((b s : ℝ) / V - x τ s) ^ 2 with hg
  set g' : ℝ → (S → ℕ) → ℝ := fun τ b =>
    ∑ s, 2 * ((b s : ℝ) / V - x τ s) * -(N.massActionVectorField κ (x τ) s) with hg'
  set D : ℝ → ℝ := fun τ => ∑ b ∈ Rset, J.Pmin τ n b * g τ b with hD
  have hDeq : ∀ τ, ∑' m, N.transition κV τ n m * g τ m = D τ := fun τ =>
    tsum_eq_sum fun b hb => by
      show J.Pmin τ n b * g τ b = 0
      rw [hsupp τ b hb, zero_mul]
  -- derivative and differential inequality
  have hgder : ∀ τ ∈ Ioo 0 T, ∀ b, HasDerivAt (fun τ => g τ b) (g' τ b) τ := by
    intro τ hτ b
    have hxτ := hasDerivAt_pi.mp (hx τ hτ)
    refine HasDerivAt.fun_sum fun s _ => ?_
    have h1 : HasDerivAt (fun τ => (b s : ℝ) / V - x τ s) (-(N.massActionVectorField κ (x τ) s))
        τ := by simpa using (hxτ s).const_sub ((b s : ℝ) / V)
    convert h1.pow 2 using 1
    push_cast; ring
  have hDder : ∀ τ ∈ Ioo 0 T, HasDerivAt D
      (∑ c ∈ Rset, J.Pmin τ n c * (J.drift (g τ) c + g' τ c)) τ := fun τ hτ =>
    J.hasDerivAt_sum_finite n Rset hsupp hclosed g g' hτ.1 fun b _ => hgder τ hτ b
  have hbound : ∀ τ ∈ Ioo 0 T,
      ∑ c ∈ Rset, J.Pmin τ n c * (J.drift (g τ) c + g' τ c) ≤ C₁ * D τ + C₂ / V := by
    intro τ hτ
    have hxτB : x τ ∈ Icc (0 : Concentration S) fun _ => Rb := by
      obtain ⟨h1, h2⟩ := hxB τ (Ioo_subset_Icc_self hτ)
      exact ⟨h1, fun s => (h2 s).trans (le_max_right _ _)⟩
    have hpt : ∀ c ∈ Rset, J.drift (g τ) c + g' τ c ≤ C₁ * g τ c + C₂ / V := fun c hc =>
      N.drift_dist_sq_le κ hV hR (le_max_left _ _) hL c (hcR c hc) (x τ) hxτB
    calc ∑ c ∈ Rset, J.Pmin τ n c * (J.drift (g τ) c + g' τ c)
        ≤ ∑ c ∈ Rset, J.Pmin τ n c * (C₁ * g τ c + C₂ / V) :=
          Finset.sum_le_sum fun c hc => mul_le_mul_of_nonneg_left (hpt c hc)
            (J.Pmin_nonneg τ hτ.1.le n c)
      _ = C₁ * D τ + C₂ / V * ∑ c ∈ Rset, J.Pmin τ n c := by
          simp only [hD, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
          congr 1 <;> exact Finset.sum_congr rfl fun c _ => by ring
      _ ≤ C₁ * D τ + C₂ / V := by
          have h1 := J.sum_Pmin_le_one τ hτ.1.le n Rset
          have h2 : 0 ≤ C₂ / V := div_nonneg hC₂0 hV0.le
          nlinarith
  -- continuity
  have hDc : ContinuousOn D (Icc 0 T) := by
    refine continuousOn_finsetSum _ fun b _ => ?_
    refine ((J.continuousOn_Pmin n b).mono fun τ hτ => hτ.1).mul ?_
    refine continuousOn_finsetSum _ fun s _ => ?_
    exact (continuousOn_const.sub ((continuous_apply s).comp_continuousOn hxc)).pow 2
  have hD0 : D 0 = g 0 n := by
    simp only [hD, JumpSystem.Pmin_zero]
    rw [Finset.sum_eq_single n (fun b _ hb => by rw [if_neg (Ne.symm hb), zero_mul])
      (fun h => absurd hnR h)]
    simp
  rw [hDeq]
  rcases ht.1.eq_or_lt with h0 | htpos
  · subst h0; rw [hD0, gronwallBound_x0]
  · -- Grönwall on `[ε, t]`, then `ε → 0⁺`
    have hT : 0 < T := lt_of_lt_of_le htpos ht.2
    have hgron : ∀ ε ∈ Ioo (0 : ℝ) t, D t ≤ gronwallBound (D ε) C₁ (C₂ / V) (t - ε) := by
      intro ε hε
      have hsub : Icc ε t ⊆ Icc 0 T := Icc_subset_Icc hε.1.le ht.2
      have h := le_gronwallBound_of_liminf_deriv_right_le (f := D)
        (f' := fun τ => ∑ c ∈ Rset, J.Pmin τ n c * (J.drift (g τ) c + g' τ c))
        (δ := D ε) (K := C₁) (ε := C₂ / V) (a := ε) (b := t) (hDc.mono hsub)
        (fun τ hτ r hr => ((hDder τ ⟨lt_of_lt_of_le hε.1 hτ.1, lt_of_lt_of_le hτ.2 ht.2⟩
          ).hasDerivWithinAt).liminf_right_slope_le hr) le_rfl
        (fun τ hτ => hbound τ ⟨lt_of_lt_of_le hε.1 hτ.1, lt_of_lt_of_le hτ.2 ht.2⟩)
      exact h t ⟨hε.2.le, le_rfl⟩
    have hC₁ne : C₁ ≠ 0 := by positivity
    have hcont : Tendsto (fun ε => gronwallBound (D ε) C₁ (C₂ / V) (t - ε)) (𝓝[>] 0)
        (𝓝 (gronwallBound (D 0) C₁ (C₂ / V) (t - 0))) := by
      simp only [gronwallBound_of_K_ne_0 hC₁ne]
      have hD0t : Tendsto D (𝓝[>] 0) (𝓝 (D 0)) := by
        have hw := hDc 0 ⟨le_rfl, hT.le⟩
        refine hw.tendsto.mono_left ?_
        refine nhdsWithin_le_of_mem ?_
        exact mem_of_superset (Ioo_mem_nhdsGT hT) Ioo_subset_Icc_self
      have hlin : Tendsto (fun ε : ℝ => t - ε) (𝓝[>] 0) (𝓝 (t - 0)) :=
        (tendsto_const_nhds.sub tendsto_id).mono_left nhdsWithin_le_nhds
      have hexp := (Real.continuous_exp.tendsto _).comp (hlin.const_mul C₁)
      exact (hD0t.mul hexp).add (tendsto_const_nhds.mul (hexp.sub tendsto_const_nhds))
    have hle := ge_of_tendsto hcont (by
      filter_upwards [Ioo_mem_nhdsGT htpos] with ε hε using hgron ε hε)
    rw [hD0, sub_zero] at hle
    exact hle

/-- **The law of large numbers as `V → ∞`, subconservative networks.** With `V = k + 1` and initial counts `n_k` satisfying
`w · n_k ≤ M V` and `n_k / V → x(0)`, the mean squared distance `E |X^V(t)/V − x(t)|²` tends to
`0` for every `t ∈ [0, T]`. -/
theorem subconservative_lln_tendsto (N : Network S) (κ : RateConstants N) {w : S → ℝ}
    (hwsub : ∀ r, ∑ s, w s * N.reactionVector r s ≤ 0) (hwpos : ∀ s, 0 < w s) {M T Rx : ℝ} (hM : 0 ≤ M)
    (x : ℝ → Concentration S) (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (N.massActionVectorField κ (x t)) t)
    (hxB : ∀ t ∈ Icc 0 T, x t ∈ Icc (0 : Concentration S) fun _ => Rx)
    (n : ℕ → S → ℕ) (hn : ∀ k, ∑ s, w s * (n k s : ℝ) ≤ M * ((k : ℝ) + 1))
    (hn0 : Tendsto (fun k => ∑ s, ((n k s : ℝ) / ((k : ℝ) + 1) - x 0 s) ^ 2) atTop (𝓝 0))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun k : ℕ => ∑' m, N.transition (N.volumeScale κ ((k : ℝ) + 1)
        (by positivity)) t (n k) m * ∑ s, ((m s : ℝ) / ((k : ℝ) + 1) - x t s) ^ 2) atTop
      (𝓝 0) := by
  obtain ⟨C₁, C₂, -, -, hbd⟩ := subconservative_lln N κ hwsub hwpos (Rx := Rx) hM x hxc hx hxB
  have hV : ∀ k : ℕ, (1 : ℝ) ≤ (k : ℝ) + 1 := fun k => by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  have hden : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hε : Tendsto (fun k : ℕ => C₂ / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hup := tendsto_gronwallBound hn0 hε C₁ t
  refine squeeze_zero (fun k => tsum_nonneg fun m => mul_nonneg
    ((N.jumpSystem _).Pmin_nonneg t ht.1 _ _) (Finset.sum_nonneg fun s _ => sq_nonneg _))
    (fun k => hbd ((k : ℝ) + 1) (hV k) (n k) (hn k) t ht) hup

end Network

namespace Examples
namespace Annihilation

open Network

/-- `2X → 0`. -/
abbrev net : Network (Fin 1) :=
  ⟨Fin 1, inferInstance, inferInstance, fun _ => ⟨![2], 0⟩⟩

def κ : RateConstants net := ⟨fun _ => 1, fun _ => one_pos⟩

/-- The number of molecules is not increased. -/
theorem w_sub : ∀ r, ∑ s, (fun _ : Fin 1 => (1 : ℝ)) s * net.reactionVector r s ≤ 0 := by
  intro r
  simp [Network.reactionVector, Reaction.vector]

/-- The network is not conservative. -/
theorem not_isConservative : ¬ net.IsConservative := by
  rintro ⟨w, hw, hpos⟩
  have h := hw _ (net.reactionVector_mem_stoichSubspace 0)
  simp [Network.reactionVector, Reaction.vector] at h
  linarith [hpos 0]

/-- The mass-action solution `x(t) = 1/(1 + 2t)`. -/
noncomputable def sol (t : ℝ) : Concentration (Fin 1) := fun _ => 1 / (1 + 2 * t)

theorem sol_deriv (t : ℝ) (ht : 0 ≤ t) : HasDerivAt sol (net.massActionVectorField κ (sol t)) t := by
  have hpos : 0 < 1 + 2 * t := by linarith
  have hc : HasDerivAt (fun t : ℝ => 1 + 2 * t) 2 t := by
    simpa using ((hasDerivAt_id t).const_mul 2).const_add 1
  have h1 : HasDerivAt (fun t : ℝ => 1 / (1 + 2 * t)) (-(2 : ℝ) / (1 + 2 * t) ^ 2) t := by
    have := hc.inv (ne_of_gt hpos)
    simp only [one_div]
    exact this
  rw [hasDerivAt_pi]
  intro s
  have hfield : net.massActionVectorField κ (sol t) s = -(2 : ℝ) / (1 + 2 * t) ^ 2 := by
    rw [massActionVectorField_apply]
    simp [massActionRate, κ, sol, Complex.massActionMonomial, Network.reactionVector,
      Reaction.vector]
    field_simp
  rw [hfield]
  exact h1

/-- **LLN instance for the non-conservative network `2X → 0`.** Started from `V` molecules at
volume `V = k + 1`, `E |X^V(t)/V − 1/(1 + 2t)|² → 0` for every `t ∈ [0, 1]`. -/
theorem lln {t : ℝ} (ht : t ∈ Icc 0 1) :
    Tendsto (fun k : ℕ => ∑' m, net.transition (net.volumeScale κ ((k : ℝ) + 1) (by positivity))
        t (fun _ => k + 1) m * ∑ s, ((m s : ℝ) / ((k : ℝ) + 1) - sol t s) ^ 2) atTop (𝓝 0) := by
  refine subconservative_lln_tendsto net κ w_sub (fun _ => one_pos) (M := 1) (Rx := 1) (by norm_num)
    sol ?_ (fun t ht => sol_deriv t ht.1.le) ?_ (fun k _ => k + 1) (fun k => ?_) ?_ ht
  · intro t ht
    exact (sol_deriv t ht.1).continuousAt.continuousWithinAt
  · intro t ht
    have hpos : 0 < 1 + 2 * t := by linarith [ht.1]
    refine ⟨fun _ => by simp [sol]; positivity, fun _ => ?_⟩
    simp only [sol]
    rw [div_le_one hpos]
    linarith [ht.1]
  · simp
  · have h : ∀ k : ℕ, ∑ s, ((((fun _ : Fin 1 => k + 1) s : ℕ) : ℝ) / ((k : ℝ) + 1) - sol 0 s) ^ 2
        = 0 := by
      intro k
      have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
      simp [sol, hk]
    simp only [h]
    exact tendsto_const_nhds

end Annihilation
end Examples

end CRNT
