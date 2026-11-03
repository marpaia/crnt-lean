import CRNT.Stochastic.KurtzLLN

/-!
# Kurtz's law of large numbers, uniform in time (exit-mass formulation)

The library has no path measure; an event "the chain leaves `K` before time `h`" is represented
by the mass that the chain frozen outside `K` (`JumpSystem.stopOutside`) has outside `K` at time `h`.

For any network, any solution `x` of the mass-action equation on `[0, T]` with values in
`[0, R_x]^S`, and any `δ ∈ (0, 1]`, split `[0, T]` into `m` intervals `[t_i, t_i + h]`,
`h = T/m`, with `m` large enough that `x` moves by less than `δ/2` on each interval.  Let
`B_i = {c : |c/V − x(t_i)|² ≤ δ²}`.  Then

`∑_{i < m} ∑_c P(t_i)(n_V, c) · (mass outside B_i at time h of the chain started at c and frozen
outside B_i) → 0`  as `V → ∞`, whenever `n_V/V → x(0)` (`kurtz_lln_uniform`).

Under the path interpretation of the frozen chain, the `i`-th term is the probability that the
chain leaves `B_i` during `[t_i, t_i + h]`, so the sum bounds the probability that
`sup_{t ≤ T} |X^V(t)/V − x(t)| > δ + δ/2`; this last step (the identification of the frozen
mass with an exit probability and the union bound) is not formalized here.

Proof of the exit estimate (`exit_mass_le`): for the chain started at `c` and frozen outside `B_i`,
`D(s) = E |X(s)/V − x(t_i + s)|²` satisfies a closed Grönwall inequality with source `O(1/V)`:
inside `B_i` by the drift estimate of the conservative LLN, and on frozen states because there the
squared distance is at least `δ²/4`, so the time-derivative term is absorbed.  Frozen states
carry `D ≥ δ²/4`, hence the exit mass is at most `(4/δ²) D(h)`.  Averaging over `P(t_i)(n, ·)`
and using `kurtz_lln_tendsto` at `t_i` finishes the proof.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology NNReal

namespace CRNT

namespace JumpSystem

variable {α : Type*} [DecidableEq α] (J : JumpSystem α)

/-- A finite set containing every state reachable from `a` by the chain frozen outside `K`. -/
noncomputable def frozenReach (K : Finset α) (a : α) : Finset α :=
  insert a (K ∪ K.biUnion fun c => Finset.univ.image fun i => J.next i c)

theorem mem_frozenReach_of_reachPos (K : Finset α) {a c : α}
    (h : (J.stopOutside K).ReachPos a c) : c ∈ J.frozenReach K a := by
  induction h with
  | refl => exact Finset.mem_insert_self _ _
  | @tail x y _ hxy _ =>
      obtain ⟨i, hi, rfl⟩ := hxy
      have hx : x ∈ K := by
        by_contra hx
        simp [stopOutside, hx] at hi
      apply Finset.mem_insert_of_mem
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩

theorem frozenReach_closed (K : Finset α) (a : α) :
    ∀ c ∈ J.frozenReach K a, ∀ i, 0 < (J.stopOutside K).rate i c →
      (J.stopOutside K).next i c ∈ J.frozenReach K a := by
  intro c _ i hi
  have hc : c ∈ K := by
    by_contra hc
    simp [stopOutside, hc] at hi
  apply Finset.mem_insert_of_mem
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩

theorem Pmin_stop_eq_zero (K : Finset α) (t : ℝ) {a b : α} (hb : b ∉ J.frozenReach K a) :
    (J.stopOutside K).Pmin t a b = 0 :=
  (J.stopOutside K).Pmin_eq_zero_of_not_reachPos t fun h =>
    hb (J.mem_frozenReach_of_reachPos K h)

end JumpSystem

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The counts within squared distance `δ²` of `V z`. -/
noncomputable def ballSet (V Rx : ℝ) (z : Concentration S) (δ : ℝ) : Finset (S → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ => Finset.range (⌈V * (Rx + 1)⌉₊ + 1)).filter
    (fun c => ∑ s, ((c s : ℝ) / V - z s) ^ 2 ≤ δ ^ 2)

theorem coord_le_of_dist_le {V Rx δ : ℝ} (hV : 0 < V) {z : Concentration S}
    (hz : ∀ s, z s ≤ Rx) (hδ1 : δ ≤ 1) (hδ0 : 0 ≤ δ) {c : S → ℕ}
    (h : ∑ s, ((c s : ℝ) / V - z s) ^ 2 ≤ δ ^ 2) (s : S) : (c s : ℝ) ≤ (Rx + 1) * V := by
  have h1 : ((c s : ℝ) / V - z s) ^ 2 ≤ 1 := by
    refine le_trans (Finset.single_le_sum (f := fun s => ((c s : ℝ) / V - z s) ^ 2)
      (fun s _ => sq_nonneg _) (Finset.mem_univ s)) (le_trans h ?_)
    nlinarith
  have h2 : (c s : ℝ) / V - z s ≤ 1 := by nlinarith [sq_nonneg ((c s : ℝ) / V - z s - 1)]
  have h3 : (c s : ℝ) / V ≤ Rx + 1 := by linarith [hz s]
  rwa [div_le_iff₀ hV] at h3

theorem mem_ballSet {V Rx δ : ℝ} (hV : 0 < V) {z : Concentration S} (hz : ∀ s, z s ≤ Rx)
    (hδ1 : δ ≤ 1) (hδ0 : 0 ≤ δ) {c : S → ℕ} :
    c ∈ ballSet V Rx z δ ↔ ∑ s, ((c s : ℝ) / V - z s) ^ 2 ≤ δ ^ 2 := by
  classical
  unfold ballSet
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rw [Fintype.mem_piFinset]
  intro s
  rw [Finset.mem_range, Nat.lt_succ_iff]
  have := coord_le_of_dist_le hV hz hδ1 hδ0 h s
  rw [mul_comm] at this
  exact_mod_cast this.trans (Nat.le_ceil _)

/-- Velocity bound: `|x_s(τ₀ + σ) − x_s(τ₀)| ≤ √F · σ` when `∑ f² ≤ F` along the solution. -/
theorem sq_sub_le_of_field_bound (N : Network S) (κ : RateConstants N) {T F : ℝ}
    (x : ℝ → Concentration S) (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (N.massActionVectorField κ (x t)) t)
    (hF : ∀ t ∈ Ioo 0 T, ∑ s, N.massActionVectorField κ (x t) s ^ 2 ≤ F)
    {τ₀ σ : ℝ} (hτ₀ : 0 ≤ τ₀) (hσ : 0 ≤ σ) (hT : τ₀ + σ ≤ T) :
    ∑ s, (x (τ₀ + σ) s - x τ₀ s) ^ 2 ≤ (Fintype.card S : ℝ) * F * σ ^ 2 := by
  rcases hσ.eq_or_lt with h0 | hσpos
  · rw [← h0]
    simp
  have hcoord : ∀ s, (x (τ₀ + σ) s - x τ₀ s) ^ 2 ≤ F * σ ^ 2 := by
    intro s
    have hlt : τ₀ < τ₀ + σ := by linarith
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (fun τ => x τ s)
      (fun τ => N.massActionVectorField κ (x τ) s) hlt
      (((continuous_apply s).comp_continuousOn hxc).mono (Icc_subset_Icc hτ₀ hT))
      (fun τ hτ => (hasDerivAt_pi.mp (hx τ ⟨lt_of_le_of_lt hτ₀ hτ.1, lt_of_lt_of_le hτ.2 hT⟩)) s)
    have hξT : ξ ∈ Ioo 0 T := ⟨lt_of_le_of_lt hτ₀ hξ.1, lt_of_lt_of_le hξ.2 hT⟩
    have hdiff : x (τ₀ + σ) s - x τ₀ s = N.massActionVectorField κ (x ξ) s * σ := by
      rw [hslope, show τ₀ + σ - τ₀ = σ by ring, div_mul_cancel₀ _ hσpos.ne']
    rw [hdiff, mul_pow]
    have h1 : N.massActionVectorField κ (x ξ) s ^ 2 ≤ F := le_trans
      (Finset.single_le_sum (f := fun s => N.massActionVectorField κ (x ξ) s ^ 2)
        (fun s _ => sq_nonneg _) (Finset.mem_univ s)) (hF ξ hξT)
    exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  calc ∑ s, (x (τ₀ + σ) s - x τ₀ s) ^ 2 ≤ ∑ _s : S, F * σ ^ 2 := Finset.sum_le_sum fun s _ =>
        hcoord s
    _ = (Fintype.card S : ℝ) * F * σ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

set_option maxHeartbeats 1600000 in
/-- **Exit estimate.** For the chain started at `c` and frozen outside the ball
`B = {|·/V − x(τ₀)|² ≤ δ²}`, the mass outside `B` at time `h` is at most
`(4/δ²) · gronwallBound(|c/V − x(τ₀)|², C₁, C₂/V, h)`, provided `x` moves by less than `δ/2`
during `[τ₀, τ₀ + h]` (`4 |S| F h² ≤ δ²`). -/
theorem exit_mass_le (N : Network S) (κ : RateConstants N) {T Rx δ : ℝ} (hRx : 0 ≤ Rx)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (x : ℝ → Concentration S) (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (N.massActionVectorField κ (x t)) t)
    (hxB : ∀ t ∈ Icc 0 T, x t ∈ Icc (0 : Concentration S) fun _ => Rx) :
    ∃ C₁ C₂ F : ℝ, 1 ≤ C₁ ∧ 0 ≤ C₂ ∧ 0 ≤ F ∧
      (∀ t ∈ Icc 0 T, ∑ s, N.massActionVectorField κ (x t) s ^ 2 ≤ F) ∧
      ∀ (V : ℝ) (hV : 1 ≤ V) (τ₀ h : ℝ), 0 ≤ τ₀ → 0 ≤ h → τ₀ + h ≤ T →
        4 * (Fintype.card S : ℝ) * F * h ^ 2 ≤ δ ^ 2 → ∀ c : S → ℕ,
        ∑' b, (if b ∈ ballSet V Rx (x τ₀) δ then 0 else
            ((N.jumpSystem (N.volumeScale κ V (by linarith))).stopOutside
              (ballSet V Rx (x τ₀) δ)).Pmin h c b) ≤
          4 / δ ^ 2 * gronwallBound (∑ s, ((c s : ℝ) / V - x τ₀ s) ^ 2) C₁ (C₂ / V) h := by
  classical
  set d := (Fintype.card S : ℝ) with hd
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  set R₁ := Rx + 1 with hR₁
  have hR₁0 : 0 ≤ R₁ := by linarith
  obtain ⟨L, hL⟩ := ((N.contDiff_massActionVectorField κ).contDiffOn
    (s := Icc (0 : Concentration S) fun _ => R₁)).exists_lipschitzOnWith
    (by simp) (convex_Icc _ _) isCompact_Icc
  obtain ⟨F2, hF2⟩ := (isCompact_Icc (a := (0 : Concentration S)) (b := fun _ => R₁)).exists_bound_of_continuousOn
    (f := fun z => ∑ s, N.massActionVectorField κ z s ^ 2)
    (continuous_finsetSum _ fun s _ =>
      ((continuous_apply s).comp (N.contDiff_massActionVectorField κ).continuous).pow 2).continuousOn
  set F := max F2 0 with hFdef
  have hF0 : 0 ≤ F := le_max_right _ _
  have hFbox : ∀ z ∈ Icc (0 : Concentration S) (fun _ => R₁),
      ∑ s, N.massActionVectorField κ z s ^ 2 ≤ F := fun z hz =>
    (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hF2 z hz).trans (le_max_left _ _))
  have hxB' : ∀ t ∈ Icc 0 T, x t ∈ Icc (0 : Concentration S) fun _ => R₁ := fun t ht =>
    ⟨(hxB t ht).1, fun s => ((hxB t ht).2 s).trans (by linarith)⟩
  set C₁ := 1 + 2 * d * L + 4 * F / δ ^ 2 with hC₁
  set C₂ := d * N.rateErr κ R₁ ^ 2 + N.noiseConst κ R₁ with hC₂
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hC₁1 : 1 + 4 * F / δ ^ 2 ≤ C₁ := by
    have : (0 : ℝ) ≤ 2 * d * L := by positivity
    linarith
  have hC₁0 : 0 ≤ C₁ := by
    have : 0 ≤ 4 * F / δ ^ 2 := by positivity
    linarith
  have hC₂0 : 0 ≤ C₂ := by
    refine add_nonneg (by positivity) (Finset.sum_nonneg fun r _ => mul_nonneg
      (mul_nonneg (κ.positive r).le (by positivity)) (Finset.sum_nonneg fun s _ => sq_nonneg _))
  have hC₁one : 1 ≤ C₁ := by
    have : 0 ≤ 4 * F / δ ^ 2 := by positivity
    linarith
  refine ⟨C₁, C₂, F, hC₁one, hC₂0, hF0, fun t ht => hFbox _ (hxB' t ht),
    fun V hV τ₀ h hτ₀ hh hτh hsmall c => ?_⟩
  have hV0 : 0 < V := by linarith
  have hC₁ne : C₁ ≠ 0 := by
    have : 0 ≤ 4 * F / δ ^ 2 := by positivity
    linarith
  set z₀ := x τ₀ with hz₀
  have hz₀B : ∀ s, z₀ s ≤ Rx := (hxB τ₀ ⟨hτ₀, by linarith⟩).2
  set K := ballSet V Rx z₀ δ with hK
  set J := N.jumpSystem (N.volumeScale κ V hV0) with hJ
  set Js := J.stopOutside K with hJs
  set g₀ : (S → ℕ) → ℝ := fun b => ∑ s, ((b s : ℝ) / V - z₀ s) ^ 2 with hg₀
  have hg₀0 : ∀ b, 0 ≤ g₀ b := fun b => Finset.sum_nonneg fun s _ => sq_nonneg _
  have hgron : g₀ c ≤ gronwallBound (g₀ c) C₁ (C₂ / V) h := by
    rw [gronwallBound_of_K_ne_0 hC₁ne]
    have h1 : 1 ≤ Real.exp (C₁ * h) := Real.one_le_exp (mul_nonneg hC₁0 hh)
    have h2 : 0 ≤ C₂ / V / C₁ := div_nonneg (div_nonneg hC₂0 hV0.le) hC₁0
    nlinarith [hg₀0 c]
  have hPs : ∀ a, Summable fun b => Js.Pmin h a b := fun a =>
    summable_of_sum_le (fun b => Js.Pmin_nonneg h hh a b) fun F => Js.sum_Pmin_le_one h hh a F
  have hmask : ∀ a, Summable fun b => if b ∈ K then (0 : ℝ) else Js.Pmin h a b := fun a =>
    Summable.of_nonneg_of_le (fun b => by split_ifs <;> simp [Js.Pmin_nonneg h hh a b])
      (fun b => by split_ifs <;> simp [Js.Pmin_nonneg h hh a b]) (hPs a)
  by_cases hcK : c ∉ K
  · -- already outside
    have hfar : δ ^ 2 < g₀ c := by
      by_contra hle; push Not at hle
      exact hcK ((mem_ballSet hV0 hz₀B hδ1 hδ.le).mpr hle)
    calc ∑' b, (if b ∈ K then 0 else Js.Pmin h c b) ≤ ∑' b, Js.Pmin h c b :=
          (hmask c).tsum_le_tsum (fun b => by split_ifs <;> simp [Js.Pmin_nonneg h hh c b]) (hPs c)
      _ ≤ 1 := (hPs c).tsum_le_of_sum_le fun F => Js.sum_Pmin_le_one h hh c F
      _ ≤ 4 / δ ^ 2 * g₀ c := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hδ2]; linarith
      _ ≤ 4 / δ ^ 2 * gronwallBound (g₀ c) C₁ (C₂ / V) h :=
          mul_le_mul_of_nonneg_left hgron (by positivity)
  push Not at hcK
  set Rset := J.frozenReach K c with hRset
  have hsupp : ∀ τ, ∀ b, b ∉ Rset → Js.Pmin τ c b = 0 := fun τ b hb =>
    J.Pmin_stop_eq_zero K τ hb
  have hclosed := J.frozenReach_closed K c
  have hcR : c ∈ Rset := Finset.mem_insert_self _ _
  -- the moving observable
  set g : ℝ → (S → ℕ) → ℝ := fun σ b => ∑ s, ((b s : ℝ) / V - x (τ₀ + σ) s) ^ 2 with hg
  have hg0 : ∀ σ b, 0 ≤ g σ b := fun σ b => Finset.sum_nonneg fun s _ => sq_nonneg _
  set g' : ℝ → (S → ℕ) → ℝ := fun σ b =>
    ∑ s, 2 * ((b s : ℝ) / V - x (τ₀ + σ) s) * -(N.massActionVectorField κ (x (τ₀ + σ)) s)
    with hg'
  set D : ℝ → ℝ := fun σ => ∑ b ∈ Rset, Js.Pmin σ c b * g σ b with hD
  have hxshift : ∀ σ ∈ Ioo 0 h, HasDerivAt (fun σ => x (τ₀ + σ))
      (N.massActionVectorField κ (x (τ₀ + σ))) σ := by
    intro σ hσ
    have h1 : τ₀ + σ ∈ Ioo 0 T := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    have hin : HasDerivAt (fun σ : ℝ => τ₀ + σ) 1 σ := by
      simpa using (hasDerivAt_id σ).const_add τ₀
    have hg : HasDerivAt x (N.massActionVectorField κ (x (τ₀ + σ))) ((fun σ : ℝ => τ₀ + σ) σ) :=
      hx (τ₀ + σ) h1
    have := hg.scomp σ hin
    rw [one_smul] at this
    exact this
  have hgder : ∀ σ ∈ Ioo 0 h, ∀ b, HasDerivAt (fun σ => g σ b) (g' σ b) σ := by
    intro σ hσ b
    have hxσ := hasDerivAt_pi.mp (hxshift σ hσ)
    refine HasDerivAt.fun_sum fun s _ => ?_
    have h1 : HasDerivAt (fun σ => (b s : ℝ) / V - x (τ₀ + σ) s)
        (-(N.massActionVectorField κ (x (τ₀ + σ)) s)) σ := by
      simpa using (hxσ s).const_sub ((b s : ℝ) / V)
    convert h1.pow 2 using 1
    push_cast; ring
  have hDder : ∀ σ ∈ Ioo 0 h, HasDerivAt D
      (∑ b ∈ Rset, Js.Pmin σ c b * (Js.drift (g σ) b + g' σ b)) σ := fun σ hσ =>
    Js.hasDerivAt_sum_finite c Rset hsupp hclosed g g' hσ.1 fun b _ => hgder σ hσ b
  -- frozen states stay at distance `δ/2`
  have hmove : ∀ σ ∈ Icc 0 h, ∑ s, (x (τ₀ + σ) s - z₀ s) ^ 2 ≤ δ ^ 2 / 4 := by
    intro σ hσ
    have hFI : ∀ t ∈ Ioo 0 T, ∑ s, N.massActionVectorField κ (x t) s ^ 2 ≤ F := fun t ht =>
      hFbox _ (hxB' t (Ioo_subset_Icc_self ht))
    have := sq_sub_le_of_field_bound N κ x hxc hx hFI hτ₀ hσ.1 (by linarith [hσ.2])
    have hσ2 : σ ^ 2 ≤ h ^ 2 := pow_le_pow_left₀ hσ.1 hσ.2 2
    have : d * F * σ ^ 2 ≤ d * F * h ^ 2 := mul_le_mul_of_nonneg_left hσ2 (by positivity)
    linarith
  have hfrozen : ∀ σ ∈ Icc 0 h, ∀ b, b ∉ K → δ ^ 2 / 4 ≤ g σ b := by
    intro σ hσ b hb
    have hfar : δ ^ 2 < g₀ b := by
      by_contra hle; push Not at hle
      exact hb ((mem_ballSet hV0 hz₀B hδ1 hδ.le).mpr hle)
    have hm := hmove σ hσ
    have htri : g₀ b ≤ 2 * g σ b + 2 * ∑ s, (x (τ₀ + σ) s - z₀ s) ^ 2 := by
      simp only [hg₀, hg, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun s _ => ?_
      nlinarith [sq_nonneg ((b s : ℝ) / V - x (τ₀ + σ) s - (x (τ₀ + σ) s - z₀ s))]
    linarith
  have hpt : ∀ σ ∈ Ioo 0 h, ∀ b ∈ Rset, Js.drift (g σ) b + g' σ b ≤ C₁ * g σ b + C₂ / V := by
    intro σ hσ b _
    have hσI : σ ∈ Icc 0 h := Ioo_subset_Icc_self hσ
    have hxσB : x (τ₀ + σ) ∈ Icc (0 : Concentration S) fun _ => R₁ :=
      hxB' (τ₀ + σ) ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    have hgb := hg0 σ b
    rw [JumpSystem.drift_stopOutside]
    split_ifs with hbK
    · have hball := (mem_ballSet hV0 hz₀B hδ1 hδ.le).mp hbK
      have hcoord : ∀ s, (b s : ℝ) ≤ R₁ * V := coord_le_of_dist_le hV0 hz₀B hδ1 hδ.le hball
      have h1 := N.drift_dist_sq_le κ hV hR₁0 le_rfl hL b hcoord (x (τ₀ + σ)) hxσB
      have hle : (1 + 2 * Fintype.card S * L) * g σ b ≤ C₁ * g σ b := by
        apply mul_le_mul_of_nonneg_right _ hgb
        have : 0 ≤ 4 * F / δ ^ 2 := by positivity
        simp only [hC₁, hd]; linarith
      have e : J.drift (g σ) b + g' σ b ≤ (1 + 2 * Fintype.card S * L) * g σ b + C₂ / V := h1
      linarith
    · have h1 := hfrozen σ hσI b hbK
      have hgg : g' σ b ≤ g σ b + ∑ s, N.massActionVectorField κ (x (τ₀ + σ)) s ^ 2 := by
        simp only [hg', hg, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun s _ => ?_
        nlinarith [sq_nonneg ((b s : ℝ) / V - x (τ₀ + σ) s +
          N.massActionVectorField κ (x (τ₀ + σ)) s)]
      have hF := hFbox _ hxσB
      have hFg : F ≤ 4 * F / δ ^ 2 * g σ b := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hδ2]
        nlinarith
      have hC1g : (1 + 4 * F / δ ^ 2) * g σ b ≤ C₁ * g σ b := mul_le_mul_of_nonneg_right hC₁1 hgb
      have : 0 ≤ C₂ / V := div_nonneg hC₂0 hV0.le
      nlinarith
  have hbound : ∀ σ ∈ Ioo 0 h,
      ∑ b ∈ Rset, Js.Pmin σ c b * (Js.drift (g σ) b + g' σ b) ≤ C₁ * D σ + C₂ / V := by
    intro σ hσ
    calc ∑ b ∈ Rset, Js.Pmin σ c b * (Js.drift (g σ) b + g' σ b)
        ≤ ∑ b ∈ Rset, Js.Pmin σ c b * (C₁ * g σ b + C₂ / V) :=
          Finset.sum_le_sum fun b hb => mul_le_mul_of_nonneg_left (hpt σ hσ b hb)
            (Js.Pmin_nonneg σ hσ.1.le c b)
      _ = C₁ * D σ + C₂ / V * ∑ b ∈ Rset, Js.Pmin σ c b := by
          simp only [hD, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
          congr 1 <;> exact Finset.sum_congr rfl fun b _ => by ring
      _ ≤ C₁ * D σ + C₂ / V := by
          have h1 := Js.sum_Pmin_le_one σ hσ.1.le c Rset
          have h2 : 0 ≤ C₂ / V := div_nonneg hC₂0 hV0.le
          nlinarith
  have hDc : ContinuousOn D (Icc 0 h) := by
    refine continuousOn_finsetSum _ fun b _ => ?_
    refine ((Js.continuousOn_Pmin c b).mono fun σ hσ => hσ.1).mul ?_
    refine continuousOn_finsetSum _ fun s _ => ?_
    refine (continuousOn_const.sub ?_).pow 2
    have hc1 : ContinuousOn (fun σ : ℝ => τ₀ + σ) (Icc 0 h) := (continuous_const.add continuous_id).continuousOn
    have hmaps : MapsTo (fun σ : ℝ => τ₀ + σ) (Icc 0 h) (Icc 0 T) := fun σ hσ =>
      ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    exact (continuous_apply s).comp_continuousOn (hxc.comp hc1 hmaps)
  have hD0 : D 0 = g₀ c := by
    simp only [hD, JumpSystem.Pmin_zero]
    rw [Finset.sum_eq_single c (fun b _ hb => by rw [if_neg (Ne.symm hb), zero_mul])
      (fun h => absurd hcR h)]
    simp [hg, hg₀, hz₀]
  have hDh : D h ≤ gronwallBound (g₀ c) C₁ (C₂ / V) h := by
    have := le_gronwallBound_of_hasDerivAt_Ioo hC₁ne hDc hDder hbound ⟨hh, le_rfl⟩
    rwa [hD0] at this
  -- the exit mass
  have hexit : ∑' b, (if b ∈ K then 0 else Js.Pmin h c b) =
      ∑ b ∈ Rset.filter (fun b => b ∉ K), Js.Pmin h c b := by
    rw [tsum_eq_sum (s := Rset) (fun b hb => by simp [hsupp h b hb]), Finset.sum_filter]
    exact Finset.sum_congr rfl fun b _ => by split_ifs <;> simp_all
  rw [hexit]
  calc ∑ b ∈ Rset.filter (fun b => b ∉ K), Js.Pmin h c b
      ≤ ∑ b ∈ Rset.filter (fun b => b ∉ K), Js.Pmin h c b * (4 / δ ^ 2 * g h b) := by
        refine Finset.sum_le_sum fun b hb => ?_
        have h1 := hfrozen h ⟨hh, le_rfl⟩ b (Finset.mem_filter.mp hb).2
        have h2 : 1 ≤ 4 / δ ^ 2 * g h b := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hδ2]; linarith
        exact le_mul_of_one_le_right (Js.Pmin_nonneg h hh c b) h2
    _ = 4 / δ ^ 2 * ∑ b ∈ Rset.filter (fun b => b ∉ K), Js.Pmin h c b * g h b := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
    _ ≤ 4 / δ ^ 2 * D h := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun b _ _ => mul_nonneg (Js.Pmin_nonneg h hh c b) (hg0 h b)
    _ ≤ 4 / δ ^ 2 * gronwallBound (g₀ c) C₁ (C₂ / V) h :=
        mul_le_mul_of_nonneg_left hDh (by positivity)

/-- `min(1, a ψ + β) ≤ max(1, a) · min(ψ, 1) + β`. -/
theorem min_one_affine_le {a ψ β : ℝ} (ha : 0 ≤ a) (hψ : 0 ≤ ψ) (hβ : 0 ≤ β) :
    min 1 (a * ψ + β) ≤ max 1 a * min ψ 1 + β := by
  rcases le_total ψ 1 with h | h
  · rw [min_eq_left h]
    have h1 : min 1 (a * ψ + β) ≤ a * ψ + β := min_le_right _ _
    have h2 : a * ψ ≤ max 1 a * ψ := mul_le_mul_of_nonneg_right (le_max_right _ _) hψ
    linarith
  · rw [min_eq_right h, mul_one]
    have h1 : min 1 (a * ψ + β) ≤ 1 := min_le_left _ _
    linarith [le_max_left 1 a]

set_option maxHeartbeats 1600000 in
/-- **Kurtz's law of large numbers uniform in time, exit-mass formulation, any network.**
There is a partition of `[0, T]` into `m` intervals of length `h = T/m`, on each of which `x`
moves by less than `δ/2`, such that the total mass leaving the balls
`{|·/V − x(i h)|² ≤ δ²}` during the corresponding intervals tends to `0` as `V → ∞`. -/
theorem kurtz_lln_uniform (N : Network S) (κ : RateConstants N) {T Rx δ : ℝ} (hT : 0 < T)
    (hRx : 0 ≤ Rx) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (x : ℝ → Concentration S) (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (N.massActionVectorField κ (x t)) t)
    (hxB : ∀ t ∈ Icc 0 T, x t ∈ Icc (0 : Concentration S) fun _ => Rx)
    (n : ℕ → S → ℕ)
    (hn0 : Tendsto (fun k => ∑ s, ((n k s : ℝ) / ((k : ℝ) + 1) - x 0 s) ^ 2) atTop (𝓝 0)) :
    ∃ m : ℕ, 0 < m ∧
      (∀ i < m, ∀ σ ∈ Icc 0 (T / m),
        ∑ s, (x (i * (T / m) + σ) s - x (i * (T / m)) s) ^ 2 ≤ δ ^ 2 / 4) ∧
      Tendsto (fun k : ℕ => ∑ i ∈ Finset.range m,
        ∑' c, N.transition (N.volumeScale κ ((k : ℝ) + 1) (by positivity)) (i * (T / m)) (n k) c *
          ∑' b, (if b ∈ ballSet ((k : ℝ) + 1) Rx (x (i * (T / m))) δ then 0 else
            ((N.jumpSystem (N.volumeScale κ ((k : ℝ) + 1) (by positivity))).stopOutside
              (ballSet ((k : ℝ) + 1) Rx (x (i * (T / m))) δ)).Pmin (T / m) c b)) atTop (𝓝 0) := by
  classical
  obtain ⟨C₁, C₂, F, hC₁, hC₂, hF0, hFx, hexit⟩ := N.exit_mass_le κ hRx hδ hδ1 x hxc hx hxB
  set d := (Fintype.card S : ℝ) with hd
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  set m : ℕ := ⌈4 * d * F * T ^ 2 / δ ^ 2⌉₊ + 1 with hm
  have hm1 : (1 : ℝ) ≤ m := by rw [hm]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈4 * d * F * T ^ 2 / δ ^ 2⌉₊]
  have hm0 : 0 < m := by rw [hm]; omega
  have hmpos : (0 : ℝ) < m := by linarith
  set h := T / m with hh
  have hh0 : 0 ≤ h := div_nonneg hT.le hmpos.le
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hsmall : 4 * d * F * h ^ 2 ≤ δ ^ 2 := by
    have hceil : 4 * d * F * T ^ 2 / δ ^ 2 ≤ m := by
      rw [hm]; push_cast
      linarith [Nat.le_ceil (4 * d * F * T ^ 2 / δ ^ 2)]
    have h1 : 4 * d * F * T ^ 2 ≤ δ ^ 2 * m := by
      have := (div_le_iff₀ hδ2).mp hceil
      linarith
    have h2 : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
    rw [hh, div_pow]
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    have : 0 ≤ δ ^ 2 := hδ2.le
    nlinarith
  have hti : ∀ i < m, 0 ≤ (i : ℝ) * h ∧ (i : ℝ) * h + h ≤ T := by
    intro i hi
    refine ⟨mul_nonneg (Nat.cast_nonneg _) hh0, ?_⟩
    have : ((i : ℝ) + 1) ≤ m := by exact_mod_cast hi
    calc (i : ℝ) * h + h = ((i : ℝ) + 1) * h := by ring
      _ ≤ m * h := mul_le_mul_of_nonneg_right this hh0
      _ = T := by rw [hh]; field_simp
  refine ⟨m, hm0, ?_, ?_⟩
  · intro i hi σ hσ
    obtain ⟨h1, h2⟩ := hti i hi
    have hFI : ∀ t ∈ Ioo 0 T, ∑ s, N.massActionVectorField κ (x t) s ^ 2 ≤ F := fun t ht =>
      hFx t (Ioo_subset_Icc_self ht)
    have := sq_sub_le_of_field_bound N κ x hxc hx hFI h1 hσ.1 (by linarith [hσ.2])
    have hσ2 : σ ^ 2 ≤ h ^ 2 := pow_le_pow_left₀ hσ.1 hσ.2 2
    have : d * F * σ ^ 2 ≤ d * F * h ^ 2 := mul_le_mul_of_nonneg_left hσ2 (by positivity)
    linarith
  -- each interval
  have hV : ∀ k : ℕ, (1 : ℝ) ≤ (k : ℝ) + 1 := fun k => by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  set A := Real.exp (C₁ * h) with hA
  set B := (Real.exp (C₁ * h) - 1) / C₁ with hB
  have hA0 : 0 ≤ A := (Real.exp_pos _).le
  have hA1 : 1 ≤ A := Real.one_le_exp (mul_nonneg (by linarith) hh0)
  have hB0 : 0 ≤ B := div_nonneg (by linarith) (by linarith)
  set A' := max 1 (4 / δ ^ 2 * A) with hA'
  have hC₁ne : C₁ ≠ 0 := by linarith
  have hterm : ∀ i < m, Tendsto (fun k : ℕ =>
      ∑' c, N.transition (N.volumeScale κ ((k : ℝ) + 1) (by positivity)) (i * h) (n k) c *
        ∑' b, (if b ∈ ballSet ((k : ℝ) + 1) Rx (x (i * h)) δ then 0 else
          ((N.jumpSystem (N.volumeScale κ ((k : ℝ) + 1) (by positivity))).stopOutside
            (ballSet ((k : ℝ) + 1) Rx (x (i * h)) δ)).Pmin h c b)) atTop (𝓝 0) := by
    intro i hi
    obtain ⟨h1, h2⟩ := hti i hi
    have htI : (i : ℝ) * h ∈ Icc 0 T := ⟨h1, by linarith⟩
    have hE := N.kurtz_lln_tendsto κ hRx x hxc hx hxB n hn0 htI
    have hden : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    have hβ : Tendsto (fun k : ℕ => 4 / δ ^ 2 * (C₂ * B) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden
    have hup := (hE.const_mul A').add hβ
    rw [mul_zero, add_zero] at hup
    refine squeeze_zero (fun k => ?_) (fun k => ?_) hup
    · refine tsum_nonneg fun c => mul_nonneg ((N.jumpSystem _).Pmin_nonneg _ h1 _ _) ?_
      refine tsum_nonneg fun b => ?_
      split_ifs
      · exact le_rfl
      · exact JumpSystem.Pmin_nonneg _ _ hh0 _ _
    · set V := (k : ℝ) + 1 with hVdef
      have hV0 : 0 < V := by positivity
      set J := N.jumpSystem (N.volumeScale κ V hV0)
      set Kb := ballSet V Rx (x (i * h)) δ
      set E : (S → ℕ) → ℝ := fun c => ∑' b, (if b ∈ Kb then 0 else
        (J.stopOutside Kb).Pmin h c b) with hE'
      set ψ : (S → ℕ) → ℝ := fun c => ∑ s, ((c s : ℝ) / V - x (i * h) s) ^ 2 with hψ
      have hψ0 : ∀ c, 0 ≤ ψ c := fun c => Finset.sum_nonneg fun s _ => sq_nonneg _
      have hP0 : ∀ c, 0 ≤ J.Pmin (i * h) (n k) c := fun c => J.Pmin_nonneg _ h1 _ _
      have hPs : Summable fun c => J.Pmin (i * h) (n k) c :=
        summable_of_sum_le hP0 fun F => J.sum_Pmin_le_one _ h1 _ F
      have hP1 : ∑' c, J.Pmin (i * h) (n k) c ≤ 1 :=
        hPs.tsum_le_of_sum_le fun F => J.sum_Pmin_le_one _ h1 _ F
      have hEs : ∀ c, Summable fun b => if b ∈ Kb then (0 : ℝ) else (J.stopOutside Kb).Pmin h c b :=
        fun c => Summable.of_nonneg_of_le
          (fun b => by split_ifs <;> simp [(J.stopOutside Kb).Pmin_nonneg h hh0 c b])
          (fun b => by split_ifs <;> simp [(J.stopOutside Kb).Pmin_nonneg h hh0 c b])
          (summable_of_sum_le (fun b => (J.stopOutside Kb).Pmin_nonneg h hh0 c b)
            fun F => (J.stopOutside Kb).sum_Pmin_le_one h hh0 c F)
      have hE0 : ∀ c, 0 ≤ E c := fun c => tsum_nonneg fun b => by
        split_ifs
        · exact le_rfl
        · exact (J.stopOutside Kb).Pmin_nonneg h hh0 c b
      have hE1 : ∀ c, E c ≤ 1 := by
        intro c
        calc E c ≤ ∑' b, (J.stopOutside Kb).Pmin h c b :=
              (hEs c).tsum_le_tsum (fun b => by
                split_ifs <;> simp [(J.stopOutside Kb).Pmin_nonneg h hh0 c b])
                (summable_of_sum_le (fun b => (J.stopOutside Kb).Pmin_nonneg h hh0 c b)
                  fun F => (J.stopOutside Kb).sum_Pmin_le_one h hh0 c F)
          _ ≤ 1 := (summable_of_sum_le (fun b => (J.stopOutside Kb).Pmin_nonneg h hh0 c b)
                fun F => (J.stopOutside Kb).sum_Pmin_le_one h hh0 c F).tsum_le_of_sum_le
                fun F => (J.stopOutside Kb).sum_Pmin_le_one h hh0 c F
      have hEle : ∀ c, E c ≤ A' * min (ψ c) 1 + 4 / δ ^ 2 * (C₂ * B) / V := by
        intro c
        have hx1 := hexit V (hV k) (i * h) h h1 hh0 h2 hsmall c
        rw [gronwallBound_of_K_ne_0 hC₁ne] at hx1
        have hEq : 4 / δ ^ 2 * (ψ c * Real.exp (C₁ * h) + C₂ / V / C₁ * (Real.exp (C₁ * h) - 1)) =
            (4 / δ ^ 2 * A) * ψ c + 4 / δ ^ 2 * (C₂ * B) / V := by
          rw [hA, hB]; field_simp
        have h3 : E c ≤ min 1 ((4 / δ ^ 2 * A) * ψ c + 4 / δ ^ 2 * (C₂ * B) / V) :=
          le_min (hE1 c) (by rw [← hEq]; exact hx1)
        refine h3.trans (min_one_affine_le (by positivity) (hψ0 c) (by positivity))
      have hsum1 : Summable fun c => J.Pmin (i * h) (n k) c * min (ψ c) 1 :=
        Summable.of_nonneg_of_le (fun c => mul_nonneg (hP0 c) (le_min (hψ0 c) zero_le_one))
          (fun c => mul_le_of_le_one_right (hP0 c) (min_le_right _ _)) hPs
      calc ∑' c, J.Pmin (i * h) (n k) c * E c
          ≤ ∑' c, (A' * (J.Pmin (i * h) (n k) c * min (ψ c) 1) +
              4 / δ ^ 2 * (C₂ * B) / V * J.Pmin (i * h) (n k) c) := by
            refine (Summable.of_nonneg_of_le (fun c => mul_nonneg (hP0 c) (hE0 c))
              (fun c => mul_le_of_le_one_right (hP0 c) (hE1 c)) hPs).tsum_le_tsum
              (fun c => ?_) ((hsum1.mul_left _).add (hPs.mul_left _))
            have := mul_le_mul_of_nonneg_left (hEle c) (hP0 c)
            linarith
        _ = A' * ∑' c, J.Pmin (i * h) (n k) c * min (ψ c) 1 +
              4 / δ ^ 2 * (C₂ * B) / V * ∑' c, J.Pmin (i * h) (n k) c := by
            rw [(hsum1.mul_left _).tsum_add (hPs.mul_left _), tsum_mul_left, tsum_mul_left]
        _ ≤ A' * ∑' c, J.Pmin (i * h) (n k) c * min (ψ c) 1 + 4 / δ ^ 2 * (C₂ * B) / V := by
            have : 0 ≤ 4 / δ ^ 2 * (C₂ * B) / V := by positivity
            nlinarith
  have htot := tendsto_finset_sum (Finset.range m) fun i hi => hterm i (Finset.mem_range.mp hi)
  simpa using htot

end Network

namespace Examples
namespace Cubic

open Network

/-- **Uniform-in-time instance for `2X → 3X`, `3X → 2X`** at the equilibrium `x* = 1`, `δ = 1/2`. -/
theorem lln_uniform :
    ∃ m : ℕ, 0 < m ∧
      Tendsto (fun k : ℕ => ∑ i ∈ Finset.range m,
        ∑' c, net.transition (net.volumeScale κ ((k : ℝ) + 1) (by positivity)) (i * (1 / m))
            (fun _ => k + 1) c *
          ∑' b, (if b ∈ ballSet ((k : ℝ) + 1) 1 xstar (1 / 2) then 0 else
            ((net.jumpSystem (net.volumeScale κ ((k : ℝ) + 1) (by positivity))).stopOutside
              (ballSet ((k : ℝ) + 1) 1 xstar (1 / 2))).Pmin (1 / m) c b)) atTop (𝓝 0) := by
  obtain ⟨m, hm, -, h⟩ := kurtz_lln_uniform net κ (T := 1) (Rx := 1) (δ := 1 / 2) one_pos
    (by norm_num) (by norm_num) (by norm_num) (fun _ => xstar) continuousOn_const
    (fun t _ => by rw [equilibrium]; exact hasDerivAt_const _ _)
    (fun t _ => ⟨fun _ => by simp [xstar], fun _ => le_refl _⟩) (fun k _ => k + 1) (by
      have h : ∀ k : ℕ, ∑ s, ((((fun _ : Fin 1 => k + 1) s : ℕ) : ℝ) / ((k : ℝ) + 1) -
          xstar s) ^ 2 = 0 := by
        intro k
        have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
        simp [xstar, hk]
      simp only [h]
      exact tendsto_const_nhds)
  exact ⟨m, hm, h⟩

end Cubic
end Examples

end CRNT
