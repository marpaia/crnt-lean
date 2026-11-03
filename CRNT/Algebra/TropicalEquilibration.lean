import CRNT.Equilibria.SteadyState
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Tropical equilibration is necessary for scaled steady states

Tropical model reduction (Noel–Grigoriev–Vakulenko–Radulescu 2012; Samal–Grigoriev–Fröhlich–
Weber–Radulescu 2015) scales the rate constants of a mass-action system by powers of a small
parameter, `κ_r = κ̄_r ε^{a_r}`, and looks for steady states whose concentrations scale as
`x_s ≈ ε^{u_s}`. Each term of a steady-state equation then has order `a_r + ⟨y_r, u⟩`, and the
**tropical equilibration condition** at `u` says: in every equation, the minimal order is attained
by at least one positive term and at least one negative term. Otherwise a single sign dominates
for small `ε` and the equation cannot vanish.

This module proves that necessity statement.

* `Tropical.IsEquilibrated c e`: among the terms with nonzero coefficient, the minimum of the orders
  `e` is attained at a term with positive coefficient and at a term with negative coefficient.
* `Tropical.eventually_sum_pos_of_minimizers_pos`: the dominance estimate. If every minimal-order
  term is positive, then `∑ c_j exp(-L (e_j + η_j))` is eventually positive as `L → ∞`, `η → 0`.
* `Tropical.isEquilibrated_of_eventually_zero`: zeros of the scaled sums force equilibration.
* `Tropical.isEquilibrated_of_scaled_zeros`: the same for power-law polynomials
  `∑ c_j ε^{a_j} ∏ x_s^{m_{js}}` with a family of positive zeros `x(ε)` whose valuations
  `log x_s / log ε` converge to `u`.
* `Network.tropicalEquilibration_of_steadyStates`: for a mass-action network with rate constants
  `κ̄_r ε^{a_r}` and positive steady states `x(ε_n)` with valuations `u`, for every species `s`
  that some reaction changes, the minimum of `a_r + ⟨y_r, u⟩` over the reactions changing `s` is
  attained by a reaction producing `s` and by a reaction consuming `s`.

The converse direction (tropical equilibrations determine nearby steady states and give the
reduced models of Samal et al.) is not formalized.
-/

namespace CRNT

namespace Tropical

open Filter Topology Finset

variable {J : Type*} [Fintype J]

/-- **Tropical equilibration.** Among the indices with nonzero coefficient, the minimum of the
orders `e` is attained at an index with positive coefficient and at an index with negative
coefficient. -/
def IsEquilibrated (c e : J → ℝ) : Prop :=
  ∃ j₁ j₂, 0 < c j₁ ∧ c j₂ < 0 ∧ ∀ j, c j ≠ 0 → e j₁ ≤ e j ∧ e j₂ ≤ e j

/-- A positive gap separating the orders of the non-minimal nonzero terms from the minimum
`e j₀`. -/
theorem exists_gap (c e : J → ℝ) (j₀ : J) (hmin : ∀ j, c j ≠ 0 → e j₀ ≤ e j) :
    ∃ γ > 0, ∀ j, c j ≠ 0 → e j ≠ e j₀ → e j₀ + γ ≤ e j := by
  classical
  let D : Finset ℝ :=
    (univ.filter fun j => c j ≠ 0 ∧ e j ≠ e j₀).image fun j => e j - e j₀
  by_cases hD : D.Nonempty
  · refine ⟨D.min' hD, ?_, ?_⟩
    · obtain ⟨j, hj, hjeq⟩ := Finset.mem_image.mp (D.min'_mem hD)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      have := hmin j hj.1
      have hne := hj.2
      rw [← hjeq]
      exact sub_pos.mpr (lt_of_le_of_ne this (Ne.symm hne))
    · intro j hj hje
      have hmem : e j - e j₀ ∈ D :=
        Finset.mem_image.mpr ⟨j, by simp [hj, hje], rfl⟩
      have := D.min'_le _ hmem
      linarith
  · refine ⟨1, one_pos, fun j hj hje => ?_⟩
    exact absurd ⟨e j - e j₀, Finset.mem_image.mpr ⟨j, by simp [hj, hje], rfl⟩⟩ hD

/-- **Dominance of the minimal order.** Let `L n → ∞` and `η n j → 0`. If the index `j₀` has
positive coefficient and minimal order among the nonzero terms, and every nonzero term of minimal
order has positive coefficient, then `∑ j, c j * exp (-(L n * (e j + η n j)))` is eventually
positive. -/
theorem eventually_sum_pos_of_minimizers_pos (c e : J → ℝ) (L : ℕ → ℝ) (η : ℕ → J → ℝ)
    (hL : Tendsto L atTop atTop) (hη : ∀ j, Tendsto (fun n => η n j) atTop (𝓝 0))
    (j₀ : J) (hj₀ : 0 < c j₀) (hmin : ∀ j, c j ≠ 0 → e j₀ ≤ e j)
    (hpos : ∀ j, c j ≠ 0 → e j = e j₀ → 0 < c j) :
    ∀ᶠ n in atTop, 0 < ∑ j, c j * Real.exp (-(L n * (e j + η n j))) := by
  classical
  obtain ⟨γ, hγ, hgap⟩ := exists_gap c e j₀ hmin
  set C : ℝ := ∑ j, |c j| with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun j _ => abs_nonneg _
  -- the error terms are eventually small
  have hηsmall : ∀ᶠ n in atTop, ∀ j, |η n j| ≤ γ / 4 := by
    rw [eventually_all]
    intro j
    have := (hη j).eventually (Metric.closedBall_mem_nhds (0 : ℝ) (by positivity : 0 < γ / 4))
    filter_upwards [this] with n hn
    simpa [Metric.mem_closedBall, Real.dist_eq] using hn
  -- `C · exp(-L γ/2)` is eventually below `c j₀`
  have hexp : ∀ᶠ n in atTop, C * Real.exp (-(L n * (γ / 2))) < c j₀ := by
    have h1 : Tendsto (fun n => L n * (γ / 2)) atTop atTop :=
      hL.atTop_mul_const (by positivity)
    have h2 : Tendsto (fun n => C * Real.exp (-(L n * (γ / 2)))) atTop (𝓝 (C * 0)) :=
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul C
    rw [mul_zero] at h2
    exact h2.eventually (gt_mem_nhds hj₀)
  filter_upwards [hηsmall, hexp, hL.eventually_gt_atTop 0] with n hn hnexp hLpos
  set A : ℝ := Real.exp (-(L n * (e j₀ + γ / 4))) with hA
  set B : ℝ := Real.exp (-(L n * (e j₀ + 3 * γ / 4))) with hB
  have hA0 : 0 < A := Real.exp_pos _
  have hB0 : 0 < B := Real.exp_pos _
  have hBA : B = A * Real.exp (-(L n * (γ / 2))) := by
    rw [hA, hB, ← Real.exp_add]; congr 1; ring
  -- termwise lower bounds
  have hterm : ∀ j, (if j = j₀ then c j₀ * A + |c j₀| * B else 0) - |c j| * B ≤
      c j * Real.exp (-(L n * (e j + η n j))) := by
    intro j
    by_cases hj : j = j₀
    · subst hj
      simp only [↓reduceIte]
      have hle : -(L n * (e j + η n j)) ≥ -(L n * (e j + γ / 4)) := by
        have := (abs_le.mp (hn j)).1
        nlinarith [(abs_le.mp (hn j)).2]
      have := Real.exp_le_exp.mpr hle
      rw [abs_of_pos hj₀]
      nlinarith
    · simp only [hj, ↓reduceIte, zero_sub]
      by_cases hcj : c j = 0
      · simp [hcj]
      by_cases hej : e j = e j₀
      · have := hpos j hcj hej
        have : 0 ≤ c j * Real.exp (-(L n * (e j + η n j))) :=
          mul_nonneg this.le (Real.exp_pos _).le
        nlinarith [abs_nonneg (c j)]
      · have hge := hgap j hcj hej
        have hle : -(L n * (e j + η n j)) ≤ -(L n * (e j₀ + 3 * γ / 4)) := by
          have := (abs_le.mp (hn j)).1
          nlinarith
        have hexpj := Real.exp_le_exp.mpr hle
        have habs : -(|c j| * B) ≤ c j * Real.exp (-(L n * (e j + η n j))) := by
          have h1 : -(|c j|) ≤ c j := neg_abs_le _
          have hE0 := (Real.exp_pos (-(L n * (e j + η n j)))).le
          calc -(|c j| * B) ≤ -(|c j| * Real.exp (-(L n * (e j + η n j)))) := by
                nlinarith [abs_nonneg (c j)]
            _ = -(|c j|) * Real.exp (-(L n * (e j + η n j))) := by ring
            _ ≤ c j * Real.exp (-(L n * (e j + η n j))) :=
                mul_le_mul_of_nonneg_right h1 hE0
        exact habs
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ (univ : Finset J)) => hterm j
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' univ j₀] at hsum
  simp only [Finset.mem_univ, ↓reduceIte] at hsum
  rw [← Finset.sum_mul] at hsum
  have hkey : 0 < c j₀ * A + |c j₀| * B - C * B := by
    have : C * B < c j₀ * A := by
      rw [hBA]
      calc C * (A * Real.exp (-(L n * (γ / 2))))
          = A * (C * Real.exp (-(L n * (γ / 2)))) := by ring
        _ < A * c j₀ := mul_lt_mul_of_pos_left hnexp hA0
        _ = c j₀ * A := by ring
    nlinarith [abs_nonneg (c j₀)]
  rw [← hC] at hsum
  linarith

/-- **Tropical equilibration is necessary.** If the scaled sums
`∑ j, c j * exp (-(L n * (e j + η n j)))` vanish eventually, with `L n → ∞`, `η n j → 0`, and some
coefficient is nonzero, then `e` is a tropical equilibration: its minimum over the nonzero terms
is attained at a positive and at a negative coefficient. -/
theorem isEquilibrated_of_eventually_zero (c e : J → ℝ) (L : ℕ → ℝ) (η : ℕ → J → ℝ)
    (hL : Tendsto L atTop atTop) (hη : ∀ j, Tendsto (fun n => η n j) atTop (𝓝 0))
    (hz : ∀ᶠ n in atTop, ∑ j, c j * Real.exp (-(L n * (e j + η n j))) = 0)
    (hne : ∃ j, c j ≠ 0) : IsEquilibrated c e := by
  classical
  obtain ⟨j₀, hj₀, hj₀min⟩ := (univ.filter fun j => c j ≠ 0).exists_min_image e
    (by obtain ⟨j, hj⟩ := hne; exact ⟨j, by simp [hj]⟩)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj₀ hj₀min
  have hmin : ∀ j, c j ≠ 0 → e j₀ ≤ e j := hj₀min
  -- a minimizer of a given sign
  have key : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      ∃ j, 0 < σ * c j ∧ ∀ j', c j' ≠ 0 → e j ≤ e j' := by
    intro σ hσ
    have hσne : σ ≠ 0 := by rcases hσ with h | h <;> simp [h]
    by_contra hno
    push Not at hno
    -- every nonzero minimal term has the opposite sign
    have hopp : ∀ j, c j ≠ 0 → e j = e j₀ → 0 < (-σ) * c j := by
      intro j hj hje
      have hmj : ∀ j', c j' ≠ 0 → e j ≤ e j' := fun j' hj' => hje ▸ hmin j' hj'
      have h1 : σ * c j ≤ 0 := by
        by_contra h; push Not at h
        obtain ⟨j', hj', hlt⟩ := hno j h
        exact absurd (hmj j' hj') (not_le.mpr hlt)
      have h2 : σ * c j ≠ 0 := mul_ne_zero hσne hj
      have : σ * c j < 0 := lt_of_le_of_ne h1 h2
      linarith
    have hev := eventually_sum_pos_of_minimizers_pos (fun j => (-σ) * c j) e L η hL hη j₀
      (hopp j₀ hj₀ rfl)
      (fun j hj => hmin j (by intro h; exact hj (by simp [h])))
      (fun j hj hje => hopp j (by intro h; exact hj (by simp [h])) hje)
    obtain ⟨n, hn1, hn2⟩ := (hev.and hz).exists
    have : ∑ j, (-σ) * c j * Real.exp (-(L n * (e j + η n j)))
        = (-σ) * ∑ j, c j * Real.exp (-(L n * (e j + η n j))) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
    rw [this, hn2, mul_zero] at hn1
    exact lt_irrefl _ hn1
  obtain ⟨j₁, hj₁, hj₁m⟩ := key 1 (Or.inl rfl)
  obtain ⟨j₂, hj₂, hj₂m⟩ := key (-1) (Or.inr rfl)
  exact ⟨j₁, j₂, by linarith, by linarith, fun j hj => ⟨hj₁m j hj, hj₂m j hj⟩⟩

variable {S : Type*} [Fintype S]

/-- **Equilibration from scaled positive zeros of a power-law polynomial.** Let `ε n → 0⁺` and let
`x n` be positive zeros (eventually) of `∑ j, c j * ε^{a j} * ∏ s, (x s)^{m j s}` whose valuations
`log (x n s) / log (ε n)` converge to `u s`. If some coefficient is nonzero, the orders
`a j + ∑ s, m j s * u s` form a tropical equilibration. -/
theorem isEquilibrated_of_scaled_zeros (c a : J → ℝ) (m : J → S → ℝ) (u : S → ℝ)
    (ε : ℕ → ℝ) (x : ℕ → S → ℝ) (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    (hx : ∀ n s, 0 < x n s)
    (hu : ∀ s, Tendsto (fun n => Real.log (x n s) / Real.log (ε n)) atTop (𝓝 (u s)))
    (hzero : ∀ᶠ n in atTop, ∑ j, c j * ε n ^ a j * ∏ s, x n s ^ m j s = 0)
    (hne : ∃ j, c j ≠ 0) :
    IsEquilibrated c (fun j => a j + ∑ s, m j s * u s) := by
  have hεw : Tendsto ε atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hε, Eventually.of_forall hε0⟩
  have hlog : Tendsto (fun n => Real.log (ε n)) atTop atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hεw
  set L : ℕ → ℝ := fun n => -Real.log (ε n) with hLdef
  have hL : Tendsto L atTop atTop := tendsto_neg_atBot_atTop.comp hlog
  set η : ℕ → J → ℝ :=
    fun n j => ∑ s, m j s * (Real.log (x n s) / Real.log (ε n) - u s) with hηdef
  have hη : ∀ j, Tendsto (fun n => η n j) atTop (𝓝 0) := by
    intro j
    have : Tendsto (fun n => ∑ s, m j s * (Real.log (x n s) / Real.log (ε n) - u s)) atTop
        (𝓝 (∑ s : S, m j s * (u s - u s))) :=
      tendsto_finsetSum _ fun s _ => ((hu s).sub_const (u s)).const_mul (m j s)
    simpa using this
  refine isEquilibrated_of_eventually_zero c _ L η hL hη ?_ hne
  filter_upwards [hzero, hlog.eventually_lt_atBot 0] with n hn hneg
  rw [← hn]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hlε : Real.log (ε n) ≠ 0 := hneg.ne
  rw [Real.rpow_def_of_pos (hε0 n)]
  have hprod : ∏ s, x n s ^ m j s = Real.exp (∑ s, Real.log (x n s) * m j s) := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun s _ => Real.rpow_def_of_pos (hx n s) _
  rw [hprod, mul_assoc, ← Real.exp_add]
  congr 2
  simp only [hLdef, hηdef]
  have hsplit : ∀ s, Real.log (x n s) * m j s =
      Real.log (ε n) * (m j s * u s + m j s * (Real.log (x n s) / Real.log (ε n) - u s)) := by
    intro s; field_simp; ring
  rw [Finset.sum_congr rfl fun s _ => hsplit s, ← Finset.mul_sum, Finset.sum_add_distrib]
  ring

end Tropical

namespace Network

open Filter Topology

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Rate constants scaled by powers of a positive parameter: `κ_r = κ̄_r ε^{a_r}`. -/
noncomputable def scaledRateConstants (N : Network S) (κ : RateConstants N) (a : N.R → ℝ)
    (ε : ℝ) (hε : 0 < ε) : RateConstants N :=
  ⟨fun r => κ.k r * ε ^ a r, fun r => mul_pos (κ.positive r) (Real.rpow_pos_of_pos hε _)⟩

/-- **Tropical equilibration of scaled mass-action steady states.** Let the rate constants be
`κ̄_r ε^{a_r}`, let `ε n → 0⁺`, and let `x n` be positive steady states for the parameter `ε n`
whose valuations `log (x n s) / log (ε n)` converge to `u s`. Then for every species `s` changed
by some reaction, the minimum of the orders `a_r + ⟨y_r, u⟩` over the reactions changing `s` is
attained by a reaction producing `s` and by a reaction consuming `s`. -/
theorem tropicalEquilibration_of_steadyStates (N : Network S) (κ : RateConstants N)
    (a : N.R → ℝ) (u : S → ℝ) (ε : ℕ → ℝ) (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    (x : ℕ → Concentration S) (hx : ∀ n, (x n).Positive)
    (hu : ∀ s, Tendsto (fun n => Real.log (x n s) / Real.log (ε n)) atTop (𝓝 (u s)))
    (hss : ∀ n, N.IsMassActionSteadyState (N.scaledRateConstants κ a (ε n) (hε0 n)) (x n))
    (s : S) (hs : ∃ r, N.reactionVector r s ≠ 0) :
    ∃ r₁ r₂, 0 < N.reactionVector r₁ s ∧ N.reactionVector r₂ s < 0 ∧
      ∀ r, N.reactionVector r s ≠ 0 →
        a r₁ + ∑ s', ((N.reaction r₁).source s' : ℝ) * u s' ≤
            a r + ∑ s', ((N.reaction r).source s' : ℝ) * u s' ∧
          a r₂ + ∑ s', ((N.reaction r₂).source s' : ℝ) * u s' ≤
            a r + ∑ s', ((N.reaction r).source s' : ℝ) * u s' := by
  have hc : ∀ r, κ.k r * N.reactionVector r s ≠ 0 ↔ N.reactionVector r s ≠ 0 := fun r =>
    ⟨fun h h' => h (by rw [h', mul_zero]), fun h => mul_ne_zero (κ.positive r).ne' h⟩
  have hE := Tropical.isEquilibrated_of_scaled_zeros (fun r => κ.k r * N.reactionVector r s) a
    (fun r s' => ((N.reaction r).source s' : ℝ)) u ε x hε0 hε (fun n s' => hx n s') hu
    (Eventually.of_forall fun n => by
      have h := hss n s
      simp only [massActionVectorField_apply] at h
      rw [← h]
      refine Finset.sum_congr rfl fun r _ => ?_
      simp only [massActionRate, scaledRateConstants, Complex.massActionMonomial,
        Real.rpow_natCast]
      ring)
    (by obtain ⟨r, hr⟩ := hs; exact ⟨r, (hc r).mpr hr⟩)
  obtain ⟨r₁, r₂, h₁, h₂, hm⟩ := hE
  refine ⟨r₁, r₂, (pos_iff_pos_of_mul_pos h₁).mp (κ.positive r₁), ?_, fun r hr =>
    hm r ((hc r).mpr hr)⟩
  by_contra h
  push Not at h
  have := mul_nonneg (κ.positive r₂).le h
  linarith

end Network

end CRNT
