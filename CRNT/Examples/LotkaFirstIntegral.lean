import CRNT.Examples.Lotka
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The Lotka network: constancy of the first integral and compact level sets

Discharges steps 2 and 3 of `CRNT/Examples/Lotka.lean`:

* `CRNT.Examples.Lotka.firstIntegralConstant` proves `FirstIntegralConstantTarget`: the first
  integral `V(x, y) = k₁ x + k₁ y − k₂ log x − k₀ log y` is constant along every positive
  solution of the mass-action system.
* `CRNT.Examples.Lotka.levelSetCompact` proves `LevelSetCompactTarget`: every sublevel set of `V`
  in the open positive quadrant is compact.

Consequences (`positive_solution_bounded`, `not_tendsto_equilibrium`): every positive solution
stays in a compact subset of the open quadrant (in particular it is persistent and bounded), and
no positive solution that starts away from the equilibrium converges to it — the equilibrium is
not attracting, as required of a centre surrounded by closed orbits. Step 4 (existence of a
period) remains `HasPositivePeriodicOrbitTarget`.
-/

namespace CRNT
namespace Examples
namespace Lotka

open Filter Topology

/-- **Step 2: the first integral is constant along positive solutions.** -/
theorem firstIntegralConstant : FirstIntegralConstantTarget := by
  intro κ γ hpos hder t
  have hA : ∀ τ, 0 < γ τ A := fun τ => hpos τ A
  have hB : ∀ τ, 0 < γ τ B := fun τ => hpos τ B
  have hd : ∀ τ, HasDerivAt (fun τ => firstIntegral κ (γ τ))
      (∑ s, firstIntegralGrad κ (γ τ) s * N.massActionVectorField κ (γ τ) s) τ := by
    intro τ
    have h1 := hder τ A
    have h2 := hder τ B
    have hlA := (h1.log (hA τ).ne')
    have hlB := (h2.log (hB τ).ne')
    have := ((((h1.const_mul (κ.k prey)).add (h2.const_mul (κ.k prey))).sub
      (hlA.const_mul (κ.k decay))).sub (hlB.const_mul (κ.k grow)))
    unfold firstIntegral
    convert this using 1
    rw [Fin.sum_univ_two]
    simp only [firstIntegralGrad, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring
  have hzero : ∀ τ, deriv (fun τ => firstIntegral κ (γ τ)) τ = 0 := fun τ => by
    rw [(hd τ).deriv, conservation_identity κ (hpos τ)]
  exact is_const_of_deriv_eq_zero (fun τ => (hd τ).differentiableAt) hzero t 0

/-- Lower bound of `t ↦ k t − a log t`. -/
theorem linLog_lower {k a t : ℝ} (hk : 0 < k) (ha : 0 < a) (ht : 0 < t) :
    k * t / 2 + a - a * Real.log (2 * a / k) ≤ k * t - a * Real.log t := by
  have h := Real.log_le_sub_one_of_pos (show 0 < k / (2 * a) * t by positivity)
  rw [Real.log_mul (by positivity) ht.ne', Real.log_div hk.ne' (by positivity)] at h
  rw [Real.log_div (by positivity) hk.ne']
  have : a * (k / (2 * a) * t) = k * t / 2 := by field_simp
  nlinarith

/-- `k t − a log t ≥ −a log t` gives a lower bound on `t`. -/
theorem linLog_ge_exp {k a t C : ℝ} (hk : 0 < k) (ha : 0 < a) (ht : 0 < t)
    (h : k * t - a * Real.log t ≤ C) : Real.exp (-C / a) ≤ t := by
  have : -a * Real.log t ≤ C := by nlinarith
  have hlog : -C / a ≤ Real.log t := by
    rw [div_le_iff₀ ha]; linarith
  calc Real.exp (-C / a) ≤ Real.exp (Real.log t) := Real.exp_le_exp.mpr hlog
    _ = t := Real.exp_log ht

/-- The first integral splits into two one-variable terms. -/
theorem firstIntegral_eq (κ : Network.RateConstants N) (x : Concentration Species) :
    firstIntegral κ x = (κ.k prey * x A - κ.k decay * Real.log (x A)) +
      (κ.k prey * x B - κ.k grow * Real.log (x B)) := by
  unfold firstIntegral; ring

/-- **Step 3: sublevel sets are compact.** -/
theorem levelSetCompact : LevelSetCompactTarget := by
  intro κ h0 h1 h2 c
  set k := κ.k prey with hkdef
  set a := κ.k decay with hadef
  set b := κ.k grow with hbdef
  set mA := a - a * Real.log (2 * a / k)
  set mB := b - b * Real.log (2 * b / k)
  set CA := c - mB
  set CB := c - mA
  set M := max (2 * (CA - mA) / k) (2 * (CB - mB) / k)
  set δ := min (Real.exp (-CA / a)) (Real.exp (-CB / b))
  have hδ : 0 < δ := lt_min (Real.exp_pos _) (Real.exp_pos _)
  have hbox : ∀ x : Concentration Species, x.Positive → firstIntegral κ x ≤ c →
      ∀ s, δ ≤ x s ∧ x s ≤ max M δ := by
    intro x hx hV s
    have hxA := hx A
    have hxB := hx B
    rw [firstIntegral_eq] at hV
    have lA := linLog_lower (k := k) (a := a) h1 h2 hxA
    have lB := linLog_lower (k := k) (a := b) h1 h0 hxB
    have hkA : 0 < k * x A := mul_pos h1 hxA
    have hkB : 0 < k * x B := mul_pos h1 hxB
    have tA : k * x A - a * Real.log (x A) ≤ CA := by simp only [CA, mB]; linarith
    have tB : k * x B - b * Real.log (x B) ≤ CB := by simp only [CB, mA]; linarith
    have loA := linLog_ge_exp h1 h2 hxA tA
    have loB := linLog_ge_exp h1 h0 hxB tB
    have hiA : x A ≤ 2 * (CA - mA) / k := by
      rw [le_div_iff₀ h1]; simp only [mA] at *; linarith
    have hiB : x B ≤ 2 * (CB - mB) / k := by
      rw [le_div_iff₀ h1]; simp only [mB] at *; linarith
    fin_cases s
    · exact ⟨(min_le_left _ _).trans loA, (hiA.trans (le_max_left _ _)).trans (le_max_left _ _)⟩
    · exact ⟨(min_le_right _ _).trans loB, (hiB.trans (le_max_right _ _)).trans (le_max_left _ _)⟩
  have hset : {x : Concentration Species | x.Positive ∧ firstIntegral κ x ≤ c} =
      Set.Icc (fun _ => δ) (fun _ => max M δ) ∩ firstIntegral κ ⁻¹' Set.Iic c := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Icc, Set.mem_preimage,
      Set.mem_Iic]
    constructor
    · rintro ⟨hx, hV⟩
      exact ⟨⟨fun s => (hbox x hx hV s).1, fun s => (hbox x hx hV s).2⟩, hV⟩
    · rintro ⟨⟨hlo, _⟩, hV⟩
      exact ⟨fun s => lt_of_lt_of_le hδ (hlo s), hV⟩
  rw [hset]
  have hcont : ContinuousOn (firstIntegral κ) (Set.Icc (fun _ => δ) (fun _ => max M δ)) := by
    have hne : ∀ s, ∀ x ∈ Set.Icc (fun _ : Species => δ) (fun _ => max M δ), x s ≠ 0 :=
      fun s x hx => (lt_of_lt_of_le hδ (hx.1 s)).ne'
    unfold firstIntegral
    refine ((((continuous_const.mul (continuous_apply A)).continuousOn).add
      ((continuous_const.mul (continuous_apply B)).continuousOn)).sub
      (continuousOn_const.mul ((continuous_apply A).continuousOn.log (hne A)))).sub
      (continuousOn_const.mul ((continuous_apply B).continuousOn.log (hne B)))
  exact isCompact_Icc.of_isClosed_subset
    (hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic) Set.inter_subset_left

/-- **Positive solutions stay in a compact subset of the open quadrant.** -/
theorem positive_solution_bounded (κ : Network.RateConstants N) (h0 : 0 < κ.k grow)
    (h1 : 0 < κ.k prey) (h2 : 0 < κ.k decay) (γ : ℝ → Concentration Species)
    (hpos : ∀ t, (γ t).Positive)
    (hder : ∀ t s, HasDerivAt (fun τ => γ τ s) (N.massActionVectorField κ (γ t) s) t) :
    ∃ K : Set (Concentration Species), IsCompact K ∧ (∀ x ∈ K, x.Positive) ∧ ∀ t, γ t ∈ K := by
  refine ⟨{x | x.Positive ∧ firstIntegral κ x ≤ firstIntegral κ (γ 0)},
    levelSetCompact κ h0 h1 h2 _, fun x hx => hx.1, fun t => ⟨hpos t, ?_⟩⟩
  rw [firstIntegralConstant κ γ hpos hder t]

/-- The equilibrium is the strict minimizer of the first integral on the positive quadrant. -/
theorem firstIntegral_gt_equilibrium (κ : Network.RateConstants N) (h0 : 0 < κ.k grow)
    (h1 : 0 < κ.k prey) (h2 : 0 < κ.k decay) {x : Concentration Species} (hx : x.Positive)
    (hne : x ≠ equilibrium κ) : firstIntegral κ (equilibrium κ) < firstIntegral κ x := by
  -- `V(x) - V(x*) = a (u - 1 - log u) + b (v - 1 - log v)`, `u = x_A/x*_A`, `v = x_B/x*_B`
  set k := κ.k prey
  set a := κ.k decay
  set b := κ.k grow
  have hxA := hx A
  have hxB := hx B
  have heA : equilibrium κ A = a / k := rfl
  have heB : equilibrium κ B = b / k := rfl
  set u := x A / (a / k)
  set v := x B / (b / k)
  have hu : 0 < u := by positivity
  have hv : 0 < v := by positivity
  have hdiff : firstIntegral κ x - firstIntegral κ (equilibrium κ) =
      a * (u - 1 - Real.log u) + b * (v - 1 - Real.log v) := by
    rw [firstIntegral_eq, firstIntegral_eq, heA, heB]
    simp only [u, v]
    rw [Real.log_div hxA.ne' (by positivity), Real.log_div hxB.ne' (by positivity)]
    field_simp
    ring
  have gA : 0 ≤ u - 1 - Real.log u := by linarith [Real.log_le_sub_one_of_pos hu]
  have gB : 0 ≤ v - 1 - Real.log v := by linarith [Real.log_le_sub_one_of_pos hv]
  -- one of `u, v` differs from `1`
  have hstrict : u ≠ 1 ∨ v ≠ 1 := by
    by_contra h
    push Not at h
    apply hne
    funext s
    fin_cases s
    · show x A = equilibrium κ A
      rw [heA, eq_div_iff h1.ne']; have := h.1; simp only [u] at this; field_simp at this; linarith
    · show x B = equilibrium κ B
      rw [heB, eq_div_iff h1.ne']; have := h.2; simp only [v] at this; field_simp at this; linarith
  have pos_of_ne : ∀ w : ℝ, 0 < w → w ≠ 1 → 0 < w - 1 - Real.log w := by
    intro w hw hw1
    have := Real.log_lt_sub_one_of_pos hw hw1
    linarith
  rcases hstrict with h | h
  · have := pos_of_ne u hu h
    nlinarith [mul_nonneg h0.le gB]
  · have := pos_of_ne v hv h
    nlinarith [mul_nonneg h2.le gA]

/-- **The equilibrium is not attracting.** A positive solution starting away from the
equilibrium never converges to it. -/
theorem not_tendsto_equilibrium (κ : Network.RateConstants N) (h0 : 0 < κ.k grow)
    (h1 : 0 < κ.k prey) (h2 : 0 < κ.k decay) (γ : ℝ → Concentration Species)
    (hpos : ∀ t, (γ t).Positive)
    (hder : ∀ t s, HasDerivAt (fun τ => γ τ s) (N.massActionVectorField κ (γ t) s) t)
    (hstart : γ 0 ≠ equilibrium κ) : ¬ Tendsto γ atTop (𝓝 (equilibrium κ)) := by
  intro hlim
  have heq_pos : (equilibrium κ).Positive := by
    intro s; fin_cases s
    · show 0 < κ.k decay / κ.k prey; positivity
    · show 0 < κ.k grow / κ.k prey; positivity
  have hcont : ContinuousAt (firstIntegral κ) (equilibrium κ) := by
    unfold firstIntegral
    have hA : equilibrium κ A ≠ 0 := (heq_pos A).ne'
    have hB : equilibrium κ B ≠ 0 := (heq_pos B).ne'
    have hlogA : ContinuousAt (fun x : Concentration Species => Real.log (x A)) (equilibrium κ) :=
      (Real.continuousAt_log hA).comp (f := fun x : Concentration Species => x A)
        (continuous_apply A).continuousAt
    have hlogB : ContinuousAt (fun x : Concentration Species => Real.log (x B)) (equilibrium κ) :=
      (Real.continuousAt_log hB).comp (f := fun x : Concentration Species => x B)
        (continuous_apply B).continuousAt
    exact ((((continuous_const.mul (continuous_apply A)).continuousAt).add
      ((continuous_const.mul (continuous_apply B)).continuousAt)).sub
      (continuousAt_const.mul hlogA)).sub (continuousAt_const.mul hlogB)
  have hV := (hcont.tendsto.comp hlim)
  have hconst : ∀ t, firstIntegral κ (γ t) = firstIntegral κ (γ 0) :=
    firstIntegralConstant κ γ hpos hder
  have : (fun t => firstIntegral κ (γ t)) = fun _ => firstIntegral κ (γ 0) := funext hconst
  rw [Function.comp_def, this] at hV
  have heq := tendsto_nhds_unique tendsto_const_nhds hV
  have := firstIntegral_gt_equilibrium κ h0 h1 h2 (hpos 0) hstart
  linarith

end Lotka
end Examples
end CRNT
