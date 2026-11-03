import CRNT.Dynamics.GlobalPersistenceFrontier
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# No drainable siphon does not give uniform persistence for unbounded orbits

The network `X → 2X`, `X + Y → X`, `0 → Y` has no drainable siphon: the only siphon is `{X}`,
and no reaction lowers the count of `X`. With unit rates the dynamics are `x' = x`,
`y' = 1 − x y`; the flow is explicit,

`x(t) = a e^t`, `y(t) = e^{−a(e^t − 1)} (b + ∫₀ᵗ e^{a(e^s − 1)} ds)`,

and is defined on all of `ℝ²`. Along the orbit of `(1, 1)` the coordinate `y` is not bounded
below by a positive constant: once `e^t ε ≥ 2`, `y ≥ ε` would force `y' ≤ −1`.

Hence `NoDrainableSiphonUniformPersistenceClaim` is **false** (`claim_false`). The theorem of
Deshpande–Gopalkrishnan concerns bounded trajectories (ω-limit points), which is the form proved in
the library (`noDrainableSiphonOmegaPersistence`).
-/

open Filter Set MeasureTheory intervalIntegral
open scoped NNReal Topology

namespace CRNT
namespace Examples
namespace NoDrainableUnbounded

open Network

/-- `X → 2X`, `X + Y → X`, `0 → Y` (species `X = 0`, `Y = 1`). -/
abbrev net : Network (Fin 2) :=
  ⟨Fin 3, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨![1, 0], ![2, 0]⟩ else if r = 1 then ⟨![1, 1], ![1, 0]⟩
    else ⟨![0, 0], ![0, 1]⟩⟩

/-! ## No drainable siphon -/

theorem count_mono (n : Fin 2 → ℕ) (r : net.R) : n 0 ≤ net.jumpNextCount n r 0 := by
  fin_cases r <;> simp [Network.jumpNextCount] <;> omega

theorem fireList_mono : ∀ (rs : List net.R) (n : Fin 2 → ℕ), n 0 ≤ net.fireListTarget n rs 0
  | [], n => le_rfl
  | r :: rs, n => (count_mono n r).trans (fireList_mono rs _)

theorem hasNoDrainableSiphon : net.HasNoDrainableSiphon := by
  rintro P ⟨hne, hsiph, ⟨n, rs, -, hdrain⟩⟩
  by_cases h1 : (1 : Fin 2) ∈ P
  · obtain ⟨s, hs, hreact⟩ := hsiph 2 ⟨1, h1, by simp [Network.IsProduct]⟩
    fin_cases s <;> simp [Network.IsReactant] at hreact
  · obtain ⟨s, hs⟩ := hne
    have hs0 : s = 0 := by
      fin_cases s
      · rfl
      · exact absurd hs h1
    subst hs0
    exact absurd (hdrain 0 hs) (not_lt.mpr (fireList_mono rs n))

/-! ## The explicit flow -/

/-- Unit rate constants. -/
def κ : RateConstants net := ⟨fun _ => 1, fun _ => one_pos⟩

theorem field_eq (x : Concentration (Fin 2)) :
    net.massActionVectorField κ x = ![x 0, 1 - x 0 * x 1] := by
  funext s
  rw [massActionVectorField_apply, Fin.sum_univ_three]
  fin_cases s <;>
    simp [massActionRate, κ, Network.reactionVector, Complex.massActionMonomial,
      Fin.prod_univ_two] <;> ring

/-- `E_a(s) = exp(a (e^s − 1))`. -/
noncomputable def E (a s : ℝ) : ℝ := Real.exp (a * (Real.exp s - 1))

theorem continuous_E : Continuous fun p : ℝ × ℝ => E p.1 p.2 := by
  unfold E; fun_prop

/-- `G_a(t) = ∫₀ᵗ E_a`. -/
noncomputable def G (a t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, E a s

theorem continuous_G : Continuous fun p : ℝ × ℝ => G p.1 p.2 := by
  unfold G
  exact continuous_parametric_primitive_of_continuous (f := fun a s => E a s) continuous_E

theorem hasDerivAt_G (a t : ℝ) : HasDerivAt (G a) (E a t) t := by
  unfold G
  have hc : Continuous (E a) := by unfold E; fun_prop
  exact integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

/-- The shift identity `G_{a e^s}(t) = e^{−a(e^s−1)} (G_a(t + s) − G_a(s))`. -/
theorem G_shift (a s t : ℝ) :
    G (a * Real.exp s) t = Real.exp (-(a * (Real.exp s - 1))) * (G a (t + s) - G a s) := by
  have hc : Continuous (E a) := by unfold E; fun_prop
  have h1 : ∀ σ, E (a * Real.exp s) σ = Real.exp (-(a * (Real.exp s - 1))) * E a (σ + s) := by
    intro σ
    unfold E
    rw [← Real.exp_add, Real.exp_add σ s]
    congr 1
    ring
  unfold G
  simp only [h1, intervalIntegral.integral_const_mul]
  congr 1
  rw [intervalIntegral.integral_comp_add_right (fun σ => E a σ) s, zero_add]
  rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]

/-- The flow curves. -/
noncomputable def gam (x : Concentration (Fin 2)) (t : ℝ) : Concentration (Fin 2) :=
  ![x 0 * Real.exp t, Real.exp (-(x 0 * (Real.exp t - 1))) * (x 1 + G (x 0) t)]

theorem gam_hasDerivAt (x : Concentration (Fin 2)) (t : ℝ) :
    HasDerivAt (gam x) (net.massActionVectorField κ (gam x t)) t := by
  rw [field_eq, hasDerivAt_pi, Fin.forall_fin_two]
  refine ⟨?_, ?_⟩
  · show HasDerivAt (fun t => x 0 * Real.exp t) _ t
    convert (Real.hasDerivAt_exp t).const_mul (x 0) using 1
    simp [gam]
  · show HasDerivAt (fun t => Real.exp (-(x 0 * (Real.exp t - 1))) * (x 1 + G (x 0) t)) _ t
    have h1 : HasDerivAt (fun t => Real.exp (-(x 0 * (Real.exp t - 1))))
        (Real.exp (-(x 0 * (Real.exp t - 1))) * (-(x 0 * Real.exp t))) t := by
      have := (((Real.hasDerivAt_exp t).sub_const 1).const_mul (x 0)).neg.exp
      convert this using 1
    have h2 : HasDerivAt (fun t => x 1 + G (x 0) t) (E (x 0) t) t :=
      (hasDerivAt_G (x 0) t).const_add (x 1)
    convert h1.mul h2 using 1
    simp only [gam, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hE : Real.exp (-(x 0 * (Real.exp t - 1))) * E (x 0) t = 1 := by
      unfold E; rw [← Real.exp_add]; simp
    linear_combination (-1 : ℝ) * hE

/-- The global mass-action flow on `ℝ²`. -/
noncomputable def flow : Flow ℝ≥0 (Concentration (Fin 2)) where
  toFun t x := gam x t
  cont' := by
    have hG : Continuous fun p : ℝ≥0 × Concentration (Fin 2) => G (p.2 0) (p.1 : ℝ) :=
      continuous_G.comp (f := fun p : ℝ≥0 × Concentration (Fin 2) => ((p.2 0, (p.1 : ℝ)) : ℝ × ℝ))
        (by fun_prop)
    rw [continuous_pi_iff, Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · simp only [gam, Function.uncurry, Matrix.cons_val_zero]
      fun_prop
    · simp only [gam, Function.uncurry, Matrix.cons_val_one]
      exact (by fun_prop : Continuous fun p : ℝ≥0 × Concentration (Fin 2) =>
        Real.exp (-(p.2 0 * (Real.exp (p.1 : ℝ) - 1)))).mul
        (((continuous_apply 1).comp continuous_snd).add hG)
  map_add' t₁ t₂ x := by
    refine funext_iff.mpr (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    · simp [gam, NNReal.coe_add, Real.exp_add]; ring
    · simp only [gam, NNReal.coe_add, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [G_shift (x 0) (t₂ : ℝ) (t₁ : ℝ)]
      have hsplit : Real.exp (-(x 0 * Real.exp ↑t₂ * (Real.exp ↑t₁ - 1))) *
          Real.exp (-(x 0 * (Real.exp ↑t₂ - 1))) =
          Real.exp (-(x 0 * (Real.exp (↑t₁ + ↑t₂) - 1))) := by
        rw [← Real.exp_add]; congr 1; rw [Real.exp_add]; ring
      have hinv : Real.exp (-(x 0 * (Real.exp ↑t₂ - 1))) * Real.exp (x 0 * (Real.exp ↑t₂ - 1)) =
          1 := by rw [← Real.exp_add]; simp
      calc Real.exp (-(x 0 * (Real.exp (↑t₁ + ↑t₂) - 1))) * (x 1 + G (x 0) (↑t₁ + ↑t₂))
          = Real.exp (-(x 0 * Real.exp ↑t₂ * (Real.exp ↑t₁ - 1))) *
              (Real.exp (-(x 0 * (Real.exp ↑t₂ - 1))) * (x 1 + G (x 0) ↑t₂) +
                Real.exp (-(x 0 * (Real.exp ↑t₂ - 1))) *
                  (G (x 0) (↑t₁ + ↑t₂) - G (x 0) ↑t₂)) := by
            rw [← hsplit]; ring
        _ = _ := by ring
  map_zero' x := by
    refine funext_iff.mpr (Fin.forall_fin_two.mpr ⟨?_, ?_⟩) <;> simp [gam, G]

theorem isMassActionFlow : net.IsMassActionFlow κ flow gam := by
  refine ⟨fun x => ?_, fun x t => rfl, fun x t _ => gam_hasDerivAt x t⟩
  refine funext_iff.mpr (Fin.forall_fin_two.mpr ⟨?_, ?_⟩) <;> simp [gam, G]

/-- **The orbit of `(1, 1)` is not uniformly persistent.** -/
theorem not_structurallyPersistentStd : ¬ net.StructurallyPersistentStd := by
  intro h
  have hx : Concentration.Positive (fun _ : Fin 2 => (1 : ℝ)) := fun _ => one_pos
  obtain ⟨ε, hε, hle⟩ := h κ flow gam isMassActionFlow _ hx 1
  set y : ℝ → ℝ := fun t => gam (fun _ => 1) t 1
  have hyle : ∀ t, 0 ≤ t → ε ≤ y t := fun t ht => hle ⟨t, ht⟩
  have hyd : ∀ t, HasDerivAt y (1 - Real.exp t * y t) t := by
    intro t
    have := (hasDerivAt_pi.mp (gam_hasDerivAt (fun _ => 1) t)) 1
    rw [field_eq] at this
    convert this using 1
    simp [gam, y]
  -- after `T₀ = log (2/ε)`, `y' ≤ −1`
  set T₀ := max 0 (Real.log (2 / ε))
  have hT₀ : 0 ≤ T₀ := le_max_left _ _
  have hderiv : ∀ t, T₀ ≤ t → 1 - Real.exp t * y t ≤ -1 := by
    intro t ht
    have h1 : 2 / ε ≤ Real.exp t := by
      calc 2 / ε = Real.exp (Real.log (2 / ε)) := (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp t := Real.exp_le_exp.mpr ((le_max_right _ _).trans ht)
    have h2 : 2 ≤ Real.exp t * ε := by rwa [div_le_iff₀ hε] at h1
    have h3 : Real.exp t * ε ≤ Real.exp t * y t :=
      mul_le_mul_of_nonneg_left (hyle t (hT₀.trans ht)) (Real.exp_pos t).le
    linarith
  set W : ℝ → ℝ := fun t => y t + t
  have hanti : AntitoneOn W (Ici T₀) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici T₀)
      (fun t _ => ((hyd t).add (hasDerivAt_id t)).continuousAt.continuousWithinAt)
      (fun t ht => ((hyd t).add (hasDerivAt_id t)).hasDerivWithinAt)
      (fun t ht => by
        rw [interior_Ici] at ht
        have := hderiv t (le_of_lt ht)
        linarith)
  set τ := T₀ + |y T₀| + 1
  have hτ : T₀ ≤ τ := by have := abs_nonneg (y T₀); simp only [τ]; linarith
  have hW := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hτ) hτ
  simp only [W] at hW
  have := hyle τ (hT₀.trans hτ)
  have habs := le_abs_self (y T₀)
  simp only [τ] at hW this
  linarith

/-- **`NoDrainableSiphonUniformPersistenceClaim` is false.** -/
theorem claim_false : ¬ net.NoDrainableSiphonUniformPersistenceClaim :=
  fun h => not_structurallyPersistentStd (h hasNoDrainableSiphon)

end NoDrainableUnbounded
end Examples
end CRNT
