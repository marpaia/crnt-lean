import CRNT.Dynamics.Contraction

/-!
# Transverse contraction of the Michaelis–Menten fast subsystem

For `E + S ⇌ C → E + P` with total enzyme `e₀` and rate constants `k₁, k₋₁, k₂`, the complex
concentration obeys, at a frozen substrate level `s ≥ 0`,

`ċ = g_s(c) = k₁ (e₀ - c) s - (k₋₁ + k₂) c`.

This fast field is contracting with rate `k₋₁ + k₂` uniformly in `s ≥ 0`, its unique equilibrium
is the Briggs–Haldane quasi-steady state `c*(s) = e₀ s / (s + K_M)`, `K_M = (k₋₁ + k₂)/k₁`, and
every solution approaches it exponentially (Tikhonov's transverse stability hypothesis for the
enzyme field; Segel–Slemrod 1989).

Main results:
* `CRNT.Enzyme.fastField_isContracting`.
* `CRNT.Enzyme.fastField_qss`: `g_s(c*(s)) = 0`.
* `CRNT.Enzyme.fast_dist_qss_le`: `|c(t) - c*(s)| ≤ e^{-(k₋₁+k₂) t} |c(0) - c*(s)|`.
-/

namespace CRNT

namespace Enzyme

/-- The fast complex field at frozen substrate `s`. -/
def fastField (k₁ km₁ k₂ e₀ s : ℝ) (c : ℝ) : ℝ := k₁ * (e₀ - c) * s - (km₁ + k₂) * c

/-- The Briggs–Haldane quasi-steady state. -/
noncomputable def qss (k₁ km₁ k₂ e₀ s : ℝ) : ℝ := e₀ * s / (s + (km₁ + k₂) / k₁)

theorem fastField_isContracting {k₁ km₁ k₂ e₀ s : ℝ} (hk₁ : 0 ≤ k₁) (hs : 0 ≤ s) :
    Contraction.IsContracting (fastField k₁ km₁ k₂ e₀ s) Set.univ (km₁ + k₂) := by
  intro a _ b _
  simp only [fastField, Real.norm_eq_abs, sq_abs]
  -- inner product on `ℝ` is multiplication
  have : (k₁ * (e₀ - a) * s - (km₁ + k₂) * a - (k₁ * (e₀ - b) * s - (km₁ + k₂) * b)) * (a - b) =
      -(k₁ * s) * (a - b) ^ 2 - (km₁ + k₂) * (a - b) ^ 2 := by ring
  rw [show (inner ℝ (k₁ * (e₀ - a) * s - (km₁ + k₂) * a - (k₁ * (e₀ - b) * s - (km₁ + k₂) * b))
      (a - b) : ℝ) = (k₁ * (e₀ - a) * s - (km₁ + k₂) * a - (k₁ * (e₀ - b) * s - (km₁ + k₂) * b)) *
      (a - b) by rw [RCLike.inner_apply, conj_trivial]; ring, this]
  nlinarith [mul_nonneg (mul_nonneg hk₁ hs) (sq_nonneg (a - b))]

theorem fastField_qss {k₁ km₁ k₂ e₀ s : ℝ} (hk₁ : 0 < k₁) (hkm : 0 < km₁ + k₂) (hs : 0 ≤ s) :
    fastField k₁ km₁ k₂ e₀ s (qss k₁ km₁ k₂ e₀ s) = 0 := by
  unfold fastField qss
  have hden : 0 < s + (km₁ + k₂) / k₁ := by positivity
  field_simp
  ring

/-- **Exponential approach to the quasi-steady state.** -/
theorem fast_dist_qss_le {k₁ km₁ k₂ e₀ s T : ℝ} (hk₁ : 0 < k₁) (hkm : 0 < km₁ + k₂) (hs : 0 ≤ s)
    {c : ℝ → ℝ} (hc : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt c (fastField k₁ km₁ k₂ e₀ s (c t)) (Set.Icc 0 T) t)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    |c t - qss k₁ km₁ k₂ e₀ s| ≤
      Real.exp (-(km₁ + k₂) * t) * |c 0 - qss k₁ km₁ k₂ e₀ s| := by
  have h := Contraction.dist_le_exp_of_contracting (fastField_isContracting hk₁.le hs)
    hc (y := fun _ => qss k₁ km₁ k₂ e₀ s)
    (fun t _ => by rw [fastField_qss hk₁ hkm hs]; exact hasDerivWithinAt_const _ _ _)
    (fun _ _ => Set.mem_univ _) (fun _ _ => Set.mem_univ _) ht
  simpa [Real.norm_eq_abs] using h

end Enzyme

end CRNT
