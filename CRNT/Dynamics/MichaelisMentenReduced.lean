import CRNT.Dynamics.FlowConstruction
import CRNT.Dynamics.MichaelisMentenManifold

/-!
# The constructed Michaelis–Menten reduced slow flow

This module closes the Michaelis–Menten quasi-steady-state reduction of
`CRNT.Dynamics.MichaelisMentenManifold` by **constructing** the reduced scalar slow flow, rather
than receiving the substrate path `σ` and its slaving as hypotheses. It supplies the substrate
curve from Mathlib's autonomous-ODE existence machinery (`ODE.exists_isIntegralCurve`) and feeds
it, together with its derivative law, into the substrate-dependent error theorem
`michaelisMenten_manifold_qssa_error`, turning the reduced-curve hypotheses into theorems.

**The reduced scalar field** (`mmReducedField`). The Michaelis–Menten rate law `ṡ = -Vmax·s/(Km+s)`
is the negative of `mmComplexEquil Km Vmax` on the physical substrate ray `s ≥ 0`. To obtain a
globally Lipschitz autonomous field — the input Mathlib's existence theorem requires — it is
extended by `0` to `s < 0`: `mmReducedField Km Vmax s = -(Vmax·s/(Km+s))` for `0 ≤ s`, else `0`.
For `0 < Km`, `0 ≤ Vmax` this field is `(Vmax/Km)`-Lipschitz (`mmReducedField_lipschitz`, from the
explicit difference quotient `Vmax·Km·(s-t)/((Km+s)(Km+t))`) and bounded by `Vmax`
(`mmReducedField_abs_le`); it vanishes on `s ≤ 0` (`mmReducedField_nonpos`, `mmReducedField_zero`),
so the substrate ray `s = 0` is an equilibrium.

**The constructed substrate curve** (`mmSubstrate`, `mmSubstrate_hasDerivAt`, `mmSubstrate_init`).
Through any initial substrate `s₀`, `ODE.exists_isIntegralCurve` furnishes a global integral curve
`σ` of `mmReducedField`. **Forward positivity** (`mmSubstrate_nonneg`): if `0 ≤ s₀` then `0 ≤ σ t`
for all `t ≥ 0` — because the field is nonpositive and vanishes at the boundary `s = 0`, a first
return to `0` forces `σ` constant thereafter (`constant_of_has_deriv_right_zero`), so the curve
cannot cross into negative substrate. On the forward ray the field therefore equals the true MM
rate law (`mmSubstrate_hasDerivAt_mm`): `σ̇ t = -mmComplexEquil Km Vmax (σ t)`.

**Closed compact-time error theorem** (`michaelisMenten_reduced_qssa_error`). For a `K`-Lipschitz
full enzyme mass-action field `full` with exact integral curve `γ`, the exact trajectory stays
within `gronwallBound δ K εf T` of the constructed reduced complex curve
`t ↦ mmComplexEquil Km Vmax (σ t) • e0` on `[0, T]`, and that bound vanishes as the initial mismatch
`δ` and the slaving defect `εf` jointly vanish. The substrate-path continuity, the right-derivative
law, and the lifted curve are now *derived* from the constructed `σ`: the explicit reduced-curve
derivative is `γᵣ' t = (Vmax·Km/(Km+σ t)² · (-mmComplexEquil Km Vmax (σ t))) • e0`
(`mmReducedComplex_hasDerivAt`).

**Out of scope (the remaining ceilings — unchanged from the result below).** (1) The slaving defect
`εf` and the initial mismatch `δ` are still inputs; deriving `εf = O(ε)` from a singular-perturbation
small parameter `ε` needs an ε-quantified normally-hyperbolic persistence theorem absent from
Mathlib v4.31. (2) The horizon stays compact: `gronwallBound δ K εf T` diverges as `T → ∞` for
`K > 0`, so infinite-horizon shadowing is unreachable. (3) The error theorem still consumes `full`,
`γ`, `K`, `δ`, `εf` as data; the gain here is purely that the reduced **substrate** flow `σ` — the
scalar Michaelis–Menten ODE — and all of its slaving structure are now constructed and proved, not
assumed.

Depends on: CRNT.Dynamics.FlowConstruction,
CRNT.Dynamics.MichaelisMentenManifold.
-/

open Set Filter
open scoped Topology RealInnerProductSpace NNReal

namespace CRNT.MichaelisMenten

/-- The scalar reduced Michaelis–Menten field, extended by `0` to the whole real line:
`mmReducedField Km Vmax s = -(Vmax·s/(Km+s))` for `0 ≤ s` and `0` for `s < 0`. On the physical ray
`s ≥ 0` it is the negative of the Michaelis–Menten complex level `mmComplexEquil Km Vmax`. -/
noncomputable def mmReducedField (Km Vmax s : ℝ) : ℝ :=
  if 0 ≤ s then -(Vmax * s / (Km + s)) else 0

/-- On the physical ray the reduced field is the negative Michaelis–Menten rate law. -/
lemma mmReducedField_of_nonneg (Km Vmax : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    mmReducedField Km Vmax s = -mmComplexEquil Km Vmax s := by
  simp only [mmReducedField, if_pos hs, mmComplexEquil]

/-- The reduced field vanishes for strictly negative substrate. -/
lemma mmReducedField_neg_eq_zero (Km Vmax : ℝ) {s : ℝ} (hs : s < 0) :
    mmReducedField Km Vmax s = 0 := by
  simp only [mmReducedField, if_neg (not_le.mpr hs)]

/-- The reduced field vanishes at the boundary substrate `s = 0`. -/
lemma mmReducedField_zero (Km Vmax : ℝ) : mmReducedField Km Vmax 0 = 0 := by
  simp [mmReducedField]

/-- The reduced field is nonpositive everywhere. -/
lemma mmReducedField_nonpos (Km Vmax : ℝ) (hKm : 0 < Km) (hV : 0 ≤ Vmax) (s : ℝ) :
    mmReducedField Km Vmax s ≤ 0 := by
  simp only [mmReducedField]
  split_ifs with hs
  · simp only [neg_nonpos]; positivity
  · exact le_refl 0

/-- The reduced field is bounded in magnitude by `Vmax`. -/
lemma mmReducedField_abs_le (Km Vmax : ℝ) (hKm : 0 < Km) (hV : 0 ≤ Vmax) (s : ℝ) :
    |mmReducedField Km Vmax s| ≤ Vmax := by
  simp only [mmReducedField]
  split_ifs with hs
  · rw [abs_neg, abs_of_nonneg (by positivity), div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg hV hs]
  · simpa using hV

/-- The core difference-quotient bound for the Michaelis–Menten complex level on the physical ray:
`|h s - h t| ≤ (Vmax/Km)·|s - t|`, where `h s = Vmax·s/(Km+s)`. -/
lemma mmComplexEquil_lipschitz_aux (Km Vmax : ℝ) (hKm : 0 < Km) (hV : 0 ≤ Vmax)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |Vmax * s / (Km + s) - Vmax * t / (Km + t)| ≤ (Vmax / Km) * |s - t| := by
  have hKs : 0 < Km + s := by linarith
  have hKt : 0 < Km + t := by linarith
  have key : Vmax * s / (Km + s) - Vmax * t / (Km + t)
      = (Vmax * Km * (s - t)) / ((Km + s) * (Km + t)) := by
    field_simp; ring
  rw [key, abs_div, abs_of_pos (by positivity : (0:ℝ) < (Km + s) * (Km + t)),
    abs_mul, abs_mul, abs_of_nonneg hV, abs_of_pos hKm, div_le_iff₀ (by positivity)]
  have h1 : Km ≤ Km + s := by linarith
  have h2 : Km ≤ Km + t := by linarith
  have hst : (0:ℝ) ≤ |s - t| := abs_nonneg _
  have hexp : (Vmax / Km) * |s - t| * ((Km + s) * (Km + t))
      = Vmax * |s - t| * ((Km + s) * (Km + t)) / Km := by ring
  rw [hexp, le_div_iff₀ hKm]
  nlinarith [mul_nonneg hV hst, mul_le_mul h1 h2 (le_of_lt hKm) (le_of_lt hKs),
    mul_nonneg (mul_nonneg hV hst) (le_of_lt (mul_pos hKs hKt))]

/-- **The reduced field is globally Lipschitz** with constant `Vmax/Km`, the input Mathlib's
autonomous-ODE existence theorem requires. Both physical pieces meet at the equilibrium `s = 0`,
and the negative piece is constant, so the global Lipschitz constant is that of the physical ray. -/
lemma mmReducedField_lipschitz (Km Vmax : ℝ) (hKm : 0 < Km) (hV : 0 ≤ Vmax) :
    LipschitzWith (Vmax / Km).toNNReal (mmReducedField Km Vmax) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro s t
  have hC : ((Vmax / Km).toNNReal : ℝ) = Vmax / Km := Real.coe_toNNReal _ (by positivity)
  rw [Real.dist_eq, Real.dist_eq, hC]
  simp only [mmReducedField]
  by_cases hs : 0 ≤ s <;> by_cases ht : 0 ≤ t
  · simp only [if_pos hs, if_pos ht]
    rw [show -(Vmax*s/(Km+s)) - -(Vmax*t/(Km+t)) = -(Vmax*s/(Km+s) - Vmax*t/(Km+t)) by ring,
      abs_neg]
    exact mmComplexEquil_lipschitz_aux Km Vmax hKm hV hs ht
  · simp only [if_pos hs, if_neg ht, sub_zero, abs_neg]
    have ht' : t < 0 := lt_of_not_ge ht
    have hkey := mmComplexEquil_lipschitz_aux Km Vmax hKm hV hs (le_refl 0)
    simp only [mul_zero, zero_div, sub_zero] at hkey
    refine le_trans hkey ?_
    have hpos : (0:ℝ) ≤ Vmax / Km := by positivity
    have habs : |s| ≤ |s - t| := by
      rw [abs_of_nonneg hs, abs_of_pos (by linarith : (0:ℝ) < s - t)]; linarith
    nlinarith [abs_nonneg s, abs_nonneg (s - t)]
  · simp only [if_neg hs, if_pos ht, zero_sub, abs_neg]
    have hs' : s < 0 := lt_of_not_ge hs
    have hkey := mmComplexEquil_lipschitz_aux Km Vmax hKm hV ht (le_refl 0)
    simp only [mul_zero, zero_div, sub_zero] at hkey
    refine le_trans hkey ?_
    have hpos : (0:ℝ) ≤ Vmax / Km := by positivity
    have habs : |t| ≤ |s - t| := by
      rw [abs_of_nonneg ht, abs_of_neg (by linarith : s - t < 0)]; linarith
    nlinarith [abs_nonneg t, abs_nonneg (s - t)]
  · simp only [if_neg hs, if_neg ht, sub_zero, abs_zero]
    positivity

/-- The reduced field is globally bounded by `Vmax.toNNReal` in norm, as `ODE.exists_isIntegralCurve`
requires. -/
lemma mmReducedField_norm_le (Km Vmax : ℝ) (hKm : 0 < Km) (hV : 0 ≤ Vmax) (x : ℝ) :
    ‖mmReducedField Km Vmax x‖ ≤ (Vmax.toNNReal : ℝ) := by
  rw [Real.norm_eq_abs, Real.coe_toNNReal Vmax hV]
  exact mmReducedField_abs_le Km Vmax hKm hV x

/-- The chosen global integral curve of `mmReducedField` through `s₀`, supplied by
`ODE.exists_isIntegralCurve`: a constructed solution of the scalar Michaelis–Menten ODE. -/
noncomputable def mmSubstrate (Km Vmax : ℝ) (hKm : 0 < Km) (hV : 0 ≤ Vmax) (s₀ : ℝ) : ℝ → ℝ :=
  (ODE.exists_isIntegralCurve (mmReducedField_lipschitz Km Vmax hKm hV)
    (mmReducedField_norm_le Km Vmax hKm hV) s₀).choose

/-- The constructed substrate curve starts at `s₀`. -/
lemma mmSubstrate_init (Km Vmax : ℝ) (hKm : 0 < Km) (hV : 0 ≤ Vmax) (s₀ : ℝ) :
    mmSubstrate Km Vmax hKm hV s₀ 0 = s₀ :=
  (ODE.exists_isIntegralCurve (mmReducedField_lipschitz Km Vmax hKm hV)
    (mmReducedField_norm_le Km Vmax hKm hV) s₀).choose_spec.1

/-- The constructed substrate curve solves the (extended) scalar reduced ODE everywhere. -/
lemma mmSubstrate_hasDerivAt (Km Vmax : ℝ) (hKm : 0 < Km) (hV : 0 ≤ Vmax) (s₀ : ℝ) (t : ℝ) :
    HasDerivAt (mmSubstrate Km Vmax hKm hV s₀)
      (mmReducedField Km Vmax (mmSubstrate Km Vmax hKm hV s₀ t)) t :=
  (ODE.exists_isIntegralCurve (mmReducedField_lipschitz Km Vmax hKm hV)
    (mmReducedField_norm_le Km Vmax hKm hV) s₀).choose_spec.2 t

/-- **Forward positivity of the constructed substrate curve.** From a nonnegative initial substrate
the curve stays nonnegative for all forward time: the field is nonpositive and vanishes at the
boundary `s = 0`, so a first return to `0` forces the curve constant thereafter, ruling out a
crossing into negative substrate. -/
lemma mmSubstrate_nonneg (Km Vmax : ℝ) (hKm : 0 < Km) (hV : 0 ≤ Vmax) {s₀ : ℝ} (hs0 : 0 ≤ s₀)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ mmSubstrate Km Vmax hKm hV s₀ t := by
  set σ := mmSubstrate Km Vmax hKm hV s₀ with hσ
  have hσd : ∀ u, HasDerivAt σ (mmReducedField Km Vmax (σ u)) u :=
    mmSubstrate_hasDerivAt Km Vmax hKm hV s₀
  have hσ0 : σ 0 = s₀ := mmSubstrate_init Km Vmax hKm hV s₀
  by_contra hneg
  rw [not_le] at hneg
  have hcont : Continuous σ := continuous_iff_continuousAt.2 fun u => (hσd u).continuousAt
  set S := {u | u ∈ Icc 0 t ∧ 0 ≤ σ u} with hS
  have h0S : (0 : ℝ) ∈ S := ⟨⟨le_refl 0, ht⟩, by rw [hσ0]; exact hs0⟩
  have hSne : S.Nonempty := ⟨0, h0S⟩
  have hSbdd : BddAbove S := ⟨t, fun u hu => hu.1.2⟩
  set t₀ := sSup S with ht₀
  have ht₀_lb : 0 ≤ t₀ := le_csSup hSbdd h0S
  have ht₀_ub : t₀ ≤ t := csSup_le hSne (fun u hu => hu.1.2)
  have hScl : IsClosed S := by
    have hSeq : S = Icc 0 t ∩ (σ ⁻¹' Ici 0) := by
      ext u; simp [hS, Set.mem_inter_iff, and_comm]
    rw [hSeq]; exact isClosed_Icc.inter (isClosed_Ici.preimage hcont)
  have ht₀S : t₀ ∈ S := hScl.csSup_mem hSne hSbdd
  have hσt₀ge : 0 ≤ σ t₀ := ht₀S.2
  have ht₀_lt : t₀ < t := by
    rcases lt_or_eq_of_le ht₀_ub with h | h
    · exact h
    · exfalso; rw [h] at hσt₀ge; linarith
  have hneg_on : ∀ u ∈ Ioc t₀ t, σ u < 0 := by
    intro u hu
    by_contra hge
    rw [not_lt] at hge
    have hmem : u ∈ S := ⟨⟨le_trans ht₀_lb hu.1.le, hu.2⟩, hge⟩
    exact absurd (le_csSup hSbdd hmem) (not_le.mpr hu.1)
  have hσt₀le : σ t₀ ≤ 0 := by
    have hlim : Tendsto σ (𝓝[Ioi t₀] t₀) (𝓝 (σ t₀)) :=
      (hcont.continuousAt).continuousWithinAt
    have hev : ∀ᶠ u in 𝓝[Ioi t₀] t₀, σ u ≤ 0 := by
      have hwin : Ioo t₀ t ∈ 𝓝[Ioi t₀] t₀ := by
        rw [mem_nhdsWithin]
        exact ⟨Iio t, isOpen_Iio, ht₀_lt, fun u hu => ⟨hu.2, hu.1⟩⟩
      filter_upwards [hwin] with u hu using (hneg_on u ⟨hu.1, hu.2.le⟩).le
    exact le_of_tendsto hlim hev
  have hσt₀ : σ t₀ = 0 := le_antisymm hσt₀le hσt₀ge
  have hderiv0 : ∀ x ∈ Ico t₀ t, HasDerivWithinAt σ 0 (Ici x) x := by
    intro x hx
    have hd := (hσd x).hasDerivWithinAt (s := Ici x)
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst h; rw [hσt₀, mmReducedField_zero] at hd; exact hd
    · rw [mmReducedField_neg_eq_zero Km Vmax (hneg_on x ⟨h, hx.2.le⟩)] at hd; exact hd
  have hconst := constant_of_has_deriv_right_zero hcont.continuousOn hderiv0 t ⟨ht₀_ub, le_refl t⟩
  rw [hσt₀] at hconst
  linarith

/-- On the forward ray the constructed substrate curve solves the **true** Michaelis–Menten scalar
ODE `ṡ = -mmComplexEquil Km Vmax s`, the field extension having vanished. -/
lemma mmSubstrate_hasDerivAt_mm (Km Vmax : ℝ) (hKm : 0 < Km) (hV : 0 ≤ Vmax) {s₀ : ℝ}
    (hs0 : 0 ≤ s₀) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (mmSubstrate Km Vmax hKm hV s₀)
      (-mmComplexEquil Km Vmax (mmSubstrate Km Vmax hKm hV s₀ t)) t := by
  have hd := mmSubstrate_hasDerivAt Km Vmax hKm hV s₀ t
  rwa [mmReducedField_of_nonneg Km Vmax (mmSubstrate_nonneg Km Vmax hKm hV hs0 ht)] at hd

/-- The pointwise `s`-derivative of the Michaelis–Menten complex level on the physical ray:
`d/ds (Vmax·s/(Km+s)) = Vmax·Km/(Km+s)²`. -/
lemma mmComplexEquil_hasDerivAt (Km Vmax : ℝ) (hKm : 0 < Km) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt (mmComplexEquil Km Vmax) (Vmax * Km / (Km + s) ^ 2) s := by
  have hKs : Km + s ≠ 0 := by positivity
  have hnum : HasDerivAt (fun s => Vmax * s) Vmax s := by
    simpa using (hasDerivAt_id s).const_mul Vmax
  have hden : HasDerivAt (fun s => Km + s) 1 s := by
    simpa using (hasDerivAt_id s).const_add Km
  have h := hnum.div hden hKs
  have heq : (Vmax * (Km + s) - Vmax * s * 1) / (Km + s) ^ 2 = Vmax * Km / (Km + s) ^ 2 := by
    rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  rw [heq] at h
  exact h

/-- The lifted reduced complex curve `t ↦ mmComplexEquil Km Vmax (σ t) • e0` has, on the forward
ray, the explicit derivative `(Vmax·Km/(Km+σ t)² · (-mmComplexEquil Km Vmax (σ t))) • e0` — the
chain rule applied to the constructed substrate ODE. -/
lemma mmReducedComplex_hasDerivAt (Km Vmax : ℝ) (hKm : 0 < Km) (hV : 0 ≤ Vmax) {s₀ : ℝ}
    (hs0 : 0 ≤ s₀) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun u => mmComplexEquil Km Vmax (mmSubstrate Km Vmax hKm hV s₀ u) • e0)
      ((Vmax * Km / (Km + mmSubstrate Km Vmax hKm hV s₀ t) ^ 2 *
        (-mmComplexEquil Km Vmax (mmSubstrate Km Vmax hKm hV s₀ t))) • e0) t := by
  set σ := mmSubstrate Km Vmax hKm hV s₀ with hσ
  have hσd := mmSubstrate_hasDerivAt_mm Km Vmax hKm hV hs0 ht
  have hpos := mmSubstrate_nonneg Km Vmax hKm hV hs0 ht
  have hcomp : HasDerivAt (fun u => mmComplexEquil Km Vmax (σ u))
      (Vmax * Km / (Km + σ t) ^ 2 * (-mmComplexEquil Km Vmax (σ t))) t :=
    (mmComplexEquil_hasDerivAt Km Vmax hKm hpos).comp t hσd
  exact hcomp.smul_const e0

/-- **Closed compact-time Michaelis–Menten reduction error theorem.** Let `full` be a `K`-Lipschitz
full enzyme mass-action field with exact integral curve `γ`. Construct the reduced substrate curve
`σ := mmSubstrate Km Vmax hKm hV s₀` from a nonnegative initial substrate `s₀`. If the constructed
reduced complex curve `t ↦ mmComplexEquil Km Vmax (σ t) • e0` carries slaving defect at most `εf`
against its own derivative `t ↦ (Vmax·Km/(Km+σ t)² · (-mmComplexEquil Km Vmax (σ t))) • e0` on
`[0, T)`, and the initial mismatch is at most `δ`, then on `[0, T]` the exact trajectory stays
within `gronwallBound δ K εf T` of the reduced complex curve, and that bound vanishes as `(δ, εf)`
jointly vanish. The substrate path, its continuity, and its right-derivative law are all derived
from the constructed `σ`; only `full`, `γ`, `δ`, `εf` remain as data. -/
theorem michaelisMenten_reduced_qssa_error (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ)
    (hKm : 0 < Km) (hV : 0 ≤ Vmax) {s₀ : ℝ} (hs0 : 0 ≤ s₀)
    (full : E → E) {K : ℝ≥0} (hl : LipschitzWith K full)
    {γ : ℝ → E} {T εf δ : ℝ} (hT : 0 ≤ T) (hδ : 0 ≤ δ) (hεf : 0 ≤ εf)
    (hγd : ∀ t, HasDerivAt γ (full (γ t)) t)
    (hdef : ODE.QssaDefect full
      (fun t => mmComplexEquil Km Vmax (mmSubstrate Km Vmax hKm hV s₀ t) • e0)
      (fun t => (Vmax * Km / (Km + mmSubstrate Km Vmax hKm hV s₀ t) ^ 2 *
        (-mmComplexEquil Km Vmax (mmSubstrate Km Vmax hKm hV s₀ t))) • e0) 0 T εf)
    (h0 : dist (γ 0) (mmComplexEquil Km Vmax (mmSubstrate Km Vmax hKm hV s₀ 0) • e0) ≤ δ) :
    (∀ t ∈ Icc 0 T,
        dist (γ t) (mmComplexEquil Km Vmax (mmSubstrate Km Vmax hKm hV s₀ t) • e0)
          ≤ gronwallBound δ K εf T) ∧
      Tendsto (fun p : ℝ × ℝ => gronwallBound p.1 K p.2 T) (𝓝 0 ×ˢ 𝓝 0) (𝓝 0) := by
  set σ := mmSubstrate Km Vmax hKm hV s₀ with hσ
  -- continuity of the lifted reduced curve on [0, T]
  have hσcont : Continuous σ := continuous_iff_continuousAt.2 fun u =>
    (mmSubstrate_hasDerivAt Km Vmax hKm hV s₀ u).continuousAt
  have hσc : ContinuousOn (fun t => mmComplexEquil Km Vmax (σ t) • e0) (Icc 0 T) := by
    refine ContinuousOn.smul (f := fun t => mmComplexEquil Km Vmax (σ t))
      (g := fun _ => e0) ?_ continuousOn_const
    have hmm : ContinuousOn (mmComplexEquil Km Vmax) (Ici 0) := by
      have hfun : mmComplexEquil Km Vmax = fun s => Vmax * s / (Km + s) := rfl
      rw [hfun]
      refine ContinuousOn.div (by fun_prop) (by fun_prop) (fun s hs => ?_)
      have : (0:ℝ) ≤ s := hs; positivity
    refine hmm.comp hσcont.continuousOn ?_
    intro t ht
    exact mmSubstrate_nonneg Km Vmax hKm hV hs0 ht.1
  -- right-derivative law from the chain rule
  have hσ' : ∀ t ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt (fun t => mmComplexEquil Km Vmax (σ t) • e0)
        ((Vmax * Km / (Km + σ t) ^ 2 * (-mmComplexEquil Km Vmax (σ t))) • e0) (Ici t) t :=
    fun t ht => (mmReducedComplex_hasDerivAt Km Vmax hKm hV hs0 ht.1).hasDerivWithinAt
  exact michaelisMenten_manifold_qssa_error_const rate hrate Km Vmax full hl hT hδ hεf hγd
    hσc hσ' hdef h0

end CRNT.MichaelisMenten
