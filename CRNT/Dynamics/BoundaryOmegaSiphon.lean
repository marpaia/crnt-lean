import CRNT.Dynamics.NegativeInvariance
import CRNT.Dynamics.StrictInflow
import CRNT.Dynamics.GlobalStability
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The zero set of a boundary ω-limit point is a siphon

The Angeli–De Leenheer–Sontag structural fact behind persistence: for a mass-action semiflow
whose orbit is bounded, the zero set `Z(w) = {s | w s = 0}` of any ω-limit point `w` is a
**siphon**. This is the bridge from the abstract dynamics to the combinatorial siphon condition —
once it holds, ruling out *critical* siphons rules out boundary ω-limit points, which is exactly
persistence.

The proof assembles the two preceding results. Suppose `Z(w)` is **not** a siphon. Then
`massActionVectorField_pos_of_not_isSiphon` gives an empty species `s` (`w s = 0`) with strictly
positive inflow `0 < ẋ_s(w)`. By `omegaLimit_negInvariant` there is `w' ∈ ω` with `ϕ 1 w' = w`,
so the genuine orbit `t ↦ γ w' t` reaches `w` at `t = 1` with derivative `ẋ(w)` there. Its
`s`-coordinate is nonnegative on `[0, ∞)` (the orbit stays in `ω`, whose points are nonnegative)
and vanishes at `t = 1`, so `1` is a local minimum; Fermat forces the derivative there to vanish,
contradicting `0 < ẋ_s(w)`.

The hypotheses isolate exactly what the genuine-field semiflow construction supplies: orbit
boundedness (`hmaps`), nonnegativity of ω-points (`hωnn`), and that ω-orbits solve the genuine
field (`hgenω`). No persistence/positivity assumption is made — `w` is allowed on the boundary,
which is the whole point.

Depends on: `CRNT.Dynamics.NegativeInvariance`,
`CRNT.Dynamics.StrictInflow`, `CRNT.Dynamics.GlobalStability`.
-/

open Filter Topology
open scoped BigOperators NNReal

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The zero set of a boundary ω-limit point is a siphon.** For a mass-action semiflow `ϕ`
(with integral curves `γ`, `hϕγ`) whose orbit through `x₀` stays in a compact `K` (`hmaps`),
whose ω-limit points are nonnegative (`hωnn`) and whose ω-orbits solve the genuine field
(`hgenω`), the zero set `P` of any ω-limit point `w` is a siphon. -/
theorem isSiphon_zeroSet_of_mem_omegaLimit (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S} (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, (y : Concentration S).Nonnegative)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    {w : Concentration S} (hw : w ∈ omegaLimit atTop ϕ {x₀})
    {P : Finset S} (hP : ∀ s, s ∈ P ↔ w s = 0) :
    N.IsSiphon P := by
  by_contra hns
  -- strict inflow at an empty species `s`
  obtain ⟨s, hsP, hpos⟩ := N.massActionVectorField_pos_of_not_isSiphon κ (hωnn w hw) hP hns
  -- backward invariance: a predecessor `w' ∈ ω` reaching `w` at time `1`
  obtain ⟨w', hw'ω, hw'eq⟩ := omegaLimit_negInvariant ϕ x₀ hK hmaps 1 hw
  have hγw'1 : γ w' (1 : ℝ) = w := by
    have h := hϕγ w' 1
    rw [hw'eq, NNReal.coe_one] at h
    exact h.symm
  -- forward invariance keeps the orbit of `w'` inside `ω`
  have hfwd : ∀ τ : ℝ≥0, ϕ τ w' ∈ omegaLimit atTop ϕ {x₀} := fun τ =>
    Flow.isInvariant_omegaLimit atTop ϕ {x₀}
      (fun t => tendsto_atTop_mono (fun _ => le_add_self) tendsto_id) τ hw'ω
  -- the `s`-coordinate along the orbit of `w'` is nonnegative for all forward time
  have hge : ∀ t : ℝ, 0 ≤ t → 0 ≤ γ w' t s := by
    intro t ht
    have hmem : γ w' t ∈ omegaLimit atTop ϕ {x₀} := by
      have h := hfwd ⟨t, ht⟩
      exact (hϕγ w' ⟨t, ht⟩) ▸ h
    exact hωnn _ hmem s
  -- it vanishes at `t = 1`, so `1` is a local minimum
  have hf1 : γ w' (1 : ℝ) s = 0 := by rw [hγw'1]; exact (hP s).mp hsP
  have hlocmin : IsLocalMin (fun t => γ w' t s) 1 := by
    have hev : ∀ᶠ t in 𝓝 (1 : ℝ), (fun t => γ w' t s) 1 ≤ (fun t => γ w' t s) t := by
      filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
      show γ w' 1 s ≤ γ w' t s
      rw [hf1]; exact hge t (le_of_lt ht)
    exact hev
  -- but the derivative there is the strictly positive inflow `ẋ_s(w)`
  have hderiv : HasDerivAt (fun t => γ w' t s) (N.massActionVectorField κ w s) 1 := by
    have H := hgenω w' hw'ω 1 zero_le_one
    rw [hγw'1] at H
    exact (hasDerivAt_pi.mp H) s
  have hzero : N.massActionVectorField κ w s = 0 := hlocmin.hasDerivAt_eq_zero hderiv
  rw [hzero] at hpos
  exact lt_irrefl 0 hpos

end Network

end CRNT
