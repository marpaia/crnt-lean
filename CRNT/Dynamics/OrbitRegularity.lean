import CRNT.Dynamics.ToricBarrierExplicit
import CRNT.Theorems.DeficiencyZero.AsymptoticStability

/-!
# Orbit regularity for a forward mass-action solution

`docs/gac-bridge-gap-analysis.md` identifies three facts about the orbit that the residual
obligation of the Global Attractor Theorem does not itself supply but that the toric barrier chain
needs.  This module discharges two of them from the residual's own hypotheses.

* **Bridge 3**, `stoichCompatible_of_forward_solution`: a forward solution stays in the
  stoichiometric compatibility class of its initial value.  This is a corollary of
  `Network.sub_mem_stoichSubspace_of_solution`, which already existed in
  `CRNT.Theorems.DeficiencyZero.AsymptoticStability`; an earlier version of this module reproved it
  from scratch, which was wasted work.
* **Bridge 2**, `orbit_pos_forward`: a forward solution starting positive and staying in a box
  remains strictly positive.

## Why `orbit_pos` does not already do bridge 2

`Network.orbit_pos` has the right argument -- first-hitting-time plus a Gronwall bound -- but is
stated for the **clamped** field `massActionVectorField κ (clampBox B (Γ t))` and for *all* `t`,
because it is built for the `ODE.exists_flow` construction.  The residual supplies the unclamped
field for `t ≥ 0` only.

`orbit_pos_forward` is the unclamped forward version.  Dropping the clamp simplifies the Gronwall
step -- no `clampBox` juggling -- at the cost of an explicit box hypothesis `hΓbdd`, which in the
residual's context comes from the compact `K` containing the orbit.  Continuity is only available
on `Set.Ici 0`, so the closed sets in the first-hitting-time argument are built with
`IsClosed.isClosed_le` relative to `Ici 0`, and the passage to the limit uses `le_on_closure`
rather than a globally closed set.

The Gronwall input is supplied internally by `Network.exists_field_lower_bound`: every consuming
reaction's monomial carries a factor of the species it consumes, so `f_s(x) ≥ -L · x s` on a box.

Nothing here is an axiom or a `sorry`.

Depends on: `CRNT.Dynamics.ToricBarrierExplicit`,
`CRNT.Theorems.DeficiencyZero.AsymptoticStability`.
-/

namespace CRNT
namespace Network

open Set

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ### Bridge 3: class invariance -/

/-- **Bridge 3.**  A forward mass-action solution never leaves the stoichiometric compatibility
class of its initial value. -/
theorem stoichCompatible_of_forward_solution (N : Network S) (κ : N.RateConstants)
    {Γ : ℝ → Concentration S}
    (hΓd : ∀ t : ℝ, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t) :
    ∀ t : ℝ, 0 ≤ t → N.StoichCompatible (Γ 0) (Γ t) := fun _t ht =>
  N.sub_mem_stoichSubspace_of_solution κ ht fun τ hτ => hΓd τ hτ.1

/-! ### Bridge 2: forward positivity -/

/-- **Bridge 2.**  A forward mass-action solution that starts strictly positive and stays inside
the box `[0, B]` remains strictly positive for all forward time.

Unlike `Network.orbit_pos` this is stated for the *unclamped* field and only assumes
differentiability for `t ≥ 0`, which is what `Network.PositiveOmegaPointForRates` provides. -/
theorem orbit_pos_forward (N : Network S) (κ : N.RateConstants) {B : ℝ}
    {Γ : ℝ → Concentration S} (hΓ0 : (Γ 0).Positive)
    (hΓbdd : ∀ t : ℝ, 0 ≤ t → ∀ s, Γ t s ≤ B)
    (hΓd : ∀ t : ℝ, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t) :
    ∀ t : ℝ, 0 ≤ t → (Γ t).Positive := by
  obtain ⟨L, hL, hbound⟩ := N.exists_field_lower_bound κ B
  have hcs : ∀ s : S, ContinuousOn (fun t => Γ t s) (Ici 0) := by
    intro s t ht
    exact (((hasDerivAt_pi.mp (hΓd t ht)) s).continuousAt).continuousWithinAt
  intro T hT
  by_contra hcon
  obtain ⟨s₀, hs₀⟩ : ∃ s, Γ T s ≤ 0 := by
    by_contra h
    simp only [not_exists, not_le] at h
    exact hcon h
  set A : Set ℝ := ⋃ s : S, {t ∈ Ici (0 : ℝ) | Γ t s ≤ 0} with hA
  have hAne : A.Nonempty := ⟨T, mem_iUnion.mpr ⟨s₀, ⟨hT, hs₀⟩⟩⟩
  have hAcl : IsClosed A := by
    rw [hA]
    exact isClosed_iUnion_of_finite fun s =>
      isClosed_Ici.isClosed_le (hcs s) continuousOn_const
  have hAbdd : BddBelow A := by
    refine ⟨0, fun t ht => ?_⟩
    obtain ⟨s, hs⟩ := mem_iUnion.mp ht
    exact hs.1
  set t₁ := sInf A with ht₁def
  have ht₁A : t₁ ∈ A := hAcl.csInf_mem hAne hAbdd
  obtain ⟨s₁, hs₁mem⟩ := mem_iUnion.mp ht₁A
  have ht₁0 : 0 ≤ t₁ := hs₁mem.1
  have hs₁ : Γ t₁ s₁ ≤ 0 := hs₁mem.2
  have hbefore : ∀ t : ℝ, 0 ≤ t → t < t₁ → (Γ t).Positive := by
    intro t ht htlt s
    by_contra hle
    rw [not_lt] at hle
    exact absurd (csInf_le hAbdd (mem_iUnion.mpr ⟨s, ⟨ht, hle⟩⟩)) (not_le.mpr htlt)
  rcases eq_or_lt_of_le ht₁0 with ht₁eq | ht₁pos
  · rw [← ht₁eq] at hs₁
    exact absurd (hΓ0 s₁) (not_lt.mpr hs₁)
  · have key : ∀ t ∈ Ico (0 : ℝ) t₁, Γ 0 s₁ * Real.exp (-(L * t)) ≤ Γ t s₁ := by
      intro t ht
      refine ge_mul_exp_of_forward_deriv_ge ht.1
        (fun τ hτ => (hasDerivAt_pi.mp (hΓd τ hτ.1)) s₁) ?_
      intro τ hτ
      have hτlt : τ < t₁ := lt_of_le_of_lt hτ.2 ht.2
      have hnn : (Γ τ).Nonnegative := (hbefore τ hτ.1 hτlt).nonnegative
      exact hbound (Γ τ) hnn (hΓbdd τ hτ.1) s₁
    have hclos : closure (Ico (0 : ℝ) t₁) = Icc 0 t₁ := closure_Ico (ne_of_lt ht₁pos)
    have hcont₁ : ContinuousOn (fun t : ℝ => Γ 0 s₁ * Real.exp (-(L * t)))
        (closure (Ico (0 : ℝ) t₁)) :=
      (continuous_const.mul
        (Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg))).continuousOn
    have hcont₂ : ContinuousOn (fun t => Γ t s₁) (closure (Ico (0 : ℝ) t₁)) := by
      rw [hclos]
      exact (hcs s₁).mono fun t ht => ht.1
    have ht₁mem : t₁ ∈ closure (Ico (0 : ℝ) t₁) := by
      rw [hclos]
      exact ⟨ht₁0, le_rfl⟩
    have hlim := le_on_closure key hcont₁ hcont₂ ht₁mem
    exact absurd (lt_of_lt_of_le (mul_pos (hΓ0 s₁) (Real.exp_pos _)) hlim) (not_lt.mpr hs₁)

end Network
end CRNT
