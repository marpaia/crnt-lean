import CRNT.Persistence.WeaklyReversibleFloor
import CRNT.Flux.PSemiflow
import CRNT.Dynamics.GlobalPersistenceFrontier

/-!
# Conservative weakly reversible networks are persistent

For a weakly reversible network with a strictly positive conservation law, every forward
mass-action solution from a positive state stays in a compact set of positive states that
depends only on the initial state: `weaklyReversible_conservative_persistentFrom`.  Hence such
networks are `StructurallyPersistent`, and the strong form of the Persistence Conjecture holds
for them (`persistenceConjectureStrong_of_conservative`).

Ingredients: the conservation law bounds every coordinate while the solution is nonnegative;
`orbit_pos_forward_of_bdd_nonneg` (the first-hitting-time argument of `orbit_pos_forward`, which
uses the box only at nonnegative states) then gives positivity, hence the bound for all forward
time; `weaklyReversible_forward_floor_uniform` gives a floor depending only on the initial state
and the bound.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Network

open Set Finset

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Forward positivity when the box bound is only known at nonnegative states. -/
theorem orbit_pos_forward_of_bdd_nonneg (N : Network S) (κ : N.RateConstants) {B : ℝ}
    {Γ : ℝ → Concentration S} (hΓ0 : (Γ 0).Positive)
    (hΓbdd : ∀ t : ℝ, 0 ≤ t → (Γ t).Nonnegative → ∀ s, Γ t s ≤ B)
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
      exact hbound (Γ τ) hnn (hΓbdd τ hτ.1 hnn) s₁
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


/-- A strictly positive conservation law bounds every forward solution from a positive state,
by a constant depending only on the initial state. -/
theorem conservative_forward_bound (N : Network S) (κ : N.RateConstants)
    {w : S → ℝ} (hw : N.IsStrictPSemiflow w) {x₀ : Concentration S} (hx₀ : x₀.Positive) :
    ∃ B : ℝ, ∀ Γ : ℝ → Concentration S, Γ 0 = x₀ →
      (∀ t : ℝ, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t) →
      ∀ t : ℝ, 0 ≤ t → ∀ s, Γ t s ≤ B := by
  set W := weightedTotal w x₀
  refine ⟨∑ s, W / w s, fun Γ hΓ0 hΓd => ?_⟩
  have hW : 0 ≤ W := Finset.sum_nonneg fun s _ => mul_nonneg (hw.2 s).le (hx₀ s).le
  have hbnn : ∀ t : ℝ, 0 ≤ t → (Γ t).Nonnegative → ∀ s, Γ t s ≤ ∑ s, W / w s := by
    intro t ht hnn s
    have hc := N.stoichCompatible_of_forward_solution κ hΓd t ht
    rw [hΓ0] at hc
    have h1 := N.coordinate_le_of_strictPSemiflow hw hx₀.nonnegative hnn hc s
    have h2 : W / w s ≤ ∑ s, W / w s :=
      Finset.single_le_sum (f := fun s => W / w s) (fun s _ => div_nonneg hW (hw.2 s).le)
        (Finset.mem_univ s)
    exact h1.trans h2
  have hpos := N.orbit_pos_forward_of_bdd_nonneg κ (hΓ0 ▸ hx₀) hbnn hΓd
  exact fun t ht => hbnn t ht (hpos t ht).nonnegative

/-- **Conservative weakly reversible networks are persistent from every positive state.** -/
theorem weaklyReversible_conservative_persistentFrom (N : Network S) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) (hcons : N.IsConservative) {x₀ : Concentration S}
    (hx₀ : x₀.Positive) : N.PersistentFrom κ x₀ := by
  obtain ⟨w, hw⟩ := hcons
  obtain ⟨B, hB⟩ := N.conservative_forward_bound κ hw hx₀
  obtain ⟨η, hη, hfloor⟩ := N.weaklyReversible_forward_floor_uniform κ hwr hx₀ B
  refine ⟨Set.univ.pi fun _ => Set.Icc η B, isCompact_univ_pi fun _ => isCompact_Icc,
    fun y hy s => lt_of_lt_of_le hη (hy s (Set.mem_univ s)).1, fun Γ hΓ0 hΓd t ht => ?_⟩
  intro s _
  exact ⟨hfloor Γ hΓ0 hΓd (hB Γ hΓ0 hΓd) t ht s, hB Γ hΓ0 hΓd t ht s⟩

/-- Conservative weakly reversible networks are structurally persistent. -/
theorem weaklyReversible_conservative_structurallyPersistent (N : Network S)
    (hwr : N.WeaklyReversible) (hcons : N.IsConservative) : N.StructurallyPersistent :=
  fun κ _ hx₀ => N.weaklyReversible_conservative_persistentFrom κ hwr hcons hx₀

/-- **The strong Persistence Conjecture holds for conservative networks.** -/
theorem persistenceConjectureStrong_of_conservative (N : Network S)
    (hcons : N.IsConservative) : N.PersistenceConjectureStrong :=
  fun hwr => N.weaklyReversible_conservative_structurallyPersistent hwr hcons

/-- The classical Persistence Conjecture holds for conservative networks. -/
theorem persistenceConjecture_of_conservative (N : Network S)
    (hcons : N.IsConservative) : N.PersistenceConjecture :=
  persistenceConjectureStrong_implies_standard (N.persistenceConjectureStrong_of_conservative hcons)

end Network
end CRNT
