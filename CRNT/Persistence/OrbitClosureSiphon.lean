import CRNT.Dynamics.StrictInflow
import CRNT.Dynamics.GenuineConfinement
import CRNT.Dynamics.DissipationBound
import CRNT.Dynamics.ReactionConeDisplacement
import CRNT.Decision.StrictConeRealization
import CRNT.Dynamics.SiphonAutocatalysis
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import CRNT.Dynamics.GlobalPersistence

/-!
# Closure points of positive orbits: siphons and drainability without boundedness

For a forward mass-action solution `γ` from a positive state and any point `w` of the closure of its
forward orbit, the zero set of `w` is a siphon (`isSiphon_zeroSet_of_orbitClosure`) and, when
nonempty, drainable (`isDrainableSiphon_zeroSet_of_orbitClosure`).  Hence, with no drainable
siphon, every closure point of every positive orbit is positive
(`orbitClosure_positive_of_hasNoDrainableSiphon`): Deshpande–Gopalkrishnan 2014, Theorem 6.2,
with no boundedness hypothesis.

The siphon step replaces the backward invariance of the ω-limit set (which needs a bounded orbit)
by an exit-time argument: near `w` the empty species `s` has inflow at least `c > 0` and the field
is bounded by `M`, so an orbit point within `r/2` of `w` with `γ_s < c r / (2M)` must have stayed in
the `r`-ball since its last exit, during which `γ_s` grew by at least `c` per unit time while the
orbit moved at most `M` per unit time; the two estimates are incompatible.

Nothing here is an axiom or a `sorry`.
-/

open Set Metric Filter Topology

namespace CRNT
namespace Persistence

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Mean-value bounds on a time interval along which the orbit stays in a region where the field
satisfies `c ≤ F_s` and `|F_q| ≤ M`. -/
theorem interval_bounds {F : (S → ℝ) → S → ℝ} {γ : ℝ → S → ℝ}
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt γ (F (γ t)) t) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {s : S} {c M : ℝ} (hin : ∀ τ ∈ Ioo a b, c ≤ F (γ τ) s ∧ ∀ q, |F (γ τ) q| ≤ M) :
    c * (b - a) ≤ γ b s - γ a s ∧ ∀ q, |γ b q - γ a q| ≤ M * (b - a) := by
  have hco : ∀ q, ContinuousOn (fun τ => γ τ q) (Icc a b) := fun q τ hτ =>
    ((hasDerivAt_pi.mp (hsol τ (ha.trans hτ.1))) q).continuousAt.continuousWithinAt
  have hder : ∀ q, ∀ τ ∈ Ioo a b, HasDerivAt (fun τ => γ τ q) (F (γ τ) q) τ := fun q τ hτ =>
    (hasDerivAt_pi.mp (hsol τ (ha.trans hτ.1.le))) q
  have hdo : ∀ q, DifferentiableOn ℝ (fun τ => γ τ q) (interior (Icc a b)) := by
    intro q τ hτ
    rw [interior_Icc] at hτ
    exact (hder q τ hτ).differentiableAt.differentiableWithinAt
  have hderiv : ∀ q, ∀ τ ∈ interior (Icc a b), deriv (fun τ => γ τ q) τ = F (γ τ) q := by
    intro q τ hτ
    rw [interior_Icc] at hτ
    exact (hder q τ hτ).deriv
  have ham : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hbm : b ∈ Icc a b := ⟨hab, le_rfl⟩
  refine ⟨?_, fun q => ?_⟩
  · refine (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv (hco s) (hdo s) (fun τ hτ => ?_)
      a ham b hbm hab
    rw [hderiv s τ hτ]
    rw [interior_Icc] at hτ
    exact (hin τ hτ).1
  · have hup := (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le (hco q) (hdo q) (C := M)
      (fun τ hτ => by
        rw [hderiv q τ hτ]; rw [interior_Icc] at hτ
        exact (abs_le.mp ((hin τ hτ).2 q)).2) a ham b hbm hab
    have hlo := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv (hco q) (hdo q) (C := -M)
      (fun τ hτ => by
        rw [hderiv q τ hτ]; rw [interior_Icc] at hτ
        exact (abs_le.mp ((hin τ hτ).2 q)).1) a ham b hbm hab
    rw [abs_le]; constructor <;> linarith

/-- **Exit-time contradiction.** Let `c ≤ F_s` and `|F_q| ≤ M` on the closed `r`-ball around
`w`.  A positive solution cannot reach the `r/2`-ball around `w` at a time where its `s`-coordinate
is below both its initial value and `c r / (2M)`. -/
theorem exit_time_contradiction {F : (S → ℝ) → S → ℝ} {γ : ℝ → S → ℝ}
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt γ (F (γ t)) t)
    (hpos : ∀ t : ℝ, 0 ≤ t → ∀ q, 0 < γ t q) {w : S → ℝ} {r c M : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hM : 0 < M) {s : S} (hball : ∀ y, dist y w < r → c ≤ F y s ∧ ∀ q, |F y q| ≤ M)
    {t : ℝ} (ht : 0 ≤ t) (hnear : dist (γ t) w < r / 2) (hs0 : γ t s < γ 0 s)
    (hsc : γ t s < c * r / (2 * M)) : False := by
  set A : Set ℝ := Icc 0 t ∩ (fun τ => dist (γ τ) w) ⁻¹' Ici r with hA
  have hγc : ContinuousOn γ (Icc 0 t) := fun τ hτ =>
    (hsol τ hτ.1).continuousAt.continuousWithinAt
  rcases A.eq_empty_or_nonempty with hAe | hAne
  · -- the orbit stays in the ball on `[0, t]`
    have hin : ∀ τ ∈ Ioo 0 t, c ≤ F (γ τ) s ∧ ∀ q, |F (γ τ) q| ≤ M := by
      intro τ hτ
      refine hball _ (not_le.mp fun h => ?_)
      have : τ ∈ A := ⟨⟨hτ.1.le, hτ.2.le⟩, h⟩
      rw [hAe] at this; exact this
    have h := (interval_bounds hsol le_rfl ht hin).1
    have : 0 ≤ c * (t - 0) := mul_nonneg hc.le (by linarith)
    linarith
  · have hAcl : IsClosed A := (((continuous_id.dist continuous_const).comp_continuousOn hγc :
      ContinuousOn (fun τ => dist (γ τ) w) (Icc 0 t))).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_Ici
    have hAbdd : BddAbove A := ⟨t, fun τ hτ => hτ.1.2⟩
    set ts := sSup A with hts
    have htsA : ts ∈ A := hAcl.csSup_mem hAne hAbdd
    have hts0 : 0 ≤ ts := htsA.1.1
    have htst : ts ≤ t := htsA.1.2
    have hin : ∀ τ ∈ Ioo ts t, c ≤ F (γ τ) s ∧ ∀ q, |F (γ τ) q| ≤ M := by
      intro τ hτ
      refine hball _ (not_le.mp fun h => ?_)
      have hτA : τ ∈ A := ⟨⟨hts0.trans hτ.1.le, hτ.2.le⟩, h⟩
      exact absurd (le_csSup hAbdd hτA) (not_le.mpr hτ.1)
    obtain ⟨h1, h2⟩ := interval_bounds hsol hts0 htst hin
    -- some coordinate moved by more than `r/2`
    have hfar : r ≤ dist (γ ts) w := htsA.2
    obtain ⟨q, hq⟩ : ∃ q, r ≤ dist (γ ts q) (w q) := by
      by_contra hcon
      push Not at hcon
      exact absurd ((dist_pi_lt_iff hr).mpr hcon) (not_lt.mpr hfar)
    have hqt : dist (γ t q) (w q) < r / 2 := lt_of_le_of_lt (dist_le_pi_dist _ _ q) hnear
    rw [Real.dist_eq] at hq hqt
    have hmove : r / 2 < |γ t q - γ ts q| := by
      have := abs_sub_abs_le_abs_sub (γ ts q - w q) (γ t q - w q)
      have e : γ ts q - w q - (γ t q - w q) = -(γ t q - γ ts q) := by ring
      rw [e, abs_neg] at this
      linarith
    have hq2 := h2 q
    have hspos := hpos ts hts0 s
    have hdt : t - ts < γ t s / c := by
      rw [lt_div_iff₀ hc]; linarith
    have : M * (t - ts) < M * (γ t s / c) := mul_lt_mul_of_pos_left hdt hM
    have hfin : M * (γ t s / c) < r / 2 := by
      rw [mul_div_assoc', div_lt_iff₀ hc]
      have := (lt_div_iff₀ (by positivity : (0:ℝ) < 2 * M)).mp hsc
      nlinarith
    linarith

end Persistence

namespace Network

open Persistence

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Closure points of a positive forward orbit are nonnegative. -/
theorem orbitClosure_nonnegative (N : Network S) (κ : N.RateConstants) {γ : ℝ → Concentration S}
    (hγ0 : (γ 0).Positive) (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    {w : Concentration S} (hw : ∀ ε > 0, ∃ t, 0 ≤ t ∧ dist (γ t) w < ε) : w.Nonnegative := by
  have hpos := N.genuineOrbit_pos κ hγ0 hsol
  intro s
  by_contra hneg
  push Not at hneg
  obtain ⟨t, ht, hd⟩ := hw (-w s) (by linarith)
  have h1 := lt_of_le_of_lt (dist_le_pi_dist _ _ s) hd
  rw [Real.dist_eq] at h1
  have h2 := hpos t ht s
  have := (abs_lt.mp h1).2
  linarith

/-- **The zero set of a closure point of a positive orbit is a siphon** (no boundedness). -/
theorem isSiphon_zeroSet_of_orbitClosure (N : Network S) (κ : N.RateConstants)
    {γ : ℝ → Concentration S} (hγ0 : (γ 0).Positive)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    {w : Concentration S} (hw : ∀ ε > 0, ∃ t, 0 ≤ t ∧ dist (γ t) w < ε)
    {P : Finset S} (hP : ∀ s, s ∈ P ↔ w s = 0) : N.IsSiphon P := by
  have hpos := N.genuineOrbit_pos κ hγ0 hsol
  have hwnn := N.orbitClosure_nonnegative κ hγ0 hsol hw
  by_contra hns
  obtain ⟨s, hsP, hfs⟩ := N.massActionVectorField_pos_of_not_isSiphon κ hwnn hP hns
  set F := N.massActionVectorField κ with hF
  have hFc : Continuous F := N.continuous_massActionVectorField κ
  set c := F w s / 2 with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  obtain ⟨ρ, hρ, hρF⟩ := Metric.continuous_iff.mp hFc w c hcpos
  obtain ⟨C, hC⟩ := (isCompact_closedBall w ρ).exists_bound_of_continuousOn hFc.continuousOn
  set M := max C 1 with hMdef
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hball : ∀ y, dist y w < ρ → c ≤ F y s ∧ ∀ q, |F y q| ≤ M := by
    intro y hy
    refine ⟨?_, fun q => ?_⟩
    · have h1 := lt_of_le_of_lt (dist_le_pi_dist (F y) (F w) s) (hρF y hy)
      rw [Real.dist_eq] at h1
      have := (abs_lt.mp h1).1
      linarith
    · have h1 : ‖F y q‖ ≤ ‖F y‖ := norm_le_pi_norm (F y) q
      have h2 := hC y (Metric.mem_closedBall.mpr hy.le)
      rw [Real.norm_eq_abs] at h1
      exact h1.trans (h2.trans (le_max_left _ _))
  have hs0 := hpos 0 le_rfl s
  set ε := min (ρ / 2) (min (γ 0 s) (c * ρ / (2 * M))) with hε
  have hεpos : 0 < ε := lt_min (by linarith) (lt_min hs0 (by positivity))
  obtain ⟨t, ht, hd⟩ := hw ε hεpos
  have hts : γ t s < ε := by
    have h1 := lt_of_le_of_lt (dist_le_pi_dist _ _ s) hd
    rw [Real.dist_eq, (hP s).mp hsP, sub_zero] at h1
    exact lt_of_le_of_lt (le_abs_self _) h1
  exact exit_time_contradiction (F := F) hsol (fun τ hτ q => hpos τ hτ q) hρ hcpos hM hball ht
    (lt_of_lt_of_le hd (min_le_left _ _))
    (lt_of_lt_of_le hts ((min_le_right _ _).trans (min_le_left _ _)))
    (lt_of_lt_of_le hts ((min_le_right _ _).trans (min_le_right _ _)))

/-- **The nonempty zero set of a closure point of a positive orbit is a drainable siphon.** -/
theorem isDrainableSiphon_zeroSet_of_orbitClosure (N : Network S) (κ : N.RateConstants)
    {γ : ℝ → Concentration S} (hγ0 : (γ 0).Positive)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    {w : Concentration S} (hw : ∀ ε > 0, ∃ t, 0 ≤ t ∧ dist (γ t) w < ε)
    {P : Finset S} (hP : ∀ s, s ∈ P ↔ w s = 0) (hPne : P.Nonempty) : N.IsDrainableSiphon P := by
  have hpos := N.genuineOrbit_pos κ hγ0 hsol
  have hPsiph := N.isSiphon_zeroSet_of_orbitClosure κ hγ0 hsol hw hP
  have hne : (Finset.univ : Finset S).Nonempty := ⟨hPne.choose, Finset.mem_univ _⟩
  set μ := Finset.univ.inf' hne (γ 0) with hμ
  have hμpos : 0 < μ := (Finset.lt_inf'_iff hne).mpr fun s _ => hγ0 s
  obtain ⟨t, ht, hd⟩ := hw μ hμpos
  have hlt : ∀ s ∈ P, γ t s < γ 0 s := by
    intro s hs
    have h1 := lt_of_le_of_lt (dist_le_pi_dist _ _ s) hd
    rw [Real.dist_eq, (hP s).mp hs, sub_zero] at h1
    exact lt_of_le_of_lt (le_abs_self _) (lt_of_lt_of_le h1
      (Finset.inf'_le _ (Finset.mem_univ s)))
  let v : N.R → ℝ := fun r => ∫ τ in (0 : ℝ)..t, N.massActionRate κ r (γ τ)
  have hvnn : N.IsNonnegativeFlux v := fun r =>
    N.integratedReactionRate_nonneg κ ht (fun τ hτ => (hpos τ hτ.1).nonnegative) r
  have hdisp := N.displacement_eq_integratedReactionFlux κ ht (fun τ hτ => hsol τ hτ.1)
    (fun τ hτ => (hpos τ hτ.1).nonnegative)
  have hvneg : ∀ s ∈ P, N.fluxNetChange v s < 0 := by
    intro s hs
    have hcoord := congrFun hdisp s
    have heq : N.fluxNetChange v s = γ t s - γ 0 s := by
      dsimp [v, fluxNetChange]
      simpa [Finset.sum_apply, Pi.sub_apply, smul_eq_mul] using hcoord.symm
    rw [heq]; linarith [hlt s hs]
  exact ⟨hPne, hPsiph, N.isDrainable_of_flux P ⟨v, hvnn, hvneg⟩⟩

/-- **Deshpande–Gopalkrishnan 2014, Theorem 6.2.** If the network has no drainable siphon, then for
every positive rate vector every point of the closure of every positive forward mass-action orbit
is positive.  No boundedness is assumed. -/
theorem orbitClosure_positive_of_hasNoDrainableSiphon (N : Network S) (hnd : N.HasNoDrainableSiphon)
    (κ : N.RateConstants) {γ : ℝ → Concentration S} (hγ0 : (γ 0).Positive)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    {w : Concentration S} (hw : ∀ ε > 0, ∃ t, 0 ≤ t ∧ dist (γ t) w < ε) : w.Positive := by
  have hwnn := N.orbitClosure_nonnegative κ hγ0 hsol hw
  by_contra hnp
  simp only [Concentration.Positive, not_forall, not_lt] at hnp
  obtain ⟨s₀, hs₀⟩ := hnp
  set P : Finset S := Finset.univ.filter (fun s => w s = 0)
  have hP : ∀ s, s ∈ P ↔ w s = 0 := fun s => by simp [P]
  exact hnd P (N.isDrainableSiphon_zeroSet_of_orbitClosure κ hγ0 hsol hw hP
    ⟨s₀, (hP s₀).2 (le_antisymm hs₀ (hwnn s₀))⟩)

/-- The ω-limit form, for every genuine mass-action flow and without the bounded-orbit hypothesis
of `BoundaryOmegaExcludedForFlow`. -/
theorem omegaLimit_positive_of_hasNoDrainableSiphon (N : Network S) (hnd : N.HasNoDrainableSiphon)
    (κ : N.RateConstants) {ϕ : Flow NNReal (Concentration S)}
    {γ : Concentration S → ℝ → Concentration S} (hflow : N.IsMassActionFlow κ ϕ γ)
    {x₀ : Concentration S} (hx₀ : x₀.Positive) :
    ∀ w ∈ omegaLimit atTop ϕ {x₀}, w.Positive := by
  obtain ⟨hγ0, hϕγ, hγd⟩ := id hflow
  intro w hw
  have hcl : w ∈ closure (Set.image2 ϕ Set.univ {x₀}) :=
    omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀}) (u := Set.univ)
      univ_mem hw
  refine N.orbitClosure_positive_of_hasNoDrainableSiphon hnd κ (γ := γ x₀)
    (by rw [hγ0 x₀]; exact hx₀) (hγd x₀) (fun ε hε => ?_)
  obtain ⟨y, hy, hdy⟩ := Metric.mem_closure_iff.mp hcl ε hε
  obtain ⟨t, _, x, hx, rfl⟩ := hy
  simp only [Set.mem_singleton_iff] at hx
  subst hx
  refine ⟨t, t.coe_nonneg, ?_⟩
  rw [← hϕγ, dist_comm]; exact hdy

/-- **Non-autocatalytic weakly reversible networks are persistent** (Deshpande–Gopalkrishnan
2014): with no self-replicable siphon, every closure point of every positive forward orbit is
positive.  No boundedness is assumed. -/
theorem orbitClosure_positive_of_weaklyReversible_hasNoSelfReplicableSiphon (N : Network S)
    (hwr : N.WeaklyReversible) (hnosr : N.HasNoSelfReplicableSiphon) (κ : N.RateConstants)
    {γ : ℝ → Concentration S} (hγ0 : (γ 0).Positive)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    {w : Concentration S} (hw : ∀ ε > 0, ∃ t, 0 ≤ t ∧ dist (γ t) w < ε) : w.Positive :=
  N.orbitClosure_positive_of_hasNoDrainableSiphon
    (N.hasNoDrainableSiphon_of_weaklyReversible_hasNoSelfReplicableSiphon' hwr hnosr) κ hγ0 hsol hw

end Network

end CRNT
