import CRNT.Dynamics.GlobalPersistence
import CRNT.Dynamics.BoundaryOmegaSiphon
import CRNT.Dynamics.ReactionConeDisplacement
import CRNT.Decision.StrictConeRealization

/-!
# No drainable siphons imply global omega-persistence

This file formalizes the direct dynamical argument behind the drainable-siphon persistence
criterion.  It deliberately avoids the stronger minimal-critical-siphon dichotomy.

Let `w` be a boundary omega-limit point of a positive bounded mass-action orbit and let `P` be its
zero set.  The existing boundary-omega theorem shows that `P` is a siphon.  Because `w_s = 0 <
x₀_s` on `P`, the open set

`{x | ∀ s ∈ P, x s < x₀ s}`

is a neighborhood of `w`.  Omega-limit membership puts `w` in the closure of the forward orbit,
so some finite-time orbit point lies in this neighborhood.  The displacement to that point is the
nonnegative integrated-reaction-rate combination from `ReactionConeDisplacement`; it is strictly
negative on every species of `P`.  Thus `P` is flux-drainable, hence drainable by the finite
strict-cone realization theorem, contradicting `HasNoDrainableSiphon`.

The conclusion is the clean bounded-orbit omega formulation `StructurallyBoundaryOmegaExcludedStd`.
No weak reversibility, deficiency, complex balance, or minimal-critical-siphon assumption is used.
-/

open Filter Topology
open scoped BigOperators NNReal

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Omega-limit points of a positive genuine mass-action orbit are nonnegative. -/
theorem omegaLimit_nonnegative_of_genuine_positiveOrbit (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    (hflow : N.IsMassActionFlow κ ϕ γ) {x₀ : Concentration S} (hx₀ : x₀.Positive) :
    ∀ w ∈ omegaLimit atTop ϕ {x₀}, w.Nonnegative := by
  obtain ⟨hγ0, hϕγ, hγd⟩ := id hflow
  have hpos : ∀ t : ℝ, 0 ≤ t → (γ x₀ t).Positive :=
    N.genuineOrbit_pos κ (by simpa [hγ0 x₀] using hx₀) (hγd x₀)
  have hnnClosed : IsClosed {x : Concentration S | x.Nonnegative} := by
    have heq : {x : Concentration S | x.Nonnegative} = ⋂ s, {x | 0 ≤ x s} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      rfl
    rw [heq]
    exact isClosed_iInter fun s => isClosed_le continuous_const (continuous_apply s)
  have horbit : Set.image2 ϕ Set.univ {x₀} ⊆ {x : Concentration S | x.Nonnegative} := by
    rintro y ⟨t, _ht, x, hx, rfl⟩
    simp only [Set.mem_singleton_iff] at hx
    subst x
    rw [hϕγ]
    exact (hpos (t : ℝ) t.coe_nonneg).nonnegative
  have hclosure : closure (Set.image2 ϕ Set.univ {x₀}) ⊆
      {x : Concentration S | x.Nonnegative} :=
    closure_minimal horbit hnnClosed
  intro w hw
  exact hclosure (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀})
    (u := Set.univ) univ_mem hw)

/-- A boundary omega-limit zero set is drainable: some finite forward displacement of the same
orbit is strictly negative on every species that vanishes at the omega point. -/
theorem isDrainable_zeroSet_of_boundary_omegaLimit (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    (hflow : N.IsMassActionFlow κ ϕ γ) {x₀ : Concentration S} (hx₀ : x₀.Positive)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    {w : Concentration S} (hw : w ∈ omegaLimit atTop ϕ {x₀})
    {P : Finset S} (hP : ∀ s, s ∈ P ↔ w s = 0) (hPne : P.Nonempty) :
    N.IsDrainableSiphon P := by
  obtain ⟨hγ0, hϕγ, hγd⟩ := id hflow
  have hpos : ∀ t : ℝ, 0 ≤ t → (γ x₀ t).Positive :=
    N.genuineOrbit_pos κ (by simpa [hγ0 x₀] using hx₀) (hγd x₀)
  have hωnn := N.omegaLimit_nonnegative_of_genuine_positiveOrbit κ hflow hx₀
  have hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t := by
    intro y _hy t ht
    exact hγd y t ht
  have hPsiph : N.IsSiphon P :=
    N.isSiphon_zeroSet_of_mem_omegaLimit κ hϕγ hK hmaps hωnn hgenω hw hP

  let U : Set (Concentration S) := ⋂ s ∈ P, {x | x s < x₀ s}
  have hUopen : IsOpen U := by
    dsimp [U]
    exact isOpen_biInter_finset fun s _ => isOpen_lt (continuous_apply s) continuous_const
  have hwU : w ∈ U := by
    dsimp [U]
    rw [Set.mem_iInter₂]
    intro s hs
    -- the membership is in a set-builder, so expose the underlying inequality first
    simp only [Set.mem_setOf_eq]
    rw [(hP s).mp hs]
    exact hx₀ s
  have hwclosure : w ∈ closure (Set.image2 ϕ Set.univ {x₀}) :=
    omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀})
      (u := Set.univ) univ_mem hw
  obtain ⟨y, hyU, hyorb⟩ := (mem_closure_iff.mp hwclosure) U hUopen hwU
  obtain ⟨t, _ht, x, hx, hxy⟩ := hyorb
  simp only [Set.mem_singleton_iff] at hx
  subst x
  subst y
  have hγtU : γ x₀ (t : ℝ) ∈ U := by simpa [hϕγ x₀ t] using hyU

  let v : N.R → ℝ := fun r => ∫ τ in (0 : ℝ)..(t : ℝ), N.massActionRate κ r (γ x₀ τ)
  have hvnn : N.IsNonnegativeFlux v := by
    intro r
    exact N.integratedReactionRate_nonneg κ t.coe_nonneg
      (fun τ hτ => (hpos τ hτ.1).nonnegative) r
  have hdisp := N.displacement_eq_integratedReactionFlux κ t.coe_nonneg
    (fun τ hτ => hγd x₀ τ hτ.1)
    (fun τ hτ => (hpos τ hτ.1).nonnegative)
  have hvneg : ∀ s ∈ P, N.fluxNetChange v s < 0 := by
    intro s hs
    have hcoord := congrFun hdisp s
    have heq : N.fluxNetChange v s = γ x₀ (t : ℝ) s - x₀ s := by
      dsimp [v, fluxNetChange]
      simpa [Finset.sum_apply, Pi.sub_apply, smul_eq_mul, hγ0 x₀] using hcoord.symm
    rw [heq]
    have hlt : γ x₀ (t : ℝ) s < x₀ s := by
      exact (Set.mem_iInter₂.mp hγtU s hs)
    linarith
  have hflux : N.IsFluxDrainable P := ⟨v, hvnn, hvneg⟩
  exact ⟨hPne, hPsiph, N.isDrainable_of_flux P hflux⟩

/-- **No drainable siphons imply omega-boundary exclusion for every bounded positive mass-action
orbit.**  This is the direct global persistence theorem; unlike the older critical-siphon route it
requires no minimal-siphon dichotomy and no weak reversibility. -/
theorem boundaryOmegaExcludedForFlow_of_hasNoDrainableSiphon (N : Network S)
    (hnd : N.HasNoDrainableSiphon) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S} :
    N.BoundaryOmegaExcludedForFlow κ ϕ γ := by
  intro hflow x₀ hx₀ hbounded w hw
  obtain ⟨K, hK, hmaps⟩ := hbounded
  have hwnn : w.Nonnegative := N.omegaLimit_nonnegative_of_genuine_positiveOrbit κ hflow hx₀ w hw
  by_contra hnpos
  simp only [Concentration.Positive, not_forall, not_lt] at hnpos
  obtain ⟨s₀, hs₀⟩ := hnpos
  have hs₀zero : w s₀ = 0 := le_antisymm hs₀ (hwnn s₀)
  let P : Finset S := Finset.univ.filter (fun s => w s = 0)
  have hP : ∀ s, s ∈ P ↔ w s = 0 := by
    intro s
    simp [P]
  have hPne : P.Nonempty := ⟨s₀, (hP s₀).2 hs₀zero⟩
  have hdr : N.IsDrainableSiphon P :=
    N.isDrainable_zeroSet_of_boundary_omegaLimit κ hflow hx₀ hK hmaps hw hP hPne
  exact hnd P hdr

/-- **Structural no-drainable-siphon persistence theorem.** -/
theorem structurallyBoundaryOmegaExcludedStd_of_hasNoDrainableSiphon (N : Network S)
    (hnd : N.HasNoDrainableSiphon) : N.StructurallyBoundaryOmegaExcludedStd := by
  intro κ ϕ γ
  exact N.boundaryOmegaExcludedForFlow_of_hasNoDrainableSiphon hnd κ

/-- **Non-autocatalytic weakly reversible networks are omega-persistent.**  Weak reversibility
turns absence of self-replicable siphons into absence of drainable siphons; the direct theorem
above then excludes every boundary omega-limit point of every bounded positive genuine orbit. -/
theorem structurallyBoundaryOmegaExcludedStd_of_weaklyReversible_hasNoSelfReplicableSiphon
    (N : Network S) (hwr : N.WeaklyReversible) (hnosr : N.HasNoSelfReplicableSiphon) :
    N.StructurallyBoundaryOmegaExcludedStd :=
  N.structurallyBoundaryOmegaExcludedStd_of_hasNoDrainableSiphon
    (N.hasNoDrainableSiphon_of_weaklyReversible_hasNoSelfReplicableSiphon' hwr hnosr)

end Network
end CRNT
