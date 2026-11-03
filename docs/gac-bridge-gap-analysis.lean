import CRNT.Dynamics.OrbitRegularity
import CRNT.Dynamics.HighCodimensionSiphonFace

/-! Gap analysis: derive the residual obligation from the blueprint criterion.  All three orbit
bridges are now discharged from the residual's own hypotheses, so this file elaborates with **no
`sorry` and no errors**: the residual follows from the blueprint data alone. -/

open Filter
open scoped NNReal Topology RealInnerProductSpace

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S] [Nonempty S]

theorem gapAnalysis (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hx₀ : x₀.Positive)
    {δ : ℝ} (hδ : 0 < δ) {P : Finset S} {B R R' M : ℝ} (hRR' : R < R')
    {ι' : Type} [Fintype ι'] [Nonempty ι']
    {m : ι' → N.euclideanStoichSubspace} {b : ι' → ℝ}
    (piece : S → ι')
    (hMclass : ∀ x : Concentration S, x.Positive → N.StoichCompatible (γ x₀ 0) x → ∀ u, x u ≤ M)
    (hpos : ∀ s : S, 0 < ((m (piece s) : EuclideanSpace ℝ S) s))
    (hlevel : ∀ s : S,
      M * (∑ u ∈ Finset.univ.erase s, max ((m (piece s) : EuclideanSpace ℝ S) u) 0)
        < -(R + b (piece s)))
    (hm : ∀ i : ι', ∀ C ∈ N.relevantCones (N.activeFaceImage P xstar (γ x₀) m b R R' i) δ B,
      m i ∈ C)
    (hstart : PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
      (N.euclideanStoichState (γ x₀ 0)) ≤ R)
    (hregime : ∀ t, 0 ≤ t →
      R ≤ PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState (γ x₀ t)) →
      PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState (γ x₀ t)) ≤ R' →
      ‖N.offFaceLogPart P xstar (γ x₀ t)‖ ≤ B) :
    ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive := by
  -- the orbit starts at `x₀`
  have hγ0 : γ x₀ 0 = x₀ := by
    have h := hϕγ x₀ 0
    simpa using h.symm
  -- a uniform coordinate ceiling on the compact `K`, hence along the orbit
  have hKne : K.Nonempty := ⟨ϕ 0 x₀, hmaps 0⟩
  obtain ⟨Bx, hBx⟩ : ∃ Bx : ℝ, ∀ y ∈ K, ∀ s, y s ≤ Bx := by
    have hco : ∀ s : S, ∃ c : ℝ, ∀ y ∈ K, y s ≤ c := by
      intro s
      obtain ⟨z, hzK, hz⟩ := hK.exists_isMaxOn hKne (continuous_apply s).continuousOn
      exact ⟨z s, fun y hy => hz hy⟩
    choose c hc using hco
    exact ⟨Finset.univ.sup' Finset.univ_nonempty c, fun y hy s =>
      le_trans (hc s y hy) (Finset.le_sup' c (Finset.mem_univ s))⟩
  have hΓbdd : ∀ t : ℝ, 0 ≤ t → ∀ s, γ x₀ t s ≤ Bx := by
    intro t ht s
    have hmem : γ x₀ t ∈ K := by
      have h := hmaps ⟨t, ht⟩
      rw [hϕγ x₀ ⟨t, ht⟩] at h
      exact (show ((⟨t, ht⟩ : ℝ≥0) : ℝ) = t from rfl) ▸ h
    exact hBx _ hmem s
  -- BRIDGE 1: DISCHARGED -- forward differentiability gives continuity on `Set.Ici 0`, which is
  -- all the trapping theorems now ask for.
  have bridge1_continuity : ContinuousOn (γ x₀) (Set.Ici 0) := fun t ht =>
    ((hsol t ht).continuousAt).continuousWithinAt
  -- BRIDGE 2: DISCHARGED -- `Network.orbit_pos_forward`, with the ceiling from compactness.
  have bridge2_forwardPositivity : ∀ t, 0 ≤ t → (γ x₀ t).Positive :=
    N.orbit_pos_forward κ (by rw [hγ0]; exact hx₀) hΓbdd hsol
  -- BRIDGE 3: DISCHARGED -- `Network.stoichCompatible_of_forward_solution`, from `hsol` alone.
  have bridge3_classInvariance : ∀ t, 0 ≤ t → N.StoichCompatible (γ x₀ 0) (γ x₀ t) :=
    N.stoichCompatible_of_forward_solution κ hsol
  exact N.exists_positive_omegaPoint_of_blueprintData κ hxs hcb hϕγ hK hmaps
    bridge1_continuity bridge2_forwardPositivity hsol bridge3_classInvariance hδ
    hRR' hMclass piece hpos hlevel hm hstart hregime

end Network
end CRNT
