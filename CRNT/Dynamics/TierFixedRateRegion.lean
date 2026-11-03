import CRNT.Dynamics.TierExtractionCompleted
import CRNT.Dynamics.TierDissipationAsymptotics
import CRNT.Dynamics.StrongEndotacticTier
import CRNT.Dynamics.GenuineConfinement
import CRNT.Theorems.DeficiencyZero.Confinement
import CRNT.Dynamics.OrbitRegularity

/-!
# Fixed-rate compact negativity region for strongly endotactic networks

`exists_logBox_negative_outside_fixed`: for a tier-descending (equivalently, strongly endotactic)
network, fixed positive rate constants, and a positive compatibility class, there is a log box
outside of which the tier dissipation is strictly negative on the class.  This is the fixed-rate
form of Corollary 5.1 of the tier literature, obtained from the proved fixed-rate negativity
`TierDescending.tierDissipationEventuallyNegative` and the proved extraction
`everyEscapingClassSequenceHasTransversalTierSubsequence`; it does not need the variable-rate
statement `UniformTierDissipationEventuallyNegative`.

Nothing here is an axiom or a `sorry`.
-/

open Filter

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Fixed-rate compact negativity region.** -/
theorem exists_logBox_negative_outside_fixed {N : Network S} (htd : N.TierDescending)
    (κ : N.RateConstants) (xref : Concentration S) :
    ∃ R : ℕ, ∀ x : Concentration S, x ∈ N.positiveCompatibilityClass xref →
      x ∉ logBox (S := S) (R : ℝ) → N.tierDissipation κ x < 0 := by
  classical
  by_contra hnot
  push_neg at hnot
  choose xs hxs hout hnonneg using hnot
  have hpos : PositiveSequence xs := fun n => (hxs n).2
  have hesc : LogEscapes xs := logEscapes_of_eventually_not_mem_logBox (S := S) hpos hout
  obtain ⟨φ, -, htrans⟩ := N.everyEscapingClassSequenceHasTransversalTierSubsequence xref xs hxs hesc
  obtain ⟨n₀, hn₀⟩ := htd.tierDissipationEventuallyNegative κ (xs ∘ φ) htrans
  exact (not_lt_of_ge (hnonneg (φ n₀))) (hn₀ n₀ le_rfl)

/-- The same region for strongly endotactic networks. -/
theorem StronglyEndotacticStd.exists_logBox_negative_outside {N : Network S}
    (hse : N.StronglyEndotacticStd) (κ : N.RateConstants) (xref : Concentration S) :
    ∃ R : ℕ, ∀ x : Concentration S, x ∈ N.positiveCompatibilityClass xref →
      x ∉ logBox (S := S) (R : ℝ) → N.tierDissipation κ x < 0 :=
  exists_logBox_negative_outside_fixed ((N.stronglyEndotacticStd_iff_tierDescending).mp hse) κ xref

/-- **Bounded forward trajectories.** For a tier-descending network and any positive rate
constants, every forward mass-action solution from a positive state is bounded.  The tier entropy
stays below `max (sup over the compact region) (V(x₀)) + 1`: at that level the state lies outside
the region, where the entropy strictly decreases. -/
theorem TierDescending.forward_bounded_uniform {N : Network S} (htd : N.TierDescending)
    (κ : N.RateConstants) {x₀ : Concentration S} (hx₀ : x₀.Positive) :
    ∃ M : ℝ, ∀ γ : ℝ → Concentration S, γ 0 = x₀ →
      (∀ t : ℝ, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t) →
      ∀ t : ℝ, 0 ≤ t → ∀ s, γ t s ≤ M := by
  classical
  obtain ⟨R, hR⟩ := exists_logBox_negative_outside_fixed htd κ x₀
  set K : Set (Concentration S) := N.compatibilityClass x₀ ∩ logBox (S := S) (R : ℝ)
  have hKc : IsCompact K :=
    (isCompact_logBox (S := S) (R : ℝ)).inter_left (N.isClosed_compatibilityClass x₀)
  have href : Concentration.Positive (tierReference S : Concentration S) := fun _ => zero_lt_one
  have hVc : Continuous (fun x : Concentration S => tierEntropy x) := by
    unfold tierEntropy; exact continuous_const.add (relEntropy_continuous href)
  obtain ⟨c, hc⟩ := (hKc.bddAbove_image hVc.continuousOn)
  set c' : ℝ := max c (tierEntropy x₀) + 1 with hc'
  refine ⟨max (Real.exp 2 * 1) (c' - 1), fun γ hγx hsol => ?_⟩
  have hγ0 : (γ 0).Positive := hγx ▸ hx₀
  have hpos := N.genuineOrbit_pos κ hγ0 hsol
  have hcomp : ∀ t, 0 ≤ t → N.StoichCompatible x₀ (γ t) := fun t ht =>
    hγx ▸ N.stoichCompatible_of_forward_solution κ hsol t ht
  -- comparison with the constant level `c'`
  have hV : ∀ t, 0 ≤ t → tierEntropy (γ t) ≤ c' := by
    intro t ht
    have hd : ∀ τ, 0 ≤ τ → HasDerivAt (fun τ => tierEntropy (γ τ))
        (N.tierDissipation κ (γ τ)) τ := fun τ hτ =>
      N.tierEntropy_hasDerivAt κ (hpos τ hτ) fun s => (hasDerivAt_pi.mp (hsol τ hτ)) s
    refine image_le_of_deriv_right_lt_deriv_boundary' (f := fun τ => tierEntropy (γ τ))
      (f' := fun τ => N.tierDissipation κ (γ τ)) (a := 0) (b := t)
      (fun τ hτ => (hd τ hτ.1).continuousAt.continuousWithinAt)
      (fun τ hτ => (hd τ hτ.1).hasDerivWithinAt)
      (B := fun _ => c') (B' := fun _ => 0)
      (by simp only [hc', hγx]; linarith [le_max_right c (tierEntropy x₀)])
      continuousOn_const (fun _ _ => hasDerivWithinAt_const _ _ _)
      (fun τ hτ heq => ?_) (Set.right_mem_Icc.2 ht)
    have hnotK : γ τ ∉ K := by
      intro hK
      have h0 : tierEntropy (γ τ) ≤ c := hc ⟨γ τ, hK, rfl⟩
      have := heq ▸ h0
      simp only [hc'] at this
      linarith [le_max_left c (tierEntropy x₀)]
    have hnotbox : γ τ ∉ logBox (S := S) (R : ℝ) := fun hb => hnotK ⟨hcomp τ hτ.1, hb⟩
    exact hR (γ τ) ⟨hcomp τ hτ.1, hpos τ hτ.1⟩ hnotbox
  intro t ht s
  have h1 : relEntropy (tierReference S) (γ t) ≤ c' - 1 := by
    have := hV t ht; unfold tierEntropy at this; linarith
  exact relEntropy_coord_le href (hpos t ht).nonnegative h1 s

theorem TierDescending.forward_bounded {N : Network S} (htd : N.TierDescending)
    (κ : N.RateConstants) {γ : ℝ → Concentration S} (hγ0 : (γ 0).Positive)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t) :
    ∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ s, γ t s ≤ M := by
  obtain ⟨M, hM⟩ := htd.forward_bounded_uniform κ hγ0
  exact ⟨M, hM γ rfl hsol⟩

/-- **Strongly endotactic networks have bounded forward trajectories** (the boundedness half of
Gopalkrishnan–Miller–Shiu 2014). -/
theorem StronglyEndotacticStd.forward_bounded {N : Network S} (hse : N.StronglyEndotacticStd)
    (κ : N.RateConstants) {γ : ℝ → Concentration S} (hγ0 : (γ 0).Positive)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t) :
    ∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ s, γ t s ≤ M :=
  ((N.stronglyEndotacticStd_iff_tierDescending).mp hse).forward_bounded κ hγ0 hsol

end Network
end CRNT
