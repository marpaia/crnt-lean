import CRNT.Dynamics.TierDissipationAsymptotics
import CRNT.Dynamics.TierExtractionCompleted
import CRNT.Dynamics.VariableTierLyapunov
import CRNT.Dynamics.StrongEndotacticTier

/-!
# Uniform tier negativity (variable rate constants)

`UniformTierDissipationEventuallyNegative` (the variable-rate form of Proposition 4.6 of
Anderson–Cappelletti–Kim–Nguyen, used for Corollary 5.1 with rates in a band `[δ, δ⁻¹]`) was a
named input of the tier route. It follows from the fixed-rate statement by **domination**: along
a subsequence on which every reaction term `x^{y_r} log(x^{y'_r}/x^{y_r})` has a constant sign,
the dissipation with rates `k_n` in the band is at most the dissipation with the fixed rates
`δ⁻¹` (on nonnegative terms) and `δ` (on negative terms), which is eventually negative.

* `TierDescending.uniformTierDissipationEventuallyNegative`.
* `TierDescending.exists_compact_class_region_negative_outside_uniform`: Corollary 5.1 with
  variable rates — a compact region in each positive class outside which the dissipation is
  negative for every rate vector in the band.
-/

open Filter
open scoped BigOperators Topology

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

theorem IsTransversalTierSequence.comp_strictMono' {N : Network S} {xs : ℕ → Concentration S}
    (htrans : N.IsTransversalTierSequence xs) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    N.IsTransversalTierSequence (xs ∘ φ) := by
  have hφtop := hφ.tendsto_atTop
  have hstrict {y y' : Complex S} (h : TierStrictBelow xs y y') :
      TierStrictBelow (xs ∘ φ) y y' := by
    change Tendsto (fun n => tierMonomial (xs (φ n)) y /
      tierMonomial (xs (φ n)) y') atTop (𝓝 0)
    exact h.comp hφtop
  have hLE {y y' : Complex S} (h : TierLE xs y y') : TierLE (xs ∘ φ) y y' := by
    rcases h with h | h
    · exact Or.inl (hstrict h)
    · obtain ⟨c, hc, hlim⟩ := h
      exact Or.inr ⟨c, hc, hlim.comp hφtop⟩
  have hcmp : N.TierComparable (xs ∘ φ) := by
    intro y hy y' hy'
    rcases htrans.1.2.2 y hy y' hy' with h | h
    · exact Or.inl (hLE h)
    · exact Or.inr (hstrict h)
  have hcross : ∃ r : N.R,
      TierStrictBelow (xs ∘ φ) (N.reaction r).source (N.reaction r).target ∨
      TierStrictBelow (xs ∘ φ) (N.reaction r).target (N.reaction r).source := by
    obtain ⟨r, hcross⟩ := htrans.2
    refine ⟨r, ?_⟩
    rcases hcross with h | h
    · exact Or.inl (hstrict h)
    · exact Or.inr (hstrict h)
  exact ⟨⟨htrans.1.1.comp φ, htrans.1.2.1.comp_strictMono hφ, hcmp⟩, hcross⟩

/-- The reaction term of the tier dissipation. -/
noncomputable def tierTerm (N : Network S) (r : N.R) (x : Concentration S) : ℝ :=
  tierMonomial x (N.reaction r).source *
    Real.log (tierMonomial x (N.reaction r).target / tierMonomial x (N.reaction r).source)

theorem tierDissipationWith_eq (N : Network S) (k : N.R → ℝ) (x : Concentration S) :
    N.tierDissipationWith k x = ∑ r, k r * N.tierTerm r x := by
  unfold tierDissipationWith tierTerm
  exact Finset.sum_congr rfl fun r _ => by ring

/-- **Uniform Proposition 4.6.** For a tier-descending network, along every transversal tier
sequence the dissipation is eventually negative, uniformly over rate vectors in a band. -/
theorem TierDescending.uniformTierDissipationEventuallyNegative {N : Network S}
    (htd : N.TierDescending) : N.UniformTierDissipationEventuallyNegative := by
  classical
  intro ks ⟨δ, hδ, hks⟩ xs htrans
  by_contra hnot
  push Not at hnot
  -- infinitely many indices with nonnegative dissipation
  have hfreq : ∃ᶠ n in atTop, 0 ≤ N.tierDissipationWith (ks n) (xs n) := by
    rw [Filter.frequently_atTop]
    intro n₀
    obtain ⟨n, hn, h⟩ := hnot n₀
    exact ⟨n, hn, h⟩
  obtain ⟨φ₀, hφ₀, hbad⟩ := Filter.extraction_of_frequently_atTop hfreq
  -- a sign pattern repeating infinitely often
  let pat : ℕ → N.R → Bool := fun m r => decide (0 ≤ N.tierTerm r (xs (φ₀ m)))
  obtain ⟨P, hP⟩ := Finite.exists_infinite_fiber pat
  have hfreqP : ∃ᶠ m in atTop, pat m = P := by
    rw [Nat.frequently_atTop_iff_infinite]
    exact Set.infinite_coe_iff.mp hP
  obtain ⟨φ₁, hφ₁, hpat⟩ := Filter.extraction_of_frequently_atTop hfreqP
  set φ := φ₀ ∘ φ₁ with hφ
  have hφmono : StrictMono φ := hφ₀.comp hφ₁
  -- the dominating fixed rates
  let κP : RateConstants N := ⟨fun r => if P r then δ⁻¹ else δ, fun r => by
    split_ifs
    · exact inv_pos.mpr hδ
    · exact hδ⟩
  have hdom : ∀ m, N.tierDissipationWith (ks (φ m)) (xs (φ m)) ≤
      N.tierDissipation κP (xs (φ m)) := by
    intro m
    rw [← tierDissipationWith_rateConstants, tierDissipationWith_eq, tierDissipationWith_eq]
    refine Finset.sum_le_sum fun r _ => ?_
    have hpr : pat (φ₁ m) r = P r := congrFun (hpat m) r
    simp only [pat, decide_eq_decide] at hpr
    obtain ⟨h1, h2⟩ := hks (φ m) r
    change ks (φ m) r * N.tierTerm r (xs (φ m)) ≤
      (if P r then δ⁻¹ else δ) * N.tierTerm r (xs (φ m))
    by_cases hPr : P r = true
    · have hnn : 0 ≤ N.tierTerm r (xs (φ m)) := by
        have := hpr; rw [hPr] at this; simp only [decide_eq_true_eq] at this; exact this
      simp only [hPr, ↓reduceIte]
      exact mul_le_mul_of_nonneg_right h2 hnn
    · have hneg : N.tierTerm r (xs (φ m)) < 0 := by
        have := hpr
        rw [Bool.not_eq_true] at hPr
        rw [hPr] at this
        simp only [decide_eq_false_iff_not, not_le] at this
        exact this
      simp only [hPr, Bool.false_eq_true, ↓reduceIte]
      exact mul_le_mul_of_nonpos_right h1 hneg.le
  obtain ⟨n₀, hn₀⟩ := htd.tierDissipationEventuallyNegative κP (xs ∘ φ)
    (htrans.comp_strictMono' hφmono)
  have h1 : N.tierDissipation κP (xs (φ n₀)) < 0 := hn₀ n₀ le_rfl
  have h2 := hdom n₀
  have h3 : 0 ≤ N.tierDissipationWith (ks (φ n₀)) (xs (φ n₀)) := hbad (φ₁ n₀)
  linarith

/-- **Corollary 5.1 with variable rates.** For a tier-descending network and a rate band
`[δ, δ⁻¹]`, each positive class contains a compact set outside of which the dissipation is
negative for every rate vector in the band. -/
theorem TierDescending.exists_compact_class_region_negative_outside_uniform {N : Network S}
    (htd : N.TierDescending) (xref : Concentration S) (δ : ℝ) :
    ∃ K : Set (Concentration S), IsCompact K ∧ K ⊆ N.positiveCompatibilityClass xref ∧
      ∀ (k : N.R → ℝ) (x : Concentration S), N.RateVectorInBand δ k →
        x ∈ N.positiveCompatibilityClass xref → x ∉ K → N.tierDissipationWith k x < 0 :=
  N.exists_compact_class_region_negative_outside_of_uniformTierNegativity
    htd.uniformTierDissipationEventuallyNegative xref δ

/-- The same for strongly endotactic networks. -/
theorem StronglyEndotacticStd.exists_compact_class_region_negative_outside_uniform
    {N : Network S} (hse : N.StronglyEndotacticStd) (xref : Concentration S) (δ : ℝ) :
    ∃ K : Set (Concentration S), IsCompact K ∧ K ⊆ N.positiveCompatibilityClass xref ∧
      ∀ (k : N.R → ℝ) (x : Concentration S), N.RateVectorInBand δ k →
        x ∈ N.positiveCompatibilityClass xref → x ∉ K → N.tierDissipationWith k x < 0 :=
  ((N.stronglyEndotacticStd_iff_tierDescending).mp hse).exists_compact_class_region_negative_outside_uniform
    xref δ

end Network
end CRNT
