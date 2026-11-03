import CRNT.Dynamics.TierLyapunov
import CRNT.Kinetics.VariableMassAction

/-!
# Tier Lyapunov identity for variable-k systems

The tier entropy calculation is pointwise in the reaction coefficients, so it extends verbatim to
positive time-dependent coefficients.  This module records that extension and the uniform
sequence-level negativity statement used by the compactness argument.
-/

open Filter
open scoped BigOperators Topology

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Tier dissipation with time-dependent positive reaction coefficients. -/
noncomputable def variableTierDissipation (N : Network S) (κ : N.VariableRateConstants)
    (t : ℝ) (x : Concentration S) : ℝ :=
  ∑ r : N.R, κ.k t r * tierMonomial x (N.reaction r).source *
    Real.log (tierMonomial x (N.reaction r).target /
      tierMonomial x (N.reaction r).source)

@[simp] theorem variableTierDissipation_const (N : Network S) (κ : N.RateConstants)
    (t : ℝ) (x : Concentration S) :
    N.variableTierDissipation κ.toVariable t x = N.tierDissipation κ x := rfl

/-- The log-gradient pairing with the variable-k vector field is exactly variable tier
dissipation. -/
theorem log_pair_variableMassActionVectorField_eq_variableTierDissipation
    (N : Network S) (κ : N.VariableRateConstants) (t : ℝ)
    {x : Concentration S} (hx : x.Positive) :
    (∑ s : S, Real.log (x s) * N.variableMassActionVectorField κ t x s) =
      N.variableTierDissipation κ t x := by
  rw [variableTierDissipation]
  simp only [variableMassActionVectorField_apply, variableMassActionRate]
  -- `Finset.sum_comm` needs a literal double sum; distribute the product first.
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  calc
    (∑ s : S, Real.log (x s) *
        (κ.k t r * (N.reaction r).source.massActionMonomial x * N.reactionVector r s))
        = κ.k t r * tierMonomial x (N.reaction r).source *
            (∑ s : S, Real.log (x s) * N.reactionVector r s) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro s _
              rw [tierMonomial_eq_massActionMonomial]
              ring
    _ = κ.k t r * tierMonomial x (N.reaction r).source *
          Real.log (tierMonomial x (N.reaction r).target /
            tierMonomial x (N.reaction r).source) := by
              rw [N.log_pair_reactionVector hx r]

/-- Tier entropy derivative identity for a variable-k solution. -/
theorem tierEntropy_hasDerivAt_variable (N : Network S) (κ : N.VariableRateConstants)
    {γ : ℝ → Concentration S} {t : ℝ} (hpos : Concentration.Positive (γ t))
    (hsol : ∀ s, HasDerivAt (fun τ => γ τ s)
      (N.variableMassActionVectorField κ t (γ t) s) t) :
    HasDerivAt (fun τ => tierEntropy (γ τ))
      (N.variableTierDissipation κ t (γ t)) t := by
  have href : Concentration.Positive (tierReference S : Concentration S) := fun _ => zero_lt_one
  have hchain := relEntropy_hasDerivAt href hpos hsol
  have hder :
      (∑ s : S, (Real.log (γ t s) - Real.log ((tierReference S) s)) *
        N.variableMassActionVectorField κ t (γ t) s) =
        N.variableTierDissipation κ t (γ t) := by
    simp only [tierReference, Real.log_one, sub_zero]
    exact N.log_pair_variableMassActionVectorField_eq_variableTierDissipation κ t hpos
  have hrel : HasDerivAt (fun τ => relEntropy (tierReference S) (γ τ))
      (N.variableTierDissipation κ t (γ t)) t := by
    simpa only [← reactionVector_apply, ← variableMassActionVectorField_apply, hder]
      using hchain
  simpa [tierEntropy] using hrel.const_add 1

/-- A sequence of positive reaction coefficient vectors uniformly bounded away from zero and
infinity.  This is the sequence form of the `δ ≤ κ_r(t) ≤ δ⁻¹` hypothesis. -/
def UniformPositiveRateSequence (N : Network S) (ks : ℕ → N.R → ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ n r, δ ≤ ks n r ∧ ks n r ≤ δ⁻¹

/-- Tier dissipation evaluated using an arbitrary coefficient vector rather than a bundled
`RateConstants`; useful for subsequence compactness. -/
noncomputable def tierDissipationWith (N : Network S) (k : N.R → ℝ)
    (x : Concentration S) : ℝ :=
  ∑ r : N.R, k r * tierMonomial x (N.reaction r).source *
    Real.log (tierMonomial x (N.reaction r).target /
      tierMonomial x (N.reaction r).source)

@[simp] theorem tierDissipationWith_rateConstants (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) : N.tierDissipationWith κ.k x = N.tierDissipation κ x := rfl

/-- Uniform Proposition-4.6-shaped statement.  Unlike the fixed-rate version, the coefficient
vector may vary with `n` but must stay in one compact positive interval. -/
def UniformTierDissipationEventuallyNegative (N : Network S) : Prop :=
  ∀ (ks : ℕ → N.R → ℝ), N.UniformPositiveRateSequence ks →
    ∀ xs : ℕ → Concentration S, N.IsTransversalTierSequence xs →
      ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → N.tierDissipationWith (ks n) (xs n) < 0

/-- Uniform tier negativity specializes immediately to ordinary fixed-rate Proposition 4.6. -/
theorem UniformTierDissipationEventuallyNegative.toFixed {N : Network S}
    (h : N.UniformTierDissipationEventuallyNegative) :
    N.TierDissipationEventuallyNegative := by
  intro κ xs hxs
  let ks : ℕ → N.R → ℝ := fun _ r => κ.k r
  have hfinite : ∃ δ : ℝ, 0 < δ ∧ ∀ r : N.R, δ ≤ κ.k r ∧ κ.k r ≤ δ⁻¹ := by
    classical
    by_cases hR : Nonempty N.R
    · let kmin : ℝ := Finset.univ.inf' (Finset.univ_nonempty) (fun r : N.R => κ.k r)
      let kmax : ℝ := Finset.univ.sup' (Finset.univ_nonempty) (fun r : N.R => κ.k r)
      have hkmin : 0 < kmin := by
        -- the infimum over a nonempty finite set is attained, so positivity transfers
        obtain ⟨r, -, hr⟩ :=
          Finset.exists_mem_eq_inf' (Finset.univ_nonempty) (fun r : N.R => κ.k r)
        dsimp only [kmin]
        rw [hr]
        exact κ.positive r
      let δ : ℝ := min kmin (min 1 kmax⁻¹)
      have hkmaxpos : 0 < kmax :=
        (κ.positive (Classical.choice hR)).trans_le
          (Finset.le_sup' (fun r : N.R => κ.k r) (Finset.mem_univ (Classical.choice hR)))
      have hδ : 0 < δ := by
        dsimp [δ]
        exact lt_min hkmin (lt_min zero_lt_one (inv_pos.mpr hkmaxpos))
      refine ⟨δ, hδ, ?_⟩
      intro r
      have hmin : kmin ≤ κ.k r := Finset.inf'_le _ (Finset.mem_univ r)
      have hmax : κ.k r ≤ kmax := Finset.le_sup' _ (Finset.mem_univ r)
      have hδmin : δ ≤ kmin := min_le_left _ _
      have hδinvmax : δ ≤ kmax⁻¹ := (min_le_right kmin _).trans (min_le_right 1 kmax⁻¹)
      refine ⟨hδmin.trans hmin, ?_⟩
      have hinv : kmax ≤ δ⁻¹ := by
        exact (le_inv_comm₀ hkmaxpos hδ).2 hδinvmax
      exact hmax.trans hinv
    · haveI : IsEmpty N.R := not_nonempty_iff.mp hR
      refine ⟨1, zero_lt_one, ?_⟩
      intro r
      exact isEmptyElim r
  obtain ⟨δ, hδ, hk⟩ := hfinite
  have hks : N.UniformPositiveRateSequence ks := ⟨δ, hδ, fun _ r => hk r⟩
  obtain ⟨n₀, hn₀⟩ := h ks hks xs hxs
  refine ⟨n₀, ?_⟩
  intro n hn
  simpa [ks] using hn₀ n hn

end Network
end CRNT
