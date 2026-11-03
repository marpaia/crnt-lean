import CRNT.Dynamics.TierOrderAlgebra
import CRNT.Dynamics.TierDirectionProjection
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Multiscale logarithmic decomposition of tier sequences

This is the formal data form of Lemma 4.4 in Anderson--Cappelletti--Kim--Nguyen.  A logarithmically
escaping positive sequence has, after subsequence extraction, finitely many divergent scales
`m₀ ≫ m₁ ≫ ...`, direction vectors `αᵢ`, and a uniformly bounded residual.  Tier comparisons are
lexicographic in the direction vectors: same-tier complex differences annihilate every `αᵢ`, while
a strict tier comparison has a first scale on which its pairing is strictly negative.

Keeping the decomposition as a structure makes the later dominance theorem independent of the
particular compactness construction used to obtain it.
-/

open Filter
open scoped BigOperators Topology

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Pairing of a real species direction with a complex difference. -/
def tierDirectionGap (a : S → ℝ) (y y' : Complex S) : ℝ :=
  complexWValue a y - complexWValue a y'

/-- Finite multiscale decomposition of logarithmic concentrations. -/
structure TierScaleDecomposition (N : Network S) (xs : ℕ → Concentration S) where
  levels : ℕ
  levels_pos : 0 < levels
  levels_le_species : levels ≤ Fintype.card S
  scale : Fin levels → ℕ → ℝ
  direction : Fin levels → S → ℝ
  residual : ℕ → S → ℝ
  scale_pos : ∀ i, ∀ᶠ n in atTop, 0 < scale i n
  scale_escape : ∀ i, Tendsto (scale i) atTop atTop
  scale_separated : ∀ i j, i < j →
    Tendsto (fun n => scale j n / scale i n) atTop (𝓝 0)
  log_eq : ∀ n s,
    Real.log (xs n s) =
      (∑ i : Fin levels, scale i n * direction i s) + residual n s
  residual_bounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ n s, |residual n s| ≤ C
  same_gap_zero : ∀ {y y' : Complex S}, y ∈ N.complexes → y' ∈ N.complexes →
    TierSame xs y y' → ∀ i, tierDirectionGap (direction i) y y' = 0
  strict_first : ∀ {y y' : Complex S}, y ∈ N.complexes → y' ∈ N.complexes →
    TierStrictBelow xs y y' →
      ∃ i : Fin levels,
        (∀ j : Fin levels, j < i → tierDirectionGap (direction j) y y' = 0) ∧
        tierDirectionGap (direction i) y y' < 0

/-- The bounded residual contributes only a uniformly bounded amount to the log ratio of any fixed
pair of complexes. -/
theorem TierScaleDecomposition.residualGap_bounded
    {N : Network S} {xs : ℕ → Concentration S}
    (D : N.TierScaleDecomposition xs) (y y' : Complex S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      |∑ s : S, (((y s : ℝ) - (y' s : ℝ)) * D.residual n s)| ≤ C := by
  obtain ⟨C, hC, hres⟩ := D.residual_bounded
  let M : ℝ := ∑ s : S, |(y s : ℝ) - (y' s : ℝ)|
  refine ⟨M * C, mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) hC, ?_⟩
  intro n
  calc
    |∑ s : S, (((y s : ℝ) - (y' s : ℝ)) * D.residual n s)|
        ≤ ∑ s : S, |((y s : ℝ) - (y' s : ℝ)) * D.residual n s| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s : S, |(y s : ℝ) - (y' s : ℝ)| * |D.residual n s| := by
          apply Finset.sum_congr rfl
          intro s _
          rw [abs_mul]
    _ ≤ ∑ s : S, |(y s : ℝ) - (y' s : ℝ)| * C := by
          exact Finset.sum_le_sum fun s _ =>
            mul_le_mul_of_nonneg_left (hres n s) (abs_nonneg _)
    _ = M * C := by simp [M, Finset.sum_mul]

/-- Exact expansion of a complex log-ratio in the multiscale coordinates. -/
theorem TierScaleDecomposition.logRatio_eq
    {N : Network S} {xs : ℕ → Concentration S}
    (D : N.TierScaleDecomposition xs) (hpos : PositiveSequence xs)
    (n : ℕ) (y y' : Complex S) :
    Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y') =
      (∑ i : Fin D.levels, D.scale i n * tierDirectionGap (D.direction i) y y') +
      ∑ s : S, (((y s : ℝ) - (y' s : ℝ)) * D.residual n s) := by
  rw [Real.log_div]
  · rw [log_tierMonomial (hpos n), log_tierMonomial (hpos n), ← Finset.sum_sub_distrib]
    calc
      (∑ s : S, ((y s : ℝ) * Real.log (xs n s) -
          (y' s : ℝ) * Real.log (xs n s)))
          = ∑ s : S, (((y s : ℝ) - (y' s : ℝ)) * Real.log (xs n s)) := by
              apply Finset.sum_congr rfl
              intro s _
              ring
      _ = ∑ s : S, (((y s : ℝ) - (y' s : ℝ)) *
          ((∑ i : Fin D.levels, D.scale i n * D.direction i s) + D.residual n s)) := by
              apply Finset.sum_congr rfl
              intro s _
              rw [D.log_eq]
      _ = (∑ i : Fin D.levels,
          D.scale i n * tierDirectionGap (D.direction i) y y') +
          ∑ s : S, (((y s : ℝ) - (y' s : ℝ)) * D.residual n s) := by
              simp only [mul_add, Finset.sum_add_distrib]
              -- distribute before swapping: `sum_comm` needs a literal double sum
              simp only [Finset.mul_sum]
              rw [Finset.sum_comm]
              congr 1
              apply Finset.sum_congr rfl
              intro i _
              simp only [tierDirectionGap, complexWValue, dotProduct, exponentVector]
              rw [← Finset.sum_sub_distrib, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro s _
              ring
  · exact (tierMonomial_pos_of_positiveSequence hpos n y).ne'
  · exact (tierMonomial_pos_of_positiveSequence hpos n y').ne'

/-- If all scales before `i` vanish on a complex difference, the expansion starts exactly at `i`.
This is the algebraic form used in the first-separating-scale argument. -/
theorem TierScaleDecomposition.logRatio_eq_from_first
    {N : Network S} {xs : ℕ → Concentration S}
    (D : N.TierScaleDecomposition xs) (hpos : PositiveSequence xs)
    (n : ℕ) (y y' : Complex S) (i : Fin D.levels)
    (hbefore : ∀ j : Fin D.levels, j < i →
      tierDirectionGap (D.direction j) y y' = 0) :
    Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y') =
      (∑ j : Fin D.levels with i ≤ j,
        D.scale j n * tierDirectionGap (D.direction j) y y') +
      ∑ s : S, (((y s : ℝ) - (y' s : ℝ)) * D.residual n s) := by
  rw [D.logRatio_eq hpos n y y']
  apply congrArg (fun z : ℝ => z +
    ∑ s : S, (((y s : ℝ) - (y' s : ℝ)) * D.residual n s))
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin D.levels))
    (fun j => i ≤ j)]
  -- normalise `¬ i ≤ j` to `j < i` first, so `hz` below matches the goal as stated
  simp only [not_le]
  have hz : ∑ j ∈ Finset.univ.filter (fun j => j < i),
      D.scale j n * tierDirectionGap (D.direction j) y y' = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [hbefore j (Finset.mem_filter.mp hj).2]
  rw [hz, add_zero]

/-- Same-tier pairs have no contribution from any divergent scale, so their log-ratio is entirely
carried by the bounded residual. -/
theorem TierScaleDecomposition.logRatio_eq_residual_of_same
    {N : Network S} {xs : ℕ → Concentration S}
    (D : N.TierScaleDecomposition xs) (hpos : PositiveSequence xs)
    {y y' : Complex S} (hy : y ∈ N.complexes) (hy' : y' ∈ N.complexes)
    (hsame : TierSame xs y y') (n : ℕ) :
    Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y') =
      ∑ s : S, (((y s : ℝ) - (y' s : ℝ)) * D.residual n s) := by
  rw [D.logRatio_eq hpos n y y']
  have hz : ∑ i : Fin D.levels,
      D.scale i n * tierDirectionGap (D.direction i) y y' = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [D.same_gap_zero hy hy' hsame i]
  rw [hz, zero_add]

/-- Proposition-valued API for the existence part of Lemma 4.4. -/
def EveryTierSequenceHasScaleDecomposition (N : Network S) : Prop :=
  ∀ xs : ℕ → Concentration S, N.IsTierSequence xs →
    -- `TierScaleDecomposition` carries data (scales, directions, residual), so it lives in
    -- `Type`; wrap it to keep this a `Prop`.
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Nonempty (N.TierScaleDecomposition (xs ∘ φ))

end Network
end CRNT
