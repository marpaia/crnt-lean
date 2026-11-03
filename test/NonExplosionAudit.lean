import CRNT.Stochastic.NonExplosionAS
import Mathlib.Probability.HasLawExists

open MeasureTheory ProbabilityTheory

/-- Non-vacuity of the holding-time hypotheses: an i.i.d. sequence (here with law `δ₁`) on some
probability space satisfies all of them. -/
example : ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (E : ℕ → Ω → ℝ),
    IsProbabilityMeasure μ ∧ (∀ k, Measurable (E k)) ∧ iIndepFun E μ ∧
      (∀ k, ∀ᵐ ω ∂μ, 0 ≤ E k ω) ∧ (∀ k, (1 : ENNReal) ≤ μ {ω | 1 ≤ E k ω}) := by
  obtain ⟨Ω, mΩ, P, X, hX, hlaw, hind, hP⟩ := exists_iid ℕ (Measure.dirac (1 : ℝ))
  refine ⟨Ω, mΩ, P, X, hP, hX, hind, fun k => ?_, fun k => ?_⟩
  · have := (hlaw k).map_eq
    rw [ae_iff]
    have hm : P {ω | ¬ 0 ≤ X k ω} = (P.map (X k)) (Set.Iio 0) := by
      rw [Measure.map_apply (hX k) measurableSet_Iio]
      congr 1; ext ω; simp
    rw [hm, this]
    simp
  · have := (hlaw k).map_eq
    have hm : P {ω | 1 ≤ X k ω} = (P.map (X k)) (Set.Ici 1) := by
      rw [Measure.map_apply (hX k) measurableSet_Ici]
      rfl
    rw [hm, this]
    simp
