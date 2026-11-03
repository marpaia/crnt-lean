import CRNT.Multistationarity.ConcordanceConverse

/-!
# Concordance injectivity including a boundary composition

`Kinetics.BoundaryInjective` uses two nonnegative compatible compositions, at least
one positive, as in Shinar–Feinberg Definition 4.3. The existing `Injective` API
continues to mean injectivity on positive compatibility classes. This module
proves the stronger conclusion and the corresponding concordance equivalence.
The kinetics still satisfy the admissibility fields of `Kinetics`.
-/

namespace CRNT.Network
open scoped BigOperators
variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}
namespace Kinetics

/-- Injectivity on compatible nonnegative pairs with at least one positive member. -/
def BoundaryInjective (K : Kinetics N) : Prop :=
  ∀ {x y : Concentration S}, x.Nonnegative → y.Nonnegative →
    (x.Positive ∨ y.Positive) → y - x ∈ N.stoichSubspace →
    K.vectorField x = K.vectorField y → x = y

/-- Weak monotonicity forces a positive rate at a positive composition for every
reaction with at least one source species. Zero-source reactions are excluded. -/
theorem rate_pos_of_positive_source {K : Kinetics N} (hwm : K.WeaklyMonotonic)
    {x : Concentration S} (hx : x.Positive) (r : N.R) (s : S)
    (hs : (N.reaction r).source s ≠ 0) : 0 < K.rate r x := by
  have hhalf : Concentration.Positive (fun s => x s / 2) := by
    intro s; exact div_pos (hx s) (by norm_num)
  have hle : (fun s => x s / 2) ≤ x := by intro s; linarith [hx s]
  have hmono := K.rate_mono r hhalf.nonnegative hx.nonnegative hle
  have hnonneg := K.rate_nonneg r hhalf.nonnegative
  by_contra hnot
  have hz : K.rate r (fun s => x s / 2) = K.rate r x := by
    have := K.rate_nonneg r hx.nonnegative
    push Not at hnot
    linarith
  have hw := (hwm (fun s => x s / 2) x hhalf.nonnegative hx.nonnegative r
    (fun s _ => (hhalf s).ne') (fun s _ => (hx s).ne')).2 hz
  rcases hw with heq | ⟨_, s', _, _, _, hlt⟩
  · have := heq s hs
    linarith [hx s]
  · linarith [hx s']

/-- A boundary/positive collision gives the same forbidden sign witness. -/
theorem concordanceWitness_of_eq_vectorField_nonnegative_positive
    {K : Kinetics N} (hwm : K.WeaklyMonotonic)
    {cs css : Concentration S} (hcs : cs.Nonnegative) (hcss : css.Positive)
    (hmem : css - cs ∈ N.stoichSubspace) (hne : cs ≠ css)
    (hfield : K.vectorField cs = K.vectorField css) :
    N.ConcordanceWitness (fun r => K.rate r css - K.rate r cs) (css - cs) := by
  set α : N.R → ℝ := fun r => K.rate r css - K.rate r cs with hα
  set σ : Concentration S := css - cs with hσ
  -- The support guards are vacuous: positive compositions never vanish.
  have hcssg : ∀ r : N.R, ∀ s : S, (N.reaction r).source s ≠ 0 → css s ≠ 0 :=
    fun r s _ => (hcss s).ne'
  -- The induced species displacement vanishes, i.e. `α ∈ ker L`.
  have hker : N.InKerL α := by
    refine N.inKerL_of_apply fun s => ?_
    have hx : K.vectorField cs s = K.vectorField css s := by rw [hfield]
    have : ∑ r : N.R, (K.rate r css - K.rate r cs) * N.reactionVector r s
        = (∑ r : N.R, K.rate r css * N.reactionVector r s)
          - ∑ r : N.R, K.rate r cs * N.reactionVector r s := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun r _ => by ring
    simp only [hα]
    rw [this]
    have e1 : ∑ r : N.R, K.rate r css * N.reactionVector r s = K.vectorField css s :=
      (K.vectorField_apply css s).symm
    have e2 : ∑ r : N.R, K.rate r cs * N.reactionVector r s = K.vectorField cs s :=
      (K.vectorField_apply cs s).symm
    rw [e1, e2, ← hx, sub_self]
  refine ⟨hker, hmem, ?_, ?_, ?_⟩
  · -- `σ ≠ 0` since `cs ≠ css`.
    simp only [hσ]
    intro h
    exact hne (sub_eq_zero.mp h).symm
  · -- Clause (i).
    intro r hαr
    by_cases hcsg : ∀ s : S, (N.reaction r).source s ≠ 0 → cs s ≠ 0
    · have hwmr := hwm cs css hcs hcss.nonnegative r hcsg (hcssg r)
      rcases lt_or_gt_of_ne hαr with hlt | hgt
      · -- `α r < 0`, i.e. `K css < K cs`; the rate strictly decreases, apply (i) swapped.
        have hrate : K.rate r css < K.rate r cs := by simp only [hα] at hlt; linarith
        have hwmr' := hwm css cs hcss.nonnegative hcs r (hcssg r) hcsg
        obtain ⟨s, hs, hsgt⟩ := hwmr'.1 hrate
        refine ⟨s, hs, ?_⟩
        have hσs : σ s < 0 := by simp only [hσ, Pi.sub_apply]; linarith
        have hαneg : α r < 0 := hlt
        rw [_root_.sign_neg hσs, _root_.sign_neg hαneg]
      · -- `α r > 0`, i.e. `K cs < K css`; the rate strictly increases, apply (i).
        have hrate : K.rate r cs < K.rate r css := by simp only [hα] at hgt; linarith
        obtain ⟨s, hs, hsgt⟩ := hwmr.1 hrate
        refine ⟨s, hs, ?_⟩
        have hσs : 0 < σ s := by simp only [hσ, Pi.sub_apply]; linarith
        have hαpos : 0 < α r := hgt
        rw [_root_.sign_pos hσs, _root_.sign_pos hαpos]
    · push Not at hcsg
      obtain ⟨s, hs, hz⟩ := hcsg
      have hrzero := K.rate_vanishing r hs hz
      have hrpos := rate_pos_of_positive_source hwm hcss r s hs
      refine ⟨s, hs, ?_⟩
      have hσs : 0 < σ s := by simpa [hσ, hz] using hcss s
      have hαpos : 0 < α r := by simpa [hα, hrzero] using hrpos
      rw [_root_.sign_pos hσs, _root_.sign_pos hαpos]
  · -- Clause (ii).
    intro r hαr
    by_cases hcsg : ∀ s : S, (N.reaction r).source s ≠ 0 → cs s ≠ 0
    · have hwmr := hwm cs css hcs hcss.nonnegative r hcsg (hcssg r)
      have hrate : K.rate r cs = K.rate r css := by
        simp only [hα] at hαr; linarith
      rcases hwmr.2 hrate with heq | ⟨s, s', hs, hs', hgt, hlt⟩
      · left
        intro s hs
        have := heq s hs
        simp only [hσ, Pi.sub_apply]; linarith
      · right
        refine ⟨s', s, hs', hs, ?_, ?_⟩
        · simp only [hσ, Pi.sub_apply]; linarith
        · simp only [hσ, Pi.sub_apply]; linarith
    · push Not at hcsg
      obtain ⟨s, hs, hz⟩ := hcsg
      have hrzero := K.rate_vanishing r hs hz
      have hrpos := rate_pos_of_positive_source hwm hcss r s hs
      have hαpos : 0 < α r := by simpa [hα, hrzero] using hrpos
      exact (hαpos.ne' hαr).elim

theorem BoundaryInjective.injective {K : Kinetics N} (h : K.BoundaryInjective) :
    K.Injective := by
  intro x₀ x hx y hy hf
  apply h hx.2.nonnegative hy.2.nonnegative (Or.inl hx.2) _ hf
  have heq : y - x = (y - x₀) - (x - x₀) := by ring
  rw [heq]
  exact N.stoichSubspace.sub_mem hy.1 hx.1

end Kinetics

/-- Concordance excludes collisions even when one composition is on the boundary. -/
theorem Concordant.boundaryInjective_of_weaklyMonotonic (hN : N.Concordant)
    {K : Kinetics N} (hwm : K.WeaklyMonotonic) : K.BoundaryInjective := by
  intro x y hx hy hpos hmem hf
  by_contra hne
  rcases hpos with hxpos | hypos
  · have hmem' : x - y ∈ N.stoichSubspace := by
      simpa only [neg_sub] using N.stoichSubspace.neg_mem hmem
    exact hN ⟨_, _, Kinetics.concordanceWitness_of_eq_vectorField_nonnegative_positive
      hwm hy hxpos hmem' (Ne.symm hne) hf.symm⟩
  · exact hN ⟨_, _, Kinetics.concordanceWitness_of_eq_vectorField_nonnegative_positive
      hwm hx hypos hmem hne hf⟩

/-- Concordance characterization for boundary-inclusive injectivity, within the
admissible `Kinetics` class. -/
theorem concordant_iff_all_weaklyMonotonic_boundaryInjective (N : Network S) :
    N.Concordant ↔ ∀ K : Kinetics N, K.WeaklyMonotonic → K.BoundaryInjective := by
  constructor
  · intro hN K hwm; exact hN.boundaryInjective_of_weaklyMonotonic hwm
  · intro hall
    apply (N.concordant_iff_all_weaklyMonotonic_injective).mpr
    intro K hwm
    exact Kinetics.BoundaryInjective.injective (hall K hwm)

end CRNT.Network
