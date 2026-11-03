import CRNT.Dynamics.GordanAlternative
import CRNT.Decision.StrictConeRealization

/-!
# Every minimal critical siphon is drainable or self-replicable

Deshpande–Gopalkrishnan (2014, Theorem 5.3(2)), with their notion of criticality:
`T` is **critical** when no nonzero nonnegative conservation law has support contained in `T`
(`IsDGCritical`).  The repository's `IsCriticalSiphon` asks only that no law have support exactly
`T`; for that notion the dichotomy fails (`CRNT/Examples/CriticalSiphonDichotomyCounterexample`).

Proof (not the paper's Gaussian elimination).  Suppose a minimal critical siphon `T` is neither
flux-self-replicable nor flux-drainable.  Gordan's alternative gives nonzero `w, u ≥ 0` supported
in `T` with `⟨w, y' − y⟩ ≤ 0` and `⟨u, y' − y⟩ ≥ 0` for every reaction.
* The support of a nonzero `z ≥ 0` with `⟨z, y' − y⟩ ≤ 0` for all reactions is a siphon; inside `T`
  it is critical, so by minimality it is all of `T`.  Hence `w > 0` on `T`.
* With `λ = min_{u_s > 0} w_s / u_s`, `z = w − λ u` is `≥ 0`, still satisfies `⟨z, y' − y⟩ ≤ 0`,
  and vanishes somewhere in `T`; so `z = 0` and `w = λ u` is a conservation law supported in
  `T`, contradicting criticality.

Nothing here is an axiom or a `sorry`.
-/

open Finset

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Deshpande–Gopalkrishnan criticality: no nonzero nonnegative conservation law is supported in
`P`. -/
def IsDGCritical (N : Network S) (P : Finset S) : Prop :=
  ¬ ∃ w : S → ℝ, (∀ s, 0 ≤ w s) ∧ (∀ s, s ∉ P → w s = 0) ∧ (∃ s, 0 < w s) ∧
    ∀ r : N.R, ∑ s, w s * N.reactionVector r s = 0

/-- A critical siphon in the sense of Deshpande–Gopalkrishnan. -/
def IsDGCriticalSiphon (N : Network S) (P : Finset S) : Prop :=
  P.Nonempty ∧ N.IsSiphon P ∧ N.IsDGCritical P

/-- A minimal critical siphon in the sense of Deshpande–Gopalkrishnan. -/
def IsMinimalDGCriticalSiphon (N : Network S) (P : Finset S) : Prop :=
  N.IsDGCriticalSiphon P ∧
    ∀ Q : Finset S, Q ⊆ P → Q ≠ P → Q.Nonempty → ¬ N.IsDGCriticalSiphon Q

/-- Subsets of critical sets are critical. -/
theorem IsDGCritical.mono {N : Network S} {P Q : Finset S} (h : N.IsDGCritical P) (hQP : Q ⊆ P) :
    N.IsDGCritical Q := by
  rintro ⟨w, hw0, hwQ, hwne, hwc⟩
  exact h ⟨w, hw0, fun s hs => hwQ s fun hq => hs (hQP hq), hwne, hwc⟩

/-- Criticality in the paper's sense implies the repository's exact-support criticality. -/
theorem isCriticalSiphon_of_isDGCriticalSiphon {N : Network S} {P : Finset S}
    (h : N.IsDGCriticalSiphon P) : N.IsCriticalSiphon P := by
  refine ⟨h.1, h.2.1, ?_⟩
  rintro ⟨v, hv0, hvP, hvc⟩
  obtain ⟨s, hs⟩ := h.1
  exact h.2.2 ⟨v, hv0, fun t ht => le_antisymm (not_lt.mp fun hlt => ht ((hvP t).mp hlt)) (hv0 t),
    ⟨s, (hvP s).mpr hs⟩, hvc⟩

/-- The support of a nonzero nonnegative vector that is nonincreasing along every reaction is a
siphon. -/
theorem isSiphon_support_of_nonincreasing (N : Network S) {z : S → ℝ} (hz0 : ∀ s, 0 ≤ z s)
    (hz : ∀ r : N.R, ∑ s, z s * N.reactionVector r s ≤ 0) :
    N.IsSiphon (univ.filter fun s => 0 < z s) := by
  intro r ⟨s, hs, hprod⟩
  have hs' : 0 < z s := (mem_filter.mp hs).2
  have hsplit : ∑ s, z s * N.reactionVector r s =
      ∑ s, z s * ((N.reaction r).target s : ℝ) - ∑ s, z s * ((N.reaction r).source s : ℝ) := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun s _ => by rw [reactionVector_apply]; ring
  have htgt : 0 < ∑ s, z s * ((N.reaction r).target s : ℝ) := by
    have hle := single_le_sum (f := fun s => z s * ((N.reaction r).target s : ℝ))
      (fun t _ => mul_nonneg (hz0 t) (Nat.cast_nonneg _)) (mem_univ s)
    have : 0 < z s * ((N.reaction r).target s : ℝ) :=
      mul_pos hs' (by exact_mod_cast Nat.pos_of_ne_zero hprod)
    linarith
  have hsrc : 0 < ∑ s, z s * ((N.reaction r).source s : ℝ) := by
    have := hz r; rw [hsplit] at this; linarith
  obtain ⟨t, ht⟩ : ∃ t, 0 < z t * ((N.reaction r).source t : ℝ) := by
    by_contra hall
    push Not at hall
    exact absurd (sum_nonpos fun t _ => hall t) (not_le.mpr hsrc)
  have hzt : 0 < z t := by
    rcases (hz0 t).eq_or_lt with h | h
    · rw [← h, zero_mul] at ht; exact absurd ht (lt_irrefl 0)
    · exact h
  have hst : (N.reaction r).source t ≠ 0 := by
    intro h0; rw [h0, Nat.cast_zero, mul_zero] at ht; exact lt_irrefl 0 ht
  exact ⟨t, mem_filter.mpr ⟨mem_univ t, hzt⟩, hst⟩

/-- In a minimal critical siphon `T`, a nonzero nonnegative vector supported in `T` and
nonincreasing along every reaction is strictly positive on all of `T`. -/
theorem pos_on_of_nonincreasing {N : Network S} {T : Finset S} (hT : N.IsMinimalDGCriticalSiphon T)
    {z : S → ℝ} (hz0 : ∀ s, 0 ≤ z s) (hzT : ∀ s, s ∉ T → z s = 0) (hzne : ∃ s, 0 < z s)
    (hz : ∀ r : N.R, ∑ s, z s * N.reactionVector r s ≤ 0) : ∀ s ∈ T, 0 < z s := by
  set Q := univ.filter fun s => 0 < z s with hQ
  have hQT : Q ⊆ T := fun s hs => by
    by_contra hsT; have := (mem_filter.mp hs).2; rw [hzT s hsT] at this; exact lt_irrefl 0 this
  have hQne : Q.Nonempty := by
    obtain ⟨s, hs⟩ := hzne; exact ⟨s, mem_filter.mpr ⟨mem_univ s, hs⟩⟩
  have hQsiph := N.isSiphon_support_of_nonincreasing hz0 hz
  have hQcrit : N.IsDGCriticalSiphon Q := ⟨hQne, hQsiph, hT.1.2.2.mono hQT⟩
  have hQeq : Q = T := by
    by_contra hne; exact hT.2 Q hQT hne hQne hQcrit
  intro s hs
  rw [← hQeq] at hs
  exact (mem_filter.mp hs).2

/-- **Deshpande–Gopalkrishnan Theorem 5.3(2), flux form.** Every minimal critical siphon is
flux-drainable or flux-self-replicable. -/
theorem fluxDrainable_or_fluxSelfReplicable_of_minimalDGCritical {N : Network S} {T : Finset S}
    (hT : N.IsMinimalDGCriticalSiphon T) : N.IsFluxDrainable T ∨ N.IsFluxSelfReplicable T := by
  by_contra hboth
  push Not at hboth
  obtain ⟨hnd, hnsr⟩ := hboth
  -- a nonincreasing `w`
  obtain ⟨w, hw0, hwT, hwne, hw⟩ := gordan_alternative (fun r => N.reactionVector r) T
    (fun ⟨v, hv, hpos⟩ => hnsr ⟨v, hv, fun s hs => by simpa [fluxNetChange] using hpos s hs⟩)
  -- a nondecreasing `u`
  obtain ⟨u, hu0, huT, hune, hu⟩ := gordan_alternative (fun r => -N.reactionVector r) T
    (fun ⟨v, hv, hpos⟩ => hnd ⟨v, hv, fun s hs => by
      have := hpos s hs
      simp only [fluxNetChange, Pi.neg_apply, mul_neg, sum_neg_distrib] at this ⊢
      linarith⟩)
  have hu' : ∀ r : N.R, 0 ≤ ∑ s, u s * N.reactionVector r s := by
    intro r; have := hu r
    simp only [Pi.neg_apply, mul_neg, sum_neg_distrib] at this; linarith
  have hwpos := pos_on_of_nonincreasing hT hw0 hwT hwne hw
  -- the ratio `λ`
  set U := univ.filter fun s => 0 < u s with hU
  have hUne : U.Nonempty := by
    obtain ⟨s, hs⟩ := hune; exact ⟨s, mem_filter.mpr ⟨mem_univ s, hs⟩⟩
  have hUT : ∀ s ∈ U, s ∈ T := fun s hs => by
    by_contra hsT; have := (mem_filter.mp hs).2; rw [huT s hsT] at this; exact lt_irrefl 0 this
  set lam := U.inf' hUne (fun s => w s / u s) with hlam
  obtain ⟨s₀, hs₀U, hs₀⟩ := U.exists_mem_eq_inf' hUne (fun s => w s / u s)
  have hu₀ : 0 < u s₀ := (mem_filter.mp hs₀U).2
  have hlampos : 0 < lam := by
    rw [hlam, hs₀]; exact div_pos (hwpos s₀ (hUT s₀ hs₀U)) hu₀
  set z : S → ℝ := fun s => w s - lam * u s with hz
  have hz0 : ∀ s, 0 ≤ z s := by
    intro s
    by_cases hs : s ∈ U
    · have hle : lam ≤ w s / u s := U.inf'_le (fun s => w s / u s) hs
      have hus := (mem_filter.mp hs).2
      rw [le_div_iff₀ hus] at hle
      simp only [hz]; linarith
    · have : u s = 0 := le_antisymm (not_lt.mp fun h => hs (mem_filter.mpr ⟨mem_univ s, h⟩))
        (hu0 s)
      simp only [hz, this, mul_zero, sub_zero]; exact hw0 s
  have hzT : ∀ s, s ∉ T → z s = 0 := fun s hs => by simp [hz, hwT s hs, huT s hs]
  have hzr : ∀ r : N.R, ∑ s, z s * N.reactionVector r s ≤ 0 := by
    intro r
    have e : ∑ s, z s * N.reactionVector r s =
        ∑ s, w s * N.reactionVector r s - lam * ∑ s, u s * N.reactionVector r s := by
      rw [mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun s _ => by simp only [hz]; ring
    rw [e]; have := mul_nonneg hlampos.le (hu' r); linarith [hw r]
  have hzs₀ : z s₀ = 0 := by
    show w s₀ - lam * u s₀ = 0
    rw [hlam, hs₀, div_mul_cancel₀ _ hu₀.ne', sub_self]
  -- `z` must vanish identically
  have hzzero : ∀ s, z s = 0 := by
    by_contra hex
    push Not at hex
    obtain ⟨s, hs⟩ := hex
    have hzpos := pos_on_of_nonincreasing hT hz0 hzT ⟨s, lt_of_le_of_ne (hz0 s) (Ne.symm hs)⟩ hzr
    have := hzpos s₀ (hUT s₀ hs₀U)
    rw [hzs₀] at this; exact lt_irrefl 0 this
  -- so `w = λ u` is a conservation law supported in `T`
  apply hT.1.2.2
  refine ⟨w, hw0, hwT, hwne, fun r => le_antisymm (hw r) ?_⟩
  have e : ∑ s, w s * N.reactionVector r s = lam * ∑ s, u s * N.reactionVector r s := by
    rw [mul_sum]; refine sum_congr rfl fun s _ => ?_
    have := hzzero s; simp only [hz] at this
    rw [show w s = lam * u s by linarith]; ring
  rw [e]; exact mul_nonneg hlampos.le (hu' r)

/-- **Deshpande–Gopalkrishnan Theorem 5.3(2).** Every minimal critical siphon is drainable or
self-replicable (finite reaction pathways). -/
theorem drainable_or_selfReplicable_of_minimalDGCritical {N : Network S} {T : Finset S}
    (hT : N.IsMinimalDGCriticalSiphon T) : N.IsDrainable T ∨ N.IsSelfReplicable T := by
  rcases fluxDrainable_or_fluxSelfReplicable_of_minimalDGCritical hT with h | h
  · exact Or.inl ((N.isDrainable_iff_flux_of_realizable N.fluxSignRealizable T).mpr h)
  · exact Or.inr ((N.isSelfReplicable_iff_flux_of_realizable N.fluxSignRealizable T).mpr h)

/-- A conservation law pairs to zero with every flux's net change. -/
theorem sum_mul_fluxNetChange_eq_zero (N : Network S) {w : S → ℝ}
    (hw : ∀ r : N.R, ∑ s, w s * N.reactionVector r s = 0) (v : N.R → ℝ) :
    ∑ s, w s * N.fluxNetChange v s = 0 := by
  simp only [fluxNetChange, mul_sum]
  rw [sum_comm]
  refine sum_eq_zero fun r _ => ?_
  have e : ∑ s, w s * (v r * N.reactionVector r s) = v r * ∑ s, w s * N.reactionVector r s := by
    rw [mul_sum]; exact sum_congr rfl fun s _ => by ring
  rw [e, hw r, mul_zero]

/-- **Deshpande–Gopalkrishnan Theorem 5.3(1), drainable half.** A flux-drainable set is
critical. -/
theorem isDGCritical_of_isFluxDrainable {N : Network S} {T : Finset S}
    (h : N.IsFluxDrainable T) : N.IsDGCritical T := by
  rintro ⟨w, hw0, hwT, ⟨s₀, hs₀⟩, hwc⟩
  obtain ⟨v, -, hv⟩ := h
  have hs₀T : s₀ ∈ T := by by_contra h'; rw [hwT s₀ h'] at hs₀; exact lt_irrefl 0 hs₀
  have hneg : ∑ s, w s * N.fluxNetChange v s < 0 := by
    have hle : ∀ s, w s * N.fluxNetChange v s ≤ 0 := fun s => by
      by_cases hs : s ∈ T
      · exact mul_nonpos_of_nonneg_of_nonpos (hw0 s) (hv s hs).le
      · rw [hwT s hs, zero_mul]
    have hpos : 0 < ∑ s, -(w s * N.fluxNetChange v s) :=
      lt_of_lt_of_le (by linarith [mul_neg_of_pos_of_neg hs₀ (hv s₀ hs₀T)])
        (single_le_sum (f := fun s => -(w s * N.fluxNetChange v s))
          (fun s _ => by linarith [hle s]) (mem_univ s₀))
    rw [sum_neg_distrib] at hpos
    linarith
  rw [N.sum_mul_fluxNetChange_eq_zero hwc v] at hneg
  exact lt_irrefl 0 hneg

/-- **Deshpande–Gopalkrishnan Theorem 5.3(1), self-replicable half.** -/
theorem isDGCritical_of_isFluxSelfReplicable {N : Network S} {T : Finset S}
    (h : N.IsFluxSelfReplicable T) : N.IsDGCritical T := by
  rintro ⟨w, hw0, hwT, ⟨s₀, hs₀⟩, hwc⟩
  obtain ⟨v, -, hv⟩ := h
  have hs₀T : s₀ ∈ T := by by_contra h'; rw [hwT s₀ h'] at hs₀; exact lt_irrefl 0 hs₀
  have hpos : 0 < ∑ s, w s * N.fluxNetChange v s := by
    have hge : ∀ s, 0 ≤ w s * N.fluxNetChange v s := fun s => by
      by_cases hs : s ∈ T
      · exact mul_nonneg (hw0 s) (hv s hs).le
      · rw [hwT s hs, zero_mul]
    exact lt_of_lt_of_le (mul_pos hs₀ (hv s₀ hs₀T))
      (single_le_sum (f := fun s => w s * N.fluxNetChange v s) (fun s _ => hge s) (mem_univ s₀))
  rw [N.sum_mul_fluxNetChange_eq_zero hwc v] at hpos
  exact lt_irrefl 0 hpos

end Network
end CRNT
