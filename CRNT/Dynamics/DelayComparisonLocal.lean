import CRNT.Dynamics.DelayComparisonLattice

/-! # Local comparison for delay equations

This module develops the componentwise delay comparison argument with Lipschitz control only on
an order-convex region containing the compared states and their joins. The delayed monotonicity
assumption is likewise restricted to a supplied set of delayed states. -/

namespace CRNT
namespace Dynamics

open Filter Topology Set
open scoped BigOperators NNReal

variable {S : Type} [Fintype S]

/-- One-step ODE comparison with Lipschitz continuity restricted to a join-closed state set. -/
theorem kamke_comparison_step_on {a b : ℝ} {f : ℝ → (S → ℝ) → (S → ℝ)} {L : ℝ≥0}
    {K : Set (S → ℝ)}
    (hlip : ∀ t ∈ Set.Icc a b, LipschitzOnWith L (f t) K)
    (hsup : ∀ a ∈ K, ∀ b ∈ K, a ⊔ b ∈ K)
    (hkamke : ∀ t ∈ Set.Icc a b, ∀ u u', u ∈ K → u' ∈ K → u ≤ u' → ∀ i, u i = u' i → f t u i ≤ f t u' i)
    {x y : ℝ → (S → ℝ)} {fx : ℝ → (S → ℝ)}
    (hx : ∀ t ∈ Set.Icc a b, HasDerivWithinAt x (fx t) (Set.Icc a b) t)
    (hsub : ∀ t ∈ Set.Icc a b, fx t ≤ f t (x t))
    (hy : ∀ t ∈ Set.Icc a b, HasDerivWithinAt y (f t (y t)) (Set.Icc a b) t)
    (hxK : ∀ t ∈ Set.Icc a b, x t ∈ K)
    (hyK : ∀ t ∈ Set.Icc a b, y t ∈ K)
    (ha : x a ≤ y a) :
    ∀ t ∈ Set.Icc a b, x t ≤ y t := by
  set D := Set.Icc a b
  set C : ℝ := 2 * L * Fintype.card S
  let w : ℝ → S → ℝ := fun t i => max (x t i - y t i) 0
  let V : ℝ → ℝ := fun t => ∑ i, (w t i) ^ 2
  have hV0 : ∀ t, 0 ≤ V t := fun t => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hw_le : ∀ t i, w t i ≤ Real.sqrt (V t) := by
    intro t i
    rw [Real.le_sqrt (le_max_right _ _) (hV0 t)]
    exact Finset.single_le_sum (f := fun i => (w t i) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  -- the derivative of `V`
  have hVd : ∀ t ∈ D, HasDerivWithinAt V
      (∑ i, 2 * w t i * (fx t i - f t (y t) i)) D t := by
    intro t ht
    refine HasDerivWithinAt.fun_sum fun i _ => ?_
    have hxi := (hasDerivWithinAt_pi.mp (hx t ht)) i
    have hyi := (hasDerivWithinAt_pi.mp (hy t ht)) i
    exact (Monotone.hasDerivAt_posPart_sq (x t i - y t i)).comp_hasDerivWithinAt t (hxi.sub hyi)
  -- the differential inequality `V' ≤ C V`
  have hVineq : ∀ t ∈ D, (∑ i, 2 * w t i * (fx t i - f t (y t) i)) ≤ C * V t := by
    intro t ht
    set z := x t ⊔ y t
    have hzK : z ∈ K := hsup _ (hxK t ht) _ (hyK t ht)
    have hzy : ‖z - y t‖ ≤ Real.sqrt (V t) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
      have this : (z - y t) i = w t i := by
        simp only [z, Pi.sub_apply, Pi.sup_apply, w]
        rcases le_total (x t i) (y t i) with h | h
        · rw [max_eq_right h, max_eq_right (by linarith)]; ring
        · rw [max_eq_left h, max_eq_left (by linarith)]
      rw [this, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact hw_le t i
    have hfl : ‖f t z - f t (y t)‖ ≤ (L : ℝ) * Real.sqrt (V t) :=
      (hlip t ht).norm_sub_le hzK (hyK t ht) |>.trans (mul_le_mul_of_nonneg_left hzy L.2)
    have hterm : ∀ i, 2 * w t i * (fx t i - f t (y t) i)
        ≤ 2 * (L : ℝ) * Real.sqrt (V t) * Real.sqrt (V t) := by
      intro i
      by_cases hpos : 0 < x t i - y t i
      · have hwi : w t i = x t i - y t i := max_eq_left hpos.le
        have hxz : x t ≤ z := le_sup_left
        have hxi : x t i = z i := by
          simp only [z, Pi.sup_apply]
          exact (max_eq_left (by linarith)).symm
        have h1 : f t (x t) i ≤ f t z i := hkamke t ht (x t) z (hxK t ht) hzK hxz i hxi
        have h2 : f t z i - f t (y t) i ≤ (L : ℝ) * Real.sqrt (V t) := by
          have := norm_le_pi_norm (f t z - f t (y t)) i
          rw [Pi.sub_apply, Real.norm_eq_abs] at this
          linarith [le_abs_self (f t z i - f t (y t) i)]
        have hw0 : 0 ≤ w t i := le_max_right _ _
        calc 2 * w t i * (fx t i - f t (y t) i)
            ≤ 2 * w t i * (f t (x t) i - f t (y t) i) :=
              mul_le_mul_of_nonneg_left (by linarith [hsub t ht i]) (by positivity)
          _ ≤ 2 * w t i * ((L : ℝ) * Real.sqrt (V t)) :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          _ ≤ 2 * Real.sqrt (V t) * ((L : ℝ) * Real.sqrt (V t)) := by
              have := hw_le t i
              have : 0 ≤ (L : ℝ) * Real.sqrt (V t) := by positivity
              nlinarith
          _ = 2 * (L : ℝ) * Real.sqrt (V t) * Real.sqrt (V t) := by ring
      · have hwi : w t i = 0 := max_eq_right (not_lt.mp hpos)
        rw [hwi, mul_zero, zero_mul]
        positivity
    calc (∑ i, 2 * w t i * (fx t i - f t (y t) i))
        ≤ ∑ _i : S, 2 * (L : ℝ) * Real.sqrt (V t) * Real.sqrt (V t) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = C * V t := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc (2 * (L : ℝ)),
            Real.mul_self_sqrt (hV0 t)]
          simp only [C]; ring
  -- the auxiliary function `g t = exp (-C t) * V t` is nonincreasing
  let g : ℝ → ℝ := fun t => Real.exp (-C * t) * V t
  have hgd : ∀ t ∈ D, HasDerivWithinAt g
      (Real.exp (-C * t) * (-C) * V t +
        Real.exp (-C * t) * ∑ i, 2 * w t i * (fx t i - f t (y t) i)) D t := by
    intro t ht
    have he : HasDerivWithinAt (fun t => Real.exp (-C * t)) (Real.exp (-C * t) * (-C)) D t := by
      have := ((hasDerivAt_id t).const_mul (-C)).exp
      simpa using this.hasDerivWithinAt
    exact he.mul (hVd t ht)
  have hanti : AntitoneOn g D := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
      (fun t ht => (hgd t ht).continuousWithinAt)
      (fun t ht => (hgd t (interior_subset ht)).mono interior_subset) ?_
    intro t ht
    have := hVineq t (interior_subset ht)
    have hep := Real.exp_pos (-C * t)
    nlinarith [mul_le_mul_of_nonneg_left this hep.le]
  have hV00 : V a = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    have : x a i - y a i ≤ 0 := by linarith [ha i]
    simp [w, max_eq_right this]
  intro t ht
  have h0D : a ∈ D := ⟨le_refl a, ht.1.trans ht.2⟩
  have hgt : g t ≤ g a := hanti h0D ht ht.1
  simp only [g, mul_zero, hV00] at hgt
  have hVt : V t = 0 := by
    have := Real.exp_pos (-C * t)
    have : V t ≤ 0 := by nlinarith [hV0 t]
    linarith [hV0 t]
  intro i
  have hwi : w t i ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (w t j))).mp hVt i (Finset.mem_univ i)
  have : max (x t i - y t i) 0 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hwi
  have := le_max_left (x t i - y t i) 0
  linarith


/-- Finite-interval orthant invariance from boundary inwardness and a local Lipschitz bound.

Unlike the global scalar Nagumo lemma, this version only requires the Lipschitz estimate on a
state region containing the trajectory and its coordinatewise positive part. It is useful for
polynomial fields, whose derivative need not be globally bounded. -/
theorem forwardInvariant_nonnegOrthant_step_on
    {a b : ℝ} {f : ℝ → (S → ℝ) → (S → ℝ)} {L : ℝ≥0} {K : Set (S → ℝ)}
    (hlip : ∀ t ∈ Set.Icc a b, LipschitzOnWith L (f t) K)
    (hclamp : ∀ u ∈ K, (fun i => max (u i) 0) ∈ K)
    (hboundary : ∀ t ∈ Set.Icc a b, ∀ u ∈ K, (∀ j, 0 ≤ u j) →
      ∀ i, u i = 0 → 0 ≤ f t u i)
    {x : ℝ → (S → ℝ)}
    (hx : ∀ t ∈ Set.Icc a b, HasDerivWithinAt x (f t (x t)) (Set.Icc a b) t)
    (hxK : ∀ t ∈ Set.Icc a b, x t ∈ K)
    (ha : ∀ i, 0 ≤ x a i) :
    ∀ t ∈ Set.Icc a b, ∀ i, 0 ≤ x t i := by
  set D := Set.Icc a b
  set C : ℝ := 2 * (L : ℝ) * Fintype.card S
  let w : ℝ → S → ℝ := fun t i => max (-(x t i)) 0
  let V : ℝ → ℝ := fun t => ∑ i, (w t i) ^ 2
  have hV0 : ∀ t, 0 ≤ V t := fun t => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hw_le : ∀ t i, w t i ≤ Real.sqrt (V t) := by
    intro t i
    rw [Real.le_sqrt (le_max_right _ _) (hV0 t)]
    exact Finset.single_le_sum (f := fun i => (w t i) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  have hVd : ∀ t ∈ D, HasDerivWithinAt V
      (∑ i, 2 * w t i * (-(f t (x t) i))) D t := by
    intro t ht
    refine HasDerivWithinAt.fun_sum fun i _ => ?_
    have hxi := (hasDerivWithinAt_pi.mp (hx t ht)) i
    exact (Monotone.hasDerivAt_posPart_sq (-(x t i))).comp_hasDerivWithinAt t hxi.neg
  have hVineq : ∀ t ∈ D, (∑ i, 2 * w t i * (-(f t (x t) i))) ≤ C * V t := by
    intro t ht
    let z : S → ℝ := fun i => max (x t i) 0
    have hzK : z ∈ K := by
      exact hclamp (x t) (hxK t ht)
    have hzx : ‖z - x t‖ ≤ Real.sqrt (V t) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
      have hi : (z - x t) i = w t i := by
        dsimp [z, w]
        rcases le_total 0 (x t i) with h | h
        · rw [max_eq_left h, max_eq_right (by linarith)]
          simp
        · rw [max_eq_right h, max_eq_left (by linarith)]
          ring
      rw [hi, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact hw_le t i
    have hfl : ‖f t z - f t (x t)‖ ≤ (L : ℝ) * Real.sqrt (V t) :=
      (hlip t ht).norm_sub_le hzK (hxK t ht) |>.trans
        (mul_le_mul_of_nonneg_left hzx L.2)
    have hterm : ∀ i, 2 * w t i * (-(f t (x t) i)) ≤
        2 * (L : ℝ) * Real.sqrt (V t) * Real.sqrt (V t) := by
      intro i
      by_cases hneg : x t i < 0
      · have hwi : w t i = -(x t i) := max_eq_left (by linarith)
        have hzi : z i = 0 := by simp [z, max_eq_right hneg.le]
        have hface := hboundary t ht z hzK (fun j => le_max_right (x t j) 0) i hzi
        have hdiff : -(f t (x t) i) ≤ (L : ℝ) * Real.sqrt (V t) := by
          have hcoord := norm_le_pi_norm (f t z - f t (x t)) i
          rw [Pi.sub_apply, Real.norm_eq_abs] at hcoord
          have hlower : -(f t (x t) i) ≤ f t z i - f t (x t) i := by linarith [hface]
          have habs : f t z i - f t (x t) i ≤ |f t z i - f t (x t) i| := le_abs_self _
          linarith [hfl, hcoord]
        calc 2 * w t i * (-(f t (x t) i))
            ≤ 2 * w t i * ((L : ℝ) * Real.sqrt (V t)) :=
              mul_le_mul_of_nonneg_left hdiff (by positivity)
          _ ≤ 2 * Real.sqrt (V t) * ((L : ℝ) * Real.sqrt (V t)) := by
              have hmul := mul_le_mul_of_nonneg_right (hw_le t i)
                (show 0 ≤ (L : ℝ) * Real.sqrt (V t) by positivity)
              nlinarith
          _ = 2 * (L : ℝ) * Real.sqrt (V t) * Real.sqrt (V t) := by ring
      · have hwi : w t i = 0 := max_eq_right (by linarith)
        have hR : 0 ≤ 2 * (L : ℝ) * Real.sqrt (V t) * Real.sqrt (V t) :=
          mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) L.2)
            (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
        calc 2 * w t i * (-(f t (x t) i)) = 0 := by simp [hwi]
          _ ≤ 2 * (L : ℝ) * Real.sqrt (V t) * Real.sqrt (V t) := hR
    calc (∑ i, 2 * w t i * (-(f t (x t) i)))
        ≤ ∑ _i : S, 2 * (L : ℝ) * Real.sqrt (V t) * Real.sqrt (V t) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = C * V t := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc (2 * (L : ℝ)),
            Real.mul_self_sqrt (hV0 t)]
          simp only [C]
          ring
  let g : ℝ → ℝ := fun t => Real.exp (-C * t) * V t
  have hgd : ∀ t ∈ D, HasDerivWithinAt g
      (Real.exp (-C * t) * (-C) * V t +
        Real.exp (-C * t) * ∑ i, 2 * w t i * (-(f t (x t) i))) D t := by
    intro t ht
    have he : HasDerivWithinAt (fun t => Real.exp (-C * t))
        (Real.exp (-C * t) * (-C)) D t := by
      have := ((hasDerivAt_id t).const_mul (-C)).exp
      simpa using this.hasDerivWithinAt
    exact he.mul (hVd t ht)
  have hanti : AntitoneOn g D := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
      (fun t ht => (hgd t ht).continuousWithinAt)
      (fun t ht => (hgd t (interior_subset ht)).mono interior_subset) ?_
    intro t ht
    have hineq := hVineq t (interior_subset ht)
    have hep := Real.exp_pos (-C * t)
    nlinarith [mul_le_mul_of_nonneg_left hineq hep.le]
  have hV0a : V a = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    have hnonneg : 0 ≤ x a i := ha i
    simp [w, max_eq_right (by linarith : -(x a i) ≤ 0)]
  intro t ht i
  have haD : a ∈ D := ⟨le_rfl, ht.1.trans ht.2⟩
  have hgt := hanti haD ht ht.1
  simp only [g, hV0a, mul_zero] at hgt
  have hVt : V t = 0 := by
    have hVt_nonneg := hV0 t
    have hexp := Real.exp_pos (-C * t)
    have : Real.exp (-C * t) * V t ≤ 0 := by simpa using hgt
    nlinarith
  have hwi : w t i ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (w t j))).mp hVt i
      (Finset.mem_univ i)
  have hzero : w t i = 0 := (pow_eq_zero_iff (n := 2) (by norm_num)).mp hwi
  have hle := le_max_left (-(x t i)) 0
  simp only [w] at hzero
  linarith


end Dynamics
end CRNT

namespace CRNT
namespace Dynamics

open Filter Topology Set
open scoped BigOperators NNReal

variable {S : Type} [Fintype S]

/-- One delay-step comparison with current Lipschitz and delayed monotonicity restricted to sets.
The delayed states need only belong to `D`; no global monotonicity outside `D` is assumed. -/
theorem delay_comparison_step_local {f : ℝ → (S → ℝ) → (S → ℝ) → (S → ℝ)}
    {K D : Set (S → ℝ)} {L : ℝ≥0} {τ a b : ℝ}
    (hlip : ∀ t ∈ Set.Icc a b, ∀ v ∈ D, LipschitzOnWith L (fun u => f t u v) K)
    (hsup : ∀ u ∈ K, ∀ u' ∈ K, u ⊔ u' ∈ K)
    (hkamke : ∀ t ∈ Set.Icc a b, ∀ v u u', v ∈ D → u ∈ K → u' ∈ K → u ≤ u' →
      ∀ i, u i = u' i → f t u v i ≤ f t u' v i)
    (hdel : ∀ t ∈ Set.Icc a b, ∀ u v v', u ∈ K → v ∈ D → v' ∈ D → v ≤ v' →
      f t u v ≤ f t u v')
    {x y : ℝ → (S → ℝ)} {fx : ℝ → (S → ℝ)}
    (hx : ∀ t ∈ Set.Icc a b, HasDerivWithinAt x (fx t) (Set.Icc a b) t)
    (hsub : ∀ t ∈ Set.Icc a b, fx t ≤ f t (x t) (x (t - τ)))
    (hy : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt y (f t (y t) (y (t - τ))) (Set.Icc a b) t)
    (hdelayed : ∀ t ∈ Set.Icc a b, x (t - τ) ≤ y (t - τ))
    (hxK : ∀ t ∈ Set.Icc a b, x t ∈ K)
    (hyK : ∀ t ∈ Set.Icc a b, y t ∈ K)
    (hdelD : ∀ t ∈ Set.Icc a b, x (t - τ) ∈ D ∧ y (t - τ) ∈ D)
    (ha : x a ≤ y a) :
    ∀ t ∈ Set.Icc a b, x t ≤ y t := by
  let g : ℝ → (S → ℝ) → (S → ℝ) := fun t u => f t u (y (t - τ))
  have hglip : ∀ t ∈ Set.Icc a b, LipschitzOnWith L (g t) K := by
    intro t ht
    exact hlip t ht (y (t - τ)) (hdelD t ht).2
  have hgkamke : ∀ t ∈ Set.Icc a b, ∀ u u', u ∈ K → u' ∈ K → u ≤ u' →
      ∀ i, u i = u' i → g t u i ≤ g t u' i := by
    intro t ht u u' hu hu' huu i hi
    exact hkamke t ht (y (t - τ)) u u' (hdelD t ht).2 hu hu' huu i hi
  have hsub' : ∀ t ∈ Set.Icc a b, fx t ≤ g t (x t) := by
    intro t ht
    exact (hsub t ht).trans (hdel t ht (x t) (x (t - τ)) (y (t - τ))
      (hxK t ht) (hdelD t ht).1 (hdelD t ht).2 (hdelayed t ht))
  have hy' : ∀ t ∈ Set.Icc a b, HasDerivWithinAt y (g t (y t)) (Set.Icc a b) t := by
    intro t ht
    exact hy t ht
  exact kamke_comparison_step_on hglip hsup hgkamke hx hsub' hy' hxK hyK ha

/-- Finite-interval delay comparison when current-state Lipschitz and delayed-state
monotonicity are known only on supplied regions. The hypotheses explicitly require both
trajectories to stay in the current-state region `K` and all delayed samples on the comparison
interval to lie in `D`; this theorem does not provide existence or invariance of those regions. -/
theorem delay_comparison_subsolution_local
    {f : ℝ → (S → ℝ) → (S → ℝ) → (S → ℝ)}
    {K D : Set (S → ℝ)} {L : ℝ≥0} {τ T : ℝ}
    (hτ : 0 < τ) (hT : 0 ≤ T)
    (hlip : ∀ t ∈ Set.Icc 0 T, ∀ v ∈ D, LipschitzOnWith L (fun u => f t u v) K)
    (hsup : ∀ u ∈ K, ∀ u' ∈ K, u ⊔ u' ∈ K)
    (hkamke : ∀ t ∈ Set.Icc 0 T, ∀ v u u', v ∈ D → u ∈ K → u' ∈ K → u ≤ u' →
      ∀ i, u i = u' i → f t u v i ≤ f t u' v i)
    (hdel : ∀ t ∈ Set.Icc 0 T, ∀ u v v', u ∈ K → v ∈ D → v' ∈ D → v ≤ v' →
      f t u v ≤ f t u v')
    {x y : ℝ → (S → ℝ)} {fx : ℝ → (S → ℝ)}
    (hx : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt x (fx t) (Set.Icc 0 T) t)
    (hsub : ∀ t ∈ Set.Icc 0 T, fx t ≤ f t (x t) (x (t - τ)))
    (hy : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt y (f t (y t) (y (t - τ))) (Set.Icc 0 T) t)
    (horder : ∀ r ∈ Set.Icc (-τ) 0, x r ≤ y r)
    (hxK : ∀ t ∈ Set.Icc 0 T, x t ∈ K)
    (hyK : ∀ t ∈ Set.Icc 0 T, y t ∈ K)
    (hdelD : ∀ t ∈ Set.Icc 0 T, x (t - τ) ∈ D ∧ y (t - τ) ∈ D) :
    ∀ r ∈ Set.Icc 0 T, x r ≤ y r := by
  have hstep : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) * τ = (n : ℝ) * τ + τ := by
    intro n
    push_cast
    ring
  have hnext : ∀ n : ℕ, (n : ℝ) * τ ≤ ((n + 1 : ℕ) : ℝ) * τ := by
    intro n
    rw [hstep n]
    linarith
  have hall : ∀ n : ℕ, ∀ r ∈ Set.Icc 0 (min T ((n : ℝ) * τ)), x r ≤ y r := by
    intro n
    induction n with
    | zero =>
        intro r hr
        have hmin : min T (((0 : ℕ) : ℝ) * τ) = 0 := by
          rw [Nat.cast_zero, zero_mul]
          exact min_eq_right (by simpa using hT)
        have hr0 : r = 0 := by
          rw [hmin] at hr
          exact le_antisymm hr.2 (by linarith [hr.1])
        subst hr0
        exact horder 0 ⟨by linarith [hτ], le_rfl⟩
    | succ n ih =>
        intro r hr
        by_cases haT : T ≤ (n : ℝ) * τ
        · have hmin : min T ((n : ℝ) * τ) = T := min_eq_left haT
          have hbmin : min T (((n + 1 : ℕ) : ℝ) * τ) = T :=
            min_eq_left (haT.trans (hnext n))
          have h1 := ih r
          rw [hmin] at h1
          rw [hbmin] at hr
          exact h1 hr
        · have haT' : (n : ℝ) * τ < T := by linarith
          have hmin : min T ((n : ℝ) * τ) = (n : ℝ) * τ := min_eq_right (le_of_lt haT')
          have hbT : min T (((n + 1 : ℕ) : ℝ) * τ) ≤ T := min_le_left _ _
          have h0n : 0 ≤ (n : ℝ) * τ := mul_nonneg (Nat.cast_nonneg n) hτ.le
          have hdel' : ∀ t ∈ Set.Icc ((n : ℝ) * τ) (min T (((n + 1 : ℕ) : ℝ) * τ)),
              x (t - τ) ≤ y (t - τ) := by
            intro t ht
            have h1 : t - τ ≤ (n : ℝ) * τ := by
              have h2 : min T (((n + 1 : ℕ) : ℝ) * τ) ≤ ((n + 1 : ℕ) : ℝ) * τ :=
                min_le_right _ _
              rw [hstep n] at h2
              have h3 : t ≤ (n : ℝ) * τ + τ := by
                have h4 := ht.2
                rw [hstep n] at h4
                linarith [h2]
              linarith
            by_cases h0 : t - τ ≤ 0
            · exact horder (t - τ) ⟨by linarith [h0n, ht.1], h0⟩
            · have hmem : t - τ ∈ Set.Icc 0 (min T ((n : ℝ) * τ)) := by
                rw [hmin]
                exact ⟨by linarith, h1⟩
              exact ih (t - τ) hmem
          have htT : ∀ t ∈ Set.Icc ((n : ℝ) * τ)
              (min T (((n + 1 : ℕ) : ℝ) * τ)), t ∈ Set.Icc 0 T := by
            intro t ht
            exact ⟨by linarith [h0n, ht.1], by linarith [ht.2, hbT]⟩
          have hxs : ∀ t ∈ Set.Icc ((n : ℝ) * τ) (min T (((n + 1 : ℕ) : ℝ) * τ)),
              HasDerivWithinAt x (fx t)
                (Set.Icc ((n : ℝ) * τ) (min T (((n + 1 : ℕ) : ℝ) * τ))) t := by
            intro t ht
            exact (hx t (htT t ht)).mono (fun s hs =>
              ⟨by linarith [h0n, hs.1], le_trans hs.2 hbT⟩)
          have hys : ∀ t ∈ Set.Icc ((n : ℝ) * τ) (min T (((n + 1 : ℕ) : ℝ) * τ)),
              HasDerivWithinAt y (f t (y t) (y (t - τ)))
                (Set.Icc ((n : ℝ) * τ) (min T (((n + 1 : ℕ) : ℝ) * τ))) t := by
            intro t ht
            exact (hy t (htT t ht)).mono (fun s hs =>
              ⟨by linarith [h0n, hs.1], le_trans hs.2 hbT⟩)
          have hsub' : ∀ t ∈ Set.Icc ((n : ℝ) * τ) (min T (((n + 1 : ℕ) : ℝ) * τ)),
              fx t ≤ f t (x t) (x (t - τ)) := by
            intro t ht
            exact hsub t (htT t ht)
          have hmemA : (n : ℝ) * τ ∈ Set.Icc 0 (min T ((n : ℝ) * τ)) :=
            ⟨by positivity, by simp [hmin]⟩
          have hstep' : ∀ t ∈ Set.Icc ((n : ℝ) * τ)
              (min T (((n + 1 : ℕ) : ℝ) * τ)), x t ≤ y t := by
            intro t ht
            have hbase : x ((n : ℝ) * τ) ≤ y ((n : ℝ) * τ) := ih _ hmemA
            exact delay_comparison_step_local
              (hlip := fun s hs v hv => hlip s (htT s hs) v hv) (hsup := hsup)
              (hkamke := fun s hs v u u' => hkamke s (htT s hs) v u u')
              (hdel := fun s hs u v v' => hdel s (htT s hs) u v v')
              (hx := hxs) (hsub := hsub') (hy := hys) (hdelayed := hdel')
              (hxK := fun s hs => hxK s (htT s hs))
              (hyK := fun s hs => hyK s (htT s hs))
              (hdelD := fun s hs => hdelD s (htT s hs)) hbase t ht
          by_cases hr' : r ≤ (n : ℝ) * τ
          · have hmem : r ∈ Set.Icc 0 (min T ((n : ℝ) * τ)) := by
              rw [hmin]
              exact ⟨hr.1, hr'⟩
            exact ih r hmem
          · exact hstep' r ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hN : min T (((Nat.ceil (T / τ) : ℕ) : ℝ) * τ) = T := by
    have h1 : T / τ ≤ (Nat.ceil (T / τ) : ℝ) := Nat.le_ceil _
    have h2 : T ≤ (Nat.ceil (T / τ) : ℝ) * τ := by
      calc T = T / τ * τ := by field_simp
        _ ≤ (Nat.ceil (T / τ) : ℝ) * τ := mul_le_mul_of_nonneg_right h1 hτ.le
    exact min_eq_left h2
  intro r hr
  have h1 := hall (Nat.ceil (T / τ)) r
  rw [hN] at h1
  exact h1 hr

end Dynamics
end CRNT
