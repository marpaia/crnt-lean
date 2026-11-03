import CRNT.Persistence.VariableRateFloor
import CRNT.Geometry.EndotacticStandard

/-!
# Bounded endotactic trajectories stay away from the boundary

Craciun, arXiv:1501.02860 v3, closing remark of §8 and footnote 126: bounded trajectories of
variable-k *endotactic* systems are persistent, because these systems embed in toric
differential inclusions (Craciun–Deshpande 2020).  This file proves that statement for the
standard notion of endotacticity (`EndotacticStd`) and rate constants varying in time inside
`[ε, 1/ε]`.

## Field condition

Fix a facet normal `a` and write `d r = ⟨a, y'_r - y_r⟩`.  Endotacticity with `w = -a` says: every
reaction with `d r < 0` has a partner `r'` with `d r' > 0` whose source has strictly smaller
`a`-potential.  The validity condition of the zero-separating region (`exists_zsh_uniform`) turns
"strictly smaller potential" into "monomial at least `exp δ` times larger".  So, if
`|d r| ≤ C · d r'` whenever `d r' > 0`, and `|R| · C · k_i ≤ exp δ · k_j`, every negative term
`u_r d_r` is at least `-1/|R|` times the positive part `T = ∑ u_r (d_r)⁺`, and
`⟨a, f(x)⟩ ≥ T - |R| · T / |R| = 0` (`dot_massActionField_nonneg_of_endotacticStd`).

The ratio constant `C` depends on the normals.  Weak reversibility avoided it by a layer-cake
argument; here it is handled by `exists_zsh_uniform`, whose finitely many normals do not depend on
the slack `δ`, so `C` can be computed first and `δ` chosen afterwards.

## Results

* `dot_massActionField_nonneg_of_endotacticStd` — the field condition.
* `endotacticStd_forward_floor_varK` — uniform positive floor for bounded forward solutions,
  time-dependent rates in `[ε, 1/ε]`.
* `endotacticStd_forward_floor_uniform`, `endotacticStd_forward_floor` — constant rates.
* `endotacticStd_conservative_confined_varK`,
  `endotacticStd_conservative_structurallyPersistent` — conservative endotactic networks are
  persistent (compact confinement), also with tempered rates.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT

open Finset Real

/-- For finitely many linear values `d i r`, a single constant bounds every ratio
`|d i r| / d i r'` with `d i r' > 0`. -/
theorem exists_ratio_bound {ι ρ : Type*} [Fintype ι] [Fintype ρ] (d : ι → ρ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i r r', 0 < d i r' → |d i r| ≤ C * d i r' := by
  refine ⟨∑ i, ∑ r, ∑ r', |d i r| / |d i r'|, ?_, fun i r r' hpos => ?_⟩
  · exact sum_nonneg fun i _ => sum_nonneg fun r _ => sum_nonneg fun r' _ =>
      div_nonneg (abs_nonneg _) (abs_nonneg _)
  · have hterm : |d i r| / |d i r'| ≤ ∑ i, ∑ r, ∑ r', |d i r| / |d i r'| := by
      have h1 : |d i r| / |d i r'| ≤ ∑ r', |d i r| / |d i r'| :=
        single_le_sum (f := fun r' => |d i r| / |d i r'|)
          (fun _ _ => div_nonneg (abs_nonneg _) (abs_nonneg _)) (mem_univ r')
      have h2 : ∑ r', |d i r| / |d i r'| ≤ ∑ r, ∑ r', |d i r| / |d i r'| :=
        single_le_sum (f := fun r => ∑ r', |d i r| / |d i r'|)
          (fun _ _ => sum_nonneg fun _ _ => div_nonneg (abs_nonneg _) (abs_nonneg _))
          (mem_univ r)
      have h3 : ∑ r, ∑ r', |d i r| / |d i r'| ≤ ∑ i, ∑ r, ∑ r', |d i r| / |d i r'| :=
        single_le_sum (f := fun i => ∑ r, ∑ r', |d i r| / |d i r'|)
          (fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
            div_nonneg (abs_nonneg _) (abs_nonneg _)) (mem_univ i)
      linarith
    rw [abs_of_pos hpos] at hterm
    rwa [div_le_iff₀ hpos] at hterm

namespace Network

open CRNT.Persistence CRNT.PolyhedralBarrier

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Endotactic field condition.** For a network that is endotactic in the standard sense, a
positive state `x`, and a normal `a` satisfying the validity condition of `exists_zsh` with slack
`δ`, the mass-action field has nonnegative component along `a`, provided the ratios
`|⟨a, y'_r - y_r⟩| / ⟨a, y'_{r'} - y_{r'}⟩` are at most `C` and `|R| · C · k_i ≤ exp δ · k_j`. -/
theorem dot_massActionField_nonneg_of_endotacticStd (N : Network S) (κ : N.RateConstants)
    (hend : N.EndotacticStd) {x : Concentration S} (hx : x.Positive) (a : S → ℝ) (δ C : ℝ)
    (hC : ∀ r r' : N.R, 0 < ∑ s, a s * N.reactionVector r' s →
      |∑ s, a s * N.reactionVector r s| ≤ C * ∑ s, a s * N.reactionVector r' s)
    (hδ : ∀ i j : N.R, (Fintype.card N.R : ℝ) * C * κ.k i ≤ exp δ * κ.k j)
    (hvalid : ∀ c ∈ N.complexes, ∀ c' ∈ N.complexes,
      ∑ s, a s * ((c s : ℝ) - c' s) < 0 → δ ≤ ∑ s, ((c s : ℝ) - c' s) * log (x s)) :
    0 ≤ ∑ s, a s * N.massActionVectorField κ x s := by
  set d : N.R → ℝ := fun r => ∑ s, a s * N.reactionVector r s with hd
  set u : N.R → ℝ := fun r => N.massActionRate κ r x with hu
  have hu0 : ∀ r, 0 ≤ u r := fun r => N.massActionRate_nonneg κ r hx.nonnegative
  have hdot : ∑ s, a s * N.massActionVectorField κ x s = ∑ r, u r * d r := by
    simp only [massActionVectorField_apply, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun r _ => ?_
    simp only [hu, hd]
    rw [mul_sum]
    exact sum_congr rfl fun s _ => by ring
  rw [hdot]
  set T : ℝ := ∑ r, u r * max (d r) 0 with hT
  have hT0 : 0 ≤ T := sum_nonneg fun r _ => mul_nonneg (hu0 r) (le_max_right _ _)
  set n : ℝ := (Fintype.card N.R : ℝ) with hn
  -- every negative term is at least `-T / |R|`
  have hneg : ∀ r, -T ≤ n * (u r * min (d r) 0) := by
    intro r
    by_cases hr : 0 ≤ d r
    · rw [min_eq_right hr, mul_zero, mul_zero]; linarith
    · push Not at hr
      rw [min_eq_left hr.le]
      -- the dominating reaction
      have hw : 0 < N.wRate (fun s => -a s) r := by
        have : N.wRate (fun s => -a s) r = -d r := by
          simp only [wRate, dotProduct, hd, neg_mul, sum_neg_distrib]
        rw [this]; linarith
      obtain ⟨r', hr'neg, hr'val⟩ := hend _ r hw
      have hdr' : 0 < d r' := by
        have : N.wRate (fun s => -a s) r' = -d r' := by
          simp only [wRate, dotProduct, hd, neg_mul, sum_neg_distrib]
        rw [this] at hr'neg; linarith
      have hpot : ∑ s, a s * (((N.reaction r').source s : ℝ) - (N.reaction r).source s) < 0 := by
        have e : ∑ s, a s * (((N.reaction r').source s : ℝ) - (N.reaction r).source s) =
            -(N.wValue (fun s => -a s) r') + N.wValue (fun s => -a s) r := by
          simp only [wValue, dotProduct, exponentVector, neg_mul, sum_neg_distrib, neg_neg]
          rw [← sum_neg_distrib, ← sum_add_distrib]
          exact sum_congr rfl fun s _ => by ring
        rw [e]; linarith
      have hv := hvalid _ (N.source_mem_complexes r') _ (N.source_mem_complexes r) hpot
      have hm : exp δ * (N.reaction r).source.massActionMonomial x ≤
          (N.reaction r').source.massActionMonomial x := by
        rw [massActionMonomial_eq_exp hx, massActionMonomial_eq_exp hx, ← exp_add]
        apply exp_le_exp.mpr
        have : ∑ s, (((N.reaction r').source s : ℝ) - (N.reaction r).source s) * log (x s) =
            ∑ s, ((N.reaction r').source s : ℝ) * log (x s) -
              ∑ s, ((N.reaction r).source s : ℝ) * log (x s) := by
          rw [← sum_sub_distrib]; exact sum_congr rfl fun s _ => by ring
        linarith
      have hmono0 : 0 ≤ (N.reaction r).source.massActionMonomial x :=
        Complex.massActionMonomial_nonneg hx.nonnegative _
      have hkr := (κ.positive r).le
      have hkr' := (κ.positive r').le
      have hratio := hC r r' hdr'
      rw [abs_of_neg hr] at hratio
      have hstep : n * (u r * (-d r)) ≤ u r' * d r' := by
        simp only [hu, massActionRate]
        calc n * (κ.k r * (N.reaction r).source.massActionMonomial x * (-d r))
            ≤ n * (κ.k r * (N.reaction r).source.massActionMonomial x * (C * d r')) := by
              have : 0 ≤ n := Nat.cast_nonneg _
              have := mul_nonneg hkr hmono0
              gcongr
          _ = (n * C * κ.k r) * ((N.reaction r).source.massActionMonomial x * d r') := by ring
          _ ≤ (exp δ * κ.k r') * ((N.reaction r).source.massActionMonomial x * d r') :=
              mul_le_mul_of_nonneg_right (hδ r r') (mul_nonneg hmono0 hdr'.le)
          _ = κ.k r' * d r' * (exp δ * (N.reaction r).source.massActionMonomial x) := by ring
          _ ≤ κ.k r' * d r' * (N.reaction r').source.massActionMonomial x :=
              mul_le_mul_of_nonneg_left hm (mul_nonneg hkr' hdr'.le)
          _ = κ.k r' * (N.reaction r').source.massActionMonomial x * d r' := by ring
      have hle : u r' * d r' ≤ T := by
        have : u r' * d r' = u r' * max (d r') 0 := by rw [max_eq_left hdr'.le]
        rw [this]
        exact single_le_sum (f := fun r => u r * max (d r) 0)
          (fun r _ => mul_nonneg (hu0 r) (le_max_right _ _)) (mem_univ r')
      nlinarith
  -- sum up
  have hsplit : ∑ r, u r * d r = T + ∑ r, u r * min (d r) 0 := by
    rw [hT, ← sum_add_distrib]
    refine sum_congr rfl fun r _ => ?_
    rw [← mul_add, max_add_min, add_zero]
  rw [hsplit]
  rcases isEmpty_or_nonempty N.R with hR | hR
  · simp [hT]
  · have hnpos : 0 < n := by rw [hn]; exact_mod_cast Fintype.card_pos
    have hsum : -(n * T) ≤ n * ∑ r, u r * min (d r) 0 := by
      have h1 := sum_le_sum (s := (univ : Finset N.R)) fun r _ => hneg r
      have h2 : ∑ r : N.R, -T = -(n * T) := by
        rw [sum_const, card_univ, nsmul_eq_mul, hn]; ring
      rw [h2, ← mul_sum] at h1
      exact h1
    have : -T ≤ ∑ r, u r * min (d r) 0 := by
      by_contra hc
      push Not at hc
      have := mul_lt_mul_of_pos_left hc hnpos
      linarith
    linarith

theorem half_le_dot_massActionField_of_endotacticStd (N : Network S) (κ : N.RateConstants)
    (hend : N.EndotacticStd) {x : Concentration S} (hx : x.Positive) (a : S → ℝ) (δ C : ℝ)
    (hC : ∀ r r' : N.R, 0 < ∑ s, a s * N.reactionVector r' s →
      |∑ s, a s * N.reactionVector r s| ≤ C * ∑ s, a s * N.reactionVector r' s)
    (hδ : ∀ i j : N.R, 2 * (Fintype.card N.R : ℝ) * C * κ.k i ≤ exp δ * κ.k j)
    (hvalid : ∀ c ∈ N.complexes, ∀ c' ∈ N.complexes,
      ∑ s, a s * ((c s : ℝ) - c' s) < 0 → δ ≤ ∑ s, ((c s : ℝ) - c' s) * log (x s)) :
    (∑ r, N.massActionRate κ r x * max (∑ s, a s * N.reactionVector r s) 0) / 2 ≤
      ∑ s, a s * N.massActionVectorField κ x s := by
  set d : N.R → ℝ := fun r => ∑ s, a s * N.reactionVector r s with hd
  set u : N.R → ℝ := fun r => N.massActionRate κ r x with hu
  have hu0 : ∀ r, 0 ≤ u r := fun r => N.massActionRate_nonneg κ r hx.nonnegative
  have hdot : ∑ s, a s * N.massActionVectorField κ x s = ∑ r, u r * d r := by
    simp only [massActionVectorField_apply, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun r _ => ?_
    simp only [hu, hd]
    rw [mul_sum]
    exact sum_congr rfl fun s _ => by ring
  rw [hdot]
  set T : ℝ := ∑ r, u r * max (d r) 0 with hT
  have hT0 : 0 ≤ T := sum_nonneg fun r _ => mul_nonneg (hu0 r) (le_max_right _ _)
  set n : ℝ := (Fintype.card N.R : ℝ) with hn
  -- every negative term is at least `-T / |R|`
  have hneg : ∀ r, -T ≤ 2 * n * (u r * min (d r) 0) := by
    intro r
    by_cases hr : 0 ≤ d r
    · rw [min_eq_right hr, mul_zero, mul_zero]; linarith
    · push Not at hr
      rw [min_eq_left hr.le]
      -- the dominating reaction
      have hw : 0 < N.wRate (fun s => -a s) r := by
        have : N.wRate (fun s => -a s) r = -d r := by
          simp only [wRate, dotProduct, hd, neg_mul, sum_neg_distrib]
        rw [this]; linarith
      obtain ⟨r', hr'neg, hr'val⟩ := hend _ r hw
      have hdr' : 0 < d r' := by
        have : N.wRate (fun s => -a s) r' = -d r' := by
          simp only [wRate, dotProduct, hd, neg_mul, sum_neg_distrib]
        rw [this] at hr'neg; linarith
      have hpot : ∑ s, a s * (((N.reaction r').source s : ℝ) - (N.reaction r).source s) < 0 := by
        have e : ∑ s, a s * (((N.reaction r').source s : ℝ) - (N.reaction r).source s) =
            -(N.wValue (fun s => -a s) r') + N.wValue (fun s => -a s) r := by
          simp only [wValue, dotProduct, exponentVector, neg_mul, sum_neg_distrib, neg_neg]
          rw [← sum_neg_distrib, ← sum_add_distrib]
          exact sum_congr rfl fun s _ => by ring
        rw [e]; linarith
      have hv := hvalid _ (N.source_mem_complexes r') _ (N.source_mem_complexes r) hpot
      have hm : exp δ * (N.reaction r).source.massActionMonomial x ≤
          (N.reaction r').source.massActionMonomial x := by
        rw [massActionMonomial_eq_exp hx, massActionMonomial_eq_exp hx, ← exp_add]
        apply exp_le_exp.mpr
        have : ∑ s, (((N.reaction r').source s : ℝ) - (N.reaction r).source s) * log (x s) =
            ∑ s, ((N.reaction r').source s : ℝ) * log (x s) -
              ∑ s, ((N.reaction r).source s : ℝ) * log (x s) := by
          rw [← sum_sub_distrib]; exact sum_congr rfl fun s _ => by ring
        linarith
      have hmono0 : 0 ≤ (N.reaction r).source.massActionMonomial x :=
        Complex.massActionMonomial_nonneg hx.nonnegative _
      have hkr := (κ.positive r).le
      have hkr' := (κ.positive r').le
      have hratio := hC r r' hdr'
      rw [abs_of_neg hr] at hratio
      have hstep : 2 * n * (u r * (-d r)) ≤ u r' * d r' := by
        simp only [hu, massActionRate]
        calc 2 * n * (κ.k r * (N.reaction r).source.massActionMonomial x * (-d r))
            ≤ 2 * n * (κ.k r * (N.reaction r).source.massActionMonomial x * (C * d r')) := by
              have : 0 ≤ n := Nat.cast_nonneg _
              have := mul_nonneg hkr hmono0
              gcongr
          _ = (2 * n * C * κ.k r) * ((N.reaction r).source.massActionMonomial x * d r') := by ring
          _ ≤ (exp δ * κ.k r') * ((N.reaction r).source.massActionMonomial x * d r') :=
              mul_le_mul_of_nonneg_right (hδ r r') (mul_nonneg hmono0 hdr'.le)
          _ = κ.k r' * d r' * (exp δ * (N.reaction r).source.massActionMonomial x) := by ring
          _ ≤ κ.k r' * d r' * (N.reaction r').source.massActionMonomial x :=
              mul_le_mul_of_nonneg_left hm (mul_nonneg hkr' hdr'.le)
          _ = κ.k r' * (N.reaction r').source.massActionMonomial x * d r' := by ring
      have hle : u r' * d r' ≤ T := by
        have : u r' * d r' = u r' * max (d r') 0 := by rw [max_eq_left hdr'.le]
        rw [this]
        exact single_le_sum (f := fun r => u r * max (d r) 0)
          (fun r _ => mul_nonneg (hu0 r) (le_max_right _ _)) (mem_univ r')
      nlinarith
  -- sum up
  have hsplit : ∑ r, u r * d r = T + ∑ r, u r * min (d r) 0 := by
    rw [hT, ← sum_add_distrib]
    refine sum_congr rfl fun r _ => ?_
    rw [← mul_add, max_add_min, add_zero]
  rw [hsplit]
  rcases isEmpty_or_nonempty N.R with hR | hR
  · simp [hT]
  · have hnpos : 0 < n := by rw [hn]; exact_mod_cast Fintype.card_pos
    have hsum : -(n * T) ≤ 2 * n * ∑ r, u r * min (d r) 0 := by
      have h1 := sum_le_sum (s := (univ : Finset N.R)) fun r _ => hneg r
      have h2 : ∑ r : N.R, -T = -(n * T) := by
        rw [sum_const, card_univ, nsmul_eq_mul, hn]; ring
      rw [h2, ← mul_sum] at h1
      exact h1
    have : -T ≤ 2 * ∑ r, u r * min (d r) 0 := by
      by_contra hc
      push Not at hc
      have := mul_lt_mul_of_pos_left hc hnpos
      linarith
    linarith


/-- **Strict endotactic field condition.** With twice the slack, the component of the field along
a normal `a` is positive as soon as some reaction vector is not orthogonal to `a`. -/
theorem dot_massActionField_pos_of_endotacticStd (N : Network S) (κ : N.RateConstants)
    (hend : N.EndotacticStd) {x : Concentration S} (hx : x.Positive) (a : S → ℝ) (δ C : ℝ)
    (hC : ∀ r r' : N.R, 0 < ∑ s, a s * N.reactionVector r' s →
      |∑ s, a s * N.reactionVector r s| ≤ C * ∑ s, a s * N.reactionVector r' s)
    (hδ : ∀ i j : N.R, 2 * (Fintype.card N.R : ℝ) * C * κ.k i ≤ exp δ * κ.k j)
    (hvalid : ∀ c ∈ N.complexes, ∀ c' ∈ N.complexes,
      ∑ s, a s * ((c s : ℝ) - c' s) < 0 → δ ≤ ∑ s, ((c s : ℝ) - c' s) * log (x s))
    (hne : ∃ r : N.R, ∑ s, a s * N.reactionVector r s ≠ 0) :
    0 < ∑ s, a s * N.massActionVectorField κ x s := by
  have h := N.half_le_dot_massActionField_of_endotacticStd κ hend hx a δ C hC hδ hvalid
  -- a reaction increasing `⟨a, ·⟩`
  obtain ⟨r, hr⟩ : ∃ r : N.R, 0 < ∑ s, a s * N.reactionVector r s := by
    obtain ⟨r, hr⟩ := hne
    rcases lt_or_gt_of_ne hr with hneg | hpos
    · have hw : 0 < N.wRate (fun s => -a s) r := by
        have : N.wRate (fun s => -a s) r = -∑ s, a s * N.reactionVector r s := by
          simp only [wRate, dotProduct, neg_mul, sum_neg_distrib]
        rw [this]; linarith
      obtain ⟨r', hr'neg, -⟩ := hend _ r hw
      refine ⟨r', ?_⟩
      have : N.wRate (fun s => -a s) r' = -∑ s, a s * N.reactionVector r' s := by
        simp only [wRate, dotProduct, neg_mul, sum_neg_distrib]
      rw [this] at hr'neg; linarith
    · exact ⟨r, hpos⟩
  have hu : 0 < N.massActionRate κ r x := by
    unfold massActionRate
    exact mul_pos (κ.positive r) (by
      rw [massActionMonomial_eq_exp hx]; exact exp_pos _)
  have hterm : N.massActionRate κ r x * max (∑ s, a s * N.reactionVector r s) 0 ≤
      ∑ r, N.massActionRate κ r x * max (∑ s, a s * N.reactionVector r s) 0 :=
    single_le_sum (f := fun r => N.massActionRate κ r x * max (∑ s, a s * N.reactionVector r s) 0)
      (fun r _ => mul_nonneg (N.massActionRate_nonneg κ r hx.nonnegative) (le_max_right _ _))
      (mem_univ r)
  have hpos : 0 < N.massActionRate κ r x * max (∑ s, a s * N.reactionVector r s) 0 := by
    rw [max_eq_left hr.le]; exact mul_pos hu hr
  linarith

/-- A slack `δ` with `|R| · C · k_i ≤ exp δ · k_j` for every rate vector in `[ε, 1/ε]`. -/
theorem exists_slack_varK_ratio (N : Network S) {ε : ℝ} (hε : 0 < ε) (C : ℝ) :
    ∃ δ : ℝ, ∀ κ : N.RateConstants, (∀ r, ε ≤ κ.k r ∧ κ.k r ≤ 1 / ε) →
      ∀ i j : N.R, (Fintype.card N.R : ℝ) * C * κ.k i ≤ exp δ * κ.k j := by
  set n : ℝ := (Fintype.card N.R : ℝ)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  refine ⟨n * |C| / ε ^ 2, fun κ hκ i j => ?_⟩
  have hki := (κ.positive i).le
  have h0 : n * C * κ.k i ≤ n * |C| * κ.k i :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self C) hn) hki
  have h1 : n * |C| * κ.k i ≤ n * |C| * (1 / ε) :=
    mul_le_mul_of_nonneg_left (hκ i).2 (mul_nonneg hn (abs_nonneg C))
  have h2 : n * |C| / ε ^ 2 ≤ exp (n * |C| / ε ^ 2) := by
    linarith [add_one_le_exp (n * |C| / ε ^ 2)]
  have h3 : n * |C| * (1 / ε) = n * |C| / ε ^ 2 * ε := by field_simp
  have h4 : n * |C| / ε ^ 2 * ε ≤ exp (n * |C| / ε ^ 2) * κ.k j :=
    mul_le_mul h2 (hκ j).1 hε.le (exp_pos _).le
  linarith

/-- Positive rate constants lie in some interval `[ε, 1/ε]`. -/
theorem exists_rate_bounds (N : Network S) (κ : N.RateConstants) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r, ε ≤ κ.k r ∧ κ.k r ≤ 1 / ε := by
  set K : ℝ := ∑ r, (κ.k r + 1 / κ.k r) with hKdef
  have hK0 : 0 ≤ K := sum_nonneg fun r _ =>
    add_nonneg (κ.positive r).le (one_div_pos.mpr (κ.positive r)).le
  refine ⟨1 / (1 + K), by positivity, fun r => ?_⟩
  have hk := κ.positive r
  have hle : κ.k r + 1 / κ.k r ≤ K :=
    single_le_sum (f := fun r => κ.k r + 1 / κ.k r) (fun r _ =>
      add_nonneg (κ.positive r).le (one_div_pos.mpr (κ.positive r)).le) (mem_univ r)
  have hinv : 0 < 1 / κ.k r := one_div_pos.mpr hk
  constructor
  · rw [div_le_iff₀ (by positivity)]
    have : 1 = κ.k r * (1 / κ.k r) := by field_simp
    nlinarith
  · rw [one_div_one_div]; linarith

/-- **Variable-k endotactic floor.** For a network that is endotactic in the standard sense,
with rate constants varying in time inside `[ε, 1/ε]`, every forward solution from `x₀` bounded
by `M` has a positive lower bound depending only on `x₀`, `M` and `ε` (Craciun, arXiv:1501.02860
v3, §8, footnote 126; Craciun–Deshpande 2020). -/
theorem endotacticStd_forward_floor_varK (N : Network S) (κ : ℝ → N.RateConstants)
    (hend : N.EndotacticStd) {ε : ℝ} (hε : 0 < ε)
    (hκ : ∀ t r, ε ≤ (κ t).k r ∧ (κ t).k r ≤ 1 / ε)
    {x₀ : Concentration S} (hx₀ : x₀.Positive) (M : ℝ) :
    ∃ η, 0 < η ∧ ∀ γ : ℝ → Concentration S, γ 0 = x₀ →
      (∀ t : ℝ, 0 ≤ t → HasDerivAt γ (N.massActionVectorField (κ t) (γ t)) t) →
      (∀ t : ℝ, 0 ≤ t → ∀ s, γ t s ≤ M) → ∀ t : ℝ, 0 ≤ t → ∀ s, η ≤ γ t s := by
  set n := Fintype.card S with hn
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · refine ⟨1, one_pos, fun _ _ _ _ t _ s => ?_⟩
    exact absurd (Fintype.card_pos_iff.mpr ⟨s⟩) (by omega)
  obtain ⟨e⟩ : Nonempty (S ≃ Fin n) := ⟨Fintype.equivFin S⟩
  obtain ⟨M', hM'1, hMM'⟩ : ∃ M', 1 ≤ M' ∧ M ≤ M' := ⟨max M 1, le_max_right _ _, le_max_left _ _⟩
  -- complex differences, closed under permutations
  obtain ⟨D, hD⟩ : ∃ D : Complex S × Complex S → Fin n → ℝ,
      D = fun p q => ((p.1 (e.symm q) : ℝ) - p.2 (e.symm q)) := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : Finset (Fin n → ℝ), H =
      (Finset.univ : Finset (Equiv.Perm (Fin n))).biUnion
        fun ρ => (N.complexes ×ˢ N.complexes).image fun p => D p ∘ ρ := ⟨_, rfl⟩
  have hsym : ∀ h ∈ H, ∀ ρ : Equiv.Perm (Fin n), h ∘ ρ ∈ H := by
    intro h hh ρ'
    rw [hH] at hh ⊢
    simp only [mem_biUnion, mem_univ, true_and, mem_image] at hh ⊢
    obtain ⟨ρ, p, hp, rfl⟩ := hh
    exact ⟨ρ * ρ', p, hp, by funext q; simp⟩
  have hDmem : ∀ c ∈ N.complexes, ∀ c' ∈ N.complexes, D (c, c') ∈ H := by
    intro c hc c' hc'
    rw [hH]
    simp only [mem_biUnion, mem_univ, true_and, mem_image]
    exact ⟨1, (c, c'), mem_product.mpr ⟨hc, hc'⟩, by funext q; simp⟩
  -- transport to `Fin n`
  have htr : ∀ (a x : S → ℝ), fdot (a ∘ e.symm) (x ∘ e.symm) = ∑ s, a s * x s := by
    intro a x
    unfold fdot
    exact Equiv.sum_comp e.symm (fun s => a s * x s)
  have htrlog : ∀ (h : Fin n → ℝ) (x : S → ℝ),
      ∑ q, h q * log (x (e.symm q)) = ∑ s, h (e s) * log (x s) := by
    intro h x
    rw [← Equiv.sum_comp e (fun q => h q * log (x (e.symm q)))]
    simp
  -- the normals, fixed before the slack
  obtain ⟨ι, hFι, hNι, a, hzsh⟩ := exists_zsh_uniform (by omega : 1 ≤ n) H hsym
  have := hFι
  have := hNι
  set aS : ι → S → ℝ := fun i s => a i (e s) with haS
  have hdotS : ∀ i (x : S → ℝ), fdot (a i) (x ∘ e.symm) = ∑ s, aS i s * x s := by
    intro i x
    have : a i = aS i ∘ e.symm := by funext q; simp [haS]
    rw [this, htr]
  -- the ratio constant and the slack
  obtain ⟨C, -, hC⟩ := exists_ratio_bound (fun (i : ι) (r : N.R) => ∑ s, aS i s * N.reactionVector r s)
  obtain ⟨δ, hδ⟩ := N.exists_slack_varK_ratio hε C
  obtain ⟨b, R', η, hR', hη, hstart, hfloor, -, hvalid⟩ :=
    hzsh δ M' hM'1 (x₀ ∘ e.symm) (fun q => hx₀ _)
  refine ⟨η, hη, fun γ hγx hsol hbdd => ?_⟩
  have hγ0 : (γ 0).Positive := hγx ▸ hx₀
  have hpos := N.orbit_pos_forward_varK κ (one_div_pos.mpr hε).le (fun t r => (hκ t r).2) hγ0
    (fun t ht _ => hbdd t ht) hsol
  set L : ι → ((S → ℝ) →L[ℝ] ℝ) := fun i =>
    -∑ s, aS i s • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s with hL
  have hLapp : ∀ i (x : S → ℝ), L i x = -∑ s, aS i s * x s := by
    intro i x
    simp [hL, smul_eq_mul]
  set b' : ι → ℝ := fun i => -b i with hb'
  have hγcont : ContinuousOn γ (Set.Ici 0) := fun t ht =>
    (hsol t ht).continuousAt.continuousWithinAt
  have hinv := barrier_le_of_local_descent_in_band (L := L) (b := b') (R := 0) (R' := R') hR'
    hγcont hsol (by
      rw [barrier_le_iff]
      intro i
      rw [hLapp, hb']
      have := hstart i
      rw [← hγx] at this
      rw [hdotS] at this
      linarith) (by
      intro t ht hlev hband i hact
      set x := γ t with hx
      set σ := barrier L b' x with hσ
      have hall : ∀ i', b i' - σ ≤ fdot (a i') (x ∘ e.symm) := by
        intro i'
        have := le_barrier L b' x i'
        rw [hLapp, hdotS] at *
        simp only [hb'] at this
        linarith
      have hacteq : fdot (a i) (x ∘ e.symm) = b i - σ := by
        rw [hLapp] at hact
        rw [hdotS]
        simp only [hb'] at hact
        linarith
      have hv := hvalid σ hlev hband (x ∘ e.symm) (fun q => hpos t ht _)
        (fun q => le_trans (hbdd t ht _) hMM') hall i hacteq
      have hnn := N.dot_massActionField_nonneg_of_endotacticStd (κ t) hend (hpos t ht) (aS i) δ C
        (fun r r' h => hC i r r' h) (hδ (κ t) (fun r => hκ t r)) (by
        intro c hc c' hc' hneg
        have hmem := hDmem c hc c' hc'
        have hdot : fdot (a i) (D (c, c')) = ∑ s, aS i s * ((c s : ℝ) - c' s) := by
          have : D (c, c') = (fun s => ((c s : ℝ) - c' s)) ∘ e.symm := by
            rw [hD]; rfl
          rw [this, hdotS]
        have := hv (D (c, c')) hmem (by rw [hdot]; exact hneg)
        simp only [Function.comp_apply] at this
        rw [htrlog, hD] at this
        simpa using this)
      rw [hLapp]
      linarith)
  intro t ht s
  have hb := hinv t ht
  rw [barrier_le_iff] at hb
  have hin : ∀ i, b i ≤ fdot (a i) (γ t ∘ e.symm) := by
    intro i
    have := hb i
    rw [hLapp, hb'] at this
    rw [hdotS]; linarith
  have := hfloor _ hin (e s)
  simpa using this

/-- **Uniform endotactic floor** for constant rate constants. -/
theorem endotacticStd_forward_floor_uniform (N : Network S) (κ : N.RateConstants)
    (hend : N.EndotacticStd) {x₀ : Concentration S} (hx₀ : x₀.Positive) (M : ℝ) :
    ∃ η, 0 < η ∧ ∀ γ : ℝ → Concentration S, γ 0 = x₀ →
      (∀ t : ℝ, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t) →
      (∀ t : ℝ, 0 ≤ t → ∀ s, γ t s ≤ M) → ∀ t : ℝ, 0 ≤ t → ∀ s, η ≤ γ t s := by
  obtain ⟨ε, hε, hb⟩ := N.exists_rate_bounds κ
  exact N.endotacticStd_forward_floor_varK (fun _ => κ) hend hε (fun _ r => hb r) hx₀ M

/-- **Bounded endotactic trajectories stay away from the boundary.** For a network that is
endotactic in the standard sense and arbitrary positive rate constants, every forward solution
from a positive state that is bounded above has all coordinates bounded below by a positive
constant for all `t ≥ 0`. -/
theorem endotacticStd_forward_floor (N : Network S) (κ : N.RateConstants)
    (hend : N.EndotacticStd)
    {γ : ℝ → Concentration S} (hγ0 : (γ 0).Positive)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    {M : ℝ} (hbdd : ∀ t : ℝ, 0 ≤ t → ∀ s, γ t s ≤ M) :
    ∃ η, 0 < η ∧ ∀ t : ℝ, 0 ≤ t → ∀ s, η ≤ γ t s := by
  obtain ⟨η, hη, h⟩ := N.endotacticStd_forward_floor_uniform κ hend hγ0 M
  exact ⟨η, hη, h γ rfl hsol hbdd⟩

/-- **Conservative endotactic networks with variable rates are persistent.** For rate constants
varying in time inside `[ε, 1/ε]`, every forward solution from a positive `x₀` stays in one compact
set of positive states. -/
theorem endotacticStd_conservative_confined_varK (N : Network S) (κ : ℝ → N.RateConstants)
    (hend : N.EndotacticStd) (hcons : N.IsConservative) {ε : ℝ} (hε : 0 < ε)
    (hκ : ∀ t r, ε ≤ (κ t).k r ∧ (κ t).k r ≤ 1 / ε)
    {x₀ : Concentration S} (hx₀ : x₀.Positive) :
    ∃ K₀ : Set (Concentration S), IsCompact K₀ ∧ (∀ y ∈ K₀, y.Positive) ∧
      ∀ Γ : ℝ → Concentration S, Γ 0 = x₀ →
        (∀ t : ℝ, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField (κ t) (Γ t)) t) →
        ∀ t : ℝ, 0 ≤ t → Γ t ∈ K₀ := by
  obtain ⟨w, hw⟩ := hcons
  set W := weightedTotal w x₀
  set B : ℝ := ∑ s, W / w s
  have hW : 0 ≤ W := Finset.sum_nonneg fun s _ => mul_nonneg (hw.2 s).le (hx₀ s).le
  have hbound : ∀ Γ : ℝ → Concentration S, Γ 0 = x₀ →
      (∀ t : ℝ, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField (κ t) (Γ t)) t) →
      ∀ t : ℝ, 0 ≤ t → ∀ s, Γ t s ≤ B := by
    intro Γ hΓ0 hΓd
    have hbnn : ∀ t : ℝ, 0 ≤ t → (Γ t).Nonnegative → ∀ s, Γ t s ≤ B := by
      intro t ht hnn s
      have hc : N.StoichCompatible (Γ 0) (Γ t) :=
        N.sub_mem_stoichSubspace_of_solution_varK κ ht fun τ hτ => hΓd τ hτ.1
      rw [hΓ0] at hc
      have h1 := N.coordinate_le_of_strictPSemiflow hw hx₀.nonnegative hnn hc s
      have h2 : W / w s ≤ B :=
        Finset.single_le_sum (f := fun s => W / w s) (fun s _ => div_nonneg hW (hw.2 s).le)
          (Finset.mem_univ s)
      exact h1.trans h2
    have hpos := N.orbit_pos_forward_varK κ (one_div_pos.mpr hε).le (fun t r => (hκ t r).2)
      (hΓ0 ▸ hx₀) hbnn hΓd
    exact fun t ht => hbnn t ht (hpos t ht).nonnegative
  obtain ⟨η, hη, hfloor⟩ := N.endotacticStd_forward_floor_varK κ hend hε hκ hx₀ B
  refine ⟨Set.univ.pi fun _ => Set.Icc η B, isCompact_univ_pi fun _ => isCompact_Icc,
    fun y hy s => lt_of_lt_of_le hη (hy s (Set.mem_univ s)).1, fun Γ hΓ0 hΓd t ht => ?_⟩
  intro s _
  exact ⟨hfloor Γ hΓ0 hΓd (hbound Γ hΓ0 hΓd) t ht s, hbound Γ hΓ0 hΓd t ht s⟩

/-- **Conservative endotactic networks are persistent from every positive state.** -/
theorem endotacticStd_conservative_persistentFrom (N : Network S) (κ : N.RateConstants)
    (hend : N.EndotacticStd) (hcons : N.IsConservative) {x₀ : Concentration S}
    (hx₀ : x₀.Positive) : N.PersistentFrom κ x₀ := by
  obtain ⟨w, hw⟩ := hcons
  obtain ⟨B, hB⟩ := N.conservative_forward_bound κ hw hx₀
  obtain ⟨η, hη, hfloor⟩ := N.endotacticStd_forward_floor_uniform κ hend hx₀ B
  refine ⟨Set.univ.pi fun _ => Set.Icc η B, isCompact_univ_pi fun _ => isCompact_Icc,
    fun y hy s => lt_of_lt_of_le hη (hy s (Set.mem_univ s)).1, fun Γ hΓ0 hΓd t ht => ?_⟩
  intro s _
  exact ⟨hfloor Γ hΓ0 hΓd (hB Γ hΓ0 hΓd) t ht s, hB Γ hΓ0 hΓd t ht s⟩

/-- **Conservative endotactic networks are structurally persistent.** -/
theorem endotacticStd_conservative_structurallyPersistent (N : Network S)
    (hend : N.EndotacticStd) (hcons : N.IsConservative) : N.StructurallyPersistent :=
  fun κ _ hx₀ => N.endotacticStd_conservative_persistentFrom κ hend hcons hx₀

end Network
end CRNT
