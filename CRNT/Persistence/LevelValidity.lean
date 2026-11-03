import CRNT.Persistence.PathWalk
import CRNT.Persistence.LogConversion
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Validity of one level of the zero-separating region

For a block of `m + 1` coordinates `z₀ ≥ z₁ ≥ … ≥ z_m > 0` and a finite list `Hk` of vectors on
those coordinates, `level_validity` produces a blueprint tree and constants `κ, s₀ > 0` such
that, at scale `s < s₀`: whenever the path `P` attains the minimum of the facet values
`z₀ + val s t P' (z ∘ succ) ≥ c` (`c ∈ [s/2, s]`) and the box condition `z₀ ^ B ≤ z_m` holds,
then `z₀ ≤ 2s` and every `h ∈ Hk` with `⟨N_P, h⟩ < 0` satisfies
`κ · (-log z₀) ≤ ∑ h_i log z_i`, where `N_P = (1, basepoint of P)` is the facet normal.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Persistence

open Finset BTree Real Filter Topology

/-- The slice functional of a vector on `m + 1` coordinates. -/
def slice (h : ℕ → ℝ) : Aff := ⟨fun l => h (l + 1), h 0⟩

open Classical in
/-- The top arrangement: slices of vectors with some nonzero later coordinate, and walls. -/
noncomputable def Atop (m : ℕ) (Hk : List (ℕ → ℝ)) : List Aff :=
  (Hk.filter fun h => decide (∃ l ∈ range m, h (l + 1) ≠ 0)).map slice ++
    (List.range m).map wallFn

/-- The tower of projections below the top arrangement. -/
noncomputable def towerA (A0 : List Aff) (m : ℕ) : ℕ → List Aff
  | j => if j + 1 < m then proj (j + 1) (towerA A0 m (j + 1)) else A0
termination_by j => m - j

theorem towerA_eq (A0 : List Aff) (m j : ℕ) :
    towerA A0 m j = if j + 1 < m then proj (j + 1) (towerA A0 m (j + 1)) else A0 := by
  rw [towerA]

theorem wallFn_α_of_lt {i l : ℕ} (h : i < l) : (wallFn i).α l = 0 := by
  unfold wallFn
  split_ifs with h0
  · show (if l = 0 then (1:ℝ) else 0) = 0
    rw [if_neg (by omega)]
  · show (if l = i then (1:ℝ) else if l + 1 = i then -1 else 0) = 0
    rw [if_neg (by omega), if_neg (by omega)]

theorem wall_mem_towerA (A0 : List Aff) (m : ℕ) (hA : ∀ i, i < m → wallFn i ∈ A0) :
    ∀ r j, j + r + 1 = m → ∀ i, i ≤ j → wallFn i ∈ towerA A0 m j := by
  intro r
  induction r with
  | zero =>
      intro j hj i hi
      rw [towerA_eq, if_neg (by omega)]; exact hA i (by omega)
  | succ r ih =>
      intro j hj i hi
      rw [towerA_eq, if_pos (by omega)]
      exact mem_proj_of_vertical (ih (j + 1) (by omega) i (by omega)) (wallFn_α_of_lt (by omega))

theorem exists_towerOK (A0 : List Aff) (m : ℕ) (hA : ∀ i, i < m → wallFn i ∈ A0) :
    ∃ c L, TowerOK (towerA A0 m) m c L := by
  -- gap constants
  have hgap : ∀ j, ∃ c, 0 < c ∧ c ≤ 1 ∧ ∀ g ∈ towerA A0 m j, ∀ g' ∈ towerA A0 m j,
      (0 < Aff.norm1 j (Aff.diff j g g') → c ≤ Aff.norm1 j (Aff.diff j g g')) ∧
      ((Aff.diff j g g').c ≠ 0 → c ≤ |(Aff.diff j g g').c|) := fun j =>
    exists_gap_const j (towerA A0 m j)
  choose cj hcj using hgap
  have hsl : ∀ j, ∃ L, 1 ≤ L ∧ ∀ g ∈ (towerA A0 m j).filter (fun g => decide (g.α j ≠ 0)),
      Aff.norm1 j g / |g.α j| ≤ L := fun j => exists_ge_of_list _ _
  choose Lj hLj using hsl
  obtain ⟨c, hc, hc1, hcle⟩ := exists_pos_le_of_forall_pos (List.range m) cj
    (fun j _ => (hcj j).1)
  obtain ⟨L, hL, hLle⟩ := exists_ge_of_list (List.range m) Lj
  refine ⟨c, L, ⟨?_, ?_, hc, hc1, hL, ?_, ?_⟩⟩
  · intro j hj g hg
    rw [towerA_eq, if_pos hj]; exact hg
  · intro j hj
    exact wall_mem_towerA A0 m hA (m - j - 1) j (by omega) j le_rfl
  · intro j hj g hg g' hg'
    have hcj' := hcle j (by simpa using hj)
    obtain ⟨h1, h2⟩ := (hcj j).2.2 g hg g' hg'
    exact ⟨fun h => le_trans hcj' (h1 h), fun h => le_trans hcj' (h2 h)⟩
  · intro j hj g hg hv
    have hq := (hLj j).2 g (List.mem_filter.mpr ⟨hg, by simpa using hv⟩)
    have hLj' := hLle j (by simpa using hj)
    have hα : 0 < |g.α j| := abs_pos.mpr hv
    rw [div_le_iff₀ hα] at hq
    nlinarith

/-- Basepoint values along a path stay in `[0, Bβ]`. -/
theorem leafB_mem : ∀ {d : ℕ} (t : BTree d) (Bβ : ℝ) (j : ℕ) (b : ℕ → ℝ), GapsPos Bβ t →
    ∀ P, IsPath t P → ∀ l, j ≤ l → l < j + d → 0 ≤ leafB t j b P l ∧ leafB t j b P l ≤ Bβ
  | _, .leaf, _, _, _, _, _, _ => fun l h1 h2 => by omega
  | d + 1, .node n β lo hi sub, Bβ, j, b, hg, P, hP => by
      obtain ⟨i, rest, rfl, hin, hrest⟩ := hP
      intro l hl1 hl2
      rcases Nat.eq_or_lt_of_le hl1 with rfl | hlt
      · rw [leafB_apply_self]; exact hg.1 i hin
      · simp only [leafB]
        exact leafB_mem (sub i) Bβ (j + 1) _ (hg.2.2 i hin) rest hrest l (by omega) (by omega)

/-- The facet normal of a path dotted with a vector. -/
noncomputable def normalDot (m : ℕ) {d : ℕ} (t : BTree d) (P : List ℕ) (h : ℕ → ℝ) : ℝ :=
  h 0 + ∑ l ∈ range m, leafB t 0 (fun _ => 1) P l * h (l + 1)

theorem eventually_small {γ X : ℝ} (hγ : 0 < γ) (hX : 0 < X) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), s ^ γ < X := by
  have ht : Tendsto (fun s : ℝ => s ^ γ) (𝓝[>] 0) (𝓝 0) := by
    have := (continuousAt_rpow_const 0 γ (Or.inr hγ.le)).tendsto
    rw [zero_rpow hγ.ne'] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact ht.eventually (gt_mem_nhds hX)

theorem eventually_neglog_ge (X : ℝ) : ∀ᶠ s in 𝓝[>] (0:ℝ), X ≤ -log s := by
  have := tendsto_log_nhdsGT_zero.eventually (eventually_le_atBot (-X))
  exact this.mono fun s hs => by linarith

theorem level_validity (m : ℕ) (Hk : List (ℕ → ℝ)) (B : ℝ) (hB : 1 ≤ B) :
    ∃ t : BTree m, ∃ ρ0 : ℝ, 0 < ρ0 ∧ WF t 1 ρ0 ∧ GapsPos (B + 3) t ∧
    ∃ κ, 0 < κ ∧ ∃ s₀, 0 < s₀ ∧ s₀ < 1 / 4 ∧
    (∀ s, 0 < s → s < s₀ → ∀ P, IsPath t P → -s ≤ pathD s t P) ∧
    ∀ s, 0 < s → s < s₀ → ∀ c, s / 2 ≤ c → c ≤ s →
    ∀ z : ℕ → ℝ, (∀ i, 0 < z i) → (∀ i, i < m → z (i + 1) ≤ z i) → z 0 ^ B ≤ z m →
    (∀ P', IsPath t P' → c ≤ z 0 + BTree.val s t P' (fun l => z (l + 1))) →
    ∀ P, IsPath t P → z 0 + BTree.val s t P (fun l => z (l + 1)) = c →
    z 0 ≤ 2 * s ∧ ∀ h ∈ Hk, normalDot m t P h < 0 →
      κ * (-log (z 0)) ≤ ∑ i ∈ range (m + 1), h i * log (z i) := by
  have hm0 : m = 0 ∨ 1 ≤ m := by omega
  -- the constant for vectors with only a first coordinate
  obtain ⟨κ2, hκ2, _, hκ2le⟩ := exists_pos_le_of_forall_pos
    (Hk.filter fun h : ℕ → ℝ => decide (h 0 ≠ 0)) (fun h : ℕ → ℝ => |h 0|) (by
      intro h hh; exact abs_pos.mpr (by simpa using (List.mem_filter.mp hh).2))
  have hκ2' : ∀ h ∈ Hk, h 0 < 0 → κ2 ≤ -h 0 := by
    intro h hh hneg
    have := hκ2le h (List.mem_filter.mpr ⟨hh, by simpa using hneg.ne⟩)
    rwa [abs_of_neg hneg] at this
  rcases hm0 with rfl | hm
  · -- a single coordinate: the tree is a leaf
    refine ⟨BTree.leaf, 1, one_pos, trivial, trivial, κ2, hκ2, 1 / 8, by norm_num, by norm_num,
      fun s hs _ P _ => by simp [pathD]; linarith, ?_⟩
    intro s hs0 hs1 c hc1 hc2 z hz _ _ _ P hP hval
    have hP' : P = [] := hP
    subst hP'
    have hz0 : z 0 = c := by simpa [BTree.val] using hval
    have hlog : log (z 0) < 0 := log_neg (hz 0) (by rw [hz0]; linarith)
    refine ⟨by rw [hz0]; linarith, fun h hh hneg => ?_⟩
    simp only [normalDot, range_zero, sum_empty, add_zero] at hneg
    simp only [zero_add, range_one, sum_singleton]
    have h1 := hκ2' h hh hneg
    have h2 : 0 < -log (z 0) := by linarith
    calc κ2 * -log (z 0) ≤ -h 0 * -log (z 0) := mul_le_mul_of_nonneg_right h1 h2.le
      _ = h 0 * log (z 0) := by ring
  -- the tower and the tree
  set A0 := Atop m Hk with hA0
  have hwalls : ∀ i, i < m → wallFn i ∈ A0 := by
    intro i hi
    simp only [hA0, Atop, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inr ⟨i, hi, rfl⟩
  obtain ⟨c0, L, hT⟩ := exists_towerOK A0 m hwalls
  set A := towerA A0 m with hAdef
  have hc := hT.c_pos; have hL := hT.L_ge
  set b0 : ℕ → ℝ := fun _ => 1 with hb0
  set ρ0 := nu c0 L m * 1 with hρ0def
  have hρ0 : 0 < ρ0 := by rw [hρ0def, mul_one]; exact nu_pos hc hL m
  have hwv : wallVal 0 b0 = 1 := by simp [wallVal]
  obtain ⟨hWF, hPr, hGP, hLP⟩ := build_spec hT hB hm m 0 (by omega) b0 1 ρ0
    (lfsGe_zero _ _ _) one_pos le_rfl hρ0.le le_rfl (by rw [hwv]) (by rw [hwv]; linarith)
  rw [hwv] at hWF
  generalize build A B c0 L m 0 b0 1 ρ0 = t at hWF hPr hGP hLP
  obtain ⟨Δ, hΔ, hBd⟩ := exists_bounded_of_gapsPos t hGP
  set lamMin := lamFactor c0 L m with hlamMin
  have hlamMin0 : 0 < lamMin := lamFactor_pos hc hL m
  obtain ⟨νmin, hν, _, hνle⟩ := exists_pos_le_of_forall_pos A0 (fun g => Aff.norm1 m g) (by
    intro g hg
    simp only [hA0, Atop, List.mem_append, List.mem_map, List.mem_filter, List.mem_range]
      at hg
    rcases hg with ⟨h, ⟨_, hex⟩, rfl⟩ | ⟨i, hi, rfl⟩
    · obtain ⟨l, hl, hne⟩ := by simpa using hex
      exact lt_of_lt_of_le (abs_pos.mpr hne)
        (Finset.single_le_sum (f := fun l => |(slice h).α l|) (fun _ _ => abs_nonneg _)
          (by simpa using hl))
    · have : |(wallFn i).α i| ≤ Aff.norm1 m (wallFn i) :=
        Finset.single_le_sum (f := fun l => |(wallFn i).α l|) (fun _ _ => abs_nonneg _)
          (by simpa using hi)
      rw [wallFn_α, abs_one] at this; linarith)
  set κ1 := lamMin * νmin / 4 with hκ1
  have hκ1pos : 0 < κ1 := by positivity
  set κ := min κ1 κ2 with hκdef
  set η1 := min (1 / 4) (lamMin / 4) with hη1def
  have hη1pos : 0 < η1 := lt_min (by norm_num) (by positivity)
  have hη1lt : η1 < 1 / 2 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  set Bβ := B + 3 with hBβ
  have hBβ0 : 0 < Bβ := by linarith
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set C := 2 * (1 + Bβ * m) with hCdef
  have hC1 : 1 ≤ C := by
    have : 0 ≤ Bβ * m := by positivity
    rw [hCdef]; linarith
  set N := (B + 3) * (log 2 + log C) + log (2 * (m : ℝ)) + log 2 with hNdef
  have hN0 : 0 ≤ N := by
    have := log_nonneg hC1
    have := log_nonneg (show (1:ℝ) ≤ 2 * m by linarith)
    have := log_nonneg (show (1:ℝ) ≤ 2 by norm_num)
    have h5 : 0 ≤ log 2 + log C := by linarith
    have := mul_nonneg (by linarith : (0:ℝ) ≤ B + 3) h5
    rw [hNdef]; linarith
  -- the smallness of the scale
  have hev : ∀ᶠ s in 𝓝[>] (0:ℝ), s ^ ρ0 < Δ / (2 * (m * Bβ) + 1) ∧
      s ^ (2 * ρ0) < 1 / (2 * (m * Bβ) + 1) ∧ log 2 + N / η1 + 1 ≤ -log s := by
    refine (eventually_small hρ0 (by positivity)).and
      ((eventually_small (by positivity) (by positivity)).and (eventually_neglog_ge _))
  obtain ⟨s₁, hs₁, hs₁P⟩ := (nhdsGT_basis (0:ℝ)).eventually_iff.mp hev
  -- the constants along any path are at least `-s/2`
  have hpDany : ∀ s, 0 < s → s < min s₁ (1 / 8) → ∀ P, IsPath t P → -(s / 2) ≤ pathD s t P := by
    intro s hs0 hs1 P hP
    obtain ⟨_, hsb, _⟩ := hs₁P ⟨hs0, lt_of_lt_of_le hs1 (min_le_left _ _)⟩
    have hs8 : s < 1 / 8 := lt_of_lt_of_le hs1 (min_le_right _ _)
    have habs := absD_le hs0 (by linarith) t 1 ρ0 hWF hBd hρ0.le P hP
    have h1 := neg_absD_le_pathD s t P
    have h2 : (m : ℝ) * Bβ * s ^ (1 + 2 * ρ0) ≤ s / 2 := by
      rw [rpow_add hs0, rpow_one]
      have : (m : ℝ) * Bβ * s ^ (2 * ρ0) ≤ 1 / 2 := by
        have h3 : (m : ℝ) * Bβ * s ^ (2 * ρ0) ≤ (m * Bβ) * (1 / (2 * (m * Bβ) + 1)) :=
          mul_le_mul_of_nonneg_left hsb.le (by positivity)
        have hX : 0 ≤ (m : ℝ) * Bβ := by positivity
        have h4 : (m * Bβ) * (1 / (2 * (m * Bβ) + 1)) ≤ 1 / 2 := by
          rw [mul_one_div, div_le_iff₀ (by positivity)]; linarith
        linarith
      calc (m : ℝ) * Bβ * (s * s ^ (2 * ρ0)) = s * ((m : ℝ) * Bβ * s ^ (2 * ρ0)) := by ring
        _ ≤ s * (1 / 2) := mul_le_mul_of_nonneg_left this hs0.le
        _ = s / 2 := by ring
    linarith
  refine ⟨t, ρ0, hρ0, hWF, hGP, κ, lt_min hκ1pos hκ2, min s₁ (1 / 8), lt_min hs₁ (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num),
    fun s hs0 hs1 P hP => by linarith [hpDany s hs0 hs1 P hP], ?_⟩
  intro s hs0 hs1 c hc1 hc2 z hz hzdesc hzbox hfac P hP hval
  obtain ⟨hsa, hsb, hsc⟩ := hs₁P ⟨hs0, lt_of_lt_of_le hs1 (min_le_left _ _)⟩
  have hs8 : s < 1 / 8 := lt_of_lt_of_le hs1 (min_le_right _ _)
  set y : ℕ → ℝ := fun l => z (l + 1) with hydef
  have hy0 : ∀ j, 0 ≤ y j := fun j => (hz _).le
  -- minimality
  have hmin : ∀ Q, IsPath t Q → BTree.val s t P y ≤ BTree.val s t Q y := by
    intro Q hQ; have := hfac Q hQ; linarith
  have hsmall : (m : ℝ) * Bβ * s ^ ρ0 ≤ Δ / 2 := by
    have h1 : (m : ℝ) * Bβ * s ^ ρ0 ≤ (m * Bβ) * (Δ / (2 * (m * Bβ) + 1)) :=
      mul_le_mul_of_nonneg_left hsa.le (by positivity)
    have hX : 0 ≤ (m : ℝ) * Bβ := by positivity
    have hfrac : (m : ℝ) * Bβ / (2 * (m * Bβ) + 1) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have h2 : (m * Bβ) * (Δ / (2 * (m * Bβ) + 1)) ≤ Δ / 2 := by
      calc (m * Bβ) * (Δ / (2 * (m * Bβ) + 1)) = Δ * ((m : ℝ) * Bβ / (2 * (m * Bβ) + 1)) := by
            ring
        _ ≤ Δ * (1 / 2) := mul_le_mul_of_nonneg_left hfrac hΔ.le
        _ = Δ / 2 := by ring
    linarith
  have hR := realized_of_isMin hs0 (by linarith) m hρ0 hΔ hsmall t 1 ρ0 (by omega) hWF hBd le_rfl
    y hy0 P hP hmin
  -- descending
  have hanti : ∀ i j, i ≤ j → j ≤ m → z j ≤ z i := by
    intro i j hij hjm
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j _ ih => exact le_trans (hzdesc j (by omega)) (ih (by omega))
  -- bounds on `z 0`
  have hvaleq := val_eq s t 0 b0 P hP y
  have hpD0 := pathD_nonpos hs0.le t 1 ρ0 hWF P hP
  have habs := absD_le hs0 (by linarith) t 1 ρ0 hWF hBd hρ0.le P hP
  have hpDlow : -(s / 2) ≤ pathD s t P := by
    have h1 := neg_absD_le_pathD s t P
    have h2 : (m : ℝ) * Bβ * s ^ (1 + 2 * ρ0) ≤ s / 2 := by
      rw [rpow_add hs0, rpow_one]
      have : (m : ℝ) * Bβ * s ^ (2 * ρ0) ≤ 1 / 2 := by
        have h3 : (m : ℝ) * Bβ * s ^ (2 * ρ0) ≤ (m * Bβ) * (1 / (2 * (m * Bβ) + 1)) :=
          mul_le_mul_of_nonneg_left hsb.le (by positivity)
        have hX : 0 ≤ (m : ℝ) * Bβ := by positivity
        have h4 : (m * Bβ) * (1 / (2 * (m * Bβ) + 1)) ≤ 1 / 2 := by
          rw [mul_one_div, div_le_iff₀ (by positivity)]; linarith
        linarith
      calc (m : ℝ) * Bβ * (s * s ^ (2 * ρ0)) = s * ((m : ℝ) * Bβ * s ^ (2 * ρ0)) := by ring
        _ ≤ s * (1 / 2) := mul_le_mul_of_nonneg_left this hs0.le
        _ = s / 2 := by ring
    linarith
  have hsumβ : 0 ≤ ∑ l ∈ range m, leafB t 0 b0 P (0 + l) * y l ∧
      ∑ l ∈ range m, leafB t 0 b0 P (0 + l) * y l ≤ Bβ * m * z 0 := by
    constructor
    · refine sum_nonneg fun l hl => mul_nonneg ?_ (hy0 l)
      exact (leafB_mem t Bβ 0 b0 hGP P hP (0 + l) (by omega) (by simp at hl; omega)).1
    · calc ∑ l ∈ range m, leafB t 0 b0 P (0 + l) * y l ≤ ∑ l ∈ range m, Bβ * z 0 := by
            refine sum_le_sum fun l hl => ?_
            have hb := leafB_mem t Bβ 0 b0 hGP P hP (0 + l) (by omega) (by simp at hl; omega)
            have hyl : y l ≤ z 0 := hanti 0 (l + 1) (by omega) (by simp at hl; omega)
            exact mul_le_mul hb.2 hyl (hy0 l) hBβ0.le
        _ = Bβ * m * z 0 := by simp; ring
  have hz0up : z 0 ≤ 2 * s := by rw [hvaleq] at hval; linarith [hsumβ.1]
  have hz0low : s / C ≤ z 0 := by
    rw [hvaleq] at hval
    have hz0pos := hz 0
    rw [div_le_iff₀ (by positivity)]
    have h1 : c ≤ z 0 + Bβ * m * z 0 := by linarith [hsumβ.2]
    have h2 : z 0 * C = 2 * (z 0 + Bβ * m * z 0) := by rw [hCdef]; ring
    rw [h2]; linarith
  have hlogz0 : log (z 0) < 0 := log_neg (hz 0) (by linarith)
  -- the conversion error
  have ha : log 2 < -log s := by
    have : 0 ≤ N / η1 := div_nonneg hN0 hη1pos.le
    linarith
  have hE : convErr (B + 3) C m (-log s) ≤ η1 := by
    unfold convErr
    rw [← hNdef]
    have hden : N / η1 + 1 ≤ -log s - log 2 := by linarith
    have hden0 : 0 < N / η1 + 1 := by positivity
    rw [div_le_iff₀ (by linarith)]
    calc N = η1 * (N / η1) := by field_simp
      _ ≤ η1 * (-log s - log 2) := by
          apply mul_le_mul_of_nonneg_left _ hη1pos.le; linarith
      _ = _ := by ring
  -- the walk
  set p : ℕ → ℝ := fun l => log (z (l + 1)) / log (z 0) with hpdef
  set Y : ℕ → ℝ := fun l => z (l + 1) with hYdef
  have hU : ∀ l, l < m → Y l ≤ ysum (m - l) (fun i => Y (l + i)) ∧
      ysum (m - l) (fun i => Y (l + i)) ≤ m * Y l := by
    intro l hl
    have hml : m - l = (m - l - 1) + 1 := by omega
    constructor
    · rw [hml, ysum, sum_range_succ']
      have : 0 ≤ ∑ i ∈ range (m - l - 1), Y (l + (i + 1)) :=
        sum_nonneg fun i _ => (hz _).le
      simp only [Nat.add_zero]; linarith
    · calc ysum (m - l) (fun i => Y (l + i)) ≤ ∑ i ∈ range (m - l), Y l := by
            refine sum_le_sum fun i hi => ?_
            simp at hi
            exact hanti (l + 1) (l + i + 1) (by omega) (by omega)
        _ = (m - l : ℕ) * Y l := by simp
        _ ≤ m * Y l := by
            apply mul_le_mul_of_nonneg_right _ (hz _).le
            exact_mod_cast Nat.sub_le m l
  have hup : ∀ l h, l < m → 0 ≤ h → h ≤ B + 3 →
      s ^ h ≤ 2 * ysum (m - l) (fun i => Y (l + i)) → p l ≤ h + η1 := by
    intro l h hl h0 hH hle
    have := conv_up (C := C) (K := m) (H := B + 3) hs0 hC1 hmR ha hz0low hz0up (hz _)
      (hU l hl).2 h0 hH hle
    linarith
  have hdown : ∀ l h, l < m → 0 ≤ h → h ≤ B + 3 →
      ysum (m - l) (fun i => Y (l + i)) ≤ 2 * s ^ h → h - η1 ≤ p l := by
    intro l h hl h0 hH hle
    have := conv_down (C := C) (K := m) (H := B + 3) hs0 hC1 hmR ha hz0low hz0up (hz _)
      (hU l hl).1 h0 hH hle
    linarith
  have hch : ∀ l, l + 1 < m → p l ≤ p (l + 1) := by
    intro l hl
    exact div_le_div_of_nonpos_of_le hlogz0.le
      (log_le_log (hz _) (hzdesc (l + 1) (by omega)))
  have hbox : ∀ l, l < m → p l ≤ B := by
    intro l hl
    have h1 : z 0 ^ B ≤ z (l + 1) := le_trans hzbox (hanti (l + 1) m (by omega) le_rfl)
    have h2 := log_le_log (rpow_pos_of_pos (hz 0) _) h1
    rw [log_rpow (hz 0)] at h2
    rw [hpdef]; dsimp only
    rw [div_le_iff_of_neg hlogz0]; linarith
  have hp0 : 1 ≤ p 0 := by
    rw [hpdef]; dsimp only
    rw [le_div_iff_of_neg hlogz0, one_mul]
    exact log_le_log (hz _) (hzdesc 0 (by omega))
  have hR' : Realized s t P (fun i => Y (0 + i)) := by
    have : (fun i => Y (0 + i)) = y := by funext i; simp [hYdef, hydef]
    rw [this]; exact hR
  obtain ⟨hQ, _, hclose⟩ := walk hη1lt hup hdown hch hbox t 0 b0 1 ρ0 P (by omega) hWF hPr hGP
    hLP hP hR' (fun _ => by linarith)
  obtain ⟨lam, hlam, hlfs, hρL⟩ := hQ
  have hAtop : A (m - 1) = A0 := by
    rw [hAdef, towerA_eq, if_neg (by omega)]
  rw [hAtop] at hlfs
  refine ⟨hz0up, fun h hh hneg => ?_⟩
  -- the sum of `h log z`
  have hsplit : ∑ i ∈ range (m + 1), h i * log (z i) =
      log (z 0) * (h 0 + ∑ l ∈ range m, h (l + 1) * p l) := by
    rw [sum_range_succ', mul_add, mul_sum]
    have : ∀ l ∈ range m, h (l + 1) * log (z (l + 1)) = log (z 0) * (h (l + 1) * p l) := by
      intro l _
      have hne : log (z 0) ≠ 0 := hlogz0.ne
      rw [hpdef]; dsimp only; field_simp
    rw [sum_congr rfl this]; ring
  rw [hsplit]
  by_cases hex : ∃ l ∈ range m, h (l + 1) ≠ 0
  · have hg : slice h ∈ A0 := by
      simp only [hA0, Atop, List.mem_append, List.mem_map, List.mem_filter]
      exact Or.inl ⟨h, ⟨hh, by simpa using hex⟩, rfl⟩
    set bL := leafB t 0 b0 P with hbL
    have hevb : Aff.eval m (slice h) bL = normalDot m t P h := by
      simp only [Aff.eval, slice, normalDot]
      rw [add_comm]; congr 1
      exact sum_congr rfl fun l _ => mul_comm _ _
    have hevp : Aff.eval m (slice h) p = h 0 + ∑ l ∈ range m, h (l + 1) * p l := by
      simp only [Aff.eval, slice]; ring
    have hne : Aff.eval m (slice h) bL ≠ 0 := by rw [hevb]; exact hneg.ne
    have hl1 := hlfs _ hg hne
    rw [abs_of_neg (by rw [hevb]; exact hneg)] at hl1
    have hlip := Aff.abs_eval_sub_le m (slice h) p bL (leafR t ρ0 P + η1) (fun l hl =>
      hclose l (by omega) hl)
    have hnorm := hνle _ hg
    have hη1lam : η1 ≤ lam / 4 := le_trans (min_le_right _ _) (by linarith)
    have hn0 := Aff.norm1_nonneg m (slice h)
    have hkey : Aff.eval m (slice h) p ≤ -(lam * Aff.norm1 m (slice h)) / 4 := by
      have := (abs_le.mp hlip).2
      have : Aff.norm1 m (slice h) * (leafR t ρ0 P + η1) ≤
          Aff.norm1 m (slice h) * (3 * lam / 4) :=
        mul_le_mul_of_nonneg_left (by linarith) hn0
      linarith
    have hkey2 : Aff.eval m (slice h) p ≤ -κ1 := by
      have : lamMin * νmin ≤ lam * Aff.norm1 m (slice h) :=
        mul_le_mul (by linarith) (by simpa using hnorm) hν.le (by linarith)
      rw [hκ1]; linarith
    rw [← hevp]
    have hκle : κ ≤ κ1 := min_le_left _ _
    have hpos : 0 < -log (z 0) := by linarith
    calc κ * -log (z 0) ≤ κ1 * -log (z 0) := mul_le_mul_of_nonneg_right hκle hpos.le
      _ ≤ -Aff.eval m (slice h) p * -log (z 0) :=
          mul_le_mul_of_nonneg_right (by linarith) hpos.le
      _ = log (z 0) * Aff.eval m (slice h) p := by ring
  · push Not at hex
    have hzero : ∑ l ∈ range m, h (l + 1) * p l = 0 :=
      sum_eq_zero fun l hl => by rw [hex l hl, zero_mul]
    have hzero' : ∑ l ∈ range m, leafB t 0 b0 P l * h (l + 1) = 0 :=
      sum_eq_zero fun l hl => by rw [hex l hl, mul_zero]
    have hh0 : h 0 < 0 := by
      have := hneg; simp only [normalDot] at this; rw [hzero'] at this; linarith
    rw [hzero, add_zero]
    have h1 := hκ2' h hh hh0
    have hκle : κ ≤ κ2 := min_le_right _ _
    have hpos : 0 < -log (z 0) := by linarith
    calc κ * -log (z 0) ≤ -h 0 * -log (z 0) :=
          mul_le_mul_of_nonneg_right (by linarith) hpos.le
      _ = log (z 0) * h 0 := by ring

end Persistence
end CRNT
