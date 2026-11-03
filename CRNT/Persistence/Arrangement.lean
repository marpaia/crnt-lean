import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr

/-!
# Affine arrangements, projection, and the local feature size

An affine functional on the first `k` coordinates of `ℕ → ℝ` is `p ↦ ∑_{l<k} α l * p l + c`.
A finite list `A` of functionals on `k+1` coordinates is *projected* to `k` coordinates by
keeping the vertical ones (`α k = 0`) and adding, for every pair of non-vertical ones, the
difference of their sections `p_k = sec g p`.

`LfsGe k A b lam` says that `lam` is a lower bound for the `ℓ∞`-distance from `b` to every
hyperplane of `A` not containing `b` (`|g b| ≥ λ ‖g‖₁`).  Two facts drive the blueprint
recursion:

* `gap_ge`: distinct section values at a point `b'` are separated by `cgap * λ'` whenever
  `λ'` bounds the local feature size of `b'` in the projected arrangement;
* `lfsGe_update`: lifting `b'` to `(b', β)` keeps a feature-size bound
  `min λ' (d / (1 + L))`, where `d` is the distance from `β` to the other section values.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Persistence

open Finset

/-- An affine functional on `ℕ → ℝ` (only finitely many coordinates are ever read). -/
structure Aff where
  α : ℕ → ℝ
  c : ℝ

namespace Aff

/-- Evaluation on the first `k` coordinates. -/
noncomputable def eval (k : ℕ) (g : Aff) (p : ℕ → ℝ) : ℝ :=
  ∑ l ∈ range k, g.α l * p l + g.c

/-- `ℓ¹` norm of the first `k` coefficients. -/
noncomputable def norm1 (k : ℕ) (g : Aff) : ℝ := ∑ l ∈ range k, |g.α l|

theorem norm1_nonneg (k : ℕ) (g : Aff) : 0 ≤ norm1 k g :=
  sum_nonneg fun _ _ => abs_nonneg _

/-- Section value of a functional on `k+1` coordinates that is non-vertical (`α k ≠ 0`). -/
noncomputable def sec (k : ℕ) (g : Aff) (p : ℕ → ℝ) : ℝ :=
  -(∑ l ∈ range k, g.α l * p l + g.c) / g.α k

/-- The difference of two sections, as a functional on `k` coordinates. -/
noncomputable def diff (k : ℕ) (g g' : Aff) : Aff :=
  ⟨fun l => -g.α l / g.α k + g'.α l / g'.α k, -g.c / g.α k + g'.c / g'.α k⟩

theorem eval_diff (k : ℕ) (g g' : Aff) (p : ℕ → ℝ) :
    eval k (diff k g g') p = sec k g p - sec k g' p := by
  simp only [eval, diff, sec]
  have h1 : ∑ l ∈ range k, (-g.α l / g.α k + g'.α l / g'.α k) * p l =
      -(∑ l ∈ range k, g.α l * p l) / g.α k + (∑ l ∈ range k, g'.α l * p l) / g'.α k := by
    rw [neg_div, Finset.sum_div, Finset.sum_div, ← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [h1]; ring

theorem eval_succ (k : ℕ) (g : Aff) (p : ℕ → ℝ) :
    eval (k + 1) g p = eval k g p + g.α k * p k := by
  simp [eval, sum_range_succ]; ring

theorem eval_succ_eq_mul (k : ℕ) (g : Aff) (hg : g.α k ≠ 0) (p : ℕ → ℝ) :
    eval (k + 1) g p = g.α k * (p k - sec k g p) := by
  rw [eval_succ, sec]; field_simp; simp only [eval]; ring

theorem eval_update_lt (k : ℕ) (g : Aff) (b : ℕ → ℝ) (β : ℝ) :
    eval k g (Function.update b k β) = eval k g b := by
  simp only [eval]
  congr 1
  refine sum_congr rfl fun l hl => ?_
  rw [Function.update_of_ne (by simp at hl; omega)]

theorem sec_update (k : ℕ) (g : Aff) (b : ℕ → ℝ) (β : ℝ) :
    sec k g (Function.update b k β) = sec k g b := by
  have h : ∑ l ∈ range k, g.α l * Function.update b k β l = ∑ l ∈ range k, g.α l * b l :=
    sum_congr rfl fun l hl => by rw [Function.update_of_ne (by simp at hl; omega)]
  simp only [sec, h]

theorem norm1_succ (k : ℕ) (g : Aff) : norm1 (k + 1) g = norm1 k g + |g.α k| := by
  simp [norm1, sum_range_succ]

/-- Lipschitz bound: `|g p - g q| ≤ ‖g‖₁ * max_l |p l - q l|`. -/
theorem abs_eval_sub_le (k : ℕ) (g : Aff) (p q : ℕ → ℝ) (r : ℝ)
    (h : ∀ l, l < k → |p l - q l| ≤ r) :
    |eval k g p - eval k g q| ≤ norm1 k g * r := by
  have e : eval k g p - eval k g q = ∑ l ∈ range k, g.α l * (p l - q l) := by
    simp only [eval]; rw [add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [e]
  calc |∑ l ∈ range k, g.α l * (p l - q l)| ≤ ∑ l ∈ range k, |g.α l * (p l - q l)| :=
        Finset.abs_sum_le_sum_abs (fun l => g.α l * (p l - q l)) (range k)
    _ ≤ ∑ l ∈ range k, |g.α l| * r := Finset.sum_le_sum fun l hl => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (h l (by simpa using hl)) (abs_nonneg _)
    _ = norm1 k g * r := by rw [norm1, Finset.sum_mul]

end Aff

/-- The projection of an arrangement on `k+1` coordinates to `k` coordinates. -/
noncomputable def proj (k : ℕ) (A : List Aff) : List Aff :=
  A.filter (fun g => decide (g.α k = 0)) ++
    (A.flatMap fun g => A.map fun g' => Aff.diff k g g')

theorem mem_proj_of_vertical {k : ℕ} {A : List Aff} {g : Aff} (hg : g ∈ A) (hv : g.α k = 0) :
    g ∈ proj k A := by
  simp [proj, hg, hv]

theorem diff_mem_proj {k : ℕ} {A : List Aff} {g g' : Aff} (hg : g ∈ A) (hg' : g' ∈ A) :
    Aff.diff k g g' ∈ proj k A := by
  simp only [proj, List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inr ⟨g, hg, g', hg', rfl⟩

/-- `λ` bounds the local feature size of `b` in `A` (on `k` coordinates). -/
def LfsGe (k : ℕ) (A : List Aff) (b : ℕ → ℝ) (lam : ℝ) : Prop :=
  ∀ g ∈ A, Aff.eval k g b ≠ 0 → lam * Aff.norm1 k g ≤ |Aff.eval k g b|

theorem LfsGe.mono {k : ℕ} {A : List Aff} {b : ℕ → ℝ} {lam lam' : ℝ} (h : LfsGe k A b lam)
    (hle : lam' ≤ lam) : LfsGe k A b lam' := fun g hg hne =>
  le_trans (mul_le_mul_of_nonneg_right hle (Aff.norm1_nonneg _ _)) (h g hg hne)

/-- Every list of positive reals has a positive lower bound. -/
theorem exists_pos_le_of_forall_pos {ι : Type*} (s : List ι) (q : ι → ℝ)
    (hq : ∀ i ∈ s, 0 < q i) : ∃ c, 0 < c ∧ c ≤ 1 ∧ ∀ i ∈ s, c ≤ q i := by
  induction s with
  | nil => exact ⟨1, one_pos, le_rfl, by simp⟩
  | cons a s ih =>
      obtain ⟨c, hc, hc1, hcs⟩ := ih fun i hi => hq i (List.mem_cons_of_mem _ hi)
      refine ⟨min c (q a), lt_min hc (hq a (by simp)), le_trans (min_le_left _ _) hc1, ?_⟩
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact min_le_right _ _
      · exact le_trans (min_le_left _ _) (hcs i hi)

/-- Every finite list of reals has an upper bound `≥ 1`. -/
theorem exists_ge_of_list {ι : Type*} (s : List ι) (q : ι → ℝ) :
    ∃ L, 1 ≤ L ∧ ∀ i ∈ s, q i ≤ L := by
  induction s with
  | nil => exact ⟨1, le_rfl, by simp⟩
  | cons a s ih =>
      obtain ⟨L, hL, hLs⟩ := ih
      refine ⟨max L (q a), le_trans hL (le_max_left _ _), ?_⟩
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact le_max_right _ _
      · exact le_trans (hLs i hi) (le_max_left _ _)

/-- The gap constant of an arrangement on `k+1` coordinates. -/
theorem exists_gap_const (k : ℕ) (A : List Aff) :
    ∃ c, 0 < c ∧ c ≤ 1 ∧ ∀ g ∈ A, ∀ g' ∈ A,
      (0 < Aff.norm1 k (Aff.diff k g g') → c ≤ Aff.norm1 k (Aff.diff k g g')) ∧
      ((Aff.diff k g g').c ≠ 0 → c ≤ |(Aff.diff k g g').c|) := by
  obtain ⟨c1, hc1, hc11, hs1⟩ := exists_pos_le_of_forall_pos
    ((A.flatMap fun g => A.map fun g' => Aff.diff k g g').filter fun d : Aff =>
    decide (0 < Aff.norm1 k d)) (fun d : Aff => Aff.norm1 k d) (by
      intro d hd; simpa using (List.mem_filter.mp hd).2)
  obtain ⟨c2, hc2, hc21, hs2⟩ := exists_pos_le_of_forall_pos
    ((A.flatMap fun g => A.map fun g' => Aff.diff k g g').filter fun d : Aff =>
    decide (d.c ≠ 0)) (fun d : Aff => |d.c|) (by
      intro d hd; exact abs_pos.mpr (by simpa using (List.mem_filter.mp hd).2))
  refine ⟨min c1 c2, lt_min hc1 hc2, le_trans (min_le_left _ _) hc11, fun g hg g' hg' => ?_⟩
  have hmem : Aff.diff k g g' ∈ (A.flatMap fun g => A.map fun g' => Aff.diff k g g') := by
    simp only [List.mem_flatMap, List.mem_map]; exact ⟨g, hg, g', hg', rfl⟩
  refine ⟨fun hpos => le_trans (min_le_left _ _) (hs1 _ (List.mem_filter.mpr ⟨hmem, by
    simpa using hpos⟩)), fun hc => le_trans (min_le_right _ _) (hs2 _ (List.mem_filter.mpr
    ⟨hmem, by simpa using hc⟩))⟩

/-- **Gap lemma.**  Distinct section values at `b'` are at least `c * λ'` apart. -/
theorem gap_ge {k : ℕ} {A : List Aff} {c : ℝ}
    (hc : ∀ g ∈ A, ∀ g' ∈ A,
      (0 < Aff.norm1 k (Aff.diff k g g') → c ≤ Aff.norm1 k (Aff.diff k g g')) ∧
      ((Aff.diff k g g').c ≠ 0 → c ≤ |(Aff.diff k g g').c|))
    (hc0 : 0 ≤ c)
    {b' : ℕ → ℝ} {lam : ℝ} (hlam1 : lam ≤ 1) (hlam0 : 0 ≤ lam) (hL : LfsGe k (proj k A) b' lam)
    {g g' : Aff} (hg : g ∈ A) (hg' : g' ∈ A)
    (hne : Aff.sec k g b' ≠ Aff.sec k g' b') :
    c * lam ≤ |Aff.sec k g b' - Aff.sec k g' b'| := by
  set d := Aff.diff k g g'
  have hev : Aff.eval k d b' = Aff.sec k g b' - Aff.sec k g' b' := Aff.eval_diff k g g' b'
  have hne' : Aff.eval k d b' ≠ 0 := by rw [hev]; exact sub_ne_zero.mpr hne
  have hlfs := hL d (diff_mem_proj hg hg') hne'
  rw [hev] at hlfs
  rcases (Aff.norm1_nonneg k d).lt_or_eq with hpos | hzero
  · have := (hc g hg g' hg').1 hpos
    calc c * lam ≤ Aff.norm1 k d * lam := mul_le_mul_of_nonneg_right this hlam0
      _ = lam * Aff.norm1 k d := mul_comm _ _
      _ ≤ _ := hlfs
  · -- all coefficients vanish: `d` is the constant `d.c ≠ 0`
    have hcoef : ∀ l ∈ range k, d.α l = 0 := by
      intro l hl
      have := (sum_eq_zero_iff_of_nonneg (fun l _ => abs_nonneg (d.α l))).mp hzero.symm l hl
      exact abs_eq_zero.mp this
    have hconst : Aff.eval k d b' = d.c := by
      simp only [Aff.eval]
      rw [sum_eq_zero (fun l hl => by rw [hcoef l hl, zero_mul]), zero_add]
    have hdc : d.c ≠ 0 := by rw [← hconst]; exact hne'
    have := (hc g hg g' hg').2 hdc
    rw [← hev, hconst]
    calc c * lam ≤ c * 1 := mul_le_mul_of_nonneg_left hlam1 hc0
      _ = c := mul_one c
      _ ≤ |d.c| := this

/-- **Lifting the feature-size bound.**  If every non-vertical functional of `A` whose section
at `b'` differs from `β` has its section at least `d0` away from `β`, and `L` bounds the slopes,
then `(b', β)` has feature size at least `min λ' (d0 / (1 + L))`. -/
theorem lfsGe_update {k : ℕ} {A : List Aff} {b' : ℕ → ℝ} {lam d0 L β : ℝ}
    (hL0 : 0 ≤ L) (hd0 : 0 ≤ d0)
    (hslope : ∀ g ∈ A, g.α k ≠ 0 → Aff.norm1 k g ≤ L * |g.α k|)
    (hlfs : LfsGe k (proj k A) b' lam)
    (hsep : ∀ g ∈ A, g.α k ≠ 0 → Aff.sec k g b' ≠ β → d0 ≤ |β - Aff.sec k g b'|) :
    LfsGe (k + 1) A (Function.update b' k β) (min lam (d0 / (1 + L))) := by
  intro g hg hne
  by_cases hv : g.α k = 0
  · have hev : Aff.eval (k + 1) g (Function.update b' k β) = Aff.eval k g b' := by
      rw [Aff.eval_succ, hv, zero_mul, add_zero, Aff.eval_update_lt]
    have hn : Aff.norm1 (k + 1) g = Aff.norm1 k g := by
      rw [Aff.norm1_succ, hv, abs_zero, add_zero]
    rw [hev] at hne; rw [hev, hn]
    exact le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Aff.norm1_nonneg _ _))
      (hlfs g (mem_proj_of_vertical hg hv) hne)
  · have hev : Aff.eval (k + 1) g (Function.update b' k β) = g.α k * (β - Aff.sec k g b') := by
      rw [Aff.eval_succ_eq_mul k g hv, Function.update_self, Aff.sec_update]
    rw [hev] at hne ⊢
    have hsecne : Aff.sec k g b' ≠ β := by
      intro h; apply hne; rw [h, sub_self, mul_zero]
    have hd := hsep g hg hv hsecne
    have hn : Aff.norm1 (k + 1) g ≤ (1 + L) * |g.α k| := by
      rw [Aff.norm1_succ]; linarith [hslope g hg hv]
    have h1L : 0 < 1 + L := by linarith
    rw [abs_mul]
    calc min lam (d0 / (1 + L)) * Aff.norm1 (k + 1) g
        ≤ d0 / (1 + L) * Aff.norm1 (k + 1) g :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (Aff.norm1_nonneg _ _)
      _ ≤ d0 / (1 + L) * ((1 + L) * |g.α k|) :=
          mul_le_mul_of_nonneg_left hn (div_nonneg hd0 h1L.le)
      _ = d0 * |g.α k| := by field_simp
      _ ≤ |β - Aff.sec k g b'| * |g.α k| := mul_le_mul_of_nonneg_right hd (abs_nonneg _)
      _ = |g.α k| * |β - Aff.sec k g b'| := mul_comm _ _

end Persistence
end CRNT
